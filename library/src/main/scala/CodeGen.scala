package sbt.datatype
import scala.compat.Platform.EOL

abstract class CodeGenerator {

  def augmentIndentTrigger(s: String): Boolean
  def reduceIndentTrigger(s: String): Boolean

  protected class IndentationAwareBuffer(val indent: String, private var level: Int = 0) {
    private val buffer: StringBuilder = new StringBuilder

    private def append(s: String): Unit = {
      val clean = s.trim
      if (reduceIndentTrigger(clean)) level = 0 max (level - 1)
      buffer append (indent * level + clean + EOL)
      if (augmentIndentTrigger(clean)) level += 1
    }

    def +=(it: Iterator[String]): Unit = it foreach append
    def +=(s: String): Unit = s.lines foreach append

    override def toString(): String = buffer.mkString
  }

  protected def buffered(op: IndentationAwareBuffer => Unit): String

  protected final def perVersionNumber[T](allFields: List[Field])(op: (List[Field], List[Field]) => T): List[T] = {
    val versionNumbers = allFields.map(_.since).sorted.distinct
    versionNumbers map { v =>
      val (provided, byDefault) = allFields partition (_.since <= v)
      op(provided, byDefault)
    }
  }

  def generate(s: Schema): Map[String, String]
  final def generate(d: Definition, parent: Option[Protocol], superFields: List[Field]): Map[String, String] =
    d match {
      case p: Protocol    => generate(p, parent, superFields)
      case r: Record      => generate(r, parent, superFields)
      case e: Enumeration => generate(e)
    }
  def generate(p: Protocol, parent: Option[Protocol], superFields: List[Field]): Map[String, String]
  def generate(r: Record, parent: Option[Protocol], superFields: List[Field]): Map[String, String]
  def generate(e: Enumeration): Map[String, String]

}

object CodeGen {
  def generate(ps: ProtocolSchema): String =
    {
      val ns = ps.namespace
      val types = ps.types map { tpe: TypeDef => generateType(ns, tpe) }
      val typesCode = types.mkString("\n")
      s"""package $ns

$typesCode"""
    }

  def generateType(namespace: String, td: TypeDef): String =
    {
      val name = td.name
      val fields = td.fields map { field: FieldSchema => s"""${field.name}: ${field.`type`.name}""" }
      val fieldsCode = fields.mkString(",\n  ")
      val ctorFields = td.fields map { field: FieldSchema => s"""val ${field.name}: ${field.`type`.name}""" }
      val ctorFieldsCode = ctorFields.mkString(",\n  ")
      val fieldNames = td.fields map { field: FieldSchema => field.name }
      val sinces = (td.fields map {_.since}).distinct.sorted
      val inclusives = sinces.zipWithIndex map { case (k, idx) =>
        val dropNum = sinces.size - 1 - idx
        sinces dropRight dropNum
      }
      val alternatives = inclusives dropRight 1
      val altCode = (alternatives map { alts =>
        generateAltCtor(td.fields, alts)
      }).mkString("\n    ")

      val fieldNamesCode = fieldNames.mkString(", ")
      val mainApply =
        s"""def apply($fieldsCode): $name =
    new $name($fieldNamesCode)"""
      s"""final class $name($ctorFieldsCode) {
  ${altCode}
  ${generateEquals(name, fieldNames)}
  ${generateHashCode(fieldNames)}
  ${generateCopy(name, td.fields)}
}

object $name {
  $mainApply
}"""
    }
  
  def generateAltCtor(fields: Vector[FieldSchema], versions: Vector[VersionNumber]): String =
    {
      val vs = versions.toSet
      val params = fields filter { f => vs contains f.since } map { f => s"${f.name}: ${f.`type`.name}" }
      val paramsCode = params.mkString(", ")
      val args = fields map { f =>
        if (vs contains f.since) f.name
        else quote(f.defaultValue getOrElse { sys.error(s"${f.name} is missing `default` value") },
          f.`type`.name)
      }
      val argsCode = args.mkString(", ")
      s"def this($paramsCode) = this($argsCode)"
    }
  def quote(value: String, tpe: String): String =
    tpe match {
      case "String" => s""""$value"""" // "
      case _        => value
    }

  def generateCopy(name: String, fields: Vector[FieldSchema]): String =
    {
      val params = fields map { f => s"${f.name}: ${f.`type`.name} = this.${f.name}" }
      val paramsCode = params.mkString(",\n    ")
      val args = fields map { f => f.name }
      val argsCode = args.mkString(", ")
      s"private[this] def copy($paramsCode): $name =\n" +
      s"    new $name($argsCode)"
    }

  def generateEquals(name: String, fieldNames: Vector[String]): String =
    {
      val fieldNamesEq = fieldNames map { n: String => s"(this.$n == x.$n)" }
      val fieldNamesEqCode = fieldNamesEq.mkString(" &&\n        ")
      s"""override def equals(o: Any): Boolean =
    o match {
      case x: $name =>
        $fieldNamesEqCode
      case _ => false
    }"""
    }

  def generateHashCode(fieldNames: Vector[String]): String =
    {
      val fieldNamesHash = fieldNames map { n: String => 
        s"hash = hash * 31 + this.$n.##"
      }
      val fieldNameHashCode = fieldNamesHash.mkString("\n      ") 
      s"""override def hashCode: Int =
    {
      var hash = 1
      $fieldNameHashCode
      hash
    }"""
    }
}

