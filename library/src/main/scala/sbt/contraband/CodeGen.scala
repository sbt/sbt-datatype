package sbt.contraband

import java.io.File
import scala.collection.immutable.ListMap
import ast.{ Definition => _, _ }
import AstUtil._

/**
 * The base for code generators.
 */
abstract class CodeGenerator {

  //make sure that EOL is *not* platform dependent by default, otherwise
  //the output of contraband will be platform dependent too.
  val EOL = "\n"

  implicit class ListMapOp[T](m: ListMap[T, String]) {
    def merge(o: ListMap[T, String]): ListMap[T, String] =
      (o foldLeft m) { case (acc, (k, v)) =>
        val existing = acc get k getOrElse ""

        acc get k match {
          case None =>
            acc + (k -> v)

          case Some(existing) =>
            // Remove `package blah` from what we want to add
            val content = v.linesIterator.toList.tail mkString EOL
            acc + (k -> (existing + EOL + EOL + content))
        }
      }

    def mapV(f: String => String): ListMap[T, String] =
      ListMap(m.toList map { case (k, v) =>
        (k, f(v))
      }: _*)
  }

  implicit protected class IndentationAwareString(code: String) {
    final def indented(implicit config: IndentationConfiguration): String = indentWith(config)

    final def indentWith(config: IndentationConfiguration): String = {
      val buffer = new IndentationAwareBuffer(config)
      code.linesIterator foreach buffer .+=
      buffer.toString
    }
  }

  protected def lookupInterfaces(s: Document, interfaceRefs: List[ast.NamedType]): List[InterfaceTypeDefinition] =
    {
      val pkg =
        s.packageDecl map { case PackageDecl(nameSegments, _, _, _) =>
          nameSegments.mkString(".")
        }
      val refs =
        interfaceRefs map { ref =>
          ref.names match {
            case Nil => sys.error(s"Invalid named type: $ref")
            case xs  =>
              val namespace = xs.init match {
                case Nil => pkg
                case xs  => Some(xs.mkString("."))
              }
              (namespace, xs.last)
          }
        }
      refs map { ref => lookupInterface(s, ref) }
    }

  protected def lookupInterface(s: Document, ref: (Option[String], String)): InterfaceTypeDefinition =
    {
      val (ns, name) = ref
      val intfs = s.definitions collect {
        case i: InterfaceTypeDefinition => i
      }
      (intfs find { i =>
        i.name == name && i.namespace == ns
      }) match {
        case Some(i) => i
        case _       => sys.error(s"$ref not found")
      }
    }

  protected def lookupChildLeaves(s: Document, interface: InterfaceTypeDefinition): List[TypeDefinition] =
    {
      val pkg =
        s.packageDecl map { case PackageDecl(nameSegments, _, _, _) =>
          nameSegments.mkString(".")
        }
      val tpe = toNamedType(interface, pkg)
      def containsTpe(intfs: List[NamedType]): Boolean =
        intfs exists { ref =>
          ref.names.size match {
            case 0 => sys.error(s"Invalid reference $intfs")
            case 1 => ref.names.head == tpe.names.last
            case _ => ref.names == tpe.names
          }
        }
      s.definitions flatMap {
        case r: ObjectTypeDefinition if containsTpe(r.interfaces)    => List(r)
        case i: InterfaceTypeDefinition if containsTpe(i.interfaces) => lookupChildLeaves(s, i)
        case _ => Nil
      }
    }

  protected def lookupChildren(s: Document, interface: InterfaceTypeDefinition): List[TypeDefinition] =
    {
      val pkg =
        s.packageDecl map { case PackageDecl(nameSegments, _, _, _) =>
          nameSegments.mkString(".")
        }
      val tpe = toNamedType(interface, pkg)
      def containsTpe(intfs: List[NamedType]): Boolean =
        intfs exists { ref =>
          ref.names.size match {
            case 0 => sys.error(s"Invalid reference $intfs")
            case 1 => ref.names.head == tpe.names.last
            case _ => ref.names == tpe.names
          }
        }
      val result = s.definitions collect {
        case r: ObjectTypeDefinition if containsTpe(r.interfaces)    => r
        case i: InterfaceTypeDefinition if containsTpe(i.interfaces) => i
      }
      result
    }

  protected def localFields(cl: RecordLikeDefinition, parents: List[InterfaceTypeDefinition]): List[FieldDefinition] =
    {
      val allFields = cl.fields filter { _.arguments.isEmpty }
      val parentFields: List[FieldDefinition] = parents flatMap { _.fields }
      def inParent(f: FieldDefinition): Boolean = {
        val x = parentFields exists { _.name == f.name }
        x
      }
      allFields filterNot inParent
    }

  /** Run an operation `op` for each different version number that affects the fields `fields`. */
  protected final def perVersionNumber[T](since: VersionNumber, fields: List[FieldDefinition])(op: (List[FieldDefinition], List[FieldDefinition]) => T): List[T] = {
    val versionNumbers = (since :: fields.map({ f => getSince(f.directives) })).sorted.distinct
    versionNumbers map { v =>
      val (provided, byDefault) = fields partition { f => getSince(f.directives) <= v }
      op(provided, byDefault)
    }
  }

  protected def javaLangBoxedType(tpe: String): String =
    tpe match {
      case "boolean" | "Boolean" => "java.lang.Boolean"
      case "byte" | "Byte"       => "java.lang.Byte"
      case "char" | "Char"       => "java.lang.Character"
      case "float" | "Float"     => "java.lang.Float"
      case "int" | "Int"         => "java.lang.Integer"
      case "long" | "Long"       => "java.lang.Long"
      case "short" | "Short"     => "java.lang.Short"
      case "double" | "Double"   => "java.lang.Double"
      case other     => other
    }

  protected def boxedType(tpe: String): String =
    tpe match {
      case "boolean" | "Boolean" => "Boolean"
      case "byte" | "Byte"       => "Byte"
      case "char" | "Char"       => "Character"
      case "float" | "Float"     => "Float"
      case "int" | "Int"         => "Integer"
      case "long" | "Long"       => "Long"
      case "short" | "Short"     => "Short"
      case "double" | "Double"   => "Double"
      case other     => other
    }

  protected def unboxedType(tpe: String): String =
    tpe match {
      case "boolean" | "Boolean" => "boolean"
      case "byte" | "Byte"       => "byte"
      case "char" | "Char"       => "char"
      case "float" | "Float"     => "float"
      case "int" | "Int"         => "int"
      case "long" | "Long"       => "long"
      case "short" | "Short"     => "short"
      case "double" | "Double"   => "double"
      case other     => other
    }

  protected def primitiveType(tpe: String): Boolean =
    tpe match {
      case "boolean" | "Boolean" => true
      case "byte" | "Byte"       => true
      case "char" | "Char"       => true
      case "float" | "Float"     => true
      case "int" | "Int"         => true
      case "long" | "Long"       => true
      case "short" | "Short"     => true
      case "double" | "Double"   => true
      case other     => false
    }

  protected def isPrimitive(tpe: ast.Type) =
    !tpe.isListType && !tpe.isLazyType && tpe.isNotNullType && primitiveType(tpe.name)

  protected def isPrimitiveArray(tpe: ast.Type) =
    tpe.isListType && !tpe.isLazyType && primitiveType(tpe.name)

  protected def containsOptional(fields: List[FieldDefinition]): Boolean =
    fields exists { f => f.fieldType.isOptionalType }

  protected def containsStrictOptional(fields: List[FieldDefinition]): Boolean =
    fields exists { f => f.fieldType.isOptionalType && !f.fieldType.isLazyType }

  protected def genJavaEquals(lhs: String, rhs: String, f0: FieldDefinition,
      fieldName: String, isJava: Boolean): String =
    f0 match {
      case f if isPrimitive(f.fieldType)      => s"($lhs.$fieldName == $rhs.$fieldName)"
      case f if isPrimitiveArray(f.fieldType) => s"java.util.Arrays.equals($lhs.$fieldName, $rhs.$fieldName)"
      case f if f.fieldType.isListType        =>
        if (isJava) s"java.util.Arrays.deepEquals($lhs.$fieldName, $rhs.$fieldName)"
        else s"java.util.Arrays.deepEquals($lhs.$fieldName.asInstanceOf[Array[Object]], $rhs.$fieldName.asInstanceOf[Array[Object]])"
      case f                                  => s"$lhs.$fieldName.equals($rhs.$fieldName)"
    }

  protected def genJavaHashCode(f0: FieldDefinition, fieldName: String, isJava: Boolean): String =
    f0 match {
      case f if isPrimitive(f.fieldType)      => s"${boxedType(f.fieldType.name)}.valueOf($fieldName).hashCode()"
      case f if isPrimitiveArray(f.fieldType) => s"java.util.Arrays.hashCode($fieldName)"
      case f if f.fieldType.isListType        =>
        if (isJava) s"java.util.Arrays.deepHashCode($fieldName)"
        else s"java.util.Arrays.deepHashCode($fieldName.asInstanceOf[Array[Object]])"
      case f                                  => s"$fieldName.hashCode()"
    }

  /** Generate the code corresponding to all definitions in `s`. */
  def generate(s: Document): ListMap[File, String]

  /** Generate the code corresponding to `d`. */
  protected def generate(s: Document, d: TypeDefinition): ListMap[File, String] =
    d match {
      case i: InterfaceTypeDefinition => generateInterface(s, i)
      case r: ObjectTypeDefinition    => generateRecord(s, r)
      case e: EnumTypeDefinition      => generateEnum(s, e)
    }

  /** Generate the code corresponding to the interface `i`. */
  protected def generateInterface(s: Document, i: InterfaceTypeDefinition): ListMap[File, String]

  /** Generate the code corresponding to the record `r`. */
  protected def generateRecord(s: Document, r: ObjectTypeDefinition): ListMap[File, String]

  /** Generate the code corresponding to the enumeration `e`. */
  protected def generateEnum(s: Document, e: EnumTypeDefinition): ListMap[File, String]

  protected def generateHeader: String =
    """/**
      | * This code is generated using [[https://www.scala-sbt.org/contraband]].
      | */
      |
      |// DO NOT EDIT MANUALLY
      |""".stripMargin
}

object CodeGen {
  def bq(id: String): String = if (ScalaKeywords.values(id)) s"`$id`" else id

  val javaOptional: String = "java.util.Optional"
  val instantiateJavaOptional: (String, String) => (String) =
    (tpe: String, e: String) => {
      if (e == "null") s"java.util.Optional.<$tpe>empty()"
      else s"java.util.Optional.<$tpe>ofNullable($e)"
    }
}
