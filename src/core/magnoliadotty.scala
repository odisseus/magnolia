package magnolia
import scala.deriving.Mirror
import scala.compiletime.erasedValue
import scala.compiletime.constValue
import scala.compiletime.summonInline
import scala.compiletime.summonFrom

import language.strictEquality

object Magnolia:
  inline def subtypesOf[Typeclass[_], Parent, T <: Tuple]
                       (tpeName: String, idx: Int)
                       (using m: Mirror.SumOf[Parent])
                       : List[Subtype[Typeclass, Parent]] =
    inline erasedValue[T] match
      case _: Unit => Nil
      case _: ((h, label) *: t) =>
        //todo: better way of getting type names https://github.com/lampepfl/dotty/issues/8739

        val childName = inline constValue[label] match
          case childName: String => childName

        val headSubtype = Subtype[Typeclass, Parent, Parent](
          name = TypeName(tpeName, childName, Nil),
          idx = idx,
          anns = Seq(),
          tc = CallByNeed(summonInline[Typeclass[h]].asInstanceOf[Typeclass[Parent]]), //weird cast but ok
          isType = m.ordinal(_) == idx,
          asType = a => a
        )

        headSubtype :: subtypesOf[Typeclass, Parent, t](tpeName, idx + 1)
    
  inline def splitInternal[Typeclass[_], T]
                          (interface: TCInterface[Typeclass])
                          (using m: Mirror.SumOf[T])
                          : Typeclass[T] =
    val tpeName: String = constValue[m.MirroredLabel]

    val subtypes = subtypesOf[Typeclass, T, Tuple.Zip[m.MirroredElemTypes, m.MirroredElemLabels]](tpeName, 0)

    //todo parent type
    val st: SealedTrait[Typeclass, T] = SealedTrait[Typeclass, T](
      TypeName("", tpeName, Nil),
      subtypes,
      Seq()
    )

    interface.split(st)

  inline def parametersOf[Typeclass[_], Parent, T <: Tuple]
                         (idx: Int)
                         (using m: Mirror.ProductOf[Parent])
                         : List[ReadOnlyParam[Typeclass, Parent]] =
    inline erasedValue[T] match
      case () =>
        Nil
      case _: ((h, label) *: t) =>
        val paramName = constValue[label] match
          case paramName: String => paramName

        val param: ReadOnlyParam[Typeclass, Parent] =
          ReadOnlyParam[Typeclass, Parent, h](
            name = paramName,
            idx = idx,
            isRepeated = false, //todo
            typeclassParam = CallByNeed(summonInline[Typeclass[h]]),
            anns = Seq()
          )

        param :: parametersOf[Typeclass, Parent, t](idx + 1)
  
  inline def joinInternal[Typeclass[_], T]
                         (interface: TCInterface[Typeclass])
                         (using m: Mirror.ProductOf[T])
                         : Typeclass[T] =
    val tpeName = constValue[m.MirroredLabel]

    val cc: ReadOnlyCaseClass[Typeclass, T] = 
      new ReadOnlyCaseClass[Typeclass, T](
        //todo parent type
        typeName = TypeName("", tpeName, Nil),
        isObject = false,
        isValueClass = false,
        parameters = parametersOf[Typeclass, T, Tuple.Zip[m.MirroredElemTypes, m.MirroredElemLabels]](0),
        annotations = Seq()
      ){}

    //todo generic
    interface.join(cc)

  inline def gen[Typeclass[_], T](interface: TCInterface[Typeclass])(using m: Mirror.Of[T]): Typeclass[T] =
    inline m match
      case given sum: Mirror.SumOf[T]      => splitInternal[Typeclass, T](interface)
      case given prod: Mirror.ProductOf[T] => joinInternal[Typeclass, T](interface)

//ideally we won't have this at all
case class TCInterface[Typeclass[_]](
  join: [T] => (cc: ReadOnlyCaseClass[Typeclass, T]) => Typeclass[T],
  split: [T] => (cc: SealedTrait[Typeclass, T]) => Typeclass[T]
)

trait Print[T]:
  def (t: T).print: String

object Print:
  def join[T](ctx: ReadOnlyCaseClass[Print, T]): Print[T] = value =>
    if (ctx.isValueClass) then
      val param = ctx.parameters.head
      param.typeclass.print(param.dereference(value))
    else
      ctx.parameters.map { param =>
        param.label + " = " + param.typeclass.print(param.dereference(value))
      }.mkString(s"${ctx.typeName.short}(", ", ", ")")

  def split[T](ctx: SealedTrait[Print, T]): Print[T] = value =>
    ctx.dispatch(value) { sub => sub.typeclass.print(sub.cast(value)) }

  //how to use given here?
  inline implicit def derived[T](using Mirror.Of[T]): Print[T] = 
    Magnolia.gen[Print, T](
      TCInterface[Print](
        [T] => (cc: ReadOnlyCaseClass[Print, T]) => join(cc),
        [T] => (st: SealedTrait[Print, T]) => split(st),
      )
    )

  given Print[String] = a => a
  given Print[Int] = _.toString

enum MyList[+T] derives Print:
  case Cons(h: T, t: MyList[T])
  case End

@main
def run = println(MyList.Cons(1, MyList.Cons(2, MyList.End)).print)
