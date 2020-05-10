/* Magnolia, version 0.10.0. Copyright 2018 Jon Pretty, Propensive Ltd.
 *
 * The primary distribution site is: http://co.ntextu.al/
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file
 * except in compliance with the License. You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software distributed under the
 * License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
 * either express or implied. See the License for the specific language governing permissions
 * and limitations under the License.
 */
package magnolia

import language.experimental.macros
import scala.annotation.tailrec

trait Subtype[Typeclass[_], Type] extends Serializable:
  type SType <: Type
  def typeName: TypeName
  def index: Int
  def typeclass: Typeclass[SType]
  def cast: PartialFunction[Type, SType]
  def annotations: Seq[Any]
  override def toString: String = s"Subtype(${typeName.full})"

object Subtype:
  def apply[Tc[_], T, S <: T](name: TypeName,
                              idx: Int,
                              anns: Seq[Any],
                              tc: CallByNeed[Tc[S]],
                              isType: T => Boolean,
                              asType: T => S)
                             : Subtype[Tc, T] =
    new Subtype[Tc, T] with PartialFunction[T, S] {
      type SType = S
      def typeName: TypeName = name
      def index: Int = idx
      def typeclass: Tc[SType] = tc.value
      def cast: PartialFunction[T, SType] = this
      def isDefinedAt(t: T) = isType(t)
      def apply(t: T): SType = asType(t)
      def annotations: Seq[Any] = anns
      override def toString: String = s"Subtype(${typeName.full})"
    }

trait ReadOnlyParam[Typeclass[_], Type] extends Serializable:
  type PType
  def label: String
  def index: Int
  def repeated: Boolean
  def typeclass: Typeclass[PType]
  def dereference(param: Type): PType
  def annotations: Seq[Any]
  override def toString: String = s"ReadOnlyParam($label)"

object ReadOnlyParam:
  def apply[Tc[_], T, P](
    name: String,
    idx: Int,
    isRepeated: Boolean,
    typeclassParam: CallByNeed[Tc[P]],
    anns: Seq[Any]
  ): ReadOnlyParam[Tc, T] = new ReadOnlyParam[Tc, T] {
    type PType = P
    override def label: String = name
    override def index: Int = idx
    override def repeated: Boolean = isRepeated
    override def typeclass: Tc[P] = typeclassParam.value
    override def dereference(t: T): P =
      t.asInstanceOf[Product].productElement(idx).asInstanceOf[PType]
    override def annotations: Seq[Any] = anns
  }

  def valueParam[Tc[_], T, P](
    name: String,
    deref: T => P,
    isRepeated: Boolean,
    typeclassParam: CallByNeed[Tc[P]],
    anns: Seq[Any]
  ): ReadOnlyParam[Tc, T] = new ReadOnlyParam[Tc, T] {
    type PType = P
    override def label: String = name
    override def index: Int = 0
    override def repeated: Boolean = isRepeated
    override def typeclass: Tc[P] = typeclassParam.value
    override def dereference(t: T): P = deref(t)
    override def annotations: Seq[Any] = anns
  }

trait Param[Typeclass[_], Type] extends ReadOnlyParam[Typeclass, Type]:
  def default: Option[PType]
  override def toString: String = s"Param($label)"

object Param:
  def apply[Tc[_], T, P](name: String,
                         idx: Int,
                         isRepeated: Boolean,
                         typeclassParam: CallByNeed[Tc[P]],
                         defaultVal: CallByNeed[Option[P]],
                         anns: Seq[Any]): Param[Tc, T] = new Param[Tc, T] {
    type PType = P
    def label: String = name
    def index: Int = idx
    def repeated: Boolean = isRepeated
    def default: Option[PType] = defaultVal.value
    def typeclass: Tc[PType] = typeclassParam.value
    def dereference(t: T): PType = t.asInstanceOf[Product].productElement(idx).asInstanceOf[PType]
    def annotations: Seq[Any] = anns
  }

  def valueParam[Tc[_], T, P](name: String,
                              deref: T => P,
                              isRepeated: Boolean,
                              typeclassParam: CallByNeed[Tc[P]],
                              defaultVal: CallByNeed[Option[P]],
                              anns: Seq[Any])
                             : Param[Tc, T] =
    new Param[Tc, T] {
      type PType = P
      def label: String = name
      def index: Int = 0
      def repeated: Boolean = isRepeated
      def default: Option[PType] = defaultVal.value
      def typeclass: Tc[PType] = typeclassParam.value
      def dereference(t: T): PType = deref(t)
      def annotations: Seq[Any] = anns
    }

trait ReadOnlyCaseClass[Typeclass[_], Type](val typeName: TypeName,
                                            val isObject: Boolean,
                                            val isValueClass: Boolean,
                                            val parameters: Seq[ReadOnlyParam[Typeclass, Type]],
                                            val annotations: Seq[Any])
                                    extends Serializable {

  override def toString: String =
    s"ReadOnlyCaseClass(${typeName.full}, ${parameters.mkString(",")})"
}

abstract class CaseClass[Typeclass[_], Type]
                        (override val typeName: TypeName,
                         override val isObject: Boolean,
                         override val isValueClass: Boolean,
                         parameters: Seq[Param[Typeclass, Type]],
                         annotations: Seq[Any]
               ) extends ReadOnlyCaseClass[Typeclass, Type]
                                          (typeName, isObject, isValueClass, parameters,annotations):

  override def toString: String = s"CaseClass(${typeName.full}, ${parameters.mkString(",")})"
  def construct(makeParam: (p: Param[Typeclass, Type]) => p.PType): Type
  def constructEither[Err](makeParam: (p: Param[Typeclass, Type]) => Either[Err, p.PType]): Either[List[Err], Type]
  def rawConstruct(fieldValues: Seq[Any]): Type

final class SealedTrait[Typeclass[_], Type]
                       (val typeName: TypeName,
                        subtypes: Seq[Subtype[Typeclass, Type]],
                        annotations: Seq[Any])
                extends Serializable:

  override def toString: String = s"SealedTrait($typeName, Seq[${subtypes.mkString(",")}])"

  def dispatch[Return](value: Type)(handle: Subtype[Typeclass, Type] => Return): Return =
    @tailrec def rec(ix: Int): Return =
      if ix < subtypes.length then
        val sub = subtypes(ix)
        if sub.cast.isDefinedAt(value) then handle(sub) else rec(ix + 1)
      else
        throw new IllegalArgumentException(s"The given value `$value` is not a sub type of `$typeName`")
    rec(0)

final case class TypeName(owner: String, short: String, typeArguments: Seq[TypeName]):
  val full: String = s"$owner.$short"

final class debug(typeNamePart: String = "") extends scala.annotation.StaticAnnotation

private[magnolia] final case class EarlyExit[E](e: E)
    extends Exception
    with util.control.NoStackTrace

object MagnoliaUtil:
  final def checkParamLengths(fieldValues: Seq[Any], paramsLength: Int, typeName: String): Unit =
    if fieldValues.lengthCompare(paramsLength) != 0 then
      val msg = "`" + typeName + "` has " + paramsLength + " fields, not " + fieldValues.size
      throw new java.lang.IllegalArgumentException(msg)

  final def keepLeft[A](values: Either[A, _]*): List[A] =
    values.toList.collect { case Left(v) => v }