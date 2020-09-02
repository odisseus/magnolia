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
package magnolia.examples

import scala.language.experimental.macros
import magnolia._

/**
  * Type class for copying an instance of some type `T`,
  * thereby replacing certain fields with other values.
  */
sealed abstract class Patcher[T] {

  /**
    * Returns a copy of `value` whereby all non-null elements of `fieldValues`
    * replace the respective fields of `value`.
    * For all null elements of `fieldValues` the original value of the
    * respective field of `value` is maintained.
    *
    * If the size of `fieldValues` doesn't exactly correspond to the
    * number of fields of `value` an [[IllegalArgumentException]] is thrown.
    */
  def patch(value: T, fieldValues: Seq[Any]): T
}

object Patcher extends LowerPriorityPatcher {

  type Typeclass[T] = Patcher[T]

  def combine[T](ctx: CaseClass[Patcher, T]): Patcher[T] =
    new Patcher[T] {
      def patch(value: T, fieldValues: Seq[Any]): T = {
        if (fieldValues.lengthCompare(ctx.parameters.size) != 0) {
          throw new IllegalArgumentException(
            s"Cannot patch value `$value`, expected ${ctx.parameters.size} fields but got ${fieldValues.size}"
          )
        }
        val effectiveFields = ctx.parameters.zip(fieldValues).map {
          case (param, x) => if (x.asInstanceOf[AnyRef] ne null) x else param dereference value
        }
        ctx.rawConstruct(effectiveFields)
      }
    }

  def dispatch[T](ctx: SealedTrait[Patcher, T]): Patcher[T] =
    new Patcher[T] {
      def patch(value: T, fieldValues: Seq[Any]): T =
        ctx.dispatch(value)(sub => sub.typeclass.patch(sub cast value, fieldValues))
    }

  implicit def gen[T]: Patcher[T] = macro Magnolia.gen[T]
}

sealed abstract class LowerPriorityPatcher {

  private[this] val _forSingleValue =
    new Patcher[Any] {
      def patch(value: Any, fieldValues: Seq[Any]): Any = {
        if (fieldValues.lengthCompare(1) != 0)
          throw new IllegalArgumentException(
            s"Cannot patch single value `$value` with patch sequence of size ${fieldValues.size}"
          )
        val head = fieldValues.head
        if (head.getClass != value.getClass)
          throw new IllegalArgumentException(
            s"Illegal patch value type. Expected `${value.getClass}` but got `${head.getClass}`"
          )
        head
      }
    }

  // once https://github.com/propensive/magnolia/issues/58 is fixed this can be marked `implicit`
  def forSingleValue[T]: Patcher[T] = _forSingleValue.asInstanceOf[Patcher[T]]
}
