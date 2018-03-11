package spanningtrees

import breeze.math.Semiring
/**
  * Attempt to use Breeze matrix facilities with LetterChoice.
  *
  * Should be activated for use by having an implicit value in scope, e.g.
  *
  *   implicit object LetterChoiceSemiring extends LetterChoiceSemiring
  *   def identityTransitionMatrix = DenseMatrix.eye[LetterChoice](nStates)
  *
  * However, the compile errors come up of this type:
  *
  * Error:(181, 63) ambiguous implicit values:
  * both method zeroFromSemiring in trait ZeroLowPriority of type
  *    [T](implicit evidence$1: breeze.math.Semiring[T])breeze.storage.Zero[T]
  * and method ObjectZero in trait ZeroVeryLowPriority of type
  *    [T <: AnyRef]=> breeze.storage.Zero[T]
  * match expected type breeze.storage.Zero[spanningtrees.LetterChoice]
  *   def identityTransitionMatrix = DenseMatrix.eye[LetterChoice](nStates)
  *
  * Error:(181, 63) could not find implicit value for evidence parameter of type
  * breeze.storage.Zero[spanningtrees.LetterChoice]
  *   def identityTransitionMatrix = DenseMatrix.eye[LetterChoice](nStates)
  *
  * There is one reference to this problem:
  *
  * https://github.com/scalanlp/breeze/issues/510
  *
  * The issue is not resolved so we don't use this LetterChoiceSemiring
  */
class LetterChoiceSemiring extends Semiring[LetterChoice] {
  override def zero: LetterChoice = LetterChoice.Zero
  override def one : LetterChoice = LetterChoice.One
  override def  +(a: LetterChoice, b: LetterChoice): LetterChoice = a+b
  override def  *(a: LetterChoice, b: LetterChoice): LetterChoice = a*b
  override def ==(a: LetterChoice, b: LetterChoice): Boolean      = a==b
  override def !=(a: LetterChoice, b: LetterChoice): Boolean      = a!=b
}
