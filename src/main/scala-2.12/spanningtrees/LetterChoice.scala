package spanningtrees

class LetterChoice(val letters: Set[Letter]) {
  import LetterChoice.{Zero,One}

  def size = letters.size

  def +(other: LetterChoice): LetterChoice = (this,other) match {
    case (Zero, _) => other
    case (_, Zero) => this
    case (_, _)    => new LetterChoice(this.letters++other.letters)
  }
  def *(other: LetterChoice): LetterChoice = (this,other) match {
    case (Zero, _) => Zero
    case (_, Zero) => Zero
    case (One , _) => other
    case (_, One ) => this
    case (_,  _  ) => new LetterChoice(distributedAddMultiply(this.letters.toList, other.letters.toList).toSet) ///// TBD
  }
  def distributedAddMultiply (letters1: List[Letter], letters2: List[Letter]): List[Letter] = {
    letters1.foldLeft(Nil:List[Letter]) {(list: List[Letter], letter1: Letter) => distributedMultiply(letter1, letters2):::list}
  }
  def distributedMultiply (letter1: Letter, letters: List[Letter]): List[Letter] = {
    letters.foldLeft(List[Letter]()) {(list: List[Letter], letter2: Letter) => (letter1*letter2)::list}
  }

  // C*D: cartesian product over the choices of C and D

  override def toString: String = if (letters.isEmpty) "@" else letters.mkString("|")
  /*
    def compactToString: String = if (letters.isEmpty) "0"
                                  else {
                                    val s = letters.size
                                    if (s ==1 && letters==Set(Letter.One)) "I"
                                    else s.toString
                                  }
  */
}
object LetterChoice {
  object Zero extends LetterChoice(Set.empty)
  object One  extends LetterChoice(Set(Letter.One))
  case class AddVEdge(e: Int) extends LetterChoice(Set(Letter.AddVEdge(e)))
  case class AddHEdge(e: Int) extends LetterChoice(Set(Letter.AddHEdge(e)))
}

