package spanningtrees

abstract class Letter {

  def actionSet: Set[Int]

  case class Compound(actionSet: Set[Int]) extends Letter

  def getVHpartition: (Seq[Int], Seq[Int]) = actionSet.toList.sorted.partition(_<0)

  def edgeNumberToString(e: Int) = s"${(('0'+e).toChar)}"

  val vhseparator = ":"
  override def toString: String = {
    if (actionSet.isEmpty) return "I"
    val (vs,hs) = getVHpartition
    val vstr = vs.reverse.map{v => edgeNumberToString(-v)}.mkString
    val hstr = hs        .map{h => edgeNumberToString( h)}.mkString
    s"$vstr$vhseparator$hstr"
  }
  def *(other: Letter): Letter = (this,other) match {
    case (Letter.One , _) => other
    case (_, Letter.One ) => this
    case (_, _          ) => Compound(this.actionSet++other.actionSet)
  }
}
object Letter {
  object One  extends Letter {def actionSet = Set.empty}

  abstract class BasicAction(e: Int) extends Letter {val actionSet = Set(e)}
  case class AddVEdge(e: Int) extends BasicAction(-e) // Note the minus!
  case class AddHEdge(e: Int) extends BasicAction( e)
}

