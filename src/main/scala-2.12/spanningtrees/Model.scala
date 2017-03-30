package spanningtrees

import java.io.PrintWriter

import scala.reflect.ClassTag
//import breeze.linalg._

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


/**
  *
  */
class Model(m: Int) {

  type IntSeqPartition  = List[List[Int]]
  type IntPartition     = Set[Set[Int]]
  type State            = IntPartition
  type Matrix[A]        = Array[Array[A]] // should become a class with a monad or so
  type TransitionMatrix = Matrix[LetterChoice]

  // bit messy: square matrix assumed
  def mapMatrix[A,B](m: Matrix[A], f: A => B)(implicit tag: ClassTag[B]): Matrix[B] = Array.tabulate[B](m.length,m.length){ (x,y) => f(m(x)(y)) }

  // answer a list of how the given list may be split in two sublists.
  // start by splitting of the head element; then the first two elements etc
  // e.g.
  // input: List(1, 2, 3)
  // splittings: Vector((List(1),List(2, 3)), (List(1, 2),List(3)), (List(1, 2, 3),List()))

  def listSplittings[T](list: Seq[T]): Seq[(Seq[T], Seq[T])] =
    (1 to list.length).map{ i => list.splitAt(i) }


  // add the given number to the last list in the given list
  def addToLastList(list: IntSeqPartition, n: Int): IntSeqPartition = {
    list match {
      case head::Nil => List(head :+ n)
      case head::tail => head :: addToLastList(tail, n)
    }
  }

  def computeNonCrossingPartitions: Seq[IntSeqPartition] = {

    // recursive helper for non-crossing partitions
    // each yielded partition is itself divided in 2 parts:
    // the enclosed part and the free part.
    // e.g. in 02,1 the 1 is enclosed; when adding 3 that cannot connect to 1.
    // so 023,1 could result, not 02,13
    //
    // A call to this method gets recursively allowed partitions of the slightly smaller problem (n-1).
    // Now we generate more of such allowed partions by the following 2 transformations:
    //
    // 1. the free partitions are each split in two, for all possible ways.
    // we add the new number to the last list of the first part of each such splitting.
    // the second part is added to the enclosed part.
    //
    // 2. another way to add the new number is to add it as its own list to any free set of a partition.
    //


    def nonCrossingPartions(n: Int): List[(IntSeqPartition, IntSeqPartition)] = {
      if (n < 0) {
        List((Nil, Nil))
      }
      else {
        val ncps1 = nonCrossingPartions(n-1)
        ncps1.flatMap{ case (free: IntSeqPartition, enclosed: IntSeqPartition) =>

          val splt = listSplittings(free)
          val mapped = splt.map{
            case (part1, part2) => (addToLastList(part1.toList, n), enclosed:::part2.toList)
          }
          val extraPartition = (free:::List(List(n)), enclosed)
          val appended = mapped.toList ::: List(extraPartition)

          appended
        }
      }
    }

    val result = nonCrossingPartions(m).map{ case (free, enclosed) => free:::enclosed}
    result
  }

  // answer some new state that results after adding the given vertical edge (from e-1 to e).
  // answer None in case it is illegal to perform this action (causing a cycle)
  def computeNextState_add_vertical(state: State, e: Int): Option[State] = {
    val e1 = e-1
    var mergedSet: Set[Int] = Set()
    val untouchedSets = state.filter{ s =>
      if (s.contains(e)) {
        if (s.contains(e1)) return None
        mergedSet ++= s
        false
      }
      else if (s.contains(e1)) {
        mergedSet ++= s
        false
      }
      else true
    }
    Some(untouchedSets + mergedSet)
  }

  // answer some new state that results after removing the given horizontal edge.
  // answer None in case it is illegal to perform this action (causing an unreachable node)
  def computeNextState_remove_horizontal(state: State, e: Int): Option[State] = {
    val eSet = Set(e)
    if (state.contains(eSet)) None
    else {
      val newState = state.map(_ - e) + eSet
      Some(newState)
    }
  }


  def multiply(a: TransitionMatrix, b: TransitionMatrix): TransitionMatrix =
    Array.tabulate(a.size, a.size)( {(row, col) =>
    var sum: LetterChoice = LetterChoice.Zero
    var i = 0
    while (i < a.size) { sum += a(row)(i) * b(i)(col); i += 1; }
    sum
  })
/*
  def multiply(m1: TransitionMatrix, m2: TransitionMatrix): TransitionMatrix = {
    val result = getEmptyTransitionMatrix
    for (i <- 0 to nStates-1;
         j <- 0 to nStates-1) {
      var newVal: LetterChoice = LetterChoice.Zero

      for (k <- 0 to nStates-1) {
        val v1 = m1(i)(k)
        val v2 = m2(k)(j)
        newVal += v1*v2
      }
      result(i)(j) = newVal
    }
    result
  }
*/

  def getEmptyTransitionMatrix: TransitionMatrix = Array.tabulate(nStates,nStates)( (x,y) => LetterChoice.Zero )

  def getSingleEdgeActionMatrix(e: Int, forHorizontal: Boolean): TransitionMatrix = {
    val result: TransitionMatrix = getEmptyTransitionMatrix

    for (i <- 0 to nStates-1) {
      val s = state(i)
      val newState = if (forHorizontal) computeNextState_remove_horizontal(s, e)
                     else                    computeNextState_add_vertical(s, e)
      newState match {
        case Some(s) => val j = stateIndex(s)
                        result(i)(j) = if (forHorizontal) LetterChoice.AddHEdge(e)
                                       else               LetterChoice.AddVEdge(e)
        case None =>
      }
    }
    result
  }
  val ncps       = computeNonCrossingPartitions

  val statesList: Vector[State] = ncps.map{ ncp => ncp.map(_.toSet).toSet }.toVector

  val statesMap: Map[State, Int] = statesList.zipWithIndex.toMap
  def nStates                    = statesList.size
  def state(i: Int): State       = statesList(i)
  def stateIndex(s: State): Int  = statesMap(s)

  def stateToString(s: State): String = s.map(_.toList.sorted.mkString).toList.sorted.mkString(",")

  println (s"m = $m")
  println (s"========")
  println (s"${statesList.size} States:")
  println (s"${statesList.take(42).zipWithIndex.map(si => s"${si._2}: ${stateToString(si._1)}").mkString("\n")}")
  println

  //println (s"${statesMap.size} Inversed states:")
  //println (s"${statesMap.toList.take(14).zipWithIndex.map(si => s"${si._2}: ${si._1._1} => ${si._1._2}").mkString("\n")}")
  //println

  val identityTransitionMatrix: TransitionMatrix =  // do not change contents!
    Array.tabulate(nStates,nStates)( (x,y) => if (x==y) LetterChoice.One else LetterChoice.Zero )

  def setDiagonalToIdentity(tm: TransitionMatrix): TransitionMatrix = {for (i <- 0 to nStates-1) tm(i)(i) = LetterChoice.One; tm }

  def makeString[A](m: Matrix[A]): String = m.map(row=>{row.map(elt=>elt.toString)}.mkString(",")).mkString("\n")
  def toSize(letterChoice: LetterChoice): Int = letterChoice.size
  def to01(  letterChoice: LetterChoice): Int = if (letterChoice.size==0) 0 else 1

  def V(e: Int) = getSingleEdgeActionMatrix(e, forHorizontal = false)
  def H(e: Int) = getSingleEdgeActionMatrix(e, forHorizontal =  true)

  def W(e: Int) = setDiagonalToIdentity(V(e))
  def G(e: Int) = setDiagonalToIdentity(H(e))

  for (i <- 1 to m) println( s"W($i):\n${makeString(W(i))}\n")
  for (i <- 0 to m) println( s"G($i):\n${makeString(G(i))}\n")

  val WW: TransitionMatrix = (1 to m).foldLeft(identityTransitionMatrix) {(tm:TransitionMatrix, i:Int) => multiply(tm, W(i))}
  val GG: TransitionMatrix = (0 to m).foldLeft(identityTransitionMatrix) {(tm:TransitionMatrix, i:Int) => multiply(tm, G(i))}

  println(  s"vertical step matrix WW:\n${makeString(WW)}\n")
  println(s"horizontal step matrix GG:\n${makeString(GG)}\n")

  val WG  = multiply(WW,GG)      ; //println(     s"E-letter matrix WG:\n${makeString(WG)}\n" )
  val GW  = multiply(GG,WW)      ; //println(     s"3-letter matrix GW:\n${makeString(GW)}\n" )
  val WGS = mapMatrix(WG, toSize); println(s"E-letter size matrix WG:\n${makeString(WGS)}\n")
  val GWS = mapMatrix(GW, toSize); println(s"3-letter size matrix GW:\n${makeString(GWS)}\n")

  val WG1 = mapMatrix(WG, to01  ); println(s"E-letter 01 matrix WG:\n${makeString(WG1)}\n")
  val GW1 = mapMatrix(GW, to01  ); println(s"3-letter 01 matrix GW:\n${makeString(GW1)}\n")

  val WGR = WG1.map(_.sum)
  val GWR = GW1.map(_.sum)

  // For a stationary matrix, we could normalize the rows of WG1 and GW1 until their sums become 0,
  // and then solve xP = I (for P=WG1,WG2).
  //
  // It is a bit easier though to solve xP = R with R the row totals of P

  // x*WGN = x
  // x*(WGN-I) = 0
  //
  // Breeze:
  // val p = P \ 0
  //
  // print makestring(p)
  //
  // make .dot file
  // http://blog.circuitsofimagination.com/2015/02/15/Markov-Chains.html

  val dotFile = new PrintWriter(s"Model$m.dot")
  dotFile.println(MarkovChainGrapher.graphvizulize("Markov structure", statesList, WGS))
  dotFile.close()


  def run {
  }

}


object Model {

  def main(args: Array[String]) = {
    for (m <- 1 to 3) new Model(m).run
  }
}