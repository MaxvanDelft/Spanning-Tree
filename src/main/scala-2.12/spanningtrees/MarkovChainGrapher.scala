package spanningtrees

/**
  * Created by maxvandelft on 30-03-17.
  */
object MarkovChainGrapher {

  type IntPartition     = Set[Set[Int]]
  type State            = IntPartition
  type Matrix[A]        = Array[Array[A]] // should become a class with a monad or so
  type TransitionMatrix = Matrix[LetterChoice]

  def header(title: String): String =
    """digraph markov_chain{
          rankdir=LR;
          label = "%s"
          node [shape = circle];

    """.format(title)

  def footer():String = "}"

//  def graphvizulize[S](title: String, chain: MarkovChain[S]):String = {
//    val states = chain.states;
//    var allTransitions = List[String]();
//    for(state <- states) {
//      allTransitions = chain.transitionsFor(state).map(tup => transitionToString(state, tup._2, tup._1)) ++ allTransitions
//    }
//    header(title) + allTransitions.foldLeft("")((a, b) => a+b) + footer();
//  }
  def graphvizulize[S](title: String, states: Seq[State], transitions: Matrix[Int]): String = {

    var allTransitions =

      for (i <- 0 to states.length - 1; initialState = states(i);
           j <- 0 to states.length - 1;    nextState = states(j)) yield (initialState, nextState, transitions(i)(j))

    header(title) + allTransitions.filter(_._3 > 0).map(transitionToString).mkString("\n") + footer();
  }

  def stateToString(s: State): String = s.map(_.toList.sorted.mkString).toList.sorted.mkString(",")


//  def transitionToString[S](initialState: S, probability: Double, nextState: S) = {
//    "\"%s\" -> \"%s\" [ label = \"%3.2f\" ];\n".format(initialState.toString, nextState.toString, probability);
//  }
  def transitionToString(initialNextCount: (State, State, Int)) = {
    val (from, to, count) = initialNextCount
    s"${stateToString(from)} -> ${stateToString(to)} [ label = $count ];"
  }
}