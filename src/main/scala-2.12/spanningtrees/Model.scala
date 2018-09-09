package spanningtrees

import java.io.PrintWriter

import scala.reflect.ClassTag
import breeze.linalg._
import eigSym.EigSym

import scala.collection.mutable

/**
  *
  */
class Model(m: Int, traceLevel: Int, traceSpecifiers: Set[String]) {

  type IntSeqPartition                = List[List[Int]]
  type IntPartition                   = Set[Set[Int]]
  type Partition                      = IntPartition
  type Matrix[A]                      = Array[Array[A]] // should become a class with a monad or so
  type PartitionAdjacencyMatrix       = Matrix[LetterChoice] // instead of 0's and 1's this contains letter choices
  type PartitionProbabilityMatrix     = Matrix[(Double, LetterChoice)] // for each letterchoice there is a probability per letter in the choice
  type PartitionLetterAdjacencyMatrix = Matrix[Int]

  def makeString[A](m: Matrix[A]): String = m.map(row=>{row.map(elt=>elt.toString)}.mkString(",")).mkString("\n")
  def toSize(letterChoice: LetterChoice): Int = letterChoice.size
  def to01(  letterChoice: LetterChoice): Int = if (letterChoice.size==0) 0 else 1

  import Model._
  def trace_eigenvalues      = traceLevel >= 4 || traceSpecifiers.contains(TRACESPECIFIER_EIGENVALUES)
  def trace_partitions       = traceLevel >= 1 || traceSpecifiers.contains(TRACESPECIFIER_PARTITIONS)


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

  // answer some new partition that results after adding the given vertical edge (from e-1 to e).
  // answer None in case it is illegal to perform this action (causing a cycle)
  def computeNextPartition_add_vertical(partition: Partition, e: Int): Option[Partition] = {
    val e1 = e-1
    var mergedSet: Set[Int] = Set()
    val untouchedSets = partition.filter{ s =>
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

  // answer some new partition that results after removing the given horizontal edge.
  // answer None in case it is illegal to perform this action (causing an unreachable node)
  def computeNextPartition_remove_horizontal(partition: Partition, e: Int): Option[Partition] = {
    val eSet = Set(e)
    if (partition.contains(eSet)) None
    else {
      val newPartition = partition.map(_ - e) + eSet
      Some(newPartition)
    }
  }


  def multiply(a: PartitionAdjacencyMatrix, b: PartitionAdjacencyMatrix): PartitionAdjacencyMatrix =
    Array.tabulate(a.size, a.size)( {(row, col) =>
    var sum: LetterChoice = LetterChoice.Zero
    var i = 0
    while (i < a.size) { sum += a(row)(i) * b(i)(col); i += 1; }
    sum
  })
/*
  def multiply(m1: TransitionMatrix, m2: TransitionMatrix): TransitionMatrix = {
    val result = getEmptyTransitionMatrix
    for (i <- 0 to nPartitions-1;
         j <- 0 to nPartitions-1) {
      var newVal: LetterChoice = LetterChoice.Zero

      for (k <- 0 to nPartitions-1) {
        val v1 = m1(i)(k)
        val v2 = m2(k)(j)
        newVal += v1*v2
      }
      result(i)(j) = newVal
    }
    result
  }
*/

  def getEmptyTransitionMatrix: PartitionAdjacencyMatrix = Array.tabulate(nPartitions,nPartitions)((x, y) => LetterChoice.Zero )

  def getSingleEdgeActionMatrix(e: Int, forHorizontal: Boolean): PartitionAdjacencyMatrix = {
    val result: PartitionAdjacencyMatrix = getEmptyTransitionMatrix

    for (i <- 0 to nPartitions-1) {
      val s = partition(i)
      val newPartition = if (forHorizontal) computeNextPartition_remove_horizontal(s, e)
                         else               computeNextPartition_add_vertical     (s, e)
      newPartition match {
        case Some(s) => val j = partitionIndex(s)
                        result(i)(j) = if (forHorizontal) LetterChoice.AddHEdge(e)
                                       else               LetterChoice.AddVEdge(e)
        case None =>
      }
    }
    result
  }

  val ncps       = computeNonCrossingPartitions.reverse

  val partitionsList: scala.Vector[Partition] = ncps.map{ ncp => ncp.map(_.toSet).toSet }.toVector

  val partitionsMap: Map[Partition, Int] = partitionsList.zipWithIndex.toMap
  def nPartitions                        = partitionsList.size
  def partition(i: Int): Partition       = partitionsList(i)
  def partitionIndex(s: Partition): Int  = partitionsMap(s)

  def partitionToString(s: Partition): String = s.map(_.toList.sorted.mkString).toList.sorted.mkString(",")


  def run {

    println (s"m = $m")
    println (s"========")
    println (s"${partitionsList.size} Partitions:")
    println (s"${partitionsList.take(42).zipWithIndex.map(si => s"${si._2}: ${partitionToString(si._1)}").mkString("\n")}")
    println

    //println (s"${partitionsMap.size} Inversed partitions:")
    //println (s"${partitionsMap.toList.take(14).zipWithIndex.map(si => s"${si._2}: ${si._1._1} => ${si._1._2}").mkString("\n")}")
    //println

    val identityTransitionMatrix: PartitionAdjacencyMatrix =  // do not change contents!
      Array.tabulate(nPartitions,nPartitions)( (x,y) => if (x==y) LetterChoice.One else LetterChoice.Zero )

    def setDiagonalToIdentity(tm: PartitionAdjacencyMatrix): PartitionAdjacencyMatrix = {for (i <- 0 to nPartitions-1) tm(i)(i) = LetterChoice.One; tm }

    def V(e: Int) = getSingleEdgeActionMatrix(e, forHorizontal = false)
    def H(e: Int) = getSingleEdgeActionMatrix(e, forHorizontal =  true)

    def W(e: Int) = setDiagonalToIdentity(V(e))
    def G(e: Int) = setDiagonalToIdentity(H(e))

    //for (i <- 1 to m) println( s"W($i):\n${makeString(W(i))}\n")
    //for (i <- 0 to m) println( s"G($i):\n${makeString(G(i))}\n")

    val WW: PartitionAdjacencyMatrix = (1 to m).foldLeft(identityTransitionMatrix) { (tm:PartitionAdjacencyMatrix, i:Int) => multiply(tm, W(i))}
    val GG: PartitionAdjacencyMatrix = (0 to m).foldLeft(identityTransitionMatrix) { (tm:PartitionAdjacencyMatrix, i:Int) => multiply(tm, G(i))}

    println(  s"vertical step matrix WW:\n${makeString(WW)}\n")
    println(s"horizontal step matrix GG:\n${makeString(GG)}\n")

    val WG  = multiply(WW,GG)      ; println(     s"E-letter matrix WG:\n${makeString(WG)}\n" )
    val GW  = multiply(GG,WW)      ; println(     s"3-letter matrix GW:\n${makeString(GW)}\n" )

    val WGS = mapMatrix(WG, toSize); println(s"E-letter size matrix WGS:\n${makeString(WGS)}\n")
    val GWS = mapMatrix(GW, toSize); println(s"3-letter size matrix GWS:\n${makeString(GWS)}\n")

    //
    // make .dot file
    // http://blog.circuitsofimagination.com/2015/02/15/Markov-Chains.html
    val dotFile = new PrintWriter(s"Model$m.dot")
    dotFile.println(MarkovChainGrapher.graphvizulize("Markov structure", partitionsList, WGS))
    dotFile.close()

    /*
    // the following code is experimental; it attempts to use Breeze, but that fails

    // val WG1 = mapMatrix(WG, to01  ); println(s"E-letter 01 matrix WG1:\n${makeString(WG1)}\n")
    // val GW1 = mapMatrix(GW, to01  ); println(s"3-letter 01 matrix GW1:\n${makeString(GW1)}\n")

    // This does not work well: matrix created mirrored over the diagonal
    // val DWGS = new DenseMatrix(WGS.length, WGS.length, WGS.flatten)
    // val DGWS = new DenseMatrix(GWS.length, GWS.length, GWS.flatten)

    //val DWGS = DenseMatrix.tabulate(WGS.length, WGS.length){case (i, j) => WGS(i)(j).toDouble}
    //val DGWS = DenseMatrix.tabulate(GWS.length, GWS.length){case (i, j) => GWS(i)(j).toDouble}

    //println(s"E-letter dense matrix DWGS:\n${DWGS.toString}\n")
    //println(s"3-letter dense matrix DGWS:\n${DGWS.toString}\n")

    //val zv = DenseVector.ones[Double](GWS.length)
    //val p1 = DWGS \ zv
    //val p2 = DGWS \ zv

    //println(s"E-letter dense matrix DWGS \\ ones:\n${p1.toString}\n")
    //println(s"3-letter dense matrix DWGS \\ ones:\n${p2.toString}\n")

    //val WGR = WG1.map(_.sum)
    //val GWR = GW1.map(_.sum)

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

    // end of experimental code
    */

    GlobalResults.setNumberOfNodesAndEdges(m=m, graph="PartitionGraph", letterType="ELetter", numNodes=nPartitions, numEdges=mapMatrix(WG,toSize).map(_.sum).sum)
    GlobalResults.setNumberOfNodesAndEdges(m=m, graph="PartitionGraph", letterType="3Letter", numNodes=nPartitions, numEdges=mapMatrix(GW,toSize).map(_.sum).sum)

    // false::true::Nil map analyse_E_or_3_LetterMatrix   would be the same as the next 2 lines
    analyse_E_or_3_LetterMatrix(do3Letter=false, E_or_3_LetterMatrix=WG)
    analyse_E_or_3_LetterMatrix(do3Letter= true, E_or_3_LetterMatrix=GW)
    analyse_E_or_3_LetterMatrixStartPartition(do3Letter=false, E_or_3_LetterMatrix=WG)
    analyse_E_or_3_LetterMatrixStartPartition(do3Letter= true, E_or_3_LetterMatrix=GW)
    // doStateWithEndPartition: Create states (letter, end partition) as opposed to states (start partition, letter)
  }


  def analyse_E_or_3_LetterMatrix(do3Letter: Boolean, E_or_3_LetterMatrix: PartitionAdjacencyMatrix) {
    // we only do 1 type of letter here. A for-loop would allow for both E-letters and 3-letters

    // Now compute probabilities for random trees:
    //   what is the chance to get a specific letter at a specific partition
    // All letters that induce the same partition transition must have the same chance. Why? Just logical?
    //
    // 1. To compute the probability matrix we consider adjacency matrices for partition-letter combinations,
    //    so this yields a Markov chain. Then between 2 nodes there is at most 1 edge, no multi-edges. The
    //    partitions in the partition-letter combination (for which we compute the adjacency matrix) have to
    //    either all be start partitions or they are all end partitions.
    //
    // 2. Of such matrices we compute the maximum eigenvalue Lambda
    //    and corresponding left eigenvector EigU and right eigenvector EigV.
    //
    // 3. Compute the stationary distribution
    //
    // 4. Compute the probability matrix of the partition-letter combinations
    //
    // 5. Finally we can get similar matrices back like WG and GW that have at each element
    //    a probability, next to the set of letters for that partition transition.
    //    Note that for each of the letters the probability is/should be the same.
    //
    // Technical considerations:
    //
    // Naming: PE and P3 are such matrices for E letters and 3 letters.
    // FTTB we only do PE, for E-letters (from WG)
    // And we only want to use meaningful partition-letter combinations, to make the matrix as small as possible
    //
    // so we get a bigger index set for PE.
    // Say we can get back to the WG index using the field ".partition", e.g. "i.partition".
    // And we get the letter by "i.letter"
    //
    // PE(i,j) = if j.letter in WG(i.partition, j.partition) then 1 else 0
    //
    // Step 1. Create PartitionLetterAdjacencyMatrix
    // Step 1.1 Find meaningful partition-letter combinations and map to partition indexes (used in WG) and letters
    //
    //   A combination of partition p and letter l is "meaningful" if there is a transition with letter l to partition p
    //
    //   Why "meaningful" rather than just the carthesian product of partions and letters?
    //   The latter would yield impractically large matrices, with (P*L)^2 elements,
    //   where P and L are the number of partitions and letters.
    //
    //   We also need reverse mapping, for a dense matrix display:
    //   - mapPIndexAndLetterToPLIndex: from a partition and a letter to the row in the PartitionLetter matrix
    //     A row represents the from-node in the markov chain; it represents both a partition and a letter
    //   - mapPIndexForAnyLetterToPLIndex from a partition to any column in the PartitionLetter matrix which relates to that partition, irrespective of the letter
    //     Note that for getting the column you cannot use the previous mapping, because the letter there belongs to the from-node
    //
    // In the process of computing the PartitionLetterAdjacencyMatrix,
    // we naively identify the meaningful combinations; we do not know in advance how many ther
    // nPLs counts these combinations, identified so far.
    // Finally nPLs has become the dimension of the resulting PartitionLetterAdjacencyMatrix

    var mapPIndexAndLetterToPLIndex    = scala.collection.mutable.Map[(Int, Letter), Int]()
    var mapPIndexForAnyLetterToPLIndex = scala.collection.mutable.Map[Int, Int]()
    var mapPLIndexToPIndex             = scala.collection.mutable.Map[Int, Int]()
    var mapPLIndexToLetter             = scala.collection.mutable.Map[Int, Letter]()

    println(s"Letter type (3/E): ${if (do3Letter) "3" else "E"}")
    println("="*50)

    var nPLs = 0

    for (i      <- 0 until nPartitions; row = E_or_3_LetterMatrix(i);
         j      <- 0 until nPartitions; letterSet = row(j).letters; pColIndex = j;
         letter <- letterSet
         // pColIndex corresponds to a column, i.e. an end partition.
         // Define (end partition, letter) node if it had not been already
         if !mapPIndexAndLetterToPLIndex.isDefinedAt((pColIndex,letter))
    ) {
      val plIndex = nPLs
      mapPIndexAndLetterToPLIndex((pColIndex,letter)) = plIndex
      mapPLIndexToPIndex(plIndex) = pColIndex
      mapPLIndexToLetter(plIndex) = letter
      nPLs += 1
    }

    println("Mapping from partition-letter-index to partition index and letter")
    for (i <- 0 until nPLs) {
      println(f"$i%2d ${mapPLIndexToPIndex(i)}%2d ${mapPLIndexToLetter(i)}")
    }
    println

    // Step 1.2 Using these mappings fill the matrix
    // Recall: The nodes correspond to (letter, end partition) or shorthand (l,p).
    // In any sequence l1 p1 l2 p2 of two end partitions and two letters the possibility of the partition
    // transition from (l1,p1) to (l2,p2) depends ONLY on p1,l2 and p2; NOT on l1
    val P3E: PartitionLetterAdjacencyMatrix = Array.tabulate(nPLs, nPLs)( {(row, col) =>
      val pIndex1 = mapPLIndexToPIndex(row) // index of end partition p1 in some state (l1,p1), though it now serves as a begin partition in the transition from p1 to p2
    val pIndex2 = mapPLIndexToPIndex(col) // index of p2 in (l2,p2)
    val letter  = mapPLIndexToLetter(col) // letter l2 in (l2,p2), a letter that potentially causes partition transition from p1 to p2
      if (E_or_3_LetterMatrix(pIndex1)(pIndex2).letters.contains(letter)) 1 else 0
    })
    println
    println(s"Partition Letter Matrix:\n${makeString(P3E)}\n")

    // 2. Compute the maximum eigenvalue Lambda
    //    and corresponding left eigenvector EigU and right eigenvector EigV.
    //    Breeze computes the right eigenvectors only directly;
    //    But you get left eigenvectors when you do the operation on the transposed matrix

    println(s"Computing eigenvalues...")

    val DPE = DenseMatrix.tabulate(nPLs, nPLs){case (i, j) => (P3E(i)(j)).toDouble}
    val DPE_Transposed = DPE.t

    val eigStuff_Right = eig(DPE)
    val eigStuff_Left  = eig(DPE_Transposed)

    // check that imaginary parts of the eigenvalues are close to 0
    val NONZERO_TOLERANCE = 1e-10 // observed was: 9e-15
    for (ev <- eigStuff_Right.eigenvaluesComplex) {
      if (Math.abs(ev) > NONZERO_TOLERANCE) {
        println(s"WARNING: Eigenvalue with nonzero imaginary part: $ev")
      }
    }
    for (ev <- eigStuff_Left.eigenvaluesComplex) {
      if (Math.abs(ev) > NONZERO_TOLERANCE) {
        println(s"WARNING: Eigenvalue with nonzero imaginary part: $ev")
      }
    }

    //val eigenvalues = eigStuff.eigenvalues
    val maxLambda_Right      =    max(eigStuff_Right.eigenvalues)
    val maxLambda_Left       =    max(eigStuff_Left .eigenvalues)
    val maxLambdaIndex_Right = argmax(eigStuff_Right.eigenvalues)
    val maxLambdaIndex_Left  = argmax(eigStuff_Left .eigenvalues)

    /* Uncomment if desired:
    println(s"lambdas right: ${eigStuff_Right.eigenvalues}")
    println(s"lambdas left: ${eigStuff_Left.eigenvalues}")
    println
    println(s"eigVectors right:\n${eigStuff_Right.eigenvectors}")
    println
    println(s"eigVectors left:\n${eigStuff_Left.eigenvectors}")
    println
    */
    val eigVector_maxLambda_Right = eigStuff_Right.eigenvectors(::, maxLambdaIndex_Right)
    val eigVector_maxLambda_Left  = eigStuff_Left .eigenvectors(::, maxLambdaIndex_Left )

    println(s"maxLambda_Right: ${maxLambda_Right}")
    println(s"maxLambda_Left : ${maxLambda_Left }")
    /* Uncomment if desired:
    println(s"maxLambdaIndex_Right: ${maxLambdaIndex_Right}")
    println(s"maxLambdaIndex_Left : ${maxLambdaIndex_Left }")
    */
    println(s"eigVector_maxLambda_Right: ${eigVector_maxLambda_Right}")
    println(s"eigVector_maxLambda_Left : ${eigVector_maxLambda_Left}")
    println

    // Step 3. Compute the stationary distribution

    val eigVector_maxLambda_LeftTimesRight = eigVector_maxLambda_Left *:* eigVector_maxLambda_Right
    val sum_values = sum(eigVector_maxLambda_LeftTimesRight)
    val eigVector_maxLambda_LeftTimesRight_sum_1 = eigVector_maxLambda_LeftTimesRight / sum_values

    println(s"eigVector_maxLambda_LeftTimesRight: ${eigVector_maxLambda_LeftTimesRight}")
    println(s"eigVector_maxLambda_LeftTimesRight_sum_1: ${eigVector_maxLambda_LeftTimesRight_sum_1}")
    println

    // Step 4. Compute the probability matrix of the partition-letter combinations

    val v = eigVector_maxLambda_Right
    val lambda = maxLambda_Right

    //    val densePartitionLetterProbabilityMatrix = DenseMatrix.tabulate(nPLs, nPLs){case (i, j) =>
    //      (u(j)*P3E(i)(j))/(lambda*u(i))
    //    }
    //
    //    println(s"PartitionLetterProbabilityMatrix: ${densePartitionLetterProbabilityMatrix}")
    //    println


    val partitionLetterProbabilityMatrix = Array.tabulate[Double](nPLs,nPLs) { case (i,j) => (v(j)*P3E(i)(j))/(lambda*v(i)) }

    def formatProbability(d: Double) = f"$d%1.3f".replace("0.",".").replace(".000",".   ")
    def formatProbabilityMatrix(pm: Matrix[Double]) = pm.map{ row => row.map(formatProbability).mkString(" ")}.mkString("\n")
    def formatProbabilityAndLetterChoice(plc: (Double, LetterChoice)): String = s"${formatProbability(plc._1)}=>${plc._2}"

    // only print the Probability matrix for small m

    if (m <= 1)
    {
      println(s"Probability matrix:\n${formatProbabilityMatrix(partitionLetterProbabilityMatrix)}")
      println
    }


    // We have states (end partition, letter): transitions correspond to sequences l1pl2q
    // Check that P(l1plq)=P(l2plq) for all l1,l2 that can proceed p
    // Check that P(lpl1q)=P(lpl2q) for all l1,l2 that cause transition pq

    // Now that we checked P(l1pl2q)=P(l3pl4q) for all l1,l3 that can proceed p and all l2,l4
    // that cause transition pq we may compute the matrix A where: a_{pq} = P(l1pl2q) for any l1
    // that can proceed p and any l2 that causes transition pq


    // Step 5. Derive the denser probability matrix notation for states (letter, end partition)
    // For any transition pq, find any l1 that can proceed p and any l2 that causes transition pq
    // Then let a_{pq} = P( (l1,p) , (l2,q) ), which we obtained earlier
    val ppm: PartitionProbabilityMatrix = Array.tabulate[(Double, LetterChoice)](nPartitions,nPartitions) { case (p,q) =>
      val letterSet        = E_or_3_LetterMatrix(p)(q)
      val letters          = letterSet.letters
      val probability      = if (letters.isEmpty) 0 else {
        def letterThatCanProceed(pindex: Int) = E_or_3_LetterMatrix.collectFirst{
          case row if row(pindex).size > 0 => row(pindex).letters.head
        }.get // we are sure that every column in the partition matrix contains a letter, so we
              // can get the result without checking whether it exists.
        val l1       = letterThatCanProceed(p)      // some letter that can proceed p
        val l2       = letters.head                 // some letter that causes transition pq
        val plIndex1 = mapPIndexAndLetterToPLIndex((p,l1))
        val plIndex2 = mapPIndexAndLetterToPLIndex((q,l2))
        partitionLetterProbabilityMatrix(plIndex1)(plIndex2)
      }
      (probability, letterSet)
    }

    val nLetterOccurences = mapMatrix(E_or_3_LetterMatrix, toSize).map(_.sum).sum
    println(s"Number of letter occurences in Partition Matrix = $nLetterOccurences"); println
    println(s"Markov matrix dimension = $nPLs")                                     ; println

    // This code is nice, but creates a big string so that the VM may run out of memory with m=4:
    //
    //def makePString[A](m: PartitionProbabilityMatrix): String = m.map(row=>{row.map(elt=>formatProbabilityAndLetterChoice(elt))}.mkString(",")).mkString("\n")
    //
    //println(s"Dense probability matrix:\n${makePString(ppm)}\n")
    //

    println(s"Dense probability matrix:")
    ppm.map{row => {println( row.map(elt=>formatProbabilityAndLetterChoice(elt)).mkString(","))}}
    println


    println(s"Dense probability matrix for states: (letter, end partition), and letter type: ${if (do3Letter) "3" else "E"}")
    ppm.map{row => {println( row.map(elt=>formatProbability(elt._1)).mkString(","))}}
    println

    val ltype = {if(do3Letter) "3Letter" else "ELetter"}
    GlobalResults.setNumberOfNodesAndEdges(m=m, graph="LetterEndPartitionGraph", letterType=ltype, numNodes=nPLs, numEdges=P3E.map(_.sum).sum)
  } // run method






  def parryMatrix(A:Array[Array[Int]]) = {
    val n = A.size
    val DPE = DenseMatrix.tabulate(n,n){case (i, j) => (A(i)(j)).toDouble}
    val DPE_Transposed = DPE.t

    val eigStuff_Right = eig(DPE)
    val eigStuff_Left  = eig(DPE_Transposed)

    // check that imaginary parts of the eigenvalues are close to 0
    val NONZERO_TOLERANCE = 1e-10 // observed was: 9e-15
    for (ev <- eigStuff_Right.eigenvaluesComplex) {
      if (Math.abs(ev) > NONZERO_TOLERANCE) {
        println(s"WARNING: Eigenvalue with nonzero imaginary part: $ev")
      }
    }
    for (ev <- eigStuff_Left.eigenvaluesComplex) {
      if (Math.abs(ev) > NONZERO_TOLERANCE) {
        println(s"WARNING: Eigenvalue with nonzero imaginary part: $ev")
      }
    }

    //val eigenvalues = eigStuff.eigenvalues
    val maxLambda_Right      =    max(eigStuff_Right.eigenvalues)
    val maxLambda_Left       =    max(eigStuff_Left .eigenvalues)
    val maxLambdaIndex_Right = argmax(eigStuff_Right.eigenvalues)
    val maxLambdaIndex_Left  = argmax(eigStuff_Left .eigenvalues)

    if (trace_eigenvalues) {
      println(s"lambdas right: ${eigStuff_Right.eigenvalues}")
      println(s"lambdas left: ${eigStuff_Left.eigenvalues}")
      println
      println(s"eigVectors right:\n${eigStuff_Right.eigenvectors}")
      println
      println(s"eigVectors left:\n${eigStuff_Left.eigenvectors}")
      println
    }
    val eigVector_maxLambda_Right = eigStuff_Right.eigenvectors(::, maxLambdaIndex_Right)
    val eigVector_maxLambda_Left  = eigStuff_Left .eigenvectors(::, maxLambdaIndex_Left )

    //println(s"maxLambda_Right: ${maxLambda_Right}")
    //println(s"maxLambda_Left : ${maxLambda_Left }")




    /* Uncomment if desired:
    println(s"maxLambdaIndex_Right: ${maxLambdaIndex_Right}")
    println(s"maxLambdaIndex_Left : ${maxLambdaIndex_Left }")
    */


    //println(s"eigVector_maxLambda_Right: ${eigVector_maxLambda_Right}")
    //println(s"eigVector_maxLambda_Left : ${eigVector_maxLambda_Left}")
    //println


    // Step 3. Compute the stationary distribution

    val eigVector_maxLambda_LeftTimesRight = eigVector_maxLambda_Left *:* eigVector_maxLambda_Right
    val sum_values = sum(eigVector_maxLambda_LeftTimesRight)
    val eigVector_maxLambda_LeftTimesRight_sum_1 = eigVector_maxLambda_LeftTimesRight / sum_values


    //println(s"eigVector_maxLambda_LeftTimesRight: ${eigVector_maxLambda_LeftTimesRight}")
    //println(s"eigVector_maxLambda_LeftTimesRight_sum_1: ${eigVector_maxLambda_LeftTimesRight_sum_1}")
    //println


    // Step 4. Compute the probability matrix of the partition-letter combinations

    val v = eigVector_maxLambda_Right
    val lambda = maxLambda_Right

    //    val densePartitionLetterProbabilityMatrix = DenseMatrix.tabulate(nPLs, nPLs){case (i, j) =>
    //      (u(j)*P3E(i)(j))/(lambda*u(i))
    //    }
    //
    //    println(s"PartitionLetterProbabilityMatrix: ${densePartitionLetterProbabilityMatrix}")
    //    println


    Array.tabulate[Double](n,n) { case (i,j) => (v(j)*A(i)(j))/(lambda*v(i)) }
  }

  // ===================================================================================================================
  // ===================================================================================================================
  // ===================================================================================================================
  // ===================================================================================================================
  // ===================================================================================================================
  // ===================================================================================================================
  // ===================================================================================================================

  def analyse_E_or_3_LetterMatrixStartPartition(do3Letter: Boolean, E_or_3_LetterMatrix: PartitionAdjacencyMatrix) {
    var mapPIndexAndLetterToPLIndex    = scala.collection.mutable.Map[(Int, Letter), Int]()
    var mapPIndexForAnyLetterToPLIndex = scala.collection.mutable.Map[Int, Int]()
    var mapPLIndexToPIndex             = scala.collection.mutable.Map[Int, Int]()
    var mapPLIndexToLetter             = scala.collection.mutable.Map[Int, Letter]()

    //println(s"Letter type (3/E): ${if (do3Letter) "3" else "E"}")
    //println("="*50)

    var nPLs = 0

    for (i      <- 0 until nPartitions; row = E_or_3_LetterMatrix(i);  startPartitionIndex = i;
         j      <- 0 until nPartitions; letterSet = row(j).letters;
         letter <- letterSet
          // pColIndex corresponds to a column, i.e. an end partition.
          // Define nodes (letter, start partition)
         ) {
            val plIndex = nPLs
            mapPIndexAndLetterToPLIndex((startPartitionIndex,letter)) = plIndex
            mapPLIndexToPIndex(plIndex) = startPartitionIndex;
            mapPLIndexToLetter(plIndex) = letter
            nPLs += 1
    }

    //println("Mapping from partition-letter-index to partition index and letter")
    //for (i <- 0 until nPLs) {
    //  println(f"$i%2d ${mapPLIndexToPIndex(i)}%2d ${mapPLIndexToLetter(i)}")
    //}
    //println

    // Step 1.2 Using these mappings fill the matrix
    // Recall: The nodes correspond to (start partition, letter) or shorthand (l,p).
    // In any sequence p1 l1 p2 l2 of two end partitions and two letters the possibility of the partition
    // transition from (p1,l1) to (p2,l2) depends ONLY on p1,l1 and p2; NOT on l2
    val P3E: PartitionLetterAdjacencyMatrix = Array.tabulate(nPLs, nPLs)( {(row, col) =>
      val pIndex1 = mapPLIndexToPIndex(row) // index of p1 in (l1,p1)
      val letter  = mapPLIndexToLetter(row) // letter l1 in (p1,l1), a letter that potentially causes partition transition from p1 to p2
      val pIndex2 = mapPLIndexToPIndex(col) // index of start partition p2, though it now serves as an end partition in some state (p2,l2)
      if (E_or_3_LetterMatrix(pIndex1)(pIndex2).letters.contains(letter)) 1 else 0
    })
    //println
    //println(s"Partition Letter Matrix:\n${makeString(P3E)}\n")

    val partitionLetterProbabilityMatrix = parryMatrix(P3E)

    def formatProbability(d: Double) = f"$d%1.3f".replace("0.",".").replace(".000",".   ")
    def formatProbabilityMatrix(pm: Matrix[Double]) = pm.map{ row => row.map(formatProbability).mkString(" ")}.mkString("\n")
    def formatProbabilityAndLetterChoice(plc: (Double, LetterChoice)): String = s"${formatProbability(plc._1)}=>${plc._2}"

    // only print the Probability matrix for small m

    if (m <= 1)
    {
      println(s"Probability matrix:\n${formatProbabilityMatrix(partitionLetterProbabilityMatrix)}")
      println
    }

    // We have states (start partition, letter): transitions correspond to sequences pl1ql2
    // Check that P(p1l1ql)=P(p2l2ql) for all (p1,l1), (p2,l2) such that l1 causes transition p1q
    // and such that l2 causes transition p2q


    // States are (start partition, letter):
    // Now that we checked that P(p1l1ql)=P(p2l2ql) for all (p1,l1), (p2,l2), we see that the
    // probability P(pl1ql2) does not depend on p and l1. We may compute the matrix A where:
    // a_{pq} = P(xl1pl2) for any (x,l1) such that l1 causes transition xp and any l2 that causes
    // transition pq. Then a_{pq} does not depend on x,l1 and is the same for all l2 that cause the
    // same partition transition. Suppose l2 causes transition pq. Define P(p,q) as the
    // probability to go from p to q via any l2. Then P(p,q) = a_{pq}
    //
    //
    // Define  for any l2 that
    // causes transition pq. This probability only depends on the partitions p and q, even if we
    // were given the sequence xl1pl2q.  not on partition x or l1 or l2


    // Step 5. Derive the denser probability matrix notation for states (start partition, letter)
    // For any partition transition qr, the probability that letter l2 causes transition qr is
    // equal to P(pl1ql2) for any letter l that causes transition pq
    // For any transition pq, find any (x,l1) such that l1 causes transition xp and find any l2 that
    // causes transition pq
    // Then let a_{pq} = P( (x,l1) , (p,l2) ), which we obtained earlier
    val ppm: PartitionProbabilityMatrix = Array.tabulate[(Double, LetterChoice)](nPartitions,nPartitions) { case (p,q) =>
      val letterSet        = E_or_3_LetterMatrix(p)(q)
      val letters          = letterSet.letters
      val probability      = if (letters.isEmpty) 0 else {
        //def letterThatCanProceed(pindex: Int) = E_or_3_LetterMatrix.collectFirst{
        //  case row if row(pindex).size > 0 => row(pindex).letters.head
        //}.get
        def partitionThatCanProceed(pindex: Int) = E_or_3_LetterMatrix.collectFirst{
          case row if row(pindex).size > 0 => pindex
        }.get // for every partition there exists a partition that can proceed it, so we can
              // get the resulting partition without checking whether it exists.

        //def letterThatCanFollow(pindex: Int) = E_or_3_LetterMatrix(pindex).collectFirst{
        //  case elt if elt.size > 0 => elt.letters.head
        //}.get // we are sure that there is a letter, so we can get it.
        //val l1       = letterThatCanFollow(q)      // some letter that can follow q

        val x        = partitionThatCanProceed(p)
        val l1       = E_or_3_LetterMatrix(x)(p).letters.head
        val l2       = letters.head                // some letter that causes transition pq
        val plIndex1 = mapPIndexAndLetterToPLIndex((x,l1))
        val plIndex2 = mapPIndexAndLetterToPLIndex((p,l2))
        partitionLetterProbabilityMatrix(plIndex1)(plIndex2)
      }
      (probability, letterSet)
    }

    val nLetterOccurences = mapMatrix(E_or_3_LetterMatrix, toSize).map(_.sum).sum
    //println(s"Number of letter occurences in Partition Matrix = $nLetterOccurences"); println
    //println(s"Markov matrix dimension = $nPLs")                                     ; println

    // This code is nice, but creates a big string so that the VM may run out of memory with m=4:
    //
    //def makePString[A](m: PartitionProbabilityMatrix): String = m.map(row=>{row.map(elt=>formatProbabilityAndLetterChoice(elt))}.mkString(",")).mkString("\n")
    //
    //println(s"Dense probability matrix:\n${makePString(ppm)}\n")
    //

    //println(s"Dense probability matrix:")
    //ppm.map{row => {println( row.map(elt=>formatProbabilityAndLetterChoice(elt)).mkString(","))}}
    //println


    println(s"Dense probability matrix for states: (start partition, letter), and letter type: ${if (do3Letter) "3" else "E"}")
    ppm.map{row => {println( row.map(elt=>formatProbability(elt._1)).mkString(","))}}
    println

    val ltype = {if(do3Letter) "3Letter" else "ELetter"}
    GlobalResults.setNumberOfNodesAndEdges(m=m, graph="StartPartitionLetterGraph", letterType=ltype, numNodes=nPLs, numEdges=P3E.map(_.sum).sum)
  } // run method
}


object Model {

  val DEFAULT_M           = 2
  val MAX_M               = 5
  val DEFAULT_TRACE_LEVEL = 2
  val MAX_TRACE_LEVEL     = 5

  val TRACESPECIFIER_EIGENVALUES    = "eigenvalues"
  val TRACESPECIFIER_PARTITIONS     = "partitions"

  val ALLOWED_TRACESPECIFIERS = Set ( TRACESPECIFIER_EIGENVALUES
                                    , TRACESPECIFIER_PARTITIONS
                                    )


  def usage(exitCode: Int = 1) = {
    val msg =
      s""" SpanningTrees by André & Max van Delft
          |
          |Usage:
          |
          |scala spanningtrees.Model [gridHeightRange] [-traceLevel] [-traceSpecifier...]
          |
          |gridHeightRange: from&to gridHeight (AKA m), e.g.: '2' (= '2 2'), '2 3'.
          |Default is '$DEFAULT_M'; max value is '$MAX_M'
          |
          |traceLevel: '1'..'$MAX_TRACE_LEVEL'; determines what will be printed.
          |Default is  '$DEFAULT_TRACE_LEVEL'
          |
          |traceSpecifier: specific aspects to be traced. Possible values:
          |${ALLOWED_TRACESPECIFIERS.toList.sorted.map(s=>s"  '$s'").mkString("\n")}
          |
          |Example usage:
          |
          |  scala spanningtrees.Model 2 3 -1 ${ALLOWED_TRACESPECIFIERS.toList.sorted.take(3).map(s=>s"-$s").mkString(" ")}
          |
        """.stripMargin
    println(msg)
    System.exit(exitCode)
  }
  def errorMessage(msg: String) = println(s"Error: $msg")

  def main(args: Array[String]): Unit = {
    var     startMOption: Option[Int] = None
    var       endMOption: Option[Int] = None
    var traceLevelOption: Option[Int] = None

    val traceSpecifiers = new mutable.HashSet[String]

    try {
      for (arg <- args) {
        if (arg.startsWith("-")) {
          arg.tail match {
            case "" => usage()
            case s if s.length==1 && s.head.isDigit => val i = s.toInt
                                                       if (i > MAX_TRACE_LEVEL) usage()
                                                       traceLevelOption = Some(i)
            case s if ALLOWED_TRACESPECIFIERS.contains(s) => traceSpecifiers += s
            case s => errorMessage(s"Illegal switch argument: $s"); usage()
          }

        }
        else {
          val i = arg.toInt // throws exception if not a proper int
          if (i > MAX_M) usage()

               if (startMOption.isEmpty) startMOption = Some(i)
          else if (  endMOption.isEmpty) {
                 if (i < startMOption.get) usage()
                 else endMOption = Some(i)
               }
          else usage()
        }
      }
      val startM     =     startMOption.getOrElse(DEFAULT_M)
      val   endM     =       endMOption.getOrElse(startM)
      val traceLevel = traceLevelOption.getOrElse(DEFAULT_TRACE_LEVEL)

      for (m <- startM to endM) new Model(m, traceLevel, traceSpecifiers.toSet).run
      // GlobalResults.printNumberOfNodesAndEdges
    }
    catch {
      case e: NumberFormatException => usage()
      case e: Exception => e.printStackTrace
                           usage(2)
    }
  }
}



object GlobalResults{
  def index(s: String) ={
    s match {
      case "PartitionGraph" => 0
      case "StartPartitionLetterGraph" => 1
      case "LetterEndPartitionGraph" => 2
      case "ELetter" => 0
      case "3Letter" => 1
    }
  }
  var numberOfNodesAndEdges : Array[Array[(Int,Int)]] = Array.tabulate(9,6)( (x,y) => (0,0) ) // should become a class with a monad or so
  def setNumberOfNodesAndEdges(m: Int, graph: String, letterType : String, numNodes: Int, numEdges: Int) = {
    numberOfNodesAndEdges(m)(index(graph)*2 + index(letterType)) = (numNodes, numEdges)
  }
  def printNumberOfNodesAndEdges = {
    println("Number of nodes and edges (|V|,|E|) of:\nPartitionGraph, StartPartitionLetterGraph and LetterEndPartitionGraph for E-letters and 3-Letters")
    for (i      <- 0 until 9; //_=println();
         j      <- 0 until 6; t=numberOfNodesAndEdges(i)(j); numNodes=t._1; numEdges=t._2;
         if numberOfNodesAndEdges(i)(j) != (0,0)
    ) {
      print(s"($numNodes,$numEdges) ")
      if (j==5) println
    }
    println("\n")
  }
}
