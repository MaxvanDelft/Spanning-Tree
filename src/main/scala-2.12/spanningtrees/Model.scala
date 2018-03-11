package spanningtrees

import java.io.PrintWriter

import scala.reflect.ClassTag
import breeze.linalg._, eigSym.EigSym


/**
  *
  */
class Model(m: Int) {

  type IntSeqPartition                = List[List[Int]]
  type IntPartition                   = Set[Set[Int]]
  type Partition                      = IntPartition
  type Matrix[A]                      = Array[Array[A]] // should become a class with a monad or so
  type PartitionAdjacencyMatrix       = Matrix[LetterChoice] // instead of 0's and 1's this contains letter choices
  type PartitionProbabilityMatrix     = Matrix[(Double, LetterChoice)] // for each letterchoice there is a probability per letter in the choice
  type PartitionLetterAdjacencyMatrix = Matrix[Int]

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

  val ncps       = computeNonCrossingPartitions

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

    def makeString[A](m: Matrix[A]): String = m.map(row=>{row.map(elt=>elt.toString)}.mkString(",")).mkString("\n")
    def toSize(letterChoice: LetterChoice): Int = letterChoice.size
    def to01(  letterChoice: LetterChoice): Int = if (letterChoice.size==0) 0 else 1

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
    // the following code is experimental; attempts to use Breeze failed up to now

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

    // Now compute probabilities for random trees:
    //   what is the chance to get a specific letter at a specific partition
    // All letters that induce the same partition transition must have the same chance. Why? Just logical?
    //
    // 1. To compute the probability matrix we consider adjacency matrices for partition-letter combinations,
    //    so this yields a Markov chain. Then between 2 nodes there is at most 1 edge, no multi-edges.
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
    // nPLs counts these combinations, identified so far

    var mapPIndexAndLetterToPLIndex    = scala.collection.mutable.Map[(Int, Letter), Int]()
    var mapPIndexForAnyLetterToPLIndex = scala.collection.mutable.Map[Int, Int]()
    var mapPLIndexToPIndex             = scala.collection.mutable.Map[Int, Int]()
    var mapPLIndexToLetter             = scala.collection.mutable.Map[Int, Letter]()

    val do3Letter = true // we only do 1 type of letter here. A for-loop would allow for both E-letters and 3-letters

    println(s"Letter type (3/E): ${if (do3Letter) "3" else "E"}")
    println

    val E_or_3_LetterMatrix = if (do3Letter) GW else WG

    var nPLs = 0
    for (i <- 0 until nPartitions) {
      val row = E_or_3_LetterMatrix(i)
      for (j <- 0 until nPartitions) {
        val letterSet: Set[Letter] = row(j).letters
        val pIndex = j
        for (letter <- letterSet) {
          if (!mapPIndexAndLetterToPLIndex.isDefinedAt((pIndex,letter))) {
            val plIndex = nPLs
            mapPIndexAndLetterToPLIndex((pIndex,letter)) = plIndex
            mapPIndexForAnyLetterToPLIndex(pIndex)       = plIndex
            mapPLIndexToPIndex(plIndex) = pIndex
            mapPLIndexToLetter(plIndex) = letter
            nPLs += 1
          }
        }
      }
    }

    println("Mapping from partition index and letter")
    for (i <- 0 until nPLs) {
      println(f"$i%2d ${mapPLIndexToPIndex(i)}%2d ${mapPLIndexToLetter(i)}")
    }
    println

    // Step 1.2 Using these mappings fill the matrix
    val P3E: PartitionLetterAdjacencyMatrix = Array.tabulate(nPLs, nPLs)( {(row, col) =>
//      val pIndex = mapPLIndexToPIndex(col)
//      val letter = mapPLIndexToLetter(col)
//      if (mapPIndexAndLetterToPLIndex((pIndex, letter)) == row) 1 else 0
      val pIndex1 = mapPLIndexToPIndex(row)
      val pIndex2 = mapPLIndexToPIndex(col)
      val letter  = mapPLIndexToLetter(col)
      if (E_or_3_LetterMatrix(pIndex1)(pIndex2).letters.contains(letter)) 1 else 0
    })
    println
    println(s"Partition Letter Matrix:\n${makeString(P3E)}\n")

    // 2. Compute the maximum eigenvalue Lambda
    //    and corresponding left eigenvector EigU and right eigenvector EigV.
    //    Breeze computes the right eigenvectors only directly;
    //    But you get left eigenvectors when you do the operation on the transposed matrix

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

/*
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
    println(s"maxLambdaIndex_Right: ${maxLambdaIndex_Right}")
    println(s"maxLambdaIndex_Left : ${maxLambdaIndex_Left }")

    println(s"eigVector_maxLambda_Right: ${eigVector_maxLambda_Right}")
    println(s"eigVector_maxLambda_Left : ${eigVector_maxLambda_Left}")
    println(s"eigVector_maxLambda_Right: ${eigVector_maxLambda_Right}")
    println(s"eigVector_maxLambda_Left : ${eigVector_maxLambda_Left}")

    // Step 3. Compute the stationary distribution

    val eigVector_maxLambda_LeftTimesRight = eigVector_maxLambda_Left *:* eigVector_maxLambda_Right
    val sum_values = sum(eigVector_maxLambda_LeftTimesRight)
    val eigVector_maxLambda_LeftTimesRight_sum_1 = eigVector_maxLambda_LeftTimesRight / sum_values

    println(s"eigVector_maxLambda_LeftTimesRight: ${eigVector_maxLambda_LeftTimesRight}")
    println(s"eigVector_maxLambda_LeftTimesRight_sum_1: ${eigVector_maxLambda_LeftTimesRight_sum_1}")

    println

    // Step 4. Compute the probability matrix of the partition-letter combinations

    val u = eigVector_maxLambda_Right
    val lambda = maxLambda_Right

//    val densePartitionLetterProbabilityMatrix = DenseMatrix.tabulate(nPLs, nPLs){case (i, j) =>
//      (u(j)*P3E(i)(j))/(lambda*u(i))
//    }
//
//    println(s"PartitionLetterProbabilityMatrix: ${densePartitionLetterProbabilityMatrix}")
//    println


    val partitionLetterProbabilityMatrix = Array.tabulate[Double](nPLs,nPLs) { case (i,j) => (u(j)*P3E(i)(j))/(lambda*u(i)) }

    def formatProbability(d: Double) = f"$d%1.3f".replace("0.",".").replace(".000",".   ")
    def formatProbabilityMatrix(pm: Matrix[Double]) = pm.map{ row => row.map(formatProbability).mkString(" ")}.mkString("\n")
    def formatProbabilityAndLetterChoice(plc: (Double, LetterChoice)): String = s"${formatProbability(plc._1)}=>${plc._2}"

    println(s"Probability matrix:\n${formatProbabilityMatrix(partitionLetterProbabilityMatrix)}")
    println

    // Step 5. Derive the denser probability matrix notation

    val ppm: PartitionProbabilityMatrix = Array.tabulate[(Double, LetterChoice)](nPartitions,nPartitions) { case (i,j) =>
       val letterSet   = E_or_3_LetterMatrix(i)(j)
      val letters     = letterSet.letters
      val probability = if (letters.isEmpty) 0 else {
        val aLetter   = letters.head
        val plIndex1  = mapPIndexForAnyLetterToPLIndex(i)
        val plIndex2  = mapPIndexAndLetterToPLIndex((j,aLetter))
        partitionLetterProbabilityMatrix(plIndex1)(plIndex2)
      }
      (probability, letterSet)
    }


    def makePString[A](m: PartitionProbabilityMatrix): String = m.map(row=>{row.map(elt=>formatProbabilityAndLetterChoice(elt))}.mkString(",")).mkString("\n")

    println(s"Dense probability matrix:\n${makePString(ppm)}\n")
    println

  } // run method
}


object Model {

  val startM = 1
  val   endM = 2

  def main(args: Array[String]) = {
    for (m <- startM to endM) new Model(m).run
  }
}