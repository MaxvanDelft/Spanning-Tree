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
  type PartitionProbabilityMatrix     = Matrix[(Double, LetterChoice)] // for each letterchoice there is a (equal) probability per letter in the choice
  type PartitionLetterAdjacencyMatrix = Matrix[Int]

  def makeString[A](m: Matrix[A]): String = m.map(row=>{row.map(elt=>elt.toString)}.mkString(",")).mkString("\n")
  def toSize(letterChoice: LetterChoice): Int = letterChoice.size
  def to01(  letterChoice: LetterChoice): Int = if (letterChoice.size==0) 0 else 1

  import Model._
  def trace_eigenvalues      = traceLevel >= 2 || traceSpecifiers.contains(TRACESPECIFIER_EIGENVALUES)
  def trace_partitions       = traceLevel >= 1 || traceSpecifiers.contains(TRACESPECIFIER_PARTITIONS)
  def trace_maxEigenvalueEigVectors = traceLevel >= 2 || traceSpecifiers.contains(TRACESPECIFIER_MAXEIGENVALUEEIGVECTORS)
  def trace_stationaryDistribution  = traceLevel >= 2 || traceSpecifiers.contains(TRACESPECIFIER_STATIONARYDISTRIBUTION)


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


    // The following function:
    // 1. Finds meaningful states (end partition, letter)
    // 2. Derives the adjacency matrix A of the corresponding graph
    // 3. Computes the Parry matrix of A. (Takes very long, the graphs are very large)
    if (m <= 3) {
      analyse_E_or_3_LetterMatrix(do3Letter=false, E_or_3_LetterMatrix=WG)
      analyse_E_or_3_LetterMatrix(do3Letter= true, E_or_3_LetterMatrix=GW)
      analyse_E_or_3_LetterMatrixStartPartition(do3Letter=false, E_or_3_LetterMatrix=WG)
      analyse_E_or_3_LetterMatrixStartPartition(do3Letter= true, E_or_3_LetterMatrix=GW)
    }

    // We approximate the probability matrix C, with c_{ij} the probobility to go from i to j in
    // a uniform path on a multigraph (here partition graph)
    // Also we approximate matrix B, with b_{ij} the probobility to go from i to j through any edge in a uniform path on a multigraph (here partition graph)
    // The probibilities b_{ij} may be assigned to the edges of the partition graph.

    def formatProbability1(d: Double) = f"$d%1.3f".replace("0.",".").replace(".000",".   ")
    def formatProbability2(d: Double) = f"$d%1.6f".replace("0.", ".").replace(".000000", ".      ")//.replace(".00000", ".    0").replace(".0000", ".   0").replace(".000", ".  0")

    /*println(s"Uniform paths edge probability matrix Eletters")
    println
    var A = WGS.map(row=>row.map(elt=>elt.toDouble))
    var C = parryMatrixApproximated(A)
    var B = Array.tabulate(nPartitions,nPartitions) { (i, j) =>
      if ( A(i)(j)==0 ) 0
      else C(i)(j) / A(i)(j)
    }
    B.map{row => {println( row.map(elt=> if ( m<=3 ) formatProbability1(elt) else formatProbability2(elt)).mkString(","))}}

    println
    println(s"Uniform paths edge probability matrix 3letters")
    A = GWS.map(row=>row.map(elt=>elt.toDouble))
    C = parryMatrixApproximated(A)
    B = Array.tabulate(nPartitions,nPartitions) { (i, j) =>
      if ( A(i)(j)==0 ) 0
      else C(i)(j) / A(i)(j)
    }
    B.map{row => {println( row.map(elt=> if ( m<=3 ) formatProbability1(elt) else formatProbability2(elt)).mkString(","))}}
    println*/


    // B: Matrix[Int] = Array.tabulate(20, 20)( {(row, col) => scala.util.Random.nextInt(10) })
    // B.map{row => {println( row.map(elt=>elt.toString).mkString(","))}}
    //parryMatrix(B)

    // val BB: Matrix[Double] = Array.tabulate(20, 20)( {(row, col) => 20*scala.util.Random.nextDouble })
    // BB.map{row => {println( row.map(elt=>elt.toString).mkString(","))}}
    // parryMatrixDoubles(BB)


    testFormulaForLambda
  }



  def multiplyM(a: Matrix[Double], b: Matrix[Double]): Matrix[Double] =
    Array.tabulate(a.size, a.size)( {(row, col) =>
    var sum: Double = 0
    var i = 0
    while (i < a.size) { sum += a(row)(i) * b(i)(col); i += 1; }
    sum
  })

  def sumM(a: Matrix[Double]): Double = {
    val n = a.length
    var sum: Double = 0
    for ( i <- 0 until n)
      //for (j <- 0 until n)
        sum = sum + a(i)(0)
    sum
  }
  def matrixPower(A: Matrix[Double], k: Int): Matrix[Double] = {
    if ( k<=1 ) A
    else if ( k%2 == 0 ){ val B = matrixPower(A,k/2); multiplyM(B,B)}
    else multiplyM(matrixPower(A,k/2),matrixPower(A,math.ceil(k.toDouble/2).toInt))
    //if ( k<=1 ) A else multiplyM(A,matrixPower(A,k-1))
  }

  //def matrixPower(A: Matrix[Double], k: Int): Matrix[Double] = {
    //if ( k<=1 ) A else multiplyM(matrixPower(A,k/2),matrixPower(A,math.ceil(k.toDouble/2).toInt))
    //if ( k<=1 ) A else multiplyM(A,matrixPower(A,k-1))
  //}

  def vectorProduct(x: Array[Double], y: Array[Double], n: Int): Double = {
    //Array.tabulate(n){case i => x(i)*y(i)}.sum
    var sum: Double = 0 ; for (i <- 0 until n){ sum = sum + x(i)*y(i) }; sum
  }
  def matrixVectorProduct(A: Matrix[Double], v: Array[Double], n: Int): Array[Double] = {
    Array.tabulate(n){case i => vectorProduct(A(i),v,n)}
  }
  def matrixVectorPower(A: Matrix[Double], v: Array[Double], k: Int, n: Int): Array[Double] = {
    if ( k<=1 ) v else matrixVectorPower(A,matrixVectorProduct(A,v,n),k-1,n)
  }

  def matrixVectorProductNormalized(A: Matrix[Double], v: Array[Double], n: Int): Array[Double] = {
    val x = Array.tabulate(n){case i => vectorProduct(A(i),v,n)}
    val sumValues = x.sum
    x.map(elt=>elt/sumValues)
  }

  def matrixVectorPowerrr(A: Matrix[Double], v: Array[Double], k: Int, n: Int): Array[Double] = {
    if ( k<=1 ) v else { matrixVectorPowerrr(A,matrixVectorProductNormalized(A,v,n),k-1,n)} /*
      val x: Array[Double] = Array.tabulate(n) (i=>matrixVectorPowerrr(A,matrixVectorProduct(A,v,n),k-1,n)(i));
      val sumValues: Double = x.sum; println(sumValues);
      x
    //;x.map(elt=>elt/sumValues)
    }*/
  }

  def time[R](block: => R): R = {
    val t0 = System.nanoTime()
    val result = block    // call-by-name
    val t1 = System.nanoTime()
    println("Elapsed time: " + (t1 - t0) + "ns")
    result
  }






  def parryMatrixDoubles(A:Array[Array[Double]]) = {
    val n = A.size
    val DPE = DenseMatrix.tabulate(n,n){case (i, j) => (A(i)(j))}
    val DPE_Transposed = DPE.t

    // Step 1. Compute eigenvalues of A
    val eigStuff_Right = time{eig(DPE)}
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

    // Step 2: Determine the maximal eigenvalue and the corresponding left and right eigenvalue
    val maxLambda_Right      =    max(eigStuff_Right.eigenvalues)
    val maxLambda_Left       =    max(eigStuff_Left .eigenvalues)
    val maxLambdaIndex_Right = argmax(eigStuff_Right.eigenvalues)
    val maxLambdaIndex_Left  = argmax(eigStuff_Left .eigenvalues)

    def formatDouble(d: Double) = f"$d%1.6f"

    if (trace_eigenvalues || trace_maxEigenvalueEigVectors){println("Parry matrix\n")}
    if (trace_eigenvalues) {
      println("Eigenvalues")
      println(s"lambdas right: ${eigStuff_Right.eigenvalues.toScalaVector.filter(Math.abs(_) > NONZERO_TOLERANCE).map(elt=>formatDouble(elt)).mkString(", ")}")
      println(s"lambdas left: ${eigStuff_Left.eigenvalues.toScalaVector.filter(Math.abs(_) > NONZERO_TOLERANCE).map(elt=>formatDouble(elt)).mkString(", ")}")
      println

      println(s"eigVectors right:\n${eigStuff_Right.eigenvectors}")
      println
      println(s"eigVectors left:\n${eigStuff_Left.eigenvectors}")
      println
    }


    var eigVector_maxLambda_Right = eigStuff_Right.eigenvectors(::, maxLambdaIndex_Right); eigVector_maxLambda_Right = eigVector_maxLambda_Right/sum(eigVector_maxLambda_Right)
    var eigVector_maxLambda_Left  = eigStuff_Left .eigenvectors(::, maxLambdaIndex_Left ); eigVector_maxLambda_Left  = eigVector_maxLambda_Left /sum(eigVector_maxLambda_Left )

    if (eigVector_maxLambda_Right(0) < 0) eigVector_maxLambda_Right = -eigVector_maxLambda_Right
    if (eigVector_maxLambda_Left (0) < 0) eigVector_maxLambda_Left = -eigVector_maxLambda_Left

    val BB: Matrix[Double] = time{matrixPower(A,10)}
    val C: Matrix[Double] = multiplyM(A,BB)
    //B.map{row => {println( row.map(elt=>elt.toString).mkString(","))}}
    //println(B.map(_.sum).sum)
    val OtherBB: Array[Double] = time{matrixVectorPower(A,A.map(row=>row(0)),10,n)}
    val OtherC: Array[Double] = matrixVectorProduct(A,OtherBB,n)
    def C_sumDiagElts(): Double = {var sum: Double = 0; for (i <- 0 until n) { sum = sum+C(i)(i)}; sum}
    val AndAnOtherBB: Array[Double] = time{matrixVectorPowerrr(A,A.map(row=>row(0)),10,n)}

    println("Approximated values")
    //BB.map{row => {println( row.map(elt=>elt.toString).mkString(","))}}
    println(s"${sumM(C)} and ${sumM(BB)} and ${sumM(C) / sumM(BB)}")
    println(s"${C.map(_.sum).sum} and ${BB.map(_.sum).sum} and ${C.map(_.sum).sum / BB.map(_.sum).sum}")
    println(s"${OtherC.sum} and ${OtherBB.sum} and ${OtherC.sum / OtherBB.sum} and ${AndAnOtherBB.sum}") // uses matrix-vector product
    val lambda_approx = C.map(_.sum).sum / BB.map(_.sum).sum
    val u_approx = Array.tabulate(BB.length) { i=> BB.map(x=>x(i)).sum }.map(x=> x*lambda_approx/C.map(_.sum).sum)
    println(s"sum u = ${u_approx.sum}")
    val v_approx = Array.tabulate(BB.length) { i=> BB(i).sum }.map(x=> x*lambda_approx/C.map(_.sum).sum)
    println(s"Maximal eigenvalue approx: $lambda_approx")
    println(s"Left and right eigenvectors of maximal lambda approx:")
    println(s"u: ${u_approx.take(20).map(elt=>formatDouble(elt)).mkString(" ")} ${if (u_approx.length > 20) s"... ${u_approx.length} total" else ""}")
    println(s"v: ${v_approx.take(20).map(elt=>formatDouble(elt)).mkString(" ")} ${if (v_approx.length > 20) s"... ${v_approx.length} total" else ""}")
    println
    // check whether uA = lambda u and Av = lambda v
    val uA = Array.tabulate(n) { j => var sum:Double = 0; for ( i <- 0 to n-1 ) sum = sum+A(i)(j)*u_approx(i); sum }
    val lambda_u = u_approx.map( j => j*lambda_approx)
    println(s"uA - lambda u = ${uA.zip(lambda_u).map(x => x._1-x._2).mkString(" ")}")

    val Av = Array.tabulate(n) { i => A(i).zip(v_approx).map(x => x._1*x._2).sum }
    val lambda_v = v_approx.map( i => i*lambda_approx)
    println(s"Av - lambda v = ${Av.zip(lambda_v).map(x => x._1-x._2).mkString(" ")}")
    println
    if (trace_maxEigenvalueEigVectors) {
      //println(s"Maximal eigenvalue:\nlambda: ${formatDouble(maxLambda_Right)}")
      println(s"Maximal eigenvalue:\nlambda: ${maxLambda_Right}")
      println
      println(s"Left and right eigenvectors of lambda:")
      println(s"u: ${eigVector_maxLambda_Left .toScalaVector.take(20).map(elt=>formatDouble(elt)).mkString(" ")} ${if (eigVector_maxLambda_Left .length > 20) s"... ${eigVector_maxLambda_Left .length} total" else ""}")
      println(s"v: ${eigVector_maxLambda_Right.toScalaVector.take(20).map(elt=>formatDouble(elt)).mkString(" ")} ${if (eigVector_maxLambda_Right.length > 20) s"... ${eigVector_maxLambda_Right.length} total" else ""}")
      println
    }


    // Optionally compute the stationary distribution
    if (trace_stationaryDistribution) {
      val eigVector_maxLambda_LeftTimesRight_Elementwise = eigVector_maxLambda_Left *:* eigVector_maxLambda_Right
      val sum_values = sum(eigVector_maxLambda_LeftTimesRight_Elementwise)
      val eigVector_maxLambda_LeftTimesRight_sum_1 = eigVector_maxLambda_LeftTimesRight_Elementwise / sum_values

      println("Stationary Distribution of the Parry Markov Chain")
      println(s"u *:* v: ${eigVector_maxLambda_LeftTimesRight_Elementwise.toScalaVector.take(20).map(elt => formatDouble(elt)).mkString(" ")} ${if (eigVector_maxLambda_LeftTimesRight_Elementwise.length > 20) s"... ${eigVector_maxLambda_LeftTimesRight_Elementwise.length} total" else ""}")
      // println(s"pi: ${eigVector_maxLambda_LeftTimesRight_sum_1.toScalaVector.take(20).map(elt=>formatDouble(elt)).mkString(" ")} ${if (eigVector_maxLambda_LeftTimesRight_Elementwise.length > 20) s"... ${eigVector_maxLambda_LeftTimesRight_Elementwise.length}"} total") does not work

      val uv = eigVector_maxLambda_LeftTimesRight_Elementwise.toScalaVector
      val pi = uv.map{elt=>elt/uv.sum}
      println(s"pi: ${pi.take(20).map(elt => formatDouble(elt)).mkString(" ")} ${if (eigVector_maxLambda_LeftTimesRight_Elementwise.length > 20) s"... ${eigVector_maxLambda_LeftTimesRight_Elementwise.length} total" else ""}")
      println
    }

    // Step 3. Compute the Parry probability matrix

    val v = eigVector_maxLambda_Right
    val lambda = maxLambda_Right

    Array.tabulate[Double](n,n) { case (i,j) => (v(j)*A(i)(j))/(lambda*v(i)) }
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
    println(s"Letter End Partition Matrix:\n${makeString(P3E)}\n")


    val partitionLetterProbabilityMatrix = parryMatrixDoubles(P3E.map(row=>row.map(elt=>elt.toDouble)))
    //val partitionLetterProbabilityMatrix = parryMatrixDoubles(P3E.map(row=>row.map(elt=>elt.toDouble)))

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
    for ( p<-0 until nPartitions ){
      for ( q<-0 until nPartitions ){
        val letters = E_or_3_LetterMatrix(p)(q).letters
        for ( l <- letters ) {
          for ( row1<-0 until nPartitions ){
            for ( row2<-0 until nPartitions ){
              val letters1 = E_or_3_LetterMatrix(row1)(p).letters
              val letters2 = E_or_3_LetterMatrix(row2)(p).letters
              if (row1 != row2 && !letters1.isEmpty && !letters2.isEmpty){
                for ( l1 <- letters1 ) {
                  for ( l2 <- letters2 ) {
                    val plIndex1_1 = mapPIndexAndLetterToPLIndex((p,l1))
                    val plIndex1_2 = mapPIndexAndLetterToPLIndex((q,l))
                    val plIndex2_1 = mapPIndexAndLetterToPLIndex((p,l2))
                    val plIndex2_2 = mapPIndexAndLetterToPLIndex((q,l))
                    val difference = partitionLetterProbabilityMatrix(plIndex1_1)(plIndex1_2) - partitionLetterProbabilityMatrix(plIndex2_1)(plIndex2_2)
                    if ( math.abs(difference) >= 1/math.pow(10,10) )
                      println(s"Difference: ${difference}")
                  }
                }
              }
            }
          }
        }
      }
    }



    // Now that we checked P(l1pl2q)=P(l3pl4q) for all l1,l3 that can proceed p and all l2,l4
    // that cause transition pq we may compute the matrix A where: a_{pq} = P(l1pl2q) for any l1
    // that can proceed p and any l2 that causes transition pq. Suppose l2 causes transition pq.
    // Define P(p,q) as the probability to go from p to q via any l2. Then P(p,q) = a_{pq}


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

    // This code is nice, but creates a big string so that the VM may run out of memory with m=4:
    //
    //def makePString[A](m: PartitionProbabilityMatrix): String = m.map(row=>{row.map(elt=>formatProbabilityAndLetterChoice(elt))}.mkString(",")).mkString("\n")
    //
    //println(s"Dense probability matrix:\n${makePString(ppm)}\n")
    //

    println(s"Dense probability-letter matrix:")
    ppm.map{row => {println( row.map(elt=>formatProbabilityAndLetterChoice(elt)).mkString(","))}}
    println


    println(s"Dense probability matrix for states: (letter, end partition), and letter type: ${if (do3Letter) "3" else "E"}")
    ppm.map{row => {println( row.map(elt=>formatProbability(elt._1)).mkString(","))}}
    println

    val ltype = {if(do3Letter) "3Letter" else "ELetter"}
    GlobalResults.setNumberOfNodesAndEdges(m=m, graph="LetterEndPartitionGraph", letterType=ltype, numNodes=nPLs, numEdges=P3E.map(_.sum).sum.toInt)
  } // run method






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
    // In any sequence p1 l1 p2 l2 of two end partitions and two letters the existence of the partition
    // transition from (p1,l1) to (p2,l2) depends ONLY on p1,l1 and p2; NOT on l2
    val P3E: PartitionLetterAdjacencyMatrix = Array.tabulate(nPLs, nPLs)( {(row, col) =>
      val pIndex1 = mapPLIndexToPIndex(row) // index of p1 in (l1,p1)
      val letter  = mapPLIndexToLetter(row) // letter l1 in (p1,l1), a letter that potentially causes partition transition from p1 to p2
      val pIndex2 = mapPLIndexToPIndex(col) // index of start partition p2, though it now serves as an end partition in some state (p2,l2)
      if (E_or_3_LetterMatrix(pIndex1)(pIndex2).letters.contains(letter)) 1 else 0
    })
    val ltype = {if(do3Letter) "3Letter" else "ELetter"}
    GlobalResults.setNumberOfNodesAndEdges(m=m, graph="StartPartitionLetterGraph", letterType=ltype, numNodes=nPLs, numEdges=P3E.map(_.sum).sum.toInt)

    println
    println(s"Start Partition Letter Matrix:\n${makeString(P3E)}\n")

    val partitionLetterProbabilityMatrix = parryMatrixDoubles(P3E.map(row=>row.map(elt=>elt.toDouble)))

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
    for ( pl<-0 until nPLs ){
      for ( row1<-0 until nPLs ){
        for ( row2<-0 until nPLs ){
          if (row1 != row2 && P3E(row1)(pl) == 1 && P3E(row2)(pl) == 1){
            val difference = partitionLetterProbabilityMatrix(row1)(pl) - partitionLetterProbabilityMatrix(row2)(pl)
            if ( math.abs(difference) >= 1/math.pow(10,10) )
              println(s"Difference: ${difference}")

          }
        }
      }
    }


    // States are (start partition, letter):
    // Now that we checked that P(p1l1ql)=P(p2l2ql) for all (p1,l1), (p2,l2), we see that the
    // probability P(pl1ql2) does not depend on p and l1. We may compute the matrix A where:
    // a_{pq} = P(xl1pl2) for any (x,l1) such that l1 causes transition xp and any l2 that causes
    // transition pq. Then a_{pq} does not depend on x,l1 and is the same for all l2 that cause the
    // same partition transition. Suppose l2 causes transition pq. Define P(p,q) as the
    // probability to go from p to q via any l2. Then P(p,q) = a_{pq}


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

    // This code is nice, but creates a big string so that the VM may run out of memory with m=4:
    //
    //def makePString[A](m: PartitionProbabilityMatrix): String = m.map(row=>{row.map(elt=>formatProbabilityAndLetterChoice(elt))}.mkString(",")).mkString("\n")
    //
    //println(s"Dense probability matrix:\n${makePString(ppm)}\n")
    //

    //println(s"Dense probability-letter matrix:")
    //ppm.map{row => {println( row.map(elt=>formatProbabilityAndLetterChoice(elt)).mkString(","))}}
    //println


    println(s"Dense probability matrix for states: (start partition, letter), and letter type: ${if (do3Letter) "3" else "E"}")
    ppm.map{row => {println( row.map(elt=>formatProbability(elt._1)).mkString(","))}}
    println
  } // run method

  def formatDouble(d: Double) = f"$d%1.6f"
  // Given an irreducible aperiodic graph with weight matrix A
  // The function below computes the probability matrix P such that probiblity of a path x_1...x_k from
  // fixed x_1 to fixed x_k is proportional to prod_i a_{x_ix_{i+1}}
  def parryMatrixApproximated(A:Array[Array[Double]], trace: Set[String]) = {
    val n = A.length
    val B: Matrix[Double] = matrixPower(A,64)
    val C: Matrix[Double] = multiplyM(A,B)
    val D: Matrix[Double] = multiplyM(A,C)
    val E: Matrix[Double] = multiplyM(A,D)
    val lambda_approx = if ( B.map(_.sum).sum == 0) 0 else C.map(_.sum).sum / B.map(_.sum).sum
    val lambda_approx2 = if ( C.map(_.sum).sum == 0) 0 else D.map(_.sum).sum / C.map(_.sum).sum
    val lambda_approx3 = if ( D.map(_.sum).sum == 0) 0 else E.map(_.sum).sum / D.map(_.sum).sum
    val u_approx = Array.tabulate(n) { i=> B.map(row=>row(i)).sum }.map(x=> x/B.map(_.sum).sum)
    val v_approx = Array.tabulate(n) { i=> B(i).sum }.map(x=> x*lambda_approx/C.map(_.sum).sum)
    val v_approx2 = Array.tabulate(n) { i=> C(i).sum }.map(x=> x*lambda_approx/D.map(_.sum).sum)
    val v_approx3 = Array.tabulate(n) { i=> D(i).sum }.map(x=> x*lambda_approx/E.map(_.sum).sum)
    //if (!trace.isEmpty)
    //println("Approximated values")
    if (trace.contains("eigenvalue")){
      println(s"Max eigenvalue approx: $lambda_approx , but also $lambda_approx2 and $lambda_approx3")

      val DPE = DenseMatrix.tabulate(n,n){case (i, j) => (A(i)(j))}
      val DPE_Transposed = DPE.t

      // Step 1. Compute eigenvalues of A
      val eigStuff_Right = eig(DPE)
      val eigStuff_Left  = eig(DPE_Transposed)

      // check that imaginary parts of the eigenvalues are close to 0
      /*val NONZERO_TOLERANCE = 1e-10 // observed was: 9e-15
      for (ev <- eigStuff_Right.eigenvaluesComplex) {
        if (Math.abs(ev) > NONZERO_TOLERANCE) {
          println(s"WARNING: Eigenvalue with nonzero imaginary part: $ev")
        }
      }
      for (ev <- eigStuff_Left.eigenvaluesComplex) {
        if (Math.abs(ev) > NONZERO_TOLERANCE) {
          println(s"WARNING: Eigenvalue with nonzero imaginary part: $ev")
        }
      }*/
      val maxLambda_Right = max(eigStuff_Right.eigenvalues)
      println(s"Max eigenvalue Breeze: $maxLambda_Right \n")
    }
    if(trace.contains("eigenvectors")) {
      println(s"Left and right eigenvectors of maximal lambda approx:")
      //println(s"u: ${u_approx.take(20).map(elt => formatDouble(elt)).mkString(" ")} ${if (n > 20) s"... $n total" else ""}")
      println(s"v: ${v_approx.take(20).map(elt => formatDouble(elt)).mkString(" ")} ${if (n > 20) s"... $n total" else ""}")
      println(s"v: ${v_approx2.take(20).map(elt => formatDouble(elt)).mkString(" ")} ${if (n > 20) s"... $n total" else ""}")
      println(s"v: ${v_approx3.take(20).map(elt => formatDouble(elt)).mkString(" ")} ${if (n > 20) s"... $n total" else ""}")
      if (u_approx.sum == v_approx.sum && u_approx.sum == 1)
        println(s"Both eigenvectors sum up to 1.")
      else
        println(s"|u| = ${u_approx.sum} and |v| = ${v_approx.sum}")
      println
    }

    // check whether uA = lambda u and Av = lambda v
    if (trace.contains("Av-lambda*v")) {
      val uA = Array.tabulate(n) { j => var sum: Double = 0; for (i <- 0 to n - 1) sum = sum + A(i)(j) * u_approx(i); sum }
      val lambda_u = u_approx.map(j => j * lambda_approx)
      println(s"uA - lambda u = ${uA.zip(lambda_u).map(x => x._1 - x._2).mkString(" ")}")

      val Av = Array.tabulate(n) { i => A(i).zip(v_approx).map(x => x._1 * x._2).sum }
      val lambda_v = v_approx.map(i => i * lambda_approx)
      println(s"Av - lambda v = ${Av.zip(lambda_v).map(x => x._1 - x._2).mkString(" ")}")
      println
    }

    // check whether pi such that pi_i = u_i*v_i, sum pi_i = 1 satisfies pi P = pi and perhaps also P pi = pi
    val P = Array.tabulate[Double](n, n) { case (i, j) => (v_approx(j) * A(i)(j)) / (v_approx(i) * lambda_approx) }
    if (trace.contains("stationary_distribution")) {
      println("Stationary distribution")
      val pi1 = Array.tabulate(n) { case i => u_approx(i) * v_approx(i) };
      println(s"${pi1.sum} and ${1 / lambda_approx} and ${matrixPower(A, 20).map(_.sum).sum / math.pow(matrixPower(A, 10).map(_.sum).sum, 2)}")
      val pi = pi1.map(i => i / pi1.sum)
      println(s"pi    :${pi.take(20).map(elt => formatDouble(elt)).mkString(" ")} ${if (n > 20) s"... $n total" else ""}")

      val pi_P = Array.tabulate(n) { case j => Array.tabulate(n) { case i => pi(i) * P(i)(j) }.sum }
      println(s"pi * P:${pi_P.take(20).map(elt => formatDouble(elt)).mkString(" ")} ${if (n > 20) s"... $n total" else ""}")

      val P_pi = Array.tabulate(n) { case i => Array.tabulate(n) { case j => pi(j) * P(i)(j) }.sum }
      println(s"P * pi:${P_pi.take(20).map(elt => formatDouble(elt)).mkString(" ")} ${if (n > 20) s"... $n total" else ""}")
    }
    //val u_accent = Array.tabulate(n) { j => u_approx(j)/pi1.sum}
    //val A_pow_10_minus_vulambda_pow_10: Matrix[Double] = Array.tabulate(20, 20)( {(row, col) => val x = B(row)(col); val y = v_approx(row)*u_accent(col)*scala.math.pow(lambda_approx,8); if(row == 0 && col == 0) println(s"$x and $y and ${x-y}"); x-y })
    //println(s"\n${B(0)(0)} and ${lambda_approx} and ${scala.math.pow(lambda_approx,8)} and ${scala.math.pow(lambda_approx,8)*pi(0)} and ${pi(0)} and ${v_approx(0)*u_accent(0)}")
    //println(A_pow_10_minus_vulambda_pow_10(0)(0))
    //println(s"\nMatrix A^10 - vu*lambda^10:\n${makeString(A_pow_10_minus_vulambda_pow_10)}")

    val A_pow_10_divided_by_elts_in_u_approx: Matrix[Double] = B.map( row => Array.tabulate(n){ i  => row(i)/u_approx(i)} )
    //println(s"\n${B(0)(0)} and ${lambda_approx} and ${scala.math.pow(lambda_approx,8)} and ${scala.math.pow(lambda_approx,8)*pi(0)} and ${pi(0)} and ${v_approx(0)*u_accent(0)}")
    //println(A_pow_10_minus_vulambda_pow_10(0)(0))
    if (trace.contains("(A/lambda)^k -> vu"))
      println(s"\nMatrix A^10/u:\n${makeString(A_pow_10_divided_by_elts_in_u_approx)}")
    P
  }

  def testFormulaForLambda() = {
    val n = 5
    //val B: Matrix[Int] = Array.tabulate(n, n)( {(row, col) => scala.util.Random.nextInt(10) })
    val A: Matrix[Double] = Array.tabulate(n, n)( {(row, col) => 20*scala.util.Random.nextDouble })
    val B: Matrix[Double] = Array.tabulate(n, n)( {(row, col) => 10*scala.util.Random.nextDouble+300 })
    //println(s"\nCompute the parry matrix of A:\n${makeString(A)}")
    //val C: Matrix[Double] = multiplyM_Elementwise(A,B)
    val C: Matrix[Double] = multiplyM(A,B)

    //val trace: Set[String] = Set("eigenvalue", "eigenvectors", "stationary_distribution", "Av-lambda*v", "stationary_distribution", "(A/lambda)^k -> vu")
    val trace: Set[String] = Set("eigenvalue", "eigenvectors")

    val P1 = parryMatrixApproximated(A,trace)
    /*var M = A
    for (k <- 1 until n-1 ){
      val v = scala.util.Random.nextInt(n-k)
      M = Array.tabulate(n-k,n-k) { (i,j) => var i_new = i; var j_new = j; if(i>=v) i_new = i+1; if(j>=v) j_new = j+1; M(i_new)(j_new) }
      parryMatrixApproximated(M,trace)
      if ( k > n*n-10 ){ println(s"\nM:\n${makeString(A)}") }
    }*/

    var M = A
    /*for ( k<-0 until n*n ){
      var i,j : Int = 0
      do {
        i = scala.util.Random.nextInt(n)
        j = scala.util.Random.nextInt(n)
      } while ( M(i)(j) == 0 )
      M(i)(j) = 0
      //if (M.map(_.sum).sum == 0){
        println(s"\nM:\n${makeString(M)}")
      //}
      //println(s"M(${i})(${j}) = ${M(i)(j)}")
      parryMatrixApproximated(M,trace)
      //if ( k > n*n-10 ){ println(s"\nM:\n${makeString(A)}") }
    }*/
    M = Array.tabulate(2,2)((i,j)=> (i,j) match {case (0,1)=>10
                                                 case (1,0)=>1
                                                 case _    =>0})
    println(s"\nCompute the parry matrix of A:\n${makeString(M)}")
    parryMatrixApproximated(M,trace)
  }
}


object Model {

  val DEFAULT_M           = 2
  val MAX_M               = 5
  val DEFAULT_TRACE_LEVEL = 2
  val MAX_TRACE_LEVEL     = 5

  val TRACESPECIFIER_PARTITIONS     = "partitions"
  val TRACESPECIFIER_EIGENVALUES    = "eigenvalues"
  val TRACESPECIFIER_MAXEIGENVALUEEIGVECTORS = "maxEigenvalueEigVectors"
  val TRACESPECIFIER_STATIONARYDISTRIBUTION  = "stationaryDistribution"

  val ALLOWED_TRACESPECIFIERS = Set ( TRACESPECIFIER_PARTITIONS
                                    , TRACESPECIFIER_EIGENVALUES
                                    , TRACESPECIFIER_MAXEIGENVALUEEIGVECTORS
                                    , TRACESPECIFIER_STATIONARYDISTRIBUTION
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
      for (arg <- args) { // parse command line arguments
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
      } // end parse command line arguments

      val startM     =     startMOption.getOrElse(DEFAULT_M)
      val   endM     =       endMOption.getOrElse(startM)
      val traceLevel = traceLevelOption.getOrElse(DEFAULT_TRACE_LEVEL)

      // run model
      for (m <- startM to endM) new Model(m, traceLevel, traceSpecifiers.toSet).run
      GlobalResults.printNumberOfNodesAndEdges
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
