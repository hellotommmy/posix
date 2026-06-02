import scala.annotation.tailrec

object PosixCubicSmoke {
  sealed trait Rexp
  case object ZERO extends Rexp
  case object ONE extends Rexp
  final case class CH(c: Char) extends Rexp
  final case class ALT(r1: Rexp, r2: Rexp) extends Rexp
  final case class SEQ(r1: Rexp, r2: Rexp) extends Rexp
  final case class STAR(r: Rexp) extends Rexp
  final case class NTIMES(r: Rexp, n: Int) extends Rexp

  sealed trait Bit
  case object Z extends Bit
  case object S extends Bit

  sealed trait Val
  case object Void extends Val
  final case class CharVal(c: Char) extends Val
  final case class LeftVal(v: Val) extends Val
  final case class RightVal(v: Val) extends Val
  final case class SeqVal(v1: Val, v2: Val) extends Val
  final case class StarsVal(vs: List[Val]) extends Val

  sealed trait ARexp
  case object AZERO extends ARexp
  final case class AONE(bs: List[Bit]) extends ARexp
  final case class ACHAR(bs: List[Bit], c: Char) extends ARexp
  final case class ASEQ(bs: List[Bit], r1: ARexp, r2: ARexp) extends ARexp
  final case class AALTs(bs: List[Bit], rs: List[ARexp]) extends ARexp
  final case class ASTAR(bs: List[Bit], r: ARexp) extends ARexp
  final case class ANTIMES(bs: List[Bit], r: ARexp, n: Int) extends ARexp

  val alphabet: List[Char] = List('a', 'b')

  def asize(r: ARexp): Int = r match {
    case AZERO => 1
    case AONE(_) => 1
    case ACHAR(_, _) => 1
    case ASEQ(_, r1, r2) => 1 + asize(r1) + asize(r2)
    case AALTs(_, rs) => 1 + rs.map(asize).sum
    case ASTAR(_, r) => 1 + asize(r)
    case ANTIMES(_, r, n) => 1 + asize(r) + n
  }

  def shapeCounts(r: ARexp): Map[String, Int] = {
    def add(xs: Map[String, Int], key: String): Map[String, Int] =
      xs.updated(key, xs.getOrElse(key, 0) + 1)
    def merge(a: Map[String, Int], b: Map[String, Int]): Map[String, Int] =
      b.foldLeft(a) { case (acc, (k, v)) => acc.updated(k, acc.getOrElse(k, 0) + v) }
    r match {
      case AZERO => Map("AZERO" -> 1)
      case AONE(bs) => Map("AONE" -> 1, s"AONE_bits_${bs.length}" -> 1)
      case ACHAR(_, _) => Map("ACHAR" -> 1)
      case ASEQ(_, r1, AONE(bs)) if bs.nonEmpty =>
        add(merge(shapeCounts(r1), shapeCounts(AONE(bs))), "ASEQ_right_AONE_nonempty")
      case ASEQ(_, r1, r2) =>
        add(merge(shapeCounts(r1), shapeCounts(r2)), "ASEQ")
      case AALTs(_, rs) =>
        rs.foldLeft(Map("AALTs" -> 1))((acc, x) => merge(acc, shapeCounts(x)))
      case ASTAR(_, r) => add(shapeCounts(r), "ASTAR")
      case ANTIMES(_, r, _) => add(shapeCounts(r), "ANTIMES")
    }
  }

  def shortCounts(r: ARexp): String =
    shapeCounts(r).toList.sortBy { case (k, _) => k }.map { case (k, v) => s"$k=$v" }.mkString(", ")

  def fuse(bs: List[Bit], r: ARexp): ARexp = r match {
    case AZERO => AZERO
    case AONE(cs) => AONE(bs ++ cs)
    case ACHAR(cs, c) => ACHAR(bs ++ cs, c)
    case AALTs(cs, rs) => AALTs(bs ++ cs, rs)
    case ASEQ(cs, r1, r2) => ASEQ(bs ++ cs, r1, r2)
    case ASTAR(cs, r) => ASTAR(bs ++ cs, r)
    case ANTIMES(cs, r, n) => ANTIMES(bs ++ cs, r, n)
  }

  def intern(r: Rexp): ARexp = r match {
    case ZERO => AZERO
    case ONE => AONE(Nil)
    case CH(c) => ACHAR(Nil, c)
    case ALT(r1, r2) => AALTs(Nil, List(fuse(List(Z), intern(r1)), fuse(List(S), intern(r2))))
    case SEQ(r1, r2) => ASEQ(Nil, intern(r1), intern(r2))
    case STAR(r) => ASTAR(Nil, intern(r))
    case NTIMES(r, n) => ANTIMES(Nil, intern(r), n)
  }

  def bnullable(r: ARexp): Boolean = r match {
    case AZERO => false
    case AONE(_) => true
    case ACHAR(_, _) => false
    case ASEQ(_, r1, r2) => bnullable(r1) && bnullable(r2)
    case AALTs(_, rs) => rs.exists(bnullable)
    case ASTAR(_, _) => true
    case ANTIMES(_, r, n) => if (n == 0) true else bnullable(r)
  }

  def bmkeps(r: ARexp): List[Bit] = r match {
    case AONE(bs) => bs
    case ASEQ(bs, r1, r2) => bs ++ bmkeps(r1) ++ bmkeps(r2)
    case AALTs(bs, r :: rs) =>
      if (bnullable(r)) bs ++ bmkeps(r) else bmkeps(AALTs(bs, rs))
    case ASTAR(bs, _) => bs ++ List(S)
    case ANTIMES(bs, r, n) =>
      if (n == 0) bs ++ List(S)
      else bs ++ List(Z) ++ bmkeps(r) ++ bmkeps(ANTIMES(Nil, r, n - 1))
    case other => sys.error(s"bmkeps on non-nullable or malformed expression: $other")
  }

  def bder(c: Char, r: ARexp): ARexp = r match {
    case AZERO => AZERO
    case AONE(_) => AZERO
    case ACHAR(bs, d) => if (c == d) AONE(bs) else AZERO
    case AALTs(bs, rs) => AALTs(bs, rs.map(bder(c, _)))
    case ASEQ(bs, r1, r2) =>
      if (bnullable(r1)) {
        AALTs(bs, List(ASEQ(Nil, bder(c, r1), r2), fuse(bmkeps(r1), bder(c, r2))))
      } else {
        ASEQ(bs, bder(c, r1), r2)
      }
    case ASTAR(bs, body) => ASEQ(bs ++ List(Z), bder(c, body), ASTAR(Nil, body))
    case ANTIMES(bs, body, n) =>
      if (n == 0) AZERO else ASEQ(bs ++ List(Z), bder(c, body), ANTIMES(Nil, body, n - 1))
  }

  def eq1(x: ARexp, y: ARexp): Boolean = (x, y) match {
    case (AZERO, AZERO) => true
    case (AONE(_), AONE(_)) => true
    case (ACHAR(_, c), ACHAR(_, d)) => c == d
    case (ASEQ(_, a1, a2), ASEQ(_, b1, b2)) => eq1(a1, b1) && eq1(a2, b2)
    case (AALTs(_, xs), AALTs(_, ys)) => xs.length == ys.length && xs.zip(ys).forall { case (a, b) => eq1(a, b) }
    case (ASTAR(_, a), ASTAR(_, b)) => eq1(a, b)
    case (ANTIMES(_, a, n), ANTIMES(_, b, m)) => n == m && eq1(a, b)
    case _ => false
  }

  def distinctWith(xs: List[ARexp]): List[ARexp] = {
    @tailrec
    def loop(todo: List[ARexp], acc: List[ARexp], out: List[ARexp]): List[ARexp] = todo match {
      case Nil => out.reverse
      case x :: rest =>
        if (acc.exists(eq1(x, _))) loop(rest, acc, out)
        else loop(rest, x :: acc, x :: out)
    }
    loop(xs, Nil, Nil)
  }

  def flts(rs: List[ARexp]): List[ARexp] = rs match {
    case Nil => Nil
    case AZERO :: tail => flts(tail)
    case AALTs(bs, xs) :: tail => xs.map(fuse(bs, _)) ++ flts(tail)
    case r :: tail => r :: flts(tail)
  }

  def bsimpAALTs(bs: List[Bit], rs: List[ARexp]): ARexp = rs match {
    case Nil => AZERO
    case r :: Nil => fuse(bs, r)
    case _ => AALTs(bs, rs)
  }

  def bsimp7ASEQAtom(bs: List[Bit], r1: ARexp, r2: ARexp): ARexp = (r1, r2) match {
    case (AZERO, _) => AZERO
    case (AONE(bs2), _) => fuse(bs ++ bs2, r2)
    case (ASEQ(bs2, a, b), _) => bsimp7ASEQAtom(bs2, a, bsimp7ASEQAtom(bs, b, r2))
    case (ACHAR(_, _), AZERO) => AZERO
    case (ACHAR(_, _), AONE(_)) => r1
    case (AALTs(_, _), AZERO) => AZERO
    case (AALTs(_, _), AONE(_)) => r1
    case (ASTAR(_, a), ASTAR(_, b)) if eq1(a, b) => r1
    case (ASTAR(_, a), ASEQ(_, ASTAR(_, b), k)) if eq1(a, b) => ASEQ(bs, r1, k)
    case (ASTAR(_, _), AZERO) => AZERO
    case (ASTAR(_, _), AONE(_)) => r1
    case (ANTIMES(_, _, _), AZERO) => AZERO
    case (ANTIMES(_, _, _), AONE(_)) => r1
    case _ => ASEQ(bs, r1, r2)
  }

  def bsimpCubicASEQAtom(bs: List[Bit], r1: ARexp, r2: ARexp): ARexp = (r1, r2) match {
    case (AZERO, _) => AZERO
    case (AONE(bs2), _) => fuse(bs ++ bs2, r2)
    case (ASEQ(bs2, a, b), _) => bsimpCubicASEQAtom(bs2, a, bsimpCubicASEQAtom(bs, b, r2))
    case (_, AZERO) => AZERO
    case (_, AONE(Nil)) => fuse(bs, r1)
    case _ => ASEQ(bs, r1, r2)
  }

  def eq1Member(r: ARexp, rs: List[ARexp]): Boolean = rs.exists(eq1(r, _))

  def pruneEq1Against(covered: List[ARexp], rs: List[ARexp]): List[ARexp] =
    rs.filterNot(r => eq1Member(r, covered))

  def seqCoverRows(r: ARexp): Option[(List[ARexp], ARexp)] = r match {
    case ASEQ(_, AALTs(_, rows), k) => Some((rows, k))
    case ASEQ(_, row, k) => Some((List(row), k))
    case _ => None
  }

  def bsimpStrongPrunePair(earlier: ARexp, later: ARexp): ARexp = (earlier, later) match {
    case (ASEQ(_, AALTs(_, lrs), k1), ASEQ(bs2, AALTs(rbs, rrs), k2)) if eq1(k1, k2) =>
      bsimp7ASEQAtom(bs2, bsimpAALTs(rbs, pruneEq1Against(lrs, rrs)), k2)
    case _ => later
  }

  def bsimpStrongPruneAgainstRows(seen: List[ARexp], r: ARexp): ARexp =
    seen.foldLeft(r)((acc, earlier) => bsimpStrongPrunePair(earlier, acc))

  def bsimpStrongPruneRows(rs: List[ARexp]): List[ARexp] = {
    def loop(seen: List[ARexp], todo: List[ARexp]): List[ARexp] = todo match {
      case Nil => Nil
      case r :: rest =>
        val pruned = bsimpStrongPruneAgainstRows(seen, r)
        pruned :: loop(pruned :: seen, rest)
    }
    loop(Nil, rs)
  }

  def bsimpStrongAALTs(bs: List[Bit], rs: List[ARexp]): ARexp =
    bsimpAALTs(bs, distinctWith(flts(bsimpStrongPruneRows(rs))))

  def bsimpCubicPrunePair(earlier: ARexp, later: ARexp): ARexp =
    (seqCoverRows(earlier), later) match {
      case (Some((covered, k1)), ASEQ(bs2, AALTs(rbs, rrs), k2)) if eq1(k1, k2) =>
        bsimpCubicASEQAtom(bs2, bsimpAALTs(rbs, pruneEq1Against(covered, rrs)), k2)
      case (Some((covered, k1)), ASEQ(_, row, k2)) if eq1(k1, k2) && eq1Member(row, covered) =>
        AZERO
      case _ => later
    }

  def bsimpCubicPruneAgainstRows(seen: List[ARexp], r: ARexp): ARexp =
    seen.foldLeft(r)((acc, earlier) => bsimpCubicPrunePair(earlier, acc))

  def bsimpCubicPruneRows(rs: List[ARexp]): List[ARexp] = {
    def loop(seen: List[ARexp], todo: List[ARexp]): List[ARexp] = todo match {
      case Nil => Nil
      case r :: rest =>
        val pruned = bsimpCubicPruneAgainstRows(seen, r)
        pruned :: loop(pruned :: seen, rest)
    }
    loop(Nil, rs)
  }

  def bsimpCubicAALTs(bs: List[Bit], rs: List[ARexp]): ARexp =
    bsimpAALTs(bs, distinctWith(flts(bsimpCubicPruneRows(rs))))

  def bsimpStrong(r: ARexp): ARexp = r match {
    case ASEQ(bs, r1, r2) => bsimp7ASEQAtom(bs, bsimpStrong(r1), bsimpStrong(r2))
    case AALTs(bs, rs) => bsimpStrongAALTs(bs, flts(rs.map(bsimpStrong)))
    case ASTAR(bs, r) => bsimpStrong(r) match {
      case AZERO => AONE(Nil)
      case AONE(_) => AONE(Nil)
      case ASTAR(bs2, s) => ASTAR(bs2, s)
      case s => ASTAR(bs, s)
    }
    case other => other
  }

  def bsimpCubic(r: ARexp): ARexp = r match {
    case ASEQ(bs, r1, r2) => bsimpCubicASEQAtom(bs, bsimpCubic(r1), bsimpCubic(r2))
    case AALTs(bs, rs) => bsimpCubicAALTs(bs, flts(rs.map(bsimpCubic)))
    case ASTAR(bs, r) => bsimpCubic(r) match {
      case AZERO => AONE(bs ++ List(S))
      case AONE(_) => AONE(bs ++ List(S))
      case s => ASTAR(bs, s)
    }
    case ANTIMES(bs, r, n) =>
      if (n == 0) AONE(bs ++ List(S))
      else bsimpCubic(r) match {
        case AZERO => AZERO
        case AONE(bs2) => AONE(bmkeps(ANTIMES(bs, AONE(bs2), n)))
        case s => ANTIMES(bs, s, n)
      }
    case other => other
  }

  def bders(r: ARexp, s: String): ARexp =
    s.foldLeft(r)((acc, c) => bder(c, acc))

  def bdersSimpCubic(r: ARexp, s: String): ARexp =
    s.foldLeft(r)((acc, c) => bsimpCubic(bder(c, acc)))

  def decodeBits(r: Rexp, bits: List[Bit]): Option[Val] = {
    def dec(re: Rexp, bs: List[Bit]): Option[(Val, List[Bit])] = re match {
      case ZERO => None
      case ONE => Some((Void, bs))
      case CH(c) => Some((CharVal(c), bs))
      case ALT(r1, r2) => bs match {
        case Z :: rest => dec(r1, rest).map { case (v, out) => (LeftVal(v), out) }
        case S :: rest => dec(r2, rest).map { case (v, out) => (RightVal(v), out) }
        case Nil => None
      }
      case SEQ(r1, r2) =>
        for {
          left <- dec(r1, bs)
          (v1, rest1) = left
          right <- dec(r2, rest1)
          (v2, rest2) = right
        } yield (SeqVal(v1, v2), rest2)
      case STAR(body) => bs match {
        case S :: rest => Some((StarsVal(Nil), rest))
        case Z :: rest =>
          for {
            head <- dec(body, rest)
            (v, rest1) = head
            tail <- dec(STAR(body), rest1)
            out <- tail match {
              case (StarsVal(vs), rest2) => Some((StarsVal(v :: vs), rest2))
              case _ => None
            }
          } yield out
        case Nil => None
      }
      case NTIMES(body, _) => dec(STAR(body), bs)
    }
    dec(r, bits).collect { case (v, Nil) => v }
  }

  def blexerValue(r: Rexp, input: String, derivative: (ARexp, String) => ARexp): Option[Val] = {
    val finalRegex = derivative(intern(r), input)
    if (bnullable(finalRegex)) decodeBits(r, bmkeps(finalRegex)) else None
  }

  def baselineValue(r: Rexp, input: String): Option[Val] =
    blexerValue(r, input, bders)

  def cubicValue(r: Rexp, input: String): Option[Val] =
    blexerValue(r, input, bdersSimpCubic)

  def charPower(c: Char, n: Int): Rexp =
    if (n == 0) ONE else SEQ(CH(c), charPower(c, n - 1))

  def altList(rs: List[Rexp]): Rexp = rs match {
    case Nil => ZERO
    case r :: Nil => r
    case r :: tail => ALT(r, altList(tail))
  }

  def thesisCh7Evil(k: Int): Rexp =
    STAR(STAR(altList((1 to k).toList.map(n => STAR(charPower('a', n))))))

  def stringsUpTo(maxLen: Int): List[String] = {
    def exact(n: Int): List[String] =
      if (n == 0) List("")
      else for { c <- alphabet; s <- exact(n - 1) } yield c + s
    (0 to maxLen).toList.flatMap(exact)
  }

  def regexesUpToDepth(maxDepth: Int): List[Rexp] = {
    val memo = scala.collection.mutable.Map.empty[Int, List[Rexp]]
    def go(d: Int): List[Rexp] = memo.getOrElseUpdate(d, {
      val base = List(ZERO, ONE) ++ alphabet.map(CH(_))
      if (d == 0) base
      else {
        val smaller = go(d - 1)
        val unary = smaller.flatMap(r => List(STAR(r), NTIMES(r, 0), NTIMES(r, 1), NTIMES(r, 2)))
        val binary = for {
          r1 <- smaller
          r2 <- smaller
          r <- List(ALT(r1, r2), SEQ(r1, r2))
        } yield r
        (base ++ unary ++ binary).distinct
      }
    })
    go(maxDepth)
  }

  final case class FailureCase(regex: Rexp, input: String, baseline: Option[Val], cubic: Option[Val])

  def checkValuePreservation(maxDepth: Int, maxInput: Int): Unit = {
    val regexes = regexesUpToDepth(maxDepth)
    val inputs = stringsUpTo(maxInput)
    var checked = 0
    regexes.foreach { r =>
      inputs.foreach { s =>
        val b = baselineValue(r, s)
        val c = cubicValue(r, s)
        checked += 1
        if (b != c) {
          val msg =
            s"""POSIX value mismatch
               |regex   = $r
               |input   = $s
               |base    = $b
               |cubic   = $c
               |""".stripMargin
          throw new AssertionError(msg)
        }
      }
    }
    println(s"checked POSIX value preservation on $checked regex/input pairs (depth <= $maxDepth, input length <= $maxInput)")
  }

  def checkEvilFamilyTrace(): Unit = {
    val r = thesisCh7Evil(5)
    val lengths = List(4, 8, 12, 16, 20)
    val trace = lengths.map { n =>
      val out = bdersSimpCubic(intern(r), "a" * n)
      n -> asize(out)
    }
    println("Chapter 7 k=5 bsimpCubic trace: " + trace.map { case (n, size) => s"$n->$size" }.mkString(", "))
    trace.foreach { case (n, size) =>
      if (size >= 1000) {
        val out = bdersSimpCubic(intern(r), "a" * n)
        println(s"Chapter 7 failed-shape n=$n: ${shortCounts(out)}")
        throw new AssertionError(s"Chapter 7 smoke threshold failed at n=$n: asize=$size")
      }
    }
  }

  def checkCounterexamples(): Unit = {
    val a = ACHAR(Nil, 'a')
    val b = ACHAR(Nil, 'b')
    val c = ACHAR(Nil, 'c')
    val d = ACHAR(Nil, 'd')
    val e = ACHAR(Nil, 'e')
    val overlap = AALTs(Nil, List(
      ASEQ(Nil, AALTs(Nil, List(a, b, d)), c),
      ASEQ(Nil, AALTs(Nil, List(a, c, e)), c)
    ))
    val overlapSize = asize(overlap)
    val prunedSize = asize(bsimpCubic(overlap))
    if (bsimpStrong(overlap) != bsimpCubic(overlap)) {
      throw new AssertionError("bsimpCubic unexpectedly diverged from bsimpStrong on shared-suffix overlap")
    }
    if (prunedSize >= overlapSize) {
      throw new AssertionError(s"shared-suffix overlap was not reduced: before=$overlapSize after=$prunedSize")
    }

    val g = ANTIMES(Nil, AALTs(Nil, List(AZERO, AONE(Nil))), 3)
    if (bsimpStrong(g) == bsimpCubic(g)) {
      throw new AssertionError("ANTIMES epsilon-body case did not distinguish bsimpCubic from bsimpStrong")
    }
    val expected = AONE(List(Z, Z, Z, S))
    if (bsimpCubic(g) != expected) {
      throw new AssertionError(s"ANTIMES epsilon-body case did not collapse to value-preserving AONE: ${bsimpCubic(g)}")
    }
    println("counterexample smoke checks passed")
  }

  def intSetting(prop: String, env: String, default: Int): Int =
    sys.props.get(prop)
      .orElse(sys.env.get(env))
      .flatMap(s => scala.util.Try(s.toInt).toOption)
      .getOrElse(default)

  def runSmoke(): Unit = {
    val maxDepth = intSetting("posix.smoke.depth", "POSIX_SMOKE_DEPTH", 2)
    val maxInput = intSetting("posix.smoke.input", "POSIX_SMOKE_INPUT", 3)
    checkValuePreservation(maxDepth, maxInput)
    checkCounterexamples()
    checkEvilFamilyTrace()
  }

  def main(args: Array[String]): Unit =
    runSmoke()
}
