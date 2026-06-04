import scala.annotation.tailrec
import scala.util.Random

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

  def rsubterms(r: Rexp): Set[Rexp] = {
    val seen = scala.collection.mutable.Set.empty[Rexp]
    def visit(x: Rexp): Unit = {
      if (seen.add(x)) {
        x match {
          case ALT(r1, r2) => visit(r1); visit(r2)
          case SEQ(r1, r2) => visit(r1); visit(r2)
          case STAR(body) => visit(body)
          case NTIMES(body, _) => visit(body)
          case _ => ()
        }
      }
    }
    visit(r)
    seen.toSet
  }

  def rdagSize(r: Rexp): Int =
    rsubterms(r).size

  def rshapeKey(r: Rexp): String = r match {
    case ZERO => "0"
    case ONE => "1"
    case CH(c) => s"c($c)"
    case ALT(r1, r2) => s"+(${rshapeKey(r1)},${rshapeKey(r2)})"
    case SEQ(r1, r2) => s".(${rshapeKey(r1)},${rshapeKey(r2)})"
    case STAR(body) => s"*(${rshapeKey(body)})"
    case NTIMES(body, n) => s"n($n,${rshapeKey(body)})"
  }

  def rshapeDagSize(r: Rexp): Int = {
    val seen = scala.collection.mutable.Set.empty[String]
    def visit(x: Rexp): Unit = {
      val key = rshapeKey(x)
      if (seen.add(key)) {
        x match {
          case ALT(r1, r2) => visit(r1); visit(r2)
          case SEQ(r1, r2) => visit(r1); visit(r2)
          case STAR(body) => visit(body)
          case NTIMES(body, _) => visit(body)
          case _ => ()
        }
      }
    }
    visit(r)
    seen.size
  }

  def adagSize(r: ARexp): Int = {
    val seen = scala.collection.mutable.Set.empty[ARexp]
    def visit(x: ARexp): Unit = {
      if (seen.add(x)) {
        x match {
          case ASEQ(_, r1, r2) => visit(r1); visit(r2)
          case AALTs(_, rs) => rs.foreach(visit)
          case ASTAR(_, body) => visit(body)
          case ANTIMES(_, body, _) => visit(body)
          case _ => ()
        }
      }
    }
    visit(r)
    seen.size
  }

  def ashapeKey(r: ARexp): String = r match {
    case AZERO => "0"
    case AONE(_) => "1"
    case ACHAR(_, c) => s"c($c)"
    case ASEQ(_, r1, r2) => s".(${ashapeKey(r1)},${ashapeKey(r2)})"
    case AALTs(_, rs) => s"+(${rs.map(ashapeKey).mkString(",")})"
    case ASTAR(_, body) => s"*(${ashapeKey(body)})"
    case ANTIMES(_, body, n) => s"n($n,${ashapeKey(body)})"
  }

  def ashapeDagSize(r: ARexp): Int = {
    val seen = scala.collection.mutable.Set.empty[String]
    def visit(x: ARexp): Unit = {
      val key = ashapeKey(x)
      if (seen.add(key)) {
        x match {
          case ASEQ(_, r1, r2) => visit(r1); visit(r2)
          case AALTs(_, rs) => rs.foreach(visit)
          case ASTAR(_, body) => visit(body)
          case ANTIMES(_, body, _) => visit(body)
          case _ => ()
        }
      }
    }
    visit(r)
    seen.size
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

  def eraseA(r: ARexp): Rexp = r match {
    case AZERO => ZERO
    case AONE(_) => ONE
    case ACHAR(_, c) => CH(c)
    case ASEQ(_, r1, r2) => SEQ(eraseA(r1), eraseA(r2))
    case AALTs(_, rs) => altList(rs.map(eraseA))
    case ASTAR(_, r) => STAR(eraseA(r))
    case ANTIMES(_, r, n) => NTIMES(eraseA(r), n)
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

  def bsimp4ASEQAtom(bs: List[Bit], r1: ARexp, r2: ARexp): ARexp = (r1, r2) match {
    case (AZERO, _) => AZERO
    case (AONE(bs2), _) => fuse(bs ++ bs2, r2)
    case (ASEQ(bs2, a, b), _) => bsimp4ASEQAtom(bs2, a, bsimp4ASEQAtom(bs, b, r2))
    case (ACHAR(_, _), AZERO) => AZERO
    case (ACHAR(_, _), AONE(_)) => r1
    case (AALTs(_, _), AZERO) => AZERO
    case (AALTs(_, _), AONE(_)) => r1
    case (ASTAR(_, _), AZERO) => AZERO
    case (ASTAR(_, _), AONE(_)) => r1
    case (ANTIMES(_, _, _), AZERO) => AZERO
    case (ANTIMES(_, _, _), AONE(_)) => r1
    case _ => ASEQ(bs, r1, r2)
  }

  def bsimp7ASEQAtom(bs: List[Bit], r1: ARexp, r2: ARexp): ARexp = (r1, r2) match {
    case (ASTAR(_, a), ASTAR(_, b)) if eq1(a, b) => r1
    case (ASTAR(_, a), ASEQ(_, ASTAR(_, b), k)) if eq1(a, b) => ASEQ(bs, r1, k)
    case _ => bsimp4ASEQAtom(bs, r1, r2)
  }

  def bsimp4ASEQAtomPosixCore(bs: List[Bit], r1: ARexp, r2: ARexp): ARexp = (r1, r2) match {
    case (AZERO, _) => AZERO
    case (_, AZERO) => AZERO
    case (AONE(bs2), _) if !bnullable(r2) => fuse(bs ++ bs2, r2)
    case (ASEQ(bs2, a, b), _) if !bnullable(a) =>
      bsimp4ASEQAtomPosixCore(bs2, a, bsimp4ASEQAtomPosixCore(bs, b, r2))
    case (_, AONE(_)) if !bnullable(r1) => fuse(bs, r1)
    case _ => ASEQ(bs, r1, r2)
  }

  def bsimp7ASEQAtomPosixCore(bs: List[Bit], r1: ARexp, r2: ARexp): ARexp = (r1, r2) match {
    case (ASTAR(_, a), ASTAR(_, b)) if eq1(a, b) && !bnullable(a) => r1
    case (ASTAR(_, a), ASEQ(_, ASTAR(_, b), k)) if eq1(a, b) && !bnullable(a) => ASEQ(bs, r1, k)
    case _ => bsimp4ASEQAtomPosixCore(bs, r1, r2)
  }

  def bsimp4ASEQAtomSafe(bs: List[Bit], r1: ARexp, r2: ARexp): ARexp = (r1, r2) match {
    case (AZERO, _) => AZERO
    case (AONE(bs2), _) => fuse(bs ++ bs2, r2)
    case (_, AZERO) => AZERO
    case (_, AONE(Nil)) => fuse(bs, r1)
    case _ => ASEQ(bs, r1, r2)
  }

  def bsimp7ASEQAtomSafe(bs: List[Bit], r1: ARexp, r2: ARexp): ARexp = (r1, r2) match {
    case _ => bsimp4ASEQAtomSafe(bs, r1, r2)
  }

  def bsimpCubicASEQAtom(bs: List[Bit], r1: ARexp, r2: ARexp): ARexp = (r1, r2) match {
    case (AZERO, _) => AZERO
    case (AONE(bs2), _) => fuse(bs ++ bs2, r2)
    case (ASEQ(bs2, a, b), _) => bsimpCubicASEQAtom(bs2, a, bsimpCubicASEQAtom(bs, b, r2))
    case (_, AZERO) => AZERO
    case (_, AONE(Nil)) => fuse(bs, r1)
    case _ => ASEQ(bs, r1, r2)
  }

  def bsimpCubicASEQAtomMode(mode: String, bs: List[Bit], r1: ARexp, r2: ARexp): ARexp =
    mode match {
      case "full" => bsimpCubicASEQAtom(bs, r1, r2)
      case "none" => ASEQ(bs, r1, r2)
      case "keyed-no-reassoc" => bsimpCubicASEQAtomMode("no-reassoc", bs, r1, r2)
      case "expanded-keyed-no-reassoc" => bsimpCubicASEQAtomMode("no-reassoc", bs, r1, r2)
      case "unary-cover-no-reassoc" => bsimpCubicASEQAtomMode("no-reassoc", bs, r1, r2)
      case "reassoc-nonnullable-left" => (r1, r2) match {
        case (ASEQ(bs2, a, b), _) if !bnullable(a) =>
          bsimpCubicASEQAtomMode(mode, bs2, a, bsimpCubicASEQAtomMode(mode, bs, b, r2))
        case _ => bsimpCubicASEQAtomMode("no-reassoc", bs, r1, r2)
      }
      case "no-reassoc" => (r1, r2) match {
        case (AZERO, _) => AZERO
        case (AONE(bs2), _) => fuse(bs ++ bs2, r2)
        case (_, AZERO) => AZERO
        case (_, AONE(Nil)) => fuse(bs, r1)
        case _ => ASEQ(bs, r1, r2)
      }
      case "no-left-one" => (r1, r2) match {
        case (AZERO, _) => AZERO
        case (ASEQ(bs2, a, b), _) => bsimpCubicASEQAtomMode(mode, bs2, a, bsimpCubicASEQAtomMode(mode, bs, b, r2))
        case (_, AZERO) => AZERO
        case (_, AONE(Nil)) => fuse(bs, r1)
        case _ => ASEQ(bs, r1, r2)
      }
      case "no-right-one" => (r1, r2) match {
        case (AZERO, _) => AZERO
        case (AONE(bs2), _) => fuse(bs ++ bs2, r2)
        case (ASEQ(bs2, a, b), _) => bsimpCubicASEQAtomMode(mode, bs2, a, bsimpCubicASEQAtomMode(mode, bs, b, r2))
        case (_, AZERO) => AZERO
        case _ => ASEQ(bs, r1, r2)
      }
      case "zeros-only" => (r1, r2) match {
        case (AZERO, _) => AZERO
        case (_, AZERO) => AZERO
        case _ => ASEQ(bs, r1, r2)
      }
      case other => throw new IllegalArgumentException(
        s"unknown POSIX_SMOKE_SEQ_MODE=$other; expected full, none, keyed-no-reassoc, expanded-keyed-no-reassoc, unary-cover-no-reassoc, reassoc-nonnullable-left, no-reassoc, no-left-one, no-right-one, or zeros-only"
      )
    }

  def eq1Member(r: ARexp, rs: List[ARexp]): Boolean = rs.exists(eq1(r, _))

  def pruneEq1Against(covered: List[ARexp], rs: List[ARexp]): List[ARexp] =
    rs.filterNot(r => eq1Member(r, covered))

  def aRunLenA(r: ARexp): Option[Int] = r match {
    case AONE(_) => Some(0)
    case ACHAR(_, 'a') => Some(1)
    case ASEQ(_, r1, r2) =>
      for {
        n1 <- aRunLenA(r1)
        n2 <- aRunLenA(r2)
      } yield n1 + n2
    case _ => None
  }

  def onlyARegex(r: ARexp): Boolean = r match {
    case AZERO => true
    case AONE(_) => true
    case ACHAR(_, c) => c == 'a'
    case ASEQ(_, r1, r2) => onlyARegex(r1) && onlyARegex(r2)
    case AALTs(_, rs) => rs.forall(onlyARegex)
    case ASTAR(_, body) => onlyARegex(body)
    case ANTIMES(_, body, _) => onlyARegex(body)
  }

  def isAStar(r: ARexp): Boolean = r match {
    case ASTAR(_, body) => aRunLenA(body).contains(1)
    case _ => false
  }

  def cheapCoveredByRows(row: ARexp, covered: List[ARexp]): Boolean =
    eq1Member(row, covered) || (onlyARegex(row) && covered.exists(isAStar))

  def pruneCheapAgainst(covered: List[ARexp], rs: List[ARexp]): List[ARexp] =
    rs.filterNot(r => cheapCoveredByRows(r, covered))

  def eq1List(xs: List[ARexp], ys: List[ARexp]): Boolean =
    xs.length == ys.length && xs.zip(ys).forall { case (x, y) => eq1(x, y) }

  def seqFactors(r: ARexp): List[ARexp] = r match {
    case ASEQ(_, r1, r2) => seqFactors(r1) ++ seqFactors(r2)
    case _ => List(r)
  }

  def seqCoverRows(r: ARexp): Option[(List[ARexp], ARexp)] = r match {
    case ASEQ(_, AALTs(_, rows), k) => Some((rows, k))
    case ASEQ(_, row, k) => Some((List(row), k))
    case _ => None
  }

  def seqCoverRowsKey(r: ARexp): Option[(List[ARexp], List[ARexp])] =
    seqFactors(r) match {
      case Nil => None
      case AALTs(_, rows) :: tail => Some((rows, tail))
      case row :: tail => Some((List(row), tail))
    }

  def expandedSeqKeys(r: ARexp, maxKeys: Int): Option[List[List[ARexp]]] = {
    def choices(f: ARexp): List[ARexp] = f match {
      case AALTs(_, rows) => rows
      case _ => List(f)
    }
    def step(acc: List[List[ARexp]], f: ARexp): Option[List[List[ARexp]]] = {
      val cs = choices(f)
      val next = for { key <- acc; c <- cs } yield key :+ c
      if (next.length > maxKeys) None else Some(next)
    }
    seqFactors(r).foldLeft(Option(List(List.empty[ARexp]))) {
      case (Some(acc), f) => step(acc, f)
      case (None, _) => None
    }
  }

  def seqKeyMember(key: List[ARexp], keys: List[List[ARexp]]): Boolean =
    keys.exists(eq1List(key, _))

  def seqKeysCovered(keys: List[List[ARexp]], covered: List[List[ARexp]]): Boolean =
    keys.nonEmpty && keys.forall(seqKeyMember(_, covered))

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

  def bsimpStrongSafePrunePair(earlier: ARexp, later: ARexp): ARexp = (earlier, later) match {
    case (ASEQ(_, AALTs(_, lrs), k1), ASEQ(bs2, AALTs(rbs, rrs), k2)) if eq1(k1, k2) =>
      bsimp7ASEQAtomSafe(bs2, bsimpAALTs(rbs, pruneEq1Against(lrs, rrs)), k2)
    case _ => later
  }

  def bsimpStrongSafePruneAgainstRows(seen: List[ARexp], r: ARexp): ARexp =
    seen.foldLeft(r)((acc, earlier) => bsimpStrongSafePrunePair(earlier, acc))

  def bsimpStrongSafePruneRows(rs: List[ARexp]): List[ARexp] = {
    def loop(seen: List[ARexp], todo: List[ARexp]): List[ARexp] = todo match {
      case Nil => Nil
      case r :: rest =>
        val pruned = bsimpStrongSafePruneAgainstRows(seen, r)
        pruned :: loop(pruned :: seen, rest)
    }
    loop(Nil, rs)
  }

  def bsimpStrongSafeAALTs(bs: List[Bit], rs: List[ARexp]): ARexp =
    bsimpAALTs(bs, distinctWith(flts(bsimpStrongSafePruneRows(rs))))

  def bsimpCubicPrunePair(earlier: ARexp, later: ARexp): ARexp =
    bsimpCubicPrunePairMode(cubicSeqMode, earlier, later)

  def bsimpCubicPrunePairMode(seqMode: String, earlier: ARexp, later: ARexp): ARexp =
    if (seqMode == "expanded-keyed-no-reassoc") {
      val maxKeys = 5000
      expandedSeqKeys(earlier, maxKeys) match {
        case Some(covered) =>
          later match {
            case ASEQ(bs2, AALTs(rbs, rrs), k2) =>
              val kept = rrs.filterNot { row =>
                expandedSeqKeys(ASEQ(Nil, row, k2), maxKeys).exists(seqKeysCovered(_, covered))
              }
              if (kept == rrs) later
              else bsimpCubicASEQAtomMode(seqMode, bs2, bsimpAALTs(rbs, kept), k2)
            case _ =>
              expandedSeqKeys(later, maxKeys) match {
                case Some(laterKeys) if seqKeysCovered(laterKeys, covered) => AZERO
                case _ => later
              }
          }
        case None => later
      }
    } else if (seqMode == "keyed-no-reassoc") {
      (seqCoverRowsKey(earlier), seqCoverRowsKey(later), later) match {
        case (Some((covered, tail1)), Some((_, tail2)), ASEQ(bs2, AALTs(rbs, rrs), k2)) if eq1List(tail1, tail2) =>
          bsimpCubicASEQAtomMode(seqMode, bs2, bsimpAALTs(rbs, pruneEq1Against(covered, rrs)), k2)
        case (Some((covered, tail1)), Some((laterRows, tail2)), _) if eq1List(tail1, tail2) && laterRows.exists(eq1Member(_, covered)) =>
          AZERO
        case _ => later
      }
    } else if (seqMode == "unary-cover-no-reassoc") {
      (seqCoverRows(earlier), later) match {
        case (Some((covered, k1)), ASEQ(bs2, AALTs(rbs, rrs), k2)) if eq1(k1, k2) =>
          bsimpCubicASEQAtomMode(seqMode, bs2, bsimpAALTs(rbs, pruneCheapAgainst(covered, rrs)), k2)
        case (Some((covered, k1)), ASEQ(_, row, k2)) if eq1(k1, k2) && cheapCoveredByRows(row, covered) =>
          AZERO
        case _ => later
      }
    } else {
      (seqCoverRows(earlier), later) match {
        case (Some((covered, k1)), ASEQ(bs2, AALTs(rbs, rrs), k2)) if eq1(k1, k2) =>
          bsimpCubicASEQAtomMode(seqMode, bs2, bsimpAALTs(rbs, pruneEq1Against(covered, rrs)), k2)
        case (Some((covered, k1)), ASEQ(_, row, k2)) if eq1(k1, k2) && eq1Member(row, covered) =>
          AZERO
        case _ => later
      }
    }

  def bsimpCubicPruneAgainstRows(seen: List[ARexp], r: ARexp): ARexp =
    bsimpCubicPruneAgainstRowsMode(cubicSeqMode, seen, r)

  def bsimpCubicPruneAgainstRowsMode(seqMode: String, seen: List[ARexp], r: ARexp): ARexp =
    seen.foldLeft(r)((acc, earlier) => bsimpCubicPrunePairMode(seqMode, earlier, acc))

  def bsimpCubicPruneRows(rs: List[ARexp]): List[ARexp] = {
    bsimpCubicPruneRowsMode(cubicSeqMode, rs)
  }

  def bsimpCubicPruneRowsMode(seqMode: String, rs: List[ARexp]): List[ARexp] = {
    def loop(seen: List[ARexp], todo: List[ARexp]): List[ARexp] = todo match {
      case Nil => Nil
      case r :: rest =>
        val pruned = bsimpCubicPruneAgainstRowsMode(seqMode, seen, r)
        pruned :: loop(pruned :: seen, rest)
    }
    loop(Nil, rs)
  }

  def bsimpCubicAALTs(bs: List[Bit], rs: List[ARexp]): ARexp =
    bsimpCubicAALTsWithMode(cubicSeqMode, bs, rs)

  def bsimpCubicAALTsWithMode(seqMode: String, bs: List[Bit], rs: List[ARexp]): ARexp =
    bsimpAALTs(bs, distinctWith(flts(bsimpCubicPruneRowsMode(seqMode, rs))))

  def bsimpStrong(r: ARexp): ARexp = r match {
    case ASEQ(bs, r1, r2) => bsimp7ASEQAtom(bs, bsimpStrong(r1), bsimpStrong(r2))
    case AALTs(bs, rs) => bsimpStrongAALTs(bs, flts(rs.map(bsimpStrong)))
    case ASTAR(bs, r) => bsimpStrong(r) match {
      case AZERO => AONE(Nil)
      case AONE(_) => AONE(Nil)
      case ASTAR(bs2, s) => ASTAR(bs2, s)
      case s => ASTAR(bs, s)
    }
    case ANTIMES(bs, body, n) => ANTIMES(bs, bsimpStrong(body), n)
    case other => other
  }

  def bsimpStrongSafe(r: ARexp): ARexp = r match {
    case ASEQ(bs, r1, r2) => bsimp7ASEQAtomSafe(bs, bsimpStrongSafe(r1), bsimpStrongSafe(r2))
    case AALTs(bs, rs) => bsimpStrongSafeAALTs(bs, flts(rs.map(bsimpStrongSafe)))
    case ASTAR(bs, r) => bsimpStrongSafe(r) match {
      case AZERO => AONE(bs ++ List(S))
      case AONE(_) => AONE(bs ++ List(S))
      case s => ASTAR(bs, s)
    }
    case other => other
  }

  def bsimpCubicWithMode(seqMode: String, r: ARexp): ARexp = r match {
    case ASEQ(bs, r1, r2) => bsimpCubicASEQAtomMode(seqMode, bs, bsimpCubicWithMode(seqMode, r1), bsimpCubicWithMode(seqMode, r2))
    case AALTs(bs, rs) => bsimpCubicAALTsWithMode(seqMode, bs, flts(rs.map(bsimpCubicWithMode(seqMode, _))))
    case ASTAR(bs, r) => bsimpCubicWithMode(seqMode, r) match {
      case AZERO => AONE(bs ++ List(S))
      case AONE(_) => AONE(bs ++ List(S))
      case s => ASTAR(bs, s)
    }
    case ANTIMES(bs, r, n) =>
      if (n == 0) AONE(bs ++ List(S))
      else bsimpCubicWithMode(seqMode, r) match {
        case AZERO => AZERO
        case AONE(bs2) => AONE(bmkeps(ANTIMES(bs, AONE(bs2), n)))
        case s => ANTIMES(bs, s, n)
      }
    case other => other
  }

  def bsimpCubic(r: ARexp): ARexp =
    bsimpCubicWithMode(cubicSeqMode, r)

  def bders(r: ARexp, s: String): ARexp =
    s.foldLeft(r)((acc, c) => bder(c, acc))

  def bdersSimpCubic(r: ARexp, s: String): ARexp =
    s.foldLeft(r)((acc, c) => bsimpCubic(bder(c, acc)))

  def bdersStrong(r: ARexp, s: String): ARexp =
    s.foldLeft(r)((acc, c) => bsimpStrong(bder(c, acc)))

  def bdersStrongSafe(r: ARexp, s: String): ARexp =
    s.foldLeft(r)((acc, c) => bsimpStrongSafe(bder(c, acc)))

  def bpderList(c: Char, r: ARexp): List[ARexp] = r match {
    case AZERO => Nil
    case AONE(_) => Nil
    case ACHAR(bs, d) => if (c == d) List(AONE(bs)) else Nil
    case AALTs(bs, rs) => rs.flatMap(bpderList(c, _)).map(fuse(bs, _))
    case ASEQ(bs, r1, r2) =>
      val left = bpderList(c, r1).map(p => bsimp4ASEQAtom(bs, p, r2))
      val right =
        if (bnullable(r1)) bpderList(c, r2).map(p => fuse(bs, fuse(bmkeps(r1), p)))
        else Nil
      left ++ right
    case ASTAR(bs, body) =>
      bpderList(c, body).map(p => bsimp4ASEQAtom(bs ++ List(Z), p, ASTAR(Nil, body)))
    case ANTIMES(bs, body, n) =>
      if (n == 0) Nil
      else bpderList(c, body).map(p => bsimp4ASEQAtom(bs ++ List(Z), p, ANTIMES(Nil, body, n - 1)))
  }

  def bpderNormList(c: Char, r: ARexp): List[ARexp] =
    bpderList(c, r).map(p => bsimp4ASEQAtom(Nil, p, AONE(Nil)))

  def bpderStrongList(c: Char, r: ARexp): List[ARexp] =
    bpderNormList(c, r).map(bsimpStrong)

  def bpderStrongRows(c: Char, rs: List[ARexp]): List[ARexp] =
    distinctWith(flts(bsimpStrongPruneRows(flts(rs.flatMap(bpderStrongList(c, _))))))

  def bpdersStrongRows(rs: List[ARexp], input: String): List[ARexp] =
    input.foldLeft(rs)((acc, c) => bpderStrongRows(c, acc))

  def bpdersStrong1Rows(r: ARexp, input: String): List[ARexp] =
    bpdersStrongRows(List(r), input)

  def asubterms(r: ARexp): Set[ARexp] = r match {
    case ASEQ(_, r1, r2) => Set(r) ++ asubterms(r1) ++ asubterms(r2)
    case AALTs(_, rs) => rs.foldLeft(Set(r))((acc, q) => acc ++ asubterms(q))
    case ASTAR(_, body) => Set(r) ++ asubterms(body)
    case ANTIMES(_, body, _) => Set(r) ++ asubterms(body)
    case _ => Set(r)
  }

  def eq1SetMember(r: ARexp, rs: Iterable[ARexp]): Boolean =
    rs.exists(eq1(r, _))

  def strongBridgeMember(r: ARexp, rs: Iterable[ARexp]): Boolean = {
    val rn = bsimpStrong(r)
    rs.exists(q =>
      eq1(r, q) || eq1(rn, q) || eq1(r, bsimpStrong(q)) ||
        activeRowSubsetCoveredBy(r, q) || activeRowSubsetCoveredBy(rn, q)
    )
  }

  def activeRowSubsetCoveredBy(r: ARexp, q: ARexp): Boolean = {
    val topLevel = (r, q) match {
      case (ASEQ(_, AALTs(_, rRows), rKey), ASEQ(_, AALTs(_, qRows), qKey)) =>
        eq1(rKey, qKey) && rRows.forall(row => rowCoveredByRows(row, qRows))
      case _ => false
    }
    topLevel || expandedRowSubsetCoveredBy(r, q)
  }

  def rowCoveredByRows(row: ARexp, rows: List[ARexp]): Boolean =
    expandedRowKeys(row).forall(key =>
      rows.exists(coverer => rowKeyCoveredBy(key, coverer))
    )

  def expandedRowKeysOption(row: ARexp, maxKeys: Int): Option[List[ARexp]] =
    expandedSeqKeys(row, maxKeys).map(keys =>
      distinctWith(keys.map(key => bsimpStrong(mkSeqFromFactors(key))))
    )

  def expandedRowKeys(row: ARexp): List[ARexp] =
    expandedRowKeysOption(row, 4096).getOrElse(List(bsimpStrong(row)))

  def rowKeyCoveredBy(key: ARexp, coverer: ARexp): Boolean = {
    val cn = bsimpStrong(coverer)
    eq1(key, coverer) || eq1(key, cn) ||
      expandedRowKeys(coverer).exists(eq1(key, _))
  }

  def expandedRowSubsetCoveredBy(r: ARexp, q: ARexp): Boolean =
    (expandedRowKeysOption(r, 8192), expandedRowKeysOption(q, 8192)) match {
      case (Some(rKeys), Some(qKeys)) =>
        rKeys.forall(rKey =>
          qKeys.exists(qKey => eq1(rKey, qKey) || eq1(rKey, bsimpStrong(qKey)))
        )
      case _ => false
    }

  def mkSeqFromFactors(fs: List[ARexp]): ARexp = fs match {
    case Nil => AONE(Nil)
    case x :: Nil => x
    case x :: xs => ASEQ(Nil, x, mkSeqFromFactors(xs))
  }

  def factoredActiveRowsOneStep(rows: List[ARexp]): List[ARexp] = {
    val groups = scala.collection.mutable.ListBuffer.empty[(ARexp, scala.collection.mutable.ListBuffer[ARexp])]

    def add(suffix: ARexp, prefix: ARexp): Unit = {
      groups.indexWhere { case (k, _) => eq1(k, suffix) } match {
        case -1 =>
          groups += suffix -> scala.collection.mutable.ListBuffer(prefix)
        case i =>
          val prefixes = groups(i)._2
          if (!prefixes.exists(eq1(prefix, _))) prefixes += prefix
      }
    }

    val workRows = distinctWith(rows.flatMap(r => asubterms(r).toList))
    workRows.foreach { row =>
      asubterms(row).foreach(sub => add(sub, AONE(Nil)))
      val factors = seqFactors(row)
      factors.indices.foreach { i =>
        val prefix = mkSeqFromFactors(factors.take(i))
        val suffix = mkSeqFromFactors(factors.drop(i))
        flts(List(prefix)).foreach(add(suffix, _))
        prefix match {
          case AALTs(_, altRows) =>
            val suffixFactors = seqFactors(suffix)
            altRows.foreach { altRow =>
              val altFactors = seqFactors(altRow)
              (1 until altFactors.length).foreach { j =>
                val branchPrefix = mkSeqFromFactors(altFactors.take(j))
                val branchSuffix = mkSeqFromFactors(altFactors.drop(j) ++ suffixFactors)
                flts(List(branchPrefix)).foreach(add(branchSuffix, _))
              }
            }
          case _ => ()
        }
      }
    }

    groups.iterator.flatMap { case (suffix, prefixes0) =>
      val prefixes = distinctWith(prefixes0.toList)
      if (prefixes.lengthCompare(2) >= 0) {
        Some(ASEQ(Nil, AALTs(Nil, prefixes), suffix))
      } else None
    }.toList
  }

  def factoredActiveRowsFromRows(rows: List[ARexp]): Set[ARexp] = {
    val seen = scala.collection.mutable.ListBuffer.empty[ARexp]
    val out = scala.collection.mutable.ListBuffer.empty[ARexp]

    def addSeen(r: ARexp): Boolean =
      if (seen.exists(eq1(r, _))) false
      else {
        seen += r
        true
      }

    rows.foreach(addSeen)
    var round = 0
    var changed = true
    while (changed && round < 8 && seen.length < 512) {
      changed = false
      factoredActiveRowsOneStep(seen.toList).foreach { r =>
        if (addSeen(r)) {
          out += r
          changed = true
        }
      }
      round += 1
    }
    out.toSet
  }

  def strongRootFromRows(rows: List[ARexp]): ARexp =
    bsimpStrong(AALTs(Nil, rows))

  def strongRowsBridgeRows(rows: List[ARexp]): Set[ARexp] =
    rows.flatMap(asubterms).toSet ++
      asubterms(strongRootFromRows(rows)) ++
      factoredActiveRowsFromRows(rows)

  sealed trait DNode
  case object DZero extends DNode
  final case class DOne(bs: List[Bit]) extends DNode
  final case class DChar(bs: List[Bit], c: Char) extends DNode
  final case class DSeq(bs: List[Bit], r1: Int, r2: Int) extends DNode
  final case class DAlts(bs: List[Bit], rs: List[Int]) extends DNode
  final case class DStar(bs: List[Bit], r: Int) extends DNode
  final case class DNTimes(bs: List[Bit], r: Int, n: Int) extends DNode

  final class DagStore(eraseBits: Boolean = false) {
    private val nodes = scala.collection.mutable.ArrayBuffer.empty[DNode]
    private val index = scala.collection.mutable.HashMap.empty[DNode, Int]
    private val derCache = scala.collection.mutable.HashMap.empty[(String, Char, Int), Int]

    def totalSize: Int = nodes.size

    def node(id: Int): DNode = nodes(id)

    private def bits(bs: List[Bit]): List[Bit] =
      if (eraseBits) Nil else bs

    private def appendBits(xs: List[Bit], ys: List[Bit]): List[Bit] =
      if (eraseBits) Nil else xs ++ ys

    private def normalizeNode(n: DNode): DNode =
      if (!eraseBits) n
      else n match {
        case DZero => DZero
        case DOne(_) => DOne(Nil)
        case DChar(_, c) => DChar(Nil, c)
        case DSeq(_, r1, r2) => DSeq(Nil, r1, r2)
        case DAlts(_, rs) => DAlts(Nil, rs)
        case DStar(_, r) => DStar(Nil, r)
        case DNTimes(_, r, n) => DNTimes(Nil, r, n)
      }

    def mk(n: DNode): Int = {
      val normalized = normalizeNode(n)
      index.getOrElseUpdate(normalized, {
        val id = nodes.length
        nodes += normalized
        id
      })
    }

    def fromARexp(r: ARexp): Int = r match {
      case AZERO => mk(DZero)
      case AONE(bs) => mk(DOne(bs))
      case ACHAR(bs, c) => mk(DChar(bs, c))
      case ASEQ(bs, r1, r2) => mk(DSeq(bs, fromARexp(r1), fromARexp(r2)))
      case AALTs(bs, rs) => mk(DAlts(bs, rs.map(fromARexp)))
      case ASTAR(bs, body) => mk(DStar(bs, fromARexp(body)))
      case ANTIMES(bs, body, n) => mk(DNTimes(bs, fromARexp(body), n))
    }

    def toARexp(id: Int): ARexp = node(id) match {
      case DZero => AZERO
      case DOne(bs) => AONE(bs)
      case DChar(bs, c) => ACHAR(bs, c)
      case DSeq(bs, r1, r2) => ASEQ(bs, toARexp(r1), toARexp(r2))
      case DAlts(bs, rs) => AALTs(bs, rs.map(toARexp))
      case DStar(bs, body) => ASTAR(bs, toARexp(body))
      case DNTimes(bs, body, n) => ANTIMES(bs, toARexp(body), n)
    }

    def fuseId(bs: List[Bit], id: Int): Int =
      if (bs.isEmpty || eraseBits) id
      else node(id) match {
        case DZero => mk(DZero)
        case DOne(cs) => mk(DOne(appendBits(bs, cs)))
        case DChar(cs, c) => mk(DChar(appendBits(bs, cs), c))
        case DSeq(cs, r1, r2) => mk(DSeq(appendBits(bs, cs), r1, r2))
        case DAlts(cs, rs) => mk(DAlts(appendBits(bs, cs), rs))
        case DStar(cs, r) => mk(DStar(appendBits(bs, cs), r))
        case DNTimes(cs, r, n) => mk(DNTimes(appendBits(bs, cs), r, n))
      }

    private val nullableCache = scala.collection.mutable.HashMap.empty[Int, Boolean]
    private val epsCache = scala.collection.mutable.HashMap.empty[Int, List[Bit]]
    private val eq1Cache = scala.collection.mutable.HashMap.empty[(Int, Int), Boolean]

    def bnullableId(id: Int): Boolean =
      nullableCache.getOrElseUpdate(id, node(id) match {
        case DZero => false
        case DOne(_) => true
        case DChar(_, _) => false
        case DSeq(_, r1, r2) => bnullableId(r1) && bnullableId(r2)
        case DAlts(_, rs) => rs.exists(bnullableId)
        case DStar(_, _) => true
        case DNTimes(_, r, n) => if (n == 0) true else bnullableId(r)
      })

    def bmkepsId(id: Int): List[Bit] =
      if (eraseBits) Nil
      else {
        epsCache.getOrElseUpdate(id, node(id) match {
          case DOne(bs) => bs
          case DSeq(bs, r1, r2) => bs ++ bmkepsId(r1) ++ bmkepsId(r2)
          case DAlts(bs, r :: rs) =>
            if (bnullableId(r)) bs ++ bmkepsId(r)
            else bmkepsId(mk(DAlts(bs, rs)))
          case DStar(bs, _) => bs ++ List(S)
          case DNTimes(bs, r, n) =>
            if (n == 0) bs ++ List(S)
            else bs ++ List(Z) ++ bmkepsId(r) ++ bmkepsId(mk(DNTimes(Nil, r, n - 1)))
          case other => sys.error(s"bmkepsId on non-nullable or malformed expression: $other")
        })
      }

    def eq1Id(x: Int, y: Int): Boolean = {
      val key = if (x <= y) (x, y) else (y, x)
      eq1Cache.getOrElseUpdate(key, (node(x), node(y)) match {
        case (DZero, DZero) => true
        case (DOne(_), DOne(_)) => true
        case (DChar(_, c), DChar(_, d)) => c == d
        case (DSeq(_, a1, a2), DSeq(_, b1, b2)) => eq1Id(a1, b1) && eq1Id(a2, b2)
        case (DAlts(_, xs), DAlts(_, ys)) =>
          xs.length == ys.length && xs.zip(ys).forall { case (a, b) => eq1Id(a, b) }
        case (DStar(_, a), DStar(_, b)) => eq1Id(a, b)
        case (DNTimes(_, a, n), DNTimes(_, b, m)) => n == m && eq1Id(a, b)
        case _ => false
      })
    }

    def eq1MemberId(r: Int, rs: List[Int]): Boolean =
      rs.exists(eq1Id(r, _))

    def eq1ListId(xs: List[Int], ys: List[Int]): Boolean =
      xs.length == ys.length && xs.zip(ys).forall { case (x, y) => eq1Id(x, y) }

    def pruneEq1AgainstId(covered: List[Int], rs: List[Int]): List[Int] =
      rs.filterNot(r => eq1MemberId(r, covered))

    def onlyARegexId(id: Int): Boolean = node(id) match {
      case DZero => true
      case DOne(_) => true
      case DChar(_, c) => c == 'a'
      case DSeq(_, r1, r2) => onlyARegexId(r1) && onlyARegexId(r2)
      case DAlts(_, rs) => rs.forall(onlyARegexId)
      case DStar(_, body) => onlyARegexId(body)
      case DNTimes(_, body, _) => onlyARegexId(body)
    }

    def isAStarId(id: Int): Boolean = node(id) match {
      case DStar(_, body) => aRunLen(body).contains(1)
      case _ => false
    }

    def cheapCoveredByRowsId(row: Int, covered: List[Int]): Boolean =
      eq1MemberId(row, covered) || (onlyARegexId(row) && covered.exists(isAStarId))

    def pruneCheapAgainstId(covered: List[Int], rs: List[Int]): List[Int] =
      rs.filterNot(r => cheapCoveredByRowsId(r, covered))

    def fltsIds(rs: List[Int]): List[Int] = rs match {
      case Nil => Nil
      case r :: tail =>
        node(r) match {
          case DZero => fltsIds(tail)
          case DAlts(bs, xs) => xs.map(fuseId(bs, _)) ++ fltsIds(tail)
          case _ => r :: fltsIds(tail)
        }
    }

    def distinctWithIds(xs: List[Int]): List[Int] = {
      @tailrec
      def loop(todo: List[Int], acc: List[Int], out: List[Int]): List[Int] = todo match {
        case Nil => out.reverse
        case x :: rest =>
          if (acc.exists(eq1Id(x, _))) loop(rest, acc, out)
          else loop(rest, x :: acc, x :: out)
      }
      loop(xs, Nil, Nil)
    }

    def bsimpAALTsId(bs: List[Bit], rs: List[Int]): Int = rs match {
      case Nil => mk(DZero)
      case r :: Nil => fuseId(bs, r)
      case _ => mk(DAlts(bs, rs))
    }

    def bsimp4ASEQAtomId(bs: List[Bit], r1: Int, r2: Int): Int =
      (node(r1), node(r2)) match {
        case (DZero, _) => mk(DZero)
        case (DOne(bs2), _) => fuseId(bs ++ bs2, r2)
        case (DSeq(bs2, a, b), _) =>
          bsimp4ASEQAtomId(bs2, a, bsimp4ASEQAtomId(bs, b, r2))
        case (_, DZero) => mk(DZero)
        case (_, DOne(_)) => fuseId(bs, r1)
        case _ => mk(DSeq(bs, r1, r2))
      }

    def bsimp7ASEQAtomId(bs: List[Bit], r1: Int, r2: Int): Int =
      (node(r1), node(r2)) match {
        case (DStar(_, a), DStar(_, b)) if eq1Id(a, b) => r1
        case (DStar(_, a), DSeq(_, left, k)) =>
          node(left) match {
            case DStar(_, b) if eq1Id(a, b) => mk(DSeq(bs, r1, k))
            case _ => bsimp4ASEQAtomId(bs, r1, r2)
          }
        case _ => bsimp4ASEQAtomId(bs, r1, r2)
      }

    def bsimpStrongPrunePairId(earlier: Int, later: Int): Int =
      (node(earlier), node(later)) match {
        case (DSeq(_, left, k1), DSeq(bs2, right, k2)) if eq1Id(k1, k2) =>
          (node(left), node(right)) match {
            case (DAlts(_, lrs), DAlts(rbs, rrs)) =>
              bsimp7ASEQAtomId(bs2, bsimpAALTsId(rbs, pruneEq1AgainstId(lrs, rrs)), k2)
            case _ => later
          }
        case _ => later
      }

    def bsimpStrongPruneRowsId(rs: List[Int]): List[Int] = {
      def loop(seen: List[Int], todo: List[Int]): List[Int] = todo match {
        case Nil => Nil
        case r :: rest =>
          val pruned = seen.foldLeft(r)((acc, earlier) =>
            bsimpStrongPrunePairId(earlier, acc))
          pruned :: loop(pruned :: seen, rest)
      }
      loop(Nil, rs)
    }

    def bsimpStrongAALTsId(bs: List[Bit], rs: List[Int]): Int =
      bsimpAALTsId(bs, distinctWithIds(fltsIds(bsimpStrongPruneRowsId(rs))))

    def bsimpStrongId(id: Int): Int = node(id) match {
      case DSeq(bs, r1, r2) =>
        bsimp7ASEQAtomId(bs, bsimpStrongId(r1), bsimpStrongId(r2))
      case DAlts(bs, rs) =>
        bsimpStrongAALTsId(bs, fltsIds(rs.map(bsimpStrongId)))
      case DStar(bs, r) =>
        val s = bsimpStrongId(r)
        node(s) match {
          case DZero => mk(DOne(Nil))
          case DOne(_) => mk(DOne(Nil))
          case DStar(bs2, body) => mk(DStar(bs2, body))
          case _ => mk(DStar(bs, s))
        }
      case DNTimes(bs, body, n) => mk(DNTimes(bs, bsimpStrongId(body), n))
      case _ => id
    }

    def bpderListId(c: Char, id: Int): List[Int] = node(id) match {
      case DZero => Nil
      case DOne(_) => Nil
      case DChar(bs, d) => if (c == d) List(mk(DOne(bs))) else Nil
      case DAlts(bs, rs) => rs.flatMap(bpderListId(c, _)).map(fuseId(bs, _))
      case DSeq(bs, r1, r2) =>
        val left = bpderListId(c, r1).map(p => bsimp4ASEQAtomId(bs, p, r2))
        val right =
          if (bnullableId(r1)) bpderListId(c, r2).map(p => fuseId(bs, fuseId(bmkepsId(r1), p)))
          else Nil
        left ++ right
      case DStar(bs, body) =>
        bpderListId(c, body).map(p =>
          bsimp4ASEQAtomId(bs ++ List(Z), p, mk(DStar(Nil, body))))
      case DNTimes(bs, body, n) =>
        if (n == 0) Nil
        else bpderListId(c, body).map(p =>
          bsimp4ASEQAtomId(bs ++ List(Z), p, mk(DNTimes(Nil, body, n - 1))))
    }

    def bpderNormListId(c: Char, id: Int): List[Int] =
      bpderListId(c, id).map(p => bsimp4ASEQAtomId(Nil, p, mk(DOne(Nil))))

    def bpderStrongListId(c: Char, id: Int): List[Int] =
      bpderNormListId(c, id).map(bsimpStrongId)

    def bpderStrongRowsId(c: Char, rs: List[Int]): List[Int] =
      distinctWithIds(fltsIds(bsimpStrongPruneRowsId(fltsIds(rs.flatMap(bpderStrongListId(c, _))))))

    def bpdersStrongRowsId(rs: List[Int], input: String): List[Int] =
      input.foldLeft(rs)((acc, c) => bpderStrongRowsId(c, acc))

    def bpdersStrong1RowsId(root: Int, input: String): List[Int] =
      bpdersStrongRowsId(List(root), input)

    def bdersStrongId(root: Int, input: String): Int =
      input.foldLeft(root)((acc, c) => bsimpStrongId(bderId(c, acc)))

    def bsimpCubicASEQAtomModeId(mode: String, bs: List[Bit], r1: Int, r2: Int): Int =
      mode match {
        case "full" =>
          node(r1) match {
            case DZero => mk(DZero)
            case DOne(bs2) => fuseId(bs ++ bs2, r2)
            case DSeq(bs2, a, b) =>
              bsimpCubicASEQAtomModeId(mode, bs2, a,
                bsimpCubicASEQAtomModeId(mode, bs, b, r2))
            case _ =>
              node(r2) match {
                case DZero => mk(DZero)
                case DOne(Nil) => fuseId(bs, r1)
                case _ => mk(DSeq(bs, r1, r2))
              }
          }
        case "none" => mk(DSeq(bs, r1, r2))
        case "keyed-no-reassoc" | "expanded-keyed-no-reassoc" | "unary-cover-no-reassoc" =>
          bsimpCubicASEQAtomModeId("no-reassoc", bs, r1, r2)
        case "reassoc-nonnullable-left" =>
          node(r1) match {
            case DSeq(bs2, a, b) if !bnullableId(a) =>
              bsimpCubicASEQAtomModeId(mode, bs2, a,
                bsimpCubicASEQAtomModeId(mode, bs, b, r2))
            case _ => bsimpCubicASEQAtomModeId("no-reassoc", bs, r1, r2)
          }
        case "no-reassoc" =>
          node(r1) match {
            case DZero => mk(DZero)
            case DOne(bs2) => fuseId(bs ++ bs2, r2)
            case _ =>
              node(r2) match {
                case DZero => mk(DZero)
                case DOne(Nil) => fuseId(bs, r1)
                case _ => mk(DSeq(bs, r1, r2))
              }
          }
        case "no-left-one" =>
          node(r1) match {
            case DZero => mk(DZero)
            case DSeq(bs2, a, b) =>
              bsimpCubicASEQAtomModeId(mode, bs2, a,
                bsimpCubicASEQAtomModeId(mode, bs, b, r2))
            case _ =>
              node(r2) match {
                case DZero => mk(DZero)
                case DOne(Nil) => fuseId(bs, r1)
                case _ => mk(DSeq(bs, r1, r2))
              }
          }
        case "no-right-one" =>
          node(r1) match {
            case DZero => mk(DZero)
            case DOne(bs2) => fuseId(bs ++ bs2, r2)
            case DSeq(bs2, a, b) =>
              bsimpCubicASEQAtomModeId(mode, bs2, a,
                bsimpCubicASEQAtomModeId(mode, bs, b, r2))
            case _ =>
              node(r2) match {
                case DZero => mk(DZero)
                case _ => mk(DSeq(bs, r1, r2))
              }
          }
        case "zeros-only" =>
          (node(r1), node(r2)) match {
            case (DZero, _) => mk(DZero)
            case (_, DZero) => mk(DZero)
            case _ => mk(DSeq(bs, r1, r2))
          }
        case other => throw new IllegalArgumentException(
          s"unknown POSIX_SMOKE_SEQ_MODE=$other; expected full, none, keyed-no-reassoc, expanded-keyed-no-reassoc, unary-cover-no-reassoc, reassoc-nonnullable-left, no-reassoc, no-left-one, no-right-one, or zeros-only"
        )
      }

    def seqFactorsId(id: Int): List[Int] = node(id) match {
      case DSeq(_, r1, r2) => seqFactorsId(r1) ++ seqFactorsId(r2)
      case _ => List(id)
    }

    def seqCoverRowsId(id: Int): Option[(List[Int], Int)] = node(id) match {
      case DSeq(_, rowBlock, k) =>
        node(rowBlock) match {
          case DAlts(_, rows) => Some((rows, k))
          case _ => Some((List(rowBlock), k))
        }
      case _ => None
    }

    def seqCoverRowsKeyId(id: Int): Option[(List[Int], List[Int])] =
      seqFactorsId(id) match {
        case Nil => None
        case first :: tail =>
          node(first) match {
            case DAlts(_, rows) => Some((rows, tail))
            case _ => Some((List(first), tail))
          }
      }

    def expandedSeqKeysId(id: Int, maxKeys: Int): Option[List[List[Int]]] = {
      def choices(f: Int): List[Int] = node(f) match {
        case DAlts(_, rows) => rows
        case _ => List(f)
      }
      def step(acc: List[List[Int]], f: Int): Option[List[List[Int]]] = {
        val cs = choices(f)
        val next = for { key <- acc; c <- cs } yield key :+ c
        if (next.length > maxKeys) None else Some(next)
      }
      seqFactorsId(id).foldLeft(Option(List(List.empty[Int]))) {
        case (Some(acc), f) => step(acc, f)
        case (None, _) => None
      }
    }

    def seqKeyMemberId(key: List[Int], keys: List[List[Int]]): Boolean =
      keys.exists(eq1ListId(key, _))

    def seqKeysCoveredId(keys: List[List[Int]], covered: List[List[Int]]): Boolean =
      keys.nonEmpty && keys.forall(seqKeyMemberId(_, covered))

    def bsimpCubicPrunePairModeId(seqMode: String, earlier: Int, later: Int): Int =
      if (seqMode == "expanded-keyed-no-reassoc") {
        val maxKeys = 5000
        expandedSeqKeysId(earlier, maxKeys) match {
          case Some(covered) =>
            node(later) match {
              case DSeq(bs2, rowBlock, k2) =>
                node(rowBlock) match {
                  case DAlts(rbs, rrs) =>
                    val kept = rrs.filterNot { row =>
                      expandedSeqKeysId(mk(DSeq(Nil, row, k2)), maxKeys)
                        .exists(seqKeysCoveredId(_, covered))
                    }
                    if (kept == rrs) later
                    else bsimpCubicASEQAtomModeId(seqMode, bs2, bsimpAALTsId(rbs, kept), k2)
                  case _ =>
                    expandedSeqKeysId(later, maxKeys) match {
                      case Some(laterKeys) if seqKeysCoveredId(laterKeys, covered) => mk(DZero)
                      case _ => later
                    }
                }
              case _ =>
                expandedSeqKeysId(later, maxKeys) match {
                  case Some(laterKeys) if seqKeysCoveredId(laterKeys, covered) => mk(DZero)
                  case _ => later
                }
            }
          case None => later
        }
      } else if (seqMode == "keyed-no-reassoc") {
        (seqCoverRowsKeyId(earlier), seqCoverRowsKeyId(later), node(later)) match {
          case (Some((covered, tail1)), Some((_, tail2)), DSeq(bs2, rowBlock, k2)) if eq1ListId(tail1, tail2) =>
            node(rowBlock) match {
              case DAlts(rbs, rrs) =>
                bsimpCubicASEQAtomModeId(seqMode, bs2, bsimpAALTsId(rbs, pruneEq1AgainstId(covered, rrs)), k2)
              case _ => later
            }
          case (Some((covered, tail1)), Some((laterRows, tail2)), _) if eq1ListId(tail1, tail2) && laterRows.exists(eq1MemberId(_, covered)) =>
            mk(DZero)
          case _ => later
        }
      } else if (seqMode == "unary-cover-no-reassoc") {
        (seqCoverRowsId(earlier), node(later)) match {
          case (Some((covered, k1)), DSeq(bs2, rowBlock, k2)) if eq1Id(k1, k2) =>
            node(rowBlock) match {
              case DAlts(rbs, rrs) =>
                bsimpCubicASEQAtomModeId(seqMode, bs2, bsimpAALTsId(rbs, pruneCheapAgainstId(covered, rrs)), k2)
              case _ if cheapCoveredByRowsId(rowBlock, covered) => mk(DZero)
              case _ => later
            }
          case _ => later
        }
      } else {
        (seqCoverRowsId(earlier), node(later)) match {
          case (Some((covered, k1)), DSeq(bs2, rowBlock, k2)) if eq1Id(k1, k2) =>
            node(rowBlock) match {
              case DAlts(rbs, rrs) =>
                bsimpCubicASEQAtomModeId(seqMode, bs2, bsimpAALTsId(rbs, pruneEq1AgainstId(covered, rrs)), k2)
              case _ if eq1MemberId(rowBlock, covered) => mk(DZero)
              case _ => later
            }
          case _ => later
        }
      }

    def bsimpCubicPruneRowsModeId(seqMode: String, rs: List[Int]): List[Int] = {
      def loop(seen: List[Int], todo: List[Int]): List[Int] = todo match {
        case Nil => Nil
        case r :: rest =>
          val pruned = seen.foldLeft(r)((acc, earlier) =>
            bsimpCubicPrunePairModeId(seqMode, earlier, acc))
          pruned :: loop(pruned :: seen, rest)
      }
      loop(Nil, rs)
    }

    def bsimpCubicAALTsWithModeId(seqMode: String, bs: List[Bit], rs: List[Int]): Int =
      bsimpAALTsId(bs, distinctWithIds(fltsIds(bsimpCubicPruneRowsModeId(seqMode, rs))))

    def bsimpCubicWithModeId(seqMode: String, id: Int): Int = node(id) match {
      case DSeq(bs, r1, r2) =>
        bsimpCubicASEQAtomModeId(seqMode, bs,
          bsimpCubicWithModeId(seqMode, r1),
          bsimpCubicWithModeId(seqMode, r2))
      case DAlts(bs, rs) =>
        bsimpCubicAALTsWithModeId(seqMode, bs,
          fltsIds(rs.map(bsimpCubicWithModeId(seqMode, _))))
      case DStar(bs, r) =>
        val s = bsimpCubicWithModeId(seqMode, r)
        node(s) match {
          case DZero => mk(DOne(bs ++ List(S)))
          case DOne(_) => mk(DOne(bs ++ List(S)))
          case _ => mk(DStar(bs, s))
        }
      case DNTimes(bs, r, n) =>
        if (n == 0) mk(DOne(bs ++ List(S)))
        else {
          val s = bsimpCubicWithModeId(seqMode, r)
          node(s) match {
            case DZero => mk(DZero)
            case DOne(_) => mk(DOne(bmkepsId(mk(DNTimes(bs, s, n)))))
            case _ => mk(DNTimes(bs, s, n))
          }
        }
      case _ => id
    }

    def bderId(c: Char, id: Int): Int = node(id) match {
      case DZero => mk(DZero)
      case DOne(_) => mk(DZero)
      case DChar(bs, d) => if (c == d) mk(DOne(bs)) else mk(DZero)
      case DAlts(bs, rs) => mk(DAlts(bs, rs.map(bderId(c, _))))
      case DSeq(bs, r1, r2) =>
        if (bnullableId(r1)) {
          mk(DAlts(bs, List(
            mk(DSeq(Nil, bderId(c, r1), r2)),
            fuseId(bmkepsId(r1), bderId(c, r2))
          )))
        } else {
          mk(DSeq(bs, bderId(c, r1), r2))
        }
      case DStar(bs, body) =>
        mk(DSeq(bs ++ List(Z), bderId(c, body), mk(DStar(Nil, body))))
      case DNTimes(bs, body, n) =>
        if (n == 0) mk(DZero)
        else mk(DSeq(bs ++ List(Z), bderId(c, body), mk(DNTimes(Nil, body, n - 1))))
    }

    def stepWithMode(seqMode: String, c: Char, root: Int): Int =
      derCache.getOrElseUpdate((seqMode, c, root), {
        fromARexp(bsimpCubicWithMode(seqMode, bder(c, toARexp(root))))
      })

    def stepDirectWithMode(seqMode: String, c: Char, root: Int): Int =
      derCache.getOrElseUpdate((s"direct:$seqMode", c, root), {
        bsimpCubicWithModeId(seqMode, bderId(c, root))
      })

    def bdersWithMode(seqMode: String, root: Int, s: String): Int =
      s.foldLeft(root)((acc, c) => stepWithMode(seqMode, c, acc))

    def bdersDirectWithMode(seqMode: String, root: Int, s: String): Int =
      s.foldLeft(root)((acc, c) => stepDirectWithMode(seqMode, c, acc))

    def reachableIds(root: Int): Set[Int] = {
      val seen = scala.collection.mutable.Set.empty[Int]
      def visit(id: Int): Unit = {
        if (seen.add(id)) {
          node(id) match {
            case DSeq(_, r1, r2) => visit(r1); visit(r2)
            case DAlts(_, rs) => rs.foreach(visit)
            case DStar(_, body) => visit(body)
            case DNTimes(_, body, _) => visit(body)
            case _ => ()
          }
        }
      }
      visit(root)
      seen.toSet
    }

    private sealed trait ShapeForm
    private case object FZero extends ShapeForm
    private case object FOne extends ShapeForm
    private final case class FChar(c: Char) extends ShapeForm
    private final case class FSeq(r1: Int, r2: Int) extends ShapeForm
    private final case class FAlts(rs: Vector[Int]) extends ShapeForm
    private final case class FStar(body: Int) extends ShapeForm
    private final case class FNTimes(body: Int, n: Int) extends ShapeForm
    private final case class FRunA(n: Int) extends ShapeForm
    private final case class FPatSet(ps: Vector[(Int, Int, Int)]) extends ShapeForm

    private val shapeMemo = scala.collection.mutable.HashMap.empty[Int, String]
    private val altSetShapeMemo = scala.collection.mutable.HashMap.empty[Int, String]
    private val shapeIdMemo = scala.collection.mutable.HashMap.empty[Int, Int]
    private val altSetShapeIdMemo = scala.collection.mutable.HashMap.empty[Int, Int]
    private val unaryModShapeIdMemo = scala.collection.mutable.HashMap.empty[Int, Int]
    private val unaryPruneShapeIdMemo = scala.collection.mutable.HashMap.empty[Int, Int]
    private val contPruneShapeIdMemo = scala.collection.mutable.HashMap.empty[Int, Int]
    private val unaryPatsApproxMemo = scala.collection.mutable.HashMap.empty[Int, Option[List[UnaryPat]]]
    private val langContPruneShapeIdMemo = scala.collection.mutable.HashMap.empty[Int, Int]
    private val langAtomicContPruneShapeIdMemo = scala.collection.mutable.HashMap.empty[Int, Int]
    private val shapeIntern = scala.collection.mutable.HashMap.empty[ShapeForm, Int]
    private var nextShapeId = 0

    private def internShape(form: ShapeForm): Int =
      shapeIntern.getOrElseUpdate(form, {
        val id = nextShapeId
        nextShapeId += 1
        id
      })

    def shapeKey(id: Int): String =
      shapeMemo.getOrElseUpdate(id, node(id) match {
        case DZero => "0"
        case DOne(_) => "1"
        case DChar(_, c) => s"c($c)"
        case DSeq(_, r1, r2) => s".(${shapeKey(r1)},${shapeKey(r2)})"
        case DAlts(_, rs) => s"+(${rs.map(shapeKey).mkString(",")})"
        case DStar(_, body) => s"*(${shapeKey(body)})"
        case DNTimes(_, body, n) => s"n($n,${shapeKey(body)})"
      })

    def shapeId(id: Int): Int =
      shapeIdMemo.getOrElseUpdate(id, node(id) match {
        case DZero => internShape(FZero)
        case DOne(_) => internShape(FOne)
        case DChar(_, c) => internShape(FChar(c))
        case DSeq(_, r1, r2) => internShape(FSeq(shapeId(r1), shapeId(r2)))
        case DAlts(_, rs) => internShape(FAlts(rs.map(shapeId).toVector))
        case DStar(_, body) => internShape(FStar(shapeId(body)))
        case DNTimes(_, body, n) => internShape(FNTimes(shapeId(body), n))
      })

    def reachableShapeSize(root: Int): Int =
      reachableIds(root).map(shapeId).size

    private def runShapeId(n: Int): Int =
      if (n == 0) internShape(FOne) else internShape(FRunA(n))

    def altSetShapeKey(id: Int): String =
      altSetShapeMemo.getOrElseUpdate(id, node(id) match {
        case DZero => "0"
        case DOne(_) => "1"
        case DChar(_, c) => s"c($c)"
        case DSeq(_, r1, r2) => s".(${altSetShapeKey(r1)},${altSetShapeKey(r2)})"
        case DAlts(_, rs) => s"+(${rs.map(altSetShapeKey).distinct.sorted.mkString(",")})"
        case DStar(_, body) => s"*(${altSetShapeKey(body)})"
        case DNTimes(_, body, n) => s"n($n,${altSetShapeKey(body)})"
      })

    def altSetShapeId(id: Int): Int =
      altSetShapeIdMemo.getOrElseUpdate(id, node(id) match {
        case DZero => internShape(FZero)
        case DOne(_) => internShape(FOne)
        case DChar(_, c) => internShape(FChar(c))
        case DSeq(_, r1, r2) => internShape(FSeq(altSetShapeId(r1), altSetShapeId(r2)))
        case DAlts(_, rs) => internShape(FAlts(rs.map(altSetShapeId).distinct.sorted.toVector))
        case DStar(_, body) => internShape(FStar(altSetShapeId(body)))
        case DNTimes(_, body, n) => internShape(FNTimes(altSetShapeId(body), n))
      })

    def aRunLen(id: Int): Option[Int] = node(id) match {
      case DOne(_) => Some(0)
      case DChar(_, 'a') => Some(1)
      case DSeq(_, r1, r2) =>
        for {
          n1 <- aRunLen(r1)
          n2 <- aRunLen(r2)
        } yield n1 + n2
      case _ => None
    }

    def unaryModShapeId(id: Int): Int =
      unaryModShapeIdMemo.getOrElseUpdate(id, node(id) match {
        case DZero => internShape(FZero)
        case DOne(_) => internShape(FOne)
        case DChar(_, 'a') => runShapeId(1)
        case DChar(_, c) => internShape(FChar(c))
        case DSeq(_, r1, r2) =>
          (aRunLen(r1), node(r2)) match {
            case (Some(prefix), DStar(_, body)) =>
              aRunLen(body) match {
                case Some(period) if period > 0 =>
                  val residue = prefix % period
                  val star = internShape(FStar(runShapeId(period)))
                  if (residue == 0) star else internShape(FSeq(runShapeId(residue), star))
                case _ =>
                  internShape(FSeq(unaryModShapeId(r1), unaryModShapeId(r2)))
              }
            case _ =>
              aRunLen(id) match {
                case Some(n) => runShapeId(n)
                case None => internShape(FSeq(unaryModShapeId(r1), unaryModShapeId(r2)))
              }
          }
        case DAlts(_, rs) => internShape(FAlts(rs.map(unaryModShapeId).toVector))
        case DStar(_, body) =>
          aRunLen(body) match {
            case Some(period) if period > 0 => internShape(FStar(runShapeId(period)))
            case _ => internShape(FStar(unaryModShapeId(body)))
          }
        case DNTimes(_, body, n) => internShape(FNTimes(unaryModShapeId(body), n))
      })

    private sealed trait UnaryPat
    private final case class UFinite(n: Int) extends UnaryPat
    private final case class UResidue(start: Int, period: Int) extends UnaryPat

    private def unaryPatId(id: Int): Option[UnaryPat] =
      aRunLen(id).map(UFinite.apply).orElse {
        node(id) match {
          case DStar(_, body) =>
            aRunLen(body).collect { case period if period > 0 => UResidue(0, period) }
          case DSeq(_, r1, r2) =>
            (aRunLen(r1), node(r2)) match {
              case (Some(start), DStar(_, body)) =>
                aRunLen(body).collect { case period if period > 0 => UResidue(start, period) }
              case _ => None
            }
          case _ => None
        }
      }

    private def unaryPatCovers(earlier: UnaryPat, later: UnaryPat): Boolean =
      (earlier, later) match {
        case (UFinite(m), UFinite(n)) => m == n
        case (UResidue(start, period), UFinite(n)) =>
          n >= start && (n - start) % period == 0
        case (UResidue(start1, period1), UResidue(start2, period2)) =>
          period1 == period2 && start2 >= start1 && (start2 - start1) % period1 == 0
        case _ => false
      }

    private def gcd(a0: Int, b0: Int): Int = {
      var a = math.abs(a0)
      var b = math.abs(b0)
      while (b != 0) {
        val t = a % b
        a = b
        b = t
      }
      if (a == 0) 1 else a
    }

    private def lcm(a: Int, b: Int): Int = {
      val g = gcd(a, b)
      val raw = (a / g).toLong * b.toLong
      if (raw > 1000000L) 1000000 else raw.toInt
    }

    private def unaryPatContains(pat: UnaryPat, n: Int): Boolean = pat match {
      case UFinite(m) => m == n
      case UResidue(start, period) => n >= start && (n - start) % period == 0
    }

    private def unaryPatSubsetOfUnion(later: UnaryPat, earlier: List[UnaryPat]): Boolean =
      later match {
        case UFinite(n) => earlier.exists(unaryPatContains(_, n))
        case UResidue(start, period) =>
          val earlierResidues = earlier.collect { case r @ UResidue(_, _) => r }
          if (earlierResidues.isEmpty) false
          else {
            val modulus = (period :: earlierResidues.map(_.period)).foldLeft(1)(lcm)
            val maxStart = (start :: earlierResidues.map(_.start)).max
            val upper = math.max(start, maxStart) + modulus
            var n = start
            var ok = true
            while (ok && n <= upper) {
              ok = earlier.exists(unaryPatContains(_, n))
              n += period
            }
            ok
          }
      }

    private def rowPatsCoveredBy(earlier: List[UnaryPat], later: List[UnaryPat]): Boolean =
      later.forall(unaryPatSubsetOfUnion(_, earlier))

    private def rowBlockPats(id: Int): Option[List[UnaryPat]] =
      node(id) match {
        case DZero => Some(Nil)
        case DAlts(_, rs) =>
          val pats = rs.map(unaryPatId)
          if (pats.forall(_.isDefined)) Some(pats.flatten) else None
        case _ => unaryPatId(id).map(List(_))
      }

    private def patKey(p: UnaryPat): (Int, Int, Int) = p match {
      case UFinite(n) => (0, n, 0)
      case UResidue(start, period) => (1, start, period)
    }

    private def normalizePats(ps: List[UnaryPat]): List[UnaryPat] = {
      val kept = scala.collection.mutable.ListBuffer.empty[UnaryPat]
      ps.foreach { p =>
        if (!kept.exists(unaryPatCovers(_, p))) {
          val survivors = kept.filterNot(unaryPatCovers(p, _)).toList
          kept.clear()
          kept ++= survivors
          kept += p
        }
      }
      kept.toList.sortBy(patKey)
    }

    private def patSetShapeId(ps: List[UnaryPat]): Int =
      internShape(FPatSet(normalizePats(ps).map(patKey).toVector))

    private def sumPat(x: UnaryPat, y: UnaryPat): UnaryPat =
      (x, y) match {
        case (UFinite(m), UFinite(n)) => UFinite(m + n)
        case (UFinite(m), UResidue(start, period)) => UResidue(m + start, period)
        case (UResidue(start, period), UFinite(m)) => UResidue(start + m, period)
        case (UResidue(start1, period1), UResidue(start2, period2)) =>
          UResidue(start1 + start2, gcd(period1, period2))
      }

    private def sumPats(xs: List[UnaryPat], ys: List[UnaryPat]): List[UnaryPat] =
      normalizePats(for { x <- xs; y <- ys } yield sumPat(x, y))

    private def starPats(ps: List[UnaryPat]): List[UnaryPat] = {
      val generators = ps.flatMap {
        case UFinite(n) if n > 0 => List(n)
        case UResidue(start, period) if start > 0 => List(start, period)
        case UResidue(_, period) => List(period)
        case _ => Nil
      }
      if (generators.isEmpty) List(UFinite(0))
      else List(UResidue(0, generators.foldLeft(0)(gcd)))
    }

    private def unaryPatsApproxId(id: Int): Option[List[UnaryPat]] =
      unaryPatsApproxMemo.getOrElseUpdate(id, node(id) match {
        case DZero => Some(Nil)
        case DOne(_) => Some(List(UFinite(0)))
        case DChar(_, 'a') => Some(List(UFinite(1)))
        case DChar(_, _) => None
        case DSeq(_, r1, r2) =>
          for {
            ps1 <- unaryPatsApproxId(r1)
            ps2 <- unaryPatsApproxId(r2)
          } yield sumPats(ps1, ps2)
        case DAlts(_, rs) =>
          val parts = rs.map(unaryPatsApproxId)
          if (parts.forall(_.isDefined)) Some(normalizePats(parts.flatten.flatten)) else None
        case DStar(_, body) =>
          unaryPatsApproxId(body).map(starPats)
        case DNTimes(_, body, n) =>
          if (n == 0) Some(List(UFinite(0)))
          else {
            unaryPatsApproxId(body).map { bodyPats =>
              (0 until n).foldLeft(List[UnaryPat](UFinite(0))) { case (acc, _) =>
                sumPats(acc, bodyPats)
              }
            }
          }
      })

    private def pruneUnaryCoveredIds(rs: List[Int]): List[Int] = {
      var covered = List.empty[UnaryPat]
      val kept = scala.collection.mutable.ListBuffer.empty[Int]
      rs.foreach { r =>
        unaryPatId(r) match {
          case Some(pat) if covered.exists(unaryPatCovers(_, pat)) => ()
          case Some(pat) =>
            kept += r
            covered = pat :: covered
          case None =>
            kept += r
        }
      }
      kept.toList
    }

    def unaryPruneShapeId(id: Int): Int =
      unaryPruneShapeIdMemo.getOrElseUpdate(id, node(id) match {
        case DZero => internShape(FZero)
        case DOne(_) => internShape(FOne)
        case DChar(_, 'a') => runShapeId(1)
        case DChar(_, c) => internShape(FChar(c))
        case DSeq(_, r1, r2) =>
          aRunLen(id) match {
            case Some(n) => runShapeId(n)
            case None => internShape(FSeq(unaryPruneShapeId(r1), unaryPruneShapeId(r2)))
          }
        case DAlts(_, rs) =>
          internShape(FAlts(pruneUnaryCoveredIds(rs).map(unaryPruneShapeId).toVector))
        case DStar(_, body) =>
          aRunLen(body) match {
            case Some(period) if period > 0 => internShape(FStar(runShapeId(period)))
            case _ => internShape(FStar(unaryPruneShapeId(body)))
          }
        case DNTimes(_, body, n) => internShape(FNTimes(unaryPruneShapeId(body), n))
      })

    def reachableUnaryPruneShapeIds(root: Int): Set[Int] = {
      val seenNodes = scala.collection.mutable.Set.empty[Int]
      val seenShapes = scala.collection.mutable.Set.empty[Int]
      def visit(id: Int): Unit = {
        if (seenNodes.add(id)) {
          seenShapes += unaryPruneShapeId(id)
          node(id) match {
            case DSeq(_, r1, r2) =>
              visit(r1)
              visit(r2)
            case DAlts(_, rs) =>
              pruneUnaryCoveredIds(rs).foreach(visit)
            case DStar(_, body) =>
              visit(body)
            case DNTimes(_, body, _) =>
              visit(body)
            case _ => ()
          }
        }
      }
      visit(root)
      seenShapes.toSet
    }

    private def branchRowsContinuationShape(id: Int): Option[(List[UnaryPat], Int)] =
      node(id) match {
        case DSeq(_, left, right) =>
          rowBlockPats(left).map(_ -> contPruneShapeId(right)).orElse {
            branchRowsContinuationShape(left).map { case (rows, cont) =>
              rows -> internShape(FSeq(cont, contPruneShapeId(right)))
            }
          }
        case _ => rowBlockPats(id).map(_ -> internShape(FOne))
      }

    private def pruneContinuationCoveredIds(rs: List[Int]): List[Int] = {
      val coveredByContinuation = scala.collection.mutable.HashMap.empty[Int, List[UnaryPat]]
      val kept = scala.collection.mutable.ListBuffer.empty[Int]
      rs.foreach { r =>
        branchRowsContinuationShape(r) match {
          case Some((rows, cont)) if rowPatsCoveredBy(coveredByContinuation.getOrElse(cont, Nil), rows) => ()
          case Some((rows, cont)) =>
            kept += r
            coveredByContinuation.update(cont, rows ++ coveredByContinuation.getOrElse(cont, Nil))
          case None =>
            kept += r
        }
      }
      kept.toList
    }

    def contPruneShapeId(id: Int): Int =
      contPruneShapeIdMemo.getOrElseUpdate(id, node(id) match {
        case DZero => internShape(FZero)
        case DOne(_) => internShape(FOne)
        case DChar(_, 'a') => runShapeId(1)
        case DChar(_, c) => internShape(FChar(c))
        case DSeq(_, r1, r2) =>
          aRunLen(id) match {
            case Some(n) => runShapeId(n)
            case None => internShape(FSeq(contPruneShapeId(r1), contPruneShapeId(r2)))
          }
        case DAlts(_, rs) =>
          internShape(FAlts(pruneContinuationCoveredIds(rs).map(contPruneShapeId).toVector))
        case DStar(_, body) =>
          aRunLen(body) match {
            case Some(period) if period > 0 => internShape(FStar(runShapeId(period)))
            case _ => internShape(FStar(contPruneShapeId(body)))
          }
        case DNTimes(_, body, n) => internShape(FNTimes(contPruneShapeId(body), n))
      })

    def reachableContPruneShapeIds(root: Int): Set[Int] = {
      val seenNodes = scala.collection.mutable.Set.empty[Int]
      val seenShapes = scala.collection.mutable.Set.empty[Int]
      def visit(id: Int): Unit = {
        if (seenNodes.add(id)) {
          seenShapes += contPruneShapeId(id)
          node(id) match {
            case DSeq(_, r1, r2) =>
              visit(r1)
              visit(r2)
            case DAlts(_, rs) =>
              pruneContinuationCoveredIds(rs).foreach(visit)
            case DStar(_, body) =>
              visit(body)
            case DNTimes(_, body, _) =>
              visit(body)
            case _ => ()
          }
        }
      }
      visit(root)
      seenShapes.toSet
    }

    private def branchRowsContinuationLangPats(id: Int): Option[(List[UnaryPat], List[UnaryPat])] =
      node(id) match {
        case DSeq(_, left, right) =>
          branchRowsContinuationLangPats(left).flatMap { case (rows, cont) =>
            unaryPatsApproxId(right).map { rightPats =>
              rows -> sumPats(cont, rightPats)
            }
          }.orElse {
            for {
              rows <- unaryPatsApproxId(left)
              cont <- unaryPatsApproxId(right)
            } yield rows -> cont
          }
        case _ => unaryPatsApproxId(id).map(_ -> List(UFinite(0)))
      }

    private def branchRowsContinuationLang(id: Int): Option[(List[UnaryPat], Int)] =
      branchRowsContinuationLangPats(id).map { case (rows, cont) =>
        rows -> patSetShapeId(cont)
      }

    private def pruneLangContinuationCoveredIds(rs: List[Int]): List[Int] = {
      val coveredByContinuation = scala.collection.mutable.HashMap.empty[Int, List[UnaryPat]]
      val kept = scala.collection.mutable.ListBuffer.empty[Int]
      rs.foreach { r =>
        branchRowsContinuationLang(r) match {
          case Some((rows, cont)) if rowPatsCoveredBy(coveredByContinuation.getOrElse(cont, Nil), rows) => ()
          case Some((rows, cont)) =>
            kept += r
            coveredByContinuation.update(cont, rows ++ coveredByContinuation.getOrElse(cont, Nil))
          case None =>
            kept += r
        }
      }
      kept.toList
    }

    def langContPruneShapeId(id: Int): Int =
      langContPruneShapeIdMemo.getOrElseUpdate(id, node(id) match {
        case DZero => patSetShapeId(Nil)
        case DOne(_) => patSetShapeId(List(UFinite(0)))
        case DChar(_, 'a') => patSetShapeId(List(UFinite(1)))
        case DChar(_, c) => internShape(FChar(c))
        case DSeq(_, r1, r2) =>
          unaryPatsApproxId(id) match {
            case Some(ps) => patSetShapeId(ps)
            case None => internShape(FSeq(langContPruneShapeId(r1), langContPruneShapeId(r2)))
          }
        case DAlts(_, rs) =>
          internShape(FAlts(pruneLangContinuationCoveredIds(rs).map(langContPruneShapeId).toVector))
        case DStar(_, body) =>
          unaryPatsApproxId(id) match {
            case Some(ps) => patSetShapeId(ps)
            case None => internShape(FStar(langContPruneShapeId(body)))
          }
        case DNTimes(_, body, n) =>
          unaryPatsApproxId(id) match {
            case Some(ps) => patSetShapeId(ps)
            case None => internShape(FNTimes(langContPruneShapeId(body), n))
          }
      })

    def reachableLangContPruneShapeIds(root: Int): Set[Int] = {
      val seenNodes = scala.collection.mutable.Set.empty[Int]
      val seenShapes = scala.collection.mutable.Set.empty[Int]
      def visit(id: Int): Unit = {
        if (seenNodes.add(id)) {
          seenShapes += langContPruneShapeId(id)
          node(id) match {
            case DSeq(_, r1, r2) =>
              visit(r1)
              visit(r2)
            case DAlts(_, rs) =>
              pruneLangContinuationCoveredIds(rs).foreach(visit)
            case DStar(_, body) =>
              visit(body)
            case DNTimes(_, body, _) =>
              visit(body)
            case _ => ()
          }
        }
      }
      visit(root)
      seenShapes.toSet
    }

    def langAtomicContPruneShapeId(id: Int): Int =
      langAtomicContPruneShapeIdMemo.getOrElseUpdate(id,
        unaryPatsApproxId(id) match {
          case Some(ps) => patSetShapeId(ps)
          case None =>
            node(id) match {
              case DZero => patSetShapeId(Nil)
              case DOne(_) => patSetShapeId(List(UFinite(0)))
              case DChar(_, 'a') => patSetShapeId(List(UFinite(1)))
              case DChar(_, c) => internShape(FChar(c))
              case DSeq(_, r1, r2) =>
                internShape(FSeq(langAtomicContPruneShapeId(r1), langAtomicContPruneShapeId(r2)))
              case DAlts(_, rs) =>
                internShape(FAlts(pruneLangContinuationCoveredIds(rs).map(langAtomicContPruneShapeId).toVector))
              case DStar(_, body) => internShape(FStar(langAtomicContPruneShapeId(body)))
              case DNTimes(_, body, n) => internShape(FNTimes(langAtomicContPruneShapeId(body), n))
            }
        })

    def reachableLangAtomicContPruneShapeIds(root: Int): Set[Int] = {
      val seenNodes = scala.collection.mutable.Set.empty[Int]
      val seenShapes = scala.collection.mutable.Set.empty[Int]
      def visit(id: Int): Unit = {
        if (seenNodes.add(id)) {
          seenShapes += langAtomicContPruneShapeId(id)
          if (unaryPatsApproxId(id).isEmpty) {
            node(id) match {
              case DSeq(_, r1, r2) =>
                visit(r1)
                visit(r2)
              case DAlts(_, rs) =>
                pruneLangContinuationCoveredIds(rs).foreach(visit)
              case DStar(_, body) =>
                visit(body)
              case DNTimes(_, body, _) =>
                visit(body)
              case _ => ()
            }
          }
        }
      }
      visit(root)
      seenShapes.toSet
    }

    def compactShapeKey(id: Int): String =
      aRunLen(id) match {
        case Some(0) => "1"
        case Some(n) => s"a^$n"
        case None =>
          node(id) match {
            case DZero => "0"
            case DOne(_) => "1"
            case DChar(_, c) => c.toString
            case DSeq(_, r1, r2) => s".(${compactShapeKey(r1)},${compactShapeKey(r2)})"
            case DAlts(_, rs) => rs.map(compactShapeKey).mkString("+(", ",", ")")
            case DStar(_, body) =>
              aRunLen(body) match {
                case Some(n) => s"(a^$n)*"
                case None => s"*(${compactShapeKey(body)})"
              }
            case DNTimes(_, body, n) => s"ntimes($n,${compactShapeKey(body)})"
          }
      }
  }

  final case class SharedResult(
      value: Option[Val],
      treeSize: Int,
      dagSize: Int,
      shapeDagSize: Int,
      statePoolSize: Int,
      shapeStatePoolSize: Int,
      altSetShapeStatePoolSize: Int,
      unaryModShapeStatePoolSize: Int,
      unaryPruneShapeStatePoolSize: Int,
      contPruneShapeStatePoolSize: Int,
      langContPruneShapeStatePoolSize: Int,
      langAtomicContPruneShapeStatePoolSize: Int,
      poolSize: Int
  )

  final case class SharedStatePoolObservation(
      label: String,
      regex: Rexp,
      input: String,
      regexSize: Int,
      statePoolSize: Int,
      ratio: Double
  )

  def sharedModeResult(
      seqMode: String,
      r: Rexp,
      input: String,
      directDag: Boolean = false,
      compareTree: Boolean = false
  ): SharedResult = {
    val store = new DagStore
    val root0 = store.fromARexp(intern(r))
    var root = root0
    var treeRegex = intern(r)
    var prefixRoots = List(root0)
    input.zipWithIndex.foreach { case (c, index) =>
      root =
        if (directDag) store.stepDirectWithMode(seqMode, c, root)
        else store.stepWithMode(seqMode, c, root)
      if (directDag && compareTree) {
        treeRegex = bsimpCubicWithMode(seqMode, bder(c, treeRegex))
        val directRegex = store.toARexp(root)
        if (directRegex != treeRegex) {
          throw new AssertionError(
            s"""direct-DAG/tree-step mismatch
               |seqMode = $seqMode
               |regex   = $r
               |input   = $input
               |prefix  = ${index + 1}
               |char    = $c
               |direct  = $directRegex
               |tree    = $treeRegex
               |""".stripMargin
          )
        }
      }
      prefixRoots = root :: prefixRoots
    }
    val finalRegex = store.toARexp(root)
    val value = if (bnullable(finalRegex)) decodeBits(r, bmkeps(finalRegex)) else None
    val prefixIds = prefixRoots.flatMap(store.reachableIds)
    val statePool = prefixIds.toSet.size
    val shapeStatePool = prefixIds.map(store.shapeId).toSet.size
    val altSetShapeStatePool = prefixIds.map(store.altSetShapeId).toSet.size
    val unaryModShapeStatePool = prefixIds.map(store.unaryModShapeId).toSet.size
    val unaryPruneShapeStatePool = prefixRoots.flatMap(store.reachableUnaryPruneShapeIds).toSet.size
    val contPruneShapeStatePool = prefixRoots.flatMap(store.reachableContPruneShapeIds).toSet.size
    val langContPruneShapeStatePool = prefixRoots.flatMap(store.reachableLangContPruneShapeIds).toSet.size
    val langAtomicContPruneShapeStatePool = prefixRoots.flatMap(store.reachableLangAtomicContPruneShapeIds).toSet.size
    SharedResult(
      value,
      asize(finalRegex),
      store.reachableIds(root).size,
      store.reachableShapeSize(root),
      statePool,
      shapeStatePool,
      altSetShapeStatePool,
      unaryModShapeStatePool,
      unaryPruneShapeStatePool,
      contPruneShapeStatePool,
      langContPruneShapeStatePool,
      langAtomicContPruneShapeStatePool,
      store.totalSize
    )
  }

  def sharedNoReassocResult(r: Rexp, input: String): SharedResult =
    sharedModeResult("no-reassoc", r, input)

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

  def decodeAValue(r: ARexp, bits: List[Bit]): Option[Val] = {
    def stripPrefix(prefix: List[Bit], bs: List[Bit]): Option[List[Bit]] =
      if (bs.startsWith(prefix)) Some(bs.drop(prefix.length)) else None

    def altValueAt(index: Int, total: Int, v: Val): Val =
      if (total <= 1) v
      else if (index == 0) LeftVal(v)
      else RightVal(altValueAt(index - 1, total - 1, v))

    def dec(re: ARexp, bs: List[Bit]): List[(Val, List[Bit])] = re match {
      case AZERO => Nil
      case AONE(prefix) => stripPrefix(prefix, bs).toList.map(rest => (Void, rest))
      case ACHAR(prefix, c) => stripPrefix(prefix, bs).toList.map(rest => (CharVal(c), rest))
      case ASEQ(prefix, r1, r2) =>
        for {
          bs0 <- stripPrefix(prefix, bs).toList
          left <- dec(r1, bs0)
          (v1, rest1) = left
          right <- dec(r2, rest1)
          (v2, rest2) = right
        } yield (SeqVal(v1, v2), rest2)
      case AALTs(prefix, rs) =>
        for {
          bs0 <- stripPrefix(prefix, bs).toList
          rowWithIndex <- rs.zipWithIndex
          (row, index) = rowWithIndex
          decoded <- dec(row, bs0)
          (v, rest) = decoded
        } yield (altValueAt(index, rs.length, v), rest)
      case ASTAR(prefix, body) =>
        stripPrefix(prefix, bs).toList.flatMap {
          case S :: rest => List((StarsVal(Nil), rest))
          case Z :: rest =>
            for {
              head <- dec(body, rest)
              (v, rest1) = head
              tail <- dec(ASTAR(Nil, body), rest1)
              out <- tail match {
                case (StarsVal(vs), rest2) => List((StarsVal(v :: vs), rest2))
                case _ => Nil
              }
            } yield out
          case Nil => Nil
        }
      case ANTIMES(prefix, body, n) =>
        stripPrefix(prefix, bs).toList.flatMap {
          case S :: rest if n == 0 => List((StarsVal(Nil), rest))
          case Z :: rest if n > 0 =>
            for {
              head <- dec(body, rest)
              (v, rest1) = head
              tail <- dec(ANTIMES(Nil, body, n - 1), rest1)
              out <- tail match {
                case (StarsVal(vs), rest2) => List((StarsVal(v :: vs), rest2))
                case _ => Nil
              }
            } yield out
          case _ => Nil
        }
    }

    dec(r, bits).collectFirst { case (v, Nil) => v }
  }

  def decodeAEpsValue(r: ARexp, bits: List[Bit]): Option[Val] = {
    def stripPrefix(prefix: List[Bit], bs: List[Bit]): Option[List[Bit]] =
      if (bs.startsWith(prefix)) Some(bs.drop(prefix.length)) else None

    def altValueAt(index: Int, total: Int, v: Val): Val =
      if (total <= 1) v
      else if (index == 0) LeftVal(v)
      else RightVal(altValueAt(index - 1, total - 1, v))

    def dec(re: ARexp, bs: List[Bit]): Option[(Val, List[Bit])] =
      if (!bnullable(re)) None
      else re match {
        case AZERO => None
        case AONE(prefix) => stripPrefix(prefix, bs).map(rest => (Void, rest))
        case ACHAR(_, _) => None
        case ASEQ(prefix, r1, r2) =>
          for {
            bs0 <- stripPrefix(prefix, bs)
            left <- dec(r1, bs0)
            (v1, rest1) = left
            right <- dec(r2, rest1)
            (v2, rest2) = right
          } yield (SeqVal(v1, v2), rest2)
        case AALTs(prefix, rs) =>
          stripPrefix(prefix, bs).flatMap { bs0 =>
            rs.zipWithIndex.collectFirst(Function.unlift { case (row, index) =>
              dec(row, bs0).map { case (v, rest) => (altValueAt(index, rs.length, v), rest) }
            })
          }
        case ASTAR(prefix, _) =>
          stripPrefix(prefix, bs).flatMap {
            case S :: rest => Some((StarsVal(Nil), rest))
            case _ => None
          }
        case ANTIMES(prefix, body, n) =>
          stripPrefix(prefix, bs).flatMap {
            case S :: rest if n == 0 => Some((StarsVal(Nil), rest))
            case Z :: rest if n > 0 =>
              for {
                head <- dec(body, rest)
                (v, rest1) = head
                tail <- dec(ANTIMES(Nil, body, n - 1), rest1)
                out <- tail match {
                  case (StarsVal(vs), rest2) => Some((StarsVal(v :: vs), rest2))
                  case _ => None
                }
              } yield out
            case _ => None
          }
      }

    dec(r, bits).collect { case (v, Nil) => v }
  }

  def annotatedValue(r: ARexp, input: String): Option[Val] = {
    val finalRegex = bders(r, input)
    if (bnullable(finalRegex)) decodeAValue(r, bmkeps(finalRegex)) else None
  }

  def blexerValue(r: Rexp, input: String, derivative: (ARexp, String) => ARexp): Option[Val] = {
    val finalRegex = derivative(intern(r), input)
    if (bnullable(finalRegex)) decodeBits(r, bmkeps(finalRegex)) else None
  }

  def baselineValue(r: Rexp, input: String): Option[Val] =
    blexerValue(r, input, bders)

  def cubicValue(r: Rexp, input: String): Option[Val] =
    blexerValue(r, input, bdersSimpCubic)

  def strongValue(r: Rexp, input: String): Option[Val] =
    blexerValue(r, input, bdersStrong)

  def strongDeferredValue(r: Rexp, input: String): Option[Val] = {
    val finalRegex = bdersStrong(intern(r), input)
    if (bnullable(finalRegex)) baselineValue(r, input) else None
  }

  final case class PosixMemoResult(
      value: Option[Val],
      acceptsStates: Int,
      valueStates: Int,
      acceptsQueries: Int,
      valueQueries: Int,
      splitProbes: Int
  )

  final case class ActiveSuffixStats(
      rows: Int,
      keys: Int,
      altNodes: Int,
      payloadRoots: Int,
      payloadDagUniverseSize: Int,
      keyDagUniverseSize: Int,
      componentUnionSize: Int,
      decompBoundSize: Int,
      maxBucket: Int,
      maxRowSize: Int,
      maxRowDagSize: Int,
      maxRowShapeDagSize: Int,
      rowDagUniverseSize: Int,
      pairBudget: Long
  )

  final case class StrongDeferredMemoResult(
      value: Option[Val],
      strongTree: Int,
      strongDag: Int,
      strongShapeDag: Int,
      memo: PosixMemoResult,
      activeSuffix: ActiveSuffixStats,
      finalActiveSuffix: ActiveSuffixStats
  )

  final case class StrongCubicObservation(
      label: String,
      regex: Rexp,
      input: String,
      regexSize: Int,
      strongTree: Int,
      ratio: Double
  )

  final case class FinalActiveBudgetConfig(
      rowsFactor: Double,
      pairFactor: Double,
      memberFactor: Double,
      memberDagFactor: Double,
      memberShapeDagFactor: Double,
      rowDagUniverseFactor: Double,
      componentUnionFactor: Double,
      decompBoundFactor: Double,
      minRegexSize: Int,
      topLimit: Int
  ) {
    def hasRowsBudget: Boolean = rowsFactor > 0.0
    def hasPairBudget: Boolean = pairFactor > 0.0
    def hasMemberBudget: Boolean = memberFactor > 0.0
    def hasMemberDagBudget: Boolean = memberDagFactor > 0.0
    def hasMemberShapeDagBudget: Boolean = memberShapeDagFactor > 0.0
    def hasRowDagUniverseBudget: Boolean = rowDagUniverseFactor > 0.0
    def hasComponentUnionBudget: Boolean = componentUnionFactor > 0.0
    def hasDecompBoundBudget: Boolean = decompBoundFactor > 0.0
    def hasBudget: Boolean =
      hasRowsBudget || hasPairBudget || hasMemberBudget ||
        hasMemberDagBudget || hasMemberShapeDagBudget ||
        hasRowDagUniverseBudget || hasComponentUnionBudget ||
        hasDecompBoundBudget
    def traceTop: Boolean = topLimit > 0
  }

  object FinalActiveBudgetConfig {
    val Disabled: FinalActiveBudgetConfig =
      FinalActiveBudgetConfig(0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 5, 0)
  }

  final case class FinalActiveBudgetObservation(
      label: String,
      regex: Rexp,
      input: String,
      regexSize: Int,
      rows: Int,
      keys: Int,
      altNodes: Int,
      payloadRoots: Int,
      payloadDagUniverseSize: Int,
      keyDagUniverseSize: Int,
      componentUnionSize: Int,
      decompBoundSize: Int,
      maxBucket: Int,
      maxRowSize: Int,
      maxRowDagSize: Int,
      maxRowShapeDagSize: Int,
      rowDagUniverseSize: Int,
      pairBudget: Long,
      rowsRatio: Double,
      memberRatio: Double,
      memberDagRatio: Double,
      memberShapeDagRatio: Double,
      rowDagUniverseRatio: Double,
      componentUnionRatio: Double,
      decompBoundRatio: Double,
      pairRatio: Double
  )

  def posixMemoResult(r: Rexp, input: String): PosixMemoResult = {
    val acceptsMemo = scala.collection.mutable.Map.empty[(Rexp, Int, Int), Boolean]
    val valueMemo = scala.collection.mutable.Map.empty[(Rexp, Int, Int), Option[Val]]
    var acceptsQueries = 0
    var valueQueries = 0
    var splitProbes = 0

    def firstSplit(candidates: Iterator[Int])(p: Int => Boolean): Option[Int] = {
      while (candidates.hasNext) {
        val k = candidates.next()
        splitProbes += 1
        if (p(k)) return Some(k)
      }
      None
    }

    def accepts(re: Rexp, i: Int, j: Int): Boolean = {
      acceptsQueries += 1
      acceptsMemo.getOrElseUpdate((re, i, j), re match {
        case ZERO => false
        case ONE => i == j
        case CH(c) => i + 1 == j && input.charAt(i) == c
        case ALT(r1, r2) => accepts(r1, i, j) || accepts(r2, i, j)
        case SEQ(r1, r2) =>
          firstSplit((i to j).iterator)(k => accepts(r1, i, k) && accepts(r2, k, j)).isDefined
        case STAR(body) =>
          i == j || firstSplit(((i + 1) to j).iterator)(k => accepts(body, i, k) && accepts(STAR(body), k, j)).isDefined
        case NTIMES(body, n) =>
          if (n == 0) i == j
          else firstSplit((i to j).iterator)(k => accepts(body, i, k) && accepts(NTIMES(body, n - 1), k, j)).isDefined
      })
    }

    def emptyNTimesValue(body: Rexp, n: Int, i: Int): Option[Val] =
      if (n == 0) Some(StarsVal(Nil))
      else {
        for {
          head <- value(body, i, i)
          tail <- emptyNTimesValue(body, n - 1, i)
          out <- tail match {
            case StarsVal(vs) => Some(StarsVal(head :: vs))
            case _ => None
          }
        } yield out
      }

    def value(re: Rexp, i: Int, j: Int): Option[Val] = {
      valueQueries += 1
      valueMemo.getOrElseUpdate((re, i, j), re match {
        case ZERO => None
        case ONE => if (i == j) Some(Void) else None
        case CH(c) => if (i + 1 == j && input.charAt(i) == c) Some(CharVal(c)) else None
        case ALT(r1, r2) =>
          value(r1, i, j).map(LeftVal.apply).orElse {
            if (accepts(r1, i, j)) None else value(r2, i, j).map(RightVal.apply)
          }
        case SEQ(r1, r2) =>
          firstSplit((i to j).reverseIterator)(k => accepts(r1, i, k) && accepts(r2, k, j))
            .flatMap { k =>
              for {
                v1 <- value(r1, i, k)
                v2 <- value(r2, k, j)
              } yield SeqVal(v1, v2)
            }
        case STAR(body) =>
          if (i == j) Some(StarsVal(Nil))
          else {
            firstSplit(((i + 1) to j).reverseIterator)(k => accepts(body, i, k) && accepts(STAR(body), k, j))
              .flatMap { k =>
                for {
                  head <- value(body, i, k)
                  if flatVal(head).nonEmpty
                  tail <- value(STAR(body), k, j)
                  out <- tail match {
                    case StarsVal(vs) => Some(StarsVal(head :: vs))
                    case _ => None
                  }
                } yield out
              }
          }
        case NTIMES(body, n) =>
          if (i == j) emptyNTimesValue(body, n, i)
          else if (n == 0) None
          else {
            firstSplit(((i + 1) to j).reverseIterator)(k => accepts(body, i, k) && accepts(NTIMES(body, n - 1), k, j))
              .flatMap { k =>
                for {
                  head <- value(body, i, k)
                  if flatVal(head).nonEmpty
                  tail <- value(NTIMES(body, n - 1), k, j)
                  out <- tail match {
                    case StarsVal(vs) => Some(StarsVal(head :: vs))
                    case _ => None
                  }
                } yield out
              }
          }
      })
    }

    val out = value(r, 0, input.length).filter(v => flatVal(v) == input)
    PosixMemoResult(out, acceptsMemo.size, valueMemo.size, acceptsQueries, valueQueries, splitProbes)
  }

  def posixMemoValue(r: Rexp, input: String): Option[Val] =
    posixMemoResult(r, input).value

  def activeSuffixRowsForStrongRoots(roots: Iterable[ARexp]): Set[ARexp] = {
    val rows = scala.collection.mutable.Set.empty[ARexp]

    def visit(q: ARexp): Unit = {
      q match {
        case ASEQ(_, AALTs(_, _), _) => rows += q
        case _ => ()
      }
      q match {
        case ASEQ(_, r1, r2) =>
          visit(r1)
          visit(r2)
        case AALTs(_, rs) =>
          rs.foreach(visit)
        case ASTAR(_, body) =>
          visit(body)
        case ANTIMES(_, body, _) =>
          visit(body)
        case _ => ()
      }
    }

    roots.foreach(visit)
    rows.toSet
  }

  def activeSuffixStatsForStrongRoots(roots: Iterable[ARexp]): ActiveSuffixStats = {
    val buckets = scala.collection.mutable.Map.empty[Rexp, scala.collection.mutable.Set[Rexp]]
    val altNodes = scala.collection.mutable.Set.empty[Rexp]
    val altDagUniverse = scala.collection.mutable.Set.empty[Rexp]
    val payloadRoots = scala.collection.mutable.Set.empty[Rexp]
    val payloadDagUniverse = scala.collection.mutable.Set.empty[Rexp]
    val keyDagUniverse = scala.collection.mutable.Set.empty[Rexp]

    activeSuffixRowsForStrongRoots(roots).foreach {
      case q @ ASEQ(_, alts @ AALTs(_, payloads), k) =>
        val key = eraseA(k)
        val row = eraseA(q)
        val bucket = buckets.getOrElseUpdate(key, scala.collection.mutable.Set.empty[Rexp])
        bucket += row
        val altRoot = eraseA(alts)
        altNodes += altRoot
        altDagUniverse ++= rsubterms(altRoot)
        payloads.foreach { p =>
          val payloadRoot = eraseA(p)
          payloadRoots += payloadRoot
          payloadDagUniverse ++= rsubterms(payloadRoot)
        }
        keyDagUniverse ++= rsubterms(key)
      case _ =>
    }

    val rows = buckets.valuesIterator.map(_.size).sum
    val keys = buckets.size
    val maxBucket = if (buckets.isEmpty) 0 else buckets.valuesIterator.map(_.size).max
    val bucketRows = buckets.valuesIterator.flatMap(_.iterator).toVector
    val maxRowSize =
      if (bucketRows.isEmpty) 0 else bucketRows.map(rsize).max
    val maxRowDagSize =
      if (bucketRows.isEmpty) 0 else bucketRows.map(rdagSize).max
    val maxRowShapeDagSize =
      if (bucketRows.isEmpty) 0 else bucketRows.map(rshapeDagSize).max
    val rowDagUniverseSize =
      bucketRows.iterator.flatMap(rsubterms).toSet.size
    val componentUnionSize =
      (bucketRows.toSet ++ altDagUniverse.toSet ++
        payloadDagUniverse.toSet ++ keyDagUniverse.toSet).size
    if (componentUnionSize != rowDagUniverseSize) {
      sys.error(
        s"internal final-active metric mismatch: componentUnion=$componentUnionSize " +
          s"rowDagUniverse=$rowDagUniverseSize")
    }
    val decompBoundSize =
      rows + altNodes.size + payloadDagUniverse.size + keyDagUniverse.size
    val pairBudget = buckets.valuesIterator.map { bucket =>
      val n = bucket.size.toLong
      n * n
    }.sum
    ActiveSuffixStats(
      rows,
      keys,
      altNodes.size,
      payloadRoots.size,
      payloadDagUniverse.size,
      keyDagUniverse.size,
      componentUnionSize,
      decompBoundSize,
      maxBucket,
      maxRowSize,
      maxRowDagSize,
      maxRowShapeDagSize,
      rowDagUniverseSize,
      pairBudget
    )
  }

  def activeSuffixStatsForStrongPrefixes(r: Rexp, input: String): ActiveSuffixStats = {
    val roots = scala.collection.mutable.ListBuffer.empty[ARexp]
    var root = intern(r)
    roots += root
    input.foreach { c =>
      root = bsimpStrong(bder(c, root))
      roots += root
    }
    activeSuffixStatsForStrongRoots(roots)
  }

  def activeSuffixStatsForStrongFinal(r: Rexp, input: String): ActiveSuffixStats = {
    val finalRegex = bdersStrong(intern(r), input)
    activeSuffixStatsForStrongRoots(List(finalRegex))
  }

  def strongDeferredMemoResult(r: Rexp, input: String): StrongDeferredMemoResult = {
    val finalRegex = bdersStrong(intern(r), input)
    val memo =
      if (bnullable(finalRegex)) posixMemoResult(r, input)
      else PosixMemoResult(None, 0, 0, 0, 0, 0)
    val activeSuffix = activeSuffixStatsForStrongPrefixes(r, input)
    val finalActiveSuffix = activeSuffixStatsForStrongRoots(List(finalRegex))
    StrongDeferredMemoResult(
      memo.value,
      asize(finalRegex),
      adagSize(finalRegex),
      ashapeDagSize(finalRegex),
      memo,
      activeSuffix,
      finalActiveSuffix
    )
  }

  def strongDeferredMemoValue(r: Rexp, input: String): Option[Val] = {
    strongDeferredMemoResult(r, input).value
  }

  def checkStrongMemoRecognitionGate(
      r: Rexp,
      input: String,
      baseline: Option[Val],
      label: String
  ): Unit = {
    val finalRegex = bdersStrong(intern(r), input)
    val strongAccepts = bnullable(finalRegex)
    val baselineAccepts = baseline.isDefined
    if (strongAccepts != baselineAccepts) {
      throw new AssertionError(
        s"""strong memo-deferred recognition gate mismatch
           |label            = $label
           |regex            = $r
           |input            = $input
           |baselineAccepts  = $baselineAccepts
           |strongAccepts    = $strongAccepts
           |baselineValue    = $baseline
           |strongTree       = ${asize(finalRegex)}
           |strongDag        = ${adagSize(finalRegex)}
           |strongShapeDag   = ${ashapeDagSize(finalRegex)}
           |finalStrong      = $finalRegex
           |""".stripMargin
      )
    }
  }

  def memoSpanBound(r: Rexp, inputLength: Int): Long =
    rsize(r).toLong * (inputLength.toLong + 1L) * (inputLength.toLong + 1L)

  def memoSplitProbeBound(r: Rexp, inputLength: Int): Long =
    memoSpanBound(r, inputLength) * (inputLength.toLong + 1L)

  def checkMemoUniverseBound(r: Rexp, input: String, result: StrongDeferredMemoResult, label: String): Unit = {
    val spanBound = memoSpanBound(r, input.length)
    val splitBound = memoSplitProbeBound(r, input.length)
    val memo = result.memo
    if (memo.acceptsStates > spanBound || memo.valueStates > spanBound || memo.splitProbes > splitBound) {
      throw new AssertionError(
        s"""strong memo-deferred universe bound failed
           |label         = $label
           |regex         = $r
           |input         = $input
           |rsize         = ${rsize(r)}
           |spanBound     = $spanBound
           |splitBound    = $splitBound
           |acceptsStates = ${memo.acceptsStates}
           |valueStates   = ${memo.valueStates}
           |splitProbes   = ${memo.splitProbes}
           |strongTree    = ${result.strongTree}
           |strongDag     = ${result.strongDag}
           |""".stripMargin
      )
    }
  }

  def strongCubicTreeBound(r: Rexp, factor: Double): Long =
    if (factor > 0.0) {
      val n = rsize(r).toDouble
      math.ceil(factor * n * n * n).toLong
    } else {
      0L
    }

  def strongCubicObservation(r: Rexp, input: String, result: StrongDeferredMemoResult, label: String): StrongCubicObservation = {
    val n = rsize(r)
    val denom = math.max(1.0, n.toDouble * n.toDouble * n.toDouble)
    StrongCubicObservation(label, r, input, n, result.strongTree, result.strongTree.toDouble / denom)
  }

  def finalActiveRowsBound(r: Rexp, factor: Double): Long =
    if (factor > 0.0) math.ceil(factor * rsize(r).toDouble).toLong else 0L

  def finalActivePairBound(r: Rexp, factor: Double): Long =
    if (factor > 0.0) {
      val n = rsize(r).toDouble
      math.ceil(factor * n * n).toLong
    } else {
      0L
    }

  def finalActiveMemberBound(r: Rexp, factor: Double): Long =
    if (factor > 0.0) math.ceil(factor * rsize(r).toDouble).toLong else 0L

  def finalActiveBudgetObservation(
      r: Rexp,
      input: String,
      result: StrongDeferredMemoResult,
      label: String
  ): FinalActiveBudgetObservation = {
    val n = rsize(r)
    val rowDenom = math.max(1.0, n.toDouble)
    val pairDenom = math.max(1.0, n.toDouble * n.toDouble)
    val stats = result.finalActiveSuffix
    FinalActiveBudgetObservation(
      label,
      r,
      input,
      n,
      stats.rows,
      stats.keys,
      stats.altNodes,
      stats.payloadRoots,
      stats.payloadDagUniverseSize,
      stats.keyDagUniverseSize,
      stats.componentUnionSize,
      stats.decompBoundSize,
      stats.maxBucket,
      stats.maxRowSize,
      stats.maxRowDagSize,
      stats.maxRowShapeDagSize,
      stats.rowDagUniverseSize,
      stats.pairBudget,
      stats.rows.toDouble / rowDenom,
      stats.maxRowSize.toDouble / rowDenom,
      stats.maxRowDagSize.toDouble / rowDenom,
      stats.maxRowShapeDagSize.toDouble / rowDenom,
      stats.rowDagUniverseSize.toDouble / rowDenom,
      stats.componentUnionSize.toDouble / rowDenom,
      stats.decompBoundSize.toDouble / rowDenom,
      stats.pairBudget.toDouble / pairDenom
    )
  }

  def finalActiveBudgetFailures(
      r: Rexp,
      result: StrongDeferredMemoResult,
      config: FinalActiveBudgetConfig
  ): List[String] = {
    if (rsize(r) < config.minRegexSize) Nil
    else {
      val rowsBound = finalActiveRowsBound(r, config.rowsFactor)
      val pairBound = finalActivePairBound(r, config.pairFactor)
      val memberBound = finalActiveMemberBound(r, config.memberFactor)
      val memberDagBound = finalActiveMemberBound(r, config.memberDagFactor)
      val memberShapeDagBound = finalActiveMemberBound(r, config.memberShapeDagFactor)
      val rowDagUniverseBound = finalActiveMemberBound(r, config.rowDagUniverseFactor)
      val componentUnionBound = finalActiveMemberBound(r, config.componentUnionFactor)
      val decompBound = finalActiveMemberBound(r, config.decompBoundFactor)
      val rowsFailure =
        if (rowsBound > 0L && result.finalActiveSuffix.rows.toLong > rowsBound) {
          List(s"finalActiveRows=${result.finalActiveSuffix.rows} > $rowsBound")
        } else Nil
      val pairFailure =
        if (pairBound > 0L && result.finalActiveSuffix.pairBudget > pairBound) {
          List(s"finalActivePairBudget=${result.finalActiveSuffix.pairBudget} > $pairBound")
        } else Nil
      val memberFailure =
        if (memberBound > 0L && result.finalActiveSuffix.maxRowSize.toLong > memberBound) {
          List(s"finalActiveMaxRowSize=${result.finalActiveSuffix.maxRowSize} > $memberBound")
        } else Nil
      val memberDagFailure =
        if (memberDagBound > 0L && result.finalActiveSuffix.maxRowDagSize.toLong > memberDagBound) {
          List(s"finalActiveMaxRowDag=${result.finalActiveSuffix.maxRowDagSize} > $memberDagBound")
        } else Nil
      val memberShapeDagFailure =
        if (memberShapeDagBound > 0L &&
            result.finalActiveSuffix.maxRowShapeDagSize.toLong > memberShapeDagBound) {
          List(s"finalActiveMaxRowShapeDag=${result.finalActiveSuffix.maxRowShapeDagSize} > $memberShapeDagBound")
        } else Nil
      val rowDagUniverseFailure =
        if (rowDagUniverseBound > 0L &&
            result.finalActiveSuffix.rowDagUniverseSize.toLong > rowDagUniverseBound) {
          List(s"finalActiveRowDagUniverse=${result.finalActiveSuffix.rowDagUniverseSize} > $rowDagUniverseBound")
        } else Nil
      val componentUnionFailure =
        if (componentUnionBound > 0L &&
            result.finalActiveSuffix.componentUnionSize.toLong > componentUnionBound) {
          List(s"finalActiveComponentUnion=${result.finalActiveSuffix.componentUnionSize} > $componentUnionBound")
        } else Nil
      val decompFailure =
        if (decompBound > 0L &&
            result.finalActiveSuffix.decompBoundSize.toLong > decompBound) {
          List(s"finalActiveDecompBound=${result.finalActiveSuffix.decompBoundSize} > $decompBound")
        } else Nil
      rowsFailure ::: pairFailure ::: memberFailure ::: memberDagFailure :::
        memberShapeDagFailure ::: rowDagUniverseFailure :::
        componentUnionFailure ::: decompFailure
    }
  }

  def checkFinalActiveBudget(
      r: Rexp,
      input: String,
      result: StrongDeferredMemoResult,
      label: String,
      config: FinalActiveBudgetConfig
  ): Unit = {
      val failures = finalActiveBudgetFailures(r, result, config)
    if (failures.nonEmpty) {
      val rowsBound = finalActiveRowsBound(r, config.rowsFactor)
      val pairBound = finalActivePairBound(r, config.pairFactor)
      val memberBound = finalActiveMemberBound(r, config.memberFactor)
      val memberDagBound = finalActiveMemberBound(r, config.memberDagFactor)
      val memberShapeDagBound = finalActiveMemberBound(r, config.memberShapeDagFactor)
      val rowDagUniverseBound = finalActiveMemberBound(r, config.rowDagUniverseFactor)
      val componentUnionBound = finalActiveMemberBound(r, config.componentUnionFactor)
      val decompBound = finalActiveMemberBound(r, config.decompBoundFactor)
      throw new AssertionError(
        s"""strong memo final-active budget failed
           |label                 = $label
           |regex                 = $r
           |input                 = $input
           |rsize                 = ${rsize(r)}
           |minRsize              = ${config.minRegexSize}
           |rowsFactor            = ${config.rowsFactor}
           |pairFactor            = ${config.pairFactor}
           |memberFactor          = ${config.memberFactor}
           |memberDagFactor       = ${config.memberDagFactor}
           |memberShapeDagFactor  = ${config.memberShapeDagFactor}
           |rowDagUniverseFactor  = ${config.rowDagUniverseFactor}
           |componentUnionFactor  = ${config.componentUnionFactor}
           |decompBoundFactor     = ${config.decompBoundFactor}
           |rowsBound             = $rowsBound
           |pairBound             = $pairBound
           |memberBound           = $memberBound
           |memberDagBound        = $memberDagBound
           |memberShapeDagBound   = $memberShapeDagBound
           |rowDagUniverseBound   = $rowDagUniverseBound
           |componentUnionBound   = $componentUnionBound
           |decompBound           = $decompBound
           |finalActiveRows       = ${result.finalActiveSuffix.rows}
           |finalActiveKeys       = ${result.finalActiveSuffix.keys}
           |finalActiveAltNodes   = ${result.finalActiveSuffix.altNodes}
           |finalActivePayloadRoots = ${result.finalActiveSuffix.payloadRoots}
           |finalActivePayloadDagUniverse = ${result.finalActiveSuffix.payloadDagUniverseSize}
           |finalActiveKeyDagUniverse = ${result.finalActiveSuffix.keyDagUniverseSize}
           |finalActiveComponentUnion = ${result.finalActiveSuffix.componentUnionSize}
           |finalActiveDecompBound = ${result.finalActiveSuffix.decompBoundSize}
           |finalActiveMaxBucket  = ${result.finalActiveSuffix.maxBucket}
           |finalActiveMaxRowSize = ${result.finalActiveSuffix.maxRowSize}
           |finalActiveMaxRowDag  = ${result.finalActiveSuffix.maxRowDagSize}
           |finalActiveMaxRowShapeDag = ${result.finalActiveSuffix.maxRowShapeDagSize}
           |finalActiveRowDagUniverse = ${result.finalActiveSuffix.rowDagUniverseSize}
           |finalActivePairBudget = ${result.finalActiveSuffix.pairBudget}
           |failures              = ${failures.mkString(", ")}
           |strongTree            = ${result.strongTree}
           |strongDag             = ${result.strongDag}
           |""".stripMargin
      )
    }
  }

  def shortLogText(text: String, max: Int = 160): String =
    if (text.length <= max) text else text.take(max) + "..."

  def shortObservationInput(input: String): String =
    shortLogText(input, 40)

  def shortObservationRegex(regex: Rexp): String =
    shortLogText(regex.toString, 220)

  def strongerCubicWorst(
      current: Option[StrongCubicObservation],
      next: StrongCubicObservation,
      minRegexSize: Int
  ): Option[StrongCubicObservation] =
    if (next.regexSize < minRegexSize) current
    else current match {
      case None => Some(next)
      case Some(old) =>
        if (next.ratio > old.ratio || (next.ratio == old.ratio && next.strongTree > old.strongTree)) Some(next)
        else current
    }

  def strongerCubicTop(
      current: Vector[StrongCubicObservation],
      next: StrongCubicObservation,
      minRegexSize: Int,
      limit: Int
  ): Vector[StrongCubicObservation] =
    if (limit <= 0 || next.regexSize < minRegexSize) current
    else {
      (current :+ next)
        .sortBy(o => (-o.ratio, -o.strongTree, -o.regexSize, o.input, o.regex.toString))
        .take(limit)
    }

  def strongerCubicObservationBetter(a: StrongCubicObservation, b: StrongCubicObservation): Boolean =
    a.ratio > b.ratio ||
      (a.ratio == b.ratio && (a.strongTree > b.strongTree ||
        (a.strongTree == b.strongTree && (a.regexSize > b.regexSize ||
          (a.regexSize == b.regexSize && (a.input < b.input ||
            (a.input == b.input && a.regex.toString < b.regex.toString)))))))

  def strongerCubicTopDistinctRegex(
      current: Vector[StrongCubicObservation],
      next: StrongCubicObservation,
      minRegexSize: Int,
      limit: Int
  ): Vector[StrongCubicObservation] =
    if (limit <= 0 || next.regexSize < minRegexSize) current
    else {
      current.find(_.regex == next.regex) match {
        case Some(old) if !strongerCubicObservationBetter(next, old) => current
        case _ =>
          (current.filterNot(_.regex == next.regex) :+ next)
            .sortBy(o => (-o.ratio, -o.strongTree, -o.regexSize, o.input, o.regex.toString))
            .take(limit)
      }
    }

  def strongCubicWorstSummary(worst: Option[StrongCubicObservation], minRegexSize: Int): String =
    worst match {
      case None => s"no strong cubic observations with rsize >= $minRegexSize"
      case Some(w) =>
        f"worst strong cubic ratio=${w.ratio}%.6f label=${w.label} tree=${w.strongTree} rsize=${w.regexSize} input=${shortObservationInput(w.input)} regex=${shortObservationRegex(w.regex)}"
    }

  def strongCubicFrontierListSummary(
      prefix: String,
      top: Vector[StrongCubicObservation],
      minRegexSize: Int
  ): String =
    if (top.isEmpty) s"no strong cubic observations with rsize >= $minRegexSize"
    else {
      top.zipWithIndex.map { case (w, i) =>
        f"#${i + 1}:ratio=${w.ratio}%.6f label=${w.label} tree=${w.strongTree} rsize=${w.regexSize} input=${shortObservationInput(w.input)} regex=${shortObservationRegex(w.regex)}"
      }.mkString(s"$prefix: ", "; ", "")
    }

  def strongCubicFrontierSummary(top: Vector[StrongCubicObservation], minRegexSize: Int): String =
    if (top.isEmpty) s"no strong cubic observations with rsize >= $minRegexSize"
    else if (top.length == 1) strongCubicWorstSummary(top.headOption, minRegexSize)
    else strongCubicFrontierListSummary("top strong cubic ratios", top, minRegexSize)

  def strongCubicFrontiersSummary(
      top: Vector[StrongCubicObservation],
      distinctRegexTop: Vector[StrongCubicObservation],
      minRegexSize: Int
  ): String =
    if (top.length <= 1) strongCubicFrontierSummary(top, minRegexSize)
    else {
      val topSummary = strongCubicFrontierListSummary("top strong cubic ratios", top, minRegexSize)
      val distinctSummary =
        strongCubicFrontierListSummary("distinct-regex strong cubic ratios", distinctRegexTop, minRegexSize)
      s"$topSummary; $distinctSummary"
    }

  def finalActiveRowsObservationBetter(
      a: FinalActiveBudgetObservation,
      b: FinalActiveBudgetObservation
  ): Boolean =
    a.rowsRatio > b.rowsRatio ||
      (a.rowsRatio == b.rowsRatio && (a.rows > b.rows ||
        (a.rows == b.rows && (a.regexSize > b.regexSize ||
          (a.regexSize == b.regexSize && (a.input < b.input ||
            (a.input == b.input && a.regex.toString < b.regex.toString)))))))

  def finalActivePairObservationBetter(
      a: FinalActiveBudgetObservation,
      b: FinalActiveBudgetObservation
  ): Boolean =
    a.pairRatio > b.pairRatio ||
      (a.pairRatio == b.pairRatio && (a.pairBudget > b.pairBudget ||
        (a.pairBudget == b.pairBudget && (a.regexSize > b.regexSize ||
          (a.regexSize == b.regexSize && (a.input < b.input ||
            (a.input == b.input && a.regex.toString < b.regex.toString)))))))

  def finalActiveMemberObservationBetter(
      a: FinalActiveBudgetObservation,
      b: FinalActiveBudgetObservation
  ): Boolean =
    a.memberRatio > b.memberRatio ||
      (a.memberRatio == b.memberRatio && (a.maxRowSize > b.maxRowSize ||
        (a.maxRowSize == b.maxRowSize && (a.regexSize > b.regexSize ||
          (a.regexSize == b.regexSize && (a.input < b.input ||
            (a.input == b.input && a.regex.toString < b.regex.toString)))))))

  def finalActiveRowDagUniverseObservationBetter(
      a: FinalActiveBudgetObservation,
      b: FinalActiveBudgetObservation
  ): Boolean =
    a.rowDagUniverseRatio > b.rowDagUniverseRatio ||
      (a.rowDagUniverseRatio == b.rowDagUniverseRatio &&
        (a.rowDagUniverseSize > b.rowDagUniverseSize ||
          (a.rowDagUniverseSize == b.rowDagUniverseSize &&
            (a.regexSize > b.regexSize ||
              (a.regexSize == b.regexSize && (a.input < b.input ||
                (a.input == b.input && a.regex.toString < b.regex.toString)))))))

  def finalActiveDecompBoundObservationBetter(
      a: FinalActiveBudgetObservation,
      b: FinalActiveBudgetObservation
  ): Boolean =
    a.decompBoundRatio > b.decompBoundRatio ||
      (a.decompBoundRatio == b.decompBoundRatio &&
        (a.decompBoundSize > b.decompBoundSize ||
          (a.decompBoundSize == b.decompBoundSize &&
            (a.regexSize > b.regexSize ||
              (a.regexSize == b.regexSize && (a.input < b.input ||
                (a.input == b.input && a.regex.toString < b.regex.toString)))))))

  def finalActiveComponentUnionObservationBetter(
      a: FinalActiveBudgetObservation,
      b: FinalActiveBudgetObservation
  ): Boolean =
    a.componentUnionRatio > b.componentUnionRatio ||
      (a.componentUnionRatio == b.componentUnionRatio &&
        (a.componentUnionSize > b.componentUnionSize ||
          (a.componentUnionSize == b.componentUnionSize &&
            (a.regexSize > b.regexSize ||
              (a.regexSize == b.regexSize && (a.input < b.input ||
                (a.input == b.input && a.regex.toString < b.regex.toString)))))))

  def finalActiveRowsTop(
      current: Vector[FinalActiveBudgetObservation],
      next: FinalActiveBudgetObservation,
      config: FinalActiveBudgetConfig
  ): Vector[FinalActiveBudgetObservation] =
    if (!config.traceTop || next.regexSize < config.minRegexSize) current
    else {
      (current :+ next)
        .sortWith(finalActiveRowsObservationBetter)
        .take(config.topLimit)
    }

  def finalActivePairTop(
      current: Vector[FinalActiveBudgetObservation],
      next: FinalActiveBudgetObservation,
      config: FinalActiveBudgetConfig
  ): Vector[FinalActiveBudgetObservation] =
    if (!config.traceTop || next.regexSize < config.minRegexSize) current
    else {
      (current :+ next)
        .sortWith(finalActivePairObservationBetter)
        .take(config.topLimit)
    }

  def finalActiveMemberTop(
      current: Vector[FinalActiveBudgetObservation],
      next: FinalActiveBudgetObservation,
      config: FinalActiveBudgetConfig
  ): Vector[FinalActiveBudgetObservation] =
    if (!config.traceTop || next.regexSize < config.minRegexSize) current
    else {
      (current :+ next)
        .sortWith(finalActiveMemberObservationBetter)
        .take(config.topLimit)
    }

  def finalActiveRowDagUniverseTop(
      current: Vector[FinalActiveBudgetObservation],
      next: FinalActiveBudgetObservation,
      config: FinalActiveBudgetConfig
  ): Vector[FinalActiveBudgetObservation] =
    if (!config.traceTop || next.regexSize < config.minRegexSize) current
    else {
      (current :+ next)
        .sortWith(finalActiveRowDagUniverseObservationBetter)
        .take(config.topLimit)
    }

  def finalActiveComponentUnionTop(
      current: Vector[FinalActiveBudgetObservation],
      next: FinalActiveBudgetObservation,
      config: FinalActiveBudgetConfig
  ): Vector[FinalActiveBudgetObservation] =
    if (!config.traceTop || next.regexSize < config.minRegexSize) current
    else {
      (current :+ next)
        .sortWith(finalActiveComponentUnionObservationBetter)
        .take(config.topLimit)
    }

  def finalActiveDecompBoundTop(
      current: Vector[FinalActiveBudgetObservation],
      next: FinalActiveBudgetObservation,
      config: FinalActiveBudgetConfig
  ): Vector[FinalActiveBudgetObservation] =
    if (!config.traceTop || next.regexSize < config.minRegexSize) current
    else {
      (current :+ next)
        .sortWith(finalActiveDecompBoundObservationBetter)
        .take(config.topLimit)
    }

  def finalActiveBudgetFrontierListSummary(
      prefix: String,
      top: Vector[FinalActiveBudgetObservation],
      metric: String,
      config: FinalActiveBudgetConfig
  ): String =
    if (top.isEmpty) s"no final-active observations with rsize >= ${config.minRegexSize}"
    else {
      top.zipWithIndex.map { case (w, i) =>
        val main = metric match {
          case "rows" => f"rowsRatio=${w.rowsRatio}%.6f rows=${w.rows}"
          case "member" =>
            f"memberRatio=${w.memberRatio}%.6f maxRowSize=${w.maxRowSize}" +
              f" maxRowDag=${w.maxRowDagSize} dagRatio=${w.memberDagRatio}%.6f" +
              f" maxRowShapeDag=${w.maxRowShapeDagSize} shapeRatio=${w.memberShapeDagRatio}%.6f"
          case "pair" => f"pairRatio=${w.pairRatio}%.6f pairBudget=${w.pairBudget}"
          case "rowDagUniverse" =>
            f"rowDagUniverseRatio=${w.rowDagUniverseRatio}%.6f rowDagUniverse=${w.rowDagUniverseSize}" +
              s" altNodes=${w.altNodes} payloadRoots=${w.payloadRoots}" +
              s" payloadDag=${w.payloadDagUniverseSize} keyDag=${w.keyDagUniverseSize}" +
              s" componentUnion=${w.componentUnionSize} decompBound=${w.decompBoundSize}"
          case "componentUnion" =>
            f"componentUnionRatio=${w.componentUnionRatio}%.6f componentUnion=${w.componentUnionSize}" +
              s" rows=${w.rows} altNodes=${w.altNodes}" +
              s" payloadDag=${w.payloadDagUniverseSize} keyDag=${w.keyDagUniverseSize}" +
              s" rowDagUniverse=${w.rowDagUniverseSize} decompBound=${w.decompBoundSize}"
          case "decompBound" =>
            f"decompBoundRatio=${w.decompBoundRatio}%.6f decompBound=${w.decompBoundSize}" +
              s" rows=${w.rows} altNodes=${w.altNodes}" +
              s" payloadDag=${w.payloadDagUniverseSize} keyDag=${w.keyDagUniverseSize}"
          case other => s"$other=unknown"
        }
        s"#${i + 1}:$main label=${w.label} rsize=${w.regexSize} input=${shortObservationInput(w.input)} regex=${shortObservationRegex(w.regex)}"
      }.mkString(s"$prefix: ", "; ", "")
    }

  def finalActiveBudgetFrontiersSummary(
      rowsTop: Vector[FinalActiveBudgetObservation],
      pairTop: Vector[FinalActiveBudgetObservation],
      memberTop: Vector[FinalActiveBudgetObservation],
      rowDagUniverseTop: Vector[FinalActiveBudgetObservation],
      componentUnionTop: Vector[FinalActiveBudgetObservation],
      decompBoundTop: Vector[FinalActiveBudgetObservation],
      config: FinalActiveBudgetConfig
  ): String =
    if (!config.traceTop && !config.hasBudget) ""
    else {
      val rowsSummary = finalActiveBudgetFrontierListSummary("top final-active row ratios", rowsTop, "rows", config)
      val memberSummary = finalActiveBudgetFrontierListSummary("top final-active member ratios", memberTop, "member", config)
      val rowDagUniverseSummary =
        finalActiveBudgetFrontierListSummary("top final-active row-DAG universe ratios", rowDagUniverseTop, "rowDagUniverse", config)
      val componentUnionSummary =
        finalActiveBudgetFrontierListSummary("top final-active component-union ratios", componentUnionTop, "componentUnion", config)
      val decompBoundSummary =
        finalActiveBudgetFrontierListSummary("top final-active decomp-bound ratios", decompBoundTop, "decompBound", config)
      val pairSummary = finalActiveBudgetFrontierListSummary("top final-active pair ratios", pairTop, "pair", config)
      s"finalActiveBudget(rowsFactor=${config.rowsFactor}, pairFactor=${config.pairFactor}, " +
        s"memberFactor=${config.memberFactor}, memberDagFactor=${config.memberDagFactor}, " +
        s"memberShapeDagFactor=${config.memberShapeDagFactor}, " +
        s"rowDagUniverseFactor=${config.rowDagUniverseFactor}, " +
        s"componentUnionFactor=${config.componentUnionFactor}, " +
        s"decompBoundFactor=${config.decompBoundFactor}, " +
        s"minRegexSize=${config.minRegexSize}, top=${config.topLimit}); " +
        s"$rowsSummary; $memberSummary; $rowDagUniverseSummary; $componentUnionSummary; $decompBoundSummary; $pairSummary"
    }

  def sharedStatePoolCubicBound(r: Rexp, factor: Double): Long =
    if (factor > 0.0) {
      val n = rsize(r).toDouble
      math.ceil(factor * n * n * n).toLong
    } else {
      0L
    }

  def sharedStatePoolObservation(
      r: Rexp,
      input: String,
      result: SharedResult,
      label: String
  ): SharedStatePoolObservation = {
    val n = rsize(r)
    val denom = math.max(1.0, n.toDouble * n.toDouble * n.toDouble)
    SharedStatePoolObservation(label, r, input, n, result.statePoolSize, result.statePoolSize.toDouble / denom)
  }

  def sharedStatePoolObservationBetter(
      a: SharedStatePoolObservation,
      b: SharedStatePoolObservation
  ): Boolean =
    a.ratio > b.ratio ||
      (a.ratio == b.ratio && (a.statePoolSize > b.statePoolSize ||
        (a.statePoolSize == b.statePoolSize && (a.regexSize > b.regexSize ||
          (a.regexSize == b.regexSize && (a.input < b.input ||
            (a.input == b.input && a.regex.toString < b.regex.toString)))))))

  def sharedStatePoolTop(
      current: Vector[SharedStatePoolObservation],
      next: SharedStatePoolObservation,
      minRegexSize: Int,
      limit: Int
  ): Vector[SharedStatePoolObservation] =
    if (limit <= 0 || next.regexSize < minRegexSize) current
    else {
      (current :+ next)
        .sortBy(o => (-o.ratio, -o.statePoolSize, -o.regexSize, o.input, o.regex.toString))
        .take(limit)
    }

  def sharedStatePoolTopDistinctRegex(
      current: Vector[SharedStatePoolObservation],
      next: SharedStatePoolObservation,
      minRegexSize: Int,
      limit: Int
  ): Vector[SharedStatePoolObservation] =
    if (limit <= 0 || next.regexSize < minRegexSize) current
    else {
      current.find(_.regex == next.regex) match {
        case Some(old) if !sharedStatePoolObservationBetter(next, old) => current
        case _ =>
          (current.filterNot(_.regex == next.regex) :+ next)
            .sortBy(o => (-o.ratio, -o.statePoolSize, -o.regexSize, o.input, o.regex.toString))
            .take(limit)
      }
    }

  def sharedStatePoolWorstSummary(
      worst: Option[SharedStatePoolObservation],
      minRegexSize: Int
  ): String =
    worst match {
      case None => s"no shared statePool observations with rsize >= $minRegexSize"
      case Some(w) =>
        f"worst shared statePool cubic ratio=${w.ratio}%.6f label=${w.label} statePool=${w.statePoolSize} rsize=${w.regexSize} input=${shortObservationInput(w.input)} regex=${shortObservationRegex(w.regex)}"
    }

  def sharedStatePoolFrontierListSummary(
      prefix: String,
      top: Vector[SharedStatePoolObservation],
      minRegexSize: Int
  ): String =
    if (top.isEmpty) s"no shared statePool observations with rsize >= $minRegexSize"
    else {
      top.zipWithIndex.map { case (w, i) =>
        f"#${i + 1}:ratio=${w.ratio}%.6f label=${w.label} statePool=${w.statePoolSize} rsize=${w.regexSize} input=${shortObservationInput(w.input)} regex=${shortObservationRegex(w.regex)}"
      }.mkString(s"$prefix: ", "; ", "")
    }

  def sharedStatePoolFrontierSummary(
      top: Vector[SharedStatePoolObservation],
      minRegexSize: Int
  ): String =
    if (top.isEmpty) s"no shared statePool observations with rsize >= $minRegexSize"
    else if (top.length == 1) sharedStatePoolWorstSummary(top.headOption, minRegexSize)
    else sharedStatePoolFrontierListSummary("top shared statePool cubic ratios", top, minRegexSize)

  def sharedStatePoolFrontiersSummary(
      top: Vector[SharedStatePoolObservation],
      distinctRegexTop: Vector[SharedStatePoolObservation],
      minRegexSize: Int
  ): String =
    if (top.length <= 1) sharedStatePoolFrontierSummary(top, minRegexSize)
    else {
      val topSummary = sharedStatePoolFrontierListSummary("top shared statePool cubic ratios", top, minRegexSize)
      val distinctSummary =
        sharedStatePoolFrontierListSummary("distinct-regex shared statePool cubic ratios", distinctRegexTop, minRegexSize)
      s"$topSummary; $distinctSummary"
    }

  def checkSharedStatePoolCubicBudget(
      r: Rexp,
      input: String,
      result: SharedResult,
      label: String,
      seqMode: String,
      minRegexSize: Int,
      factor: Double
  ): Unit = {
    val budget = sharedStatePoolCubicBound(r, factor)
    if (budget > 0L && rsize(r) >= minRegexSize && result.statePoolSize.toLong > budget) {
      throw new AssertionError(
        s"""shared statePool cubic budget failed
           |label     = $label
           |seqMode   = $seqMode
           |regex     = $r
           |input     = $input
           |rsize     = ${rsize(r)}
           |minRsize  = $minRegexSize
           |factor    = $factor
           |budget    = $budget
           |tree      = ${result.treeSize}
           |dag       = ${result.dagSize}
           |shapeDag  = ${result.shapeDagSize}
           |statePool = ${result.statePoolSize}
           |shapePool = ${result.shapeStatePoolSize}
           |altSetShapePool = ${result.altSetShapeStatePoolSize}
           |unaryModShapePool = ${result.unaryModShapeStatePoolSize}
           |unaryPruneShapePool = ${result.unaryPruneShapeStatePoolSize}
           |contPruneShapePool = ${result.contPruneShapeStatePoolSize}
           |langContPruneShapePool = ${result.langContPruneShapeStatePoolSize}
           |pool      = ${result.poolSize}
           |""".stripMargin
      )
    }
  }

  def checkStrongCubicTreeBudget(
      r: Rexp,
      input: String,
      result: StrongDeferredMemoResult,
      label: String,
      factor: Double
  ): Unit = {
    val budget = strongCubicTreeBound(r, factor)
    if (budget > 0L && result.strongTree.toLong > budget) {
      throw new AssertionError(
        s"""strong memo-deferred cubic tree budget failed
           |label      = $label
           |regex      = $r
           |input      = $input
           |rsize      = ${rsize(r)}
           |factor     = $factor
           |budget     = $budget
           |strongTree = ${result.strongTree}
           |strongDag  = ${result.strongDag}
           |""".stripMargin
      )
    }
  }

  def strongCubicBudgetExceeded(r: Rexp, input: String, factor: Double): Boolean = {
    if (factor <= 0.0) false
    else {
      val result = strongDeferredMemoResult(r, input)
      result.strongTree.toLong > strongCubicTreeBound(r, factor)
    }
  }

  def strongMemoDagLinearBound(r: Rexp, factor: Double): Long =
    if (factor > 0.0) math.ceil(factor * rsize(r).toDouble).toLong else 0L

  def strongMemoDagBudgetExceeded(r: Rexp, input: String, factor: Double): Boolean = {
    if (factor <= 0.0) false
    else {
      val result = strongDeferredMemoResult(r, input)
      result.strongDag.toLong > strongMemoDagLinearBound(r, factor)
    }
  }

  def strongCubicBudgetReport(r: Rexp, input: String, label: String, factor: Double): String = {
    val result = strongDeferredMemoResult(r, input)
    val budget = strongCubicTreeBound(r, factor)
    val obs = strongCubicObservation(r, input, result, label)
    val base = baselineValue(r, input)
    s"""strong cubic budget witness
       |label        = $label
       |regex        = $r
       |input        = $input
       |rsize        = ${obs.regexSize}
       |factor       = $factor
       |budget       = $budget
       |strongTree   = ${result.strongTree}
       |strongDag    = ${result.strongDag}
       |ratio        = ${obs.ratio}
       |base         = $base
       |memo         = ${result.value}
       |valueOK      = ${base == result.value}
       |memoStates   = ${result.memo.acceptsStates}+${result.memo.valueStates}
       |splitProbes  = ${result.memo.splitProbes}
       |""".stripMargin
  }

  def strongMemoDagBudgetReport(r: Rexp, input: String, label: String, factor: Double): String = {
    val result = strongDeferredMemoResult(r, input)
    val budget = strongMemoDagLinearBound(r, factor)
    val base = baselineValue(r, input)
    s"""strong memo DAG budget witness
       |label        = $label
       |regex        = $r
       |input        = $input
       |rsize        = ${rsize(r)}
       |factor       = $factor
       |budget       = $budget
       |strongTree   = ${result.strongTree}
       |strongDag    = ${result.strongDag}
       |strongShape  = ${result.strongShapeDag}
       |dagRatio     = ${result.strongDag.toDouble / math.max(1.0, rsize(r).toDouble)}
       |finalRows    = ${result.finalActiveSuffix.rows}
       |finalAltNodes = ${result.finalActiveSuffix.altNodes}
       |finalPayloadRoots = ${result.finalActiveSuffix.payloadRoots}
       |finalPayloadDag = ${result.finalActiveSuffix.payloadDagUniverseSize}
       |finalKeyDag = ${result.finalActiveSuffix.keyDagUniverseSize}
       |finalComponentUnion = ${result.finalActiveSuffix.componentUnionSize}
       |finalDecompBound = ${result.finalActiveSuffix.decompBoundSize}
       |finalMaxRowDag = ${result.finalActiveSuffix.maxRowDagSize}
       |finalRowDagUniverse = ${result.finalActiveSuffix.rowDagUniverseSize}
       |base         = $base
       |memo         = ${result.value}
       |valueOK      = ${base == result.value}
       |memoStates   = ${result.memo.acceptsStates}+${result.memo.valueStates}
       |splitProbes  = ${result.memo.splitProbes}
       |""".stripMargin
  }

  def finalActiveBudgetExceeded(r: Rexp, input: String, config: FinalActiveBudgetConfig): Boolean = {
    if (!config.hasBudget || rsize(r) < config.minRegexSize) false
    else {
      val result = strongDeferredMemoResult(r, input)
      finalActiveBudgetFailures(r, result, config).nonEmpty
    }
  }

  def finalActiveBudgetReport(
      r: Rexp,
      input: String,
      label: String,
      config: FinalActiveBudgetConfig
  ): String = {
    val result = strongDeferredMemoResult(r, input)
    val rowsBound = finalActiveRowsBound(r, config.rowsFactor)
    val pairBound = finalActivePairBound(r, config.pairFactor)
    val memberBound = finalActiveMemberBound(r, config.memberFactor)
    val memberDagBound = finalActiveMemberBound(r, config.memberDagFactor)
    val memberShapeDagBound = finalActiveMemberBound(r, config.memberShapeDagFactor)
    val rowDagUniverseBound = finalActiveMemberBound(r, config.rowDagUniverseFactor)
    val componentUnionBound = finalActiveMemberBound(r, config.componentUnionFactor)
    val decompBound = finalActiveMemberBound(r, config.decompBoundFactor)
    val obs = finalActiveBudgetObservation(r, input, result, label)
    val base = baselineValue(r, input)
    s"""strong memo final-active budget witness
       |label                 = $label
       |regex                 = $r
       |input                 = $input
       |rsize                 = ${obs.regexSize}
       |rowsFactor            = ${config.rowsFactor}
       |pairFactor            = ${config.pairFactor}
       |memberFactor          = ${config.memberFactor}
       |memberDagFactor       = ${config.memberDagFactor}
       |memberShapeDagFactor  = ${config.memberShapeDagFactor}
       |rowDagUniverseFactor  = ${config.rowDagUniverseFactor}
       |componentUnionFactor  = ${config.componentUnionFactor}
       |decompBoundFactor     = ${config.decompBoundFactor}
       |rowsBound             = $rowsBound
       |pairBound             = $pairBound
       |memberBound           = $memberBound
       |memberDagBound        = $memberDagBound
       |memberShapeDagBound   = $memberShapeDagBound
       |rowDagUniverseBound   = $rowDagUniverseBound
       |componentUnionBound   = $componentUnionBound
       |decompBound           = $decompBound
       |finalActiveRows       = ${obs.rows}
       |finalActiveKeys       = ${obs.keys}
       |finalActiveAltNodes   = ${obs.altNodes}
       |finalActivePayloadRoots = ${obs.payloadRoots}
       |finalActivePayloadDagUniverse = ${obs.payloadDagUniverseSize}
       |finalActiveKeyDagUniverse = ${obs.keyDagUniverseSize}
       |finalActiveComponentUnion = ${obs.componentUnionSize}
       |finalActiveDecompBound = ${obs.decompBoundSize}
       |finalActiveMaxBucket  = ${obs.maxBucket}
       |finalActiveMaxRowSize = ${obs.maxRowSize}
       |finalActiveMaxRowDag  = ${obs.maxRowDagSize}
       |finalActiveMaxRowShapeDag = ${obs.maxRowShapeDagSize}
       |finalActiveRowDagUniverse = ${obs.rowDagUniverseSize}
       |finalActivePairBudget = ${obs.pairBudget}
       |rowsRatio             = ${obs.rowsRatio}
       |memberRatio           = ${obs.memberRatio}
       |memberDagRatio        = ${obs.memberDagRatio}
       |memberShapeDagRatio   = ${obs.memberShapeDagRatio}
       |rowDagUniverseRatio   = ${obs.rowDagUniverseRatio}
       |componentUnionRatio   = ${obs.componentUnionRatio}
       |decompBoundRatio      = ${obs.decompBoundRatio}
       |pairRatio             = ${obs.pairRatio}
       |strongTree            = ${result.strongTree}
       |strongDag             = ${result.strongDag}
       |base                  = $base
       |memo                  = ${result.value}
       |valueOK               = ${base == result.value}
       |memoStates            = ${result.memo.acceptsStates}+${result.memo.valueStates}
       |splitProbes           = ${result.memo.splitProbes}
       |failures              = ${finalActiveBudgetFailures(r, result, config).mkString(", ")}
       |""".stripMargin
  }

  def strongSafeValue(r: Rexp, input: String): Option[Val] =
    blexerValue(r, input, bdersStrongSafe)

  def nullableErasedValue(r: ARexp): Option[Val] =
    if (bnullable(r)) decodeBits(eraseA(r), bmkeps(r)) else None

  def flatVal(v: Val): String = v match {
    case Void => ""
    case CharVal(c) => c.toString
    case LeftVal(w) => flatVal(w)
    case RightVal(w) => flatVal(w)
    case SeqVal(v1, v2) => flatVal(v1) + flatVal(v2)
    case StarsVal(vs) => vs.map(flatVal).mkString
  }

  def reparseRecon(before: ARexp)(v: Val): Option[Val] =
    annotatedValue(before, flatVal(v))

  def sketchNestedStarRecon(v: Val): Option[Val] = v match {
    case StarsVal(Nil) => Some(StarsVal(Nil))
    case StarsVal(vs) => Some(StarsVal(List(StarsVal(vs))))
    case _ => None
  }

  def sketchStarAbsorbRecon(v: Val): Option[Val] = v match {
    case StarsVal(vs) => Some(SeqVal(StarsVal(vs), StarsVal(Nil)))
    case _ => None
  }

  def sketchSeqReassocRecon(v: Val): Option[Val] = v match {
    case SeqVal(v1, SeqVal(v2, v3)) => Some(SeqVal(SeqVal(v1, v2), v3))
    case _ => None
  }

  def splitAltChoice(total: Int, v: Val): Option[(Int, Val)] =
    if (total <= 0) None
    else if (total == 1) Some((0, v))
    else v match {
      case LeftVal(v0) => Some((0, v0))
      case RightVal(vs) => splitAltChoice(total - 1, vs).map { case (i, w) => (i + 1, w) }
      case _ => None
    }

  def injectA(r: ARexp, c: Char, v: Val): Option[Val] = r match {
    case AZERO => None
    case AONE(_) => None
    case ACHAR(_, d) =>
      if (c == d && v == Void) Some(CharVal(d)) else None
    case AALTs(_, rs) =>
      splitAltChoice(rs.length, v).flatMap { case (index, rowValue) =>
        rs.lift(index).flatMap(row => injectA(row, c, rowValue).map(altValueAt(index, rs.length, _)))
      }
    case ASEQ(_, r1, r2) =>
      if (bnullable(r1)) {
        v match {
          case LeftVal(SeqVal(v1, v2)) =>
            injectA(r1, c, v1).map(SeqVal(_, v2))
          case RightVal(v2) =>
            for {
              eps1 <- decodeAEpsValue(r1, bmkeps(r1))
              w2 <- injectA(r2, c, v2)
            } yield SeqVal(eps1, w2)
          case _ => None
        }
      } else {
        v match {
          case SeqVal(v1, v2) => injectA(r1, c, v1).map(SeqVal(_, v2))
          case _ => None
        }
      }
    case ASTAR(_, body) =>
      v match {
        case SeqVal(v1, StarsVal(vs)) => injectA(body, c, v1).map(w => StarsVal(w :: vs))
        case _ => None
      }
    case ANTIMES(_, body, n) =>
      if (n <= 0) None
      else v match {
        case SeqVal(v1, StarsVal(vs)) => injectA(body, c, v1).map(w => StarsVal(w :: vs))
        case _ => None
      }
  }

  final case class ValueCert(regex: ARexp, recon: Val => Option[Val])
  final case class AltRowCert(regex: ARexp, originalIndex: Int, recon: Val => Option[Val])

  def traverseOption[A, B](xs: List[A])(f: A => Option[B]): Option[List[B]] =
    xs.foldRight(Option(List.empty[B])) { (x, acc) =>
      for {
        y <- f(x)
        ys <- acc
      } yield y :: ys
    }

  def mapSeqCertValue(left: ValueCert, right: ValueCert, v: Val): Option[Val] =
    v match {
      case SeqVal(v1, v2) =>
        for {
          w1 <- left.recon(v1)
          w2 <- right.recon(v2)
        } yield SeqVal(w1, w2)
      case _ => None
    }

  def certIdentity(r: ARexp): ValueCert =
    ValueCert(r, v => Some(v))

  def altValueAt(index: Int, total: Int, v: Val): Val =
    if (total <= 1) v
    else if (index == 0) LeftVal(v)
    else RightVal(altValueAt(index - 1, total - 1, v))

  def mapAltChoice(certs: List[ValueCert], v: Val): Option[Val] =
    certs match {
      case Nil => None
      case c :: Nil => c.recon(v)
      case c :: rest => v match {
        case LeftVal(v0) => c.recon(v0).map(LeftVal.apply)
        case RightVal(vs) => mapAltChoice(rest, vs).map(RightVal.apply)
        case _ => None
      }
    }

  def mapAltRowChoice(rows: List[AltRowCert], originalTotal: Int, v: Val): Option[Val] =
    rows match {
      case Nil => None
      case row :: Nil => row.recon(v).map(altValueAt(row.originalIndex, originalTotal, _))
      case row :: rest => v match {
        case LeftVal(v0) =>
          row.recon(v0).map(altValueAt(row.originalIndex, originalTotal, _))
        case RightVal(vs) => mapAltRowChoice(rest, originalTotal, vs)
        case _ => None
      }
    }

  def fltAltRowCert(row: ValueCert, originalIndex: Int): List[AltRowCert] =
    row.regex match {
      case AZERO => Nil
      case AALTs(bs, rs) =>
        rs.zipWithIndex.map { case (r, innerIndex) =>
          AltRowCert(
            fuse(bs, r),
            originalIndex,
            v => row.recon(altValueAt(innerIndex, rs.length, v))
          )
        }
      case r => List(AltRowCert(r, originalIndex, row.recon))
    }

  def distinctAltRowCerts(rows: List[AltRowCert]): List[AltRowCert] = {
    @tailrec
    def loop(todo: List[AltRowCert], seen: List[ARexp], out: List[AltRowCert]): List[AltRowCert] =
      todo match {
        case Nil => out.reverse
        case row :: rest =>
          if (seen.exists(eq1(row.regex, _))) loop(rest, seen, out)
          else loop(rest, row.regex :: seen, row :: out)
      }
    loop(rows, Nil, Nil)
  }

  def mapKeptInnerAltChoice(rows: List[(ARexp, Int)], originalTotal: Int, v: Val): Option[Val] = {
    val certRows = rows.map { case (row, originalIndex) =>
      AltRowCert(row, originalIndex, x => Some(x))
    }
    mapAltRowChoice(certRows, originalTotal, v)
  }

  def pruneAltRowCertPair(earlier: ARexp, later: AltRowCert): AltRowCert =
    (earlier, later.regex) match {
      case (ASEQ(_, AALTs(_, covered), k1), ASEQ(bs2, AALTs(rbs, rows), k2)) if eq1(k1, k2) =>
        val kept = rows.zipWithIndex.filterNot { case (row, _) => eq1Member(row, covered) }
        if (kept.length == rows.length) later
        else {
          val inner = bsimpAALTs(rbs, kept.map(_._1))
          val atom = bsimp7ASEQAtomCert(bs2, inner, k2)
          AltRowCert(
            atom.regex,
            later.originalIndex,
            v => atom.recon(v).flatMap {
              case SeqVal(innerValue, tailValue) =>
                mapKeptInnerAltChoice(kept, rows.length, innerValue)
                  .flatMap(innerOriginal => later.recon(SeqVal(innerOriginal, tailValue)))
              case _ => None
            }
          )
        }
      case (ASEQ(_, AALTs(_, covered), k1), ASEQ(_, row, k2)) if eq1(k1, k2) && eq1Member(row, covered) =>
        AltRowCert(AZERO, later.originalIndex, _ => None)
      case _ => later
    }

  def pruneAltRowCertAgainst(seen: List[AltRowCert], row: AltRowCert): AltRowCert =
    seen.foldLeft(row)((acc, earlier) => pruneAltRowCertPair(earlier.regex, acc))

  def pruneAltRowCerts(rows: List[AltRowCert]): List[AltRowCert] = {
    def loop(seen: List[AltRowCert], todo: List[AltRowCert]): List[AltRowCert] =
      todo match {
        case Nil => Nil
        case row :: rest =>
          val pruned = pruneAltRowCertAgainst(seen, row)
          pruned :: loop(pruned :: seen, rest)
      }
    loop(Nil, rows)
  }

  def bsimpAALTsCert(bs: List[Bit], rows: List[ValueCert]): ValueCert = {
    val before = AALTs(bs, rows.map(_.regex))
    val originalTotal = rows.length
    val flatRows = rows.zipWithIndex.flatMap { case (row, index) => fltAltRowCert(row, index) }
    val keptRows = distinctAltRowCerts(pruneAltRowCerts(flatRows))
    val out = bsimpAALTs(bs, keptRows.map(_.regex))
    out match {
      case AZERO => ValueCert(AZERO, _ => None)
      case _ => ValueCert(out, v => mapAltRowChoice(keptRows, originalTotal, v))
    }
  }

  def bsimp4ASEQAtomCert(bs: List[Bit], r1: ARexp, r2: ARexp): ValueCert = {
    (r1, r2) match {
      case (AZERO, _) =>
        ValueCert(AZERO, _ => None)
      case (AONE(bs2), _) =>
        ValueCert(fuse(bs ++ bs2, r2), v => Some(SeqVal(Void, v)))
      case (ASEQ(bs2, a, b), _) =>
        val inner = bsimp4ASEQAtomCert(bs, b, r2)
        val outer = bsimp4ASEQAtomCert(bs2, a, inner.regex)
        ValueCert(
          outer.regex,
          v => outer.recon(v).flatMap {
            case SeqVal(va, innerValue) =>
              inner.recon(innerValue).flatMap {
                case SeqVal(vb, vr2) => Some(SeqVal(SeqVal(va, vb), vr2))
                case _ => None
              }
            case _ => None
          }
        )
      case (ACHAR(_, _), AZERO) | (AALTs(_, _), AZERO) |
           (ASTAR(_, _), AZERO) | (ANTIMES(_, _, _), AZERO) =>
        ValueCert(AZERO, _ => None)
      case (ACHAR(_, _), AONE(_)) | (AALTs(_, _), AONE(_)) |
           (ASTAR(_, _), AONE(_)) | (ANTIMES(_, _, _), AONE(_)) =>
        ValueCert(r1, v => Some(SeqVal(v, Void)))
      case _ =>
        ValueCert(ASEQ(bs, r1, r2), v => Some(v))
    }
  }

  def bsimp7ASEQAtomCert(bs: List[Bit], r1: ARexp, r2: ARexp): ValueCert = {
    (r1, r2) match {
      case (ASTAR(_, a), ASTAR(_, b)) if eq1(a, b) =>
        ValueCert(r1, v => Some(SeqVal(v, StarsVal(Nil))))
      case (ASTAR(_, a), ASEQ(_, ASTAR(_, b), k)) if eq1(a, b) =>
        ValueCert(
          ASEQ(bs, r1, k),
          {
            case SeqVal(vStar, vk) => Some(SeqVal(vStar, SeqVal(StarsVal(Nil), vk)))
            case _ => None
          }
        )
      case _ => bsimp4ASEQAtomCert(bs, r1, r2)
    }
  }

  def bsimp7ASEQAtomPosixCoreCert(bs: List[Bit], r1: ARexp, r2: ARexp): ValueCert = {
    val before = ASEQ(bs, r1, r2)
    val after = bsimp7ASEQAtomPosixCore(bs, r1, r2)
    after match {
      case AZERO => ValueCert(AZERO, _ => None)
      case _ if after == before => ValueCert(after, v => Some(v))
      case _ => ValueCert(after, reparseRecon(before))
    }
  }

  def bsimpStrongCoreShape(r: ARexp): ARexp = r match {
    case ASEQ(bs, r1, r2) =>
      bsimp7ASEQAtomPosixCore(bs, bsimpStrongCoreShape(r1), bsimpStrongCoreShape(r2))
    case AALTs(bs, rs) =>
      val certs = rs.map(r0 => certIdentity(bsimpStrongCoreShape(r0)))
      bsimpAALTsCert(bs, certs).regex
    case ASTAR(bs, r0) =>
      bsimpStrongCoreShape(r0) match {
        case AZERO => AONE(Nil)
        case AONE(_) => AONE(Nil)
        case ASTAR(bs2, s) if !bnullable(s) => ASTAR(bs2, s)
        case s => ASTAR(bs, s)
      }
    case other => other
  }

  def bsimpStrongCoreCert(r: ARexp): ValueCert = {
    r match {
      case ASEQ(bs, r1, r2) =>
        val left = bsimpStrongCoreCert(r1)
        val right = bsimpStrongCoreCert(r2)
        val atom = bsimp7ASEQAtomPosixCoreCert(bs, left.regex, right.regex)
        ValueCert(
          atom.regex,
          v => atom.recon(v).flatMap(mapSeqCertValue(left, right, _))
        )
      case AALTs(bs, rs) =>
        bsimpAALTsCert(bs, rs.map(bsimpStrongCoreCert))
      case ASTAR(bs, body) =>
        val inner = bsimpStrongCoreCert(body)
        inner.regex match {
          case AZERO =>
            ValueCert(AONE(Nil), {
              case Void => Some(StarsVal(Nil))
              case _ => None
            })
          case AONE(_) =>
            ValueCert(AONE(Nil), {
              case Void => Some(StarsVal(Nil))
              case _ => None
            })
          case ASTAR(bs2, s) if !bnullable(s) =>
            ValueCert(
              ASTAR(bs2, s),
              {
                case StarsVal(Nil) => Some(StarsVal(Nil))
                case v @ StarsVal(_ :: _) => inner.recon(v).map(w => StarsVal(List(w)))
                case _ => None
              }
            )
          case s =>
            ValueCert(
              ASTAR(bs, s),
              {
                case StarsVal(vs) => traverseOption(vs)(inner.recon).map(StarsVal.apply)
                case _ => None
              }
            )
        }
      case other => certIdentity(other)
    }
  }

  def bsimpStrongCore(r: ARexp): ARexp =
    bsimpStrongCoreCert(r).regex

  def bdersStrongCore(r: ARexp, s: String): ARexp =
    s.foldLeft(r)((acc, c) => bsimpStrongCore(bder(c, acc)))

  def bsimpStrongFullCert(r: ARexp): ValueCert = {
    r match {
      case ASEQ(bs, r1, r2) =>
        val left = bsimpStrongFullCert(r1)
        val right = bsimpStrongFullCert(r2)
        val atom = bsimp7ASEQAtomCert(bs, left.regex, right.regex)
        ValueCert(
          atom.regex,
          v => atom.recon(v).flatMap(mapSeqCertValue(left, right, _))
        )
      case AALTs(bs, rs) =>
        bsimpAALTsCert(bs, rs.map(bsimpStrongFullCert))
      case ASTAR(bs, body) =>
        val inner = bsimpStrongFullCert(body)
        inner.regex match {
          case AZERO =>
            ValueCert(AONE(Nil), {
              case Void => Some(StarsVal(Nil))
              case _ => None
            })
          case AONE(_) =>
            ValueCert(AONE(Nil), {
              case Void => Some(StarsVal(Nil))
              case _ => None
            })
          case ASTAR(bs2, s) =>
            ValueCert(
              ASTAR(bs2, s),
              reparseRecon(ASTAR(bs, body))
            )
          case s =>
            ValueCert(
              ASTAR(bs, s),
              {
                case StarsVal(vs) => traverseOption(vs)(inner.recon).map(StarsVal.apply)
                case _ => None
              }
            )
        }
      case other => certIdentity(other)
    }
  }

  def bsimpStrongFullCertShape(r: ARexp): ARexp =
    bsimpStrongFullCert(r).regex

  def bdersStrongFullCert(r: ARexp, s: String): ARexp =
    s.foldLeft(r)((acc, c) => bsimpStrongFullCertShape(bder(c, acc)))

  final case class LoopValueCert(regex: ARexp, recon: Val => Option[Val])

  def rawInjectCertifiedValue(r: Rexp, input: String): Option[Val] = {
    val finalCert = input.foldLeft(LoopValueCert(intern(r), v => Some(v): Option[Val])) {
      case (state, c) =>
        val raw = bder(c, state.regex)
        val previousRecon = state.recon
        val previousRegex = state.regex
        LoopValueCert(
          raw,
          v => injectA(previousRegex, c, v).flatMap(previousRecon)
        )
    }
    if (bnullable(finalCert.regex)) {
      decodeAEpsValue(finalCert.regex, bmkeps(finalCert.regex)).flatMap(finalCert.recon)
    } else None
  }

  def strongCoreCertifiedValue(r: Rexp, input: String): Option[Val] = {
    val finalCert = input.foldLeft(LoopValueCert(intern(r), v => Some(v): Option[Val])) {
      case (state, c) =>
        val raw = bder(c, state.regex)
        val cert = bsimpStrongCoreCert(raw)
        val previousRecon = state.recon
        val previousRegex = state.regex
        LoopValueCert(
          cert.regex,
          v => cert.recon(v)
            .flatMap(rawValue => injectA(previousRegex, c, rawValue))
            .flatMap(previousRecon)
        )
    }
    if (bnullable(finalCert.regex)) {
      decodeAEpsValue(finalCert.regex, bmkeps(finalCert.regex)).flatMap(finalCert.recon)
    } else None
  }

  def strongFullCertifiedValue(r: Rexp, input: String): Option[Val] = {
    val finalCert = input.foldLeft(LoopValueCert(intern(r), v => Some(v): Option[Val])) {
      case (state, c) =>
        val raw = bder(c, state.regex)
        val cert = bsimpStrongFullCert(raw)
        val previousRecon = state.recon
        val previousRegex = state.regex
        LoopValueCert(
          cert.regex,
          v => cert.recon(v)
            .flatMap(rawValue => injectA(previousRegex, c, rawValue))
            .flatMap(previousRecon)
        )
    }
    if (bnullable(finalCert.regex)) {
      decodeAEpsValue(finalCert.regex, bmkeps(finalCert.regex)).flatMap(finalCert.recon)
    } else None
  }

  final case class LoopSizeSummary(finalSize: Int, finalDag: Int, maxRaw: Int, maxCore: Int)

  def strongCoreLoopSizeSummary(r: Rexp, input: String): LoopSizeSummary = {
    var current = intern(r)
    var maxRaw = asize(current)
    var maxCore = asize(current)
    input.foreach { c =>
      val raw = bder(c, current)
      val cert = bsimpStrongCoreCert(raw)
      maxRaw = math.max(maxRaw, asize(raw))
      maxCore = math.max(maxCore, asize(cert.regex))
      current = cert.regex
    }
    LoopSizeSummary(asize(current), adagSize(current), maxRaw, maxCore)
  }

  def strongFullLoopSizeSummary(r: Rexp, input: String): LoopSizeSummary = {
    var current = intern(r)
    var maxRaw = asize(current)
    var maxCore = asize(current)
    input.foreach { c =>
      val raw = bder(c, current)
      val cert = bsimpStrongFullCert(raw)
      maxRaw = math.max(maxRaw, asize(raw))
      maxCore = math.max(maxCore, asize(cert.regex))
      current = cert.regex
    }
    LoopSizeSummary(asize(current), adagSize(current), maxRaw, maxCore)
  }

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
      else for { c <- alphabet; s <- exact(n - 1) } yield c.toString + s
    (0 to maxLen).toList.flatMap(exact)
  }

  def regexesUpToDepth(maxDepth: Int, maxRegexes: Int): List[Rexp] = {
    val memo = scala.collection.mutable.Map.empty[Int, List[Rexp]]
    def go(d: Int): List[Rexp] = memo.getOrElseUpdate(d, {
      val base = List(ZERO, ONE) ++ alphabet.map(CH(_))
      if (d == 0) base
      else {
        val smaller = go(d - 1)
        val estimated = base.length.toLong + 4L * smaller.length + 2L * smaller.length * smaller.length
        if (estimated > maxRegexes) {
          throw new IllegalArgumentException(
            s"exhaustive regex generation depth=$d would create about $estimated regexes before deduplication; " +
              s"cap is $maxRegexes. Lower POSIX_SMOKE_DEPTH or raise POSIX_SMOKE_MAX_REGEXES deliberately."
          )
        }
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

  def randomRegex(rng: Random, depth: Int): Rexp = {
    def base(): Rexp = rng.nextInt(4) match {
      case 0 => ZERO
      case 1 => ONE
      case _ => CH(alphabet(rng.nextInt(alphabet.length)))
    }
    if (depth <= 0) base()
    else rng.nextInt(9) match {
      case 0 => ZERO
      case 1 => ONE
      case 2 => CH(alphabet(rng.nextInt(alphabet.length)))
      case 3 => ALT(randomRegex(rng, depth - 1), randomRegex(rng, depth - 1))
      case 4 => SEQ(randomRegex(rng, depth - 1), randomRegex(rng, depth - 1))
      case 5 => STAR(randomRegex(rng, depth - 1))
      case 6 => STAR(STAR(randomRegex(rng, depth - 1)))
      case 7 => NTIMES(randomRegex(rng, depth - 1), rng.nextInt(4))
      case _ => ALT(SEQ(randomRegex(rng, depth - 1), randomRegex(rng, depth - 1)), randomRegex(rng, depth - 1))
    }
  }

  def randomInput(rng: Random, maxLen: Int): String = {
    val n = rng.nextInt(maxLen + 1)
    (0 until n).map(_ => alphabet(rng.nextInt(alphabet.length))).mkString
  }

  final case class FailureCase(regex: Rexp, input: String, baseline: Option[Val], cubic: Option[Val])

  def checkValuePreservation(maxDepth: Int, maxInput: Int, maxRegexes: Int): Unit = {
    val regexes = regexesUpToDepth(maxDepth, maxRegexes)
    val inputs = stringsUpTo(maxInput)
    var checked = 0
    regexes.foreach { r =>
      inputs.foreach { s =>
        val b = baselineValue(r, s)
        val c = cubicValue(r, s)
        checked += 1
        if (b != c) {
          val baseFinal = bders(intern(r), s)
          val cubicFinal = bdersSimpCubic(intern(r), s)
          val msg =
            s"""POSIX value mismatch
               |regex   = $r
               |input   = $s
               |base    = $b
               |cubic   = $c
               |baseRe  = $baseFinal
               |cubicRe = $cubicFinal
               |baseEps = ${if (bnullable(baseFinal)) Some(bmkeps(baseFinal)) else None}
               |cubicEps= ${if (bnullable(cubicFinal)) Some(bmkeps(cubicFinal)) else None}
               |""".stripMargin
          throw new AssertionError(msg)
        }
      }
    }
    println(s"checked POSIX value preservation on $checked regex/input pairs (depth <= $maxDepth, input length <= $maxInput)")
  }

  def checkRandomValuePreservation(cases: Int, maxDepth: Int, maxInput: Int, seed: Long): Unit = {
    val rng = new Random(seed)
    var checked = 0
    (0 until cases).foreach { _ =>
      val r = randomRegex(rng, maxDepth)
      val s = randomInput(rng, maxInput)
      val b = baselineValue(r, s)
      val c = cubicValue(r, s)
      checked += 1
      if (b != c) {
        val baseFinal = bders(intern(r), s)
        val cubicFinal = bdersSimpCubic(intern(r), s)
        val msg =
          s"""random POSIX value mismatch
             |seed    = $seed
             |case    = $checked
             |regex   = $r
             |input   = $s
             |base    = $b
             |cubic   = $c
             |baseRe  = $baseFinal
             |cubicRe = $cubicFinal
             |baseEps = ${if (bnullable(baseFinal)) Some(bmkeps(baseFinal)) else None}
             |cubicEps= ${if (bnullable(cubicFinal)) Some(bmkeps(cubicFinal)) else None}
             |""".stripMargin
        throw new AssertionError(msg)
      }
    }
    println(s"checked random POSIX value preservation on $checked cases (depth <= $maxDepth, input length <= $maxInput, seed=$seed)")
  }

  def checkStrongValuePreservation(maxDepth: Int, maxInput: Int, maxRegexes: Int): Unit = {
    val regexes = regexesUpToDepth(maxDepth, maxRegexes)
    val inputs = stringsUpTo(maxInput)
    var checked = 0
    regexes.foreach { r =>
      inputs.foreach { s =>
        val b = baselineValue(r, s)
        val strong = strongValue(r, s)
        checked += 1
        if (b != strong) {
          val baseFinal = bders(intern(r), s)
          val strongFinal = bdersStrong(intern(r), s)
          val msg =
            s"""bsimpStrong POSIX value mismatch
               |regex    = $r
               |input    = $s
               |base     = $b
               |strong   = $strong
               |baseRe   = $baseFinal
               |strongRe = $strongFinal
               |baseEps  = ${if (bnullable(baseFinal)) Some(bmkeps(baseFinal)) else None}
               |strongEps= ${if (bnullable(strongFinal)) Some(bmkeps(strongFinal)) else None}
               |""".stripMargin
          throw new AssertionError(msg)
        }
      }
    }
    println(s"checked bsimpStrong POSIX values on $checked regex/input pairs (depth <= $maxDepth, input length <= $maxInput)")
  }

  def checkStrongRandomValuePreservation(cases: Int, maxDepth: Int, maxInput: Int, seed: Long): Unit = {
    val rng = new Random(seed)
    var checked = 0
    (0 until cases).foreach { _ =>
      val r = randomRegex(rng, maxDepth)
      val s = randomInput(rng, maxInput)
      val b = baselineValue(r, s)
      val strong = strongValue(r, s)
      checked += 1
      if (b != strong) {
        val baseFinal = bders(intern(r), s)
        val strongFinal = bdersStrong(intern(r), s)
        val msg =
          s"""bsimpStrong random POSIX value mismatch
             |seed     = $seed
             |case     = $checked
             |regex    = $r
             |input    = $s
             |base     = $b
             |strong   = $strong
             |baseRe   = $baseFinal
             |strongRe = $strongFinal
             |baseEps  = ${if (bnullable(baseFinal)) Some(bmkeps(baseFinal)) else None}
             |strongEps= ${if (bnullable(strongFinal)) Some(bmkeps(strongFinal)) else None}
             |""".stripMargin
        throw new AssertionError(msg)
      }
    }
    println(s"checked bsimpStrong random POSIX values on $checked cases (depth <= $maxDepth, input length <= $maxInput, seed=$seed)")
  }

  def checkStrongDeferredValuePreservation(maxDepth: Int, maxInput: Int, maxRegexes: Int): Unit = {
    val regexes = regexesUpToDepth(maxDepth, maxRegexes)
    val inputs = stringsUpTo(maxInput)
    var checked = 0
    regexes.foreach { r =>
      inputs.foreach { s =>
        val b = baselineValue(r, s)
        val deferred = strongDeferredValue(r, s)
        checked += 1
        if (b != deferred) {
          val strongFinal = bdersStrong(intern(r), s)
          throw new AssertionError(
            s"""strong deferred POSIX value mismatch
               |case       = $checked
               |regex      = $r
               |input      = $s
               |base       = $b
               |deferred   = $deferred
               |strongSize = ${asize(strongFinal)}
               |strongNull = ${bnullable(strongFinal)}
               |""".stripMargin
          )
        }
      }
    }
    println(s"checked strong deferred POSIX values on $checked regex/input pairs (depth <= $maxDepth, input length <= $maxInput)")
  }

  def checkStrongDeferredRandomValuePreservation(cases: Int, maxDepth: Int, maxInput: Int, seed: Long): Unit = {
    val rng = new Random(seed)
    var checked = 0
    (0 until cases).foreach { _ =>
      val r = randomRegex(rng, maxDepth)
      val s = randomInput(rng, maxInput)
      val b = baselineValue(r, s)
      val deferred = strongDeferredValue(r, s)
      checked += 1
      if (b != deferred) {
        val strongFinal = bdersStrong(intern(r), s)
        throw new AssertionError(
          s"""strong deferred random POSIX value mismatch
             |seed       = $seed
             |case       = $checked
             |regex      = $r
             |input      = $s
             |base       = $b
             |deferred   = $deferred
             |strongSize = ${asize(strongFinal)}
             |strongNull = ${bnullable(strongFinal)}
             |""".stripMargin
        )
      }
    }
    println(s"checked strong deferred POSIX values on $checked random cases (depth <= $maxDepth, input length <= $maxInput, seed=$seed)")
  }

  def checkStrongDeferredMemoValuePreservation(
      maxDepth: Int,
      maxInput: Int,
      maxRegexes: Int,
      treeCubicFactor: Double,
      minRegexSize: Int,
      topLimit: Int,
      finalActiveConfig: FinalActiveBudgetConfig = FinalActiveBudgetConfig.Disabled
  ): Unit = {
    val regexes = regexesUpToDepth(maxDepth, maxRegexes)
    val inputs = stringsUpTo(maxInput)
    var checked = 0
    var frontier = Vector.empty[StrongCubicObservation]
    var distinctFrontier = Vector.empty[StrongCubicObservation]
    var finalActiveRowsFrontier = Vector.empty[FinalActiveBudgetObservation]
    var finalActivePairFrontier = Vector.empty[FinalActiveBudgetObservation]
    var finalActiveMemberFrontier = Vector.empty[FinalActiveBudgetObservation]
    var finalActiveRowDagUniverseFrontier = Vector.empty[FinalActiveBudgetObservation]
    var finalActiveComponentUnionFrontier = Vector.empty[FinalActiveBudgetObservation]
    var finalActiveDecompBoundFrontier = Vector.empty[FinalActiveBudgetObservation]
    regexes.foreach { r =>
      inputs.foreach { s =>
        checked += 1
        val b = baselineValue(r, s)
        val result = strongDeferredMemoResult(r, s)
        val deferred = result.value
        checkStrongMemoRecognitionGate(r, s, b, s"exhaustive case $checked")
        checkMemoUniverseBound(r, s, result, s"exhaustive case $checked")
        val obs = strongCubicObservation(r, s, result, s"exhaustive case $checked")
        frontier = strongerCubicTop(frontier, obs, minRegexSize, topLimit)
        distinctFrontier = strongerCubicTopDistinctRegex(distinctFrontier, obs, minRegexSize, topLimit)
        checkStrongCubicTreeBudget(r, s, result, s"exhaustive case $checked", treeCubicFactor)
        val finalObs = finalActiveBudgetObservation(r, s, result, s"exhaustive case $checked")
        finalActiveRowsFrontier = finalActiveRowsTop(finalActiveRowsFrontier, finalObs, finalActiveConfig)
        finalActivePairFrontier = finalActivePairTop(finalActivePairFrontier, finalObs, finalActiveConfig)
        finalActiveMemberFrontier = finalActiveMemberTop(finalActiveMemberFrontier, finalObs, finalActiveConfig)
        finalActiveRowDagUniverseFrontier =
          finalActiveRowDagUniverseTop(finalActiveRowDagUniverseFrontier, finalObs, finalActiveConfig)
        finalActiveComponentUnionFrontier =
          finalActiveComponentUnionTop(finalActiveComponentUnionFrontier, finalObs, finalActiveConfig)
        finalActiveDecompBoundFrontier =
          finalActiveDecompBoundTop(finalActiveDecompBoundFrontier, finalObs, finalActiveConfig)
        checkFinalActiveBudget(r, s, result, s"exhaustive case $checked", finalActiveConfig)
        if (b != deferred) {
          val strongFinal = bdersStrong(intern(r), s)
          throw new AssertionError(
            s"""strong memo-deferred POSIX value mismatch
               |case       = $checked
               |regex      = $r
               |input      = $s
               |base       = $b
               |memo       = $deferred
               |strongSize = ${asize(strongFinal)}
               |strongNull = ${bnullable(strongFinal)}
               |""".stripMargin
          )
        }
      }
    }
    val finalActiveSummary =
      finalActiveBudgetFrontiersSummary(
        finalActiveRowsFrontier,
        finalActivePairFrontier,
        finalActiveMemberFrontier,
        finalActiveRowDagUniverseFrontier,
        finalActiveComponentUnionFrontier,
        finalActiveDecompBoundFrontier,
        finalActiveConfig
      )
    val suffix = if (finalActiveSummary.isEmpty) "" else s"; $finalActiveSummary"
    println(s"checked strong memo-deferred POSIX values and recognition gates on $checked regex/input pairs (depth <= $maxDepth, input length <= $maxInput, strongCubicFactor=$treeCubicFactor, strongCubicMinRegexSize=$minRegexSize, strongCubicTop=$topLimit); ${strongCubicFrontiersSummary(frontier, distinctFrontier, minRegexSize)}$suffix")
  }

  def checkStrongDeferredMemoRandomValuePreservation(
      cases: Int,
      maxDepth: Int,
      maxInput: Int,
      seed: Long,
      treeCubicFactor: Double,
      minRegexSize: Int,
      topLimit: Int,
      finalActiveConfig: FinalActiveBudgetConfig = FinalActiveBudgetConfig.Disabled
  ): Unit = {
    val rng = new Random(seed)
    var checked = 0
    var frontier = Vector.empty[StrongCubicObservation]
    var distinctFrontier = Vector.empty[StrongCubicObservation]
    var finalActiveRowsFrontier = Vector.empty[FinalActiveBudgetObservation]
    var finalActivePairFrontier = Vector.empty[FinalActiveBudgetObservation]
    var finalActiveMemberFrontier = Vector.empty[FinalActiveBudgetObservation]
    var finalActiveRowDagUniverseFrontier = Vector.empty[FinalActiveBudgetObservation]
    var finalActiveComponentUnionFrontier = Vector.empty[FinalActiveBudgetObservation]
    var finalActiveDecompBoundFrontier = Vector.empty[FinalActiveBudgetObservation]
    (0 until cases).foreach { _ =>
      checked += 1
      val r = randomRegex(rng, maxDepth)
      val s = randomInput(rng, maxInput)
      val b = baselineValue(r, s)
      val result = strongDeferredMemoResult(r, s)
      val deferred = result.value
      checkStrongMemoRecognitionGate(r, s, b, s"random seed=$seed case=$checked")
      checkMemoUniverseBound(r, s, result, s"random seed=$seed case=$checked")
      val obs = strongCubicObservation(r, s, result, s"random seed=$seed case=$checked")
      frontier = strongerCubicTop(frontier, obs, minRegexSize, topLimit)
      distinctFrontier = strongerCubicTopDistinctRegex(distinctFrontier, obs, minRegexSize, topLimit)
      checkStrongCubicTreeBudget(r, s, result, s"random seed=$seed case=$checked", treeCubicFactor)
      val finalObs = finalActiveBudgetObservation(r, s, result, s"random seed=$seed case=$checked")
      finalActiveRowsFrontier = finalActiveRowsTop(finalActiveRowsFrontier, finalObs, finalActiveConfig)
      finalActivePairFrontier = finalActivePairTop(finalActivePairFrontier, finalObs, finalActiveConfig)
      finalActiveMemberFrontier = finalActiveMemberTop(finalActiveMemberFrontier, finalObs, finalActiveConfig)
      finalActiveRowDagUniverseFrontier =
        finalActiveRowDagUniverseTop(finalActiveRowDagUniverseFrontier, finalObs, finalActiveConfig)
      finalActiveComponentUnionFrontier =
        finalActiveComponentUnionTop(finalActiveComponentUnionFrontier, finalObs, finalActiveConfig)
      finalActiveDecompBoundFrontier =
        finalActiveDecompBoundTop(finalActiveDecompBoundFrontier, finalObs, finalActiveConfig)
      checkFinalActiveBudget(r, s, result, s"random seed=$seed case=$checked", finalActiveConfig)
      if (b != deferred) {
        val strongFinal = bdersStrong(intern(r), s)
        throw new AssertionError(
          s"""strong memo-deferred random POSIX value mismatch
             |seed       = $seed
             |case       = $checked
             |regex      = $r
             |input      = $s
             |base       = $b
             |memo       = $deferred
             |strongSize = ${asize(strongFinal)}
             |strongNull = ${bnullable(strongFinal)}
             |""".stripMargin
        )
      }
    }
    val finalActiveSummary =
      finalActiveBudgetFrontiersSummary(
        finalActiveRowsFrontier,
        finalActivePairFrontier,
        finalActiveMemberFrontier,
        finalActiveRowDagUniverseFrontier,
        finalActiveComponentUnionFrontier,
        finalActiveDecompBoundFrontier,
        finalActiveConfig
      )
    val suffix = if (finalActiveSummary.isEmpty) "" else s"; $finalActiveSummary"
    println(s"checked strong memo-deferred POSIX values and recognition gates on $checked random cases (depth <= $maxDepth, input length <= $maxInput, seed=$seed, strongCubicFactor=$treeCubicFactor, strongCubicMinRegexSize=$minRegexSize, strongCubicTop=$topLimit); ${strongCubicFrontiersSummary(frontier, distinctFrontier, minRegexSize)}$suffix")
  }

  final case class StrongRowsBridgeStats(
      checked: Int,
      finalActiveRows: Long,
      finalActiveCovered: Long,
      maxRowList: Int,
      maxRowSubterms: Int,
      firstMiss: Option[String]
  )

  def mkSeqFromFactorIds(store: DagStore, fs: List[Int]): Int = fs match {
    case Nil => store.mk(DOne(Nil))
    case x :: Nil => x
    case x :: xs => store.mk(DSeq(Nil, x, mkSeqFromFactorIds(store, xs)))
  }

  def activeSuffixRowIdsForRoots(store: DagStore, roots: Iterable[Int]): Set[Int] = {
    val rows = scala.collection.mutable.Set.empty[Int]
    val seen = scala.collection.mutable.Set.empty[Int]

    def visit(id: Int): Unit = {
      if (seen.add(id)) {
        store.node(id) match {
          case DSeq(_, rowBlock, _) =>
            store.node(rowBlock) match {
              case DAlts(_, _) => rows += id
              case _ => ()
            }
          case _ => ()
        }
        store.node(id) match {
          case DSeq(_, r1, r2) =>
            visit(r1)
            visit(r2)
          case DAlts(_, rs) =>
            rs.foreach(visit)
          case DStar(_, body) =>
            visit(body)
          case DNTimes(_, body, _) =>
            visit(body)
          case _ => ()
        }
      }
    }

    roots.foreach(visit)
    rows.toSet
  }

  def expandedRowKeysOptionId(store: DagStore, row: Int, maxKeys: Int): Option[List[Int]] =
    store.expandedSeqKeysId(row, maxKeys).map(keys =>
      store.distinctWithIds(keys.map(key => store.bsimpStrongId(mkSeqFromFactorIds(store, key))))
    )

  def expandedRowKeysId(store: DagStore, row: Int): List[Int] =
    expandedRowKeysOptionId(store, row, 4096).getOrElse(List(store.bsimpStrongId(row)))

  def rowKeyCoveredById(store: DagStore, key: Int, coverer: Int): Boolean = {
    val cn = store.bsimpStrongId(coverer)
    store.eq1Id(key, coverer) || store.eq1Id(key, cn) ||
      expandedRowKeysId(store, coverer).exists(store.eq1Id(key, _))
  }

  def rowCoveredByRowsId(store: DagStore, row: Int, rows: List[Int]): Boolean =
    expandedRowKeysId(store, row).forall(key =>
      rows.exists(coverer => rowKeyCoveredById(store, key, coverer))
    )

  def expandedRowSubsetCoveredById(store: DagStore, r: Int, q: Int): Boolean =
    (expandedRowKeysOptionId(store, r, 8192), expandedRowKeysOptionId(store, q, 8192)) match {
      case (Some(rKeys), Some(qKeys)) =>
        rKeys.forall(rKey =>
          qKeys.exists(qKey => store.eq1Id(rKey, qKey) || store.eq1Id(rKey, store.bsimpStrongId(qKey)))
        )
      case _ => false
    }

  def activeRowSubsetCoveredById(store: DagStore, r: Int, q: Int): Boolean = {
    val topLevel = (store.node(r), store.node(q)) match {
      case (DSeq(_, rBlock, rKey), DSeq(_, qBlock, qKey)) =>
        (store.node(rBlock), store.node(qBlock)) match {
          case (DAlts(_, rRows), DAlts(_, qRows)) =>
            store.eq1Id(rKey, qKey) && rRows.forall(row => rowCoveredByRowsId(store, row, qRows))
          case _ => false
        }
      case _ => false
    }
    topLevel || expandedRowSubsetCoveredById(store, r, q)
  }

  def strongBridgeMemberId(store: DagStore, r: Int, rs: Iterable[Int]): Boolean = {
    val rn = store.bsimpStrongId(r)
    rs.exists(q =>
      store.eq1Id(r, q) || store.eq1Id(rn, q) || store.eq1Id(r, store.bsimpStrongId(q)) ||
        activeRowSubsetCoveredById(store, r, q) || activeRowSubsetCoveredById(store, rn, q)
    )
  }

  def factoredActiveRowsOneStepId(store: DagStore, rows: List[Int]): List[Int] = {
    val groups = scala.collection.mutable.ListBuffer.empty[(Int, scala.collection.mutable.ListBuffer[Int])]

    def add(suffix: Int, prefix: Int): Unit = {
      groups.indexWhere { case (k, _) => store.eq1Id(k, suffix) } match {
        case -1 =>
          groups += suffix -> scala.collection.mutable.ListBuffer(prefix)
        case i =>
          val prefixes = groups(i)._2
          if (!prefixes.exists(store.eq1Id(prefix, _))) prefixes += prefix
      }
    }

    val workRows = store.distinctWithIds(rows.flatMap(r => store.reachableIds(r).toList.sorted))
    workRows.foreach { row =>
      store.reachableIds(row).foreach(sub => add(sub, store.mk(DOne(Nil))))
      val factors = store.seqFactorsId(row)
      factors.indices.foreach { i =>
        val prefix = mkSeqFromFactorIds(store, factors.take(i))
        val suffix = mkSeqFromFactorIds(store, factors.drop(i))
        store.fltsIds(List(prefix)).foreach(add(suffix, _))
        store.node(prefix) match {
          case DAlts(_, altRows) =>
            val suffixFactors = store.seqFactorsId(suffix)
            altRows.foreach { altRow =>
              val altFactors = store.seqFactorsId(altRow)
              (1 until altFactors.length).foreach { j =>
                val branchPrefix = mkSeqFromFactorIds(store, altFactors.take(j))
                val branchSuffix = mkSeqFromFactorIds(store, altFactors.drop(j) ++ suffixFactors)
                store.fltsIds(List(branchPrefix)).foreach(add(branchSuffix, _))
              }
            }
          case _ => ()
        }
      }
    }

    groups.iterator.flatMap { case (suffix, prefixes0) =>
      val prefixes = store.distinctWithIds(prefixes0.toList)
      if (prefixes.lengthCompare(2) >= 0) {
        Some(store.mk(DSeq(Nil, store.mk(DAlts(Nil, prefixes)), suffix)))
      } else None
    }.toList
  }

  def factoredActiveRowsFromRowsId(store: DagStore, rows: List[Int]): Set[Int] = {
    val seen = scala.collection.mutable.ListBuffer.empty[Int]
    val out = scala.collection.mutable.ListBuffer.empty[Int]

    def addSeen(r: Int): Boolean =
      if (seen.exists(store.eq1Id(r, _))) false
      else {
        seen += r
        true
      }

    rows.foreach(addSeen)
    var round = 0
    var changed = true
    while (changed && round < 8 && seen.length < 512) {
      changed = false
      factoredActiveRowsOneStepId(store, seen.toList).foreach { r =>
        if (addSeen(r)) {
          out += r
          changed = true
        }
      }
      round += 1
    }
    out.toSet
  }

  def strongRootFromRowsId(store: DagStore, rows: List[Int]): Int =
    store.bsimpStrongId(store.mk(DAlts(Nil, rows)))

  def strongRowsBridgeRowsId(store: DagStore, rows: List[Int]): Set[Int] =
    rows.flatMap(r => store.reachableIds(r)).toSet ++
      store.reachableIds(strongRootFromRowsId(store, rows)) ++
      factoredActiveRowsFromRowsId(store, rows)

  def strongRowsBridgeDagCase(
      r: Rexp,
      s: String,
      label: String,
      checkValue: Boolean = true
  ): (Int, Int, Int, Int, Option[String]) = {
    val store = new DagStore(eraseBits = true)
    val root = store.fromARexp(intern(r))
    val finalStrong = store.bdersStrongId(root, s)
    val rowList = store.bpdersStrong1RowsId(root, s)
    val strongGate = store.bnullableId(finalStrong)
    val rowGate = rowList.exists(store.bnullableId)
    if (rowGate != strongGate) {
      throw new AssertionError(
        s"""DAG strong row-gate mismatch
           |label      = $label
           |regex      = $r
           |input      = $s
           |rowGate    = $rowGate
           |strongGate = $strongGate
           |rowCount   = ${rowList.length}
           |strongKey  = ${store.compactShapeKey(finalStrong)}
           |""".stripMargin
      )
    }

    if (checkValue) {
      val b = baselineValue(r, s)
      val rowMemo = if (rowGate) posixMemoValue(r, s) else None
      if (b != rowMemo) {
        throw new AssertionError(
          s"""DAG strong row-gated memo POSIX mismatch
             |label   = $label
             |regex   = $r
             |input   = $s
             |base    = $b
             |rowMemo = $rowMemo
             |rows    = ${rowList.length}
             |""".stripMargin
        )
      }
    }

    val finalActive = activeSuffixRowIdsForRoots(store, List(finalStrong))
    val bridgeRows = strongRowsBridgeRowsId(store, rowList)
    val covered = finalActive.count(q => strongBridgeMemberId(store, q, bridgeRows))
    val firstMiss = finalActive.find(q => !strongBridgeMemberId(store, q, bridgeRows)).map { q =>
      s"""DAG strong final-active row not covered by bpdersStrong1Rows subterms/factoring
         |label       = $label
         |regex       = $r
         |input       = $s
         |missingKey  = ${store.compactShapeKey(q)}
         |missingNorm = ${store.compactShapeKey(store.bsimpStrongId(q))}
         |strongKey   = ${store.compactShapeKey(finalStrong)}
         |rowCount    = ${rowList.length}
         |bridgeRows  = ${bridgeRows.size}
         |""".stripMargin
    }
    (finalActive.size, covered, bridgeRows.size, rowList.length, firstMiss)
  }

  def strongRowsBridgeCase(
      r: Rexp,
      s: String,
      label: String
  ): (Int, Int, Int, Option[String]) = {
    val finalStrong = bdersStrong(intern(r), s)
    val rowList = bpdersStrong1Rows(intern(r), s)
    val strongGate = bnullable(finalStrong)
    val rowGate = rowList.exists(bnullable)
    if (rowGate != strongGate) {
      throw new AssertionError(
        s"""strong row-gate mismatch
           |label      = $label
           |regex      = $r
           |input      = $s
           |rowGate    = $rowGate
           |strongGate = $strongGate
           |rows       = $rowList
           |strong     = $finalStrong
           |""".stripMargin
      )
    }

    val b = baselineValue(r, s)
    val rowMemo = if (rowGate) posixMemoValue(r, s) else None
    if (b != rowMemo) {
      throw new AssertionError(
        s"""strong row-gated memo POSIX mismatch
           |label   = $label
           |regex   = $r
           |input   = $s
           |base    = $b
           |rowMemo = $rowMemo
           |rows    = $rowList
           |strong  = $finalStrong
           |""".stripMargin
      )
    }

    val finalActive = activeSuffixRowsForStrongRoots(List(finalStrong))
    val rowSubterms = strongRowsBridgeRows(rowList)
    val factoredRows = factoredActiveRowsFromRows(rowList)
    val bridgeRows = rowSubterms ++ factoredRows
    val covered = finalActive.count(q => strongBridgeMember(q, bridgeRows))
    val firstMiss = finalActive.find(q => !strongBridgeMember(q, bridgeRows)).map { q =>
      s"""strong final-active row not covered by bpdersStrong1Rows subterms/factoring
         |label       = $label
         |regex       = $r
         |input       = $s
         |missing     = $q
         |missingNorm = ${bsimpStrong(q)}
         |finalStrong = $finalStrong
         |rowList     = $rowList
         |factored    = $factoredRows
         |""".stripMargin
    }
    (finalActive.size, covered, bridgeRows.size, firstMiss)
  }

  def mergeStrongRowsBridgeStats(
      acc: StrongRowsBridgeStats,
      activeRows: Int,
      coveredRows: Int,
      rowListSize: Int,
      rowSubtermSize: Int,
      miss: Option[String]
  ): StrongRowsBridgeStats =
    StrongRowsBridgeStats(
      acc.checked + 1,
      acc.finalActiveRows + activeRows,
      acc.finalActiveCovered + coveredRows,
      math.max(acc.maxRowList, rowListSize),
      math.max(acc.maxRowSubterms, rowSubtermSize),
      acc.firstMiss.orElse(miss)
    )

  def checkStrongRowsBridgeValuePreservation(
      maxDepth: Int,
      maxInput: Int,
      maxRegexes: Int,
      requireCoverage: Boolean,
      useDag: Boolean = false
  ): Unit = {
    val regexes = regexesUpToDepth(maxDepth, maxRegexes)
    val inputs = stringsUpTo(maxInput)
    var stats = StrongRowsBridgeStats(0, 0L, 0L, 0, 0, None)
    regexes.foreach { r =>
      inputs.foreach { s =>
        val (active, covered, subterms, rowCount, miss) =
          if (useDag) strongRowsBridgeDagCase(r, s, s"exhaustive DAG case ${stats.checked + 1}")
          else {
            val rowList = bpdersStrong1Rows(intern(r), s)
            val (active0, covered0, subterms0, miss0) =
              strongRowsBridgeCase(r, s, s"exhaustive case ${stats.checked + 1}")
            (active0, covered0, subterms0, rowList.length, miss0)
          }
        stats = mergeStrongRowsBridgeStats(stats, active, covered, rowCount, subterms, miss)
      }
    }
    if (requireCoverage && stats.firstMiss.isDefined) {
      throw new AssertionError(stats.firstMiss.get)
    }
    println(
      s"checked ${if (useDag) "DAG " else ""}strong row-gated memo POSIX bridge on ${stats.checked} regex/input pairs " +
      s"(depth <= $maxDepth, input length <= $maxInput); " +
      s"final-active coverage=${stats.finalActiveCovered}/${stats.finalActiveRows}, " +
      s"maxRows=${stats.maxRowList}, maxBridgeRows=${stats.maxRowSubterms}" +
      stats.firstMiss.map(m => s"; first uncovered active row:\n$m").getOrElse("")
    )
  }

  def checkStrongRowsBridgeRandomValuePreservation(
      cases: Int,
      maxDepth: Int,
      maxInput: Int,
      seed: Long,
      requireCoverage: Boolean,
      useDag: Boolean = false
  ): Unit = {
    val rng = new Random(seed)
    var stats = StrongRowsBridgeStats(0, 0L, 0L, 0, 0, None)
    (0 until cases).foreach { _ =>
      val r = randomRegex(rng, maxDepth)
      val s = randomInput(rng, maxInput)
      val (active, covered, subterms, rowCount, miss) =
        if (useDag) strongRowsBridgeDagCase(r, s, s"random DAG seed=$seed case ${stats.checked + 1}")
        else {
          val rowList = bpdersStrong1Rows(intern(r), s)
          val (active0, covered0, subterms0, miss0) =
            strongRowsBridgeCase(r, s, s"random seed=$seed case ${stats.checked + 1}")
          (active0, covered0, subterms0, rowList.length, miss0)
        }
      stats = mergeStrongRowsBridgeStats(stats, active, covered, rowCount, subterms, miss)
    }
    if (requireCoverage && stats.firstMiss.isDefined) {
      throw new AssertionError(stats.firstMiss.get)
    }
    println(
      s"checked ${if (useDag) "DAG " else ""}strong row-gated memo POSIX bridge on ${stats.checked} random cases " +
      s"(depth <= $maxDepth, input length <= $maxInput, seed=$seed); " +
      s"final-active coverage=${stats.finalActiveCovered}/${stats.finalActiveRows}, " +
      s"maxRows=${stats.maxRowList}, maxBridgeRows=${stats.maxRowSubterms}" +
      stats.firstMiss.map(m => s"; first uncovered active row:\n$m").getOrElse("")
    )
  }

  def checkStrongRowsBridgeCh7Trace(
      k: Int,
      lengths: List[Int],
      requireCoverage: Boolean,
      useDag: Boolean = false
  ): Unit = {
    val r = thesisCh7Evil(k)
    var stats = StrongRowsBridgeStats(0, 0L, 0L, 0, 0, None)
    lengths.foreach { n =>
      val s = "a" * n
      val (active, covered, bridgeRows, rowCount, miss) =
        if (useDag) strongRowsBridgeDagCase(r, s, s"Chapter 7 DAG k=$k n=$n", checkValue = false)
        else {
          val rowList = bpdersStrong1Rows(intern(r), s)
          val (active0, covered0, bridgeRows0, miss0) =
            strongRowsBridgeCase(r, s, s"Chapter 7 k=$k n=$n")
          (active0, covered0, bridgeRows0, rowList.length, miss0)
        }
      stats = mergeStrongRowsBridgeStats(stats, active, covered, rowCount, bridgeRows, miss)
    }
    if (requireCoverage && stats.firstMiss.isDefined) {
      throw new AssertionError(stats.firstMiss.get)
    }
    println(
      s"checked Chapter 7 ${if (useDag) "DAG " else ""}strong row-gated memo bridge for k=$k lengths=${lengths.mkString(",")}; " +
      s"final-active coverage=${stats.finalActiveCovered}/${stats.finalActiveRows}, " +
      s"maxRows=${stats.maxRowList}, maxBridgeRows=${stats.maxRowSubterms}" +
      stats.firstMiss.map(m => s"; first uncovered active row:\n$m").getOrElse("")
    )
  }

  def strongRowsBridgeCoverageMiss(r: Rexp, s: String, label: String): Option[String] =
    strongRowsBridgeCase(r, s, label)._4

  def strongRowsBridgeCoverageMismatch(r: Rexp, s: String): Boolean =
    strongRowsBridgeCoverageMiss(r, s, "bridge coverage predicate").isDefined

  def strongRowsBridgeCoverageReport(r: Rexp, s: String, label: String): String = {
    val finalStrong = bdersStrong(intern(r), s)
    val rowList = bpdersStrong1Rows(intern(r), s)
    val finalActive = activeSuffixRowsForStrongRoots(List(finalStrong))
    val factoredRows = factoredActiveRowsFromRows(rowList)
    val rowRoot = strongRootFromRows(rowList)
    val bridgeRows = strongRowsBridgeRows(rowList)
    val covered = finalActive.count(q => strongBridgeMember(q, bridgeRows))
    val miss = finalActive.find(q => !strongBridgeMember(q, bridgeRows))
    val factoredHit = miss.flatMap(q => factoredRows.find(p => strongBridgeMember(q, List(p))))
    val rowRootHit = miss.exists(q => strongBridgeMember(q, asubterms(rowRoot)))
    s"""$label
       |regex       = $r
       |input       = $s
       |rsize       = ${rsize(r)}
       |strongTree  = ${asize(finalStrong)}
       |strongDag   = ${adagSize(finalStrong)}
       |rowRootTree = ${asize(rowRoot)}
       |rowRootEq1  = ${eq1(finalStrong, rowRoot)}
       |rowListSize = ${rowList.length}
       |factoredRows= ${factoredRows.size}
       |bridgeRows  = ${bridgeRows.size}
       |coverage    = $covered/${finalActive.size}
       |missing     = ${miss.getOrElse("<none>")}
       |missingNorm = ${miss.map(bsimpStrong).getOrElse("<none>")}
       |factoredHit = ${factoredHit.getOrElse("<none>")}
       |rowRootHit  = $rowRootHit
       |finalStrong = $finalStrong
       |rowRoot     = $rowRoot
       |rowList     = $rowList
       |""".stripMargin
  }

  def checkStrongDeferredMemoKnownCounterexamples(
      treeCubicFactor: Double,
      minRegexSize: Int,
      topLimit: Int,
      finalActiveConfig: FinalActiveBudgetConfig = FinalActiveBudgetConfig.Disabled
  ): Unit = {
    val cases = List(
      "direct nested-star CE" -> STAR(STAR(CH('a'))) -> List("", "a", "aa", "aaa"),
      "full-cert greedy sequence CE" ->
        SEQ(STAR(ALT(STAR(CH('b')), SEQ(CH('b'), CH('a')))), STAR(CH('a'))) ->
        List("", "b", "bb", "bba", "bbba", "bbaa"),
      "nested nullable seq alt CE family" ->
        STAR(STAR(ALT(SEQ(STAR(CH('a')), ONE), CH('b')))) ->
        List("", "a", "b", "bab", "abaaabab")
    )
    var checked = 0
    var frontier = Vector.empty[StrongCubicObservation]
    var distinctFrontier = Vector.empty[StrongCubicObservation]
    var finalActiveRowsFrontier = Vector.empty[FinalActiveBudgetObservation]
    var finalActivePairFrontier = Vector.empty[FinalActiveBudgetObservation]
    var finalActiveMemberFrontier = Vector.empty[FinalActiveBudgetObservation]
    var finalActiveRowDagUniverseFrontier = Vector.empty[FinalActiveBudgetObservation]
    var finalActiveComponentUnionFrontier = Vector.empty[FinalActiveBudgetObservation]
    var finalActiveDecompBoundFrontier = Vector.empty[FinalActiveBudgetObservation]
    cases.foreach { case ((name, r), inputs) =>
      inputs.foreach { s =>
        checked += 1
        val base = baselineValue(r, s)
        val result = strongDeferredMemoResult(r, s)
        checkStrongMemoRecognitionGate(r, s, base, s"known CE $name input=$s")
        checkMemoUniverseBound(r, s, result, s"known CE $name input=$s")
        val obs = strongCubicObservation(r, s, result, s"known CE $name input=$s")
        frontier = strongerCubicTop(frontier, obs, minRegexSize, topLimit)
        distinctFrontier = strongerCubicTopDistinctRegex(distinctFrontier, obs, minRegexSize, topLimit)
        checkStrongCubicTreeBudget(r, s, result, s"known CE $name input=$s", treeCubicFactor)
        val finalObs = finalActiveBudgetObservation(r, s, result, s"known CE $name input=$s")
        finalActiveRowsFrontier = finalActiveRowsTop(finalActiveRowsFrontier, finalObs, finalActiveConfig)
        finalActivePairFrontier = finalActivePairTop(finalActivePairFrontier, finalObs, finalActiveConfig)
        finalActiveMemberFrontier = finalActiveMemberTop(finalActiveMemberFrontier, finalObs, finalActiveConfig)
        finalActiveRowDagUniverseFrontier =
          finalActiveRowDagUniverseTop(finalActiveRowDagUniverseFrontier, finalObs, finalActiveConfig)
        finalActiveComponentUnionFrontier =
          finalActiveComponentUnionTop(finalActiveComponentUnionFrontier, finalObs, finalActiveConfig)
        finalActiveDecompBoundFrontier =
          finalActiveDecompBoundTop(finalActiveDecompBoundFrontier, finalObs, finalActiveConfig)
        checkFinalActiveBudget(r, s, result, s"known CE $name input=$s", finalActiveConfig)
        if (base != result.value) {
          throw new AssertionError(
            s"""strong memo-deferred known CE mismatch: $name
               |regex      = $r
               |input      = $s
               |base       = $base
               |memo       = ${result.value}
               |strongTree = ${result.strongTree}
               |strongDag  = ${result.strongDag}
               |memoStates = ${result.memo.acceptsStates}+${result.memo.valueStates}
               |splits     = ${result.memo.splitProbes}
               |""".stripMargin
          )
        }
      }
    }
    val finalActiveSummary =
      finalActiveBudgetFrontiersSummary(
        finalActiveRowsFrontier,
        finalActivePairFrontier,
        finalActiveMemberFrontier,
        finalActiveRowDagUniverseFrontier,
        finalActiveComponentUnionFrontier,
        finalActiveDecompBoundFrontier,
        finalActiveConfig
      )
    val suffix = if (finalActiveSummary.isEmpty) "" else s"; $finalActiveSummary"
    println(s"checked strong memo-deferred known CE grid values and recognition gates on $checked cases (strongCubicFactor=$treeCubicFactor, strongCubicMinRegexSize=$minRegexSize, strongCubicTop=$topLimit); ${strongCubicFrontiersSummary(frontier, distinctFrontier, minRegexSize)}$suffix")
  }

  def checkStrongFullKnownBoundaryCounterexample(): Unit = {
    val r = SEQ(STAR(ALT(STAR(CH('b')), SEQ(CH('b'), CH('a')))), STAR(CH('a')))
    val input = "bba"
    val base = baselineValue(r, input)
    val full = strongFullCertifiedValue(r, input)
    val memo = strongDeferredMemoValue(r, input)
    val finalFull = bdersStrongFullCert(intern(r), input)
    val finalStrong = bdersStrong(intern(r), input)
    if (base.isEmpty) {
      throw new AssertionError("known greedy-boundary CE unexpectedly has no baseline POSIX value")
    }
    if (base == full) {
      throw new AssertionError(
        s"""known greedy-boundary CE no longer fails StrongFullCert
           |regex     = $r
           |input     = $input
           |base      = $base
           |full      = $full
           |fullSize  = ${asize(finalFull)}
           |""".stripMargin
      )
    }
    if (base != memo) {
      throw new AssertionError(
        s"""strong memo-deferred failed known greedy-boundary CE
           |regex     = $r
           |input     = $input
           |base      = $base
           |memo      = $memo
           |""".stripMargin
      )
    }
    if (asize(finalFull) != asize(finalStrong)) {
      throw new AssertionError(
        s"""StrongFullCert no longer preserves the strong-tree size on the known CE
           |regex      = $r
           |input      = $input
           |fullSize   = ${asize(finalFull)}
           |strongSize = ${asize(finalStrong)}
           |""".stripMargin
      )
    }
    println(
      s"checked known greedy-boundary CE: StrongFullCert fails as expected, " +
        s"StrongDeferredMemo matches baseline, tree=${asize(finalFull)}"
    )
  }

  def checkStrongSafeValuePreservation(maxDepth: Int, maxInput: Int, maxRegexes: Int): Unit = {
    val regexes = regexesUpToDepth(maxDepth, maxRegexes)
    val inputs = stringsUpTo(maxInput)
    var checked = 0
    regexes.foreach { r =>
      inputs.foreach { s =>
        val b = baselineValue(r, s)
        val strong = strongSafeValue(r, s)
        checked += 1
        if (b != strong) {
          val baseFinal = bders(intern(r), s)
          val strongFinal = bdersStrongSafe(intern(r), s)
          val msg =
            s"""bsimpStrongSafe POSIX value mismatch
               |regex      = $r
               |input      = $s
               |base       = $b
               |strongSafe = $strong
               |baseRe     = $baseFinal
               |safeRe     = $strongFinal
               |baseEps    = ${if (bnullable(baseFinal)) Some(bmkeps(baseFinal)) else None}
               |safeEps    = ${if (bnullable(strongFinal)) Some(bmkeps(strongFinal)) else None}
               |""".stripMargin
          throw new AssertionError(msg)
        }
      }
    }
    println(s"checked bsimpStrongSafe POSIX values on $checked regex/input pairs (depth <= $maxDepth, input length <= $maxInput)")
  }

  def checkStrongSafeRandomValuePreservation(cases: Int, maxDepth: Int, maxInput: Int, seed: Long): Unit = {
    val rng = new Random(seed)
    var checked = 0
    (0 until cases).foreach { _ =>
      val r = randomRegex(rng, maxDepth)
      val s = randomInput(rng, maxInput)
      val b = baselineValue(r, s)
      val strong = strongSafeValue(r, s)
      checked += 1
      if (b != strong) {
        val baseFinal = bders(intern(r), s)
        val strongFinal = bdersStrongSafe(intern(r), s)
        val msg =
          s"""bsimpStrongSafe random POSIX value mismatch
             |seed       = $seed
             |case       = $checked
             |regex      = $r
             |input      = $s
             |base       = $b
             |strongSafe = $strong
             |baseRe     = $baseFinal
             |safeRe     = $strongFinal
             |baseEps    = ${if (bnullable(baseFinal)) Some(bmkeps(baseFinal)) else None}
             |safeEps    = ${if (bnullable(strongFinal)) Some(bmkeps(strongFinal)) else None}
             |""".stripMargin
        throw new AssertionError(msg)
      }
    }
    println(s"checked bsimpStrongSafe random POSIX values on $checked cases (depth <= $maxDepth, input length <= $maxInput, seed=$seed)")
  }

  def checkSharedValuePreservation(
      seqMode: String,
      maxDepth: Int,
      maxInput: Int,
      maxRegexes: Int,
      directDag: Boolean = false,
      compareTree: Boolean = false,
      statePoolCubicFactor: Double = 0.0,
      statePoolMinRegexSize: Int = 5,
      statePoolTopLimit: Int = 1
  ): Unit = {
    val regexes = regexesUpToDepth(maxDepth, maxRegexes)
    val inputs = stringsUpTo(maxInput)
    var checked = 0
    val label = if (directDag) "direct-shared" else "shared"
    var frontier = Vector.empty[SharedStatePoolObservation]
    var distinctFrontier = Vector.empty[SharedStatePoolObservation]
    regexes.foreach { r =>
      inputs.foreach { s =>
        val b = baselineValue(r, s)
        val shared = sharedModeResult(seqMode, r, s, directDag, compareTree)
        checked += 1
        val obs = sharedStatePoolObservation(r, s, shared, s"$label $seqMode exhaustive case $checked")
        frontier = sharedStatePoolTop(frontier, obs, statePoolMinRegexSize, statePoolTopLimit)
        distinctFrontier = sharedStatePoolTopDistinctRegex(distinctFrontier, obs, statePoolMinRegexSize, statePoolTopLimit)
        checkSharedStatePoolCubicBudget(r, s, shared, obs.label, seqMode, statePoolMinRegexSize, statePoolCubicFactor)
        if (b != shared.value) {
          throw new AssertionError(
            s"""$label $seqMode POSIX value mismatch
               |regex   = $r
               |input   = $s
               |base    = $b
               |shared  = ${shared.value}
               |sizes   = tree=${shared.treeSize}, dag=${shared.dagSize}, shape=${shared.shapeDagSize}, statePool=${shared.statePoolSize}, shapeStatePool=${shared.shapeStatePoolSize}, altSetShapeStatePool=${shared.altSetShapeStatePoolSize}, unaryModShapeStatePool=${shared.unaryModShapeStatePoolSize}, unaryPruneShapeStatePool=${shared.unaryPruneShapeStatePoolSize}, contPruneShapeStatePool=${shared.contPruneShapeStatePoolSize}, langContPruneShapeStatePool=${shared.langContPruneShapeStatePoolSize}, langAtomicContPruneShapeStatePool=${shared.langAtomicContPruneShapeStatePoolSize}, pool=${shared.poolSize}
               |""".stripMargin
          )
        }
      }
    }
    println(s"checked $label $seqMode POSIX values on $checked regex/input pairs (depth <= $maxDepth, input length <= $maxInput, sharedStatePoolCubicFactor=$statePoolCubicFactor, sharedStatePoolMinRegexSize=$statePoolMinRegexSize, sharedStatePoolTop=$statePoolTopLimit); ${sharedStatePoolFrontiersSummary(frontier, distinctFrontier, statePoolMinRegexSize)}")
  }

  def checkSharedRandomValuePreservation(
      seqMode: String,
      cases: Int,
      maxDepth: Int,
      maxInput: Int,
      seed: Long,
      directDag: Boolean = false,
      compareTree: Boolean = false,
      statePoolCubicFactor: Double = 0.0,
      statePoolMinRegexSize: Int = 5,
      statePoolTopLimit: Int = 1
  ): Unit = {
    val rng = new Random(seed)
    var checked = 0
    val label = if (directDag) "direct-shared" else "shared"
    var frontier = Vector.empty[SharedStatePoolObservation]
    var distinctFrontier = Vector.empty[SharedStatePoolObservation]
    (0 until cases).foreach { _ =>
      val r = randomRegex(rng, maxDepth)
      val s = randomInput(rng, maxInput)
      val b = baselineValue(r, s)
      val shared = sharedModeResult(seqMode, r, s, directDag, compareTree)
      checked += 1
      val obs = sharedStatePoolObservation(r, s, shared, s"$label $seqMode random seed=$seed case=$checked")
      frontier = sharedStatePoolTop(frontier, obs, statePoolMinRegexSize, statePoolTopLimit)
      distinctFrontier = sharedStatePoolTopDistinctRegex(distinctFrontier, obs, statePoolMinRegexSize, statePoolTopLimit)
      checkSharedStatePoolCubicBudget(r, s, shared, obs.label, seqMode, statePoolMinRegexSize, statePoolCubicFactor)
      if (b != shared.value) {
        throw new AssertionError(
          s"""$label $seqMode random POSIX value mismatch
             |seed    = $seed
             |case    = $checked
             |regex   = $r
             |input   = $s
             |base    = $b
             |shared  = ${shared.value}
             |sizes   = tree=${shared.treeSize}, dag=${shared.dagSize}, shape=${shared.shapeDagSize}, statePool=${shared.statePoolSize}, shapeStatePool=${shared.shapeStatePoolSize}, altSetShapeStatePool=${shared.altSetShapeStatePoolSize}, unaryModShapeStatePool=${shared.unaryModShapeStatePoolSize}, unaryPruneShapeStatePool=${shared.unaryPruneShapeStatePoolSize}, contPruneShapeStatePool=${shared.contPruneShapeStatePoolSize}, langContPruneShapeStatePool=${shared.langContPruneShapeStatePoolSize}, langAtomicContPruneShapeStatePool=${shared.langAtomicContPruneShapeStatePoolSize}, pool=${shared.poolSize}
             |""".stripMargin
        )
      }
    }
    println(s"checked $label $seqMode random POSIX values on $checked cases (depth <= $maxDepth, input length <= $maxInput, seed=$seed, sharedStatePoolCubicFactor=$statePoolCubicFactor, sharedStatePoolMinRegexSize=$statePoolMinRegexSize, sharedStatePoolTop=$statePoolTopLimit); ${sharedStatePoolFrontiersSummary(frontier, distinctFrontier, statePoolMinRegexSize)}")
  }

  def checkSharedEvilFamilyTrace(
      seqMode: String,
      k: Int,
      lengths: List[Int],
      dagThreshold: Int,
      shapeThreshold: Int,
      directDag: Boolean = false,
      compareTree: Boolean = false,
      statePoolCubicFactor: Double = 0.0,
      statePoolMinRegexSize: Int = 5,
      statePoolTopLimit: Int = 1
  ): Unit = {
    val r = thesisCh7Evil(k)
    val label = if (directDag) "direct-shared" else "shared"
    val trace = lengths.map { n =>
      val out = sharedModeResult(seqMode, r, "a" * n, directDag, compareTree)
      n -> out
    }
    println(s"Chapter 7 k=$k $label $seqMode trace: " +
      trace.map { case (n, out) =>
        s"$n->tree=${out.treeSize}/dag=${out.dagSize}/shape=${out.shapeDagSize}/statePool=${out.statePoolSize}/shapeStatePool=${out.shapeStatePoolSize}/altSetShapeStatePool=${out.altSetShapeStatePoolSize}/unaryModShapeStatePool=${out.unaryModShapeStatePoolSize}/unaryPruneShapeStatePool=${out.unaryPruneShapeStatePoolSize}/contPruneShapeStatePool=${out.contPruneShapeStatePoolSize}/langContPruneShapeStatePool=${out.langContPruneShapeStatePoolSize}/langAtomicContPruneShapeStatePool=${out.langAtomicContPruneShapeStatePoolSize}/pool=${out.poolSize}"
      }.mkString(", "))
    trace.foreach { case (n, out) =>
      if (dagThreshold > 0 && out.dagSize >= dagThreshold) {
        throw new AssertionError(s"$label $seqMode DAG threshold failed at n=$n: dag=${out.dagSize} threshold=$dagThreshold")
      }
      if (shapeThreshold > 0 && out.shapeDagSize >= shapeThreshold) {
        throw new AssertionError(s"$label $seqMode shape-DAG threshold failed at n=$n: shape=${out.shapeDagSize} threshold=$shapeThreshold")
      }
      val input = "a" * n
      val obs = sharedStatePoolObservation(r, input, out, s"Chapter 7 k=$k n=$n")
      checkSharedStatePoolCubicBudget(r, input, out, obs.label, seqMode, statePoolMinRegexSize, statePoolCubicFactor)
    }
    val frontier = trace.foldLeft(Vector.empty[SharedStatePoolObservation]) { case (acc, (n, out)) =>
      sharedStatePoolTop(acc, sharedStatePoolObservation(r, "a" * n, out, s"Chapter 7 k=$k n=$n"), statePoolMinRegexSize, statePoolTopLimit)
    }
    val distinctFrontier = trace.foldLeft(Vector.empty[SharedStatePoolObservation]) { case (acc, (n, out)) =>
      sharedStatePoolTopDistinctRegex(acc, sharedStatePoolObservation(r, "a" * n, out, s"Chapter 7 k=$k n=$n"), statePoolMinRegexSize, statePoolTopLimit)
    }
    println(s"Chapter 7 k=$k $label $seqMode shared statePool cubic frontier (factor=$statePoolCubicFactor, minRegexSize=$statePoolMinRegexSize, top=$statePoolTopLimit): ${sharedStatePoolFrontiersSummary(frontier, distinctFrontier, statePoolMinRegexSize)}")
  }

  def sharedResultMetric(metric: String, out: SharedResult): Int =
    metric match {
      case "tree" => out.treeSize
      case "dag" => out.dagSize
      case "shape" | "shapeDag" => out.shapeDagSize
      case "statePool" => out.statePoolSize
      case "shapeStatePool" | "shapePool" => out.shapeStatePoolSize
      case "altSetShapeStatePool" | "altSetShapePool" => out.altSetShapeStatePoolSize
      case "unaryModShapeStatePool" | "unaryModShapePool" => out.unaryModShapeStatePoolSize
      case "unaryPruneShapeStatePool" | "unaryPruneShapePool" => out.unaryPruneShapeStatePoolSize
      case "contPruneShapeStatePool" | "contPruneShapePool" => out.contPruneShapeStatePoolSize
      case "langContPruneShapeStatePool" | "langContPruneShapePool" => out.langContPruneShapeStatePoolSize
      case "langAtomicContPruneShapeStatePool" | "langAtomicContPruneShapePool" =>
        out.langAtomicContPruneShapeStatePoolSize
      case "pool" => out.poolSize
      case other =>
        throw new IllegalArgumentException(
          s"unknown POSIX_SMOKE_SHARED_PLATEAU_METRIC=$other; expected tree, dag, shape, shapeDag, statePool, shapeStatePool, shapePool, altSetShapeStatePool, altSetShapePool, unaryModShapeStatePool, unaryModShapePool, unaryPruneShapeStatePool, unaryPruneShapePool, contPruneShapeStatePool, contPruneShapePool, langContPruneShapeStatePool, langContPruneShapePool, langAtomicContPruneShapeStatePool, langAtomicContPruneShapePool, or pool"
        )
    }

  def checkSharedEvilFamilyPlateau(
      seqMode: String,
      k: Int,
      maxLength: Int,
      step: Int,
      metric: String,
      requirePlateau: Boolean,
      directDag: Boolean = false,
      compareTree: Boolean = false,
      statePoolCubicFactor: Double = 0.0,
      statePoolMinRegexSize: Int = 5,
      statePoolTopLimit: Int = 1,
      growthTopLimit: Int = 0,
      progress: Boolean = false,
      metricOnly: Boolean = false
  ): Unit = {
    if (maxLength <= 0) return
    if (step <= 0) {
      throw new IllegalArgumentException(s"shared plateau step must be positive, got $step")
    }
    val r = thesisCh7Evil(k)
    val label = if (directDag) "direct-shared" else "shared"
    val store = new DagStore(eraseBits = metricOnly)
    var root = store.fromARexp(intern(r))
    var treeRegex = intern(r)

    if (metricOnly && metric == "tree") {
      throw new IllegalArgumentException("metric-only long-tail cannot measure tree size without reconstructing the full tree")
    }

    def metricOnlyRootKeys(id: Int): Set[Int] =
      metric match {
        case "statePool" => store.reachableIds(id)
        case "shapeStatePool" | "shapePool" => store.reachableIds(id).map(store.shapeId)
        case "altSetShapeStatePool" | "altSetShapePool" => store.reachableIds(id).map(store.altSetShapeId)
        case "unaryModShapeStatePool" | "unaryModShapePool" => store.reachableIds(id).map(store.unaryModShapeId)
        case "unaryPruneShapeStatePool" | "unaryPruneShapePool" => store.reachableUnaryPruneShapeIds(id)
        case "contPruneShapeStatePool" | "contPruneShapePool" => store.reachableContPruneShapeIds(id)
        case "langContPruneShapeStatePool" | "langContPruneShapePool" => store.reachableLangContPruneShapeIds(id)
        case "langAtomicContPruneShapeStatePool" | "langAtomicContPruneShapePool" =>
          store.reachableLangAtomicContPruneShapeIds(id)
        case "dag" | "shape" | "shapeDag" | "pool" => Set.empty
        case _ => Set.empty
      }

    var statePoolIds = if (metricOnly) Set.empty[Int] else store.reachableIds(root)
    var shapeStatePoolKeys = if (metricOnly) Set.empty[Int] else statePoolIds.map(store.shapeId)
    var altSetShapeStatePoolKeys = if (metricOnly) Set.empty[Int] else statePoolIds.map(store.altSetShapeId)
    var unaryModShapeStatePoolKeys = if (metricOnly) Set.empty[Int] else statePoolIds.map(store.unaryModShapeId)
    var unaryPruneShapeStatePoolKeys = if (metricOnly) Set.empty[Int] else store.reachableUnaryPruneShapeIds(root)
    var contPruneShapeStatePoolKeys = if (metricOnly) Set.empty[Int] else store.reachableContPruneShapeIds(root)
    var langContPruneShapeStatePoolKeys = if (metricOnly) Set.empty[Int] else store.reachableLangContPruneShapeIds(root)
    var langAtomicContPruneShapeStatePoolKeys =
      if (metricOnly) Set.empty[Int] else store.reachableLangAtomicContPruneShapeIds(root)
    var metricOnlyKeys = if (metricOnly) metricOnlyRootKeys(root) else Set.empty[Int]
    var shapeWitnesses = statePoolIds.iterator.map(id => store.shapeId(id) -> id).toMap

    def metricOnlyValue: Int =
      metric match {
        case "dag" => store.reachableIds(root).size
        case "shape" | "shapeDag" => store.reachableShapeSize(root)
        case "pool" => store.totalSize
        case _ => metricOnlyKeys.size
      }

    def metricOnlySnapshot(value: Int): SharedResult =
      SharedResult(
        None,
        -1,
        if (metric == "dag") value else -1,
        if (metric == "shape" || metric == "shapeDag") value else -1,
        if (metric == "statePool") value else -1,
        if (metric == "shapeStatePool" || metric == "shapePool") value else -1,
        if (metric == "altSetShapeStatePool" || metric == "altSetShapePool") value else -1,
        if (metric == "unaryModShapeStatePool" || metric == "unaryModShapePool") value else -1,
        if (metric == "unaryPruneShapeStatePool" || metric == "unaryPruneShapePool") value else -1,
        if (metric == "contPruneShapeStatePool" || metric == "contPruneShapePool") value else -1,
        if (metric == "langContPruneShapeStatePool" || metric == "langContPruneShapePool") value else -1,
        if (metric == "langAtomicContPruneShapeStatePool" || metric == "langAtomicContPruneShapePool") value else -1,
        if (metric == "pool") value else store.totalSize
      )

    def snapshot(length: Int): SharedResult = {
      if (metricOnly) {
        metricOnlySnapshot(metricOnlyValue)
      } else {
        val finalRegex = store.toARexp(root)
        SharedResult(
          None,
          asize(finalRegex),
          store.reachableIds(root).size,
          store.reachableShapeSize(root),
          statePoolIds.size,
          shapeStatePoolKeys.size,
          altSetShapeStatePoolKeys.size,
          unaryModShapeStatePoolKeys.size,
          unaryPruneShapeStatePoolKeys.size,
          contPruneShapeStatePoolKeys.size,
          langContPruneShapeStatePoolKeys.size,
          langAtomicContPruneShapeStatePoolKeys.size,
          store.totalSize
        )
      }
    }

    val points = scala.collection.mutable.ArrayBuffer.empty[(Int, SharedResult, Int)]
    var frontier = Vector.empty[SharedStatePoolObservation]
    var distinctFrontier = Vector.empty[SharedStatePoolObservation]
    var lastSampleShapeKeys = shapeStatePoolKeys
    var growthSamples = Vector.empty[String]
    var previous = Option.empty[(Int, Int)]
    var nonIncrease = Option.empty[(Int, Int, Int)]
    var currentLength = 0
    while (currentLength <= maxLength && nonIncrease.isEmpty) {
      val input = if (metricOnly) "" else "a" * currentLength
      val out = snapshot(currentLength)
      val value = sharedResultMetric(metric, out)
      points += ((currentLength, out, value))
      if (progress) {
        println(
          s"Chapter 7 k=$k $label $seqMode long-tail-progress n=$currentLength metric=$metric value=$value tree=${out.treeSize} dag=${out.dagSize} shape=${out.shapeDagSize} statePool=${out.statePoolSize} shapeStatePool=${out.shapeStatePoolSize} altSetShapeStatePool=${out.altSetShapeStatePoolSize} unaryModShapeStatePool=${out.unaryModShapeStatePoolSize} unaryPruneShapeStatePool=${out.unaryPruneShapeStatePoolSize} contPruneShapeStatePool=${out.contPruneShapeStatePoolSize} langContPruneShapeStatePool=${out.langContPruneShapeStatePoolSize} langAtomicContPruneShapeStatePool=${out.langAtomicContPruneShapeStatePoolSize} pool=${out.poolSize}"
        )
      }
      if (!metricOnly) {
        val obs = sharedStatePoolObservation(r, input, out, s"Chapter 7 plateau k=$k n=$currentLength")
        frontier = sharedStatePoolTop(frontier, obs, statePoolMinRegexSize, statePoolTopLimit)
        distinctFrontier = sharedStatePoolTopDistinctRegex(distinctFrontier, obs, statePoolMinRegexSize, statePoolTopLimit)
        checkSharedStatePoolCubicBudget(r, input, out, obs.label, seqMode, statePoolMinRegexSize, statePoolCubicFactor)
      }
      if (!metricOnly && growthTopLimit > 0 && currentLength > 0) {
        val newKeys = shapeStatePoolKeys -- lastSampleShapeKeys
        val examples = newKeys.toVector
          .sortBy(identity)
          .take(growthTopLimit)
          .map(k => shortLogText(shapeWitnesses.get(k).map(store.compactShapeKey).getOrElse(s"shape#$k"), 180))
        growthSamples = growthSamples :+
          s"n=$currentLength newShapes=${newKeys.size}" +
            (if (examples.isEmpty) "" else examples.mkString(" examples=[", " | ", "]"))
        lastSampleShapeKeys = shapeStatePoolKeys
      }
      previous.foreach { case (prevN, prevValue) =>
        if (value <= prevValue) {
          nonIncrease = Some((currentLength, prevValue, value))
        }
      }
      previous = Some((currentLength, value))
      if (currentLength >= maxLength) {
        currentLength = maxLength + 1
      } else {
        var advanced = 0
        while (advanced < step && currentLength < maxLength && nonIncrease.isEmpty) {
          root =
            if (directDag) store.stepDirectWithMode(seqMode, 'a', root)
            else store.stepWithMode(seqMode, 'a', root)
          if (directDag && compareTree) {
            treeRegex = bsimpCubicWithMode(seqMode, bder('a', treeRegex))
            val directRegex = store.toARexp(root)
            if (directRegex != treeRegex) {
              throw new AssertionError(
                s"""direct-DAG/tree-step mismatch in long-tail plateau
                   |seqMode = $seqMode
                   |regex   = $r
                   |prefix  = ${currentLength + 1}
                   |direct  = $directRegex
                   |tree    = $treeRegex
                   |""".stripMargin
              )
            }
          }
          if (metricOnly) {
            metricOnlyKeys = metricOnlyKeys ++ metricOnlyRootKeys(root)
          } else {
            val ids = store.reachableIds(root)
            statePoolIds = statePoolIds ++ ids
            shapeStatePoolKeys = shapeStatePoolKeys ++ ids.map(store.shapeId)
            altSetShapeStatePoolKeys = altSetShapeStatePoolKeys ++ ids.map(store.altSetShapeId)
            unaryModShapeStatePoolKeys = unaryModShapeStatePoolKeys ++ ids.map(store.unaryModShapeId)
            unaryPruneShapeStatePoolKeys = unaryPruneShapeStatePoolKeys ++ store.reachableUnaryPruneShapeIds(root)
            contPruneShapeStatePoolKeys = contPruneShapeStatePoolKeys ++ store.reachableContPruneShapeIds(root)
            langContPruneShapeStatePoolKeys = langContPruneShapeStatePoolKeys ++ store.reachableLangContPruneShapeIds(root)
            langAtomicContPruneShapeStatePoolKeys =
              langAtomicContPruneShapeStatePoolKeys ++ store.reachableLangAtomicContPruneShapeIds(root)
            ids.foreach { id =>
              val key = store.shapeId(id)
              if (!shapeWitnesses.contains(key)) {
                shapeWitnesses = shapeWitnesses.updated(key, id)
              }
            }
          }
          currentLength += 1
          advanced += 1
        }
      }
    }
    val renderedPoints = points.map { case (len, out, value) =>
      s"$len->$metric=$value/tree=${out.treeSize}/dag=${out.dagSize}/shape=${out.shapeDagSize}/statePool=${out.statePoolSize}/shapeStatePool=${out.shapeStatePoolSize}/altSetShapeStatePool=${out.altSetShapeStatePoolSize}/unaryModShapeStatePool=${out.unaryModShapeStatePoolSize}/unaryPruneShapeStatePool=${out.unaryPruneShapeStatePoolSize}/contPruneShapeStatePool=${out.contPruneShapeStatePoolSize}/langContPruneShapeStatePool=${out.langContPruneShapeStatePoolSize}/langAtomicContPruneShapeStatePool=${out.langAtomicContPruneShapeStatePoolSize}/pool=${out.poolSize}"
    }.toVector
    val compact =
      if (renderedPoints.length <= 24) renderedPoints.mkString(", ")
      else ((renderedPoints.take(12) :+ "...") ++ renderedPoints.takeRight(8)).mkString(", ")
    val metricOnlyLabel = if (metricOnly) " metric-only" else ""
    println(s"Chapter 7 k=$k $label $seqMode long-tail$metricOnlyLabel metric=$metric step=$step max=$maxLength: $compact")
    if (growthTopLimit > 0) {
      val compactGrowth =
        if (growthSamples.length <= 20) growthSamples.mkString("; ")
        else ((growthSamples.take(10) :+ "...") ++ growthSamples.takeRight(8)).mkString("; ")
      println(s"Chapter 7 k=$k $label $seqMode long-tail shape-growth samples: $compactGrowth")
    }
    if (!metricOnly) {
      println(s"Chapter 7 k=$k $label $seqMode long-tail statePool frontier (factor=$statePoolCubicFactor, minRegexSize=$statePoolMinRegexSize, top=$statePoolTopLimit): ${sharedStatePoolFrontiersSummary(frontier, distinctFrontier, statePoolMinRegexSize)}")
    } else {
      println(s"Chapter 7 k=$k $label $seqMode long-tail metric-only skipped statePool frontier and full-tree reconstruction")
    }
    nonIncrease match {
      case Some((len, prevValue, value)) =>
        println(s"Chapter 7 k=$k $label $seqMode long-tail metric=$metric first non-increase at n=$len: previous=$prevValue current=$value")
      case None =>
        val last = points.lastOption.map { case (len, _, value) => s"n=$len value=$value" }.getOrElse("no points")
        val msg =
          s"Chapter 7 k=$k $label $seqMode long-tail metric=$metric remained strictly increasing through $last (step=$step, max=$maxLength)"
        if (requirePlateau) {
          throw new AssertionError(msg)
        } else {
          println(msg)
        }
    }
  }

  def checkSharedNoReassocValuePreservation(maxDepth: Int, maxInput: Int, maxRegexes: Int): Unit =
    checkSharedValuePreservation("no-reassoc", maxDepth, maxInput, maxRegexes)

  def checkSharedNoReassocRandomValuePreservation(cases: Int, maxDepth: Int, maxInput: Int, seed: Long): Unit =
    checkSharedRandomValuePreservation("no-reassoc", cases, maxDepth, maxInput, seed)

  def checkSharedNoReassocEvilFamilyTrace(
      k: Int,
      lengths: List[Int],
      dagThreshold: Int,
      shapeThreshold: Int
  ): Unit =
    checkSharedEvilFamilyTrace("no-reassoc", k, lengths, dagThreshold, shapeThreshold)

  def checkEvilFamilyTrace(
      k: Int,
      lengths: List[Int],
      treeThreshold: Int,
      dagThreshold: Int,
      shapeThreshold: Int
  ): Unit = {
    val r = thesisCh7Evil(k)
    val trace = lengths.map { n =>
      val out = bdersSimpCubic(intern(r), "a" * n)
      n -> (asize(out), adagSize(out), ashapeDagSize(out))
    }
    println(s"Chapter 7 k=$k bsimpCubic trace: " +
      trace.map { case (n, (tree, dag, shapeDag)) => s"$n->$tree/dag=$dag/shape=$shapeDag" }.mkString(", "))
    trace.foreach { case (n, (size, dagSize, shapeSize)) =>
      if (size >= treeThreshold) {
        val out = bdersSimpCubic(intern(r), "a" * n)
        println(s"Chapter 7 failed-shape n=$n: ${shortCounts(out)}")
        throw new AssertionError(s"Chapter 7 smoke threshold failed at n=$n: asize=$size threshold=$treeThreshold")
      }
      if (dagThreshold > 0 && dagSize >= dagThreshold) {
        throw new AssertionError(s"Chapter 7 DAG threshold failed at n=$n: adagSize=$dagSize threshold=$dagThreshold")
      }
      if (shapeThreshold > 0 && shapeSize >= shapeThreshold) {
        throw new AssertionError(s"Chapter 7 shape-DAG threshold failed at n=$n: ashapeDagSize=$shapeSize threshold=$shapeThreshold")
      }
    }
  }

  def checkStrongEvilFamilyTrace(k: Int, lengths: List[Int]): Unit = {
    val r = thesisCh7Evil(k)
    val trace = lengths.map { n =>
      val out = bdersStrong(intern(r), "a" * n)
      n -> (asize(out), adagSize(out), ashapeDagSize(out))
    }
    println(s"Chapter 7 k=$k bsimpStrong trace: " +
      trace.map { case (n, (tree, dag, shape)) =>
        s"$n->$tree/dag=$dag/shape=$shape"
      }.mkString(", "))
  }

  private def csvEscape(s: String): String =
    "\"" + s.replace("\"", "\"\"") + "\""

  private def isStrongMemoMetric(metric: String): Boolean =
    metric.startsWith("strongMemo")

  private def ch7StrongMemoSizeValue(
      metric: String,
      r: Rexp,
      input: String,
      result: StrongDeferredMemoResult
  ): Option[Long] =
    metric match {
      case "strongMemoTree" => Some(result.strongTree.toLong)
      case "strongMemoDag" => Some(result.strongDag.toLong)
      case "strongMemoShape" => Some(result.strongShapeDag.toLong)
      case "strongMemoAcceptsStates" => Some(result.memo.acceptsStates.toLong)
      case "strongMemoValueStates" => Some(result.memo.valueStates.toLong)
      case "strongMemoStates" =>
        Some(result.memo.acceptsStates.toLong + result.memo.valueStates.toLong)
      case "strongMemoSplitProbes" => Some(result.memo.splitProbes.toLong)
      case "strongMemoQueries" =>
        Some(result.memo.acceptsQueries.toLong + result.memo.valueQueries.toLong)
      case "strongMemoActiveRows" => Some(result.activeSuffix.rows.toLong)
      case "strongMemoActiveKeys" => Some(result.activeSuffix.keys.toLong)
      case "strongMemoActiveAltNodes" => Some(result.activeSuffix.altNodes.toLong)
      case "strongMemoActivePayloadRoots" =>
        Some(result.activeSuffix.payloadRoots.toLong)
      case "strongMemoActivePayloadDag" =>
        Some(result.activeSuffix.payloadDagUniverseSize.toLong)
      case "strongMemoActiveKeyDag" =>
        Some(result.activeSuffix.keyDagUniverseSize.toLong)
      case "strongMemoActiveComponentUnion" =>
        Some(result.activeSuffix.componentUnionSize.toLong)
      case "strongMemoActiveDecompBound" =>
        Some(result.activeSuffix.decompBoundSize.toLong)
      case "strongMemoActiveMaxBucket" =>
        Some(result.activeSuffix.maxBucket.toLong)
      case "strongMemoActiveMaxRowSize" =>
        Some(result.activeSuffix.maxRowSize.toLong)
      case "strongMemoActiveMaxRowDag" =>
        Some(result.activeSuffix.maxRowDagSize.toLong)
      case "strongMemoActiveMaxRowShapeDag" =>
        Some(result.activeSuffix.maxRowShapeDagSize.toLong)
      case "strongMemoActiveRowDagUniverse" =>
        Some(result.activeSuffix.rowDagUniverseSize.toLong)
      case "strongMemoActivePairBudget" =>
        Some(result.activeSuffix.pairBudget)
      case "strongMemoFinalActiveRows" =>
        Some(result.finalActiveSuffix.rows.toLong)
      case "strongMemoFinalActiveKeys" =>
        Some(result.finalActiveSuffix.keys.toLong)
      case "strongMemoFinalActiveAltNodes" =>
        Some(result.finalActiveSuffix.altNodes.toLong)
      case "strongMemoFinalActivePayloadRoots" =>
        Some(result.finalActiveSuffix.payloadRoots.toLong)
      case "strongMemoFinalActivePayloadDag" =>
        Some(result.finalActiveSuffix.payloadDagUniverseSize.toLong)
      case "strongMemoFinalActiveKeyDag" =>
        Some(result.finalActiveSuffix.keyDagUniverseSize.toLong)
      case "strongMemoFinalActiveComponentUnion" =>
        Some(result.finalActiveSuffix.componentUnionSize.toLong)
      case "strongMemoFinalActiveDecompBound" =>
        Some(result.finalActiveSuffix.decompBoundSize.toLong)
      case "strongMemoFinalActiveMaxBucket" =>
        Some(result.finalActiveSuffix.maxBucket.toLong)
      case "strongMemoFinalActiveMaxRowSize" =>
        Some(result.finalActiveSuffix.maxRowSize.toLong)
      case "strongMemoFinalActiveMaxRowDag" =>
        Some(result.finalActiveSuffix.maxRowDagSize.toLong)
      case "strongMemoFinalActiveMaxRowShapeDag" =>
        Some(result.finalActiveSuffix.maxRowShapeDagSize.toLong)
      case "strongMemoFinalActiveRowDagUniverse" =>
        Some(result.finalActiveSuffix.rowDagUniverseSize.toLong)
      case "strongMemoFinalActivePairBudget" =>
        Some(result.finalActiveSuffix.pairBudget)
      case "strongMemoSpanBound" => Some(memoSpanBound(r, input.length))
      case "strongMemoSplitBound" => Some(memoSplitProbeBound(r, input.length))
      case _ => None
    }

  private def ch7SizeValue(metric: String, seqMode: String, r: Rexp, input: String): Long =
    metric match {
      case "strongTree" => asize(bdersStrong(intern(r), input)).toLong
      case "strongDag" => adagSize(bdersStrong(intern(r), input)).toLong
      case "strongShape" => ashapeDagSize(bdersStrong(intern(r), input)).toLong
      case "strongMemoTree" => strongDeferredMemoResult(r, input).strongTree.toLong
      case "strongMemoDag" => strongDeferredMemoResult(r, input).strongDag.toLong
      case "strongMemoShape" => strongDeferredMemoResult(r, input).strongShapeDag.toLong
      case "strongMemoAcceptsStates" => strongDeferredMemoResult(r, input).memo.acceptsStates.toLong
      case "strongMemoValueStates" => strongDeferredMemoResult(r, input).memo.valueStates.toLong
      case "strongMemoStates" =>
        val memo = strongDeferredMemoResult(r, input).memo
        memo.acceptsStates.toLong + memo.valueStates.toLong
      case "strongMemoSplitProbes" => strongDeferredMemoResult(r, input).memo.splitProbes.toLong
      case "strongMemoQueries" =>
        val memo = strongDeferredMemoResult(r, input).memo
        memo.acceptsQueries.toLong + memo.valueQueries.toLong
      case "strongMemoActiveRows" => strongDeferredMemoResult(r, input).activeSuffix.rows.toLong
      case "strongMemoActiveKeys" => strongDeferredMemoResult(r, input).activeSuffix.keys.toLong
      case "strongMemoActiveAltNodes" => strongDeferredMemoResult(r, input).activeSuffix.altNodes.toLong
      case "strongMemoActivePayloadRoots" => strongDeferredMemoResult(r, input).activeSuffix.payloadRoots.toLong
      case "strongMemoActivePayloadDag" =>
        strongDeferredMemoResult(r, input).activeSuffix.payloadDagUniverseSize.toLong
      case "strongMemoActiveKeyDag" =>
        strongDeferredMemoResult(r, input).activeSuffix.keyDagUniverseSize.toLong
      case "strongMemoActiveComponentUnion" =>
        strongDeferredMemoResult(r, input).activeSuffix.componentUnionSize.toLong
      case "strongMemoActiveDecompBound" =>
        strongDeferredMemoResult(r, input).activeSuffix.decompBoundSize.toLong
      case "strongMemoActiveMaxBucket" => strongDeferredMemoResult(r, input).activeSuffix.maxBucket.toLong
      case "strongMemoActiveMaxRowSize" => strongDeferredMemoResult(r, input).activeSuffix.maxRowSize.toLong
      case "strongMemoActiveMaxRowDag" => strongDeferredMemoResult(r, input).activeSuffix.maxRowDagSize.toLong
      case "strongMemoActiveMaxRowShapeDag" =>
        strongDeferredMemoResult(r, input).activeSuffix.maxRowShapeDagSize.toLong
      case "strongMemoActiveRowDagUniverse" =>
        strongDeferredMemoResult(r, input).activeSuffix.rowDagUniverseSize.toLong
      case "strongMemoActivePairBudget" => strongDeferredMemoResult(r, input).activeSuffix.pairBudget
      case "strongMemoFinalActiveRows" => strongDeferredMemoResult(r, input).finalActiveSuffix.rows.toLong
      case "strongMemoFinalActiveKeys" => strongDeferredMemoResult(r, input).finalActiveSuffix.keys.toLong
      case "strongMemoFinalActiveAltNodes" =>
        strongDeferredMemoResult(r, input).finalActiveSuffix.altNodes.toLong
      case "strongMemoFinalActivePayloadRoots" =>
        strongDeferredMemoResult(r, input).finalActiveSuffix.payloadRoots.toLong
      case "strongMemoFinalActivePayloadDag" =>
        strongDeferredMemoResult(r, input).finalActiveSuffix.payloadDagUniverseSize.toLong
      case "strongMemoFinalActiveKeyDag" =>
        strongDeferredMemoResult(r, input).finalActiveSuffix.keyDagUniverseSize.toLong
      case "strongMemoFinalActiveComponentUnion" =>
        strongDeferredMemoResult(r, input).finalActiveSuffix.componentUnionSize.toLong
      case "strongMemoFinalActiveDecompBound" =>
        strongDeferredMemoResult(r, input).finalActiveSuffix.decompBoundSize.toLong
      case "strongMemoFinalActiveMaxBucket" => strongDeferredMemoResult(r, input).finalActiveSuffix.maxBucket.toLong
      case "strongMemoFinalActiveMaxRowSize" => strongDeferredMemoResult(r, input).finalActiveSuffix.maxRowSize.toLong
      case "strongMemoFinalActiveMaxRowDag" => strongDeferredMemoResult(r, input).finalActiveSuffix.maxRowDagSize.toLong
      case "strongMemoFinalActiveMaxRowShapeDag" =>
        strongDeferredMemoResult(r, input).finalActiveSuffix.maxRowShapeDagSize.toLong
      case "strongMemoFinalActiveRowDagUniverse" =>
        strongDeferredMemoResult(r, input).finalActiveSuffix.rowDagUniverseSize.toLong
      case "strongMemoFinalActivePairBudget" => strongDeferredMemoResult(r, input).finalActiveSuffix.pairBudget
      case "strongMemoSpanBound" => memoSpanBound(r, input.length)
      case "strongMemoSplitBound" => memoSplitProbeBound(r, input.length)
      case "strongSafeTree" => asize(bdersStrongSafe(intern(r), input)).toLong
      case "strongSafeDag" => adagSize(bdersStrongSafe(intern(r), input)).toLong
      case "strongSafeShape" => ashapeDagSize(bdersStrongSafe(intern(r), input)).toLong
      case "cubicTree" => asize(bdersSimpCubic(intern(r), input)).toLong
      case "cubicDag" => adagSize(bdersSimpCubic(intern(r), input)).toLong
      case "cubicShape" => ashapeDagSize(bdersSimpCubic(intern(r), input)).toLong
      case "sharedTree" => sharedModeResult(seqMode, r, input, directDag = true).treeSize.toLong
      case "sharedDag" => sharedModeResult(seqMode, r, input, directDag = true).dagSize.toLong
      case "sharedShape" => sharedModeResult(seqMode, r, input, directDag = true).shapeDagSize.toLong
      case "sharedStatePool" => sharedModeResult(seqMode, r, input, directDag = true).statePoolSize.toLong
      case "sharedShapeStatePool" => sharedModeResult(seqMode, r, input, directDag = true).shapeStatePoolSize.toLong
      case "langContPruneShapeStatePool" =>
        sharedModeResult(seqMode, r, input, directDag = true).langContPruneShapeStatePoolSize.toLong
      case "langAtomicContPruneShapeStatePool" =>
        sharedModeResult(seqMode, r, input, directDag = true).langAtomicContPruneShapeStatePoolSize.toLong
      case other =>
        throw new IllegalArgumentException(
          s"unknown POSIX_SMOKE_CH7_SIZE_METRIC=$other; expected strongTree, strongDag, strongShape, strongMemoTree, strongMemoDag, strongMemoShape, strongMemoAcceptsStates, strongMemoValueStates, strongMemoStates, strongMemoSplitProbes, strongMemoQueries, strongMemoActiveRows, strongMemoActiveKeys, strongMemoActiveAltNodes, strongMemoActivePayloadRoots, strongMemoActivePayloadDag, strongMemoActiveKeyDag, strongMemoActiveComponentUnion, strongMemoActiveDecompBound, strongMemoActiveMaxBucket, strongMemoActiveMaxRowSize, strongMemoActiveMaxRowDag, strongMemoActiveMaxRowShapeDag, strongMemoActiveRowDagUniverse, strongMemoActivePairBudget, strongMemoFinalActiveRows, strongMemoFinalActiveKeys, strongMemoFinalActiveAltNodes, strongMemoFinalActivePayloadRoots, strongMemoFinalActivePayloadDag, strongMemoFinalActiveKeyDag, strongMemoFinalActiveComponentUnion, strongMemoFinalActiveDecompBound, strongMemoFinalActiveMaxBucket, strongMemoFinalActiveMaxRowSize, strongMemoFinalActiveMaxRowDag, strongMemoFinalActiveMaxRowShapeDag, strongMemoFinalActiveRowDagUniverse, strongMemoFinalActivePairBudget, strongMemoSpanBound, strongMemoSplitBound, strongSafeTree, strongSafeDag, strongSafeShape, cubicTree, cubicDag, cubicShape, sharedTree, sharedDag, sharedShape, sharedStatePool, sharedShapeStatePool, langContPruneShapeStatePool, or langAtomicContPruneShapeStatePool"
        )
    }

  def writeCh7SizeCsv(
      path: String,
      ks: List[Int],
      lengths: List[Int],
      metrics: List[String],
      seqMode: String
  ): Unit = {
    val p = java.nio.file.Paths.get(path)
    val parent = p.getParent
    if (parent != null) java.nio.file.Files.createDirectories(parent)
    val out = new java.io.PrintWriter(java.nio.file.Files.newBufferedWriter(p))
    try {
      out.println("k,n,metric,value,seqMode")
      for {
        k <- ks
        n <- lengths
      } {
        val r = thesisCh7Evil(k)
        val input = "a" * n
        val strongMemoResult =
          if (metrics.exists(isStrongMemoMetric)) Some(strongDeferredMemoResult(r, input))
          else None
        metrics.foreach { metric =>
          val value =
            strongMemoResult
              .flatMap(ch7StrongMemoSizeValue(metric, r, input, _))
              .getOrElse(ch7SizeValue(metric, seqMode, r, input))
          out.println(s"$k,$n,${csvEscape(metric)},$value,${csvEscape(seqMode)}")
        }
      }
    } finally {
      out.close()
    }
    println(s"wrote Chapter 7 size CSV: $path")
  }

  def checkStrongDeferredMemoEvilFamilyTrace(
      k: Int,
      lengths: List[Int],
      treeThreshold: Int,
      dagThreshold: Int,
      shapeThreshold: Int,
      treeCubicFactor: Double,
      minRegexSize: Int,
      topLimit: Int,
      finalActiveConfig: FinalActiveBudgetConfig = FinalActiveBudgetConfig.Disabled
  ): Unit = {
    val r = thesisCh7Evil(k)
    val rootSize = rsize(r).toLong
    val cubicTreeBound = strongCubicTreeBound(r, treeCubicFactor)
    var frontier = Vector.empty[StrongCubicObservation]
    var distinctFrontier = Vector.empty[StrongCubicObservation]
    var finalActiveRowsFrontier = Vector.empty[FinalActiveBudgetObservation]
    var finalActivePairFrontier = Vector.empty[FinalActiveBudgetObservation]
    var finalActiveMemberFrontier = Vector.empty[FinalActiveBudgetObservation]
    var finalActiveRowDagUniverseFrontier = Vector.empty[FinalActiveBudgetObservation]
    var finalActiveComponentUnionFrontier = Vector.empty[FinalActiveBudgetObservation]
    var finalActiveDecompBoundFrontier = Vector.empty[FinalActiveBudgetObservation]
    val trace = lengths.map { n =>
      val input = "a" * n
      val result = strongDeferredMemoResult(r, input)
      val obs = strongCubicObservation(r, input, result, s"Chapter 7 k=$k n=$n")
      frontier = strongerCubicTop(frontier, obs, minRegexSize, topLimit)
      distinctFrontier = strongerCubicTopDistinctRegex(distinctFrontier, obs, minRegexSize, topLimit)
      val finalObs = finalActiveBudgetObservation(r, input, result, s"Chapter 7 k=$k n=$n")
      finalActiveRowsFrontier = finalActiveRowsTop(finalActiveRowsFrontier, finalObs, finalActiveConfig)
      finalActivePairFrontier = finalActivePairTop(finalActivePairFrontier, finalObs, finalActiveConfig)
      finalActiveMemberFrontier = finalActiveMemberTop(finalActiveMemberFrontier, finalObs, finalActiveConfig)
      finalActiveRowDagUniverseFrontier =
        finalActiveRowDagUniverseTop(finalActiveRowDagUniverseFrontier, finalObs, finalActiveConfig)
      finalActiveComponentUnionFrontier =
        finalActiveComponentUnionTop(finalActiveComponentUnionFrontier, finalObs, finalActiveConfig)
      finalActiveDecompBoundFrontier =
        finalActiveDecompBoundTop(finalActiveDecompBoundFrontier, finalObs, finalActiveConfig)
      checkMemoUniverseBound(r, input, result, s"Chapter 7 k=$k n=$n")
      checkFinalActiveBudget(r, input, result, s"Chapter 7 k=$k n=$n", finalActiveConfig)
      if (!result.value.exists(flatVal(_) == input)) {
        throw new AssertionError(
          s"""Chapter 7 strong memo-deferred value reconstruction failed
             |k          = $k
             |n          = $n
             |regex      = $r
             |input      = $input
             |memo       = ${result.value}
             |strongTree = ${result.strongTree}
             |strongDag  = ${result.strongDag}
             |""".stripMargin
        )
      }
      if (treeThreshold > 0 && result.strongTree >= treeThreshold) {
        val out = bdersStrong(intern(r), input)
        println(s"Chapter 7 strong failed-shape n=$n: ${shortCounts(out)}")
        throw new AssertionError(
          s"Chapter 7 strong tree threshold failed at n=$n: asize=${result.strongTree} threshold=$treeThreshold"
        )
      }
      checkStrongCubicTreeBudget(r, input, result, s"Chapter 7 k=$k n=$n", treeCubicFactor)
      if (dagThreshold > 0 && result.strongDag >= dagThreshold) {
        throw new AssertionError(
          s"Chapter 7 strong DAG threshold failed at n=$n: adagSize=${result.strongDag} threshold=$dagThreshold"
        )
      }
      if (shapeThreshold > 0 && result.strongShapeDag >= shapeThreshold) {
        throw new AssertionError(
          s"Chapter 7 strong shape-DAG threshold failed at n=$n: ashapeDagSize=${result.strongShapeDag} threshold=$shapeThreshold"
        )
      }
      n -> result
    }
    println(s"Chapter 7 k=$k strong deferred memo trace: " +
      trace.map { case (n, s) =>
        val spanBound = memoSpanBound(r, n)
        val splitBound = memoSplitProbeBound(r, n)
        s"$n->strong=${s.strongTree}/dag=${s.strongDag}/shape=${s.strongShapeDag}" +
          s"/rsize=$rootSize/cubicTreeBound=$cubicTreeBound" +
          s"/memoA=${s.memo.acceptsStates}/memoV=${s.memo.valueStates}" +
          s"/activeRows=${s.activeSuffix.rows}/activeKeys=${s.activeSuffix.keys}" +
          s"/activeAltNodes=${s.activeSuffix.altNodes}" +
          s"/activePayloadRoots=${s.activeSuffix.payloadRoots}" +
          s"/activePayloadDag=${s.activeSuffix.payloadDagUniverseSize}" +
          s"/activeKeyDag=${s.activeSuffix.keyDagUniverseSize}" +
          s"/activeComponentUnion=${s.activeSuffix.componentUnionSize}" +
          s"/activeDecompBound=${s.activeSuffix.decompBoundSize}" +
          s"/activeMaxBucket=${s.activeSuffix.maxBucket}" +
          s"/activeMaxRowSize=${s.activeSuffix.maxRowSize}" +
          s"/activeMaxRowDag=${s.activeSuffix.maxRowDagSize}" +
          s"/activeMaxRowShapeDag=${s.activeSuffix.maxRowShapeDagSize}" +
          s"/activeRowDagUniverse=${s.activeSuffix.rowDagUniverseSize}" +
          s"/activePairs=${s.activeSuffix.pairBudget}" +
          s"/finalRows=${s.finalActiveSuffix.rows}/finalKeys=${s.finalActiveSuffix.keys}" +
          s"/finalAltNodes=${s.finalActiveSuffix.altNodes}" +
          s"/finalPayloadRoots=${s.finalActiveSuffix.payloadRoots}" +
          s"/finalPayloadDag=${s.finalActiveSuffix.payloadDagUniverseSize}" +
          s"/finalKeyDag=${s.finalActiveSuffix.keyDagUniverseSize}" +
          s"/finalComponentUnion=${s.finalActiveSuffix.componentUnionSize}" +
          s"/finalDecompBound=${s.finalActiveSuffix.decompBoundSize}" +
          s"/finalMaxBucket=${s.finalActiveSuffix.maxBucket}" +
          s"/finalMaxRowSize=${s.finalActiveSuffix.maxRowSize}" +
          s"/finalMaxRowDag=${s.finalActiveSuffix.maxRowDagSize}" +
          s"/finalMaxRowShapeDag=${s.finalActiveSuffix.maxRowShapeDagSize}" +
          s"/finalRowDagUniverse=${s.finalActiveSuffix.rowDagUniverseSize}" +
          s"/finalPairs=${s.finalActiveSuffix.pairBudget}" +
          s"/spanBound=$spanBound" +
          s"/queries=${s.memo.acceptsQueries}+${s.memo.valueQueries}" +
          s"/splits=${s.memo.splitProbes}/splitBound=$splitBound"
      }.mkString(", ") +
      s"; ${strongCubicFrontiersSummary(frontier, distinctFrontier, minRegexSize)}" +
      (finalActiveBudgetFrontiersSummary(
        finalActiveRowsFrontier,
        finalActivePairFrontier,
        finalActiveMemberFrontier,
        finalActiveRowDagUniverseFrontier,
        finalActiveComponentUnionFrontier,
        finalActiveDecompBoundFrontier,
        finalActiveConfig
      ) match {
        case "" => ""
        case summary => s"; $summary"
      }))
  }

  def checkStrongSafeEvilFamilyTrace(k: Int, lengths: List[Int]): Unit = {
    val r = thesisCh7Evil(k)
    val trace = lengths.map { n =>
      val out = bdersStrongSafe(intern(r), "a" * n)
      n -> (asize(out), adagSize(out), ashapeDagSize(out))
    }
    println(s"Chapter 7 k=$k bsimpStrongSafe trace: " +
      trace.map { case (n, (tree, dag, shape)) =>
        s"$n->$tree/dag=$dag/shape=$shape"
      }.mkString(", "))
  }

  def checkStrongCoreEvilFamilyTrace(k: Int, lengths: List[Int]): Unit = {
    val r = thesisCh7Evil(k)
    val trace = lengths.map { n =>
      val out = bdersStrongCore(intern(r), "a" * n)
      n -> (asize(out), adagSize(out), ashapeDagSize(out))
    }
    println(s"Chapter 7 k=$k bsimpStrongCore trace: " +
      trace.map { case (n, (tree, dag, shape)) =>
        s"$n->$tree/dag=$dag/shape=$shape"
      }.mkString(", "))
  }

  def checkStrongCoreLoopSizeTrace(k: Int, lengths: List[Int]): Unit = {
    val r = thesisCh7Evil(k)
    val trace = lengths.map { n =>
      val summary = strongCoreLoopSizeSummary(r, "a" * n)
      n -> summary
    }
    println(s"Chapter 7 k=$k bsimpStrongCore loop summary: " +
      trace.map { case (n, s) =>
        s"$n->final=${s.finalSize}/dag=${s.finalDag}/maxRaw=${s.maxRaw}/maxCore=${s.maxCore}"
      }.mkString(", "))
  }

  def checkStrongFullLoopSizeTrace(k: Int, lengths: List[Int]): Unit = {
    val r = thesisCh7Evil(k)
    val trace = lengths.map { n =>
      val summary = strongFullLoopSizeSummary(r, "a" * n)
      n -> summary
    }
    println(s"Chapter 7 k=$k bsimpStrongFullCert loop summary: " +
      trace.map { case (n, s) =>
        s"$n->final=${s.finalSize}/dag=${s.finalDag}/maxRaw=${s.maxRaw}/maxFull=${s.maxCore}"
      }.mkString(", "))
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

    val nestedStar = STAR(STAR(CH('a')))
    val nestedBase = baselineValue(nestedStar, "a")
    val nestedStrong = strongValue(nestedStar, "a")
    if (nestedBase == nestedStrong) {
      throw new AssertionError("bsimpStrong nested-star collapse no longer witnesses a POSIX value mismatch")
    }
    println("counterexample smoke checks passed")
  }

  def checkStrongReconstructionSketch(): Unit = {
    final case class SketchCase(
        name: String,
        regex: Rexp,
        input: String,
        reconstruct: Val => Option[Val]
    )

    val cases = List(
      SketchCase(
        "nested-star collapse",
        STAR(STAR(CH('a'))),
        "a",
        sketchNestedStarRecon
      ),
      SketchCase(
        "star absorption",
        SEQ(STAR(CH('a')), STAR(CH('a'))),
        "a",
        sketchStarAbsorbRecon
      ),
      SketchCase(
        "right nullable unit after star-zero",
        SEQ(STAR(CH('a')), STAR(ZERO)),
        "a",
        sketchStarAbsorbRecon
      )
    )

    cases.foreach { tc =>
      val base = baselineValue(tc.regex, tc.input)
      val strongFinal = bdersStrong(intern(tc.regex), tc.input)
      val strongLocal = nullableErasedValue(strongFinal)
      val reconstructed = strongLocal.flatMap(tc.reconstruct)
      if (base != reconstructed) {
        throw new AssertionError(
          s"""strong reconstruction sketch failed: ${tc.name}
             |regex          = ${tc.regex}
             |input          = ${tc.input}
             |baseline       = $base
             |strongFinal    = $strongFinal
             |strongLocal    = $strongLocal
             |reconstructed  = $reconstructed
             |strongFinalSize= ${asize(strongFinal)}
             |""".stripMargin
        )
      }
      println(
        s"strong reconstruction sketch ${tc.name}: strongSize=${asize(strongFinal)} value=$reconstructed"
      )
    }

    val reassocSmall = SeqVal(CharVal('a'), SeqVal(CharVal('b'), CharVal('c')))
    val reassocLarge = SeqVal(SeqVal(CharVal('a'), CharVal('b')), CharVal('c'))
    if (sketchSeqReassocRecon(reassocSmall) != Some(reassocLarge)) {
      throw new AssertionError("sequence reassociation sketch transformer failed")
    }
    println("strong reconstruction sketch sequence reassociation transformer passed")
  }

  def checkStrongLocalCertificateLaws(): Unit = {
    def checkLaw(name: String, before: ARexp, after: ARexp, rebuild: Val => Option[Val], maxInput: Int): Unit = {
      stringsUpTo(maxInput).foreach { input =>
        val beforeValue = annotatedValue(before, input)
        val afterValue = annotatedValue(after, input)
        val rebuilt = afterValue.flatMap(rebuild)
        if (beforeValue != rebuilt) {
          throw new AssertionError(
            s"""strong local certificate law failed: $name
               |input       = $input
               |before      = $before
               |after       = $after
               |beforeValue = $beforeValue
               |afterValue  = $afterValue
               |rebuilt     = $rebuilt
               |""".stripMargin
          )
        }
      }
      println(s"strong local certificate law $name passed on inputs <= $maxInput")
    }

    val a = ACHAR(Nil, 'a')
    val b = ACHAR(Nil, 'b')
    val aa = ASEQ(Nil, a, a)
    val aOrB = AALTs(Nil, List(fuse(List(Z), a), fuse(List(S), b)))
    val bodies = List(a, aa, aOrB)

    bodies.foreach { body =>
      checkLaw(
        s"nested-star collapse body=${ashapeKey(body)}",
        ASTAR(Nil, ASTAR(Nil, body)),
        ASTAR(Nil, body),
        sketchNestedStarRecon,
        4
      )
      checkLaw(
        s"star absorption body=${ashapeKey(body)}",
        ASEQ(Nil, ASTAR(Nil, body), ASTAR(Nil, body)),
        ASTAR(Nil, body),
        sketchStarAbsorbRecon,
        4
      )
    }

    checkLaw(
      "star-zero collapse",
      ASTAR(Nil, AZERO),
      AONE(Nil),
      {
        case Void => Some(StarsVal(Nil))
        case _ => None
      },
      2
    )

    checkLaw(
      "right AONE deletion with carried bits",
      ASEQ(Nil, ASTAR(Nil, a), AONE(List(S))),
      ASTAR(Nil, a),
      v => Some(SeqVal(v, Void)),
      4
    )

    checkLaw(
      "sequence reassociation",
      ASEQ(Nil, ASEQ(Nil, a, b), a),
      ASEQ(Nil, a, ASEQ(Nil, b, a)),
      sketchSeqReassocRecon,
      3
    )
  }

  def checkStrongCoreCertOnDerivatives(maxDepth: Int, maxInput: Int, maxRegexes: Int): Unit = {
    def checkOne(r: Rexp, s: String, checked: Int): Unit = {
      val before = bders(intern(r), s)
      val cert = bsimpStrongCoreCert(before)
      val beforeValue = if (bnullable(before)) decodeAEpsValue(before, bmkeps(before)) else None
      val afterValue =
        if (bnullable(cert.regex)) decodeAEpsValue(cert.regex, bmkeps(cert.regex)).flatMap(cert.recon)
        else None
      if (beforeValue != afterValue) {
        throw new AssertionError(
          s"""strong core certificate mismatch on derivative expression
             |case        = $checked
             |regex       = $r
             |input       = $s
             |before      = $before
             |after       = ${cert.regex}
             |beforeValue = $beforeValue
             |afterValue  = $afterValue
             |beforeEps   = ${if (bnullable(before)) Some(bmkeps(before)) else None}
             |afterEps    = ${if (bnullable(cert.regex)) Some(bmkeps(cert.regex)) else None}
             |""".stripMargin
        )
      }
    }

    val regexes = regexesUpToDepth(maxDepth, maxRegexes)
    val inputs = stringsUpTo(maxInput)
    var checked = 0
    regexes.foreach { r =>
      inputs.foreach { s =>
        checked += 1
        checkOne(r, s, checked)
      }
    }
    println(s"checked strong core certificates on $checked derivative expressions (depth <= $maxDepth, input length <= $maxInput)")
  }

  def checkStrongCoreCertRandom(cases: Int, maxDepth: Int, maxInput: Int, seed: Long): Unit = {
    val rng = new Random(seed)
    var checked = 0
    (0 until cases).foreach { _ =>
      checked += 1
      val r = randomRegex(rng, maxDepth)
      val s = randomInput(rng, maxInput)
      val before = bders(intern(r), s)
      val cert = bsimpStrongCoreCert(before)
      val beforeValue = if (bnullable(before)) decodeAEpsValue(before, bmkeps(before)) else None
      val afterValue =
        if (bnullable(cert.regex)) decodeAEpsValue(cert.regex, bmkeps(cert.regex)).flatMap(cert.recon)
        else None
      if (beforeValue != afterValue) {
        throw new AssertionError(
          s"""strong core certificate random mismatch on derivative expression
             |seed        = $seed
             |case        = $checked
             |regex       = $r
             |input       = $s
             |before      = $before
             |after       = ${cert.regex}
             |beforeValue = $beforeValue
             |afterValue  = $afterValue
             |beforeEps   = ${if (bnullable(before)) Some(bmkeps(before)) else None}
             |afterEps    = ${if (bnullable(cert.regex)) Some(bmkeps(cert.regex)) else None}
             |""".stripMargin
        )
      }
    }
    println(s"checked strong core certificates on $checked random derivative expressions (depth <= $maxDepth, input length <= $maxInput, seed=$seed)")
  }

  def checkStrongCoreCertifiedValuePreservation(maxDepth: Int, maxInput: Int, maxRegexes: Int): Unit = {
    val regexes = regexesUpToDepth(maxDepth, maxRegexes)
    val inputs = stringsUpTo(maxInput)
    var checked = 0
    regexes.foreach { r =>
      inputs.foreach { s =>
        checked += 1
        val base = baselineValue(r, s)
        val certified = strongCoreCertifiedValue(r, s)
        if (base != certified) {
          throw new AssertionError(
            s"""strong core certified loop value mismatch
               |case      = $checked
               |regex     = $r
             |input     = $s
             |base      = $base
             |certified = $certified
             |coreSize  = ${asize(bdersStrongCore(intern(r), s))}
             |baseSize  = ${asize(bders(intern(r), s))}
             |""".stripMargin
          )
        }
      }
    }
    println(s"checked strong core certified loop values on $checked regex/input pairs (depth <= $maxDepth, input length <= $maxInput)")
  }

  def checkStrongCoreCertifiedValueRandom(cases: Int, maxDepth: Int, maxInput: Int, seed: Long): Unit = {
    val rng = new Random(seed)
    var checked = 0
    (0 until cases).foreach { _ =>
      checked += 1
      val r = randomRegex(rng, maxDepth)
      val s = randomInput(rng, maxInput)
      val base = baselineValue(r, s)
      val certified = strongCoreCertifiedValue(r, s)
      if (base != certified) {
        throw new AssertionError(
          s"""strong core certified loop random value mismatch
             |seed      = $seed
             |case      = $checked
             |regex     = $r
             |input     = $s
             |base      = $base
             |certified = $certified
             |coreSize  = ${asize(bdersStrongCore(intern(r), s))}
             |baseSize  = ${asize(bders(intern(r), s))}
             |""".stripMargin
          )
      }
    }
    println(s"checked strong core certified loop values on $checked random cases (depth <= $maxDepth, input length <= $maxInput, seed=$seed)")
  }

  def checkStrongFullCertifiedValuePreservation(maxDepth: Int, maxInput: Int, maxRegexes: Int): Unit = {
    val regexes = regexesUpToDepth(maxDepth, maxRegexes)
    val inputs = stringsUpTo(maxInput)
    var checked = 0
    regexes.foreach { r =>
      inputs.foreach { s =>
        checked += 1
        val base = baselineValue(r, s)
        val certified = strongFullCertifiedValue(r, s)
        if (base != certified) {
          throw new AssertionError(
            s"""strong full certified loop value mismatch
               |case      = $checked
               |regex     = $r
             |input     = $s
             |base      = $base
             |certified = $certified
             |fullSize  = ${asize(bdersStrongFullCert(intern(r), s))}
             |baseSize  = ${asize(bders(intern(r), s))}
             |""".stripMargin
          )
        }
      }
    }
    println(s"checked strong full certified loop values on $checked regex/input pairs (depth <= $maxDepth, input length <= $maxInput)")
  }

  def checkStrongFullCertifiedValueRandom(cases: Int, maxDepth: Int, maxInput: Int, seed: Long): Unit = {
    val rng = new Random(seed)
    var checked = 0
    (0 until cases).foreach { _ =>
      checked += 1
      val r = randomRegex(rng, maxDepth)
      val s = randomInput(rng, maxInput)
      val base = baselineValue(r, s)
      val certified = strongFullCertifiedValue(r, s)
      if (base != certified) {
        throw new AssertionError(
          s"""strong full certified loop random value mismatch
             |seed      = $seed
             |case      = $checked
             |regex     = $r
             |input     = $s
             |base      = $base
             |certified = $certified
             |fullSize  = ${asize(bdersStrongFullCert(intern(r), s))}
             |baseSize  = ${asize(bders(intern(r), s))}
             |""".stripMargin
        )
      }
    }
    println(s"checked strong full certified loop values on $checked random cases (depth <= $maxDepth, input length <= $maxInput, seed=$seed)")
  }

  def rsize(r: Rexp): Int = r match {
    case ZERO | ONE | CH(_) => 1
    case ALT(r1, r2) => 1 + rsize(r1) + rsize(r2)
    case SEQ(r1, r2) => 1 + rsize(r1) + rsize(r2)
    case STAR(r0) => 1 + rsize(r0)
    case NTIMES(r0, n) => 1 + rsize(r0) + n
  }

  def strongCoreLoopMismatch(r: Rexp, s: String): Boolean =
    baselineValue(r, s) != strongCoreCertifiedValue(r, s)

  def strongFullLoopMismatch(r: Rexp, s: String): Boolean =
    baselineValue(r, s) != strongFullCertifiedValue(r, s)

  def strongDirectMismatch(r: Rexp, s: String): Boolean =
    baselineValue(r, s) != strongValue(r, s)

  def rawInjectLoopMismatch(r: Rexp, s: String): Boolean =
    baselineValue(r, s) != rawInjectCertifiedValue(r, s)

  def strongCoreLoopMismatchReport(r: Rexp, s: String, label: String): String = {
    val base = baselineValue(r, s)
    val certified = strongCoreCertifiedValue(r, s)
    val finalCore = bdersStrongCore(intern(r), s)
    val baseFinal = bders(intern(r), s)
    s"""$label
       |regex     = $r
       |input     = $s
       |rsize     = ${rsize(r)}
       |base      = $base
       |certified = $certified
       |coreSize  = ${asize(finalCore)}
       |coreShape = ${ashapeDagSize(finalCore)}
       |baseSize  = ${asize(baseFinal)}
       |coreCounts= ${shortCounts(finalCore)}
       |baseCounts= ${shortCounts(baseFinal)}
       |""".stripMargin
  }

  def strongDirectMismatchReport(r: Rexp, s: String, label: String): String = {
    val base = baselineValue(r, s)
    val strong = strongValue(r, s)
    val finalStrong = bdersStrong(intern(r), s)
    val baseFinal = bders(intern(r), s)
    s"""$label
       |regex      = $r
       |input      = $s
       |rsize      = ${rsize(r)}
       |base       = $base
       |strong     = $strong
       |strongSize = ${asize(finalStrong)}
       |strongShape= ${ashapeDagSize(finalStrong)}
       |baseSize   = ${asize(baseFinal)}
       |strongNull = ${bnullable(finalStrong)}
       |baseNull   = ${bnullable(baseFinal)}
       |strongBits = ${if (bnullable(finalStrong)) Some(bmkeps(finalStrong)) else None}
       |baseBits   = ${if (bnullable(baseFinal)) Some(bmkeps(baseFinal)) else None}
       |""".stripMargin
  }

  def strongFullLoopMismatchReport(r: Rexp, s: String, label: String): String = {
    val base = baselineValue(r, s)
    val certified = strongFullCertifiedValue(r, s)
    val finalFull = bdersStrongFullCert(intern(r), s)
    val finalStrong = bdersStrong(intern(r), s)
    val baseFinal = bders(intern(r), s)
    s"""$label
       |regex      = $r
       |input      = $s
       |rsize      = ${rsize(r)}
       |base       = $base
       |certified  = $certified
       |finalFull  = $finalFull
       |finalStrong= $finalStrong
       |fullSize   = ${asize(finalFull)}
       |strongSize = ${asize(finalStrong)}
       |fullShape  = ${ashapeDagSize(finalFull)}
       |baseSize   = ${asize(baseFinal)}
       |fullCounts = ${shortCounts(finalFull)}
       |baseCounts = ${shortCounts(baseFinal)}
       |""".stripMargin
  }

  def regexShrinkCandidates(r: Rexp): List[Rexp] = {
    val atoms = List(ZERO, ONE, CH('a'), CH('b'))
    val structural = r match {
      case ZERO | ONE | CH(_) => Nil
      case ALT(r1, r2) =>
        List(r1, r2) ++
          regexShrinkCandidates(r1).map(ALT(_, r2)) ++
          regexShrinkCandidates(r2).map(ALT(r1, _))
      case SEQ(r1, r2) =>
        List(r1, r2) ++
          regexShrinkCandidates(r1).map(SEQ(_, r2)) ++
          regexShrinkCandidates(r2).map(SEQ(r1, _))
      case STAR(r0) =>
        List(r0) ++ regexShrinkCandidates(r0).map(STAR.apply)
      case NTIMES(r0, n) =>
        List(r0, STAR(r0)) ++
          (0 until n).toList.map(NTIMES(r0, _)) ++
          regexShrinkCandidates(r0).map(NTIMES(_, n))
    }
    (atoms ++ structural).filter(_ != r).distinct.sortBy(rsize)
  }

  def inputShrinkCandidates(s: String): List[String] = {
    val deletes = s.indices.toList.map(i => s.take(i) + s.drop(i + 1))
    val replacements =
      s.indices.toList.flatMap { i =>
        alphabet.map(c => s.updated(i, c)).filter(_ != s)
      }
    (deletes ++ replacements).distinct.sortBy(_.length)
  }

  def shrinkStrongCoreCE(startR: Rexp, startInput: String): (Rexp, String) = {
    @tailrec
    def loop(r: Rexp, s: String): (Rexp, String) = {
      val inputHit = inputShrinkCandidates(s).find(t => strongCoreLoopMismatch(r, t))
      inputHit match {
        case Some(t) => loop(r, t)
        case None =>
          regexShrinkCandidates(r).find(candidate => strongCoreLoopMismatch(candidate, s)) match {
            case Some(candidate) => loop(candidate, s)
            case None => (r, s)
          }
      }
    }
    loop(startR, startInput)
  }

  def shrinkStrongFullCE(startR: Rexp, startInput: String): (Rexp, String) = {
    @tailrec
    def loop(r: Rexp, s: String): (Rexp, String) = {
      val inputHit = inputShrinkCandidates(s).find(t => strongFullLoopMismatch(r, t))
      inputHit match {
        case Some(t) => loop(r, t)
        case None =>
          regexShrinkCandidates(r).find(candidate => strongFullLoopMismatch(candidate, s)) match {
            case Some(candidate) => loop(candidate, s)
            case None => (r, s)
          }
      }
    }
    loop(startR, startInput)
  }

  def shrinkStrongDirectCE(startR: Rexp, startInput: String): (Rexp, String) = {
    @tailrec
    def loop(r: Rexp, s: String): (Rexp, String) = {
      val inputHit = inputShrinkCandidates(s).find(t => strongDirectMismatch(r, t))
      inputHit match {
        case Some(t) => loop(r, t)
        case None =>
          regexShrinkCandidates(r).find(candidate => strongDirectMismatch(candidate, s)) match {
            case Some(candidate) => loop(candidate, s)
            case None => (r, s)
          }
      }
    }
    loop(startR, startInput)
  }

  def shrinkStrongCubicBudgetCE(
      startR: Rexp,
      startInput: String,
      factor: Double,
      minRegexSize: Int
  ): (Rexp, String) = {
    @tailrec
    def loop(r: Rexp, s: String, seen: Set[(Rexp, String)]): (Rexp, String) = {
      val nextSeen = seen + ((r, s))
      val inputHit = inputShrinkCandidates(s)
        .filterNot(t => nextSeen.contains((r, t)))
        .find(t => strongCubicBudgetExceeded(r, t, factor))
      inputHit match {
        case Some(t) => loop(r, t, nextSeen)
        case None =>
          regexShrinkCandidates(r)
            .filterNot(candidate => nextSeen.contains((candidate, s)))
            .filter(candidate => rsize(candidate) >= minRegexSize)
            .find(candidate => strongCubicBudgetExceeded(candidate, s, factor)) match {
            case Some(candidate) => loop(candidate, s, nextSeen)
            case None => (r, s)
          }
      }
    }
    loop(startR, startInput, Set.empty)
  }

  def shrinkStrongMemoDagBudgetCE(
      startR: Rexp,
      startInput: String,
      factor: Double,
      minRegexSize: Int
  ): (Rexp, String) = {
    @tailrec
    def loop(r: Rexp, s: String, seen: Set[(Rexp, String)]): (Rexp, String) = {
      val nextSeen = seen + ((r, s))
      val inputHit = inputShrinkCandidates(s)
        .filterNot(t => nextSeen.contains((r, t)))
        .find(t => strongMemoDagBudgetExceeded(r, t, factor))
      inputHit match {
        case Some(t) => loop(r, t, nextSeen)
        case None =>
          regexShrinkCandidates(r)
            .filterNot(candidate => nextSeen.contains((candidate, s)))
            .filter(candidate => rsize(candidate) >= minRegexSize)
            .find(candidate => strongMemoDagBudgetExceeded(candidate, s, factor)) match {
            case Some(candidate) => loop(candidate, s, nextSeen)
            case None => (r, s)
          }
      }
    }
    loop(startR, startInput, Set.empty)
  }

  def shrinkFinalActiveBudgetCE(
      startR: Rexp,
      startInput: String,
      config: FinalActiveBudgetConfig
  ): (Rexp, String) = {
    @tailrec
    def loop(r: Rexp, s: String, seen: Set[(Rexp, String)]): (Rexp, String) = {
      val nextSeen = seen + ((r, s))
      val inputHit = inputShrinkCandidates(s)
        .filterNot(t => nextSeen.contains((r, t)))
        .find(t => finalActiveBudgetExceeded(r, t, config))
      inputHit match {
        case Some(t) => loop(r, t, nextSeen)
        case None =>
          regexShrinkCandidates(r)
            .filterNot(candidate => nextSeen.contains((candidate, s)))
            .filter(candidate => rsize(candidate) >= config.minRegexSize)
            .find(candidate => finalActiveBudgetExceeded(candidate, s, config)) match {
            case Some(candidate) => loop(candidate, s, nextSeen)
            case None => (r, s)
          }
      }
    }
    loop(startR, startInput, Set.empty)
  }

  def shrinkStrongRowsBridgeCE(startR: Rexp, startInput: String): (Rexp, String) = {
    @tailrec
    def loop(r: Rexp, s: String, seen: Set[(Rexp, String)]): (Rexp, String) = {
      val nextSeen = seen + ((r, s))
      val inputHit = inputShrinkCandidates(s)
        .filterNot(t => nextSeen.contains((r, t)))
        .find(t => strongRowsBridgeCoverageMismatch(r, t))
      inputHit match {
        case Some(t) => loop(r, t, nextSeen)
        case None =>
          regexShrinkCandidates(r)
            .filterNot(candidate => nextSeen.contains((candidate, s)))
            .find(candidate => strongRowsBridgeCoverageMismatch(candidate, s)) match {
            case Some(candidate) => loop(candidate, s, nextSeen)
            case None => (r, s)
          }
      }
    }
    loop(startR, startInput, Set.empty)
  }

  def findStrongDirectValueCounterexample(cases: Int, maxDepth: Int, maxInput: Int, seed: Long): Unit = {
    val rng = new Random(seed)
    var found = false
    var checked = 0
    (0 until cases).foreach { _ =>
      if (!found) {
        checked += 1
        val r = randomRegex(rng, maxDepth)
        val s = randomInput(rng, maxInput)
        if (strongDirectMismatch(r, s)) {
          found = true
          println(strongDirectMismatchReport(r, s, s"direct bsimpStrong POSIX CE before shrinking (seed=$seed case=$checked)"))
          val (shrunkR, shrunkS) = shrinkStrongDirectCE(r, s)
          println(strongDirectMismatchReport(shrunkR, shrunkS, "direct bsimpStrong POSIX CE after greedy shrinking"))
        }
      }
    }
    if (!found) {
      println(s"no direct bsimpStrong POSIX CE found in $checked random cases (depth <= $maxDepth, input length <= $maxInput, seed=$seed)")
    }
  }

  def findStrongCoreCertifiedValueCounterexample(cases: Int, maxDepth: Int, maxInput: Int, seed: Long): Unit = {
    val rng = new Random(seed)
    var found = false
    var checked = 0
    (0 until cases).foreach { _ =>
      if (!found) {
        checked += 1
        val r = randomRegex(rng, maxDepth)
        val s = randomInput(rng, maxInput)
        if (strongCoreLoopMismatch(r, s)) {
          found = true
          println(strongCoreLoopMismatchReport(r, s, s"strong core certified loop CE before shrinking (seed=$seed case=$checked)"))
          val (shrunkR, shrunkS) = shrinkStrongCoreCE(r, s)
          println(strongCoreLoopMismatchReport(shrunkR, shrunkS, "strong core certified loop CE after greedy shrinking"))
        }
      }
    }
    if (!found) {
      println(s"no strong core certified loop CE found in $checked random cases (depth <= $maxDepth, input length <= $maxInput, seed=$seed)")
    }
  }

  def findStrongFullCertifiedValueCounterexample(cases: Int, maxDepth: Int, maxInput: Int, seed: Long): Unit = {
    val rng = new Random(seed)
    var found = false
    var checked = 0
    (0 until cases).foreach { _ =>
      if (!found) {
        checked += 1
        val r = randomRegex(rng, maxDepth)
        val s = randomInput(rng, maxInput)
        if (strongFullLoopMismatch(r, s)) {
          found = true
          println(strongFullLoopMismatchReport(r, s, s"strong full certified loop CE before shrinking (seed=$seed case=$checked)"))
          val (shrunkR, shrunkS) = shrinkStrongFullCE(r, s)
          println(strongFullLoopMismatchReport(shrunkR, shrunkS, "strong full certified loop CE after greedy shrinking"))
        }
      }
    }
    if (!found) {
      println(s"no strong full certified loop CE found in $checked random cases (depth <= $maxDepth, input length <= $maxInput, seed=$seed)")
    }
  }

  def findRawInjectCounterexample(cases: Int, maxDepth: Int, maxInput: Int, seed: Long): Unit = {
    val rng = new Random(seed)
    var found = false
    var checked = 0
    (0 until cases).foreach { _ =>
      if (!found) {
        checked += 1
        val r = randomRegex(rng, maxDepth)
        val s = randomInput(rng, maxInput)
        if (rawInjectLoopMismatch(r, s)) {
          found = true
          println(
            s"""raw inject loop CE (seed=$seed case=$checked)
               |regex     = $r
               |input     = $s
               |rsize     = ${rsize(r)}
               |base      = ${baselineValue(r, s)}
               |rawInject = ${rawInjectCertifiedValue(r, s)}
               |baseSize  = ${asize(bders(intern(r), s))}
               |""".stripMargin
          )
        }
      }
    }
    if (!found) {
      println(s"no raw inject loop CE found in $checked random cases (depth <= $maxDepth, input length <= $maxInput, seed=$seed)")
    }
  }

  def findStrongCubicBudgetCounterexample(
      cases: Int,
      maxDepth: Int,
      maxInput: Int,
      seed: Long,
      factor: Double,
      minRegexSize: Int
  ): Unit = {
    if (factor <= 0.0) {
      throw new IllegalArgumentException("FindStrongCubicBudgetCE requires -StrongCubicFactor / POSIX_SMOKE_STRONG_CUBIC_FACTOR > 0")
    }
    val rng = new Random(seed)
    var found = false
    var checked = 0
    (0 until cases).foreach { _ =>
      if (!found) {
        checked += 1
        val r = randomRegex(rng, maxDepth)
        val s = randomInput(rng, maxInput)
        if (rsize(r) >= minRegexSize && strongCubicBudgetExceeded(r, s, factor)) {
          found = true
          println(strongCubicBudgetReport(r, s, s"strong cubic budget CE before shrinking (seed=$seed case=$checked)", factor))
          val (shrunkR, shrunkS) = shrinkStrongCubicBudgetCE(r, s, factor, minRegexSize)
          println(strongCubicBudgetReport(shrunkR, shrunkS, s"strong cubic budget CE after greedy shrinking (minRegexSize=$minRegexSize)", factor))
        }
      }
    }
    if (!found) {
      println(s"no strong cubic budget CE found in $checked random cases (depth <= $maxDepth, input length <= $maxInput, seed=$seed, factor=$factor, minRegexSize=$minRegexSize)")
    }
  }

  def findStrongMemoDagBudgetCounterexample(
      cases: Int,
      maxDepth: Int,
      maxInput: Int,
      seed: Long,
      factor: Double,
      minRegexSize: Int
  ): Unit = {
    if (factor <= 0.0) {
      throw new IllegalArgumentException("FindStrongMemoDagBudgetCE requires -StrongMemoDagFactor / POSIX_SMOKE_STRONG_MEMO_DAG_FACTOR > 0")
    }
    val rng = new Random(seed)
    var found = false
    var checked = 0
    (0 until cases).foreach { _ =>
      if (!found) {
        checked += 1
        val r = randomRegex(rng, maxDepth)
        val s = randomInput(rng, maxInput)
        if (rsize(r) >= minRegexSize && strongMemoDagBudgetExceeded(r, s, factor)) {
          found = true
          println(strongMemoDagBudgetReport(r, s, s"strong memo DAG budget CE before shrinking (seed=$seed case=$checked)", factor))
          val (shrunkR, shrunkS) = shrinkStrongMemoDagBudgetCE(r, s, factor, minRegexSize)
          println(strongMemoDagBudgetReport(shrunkR, shrunkS, s"strong memo DAG budget CE after greedy shrinking (minRegexSize=$minRegexSize)", factor))
        }
      }
    }
    if (!found) {
      println(s"no strong memo DAG budget CE found in $checked random cases (depth <= $maxDepth, input length <= $maxInput, seed=$seed, factor=$factor, minRegexSize=$minRegexSize)")
    }
  }

  def findFinalActiveBudgetCounterexample(
      cases: Int,
      maxDepth: Int,
      maxInput: Int,
      seed: Long,
    config: FinalActiveBudgetConfig
  ): Unit = {
    if (!config.hasBudget) {
      throw new IllegalArgumentException(
        "FindStrongFinalActiveBudgetCE requires a positive final-active rows, member, member-DAG, member-shape-DAG, row-DAG-universe, component-union, decomp-bound, or pair factor"
      )
    }
    val rng = new Random(seed)
    var found = false
    var checked = 0
    (0 until cases).foreach { _ =>
      if (!found) {
        checked += 1
        val r = randomRegex(rng, maxDepth)
        val s = randomInput(rng, maxInput)
        if (rsize(r) >= config.minRegexSize && finalActiveBudgetExceeded(r, s, config)) {
          found = true
          println(finalActiveBudgetReport(r, s, s"strong final-active budget CE before shrinking (seed=$seed case=$checked)", config))
          val (shrunkR, shrunkS) = shrinkFinalActiveBudgetCE(r, s, config)
          println(finalActiveBudgetReport(shrunkR, shrunkS, s"strong final-active budget CE after greedy shrinking (minRegexSize=${config.minRegexSize})", config))
        }
      }
    }
    if (!found) {
      println(s"no strong final-active budget CE found in $checked random cases (depth <= $maxDepth, input length <= $maxInput, seed=$seed, rowsFactor=${config.rowsFactor}, pairFactor=${config.pairFactor}, memberFactor=${config.memberFactor}, memberDagFactor=${config.memberDagFactor}, memberShapeDagFactor=${config.memberShapeDagFactor}, rowDagUniverseFactor=${config.rowDagUniverseFactor}, componentUnionFactor=${config.componentUnionFactor}, decompBoundFactor=${config.decompBoundFactor}, minRegexSize=${config.minRegexSize})")
    }
  }

  def findStrongRowsBridgeCounterexample(cases: Int, maxDepth: Int, maxInput: Int, seed: Long): Unit = {
    val rng = new Random(seed)
    var found = false
    var checked = 0
    (0 until cases).foreach { _ =>
      if (!found) {
        checked += 1
        val r = randomRegex(rng, maxDepth)
        val s = randomInput(rng, maxInput)
        if (strongRowsBridgeCoverageMismatch(r, s)) {
          found = true
          println(strongRowsBridgeCoverageReport(r, s, s"strong rows bridge CE before shrinking (seed=$seed case=$checked)"))
          val (shrunkR, shrunkS) = shrinkStrongRowsBridgeCE(r, s)
          println(strongRowsBridgeCoverageReport(shrunkR, shrunkS, "strong rows bridge CE after greedy shrinking"))
        }
      }
    }
    if (!found) {
      println(s"no strong rows bridge CE found in $checked random cases (depth <= $maxDepth, input length <= $maxInput, seed=$seed)")
    }
  }

  def checkStrongCoreHandCases(): Unit = {
    val candidates = List(
      "nested nullable star alt" -> STAR(STAR(ALT(STAR(CH('a')), CH('b')))),
      "nullable star alt then a-star" -> SEQ(STAR(ALT(STAR(CH('b')), SEQ(CH('b'), CH('a')))), STAR(CH('a'))),
      "nested nullable seq alt" -> STAR(STAR(ALT(SEQ(STAR(CH('a')), ONE), CH('b')))),
      "nested nullable seq-zero alt" -> STAR(STAR(ALT(SEQ(STAR(SEQ(STAR(CH('a')), ONE)), ONE), CH('b'))))
    )
    val inputs = List("", "a", "b", "ab", "ba", "aba", "bab", "bba", "abab", "abaab", "abaaabab")
    var mismatches = 0
    candidates.foreach { case (name, r) =>
      inputs.foreach { s =>
        val base = baselineValue(r, s)
        val certified = strongCoreCertifiedValue(r, s)
        if (base != certified) {
          mismatches += 1
          println(
            s"""strong core hand CE: $name
               |regex     = $r
               |input     = $s
               |base      = $base
               |certified = $certified
               |coreSize  = ${asize(bdersStrongCore(intern(r), s))}
               |baseSize  = ${asize(bders(intern(r), s))}
               |""".stripMargin
          )
        }
      }
    }
    if (mismatches == 0) println(s"checked ${candidates.length * inputs.length} strong core hand cases without mismatch")
    else throw new AssertionError(s"strong core hand cases found $mismatches mismatch(es)")
  }

  def traceStrongFullKnownCE(): Unit = {
    val hard =
      STAR(STAR(STAR(STAR(
        ALT(
          SEQ(CH('b'), ONE),
          SEQ(
            ALT(SEQ(STAR(CH('a')), CH('a')), ZERO),
            STAR(STAR(STAR(STAR(ONE))))
          )
        )
      ))))
    val baseBody =
      ALT(
        SEQ(CH('b'), ONE),
        SEQ(SEQ(STAR(CH('a')), CH('a')), ONE)
      )
    val candidates = List(
      "hard random CE" -> hard,
      "tail ONE, four stars" -> STAR(STAR(STAR(STAR(baseBody)))),
      "tail ONE, three stars" -> STAR(STAR(STAR(baseBody))),
      "tail ONE, two stars" -> STAR(STAR(baseBody)),
      "tail ONE, one star" -> STAR(baseBody),
      "no trailing ONE, two stars" -> STAR(STAR(ALT(CH('b'), SEQ(STAR(CH('a')), CH('a'))))),
      "no trailing ONE, one star" -> STAR(ALT(CH('b'), SEQ(STAR(CH('a')), CH('a')))),
      "tail STAR(ONE), four stars" -> STAR(STAR(STAR(STAR(
        ALT(SEQ(CH('b'), ONE), SEQ(SEQ(STAR(CH('a')), CH('a')), STAR(ONE)))
      )))),
      "tail STAR(ONE), three stars" -> STAR(STAR(STAR(
        ALT(SEQ(CH('b'), ONE), SEQ(SEQ(STAR(CH('a')), CH('a')), STAR(ONE)))
      )))
    )
    val input = "abbabb"
    candidates.foreach { case (name, r) =>
      var stopped = false
      input.indices.toList.map(i => input.take(i + 1)).foreach { prefix =>
        if (!stopped) {
          val base = baselineValue(r, prefix)
          val full = strongFullCertifiedValue(r, prefix)
          val finalFull = bdersStrongFullCert(intern(r), prefix)
          val mark = if (base == full) "ok" else "CE"
          println(
            s"strong full known $name prefix $mark prefix=$prefix rsize=${rsize(r)} fullSize=${asize(finalFull)} " +
              s"strongSize=${asize(bdersStrong(intern(r), prefix))} baseDefined=${base.isDefined} fullDefined=${full.isDefined}"
          )
          if (base != full) {
            println(strongFullLoopMismatchReport(r, prefix, s"strong full known prefix mismatch: $name"))
            stopped = true
          }
        }
      }
    }
  }

  def intSetting(prop: String, env: String, default: Int): Int =
    sys.props.get(prop)
      .orElse(sys.env.get(env))
      .flatMap(s => scala.util.Try(s.toInt).toOption)
      .getOrElse(default)

  def longSetting(prop: String, env: String, default: Long): Long =
    sys.props.get(prop)
      .orElse(sys.env.get(env))
      .flatMap(s => scala.util.Try(s.toLong).toOption)
      .getOrElse(default)

  def doubleSetting(prop: String, env: String, default: Double): Double =
    sys.props.get(prop)
      .orElse(sys.env.get(env))
      .flatMap(s => scala.util.Try(s.toDouble).toOption)
      .getOrElse(default)

  def stringSetting(prop: String, env: String, default: String): String =
    sys.props.get(prop)
      .orElse(sys.env.get(env))
      .getOrElse(default)

  def stringListSetting(prop: String, env: String, default: List[String]): List[String] =
    stringSetting(prop, env, default.mkString(","))
      .split(",")
      .toList
      .map(_.trim)
      .filter(_.nonEmpty)

  def intListSetting(prop: String, env: String, default: List[Int]): List[Int] =
    stringSetting(prop, env, default.mkString(","))
      .split(",")
      .toList
      .map(_.trim)
      .filter(_.nonEmpty)
      .map(_.toInt)

  def boolSetting(prop: String, env: String, default: Boolean): Boolean =
    stringSetting(prop, env, if (default) "1" else "0").toLowerCase match {
      case "1" | "true" | "yes" | "on" => true
      case "0" | "false" | "no" | "off" => false
      case other => throw new IllegalArgumentException(s"invalid boolean setting $env/$prop=$other")
    }

  lazy val cubicSeqMode: String =
    stringSetting("posix.smoke.seqMode", "POSIX_SMOKE_SEQ_MODE", "full")

  def runSmoke(): Unit = {
    val maxDepth = intSetting("posix.smoke.depth", "POSIX_SMOKE_DEPTH", 2)
    val maxInput = intSetting("posix.smoke.input", "POSIX_SMOKE_INPUT", 3)
    val maxRegexes = intSetting("posix.smoke.maxRegexes", "POSIX_SMOKE_MAX_REGEXES", 100000)
    val randomCases = intSetting("posix.smoke.randomCases", "POSIX_SMOKE_RANDOM_CASES", 0)
    val randomDepth = intSetting("posix.smoke.randomDepth", "POSIX_SMOKE_RANDOM_DEPTH", 5)
    val randomInputMax = intSetting("posix.smoke.randomInput", "POSIX_SMOKE_RANDOM_INPUT", 6)
    val randomSeed = longSetting("posix.smoke.seed", "POSIX_SMOKE_SEED", 20260602L)
    val ch7SizeCsv = stringSetting("posix.smoke.ch7SizeCsv", "POSIX_SMOKE_CH7_SIZE_CSV", "")
    val ch7SizeKs = intListSetting("posix.smoke.ch7SizeKs", "POSIX_SMOKE_CH7_SIZE_KS", List(3, 5, 8))
    val ch7SizeLengths = intListSetting(
      "posix.smoke.ch7SizeLengths",
      "POSIX_SMOKE_CH7_SIZE_LENGTHS",
      (0 to 30).toList
    )
    val ch7SizeMetrics = stringListSetting(
      "posix.smoke.ch7SizeMetrics",
      "POSIX_SMOKE_CH7_SIZE_METRICS",
      List(
        "strongTree",
        "cubicTree",
        "sharedShapeStatePool",
        "langContPruneShapeStatePool"
      )
    )
    val ch7K = intSetting("posix.smoke.ch7K", "POSIX_SMOKE_CH7_K", 5)
    val ch7Lengths = intListSetting("posix.smoke.ch7Lengths", "POSIX_SMOKE_CH7_LENGTHS", List(4, 8, 12, 16, 20))
    val ch7TreeThreshold = intSetting("posix.smoke.ch7TreeThreshold", "POSIX_SMOKE_CH7_TREE_THRESHOLD", 1000)
    val ch7DagThreshold = intSetting("posix.smoke.ch7DagThreshold", "POSIX_SMOKE_CH7_DAG_THRESHOLD", 0)
    val ch7ShapeThreshold = intSetting("posix.smoke.ch7ShapeThreshold", "POSIX_SMOKE_CH7_SHAPE_THRESHOLD", 0)
    val ch7StrongCubicFactor = doubleSetting("posix.smoke.ch7StrongCubicFactor", "POSIX_SMOKE_CH7_STRONG_CUBIC_FACTOR", 0.0)
    val strongCubicFactor = doubleSetting("posix.smoke.strongCubicFactor", "POSIX_SMOKE_STRONG_CUBIC_FACTOR", 0.0)
    val strongCubicMinRegexSize = intSetting("posix.smoke.strongCubicMinRegexSize", "POSIX_SMOKE_STRONG_CUBIC_MIN_REGEX_SIZE", 5)
    val strongCubicTop = intSetting("posix.smoke.strongCubicTop", "POSIX_SMOKE_STRONG_CUBIC_TOP", 1)
    val strongMemoDagFactor = doubleSetting("posix.smoke.strongMemoDagFactor", "POSIX_SMOKE_STRONG_MEMO_DAG_FACTOR", 0.0)
    val strongMemoDagMinRegexSize = intSetting("posix.smoke.strongMemoDagMinRegexSize", "POSIX_SMOKE_STRONG_MEMO_DAG_MIN_REGEX_SIZE", 5)
    val strongFinalActiveRowsFactor = doubleSetting("posix.smoke.strongFinalActiveRowsFactor", "POSIX_SMOKE_STRONG_FINAL_ACTIVE_ROWS_FACTOR", 0.0)
    val strongFinalActivePairFactor = doubleSetting("posix.smoke.strongFinalActivePairFactor", "POSIX_SMOKE_STRONG_FINAL_ACTIVE_PAIR_FACTOR", 0.0)
    val strongFinalActiveMemberFactor = doubleSetting("posix.smoke.strongFinalActiveMemberFactor", "POSIX_SMOKE_STRONG_FINAL_ACTIVE_MEMBER_FACTOR", 0.0)
    val strongFinalActiveMemberDagFactor = doubleSetting("posix.smoke.strongFinalActiveMemberDagFactor", "POSIX_SMOKE_STRONG_FINAL_ACTIVE_MEMBER_DAG_FACTOR", 0.0)
    val strongFinalActiveMemberShapeDagFactor = doubleSetting("posix.smoke.strongFinalActiveMemberShapeDagFactor", "POSIX_SMOKE_STRONG_FINAL_ACTIVE_MEMBER_SHAPE_DAG_FACTOR", 0.0)
    val strongFinalActiveRowDagUniverseFactor = doubleSetting("posix.smoke.strongFinalActiveRowDagUniverseFactor", "POSIX_SMOKE_STRONG_FINAL_ACTIVE_ROW_DAG_UNIVERSE_FACTOR", 0.0)
    val strongFinalActiveComponentUnionFactor = doubleSetting("posix.smoke.strongFinalActiveComponentUnionFactor", "POSIX_SMOKE_STRONG_FINAL_ACTIVE_COMPONENT_UNION_FACTOR", 0.0)
    val strongFinalActiveDecompBoundFactor = doubleSetting("posix.smoke.strongFinalActiveDecompBoundFactor", "POSIX_SMOKE_STRONG_FINAL_ACTIVE_DECOMP_BOUND_FACTOR", 0.0)
    val strongFinalActiveMinRegexSize = intSetting("posix.smoke.strongFinalActiveMinRegexSize", "POSIX_SMOKE_STRONG_FINAL_ACTIVE_MIN_REGEX_SIZE", 5)
    val strongFinalActiveTop = intSetting("posix.smoke.strongFinalActiveTop", "POSIX_SMOKE_STRONG_FINAL_ACTIVE_TOP", 0)
    val strongFinalActiveConfig =
      FinalActiveBudgetConfig(
        strongFinalActiveRowsFactor,
        strongFinalActivePairFactor,
        strongFinalActiveMemberFactor,
        strongFinalActiveMemberDagFactor,
        strongFinalActiveMemberShapeDagFactor,
        strongFinalActiveRowDagUniverseFactor,
        strongFinalActiveComponentUnionFactor,
        strongFinalActiveDecompBoundFactor,
        strongFinalActiveMinRegexSize,
        strongFinalActiveTop
      )
    val sharedStatePoolCubicFactor = doubleSetting("posix.smoke.sharedStatePoolCubicFactor", "POSIX_SMOKE_SHARED_STATE_POOL_CUBIC_FACTOR", 0.0)
    val sharedStatePoolMinRegexSize = intSetting("posix.smoke.sharedStatePoolCubicMinRegexSize", "POSIX_SMOKE_SHARED_STATE_POOL_CUBIC_MIN_REGEX_SIZE", 5)
    val sharedStatePoolTop = intSetting("posix.smoke.sharedStatePoolCubicTop", "POSIX_SMOKE_SHARED_STATE_POOL_CUBIC_TOP", 1)
    val sharedPlateauMaxLength = intSetting("posix.smoke.sharedPlateauMaxLength", "POSIX_SMOKE_SHARED_PLATEAU_MAX_LENGTH", 0)
    val sharedPlateauStep = intSetting("posix.smoke.sharedPlateauStep", "POSIX_SMOKE_SHARED_PLATEAU_STEP", 4)
    val sharedPlateauMetric = stringSetting("posix.smoke.sharedPlateauMetric", "POSIX_SMOKE_SHARED_PLATEAU_METRIC", "shapeStatePool")
    val sharedPlateauRequire = boolSetting("posix.smoke.sharedPlateauRequire", "POSIX_SMOKE_SHARED_PLATEAU_REQUIRE", false)
    val sharedPlateauGrowthTop = intSetting("posix.smoke.sharedPlateauGrowthTop", "POSIX_SMOKE_SHARED_PLATEAU_GROWTH_TOP", 0)
    val sharedPlateauProgress = boolSetting("posix.smoke.sharedPlateauProgress", "POSIX_SMOKE_SHARED_PLATEAU_PROGRESS", false)
    val sharedPlateauMetricOnly = boolSetting("posix.smoke.sharedPlateauMetricOnly", "POSIX_SMOKE_SHARED_PLATEAU_METRIC_ONLY", false)
    val sharedNoReassoc = boolSetting("posix.smoke.sharedNoReassoc", "POSIX_SMOKE_SHARED_NO_REASSOC", false)
    val sharedDirectDag = boolSetting("posix.smoke.sharedDirectDag", "POSIX_SMOKE_SHARED_DIRECT_DAG", false)
    val sharedDirectCompareTree = boolSetting("posix.smoke.sharedDirectCompareTree", "POSIX_SMOKE_SHARED_DIRECT_COMPARE_TREE", false)
    val traceStrong = boolSetting("posix.smoke.traceStrong", "POSIX_SMOKE_TRACE_STRONG", false)
    val checkStrong = boolSetting("posix.smoke.checkStrong", "POSIX_SMOKE_CHECK_STRONG", false)
    val checkStrongDeferred = boolSetting("posix.smoke.checkStrongDeferred", "POSIX_SMOKE_CHECK_STRONG_DEFERRED", false)
    val checkStrongDeferredMemo = boolSetting("posix.smoke.checkStrongDeferredMemo", "POSIX_SMOKE_CHECK_STRONG_DEFERRED_MEMO", false)
    val traceStrongDeferredMemo = boolSetting("posix.smoke.traceStrongDeferredMemo", "POSIX_SMOKE_TRACE_STRONG_DEFERRED_MEMO", false)
    val checkStrongRowsBridge = boolSetting("posix.smoke.checkStrongRowsBridge", "POSIX_SMOKE_CHECK_STRONG_ROWS_BRIDGE", false)
    val requireStrongRowsBridgeCoverage = boolSetting("posix.smoke.requireStrongRowsBridgeCoverage", "POSIX_SMOKE_REQUIRE_STRONG_ROWS_BRIDGE_COVERAGE", false)
    val checkStrongRowsBridgeCh7 = boolSetting("posix.smoke.checkStrongRowsBridgeCh7", "POSIX_SMOKE_CHECK_STRONG_ROWS_BRIDGE_CH7", false)
    val strongRowsBridgeOnlyCh7 = boolSetting("posix.smoke.strongRowsBridgeOnlyCh7", "POSIX_SMOKE_STRONG_ROWS_BRIDGE_ONLY_CH7", false)
    val strongRowsBridgeDag = boolSetting("posix.smoke.strongRowsBridgeDag", "POSIX_SMOKE_STRONG_ROWS_BRIDGE_DAG", false)
    val checkStrongSafe = boolSetting("posix.smoke.checkStrongSafe", "POSIX_SMOKE_CHECK_STRONG_SAFE", false)
    val traceStrongSafe = boolSetting("posix.smoke.traceStrongSafe", "POSIX_SMOKE_TRACE_STRONG_SAFE", false)
    val traceStrongRecon = boolSetting("posix.smoke.traceStrongRecon", "POSIX_SMOKE_TRACE_STRONG_RECON", false)
    val traceStrongCore = boolSetting("posix.smoke.traceStrongCore", "POSIX_SMOKE_TRACE_STRONG_CORE", false)
    val traceStrongCoreLoop = boolSetting("posix.smoke.traceStrongCoreLoop", "POSIX_SMOKE_TRACE_STRONG_CORE_LOOP", false)
    val checkStrongCoreCert = boolSetting("posix.smoke.checkStrongCoreCert", "POSIX_SMOKE_CHECK_STRONG_CORE_CERT", false)
    val checkStrongCoreLoop = boolSetting("posix.smoke.checkStrongCoreLoop", "POSIX_SMOKE_CHECK_STRONG_CORE_LOOP", false)
    val checkStrongFullLoop = boolSetting("posix.smoke.checkStrongFullLoop", "POSIX_SMOKE_CHECK_STRONG_FULL_LOOP", false)
    val traceStrongFullLoop = boolSetting("posix.smoke.traceStrongFullLoop", "POSIX_SMOKE_TRACE_STRONG_FULL_LOOP", false)
    val checkStrongFullKnownCE = boolSetting("posix.smoke.checkStrongFullKnownCE", "POSIX_SMOKE_CHECK_STRONG_FULL_KNOWN_CE", false)
    val findStrongDirectCE = boolSetting("posix.smoke.findStrongDirectCE", "POSIX_SMOKE_FIND_STRONG_DIRECT_CE", false)
    val findStrongCoreCE = boolSetting("posix.smoke.findStrongCoreCE", "POSIX_SMOKE_FIND_STRONG_CORE_CE", false)
    val findStrongFullCE = boolSetting("posix.smoke.findStrongFullCE", "POSIX_SMOKE_FIND_STRONG_FULL_CE", false)
    val findRawInjectCE = boolSetting("posix.smoke.findRawInjectCE", "POSIX_SMOKE_FIND_RAW_INJECT_CE", false)
    val findStrongCubicBudgetCE = boolSetting("posix.smoke.findStrongCubicBudgetCE", "POSIX_SMOKE_FIND_STRONG_CUBIC_BUDGET_CE", false)
    val findStrongMemoDagBudgetCE = boolSetting("posix.smoke.findStrongMemoDagBudgetCE", "POSIX_SMOKE_FIND_STRONG_MEMO_DAG_BUDGET_CE", false)
    val findStrongFinalActiveBudgetCE = boolSetting("posix.smoke.findStrongFinalActiveBudgetCE", "POSIX_SMOKE_FIND_STRONG_FINAL_ACTIVE_BUDGET_CE", false)
    val findStrongRowsBridgeCE = boolSetting("posix.smoke.findStrongRowsBridgeCE", "POSIX_SMOKE_FIND_STRONG_ROWS_BRIDGE_CE", false)
    val checkStrongCoreHand = boolSetting("posix.smoke.checkStrongCoreHand", "POSIX_SMOKE_CHECK_STRONG_CORE_HAND", false)
    val traceStrongFullKnown = boolSetting("posix.smoke.traceStrongFullKnown", "POSIX_SMOKE_TRACE_STRONG_FULL_KNOWN", false)
    val skipLegacyCubic = boolSetting("posix.smoke.skipLegacyCubic", "POSIX_SMOKE_SKIP_LEGACY_CUBIC", false)
    if (!skipLegacyCubic || ch7SizeCsv.nonEmpty || sharedNoReassoc || sharedDirectDag) {
      println(s"bsimpCubic sequence mode: $cubicSeqMode")
    }
    if (ch7SizeCsv.nonEmpty) {
      writeCh7SizeCsv(ch7SizeCsv, ch7SizeKs, ch7SizeLengths, ch7SizeMetrics, cubicSeqMode)
      return
    }
    if (!skipLegacyCubic) {
      checkValuePreservation(maxDepth, maxInput, maxRegexes)
      if (randomCases > 0) {
        checkRandomValuePreservation(randomCases, randomDepth, randomInputMax, randomSeed)
      }
    }
    if (checkStrong) {
      checkStrongValuePreservation(maxDepth, maxInput, maxRegexes)
      if (randomCases > 0) {
        checkStrongRandomValuePreservation(randomCases, randomDepth, randomInputMax, randomSeed)
      }
    }
    if (checkStrongDeferred) {
      checkStrongDeferredValuePreservation(maxDepth, maxInput, maxRegexes)
      if (randomCases > 0) {
        checkStrongDeferredRandomValuePreservation(randomCases, randomDepth, randomInputMax, randomSeed)
      }
    }
    if (checkStrongDeferredMemo) {
      checkStrongDeferredMemoValuePreservation(maxDepth, maxInput, maxRegexes, strongCubicFactor, strongCubicMinRegexSize, strongCubicTop, strongFinalActiveConfig)
      checkStrongDeferredMemoKnownCounterexamples(strongCubicFactor, strongCubicMinRegexSize, strongCubicTop, strongFinalActiveConfig)
      if (randomCases > 0) {
        checkStrongDeferredMemoRandomValuePreservation(randomCases, randomDepth, randomInputMax, randomSeed, strongCubicFactor, strongCubicMinRegexSize, strongCubicTop, strongFinalActiveConfig)
      }
    }
    if (checkStrongRowsBridge) {
      if (!strongRowsBridgeOnlyCh7) {
        checkStrongRowsBridgeValuePreservation(maxDepth, maxInput, maxRegexes, requireStrongRowsBridgeCoverage, strongRowsBridgeDag)
        if (randomCases > 0) {
          checkStrongRowsBridgeRandomValuePreservation(randomCases, randomDepth, randomInputMax, randomSeed, requireStrongRowsBridgeCoverage, strongRowsBridgeDag)
        }
      }
      if (checkStrongRowsBridgeCh7) {
        checkStrongRowsBridgeCh7Trace(ch7K, ch7Lengths, requireStrongRowsBridgeCoverage, strongRowsBridgeDag)
      }
    }
    if (checkStrongSafe) {
      checkStrongSafeValuePreservation(maxDepth, maxInput, maxRegexes)
      if (randomCases > 0) {
        checkStrongSafeRandomValuePreservation(randomCases, randomDepth, randomInputMax, randomSeed)
      }
    }
    if (!skipLegacyCubic) {
      checkCounterexamples()
    }
    if (traceStrongRecon) {
      checkStrongReconstructionSketch()
      checkStrongLocalCertificateLaws()
    }
    if (checkStrongCoreCert) {
      checkStrongCoreCertOnDerivatives(maxDepth, maxInput, maxRegexes)
      if (randomCases > 0) {
        checkStrongCoreCertRandom(randomCases, randomDepth, randomInputMax, randomSeed)
      }
    }
    if (checkStrongCoreLoop) {
      checkStrongCoreCertifiedValuePreservation(maxDepth, maxInput, maxRegexes)
      if (randomCases > 0) {
        checkStrongCoreCertifiedValueRandom(randomCases, randomDepth, randomInputMax, randomSeed)
      }
    }
    if (checkStrongFullLoop) {
      checkStrongFullCertifiedValuePreservation(maxDepth, maxInput, maxRegexes)
      if (randomCases > 0) {
        checkStrongFullCertifiedValueRandom(randomCases, randomDepth, randomInputMax, randomSeed)
      }
    }
    if (checkStrongFullKnownCE) {
      checkStrongFullKnownBoundaryCounterexample()
    }
    if (findStrongDirectCE) {
      findStrongDirectValueCounterexample(math.max(randomCases, 1), randomDepth, randomInputMax, randomSeed)
    }
    if (findStrongCoreCE) {
      findStrongCoreCertifiedValueCounterexample(math.max(randomCases, 1), randomDepth, randomInputMax, randomSeed)
    }
    if (findStrongFullCE) {
      findStrongFullCertifiedValueCounterexample(math.max(randomCases, 1), randomDepth, randomInputMax, randomSeed)
    }
    if (findRawInjectCE) {
      findRawInjectCounterexample(math.max(randomCases, 1), randomDepth, randomInputMax, randomSeed)
    }
    if (findStrongCubicBudgetCE) {
      findStrongCubicBudgetCounterexample(math.max(randomCases, 1), randomDepth, randomInputMax, randomSeed, strongCubicFactor, strongCubicMinRegexSize)
    }
    if (findStrongMemoDagBudgetCE) {
      findStrongMemoDagBudgetCounterexample(math.max(randomCases, 1), randomDepth, randomInputMax, randomSeed, strongMemoDagFactor, strongMemoDagMinRegexSize)
    }
    if (findStrongFinalActiveBudgetCE) {
      findFinalActiveBudgetCounterexample(math.max(randomCases, 1), randomDepth, randomInputMax, randomSeed, strongFinalActiveConfig)
    }
    if (findStrongRowsBridgeCE) {
      findStrongRowsBridgeCounterexample(math.max(randomCases, 1), randomDepth, randomInputMax, randomSeed)
    }
    if (checkStrongCoreHand) {
      checkStrongCoreHandCases()
    }
    if (traceStrongFullKnown) {
      traceStrongFullKnownCE()
    }
    if (traceStrong) {
      checkStrongEvilFamilyTrace(ch7K, ch7Lengths)
    }
    if (traceStrongDeferredMemo) {
      checkStrongDeferredMemoEvilFamilyTrace(
        ch7K,
        ch7Lengths,
        ch7TreeThreshold,
        ch7DagThreshold,
        ch7ShapeThreshold,
        ch7StrongCubicFactor,
        strongCubicMinRegexSize,
        strongCubicTop,
        strongFinalActiveConfig
      )
    }
    if (traceStrongSafe) {
      checkStrongSafeEvilFamilyTrace(ch7K, ch7Lengths)
    }
    if (traceStrongCore) {
      checkStrongCoreEvilFamilyTrace(ch7K, ch7Lengths)
    }
    if (traceStrongCoreLoop) {
      checkStrongCoreLoopSizeTrace(ch7K, ch7Lengths)
    }
    if (traceStrongFullLoop) {
      checkStrongFullLoopSizeTrace(ch7K, ch7Lengths)
    }
    if (!skipLegacyCubic) {
      checkEvilFamilyTrace(ch7K, ch7Lengths, ch7TreeThreshold, ch7DagThreshold, ch7ShapeThreshold)
    }
    if (sharedNoReassoc || sharedDirectDag) {
      checkSharedValuePreservation(
        cubicSeqMode,
        maxDepth,
        maxInput,
        maxRegexes,
        sharedDirectDag,
        sharedDirectCompareTree,
        sharedStatePoolCubicFactor,
        sharedStatePoolMinRegexSize,
        sharedStatePoolTop
      )
      if (randomCases > 0) {
        checkSharedRandomValuePreservation(
          cubicSeqMode,
          randomCases,
          randomDepth,
          randomInputMax,
          randomSeed,
          sharedDirectDag,
          sharedDirectCompareTree,
          sharedStatePoolCubicFactor,
          sharedStatePoolMinRegexSize,
          sharedStatePoolTop
        )
      }
      checkSharedEvilFamilyTrace(
        cubicSeqMode,
        ch7K,
        ch7Lengths,
        ch7DagThreshold,
        ch7ShapeThreshold,
        sharedDirectDag,
        sharedDirectCompareTree,
        sharedStatePoolCubicFactor,
        sharedStatePoolMinRegexSize,
        sharedStatePoolTop
      )
      checkSharedEvilFamilyPlateau(
        cubicSeqMode,
        ch7K,
        sharedPlateauMaxLength,
        sharedPlateauStep,
        sharedPlateauMetric,
        sharedPlateauRequire,
        sharedDirectDag,
        sharedDirectCompareTree,
        sharedStatePoolCubicFactor,
        sharedStatePoolMinRegexSize,
        sharedStatePoolTop,
        sharedPlateauGrowthTop,
        sharedPlateauProgress,
        sharedPlateauMetricOnly
      )
    }
  }

  def main(args: Array[String]): Unit =
    runSmoke()
}
