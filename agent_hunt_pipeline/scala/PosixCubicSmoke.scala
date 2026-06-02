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
        s"unknown POSIX_SMOKE_SEQ_MODE=$other; expected full, none, keyed-no-reassoc, expanded-keyed-no-reassoc, reassoc-nonnullable-left, no-reassoc, no-left-one, no-right-one, or zeros-only"
      )
    }

  def eq1Member(r: ARexp, rs: List[ARexp]): Boolean = rs.exists(eq1(r, _))

  def pruneEq1Against(covered: List[ARexp], rs: List[ARexp]): List[ARexp] =
    rs.filterNot(r => eq1Member(r, covered))

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

  sealed trait DNode
  case object DZero extends DNode
  final case class DOne(bs: List[Bit]) extends DNode
  final case class DChar(bs: List[Bit], c: Char) extends DNode
  final case class DSeq(bs: List[Bit], r1: Int, r2: Int) extends DNode
  final case class DAlts(bs: List[Bit], rs: List[Int]) extends DNode
  final case class DStar(bs: List[Bit], r: Int) extends DNode
  final case class DNTimes(bs: List[Bit], r: Int, n: Int) extends DNode

  final class DagStore {
    private val nodes = scala.collection.mutable.ArrayBuffer.empty[DNode]
    private val index = scala.collection.mutable.HashMap.empty[DNode, Int]
    private val derCache = scala.collection.mutable.HashMap.empty[(String, Char, Int), Int]

    def totalSize: Int = nodes.size

    def node(id: Int): DNode = nodes(id)

    def mk(n: DNode): Int =
      index.getOrElseUpdate(n, {
        val id = nodes.length
        nodes += n
        id
      })

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

    def stepWithMode(seqMode: String, c: Char, root: Int): Int =
      derCache.getOrElseUpdate((seqMode, c, root), {
        fromARexp(bsimpCubicWithMode(seqMode, bder(c, toARexp(root))))
      })

    def bdersWithMode(seqMode: String, root: Int, s: String): Int =
      s.foldLeft(root)((acc, c) => stepWithMode(seqMode, c, acc))

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

    private val shapeMemo = scala.collection.mutable.HashMap.empty[Int, String]

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

    def reachableShapeSize(root: Int): Int =
      reachableIds(root).map(shapeKey).size
  }

  final case class SharedResult(
      value: Option[Val],
      treeSize: Int,
      dagSize: Int,
      shapeDagSize: Int,
      poolSize: Int
  )

  def sharedModeResult(seqMode: String, r: Rexp, input: String): SharedResult = {
    val store = new DagStore
    val root0 = store.fromARexp(intern(r))
    val root = store.bdersWithMode(seqMode, root0, input)
    val finalRegex = store.toARexp(root)
    val value = if (bnullable(finalRegex)) decodeBits(r, bmkeps(finalRegex)) else None
    SharedResult(
      value,
      asize(finalRegex),
      store.reachableIds(root).size,
      store.reachableShapeSize(root),
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

  def strongSafeValue(r: Rexp, input: String): Option[Val] =
    blexerValue(r, input, bdersStrongSafe)

  def nullableErasedValue(r: ARexp): Option[Val] =
    if (bnullable(r)) decodeBits(eraseA(r), bmkeps(r)) else None

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

  def checkSharedValuePreservation(seqMode: String, maxDepth: Int, maxInput: Int, maxRegexes: Int): Unit = {
    val regexes = regexesUpToDepth(maxDepth, maxRegexes)
    val inputs = stringsUpTo(maxInput)
    var checked = 0
    regexes.foreach { r =>
      inputs.foreach { s =>
        val b = baselineValue(r, s)
        val shared = sharedModeResult(seqMode, r, s)
        checked += 1
        if (b != shared.value) {
          throw new AssertionError(
            s"""shared $seqMode POSIX value mismatch
               |regex   = $r
               |input   = $s
               |base    = $b
               |shared  = ${shared.value}
               |sizes   = tree=${shared.treeSize}, dag=${shared.dagSize}, shape=${shared.shapeDagSize}, pool=${shared.poolSize}
               |""".stripMargin
          )
        }
      }
    }
    println(s"checked shared $seqMode POSIX values on $checked regex/input pairs (depth <= $maxDepth, input length <= $maxInput)")
  }

  def checkSharedRandomValuePreservation(seqMode: String, cases: Int, maxDepth: Int, maxInput: Int, seed: Long): Unit = {
    val rng = new Random(seed)
    var checked = 0
    (0 until cases).foreach { _ =>
      val r = randomRegex(rng, maxDepth)
      val s = randomInput(rng, maxInput)
      val b = baselineValue(r, s)
      val shared = sharedModeResult(seqMode, r, s)
      checked += 1
      if (b != shared.value) {
        throw new AssertionError(
          s"""shared $seqMode random POSIX value mismatch
             |seed    = $seed
             |case    = $checked
             |regex   = $r
             |input   = $s
             |base    = $b
             |shared  = ${shared.value}
             |sizes   = tree=${shared.treeSize}, dag=${shared.dagSize}, shape=${shared.shapeDagSize}, pool=${shared.poolSize}
             |""".stripMargin
        )
      }
    }
    println(s"checked shared $seqMode random POSIX values on $checked cases (depth <= $maxDepth, input length <= $maxInput, seed=$seed)")
  }

  def checkSharedEvilFamilyTrace(
      seqMode: String,
      k: Int,
      lengths: List[Int],
      dagThreshold: Int,
      shapeThreshold: Int
  ): Unit = {
    val r = thesisCh7Evil(k)
    val trace = lengths.map { n =>
      val out = sharedModeResult(seqMode, r, "a" * n)
      n -> out
    }
    println(s"Chapter 7 k=$k shared $seqMode trace: " +
      trace.map { case (n, out) =>
        s"$n->tree=${out.treeSize}/dag=${out.dagSize}/shape=${out.shapeDagSize}/pool=${out.poolSize}"
      }.mkString(", "))
    trace.foreach { case (n, out) =>
      if (dagThreshold > 0 && out.dagSize >= dagThreshold) {
        throw new AssertionError(s"shared $seqMode DAG threshold failed at n=$n: dag=${out.dagSize} threshold=$dagThreshold")
      }
      if (shapeThreshold > 0 && out.shapeDagSize >= shapeThreshold) {
        throw new AssertionError(s"shared $seqMode shape-DAG threshold failed at n=$n: shape=${out.shapeDagSize} threshold=$shapeThreshold")
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

  def stringSetting(prop: String, env: String, default: String): String =
    sys.props.get(prop)
      .orElse(sys.env.get(env))
      .getOrElse(default)

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
    val ch7K = intSetting("posix.smoke.ch7K", "POSIX_SMOKE_CH7_K", 5)
    val ch7Lengths = intListSetting("posix.smoke.ch7Lengths", "POSIX_SMOKE_CH7_LENGTHS", List(4, 8, 12, 16, 20))
    val ch7TreeThreshold = intSetting("posix.smoke.ch7TreeThreshold", "POSIX_SMOKE_CH7_TREE_THRESHOLD", 1000)
    val ch7DagThreshold = intSetting("posix.smoke.ch7DagThreshold", "POSIX_SMOKE_CH7_DAG_THRESHOLD", 0)
    val ch7ShapeThreshold = intSetting("posix.smoke.ch7ShapeThreshold", "POSIX_SMOKE_CH7_SHAPE_THRESHOLD", 0)
    val sharedNoReassoc = boolSetting("posix.smoke.sharedNoReassoc", "POSIX_SMOKE_SHARED_NO_REASSOC", false)
    val traceStrong = boolSetting("posix.smoke.traceStrong", "POSIX_SMOKE_TRACE_STRONG", false)
    val checkStrong = boolSetting("posix.smoke.checkStrong", "POSIX_SMOKE_CHECK_STRONG", false)
    val checkStrongSafe = boolSetting("posix.smoke.checkStrongSafe", "POSIX_SMOKE_CHECK_STRONG_SAFE", false)
    val traceStrongSafe = boolSetting("posix.smoke.traceStrongSafe", "POSIX_SMOKE_TRACE_STRONG_SAFE", false)
    val traceStrongRecon = boolSetting("posix.smoke.traceStrongRecon", "POSIX_SMOKE_TRACE_STRONG_RECON", false)
    println(s"bsimpCubic sequence mode: $cubicSeqMode")
    checkValuePreservation(maxDepth, maxInput, maxRegexes)
    if (randomCases > 0) {
      checkRandomValuePreservation(randomCases, randomDepth, randomInputMax, randomSeed)
    }
    if (checkStrong) {
      checkStrongValuePreservation(maxDepth, maxInput, maxRegexes)
      if (randomCases > 0) {
        checkStrongRandomValuePreservation(randomCases, randomDepth, randomInputMax, randomSeed)
      }
    }
    if (checkStrongSafe) {
      checkStrongSafeValuePreservation(maxDepth, maxInput, maxRegexes)
      if (randomCases > 0) {
        checkStrongSafeRandomValuePreservation(randomCases, randomDepth, randomInputMax, randomSeed)
      }
    }
    checkCounterexamples()
    if (traceStrongRecon) {
      checkStrongReconstructionSketch()
    }
    if (traceStrong) {
      checkStrongEvilFamilyTrace(ch7K, ch7Lengths)
    }
    if (traceStrongSafe) {
      checkStrongSafeEvilFamilyTrace(ch7K, ch7Lengths)
    }
    checkEvilFamilyTrace(ch7K, ch7Lengths, ch7TreeThreshold, ch7DagThreshold, ch7ShapeThreshold)
    if (sharedNoReassoc) {
      checkSharedValuePreservation(cubicSeqMode, maxDepth, maxInput, maxRegexes)
      if (randomCases > 0) {
        checkSharedRandomValuePreservation(cubicSeqMode, randomCases, randomDepth, randomInputMax, randomSeed)
      }
      checkSharedEvilFamilyTrace(cubicSeqMode, ch7K, ch7Lengths, ch7DagThreshold, ch7ShapeThreshold)
    }
  }

  def main(args: Array[String]): Unit =
    runSmoke()
}
