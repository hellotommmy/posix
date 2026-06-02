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

  final case class StrongDeferredMemoResult(
      value: Option[Val],
      strongTree: Int,
      strongDag: Int,
      strongShapeDag: Int,
      memo: PosixMemoResult
  )

  final case class StrongCubicObservation(
      label: String,
      regex: Rexp,
      input: String,
      regexSize: Int,
      strongTree: Int,
      ratio: Double
  )

  val StrongCubicWorstMinRegexSize = 5

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

  def strongDeferredMemoResult(r: Rexp, input: String): StrongDeferredMemoResult = {
    val finalRegex = bdersStrong(intern(r), input)
    val memo =
      if (bnullable(finalRegex)) posixMemoResult(r, input)
      else PosixMemoResult(None, 0, 0, 0, 0, 0)
    StrongDeferredMemoResult(
      memo.value,
      asize(finalRegex),
      adagSize(finalRegex),
      ashapeDagSize(finalRegex),
      memo
    )
  }

  def strongDeferredMemoValue(r: Rexp, input: String): Option[Val] = {
    strongDeferredMemoResult(r, input).value
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

  def strongerCubicWorst(
      current: Option[StrongCubicObservation],
      next: StrongCubicObservation
  ): Option[StrongCubicObservation] =
    if (next.regexSize < StrongCubicWorstMinRegexSize) current
    else current match {
      case None => Some(next)
      case Some(old) =>
        if (next.ratio > old.ratio || (next.ratio == old.ratio && next.strongTree > old.strongTree)) Some(next)
        else current
    }

  def strongCubicWorstSummary(worst: Option[StrongCubicObservation]): String =
    worst match {
      case None => s"no strong cubic observations with rsize >= $StrongCubicWorstMinRegexSize"
      case Some(w) =>
        f"worst strong cubic ratio=${w.ratio}%.6f label=${w.label} tree=${w.strongTree} rsize=${w.regexSize} input=${w.input} regex=${w.regex}"
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
      treeCubicFactor: Double
  ): Unit = {
    val regexes = regexesUpToDepth(maxDepth, maxRegexes)
    val inputs = stringsUpTo(maxInput)
    var checked = 0
    var worst: Option[StrongCubicObservation] = None
    regexes.foreach { r =>
      inputs.foreach { s =>
        checked += 1
        val b = baselineValue(r, s)
        val result = strongDeferredMemoResult(r, s)
        val deferred = result.value
        checkMemoUniverseBound(r, s, result, s"exhaustive case $checked")
        worst = strongerCubicWorst(worst, strongCubicObservation(r, s, result, s"exhaustive case $checked"))
        checkStrongCubicTreeBudget(r, s, result, s"exhaustive case $checked", treeCubicFactor)
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
    println(s"checked strong memo-deferred POSIX values on $checked regex/input pairs (depth <= $maxDepth, input length <= $maxInput, strongCubicFactor=$treeCubicFactor); ${strongCubicWorstSummary(worst)}")
  }

  def checkStrongDeferredMemoRandomValuePreservation(
      cases: Int,
      maxDepth: Int,
      maxInput: Int,
      seed: Long,
      treeCubicFactor: Double
  ): Unit = {
    val rng = new Random(seed)
    var checked = 0
    var worst: Option[StrongCubicObservation] = None
    (0 until cases).foreach { _ =>
      checked += 1
      val r = randomRegex(rng, maxDepth)
      val s = randomInput(rng, maxInput)
      val b = baselineValue(r, s)
      val result = strongDeferredMemoResult(r, s)
      val deferred = result.value
      checkMemoUniverseBound(r, s, result, s"random seed=$seed case=$checked")
      worst = strongerCubicWorst(worst, strongCubicObservation(r, s, result, s"random seed=$seed case=$checked"))
      checkStrongCubicTreeBudget(r, s, result, s"random seed=$seed case=$checked", treeCubicFactor)
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
    println(s"checked strong memo-deferred POSIX values on $checked random cases (depth <= $maxDepth, input length <= $maxInput, seed=$seed, strongCubicFactor=$treeCubicFactor); ${strongCubicWorstSummary(worst)}")
  }

  def checkStrongDeferredMemoKnownCounterexamples(treeCubicFactor: Double): Unit = {
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
    var worst: Option[StrongCubicObservation] = None
    cases.foreach { case ((name, r), inputs) =>
      inputs.foreach { s =>
        checked += 1
        val base = baselineValue(r, s)
        val result = strongDeferredMemoResult(r, s)
        checkMemoUniverseBound(r, s, result, s"known CE $name input=$s")
        worst = strongerCubicWorst(worst, strongCubicObservation(r, s, result, s"known CE $name input=$s"))
        checkStrongCubicTreeBudget(r, s, result, s"known CE $name input=$s", treeCubicFactor)
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
    println(s"checked strong memo-deferred known CE grid on $checked cases (strongCubicFactor=$treeCubicFactor); ${strongCubicWorstSummary(worst)}")
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

  def checkStrongDeferredMemoEvilFamilyTrace(
      k: Int,
      lengths: List[Int],
      treeThreshold: Int,
      dagThreshold: Int,
      shapeThreshold: Int,
      treeCubicFactor: Double
  ): Unit = {
    val r = thesisCh7Evil(k)
    val rootSize = rsize(r).toLong
    val cubicTreeBound = strongCubicTreeBound(r, treeCubicFactor)
    var worst: Option[StrongCubicObservation] = None
    val trace = lengths.map { n =>
      val input = "a" * n
      val result = strongDeferredMemoResult(r, input)
      worst = strongerCubicWorst(worst, strongCubicObservation(r, input, result, s"Chapter 7 k=$k n=$n"))
      checkMemoUniverseBound(r, input, result, s"Chapter 7 k=$k n=$n")
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
          s"/spanBound=$spanBound" +
          s"/queries=${s.memo.acceptsQueries}+${s.memo.valueQueries}" +
          s"/splits=${s.memo.splitProbes}/splitBound=$splitBound"
      }.mkString(", ") +
      s"; ${strongCubicWorstSummary(worst)}")
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

  def shrinkStrongCubicBudgetCE(startR: Rexp, startInput: String, factor: Double): (Rexp, String) = {
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
            .find(candidate => strongCubicBudgetExceeded(candidate, s, factor)) match {
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

  def findStrongCubicBudgetCounterexample(cases: Int, maxDepth: Int, maxInput: Int, seed: Long, factor: Double): Unit = {
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
        if (strongCubicBudgetExceeded(r, s, factor)) {
          found = true
          println(strongCubicBudgetReport(r, s, s"strong cubic budget CE before shrinking (seed=$seed case=$checked)", factor))
          val (shrunkR, shrunkS) = shrinkStrongCubicBudgetCE(r, s, factor)
          println(strongCubicBudgetReport(shrunkR, shrunkS, "strong cubic budget CE after greedy shrinking", factor))
        }
      }
    }
    if (!found) {
      println(s"no strong cubic budget CE found in $checked random cases (depth <= $maxDepth, input length <= $maxInput, seed=$seed, factor=$factor)")
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
    val ch7StrongCubicFactor = doubleSetting("posix.smoke.ch7StrongCubicFactor", "POSIX_SMOKE_CH7_STRONG_CUBIC_FACTOR", 0.0)
    val strongCubicFactor = doubleSetting("posix.smoke.strongCubicFactor", "POSIX_SMOKE_STRONG_CUBIC_FACTOR", 0.0)
    val sharedNoReassoc = boolSetting("posix.smoke.sharedNoReassoc", "POSIX_SMOKE_SHARED_NO_REASSOC", false)
    val traceStrong = boolSetting("posix.smoke.traceStrong", "POSIX_SMOKE_TRACE_STRONG", false)
    val checkStrong = boolSetting("posix.smoke.checkStrong", "POSIX_SMOKE_CHECK_STRONG", false)
    val checkStrongDeferred = boolSetting("posix.smoke.checkStrongDeferred", "POSIX_SMOKE_CHECK_STRONG_DEFERRED", false)
    val checkStrongDeferredMemo = boolSetting("posix.smoke.checkStrongDeferredMemo", "POSIX_SMOKE_CHECK_STRONG_DEFERRED_MEMO", false)
    val traceStrongDeferredMemo = boolSetting("posix.smoke.traceStrongDeferredMemo", "POSIX_SMOKE_TRACE_STRONG_DEFERRED_MEMO", false)
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
    val checkStrongCoreHand = boolSetting("posix.smoke.checkStrongCoreHand", "POSIX_SMOKE_CHECK_STRONG_CORE_HAND", false)
    val traceStrongFullKnown = boolSetting("posix.smoke.traceStrongFullKnown", "POSIX_SMOKE_TRACE_STRONG_FULL_KNOWN", false)
    val skipLegacyCubic = boolSetting("posix.smoke.skipLegacyCubic", "POSIX_SMOKE_SKIP_LEGACY_CUBIC", false)
    println(s"bsimpCubic sequence mode: $cubicSeqMode")
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
      checkStrongDeferredMemoValuePreservation(maxDepth, maxInput, maxRegexes, strongCubicFactor)
      checkStrongDeferredMemoKnownCounterexamples(strongCubicFactor)
      if (randomCases > 0) {
        checkStrongDeferredMemoRandomValuePreservation(randomCases, randomDepth, randomInputMax, randomSeed, strongCubicFactor)
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
      findStrongCubicBudgetCounterexample(math.max(randomCases, 1), randomDepth, randomInputMax, randomSeed, strongCubicFactor)
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
        ch7StrongCubicFactor
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
