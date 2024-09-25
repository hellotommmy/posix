// A simple lexer inspired by work of Sulzmann & Lu
//==================================================
//
// Call the test cases with 
//
//   amm lexer.sc small
//   amm lexer.sc fib
//   amm lexer.sc loops
//   amm lexer.sc email
//
//   amm lexer.sc all
import scala.annotation.tailrec

// regular expressions including records
abstract class Rexp 
case object ZERO extends Rexp
case object ONE extends Rexp
case object ANYCHAR extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALTS(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 
case class RECD(x: String, r: Rexp) extends Rexp  
case class NTIMES(n: Int, r: Rexp) extends Rexp
case class OPTIONAL(r: Rexp) extends Rexp
case class NOT(r: Rexp) extends Rexp
                // records for extracting strings or tokens
case class BACKREF(r: Rexp, middle: Rexp, cs: List[Char]) extends Rexp
case class HALF(middle: Rexp, residue: List[Char], repeated_string: String) extends Rexp
case class RESIDUE(cs: List[Char], s: String) extends Rexp

// case class NEGACHAR(c: Char) extends Rexp
  
// values  
abstract class Val
case object Failure extends Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val
case class Rec(x: String, v: Val) extends Val
case class Ntime(vs: List[Val]) extends Val
case class Optionall(v: Val) extends Val
case class Nots(s: String) extends Val
case class BackVal(v1: Val, vmid: Val, repeated_string: String) extends Val



abstract class Bit
case object S extends Bit
case object Z extends Bit
case class STAR_ITERS(cnt: Int) extends Bit
// case case class Backbit(r_bits: Bits, mid_bits: Bits, repeated_string: List[Char]) extends Bit
case class Backbit(repeated_string: String) extends Bit
//needed to more efficiently encode star iterations


type Bits = List[Bit]

abstract class ARexp 
case object AZERO extends ARexp
case class AONE(bs: Bits) extends ARexp
case class ACHAR(bs: Bits, c: Char) extends ARexp
case class AALTS(bs: Bits, rs: List[ARexp]) extends ARexp 
case class ASEQ(bs: Bits, r1: ARexp, r2: ARexp) extends ARexp 
case class ASTAR(bs: Bits, r: ARexp) extends ARexp 
case class ANOT(bs: Bits, r: ARexp) extends ARexp
case class AANYCHAR(bs: Bits) extends ARexp
case class ABACKREF(bs: Bits, r: ARexp, middle: ARexp, requires: List[Char]) extends ARexp
case class AHALF(bs: Bits, middle: ARexp, requires: List[Char], repeated_string: String) extends ARexp
case class ARESIDUE(bs: Bits, requires: List[Char], repeated_string: String) extends ARexp
// case class NEGACHAR(middle: ARexp, cs: List[Char]) extends ARexp

import scala.util.Try
   
// some convenience for typing in regular expressions

def charlist2rexp(s : List[Char]): Rexp = s match {
  case Nil => ONE
  case c::Nil => CHAR(c)
  case c::s => SEQ(CHAR(c), charlist2rexp(s))
}
implicit def string2rexp(s : String) : Rexp = 
  charlist2rexp(s.toList)

implicit def RexpOps(r: Rexp) = new {
  def | (s: Rexp) = ALTS(r, s)
  def % = STAR(r)
  def ~ (s: Rexp) = SEQ(r, s)
  //def ? (r: Rexp) = ALTS(r, "")
}

implicit def stringOps(s: String) = new {
  def | (r: Rexp) = ALTS(s, r)
  def | (r: String) = ALTS(s, r)
  def % = STAR(s)
  def ~ (r: Rexp) = SEQ(s, r)
  def ~ (r: String) = SEQ(s, r)
  def $ (r: Rexp) = RECD(s, r)
  //def ? (r: String) = ALTS(r, "")
}

// extracts a string from a value
def flatten(v: Val) : String = v match {
  case Empty => ""
  case Chr(c) => c.toString
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case Sequ(v1, v2) => flatten(v1) ++ flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString
  case Ntime(vs) => vs.map(flatten).mkString
  case Optionall(v) => flatten(v)
  case Rec(_, v) => flatten(v)
}


// extracts an environment from a value;
// used for tokenising a string
def env(v: Val) : List[(String, String)] = v match {
  case Empty => Nil
  case Chr(c) => Nil
  case Left(v) => env(v)
  case Right(v) => env(v)
  case Sequ(v1, v2) => env(v1) ::: env(v2)
  case Stars(vs) => vs.flatMap(env)
  case Ntime(vs) => vs.flatMap(env)
  case Rec(x, v) => (x, flatten(v))::env(v)
  case Optionall(v) => env(v)
  case Nots(s) => ("Negative", s) :: Nil
}

//if the bitsequence indicates some more characters are still 
//needed to complete the back reference,
//then this regex is not nullable (negative number more chars needed)
// def bsnullable(bs: Bits) : Boolean = bs match {
//   case Nil => true
//   case REQUIRE(_)::bs => false
//   case b::bs => bsnullable(bs)
// }


// The Lexing Rules for the WHILE Language

  // bnullable function: tests whether the aregular 
  // expression can recognise the empty string
def bnullable (r: ARexp) : Boolean = r match {
    case AZERO => false
    case AONE(_) => true
    case ACHAR(_,_) => false
    case AALTS(_, rs) => rs.exists(bnullable)
    case ASEQ(_, r1, r2) => bnullable(r1) && bnullable(r2)
    case ASTAR(_, _) => true
    case ANOT(_, rn) => !bnullable(rn)
    case ABACKREF(bs, r1, rm, cs) => 
      bnullable(r1) && bnullable(rm) && cs.isEmpty
    case AHALF(bs, mid, cs, s) => bnullable(mid) && cs.isEmpty
    case ARESIDUE(bs, cs, s) => cs.isEmpty
    // case ARESIDUE(bs, )
      //also need to make sure cs does not require more characters
  }

// def bmkeps(r: ARexp) : Bits = r match {
//     case AONE(bs) => bs
//     case AALTS(bs, rs) => {
//       val n = rs.indexWhere(bnullable)
//       bs ++ bmkeps(rs(n))
//     }
//     case ASEQ(bs, r1, r2) => bs ++ bmkeps(r1) ++ bmkeps(r2)
//     case ASTAR(bs, r) => bs ++ List(S)
//     case ANOT(bs, rn) => bs
//   }




// def fuse(bs: Bits, r: ARexp) : ARexp = r match {
//     case AZERO => AZERO
//     case AONE(cs) => AONE(bs ++ cs)
//     case ACHAR(cs, f) => ACHAR(bs ++ cs, f)
//     case AALTS(cs, rs) => AALTS(bs ++ cs, rs)
//     case ASEQ(cs, r1, r2) => ASEQ(bs ++ cs, r1, r2)
//     case ASTAR(cs, r) => ASTAR(bs ++ cs, r)
//     case ANOT(cs, r) => ANOT(bs ++ cs, r)
//   }
def fuse(bs: Bits, r: ARexp) : ARexp = r match {
  case AZERO => AZERO
  case AONE(cs) => AONE(cs ++ bs)
  case ACHAR(cs, c) => ACHAR(cs ++ bs, c)
  case AALTS(cs, rs) => AALTS(cs ++ bs, rs)
  case ASEQ(cs, r1, r2) => ASEQ(cs ++ bs, r1, r2)
  case ASTAR(cs, r) => ASTAR(cs ++ bs, r)
  case ABACKREF(bs1, r, mid, required_cs) => ABACKREF(bs1 ++ bs, r, mid, required_cs)
  case AHALF(bs1, mid, required_cs, str) => AHALF(bs1 ++ bs, mid, required_cs, str)
  case ARESIDUE(bs1, required_cs, str) => ARESIDUE(bs1 ++ bs, required_cs, str)
  case _ => println("hello fuse"); AZERO
}
def atomic(r: Rexp) : Boolean = r match {
    case ZERO => true
    case ONE => true
    case CHAR(_) => true
    case ANYCHAR => true
    case _ => false
}
def internalise(r: Rexp) : ARexp = r match {
    case ZERO => AZERO
    case ONE => AONE(Nil)
    case CHAR(c) => ACHAR(Nil, c)
    //case PRED(f) => APRED(Nil, f)
    case ALTS(r1, r2) => 
      AALTS(Nil, List(fuse(List(Z), internalise(r1)), fuse(List(S), internalise(r2))))
    // case ALTS(r1::rs) => {
    //   val AALTS(Nil, rs2) = internalise(ALTS(rs))
    //   AALTS(Nil, fuse(List(S), internalise(r1)) :: rs2.map(fuse(List(Z), _)))
    // }
    case SEQ(r1, r2) => ASEQ(Nil, internalise(r1), internalise(r2))
    case STAR(r) => if(atomic(r)) ASTAR(STAR_ITERS(0)::Nil, internalise(r)) else ASTAR(Nil, internalise(r)) 
    //newEncoding: if STAR has an "atomic" core, then don't store iterations like S,S,S,... (unary format), but
    //use digits to represent number of iterations instead
    case RECD(x, r) => internalise(r)
    case NOT(r) => ANOT(Nil, internalise(r))
    case ANYCHAR => AANYCHAR(Nil)
    case BACKREF(r, rmid, cs) => ABACKREF(Nil, internalise(r), internalise(rmid), cs)
    // case NTIMES(n, r) => ANTIMES(Nil, n, internalise(r))
    case _ => println("hiInternalise");AZERO
}




def flats(rs: List[ARexp]): List[ARexp] = rs match {
    case Nil => Nil
    case AZERO :: rs1 => flats(rs1)
    case AALTS(bs, rs1) :: rs2 => rs1.map(fuse(bs, _)) ::: flats(rs2)
    case r1 :: rs2 => r1 :: flats(rs2)
  }



def distinctBy[B, C](xs: List[B], f: B => C, acc: List[C] = Nil): List[B] = xs match {
  case Nil => Nil
  case (x::xs) => {
    val res = f(x)
    if (acc.contains(res)) distinctBy(xs, f, acc)  
    else x::distinctBy(xs, f, res::acc)
  }
} 


def mkatomic(r: Rexp) : Val = r match {
    case ANYCHAR => Chr('*')
    case CHAR(c) => Chr(c)
    case ONE => Empty
    case r => throw new Exception("mkatomic can't make from " + r)
}

// def decode_aux(r: Rexp, bs: Bits) : (Val, Bits) = (r, bs) match {
//   case (ONE, bs) => (Empty, bs)
//   case (CHAR(f), bs) => (Chr(f), bs)
//   case (ALTS(r1, r2), S::bs1) => {
//       val (v, bs2) = decode_aux(r1, bs1)
//       (Left(v), bs2)
//   }
//   case (ALTS(r1, r2), Z::bs1) => {
//       val (v, bs2) = decode_aux(r2, bs1)
//       (Right(v), bs2)
//   }
//   case (SEQ(r1, r2), bs) => {
//     val (v1, bs1) = decode_aux(r1, bs)
//     val (v2, bs2) = decode_aux(r2, bs1)
//     (Sequ(v1, v2), bs2)
//   }
//   case (STAR(r1), Z::bs) => {
//     val (v, bs1) = decode_aux(r1, bs)
//     //(v)
//     val (Stars(vs), bs2) = decode_aux(STAR(r1), bs1)
//     (Stars(v::vs), bs2)
//   }
//   case (STAR(_), S::bs) => (Stars(Nil), bs)
//   case (RECD(x, r1), bs) => {
//     val (v, bs1) = decode_aux(r1, bs)
//     (Rec(x, v), bs1)
//   }
//   case (NOT(r), bs) => (Nots(r.toString), bs)
// }

// def decode(r: Rexp, bs: Bits) = decode_aux(r, bs) match {
//   case (v, Nil) => v
//   case _ => throw new Exception("Not decodable")
// }

// we first defunctionalize the CPS-version, this is
// inspired by the very nice paper "Defunctionalization at Work"
// by Danvy and Nielsen.

// this is an encoding of the continuation
abstract class RegStack
case object CEMPTY extends RegStack
case class CLEFT(k: RegStack) extends RegStack
case class CRIGHT(k: RegStack) extends RegStack
case class CSEQ1(r: Rexp, k: RegStack) extends RegStack
case class CSEQ2(v: Val, k: RegStack) extends RegStack
case class CSTARS(r: Rexp, vs: List[Val], k: RegStack) extends RegStack
case class CBACKREF(mid: Rexp, repeated_string: String, k: RegStack) extends RegStack
case class CHALF(repeated_string: String, vbeg: Val, k: RegStack) extends RegStack

// def decode3(r: Rexp, bs: Bits, k: RegStack) : (Val, Bits) = {
//   //println(s"decode: $r $bs $k")
//   (r, bs) match {
//   case (ONE, bs) => pop_and_decode(k, Empty, bs)
//   case (CHAR(c), bs) => pop_and_decode(k, Chr(c), bs)
//   case (ALTS(r1, r2), S::bs) => decode3(r1, bs, CLEFT(k))
//   case (ALTS(r1, r2), Z::bs) => decode3(r2, bs, CRIGHT(k))
//   case (SEQ(r1, r2), bs) => decode3(r1, bs, CSEQ1(r2, k))
//   case (STAR(_), Z::bs) => pop_and_decode(k, Stars(Nil), bs) 
//   case (STAR(r1), S::bs) => decode3(r1, bs, CSTARS(r1, Nil, k))
//   case (NTIMES(_, r), bs) => decode3(STAR(r), bs, k)
// }}

// def pop_and_decode(k: RegStack, v: Val, bs: Bits) : (Val, Bits) = {
//   //println(s"pop: $k $v $bs") 
//   k match {
//   case CEMPTY => (v, bs)
//   case CLEFT(rest) => pop_and_decode(rest, Left(v), bs)
//   case CRIGHT(rest) => pop_and_decode(rest, Right(v), bs)
//   case CSEQ1(r2, rest) => decode3(r2, bs, CSEQ2(v, rest))
//   case CSEQ2(v1, rest) => pop_and_decode(rest, Sequ(v1, v), bs)
//   case CSTARS(r1, vs, rest) => bs match {
//     case Z::bs => pop_and_decode(rest, Stars(vs :+ v), bs)
//     case S::bs => decode3(r1, bs, CSTARS(r1, vs :+ v, rest))
//   }
// }}

// now the version above is stack-safe in any other FP language,
// but Scala still does not cooperate because it does not optimise
// mutual recursive function calls; therefore the contortions below
// to twist it into a single function

abstract class Call 
case class Dec(r: Rexp, bs: Bits, k: RegStack) extends Call
case class Pop(k: RegStack, v: Val, bs: Bits) extends Call

@tailrec
def de3(c: Call) : (Val, Bits) = c match {
  case Dec(r: Rexp, bs: Bits, k: RegStack) => {
    (r, bs) match {
    case (ONE, bs) => de3(Pop(k, Empty, bs))
    case (ANYCHAR, bs) => de3(Pop(k, Chr('*'), bs))
    case (CHAR(c), bs) => de3(Pop(k, Chr(c), bs))
    case (ALTS(r1, r2), Z::bs) => de3(Dec(r1, bs, CLEFT(k)))
    case (ALTS(r1, r2), S::bs) => de3(Dec(r2, bs, CRIGHT(k)))
    case (SEQ(r1, r2), bs) => de3(Dec(r1, bs, CSEQ1(r2, k)))
    case (STAR(_), S::bs) => de3(Pop(k, Stars(Nil), bs)) //S for no more
    case (STAR(r1), Z::bs) => de3(Dec(r1, bs, CSTARS(r1, Nil, k)))//Z for more
    //newEncoding: if found new encoding then decode using # of iterations directly
    case (STAR(r1), STAR_ITERS(i)::bs) => if(i > 0) de3(Pop(k, Stars(Nil), bs)) else de3(Pop(k, Stars(Nil), bs))
    //List.fill(i)(mkatomic(r1))
    case (NTIMES(_, r), bs) => de3(Dec(STAR(r), bs, k))
    
    //backref is marked by a backbit, with repeated string s. cs is always Nil
    case (BACKREF(r, mid, cs), Backbit(s) :: bs) => de3(Dec(r, bs, CBACKREF(mid, s, k)))
    // case (HALF(r, mid, cs)) half not yet part of normal Rexp input
    
    }
  }
  case Pop(k: RegStack, v: Val, bs: Bits) => {
    k match {
      case CEMPTY => (v, bs)
      case CLEFT(rest) => de3(Pop(rest, Left(v), bs))
      case CRIGHT(rest) => de3(Pop(rest, Right(v), bs))
      case CSEQ1(r2, rest) => de3(Dec(r2, bs, CSEQ2(v, rest)))
      case CSEQ2(v1, rest) => de3(Pop(rest, Sequ(v1, v), bs))
      case CSTARS(r1, vs, rest) => bs match {
        case S::bs => de3(Pop(rest, Stars(vs :+ v), bs))
        case Z::bs => de3(Dec(r1, bs, CSTARS(r1, vs :+ v, rest)))
        case STAR_ITERS(i)::bs => de3(Pop(rest, Stars(Nil), bs))//List.fill(i)(mkatomic(r1))
        //this should not even be triggered right now because STAR_ITERS only works on
      }
      case CBACKREF(mid, rep_str, rest) => de3(Dec(mid, bs, CHALF(rep_str, v, rest)))
      case CHALF(rep_str, vbeg, rest) => de3(Pop(rest, BackVal(vbeg, v, rep_str), bs))
    }
  }
}

// decoding is now truly tail-recursive

def decode(r: Rexp, bs: Bits) = de3(Dec(r, bs, CEMPTY)) match {
  case (v, Nil) => v
  case (v, bs) => throw new Exception(v.toString+" "+ bs.toString+" in decode")
}

// def decode_aux_new(r: Rexp, bs: Bits) : (Val, Bits) = (r, bs) match {
//   case (ONE, bs) => (Empty, bs)
//   case (CHAR(f), bs) => (Chr(f), bs)
//   case (ALTS(r1, r2), S::bs1) => {
//       val (v, bs2) = decode_aux_new(r1, bs1)
//       (Left(v), bs2)
//   }
//   case (ALTS(r1, r2), Z::bs1) => {
//       val (v, bs2) = decode_aux_new(r2, bs1)
//       (Right(v), bs2)
//   }
//   case (SEQ(r1, r2), bs) => {
//     val (v1, bs1) = decode_aux_new(r1, bs)
//     val (v2, bs2) = decode_aux_new(r2, bs1)
//     (Sequ(v1, v2), bs2)
//   }
//   case (STAR(r1), Z::bs) => {
//     val (v, bs1) = decode_aux_new(r1, bs)
//     //(v)
//     val (Stars(vs), bs2) = decode_aux_new(STAR(r1), bs1)
//     (Stars(v::vs), bs2)
//   }
//   case (STAR(_), S::bs) => (Stars(Nil), bs)
//   case (RECD(x, r1), bs) => {
//     val (v, bs1) = decode_aux_new(r1, bs)
//     (Rec(x, v), bs1)
//   }
//   case (NOT(r), bs) => (Nots(r.toString), bs)
// }

// def decode_new(r: Rexp, bs: Bits) = decode_aux_new(r, bs) match {
//   case (v, Nil) => v
//   case _ => throw new Exception("Not decodable")
// }



  def erase(r:ARexp): Rexp = r match{
    case AZERO => ZERO
    case AONE(_) => ONE
    case ACHAR(bs, c) => CHAR(c)
    case AALTS(bs, Nil) => ZERO
    case AALTS(bs, a::Nil) => erase(a)
    case AALTS(bs, a::as) => ALTS(erase(a), erase(AALTS(bs, as)))
    case ASEQ(bs, r1, r2) => SEQ (erase(r1), erase(r2))
    case ASTAR(cs, r)=> STAR(erase(r))
    case ANOT(bs, r) => NOT(erase(r))
    case AANYCHAR(bs) => ANYCHAR
    case ABACKREF(bs, r, mid, cs) => BACKREF(erase(r), erase(mid), cs)
    case AHALF(bs, mid, cs, s) => HALF(erase(mid), cs, s)
    case ARESIDUE(bs, cs, s) => RESIDUE(cs, s)
  }


def strmkeps(cs: List[Char]) : Bits = cs match {
  case Nil => Nil
}

def bmkeps(r: ARexp) : Bits = r match {
  case AONE(bs) => bs
  case AALTS(bs, r::Nil) => bmkeps(r) ++ bs
  case AALTS(bs, r::rs) =>
    if (bnullable(r)) bmkeps(r) ++ bs else bmkeps(AALTS(bs, rs))
  //case AALTS(bs, r::rs) => {
  //  val n = rs.indexWhere(bnullable)
  //  bmkeps(rs(n)) ++ bs
  //}
  case ASEQ(bs, r1, r2) => bmkeps(r2) ++ bmkeps(r1) ++  bs
  case ASTAR(bs, r) => if(atomic(erase(r))) bs else S::bs//newEncoding: if r is atomic then its lexical info is
  //encoded as "STAR_ITERS(i)", no boundary bit (S) needed

  case ABACKREF(bs, r1, mid, cs) => //use Backbit to mark beginning of a back reference
    bmkeps(mid) ++ bmkeps(r1) ++ (Backbit(cs.reverse.toString) :: bs)
  case AHALF(bs, mid, cs, s) => strmkeps(cs) ++ bmkeps(mid) ++ bs
  case ARESIDUE(bs, cs, s) => strmkeps(cs) ++ bs
}

//*** for Christian: new code starts here
def bder_bsimp_rev(c: Char, r: ARexp) : ARexp = r match {
    case AZERO => AZERO
    case AONE(_) => AZERO
    case ACHAR(bs, f) => if (c == f) AONE(bs) else AZERO
    case AALTS(bs, rs) => distinctBy(flats(rs.map(bder_bsimp_rev(c, _))), erase) match {
      case Nil => AZERO
      case a :: Nil => fuse(bs, a)
      case as => AALTS(bs, as)
    }
    case ASEQ(bs, r1, r2) => 
      if (bnullable(r1)) 
        (bder_bsimp_rev(c, r1), bder_bsimp_rev(c, r2)) match {//this can be implemented as a dB+flats on AALTS(r1ds, r2ds) as well, might need to do both and test which is faster
          case (AZERO, AZERO) => AZERO
          case (AZERO, r2ds) =>  fuse(bs ++ bmkeps(r1), r2ds);
          case (AONE(bs1p), r2ds) => r2ds match {
            case AZERO => fuse(bs ++ bs1p, r2)
            case r2ds => AALTS(bs, fuse(bs1p, r2) :: fuse(bmkeps(r1), r2ds) :: Nil)//r2ds never equal to r2 under erase
          }
          case (r1ds, AZERO) => ASEQ(bs, r1ds, r2) //r1ds not AONE, but r2ds AZERO
          //case (AONE(bsp), r2ds) => AALTS(bs, AONE(bsp), r2ds)
          case (r1ds, r2ds) => distinctBy(ASEQ(Nil, r1ds, r2) :: fuse(bmkeps(r1), r2ds) :: Nil, erase ) match {
            case a::Nil => AALTS(bs, a::Nil)
            case as => AALTS(bs, as)
          }
            // AALTS(bs, :: Nil ) //MIGHT de-duplicate this 2-element list, but not necessary it seems
        }
      else bder_bsimp_rev(c, r1) match {//possible to further avoid computation say ignoring r2 if r1 0
          case AZERO => AZERO
          case AONE(bsp) => fuse(bs++bsp, r2)
          case r1ds => ASEQ(bs, r1ds, r2)
        }
    case ASTAR(bs, r) => bder_bsimp_rev(c, r) match {//possible to further avoid computation say ignoring r2 if r1 0
          case AZERO => AZERO
          case AONE(bsp) => bs match {
            case STAR_ITERS(i) :: bs1 => ASTAR(bsp ++ (STAR_ITERS(i+1) :: bs1), r)//ASTAR(bsp ++ (Z :: bs), r)
            case _ => ASTAR(bsp ++ (Z :: bs), r)//throw new Exception("assertion failure: newEncoding should be used but not in place" + bs + r)
          //this clause is *NOT* a sufficient condition for (atomic(erase(r))) to be true, 
          //example: (a+b)* --> 1.(a+b)*
          }
          case rds => ASEQ(bs, fuse(List(Z), rds), ASTAR(Nil, r))
        }
    case ANOT(bs, rn) => ANOT(bs, bder_bsimp_rev(c, rn))
    case AANYCHAR(bs) => AONE(bs)

    
    //cs just records what extra characters are needed, if the captured expression is derived,
    //a new character c is added to cs, to indicate the re-occurring string needs an extra char
    //note that this is also built in reverse order, and has to be reversed at end of lexing
    case ABACKREF(bs, r1, mid, cs) => if(bnullable(r1)) bder_bsimp_rev(c, r1) match {
        //(r1.mid.r1back)\c = 0.mid.r1back+(mid.r1)\c = (mid.r1back)\c
        //the marker bit Backbit(s) is used to indicate the start location of a back reference,
        //here we put the bit into bitcodes the last chance where such a location can be identified,
        //namely when a backref is turned into its last half.
        case AZERO => val s = cs.reverse.toString; bder_bsimp_rev(c, AHALF(bmkeps(r1) ++ (Backbit(s) :: bs), mid, cs.reverse, s))//rev(rs@rs') = (rev rs')@(rev rs)
        //(r1.mid.r1back)\c = 1.mid.r1back(+c required)+(mid.r1back)\c =
        //mid.r1back(+c required) + (mid.r1back)\c
        case AONE(bsp) => val s = (c::cs).reverse.toString;
          AALTS(bs, List(fuse(Backbit(s) :: Nil, AHALF(bsp, mid, (c::cs).reverse, s)), 
            bder_bsimp_rev(c, fuse(Backbit(cs.reverse.toString) :: Nil, AHALF(bmkeps(r1), mid, cs.reverse, cs.reverse.toString)) ) ))
        case r1c => 
          AALTS(bs, List(ABACKREF(Nil, r1c, mid, c::cs), 
            bder_bsimp_rev(c, fuse(Backbit(cs.reverse.toString) :: Nil, AHALF(bmkeps(r1), mid, cs.reverse, cs.reverse.toString)) )))
      }
      else ABACKREF(bs, bder_bsimp_rev(c, r1), mid, c::cs) //not nullable case
        //when doing derivatives on the captured regular expression, 
        //its repetition is also being derived, consuming the same character c (in the future)

      //for quick experiment I didn't implement any simplifications here. (TODO)
      case AHALF(bs, mid, cs, s) => if (bnullable(mid)) bder_bsimp_rev(c, mid) match {
        case mid_der => cs match {//TODO: this part is unoptimised--need a constructor for last phase of backref matching
          case d::ds => if(d == c) AALTS(bs, List(AHALF(Nil, mid_der, cs, s), 
            ARESIDUE(bmkeps(mid), ds, s) ))
            else AHALF(bs, mid_der, cs, s) //d and c doesn't match, only mid a derivative possibility
          case Nil => AHALF(bs, mid_der, cs, s) //cs empty, only mid a derivative possibility
      }
      }
        else AHALF(bs, bder_bsimp_rev(c, mid), cs, s)
      case ARESIDUE(bs, cs, s) => cs match {
        case d::ds => if(c == d) ARESIDUE(bs, ds, s) else AZERO
        case Nil => AZERO
      }
      
} 

// def bder_rev(c: Char, r: ARexp) : ARexp = r match {
//   case AZERO => AZERO
//   case AONE(_) => AZERO
//   case ACHAR(bs, d) => if (c == d) AONE(bs) else AZERO
//   case AALTS(bs, rs) => AALTS(bs, rs.map(bder_rev(c, _)))
//   case ASEQ(bs, r1, r2) =>
//     if (bnullable(r1)) AALT(bs, ASEQ(Nil, bder_rev(c, r1), r2), fuse(bmkeps(r1), bder_rev(c, r2)))
//     else ASEQ(bs, bder_rev(c, r1), r2)
//   case ASTAR(bs, r) => ASEQ(Z :: bs, bder_rev(c, r), ASTAR(Nil, r))
// }

def bders_simp_compressed(r: ARexp, s: List[Char]) : ARexp = s match {
    case Nil => r
    case c::cs => {val bder_bsimp_rev_res = bder_bsimp_rev(c, r); bders_simp_compressed(bder_bsimp_rev_res, cs) }
}

def blex_simp_compressed(r: ARexp, s: List[Char]) : Option[Bits]= s match {
    case Nil => if (bnullable(r)) Some(bmkeps(r)) else None
    case c::cs => {val bder_bsimp_rev_res = bder_bsimp_rev(c, r); blex_simp_compressed(bder_bsimp_rev_res, cs) }
}
def blexing_simp_compressed(r: Rexp, s: String) : Option[Val] = {
  blex_simp_compressed(internalise(r), s.toList) match {
    case Some(bits) => Some(decode(r, bits.reverse))
    case None => None
  }
}



// println("TEST for a**b")
def time[R](block: => R): R = {
    val t0 = System.nanoTime()
    val result = block    // call-by-name
    val t1 = System.nanoTime()
    println(" " + (t1 - t0)/1e9 + "")
    result
}
val astarstarB: Rexp = STAR(STAR("a"))~("b")
val data_points_x_axis = List.range(0, 4000, 400)
// println("a**b matching aa....a: no decoding needed")
// for (i <- data_points_x_axis) 
//   { print(i); 
//  time { 
//     (blexing_simp_compressed(astarstarB, ("a"*i))) 
//     } 
//   }
println("a**b matching aa....ab: decoding required")
for (i <- data_points_x_axis) 
  { print(i); 
 time { 
    (blexing_simp_compressed(astarstarB, ("a"*i+"b"))) 
    } 
  }
// println(blexing_simp_compressed((astarstarB), "aaab"))

import scala.io.Source
// println("TEST for Twain dataset")

def Twain_iterating_func() : String  = {
    val filename = "Twain_novels.txt"
    val fileHandler = Source.fromFile(filename)
    val strWeNeed = fileHandler.mkString
    //println(strWeNeed.length)
    
    strWeNeed
//     for (line <- Source.fromFile(filename).getText) {
        
// }
}
// Twain	5 ms	20 ms	486 ms	16 ms	3 ms	16 ms
// (?i)Twain	79 ms	124 ms	598 ms	160 ms	73 ms	16 ms
// [a-z]shing	564 ms	997 ms	724 ms	15 ms	113 ms	14 ms
// Huck[a-zA-S]+|Saw[a-zA-S]+

def q_mark(r: Rexp) : Rexp = ALTS(r, ONE)
val any_string = STAR(ANYCHAR)
def sub(r: Rexp) : Rexp = SEQ(any_string, SEQ(r, any_string))

val twain2_regex =  sub(SEQ(q_mark("i"), "Twain"))
val twain1_regex = sub("Twain")


// time  { Twain_iterating_func()}
// val huge_twain_string = Twain_iterating_func()
// val huge_first_100000 = huge_twain_string.take(100000)
// val huge_first_1000000 = huge_twain_string.take(1000000)
// println(huge_first_100000.length)
// time{ blexing_simp_compressed(twain2_regex, huge_twain_string) }
// time{ (blexing_simp_compressed((twain2_regex), huge_first_100000)) }
// time{ (blexing_simp_compressed((twain2_regex), huge_first_1000000)) }
// time{ (blexing_simp_compressed((twain1_regex), huge_twain_string)) }
// println(huge_first_1000000.length)
// time{ (blexing_simp_compressed((twain2_regex), huge_first_1000000))}

// println(internalise(twain2_regex))

println("TEST for 0+a1 and a")
val reg = ALTS(ZERO,SEQ(CHAR('a'),ONE))
val str = "a"
println(blexing_simp_compressed((reg), str))

println("TEST for a* and aa")
val reg2 = STAR("a"|"b") ~ STAR("b")
val str2 = "abb"
println(blexing_simp_compressed(reg2, str2))




//towards html-style opening and closing tags with content
val back_reg = BACKREF(STAR(ANYCHAR), STAR(ANYCHAR), Nil)//BACKREF("tag", "a", "tag")

println(blexing_simp_compressed(back_reg, "weeweeboodwweewee"))
println(blexing_simp_compressed(back_reg, "foo foo"))
println(blexing_simp_compressed(back_reg, "TanTan"))
println(blexing_simp_compressed(back_reg, "oo"))
println(blexing_simp_compressed(back_reg, "tag> table </tag"))


