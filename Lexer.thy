   
theory Lexer
  imports PosixSpec 
begin

section \<open>The Lexer Functions by Sulzmann and Lu  (without simplification)\<close>

(* BACKREF-MIGRATION-TODO (definition augmentation):
   Add mkeps cases for BACKREF4/HALF/RESIDUE in the original lexer. *)
fun 
  mkeps :: "rexp \<Rightarrow> val"
where
  "mkeps(ONE) = Void"
| "mkeps(SEQ r1 r2) = Seq (mkeps r1) (mkeps r2)"
| "mkeps(ALT r1 r2) = (if nullable(r1) then Left (mkeps r1) else Right (mkeps r2))"
| "mkeps(STAR r) = Stars []"
| "mkeps(NTIMES r n) = Stars (replicate n (mkeps r))"
| "mkeps(BACKREF4 r1 r2 r3 r4 cs) =
    Backref4 (mkeps r1) (mkeps r2) (mkeps r3) (mkeps r4) cs"
| "mkeps(HALF r cs rep) = Half (mkeps r) cs rep"
| "mkeps(RESIDUE cs rep) = Residue cs rep"

(* BACKREF-MIGRATION-TODO (definition augmentation, ADMIN APPROVAL REQUIRED):
   Add injval cases for BACKREF4/HALF/RESIDUE directly to the original
   function. Migrate only the useful binjval/ginjval ideas; do not keep
   parallel injectors. *)
fun inj_residue :: "string \<Rightarrow> string \<Rightarrow> char \<Rightarrow> val \<Rightarrow> val"
where
  "inj_residue [] rep c v = Void"
| "inj_residue (d # ds) rep c v =
    (case v of
      Residue ds' rep' \<Rightarrow>
        (if d = c \<and> ds' = ds \<and> rep' = rep then Residue (d # ds) rep else Void)
    | _ \<Rightarrow> Void)"

primrec injval :: "rexp \<Rightarrow> char \<Rightarrow> val \<Rightarrow> val"
where
  "injval ZERO c v = Void"
| "injval ONE c v = Void"
| "injval (CH d) c v = (case v of Void \<Rightarrow> Char d | _ \<Rightarrow> Void)"
| "injval (SEQ r1 r2) c v =
    (case v of
      Seq v1 v2 \<Rightarrow> Seq (injval r1 c v1) v2
    | Left (Seq v1 v2) \<Rightarrow> Seq (injval r1 c v1) v2
    | Right v2 \<Rightarrow> Seq (mkeps r1) (injval r2 c v2)
    | _ \<Rightarrow> Void)"
| "injval (ALT r1 r2) c v =
    (case v of
      Left v1 \<Rightarrow> Left (injval r1 c v1)
    | Right v2 \<Rightarrow> Right (injval r2 c v2)
    | _ \<Rightarrow> Void)"
| "injval (STAR r) c v =
    (case v of Seq v' (Stars vs) \<Rightarrow> Stars ((injval r c v') # vs) | _ \<Rightarrow> Void)"
| "injval (NTIMES r n) c v =
    (case v of Seq v' (Stars vs) \<Rightarrow> Stars ((injval r c v') # vs) | _ \<Rightarrow> Void)"
| "injval (BACKREF4 r1 r2 r3 r4 cs) c v =
    (case v of
      Backref4 v1 v2 v3 v4 cs' \<Rightarrow>
        (if cs' = cs then Backref4 (injval r1 c v1) v2 v3 v4 cs else Void)
    | Left (Backref4 v1 v2 v3 v4 cs') \<Rightarrow>
        (if cs' = cs then Backref4 (injval r1 c v1) v2 v3 v4 cs else Void)
    | Right (Backref4 v1 v2 v3 v4 cs') \<Rightarrow>
        (if cs' = c # cs then Backref4 (mkeps r1) (injval r2 c v2) v3 v4 cs
         else Void)
    | Right (Left (Backref4 v1 v2 v3 v4 cs')) \<Rightarrow>
        (if cs' = c # cs then Backref4 (mkeps r1) (injval r2 c v2) v3 v4 cs
         else Void)
    | Right (Right (Seq v3 (Seq res v4))) \<Rightarrow>
        (case res of
          Residue rs rep \<Rightarrow>
            (if rs = rev cs \<and> rep = rev cs
             then Backref4 (mkeps r1) (mkeps r2) (injval r3 c v3) v4 cs
             else Void)
        | _ \<Rightarrow> Void)
    | Right (Right (Left (Seq v3 (Seq res v4)))) \<Rightarrow>
        (case res of
          Residue rs rep \<Rightarrow>
            (if rs = rev cs \<and> rep = rev cs
             then Backref4 (mkeps r1) (mkeps r2) (injval r3 c v3) v4 cs
             else Void)
        | _ \<Rightarrow> Void)
    | Right (Right (Right (Seq res v4))) \<Rightarrow>
        (case inj_residue (rev cs) (rev cs) c res of
          Residue _ _ \<Rightarrow> Backref4 (mkeps r1) (mkeps r2) (mkeps r3) v4 cs
        | _ \<Rightarrow> Void)
    | Right (Right (Right (Right v4))) \<Rightarrow>
        (if rev cs = []
         then Backref4 (mkeps r1) (mkeps r2) (mkeps r3) (injval r4 c v4) cs
         else Void)
    | _ \<Rightarrow> Void)"
| "injval (HALF r cs rep) c v =
    (case v of
      Half v' cs' rep' \<Rightarrow> Half (injval r c v') cs rep
    | Left (Half v' cs' rep') \<Rightarrow> Half (injval r c v') cs rep
    | Right w \<Rightarrow>
        (case inj_residue cs rep c w of
          Residue _ _ \<Rightarrow> Half (mkeps r) cs rep
        | _ \<Rightarrow> Void)
    | _ \<Rightarrow> Void)"
| "injval (RESIDUE cs rep) c v = inj_residue cs rep c v"

fun 
  lexer :: "rexp \<Rightarrow> string \<Rightarrow> val option"
where
  "lexer r [] = (if nullable r then Some(mkeps r) else None)"
| "lexer r (c#s) = (case (lexer (der c r) s) of  
                    None \<Rightarrow> None
                  | Some(v) \<Rightarrow> Some(injval r c v))"



section \<open>Mkeps, Injval Properties\<close>

(* BACKREF-MIGRATION-TODO (proof constructor-case extension):
   Extend this original lexer value theorem with BACKREF4/HALF/RESIDUE cases. *)
lemma mkeps_flat:
  assumes "nullable(r)" 
  shows "flat (mkeps r) = []"
using assms
  by (induct rule: mkeps.induct) (auto)

lemma Prf_NTimes_empty:
  assumes "\<forall>v \<in> set vs. \<Turnstile> v : r \<and> flat v = []" 
  and     "length vs = n"
  shows "\<Turnstile> Stars vs : NTIMES r n"
  using assms
  by (metis Prf.intros(7) empty_iff eq_Nil_appendI list.set(1))
  

(* BACKREF-MIGRATION-TODO (proof constructor-case extension):
   Extend this original lexer value theorem with BACKREF4/HALF/RESIDUE cases. *)
lemma mkeps_nullable:
  assumes "nullable(r)" 
  shows "\<Turnstile> mkeps r : r"
using assms
  apply (induct rule: mkeps.induct) 
  apply(auto intro: Prf.intros split: if_splits)
  apply (metis Prf.intros(7) append_is_Nil_conv empty_iff list.set(1) list.size(3))
  apply(rule Prf_NTimes_empty)
  apply(auto simp add: mkeps_flat)
  done
 
lemma Prf_der_residue_flat:
  assumes "\<Turnstile> v : der_residue c cs rep"
  shows "cs = c # flat v"
  using assms
  by (cases cs) (auto elim!: Prf_elims split: if_splits)

lemma Prf_RESIDUE_value_shape:
  assumes "\<Turnstile> v : RESIDUE cs rep"
  shows "v = Residue cs rep"
  using assms by (auto elim!: Prf_elims)

lemma Prf_der_residue_value_shape:
  assumes "\<Turnstile> v : der_residue c cs rep"
  obtains ds where "cs = c # ds" "v = Residue ds rep" "flat v = ds"
  using assms
  by (cases cs) (auto elim!: Prf_elims split: if_splits)

lemma Prf_der_residue_inj:
  assumes "\<Turnstile> v : der_residue c cs rep"
  shows "inj_residue cs rep c v = Residue cs rep"
  using assms
  by (cases cs; cases v) (auto elim!: Prf_elims split: if_splits)

lemma Prf_der_residue_unique:
  assumes "\<Turnstile> a : der_residue c cs rep" "\<Turnstile> v : der_residue c cs rep"
  shows "a = v"
  using assms
  by (cases cs; cases a; cases v) (auto elim!: Prf_elims split: if_splits)

lemma Prf_der_residue_inj_flat:
  assumes "\<Turnstile> v : der_residue c cs rep"
  shows "flat (inj_residue cs rep c v) = c # flat v"
  using assms Prf_der_residue_flat Prf_der_residue_inj by simp

lemma Prf_der_residue_inj_Prf:
  assumes "\<Turnstile> v : der_residue c cs rep"
  shows "\<Turnstile> inj_residue cs rep c v : RESIDUE cs rep"
  using assms Prf_der_residue_inj by (simp add: Prf.intros)

lemma Prf_der_residue_half_inj_flat:
  assumes "nullable r" "\<Turnstile> v : der_residue c cs rep"
  shows "flat (case inj_residue cs rep c v of Residue ds rep' \<Rightarrow> Half (mkeps r) cs rep | _ \<Rightarrow> Void) =
    c # flat v"
  using assms Prf_der_residue_flat Prf_der_residue_inj
  by (simp add: mkeps_flat)

lemma Prf_der_residue_half_inj:
  assumes "nullable r" "\<Turnstile> v : der_residue c cs rep"
  shows "\<Turnstile> (case inj_residue cs rep c v of Residue ds rep' \<Rightarrow> Half (mkeps r) cs rep | _ \<Rightarrow> Void) :
    HALF r cs rep"
  using assms Prf_der_residue_inj
  by (auto intro!: Prf.intros mkeps_nullable)

lemma Prf_BACKREF4_value_shape:
  assumes "\<Turnstile> w : BACKREF4 r1 r2 r3 r4 cs"
  obtains v1 v2 v3 v4 where
    "w = Backref4 v1 v2 v3 v4 cs"
    "\<Turnstile> v1 : r1" "\<Turnstile> v2 : r2" "\<Turnstile> v3 : r3" "\<Turnstile> v4 : r4"
  using assms by (auto elim!: Prf_elims)

lemma Prf_BACKREF4_capture_value_shape:
  assumes "\<Turnstile> w : BACKREF4 ONE (der c r2) r3 r4 (c # cs)"
  obtains v2 v3 v4 where
    "w = Backref4 Void v2 v3 v4 (c # cs)"
    "\<Turnstile> v2 : der c r2" "\<Turnstile> v3 : r3" "\<Turnstile> v4 : r4"
  using assms by (auto elim!: Prf_elims)

lemma Prf_BACKREF4_tail3_value_shape:
  assumes "\<Turnstile> w : SEQ (der c r3) (SEQ (RESIDUE (rev cs) (rev cs)) r4)"
  obtains v3 v4 where
    "w = Seq v3 (Seq (Residue (rev cs) (rev cs)) v4)"
    "\<Turnstile> v3 : der c r3" "\<Turnstile> v4 : r4"
  using assms by (auto elim!: Prf_elims)

lemma Prf_BACKREF4_tail_residue_value_shape:
  assumes "\<Turnstile> w : SEQ (der_residue c (rev cs) (rev cs)) r4"
  obtains ds v4 where
    "rev cs = c # ds"
    "w = Seq (Residue ds (rev cs)) v4"
    "cs = rev ds @ [c]"
    "\<Turnstile> v4 : r4"
proof -
  from assms obtain vres v4 where w:
    "w = Seq vres v4" "\<Turnstile> vres : der_residue c (rev cs) (rev cs)" "\<Turnstile> v4 : r4"
    by (auto elim!: Prf_elims)
  then obtain ds where ds:
    "rev cs = c # ds" "vres = Residue ds (rev cs)"
    using Prf_der_residue_value_shape by blast
  then have "cs = rev ds @ [c]"
    by (metis rev.simps(2) rev_rev_ident)
  then show ?thesis
    using that w ds by simp
qed

lemma Prf_BACKREF4_prefix_inj_flat:
  assumes IH: "\<And>v. \<Turnstile> v : der c r1 \<Longrightarrow> flat (injval r1 c v) = c # flat v"
    and p: "\<Turnstile> w : BACKREF4 (der c r1) r2 r3 r4 cs"
  shows "flat (injval (BACKREF4 r1 r2 r3 r4 cs) c w) = c # flat w"
    and "flat (injval (BACKREF4 r1 r2 r3 r4 cs) c (Left w)) = c # flat (Left w)"
  using p by (auto elim!: Prf_elims simp add: IH)

lemma Prf_BACKREF4_capture_inj_flat:
  assumes n1: "nullable r1"
    and IH: "\<And>v. \<Turnstile> v : der c r2 \<Longrightarrow> flat (injval r2 c v) = c # flat v"
    and p: "\<Turnstile> w : BACKREF4 ONE (der c r2) r3 r4 (c # cs)"
  shows "flat (injval (BACKREF4 r1 r2 r3 r4 cs) c (Right w)) = c # flat (Right w)"
    and "flat (injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Left w))) =
      c # flat (Right (Left w))"
  using p n1 by (auto elim!: Prf_elims simp add: IH mkeps_flat)

lemma Prf_BACKREF4_tail3_inj_flat:
  assumes n1: "nullable r1" and n2: "nullable r2"
    and IH: "\<And>v. \<Turnstile> v : der c r3 \<Longrightarrow> flat (injval r3 c v) = c # flat v"
    and p: "\<Turnstile> w : SEQ (der c r3) (SEQ (RESIDUE (rev cs) (rev cs)) r4)"
  shows "flat (injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right w))) =
      c # flat (Right (Right w))"
    and "flat (injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right (Left w)))) =
      c # flat (Right (Right (Left w)))"
  using p n1 n2
  by (auto elim!: Prf_elims simp add: IH mkeps_flat)

lemma Prf_BACKREF4_tail_residue_inj_flat:
  assumes n1: "nullable r1" and n2: "nullable r2" and n3: "nullable r3"
    and p: "\<Turnstile> w : SEQ (der_residue c (rev cs) (rev cs)) r4"
  shows "flat (injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right (Right w)))) =
    c # flat (Right (Right (Right w)))"
proof -
  from p obtain v1 v2 where w:
    "w = Seq v1 v2" "\<Turnstile> v1 : der_residue c (rev cs) (rev cs)" "\<Turnstile> v2 : r4"
    by (auto elim!: Prf_elims)
  then have rev_cs: "rev cs = c # flat v1"
    using Prf_der_residue_flat by blast
  have residue: "inj_residue (rev cs) (rev cs) c v1 = Residue (rev cs) (rev cs)"
    using w(2) by (rule Prf_der_residue_inj)
  have cs: "cs = rev (flat v1) @ [c]"
    using rev_cs by (metis rev.simps(2) rev_rev_ident)
  show ?thesis
    using w n1 n2 n3 rev_cs residue cs by (simp add: mkeps_flat)
qed

lemma Prf_BACKREF4_tail4_inj_flat:
  assumes n1: "nullable r1" and n2: "nullable r2" and n3: "nullable r3"
    and empty: "rev cs = []"
    and IH: "\<And>v. \<Turnstile> v : der c r4 \<Longrightarrow> flat (injval r4 c v) = c # flat v"
    and p: "\<Turnstile> w : der c r4"
  shows "flat (injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right (Right (Right w))))) =
    c # flat (Right (Right (Right (Right w))))"
  using p n1 n2 n3 empty
  by (auto simp add: IH mkeps_flat)

lemma Prf_BACKREF4_prefix_inj:
  assumes IH: "\<And>v. \<Turnstile> v : der c r1 \<Longrightarrow> \<Turnstile> injval r1 c v : r1"
    and p: "\<Turnstile> w : BACKREF4 (der c r1) r2 r3 r4 cs"
  shows "\<Turnstile> injval (BACKREF4 r1 r2 r3 r4 cs) c w : BACKREF4 r1 r2 r3 r4 cs"
    and "\<Turnstile> injval (BACKREF4 r1 r2 r3 r4 cs) c (Left w) :
      BACKREF4 r1 r2 r3 r4 cs"
  using p by (auto intro!: Prf.intros elim!: Prf_elims simp add: IH)

lemma Prf_BACKREF4_capture_inj:
  assumes n1: "nullable r1"
    and IH: "\<And>v. \<Turnstile> v : der c r2 \<Longrightarrow> \<Turnstile> injval r2 c v : r2"
    and p: "\<Turnstile> w : BACKREF4 ONE (der c r2) r3 r4 (c # cs)"
  shows "\<Turnstile> injval (BACKREF4 r1 r2 r3 r4 cs) c (Right w) :
      BACKREF4 r1 r2 r3 r4 cs"
    and "\<Turnstile> injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Left w)) :
      BACKREF4 r1 r2 r3 r4 cs"
  using p n1 by (auto intro!: Prf.intros mkeps_nullable elim!: Prf_elims simp add: IH)

lemma Prf_BACKREF4_tail3_inj:
  assumes n1: "nullable r1" and n2: "nullable r2"
    and IH: "\<And>v. \<Turnstile> v : der c r3 \<Longrightarrow> \<Turnstile> injval r3 c v : r3"
    and p: "\<Turnstile> w : SEQ (der c r3) (SEQ (RESIDUE (rev cs) (rev cs)) r4)"
  shows "\<Turnstile> injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right w)) :
      BACKREF4 r1 r2 r3 r4 cs"
    and "\<Turnstile> injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right (Left w))) :
      BACKREF4 r1 r2 r3 r4 cs"
  using p n1 n2 by (auto intro!: Prf.intros mkeps_nullable elim!: Prf_elims simp add: IH)

lemma Prf_BACKREF4_tail_residue_inj:
  assumes n1: "nullable r1" and n2: "nullable r2" and n3: "nullable r3"
    and p: "\<Turnstile> w : SEQ (der_residue c (rev cs) (rev cs)) r4"
  shows "\<Turnstile> injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right (Right w))) :
    BACKREF4 r1 r2 r3 r4 cs"
proof -
  from p obtain vres v4 where w:
    "w = Seq vres v4" "\<Turnstile> vres : der_residue c (rev cs) (rev cs)" "\<Turnstile> v4 : r4"
    by (auto elim!: Prf_elims)
  have residue: "inj_residue (rev cs) (rev cs) c vres = Residue (rev cs) (rev cs)"
    using w(2) by (rule Prf_der_residue_inj)
  show ?thesis
    using w residue n1 n2 n3 by (auto intro!: Prf.intros mkeps_nullable)
qed

lemma Prf_BACKREF4_tail4_inj:
  assumes n1: "nullable r1" and n2: "nullable r2" and n3: "nullable r3"
    and empty: "rev cs = []"
    and IH: "\<And>v. \<Turnstile> v : der c r4 \<Longrightarrow> \<Turnstile> injval r4 c v : r4"
    and p: "\<Turnstile> w : der c r4"
  shows "\<Turnstile> injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right (Right (Right w)))) :
    BACKREF4 r1 r2 r3 r4 cs"
  using p n1 n2 n3 empty
  by (auto intro!: Prf.intros mkeps_nullable simp add: IH)

(* BACKREF-MIGRATION-TODO (proof constructor-case extension):
   Extend this original lexer value theorem with BACKREF4/HALF/RESIDUE cases. *)
lemma Prf_injval_flat:
  assumes "\<Turnstile> v : der c r" 
  shows "flat (injval r c v) = c # (flat v)"
  using assms
proof (induct r arbitrary: c v)
  case ZERO
  then show ?case by (auto elim!: Prf_elims)
next
  case ONE
  then show ?case by (auto elim!: Prf_elims)
next
  case (CH x)
  then show ?case by (auto elim!: Prf_elims split: if_splits)
next
  case (SEQ r1 r2)
  then show ?case
    by (auto elim!: Prf_elims simp add: mkeps_flat split: if_splits)
next
  case (ALT r1 r2)
  then show ?case by (auto elim!: Prf_elims)
next
  case (STAR r)
  then show ?case by (auto elim!: Prf_elims)
next
  case (NTIMES r n)
  then show ?case
  proof (cases n)
    case 0
    then show ?thesis
      using NTIMES.prems by (auto elim!: Prf_elims)
  next
    case (Suc m)
    then obtain v' vs where v:
      "v = Seq v' (Stars vs)" "\<Turnstile> v' : der c r"
      using NTIMES.prems by (auto elim!: Prf_elims)
    then show ?thesis
      using NTIMES.hyps by simp
  qed
next
  case (BACKREF4 r1 r2 r3 r4 cs)
  let ?prefix = "BACKREF4 (der c r1) r2 r3 r4 cs"
  let ?capture = "BACKREF4 ONE (der c r2) r3 r4 (c # cs)"
  let ?res = "rev cs"
  let ?mid = "SEQ (RESIDUE ?res ?res) r4"
  let ?res_tail =
    "if ?res = []
     then ALT (SEQ (der_residue c ?res ?res) r4) (der c r4)
     else SEQ (der_residue c ?res ?res) r4"
  let ?tail =
    "if nullable r3
     then ALT (SEQ (der c r3) ?mid) ?res_tail
     else SEQ (der c r3) ?mid"
  let ?rest = "if nullable r2 then ALT ?capture ?tail else ?capture"
  have prem: "\<Turnstile> v : der c (BACKREF4 r1 r2 r3 r4 cs)"
    by fact
  show ?case
  proof (cases "nullable r1")
    case False
    then have p: "\<Turnstile> v : ?prefix"
      using prem by (simp add: Let_def)
    show ?thesis
      using Prf_BACKREF4_prefix_inj_flat(1)[OF BACKREF4.hyps(1) p] .
  next
    case n1: True
    then have alt1: "\<Turnstile> v : ALT ?prefix ?rest"
      using prem by (simp add: Let_def)
    then consider
      (prefix) w where "v = Left w" "\<Turnstile> w : ?prefix"
    | (rest) w where "v = Right w" "\<Turnstile> w : ?rest"
      by (erule Prf_elims) auto
    then show ?thesis
    proof cases
      case prefix
      then show ?thesis
        using Prf_BACKREF4_prefix_inj_flat(2)[OF BACKREF4.hyps(1) prefix(2)] by simp
    next
      case (rest w)
      show ?thesis
      proof (cases "nullable r2")
        case False
        then have cap: "\<Turnstile> w : ?capture"
          using rest by simp
        then show ?thesis
          using rest Prf_BACKREF4_capture_inj_flat(1)[OF n1 BACKREF4.hyps(2) cap] by simp
      next
        case n2: True
        then have alt2: "\<Turnstile> w : ALT ?capture ?tail"
          using rest by simp
        then consider
          (capture) wc where "w = Left wc" "\<Turnstile> wc : ?capture"
        | (tail) wt where "w = Right wt" "\<Turnstile> wt : ?tail"
          by (erule Prf_elims) auto
        then show ?thesis
        proof cases
          case capture
          then show ?thesis
            using rest Prf_BACKREF4_capture_inj_flat(2)[OF n1 BACKREF4.hyps(2) capture(2)]
            by simp
        next
          case (tail wt)
          show ?thesis
          proof (cases "nullable r3")
            case False
            then have p: "\<Turnstile> wt : SEQ (der c r3) ?mid"
              using tail by simp
            then show ?thesis
              using rest tail Prf_BACKREF4_tail3_inj_flat(1)[OF n1 n2 BACKREF4.hyps(3) p]
              by simp
          next
            case n3: True
            then have alt3: "\<Turnstile> wt : ALT (SEQ (der c r3) ?mid) ?res_tail"
              using tail by simp
            then consider
              (tail3) w3 where "wt = Left w3" "\<Turnstile> w3 : SEQ (der c r3) ?mid"
            | (residue) wr where "wt = Right wr" "\<Turnstile> wr : ?res_tail"
              by (erule Prf_elims) auto
            then show ?thesis
            proof cases
              case tail3
              then show ?thesis
                using rest tail Prf_BACKREF4_tail3_inj_flat(2)[OF n1 n2 BACKREF4.hyps(3) tail3(2)]
                by simp
            next
              case (residue wr)
              show ?thesis
              proof (cases "?res")
                case Nil
                then have alt4: "\<Turnstile> wr : ALT (SEQ (der_residue c ?res ?res) r4) (der c r4)"
                  using residue by simp
                then consider
                  (impossible) wi where "wr = Left wi" "\<Turnstile> wi : SEQ (der_residue c ?res ?res) r4"
                | (tail4) w4 where "wr = Right w4" "\<Turnstile> w4 : der c r4"
                  by (erule Prf_elims) auto
                then show ?thesis
                proof cases
                  case impossible
                  then show ?thesis
                    using Nil by (auto elim!: Prf_elims)
                next
                  case tail4
                  then show ?thesis
                    using rest tail residue Nil
                      Prf_BACKREF4_tail4_inj_flat[OF n1 n2 n3 Nil BACKREF4.hyps(4) tail4(2)]
                    by simp
                qed
              next
                case (Cons a list)
                then have p: "\<Turnstile> wr : SEQ (der_residue c ?res ?res) r4"
                  using residue by simp
                then show ?thesis
                  using rest tail residue
                    Prf_BACKREF4_tail_residue_inj_flat[OF n1 n2 n3 p]
                  by simp
              qed
            qed
          qed
        qed
      qed
    qed
  qed
next
  case (HALF r cs rep)
  show ?case
  proof (cases "nullable r")
    case False
    then obtain v0 where v: "v = Half v0 cs rep" and p: "\<Turnstile> v0 : der c r"
      using HALF.prems by (auto elim!: Prf_elims)
    then show ?thesis
      using HALF.hyps by simp
  next
    case True
    then have alt: "\<Turnstile> v : ALT (HALF (der c r) cs rep) (der_residue c cs rep)"
      using HALF.prems by simp
    then consider
      (left) v0 where "v = Left (Half v0 cs rep)" "\<Turnstile> v0 : der c r"
    | (right) vr where "v = Right vr" "\<Turnstile> vr : der_residue c cs rep"
      by (auto elim!: Prf_elims)
    then show ?thesis
    proof cases
      case left
      then show ?thesis
        using HALF.hyps by simp
    next
      case right
      then show ?thesis
        using True Prf_der_residue_half_inj_flat by simp
    qed
  qed
next
  case (RESIDUE cs rep)
  then show ?case
    by (simp add: Prf_der_residue_inj_flat)
qed

(* BACKREF-MIGRATION-TODO (proof constructor-case extension):
   Extend this original lexer value theorem with BACKREF4/HALF/RESIDUE cases. *)
lemma Prf_injval:
  assumes "\<Turnstile> v : der c r" 
  shows "\<Turnstile> (injval r c v) : r"
  using assms
proof (induct r arbitrary: c v)
  case ZERO
  then show ?case by (auto elim!: Prf_elims)
next
  case ONE
  then show ?case by (auto elim!: Prf_elims)
next
  case (CH x)
  then show ?case by (auto intro!: Prf.intros elim!: Prf_elims split: if_splits)
next
  case (SEQ r1 r2)
  then show ?case
    by (auto intro!: Prf.intros mkeps_nullable elim!: Prf_elims
      simp add: Prf_injval_flat split: if_splits)
next
  case (ALT r1 r2)
  then show ?case
    by (auto intro!: Prf.intros elim!: Prf_elims)
next
  case (STAR r)
  then show ?case
    by (auto intro!: Prf.intros elim!: Prf_elims simp add: Prf_injval_flat)
next
  case (NTIMES r n)
  then show ?case
    apply (cases n)
     apply (auto elim!: Prf_elims simp add: Prf_injval_flat)
    apply (subst append.simps(2)[symmetric])
    apply (rule Prf.intros)
      apply (metis Prf_injval_flat list.distinct(1) set_ConsD)
     apply blast
    apply simp
    done
next
  case (BACKREF4 r1 r2 r3 r4 cs)
  let ?prefix = "BACKREF4 (der c r1) r2 r3 r4 cs"
  let ?capture = "BACKREF4 ONE (der c r2) r3 r4 (c # cs)"
  let ?res = "rev cs"
  let ?mid = "SEQ (RESIDUE ?res ?res) r4"
  let ?res_tail =
    "if ?res = []
     then ALT (SEQ (der_residue c ?res ?res) r4) (der c r4)
     else SEQ (der_residue c ?res ?res) r4"
  let ?tail =
    "if nullable r3
     then ALT (SEQ (der c r3) ?mid) ?res_tail
     else SEQ (der c r3) ?mid"
  let ?rest = "if nullable r2 then ALT ?capture ?tail else ?capture"
  have prem: "\<Turnstile> v : der c (BACKREF4 r1 r2 r3 r4 cs)"
    by fact
  show ?case
  proof (cases "nullable r1")
    case False
    then have p: "\<Turnstile> v : ?prefix"
      using prem by (simp add: Let_def)
    show ?thesis
      using Prf_BACKREF4_prefix_inj(1)[OF BACKREF4.hyps(1) p] .
  next
    case n1: True
    then have alt1: "\<Turnstile> v : ALT ?prefix ?rest"
      using prem by (simp add: Let_def)
    then consider
      (prefix) w where "v = Left w" "\<Turnstile> w : ?prefix"
    | (rest) w where "v = Right w" "\<Turnstile> w : ?rest"
      by (erule Prf_elims) auto
    then show ?thesis
    proof cases
      case prefix
      then show ?thesis
        using Prf_BACKREF4_prefix_inj(2)[OF BACKREF4.hyps(1) prefix(2)] by simp
    next
      case (rest w)
      show ?thesis
      proof (cases "nullable r2")
        case False
        then have cap: "\<Turnstile> w : ?capture"
          using rest by simp
        then show ?thesis
          using rest Prf_BACKREF4_capture_inj(1)[OF n1 BACKREF4.hyps(2) cap] by simp
      next
        case n2: True
        then have alt2: "\<Turnstile> w : ALT ?capture ?tail"
          using rest by simp
        then consider
          (capture) wc where "w = Left wc" "\<Turnstile> wc : ?capture"
        | (tail) wt where "w = Right wt" "\<Turnstile> wt : ?tail"
          by (erule Prf_elims) auto
        then show ?thesis
        proof cases
          case capture
          then show ?thesis
            using rest Prf_BACKREF4_capture_inj(2)[OF n1 BACKREF4.hyps(2) capture(2)]
            by simp
        next
          case (tail wt)
          show ?thesis
          proof (cases "nullable r3")
            case False
            then have p: "\<Turnstile> wt : SEQ (der c r3) ?mid"
              using tail by simp
            then show ?thesis
              using rest tail Prf_BACKREF4_tail3_inj(1)[OF n1 n2 BACKREF4.hyps(3) p]
              by simp
          next
            case n3: True
            then have alt3: "\<Turnstile> wt : ALT (SEQ (der c r3) ?mid) ?res_tail"
              using tail by simp
            then consider
              (tail3) w3 where "wt = Left w3" "\<Turnstile> w3 : SEQ (der c r3) ?mid"
            | (residue) wr where "wt = Right wr" "\<Turnstile> wr : ?res_tail"
              by (erule Prf_elims) auto
            then show ?thesis
            proof cases
              case tail3
              then show ?thesis
                using rest tail Prf_BACKREF4_tail3_inj(2)[OF n1 n2 BACKREF4.hyps(3) tail3(2)]
                by simp
            next
              case (residue wr)
              show ?thesis
              proof (cases "?res")
                case Nil
                then have alt4: "\<Turnstile> wr : ALT (SEQ (der_residue c ?res ?res) r4) (der c r4)"
                  using residue by simp
                then consider
                  (impossible) wi where "wr = Left wi" "\<Turnstile> wi : SEQ (der_residue c ?res ?res) r4"
                | (tail4) w4 where "wr = Right w4" "\<Turnstile> w4 : der c r4"
                  by (erule Prf_elims) auto
                then show ?thesis
                proof cases
                  case impossible
                  then show ?thesis
                    using Nil by (auto elim!: Prf_elims)
                next
                  case tail4
                  then show ?thesis
                    using rest tail residue Nil
                      Prf_BACKREF4_tail4_inj[OF n1 n2 n3 Nil BACKREF4.hyps(4) tail4(2)]
                    by simp
                qed
              next
                case (Cons a list)
                then have p: "\<Turnstile> wr : SEQ (der_residue c ?res ?res) r4"
                  using residue by simp
                then show ?thesis
                  using rest tail residue
                    Prf_BACKREF4_tail_residue_inj[OF n1 n2 n3 p]
                  by simp
              qed
            qed
          qed
        qed
      qed
    qed
  qed
next
  case (HALF r cs rep)
  show ?case
  proof (cases "nullable r")
    case False
    then obtain v0 where v: "v = Half v0 cs rep" and p: "\<Turnstile> v0 : der c r"
      using HALF.prems by (auto elim!: Prf_elims)
    then show ?thesis
      using HALF.hyps by (auto intro!: Prf.intros)
  next
    case True
    then have alt: "\<Turnstile> v : ALT (HALF (der c r) cs rep) (der_residue c cs rep)"
      using HALF.prems by simp
    then consider
      (left) v0 where "v = Left (Half v0 cs rep)" "\<Turnstile> v0 : der c r"
    | (right) vr where "v = Right vr" "\<Turnstile> vr : der_residue c cs rep"
      by (auto elim!: Prf_elims)
    then show ?thesis
    proof cases
      case left
      then show ?thesis
        using HALF.hyps by (auto intro!: Prf.intros)
    next
      case right
      then show ?thesis
        using True Prf_der_residue_half_inj by simp
    qed
  qed
next
  case (RESIDUE cs rep)
  then show ?case
    by (simp add: Prf_der_residue_inj_Prf)
qed

text \<open>Mkeps and injval produce, or preserve, Posix values.\<close>


(* BACKREF-MIGRATION-TODO (proof constructor-case extension):
   Extend nullable POSIX construction for BACKREF4/HALF/RESIDUE. *)
lemma Posix_mkeps:
  assumes "nullable r"
  shows "[] \<in> r \<rightarrow> mkeps r"
  using assms
proof (induct r)
  case ZERO
  then show ?case by simp
next
  case ONE
  then show ?case by (simp add: Posix_ONE)
next
  case (CH x)
  then show ?case by simp
next
  case (SEQ r1 r2)
  then have r1: "[] \<in> r1 \<rightarrow> mkeps r1" and r2: "[] \<in> r2 \<rightarrow> mkeps r2"
    by simp_all
  have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = [] \<and>
      ([] @ s\<^sub>3) \<in> L r1 \<and> s\<^sub>4 \<in> L r2)"
    by simp
  then show ?case
    using Posix_SEQ[OF r1 r2] by simp
next
  case (ALT r1 r2)
  show ?case
  proof (cases "nullable r1")
    case True
    then show ?thesis
      using ALT.hyps(1) by (simp add: Posix_ALT1)
  next
    case False
    then have "[] \<in> r2 \<rightarrow> mkeps r2"
      using ALT by simp
    moreover have "[] \<notin> L r1"
      using False nullable_correctness by blast
    ultimately show ?thesis
      using False by (simp add: Posix_ALT2)
  qed
next
  case (STAR r)
  then show ?case by (simp add: Posix_STAR2)
next
  case (NTIMES r n)
  show ?case
  proof (cases "n = 0")
    case True
    then show ?thesis
      by (simp add: Posix_NTIMES2)
  next
    case False
    then have "nullable r"
      using NTIMES.prems by simp
    then have "[] \<in> r \<rightarrow> mkeps r"
      using NTIMES.hyps by simp
    then show ?thesis
      by (simp add: Posix_NTIMES2)
  qed
next
  case (BACKREF4 r1 r2 r3 r4 cs)
  then have parts:
    "[] \<in> r1 \<rightarrow> mkeps r1" "[] \<in> r2 \<rightarrow> mkeps r2"
    "[] \<in> r3 \<rightarrow> mkeps r3" "[] \<in> r4 \<rightarrow> mkeps r4" "cs = []"
    by simp_all
  have longest: "BACKREF4_longest r1 r2 r3 r4 [] [] [] [] []"
    unfolding BACKREF4_longest_def by auto
  then show ?case
    using Posix_BACKREF4[OF parts(1) parts(2) parts(3) parts(4) longest] parts(5)
    by simp
next
  case (HALF r cs rep)
  then have rpos: "[] \<in> r \<rightarrow> mkeps r" and cs_empty: "cs = []"
    by simp_all
  have "([] @ cs) \<in> HALF r cs rep \<rightarrow> Half (mkeps r) cs rep"
    using rpos by (rule Posix_HALF)
  then show ?case
    using cs_empty by simp
next
  case (RESIDUE cs rep)
  then show ?case
    by (simp add: Posix_RESIDUE)
qed



lemma Posix_der_residue_string:
  assumes "s \<in> der_residue c cs rep \<rightarrow> v"
  shows "cs = c # s"
  using assms
  by (cases cs) (auto elim!: Posix_elims split: if_splits)

lemma Posix_der_residue_inj:
  assumes "s \<in> der_residue c cs rep \<rightarrow> v"
  shows "inj_residue cs rep c v = Residue cs rep"
  using assms
  by (cases cs; cases v) (auto elim!: Posix_elims split: if_splits)

lemma Posix_der_residue_half_inj:
  assumes "nullable r" "s \<in> der_residue c cs rep \<rightarrow> v"
  shows "(c # s) \<in> HALF r cs rep \<rightarrow>
    (case inj_residue cs rep c v of Residue ds rep' \<Rightarrow> Half (mkeps r) cs rep | _ \<Rightarrow> Void)"
  using assms
proof (cases cs)
  case Nil
  then have "s \<in> ZERO \<rightarrow> v"
    using assms by simp
  then have False by cases
  then show ?thesis by simp
next
  case (Cons d ds)
  show ?thesis
  proof (cases "c = d")
    case True
    then have pos: "s \<in> RESIDUE ds rep \<rightarrow> v"
      using assms Cons by simp
    then have sv: "s = ds" "v = Residue ds rep"
      by (auto elim!: Posix_elims)
    have eps: "[] \<in> r \<rightarrow> mkeps r"
      using assms(1) by (rule Posix_mkeps)
    have "([] @ (d # ds)) \<in> HALF r (d # ds) rep \<rightarrow> Half (mkeps r) (d # ds) rep"
      using eps by (rule Posix_HALF)
    then show ?thesis
      using True Cons sv by simp
  next
    case False
    then have "s \<in> ZERO \<rightarrow> v"
      using assms Cons by simp
    then have False by cases
    then show ?thesis by simp
  qed
qed

lemma Posix_SEQ_longest_first:
  assumes no_longer:
    "\<not> (\<exists>x y. x \<noteq> [] \<and> x @ y = s2 \<and> s1 @ x \<in> L r1 \<and> y \<in> L r2)"
    and t1: "t1 \<in> L r1" and t2: "t2 \<in> L r2"
    and eq: "s1 @ s2 = t1 @ t2"
  shows "length t1 \<le> length s1"
proof (rule ccontr)
  assume "\<not> length t1 \<le> length s1"
  then have longer: "length s1 < length t1"
    by simp
  then obtain x where x: "t1 = s1 @ x" "s2 = x @ t2"
    using eq by (auto simp add: append_eq_append_conv2)
  then have "x \<noteq> []"
    using longer by auto
  then show False
    using no_longer x t1 t2 by blast
qed

lemma BACKREF4_longest_len1D:
  assumes longest: "BACKREF4_longest r1 r2 r3 r4 cs s1 s2 s3 s4"
    and t1: "t1 \<in> L r1" and t2: "t2 \<in> L r2"
    and t3: "t3 \<in> L r3" and t4: "t4 \<in> L r4"
    and eq: "s1 @ s2 @ s3 @ rev cs @ s2 @ s4 =
      t1 @ t2 @ t3 @ rev cs @ t2 @ t4"
  shows "length t1 \<le> length s1"
  using assms unfolding BACKREF4_longest_def by blast

lemma BACKREF4_longest_len2D:
  assumes longest: "BACKREF4_longest r1 r2 r3 r4 cs s1 s2 s3 s4"
    and t1: "t1 \<in> L r1" and t2: "t2 \<in> L r2"
    and t3: "t3 \<in> L r3" and t4: "t4 \<in> L r4"
    and eq: "s1 @ s2 @ s3 @ rev cs @ s2 @ s4 =
      t1 @ t2 @ t3 @ rev cs @ t2 @ t4"
    and len1: "length t1 = length s1"
  shows "length t2 \<le> length s2"
  using assms unfolding BACKREF4_longest_def by blast

lemma BACKREF4_longest_len3D:
  assumes longest: "BACKREF4_longest r1 r2 r3 r4 cs s1 s2 s3 s4"
    and t1: "t1 \<in> L r1" and t2: "t2 \<in> L r2"
    and t3: "t3 \<in> L r3" and t4: "t4 \<in> L r4"
    and eq: "s1 @ s2 @ s3 @ rev cs @ s2 @ s4 =
      t1 @ t2 @ t3 @ rev cs @ t2 @ t4"
    and len1: "length t1 = length s1"
    and len2: "length t2 = length s2"
  shows "length t3 \<le> length s3"
  using assms unfolding BACKREF4_longest_def by blast

lemma BACKREF4_longest_prefix_inj:
  assumes longest: "BACKREF4_longest (der c r1) r2 r3 r4 cs s1 s2 s3 s4"
  shows "BACKREF4_longest r1 r2 r3 r4 cs (c # s1) s2 s3 s4"
  unfolding BACKREF4_longest_def
proof safe
  fix t1 t2 t3 t4
  assume t1_in: "t1 \<in> L r1" and t2_in: "t2 \<in> L r2"
    and t3_in: "t3 \<in> L r3" and t4_in: "t4 \<in> L r4"
    and eq0: "(c # s1) @ s2 @ s3 @ rev cs @ s2 @ s4 =
      t1 @ t2 @ t3 @ rev cs @ t2 @ t4"
  show "length t1 \<le> length (c # s1)"
  proof (cases t1)
    case Nil
    then show ?thesis by simp
  next
    case (Cons d ds)
    then have ds: "ds \<in> L (der c r1)"
      using t1_in eq0 by (auto simp add: der_correctness Der_def)
    have eq: "s1 @ s2 @ s3 @ rev cs @ s2 @ s4 =
      ds @ t2 @ t3 @ rev cs @ t2 @ t4"
      using eq0 Cons by auto
    have "length ds \<le> length s1"
      using BACKREF4_longest_len1D[OF longest ds t2_in t3_in t4_in eq] .
    then show ?thesis
      using Cons by simp
  qed
next
  fix t1 t2 t3 t4
  assume t1_in: "t1 \<in> L r1" and t2_in: "t2 \<in> L r2"
    and t3_in: "t3 \<in> L r3" and t4_in: "t4 \<in> L r4"
    and eq0: "(c # s1) @ s2 @ s3 @ rev cs @ s2 @ s4 =
      t1 @ t2 @ t3 @ rev cs @ t2 @ t4"
    and len: "length t1 = length (c # s1)"
  show "length t2 \<le> length s2"
    proof (cases t1)
      case Nil
      then show ?thesis
        using len by simp
    next
      case (Cons d ds)
      then have ds: "ds \<in> L (der c r1)"
        using t1_in eq0 by (auto simp add: der_correctness Der_def)
      have eq: "s1 @ s2 @ s3 @ rev cs @ s2 @ s4 =
        ds @ t2 @ t3 @ rev cs @ t2 @ t4"
        using eq0 Cons by auto
      have "length ds = length s1"
        using len Cons by simp
      then show ?thesis
        using BACKREF4_longest_len2D[OF longest ds t2_in t3_in t4_in eq] by blast
    qed
next
  fix t1 t2 t3 t4
  assume t1_in: "t1 \<in> L r1" and t2_in: "t2 \<in> L r2"
    and t3_in: "t3 \<in> L r3" and t4_in: "t4 \<in> L r4"
    and eq0: "(c # s1) @ s2 @ s3 @ rev cs @ s2 @ s4 =
      t1 @ t2 @ t3 @ rev cs @ t2 @ t4"
    and len1: "length t1 = length (c # s1)"
    and len2: "length t2 = length s2"
  show "length t3 \<le> length s3"
    proof (cases t1)
      case Nil
      then show ?thesis
        using len1 by simp
    next
      case (Cons d ds)
      then have ds: "ds \<in> L (der c r1)"
        using t1_in eq0 by (auto simp add: der_correctness Der_def)
      have eq: "s1 @ s2 @ s3 @ rev cs @ s2 @ s4 =
        ds @ t2 @ t3 @ rev cs @ t2 @ t4"
        using eq0 Cons by auto
      have "length ds = length s1" "length t2 = length s2"
        using len1 len2 Cons by simp_all
      then show ?thesis
        using BACKREF4_longest_len3D[OF longest ds t2_in t3_in t4_in eq] by blast
    qed
qed

lemma BACKREF4_longest_capture_inj:
  assumes no_prefix:
    "s2 @ s3 @ rev (c # cs) @ s2 @ s4 \<notin>
      L (BACKREF4 (der c r1) r2 r3 r4 cs)"
    and longest:
      "BACKREF4_longest ONE (der c r2) r3 r4 (c # cs) [] s2 s3 s4"
  shows "BACKREF4_longest r1 r2 r3 r4 cs [] (c # s2) s3 s4"
  unfolding BACKREF4_longest_def
proof safe
  fix t1 t2 t3 t4
  assume t1_in: "t1 \<in> L r1" and t2_in: "t2 \<in> L r2"
    and t3_in: "t3 \<in> L r3" and t4_in: "t4 \<in> L r4"
    and eq0: "[] @ (c # s2) @ s3 @ rev cs @ (c # s2) @ s4 =
      t1 @ t2 @ t3 @ rev cs @ t2 @ t4"
  show "length t1 \<le> length []"
  proof (cases t1)
    case Nil
    then show ?thesis by simp
  next
    case (Cons d ds)
    then have "s2 @ s3 @ rev (c # cs) @ s2 @ s4 \<in>
      L (BACKREF4 (der c r1) r2 r3 r4 cs)"
      using t1_in t2_in t3_in t4_in eq0
      by (auto simp add: backref_lang4_def der_correctness Der_def)
    then show ?thesis
      using no_prefix by simp
  qed
next
  fix t1 t2 t3 t4
  assume t1_in: "t1 \<in> L r1" and t2_in: "t2 \<in> L r2"
    and t3_in: "t3 \<in> L r3" and t4_in: "t4 \<in> L r4"
    and eq0: "[] @ (c # s2) @ s3 @ rev cs @ (c # s2) @ s4 =
      t1 @ t2 @ t3 @ rev cs @ t2 @ t4"
    and len1: "length t1 = length []"
  have t1_nil: "t1 = []"
    using len1 by simp
  have one_in: "[] \<in> L ONE"
    by simp
  have len_nil: "length [] = length []"
    by simp
  show "length t2 \<le> length (c # s2)"
  proof (cases t2)
    case Nil
    then show ?thesis by simp
  next
    case (Cons d ds)
    then have ds: "ds \<in> L (der c r2)"
      using t2_in eq0 t1_nil by (auto simp add: der_correctness Der_def)
    have eq: "s2 @ s3 @ rev (c # cs) @ s2 @ s4 =
      ds @ t3 @ rev (c # cs) @ ds @ t4"
      using eq0 t1_nil Cons by auto
    have eq_long: "[] @ s2 @ s3 @ rev (c # cs) @ s2 @ s4 =
      [] @ ds @ t3 @ rev (c # cs) @ ds @ t4"
      using eq by simp
    have "length ds \<le> length s2"
      using BACKREF4_longest_len2D[OF longest one_in ds t3_in t4_in eq_long len_nil] .
    then show ?thesis
      using Cons by simp
  qed
next
  fix t1 t2 t3 t4
  assume t1_in: "t1 \<in> L r1" and t2_in: "t2 \<in> L r2"
    and t3_in: "t3 \<in> L r3" and t4_in: "t4 \<in> L r4"
    and eq0: "[] @ (c # s2) @ s3 @ rev cs @ (c # s2) @ s4 =
      t1 @ t2 @ t3 @ rev cs @ t2 @ t4"
    and len1: "length t1 = length []"
    and len2: "length t2 = length (c # s2)"
  have t1_nil: "t1 = []"
    using len1 by simp
  have one_in: "[] \<in> L ONE"
    by simp
  have len_nil: "length [] = length []"
    by simp
  show "length t3 \<le> length s3"
  proof (cases t2)
    case Nil
    then show ?thesis
      using len2 by simp
  next
    case (Cons d ds)
    then have ds: "ds \<in> L (der c r2)"
      using t2_in eq0 t1_nil by (auto simp add: der_correctness Der_def)
    have eq: "s2 @ s3 @ rev (c # cs) @ s2 @ s4 =
      ds @ t3 @ rev (c # cs) @ ds @ t4"
      using eq0 t1_nil Cons by auto
    have eq_long: "[] @ s2 @ s3 @ rev (c # cs) @ s2 @ s4 =
      [] @ ds @ t3 @ rev (c # cs) @ ds @ t4"
      using eq by simp
    have "length ds = length s2"
      using len2 Cons by simp
    then show ?thesis
      using BACKREF4_longest_len3D[OF longest one_in ds t3_in t4_in eq_long len_nil] by simp
  qed
qed

lemma BACKREF4_longest_tail3_inj:
  assumes no_prefix:
    "s3 @ rev cs @ s4 \<notin> L (BACKREF4 (der c r1) r2 r3 r4 cs)"
    and no_capture:
      "s3 @ rev cs @ s4 \<notin>
        L (BACKREF4 ONE (der c r2) r3 r4 (c # cs))"
    and no_longer:
      "\<not> (\<exists>x y. x \<noteq> [] \<and> x @ y = rev cs @ s4 \<and>
        s3 @ x \<in> L (der c r3) \<and>
        y \<in> L (SEQ (RESIDUE (rev cs) (rev cs)) r4))"
  shows "BACKREF4_longest r1 r2 r3 r4 cs [] [] (c # s3) s4"
  unfolding BACKREF4_longest_def
proof safe
  fix t1 t2 t3 t4
  assume t1_in: "t1 \<in> L r1" and t2_in: "t2 \<in> L r2"
    and t3_in: "t3 \<in> L r3" and t4_in: "t4 \<in> L r4"
    and eq0: "[] @ [] @ (c # s3) @ rev cs @ [] @ s4 =
      t1 @ t2 @ t3 @ rev cs @ t2 @ t4"
  show "length t1 \<le> length []"
    using t1_in t2_in t3_in t4_in eq0 no_prefix
    by (cases t1) (auto simp add: backref_lang4_def der_correctness Der_def)
next
  fix t1 t2 t3 t4
  assume t1_in: "t1 \<in> L r1" and t2_in: "t2 \<in> L r2"
    and t3_in: "t3 \<in> L r3" and t4_in: "t4 \<in> L r4"
    and eq0: "[] @ [] @ (c # s3) @ rev cs @ [] @ s4 =
      t1 @ t2 @ t3 @ rev cs @ t2 @ t4"
    and len1: "length t1 = length []"
  have t1_nil: "t1 = []"
    using len1 by simp
  show "length t2 \<le> length []"
  proof (cases t2)
    case Nil
    then show ?thesis by simp
  next
    case (Cons d ds)
    then have "s3 @ rev cs @ s4 \<in>
      L (BACKREF4 ONE (der c r2) r3 r4 (c # cs))"
      using t2_in t3_in t4_in eq0 t1_nil
      by (auto simp add: backref_lang4_def der_correctness Der_def)
    then show ?thesis
      using no_capture by simp
  qed
next
  fix t1 t2 t3 t4
  assume t1_in: "t1 \<in> L r1" and t2_in: "t2 \<in> L r2"
    and t3_in: "t3 \<in> L r3" and t4_in: "t4 \<in> L r4"
    and eq0: "[] @ [] @ (c # s3) @ rev cs @ [] @ s4 =
      t1 @ t2 @ t3 @ rev cs @ t2 @ t4"
    and len1: "length t1 = length []"
    and len2: "length t2 = length []"
  have nils: "t1 = []" "t2 = []"
    using len1 len2 by auto
  show "length t3 \<le> length (c # s3)"
  proof (cases t3)
    case Nil
    then show ?thesis by simp
  next
    case (Cons d ds)
    then have ds_lang: "ds \<in> L (der c r3)"
      using t3_in eq0 nils by (auto simp add: der_correctness Der_def)
    have eq: "s3 @ rev cs @ s4 = ds @ (rev cs @ t4)"
      using eq0 nils Cons by auto
    have mid: "rev cs @ t4 \<in> L (SEQ (RESIDUE (rev cs) (rev cs)) r4)"
      using t4_in by (auto simp add: Sequ_def)
    have "length ds \<le> length s3"
      using Posix_SEQ_longest_first[OF no_longer ds_lang mid eq] .
    then show ?thesis
      using Cons by simp
  qed
qed

lemma BACKREF4_longest_tail_residue_inj:
  assumes res: "rev cs = c # sr"
    and no_prefix:
      "sr @ s4 \<notin> L (BACKREF4 (der c r1) r2 r3 r4 cs)"
    and no_capture:
      "sr @ s4 \<notin> L (BACKREF4 ONE (der c r2) r3 r4 (c # cs))"
    and no_tail3:
      "sr @ s4 \<notin> L (SEQ (der c r3)
        (SEQ (RESIDUE (rev cs) (rev cs)) r4))"
  shows "BACKREF4_longest r1 r2 r3 r4 cs [] [] [] s4"
  unfolding BACKREF4_longest_def
proof safe
  fix t1 t2 t3 t4
  assume t1_in: "t1 \<in> L r1" and t2_in: "t2 \<in> L r2"
    and t3_in: "t3 \<in> L r3" and t4_in: "t4 \<in> L r4"
    and eq0: "[] @ [] @ [] @ rev cs @ [] @ s4 =
      t1 @ t2 @ t3 @ rev cs @ t2 @ t4"
  show "length t1 \<le> length []"
  proof (cases t1)
    case Nil
    then show ?thesis by simp
  next
    case (Cons d ds)
    then have "sr @ s4 \<in> L (BACKREF4 (der c r1) r2 r3 r4 cs)"
      using t1_in t2_in t3_in t4_in eq0 res
      by (auto simp add: backref_lang4_def der_correctness Der_def)
    then show ?thesis
      using no_prefix by simp
  qed
next
  fix t1 t2 t3 t4
  assume t1_in: "t1 \<in> L r1" and t2_in: "t2 \<in> L r2"
    and t3_in: "t3 \<in> L r3" and t4_in: "t4 \<in> L r4"
    and eq0: "[] @ [] @ [] @ rev cs @ [] @ s4 =
      t1 @ t2 @ t3 @ rev cs @ t2 @ t4"
    and len1: "length t1 = length []"
  have t1_nil: "t1 = []"
    using len1 by simp
  show "length t2 \<le> length []"
  proof (cases t2)
    case Nil
    then show ?thesis by simp
  next
    case (Cons d ds)
    then have "sr @ s4 \<in> L (BACKREF4 ONE (der c r2) r3 r4 (c # cs))"
      using t2_in t3_in t4_in eq0 t1_nil res
      by (auto simp add: backref_lang4_def der_correctness Der_def)
    then show ?thesis
      using no_capture by simp
  qed
next
  fix t1 t2 t3 t4
  assume t1_in: "t1 \<in> L r1" and t2_in: "t2 \<in> L r2"
    and t3_in: "t3 \<in> L r3" and t4_in: "t4 \<in> L r4"
    and eq0: "[] @ [] @ [] @ rev cs @ [] @ s4 =
      t1 @ t2 @ t3 @ rev cs @ t2 @ t4"
    and len1: "length t1 = length []"
    and len2: "length t2 = length []"
  have nils: "t1 = []" "t2 = []"
    using len1 len2 by auto
  show "length t3 \<le> length []"
  proof (cases t3)
    case Nil
    then show ?thesis by simp
  next
    case (Cons d ds)
    then have "sr @ s4 \<in>
      L (SEQ (der c r3) (SEQ (RESIDUE (rev cs) (rev cs)) r4))"
      using t3_in t4_in eq0 nils res
      by (auto simp add: Sequ_def der_correctness Der_def)
    then show ?thesis
      using no_tail3 by simp
  qed
qed

lemma BACKREF4_longest_tail4_inj:
  assumes empty: "rev cs = []"
    and no_prefix:
      "s4 \<notin> L (BACKREF4 (der c r1) r2 r3 r4 cs)"
    and no_capture:
      "s4 \<notin> L (BACKREF4 ONE (der c r2) r3 r4 (c # cs))"
    and no_tail3:
      "s4 \<notin> L (SEQ (der c r3)
        (SEQ (RESIDUE (rev cs) (rev cs)) r4))"
  shows "BACKREF4_longest r1 r2 r3 r4 cs [] [] [] (c # s4)"
  unfolding BACKREF4_longest_def
proof safe
  fix t1 t2 t3 t4
  assume t1_in: "t1 \<in> L r1" and t2_in: "t2 \<in> L r2"
    and t3_in: "t3 \<in> L r3" and t4_in: "t4 \<in> L r4"
    and eq0: "[] @ [] @ [] @ rev cs @ [] @ (c # s4) =
      t1 @ t2 @ t3 @ rev cs @ t2 @ t4"
  show "length t1 \<le> length []"
  proof (cases t1)
    case Nil
    then show ?thesis by simp
  next
    case (Cons d ds)
    then have "s4 \<in> L (BACKREF4 (der c r1) r2 r3 r4 cs)"
      using t1_in t2_in t3_in t4_in eq0 empty
      by (auto simp add: backref_lang4_def der_correctness Der_def)
    then show ?thesis
      using no_prefix by simp
  qed
next
  fix t1 t2 t3 t4
  assume t1_in: "t1 \<in> L r1" and t2_in: "t2 \<in> L r2"
    and t3_in: "t3 \<in> L r3" and t4_in: "t4 \<in> L r4"
    and eq0: "[] @ [] @ [] @ rev cs @ [] @ (c # s4) =
      t1 @ t2 @ t3 @ rev cs @ t2 @ t4"
    and len1: "length t1 = length []"
  have t1_nil: "t1 = []"
    using len1 by simp
  show "length t2 \<le> length []"
  proof (cases t2)
    case Nil
    then show ?thesis by simp
  next
    case (Cons d ds)
    then have "s4 \<in> L (BACKREF4 ONE (der c r2) r3 r4 (c # cs))"
      using t2_in t3_in t4_in eq0 t1_nil empty
      by (auto simp add: backref_lang4_def der_correctness Der_def)
    then show ?thesis
      using no_capture by simp
  qed
next
  fix t1 t2 t3 t4
  assume t1_in: "t1 \<in> L r1" and t2_in: "t2 \<in> L r2"
    and t3_in: "t3 \<in> L r3" and t4_in: "t4 \<in> L r4"
    and eq0: "[] @ [] @ [] @ rev cs @ [] @ (c # s4) =
      t1 @ t2 @ t3 @ rev cs @ t2 @ t4"
    and len1: "length t1 = length []"
    and len2: "length t2 = length []"
  have nils: "t1 = []" "t2 = []"
    using len1 len2 by auto
  show "length t3 \<le> length []"
  proof (cases t3)
    case Nil
    then show ?thesis by simp
  next
    case (Cons d ds)
    then have "s4 \<in> L (SEQ (der c r3) (SEQ (RESIDUE (rev cs) (rev cs)) r4))"
      using t3_in t4_in eq0 nils empty
      by (auto simp add: Sequ_def der_correctness Der_def)
    then show ?thesis
      using no_tail3 by simp
  qed
qed

(* BACKREF-MIGRATION-TODO (proof constructor-case extension, ADMIN APPROVAL REQUIRED):
   Extend POSIX preservation of injval for BACKREF4/HALF/RESIDUE after the
   BACKREF4 Posix rule and injval cases are approved. This is a main bounty
   item. *)
lemma Posix_injval:
  assumes "s \<in> (der c r) \<rightarrow> v"
  shows "(c # s) \<in> r \<rightarrow> (injval r c v)"
using assms
proof(induct r arbitrary: s v rule: rexp.induct)
  case ZERO
  have "s \<in> der c ZERO \<rightarrow> v" by fact
  then have "s \<in> ZERO \<rightarrow> v" by simp
  then have "False" by cases
  then show "(c # s) \<in> ZERO \<rightarrow> (injval ZERO c v)" by simp
next
  case ONE
  have "s \<in> der c ONE \<rightarrow> v" by fact
  then have "s \<in> ZERO \<rightarrow> v" by simp
  then have "False" by cases
  then show "(c # s) \<in> ONE \<rightarrow> (injval ONE c v)" by simp
next 
  case (CH d)
  consider (eq) "c = d" | (ineq) "c \<noteq> d" by blast
  then show "(c # s) \<in> (CH d) \<rightarrow> (injval (CH d) c v)"
  proof (cases)
    case eq
    have "s \<in> der c (CH d) \<rightarrow> v" by fact
    then have "s \<in> ONE \<rightarrow> v" using eq by simp
    then have eqs: "s = [] \<and> v = Void" by cases simp
    show "(c # s) \<in> CH d \<rightarrow> injval (CH d) c v" using eq eqs 
    by (auto intro: Posix.intros)
  next
    case ineq
    have "s \<in> der c (CH d) \<rightarrow> v" by fact
    then have "s \<in> ZERO \<rightarrow> v" using ineq by simp
    then have "False" by cases
    then show "(c # s) \<in> CH d \<rightarrow> injval (CH d) c v" by simp
  qed
next
  case (ALT r1 r2)
  have IH1: "\<And>s v. s \<in> der c r1 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r1 \<rightarrow> injval r1 c v" by fact
  have IH2: "\<And>s v. s \<in> der c r2 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r2 \<rightarrow> injval r2 c v" by fact
  have "s \<in> der c (ALT r1 r2) \<rightarrow> v" by fact
  then have "s \<in> ALT (der c r1) (der c r2) \<rightarrow> v" by simp
  then consider (left) v' where "v = Left v'" "s \<in> der c r1 \<rightarrow> v'" 
              | (right) v' where "v = Right v'" "s \<notin> L (der c r1)" "s \<in> der c r2 \<rightarrow> v'" 
              by cases auto
  then show "(c # s) \<in> ALT r1 r2 \<rightarrow> injval (ALT r1 r2) c v"
  proof (cases)
    case left
    have "s \<in> der c r1 \<rightarrow> v'" by fact
    then have "(c # s) \<in> r1 \<rightarrow> injval r1 c v'" using IH1 by simp
    then have "(c # s) \<in> ALT r1 r2 \<rightarrow> injval (ALT r1 r2) c (Left v')" by (auto intro: Posix.intros)
    then show "(c # s) \<in> ALT r1 r2 \<rightarrow> injval (ALT r1 r2) c v" using left by simp
  next 
    case right
    have "s \<notin> L (der c r1)" by fact
    then have "c # s \<notin> L r1" by (simp add: der_correctness Der_def)
    moreover 
    have "s \<in> der c r2 \<rightarrow> v'" by fact
    then have "(c # s) \<in> r2 \<rightarrow> injval r2 c v'" using IH2 by simp
    ultimately have "(c # s) \<in> ALT r1 r2 \<rightarrow> injval (ALT r1 r2) c (Right v')" 
      by (auto intro: Posix.intros)
    then show "(c # s) \<in> ALT r1 r2 \<rightarrow> injval (ALT r1 r2) c v" using right by simp
  qed
next
  case (SEQ r1 r2)
  have IH1: "\<And>s v. s \<in> der c r1 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r1 \<rightarrow> injval r1 c v" by fact
  have IH2: "\<And>s v. s \<in> der c r2 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r2 \<rightarrow> injval r2 c v" by fact
  have "s \<in> der c (SEQ r1 r2) \<rightarrow> v" by fact
  then consider 
        (left_nullable) v1 v2 s1 s2 where 
        "v = Left (Seq v1 v2)"  "s = s1 @ s2" 
        "s1 \<in> der c r1 \<rightarrow> v1" "s2 \<in> r2 \<rightarrow> v2" "nullable r1" 
        "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L (der c r1) \<and> s\<^sub>4 \<in> L r2)"
      | (right_nullable) v1 s1 s2 where 
        "v = Right v1" "s = s1 @ s2"  
        "s \<in> der c r2 \<rightarrow> v1" "nullable r1" "s1 @ s2 \<notin> L (SEQ (der c r1) r2)"
      | (not_nullable) v1 v2 s1 s2 where
        "v = Seq v1 v2" "s = s1 @ s2" 
        "s1 \<in> der c r1 \<rightarrow> v1" "s2 \<in> r2 \<rightarrow> v2" "\<not>nullable r1" 
        "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L (der c r1) \<and> s\<^sub>4 \<in> L r2)"
        by (force split: if_splits elim!: Posix_elims simp add: Sequ_def der_correctness Der_def)   
  then show "(c # s) \<in> SEQ r1 r2 \<rightarrow> injval (SEQ r1 r2) c v" 
    proof (cases)
      case left_nullable
      have "s1 \<in> der c r1 \<rightarrow> v1" by fact
      then have "(c # s1) \<in> r1 \<rightarrow> injval r1 c v1" using IH1 by simp
      moreover
      have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L (der c r1) \<and> s\<^sub>4 \<in> L r2)" by fact
      then have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> L r1 \<and> s\<^sub>4 \<in> L r2)" by (simp add: der_correctness Der_def)
      ultimately have "((c # s1) @ s2) \<in> SEQ r1 r2 \<rightarrow> Seq (injval r1 c v1) v2" using left_nullable by (rule_tac Posix.intros)
      then show "(c # s) \<in> SEQ r1 r2 \<rightarrow> injval (SEQ r1 r2) c v" using left_nullable by simp
    next
      case right_nullable
      have "nullable r1" by fact
      then have "[] \<in> r1 \<rightarrow> (mkeps r1)" by (rule Posix_mkeps)
      moreover
      have "s \<in> der c r2 \<rightarrow> v1" by fact
      then have "(c # s) \<in> r2 \<rightarrow> (injval r2 c v1)" using IH2 by simp
      moreover
      have "s1 @ s2 \<notin> L (SEQ (der c r1) r2)" by fact
      then have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = c # s \<and> [] @ s\<^sub>3 \<in> L r1 \<and> s\<^sub>4 \<in> L r2)" using right_nullable
        by(auto simp add: der_correctness Der_def append_eq_Cons_conv Sequ_def)
      ultimately have "([] @ (c # s)) \<in> SEQ r1 r2 \<rightarrow> Seq (mkeps r1) (injval r2 c v1)"
      by(rule Posix.intros)
      then show "(c # s) \<in> SEQ r1 r2 \<rightarrow> injval (SEQ r1 r2) c v" using right_nullable by simp
    next
      case not_nullable
      have "s1 \<in> der c r1 \<rightarrow> v1" by fact
      then have "(c # s1) \<in> r1 \<rightarrow> injval r1 c v1" using IH1 by simp
      moreover
      have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L (der c r1) \<and> s\<^sub>4 \<in> L r2)" by fact
      then have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> L r1 \<and> s\<^sub>4 \<in> L r2)" by (simp add: der_correctness Der_def)
      ultimately have "((c # s1) @ s2) \<in> SEQ r1 r2 \<rightarrow> Seq (injval r1 c v1) v2" using not_nullable 
        by (rule_tac Posix.intros) (simp_all) 
      then show "(c # s) \<in> SEQ r1 r2 \<rightarrow> injval (SEQ r1 r2) c v" using not_nullable by simp
    qed
next
  case (STAR r)
  have IH: "\<And>s v. s \<in> der c r \<rightarrow> v \<Longrightarrow> (c # s) \<in> r \<rightarrow> injval r c v" by fact
  have "s \<in> der c (STAR r) \<rightarrow> v" by fact
  then consider
      (cons) v1 vs s1 s2 where 
        "v = Seq v1 (Stars vs)" "s = s1 @ s2" 
        "s1 \<in> der c r \<rightarrow> v1" "s2 \<in> (STAR r) \<rightarrow> (Stars vs)"
        "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L (der c r) \<and> s\<^sub>4 \<in> L (STAR r))" 
        apply(auto elim!: Posix_elims(1-5) simp add: der_correctness Der_def intro: Posix.intros)
        apply(rotate_tac 3)
        apply(erule_tac Posix_elims(6))
        apply (simp add: Posix.intros(6))
        using Posix.intros(7) by blast
    then show "(c # s) \<in> STAR r \<rightarrow> injval (STAR r) c v" 
    proof (cases)
      case cons
          have "s1 \<in> der c r \<rightarrow> v1" by fact
          then have "(c # s1) \<in> r \<rightarrow> injval r c v1" using IH by simp
        moreover
          have "s2 \<in> STAR r \<rightarrow> Stars vs" by fact
        moreover 
          have "(c # s1) \<in> r \<rightarrow> injval r c v1" by fact 
          then have "flat (injval r c v1) = (c # s1)" by (rule Posix1)
          then have "flat (injval r c v1) \<noteq> []" by simp
        moreover 
          have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L (der c r) \<and> s\<^sub>4 \<in> L (STAR r))" by fact
          then have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> L r \<and> s\<^sub>4 \<in> L (STAR r))" 
            by (simp add: der_correctness Der_def)
        ultimately 
        have "((c # s1) @ s2) \<in> STAR r \<rightarrow> Stars (injval r c v1 # vs)" by (rule Posix.intros)
        then show "(c # s) \<in> STAR r \<rightarrow> injval (STAR r) c v" using cons by(simp)
      qed
next
  case (NTIMES r n)
  have IH: "\<And>s v. s \<in> der c r \<rightarrow> v \<Longrightarrow> (c # s) \<in> r \<rightarrow> injval r c v" by fact
  have "s \<in> der c (NTIMES r n) \<rightarrow> v" by fact
  then consider
      (cons) v1 vs s1 s2 where 
        "v = Seq v1 (Stars vs)" "s = s1 @ s2" 
        "s1 \<in> der c r \<rightarrow> v1" "s2 \<in> (NTIMES r (n - 1)) \<rightarrow> (Stars vs)" "0 < n"
        "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L (der c r) \<and> s\<^sub>4 \<in> L (NTIMES r (n - 1)))" 
    apply(auto elim: Posix_elims simp add: der_correctness Der_def intro: Posix.intros split: if_splits)
    apply(erule Posix_elims)
    apply(simp)
    apply(subgoal_tac "\<exists>vss. v2 = Stars vss")
    apply(clarify)
    apply(drule_tac x="vss" in meta_spec)
    apply(drule_tac x="s1" in meta_spec)
    apply(drule_tac x="s2" in meta_spec)
     apply(simp add: der_correctness Der_def)
    apply(erule Posix_elims)
     apply(auto)
      done
    then show "(c # s) \<in> (NTIMES r n) \<rightarrow> injval (NTIMES r n) c v" 
    proof (cases)
      case cons
          have "s1 \<in> der c r \<rightarrow> v1" by fact
          then have "(c # s1) \<in> r \<rightarrow> injval r c v1" using IH by simp
        moreover
          have "s2 \<in> (NTIMES r (n - 1)) \<rightarrow> Stars vs" by fact
        moreover 
          have "(c # s1) \<in> r \<rightarrow> injval r c v1" by fact 
          then have "flat (injval r c v1) = (c # s1)" by (rule Posix1)
          then have "flat (injval r c v1) \<noteq> []" by simp
        moreover 
          have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L (der c r) \<and> s\<^sub>4 \<in> L (NTIMES r (n - 1)))" by fact
          then have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> L r \<and> s\<^sub>4 \<in> L (NTIMES r (n - 1)))"
            by (simp add: der_correctness Der_def)
        ultimately 
        have "((c # s1) @ s2) \<in> NTIMES r n \<rightarrow> Stars (injval r c v1 # vs)"
          by (metis One_nat_def Posix_NTIMES1 Suc_eq_plus1 Suc_pred cons(5))
        then show "(c # s) \<in> NTIMES r n \<rightarrow> injval (NTIMES r n) c v" using cons by(simp)
      qed  
next
  case (BACKREF4 r1 r2 r3 r4 cs)
  let ?prefix = "BACKREF4 (der c r1) r2 r3 r4 cs"
  let ?capture = "BACKREF4 ONE (der c r2) r3 r4 (c # cs)"
  let ?res = "rev cs"
  let ?mid = "SEQ (RESIDUE ?res ?res) r4"
  let ?res_tail =
    "if ?res = []
     then ALT (SEQ (der_residue c ?res ?res) r4) (der c r4)
     else SEQ (der_residue c ?res ?res) r4"
  let ?tail =
    "if nullable r3
     then ALT (SEQ (der c r3) ?mid) ?res_tail
     else SEQ (der c r3) ?mid"
  let ?rest = "if nullable r2 then ALT ?capture ?tail else ?capture"
  have IH1: "\<And>s v. s \<in> der c r1 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r1 \<rightarrow> injval r1 c v"
    by fact
  have IH2: "\<And>s v. s \<in> der c r2 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r2 \<rightarrow> injval r2 c v"
    by fact
  have IH3: "\<And>s v. s \<in> der c r3 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r3 \<rightarrow> injval r3 c v"
    by fact
  have IH4: "\<And>s v. s \<in> der c r4 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r4 \<rightarrow> injval r4 c v"
    by fact
  have prem: "s \<in> der c (BACKREF4 r1 r2 r3 r4 cs) \<rightarrow> v"
    by fact

  have prefix_case:
    "\<And>w. s \<in> ?prefix \<rightarrow> w \<Longrightarrow>
      (c # s) \<in> BACKREF4 r1 r2 r3 r4 cs \<rightarrow>
        injval (BACKREF4 r1 r2 r3 r4 cs) c w"
  proof -
    fix w
    assume p: "s \<in> ?prefix \<rightarrow> w"
    then obtain s1 s2 s3 s4 v1 v2 v3 v4 where parts:
      "s = s1 @ s2 @ s3 @ rev cs @ s2 @ s4"
      "w = Backref4 v1 v2 v3 v4 cs"
      "s1 \<in> der c r1 \<rightarrow> v1" "s2 \<in> r2 \<rightarrow> v2"
      "s3 \<in> r3 \<rightarrow> v3" "s4 \<in> r4 \<rightarrow> v4"
      "BACKREF4_longest (der c r1) r2 r3 r4 cs s1 s2 s3 s4"
      by (auto elim!: Posix_elims)
    have r1pos: "(c # s1) \<in> r1 \<rightarrow> injval r1 c v1"
      using IH1 parts(3) by simp
    have longest: "BACKREF4_longest r1 r2 r3 r4 cs (c # s1) s2 s3 s4"
      using BACKREF4_longest_prefix_inj[OF parts(7)] .
    have "((c # s1) @ s2 @ s3 @ rev cs @ s2 @ s4) \<in>
      BACKREF4 r1 r2 r3 r4 cs \<rightarrow> Backref4 (injval r1 c v1) v2 v3 v4 cs"
      using Posix_BACKREF4[OF r1pos parts(4) parts(5) parts(6) longest] by simp
    then show "(c # s) \<in> BACKREF4 r1 r2 r3 r4 cs \<rightarrow>
      injval (BACKREF4 r1 r2 r3 r4 cs) c w"
      using parts by simp
  qed

  have capture_case:
    "\<And>w. [] \<in> r1 \<rightarrow> mkeps r1 \<Longrightarrow> s \<notin> L ?prefix \<Longrightarrow> s \<in> ?capture \<rightarrow> w \<Longrightarrow>
      (c # s) \<in> BACKREF4 r1 r2 r3 r4 cs \<rightarrow>
        injval (BACKREF4 r1 r2 r3 r4 cs) c (Right w)"
  proof -
    fix w
    assume r1_eps: "[] \<in> r1 \<rightarrow> mkeps r1" and no_prefix: "s \<notin> L ?prefix"
      and cap: "s \<in> ?capture \<rightarrow> w"
    then obtain s2 s3 s4 v2 v3 v4 where parts:
      "s = s2 @ s3 @ rev (c # cs) @ s2 @ s4"
      "w = Backref4 Void v2 v3 v4 (c # cs)"
      "s2 \<in> der c r2 \<rightarrow> v2" "s3 \<in> r3 \<rightarrow> v3" "s4 \<in> r4 \<rightarrow> v4"
      "BACKREF4_longest ONE (der c r2) r3 r4 (c # cs) [] s2 s3 s4"
      by (auto elim!: Posix_elims)
    have r2pos: "(c # s2) \<in> r2 \<rightarrow> injval r2 c v2"
      using IH2 parts(3) by simp
    have longest: "BACKREF4_longest r1 r2 r3 r4 cs [] (c # s2) s3 s4"
      using BACKREF4_longest_capture_inj[OF _ parts(6)] no_prefix parts(1) by simp
    have "([] @ (c # s2) @ s3 @ rev cs @ (c # s2) @ s4) \<in>
      BACKREF4 r1 r2 r3 r4 cs \<rightarrow>
        Backref4 (mkeps r1) (injval r2 c v2) v3 v4 cs"
      using Posix_BACKREF4[OF r1_eps r2pos parts(4) parts(5) longest] by simp
    then show "(c # s) \<in> BACKREF4 r1 r2 r3 r4 cs \<rightarrow>
      injval (BACKREF4 r1 r2 r3 r4 cs) c (Right w)"
      using parts by simp
  qed

  have tail3_case:
    "\<And>w. [] \<in> r1 \<rightarrow> mkeps r1 \<Longrightarrow> nullable r2 \<Longrightarrow> s \<notin> L ?prefix \<Longrightarrow> s \<notin> L ?capture \<Longrightarrow>
      s \<in> SEQ (der c r3) ?mid \<rightarrow> w \<Longrightarrow>
      (c # s) \<in> BACKREF4 r1 r2 r3 r4 cs \<rightarrow>
        injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right w))"
  proof -
    fix w
    assume eps1: "[] \<in> r1 \<rightarrow> mkeps r1" and n2: "nullable r2" and no_prefix: "s \<notin> L ?prefix"
      and no_capture: "s \<notin> L ?capture"
      and p: "s \<in> SEQ (der c r3) ?mid \<rightarrow> w"
    from p obtain s3 sm v3 vm where outer:
      "s = s3 @ sm" "w = Seq v3 vm" "s3 \<in> der c r3 \<rightarrow> v3"
      "sm \<in> ?mid \<rightarrow> vm"
      "\<not> (\<exists>x y. x \<noteq> [] \<and> x @ y = sm \<and>
        s3 @ x \<in> L (der c r3) \<and> y \<in> L ?mid)"
      using p
      apply cases
      apply auto
      done
    from outer(4) obtain sres s4 vres v4 where inner:
      "sm = sres @ s4" "vm = Seq vres v4"
      "sres \<in> RESIDUE (rev cs) (rev cs) \<rightarrow> vres" "s4 \<in> r4 \<rightarrow> v4"
      using outer(4)
      apply cases
      apply auto
      done
    have seq_s: "s = s3 @ sres @ s4"
      using outer(1) inner(1) by simp
    have seq_w: "w = Seq v3 (Seq vres v4)"
      using outer(2) inner(2) by simp
    have no_longer:
      "\<not> (\<exists>x y. x \<noteq> [] \<and> x @ y = sres @ s4 \<and>
        s3 @ x \<in> L (der c r3) \<and> y \<in> L ?mid)"
      using outer(5) inner(1) by simp
    have sres_eq: "sres = rev cs"
      using inner(3) by (auto elim!: Posix_elims(10))
    have vres_eq: "vres = Residue (rev cs) (rev cs)"
      using inner(3) by (auto elim!: Posix_elims(10))
    have eps2: "[] \<in> r2 \<rightarrow> mkeps r2"
      using n2 by (rule Posix_mkeps)
    have r3pos: "(c # s3) \<in> r3 \<rightarrow> injval r3 c v3"
      using IH3 outer(3) by simp
    have no_prefix': "s3 @ rev cs @ s4 \<notin> L ?prefix"
      using no_prefix seq_s sres_eq by simp
    have no_capture': "s3 @ rev cs @ s4 \<notin> L ?capture"
      using no_capture seq_s sres_eq by simp
    have no_longer':
      "\<not> (\<exists>x y. x \<noteq> [] \<and> x @ y = rev cs @ s4 \<and>
        s3 @ x \<in> L (der c r3) \<and> y \<in> L ?mid)"
      using no_longer sres_eq by simp
    have longest: "BACKREF4_longest r1 r2 r3 r4 cs [] [] (c # s3) s4"
      using BACKREF4_longest_tail3_inj[OF no_prefix' no_capture' no_longer'] .
    have "([] @ [] @ (c # s3) @ rev cs @ [] @ s4) \<in>
      BACKREF4 r1 r2 r3 r4 cs \<rightarrow>
        Backref4 (mkeps r1) (mkeps r2) (injval r3 c v3) v4 cs"
      using Posix_BACKREF4[OF eps1 eps2 r3pos inner(4) longest] by simp
    then show "(c # s) \<in> BACKREF4 r1 r2 r3 r4 cs \<rightarrow>
      injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right w))"
      using seq_s seq_w sres_eq vres_eq by simp
  qed

  have residue_case:
    "\<And>w sr. [] \<in> r1 \<rightarrow> mkeps r1 \<Longrightarrow> nullable r2 \<Longrightarrow> nullable r3 \<Longrightarrow> rev cs = c # sr \<Longrightarrow>
      s \<notin> L ?prefix \<Longrightarrow> s \<notin> L ?capture \<Longrightarrow>
      s \<notin> L (SEQ (der c r3) ?mid) \<Longrightarrow>
      s \<in> SEQ (der_residue c ?res ?res) r4 \<rightarrow> w \<Longrightarrow>
      (c # s) \<in> BACKREF4 r1 r2 r3 r4 cs \<rightarrow>
        injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right (Right w)))"
  proof -
    fix w sr
    assume eps1: "[] \<in> r1 \<rightarrow> mkeps r1" and n2: "nullable r2" and n3: "nullable r3" and res: "rev cs = c # sr"
      and no_prefix: "s \<notin> L ?prefix" and no_capture: "s \<notin> L ?capture"
      and no_tail3: "s \<notin> L (SEQ (der c r3) ?mid)"
      and p: "s \<in> SEQ (der_residue c ?res ?res) r4 \<rightarrow> w"
    then obtain sres s4 vres v4 where parts:
      "s = sres @ s4" "w = Seq vres v4"
      "sres \<in> der_residue c ?res ?res \<rightarrow> vres" "s4 \<in> r4 \<rightarrow> v4"
      by (elim Posix_elims(5)) auto
    then have sres: "sres = sr"
      using Posix_der_residue_string res by fastforce
    have residue_val: "inj_residue ?res ?res c vres = Residue ?res ?res"
      using parts(3) by (rule Posix_der_residue_inj)
    have eps2: "[] \<in> r2 \<rightarrow> mkeps r2"
      using n2 by (rule Posix_mkeps)
    have eps3: "[] \<in> r3 \<rightarrow> mkeps r3"
      using n3 by (rule Posix_mkeps)
    have longest: "BACKREF4_longest r1 r2 r3 r4 cs [] [] [] s4"
      using BACKREF4_longest_tail_residue_inj[OF res] no_prefix no_capture no_tail3
        parts(1) sres by simp
    have "([] @ [] @ [] @ rev cs @ [] @ s4) \<in>
      BACKREF4 r1 r2 r3 r4 cs \<rightarrow>
        Backref4 (mkeps r1) (mkeps r2) (mkeps r3) v4 cs"
      using Posix_BACKREF4[OF eps1 eps2 eps3 parts(4) longest] by simp
    then show "(c # s) \<in> BACKREF4 r1 r2 r3 r4 cs \<rightarrow>
      injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right (Right w)))"
      using parts res sres residue_val by simp
  qed

  have tail4_case:
    "\<And>w. [] \<in> r1 \<rightarrow> mkeps r1 \<Longrightarrow> nullable r2 \<Longrightarrow> nullable r3 \<Longrightarrow> rev cs = [] \<Longrightarrow>
      s \<notin> L ?prefix \<Longrightarrow> s \<notin> L ?capture \<Longrightarrow>
      s \<notin> L (SEQ (der c r3) ?mid) \<Longrightarrow>
      s \<in> der c r4 \<rightarrow> w \<Longrightarrow>
      (c # s) \<in> BACKREF4 r1 r2 r3 r4 cs \<rightarrow>
        injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right (Right (Right w))))"
  proof -
    fix w
    assume eps1: "[] \<in> r1 \<rightarrow> mkeps r1" and n2: "nullable r2" and n3: "nullable r3" and empty: "rev cs = []"
      and no_prefix: "s \<notin> L ?prefix" and no_capture: "s \<notin> L ?capture"
      and no_tail3: "s \<notin> L (SEQ (der c r3) ?mid)"
      and p: "s \<in> der c r4 \<rightarrow> w"
    have eps2: "[] \<in> r2 \<rightarrow> mkeps r2"
      using n2 by (rule Posix_mkeps)
    have eps3: "[] \<in> r3 \<rightarrow> mkeps r3"
      using n3 by (rule Posix_mkeps)
    have r4pos: "(c # s) \<in> r4 \<rightarrow> injval r4 c w"
      using IH4 p by simp
    have longest: "BACKREF4_longest r1 r2 r3 r4 cs [] [] [] (c # s)"
      using BACKREF4_longest_tail4_inj[OF empty] no_prefix no_capture no_tail3 by simp
    have "([] @ [] @ [] @ rev cs @ [] @ (c # s)) \<in>
      BACKREF4 r1 r2 r3 r4 cs \<rightarrow>
        Backref4 (mkeps r1) (mkeps r2) (mkeps r3) (injval r4 c w) cs"
      using Posix_BACKREF4[OF eps1 eps2 eps3 r4pos longest] by simp
    then show "(c # s) \<in> BACKREF4 r1 r2 r3 r4 cs \<rightarrow>
      injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right (Right (Right w))))"
      using empty by simp
  qed

  show "(c # s) \<in> BACKREF4 r1 r2 r3 r4 cs \<rightarrow>
      injval (BACKREF4 r1 r2 r3 r4 cs) c v"
  proof (cases "nullable r1")
    case False
    then have "s \<in> ?prefix \<rightarrow> v"
      using prem by (simp add: Let_def)
    then show ?thesis
      by (rule prefix_case)
  next
    case n1: True
    have eps1: "[] \<in> r1 \<rightarrow> mkeps r1"
      using n1 by (rule Posix_mkeps)
    have alt1: "s \<in> ALT ?prefix ?rest \<rightarrow> v"
      using prem n1 by (simp add: Let_def)
    then consider
      (prefix) w where "v = Left w" "s \<in> ?prefix \<rightarrow> w"
    | (rest) w where "v = Right w" "s \<in> ?rest \<rightarrow> w" "s \<notin> L ?prefix"
      by (erule Posix_elims) auto
    then show ?thesis
    proof cases
      case prefix
      have inj_left:
        "injval (BACKREF4 r1 r2 r3 r4 cs) c (Left w) =
          injval (BACKREF4 r1 r2 r3 r4 cs) c w"
        using prefix(2) by (auto elim!: Posix_elims(8))
      then show ?thesis
        using prefix prefix_case[OF prefix(2)] by simp
    next
      case (rest w)
      show ?thesis
      proof (cases "nullable r2")
        case False
        then have "s \<in> ?capture \<rightarrow> w"
          using rest by simp
        then show ?thesis
          using capture_case[OF eps1 rest(3)] rest by simp
      next
        case n2: True
        then have alt2: "s \<in> ALT ?capture ?tail \<rightarrow> w"
          using rest by simp
        then consider
          (capture) wc where "w = Left wc" "s \<in> ?capture \<rightarrow> wc"
        | (tail) wt where "w = Right wt" "s \<in> ?tail \<rightarrow> wt" "s \<notin> L ?capture"
          by (erule Posix_elims) auto
        then show ?thesis
        proof cases
          case capture
          have inj_capture_left:
            "injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Left wc)) =
              injval (BACKREF4 r1 r2 r3 r4 cs) c (Right wc)"
            using capture(2) by (auto elim!: Posix_elims(8))
          then show ?thesis
            using capture capture_case[OF eps1 rest(3) capture(2)] rest by simp
        next
          case (tail wt)
          show ?thesis
          proof (cases "nullable r3")
            case False
            then have p: "s \<in> SEQ (der c r3) ?mid \<rightarrow> wt"
              using tail by simp
            then show ?thesis
              using tail3_case[OF eps1 n2 rest(3) tail(3) p] rest tail by simp
          next
            case n3: True
            then have alt3: "s \<in> ALT (SEQ (der c r3) ?mid) ?res_tail \<rightarrow> wt"
              using tail by simp
            then consider
              (tail3) w3 where "wt = Left w3" "s \<in> SEQ (der c r3) ?mid \<rightarrow> w3"
            | (residue) wr where "wt = Right wr" "s \<in> ?res_tail \<rightarrow> wr"
                "s \<notin> L (SEQ (der c r3) ?mid)"
              by (erule Posix_elims) auto
            then show ?thesis
            proof cases
              case tail3
              have inj_tail3_left:
                "injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right (Left w3))) =
                  injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right w3))"
                using tail3(2) by (auto elim!: Posix_elims(5))
              then show ?thesis
                using tail3 tail3_case[OF eps1 n2 rest(3) tail(3) tail3(2)] rest tail by simp
            next
              case (residue wr)
              show ?thesis
              proof (cases "?res")
                case Nil
                then have alt4:
                  "s \<in> ALT (SEQ (der_residue c ?res ?res) r4) (der c r4) \<rightarrow> wr"
                  using residue by simp
                then consider
                  (impossible) wi where "wr = Left wi"
                    "s \<in> SEQ (der_residue c ?res ?res) r4 \<rightarrow> wi"
                | (tail4) w4 where "wr = Right w4" "s \<in> der c r4 \<rightarrow> w4"
                  by (erule Posix_elims) auto
                then show ?thesis
                proof cases
                  case impossible
                  then show ?thesis
                    using Nil by (auto elim!: Posix_elims)
                next
                  case tail4
                  then show ?thesis
                    using tail4_case[OF eps1 n2 n3 Nil rest(3) tail(3) residue(3) tail4(2)]
                      rest tail residue Nil by simp
                qed
              next
                case (Cons a list)
                then have p: "s \<in> SEQ (der_residue c ?res ?res) r4 \<rightarrow> wr"
                  using residue by simp
                have res': "rev cs = c # list"
                  using p Cons by (auto split: if_splits elim!: Posix_elims)
                then show ?thesis
                  using residue_case[OF eps1 n2 n3 res' rest(3) tail(3) residue(3) p]
                    rest tail residue by simp
              qed
            qed
          qed
        qed
      qed
    qed
  qed
next
  case (HALF r cs rep)
  have IH: "\<And>s v. s \<in> der c r \<rightarrow> v \<Longrightarrow> (c # s) \<in> r \<rightarrow> injval r c v"
    by fact
  have prem: "s \<in> der c (HALF r cs rep) \<rightarrow> v"
    by fact
  show "(c # s) \<in> HALF r cs rep \<rightarrow> injval (HALF r cs rep) c v"
  proof (cases "nullable r")
    case False
    then have "s \<in> HALF (der c r) cs rep \<rightarrow> v"
      using prem by simp
    then obtain s0 v0 where half:
      "s = s0 @ cs" "v = Half v0 cs rep" "s0 \<in> der c r \<rightarrow> v0"
      by cases auto
    then have "(c # s0) \<in> r \<rightarrow> injval r c v0"
      using IH by simp
    then have "((c # s0) @ cs) \<in> HALF r cs rep \<rightarrow> Half (injval r c v0) cs rep"
      by (rule Posix_HALF)
    then show ?thesis
      using half by simp
  next
    case True
    then have alt: "s \<in> ALT (HALF (der c r) cs rep) (der_residue c cs rep) \<rightarrow> v"
      using prem by simp
    then consider
      (left) s0 v0 where
        "v = Left (Half v0 cs rep)" "s = s0 @ cs" "s0 \<in> der c r \<rightarrow> v0"
    | (right) vr where "v = Right vr" "s \<in> der_residue c cs rep \<rightarrow> vr"
      using alt
      apply cases
      apply (auto elim!: Posix_elims)
      done
    then show ?thesis
    proof cases
      case left
      then have "(c # s0) \<in> r \<rightarrow> injval r c v0"
        using IH by simp
      then have "((c # s0) @ cs) \<in> HALF r cs rep \<rightarrow> Half (injval r c v0) cs rep"
        by (rule Posix_HALF)
      then show ?thesis
        using left by simp
    next
      case right
      then have "(c # s) \<in> HALF r cs rep \<rightarrow>
        (case inj_residue cs rep c vr of Residue ds rep' \<Rightarrow> Half (mkeps r) cs rep | _ \<Rightarrow> Void)"
        using True by (intro Posix_der_residue_half_inj)
      then show ?thesis
        using right by simp
    qed
  qed
next
  case (RESIDUE cs rep)
  have cs_eq: "cs = c # s"
    using RESIDUE
    by (simp add: Posix_der_residue_string)
  have residue: "inj_residue cs rep c v = Residue cs rep"
    using RESIDUE by (simp add: Posix_der_residue_inj)
  show "(c # s) \<in> RESIDUE cs rep \<rightarrow> injval (RESIDUE cs rep) c v"
    using cs_eq residue by (simp add: Posix_RESIDUE)
qed


section \<open>Lexer Correctness\<close>


(* BACKREF-MIGRATION-TODO (proof constructor-case extension):
   Recheck and extend the original lexer correctness theorem after
   der/injval/Posix are extended. Wrapper lexer correctness does not count. *)
lemma lexer_correct_None:
  shows "s \<notin> L r \<longleftrightarrow> lexer r s = None"
  apply(induct s arbitrary: r)
  apply(simp)
  apply(simp add: nullable_correctness)
  apply(simp)
  apply(drule_tac x="der a r" in meta_spec) 
  apply(auto)
apply(auto simp add: der_correctness Der_def)
done

(* BACKREF-MIGRATION-TODO (proof constructor-case extension):
   Recheck and extend the original lexer correctness theorem after
   der/injval/Posix are extended. Wrapper lexer correctness does not count. *)
lemma lexer_correct_Some:
  shows "s \<in> L r \<longleftrightarrow> (\<exists>v. lexer r s = Some(v) \<and> s \<in> r \<rightarrow> v)"
  apply(induct s arbitrary : r)
  apply(simp only: lexer.simps)
  apply(simp)
  apply(simp add: nullable_correctness Posix_mkeps)
  apply(drule_tac x="der a r" in meta_spec)
  apply(simp (no_asm_use) add: der_correctness Der_def del: lexer.simps) 
  apply(simp del: lexer.simps)
  apply(simp only: lexer.simps)
  apply(case_tac "lexer (der a r) s = None")
   apply(auto)[1]
  apply(simp)
  apply(erule exE)
  apply(simp)
  apply(rule iffI)
  apply(simp add: Posix_injval)
  apply(simp add: Posix1(1))
done 

(* BACKREF-MIGRATION-TODO (proof constructor-case extension):
   Recheck and extend the original lexer correctness theorem after
   der/injval/Posix are extended. Wrapper lexer correctness does not count. *)
lemma lexer_correctness:
  shows "(lexer r s = Some v) \<longleftrightarrow> s \<in> r \<rightarrow> v"
  and   "(lexer r s = None) \<longleftrightarrow> \<not>(\<exists>v. s \<in> r \<rightarrow> v)"
using Posix1(1) Posix_determ lexer_correct_None lexer_correct_Some apply fastforce
using Posix1(1) lexer_correct_None lexer_correct_Some by blast


subsection \<open>A slight reformulation of the lexer algorithm using stacked functions\<close>

fun flex :: "rexp \<Rightarrow> (val \<Rightarrow> val) => string \<Rightarrow> (val \<Rightarrow> val)"
  where
  "flex r f [] = f"
| "flex r f (c#s) = flex (der c r) (\<lambda>v. f (injval r c v)) s"  

lemma flex_fun_apply:
  shows "g (flex r f s v) = flex r (g o f) s v"
  apply(induct s arbitrary: g f r v)
  apply(simp_all add: comp_def)
  by meson

lemma flex_fun_apply2:
  shows "g (flex r id s v) = flex r g s v"
  by (simp add: flex_fun_apply)


lemma flex_append:
  shows "flex r f (s1 @ s2) = flex (ders s1 r) (flex r f s1) s2"
  apply(induct s1 arbitrary: s2 r f)
  apply(simp_all)
  done  

lemma lexer_flex:
  shows "lexer r s = (if nullable (ders s r) 
                      then Some(flex r id s (mkeps (ders s r))) else None)"
  apply(induct s arbitrary: r)
  apply(simp_all add: flex_fun_apply)
  done  

lemma Posix_flex:
  assumes "s2 \<in> (ders s1 r) \<rightarrow> v"
  shows "(s1 @ s2) \<in> r \<rightarrow> flex r id s1 v"
  using assms
  apply(induct s1 arbitrary: r v s2)
  apply(simp)
  apply(simp)  
  apply(drule_tac x="der a r" in meta_spec)
  apply(drule_tac x="v" in meta_spec)
  apply(drule_tac x="s2" in meta_spec)
  apply(simp)
  using  Posix_injval
  apply(drule_tac Posix_injval)
  apply(subst (asm) (5) flex_fun_apply)
  apply(simp)
  done

lemma injval_inj_HALF:
  assumes IH: "\<And>a c v. \<lbrakk>\<Turnstile> a : der c r; \<Turnstile> v : der c r;
      injval r c a = injval r c v\<rbrakk> \<Longrightarrow> a = v"
    and A: "\<Turnstile> a : der c (HALF r cs rep)"
    and V: "\<Turnstile> v : der c (HALF r cs rep)"
    and E: "injval (HALF r cs rep) c a = injval (HALF r cs rep) c v"
  shows "a = v"
proof (cases "nullable r")
  case False
  then obtain a0 v0 where av:
    "a = Half a0 cs rep" "\<Turnstile> a0 : der c r"
    "v = Half v0 cs rep" "\<Turnstile> v0 : der c r"
    using A V by (auto elim!: Prf_elims)
  then have "injval r c a0 = injval r c v0"
    using E by simp
  then have "a0 = v0"
    using IH av by blast
  then show ?thesis
    using av by simp
next
  case n: True
  then have Aalt: "\<Turnstile> a : ALT (HALF (der c r) cs rep) (der_residue c cs rep)"
    using A by simp
  then consider
    (a_left) a0 where "a = Left (Half a0 cs rep)" "\<Turnstile> a0 : der c r"
  | (a_right) ar where "a = Right ar" "\<Turnstile> ar : der_residue c cs rep"
    by (auto elim!: Prf_elims)
  then show ?thesis
  proof cases
    case (a_left a0)
    have Valt: "\<Turnstile> v : ALT (HALF (der c r) cs rep) (der_residue c cs rep)"
      using V n by simp
    then consider
      (v_left) v0 where "v = Left (Half v0 cs rep)" "\<Turnstile> v0 : der c r"
    | (v_right) vr where "v = Right vr" "\<Turnstile> vr : der_residue c cs rep"
      by (auto elim!: Prf_elims)
    then show ?thesis
    proof cases
      case (v_left v0)
      then have "injval r c a0 = injval r c v0"
        using E a_left by simp
      then have "a0 = v0"
        using IH a_left v_left by blast
      then show ?thesis
        using a_left v_left by simp
    next
      case (v_right vr)
      have vr_inj: "inj_residue cs rep c vr = Residue cs rep"
        using v_right(2) by (rule Prf_der_residue_inj)
      have eq: "injval r c a0 = mkeps r"
        using E a_left v_right vr_inj by simp
      have "flat (injval r c a0) = c # flat a0"
        using a_left(2) by (rule Prf_injval_flat)
      moreover have "flat (injval r c a0) = flat (mkeps r)"
        using eq by simp
      ultimately have "c # flat a0 = []"
        using n by (simp add: mkeps_flat)
      then show ?thesis by simp
    qed
  next
    case (a_right ar)
    have Valt: "\<Turnstile> v : ALT (HALF (der c r) cs rep) (der_residue c cs rep)"
    using V n by simp
    then consider
      (v_left) v0 where "v = Left (Half v0 cs rep)" "\<Turnstile> v0 : der c r"
    | (v_right) vr where "v = Right vr" "\<Turnstile> vr : der_residue c cs rep"
      by (auto elim!: Prf_elims)
    then show ?thesis
    proof cases
      case (v_left v0)
      have ar_inj: "inj_residue cs rep c ar = Residue cs rep"
        using a_right(2) by (rule Prf_der_residue_inj)
      have eq: "mkeps r = injval r c v0"
        using E a_right v_left ar_inj by simp
      have "flat (injval r c v0) = c # flat v0"
        using v_left(2) by (rule Prf_injval_flat)
      moreover have "flat (mkeps r) = flat (injval r c v0)"
        using eq by simp
      ultimately have "[] = c # flat v0"
        using n by (simp add: mkeps_flat)
      then show ?thesis by simp
    next
      case (v_right vr)
      have "ar = vr"
        using a_right(2) v_right(2) by (rule Prf_der_residue_unique)
      then show ?thesis
        using a_right v_right by simp
    qed
  qed
qed

lemma injval_mkeps_False:
  assumes n: "nullable r"
    and p: "\<Turnstile> v : der c r"
    and eq: "injval r c v = mkeps r"
  shows False
proof -
  have "flat (injval r c v) = c # flat v"
    using p by (rule Prf_injval_flat)
  moreover have "flat (mkeps r) = []"
    using n by (rule mkeps_flat)
  ultimately show False
    using eq by simp
qed

lemma Prf_ALT_SEQ_der_shape:
  assumes "\<Turnstile> v : ALT (SEQ (der c r1) r2) (der c r2)"
  obtains v1 v2 where "v = Left (Seq v1 v2)" "\<Turnstile> v1 : der c r1" "\<Turnstile> v2 : r2"
        | v2 where "v = Right v2" "\<Turnstile> v2 : der c r2"
  using assms
  by (auto elim!: Prf_elims)

lemma injval_inj_SEQ:
  assumes IH1: "\<And>a c v. \<lbrakk>\<Turnstile> a : der c r1; \<Turnstile> v : der c r1;
      injval r1 c a = injval r1 c v\<rbrakk> \<Longrightarrow> a = v"
    and IH2: "\<And>a c v. \<lbrakk>\<Turnstile> a : der c r2; \<Turnstile> v : der c r2;
      injval r2 c a = injval r2 c v\<rbrakk> \<Longrightarrow> a = v"
    and A: "\<Turnstile> a : der c (SEQ r1 r2)"
    and V: "\<Turnstile> v : der c (SEQ r1 r2)"
    and E: "injval (SEQ r1 r2) c a = injval (SEQ r1 r2) c v"
  shows "a = v"
proof (cases "nullable r1")
  case False
  then have Aseq: "\<Turnstile> a : SEQ (der c r1) r2"
    using A by simp
  then obtain a1 a2 where av:
    "a = Seq a1 a2" "\<Turnstile> a1 : der c r1" "\<Turnstile> a2 : r2"
    by (auto elim: Prf_elims(2))
  have Vseq: "\<Turnstile> v : SEQ (der c r1) r2"
    using V False by simp
  then obtain v1 v2 where vv:
    "v = Seq v1 v2" "\<Turnstile> v1 : der c r1" "\<Turnstile> v2 : r2"
    by (auto elim: Prf_elims(2))
  have eqs: "injval r1 c a1 = injval r1 c v1" "a2 = v2"
    using E av vv by simp_all
  then have "a1 = v1"
    using IH1 av vv by blast
  then show ?thesis
    using av vv eqs by simp
next
  case n: True
  then have Aalt: "\<Turnstile> a : ALT (SEQ (der c r1) r2) (der c r2)"
    using A by simp
  from Aalt consider
    (a_left) a1 a2 where "a = Left (Seq a1 a2)" "\<Turnstile> a1 : der c r1" "\<Turnstile> a2 : r2"
  | (a_right) a2 where "a = Right a2" "\<Turnstile> a2 : der c r2"
    by (rule Prf_ALT_SEQ_der_shape)
  then show ?thesis
  proof cases
    case (a_left a1 a2)
    have Valt: "\<Turnstile> v : ALT (SEQ (der c r1) r2) (der c r2)"
      using V n by simp
    from Valt consider
      (v_left) v1 v2 where "v = Left (Seq v1 v2)" "\<Turnstile> v1 : der c r1" "\<Turnstile> v2 : r2"
    | (v_right) v2 where "v = Right v2" "\<Turnstile> v2 : der c r2"
      by (rule Prf_ALT_SEQ_der_shape)
    then show ?thesis
    proof cases
      case (v_left v1 v2)
      have eqs: "injval r1 c a1 = injval r1 c v1" "a2 = v2"
        using E a_left v_left by simp_all
      then have "a1 = v1"
        using IH1 a_left v_left by blast
      then show ?thesis
        using a_left v_left eqs by simp
    next
      case (v_right v2)
      have "injval r1 c a1 = mkeps r1"
        using E a_left v_right by simp
      then show ?thesis
        using injval_mkeps_False[OF n a_left(2)] by simp
    qed
  next
    case (a_right a2)
    have Valt: "\<Turnstile> v : ALT (SEQ (der c r1) r2) (der c r2)"
      using V n by simp
    from Valt consider
      (v_left) v1 v2 where "v = Left (Seq v1 v2)" "\<Turnstile> v1 : der c r1" "\<Turnstile> v2 : r2"
    | (v_right) v2 where "v = Right v2" "\<Turnstile> v2 : der c r2"
      by (rule Prf_ALT_SEQ_der_shape)
    then show ?thesis
    proof cases
      case (v_left v1 v2)
      have "mkeps r1 = injval r1 c v1"
        using E a_right v_left by simp
      then show ?thesis
        using injval_mkeps_False[OF n v_left(2)] by simp
    next
      case (v_right v2)
      have "injval r2 c a2 = injval r2 c v2"
        using E a_right v_right by simp
      then have "a2 = v2"
        using IH2 a_right v_right by blast
      then show ?thesis
        using a_right v_right by simp
    qed
  qed
qed

lemma injval_inj_ALT:
  assumes IH1: "\<And>a c v. \<lbrakk>\<Turnstile> a : der c r1; \<Turnstile> v : der c r1;
      injval r1 c a = injval r1 c v\<rbrakk> \<Longrightarrow> a = v"
    and IH2: "\<And>a c v. \<lbrakk>\<Turnstile> a : der c r2; \<Turnstile> v : der c r2;
      injval r2 c a = injval r2 c v\<rbrakk> \<Longrightarrow> a = v"
    and A: "\<Turnstile> a : der c (ALT r1 r2)"
    and V: "\<Turnstile> v : der c (ALT r1 r2)"
    and E: "injval (ALT r1 r2) c a = injval (ALT r1 r2) c v"
  shows "a = v"
proof -
  have Aalt: "\<Turnstile> a : ALT (der c r1) (der c r2)"
    using A by simp
  from Aalt consider
    (a_left) a1 where "a = Left a1" "\<Turnstile> a1 : der c r1"
  | (a_right) a2 where "a = Right a2" "\<Turnstile> a2 : der c r2"
    by (auto elim: Prf_elims(3))
  then show ?thesis
  proof cases
    case (a_left a1)
    have Valt: "\<Turnstile> v : ALT (der c r1) (der c r2)"
      using V by simp
    from Valt consider
      (v_left) v1 where "v = Left v1" "\<Turnstile> v1 : der c r1"
    | (v_right) v2 where "v = Right v2" "\<Turnstile> v2 : der c r2"
      by (auto elim: Prf_elims(3))
    then show ?thesis
    proof cases
      case (v_left v1)
      then have "a1 = v1"
        using IH1 a_left E by simp
      then show ?thesis
        using a_left v_left by simp
    next
      case v_right
      then show ?thesis
        using E a_left by simp
    qed
  next
    case (a_right a2)
    have Valt: "\<Turnstile> v : ALT (der c r1) (der c r2)"
      using V by simp
    from Valt consider
      (v_left) v1 where "v = Left v1" "\<Turnstile> v1 : der c r1"
    | (v_right) v2 where "v = Right v2" "\<Turnstile> v2 : der c r2"
      by (auto elim: Prf_elims(3))
    then show ?thesis
    proof cases
      case v_left
      then show ?thesis
        using E a_right by simp
    next
      case (v_right v2)
      then have "a2 = v2"
        using IH2 a_right E by simp
      then show ?thesis
        using a_right v_right by simp
    qed
  qed
qed

lemma Prf_STAR_value_shape:
  assumes "\<Turnstile> v : STAR r"
  obtains vs where "v = Stars vs"
  using assms by (auto elim: Prf_elims(6))

lemma Prf_NTIMES_value_shape:
  assumes "\<Turnstile> v : NTIMES r n"
  obtains vs where "v = Stars vs"
  using assms by (auto elim: Prf_elims(7))

lemma injval_inj_STAR:
  assumes IH: "\<And>a c v. \<lbrakk>\<Turnstile> a : der c r; \<Turnstile> v : der c r;
      injval r c a = injval r c v\<rbrakk> \<Longrightarrow> a = v"
    and A: "\<Turnstile> a : der c (STAR r)"
    and V: "\<Turnstile> v : der c (STAR r)"
    and E: "injval (STAR r) c a = injval (STAR r) c v"
  shows "a = v"
proof -
  from A obtain a1 ar where av:
    "a = Seq a1 ar" "\<Turnstile> a1 : der c r" "\<Turnstile> ar : STAR r"
    by (auto elim: Prf_elims(2))
  from av(3) obtain as where ar: "ar = Stars as"
    by (rule Prf_STAR_value_shape)
  from V obtain v1 vr where vv:
    "v = Seq v1 vr" "\<Turnstile> v1 : der c r" "\<Turnstile> vr : STAR r"
    by (auto elim: Prf_elims(2))
  from vv(3) obtain vs where vr: "vr = Stars vs"
    by (rule Prf_STAR_value_shape)
  have eqs: "injval r c a1 = injval r c v1" "as = vs"
    using E av vv ar vr by simp_all
  then have "a1 = v1"
    using IH av vv by blast
  then show ?thesis
    using av vv ar vr eqs by simp
qed

lemma injval_inj_NTIMES:
  assumes IH: "\<And>a c v. \<lbrakk>\<Turnstile> a : der c r; \<Turnstile> v : der c r;
      injval r c a = injval r c v\<rbrakk> \<Longrightarrow> a = v"
    and A: "\<Turnstile> a : der c (NTIMES r n)"
    and V: "\<Turnstile> v : der c (NTIMES r n)"
    and E: "injval (NTIMES r n) c a = injval (NTIMES r n) c v"
  shows "a = v"
proof (cases n)
  case 0
  then have "\<Turnstile> a : ZERO"
    using A by simp
  then show ?thesis
    by (auto elim: Prf_elims(1))
next
  case (Suc m)
  then have Aseq: "\<Turnstile> a : SEQ (der c r) (NTIMES r m)"
    using A by simp
  from Aseq obtain a1 ar where av:
    "a = Seq a1 ar" "\<Turnstile> a1 : der c r" "\<Turnstile> ar : NTIMES r m"
    by (auto elim: Prf_elims(2))
  from av(3) obtain as where ar: "ar = Stars as"
    by (rule Prf_NTIMES_value_shape)
  have Vseq: "\<Turnstile> v : SEQ (der c r) (NTIMES r m)"
    using V Suc by simp
  from Vseq obtain v1 vr where vv:
    "v = Seq v1 vr" "\<Turnstile> v1 : der c r" "\<Turnstile> vr : NTIMES r m"
    by (auto elim: Prf_elims(2))
  from vv(3) obtain vs where vr: "vr = Stars vs"
    by (rule Prf_NTIMES_value_shape)
  have eqs: "injval r c a1 = injval r c v1" "as = vs"
    using E av vv ar vr by simp_all
  then have "a1 = v1"
    using IH av vv by blast
  then show ?thesis
    using av vv ar vr eqs by simp
qed

lemma injval_inj_BACKREF4_prefix:
  assumes IH: "\<And>a c v. \<lbrakk>\<Turnstile> a : der c r1; \<Turnstile> v : der c r1;
      injval r1 c a = injval r1 c v\<rbrakk> \<Longrightarrow> a = v"
    and A: "\<Turnstile> a : BACKREF4 (der c r1) r2 r3 r4 cs"
    and V: "\<Turnstile> v : BACKREF4 (der c r1) r2 r3 r4 cs"
    and E: "injval (BACKREF4 r1 r2 r3 r4 cs) c a =
      injval (BACKREF4 r1 r2 r3 r4 cs) c v"
  shows "a = v"
proof -
  from A obtain a1 a2 a3 a4 where av:
    "a = Backref4 a1 a2 a3 a4 cs"
    "\<Turnstile> a1 : der c r1" "\<Turnstile> a2 : r2" "\<Turnstile> a3 : r3" "\<Turnstile> a4 : r4"
    by (auto elim!: Prf_elims)
  from V obtain v1 v2 v3 v4 where vv:
    "v = Backref4 v1 v2 v3 v4 cs"
    "\<Turnstile> v1 : der c r1" "\<Turnstile> v2 : r2" "\<Turnstile> v3 : r3" "\<Turnstile> v4 : r4"
    by (auto elim!: Prf_elims)
  have eqs:
    "injval r1 c a1 = injval r1 c v1" "a2 = v2" "a3 = v3" "a4 = v4"
    using E av vv by simp_all
  then have "a1 = v1"
    using IH av vv by blast
  then show ?thesis
    using av vv eqs by simp
qed

lemma injval_inj_BACKREF4_capture:
  assumes IH: "\<And>a c v. \<lbrakk>\<Turnstile> a : der c r2; \<Turnstile> v : der c r2;
      injval r2 c a = injval r2 c v\<rbrakk> \<Longrightarrow> a = v"
    and A: "\<Turnstile> a : BACKREF4 ONE (der c r2) r3 r4 (c # cs)"
    and V: "\<Turnstile> v : BACKREF4 ONE (der c r2) r3 r4 (c # cs)"
    and E: "injval (BACKREF4 r1 r2 r3 r4 cs) c (Right a) =
      injval (BACKREF4 r1 r2 r3 r4 cs) c (Right v)"
  shows "a = v"
proof -
  from A obtain a2 a3 a4 where av:
    "a = Backref4 Void a2 a3 a4 (c # cs)"
    "\<Turnstile> a2 : der c r2" "\<Turnstile> a3 : r3" "\<Turnstile> a4 : r4"
    by (auto elim!: Prf_elims)
  from V obtain v2 v3 v4 where vv:
    "v = Backref4 Void v2 v3 v4 (c # cs)"
    "\<Turnstile> v2 : der c r2" "\<Turnstile> v3 : r3" "\<Turnstile> v4 : r4"
    by (auto elim!: Prf_elims)
  have eqs:
    "injval r2 c a2 = injval r2 c v2" "a3 = v3" "a4 = v4"
    using E av vv by simp_all
  then have "a2 = v2"
    using IH av vv by blast
  then show ?thesis
    using av vv eqs by simp
qed

lemma injval_inj_BACKREF4_prefix_capture:
  assumes n1: "nullable r1"
    and IH1: "\<And>a c v. \<lbrakk>\<Turnstile> a : der c r1; \<Turnstile> v : der c r1;
      injval r1 c a = injval r1 c v\<rbrakk> \<Longrightarrow> a = v"
    and IH2: "\<And>a c v. \<lbrakk>\<Turnstile> a : der c r2; \<Turnstile> v : der c r2;
      injval r2 c a = injval r2 c v\<rbrakk> \<Longrightarrow> a = v"
    and A: "\<Turnstile> a : ALT (BACKREF4 (der c r1) r2 r3 r4 cs)
      (BACKREF4 ONE (der c r2) r3 r4 (c # cs))"
    and V: "\<Turnstile> v : ALT (BACKREF4 (der c r1) r2 r3 r4 cs)
      (BACKREF4 ONE (der c r2) r3 r4 (c # cs))"
    and E: "injval (BACKREF4 r1 r2 r3 r4 cs) c a =
      injval (BACKREF4 r1 r2 r3 r4 cs) c v"
  shows "a = v"
proof -
  from A consider
    (a_prefix) ap where "a = Left ap" "\<Turnstile> ap : BACKREF4 (der c r1) r2 r3 r4 cs"
  | (a_capture) ac where "a = Right ac" "\<Turnstile> ac : BACKREF4 ONE (der c r2) r3 r4 (c # cs)"
    by (auto elim: Prf_elims(3))
  then show ?thesis
  proof cases
    case (a_prefix ap)
    from V consider
      (v_prefix) vp where "v = Left vp" "\<Turnstile> vp : BACKREF4 (der c r1) r2 r3 r4 cs"
    | (v_capture) vc where "v = Right vc" "\<Turnstile> vc : BACKREF4 ONE (der c r2) r3 r4 (c # cs)"
      by (auto elim: Prf_elims(3))
    then show ?thesis
    proof cases
      case (v_prefix vp)
      have left_ap: "injval (BACKREF4 r1 r2 r3 r4 cs) c (Left ap) =
        injval (BACKREF4 r1 r2 r3 r4 cs) c ap"
        using a_prefix(2) by (auto elim!: Prf_elims)
      have left_vp: "injval (BACKREF4 r1 r2 r3 r4 cs) c (Left vp) =
        injval (BACKREF4 r1 r2 r3 r4 cs) c vp"
        using v_prefix(2) by (auto elim!: Prf_elims)
      have Eap: "injval (BACKREF4 r1 r2 r3 r4 cs) c ap =
        injval (BACKREF4 r1 r2 r3 r4 cs) c vp"
        using E a_prefix(1) v_prefix(1) left_ap left_vp by simp
      have "ap = vp"
        using injval_inj_BACKREF4_prefix[OF IH1 a_prefix(2) v_prefix(2) Eap] .
      then show ?thesis using a_prefix v_prefix by simp
    next
      case (v_capture vc)
      from a_prefix obtain a1 a2 a3 a4 where ap:
        "ap = Backref4 a1 a2 a3 a4 cs" "\<Turnstile> a1 : der c r1"
        by (auto elim!: Prf_elims)
      from v_capture obtain v2 v3 v4 where vc:
        "vc = Backref4 Void v2 v3 v4 (c # cs)" "\<Turnstile> v2 : der c r2"
        by (auto elim!: Prf_elims)
      have "injval r1 c a1 = mkeps r1"
        using E a_prefix(1) v_capture(1) ap vc by simp
      then show ?thesis
        using injval_mkeps_False[OF n1 ap(2)] by simp
    qed
  next
    case (a_capture ac)
    from V consider
      (v_prefix) vp where "v = Left vp" "\<Turnstile> vp : BACKREF4 (der c r1) r2 r3 r4 cs"
    | (v_capture) vc where "v = Right vc" "\<Turnstile> vc : BACKREF4 ONE (der c r2) r3 r4 (c # cs)"
      by (auto elim: Prf_elims(3))
    then show ?thesis
    proof cases
      case (v_prefix vp)
      from a_capture obtain a2 a3 a4 where ac:
        "ac = Backref4 Void a2 a3 a4 (c # cs)" "\<Turnstile> a2 : der c r2"
        by (auto elim!: Prf_elims)
      from v_prefix obtain v1 v2 v3 v4 where vp:
        "vp = Backref4 v1 v2 v3 v4 cs" "\<Turnstile> v1 : der c r1"
        by (auto elim!: Prf_elims)
      have "mkeps r1 = injval r1 c v1"
        using E a_capture(1) v_prefix(1) ac vp by simp
      then show ?thesis
        using injval_mkeps_False[OF n1 vp(2)] by simp
    next
      case (v_capture vc)
      have Eac: "injval (BACKREF4 r1 r2 r3 r4 cs) c (Right ac) =
        injval (BACKREF4 r1 r2 r3 r4 cs) c (Right vc)"
        using E a_capture(1) v_capture(1) by simp
      have "ac = vc"
        using injval_inj_BACKREF4_capture[OF IH2 a_capture(2) v_capture(2) Eac] .
      then show ?thesis using a_capture v_capture by simp
    qed
  qed
qed

lemma injval_inj_BACKREF4_capture_left:
  assumes IH: "\<And>a c v. \<lbrakk>\<Turnstile> a : der c r2; \<Turnstile> v : der c r2;
      injval r2 c a = injval r2 c v\<rbrakk> \<Longrightarrow> a = v"
    and A: "\<Turnstile> a : BACKREF4 ONE (der c r2) r3 r4 (c # cs)"
    and V: "\<Turnstile> v : BACKREF4 ONE (der c r2) r3 r4 (c # cs)"
    and E: "injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Left a)) =
      injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Left v))"
  shows "a = v"
proof -
  have a_eq: "injval (BACKREF4 r1 r2 r3 r4 cs) c (Right a) =
    injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Left a))"
    using A by (auto elim!: Prf_elims)
  have v_eq: "injval (BACKREF4 r1 r2 r3 r4 cs) c (Right v) =
    injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Left v))"
    using V by (auto elim!: Prf_elims)
  have E': "injval (BACKREF4 r1 r2 r3 r4 cs) c (Right a) =
    injval (BACKREF4 r1 r2 r3 r4 cs) c (Right v)"
    using E a_eq v_eq by simp
  show ?thesis
    using injval_inj_BACKREF4_capture[OF IH A V E'] .
qed

lemma injval_inj_BACKREF4_tail3:
  assumes IH: "\<And>a c v. \<lbrakk>\<Turnstile> a : der c r3; \<Turnstile> v : der c r3;
      injval r3 c a = injval r3 c v\<rbrakk> \<Longrightarrow> a = v"
    and A: "\<Turnstile> a : SEQ (der c r3) (SEQ (RESIDUE (rev cs) (rev cs)) r4)"
    and V: "\<Turnstile> v : SEQ (der c r3) (SEQ (RESIDUE (rev cs) (rev cs)) r4)"
    and E: "injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right a)) =
      injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right v))"
  shows "a = v"
proof -
  from A obtain a3 a4 where av:
    "a = Seq a3 (Seq (Residue (rev cs) (rev cs)) a4)"
    "\<Turnstile> a3 : der c r3" "\<Turnstile> a4 : r4"
    by (rule Prf_BACKREF4_tail3_value_shape)
  from V obtain v3 v4 where vv:
    "v = Seq v3 (Seq (Residue (rev cs) (rev cs)) v4)"
    "\<Turnstile> v3 : der c r3" "\<Turnstile> v4 : r4"
    by (rule Prf_BACKREF4_tail3_value_shape)
  have eqs: "injval r3 c a3 = injval r3 c v3" "a4 = v4"
    using E av vv by simp_all
  then have "a3 = v3"
    using IH av vv by blast
  then show ?thesis
    using av vv eqs by simp
qed

lemma injval_inj_BACKREF4_tail3_left:
  assumes IH: "\<And>a c v. \<lbrakk>\<Turnstile> a : der c r3; \<Turnstile> v : der c r3;
      injval r3 c a = injval r3 c v\<rbrakk> \<Longrightarrow> a = v"
    and A: "\<Turnstile> a : SEQ (der c r3) (SEQ (RESIDUE (rev cs) (rev cs)) r4)"
    and V: "\<Turnstile> v : SEQ (der c r3) (SEQ (RESIDUE (rev cs) (rev cs)) r4)"
    and E: "injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right (Left a))) =
      injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right (Left v)))"
  shows "a = v"
proof -
  have a_eq: "injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right a)) =
    injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right (Left a)))"
    using A by (auto elim!: Prf_elims)
  have v_eq: "injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right v)) =
    injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right (Left v)))"
    using V by (auto elim!: Prf_elims)
  have E': "injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right a)) =
    injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right v))"
    using E a_eq v_eq by simp
  show ?thesis
    using injval_inj_BACKREF4_tail3[OF IH A V E'] .
qed

lemma injval_inj_BACKREF4_res_tail:
  assumes IH: "\<And>a c v. \<lbrakk>\<Turnstile> a : der c r4; \<Turnstile> v : der c r4;
      injval r4 c a = injval r4 c v\<rbrakk> \<Longrightarrow> a = v"
    and A: "\<Turnstile> a : (if rev cs = []
      then ALT (SEQ (der_residue c (rev cs) (rev cs)) r4) (der c r4)
      else SEQ (der_residue c (rev cs) (rev cs)) r4)"
    and V: "\<Turnstile> v : (if rev cs = []
      then ALT (SEQ (der_residue c (rev cs) (rev cs)) r4) (der c r4)
      else SEQ (der_residue c (rev cs) (rev cs)) r4)"
    and E: "injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right (Right a))) =
      injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right (Right v)))"
  shows "a = v"
proof (cases "rev cs")
  case Nil
  then have Aalt: "\<Turnstile> a : ALT (SEQ (der_residue c [] []) r4) (der c r4)"
    using A by simp
  from Aalt consider
    (a_bad) ab where "a = Left ab" "\<Turnstile> ab : SEQ (der_residue c [] []) r4"
  | (a_tail4) a4 where "a = Right a4" "\<Turnstile> a4 : der c r4"
    by (auto elim: Prf_elims(3))
  then show ?thesis
  proof cases
    case a_bad
    then show ?thesis
      by (auto elim!: Prf_elims)
  next
    case (a_tail4 a4)
    have Valt: "\<Turnstile> v : ALT (SEQ (der_residue c [] []) r4) (der c r4)"
      using V Nil by simp
    from Valt consider
      (v_bad) vb where "v = Left vb" "\<Turnstile> vb : SEQ (der_residue c [] []) r4"
    | (v_tail4) v4 where "v = Right v4" "\<Turnstile> v4 : der c r4"
      by (auto elim: Prf_elims(3))
    then show ?thesis
    proof cases
      case v_bad
      then show ?thesis
        by (auto elim!: Prf_elims)
    next
      case (v_tail4 v4)
      have "injval r4 c a4 = injval r4 c v4"
        using E Nil a_tail4 v_tail4 by simp
      then have "a4 = v4"
        using IH a_tail4 v_tail4 by blast
      then show ?thesis
        using a_tail4 v_tail4 by simp
    qed
  qed
next
  case (Cons d ds)
  then have Aseq: "\<Turnstile> a : SEQ (der_residue c (rev cs) (rev cs)) r4"
    using A by simp
  from Aseq obtain ar a4 where av:
    "a = Seq ar a4" "\<Turnstile> ar : der_residue c (rev cs) (rev cs)" "\<Turnstile> a4 : r4"
    by (auto elim!: Prf_elims)
  have Vseq: "\<Turnstile> v : SEQ (der_residue c (rev cs) (rev cs)) r4"
    using V Cons by simp
  from Vseq obtain vr v4 where vv:
    "v = Seq vr v4" "\<Turnstile> vr : der_residue c (rev cs) (rev cs)" "\<Turnstile> v4 : r4"
    by (auto elim!: Prf_elims)
  have ar_inj: "inj_residue (rev cs) (rev cs) c ar = Residue (rev cs) (rev cs)"
    using av(2) by (rule Prf_der_residue_inj)
  have vr_inj: "inj_residue (rev cs) (rev cs) c vr = Residue (rev cs) (rev cs)"
    using vv(2) by (rule Prf_der_residue_inj)
  have "ar = vr"
    using av(2) vv(2) by (rule Prf_der_residue_unique)
  moreover have "a4 = v4"
    using E av vv ar_inj vr_inj by simp
  ultimately show ?thesis
    using av vv by simp
qed

lemma injval_inj_BACKREF4_tail3_res_tail_False:
  assumes n3: "nullable r3"
    and A: "\<Turnstile> a : SEQ (der c r3) (SEQ (RESIDUE (rev cs) (rev cs)) r4)"
    and V: "\<Turnstile> v : (if rev cs = []
      then ALT (SEQ (der_residue c (rev cs) (rev cs)) r4) (der c r4)
      else SEQ (der_residue c (rev cs) (rev cs)) r4)"
    and E: "injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right (Left a))) =
      injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right (Right v)))"
  shows False
proof -
  from A obtain a3 a4 where av:
    "a = Seq a3 (Seq (Residue (rev cs) (rev cs)) a4)"
    "\<Turnstile> a3 : der c r3" "\<Turnstile> a4 : r4"
    by (rule Prf_BACKREF4_tail3_value_shape)
  have "injval r3 c a3 = mkeps r3"
  proof (cases "rev cs")
    case Nil
    then have Valt: "\<Turnstile> v : ALT (SEQ (der_residue c [] []) r4) (der c r4)"
      using V by simp
    from Valt consider
      (bad) vb where "v = Left vb" "\<Turnstile> vb : SEQ (der_residue c [] []) r4"
    | (tail4) v4 where "v = Right v4" "\<Turnstile> v4 : der c r4"
      by (auto elim: Prf_elims(3))
    then show ?thesis
    proof cases
      case bad
      then show ?thesis
        by (auto elim!: Prf_elims)
    next
      case tail4
      then show ?thesis
        using E av Nil by simp
    qed
  next
    case (Cons d ds)
    then have Vseq: "\<Turnstile> v : SEQ (der_residue c (rev cs) (rev cs)) r4"
      using V by simp
    from Vseq obtain vr v4 where vv:
      "v = Seq vr v4" "\<Turnstile> vr : der_residue c (rev cs) (rev cs)" "\<Turnstile> v4 : r4"
      by (auto elim!: Prf_elims)
    have vr_inj: "inj_residue (rev cs) (rev cs) c vr = Residue (rev cs) (rev cs)"
      using vv(2) by (rule Prf_der_residue_inj)
    show ?thesis
      using E av vv vr_inj by simp
  qed
  then show False
    using injval_mkeps_False[OF n3 av(2)] by blast
qed

lemma injval_inj_BACKREF4_tail:
  assumes n3: "nullable r3"
    and IH3: "\<And>a c v. \<lbrakk>\<Turnstile> a : der c r3; \<Turnstile> v : der c r3;
      injval r3 c a = injval r3 c v\<rbrakk> \<Longrightarrow> a = v"
    and IH4: "\<And>a c v. \<lbrakk>\<Turnstile> a : der c r4; \<Turnstile> v : der c r4;
      injval r4 c a = injval r4 c v\<rbrakk> \<Longrightarrow> a = v"
    and A: "\<Turnstile> a : ALT (SEQ (der c r3) (SEQ (RESIDUE (rev cs) (rev cs)) r4))
      (if rev cs = []
       then ALT (SEQ (der_residue c (rev cs) (rev cs)) r4) (der c r4)
       else SEQ (der_residue c (rev cs) (rev cs)) r4)"
    and V: "\<Turnstile> v : ALT (SEQ (der c r3) (SEQ (RESIDUE (rev cs) (rev cs)) r4))
      (if rev cs = []
       then ALT (SEQ (der_residue c (rev cs) (rev cs)) r4) (der c r4)
       else SEQ (der_residue c (rev cs) (rev cs)) r4)"
    and E: "injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right a)) =
      injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right v))"
  shows "a = v"
proof -
  let ?tail3 = "SEQ (der c r3) (SEQ (RESIDUE (rev cs) (rev cs)) r4)"
  let ?res_tail = "if rev cs = []
       then ALT (SEQ (der_residue c (rev cs) (rev cs)) r4) (der c r4)
       else SEQ (der_residue c (rev cs) (rev cs)) r4"
  from A consider
    (a_tail3) a3 where "a = Left a3" "\<Turnstile> a3 : ?tail3"
  | (a_res) ar where "a = Right ar" "\<Turnstile> ar : ?res_tail"
    by (auto elim: Prf_elims(3))
  then show ?thesis
  proof cases
    case (a_tail3 a3)
    from V consider
      (v_tail3) v3 where "v = Left v3" "\<Turnstile> v3 : ?tail3"
    | (v_res) vr where "v = Right vr" "\<Turnstile> vr : ?res_tail"
      by (auto elim: Prf_elims(3))
    then show ?thesis
    proof cases
      case (v_tail3 v3)
      have E3: "injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right (Left a3))) =
        injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right (Left v3)))"
        using E a_tail3 v_tail3 by simp
      have "a3 = v3"
        using injval_inj_BACKREF4_tail3_left[OF IH3 a_tail3(2) v_tail3(2) E3] .
      then show ?thesis
        using a_tail3 v_tail3 by simp
    next
      case (v_res vr)
      have E3: "injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right (Left a3))) =
        injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right (Right vr)))"
        using E a_tail3 v_res by simp
      then show ?thesis
        using injval_inj_BACKREF4_tail3_res_tail_False[OF n3 a_tail3(2) v_res(2) E3]
        by simp
    qed
  next
    case (a_res ar)
    from V consider
      (v_tail3) v3 where "v = Left v3" "\<Turnstile> v3 : ?tail3"
    | (v_res) vr where "v = Right vr" "\<Turnstile> vr : ?res_tail"
      by (auto elim: Prf_elims(3))
    then show ?thesis
    proof cases
      case (v_tail3 v3)
      have E3: "injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right (Left v3))) =
        injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right (Right ar)))"
        using E a_res v_tail3 by simp
      then show ?thesis
        using injval_inj_BACKREF4_tail3_res_tail_False[OF n3 v_tail3(2) a_res(2) E3]
        by simp
    next
      case (v_res vr)
      have E4: "injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right (Right ar))) =
        injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right (Right vr)))"
        using E a_res v_res by simp
      have "ar = vr"
        using injval_inj_BACKREF4_res_tail[OF IH4 a_res(2) v_res(2) E4] .
      then show ?thesis
        using a_res v_res by simp
    qed
  qed
qed

lemma injval_inj_BACKREF4_prefix_rest_False:
  assumes n1: "nullable r1"
    and A: "\<Turnstile> a : BACKREF4 (der c r1) r2 r3 r4 cs"
    and V: "\<Turnstile> v : ALT (BACKREF4 ONE (der c r2) r3 r4 (c # cs))
      (if nullable r3
       then ALT (SEQ (der c r3) (SEQ (RESIDUE (rev cs) (rev cs)) r4))
         (if rev cs = []
          then ALT (SEQ (der_residue c (rev cs) (rev cs)) r4) (der c r4)
          else SEQ (der_residue c (rev cs) (rev cs)) r4)
       else SEQ (der c r3) (SEQ (RESIDUE (rev cs) (rev cs)) r4))"
    and E: "injval (BACKREF4 r1 r2 r3 r4 cs) c (Left a) =
      injval (BACKREF4 r1 r2 r3 r4 cs) c (Right v)"
  shows False
proof -
  from A obtain a1 a2 a3 a4 where av:
    "a = Backref4 a1 a2 a3 a4 cs" "\<Turnstile> a1 : der c r1"
    by (auto elim!: Prf_elims)
  have "injval r1 c a1 = mkeps r1"
    using E av V
    by (auto elim!: Prf_elims simp add: Prf_der_residue_inj split: if_splits)
  then show False
    using injval_mkeps_False[OF n1 av(2)] by blast
qed

lemma injval_inj_BACKREF4_capture_tail_False:
  assumes n2: "nullable r2"
    and A: "\<Turnstile> a : BACKREF4 ONE (der c r2) r3 r4 (c # cs)"
    and V: "\<Turnstile> v : (if nullable r3
       then ALT (SEQ (der c r3) (SEQ (RESIDUE (rev cs) (rev cs)) r4))
         (if rev cs = []
          then ALT (SEQ (der_residue c (rev cs) (rev cs)) r4) (der c r4)
          else SEQ (der_residue c (rev cs) (rev cs)) r4)
       else SEQ (der c r3) (SEQ (RESIDUE (rev cs) (rev cs)) r4))"
    and E: "injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Left a)) =
      injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right v))"
  shows False
proof -
  from A obtain a2 a3 a4 where av:
    "a = Backref4 Void a2 a3 a4 (c # cs)" "\<Turnstile> a2 : der c r2"
    by (auto elim!: Prf_elims)
  have "injval r2 c a2 = mkeps r2"
    using E av V
    by (auto elim!: Prf_elims simp add: Prf_der_residue_inj split: if_splits)
  then show False
    using injval_mkeps_False[OF n2 av(2)] by blast
qed

lemma injval_inj_BACKREF4_full:
  assumes n1: "nullable r1"
    and n2: "nullable r2"
    and IH1: "\<And>a c v. \<lbrakk>\<Turnstile> a : der c r1; \<Turnstile> v : der c r1;
      injval r1 c a = injval r1 c v\<rbrakk> \<Longrightarrow> a = v"
    and IH2: "\<And>a c v. \<lbrakk>\<Turnstile> a : der c r2; \<Turnstile> v : der c r2;
      injval r2 c a = injval r2 c v\<rbrakk> \<Longrightarrow> a = v"
    and IH3: "\<And>a c v. \<lbrakk>\<Turnstile> a : der c r3; \<Turnstile> v : der c r3;
      injval r3 c a = injval r3 c v\<rbrakk> \<Longrightarrow> a = v"
    and IH4: "\<And>a c v. \<lbrakk>\<Turnstile> a : der c r4; \<Turnstile> v : der c r4;
      injval r4 c a = injval r4 c v\<rbrakk> \<Longrightarrow> a = v"
    and A: "\<Turnstile> a : ALT (BACKREF4 (der c r1) r2 r3 r4 cs)
      (ALT (BACKREF4 ONE (der c r2) r3 r4 (c # cs))
        (if nullable r3
         then ALT (SEQ (der c r3) (SEQ (RESIDUE (rev cs) (rev cs)) r4))
           (if rev cs = []
            then ALT (SEQ (der_residue c (rev cs) (rev cs)) r4) (der c r4)
            else SEQ (der_residue c (rev cs) (rev cs)) r4)
         else SEQ (der c r3) (SEQ (RESIDUE (rev cs) (rev cs)) r4)))"
    and V: "\<Turnstile> v : ALT (BACKREF4 (der c r1) r2 r3 r4 cs)
      (ALT (BACKREF4 ONE (der c r2) r3 r4 (c # cs))
        (if nullable r3
         then ALT (SEQ (der c r3) (SEQ (RESIDUE (rev cs) (rev cs)) r4))
           (if rev cs = []
            then ALT (SEQ (der_residue c (rev cs) (rev cs)) r4) (der c r4)
            else SEQ (der_residue c (rev cs) (rev cs)) r4)
         else SEQ (der c r3) (SEQ (RESIDUE (rev cs) (rev cs)) r4)))"
    and E: "injval (BACKREF4 r1 r2 r3 r4 cs) c a =
      injval (BACKREF4 r1 r2 r3 r4 cs) c v"
  shows "a = v"
proof -
  let ?prefix = "BACKREF4 (der c r1) r2 r3 r4 cs"
  let ?capture = "BACKREF4 ONE (der c r2) r3 r4 (c # cs)"
  let ?tail = "if nullable r3
         then ALT (SEQ (der c r3) (SEQ (RESIDUE (rev cs) (rev cs)) r4))
           (if rev cs = []
            then ALT (SEQ (der_residue c (rev cs) (rev cs)) r4) (der c r4)
            else SEQ (der_residue c (rev cs) (rev cs)) r4)
         else SEQ (der c r3) (SEQ (RESIDUE (rev cs) (rev cs)) r4)"
  from A consider
    (a_prefix) ap where "a = Left ap" "\<Turnstile> ap : ?prefix"
  | (a_rest) ar where "a = Right ar" "\<Turnstile> ar : ALT ?capture ?tail"
    by (auto elim: Prf_elims(3))
  then show ?thesis
  proof cases
    case (a_prefix ap)
    from V consider
      (v_prefix) vp where "v = Left vp" "\<Turnstile> vp : ?prefix"
    | (v_rest) vr where "v = Right vr" "\<Turnstile> vr : ALT ?capture ?tail"
      by (auto elim: Prf_elims(3))
    then show ?thesis
    proof cases
      case (v_prefix vp)
      have left_ap: "injval (BACKREF4 r1 r2 r3 r4 cs) c (Left ap) =
        injval (BACKREF4 r1 r2 r3 r4 cs) c ap"
        using a_prefix(2) by (auto elim!: Prf_elims)
      have left_vp: "injval (BACKREF4 r1 r2 r3 r4 cs) c (Left vp) =
        injval (BACKREF4 r1 r2 r3 r4 cs) c vp"
        using v_prefix(2) by (auto elim!: Prf_elims)
      have Eap: "injval (BACKREF4 r1 r2 r3 r4 cs) c ap =
        injval (BACKREF4 r1 r2 r3 r4 cs) c vp"
        using E a_prefix(1) v_prefix(1) left_ap left_vp by simp
      have "ap = vp"
        using injval_inj_BACKREF4_prefix[OF IH1 a_prefix(2) v_prefix(2) Eap] .
      then show ?thesis
        using a_prefix v_prefix by simp
    next
      case (v_rest vr)
      then show ?thesis
        using injval_inj_BACKREF4_prefix_rest_False[OF n1 a_prefix(2) v_rest(2)]
          E a_prefix(1) v_rest(1)
        by simp
    qed
  next
    case (a_rest ar)
    from V consider
      (v_prefix) vp where "v = Left vp" "\<Turnstile> vp : ?prefix"
    | (v_rest) vr where "v = Right vr" "\<Turnstile> vr : ALT ?capture ?tail"
      by (auto elim: Prf_elims(3))
    then show ?thesis
    proof cases
      case (v_prefix vp)
      have E': "injval (BACKREF4 r1 r2 r3 r4 cs) c (Left vp) =
        injval (BACKREF4 r1 r2 r3 r4 cs) c (Right ar)"
        using E a_rest(1) v_prefix(1) by simp
      then show ?thesis
        using injval_inj_BACKREF4_prefix_rest_False[OF n1 v_prefix(2) a_rest(2) E']
        by simp
    next
      case (v_rest vr)
      from a_rest(2) consider
        (a_capture) ac where "ar = Left ac" "\<Turnstile> ac : ?capture"
      | (a_tail) at where "ar = Right at" "\<Turnstile> at : ?tail"
        by (auto elim: Prf_elims(3))
      then show ?thesis
      proof cases
        case (a_capture ac)
        from v_rest(2) consider
          (v_capture) vc where "vr = Left vc" "\<Turnstile> vc : ?capture"
        | (v_tail) vt where "vr = Right vt" "\<Turnstile> vt : ?tail"
          by (auto elim: Prf_elims(3))
        then show ?thesis
        proof cases
          case (v_capture vc)
          have Ecap: "injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Left ac)) =
            injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Left vc))"
            using E a_rest(1) v_rest(1) a_capture(1) v_capture(1) by simp
          have "ac = vc"
            using injval_inj_BACKREF4_capture_left[OF IH2 a_capture(2) v_capture(2) Ecap] .
          then show ?thesis
            using a_rest v_rest a_capture v_capture by simp
        next
          case (v_tail vt)
          have Ecap: "injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Left ac)) =
            injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right vt))"
            using E a_rest(1) v_rest(1) a_capture(1) v_tail(1) by simp
          then show ?thesis
            using injval_inj_BACKREF4_capture_tail_False[OF n2 a_capture(2) v_tail(2) Ecap]
            by simp
        qed
      next
        case (a_tail at)
        from v_rest(2) consider
          (v_capture) vc where "vr = Left vc" "\<Turnstile> vc : ?capture"
        | (v_tail) vt where "vr = Right vt" "\<Turnstile> vt : ?tail"
          by (auto elim: Prf_elims(3))
        then show ?thesis
        proof cases
          case (v_capture vc)
          have Ecap: "injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Left vc)) =
            injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right at))"
            using E a_rest(1) v_rest(1) a_tail(1) v_capture(1) by simp
          then show ?thesis
            using injval_inj_BACKREF4_capture_tail_False[OF n2 v_capture(2) a_tail(2) Ecap]
            by simp
        next
          case (v_tail vt)
          show ?thesis
          proof (cases "nullable r3")
            case False
            have At: "\<Turnstile> at : SEQ (der c r3) (SEQ (RESIDUE (rev cs) (rev cs)) r4)"
              using a_tail(2) False by simp
            have Vt: "\<Turnstile> vt : SEQ (der c r3) (SEQ (RESIDUE (rev cs) (rev cs)) r4)"
              using v_tail(2) False by simp
            have Et: "injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right at)) =
              injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right vt))"
              using E a_rest(1) v_rest(1) a_tail(1) v_tail(1) by simp
            have "at = vt"
              using injval_inj_BACKREF4_tail3[OF IH3 At Vt Et] .
            then show ?thesis
              using a_rest v_rest a_tail v_tail by simp
          next
            case n3: True
            have At: "\<Turnstile> at : ALT
              (SEQ (der c r3) (SEQ (RESIDUE (rev cs) (rev cs)) r4))
              (if rev cs = []
               then ALT (SEQ (der_residue c (rev cs) (rev cs)) r4) (der c r4)
               else SEQ (der_residue c (rev cs) (rev cs)) r4)"
              using a_tail(2) n3 by simp
            have Vt: "\<Turnstile> vt : ALT
              (SEQ (der c r3) (SEQ (RESIDUE (rev cs) (rev cs)) r4))
              (if rev cs = []
               then ALT (SEQ (der_residue c (rev cs) (rev cs)) r4) (der c r4)
               else SEQ (der_residue c (rev cs) (rev cs)) r4)"
              using v_tail(2) n3 by simp
            have Et: "injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right at)) =
              injval (BACKREF4 r1 r2 r3 r4 cs) c (Right (Right vt))"
              using E a_rest(1) v_rest(1) a_tail(1) v_tail(1) by simp
            have "at = vt"
              using injval_inj_BACKREF4_tail[OF n3 IH3 IH4 At Vt Et] .
            then show ?thesis
              using a_rest v_rest a_tail v_tail by simp
          qed
        qed
      qed
    qed
  qed
qed

(* BACKREF-MIGRATION-TODO (proof constructor-case extension):
   Extend this supporting original lexer proof with BACKREF4/HALF/RESIDUE cases. *)
lemma injval_inj:
  assumes "\<Turnstile> a : (der c r)" "\<Turnstile> v : (der c r)" "injval r c a = injval r c v" 
  shows "a = v"
  using assms
proof (induct r arbitrary: a c v)
  case ZERO
  then show ?case by (auto elim: Prf_elims(1))
next
  case ONE
  then show ?case by (auto elim: Prf_elims(1))
next
  case (CH x)
  then show ?case by (cases "c = x") (auto elim: Prf_elims)
next
  case (SEQ r1 r2)
  then show ?case
    by (rule injval_inj_SEQ)
next
  case (ALT r1 r2)
  then show ?case
    by (rule injval_inj_ALT)
next
  case (STAR r)
  then show ?case
    by (rule injval_inj_STAR)
next
  case (NTIMES r n)
  then show ?case
    by (rule injval_inj_NTIMES)
next
  case (BACKREF4 r1 r2 r3 r4 cs)
  let ?prefix = "BACKREF4 (der c r1) r2 r3 r4 cs"
  let ?capture = "BACKREF4 ONE (der c r2) r3 r4 (c # cs)"
  let ?res = "rev cs"
  let ?res_tail =
    "if ?res = []
     then ALT (SEQ (der_residue c ?res ?res) r4) (der c r4)
     else SEQ (der_residue c ?res ?res) r4"
  let ?tail =
    "if nullable r3
     then ALT (SEQ (der c r3) (SEQ (RESIDUE ?res ?res) r4)) ?res_tail
     else SEQ (der c r3) (SEQ (RESIDUE ?res ?res) r4)"
  show ?case
  proof (cases "nullable r1")
    case False
    have A: "\<Turnstile> a : ?prefix"
      using BACKREF4.prems(1) False by (simp add: Let_def)
    have V: "\<Turnstile> v : ?prefix"
      using BACKREF4.prems(2) False by (simp add: Let_def)
    show ?thesis
      using injval_inj_BACKREF4_prefix[OF BACKREF4.hyps(1) A V BACKREF4.prems(3)] .
  next
    case n1: True
    show ?thesis
    proof (cases "nullable r2")
      case False
      have A: "\<Turnstile> a : ALT ?prefix ?capture"
        using BACKREF4.prems(1) n1 False by (simp add: Let_def)
      have V: "\<Turnstile> v : ALT ?prefix ?capture"
        using BACKREF4.prems(2) n1 False by (simp add: Let_def)
      show ?thesis
        using injval_inj_BACKREF4_prefix_capture
          [OF n1 BACKREF4.hyps(1) BACKREF4.hyps(2) A V BACKREF4.prems(3)] .
    next
      case n2: True
      have A: "\<Turnstile> a : ALT ?prefix (ALT ?capture ?tail)"
        using BACKREF4.prems(1) n1 n2 by (simp add: Let_def)
      have V: "\<Turnstile> v : ALT ?prefix (ALT ?capture ?tail)"
        using BACKREF4.prems(2) n1 n2 by (simp add: Let_def)
      show ?thesis
        using injval_inj_BACKREF4_full
          [OF n1 n2 BACKREF4.hyps(1) BACKREF4.hyps(2) BACKREF4.hyps(3) BACKREF4.hyps(4)
            A V BACKREF4.prems(3)] .
    qed
  qed
next
  case (HALF r cs rep)
  then show ?case
    by (rule injval_inj_HALF)
next
  case (RESIDUE cs rep)
  then show ?case
    using Prf_der_residue_unique[of a c cs rep v] by simp
qed


(* BACKREF-MIGRATION-TODO (proof constructor-case extension):
   Extend this supporting original lexer proof with BACKREF4/HALF/RESIDUE cases. *)
lemma uu:
  assumes "(c # s) \<in> r \<rightarrow> injval r c v" "\<Turnstile> v : (der c r)"
  shows "s \<in> der c r \<rightarrow> v"
  using assms
  apply -
  apply(subgoal_tac "lexer r (c # s) = Some (injval r c v)")
  prefer 2
  using lexer_correctness(1) apply blast
  apply(simp add: )
  apply(case_tac  "lexer (der c r) s")
   apply(simp)
  apply(simp)
  apply(case_tac "s \<in> der c r \<rightarrow> a")
   prefer 2
   apply (simp add: lexer_correctness(1))
  apply(subgoal_tac "\<Turnstile> a : (der c r)")
   prefer 2
  using Posix1a apply blast
  using injval_inj by blast
  

(* BACKREF-MIGRATION-TODO (proof constructor-case extension):
   Extend this supporting original lexer proof with BACKREF4/HALF/RESIDUE cases. *)
lemma Posix_flex2:
  assumes "(s1 @ s2) \<in> r \<rightarrow> flex r id s1 v" "\<Turnstile> v : ders s1 r"
  shows "s2 \<in> (ders s1 r) \<rightarrow> v"
  using assms
  apply(induct s1 arbitrary: r v s2 rule: rev_induct)
  apply(simp)
  apply(simp)  
  apply(drule_tac x="r" in meta_spec)
  apply(drule_tac x="injval (ders xs r) x v" in meta_spec)
  apply(drule_tac x="x#s2" in meta_spec)
  apply(simp add: flex_append ders_append)
  using Prf_injval uu by blast

(* BACKREF-MIGRATION-TODO (proof constructor-case extension):
   Extend this supporting original lexer proof with BACKREF4/HALF/RESIDUE cases. *)
lemma Posix_flex3:
  assumes "s1 \<in> r \<rightarrow> flex r id s1 v" "\<Turnstile> v : ders s1 r"
  shows "[] \<in> (ders s1 r) \<rightarrow> v"
  using assms
  by (simp add: Posix_flex2)

lemma flex_injval:
  shows "flex (der a r) (injval r a) s v = injval r a (flex (der a r) id s v)"
  by (simp add: flex_fun_apply)
  
(* BACKREF-MIGRATION-TODO (proof constructor-case extension):
   Extend this supporting original lexer proof with BACKREF4/HALF/RESIDUE cases. *)
lemma Prf_flex:
  assumes "\<Turnstile> v : ders s r"
  shows "\<Turnstile> flex r id s v : r"
  using assms
  apply(induct s arbitrary: v r)
  apply(simp)
  apply(simp)
  by (simp add: Prf_injval flex_injval)

end
