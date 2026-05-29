theory RegLangs
  imports Main "HOL-Library.Sublist"
begin

section \<open>Sequential Composition of Languages\<close>

definition
  Sequ :: "string set \<Rightarrow> string set \<Rightarrow> string set" ("_ ;; _" [100,100] 100)
where 
  "A ;; B = {s1 @ s2 | s1 s2. s1 \<in> A \<and> s2 \<in> B}"

text \<open>Two Simple Properties about Sequential Composition\<close>

lemma Sequ_empty_string [simp]:
  shows "A ;; {[]} = A"
  and   "{[]} ;; A = A"
by (simp_all add: Sequ_def)

lemma Sequ_empty [simp]:
  shows "A ;; {} = {}"
  and   "{} ;; A = {}"
  by (simp_all add: Sequ_def)

lemma concI[simp,intro]: "u : A \<Longrightarrow> v : B \<Longrightarrow> u@v : A ;; B"
by (auto simp add: Sequ_def)

lemma concE[elim]: 
assumes "w \<in> A ;; B"
obtains u v where "u \<in> A" "v \<in> B" "w = u@v"
using assms by (auto simp: Sequ_def)

lemma concI_if_Nil2: "[] \<in> B \<Longrightarrow> xs : A \<Longrightarrow> xs \<in> A ;; B"
by (metis append_Nil2 concI)

lemma conc_assoc: "(A ;; B) ;; C = A ;; (B ;; C)"
by (auto elim!: concE) (simp only: append_assoc[symmetric] concI)


text \<open>Language power operations\<close>

overloading lang_pow == "compow :: nat \<Rightarrow> string set \<Rightarrow> string set"
begin
  primrec lang_pow :: "nat \<Rightarrow> string set \<Rightarrow> string set" where
  "lang_pow 0 A = {[]}" |
  "lang_pow (Suc n) A = A ;; (lang_pow n A)"
end


lemma conc_pow_comm:
  shows "A ;; (A ^^ n) = (A ^^ n) ;; A"
by (induct n) (simp_all add: conc_assoc[symmetric])

lemma lang_pow_add: "A ^^ (n + m) = (A ^^ n) ;; (A ^^ m)"
  by (induct n) (auto simp: conc_assoc)

lemma lang_empty: 
  fixes A::"string set"
  shows "A ^^ 0 = {[]}"
  by simp

section \<open>Semantic Derivative (Left Quotient) of Languages\<close>

definition
  Der :: "char \<Rightarrow> string set \<Rightarrow> string set"
where
  "Der c A \<equiv> {s. c # s \<in> A}"

definition
  Ders :: "string \<Rightarrow> string set \<Rightarrow> string set"
where
  "Ders s A \<equiv> {s'. s @ s' \<in> A}"

lemma Der_null [simp]:
  shows "Der c {} = {}"
unfolding Der_def
by auto

lemma Der_empty [simp]:
  shows "Der c {[]} = {}"
unfolding Der_def
by auto

lemma Der_char [simp]:
  shows "Der c {[d]} = (if c = d then {[]} else {})"
unfolding Der_def
by auto

lemma Der_union [simp]:
  shows "Der c (A \<union> B) = Der c A \<union> Der c B"
unfolding Der_def
by auto

lemma Der_Sequ [simp]:
  shows "Der c (A ;; B) = (Der c A) ;; B \<union> (if [] \<in> A then Der c B else {})"
unfolding Der_def Sequ_def
by (auto simp add: Cons_eq_append_conv)


section \<open>Kleene Star for Languages\<close>

inductive_set
  Star :: "string set \<Rightarrow> string set" ("_\<star>" [101] 102)
  for A :: "string set"
where
  start[intro]: "[] \<in> A\<star>"
| step[intro]:  "\<lbrakk>s1 \<in> A; s2 \<in> A\<star>\<rbrakk> \<Longrightarrow> s1 @ s2 \<in> A\<star>"

(* Arden's lemma *)

lemma Star_cases:
  shows "A\<star> = {[]} \<union> A ;; A\<star>"
unfolding Sequ_def
by (auto) (metis Star.simps)

lemma Star_decomp: 
  assumes "c # x \<in> A\<star>" 
  shows "\<exists>s1 s2. x = s1 @ s2 \<and> c # s1 \<in> A \<and> s2 \<in> A\<star>"
using assms
by (induct x\<equiv>"c # x" rule: Star.induct) 
   (auto simp add: append_eq_Cons_conv)

lemma Star_Der_Sequ: 
  shows "Der c (A\<star>) \<subseteq> (Der c A) ;; A\<star>"
unfolding Der_def Sequ_def
by(auto simp add: Star_decomp)

lemma Der_inter[simp]:   "Der a (A \<inter> B) = Der a A \<inter> Der a B"
  and Der_compl[simp]:   "Der a (-A) = - Der a A"
  and Der_Union[simp]:   "Der a (Union M) = Union(Der a ` M)"
  and Der_UN[simp]:      "Der a (UN x:I. S x) = (UN x:I. Der a (S x))"
by (auto simp: Der_def)

lemma Der_star[simp]:
  shows "Der c (A\<star>) = (Der c A) ;; A\<star>"
proof -    
  have "Der c (A\<star>) = Der c ({[]} \<union> A ;; A\<star>)"  
    by (simp only: Star_cases[symmetric])
  also have "... = Der c (A ;; A\<star>)"
    by (simp only: Der_union Der_empty) (simp)
  also have "... = (Der c A) ;; A\<star> \<union> (if [] \<in> A then Der c (A\<star>) else {})"
    by simp
  also have "... =  (Der c A) ;; A\<star>"
    using Star_Der_Sequ by auto
  finally show "Der c (A\<star>) = (Der c A) ;; A\<star>" .
qed

lemma Der_pow[simp]:
  shows "Der c (A ^^ n) = (if n = 0 then {} else (Der c A) ;; (A ^^ (n - 1)))"
  apply(induct n arbitrary: A)
   apply(auto simp add: Cons_eq_append_conv)
  by (metis Suc_pred concI_if_Nil2 conc_assoc conc_pow_comm lang_pow.simps(2))


lemma Star_concat:
  assumes "\<forall>s \<in> set ss. s \<in> A"  
  shows "concat ss \<in> A\<star>"
using assms by (induct ss) (auto)

lemma Star_split:
  assumes "s \<in> A\<star>"
  shows "\<exists>ss. concat ss = s \<and> (\<forall>s \<in> set ss. s \<in> A \<and> s \<noteq> [])"
using assms
  apply(induct rule: Star.induct)
  using concat.simps(1) apply fastforce
  apply(clarify)
  by (metis append_Nil concat.simps(2) set_ConsD)


lemma Star_pow1:
  assumes "s \<in> A\<star>"
  shows "\<exists>n. s \<in> A ^^ n"
  using assms
  apply(induct)
  apply (metis insert_iff lang_empty)
  by (metis concI lang_pow.simps(2))

lemma Star_pow2:
  assumes "s \<in> A ^^ n"
  shows "s \<in> A\<star>"
  using assms
  apply(induct n arbitrary: s)
  apply (simp add: Star.start)
  using Star.step by auto

lemma concI_if_Nil1: "[] \<in> A \<Longrightarrow> xs \<in> B \<Longrightarrow> xs \<in> A ;; B"
  by (metis append_Nil concI)

lemma Nil_in_conc[simp]: "[] \<in> A ;; B \<longleftrightarrow> [] \<in> A \<and> [] \<in> B"
by (metis append_is_Nil_conv concE concI)

lemma empty_pow_add:
  fixes s :: string
  assumes "[] \<in> A" "s \<in> A ^^ n"
  shows "s \<in> A ^^ (n + m)"
  using assms
  apply(induct m arbitrary: n)
  apply(auto simp add: concI_if_Nil1)
  done
  

section \<open>Regular Expressions\<close>

(* BACKREF-MIGRATION-TODO (definition augmentation, ADMIN APPROVAL REQUIRED):
   Extend the original rexp datatype directly with the final four-part
   backreference constructor, plus derivative-only HALF and RESIDUE states.
   Do not introduce brexp/gbrexp aliases or wrapper datatypes. The approved
   language shape should be the generalized four-language form, not the old
   two-component pilot backref_lang. *)
datatype rexp =
  ZERO
| ONE
| CH char
| SEQ rexp rexp
| ALT rexp rexp
| STAR rexp
| NTIMES rexp nat
| BACKREF4 rexp rexp rexp rexp string
| HALF rexp string string
| RESIDUE string string

section \<open>Semantics of Regular Expressions\<close>

definition backref_lang4 ::
  "string set \<Rightarrow> string set \<Rightarrow> string set \<Rightarrow> string set \<Rightarrow> string \<Rightarrow> string set"
where
  "backref_lang4 L1 L2 L3 L4 cs =
    {s1 @ s2 @ s3 @ rev cs @ s2 @ s4 | s1 s2 s3 s4.
      s1 \<in> L1 \<and> s2 \<in> L2 \<and> s3 \<in> L3 \<and> s4 \<in> L4}"

lemma backref_lang4I:
  assumes "s1 \<in> L1" "s2 \<in> L2" "s3 \<in> L3" "s4 \<in> L4"
  shows "s1 @ s2 @ s3 @ rev cs @ s2 @ s4 \<in> backref_lang4 L1 L2 L3 L4 cs"
  using assms by (auto simp add: backref_lang4_def)
 
(* BACKREF-MIGRATION-TODO (definition augmentation, ADMIN APPROVAL REQUIRED):
   Add L cases for the new BACKREF4/HALF/RESIDUE constructors. BACKREF4 must
   use backref_lang4 directly in this file, with strings of the form
   s1 @ s2 @ s3 @ rev cs @ s2 @ s4. Delete or retire the simplified
   backref_lang target after migration. *)
fun
  L :: "rexp \<Rightarrow> string set"
where
  "L (ZERO) = {}"
| "L (ONE) = {[]}"
| "L (CH c) = {[c]}"
| "L (SEQ r1 r2) = (L r1) ;; (L r2)"
| "L (ALT r1 r2) = (L r1) \<union> (L r2)"
| "L (STAR r) = (L r)\<star>"
| "L (NTIMES r n) = (L r) ^^ n"
| "L (BACKREF4 r1 r2 r3 r4 cs) = backref_lang4 (L r1) (L r2) (L r3) (L r4) cs"
| "L (HALF r cs rep) = (L r) ;; {cs}"
| "L (RESIDUE cs rep) = {cs}"

section \<open>Nullable, Derivatives\<close>

(* BACKREF-MIGRATION-TODO (definition augmentation):
   Add nullable cases for BACKREF4/HALF/RESIDUE once the rexp constructors are
   approved. This must extend the original nullable function, not a wrapper. *)
fun
 nullable :: "rexp \<Rightarrow> bool"
where
  "nullable (ZERO) = False"
| "nullable (ONE) = True"
| "nullable (CH c) = False"
| "nullable (ALT r1 r2) = (nullable r1 \<or> nullable r2)"
| "nullable (SEQ r1 r2) = (nullable r1 \<and> nullable r2)"
| "nullable (STAR r) = True"
| "nullable (NTIMES r n) = (if n = 0 then True else nullable r)"
| "nullable (BACKREF4 r1 r2 r3 r4 cs) =
    (nullable r1 \<and> nullable r2 \<and> nullable r3 \<and> nullable r4 \<and> cs = [])"
| "nullable (HALF r cs rep) = (nullable r \<and> cs = [])"
| "nullable (RESIDUE cs rep) = (cs = [])"

(* BACKREF-MIGRATION-TODO (definition augmentation, ADMIN APPROVAL REQUIRED):
   Add derivative cases for BACKREF4/HALF/RESIDUE directly to der. Migrate the
   useful gxder/xder residue idea into this original function, then delete the
   pilot gxder path. Avoid broad automation if any proof command starts running
   for tens of seconds; split it into local lemmas instead. *)
fun der_residue :: "char \<Rightarrow> string \<Rightarrow> string \<Rightarrow> rexp"
where
  "der_residue c [] rep = ZERO"
| "der_residue c (d # ds) rep = (if c = d then RESIDUE ds rep else ZERO)"

fun
 der :: "char \<Rightarrow> rexp \<Rightarrow> rexp"
where
  "der c (ZERO) = ZERO"
| "der c (ONE) = ZERO"
| "der c (CH d) = (if c = d then ONE else ZERO)"
| "der c (ALT r1 r2) = ALT (der c r1) (der c r2)"
| "der c (SEQ r1 r2) = 
     (if nullable r1
      then ALT (SEQ (der c r1) r2) (der c r2)
      else SEQ (der c r1) r2)"
| "der c (STAR r) = SEQ (der c r) (STAR r)"
| "der c (NTIMES r n) = (if n = 0 then ZERO else SEQ (der c r) (NTIMES r (n - 1)))"
| "der c (BACKREF4 r1 r2 r3 r4 cs) =
     (let prefix = BACKREF4 (der c r1) r2 r3 r4 cs;
          capture = BACKREF4 ONE (der c r2) r3 r4 (c # cs);
          res = rev cs;
          res_tail = (if res = []
            then ALT (SEQ (der_residue c res res) r4) (der c r4)
            else SEQ (der_residue c res res) r4);
          tail = (if nullable r3
            then ALT (SEQ (der c r3) (SEQ (RESIDUE res res) r4)) res_tail
            else SEQ (der c r3) (SEQ (RESIDUE res res) r4))
      in if nullable r1
         then ALT prefix (if nullable r2 then ALT capture tail else capture)
         else prefix)"
| "der c (HALF r cs rep) =
     (if nullable r
      then ALT (HALF (der c r) cs rep) (der_residue c cs rep)
      else HALF (der c r) cs rep)"
| "der c (RESIDUE cs rep) = der_residue c cs rep"

fun 
 ders :: "string \<Rightarrow> rexp \<Rightarrow> rexp"
where
  "ders [] r = r"
| "ders (c # s) r = ders s (der c r)"


lemma pow_empty_iff:
  shows "[] \<in> (L r) ^^ n \<longleftrightarrow> (if n = 0 then True else [] \<in> (L r))"
  by (induct n) (auto simp add: Sequ_def)

(* BACKREF-MIGRATION-TODO (proof constructor-case extension):
   Extend nullable_correctness with direct BACKREF4/HALF/RESIDUE cases. *)
lemma nullable_correctness:
  shows "nullable r  \<longleftrightarrow> [] \<in> (L r)"
  by (induct r) (auto simp add: Sequ_def pow_empty_iff backref_lang4_def)

lemma Der_singleton_string [simp]:
  "Der c {d # ds} = (if c = d then {ds} else {})"
  by (auto simp add: Der_def)

lemma L_der_residue:
  "L (der_residue c cs rep) = Der c {cs}"
  by (cases cs) auto

lemma Der_backref_lang4:
  "Der c (backref_lang4 L1 L2 L3 L4 cs) =
   backref_lang4 (Der c L1) L2 L3 L4 cs \<union>
   (if [] \<in> L1 then backref_lang4 {[]} (Der c L2) L3 L4 (c # cs) else {}) \<union>
   (if [] \<in> L1 \<and> [] \<in> L2 then Der c (L3 ;; ({rev cs} ;; L4)) else {})"
proof (rule equalityI)
  show "Der c (backref_lang4 L1 L2 L3 L4 cs) \<subseteq>
    backref_lang4 (Der c L1) L2 L3 L4 cs \<union>
    (if [] \<in> L1 then backref_lang4 {[]} (Der c L2) L3 L4 (c # cs) else {}) \<union>
    (if [] \<in> L1 \<and> [] \<in> L2 then Der c (L3 ;; ({rev cs} ;; L4)) else {})"
  proof
    fix s
    assume "s \<in> Der c (backref_lang4 L1 L2 L3 L4 cs)"
    then obtain s1 s2 s3 s4 where parts:
      "s1 \<in> L1" "s2 \<in> L2" "s3 \<in> L3" "s4 \<in> L4"
      "c # s = s1 @ s2 @ s3 @ rev cs @ s2 @ s4"
      by (auto simp add: Der_def backref_lang4_def)
    show "s \<in>
      backref_lang4 (Der c L1) L2 L3 L4 cs \<union>
      (if [] \<in> L1 then backref_lang4 {[]} (Der c L2) L3 L4 (c # cs) else {}) \<union>
      (if [] \<in> L1 \<and> [] \<in> L2 then Der c (L3 ;; ({rev cs} ;; L4)) else {})"
    proof (cases s1)
      case Nil
      then have nil1: "[] \<in> L1"
        using parts by simp
      from Nil parts have rest:
        "c # s = s2 @ s3 @ rev cs @ s2 @ s4"
        by simp
      show ?thesis
      proof (cases s2)
        case Nil
        then have "[] \<in> L2"
          using parts by simp
        moreover have "s \<in> Der c (L3 ;; ({rev cs} ;; L4))"
          using Nil rest parts by (auto simp add: Der_def Sequ_def)
        ultimately show ?thesis
          using nil1 by simp
      next
        case (Cons d ds)
        then have "ds \<in> Der c L2"
          using parts rest by (auto simp add: Der_def)
        moreover have "s = ds @ s3 @ rev (c # cs) @ ds @ s4"
          using Cons rest by auto
        ultimately have "s \<in> backref_lang4 {[]} (Der c L2) L3 L4 (c # cs)"
          using parts by (auto simp add: backref_lang4_def)
        then show ?thesis
          using nil1 by simp
      qed
    next
      case (Cons d ds)
      then have "ds \<in> Der c L1"
        using parts by (auto simp add: Der_def)
      moreover have "s = ds @ s2 @ s3 @ rev cs @ s2 @ s4"
        using Cons parts by auto
      ultimately have "s \<in> backref_lang4 (Der c L1) L2 L3 L4 cs"
        using parts by (auto simp add: backref_lang4_def)
      then show ?thesis by simp
    qed
  qed
next
  show "backref_lang4 (Der c L1) L2 L3 L4 cs \<union>
    (if [] \<in> L1 then backref_lang4 {[]} (Der c L2) L3 L4 (c # cs) else {}) \<union>
    (if [] \<in> L1 \<and> [] \<in> L2 then Der c (L3 ;; ({rev cs} ;; L4)) else {})
    \<subseteq> Der c (backref_lang4 L1 L2 L3 L4 cs)"
  proof
    fix s
    assume mem: "s \<in> backref_lang4 (Der c L1) L2 L3 L4 cs \<union>
      (if [] \<in> L1 then backref_lang4 {[]} (Der c L2) L3 L4 (c # cs) else {}) \<union>
      (if [] \<in> L1 \<and> [] \<in> L2 then Der c (L3 ;; ({rev cs} ;; L4)) else {})"
    from mem consider
      (prefix) "s \<in> backref_lang4 (Der c L1) L2 L3 L4 cs"
    | (capture) "s \<in> (if [] \<in> L1 then backref_lang4 {[]} (Der c L2) L3 L4 (c # cs) else {})"
    | (tail) "s \<in> (if [] \<in> L1 \<and> [] \<in> L2 then Der c (L3 ;; ({rev cs} ;; L4)) else {})"
      by blast
    then show "s \<in> Der c (backref_lang4 L1 L2 L3 L4 cs)"
    proof cases
      case prefix
      then obtain s1 s2 s3 s4 where parts:
        "s1 \<in> Der c L1" "s2 \<in> L2" "s3 \<in> L3" "s4 \<in> L4"
        "s = s1 @ s2 @ s3 @ rev cs @ s2 @ s4"
        by (auto simp add: backref_lang4_def)
      have s1_in: "c # s1 \<in> L1"
        using parts by (simp add: Der_def)
      have "(c # s1) @ s2 @ s3 @ rev cs @ s2 @ s4 \<in> backref_lang4 L1 L2 L3 L4 cs"
        using s1_in parts by (intro backref_lang4I)
      moreover have "c # s = (c # s1) @ s2 @ s3 @ rev cs @ s2 @ s4"
        using parts by simp
      ultimately have "c # s \<in> backref_lang4 L1 L2 L3 L4 cs"
        by simp
      then show ?thesis
        by (simp add: Der_def)
    next
      case capture
      then obtain s2 s3 s4 where parts:
        "[] \<in> L1" "s2 \<in> Der c L2" "s3 \<in> L3" "s4 \<in> L4"
        "s = s2 @ s3 @ rev cs @ c # s2 @ s4"
        by (cases "[] \<in> L1") (auto simp add: backref_lang4_def)
      have s2_in: "c # s2 \<in> L2"
        using parts by (simp add: Der_def)
      have "[] @ (c # s2) @ s3 @ rev cs @ (c # s2) @ s4 \<in> backref_lang4 L1 L2 L3 L4 cs"
        using parts s2_in by (intro backref_lang4I)
      moreover have "c # s = [] @ (c # s2) @ s3 @ rev cs @ (c # s2) @ s4"
        using parts by simp
      ultimately have "c # s \<in> backref_lang4 L1 L2 L3 L4 cs"
        by simp
      then show ?thesis
        by (simp add: Der_def)
    next
      case tail
      have both: "[] \<in> L1 \<and> [] \<in> L2"
        using tail by (cases "[] \<in> L1 \<and> [] \<in> L2") auto
      have nils: "[] \<in> L1" "[] \<in> L2"
        using both by auto
      have "s \<in> Der c (L3 ;; ({rev cs} ;; L4))"
        using tail nils by simp
      then obtain s3 s4 where parts:
        "[] \<in> L1" "[] \<in> L2" "s3 \<in> L3" "s4 \<in> L4"
        "c # s = s3 @ rev cs @ s4"
        using nils by (auto simp add: Der_def Sequ_def)
      have "[] @ [] @ s3 @ rev cs @ [] @ s4 \<in> backref_lang4 L1 L2 L3 L4 cs"
        using parts by (intro backref_lang4I)
      then have "c # s \<in> backref_lang4 L1 L2 L3 L4 cs"
        using parts by simp
      then show ?thesis
        by (simp add: Der_def)
    qed
  qed
qed

(* BACKREF-MIGRATION-TODO (proof constructor-case extension):
   Extend der_correctness with direct BACKREF4/HALF/RESIDUE cases, using a
   migrated Der_backref_lang4 lemma in this file. Wrapper derivative theorems
   do not count as bounty. *)
lemma der_correctness:
  shows "L (der c r) = Der c (L r)"
proof (induct r arbitrary: c)
  case ZERO
  then show ?case by simp
next
  case ONE
  then show ?case by simp
next
  case (CH x)
  then show ?case by simp
next
  case (SEQ r1 r2)
  then show ?case
    by (auto simp add: nullable_correctness Der_Sequ)
next
  case (ALT r1 r2)
  then show ?case by simp
next
  case (STAR r)
  then show ?case by simp
next
  case (NTIMES r n)
  have "L (der c (NTIMES r n)) =
    (if n = 0 then {} else Der c (L r) ;; (L r ^^ (n - 1)))"
    using NTIMES by (cases n) simp_all
  also have "... = Der c (L (NTIMES r n))"
    by simp
  finally show ?case .
next
  case (BACKREF4 r1 r2 r3 r4 cs)
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
  have res_tail: "L ?res_tail = Der c ({?res} ;; L r4)"
  proof (cases ?res)
    case Nil
    then show ?thesis
      using BACKREF4(4)[of c]
      by (simp add: L_der_residue Der_Sequ)
  next
    case (Cons d ds)
    then show ?thesis
      by (simp add: L_der_residue Der_Sequ)
  qed
  have tail: "L ?tail = Der c (L r3 ;; ({?res} ;; L r4))"
    using BACKREF4(3)[of c] res_tail
    by (simp add: nullable_correctness Der_Sequ)
  show ?case
    using BACKREF4(1,2) tail
    by (simp add: Let_def nullable_correctness Der_backref_lang4 Un_assoc)
next
  case (HALF r cs rep)
  then show ?case
    by (simp add: nullable_correctness L_der_residue Der_Sequ)
next
  case (RESIDUE cs rep)
  then show ?case
    by (simp add: L_der_residue)
qed


(* BACKREF-MIGRATION-TODO (proof constructor-case extension):
   Recheck ders_correctness after der_correctness is extended; this theorem
   must remain the original repeated-derivative correctness statement. *)
lemma ders_correctness:
  shows "L (ders s r) = Ders s (L r)"
  by (induct s arbitrary: r)
     (simp_all add: Ders_def der_correctness Der_def)

lemma ders_append:
  shows "ders (s1 @ s2) r = ders s2 (ders s1 r)"
  by (induct s1 arbitrary: s2 r) (auto)

lemma ders_snoc:
  shows "ders (s @ [c]) r = der c (ders s r)"
  by (simp add: ders_append)


end
