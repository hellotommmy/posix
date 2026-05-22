theory BackRefLang
  imports RegLangs
begin

section \<open>Backreference Pilot Language\<close>

datatype brexp =
  BZERO
| BONE
| BCH char
| BSEQ brexp brexp
| BALT brexp brexp
| BSTAR brexp
| BNTIMES brexp nat
| BBACKREF brexp brexp string
| BHALF brexp string string
| BRESIDUE string string

definition backref_lang :: "string set \<Rightarrow> string set \<Rightarrow> string \<Rightarrow> string set"
where
  "backref_lang A B cs = {x @ y @ rev cs @ x | x y. x \<in> A \<and> y \<in> B}"

fun BL :: "brexp \<Rightarrow> string set"
where
  "BL BZERO = {}"
| "BL BONE = {[]}"
| "BL (BCH c) = {[c]}"
| "BL (BSEQ r1 r2) = BL r1 ;; BL r2"
| "BL (BALT r1 r2) = BL r1 \<union> BL r2"
| "BL (BSTAR r) = (BL r)\<star>"
| "BL (BNTIMES r n) = (BL r) ^^ n"
| "BL (BBACKREF r mid cs) = backref_lang (BL r) (BL mid) cs"
| "BL (BHALF mid cs rep) = BL mid ;; {cs}"
| "BL (BRESIDUE cs rep) = {cs}"

lemma BL_BBACKREF_empty:
  "BL (BBACKREF r mid []) = {x @ y @ x | x y. x \<in> BL r \<and> y \<in> BL mid}"
  by (auto simp add: backref_lang_def)

fun xnullable :: "brexp \<Rightarrow> bool"
where
  "xnullable BZERO = False"
| "xnullable BONE = True"
| "xnullable (BCH c) = False"
| "xnullable (BSEQ r1 r2) = (xnullable r1 \<and> xnullable r2)"
| "xnullable (BALT r1 r2) = (xnullable r1 \<or> xnullable r2)"
| "xnullable (BSTAR r) = True"
| "xnullable (BNTIMES r n) = (if n = 0 then True else xnullable r)"
| "xnullable (BBACKREF r mid cs) = (xnullable r \<and> xnullable mid \<and> cs = [])"
| "xnullable (BHALF mid cs rep) = (xnullable mid \<and> cs = [])"
| "xnullable (BRESIDUE cs rep) = (cs = [])"

fun xder_residue :: "char \<Rightarrow> string \<Rightarrow> string \<Rightarrow> brexp"
where
  "xder_residue c [] rep = BZERO"
| "xder_residue c (d # ds) rep = (if c = d then BRESIDUE ds rep else BZERO)"

fun xder :: "char \<Rightarrow> brexp \<Rightarrow> brexp"
where
  "xder c BZERO = BZERO"
| "xder c BONE = BZERO"
| "xder c (BCH d) = (if c = d then BONE else BZERO)"
| "xder c (BALT r1 r2) = BALT (xder c r1) (xder c r2)"
| "xder c (BSEQ r1 r2) =
     (if xnullable r1
      then BALT (BSEQ (xder c r1) r2) (xder c r2)
      else BSEQ (xder c r1) r2)"
| "xder c (BSTAR r) = BSEQ (xder c r) (BSTAR r)"
| "xder c (BNTIMES r n) =
     (if n = 0 then BZERO else BSEQ (xder c r) (BNTIMES r (n - 1)))"
| "xder c (BBACKREF r mid cs) =
     (if xnullable r
      then BALT
        (BBACKREF (xder c r) mid (c # cs))
        (if xnullable mid
         then BALT (BHALF (xder c mid) (rev cs) (rev cs))
                   (xder_residue c (rev cs) (rev cs))
         else BHALF (xder c mid) (rev cs) (rev cs))
      else BBACKREF (xder c r) mid (c # cs))"
| "xder c (BHALF mid cs rep) =
     (if xnullable mid
      then BALT (BHALF (xder c mid) cs rep) (xder_residue c cs rep)
      else BHALF (xder c mid) cs rep)"
| "xder c (BRESIDUE cs rep) = xder_residue c cs rep"

fun xders :: "brexp \<Rightarrow> string \<Rightarrow> brexp"
where
  "xders r [] = r"
| "xders r (c # s) = xders (xder c r) s"

section \<open>Correctness\<close>

lemma Der_singleton_string [simp]:
  "Der c {d # ds} = (if c = d then {ds} else {})"
  by (auto simp add: Der_def)

lemma BL_xder_residue:
  "BL (xder_residue c cs rep) = Der c {cs}"
  by (cases cs) auto

lemma lang_pow_empty_iff:
  fixes A :: "string set"
  shows "[] \<in> A ^^ n \<longleftrightarrow> (if n = 0 then True else [] \<in> A)"
proof (induct n)
  case 0
  show ?case by (simp add: lang_pow.simps)
next
  case (Suc n)
  have "[] \<in> A ^^ Suc n \<longleftrightarrow> [] \<in> A \<and> [] \<in> A ^^ n"
    by (auto simp add: Sequ_def lang_pow.simps)
  also have "... \<longleftrightarrow> [] \<in> A"
    using Suc by auto
  finally show ?case by simp
qed

lemma xnullable_correctness:
  "xnullable r \<longleftrightarrow> [] \<in> BL r"
  apply (induct r)
           apply (auto simp add: Sequ_def backref_lang_def lang_pow_empty_iff)
  done

lemma Der_backref_lang:
  "Der c (backref_lang A B cs) =
   backref_lang (Der c A) B (c # cs) \<union>
     (if [] \<in> A then Der c (B ;; {rev cs}) else {})"
proof (rule equalityI)
  show "Der c (backref_lang A B cs) \<subseteq>
    backref_lang (Der c A) B (c # cs) \<union>
      (if [] \<in> A then Der c (B ;; {rev cs}) else {})"
  proof
    fix s
    assume "s \<in> Der c (backref_lang A B cs)"
    then obtain x y where xy:
      "x \<in> A" "y \<in> B" "c # s = x @ y @ rev cs @ x"
      by (auto simp add: Der_def backref_lang_def)
    show "s \<in> backref_lang (Der c A) B (c # cs) \<union>
      (if [] \<in> A then Der c (B ;; {rev cs}) else {})"
    proof (cases x)
      case Nil
      then have "[] \<in> A"
        using xy by simp
      moreover have "s \<in> Der c (B ;; {rev cs})"
        using xy Nil by (auto simp add: Der_def Sequ_def)
      ultimately show ?thesis by simp
    next
      case (Cons d xs)
      then have "c = d" "s = xs @ y @ rev cs @ d # xs"
        using xy by auto
      then have "xs \<in> Der c A"
        using xy Cons by (simp add: Der_def)
      moreover have "s = xs @ y @ rev (c # cs) @ xs"
        using \<open>c = d\<close> \<open>s = xs @ y @ rev cs @ d # xs\<close> by simp
      ultimately have "s \<in> backref_lang (Der c A) B (c # cs)"
        using xy by (auto simp add: backref_lang_def)
      then show ?thesis by simp
    qed
  qed
next
  show "backref_lang (Der c A) B (c # cs) \<union>
    (if [] \<in> A then Der c (B ;; {rev cs}) else {})
    \<subseteq> Der c (backref_lang A B cs)"
  proof
    fix s
    assume "s \<in> backref_lang (Der c A) B (c # cs) \<union>
      (if [] \<in> A then Der c (B ;; {rev cs}) else {})"
    then show "s \<in> Der c (backref_lang A B cs)"
    proof
      assume "s \<in> backref_lang (Der c A) B (c # cs)"
      then obtain x y where xy:
        "x \<in> Der c A" "y \<in> B" "s = x @ y @ rev (c # cs) @ x"
        by (auto simp add: backref_lang_def)
      then have "c # x \<in> A"
        by (simp add: Der_def)
      moreover have "c # s = (c # x) @ y @ rev cs @ (c # x)"
        using xy by (simp add: append_assoc)
      ultimately have "\<exists>xa ya. c # s = xa @ ya @ rev cs @ xa \<and> xa \<in> A \<and> ya \<in> B"
        using xy by (intro exI[of _ "c # x"] exI[of _ y]) auto
      then show "s \<in> Der c (backref_lang A B cs)"
        by (simp add: Der_def backref_lang_def)
    next
      assume h: "s \<in> (if [] \<in> A then Der c (B ;; {rev cs}) else {})"
      then have nil: "[] \<in> A"
        by (cases "[] \<in> A") (simp_all del: Der_Sequ)
      from h have der: "s \<in> Der c (B ;; {rev cs})"
        by (cases "[] \<in> A") (simp_all del: Der_Sequ)
      from der obtain y where y: "y \<in> B" "c # s = y @ rev cs"
        unfolding Der_def Sequ_def by auto
      have "\<exists>xa ya. c # s = xa @ ya @ rev cs @ xa \<and> xa \<in> A \<and> ya \<in> B"
        using nil y by (intro exI[of _ "[]"] exI[of _ y]) auto
      then show "s \<in> Der c (backref_lang A B cs)"
        by (simp add: Der_def backref_lang_def)
    qed
  qed
qed

lemma xder_correctness:
  "BL (xder c r) = Der c (BL r)"
  by (induct r arbitrary: c)
     (simp_all add: xnullable_correctness Der_backref_lang BL_xder_residue)

lemma xders_append:
  "xders r (s1 @ s2) = xders (xders r s1) s2"
  by (induct s1 arbitrary: r s2) simp_all

lemma xders_snoc:
  "xders r (s @ [c]) = xder c (xders r s)"
  by (simp add: xders_append)

lemma xders_correctness:
  "BL (xders r s) = Ders s (BL r)"
  apply (induct s arbitrary: r)
   apply (simp add: Ders_def)
  apply (simp add: xder_correctness Ders_def Der_def)
  done

end
