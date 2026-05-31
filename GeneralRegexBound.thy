theory GeneralRegexBound 
  imports "BasicIdentities" 
begin

lemma size_geq1:
  shows "rsize r \<ge> 1"
  by (induct r) auto 

(* BACKREF-MIGRATION-TODO (bounds invariant, ADMIN APPROVAL REQUIRED):
   The original finite-universe argument is valid only for the old regular
   rrexp skeleton. The new backreference states carry arbitrary strings while
   the structural size deliberately ignores payload length, so {r. rsize r <= N}
   is not finite once RBACKREF4/RHALF/RRESIDUE are present. Keep the bound
   theorem honest by making the legacy invariant explicit until a payload-aware
   or quotient-based bound is designed. *)
fun legacy_rrexp :: "rrexp \<Rightarrow> bool" where
  "legacy_rrexp RZERO = True"
| "legacy_rrexp RONE = True"
| "legacy_rrexp (RCHAR c) = True"
| "legacy_rrexp (RALTS rs) = (\<forall>r \<in> set rs. legacy_rrexp r)"
| "legacy_rrexp (RSEQ r1 r2) = (legacy_rrexp r1 \<and> legacy_rrexp r2)"
| "legacy_rrexp (RSTAR r) = legacy_rrexp r"
| "legacy_rrexp (RNTIMES r n) = legacy_rrexp r"
| "legacy_rrexp (RBACKREF4 r1 r2 r3 r4 cs) = False"
| "legacy_rrexp (RHALF r cs rep) = False"
| "legacy_rrexp (RRESIDUE cs rep) = False"

lemma legacy_rflts:
  assumes "\<forall>r \<in> set rs. legacy_rrexp r"
  shows "\<forall>r \<in> set (rflts rs). legacy_rrexp r"
  using assms
  by (induct rs rule: rflts.induct) auto

lemma legacy_rdistinct:
  assumes "\<forall>r \<in> set rs. legacy_rrexp r"
  shows "\<forall>r \<in> set (rdistinct rs acc). legacy_rrexp r"
  using assms by (auto simp add: rdistinct_set_equality1)

lemma legacy_rsimp_ALTs:
  assumes "\<forall>r \<in> set rs. legacy_rrexp r"
  shows "legacy_rrexp (rsimp_ALTs rs)"
  using assms
proof (cases rs)
  case Nil
  then show ?thesis
    by simp
next
  case (Cons r rs')
  show ?thesis
  proof (cases rs')
    assume "rs' = []"
    then show ?thesis
      using Cons assms by simp
  next
    fix r' rs''
    assume "rs' = r' # rs''"
    then show ?thesis
      using Cons assms by simp
  qed
qed

lemma legacy_rsimp_SEQ:
  assumes "legacy_rrexp r1" "legacy_rrexp r2"
  shows "legacy_rrexp (rsimp_SEQ r1 r2)"
  using assms by (cases r1; cases r2; auto)

lemma legacy_rsimp:
  assumes "legacy_rrexp r"
  shows "legacy_rrexp (rsimp r)"
  using assms
proof (induction r)
  case (RALTS rs)
  have mapped: "\<forall>r \<in> set (map rsimp rs). legacy_rrexp r"
    using RALTS by auto
  have flat: "\<forall>r \<in> set (rflts (map rsimp rs)). legacy_rrexp r"
    using legacy_rflts[OF mapped] .
  have distinct: "\<forall>r \<in> set (rdistinct (rflts (map rsimp rs)) {}). legacy_rrexp r"
    using legacy_rdistinct[OF flat] .
  show ?case
    using legacy_rsimp_ALTs[OF distinct] by simp
next
  case (RSEQ r1 r2)
  then show ?case
    using legacy_rsimp_SEQ by simp
qed simp_all

lemma legacy_rder:
  assumes "legacy_rrexp r"
  shows "legacy_rrexp (rder c r)"
  using assms by (induction r) auto

lemma legacy_rders_simp:
  assumes "legacy_rrexp r"
  shows "legacy_rrexp (rders_simp r s)"
  using assms
  by (induction s arbitrary: r) (auto simp add: legacy_rsimp legacy_rder)

lemma legacy_rsimp4_SEQ_atom:
  assumes "legacy_rrexp r1" "legacy_rrexp r2"
  shows "legacy_rrexp (rsimp4_SEQ_atom r1 r2)"
  using assms
proof (induct r1 arbitrary: r2)
  case RZERO
  then show ?case by simp
next
  case RONE
  then show ?case by simp
next
  case (RCHAR c)
  then show ?case
    by (cases r2) simp_all
next
  case (RSEQ r1 r1')
  have left: "legacy_rrexp r1"
    using RSEQ.prems by simp
  have mid: "legacy_rrexp r1'"
    using RSEQ.prems by simp
  have inner: "legacy_rrexp (rsimp4_SEQ_atom r1' r2)"
    by (rule RSEQ.hyps(2)[OF mid RSEQ.prems(2)])
  show ?case
    by (simp add: RSEQ.hyps(1)[OF left inner])
next
  case (RALTS rs)
  then show ?case
    by (cases r2) simp_all
next
  case (RSTAR r)
  then show ?case
    by (cases r2) simp_all
next
  case (RNTIMES r n)
  then show ?case
    by (cases r2) simp_all
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  have False
    using RBACKREF4.prems(1) by simp
  then show ?case by simp
next
  case (RHALF r cs rep)
  have False
    using RHALF.prems(1) by simp
  then show ?case by simp
next
  case (RRESIDUE cs rep)
  have False
    using RRESIDUE.prems(1) by simp
  then show ?case by simp
qed

lemma legacy_rsimp5_alt_rows:
  assumes "legacy_rrexp r"
  shows "\<forall>x \<in> set (rsimp5_alt_rows r). legacy_rrexp x"
  using assms by (cases r) auto

lemma legacy_rsimp5_seq_products:
  assumes "\<forall>x \<in> set xs. legacy_rrexp x"
      and "\<forall>y \<in> set ys. legacy_rrexp y"
  shows "\<forall>z \<in> set (rsimp5_seq_products xs ys). legacy_rrexp z"
  using assms legacy_rsimp4_SEQ_atom by (induct xs) auto

lemma legacy_rsimp5_SEQ:
  assumes "legacy_rrexp r1" "legacy_rrexp r2"
  shows "legacy_rrexp (rsimp5_SEQ r1 r2)"
proof -
  have rows1: "\<forall>x \<in> set (rsimp5_alt_rows r1). legacy_rrexp x"
    by (rule legacy_rsimp5_alt_rows[OF assms(1)])
  have rows2: "\<forall>x \<in> set (rsimp5_alt_rows r2). legacy_rrexp x"
    by (rule legacy_rsimp5_alt_rows[OF assms(2)])
  have products: "\<forall>z \<in>
      set (rsimp5_seq_products (rsimp5_alt_rows r1) (rsimp5_alt_rows r2)).
      legacy_rrexp z"
    by (rule legacy_rsimp5_seq_products[OF rows1 rows2])
  have flat: "\<forall>z \<in>
      set (rflts (rsimp5_seq_products (rsimp5_alt_rows r1) (rsimp5_alt_rows r2))).
      legacy_rrexp z"
    by (rule legacy_rflts[OF products])
  have distinct: "\<forall>z \<in>
      set (rdistinct
        (rflts (rsimp5_seq_products (rsimp5_alt_rows r1) (rsimp5_alt_rows r2)))
        {}). legacy_rrexp z"
    by (rule legacy_rdistinct[OF flat])
  show ?thesis
    unfolding rsimp5_SEQ_def
    by (rule legacy_rsimp_ALTs[OF distinct])
qed

lemma legacy_rsimp5:
  assumes "legacy_rrexp r"
  shows "legacy_rrexp (rsimp5 r)"
  using assms
proof (induction r)
  case (RALTS rs)
  have mapped: "\<forall>r \<in> set (map rsimp5 rs). legacy_rrexp r"
    using RALTS by auto
  have flat: "\<forall>r \<in> set (rflts (map rsimp5 rs)). legacy_rrexp r"
    using legacy_rflts[OF mapped] .
  have distinct: "\<forall>r \<in> set (rdistinct (rflts (map rsimp5 rs)) {}). legacy_rrexp r"
    using legacy_rdistinct[OF flat] .
  show ?case
    using legacy_rsimp_ALTs[OF distinct] by simp
next
  case (RSEQ r1 r2)
  then show ?case
    using legacy_rsimp5_SEQ by simp
qed simp_all

lemma legacy_rders_simp5:
  assumes "legacy_rrexp r"
  shows "legacy_rrexp (rders_simp5 r s)"
  using assms
  by (induction s arbitrary: r) (auto simp add: legacy_rsimp5 legacy_rder)

lemma legacy_rsimp6_SEQ_atom:
  assumes "legacy_rrexp r1" "legacy_rrexp r2"
  shows "legacy_rrexp (rsimp6_SEQ_atom r1 r2)"
  using assms
  by (cases r1; cases r2; auto simp add: rsimp6_SEQ_atom_def legacy_rsimp4_SEQ_atom)

lemma legacy_rsimp6_seq_products:
  assumes "\<forall>x \<in> set xs. legacy_rrexp x"
      and "\<forall>y \<in> set ys. legacy_rrexp y"
  shows "\<forall>z \<in> set (rsimp6_seq_products xs ys). legacy_rrexp z"
  using assms legacy_rsimp6_SEQ_atom
  unfolding rsimp6_seq_products_def by auto

lemma legacy_rsimp6_SEQ:
  assumes "legacy_rrexp r1" "legacy_rrexp r2"
  shows "legacy_rrexp (rsimp6_SEQ r1 r2)"
proof -
  have rows1: "\<forall>x \<in> set (rsimp5_alt_rows r1). legacy_rrexp x"
    by (rule legacy_rsimp5_alt_rows[OF assms(1)])
  have rows2: "\<forall>x \<in> set (rsimp5_alt_rows r2). legacy_rrexp x"
    by (rule legacy_rsimp5_alt_rows[OF assms(2)])
  have products: "\<forall>z \<in>
      set (rsimp6_seq_products (rsimp5_alt_rows r1) (rsimp5_alt_rows r2)).
      legacy_rrexp z"
    by (rule legacy_rsimp6_seq_products[OF rows1 rows2])
  have flat: "\<forall>z \<in>
      set (rflts (rsimp6_seq_products (rsimp5_alt_rows r1) (rsimp5_alt_rows r2))).
      legacy_rrexp z"
    by (rule legacy_rflts[OF products])
  have distinct: "\<forall>z \<in>
      set (rdistinct
        (rflts (rsimp6_seq_products (rsimp5_alt_rows r1) (rsimp5_alt_rows r2)))
        {}). legacy_rrexp z"
    by (rule legacy_rdistinct[OF flat])
  show ?thesis
    unfolding rsimp6_SEQ_def
    by (rule legacy_rsimp_ALTs[OF distinct])
qed

lemma legacy_rsimp6:
  assumes "legacy_rrexp r"
  shows "legacy_rrexp (rsimp6 r)"
  using assms
proof (induction r rule: rsimp6.induct)
  case (1 r1 r2)
  then show ?case
    by (simp add: legacy_rsimp6_SEQ)
next
  case (2 rs)
  have mapped: "\<forall>r \<in> set (map rsimp6 rs). legacy_rrexp r"
    using 2 by auto
  have flat: "\<forall>r \<in> set (rflts (map rsimp6 rs)). legacy_rrexp r"
    using legacy_rflts[OF mapped] .
  have distinct: "\<forall>r \<in> set (rdistinct (rflts (map rsimp6 rs)) {}). legacy_rrexp r"
    using legacy_rdistinct[OF flat] .
  show ?case
    using legacy_rsimp_ALTs[OF distinct] by simp
next
  case (3 r)
  have "legacy_rrexp (rsimp6 r)"
    using 3 by simp
  then show ?case
    by (cases "rsimp6 r") simp_all
qed simp_all

lemma legacy_rders_simp6:
  assumes "legacy_rrexp r"
  shows "legacy_rrexp (rders_simp6 r s)"
  using assms
  by (induction s arbitrary: r) (auto simp add: legacy_rsimp6 legacy_rder)

fun rpder :: "char \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "rpder c RZERO = {}"
| "rpder c RONE = {}"
| "rpder c (RCHAR d) = (if c = d then {RONE} else {})"
| "rpder c (RALTS rs) = (\<Union> (set (map (rpder c) rs)))"
| "rpder c (RSEQ r1 r2) =
    ((\<lambda>p. rsimp4_SEQ_atom p r2) ` rpder c r1 \<union>
      (if rnullable r1 then rpder c r2 else {}))"
| "rpder c (RSTAR r) = ((\<lambda>p. rsimp4_SEQ_atom p (RSTAR r)) ` rpder c r)"
| "rpder c (RNTIMES r n) =
    (if n = 0 then {} else
      ((\<lambda>p. rsimp4_SEQ_atom p (RNTIMES r (n - 1))) ` rpder c r))"
| "rpder c (RBACKREF4 r1 r2 r3 r4 cs) = {}"
| "rpder c (RHALF r cs rep) = {}"
| "rpder c (RRESIDUE cs rep) = {}"

definition RLS :: "rrexp set \<Rightarrow> string set" where
  "RLS rs = (\<Union>r \<in> rs. RL r)"

lemma finite_rpder [simp]:
  "finite (rpder c r)"
  by (induct r) auto

lemma legacy_rpder:
  assumes "legacy_rrexp r" "p \<in> rpder c r"
  shows "legacy_rrexp p"
  using assms
proof (induct r arbitrary: p)
  case RZERO
  then show ?case by simp
next
  case RONE
  then show ?case by simp
next
  case (RCHAR d)
  then show ?case
    by (cases "c = d") simp_all
next
  case (RALTS rs)
  then obtain r where r: "r \<in> set rs" "p \<in> rpder c r"
    by auto
  have "legacy_rrexp r"
    using RALTS.prems r by simp
  then show ?case
    using RALTS.hyps[OF r(1)] r by blast
next
  case (RSEQ r1 r2)
  have p_cases: "p \<in> (\<lambda>q. rsimp4_SEQ_atom q r2) ` rpder c r1 \<or>
      p \<in> (if rnullable r1 then rpder c r2 else {})"
    using RSEQ.prems by simp
  then show ?case
  proof
    assume left: "p \<in> (\<lambda>q. rsimp4_SEQ_atom q r2) ` rpder c r1"
    then obtain q where q: "q \<in> rpder c r1" "p = rsimp4_SEQ_atom q r2"
      by blast
    have q_legacy: "legacy_rrexp q"
      by (rule RSEQ.hyps(1)) (use RSEQ.prems q in auto)
    have r2_legacy: "legacy_rrexp r2"
      using RSEQ.prems by simp
    show ?thesis
      using q q_legacy r2_legacy legacy_rsimp4_SEQ_atom by blast
  next
    assume right: "p \<in> (if rnullable r1 then rpder c r2 else {})"
    then have p_r2: "p \<in> rpder c r2"
      by (cases "rnullable r1") simp_all
    show ?thesis
      by (rule RSEQ.hyps(2)) (use RSEQ.prems p_r2 in auto)
  qed
next
  case (RSTAR r)
  then obtain q where q: "q \<in> rpder c r" "p = rsimp4_SEQ_atom q (RSTAR r)"
    by auto
  have q_legacy: "legacy_rrexp q"
    by (rule RSTAR.hyps) (use RSTAR.prems q in auto)
  have star_legacy: "legacy_rrexp (RSTAR r)"
    using RSTAR.prems by simp
  show ?case
    using q q_legacy star_legacy legacy_rsimp4_SEQ_atom by blast
next
  case (RNTIMES r n)
  then show ?case
  proof (cases n)
    case 0
    then show ?thesis
      using RNTIMES.prems by simp
  next
    case (Suc m)
    then obtain q where q: "q \<in> rpder c r"
      "p = rsimp4_SEQ_atom q (RNTIMES r m)"
      using RNTIMES.prems by auto
    have q_legacy: "legacy_rrexp q"
      by (rule RNTIMES.hyps) (use RNTIMES.prems q in auto)
    have ntimes_legacy: "legacy_rrexp (RNTIMES r m)"
      using RNTIMES.prems by simp
    show ?thesis
      using q q_legacy ntimes_legacy legacy_rsimp4_SEQ_atom by blast
  qed
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  have False
    using RBACKREF4.prems(2) by simp
  then show ?case by simp
next
  case (RHALF r cs rep)
  have False
    using RHALF.prems(2) by simp
  then show ?case by simp
next
  case (RRESIDUE cs rep)
  have False
    using RRESIDUE.prems(2) by simp
  then show ?case by simp
qed

lemma card_rpder_list_le_rsizes:
  assumes "\<And>r. r \<in> set rs \<Longrightarrow> card (rpder c r) \<le> rsize r"
  shows "card (\<Union> (set (map (rpder c) rs))) \<le> rsizes rs"
  using assms
proof (induct rs)
  case Nil
  then show ?case by simp
next
  case (Cons r rs)
  have head: "card (rpder c r) \<le> rsize r"
    by (rule Cons.prems) simp
  have tail: "card (\<Union> (set (map (rpder c) rs))) \<le> rsizes rs"
    by (rule Cons.hyps) (use Cons.prems in auto)
  have "card (\<Union> (set (map (rpder c) (r # rs)))) \<le>
    card (rpder c r) + card (\<Union> (set (map (rpder c) rs)))"
    by (simp add: card_Un_le)
  then show ?case
    using head tail by simp
qed

lemma card_rpder_le_rsize:
  assumes "legacy_rrexp r"
  shows "card (rpder c r) \<le> rsize r"
  using assms
proof (induct r)
  case RZERO
  then show ?case by simp
next
  case RONE
  then show ?case by simp
next
  case (RCHAR d)
  then show ?case by simp
next
  case (RALTS rs)
  have elems: "\<And>r. r \<in> set rs \<Longrightarrow> card (rpder c r) \<le> rsize r"
    using RALTS by auto
  have row_bound: "card (rpder c (RALTS rs)) \<le> rsizes rs"
    using card_rpder_list_le_rsizes[OF elems] by simp
  have "rsizes rs \<le> rsize (RALTS rs)"
    by simp
  show ?case
    using row_bound \<open>rsizes rs \<le> rsize (RALTS rs)\<close> by linarith
next
  case (RSEQ r1 r2)
  have left: "card ((\<lambda>p. rsimp4_SEQ_atom p r2) ` rpder c r1) \<le>
      card (rpder c r1)"
    by (rule card_image_le) simp
  have right: "card (if rnullable r1 then rpder c r2 else {}) \<le> rsize r2"
    using RSEQ by simp
  have "card (rpder c (RSEQ r1 r2)) \<le>
      card ((\<lambda>p. rsimp4_SEQ_atom p r2) ` rpder c r1) +
        card (if rnullable r1 then rpder c r2 else {})"
    by (simp add: card_Un_le)
  also have "... \<le> rsize r1 + rsize r2"
  proof -
    have r1_bound: "card (rpder c r1) \<le> rsize r1"
      by (rule RSEQ.hyps(1)) (use RSEQ.prems in simp)
    have left_size:
      "card ((\<lambda>p. rsimp4_SEQ_atom p r2) ` rpder c r1) \<le> rsize r1"
      using left r1_bound by linarith
    show ?thesis
      using left_size right by linarith
  qed
  also have "... \<le> rsize (RSEQ r1 r2)"
    by simp
  finally show ?case .
next
  case (RSTAR r)
  have "card (rpder c (RSTAR r)) \<le> card (rpder c r)"
    by (simp add: card_image_le)
  also have "... \<le> rsize r"
    using RSTAR by simp
  also have "... \<le> rsize (RSTAR r)"
    by simp
  finally show ?case .
next
  case (RNTIMES r n)
  then show ?case
  proof (cases n)
    case 0
    then show ?thesis by simp
  next
    case (Suc m)
    have "card (rpder c (RNTIMES r n)) \<le> card (rpder c r)"
      using Suc by (simp add: card_image_le)
    also have "... \<le> rsize r"
      using RNTIMES by simp
    also have "... \<le> rsize (RNTIMES r n)"
      by simp
    finally show ?thesis .
  qed
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  then show ?case by simp
next
  case (RHALF r cs rep)
  then show ?case by simp
next
  case (RRESIDUE cs rep)
  then show ?case by simp
qed

lemma RLS_image_rsimp4_SEQ_atom:
  "RLS ((\<lambda>p. rsimp4_SEQ_atom p k) ` ps) = RLS ps ;; RL k"
  unfolding RLS_def
  by (auto simp add: RL_rsimp4_SEQ_atom Sequ_def)

lemma RLS_rpder:
  assumes "legacy_rrexp r"
  shows "RLS (rpder c r) = Der c (RL r)"
  using assms
proof (induct r)
  case RZERO
  then show ?case
    by (simp add: RLS_def)
next
  case RONE
  then show ?case
    by (simp add: RLS_def)
next
  case (RCHAR d)
  then show ?case
    by (simp add: RLS_def)
next
  case (RALTS rs)
  have "RLS (rpder c (RALTS rs)) =
    (\<Union>r \<in> set rs. RLS (rpder c r))"
    unfolding RLS_def by auto
  also have "... = (\<Union>r \<in> set rs. Der c (RL r))"
    using RALTS by auto
  also have "... = Der c (RL (RALTS rs))"
    by auto
  finally show ?case .
next
  case (RSEQ r1 r2)
  have left: "RLS ((\<lambda>p. rsimp4_SEQ_atom p r2) ` rpder c r1) =
      Der c (RL r1) ;; RL r2"
    using RSEQ by (simp add: RLS_image_rsimp4_SEQ_atom)
  show ?case
  proof (cases "rnullable r1")
    case True
    then have "[] \<in> RL r1"
      by (simp add: RL_rnullable)
    then show ?thesis
      using True left RSEQ by (simp add: RLS_def RLS_image_rsimp4_SEQ_atom)
  next
    case False
    then have "[] \<notin> RL r1"
      by (simp add: RL_rnullable)
    then show ?thesis
      using False left by (simp add: RLS_def RLS_image_rsimp4_SEQ_atom)
  qed
next
  case (RSTAR r)
  then show ?case
    by (simp add: RLS_image_rsimp4_SEQ_atom)
next
  case (RNTIMES r n)
  then show ?case
  proof (cases n)
    case 0
    then show ?thesis
      by (simp add: RLS_def)
  next
    case (Suc m)
    have "RLS (rpder c (RNTIMES r n)) =
      RLS ((\<lambda>p. rsimp4_SEQ_atom p (RNTIMES r m)) ` rpder c r)"
      using Suc by simp
    also have "... = Der c (RL r) ;; RL (RNTIMES r m)"
      using RNTIMES by (simp add: RLS_image_rsimp4_SEQ_atom)
    also have "... = Der c (RL (RNTIMES r n))"
    proof -
      have "Der c (RL (RNTIMES r n)) =
        Der c (RL r) ;; RL (RNTIMES r m)"
      proof -
        have "Der c (RL (RNTIMES r n)) = Der c ((RL r) ^^ Suc m)"
          using Suc by simp
        also have "... = Der c (RL r) ;; ((RL r) ^^ m)"
          by (subst Der_pow) simp
        also have "... = Der c (RL r) ;; RL (RNTIMES r m)"
          by simp
        finally show ?thesis .
      qed
      then show ?thesis by simp
    qed
    finally show ?thesis .
  qed
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  then show ?case by simp
next
  case (RHALF r cs rep)
  then show ?case by simp
next
  case (RRESIDUE cs rep)
  then show ?case by simp
qed

lemma RLS_rpder_rder:
  assumes "legacy_rrexp r"
  shows "RLS (rpder c r) = RL (rder c r)"
  using RLS_rpder[OF assms] RL_rder[of c r] by simp

definition rpder_set :: "char \<Rightarrow> rrexp set \<Rightarrow> rrexp set" where
  "rpder_set c rs = (\<Union>r \<in> rs. rpder c r)"

fun rpders :: "rrexp set \<Rightarrow> string \<Rightarrow> rrexp set" where
  "rpders rs [] = rs"
| "rpders rs (c # s) = rpders (rpder_set c rs) s"

definition rpders1 :: "rrexp \<Rightarrow> string \<Rightarrow> rrexp set" where
  "rpders1 r s = rpders {r} s"

lemma finite_rpder_set [simp]:
  assumes "finite rs"
  shows "finite (rpder_set c rs)"
  using assms unfolding rpder_set_def by auto

lemma finite_rpders [simp]:
  assumes "finite rs"
  shows "finite (rpders rs s)"
  using assms by (induct s arbitrary: rs) auto

lemma legacy_rpder_set:
  assumes "\<forall>r \<in> rs. legacy_rrexp r"
      and "p \<in> rpder_set c rs"
  shows "legacy_rrexp p"
  using assms unfolding rpder_set_def
  by (auto intro: legacy_rpder)

lemma legacy_rpders:
  assumes "\<forall>r \<in> rs. legacy_rrexp r"
      and "p \<in> rpders rs s"
  shows "legacy_rrexp p"
  using assms
proof (induct s arbitrary: rs)
  case Nil
  then show ?case by simp
next
  case (Cons c s)
  have next_legacy: "\<forall>r \<in> rpder_set c rs. legacy_rrexp r"
    using Cons.prems(1) legacy_rpder_set by blast
  have p_next: "p \<in> rpders (rpder_set c rs) s"
    using Cons.prems(2) by simp
  show ?case
    by (rule Cons.hyps[OF next_legacy p_next])
qed

lemma RLS_rpder_set:
  assumes "\<forall>r \<in> rs. legacy_rrexp r"
  shows "RLS (rpder_set c rs) = Der c (RLS rs)"
proof -
  have "RLS (rpder_set c rs) = (\<Union>r \<in> rs. RLS (rpder c r))"
    unfolding RLS_def rpder_set_def by auto
  also have "... = (\<Union>r \<in> rs. Der c (RL r))"
    using assms RLS_rpder by blast
  also have "... = Der c (RLS rs)"
    unfolding RLS_def Der_def by auto
  finally show ?thesis .
qed

lemma Ders_Cons:
  "Ders (c # s) A = Ders s (Der c A)"
  unfolding Ders_def Der_def by auto

lemma RL_rders_simp5:
  "RL (rders_simp5 r s) = Ders s (RL r)"
proof (induct s arbitrary: r)
  case Nil
  then show ?case
    by (simp add: Ders_def)
next
  case (Cons c s)
  have "RL (rders_simp5 r (c # s)) =
    Ders s (RL (rsimp5 (rder c r)))"
    by (simp add: Cons.hyps)
  also have "... = Ders s (RL (rder c r))"
    by (simp add: RL_rsimp5[symmetric])
  also have "... = Ders s (Der c (RL r))"
    by (simp add: RL_rder)
  also have "... = Ders (c # s) (RL r)"
    by (simp add: Ders_Cons)
  finally show ?case .
qed

lemma RLS_rpders:
  assumes "\<forall>r \<in> rs. legacy_rrexp r"
  shows "RLS (rpders rs s) = Ders s (RLS rs)"
  using assms
proof (induct s arbitrary: rs)
  case Nil
  then show ?case
    by (simp add: Ders_def)
next
  case (Cons c s)
  have next_legacy: "\<forall>r \<in> rpder_set c rs. legacy_rrexp r"
    using Cons.prems legacy_rpder_set by blast
  have "RLS (rpders rs (c # s)) =
    Ders s (RLS (rpder_set c rs))"
    by (simp add: Cons.hyps[OF next_legacy])
  also have "... = Ders s (Der c (RLS rs))"
    by (simp add: RLS_rpder_set[OF Cons.prems])
  also have "... = Ders (c # s) (RLS rs)"
    by (simp add: Ders_Cons)
  finally show ?case .
qed

lemma RLS_rpders1:
  assumes "legacy_rrexp r"
  shows "RLS (rpders1 r s) = Ders s (RL r)"
  using RLS_rpders[of "{r}" s] assms
  by (simp add: rpders1_def RLS_def)

fun rpder_list :: "char \<Rightarrow> rrexp \<Rightarrow> rrexp list" where
  "rpder_list c RZERO = []"
| "rpder_list c RONE = []"
| "rpder_list c (RCHAR d) = (if c = d then [RONE] else [])"
| "rpder_list c (RALTS rs) = concat (map (rpder_list c) rs)"
| "rpder_list c (RSEQ r1 r2) =
    map (\<lambda>p. rsimp4_SEQ_atom p r2) (rpder_list c r1) @
      (if rnullable r1 then rpder_list c r2 else [])"
| "rpder_list c (RSTAR r) =
    map (\<lambda>p. rsimp4_SEQ_atom p (RSTAR r)) (rpder_list c r)"
| "rpder_list c (RNTIMES r n) =
    (if n = 0 then [] else
      map (\<lambda>p. rsimp4_SEQ_atom p (RNTIMES r (n - 1))) (rpder_list c r))"
| "rpder_list c (RBACKREF4 r1 r2 r3 r4 cs) = []"
| "rpder_list c (RHALF r cs rep) = []"
| "rpder_list c (RRESIDUE cs rep) = []"

lemma set_rpder_list:
  "set (rpder_list c r) = rpder c r"
  by (induct r) auto

lemma length_rpder_list_list_le_rsizes:
  assumes "\<And>r. r \<in> set rs \<Longrightarrow> length (rpder_list c r) \<le> rsize r"
  shows "length (concat (map (rpder_list c) rs)) \<le> rsizes rs"
  using assms
proof (induct rs)
  case Nil
  then show ?case by simp
next
  case (Cons r rs)
  have head: "length (rpder_list c r) \<le> rsize r"
    by (rule Cons.prems) simp
  have tail: "length (concat (map (rpder_list c) rs)) \<le> rsizes rs"
    by (rule Cons.hyps) (use Cons.prems in auto)
  show ?case
    using head tail by simp
qed

lemma length_rpder_list_le_rsize:
  assumes "legacy_rrexp r"
  shows "length (rpder_list c r) \<le> rsize r"
  using assms
proof (induct r)
  case RZERO
  then show ?case by simp
next
  case RONE
  then show ?case by simp
next
  case (RCHAR d)
  then show ?case by simp
next
  case (RALTS rs)
  have elems: "\<And>r. r \<in> set rs \<Longrightarrow> length (rpder_list c r) \<le> rsize r"
    using RALTS by auto
  have "length (rpder_list c (RALTS rs)) \<le> rsizes rs"
    using length_rpder_list_list_le_rsizes[OF elems] by simp
  then show ?case by simp
next
  case (RSEQ r1 r2)
  have left: "length (rpder_list c r1) \<le> rsize r1"
    by (rule RSEQ.hyps(1)) (use RSEQ.prems in simp)
  have right: "length (if rnullable r1 then rpder_list c r2 else []) \<le> rsize r2"
    using RSEQ by simp
  have "length (rpder_list c (RSEQ r1 r2)) =
    length (rpder_list c r1) +
      length (if rnullable r1 then rpder_list c r2 else [])"
    by simp
  also have "... \<le> rsize r1 + rsize r2"
    using left right by linarith
  also have "... \<le> rsize (RSEQ r1 r2)"
    by simp
  finally show ?case .
next
  case (RSTAR r)
  then show ?case by simp
next
  case (RNTIMES r n)
  then show ?case
  proof (cases n)
    case 0
    then show ?thesis by simp
  next
    case (Suc m)
    have "length (rpder_list c (RNTIMES r n)) = length (rpder_list c r)"
      using Suc by simp
    also have "... \<le> rsize r"
      using RNTIMES by simp
    also have "... \<le> rsize (RNTIMES r n)"
      by simp
    finally show ?thesis .
  qed
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  then show ?case by simp
next
  case (RHALF r cs rep)
  then show ?case by simp
next
  case (RRESIDUE cs rep)
  then show ?case by simp
qed

definition rpd_der :: "char \<Rightarrow> rrexp \<Rightarrow> rrexp" where
  "rpd_der c r = rsimp_ALTs (rdistinct (rflts (rpder_list c r)) {})"

definition rpder_norm_list :: "char \<Rightarrow> rrexp \<Rightarrow> rrexp list" where
  "rpder_norm_list c r = map (\<lambda>p. rsimp4_SEQ_atom p RONE) (rpder_list c r)"

definition rpd_der_norm :: "char \<Rightarrow> rrexp \<Rightarrow> rrexp" where
  "rpd_der_norm c r = rsimp_ALTs (rdistinct (rflts (rpder_norm_list c r)) {})"

definition rpder_norm6_list :: "char \<Rightarrow> rrexp \<Rightarrow> rrexp list" where
  "rpder_norm6_list c r = map rsimp6 (rpder_norm_list c r)"

definition rpd_der_norm6 :: "char \<Rightarrow> rrexp \<Rightarrow> rrexp" where
  "rpd_der_norm6 c r = rsimp_ALTs (rdistinct (rflts (rpder_norm6_list c r)) {})"

definition rpder_norm_set :: "char \<Rightarrow> rrexp set \<Rightarrow> rrexp set" where
  "rpder_norm_set c rs = (\<Union>r \<in> rs. set (rpder_norm_list c r))"

definition rpder_norm6_set :: "char \<Rightarrow> rrexp set \<Rightarrow> rrexp set" where
  "rpder_norm6_set c rs = (\<Union>r \<in> rs. set (rpder_norm6_list c r))"

definition rpder_norm_rows :: "char \<Rightarrow> rrexp list \<Rightarrow> rrexp list" where
  "rpder_norm_rows c rs =
    rdistinct (rflts (concat (map (rpder_norm_list c) rs))) {}"

definition rpder_norm6_rows :: "char \<Rightarrow> rrexp list \<Rightarrow> rrexp list" where
  "rpder_norm6_rows c rs =
    rdistinct (rflts (concat (map (rpder_norm6_list c) rs))) {}"

lemma rsize_rpd_der_le_rsizes_rpder_list:
  "rsize (rpd_der c r) \<le> Suc (rsizes (rpder_list c r))"
proof -
  have "rsize (rpd_der c r) \<le>
    rsize (RALTS (rdistinct (rflts (rpder_list c r)) {}))"
    unfolding rpd_der_def by (rule rsimp_aalts_smaller)
  also have "... = Suc (rsizes (rdistinct (rflts (rpder_list c r)) {}))"
    by simp
  also have "... \<le> Suc (rsizes (rflts (rpder_list c r)))"
    using rdistinct_smaller[of "rflts (rpder_list c r)" "{}"] by simp
  also have "... \<le> Suc (rsizes (rpder_list c r))"
    using rflts_mono[of "rpder_list c r"] by simp
  finally show ?thesis .
qed

lemma rsize_rpd_der_norm_le_rsizes:
  "rsize (rpd_der_norm c r) \<le> Suc (rsizes (rpder_norm_list c r))"
proof -
  have "rsize (rpd_der_norm c r) \<le>
    rsize (RALTS (rdistinct (rflts (rpder_norm_list c r)) {}))"
    unfolding rpd_der_norm_def by (rule rsimp_aalts_smaller)
  also have "... = Suc (rsizes (rdistinct (rflts (rpder_norm_list c r)) {}))"
    by simp
  also have "... \<le> Suc (rsizes (rflts (rpder_norm_list c r)))"
    using rdistinct_smaller[of "rflts (rpder_norm_list c r)" "{}"] by simp
  also have "... \<le> Suc (rsizes (rpder_norm_list c r))"
    using rflts_mono[of "rpder_norm_list c r"] by simp
  finally show ?thesis .
qed

fun rders_pder :: "rrexp \<Rightarrow> string \<Rightarrow> rrexp" where
  "rders_pder r [] = r"
| "rders_pder r (c # s) = rders_pder (rpd_der c r) s"

fun rders_pder_norm :: "rrexp \<Rightarrow> string \<Rightarrow> rrexp" where
  "rders_pder_norm r [] = r"
| "rders_pder_norm r (c # s) = rders_pder_norm (rpd_der_norm c r) s"

fun rders_pder_norm6 :: "rrexp \<Rightarrow> string \<Rightarrow> rrexp" where
  "rders_pder_norm6 r [] = r"
| "rders_pder_norm6 r (c # s) = rders_pder_norm6 (rpd_der_norm6 c r) s"

fun rpders_norm_set :: "rrexp set \<Rightarrow> string \<Rightarrow> rrexp set" where
  "rpders_norm_set rs [] = rs"
| "rpders_norm_set rs (c # s) = rpders_norm_set (rpder_norm_set c rs) s"

fun rpders_norm6_set :: "rrexp set \<Rightarrow> string \<Rightarrow> rrexp set" where
  "rpders_norm6_set rs [] = rs"
| "rpders_norm6_set rs (c # s) = rpders_norm6_set (rpder_norm6_set c rs) s"

definition rpders_norm1 :: "rrexp \<Rightarrow> string \<Rightarrow> rrexp set" where
  "rpders_norm1 r s = rpders_norm_set {r} s"

definition rpders_norm16 :: "rrexp \<Rightarrow> string \<Rightarrow> rrexp set" where
  "rpders_norm16 r s = rpders_norm6_set {r} s"

fun rpders_norm_rows :: "rrexp list \<Rightarrow> string \<Rightarrow> rrexp list" where
  "rpders_norm_rows rs [] = rs"
| "rpders_norm_rows rs (c # s) = rpders_norm_rows (rpder_norm_rows c rs) s"

fun rpders_norm6_rows :: "rrexp list \<Rightarrow> string \<Rightarrow> rrexp list" where
  "rpders_norm6_rows rs [] = rs"
| "rpders_norm6_rows rs (c # s) = rpders_norm6_rows (rpder_norm6_rows c rs) s"

definition rpders_norm1_rows :: "rrexp \<Rightarrow> string \<Rightarrow> rrexp list" where
  "rpders_norm1_rows r s = rpders_norm_rows [r] s"

definition rpders_norm16_rows :: "rrexp \<Rightarrow> string \<Rightarrow> rrexp list" where
  "rpders_norm16_rows r s = rpders_norm6_rows [r] s"

lemma finite_rpder_norm_set [simp]:
  assumes "finite rs"
  shows "finite (rpder_norm_set c rs)"
  using assms unfolding rpder_norm_set_def by auto

lemma finite_rpder_norm6_set [simp]:
  assumes "finite rs"
  shows "finite (rpder_norm6_set c rs)"
  using assms unfolding rpder_norm6_set_def by auto

lemma finite_rpders_norm_set [simp]:
  assumes "finite rs"
  shows "finite (rpders_norm_set rs s)"
  using assms by (induct s arbitrary: rs) auto

lemma finite_rpders_norm6_set [simp]:
  assumes "finite rs"
  shows "finite (rpders_norm6_set rs s)"
  using assms by (induct s arbitrary: rs) auto

lemma distinct_rpder_norm_rows [simp]:
  "distinct (rpder_norm_rows c rs)"
  by (simp add: rpder_norm_rows_def rdistinct_does_the_job)

lemma distinct_rpder_norm6_rows [simp]:
  "distinct (rpder_norm6_rows c rs)"
  by (simp add: rpder_norm6_rows_def rdistinct_does_the_job)

lemma distinct_rpders_norm_rows:
  assumes "distinct rs"
  shows "distinct (rpders_norm_rows rs s)"
  using assms by (induct s arbitrary: rs) simp_all

lemma distinct_rpders_norm6_rows:
  assumes "distinct rs"
  shows "distinct (rpders_norm6_rows rs s)"
  using assms by (induct s arbitrary: rs) simp_all

lemma distinct_rpders_norm1_rows [simp]:
  "distinct (rpders_norm1_rows r s)"
  by (simp add: rpders_norm1_rows_def distinct_rpders_norm_rows)

lemma distinct_rpders_norm16_rows [simp]:
  "distinct (rpders_norm16_rows r s)"
  by (simp add: rpders_norm16_rows_def distinct_rpders_norm6_rows)

lemma legacy_rpd_der:
  assumes "legacy_rrexp r"
  shows "legacy_rrexp (rpd_der c r)"
proof -
  have elems: "\<forall>p \<in> set (rpder_list c r). legacy_rrexp p"
    using assms legacy_rpder set_rpder_list by blast
  have flat: "\<forall>p \<in> set (rflts (rpder_list c r)). legacy_rrexp p"
    by (rule legacy_rflts[OF elems])
  have distinct:
    "\<forall>p \<in> set (rdistinct (rflts (rpder_list c r)) {}). legacy_rrexp p"
    by (rule legacy_rdistinct[OF flat])
  show ?thesis
    unfolding rpd_der_def by (rule legacy_rsimp_ALTs[OF distinct])
qed

lemma legacy_rpder_norm_list:
  assumes "legacy_rrexp r"
  shows "\<forall>p \<in> set (rpder_norm_list c r). legacy_rrexp p"
proof -
  have elems: "\<forall>p \<in> set (rpder_list c r). legacy_rrexp p"
    using assms legacy_rpder set_rpder_list by blast
  show ?thesis
    unfolding rpder_norm_list_def
    using elems legacy_rsimp4_SEQ_atom[of _ RONE]
    by auto
qed

lemma legacy_rpd_der_norm:
  assumes "legacy_rrexp r"
  shows "legacy_rrexp (rpd_der_norm c r)"
proof -
  have elems: "\<forall>p \<in> set (rpder_norm_list c r). legacy_rrexp p"
    by (rule legacy_rpder_norm_list[OF assms])
  have flat: "\<forall>p \<in> set (rflts (rpder_norm_list c r)). legacy_rrexp p"
    by (rule legacy_rflts[OF elems])
  have distinct:
    "\<forall>p \<in> set (rdistinct (rflts (rpder_norm_list c r)) {}). legacy_rrexp p"
    by (rule legacy_rdistinct[OF flat])
  show ?thesis
    unfolding rpd_der_norm_def by (rule legacy_rsimp_ALTs[OF distinct])
qed

lemma legacy_rpder_norm6_list:
  assumes "legacy_rrexp r"
  shows "\<forall>p \<in> set (rpder_norm6_list c r). legacy_rrexp p"
proof -
  have elems: "\<forall>p \<in> set (rpder_norm_list c r). legacy_rrexp p"
    by (rule legacy_rpder_norm_list[OF assms])
  show ?thesis
    unfolding rpder_norm6_list_def
    using elems legacy_rsimp6 by auto
qed

lemma legacy_rpd_der_norm6:
  assumes "legacy_rrexp r"
  shows "legacy_rrexp (rpd_der_norm6 c r)"
proof -
  have elems: "\<forall>p \<in> set (rpder_norm6_list c r). legacy_rrexp p"
    by (rule legacy_rpder_norm6_list[OF assms])
  have flat: "\<forall>p \<in> set (rflts (rpder_norm6_list c r)). legacy_rrexp p"
    by (rule legacy_rflts[OF elems])
  have distinct:
    "\<forall>p \<in> set (rdistinct (rflts (rpder_norm6_list c r)) {}). legacy_rrexp p"
    by (rule legacy_rdistinct[OF flat])
  show ?thesis
    unfolding rpd_der_norm6_def by (rule legacy_rsimp_ALTs[OF distinct])
qed

lemma legacy_rpder_norm_set:
  assumes "\<forall>r \<in> rs. legacy_rrexp r"
      and "p \<in> rpder_norm_set c rs"
  shows "legacy_rrexp p"
  using assms legacy_rpder_norm_list
  unfolding rpder_norm_set_def by blast

lemma legacy_rpder_norm6_set:
  assumes "\<forall>r \<in> rs. legacy_rrexp r"
      and "p \<in> rpder_norm6_set c rs"
  shows "legacy_rrexp p"
  using assms legacy_rpder_norm6_list
  unfolding rpder_norm6_set_def by blast

lemma legacy_rpder_norm_rows:
  assumes "\<forall>r \<in> set rs. legacy_rrexp r"
  shows "\<forall>p \<in> set (rpder_norm_rows c rs). legacy_rrexp p"
proof -
  have elems:
    "\<forall>p \<in> set (concat (map (rpder_norm_list c) rs)). legacy_rrexp p"
    using assms legacy_rpder_norm_list by auto
  have flat:
    "\<forall>p \<in> set (rflts (concat (map (rpder_norm_list c) rs))). legacy_rrexp p"
    by (rule legacy_rflts[OF elems])
  have distinct:
    "\<forall>p \<in> set (rdistinct (rflts (concat (map (rpder_norm_list c) rs))) {}). legacy_rrexp p"
    by (rule legacy_rdistinct[OF flat])
  then show ?thesis
    by (simp add: rpder_norm_rows_def)
qed

lemma legacy_rpder_norm6_rows:
  assumes "\<forall>r \<in> set rs. legacy_rrexp r"
  shows "\<forall>p \<in> set (rpder_norm6_rows c rs). legacy_rrexp p"
proof -
  have elems:
    "\<forall>p \<in> set (concat (map (rpder_norm6_list c) rs)). legacy_rrexp p"
    using assms legacy_rpder_norm6_list by auto
  have flat:
    "\<forall>p \<in> set (rflts (concat (map (rpder_norm6_list c) rs))). legacy_rrexp p"
    by (rule legacy_rflts[OF elems])
  have distinct:
    "\<forall>p \<in> set (rdistinct (rflts (concat (map (rpder_norm6_list c) rs))) {}). legacy_rrexp p"
    by (rule legacy_rdistinct[OF flat])
  then show ?thesis
    by (simp add: rpder_norm6_rows_def)
qed

lemma legacy_rders_pder:
  assumes "legacy_rrexp r"
  shows "legacy_rrexp (rders_pder r s)"
  using assms
  by (induct s arbitrary: r) (auto simp add: legacy_rpd_der)

lemma legacy_rders_pder_norm:
  assumes "legacy_rrexp r"
  shows "legacy_rrexp (rders_pder_norm r s)"
  using assms
  by (induct s arbitrary: r) (auto simp add: legacy_rpd_der_norm)

lemma legacy_rders_pder_norm6:
  assumes "legacy_rrexp r"
  shows "legacy_rrexp (rders_pder_norm6 r s)"
  using assms
  by (induct s arbitrary: r) (auto simp add: legacy_rpd_der_norm6)

lemma legacy_rpders_norm_set:
  assumes "\<forall>r \<in> rs. legacy_rrexp r"
      and "p \<in> rpders_norm_set rs s"
  shows "legacy_rrexp p"
  using assms
proof (induct s arbitrary: rs)
  case Nil
  then show ?case by simp
next
  case (Cons c s)
  have next_legacy: "\<forall>r \<in> rpder_norm_set c rs. legacy_rrexp r"
    using Cons.prems(1) legacy_rpder_norm_set by blast
  have p_next: "p \<in> rpders_norm_set (rpder_norm_set c rs) s"
    using Cons.prems(2) by simp
  show ?case
    by (rule Cons.hyps[OF next_legacy p_next])
qed

lemma legacy_rpders_norm6_set:
  assumes "\<forall>r \<in> rs. legacy_rrexp r"
      and "p \<in> rpders_norm6_set rs s"
  shows "legacy_rrexp p"
  using assms
proof (induct s arbitrary: rs)
  case Nil
  then show ?case by simp
next
  case (Cons c s)
  have next_legacy: "\<forall>r \<in> rpder_norm6_set c rs. legacy_rrexp r"
    using Cons.prems(1) legacy_rpder_norm6_set by blast
  have p_next: "p \<in> rpders_norm6_set (rpder_norm6_set c rs) s"
    using Cons.prems(2) by simp
  show ?case
    by (rule Cons.hyps[OF next_legacy p_next])
qed

lemma legacy_rpders_norm_rows:
  assumes "\<forall>r \<in> set rs. legacy_rrexp r"
      and "p \<in> set (rpders_norm_rows rs s)"
  shows "legacy_rrexp p"
  using assms
proof (induct s arbitrary: rs)
  case Nil
  then show ?case by simp
next
  case (Cons c s)
  have next_legacy: "\<forall>r \<in> set (rpder_norm_rows c rs). legacy_rrexp r"
    by (rule legacy_rpder_norm_rows[OF Cons.prems(1)])
  have p_next: "p \<in> set (rpders_norm_rows (rpder_norm_rows c rs) s)"
    using Cons.prems(2) by simp
  show ?case
    by (rule Cons.hyps[OF next_legacy p_next])
qed

lemma legacy_rpders_norm6_rows:
  assumes "\<forall>r \<in> set rs. legacy_rrexp r"
      and "p \<in> set (rpders_norm6_rows rs s)"
  shows "legacy_rrexp p"
  using assms
proof (induct s arbitrary: rs)
  case Nil
  then show ?case by simp
next
  case (Cons c s)
  have next_legacy: "\<forall>r \<in> set (rpder_norm6_rows c rs). legacy_rrexp r"
    by (rule legacy_rpder_norm6_rows[OF Cons.prems(1)])
  have p_next: "p \<in> set (rpders_norm6_rows (rpder_norm6_rows c rs) s)"
    using Cons.prems(2) by simp
  show ?case
    by (rule Cons.hyps[OF next_legacy p_next])
qed

lemma RL_rpd_der:
  assumes "legacy_rrexp r"
  shows "RL (rpd_der c r) = Der c (RL r)"
proof -
  have "RL (rpd_der c r) = (\<Union> (set (map RL (rpder_list c r))))"
    unfolding rpd_der_def by (rule RL_rsimp_ALTs_normalize)
  also have "... = RLS (rpder c r)"
    unfolding RLS_def using set_rpder_list[of c r] by auto
  also have "... = Der c (RL r)"
    by (rule RLS_rpder[OF assms])
  finally show ?thesis .
qed

lemma RL_rsimp4_SEQ_atom_RONE:
  "RL (rsimp4_SEQ_atom p RONE) = RL p"
  using RL_rsimp4_SEQ_atom[of p RONE]
  by (simp add: Sequ_def)

lemma RL_rpder_norm_list:
  "(\<Union> (set (map RL (rpder_norm_list c r)))) =
    (\<Union> (set (map RL (rpder_list c r))))"
  unfolding rpder_norm_list_def
  by (auto simp add: RL_rsimp4_SEQ_atom_RONE)

lemma RL_rpder_norm6_list:
  "(\<Union> (set (map RL (rpder_norm6_list c r)))) =
    (\<Union> (set (map RL (rpder_norm_list c r))))"
  unfolding rpder_norm6_list_def
  by (auto simp add: RL_rsimp6[symmetric])

lemma RL_rpd_der_norm:
  assumes "legacy_rrexp r"
  shows "RL (rpd_der_norm c r) = Der c (RL r)"
proof -
  have "RL (rpd_der_norm c r) =
    (\<Union> (set (map RL (rpder_norm_list c r))))"
    unfolding rpd_der_norm_def by (rule RL_rsimp_ALTs_normalize)
  also have "... = (\<Union> (set (map RL (rpder_list c r))))"
    by (rule RL_rpder_norm_list)
  also have "... = RLS (rpder c r)"
    unfolding RLS_def using set_rpder_list[of c r] by auto
  also have "... = Der c (RL r)"
    by (rule RLS_rpder[OF assms])
  finally show ?thesis .
qed

lemma RL_rpd_der_norm6:
  assumes "legacy_rrexp r"
  shows "RL (rpd_der_norm6 c r) = Der c (RL r)"
proof -
  have "RL (rpd_der_norm6 c r) =
    (\<Union> (set (map RL (rpder_norm6_list c r))))"
    unfolding rpd_der_norm6_def by (rule RL_rsimp_ALTs_normalize)
  also have "... = (\<Union> (set (map RL (rpder_norm_list c r))))"
    by (rule RL_rpder_norm6_list)
  also have "... = Der c (RL r)"
    by (simp add: RL_rpd_der_norm[OF assms, symmetric] rpd_der_norm_def RL_rsimp_ALTs_normalize)
  finally show ?thesis .
qed

lemma RLS_rpder_norm_set:
  assumes "\<forall>r \<in> rs. legacy_rrexp r"
  shows "RLS (rpder_norm_set c rs) = Der c (RLS rs)"
proof -
  have "RLS (rpder_norm_set c rs) =
    (\<Union>r \<in> rs. \<Union> (set (map RL (rpder_norm_list c r))))"
    unfolding RLS_def rpder_norm_set_def by auto
  also have "... = (\<Union>r \<in> rs. \<Union> (set (map RL (rpder_list c r))))"
    using RL_rpder_norm_list by simp
  also have "... = (\<Union>r \<in> rs. RLS (rpder c r))"
    unfolding RLS_def using set_rpder_list by auto
  also have "... = (\<Union>r \<in> rs. Der c (RL r))"
    using assms RLS_rpder by blast
  also have "... = Der c (RLS rs)"
    unfolding RLS_def Der_def by auto
  finally show ?thesis .
qed

lemma RLS_rpder_norm6_set:
  assumes "\<forall>r \<in> rs. legacy_rrexp r"
  shows "RLS (rpder_norm6_set c rs) = Der c (RLS rs)"
proof -
  have "RLS (rpder_norm6_set c rs) =
    (\<Union>r \<in> rs. \<Union> (set (map RL (rpder_norm6_list c r))))"
    unfolding RLS_def rpder_norm6_set_def by auto
  also have "... =
    (\<Union>r \<in> rs. \<Union> (set (map RL (rpder_norm_list c r))))"
    using RL_rpder_norm6_list by simp
  also have "... = RLS (rpder_norm_set c rs)"
    unfolding RLS_def rpder_norm_set_def by auto
  also have "... = Der c (RLS rs)"
    by (rule RLS_rpder_norm_set[OF assms])
  finally show ?thesis .
qed

lemma RLS_set_rdistinct_rflts:
  "RLS (set (rdistinct (rflts rs) {})) = RLS (set rs)"
  unfolding RLS_def
  using RL_rsimp_rdistinct[of "rflts rs"] RL_rsimp_rflts[of rs]
  by simp

lemma RLS_set_concat_rpder_norm_list:
  "RLS (set (concat (map (rpder_norm_list c) rs))) =
    RLS (rpder_norm_set c (set rs))"
  unfolding RLS_def rpder_norm_set_def by auto

lemma RLS_set_concat_rpder_norm6_list:
  "RLS (set (concat (map (rpder_norm6_list c) rs))) =
    RLS (rpder_norm6_set c (set rs))"
  unfolding RLS_def rpder_norm6_set_def by auto

lemma RLS_rpder_norm_rows:
  assumes "\<forall>r \<in> set rs. legacy_rrexp r"
  shows "RLS (set (rpder_norm_rows c rs)) = Der c (RLS (set rs))"
proof -
  have "RLS (set (rpder_norm_rows c rs)) =
    RLS (set (concat (map (rpder_norm_list c) rs)))"
    unfolding rpder_norm_rows_def by (rule RLS_set_rdistinct_rflts)
  also have "... = RLS (rpder_norm_set c (set rs))"
    by (rule RLS_set_concat_rpder_norm_list)
  also have "... = Der c (RLS (set rs))"
    by (rule RLS_rpder_norm_set) (use assms in auto)
  finally show ?thesis .
qed

lemma RLS_rpder_norm6_rows:
  assumes "\<forall>r \<in> set rs. legacy_rrexp r"
  shows "RLS (set (rpder_norm6_rows c rs)) = Der c (RLS (set rs))"
proof -
  have "RLS (set (rpder_norm6_rows c rs)) =
    RLS (set (concat (map (rpder_norm6_list c) rs)))"
    unfolding rpder_norm6_rows_def by (rule RLS_set_rdistinct_rflts)
  also have "... = RLS (rpder_norm6_set c (set rs))"
    by (rule RLS_set_concat_rpder_norm6_list)
  also have "... = Der c (RLS (set rs))"
    by (rule RLS_rpder_norm6_set) (use assms in auto)
  finally show ?thesis .
qed

lemma RL_rders_pder:
  assumes "legacy_rrexp r"
  shows "RL (rders_pder r s) = Ders s (RL r)"
  using assms
proof (induct s arbitrary: r)
  case Nil
  then show ?case by (simp add: Ders_def)
next
  case (Cons c s)
  have next_legacy: "legacy_rrexp (rpd_der c r)"
    by (rule legacy_rpd_der[OF Cons.prems])
  have "RL (rders_pder r (c # s)) = Ders s (RL (rpd_der c r))"
    by (simp add: Cons.hyps[OF next_legacy])
  also have "... = Ders s (Der c (RL r))"
    by (simp add: RL_rpd_der[OF Cons.prems])
  also have "... = Ders (c # s) (RL r)"
    by (simp add: Ders_Cons)
  finally show ?case .
qed

lemma RLS_rpders_norm_set:
  assumes "\<forall>r \<in> rs. legacy_rrexp r"
  shows "RLS (rpders_norm_set rs s) = Ders s (RLS rs)"
  using assms
proof (induct s arbitrary: rs)
  case Nil
  then show ?case
    by (simp add: Ders_def)
next
  case (Cons c s)
  have next_legacy: "\<forall>r \<in> rpder_norm_set c rs. legacy_rrexp r"
    using Cons.prems legacy_rpder_norm_set by blast
  have "RLS (rpders_norm_set rs (c # s)) =
    Ders s (RLS (rpder_norm_set c rs))"
    by (simp add: Cons.hyps[OF next_legacy])
  also have "... = Ders s (Der c (RLS rs))"
    by (simp add: RLS_rpder_norm_set[OF Cons.prems])
  also have "... = Ders (c # s) (RLS rs)"
    by (simp add: Ders_Cons)
  finally show ?case .
qed

lemma RLS_rpders_norm6_set:
  assumes "\<forall>r \<in> rs. legacy_rrexp r"
  shows "RLS (rpders_norm6_set rs s) = Ders s (RLS rs)"
  using assms
proof (induct s arbitrary: rs)
  case Nil
  then show ?case
    by (simp add: Ders_def)
next
  case (Cons c s)
  have next_legacy: "\<forall>r \<in> rpder_norm6_set c rs. legacy_rrexp r"
    using Cons.prems legacy_rpder_norm6_set by blast
  have "RLS (rpders_norm6_set rs (c # s)) =
    Ders s (RLS (rpder_norm6_set c rs))"
    by (simp add: Cons.hyps[OF next_legacy])
  also have "... = Ders s (Der c (RLS rs))"
    by (simp add: RLS_rpder_norm6_set[OF Cons.prems])
  also have "... = Ders (c # s) (RLS rs)"
    by (simp add: Ders_Cons)
  finally show ?case .
qed

lemma RLS_rpders_norm1:
  assumes "legacy_rrexp r"
  shows "RLS (rpders_norm1 r s) = Ders s (RL r)"
  using RLS_rpders_norm_set[of "{r}" s] assms
  by (simp add: rpders_norm1_def RLS_def)

lemma RLS_rpders_norm16:
  assumes "legacy_rrexp r"
  shows "RLS (rpders_norm16 r s) = Ders s (RL r)"
  using RLS_rpders_norm6_set[of "{r}" s] assms
  by (simp add: rpders_norm16_def RLS_def)

lemma RLS_rpders_norm_rows:
  assumes "\<forall>r \<in> set rs. legacy_rrexp r"
  shows "RLS (set (rpders_norm_rows rs s)) = Ders s (RLS (set rs))"
  using assms
proof (induct s arbitrary: rs)
  case Nil
  then show ?case
    by (simp add: Ders_def)
next
  case (Cons c s)
  have next_legacy: "\<forall>r \<in> set (rpder_norm_rows c rs). legacy_rrexp r"
    by (rule legacy_rpder_norm_rows[OF Cons.prems])
  have "RLS (set (rpders_norm_rows rs (c # s))) =
    Ders s (RLS (set (rpder_norm_rows c rs)))"
    by (simp add: Cons.hyps[OF next_legacy])
  also have "... = Ders s (Der c (RLS (set rs)))"
    by (simp add: RLS_rpder_norm_rows[OF Cons.prems])
  also have "... = Ders (c # s) (RLS (set rs))"
    by (simp add: Ders_Cons)
  finally show ?case .
qed

lemma RLS_rpders_norm6_rows:
  assumes "\<forall>r \<in> set rs. legacy_rrexp r"
  shows "RLS (set (rpders_norm6_rows rs s)) = Ders s (RLS (set rs))"
  using assms
proof (induct s arbitrary: rs)
  case Nil
  then show ?case
    by (simp add: Ders_def)
next
  case (Cons c s)
  have next_legacy: "\<forall>r \<in> set (rpder_norm6_rows c rs). legacy_rrexp r"
    by (rule legacy_rpder_norm6_rows[OF Cons.prems])
  have "RLS (set (rpders_norm6_rows rs (c # s))) =
    Ders s (RLS (set (rpder_norm6_rows c rs)))"
    by (simp add: Cons.hyps[OF next_legacy])
  also have "... = Ders s (Der c (RLS (set rs)))"
    by (simp add: RLS_rpder_norm6_rows[OF Cons.prems])
  also have "... = Ders (c # s) (RLS (set rs))"
    by (simp add: Ders_Cons)
  finally show ?case .
qed

lemma RLS_rpders_norm1_rows:
  assumes "legacy_rrexp r"
  shows "RLS (set (rpders_norm1_rows r s)) = Ders s (RL r)"
  using RLS_rpders_norm_rows[of "[r]" s] assms
  by (simp add: rpders_norm1_rows_def RLS_def)

lemma RLS_rpders_norm16_rows:
  assumes "legacy_rrexp r"
  shows "RLS (set (rpders_norm16_rows r s)) = Ders s (RL r)"
  using RLS_rpders_norm6_rows[of "[r]" s] assms
  by (simp add: rpders_norm16_rows_def RLS_def)

lemma RL_rders_pder_norm:
  assumes "legacy_rrexp r"
  shows "RL (rders_pder_norm r s) = Ders s (RL r)"
  using assms
proof (induct s arbitrary: r)
  case Nil
  then show ?case by (simp add: Ders_def)
next
  case (Cons c s)
  have next_legacy: "legacy_rrexp (rpd_der_norm c r)"
    by (rule legacy_rpd_der_norm[OF Cons.prems])
  have "RL (rders_pder_norm r (c # s)) = Ders s (RL (rpd_der_norm c r))"
    by (simp add: Cons.hyps[OF next_legacy])
  also have "... = Ders s (Der c (RL r))"
    by (simp add: RL_rpd_der_norm[OF Cons.prems])
  also have "... = Ders (c # s) (RL r)"
    by (simp add: Ders_Cons)
  finally show ?case .
qed

lemma RL_rders_pder_norm6:
  assumes "legacy_rrexp r"
  shows "RL (rders_pder_norm6 r s) = Ders s (RL r)"
  using assms
proof (induct s arbitrary: r)
  case Nil
  then show ?case by (simp add: Ders_def)
next
  case (Cons c s)
  have next_legacy: "legacy_rrexp (rpd_der_norm6 c r)"
    by (rule legacy_rpd_der_norm6[OF Cons.prems])
  have "RL (rders_pder_norm6 r (c # s)) = Ders s (RL (rpd_der_norm6 c r))"
    by (simp add: Cons.hyps[OF next_legacy])
  also have "... = Ders s (Der c (RL r))"
    by (simp add: RL_rpd_der_norm6[OF Cons.prems])
  also have "... = Ders (c # s) (RL r)"
    by (simp add: Ders_Cons)
  finally show ?case .
qed

fun rsubterms :: "rrexp \<Rightarrow> rrexp set" where
  "rsubterms RZERO = {RZERO}"
| "rsubterms RONE = {RONE}"
| "rsubterms (RCHAR c) = {RCHAR c}"
| "rsubterms (RALTS rs) = insert (RALTS rs) (\<Union> (set (map rsubterms rs)))"
| "rsubterms (RSEQ r1 r2) = insert (RSEQ r1 r2) (rsubterms r1 \<union> rsubterms r2)"
| "rsubterms (RSTAR r) = insert (RSTAR r) (rsubterms r)"
| "rsubterms (RNTIMES r n) = insert (RNTIMES r n) (rsubterms r)"
| "rsubterms (RBACKREF4 r1 r2 r3 r4 cs) =
    insert (RBACKREF4 r1 r2 r3 r4 cs)
      (rsubterms r1 \<union> rsubterms r2 \<union> rsubterms r3 \<union> rsubterms r4)"
| "rsubterms (RHALF r cs rep) = insert (RHALF r cs rep) (rsubterms r)"
| "rsubterms (RRESIDUE cs rep) = {RRESIDUE cs rep}"

lemma finite_rsubterms [simp]:
  "finite (rsubterms r)"
  by (induct r) auto

lemma self_rsubterm [simp]:
  "r \<in> rsubterms r"
  by (induct r) auto

lemma finite_rsubterms_list [simp]:
  "finite (\<Union> (set (map rsubterms rs)))"
  by (induct rs) auto

lemma card_Un3_le:
  "card (A \<union> B \<union> C) \<le> card A + card B + card C"
proof -
  have "card (A \<union> B \<union> C) \<le> card (A \<union> B) + card C"
    by (rule card_Un_le)
  also have "... \<le> card A + card B + card C"
    using card_Un_le[of A B] by simp
  finally show ?thesis .
qed

lemma card_Un4_le:
  "card (A \<union> B \<union> C \<union> D) \<le> card A + card B + card C + card D"
proof -
  have "card (A \<union> B \<union> C \<union> D) \<le> card (A \<union> B \<union> C) + card D"
    by (rule card_Un_le)
  also have "... \<le> card A + card B + card C + card D"
    using card_Un3_le[of A B C] by simp
  finally show ?thesis .
qed

lemma card_rsubterms_list_le_rsizes:
  assumes step: "\<And>r. r \<in> set rs \<Longrightarrow> card (rsubterms r) \<le> rsize r"
  shows "card (\<Union> (set (map rsubterms rs))) \<le> rsizes rs"
  using step
proof (induct rs)
  case Nil
  then show ?case by simp
next
  case (Cons r rs)
  have "card (\<Union> (set (map rsubterms (r # rs)))) =
    card (rsubterms r \<union> (\<Union> (set (map rsubterms rs))))"
    by simp
  also have "... \<le> card (rsubterms r) + card (\<Union> (set (map rsubterms rs)))"
    by (rule card_Un_le)
  also have "... \<le> rsize r + rsizes rs"
  proof -
    have r_le: "card (rsubterms r) \<le> rsize r"
      using Cons.prems by simp
    have rs_le: "card (\<Union> (set (map rsubterms rs))) \<le> rsizes rs"
      using Cons.hyps Cons.prems by simp
    show ?thesis
      using r_le rs_le by linarith
  qed
  finally show ?case
    by simp
qed

lemma card_insert_le_Suc:
  assumes "finite A"
  shows "card (insert x A) \<le> Suc (card A)"
  using assms by (simp add: card_insert_if)

lemma card_insert2_Un_le:
  assumes "finite A" "finite B"
  shows "card (insert x (insert y (A \<union> B))) \<le> 2 + card A + card B"
proof -
  have "card (insert x (insert y (A \<union> B))) \<le> Suc (card (insert y (A \<union> B)))"
    by (rule card_insert_le_Suc) (simp add: assms)
  also have "... \<le> Suc (Suc (card (A \<union> B)))"
    using assms card_insert_le_Suc[of "A \<union> B" y] by simp
  also have "... \<le> 2 + card A + card B"
    using card_Un_le[of A B] by simp
  finally show ?thesis .
qed

lemma cubic_padding_bound:
  fixes n :: nat
  shows "2 + n + n * (n * (n + 3)) \<le> (n + 3) ^ 3"
proof -
  have "(n + 3) ^ 3 = n * (n * (n + 3)) + (6 * n + 9) * (n + 3)"
    by (simp add: algebra_simps power3_eq_cube)
  moreover have "2 + n \<le> (6 * n + 9) * (n + 3)"
  proof -
    have "2 + n \<le> 6 * n + 9"
      by simp
    also have "... \<le> (6 * n + 9) * (n + 3)"
    proof -
      have "(6 * n + 9) * 1 \<le> (6 * n + 9) * (n + 3)"
        by (rule mult_le_mono2) simp
      then show ?thesis
        by simp
    qed
    finally show ?thesis .
  qed
  ultimately show ?thesis
    by simp
qed

lemma card_rsubterms_le_rsize:
  "card (rsubterms r) \<le> rsize r"
proof (induct r)
  case RZERO
  then show ?case by simp
next
  case RONE
  then show ?case by simp
next
  case (RCHAR x)
  then show ?case by simp
next
  case (RALTS rs)
  have "card (rsubterms (RALTS rs)) \<le>
    Suc (card (\<Union> (set (map rsubterms rs))))"
    by (simp add: card_insert_le_Suc)
  also have "... \<le> Suc (rsizes rs)"
    using card_rsubterms_list_le_rsizes[of rs] RALTS by simp
  finally show ?case
    by simp
next
  case (RSEQ r1 r2)
  have "card (rsubterms (RSEQ r1 r2)) \<le>
    Suc (card (rsubterms r1 \<union> rsubterms r2))"
    by (simp add: card_insert_le_Suc)
  also have "... \<le> Suc (card (rsubterms r1) + card (rsubterms r2))"
    using card_Un_le by simp
  also have "... \<le> rsize (RSEQ r1 r2)"
    using RSEQ by simp
  finally show ?case .
next
  case (RSTAR r)
  have "card (rsubterms (RSTAR r)) \<le> Suc (card (rsubterms r))"
    by (simp add: card_insert_le_Suc)
  also have "... \<le> rsize (RSTAR r)"
    using RSTAR by simp
  finally show ?case .
next
  case (RNTIMES r n)
  have "card (rsubterms (RNTIMES r n)) \<le> Suc (card (rsubterms r))"
    by (simp add: card_insert_le_Suc)
  also have "... \<le> rsize (RNTIMES r n)"
    using RNTIMES by simp
  finally show ?case .
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  have "card (rsubterms (RBACKREF4 r1 r2 r3 r4 cs)) \<le>
    Suc (card (rsubterms r1 \<union> rsubterms r2 \<union> rsubterms r3 \<union> rsubterms r4))"
    by (simp add: card_insert_le_Suc)
  also have "... \<le>
    Suc (card (rsubterms r1) + card (rsubterms r2) +
      card (rsubterms r3) + card (rsubterms r4))"
    using card_Un4_le[of "rsubterms r1" "rsubterms r2" "rsubterms r3" "rsubterms r4"] by simp
  also have "... \<le> rsize (RBACKREF4 r1 r2 r3 r4 cs)"
    using RBACKREF4 by simp
  finally show ?case .
next
  case (RHALF r cs rep)
  have "card (rsubterms (RHALF r cs rep)) \<le> Suc (card (rsubterms r))"
    by (simp add: card_insert_le_Suc)
  also have "... \<le> rsize (RHALF r cs rep)"
    using RHALF by simp
  finally show ?case .
next
  case (RRESIDUE cs rep)
  then show ?case by simp
qed

lemma rsize_member_le_rsizes:
  assumes "r \<in> set rs"
  shows "rsize r \<le> rsizes rs"
  using assms
  by (induct rs) auto

lemma rsubterms_member_size_le_rsize:
  assumes "q \<in> rsubterms r"
  shows "rsize q \<le> rsize r"
  using assms
proof (induct r arbitrary: q)
  case RZERO
  then show ?case by simp
next
  case RONE
  then show ?case by simp
next
  case (RCHAR x)
  then show ?case by simp
next
  case (RALTS rs)
  then show ?case
  proof (cases "q = RALTS rs")
    case True
    then show ?thesis by simp
  next
    case False
    then obtain r where r: "r \<in> set rs" "q \<in> rsubterms r"
      using RALTS.prems by auto
    have "rsize q \<le> rsize r"
      using RALTS r by auto
    also have "... \<le> rsizes rs"
      using rsize_member_le_rsizes[OF r(1)] .
    finally show ?thesis
      by simp
  qed
next
  case (RSEQ r1 r2)
  then show ?case
  proof (cases "q = RSEQ r1 r2")
    case True
    then show ?thesis by simp
  next
    case False
    then consider "q \<in> rsubterms r1" | "q \<in> rsubterms r2"
      using RSEQ.prems by auto
    then show ?thesis
    proof cases
      case 1
      then have "rsize q \<le> rsize r1"
        using RSEQ by auto
      then show ?thesis by simp
    next
      case 2
      then have "rsize q \<le> rsize r2"
        using RSEQ by auto
      then show ?thesis by simp
    qed
  qed
next
  case (RSTAR r)
  then show ?case
  proof (cases "q = RSTAR r")
    case True
    then show ?thesis by simp
  next
    case False
    then have "q \<in> rsubterms r"
      using RSTAR.prems by auto
    then have "rsize q \<le> rsize r"
      using RSTAR by auto
    then show ?thesis by simp
  qed
next
  case (RNTIMES r n)
  then show ?case
  proof (cases "q = RNTIMES r n")
    case True
    then show ?thesis by simp
  next
    case False
    then have "q \<in> rsubterms r"
      using RNTIMES.prems by auto
    then have "rsize q \<le> rsize r"
      using RNTIMES by auto
    then show ?thesis by simp
  qed
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  then show ?case
  proof (cases "q = RBACKREF4 r1 r2 r3 r4 cs")
    case True
    then show ?thesis by simp
  next
    case False
    then consider "q \<in> rsubterms r1" | "q \<in> rsubterms r2" |
      "q \<in> rsubterms r3" | "q \<in> rsubterms r4"
      using RBACKREF4.prems by auto
    then show ?thesis
    proof cases
      case 1
      then have "rsize q \<le> rsize r1"
        using RBACKREF4 by auto
      then show ?thesis by simp
    next
      case 2
      then have "rsize q \<le> rsize r2"
        using RBACKREF4 by auto
      then show ?thesis by simp
    next
      case 3
      then have "rsize q \<le> rsize r3"
        using RBACKREF4 by auto
      then show ?thesis by simp
    next
      case 4
      then have "rsize q \<le> rsize r4"
        using RBACKREF4 by auto
      then show ?thesis by simp
    qed
  qed
next
  case (RHALF r cs rep)
  then show ?case
  proof (cases "q = RHALF r cs rep")
    case True
    then show ?thesis by simp
  next
    case False
    then have "q \<in> rsubterms r"
      using RHALF.prems by auto
    then have "rsize q \<le> rsize r"
      using RHALF by auto
    then show ?thesis by simp
  qed
next
  case (RRESIDUE cs rep)
  then show ?case by simp
qed

definition rcontinuations :: "rrexp \<Rightarrow> rrexp set" where
  "rcontinuations r =
    rsubterms r \<union>
    RSTAR ` rsubterms r \<union>
    (\<lambda>(s, n). RNTIMES s n) ` (rsubterms r \<times> {..rsize r})"

lemma finite_rcontinuations [simp]:
  "finite (rcontinuations r)"
  by (simp add: rcontinuations_def)

lemma card_rcontinuations_le:
  "card (rcontinuations r) \<le> rsize r * (rsize r + 3)"
proof -
  let ?A = "rsubterms r"
  let ?B = "RSTAR ` ?A"
  let ?C = "(\<lambda>(s, n). RNTIMES s n) ` (?A \<times> {..rsize r})"
  have A: "card ?A \<le> rsize r"
    by (rule card_rsubterms_le_rsize)
  have B: "card ?B \<le> card ?A"
    by (rule card_image_le) simp
  have C: "card ?C \<le> card ?A * Suc (rsize r)"
  proof -
    have "card ?C \<le> card (?A \<times> {..rsize r})"
      by (rule card_image_le) simp
    then show ?thesis
      by simp
  qed
  have "card (rcontinuations r) = card (?A \<union> ?B \<union> ?C)"
    unfolding rcontinuations_def
    by simp
  also have "... \<le> card ?A + card ?B + card ?C"
    by (rule card_Un3_le)
  also have "... \<le> card ?A * (rsize r + 3)"
  proof -
    have "card ?A + card ?B + card ?C \<le>
      card ?A + card ?A + card ?A * Suc (rsize r)"
      using B C by linarith
    also have "... = card ?A * (rsize r + 3)"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  also have "... \<le> rsize r * (rsize r + 3)"
    using A by (simp add: mult_right_mono)
  finally show ?thesis .
qed

definition partial_derivative_universe :: "rrexp \<Rightarrow> rrexp set" where
  "partial_derivative_universe r =
    insert RZERO
      (insert RONE
        (rsubterms r \<union>
         (\<lambda>(p, k). RSEQ p k) ` (rsubterms r \<times> rcontinuations r)))"

lemma finite_partial_derivative_universe [simp]:
  "finite (partial_derivative_universe r)"
  by (simp add: partial_derivative_universe_def)

lemma partial_derivative_universe_card_cubic:
  "card (partial_derivative_universe r) \<le> (rsize r + 3) ^ 3"
proof -
  let ?A = "rsubterms r"
  let ?K = "rcontinuations r"
  let ?P = "(\<lambda>(p, k). RSEQ p k) ` (?A \<times> ?K)"
  have A: "card ?A \<le> rsize r"
    by (rule card_rsubterms_le_rsize)
  have K: "card ?K \<le> rsize r * (rsize r + 3)"
    by (rule card_rcontinuations_le)
  have P: "card ?P \<le> card ?A * card ?K"
  proof -
    have "card ?P \<le> card (?A \<times> ?K)"
      by (rule card_image_le) simp
    then show ?thesis
      by simp
  qed
  have P_size: "card ?P \<le> rsize r * (rsize r * (rsize r + 3))"
  proof -
    have "card ?P \<le> card ?A * (rsize r * (rsize r + 3))"
    proof -
      have "card ?A * card ?K \<le> card ?A * (rsize r * (rsize r + 3))"
        using K by (simp add: mult_left_mono)
      then show ?thesis
        using P by linarith
    qed
    also have "... \<le> rsize r * (rsize r * (rsize r + 3))"
      using A by (simp add: mult_right_mono)
    finally show ?thesis .
  qed
  have "card (partial_derivative_universe r) \<le> 2 + card ?A + card ?P"
    unfolding partial_derivative_universe_def
    by (rule card_insert2_Un_le) simp_all
  also have "... \<le> 2 + rsize r + rsize r * (rsize r * (rsize r + 3))"
    using A P_size by linarith
  also have "... \<le> (rsize r + 3) ^ 3"
    by (rule cubic_padding_bound)
  finally show ?thesis .
qed

fun rlinear_continuations :: "rrexp \<Rightarrow> rrexp set" where
  "rlinear_continuations RZERO = {}"
| "rlinear_continuations RONE = {}"
| "rlinear_continuations (RCHAR c) = {}"
| "rlinear_continuations (RALTS rs) =
    (\<Union> (set (map rlinear_continuations rs)))"
| "rlinear_continuations (RSEQ r1 r2) =
    insert r2 (rlinear_continuations r1 \<union> rlinear_continuations r2)"
| "rlinear_continuations (RSTAR r) =
    insert (RSTAR r) (rlinear_continuations r)"
| "rlinear_continuations (RNTIMES r n) =
    ((\<lambda>k. RNTIMES r k) ` {..n}) \<union> rlinear_continuations r"
| "rlinear_continuations (RBACKREF4 r1 r2 r3 r4 cs) =
    rlinear_continuations r1 \<union> rlinear_continuations r2 \<union>
    rlinear_continuations r3 \<union> rlinear_continuations r4"
| "rlinear_continuations (RHALF r cs rep) = rlinear_continuations r"
| "rlinear_continuations (RRESIDUE cs rep) = {}"

lemma finite_rlinear_continuations [simp]:
  "finite (rlinear_continuations r)"
  by (induct r) auto

lemma finite_rlinear_continuations_list [simp]:
  "finite (\<Union> (set (map rlinear_continuations rs)))"
  by (induct rs) auto

lemma card_rlinear_continuations_list_le_rsizes:
  assumes step: "\<And>r. r \<in> set rs \<Longrightarrow> card (rlinear_continuations r) \<le> rsize r"
  shows "card (\<Union> (set (map rlinear_continuations rs))) \<le> rsizes rs"
  using step
proof (induct rs)
  case Nil
  then show ?case by simp
next
  case (Cons r rs)
  have "card (\<Union> (set (map rlinear_continuations (r # rs)))) =
    card (rlinear_continuations r \<union> (\<Union> (set (map rlinear_continuations rs))))"
    by simp
  also have "... \<le> card (rlinear_continuations r) +
    card (\<Union> (set (map rlinear_continuations rs)))"
    by (rule card_Un_le)
  also have "... \<le> rsize r + rsizes rs"
  proof -
    have r_le: "card (rlinear_continuations r) \<le> rsize r"
      using Cons.prems by simp
    have rs_le: "card (\<Union> (set (map rlinear_continuations rs))) \<le> rsizes rs"
      using Cons.hyps Cons.prems by simp
    show ?thesis
      using r_le rs_le by linarith
  qed
  finally show ?case
    by simp
qed

lemma card_rlinear_continuations_le_rsize:
  "card (rlinear_continuations r) \<le> rsize r"
proof (induct r)
  case RZERO
  then show ?case by simp
next
  case RONE
  then show ?case by simp
next
  case (RCHAR x)
  then show ?case by simp
next
  case (RALTS rs)
  then show ?case
    using card_rlinear_continuations_list_le_rsizes[of rs] by simp
next
  case (RSEQ r1 r2)
  have "card (rlinear_continuations (RSEQ r1 r2)) \<le>
    Suc (card (rlinear_continuations r1 \<union> rlinear_continuations r2))"
    by (simp add: card_insert_le_Suc)
  also have "... \<le> Suc (card (rlinear_continuations r1) +
    card (rlinear_continuations r2))"
    using card_Un_le by simp
  also have "... \<le> rsize (RSEQ r1 r2)"
    using RSEQ by simp
  finally show ?case .
next
  case (RSTAR r)
  have "card (rlinear_continuations (RSTAR r)) \<le>
    Suc (card (rlinear_continuations r))"
    by (simp add: card_insert_le_Suc)
  also have "... \<le> rsize (RSTAR r)"
    using RSTAR by simp
  finally show ?case .
next
  case (RNTIMES r n)
  have upto: "card ((\<lambda>k. RNTIMES r k) ` {..n}) \<le> Suc n"
  proof -
    have "card ((\<lambda>k. RNTIMES r k) ` {..n}) \<le> card ({..n})"
      by (rule card_image_le) simp
    then show ?thesis
      by simp
  qed
  have "card (rlinear_continuations (RNTIMES r n)) =
    card (((\<lambda>k. RNTIMES r k) ` {..n}) \<union> rlinear_continuations r)"
    by simp
  also have "... \<le>
    card ((\<lambda>k. RNTIMES r k) ` {..n}) + card (rlinear_continuations r)"
    by (rule card_Un_le)
  also have "... \<le> Suc n + rsize r"
    using upto RNTIMES by simp
  also have "... \<le> rsize (RNTIMES r n)"
    by simp
  finally show ?case .
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  have "card (rlinear_continuations (RBACKREF4 r1 r2 r3 r4 cs)) \<le>
    card (rlinear_continuations r1) + card (rlinear_continuations r2) +
    card (rlinear_continuations r3) + card (rlinear_continuations r4)"
    using card_Un4_le[of "rlinear_continuations r1" "rlinear_continuations r2"
      "rlinear_continuations r3" "rlinear_continuations r4"] by simp
  also have "... \<le> rsize (RBACKREF4 r1 r2 r3 r4 cs)"
    using RBACKREF4 by simp
  finally show ?case .
next
  case (RHALF r cs rep)
  then show ?case by simp
next
  case (RRESIDUE cs rep)
  then show ?case by simp
qed

lemma rlinear_continuations_member_size_le_rsize:
  assumes "q \<in> rlinear_continuations r"
  shows "rsize q \<le> rsize r"
  using assms
proof (induct r arbitrary: q)
  case RZERO
  then show ?case by simp
next
  case RONE
  then show ?case by simp
next
  case (RCHAR x)
  then show ?case by simp
next
  case (RALTS rs)
  then obtain r where r: "r \<in> set rs" "q \<in> rlinear_continuations r"
    by auto
  have "rsize q \<le> rsize r"
    using RALTS r by auto
  also have "... \<le> rsizes rs"
    using rsize_member_le_rsizes[OF r(1)] .
  finally show ?case
    by simp
next
  case (RSEQ r1 r2)
  then show ?case
  proof (cases "q = r2")
    case True
    then show ?thesis by simp
  next
    case False
    then consider "q \<in> rlinear_continuations r1" | "q \<in> rlinear_continuations r2"
      using RSEQ.prems by auto
    then show ?thesis
    proof cases
      case 1
      then have "rsize q \<le> rsize r1"
        using RSEQ by auto
      then show ?thesis by simp
    next
      case 2
      then have "rsize q \<le> rsize r2"
        using RSEQ by auto
      then show ?thesis by simp
    qed
  qed
next
  case (RSTAR r)
  then show ?case
  proof (cases "q = RSTAR r")
    case True
    then show ?thesis by simp
  next
    case False
    then have "q \<in> rlinear_continuations r"
      using RSTAR.prems by auto
    then have "rsize q \<le> rsize r"
      using RSTAR by auto
    then show ?thesis by simp
  qed
next
  case (RNTIMES r n)
  then show ?case
  proof (cases "q \<in> ((\<lambda>k. RNTIMES r k) ` {..n})")
    case True
    then obtain k where k: "k \<le> n" "q = RNTIMES r k"
      by auto
    then show ?thesis
      by simp
  next
    case False
    then have "q \<in> rlinear_continuations r"
      using RNTIMES.prems by auto
    then have "rsize q \<le> rsize r"
      using RNTIMES by auto
    then show ?thesis
      by simp
  qed
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  then consider "q \<in> rlinear_continuations r1" |
    "q \<in> rlinear_continuations r2" |
    "q \<in> rlinear_continuations r3" |
    "q \<in> rlinear_continuations r4"
    by auto
  then show ?case
  proof cases
    case 1
    then have "rsize q \<le> rsize r1"
      using RBACKREF4 by auto
    then show ?thesis by simp
  next
    case 2
    then have "rsize q \<le> rsize r2"
      using RBACKREF4 by auto
    then show ?thesis by simp
  next
    case 3
    then have "rsize q \<le> rsize r3"
      using RBACKREF4 by auto
    then show ?thesis by simp
  next
    case 4
    then have "rsize q \<le> rsize r4"
      using RBACKREF4 by auto
    then show ?thesis by simp
  qed
next
  case (RHALF r cs rep)
  then have "q \<in> rlinear_continuations r"
    by auto
  then have "rsize q \<le> rsize r"
    using RHALF by auto
  then show ?case
    by simp
next
  case (RRESIDUE cs rep)
  then show ?case by simp
qed

definition partial_derivative_frontier_universe :: "rrexp \<Rightarrow> rrexp set" where
  "partial_derivative_frontier_universe r =
    insert RZERO
      (insert RONE
        (rsubterms r \<union>
         rlinear_continuations r \<union>
         (\<lambda>(p, k). RSEQ p k) ` (rsubterms r \<times> rlinear_continuations r)))"

lemma finite_partial_derivative_frontier_universe [simp]:
  "finite (partial_derivative_frontier_universe r)"
  by (simp add: partial_derivative_frontier_universe_def)

lemma partial_derivative_frontier_universe_zero [simp]:
  "RZERO \<in> partial_derivative_frontier_universe r"
  by (simp add: partial_derivative_frontier_universe_def)

lemma partial_derivative_frontier_universe_one [simp]:
  "RONE \<in> partial_derivative_frontier_universe r"
  by (simp add: partial_derivative_frontier_universe_def)

lemma partial_derivative_frontier_universe_subterm:
  assumes "p \<in> rsubterms r"
  shows "p \<in> partial_derivative_frontier_universe r"
  using assms by (auto simp add: partial_derivative_frontier_universe_def)

lemma partial_derivative_frontier_universe_continuation:
  assumes "k \<in> rlinear_continuations r"
  shows "k \<in> partial_derivative_frontier_universe r"
  using assms by (auto simp add: partial_derivative_frontier_universe_def)

lemma partial_derivative_frontier_universe_seq:
  assumes "p \<in> rsubterms r" "k \<in> rlinear_continuations r"
  shows "RSEQ p k \<in> partial_derivative_frontier_universe r"
  using assms by (auto simp add: partial_derivative_frontier_universe_def)

lemma quadratic_padding_bound:
  fixes n :: nat
  shows "2 + n + n + n * n \<le> (n + 2) ^ 2"
proof -
  have "(n + 2) ^ 2 = n * n + 4 * n + 4"
    by (simp add: algebra_simps power2_eq_square)
  moreover have "2 + n + n \<le> 4 * n + 4"
    by simp
  ultimately show ?thesis
    by simp
qed

lemma partial_derivative_frontier_universe_card_quadratic:
  "card (partial_derivative_frontier_universe r) \<le> (rsize r + 2) ^ 2"
proof -
  let ?A = "rsubterms r"
  let ?K = "rlinear_continuations r"
  let ?P = "(\<lambda>(p, k). RSEQ p k) ` (?A \<times> ?K)"
  have A: "card ?A \<le> rsize r"
    by (rule card_rsubterms_le_rsize)
  have K: "card ?K \<le> rsize r"
    by (rule card_rlinear_continuations_le_rsize)
  have P: "card ?P \<le> card ?A * card ?K"
  proof -
    have "card ?P \<le> card (?A \<times> ?K)"
      by (rule card_image_le) simp
    then show ?thesis
      by simp
  qed
  have P_size: "card ?P \<le> rsize r * rsize r"
  proof -
    have "card ?P \<le> card ?A * rsize r"
    proof -
      have "card ?A * card ?K \<le> card ?A * rsize r"
        using K by (simp add: mult_left_mono)
      then show ?thesis
        using P by linarith
    qed
    also have "... \<le> rsize r * rsize r"
      using A by (simp add: mult_right_mono)
    finally show ?thesis .
  qed
  have "card (partial_derivative_frontier_universe r) \<le>
    2 + card ?A + card ?K + card ?P"
  proof -
    have U: "partial_derivative_frontier_universe r =
      insert RZERO (insert RONE (?A \<union> ?K \<union> ?P))"
      unfolding partial_derivative_frontier_universe_def by simp
    have "card (insert RZERO (insert RONE (?A \<union> ?K \<union> ?P))) \<le>
      2 + card (?A \<union> ?K) + card ?P"
      by (rule card_insert2_Un_le) simp_all
    also have "... \<le> 2 + card ?A + card ?K + card ?P"
      using card_Un_le[of ?A ?K] by simp
    finally show ?thesis
      using U by simp
  qed
  also have "... \<le> 2 + rsize r + rsize r + rsize r * rsize r"
    using A K P_size by linarith
  also have "... \<le> (rsize r + 2) ^ 2"
    by (rule quadratic_padding_bound)
  finally show ?thesis .
qed

lemma partial_derivative_frontier_universe_member_size_linear:
  assumes "q \<in> partial_derivative_frontier_universe r"
  shows "rsize q \<le> Suc (rsize r + rsize r)"
proof -
  let ?A = "rsubterms r"
  let ?K = "rlinear_continuations r"
  let ?P = "(\<lambda>(p, k). RSEQ p k) ` (?A \<times> ?K)"
  have q_cases: "q = RZERO \<or> q = RONE \<or> q \<in> ?A \<or> q \<in> ?K \<or> q \<in> ?P"
    using assms unfolding partial_derivative_frontier_universe_def by auto
  then show ?thesis
  proof
    assume "q = RZERO"
    then show ?thesis by simp
  next
    assume rest1: "q = RONE \<or> q \<in> ?A \<or> q \<in> ?K \<or> q \<in> ?P"
    then show ?thesis
    proof
      assume "q = RONE"
      then show ?thesis by simp
    next
      assume rest2: "q \<in> ?A \<or> q \<in> ?K \<or> q \<in> ?P"
      then show ?thesis
      proof
        assume "q \<in> ?A"
        then have "rsize q \<le> rsize r"
          using rsubterms_member_size_le_rsize by blast
        then show ?thesis by simp
      next
        assume rest3: "q \<in> ?K \<or> q \<in> ?P"
        then show ?thesis
        proof
          assume "q \<in> ?K"
          then have "rsize q \<le> rsize r"
            using rlinear_continuations_member_size_le_rsize by blast
          then show ?thesis by simp
        next
          assume "q \<in> ?P"
          then obtain p k where pk:
            "p \<in> ?A" "k \<in> ?K" "q = RSEQ p k"
            by auto
          have p_size: "rsize p \<le> rsize r"
            using pk rsubterms_member_size_le_rsize by blast
          have k_size: "rsize k \<le> rsize r"
            using pk rlinear_continuations_member_size_le_rsize by blast
          show ?thesis
            using pk p_size k_size by simp
        qed
      qed
    qed
  qed
qed

fun rfrontier :: "rrexp \<Rightarrow> rrexp set"
  and rfrontiers :: "rrexp list \<Rightarrow> rrexp set" where
  "rfrontier RZERO = {}"
| "rfrontier (RALTS rs) = rfrontiers rs"
| "rfrontier r = {r}"
| "rfrontiers [] = {}"
| "rfrontiers (r # rs) = rfrontier r \<union> rfrontiers rs"

lemma finite_rfrontier [simp]:
  "finite (rfrontier r)"
  and finite_rfrontiers [simp]:
  "finite (rfrontiers rs)"
  by (induct r and rs rule: rfrontier_rfrontiers.induct) auto

lemma card_rfrontier_le_rsize:
  "card (rfrontier r) \<le> rsize r"
  and card_rfrontiers_le_rsizes:
  "card (rfrontiers rs) \<le> rsizes rs"
  apply (induct r and rs rule: rfrontier_rfrontiers.induct)
      apply simp_all
  by (meson add_mono card_Un_le le_trans)

fun rnonseq :: "rrexp \<Rightarrow> bool" where
  "rnonseq (RSEQ r1 r2) = False"
| "rnonseq r = True"

lemma rfrontier_subset_rsubterms:
  "rfrontier r \<subseteq> rsubterms r"
  and rfrontiers_subset_rsubterms:
  "rfrontiers rs \<subseteq> (\<Union> (set (map rsubterms rs)))"
  by (induct r and rs rule: rfrontier_rfrontiers.induct) auto

lemma rsubterms_trans:
  assumes "q \<in> rsubterms r" "p \<in> rsubterms q"
  shows "p \<in> rsubterms r"
  using assms
  by (induct r arbitrary: q p) auto

lemma rsubterms_subterm_subset_frontier:
  assumes "q \<in> rsubterms r"
  shows "rsubterms q \<subseteq> partial_derivative_frontier_universe r"
proof
  fix p
  assume "p \<in> rsubterms q"
  then have "p \<in> rsubterms r"
    using rsubterms_trans[OF assms] by blast
  then show "p \<in> partial_derivative_frontier_universe r"
    by (rule partial_derivative_frontier_universe_subterm)
qed

lemma rfrontier_subterm_subset:
  assumes "q \<in> rsubterms r"
  shows "rfrontier q \<subseteq> partial_derivative_frontier_universe r"
proof
  fix x
  assume "x \<in> rfrontier q"
  then have "x \<in> rsubterms q"
    using rfrontier_subset_rsubterms by blast
  then have "x \<in> rsubterms r"
    using rsubterms_trans[OF assms] by blast
  then show "x \<in> partial_derivative_frontier_universe r"
    by (rule partial_derivative_frontier_universe_subterm)
qed

lemma rlinear_continuations_subterm_subset:
  assumes "q \<in> rsubterms r"
  shows "rlinear_continuations q \<subseteq> rlinear_continuations r"
  using assms
  by (induct r arbitrary: q) fastforce+

lemma partial_derivative_frontier_universe_subterm_mono:
  assumes "q \<in> rsubterms r"
  shows "partial_derivative_frontier_universe q \<subseteq> partial_derivative_frontier_universe r"
proof
  fix x
  assume x: "x \<in> partial_derivative_frontier_universe q"
  then consider
      "x = RZERO"
    | "x = RONE"
    | "x \<in> rsubterms q"
    | "x \<in> rlinear_continuations q"
    | p k where "p \<in> rsubterms q" "k \<in> rlinear_continuations q" "x = RSEQ p k"
    unfolding partial_derivative_frontier_universe_def by auto
  then show "x \<in> partial_derivative_frontier_universe r"
  proof cases
    case 1
    then show ?thesis by simp
  next
    case 2
    then show ?thesis by simp
  next
    case 3
    then have "x \<in> rsubterms r"
      using rsubterms_trans[OF assms] by blast
    then show ?thesis
      by (rule partial_derivative_frontier_universe_subterm)
  next
    case 4
    then have "x \<in> rlinear_continuations r"
      using rlinear_continuations_subterm_subset[OF assms] by blast
    then show ?thesis
      by (rule partial_derivative_frontier_universe_continuation)
  next
    case (5 p k)
    have "p \<in> rsubterms r"
      using rsubterms_trans[OF assms 5(1)] .
    moreover have "k \<in> rlinear_continuations r"
      using rlinear_continuations_subterm_subset[OF assms] 5 by blast
    ultimately show ?thesis
      using 5 by (auto intro: partial_derivative_frontier_universe_seq)
  qed
qed

lemma rsubterms_linear_continuation_subset:
  assumes "k \<in> rlinear_continuations r"
  shows "rsubterms k \<subseteq> partial_derivative_frontier_universe r"
  using assms
proof (induct r arbitrary: k)
  case RZERO
  then show ?case by simp
next
  case RONE
  then show ?case by simp
next
  case (RCHAR x)
  then show ?case by simp
next
  case (RALTS rs)
  then obtain q where q: "q \<in> set rs" "k \<in> rlinear_continuations q"
    by auto
  have "rsubterms k \<subseteq> partial_derivative_frontier_universe q"
    using RALTS.hyps[OF q(1)] q(2) by blast
  also have "... \<subseteq> partial_derivative_frontier_universe (RALTS rs)"
  proof -
    have "q \<in> rsubterms (RALTS rs)"
    proof -
      have "q \<in> (\<Union> (set (map rsubterms rs)))"
        using q(1) self_rsubterm by force
      then show ?thesis by simp
    qed
    then show ?thesis
      by (rule partial_derivative_frontier_universe_subterm_mono)
  qed
  finally show ?case .
next
  case (RSEQ r1 r2)
  then consider
      "k = r2"
    | "k \<in> rlinear_continuations r1"
    | "k \<in> rlinear_continuations r2"
    by auto
  then show ?case
  proof cases
    case 1
    have "r2 \<in> rsubterms (RSEQ r1 r2)"
      by simp
    then show ?thesis
      using 1 rsubterms_subterm_subset_frontier by blast
  next
    case 2
    have "rsubterms k \<subseteq> partial_derivative_frontier_universe r1"
      using RSEQ.hyps(1)[OF 2] .
    also have "... \<subseteq> partial_derivative_frontier_universe (RSEQ r1 r2)"
      by (intro partial_derivative_frontier_universe_subterm_mono) auto
    finally show ?thesis .
  next
    case 3
    have "rsubterms k \<subseteq> partial_derivative_frontier_universe r2"
      using RSEQ.hyps(2)[OF 3] .
    also have "... \<subseteq> partial_derivative_frontier_universe (RSEQ r1 r2)"
      by (intro partial_derivative_frontier_universe_subterm_mono) auto
    finally show ?thesis .
  qed
next
  case (RSTAR r)
  then consider "k = RSTAR r" | "k \<in> rlinear_continuations r"
    by auto
  then show ?case
  proof cases
    case 1
    have "RSTAR r \<in> rsubterms (RSTAR r)"
      by simp
    then show ?thesis
      using 1 rsubterms_subterm_subset_frontier by blast
  next
    case 2
    have "rsubterms k \<subseteq> partial_derivative_frontier_universe r"
      using RSTAR.hyps[OF 2] .
    also have "... \<subseteq> partial_derivative_frontier_universe (RSTAR r)"
      by (intro partial_derivative_frontier_universe_subterm_mono) auto
    finally show ?thesis .
  qed
next
  case (RNTIMES r n)
  then consider
      m where "m \<le> n" "k = RNTIMES r m"
    | "k \<in> rlinear_continuations r"
    by auto
  then show ?case
  proof cases
    case (1 m)
    show ?thesis
    proof
      fix x
      assume x: "x \<in> rsubterms k"
      then consider "x = RNTIMES r m" | "x \<in> rsubterms r"
        using 1 by auto
      then show "x \<in> partial_derivative_frontier_universe (RNTIMES r n)"
      proof cases
        case 1
        have "RNTIMES r m \<in> rlinear_continuations (RNTIMES r n)"
          using \<open>m \<le> n\<close> by auto
        then have "RNTIMES r m \<in>
          partial_derivative_frontier_universe (RNTIMES r n)"
          by (rule partial_derivative_frontier_universe_continuation)
        then show ?thesis
          using 1 by simp
      next
        case 2
        then have "x \<in> rsubterms (RNTIMES r n)"
          by simp
        then show ?thesis
          by (rule partial_derivative_frontier_universe_subterm)
      qed
    qed
  next
    case 2
    have "rsubterms k \<subseteq> partial_derivative_frontier_universe r"
      using RNTIMES.hyps[OF 2] .
    also have "... \<subseteq> partial_derivative_frontier_universe (RNTIMES r n)"
      by (intro partial_derivative_frontier_universe_subterm_mono) auto
    finally show ?thesis .
  qed
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  then consider
      "k \<in> rlinear_continuations r1"
    | "k \<in> rlinear_continuations r2"
    | "k \<in> rlinear_continuations r3"
    | "k \<in> rlinear_continuations r4"
    by auto
  then show ?case
  proof cases
    case 1
    have "rsubterms k \<subseteq> partial_derivative_frontier_universe r1"
      using RBACKREF4.hyps(1)[OF 1] .
    also have "... \<subseteq> partial_derivative_frontier_universe
      (RBACKREF4 r1 r2 r3 r4 cs)"
      by (intro partial_derivative_frontier_universe_subterm_mono) auto
    finally show ?thesis .
  next
    case 2
    have "rsubterms k \<subseteq> partial_derivative_frontier_universe r2"
      using RBACKREF4.hyps(2)[OF 2] .
    also have "... \<subseteq> partial_derivative_frontier_universe
      (RBACKREF4 r1 r2 r3 r4 cs)"
      by (intro partial_derivative_frontier_universe_subterm_mono) auto
    finally show ?thesis .
  next
    case 3
    have "rsubterms k \<subseteq> partial_derivative_frontier_universe r3"
      using RBACKREF4.hyps(3)[OF 3] .
    also have "... \<subseteq> partial_derivative_frontier_universe
      (RBACKREF4 r1 r2 r3 r4 cs)"
      by (intro partial_derivative_frontier_universe_subterm_mono) auto
    finally show ?thesis .
  next
    case 4
    have "rsubterms k \<subseteq> partial_derivative_frontier_universe r4"
      using RBACKREF4.hyps(4)[OF 4] .
    also have "... \<subseteq> partial_derivative_frontier_universe
      (RBACKREF4 r1 r2 r3 r4 cs)"
      by (intro partial_derivative_frontier_universe_subterm_mono) auto
    finally show ?thesis .
  qed
next
  case (RHALF r cs rep)
  have "rsubterms k \<subseteq> partial_derivative_frontier_universe r"
    using RHALF by auto
  also have "... \<subseteq> partial_derivative_frontier_universe (RHALF r cs rep)"
    by (intro partial_derivative_frontier_universe_subterm_mono) auto
  finally show ?case .
next
  case (RRESIDUE cs rep)
  then show ?case by simp
qed

lemma rfrontier_linear_continuation_subset:
  assumes "k \<in> rlinear_continuations r"
  shows "rfrontier k \<subseteq> partial_derivative_frontier_universe r"
  using assms
proof (induct r arbitrary: k)
  case RZERO
  then show ?case by simp
next
  case RONE
  then show ?case by simp
next
  case (RCHAR x)
  then show ?case by simp
next
  case (RALTS rs)
  then obtain q where q: "q \<in> set rs" "k \<in> rlinear_continuations q"
    by auto
  have "rfrontier k \<subseteq> partial_derivative_frontier_universe q"
    using RALTS q by auto
  also have "... \<subseteq> partial_derivative_frontier_universe (RALTS rs)"
  proof -
    have "q \<in> rsubterms (RALTS rs)"
    proof -
      have "q \<in> (\<Union> (set (map rsubterms rs)))"
        using q(1) by force
      then show ?thesis
        by simp
    qed
    then show ?thesis
      by (rule partial_derivative_frontier_universe_subterm_mono)
  qed
  finally show ?case .
next
  case (RSEQ r1 r2)
  then consider
      "k = r2"
    | "k \<in> rlinear_continuations r1"
    | "k \<in> rlinear_continuations r2"
    by auto
  then show ?case
  proof cases
    case 1
    have "r2 \<in> rsubterms (RSEQ r1 r2)"
      by simp
    then show ?thesis
      using 1 rfrontier_subterm_subset by blast
  next
    case 2
    have "rfrontier k \<subseteq> partial_derivative_frontier_universe r1"
      using RSEQ 2 by auto
    also have "... \<subseteq> partial_derivative_frontier_universe (RSEQ r1 r2)"
      by (intro partial_derivative_frontier_universe_subterm_mono) auto
    finally show ?thesis .
  next
    case 3
    have "rfrontier k \<subseteq> partial_derivative_frontier_universe r2"
      using RSEQ 3 by auto
    also have "... \<subseteq> partial_derivative_frontier_universe (RSEQ r1 r2)"
      by (intro partial_derivative_frontier_universe_subterm_mono) auto
    finally show ?thesis .
  qed
next
  case (RSTAR r)
  then consider "k = RSTAR r" | "k \<in> rlinear_continuations r"
    by auto
  then show ?case
  proof cases
    case 1
    have "RSTAR r \<in> rsubterms (RSTAR r)"
      by simp
    then show ?thesis
      using 1 rfrontier_subterm_subset by blast
  next
    case 2
    have "rfrontier k \<subseteq> partial_derivative_frontier_universe r"
      using RSTAR 2 by auto
    also have "... \<subseteq> partial_derivative_frontier_universe (RSTAR r)"
      by (intro partial_derivative_frontier_universe_subterm_mono) auto
    finally show ?thesis .
  qed
next
  case (RNTIMES r n)
  then consider
      m where "m \<le> n" "k = RNTIMES r m"
    | "k \<in> rlinear_continuations r"
    by auto
  then show ?case
  proof cases
    case 1
    then show ?thesis
      using partial_derivative_frontier_universe_continuation[of k "RNTIMES r n"] RNTIMES.prems
      by auto
  next
    case 2
    have "rfrontier k \<subseteq> partial_derivative_frontier_universe r"
      using RNTIMES 2 by auto
    also have "... \<subseteq> partial_derivative_frontier_universe (RNTIMES r n)"
      by (intro partial_derivative_frontier_universe_subterm_mono) auto
    finally show ?thesis .
  qed
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  then consider
      "k \<in> rlinear_continuations r1"
    | "k \<in> rlinear_continuations r2"
    | "k \<in> rlinear_continuations r3"
    | "k \<in> rlinear_continuations r4"
    by auto
  then show ?case
  proof cases
    case 1
    have "rfrontier k \<subseteq> partial_derivative_frontier_universe r1"
      using RBACKREF4 1 by auto
    also have "... \<subseteq> partial_derivative_frontier_universe (RBACKREF4 r1 r2 r3 r4 cs)"
      by (intro partial_derivative_frontier_universe_subterm_mono) auto
    finally show ?thesis .
  next
    case 2
    have "rfrontier k \<subseteq> partial_derivative_frontier_universe r2"
      using RBACKREF4 2 by auto
    also have "... \<subseteq> partial_derivative_frontier_universe (RBACKREF4 r1 r2 r3 r4 cs)"
      by (intro partial_derivative_frontier_universe_subterm_mono) auto
    finally show ?thesis .
  next
    case 3
    have "rfrontier k \<subseteq> partial_derivative_frontier_universe r3"
      using RBACKREF4 3 by auto
    also have "... \<subseteq> partial_derivative_frontier_universe (RBACKREF4 r1 r2 r3 r4 cs)"
      by (intro partial_derivative_frontier_universe_subterm_mono) auto
    finally show ?thesis .
  next
    case 4
    have "rfrontier k \<subseteq> partial_derivative_frontier_universe r4"
      using RBACKREF4 4 by auto
    also have "... \<subseteq> partial_derivative_frontier_universe (RBACKREF4 r1 r2 r3 r4 cs)"
      by (intro partial_derivative_frontier_universe_subterm_mono) auto
    finally show ?thesis .
  qed
next
  case (RHALF r cs rep)
  have "rfrontier k \<subseteq> partial_derivative_frontier_universe r"
    using RHALF by auto
  also have "... \<subseteq> partial_derivative_frontier_universe (RHALF r cs rep)"
    by (intro partial_derivative_frontier_universe_subterm_mono) auto
  finally show ?case .
next
  case (RRESIDUE cs rep)
  then show ?case by simp
qed

lemma rfrontier_frontier_universe_member_subset:
  assumes "q \<in> partial_derivative_frontier_universe r"
  shows "rfrontier q \<subseteq> partial_derivative_frontier_universe r"
proof
  fix x
  assume x: "x \<in> rfrontier q"
  let ?A = "rsubterms r"
  let ?K = "rlinear_continuations r"
  let ?P = "(\<lambda>(p, k). RSEQ p k) ` (?A \<times> ?K)"
  have q_cases: "q = RZERO \<or> q = RONE \<or> q \<in> ?A \<or> q \<in> ?K \<or> q \<in> ?P"
    using assms unfolding partial_derivative_frontier_universe_def by auto
  then show "x \<in> partial_derivative_frontier_universe r"
  proof
    assume "q = RZERO"
    then show ?thesis
      using x by simp
  next
    assume rest1: "q = RONE \<or> q \<in> ?A \<or> q \<in> ?K \<or> q \<in> ?P"
    then show ?thesis
    proof
      assume "q = RONE"
      then show ?thesis
        using x by simp
    next
      assume rest2: "q \<in> ?A \<or> q \<in> ?K \<or> q \<in> ?P"
      then show ?thesis
      proof
        assume "q \<in> ?A"
        then show ?thesis
          using x rfrontier_subterm_subset by blast
      next
        assume rest3: "q \<in> ?K \<or> q \<in> ?P"
        then show ?thesis
        proof
          assume "q \<in> ?K"
          then show ?thesis
            using x rfrontier_linear_continuation_subset by blast
        next
          assume "q \<in> ?P"
          then have "q \<in> partial_derivative_frontier_universe r"
            unfolding partial_derivative_frontier_universe_def by auto
          moreover have "rfrontier q = {q}"
            using \<open>q \<in> ?P\<close> by auto
          ultimately show ?thesis
            using x by auto
        qed
      qed
    qed
  qed
qed

lemma rsubterms_frontier_universe_member_subset:
  assumes "q \<in> partial_derivative_frontier_universe r"
  shows "rsubterms q \<subseteq> partial_derivative_frontier_universe r"
proof
  fix x
  assume x: "x \<in> rsubterms q"
  let ?A = "rsubterms r"
  let ?K = "rlinear_continuations r"
  let ?P = "(\<lambda>(p, k). RSEQ p k) ` (?A \<times> ?K)"
  have q_cases: "q = RZERO \<or> q = RONE \<or> q \<in> ?A \<or> q \<in> ?K \<or> q \<in> ?P"
    using assms unfolding partial_derivative_frontier_universe_def by auto
  then show "x \<in> partial_derivative_frontier_universe r"
  proof
    assume "q = RZERO"
    then show ?thesis
      using x by simp
  next
    assume rest1: "q = RONE \<or> q \<in> ?A \<or> q \<in> ?K \<or> q \<in> ?P"
    then show ?thesis
    proof
      assume "q = RONE"
      then show ?thesis
        using x by simp
    next
      assume rest2: "q \<in> ?A \<or> q \<in> ?K \<or> q \<in> ?P"
      then show ?thesis
      proof
        assume "q \<in> ?A"
        then show ?thesis
          using x rsubterms_subterm_subset_frontier by blast
      next
        assume rest3: "q \<in> ?K \<or> q \<in> ?P"
        then show ?thesis
        proof
          assume "q \<in> ?K"
          then show ?thesis
            using x rsubterms_linear_continuation_subset by blast
        next
          assume "q \<in> ?P"
          then obtain p k where pk:
              "p \<in> ?A" "k \<in> ?K" "q = RSEQ p k"
            by auto
          then consider
              "x = RSEQ p k"
            | "x \<in> rsubterms p"
            | "x \<in> rsubterms k"
            using x by auto
          then show ?thesis
          proof cases
            case 1
            have "RSEQ p k \<in> partial_derivative_frontier_universe r"
              by (rule partial_derivative_frontier_universe_seq)
                (use pk in auto)
            then show ?thesis
              using 1 by simp
          next
            case 2
            then show ?thesis
              using pk rsubterms_subterm_subset_frontier by blast
          next
            case 3
            then show ?thesis
              using pk rsubterms_linear_continuation_subset by blast
          qed
        qed
      qed
    qed
  qed
qed

lemma rfrontier_rsimp4_SEQ_atom_nonseq_subset:
  assumes p: "p \<in> rsubterms r"
      and k: "k \<in> rlinear_continuations r"
      and k_frontier: "rfrontier k \<subseteq> partial_derivative_frontier_universe r"
      and nonseq: "rnonseq p"
  shows "rfrontier (rsimp4_SEQ_atom p k) \<subseteq> partial_derivative_frontier_universe r"
  using p k k_frontier nonseq
proof (cases p)
  case RZERO
  then show ?thesis by simp
next
  case RONE
  then show ?thesis
    using k_frontier by auto
next
  case (RCHAR x)
  then show ?thesis
    using p k by (cases k) (auto simp add: partial_derivative_frontier_universe_def)
next
  case (RSEQ x41 x42)
  then show ?thesis
    using nonseq by simp
next
  case (RALTS x5)
  note p_RALTS = RALTS
  then show ?thesis
  proof (cases k)
    case RONE
    have "rfrontier p \<subseteq> partial_derivative_frontier_universe r"
      by (rule rfrontier_subterm_subset[OF p])
    then show ?thesis
      using p_RALTS RONE by simp
  next
    case RZERO
    then show ?thesis
      using p_RALTS by simp
  next
    case (RCHAR x)
    then show ?thesis
      using p k p_RALTS by (auto simp add: partial_derivative_frontier_universe_def)
  next
    case (RSEQ x1 x2)
    then show ?thesis
      using p k p_RALTS by (auto simp add: partial_derivative_frontier_universe_def)
  next
    case (RALTS xs)
    then show ?thesis
      using p k p_RALTS by (auto simp add: partial_derivative_frontier_universe_def)
  next
    case (RSTAR x)
    then show ?thesis
      using p k p_RALTS by (auto simp add: partial_derivative_frontier_universe_def)
  next
    case (RNTIMES x n)
    then show ?thesis
      using p k p_RALTS by (auto simp add: partial_derivative_frontier_universe_def)
  next
    case (RBACKREF4 x1 x2 x3 x4 xs)
    then show ?thesis
      using p k p_RALTS by (auto simp add: partial_derivative_frontier_universe_def)
  next
    case (RHALF x xs rep)
    then show ?thesis
      using p k p_RALTS by (auto simp add: partial_derivative_frontier_universe_def)
  next
    case (RRESIDUE xs rep)
    then show ?thesis
      using p k p_RALTS by (auto simp add: partial_derivative_frontier_universe_def)
  qed
next
  case (RSTAR x6)
  then show ?thesis
    using p k by (cases k) (auto simp add: partial_derivative_frontier_universe_def)
next
  case (RNTIMES x71 x72)
  then show ?thesis
    using p k by (cases k) (auto simp add: partial_derivative_frontier_universe_def)
next
  case (RBACKREF4 x81 x82 x83 x84 x85)
  then show ?thesis
    using p k by (cases k) (auto simp add: partial_derivative_frontier_universe_def)
next
  case (RHALF x91 x92 x93)
  then show ?thesis
    using p k by (cases k) (auto simp add: partial_derivative_frontier_universe_def)
next
  case (RRESIDUE x101 x102)
  then show ?thesis
    using p k by (cases k) (auto simp add: partial_derivative_frontier_universe_def)
qed

lemma rfrontier_rsimp4_SEQ_atom_nonseq_subset':
  assumes p: "p \<in> rsubterms r"
      and k: "k \<in> rlinear_continuations r"
      and nonseq: "rnonseq p"
  shows "rfrontier (rsimp4_SEQ_atom p k) \<subseteq> partial_derivative_frontier_universe r"
  by (rule rfrontier_rsimp4_SEQ_atom_nonseq_subset)
    (use p k nonseq rfrontier_linear_continuation_subset in auto)

lemma rfrontiers_append [simp]:
  "rfrontiers (rs1 @ rs2) = rfrontiers rs1 \<union> rfrontiers rs2"
  by (induct rs1) auto

lemma rfrontiers_member_iff:
  "q \<in> rfrontiers rs \<longleftrightarrow> (\<exists>r \<in> set rs. q \<in> rfrontier r)"
  by (induct rs) auto

lemma rfrontiers_rdistinct_empty [simp]:
  "rfrontiers (rdistinct rs {}) = rfrontiers rs"
  by (auto simp add: rfrontiers_member_iff rdistinct_set_equality)

lemma rfrontiers_rflts [simp]:
  "rfrontiers (rflts rs) = rfrontiers rs"
  by (induct rs rule: rflts.induct) auto

lemma rfrontier_rsimp_ALTs_eq [simp]:
  "rfrontier (rsimp_ALTs rs) = rfrontiers rs"
proof (cases rs)
  case Nil
  then show ?thesis by simp
next
  case (Cons r rs')
  note rs_shape = Cons
  then show ?thesis
  proof (cases rs')
    case Nil
    then show ?thesis
      using rs_shape by simp
  next
    case (Cons s ss)
    then have "rs = r # s # ss"
      using rs_shape by simp
    then show ?thesis
      by simp
  qed
qed

lemma rfrontier_normalize_eq [simp]:
  "rfrontier (rsimp_ALTs (rdistinct (rflts rs) {})) = rfrontiers rs"
  by simp

lemma rfrontiers_subsetI:
  assumes "\<And>r. r \<in> set rs \<Longrightarrow> rfrontier r \<subseteq> U"
  shows "rfrontiers rs \<subseteq> U"
  using assms by (induct rs) auto

lemma rfrontier_rsimp_ALTs_subset:
  assumes "rfrontiers rs \<subseteq> U"
  shows "rfrontier (rsimp_ALTs rs) \<subseteq> U"
proof (cases rs)
  case Nil
  then show ?thesis by simp
next
  case (Cons a rest)
  then show ?thesis
  proof (cases rest)
    case Nil
    then show ?thesis
      using Cons assms by simp
  next
    case (Cons b bs)
    have rs_shape: "rs = a # b # bs"
      using Cons `rs = a # rest` by simp
    then have "rfrontier (rsimp_ALTs rs) = rfrontiers rs"
      by simp
    then show ?thesis
      using assms by simp
  qed
qed

lemma rfrontiers_rflts_subset:
  assumes "rfrontiers rs \<subseteq> U"
  shows "rfrontiers (rflts rs) \<subseteq> U"
  using assms
  by (induct rs rule: rflts.induct) auto

lemma rfrontiers_rdistinct_subset:
  assumes "rfrontiers rs \<subseteq> U"
  shows "rfrontiers (rdistinct rs acc) \<subseteq> U"
  using assms
  by (induct rs arbitrary: acc) auto

lemma rfrontier_normalize_subset:
  assumes "\<And>r. r \<in> set rs \<Longrightarrow> rfrontier r \<subseteq> U"
  shows "rfrontier (rsimp_ALTs (rdistinct (rflts rs) {})) \<subseteq> U"
proof -
  have "rfrontiers rs \<subseteq> U"
    by (rule rfrontiers_subsetI) (use assms in auto)
  then have "rfrontiers (rflts rs) \<subseteq> U"
    by (rule rfrontiers_rflts_subset)
  then have "rfrontiers (rdistinct (rflts rs) {}) \<subseteq> U"
    by (rule rfrontiers_rdistinct_subset)
  then show ?thesis
    by (rule rfrontier_rsimp_ALTs_subset)
qed

lemma rfrontiers_frontier_universe_members_subset:
  assumes "set rs \<subseteq> partial_derivative_frontier_universe r"
  shows "rfrontiers rs \<subseteq> partial_derivative_frontier_universe r"
  by (rule rfrontiers_subsetI)
    (use assms rfrontier_frontier_universe_member_subset in blast)

lemma rfrontier_rpd_der_norm_subsetI:
  assumes "rfrontiers (rpder_norm_list c r) \<subseteq> U"
  shows "rfrontier (rpd_der_norm c r) \<subseteq> U"
  unfolding rpd_der_norm_def
  by (rule rfrontier_normalize_subset)
    (use assms rfrontiers_member_iff in blast)

lemma rfrontier_rsimp4_SEQ_RONE_subset:
  "rfrontier (rsimp4_SEQ RONE k) \<subseteq> rfrontier k"
proof -
  have "rfrontier
      (rsimp_ALTs (rdistinct (rflts (rsimp4_seq_row RONE k)) {})) \<subseteq>
    rfrontier k"
    by (rule rfrontier_normalize_subset) auto
  then show ?thesis
    by (simp add: rsimp4_SEQ_def)
qed

lemma card_rfrontier_rsimp4_SEQ_RONE_le:
  "card (rfrontier (rsimp4_SEQ RONE k)) \<le> card (rfrontier k)"
  by (rule card_mono) (simp_all add: rfrontier_rsimp4_SEQ_RONE_subset)

lemma card_rfrontier_rsimp4_SEQ_atom_le:
  "card (rfrontier (rsimp4_SEQ_atom r k)) \<le>
    rsize r + card (rfrontier k)"
proof (induct r arbitrary: k)
  case RZERO
  then show ?case by simp
next
  case RONE
  then show ?case by simp
next
  case (RCHAR x)
  then show ?case
    by (cases k) simp_all
next
  case (RSEQ r1 r2)
  have "card (rfrontier (rsimp4_SEQ_atom (RSEQ r1 r2) k)) =
    card (rfrontier (rsimp4_SEQ_atom r1 (rsimp4_SEQ_atom r2 k)))"
    by simp
  also have "... \<le> rsize r1 +
    card (rfrontier (rsimp4_SEQ_atom r2 k))"
    by (rule RSEQ.hyps(1))
  also have "... \<le> rsize r1 + (rsize r2 + card (rfrontier k))"
    using RSEQ.hyps(2)[of k] by linarith
  also have "... \<le> rsize (RSEQ r1 r2) + card (rfrontier k)"
    by simp
  finally show ?case .
next
  case (RALTS rs)
  then show ?case
  proof (cases k)
    case RONE
    then show ?thesis
      using card_rfrontiers_le_rsizes[of rs] by simp
  qed simp_all
next
  case (RSTAR r)
  then show ?case
    by (cases k) simp_all
next
  case (RNTIMES r n)
  then show ?case
    by (cases k) simp_all
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  then show ?case
    by (cases k) simp_all
next
  case (RHALF r cs rep)
  then show ?case
    by (cases k) simp_all
next
  case (RRESIDUE cs rep)
  then show ?case
    by (cases k) simp_all
qed

lemma rsimp4_SEQ_atom_assoc:
  "rsimp4_SEQ_atom (rsimp4_SEQ_atom r1 r2) k =
    rsimp4_SEQ_atom r1 (rsimp4_SEQ_atom r2 k)"
proof (induct r1 arbitrary: r2 k)
  case RZERO
  then show ?case by simp
next
  case RONE
  then show ?case by simp
next
  case (RCHAR c)
  then show ?case
    by (cases r2) simp_all
next
  case (RSEQ r1 r1')
  have "rsimp4_SEQ_atom (rsimp4_SEQ_atom (RSEQ r1 r1') r2) k =
    rsimp4_SEQ_atom (rsimp4_SEQ_atom r1 (rsimp4_SEQ_atom r1' r2)) k"
    by simp
  also have "... =
    rsimp4_SEQ_atom r1
      (rsimp4_SEQ_atom (rsimp4_SEQ_atom r1' r2) k)"
    by (rule RSEQ.hyps(1))
  also have "... =
    rsimp4_SEQ_atom r1
      (rsimp4_SEQ_atom r1' (rsimp4_SEQ_atom r2 k))"
    by (simp add: RSEQ.hyps(2))
  finally show ?case
    by simp
next
  case (RALTS rs)
  then show ?case
    by (cases r2) simp_all
next
  case (RSTAR r)
  then show ?case
    by (cases r2) simp_all
next
  case (RNTIMES r n)
  then show ?case
    by (cases r2) simp_all
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  then show ?case
    by (cases r2) simp_all
next
  case (RHALF r cs rep)
  then show ?case
    by (cases r2) simp_all
next
  case (RRESIDUE cs rep)
  then show ?case
    by (cases r2) simp_all
qed

lemma card_rfrontier_normalize_le_rfrontiers:
  "card (rfrontier (rsimp_ALTs (rdistinct (rflts rs) {}))) \<le>
    card (rfrontiers rs)"
proof -
  have sub: "rfrontier (rsimp_ALTs (rdistinct (rflts rs) {})) \<subseteq>
    rfrontiers rs"
    by (rule rfrontier_normalize_subset)
      (induct rs, auto)
  show ?thesis
    by (rule card_mono) (simp_all add: sub)
qed

lemma component_frontier_le_product:
  fixes c :: nat
  shows "rsize r + c \<le> rsize r * Suc c"
proof -
  have "c \<le> rsize r * c"
    using size_geq1[of r] by (simp add: mult.commute)
  then show ?thesis
    by (simp add: algebra_simps)
qed

lemma card_rfrontiers_concat_rsimp4_seq_rows_le:
  "card (rfrontiers (concat (map (\<lambda>x. rsimp4_seq_row x k) rs))) \<le>
    rsizes rs * Suc (card (rfrontier k))"
proof (induct rs)
  case Nil
  then show ?case by simp
next
  case (Cons r rs)
  let ?c = "card (rfrontier k)"
  have "card (rfrontiers (concat (map (\<lambda>x. rsimp4_seq_row x k) (r # rs)))) \<le>
    card (rfrontier (rsimp4_SEQ_atom r k)) +
    card (rfrontiers (concat (map (\<lambda>x. rsimp4_seq_row x k) rs)))"
    by (simp add: card_Un_le)
  also have "... \<le> (rsize r + ?c) + rsizes rs * Suc ?c"
    using Cons.hyps card_rfrontier_rsimp4_SEQ_atom_le[of r k] by linarith
  also have "... \<le> rsize r * Suc ?c + rsizes rs * Suc ?c"
    using component_frontier_le_product[of r ?c] by linarith
  also have "... = rsizes (r # rs) * Suc ?c"
    by (simp add: algebra_simps)
  finally show ?case .
qed

lemma card_rfrontier_rsimp4_SEQ_single_le:
  "card (rfrontier
      (rsimp_ALTs (rdistinct (rflts (rsimp4_seq_row r k)) {}))) \<le>
    rsize r * Suc (card (rfrontier k))"
proof -
  have "card (rfrontier
      (rsimp_ALTs (rdistinct (rflts (rsimp4_seq_row r k)) {}))) \<le>
    card (rfrontier (rsimp4_SEQ_atom r k))"
    using card_rfrontier_normalize_le_rfrontiers[of "rsimp4_seq_row r k"]
    by simp
  also have "... \<le> rsize r + card (rfrontier k)"
    by (rule card_rfrontier_rsimp4_SEQ_atom_le)
  also have "... \<le> rsize r * Suc (card (rfrontier k))"
    by (rule component_frontier_le_product)
  finally show ?thesis .
qed

lemma card_rfrontier_rsimp4_SEQ_le:
  "card (rfrontier (rsimp4_SEQ r k)) \<le>
    rsize r * Suc (card (rfrontier k))"
proof (cases r)
  case RZERO
  then show ?thesis
    using card_rfrontier_rsimp4_SEQ_single_le[of RZERO k]
    by (simp add: rsimp4_SEQ_def)
next
  case RONE
  then show ?thesis
    using card_rfrontier_rsimp4_SEQ_single_le[of RONE k]
    by (simp add: rsimp4_SEQ_def)
next
  case (RCHAR x)
  then show ?thesis
    using card_rfrontier_rsimp4_SEQ_single_le[of "RCHAR x" k]
    by (simp add: rsimp4_SEQ_def)
next
  case (RSEQ r1 r2)
  then show ?thesis
    using card_rfrontier_rsimp4_SEQ_single_le[of "RSEQ r1 r2" k]
    by (simp add: rsimp4_SEQ_def)
next
  case (RALTS rs)
  have rows: "card
      (rfrontier
        (rsimp_ALTs
          (rdistinct (rflts (concat (map (\<lambda>x. rsimp4_seq_row x k) rs))) {}))) \<le>
    card (rfrontiers (concat (map (\<lambda>x. rsimp4_seq_row x k) rs)))"
    by (rule card_rfrontier_normalize_le_rfrontiers)
  have "card (rfrontier (rsimp4_SEQ (RALTS rs) k)) \<le>
    card (rfrontiers (concat (map (\<lambda>x. rsimp4_seq_row x k) rs)))"
    using rows by (simp add: rsimp4_SEQ_def)
  also have "... \<le> rsizes rs * Suc (card (rfrontier k))"
    by (rule card_rfrontiers_concat_rsimp4_seq_rows_le)
  also have "... \<le> rsize (RALTS rs) * Suc (card (rfrontier k))"
    by simp
  finally show ?thesis
    using RALTS by simp
next
  case (RSTAR r)
  then show ?thesis
    using card_rfrontier_rsimp4_SEQ_single_le[of "RSTAR r" k]
    by (simp add: rsimp4_SEQ_def)
next
  case (RNTIMES r n)
  then show ?thesis
    using card_rfrontier_rsimp4_SEQ_single_le[of "RNTIMES r n" k]
    by (simp add: rsimp4_SEQ_def)
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  then show ?thesis
    using card_rfrontier_rsimp4_SEQ_single_le[of "RBACKREF4 r1 r2 r3 r4 cs" k]
    by (simp add: rsimp4_SEQ_def)
next
  case (RHALF r cs rep)
  then show ?thesis
    using card_rfrontier_rsimp4_SEQ_single_le[of "RHALF r cs rep" k]
    by (simp add: rsimp4_SEQ_def)
next
  case (RRESIDUE cs rep)
  then show ?thesis
    using card_rfrontier_rsimp4_SEQ_single_le[of "RRESIDUE cs rep" k]
    by (simp add: rsimp4_SEQ_def)
qed

fun rseq_sources :: "rrexp \<Rightarrow> rrexp set" where
  "rseq_sources (RALTS rs) = set rs"
| "rseq_sources r = {r}"

lemma rfrontier_rsimp4_SEQ_single:
  assumes "rfrontier (rsimp4_SEQ_atom r1 r2) \<subseteq> U"
  shows "rfrontier (rsimp_ALTs (rdistinct (rflts (rsimp4_seq_row r1 r2)) {})) \<subseteq> U"
  by (rule rfrontier_normalize_subset) (use assms in auto)

lemma rfrontier_rsimp4_SEQ_subset:
  assumes "\<And>x. x \<in> rseq_sources r1 \<Longrightarrow> rfrontier (rsimp4_SEQ_atom x r2) \<subseteq> U"
  shows "rfrontier (rsimp4_SEQ r1 r2) \<subseteq> U"
proof (cases r1)
  case RZERO
  have "rfrontier (rsimp_ALTs (rdistinct (rflts (rsimp4_seq_row RZERO r2)) {})) \<subseteq> U"
    by (rule rfrontier_rsimp4_SEQ_single) (use assms in auto)
  then show ?thesis
    by (simp add: RZERO rsimp4_SEQ_def)
next
  case RONE
  have "rfrontier (rsimp_ALTs (rdistinct (rflts (rsimp4_seq_row RONE r2)) {})) \<subseteq> U"
    by (rule rfrontier_rsimp4_SEQ_single) (use assms RONE in auto)
  then show ?thesis
    by (simp add: RONE rsimp4_SEQ_def)
next
  case (RCHAR x)
  have "rfrontier (rsimp_ALTs (rdistinct (rflts (rsimp4_seq_row (RCHAR x) r2)) {})) \<subseteq> U"
    by (rule rfrontier_rsimp4_SEQ_single) (use assms RCHAR in auto)
  then show ?thesis
    by (simp add: RCHAR rsimp4_SEQ_def)
next
  case (RSEQ x41 x42)
  have "rfrontier (rsimp_ALTs (rdistinct (rflts (rsimp4_seq_row (RSEQ x41 x42) r2)) {})) \<subseteq> U"
    by (rule rfrontier_rsimp4_SEQ_single) (use assms RSEQ in auto)
  then show ?thesis
    by (simp add: RSEQ rsimp4_SEQ_def)
next
  case (RALTS rs)
  have "\<And>y. y \<in> set (concat (map (\<lambda>x. rsimp4_seq_row x r2) rs)) \<Longrightarrow>
    rfrontier y \<subseteq> U"
    using assms RALTS by auto
  then have "rfrontier
    (rsimp_ALTs (rdistinct (rflts (concat (map (\<lambda>x. rsimp4_seq_row x r2) rs))) {})) \<subseteq> U"
    by (rule rfrontier_normalize_subset)
  then show ?thesis
    by (simp add: RALTS rsimp4_SEQ_def)
next
  case (RSTAR x6)
  have "rfrontier (rsimp_ALTs (rdistinct (rflts (rsimp4_seq_row (RSTAR x6) r2)) {})) \<subseteq> U"
    by (rule rfrontier_rsimp4_SEQ_single) (use assms RSTAR in auto)
  then show ?thesis
    by (simp add: RSTAR rsimp4_SEQ_def)
next
  case (RNTIMES x71 x72)
  have "rfrontier (rsimp_ALTs (rdistinct (rflts (rsimp4_seq_row (RNTIMES x71 x72) r2)) {})) \<subseteq> U"
    by (rule rfrontier_rsimp4_SEQ_single) (use assms RNTIMES in auto)
  then show ?thesis
    by (simp add: RNTIMES rsimp4_SEQ_def)
next
  case (RBACKREF4 x81 x82 x83 x84 x85)
  have "rfrontier (rsimp_ALTs (rdistinct (rflts (rsimp4_seq_row (RBACKREF4 x81 x82 x83 x84 x85) r2)) {})) \<subseteq> U"
    by (rule rfrontier_rsimp4_SEQ_single) (use assms RBACKREF4 in auto)
  then show ?thesis
    by (simp add: RBACKREF4 rsimp4_SEQ_def)
next
  case (RHALF x91 x92 x93)
  have "rfrontier (rsimp_ALTs (rdistinct (rflts (rsimp4_seq_row (RHALF x91 x92 x93) r2)) {})) \<subseteq> U"
    by (rule rfrontier_rsimp4_SEQ_single) (use assms RHALF in auto)
  then show ?thesis
    by (simp add: RHALF rsimp4_SEQ_def)
next
  case (RRESIDUE x101 x102)
  have "rfrontier (rsimp_ALTs (rdistinct (rflts (rsimp4_seq_row (RRESIDUE x101 x102) r2)) {})) \<subseteq> U"
    by (rule rfrontier_rsimp4_SEQ_single) (use assms RRESIDUE in auto)
  then show ?thesis
    by (simp add: RRESIDUE rsimp4_SEQ_def)
qed

lemma rfrontier_rsimp4_SEQ_memberE:
  assumes "q \<in> rfrontier (rsimp4_SEQ r k)"
  obtains x where "x \<in> rseq_sources r" "q \<in> rfrontier (rsimp4_SEQ_atom x k)"
proof (cases r)
  case (RALTS rs)
  have "q \<in> rfrontiers (concat (map (\<lambda>x. rsimp4_seq_row x k) rs))"
    using assms RALTS by (simp add: rsimp4_SEQ_def)
  then obtain x where x: "x \<in> set rs" "q \<in> rfrontier (rsimp4_SEQ_atom x k)"
    by (induct rs) auto
  then show ?thesis
    using RALTS that by simp
next
  case RZERO
  have "q \<in> rfrontier (rsimp4_SEQ_atom RZERO k)"
    using assms RZERO by (simp add: rsimp4_SEQ_def)
  then show ?thesis
    using RZERO that by simp
next
  case RONE
  have "q \<in> rfrontier (rsimp4_SEQ_atom RONE k)"
    using assms RONE by (simp add: rsimp4_SEQ_def)
  then show ?thesis
    using RONE that by simp
next
  case (RCHAR c)
  have "q \<in> rfrontier (rsimp4_SEQ_atom (RCHAR c) k)"
    using assms RCHAR by (simp add: rsimp4_SEQ_def)
  then show ?thesis
    using RCHAR that by simp
next
  case (RSEQ r1 r2)
  have "q \<in> rfrontier (rsimp4_SEQ_atom (RSEQ r1 r2) k)"
    using assms RSEQ by (simp add: rsimp4_SEQ_def)
  then show ?thesis
    using RSEQ that by simp
next
  case (RSTAR r)
  have "q \<in> rfrontier (rsimp4_SEQ_atom (RSTAR r) k)"
    using assms RSTAR by (simp add: rsimp4_SEQ_def)
  then show ?thesis
    using RSTAR that by simp
next
  case (RNTIMES r n)
  have "q \<in> rfrontier (rsimp4_SEQ_atom (RNTIMES r n) k)"
    using assms RNTIMES by (simp add: rsimp4_SEQ_def)
  then show ?thesis
    using RNTIMES that by simp
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  have "q \<in> rfrontier (rsimp4_SEQ_atom (RBACKREF4 r1 r2 r3 r4 cs) k)"
    using assms RBACKREF4 by (simp add: rsimp4_SEQ_def)
  then show ?thesis
    using RBACKREF4 that by simp
next
  case (RHALF r cs rep)
  have "q \<in> rfrontier (rsimp4_SEQ_atom (RHALF r cs rep) k)"
    using assms RHALF by (simp add: rsimp4_SEQ_def)
  then show ?thesis
    using RHALF that by simp
next
  case (RRESIDUE cs rep)
  have "q \<in> rfrontier (rsimp4_SEQ_atom (RRESIDUE cs rep) k)"
    using assms RRESIDUE by (simp add: rsimp4_SEQ_def)
  then show ?thesis
    using RRESIDUE that by simp
qed

lemma rfrontier_rsimp4_SEQ_atom_source_subset:
  assumes "x \<in> rseq_sources r"
  shows "rfrontier (rsimp4_SEQ_atom x k) \<subseteq>
    rfrontier (rsimp4_SEQ r k)"
proof (cases r)
  case (RALTS rs)
  show ?thesis
  proof
    fix q
    assume q: "q \<in> rfrontier (rsimp4_SEQ_atom x k)"
    have "x \<in> set rs"
      using assms RALTS by simp
    then have "rsimp4_SEQ_atom x k \<in>
      set (concat (map (\<lambda>y. rsimp4_seq_row y k) rs))"
      by auto
    then have "q \<in> rfrontiers (concat (map (\<lambda>y. rsimp4_seq_row y k) rs))"
      using q rfrontiers_member_iff by blast
    then show "q \<in> rfrontier (rsimp4_SEQ r k)"
      using RALTS by (simp add: rsimp4_SEQ_def)
  qed
next
  case RZERO
  then show ?thesis
    using assms by (simp add: rsimp4_SEQ_def)
next
  case RONE
  then show ?thesis
    using assms by (simp add: rsimp4_SEQ_def)
next
  case (RCHAR c)
  then show ?thesis
    using assms by (simp add: rsimp4_SEQ_def)
next
  case (RSEQ r1 r2)
  then show ?thesis
    using assms by (simp add: rsimp4_SEQ_def)
next
  case (RSTAR r)
  then show ?thesis
    using assms by (simp add: rsimp4_SEQ_def)
next
  case (RNTIMES r n)
  then show ?thesis
    using assms by (simp add: rsimp4_SEQ_def)
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  then show ?thesis
    using assms by (simp add: rsimp4_SEQ_def)
next
  case (RHALF r cs rep)
  then show ?thesis
    using assms by (simp add: rsimp4_SEQ_def)
next
  case (RRESIDUE cs rep)
  then show ?thesis
    using assms by (simp add: rsimp4_SEQ_def)
qed

lemma rfrontier_rsimp4_SEQ_nonalt_eq_atom:
  assumes "nonalt r"
  shows "rfrontier (rsimp4_SEQ r k) =
    rfrontier (rsimp4_SEQ_atom r k)"
  using assms
  by (cases r) (simp_all add: rsimp4_SEQ_def)

lemma rfrontier_rsimp4_SEQ_rsimp_ALTs_nonalt_subset:
  assumes step: "\<And>x. x \<in> set rs \<Longrightarrow> rfrontier (rsimp4_SEQ x k) \<subseteq> U"
      and nonalt: "\<And>x. x \<in> set rs \<Longrightarrow> nonalt x"
  shows "rfrontier (rsimp4_SEQ (rsimp_ALTs rs) k) \<subseteq> U"
proof (cases rs)
  case Nil
  then show ?thesis
    by (simp add: rsimp4_SEQ_def)
next
  case (Cons r rs')
  note rs_shape = Cons
  then show ?thesis
  proof (cases rs')
    case Nil
    then show ?thesis
      using rs_shape step by simp
  next
    case (Cons r' rs'')
    then have rs_two: "rs = r # r' # rs''"
      using rs_shape by simp
    have "\<And>x. x \<in> rseq_sources (RALTS rs) \<Longrightarrow>
      rfrontier (rsimp4_SEQ_atom x k) \<subseteq> U"
    proof -
      fix x
      assume x: "x \<in> rseq_sources (RALTS rs)"
      then have x_set: "x \<in> set rs"
        by simp
      have "rfrontier (rsimp4_SEQ_atom x k) =
        rfrontier (rsimp4_SEQ x k)"
        using nonalt[OF x_set]
        by (simp add: rfrontier_rsimp4_SEQ_nonalt_eq_atom)
      also have "... \<subseteq> U"
        by (rule step[OF x_set])
      finally show "rfrontier (rsimp4_SEQ_atom x k) \<subseteq> U" .
    qed
    then have "rfrontier (rsimp4_SEQ (RALTS rs) k) \<subseteq> U"
      by (rule rfrontier_rsimp4_SEQ_subset)
    then show ?thesis
      using rs_two by simp
  qed
qed

lemma good_rsimp4_SEQ_atom:
  assumes "good r1 \<or> r1 = RZERO" "good r2 \<or> r2 = RZERO"
  shows "good (rsimp4_SEQ_atom r1 r2) \<or> rsimp4_SEQ_atom r1 r2 = RZERO"
  using assms
proof (induct r1 arbitrary: r2)
  case RZERO
  then show ?case by simp
next
  case RONE
  then show ?case by simp
next
  case (RCHAR c)
  then show ?case
    by (cases r2) simp_all
next
  case (RSEQ r1 r1')
  have good_left: "good r1"
    using RSEQ.prems by (cases r1; cases r1') auto
  have good_mid: "good r1'"
    using RSEQ.prems by (cases r1; cases r1') auto
  have inner: "good (rsimp4_SEQ_atom r1' r2) \<or>
      rsimp4_SEQ_atom r1' r2 = RZERO"
    by (rule RSEQ.hyps(2)) (use good_mid RSEQ.prems in auto)
  show ?case
    by (simp add: RSEQ.hyps(1)[OF disjI1[OF good_left] inner])
next
  case (RALTS rs)
  then show ?case
  proof (cases r2)
    case RZERO
    then show ?thesis by simp
  next
    case RONE
    then show ?thesis
      using RALTS.prems by simp
  next
    case (RCHAR c)
    then show ?thesis
      using RALTS.prems by simp
  next
    case (RSEQ a b)
    then show ?thesis
      using RALTS.prems by simp
  next
    case (RALTS xs)
    then show ?thesis
      using RALTS.prems by simp
  next
    case (RSTAR r)
    then show ?thesis
      using RALTS.prems by simp
  next
    case (RNTIMES r n)
    then show ?thesis
      using RALTS.prems by simp
  next
    case (RBACKREF4 a b c d cs)
    then show ?thesis
      using RALTS.prems by simp
  next
    case (RHALF r cs rep)
    then show ?thesis
      using RALTS.prems by simp
  next
    case (RRESIDUE cs rep)
    then show ?thesis
      using RALTS.prems by simp
  qed
next
  case (RSTAR r)
  then show ?case
    by (cases r2) simp_all
next
  case (RNTIMES r n)
  then show ?case
    by (cases r2) simp_all
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  then show ?case
    by (cases r2) simp_all
next
  case (RHALF r cs rep)
  then show ?case
    by (cases r2) simp_all
next
  case (RRESIDUE cs rep)
  then show ?case
    by (cases r2) simp_all
qed

lemma good_rsimp_ALTs_rdistinct_rflts:
  assumes "\<forall>r \<in> set rs. good r \<or> r = RZERO"
  shows "good (rsimp_ALTs (rdistinct (rflts rs) {})) \<or>
    rsimp_ALTs (rdistinct (rflts rs) {}) = RZERO"
proof -
  let ?xs = "rdistinct (rflts rs) {}"
  have good_nonalt: "\<forall>r \<in> set ?xs. good r \<and> nonalt r"
    using flts3_good_nonalt[OF assms] by (simp add: rdistinct_set_equality)
  have distinct: "distinct ?xs"
    by (rule rdistinct_does_the_job)
  show ?thesis
  proof (cases ?xs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons a ys)
    note xs_cons = Cons
    then show ?thesis
    proof (cases ys)
      case Nil
      then show ?thesis
        using xs_cons good_nonalt by simp
    next
      case (Cons b zs)
      then show ?thesis
        using xs_cons good_nonalt distinct by simp
    qed
  qed
qed

lemma good_rsimp4_SEQ_rows:
  assumes "\<forall>r \<in> set rs. good r \<or> r = RZERO"
      and "good k \<or> k = RZERO"
  shows "\<forall>r \<in> set (concat (map (\<lambda>x. rsimp4_seq_row x k) rs)).
    good r \<or> r = RZERO"
  using assms good_rsimp4_SEQ_atom by auto

lemma good_rsimp4_SEQ:
  assumes "good r1 \<or> r1 = RZERO" "good r2 \<or> r2 = RZERO"
  shows "good (rsimp4_SEQ r1 r2) \<or> rsimp4_SEQ r1 r2 = RZERO"
proof (cases r1)
  case RZERO
  have "\<forall>r \<in> set (rsimp4_seq_row r1 r2). good r \<or> r = RZERO"
    using good_rsimp4_SEQ_atom[OF assms] by simp
  then show ?thesis
    using RZERO good_rsimp_ALTs_rdistinct_rflts
    by (simp add: rsimp4_SEQ_def)
next
  case RONE
  have "\<forall>r \<in> set (rsimp4_seq_row r1 r2). good r \<or> r = RZERO"
    using good_rsimp4_SEQ_atom[OF assms] by simp
  then show ?thesis
    using RONE good_rsimp_ALTs_rdistinct_rflts
    by (simp add: rsimp4_SEQ_def)
next
  case (RCHAR x)
  have "\<forall>r \<in> set (rsimp4_seq_row r1 r2). good r \<or> r = RZERO"
    using good_rsimp4_SEQ_atom[OF assms] by simp
  then show ?thesis
    using RCHAR good_rsimp_ALTs_rdistinct_rflts
    by (simp add: rsimp4_SEQ_def)
next
  case (RSEQ x1 x2)
  have "\<forall>r \<in> set (rsimp4_seq_row r1 r2). good r \<or> r = RZERO"
    using good_rsimp4_SEQ_atom[OF assms] by simp
  then show ?thesis
    using RSEQ good_rsimp_ALTs_rdistinct_rflts
    by (simp add: rsimp4_SEQ_def)
next
  case (RALTS rs)
  have elems: "\<forall>r \<in> set rs. good r \<or> r = RZERO"
    using assms RALTS good_RALTS_elem by fastforce
  have rows: "\<forall>r \<in> set (concat (map (\<lambda>x. rsimp4_seq_row x r2) rs)).
      good r \<or> r = RZERO"
    by (rule good_rsimp4_SEQ_rows[OF elems assms(2)])
  show ?thesis
    using RALTS good_rsimp_ALTs_rdistinct_rflts[OF rows]
    by (simp add: rsimp4_SEQ_def)
next
  case (RSTAR x)
  have "\<forall>r \<in> set (rsimp4_seq_row r1 r2). good r \<or> r = RZERO"
    using good_rsimp4_SEQ_atom[OF assms] by simp
  then show ?thesis
    using RSTAR good_rsimp_ALTs_rdistinct_rflts
    by (simp add: rsimp4_SEQ_def)
next
  case (RNTIMES x1 x2)
  have "\<forall>r \<in> set (rsimp4_seq_row r1 r2). good r \<or> r = RZERO"
    using good_rsimp4_SEQ_atom[OF assms] by simp
  then show ?thesis
    using RNTIMES good_rsimp_ALTs_rdistinct_rflts
    by (simp add: rsimp4_SEQ_def)
next
  case (RBACKREF4 x1 x2 x3 x4 x5)
  have "\<forall>r \<in> set (rsimp4_seq_row r1 r2). good r \<or> r = RZERO"
    using good_rsimp4_SEQ_atom[OF assms] by simp
  then show ?thesis
    using RBACKREF4 good_rsimp_ALTs_rdistinct_rflts
    by (simp add: rsimp4_SEQ_def)
next
  case (RHALF x1 x2 x3)
  have "\<forall>r \<in> set (rsimp4_seq_row r1 r2). good r \<or> r = RZERO"
    using good_rsimp4_SEQ_atom[OF assms] by simp
  then show ?thesis
    using RHALF good_rsimp_ALTs_rdistinct_rflts
    by (simp add: rsimp4_SEQ_def)
next
  case (RRESIDUE x1 x2)
  have "\<forall>r \<in> set (rsimp4_seq_row r1 r2). good r \<or> r = RZERO"
    using good_rsimp4_SEQ_atom[OF assms] by simp
  then show ?thesis
    using RRESIDUE good_rsimp_ALTs_rdistinct_rflts
    by (simp add: rsimp4_SEQ_def)
qed

lemma good_rsimp4:
  shows "good (rsimp4 r) \<or> rsimp4 r = RZERO"
proof (induct r)
  case RZERO
  then show ?case by simp
next
  case RONE
  then show ?case by simp
next
  case (RCHAR x)
  then show ?case by simp
next
  case (RSEQ r1 r2)
  then show ?case
    using good_rsimp4_SEQ by simp
next
  case (RALTS rs)
  have elems: "\<forall>r \<in> set (map rsimp4 rs). good r \<or> r = RZERO"
    using RALTS by auto
  show ?case
    using good_rsimp_ALTs_rdistinct_rflts[OF elems] by simp
next
  case (RSTAR r)
  then show ?case by simp
next
  case (RNTIMES r n)
  then show ?case by simp
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  then show ?case by simp
next
  case (RHALF r cs rep)
  then show ?case by simp
next
  case (RRESIDUE cs rep)
  then show ?case by simp
qed

lemma good_rsimp5_alt_rows:
  assumes "good r \<or> r = RZERO"
  shows "\<forall>x \<in> set (rsimp5_alt_rows r). good x \<or> x = RZERO"
  using assms good_RALTS_elem by (cases r) auto

lemma good_rsimp5_seq_products:
  assumes "\<forall>x \<in> set xs. good x \<or> x = RZERO"
      and "\<forall>y \<in> set ys. good y \<or> y = RZERO"
  shows "\<forall>z \<in> set (rsimp5_seq_products xs ys). good z \<or> z = RZERO"
  using assms good_rsimp4_SEQ_atom by (induct xs) auto

lemma good_rsimp5_SEQ:
  assumes "good r1 \<or> r1 = RZERO" "good r2 \<or> r2 = RZERO"
  shows "good (rsimp5_SEQ r1 r2) \<or> rsimp5_SEQ r1 r2 = RZERO"
proof -
  have rows1: "\<forall>x \<in> set (rsimp5_alt_rows r1). good x \<or> x = RZERO"
    by (rule good_rsimp5_alt_rows[OF assms(1)])
  have rows2: "\<forall>x \<in> set (rsimp5_alt_rows r2). good x \<or> x = RZERO"
    by (rule good_rsimp5_alt_rows[OF assms(2)])
  have products: "\<forall>z \<in>
      set (rsimp5_seq_products (rsimp5_alt_rows r1) (rsimp5_alt_rows r2)).
      good z \<or> z = RZERO"
    by (rule good_rsimp5_seq_products[OF rows1 rows2])
  show ?thesis
    unfolding rsimp5_SEQ_def
    by (rule good_rsimp_ALTs_rdistinct_rflts[OF products])
qed

lemma good_rsimp5:
  shows "good (rsimp5 r) \<or> rsimp5 r = RZERO"
proof (induct r)
  case RZERO
  then show ?case by simp
next
  case RONE
  then show ?case by simp
next
  case (RCHAR x)
  then show ?case by simp
next
  case (RSEQ r1 r2)
  then show ?case
    using good_rsimp5_SEQ by simp
next
  case (RALTS rs)
  have elems: "\<forall>r \<in> set (map rsimp5 rs). good r \<or> r = RZERO"
    using RALTS by auto
  show ?case
    using good_rsimp_ALTs_rdistinct_rflts[OF elems] by simp
next
  case (RSTAR r)
  then show ?case by simp
next
  case (RNTIMES r n)
  then show ?case by simp
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  then show ?case by simp
next
  case (RHALF r cs rep)
  then show ?case by simp
next
  case (RRESIDUE cs rep)
  then show ?case by simp
qed

lemma length_rsimp5_seq_products [simp]:
  "length (rsimp5_seq_products xs ys) = length xs * length ys"
  by (induct xs) auto

lemma length_rsimp5_alt_rows_le_rsize:
  "length (rsimp5_alt_rows r) \<le> rsize r"
proof (cases r)
  case (RALTS rs)
  have "length rs \<le> rsizes rs"
  proof (induct rs)
    case Nil
    then show ?case by simp
  next
    case (Cons a rs)
    have "1 \<le> rsize a"
      using size_geq1[of a] .
    then show ?case
      using Cons by simp
  qed
  then show ?thesis
    using RALTS by simp
qed simp_all

lemma length_rsimp5_seq_products_alt_rows_le:
  "length (rsimp5_seq_products (rsimp5_alt_rows r1) (rsimp5_alt_rows r2)) \<le>
    rsize r1 * rsize r2"
proof -
  have "length (rsimp5_alt_rows r1) * length (rsimp5_alt_rows r2) \<le>
    rsize r1 * rsize r2"
    by (rule mult_mono)
      (use length_rsimp5_alt_rows_le_rsize in auto)
  then show ?thesis by simp
qed

lemma rsimp4_SEQ_atom_RZERO_right [simp]:
  "rsimp4_SEQ_atom r RZERO = RZERO"
  by (induct r) simp_all

fun row_nf :: "rrexp \<Rightarrow> bool" where
  "row_nf RZERO = False"
| "row_nf RONE = True"
| "row_nf (RCHAR c) = True"
| "row_nf (RALTS rs) = False"
| "row_nf (RSEQ r1 r2) =
    (row_nf r1 \<and> row_nf r2 \<and>
      r1 \<noteq> RZERO \<and> r1 \<noteq> RONE \<and> r2 \<noteq> RZERO \<and> r2 \<noteq> RONE)"
| "row_nf (RSTAR r) = True"
| "row_nf (RNTIMES r n) = True"
| "row_nf (RBACKREF4 r1 r2 r3 r4 cs) = True"
| "row_nf (RHALF r cs rep) = True"
| "row_nf (RRESIDUE cs rep) = True"

lemma row_nf_nonalt:
  assumes "row_nf r"
  shows "nonalt r"
  using assms by (cases r) auto

lemma row_nf_not_RZERO:
  assumes "row_nf r"
  shows "r \<noteq> RZERO"
  using assms by (cases r) auto

lemma row_nf_rsimp4_SEQ_atom:
  assumes "row_nf x" "row_nf y"
  shows "row_nf (rsimp4_SEQ_atom x y) \<or> rsimp4_SEQ_atom x y = RZERO"
  using assms
proof (induct x arbitrary: y)
  case RZERO
  then show ?case by simp
next
  case RONE
  then show ?case by simp
next
  case (RCHAR c)
  then show ?case
    by (cases y) simp_all
next
  case (RSEQ x1 x2)
  have x1_nf: "row_nf x1"
    using RSEQ.prems by simp
  have x2_nf: "row_nf x2"
    using RSEQ.prems by simp
  have inner: "row_nf (rsimp4_SEQ_atom x2 y) \<or>
      rsimp4_SEQ_atom x2 y = RZERO"
    by (rule RSEQ.hyps(2)[OF x2_nf RSEQ.prems(2)])
  then show ?case
  proof
    assume inner_nf: "row_nf (rsimp4_SEQ_atom x2 y)"
    show ?thesis
      using RSEQ.hyps(1)[OF x1_nf inner_nf] by simp
  next
    assume inner_zero: "rsimp4_SEQ_atom x2 y = RZERO"
    then show ?thesis by simp
  qed
next
  case (RALTS rs)
  then show ?case by simp
next
  case (RSTAR r)
  then show ?case
    by (cases y) simp_all
next
  case (RNTIMES r n)
  then show ?case
    by (cases y) simp_all
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  then show ?case
    by (cases y) simp_all
next
  case (RHALF r cs rep)
  then show ?case
    by (cases y) simp_all
next
  case (RRESIDUE cs rep)
  then show ?case
    by (cases y) simp_all
qed

lemma row_nf_rsimp5_seq_products:
  assumes "\<forall>x \<in> set xs. row_nf x"
      and "\<forall>y \<in> set ys. row_nf y"
  shows "\<forall>z \<in> set (rsimp5_seq_products xs ys). row_nf z \<or> z = RZERO"
  using assms row_nf_rsimp4_SEQ_atom by (induct xs) auto

definition rows_nf :: "rrexp \<Rightarrow> bool" where
  "rows_nf r = (\<forall>x \<in> set (rsimp5_alt_rows r). row_nf x)"

lemma row_nf_alt_rows_self:
  assumes "row_nf r"
  shows "rsimp5_alt_rows r = [r]"
  using assms by (cases r) auto

lemma rows_nf_of_row_nf_or_zero:
  assumes "row_nf r \<or> r = RZERO"
  shows "rows_nf r"
  using assms row_nf_alt_rows_self
  by (auto simp add: rows_nf_def)

lemma rows_nf_rflts:
  assumes "\<forall>r \<in> set rs. rows_nf r"
  shows "\<forall>x \<in> set (rflts rs). row_nf x"
  using assms
  by (induct rs rule: rflts.induct) (auto simp add: rows_nf_def)

lemma rows_nf_rdistinct:
  assumes "\<forall>x \<in> set rs. row_nf x"
  shows "\<forall>x \<in> set (rdistinct rs acc). row_nf x"
  using assms by (auto simp add: rdistinct_set_equality1)

lemma rows_nf_rsimp_ALTs:
  assumes "\<forall>x \<in> set rs. row_nf x"
  shows "rows_nf (rsimp_ALTs rs)"
proof (cases rs)
  case Nil
  then show ?thesis
    by (simp add: rows_nf_def)
next
  case (Cons r rs')
  note rs_outer = Cons
  then show ?thesis
  proof (cases rs')
    case Nil
    then have "row_nf r"
      using Cons assms by simp
    then show ?thesis
      using Cons Nil row_nf_alt_rows_self
      by (simp add: rows_nf_def)
  next
    case (Cons r' rs'')
    then have rs_shape: "rs = r # r' # rs''"
      using rs_outer by simp
    then show ?thesis
      using assms rs_shape by (simp add: rows_nf_def)
  qed
qed

lemma rows_nf_normalize:
  assumes "\<forall>r \<in> set rs. rows_nf r"
  shows "rows_nf (rsimp_ALTs (rdistinct (rflts rs) {}))"
proof -
  have flat: "\<forall>x \<in> set (rflts rs). row_nf x"
    by (rule rows_nf_rflts[OF assms])
  have distinct: "\<forall>x \<in> set (rdistinct (rflts rs) {}). row_nf x"
    by (rule rows_nf_rdistinct[OF flat])
  show ?thesis
    by (rule rows_nf_rsimp_ALTs[OF distinct])
qed

lemma rows_nf_rsimp5_SEQ:
  assumes "rows_nf r1" "rows_nf r2"
  shows "rows_nf (rsimp5_SEQ r1 r2)"
proof -
  have rows1: "\<forall>x \<in> set (rsimp5_alt_rows r1). row_nf x"
    using assms(1) by (simp add: rows_nf_def)
  have rows2: "\<forall>x \<in> set (rsimp5_alt_rows r2). row_nf x"
    using assms(2) by (simp add: rows_nf_def)
  have products: "\<forall>z \<in>
      set (rsimp5_seq_products (rsimp5_alt_rows r1) (rsimp5_alt_rows r2)).
      row_nf z \<or> z = RZERO"
    by (rule row_nf_rsimp5_seq_products[OF rows1 rows2])
  have products_rows: "\<forall>z \<in>
      set (rsimp5_seq_products (rsimp5_alt_rows r1) (rsimp5_alt_rows r2)).
      rows_nf z"
    using products rows_nf_of_row_nf_or_zero by blast
  show ?thesis
    unfolding rsimp5_SEQ_def
    by (rule rows_nf_normalize[OF products_rows])
qed

lemma rows_nf_rsimp5:
  shows "rows_nf (rsimp5 r)"
proof (induct r)
  case RZERO
  then show ?case
    by (simp add: rows_nf_def)
next
  case RONE
  then show ?case
    by (simp add: rows_nf_def)
next
  case (RCHAR c)
  then show ?case
    by (simp add: rows_nf_def)
next
  case (RSEQ r1 r2)
  then show ?case
    using rows_nf_rsimp5_SEQ by simp
next
  case (RALTS rs)
  have "\<forall>r \<in> set (map rsimp5 rs). rows_nf r"
    using RALTS by auto
  then show ?case
    using rows_nf_normalize by simp
next
  case (RSTAR r)
  then show ?case
    by (simp add: rows_nf_def)
next
  case (RNTIMES r n)
  then show ?case
    by (simp add: rows_nf_def)
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  then show ?case
    by (simp add: rows_nf_def)
next
  case (RHALF r cs rep)
  then show ?case
    by (simp add: rows_nf_def)
next
  case (RRESIDUE cs rep)
  then show ?case
    by (simp add: rows_nf_def)
qed

lemma card_rfrontier_row_nf_or_zero_le_one:
  assumes "row_nf r \<or> r = RZERO"
  shows "card (rfrontier r) \<le> 1"
  using assms by (cases r) auto

lemma card_rfrontiers_row_nf_or_zero_le_length:
  assumes "\<forall>r \<in> set rs. row_nf r \<or> r = RZERO"
  shows "card (rfrontiers rs) \<le> length rs"
  using assms
proof (induct rs)
  case Nil
  then show ?case by simp
next
  case (Cons r rs)
  have head: "card (rfrontier r) \<le> 1"
    by (rule card_rfrontier_row_nf_or_zero_le_one) (use Cons.prems in auto)
  have tail: "card (rfrontiers rs) \<le> length rs"
    by (rule Cons.hyps) (use Cons.prems in auto)
  have "card (rfrontiers (r # rs)) \<le>
    card (rfrontier r) + card (rfrontiers rs)"
    by (simp add: card_Un_le)
  then show ?case
    using head tail by simp
qed

lemma card_rfrontier_rsimp5_SEQ_le_size_product_if_row_nf:
  assumes "\<forall>x \<in> set (rsimp5_alt_rows r1). row_nf x"
      and "\<forall>x \<in> set (rsimp5_alt_rows r2). row_nf x"
  shows "card (rfrontier (rsimp5_SEQ r1 r2)) \<le> rsize r1 * rsize r2"
proof -
  let ?rows1 = "rsimp5_alt_rows r1"
  let ?rows2 = "rsimp5_alt_rows r2"
  let ?products = "rsimp5_seq_products ?rows1 ?rows2"
  have products: "\<forall>z \<in> set ?products. row_nf z \<or> z = RZERO"
    by (rule row_nf_rsimp5_seq_products[OF assms])
  have "card (rfrontier (rsimp5_SEQ r1 r2)) = card (rfrontiers ?products)"
    by (simp add: rsimp5_SEQ_def)
  also have "... \<le> length ?products"
    by (rule card_rfrontiers_row_nf_or_zero_le_length[OF products])
  also have "... \<le> rsize r1 * rsize r2"
    by (rule length_rsimp5_seq_products_alt_rows_le)
  finally show ?thesis .
qed

lemma card_rfrontier_rsimp5_SEQ_le_size_product:
  "card (rfrontier (rsimp5_SEQ (rsimp5 r1) (rsimp5 r2))) \<le>
    rsize (rsimp5 r1) * rsize (rsimp5 r2)"
proof -
  have rows1: "\<forall>x \<in> set (rsimp5_alt_rows (rsimp5 r1)). row_nf x"
    using rows_nf_rsimp5 by (simp add: rows_nf_def)
  have rows2: "\<forall>x \<in> set (rsimp5_alt_rows (rsimp5 r2)). row_nf x"
    using rows_nf_rsimp5 by (simp add: rows_nf_def)
  show ?thesis
    by (rule card_rfrontier_rsimp5_SEQ_le_size_product_if_row_nf[OF rows1 rows2])
qed

lemma rfrontier_alt_rows_eq:
  "rfrontier r = rfrontiers (rsimp5_alt_rows r)"
  by (cases r) simp_all

lemma card_rfrontier_rows_nf_le_alt_rows:
  assumes "rows_nf r"
  shows "card (rfrontier r) \<le> length (rsimp5_alt_rows r)"
proof -
  have rows: "\<forall>x \<in> set (rsimp5_alt_rows r). row_nf x \<or> x = RZERO"
    using assms by (auto simp add: rows_nf_def)
  have "card (rfrontier r) = card (rfrontiers (rsimp5_alt_rows r))"
    by (simp add: rfrontier_alt_rows_eq)
  also have "... \<le> length (rsimp5_alt_rows r)"
    by (rule card_rfrontiers_row_nf_or_zero_le_length[OF rows])
  finally show ?thesis .
qed

lemma card_rfrontier_rsimp5_le_alt_rows:
  "card (rfrontier (rsimp5 r)) \<le> length (rsimp5_alt_rows (rsimp5 r))"
  by (rule card_rfrontier_rows_nf_le_alt_rows[OF rows_nf_rsimp5])

lemma rsimp5_rows_two_binary_alts:
  assumes "a \<noteq> b" "c \<noteq> d"
  shows "length
    (rsimp5_alt_rows
      (rsimp5 (RSEQ (RALTS [RCHAR a, RCHAR b]) (RALTS [RCHAR c, RCHAR d])))) = 4"
proof -
  have "b \<noteq> a" "d \<noteq> c"
    using assms by auto
  then show ?thesis
    using assms by (simp add: rsimp5_SEQ_def)
qed

lemma rfrontier_nonzero_nonalt_self:
  assumes "r \<noteq> RZERO" "nonalt r"
  shows "r \<in> rfrontier r"
  using assms by (cases r) simp_all

lemma rfrontier_nonzero_nonalt_eq:
  assumes "r \<noteq> RZERO" "nonalt r"
  shows "rfrontier r = {r}"
  using assms by (cases r) simp_all

lemma rfrontier_good_member_SEQ_subset:
  assumes "good r \<or> r = RZERO"
      and "x \<in> rfrontier r"
  shows "rfrontier (rsimp4_SEQ x k) \<subseteq> rfrontier (rsimp4_SEQ r k)"
proof (cases r)
  case RZERO
  then show ?thesis
    using assms by simp
next
  case RONE
  then show ?thesis
    using assms by simp
next
  case (RCHAR c)
  then show ?thesis
    using assms by simp
next
  case (RSEQ r1 r2)
  then show ?thesis
    using assms by simp
next
  case (RALTS rs)
  then obtain y where y: "y \<in> set rs" "x \<in> rfrontier y"
    using assms rfrontiers_member_iff by auto
  have good_y: "good y \<and> nonalt y"
    using assms RALTS y(1) good_RALTS_elem by blast
  then have y_nonzero: "y \<noteq> RZERO"
    using good_not_RZERO by blast
  have y_frontier: "rfrontier y = {y}"
    by (rule rfrontier_nonzero_nonalt_eq) (use y_nonzero good_y in auto)
  have x_y: "x = y"
    using y(2) y_frontier by simp
  have "rfrontier (rsimp4_SEQ x k) =
    rfrontier (rsimp4_SEQ_atom x k)"
    using good_y x_y by (simp add: rfrontier_rsimp4_SEQ_nonalt_eq_atom)
  also have "... \<subseteq> rfrontier (rsimp4_SEQ r k)"
  proof -
    have "x \<in> rseq_sources r"
      using RALTS y(1) x_y by simp
    then show ?thesis
      by (rule rfrontier_rsimp4_SEQ_atom_source_subset)
  qed
  finally show ?thesis .
next
  case (RSTAR r)
  then show ?thesis
    using assms by simp
next
  case (RNTIMES r n)
  then show ?thesis
    using assms by simp
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  then show ?thesis
    using assms by simp
next
  case (RHALF r cs rep)
  then show ?thesis
    using assms by simp
next
  case (RRESIDUE cs rep)
  then show ?thesis
    using assms by simp
qed

lemma rfrontier_rsimp4_SEQ_nonseq_sources_subset:
  assumes sub: "\<And>x. x \<in> rseq_sources r1 \<Longrightarrow> x \<in> rsubterms r"
      and nonseq: "\<And>x. x \<in> rseq_sources r1 \<Longrightarrow> rnonseq x"
      and cont: "r2 \<in> rlinear_continuations r"
  shows "rfrontier (rsimp4_SEQ r1 r2) \<subseteq> partial_derivative_frontier_universe r"
  by (rule rfrontier_rsimp4_SEQ_subset)
    (use sub nonseq cont rfrontier_rsimp4_SEQ_atom_nonseq_subset' in blast)

lemma simple_continuations_miss_left_nested_suffix:
  "RSEQ (RCHAR b) (RCHAR c) \<notin>
    rlinear_continuations (RSEQ (RSEQ (RSTAR (RCHAR a)) (RCHAR b)) (RCHAR c))"
  by simp

lemma rsimp4_derivative_needs_left_nested_suffix:
  assumes "a \<noteq> b"
  shows "RSEQ (RSTAR (RCHAR a)) (RSEQ (RCHAR b) (RCHAR c)) \<in>
    rfrontier
      (rsimp4
        (rder a (RSEQ (RSEQ (RSTAR (RCHAR a)) (RCHAR b)) (RCHAR c))))"
  using assms by (simp add: rsimp4_SEQ_def)

fun rpath_continuations_acc :: "rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "rpath_continuations_acc RZERO k = {}"
| "rpath_continuations_acc RONE k = {}"
| "rpath_continuations_acc (RCHAR c) k = {k}"
| "rpath_continuations_acc (RALTS rs) k =
    (\<Union> (set (map (\<lambda>r. rpath_continuations_acc r k) rs)))"
| "rpath_continuations_acc (RSEQ r1 r2) k =
    rpath_continuations_acc r1 (rsimp4_SEQ_atom r2 k) \<union>
    rpath_continuations_acc r2 k"
| "rpath_continuations_acc (RSTAR r) k =
    rpath_continuations_acc r (rsimp4_SEQ_atom (RSTAR r) k)"
| "rpath_continuations_acc (RNTIMES r n) k =
    (if n = 0 then {} else
      rpath_continuations_acc r (rsimp4_SEQ_atom (RNTIMES r (n - 1)) k))"
| "rpath_continuations_acc (RBACKREF4 r1 r2 r3 r4 cs) k =
    rpath_continuations_acc r1 k \<union> rpath_continuations_acc r2 k \<union>
    rpath_continuations_acc r3 k \<union> rpath_continuations_acc r4 k"
| "rpath_continuations_acc (RHALF r cs rep) k = rpath_continuations_acc r k"
| "rpath_continuations_acc (RRESIDUE cs rep) k = {}"

definition rpath_continuations :: "rrexp \<Rightarrow> rrexp set" where
  "rpath_continuations r = rpath_continuations_acc r RONE"

lemma finite_rpath_continuations_acc [simp]:
  "finite (rpath_continuations_acc r k)"
  by (induct r arbitrary: k) auto

lemma finite_rpath_continuations_list [simp]:
  "finite (\<Union> (set (map (\<lambda>r. rpath_continuations_acc r k) rs)))"
  by (induct rs) auto

lemma card_rpath_continuations_acc_list_le_rsizes:
  assumes step: "\<And>r. r \<in> set rs \<Longrightarrow>
    card (rpath_continuations_acc r k) \<le> rsize r"
  shows "card (\<Union> (set (map (\<lambda>r. rpath_continuations_acc r k) rs)))
    \<le> rsizes rs"
  using step
proof (induct rs)
  case Nil
  then show ?case by simp
next
  case (Cons r rs)
  have "card (\<Union> (set (map (\<lambda>r. rpath_continuations_acc r k) (r # rs)))) =
    card (rpath_continuations_acc r k \<union>
      (\<Union> (set (map (\<lambda>r. rpath_continuations_acc r k) rs))))"
    by simp
  also have "... \<le> card (rpath_continuations_acc r k) +
    card (\<Union> (set (map (\<lambda>r. rpath_continuations_acc r k) rs)))"
    by (rule card_Un_le)
  also have "... \<le> rsize r + rsizes rs"
  proof -
    have r_le: "card (rpath_continuations_acc r k) \<le> rsize r"
      using Cons.prems by simp
    have rs_le: "card (\<Union> (set (map (\<lambda>r. rpath_continuations_acc r k) rs)))
      \<le> rsizes rs"
      using Cons.hyps Cons.prems by simp
    show ?thesis
      using r_le rs_le by linarith
  qed
  finally show ?case
    by simp
qed

lemma card_rpath_continuations_acc_le_rsize:
  "card (rpath_continuations_acc r k) \<le> rsize r"
proof (induct r arbitrary: k)
  case RZERO
  then show ?case by simp
next
  case RONE
  then show ?case by simp
next
  case (RCHAR x)
  then show ?case by simp
next
  case (RALTS rs)
  then show ?case
    using card_rpath_continuations_acc_list_le_rsizes[of rs k] by simp
next
  case (RSEQ r1 r2)
  have "card (rpath_continuations_acc (RSEQ r1 r2) k) \<le>
    card (rpath_continuations_acc r1 (rsimp4_SEQ_atom r2 k)) +
    card (rpath_continuations_acc r2 k)"
    by (simp add: card_Un_le)
  also have "... \<le> rsize r1 + rsize r2"
  proof -
    have left: "card (rpath_continuations_acc r1 (rsimp4_SEQ_atom r2 k)) \<le> rsize r1"
      using RSEQ.hyps(1) by simp
    have right: "card (rpath_continuations_acc r2 k) \<le> rsize r2"
      using RSEQ.hyps(2) by simp
    show ?thesis
      using left right by linarith
  qed
  also have "... \<le> rsize (RSEQ r1 r2)"
    by simp
  finally show ?case .
next
  case (RSTAR r)
  then have "card (rpath_continuations_acc r (rsimp4_SEQ_atom (RSTAR r) k)) \<le> rsize r"
    by simp
  then show ?case by simp
next
  case (RNTIMES r n)
  then show ?case
  proof (cases n)
    case 0
    then show ?thesis by simp
  next
    case (Suc m)
    have "card (rpath_continuations_acc r
      (rsimp4_SEQ_atom (RNTIMES r m) k)) \<le> rsize r"
      using RNTIMES.hyps by simp
    then show ?thesis
      using Suc by simp
  qed
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  have "card (rpath_continuations_acc (RBACKREF4 r1 r2 r3 r4 cs) k) \<le>
    card (rpath_continuations_acc r1 k) + card (rpath_continuations_acc r2 k) +
    card (rpath_continuations_acc r3 k) + card (rpath_continuations_acc r4 k)"
    using card_Un4_le[of "rpath_continuations_acc r1 k" "rpath_continuations_acc r2 k"
      "rpath_continuations_acc r3 k" "rpath_continuations_acc r4 k"] by simp
  also have "... \<le> rsize (RBACKREF4 r1 r2 r3 r4 cs)"
  proof -
    have c1: "card (rpath_continuations_acc r1 k) \<le> rsize r1"
      using RBACKREF4.hyps(1) by simp
    have c2: "card (rpath_continuations_acc r2 k) \<le> rsize r2"
      using RBACKREF4.hyps(2) by simp
    have c3: "card (rpath_continuations_acc r3 k) \<le> rsize r3"
      using RBACKREF4.hyps(3) by simp
    have c4: "card (rpath_continuations_acc r4 k) \<le> rsize r4"
      using RBACKREF4.hyps(4) by simp
    show ?thesis
      using c1 c2 c3 c4 by simp
  qed
  finally show ?case .
next
  case (RHALF r cs rep)
  then have "card (rpath_continuations_acc r k) \<le> rsize r"
    by simp
  then show ?case by simp
next
  case (RRESIDUE cs rep)
  then show ?case by simp
qed

lemma card_rpath_continuations_le_rsize:
  "card (rpath_continuations r) \<le> rsize r"
  unfolding rpath_continuations_def
  by (rule card_rpath_continuations_acc_le_rsize)

lemma rsize_rsimp4_SEQ_atom_le:
  "rsize (rsimp4_SEQ_atom r1 r2) \<le> Suc (rsize r1 + rsize r2)"
proof (induct r1 arbitrary: r2)
  case RZERO
  then show ?case by simp
next
  case RONE
  then show ?case by simp
next
  case (RCHAR x)
  show ?case
  proof (cases r2)
    case RZERO
    then show ?thesis by simp
  next
    case RONE
    then show ?thesis by simp
  next
    case (RCHAR y)
    then show ?thesis by simp
  next
    case (RSEQ y1 y2)
    then show ?thesis by simp
  next
    case (RALTS ys)
    then show ?thesis by simp
  next
    case (RSTAR y)
    then show ?thesis by simp
  next
    case (RNTIMES y n)
    then show ?thesis by simp
  next
    case (RBACKREF4 y1 y2 y3 y4 ys)
    then show ?thesis by simp
  next
    case (RHALF y ys rep)
    then show ?thesis by simp
  next
    case (RRESIDUE ys rep)
    then show ?thesis by simp
  qed
next
  case (RSEQ r1 r1')
  have "rsize (rsimp4_SEQ_atom (RSEQ r1 r1') r2) =
    rsize (rsimp4_SEQ_atom r1 (rsimp4_SEQ_atom r1' r2))"
    by simp
  also have "... \<le> Suc (rsize r1 + rsize (rsimp4_SEQ_atom r1' r2))"
    using RSEQ.hyps(1) by simp
  also have "... \<le> Suc (rsize r1 + Suc (rsize r1' + rsize r2))"
    using RSEQ.hyps(2) by simp
  also have "... \<le> Suc (rsize (RSEQ r1 r1') + rsize r2)"
    by simp
  finally show ?case .
next
  case (RALTS x)
  then show ?case
    by (cases r2) simp_all
next
  case (RSTAR x)
  then show ?case
    by (cases r2) simp_all
next
  case (RNTIMES x1 x2)
  then show ?case
    by (cases r2) simp_all
next
  case (RBACKREF4 x1 x2 x3 x4 x5)
  then show ?case
    by (cases r2) simp_all
next
  case (RHALF x1 x2 x3)
  then show ?case
    by (cases r2) simp_all
next
  case (RRESIDUE x1 x2)
  then show ?case
    by (cases r2) simp_all
qed

lemma square_mono_nat:
  fixes m n :: nat
  assumes "m \<le> n"
  shows "m\<^sup>2 \<le> n\<^sup>2"
proof -
  have "m * m \<le> n * m"
    using assms by (simp add: mult_right_mono)
  also have "... \<le> n * n"
    using assms by (simp add: mult_left_mono)
  finally show ?thesis
    by (simp add: power2_eq_square)
qed

lemma add_square_le_Suc_square:
  fixes n :: nat
  shows "n + n\<^sup>2 \<le> (Suc n)\<^sup>2"
  by (simp add: power2_eq_square algebra_simps)

lemma Suc_plus_square_le_Suc_square:
  fixes n :: nat
  shows "Suc n + n\<^sup>2 \<le> (Suc n)\<^sup>2"
  by (simp add: power2_eq_square algebra_simps)

lemma nat_le_one_plus_square:
  fixes n :: nat
  shows "n \<le> 1 + n\<^sup>2"
  by (cases n) (simp_all add: power2_eq_square algebra_simps)

lemma component_plus_square_le_Suc_sum_square:
  fixes a b :: nat
  shows "b + a\<^sup>2 \<le> (Suc (a + b))\<^sup>2"
proof -
  have a2: "a\<^sup>2 \<le> (a + b)\<^sup>2"
    by (rule square_mono_nat) simp
  have "b + a\<^sup>2 \<le> (a + b) + (a + b)\<^sup>2"
    using a2 by linarith
  also have "... \<le> (Suc (a + b))\<^sup>2"
    by (rule add_square_le_Suc_square)
  finally show ?thesis .
qed

lemma component_Suc_plus_shifted_square_le:
  fixes a b :: nat
  shows "Suc b + (a + 2)\<^sup>2 \<le> (Suc (a + b) + 2)\<^sup>2"
proof -
  let ?n = "a + b + 2"
  have sq: "(a + 2)\<^sup>2 \<le> ?n\<^sup>2"
    by (rule square_mono_nat) simp
  have "Suc b + (a + 2)\<^sup>2 \<le> ?n + ?n\<^sup>2"
    using sq by linarith
  also have "... \<le> (Suc ?n)\<^sup>2"
    by (rule add_square_le_Suc_square)
  also have "(Suc ?n)\<^sup>2 = (Suc (a + b) + 2)\<^sup>2"
    by simp
  finally show ?thesis .
qed

lemma rfrontier_rsimp4_SEQ_atom_member_size_quadratic:
  assumes "q \<in> rfrontier (rsimp4_SEQ_atom r k)"
  shows "rsize q \<le> rsize k + (rsize r + 2)\<^sup>2"
  using assms
proof (induct r arbitrary: k q)
  case RZERO
  then show ?case by simp
next
  case RONE
  have "q \<in> rfrontier k"
    using RONE.prems by simp
  then have "q \<in> rsubterms k"
    using rfrontier_subset_rsubterms by blast
  then have "rsize q \<le> rsize k"
    using rsubterms_member_size_le_rsize by blast
  then show ?case by simp
next
  case (RCHAR x)
  then show ?case
    by (cases k) (simp_all add: power2_eq_square)
next
  case (RSEQ r1 r2)
  have "rsize q \<le>
    rsize (rsimp4_SEQ_atom r2 k) + (rsize r1 + 2)\<^sup>2"
    using RSEQ.hyps(1) RSEQ.prems by simp
  also have "... \<le> Suc (rsize r2 + rsize k) + (rsize r1 + 2)\<^sup>2"
    using rsize_rsimp4_SEQ_atom_le[of r2 k] by linarith
  also have "... \<le> rsize k + (rsize (RSEQ r1 r2) + 2)\<^sup>2"
  proof -
    have "Suc (rsize r2) + (rsize r1 + 2)\<^sup>2 \<le>
      (Suc (rsize r1 + rsize r2) + 2)\<^sup>2"
      by (rule component_Suc_plus_shifted_square_le)
    then show ?thesis
      by simp
  qed
  finally show ?case .
next
  case (RALTS rs)
  then show ?case
  proof (cases k)
    case RONE
    have q_front: "q \<in> rfrontiers rs"
      using RALTS.prems RONE by simp
    then have "q \<in> (\<Union> (set (map rsubterms rs)))"
      using rfrontiers_subset_rsubterms by blast
    then have "q \<in> rsubterms (RALTS rs)"
      by simp
    then have "rsize q \<le> rsize (RALTS rs)"
      using rsubterms_member_size_le_rsize by blast
    moreover have "rsize (RALTS rs) \<le>
      rsize RONE + (rsize (RALTS rs) + 2)\<^sup>2"
    proof -
      have base: "rsize (RALTS rs) \<le> 1 + (rsize (RALTS rs))\<^sup>2"
        by (rule nat_le_one_plus_square)
      have sq: "(rsize (RALTS rs))\<^sup>2 \<le> (rsize (RALTS rs) + 2)\<^sup>2"
        by (rule square_mono_nat) simp
      have "rsize (RALTS rs) \<le> 1 + (rsize (RALTS rs) + 2)\<^sup>2"
        using base sq by linarith
      then show ?thesis
        by simp
    qed
    then show ?thesis
      using RONE calculation by simp
  qed (simp_all add: power2_eq_square)
next
  case (RSTAR r)
  then show ?case
    by (cases k) (simp_all add: power2_eq_square)
next
  case (RNTIMES r n)
  then show ?case
    by (cases k) (simp_all add: power2_eq_square)
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  then show ?case
    by (cases k) (simp_all add: power2_eq_square)
next
  case (RHALF r cs rep)
  then show ?case
    by (cases k) (simp_all add: power2_eq_square)
next
  case (RRESIDUE cs rep)
  then show ?case
    by (cases k) (simp_all add: power2_eq_square)
qed

lemma rfrontier_normalize_memberE:
  assumes "q \<in> rfrontier (rsimp_ALTs (rdistinct (rflts rs) {}))"
  obtains r where "r \<in> set rs" "q \<in> rfrontier r"
proof -
  have sub: "rfrontier (rsimp_ALTs (rdistinct (rflts rs) {})) \<subseteq>
    rfrontiers rs"
    by (rule rfrontier_normalize_subset)
      (induct rs, auto)
  then have "q \<in> rfrontiers rs"
    using assms by blast
  then show ?thesis
    using that by (induct rs) auto
qed

lemma rfrontier_member_in_rfrontiers:
  assumes "r \<in> set rs" "q \<in> rfrontier r"
  shows "q \<in> rfrontiers rs"
  using assms by (induct rs) auto

lemma rfrontiers_concat_rsimp4_seq_rows_memberE:
  assumes "q \<in> rfrontiers (concat (map (\<lambda>x. rsimp4_seq_row x k) rs))"
  obtains r where "r \<in> set rs" "q \<in> rfrontier (rsimp4_SEQ_atom r k)"
  using assms that
  by (induct rs) auto

lemma rfrontier_rsimp4_SEQ_single_member_size_quadratic:
  assumes "q \<in> rfrontier
    (rsimp_ALTs (rdistinct (rflts (rsimp4_seq_row r k)) {}))"
  shows "rsize q \<le> rsize k + (rsize r + 2)\<^sup>2"
proof -
  obtain r' where r': "r' \<in> set (rsimp4_seq_row r k)" "q \<in> rfrontier r'"
    using assms by (rule rfrontier_normalize_memberE)
  then have "q \<in> rfrontier (rsimp4_SEQ_atom r k)"
    by simp
  then show ?thesis
    by (rule rfrontier_rsimp4_SEQ_atom_member_size_quadratic)
qed

lemma rfrontier_rsimp4_SEQ_member_size_quadratic:
  assumes "q \<in> rfrontier (rsimp4_SEQ r k)"
  shows "rsize q \<le> rsize k + (rsize r + 2)\<^sup>2"
  using assms
proof (cases r)
  case RZERO
  have "q \<in> rfrontier
    (rsimp_ALTs (rdistinct (rflts (rsimp4_seq_row RZERO k)) {}))"
    using assms RZERO by (simp add: rsimp4_SEQ_def)
  then have "rsize q \<le> rsize k + (rsize RZERO + 2)\<^sup>2"
    by (rule rfrontier_rsimp4_SEQ_single_member_size_quadratic)
  then show ?thesis
    using RZERO by simp
next
  case RONE
  have "q \<in> rfrontier
    (rsimp_ALTs (rdistinct (rflts (rsimp4_seq_row RONE k)) {}))"
    using assms RONE by (simp add: rsimp4_SEQ_def)
  then have "rsize q \<le> rsize k + (rsize RONE + 2)\<^sup>2"
    by (rule rfrontier_rsimp4_SEQ_single_member_size_quadratic)
  then show ?thesis
    using RONE by simp
next
  case (RCHAR x)
  have "q \<in> rfrontier
    (rsimp_ALTs (rdistinct (rflts (rsimp4_seq_row (RCHAR x) k)) {}))"
    using assms RCHAR by (simp add: rsimp4_SEQ_def)
  then have "rsize q \<le> rsize k + (rsize (RCHAR x) + 2)\<^sup>2"
    by (rule rfrontier_rsimp4_SEQ_single_member_size_quadratic)
  then show ?thesis
    using RCHAR by simp
next
  case (RSEQ r1 r2)
  have "q \<in> rfrontier
    (rsimp_ALTs (rdistinct (rflts (rsimp4_seq_row (RSEQ r1 r2) k)) {}))"
    using assms RSEQ by (simp add: rsimp4_SEQ_def)
  then have "rsize q \<le> rsize k + (rsize (RSEQ r1 r2) + 2)\<^sup>2"
    by (rule rfrontier_rsimp4_SEQ_single_member_size_quadratic)
  then show ?thesis
    using RSEQ by simp
next
  case (RALTS rs)
  have q_rows: "q \<in> rfrontiers (concat (map (\<lambda>x. rsimp4_seq_row x k) rs))"
  proof -
    have "q \<in> rfrontier
      (rsimp_ALTs
        (rdistinct (rflts (concat (map (\<lambda>x. rsimp4_seq_row x k) rs))) {}))"
      using assms RALTS by (simp add: rsimp4_SEQ_def)
    then obtain row where row:
        "row \<in> set (concat (map (\<lambda>x. rsimp4_seq_row x k) rs))"
        "q \<in> rfrontier row"
      by (rule rfrontier_normalize_memberE)
    then show ?thesis
      by (rule rfrontier_member_in_rfrontiers)
  qed
  then obtain r' where r': "r' \<in> set rs"
      "q \<in> rfrontier (rsimp4_SEQ_atom r' k)"
    by (rule rfrontiers_concat_rsimp4_seq_rows_memberE)
  have "rsize q \<le> rsize k + (rsize r' + 2)\<^sup>2"
    using rfrontier_rsimp4_SEQ_atom_member_size_quadratic[OF r'(2)] .
  also have "... \<le> rsize k + (rsize (RALTS rs) + 2)\<^sup>2"
  proof -
    have "rsize r' + 2 \<le> rsize (RALTS rs) + 2"
      using rsize_member_le_rsizes[OF r'(1)] by simp
    then have "(rsize r' + 2)\<^sup>2 \<le> (rsize (RALTS rs) + 2)\<^sup>2"
      by (rule square_mono_nat)
    then show ?thesis
      by linarith
  qed
  finally show ?thesis
    using RALTS by simp
next
  case (RSTAR r)
  have "q \<in> rfrontier
    (rsimp_ALTs (rdistinct (rflts (rsimp4_seq_row (RSTAR r) k)) {}))"
    using assms RSTAR by (simp add: rsimp4_SEQ_def)
  then have "rsize q \<le> rsize k + (rsize (RSTAR r) + 2)\<^sup>2"
    by (rule rfrontier_rsimp4_SEQ_single_member_size_quadratic)
  then show ?thesis
    using RSTAR by simp
next
  case (RNTIMES r n)
  have "q \<in> rfrontier
    (rsimp_ALTs (rdistinct (rflts (rsimp4_seq_row (RNTIMES r n) k)) {}))"
    using assms RNTIMES by (simp add: rsimp4_SEQ_def)
  then have "rsize q \<le> rsize k + (rsize (RNTIMES r n) + 2)\<^sup>2"
    by (rule rfrontier_rsimp4_SEQ_single_member_size_quadratic)
  then show ?thesis
    using RNTIMES by simp
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  have "q \<in> rfrontier
    (rsimp_ALTs
      (rdistinct (rflts (rsimp4_seq_row (RBACKREF4 r1 r2 r3 r4 cs) k)) {}))"
    using assms RBACKREF4 by (simp add: rsimp4_SEQ_def)
  then have "rsize q \<le>
    rsize k + (rsize (RBACKREF4 r1 r2 r3 r4 cs) + 2)\<^sup>2"
    by (rule rfrontier_rsimp4_SEQ_single_member_size_quadratic)
  then show ?thesis
    using RBACKREF4 by simp
next
  case (RHALF r cs rep)
  have "q \<in> rfrontier
    (rsimp_ALTs (rdistinct (rflts (rsimp4_seq_row (RHALF r cs rep) k)) {}))"
    using assms RHALF by (simp add: rsimp4_SEQ_def)
  then have "rsize q \<le> rsize k + (rsize (RHALF r cs rep) + 2)\<^sup>2"
    by (rule rfrontier_rsimp4_SEQ_single_member_size_quadratic)
  then show ?thesis
    using RHALF by simp
next
  case (RRESIDUE cs rep)
  have "q \<in> rfrontier
    (rsimp_ALTs (rdistinct (rflts (rsimp4_seq_row (RRESIDUE cs rep) k)) {}))"
    using assms RRESIDUE by (simp add: rsimp4_SEQ_def)
  then have "rsize q \<le> rsize k + (rsize (RRESIDUE cs rep) + 2)\<^sup>2"
    by (rule rfrontier_rsimp4_SEQ_single_member_size_quadratic)
  then show ?thesis
    using RRESIDUE by simp
qed

lemma rpath_continuations_acc_member_size_quadratic:
  assumes "q \<in> rpath_continuations_acc r k"
  shows "rsize q \<le> rsize k + (rsize r + 2)\<^sup>2"
  using assms
proof (induct r arbitrary: k q)
  case RZERO
  then show ?case by simp
next
  case RONE
  then show ?case by simp
next
  case (RCHAR x)
  then show ?case by simp
next
  case (RALTS rs)
  then obtain r where r: "r \<in> set rs" "q \<in> rpath_continuations_acc r k"
    by auto
  have "rsize q \<le> rsize k + (rsize r + 2)\<^sup>2"
    using RALTS r by auto
  also have "... \<le> rsize k + (rsize (RALTS rs) + 2)\<^sup>2"
  proof -
    have "rsize r + 2 \<le> rsize (RALTS rs) + 2"
      using rsize_member_le_rsizes[OF r(1)] by simp
    then have "(rsize r + 2)\<^sup>2 \<le> (rsize (RALTS rs) + 2)\<^sup>2"
      by (rule square_mono_nat)
    then show ?thesis
      by linarith
  qed
  finally show ?case .
next
  case (RSEQ r1 r2)
  then consider
      "q \<in> rpath_continuations_acc r1 (rsimp4_SEQ_atom r2 k)"
    | "q \<in> rpath_continuations_acc r2 k"
    by auto
  then show ?case
  proof cases
    case 1
    have "rsize q \<le>
      rsize (rsimp4_SEQ_atom r2 k) + (rsize r1 + 2)\<^sup>2"
      using RSEQ 1 by auto
    also have "... \<le> Suc (rsize r2 + rsize k) + (rsize r1 + 2)\<^sup>2"
      using rsize_rsimp4_SEQ_atom_le[of r2 k] by linarith
    also have "... \<le> rsize k + (rsize (RSEQ r1 r2) + 2)\<^sup>2"
    proof -
      have "Suc (rsize r2) + (rsize r1 + 2)\<^sup>2 \<le>
        (Suc (rsize r1 + rsize r2) + 2)\<^sup>2"
        by (rule component_Suc_plus_shifted_square_le)
      then show ?thesis
        by simp
    qed
    finally show ?thesis .
  next
    case 2
    have "rsize q \<le> rsize k + (rsize r2 + 2)\<^sup>2"
      using RSEQ 2 by auto
    also have "... \<le> rsize k + (rsize (RSEQ r1 r2) + 2)\<^sup>2"
      using square_mono_nat[of "rsize r2 + 2" "rsize (RSEQ r1 r2) + 2"] by simp
    finally show ?thesis .
  qed
next
  case (RSTAR r)
  have "rsize q \<le>
    rsize (rsimp4_SEQ_atom (RSTAR r) k) + (rsize r + 2)\<^sup>2"
    using RSTAR by auto
  also have "... \<le> Suc (rsize (RSTAR r) + rsize k) + (rsize r + 2)\<^sup>2"
    using rsize_rsimp4_SEQ_atom_le[of "RSTAR r" k] by linarith
  also have "... \<le> rsize k + (rsize (RSTAR r) + 2)\<^sup>2"
  proof -
    have "Suc (rsize (RSTAR r)) + (rsize r + 2)\<^sup>2 \<le>
      (rsize (RSTAR r) + 2)\<^sup>2"
      using add_square_le_Suc_square[of "rsize r + 2"] by simp
    then show ?thesis
      by simp
  qed
  finally show ?case .
next
  case (RNTIMES r n)
  then show ?case
  proof (cases n)
    case 0
    then show ?thesis
      using RNTIMES by simp
  next
    case (Suc m)
    have q: "q \<in> rpath_continuations_acc r
      (rsimp4_SEQ_atom (RNTIMES r m) k)"
      using RNTIMES Suc by simp
    have "rsize q \<le>
      rsize (rsimp4_SEQ_atom (RNTIMES r m) k) + (rsize r + 2)\<^sup>2"
      using RNTIMES.hyps[OF q] .
    also have "... \<le> Suc (rsize (RNTIMES r m) + rsize k) + (rsize r + 2)\<^sup>2"
      using rsize_rsimp4_SEQ_atom_le[of "RNTIMES r m" k] by linarith
  also have "... \<le> rsize k + (rsize (RNTIMES r n) + 2)\<^sup>2"
    proof -
      let ?base = "rsize r + Suc m + 2"
      have r_le: "rsize r + 2 \<le> ?base"
        by simp
      have sq_le: "(rsize r + 2)\<^sup>2 \<le> ?base\<^sup>2"
        by (rule square_mono_nat[OF r_le])
      have size_le: "Suc (rsize (RNTIMES r m)) \<le> ?base"
        by simp
      have "Suc (rsize (RNTIMES r m)) + (rsize r + 2)\<^sup>2 \<le>
        ?base + ?base\<^sup>2"
        using sq_le size_le by linarith
      also have "... \<le> (Suc ?base)\<^sup>2"
        by (rule add_square_le_Suc_square)
      finally show ?thesis
        using Suc by simp
    qed
    finally show ?thesis .
  qed
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  then consider
      "q \<in> rpath_continuations_acc r1 k"
    | "q \<in> rpath_continuations_acc r2 k"
    | "q \<in> rpath_continuations_acc r3 k"
    | "q \<in> rpath_continuations_acc r4 k"
    by auto
  then show ?case
  proof cases
    case 1
    then have "rsize q \<le> rsize k + (rsize r1 + 2)\<^sup>2"
      using RBACKREF4 by auto
    then show ?thesis
    proof -
      have "(rsize r1 + 2)\<^sup>2 \<le> (rsize (RBACKREF4 r1 r2 r3 r4 cs) + 2)\<^sup>2"
        by (rule square_mono_nat) simp
      then show ?thesis
        using \<open>rsize q \<le> rsize k + (rsize r1 + 2)\<^sup>2\<close> by linarith
    qed
  next
    case 2
    then have "rsize q \<le> rsize k + (rsize r2 + 2)\<^sup>2"
      using RBACKREF4 by auto
    then show ?thesis
    proof -
      have "(rsize r2 + 2)\<^sup>2 \<le> (rsize (RBACKREF4 r1 r2 r3 r4 cs) + 2)\<^sup>2"
        by (rule square_mono_nat) simp
      then show ?thesis
        using \<open>rsize q \<le> rsize k + (rsize r2 + 2)\<^sup>2\<close> by linarith
    qed
  next
    case 3
    then have "rsize q \<le> rsize k + (rsize r3 + 2)\<^sup>2"
      using RBACKREF4 by auto
    then show ?thesis
    proof -
      have "(rsize r3 + 2)\<^sup>2 \<le> (rsize (RBACKREF4 r1 r2 r3 r4 cs) + 2)\<^sup>2"
        by (rule square_mono_nat) simp
      then show ?thesis
        using \<open>rsize q \<le> rsize k + (rsize r3 + 2)\<^sup>2\<close> by linarith
    qed
  next
    case 4
    then have "rsize q \<le> rsize k + (rsize r4 + 2)\<^sup>2"
      using RBACKREF4 by auto
    then show ?thesis
    proof -
      have "(rsize r4 + 2)\<^sup>2 \<le> (rsize (RBACKREF4 r1 r2 r3 r4 cs) + 2)\<^sup>2"
        by (rule square_mono_nat) simp
      then show ?thesis
        using \<open>rsize q \<le> rsize k + (rsize r4 + 2)\<^sup>2\<close> by linarith
    qed
  qed
next
  case (RHALF r cs rep)
  then have "rsize q \<le> rsize k + (rsize r + 2)\<^sup>2"
    by auto
  then show ?case
  proof -
    have "(rsize r + 2)\<^sup>2 \<le> (rsize (RHALF r cs rep) + 2)\<^sup>2"
      by (rule square_mono_nat) simp
    then show ?thesis
      using \<open>rsize q \<le> rsize k + (rsize r + 2)\<^sup>2\<close> by linarith
  qed
next
  case (RRESIDUE cs rep)
  then show ?case by simp
qed

lemma rpath_continuations_member_size_quadratic:
  assumes "q \<in> rpath_continuations r"
  shows "rsize q \<le> 1 + (rsize r + 2)\<^sup>2"
proof -
  have "rsize q \<le> rsize RONE + (rsize r + 2)\<^sup>2"
    using assms
    unfolding rpath_continuations_def
    by (rule rpath_continuations_acc_member_size_quadratic)
  then show ?thesis
    by simp
qed

lemma finite_rpath_continuations [simp]:
  "finite (rpath_continuations r)"
  unfolding rpath_continuations_def by simp

definition partial_derivative_path_universe :: "rrexp \<Rightarrow> rrexp set" where
  "partial_derivative_path_universe r =
    insert RZERO (insert RONE (rsubterms r \<union> rpath_continuations r))"

definition partial_derivative_live_path_universe :: "rrexp \<Rightarrow> rrexp set" where
  "partial_derivative_live_path_universe r =
    insert RZERO (insert RONE (insert r (rpath_continuations r)))"

lemma finite_partial_derivative_path_universe [simp]:
  "finite (partial_derivative_path_universe r)"
  by (simp add: partial_derivative_path_universe_def rpath_continuations_def)

lemma finite_partial_derivative_live_path_universe [simp]:
  "finite (partial_derivative_live_path_universe r)"
  by (simp add: partial_derivative_live_path_universe_def rpath_continuations_def)

lemma partial_derivative_live_path_universe_subset_path:
  "partial_derivative_live_path_universe r \<subseteq>
    partial_derivative_path_universe r"
  by (auto simp add: partial_derivative_live_path_universe_def
      partial_derivative_path_universe_def)

lemma partial_derivative_path_universe_card_linear:
  "card (partial_derivative_path_universe r) \<le> 2 + 2 * rsize r"
proof -
  let ?A = "rsubterms r"
  let ?K = "rpath_continuations r"
  have A: "card ?A \<le> rsize r"
    by (rule card_rsubterms_le_rsize)
  have K: "card ?K \<le> rsize r"
    by (rule card_rpath_continuations_le_rsize)
  have "card (partial_derivative_path_universe r) \<le> 2 + card ?A + card ?K"
  proof -
    have U: "partial_derivative_path_universe r = insert RZERO (insert RONE (?A \<union> ?K))"
      unfolding partial_derivative_path_universe_def by simp
    have "card (insert RZERO (insert RONE (?A \<union> ?K))) \<le>
      2 + card ?A + card ?K"
      by (rule card_insert2_Un_le) simp_all
    then show ?thesis
      using U by simp
  qed
  also have "... \<le> 2 + 2 * rsize r"
    using A K by linarith
  finally show ?thesis .
qed

lemma partial_derivative_path_universe_member_size_quadratic:
  assumes "q \<in> partial_derivative_path_universe r"
  shows "rsize q \<le> 1 + (rsize r + 2)\<^sup>2"
proof -
  let ?A = "rsubterms r"
  let ?K = "rpath_continuations r"
  have q_cases: "q = RZERO \<or> q = RONE \<or> q \<in> ?A \<or> q \<in> ?K"
    using assms unfolding partial_derivative_path_universe_def by auto
  then show ?thesis
  proof
    assume "q = RZERO"
    then show ?thesis by simp
  next
    assume rest1: "q = RONE \<or> q \<in> ?A \<or> q \<in> ?K"
    then show ?thesis
    proof
      assume "q = RONE"
      then show ?thesis by simp
    next
      assume rest2: "q \<in> ?A \<or> q \<in> ?K"
      then show ?thesis
      proof
        assume "q \<in> ?A"
        then have "rsize q \<le> rsize r"
          using rsubterms_member_size_le_rsize by blast
        then show ?thesis
        proof -
          have "rsize r \<le> 1 + (rsize r + 2)\<^sup>2"
            using nat_le_one_plus_square[of "rsize r + 2"] by simp
          then show ?thesis
            using \<open>rsize q \<le> rsize r\<close> by linarith
        qed
      next
        assume "q \<in> ?K"
        then show ?thesis
          using rpath_continuations_member_size_quadratic by blast
      qed
    qed
  qed
qed

lemma linear_times_quadratic_cubic_bound:
  fixes n :: nat
  shows "(2 + 2 * n) * (1 + (n + 2)\<^sup>2) \<le> 2 * (n + 3) ^ 3"
  by (simp add: power2_eq_square power3_eq_cube algebra_simps)

lemma rsizes_le_length_times_bound:
  assumes "\<And>x. x \<in> set rs \<Longrightarrow> rsize x \<le> M"
  shows "rsizes rs \<le> length rs * M"
  using assms
proof (induct rs)
  case Nil
  then show ?case by simp
next
  case (Cons r rs)
  have head: "rsize r \<le> M"
    by (rule Cons.prems) simp
  have tail: "rsizes rs \<le> length rs * M"
    by (rule Cons.hyps) (use Cons.prems in auto)
  show ?case
    using head tail by simp
qed

lemma length_distinct_subset_card:
  assumes "finite A" "set rs \<subseteq> A" "distinct rs"
  shows "length rs \<le> card A"
proof -
  have "length rs = card (set rs)"
    using assms by (simp add: distinct_card)
  also have "... \<le> card A"
    by (rule card_mono) (use assms in auto)
  finally show ?thesis .
qed

lemma rsizes_distinct_path_universe_cubic:
  assumes "set rs \<subseteq> partial_derivative_path_universe r"
      and "distinct rs"
  shows "rsizes rs \<le> 2 * (rsize r + 3) ^ 3"
proof -
  let ?U = "partial_derivative_path_universe r"
  let ?M = "1 + (rsize r + 2)\<^sup>2"
  have member_bound: "\<And>x. x \<in> set rs \<Longrightarrow> rsize x \<le> ?M"
    using assms(1) partial_derivative_path_universe_member_size_quadratic
    by blast
  have "rsizes rs \<le> length rs * ?M"
    by (rule rsizes_le_length_times_bound[OF member_bound])
  also have "... \<le> card ?U * ?M"
  proof -
    have "length rs \<le> card ?U"
      by (rule length_distinct_subset_card) (use assms in auto)
    then show ?thesis
      by (rule mult_right_mono) simp
  qed
  also have "... \<le> (2 + 2 * rsize r) * ?M"
  proof -
    have "card ?U \<le> 2 + 2 * rsize r"
      by (rule partial_derivative_path_universe_card_linear)
    then show ?thesis
      by (rule mult_right_mono) simp
  qed
  also have "... \<le> 2 * (rsize r + 3) ^ 3"
    by (rule linear_times_quadratic_cubic_bound)
  finally show ?thesis .
qed

lemma rsizes_distinct_live_path_universe_cubic:
  assumes "set rs \<subseteq> partial_derivative_live_path_universe r"
      and "distinct rs"
  shows "rsizes rs \<le> 2 * (rsize r + 3) ^ 3"
  by (rule rsizes_distinct_path_universe_cubic)
    (use assms partial_derivative_live_path_universe_subset_path in blast)+

lemma quadratic_times_linear_cubic_bound:
  fixes n :: nat
  shows "(n + 2) ^ 2 * Suc (n + n) \<le> 3 * (n + 2) ^ 3"
proof -
  have linear: "Suc (n + n) \<le> 3 * (n + 2)"
    by simp
  have "(n + 2) ^ 2 * Suc (n + n) \<le>
      (n + 2) ^ 2 * (3 * (n + 2))"
    by (rule mult_left_mono[OF linear]) simp
  also have "... = 3 * ((n + 2) ^ 2 * (n + 2))"
    by (simp add: algebra_simps)
  also have "... = 3 * (n + 2) ^ 3"
    by (simp add: power3_eq_cube power2_eq_square)
  finally show ?thesis .
qed

lemma rsizes_distinct_frontier_universe_cubic:
  assumes "set rs \<subseteq> partial_derivative_frontier_universe r"
      and "distinct rs"
  shows "rsizes rs \<le> 3 * (rsize r + 2) ^ 3"
proof -
  let ?U = "partial_derivative_frontier_universe r"
  let ?M = "Suc (rsize r + rsize r)"
  have member_bound: "\<And>x. x \<in> set rs \<Longrightarrow> rsize x \<le> ?M"
    using assms(1) partial_derivative_frontier_universe_member_size_linear
    by blast
  have "rsizes rs \<le> length rs * ?M"
    by (rule rsizes_le_length_times_bound[OF member_bound])
  also have "... \<le> card ?U * ?M"
  proof -
    have "length rs \<le> card ?U"
      by (rule length_distinct_subset_card) (use assms in auto)
    then show ?thesis
      by (rule mult_right_mono) simp
  qed
  also have "... \<le> (rsize r + 2) ^ 2 * ?M"
  proof -
    have "card ?U \<le> (rsize r + 2) ^ 2"
      by (rule partial_derivative_frontier_universe_card_quadratic)
    then show ?thesis
      by (rule mult_right_mono) simp
  qed
  also have "... \<le> 3 * (rsize r + 2) ^ 3"
    by (rule quadratic_times_linear_cubic_bound)
  finally show ?thesis .
qed

definition partial_derivative_cubic_universe :: "rrexp \<Rightarrow> rrexp set" where
  "partial_derivative_cubic_universe r =
    partial_derivative_path_universe r \<union> partial_derivative_frontier_universe r"

lemma finite_partial_derivative_cubic_universe [simp]:
  "finite (partial_derivative_cubic_universe r)"
  by (simp add: partial_derivative_cubic_universe_def)

lemma partial_derivative_path_universe_subset_cubic:
  "partial_derivative_path_universe r \<subseteq>
    partial_derivative_cubic_universe r"
  by (simp add: partial_derivative_cubic_universe_def)

lemma partial_derivative_frontier_universe_subset_cubic:
  "partial_derivative_frontier_universe r \<subseteq>
    partial_derivative_cubic_universe r"
  by (simp add: partial_derivative_cubic_universe_def)

lemma set_rdistinct_subset:
  assumes "set rs \<subseteq> U"
  shows "set (rdistinct rs acc) \<subseteq> U"
  using assms
  by (induct rs arbitrary: acc) auto

lemma set_rflts_good_subset_rfrontiers:
  assumes "\<forall>r \<in> set rs. good r \<or> r = RZERO"
  shows "set (rflts rs) \<subseteq> insert RZERO (rfrontiers rs)"
  using assms
proof (induct rs)
  case Nil
  then show ?case by simp
next
  case (Cons a rs)
  have tail_good: "\<forall>r \<in> set rs. good r \<or> r = RZERO"
    using Cons.prems by simp
  have tail_subset: "set (rflts rs) \<subseteq> insert RZERO (rfrontiers rs)"
    by (rule Cons.hyps[OF tail_good])
  show ?case
  proof (cases a)
    case RZERO
    then show ?thesis
      using tail_subset by simp
  next
    case (RALTS rs1)
    have good_alt: "good (RALTS rs1)"
      using Cons.prems RALTS by simp
    have elems_good: "\<forall>r \<in> set rs1. good r \<and> nonalt r"
      using good_alt good_RALTS_elem by blast
    have head_subset: "set rs1 \<subseteq> rfrontiers rs1"
    proof
      fix x
      assume x: "x \<in> set rs1"
      have "x \<noteq> RZERO"
        using elems_good x good_not_RZERO by blast
      moreover have "nonalt x"
        using elems_good x by blast
      ultimately have "x \<in> rfrontier x"
        by (rule rfrontier_nonzero_nonalt_self)
      then show "x \<in> rfrontiers rs1"
        using x rfrontiers_member_iff by blast
    qed
    show ?thesis
      using RALTS head_subset tail_subset by auto
  qed (use tail_subset in auto)
qed

lemma set_rflts_subset_rsubterms_list:
  "set (rflts rs) \<subseteq> (\<Union>r \<in> set rs. rsubterms r)"
proof (induct rs)
  case Nil
  then show ?case by simp
next
  case (Cons a rs)
  show ?case
  proof (cases a)
    case RZERO
    then show ?thesis
      using Cons.hyps by auto
  next
    case (RALTS rs1)
    have "set rs1 \<subseteq> rsubterms (RALTS rs1)"
      using self_rsubterm by auto
    then show ?thesis
      using Cons.hyps RALTS by auto
  qed (use Cons.hyps in auto)
qed

lemma set_rflts_frontier_universe_subset:
  assumes "set rs \<subseteq> partial_derivative_frontier_universe r"
  shows "set (rflts rs) \<subseteq> partial_derivative_frontier_universe r"
proof
  fix x
  assume "x \<in> set (rflts rs)"
  then have "x \<in> (\<Union>q \<in> set rs. rsubterms q)"
    using set_rflts_subset_rsubterms_list[of rs] by blast
  then obtain q where q: "q \<in> set rs" "x \<in> rsubterms q"
    by blast
  have "rsubterms q \<subseteq> partial_derivative_frontier_universe r"
    by (rule rsubterms_frontier_universe_member_subset)
      (use assms q in auto)
  then show "x \<in> partial_derivative_frontier_universe r"
    using q by blast
qed

lemma set_rflts_subterms_subsetI:
  assumes "\<And>q. q \<in> set rs \<Longrightarrow> rsubterms q \<subseteq> U"
  shows "set (rflts rs) \<subseteq> U"
proof
  fix x
  assume "x \<in> set (rflts rs)"
  then have "x \<in> (\<Union>q \<in> set rs. rsubterms q)"
    using set_rflts_subset_rsubterms_list[of rs] by blast
  then obtain q where q: "q \<in> set rs" "x \<in> rsubterms q"
    by blast
  show "x \<in> U"
    using assms[OF q(1)] q(2) by blast
qed

lemma set_rdistinct_rflts_frontier_universe_subset:
  assumes "set rs \<subseteq> partial_derivative_frontier_universe r"
  shows "set (rdistinct (rflts rs) acc) \<subseteq>
    partial_derivative_frontier_universe r"
  by (rule set_rdistinct_subset)
    (rule set_rflts_frontier_universe_subset[OF assms])

lemma rpder_norm_rows_frontier_universe_subsetI:
  assumes "\<And>q. q \<in> set rs \<Longrightarrow>
    set (rpder_norm_list c q) \<subseteq> partial_derivative_frontier_universe r"
  shows "set (rpder_norm_rows c rs) \<subseteq>
    partial_derivative_frontier_universe r"
proof -
  have "set (concat (map (rpder_norm_list c) rs)) \<subseteq>
      partial_derivative_frontier_universe r"
    using assms by auto
  then have "set (rdistinct
      (rflts (concat (map (rpder_norm_list c) rs))) {}) \<subseteq>
      partial_derivative_frontier_universe r"
    by (rule set_rdistinct_rflts_frontier_universe_subset)
  then show ?thesis
    by (simp add: rpder_norm_rows_def)
qed

lemma rpder_norm_rows_subterms_subsetI:
  assumes "\<And>q p. q \<in> set rs \<Longrightarrow> p \<in> set (rpder_norm_list c q) \<Longrightarrow>
    rsubterms p \<subseteq> U"
  shows "set (rpder_norm_rows c rs) \<subseteq> U"
proof -
  have flat: "set (rflts (concat (map (rpder_norm_list c) rs))) \<subseteq> U"
    by (rule set_rflts_subterms_subsetI)
      (use assms in auto)
  have "set (rdistinct
      (rflts (concat (map (rpder_norm_list c) rs))) {}) \<subseteq> U"
    by (rule set_rdistinct_subset[OF flat])
  then show ?thesis
    by (simp add: rpder_norm_rows_def)
qed

lemma rpder_norm6_rows_subterms_subsetI:
  assumes "\<And>q p. q \<in> set rs \<Longrightarrow> p \<in> set (rpder_norm6_list c q) \<Longrightarrow>
    rsubterms p \<subseteq> U"
  shows "set (rpder_norm6_rows c rs) \<subseteq> U"
proof -
  have flat: "set (rflts (concat (map (rpder_norm6_list c) rs))) \<subseteq> U"
    by (rule set_rflts_subterms_subsetI)
      (use assms in auto)
  have "set (rdistinct
      (rflts (concat (map (rpder_norm6_list c) rs))) {}) \<subseteq> U"
    by (rule set_rdistinct_subset[OF flat])
  then show ?thesis
    by (simp add: rpder_norm6_rows_def)
qed

lemma rpders_norm_rows_frontier_universe_subsetI:
  assumes init: "set rs \<subseteq> partial_derivative_frontier_universe r"
      and step: "\<And>q c. q \<in> partial_derivative_frontier_universe r \<Longrightarrow>
        set (rpder_norm_list c q) \<subseteq> partial_derivative_frontier_universe r"
  shows "set (rpders_norm_rows rs s) \<subseteq>
    partial_derivative_frontier_universe r"
  using init
proof (induct s arbitrary: rs)
  case Nil
  then show ?case by simp
next
  case (Cons c s)
  have next_subset: "set (rpder_norm_rows c rs) \<subseteq>
    partial_derivative_frontier_universe r"
    by (rule rpder_norm_rows_frontier_universe_subsetI)
      (use Cons.prems step in auto)
  show ?case
    by (simp add: Cons.hyps[OF next_subset])
qed

lemma rpders_norm1_rows_frontier_universe_subsetI:
  assumes step: "\<And>q c. q \<in> partial_derivative_frontier_universe r \<Longrightarrow>
    set (rpder_norm_list c q) \<subseteq> partial_derivative_frontier_universe r"
  shows "set (rpders_norm1_rows r s) \<subseteq>
    partial_derivative_frontier_universe r"
proof -
  have "set [r] \<subseteq> partial_derivative_frontier_universe r"
    by (simp add: partial_derivative_frontier_universe_subterm)
  then have "set (rpders_norm_rows [r] s) \<subseteq>
      partial_derivative_frontier_universe r"
    by (rule rpders_norm_rows_frontier_universe_subsetI)
      (use step in auto)
  then show ?thesis
    by (simp add: rpders_norm1_rows_def)
qed

lemma rpders_norm_rows_subterms_subsetI:
  assumes init: "set rs \<subseteq> U"
      and step: "\<And>q c p. q \<in> U \<Longrightarrow> p \<in> set (rpder_norm_list c q) \<Longrightarrow>
        rsubterms p \<subseteq> U"
  shows "set (rpders_norm_rows rs s) \<subseteq> U"
  using init
proof (induct s arbitrary: rs)
  case Nil
  then show ?case by simp
next
  case (Cons c s)
  have next_subset: "set (rpder_norm_rows c rs) \<subseteq> U"
  proof (rule rpder_norm_rows_subterms_subsetI)
    fix q p
    assume q: "q \<in> set rs"
      and p: "p \<in> set (rpder_norm_list c q)"
    have "q \<in> U"
      using Cons.prems q by blast
    then show "rsubterms p \<subseteq> U"
      by (rule step[OF _ p])
  qed
  show ?case
    by (simp add: Cons.hyps[OF next_subset])
qed

lemma rpders_norm1_rows_subterms_subsetI:
  assumes init: "r \<in> U"
      and step: "\<And>q c p. q \<in> U \<Longrightarrow> p \<in> set (rpder_norm_list c q) \<Longrightarrow>
        rsubterms p \<subseteq> U"
  shows "set (rpders_norm1_rows r s) \<subseteq> U"
proof -
  have "set [r] \<subseteq> U"
    using init by simp
  then have "set (rpders_norm_rows [r] s) \<subseteq> U"
    by (rule rpders_norm_rows_subterms_subsetI)
      (use step in auto)
  then show ?thesis
    by (simp add: rpders_norm1_rows_def)
qed

lemma rpders_norm6_rows_subterms_subsetI:
  assumes init: "set rs \<subseteq> U"
      and step: "\<And>q c p. q \<in> U \<Longrightarrow> p \<in> set (rpder_norm6_list c q) \<Longrightarrow>
        rsubterms p \<subseteq> U"
  shows "set (rpders_norm6_rows rs s) \<subseteq> U"
  using init
proof (induct s arbitrary: rs)
  case Nil
  then show ?case by simp
next
  case (Cons c s)
  have next_subset: "set (rpder_norm6_rows c rs) \<subseteq> U"
  proof (rule rpder_norm6_rows_subterms_subsetI)
    fix q p
    assume q: "q \<in> set rs"
      and p: "p \<in> set (rpder_norm6_list c q)"
    have "q \<in> U"
      using Cons.prems q by blast
    then show "rsubterms p \<subseteq> U"
      by (rule step[OF _ p])
  qed
  show ?case
    by (simp add: Cons.hyps[OF next_subset])
qed

lemma rpders_norm16_rows_subterms_subsetI:
  assumes init: "r \<in> U"
      and step: "\<And>q c p. q \<in> U \<Longrightarrow> p \<in> set (rpder_norm6_list c q) \<Longrightarrow>
        rsubterms p \<subseteq> U"
  shows "set (rpders_norm16_rows r s) \<subseteq> U"
proof -
  have "set [r] \<subseteq> U"
    using init by simp
  then have "set (rpders_norm6_rows [r] s) \<subseteq> U"
    by (rule rpders_norm6_rows_subterms_subsetI)
      (use step in auto)
  then show ?thesis
    by (simp add: rpders_norm16_rows_def)
qed

lemma rsizes_filter_partition:
  "rsizes rs =
    rsizes (filter P rs) + rsizes (filter (\<lambda>x. \<not> P x) rs)"
  by (induct rs) auto

lemma cube_mono_offset:
  fixes n :: nat
  shows "(n + 2) ^ 3 \<le> (n + 3) ^ 3"
  by (rule power_mono) simp_all

lemma rsizes_distinct_cubic_universe_cubic:
  assumes "set rs \<subseteq> partial_derivative_cubic_universe r"
      and "distinct rs"
  shows "rsizes rs \<le> 5 * (rsize r + 3) ^ 3"
proof -
  let ?path = "partial_derivative_path_universe r"
  let ?front = "partial_derivative_frontier_universe r"
  let ?rs_path = "filter (\<lambda>x. x \<in> ?path) rs"
  let ?rs_front = "filter (\<lambda>x. x \<notin> ?path) rs"
  have path_subset: "set ?rs_path \<subseteq> ?path"
    by auto
  have front_subset: "set ?rs_front \<subseteq> ?front"
    using assms(1)
    by (auto simp add: partial_derivative_cubic_universe_def)
  have path_cubic: "rsizes ?rs_path \<le> 2 * (rsize r + 3) ^ 3"
    by (rule rsizes_distinct_path_universe_cubic)
      (use assms path_subset in auto)
  have front_cubic: "rsizes ?rs_front \<le> 3 * (rsize r + 3) ^ 3"
  proof -
    have "rsizes ?rs_front \<le> 3 * (rsize r + 2) ^ 3"
      by (rule rsizes_distinct_frontier_universe_cubic)
        (use assms front_subset in auto)
    also have "... \<le> 3 * (rsize r + 3) ^ 3"
      using cube_mono_offset[of "rsize r"] by simp
    finally show ?thesis .
  qed
  have "rsizes rs = rsizes ?rs_path + rsizes ?rs_front"
    by (rule rsizes_filter_partition)
  also have "... \<le>
    2 * (rsize r + 3) ^ 3 + 3 * (rsize r + 3) ^ 3"
    using path_cubic front_cubic by linarith
  also have "... = 5 * (rsize r + 3) ^ 3"
    by simp
  finally show ?thesis .
qed

lemma rsizes_rpders_norm1_rows_frontier_universe_cubic:
  assumes "set (rpders_norm1_rows r s) \<subseteq>
    partial_derivative_frontier_universe r"
  shows "rsizes (rpders_norm1_rows r s) \<le> 3 * (rsize r + 2) ^ 3"
  by (rule rsizes_distinct_frontier_universe_cubic)
    (use assms in auto)

lemma rsizes_rpders_norm1_rows_frontier_universe_cubicI:
  assumes step: "\<And>q c. q \<in> partial_derivative_frontier_universe r \<Longrightarrow>
    set (rpder_norm_list c q) \<subseteq> partial_derivative_frontier_universe r"
  shows "rsizes (rpders_norm1_rows r s) \<le> 3 * (rsize r + 2) ^ 3"
proof -
  have "set (rpders_norm1_rows r s) \<subseteq>
      partial_derivative_frontier_universe r"
    by (rule rpders_norm1_rows_frontier_universe_subsetI[OF step])
  then show ?thesis
    by (rule rsizes_rpders_norm1_rows_frontier_universe_cubic)
qed

lemma rsizes_rpders_norm1_rows_cubic_universe_cubic:
  assumes "set (rpders_norm1_rows r s) \<subseteq>
    partial_derivative_cubic_universe r"
  shows "rsizes (rpders_norm1_rows r s) \<le> 5 * (rsize r + 3) ^ 3"
  by (rule rsizes_distinct_cubic_universe_cubic)
    (use assms in auto)

lemma rsizes_rpders_norm1_rows_cubic_universe_cubicI:
  assumes step: "\<And>q c p. q \<in> partial_derivative_cubic_universe r \<Longrightarrow>
    p \<in> set (rpder_norm_list c q) \<Longrightarrow>
    rsubterms p \<subseteq> partial_derivative_cubic_universe r"
  shows "rsizes (rpders_norm1_rows r s) \<le> 5 * (rsize r + 3) ^ 3"
proof -
  have init: "r \<in> partial_derivative_cubic_universe r"
    by (simp add: partial_derivative_cubic_universe_def
        partial_derivative_path_universe_def)
  have "set (rpders_norm1_rows r s) \<subseteq>
      partial_derivative_cubic_universe r"
    by (rule rpders_norm1_rows_subterms_subsetI[OF init step])
  then show ?thesis
    by (rule rsizes_rpders_norm1_rows_cubic_universe_cubic)
qed

lemma rsizes_rpders_norm16_rows_cubic_universe_cubic:
  assumes "set (rpders_norm16_rows r s) \<subseteq>
    partial_derivative_cubic_universe r"
  shows "rsizes (rpders_norm16_rows r s) \<le> 5 * (rsize r + 3) ^ 3"
  by (rule rsizes_distinct_cubic_universe_cubic)
    (use assms in auto)

lemma rsizes_rpders_norm16_rows_cubic_universe_cubicI:
  assumes step: "\<And>q c p. q \<in> partial_derivative_cubic_universe r \<Longrightarrow>
    p \<in> set (rpder_norm6_list c q) \<Longrightarrow>
    rsubterms p \<subseteq> partial_derivative_cubic_universe r"
  shows "rsizes (rpders_norm16_rows r s) \<le> 5 * (rsize r + 3) ^ 3"
proof -
  have init: "r \<in> partial_derivative_cubic_universe r"
    by (simp add: partial_derivative_cubic_universe_def
        partial_derivative_path_universe_def)
  have "set (rpders_norm16_rows r s) \<subseteq>
      partial_derivative_cubic_universe r"
    by (rule rpders_norm16_rows_subterms_subsetI[OF init step])
  then show ?thesis
    by (rule rsizes_rpders_norm16_rows_cubic_universe_cubic)
qed

lemma rsizes_rpders_norm16_rows_normalized_root_cubicI:
  assumes step: "\<And>q c p. q \<in> partial_derivative_cubic_universe (rsimp6 r) \<Longrightarrow>
    p \<in> set (rpder_norm6_list c q) \<Longrightarrow>
    rsubterms p \<subseteq> partial_derivative_cubic_universe (rsimp6 r)"
  shows "rsizes (rpders_norm16_rows (rsimp6 r) s) \<le>
    5 * (rsize (rsimp6 r) + 3) ^ 3"
  by (rule rsizes_rpders_norm16_rows_cubic_universe_cubicI[OF assms])

lemma rsizes_rpders_norm16_rows_live_path_universe_cubic:
  assumes "set (rpders_norm16_rows r s) \<subseteq>
    partial_derivative_live_path_universe r"
  shows "rsizes (rpders_norm16_rows r s) \<le> 2 * (rsize r + 3) ^ 3"
  by (rule rsizes_distinct_live_path_universe_cubic)
    (use assms in auto)

lemma rsizes_rpders_norm16_rows_live_path_universe_cubicI:
  assumes step: "\<And>q c p. q \<in> partial_derivative_live_path_universe r \<Longrightarrow>
    p \<in> set (rpder_norm6_list c q) \<Longrightarrow>
    rsubterms p \<subseteq> partial_derivative_live_path_universe r"
  shows "rsizes (rpders_norm16_rows r s) \<le> 2 * (rsize r + 3) ^ 3"
proof -
  have init: "r \<in> partial_derivative_live_path_universe r"
    by (simp add: partial_derivative_live_path_universe_def)
  have "set (rpders_norm16_rows r s) \<subseteq>
      partial_derivative_live_path_universe r"
    by (rule rpders_norm16_rows_subterms_subsetI[OF init step])
  then show ?thesis
    by (rule rsizes_rpders_norm16_rows_live_path_universe_cubic)
qed

lemma partial_derivative_path_universe_zero [simp]:
  "RZERO \<in> partial_derivative_path_universe r"
  by (simp add: partial_derivative_path_universe_def)

lemma partial_derivative_path_universe_one [simp]:
  "RONE \<in> partial_derivative_path_universe r"
  by (simp add: partial_derivative_path_universe_def)

lemma partial_derivative_path_universe_subterm:
  assumes "p \<in> rsubterms r"
  shows "p \<in> partial_derivative_path_universe r"
  using assms by (auto simp add: partial_derivative_path_universe_def)

lemma partial_derivative_path_universe_path_continuation:
  assumes "p \<in> rpath_continuations r"
  shows "p \<in> partial_derivative_path_universe r"
  using assms by (auto simp add: partial_derivative_path_universe_def)

lemma rsimp4_derivative_needs_path_continuation:
  assumes "a \<noteq> b"
  shows "RSEQ (RSTAR (RCHAR a)) (RSEQ (RCHAR b) (RCHAR c)) \<in>
    partial_derivative_path_universe
      (RSEQ (RSEQ (RSTAR (RCHAR a)) (RCHAR b)) (RCHAR c))"
  using assms
  by (simp add: partial_derivative_path_universe_def
      rpath_continuations_def rsimp4_SEQ_def)

lemma frontier_universe_not_closed_under_rpder_norm_list:
  fixes a b d :: char
  assumes "a \<noteq> b"
  defines "r \<equiv>
    RSEQ (RSEQ (RSTAR (RCHAR a)) (RCHAR b)) (RCHAR d)"
  defines "x \<equiv>
    RSEQ (RSTAR (RCHAR a)) (RSEQ (RCHAR b) (RCHAR d))"
  shows "r \<in> partial_derivative_frontier_universe r"
    and "x \<in> set (rpder_norm_list a r)"
    and "x \<notin> partial_derivative_frontier_universe r"
    and "x \<in> partial_derivative_path_universe r"
  using assms
  by (simp_all add: r_def x_def rpder_norm_list_def
      partial_derivative_frontier_universe_def
      partial_derivative_path_universe_def
      rpath_continuations_def rsimp4_SEQ_def)

lemma cubic_universe_not_closed_under_rpder_norm_list:
  fixes a :: char
  defines "r \<equiv> RSTAR (RSTAR (RCHAR a))"
  defines "q \<equiv> RSEQ (RSTAR (RSTAR (RCHAR a))) (RSTAR (RCHAR a))"
  defines "p \<equiv>
    RSEQ (RSTAR (RCHAR a))
      (RSEQ (RSTAR (RSTAR (RCHAR a))) (RSTAR (RCHAR a)))"
  shows "q \<in> partial_derivative_cubic_universe r"
    and "p \<in> set (rpder_norm_list a q)"
    and "p \<notin> partial_derivative_cubic_universe r"
  by (simp_all add: r_def q_def p_def rpder_norm_list_def
      partial_derivative_cubic_universe_def
      partial_derivative_frontier_universe_def
      partial_derivative_path_universe_def
      rpath_continuations_def rsimp4_SEQ_def)

lemma rsimp6_collapses_cubic_counterexample_row:
  fixes a :: char
  defines "p \<equiv>
    RSEQ (RSTAR (RCHAR a))
      (RSEQ (RSTAR (RSTAR (RCHAR a))) (RSTAR (RCHAR a)))"
  shows "rsimp6 p = RSTAR (RCHAR a)"
  by (simp add: p_def rsimp6_SEQ_def rsimp6_seq_products_def
      rsimp6_SEQ_atom_def)

lemma reachable_norm6_row_can_leave_current_cubic_universe:
  fixes a :: char
  defines "r \<equiv> RSTAR (RALTS [RZERO, RCHAR a])"
  defines "p \<equiv> RSTAR (RCHAR a)"
  shows "p \<in> set (rpders_norm16_rows r [a])"
    and "p \<notin> partial_derivative_cubic_universe r"
  by (simp_all add: r_def p_def rpders_norm16_rows_def
      rpder_norm6_rows_def rpder_norm6_list_def rpder_norm_list_def
      partial_derivative_cubic_universe_def
      partial_derivative_frontier_universe_def
      partial_derivative_path_universe_def
      rpath_continuations_def rlinear_continuations.simps
      rsimp6_SEQ_def rsimp6_seq_products_def rsimp6_SEQ_atom_def)

lemma normalized_root_universe_not_all_q_closed_under_norm6:
  fixes b :: char
  defines "r \<equiv> RSTAR (RSEQ (RCHAR b) (RCHAR b))"
  defines "q \<equiv> RSEQ r (RCHAR b)"
  defines "p \<equiv> RSEQ (RCHAR b) q"
  shows "q \<in> partial_derivative_cubic_universe r"
    and "p \<in> set (rpder_norm6_list b q)"
    and "\<not> rsubterms p \<subseteq> partial_derivative_cubic_universe r"
  by (simp_all add: r_def q_def p_def rpder_norm6_list_def
      rpder_norm_list_def partial_derivative_cubic_universe_def
      partial_derivative_frontier_universe_def
      partial_derivative_path_universe_def
      rpath_continuations_def rsimp6_SEQ_def rsimp6_seq_products_def
      rsimp6_SEQ_atom_def rsimp5_SEQ_def)

lemma path_universe_misses_distributed_suffix_atom:
  "RSEQ (RCHAR b) (RCHAR d) \<notin>
    partial_derivative_path_universe
      (RSEQ (RCHAR a) (RSEQ (RALTS [RCHAR b, RCHAR c]) (RCHAR d)))"
  by (simp add: partial_derivative_path_universe_def rpath_continuations_def)

lemma rsimp4_derivative_can_distribute_suffix_atom:
  "RSEQ (RCHAR b) (RCHAR d) \<in>
    rfrontier
      (rsimp4
        (rder a
          (RSEQ (RCHAR a) (RSEQ (RALTS [RCHAR b, RCHAR c]) (RCHAR d)))))"
  by (simp add: rsimp4_SEQ_def)

fun rder_path_continuations_acc :: "char \<Rightarrow> rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "rder_path_continuations_acc c RZERO k = {}"
| "rder_path_continuations_acc c RONE k = {}"
| "rder_path_continuations_acc c (RCHAR d) k = (if c = d then {k} else {})"
| "rder_path_continuations_acc c (RALTS rs) k =
    (\<Union> (set (map (\<lambda>r. rder_path_continuations_acc c r k) rs)))"
| "rder_path_continuations_acc c (RSEQ r1 r2) k =
    rder_path_continuations_acc c r1 (rsimp4_SEQ_atom r2 k) \<union>
    (if rnullable r1 then rder_path_continuations_acc c r2 k else {})"
| "rder_path_continuations_acc c (RSTAR r) k =
    rder_path_continuations_acc c r (rsimp4_SEQ_atom (RSTAR r) k)"
| "rder_path_continuations_acc c (RNTIMES r n) k =
    (if n = 0 then {} else
      rder_path_continuations_acc c r (rsimp4_SEQ_atom (RNTIMES r (n - 1)) k))"
| "rder_path_continuations_acc c (RBACKREF4 r1 r2 r3 r4 cs) k =
    rder_path_continuations_acc c r1 k \<union> rder_path_continuations_acc c r2 k \<union>
    rder_path_continuations_acc c r3 k \<union> rder_path_continuations_acc c r4 k"
| "rder_path_continuations_acc c (RHALF r cs rep) k =
    rder_path_continuations_acc c r k"
| "rder_path_continuations_acc c (RRESIDUE cs rep) k = {}"

definition rder_path_continuations :: "char \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "rder_path_continuations c r = rder_path_continuations_acc c r RONE"

lemma rder_path_continuations_acc_subset:
  "rder_path_continuations_acc c r k \<subseteq> rpath_continuations_acc r k"
proof (induct r arbitrary: k)
  case (RBACKREF4 r1 r2 r3 r4 cs)
  show ?case
  proof
    fix x
    assume "x \<in> rder_path_continuations_acc c (RBACKREF4 r1 r2 r3 r4 cs) k"
    then consider
        "x \<in> rder_path_continuations_acc c r1 k"
      | "x \<in> rder_path_continuations_acc c r2 k"
      | "x \<in> rder_path_continuations_acc c r3 k"
      | "x \<in> rder_path_continuations_acc c r4 k"
      by auto
    then show "x \<in> rpath_continuations_acc (RBACKREF4 r1 r2 r3 r4 cs) k"
    proof cases
      case 1
      then have "x \<in> rpath_continuations_acc r1 k"
        using RBACKREF4.hyps(1) by auto
      then show ?thesis by auto
    next
      case 2
      then have "x \<in> rpath_continuations_acc r2 k"
        using RBACKREF4.hyps(2) by auto
      then show ?thesis by auto
    next
      case 3
      then have "x \<in> rpath_continuations_acc r3 k"
        using RBACKREF4.hyps(3) by auto
      then show ?thesis by auto
    next
      case 4
      then have "x \<in> rpath_continuations_acc r4 k"
        using RBACKREF4.hyps(4) by auto
      then show ?thesis by auto
    qed
  qed
qed auto

lemma rder_path_continuations_subset:
  "rder_path_continuations c r \<subseteq> rpath_continuations r"
  unfolding rder_path_continuations_def rpath_continuations_def
  by (rule rder_path_continuations_acc_subset)

lemma rder_path_continuations_universe_subset:
  "rder_path_continuations c r \<subseteq> partial_derivative_path_universe r"
  using rder_path_continuations_subset
    partial_derivative_path_universe_path_continuation
  by blast

lemma rpder_list_path_continuations_acc_subset:
  assumes "legacy_rrexp r"
  shows "set (map (\<lambda>p. rsimp4_SEQ_atom p k) (rpder_list c r)) \<subseteq>
    rder_path_continuations_acc c r k"
  using assms
proof (induct r arbitrary: k)
  case RZERO
  then show ?case by simp
next
  case RONE
  then show ?case by simp
next
  case (RCHAR d)
  then show ?case by simp
next
  case (RALTS rs)
  show ?case
  proof
    fix x
    assume x: "x \<in> set (map (\<lambda>p. rsimp4_SEQ_atom p k)
      (rpder_list c (RALTS rs)))"
    then obtain r p where r:
        "r \<in> set rs"
        "p \<in> set (rpder_list c r)"
        "x = rsimp4_SEQ_atom p k"
      by auto
    have legacy: "legacy_rrexp r"
      using RALTS.prems r(1) by auto
    have subset: "set (map (\<lambda>p. rsimp4_SEQ_atom p k) (rpder_list c r)) \<subseteq>
      rder_path_continuations_acc c r k"
      by (rule RALTS.hyps[OF r(1) legacy])
    have "x \<in> rder_path_continuations_acc c r k"
      using subset r by auto
    then show "x \<in> rder_path_continuations_acc c (RALTS rs) k"
      using r(1) by auto
  qed
next
  case (RSEQ r1 r2)
  have left: "set (map (\<lambda>p. rsimp4_SEQ_atom p (rsimp4_SEQ_atom r2 k))
      (rpder_list c r1)) \<subseteq>
    rder_path_continuations_acc c r1 (rsimp4_SEQ_atom r2 k)"
    by (rule RSEQ.hyps(1)) (use RSEQ.prems in simp)
  have right: "set (map (\<lambda>p. rsimp4_SEQ_atom p k) (rpder_list c r2)) \<subseteq>
    rder_path_continuations_acc c r2 k"
    by (rule RSEQ.hyps(2)) (use RSEQ.prems in simp)
  show ?case
    using left right by (auto simp add: rsimp4_SEQ_atom_assoc)
next
  case (RSTAR r)
  have inner: "set (map (\<lambda>p. rsimp4_SEQ_atom p
      (rsimp4_SEQ_atom (RSTAR r) k)) (rpder_list c r)) \<subseteq>
    rder_path_continuations_acc c r (rsimp4_SEQ_atom (RSTAR r) k)"
    by (rule RSTAR.hyps) (use RSTAR.prems in simp)
  then show ?case
    by (auto simp add: rsimp4_SEQ_atom_assoc)
next
  case (RNTIMES r n)
  then show ?case
  proof (cases n)
    case 0
    then show ?thesis by simp
  next
    case (Suc m)
    have inner: "set (map (\<lambda>p. rsimp4_SEQ_atom p
        (rsimp4_SEQ_atom (RNTIMES r m) k)) (rpder_list c r)) \<subseteq>
      rder_path_continuations_acc c r (rsimp4_SEQ_atom (RNTIMES r m) k)"
      by (rule RNTIMES.hyps) (use RNTIMES.prems in simp)
    then show ?thesis
      using Suc by (auto simp add: rsimp4_SEQ_atom_assoc)
  qed
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  then show ?case by simp
next
  case (RHALF r cs rep)
  then show ?case by simp
next
  case (RRESIDUE cs rep)
  then show ?case by simp
qed

lemma rpder_list_path_universe_subset:
  assumes "legacy_rrexp r"
  shows "set (map (\<lambda>p. rsimp4_SEQ_atom p RONE) (rpder_list c r)) \<subseteq>
    partial_derivative_path_universe r"
proof -
  have "set (map (\<lambda>p. rsimp4_SEQ_atom p RONE) (rpder_list c r)) \<subseteq>
    rder_path_continuations c r"
    unfolding rder_path_continuations_def
    by (rule rpder_list_path_continuations_acc_subset[OF assms])
  then show ?thesis
    using rder_path_continuations_universe_subset[of c r] by auto
qed

lemma rpder_norm_list_path_universe_subset:
  assumes "legacy_rrexp r"
  shows "set (rpder_norm_list c r) \<subseteq> partial_derivative_path_universe r"
  unfolding rpder_norm_list_def
  by (rule rpder_list_path_universe_subset[OF assms])

lemma rpder_norm_rows_single_path_subterms_subset:
  assumes "legacy_rrexp r"
  shows "set (rpder_norm_rows c [r]) \<subseteq>
    (\<Union>q \<in> partial_derivative_path_universe r. rsubterms q)"
proof -
  have norm_subset: "set (rpder_norm_list c r) \<subseteq>
      partial_derivative_path_universe r"
    by (rule rpder_norm_list_path_universe_subset[OF assms])
  have flat_subset: "set (rflts (rpder_norm_list c r)) \<subseteq>
      (\<Union>q \<in> set (rpder_norm_list c r). rsubterms q)"
    by (rule set_rflts_subset_rsubterms_list)
  have "set (rdistinct (rflts (rpder_norm_list c r)) {}) \<subseteq>
      set (rflts (rpder_norm_list c r))"
    by (rule set_rdistinct_subset) simp
  also have "... \<subseteq>
      (\<Union>q \<in> partial_derivative_path_universe r. rsubterms q)"
    using flat_subset norm_subset by blast
  finally show ?thesis
    by (simp add: rpder_norm_rows_def)
qed

lemma rsizes_rpder_list_RONE_cubic:
  assumes "legacy_rrexp r"
  shows "rsizes (map (\<lambda>p. rsimp4_SEQ_atom p RONE) (rpder_list c r)) \<le>
    2 * (rsize r + 3) ^ 3"
proof -
  let ?rows = "map (\<lambda>p. rsimp4_SEQ_atom p RONE) (rpder_list c r)"
  let ?M = "1 + (rsize r + 2)\<^sup>2"
  have member_bound: "\<And>x. x \<in> set ?rows \<Longrightarrow> rsize x \<le> ?M"
    using rpder_list_path_universe_subset[OF assms]
      partial_derivative_path_universe_member_size_quadratic
    by blast
  have "rsizes ?rows \<le> length ?rows * ?M"
    by (rule rsizes_le_length_times_bound[OF member_bound])
  also have "... \<le> rsize r * ?M"
  proof -
    have "length ?rows \<le> rsize r"
      using length_rpder_list_le_rsize[OF assms] by simp
    then show ?thesis
      by (rule mult_right_mono) simp
  qed
  also have "... \<le> (2 + 2 * rsize r) * ?M"
    by simp
  also have "... \<le> 2 * (rsize r + 3) ^ 3"
    by (rule linear_times_quadratic_cubic_bound)
  finally show ?thesis .
qed

lemma rsizes_rpder_norm_list_cubic:
  assumes "legacy_rrexp r"
  shows "rsizes (rpder_norm_list c r) \<le> 2 * (rsize r + 3) ^ 3"
  unfolding rpder_norm_list_def
  by (rule rsizes_rpder_list_RONE_cubic[OF assms])

lemma rsize_rpd_der_norm_cubic:
  assumes "legacy_rrexp r"
  shows "rsize (rpd_der_norm c r) \<le> Suc (2 * (rsize r + 3) ^ 3)"
proof -
  have "rsize (rpd_der_norm c r) \<le> Suc (rsizes (rpder_norm_list c r))"
    by (rule rsize_rpd_der_norm_le_rsizes)
  also have "... \<le> Suc (2 * (rsize r + 3) ^ 3)"
    using rsizes_rpder_norm_list_cubic[OF assms] by simp
  finally show ?thesis .
qed

fun rpath_frontier_acc :: "rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "rpath_frontier_acc RZERO k = {}"
| "rpath_frontier_acc RONE k = {}"
| "rpath_frontier_acc (RCHAR c) k = rfrontier (rsimp4_SEQ RONE k)"
| "rpath_frontier_acc (RALTS rs) k =
    (\<Union> (set (map (\<lambda>r. rpath_frontier_acc r k) rs)))"
| "rpath_frontier_acc (RSEQ r1 r2) k =
    rpath_frontier_acc r1 (rsimp4_SEQ (rsimp4 r2) k) \<union>
    rpath_frontier_acc r2 k"
| "rpath_frontier_acc (RSTAR r) k =
    rpath_frontier_acc r (rsimp4_SEQ (RSTAR r) k)"
| "rpath_frontier_acc (RNTIMES r n) k =
    (if n = 0 then {} else
      rpath_frontier_acc r (rsimp4_SEQ (RNTIMES r (n - 1)) k))"
| "rpath_frontier_acc (RBACKREF4 r1 r2 r3 r4 cs) k =
    rpath_frontier_acc r1 k \<union> rpath_frontier_acc r2 k \<union>
    rpath_frontier_acc r3 k \<union> rpath_frontier_acc r4 k"
| "rpath_frontier_acc (RHALF r cs rep) k = rpath_frontier_acc r k"
| "rpath_frontier_acc (RRESIDUE cs rep) k = {}"

definition rpath_frontiers :: "rrexp \<Rightarrow> rrexp set" where
  "rpath_frontiers r = rpath_frontier_acc r RONE"

definition partial_derivative_path_frontier_universe :: "rrexp \<Rightarrow> rrexp set" where
  "partial_derivative_path_frontier_universe r =
    insert RZERO (insert RONE (rsubterms r \<union> rpath_frontiers r))"

lemma finite_rpath_frontier_acc [simp]:
  "finite (rpath_frontier_acc r k)"
  by (induct r arbitrary: k) auto

lemma finite_rpath_frontiers [simp]:
  "finite (rpath_frontiers r)"
  by (simp add: rpath_frontiers_def)

lemma finite_partial_derivative_path_frontier_universe [simp]:
  "finite (partial_derivative_path_frontier_universe r)"
  by (simp add: partial_derivative_path_frontier_universe_def)

lemma partial_derivative_path_frontier_universe_card_le:
  "card (partial_derivative_path_frontier_universe r) \<le>
    2 + rsize r + card (rpath_frontiers r)"
proof -
  have "card (partial_derivative_path_frontier_universe r) \<le>
    2 + card (rsubterms r) + card (rpath_frontiers r)"
    unfolding partial_derivative_path_frontier_universe_def
    by (rule card_insert2_Un_le) simp_all
  also have "... \<le> 2 + rsize r + card (rpath_frontiers r)"
    using card_rsubterms_le_rsize[of r] by linarith
  finally show ?thesis .
qed

lemma partial_derivative_path_frontier_universe_alt_child_mono:
  assumes "r \<in> set rs"
  shows "partial_derivative_path_frontier_universe r \<subseteq>
    partial_derivative_path_frontier_universe (RALTS rs)"
  using assms
  unfolding partial_derivative_path_frontier_universe_def
    rpath_frontiers_def
  by auto

lemma rfrontier_rsimp4_rder_RZERO_path_frontier [simp]:
  "rfrontier (rsimp4 (rder c RZERO)) \<subseteq>
    partial_derivative_path_frontier_universe RZERO"
  by (simp add: partial_derivative_path_frontier_universe_def)

lemma rfrontier_rsimp4_rder_RONE_path_frontier [simp]:
  "rfrontier (rsimp4 (rder c RONE)) \<subseteq>
    partial_derivative_path_frontier_universe RONE"
  by (simp add: partial_derivative_path_frontier_universe_def)

lemma rfrontier_rsimp4_rder_RCHAR_path_frontier [simp]:
  "rfrontier (rsimp4 (rder c (RCHAR d))) \<subseteq>
    partial_derivative_path_frontier_universe (RCHAR d)"
  by (cases "c = d") (simp_all add: partial_derivative_path_frontier_universe_def)

lemma rfrontier_rsimp4_rder_RALTS_path_frontier:
  assumes step: "\<And>r. r \<in> set rs \<Longrightarrow>
    rfrontier (rsimp4 (rder c r)) \<subseteq>
      partial_derivative_path_frontier_universe r"
  shows "rfrontier (rsimp4 (rder c (RALTS rs))) \<subseteq>
    partial_derivative_path_frontier_universe (RALTS rs)"
proof
  fix q
  assume q: "q \<in> rfrontier (rsimp4 (rder c (RALTS rs)))"
  have q_norm: "q \<in>
    rfrontier
      (rsimp_ALTs (rdistinct (rflts (map (rsimp4 \<circ> rder c) rs)) {}))"
    using q by simp
  then obtain x where x:
      "x \<in> set (map (rsimp4 \<circ> rder c) rs)"
      "q \<in> rfrontier x"
    by (rule rfrontier_normalize_memberE)
  then obtain r where r: "r \<in> set rs" "x = rsimp4 (rder c r)"
    by (auto simp add: comp_def)
  have "q \<in> partial_derivative_path_frontier_universe r"
    using step[OF r(1)] x r by blast
  moreover have "partial_derivative_path_frontier_universe r \<subseteq>
    partial_derivative_path_frontier_universe (RALTS rs)"
    by (rule partial_derivative_path_frontier_universe_alt_child_mono[OF r(1)])
  ultimately show "q \<in> partial_derivative_path_frontier_universe (RALTS rs)"
    by blast
qed

lemma rfrontier_rsimp4_SEQ_rder_RZERO_path_acc [simp]:
  "rfrontier (rsimp4_SEQ (rsimp4 (rder c RZERO)) k) \<subseteq>
    insert RZERO (rpath_frontier_acc RZERO k)"
  by (simp add: rsimp4_SEQ_def)

lemma rfrontier_rsimp4_SEQ_rder_RONE_path_acc [simp]:
  "rfrontier (rsimp4_SEQ (rsimp4 (rder c RONE)) k) \<subseteq>
    insert RZERO (rpath_frontier_acc RONE k)"
  by (simp add: rsimp4_SEQ_def)

lemma rfrontier_rsimp4_SEQ_rder_RCHAR_path_acc [simp]:
  "rfrontier (rsimp4_SEQ (rsimp4 (rder c (RCHAR d))) k) \<subseteq>
    insert RZERO (rpath_frontier_acc (RCHAR d) k)"
proof (cases "c = d")
  case True
  then show ?thesis by auto
next
  case False
  then show ?thesis
    by (simp add: rsimp4_SEQ_def)
qed

lemma rfrontier_rsimp4_SEQ_rder_RALTS_path_acc:
  assumes step: "\<And>r. r \<in> set rs \<Longrightarrow>
    rfrontier (rsimp4_SEQ (rsimp4 (rder c r)) k) \<subseteq>
      insert RZERO (rpath_frontier_acc r k)"
  shows "rfrontier (rsimp4_SEQ (rsimp4 (rder c (RALTS rs))) k) \<subseteq>
    insert RZERO (rpath_frontier_acc (RALTS rs) k)"
proof -
  let ?xs = "rdistinct (rflts (map (rsimp4 \<circ> rder c) rs)) {}"
  have mapped_good: "\<forall>r \<in> set (map (rsimp4 \<circ> rder c) rs).
      good r \<or> r = RZERO"
    using good_rsimp4 by auto
  have xs_good: "\<forall>x \<in> set ?xs. good x \<and> nonalt x"
    using flts3_good_nonalt[OF mapped_good]
    by (simp add: rdistinct_set_equality)
  have elem_subset: "\<And>x. x \<in> set ?xs \<Longrightarrow>
    rfrontier (rsimp4_SEQ x k) \<subseteq>
      insert RZERO (rpath_frontier_acc (RALTS rs) k)"
  proof -
    fix x
    assume x: "x \<in> set ?xs"
    have x_nonalt: "nonalt x"
      using xs_good x by blast
    have x_nonzero: "x \<noteq> RZERO"
      using xs_good x good_not_RZERO by blast
    have x_front_xs: "x \<in> rfrontiers ?xs"
      using x rfrontier_nonzero_nonalt_self[OF x_nonzero x_nonalt]
        rfrontiers_member_iff by blast
    have x_front_children: "x \<in> rfrontiers (map (rsimp4 \<circ> rder c) rs)"
      using x_front_xs by simp
    then obtain y where y:
        "y \<in> set (map (rsimp4 \<circ> rder c) rs)"
        "x \<in> rfrontier y"
      using rfrontiers_member_iff by blast
    then obtain r where r: "r \<in> set rs" "y = rsimp4 (rder c r)"
      by (auto simp add: comp_def)
    have y_good: "good y \<or> y = RZERO"
      using r(2) good_rsimp4 by simp
    have "rfrontier (rsimp4_SEQ x k) \<subseteq>
      rfrontier (rsimp4_SEQ y k)"
      by (rule rfrontier_good_member_SEQ_subset[OF y_good y(2)])
    also have "... \<subseteq> insert RZERO (rpath_frontier_acc r k)"
      using step[OF r(1)] r(2) by simp
    also have "... \<subseteq> insert RZERO (rpath_frontier_acc (RALTS rs) k)"
      using r(1) by auto
    finally show "rfrontier (rsimp4_SEQ x k) \<subseteq>
      insert RZERO (rpath_frontier_acc (RALTS rs) k)" .
  qed
  have "rfrontier (rsimp4_SEQ (rsimp_ALTs ?xs) k) \<subseteq>
    insert RZERO (rpath_frontier_acc (RALTS rs) k)"
    by (rule rfrontier_rsimp4_SEQ_rsimp_ALTs_nonalt_subset)
      (use elem_subset xs_good in auto)
  then show ?thesis
    by (simp add: comp_def)
qed

lemma left_nested_atom_in_path_frontier_universe:
  assumes "a \<noteq> b"
  shows "RSEQ (RSTAR (RCHAR a)) (RSEQ (RCHAR b) (RCHAR c)) \<in>
    partial_derivative_path_frontier_universe
      (RSEQ (RSEQ (RSTAR (RCHAR a)) (RCHAR b)) (RCHAR c))"
  using assms
  by (simp add: partial_derivative_path_frontier_universe_def
      rpath_frontiers_def rsimp4_SEQ_def)

lemma distributed_suffix_atom_in_path_frontier_universe:
  "RSEQ (RCHAR b) (RCHAR d) \<in>
    partial_derivative_path_frontier_universe
      (RSEQ (RCHAR a) (RSEQ (RALTS [RCHAR b, RCHAR c]) (RCHAR d)))"
  by (simp add: partial_derivative_path_frontier_universe_def
      rpath_frontiers_def rsimp4_SEQ_def)

fun rpath_atom_frontier_acc :: "rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "rpath_atom_frontier_acc RZERO k = {}"
| "rpath_atom_frontier_acc RONE k = {}"
| "rpath_atom_frontier_acc (RCHAR c) k = rfrontier (rsimp4_SEQ RONE k)"
| "rpath_atom_frontier_acc (RALTS rs) k =
    (\<Union> (set (map (\<lambda>r. rpath_atom_frontier_acc r k) rs)))"
| "rpath_atom_frontier_acc (RSEQ r1 r2) k =
    rpath_atom_frontier_acc r1 (rsimp4_SEQ_atom (rsimp4 r2) k) \<union>
    rpath_atom_frontier_acc r2 k"
| "rpath_atom_frontier_acc (RSTAR r) k =
    rpath_atom_frontier_acc r (rsimp4_SEQ_atom (RSTAR r) k)"
| "rpath_atom_frontier_acc (RNTIMES r n) k =
    (if n = 0 then {} else
      rpath_atom_frontier_acc r (rsimp4_SEQ_atom (RNTIMES r (n - 1)) k))"
| "rpath_atom_frontier_acc (RBACKREF4 r1 r2 r3 r4 cs) k =
    rpath_atom_frontier_acc r1 k \<union> rpath_atom_frontier_acc r2 k \<union>
    rpath_atom_frontier_acc r3 k \<union> rpath_atom_frontier_acc r4 k"
| "rpath_atom_frontier_acc (RHALF r cs rep) k = rpath_atom_frontier_acc r k"
| "rpath_atom_frontier_acc (RRESIDUE cs rep) k = {}"

definition rpath_atom_frontiers :: "rrexp \<Rightarrow> rrexp set" where
  "rpath_atom_frontiers r = rpath_atom_frontier_acc r RONE"

definition partial_derivative_path_atom_frontier_universe :: "rrexp \<Rightarrow> rrexp set" where
  "partial_derivative_path_atom_frontier_universe r =
    insert RZERO (insert RONE (rsubterms r \<union> rpath_atom_frontiers r))"

definition rpath_dual_frontier_acc :: "rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "rpath_dual_frontier_acc r k =
    rpath_frontier_acc r k \<union> rpath_atom_frontier_acc r k"

definition rpath_dual_frontiers :: "rrexp \<Rightarrow> rrexp set" where
  "rpath_dual_frontiers r = rpath_dual_frontier_acc r RONE"

definition partial_derivative_path_dual_frontier_universe :: "rrexp \<Rightarrow> rrexp set" where
  "partial_derivative_path_dual_frontier_universe r =
    insert RZERO (insert RONE (rsubterms r \<union> rpath_dual_frontiers r))"

lemma finite_rpath_atom_frontier_acc [simp]:
  "finite (rpath_atom_frontier_acc r k)"
  by (induct r arbitrary: k) auto

lemma finite_rpath_atom_frontiers [simp]:
  "finite (rpath_atom_frontiers r)"
  by (simp add: rpath_atom_frontiers_def)

lemma finite_partial_derivative_path_atom_frontier_universe [simp]:
  "finite (partial_derivative_path_atom_frontier_universe r)"
  by (simp add: partial_derivative_path_atom_frontier_universe_def)

lemma finite_rpath_dual_frontiers [simp]:
  "finite (rpath_dual_frontiers r)"
  by (simp add: rpath_dual_frontiers_def rpath_dual_frontier_acc_def)

lemma finite_partial_derivative_path_dual_frontier_universe [simp]:
  "finite (partial_derivative_path_dual_frontier_universe r)"
  by (simp add: partial_derivative_path_dual_frontier_universe_def)

lemma partial_derivative_path_atom_frontier_universe_card_le:
  "card (partial_derivative_path_atom_frontier_universe r) \<le>
    2 + rsize r + card (rpath_atom_frontiers r)"
proof -
  have "card (partial_derivative_path_atom_frontier_universe r) \<le>
    2 + card (rsubterms r) + card (rpath_atom_frontiers r)"
    unfolding partial_derivative_path_atom_frontier_universe_def
    by (rule card_insert2_Un_le) simp_all
  also have "... \<le> 2 + rsize r + card (rpath_atom_frontiers r)"
    using card_rsubterms_le_rsize[of r] by linarith
  finally show ?thesis .
qed

lemma partial_derivative_path_dual_frontier_universe_card_le:
  "card (partial_derivative_path_dual_frontier_universe r) \<le>
    2 + rsize r + card (rpath_frontiers r) + card (rpath_atom_frontiers r)"
proof -
  have "card (partial_derivative_path_dual_frontier_universe r) \<le>
    2 + card (rsubterms r) + card (rpath_dual_frontiers r)"
    unfolding partial_derivative_path_dual_frontier_universe_def
    by (rule card_insert2_Un_le) simp_all
  also have "... \<le>
    2 + rsize r + card (rpath_frontiers r) + card (rpath_atom_frontiers r)"
  proof -
    have subterms: "card (rsubterms r) \<le> rsize r"
      by (rule card_rsubterms_le_rsize)
    have dual: "card (rpath_dual_frontiers r) \<le>
      card (rpath_frontiers r) + card (rpath_atom_frontiers r)"
      unfolding rpath_dual_frontiers_def rpath_dual_frontier_acc_def
        rpath_frontiers_def rpath_atom_frontiers_def
      by (rule card_Un_le)
    show ?thesis
      using subterms dual by linarith
  qed
  finally show ?thesis .
qed

lemma rpath_frontier_acc_subset_dual:
  "rpath_frontier_acc r k \<subseteq> rpath_dual_frontier_acc r k"
  by (simp add: rpath_dual_frontier_acc_def)

lemma rpath_atom_frontier_acc_subset_dual:
  "rpath_atom_frontier_acc r k \<subseteq> rpath_dual_frontier_acc r k"
  by (simp add: rpath_dual_frontier_acc_def)

lemma partial_derivative_path_frontier_universe_subset_dual:
  "partial_derivative_path_frontier_universe r \<subseteq>
    partial_derivative_path_dual_frontier_universe r"
  unfolding partial_derivative_path_frontier_universe_def
    partial_derivative_path_dual_frontier_universe_def
    rpath_dual_frontiers_def rpath_dual_frontier_acc_def
    rpath_frontiers_def rpath_atom_frontiers_def
  by auto

lemma partial_derivative_path_atom_frontier_universe_subset_dual:
  "partial_derivative_path_atom_frontier_universe r \<subseteq>
    partial_derivative_path_dual_frontier_universe r"
  unfolding partial_derivative_path_atom_frontier_universe_def
    partial_derivative_path_dual_frontier_universe_def
    rpath_dual_frontiers_def rpath_dual_frontier_acc_def
    rpath_frontiers_def rpath_atom_frontiers_def
  by auto

lemma partial_derivative_path_atom_frontier_universe_alt_child_mono:
  assumes "r \<in> set rs"
  shows "partial_derivative_path_atom_frontier_universe r \<subseteq>
    partial_derivative_path_atom_frontier_universe (RALTS rs)"
  using assms
  unfolding partial_derivative_path_atom_frontier_universe_def
    rpath_atom_frontiers_def
  by auto

lemma partial_derivative_path_dual_frontier_universe_alt_child_mono:
  assumes "r \<in> set rs"
  shows "partial_derivative_path_dual_frontier_universe r \<subseteq>
    partial_derivative_path_dual_frontier_universe (RALTS rs)"
  using assms
  unfolding partial_derivative_path_dual_frontier_universe_def
    rpath_dual_frontiers_def rpath_dual_frontier_acc_def
    rpath_frontiers_def rpath_atom_frontiers_def
  by auto

lemma rfrontier_rsimp4_rder_RZERO_path_atom_frontier [simp]:
  "rfrontier (rsimp4 (rder c RZERO)) \<subseteq>
    partial_derivative_path_atom_frontier_universe RZERO"
  by (simp add: partial_derivative_path_atom_frontier_universe_def)

lemma rfrontier_rsimp4_rder_RONE_path_atom_frontier [simp]:
  "rfrontier (rsimp4 (rder c RONE)) \<subseteq>
    partial_derivative_path_atom_frontier_universe RONE"
  by (simp add: partial_derivative_path_atom_frontier_universe_def)

lemma rfrontier_rsimp4_rder_RCHAR_path_atom_frontier [simp]:
  "rfrontier (rsimp4 (rder c (RCHAR d))) \<subseteq>
    partial_derivative_path_atom_frontier_universe (RCHAR d)"
  by (cases "c = d") (simp_all add: partial_derivative_path_atom_frontier_universe_def)

lemma rfrontier_rsimp4_rder_RALTS_path_atom_frontier:
  assumes step: "\<And>r. r \<in> set rs \<Longrightarrow>
    rfrontier (rsimp4 (rder c r)) \<subseteq>
      partial_derivative_path_atom_frontier_universe r"
  shows "rfrontier (rsimp4 (rder c (RALTS rs))) \<subseteq>
    partial_derivative_path_atom_frontier_universe (RALTS rs)"
proof
  fix q
  assume q: "q \<in> rfrontier (rsimp4 (rder c (RALTS rs)))"
  have q_norm: "q \<in>
    rfrontier
      (rsimp_ALTs (rdistinct (rflts (map (rsimp4 \<circ> rder c) rs)) {}))"
    using q by simp
  then obtain x where x:
      "x \<in> set (map (rsimp4 \<circ> rder c) rs)"
      "q \<in> rfrontier x"
    by (rule rfrontier_normalize_memberE)
  then obtain r where r: "r \<in> set rs" "x = rsimp4 (rder c r)"
    by (auto simp add: comp_def)
  have "q \<in> partial_derivative_path_atom_frontier_universe r"
    using step[OF r(1)] x r by blast
  moreover have "partial_derivative_path_atom_frontier_universe r \<subseteq>
    partial_derivative_path_atom_frontier_universe (RALTS rs)"
    by (rule partial_derivative_path_atom_frontier_universe_alt_child_mono[OF r(1)])
  ultimately show "q \<in> partial_derivative_path_atom_frontier_universe (RALTS rs)"
    by blast
qed

lemma rfrontier_rsimp4_rder_RZERO_path_dual_frontier [simp]:
  "rfrontier (rsimp4 (rder c RZERO)) \<subseteq>
    partial_derivative_path_dual_frontier_universe RZERO"
  by (simp add: partial_derivative_path_dual_frontier_universe_def)

lemma rfrontier_rsimp4_rder_RONE_path_dual_frontier [simp]:
  "rfrontier (rsimp4 (rder c RONE)) \<subseteq>
    partial_derivative_path_dual_frontier_universe RONE"
  by (simp add: partial_derivative_path_dual_frontier_universe_def)

lemma rfrontier_rsimp4_rder_RCHAR_path_dual_frontier [simp]:
  "rfrontier (rsimp4 (rder c (RCHAR d))) \<subseteq>
    partial_derivative_path_dual_frontier_universe (RCHAR d)"
  by (cases "c = d") (simp_all add: partial_derivative_path_dual_frontier_universe_def)

lemma rfrontier_rsimp4_rder_RALTS_path_dual_frontier:
  assumes step: "\<And>r. r \<in> set rs \<Longrightarrow>
    rfrontier (rsimp4 (rder c r)) \<subseteq>
      partial_derivative_path_dual_frontier_universe r"
  shows "rfrontier (rsimp4 (rder c (RALTS rs))) \<subseteq>
    partial_derivative_path_dual_frontier_universe (RALTS rs)"
proof
  fix q
  assume q: "q \<in> rfrontier (rsimp4 (rder c (RALTS rs)))"
  have q_norm: "q \<in>
    rfrontier
      (rsimp_ALTs (rdistinct (rflts (map (rsimp4 \<circ> rder c) rs)) {}))"
    using q by simp
  then obtain x where x:
      "x \<in> set (map (rsimp4 \<circ> rder c) rs)"
      "q \<in> rfrontier x"
    by (rule rfrontier_normalize_memberE)
  then obtain r where r: "r \<in> set rs" "x = rsimp4 (rder c r)"
    by (auto simp add: comp_def)
  have "q \<in> partial_derivative_path_dual_frontier_universe r"
    using step[OF r(1)] x r by blast
  moreover have "partial_derivative_path_dual_frontier_universe r \<subseteq>
    partial_derivative_path_dual_frontier_universe (RALTS rs)"
    by (rule partial_derivative_path_dual_frontier_universe_alt_child_mono[OF r(1)])
  ultimately show "q \<in> partial_derivative_path_dual_frontier_universe (RALTS rs)"
    by blast
qed

lemma rfrontier_rsimp5_rder_RZERO_path_dual_frontier [simp]:
  "rfrontier (rsimp5 (rder c RZERO)) \<subseteq>
    partial_derivative_path_dual_frontier_universe RZERO"
  by (simp add: partial_derivative_path_dual_frontier_universe_def)

lemma rfrontier_rsimp5_rder_RONE_path_dual_frontier [simp]:
  "rfrontier (rsimp5 (rder c RONE)) \<subseteq>
    partial_derivative_path_dual_frontier_universe RONE"
  by (simp add: partial_derivative_path_dual_frontier_universe_def)

lemma rfrontier_rsimp5_rder_RCHAR_path_dual_frontier [simp]:
  "rfrontier (rsimp5 (rder c (RCHAR d))) \<subseteq>
    partial_derivative_path_dual_frontier_universe (RCHAR d)"
  by (cases "c = d") (simp_all add: partial_derivative_path_dual_frontier_universe_def)

lemma rfrontier_rsimp5_rder_RALTS_path_dual_frontier:
  assumes step: "\<And>r. r \<in> set rs \<Longrightarrow>
    rfrontier (rsimp5 (rder c r)) \<subseteq>
      partial_derivative_path_dual_frontier_universe r"
  shows "rfrontier (rsimp5 (rder c (RALTS rs))) \<subseteq>
    partial_derivative_path_dual_frontier_universe (RALTS rs)"
proof
  fix q
  assume q: "q \<in> rfrontier (rsimp5 (rder c (RALTS rs)))"
  have q_norm: "q \<in>
    rfrontier
      (rsimp_ALTs (rdistinct (rflts (map (rsimp5 \<circ> rder c) rs)) {}))"
    using q by (simp add: comp_def)
  then obtain x where x:
      "x \<in> set (map (rsimp5 \<circ> rder c) rs)"
      "q \<in> rfrontier x"
    by (rule rfrontier_normalize_memberE)
  then obtain r where r: "r \<in> set rs" "x = rsimp5 (rder c r)"
    by (auto simp add: comp_def)
  have "q \<in> partial_derivative_path_dual_frontier_universe r"
    using step[OF r(1)] x r by blast
  moreover have "partial_derivative_path_dual_frontier_universe r \<subseteq>
    partial_derivative_path_dual_frontier_universe (RALTS rs)"
    by (rule partial_derivative_path_dual_frontier_universe_alt_child_mono[OF r(1)])
  ultimately show "q \<in> partial_derivative_path_dual_frontier_universe (RALTS rs)"
    by blast
qed

lemma rfrontier_rsimp4_SEQ_rder_RZERO_path_atom_acc [simp]:
  "rfrontier (rsimp4_SEQ (rsimp4 (rder c RZERO)) k) \<subseteq>
    insert RZERO (rpath_atom_frontier_acc RZERO k)"
  by (simp add: rsimp4_SEQ_def)

lemma rfrontier_rsimp4_SEQ_rder_RONE_path_atom_acc [simp]:
  "rfrontier (rsimp4_SEQ (rsimp4 (rder c RONE)) k) \<subseteq>
    insert RZERO (rpath_atom_frontier_acc RONE k)"
  by (simp add: rsimp4_SEQ_def)

lemma rfrontier_rsimp4_SEQ_rder_RCHAR_path_atom_acc [simp]:
  "rfrontier (rsimp4_SEQ (rsimp4 (rder c (RCHAR d))) k) \<subseteq>
    insert RZERO (rpath_atom_frontier_acc (RCHAR d) k)"
proof (cases "c = d")
  case True
  then show ?thesis by auto
next
  case False
  then show ?thesis
    by (simp add: rsimp4_SEQ_def)
qed

lemma rfrontier_rsimp4_SEQ_rder_RALTS_path_atom_acc:
  assumes step: "\<And>r. r \<in> set rs \<Longrightarrow>
    rfrontier (rsimp4_SEQ (rsimp4 (rder c r)) k) \<subseteq>
      insert RZERO (rpath_atom_frontier_acc r k)"
  shows "rfrontier (rsimp4_SEQ (rsimp4 (rder c (RALTS rs))) k) \<subseteq>
    insert RZERO (rpath_atom_frontier_acc (RALTS rs) k)"
proof -
  let ?xs = "rdistinct (rflts (map (rsimp4 \<circ> rder c) rs)) {}"
  have mapped_good: "\<forall>r \<in> set (map (rsimp4 \<circ> rder c) rs).
      good r \<or> r = RZERO"
    using good_rsimp4 by auto
  have xs_good: "\<forall>x \<in> set ?xs. good x \<and> nonalt x"
    using flts3_good_nonalt[OF mapped_good]
    by (simp add: rdistinct_set_equality)
  have elem_subset: "\<And>x. x \<in> set ?xs \<Longrightarrow>
    rfrontier (rsimp4_SEQ x k) \<subseteq>
      insert RZERO (rpath_atom_frontier_acc (RALTS rs) k)"
  proof -
    fix x
    assume x: "x \<in> set ?xs"
    have x_nonalt: "nonalt x"
      using xs_good x by blast
    have x_nonzero: "x \<noteq> RZERO"
      using xs_good x good_not_RZERO by blast
    have x_front_xs: "x \<in> rfrontiers ?xs"
      using x rfrontier_nonzero_nonalt_self[OF x_nonzero x_nonalt]
        rfrontiers_member_iff by blast
    have x_front_children: "x \<in> rfrontiers (map (rsimp4 \<circ> rder c) rs)"
      using x_front_xs by simp
    then obtain y where y:
        "y \<in> set (map (rsimp4 \<circ> rder c) rs)"
        "x \<in> rfrontier y"
      using rfrontiers_member_iff by blast
    then obtain r where r: "r \<in> set rs" "y = rsimp4 (rder c r)"
      by (auto simp add: comp_def)
    have y_good: "good y \<or> y = RZERO"
      using r(2) good_rsimp4 by simp
    have "rfrontier (rsimp4_SEQ x k) \<subseteq>
      rfrontier (rsimp4_SEQ y k)"
      by (rule rfrontier_good_member_SEQ_subset[OF y_good y(2)])
    also have "... \<subseteq> insert RZERO (rpath_atom_frontier_acc r k)"
      using step[OF r(1)] r(2) by simp
    also have "... \<subseteq> insert RZERO (rpath_atom_frontier_acc (RALTS rs) k)"
      using r(1) by auto
    finally show "rfrontier (rsimp4_SEQ x k) \<subseteq>
      insert RZERO (rpath_atom_frontier_acc (RALTS rs) k)" .
  qed
  have "rfrontier (rsimp4_SEQ (rsimp_ALTs ?xs) k) \<subseteq>
    insert RZERO (rpath_atom_frontier_acc (RALTS rs) k)"
    by (rule rfrontier_rsimp4_SEQ_rsimp_ALTs_nonalt_subset)
      (use elem_subset xs_good in auto)
  then show ?thesis
    by (simp add: comp_def)
qed

lemma rfrontier_rsimp4_SEQ_rder_RZERO_path_dual_acc [simp]:
  "rfrontier (rsimp4_SEQ (rsimp4 (rder c RZERO)) k) \<subseteq>
    insert RZERO (rpath_dual_frontier_acc RZERO k)"
  using rfrontier_rsimp4_SEQ_rder_RZERO_path_acc[of c k]
    rpath_frontier_acc_subset_dual[of RZERO k]
  by blast

lemma rfrontier_rsimp4_SEQ_rder_RONE_path_dual_acc [simp]:
  "rfrontier (rsimp4_SEQ (rsimp4 (rder c RONE)) k) \<subseteq>
    insert RZERO (rpath_dual_frontier_acc RONE k)"
  using rfrontier_rsimp4_SEQ_rder_RONE_path_acc[of c k]
    rpath_frontier_acc_subset_dual[of RONE k]
  by blast

lemma rfrontier_rsimp4_SEQ_rder_RCHAR_path_dual_acc [simp]:
  "rfrontier (rsimp4_SEQ (rsimp4 (rder c (RCHAR d))) k) \<subseteq>
    insert RZERO (rpath_dual_frontier_acc (RCHAR d) k)"
  using rfrontier_rsimp4_SEQ_rder_RCHAR_path_acc[of c d k]
    rpath_frontier_acc_subset_dual[of "RCHAR d" k]
  by blast

lemma rfrontier_rsimp4_SEQ_rder_RALTS_path_dual_acc:
  assumes step: "\<And>r. r \<in> set rs \<Longrightarrow>
    rfrontier (rsimp4_SEQ (rsimp4 (rder c r)) k) \<subseteq>
      insert RZERO (rpath_dual_frontier_acc r k)"
  shows "rfrontier (rsimp4_SEQ (rsimp4 (rder c (RALTS rs))) k) \<subseteq>
    insert RZERO (rpath_dual_frontier_acc (RALTS rs) k)"
proof -
  let ?xs = "rdistinct (rflts (map (rsimp4 \<circ> rder c) rs)) {}"
  have mapped_good: "\<forall>r \<in> set (map (rsimp4 \<circ> rder c) rs).
      good r \<or> r = RZERO"
    using good_rsimp4 by auto
  have xs_good: "\<forall>x \<in> set ?xs. good x \<and> nonalt x"
    using flts3_good_nonalt[OF mapped_good]
    by (simp add: rdistinct_set_equality)
  have elem_subset: "\<And>x. x \<in> set ?xs \<Longrightarrow>
    rfrontier (rsimp4_SEQ x k) \<subseteq>
      insert RZERO (rpath_dual_frontier_acc (RALTS rs) k)"
  proof -
    fix x
    assume x: "x \<in> set ?xs"
    have x_nonalt: "nonalt x"
      using xs_good x by blast
    have x_nonzero: "x \<noteq> RZERO"
      using xs_good x good_not_RZERO by blast
    have x_front_xs: "x \<in> rfrontiers ?xs"
      using x rfrontier_nonzero_nonalt_self[OF x_nonzero x_nonalt]
        rfrontiers_member_iff by blast
    have x_front_children: "x \<in> rfrontiers (map (rsimp4 \<circ> rder c) rs)"
      using x_front_xs by simp
    then obtain y where y:
        "y \<in> set (map (rsimp4 \<circ> rder c) rs)"
        "x \<in> rfrontier y"
      using rfrontiers_member_iff by blast
    then obtain r where r: "r \<in> set rs" "y = rsimp4 (rder c r)"
      by (auto simp add: comp_def)
    have y_good: "good y \<or> y = RZERO"
      using r(2) good_rsimp4 by simp
    have "rfrontier (rsimp4_SEQ x k) \<subseteq>
      rfrontier (rsimp4_SEQ y k)"
      by (rule rfrontier_good_member_SEQ_subset[OF y_good y(2)])
    also have "... \<subseteq> insert RZERO (rpath_dual_frontier_acc r k)"
      using step[OF r(1)] r(2) by simp
    also have "... \<subseteq> insert RZERO (rpath_dual_frontier_acc (RALTS rs) k)"
      using r(1) by (auto simp add: rpath_dual_frontier_acc_def)
    finally show "rfrontier (rsimp4_SEQ x k) \<subseteq>
      insert RZERO (rpath_dual_frontier_acc (RALTS rs) k)" .
  qed
  have "rfrontier (rsimp4_SEQ (rsimp_ALTs ?xs) k) \<subseteq>
    insert RZERO (rpath_dual_frontier_acc (RALTS rs) k)"
    by (rule rfrontier_rsimp4_SEQ_rsimp_ALTs_nonalt_subset)
      (use elem_subset xs_good in auto)
  then show ?thesis
    by (simp add: comp_def)
qed

lemma distributed_suffix_atom_in_path_atom_frontier_universe:
  "RSEQ (RCHAR b) (RCHAR d) \<in>
    partial_derivative_path_atom_frontier_universe
      (RSEQ (RCHAR a) (RSEQ (RALTS [RCHAR b, RCHAR c]) (RCHAR d)))"
  by (simp add: partial_derivative_path_atom_frontier_universe_def
      rpath_atom_frontiers_def rsimp4_SEQ_def)

lemma distributed_suffix_atom_in_path_dual_frontier_universe:
  "RSEQ (RCHAR b) (RCHAR d) \<in>
    partial_derivative_path_dual_frontier_universe
      (RSEQ (RCHAR a) (RSEQ (RALTS [RCHAR b, RCHAR c]) (RCHAR d)))"
  by (simp add: partial_derivative_path_dual_frontier_universe_def
      rpath_dual_frontiers_def rpath_dual_frontier_acc_def
      rpath_frontiers_def rpath_atom_frontiers_def rsimp4_SEQ_def)

lemma rsimp4_derivative_keeps_middle_alt_opaque:
  assumes "c \<noteq> d"
  shows "RSEQ (RCHAR b) (RSEQ (RALTS [RCHAR c, RCHAR d]) (RCHAR e)) \<in>
    rfrontier
      (rsimp4
        (rder a
          (RSEQ
            (RSEQ (RSEQ (RCHAR a) (RCHAR b)) (RALTS [RCHAR c, RCHAR d]))
            (RCHAR e))))"
proof -
  have "d \<noteq> c"
    using assms by simp
  then show ?thesis
    using assms by (simp add: rsimp4_SEQ_def)
qed

lemma current_path_frontier_universe_misses_middle_alt_opaque:
  assumes "c \<noteq> d"
  shows "RSEQ (RCHAR b) (RSEQ (RALTS [RCHAR c, RCHAR d]) (RCHAR e)) \<notin>
    partial_derivative_path_frontier_universe
      (RSEQ
        (RSEQ (RSEQ (RCHAR a) (RCHAR b)) (RALTS [RCHAR c, RCHAR d]))
        (RCHAR e))"
proof -
  have "d \<noteq> c"
    using assms by simp
  then show ?thesis
    using assms
  by (simp add: partial_derivative_path_frontier_universe_def
      rpath_frontiers_def rsimp4_SEQ_def)
qed

lemma middle_alt_opaque_in_path_atom_frontier_universe:
  assumes "c \<noteq> d"
  shows "RSEQ (RCHAR b) (RSEQ (RALTS [RCHAR c, RCHAR d]) (RCHAR e)) \<in>
    partial_derivative_path_atom_frontier_universe
      (RSEQ
        (RSEQ (RSEQ (RCHAR a) (RCHAR b)) (RALTS [RCHAR c, RCHAR d]))
        (RCHAR e))"
proof -
  have "d \<noteq> c"
    using assms by simp
  then show ?thesis
    using assms
    by (simp add: partial_derivative_path_atom_frontier_universe_def
        rpath_atom_frontiers_def rsimp4_SEQ_def)
qed

lemma middle_alt_opaque_in_path_dual_frontier_universe:
  assumes "c \<noteq> d"
  shows "RSEQ (RCHAR b) (RSEQ (RALTS [RCHAR c, RCHAR d]) (RCHAR e)) \<in>
    partial_derivative_path_dual_frontier_universe
      (RSEQ
        (RSEQ (RSEQ (RCHAR a) (RCHAR b)) (RALTS [RCHAR c, RCHAR d]))
        (RCHAR e))"
proof -
  have "d \<noteq> c"
    using assms by simp
  then show ?thesis
    using assms
    by (simp add: partial_derivative_path_dual_frontier_universe_def
        rpath_dual_frontiers_def rpath_dual_frontier_acc_def
        rpath_frontiers_def rpath_atom_frontiers_def rsimp4_SEQ_def)
qed

lemma rsimp5_derivative_distributes_middle_alt_left:
  assumes "c \<noteq> d"
  shows "RSEQ (RCHAR b) (RSEQ (RCHAR c) (RCHAR e)) \<in>
    rfrontier
      (rsimp5
        (rder a
          (RSEQ
            (RSEQ (RSEQ (RCHAR a) (RCHAR b)) (RALTS [RCHAR c, RCHAR d]))
            (RCHAR e))))"
proof -
  have "d \<noteq> c"
    using assms by simp
  then show ?thesis
    using assms by (simp add: rsimp5_SEQ_def)
qed

lemma rsimp5_derivative_distributes_middle_alt_right:
  assumes "c \<noteq> d"
  shows "RSEQ (RCHAR b) (RSEQ (RCHAR d) (RCHAR e)) \<in>
    rfrontier
      (rsimp5
        (rder a
          (RSEQ
            (RSEQ (RSEQ (RCHAR a) (RCHAR b)) (RALTS [RCHAR c, RCHAR d]))
            (RCHAR e))))"
proof -
  have "d \<noteq> c"
    using assms by simp
  then show ?thesis
    using assms by (simp add: rsimp5_SEQ_def)
qed

lemma rsimp5_derivative_distributes_right_alt_suffix_left:
  assumes "a \<noteq> b" "b \<noteq> c" "c \<noteq> d"
  shows "RSEQ (RCHAR b) (RCHAR c) \<in>
    rfrontier
      (rsimp5
        (rder a
          (RSEQ (RSEQ (RCHAR a) (RCHAR b))
            (RALTS [RCHAR c, RCHAR d]))))"
proof -
  have "d \<noteq> c"
    using assms by simp
  then show ?thesis
    using assms by (simp add: rsimp5_SEQ_def)
qed

lemma rsimp5_derivative_distributes_right_alt_suffix_right:
  assumes "a \<noteq> b" "b \<noteq> c" "c \<noteq> d"
  shows "RSEQ (RCHAR b) (RCHAR d) \<in>
    rfrontier
      (rsimp5
        (rder a
          (RSEQ (RSEQ (RCHAR a) (RCHAR b))
            (RALTS [RCHAR c, RCHAR d]))))"
proof -
  have "d \<noteq> c"
    using assms by simp
  then show ?thesis
    using assms by (simp add: rsimp5_SEQ_def)
qed

lemma current_dual_frontier_universe_misses_right_alt_suffix_distribution:
  assumes "a \<noteq> b" "b \<noteq> c" "c \<noteq> d"
  shows "RSEQ (RCHAR b) (RCHAR c) \<notin>
    partial_derivative_path_dual_frontier_universe
      (RSEQ (RSEQ (RCHAR a) (RCHAR b))
        (RALTS [RCHAR c, RCHAR d]))"
proof -
  have "d \<noteq> c"
    using assms by simp
  then show ?thesis
    using assms
    by (simp add: partial_derivative_path_dual_frontier_universe_def
        rpath_dual_frontiers_def rpath_dual_frontier_acc_def
        rpath_frontiers_def rpath_atom_frontiers_def rsimp4_SEQ_def)
qed

definition RSEQ_set where
  "RSEQ_set A n \<equiv> {RSEQ r1 r2 | r1 r2. r1 \<in> A \<and> r2 \<in> A \<and> rsize r1 + rsize r2 \<le> n}"

definition RSEQ_set_cartesian where
  "RSEQ_set_cartesian A  = {RSEQ r1 r2 | r1 r2. r1 \<in> A \<and> r2 \<in> A}"

definition RALT_set where
  "RALT_set A n \<equiv> {RALTS rs | rs. set rs \<subseteq> A \<and> rsizes rs \<le> n}"

definition RALTs_set where
  "RALTs_set A n \<equiv> {RALTS rs | rs. (\<forall>r \<in> set rs. r \<in> A) \<and> rsizes rs \<le> n}"

definition RNTIMES_set where
  "RNTIMES_set A n \<equiv> {RNTIMES r m | m r. r \<in> A \<and> rsize r + m \<le> n}"



definition
  "sizeNregex N \<equiv> {r. legacy_rrexp r \<and> rsize r \<le> N}"

lemma elem_size_le_rsizes:
  assumes "r \<in> set rs"
  shows "rsize r \<le> rsizes rs"
  using assms by (induct rs) auto

lemma elem_size_le_bound:
  assumes "r \<in> set rs" "rsizes rs \<le> n"
  shows "rsize r \<le> n"
  using assms elem_size_le_rsizes by fastforce


lemma sizenregex_induct1:
  "sizeNregex (Suc n) = (({RZERO, RONE} \<union> {RCHAR c| c. True}) 
                         \<union> (RSTAR ` sizeNregex n) 
                         \<union> (RSEQ_set (sizeNregex n) n)
                         \<union> (RALTs_set (sizeNregex n) n))
                         \<union> (RNTIMES_set (sizeNregex n) n)"
  unfolding sizeNregex_def RSEQ_set_def RALTs_set_def RNTIMES_set_def
  apply(auto)
        apply(case_tac x)
             apply(auto simp add: elem_size_le_bound)
  done
    

lemma s4:
  "RSEQ_set A n \<subseteq> RSEQ_set_cartesian A"
  using RSEQ_set_cartesian_def RSEQ_set_def by fastforce

lemma s5:
  assumes "finite A"
  shows "finite (RSEQ_set_cartesian A)"
  using assms
  apply(subgoal_tac "RSEQ_set_cartesian A = (\<lambda>(x1, x2). RSEQ x1 x2) ` (A \<times> A)")
  apply simp
  unfolding RSEQ_set_cartesian_def
  apply(auto)
  done


definition RALTs_set_length
  where
  "RALTs_set_length A n l \<equiv> {RALTS rs | rs. (\<forall>r \<in> set rs. r \<in> A) \<and> rsizes rs \<le> n \<and> length rs \<le> l}"


definition RALTs_set_length2
  where
  "RALTs_set_length2 A l \<equiv> {RALTS rs | rs. (\<forall>r \<in> set rs. r \<in> A) \<and> length rs \<le> l}"

definition set_length2
  where
  "set_length2 A l \<equiv> {rs. (\<forall>r \<in> set rs. r \<in> A) \<and> length rs \<le> l}"


lemma r000: 
  shows "RALTs_set_length A n l \<subseteq> RALTs_set_length2 A l"
  apply(auto simp add: RALTs_set_length2_def RALTs_set_length_def)
  done


lemma r02: 
  shows "set_length2 A 0 \<subseteq> {[]}"
  by (auto simp add: set_length2_def)

lemma r03:
  shows "set_length2 A (Suc n) \<subseteq> 
          {[]} \<union> (\<lambda>(h, t). h # t) ` (A \<times> (set_length2 A n))"
  apply(auto simp add: set_length2_def)
  apply(case_tac x)
   apply(auto)
  done

lemma r1:
  assumes "finite A" 
  shows "finite (set_length2 A n)"
  using assms
  apply(induct n)
  apply(rule finite_subset)
    apply(rule r02)
   apply(simp)    
  apply(rule finite_subset)
   apply(rule r03)
  apply(simp)
  done

lemma size_sum_more_than_len:
  shows "rsizes rs \<ge> length rs"
  apply(induct rs)
   apply simp
  apply simp
  apply(subgoal_tac "rsize a \<ge> 1")
   apply linarith
  using size_geq1 by auto


lemma sum_list_len:
  shows "rsizes rs \<le> n \<Longrightarrow> length rs \<le> n"
  by (meson order.trans size_sum_more_than_len)


lemma t2:
  shows "RALTs_set A n \<subseteq> RALTs_set_length A n n"
  unfolding RALTs_set_length_def RALTs_set_def
  apply(auto)
  using sum_list_len by blast

lemma s8_aux:
  assumes "finite A" 
  shows "finite (RALTs_set_length A n n)"
proof -
  have "finite A" by fact
  then have "finite (set_length2 A n)"
    by (simp add: r1)
  moreover have "(RALTS ` (set_length2 A n)) = RALTs_set_length2 A n"
    unfolding RALTs_set_length2_def set_length2_def
    by (auto)
  ultimately have "finite (RALTs_set_length2 A n)"
    by (metis finite_imageI)
  then show ?thesis
    by (metis infinite_super r000)
qed

lemma char_finite:
  shows "finite  {RCHAR c |c. True}"
  apply simp
  apply(subgoal_tac "finite (RCHAR ` (UNIV::char set))")
   prefer 2
   apply simp
  by (simp add: full_SetCompr_eq)

thm RNTIMES_set_def

lemma s9_aux0:
  shows "RNTIMES_set (insert r A) n \<subseteq> RNTIMES_set A n \<union> (\<Union> i \<in> {..n}. {RNTIMES r i})"
apply(auto simp add: RNTIMES_set_def)
  done

lemma s9_aux:
  assumes "finite A"
  shows "finite (RNTIMES_set A n)"
  using assms
  apply(induct A arbitrary: n)
   apply(auto simp add: RNTIMES_set_def)[1]
  apply(subgoal_tac "finite (RNTIMES_set F n \<union> (\<Union> i \<in> {..n}. {RNTIMES x i}))")
  apply (metis finite_subset s9_aux0)
  by blast

(* BACKREF-MIGRATION-TODO (proof constructor-case extension):
   Extend finite_size_n for the approved representation of backreference
   constructors. This is a real bounds theorem; wrapper cardinality facts in a
   separate BackRefBoundedBlueprint-style file must not count as bounty. *)
lemma finite_size_n:
  shows "finite (sizeNregex n)"
  apply(induct n)
   apply(simp add: sizeNregex_def)
  apply (metis (mono_tags, lifting) not_finite_existsD not_one_le_zero size_geq1)
  apply(subst sizenregex_induct1)
  apply(simp only: finite_Un)
  apply(rule conjI)+
        apply(simp)
  
  using char_finite apply blast
    apply(simp)
   apply(rule finite_subset)
    apply(rule s4)
   apply(rule s5)
   apply(simp)
  apply(rule finite_subset)
   apply(rule t2)
  apply(rule s8_aux)
    apply(simp)
  apply(simp add: s9_aux)
  done


lemma three_easy_cases0: 
  shows "rsize (rders_simp RZERO s) \<le> Suc 0"
  apply(induct s)
   apply simp
  apply simp
  done


lemma three_easy_cases1: 
  shows "rsize (rders_simp RONE s) \<le> Suc 0"
    apply(induct s)
   apply simp
  apply simp
  using three_easy_cases0 by auto


lemma three_easy_casesC: 
  shows "rsize (rders_simp (RCHAR c) s) \<le> Suc 0"
  apply(induct s)
   apply simp
  apply simp
  apply(case_tac " a = c")
  using three_easy_cases1 apply blast
  apply simp
  using three_easy_cases0 by force
  
end

