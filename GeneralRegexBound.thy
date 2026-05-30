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
         (\<lambda>(p, k). RSEQ p k) ` (rsubterms r \<times> rlinear_continuations r)))"

lemma finite_partial_derivative_frontier_universe [simp]:
  "finite (partial_derivative_frontier_universe r)"
  by (simp add: partial_derivative_frontier_universe_def)

lemma quadratic_padding_bound:
  fixes n :: nat
  shows "2 + n + n * n \<le> (n + 2) ^ 2"
proof -
  have "(n + 2) ^ 2 = n * n + 4 * n + 4"
    by (simp add: algebra_simps power2_eq_square)
  moreover have "2 + n \<le> 4 * n + 4"
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
  have "card (partial_derivative_frontier_universe r) \<le> 2 + card ?A + card ?P"
    unfolding partial_derivative_frontier_universe_def
    by (rule card_insert2_Un_le) simp_all
  also have "... \<le> 2 + rsize r + rsize r * rsize r"
    using A P_size by linarith
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
  have q_cases: "q = RZERO \<or> q = RONE \<or> q \<in> ?A \<or> q \<in> ?P"
    using assms unfolding partial_derivative_frontier_universe_def by auto
  then show ?thesis
  proof
    assume "q = RZERO"
    then show ?thesis by simp
  next
    assume rest1: "q = RONE \<or> q \<in> ?A \<or> q \<in> ?P"
    then show ?thesis
    proof
      assume "q = RONE"
      then show ?thesis by simp
    next
      assume rest2: "q \<in> ?A \<or> q \<in> ?P"
      then show ?thesis
      proof
        assume "q \<in> ?A"
        then have "rsize q \<le> rsize r"
          using rsubterms_member_size_le_rsize by blast
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

