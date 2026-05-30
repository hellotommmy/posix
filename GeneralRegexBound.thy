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

lemma finite_partial_derivative_path_universe [simp]:
  "finite (partial_derivative_path_universe r)"
  by (simp add: partial_derivative_path_universe_def rpath_continuations_def)

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

