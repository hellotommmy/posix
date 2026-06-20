(*  Route-2 / N-route — Wave 2A: the normalized opening delta_N (= ndlforms).
    Owner: norm/01-alpha lane.  Session: Posix_Norm.

    delta_N mirrors the lexer's row_dlforms but distributes an alternation-headed
    sequence via the associative nplug (alpha) instead of sigma7, so it opens into
    FULLY normalized rows (matching experiments/norm/norm_model.py).  This is route-
    agnostic N-machinery: it is correct regardless of how the (currently open, post-
    Claim-L-refutation) old->new bridge is rescued.  Termination uses rsize_nplug_le.
    No unfinished proofs.  *)

theory NormalizedOpening
  imports NormalizedStrong
begin

lemma rsize_member_le_sum: "q \<in> set rs \<Longrightarrow> rsize q \<le> sum_list (map rsize rs)"
  by (induction rs) auto

function (sequential) ndlforms :: "rrexp \<Rightarrow> rrexp set" where
  "ndlforms RZERO = {}"
| "ndlforms (RALTS rs) = (\<Union>q \<in> set rs. ndlforms q)"
| "ndlforms (RSEQ (RALTS ps) k) = (\<Union>p \<in> set ps. ndlforms (nplug p k))"
| "ndlforms r = rfrontier r"
  by pat_completeness auto

termination
proof (relation "measure rsize", goal_cases)
  case 1 show ?case by simp
next
  case (2 rs q)
  then show ?case by (simp add: rsize_member_le_sum le_imp_less_Suc)
next
  case (3 ps k p)
  then have "rsize (nplug p k) \<le> sum_list (map rsize ps) + rsize k + 1"
    using rsize_nplug_le[of p k] rsize_member_le_sum[of p ps] by simp
  then show ?case by simp
qed

lemma finite_rfrontier: "finite (rfrontier r)"
  by (induction r) auto

lemma finite_ndlforms: "finite (ndlforms r)"
  by (induction r rule: ndlforms.induct) (auto simp: finite_rfrontier)

end
