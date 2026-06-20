theory Card_Route1_Cover
  imports "Posix_Cubic.DirectUniverseCubic"
begin

(* ===================================================================== *)
(* LANE COVER — prove L1 (the SAA-level singleton cover).  See ROUTE_COVER.md. *)
(* Build: scripts\codex-isabelle-build-posix.ps1 -Session Posix_Card_Route1_Cover *)
(* NO sorry. Build green. Fail-stop + report.                            *)
(* ===================================================================== *)

(* shared defs (same names as the integration file) *)
definition single_root :: "rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "single_root q k =
     rsimpStrong_dlform_closure (rfrontier (rsimp4_SEQ_atom (RALTS [q]) k))"
definition single_term :: "rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "single_term q k =
     rsimpStrong_dlform_closure (apder_term_frontier_acc q k)"

lemma strong_apder_acc_RALTS_terms_singleton_cover:
  "rsimpStrong_dlform_closure (apder_term_frontier_acc (RALTS rs) k) \<subseteq>
    (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
  by (auto simp add: strong_apder_acc_def rsimpStrong_dlform_closure_def)

lemma strong_apder_acc_RALTS_root_RZERO_singleton_cover:
  "rsimpStrong_dlform_closure
     (rfrontier (rsimp4_SEQ_atom (RALTS rs) RZERO)) \<subseteq>
    (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) RZERO)"
  by (simp add: rsimpStrong_dlform_closure_def)

lemma strong_apder_acc_RALTS_root_RONE_singleton_cover:
  "rsimpStrong_dlform_closure
     (rfrontier (rsimp4_SEQ_atom (RALTS rs) RONE)) \<subseteq>
    (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) RONE)"
  by (induct rs)
    (auto simp add: strong_apder_acc_def rsimpStrong_dlform_closure_def)

lemma strong_apder_acc_RALTS_singleton_cover_RZERO:
  "strong_apder_acc (RALTS rs) RZERO \<subseteq>
    (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) RZERO)"
  using strong_apder_acc_RALTS_root_RZERO_singleton_cover[of rs]
    strong_apder_acc_RALTS_terms_singleton_cover[of rs RZERO]
  by (auto simp add: strong_apder_acc_def rsimpStrong_dlform_closure_def)

lemma strong_apder_acc_RALTS_singleton_cover_RONE:
  "strong_apder_acc (RALTS rs) RONE \<subseteq>
    (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) RONE)"
  using strong_apder_acc_RALTS_root_RONE_singleton_cover[of rs]
    strong_apder_acc_RALTS_terms_singleton_cover[of rs RONE]
  by (auto simp add: strong_apder_acc_def rsimpStrong_dlform_closure_def)

lemma row_dlforms_rsimpStrong_raw_subset_frontier_closure:
  "row_dlforms (rsimpStrong_raw p) \<subseteq>
    rsimpStrong_dlform_closure (rfrontier p)"
proof (induct p)
  case RZERO
  then show ?case
    by simp
next
  case (RALTS rs)
  show ?case
  proof (rule row_dlforms_rsimpStrong_raw_RALTS_subsetI)
    fix q
    assume q: "q \<in> set rs"
    have q_sub:
      "row_dlforms (rsimpStrong_raw q) \<subseteq>
        rsimpStrong_dlform_closure (rfrontier q)"
      by (rule RALTS.hyps[OF q])
    have front_sub: "rfrontier q \<subseteq> rfrontier (RALTS rs)"
      using q by (auto simp add: rfrontiers_member_iff)
    have closure_sub:
      "rsimpStrong_dlform_closure (rfrontier q) \<subseteq>
        rsimpStrong_dlform_closure (rfrontier (RALTS rs))"
      by (rule rsimpStrong_dlform_closure_mono[OF front_sub])
    show "row_dlforms (rsimpStrong_raw q) \<subseteq>
        rsimpStrong_dlform_closure (rfrontier (RALTS rs))"
      using q_sub closure_sub by blast
  qed
qed (auto simp add: rsimpStrong_dlform_closure_def)

lemma rprune_eq_against_set_subset_local:
  "set (rprune_eq_against covered rs) \<subseteq> set rs"
  by (induct rs) auto

lemma row_dlforms_rsimp7_rsimp_ALTs_subset_RALTS:
  assumes ps: "set ps \<subseteq> set qs"
    and nf: "\<forall>q \<in> set qs. rtail_nf q"
  shows "row_dlforms (rsimp7_SEQ_atom (rsimp_ALTs ps) k) \<subseteq>
    row_dlforms (rsimp7_SEQ_atom (RALTS qs) k)"
proof (cases k)
  case RZERO
  then show ?thesis
    by (cases "rsimp_ALTs ps") (simp_all add: rsimp7_SEQ_atom_def)
next
  case RONE
  show ?thesis
  proof (cases ps)
    case Nil
    then show ?thesis
      using RONE by (simp add: rsimp7_SEQ_atom_def)
  next
    case (Cons p ps')
    have stable: "\<And>q. q \<in> set ps \<Longrightarrow> rsimp7_SEQ_atom q RONE = q"
      by (rule rtail_nf_RONE_stable7) (use ps nf in auto)
    show ?thesis
      using RONE Cons ps stable
      by (cases ps') (auto simp add: rsimp7_SEQ_atom_def)
  qed
next
  case (RCHAR c)
  then show ?thesis
    using ps by (cases ps; cases "tl ps") (auto simp add: rsimp7_SEQ_atom_def)
next
  case (RSEQ k1 k2)
  then show ?thesis
    using ps by (cases ps; cases "tl ps") (auto simp add: rsimp7_SEQ_atom_def)
next
  case (RALTS ks)
  then show ?thesis
    using ps by (cases ps; cases "tl ps") (auto simp add: rsimp7_SEQ_atom_def)
next
  case (RSTAR k)
  then show ?thesis
    using ps by (cases ps; cases "tl ps") (auto simp add: rsimp7_SEQ_atom_def)
next
  case (RNTIMES k n)
  then show ?thesis
    using ps by (cases ps; cases "tl ps") (auto simp add: rsimp7_SEQ_atom_def)
next
  case (RBACKREF4 k1 k2 k3 k4 cs)
  then show ?thesis
    using ps by (cases ps; cases "tl ps") (auto simp add: rsimp7_SEQ_atom_def)
next
  case (RHALF k cs rep)
  then show ?thesis
    using ps by (cases ps; cases "tl ps") (auto simp add: rsimp7_SEQ_atom_def)
next
  case (RRESIDUE cs rep)
  then show ?thesis
    using ps by (cases ps; cases "tl ps") (auto simp add: rsimp7_SEQ_atom_def)
qed

lemma row_dlforms_rsimp7_subset_rsimp4_or_suffix:
  "row_dlforms (rsimp7_SEQ_atom r k) \<subseteq>
    row_dlforms (rsimp4_SEQ_atom r k) \<union> row_dlforms k"
proof (cases r)
  case (RSTAR p)
  then show ?thesis
    by (cases k)
      (auto simp add: rsimp7_SEQ_atom_def split: rrexp.splits if_splits)
qed (simp_all add: rsimp7_SEQ_atom_def)

lemma row_dlforms_rsimp7_assoc_subset_suffix_rtail_nf:
  assumes k_nf: "rtail_nf k"
    and K_nf: "rtail_nf K"
  shows "row_dlforms (rsimp7_SEQ_atom (rsimp7_SEQ_atom p k) K) \<subseteq>
    row_dlforms (rsimp7_SEQ_atom p (rsimp4_SEQ_atom k K)) \<union>
    row_dlforms K"
proof (cases p)
  case RZERO
  then show ?thesis
    by (cases p; cases K)
      (simp_all add: rsimp7_SEQ_atom_def split: rrexp.splits prod.splits)
next
  case RONE
  have sub: "row_dlforms (rsimp7_SEQ_atom k K) \<subseteq>
      row_dlforms (rsimp4_SEQ_atom k K) \<union> row_dlforms K"
    by (rule row_dlforms_rsimp7_subset_rsimp4_or_suffix)
  then show ?thesis
    using RONE by (simp add: rsimp7_SEQ_atom_def)
next
  case (RCHAR c)
  have sub:
      "row_dlforms
        (rsimp7_SEQ_atom (rsimp4_SEQ_atom (RCHAR c) k) K) \<subseteq>
       row_dlforms
        (rsimp4_SEQ_atom (rsimp4_SEQ_atom (RCHAR c) k) K) \<union>
       row_dlforms K"
    by (rule row_dlforms_rsimp7_subset_rsimp4_or_suffix)
  then show ?thesis
    using RCHAR
    by (simp add: rsimp7_SEQ_atom_def rsimp4_SEQ_atom_assoc)
next
  case (RSEQ p1 p2)
  have sub:
      "row_dlforms
        (rsimp7_SEQ_atom (rsimp4_SEQ_atom (RSEQ p1 p2) k) K) \<subseteq>
       row_dlforms
        (rsimp4_SEQ_atom (rsimp4_SEQ_atom (RSEQ p1 p2) k) K) \<union>
       row_dlforms K"
    by (rule row_dlforms_rsimp7_subset_rsimp4_or_suffix)
  then show ?thesis
    using RSEQ
    by (simp add: rsimp7_SEQ_atom_def rsimp4_SEQ_atom_assoc)
next
  case (RALTS ps)
  have sub:
      "row_dlforms
        (rsimp7_SEQ_atom (rsimp4_SEQ_atom (RALTS ps) k) K) \<subseteq>
       row_dlforms
        (rsimp4_SEQ_atom (rsimp4_SEQ_atom (RALTS ps) k) K) \<union>
       row_dlforms K"
    by (rule row_dlforms_rsimp7_subset_rsimp4_or_suffix)
  then show ?thesis
    using RALTS
    by (simp add: rsimp7_SEQ_atom_def rsimp4_SEQ_atom_assoc)
next
  case (RSTAR r)
  note p_star = RSTAR
  show ?thesis
  proof (cases k)
    case RZERO
    then show ?thesis
      using RSTAR by (simp add: rsimp7_SEQ_atom_def)
  next
    case RONE
    then show ?thesis
      using RSTAR by (simp add: rsimp7_SEQ_atom_def)
  next
    case (RCHAR c)
    have sub:
        "row_dlforms
          (rsimp7_SEQ_atom (rsimp4_SEQ_atom (RSTAR r) (RCHAR c)) K) \<subseteq>
         row_dlforms
          (rsimp4_SEQ_atom (rsimp4_SEQ_atom (RSTAR r) (RCHAR c)) K) \<union>
         row_dlforms K"
      by (rule row_dlforms_rsimp7_subset_rsimp4_or_suffix)
    then show ?thesis
      using RSTAR RCHAR
      by (cases K)
        (simp_all add: rsimp7_SEQ_atom_def rsimp4_SEQ_atom_assoc)
  next
    case (RALTS rs)
    have sub:
        "row_dlforms
          (rsimp7_SEQ_atom (rsimp4_SEQ_atom (RSTAR r) (RALTS rs)) K) \<subseteq>
         row_dlforms
          (rsimp4_SEQ_atom (rsimp4_SEQ_atom (RSTAR r) (RALTS rs)) K) \<union>
         row_dlforms K"
      by (rule row_dlforms_rsimp7_subset_rsimp4_or_suffix)
    then show ?thesis
      using RSTAR RALTS
      by (cases K)
        (simp_all add: rsimp7_SEQ_atom_def rsimp4_SEQ_atom_assoc)
  next
    case (RSTAR s)
    show ?thesis
    proof (cases "r = s")
      case True
      show ?thesis
      proof (cases K)
        case (RSEQ K1 K2)
        then show ?thesis
          using p_star RSTAR True K_nf
          by (cases K1)
            (auto simp add: rsimp7_SEQ_atom_def rsimp4_SEQ_atom_assoc)
      qed (use p_star RSTAR True K_nf in
          \<open>simp_all add: rsimp7_SEQ_atom_def rsimp4_SEQ_atom_assoc\<close>)
    next
      case False
      show ?thesis
      proof (cases K)
        case (RSEQ K1 K2)
        then show ?thesis
          using p_star RSTAR False K_nf
          by (cases K1)
            (auto simp add: rsimp7_SEQ_atom_def rsimp4_SEQ_atom_assoc)
      qed (use p_star RSTAR False K_nf in
          \<open>simp_all add: rsimp7_SEQ_atom_def rsimp4_SEQ_atom_assoc\<close>)
    qed
  next
    case (RSEQ k1 k2)
    note k_seq = RSEQ
    show ?thesis
    proof (cases k1)
      case RZERO
      then show ?thesis
        using p_star k_seq k_nf by simp
    next
      case RONE
      then show ?thesis
        using p_star k_seq k_nf by simp
    next
      case (RCHAR c)
      let ?C = "rsimp4_SEQ_atom k2 K"
      show ?thesis
        using p_star k_seq RCHAR
        by (cases ?C)
          (simp_all add: rsimp7_SEQ_atom_def rsimp4_SEQ_atom_assoc)
    next
      case (RSEQ a b)
      then show ?thesis
        using p_star k_seq k_nf by simp
    next
      case (RALTS rs)
      let ?C = "rsimp4_SEQ_atom k2 K"
      show ?thesis
        using p_star k_seq RALTS
        by (cases ?C)
          (simp_all add: rsimp7_SEQ_atom_def rsimp4_SEQ_atom_assoc)
    next
      case (RSTAR s)
      let ?C = "rsimp4_SEQ_atom k2 K"
      show ?thesis
      proof (cases "r = s")
        case True
        then show ?thesis
          using p_star k_seq RSTAR
          by (cases ?C)
            (simp_all add: rsimp7_SEQ_atom_def rsimp4_SEQ_atom_assoc)
      next
        case False
        then show ?thesis
          using p_star k_seq RSTAR
          by (cases ?C)
            (simp_all add: rsimp7_SEQ_atom_def rsimp4_SEQ_atom_assoc)
      qed
    next
      case (RNTIMES s n)
      let ?C = "rsimp4_SEQ_atom k2 K"
      show ?thesis
        using p_star k_seq RNTIMES
        by (cases ?C)
          (simp_all add: rsimp7_SEQ_atom_def rsimp4_SEQ_atom_assoc)
    next
      case (RBACKREF4 r1 r2 r3 r4 cs)
      let ?C = "rsimp4_SEQ_atom k2 K"
      show ?thesis
        using p_star k_seq RBACKREF4
        by (cases ?C)
          (simp_all add: rsimp7_SEQ_atom_def rsimp4_SEQ_atom_assoc)
    next
      case (RHALF s cs rep)
      let ?C = "rsimp4_SEQ_atom k2 K"
      show ?thesis
        using p_star k_seq RHALF
        by (cases ?C)
          (simp_all add: rsimp7_SEQ_atom_def rsimp4_SEQ_atom_assoc)
    next
      case (RRESIDUE cs rep)
      let ?C = "rsimp4_SEQ_atom k2 K"
      show ?thesis
        using p_star k_seq RRESIDUE
        by (cases ?C)
          (simp_all add: rsimp7_SEQ_atom_def rsimp4_SEQ_atom_assoc)
    qed
  next
    case (RNTIMES s n)
    have sub:
        "row_dlforms
          (rsimp7_SEQ_atom (rsimp4_SEQ_atom (RSTAR r) (RNTIMES s n)) K) \<subseteq>
         row_dlforms
          (rsimp4_SEQ_atom (rsimp4_SEQ_atom (RSTAR r) (RNTIMES s n)) K) \<union>
         row_dlforms K"
      by (rule row_dlforms_rsimp7_subset_rsimp4_or_suffix)
    then show ?thesis
      using RSTAR RNTIMES
      by (cases K)
        (simp_all add: rsimp7_SEQ_atom_def rsimp4_SEQ_atom_assoc)
  next
    case (RBACKREF4 r1 r2 r3 r4 cs)
    have sub:
        "row_dlforms
          (rsimp7_SEQ_atom
            (rsimp4_SEQ_atom (RSTAR r) (RBACKREF4 r1 r2 r3 r4 cs)) K) \<subseteq>
         row_dlforms
          (rsimp4_SEQ_atom
            (rsimp4_SEQ_atom (RSTAR r) (RBACKREF4 r1 r2 r3 r4 cs)) K) \<union>
         row_dlforms K"
      by (rule row_dlforms_rsimp7_subset_rsimp4_or_suffix)
    then show ?thesis
      using RSTAR RBACKREF4
      by (cases K)
        (simp_all add: rsimp7_SEQ_atom_def rsimp4_SEQ_atom_assoc)
  next
    case (RHALF s cs rep)
    have sub:
        "row_dlforms
          (rsimp7_SEQ_atom (rsimp4_SEQ_atom (RSTAR r) (RHALF s cs rep)) K) \<subseteq>
         row_dlforms
          (rsimp4_SEQ_atom
            (rsimp4_SEQ_atom (RSTAR r) (RHALF s cs rep)) K) \<union>
         row_dlforms K"
      by (rule row_dlforms_rsimp7_subset_rsimp4_or_suffix)
    then show ?thesis
      using RSTAR RHALF
      by (cases K)
        (simp_all add: rsimp7_SEQ_atom_def rsimp4_SEQ_atom_assoc)
  next
    case (RRESIDUE cs rep)
    have sub:
        "row_dlforms
          (rsimp7_SEQ_atom (rsimp4_SEQ_atom (RSTAR r) (RRESIDUE cs rep)) K) \<subseteq>
         row_dlforms
          (rsimp4_SEQ_atom
            (rsimp4_SEQ_atom (RSTAR r) (RRESIDUE cs rep)) K) \<union>
         row_dlforms K"
      by (rule row_dlforms_rsimp7_subset_rsimp4_or_suffix)
    then show ?thesis
      using RSTAR RRESIDUE
      by (cases K)
        (simp_all add: rsimp7_SEQ_atom_def rsimp4_SEQ_atom_assoc)
  qed
next
  case (RNTIMES r n)
  have sub:
      "row_dlforms
        (rsimp7_SEQ_atom (rsimp4_SEQ_atom (RNTIMES r n) k) K) \<subseteq>
       row_dlforms
        (rsimp4_SEQ_atom (rsimp4_SEQ_atom (RNTIMES r n) k) K) \<union>
       row_dlforms K"
    by (rule row_dlforms_rsimp7_subset_rsimp4_or_suffix)
  then show ?thesis
    using RNTIMES
    by (simp add: rsimp7_SEQ_atom_def rsimp4_SEQ_atom_assoc)
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  have sub:
      "row_dlforms
        (rsimp7_SEQ_atom
          (rsimp4_SEQ_atom (RBACKREF4 r1 r2 r3 r4 cs) k) K) \<subseteq>
       row_dlforms
        (rsimp4_SEQ_atom
          (rsimp4_SEQ_atom (RBACKREF4 r1 r2 r3 r4 cs) k) K) \<union>
       row_dlforms K"
    by (rule row_dlforms_rsimp7_subset_rsimp4_or_suffix)
  then show ?thesis
    using RBACKREF4
    by (simp add: rsimp7_SEQ_atom_def rsimp4_SEQ_atom_assoc)
next
  case (RHALF r cs rep)
  have sub:
      "row_dlforms
        (rsimp7_SEQ_atom (rsimp4_SEQ_atom (RHALF r cs rep) k) K) \<subseteq>
       row_dlforms
        (rsimp4_SEQ_atom (rsimp4_SEQ_atom (RHALF r cs rep) k) K) \<union>
       row_dlforms K"
    by (rule row_dlforms_rsimp7_subset_rsimp4_or_suffix)
  then show ?thesis
    using RHALF
    by (simp add: rsimp7_SEQ_atom_def rsimp4_SEQ_atom_assoc)
next
  case (RRESIDUE cs rep)
  have sub:
      "row_dlforms
        (rsimp7_SEQ_atom (rsimp4_SEQ_atom (RRESIDUE cs rep) k) K) \<subseteq>
       row_dlforms
        (rsimp4_SEQ_atom (rsimp4_SEQ_atom (RRESIDUE cs rep) k) K) \<union>
       row_dlforms K"
    by (rule row_dlforms_rsimp7_subset_rsimp4_or_suffix)
  then show ?thesis
    using RRESIDUE
    by (simp add: rsimp7_SEQ_atom_def rsimp4_SEQ_atom_assoc)
qed

lemma row_dlforms_rsimp7_nested_altseq_subset_later_or_suffix:
  assumes ps: "set ps \<subseteq> set qs"
    and qs_nf: "\<forall>q \<in> set qs. rtail_nf q"
    and k_nf: "rtail_nf k"
    and K_nf: "rtail_nf K"
  shows "row_dlforms
      (rsimp7_SEQ_atom (rsimp7_SEQ_atom (rsimp_ALTs ps) k) K) \<subseteq>
    row_dlforms (rsimp7_SEQ_atom (RSEQ (RALTS qs) k) K) \<union> row_dlforms K"
proof -
  have assoc:
      "row_dlforms
        (rsimp7_SEQ_atom (rsimp7_SEQ_atom (rsimp_ALTs ps) k) K) \<subseteq>
       row_dlforms
        (rsimp7_SEQ_atom (rsimp_ALTs ps) (rsimp4_SEQ_atom k K)) \<union>
       row_dlforms K"
    by (rule row_dlforms_rsimp7_assoc_subset_suffix_rtail_nf
        [OF k_nf K_nf])
  have branch:
      "row_dlforms
        (rsimp7_SEQ_atom (rsimp_ALTs ps) (rsimp4_SEQ_atom k K)) \<subseteq>
       row_dlforms
        (rsimp7_SEQ_atom (RALTS qs) (rsimp4_SEQ_atom k K))"
    by (rule row_dlforms_rsimp7_rsimp_ALTs_subset_RALTS
        [OF ps qs_nf])
  have rewrite:
      "rsimp7_SEQ_atom (RSEQ (RALTS qs) k) K =
       rsimp7_SEQ_atom (RALTS qs) (rsimp4_SEQ_atom k K)"
    by (simp add: rsimp7_SEQ_atom_def rsimp4_SEQ_atom_assoc)
  have target_eq:
      "row_dlforms (rsimp7_SEQ_atom (RSEQ (RALTS qs) k) K) =
       row_dlforms
        (rsimp7_SEQ_atom (RALTS qs) (rsimp4_SEQ_atom k K))"
    by (simp add: rewrite)
  show ?thesis
    using assoc branch target_eq by blast
qed

lemma row_dlforms_rsimp7_prune_pair_subset_later_or_suffix:
  assumes later_nf: "rtail_nf later"
    and K_nf: "rtail_nf K"
  shows
  "row_dlforms
      (rsimp7_SEQ_atom (rsimpStrong_prune_pair_raw earlier later) K) \<subseteq>
    row_dlforms (rsimp7_SEQ_atom later K) \<union> row_dlforms K"
proof -
  consider
    (shared) lrs rrs k where
      "earlier = RSEQ (RALTS lrs) k"
      "later = RSEQ (RALTS rrs) k"
  | (other) "\<not> (\<exists>lrs rrs k.
      earlier = RSEQ (RALTS lrs) k \<and>
      later = RSEQ (RALTS rrs) k)"
    by blast
  then show ?thesis
  proof cases
    case (shared lrs rrs k)
    have pruned: "set (rprune_eq_against lrs rrs) \<subseteq> set rrs"
      by (rule rprune_eq_against_set_subset_local)
    have rrs_nf: "\<forall>q \<in> set rrs. rtail_nf q"
      using later_nf shared by simp
    have k_nf: "rtail_nf k"
      using later_nf shared by simp
    have "row_dlforms
        (rsimp7_SEQ_atom
          (rsimp7_SEQ_atom (rsimp_ALTs (rprune_eq_against lrs rrs)) k) K)
        \<subseteq>
        row_dlforms (rsimp7_SEQ_atom (RSEQ (RALTS rrs) k) K) \<union>
        row_dlforms K"
      by (rule row_dlforms_rsimp7_nested_altseq_subset_later_or_suffix
          [OF pruned rrs_nf k_nf K_nf])
    then show ?thesis
      using shared by (simp add: rsimpStrong_prune_pair_raw_def)
  next
    case other
    have "rsimpStrong_prune_pair_raw earlier later = later"
      using other
      unfolding rsimpStrong_prune_pair_raw_def
      by (cases earlier; cases later) (auto split: rrexp.splits)
    then show ?thesis
      by simp
  qed
qed

lemma row_dlforms_singleton_root_subset_strong_apder_acc:
  "row_dlforms (rsimpStrong_raw (rsimp4_SEQ_atom (RALTS [q]) k)) \<subseteq>
    strong_apder_acc (RALTS [q]) k"
proof -
  have "row_dlforms (rsimpStrong_raw (rsimp4_SEQ_atom (RALTS [q]) k)) \<subseteq>
      rsimpStrong_dlform_closure
        (rfrontier (rsimp4_SEQ_atom (RALTS [q]) k))"
    by (rule row_dlforms_rsimpStrong_raw_subset_frontier_closure)
  also have "... \<subseteq> strong_apder_acc (RALTS [q]) k"
    unfolding strong_apder_acc_def
    by (rule rsimpStrong_dlform_closure_mono) auto
  finally show ?thesis .
qed

lemma row_dlforms_RALTS_singleton_roots_subset_cover:
  "row_dlforms
      (rsimpStrong_raw
        (RALTS (map (\<lambda>q. rsimp4_SEQ_atom (RALTS [q]) k) rs))) \<subseteq>
    (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
proof (rule row_dlforms_rsimpStrong_raw_RALTS_subsetI)
  fix p
  assume p: "p \<in> set (map (\<lambda>q. rsimp4_SEQ_atom (RALTS [q]) k) rs)"
  then obtain q where q: "q \<in> set rs"
    and p_def: "p = rsimp4_SEQ_atom (RALTS [q]) k"
    by auto
  have "row_dlforms (rsimpStrong_raw p) \<subseteq>
      strong_apder_acc (RALTS [q]) k"
    using p_def by (simp add: row_dlforms_singleton_root_subset_strong_apder_acc)
  then show "row_dlforms (rsimpStrong_raw p) \<subseteq>
      (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
    using q by blast
qed

definition singleton_saa_ok :: "rrexp \<Rightarrow> rrexp \<Rightarrow> bool" where
  "singleton_saa_ok q t \<longleftrightarrow>
    (\<forall>k. row_dlforms (rsimp7_SEQ_atom t (rsimpStrong_raw k)) \<subseteq>
      strong_apder_acc (RALTS [q]) k)"

definition singleton_saa_key_credit :: "rrexp \<Rightarrow> rrexp \<Rightarrow> bool" where
  "singleton_saa_key_credit q t \<longleftrightarrow>
    (\<forall>rows tail k.
      t = RSEQ (RALTS rows) tail \<longrightarrow>
      (RONE \<in> set rows \<or> (\<exists>s. tail = RSTAR s \<and> RSTAR s \<in> set rows)) \<longrightarrow>
      row_dlforms (rsimpStrong_raw (rsimp4_SEQ_atom tail k)) \<subseteq>
        strong_apder_acc (RALTS [q]) k)"

definition singleton_saa_scan_ok :: "rrexp \<Rightarrow> rrexp \<Rightarrow> bool" where
  "singleton_saa_scan_ok q t \<longleftrightarrow>
    singleton_saa_ok q t \<and> singleton_saa_key_credit q t"

(* ===================================================================== *)
(* GENERIC-k normalisation of the ROOT carrier.  For k \<notin> {RZERO,RONE} the   *)
(* sigma4 plug freezes to RSEQ (RALTS rs) k whose rfrontier is the single   *)
(* row, so the strong-dl closure of the ROOT carrier is just the strong     *)
(* opening of that one row.                                                  *)
(* ===================================================================== *)

lemma rsimpStrong_dlform_closure_rfrontier_RALTS_seq_eq:
  assumes "k \<noteq> RZERO" and "k \<noteq> RONE"
  shows "rsimpStrong_dlform_closure (rfrontier (rsimp4_SEQ_atom (RALTS rs) k))
       = row_dlforms (rsimpStrong_raw (RSEQ (RALTS rs) k))"
proof -
  have "rsimp4_SEQ_atom (RALTS rs) k = RSEQ (RALTS rs) k"
    using assms by (cases k) auto
  then show ?thesis
    by (simp add: rsimpStrong_dlform_closure_def)
qed

(* ===================================================================== *)
(* L1 REDUCED TO ONE BRIDGE.  The two-carrier split (Carriers I/II) makes   *)
(* the singleton cover follow GREEN from a single inclusion `root_split`:    *)
(* the ROOT carrier of the parent lands in (the branch ROOT carriers) UNION  *)
(* (the parent ACC closure).  Both targets are already covered:              *)
(*   - branch roots      : row_dlforms_singleton_root_subset_strong_apder_acc *)
(*   - parent acc closure: strong_apder_acc_RALTS_terms_singleton_cover       *)
(* so this lemma discharges everything EXCEPT `root_split`.                   *)
(*                                                                            *)
(* `root_split` is exactly the [VALIDATED, TRUE >12M] B1/B2 statement:        *)
(* every opened parent ROOT row y either (B1) has a surviving branch-root     *)
(* origin -> a branch root carrier; or (B2) is a cross-prune sigma7-collapsed *)
(* bare star `RSTAR s` with NO root origin -> the ACC carrier (a branch       *)
(* ending in a star sequence has an acc row  RSEQ (RSTAR s) (RSTAR s),  whose *)
(* strong opening collapses to RSTAR s, yielding the singleton {RSTAR s}).    *)
(* It is the lone open goal; the rest of L1 is closed here.                   *)
(* ===================================================================== *)

lemma strong_apder_acc_RALTS_singleton_cover_if_root_split:
  assumes root_split:
    "rsimpStrong_dlform_closure (rfrontier (rsimp4_SEQ_atom (RALTS rs) k)) \<subseteq>
      (\<Union>q \<in> set rs.
         row_dlforms (rsimpStrong_raw (rsimp4_SEQ_atom (RALTS [q]) k))) \<union>
      rsimpStrong_dlform_closure (apder_term_frontier_acc (RALTS rs) k)"
  shows "strong_apder_acc (RALTS rs) k \<subseteq>
    (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
proof -
  have terms:
    "rsimpStrong_dlform_closure (apder_term_frontier_acc (RALTS rs) k) \<subseteq>
       (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
    by (rule strong_apder_acc_RALTS_terms_singleton_cover)
  have branch_roots:
    "(\<Union>q \<in> set rs.
        row_dlforms (rsimpStrong_raw (rsimp4_SEQ_atom (RALTS [q]) k))) \<subseteq>
       (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
    using row_dlforms_singleton_root_subset_strong_apder_acc by fast
  have root:
    "rsimpStrong_dlform_closure (rfrontier (rsimp4_SEQ_atom (RALTS rs) k)) \<subseteq>
       (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
    using root_split branch_roots terms by blast
  show ?thesis
    unfolding strong_apder_acc_def
    using root terms
    by (auto simp add: strong_apder_acc_def rsimpStrong_dlform_closure_def)
qed

(* ===================================================================== *)
(* TARGET (still OPEN: needs `root_split` above).                           *)
(*   lemma strong_apder_acc_RALTS_singleton_cover:                          *)
(*     "strong_apder_acc (RALTS rs) k                                       *)
(*        \<subseteq> (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"                  *)
(* Discharge `root_split` (the B1/B2 escape bridge) and apply               *)
(* strong_apder_acc_RALTS_singleton_cover_if_root_split.                    *)
(* ===================================================================== *)

end
