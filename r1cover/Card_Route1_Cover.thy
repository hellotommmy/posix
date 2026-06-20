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
(* TAGGED PROVENANCE SCAFFOLD (sound; verdict_G2 §1).  Each row carries its  *)
(* origin branch q so the cross-prune sigma7 escape can be routed to q's ACC *)
(* carrier.  Projections show the tagged pipeline mirrors the real           *)
(* rsimpStrong_raw (RALTS rs) row list; origin shows every tag is a branch.  *)
(* ===================================================================== *)

type_synonym tagged_row = "rrexp \<times> rrexp"

fun tagged_rflts :: "tagged_row list \<Rightarrow> tagged_row list" where
  "tagged_rflts [] = []"
| "tagged_rflts ((q, RZERO) # xs) = tagged_rflts xs"
| "tagged_rflts ((q, RALTS ys) # xs) = map (\<lambda>y. (q, y)) ys @ tagged_rflts xs"
| "tagged_rflts ((q, t) # xs) = (q, t) # tagged_rflts xs"

lemma map_snd_tagged_rflts:
  "map snd (tagged_rflts xs) = rflts (map snd xs)"
  by (induction xs rule: tagged_rflts.induct) (auto simp add: comp_def)

lemma fst_tagged_rflts_subset:
  "set (map fst (tagged_rflts xs)) \<subseteq> set (map fst xs)"
  by (induction xs rule: tagged_rflts.induct) auto

definition tagged_prune_pair_raw :: "tagged_row \<Rightarrow> tagged_row \<Rightarrow> tagged_row" where
  "tagged_prune_pair_raw earlier later =
     (fst later, rsimpStrong_prune_pair_raw (snd earlier) (snd later))"

fun tagged_prune_against_rows_raw :: "tagged_row list \<Rightarrow> tagged_row \<Rightarrow> tagged_row" where
  "tagged_prune_against_rows_raw [] r = r"
| "tagged_prune_against_rows_raw (x # xs) r =
     tagged_prune_against_rows_raw xs (tagged_prune_pair_raw x r)"

fun tagged_prune_rows_acc_raw :: "tagged_row list \<Rightarrow> tagged_row list \<Rightarrow> tagged_row list" where
  "tagged_prune_rows_acc_raw seen [] = []"
| "tagged_prune_rows_acc_raw seen (r # rs) =
     (let r' = tagged_prune_against_rows_raw seen r
      in r' # tagged_prune_rows_acc_raw (r' # seen) rs)"

definition tagged_prune_rows_raw :: "tagged_row list \<Rightarrow> tagged_row list" where
  "tagged_prune_rows_raw rs = tagged_prune_rows_acc_raw [] rs"

lemma snd_tagged_prune_pair_raw:
  "snd (tagged_prune_pair_raw e r) =
     rsimpStrong_prune_pair_raw (snd e) (snd r)"
  by (simp add: tagged_prune_pair_raw_def)

lemma fst_tagged_prune_pair_raw:
  "fst (tagged_prune_pair_raw e r) = fst r"
  by (simp add: tagged_prune_pair_raw_def)

lemma snd_tagged_prune_against_rows_raw:
  "snd (tagged_prune_against_rows_raw seen r) =
     rsimpStrong_prune_against_rows_raw (map snd seen) (snd r)"
  by (induction seen arbitrary: r)
    (simp_all add: snd_tagged_prune_pair_raw tagged_prune_pair_raw_def)

lemma fst_tagged_prune_against_rows_raw:
  "fst (tagged_prune_against_rows_raw seen r) = fst r"
  by (induction seen arbitrary: r)
    (simp_all add: fst_tagged_prune_pair_raw)

lemma map_snd_tagged_prune_rows_acc_raw:
  "map snd (tagged_prune_rows_acc_raw seen rs) =
     rsimpStrong_prune_rows_acc_raw (map snd seen) (map snd rs)"
  by (induction rs arbitrary: seen)
    (simp_all add: Let_def snd_tagged_prune_against_rows_raw)

lemma map_snd_tagged_prune_rows_raw:
  "map snd (tagged_prune_rows_raw rs) =
     rsimpStrong_prune_rows_raw (map snd rs)"
  by (simp add: tagged_prune_rows_raw_def rsimpStrong_prune_rows_raw_def
      map_snd_tagged_prune_rows_acc_raw)

lemma fst_tagged_prune_rows_acc_raw_subset:
  "set (map fst (tagged_prune_rows_acc_raw seen rs)) \<subseteq> set (map fst rs)"
proof (induction rs arbitrary: seen)
  case Nil
  then show ?case by simp
next
  case (Cons r rs)
  have "fst (tagged_prune_against_rows_raw seen r) = fst r"
    by (rule fst_tagged_prune_against_rows_raw)
  then show ?case
    using Cons.IH[of "tagged_prune_against_rows_raw seen r # seen"]
    by (auto simp add: Let_def)
qed

lemma fst_tagged_prune_rows_raw_subset:
  "set (map fst (tagged_prune_rows_raw rs)) \<subseteq> set (map fst rs)"
  unfolding tagged_prune_rows_raw_def
  by (rule fst_tagged_prune_rows_acc_raw_subset)

fun tagged_rdistinct :: "tagged_row list \<Rightarrow> rrexp set \<Rightarrow> tagged_row list" where
  "tagged_rdistinct [] acc = []"
| "tagged_rdistinct ((q, t) # xs) acc =
     (if t \<in> acc
      then tagged_rdistinct xs acc
      else (q, t) # tagged_rdistinct xs ({t} \<union> acc))"

lemma map_snd_tagged_rdistinct:
  "map snd (tagged_rdistinct xs acc) = rdistinct (map snd xs) acc"
  by (induction xs arbitrary: acc) auto

lemma fst_tagged_rdistinct_subset:
  "set (map fst (tagged_rdistinct xs acc)) \<subseteq> set (map fst xs)"
  by (induction xs acc rule: tagged_rdistinct.induct) auto

definition tagged_Strong_ALTs_rows :: "rrexp list \<Rightarrow> tagged_row list" where
  "tagged_Strong_ALTs_rows rs =
     tagged_rdistinct
       (tagged_rflts
         (tagged_prune_rows_raw
           (tagged_rflts (map (\<lambda>q. (q, rsimpStrong_raw q)) rs))))
       {}"

lemma map_snd_tagged_Strong_ALTs_rows:
  "map snd (tagged_Strong_ALTs_rows rs) =
     rdistinct
       (rflts
         (rsimpStrong_prune_rows_raw
           (rflts (map rsimpStrong_raw rs))))
       {}"
  unfolding tagged_Strong_ALTs_rows_def
  by (simp add: map_snd_tagged_rdistinct map_snd_tagged_rflts
      map_snd_tagged_prune_rows_raw comp_def)

lemma rsimpStrong_raw_RALTS_tagged_rows:
  "rsimpStrong_raw (RALTS rs) =
     rsimp_ALTs (map snd (tagged_Strong_ALTs_rows rs))"
  by (simp add: rsimpStrong_ALTs_raw_def map_snd_tagged_Strong_ALTs_rows)

lemma tagged_Strong_ALTs_rows_origin:
  assumes "(q, t) \<in> set (tagged_Strong_ALTs_rows rs)"
  shows "q \<in> set rs"
proof -
  have "q \<in> set (map fst (tagged_Strong_ALTs_rows rs))"
    using assms by (metis fst_conv image_eqI list.set_map)
  also have "set (map fst (tagged_Strong_ALTs_rows rs)) \<subseteq>
      set (map fst (map (\<lambda>q. (q, rsimpStrong_raw q)) rs))"
    unfolding tagged_Strong_ALTs_rows_def
    using fst_tagged_rdistinct_subset fst_tagged_rflts_subset
      fst_tagged_prune_rows_raw_subset by (meson subset_trans)
  also have "... = set rs" by (simp add: comp_def)
  finally show ?thesis .
qed

(* ===================================================================== *)
(* Routing bricks for the ACC carrier (Carrier I).                          *)
(* ===================================================================== *)

(* parent ACC closure distributes over the RALTS branches *)
lemma rsimpStrong_dlform_closure_apder_term_frontier_acc_RALTS_distrib:
  "rsimpStrong_dlform_closure (apder_term_frontier_acc (RALTS rs) k) =
     (\<Union>q \<in> set rs. rsimpStrong_dlform_closure (apder_term_frontier_acc q k))"
  by (auto simp add: rsimpStrong_dlform_closure_def)

(* the ACC closure of any r is contained in its strong carrier *)
lemma rsimpStrong_dlform_closure_apder_term_frontier_acc_subset_strong_apder_acc:
  "rsimpStrong_dlform_closure (apder_term_frontier_acc q k) \<subseteq> strong_apder_acc q k"
  unfolding strong_apder_acc_def
  by (rule rsimpStrong_dlform_closure_mono) auto

(* singleton ACC carrier coincides with the bare-branch ACC carrier *)
lemma strong_apder_acc_RALTS_singleton_acc_eq:
  "rsimpStrong_dlform_closure (apder_term_frontier_acc (RALTS [q]) k) =
     rsimpStrong_dlform_closure (apder_term_frontier_acc q k)"
  by simp

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
(* COVER ROOT reduced to the per-tagged-row SAA invariant.  Using the       *)
(* provenance scaffold, the parent ROOT opening decomposes into the strong   *)
(* openings of the tagged final rows; if each tagged row (q,t) opens into    *)
(* its origin branch's full carrier strong_apder_acc (RALTS[q]) k, the whole *)
(* cover root follows.  This isolates the open wall to exactly `inv` (the    *)
(* B1/B2 escape routing), for the generic tail S k \<notin> {RZERO,RONE}.            *)
(* ===================================================================== *)

lemma cover_root_from_tagged_invariant:
  assumes Sk0: "rsimpStrong_raw k \<noteq> RZERO"
    and Sk1: "rsimpStrong_raw k \<noteq> RONE"
    and inv: "\<And>q t. (q, t) \<in> set (tagged_Strong_ALTs_rows rs) \<Longrightarrow>
        row_dlforms (rsimp7_SEQ_atom t (rsimpStrong_raw k)) \<subseteq>
          strong_apder_acc (RALTS [q]) k"
  shows "row_dlforms (rsimpStrong_raw (RSEQ (RALTS rs) k)) \<subseteq>
           (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
proof -
  define ROWS where "ROWS = map snd (tagged_Strong_ALTs_rows rs)"
  have rows_eq:
    "ROWS = rdistinct
       (rflts (rsimpStrong_prune_rows_raw (rflts (map rsimpStrong_raw rs)))) {}"
    unfolding ROWS_def by (rule map_snd_tagged_Strong_ALTs_rows)
  have nf_map: "\<forall>t \<in> set (map rsimpStrong_raw rs). rtail_nf t"
    using rtail_nf_rsimpStrong_raw by auto
  have nf_flat1: "\<forall>t \<in> set (rflts (map rsimpStrong_raw rs)). rtail_nf t"
    by (rule rtail_nf_rflts[OF nf_map])
  have nf_prune:
    "\<forall>t \<in> set (rsimpStrong_prune_rows_raw
        (rflts (map rsimpStrong_raw rs))). rtail_nf t"
    by (rule rtail_nf_rsimpStrong_prune_rows_raw[OF nf_flat1])
  have nf_flat2:
    "\<forall>t \<in> set (rflts (rsimpStrong_prune_rows_raw
        (rflts (map rsimpStrong_raw rs)))). rtail_nf t"
    by (rule rtail_nf_rflts[OF nf_prune])
  have rows_nf: "\<forall>t \<in> set ROWS. rtail_nf t"
    using rows_eq nf_flat2 set_rdistinct_subset[of "rflts (rsimpStrong_prune_rows_raw
        (rflts (map rsimpStrong_raw rs)))" _ "{}"]
    by auto
  have step1:
    "rsimpStrong_raw (RSEQ (RALTS rs) k) =
       rsimp7_SEQ_atom (rsimp_ALTs ROWS) (rsimpStrong_raw k)"
    by (simp add: rsimpStrong_ALTs_raw_def map_snd_tagged_Strong_ALTs_rows ROWS_def)
  have sub_RALTS:
    "row_dlforms (rsimp7_SEQ_atom (rsimp_ALTs ROWS) (rsimpStrong_raw k)) \<subseteq>
       row_dlforms (rsimp7_SEQ_atom (RALTS ROWS) (rsimpStrong_raw k))"
    by (rule row_dlforms_rsimp7_rsimp_ALTs_subset_RALTS[OF subset_refl rows_nf])
  have eqK:
    "rsimp4_SEQ_atom (RALTS ROWS) (rsimpStrong_raw k) =
       RSEQ (RALTS ROWS) (rsimpStrong_raw k)"
    using Sk0 Sk1 by (cases "rsimpStrong_raw k") auto
  have open_eq:
    "row_dlforms (rsimp7_SEQ_atom (RALTS ROWS) (rsimpStrong_raw k)) =
       (\<Union>t \<in> set ROWS. row_dlforms (rsimp7_SEQ_atom t (rsimpStrong_raw k)))"
    by (simp add: rsimp7_SEQ_atom_RALTS eqK)
  have each:
    "(\<Union>t \<in> set ROWS. row_dlforms (rsimp7_SEQ_atom t (rsimpStrong_raw k))) \<subseteq>
       (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
  proof (rule UN_least)
    fix t assume tin: "t \<in> set ROWS"
    then obtain p where p: "p \<in> set (tagged_Strong_ALTs_rows rs)" "snd p = t"
      unfolding ROWS_def by auto
    obtain q where pq: "p = (q, t)" using p(2) by (cases p) auto
    have q_in: "q \<in> set rs"
      using tagged_Strong_ALTs_rows_origin p(1) pq by simp
    have "row_dlforms (rsimp7_SEQ_atom t (rsimpStrong_raw k)) \<subseteq>
        strong_apder_acc (RALTS [q]) k"
      using inv p(1) pq by simp
    then show "row_dlforms (rsimp7_SEQ_atom t (rsimpStrong_raw k)) \<subseteq>
        (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
      using q_in by blast
  qed
  have "row_dlforms (rsimpStrong_raw (RSEQ (RALTS rs) k)) =
      row_dlforms (rsimp7_SEQ_atom (rsimp_ALTs ROWS) (rsimpStrong_raw k))"
    by (rule arg_cong[where f = row_dlforms, OF step1])
  also have "... \<subseteq>
      row_dlforms (rsimp7_SEQ_atom (RALTS ROWS) (rsimpStrong_raw k))"
    by (rule sub_RALTS)
  also have "... =
      (\<Union>t \<in> set ROWS. row_dlforms (rsimp7_SEQ_atom t (rsimpStrong_raw k)))"
    by (rule open_eq)
  also have "... \<subseteq> (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
    by (rule each)
  finally show ?thesis .
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
(* FULL cover from the single per-row invariant `inv` (generic k and S k).   *)
(* Assembles the ROOT (cover_root_from_tagged_invariant, via the generic-k    *)
(* frontier normalisation) with the green TERM carrier.  This reduces L1 (in  *)
(* the generic regime) to EXACTLY `inv`: every tagged final row opens into    *)
(* its origin branch's full carrier.                                          *)
(* ===================================================================== *)

lemma strong_apder_acc_RALTS_singleton_cover_from_inv:
  assumes k0: "k \<noteq> RZERO" and k1: "k \<noteq> RONE"
    and Sk0: "rsimpStrong_raw k \<noteq> RZERO" and Sk1: "rsimpStrong_raw k \<noteq> RONE"
    and inv: "\<And>q t. (q, t) \<in> set (tagged_Strong_ALTs_rows rs) \<Longrightarrow>
        row_dlforms (rsimp7_SEQ_atom t (rsimpStrong_raw k)) \<subseteq>
          strong_apder_acc (RALTS [q]) k"
  shows "strong_apder_acc (RALTS rs) k \<subseteq>
    (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
proof -
  have root:
    "rsimpStrong_dlform_closure (rfrontier (rsimp4_SEQ_atom (RALTS rs) k)) \<subseteq>
       (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
    using cover_root_from_tagged_invariant[OF Sk0 Sk1 inv]
    by (simp add: rsimpStrong_dlform_closure_rfrontier_RALTS_seq_eq[OF k0 k1])
  have terms:
    "rsimpStrong_dlform_closure (apder_term_frontier_acc (RALTS rs) k) \<subseteq>
       (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
    by (rule strong_apder_acc_RALTS_terms_singleton_cover)
  show ?thesis
    unfolding strong_apder_acc_def
    using root terms
    by (auto simp add: strong_apder_acc_def rsimpStrong_dlform_closure_def)
qed

(* ===================================================================== *)
(* TARGET — strong_apder_acc_RALTS_singleton_cover — remains OPEN.           *)
(* It is now reduced to a SINGLE goal, `inv`:                                *)
(*   \<And>q t. (q,t) \<in> set (tagged_Strong_ALTs_rows rs) \<Longrightarrow>                     *)
(*     row_dlforms (rsimp7_SEQ_atom t (rsimpStrong_raw k))                   *)
(*       \<subseteq> strong_apder_acc (RALTS [q]) k                                    *)
(* (plus the degenerate tails k or S k \<in> {RZERO,RONE}, handled by the green   *)
(* base lemmas / no-tail row_dlforms_rsimpStrong_raw_RALTS_subsetI).         *)
(*                                                                            *)
(* `inv` is the [VALIDATED] B1/B2 statement at row level: each tagged final  *)
(* row of the strong-pruned alternation opens (against S k) into its origin   *)
(* branch's carrier.  B1 (surviving root) is the easy half; B2 is the wall:   *)
(* a cross-prune sigma7-collapse row (bare RSTAR s, or a RONE-headed tail     *)
(* escape) must route into the branch ACC carrier.  The discharging fact is   *)
(* apder_term_frontier_acc_eq:                                                *)
(*   apder_term_frontier_acc q k = (\<Union>p\<in>apder_terms q. rfrontier (rsimp4_SEQ_atom p k)) *)
(* together with apder_terms (RSTAR s) = (\<lambda>p. rsimp4_SEQ_atom p (RSTAR s)) ` apder_terms s; *)
(* the missing connector (GAP) is: the prune sigma7 escape from a row of S q  *)
(* is rsimp4_SEQ_atom p (S k) for some p \<in> apder_terms q.  This is the lone   *)
(* remaining hard lemma; prove it, then `inv` follows by pipeline tracking    *)
(* over tagged_Strong_ALTs_rows and the cover closes via                      *)
(* strong_apder_acc_RALTS_singleton_cover_from_inv.                          *)
(* ===================================================================== *)

end
