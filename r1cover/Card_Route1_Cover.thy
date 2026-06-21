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

lemma rdistinct_set_subset_local:
  "set (rdistinct xs acc) \<subseteq> set xs"
  by (induct xs arbitrary: acc) auto

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

lemma rsimp7_SEQ_atom_RZERO_right [simp]:
  "rsimp7_SEQ_atom t RZERO = RZERO"
  by (cases t) (simp_all add: rsimp7_SEQ_atom_def split: prod.splits rrexp.splits)

lemma row_dlforms_rsimp7_rsimp_ALTs_subset_UN:
  assumes nf: "\<forall>p \<in> set ps. rtail_nf p"
  shows
  "row_dlforms (rsimp7_SEQ_atom (rsimp_ALTs ps) K) \<subseteq>
    (\<Union>p \<in> set ps. row_dlforms (rsimp7_SEQ_atom p K))"
proof (cases ps)
  case Nil
  then show ?thesis
    by (simp add: rsimp7_SEQ_atom_def)
next
  case (Cons p ps')
  note ps_eq0 = Cons
  then show ?thesis
  proof (cases ps')
    case Nil
    then show ?thesis
      using Cons by simp
  next
    case (Cons q qs)
    have ps_eq: "ps = p # q # qs"
      using ps_eq0 Cons by simp
    have rows_nf: "\<And>r. r \<in> set (p # q # qs) \<Longrightarrow> rtail_nf r"
      using nf ps_eq by auto
    show ?thesis
    proof (cases K)
      case RONE
      have stable: "\<And>r. r \<in> set (p # q # qs) \<Longrightarrow>
          rsimp7_SEQ_atom r RONE = r"
        by (rule rtail_nf_RONE_stable7) (rule rows_nf)
      show ?thesis
        using ps_eq RONE stable by auto
    qed (use ps_eq in
        \<open>simp_all add: rsimp7_SEQ_atom_def\<close>)
  qed
qed

lemma row_dlforms_rsimp7_member_subset_rsimp_ALTs:
  assumes t: "t \<in> set ps"
    and nf: "\<forall>p \<in> set ps. rtail_nf p"
  shows "row_dlforms (rsimp7_SEQ_atom t K) \<subseteq>
    row_dlforms (rsimp7_SEQ_atom (rsimp_ALTs ps) K)"
proof (cases ps)
  case Nil
  then show ?thesis
    using t by simp
next
  case (Cons p ps')
  note ps_eq0 = Cons
  then show ?thesis
  proof (cases ps')
    case Nil
    then show ?thesis
      using ps_eq0 t by simp
  next
    case (Cons q qs)
    have ps_eq: "ps = p # q # qs"
      using ps_eq0 Cons by simp
    have t_nf: "rtail_nf t"
      using nf t by blast
    show ?thesis
    proof (cases K)
      case RZERO
      then show ?thesis
        by simp
    next
      case RONE
      have stable: "rsimp7_SEQ_atom t RONE = t"
        by (rule rtail_nf_RONE_stable7[OF t_nf])
      show ?thesis
        using ps_eq t RONE stable by auto
    qed (use ps_eq t in \<open>auto simp add: rsimp7_SEQ_atom_def\<close>)
  qed
qed

lemma row_dlforms_rsimp7_single_subset_rsimp_ALTs_rflts:
  assumes t_nf: "rtail_nf t"
  shows "row_dlforms (rsimp7_SEQ_atom t K) \<subseteq>
    row_dlforms (rsimp7_SEQ_atom (rsimp_ALTs (rflts [t])) K)"
proof (cases t)
  case RZERO
  then show ?thesis by simp
next
  case (RALTS xs)
  show ?thesis
  proof (cases xs)
    case Nil
    then show ?thesis
      using RALTS by (cases K) simp_all
  next
    case (Cons p ps)
    note xs_eq = Cons
    then show ?thesis
    proof (cases ps)
      case Nil
      have p_nf: "rtail_nf p"
        using t_nf RALTS xs_eq Nil by simp
      then show ?thesis
      proof (cases K)
        case RONE
        have stable: "rsimp7_SEQ_atom p RONE = p"
          by (rule rtail_nf_RONE_stable7[OF p_nf])
        show ?thesis
          using RALTS xs_eq Nil RONE stable by simp
      qed (use RALTS xs_eq Nil in \<open>simp_all add: rsimp7_SEQ_atom_def\<close>)
    next
      case (Cons q qs)
      have xs_long: "xs = p # q # qs"
        using xs_eq Cons by simp
      then show ?thesis
        using RALTS xs_long by simp
    qed
  qed
qed (simp_all add: rsimp7_SEQ_atom_def)

lemma row_dlforms_rsimp7_member_subset_RALTS:
  assumes t: "t \<in> set ts"
    and nf: "rtail_nf t"
  shows "row_dlforms (rsimp7_SEQ_atom t K) \<subseteq>
    row_dlforms (rsimp7_SEQ_atom (RALTS ts) K)"
proof (cases K)
  case RZERO
  then show ?thesis by simp
next
  case RONE
  have stable: "rsimp7_SEQ_atom t RONE = t"
    by (rule rtail_nf_RONE_stable7[OF nf])
  then show ?thesis
    using t RONE stable by auto
qed (use t in \<open>auto simp add: rsimp7_SEQ_atom_def\<close>)

lemma rsimp_ALTs_RONE_member:
  assumes "rsimp_ALTs xs = RONE"
  shows "RONE \<in> set xs"
  using assms
  by (cases xs; cases "tl xs") auto

lemma rsimp_ALTs_RSTAR_member:
  assumes "rsimp_ALTs xs = RSTAR s"
  shows "RSTAR s \<in> set xs"
  using assms
  by (cases xs; cases "tl xs") auto

lemma row_dlforms_RONE_tail_credit:
  "row_dlforms (rsimp7_SEQ_atom RONE (rsimpStrong_raw k)) \<subseteq>
    row_dlforms (rsimpStrong_raw (rsimp4_SEQ_atom RONE k))"
  by simp

lemma row_dlforms_RSTAR_tail_credit_fix:
  assumes star_fix: "rsimpStrong_raw (RSTAR s) = RSTAR s"
  shows "row_dlforms (rsimp7_SEQ_atom (RSTAR s) (rsimpStrong_raw k)) \<subseteq>
    row_dlforms (rsimpStrong_raw (rsimp4_SEQ_atom (RSTAR s) k))"
proof (cases k)
  case RZERO
  then show ?thesis by simp
next
  case RONE
  then show ?thesis
    using star_fix by (simp add: rsimp7_SEQ_atom_def)
qed (use star_fix in \<open>simp_all add: rsimp7_SEQ_atom_def\<close>)

type_synonym tagged_row = "rrexp \<times> rrexp"

lemma map_snd_map_Pair [simp]:
  "map snd (map (Pair q) ys) = ys"
  by (induct ys) simp_all

lemma map_snd_comp_Pair [simp]:
  "map (snd \<circ> Pair q) ys = ys"
  by (induct ys) simp_all

lemma map_snd_tagged_initial [simp]:
  "map snd (map (\<lambda>q. (q, f q)) rs) = map f rs"
  by (induct rs) simp_all

lemma map_snd_comp_tagged_initial [simp]:
  "map (snd \<circ> (\<lambda>q. (q, f q))) rs = map f rs"
  by (induct rs) simp_all

fun tagged_rflts :: "tagged_row list \<Rightarrow> tagged_row list" where
  "tagged_rflts [] = []"
| "tagged_rflts ((q, RZERO) # xs) =
    tagged_rflts xs"
| "tagged_rflts ((q, RALTS ys) # xs) =
    map (\<lambda>y. (q, y)) ys @ tagged_rflts xs"
| "tagged_rflts ((q, t) # xs) =
    (q, t) # tagged_rflts xs"

lemma map_snd_tagged_rflts:
  "map snd (tagged_rflts xs) = rflts (map snd xs)"
  by (induct xs rule: tagged_rflts.induct) simp_all

lemma fst_tagged_rflts_subset:
  "set (map fst (tagged_rflts xs)) \<subseteq> set (map fst xs)"
  by (induct xs rule: tagged_rflts.induct) auto

definition tagged_prune_pair_raw ::
  "tagged_row \<Rightarrow> tagged_row \<Rightarrow> tagged_row" where
  "tagged_prune_pair_raw earlier later =
    (fst later, rsimpStrong_prune_pair_raw (snd earlier) (snd later))"

fun tagged_prune_against_rows_raw ::
  "tagged_row list \<Rightarrow> tagged_row \<Rightarrow> tagged_row" where
  "tagged_prune_against_rows_raw [] r = r"
| "tagged_prune_against_rows_raw (x # xs) r =
    tagged_prune_against_rows_raw xs (tagged_prune_pair_raw x r)"

fun tagged_prune_rows_acc_raw ::
  "tagged_row list \<Rightarrow> tagged_row list \<Rightarrow> tagged_row list" where
  "tagged_prune_rows_acc_raw seen [] = []"
| "tagged_prune_rows_acc_raw seen (r # rs) =
    (let r' = tagged_prune_against_rows_raw seen r
     in r' # tagged_prune_rows_acc_raw (r' # seen) rs)"

definition tagged_prune_rows_raw ::
  "tagged_row list \<Rightarrow> tagged_row list" where
  "tagged_prune_rows_raw rs =
    tagged_prune_rows_acc_raw [] rs"

lemma map_snd_tagged_prune_pair_raw:
  "snd (tagged_prune_pair_raw e r) =
    rsimpStrong_prune_pair_raw (snd e) (snd r)"
  by (simp add: tagged_prune_pair_raw_def)

lemma map_snd_tagged_prune_against_rows_raw:
  "snd (tagged_prune_against_rows_raw seen r) =
    rsimpStrong_prune_against_rows_raw (map snd seen) (snd r)"
  by (induct seen arbitrary: r)
    (simp_all add: tagged_prune_pair_raw_def)

lemma map_snd_tagged_prune_rows_acc_raw:
  "map snd (tagged_prune_rows_acc_raw seen rs) =
    rsimpStrong_prune_rows_acc_raw (map snd seen) (map snd rs)"
  by (induct rs arbitrary: seen)
    (simp_all add: Let_def map_snd_tagged_prune_against_rows_raw)

lemma map_snd_tagged_prune_rows_raw:
  "map snd (tagged_prune_rows_raw rs) =
    rsimpStrong_prune_rows_raw (map snd rs)"
  by (simp add: tagged_prune_rows_raw_def
      rsimpStrong_prune_rows_raw_def
      map_snd_tagged_prune_rows_acc_raw)

lemma fst_tagged_prune_pair_raw:
  "fst (tagged_prune_pair_raw e r) = fst r"
  by (simp add: tagged_prune_pair_raw_def)

lemma fst_tagged_prune_against_rows_raw:
  "fst (tagged_prune_against_rows_raw seen r) = fst r"
  by (induct seen arbitrary: r)
    (simp_all add: tagged_prune_pair_raw_def)

lemma fst_tagged_prune_rows_acc_raw_subset:
  "set (map fst (tagged_prune_rows_acc_raw seen rs)) \<subseteq>
    set (map fst rs)"
  by (induct rs arbitrary: seen)
    (auto simp add: Let_def fst_tagged_prune_against_rows_raw)

lemma fst_tagged_prune_rows_raw_subset:
  "set (map fst (tagged_prune_rows_raw xs)) \<subseteq> set (map fst xs)"
  unfolding tagged_prune_rows_raw_def
  by (rule fst_tagged_prune_rows_acc_raw_subset)

fun tagged_rdistinct ::
  "tagged_row list \<Rightarrow> rrexp set \<Rightarrow> tagged_row list" where
  "tagged_rdistinct [] acc = []"
| "tagged_rdistinct ((q, t) # xs) acc =
    (if t \<in> acc
     then tagged_rdistinct xs acc
     else (q, t) # tagged_rdistinct xs ({t} \<union> acc))"

lemma map_snd_tagged_rdistinct:
  "map snd (tagged_rdistinct xs acc) =
    rdistinct (map snd xs) acc"
  by (induct xs arbitrary: acc) auto

lemma fst_tagged_rdistinct_subset:
  "set (map fst (tagged_rdistinct xs acc)) \<subseteq> set (map fst xs)"
proof (induct xs arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    by (cases x) auto
qed

definition tagged_Strong_ALTs_rows ::
  "rrexp list \<Rightarrow> tagged_row list" where
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
      map_snd_tagged_prune_rows_raw)

lemma rsimpStrong_raw_RALTS_tagged_rows:
  "rsimpStrong_raw (RALTS rs) =
    rsimp_ALTs (map snd (tagged_Strong_ALTs_rows rs))"
  by (simp add: rsimpStrong_ALTs_raw_def
      map_snd_tagged_Strong_ALTs_rows)

lemma tagged_Strong_ALTs_rows_origin:
  assumes "(q, t) \<in> set (tagged_Strong_ALTs_rows rs)"
  shows "q \<in> set rs"
proof -
  let ?init = "tagged_rflts (map (\<lambda>q. (q, rsimpStrong_raw q)) rs)"
  let ?pruned = "tagged_prune_rows_raw ?init"
  let ?flat = "tagged_rflts ?pruned"
  have rd_sub: "fst ` set (tagged_rdistinct ?flat {}) \<subseteq>
      fst ` set ?flat"
    using fst_tagged_rdistinct_subset[of ?flat "{}"] by auto
  have flat_sub: "fst ` set ?flat \<subseteq> fst ` set ?pruned"
    using fst_tagged_rflts_subset[of ?pruned] by auto
  have prune_sub: "fst ` set ?pruned \<subseteq> fst ` set ?init"
    using fst_tagged_prune_rows_raw_subset[of ?init] by auto
  have init_sub: "fst ` set ?init \<subseteq> set rs"
    using fst_tagged_rflts_subset[of "map (\<lambda>q. (q, rsimpStrong_raw q)) rs"]
    by auto
  have q_mem: "q \<in> fst ` set (tagged_Strong_ALTs_rows rs)"
    using assms by force
  have all_sub:
      "fst ` set (tagged_Strong_ALTs_rows rs) \<subseteq> set rs"
    using rd_sub flat_sub prune_sub init_sub
    unfolding tagged_Strong_ALTs_rows_def
    by blast
  then show ?thesis
    using q_mem by blast
qed

lemma tagged_Strong_ALTs_rows_snd_rtail_nf:
  assumes "(q, t) \<in> set (tagged_Strong_ALTs_rows rs)"
  shows "rtail_nf t"
proof -
  let ?base = "rflts (map rsimpStrong_raw rs)"
  let ?pruned = "rsimpStrong_prune_rows_raw ?base"
  let ?flat = "rflts ?pruned"
  let ?rows = "rdistinct ?flat {}"
  have base_nf: "\<forall>x \<in> set ?base. rtail_nf x"
  proof (rule rtail_nf_rflts)
    show "\<forall>x \<in> set (map rsimpStrong_raw rs). rtail_nf x"
      using rtail_nf_rsimpStrong_raw by auto
  qed
  have pruned_nf: "\<forall>x \<in> set ?pruned. rtail_nf x"
    by (rule rtail_nf_rsimpStrong_prune_rows_raw[OF base_nf])
  have flat_nf: "\<forall>x \<in> set ?flat. rtail_nf x"
    by (rule rtail_nf_rflts[OF pruned_nf])
  have t_tagged: "t \<in> set (map snd (tagged_Strong_ALTs_rows rs))"
    using assms by force
  have t_row: "t \<in> set ?rows"
    using t_tagged by (simp add: map_snd_tagged_Strong_ALTs_rows)
  have "set ?rows \<subseteq> set ?flat"
    by (rule rdistinct_set_subset_local)
  then show ?thesis
    using flat_nf t_row by blast
qed

lemma row_dlforms_rsimpStrong_raw_RALTS_tagged_open:
  "row_dlforms (rsimp7_SEQ_atom (rsimpStrong_raw (RALTS rs)) K) \<subseteq>
    (\<Union>qt \<in> set (tagged_Strong_ALTs_rows rs).
      row_dlforms (rsimp7_SEQ_atom (snd qt) K))"
proof -
  let ?trs = "tagged_Strong_ALTs_rows rs"
  have nf: "\<forall>t \<in> set (map snd ?trs). rtail_nf t"
  proof
    fix t
    assume "t \<in> set (map snd ?trs)"
    then obtain q where "(q, t) \<in> set ?trs"
      by auto
    then show "rtail_nf t"
      by (rule tagged_Strong_ALTs_rows_snd_rtail_nf)
  qed
  have opened:
      "row_dlforms
        (rsimp7_SEQ_atom (rsimp_ALTs (map snd ?trs)) K) \<subseteq>
       (\<Union>t \<in> set (map snd ?trs).
          row_dlforms (rsimp7_SEQ_atom t K))"
    by (rule row_dlforms_rsimp7_rsimp_ALTs_subset_UN[OF nf])
  have root_eq:
      "rsimpStrong_raw (RALTS rs) = rsimp_ALTs (map snd ?trs)"
    by (rule rsimpStrong_raw_RALTS_tagged_rows)
  show ?thesis
    using opened
    unfolding root_eq
    by auto
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

lemma rsimpStrong_ALTs_raw_single_RONE [simp]:
  "rsimpStrong_ALTs_raw [RONE] = RONE"
  by (simp add: rsimpStrong_ALTs_raw_def rsimpStrong_prune_rows_raw_def)

lemma rsimpStrong_ALTs_raw_single_RCHAR [simp]:
  "rsimpStrong_ALTs_raw [RCHAR c] = RCHAR c"
  by (simp add: rsimpStrong_ALTs_raw_def rsimpStrong_prune_rows_raw_def)

lemma singleton_saa_ok_RZERO_raw:
  "singleton_saa_ok RZERO (rsimpStrong_raw RZERO)"
  by (simp add: singleton_saa_ok_def rsimp7_SEQ_atom_def)

lemma singleton_saa_ok_RONE_raw:
  "singleton_saa_ok RONE (rsimpStrong_raw RONE)"
  unfolding singleton_saa_ok_def
proof
  fix k
  have root:
      "row_dlforms (rsimpStrong_raw (rsimp4_SEQ_atom (RALTS [RONE]) k)) \<subseteq>
       strong_apder_acc (RALTS [RONE]) k"
    by (rule row_dlforms_singleton_root_subset_strong_apder_acc)
  show "row_dlforms (rsimp7_SEQ_atom (rsimpStrong_raw RONE)
      (rsimpStrong_raw k)) \<subseteq> strong_apder_acc (RALTS [RONE]) k"
    using root by (cases k) simp_all
qed

lemma singleton_saa_ok_RCHAR_raw:
  "singleton_saa_ok (RCHAR c) (rsimpStrong_raw (RCHAR c))"
  unfolding singleton_saa_ok_def
proof
  fix k
  have root:
      "row_dlforms
        (rsimpStrong_raw (rsimp4_SEQ_atom (RALTS [RCHAR c]) k)) \<subseteq>
       strong_apder_acc (RALTS [RCHAR c]) k"
    by (rule row_dlforms_singleton_root_subset_strong_apder_acc)
  show "row_dlforms (rsimp7_SEQ_atom (rsimpStrong_raw (RCHAR c))
      (rsimpStrong_raw k)) \<subseteq>
    strong_apder_acc (RALTS [RCHAR c]) k"
    using root by (cases k)
      (simp_all add: rsimpStrong_raw_rsimp4_SEQ_atom_RCHAR)
qed

lemma singleton_saa_ok_prune_pair_raw_if_suffix:
  assumes ok: "singleton_saa_ok q later"
    and later_nf: "rtail_nf later"
    and suffix:
      "\<And>k. row_dlforms (rsimpStrong_raw k) \<subseteq>
        strong_apder_acc (RALTS [q]) k"
  shows "singleton_saa_ok q
    (rsimpStrong_prune_pair_raw earlier later)"
  unfolding singleton_saa_ok_def
proof
  fix k
  have K_nf: "rtail_nf (rsimpStrong_raw k)"
    by (rule rtail_nf_rsimpStrong_raw)
  have split:
      "row_dlforms
        (rsimp7_SEQ_atom
          (rsimpStrong_prune_pair_raw earlier later)
          (rsimpStrong_raw k)) \<subseteq>
       row_dlforms (rsimp7_SEQ_atom later (rsimpStrong_raw k)) \<union>
       row_dlforms (rsimpStrong_raw k)"
    by (rule row_dlforms_rsimp7_prune_pair_subset_later_or_suffix
        [OF later_nf K_nf])
  have later:
      "row_dlforms (rsimp7_SEQ_atom later (rsimpStrong_raw k)) \<subseteq>
       strong_apder_acc (RALTS [q]) k"
    using ok unfolding singleton_saa_ok_def by blast
  have suff:
      "row_dlforms (rsimpStrong_raw k) \<subseteq>
       strong_apder_acc (RALTS [q]) k"
    by (rule suffix)
  show "row_dlforms
      (rsimp7_SEQ_atom
        (rsimpStrong_prune_pair_raw earlier later)
        (rsimpStrong_raw k)) \<subseteq>
    strong_apder_acc (RALTS [q]) k"
    using split later suff by blast
qed

lemma tagged_prune_pair_raw_preserves_singleton_saa_ok_if_suffix:
  assumes ok: "singleton_saa_ok (fst later) (snd later)"
    and later_nf: "rtail_nf (snd later)"
    and suffix:
      "\<And>k. row_dlforms (rsimpStrong_raw k) \<subseteq>
        strong_apder_acc (RALTS [fst later]) k"
  shows "singleton_saa_ok
    (fst (tagged_prune_pair_raw earlier later))
    (snd (tagged_prune_pair_raw earlier later))"
  using singleton_saa_ok_prune_pair_raw_if_suffix
    [OF ok later_nf suffix]
  by (simp add: tagged_prune_pair_raw_def)

lemma singleton_saa_ok_prune_against_rows_raw_if_suffix:
  assumes ok: "singleton_saa_ok q t"
    and t_nf: "rtail_nf t"
    and suffix:
      "\<And>k. row_dlforms (rsimpStrong_raw k) \<subseteq>
        strong_apder_acc (RALTS [q]) k"
  shows "singleton_saa_ok q
    (rsimpStrong_prune_against_rows_raw seen t)"
  using ok t_nf
proof (induct seen arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  let ?t' = "rsimpStrong_prune_pair_raw x t"
  have t'_ok: "singleton_saa_ok q ?t'"
    by (rule singleton_saa_ok_prune_pair_raw_if_suffix
        [OF Cons.prems(1) Cons.prems(2) suffix])
  have t'_nf: "rtail_nf ?t'"
    by (rule rtail_nf_rsimpStrong_prune_pair_raw[OF Cons.prems(2)])
  show ?case
    by simp (rule Cons.hyps[OF t'_ok t'_nf])
qed

lemma tagged_prune_against_rows_raw_preserves_singleton_saa_ok_if_suffix:
  assumes ok: "singleton_saa_ok (fst later) (snd later)"
    and later_nf: "rtail_nf (snd later)"
    and suffix:
      "\<And>k. row_dlforms (rsimpStrong_raw k) \<subseteq>
        strong_apder_acc (RALTS [fst later]) k"
  shows "singleton_saa_ok
    (fst (tagged_prune_against_rows_raw seen later))
    (snd (tagged_prune_against_rows_raw seen later))"
  using singleton_saa_ok_prune_against_rows_raw_if_suffix
    [OF ok later_nf suffix, of "map snd seen"]
  by (simp add: fst_tagged_prune_against_rows_raw
      map_snd_tagged_prune_against_rows_raw)

lemma singleton_saa_ok_flatten:
  assumes ok: "singleton_saa_ok q (RALTS xs)"
    and x: "x \<in> set xs"
    and nf: "rtail_nf x"
  shows "singleton_saa_ok q x"
  unfolding singleton_saa_ok_def
proof
  fix k
  have "row_dlforms (rsimp7_SEQ_atom x (rsimpStrong_raw k)) \<subseteq>
      row_dlforms (rsimp7_SEQ_atom (RALTS xs) (rsimpStrong_raw k))"
    by (rule row_dlforms_rsimp7_member_subset_RALTS[OF x nf])
  also have "... \<subseteq> strong_apder_acc (RALTS [q]) k"
    using ok unfolding singleton_saa_ok_def by blast
  finally show "row_dlforms (rsimp7_SEQ_atom x (rsimpStrong_raw k)) \<subseteq>
      strong_apder_acc (RALTS [q]) k" .
qed

lemma tagged_rdistinct_preserves_singleton_saa_ok:
  assumes ok: "\<forall>qt \<in> set xs. singleton_saa_ok (fst qt) (snd qt)"
  shows "\<forall>qt \<in> set (tagged_rdistinct xs acc).
    singleton_saa_ok (fst qt) (snd qt)"
  using ok
proof (induct xs arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons qt xs)
  then show ?case
    by (cases qt) auto
qed

lemma tagged_rdistinct_preserves_singleton_saa_key_credit:
  assumes ok: "\<forall>qt \<in> set xs. singleton_saa_key_credit (fst qt) (snd qt)"
  shows "\<forall>qt \<in> set (tagged_rdistinct xs acc).
    singleton_saa_key_credit (fst qt) (snd qt)"
  using ok
proof (induct xs arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons qt xs)
  then show ?case
    by (cases qt) auto
qed

lemma tagged_rdistinct_preserves_singleton_saa_scan_ok:
  assumes ok: "\<forall>qt \<in> set xs. singleton_saa_scan_ok (fst qt) (snd qt)"
  shows "\<forall>qt \<in> set (tagged_rdistinct xs acc).
    singleton_saa_scan_ok (fst qt) (snd qt)"
proof -
  have ok_saa: "\<forall>qt \<in> set (tagged_rdistinct xs acc).
      singleton_saa_ok (fst qt) (snd qt)"
    by (rule tagged_rdistinct_preserves_singleton_saa_ok)
      (use ok in \<open>auto simp add: singleton_saa_scan_ok_def\<close>)
  have ok_credit: "\<forall>qt \<in> set (tagged_rdistinct xs acc).
      singleton_saa_key_credit (fst qt) (snd qt)"
    by (rule tagged_rdistinct_preserves_singleton_saa_key_credit)
      (use ok in \<open>auto simp add: singleton_saa_scan_ok_def\<close>)
  show ?thesis
    using ok_saa ok_credit
    by (auto simp add: singleton_saa_scan_ok_def)
qed

lemma tagged_rflts_preserves_singleton_saa_ok:
  assumes ok: "\<forall>qt \<in> set xs. singleton_saa_ok (fst qt) (snd qt)"
    and nf: "\<forall>qt \<in> set (tagged_rflts xs). rtail_nf (snd qt)"
  shows "\<forall>qt \<in> set (tagged_rflts xs).
    singleton_saa_ok (fst qt) (snd qt)"
  using ok nf
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  obtain q t where a_def: "a = (q, t)"
    by (cases a) auto
  have tail_nf: "\<forall>qt \<in> set (tagged_rflts xs). rtail_nf (snd qt)"
  proof
    fix qt
    assume qt: "qt \<in> set (tagged_rflts xs)"
    have "qt \<in> set (tagged_rflts (a # xs))"
      using a_def qt by (cases t) auto
    then show "rtail_nf (snd qt)"
      using Cons.prems by blast
  qed
  have tail_ok: "\<forall>qt \<in> set (tagged_rflts xs).
      singleton_saa_ok (fst qt) (snd qt)"
    by (rule Cons.hyps) (use Cons.prems tail_nf in auto)
  show ?case
  proof (cases t)
    case RZERO
    then show ?thesis
      using a_def RZERO tail_ok by simp
  next
    case (RALTS ys)
    have alt_ok: "singleton_saa_ok q (RALTS ys)"
      using Cons.prems a_def RALTS by simp
    have ys_nf: "\<forall>y \<in> set ys. rtail_nf y"
    proof
      fix y
      assume y: "y \<in> set ys"
      have "(q, y) \<in> set (tagged_rflts (a # xs))"
        using a_def RALTS y by simp
      then have "rtail_nf (snd (q, y))"
        using Cons.prems by blast
      then show "rtail_nf y"
        by simp
    qed
    have ys_ok: "\<forall>y \<in> set ys. singleton_saa_ok q y"
    proof
      fix y
      assume y: "y \<in> set ys"
      show "singleton_saa_ok q y"
        by (rule singleton_saa_ok_flatten[OF alt_ok y])
          (use ys_nf y in auto)
    qed
    show ?thesis
      using a_def RALTS ys_ok tail_ok by auto
  qed (use Cons.prems a_def tail_ok in auto)
qed

(* TARGET (prove below; statement + steer in ROUTE_COVER.md):
   lemma strong_apder_acc_RALTS_singleton_cover:
     "strong_apder_acc (RALTS rs) k \<subseteq> (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
   Prove at the SAA level (fix-(a)); do NOT use the false dl_le_pruned_altseq route. *)

end
