theory Card_Route1_Bnd
  imports "Posix_Cubic.DirectUniverseCubic"
begin

(* ===================================================================== *)
(* LANE BOUNDARY — prove S1 + boundary_term_absorb.  See ROUTE_BND.md.    *)
(* Build: scripts\codex-isabelle-build-posix.ps1 -Session Posix_Card_Route1_Bnd *)
(* NO sorry. Build green. Fail-stop + report.                            *)
(* ===================================================================== *)

definition D :: "rrexp \<Rightarrow> rrexp \<Rightarrow> nat" where
  "D r k = card (strong_apder_acc r k - strong_apder_acc RONE k)"
definition single_root :: "rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "single_root q k =
     rsimpStrong_dlform_closure (rfrontier (rsimp4_SEQ_atom (RALTS [q]) k))"
definition single_term :: "rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "single_term q k =
     rsimpStrong_dlform_closure (apder_term_frontier_acc q k)"
definition boundary_excess :: "rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "boundary_excess t k =
     strong_apder_acc RONE (rsimp4_SEQ_atom t k) - strong_apder_acc RONE k"
definition root_excess :: "rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "root_excess t k = single_root t k - strong_apder_acc RONE k"
definition term_excess :: "rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "term_excess t k = single_term t k - strong_apder_acc RONE k"

fun bnd_spine :: "rrexp \<Rightarrow> rrexp list" where
  "bnd_spine (RSEQ p q) = p # bnd_spine q"
| "bnd_spine r = [r]"

datatype bnd_profile_pos =
    AtomPos rrexp
  | StarRun rrexp nat

fun bnd_profile_cons :: "rrexp \<Rightarrow> bnd_profile_pos list \<Rightarrow> bnd_profile_pos list" where
  "bnd_profile_cons (RSTAR r) [] = [StarRun r 1]"
| "bnd_profile_cons (RSTAR r) (StarRun s n # ps) =
    (if r = s then StarRun s (Suc n) # ps else StarRun r 1 # StarRun s n # ps)"
| "bnd_profile_cons (RSTAR r) (p # ps) = StarRun r 1 # p # ps"
| "bnd_profile_cons r ps = AtomPos r # ps"

fun bnd_profile_cons7_star :: "rrexp \<Rightarrow> bnd_profile_pos list \<Rightarrow> bnd_profile_pos list" where
  "bnd_profile_cons7_star r [] = [StarRun r 1]"
| "bnd_profile_cons7_star r (StarRun s n # ps) =
    (if r = s then StarRun s n # ps else StarRun r 1 # StarRun s n # ps)"
| "bnd_profile_cons7_star r (p # ps) = StarRun r 1 # p # ps"

fun bnd_profile_push :: "rrexp \<Rightarrow> bnd_profile_pos list \<Rightarrow> bnd_profile_pos list" where
  "bnd_profile_push (RSTAR r) [] = [StarRun r 1]"
| "bnd_profile_push (RSTAR r) (StarRun s n # ps) =
    (if r = s then StarRun s (Suc n) # ps else StarRun r 1 # StarRun s n # ps)"
| "bnd_profile_push (RSTAR r) (p # ps) = StarRun r 1 # p # ps"
| "bnd_profile_push r ps = AtomPos r # ps"

fun bnd_profile :: "rrexp \<Rightarrow> bnd_profile_pos list" where
  "bnd_profile (RSEQ p q) = bnd_profile_cons p (bnd_profile q)"
| "bnd_profile (RSTAR r) = [StarRun r 1]"
| "bnd_profile r = [AtomPos r]"

lemma bnd_profile_cons_nonempty [simp]:
  "bnd_profile_cons r ps \<noteq> []"
proof (cases r)
  case (RSTAR s)
  then show ?thesis
  proof (cases ps)
    case Nil
    then show ?thesis
      using RSTAR by simp
  next
    case (Cons p ps')
    then show ?thesis
      using RSTAR by (cases p) simp_all
  qed
qed simp_all

lemma bnd_profile_nonempty [simp]:
  "bnd_profile r \<noteq> []"
  by (cases r) simp_all

lemma bnd_profile_single_StarRun_pos:
  assumes "bnd_profile r = [StarRun s n]"
  shows "0 < n"
  using assms
proof (cases r)
  case (RSEQ p q)
  then show ?thesis
  proof (cases p)
    case (RSTAR u)
    obtain h hs where prof: "bnd_profile q = h # hs"
      using bnd_profile_nonempty[of q] by (cases "bnd_profile q") auto
    show ?thesis
      using assms RSEQ RSTAR prof by (cases h) (auto split: if_splits)
  qed (use assms RSEQ in auto)
qed (use assms in auto)

lemma bnd_profile_cons_profile_single_StarRun_gt_one:
  assumes "bnd_profile_cons r (bnd_profile q) = [StarRun s n]"
  shows "Suc 0 < n"
proof (cases r)
  case (RSTAR u)
  obtain h hs where prof: "bnd_profile q = h # hs"
    using bnd_profile_nonempty[of q] by (cases "bnd_profile q") auto
  show ?thesis
    using assms RSTAR prof
    by (cases h) (auto dest: bnd_profile_single_StarRun_pos split: if_splits)
qed (use assms in auto)

lemma bnd_profile_rsimp7_RSTAR_nontriv:
  assumes "k \<noteq> RZERO" "k \<noteq> RONE"
  shows "bnd_profile (rsimp7_SEQ_atom (RSTAR r) k) =
    bnd_profile_cons7_star r (bnd_profile k)"
  using assms
proof (cases k)
  case (RSEQ k1 k2)
  then show ?thesis
  proof (cases k1)
    case (RSTAR s)
    then show ?thesis
    proof (cases "bnd_profile k2")
      case Nil
      then show ?thesis
        using bnd_profile_nonempty[of k2] by simp
    next
      case (Cons h hs)
      then show ?thesis
        using RSEQ RSTAR
        by (cases h) (auto simp add: rsimp7_SEQ_atom_def split: if_splits)
    qed
  qed (simp_all add: rsimp7_SEQ_atom_def)
qed (simp_all add: rsimp7_SEQ_atom_def)

fun bnd_key_pos :: "bnd_profile_pos \<Rightarrow> bnd_profile_pos" where
  "bnd_key_pos (AtomPos r) = AtomPos r"
| "bnd_key_pos (StarRun r n) = StarRun r 1"

lemma bnd_key_pos_idem [simp]:
  "bnd_key_pos (bnd_key_pos p) = bnd_key_pos p"
  by (cases p) simp_all

lemma map_bnd_key_pos_idem [simp]:
  "map bnd_key_pos (map bnd_key_pos ps) = map bnd_key_pos ps"
  by (induction ps) simp_all

lemma map_bnd_key_pos_profile_cons_eq_single_Atom [simp]:
  "map bnd_key_pos (bnd_profile_cons r ps) = [AtomPos a] \<longleftrightarrow>
    (case r of RSTAR s \<Rightarrow> False | _ \<Rightarrow> r = a \<and> ps = [])"
proof (cases r)
  case (RSTAR s)
  then show ?thesis
  proof (cases ps)
    case Nil
    then show ?thesis
      using RSTAR by simp
  next
    case (Cons p ps')
    then show ?thesis
      using RSTAR by (cases p) simp_all
  qed
qed simp_all

lemma map_bnd_key_pos_profile_cons_profile_ne_single_Atom [simp]:
  "map bnd_key_pos (bnd_profile_cons r (bnd_profile q)) \<noteq> [AtomPos a]"
  "[AtomPos a] \<noteq> map bnd_key_pos (bnd_profile_cons r (bnd_profile q))"
proof -
  show left: "map bnd_key_pos (bnd_profile_cons r (bnd_profile q)) \<noteq> [AtomPos a]"
  proof
    assume "map bnd_key_pos (bnd_profile_cons r (bnd_profile q)) = [AtomPos a]"
    then have "(case r of RSTAR s \<Rightarrow> False | _ \<Rightarrow> r = a \<and> bnd_profile q = [])"
      by simp
    then show False
      by (cases r) simp_all
  qed
  show "[AtomPos a] \<noteq> map bnd_key_pos (bnd_profile_cons r (bnd_profile q))"
  proof
    assume "[AtomPos a] = map bnd_key_pos (bnd_profile_cons r (bnd_profile q))"
    then have "map bnd_key_pos (bnd_profile_cons r (bnd_profile q)) = [AtomPos a]"
      by simp
    then show False
      using left by contradiction
  qed
qed

lemma map_bnd_key_pos_star_cons_key_pos [simp]:
  "map bnd_key_pos (bnd_profile_cons (RSTAR r) [bnd_key_pos z]) =
    map bnd_key_pos (bnd_profile_cons (RSTAR r) [z])"
  by (cases z) simp_all

lemma map_bnd_key_pos_star_cons_map_key [simp]:
  "map bnd_key_pos (bnd_profile_cons (RSTAR r) (map bnd_key_pos ps)) =
    map bnd_key_pos (bnd_profile_cons (RSTAR r) ps)"
proof (cases ps)
  case Nil
  then show ?thesis
    by simp
next
  case (Cons p ps')
  then show ?thesis
    by (cases p) simp_all
qed

lemma map_bnd_key_pos_star_cons_Cons:
  assumes "bnd_key_pos p = bnd_key_pos q"
    and "map bnd_key_pos ps = map bnd_key_pos qs"
  shows "map bnd_key_pos (bnd_profile_cons (RSTAR r) (p # ps)) =
    map bnd_key_pos (bnd_profile_cons (RSTAR r) (q # qs))"
  using assms by (cases p; cases q) (auto split: if_splits)

lemma map_bnd_key_pos_star_cons_cong:
  assumes "map bnd_key_pos ps = map bnd_key_pos qs"
  shows "map bnd_key_pos (bnd_profile_cons (RSTAR r) ps) =
    map bnd_key_pos (bnd_profile_cons (RSTAR r) qs)"
  using assms
proof (cases ps)
  case Nil
  then show ?thesis
    using assms by (cases qs) auto
next
  case (Cons p ps')
  have ps_def: "ps = p # ps'"
    using Cons by simp
  then show ?thesis
  proof (cases qs)
    case Nil
    then show ?thesis
      using assms ps_def by auto
  next
    case (Cons q qs')
    have head: "bnd_key_pos p = bnd_key_pos q"
      using assms ps_def Cons by simp
    have tail: "map bnd_key_pos ps' = map bnd_key_pos qs'"
      using assms ps_def Cons by simp
    show ?thesis
      using ps_def Cons
      by (simp add: map_bnd_key_pos_star_cons_Cons[OF head tail])
  qed
qed

definition bnd_key :: "rrexp \<Rightarrow> bnd_profile_pos list" where
  "bnd_key r = map bnd_key_pos (bnd_profile r)"

fun bnd_counts_profile :: "bnd_profile_pos list \<Rightarrow> nat list" where
  "bnd_counts_profile [] = []"
| "bnd_counts_profile (AtomPos r # ps) = bnd_counts_profile ps"
| "bnd_counts_profile (StarRun r n # ps) = n # bnd_counts_profile ps"

definition bnd_counts :: "rrexp \<Rightarrow> nat list" where
  "bnd_counts r = bnd_counts_profile (bnd_profile r)"

definition bnd_lift_compatible :: "rrexp \<Rightarrow> rrexp \<Rightarrow> bool" where
  "bnd_lift_compatible x y \<longleftrightarrow>
     bnd_key x = bnd_key y \<and>
     list_all2 (\<lambda>m n. m \<le> n) (bnd_counts x) (bnd_counts y)"

fun bnd_counts_one_pos_le :: "nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "bnd_counts_one_pos_le [] [] = True"
| "bnd_counts_one_pos_le (m # ms) (n # ns) =
    (m \<le> n \<and>
      ((m = n \<and> bnd_counts_one_pos_le ms ns) \<or>
       (m < n \<and> ms = ns)))"
| "bnd_counts_one_pos_le _ _ = False"

lemma bnd_counts_one_pos_le_star_cons_key_pos [simp]:
  assumes "bnd_counts_one_pos_le [Suc 0] (bnd_counts_profile [z])"
  shows "bnd_counts_one_pos_le
      (bnd_counts_profile (bnd_profile_cons (RSTAR r) [bnd_key_pos z]))
      (bnd_counts_profile (bnd_profile_cons (RSTAR r) [z]))"
  using assms by (cases z) auto

lemma bnd_counts_one_pos_le_star_cons_map_key [simp]:
  assumes "bnd_counts_one_pos_le
      (bnd_counts_profile (map bnd_key_pos ps))
      (bnd_counts_profile ps)"
  shows "bnd_counts_one_pos_le
      (bnd_counts_profile (bnd_profile_cons (RSTAR r) (map bnd_key_pos ps)))
      (bnd_counts_profile (bnd_profile_cons (RSTAR r) ps))"
  using assms
proof (cases ps)
  case Nil
  then show ?thesis
    by simp
next
  case (Cons p ps')
  then show ?thesis
    using assms by (cases p) auto
qed

lemma bnd_counts_one_pos_le_star_cons_Cons:
  assumes "bnd_key_pos p = bnd_key_pos q"
    and "map bnd_key_pos ps = map bnd_key_pos qs"
    and "bnd_counts_one_pos_le
      (bnd_counts_profile (p # ps)) (bnd_counts_profile (q # qs))"
  shows "bnd_counts_one_pos_le
      (bnd_counts_profile (bnd_profile_cons (RSTAR r) (p # ps)))
      (bnd_counts_profile (bnd_profile_cons (RSTAR r) (q # qs)))"
  using assms by (cases p; cases q) (auto split: if_splits)

lemma bnd_counts_one_pos_le_star_cons_cong:
  assumes key: "map bnd_key_pos ps = map bnd_key_pos qs"
    and counts: "bnd_counts_one_pos_le
      (bnd_counts_profile ps) (bnd_counts_profile qs)"
  shows "bnd_counts_one_pos_le
      (bnd_counts_profile (bnd_profile_cons (RSTAR r) ps))
      (bnd_counts_profile (bnd_profile_cons (RSTAR r) qs))"
  using key counts
proof (cases ps)
  case Nil
  then show ?thesis
    using key counts by (cases qs) auto
next
  case (Cons p ps')
  have ps_def: "ps = p # ps'"
    using Cons by simp
  then show ?thesis
  proof (cases qs)
    case Nil
    then show ?thesis
      using key counts ps_def by auto
  next
    case (Cons q qs')
    have head: "bnd_key_pos p = bnd_key_pos q"
      using key ps_def Cons by simp
    have tail: "map bnd_key_pos ps' = map bnd_key_pos qs'"
      using key ps_def Cons by simp
    have counts': "bnd_counts_one_pos_le
      (bnd_counts_profile (p # ps')) (bnd_counts_profile (q # qs'))"
      using counts ps_def Cons by simp
    show ?thesis
      using ps_def Cons
      by (simp add: bnd_counts_one_pos_le_star_cons_Cons[OF head tail counts'])
  qed
qed

lemma bnd_profile_cons_profile_single_not_counts_le_one [simp]:
  assumes "bnd_profile_cons r (bnd_profile q) = [z]"
  shows "\<not> bnd_counts_one_pos_le (bnd_counts_profile [z]) [Suc 0]"
proof (cases z)
  case (AtomPos a)
  then have "map bnd_key_pos (bnd_profile_cons r (bnd_profile q)) = [AtomPos a]"
    using assms by simp
  then have "(case r of RSTAR s \<Rightarrow> False | _ \<Rightarrow> r = a \<and> bnd_profile q = [])"
    by simp
  then have False
    by (cases r) simp_all
  then show ?thesis
    by simp
next
  case (StarRun s n)
  then have "bnd_profile_cons r (bnd_profile q) = [StarRun s n]"
    using assms by simp
  then have "Suc 0 < n"
    by (rule bnd_profile_cons_profile_single_StarRun_gt_one)
  then show ?thesis
    using StarRun by simp
qed

lemma bnd_profile_cons7_star_cong:
  assumes key: "map bnd_key_pos ps = map bnd_key_pos qs"
    and counts: "bnd_counts_one_pos_le
      (bnd_counts_profile ps) (bnd_counts_profile qs)"
  shows "map bnd_key_pos (bnd_profile_cons7_star r ps) =
      map bnd_key_pos (bnd_profile_cons7_star r qs) \<and>
    bnd_counts_one_pos_le
      (bnd_counts_profile (bnd_profile_cons7_star r ps))
      (bnd_counts_profile (bnd_profile_cons7_star r qs))"
  using key counts
proof (cases ps)
  case Nil
  then show ?thesis
    using key counts by (cases qs) auto
next
  case (Cons p ps')
  have ps_def: "ps = p # ps'"
    using Cons by simp
  then show ?thesis
  proof (cases qs)
    case Nil
    then show ?thesis
      using key counts ps_def by auto
  next
    case (Cons q qs')
    show ?thesis
      using key counts ps_def Cons
      by (cases p; cases q) (auto split: if_splits)
  qed
qed

definition bnd_seam_lift :: "rrexp \<Rightarrow> rrexp \<Rightarrow> bool" where
  "bnd_seam_lift x y \<longleftrightarrow>
     bnd_key x = bnd_key y \<and>
     bnd_counts_one_pos_le (bnd_counts x) (bnd_counts y)"

lemma bnd_counts_list_all2_le_refl [simp]:
  "list_all2 (\<lambda>m n. m \<le> n) (xs :: nat list) xs"
  by (induction xs) simp_all

lemma bnd_counts_one_pos_le_refl [simp]:
  "bnd_counts_one_pos_le xs xs"
  by (induction xs) simp_all

lemma bnd_counts_one_pos_le_imp_list_all2:
  assumes "bnd_counts_one_pos_le xs ys"
  shows "list_all2 (\<lambda>m n. m \<le> n) xs ys"
  using assms
  by (induction xs ys rule: bnd_counts_one_pos_le.induct) auto

lemma bnd_seam_lift_imp_lift_compatible:
  assumes "bnd_seam_lift x y"
  shows "bnd_lift_compatible x y"
  using assms bnd_counts_one_pos_le_imp_list_all2
  by (simp add: bnd_seam_lift_def bnd_lift_compatible_def)

lemma bnd_seam_lift_rsimp4_same_head:
  assumes "bnd_seam_lift kX kY"
  shows "bnd_seam_lift
      (rsimp4_SEQ_atom p kX)
      (rsimp4_SEQ_atom p kY)"
  using assms
proof (induction p arbitrary: kX kY)
  case RZERO
  then show ?case
    by (simp add: bnd_seam_lift_def bnd_key_def bnd_counts_def)
next
  case RONE
  then show ?case
    by simp
next
  case (RCHAR c)
  then show ?case
    by (cases kX; cases kY)
      (auto simp add: bnd_seam_lift_def bnd_key_def bnd_counts_def
        split: rrexp.splits bnd_profile_pos.splits)
next
  case (RSEQ p1 p2)
  have tail:
    "bnd_seam_lift
      (rsimp4_SEQ_atom p2 kX)
      (rsimp4_SEQ_atom p2 kY)"
    by (rule RSEQ.IH(2)[OF RSEQ.prems])
  show ?case
    using RSEQ.IH(1)[OF tail] by simp
next
  case (RALTS rs)
  then show ?case
    by (cases kX; cases kY)
      (auto simp add: bnd_seam_lift_def bnd_key_def bnd_counts_def
        split: rrexp.splits bnd_profile_pos.splits)
next
  case (RSTAR r)
  then show ?case
    by (cases kX; cases kY)
      (auto simp add: bnd_seam_lift_def bnd_key_def bnd_counts_def
        intro: map_bnd_key_pos_star_cons_cong
          bnd_counts_one_pos_le_star_cons_cong
        split: rrexp.splits bnd_profile_pos.splits)
next
  case (RNTIMES r n)
  then show ?case
    by (cases kX; cases kY)
      (auto simp add: bnd_seam_lift_def bnd_key_def bnd_counts_def
        split: rrexp.splits bnd_profile_pos.splits)
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  then show ?case
    by (cases kX; cases kY)
      (auto simp add: bnd_seam_lift_def bnd_key_def bnd_counts_def
        split: rrexp.splits bnd_profile_pos.splits)
next
  case (RHALF r cs rep)
  then show ?case
    by (cases kX; cases kY)
      (auto simp add: bnd_seam_lift_def bnd_key_def bnd_counts_def
        split: rrexp.splits bnd_profile_pos.splits)
next
  case (RRESIDUE cs rep)
  then show ?case
    by (cases kX; cases kY)
      (auto simp add: bnd_seam_lift_def bnd_key_def bnd_counts_def
        split: rrexp.splits bnd_profile_pos.splits)
qed

lemma bnd_seam_lift_rsimp7_RSTAR_same_head:
  assumes "bnd_seam_lift kX kY"
  shows "bnd_seam_lift
      (rsimp7_SEQ_atom (RSTAR r) kX)
      (rsimp7_SEQ_atom (RSTAR r) kY)"
proof (cases "kX = RZERO \<or> kX = RONE \<or> kY = RZERO \<or> kY = RONE")
  case True
  then show ?thesis
    using assms
    by (cases kX; cases kY)
      (auto simp add: bnd_seam_lift_def bnd_key_def bnd_counts_def
        rsimp7_SEQ_atom_def split: rrexp.splits bnd_profile_pos.splits)
next
  case False
  then have nz:
    "kX \<noteq> RZERO" "kX \<noteq> RONE" "kY \<noteq> RZERO" "kY \<noteq> RONE"
    by auto
  have lift:
    "map bnd_key_pos (bnd_profile_cons7_star r (bnd_profile kX)) =
      map bnd_key_pos (bnd_profile_cons7_star r (bnd_profile kY)) \<and>
    bnd_counts_one_pos_le
      (bnd_counts_profile (bnd_profile_cons7_star r (bnd_profile kX)))
      (bnd_counts_profile (bnd_profile_cons7_star r (bnd_profile kY)))"
    using assms
    by (intro bnd_profile_cons7_star_cong)
      (simp_all add: bnd_seam_lift_def bnd_key_def bnd_counts_def)
  show ?thesis
    using lift
    by (simp add: bnd_seam_lift_def bnd_key_def bnd_counts_def
      bnd_profile_rsimp7_RSTAR_nontriv[OF nz(1,2)]
      bnd_profile_rsimp7_RSTAR_nontriv[OF nz(3,4)])
qed

lemma bnd_seam_lift_rsimp7_same_head:
  assumes "bnd_seam_lift kX kY"
  shows "bnd_seam_lift
      (rsimp7_SEQ_atom p kX)
      (rsimp7_SEQ_atom p kY)"
  using assms
proof (cases p)
  case RZERO
  then show ?thesis
    using bnd_seam_lift_rsimp4_same_head[OF assms, of RZERO]
    by (simp add: rsimp7_SEQ_atom_def)
next
  case RONE
  then show ?thesis
    using bnd_seam_lift_rsimp4_same_head[OF assms, of RONE]
    by (simp add: rsimp7_SEQ_atom_def)
next
  case (RCHAR c)
  then show ?thesis
    using bnd_seam_lift_rsimp4_same_head[OF assms, of "RCHAR c"]
    by (simp add: rsimp7_SEQ_atom_def)
next
  case (RSEQ p1 p2)
  then show ?thesis
    using bnd_seam_lift_rsimp4_same_head[OF assms, of "RSEQ p1 p2"]
    by (simp add: rsimp7_SEQ_atom_def)
next
  case (RALTS rs)
  then show ?thesis
    using bnd_seam_lift_rsimp4_same_head[OF assms, of "RALTS rs"]
    by (simp add: rsimp7_SEQ_atom_def)
next
  case (RSTAR r)
  then show ?thesis
    using bnd_seam_lift_rsimp7_RSTAR_same_head[OF assms] by simp
next
  case (RNTIMES r n)
  then show ?thesis
    using bnd_seam_lift_rsimp4_same_head[OF assms, of "RNTIMES r n"]
    by (simp add: rsimp7_SEQ_atom_def)
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  then show ?thesis
    using bnd_seam_lift_rsimp4_same_head[OF assms, of "RBACKREF4 r1 r2 r3 r4 cs"]
    by (simp add: rsimp7_SEQ_atom_def)
next
  case (RHALF r cs rep)
  then show ?thesis
    using bnd_seam_lift_rsimp4_same_head[OF assms, of "RHALF r cs rep"]
    by (simp add: rsimp7_SEQ_atom_def)
next
  case (RRESIDUE cs rep)
  then show ?thesis
    using bnd_seam_lift_rsimp4_same_head[OF assms, of "RRESIDUE cs rep"]
    by (simp add: rsimp7_SEQ_atom_def)
qed

lemma bnd_lift_compatible_rsimp7_same_head:
  assumes "bnd_seam_lift kX kY"
    and "rtail_nf p"
  shows "bnd_lift_compatible
       (rsimp7_SEQ_atom p kX)
       (rsimp7_SEQ_atom p kY)"
  by (rule bnd_seam_lift_imp_lift_compatible)
    (rule bnd_seam_lift_rsimp7_same_head[OF assms(1)])

lemma bnd_counts_one_pos_le_rsimp7_same_head:
  assumes "bnd_seam_lift kX kY"
    and "rtail_nf p"
  shows "bnd_counts_one_pos_le
      (bnd_counts (rsimp7_SEQ_atom p kX))
      (bnd_counts (rsimp7_SEQ_atom p kY))"
  using bnd_seam_lift_rsimp7_same_head[OF assms(1)]
  by (simp add: bnd_seam_lift_def)

lemma card_le_if_missing_in_image:
  fixes X Y :: "'a set"
  assumes "finite X" "finite Y" "X - Y \<subseteq> f ` (Y - X)"
  shows "card X \<le> card Y"
proof -
  have finXY: "finite (X \<inter> Y)" "finite (X - Y)" "finite (Y - X)"
    using assms(1,2) by simp_all
  have X: "card X = card (X \<inter> Y) + card (X - Y)"
  proof -
    have "X = (X \<inter> Y) \<union> (X - Y)"
      by auto
    then have "card X = card ((X \<inter> Y) \<union> (X - Y))"
      by simp
    also have "... = card (X \<inter> Y) + card (X - Y)"
      using finXY by (intro card_Un_disjoint) auto
    finally show ?thesis .
  qed
  have Y: "card Y = card (X \<inter> Y) + card (Y - X)"
  proof -
    have "Y = (X \<inter> Y) \<union> (Y - X)"
      by auto
    then have "card Y = card ((X \<inter> Y) \<union> (Y - X))"
      by simp
    also have "... = card (X \<inter> Y) + card (Y - X)"
      using finXY by (intro card_Un_disjoint) auto
    finally show ?thesis .
  qed
  have "card (X - Y) \<le> card (f ` (Y - X))"
    by (rule card_mono) (use assms finXY in auto)
  also have "... \<le> card (Y - X)"
    by (rule card_image_le) (use finXY in auto)
  finally show ?thesis
    using X Y by simp
qed

lemma card_le_of_card_diff_le:
  fixes X Y :: "'a set"
  assumes "finite X" "finite Y" "card (X - Y) \<le> card (Y - X)"
  shows "card X \<le> card Y"
proof -
  have finXY: "finite (X \<inter> Y)" "finite (X - Y)" "finite (Y - X)"
    using assms(1,2) by simp_all
  have X: "card X = card (X \<inter> Y) + card (X - Y)"
  proof -
    have "X = (X \<inter> Y) \<union> (X - Y)"
      by auto
    then have "card X = card ((X \<inter> Y) \<union> (X - Y))"
      by simp
    also have "... = card (X \<inter> Y) + card (X - Y)"
      using finXY by (intro card_Un_disjoint) auto
    finally show ?thesis .
  qed
  have Y: "card Y = card (X \<inter> Y) + card (Y - X)"
  proof -
    have "Y = (X \<inter> Y) \<union> (Y - X)"
      by auto
    then have "card Y = card ((X \<inter> Y) \<union> (Y - X))"
      by simp
    also have "... = card (X \<inter> Y) + card (Y - X)"
      using finXY by (intro card_Un_disjoint) auto
    finally show ?thesis .
  qed
  show ?thesis
    using assms(3) X Y by simp
qed

lemma card_diff_le_from_inj_on:
  fixes X Y :: "'a set"
  assumes finY: "finite (Y - X)"
    and maps: "\<And>x. x \<in> X - Y \<Longrightarrow> f x \<in> Y - X"
    and inj: "inj_on f (X - Y)"
  shows "card (X - Y) \<le> card (Y - X)"
proof -
  have "card (X - Y) = card (f ` (X - Y))"
    using inj by (rule card_image[symmetric])
  also have "... \<le> card (Y - X)"
    by (rule card_mono[OF finY]) (use maps in auto)
  finally show ?thesis .
qed

lemma finite_single_root [simp]:
  "finite (single_root q k)"
  by (simp add: single_root_def)

lemma finite_single_term [simp]:
  "finite (single_term q k)"
  by (simp add: single_term_def)

lemma finite_boundary_excess [simp]:
  "finite (boundary_excess t k)"
  by (simp add: boundary_excess_def)

lemma finite_root_excess [simp]:
  "finite (root_excess t k)"
  by (simp add: root_excess_def)

lemma finite_term_excess [simp]:
  "finite (term_excess t k)"
  by (simp add: term_excess_def)

lemma boundary_excess_le_root_excess_if_missing:
  assumes "boundary_excess t k - root_excess t k
      \<subseteq> rsimpStrong_raw ` (root_excess t k - boundary_excess t k)"
  shows "card (boundary_excess t k) \<le> card (root_excess t k)"
  by (rule card_le_if_missing_in_image[OF finite_boundary_excess finite_root_excess assms])

lemma boundary_term_absorb_if_missing_with_term:
  assumes "(boundary_excess t k \<union> term_excess t k)
      - (root_excess t k \<union> term_excess t k)
      \<subseteq> rsimpStrong_raw `
        ((root_excess t k \<union> term_excess t k)
          - (boundary_excess t k \<union> term_excess t k))"
  shows "card (boundary_excess t k \<union> term_excess t k)
      \<le> card (root_excess t k \<union> term_excess t k)"
  by (rule card_le_if_missing_in_image) (use assms in auto)

lemma boundary_missing_from_subset:
  assumes "boundary_excess t k \<subseteq> root_excess t k"
  shows "boundary_excess t k - root_excess t k
      \<subseteq> rsimpStrong_raw ` (root_excess t k - boundary_excess t k)"
  using assms by auto

lemma strong_apder_acc_singleton_decomp:
  "strong_apder_acc (RALTS [q]) k = single_root q k \<union> single_term q k"
  by (simp add: strong_apder_acc_def single_root_def single_term_def
      rsimpStrong_dlform_closure_def)

lemmas boundary_excess_defs =
  boundary_excess_def root_excess_def strong_apder_acc_def single_root_def
  rsimpStrong_dlform_closure_def rsimpStrong_ALTs_raw_def
  rsimpStrong_prune_rows_raw_def rsimpStrong_prune_pair_raw_def
  rsimp7_SEQ_atom_def Let_def

lemma boundary_excess_RZERO_subset:
  "boundary_excess RZERO k \<subseteq> root_excess RZERO k"
  by (cases k; simp_all add: boundary_excess_defs split: rrexp.splits)

lemma boundary_missing_RZERO:
  "boundary_excess RZERO k - root_excess RZERO k
      \<subseteq> rsimpStrong_raw ` (root_excess RZERO k - boundary_excess RZERO k)"
  by (rule boundary_missing_from_subset[OF boundary_excess_RZERO_subset])

lemma boundary_excess_RONE_subset:
  "boundary_excess RONE k \<subseteq> root_excess RONE k"
  by (cases k; simp_all add: boundary_excess_defs split: rrexp.splits)

lemma boundary_missing_RONE:
  "boundary_excess RONE k - root_excess RONE k
      \<subseteq> rsimpStrong_raw ` (root_excess RONE k - boundary_excess RONE k)"
  by (rule boundary_missing_from_subset[OF boundary_excess_RONE_subset])

lemma boundary_excess_RCHAR_subset:
  "boundary_excess (RCHAR c) k \<subseteq> root_excess (RCHAR c) k"
  by (cases k; simp_all add: boundary_excess_defs split: rrexp.splits)

lemma boundary_missing_RCHAR:
  "boundary_excess (RCHAR c) k - root_excess (RCHAR c) k
      \<subseteq> rsimpStrong_raw ` (root_excess (RCHAR c) k - boundary_excess (RCHAR c) k)"
  by (rule boundary_missing_from_subset[OF boundary_excess_RCHAR_subset])

lemma boundary_excess_RALTS_RZERO_subset:
  "boundary_excess (RALTS rs) RZERO \<subseteq> root_excess (RALTS rs) RZERO"
  by (simp add: boundary_excess_defs split: rrexp.splits)

lemma boundary_missing_RALTS_RZERO:
  "boundary_excess (RALTS rs) RZERO - root_excess (RALTS rs) RZERO
      \<subseteq> rsimpStrong_raw ` (root_excess (RALTS rs) RZERO - boundary_excess (RALTS rs) RZERO)"
  by (rule boundary_missing_from_subset[OF boundary_excess_RALTS_RZERO_subset])

lemma boundary_excess_RALTS_RONE_subset:
  "boundary_excess (RALTS rs) RONE \<subseteq> root_excess (RALTS rs) RONE"
  by (simp add: boundary_excess_defs split: rrexp.splits)

lemma boundary_missing_RALTS_RONE:
  "boundary_excess (RALTS rs) RONE - root_excess (RALTS rs) RONE
      \<subseteq> rsimpStrong_raw ` (root_excess (RALTS rs) RONE - boundary_excess (RALTS rs) RONE)"
  by (rule boundary_missing_from_subset[OF boundary_excess_RALTS_RONE_subset])

lemma rsimpStrong_raw_RALTS_single_RSTAR:
  "rsimpStrong_raw (RALTS [RSTAR r]) = rsimpStrong_raw (RSTAR r)"
  by (cases "rsimpStrong_raw r";
      simp_all add: rsimpStrong_ALTs_raw_def rsimpStrong_prune_rows_raw_def)

lemma rsimpStrong_ALTs_raw_single_RSTAR:
  "rsimpStrong_ALTs_raw (rflts [rsimpStrong_raw (RSTAR r)]) =
     rsimpStrong_raw (RSTAR r)"
  by (cases "rsimpStrong_raw r";
      simp_all add: rsimpStrong_ALTs_raw_def rsimpStrong_prune_rows_raw_def)

lemma single_root_RSTAR_RZERO_eq_boundary:
  "single_root (RSTAR r) RZERO =
     strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) RZERO)"
  by (simp add: single_root_def strong_apder_acc_def
      rsimpStrong_dlform_closure_def)

lemma single_root_RSTAR_RONE_eq_boundary:
  "single_root (RSTAR r) RONE =
     strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) RONE)"
  by (simp add: single_root_def strong_apder_acc_def
      rsimpStrong_dlform_closure_def rsimpStrong_raw_RALTS_single_RSTAR)

lemma single_root_RSTAR_RCHAR_eq_boundary:
  "single_root (RSTAR r) (RCHAR c) =
     strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) (RCHAR c))"
  by (cases "rsimpStrong_raw r";
      simp_all add: single_root_def strong_apder_acc_def
      rsimpStrong_dlform_closure_def rsimpStrong_ALTs_raw_def
      rsimpStrong_prune_rows_raw_def)

lemma single_root_RSTAR_RSEQ_eq_boundary:
  "single_root (RSTAR r) (RSEQ k1 k2) =
     strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) (RSEQ k1 k2))"
  by (cases "rsimpStrong_raw r";
      simp_all add: single_root_def strong_apder_acc_def
      rsimpStrong_dlform_closure_def rsimpStrong_ALTs_raw_def
      rsimpStrong_prune_rows_raw_def)

lemma single_root_RSTAR_RALTS_eq_boundary:
  "single_root (RSTAR r) (RALTS ks) =
     strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) (RALTS ks))"
  by (cases "rsimpStrong_raw r";
      simp_all add: single_root_def strong_apder_acc_def
      rsimpStrong_dlform_closure_def rsimpStrong_ALTs_raw_def
      rsimpStrong_prune_rows_raw_def)

lemma single_root_RSTAR_RSTAR_eq_boundary:
  "single_root (RSTAR r) (RSTAR s) =
     strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) (RSTAR s))"
  by (cases "rsimpStrong_raw r";
      simp_all add: single_root_def strong_apder_acc_def
      rsimpStrong_dlform_closure_def rsimpStrong_ALTs_raw_def
      rsimpStrong_prune_rows_raw_def rsimp7_SEQ_atom_def)

lemma single_root_RSTAR_RNTIMES_eq_boundary:
  "single_root (RSTAR r) (RNTIMES s n) =
     strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) (RNTIMES s n))"
  by (cases "rsimpStrong_raw r";
      simp_all add: single_root_def strong_apder_acc_def
      rsimpStrong_dlform_closure_def rsimpStrong_ALTs_raw_def
      rsimpStrong_prune_rows_raw_def)

lemma single_root_RSTAR_RBACKREF4_eq_boundary:
  "single_root (RSTAR r) (RBACKREF4 r1 r2 r3 r4 cs) =
     strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) (RBACKREF4 r1 r2 r3 r4 cs))"
  by (cases "rsimpStrong_raw r";
      simp_all add: single_root_def strong_apder_acc_def
      rsimpStrong_dlform_closure_def rsimpStrong_ALTs_raw_def
      rsimpStrong_prune_rows_raw_def)

lemma single_root_RSTAR_RHALF_eq_boundary:
  "single_root (RSTAR r) (RHALF s cs rep) =
     strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) (RHALF s cs rep))"
  by (cases "rsimpStrong_raw r";
      simp_all add: single_root_def strong_apder_acc_def
      rsimpStrong_dlform_closure_def rsimpStrong_ALTs_raw_def
      rsimpStrong_prune_rows_raw_def)

lemma single_root_RSTAR_RRESIDUE_eq_boundary:
  "single_root (RSTAR r) (RRESIDUE cs rep) =
     strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) (RRESIDUE cs rep))"
  by (cases "rsimpStrong_raw r";
      simp_all add: single_root_def strong_apder_acc_def
      rsimpStrong_dlform_closure_def rsimpStrong_ALTs_raw_def
      rsimpStrong_prune_rows_raw_def)

lemma single_root_RSTAR_eq_boundary:
  "single_root (RSTAR r) k =
     strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k)"
  by (cases k)
     (simp_all add: single_root_RSTAR_RZERO_eq_boundary
        single_root_RSTAR_RONE_eq_boundary
        single_root_RSTAR_RCHAR_eq_boundary
        single_root_RSTAR_RSEQ_eq_boundary
        single_root_RSTAR_RALTS_eq_boundary
        single_root_RSTAR_RSTAR_eq_boundary
        single_root_RSTAR_RNTIMES_eq_boundary
        single_root_RSTAR_RBACKREF4_eq_boundary
        single_root_RSTAR_RHALF_eq_boundary
        single_root_RSTAR_RRESIDUE_eq_boundary)

lemma boundary_excess_RSTAR_subset:
  "boundary_excess (RSTAR r) k \<subseteq> root_excess (RSTAR r) k"
  by (simp add: boundary_excess_def root_excess_def single_root_RSTAR_eq_boundary)

lemma boundary_missing_RSTAR:
  "boundary_excess (RSTAR r) k - root_excess (RSTAR r) k
      \<subseteq> rsimpStrong_raw ` (root_excess (RSTAR r) k - boundary_excess (RSTAR r) k)"
  by (rule boundary_missing_from_subset[OF boundary_excess_RSTAR_subset])

lemma boundary_excess_RBACKREF4_subset:
  "boundary_excess (RBACKREF4 r1 r2 r3 r4 cs) k
      \<subseteq> root_excess (RBACKREF4 r1 r2 r3 r4 cs) k"
  by (cases k; simp_all add: boundary_excess_defs split: rrexp.splits)

lemma boundary_missing_RBACKREF4:
  "boundary_excess (RBACKREF4 r1 r2 r3 r4 cs) k
      - root_excess (RBACKREF4 r1 r2 r3 r4 cs) k
      \<subseteq> rsimpStrong_raw `
        (root_excess (RBACKREF4 r1 r2 r3 r4 cs) k
          - boundary_excess (RBACKREF4 r1 r2 r3 r4 cs) k)"
  by (rule boundary_missing_from_subset[OF boundary_excess_RBACKREF4_subset])

lemma boundary_excess_RHALF_subset:
  "boundary_excess (RHALF r cs rep) k \<subseteq> root_excess (RHALF r cs rep) k"
  by (cases k; simp_all add: boundary_excess_defs split: rrexp.splits)

lemma boundary_missing_RHALF:
  "boundary_excess (RHALF r cs rep) k - root_excess (RHALF r cs rep) k
      \<subseteq> rsimpStrong_raw `
        (root_excess (RHALF r cs rep) k - boundary_excess (RHALF r cs rep) k)"
  by (rule boundary_missing_from_subset[OF boundary_excess_RHALF_subset])

lemma boundary_excess_RRESIDUE_subset:
  "boundary_excess (RRESIDUE cs rep) k \<subseteq> root_excess (RRESIDUE cs rep) k"
  by (cases k; simp_all add: boundary_excess_defs split: rrexp.splits)

lemma boundary_missing_RRESIDUE:
  "boundary_excess (RRESIDUE cs rep) k - root_excess (RRESIDUE cs rep) k
      \<subseteq> rsimpStrong_raw `
        (root_excess (RRESIDUE cs rep) k - boundary_excess (RRESIDUE cs rep) k)"
  by (rule boundary_missing_from_subset[OF boundary_excess_RRESIDUE_subset])

lemma boundary_excess_RNTIMES_subset:
  "boundary_excess (RNTIMES r n) k \<subseteq> root_excess (RNTIMES r n) k"
  by (cases k; simp_all add: boundary_excess_defs split: rrexp.splits)

lemma boundary_missing_RNTIMES:
  "boundary_excess (RNTIMES r n) k - root_excess (RNTIMES r n) k
      \<subseteq> rsimpStrong_raw `
        (root_excess (RNTIMES r n) k - boundary_excess (RNTIMES r n) k)"
  by (rule boundary_missing_from_subset[OF boundary_excess_RNTIMES_subset])

(* TARGETS (prove below; statements + steer in ROUTE_BND.md):
   (S1)  card (strong_apder_acc RONE (rsimp4_SEQ_atom t k) - strong_apder_acc RONE k)
           <= card (single_root t k - strong_apder_acc RONE k)
   (boundary_term_absorb)
         card ((strong_apder_acc RONE (rsimp4_SEQ_atom t k) - strong_apder_acc RONE k)
               \<union> (single_term t k - strong_apder_acc RONE k))
           <= D (RALTS [t]) k
   Prove boundary_term_absorb VIA S1 (boundary-excess <= root-excess, collision-free),
   NOT via a raw injection. *)

end
