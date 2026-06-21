(*  Route-2 / N-route — Wave 1B: the normalizer N (= nstrong) + nalts.
    Owner: norm/01-alpha lane.  Session: Posix_Norm.

    N normalises a regex by collapsing ALL adjacent equal stars on the sequence spine
    (via the associative append nplug from NormalizedAppend), unlike the lexer's S
    (= rsimpStrong_raw), which collapses only a LEADING a*.a*.  nalts mirrors the
    lexer's cross-row prune but re-plugs via nplug (so it collapses the a*.a* that
    sigma7 leaves), matching experiments/norm/norm_model.py.

    Target of this brick: nstrong_rsimp4_shadow :  N (rsimp4_SEQ_atom r k) = nplug (N r) (N k)
    (kill-criterion #1; validated 0/80210; reduces to the GREEN nplug_assoc).
    No sorry/oops/admit.  *)

theory NormalizedStrong
  imports NormalizedAppend GeneralRegexBound
begin

section \<open>Definitions\<close>

text \<open>The new alternation prune: same shape as the lexer's rsimpStrong cross-row prune
  (GeneralRegexBound), but the re-plug uses nplug (alpha), not sigma7.\<close>

definition nprune_pair :: "rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp" where
  "nprune_pair earlier later =
    (case earlier of
       RSEQ (RALTS lrs) k1 \<Rightarrow>
         (case later of
            RSEQ (RALTS rrs) k2 \<Rightarrow>
              (if k1 = k2 then nplug (rsimp_ALTs (rprune_eq_against lrs rrs)) k2 else later)
          | _ \<Rightarrow> later)
     | _ \<Rightarrow> later)"

fun nprune_against_rows :: "rrexp list \<Rightarrow> rrexp \<Rightarrow> rrexp" where
  "nprune_against_rows [] r = r"
| "nprune_against_rows (x # xs) r = nprune_against_rows xs (nprune_pair x r)"

fun nprune_rows_acc :: "rrexp list \<Rightarrow> rrexp list \<Rightarrow> rrexp list" where
  "nprune_rows_acc seen [] = []"
| "nprune_rows_acc seen (r # rs) =
     (let r' = nprune_against_rows seen r in r' # nprune_rows_acc (r' # seen) rs)"

definition nprune_rows :: "rrexp list \<Rightarrow> rrexp list" where
  "nprune_rows rs = nprune_rows_acc [] rs"

definition nalts :: "rrexp list \<Rightarrow> rrexp" where
  "nalts rs = rsimp_ALTs (rdistinct (rflts (nprune_rows rs)) {})"

text \<open>The normalizer.  RSEQ via nplug; RALTS via nalts; RSTAR idempotent.
  Non-legacy constructors are handled like rsimpStrong_raw (they never occur on the
  clean fragment).\<close>

fun nstrong :: "rrexp \<Rightarrow> rrexp" where
  "nstrong RZERO = RZERO"
| "nstrong RONE = RONE"
| "nstrong (RCHAR c) = RCHAR c"
| "nstrong (RSEQ r1 r2) = nplug (nstrong r1) (nstrong r2)"
| "nstrong (RALTS rs) = nalts (map nstrong rs)"
| "nstrong (RSTAR r) =
     (case nstrong r of RZERO \<Rightarrow> RONE | RONE \<Rightarrow> RONE | RSTAR s \<Rightarrow> RSTAR s | s \<Rightarrow> RSTAR s)"
| "nstrong (RNTIMES r n) = RNTIMES (nstrong r) n"
| "nstrong (RBACKREF4 r1 r2 r3 r4 cs) = RBACKREF4 r1 r2 r3 r4 cs"
| "nstrong (RHALF r cs rep) = RHALF r cs rep"
| "nstrong (RRESIDUE cs rep) = RRESIDUE cs rep"


section \<open>nplug zero/unit laws and canonicity\<close>

lemma nplug_RZERO_left [simp]: "nplug RZERO y = RZERO"
  by (simp add: nplug_def norm_seq_def)

lemma nplug_RZERO_right [simp]: "nplug y RZERO = RZERO"
  by (simp add: nplug_def norm_seq_def)

lemma norm_seq_idem: "norm_seq (norm_seq xs) = norm_seq xs"
  using norm_seq_absorb_left[of xs "[]"] by simp

text \<open>A regex is spine-canonical iff re-splitting and re-normalising its spine returns it.\<close>
definition seqcanon :: "rrexp \<Rightarrow> bool" where
  "seqcanon w \<longleftrightarrow> mk_seq (norm_seq (seq_factors w)) = w"

lemma seqcanon_nplug: "seqcanon (nplug r k)"
proof -
  let ?A = "norm_seq (seq_factors r @ seq_factors k)"
  have at: "\<forall>x \<in> set ?A. \<not> is_rseq x"
    by (rule norm_seq_atomic) (auto simp: seq_factors_atomic)
  show ?thesis
  proof (cases "?A = []")
    case True
    then show ?thesis by (simp add: seqcanon_def nplug_def norm_seq_def)
  next
    case False
    have "seq_factors (nplug r k) = ?A"
      using at False by (simp add: nplug_def seq_factors_mk_seq)
    then show ?thesis
      by (simp add: seqcanon_def nplug_def norm_seq_idem)
  qed
qed

text \<open>Any non-sequence is trivially spine-canonical (its spine is a singleton).\<close>
lemma seqcanon_nonseq: "\<not> is_rseq w \<Longrightarrow> seqcanon w"
  by (cases w) (simp_all add: seqcanon_def norm_seq_def)

lemma nplug_RONE_right: "seqcanon y \<Longrightarrow> nplug y RONE = y"
  by (simp add: nplug_def seqcanon_def norm_seq_append_one)

lemma nplug_RONE_left: "seqcanon y \<Longrightarrow> nplug RONE y = y"
  by (simp add: nplug_def seqcanon_def norm_seq_cons_one)


section \<open>Structural canonicity (goodN) of nstrong outputs\<close>

text \<open>@{term goodN} = fully spine-canonical: every RSEQ spine is seqcanon and every
  alternation branch is recursively goodN.  The RALTS clause @{term "list_all goodN bs"}
  is exactly what makes rflts (which splices RALTS branches) preserve goodN.\<close>

fun goodN :: "rrexp \<Rightarrow> bool" where
  "goodN (RSEQ a b) = (seqcanon (RSEQ a b) \<and> goodN a \<and> goodN b)"
| "goodN (RALTS bs) = list_all goodN bs"
| "goodN (RSTAR r) = goodN r"
| "goodN (RNTIMES r n) = goodN r"
| "goodN RZERO = True"
| "goodN RONE = True"
| "goodN (RCHAR c) = True"
| "goodN (RBACKREF4 r1 r2 r3 r4 cs) = True"
| "goodN (RHALF r cs rep) = True"
| "goodN (RRESIDUE cs rep) = True"

lemma goodN_imp_seqcanon: "goodN w \<Longrightarrow> seqcanon w"
  by (cases w) (auto simp: seqcanon_nonseq)

lemma goodN_seq_factors: "goodN w \<Longrightarrow> list_all goodN (seq_factors w)"
  by (induction w) auto

lemma norm_seq_subset: "set (norm_seq xs) \<subseteq> set xs"
  using fold_stars_subset[of "drop_ones xs"] drop_ones_subset[of xs]
  by (auto simp: norm_seq_def)

lemma goodN_rflts: "list_all goodN xs \<Longrightarrow> list_all goodN (rflts xs)"
  by (induction xs rule: rflts.induct) auto

lemma goodN_rdistinct: "list_all goodN xs \<Longrightarrow> list_all goodN (rdistinct xs acc)"
  by (induction xs acc rule: rdistinct.induct) auto

lemma goodN_rsimp_ALTs: "list_all goodN xs \<Longrightarrow> goodN (rsimp_ALTs xs)"
  by (cases xs rule: rsimp_ALTs.cases) auto


section \<open>mk\_seq preserves goodN on a normalised atomic factor list\<close>

lemma drop_ones_length: "length (drop_ones xs) \<le> length xs"
  by (induction xs rule: drop_ones.induct) auto

lemma fold_stars_length: "length (fold_stars xs) \<le> length xs"
  by (induction xs rule: fold_stars.induct) (auto split: if_splits)

lemma drop_ones_Cons: "a \<noteq> RONE \<Longrightarrow> drop_ones (a # zs) = a # drop_ones zs"
  by (cases a) auto

text \<open>Norm-normality is suffix-closed: drop the head of a norm\_seq-fixed list.
  The fold-collapse branch is impossible because fold\_stars never grows a list.\<close>
lemma norm_seq_tl:
  assumes "norm_seq (a # zs) = a # zs"
  shows "norm_seq zs = zs"
proof (cases "zs = []")
  case True thus ?thesis by (simp add: norm_seq_def)
next
  case False
  have nz: "RZERO \<notin> set (a # zs)"
  proof
    assume "RZERO \<in> set (a # zs)"
    then have "norm_seq (a # zs) = [RZERO]" by (simp add: norm_seq_def)
    with assms False show False by simp
  qed
  then have nzzs: "RZERO \<notin> set zs" by simp
  have ane: "a \<noteq> RONE"
  proof
    assume aR: "a = RONE"
    have "norm_seq (a # zs) = fold_stars (drop_ones zs)"
      using nz aR by (simp add: norm_seq_def)
    moreover have "RONE \<notin> set (fold_stars (drop_ones zs))"
      by (rule fold_stars_no_one[OF drop_ones_no_one])
    ultimately have "RONE \<notin> set (a # zs)" using assms by simp
    with aR show False by simp
  qed
  have "norm_seq (a # zs) = fold_stars (a # drop_ones zs)"
    using nz by (simp add: norm_seq_def drop_ones_Cons[OF ane])
  with assms have F: "fold_stars (a # drop_ones zs) = a # zs" by simp
  have "fold_stars (drop_ones zs) = zs"
  proof (cases "drop_ones zs \<noteq> [] \<and> a = hd (drop_ones zs) \<and> is_rstar a")
    case True
    then have "fold_stars (a # drop_ones zs) = fold_stars (drop_ones zs)"
      using fold_stars_cons_fold by auto
    with F have "fold_stars (drop_ones zs) = a # zs" by simp
    then have "length (a # zs) \<le> length (drop_ones zs)"
      using fold_stars_length[of "drop_ones zs"] by simp
    moreover have "length (drop_ones zs) \<le> length zs" by (rule drop_ones_length)
    ultimately show ?thesis by simp
  next
    case False
    then have "fold_stars (a # drop_ones zs) = a # fold_stars (drop_ones zs)"
      by (rule fold_stars_cons_keep)
    with F show ?thesis by simp
  qed
  then show ?thesis using nzzs by (simp add: norm_seq_def)
qed

lemma seqcanon_mk_seq:
  assumes "\<forall>x \<in> set xs. \<not> is_rseq x" "norm_seq xs = xs"
  shows "seqcanon (mk_seq xs)"
proof (cases "xs = []")
  case True then show ?thesis by (simp add: seqcanon_def norm_seq_def)
next
  case False
  have "seq_factors (mk_seq xs) = xs"
    using assms(1) False by (simp add: seq_factors_mk_seq)
  then show ?thesis by (simp add: seqcanon_def assms(2))
qed

lemma mk_seq_goodN:
  "list_all goodN xs \<Longrightarrow> (\<forall>x \<in> set xs. \<not> is_rseq x) \<Longrightarrow> norm_seq xs = xs
   \<Longrightarrow> goodN (mk_seq xs)"
proof (induction xs rule: mk_seq.induct)
  case 1 show ?case by simp
next
  case (2 x) then show ?case by simp
next
  case (3 x y xs)
  have gx: "goodN x" using "3.prems"(1) by simp
  have lyxs: "list_all goodN (y # xs)" using "3.prems"(1) by simp
  have atom: "\<forall>z \<in> set (y # xs). \<not> is_rseq z" using "3.prems"(2) by simp
  have nrm: "norm_seq (y # xs) = y # xs" using "3.prems"(3) by (rule norm_seq_tl)
  have gtl: "goodN (mk_seq (y # xs))" using "3.IH"[OF lyxs atom nrm] .
  have sc: "seqcanon (mk_seq (x # y # xs))"
    using "3.prems"(2) "3.prems"(3) by (rule seqcanon_mk_seq)
  show ?case using sc gx gtl by simp
qed

lemma goodN_nplug:
  assumes "goodN r" "goodN k" shows "goodN (nplug r k)"
proof -
  let ?xs = "seq_factors r @ seq_factors k"
  have g: "list_all goodN ?xs"
    using goodN_seq_factors[OF assms(1)] goodN_seq_factors[OF assms(2)] by simp
  have gL: "list_all goodN (norm_seq ?xs)"
    using g norm_seq_subset[of ?xs] by (auto simp: list_all_iff)
  have atL: "\<forall>x \<in> set (norm_seq ?xs). \<not> is_rseq x"
    by (rule norm_seq_atomic) (auto simp: seq_factors_atomic)
  have idL: "norm_seq (norm_seq ?xs) = norm_seq ?xs" by (rule norm_seq_idem)
  have "goodN (mk_seq (norm_seq ?xs))" using gL atL idL by (rule mk_seq_goodN)
  then show ?thesis by (simp add: nplug_def)
qed


section \<open>goodN propagates through nalts and nstrong\<close>

lemma goodN_rprune_eq_against:
  "list_all goodN rrs \<Longrightarrow> list_all goodN (rprune_eq_against lrs rrs)"
  by (induction rrs) auto

lemma goodN_nprune_pair:
  assumes "goodN later" shows "goodN (nprune_pair earlier later)"
proof -
  have "nprune_pair earlier later = later \<or>
        (\<exists>lrs rrs k. later = RSEQ (RALTS rrs) k \<and>
            nprune_pair earlier later = nplug (rsimp_ALTs (rprune_eq_against lrs rrs)) k)"
    by (auto simp: nprune_pair_def split: rrexp.splits if_splits)
  then show ?thesis
  proof
    assume "nprune_pair earlier later = later"
    thus ?thesis using assms by simp
  next
    assume "\<exists>lrs rrs k. later = RSEQ (RALTS rrs) k \<and>
             nprune_pair earlier later = nplug (rsimp_ALTs (rprune_eq_against lrs rrs)) k"
    then obtain lrs rrs k where
      L: "later = RSEQ (RALTS rrs) k" and
      NP: "nprune_pair earlier later = nplug (rsimp_ALTs (rprune_eq_against lrs rrs)) k" by auto
    have gk: "goodN k" and grrs: "list_all goodN rrs" using assms L by auto
    have "goodN (nplug (rsimp_ALTs (rprune_eq_against lrs rrs)) k)"
      using grrs gk by (intro goodN_nplug goodN_rsimp_ALTs goodN_rprune_eq_against)
    with NP show ?thesis by simp
  qed
qed

lemma goodN_nprune_against_rows:
  "goodN r \<Longrightarrow> goodN (nprune_against_rows seen r)"
  by (induction seen arbitrary: r) (auto simp: goodN_nprune_pair)

lemma goodN_nprune_rows_acc:
  "list_all goodN rs \<Longrightarrow> list_all goodN (nprune_rows_acc seen rs)"
  by (induction rs arbitrary: seen) (auto simp: goodN_nprune_against_rows Let_def)

lemma goodN_nprune_rows: "list_all goodN rs \<Longrightarrow> list_all goodN (nprune_rows rs)"
  by (simp add: nprune_rows_def goodN_nprune_rows_acc)

lemma goodN_nalts: "list_all goodN rs \<Longrightarrow> goodN (nalts rs)"
  unfolding nalts_def
  by (intro goodN_rsimp_ALTs goodN_rdistinct goodN_rflts goodN_nprune_rows)

lemma goodN_nstrong: "goodN (nstrong z)"
proof (induction z)
  case (RSEQ z1 z2) then show ?case by (simp add: goodN_nplug)
next
  case (RALTS rs) then show ?case
    by (auto simp: goodN_nalts list_all_iff)
next
  case (RSTAR z) then show ?case by (auto split: rrexp.split)
next
  case (RNTIMES z n) then show ?case by simp
qed simp_all

lemma seqcanon_nstrong: "seqcanon (nstrong z)"
  by (rule goodN_imp_seqcanon[OF goodN_nstrong])


section \<open>nstrong\_rsimp4\_shadow (kill-criterion #1)\<close>

lemma nplug_nstrong_RONE [simp]: "nplug (nstrong r) RONE = nstrong r"
  by (rule nplug_RONE_right[OF seqcanon_nstrong])

lemma nplug_RONE_nstrong [simp]: "nplug RONE (nstrong r) = nstrong r"
  by (rule nplug_RONE_left[OF seqcanon_nstrong])

lemma nplug_RONE_nonseq [simp]: "\<not> is_rseq w \<Longrightarrow> nplug w RONE = w"
  by (rule nplug_RONE_right[OF seqcanon_nonseq])

lemma nplug_RONE_nonseq_left [simp]: "\<not> is_rseq w \<Longrightarrow> nplug RONE w = w"
  by (rule nplug_RONE_left[OF seqcanon_nonseq])

lemma nplug_nplug_RONE [simp]: "nplug (nplug r k) RONE = nplug r k"
  by (rule nplug_RONE_right[OF seqcanon_nplug])

lemma nplug_same_nstrong_RSTAR [simp]:
  "nplug (nstrong (RSTAR r)) (nstrong (RSTAR r)) = nstrong (RSTAR r)"
  by (cases "nstrong r") (simp_all add: nplug_def norm_seq_def)

lemma nplug_nstrong_RSTAR_absorb_left [simp]:
  "nplug (nstrong (RSTAR r)) (nplug (nstrong (RSTAR r)) k) =
    nplug (nstrong (RSTAR r)) k"
proof -
  have "nplug (nstrong (RSTAR r)) (nplug (nstrong (RSTAR r)) k) =
      nplug (nplug (nstrong (RSTAR r)) (nstrong (RSTAR r))) k"
    by (rule nplug_assoc[symmetric])
  also have "... = nplug (nstrong (RSTAR r)) k"
    by (cases "nstrong r") (simp_all add: nplug_def norm_seq_def)
  finally show ?thesis .
qed

text \<open>The one stubborn leaf: @{term "nalts (map nstrong rs)"} may itself be a sequence,
  so it needs the goodN/seqcanon route rather than @{thm nplug_RONE_nonseq}.\<close>
lemma seqcanon_nalts_nstrong: "seqcanon (nalts (map nstrong rs))"
proof (rule goodN_imp_seqcanon)
  show "goodN (nalts (map nstrong rs))"
    by (rule goodN_nalts) (simp add: list_all_iff goodN_nstrong)
qed

lemma nplug_nalts_nstrong_RONE [simp]:
  "nplug (nalts (map nstrong rs)) RONE = nalts (map nstrong rs)"
  by (rule nplug_RONE_right[OF seqcanon_nalts_nstrong])

theorem nstrong_rsimp4_shadow:
  "nstrong (rsimp4_SEQ_atom r k) = nplug (nstrong r) (nstrong k)"
proof (induction r k rule: rsimp4_SEQ_atom.induct)
  case (3 r1 r2 r3)
  have "nstrong (rsimp4_SEQ_atom (RSEQ r1 r2) r3)
        = nplug (nstrong r1) (nplug (nstrong r2) (nstrong r3))"
    by (simp add: "3.IH"(1) "3.IH"(2))
  also have "... = nplug (nplug (nstrong r1) (nstrong r2)) (nstrong r3)"
    by (rule nplug_assoc[symmetric])
  finally show ?case by simp
qed (simp_all split: rrexp.split)

lemma nstrong_rsimp7_shadow:
  "nstrong (rsimp7_SEQ_atom r k) = nplug (nstrong r) (nstrong k)"
proof (cases r)
  case (RSTAR p)
  note r_eq = RSTAR
  show ?thesis
  proof (cases k)
    case RONE
    have unit: "nplug (nstrong (RSTAR p)) RONE = nstrong (RSTAR p)"
      by (cases "nstrong p") (simp_all add: nplug_def norm_seq_def)
    show ?thesis using r_eq RONE unit
      by (simp add: rsimp7_SEQ_atom_def)
  next
    case (RSTAR q)
    note k_eq = RSTAR
    show ?thesis
    proof (cases "p = q")
      case True
      have dup: "nplug (nstrong (RSTAR p)) (nstrong (RSTAR p)) = nstrong (RSTAR p)"
        by (cases "nstrong p") (simp_all add: nplug_def norm_seq_def)
      show ?thesis using r_eq k_eq True dup
        by (simp add: rsimp7_SEQ_atom_def)
    next
      case False
      show ?thesis using r_eq k_eq False
        by (simp add: rsimp7_SEQ_atom_def nstrong_rsimp4_shadow)
    qed
  next
    case (RSEQ k1 k2)
    note k_eq = RSEQ
    show ?thesis
    proof (cases k1)
      case (RSTAR q)
      note k1_eq = RSTAR
      show ?thesis
      proof (cases "p = q")
        case True
        have dup:
          "nplug (nstrong (RSTAR p)) (nplug (nstrong (RSTAR p)) (nstrong k2)) =
            nplug (nstrong (RSTAR p)) (nstrong k2)"
          by (rule nplug_nstrong_RSTAR_absorb_left)
        show ?thesis using r_eq k_eq k1_eq True dup
          by (simp add: rsimp7_SEQ_atom_def)
      next
        case False
        show ?thesis using r_eq k_eq k1_eq False
          by (simp add: rsimp7_SEQ_atom_def nstrong_rsimp4_shadow)
      qed
    qed (use r_eq k_eq in \<open>simp_all add: rsimp7_SEQ_atom_def nstrong_rsimp4_shadow\<close>)
  qed (use r_eq in \<open>simp_all add: rsimp7_SEQ_atom_def nstrong_rsimp4_shadow\<close>)
qed (simp_all add: rsimp7_SEQ_atom_def nstrong_rsimp4_shadow nplug_assoc)


section \<open>Size bound for nplug (needed for the opening's termination)\<close>

lemma sum_rsize_seq_factors:
  "sum_list (map rsize (seq_factors r)) + length (seq_factors r) = Suc (rsize r)"
  by (induction r) auto

lemma rsize_mk_seq:
  "xs \<noteq> [] \<Longrightarrow> Suc (rsize (mk_seq xs)) = sum_list (map rsize xs) + length xs"
  by (induction xs rule: mk_seq.induct) auto

lemma drop_ones_sum_rsize: "sum_list (map rsize (drop_ones xs)) \<le> sum_list (map rsize xs)"
  by (induction xs rule: drop_ones.induct) auto

lemma fold_stars_sum_rsize: "sum_list (map rsize (fold_stars xs)) \<le> sum_list (map rsize xs)"
  by (induction xs rule: fold_stars.induct) (auto split: if_splits)

lemma rsize_ge_1: "Suc 0 \<le> rsize r"
  by (induction r) auto

lemma one_le_sum_rsize:
  assumes "xs \<noteq> []" shows "Suc 0 \<le> sum_list (map rsize xs)"
proof -
  obtain a ys where axs: "xs = a # ys" using assms by (cases xs) auto
  have "Suc 0 \<le> rsize a" by (rule rsize_ge_1)
  also have "rsize a \<le> sum_list (map rsize xs)" using axs by simp
  finally show ?thesis .
qed

lemma norm_seq_sum_rsize: "sum_list (map rsize (norm_seq xs)) \<le> sum_list (map rsize xs)"
proof (cases "RZERO \<in> set xs")
  case True
  then have "xs \<noteq> []" by auto
  then have "Suc 0 \<le> sum_list (map rsize xs)" by (rule one_le_sum_rsize)
  then show ?thesis using True by (simp add: norm_seq_def)
next
  case False
  then show ?thesis
    using fold_stars_sum_rsize[of "drop_ones xs"] drop_ones_sum_rsize[of xs]
    by (simp add: norm_seq_def)
qed

lemma norm_seq_length_le: "length (norm_seq xs) \<le> length xs"
proof (cases "RZERO \<in> set xs")
  case True then show ?thesis by (cases xs) (auto simp: norm_seq_def)
next
  case False then show ?thesis
    using fold_stars_length[of "drop_ones xs"] drop_ones_length[of xs]
    by (simp add: norm_seq_def)
qed

lemma rsize_nplug_le: "rsize (nplug r k) \<le> rsize r + rsize k + 1"
proof -
  let ?xs = "seq_factors r @ seq_factors k"
  have S: "sum_list (map rsize ?xs) + length ?xs = Suc (rsize r) + Suc (rsize k)"
    using sum_rsize_seq_factors[of r] sum_rsize_seq_factors[of k] by simp
  show ?thesis
  proof (cases "norm_seq ?xs = []")
    case True then show ?thesis by (simp add: nplug_def)
  next
    case False
    have "Suc (rsize (nplug r k))
            = sum_list (map rsize (norm_seq ?xs)) + length (norm_seq ?xs)"
      using False by (simp add: nplug_def rsize_mk_seq)
    also have "... \<le> sum_list (map rsize ?xs) + length ?xs"
      using norm_seq_sum_rsize[of ?xs] norm_seq_length_le[of ?xs] by simp
    also have "... = Suc (rsize r) + Suc (rsize k)" using S by simp
    finally show ?thesis by simp
  qed
qed

end
