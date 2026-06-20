(*  Route-2 / N-route — Wave 1A: normalized associative append (alpha = nplug).
    Owner: norm/01-alpha lane.  Session: Posix_Norm (parent Posix_Base).

    Design (route2_verdict.md sec.4, docs/norm-route/00-design.md):
      alpha(r,k) = mk_seq (norm_seq (seq_factors r @ seq_factors k))
    on a flat SEQUENCE SPINE, where norm_seq (1) drops RONE, (2) collapses to [RZERO]
    if any RZERO factor, (3) folds adjacent identical STARS (...,s*,s*,... |-> ...,s*,...).
    The lone load-bearing fact downstream is nplug_assoc (kill-criterion #1 reduces to it;
    see docs/norm-route/01-adversarial.md).  Validated 0/5,268,024 in norm_model.py [T3].

    Definitions + foundational list lemmas + the absorb/associativity development.
    All proofs complete in-theory; nothing is deferred or axiomatised.  *)

theory NormalizedAppend
  imports "Posix_Base.BasicIdentities"
begin

section \<open>Definitions\<close>

fun is_rstar :: "rrexp \<Rightarrow> bool" where
  "is_rstar (RSTAR _) = True"
| "is_rstar _ = False"

fun is_rseq :: "rrexp \<Rightarrow> bool" where
  "is_rseq (RSEQ _ _) = True"
| "is_rseq _ = False"

text \<open>The sequence spine: flatten a right/left-nested RSEQ into its atomic factors.\<close>
fun seq_factors :: "rrexp \<Rightarrow> rrexp list" where
  "seq_factors (RSEQ r1 r2) = seq_factors r1 @ seq_factors r2"
| "seq_factors r = [r]"

text \<open>Rebuild a right-nested sequence from a factor list (empty \<mapsto> RONE).\<close>
fun mk_seq :: "rrexp list \<Rightarrow> rrexp" where
  "mk_seq [] = RONE"
| "mk_seq [x] = x"
| "mk_seq (x # y # xs) = RSEQ x (mk_seq (y # xs))"

text \<open>Drop the unit factors.\<close>
fun drop_ones :: "rrexp list \<Rightarrow> rrexp list" where
  "drop_ones [] = []"
| "drop_ones (RONE # xs) = drop_ones xs"
| "drop_ones (x # xs) = x # drop_ones xs"

text \<open>Collapse adjacent identical stars (..,s*,s*,.. \<mapsto> ..,s*,..). Non-stars untouched.\<close>
fun fold_stars :: "rrexp list \<Rightarrow> rrexp list" where
  "fold_stars [] = []"
| "fold_stars [x] = [x]"
| "fold_stars (x # y # xs) =
     (if x = y \<and> is_rstar x then fold_stars (y # xs) else x # fold_stars (y # xs))"

definition norm_seq :: "rrexp list \<Rightarrow> rrexp list" where
  "norm_seq xs = (if RZERO \<in> set xs then [RZERO] else fold_stars (drop_ones xs))"

definition nplug :: "rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp" where
  "nplug r k = mk_seq (norm_seq (seq_factors r @ seq_factors k))"


section \<open>Foundational lemmas\<close>

subsection \<open>seq\_factors / mk\_seq round-trip\<close>

lemma seq_factors_nonempty: "seq_factors r \<noteq> []"
  by (induction r) auto

lemma seq_factors_atomic: "x \<in> set (seq_factors r) \<Longrightarrow> \<not> is_rseq x"
  by (induction r arbitrary: x) auto

lemma seq_factors_singleton: "\<not> is_rseq x \<Longrightarrow> seq_factors x = [x]"
  by (cases x) auto

lemma seq_factors_mk_seq:
  "(\<forall>x \<in> set xs. \<not> is_rseq x) \<Longrightarrow>
     seq_factors (mk_seq xs) = (if xs = [] then [RONE] else xs)"
proof (induction xs rule: mk_seq.induct)
  case 1 show ?case by simp
next
  case (2 x)
  then have "\<not> is_rseq x" by simp
  then show ?case by (simp add: seq_factors_singleton)
next
  case (3 x y xs)
  have ax: "\<not> is_rseq x" using "3.prems" by simp
  have prem: "\<forall>z \<in> set (y # xs). \<not> is_rseq z" using "3.prems" by simp
  have "seq_factors (mk_seq (x # y # xs)) = seq_factors x @ seq_factors (mk_seq (y # xs))"
    by simp
  also have "seq_factors x = [x]" using ax by (rule seq_factors_singleton)
  also have "seq_factors (mk_seq (y # xs)) = y # xs" using "3.IH"[OF prem] by simp
  finally show ?case by simp
qed

subsection \<open>drop\_ones\<close>

lemma drop_ones_no_one: "RONE \<notin> set (drop_ones xs)"
  by (induction xs rule: drop_ones.induct) auto

lemma drop_ones_append: "drop_ones (xs @ ys) = drop_ones xs @ drop_ones ys"
  by (induction xs rule: drop_ones.induct) auto

lemma drop_ones_subset: "set (drop_ones xs) \<subseteq> set xs"
  by (induction xs rule: drop_ones.induct) auto

lemma drop_ones_no_zero: "RZERO \<notin> set xs \<Longrightarrow> RZERO \<notin> set (drop_ones xs)"
  using drop_ones_subset by blast

lemma norm_seq_cons_one: "norm_seq (RONE # ys) = norm_seq ys"
  by (simp add: norm_seq_def)

subsection \<open>fold\_stars\<close>

lemma fold_stars_Cons:
  "fold_stars (x # v) =
     (if v \<noteq> [] \<and> x = hd v \<and> is_rstar x then fold_stars v else x # fold_stars v)"
  by (cases v) auto

lemma fold_stars_nonempty: "xs \<noteq> [] \<Longrightarrow> fold_stars xs \<noteq> []"
  by (induction xs rule: fold_stars.induct) auto

lemma fold_stars_hd: "xs \<noteq> [] \<Longrightarrow> hd (fold_stars xs) = hd xs"
  by (induction xs rule: fold_stars.induct) auto

lemma fold_stars_subset: "set (fold_stars xs) \<subseteq> set xs"
  by (induction xs rule: fold_stars.induct) auto


section \<open>fold\_stars absorb (the boundary star-fold congruence)\<close>

text \<open>Two unconditional rewrites for @{term "fold_stars (x # zs)"}: fold (drop x) when x
  is a star equal to the head, keep otherwise.  Used via @{method rule} so simp never
  unfolds the conditional @{thm fold_stars.simps(3)} (which it then mis-splits).\<close>

lemma fold_stars_cons_fold:
  assumes "zs \<noteq> []" "x = hd zs" "is_rstar x"
  shows "fold_stars (x # zs) = fold_stars zs"
  using assms by (simp add: fold_stars_Cons)

lemma fold_stars_cons_keep:
  assumes "\<not> (zs \<noteq> [] \<and> x = hd zs \<and> is_rstar x)"
  shows "fold_stars (x # zs) = x # fold_stars zs"
  using assms by (simp add: fold_stars_Cons)

lemma fold_stars_absorb_left:
  "fold_stars (fold_stars u @ v) = fold_stars (u @ v)"
proof (induction u rule: fold_stars.induct)
  case 1 show ?case by simp
next
  case (2 x) show ?case by simp
next
  case (3 x y xs)
  have key: "fold_stars (y # xs) \<noteq> []" by (simp add: fold_stars_nonempty)
  have IH: "fold_stars (fold_stars (y # xs) @ v) = fold_stars ((y # xs) @ v)"
    using "3.IH" by blast
  show ?case
  proof (cases "x = y \<and> is_rstar x")
    case True
    have e: "fold_stars (x # y # xs) = fold_stars (y # xs)"
      by (rule fold_stars_cons_fold) (use True in auto)
    have e2: "fold_stars (x # ((y # xs) @ v)) = fold_stars ((y # xs) @ v)"
      by (rule fold_stars_cons_fold) (use True in auto)
    have "fold_stars (fold_stars (x # y # xs) @ v) = fold_stars (fold_stars (y # xs) @ v)"
      by (simp only: e)
    also have "... = fold_stars ((y # xs) @ v)" by (rule IH)
    also have "... = fold_stars (x # ((y # xs) @ v))" by (simp only: e2)
    also have "... = fold_stars ((x # y # xs) @ v)" by (simp only: append.simps)
    finally show ?thesis .
  next
    case False
    have e: "fold_stars (x # y # xs) = x # fold_stars (y # xs)"
      by (rule fold_stars_cons_keep) (use False in auto)
    have e2: "fold_stars (x # ((y # xs) @ v)) = x # fold_stars ((y # xs) @ v)"
      by (rule fold_stars_cons_keep) (use False in auto)
    have "fold_stars (fold_stars (x # y # xs) @ v)
            = fold_stars ((x # fold_stars (y # xs)) @ v)" by (simp only: e)
    also have "... = fold_stars (x # (fold_stars (y # xs) @ v))" by (simp only: append.simps)
    also have "... = x # fold_stars (fold_stars (y # xs) @ v)"
    proof (rule fold_stars_cons_keep)
      show "\<not> (fold_stars (y # xs) @ v \<noteq> [] \<and> x = hd (fold_stars (y # xs) @ v) \<and> is_rstar x)"
        using False key fold_stars_hd[of "y # xs"] by (simp add: hd_append)
    qed
    also have "... = x # fold_stars ((y # xs) @ v)" by (simp add: IH)
    also have "... = fold_stars (x # ((y # xs) @ v))" by (rule e2[symmetric])
    also have "... = fold_stars ((x # y # xs) @ v)" by (simp only: append.simps)
    finally show ?thesis .
  qed
qed

lemma fold_stars_idem: "fold_stars (fold_stars v) = fold_stars v"
  using fold_stars_absorb_left[of v "[]"] by simp

lemma fold_stars_empty_iff: "fold_stars v = [] \<longleftrightarrow> v = []"
  using fold_stars_nonempty[of v] by (cases v) auto

lemma fold_stars_absorb_right:
  "fold_stars (u @ fold_stars v) = fold_stars (u @ v)"
proof (induction u rule: fold_stars.induct)
  case 1 show ?case by (simp add: fold_stars_idem)
next
  case (2 x)
  show ?case
  proof (cases "v = []")
    case True then show ?thesis by simp
  next
    case False
    then have vne: "v \<noteq> []" by simp
    from vne have ne: "fold_stars v \<noteq> []" by (simp add: fold_stars_empty_iff)
    from vne have hdv: "hd (fold_stars v) = hd v" by (rule fold_stars_hd)
    show ?thesis
    proof (cases "x = hd v \<and> is_rstar x")
      case True
      have a: "fold_stars (x # fold_stars v) = fold_stars (fold_stars v)"
        by (rule fold_stars_cons_fold) (use ne hdv True in auto)
      have b: "fold_stars (x # v) = fold_stars v"
        by (rule fold_stars_cons_fold) (use vne True in auto)
      have "fold_stars ([x] @ fold_stars v) = fold_stars (fold_stars v)" using a by simp
      also have "... = fold_stars v" by (rule fold_stars_idem)
      also have "... = fold_stars ([x] @ v)" using b by simp
      finally show ?thesis .
    next
      case False
      have a: "fold_stars (x # fold_stars v) = x # fold_stars (fold_stars v)"
        by (rule fold_stars_cons_keep) (use ne hdv False in auto)
      have b: "fold_stars (x # v) = x # fold_stars v"
        by (rule fold_stars_cons_keep) (use vne False in auto)
      have "fold_stars ([x] @ fold_stars v) = x # fold_stars (fold_stars v)" using a by simp
      also have "... = x # fold_stars v" by (simp add: fold_stars_idem)
      also have "... = fold_stars ([x] @ v)" using b by simp
      finally show ?thesis .
    qed
  qed
next
  case (3 x y xs)
  have IH: "fold_stars ((y # xs) @ fold_stars v) = fold_stars ((y # xs) @ v)"
    using "3.IH" by blast
  show ?case
  proof (cases "x = y \<and> is_rstar x")
    case True
    have e1: "fold_stars (x # ((y # xs) @ fold_stars v)) = fold_stars ((y # xs) @ fold_stars v)"
      by (rule fold_stars_cons_fold) (use True in auto)
    have e2: "fold_stars (x # ((y # xs) @ v)) = fold_stars ((y # xs) @ v)"
      by (rule fold_stars_cons_fold) (use True in auto)
    have "fold_stars ((x # y # xs) @ fold_stars v) = fold_stars (x # ((y # xs) @ fold_stars v))"
      by (simp only: append.simps)
    also have "... = fold_stars ((y # xs) @ fold_stars v)" by (rule e1)
    also have "... = fold_stars ((y # xs) @ v)" by (rule IH)
    also have "... = fold_stars (x # ((y # xs) @ v))" by (rule e2[symmetric])
    also have "... = fold_stars ((x # y # xs) @ v)" by (simp only: append.simps)
    finally show ?thesis .
  next
    case False
    have e1: "fold_stars (x # ((y # xs) @ fold_stars v)) = x # fold_stars ((y # xs) @ fold_stars v)"
      by (rule fold_stars_cons_keep) (use False in auto)
    have e2: "fold_stars (x # ((y # xs) @ v)) = x # fold_stars ((y # xs) @ v)"
      by (rule fold_stars_cons_keep) (use False in auto)
    have "fold_stars ((x # y # xs) @ fold_stars v) = fold_stars (x # ((y # xs) @ fold_stars v))"
      by (simp only: append.simps)
    also have "... = x # fold_stars ((y # xs) @ fold_stars v)" by (rule e1)
    also have "... = x # fold_stars ((y # xs) @ v)" by (simp only: IH)
    also have "... = fold_stars (x # ((y # xs) @ v))" by (rule e2[symmetric])
    also have "... = fold_stars ((x # y # xs) @ v)" by (simp only: append.simps)
    finally show ?thesis .
  qed
qed


section \<open>norm\_seq absorb and the associativity of nplug\<close>

lemma drop_ones_id: "RONE \<notin> set zs \<Longrightarrow> drop_ones zs = zs"
  by (induction zs rule: drop_ones.induct) auto

lemma fold_stars_no_one: "RONE \<notin> set zs \<Longrightarrow> RONE \<notin> set (fold_stars zs)"
  using fold_stars_subset[of zs] by auto

lemma norm_seq_no_zero: "RZERO \<notin> set xs \<Longrightarrow> RZERO \<notin> set (norm_seq xs)"
  using fold_stars_subset[of "drop_ones xs"] drop_ones_subset[of xs]
  by (auto simp: norm_seq_def)

lemma norm_seq_atomic:
  assumes "\<forall>x \<in> set zs. \<not> is_rseq x"
  shows "\<forall>x \<in> set (norm_seq zs). \<not> is_rseq x"
proof (cases "RZERO \<in> set zs")
  case True then show ?thesis by (simp add: norm_seq_def)
next
  case False
  have "set (norm_seq zs) \<subseteq> set zs"
    using False fold_stars_subset[of "drop_ones zs"] drop_ones_subset[of zs]
    by (auto simp: norm_seq_def)
  thus ?thesis using assms by auto
qed

text \<open>The unit and zero collapse is invariant under a trailing/leading RONE.\<close>
lemma norm_seq_append_one: "norm_seq (ys @ [RONE]) = norm_seq ys"
  by (simp add: norm_seq_def drop_ones_append)

text \<open>When @{term xs} carries no RZERO, dropping ones after normalising is the same
  as the bare star-fold of the unit-free list.\<close>
lemma drop_ones_norm_seq:
  assumes "RZERO \<notin> set xs"
  shows "drop_ones (norm_seq xs) = fold_stars (drop_ones xs)"
proof -
  have "norm_seq xs = fold_stars (drop_ones xs)" using assms by (simp add: norm_seq_def)
  moreover have "RONE \<notin> set (fold_stars (drop_ones xs))"
    by (rule fold_stars_no_one[OF drop_ones_no_one])
  ultimately show ?thesis by (simp add: drop_ones_id)
qed

lemma norm_seq_absorb_left: "norm_seq (norm_seq xs @ ys) = norm_seq (xs @ ys)"
proof (cases "RZERO \<in> set xs")
  case True
  then have "norm_seq xs = [RZERO]" "RZERO \<in> set (xs @ ys)" by (auto simp: norm_seq_def)
  then show ?thesis by (simp add: norm_seq_def)
next
  case noxs: False
  show ?thesis
  proof (cases "RZERO \<in> set ys")
    case True
    then have "RZERO \<in> set (norm_seq xs @ ys)" "RZERO \<in> set (xs @ ys)" by auto
    then show ?thesis by (simp add: norm_seq_def)
  next
    case noys: False
    have nz1: "RZERO \<notin> set (norm_seq xs @ ys)"
      using norm_seq_no_zero[OF noxs] noys by simp
    have nz2: "RZERO \<notin> set (xs @ ys)" using noxs noys by simp
    have "norm_seq (norm_seq xs @ ys) = fold_stars (drop_ones (norm_seq xs) @ drop_ones ys)"
      using nz1 by (simp add: norm_seq_def drop_ones_append)
    also have "... = fold_stars (fold_stars (drop_ones xs) @ drop_ones ys)"
      using noxs by (simp add: drop_ones_norm_seq)
    also have "... = fold_stars (drop_ones xs @ drop_ones ys)"
      by (rule fold_stars_absorb_left)
    also have "... = norm_seq (xs @ ys)"
      using nz2 by (simp add: norm_seq_def drop_ones_append)
    finally show ?thesis .
  qed
qed

lemma norm_seq_absorb_right: "norm_seq (xs @ norm_seq ys) = norm_seq (xs @ ys)"
proof (cases "RZERO \<in> set ys")
  case True
  then have "norm_seq ys = [RZERO]" "RZERO \<in> set (xs @ ys)" by (auto simp: norm_seq_def)
  then show ?thesis by (simp add: norm_seq_def)
next
  case noys: False
  show ?thesis
  proof (cases "RZERO \<in> set xs")
    case True
    then have "RZERO \<in> set (xs @ norm_seq ys)" "RZERO \<in> set (xs @ ys)" by auto
    then show ?thesis by (simp add: norm_seq_def)
  next
    case noxs: False
    have nz1: "RZERO \<notin> set (xs @ norm_seq ys)"
      using norm_seq_no_zero[OF noys] noxs by simp
    have nz2: "RZERO \<notin> set (xs @ ys)" using noxs noys by simp
    have "norm_seq (xs @ norm_seq ys) = fold_stars (drop_ones xs @ drop_ones (norm_seq ys))"
      using nz1 by (simp add: norm_seq_def drop_ones_append)
    also have "... = fold_stars (drop_ones xs @ fold_stars (drop_ones ys))"
      using noys by (simp add: drop_ones_norm_seq)
    also have "... = fold_stars (drop_ones xs @ drop_ones ys)"
      by (rule fold_stars_absorb_right)
    also have "... = norm_seq (xs @ ys)"
      using nz2 by (simp add: norm_seq_def drop_ones_append)
    finally show ?thesis .
  qed
qed

text \<open>Re-splitting a rebuilt sequence and re-normalising is the same as normalising the
  original factor list (the stray RONE from the empty rebuild is absorbed by norm\_seq).\<close>
lemma norm_seq_sfms_left:
  assumes "\<forall>x \<in> set xs. \<not> is_rseq x"
  shows "norm_seq (seq_factors (mk_seq xs) @ ys) = norm_seq (xs @ ys)"
proof (cases "xs = []")
  case True then show ?thesis
    by (simp add: seq_factors_mk_seq[OF assms] norm_seq_cons_one)
next
  case False then show ?thesis by (simp add: seq_factors_mk_seq[OF assms])
qed

lemma norm_seq_sfms_right:
  assumes "\<forall>x \<in> set xs. \<not> is_rseq x"
  shows "norm_seq (ys @ seq_factors (mk_seq xs)) = norm_seq (ys @ xs)"
proof (cases "xs = []")
  case True then show ?thesis
    by (simp add: seq_factors_mk_seq[OF assms] norm_seq_append_one)
next
  case False then show ?thesis by (simp add: seq_factors_mk_seq[OF assms])
qed

theorem nplug_assoc: "nplug (nplug r k) h = nplug r (nplug k h)"
proof -
  have ar: "\<forall>x \<in> set (seq_factors r). \<not> is_rseq x" using seq_factors_atomic by blast
  have ak: "\<forall>x \<in> set (seq_factors k). \<not> is_rseq x" using seq_factors_atomic by blast
  have ah: "\<forall>x \<in> set (seq_factors h). \<not> is_rseq x" using seq_factors_atomic by blast
  have arl: "\<forall>x \<in> set (norm_seq (seq_factors r @ seq_factors k)). \<not> is_rseq x"
    by (rule norm_seq_atomic) (use ar ak in auto)
  have akl: "\<forall>x \<in> set (norm_seq (seq_factors k @ seq_factors h)). \<not> is_rseq x"
    by (rule norm_seq_atomic) (use ak ah in auto)
  have "nplug (nplug r k) h
        = mk_seq (norm_seq (seq_factors (mk_seq (norm_seq (seq_factors r @ seq_factors k)))
                            @ seq_factors h))"
    by (simp add: nplug_def)
  also have "... = mk_seq (norm_seq (norm_seq (seq_factors r @ seq_factors k) @ seq_factors h))"
    by (simp add: norm_seq_sfms_left[OF arl])
  also have "... = mk_seq (norm_seq ((seq_factors r @ seq_factors k) @ seq_factors h))"
    by (simp add: norm_seq_absorb_left)
  also have "... = mk_seq (norm_seq (seq_factors r @ (seq_factors k @ seq_factors h)))"
    by simp
  also have "... = mk_seq (norm_seq (seq_factors r @ norm_seq (seq_factors k @ seq_factors h)))"
    by (simp add: norm_seq_absorb_right)
  also have "... = mk_seq (norm_seq (seq_factors r
                     @ seq_factors (mk_seq (norm_seq (seq_factors k @ seq_factors h)))))"
    by (simp add: norm_seq_sfms_right[OF akl])
  also have "... = nplug r (nplug k h)"
    by (simp add: nplug_def)
  finally show ?thesis .
qed

end
