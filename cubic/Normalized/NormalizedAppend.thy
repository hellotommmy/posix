(*  Route-2 / N-route — Wave 1A: normalized associative append (alpha = nplug).
    Owner: norm/01-alpha lane.  Session: Posix_Norm (parent Posix_Base).

    Design (route2_verdict.md sec.4, docs/norm-route/00-design.md):
      alpha(r,k) = mk_seq (norm_seq (seq_factors r @ seq_factors k))
    on a flat SEQUENCE SPINE, where norm_seq (1) drops RONE, (2) collapses to [RZERO]
    if any RZERO factor, (3) folds adjacent identical STARS (...,s*,s*,... |-> ...,s*,...).
    The lone load-bearing fact downstream is nplug_assoc (kill-criterion #1 reduces to it;
    see docs/norm-route/01-adversarial.md).  Validated 0/5,268,024 in norm_model.py [T3].

    THIS BRICK (committed green): definitions + foundational list lemmas.
    NEXT increment: fold_stars absorb -> norm_seq absorb -> nplug_assoc + rsize bounds.
    No sorry/oops/admit, ever.  *)

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

end
