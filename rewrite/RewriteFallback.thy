theory RewriteFallback
  imports GeneralRegexBound
begin

text \<open>
  Independent fallback lane for the step-wise-strong vs once-strong route.
  The primitive step is the Ch6 closed-form move that toggles between a
  factored common suffix and the corresponding opened rows.  The Python gate
  @{file "../scratch_rewrite_fallback_validate.py"} validated that the recursive
  closed-form version of this relation relates
  @{term "rders_simpStrong r s"} and @{term "rsimpStrong_raw (rders r s)"}
  on the witness/direct-universe corpus, while stricter structural equality
  candidates are false.
\<close>

inductive rprime_step :: "rrexp \<Rightarrow> rrexp \<Rightarrow> bool" where
  seq_alts_expand:
    "rprime_step
      (RSEQ (RALTS rs) k)
      (RALTS (map (\<lambda>q. rsimp7_SEQ_atom q k) rs))"
| seq_alts_factor:
    "rprime_step
      (RALTS (map (\<lambda>q. rsimp7_SEQ_atom q k) rs))
      (RSEQ (RALTS rs) k)"
| alts_context:
    "rprime_step r r' \<Longrightarrow>
      rprime_step (RALTS (xs @ r # ys)) (RALTS (xs @ r' # ys))"
| seq_left_context:
    "rprime_step r r' \<Longrightarrow>
      rprime_step (RSEQ r k) (RSEQ r' k)"
| seq_right_context:
    "rprime_step k k' \<Longrightarrow>
      rprime_step (RSEQ r k) (RSEQ r k')"
| star_context:
    "rprime_step r r' \<Longrightarrow>
      rprime_step (RSTAR r) (RSTAR r')"

inductive rprime_rewrites :: "rrexp \<Rightarrow> rrexp \<Rightarrow> bool" where
  refl [intro, simp]: "rprime_rewrites r r"
| step [intro]:
    "rprime_step r s \<Longrightarrow> rprime_rewrites s t \<Longrightarrow>
      rprime_rewrites r t"

lemma rprime_rewrites_one:
  assumes "rprime_step r s"
  shows "rprime_rewrites r s"
  using assms by blast

lemma rprime_rewrites_trans [trans]:
  assumes "rprime_rewrites r s"
    and "rprime_rewrites s t"
  shows "rprime_rewrites r t"
  using assms
  by (induct rule: rprime_rewrites.induct) blast+

lemma RL_RALTS_map_rsimp7_SEQ_atom:
  "RL (RALTS (map (\<lambda>q. rsimp7_SEQ_atom q k) rs)) =
    RL (RSEQ (RALTS rs) k)"
proof -
  have "RL (RALTS (map (\<lambda>q. rsimp7_SEQ_atom q k) rs)) =
      (\<Union> (RL ` set (rsimp7_seq_products rs [k])))"
    by (simp add: rsimp7_seq_products_def)
  also have "... = (\<Union> (RL ` set rs)) ;; (\<Union> (RL ` set [k]))"
    by (rule RL_rsimp7_seq_products)
  also have "... = RL (RSEQ (RALTS rs) k)"
    by simp
  finally show ?thesis .
qed

lemma rprime_step_preserves_RL:
  assumes "rprime_step r s"
  shows "RL r = RL s"
  using assms
proof (induct rule: rprime_step.induct)
  case (seq_alts_expand rs k)
  then show ?case
    by (rule sym, rule RL_RALTS_map_rsimp7_SEQ_atom)
next
  case (seq_alts_factor rs k)
  then show ?case
    by (rule RL_RALTS_map_rsimp7_SEQ_atom)
next
  case (alts_context r r' xs ys)
  then show ?case
    by auto
next
  case (seq_left_context r r' k)
  then show ?case
    by (simp add: Sequ_def)
next
  case (seq_right_context k k' r)
  then show ?case
    by (simp add: Sequ_def)
next
  case (star_context r r')
  then show ?case
    by simp
qed

lemma rprime_rewrites_preserves_RL:
  assumes "rprime_rewrites r s"
  shows "RL r = RL s"
  using assms
proof (induct rule: rprime_rewrites.induct)
  case (refl r)
  then show ?case by simp
next
  case (step r s t)
  have "RL r = RL s"
    by (rule rprime_step_preserves_RL[OF step.hyps(1)])
  also have "... = RL t"
    by (rule step.hyps(3))
  finally show ?case .
qed

definition rprime_rel :: "rrexp \<Rightarrow> rrexp \<Rightarrow> bool" where
  "rprime_rel r s \<longleftrightarrow>
    (\<exists>u. rprime_rewrites (rsimpStrong_raw r) u \<and>
         rprime_rewrites (rsimpStrong_raw s) u)"

lemma rprime_rel_refl [simp]:
  "rprime_rel r r"
  unfolding rprime_rel_def by blast

lemma rprime_rel_sym:
  assumes "rprime_rel r s"
  shows "rprime_rel s r"
  using assms unfolding rprime_rel_def by blast

lemma rprime_rel_preserves_RL:
  assumes "rprime_rel r s"
  shows "RL r = RL s"
proof -
  obtain u where r: "rprime_rewrites (rsimpStrong_raw r) u"
    and s: "rprime_rewrites (rsimpStrong_raw s) u"
    using assms unfolding rprime_rel_def by blast
  have "RL r = RL (rsimpStrong_raw r)"
    by (simp add: RL_rsimpStrong_raw)
  also have "... = RL u"
    by (rule rprime_rewrites_preserves_RL[OF r])
  also have "... = RL (rsimpStrong_raw s)"
    using rprime_rewrites_preserves_RL[OF s] by simp
  also have "... = RL s"
    by (simp add: RL_rsimpStrong_raw)
  finally show ?thesis .
qed

end
