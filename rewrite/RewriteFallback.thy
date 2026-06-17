theory RewriteFallback
  imports GeneralRegexBound
begin

text \<open>
  Independent fallback lane for the step-wise-strong vs once-strong route.
  The primitive step is the Ch6 closed-form move that toggles between a
  factored common suffix and the corresponding opened rows.  The Python gate
  \<open>scratch_rewrite_fallback_validate.py\<close> validated that the recursive
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

text \<open>
  DIAGNOSTIC (2026-06-17, lane RW-1 / D, the @{text "\<rightarrow>r'"} derivative-commutation angle).

  The thesis Ch.5 rewrite-relation method proves commutation with the derivative
  only UP TO the simplifier: @{term "rsimp (rder x (rsimp r)) = rsimp (rder x r)"}
  (\<open>ClosedForms.thy\<close>, proved via the @{text "h\<leadsto>"} system + \<open>rsimp_idem\<close>).  That
  proof crucially needs the simplifier to be (a) idempotent and (b)
  derivative-commuting.  @{const rsimp} has both.

  @{const rsimpStrong_raw} (the simplifier this lane's @{const rprime_rel} is built
  on) has NEITHER: it is already recorded as non-idempotent
  (\<open>rsimpStrong_raw_not_idempotent\<close>, \<open>AntimirovFactoredTransition.thy\<close>; witness a
  nested star), and the lemma below records that it does not commute with the
  derivative along @{const rprime_step} either.  For the single @{thm [source]
  rprime_step.seq_alts_expand} redex
  @{term "r = RSEQ (RALTS [RSTAR (RCHAR b), RCHAR b]) (RCHAR b)"} we have
  @{term "rprime_step r s"} yet the two strong-simplified derivatives differ
  (the @{text r}-side keeps the @{text "(a* + 1)\<cdot>a"} factor; the @{text s}-side
  prunes a row, so even @{term rsize} differs: 8 vs 7).

  Consequence: ``@{text "\<rightarrow>r'"} commutes with the derivative'' is FALSE as framed
  for @{const rsimpStrong_raw}.  This was machine-checked exhaustively on the
  witness corpus (\<open>scratch_rprime_commute_validate.py\<close>): the relation-level
  commutation @{term "rprime_step r s \<longrightarrow> rprime_rewrites (rder c r) (rder c s)"},
  its closure, and the simp-modulo form all fail; even augmenting @{const
  rprime_step} with every @{text "h\<leadsto>"} structural rule only reaches the target
  on 33% of redexes (the @{const rsimp7_SEQ_atom} normalization baked into the
  expand rule prevents reaching @{term "rder c s"} exactly).  Salvaging the lane
  needs a strong simplifier with @{const rsimp}'s algebraic properties
  (idempotent + derivative-commuting), or a transport that avoids commutation.
\<close>

lemma rprime_step_not_der_commute_modulo_rsimpStrong_raw:
  fixes b :: char
  shows "rprime_step
           (RSEQ (RALTS [RSTAR (RCHAR b), RCHAR b]) (RCHAR b))
           (RALTS (map (\<lambda>q. rsimp7_SEQ_atom q (RCHAR b)) [RSTAR (RCHAR b), RCHAR b]))"
    and "rsimpStrong_raw (rder b (RSEQ (RALTS [RSTAR (RCHAR b), RCHAR b]) (RCHAR b)))
         \<noteq> rsimpStrong_raw
              (rder b (RALTS (map (\<lambda>q. rsimp7_SEQ_atom q (RCHAR b))
                                  [RSTAR (RCHAR b), RCHAR b])))"
proof -
  show "rprime_step
          (RSEQ (RALTS [RSTAR (RCHAR b), RCHAR b]) (RCHAR b))
          (RALTS (map (\<lambda>q. rsimp7_SEQ_atom q (RCHAR b)) [RSTAR (RCHAR b), RCHAR b]))"
    by (rule rprime_step.seq_alts_expand)
next
  show "rsimpStrong_raw (rder b (RSEQ (RALTS [RSTAR (RCHAR b), RCHAR b]) (RCHAR b)))
         \<noteq> rsimpStrong_raw
              (rder b (RALTS (map (\<lambda>q. rsimp7_SEQ_atom q (RCHAR b))
                                  [RSTAR (RCHAR b), RCHAR b])))"
    by (simp add: rsimp7_SEQ_atom_def rsimp4_SEQ_atom.simps
        rsimpStrong_ALTs_raw_def rsimpStrong_prune_rows_raw_def
        rsimpStrong_prune_pair_raw_def Let_def)
qed

end
