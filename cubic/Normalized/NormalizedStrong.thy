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

end
