> STATUS BANNER 2026-06-12 (secretary): HISTORICAL snapshot of the June 6-8
> proof state. Its theorem statements are settled and citable, but its route
> spine (choice rows / accumulator contracts / normal-canonical) predates the
> current set-ledger gate in `MAINLINE.md`. Content below is unchanged.
# Cubic Bound Proof Write-Up

Date: 2026-06-06

## Status Correction, 2026-06-07

This write-up is not a completed proof of the final strong/memo POSIX route.
In particular, the parts phrased with `aseq_terms` prove only auxiliary
split-atom inclusions.  They do not prove the Antimirov/linear-form stage-one
statement, because `aseq_terms` opens every product and therefore loses whole
residual terms such as `a(aa)`, `aa`, and `a`.

The corrected stage-one splitter is `ader_front`/`rfrontier`, not
`row_dlforms`.  `row_dlforms` also opens too much structure for this stage
when it recursively expands rows such as `RSEQ (RALTS ps) k`; it remains an
auxiliary tool for the later canonical/prune accounting only.

## Checked Normal-Canonical Main Theorem, 2026-06-08

The pure Antimirov/factored derivative route now has a checked regex-level
cubic theorem.  Define

$$
D_N(r,s) =
\mathrm{rsimp\_ALTs}
  (\mathrm{normal\_frontier\_canonical\_rows}
    (\mathrm{afactored1}(r,s))).
$$

In Isabelle this is `normal_canonical_derivative`.  Under
`legacy_rrexp r` and `apder_nf r`, the theorem
`normal_canonical_derivative_cubic_contract` proves

$$
\mathcal L(D_N(r,s))=\mathrm{Ders}(s,\mathcal L(r)),
$$

$$
\mathrm{rfrontier}(D_N(r,s))
\subseteq \mathrm{normal\_antimirov\_frontier}(r),
$$

and

$$
|D_N(r,s)|\le
1+(\mathrm{apder\_awidth}(r)+|r|+3)^3.
$$

The theorem `normal_canonical_derivative_exact_frontier_contract` also proves
that the canonical derivative has no duplicate normal frontier rows:

$$
\mathrm{rfrontier}(D_N(r,s))
=
\mathrm{set}(
  \mathrm{normal\_frontier\_canonical\_rows}
    (\mathrm{afactored1}(r,s))),
$$

with that row list `distinct`, contained in
`normal_antimirov_frontier r`, and cardinality bounded by the same cubic.  This
is the requested two-step separation for the pure route: derivatives prove
frontier inclusion; canonicalization proves uniqueness/no duplicates.

The later checked strengthening makes the same-front invariant explicit.  The
theorem `normal_canonical_derivative_frontier_eq_ader_front` proves

$$
\mathrm{rfrontier}(D_N(r,s))=\mathrm{ader\_front}(r,s),
$$

and `normal_frontier_canonical_rows_same_front` proves that the canonical rows
are rows for that same derivative front, not arbitrary combinations of the
global universe.  The wrapper theorem
`normal_canonical_derivative_main_cubic_bound` packages the language equality,
exact front equality, normal-frontier inclusion, same-front row property,
frontier cardinal bound, and whole-regex cubic size bound in one checked
statement.

The checked strong-simplified wrapper is
`normal_canonical_then_strong_main_cubic_bound`.  Since `rsimpStrong_raw`
preserves language and does not increase `rsize`, it proves

$$
\mathcal L(\mathrm{rsimpStrong\_raw}(D_N(r,s)))
= \mathcal L(\mathrm{rders\_pder\_norm}(r,s))
= \mathrm{Ders}(s,\mathcal L(r)),
$$

and

$$
|\mathrm{rsimpStrong\_raw}(D_N(r,s))|
\le 1+(\mathrm{apder\_awidth}(r)+|r|+3)^3.
$$

Thus the clean pipeline "normal Antimirov canonical derivative, then strong
simplify the resulting regex" has a checked cubic regex-size bound.

For the old raw/strong-dcanon row pipeline, the current checked bridge is
still conditional rather than final.  The canonicalized strong rows satisfy

$$
\mathrm{row\_dlformss}
  (\mathrm{rpder\_strong\_dcanon\_rows\_raw}(c,\mathrm{afactored1}(r,s)))
\subseteq
\mathrm{afactored1\_strong\_dlform\_universe}(r,s,c),
$$

so the remaining obligation is a cubic total-size bound for that local
whole-residual universe.  A simpler local argument is known to be false:
`rsimpStrong_raw_row_dlforms_cost_not_monotone` gives an `apder_nf` example
where

$$
\mathrm{rsize\_set}(\mathrm{row\_dlforms}(\mathrm{rsimpStrong\_raw}(p)))=12
\quad\text{but}\quad
\mathrm{rsize\_set}(\mathrm{row\_dlforms}(p))=10.
$$

Thus the unfinished raw-route proof must count global same-front/shared-suffix
structure; it cannot rely on one-step `row_dlforms` cost monotonicity.

The latest checked bridge restates that obligation in same-front row language:

$$
\mathrm{afactored1\_strong\_dlform\_universe}(r,s,c)
\subseteq
\mathrm{rsimpStrong\_dlform\_closure}
  (\mathrm{set}(\mathrm{afactored1}(r,s@[c]))).
$$

The theorem
`rpder_strong_dcanon_rows_raw_afactored1_next_rows_closure_cubic_contractI`
shows that a cubic total-size bound for this next-front rows closure is enough
to recover the old raw strong/dcanon cubic contract.

## Short Answer

For the pure normal Antimirov/factored route, yes: the checked
`normal_canonical_derivative` regex has cubic size as stated above.  This is a
whole-regex theorem for arbitrary derivative string `s`, but it is not the
final strong/memo POSIX theorem.

For the checked one-step strong simplification pipeline, the simplifier-facing
row result has a conditional cubic interface.  More precisely, if one
derivative step starts from a single legacy regex $r$, then the checked
choice-row theorem bounds not only the number of rows but also the total regex
size of all rows:

$$
\mathrm{rsizes}(rows)\le 2(|r|+3)^3.
$$

The same theorem also bounds row count, distinct row count, and
Antimirov-linear-term count by the same cubic expression.  The POSIX-lifted
version replaces $|r|$ by $\mathrm{rxsize}(r)$.

For the whole repeated derivative computation on an arbitrary input string,
the answer is conditional: the accumulator theorem guarantees cubic size as
soon as the chosen active/least-owner row universe satisfies

$$
|U|\cdot M \le K\cdot \mathrm{rxsize}(r)^3.
$$

That universe-cardinality/member-size instantiation is the remaining outer
obligation.  The current exact `sizeNregex` theorem gives the mechanically
checked budget

$$
|\mathrm{sizeNregex}(N)|\cdot N,
$$

which is correct and finite but is not by itself the desired small cubic bound.

This note records the currently checked cubic-bound proof route.  The strongest
fully checked statement is a one-step Antimirov/strong-row cubic bound, lifted
to the POSIX `rerase (intern r)` surface, plus multi-step accumulator contracts
parameterized by a finite closed row universe.  A pure all-input theorem of the
form "the whole memo row universe is bounded by $K |r|^3$" still requires the
separate universe-cardinality instantiation; the checked contracts below are
the proof interface that such an instantiation plugs into.

## Notation

Write

$$
  |r| := \mathrm{rsize}(r)
$$

for raw regular expressions and

$$
  |r|_{\mathrm{POSIX}} := \mathrm{rxsize}(r)
$$

for source POSIX expressions.  In the formalization,

$$
  \mathrm{rsize}(\mathrm{rerase}(\mathrm{intern}\ r)) =
  \mathrm{rxsize}(r)
$$

is checked as `rsize_rerase_intern`, and similarly

$$
  \mathrm{asize}(\mathrm{intern}\ r)=\mathrm{rxsize}(r).
$$

For a list of rows `rows`, the proof tracks four accounting quantities:

$$
\begin{aligned}
  &\mathrm{length}(\mathrm{rows}),\\
  &|\mathrm{set}(\mathrm{rows})|,\\
  &\mathrm{rlinear\_termss}(\mathrm{rows}),\\
  &\mathrm{rsizes}(\mathrm{rows}).
\end{aligned}
$$

The first is list length, the second is distinct row count, the third is the
Antimirov-style number of linear terms after row factoring, and the fourth is
total syntactic size.  Since each row has positive size, the basic bookkeeping
lemmas turn an `rsizes` bound into the other three bounds:

$$
  \mathrm{length}(\mathrm{rows}),
  |\mathrm{set}(\mathrm{rows})|,
  \mathrm{rlinear\_termss}(\mathrm{rows})
  \le \mathrm{rsizes}(\mathrm{rows}).
$$

Formal lemmas:

- `length_le_rsizes`
- `card_set_le_rsizes_early`
- `rlinear_termss_le_rsizes`
- `rpders_strong1_rows_raw_budget_from_rsizes_bound`

## Antimirov Rows

The Antimirov-style generator is `rpder_list`:

$$
\begin{aligned}
  \mathrm{rpder\_list}\ c\ 0 &= [],\\
  \mathrm{rpder\_list}\ c\ 1 &= [],\\
  \mathrm{rpder\_list}\ c\ d &= [1] \quad\text{if } c=d,\\
  \mathrm{rpder\_list}\ c\ (\sum_i r_i)
    &= \mathrm{concat}(\mathrm{map}\ (\mathrm{rpder\_list}\ c)\ [r_i]),\\
  \mathrm{rpder\_list}\ c\ (r_1 r_2)
    &= \{p r_2 : p \in \mathrm{rpder\_list}\ c\ r_1\}
       \cup
       \begin{cases}
         \mathrm{rpder\_list}\ c\ r_2 & \text{if } r_1 \text{ nullable},\\
         [] & \text{otherwise},
       \end{cases}\\
  \mathrm{rpder\_list}\ c\ (r^*)
    &= \{p r^* : p \in \mathrm{rpder\_list}\ c\ r\}.
\end{aligned}
$$

In Isabelle this is the list version of the partial derivative set:

$$
  \mathrm{set}(\mathrm{rpder\_list}\ c\ r)=\mathrm{rpder}\ c\ r.
$$

The normalized row list is

$$
  \mathrm{rpder\_norm\_list}\ c\ r
  = \mathrm{map}\ (\lambda p.\ \mathrm{rsimp4\_SEQ\_atom}\ p\ 1)
      (\mathrm{rpder\_list}\ c\ r).
$$

The key checked Antimirov-size fact is:

$$
  \mathrm{rsizes}(\mathrm{rpder\_norm\_list}\ c\ r)
  \le 2(|r|+3)^3
$$

for legacy raw regexes.  This is theorem
`rsizes_rpder_norm_list_cubic`.

Intuitively, Antimirov produces only one frontier term per consumed symbol
occurrence.  The proof does not try to count simplified derivatives by their
final syntax directly; it first bounds the generated linear-form frontier and
then proves that the later row simplifications are size non-increasing relative
to that generated frontier.

## Product-Term Split

The new pure factored file isolates the "split the row first" invariant:

- `AntimirovFactoredTransition.thy:aseq_terms`
- `AntimirovFactoredTransition.thy:aseq_termss`

These split top-level alternatives and `RSEQ` products into Antimirov-style
terms.  The checked step lemma is:

- `rpder_norm_list_aseq_terms_subsetI`

It says that if a universe $U$ contains $0,1$, is closed under subterms, and is
closed under the predecessor step for counted repetitions
$RNTIMES(r,n+1)\mapsto RNTIMES(r,n)$, then one pure Antimirov derivative step
does not introduce new product-split terms outside $U$.

The arbitrary-input induction is:

- `afactored_steps_aseq_terms_closed_legacy_subsetI`
- `afactored1_aseq_terms_cubic_universe_structuralI`

The root-derived frontier universe now discharges those structural obligations.
The checked unconditional theorem is:

- `afactored1_aseq_terms_frontier_universe_contract`

For every legacy raw regex $r$ and input string $s$,

$$
\begin{aligned}
  \mathrm{aseq\_termss}(\mathrm{afactored1}\ r\ s)
    &\subseteq \mathrm{partial\_derivative\_frontier\_universe}(r),\\
  |\mathrm{aseq\_termss}(\mathrm{afactored1}\ r\ s)|
    &\le (|r|+2)^2,\\
  q \in \mathrm{aseq\_termss}(\mathrm{afactored1}\ r\ s)
    &\Longrightarrow |q|\le 1+2|r|.
\end{aligned}
$$

The key new closure fact is
`partial_derivative_frontier_universe_ntimes_predecessor`: if
$RNTIMES(q,n+1)$ is already in the frontier universe of $r$, then
$RNTIMES(q,n)$ is also in that same universe.  This matches the counted-repeat
case in Antimirov's linear-form proof.

This is the precise formal version of "after arbitrarily many derivatives, if
we split products into Antimirov terms, the terms are still chosen from the
same original finite frontier."  What it does not yet prove is that the concrete
raw row syntax used by the strong scanner has total `rsizes` bounded solely by
this term set; that needs a row-owner/factored-row bridge controlling product
chains and the strong prune/absorb representation.

## One-Step Main Theorem

The current proof-facing row choice is:

$$
\begin{aligned}
\mathrm{rpder\_strong\_rows\_clean\_terms\_choice}\ c\ rs\ rows
\quad\Longleftrightarrow\quad
& rows = \mathrm{rpder\_strong\_rows\_clean}\ c\ rs\\
&\lor\ 
  \mathrm{rpder\_strong\_rows\_clean\_terms\_absorbed\_pruned}\ c\ rs\ rows.
\end{aligned}
$$

This says: either use the clean Antimirov-shaped fallback rows, or use the
scan/prune rows after only the safe absorbed/pruned transformations whose
budget is known not to exceed the generated Antimirov rows.

### Theorem 1: one-step choice-row cubic bound

If `legacy_rrexp r` and

$$
  \mathrm{rpder\_strong\_rows\_clean\_terms\_choice}\ c\ [r]\ rows,
$$

then

$$
  \mathrm{RLS}(\mathrm{set}\ rows)=\mathrm{Der}\ c\ (\mathrm{RL}\ r)
$$

and all four row budgets satisfy

$$
\begin{aligned}
  \mathrm{length}(rows) &\le 2(|r|+3)^3,\\
  |\mathrm{set}(rows)| &\le 2(|r|+3)^3,\\
  \mathrm{rlinear\_termss}(rows) &\le 2(|r|+3)^3,\\
  \mathrm{rsizes}(rows) &\le 2(|r|+3)^3.
\end{aligned}
$$

Formal theorem:

- `rpder_strong_rows_clean_terms_choice_single_cubic_budget_contract`

Proof structure:

1. Correctness:

   $$
     \mathrm{RLS}(\mathrm{set}\ rows)
     = \mathrm{Der}\ c\ (\mathrm{RL}\ r)
   $$

   follows by case analysis on the choice relation:

   - clean fallback uses `RLS_rpder_strong_rows_clean`;
   - safe absorbed/pruned rows use
     `RLS_rpder_strong_rows_clean_terms_absorbed_pruned`.

   This is packaged as
   `RLS_rpder_strong_rows_clean_terms_choice`.

2. Generated-frontier budget:

   $$
   \begin{aligned}
     \mathrm{length}(rows),\ 
     |\mathrm{set}(rows)|,\ 
     \mathrm{rlinear\_termss}(rows),\ 
     \mathrm{rsizes}(rows)
     \le
     \mathrm{rsizes}(
       \mathrm{concat}(
         \mathrm{map}\ (\mathrm{rpder\_norm\_list}\ c)\ [r])).
   \end{aligned}
   $$

   This is `rpder_strong_rows_clean_terms_choice_generated_budget`.

3. For a singleton list:

   $$
   \mathrm{rsizes}(
     \mathrm{concat}(
       \mathrm{map}\ (\mathrm{rpder\_norm\_list}\ c)\ [r]))
   =
   \mathrm{rsizes}(\mathrm{rpder\_norm\_list}\ c\ r).
   $$

4. Apply the Antimirov cubic bound:

   $$
     \mathrm{rsizes}(\mathrm{rpder\_norm\_list}\ c\ r)
     \le 2(|r|+3)^3.
   $$

Combining (2)--(4) gives the four cubic inequalities.

## POSIX Lift

The raw theorem is lifted to source POSIX regexes by erasing the annotations
introduced by `intern`.

### Theorem 2: POSIX one-step choice-row cubic bound

If `legacy_rexp r` and

$$
  \mathrm{rpder\_strong\_rows\_clean\_terms\_choice}\ c\
    [\mathrm{rerase}(\mathrm{intern}\ r)]\ rows,
$$

then

$$
  \mathrm{RLS}(\mathrm{set}\ rows)
  = \mathrm{Der}\ c\ (\mathrm{RL}(\mathrm{rerase}(\mathrm{intern}\ r)))
$$

and

$$
\begin{aligned}
  \mathrm{length}(rows) &\le 2(|r|_{\mathrm{POSIX}}+3)^3,\\
  |\mathrm{set}(rows)| &\le 2(|r|_{\mathrm{POSIX}}+3)^3,\\
  \mathrm{rlinear\_termss}(rows) &\le 2(|r|_{\mathrm{POSIX}}+3)^3,\\
  \mathrm{rsizes}(rows) &\le 2(|r|_{\mathrm{POSIX}}+3)^3.
\end{aligned}
$$

Formal theorem:

- `rpder_strong_rows_clean_terms_choice_rerase_intern_single_cubic_budget_contract`

The proof is one line after Theorem 1:

$$
  \mathrm{legacy\_rrexp}(\mathrm{rerase}(\mathrm{intern}\ r))
$$

comes from `legacy_rerase_intern`, and

$$
  \mathrm{rsize}(\mathrm{rerase}(\mathrm{intern}\ r))
  = \mathrm{rxsize}(r)
$$

converts the bound from raw size to POSIX size.

There is also a raw strong-row version, without the choice relation:

- `rpder_strong_rows_raw_rerase_intern_single_cubic_budget_contract`

It proves the same one-step correctness and budget bounds for

$$
  \mathrm{rpder\_strong\_rows\_raw}\ c\
    [\mathrm{rerase}(\mathrm{intern}\ r)].
$$

## Multi-Step Accumulator Interface

For an input string $s$, the raw row accumulator is

$$
  \mathrm{rpders\_strong1\_rows\_raw}\ 
    (\mathrm{rerase}(\mathrm{intern}\ r))\ s.
$$

The proof does not count this list by expanding every derivative tree.  Instead
it shows that, if all rows stay inside a finite closed universe $U$, then the
four budgets are bounded by

$$
  |U| \cdot M,
$$

where $M$ is a uniform member-size bound for rows in $U$.

### Theorem 3: active-suffix universe accumulator contract

Assume:

$$
\begin{aligned}
&\mathrm{legacy\_rexp}\ r,\\
&\mathrm{rerase}(\mathrm{intern}\ r)\in U,\\
&q\in U \Rightarrow \mathrm{set}(\mathrm{rflts}[q])\subseteq U,\\
&\text{normalized strong raw one-step rows from } U \text{ stay in } U,\\
&\mathrm{raw\_shared\_prune\_active\_suffix\_closure}(U)\subseteq U,\\
&q\in U \Rightarrow \mathrm{rsubterms}(q)\subseteq U,\\
&\mathrm{finite}(U),\\
&|U|\le C,\\
&q\in U \Rightarrow \mathrm{rsize}(q)\le M,\\
&C\cdot M\le B.
\end{aligned}
$$

Then the POSIX row gate is correct and the accumulator budgets satisfy

$$
\begin{aligned}
  \mathrm{asizes}(
    \mathrm{bpders\_strong1\_rows}(\mathrm{intern}\ r)\ s)
    &\le B,\\
  \mathrm{length}(
    \mathrm{rpders\_strong1\_rows\_raw}
      (\mathrm{rerase}(\mathrm{intern}\ r))\ s)
    &\le B,\\
  |\mathrm{set}(
    \mathrm{rpders\_strong1\_rows\_raw}
      (\mathrm{rerase}(\mathrm{intern}\ r))\ s)|
    &\le B,\\
  \mathrm{rlinear\_termss}(
    \mathrm{rpders\_strong1\_rows\_raw}
      (\mathrm{rerase}(\mathrm{intern}\ r))\ s)
    &\le B,\\
  \mathrm{rsizes}(
    \mathrm{rpders\_strong1\_rows\_raw}
      (\mathrm{rerase}(\mathrm{intern}\ r))\ s)
    &\le B.
\end{aligned}
$$

It also proves the bridge

$$
  \mathrm{map}\ \mathrm{rerase}\
    (\mathrm{bpders\_strong1\_rows}(\mathrm{intern}\ r)\ s)
  =
  \mathrm{rpders\_strong1\_rows\_raw}
    (\mathrm{rerase}(\mathrm{intern}\ r))\ s.
$$

Formal theorem:

- `strong_deferred_row_gate_norm_active_suffix_universe_accumulator_POSIX_contract`

This is the main parameterized cubic interface.  To get a concrete cubic bound,
instantiate it with a universe satisfying, for $n=|r|_{\mathrm{POSIX}}$,

$$
  |U|\le A n^2,\qquad
  \forall q\in U.\ \mathrm{rsize}(q)\le M_0 n.
$$

Then choose

$$
  B = A M_0 n^3.
$$

The theorem gives all five annotated/raw accumulator budgets bounded by
$A M_0 n^3$, together with POSIX correctness.

## Checked Size-$N$ Main Contract

The exact checked `sizeNregex` contract is a convenient closed-universe
instance.  Let

$$
  \mathrm{sizeNregex}(N)=\{q\mid \mathrm{legacy\_rrexp}(q)
    \land \mathrm{rsize}(q)\le N\}.
$$

### Theorem 4: exact `sizeNregex` POSIX accumulator contract

Assume:

$$
\begin{aligned}
&\mathrm{legacy\_rexp}\ r,\\
&\mathrm{rxsize}(r)\le N,\\
&\text{the normalized raw strong step is closed in }
  \mathrm{sizeNregex}(N).
\end{aligned}
$$

Then the POSIX matcher based on

$$
  \mathrm{bnullable}(
    \mathrm{bders\_simpStrong}(\mathrm{intern}\ r)\ s)
$$

is correct:

$$
  \left(
    \text{the gate returns } \mathrm{Some}\ v
  \right)
  \Longleftrightarrow
  s\in r\to v,
$$

and its failure case is also exact:

$$
  \left(
    \text{the gate returns } \mathrm{None}
  \right)
  \Longleftrightarrow
  \neg\exists v.\ s\in r\to v.
$$

Moreover, if it returns a value, then

$$
  \mathrm{flat}(v)=s.
$$

The row budgets are:

$$
\begin{aligned}
  \mathrm{asizes}(
    \mathrm{bpders\_strong1\_rows}(\mathrm{intern}\ r)\ s)
    &\le |\mathrm{sizeNregex}(N)|\cdot N,\\
  \mathrm{length}(
    \mathrm{rpders\_strong1\_rows\_raw}
      (\mathrm{rerase}(\mathrm{intern}\ r))\ s)
    &\le |\mathrm{sizeNregex}(N)|\cdot N,\\
  |\mathrm{set}(
    \mathrm{rpders\_strong1\_rows\_raw}
      (\mathrm{rerase}(\mathrm{intern}\ r))\ s)|
    &\le |\mathrm{sizeNregex}(N)|\cdot N,\\
  \mathrm{rlinear\_termss}(
    \mathrm{rpders\_strong1\_rows\_raw}
      (\mathrm{rerase}(\mathrm{intern}\ r))\ s)
    &\le |\mathrm{sizeNregex}(N)|\cdot N,\\
  \mathrm{rsizes}(
    \mathrm{rpders\_strong1\_rows\_raw}
      (\mathrm{rerase}(\mathrm{intern}\ r))\ s)
    &\le |\mathrm{sizeNregex}(N)|\cdot N.
\end{aligned}
$$

Formal theorem:

- `strong_deferred_original_sizeNregex_active_suffix_memo_POSIX_accumulator_exact_budget_contract`

This theorem is exact but not itself the desired small cubic statement, because
the formalization does not use a cubic estimate for
$|\mathrm{sizeNregex}(N)|$.  It is useful because it proves that the final
accumulator proof has the right shape: once the active universe is replaced by
a smaller Antimirov/least-owner universe with cubic cardinality times member
size, the same proof gives the cubic bound.

## Least-Owner DAG Bridge

The latest smaller-universe bridge is:

- `rpders_strong1_rows_raw_intern_least_owner_dag_budget_boundI`
- `strong_deferred_row_gate_least_owner_dag_accumulator_POSIX_contract`
- `strong_deferred_row_gate_norm_active_suffix_universe_accumulator_POSIX_contract`

The first theorem says that if the least-owner DAG universe is finite and every
member has size at most $M$, then

$$
\begin{aligned}
  \mathrm{length}(A_s),\
  |\mathrm{set}(A_s)|,\
  \mathrm{rlinear\_termss}(A_s),\
  \mathrm{rsizes}(A_s)
  \le
  |\mathrm{leastOwnerDag}(r,s)|\cdot M,
\end{aligned}
$$

where

$$
  A_s =
  \mathrm{rpders\_strong1\_rows\_raw}
    (\mathrm{rerase}(\mathrm{intern}\ r))\ s.
$$

The second theorem adds POSIX correctness and the annotated/raw erasure bridge.
The third theorem shows how to obtain the least-owner DAG assumptions from any
active-suffix universe $U$ satisfying closure, finiteness, cardinality, and
member-size bounds.

This is the point where the current proof most closely follows the Antimirov
linear-forms argument: the accumulator is charged to a finite set of active
linear forms/row owners, and the row-count, term-count, and total-size budgets
all reduce to cardinality times a member-size bound.

## Proof Summary

The checked proof has the following spine.

1. Antimirov generation:

   $$
     \mathrm{set}(\mathrm{rpder\_list}\ c\ r)=\mathrm{rpder}\ c\ r.
   $$

2. Generated frontier bound:

   $$
     \mathrm{rsizes}(\mathrm{rpder\_norm\_list}\ c\ r)
     \le 2(|r|+3)^3.
   $$

3. Strong-row simplification is budget-preserving relative to generated rows:

   clean rows, term-absorbed rows, pruned rows, and raw rows all have
   `length`, `card (set ...)`, `rlinear_termss`, and `rsizes` bounded by the
   generated `rpder_norm_list` budget.

4. Therefore one derivative step from `[r]` has cubic row budget:

   $$
   \#\mathrm{rows},\ \#\mathrm{linearTerms},\ \mathrm{totalSize}
   \le 2(|r|+3)^3.
   $$

5. POSIX `intern`/`rerase` preserves the size measure:

   $$
     |\mathrm{rerase}(\mathrm{intern}\ r)|=|r|_{\mathrm{POSIX}}.
   $$

6. Multi-step accumulation is bounded by a finite closed universe:

   $$
     \mathrm{rsizes}(A_s)\le |U|\cdot M.
   $$

7. If the chosen active universe satisfies

   $$
     |U|\cdot M\le K |r|_{\mathrm{POSIX}}^3,
   $$

   then all accumulator budgets are cubic, and the POSIX matcher remains
   correct.

## Verification

The following checks passed after the latest proof edits:

- `isabelle build -D . Posix`
- full CI via
  `agent_hunt_pipeline/scripts/isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 240`

The full CI included:

- known scan-vs-Antimirov row-diff regressions: 9 cases, `observations=0`;
- exhaustive row comparison: 84,300 regex/input pairs, `observations=0`;
- Isabelle sessions `Posix` and `BackRefPilot`.

Additional deeper fuzzing at depth 10 / input length 24 on seeds
`20260800..20260804` checked 10,000 random cases and found no actionable
scan/prune row witness worse than the Antimirov strong linear-form rows.

## Status

Closed and checked:

- one-step Antimirov/strong-row cubic bound;
- POSIX-lifted one-step cubic bound;
- raw strong-row one-step cubic bound;
- pure Antimirov product-term split closure for arbitrary many derivatives,
  unconditionally inside `partial_derivative_frontier_universe r`, with
  quadratic term-cardinality and linear member-size bounds;
- finite-universe accumulator contract;
- least-owner DAG accumulator bridge;
- exact `sizeNregex` POSIX accumulator budget contract;
- scan-vs-Antimirov comparison harness at the current fixed point.

Still not claimed as a final standalone theorem:

- a pure all-input statement eliminating the universe assumptions by proving
  the selected active/least-owner universe has
  $|U|\cdot M \le K |r|_{\mathrm{POSIX}}^3$ for a fixed constant $K$.
- a representation theorem turning the bounded Antimirov split-term vocabulary
  into a bounded concrete raw-row/strong-simplifier `rsizes` universe.
