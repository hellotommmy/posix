下面给一个可以直接交给本机 IDE agents 的执行计划。核心原则是：**先手工 adversarial design，再写定义，再证明小 lemma，最后才合并成大证明**。Python 只做 sanity/regression，不再作为“先猜后测”的主流程。

当前正式目标仍是旧的 `apder_strong_dlfrontier` 线性计数；Gate 已经 green，只差线性 row-count，且任意线性界都够，二次界不够。旧定义中 `σ4/σ7/S/row_dlforms/strong_apder_acc` 的形状和 cross-prune wall 是问题根源。 

---

# 0. 总路线

不要再证明：

[
U_{\mathrm{old}}(r)\subseteq U_N(r)
]

也不要证明：

[
\mathrm{oldActualRows}(r)\subseteq U_N(r).
]

这两个 exact containment 都会被

[
b^\star\cdot(a^\star\cdot a^\star)
]

这种 row 打爆。

要证明的是：

[
U_{\mathrm{old}}(r)
\hookrightarrow
U_N^#(r),
\qquad
|U_N^#(r)|\le C|r|+D.
]

其中 (U_N^#) 是 **带 provenance 的 normalized universe**。它的 row 部分用新 normalizer (N) 压缩，provenance 部分记录“旧 syntactic row 为什么会存在”。这样旧 row 可以 inject 进去，但总数仍线性。

最终链条是：

[
U_{\mathrm{old}}(r)
\subseteq
\mathrm{strong_apder_acc}(r,1)
\hookrightarrow
A_N^#(r,1)
]

并证明

[
|A_N^#(r,1)|\le C|r|+D.
]

然后旧 Gate 仍然可用，因为现有 black-box 只需要旧 `apder_strong_dlfrontier` 的线性 card bound。 

---

# 1. Repo / worktree 布局

建议每个 lane 一个 worktree，避免互相污染。

```text
../wt-norm-00-base
../wt-norm-01-alpha
../wt-norm-02-opening
../wt-norm-03-count
../wt-norm-04-shadow
../wt-norm-05-prov
../wt-norm-06-integrate
../wt-norm-07-actual-rewrite-backup
```

对应 branches：

```text
norm/00-base
norm/01-alpha
norm/02-opening
norm/03-count
norm/04-shadow
norm/05-prov
norm/06-integrate
norm/07-actual-rewrite-backup
```

建议新增目录：

```text
cubic/Normalized/
  NormalizedAppend.thy
  NormalizedStrong.thy
  NormalizedOpening.thy
  NormalizedAccumulator.thy
  NormalizedCount.thy
  NormalizedShadow.thy
  NormalizedProvenance.thy
  NormalizedGateBridge.thy

experiments/norm/
  norm_model.py
  adversarial_families.py
  README.md

docs/norm-route/
  00-design.md
  01-adversarial.md
  02-lemma-map.md
  03-failures.md
```

每个 agent 先写自己的：

```text
docs/norm-route/<lane>-adversarial.md
```

内容必须包括：

1. 要证明的 lemma；
2. 为什么旧反例不直接杀死它；
3. 主动构造的小反例尝试；
4. 如果失败，最小失败例；
5. 该 lane 是否继续 formalize。

---

# 2. 全局纪律

每个 worktree 都必须遵守：

```bash
grep -R "sorry\|oops\|admit" -n cubic/Normalized && exit 1
isabelle build -D .
```

`.thy` 文件里不要放未证 lemma。可以把 conjecture 放进 markdown，不要用 `sorry` 留在 theory 里。

Python 用于：

1. 检查新定义是否符合预期；
2. replay named counterexamples；
3. 检查小尺寸 exhaustive；
4. 找最小失败例。

但是每个新假说先要有手工 adversarial 分析，再写 Python。

---

# 3. Wave 0：共同基线

## Worktree

```text
../wt-norm-00-base
```

## 目标

建立共享文档和 Python faithful model。这个 model 不负责“证明”，只负责 regression。

## 文件

```text
experiments/norm/norm_model.py
experiments/norm/adversarial_families.py
docs/norm-route/00-design.md
docs/norm-route/01-adversarial.md
docs/norm-route/02-lemma-map.md
```

## 必须 encode 的 regression examples

1. 旧 SAA/RALTS leak：

[
1+(b^\star\cdot a^\star),\quad k=a^\star.
]

2. 两分支 RALTS failure：

[
(b^\star\cdot a^\star)+(c^\star\cdot a^\star),\quad k=a^\star.
]

3. collapsing-tail CE：

[
(1+((a+1)\cdot a^\star)+a)\cdot a^\star.
]

4. reachable-wrapper：

[
d\cdot(((b^\star a^\star)+(c^\star a^\star))\cdot a^\star).
]

5. deep tail：

[
b^\star\cdot(a^\star\cdot(a^\star\cdots a^\star)).
]

6. awidth refutation：

[
1+(c^\star+1)^\star.
]

7. unreachable-continuation leak：

[
k=b^\star\cdot b^\star
]

as a standalone continuation.

## Acceptance

Python reproduces old known failures and confirms:

```text
old exact containment into normalized U_N fails
normalized shadow membership plausibly holds
```

This lane should also write a one-page “do not prove these” list.

---

# 4. Wave 1A：定义 normalized append (\alpha)

## Worktree

```text
../wt-norm-01-alpha
```

## Theory

```text
cubic/Normalized/NormalizedAppend.thy
```

## 关键设计

不要直接用递归式：

[
\alpha(r_1\cdot r_2,k)=\alpha(r_1,\alpha(r_2,k))
]

来定义 Isabelle function。这个 termination 会很麻烦。

建议用 **sequence spine**：

```isabelle
fun seq_factors :: "rrexp => rrexp list"
fun mk_seq      :: "rrexp list => rrexp"
fun norm_seq    :: "rrexp list => rrexp list"
definition nplug :: "rrexp => rrexp => rrexp"
```

数学定义：

[
\mathrm{fac}(r_1\cdot r_2)=\mathrm{fac}(r_1)@\mathrm{fac}(r_2),
\qquad
\mathrm{fac}(r)=[r]\quad\text{otherwise}.
]

`norm_seq` 做三件事：

1. 删除 (1)；
2. 若出现 (0)，整条 sequence 变成 ([0])；
3. 折叠相邻相同 star：

[
\ldots,x^\star,x^\star,\ldots
\mapsto
\ldots,x^\star,\ldots.
]

然后：

[
\alpha(r,k)
:=
\mathrm{mkSeq}\bigl(\mathrm{normSeq}(\mathrm{fac}(r)@\mathrm{fac}(k))\bigr).
]

`mk_seq` 右结合：

[
[]\mapsto 1,
\quad
[x]\mapsto x,
\quad
x::xs\mapsto x\cdot \mathrm{mkSeq}(xs).
]

## 必证小 lemma

先证明 list 层 lemma，不要直接冲 rrexp 层。

```isabelle
norm_seq_idem:
  norm_seq (norm_seq xs) = norm_seq xs

norm_seq_append_assoc:
  norm_seq (norm_seq (xs @ ys) @ zs)
  = norm_seq (xs @ ys @ zs)

nplug_assoc:
  nplug (nplug r k) h = nplug r (nplug k h)
```

可能需要把 `nplug_assoc` 限制在 `nseq_normal` 上。若 unrestricted 失败，先报告最小反例，不要硬证。

## Adversarial 手工检查

必须手算：

[
\alpha(b^\star\cdot a^\star,a^\star)=b^\star\cdot a^\star.
]

[
\alpha(b^\star\cdot(a^\star\cdot a^\star),a^\star)
==================================================

b^\star\cdot a^\star.
]

[
\alpha((b^\star+c^\star),a^\star)
=================================

(b^\star+c^\star)\cdot a^\star.
]

最后一个不能被错误分配；分配只属于 opening，不属于 append。

## Acceptance

1. `NormalizedAppend.thy` green；
2. no sorry/oops/admit；
3. `nplug_assoc` 或明确 weaker lemma green；
4. Python 中 `nplug` 通过 regression examples。

---

# 5. Wave 1B：定义新 normalizer (N)

## Worktree

继续 `../wt-norm-01-alpha` 或新分支：

```text
../wt-norm-01-alpha
```

## Theory

```text
cubic/Normalized/NormalizedStrong.thy
```

## 定义

```isabelle
fun nstrong :: "rrexp => rrexp"
```

数学定义：

[
N(0)=0,\quad N(1)=1,\quad N(c)=c.
]

[
N(r_1\cdot r_2)=\alpha(N(r_1),N(r_2)).
]

[
N(r^\star)=
\begin{cases}
1,&N(r)=0,\
1,&N(r)=1,\
s^\star,&N(r)=s^\star,\
N(r)^\star,&\text{otherwise}.
\end{cases}
]

Alternation：

[
N(\sum_i r_i)=\mathrm{nalts}(\mathrm{map}\ N\ r_i).
]

其中 `nalts` 不能继续用旧 `rsimpStrong_ALTs_raw`。要复制旧 prune 形状，但 pair-prune 里用 (\alpha)，不用 `σ7`。

定义：

```isabelle
definition nprune_pair :: "rrexp => rrexp => rrexp"
```

只在同形时触发：

[
e=(\sum lrs)\cdot k,\quad
l=(\sum rrs)\cdot k.
]

则：

[
\mathrm{nprunePair}(e,l)
========================

\alpha(\mathrm{alts}(rrs\setminus lrs),k).
]

其他情况 later 不变。

然后：

```isabelle
fun nprune_against_rows
fun nprune_rows_acc
definition nprune_rows
definition nalts
```

结构和旧 `rsimpStrong_prune_rows_raw` 一致，但 replug 换成 `nplug/alpha`。旧 prune 的形状和 source of wall 在定义文件里已经明确。

## 必证 lemma

```isabelle
nstrong_idem:
  nstrong (nstrong r) = nstrong r

nstrong_nplug:
  nstrong (rsimp4_SEQ_atom r k)
  = nplug (nstrong r) (nstrong k)
```

第二个是整条路线的核心。如果失败，整条 (N)-route 需要重设。

还要证 size：

```isabelle
rsize_nstrong_le:
  rsize (nstrong r) <= rsize r

rsize_nplug_le:
  rsize (nplug r k) <= rsize r + rsize k
```

若 alternation prune 让 `nstrong_idem` 难证，可以先只证明 clean fragment 上的版本：

```isabelle
apder_clean r ==> nstrong (nstrong r) = nstrong r
```

## Adversarial 检查

必须针对 old cross-prune CE 手算：

[
N\bigl(a\cdot(a^\star\cdot a^\star)\bigr)
=========================================

a\cdot a^\star.
]

[
N(a^\star\cdot a^\star)=a^\star.
]

并检查 `nalts` prune 后不会重新制造 unnormalized tail。

## Acceptance

1. `nstrong_nplug` green，至少 clean fragment 版本；
2. `nstrong_idem` green，至少 clean fragment 版本；
3. old CE 被 (N) 压掉；
4. 没有使用旧 `rsimpStrong_raw` 作为核心 normalizer。

---

# 6. Wave 2A：定义新 opening (\delta_N)

## Worktree

```text
../wt-norm-02-opening
```

## Theory

```text
cubic/Normalized/NormalizedOpening.thy
```

## 定义

```isabelle
function ndlforms :: "rrexp => rrexp set"
```

数学定义：

[
\delta_N(0)=\varnothing.
]

[
\delta_N(\sum_i r_i)=\bigcup_i\delta_N(r_i).
]

[
\delta_N((\sum_i p_i)\cdot k)
=============================

\bigcup_i\delta_N(\alpha(p_i,k)).
]

其他：

[
\delta_N(r)=F(r).
]

注意 termination：输入

[
(\sum_i p_i)\cdot k
]

大小比每个

[
\alpha(p_i,k)
]

大至少一个 `RALTS` node。需要用 `rsize_nplug_le` 或专门 lemma 支撑 termination。

## 必证 lemma

```isabelle
ndlforms_finite:
  finite (ndlforms r)

old_opening_shadow:
  x ∈ row_dlforms r
  ==> nstrong x ∈ ndlforms (nstrong r)
```

这是 shadow bridge 的第一块。

如果 unrestricted 失败，改成：

```isabelle
apder_nf r ==> x ∈ row_dlforms r ==> nstrong x ∈ ndlforms (nstrong r)
```

或者：

```isabelle
x ∈ row_dlforms (rsimpStrong_raw r)
==> nstrong x ∈ ndlforms (nstrong r)
```

但要记录为什么 weakening 足够用于 old `strong_apder_acc`。

## Adversarial 检查

必须手算：

旧：

[
row_dlforms((q_b+q_c)\cdot a^\star)
===================================

{b^\star(a^\star a^\star),c^\star(a^\star a^\star)}.
]

新 shadow：

[
\delta_N(N((q_b+q_c)\cdot a^\star))
===================================

{b^\star a^\star,c^\star a^\star}.
]

所以 exact containment false，但 shadow containment true。

## Acceptance

`old_opening_shadow` green 或有精确 weaker lemma + justification。

---

# 7. Wave 2B：定义 normalized accumulator (A_N)

## Worktree

```text
../wt-norm-02-opening
```

## Theory

```text
cubic/Normalized/NormalizedAccumulator.thy
```

## 定义

```isabelle
fun nterm_acc :: "rrexp => rrexp => rrexp set"
definition nacc :: "rrexp => rrexp => rrexp set"
definition nbase :: "rrexp => rrexp set"
```

数学定义：

[
T_N(0,k)=T_N(1,k)=\varnothing.
]

[
T_N(c,k)=F(k).
]

[
T_N(r_1+r_2+\cdots,k)=\bigcup_i T_N(r_i,k).
]

[
T_N(r_1\cdot r_2,k)
===================

T_N(r_1,\alpha(N(r_2),k))
\cup
T_N(r_2,k).
]

[
T_N(r^\star,k)
==============

T_N(r,\alpha(N(r^\star),k)).
]

Then:

[
A_N(r,k)
========

\delta_N(\alpha(N(r),k))
\cup
\bigcup_{p\in T_N(r,k)}\delta_N(p).
]

[
B_N(k)=A_N(1,k)=\delta_N(k).
]

## 必证 recurrence

```isabelle
nacc_RSEQ_subset:
  nacc (RSEQ r1 r2) k
  ⊆ nacc r1 (nplug (nstrong r2) k) ∪ nacc r2 k

nacc_RALTS_subset:
  nacc (RALTS rs) k
  ⊆ (⋃q∈set rs. nacc q k)

nacc_RSTAR_subset:
  nacc (RSTAR r) k
  ⊆ ndlforms (nplug (nstrong (RSTAR r)) k)
     ∪ nacc r (nplug (nstrong (RSTAR r)) k)

nbase_sigma_subset:
  nbase (nplug (nstrong r) k) ⊆ nacc r k
```

这些是新 telescope 的基础，类似旧 green SAA diff machinery，但不再混用旧 `σ4/σ7/S`。旧 SAA 中 RSEQ/RSTAR/RCHAR 已 green，RALTS under continuation leaky；本路线就是为了用同一套 (N,\alpha,\delta_N) 消除这种不一致。 

## Acceptance

四个 recurrence 至少 subset 版本 green。

---

# 8. Wave 3：内部 normalized count

## Worktree

```text
../wt-norm-03-count
```

## Theory

```text
cubic/Normalized/NormalizedCount.thy
```

## 目标

先证明无 provenance 的内部 count：

```isabelle
lemma card_nacc_diff_base_le:
  assumes "apder_clean r" "nstrong k = k"
  shows "card (nacc r k - nbase k) <= rsize r"
```

如果 exact `<= rsize r` 太紧，允许：

```isabelle
card (nacc r k - nbase k) <= C * rsize r + D
```

只要常数固定即可。

## 构造

按 constructor induction：

### RZERO/RONE

空。

### RCHAR

最多一个 root row：

[
|A_N(c,k)-B_N(k)|\le1.
]

### RSEQ

用 telescope：

[
A_N(r_1r_2,k)
\subseteq
A_N(r_1,\alpha(Nr_2,k))\cup A_N(r_2,k).
]

且：

[
B_N(\alpha(Nr_2,k))\subseteq A_N(r_2,k).
]

于是：

[
|A_N(r_1r_2,k)-B_N(k)|
\le
|A_N(r_1,k')-B_N(k')|
+
|A_N(r_2,k)-B_N(k)|.
]

### RALTS

由 subset：

[
A_N(\sum_i r_i,k)\subseteq\bigcup_i A_N(r_i,k).
]

所以：

[
|A_N(\sum_i r_i,k)-B_N(k)|
\le
\sum_i |A_N(r_i,k)-B_N(k)|.
]

不需要 `+1`。

### RSTAR

root 最多一个，再递归：

[
|A_N(r^\star,k)-B_N(k)|
\le
1+|A_N(r,k')-B_N(k')|.
]

## Adversarial 检查

必须在 markdown 里解释：

1. 为什么旧两分支 RALTS counterexample 不打爆这个 count；
2. 为什么 deep-tail 不产生超线性；
3. 为什么 `RALTS` 不需要 `+1`；
4. 为什么 product tagging 不在这里出现。

## Acceptance

1. 内部 count theorem green；
2. 如果只得到 (C|r|+D)，记录 (C,D)；
3. Python exhaustive 小尺寸验证 `card(nacc r RONE) <= C*rsize r+D`。

---

# 9. Wave 4：old-to-new normalized shadow

## Worktree

```text
../wt-norm-04-shadow
```

## Theory

```text
cubic/Normalized/NormalizedShadow.thy
```

## 目标

证明旧 SAA rows 的 normalized shadow 落入新 (A_N)。

先做 set 版本：

```isabelle
lemma old_acc_shadow:
  assumes "apder_nf r" "apder_nf k"
  assumes "x ∈ strong_apder_acc r k"
  shows "nstrong x ∈ nacc r (nstrong k)"
```

如果 base/diff 需要更精细，拆成：

```isabelle
x ∈ row_dlforms (rsimpStrong_raw p)
==> nstrong x ∈ ndlforms (nstrong p)
```

和：

```isabelle
p ∈ rfrontier (rsimp4_SEQ_atom r k)
   ∪ apder_term_frontier_acc r k
==> nstrong p ∈ root_or_term_carrier_N r (nstrong k)
```

## 关键 lemmas

```isabelle
nstrong_rsimpStrong_shadow:
  nstrong (rsimpStrong_raw r) = nstrong r

nstrong_rsimp4_shadow:
  nstrong (rsimp4_SEQ_atom r k)
  = nplug (nstrong r) (nstrong k)

old_term_acc_shadow:
  p ∈ apder_term_frontier_acc r k
  ==> nstrong p ∈ nterm_acc r (nstrong k)
```

其中 `old_term_acc_shadow` 应按 constructor induction 做。

## Adversarial 检查

必须解释下面例子：

[
x=b^\star(a^\star a^\star)
\notin U_N
]

但：

[
N(x)=b^\star a^\star\in U_N.
]

所以 theorem 必须是 shadow，不是 containment。

## Acceptance

`old_acc_shadow` green，或者得到足够用于 provenance injection 的版本。

---

# 10. Wave 5：provenance-indexed universe (A_N^#)

## Worktree

```text
../wt-norm-05-prov
```

## Theory

```text
cubic/Normalized/NormalizedProvenance.thy
```

这是主战场。

## 不能做什么

不能定义：

[
A_N^#(r,k)=A_N(r,k)\times \Pi(r)
]

因为这会导致 quadratic。

不能把 provenance tag 定义成旧 row 本身，因为那是 tautological，无法计数。

## 推荐 datatype

```isabelle
datatype prov =
    PRoot
  | PTerm
  | PSeqL prov
  | PSeqR prov
  | PAlt nat prov
  | PStar prov
  | POpenAlt nat
  | PTailFold nat
  | PPrune nat nat
```

但注意：`nat` 不能随便无限用。每个 `nat` 必须绑定到 list index 或 constructor occurrence，最终能 charge 到 `rsize r`。

如果 Isabelle 里 index 麻烦，可以先用 path：

```isabelle
datatype side = L | R | S | A nat
type_synonym path = "side list"
```

tag 为：

```isabelle
datatype prov = Prov path prov_kind
datatype prov_kind = Root | Term | OpenAlt | TailFold | Prune
```

## 定义目标

不要先定义全局 product。定义递归 excess set：

```isabelle
fun nacc_excess_sharp :: "rrexp => rrexp => (prov × rrexp) set"
```

数学形状：

[
E_N^#(0,k)=E_N^#(1,k)=\varnothing.
]

[
E_N^#(c,k)={(\mathrm{root},x)\mid x\in \delta_N(\alpha(c,k))-\delta_N(k)}.
]

[
E_N^#(r_1r_2,k)
===============

L(E_N^#(r_1,\alpha(Nr_2,k)))
\cup
R(E_N^#(r_2,k)).
]

[
E_N^#(\sum_i r_i,k)
===================

\bigcup_i A_i(E_N^#(r_i,k))
\cup
D_{\mathrm{alt}}(rs,k).
]

[
E_N^#(r^\star,k)
================

D_{\star}(r,k)
\cup
S(E_N^#(r,\alpha(N(r^\star),k))).
]

其中 (D_{\mathrm{alt}}) 和 (D_\star) 是 debt sets，必须小。

初始可以尝试：

[
D_{\mathrm{alt}}(rs,k)=\varnothing
]

因为内部 normalized (A_N) 的 RALTS 应该 clean。

但 old-to-new injection 可能需要 alt-opening debt。若需要，定义：

[
D_{\mathrm{alt}}(rs,k)
======================

{(\mathrm{OpenAlt}(i),x)
\mid
x\in \delta_N(\alpha(N(r_i),k))-\delta_N(k)
}.
]

这仍然按 branch 线性。

## 必证 count

```isabelle
card_nacc_excess_sharp_le:
  assumes "apder_clean r" "nstrong k = k"
  shows "card (nacc_excess_sharp r k) <= C * rsize r + D"
```

目标常数 (C) 不重要。先拿 (C=4,D=4)。不要为了 (C=1) 卡住。

## 必证 injection

```isabelle
lemma old_acc_diff_inj_sharp:
  assumes "apder_nf r" "apder_nf k"
  shows "∃f. inj_on f (strong_apder_acc r k - strong_apder_acc RONE k)
          ∧ f ` (strong_apder_acc r k - strong_apder_acc RONE k)
             ⊆ nacc_excess_sharp r (nstrong k)"
```

如果直接函数难定义，先证明更弱 card lemma：

```isabelle
card (strong_apder_acc r k - strong_apder_acc RONE k)
<= card (nacc_excess_sharp r (nstrong k))
```

但最终最好给 injection，因为 card proof更难调试。

## Adversarial 检查

必须专门打以下族：

[
q_i=b_i^\star a^\star,
\qquad
r_n=(q_1+\cdots+q_n)\cdot a^\star.
]

旧 row 有：

[
R_i=b_i^\star a^\star,
\quad
P_i=b_i^\star(a^\star a^\star).
]

它们都 normalize 到 (R_i)。必须保证：

[
R_i\mapsto(\pi_1,R_i),
\quad
P_i\mapsto(\pi_2,R_i),
\quad
\pi_1\neq\pi_2.
]

同时 tag 数是 (O(n))，不是 (O(n^2))。

还要打 deep-tail：

[
b^\star(a^\star(a^\star(\cdots a^\star))).
]

fiber multiplicity 可以随深度增长，但必须 charge 到 tail depth，因此总数线性。

## Acceptance

1. `card_nacc_excess_sharp_le` green；
2. old SAA diff 注入或 card inequality green；
3. Python 对 named CEs 和 adversarial families 0 collision；
4. tag set 不使用全局 product。

---

# 11. Wave 6：集成回旧 Gate

## Worktree

```text
../wt-norm-06-integrate
```

## Theory

```text
cubic/Normalized/NormalizedGateBridge.thy
```

## 目标 theorem

先证明 looser 线性版：

```isabelle
lemma card_apder_strong_dlfrontier_linear_norm:
  assumes "apder_clean r"
  shows "card (apder_strong_dlfrontier r) <= C * rsize r + D"
```

证明链：

1. 旧 green bridge：

```isabelle
apder_strong_dlfrontier r
⊆ strong_apder_acc r RONE
```

已有。

2. provenance injection/card：

[
|\mathrm{strong_apder_acc}(r,1)-\mathrm{strong_apder_acc}(1,1)|
\le
|A_N^#(r,1)|.
]

3. base singleton lift：

旧库已有 `card_le_Suc_card_Diff_singleton`。

4. 得到：

[
|U_{\mathrm{old}}(r)|\le C|r|+D.
]

5. 修改 downstream budget lemma，把 `Suc(rsize r)` 替换成 (C|r|+D)，因为任意线性 bound 仍关 Gate。

## Acceptance

1. 新 linear theorem green；
2. 新 Gate corollary green；
3. 没有改 opaque `afactored1` / `rpder_strong_rows_raw`；
4. 没有触碰 lexer actual internals。

---

# 12. Backup route：替换 actual interface

## Worktree

```text
../wt-norm-07-actual-rewrite-backup
```

只有当 provenance route 被明确小反例杀死时才启动。

## 思路

定义 normalized actual rows：

[
\mathrm{actual}_N
]

直接用 (N,\alpha,\delta_N)，然后证明它与旧 actual row semantics 等价。

优点：内部干净。

缺点：需要重做 row-level assembly，可能碰 opaque `afactored1` / `rpder_strong_rows_raw`，工程量大。当前文件说明这些 opaque 函数只应作为 final Gate black-box 处理，因此这条是 backup，不是主线。

---

# 13. 推荐 agent prompts

下面这些可以直接分配。

---

## Agent 00：Baseline / adversarial harness

**Role**：建立共同基线，不证明 Isabelle。

**Task**：

1. 阅读 `CARD_FRONTIER.md` 和 `DEFINITIONS.txt`。
2. 在 `experiments/norm/norm_model.py` 中实现旧 definitions。
3. encode named CEs 和 adversarial families。
4. 输出 `docs/norm-route/01-adversarial.md`，列出不允许再证明的 false statements。

**Must include**：

* old RALTS two-branch failure；
* old exact containment into (U_N) failure；
* deep-tail family；
* awidth refutation；
* reachable-wrapper family。

**Deliverable**：

```text
norm_model.py
adversarial_families.py
01-adversarial.md
```

**Fail-stop**：如果 faithful model 不能 reproduce known CEs，停止并报告 mismatch。

---

## Agent 01：Normalized append / normalizer

**Role**：定义 (\alpha,N)。

**Task**：

1. Implement `seq_factors`, `mk_seq`, `norm_seq`, `nplug`.
2. Implement `nstrong`.
3. Replace old ALTS prune replug by `nplug`.
4. Prove list-level append lemmas first.
5. Prove `nstrong_rsimp4_shadow`.

**Do not**：

* 不要直接递归定义 `nplug (RSEQ r1 r2) k = ...`；
* 不要用旧 `rsimpStrong_raw` 当 (N)；
* 不要把 conjecture 留在 `.thy` 里。

**Deliverable**：

```text
NormalizedAppend.thy
NormalizedStrong.thy
01-alpha-adversarial.md
```

**Acceptance**：

`nplug_assoc` 或 sufficient weaker lemma green；`nstrong_rsimp4_shadow` green。

---

## Agent 02：Normalized opening / accumulator

**Role**：定义 (\delta_N,A_N)。

**Task**：

1. Implement `ndlforms`.
2. Prove `old_opening_shadow`.
3. Implement `nterm_acc`, `nacc`, `nbase`.
4. Prove constructor subset recurrences.

**Do not**：

* 不要试图证明 old rows subset new rows；
* theorem 必须是 shadow：

[
x\in old \Rightarrow N(x)\in new.
]

**Deliverable**：

```text
NormalizedOpening.thy
NormalizedAccumulator.thy
02-opening-adversarial.md
```

**Acceptance**：

`old_opening_shadow` 和 `nacc_*_subset` green。

---

## Agent 03：Internal count

**Role**：证明 normalized carrier 自身线性。

**Task**：

1. Prove:

[
|A_N(r,k)-B_N(k)|\le C|r|+D.
]

2. Start with (C=4,D=4)，不要追求 tight。
3. Use constructor induction and telescope.

**Do not**：

* 不要用 per-row sum；
* 不要依赖 old `strong_apder_acc`；
* 不要处理 old actual rows。

**Deliverable**：

```text
NormalizedCount.thy
03-count-adversarial.md
```

**Acceptance**：

线性 count green；constants explicit。

---

## Agent 04：Shadow bridge

**Role**：证明旧 SAA rows normalize into new accumulator。

**Task**：

Prove:

[
x\in strong_apder_acc(r,k)
\Rightarrow
N(x)\in A_N(r,N(k)).
]

Split into:

1. `row_dlforms` shadow；
2. `rsimpStrong_raw` shadow；
3. `apder_term_frontier_acc` shadow；
4. carrier union shadow。

**Do not**：

* 不要证明 exact containment；
* 不要引入 provenance yet。

**Deliverable**：

```text
NormalizedShadow.thy
04-shadow-adversarial.md
```

**Acceptance**：

`old_acc_shadow` green。

---

## Agent 05：Provenance injection

**Role**：主战场。给旧 rows 一个 injective normalized key。

**Task**：

1. Define finite recursive `nacc_excess_sharp`.
2. Define injection or prove card inequality:

[
strong_apder_acc(r,k)-strong_apder_acc(1,k)
\hookrightarrow
A_N^#(r,N(k)).
]

3. Prove:

[
|A_N^#(r,k)|\le C|r|+D.
]

**Do not**：

* 不要用 (A_N(r,k)\times\Pi(r))；
* 不要把旧 row 本身放进 tag；
* 不要让 tag count 变 quadratic。

**Deliverable**：

```text
NormalizedProvenance.thy
05-prov-adversarial.md
```

**Acceptance**：

named families 0 collision；linear bound green；injection/card bridge green。

---

## Agent 06：Integration

**Role**：把线性 bound 接回旧 Gate。

**Task**：

1. Use existing green bridge:

[
apder_strong_dlfrontier(r)\subseteq strong_apder_acc(r,1).
]

2. Use provenance card bound.
3. Prove loose linear count for old `apder_strong_dlfrontier`.
4. Loosen downstream budget from `Suc(rsize r)` to (C|r|+D).
5. Reprove cubic Gate corollary.

**Deliverable**：

```text
NormalizedGateBridge.thy
06-integrate.md
```

**Acceptance**：

new unconditional Gate theorem green.

---

# 14. Kill criteria

立刻停止并报告，不要硬 formalize：

1. `nstrong_rsimp4_shadow` 被 clean 小例子杀死；
2. `old_opening_shadow` 被 clean 小例子杀死；
3. `nacc_RSEQ_subset` 需要非自然 side condition；
4. `nacc_RALTS_subset` 又需要 global `+1`；
5. `nacc_excess_sharp` 只能通过 product (A_N\times\Pi) 计数；
6. adversarial family (q_i=b_i^\star a^\star) 让 tag 数变 (Ω(n^2))；
7. deep-tail family 让 tag 数超过 syntax depth 的线性 charge；
8. 需要打开 `afactored1` / `rpder_strong_rows_raw` 内部才能走主线。

如果触发 8，切换 backup route，不要在主线里碰 actual internals。

---

# 15. 最短执行顺序

建议实际执行顺序：

```text
00 baseline
  ↓
01 alpha/N
  ↓
02 opening/accumulator
  ↓
03 internal count
  ↓
04 shadow
  ↓
05 provenance
  ↓
06 integration
```

其中 00 和 01 可以并行；03 和 04 可以在 02 后并行；05 必须等 03/04。

---

# 16. 最重要的成功判据

如果这条路线是对的，最终会出现两个核心 green lemma：

```isabelle
lemma old_acc_diff_card_le_sharp:
  assumes "apder_clean r" "apder_nf k"
  shows
    "card (strong_apder_acc r k - strong_apder_acc RONE k)
       <= C * rsize r + D"

lemma card_apder_strong_dlfrontier_linear_norm:
  assumes "apder_clean r"
  shows
    "card (apder_strong_dlfrontier r)
       <= C * rsize r + D"
```

第一条是实质证明；第二条只是接旧 green bridge。然后 cubic Gate 按现有路径关闭。现有文档也明确说只要线性 card bound，Gate 就能关。
