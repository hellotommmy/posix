我读了新的 follow-up。结论更新如下：**SAA 路线可以继续走，但不能用全局 `+1`；要把 RALTS 的“根行额外残差”显式记账，并把它按 branch export credit 付掉。** follow-up 已确认旧 `+1` 反例正确，并要求给出递归 debt、全局线性累计检查和 Python evidence。

我给出的设计是：把 RALTS 步改成

[
|A(\Sigma rs,k)-A(1,k)|
\le
\sum_{q\in set(rs)} |A(q,k)-A(1,k)| + d(rs,k),
]

其中 (d) 不是常数，而是 **parent RALTS root rows 相对 child root rows 的额外部分**。然后证明这个 (d) 可以由每个 branch 自己的 export credit (\beta(q,k)) 支付，且

[
M(q,k)+\beta(q,k)\le |q|
]

对 clean nonalt branch 成立。这样 RALTS 节点处

[
M(\Sigma rs,k)
==============

\sum_q M(q,k)+d(rs,k)
\le
\sum_q(M(q,k)+\beta(q,k))
\le
\sum_q |q|
\le
|\Sigma rs|.
]

所以累计 debt **线性闭合**，Python 检查得到最强形式：

[
|A(r,1)-A(1,1)|\le M(r,1)\le |r|.
]

这给 (c=1,d=0)。再经绿色 bridge (U(r)\subseteq A(r,1)) 和 `card_le_Suc_card_Diff_singleton`，得到目标

[
|U(r)|\le |r|+1.
]

这里 (U)、`strong_apder_acc`、`rsimp4_SEQ_atom`、`rsimp7_SEQ_atom`、`row_dlforms`、`rsimpStrong_raw` 都按附件中的定义建模；`strong_apder_acc` 的 RSEQ/RSTAR/RCHAR clean subset 与 (U\subseteq A(r,1)) bridge 是现有 green facts。    

---

## 1. 短符号

用短符号写：

[
S r := \texttt{rsimpStrong_raw }r,\qquad
\sigma(r,k):=\texttt{rsimp4_SEQ_atom }r,k,
]

[
\tau(r,k):=\texttt{rsimp7_SEQ_atom }r,k,\qquad
\delta r:=\texttt{row_dlforms }r.
]

[
C(X):=\bigcup_{p\in X}\delta(S p).
]

[
A(r,k):=\texttt{strong_apder_acc }r,k
= C(\texttt{rfrontier}(\sigma(r,k))\cup TF(r,k)).
]

[
B(k):=A(1,k).
]

根行集合：

[
\rho(r,k):=C(\texttt{rfrontier}(\sigma(r,k))).
]

branch 在 parent RALTS root 中被打开时的行：

[
\pi(q,k):=\delta(\tau(Sq,Sk)).
]

这正是“把 branch 先 strong，再按 parent continuation 打开”的单 branch 近似。

---

## 2. 新 debt 定义

RALTS 根行额外 debt：

[
d(rs,k)
:=
\left|
\bigl(\rho(\Sigma rs,k)-B(k)\bigr)
----------------------------------

\bigcup_{q\in set(rs)}\bigl(\rho(q,k)-B(k)\bigr)
\right|.
]

branch export credit：

[
\beta(q,k)
:=
\left|
\bigl(\pi(q,k)-B(k)\bigr)
-------------------------

\bigl(\rho(q,k)-B(k)\bigr)
\right|.
]

含义很直接：

* (d(rs,k))：parent RALTS root 打开后，child root rows 没有覆盖到的行数。
* (\beta(q,k))：branch (q) 如果被放进一个 surrounding RALTS，在 parent root 里可能额外制造多少 child-root 不存在的行。

关键 inequality 是：

[
d(rs,k)\le \sum_{q\in set(rs)}\beta(q,k).
]

这个式子就是把 set-level prune / dedup 产生的残差，重新按 branch origin 付费。它不要求 parent residual row 是 child SAA 的成员；只要求它由某个 branch 的 export credit 预算覆盖。

---

## 3. 递归 bound (M)

定义：

```isabelle
fun M :: "rrexp => rrexp => nat" where
  "M RZERO k = 0"
| "M RONE k = 0"
| "M (RCHAR c) k = 1"
| "M (RSEQ r1 r2) k =
     M r1 (rsimp4_SEQ_atom r2 k) + M r2 k"
| "M (RSTAR r) k =
     card (rho (RSTAR r) k - strong_apder_acc RONE k)
     + M r (rsimp4_SEQ_atom (RSTAR r) k)"
| "M (RALTS rs) k =
     (SUM q in set rs. M q k) + ralts_tail_debt rs k"
```

其中：

```isabelle
definition rho :: "rrexp => rrexp => rrexp set" where
  "rho r k =
     rsimpStrong_dlform_closure (rfrontier (rsimp4_SEQ_atom r k))"

definition pi :: "rrexp => rrexp => rrexp set" where
  "pi q k =
     row_dlforms (rsimp7_SEQ_atom (rsimpStrong_raw q) (rsimpStrong_raw k))"

definition ralts_tail_debt :: "rrexp list => rrexp => nat" where
  "ralts_tail_debt rs k =
     card ((rho (RALTS rs) k - strong_apder_acc RONE k)
           - (UN q:set rs. rho q k - strong_apder_acc RONE k))"

definition branch_export :: "rrexp => rrexp => nat" where
  "branch_export q k =
     card ((pi q k - strong_apder_acc RONE k)
           - (rho q k - strong_apder_acc RONE k))"
```

如果更想完全避免 notation，可以把 `rho/pi` 展开成定义式。它们不是新语义，只是对现有 recursive functions 的短封装。

---

## 4. 要 formalize 的 lemma 组

### 4.1 corrected RALTS step

```isabelle
lemma strong_apder_acc_RALTS_diff_debt_le:
  assumes "apder_nf (RALTS rs)" and "apder_nf k"
  shows
    "card (strong_apder_acc (RALTS rs) k - strong_apder_acc RONE k)
     <=
     (SUM q in set rs.
        card (strong_apder_acc q k - strong_apder_acc RONE k))
     + ralts_tail_debt rs k"
```

证明思路：

[
A(\Sigma rs,k)
\subseteq
\rho(\Sigma rs,k)\cup \bigcup_{q\in set(rs)} A(q,k).
]

因为 `apder_term_frontier_acc (RALTS rs) k` 正好是 child term carriers 的 union，而唯一不在 child SAA 中自动出现的是 parent RALTS root carrier。于是差掉 (B(k)) 后，用

[
|X\cup Y|\le |Y|+|X-Y|
]

得到上式，其中 (X) 是 parent root rows，(Y) 是 child SAA union，最后用 child root rows (\rho(q,k)\subseteq A(q,k)) 得到 (d(rs,k))。

### 4.2 branch-origin debt bound

```isabelle
lemma ralts_tail_debt_le_sum_branch_export:
  assumes "apder_nf (RALTS rs)" and "apder_nf k"
  shows
    "ralts_tail_debt rs k
     <= (SUM q in set rs. branch_export q k)"
```

这条是 set-prune provenance lemma：`rsimpStrong_ALTs_raw` 的 prune scan 只删除 earlier row 已覆盖的 head branches，row 本身不凭空生成 branch；所以每个 residual opened row 都有某个 source branch (q)。附件里也明确指出 prune 是 left-to-right scan，删除 covered branches，rows shrink but are not dropped，这是此 lemma 的结构来源。

### 4.3 simultaneous size lemmas

```isabelle
lemma M_acc_le:
  assumes "apder_nf r" and "apder_nf k"
  shows
    "card (strong_apder_acc r k - strong_apder_acc RONE k) <= M r k"
```

构造归纳：

* RCHAR 用现有 green `card_strong_apder_acc_RCHAR_diff_base_le`。
* RSEQ 用 `strong_apder_acc_RSEQ_subset`、`strong_apder_acc_RONE_sigma_subset`、`card_Un_Diff_telescope_le`。
* RSTAR 用 `strong_apder_acc_RSTAR_subset` 加 root term。
* RALTS 用上面的 corrected debt step。相关 green machinery 已在附件中列出。

然后需要强一点的 size/export lemma：

```isabelle
lemma M_nonalt_export_le_rsize:
  assumes "apder_nf q" and "nonalt q" and "q ~= RZERO" and "apder_nf k"
  shows
    "M q k + branch_export q k <= rsize q"
```

以及主线性 bound：

```isabelle
lemma M_le_rsize:
  assumes "apder_clean r" and "apder_nf k"
  shows "M r k <= rsize r"
```

RALTS case 用 `apder_nf (RALTS rs)` 给出的 branch 条件：

```isabelle
forall q in set rs. apder_nf q /\ nonalt q /\ q ~= RZERO
```

这正是 `apder_nf` 对 RALTS 的定义。

于是：

[
\begin{aligned}
M(\Sigma rs,k)
&=\sum_q M(q,k)+d(rs,k)\
&\le \sum_q M(q,k)+\sum_q\beta(q,k)\
&=\sum_q(M(q,k)+\beta(q,k))\
&\le \sum_q |q|\
&\le 1+\sum_q |q|\
&=|\Sigma rs|.
\end{aligned}
]

最后：

```isabelle
lemma card_apder_strong_dlfrontier_le:
  assumes "apder_clean r"
  shows "card (apder_strong_dlfrontier r) <= Suc (rsize r)"
```

由：

```isabelle
apder_strong_dlfrontier r <= strong_apder_acc r RONE
strong_apder_acc RONE RONE = {RONE}
card A <= Suc (card (A - {x}))
card (strong_apder_acc r RONE - strong_apder_acc RONE RONE) <= M r RONE <= rsize r
```

得到。Gate 本身已经 green modulo 这个 linear row-count lemma；附件明确说任意 linear card bound 也足够闭合 Gate。

---

## 5. 反例上的逐步计算

令

[
q_b=b^*\cdot a^*,\qquad q_c=c^*\cdot a^*,\qquad k=a^*.
]

旧目标失败：

[
|A(q_b,k)-B(k)|=1,\qquad
|A(q_c,k)-B(k)|=1.
]

child rows 是：

[
A(q_b,k)-B(k)={b^*\cdot a^*},
]

[
A(q_c,k)-B(k)={c^*\cdot a^*}.
]

parent RALTS full rows 是：

[
A(q_b+q_c,k)-B(k)
=================

{
b^*\cdot a^*,
c^*\cdot a^*,
b^*\cdot(a^*\cdot a^*),
c^*\cdot(a^*\cdot a^*)
}.
]

所以：

[
LHS=4,\qquad RHS_{\text{old}}=1+1+1=3.
]

新 debt：

[
d([q_b,q_c],k)=
|{b^*\cdot(a^*\cdot a^*),c^*\cdot(a^*\cdot a^*)}|=2.
]

并且：

[
\beta(q_b,k)=1,\qquad \beta(q_c,k)=1.
]

所以：

[
4\le 1+1+2.
]

对于一般族

[
rs_n=[x_i^*\cdot a^*]_{i<n},\qquad k=a^*,
]

旧 bound 是：

[
2n\le n+1
]

对 (n\ge2) 失败。新 bound 是：

[
2n\le n+n,
]

精确成立。

---

## 6. Python validation

我重新跑了 faithful Python model，并把 validation 脚本保存了：

[model_saa_debt.py](sandbox:/mnt/data/model_saa_debt.py)

[saa_debt_validation.py](sandbox:/mnt/data/saa_debt_validation.py)

核心输出：

```text
false +1 CE: B(parent,k)= 4 child_sum+1= 3 D= 2 child_sum+D= 4
single-branch leak: B= 2 child_sum+1= 2 D= 1
collapsing-tail CE: size= 12 |U|= 4 has a*.a*= True has a.(a*.a*)= True
awidth CE: size= 7 |U|= 3 awidth+1= 2
unreachable k=b*.b*: B= 4 sum+D= 4 D<=sum_beta= True

n-branch flat/nested n<=50
  tops= 100 pairs= 13000 alts= 100 violations= 0
  max_F_ratio= 1.0 max_beta= 1

witness/stars
  tops= 15 pairs= 363 alts= 36 violations= 0
  max_F_ratio= 1.0 max_beta= 0

exhaustive canonical clean size<=8 alphabet={a,b,c}
  tops= 67082 pairs= 518871 alts= 93113 violations= 0
  max_F_ratio= 1.0 max_beta= 1

deterministic random sample size=9 alphabet={a,b,c}
  size9 total=263677 sample=5000
  pairs= 45000 alts= 8122 violations= 0
  max_F_ratio= 1.0 max_beta= 0
```

Checked predicates:

```python
# accumulator bound
B(r,k) <= F(r,k)

# closed linear bound
F(r,RONE) <= rsize(r)

# RALTS debt covered by branch export
D_alts(rs,k) <= sum(branch_extra(q,k) for q in set(rs))

# branch export has local size slack
F(q,k) + branch_extra(q,k) <= rsize(q)
```

其中 Python 名字对应：

```python
F              = M
D_alts         = ralts_tail_debt
branch_extra   = branch_export
B(r,k)         = card(A(r,k) - B(k))
```

我没有声称 full size-9 exhaustive；size-9 全 canonical set 有 263,677 个 top forms，脚本做了 deterministic random sample 5,000 个。size≤8 是 exhaustive canonical clean normal forms，alphabet `{a,b,c}`，duplicate-free sorted ALTS；另外覆盖了 n-branch flat/nested 到 n=50、witness/stars、旧 `+1` 反例、collapsing-tail CE、Tail2-style weird continuation、awidth CE。


没有停止；上一次只是把**原 prompt 的 `+1` RALTS step 是假命题**这件事先 fail-stop 了。你新传的 follow-up 已经把目标修正成“找一个可累计的线性 debt / 或者转 direct (U) lane”，我继续做了。当前结果如下。

## 当前最重要的新结论

原来的

[
D(A,rs,k)\le \sum_{q\in set(rs)}D(q,k)+1
]

是假的，这个已经确认。这里我记

[
D(r,k):=
\left|\operatorname{SAA}(r,k)-\operatorname{SAA}(1,k)\right|,
\qquad
A,rs := \operatorname{RALTS},rs .
]

follow-up 也明确说，两分支族

[
A[x_i^*\cdot a^*]_{i<n},\quad k=a^*
]

给出 parent (2n) vs child-sum+(1=n+1)，所以单个 `+1` 不可能成立。

继续测以后，我发现更强的一点：

[
D(A[q],k)\le D(q,k)+1
]

也是假命题。最小的新杀手之一是

[
q=(1+a^*)\cdot b^*,\qquad k=b^* .
]

逐步算：

[
D(q,k)=1,
]

但

[
D(A[q],k)=3.
]

具体 parent singleton rows 是

[
{,a^*\cdot b^*,; b^*\cdot b^*,; a^*\cdot(b^*\cdot b^*),}.
]

所以

[
3>D(q,k)+1=2.
]

这说明“每个 branch 一个 `+1` 加到 child realized count 上”也不够。问题不是只有跨 branch 共享 slack，而是 **child (D(q,k)) 本身可能因为 continuation 强化塌缩得太厉害，留下很多结构 slack 没被计入**。

## 可行修正：不用 child count，改用 branch size budget

现在看起来最干净的 SAA 修正不是

[
D(A,rs,k)\le \sum_q D(q,k)+\delta(rs,k),
]

而是直接换成一个可 telescoping 的 RALTS step：

[
\boxed{
D(A,rs,k)\le \sum_{q\in set(rs)} |q|
}
]

更 Isabelle-friendly 可以用 list 版本：

[
\boxed{
D(A,rs,k)\le \sum_{q\in rs}|q|
}
]

因为

[
|A,rs|=1+\sum_{q\in rs}|q|,
]

所以这一步甚至给 RALTS 留了 1 个 constructor slack。

这走的是 follow-up 里允许的路线 `(b)`：looser-but-telescoping per-step bound，而不是硬把每个 parent row 注入到 child (D(q,k)) 里。follow-up 要求的是 corrected RALTS step 或者仍然线性的 looser telescope。

## 关键设计

引入 singleton alternation：

[
\Lambda(q,k):=\operatorname{SAA}(A[q],k).
]

两个核心 lemma：

### Lemma 1：branch-origin cover

[
\boxed{
\operatorname{SAA}(A,rs,k)
\subseteq
\bigcup_{q\in set(rs)} \Lambda(q,k)
}
]

直觉：`rsimpStrong_ALTs_raw` 的 set-level prune 只会删除 later row 里的 head-alternation branches，不会凭空制造一个没有源 branch 的 row。`rflts` 只是 flatten/drop zero，`rdistinct` 只是去重，pairwise prune 只在相同 right factor 下删掉已覆盖 branches；这些定义都在 `DEFINITIONS.txt` 里。 

这个 lemma 避免了 false subset

[
\operatorname{SAA}(A,rs,k)
\subseteq
\bigcup_q \operatorname{SAA}(q,k).
]

正确 cover 的目标不是 child carrier，而是 singleton-alt carrier。

### Lemma 2：singleton-size bound

[
\boxed{
D(A[q],k)\le |q|
}
]

这一步正好吸收所有 `a*·a*` tail-doubling。比如

[
q=(1+a^*)\cdot b^*
]

时，singleton parent 有 3 个非 base rows，但 (|q|=7)，所以完全够用。这个 lemma 比

[
D(A[q],k)\le D(q,k)+1
]

弱得多，但它正是能 telescoping 的形式。

于是 RALTS step 变成：

[
\begin{aligned}
D(A,rs,k)
&\le
\left|
\left(\bigcup_{q\in set(rs)}\Lambda(q,k)\right)
-----------------------------------------------

\operatorname{SAA}(1,k)
\right| \
&\le
\sum_{q\in set(rs)}
\left|\Lambda(q,k)-\operatorname{SAA}(1,k)\right|\
&\le
\sum_{q\in set(rs)} |q|\
&\le
\sum_{q\in rs}|q|\
&< |A,rs|.
\end{aligned}
]

所以 RALTS closes without any `+1` miracle.

## 全局 induction 形式

目标可以直接设成：

[
\boxed{
D(r,k)\le |r|
}
]

对所有 clean / nf 相关 (r,k)。

构造子步骤：

[
D(c,k)\le 1=|c|
]

用现有 RCHAR diff base。

[
D(r_1\cdot r_2,k)
\le
D(r_1,\sigma_4(r_2,k))+D(r_2,k)
\le
|r_1|+|r_2|
<
|r_1\cdot r_2|.
]

这里用现有 `strong_apder_acc_RSEQ_subset`、`strong_apder_acc_RONE_sigma_subset`、`card_Un_Diff_telescope_le`。 

[
D(r^*,k)
\le
1+D(r,\sigma_4(r^*,k))
\le
1+|r|
=====

|r^*|.
]

这里用现有 RSTAR split，再配一个 root-row (\le 1) lemma。`DEFINITIONS.txt` 里 RSTAR subset 已经是 green machinery 的一部分。

[
D(A,rs,k)
\le
\sum_{q\in rs}|q|
<
1+\sum_{q\in rs}|q|
===================

|A,rs|.
]

这是新的 RALTS 修正。

最后由 bridge

[
U(r)\subseteq \operatorname{SAA}(r,1)
]

和

[
\operatorname{SAA}(1,1)={1}
]

得

[
|U(r)|\le 1+D(r,1)\le |r|+1.
]

这正好回到原 Gate 所需的线性 count lemma；而文档也说明任意线性 bound 都足以 close Gate，原目标是 (|U(r)|\le |r|+1)。 

## 建议加入的递归定义

这里只需要一个很小的 list budget；不要再定义复杂 `ralts_tail_debt rs k`。

```isabelle
fun ralts_size_budget :: "rrexp list => nat" where
  "ralts_size_budget [] = 0"
| "ralts_size_budget (q # qs) = rsize q + ralts_size_budget qs"
```

缩写：

```isabelle
definition D :: "rrexp => rrexp => nat" where
  "D r k = card (strong_apder_acc r k - strong_apder_acc RONE k)"

definition one_alt :: "rrexp => rrexp" where
  "one_alt q = RALTS [q]"
```

新增 lemma statements：

```isabelle
lemma strong_apder_acc_RALTS_singleton_cover:
  "strong_apder_acc (RALTS rs) k
   <= (UN q:set rs. strong_apder_acc (RALTS [q]) k)"
```

```isabelle
lemma card_strong_apder_acc_singleton_RALTS_diff_base_le_rsize:
  assumes "apder_nf q" "apder_nf k"
  shows
    "card (strong_apder_acc (RALTS [q]) k - strong_apder_acc RONE k)
     <= rsize q"
```

```isabelle
lemma card_strong_apder_acc_RALTS_diff_base_le_size_budget:
  assumes "list_all apder_nf rs" "apder_nf k"
  shows
    "card (strong_apder_acc (RALTS rs) k - strong_apder_acc RONE k)
     <= ralts_size_budget rs"
```

主 induction：

```isabelle
lemma card_strong_apder_acc_diff_base_le_rsize:
  assumes "apder_clean r" "apder_nf k"
  shows
    "card (strong_apder_acc r k - strong_apder_acc RONE k)
     <= rsize r"
```

最后：

```isabelle
lemma card_apder_strong_dlfrontier_le:
  assumes "apder_clean r"
  shows "card (apder_strong_dlfrontier r) <= Suc (rsize r)"
```

## Python validation 摘要

我保留了原模型 `model_short.py`，又写了一个新的 validation 脚本：

[下载 validation 脚本](sandbox:/mnt/data/saa_singleton_size_validate.py)

核心 predicates：

```python
def singleton_size_ok(q, k):
    return D(ALTS([q]), k) <= rsize(q)

def ralts_singleton_cover_ok(r, k):
    cover = set()
    for q in set(r.branches):
        cover |= SAA(ALTS([q]), k)
    return SAA(r, k) <= cover

def ralts_size_step_ok(r, k):
    return D(r, k) <= sum(rsize(q) for q in set(r.branches))

def global_saa_size_ok(r, k):
    return D(r, k) <= rsize(r)

def global_U_ok(r):
    return len(U(r)) <= rsize(r) + 1
```

已跑过的结果：

```text
NAMED
SAA leak one branch: size 7, D 2, U 3
SAA +1 false two branches: size 11, D 4, U 3
hard singleton: size 8, D 3, U 2
collapsing-tail: size 12, D 4, U 4
awidth: size 7, D 2, U 3

flat n=100: size 501, D@a* 200, sumsize 500
seq  n=100: size 504, D@1 201, U 201
```

Exhaustive / random checks:

```text
OK exhaustive abc N=6 K=3 max_alt=2
q=4334, r=3965, k=53

OK exhaustive ab N=7 K=3 max_alt=2
q=9143, r=7920, k=35

OK exhaustive ab N=6 K=4 max_alt=2
q=2062, r=1812, k=122

OK top_U abc N=8 max_alt=2
total=96580

OK top_U ab N=9 max_alt=2
total=161904

OK random M=10000
pool_q=107601, pool_r=96580, pool_k=204
```

## 当前状态判断

现在我不会再推荐 `sum child D + constant debt`。它已经被两个层次打穿：

[
+1
]

全局 singleton slack 是假的；

[
D(A[q],k)\le D(q,k)+1
]

per-branch slack 也是假。

应该改成：

[
\boxed{
D(A,rs,k)\le \sum_{q\in rs}|q|
}
]

也就是 branch-origin cover + singleton-size bound。这个形式 Python 上没有找到反例，而且直接 telescopes 到

[
D(r,k)\le |r|
]

再推出

[
|U(r)|\le |r|+1.
]

还没完成的是 Isabelle 层面的 `singleton-size bound` 证明。它现在是新的核心 proof obligation；但它比原来的注入到 child (D(q,k)) 明显更对，因为它允许 branch 内部的 unused syntax slack 支付那些 uncollapsed (s^*\cdot s^*) residual rows。
