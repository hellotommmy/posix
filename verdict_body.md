最简、最可能成功的路线：**做一个“锚定右尾、size‑1 基准”的仿射 trace 证书**。不要再把 `HEAD` 和 `BODY` 分配到固定互补预算里，也不要证明 `pot ... k ≤ pot ... RONE + slope*(|k|-1)`；后者会被“同 size 的 `RONE` 和 `RCHAR` 成本不同”卡死。目标应直接证明：

```isabelle
pot (RSTAR r) k ≤ M^3 + 3*M^2*rsize k
```

其中 `M = rsize (RSTAR r)`。这正是现有绿色链条唯一缺的 `env`；一旦有它，`M^3 + 3*M^2*n ≤ (M+n)^3 - n^3` 和整个 cube-shell/root/gate bridge 都已经是 GREEN。

## 核心想法

把 `pot (RSTAR r) k` 展开成 trace，但不要把外部尾巴 `k` 实例化为 `RONE`。改为引入一个**符号右孔 `□`**，并给 `□` 两个解释：

```text
size1 cost : 把 □ 当作任意 size=1 的尾巴上界
tail slope : □ 每增加 1 个 size 单位时最多多付多少
```

于是证明：

```isabelle
pot (RSTAR r) k
  ≤ A1(r) + B(r) * (rsize k - 1)

A1(r) ≤ M^3 + 3*M^2
B(r)  ≤ 3*M^2
```

因为 `1 ≤ rsize k`，立刻得到：

```isabelle
A1(r) + B(r) * (rsize k - 1)
≤ M^3 + 3*M^2 + 3*M^2*(rsize k - 1)
= M^3 + 3*M^2*rsize k
```

这同时覆盖 `M=2,3,4`，不需要小规模特判，也不使用任何失败的 additive complement。这个设计也正好处理 prompt 里指出的障碍：`pot (RSTAR r) k` 依赖 `k` 的结构，不只依赖 size，所以不能拿实际 `pot ... RONE` 当斜率锚点。

## 需要新增的 Isabelle 对象

先保留已有 `pot_trace`，但给 RSTAR 专门加一个“锚定右尾 trace”。右尾始终是：

```isabelle
σ (RSTAR r) k
```

递归展开 body 时，任何 continuation 都是：

```isabelle
prefix1 · prefix2 · ... · prefixm · (RSTAR r) · k
```

即 `k` 永远在最右端，且在唯一的根锚 `RSTAR r` 后面。不要证明过强的

```isabelle
S (σ (RSTAR r) k) = S k
```

只证明“右孔只在线性位置出现”。

建议定义：

```isabelle
abbreviation pot where
  "pot ≡ strong_opened_live_acc_potential"

abbreviation σ where
  "σ ≡ rsimp4_SEQ_atom"

abbreviation S where
  "S ≡ rsimpStrong_raw"

abbreviation opn where
  "opn x ≡ rsize_set (row_dlforms (S x))"
```

锚定 context：

```isabelle
fun aplug :: "rrexp ⇒ rrexp list ⇒ rrexp ⇒ rrexp" where
  "aplug a [] k = σ (RSTAR a) k"
| "aplug a (x # xs) k = σ x (aplug a xs k)"
```

锚定事件：

```isabelle
datatype aevt =
    AU
  | AO "rrexp list"   (* open of aplug r xs k *)
  | AF "rrexp list"   (* frontier event of aplug r xs k *)
```

事件成本：

```isabelle
fun aevt_cost :: "rrexp ⇒ rrexp ⇒ aevt ⇒ nat" where
  "aevt_cost r k AU = 1"
| "aevt_cost r k (AO xs) =
     rsize_set (row_dlforms (S (aplug r xs k)))"
| "aevt_cost r k (AF xs) =
     rsize_set (row_dlformss_set (S ` rfrontier (aplug r xs k)))"
```

body trace：

```isabelle
fun atrace :: "rrexp ⇒ rrexp list ⇒ aevt list" where
  "atrace RZERO xs = [AU]"
| "atrace RONE xs = [AU, AO xs, AF xs]"
| "atrace (RCHAR c) xs = [AO (RCHAR c # xs), AU, AO xs, AF xs]"
| "atrace (RALTS rs) xs =
     AU # AO (RALTS rs # xs) # concat (map (λq. atrace q xs) rs)"
| "atrace (RSEQ p q) xs =
     atrace p (q # xs) @ atrace q xs"
| "atrace (RSTAR q) xs =
     AO (RSTAR q # xs) # atrace q (RSTAR q # xs)"
```

根 RSTAR 事件列表：

```isabelle
definition rstar_atrace :: "rrexp ⇒ aevt list" where
  "rstar_atrace r = AO [] # atrace r []"
```

对应 soundness：

```isabelle
lemma rstar_atrace_sound:
  assumes free: "rntimes_free (RSTAR r)"
      and leg:  "legacy_rrexp (RSTAR r)"
  shows
    "pot (RSTAR r) k =
       sum_list (map (aevt_cost r k) (rstar_atrace r))"
```

这个 lemma 只是现有 `pot_trace_sound` 的专门化/重排；现有 trace substrate 已经 GREEN，并且正是为“直接 bound potential，而不是 deduped set”准备的。

## 三个真正要证明的 lemma

### 1. 右尾仿射 opening lemma

定义两个 hole-aware 成本函数：

```isabelle
aevt_A1 :: "rrexp ⇒ aevt ⇒ nat"
aevt_B  :: "rrexp ⇒ aevt ⇒ nat"
```

含义：

```text
aevt_A1 r e = 事件 e 在右孔 □ 被当成 size=1 原子时的符号 ledger 上界
aevt_B  r e = 事件 e 的 opened/frontier ledger 中右孔 □ 的总出现权重
```

然后证明：

```isabelle
lemma aevt_tail_affine_size1:
  assumes nf: "apder_nf (RSTAR r)"
      and clean: "apder_clean (RSTAR r)"
  shows
    "aevt_cost r k e
       ≤ aevt_A1 r e + aevt_B r e * (rsize k - 1)"
```

这里的 `aevt_A1` **不是** `aevt_cost r RONE e`。它是“所有 size=1 尾巴”的统一符号上界，所以不会被 `RONE` vs `RCHAR c` 的同 size 差异击穿。实现上最稳的是加一个 hole-aware `hrrexp`，让 `□` 有两个度量：

```isabelle
hsize1 □ = 1
hmult  □ = 1
```

并为 `row_dlforms`、`rfrontier`、`rsimpStrong_raw` 写对应的 hole-aware 上界版本。真实 `k` 实例化后用：

```isabelle
rsize (hinst H k) ≤ hsize1 H + hmult H * (rsize k - 1)
```

向 opened ledger 和 frontier ledger 提升。

### 2. size‑1 intercept bridge

```isabelle
lemma rstar_atrace_A1_bound:
  assumes nf: "apder_nf (RSTAR r)"
      and clean: "apder_clean (RSTAR r)"
      and free: "rntimes_free (RSTAR r)"
      and leg: "legacy_rrexp (RSTAR r)"
  defines "M ≡ rsize (RSTAR r)"
  shows
    "sum_list (map (aevt_A1 r) (rstar_atrace r))
       ≤ M^3 + 3 * M^2"
```

这是“cubic intercept”，但它要 charge **trace 本身**，不能走：

```isabelle
rsize_set universe ≤ pot
```

的反方向。现有文件明确指出 `pot` over-approximates set，`rsize_set ... ≤ pot` 是 wrong direction；因此必须把 `pot_trace` 里的事件直接 charge 到 static star universe / tagged static rows。

可实现的 charge 结构：

```isabelle
datatype charge =
    CUnit nat
  | COpen path rrexp
  | CFront path rrexp
```

证明：

```isabelle
lemma rstar_A1_trace_charge:
  "sum_list (map (aevt_A1 r) (rstar_atrace r))
     ≤ sum_list (map charge_cost1 (rstar_charges r))"
```

再证明 `rstar_charges r` 是 STAR 的静态导数宇宙的 tagged 展开；每个非 unit charge 的底层 row 进入 `apder_rows (RSTAR r)` 或对应 opened frontier carrier。这里用已有的线性 row-count、quadratic member-size、quadratic opening ingredients：`strong_opened_live_row_universe_acc_RSTAR_subset`、`card_apder_rows_clean_le_rsize_plus_2`、`apder_rows_member_size_quadratic`、`rsize_set_row_dlforms_rsimpStrong_raw_quadratic`。

关键点：charge 是 **tagged/list**，不是 deduped set。这样证明的是：

```isabelle
sum event costs ≤ sum tagged charge costs
```

而不是把 set bound 倒过来用。

### 3. slope 二次界

```isabelle
lemma rstar_atrace_B_bound:
  assumes nf: "apder_nf (RSTAR r)"
      and clean: "apder_clean (RSTAR r)"
      and free: "rntimes_free (RSTAR r)"
      and leg: "legacy_rrexp (RSTAR r)"
  defines "M ≡ rsize (RSTAR r)"
  shows
    "sum_list (map (aevt_B r) (rstar_atrace r))
       ≤ 3 * M^2"
```

这是唯一真正的 slope lemma。证明不要用 slot ledger、weak carrier、row-to-slot injection。那些路线已经被 counterexample 排除；文档里明确说 per-row/per-slot membership 类证明都死了，必须做 total-budget argument。

`slope` 的归纳不需要知道 `k` 的结构，只数右孔 `□` 在 opened/frontier 事件中的出现权重。RSTAR 分支的关键 invariant 是：

```text
body trace 中不会产生第二个“同一个根锚 RSTAR r”；
所有新 prefix 都在根锚左侧，外部 k 仍在最右端。
```

因此没有 `k × k`，只有 `B(r) * rsize k`。这正是 sketch 里验证过的 affine 机制：`pot(RSTAR r,k)` 对 `rsize k` 呈线性 envelope，且总 slope ≤ `3*M^2`。

## 最终 assembly

```isabelle
lemma strong_opened_live_acc_potential_RSTAR_affine_envelope:
  assumes nf: "apder_nf (RSTAR r)"
      and clean: "apder_clean (RSTAR r)"
      and free: "rntimes_free (RSTAR r)"
      and leg: "legacy_rrexp (RSTAR r)"
  shows
    "strong_opened_live_acc_potential (RSTAR r) k
       ≤ (rsize (RSTAR r))^3
         + 3 * (rsize (RSTAR r))^2 * rsize k"
proof -
  let ?M = "rsize (RSTAR r)"
  let ?n = "rsize k"

  have npos: "1 ≤ ?n"
    by (cases k) simp_all

  have sound:
    "pot (RSTAR r) k =
       sum_list (map (aevt_cost r k) (rstar_atrace r))"
    using rstar_atrace_sound[OF free leg] .

  have aff:
    "sum_list (map (aevt_cost r k) (rstar_atrace r))
       ≤ sum_list (map (aevt_A1 r) (rstar_atrace r))
         + sum_list (map (aevt_B r) (rstar_atrace r)) * (?n - 1)"
    using aevt_tail_affine_size1[OF nf clean]
    by (simp add: sum_list_addf sum_list_mult_const)

  have A1:
    "sum_list (map (aevt_A1 r) (rstar_atrace r))
       ≤ ?M^3 + 3 * ?M^2"
    using rstar_atrace_A1_bound[OF nf clean free leg] by simp

  have B:
    "sum_list (map (aevt_B r) (rstar_atrace r))
       ≤ 3 * ?M^2"
    using rstar_atrace_B_bound[OF nf clean free leg] by simp

  have
    "pot (RSTAR r) k
       ≤ (?M^3 + 3 * ?M^2) + (3 * ?M^2) * (?n - 1)"
    using sound aff A1 B by nlinarith
  also have "... = ?M^3 + 3 * ?M^2 * ?n"
    using npos by nlinarith
  finally show ?thesis
    by simp
qed
```

如果当前工程里 `apder_clean (RSTAR r)` 已经蕴含 `rntimes_free` / `legacy_rrexp`，就把 `free`、`leg` 从 theorem statement 里删掉，只保留在内部通过已有 simp/intro 取出。不要加 `apder_nf k`；目标需要对所有 `k` 统一成立。

## HEAD 怎么放进去

`HEAD` 不需要独立分配 complement。它只是 `rstar_atrace r` 的第一个事件 `AO []`。作为 sanity lemma 可以导出：

```isabelle
lemma RSTAR_HEAD_linear:
  assumes nf: "apder_nf (RSTAR r)"
      and clean: "apder_clean (RSTAR r)"
  defines "M ≡ rsize (RSTAR r)"
  shows
    "opn (σ (RSTAR r) k) ≤ 2*M + 2*M*rsize k"
```

但最终证明不靠：

```isabelle
BODY ≤ envelope - HEAD_budget
```

因为小 `M` 下这种 additive split 已知不安全。prompt 明确给出 `M=2` 的 false complements，并要求不要走这条路。

## 实施顺序

先做这 5 个最小补丁：

```isabelle
aplug
aevt / aevt_cost / atrace / rstar_atrace
rstar_atrace_sound
aevt_tail_affine_size1
rstar_atrace_A1_bound
rstar_atrace_B_bound
strong_opened_live_acc_potential_RSTAR_affine_envelope
```

完成后直接复用已有：

```isabelle
strong_opened_live_acc_potential_RSTAR_cube_shell
strong_opened_live_acc_potential_cube_shell
strong_opened_live_acc_potential_root_cubic
actual_gate_bridge_from_strong_opened_live_potential
```

这些桥已经是 GREEN；附件里的 reduction 明确显示 gate 现在只差 RSTAR 这个 affine envelope。
