# Stephan 第 69 条猜想（OEIS A060621）：余维 3 的 zonotope 铺砌翻转数

日期：2026-11-26。

## 1. 命题

OEIS [A060621](https://oeis.org/A060621)（Latapy，2001）：循环 zonotope Z(d+3, d) 的 d 维铺砌之间的翻转（flip）个数，

> 12, 36, 100, 264, 672, 1664, 4032, 9600, 22528, 52224（d = 0…9）。

Ralf Stephan 2004-04-08 在该词条写下“Numbers so far satisfy a(n) = 2^n·(n²+11n+24)/2”，并把它列为《Prove or disprove. 100 conjectures from the OEIS》（[arXiv:math/0409509](https://arxiv.org/abs/math/0409509)）的第 69 条。他 2005-10 的状态页上这一条是空白；OEIS 词条到今天仍只有这句观察和 Colin Barker 2013 年的“Empirical g.f.”。

**定理。** 对所有 d ≥ 0，

> a(d) = (d² + 11d + 24)·2^(d−1)，

等价地，记 n = d + 3，翻转数为 n(n+5)·2^(n−4)。

## 2. 组合模型

Ziegler（*Higher Bruhat orders and cyclic hyperplane arrangements*, Topology 32, 1993）证明：

- Z(n, k) 的铺砌与高阶 Bruhat 序 B(n, k) 的元素一一对应，翻转对应 B(n, k) 的覆盖关系；
- B(n, k) 同构于 C([n], k+1) 的“相容子集”按单步包含（每次添一个元素、保持相容）构成的偏序。子集 U 相容，是指对每个 (k+2)-子集 X，U 与 X 的 packet（X 的全部 (k+1)-子集，按字典序排列）之交是它的一个前段或后段。

（定义的措辞取自 [arXiv:2412.10532](https://arxiv.org/abs/2412.10532) 的 Definition 2.1、2.10，该文注明出自 Ziegler。Ziegler 原文的扫描版我没能读到文字，所以这里引用的是二手转述。）

取 k = n − 3。把每个 (n−2)-子集换成它的补集——一个 2-子集，即 [n] 上的一条边——U 就成了一个图 G。X = [n] ∖ {p} 的 packet 变成与 p 关联的全部边 {p, q}；X ∖ {q} 的字典序恰是 q 的逆序。于是：

> **相容图。** [n] 上的图 G 相容，当且仅当每个顶点 p 的邻域 N(p) 是 [n] ∖ {p}（按自然顺序）的一个前段或后段。
>
> **翻转。** 一对 (G, e)：e 不是 G 的边，G 与 G + e 都相容。

余维 3 的翻转数就是这种 (G, e) 的个数。用这个模型穷举（[zonotope/verify_flips.py](zonotope/verify_flips.py)，[日志](logs/zonotope_verify.log)）：相容图个数与 Ziegler 的公式 2^n + n·2^(n−2) − 2n 一致，翻转数与 OEIS 的 10 项全部一致，并延伸到 n = 14。

下面的证明只涉及这个模型。顶点集取任意有限集 S ⊂ ℕ（这样删去顶点后不必重新编号）。

## 3. 证明

固定 S 中的 i < j，记

- A = {q ∈ S : q < i}，B = {q ∈ S : i < q < j}，C = {q ∈ S : q > j}，大小分别为 α、β、γ。

“101 / 010 引理”：一行（某顶点 p 对其余顶点的邻接 0/1 序列）是前段或后段，当且仅当它没有子序列 1 0 1 和 0 1 0。下面反复用它。

### 3.1 翻转的四种类型

**引理 1。** 设 ij 不是 G 的边，G 相容。则 G + ij 相容，当且仅当

- N(i) = {q < j} ∖ {i}（记作 iD）或 N(i) = {q > j}（iU），并且
- N(j) = {q < i}（jD）或 N(j) = {q > i} ∖ {j}（jU）。

当 |S| ≥ 3 时，i 的两种情形互斥，j 的两种情形也互斥。

*证明。* 只有 i、j 两行在 j、i 两个位置上改变。i 的行在位置 j 处由 0 变 1，变化前后都单调。分四种情况（前/后 × 前/后）讨论即得：j 以下的位置取值全相同，j 以上的位置取值全相同，且两侧不能同为 1 或同为 0（除非一侧为空）。反向是直接验证。∎

所以在 (i, j) 处的翻转恰好分成 DD、DU、UD、UU 四类（按 i、j 两行的形状）。

**引理 2（补图）。** G ↦ “G + ij 在完全图中的补图”是 DD 类与 UU 类之间、DU 类与 UD 类之间的双射。

*证明。* 取补把前段换成后段，101 换成 010；i、j 两行按定义直接算出。该映射是对合。∎

于是 (i, j) 处的翻转数 = 2·|DD| + 2·|DU|。

### 3.2 克隆引理

**引理 3。** 设 H 是 S ∖ {w} 上的相容图，t 是 S 中与 w 相邻的顶点（两者之间没有 S 的其他元素）。把 w 加进来，使得对某个顶点 p ≠ t，“p 与 w 是否相邻”等于“p 与 t 是否相邻”，则 p 的行仍然单调。

*证明。* p 的行里只是在 t 的位置旁边插入了一个与之相等的值。∎

下面每一步删去的顶点 w，其邻域都被条件完全确定，并且除了 i、j 两行之外，w 正好是 i 或 j 的克隆；i、j、w 三行的形状是显式的。因此“删去 w”是到小一号的同类图族的双射：单射因为 N(w) 被确定，满射由克隆引理保证。只有两处（只剩 A、或只剩 C 的末端）w 不是克隆，而是新的最小 / 最大顶点，这时用“单调行的最高位为 1（或最低位为 0）则它是后段”直接验证。

### 3.3 DU 类：|DU| = C(α+β+γ, β)

DU 类：N(i) = {q < j} ∖ {i}，N(j) = {q > i} ∖ {j}。对 |S| 归纳。

- **A ≠ ∅。** 取 a = max A。
  - 若 a 与 B 的每个顶点相邻，则 N(a) = {q < j} ∖ {a}（a 是 i 的克隆）。删去 a，得到 (α−1, β, γ) 的 DU 类。
  - 否则（此时 B ≠ ∅）取 b = max B：a 与 b 不相邻，由此 b 在 A 中没有邻居、与 C 全相邻，N(b) = {q ≥ i} ∖ {b}（b 是 j 的克隆，i 行除外）。删去 b，得到 (α, β−1, γ)。
  
  两种情况互斥且穷尽，故 |DU(α,β,γ)| = |DU(α−1,β,γ)| + |DU(α,β−1,γ)|，即 Pascal 递推。
- **A = ∅，C ≠ ∅。** 镜像：c = min C 与 B 全相邻（删 c），或 b = min B 在 C 中无邻居、与 A 全相邻（删 b）。
- **A = C = ∅，B ≠ ∅。** b = max B 的邻域必为全体，删去。
- **S = {i, j}。** 只有空图。

每一步“邻域被确定”都是一两次 101 / 010 引理的应用，例如第一种情形：a 与 i 相邻、与 j 不相邻，故对 q < a，(q, i, j) 不能是 0 1 0，得 a ~ q；对 q > j，(i, j, q) 不能是 1 0 1，得 a ≁ q。

### 3.4 DD 类：|DD| = 2^((β−1)⁺ + (α+γ−1)⁺)

DD 类：N(i) = {q < j} ∖ {i}，N(j) = {q < i}。其中 x⁺ = max(x, 0)。

- **β ≥ 2。** b₁ = min B，b₂ = max B。若 b₁ ~ b₂，则 b₁ 与 B 的其余顶点全相邻，N(b₁) = {q < j} ∖ {b₁}（i 的克隆），删去；否则 b₂ 在 B 中无邻居，N(b₂) = {q ≤ i}（j 的克隆），删去。两边都落到 (α, β−1, γ)，故个数翻倍。
- **β = 1。** 唯一的 b 被确定，删去，个数不变。
- **β = 0，α, γ ≥ 1。** a = max A，c = min C。若 a ~ c，则 c 与 A 全相邻、在 C 中无邻居，N(c) = {q < i}（j 的克隆），删去 c；否则 a 与 A 的其余顶点全相邻、在 C 中无邻居，N(a) = {q ≤ j} ∖ {a}（i 的克隆，j 行除外），删去 a。得 |DD(α,0,γ)| = |DD(α,0,γ−1)| + |DD(α−1,0,γ)|，两项相等，故翻倍。
- **β = γ = 0，α ≥ 2。** a₁ = min A，a₂ = max A。若 a₁ ~ a₂，则 a₂ 与 A 全相邻，删 a₂；否则 a₁ 在 A 中无邻居（N(a₁) = {i, j}，它是新的最小顶点），删 a₁。翻倍。α = 1 时不变。
- **α = β = 0，γ ≥ 2。** c₁ = min C，c₂ = max C。若 c₁ ~ c₂，则 c₂ 与 C 全相邻（新的最大顶点），删 c₂；否则 c₁ 孤立（j 的克隆），删 c₁。翻倍。γ = 1 时不变。

### 3.5 求和

取 S = {0, …, n−1}，n ≥ 3，则 α = i，β = j − i − 1，γ = n − 1 − j，α + β + γ = n − 2。

- Σ_{i<j} C(n−2, j−i−1) = Σ_β (n−1−β)·C(n−2, β) = n·2^(n−3)。
- Σ_{i<j} 2^((β−1)⁺ + (n−3−β)⁺)：β = 0 的 n−1 对和 (i, j) = (0, n−1) 这一对各贡献 2^(n−3)，其余每对贡献 2^(n−4)，合计 n(n+1)·2^(n−5)。

翻转数 = 2·n(n+1)·2^(n−5) + 2·n·2^(n−3) = n(n+5)·2^(n−4)。∎

## 4. Lean 4 形式化

Lean 4.19.0 + Mathlib v4.19.0，共 8 个模块、约 2300 行，无 `sorry`、无 `native_decide`，主定理只依赖 `propext`、`Classical.choice`、`Quot.sound`（[logs/zonotope_axioms.log](logs/zonotope_axioms.log)）。

| 文中 | Lean |
|---|---|
| 相容图 | `ZonoFlips.Consistent`（[Basic.lean](ZonotopeFlips/Basic.lean)） |
| 全体翻转 | `ZonoFlips.flipPairs`（[Total.lean](ZonotopeFlips/Total.lean)） |
| 删点双射的通用形式 | `card_del_eq`、`cls_del_card`（[Classes.lean](ZonotopeFlips/Classes.lean)） |
| 克隆引理 | `monoP_clone`、`cons_ins_clone_i`、`cons_ins_clone_j` |
| 3.3 | `card_DU`（[DU.lean](ZonotopeFlips/DU.lean)、[DUCount.lean](ZonotopeFlips/DUCount.lean)） |
| 3.4 | `card_DD`（[DD.lean](ZonotopeFlips/DD.lean)、[DDCount.lean](ZonotopeFlips/DDCount.lean)） |
| 引理 1、2 | `rows_of_flip`、`flip_of_cls`、`card_flipSet`、`card_UU`、`card_UD`（[Flips.lean](ZonotopeFlips/Flips.lean)） |
| 定理 | `card_flipPairs_eq : 2 * (flipPairs (d + 3)).card = (d ^ 2 + 11 * d + 24) * 2 ^ d` |
| 同上，按顶点数 | `flipCount_eq : 4 ≤ n → flipCount n = n * (n + 5) * 2 ^ (n - 4)` |
| OEIS 的 10 项 | `flipCount_values` |

[tests/ExamplesZono.lean](tests/ExamplesZono.lean) 用 `decide` 直接从定义核对了几个具体例子（例如路径 0–1–2–3 相容，单边 0–2 在 4 个顶点上不相容，3 个顶点上所有图都相容）。

## 5. 证明了什么，没证明什么

- **已形式化：** 第 2 节的图模型里，翻转数对所有 n ≥ 3 等于 n(n+5)·2^(n−4)。
- **未形式化、引用文献：** “zonotope 铺砌及其翻转 ↔ 高阶 Bruhat 序及其覆盖关系 ↔ 相容子集的单步包含”（Ziegler 1993），以及从 (n−2)-子集到图的补集转写。后者是直接的改写；整条链由穷举结果与 OEIS 的 10 项吻合作旁证。
- **新颖性：** 我查了 OEIS 词条、Latapy 的原文、[arXiv:2412.10532](https://arxiv.org/abs/2412.10532)（2024，重新证明了 |B(n, n−3)| 的公式）以及若干检索，没有找到这个边数公式的证明。检索是有限的；Ziegler 原文我只能读到扫描件，无法排除其中或别处已有等价结论。未经同行评审。
- **分量：** 这是一条 22 年没人写下证明的计数猜想，证明是初等的，不是重要的开放问题。
