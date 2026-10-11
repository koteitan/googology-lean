[← Back](README-ja.md) | [English](LEAN.md) | [Japanese](LEAN-ja.md)

# Lean での $`R_2^+`$：$`R_2^C`$、核、FRAG、$`V_\omega(1)`$ より下のやり直しのブロック

このページは、40 回目（[SHIFT10-ja.md](SHIFT10-ja.md) §3.3、段階 1）、41 回目（[SHIFT11-ja.md](SHIFT11-ja.md) §1.3、段階 2）、42 回目（[SHIFT11-ja.md](SHIFT11-ja.md) §2.3、段階 3）、43 回目（[SHIFT11-ja.md](SHIFT11-ja.md) §3.3、段階 4）で足したディレクトリ [R2/](R2/)（名前空間
`Googology.Trans.PoR.InaccPsi.R2`）の Lean のファイルを説明する。どのファイルもライブラリ全体とともにモジュールとして作られる（`lake build`、緑、`sorry` 無し）。どちらの段階の監査も、
どの公理も引いた論文に忠実で、どの定義も正しく、どの主な定理も Lean が証明していると認め、致命的な点も進行を止める点も見つけなかった。

**これで何が変わるか。** ほかのページの $`\upsilon_{\omega\cdot\omega}`$ より上のほとんどの結果は「FRAG のもと」で述べている。FRAG は今は Lean の定理で、標準でない公理は Wilken の 2 本の論文
から引いた 20 個の事実（とその論文の対象のための 7 個の定数）だけ。だから「FRAG のもと」は「この 20 個の引いた事実のもと」と読める。段階 2 は INC1、核についての Carlson の定理、定理 CP を足す。段階 3 は補題 L と、$`\upsilon_{\omega^3}`$ より下の $`R_2^C`$ の構造（最初の組、
定理 B と TOP つきの B″、RS、SK3）を足す。段階 4 は順序数のやり直しの添字の上のやり直しのブロックを足す：補題 TOP$`_\lambda`$ と RS$`_\lambda`$、定理 BLK$`^\Xi`$、$`V_\omega(1)`$ より下で OFF-V の閉じた形つきの定理 BLK$`^O`$、$`V_\omega(1)`$ より下の CORE-C。新しい公理は無い。公理は 4 つのファイル Cited、CitedR1、CitedC09、CitedL にあり、全部で 44 個（定数 9 個と事実 35 個）。この数も、このページのどの公理の数も、
Lean の 3 つの標準の公理 `propext`、`Classical.choice`、`Quot.sound` を除いている（だから `#print axioms` をそのまま見ると 3 個多い）。

## 1. ファイル

| ファイル | 中身 | 使う公理 |
|---|---|---|
| [R2/Defs.lean](R2/Defs.lean) | Carlson 2009 からの $`R_2^C`$ の定義：閉じた集合（Def 2.1、2.3）、被覆（Def 5.2）、$`\le_1^\infty`$ と $`\le_2^\infty`$（Def 5.3）、右端についての再帰での $`\le_1`$、$`\le_2`$（Def 5.4）。どの解釈でも同型、$`\le_{pw}`$、同型最小の集合、核（Def 2.6） | 無し |
| [R2/Basic.lean](R2/Basic.lean) | 再帰の等式。$`\le_1`$、$`\le_2`$ の基本の性質。届く先 | 無し |
| [R2/Loc.lean](R2/Loc.lean) | 補題 LOC とその系 | 無し |
| [R2/Cited.lean](R2/Cited.lean) | 段階 1 の公理（§2.1） | — |
| [R2/Points.lean](R2/Points.lean) | $`R_1^+`$ の $`\upsilon`$ の点、切片、やり直し $`\rho_\lambda`$、届く先 $`r(\lambda)`$ | 引いたもの |
| [R2/Frag.lean](R2/Frag.lean) | 補題 ST、定義域全体での基 1 つの FRAG | 引いたもの |
| [R2/FragBase.lean](R2/FragBase.lean) | 閉包、成分、切片、定義域 $`D_k`$、集合の上の 1 回の基の取りかえ、場合分け | 引いたもの |
| [R2/FragM.lean](R2/FragM.lean) | 高さ、縮める段階、基がいくつでもの定理 FRAG | 引いたもの |
| [R2/Frag2.lean](R2/Frag2.lean) | Lean の $`R_2^C`$ についての定理 FRAG2 | `le1R` だけ |
| [R2/Arith.lean](R2/Arith.lean) | Carlson 2009, L.4.4、L.4.5（閉じた埋め込み）、L.5.5 (7)。成分と閉じた集合 | 無し |
| [R2/CitedC09.lean](R2/CitedC09.lean) | Carlson 2009 からの 2 つの公理（§2.3） | — |
| [R2/CoreC.lean](R2/CoreC.lean) | Thm 14.10 と 14.14 からの核：同型最小の集合は最小、核は始めの切片、核の点には届く先がある | C09 |
| [R2/Move.lean](R2/Move.lean) | 補題 MOVE。定理 CP\* と CP | 無し / C09 |
| [R2/CitedR1.lean](R2/CitedR1.lean) | 段階 2 で足した $`R_1^+`$ と $`T^\tau`$ についての 11 個の公理（§2.2） | — |
| [R2/Ups.lean](R2/Ups.lean) | Lean の $`\upsilon`$ は Wilken の $`\upsilon`$（Wilken 2020, Def 21.4）。$`\upsilon_n`$、$`\upsilon_\omega`$ は可算 | 引いたもの |
| [R2/R1Gap.lean](R2/R1Gap.lean) | $`R_1^+`$ の届く先、区間、区間の中の $`\lt_1`$ の前の点 | 引いたもの |
| [R2/CCF.lean](R2/CCF.lean) | 定理 CC-F（$`R_1^+`$ での閉じた被覆の写し） | 引いたもの |
| [R2/Inc1.lean](R2/Inc1.lean) | LEFT-AT、FANCOF、PI2-UP、CLEAN-C、NOBAD。定理 INC1 | 引いたもの |
| [R2/BlockC.lean](R2/BlockC.lean) | RIGHT-LIM、極限の添字つきの LEFT、RE-U、ブロックの中の SK1、最初の組より下で $`\le_1`$ について $`R_2^C = R_1^+`$、骨組みを減らした FRAG2 と FRAG | 引いたもの |
| [R2/CitedL.lean](R2/CitedL.lean) | 段階 3 の 4 つの公理（§2.4） | — |
| [R2/ChainL.lean](R2/ChainL.lean) | 補題 L（鎖の上限。区間の中でも） | 引いたもの（16 個） |
| [R2/BaseC.lean](R2/BaseC.lean) | 基の取りかえとその逆は加法的に主要な数と $`R_1^+`$ の $`\le_1`$ を保つ。閉じた像 | 引いたもの |
| [R2/Pair1.lean](R2/Pair1.lean) | $`R_2^C`$ での定理 A：最初の組 $`\upsilon_\omega \lt_2 \upsilon_{\omega+1}`$。補題 COMP-C | 引いたもの（35 個） |
| [R2/BlockB.lean](R2/BlockB.lean) | ブロックの中の SK1。定理 B（$`\upsilon_{\omega\cdot\omega}`$ より下の組） | 引いたもの（35 個） |
| [R2/RstC.lean](R2/RstC.lean) | やり直しとその最初のブロック：補題 C″ (a)、B″4、TOP | 引いたもの（35 個） |
| [R2/Blk3.lean](R2/Blk3.lean) | $`\upsilon_{\omega^3}`$ より下のどのやり直しでも：定理 B″、$`\upsilon_{\omega^3}`$ より下の組、SK3 | 引いたもの（35 個） |
| [R2/RS.lean](R2/RS.lean) | 補題 RS と RS$`^h`$：$`\rho_h`$ の届く先 | 引いたもの（41 個） |
| [R2/RstK.lean](R2/RstK.lean) | やり直しより下の蓋を求めないやり直しの文脈。蓋を使わない段階 3 の補題。項 $`x\cdot m + k`$ についての **ずれつきの補題 TOP** | 引いたもの（35 個） |
| [R2/Off.lean](R2/Off.lean) | $`\Xi`$（$`\upsilon`$ の導関数）、$`\Xi_\omega`$。$`c(\lambda) = -1 + \mathrm{logend}(\lambda)`$ とずれ $`c^*`$。$`\Xi_\omega`$ までのずれの補題 | 引いたもの（14 個以下） |
| [R2/BlkX.lean](R2/BlkX.lean) | 要る入力を持つどのずれでも、やり直しの添字に沿ったブロックの構造（FRAG 無し）。TOP$`_\lambda`$ | 引いたもの（35 個） |
| [R2/RSX.lean](R2/RSX.lean) | **やり直しを行き先とする補題 RS**。RS$`_\lambda`$。**定理 BLK$`^\Xi`$**。$`\omega^e`$、$`\Xi_n`$、$`\Xi_\omega`$ での届く先 | 引いたもの（41 個） |
| [R2/OffPhi.lean](R2/OffPhi.lean) | $`\mathrm{logend}`$。$`\Phi_1`$。$`\Phi_1`$ より下のずれ。$`\Phi_1`$ より下の BLK$`^O`$ | 引いたもの（41 個） |
| [R2/OffV.lean](R2/OffV.lean) | $`V_n`$、$`V_\omega(1)`$、OFF-V の閉じた形。**$`V_\omega(1)`$ より下の定理 BLK$`^O`$**。$`V_n(\alpha)`$ と $`\Phi_1`$ での届く先 | 引いたもの（41 個） |
| [R2/CoreX.lean](R2/CoreX.lean) | **CORE-C**：$`[0, V_\omega(1)) \subseteq \mathrm{Core}(R_2^C)`$ | 引いたもの（35 個）+ C09 |

[R2/Defs.lean](R2/Defs.lean) の 2 つの読みは Carlson の文と同じ意味で、そこで説明している：$`\le_2^\infty`$ の節 (c) と (d) は 1 つの被覆にする（有限集合の被覆は順序の同型）。「どの有限の構造」は
関係つきの順序数の有限の閉じた集合の上を動く（どの有限の算術の構造もそのどれかと同型、Carlson 2009 の L.4.6 のあとの注意）。「$`c`$ より下に共終に多く」は狭い意味で読む（どの
$`c' \lt c`$ にもその上の写しがある）。Carlson 2009 の L.5.5 (1) の証明と同じ。

## 2. 公理

### 2.1 段階 1（[R2/Cited.lean](R2/Cited.lean)）

このファイル（と CitedR1）の公理は $`R_2^C`$ に触れない。Carlson の定義の読み違いは Lean の $`R_2^C`$ を Carlson のものと違うものにしうるだけで、公理を矛盾させることはできない。公理は
$`R_1^+ = (\mathrm{Ord}; 0, +, \le, \le_1)`$ と、基の取りかえ $`\pi_{\sigma,\tau}`$ つきの Wilken の項の体系 $`T^\tau`$ についてのもので、いつも $`\varepsilon`$ 数 $`\sigma \lt \tau \lt \Omega_1`$、$`\Omega_1 = \omega_1`$ について。

論文：[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161。[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175。

**7 個の定数**（論文の対象で、Lean では定義しない）：`le1R`（$`R_1^+`$ の $`\le_1`$）、`Tset`（$`T^\tau`$）、`Par`（$`\mathrm{Par}^\tau`$、[W07a] Def 3.28）、`pi`（$`\pi_{\sigma,\tau}`$、[W07a] Def 5.1）、`ht`（高さ、
[W07a] L.3.27）、`Dl` と `Dp`（項 $`\vartheta^\tau(\Delta_n)`$ と $`\vartheta^\tau(\Delta_n + 1)`$）。

**20 個の事実：**

| 公理 | 主張（短く） | 出典 |
|---|---|---|
| `le1R_trans`、`le1R_le`、`le1R_of_le` | $`\le_1`$ は推移的、$`\le`$ の中、区間の性質を持つ | [W07b] L.2.1 と §1（主張は [W07b] §2） |
| `le1R_two_iff` | $`a \gt 0`$ で：$`a \le_1 a\cdot 2`$ は $`a`$ が $`\varepsilon`$ 数のときちょうど | [W07b] Thm 2.2 のあとの注意 |
| `TB_inter_lt` | $`T^\tau[\sigma] \cap \tau = \sigma`$ | [W07a] L.5.3 の証明 |
| `pi_lt`、`pi_base`、`pi_Om1` | $`\pi`$ は $`\sigma`$ より下を動かさず、$`\tau`$ を $`\sigma`$ へ送り、$`\Omega_1`$ を動かさない | [W07a] Def 5.1（L.3.27 の証明と Def 3.1 のあとの注意とともに） |
| `pi_bijOn`、`pi_add`、`pi_ht_Par` | $`\pi`$ は順序の同型で、$`+`$、高さ、パラメタを保つ | [W07a] L.5.3 (b)–(e)、Cor 5.4 |
| `lh_pi` | $`\pi`$ は $`R_1^+`$ の届く先 $`\mathrm{lh}`$ を保つ | [W07b] L.4.4、Thm 5.3、Cor 5.7 |
| `T_inter_Om1` | $`T^\tau \cap \Omega_1`$ は、上のすべてと $`\le_1`$ になる $`\alpha \gt \tau`$ の最小 | [W07b] Cor 5.10 |
| `Par_lt`、`Par_comps` | 小さい順序数と和のパラメタ | [W07a] Def 3.28 |
| `ht_spec`、`Dl_spec` | 高さ。項 $`\vartheta^\tau(\Delta_n)`$ | [W07a] L.3.27、Def 3.26 |
| `Dl_E` | $`\vartheta^\tau(\Delta_n)`$ は $`\tau`$ より上の $`\varepsilon`$ 数 | [W07a] L.4.3、Def 3.28 |
| `Dp_spec` | $`\alpha^+ = \vartheta^\alpha(\Delta)`$ | [W07a] Conv. 4.1、L.6.3 |
| `par_track` | 基を変えたあとのパラメタ | [W07a] L.6.10 と L.6.3、L.3.30 |

8 個の公理は引いた 2–3 個の節を 1 つの主張にしたもので、監査はどのつなぎも確かめた。`par_track` では Lean は成分についての閉じ方だけを、論文は成分と途中の和についての閉じ方を
求める。途中の和を足しても閉包は変わらないので、Lean の公理は論文の補題から出る。$`R_1^+`$ についての 3 つの事実（`le1R_trans`、`le1R_of_le`、`le1R_two_iff`）は手元に無い Wilken, AML 45 (2006)
で証明されていて、主張は [W07b] §2 にある。監査は公理どうしの食い違いを見つけなかった。小さいモデルも見つからなかった（$`R_1^+`$ についての事実の安いモデルは `Dl_E` を満たさない）ので、
無矛盾さは論文の対象に頼る。

### 2.2 段階 2、$`R_1^+`$ と $`T^\tau`$（[R2/CitedR1.lean](R2/CitedR1.lean)）

約束は §2.1 と同じ（$`\Omega_1 = \omega_1`$、基は $`1`$ か $`\varepsilon`$ 数、可算）。足した論文：Wilken, "A glimpse of Σ₃-elementarity" (2020)。

| 公理 | 主張（短く） | 出典 |
|---|---|---|
| `le1R_refl` | $`\le_1`$ は反射的 | [W07b] L.2.1 |
| `le1R_limit` | 極限 $`\lambda \gt a`$ で、$`[a, \lambda)`$ のどの $`b`$ でも $`a \le_1 b`$ なら $`a \le_1 \lambda`$ | [W07b] L.2.1 (a) |
| `le1R_lim_P` | ある $`b \gt a`$ で $`a \le_1 b`$ なら、$`a`$ は加法的に主要な数の極限 | [W07b] Thm 2.2 のあとの注意 |
| `tauW`（定数）、`tauW_normal` | Wilken の点 $`\tau_\xi`$ は真に増え、連続 | [W07a] Def 9.1 |
| `ltInf1_iff_tauW` | $`a \lt_1 \infty`$ は、ある $`\rho`$ で $`a = \tau_\rho`$ のときちょうど | [W07b] Cor 5.10 |
| `T_inter_Om1_one` | $`T^1 \cap \Omega_1`$ は $`a \lt_1 \infty`$ となる $`a \gt 1`$ の最小 | [W07b] Cor 5.10 と [W07a] Thm 3.23 |
| `T_one_bound` | $`T^1 \cap \Omega_1`$ は可算個の可算順序数の上限 | [W07a] Thm 3.23 と L.3.30 |
| `le1R_copy` | $`a \le_1 b`$ の有限集合による判定（向き「$`\Rightarrow`$」） | Wilken 2020, Prop 21.6 |
| `le1R_loc` | 加法的に主要な数の $`\tau`$ での局所化 | [W07b] Def 5.8、Cor 5.9 |
| `claim56` | ある有限集合のどの被覆も、その下の部分を動かさないことはない | [W07b] Claim 5.6（Thm 5.3 の証明） |

監査はどれも忠実と認めた。`claim56` の Lean の形は求めることが少ない（被覆と数える写像が少ない）ので、論文の主張より弱い。`le1R_refl`、`le1R_limit`、`le1R_lim_P` は手元に無い
Wilken, AML 45 (2006) の結果の言い直しで、主張は [W07b] §2 にある。Wilken 2020 は Prop 21.6 を手元に無い Carlson, AML 38 (1999) によるとするが、証明を載せ直しているので、その論文から
取るものは無い。$`R_1^+`$ についての事実の安いモデルは `claim56` を破るのでモデルではない。監査は食い違いを見つけなかった。

### 2.3 段階 2、Carlson 2009（[R2/CitedC09.lean](R2/CitedC09.lean)）

| 公理 | 主張（短く） | 出典 |
|---|---|---|
| `C09_thm14_10` | $`R_2^C`$ の有限の閉じた集合 $`A`$ について、$`A`$ と同型で、$`P^*`$ の被覆であるどの閉じた $`Q`$ よりも点ごとに下で、同型最小な $`P^*`$ がある | Carlson 2009, Thm 14.10 (1)–(3) |
| `C09_thm14_14` | $`R_2^C`$ の核は、上のすべてと $`\le_1`$ になる最小の $`\kappa`$。無ければ Ord 全体 | Carlson 2009, Thm 14.14 |

これらは $`R_2^C`$ に触れる最初の公理：Lean の $`R_2^C`$ が Carlson のものと違えば偽になりうる（どちらの監査も定義は文字どおりと認めた）。Thm 14.10 の Lean の形は $`0`$ を含まない
集合も許すが、その場合は $`0`$ を含む場合から出る。$`0 \le_i b`$ は $`b = 0`$ のときだけで、被覆は $`0`$ を外に保つから。

### 2.4 段階 3（[R2/CitedL.lean](R2/CitedL.lean)）

| 公理 | 主張（短く） | 出典 |
|---|---|---|
| `lhT`（定数） | $`\alpha \in T^\tau \cap \Omega_1`$ について定義される $`\mathrm{lh}^\tau(\alpha)`$ | [W07b] Def 4.1 |
| `lh_eq_lhT` | 可算の $`\tau \in \{1\} \cup E`$ と、$`\tau \lt \alpha \lt \Omega_1`$ で加法的に主要な $`\alpha \in T^\tau`$ について、$`R_1^+`$ での $`\alpha`$ の届く先は $`\mathrm{lh}^\tau(\alpha)`$ | [W07b] Thm 5.3 |
| `ht_lhT_lt` | そのような $`\alpha`$ が $`\varepsilon`$ 数なら $`\mathrm{ht}_\alpha(\mathrm{lh}^\tau(\alpha)) \lt \mathrm{ht}_\tau(\alpha)`$ | [W07b] L.4.5 |
| `Par_sub` | $`\mathrm{Par}^\tau(\alpha) \subseteq \tau`$（$`\tau \in E`$ についてだけ述べる。論文は $`\tau = 1`$ も持つが要らない） | [W07a] Def 3.28 |

監査は 4 つとも忠実と認めた。論文の「$`\alpha = \vartheta^\tau(\Delta + \eta)`$」は、CitedR1 にすでにあるつなぎで「$`\alpha`$ は加法的に主要」と読み、「$`\Delta \gt 0`$」は「$`\alpha`$ は
$`\varepsilon`$ 数」と読む（[W07a] L.4.3）。新しい公理はどれも $`R_2^C`$ に触れず、段階 3 のどの定理も CitedC09 の公理を使わない。

## 3. 定理

「無し」は Lean の標準の公理 `propext`、`Classical.choice`、`Quot.sound` だけということ（`#print axioms` による）。

| 定理 | 主張 | 公理 |
|---|---|---|
| `le1_iff`、`le2_iff` | Carlson 2009, Def 5.4 の再帰の等式 | 無し |
| `le1_refl`、`le1_trans`、`le1_le`、`le1_antisymm`、`le2_refl`、`le2_trans`、`le2_le1`、`le2_le` | $`\le_1`$、$`\le_2`$ は反射的で推移的、$`\le_2 \subseteq \le_1 \subseteq \le`$ | 無し |
| `le2_of_le1` | Carlson 2009, L.5.5 (6) | 無し |
| `le1_of_le_of_le1`、`le1_limit` | $`\le_1`$ の区間と極限の性質 | 無し |
| `cof_core`、`le1_cof` | Carlson 2009, L.5.5 (1) | 無し |
| `exists_closed` | $`(\mathrm{Ord}; 0, +, \le)`$ についての Carlson 2009, L.2.5 | 無し |
| `exists_reach`、`reach_spec` | $`x`$ がそれより大きいどの順序数とも $`\le_1`$ でない限り $`\mathrm{lh}(x)`$ がある | 無し |
| `isominimal_congr` | 補題 LOC：有限集合が同型最小かどうかは、その最大の元までの構造だけで決まる | 無し |
| `core_subset_of_agree` | $`R`$ と $`R'`$ が $`\kappa`$ より下で一致し $`\mathrm{Core}(R) \subseteq \kappa`$ なら $`\mathrm{Core}(R) \subseteq \mathrm{Core}(R')`$ | 無し |
| `upsPt_inE`、`le1R_lt_ups`、`exists_next` | $`\upsilon`$ の点は $`\varepsilon`$ 数。$`\upsilon`$ の点をまたぐ $`\le_1`$。次の $`\upsilon`$ の点 | 引いたもの |
| `st_le1` | 補題 ST：基の取りかえは $`\le_1`$ を両向きに保つ | 引いたもの（8 個） |
| `frag1` | 定義域全体での基 1 つの FRAG | 引いたもの（16 個） |
| `frag` | **定理 FRAG**：可算の $`\upsilon`$ の点 $`\kappa`$、その上の可算の $`\upsilon`$ の点 $`b_0 \lt \dots \lt b_{m-1}`$ と $`c_0 \lt \dots \lt c_{m-1}`$、有限の $`F \subseteq D_m`$ について、$`\kappa`$ より下で恒等、$`b_k`$ を $`c_k`$ へ、$`b_k`$ の切片を $`c_k`$ の切片へ送り、$`0, +, \le`$ と $`R_1^+`$ の $`\le_1`$ を両向きに保ち、$`\upsilon`$ の点と $`\varepsilon`$ 数を保つ $`\Psi`$ がある | 引いたもの（27 個すべて） |
| `frag2` | **定理 FRAG2**：$`R_2^C`$ が $`Y \cup \Psi[Y]`$ で骨組みなら、$`0, +, \le`$、$`R_1^+`$ の $`\le_1`$、$`\upsilon`$ の点を保つ写像が $`Y`$ の上で $`R_2^C`$ の同型なのは、蓋と $`\upsilon`$ の点の組を保つときちょうど | `le1R` |

**段階 2。**

| 定理 | 主張 | 公理 |
|---|---|---|
| `le_of_le_on_indec`、`ext_arithIso`、`ext_closed`、`ext_unique` | Carlson 2009, L.4.4 と L.4.5：閉じた集合の加法的に主要な数の上の順序を保つ写像は、閉じた埋め込みにただ 1 通りに広がる | 無し |
| `indec_of_lt1`、`indec_of_lt2_right` | Carlson 2009, L.5.5 (7) | 無し |
| `isominimal_least` | 同型最小の集合は、それが覆うどの閉じた集合よりも点ごとに下 | Thm 14.10 |
| `core_downward`、`exists_reach_of_core`、`core_subset_of_agree_C` | 核は始めの切片。核のどの点にも届く先がある。LOC の系をその仮定無しで | Thm 14.14 |
| `move` | 補題 MOVE：加法的に主要な点を 1 つ下に動かすと被覆になる | 無し |
| `cp_star`、`cp` | 定理 CP\* と CP：届く先の $`\le_1`$ の前の点が $`u`$ より下で共終な、核の加法的に主要な点 $`u`$ は組の左端 | Thm 14.10（`cp'` は Thm 14.14 も） |
| `upsilon_normal`、`upsPt_iff_upsilon`、`upsilon_succ_T`、`upsilon_omega_lt_Om1` | Lean の $`\upsilon`$ は Wilken 2020, Def 21.4 を満たし、正規。$`\upsilon_n`$、$`\upsilon_\omega`$ は可算 | 引いたもの |
| `ccf` | 定理 CC-F | 引いたもの |
| `inc1` | **定理 INC1**：$`R_2^C`$ で $`a \le_1 b`$ かつ $`b \lt \Omega_1`$ なら $`R_1^+`$ で $`a \le_1 b`$（$`R_2^C`$ についての公理無し） | 引いたもの（16 個） |
| `left`、`left_limit`、`fan_right_ups`、`right_lim`、`re_u` | LEFT（可算の $`\lt_2`$ の左端は $`\upsilon_\lambda`$、$`\lambda`$ は極限）、NOBAD、RIGHT-LIM、RE-U | 引いたもの |
| `block_le1_iff`、`le1_iff_le1R_below`、`le1_iff_le1R_upsilon_omega` | ブロックの中の SK1。最初の $`\lt_2`$ の右端より下と $`[0, \upsilon_\omega]`$ で、$`R_2^C`$ の $`\le_1`$ は $`R_1^+`$ の $`\le_1`$ に等しい | 引いたもの |
| `frag2_C`、`frag_frag2_C` | INC1 と LEFT で骨組みの仮定を減らした FRAG2。それとあわせた FRAG の写像 | 引いたもの |

INC1 の証明は、このプロジェクトの補題 L の代わりに [W07b] Cor 5.9（区間の中の $`\lt_1`$ の前の点は有限個）を使い、そのぶん簡単になった。監査は 101 個の定理の公理を印字した。どれも
Lean の標準の 3 つと引いた 40 個だけを使う。

**段階 3。** `rI`、`rstCtx`、`thmB2_C`、`rs_h`、`reach_rst` では Lean の添字は論文より 1 小さい（Lean の $`h`$ ＝ 論文の $`h - 1`$）：Lean の $`h`$ はやり直し $`\rho_{h+1} = \upsilon_{\omega^2(h+1)}`$。段階 4 からはこれらのファイルの説明の行にそう書いてあり、`Par_sub` の説明の行は $`\tau \in E`$ についてだけ述べていると書く。

| 定理 | 主張 | 公理 |
|---|---|---|
| `chain_bound`、`chain_bound_gap` | **補題 L**：$`\tau \in \{1\} \cup E`$、$`z_0 \in T^\tau \cap (\tau, \Omega_1)`$ について、$`R_1^+`$ の鎖 $`z_0 \lt_1 \dots \lt_1 z_k`$ は $`k \le \mathrm{ht}_\tau(z_0) + 1`$。区間の中でも同じ | 引いたもの（16 個） |
| `thmA_C`、`first_pair` | **定理 A**：$`\upsilon_\omega \lt_2 \upsilon_{\omega+1}`$ が $`R_2^C`$ の最小の組で、左端は $`\upsilon_\omega`$ だけ。$`\upsilon_{\omega+1}`$ までは $`\le_1`$ は $`R_1^+`$ のもの。$`\upsilon_{\omega+1}`$ 以下のどの点もより大きい点に $`\le_1`$ でない | 引いたもの（35 個） |
| `comp_c` | **補題 COMP-C**：切片の圧縮（定理 CC-F、そして逆向きの基の取りかえ）は $`R_2^C`$ の被覆 | 引いたもの（35 個） |
| `thmB_C` | **定理 B**：$`\upsilon_{\omega\cdot\omega}`$ より下の組はちょうど $`(\upsilon_{\omega(j+1)}, \upsilon_{\omega(j+1)+1})`$。ブロックの頂上で蓋。ブロックの中で $`R_1^+`$ の $`\le_1`$ | 引いたもの（35 個） |
| `thmB2_C` | **TOP つきの定理 B″**。$`\upsilon_{\omega^3}`$ より下のどのやり直しでも（その 7 つの節、[SHIFT11-ja.md](SHIFT11-ja.md) §2.3） | 引いたもの（35 個） |
| `rs_h`、`reach_rst` | **RS、RS$`^h`$**：$`\rho_h \le_1 \delta_h + 1`$、そして $`\mathrm{lh}(\rho_h) = \delta_h + 1`$ | 引いたもの（41 個） |
| `pairs_lt_w3` | $`\upsilon_{\omega^3}`$ より下の組はちょうど $`(\upsilon_\xi, \upsilon_{\xi+1})`$、$`\xi = \omega^2 h + \omega j + \omega`$ | 引いたもの（35 個） |
| `sk3_C` | **SK3**：$`\upsilon_{\omega^3}`$ より下で $`\upsilon`$ の点でないどの点も、どの $`\gamma`$ とも $`R_1^+`$ の $`\le_1`$ を持つ | 引いたもの（35 個） |
| `not_le1_zero` | $`R_2^C`$ で $`0 \le_1 b`$ は $`b = 0`$ のときだけ | 無し |

監査は 11 個の主な主張の公理を印字した。あわせて 44 個の引いた公理のうち 41 個を使う。どのモジュールも、それが取り込むモジュールだけとともに単独でも確かめ、終わりに偽の主張を
足すとその確かめは失敗した。

**段階 4。** 新しい公理は無い。ここで $`\Xi_\alpha`$ は $`\iota \mapsto \upsilon_\iota`$ の 0 でない $`\alpha`$ 番目の固定点、$`V_0 = \upsilon`$、$`V_{n+1}`$ は $`V_n`$ の導関数、$`V_\omega(1) = \sup_n V_{n+1}(1)`$、$`\Phi_1 = V_2(1)`$、
$`\Xi_\omega`$ より下で $`c^*(\lambda) = -1 + \mathrm{logend}(\lambda)`$、$`c^*(\Xi_\omega) = \Xi_\omega + 1`$（[REACHES-ja.md](REACHES-ja.md) §1）。

| 定理 | 主張 | 公理 |
|---|---|---|
| `RstK.top_gen` | **ずれつきの補題 TOP**：$`\rho`$ より下の蓋を求めないやり直しの文脈で、項 $`t(x) = x\cdot m + k`$ について、ある $`x_0 \lt \rho`$ より上のどの組も、項が許すより先にその右端を越えて届く点を持たなければ、$`\rho`$ は $`\delta + t(\rho)`$ より上のどの点にも $`\le_1`$ でない | 引いたもの（35 個） |
| `rs_rst` | **やり直しを行き先とする補題 RS**：$`\rho_r`$ より下で共終なやり直し $`\rho_\mu`$ が $`\rho_\mu \le_1 \delta_\mu + t(\rho_\mu)`$ を満たせば、$`\rho_r \le_1 \delta_r + t(\rho_r) + 1`$（FRAG による） | 引いたもの（41 個） |
| `rs_all`、`reach_all` | **RS$`_\lambda`$ と TOP$`_\lambda`$**：$`\lambda \le \Xi_\omega`$ のどのやり直しの添字でも $`\mathrm{lh}(\rho_\lambda) = \delta_\lambda + c^*(\lambda)`$ | 引いたもの（41 個） |
| `blkXi` | **定理 BLK$`^\Xi`$**：(i) 右端が $`\upsilon_{\Xi_\omega+\omega^2}`$ より下の $`\lt_2`$ の組はちょうど $`(\upsilon_{\mu+\omega j}, \upsilon_{\mu+\omega j+1})`$。(ii) $`\lambda \le \Xi_\omega`$ では、$`\rho_\lambda`$ より下のどの点もそれ以上の点に $`\le_1`$ でなく、$`\rho_\lambda`$ は $`\lt_2`$ の後の点を持たず、その届く先は $`\delta_\lambda + c^*(\lambda)`$。(iii) 上限より下で $`\upsilon`$ の点でないどの点も $`R_1^+`$ の $`\le_1`$ を持つ | 引いたもの（41 個） |
| `blkPhi`、`blkV` | $`\Phi_1`$ より下と $`V_\omega(1)`$ より下の **定理 BLK$`^O`$**。OFF-V の閉じた形つき：ずれは段 0 で $`c(\lambda)`$、$`\lambda = V_n(\alpha)`$ で $`\rho\cdot n + \mathrm{logend}(\alpha)`$ | 引いたもの（41 個） |
| `reach_w3`、`reach_ww`、`reach_Xi`、`reach_XiW`、`reach_XiA`、`reach_Phi1`、`reach_Vn` | 届く先：$`\omega^3`$ で $`\delta + 2`$、$`\omega^\omega`$ で $`\delta + \omega`$、$`\Xi_n`$ で $`\delta + \Xi_n`$、$`\Xi_\omega`$ で $`\delta + \Xi_\omega + 1`$、$`\Xi_\alpha`$（$`\alpha \lt \Phi_1`$）で $`\delta + \Xi_\alpha + \mathrm{logend}(\alpha)`$、$`\Phi_1`$ で $`\delta + \Phi_1\cdot 2`$、$`V_n(\alpha)`$ で $`\delta + V_n(\alpha)\cdot n + \mathrm{logend}(\alpha)`$ | 引いたもの（41 個） |
| `core_Xi`、`core_Phi`、`core_V` | **CORE-C**：$`[0, \upsilon_{\Xi_\omega+\omega^2})`$、$`[0, \Phi_1)`$、$`[0, V_\omega(1))`$ は $`\mathrm{Core}(R_2^C)`$ に入る（FRAG 無し） | 引いたもの（35 個）+ Thm 14.14 |

監査は 76 個の定理の公理を印字した。あわせて 44 個の引いた公理のうち 42 個を使う（`le1R_limit` と `C09_thm14_10` は使わない）。どのモジュールも単独で、そして全部まとめて確かめ直し、
致命的な点も進行を止める点も見つけなかった。3 つの細かい点：(i) は **右** 端が上限より下の組についてのもの（論文の主張は左端で述べる。やり直しについては (ii) が残りを除く）。
(iii) は $`\upsilon`$ の点でない点を覆い、やり直しでない $`\upsilon`$ の点は覆わない。(ii) は `IsReach`（$`\rho \le_1 \gamma`$ となる最大の $`\gamma`$）で述べ、区間の形
$`\{\gamma : \rho \le_1 \gamma\} = [\rho, \delta + c^*]`$ は公理を使わない Basic の `le1_of_le_of_le1` から出る。論文の再帰的なずれ $`O`$ は形式化していない：Lean は $`V_\omega(1)`$ より下で閉じた形を
直接証明する。ずれの項は $`m`$ が有限の $`x\cdot m + k`$ なので、[W07a] L.4.2 と [W07b] Thm 2.2 は要らない。だからこの段階は、ずれ $`\rho\cdot\omega`$ が項 $`\omega^{x+1}`$ を要する $`V_\omega(1)`$ で止まる。

`frag` の定義域 $`D_m`$ は $`D_{m-1}`$ の閉包の中のパラメタを許す。これは論文の証明（[RESTARTS-ja.md](RESTARTS-ja.md) §1）の定義域を含むので、Lean の定理のほうが強い。基はすべて可算で、
これらのページで使うのはその場合だけ。

## 4. まだ Lean に無いもの

この順に（これらの段階の論文での証明はある。[SHIFT11-ja.md](SHIFT11-ja.md) §3.6 を見よ）：

- $`V_\omega(1)`$ より上の BLK$`^O`$（$`\Lambda_\varepsilon`$ まで）。$`\omega^t`$ と $`\varepsilon_{x+1}`$ を持つずれの項が要るので、引いた事実として [W07a] L.4.2 と一般の [W07b] Thm 2.2 が要る（Thm 2.2 の
  証明は手元に無い Wilken, AML 45 (2006) にある。その主張を [W07b] §2 から引くか、このプロジェクト自身の証明を形式化する）。あるいは再帰的なずれ $`O`$。
- SKEL⁺、CAP、LIFT-0。次に定理 O$`^C`$（CP は用意できている）、NU-CT、$`\nu_C`$。
- $`R_2^S`$ の側は形式化していない。
