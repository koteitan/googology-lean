[← Back](README-ja.md) | [English](LEAN.md) | [Japanese](LEAN-ja.md)

# Lean での $`R_2^+`$：$`R_2^C`$、核、FRAG

このページは、40 回目（[SHIFT10-ja.md](SHIFT10-ja.md) §3.3）で足したディレクトリ [R2/](R2/)（名前空間 `Googology.Trans.PoR.InaccPsi.R2`）の Lean のファイルを説明する。ライブラリ全体と
ともに作られる（`lake build`、緑、`sorry` 無し）。監査は、どの公理も引いた論文に忠実で、どの定義も正しく、どの主な定理も Lean が証明していると認め、致命的な点も進行を止める点も
見つけなかった。

**これで何が変わるか。** ほかのページの $`\upsilon_{\omega\cdot\omega}`$ より上のほとんどの結果は「FRAG のもと」で述べている。FRAG は今は Lean の定理で、標準でない公理は Wilken の 2 本の論文
から引いた 20 個の事実（とその論文の対象のための 7 個の定数）だけ。だから「FRAG のもと」は「この 20 個の引いた事実のもと」と読める。

## 1. ファイル

| ファイル | 中身 | 使う公理 |
|---|---|---|
| [R2/Defs.lean](R2/Defs.lean) | Carlson 2009 からの $`R_2^C`$ の定義：閉じた集合（Def 2.1、2.3）、被覆（Def 5.2）、$`\le_1^\infty`$ と $`\le_2^\infty`$（Def 5.3）、右端についての再帰での $`\le_1`$、$`\le_2`$（Def 5.4）。どの解釈でも同型、$`\le_{pw}`$、同型最小の集合、核（Def 2.6） | 無し |
| [R2/Basic.lean](R2/Basic.lean) | 再帰の等式。$`\le_1`$、$`\le_2`$ の基本の性質。届く先 | 無し |
| [R2/Loc.lean](R2/Loc.lean) | 補題 LOC とその系 | 無し |
| [R2/Cited.lean](R2/Cited.lean) | 公理はここだけ（§2） | — |
| [R2/Points.lean](R2/Points.lean) | $`R_1^+`$ の $`\upsilon`$ の点、切片、やり直し $`\rho_\lambda`$、届く先 $`r(\lambda)`$ | 引いたもの |
| [R2/Frag.lean](R2/Frag.lean) | 補題 ST、定義域全体での基 1 つの FRAG | 引いたもの |
| [R2/FragBase.lean](R2/FragBase.lean) | 閉包、成分、切片、定義域 $`D_k`$、集合の上の 1 回の基の取りかえ、場合分け | 引いたもの |
| [R2/FragM.lean](R2/FragM.lean) | 高さ、縮める段階、基がいくつでもの定理 FRAG | 引いたもの |
| [R2/Frag2.lean](R2/Frag2.lean) | Lean の $`R_2^C`$ についての定理 FRAG2 | `le1R` だけ |

[R2/Defs.lean](R2/Defs.lean) の 2 つの読みは Carlson の文と同じ意味で、そこで説明している：$`\le_2^\infty`$ の節 (c) と (d) は 1 つの被覆にする（有限集合の被覆は順序の同型）。「どの有限の構造」は
関係つきの順序数の有限の閉じた集合の上を動く（どの有限の算術の構造もそのどれかと同型、Carlson 2009 の L.4.6 のあとの注意）。「$`c`$ より下に共終に多く」は狭い意味で読む（どの
$`c' \lt c`$ にもその上の写しがある）。Carlson 2009 の L.5.5 (1) の証明と同じ。

## 2. 公理（[R2/Cited.lean](R2/Cited.lean)）

$`R_2^C`$ に触れる公理は無い。Carlson の定義の読み違いは Lean の $`R_2^C`$ を Carlson のものと違うものにしうるだけで、公理を矛盾させることはできない。公理は
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

`frag` の定義域 $`D_m`$ は $`D_{m-1}`$ の閉包の中のパラメタを許す。これは論文の証明（[RESTARTS-ja.md](RESTARTS-ja.md) §1）の定義域を含むので、Lean の定理のほうが強い。基はすべて可算で、
これらのページで使うのはその場合だけ。

## 4. まだ Lean に無いもの

- $`R_2^C`$ の $`\le_1`$（定義したもの）と $`R_1^+`$ の $`\le_1`$（定数 `le1R`）のつながり：まず INC1（[BREAK-ja.md](BREAK-ja.md) §1）。FRAG2 は骨組みを仮定として取る。
- Carlson 2009, Thm 14.10 と Thm 14.14（核は、上のすべてと $`\le_1`$ になる最小の $`\kappa`$）。LOC の系はこれを仮定として取る。
- `upsilon` が Wilken の $`\upsilon`$ であること（$`\{0\}`$ と上のすべてと $`\le_1`$ になる点の数え上げとして定義している）、`reach` がある所では最大であること。
- $`\nu_C`$ への鎖、この順で：Carlson 2009, L.4.4–4.5。補題 MOVE と定理 CP。INC1。$`\upsilon_{\omega^3}`$ より下のブロック（FRAG と FRAG2 の最初の使い道）。やり直しのブロック（BLK$`^\Xi`$、BLK$`^O`$）。
  SKEL⁺、CAP、LIFT-0。定理 O$`^C`$、NU-CT、$`\nu_C`$ の名前。$`R_2^S`$ の側は形式化していない。
