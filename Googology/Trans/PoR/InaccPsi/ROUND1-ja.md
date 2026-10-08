[← Back](README-ja.md) | [English](ROUND1.md) | [Japanese](ROUND1-ja.md)

# $`R_2^+`$ の 1 回目：有限集合による判定、長さ 3 の鎖に向けて、下界に向けて

1 回目（2026-10）のこれらの結果は [README-ja.md](README-ja.md) §3 にあった。GitHub が数式を描ける量に収めるため、変えずにここへ移した。
状態の言葉は [README-ja.md](README-ja.md) §3 のもの。補題 HULL、予想 C3′、定理 S など、ここでリンク無しに名前を挙げる結果は [README-ja.md](README-ja.md) §3 にある。

## 1. $`R_2^S`$ での有限集合による判定

（2026-10。）言語 $`\{0, +, \le, \le_1, \le_2\}`$ を有限の関係の言語として読む。

- **T1**（$`\Sigma_1`$）。$`\alpha \le_1 \beta`$ は次と同値：有限の $`X \subset \alpha`$ と $`Y \subset [\alpha, \beta)`$ のどれにも、
  $`X \lt \tilde Y`$ となる $`\tilde Y \subset \alpha`$ と、$`X`$ を動かさない同型 $`X \cup \tilde Y \cong X \cup Y`$ がある。
  $`\tilde Y`$ は、どの $`\rho \lt \alpha`$ より上にもとれる。
- **補題 PR。** $`\alpha \lt_1 \beta`$ なら $`\alpha = \omega^a`$（$`a`$ は極限）。$`\alpha \lt_2 \beta`$ なら $`\beta = \omega^\lambda`$
  （$`\lambda`$ は極限）で、$`\alpha`$ はその $`\lt_1`$ の前の元たちの上限。
- **T2**（$`\Sigma_2`$、段つきの形。「同値」である。Wilken 2021 の Prop 1.6 と Wilken 2020 の Prop 21.11 は片向き
  だけ）。$`\alpha \le_2 \beta`$ は次と同値：そういう $`X, Y`$ とどの $`k`$ にも、T1 のような写し $`\tilde Y`$ があって、
  $`\alpha`$ 未満の $`k`$ 個以下の点でのどの拡張も、同型を $`\beta`$ の中へ延ばす。写しは、さらに共終に、
  $`y \le_1 \beta \Leftrightarrow \tilde y \le_1 \alpha`$ となるように、$`X \cup Y`$ が閉じていれば閉じるように、とれる。
- **定理 CMP。** $`\alpha \le_i^S \beta`$ なら、$`R_2^S`$ の中で計算した Carlson の被覆の条件が $`\le_i`$（$`i = 1, 2`$）で成り立つ。
  Carlson 2009, 98 ページは、これを証明なしに予告する。補題 KEEP：先頭の項への置き換えは、前向きの $`\le_1`$ と
  $`\le_2`$ を保つ。$`\lt_2`$ の組の両端は加法的主要数だから。

## 2. 長さ 3 の鎖を具体的に求めて

（2026-10、査読 1 回。）予想 C3′ の上半分についての結果：
- **集合論の反映。** ELEM：$`H`$ がある $`H(\vartheta)`$ の初等部分モデルで $`H \cap \gamma = \delta`$ が順序数なら、$`R_2|\delta`$ は $`R_2|\gamma`$ の
  初等部分構造（$`R_2^S`$ でも $`R_2^C`$ でも）。CLUB-1：非可算な正則 $`\kappa`$ では、$`\delta \le_1 \infty`$ となる $`\delta \lt \kappa`$ は club を含む。
  CHAINS-S：$`R_2^S`$ ではそのうちのどの 2 つも $`\le_2`$ なので、$`R_2^S`$ には可算な順序数の中にどの有限の長さの鎖もある。
  HIGH：そういう $`\delta`$ はどれも $`\omega_1^{CK} \gt \psi_{\Omega_1}(\Lambda)`$ より上なので、この方法では InaccPsi の範囲の中に鎖は出ない。
- **基数での $`\le_2`$。** LOCAL-2：HULL の写しは、$`\pi(\beta)`$ より下のすべての拡張で T2 の拡張の条件を満たす（$`Y \subseteq H`$ が
  要る）。破れうるのは $`[\pi(\beta), \kappa)`$ の点を通してだけ。CHANG-2（条件つき）：Chang 型の包の仮定から $`R_2^S`$ で
  $`\kappa \le_2 \lambda`$。その仮定は $`\lambda \ge \kappa^+`$ を強いる。SC2：$`V_\kappa \prec_{\Sigma_2} V_\beta`$ なら $`R_2^S`$ で $`\kappa \le_2 \beta`$。
  I0-NOT-SIGMA2：$`I_0`$ が最小の弱到達不能基数なら、$`V_{I_0}`$ は $`\beta \ge I_0 + 2`$ のどの $`V_\beta`$ でも $`\Sigma_2`$ 初等ではない。
  REFORM：「$`I_0 \le_2 \lambda`$」は $`\omega_1^{CK}`$ より上の 2 つの順序数についての命題と同値。未解決：ある $`\beta \gt I_0`$ で
  $`I_0 \le_2 \beta`$ か。
- **NO-PROMOTE。** $`\tau = \upsilon_{\omega^2}`$ は $`\tau \le_1 \upsilon_{\omega^2+\omega+1}`$（$`\tau`$ の上のやり直し $`r_{\omega+1}`$）となる
  $`\varepsilon`$ 数だが、$`\{\upsilon_{\omega^2+1}, \upsilon_{\omega^2+\omega}, \upsilon_{\omega^2+\omega+1}\}`$ は鎖ではない（R2PLUS の補題 TOP と
  定理 B′′。$`R_2^S`$ では FRAG なし、$`R_2^C`$ では EQB′′ を通す）。だから $`\tau`$ の $`\le_1`$ の届く先だけでは C3′ は示せない。
  $`c_0`$ の $`\le_2`$ の性質が要る。
- **補題 K と COLLAPSE-FAIL。** 包 $`\mathrm{Cl}(0, 0) \cap \Omega_2`$ のつぶしは、置き換え $`\Omega_1 \mapsto \Gamma_0`$（証明済み）。
  $`\Omega_1 \le_1 \varepsilon_{\Omega_1+1}\cdot 2`$（証明済み）。「$`\Gamma_0 \le_1 \varepsilon_{\Gamma_0+1}\cdot 2`$ ではない」は**証明されていない**：
  査読が止める点を見つけた（証明が右端そのものを $`Y`$ の点に使うが、判定 T1 はそれを許さない）。査読者は直し方を
  出したが、それはまだ査読されていない。これが成り立てば、InaccPsi の包をつぶしても $`\le_1`$ は保たれず、基数での
  $`\le_2`$ の関係を可算な値へ下ろすことはできない。

## 3. 下界に向けて

（2026-10、$`R_2^C`$。）$`\theta_0 = \psi_{\Omega_1}(\psi_{I_0}(0))`$ と書く。

- **補題 I-FREE。** 可算な標準形が到達不能基数の記号を含まないことと、その値が $`\theta_0`$ 未満であることは同値。
  だから到達不能基数を使わない項は、ちょうど $`\theta_0 \lt \psi_{\Omega_1}(I_0)`$ 未満の項。
- **補題 OE。** $`\gamma`$ 未満の標準形から点つきパターンへの写像 $`F`$ で、「$`F(t)`$ の最小の実現の点」が $`t`$ について
  狭義に増加するものがあれば、$`[0, \gamma) \subseteq \mathrm{Core}(R_2^C)`$。**EPS-RED**：$`F`$ は値が $`\varepsilon`$ 数の項でだけ
  要る。**FS-OE**：狭義の増加は 2 つの局所的な段「前の項は $`t`$ より下」「$`t[n]`$ は $`t`$ より下」から出る。
- **RED-BMS。** [R2PLUS-ja.md](../../BMS/PoR/Trio/R2PLUS-ja.md) の定理 S と合わせると、$`\gamma`$ より下の下界は、
  $`\gamma`$ 未満の $`\varepsilon`$ 数の項から $`V`$ 未満（FRAG を使えば $`V_3`$ 未満。FRAG は証明済み）の標準形のトリオ行列への順序を保つ
  埋め込み $`\mu`$ から出る。**S-RED**：Lean のクラス `TrioStdL` の行列では、$`\Phi_3`$ の点の狭義の増加は、ただ 1 つの命題
  「どの $`A`$ と $`k`$ でも $`\Phi_3(A[k])`$ の点は $`\Phi_3(A)`$ の点より下」に帰着する（Lean の定理 `trio_fs` と BMS の停止性から）。
- **補題 MU-A。** 項の断片 $`G_A`$（和。$`\Omega_\omega`$、$`\omega^{\Omega_\omega + c}`$、$`\theta\cdot\omega^e`$ の和の $`\psi_{\Omega_1}`$）の上で、
  トリオ行列への再帰的な写像 $`\mu`$ は狭義に増加。
- **補題 UNIF-V。** $`A_m = (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)^m`$（$`m \ge 3`$）とどの $`N`$ でも、$`\Phi_3(A_m[N])`$ の点は
  $`\Phi_3(A_m)`$ の点より下。$`\Phi_3`$ の出力の形を仮定する（$`m \le 8`$、$`N \le 6`$ で確認済み）。R2PLUS の定理 V
  （$`m = 2`$）を広げる。$`m = 3`$ では、出力の形がどの $`N`$ でも与えられた（2026-10、査読 1 回）。ただしその補題は
  スケッチしか書かれていないので、$`m = 3`$ は証明済みに数えない。CORE-C3 はこれを使わない。
- **補題 MU-B**（2026-10、査読 1 回）。もっと大きな断片 $`G_B \supset G_A`$：可算な極限の添字 $`\Omega_\xi`$（$`\xi`$ の中に
  $`\psi_{\Omega_1}`$ の項があってもよい）、可算な $`\kappa \ge 1`$ と $`c`$ での項 $`\omega^{\Omega_\xi\cdot\kappa + c}`$、添字の違う項の和、
  $`\theta`$ の尾、$`x \ge \psi_{\Omega_1}(\Omega_\omega)`$ での可算な $`\omega^x`$。広げた写像 $`\mu_B`$ は、$`G_A`$ の上では $`\mu`$ に等しく、
  $`\psi_{\Omega_1}(\Omega_\xi)`$（$`\xi \lt \varepsilon_0`$ は極限）では Lean の写像 `omegaIndexMatrix` に等しい。$`\mu_B`$ は $`G_B`$ の上で
  狭義に増加し、どの像も SRO より下。像が標準形であること：証明済み（Lean `trioStdL_omegaIndexMatrix`）なのは
  $`\psi_{\Omega_1}(\Omega_\xi)`$（$`\xi \lt \varepsilon_0`$ は極限）だけ。ほかは確認済み。査読は止める点を 1 つ見つけた。MU-B そのもの
  ではなく、MU-B を核に使うことに対して：核の分かっている部分に順序数は増えない。$`G_B`$ には
  $`[\varepsilon_0, \psi_{\Omega_1}(\Omega_\omega))`$ の元が無く（証明済み）、順序型は小さい（予想：アッカーマン順序数くらい）。補題 OE が
  与えるのは $`[0, \mathrm{otp}(G_B))`$ だけ。次の段では、$`\varepsilon_0`$ と $`\psi_{\Omega_1}(\Omega_\omega)`$ の間の $`\varepsilon`$ 数を
  覆わなければならない。
- **補題 MU-0**（2026-10、査読 1 回）。$`\upsilon_1 = \psi_{\Omega_1}(\Omega_\omega)`$ 未満の標準形は、辞書式順序の標準形のペア数列（空のものを
  含む）と順序同型。写像 $`\mu_0`$ は和を連結に、加法的主要数の項を根が 1 つの数列に送る。引用 1 つを仮定して証明済み：
  $`\upsilon_1`$ は Buchholz の $`\psi_0(\Omega_\omega)`$ に等しい（Lean の公理 `core_eq_psi`。出典は Buchholz 1986 で、最初に引いた
  Wilken 2007 ではない）。Lean の定理（`pairOrd_injective`、`range_pairOrd`、`ordOf_append'`、`lemmaR`）も使う。$`\mu_0`$ は
  「値をとり、ペアの順位の逆をとる」もので、項の上の再帰ではない。
- **補題 MU-B0**（2026-10、査読 1 回）。MU-B は $`G_{B0}`$ の上でも成り立つ。$`G_{B0}`$ は、土台を $`\upsilon_1`$ 未満のすべての加法的主要数の
  項に広げた $`G_B`$ で、土台では $`\mu_0`$ を使う：$`\mu_B`$ は狭義に増加し、どの像も SRO より下。像が標準形であることは
  確認済みだけ。**すき間**（証明済み）：$`G_{B0}`$ は $`[0, \varepsilon_{\upsilon_1+1})`$ を含み、そこから $`\upsilon_2 = \psi_{\Omega_1}(\Omega_\omega + \theta)`$
  までは何も含まない。だから段 0 の族 (M4) は、そこで核の証明済みの部分に順序数を足さない（まったく足さないことは
  もっともらしいが、証明されていない）。次のすき間は 1 つ上の段の土台（引数 $`\Omega_\omega + \zeta`$、$`\zeta \lt \theta`$。補題 TR1、未解決）。
