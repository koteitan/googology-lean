[← Back](README-ja.md) | [English](SHIFT13.md) | [Japanese](SHIFT13-ja.md)

# $`R_2^+`$ の 47、48 回目：$`R_2^C`$ で $`Z^\theta`$ まで、そして $`L(\Omega_3)`$ まで、$`R_2^S`$ で $`Z^{\mathrm{V}}`$ まで、そして $`Z^\theta`$ までの主張、Lean で $`\Lambda_{\varepsilon_{x+2}}`$ までのやり直しのブロックと、どの段でもの LIFT-0

このページは [SHIFT12-ja.md](SHIFT12-ja.md) の続き（そこの §3 が 46 回目）。§1 が 47 回目、§2 が 48 回目。状態の言葉は [README-ja.md](README-ja.md) §3 のもの：**証明済み** とは、独立した査読者が、
致命的な点も進行を止める点も無しに証明されていると認めたこと。致命的な点か進行を止める点があるものは **未証明** に挙げる。証明書は再生されたものだけを数える。
査読者が、知られたことか目標そのものの言い直しにすぎないと言った結果は、進みとして数えない。

## 1. 47 回目

論文は 3 本（2026-10）：$`Z^{\mathrm{V}}`$ より先の $`\psi_{\Omega_3}`$ の原子を持つ乗数の論文（§1.1）と、$`Z^{\mathrm{WW}}`$ より先の $`R_2^S`$ の側の論文（§1.2）は、どちらも査読 1 回。$`R_2^C`$ の
Lean の 8 つ目の段階（§1.3）は、公理と定義を確かめる監査を受けた（証明は Lean が確かめる）。この節の結果は、回数を書いていなければ査読 1 回。段の番号は
[SHIFT12-ja.md](SHIFT12-ja.md) §1 と同じ（論文より 1 つ大きい）。

記号は [SHIFT12-ja.md](SHIFT12-ja.md) のもの：$`L(e) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + P'\cdot e)`$、$`P' = \psi_{\Omega_2}(\Omega_\omega\cdot 2)`$、$`\theta'_2 = \psi_{\Omega_3}(\Omega_\omega\cdot 2)`$、
$`G''(\zeta) = \psi_{\Omega_2}(\Omega_\omega\cdot 2 + \theta'_2\cdot\zeta)`$。また $`\theta = \psi_{\Omega_2}(\Omega_\omega)`$（論文では $`P`$）、$`\theta_2 = \psi_{\Omega_3}(\Omega_\omega)`$、
$`\theta'_3 = \psi_{\Omega_4}(\Omega_\omega\cdot 2)`$、$`\Phi_\Omega = \psi_{\Omega_2}(\Omega_2)`$、$`\Phi_2 = \psi_{\Omega_3}(\Omega_3)`$（[SHIFT2-ja.md](SHIFT2-ja.md) §2.1 と同じ）。

**$`R_2^C`$ での最前線は $`Z^\theta`$ に進んだ。** FRAG のもとで、**Wilken の主張は $`R_2^C`$ で $`[0, Z^\theta]`$ で成り立つ（両方の半分）**。ここで

```math
Z^\theta = L(\theta'_2\cdot\theta_2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+\theta_2}),\qquad \theta_2 = \psi_{\Omega_3}(\Omega_\omega),
```

で、$`\beta_0 \gt Z^\theta`$ と $`T_3^C \gt Z^\theta`$ も成り立つ（§1.1）。前の回に予想した点 $`L(\theta'_2\cdot\psi_{\Omega_3}(\Omega_3))`$ は越えた。**$`R_2^S`$ では主張は今は
$`[0, Z^{\mathrm{V}})`$ で成り立ち**（FRAG のもと）、[SHIFT12-ja.md](SHIFT12-ja.md) §3.2 の予想 CAP$`^{\mathrm{WW}}`$ は証明された（§1.2）。$`Z^{\mathrm{V}}`$ から

```math
Z^{\mathrm{VG}} = L(\theta'_2\cdot\psi_{\Omega_3}(0) + \omega^{G''(\omega^2)+1}) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+\psi_{\Omega_3}(0)} + \omega^{G''(\omega^2)+1})
```

への段階には、蓋だけを読む 2 つ目の証明がある（§1.2）ので、**査読 2 回**。Lean では：$`\nu_C`$ はやり直し、$`\Lambda_{\varepsilon\cdot\omega}`$ までの定理 BLK$`^O`$、どの段でもの LIFT-0 と O$`^C`$（§1.3）。

引く論文：§1.1 と §1.2 は査読済みの段階を通してだけ：[W07a] と [W07b]（L.2.1、Cor 5.10）、Carlson 2009（L.5.5、L.5.7 (3)）、Wilken 2020（Prop 21.6、Def 21.4、Thm 21.13）、[CW12b]（L.7.5）、
[C11]（LOC-ISO を通して）。§1.3 は Carlson 2009（Lemma 15.11、Thm 14.10 (1)、Cor 15.15、Def 5.6）、Carlson 2001（「respects」の定義）、前の段階の公理を通してだけの [W07a] と [W07b]。
どれも Wilken, JSL 72 (2007)、Carlson, AML 38 (1999)、Wilken, AML 45 (2006) を使わない。

46 回目の査読の細かい点は直した：[SHIFT12-ja.md](SHIFT12-ja.md) §3.1 の査読の m1–m6 は §1.1 の論文で（m1：$`L`$ の定義域の補題は今はどの添字でも証明された）、そこの §3.2 の査読の m1–m4 は
§1.2 の論文で、そこの §3.3 の監査の m1、m3、m5 は Lean で（§1.3。m2、m4、m6 はすでに [LEAN-ja.md](LEAN-ja.md) と [REACHES-ja.md](REACHES-ja.md) にある）。違う入力に頼る部分の名札は、下で
分けて書く（そこの §3.1 の査読の m6 と §3.2 の査読の m4）。

### 1.1 $`\theta_2`$ より下の乗数と、$`R_2^C`$ で $`[0, Z^\theta]`$ での主張

乗数とは今はどの $`\zeta \lt \theta_2`$ でもよく、$`n`$ 項の層の $`\Omega_2, \Omega_3, \dots`$ を使う形（[SHIFT3-ja.md](SHIFT3-ja.md) §2.1 を 1 段上げたもの）で書く。$`G''(\zeta)`$ が標準形のとき、乗数は
正規という。段 3 のやり直し $`b = L(\lambda'')`$ での読み $`R''_b(\zeta)`$ は、その形のどの $`\Omega_k`$ も（つぶしとともに）$`\Omega_{k-1}`$ に下げ、各定数 $`c`$ を $`o_b(c)`$ と読んだもの。

- **どの添字でもの $`L`$ の定義域**（FRAG 無しで証明済み。[SHIFT12-ja.md](SHIFT12-ja.md) §3.1 の査読の m1）。頭の部分の補題 DOWN″、可算の定数の上界 CMAX、そして判定
  「$`\lambda''+u`$ が $`L`$ の定義域に入るのは、$`u`$ の可算の定数が $`L(\lambda''+u)`$ より下のとき、そのときだけ」（$`u \lt P'`$）は、どの添字でも成り立つ。どれも定義域の定義と単調性だけに頼り、
  [SHIFT12-ja.md](SHIFT12-ja.md) §3.1 での 6 つの使い方は確かめ直した。細かい点：CMAX に書いた理由は、可算のつぶしの中の可算の部分項では成り立たない。結果は帰納法で成り立つ (m1)。
  可算の定数の 2 つの定義は同じ判定を与える (m2)。
- **THETA″$`^\theta`$**（FRAG 無しで証明済み）。$`\theta_2`$ より下のどの正規な乗数も段を持ち、$`\zeta \mapsto 1 + R''_b(\zeta)`$ は、$`o_b`$ の定義域にある正規な乗数から、$`\lambda''+u`$ が $`L`$ の
  定義域に入るずれ $`1 \le u \lt \theta`$ の上への順序同型。だから $`o_b(G''(\zeta)) = L(\lambda''+1+R''_b(\zeta))`$ で、$`o_b`$ は $`G''(\theta_2)`$ より下の符号を $`[0, L(\lambda''+\theta))`$ の上へ移す。
  定数が無ければ $`R''_b`$ はどの添字も 1 つずらすだけ。細かい点：単調性についての 1 つの注意は向きが逆。帰納法でその段階は閉じる (m3)。
- **$`\theta`$ より下のどの符号のつなぎ**（FRAG のもとで証明済み）。$`[\Omega_1, \theta)`$ のどの符号（たとえば $`\psi_{\Omega_2}(0)`$、$`\Phi_\Omega`$、$`\varepsilon_{\Phi_\Omega+1}`$、$`\psi_{\Omega_2}(\Omega_3)`$）の
  つなぎでの留めも、つなぎでの $`n`$ 項の項のちょうどの基の取り替えを、その一般の形で使う。遠い運び、留め、頂上の補題、長いやり直しの一歩、しきい値 $`\theta`$ のまたぎの補題がそこから出る。
  細かい点：端の点 $`L(\lambda''+\theta)`$ は覆われない（そのつなぎの符号は $`\theta`$ そのもの）。あとのどの段階も使わないので、補題はそれより下の点に限る (m4)。ちょうどの基の取り替えは一般の形で
  引くこと (m5)。
- **EXACT-GS⁺**（FRAG 無しで証明済み）：$`n`$ 項の道具を使わない、$`\varepsilon_{\Phi+1}`$ より下の形のちょうどの基の取り替え。下の控えの $`Z^{\mathrm{E}}`$ を支える。
- **定理 ENUM-REACH″$`^\theta`$**（移しで証明済み、FRAG のもと）：$`Z^\theta`$ より下で符号 $`c''`$ を持つ段 3 のどのやり直し $`b = L(\lambda'')`$ でも $`r(b) = k''_b(o_b(c''))`$ で、段
  $`\zeta \ge \Omega_2^2`$ の符号なら $`r(b) \lt L(\lambda''+1+R''_b(\zeta)+\omega^2) \lt L(\lambda''+\theta)`$ でもある。$`Z^\theta`$ より下でまたがれるやり直しはどれも短い。例：
  $`N = L(\theta'_2\cdot\psi_{\Omega_3}(0)+\psi_{\Omega_2}(0))`$ で $`r(Z^{\mathrm{V}}) = \delta''_1(N) + \Gamma_{N+1}`$、$`N = L(\theta'_2\cdot\Phi_2+\Phi_\Omega)`$ で $`r(Z^\Phi) = \delta''_1(N) + \Phi^N`$。
  値 $`r(Z^{\mathrm{V}})`$ は [SHIFT12-ja.md](SHIFT12-ja.md) §3.1 に、$`Z^{\mathrm{V}}`$ より上の届く先を読む証明、つまりその帰納法の範囲の外を読む証明で記録されていた（§1.2 の B-1）。ここでは
  帰納法が $`Z^\theta`$ より下で回るので、この値は今は証明された。$`r(Z^\theta)`$ は未解決。**のちに（48 回目、§2.1）：** $`r(Z^\theta)`$ は証明され、符号 $`\theta`$ のつなぎも証明された (m4)。
- **定理 C$`^{\theta\sharp}`$ と $`[0, Z^\theta]`$ での主張**（移しで証明済み、FRAG のもと）。$`Z^\theta`$ より下の新しい組はどれも、中に新しい組を持たない段 3 の $`\tau''`$-$`\delta''`$ の組で、
  扇の頂点も 3 重の入れ子も無い。$`\zeta \lt \theta_2`$ が正規のどの $`L(\theta'_2\cdot\zeta)`$ も、$`\le_1`$ の前の点を持たず、下のどの点も越えて届かない点。だから $`\beta_0 \gt Z^\theta`$、
  $`T_3^C \gt Z^\theta`$、$`[0, Z^\theta] \subseteq \mathrm{Core}(R_2^C)`$ で、$`Z^\theta`$ はつぶす引数が $`I_\omega`$ より下の InaccPsi の標準形。途中に $`L(\theta'_2\cdot\psi_{\Omega_3}(1))`$、
  $`L(\theta'_2\cdot\psi_{\Omega_3}(\Omega_2))`$、$`L(\theta'_2\cdot\psi_{\Omega_3}(\Omega_4))`$。細かい点：基の点での段階の 1 つの理由は、加法的に主でない乗数では正しくない。結論は成り立つ (m6)。
  $`Z^\theta`$ での $`R_2^S`$ の側は条件つき（数えない）。
- **入力の少ない 3 つの部分**は分けて記録する：$`(Z^{\mathrm{V}}, Z^\Phi]`$ は $`\Gamma`$ の原子 $`\psi_{\Omega_3}(\beta)`$ の層だけを使い、$`(Z^\Phi, Z^{\mathrm{E}}]`$ は EXACT-GS⁺ も、
  $`(Z^{\mathrm{E}}, Z^\theta]`$ は $`n`$ 項の道具も使う。ここで

```math
Z^\Phi = L(\theta'_2\cdot\Phi_2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+\Phi_2}),\qquad Z^{\mathrm{E}} = L(\theta'_2\cdot\varepsilon_{\Phi_2+1}) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+\varepsilon_{\Phi_2+1}}).
```

- **鋭い形の $`Z^\theta`$ より下の CAP-0″**。$`Z^\theta`$ より下では段 3 の長いやり直しはまたがれない（証明済み、FRAG のもと）。
- **最初の長いまたぎへ**（FRAG 無しで証明済み）：$`[\theta_2, \Omega_\omega)`$ の定数の無い乗数について、読み READ″（READ を 1 段上げたもの、[SHIFT4-ja.md](SHIFT4-ja.md) §2.2）と、その補題
  PLATEAU″-3、ALIGN″、HN″、MONO″。これで $`R''(\theta'_3\cdot\omega^2) = G''(\omega^2)`$。**LONG-FIRST″**（含意として証明済み）：$`\theta'_3\cdot\omega^2`$ までの正規な乗数の読みが $`1 + R''`$ なら
  （予想 THETA″$`^{\mathrm{READ}}`$）、またがれる段 3 の最初の長いやり直しは $`L(\lambda''+G''(\omega^2))`$ で、それは符号 $`G''(\theta'_3\cdot\omega^2)`$ で起こる。査読者は、そこで使う正規性の事実の
  1 行の証明を書いた (m7)。
- **$`Z^\theta`$ より先**（数えない）：$`[\theta, P')`$ の符号のつなぎでの留めは未解決（つなぎの点がつなぎの区間の外にあるので、相対的な遠い留めを 1 段上げたものが要る）。予想：主張は
  $`L(\theta'_2\cdot\theta'_2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2\cdot 2})`$ まで続く。

### 1.2 $`R_2^S`$ で $`[0, Z^{\mathrm{V}})`$、CAP$`^{\mathrm{WW}}`$、基 $`Z^{\mathrm{V}}`$ で蓋だけを読む帰納法

言葉は [SHIFT12-ja.md](SHIFT12-ja.md) §2.2 のもの。$`\lambda_{\mathrm{WW}}`$、$`\lambda_{\mathrm{V}}`$ は $`Z^{\mathrm{WW}}`$、$`Z^{\mathrm{V}}`$ の添字。

- **CAP$`^{\mathrm{WW}}`$**（証明済み、FRAG のもと。[SHIFT12-ja.md](SHIFT12-ja.md) §3.1 の ENUM-REACH″$`^{\mathrm{V}}`$ の例で、その帰納法は $`Z^{\mathrm{V}}`$ より下で回るので $`Z^{\mathrm{WW}}`$ の
  窓を覆う）：$`N = L(\theta'_2\cdot\Omega_2^2+\Omega_1^2)`$ で $`r(Z^{\mathrm{WW}}) = \delta''_1(N) + N\cdot 2`$。$`k \ge 1`$ のどの $`b = L(\lambda_{\mathrm{WW}} + G''(\omega^2)\cdot k)`$ でも
  $`r(b) = \delta''_1(R''_1(b)) + 1`$。そして $`r(Z^{\mathrm{WWG}}) = \delta''_1(R''_1(b)) + 2`$。
- **$`R_2^S`$ での主張**（証明済み、FRAG のもと）：$`[0, Z^{\mathrm{WWG}})`$ で（S-COND$`^{\mathrm{WW}}`$ と CAP$`^{\mathrm{WW}}`$。$`\Omega_2^2`$ より下の読みと和によるつなぎだけに頼る）、
  $`[0, L(\theta'_2\cdot\Omega_2^\omega))`$ で（S-FOLLOW。$`\Omega_2^\omega`$ より下の読みにも頼るが、つなぎは和によるものだけ）、$`[0, Z^{\mathrm{V}})`$ で（S-FOLLOW。ヴェブレンの符号のつなぎにも頼る）。
  $`Z^{\mathrm{V}}`$ より下で Carlson の判定が成り立つ。[SHIFT12-ja.md](SHIFT12-ja.md) の §3.2 とあわせ、$`[0, Z^{\mathrm{WW}})`$ には 2 つの証明がある（査読 2 回）。細かい点：1 つ目の部分の 1 つの
  段階が、ヴェブレンの符号のつなぎに頼る $`\beta_0 \gt Z^{\mathrm{V}}`$ を引いている。そこは $`\beta_0 \gt Z^{\mathrm{WWG}}`$ で足りる (m1)。
- **$`(Z^{\mathrm{WW}}, Z^{\mathrm{V}})`$ の基の点**（証明済み）：BASE-TEST″$`^{\mathrm{V}}`$、NEXT-BASE″$`^{\mathrm{V}}`$ と、それぞれの基の点の届く先、その蓋、次の $`\tau''`$ の点、次の基の点の表。
  1 つの補題の「最初の」は今は証明された。細かい点：引いた有限性の補題の基を名指すこと (m2)。1 つの段階で $`\lambda'' \ge \mu''+\omega^2`$ を書くこと (m3)。
- **基 $`Z^{\mathrm{V}}`$ で蓋だけを読む帰納法**（移しで証明済み、FRAG のもと）：$`\beta_0 \gt Z^{\mathrm{VG}}`$、$`T_3^C \gt Z^{\mathrm{VG}}`$、$`R_2^C`$ で $`[0, Z^{\mathrm{VG}}]`$ での主張。
  $`r(Z^{\mathrm{V}})`$ の値は読まない。§1.1 とあわせ、$`(Z^{\mathrm{V}}, Z^{\mathrm{VG}}]`$ には 2 つの証明がある。基 $`L(\theta'_2\cdot\Omega_2^\omega)`$ だけ（和によるつなぎだけ）でも、同じ方法で
  $`\beta_0 \gt L(\theta'_2\cdot\Omega_2^\omega + \omega^{G''(\omega^2)+1})`$ が出る。
- **証明されていない（進行を止める点 B-1）：** $`R_2^S`$ で $`[0, L(\lambda_{\mathrm{V}} + G''(\omega^2)))`$ での主張と $`Z^{\mathrm{V}} \in \mathrm{Core}(R_2^S)`$。どちらも
  $`N_{\mathrm{V}} = L(\lambda_{\mathrm{V}} + \psi_{\Omega_2}(0))`$ で $`r(Z^{\mathrm{V}}) \lt R''_1(N_{\mathrm{V}})`$ が要る。論文は $`r(Z^{\mathrm{V}})`$ を [SHIFT12-ja.md](SHIFT12-ja.md) §3.1 から取ったが、その証明は
  $`N_{\mathrm{V}} \gt Z^{\mathrm{V}}`$ のちょうどの届く先を読み、それはその帰納法の範囲の外。だからその値はそこでは条件つき。§1.1 の ENUM-REACH″$`^\theta`$ がその値を証明するので段階は出るはずだが、
  この組み合わせは査読されていないので数えない。$`Z^{\mathrm{V}}`$ より上の符号 $`G''(\omega^2)`$ のやり直しの届く先（CAP$`^{\mathrm{V}}`$ (ii)）は予想。細かい点：同じ入力が $`r(Z^{\mathrm{V}})`$ も
  止めることを未解決の一覧に書く (m4)。見出しの行を条件つきとする (m5)。**のちに（48 回目、§2.2）：** B-1 は閉じ、CAP$`^{\mathrm{V}}`$ は証明され、
  $`R_2^S`$ での主張は $`[0, Z^\theta)`$ で成り立つ。

### 1.3 Lean、段階 8：$`\nu_C`$ はやり直し、$`\Lambda_{\varepsilon\cdot\omega}`$ までのやり直しのブロック、どの段でもの LIFT-0 と O$`^C`$

ここで $`\varepsilon = \varepsilon_{\rho+1}`$（そのやり直しでの値）、$`\Lambda_{\varepsilon\cdot\omega}`$ は、その下でどの $`j \lt \omega`$ でも $`\varepsilon_{x+1}\cdot j`$ が共終に実現される最小のやり直しの添字。
$`k`$ 重の入れ子とは $`a_i \le_2 b_i`$ となる $`a_0 \lt \dots \lt a_{k-1} \lt b_{k-1} \lt \dots \lt b_0`$ で、$`T_k`$ は $`k`$ 重の入れ子の頂上 $`b_0`$ の最小のもの。

- **ファイル。** [R2/](R2/) の新しい 8 個のモジュール（NuRst、EpsM、BlkGen、ORecM、LamVal、NestK、CitedNest、LiftK）。CitedNest に **新しい公理が 1 つ**：Carlson 2009 の Lemma 15.11 と
  Thm 14.10 (1) を、$`k`$ 個の入れ子の組の型について、「どの $`k`$ でも $`k`$ 重の入れ子がある」として使う（`C09_nestk`）。これで公理は 7 個のファイルに 52 個。この段階の定理はそのうち
  51 個を使う。リポジトリでは BlkGen の 9 個の名前に接尾辞 `Gen` をつけた（たとえば `OffSpecGen`、`blk_genGen`）。BlkG に同じ名前がすでにあるため。ライブラリ全体が作られ（緑、`sorry` 無し）、
  どの Cited\* ファイルも自由な変数を禁じて作られ、自由な変数を持つ見本の公理は失敗する。詳しくは [LEAN-ja.md](LEAN-ja.md)。**のちに（48 回目、§2.3）：** `C09_nest` は定理になり、
  CitedNest は消した（6 つのファイルに 51 個の公理）。
- **$`\nu_C`$ はやり直し**（`nuC_restart`）。$`\mathrm{lh}(\rho_L) = \nu_C`$ と $`U_2 = \mathrm{Pred}_1(\rho_L) \cup \{\rho_L, \nu_C\}`$（`U2_shape`、段階 7 の監査の m3）も。新しい公理無し。
- **$`\Lambda_{\varepsilon\cdot\omega}`$ までの BLK$`^O`$**（`blkM`、`coreM`）。項 $`\varepsilon_{x+1}\cdot n + t`$ の EXACT、IMG、RS、自分の RS を持つどの項の関数でものブロックの定理、大きくした項の
  集合の上の再帰的なずれ。$`B \le \Lambda_{\varepsilon\cdot\omega}`$ のどのやり直しの添字でも、ちょうどの届く先と CORE-C つきで BLK$`^O`$ の (i)–(iii) が成り立ち、$`\Lambda_{\varepsilon\cdot\omega} \lt \Omega_1`$。
  新しい公理無し。
- **最前線でのずれ**（`lam_values`）：$`\Lambda_\varepsilon`$ で $`\varepsilon+1`$、$`\Lambda_{\varepsilon+1}`$ で $`\varepsilon+2`$、$`\Lambda_{\varepsilon\cdot 2}`$ で $`\varepsilon\cdot 2+1`$、$`\Lambda_{\varepsilon\cdot\omega}`$ で
  $`\varepsilon\cdot\omega`$。そして $`\Lambda_\varepsilon \lt \Lambda_{\varepsilon+1} \lt \Lambda_{\varepsilon\cdot 2} \lt \Lambda_{\varepsilon\cdot\omega} \lt \Omega_1`$。段階 7 のずれは、ちょうど $`\Lambda_{\varepsilon\cdot 2}`$ で届く先で
  なくなる。InaccPsi の名前 $`\Lambda_{\varepsilon+1} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+E+2})`$、$`\Lambda_{\varepsilon\cdot 2} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+E\cdot 2+1})`$、
  $`\Lambda_{\varepsilon\cdot\omega} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+E\cdot\omega})`$（$`E = \varepsilon_{\Omega_1+1}`$）は紙の上で導いただけ：予想（監査の n4）。
- **標準でない最初の組の場所**（`nuC_bound`）：$`\upsilon_{\Lambda_{\varepsilon\cdot\omega}} \le \rho_L \lt \nu_C \lt \Omega_1`$。$`\nu_C`$ の記法による上界はまだ無い。
- **$`k`$ 重の入れ子、どの段でもの LIFT-0 と O$`^C`$**（NestK、LiftK）。与えられた $`k`$ 重の入れ子について、新しい公理無しで：NEST-UP、$`T_k \lt \Omega_1`$、$`T_k`$ での CAP、
  $`[0, T_k] \subseteq \mathrm{Core}(R_2^C)`$、段 $`k`$ での LIFT-0（組、形、届く先、隙間の項と $`T_{k-1} \lt s_k`$）、段 $`k`$ での定理 O$`^C`$。使うのは Carlson 2009 の 3 つの公理だけで、Wilken の
  論文の公理は使わない。`C09_nestk` があれば、これらはどの $`k`$ でも成り立ち（`liftK`）、$`T_1 \lt T_2 \lt T_3 \lt \dots \lt \Omega_1`$、$`T_2 = \nu_C`$。段 2 では、これは O$`^C`$ を 39 個でなく 3 個の
  公理からもう一度証明する。
- **監査** はまとめを作り直して走らせ（緑、`sorry` 無し）、116 個の定理すべての公理を書き出した。致命的な点も進行を止める点も無い。`C09_nestk` は忠実。私たちの段階（入れ子の構造が型で
  あること、Carlson 2009 の Def 5.6 の 1〜7）は 1 項ずつ確かめた。定義（入れ子、$`T_k`$、大きくしたずれ、$`\Lambda_{\varepsilon\cdot\omega}`$）は正しい。細かい点：`liftK_two` は新しい公理を使わない (n1)。
  段階 7 の公理 `C09_nest` は `C09_nestk` の $`k = 2`$ の場合 (n2、今は LiftK の説明の行に書いた)。LiftK の説明の 1 行はこのページ群の記号で、Lean の命題ではない (n3、今はそこに書いた)。
  $`\Lambda_{\varepsilon+1}`$、$`\Lambda_{\varepsilon\cdot 2}`$、$`\Lambda_{\varepsilon\cdot\omega}`$ の名前は予想のまま (n4)。

### 1.4 47 回目のあとの状態

- **$`R_2^C`$ での Wilken の主張**：両方の半分が FRAG 無しで $`[0, X_4]`$ で、**FRAG のもとで $`[0, Z^\theta]`$ で** 成り立つ（査読 1 回、§1.1。部分 $`(Z^{\mathrm{V}}, Z^\Phi]`$、
  $`(Z^\Phi, Z^{\mathrm{E}}]`$、$`(Z^{\mathrm{E}}, Z^\theta]`$ はこの順に多くの入力に頼る）。$`(Z^\Lambda, Z^{\mathrm{LG}}]`$、$`(Z^{\mathrm{FP}}, Z^{\mathrm{FPG}}]`$、$`(Z^{\mathrm{W}}, Z^{\mathrm{WG}}]`$、
  $`(Z^{\mathrm{WW}}, Z^{\mathrm{WWG}}]`$、$`(Z^{\mathrm{V}}, Z^{\mathrm{VG}}]`$ は 2 つの証明（査読 2 回）。$`Z^\theta`$ より上：証明されていない。
- **$`R_2^S`$ での Wilken の主張**：$`[0, \upsilon_{\omega^3}]`$ で、そして FRAG のもとで **$`[0, Z^{\mathrm{V}})`$ で**（査読 1 回、§1.2）。$`[0, Z^{\mathrm{WW}})`$ は 2 つの証明（査読 2 回）。
  FRAG のもとで $`\beta_0 \gt Z^\theta`$。(E) は未解決で、$`\beta_0`$ の場所は分からない。
- **届く先**（FRAG のもと）：段 3 では $`Z^\theta`$ より下のどのやり直しでも $`r(b) = k''_b(o_b(c''))`$。$`r(Z^{\mathrm{WW}})`$、$`r(Z^{\mathrm{V}})`$、$`r(Z^\Phi)`$ は §1.1、§1.2 のとおり。
  $`r(Z^\theta)`$ は未解決。
- **LOW：FRAG のもとで偽**（[SHIFT11-ja.md](SHIFT11-ja.md) §1.1、査読 1 回）。この回は触れていない。**$`\nu_3`$：証明されていない**。CAP-0″ は $`Z^\theta`$ より下で成り立つ。
- **Lean**：[SHIFT12-ja.md](SHIFT12-ja.md) §3.4 のものに加えて、今は $`\nu_C`$ はやり直し、$`\Lambda_{\varepsilon\cdot\omega}`$ までの BLK$`^O`$ と CORE-C、$`\upsilon_{\Lambda_{\varepsilon\cdot\omega}} \le \rho_L`$、
  どの段でもの LIFT-0 と O$`^C`$（§1.3）。
- $`\theta_0`$ より下の下からの評価の計画：この回は扱っていない（$`\iota(\mathrm{CH}_5) \ge \psi_{\Omega_1}(S_*)`$。$`S_*`$ より先は予想 LEX-SELF）。SRO より下の段階：変化なし（3,166 個の見本の
  行列すべてでどの $`n`$ でも済み。SRO より下のすべての標準の行列についての一般の主張だけが未解決）。

### 1.5 47 回目の確かめ

どの実行も 60 秒未満。どれも証明ではない。

- §1.1。著者：名前、$`L`$ の定義域、正規性（400 個の乗数）、読み（16,770 組と 19,460 組での順序）、段、値、定数の無い読み（27,028 組）の 12 の確かめ、失敗 0。査読者：著者の範囲より
  上の 4 つの基での 219 個の頭の部分を持つ 440 個のずれ、$`\psi_{\Omega_3}`$ と $`\psi_{\Omega_4}`$ の原子を持つ 260 個の乗数、覆いの補題の 1,541 個の符号、失敗 0。
- §1.2。著者：蓋、基の点の表、$`Z^{\mathrm{V}}`$ より上の符号についての 4 回の実行、失敗 0（2 つ目の最初の実行は、著者自身のスクリプトで間違った蓋を使っていた。証明の文は影響を
  受けない）。査読者は探しを走らせていない：進行を止める点は帰納法の範囲についてのもの。
- §1.3。Lean：8 個のモジュールをそれぞれ単独で、そして全部まとめて、緑。終わりに偽の主張を足すと失敗する。監査が自分で作った、116 個の定理すべての公理つきのまとめも緑。
  リポジトリでのライブラリ全体の build は緑で、`sorry` 無し。7 個の Cited\* ファイルすべてが自由な変数を禁じて作られ、見本は失敗する。

### 1.6 未解決

- $`Z^\theta`$ より上：$`[\theta, P')`$ の符号のつなぎでの留め（相対的な遠い留めを 1 段上げたもの。予想：$`L(\theta'_2\cdot\theta'_2)`$ まで）、組に $`\Omega_\omega`$ を含む読み、予想
  THETA″$`^{\mathrm{READ}}`$、符号 $`G''(\theta'_3\cdot\omega^2)`$ からの段 3 の長いやり直しのまたぎ。$`r(Z^\theta)`$。そして $`L(\Omega_\omega)`$ までの CAP-0″、CAP-1″、段 4 の LONG-CLASS、
  (H2$`^{\mathrm{cr}}`$)、1 つ上の LEFT⁺、(H3)、NU-CT$`_3`$、$`\nu_3`$。
- FRAG のもとで $`R_2^C`$ で $`Z^\theta`$ より上の主張（FRAG 無しなら $`X_4`$ より上）、$`R_2^S`$ で $`Z^{\mathrm{V}}`$ より上の主張（§1.1 の $`r(Z^{\mathrm{V}})`$ で $`Z^{\mathrm{V}}`$ を越える段階は
  査読が要る。そのあと CAP$`^{\mathrm{V}}`$ (ii)、$`Z^{\mathrm{V}}`$ より上の符号 $`G''(\omega^2)`$ のやり直しの届く先）。
- Lean、この順に：$`\Lambda_{\varepsilon\cdot\omega}`$ とその先での BLK$`^O`$（項 $`\omega^{\varepsilon+1}`$、そして $`\varepsilon_{x+2}`$ と $`x`$ のヴェブレンの項）。$`\Lambda_\varepsilon`$、$`\Lambda_{\varepsilon+1}`$、
  $`\Lambda_{\varepsilon\cdot 2}`$、$`\Lambda_{\varepsilon\cdot\omega}`$ の InaccPsi の名前。LIFT-0 の残り（届く先についての $`[0, s_k)`$ の閉じ方、隙間での届く先、定理 SH）。$`\nu_C`$ の記法による上界
  （目標 $`L(\omega+1)`$）。$`R_2^S`$ の側。
- $`R_2^S = R_2^C`$：(E)、$`\beta_0`$、FAN-LOAD、$`\kappa_C`$ より上の後続の段での $`\le_1`$ の逆向き。
- $`\iota(\mathrm{CH}_2)`$、$`m_F`$、$`x_F`$、$`f_0`$、$`m_3`$、$`c_0`$ の評価と、$`\iota(\mathrm{CH}_3)`$ の上からの評価。
- 最初の到達不能基数（この回は扱っていない）：$`S_*`$ より先は $`\alpha \ge \Gamma_0`$ の容量（予想 LEX-SELF）か別の道。そして $`\theta_0`$ までの $`\Omega`$ の塔。$`\Theta_1`$ を越える $`\mathrm{CH}_2`$。
  SRO より下のすべての標準の行列での段階。
- 名前：$`R(\Theta_{d\omega})`$。$`\Lambda_{\mathrm{fp}2}`$ と $`\Theta_1`$ の間の正確なずれ。符号で書いた届く先の InaccPsi の式。[COVER-ja.md](COVER-ja.md) §9 の残り。

## 2. 48 回目

論文は 3 本（2026-10）：$`Z^\theta`$ より先の $`[\theta, \Phi^{P'})`$ の符号の論文（§2.1）と、$`Z^{\mathrm{V}}`$ より先の $`R_2^S`$ の側の論文（§2.2）は、どちらも査読 1 回。$`R_2^C`$ の Lean の
9 つ目の段階（§2.3）は、公理と定義を確かめる監査を受けた（証明は Lean が確かめる）。この節の結果は、回数を書いていなければ査読 1 回。段の番号は §1 と同じ。

記号は §1 のもの。また $`\Phi^{P'} = \psi_{\Omega_2}(\Omega_\omega\cdot 2 + \Omega_2)`$ は $`P'`$ より上の最初の $`\Gamma`$ の不動点。乗数 $`\zeta^* = \psi_{\Omega_3}(\Omega_\omega\cdot 2 + \Omega_3)`$ は
$`\Omega_3`$ の下の平らな所の始まり。

**$`R_2^C`$ での最前線は $`L(\Omega_3)`$ に進んだ。** FRAG のもとで、**Wilken の主張は $`R_2^C`$ で $`[0, Z^{\Omega_3}]`$ で成り立つ（両方の半分）**。ここで

```math
Z^{\Omega_3} = L(\Omega_3) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \Omega_3)
```

で、$`\beta_0 \gt Z^{\Omega_3}`$ と $`T_3^C \gt Z^{\Omega_3}`$ も成り立つ（§2.1）。前の回に予想した点 $`L(\theta'_2\cdot\theta'_2)`$ は越えた。**$`R_2^S`$ では主張は今は $`[0, Z^\theta)`$ で
成り立つ**（FRAG のもと）。§1.2 の進行を止める点 B-1 は閉じた（§2.2）。$`Z^\theta`$ から

```math
Z^{\theta\mathrm{G}} = L(\theta'_2\cdot\theta_2 + \omega^{G''(\omega^2)+1}) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+\theta_2} + \omega^{G''(\omega^2)+1})
```

への段階には、蓋だけを読む 2 つ目の証明がある（§2.2）ので、**査読 2 回**。Lean では：$`\Lambda_{\varepsilon_{x+2}}`$ までの定理 BLK$`^O`$、LIFT-0 の残り、定理 SH のブロックの形、そして公理が
1 個減った（§2.3）。

引く論文：§2.1 と §2.2 は査読済みの段階を通してだけ：[W07a] と [W07b]（L.2.1）、Carlson 2009（L.5.5、L.5.7 (3)）、Wilken 2020（Prop 21.6）、[CW12b]（L.7.5）、[C11]（LOC-ISO を通して）。
§2.3 は Carlson 2009（Lemma 15.11、Thm 14.10 (1)、Cor 15.15、Def 5.6）と、前の段階の公理を通してだけの [W07a]（Lemma 4.2、4.3、Def 3.28）と [W07b]（Thm 2.2、Cor 5.10）。
どれも Wilken, JSL 72 (2007)、Carlson, AML 38 (1999)、Wilken, AML 45 (2006) を使わない。

47 回目の査読の細かい点は直した：§1.1 の査読の m1–m7 は §2.1 の論文で（m4：§1.1 の補題は端点 $`L(\lambda''+\theta)`$ より下の点に制限し、符号 $`\theta`$ のつなぎは今は下で証明された。
m7 は証明された）、§1.2 の査読の m1–m5 は §2.2 の論文で、§1.3 の監査の n1–n4 は Lean で（§2.3）。

### 2.1 $`\Phi^{P'}`$ より下の符号と、$`R_2^C`$ での $`[0, Z^{\Omega_3}]`$ の主張

- **SHIFT$`^K`$**（証明済み、FRAG 無し）。どの $`\Omega_k`$ も $`\Omega_{k-1}`$ に下げ（$`2 \le k \lt \omega`$、つぶしも一緒に。$`\Omega_\omega`$ はそのまま）、各定数 $`c`$（$`\Omega_2`$ より下の
  極大な部分項）を $`f(c)`$ に替える。$`f`$ は可算な標準形の上への、どんな狭義増加の写像でもよい。これは標準形と順序を保ち、逆にたどれる。InaccPsi の比べ方から直接読み取れ、
  §1.1 の $`n`$ 項の形を符号の側で置きかえる。細かい点：$`\Omega`$ やつぶしの添字は定数に入れない。そこでは段そのものが項だから (m1)。査読者は乱数の写像 $`f`$ でも試した（144,540 組、
  失敗 0）。
- **引数の上界**（証明済み、FRAG 無し）。乗数 $`\zeta \lt \zeta^*`$ では、定数の外のどのつぶしも引数が $`\lt \Omega_\omega\cdot 2+\zeta`$。ずれ $`u \lt \Phi^{P'}`$ では、可算な定数の外のどの
  非可算なつぶしも引数が $`\lt \Omega_\omega\cdot 2+u`$。よってどの $`u \lt \Phi^{P'}`$ とどの $`\lambda''`$ でも：$`\lambda''+u`$ が $`L`$ の定義域にあるのは、$`u`$ の可算な定数がすべて
  $`L(\lambda''+u)`$ より下のときに限る。$`\Phi^{P'}`$ より下では、ずれは基によらない。基によるのは $`\Phi^{P'}`$ から（$`\theta'_2`$ からではない）。
- **空の平らな所**（証明済み、FRAG 無し）。$`[\zeta^*, \Omega_3)`$ には $`L`$ の添字が無く、$`\Omega_3`$ より下のどの正規な乗数も $`\zeta^*`$ より下で、$`L(\Omega_3)`$ は $`e \lt \Omega_3`$ の
  $`L(e)`$ の上限。
- **THETA″$`^{\Omega_3}`$**（証明済み、FRAG 無し）。段 3 のどのやり直し $`b = L(\lambda'')`$ でも、$`\zeta \mapsto 1 + R''_b(\zeta)`$（$`R''_b`$ は $`f = o_b`$ での SHIFT$`^K`$）は、$`o_b`$ の
  定義域にある $`\Omega_3`$ より下の正規な乗数から、$`\Phi^{P'}`$ より下のずれの始めの部分の上への順序同型で、$`o_b(G''(\zeta)) = L(\lambda''+1+R''_b(\zeta))`$。よって読み
  THETA″$`^{\mathrm{READ}}`$ は定数つきで $`[\theta_2, \Omega_3)`$ で成り立つ。定数が無ければ：$`\theta_2 \mapsto \theta`$、$`\theta'_2 \mapsto P'`$、上限は $`\Phi^{P'}`$。
- **$`[\theta, P')`$ のどの符号のつなぎも**（移しで証明済み、FRAG のもと）。そういうつなぎの点はつなぎの区間の外にある。その留めは、相対的な遠い留め（RELPIN）を 1 段上げたもので、
  根の隙間から遠い相対的な基で、勝手な像での H-RC と、一般の形の正確な基の取りかえを使う。符号 $`\theta`$ そのものは §1.1 で開いたままの端点。細かい点：$`R`$ が無限のとき、ある
  ずれは $`2+R`$ でなく $`(1+R)+1`$ でなければならない (m2)。
- **$`[P', \Phi^{P'})`$ のどの符号のつなぎも**（移しで証明済み、FRAG のもと）：つなぎでの L-PIN、次の $`L`$ の点で勝手な $`L`$ の点を像とする H-RC、$`\Gamma`$ の項の正確な基の取りかえ、
  単位についての単調性。細かい点：留めは下の定数の $`+`$ とカントール標準形の部分についての閉包の全部に要る (m3)。つなぎより下の可算な定数はそのまま留まる (m4)。
- **定理 ENUM-REACH″$`^{\Omega_3}`$**（移しで証明済み、FRAG のもと）：$`Z^{\Omega_3}`$ より下の段 3 のどのやり直し $`b = L(\lambda'')`$ でも $`r(b) = k''_b(o_b(c''))`$。段 $`\zeta \ge \Omega_2^2`$ の
  符号では $`r(b) \lt L(\lambda''+1+R''_b(\zeta)+\omega^2) \lt L(\lambda''+\Phi^{P'})`$ も。$`Z^{\Omega_3}`$ より下でまたがれるやり直しはどれも短い。
- **$`Z^\theta`$ での届く先**（証明済み、ENUM-REACH″$`^{\Omega_3}`$ の場合）。$`N = L(\theta'_2\cdot\theta_2+\theta)`$ と、$`N`$ の区間の上の最初の点
  $`N^\infty = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+\theta_2} + \omega^{P'+\theta} + \theta)`$ で：$`r(Z^\theta) = r(N) = \delta''_1(N) + N^\infty`$。また
  $`N^\theta = L(\theta'_2\cdot\theta_2+\psi_{\Omega_2}(0))`$ で $`r(N^\theta) = \delta''_1(N^\theta) + \Gamma_{N^\theta+1}`$、$`N' = L(\theta'_2\cdot\theta'_2+P')`$ で
  $`r(Z^{\theta'}) = \delta''_1(N') + L(\theta'_2\cdot\theta'_2+P'+1)`$。よって §1.1 で未解決だった $`r(Z^\theta)`$ は証明された。細かい点：ある値は値の表からでなく連続性で読む (m5)。言い方 (m6)。
- **定理 C$`^{\Omega_3\sharp}`$ と $`[0, Z^{\Omega_3}]`$ での主張**（移しで証明済み、FRAG のもと）。$`Z^{\Omega_3}`$ より下の新しい組はどれも段 3 の $`\tau''`$-$`\delta''`$ の組で、中に新しい組を
  持たない。扇の頂点も 3 重の入れ子も無く、どの $`L(\theta'_2\cdot\zeta)`$（$`\zeta`$ は正規）も $`Z^{\Omega_3}`$ そのものも $`\le_1`$ で前にある点を持たない。よって $`\beta_0 \gt Z^{\Omega_3}`$、
  $`T_3^C \gt Z^{\Omega_3}`$、$`[0, Z^{\Omega_3}] \subseteq \mathrm{Core}(R_2^C)`$ で、$`Z^{\Omega_3}`$ はつぶしの引数が $`I_\omega`$ より下の InaccPsi の標準形。$`Z^{\Omega_3}`$ での $`R_2^S`$ の側は
  主張しない。
- **入力の少ない部分**（証明済み、FRAG のもと）：$`[P', \Phi^{P'})`$ の符号のつなぎ無しで、主張は §1.1 で予想した点まで成り立つ。

```math
Z^{\theta'} = L(\theta'_2\cdot\theta'_2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2\cdot 2}).
```

- **$`Z^{\Omega_3}`$ より下の CAP-0″**、そして $`Z^{\Omega_3}`$ より下では段 3 の長いやり直しはまたがれない（証明済み、FRAG のもと）。
- **$`Z^{\Omega_3}`$ より先**（数えない）。$`\Omega_3`$ から先の読みは READ″ で、ずらしではない。$`[\Omega_3, \theta'_3\cdot\omega^2]`$ での THETA″$`^{\mathrm{READ}}`$ は予想。4 つの補題が
  足りない。どれも段 1 の査読済みの補題を 1 段上げたもの（非可算な定数つきの定義域の補題、平らな所と上への補題、定数つきの余白、天井）。$`[\Phi^{P'}, G''(\omega^2))`$ の符号のつなぎは
  未解決：$`n`$ 番目の $`L`$ の点での L-PIN と、勝手な像でいくつもの隙間を通る遠い留めが要る。予想：次の最前線は最初の長いまたぎで、$`L(\theta'_2\cdot\theta'_3\cdot\omega^2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_3+2})`$。
  §1.1 の LONG-FIRST″ は今は確かめただけの入力を持たない。

### 2.2 $`R_2^S`$ での $`[0, Z^\theta)`$、CAP$`^{\mathrm{V}}`$、$`Z^\theta`$ での蓋だけの帰納法

言葉は §1.2 のもの。$`\lambda_{\mathrm{V}}`$ は $`Z^{\mathrm{V}}`$ の添字で、$`N_{\mathrm{V}} = L(\lambda_{\mathrm{V}} + \psi_{\Omega_2}(0))`$。

- **CAP$`^{\mathrm{V}}`$**（証明済み、FRAG のもと。§1.1 の ENUM-REACH″$`^\theta`$ の場合で、その帰納法は $`Z^\theta`$ より下を走るので、$`N_{\mathrm{V}}`$ と $`Z^{\mathrm{V}}`$ の窓の全部を覆う）：
  $`r(Z^{\mathrm{V}}) = r(N_{\mathrm{V}}) = \delta''_1(N_{\mathrm{V}}) + \Gamma_{N_{\mathrm{V}}+1}`$。どの $`b = L(\lambda_{\mathrm{V}} + G''(\omega^2)\cdot k)`$（$`k \ge 1`$）も $`r(b) = \delta''_1(R''_1(b)) + 1`$。
  $`r(Z^{\mathrm{VG}}) = \delta''_1(R''_1(b)) + 2`$。**これで §1.2 の B-1 は閉じた**：この段階が読む届く先は、今はどれも帰納法の範囲の中にある。細かい点：入力のいちばん少ない名札の入力の
  一覧に、$`Z^{\mathrm{V}}`$ での §1.1 のまたぎの補題を足すこと (m1)。
- **$`R_2^S`$ での主張**（証明済み、FRAG のもと）：$`[0, Z^{\mathrm{VG}})`$ で、$`Z^{\mathrm{V}} \in \mathrm{Core}(R_2^S)`$ つき（S-COND$`^{\mathrm{V}}`$ と CAP$`^{\mathrm{V}}`$）。そして $`[0, Z^\theta)`$ で
  （§1.1 の基の点での S-FOLLOW）。$`Z^\theta`$ より下で Carlson の判定が成り立つ。入力を減らせば $`[0, Z^\Phi)`$ と $`[0, Z^{\mathrm{E}})`$ で。§1.2 と合わせて、$`[0, Z^{\mathrm{V}})`$ は 2 つの
  証明（査読 2 回）。
- **$`(Z^{\mathrm{V}}, Z^\theta)`$ の基の点**（証明済み）：BASE-TEST″$`^\theta`$、NEXT-BASE″$`^\theta`$、基を名指した FIRST-LL、そして各基の点の届く先、蓋、次の $`\tau''`$ の点、次の基の点の表。
  査読者は 6 行を手で計算し直した。細かい点：言い方 (m2、m4、m5) と 2 つの引用 (m3、m6)。
- **基 $`Z^\theta`$ での蓋だけの帰納法**（移しで証明済み、FRAG のもと）：$`\beta_0 \gt Z^{\theta\mathrm{G}}`$、$`T_3^C \gt Z^{\theta\mathrm{G}}`$、$`R_2^C`$ で $`[0, Z^{\theta\mathrm{G}}]`$ の主張。
  $`r(Z^\theta)`$ の値は読まない。§2.1 と合わせて、$`(Z^\theta, Z^{\theta\mathrm{G}}]`$ は 2 つの証明。入力を減らせば基 $`Z^{\mathrm{E}}`$ と $`Z^\Phi`$ で同じこと。
- **$`Z^\theta`$ より先**（数えない）。S-COND$`^\theta`$（含意として証明済み）は、その窓のやり直しが問題の基より下に届くとき、$`Z^\theta`$ より上の $`R_2^S`$ での主張を与える。これは
  $`r(Z^\theta)`$ が要る。この論文は値を証明した §2.1 無しで書かれ、組み合わせは査読されていない。

### 2.3 Lean、段階 9：$`\Lambda_{\varepsilon_{x+2}}`$ までのやり直しのブロック、LIFT-0 の残り、公理が 1 個減った

ここで $`\varepsilon = \varepsilon_{\rho+1}`$ は問題のやり直し $`\rho`$ でのもので、項の中の $`x`$ は $`\rho`$ を表す：$`\Lambda_{\varepsilon\cdot x}`$、$`\Lambda_{\varepsilon^2}`$、$`\Lambda_{\varepsilon_{x+2}}`$ は、
ずれがそれぞれ $`\varepsilon\cdot\rho = \omega^{\varepsilon+\rho}`$、$`\varepsilon\cdot\varepsilon`$、$`\varepsilon_{\rho+2}`$ になる最小のやり直しの添字。

- **ファイル。** [R2/](R2/) の新しい 9 個のモジュール（NestDef、EpsQ、ORecQ、LiftR、EpsX、ORecX、EpsY、ImgY、ORecY）と、変えた 4 個（CitedCore、NestC、NestK、LiftK）。CitedNest は
  消した。**新しい公理は無く、公理が 1 個減った：** `C09_nest` は今は NestC の定理で、`C09_nestk` の $`k = 2`$ の場合（§1.3 の監査の n2）。`C09_nestk` は CitedCore に移した。今は 6 つの
  ファイルに 51 個の公理で、定理はそのうち 50 個を使う（`le1R_limit` は使わない）。ライブラリ全体の build は緑で `sorry` 無し。どの Cited\* ファイルも自由な変数を禁じて作られ、見本
  （NestDef の import を外した CitedCore）は失敗する。ほかのモジュールと名前はぶつからない。詳しくは [LEAN-ja.md](LEAN-ja.md)。
- **$`\Lambda_{\varepsilon_{x+2}}`$ までの BLK$`^O`$**（EpsQ から ORecY）。原子 $`\omega^{\varepsilon+\beta}`$ の EXACT と IMG を、$`\varepsilon`$ をそれ自身の基として扱って示した。EXACT には
  $`\varepsilon \in T^\rho[\sigma]`$ が要る。Lean はこれを新しい引いた事実からでなく、値から、先頭の部分をたどって下りることで得る（[W07a] Def 3.28）。大きくした項の集まりの上の再帰的な
  ずれで、BLK$`^O`$ の (i)–(iii) はちょうどの届く先と CORE-C つきで、$`\Lambda_{\varepsilon_{x+2}}`$ までのどのやり直しの添字でも（その添字も含めて）成り立つ：
  $`\Lambda = \Lambda_{\varepsilon\cdot\omega}`$、$`\Lambda_{\varepsilon\cdot x}`$、$`\Lambda_{\varepsilon^2}`$、$`\Lambda_{\varepsilon_{x+2}}`$ でそれぞれ $`\mathrm{lh}(\rho_\Lambda) = \delta + \varepsilon\cdot\omega`$、$`\delta + \varepsilon\cdot\rho`$、
  $`\delta + \varepsilon\cdot\varepsilon`$、$`\delta + \varepsilon_{\rho+2}`$。また $`\Lambda_{\varepsilon\cdot\omega} \lt \Lambda_{\varepsilon\cdot x} \lt \Lambda_{\varepsilon^2} \lt \Lambda_{\varepsilon_{x+2}} \lt \Omega_1`$。InaccPsi の名前
  $`\Lambda_{\varepsilon\cdot x} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+E\cdot\Omega_1})`$、$`\Lambda_{\varepsilon^2} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+E^2})`$、
  $`\Lambda_{\varepsilon_{x+2}} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\varepsilon_{\Omega_1+2}})`$（$`E = \varepsilon_{\Omega_1+1}`$）は予想。
- **最初の標準でない組の場所**：$`\Lambda_{\varepsilon_{x+2}} + \omega^2 \le L`$ と $`\upsilon_{\Lambda_{\varepsilon_{x+2}}} \le \rho_L \lt \nu_C \lt \Omega_1`$。$`\nu_C`$ の記法による上界はまだ無い。Lean には
  InaccPsi から $`\upsilon`$ へのつながりが無く、最初のつながり $`\upsilon_1 \le \psi_{\Omega_1}(\Omega_\omega)`$ でさえ、$`T^\tau \cap \Omega_1`$ の順序型についての引いた事実が要る。手もとの
  論文のどれもそれを定理として述べていない。
- **LIFT-0 の残り**（LiftR、どの段 $`k`$ でも）：$`[0, s_k)`$ は届く先について閉じている。$`U_k`$ の隣り合う 2 つの要素の間の点は、上の要素より下に届く。$`U_k`$ の要素 $`u`$ より下の
  点は、$`[u, T_k]`$ のすべてと $`\le_1`$ でも $`\le_2`$ でも同じ関係にある。$`s_k`$ がある。
- **定理 SH のブロックの形**（LiftR）。どの $`\xi`$ でも、$`T_k(\xi)`$ を $`\xi`$ より上の $`k`$ 重の入れ子の最小の上端として：$`\xi`$ より上のブロックの CAP、集合 $`U`$、届く先、隙間、
  O$`^C`$。そして $`\xi \lt T_j`$ なら $`[0, T_{m+1}(\xi)] \subseteq \mathrm{Core}(R_2^C)`$。「$`\lt_2`$ で前にある点がちょうど 1 つ」は $`\xi`$ より上の点の中でだけ証明された。定理 SH の全部は
  未解決（監査の m5）。
- **監査** はまとめを作り直し（同じバイト列）、走らせ（緑、`sorry` 無し）、263 個の定理すべての公理を書き出した。致命的な点も進行を止める点も無い。`C09_nestk` は忠実（Carlson 2009 の
  Def 5.6、Lemma 15.11、Thm 14.10 (1) を読み直した）。[W07a] Lemma 4.2 の新しい使い方はその範囲の中。細かい点：上界 $`\upsilon_{\Lambda_{\varepsilon_{x+2}}+\omega^2} \le \rho_L`$ は 2 つの定理から単調性で
  出るが、1 つの定理ではない (m1)。ページには 6 つのファイルに 51 個の公理と書くこと (m2、ここで済み)。`C09_nest` は名前が引いた事実に見えるが定理 (m3)。記録ではライブラリを
  モジュールごとに作ること (m4、済み)。定理 SH の全部は未解決 (m5)。将来引く事実 $`\vartheta^\tau(\Omega_1) = \varepsilon_{\tau+1}`$ には [W07a] Lemma 4.3 だけでなく数え上げの性質が要る (m6)。
  Lean は、いちばん下の宇宙に到達不能基数の列があることを証明できない (m7、言い方)。

### 2.4 48 回目のあとの状態

- **$`R_2^C`$ での Wilken の主張**：両方の半分が FRAG 無しで $`[0, X_4]`$ で、**FRAG のもとで $`[0, Z^{\Omega_3}]`$ で** 成り立つ（査読 1 回、§2.1。$`[0, Z^{\theta'}]`$ は入力を減らして）。
  $`(Z^\Lambda, Z^{\mathrm{LG}}]`$、$`(Z^{\mathrm{FP}}, Z^{\mathrm{FPG}}]`$、$`(Z^{\mathrm{W}}, Z^{\mathrm{WG}}]`$、$`(Z^{\mathrm{WW}}, Z^{\mathrm{WWG}}]`$、$`(Z^{\mathrm{V}}, Z^{\mathrm{VG}}]`$、$`(Z^\theta, Z^{\theta\mathrm{G}}]`$ は 2 つの
  証明（査読 2 回）。$`Z^{\Omega_3}`$ より上：証明されていない。
- **$`R_2^S`$ での Wilken の主張**：$`[0, \upsilon_{\omega^3}]`$ で、そして FRAG のもとで **$`[0, Z^\theta)`$ で**（査読 1 回、§2.2）。$`[0, Z^{\mathrm{V}})`$ は 2 つの証明（査読 2 回）。
  FRAG のもとで $`\beta_0 \gt Z^{\Omega_3}`$。(E) は未解決で、$`\beta_0`$ の場所は分からない。
- **届く先**（FRAG のもと）：段 3 では $`Z^{\Omega_3}`$ より下のどのやり直しでも $`r(b) = k''_b(o_b(c''))`$。$`r(Z^{\mathrm{V}})`$、$`r(Z^\theta)`$、$`r(N^\theta)`$、$`r(Z^{\theta'})`$ は §2.1、§2.2 のとおり。
- **LOW：FRAG のもとで偽**（[SHIFT11-ja.md](SHIFT11-ja.md) §1.1、査読 1 回）。この回は触れていない。**$`\nu_3`$：証明されていない**。CAP-0″ は $`Z^{\Omega_3}`$ より下で成り立つ。
- **Lean**：§1.4 のものに加えて、今は $`\Lambda_{\varepsilon_{x+2}}`$ までの BLK$`^O`$ と CORE-C、$`\upsilon_{\Lambda_{\varepsilon_{x+2}}} \le \rho_L`$、LIFT-0 の残り、定理 SH のブロックの形、6 つの
  ファイルに 51 個の公理（§2.3）。
- $`\theta_0`$ より下の下からの評価の計画：この回は扱っていない（$`\iota(\mathrm{CH}_5) \ge \psi_{\Omega_1}(S_*)`$。$`S_*`$ より先は予想 LEX-SELF）。SRO より下の段階：変化なし（3,166 個の見本の
  行列すべてでどの $`n`$ でも済み。SRO より下のすべての標準の行列についての一般の主張だけが未解決）。

### 2.5 48 回目の確かめ

どの実行も 60 秒未満。どれも証明ではない。

- §2.1。著者：11 の確かめ（名前。39,800 組と 25,440 組での定数つきのずらし。6 つの基での 260 個と 540 個のずれでの $`L`$ の定義域。300 個の符号での覆いの補題。240 個と 160 個のずれでの
  逆。30 個の添字での空の平らな所。$`Z^\theta`$、$`N^\theta`$、$`Z^{\theta'}`$ での届く先）、失敗 0（途中の実行のいくつかは著者自身のスクリプトの誤りで止まった。証明の文は影響を受けない）。
  査読者：乱数の増加写像での SHIFT$`^K`$ を 144,540 組で、引数の上界を 5,946 個の乗数で、失敗 0。
- §2.2。著者：蓋と基の点の表についての 5 回の実行、失敗 0（ある確かめの最初の実行は、蓋が「以下」の所を狭義で比べた。スクリプトの誤りで、証明の誤りではない）。査読者は探しを
  走らせていない：いちばん弱い段階は帰納法の範囲と名札についてのもの。
- §2.3。Lean：新しいモジュールをそれぞれ単独で、リポジトリに対してと記録のあとの状態で、そして全部まとめて、緑。263 個の定理すべての公理。終わりに偽の主張を足すと失敗する。
  監査自身の実行も緑。リポジトリでのライブラリ全体の build は緑で、`sorry` 無し。6 つの Cited\* ファイルすべてが自由な変数を禁じて作られ、見本は失敗する。

### 2.6 未解決

- $`Z^{\Omega_3}`$ より上：$`[\Omega_3, \theta'_3\cdot\omega^2]`$ での THETA″$`^{\mathrm{READ}}`$（1 段上の 4 つの補題）、$`[\Phi^{P'}, G''(\omega^2))`$ の符号のつなぎ（$`n`$ 番目の $`L`$ の点での L-PIN、
  いくつもの隙間を通る遠い留め）、そして符号 $`G''(\theta'_3\cdot\omega^2)`$ からの段 3 の長いやり直しのまたぎ（予想：次の最前線は $`\psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_3+2})`$）。
  そして $`L(\Omega_\omega)`$ までの CAP-0″、CAP-1″、段 4 の LONG-CLASS、(H2$`^{\mathrm{cr}}`$)、1 つ上の LEFT⁺、(H3)、NU-CT$`_3`$、$`\nu_3`$。
- FRAG のもとで $`R_2^C`$ で $`Z^{\Omega_3}`$ より上の主張（FRAG 無しなら $`X_4`$ より上）、$`R_2^S`$ で $`Z^\theta`$ より上の主張（§2.1 の $`r(Z^\theta)`$ と S-COND$`^\theta`$ の組み合わせは査読が
  要る。そのあと $`(Z^\theta, Z^{\Omega_3}]`$ の基の点）。
- Lean、この順に：$`\Lambda_{\varepsilon_{x+2}}`$ より先の BLK$`^O`$（$`\varepsilon_{x+2}`$ の EXACT には、$`\varepsilon_{\rho+2}`$ しか $`T^\rho[\sigma]`$ にあると分かっていないときに
  $`\varepsilon_{\rho+1} \in T^\rho[\sigma]`$ が要る。引いた事実 $`\vartheta^\tau(\Omega_1) = \varepsilon_{\tau+1}`$ をその正確な場所つきで足せば閉じる）。点 $`\Lambda`$ の InaccPsi の名前。ブロックの形より
  先の定理 SH。$`\nu_C`$ の記法による上界（目標 $`L(\omega+1)`$）。$`R_2^S`$ の側。
- $`R_2^S = R_2^C`$：(E)、$`\beta_0`$、FAN-LOAD、$`\kappa_C`$ より上の後続の段での $`\le_1`$ の逆向き。
- $`\iota(\mathrm{CH}_2)`$、$`m_F`$、$`x_F`$、$`f_0`$、$`m_3`$、$`c_0`$ の評価と、$`\iota(\mathrm{CH}_3)`$ の上からの評価。
- 最初の到達不能基数（この回は扱っていない）：$`S_*`$ より先は $`\alpha \ge \Gamma_0`$ の容量（予想 LEX-SELF）か別の道。そして $`\theta_0`$ までの $`\Omega`$ の塔。$`\Theta_1`$ を越える $`\mathrm{CH}_2`$。
  SRO より下のすべての標準の行列での段階。
- 名前：$`R(\Theta_{d\omega})`$。$`\Lambda_{\mathrm{fp}2}`$ と $`\Theta_1`$ の間の正確なずれ。符号で書いた届く先の InaccPsi の式。[COVER-ja.md](COVER-ja.md) §9 の残り。
