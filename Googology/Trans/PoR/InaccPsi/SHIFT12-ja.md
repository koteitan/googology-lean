[← Back](README-ja.md) | [English](SHIFT12.md) | [Japanese](SHIFT12-ja.md)

# $`R_2^+`$ の 44・45 回目：$`R_2^C`$ で $`Z^{\mathrm{WW}}`$ まで、$`R_2^S`$ で $`Z^{\mathrm{W}}`$ までの主張、$`L_3(\omega)`$ でのブロック、$`R_2^C`$ の $`\Lambda_\varepsilon`$ までのやり直しのブロックを Lean で

このページは [SHIFT11-ja.md](SHIFT11-ja.md) の続き（そこの §3 が 43 回目）。§1 が 44 回目、§2 が 45 回目。状態の言葉は [README-ja.md](README-ja.md) §3 のもの：**証明済み** とは、独立した査読者が、
致命的な点も進行を止める点も無しに証明されていると認めたこと。致命的な点か進行を止める点があるものは **未証明** に挙げる。証明書は再生されたものだけを数える。
査読者が、知られたことか目標そのものの言い直しにすぎないと言った結果は、進みとして数えない。

## 1. 44 回目

論文は 3 本（2026-10）：$`Z^{\mathrm{FP}}`$ より先の段 3 のちょうどの届く先と $`L_3(\omega)`$ でのブロックの論文（§1.1）と、$`Z^\Lambda`$ より先の $`R_2^S`$ の側の論文（§1.2）は、どちらも査読 1 回。
$`R_2^C`$ の Lean の 5 つ目の段階（§1.3）は、公理と定義を確かめる監査を受けた（証明は Lean が確かめる）。この節の結果は、回数を書いていなければ査読 1 回。段の番号は
[SHIFT11-ja.md](SHIFT11-ja.md) §1 と同じ（論文より 1 つ大きい）：やり直し $`L(\lambda'')`$ は段 3 にあり、点 $`L_3(e) = \psi_{\Omega_1}(\Omega_\omega\cdot 3 + P_3\cdot e)`$ は段 4 のやり直し。

**$`R_2^C`$ での最前線は $`Z^{\mathrm{W}}`$ に進んだ。** FRAG のもとで、**Wilken の主張は $`R_2^C`$ で $`[0, Z^{\mathrm{W}}]`$ で成り立つ（両方の半分）**。ここで

```math
Z^{\mathrm{W}} = L(\theta'_2\cdot(\Omega_2+\omega^2)) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+\Omega_2} + \omega^{\theta'_2+2}),\qquad \theta'_2 = \psi_{\Omega_3}(\Omega_\omega\cdot 2),
```

で、$`\beta_0 \gt Z^{\mathrm{W}}`$ と $`T_3^C \gt Z^{\mathrm{W}}`$ も成り立つ（査読 1 回、§1.1）。名前の W は、$`Z^{\mathrm{W}}`$ より下の符号がやり直しの 1 つの窓（§1.1 で定める）の中で読まれることを表す。途中に
$`L(\theta'_2\cdot(\Omega_2+1)) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+\Omega_2} + \theta'_2)`$ がある。$`Z^{\mathrm{FP}}`$ から

```math
Z^{\mathrm{FPG}} = L(\theta'_2\cdot\Omega_2 + \omega^{\hat G''+G''(\omega^2)} + \omega^{G''(\omega^2)+1}) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+\Omega_2} + \omega^{\hat G''+G''(\omega^2)} + \omega^{G''(\omega^2)+1})
```

への段階には、蓋だけを読む 2 つ目の証明がある（§1.2）ので、**査読 2 回**。**$`R_2^S`$ では主張は今は $`[0, Z^{\mathrm{FP}})`$ で成り立つ**（FRAG のもと、査読 1 回、§1.2）。その途中で $`Z^\Lambda`$ の
届く先が分かった。$`\nu_3`$ へ：43 回目の進行を止める点（$`L_3(\omega)`$ でのブロック）は片づき、$`T_3^S = \nu_3`$ は今は名前のついた 3 つの仮定から出る。$`\nu_3`$ そのものは証明されていない。

引く論文：§1.1 と §1.2 は査読済みの段階を通してだけ：[W07b]（L.2.1）、Carlson 2009（Def 5.3、L.5.5、L.5.7 (3)）、Wilken 2020（(21.10)、(21.12)、Prop 21.6、Prop 21.11、Thm 21.13）、
[CW12b]（L.7.5）。§1.2 では [C11] も（LOC-ISO を通して）。§1.3 は [W07a]（Def 3.22、Def 3.28、L.3.30、L.4.2、Def 5.1）と [W07b]（Thm 2.2。主張だけを引く）と、Lean ですでに引いている
事実。どれも Wilken, JSL 72 (2007)、Carlson, AML 38 (1999)、Wilken, AML 45 (2006) を使わない。

43 回目の査読の細かい点は直した：[SHIFT11-ja.md](SHIFT11-ja.md) §3.1 の査読の m1–m7 は §1.1 の論文で（m1 は留めの有限集合を広げた遠い頂上の補題として、移しで証明済み）、そこの §3.2 の査読の
m1–m6 は §1.2 の論文で、そこの §3.3 の監査の n1–n3 は Lean の説明の行で（§1.3）。

### 1.1 $`Z^{\mathrm{W}}`$ までの段 3 のちょうどの届く先、$`R_2^C`$ で $`[0, Z^{\mathrm{W}}]`$ での主張、$`L_3(\omega)`$ でのブロック

記号は [SHIFT11-ja.md](SHIFT11-ja.md) §3.1 のもの：段 3 のやり直し $`b = L(\lambda'')`$ について、$`F''_b = L(\lambda''+\Omega_1)`$、$`o_b`$ は $`b`$ での読み、$`k''_b`$ は $`b`$ に相対的に閉じた点を並べたもの、
$`G''(\zeta) = \psi_{\Omega_2}(\Omega_\omega\cdot 2 + \theta'_2\cdot\zeta)`$、$`\hat G'' = G''(\Omega_2)`$。$`b`$ の **窓** は $`[b, L(\lambda''+\Omega_1+\omega^2))`$。[SHIFT10-ja.md](SHIFT10-ja.md) §2.1 の遠い留めはそこにある。

- **TIER と THETA″$`^W`$**（FRAG 無しで証明済み）。$`x \lt \omega^2`$ について、段の写像は $`[\Omega_1, P')`$ の段 1 の符号を $`[G''(\Omega_2+x), G''(\Omega_2+x+1))`$ の符号の上へ運ぶ。その一歩は段を
  読まない：$`\Omega_2+x`$ はつぶしを持たないから。読みは $`o_b(G''(\Omega_2+x)) = L(\lambda''+\Omega_1+x)`$ で、$`o_b`$ は $`G''(\Omega_2+\omega^2)`$ より下の符号を $`[0, L(\lambda''+\Omega_1+\omega^2))`$ の上へ移す。
  $`\Omega_1`$ より下の符号は $`b`$ より下で読まれ、ほかは窓の中で読まれる。さらに $`Z^{\mathrm{W}}`$ の添字までの範囲の補題：**$`Z^{\mathrm{W}}`$ より下では段 3 の長いやり直しはまたがれない**（またがれる
  やり直しは短いか、$`F''_b`$）。細かい点：どの符号も窓の中で読まれるという 1 文は $`\Omega_1`$ より下で偽。極限の一歩は使う連続性の事実を名指すこと (m1)。
- **定理 ENUM-REACH″$`^{\mathrm{W}}`$**（移しで証明済み、FRAG のもと）。$`Z^{\mathrm{W}}`$ より下で符号 $`c''`$ を持つ段 3 のどのやり直し $`b = L(\lambda'')`$ でも $`r(b) = k''_b(o_b(c''))`$（両方の半分）。
  符号 $`c'' \ge \hat G''`$ は $`F''_b`$ に着地し、$`r(b) = k''_{F''_b}(o_b(c'')) \lt L(\lambda''+\Omega_1+\omega^2)`$。たとえば π 符号 $`G''(\Omega_2+\omega+1)`$ では $`r(b) = \delta''_1(F''_b)\cdot 2`$。「$`\ge`$」の半分は窓の上の
  長いやり直しの一歩、「$`\le`$」の半分は留めを広げた遠い頂上の補題。さらに値の順、$`r(b) \ge o_b(c'')`$、鋭いまたぎの規則、蓋。査読者は例を手で計算し直した。細かい点：遠い頂上の補題の
  条件の 1 つ（有限集合が正しいブロックに届く）は成り立つが、書かれていない (m2)。
- **定理 C$`^{\mathrm{W}\sharp}`$ と $`[0, Z^{\mathrm{W}}]`$ での主張**（移しで証明済み、FRAG のもと）。$`Z^{\mathrm{W}}`$ より下では、新しい組はどれも新しい組を含まない段 3 の $`\tau''`$-$`\delta''`$ の組で、
  どのやり直しもちょうどの届く先を持ち、扇の頂点も 3 重の入れ子も無い。$`Z^{\mathrm{W}}`$ と、$`1 \le x \le \omega^2`$ のどの $`L(\theta'_2\cdot(\Omega_2+x))`$ も、$`\le_1`$ の前の点を持たず、下のどの点も越えて届かない点。
  だから $`\beta_0 \gt Z^{\mathrm{W}}`$、$`T_3^C \gt Z^{\mathrm{W}}`$、$`[0, Z^{\mathrm{W}}] \subseteq \mathrm{Core}(R_2^C)`$ で、$`Z^{\mathrm{W}}`$ はつぶす引数が $`I_\omega`$ より下の InaccPsi の標準形。途中の点
  $`L(\theta'_2\cdot(\Omega_2+x))`$ はその制限（両方の半分）。覆われない最初の符号は $`G''(\Omega_2+\omega^2)`$ で、$`Z^{\mathrm{W}}`$ そのものの π 符号。その読みは窓を出る。査読者は $`Z^{\mathrm{W}}`$ の式を
  計算し直した。細かい点：届く先が $`F''_b`$ の区域の中で終わる、またぐ点の原子は、「両側で真」ではなく BASE-INV の 2 つの場合で覆われる (m3)。$`Z^{\mathrm{W}}`$ での $`R_2^S`$ の側は概略（数えない）。
- **鋭い形の $`Z^{\mathrm{W}}`$ より下の CAP-0″**（証明済み、FRAG のもと）：$`Z^{\mathrm{W}}`$ より下の段 3 のどのやり直しも自分をまたがない。
- **$`\nu_3 = L_3(\omega+1) = \psi_{\Omega_1}(\Omega_\omega\cdot 3 + \omega^{P_3+1} + P_3)`$ へ。** $`y_3`$ を、段 3 で骨組み型でない $`R_2^S`$ の組の最小の右端とする。
  - **TAUL**（FRAG 無しで証明済み）：段 3 のどのやり直しも、段 3 の骨組み型の組の左端ではない。細かい点：証明では、下の段の骨組み型の左端はどれも $`L(0)`$ より下か、隙間
    $`(L(e), L(e+1))`$ の真に中にある、と言うこと (m5)。
  - **SKEL″$`^\nu`$**（$`R_2^S`$ で $`\min(y_3, L(\Omega_\omega))`$ より下で、移しで証明済み、FRAG のもと。$`L(\Omega_\omega)`$ より上は含意として証明済み）：段 3 の区域の骨組みは $`y_3`$ より下で、
    **$`\le_1`$ の前の点がどうであっても**、それが区域の中で共終でも成り立つ。またぐ点は段 3 のやり直しなので、TAUL と $`y_3`$ の選び方から、その $`\lt_2`$ の原子は両方の構造で偽。$`\le_1`$ の
    原子は、1 つ下の SKEL⁺（[BREAK-ja.md](BREAK-ja.md) §2）と同じく、有限集合 1 つずつで扱う。基の点は要らない。細かい点：これが広げる前の補題を名指すこと、「基は左端でない」を
    「基は $`y_3`$ より下に $`\lt_2`$ の後の点を持たない」と読むこと（基は $`L_3(\omega) \lt_2 \nu_3`$ の左端）、$`R_2^S`$ の主張と書くこと (m4)。
  - **SHIFT$`_3''`$**（含意として FRAG のもとで証明済み）。(Y) $`y_3 \ge \nu_3`$、(H2$`^{\mathrm{cr}}`$) $`L_3(\omega)`$ をまたぐやり直しのちょうどの届く先、(H3) $`L(\Omega_\omega)`$ より上の FRAG と隙間の
    計算、から：$`R_2^S`$ で $`L_3(\omega) \lt_2 \nu_3`$、$`L_3(\omega)`$ のブロック（SKEL″$`^\nu`$ から）は中に段 2 の組を持つ段 3 の組を含むので、$`\nu_3`$ より下に 3 重の入れ子があり、
    $`T_3^S = y_3 = \nu_3`$。**これで [SHIFT11-ja.md](SHIFT11-ja.md) §3.1 の進行を止める点 B-1 が片づく**：$`L_3(\omega)`$ でのブロックは、もう基の点も有界な $`\le_1`$ の前の点の集合も求めない。
    査読者は 3 重の入れ子と $`\nu_3`$ の名前を計算し直した。細かい点：(Y) は未解決の入力に頼るので、「$`T_3^S = \nu_3`$」は含意のまま (m6)。
  - 43 回目の査読の仮定つきの NU-LOW‴（含意として証明済み）：$`R_2^S`$ で (Y) を与える。$`R_2^C`$ についての節は NU-CT$`_3`$（概略）に頼る。
  - **未証明：$`\nu_3`$。** 未解決の入力：$`[Z^{\mathrm{W}}, L(\Omega_\omega))`$ での CAP-0″、CAP-1″、段 4 の LONG-CLASS、(H2$`^{\mathrm{cr}}`$)、1 つ上の LEFT⁺（名前のついた 1 つの段階で、NU-LOW‴ の
    左端についての 2 つの仮定を与える）。概略：(H3) と NU-CT$`_3`$。
- **$`Z^{\mathrm{W}}`$ より先**（数えない）：2 つ目の窓（ずれ $`\Omega_1+x'`$ にわたる遠い留め）は概略で、次の最前線の見込みは $`L(\theta'_2\cdot\Omega_2\cdot 2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+\Omega_2}\cdot 2)`$。
  段 3 の長いやり直しの最初のまたぎが $`\theta'_3 = \psi_{\Omega_4}(\Omega_\omega\cdot 2)`$ として符号 $`G''(\theta'_3\cdot\omega^2)`$ で起こることは予想。**後で（§2.1）：** 2 つ目の窓は証明され、
  FRAG のもとで主張は $`R_2^C`$ で $`[0, Z^{\mathrm{WW}}]`$ で成り立つ。

### 1.2 $`R_2^S`$ で $`[0, Z^{\mathrm{FP}})`$、そして基 $`Z^{\mathrm{FP}}`$ で蓋だけを読む帰納法

言葉は [SHIFT11-ja.md](SHIFT11-ja.md) §3.2 のもの。$`b`$ をまたぐ点とは、$`x \le_1 b`$ となる点 $`x \lt b`$ のこと。

- **$`Z^\Lambda`$ の届く先と LONG″-CAP**（証明済み、FRAG のもと）。π 符号 $`G''(\omega^2)`$ での ENUM-REACH″$`^{\mathrm{FP}}`$（[SHIFT11-ja.md](SHIFT11-ja.md) §3.1）の例として：

  $`r(Z^\Lambda) = \delta''_1(L(\theta'_2\cdot\omega^2+\omega^2)) + 1 = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+2} + \omega^{P'+2} + \omega^{P'+1} + P') + 1,`$

  そして符号か π 符号が $`G''(\omega^2)`$ の、$`Z^{\mathrm{FP}}`$ より下の段 3 のどのやり直し $`b = L(\lambda'')`$ でも $`r(b) = \delta''_1(L(\lambda''+\omega^2)) + 1 \lt L(\lambda''+\omega^2\cdot 2)`$。これは
  [SHIFT11-ja.md](SHIFT11-ja.md) §3.2 の予想 LONG″-CAP で、予想した値のとおり。そこの §3.1 の査読は符号で確かめた。π 符号では値に査読済みの 2 つ目の出どころ、[SHIFT10-ja.md](SHIFT10-ja.md) §1.1 の
  LONG″-$`G''(\omega^2)`$ があり、それは残る（取り下げた結果はそこに届かない）。細かい点：その出どころを証明の中で引くこと (m4)。
- **LOC-PASS**（証明済み）。$`Z \lt \beta_0`$ が $`\le_1`$ の前の点を持たず、下のどの点も越えて届かない点で、分解できない $`\mu`$ が $`(r(Z), \beta_0]`$ にあれば、$`R_2^S`$ の芯は $`[0, Z]`$ を含む
  （LOC-ISO から）。これはそこの §3.2 の査読の m1。
- **S-PAST-Λ**（証明済み、FRAG のもと）。$`(Z^\Lambda, Z^{\mathrm{LG}}]`$ にある段 3 の区域の基 $`\mu`$ は、$`\mu`$ がその下の符号 $`G''(\omega^2)`$ の長いやり直し 1 つの次のやり直しの点でない限り、
  $`\le_1`$ の前の点を持たない。だから主張は $`R_2^S`$ で $`[0, Z^{\mathrm{LG}})`$ で成り立つ。細かい点：論文のはじめの行は「$`r(Z^\Lambda)`$ の蓋だけで」と言うが、証明はどの
  $`L(\theta'_2\cdot\omega^2 + G''(\omega^2)\cdot k)`$ でも LONG″-CAP を要し、$`r(Z^\Lambda)`$ だけでは $`[0, L(\theta'_2\cdot\omega^2 + G''(\omega^2)))`$ しか出ない (m1)。
- **S-FOLLOW と $`R_2^S`$ で $`[0, Z^{\mathrm{FP}})`$ での主張**（証明済み、FRAG のもと）。$`Z`$ が $`\beta_0 \gt Z`$ で $`R_2^S`$ で $`\le_1`$ の前の点を持たない $`\upsilon`$ の点なら、主張は $`R_2^S`$ で
  $`[0, Z)`$ で成り立つ。だから $`R_2^C`$ のこの形の最前線はどれも、$`R_2^S`$ で同じ最前線（半開区間）を与える。[SHIFT11-ja.md](SHIFT11-ja.md) §3.1 とあわせて：**主張は $`R_2^S`$ で
  $`[0, Z^{\mathrm{FP}})`$ で成り立ち**、$`Z^{\mathrm{FP}}`$ より下の $`R_2^S`$ のどの組でも Carlson の判定が成り立つ。細かい点：論文が挙げた一番弱い段階は弱くない（$`\beta_0`$ より下では 2 つの構造は
  一致する）。本当に頼っているのは [SHIFT11-ja.md](SHIFT11-ja.md) §3.1 全体で、査読 1 回 (m3)。注意の 1 つは「のとき、またそのときに限り」と言うが、証明されているのは「のとき」だけ (m2)。
- **基 $`Z^{\mathrm{FP}}`$ で蓋だけを読む帰納法**（移しで証明済み、FRAG のもと）。[SHIFT11-ja.md](SHIFT11-ja.md) §3.2 の帰納法は、基の点を 3 つの性質（$`\beta_0`$ がその上にある、下のどの点も
  それを越えて届かない、その下のどの隙間でも隙間の計算が成り立つ）を通してだけ読み、$`Z^{\mathrm{FP}}`$ はそれを持つ。$`Z^{\mathrm{FP}}`$ で走らせると：$`\beta_0 \gt Z^{\mathrm{FPG}}`$、$`T_3^C \gt Z^{\mathrm{FPG}}`$、
  $`Z^{\mathrm{FPG}}`$ より下の Carlson の判定、$`R_2^C`$ で $`[0, Z^{\mathrm{FPG}}]`$ での主張。査読者は、証明が読み、$`Z^\Lambda`$ は持ち $`Z^{\mathrm{FP}}`$ は持たない性質を探した。7 つの候補はどれも移る。
  $`Z^{\mathrm{FP}} \lt Z^{\mathrm{FPG}} \lt L(\theta'_2\cdot(\Omega_2+1)) \lt Z^{\mathrm{W}}`$ なので、これは §1.1 のちょうどの値によらない $`(Z^{\mathrm{FP}}, Z^{\mathrm{FPG}}]`$ の 2 つ目の証明。
- **S-COND$`^{\mathrm{FP}}`$**（含意として証明済み）：$`Z^{\mathrm{FP}}`$ より上で $`Z^{\mathrm{FPG}}`$ 以下の区域の基 $`\mu`$ のうち、$`Z^{\mathrm{FP}}`$ 以上の符号 $`G''(\omega^2)`$ の長いやり直しが届かないものについて、
  $`R_2^S`$ で $`[0, \mu)`$ での主張。$`r(Z^{\mathrm{FP}})`$ の蓋（予想 CAP$`^{\mathrm{FP}}`$）があれば $`R_2^S`$ は $`Z^{\mathrm{FP}}`$ を越える。**後で（§2.2）：** CAP$`^{\mathrm{FP}}`$ は証明され、主張は
  $`R_2^S`$ で $`[0, Z^{\mathrm{W}})`$ で成り立つ。

### 1.3 Lean、段階 5：$`\Lambda_\Gamma`$ までと $`\Phi_\Gamma`$ より下のやり直しのブロック

- **ファイル。** [R2/](R2/) の新しい 8 個のモジュール（CitedW、FragX、Exact、RSG、TopG、BlkG、OffG、OffG2）と、RSX、OffPhi、OffV、BlkX の説明の行（[SHIFT11-ja.md](SHIFT11-ja.md) §3.3 の
  監査の n1–n3。コードは変わらない）。リポジトリでは、どれもライブラリ全体とともにモジュールとして作られる（緑、`sorry` 無し）。詳しくは [LEAN-ja.md](LEAN-ja.md)。
- **新しく引いた公理 5 個**（ファイル CitedW）：[W07b] Thm 2.2。主張から引く（$`0 \lt \xi \le \alpha`$ で、$`R_1`$ で $`\alpha \le_1 \alpha+\xi`$ となるのは、$`\mathrm{logend}(\alpha') \ge \xi`$ の
  $`\alpha = \omega^{\alpha'}`$ のときに限る。その証明は使わない論文にある）。[W07a] L.4.2（$`\vartheta^\tau(1+\alpha) = \bar\omega_{\tau+\alpha}`$。$`\bar\omega`$ は $`\varepsilon`$ 数でない加法的主要数を並べたもの）。
  [W07a] Def 3.22、Def 3.28、L.3.30（$`\vartheta^\tau(\xi)`$ は $`\xi`$ と同じパラメタを持つ項）。[W07a] Def 5.1 の 4 つ目の場合（$`\vartheta^\tau`$ の項の基の取りかえ）。定数 $`\vartheta^\tau`$。前の段階と
  同じく、[W07a] の $`\Omega_1`$ は $`\omega_1`$ と取る。
- **$`D_1`$ の上の基の取りかえつきの FRAG**（`fragX`）：$`D_1`$ の点の上では、FRAG の写像はただ 1 つの基の取りかえ $`\pi`$。新しい公理は無い。
- **補題 EXACT**（`pi_tq`）：$`r`$ から $`s`$ への基の取りかえ $`\pi`$ について $`\pi(r\cdot\gamma+e) = s\cdot\gamma+e`$、$`\pi(r\cdot r+e) = s\cdot s+e`$（$`\gamma, e \lt s`$）。
- これらの項についての **やり直しを行き先とする RS**（`rs_rstG`）、**補題 IMG**（`wit_pow`、`wit_mul`、`wit_sq`：写しはこれらの項を小さくしない）、**TOP$`^O`$**（`top_tq`、FRAG 無し）。
- **$`\Lambda_\Gamma`$ までの定理 BLK$`^O`$**（`blkG`）：$`\lambda \le \Lambda_\Gamma`$ のどのやり直しの添字でも BLK$`^O`$ の (i)–(iii)。ずれは **どの順序数の段でも** OFF-V の閉じた形：段 0 で $`c(\lambda)`$、
  どの $`\gamma \ge 1`$ でも $`\lambda = V_\gamma(\alpha)`$ で $`\rho\cdot\gamma + \mathrm{logend}(\alpha)`$、$`\Lambda_\Gamma`$ で $`\rho\cdot\rho`$。値：$`\mathrm{lh}(V_\omega(1)) = \delta + V_\omega(1)\cdot\omega`$、
  $`\mathrm{lh}(\Lambda_\Gamma) = \delta + \Lambda_\Gamma^2`$。
- **$`\Phi_\Gamma`$ より下の定理 BLK$`^O`$**（`blkG2`）。$`\Phi_\Gamma`$ は Γ の点を並べる関数 $`G_\Gamma`$ の最初の不動点（$`G_\Gamma(1) = \Lambda_\Gamma`$。Γ の点とは、すべての $`\gamma \lt \lambda`$ で
  $`V_\gamma(\lambda) = \lambda`$ となる $`\lambda \gt 0`$）。Γ の点 $`G_\Gamma(\alpha)`$ でずれは $`\rho^2 + \mathrm{logend}(\alpha)`$。ほかのやり直しの添字では OFF-V のもの。Lean は
  $`V_\omega(1) \lt \Lambda_\Gamma \lt \Phi_\Gamma \lt \Omega_1`$ を証明する。
- **CORE-C**（`coreG2`）：$`[0, \Phi_\Gamma) \subseteq \mathrm{Core}(R_2^C)`$。FRAG 無し（前は $`[0, V_\omega(1))`$）。
- **公理。** 主な定理は 49 個の引いた公理のうち 47 個を使う（段階 4 の 42 個と新しい 5 個）。引いた公理は今は 5 つのファイルに 49 個（定数 10 個、事実 39 個）。
- **監査**：新しい 5 個の公理は忠実、どの定義も正しい（Γ の点と $`\Lambda_\Gamma`$ は [REACHES-ja.md](REACHES-ja.md) §1 と [PINS-ja.md](PINS-ja.md) の集合と同じ）、どの主な定理も Lean で証明済み。
  段階の 160 個の定理すべての公理を出力した。致命的な点も進行を止める点も無い。細かい点：[LEAN-ja.md](LEAN-ja.md) の公理の数 (m1)。そこに [W07b] Thm 2.2 は主張だけを引くと書くこと (m2)、
  $`\Omega_1 = \omega_1`$ と書くこと (m3)。$`\Phi_\Gamma`$ で見込まれるずれ $`\rho^2+\rho`$ は紙の上だけで、Lean の結果ではない (m4)。$`\Phi_\Gamma`$ より下の範囲は $`\Lambda_\Gamma`$ までの範囲を含む (m5)。

### 1.4 44 回目のあとの状態

- **$`R_2^C`$ での Wilken の主張**：両方の半分が FRAG 無しで $`[0, X_4]`$ で、**FRAG のもとで $`[0, Z^{\mathrm{W}}]`$ で** 成り立つ（査読 1 回、§1.1）。$`(Z^\Lambda, Z^{\mathrm{LG}}]`$ と
  $`(Z^{\mathrm{FP}}, Z^{\mathrm{FPG}}]`$ は 2 つの証明（査読 2 回）。$`Z^{\mathrm{W}}`$ より上：証明されていない。
- **$`R_2^S`$ での Wilken の主張**：$`[0, \upsilon_{\omega^3}]`$ で（FRAG があってもなくても）、そして FRAG のもとで **$`[0, Z^{\mathrm{FP}})`$ で**（査読 1 回、§1.2）。FRAG のもとで $`\beta_0 \gt Z^{\mathrm{W}}`$。
  (E) は未解決で、$`\beta_0`$ の場所は分からない。
- **届く先**（FRAG のもと）：段 3 では $`Z^{\mathrm{W}}`$ より下のどのやり直しでも $`r(b) = k''_b(o_b(c''))`$。$`r(Z^\Lambda)`$ は §1.2 のとおり。
- **LOW：FRAG のもとで偽**（[SHIFT11-ja.md](SHIFT11-ja.md) §1.1、査読 1 回）。この回は触れていない。**$`\nu_3`$：証明されていない**。その上の半分は今は名前のついた 3 つの仮定からの含意（§1.1）。
- **Lean**：[SHIFT11-ja.md](SHIFT11-ja.md) §3.4 のものに加えて、今は $`\Lambda_\Gamma`$ までと $`\Phi_\Gamma`$ より下の BLK$`^O`$、$`\Phi_\Gamma`$ より下の CORE-C（§1.3）。
- $`\theta_0`$ より下の下からの評価の計画：この回は扱っていない（$`\iota(\mathrm{CH}_5) \ge \psi_{\Omega_1}(S_*)`$。$`S_*`$ より先は予想 LEX-SELF）。SRO より下の段階：変化なし（3,166 個の見本の
  行列すべてでどの $`n`$ でも済み。SRO より下のすべての標準の行列についての一般の主張だけが未解決）。

### 1.5 44 回目の確かめ

どの実行も 60 秒未満。どれも証明ではない。

- §1.1。著者：名前、段、符号、読み（予想した点の標準形、順序、定義域）と、4 つの段での段の写像の行きと帰り。失敗 0。はじめの実行では試しの条件の 1 つが間違っていて（長い符号の
  いくつかを失敗と数えた）、直した。記録にそう書いてある。査読者：段 3 のでたらめなやり直しの添字 375 個（符号と窓）と、さらに 2 つの段での段の写像。失敗 0。査読者のはじめの実行は
  標準形でないずれを使ったので、2 回目の実行だけを数える。
- §1.2。著者：項についての 3 回の実行（標準形、定義域、順序）、失敗 0。査読者：2 つの基 $`Z^\Lambda`$ と $`Z^{\mathrm{FP}}`$ で定義域、符号の種類、順序を比べる 600 個の場合、食い違い 0。
- §1.3。Lean：8 個のモジュールをそれぞれ単独で、そして全部まとめて、緑。終わりに偽の主張を足すと失敗する（監査がやり直した）。リポジトリでのライブラリ全体の build は緑で、`sorry` 無し。

### 1.6 未解決

- $`Z^{\mathrm{W}}`$ より上：2 つ目の窓（ずれ $`\Omega_1+x'`$ にわたる遠い留め、$`\Omega_2+\omega^2`$ を越える段の読み）。そして符号 $`G''(\theta'_3\cdot\omega^2)`$ からの段 3 の長いやり直しのまたぎ
  （1 つ上での [SHIFT11-ja.md](SHIFT11-ja.md) §1.1 の数え上げ）。そして $`L(\Omega_\omega)`$ までの CAP-0″、CAP-1″、段 4 の LONG-CLASS、(H2$`^{\mathrm{cr}}`$)、1 つ上の LEFT⁺、(H3)、NU-CT$`_3`$、$`\nu_3`$。
- FRAG のもとで $`R_2^C`$ で $`Z^{\mathrm{W}}`$ より上の主張（FRAG 無しなら $`X_4`$ より上）、$`R_2^S`$ で $`Z^{\mathrm{FP}}`$ より上の主張（$`r(Z^{\mathrm{FP}})`$ の蓋、予想 CAP$`^{\mathrm{FP}}`$。$`Z^{\mathrm{W}}`$ での
  $`R_2^S`$ の側は概略）。
- Lean、この順に：$`\Phi_\Gamma`$ から $`\Lambda_\varepsilon`$ までの BLK$`^O`$（一般のカントール標準形のずれの項か、閉じた形の層をもっと）。再帰的なずれ $`O`$。そして SKEL⁺ と CAP（Lean のブロックの
  帰納法はまだ各やり直しのちょうどの届く先を要する。次の一歩は届く先を計算しない形）、LIFT-0、O$`^C`$、NU-CT、$`\nu_C`$。$`R_2^S`$ の側。
- $`R_2^S = R_2^C`$：(E)、$`\beta_0`$、FAN-LOAD、$`\kappa_C`$ より上の後続の段での $`\le_1`$ の逆向き。
- $`\iota(\mathrm{CH}_2)`$、$`m_F`$、$`x_F`$、$`f_0`$、$`m_3`$、$`c_0`$ の評価と、$`\iota(\mathrm{CH}_3)`$ の上からの評価。
- 最初の到達不能基数（この回は扱っていない）：$`S_*`$ より先は $`\alpha \ge \Gamma_0`$ の容量（予想 LEX-SELF）か別の道。そして $`\theta_0`$ までの $`\Omega`$ の塔。$`\Theta_1`$ を越える $`\mathrm{CH}_2`$。
  SRO より下のすべての標準の行列での段階。
- 名前：$`R(\Theta_{d\omega})`$。$`\Lambda_{\mathrm{fp}2}`$ と $`\Theta_1`$ の間の正確なずれ。符号で書いた届く先の InaccPsi の式。[COVER-ja.md](COVER-ja.md) §9 の残り。

後で：今の一覧は §2.6。

## 2. 45 回目

論文は 3 本（2026-10）：$`Z^{\mathrm{W}}`$ より先の段 3 の 2 つ目の窓の論文（§2.1）と、$`Z^{\mathrm{FP}}`$ より先の $`R_2^S`$ の側の論文（§2.2）は、どちらも査読 1 回。$`R_2^C`$ の Lean の
6 つ目の段階（§2.3）は、公理と定義を確かめる監査を受けた（証明は Lean が確かめる）。この節の結果は、回数を書いていなければ査読 1 回。段の番号は §1 と同じ。

**$`R_2^C`$ での最前線は $`Z^{\mathrm{WW}}`$ に進んだ。** FRAG のもとで、**Wilken の主張は $`R_2^C`$ で $`[0, Z^{\mathrm{WW}}]`$ で成り立つ（両方の半分）**。ここで

```math
Z^{\mathrm{W2}} = L(\theta'_2\cdot\Omega_2\cdot 2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+\Omega_2}\cdot 2),\qquad Z^{\mathrm{WW}} = L(\theta'_2\cdot\Omega_2^2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+\Omega_2\cdot 2}),
```

で、$`\beta_0 \gt Z^{\mathrm{WW}}`$ と $`T_3^C \gt Z^{\mathrm{WW}}`$ も成り立つ（§2.1）。査読は $`[0, Z^{\mathrm{W2}}]`$ を 1 行ずつ読み、$`(Z^{\mathrm{W2}}, Z^{\mathrm{WW}}]`$ の段階は一番弱い段階だけを読んだ。
どちらも査読 1 回。$`Z^{\mathrm{W}}`$ から

```math
Z^{\mathrm{WG}} = L(\theta'_2\cdot(\Omega_2+\omega^2) + \omega^{G''(\omega^2)+1}) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+\Omega_2} + \omega^{\theta'_2+2} + \omega^{G''(\omega^2)+1})
```

への段階には、蓋だけを読む 2 つ目の証明がある（§2.2）ので、**査読 2 回**。**$`R_2^S`$ では主張は今は $`[0, Z^{\mathrm{W}})`$ で成り立つ**（FRAG のもと、査読 1 回、§2.2。その入力の §1.1 は
査読 1 回）。$`[0, Z^{\mathrm{FPG}})`$ には 2 つの証明がある（査読 2 回）。$`\nu_3`$ へは CAP-0″ だけが進む（今は $`Z^{\mathrm{WW}}`$ より下）。

引く論文：§2.1 と §2.2 は査読済みの段階を通してだけ：[W07b]（L.2.1）、Carlson 2009（L.5.5、L.5.7 (3)）、Wilken 2020（(21.10)、(21.12)、Prop 21.6、Thm 21.13）、[CW12b]（L.7.5。§2.2 の査読者が
読み直した：$`\lt_2`$ の組の左端は $`\lt_1`$ の無限の鎖の上限）、[C11]（LOC-ISO を通して）。§2.3 は [C09]（Def 5.2–5.4、Thm 14.14）と、前の段階の公理を通してだけの [W07a] と [W07b]。
どれも Wilken, JSL 72 (2007)、Carlson, AML 38 (1999)、Wilken, AML 45 (2006) を使わない。

44 回目の査読の細かい点は直した：§1.1 の査読の m1–m6 は §2.1 の論文で、§1.2 の査読の m1–m4 は §2.2 の論文で、§1.3 の監査の m2–m5 は CitedW と OffG2 の説明の行で（§2.3。m1 の公理の数は
すでに [LEAN-ja.md](LEAN-ja.md) にある）。

### 2.1 段 3 の 2 つ目の窓と、$`R_2^C`$ で $`[0, Z^{\mathrm{WW}}]`$ での主張

記号は §1.1 のもの。段 3 のやり直し $`b = L(\lambda'')`$ について $`F''_b = L(\lambda''+\Omega_1)`$ で、$`b`$ の **2 つ目の窓** は $`[F''_b, L(\lambda''+\Omega_1\cdot 2))`$。

- **どの $`x \lt G''(\Omega_2\cdot 2)`$ でも段 $`G''(\Omega_2+x)`$**（FRAG 無しで証明済み）。$`G''(\Omega_2\cdot 2) = \psi_{\Omega_2}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+\Omega_2}\cdot 2)`$ は $`x \mapsto G''(\Omega_2+x)`$ の
  最小の不動点。$`G''(\Omega_2\cdot 2)`$ より下のどの標準形 $`x`$ でも、符号 $`G''(\Omega_2+x)`$ は標準形で、段の補題が成り立つ。$`L`$ の添字は
  $`[\theta'_2\cdot(\Omega_2+G''(\Omega_2\cdot 2)), \theta'_2\cdot\Omega_2\cdot 2)`$ に無い。読みは $`o_b(G''(\Omega_2+x)) = L(\lambda''+\Omega_1+o_b(x))`$ で、$`o_b`$ は $`G''(\Omega_2\cdot 2)`$ より下の符号を
  $`[0, L(\lambda''+\Omega_1\cdot 2))`$ の上へ移す：$`\hat G''`$ からの符号は 2 つの窓の中で読まれる。範囲の補題は $`Z^{\mathrm{W2}}`$ の添字まで成り立つ。細かい点：$`x`$ が $`x \mapsto G''(\Omega_2+x)`$ の
  くり返しの値のとき、証明の 1 つの段階の順が違う (m1)。数えられないずれ $`\Omega_1+x'`$ や $`\Omega_1\cdot u+v`$ の定義域の条件は、ずれそのものではなく、その可算の定数が $`L(e)`$ より下にあること (m2)。
- **2 つ目の窓の上の遠い留め**（移しで証明済み、FRAG のもと）：§1.1 の遠い運び、遠い留め、遠い区域の頂上の補題、長いやり直しの一歩、またぎの補題が 2 つ目の窓へ広がる。査読者は
  $`F''_b`$ から始まる留めの鎖（著者が挙げた一番弱い段階）を試し、欠けは無かった。
- **定理 ENUM-REACH″$`^{\mathrm{W2}}`$**（移しで証明済み、FRAG のもと）。$`Z^{\mathrm{W2}}`$ より下で符号 $`c''`$ を持つ段 3 のどのやり直し $`b = L(\lambda'')`$ でも $`r(b) = k''_b(o_b(c''))`$（両方の
  半分）。$`Z^{\mathrm{W2}}`$ より下でまたがれるやり直しはどれも短い（符号が可算か $`\Omega_1`$）ので、長いやり直しのまたぎは要らない。$`\hat G''`$ からの符号は 1 つ目か 2 つ目の窓に着地し、
  $`r(b) \lt L(\lambda''+\Omega_1\cdot 2)`$。たとえば $`Z^{\mathrm{W}}`$ の π 符号 $`G''(\Omega_2+\omega^2)`$ では：

  $`r(Z^{\mathrm{W}}) = \delta''_1(L(\theta'_2\cdot(\Omega_2+\omega^2)+\Omega_1+\omega^2)) + 1,`$

  2 つ目の窓の最初の符号。これは §2.2 の論文が予想 CAP$`^{\mathrm{W}}`$ (i) として残した値。
- **定理 C$`^{\mathrm{W2}\sharp}`$ と $`[0, Z^{\mathrm{W2}}]`$ での主張**（移しで証明済み、FRAG のもと）。$`Z^{\mathrm{W2}}`$ より下では、新しい組はどれも新しい組を含まない段 3 の
  $`\tau''`$-$`\delta''`$ の組で、どのやり直しもちょうどの届く先を持ち、扇の頂点も 3 重の入れ子も無い。$`Z^{\mathrm{W2}}`$ と途中のどの $`L(\theta'_2\cdot(\Omega_2+x))`$ も、$`\le_1`$ の前の点を持たず、
  下のどの点も越えて届かない点。だから $`\beta_0 \gt Z^{\mathrm{W2}}`$、$`T_3^C \gt Z^{\mathrm{W2}}`$、$`[0, Z^{\mathrm{W2}}] \subseteq \mathrm{Core}(R_2^C)`$ で、$`Z^{\mathrm{W2}}`$ はつぶす引数が $`I_\omega`$ より下の
  InaccPsi の標準形。この部分で覆われない最初の符号は $`G''(\Omega_2\cdot 2)`$ で、$`Z^{\mathrm{W2}}`$ の π 符号。$`Z^{\mathrm{W2}}`$ での $`R_2^S`$ の側は条件つき（数えない）。
- **$`\Omega_2\cdot 2`$ より先の読みと $`[0, Z^{\mathrm{WW}}]`$ での主張**（移しで証明済み、FRAG のもと。査読は一番弱い段階を確かめた）。$`G''(\Omega_2\cdot\xi+x)`$ が標準形になるどの乗数
  $`\Omega_2\cdot\xi+x \lt \Omega_2^2`$ でも $`o_b(G''(\Omega_2\cdot\xi+x)) = L(\lambda''+\Omega_1\cdot o_b(\xi)+o_b(x))`$。新しい留めの段階は符号 $`\Omega_1+c`$ のつなぎだけで、和しか使わない。$`Z^{\mathrm{WW}}`$ より下では
  どの読みも $`\Omega_1^2 \lt G''(\omega^2)`$ より下にとどまるので、段 3 の長いやり直しはまたがれない。だから主張は $`R_2^C`$ で $`[0, Z^{\mathrm{WW}}]`$ で成り立ち、$`\beta_0 \gt Z^{\mathrm{WW}}`$、
  $`T_3^C \gt Z^{\mathrm{WW}}`$。その下のどの $`L(\theta'_2\cdot(\Omega_2\cdot\xi+x))`$（たとえば $`L(\theta'_2\cdot\Omega_2\cdot k)`$、$`L(\theta'_2\cdot\Omega_2\cdot\omega)`$）も制限。細かい点：符号 $`\Omega_1+c`$ での値は、
  ある論文が小さい添字についてだけ述べた $`\Omega_1^2`$ より下の符号の規則ではなく、短い符号の規則を引くこと (m3)。$`\Omega_1^2`$ の倍数についての 1 文を書き直すこと (m4)。2 つの部分を分けて
  記録すること (m5)。
- **鋭い形の $`Z^{\mathrm{WW}}`$ より下の CAP-0″**（証明済み、FRAG のもと）。
- **$`Z^{\mathrm{WW}}`$ より先**（数えない）：次の段階は符号 $`\Omega_1\cdot 2`$ 以上のつなぎで、和だけでは足りない。段 3 の長いやり直しの最初のまたぎが符号 $`G''(\theta'_3\cdot\omega^2)`$ で
  起こるかは予想のまま：$`\psi_{\Omega_3}`$ と $`\psi_{\Omega_4}`$ の原子を持つ乗数の読みが要る。1 つ上の LEFT⁺ と $`\nu_3`$ のほかの入力は扱っていない。

### 2.2 $`R_2^S`$ で $`[0, Z^{\mathrm{W}})`$、$`Z^{\mathrm{FP}}`$ での蓋、基 $`Z^{\mathrm{W}}`$ で蓋だけを読む帰納法

言葉は §1.2 のもの。$`Z^{\mathrm{FP}}`$ と $`Z^{\mathrm{W}}`$ の添字を $`\lambda_{\mathrm{FP}}`$、$`\lambda_{\mathrm{W}}`$ と書き、やり直し $`b = L(\lambda'')`$ について $`R''_1(b) = L(\lambda''+\omega^2)`$ と書く。

- **CAP$`^{\mathrm{FP}}`$**（証明済み、FRAG のもと。§1.1 のちょうどの届く先の例）。(i) $`r(Z^{\mathrm{FP}}) = \delta''_1(F''_{Z^{\mathrm{FP}}}) + F''_{Z^{\mathrm{FP}}} + R''_1(Z^{\mathrm{FP}})`$ で、これは
  $`R''_1(F''_{Z^{\mathrm{FP}}})`$ より下。(ii) $`k \ge 1`$ のどの $`b = L(\lambda_{\mathrm{FP}} + G''(\omega^2)\cdot k)`$ でも $`r(b) = \delta''_1(R''_1(b)) + 1`$。これは §1.2 の予想 CAP$`^{\mathrm{FP}}`$。査読者は、
  (ii) が $`Z^{\mathrm{W}}`$ より上の届く先を要しないことを確かめた：$`Z^{\mathrm{FP}}`$ と前の $`b`$ はどの $`b`$ よりも下に届くので $`b`$ は $`\le_1`$ の前の点を持たず、$`b`$ がまたぐ点は $`Z^{\mathrm{W}}`$ より
  下にある。細かい点：これを証明の中に書くこと (m3)。
- **S-F2：$`R_2^S`$ で $`[0, Z^{\mathrm{W}})`$ での主張**（証明済み、FRAG のもと。その入力である §1.1 の $`Z^{\mathrm{W}}`$ より下のちょうどの届く先は査読 1 回）。点 $`Z^{\mathrm{W}}`$ での S-FOLLOW。
  $`Z^{\mathrm{W}}`$ は $`\le_1`$ の前の点を持たず、下のどの点もそれを越えて届かず、$`\beta_0 \gt Z^{\mathrm{W}}`$。$`Z^{\mathrm{W}}`$ より下の $`R_2^S`$ のどの組でも Carlson の判定が成り立つ。細かい点：届く先が
  後の隙間で終わる、またぐ点の原子の扱いを名指すこと (m5)。
- **S-FPG**（証明済み、FRAG のもと）：$`R_2^S`$ で $`[0, Z^{\mathrm{FPG}})`$ での主張の 2 つ目の証明。S-COND$`^{\mathrm{FP}}`$（§1.2）と CAP$`^{\mathrm{FP}}`$ から、§1.1 の後半のちょうどの届く先を
  使わずに。細かい点：前の補題の端点の文を引くこと (m2)。
- **BASE-TEST″ と $`(Z^{\mathrm{FP}}, Z^{\mathrm{W}}]`$ の基の点の表**（証明済み）：それぞれの基の点について、その届く先、それがまたぐもの、$`\le_1`$ の前の点を持たない次の基の点。
  $`Z^{\mathrm{W}}`$ の行は下の LB$`^{\mathrm{W}}`$ に頼り、証明されていない。
- **基 $`Z^{\mathrm{W}}`$ で蓋だけを読む帰納法**（移しで証明済み、FRAG のもと）：$`\beta_0 \gt Z^{\mathrm{WG}}`$、$`T_3^C \gt Z^{\mathrm{WG}}`$、$`R_2^C`$ で $`[0, Z^{\mathrm{WG}}]`$ での主張。$`r(Z^{\mathrm{W}})`$ の値は
  読まない。$`Z^{\mathrm{WG}} \lt Z^{\mathrm{W2}}`$ なので、これは $`(Z^{\mathrm{W}}, Z^{\mathrm{WG}}]`$ の 2 つ目の証明。細かい点：範囲の端点の $`\lambda`$ を述べること (m1)。またぐ点 $`Z^{\mathrm{W}}`$ には
  「届く先は分からない」と書くこと (m4)。
- **S-COND$`^{\mathrm{W}}`$**（含意として証明済み）：$`Z^{\mathrm{W}}`$ より上で $`Z^{\mathrm{WG}}`$ 以下の区域の基 $`\mu`$ のうち、$`Z^{\mathrm{W}}`$ と $`L(\lambda_{\mathrm{W}} + G''(\omega^2)\cdot k)`$（$`k \ge 1`$）の
  どれも届かないものについて、$`R_2^S`$ で $`[0, \mu)`$ での主張。たとえば $`r(Z^{\mathrm{W}}) \lt L(\lambda_{\mathrm{W}} + G''(\omega^2))`$ なら $`[0, L(\lambda_{\mathrm{W}} + G''(\omega^2)))`$ での主張が出る。
- **未証明：LB$`^{\mathrm{W}}`$**（この論文で証明したとする $`r(Z^{\mathrm{W}}) \ge R''_1(F''_{Z^{\mathrm{W}}})`$）。進行を止める点 B-1：証明は §1.1 のちょうどの届く先の議論をその範囲の端点
  $`Z^{\mathrm{W}}`$ へ移すが、そこでは $`Z^{\mathrm{W}}`$ がまたぐ $`(Z^{\mathrm{W}}, R''_1(F''_{Z^{\mathrm{W}}}))`$ の短いやり直しのちょうどの届く先が要り、引いたどの段階もそれを与えない。論文のほかの
  結果はこれを使わない。CAP$`^{\mathrm{W}}`$ はこの論文では予想。
- **同じ回の後で**（§2.1）：値 $`r(Z^{\mathrm{W}}) = \delta''_1(R''_1(F''_{Z^{\mathrm{W}}})) + 1`$ は ENUM-REACH″$`^{\mathrm{W2}}`$ の 1 行（証明済み、査読 1 回）で、それはそれらの届く先を自分の帰納法の中で
  読む。そこから LB$`^{\mathrm{W}}`$ と CAP$`^{\mathrm{W}}`$ (i) が出る。S-COND$`^{\mathrm{W}}`$ とあわせると $`R_2^S`$ で $`[0, L(\lambda_{\mathrm{W}} + G''(\omega^2)))`$ での主張が出るはずだが、この組み合わせは
  査読されていないので数えない。

### 2.3 Lean、段階 6：再帰的なずれと $`\Lambda_\varepsilon`$ までのやり直しのブロック、届く先を使わない SKEL⁺

- **ファイル。** [R2/](R2/) の新しい 8 個のモジュール（OTerm、TopO、RSO、BlkO、ORec、OPhi、SkelC、SkelO）と、CitedW と OffG2 の説明の行（§1.3 の監査の m2–m5。コードは変わらない）。
  リポジトリでは、どれもライブラリ全体とともにモジュールとして作られる（緑、`sorry` 無し）。**新しい公理は無い**：主な定理は 49 個の引いた公理のうち 47 個を使う。詳しくは [LEAN-ja.md](LEAN-ja.md)。
- **1 変数の項**（`OT`）：定数、$`\omega^{x+t}`$、和。定数より上の $`\varepsilon`$ 数 $`x`$ では、これらは $`x`$ に相対的なカントール標準形のすべて。どの項でも **補題 EXACT**（`pi_ev`）、2 つの基での
  2 つの項の **一様な比べ方**（`uni_le`、`uni_eq`）、$`\varepsilon_{r+1}`$ より下のどの順序数も $`r`$ でのある項の値（`rep`、公理無し）。
- どの項でも、$`\varepsilon_{\rho+1}`$ より下のどの値でも **補題 IMG**（`RstK.img_val`）、**補題 TOP**（`RstK.top_pkg`）、やり直しを行き先とする **補題 RS$`^O`$**（`rs_rstT`）。
- **再帰的なずれ $`O`$**（`Orec`、整礎な再帰で）：$`O(\lambda)`$ は、1 と、$`\lambda`$ より下で共終に実現される項 $`t`$ についての $`t(\rho_\lambda)+1`$ の上限（どの $`\nu \lt \lambda`$ でも、ある
  やり直しの添字 $`\mu \in (\nu, \lambda)`$ で $`t(\rho_\mu) \le O(\mu)`$）。$`\Lambda_\varepsilon`$（`LamE`）は、$`\varepsilon_{\rho_\mu+1} \le O(\mu)`$ が共終に起こる最小のやり直しの添字。TOP の入力は仮定せず
  証明する（`topIn_Orec`）。
- **$`\Lambda_\varepsilon`$ までの定理 BLK$`^O`$**（`blkO`）：$`B \lt \Omega_1`$ で $`B \le \Lambda_\varepsilon`$ のどのやり直しの添字 $`B`$ でも BLK$`^O`$ の (i)–(iii)。だから $`\lambda \lt \Lambda_\varepsilon`$ のどの
  やり直しの添字でも $`\mathrm{lh}(\rho_\lambda) = \delta_\lambda + O(\lambda)`$（`reach_Orec`）、そして同じ $`B`$ で **CORE-C**：$`[0, \upsilon_B) \subseteq \mathrm{Core}(R_2^C)`$（`coreO`）。FRAG 無し。
- **段階 5 との照らし合わせ**（`OPhi`）：$`\Phi_\Gamma`$ より下で $`O`$ は §1.3 の閉じた形と等しい。$`\Phi_\Gamma \lt \Lambda_\varepsilon`$。$`O(\Phi_\Gamma) = \Phi_\Gamma^2 + \Phi_\Gamma`$（§1.3 の監査が紙の上だけと
  言った値が今は Lean にある）。だから $`\mathrm{lh}(\Phi_\Gamma) = \delta + \Phi_\Gamma^2 + \Phi_\Gamma`$。
- **届く先を使わない $`R_2^C`$ の SKEL⁺**（`skelPlusC`、FRAG 無し、引いた公理は 32 個で CitedW のものは使わない）。Lean の $`\nu_C`$ を、標準の組
  $`(\upsilon_{\mu+\omega\cdot(j+1)}, \upsilon_{\mu+\omega\cdot(j+1)+1})`$ でない $`\lt_2`$ の組の最小の右端とする。$`[0, \nu_C)`$ では：どの $`\lt_2`$ の組も標準、どの標準の組も $`\lt_2`$ の組、どの点もやり直しか
  ブロックの中にあり、ブロックの中では $`R_1^+`$ の $`\le_1`$、やり直しの $`\lt_1`$ の前の点はやり直し。証明はちょうどの届く先のかわりに、前向きにだけ動く被覆と、ある点より下で終わる届く先の上の
  上界 1 つを使う。さらに $`B \le \Lambda_\varepsilon`$ のどのやり直しの添字でも $`\upsilon_B \le \nu_C`$（`ups_le_nuC`）、$`\Phi_\Gamma \lt \nu_C`$。
- **CAP**（`capTC`）：中に組が入れ子になった組の最小の頂上 $`T_C`$ があれば、$`T_C`$ 以下のどの $`\alpha`$ も $`T_C`$ より上の点に $`\le_1`$ でない。そして $`\nu_C \le T_C`$。
- **監査**：使われた 47 個の公理は忠実、どの定義も正しい、どの主な定理も Lean で証明済み。監査が自分で作ったまとめと、235 個の定理の定数すべての公理を調べる道具の結果は報告と一致し、
  `sorry` と局所の公理を入れた対照はその道具が見つけた。致命的な点も進行を止める点も無い。細かい点：(n1) Lean の $`O`$ は [REACHES-ja.md](REACHES-ja.md) §1 の $`O`$ と害の無い 3 点で違う：
  Lean は集合に 1 を足す（後続のやり直しの添字では文書は空集合の上限を与えるが、ずれは 1）。Lean には項 $`\varepsilon_{x+1}`$ が無いので、その $`O`$ は $`\varepsilon_{\rho+1}`$ 以下にとどまり、文書と違うのは
  $`\Lambda_\varepsilon`$ からだけで、そこはどの定理も使わない。Lean は $`\omega^{x+t}`$ だけを使い、それで $`\varepsilon_{x+1}`$ より下の文書の項はすべて出る。(n2) $`\Lambda_\varepsilon \lt \Omega_1`$ は Lean に無い
  （紙の上にはある）ので、Lean の範囲は「$`B \le \Lambda_\varepsilon`$」。(n3) 定理の 1 つに余計な仮定がある。(n4) [W07b] Thm 2.2 は今も主張だけを引く。(n5) サーバが import をためているので確かめは
  速い。新しく作ったまとめが、確かめが本当に走ることを示す。

### 2.4 45 回目のあとの状態

- **$`R_2^C`$ での Wilken の主張**：両方の半分が FRAG 無しで $`[0, X_4]`$ で、**FRAG のもとで $`[0, Z^{\mathrm{WW}}]`$ で** 成り立つ（査読 1 回、§2.1。$`Z^{\mathrm{W2}}`$ より上の部分は一番弱い
  段階を確かめた）。$`(Z^\Lambda, Z^{\mathrm{LG}}]`$、$`(Z^{\mathrm{FP}}, Z^{\mathrm{FPG}}]`$、$`(Z^{\mathrm{W}}, Z^{\mathrm{WG}}]`$ は 2 つの証明（査読 2 回）。$`Z^{\mathrm{WW}}`$ より上：証明されていない。
- **$`R_2^S`$ での Wilken の主張**：$`[0, \upsilon_{\omega^3}]`$ で（FRAG があってもなくても）、そして FRAG のもとで **$`[0, Z^{\mathrm{W}})`$ で**（査読 1 回、§2.2）。$`[0, Z^{\mathrm{FPG}})`$ は 2 つの証明
  （査読 2 回）。FRAG のもとで $`\beta_0 \gt Z^{\mathrm{WW}}`$ なので、右端が $`Z^{\mathrm{WW}}`$ より下のどの関係でも 2 つの構造は一致する。(E) は未解決で、$`\beta_0`$ の場所は分からない。
- **届く先**（FRAG のもと）：段 3 では $`Z^{\mathrm{WW}}`$ より下のどのやり直しでも $`r(b) = k''_b(o_b(c''))`$。$`r(Z^{\mathrm{FP}})`$ と $`r(Z^{\mathrm{W}})`$ は §2.1、§2.2 のとおり。
- **LOW：FRAG のもとで偽**（[SHIFT11-ja.md](SHIFT11-ja.md) §1.1、査読 1 回）。この回は触れていない。**$`\nu_3`$：証明されていない**。CAP-0″ は $`Z^{\mathrm{WW}}`$ より下で成り立つ。
- **Lean**：§1.4 のものに加えて、今は $`\Lambda_\varepsilon`$ までのどのやり直しの添字でも再帰的なずれでの BLK$`^O`$、それらの添字での $`\upsilon_B`$ より下の CORE-C、$`O(\Phi_\Gamma)`$、
  $`\nu_C`$ より下の届く先を使わない $`R_2^C`$ の SKEL⁺、$`T_C`$ での CAP（§2.3）。
- $`\theta_0`$ より下の下からの評価の計画：この回は扱っていない（$`\iota(\mathrm{CH}_5) \ge \psi_{\Omega_1}(S_*)`$。$`S_*`$ より先は予想 LEX-SELF）。SRO より下の段階：変化なし（3,166 個の見本の
  行列すべてでどの $`n`$ でも済み。SRO より下のすべての標準の行列についての一般の主張だけが未解決）。

### 2.5 45 回目の確かめ

どの実行も 60 秒未満。どれも証明ではない。

- §2.1。著者：名前、標準形、定義域、読み、予想した点の順序の 9 つの確かめ、失敗 0。査読者：2 つ目の窓の段についてのでたらめな項 400 個と、$`\Omega_2\cdot 2`$ より先の読みと $`L`$ の
  定義域についてのでたらめな乗数 3,000 個、失敗 0。
- §2.2。著者：順序、標準形、定義域、符号、式の形についての 4 回の実行、失敗 0。査読者：基 $`Z^{\mathrm{W}}`$ での $`L`$ の定義域を、可算のずれ 12 個と $`\Omega_1`$ より上のずれ 8 個で、失敗 0
  （これは添字の側だけを試す。欠け B-1 は数値では試せない）。
- §2.3。Lean：8 個のモジュールをそれぞれ単独で、そして全部まとめて、緑。終わりに偽の主張を足すと失敗する。監査が自分で作った、定理の定数すべての公理を調べる道具つきのまとめも緑。
  リポジトリでのライブラリ全体の build は緑で、`sorry` 無し。

### 2.6 未解決

- $`Z^{\mathrm{WW}}`$ より上：符号 $`\Omega_1\cdot 2`$ 以上のつなぎ（和を越える）、$`\psi_{\Omega_3}`$ と $`\psi_{\Omega_4}`$ の原子を持つ乗数の読み、そして段 3 の長いやり直しのまたぎ（予想：最初は
  符号 $`G''(\theta'_3\cdot\omega^2)`$ で）と 1 つ上でのその数え上げ。そして $`L(\Omega_\omega)`$ までの CAP-0″、CAP-1″、段 4 の LONG-CLASS、(H2$`^{\mathrm{cr}}`$)、1 つ上の LEFT⁺、(H3)、NU-CT$`_3`$、$`\nu_3`$。
- FRAG のもとで $`R_2^C`$ で $`Z^{\mathrm{WW}}`$ より上の主張（FRAG 無しなら $`X_4`$ より上）、$`R_2^S`$ で $`Z^{\mathrm{W}}`$ より上の主張（$`r(Z^{\mathrm{W}})`$ と S-COND$`^{\mathrm{W}}`$ からの一歩は査読が要る。
  CAP$`^{\mathrm{W}}`$ (ii) は予想。$`Z^{\mathrm{W2}}`$ と $`Z^{\mathrm{WW}}`$ での $`R_2^S`$ の側は条件つき）。
- Lean、この順に：$`\Lambda_\varepsilon \lt \Omega_1`$。$`\Lambda_\varepsilon`$ を越える BLK$`^O`$（$`\varepsilon_{x+1}`$ を越える項と、それについての EXACT と IMG）。$`\Phi_\Gamma`$ と $`\Lambda_\varepsilon`$ の間の
  $`O`$ の閉じた値。$`\nu_C`$ の上からの評価（$`T_C \lt \Omega_1`$ かは未解決）。LIFT-0、O$`^C`$、NU-CT、$`\nu_C`$ の値。$`R_2^S`$ の側。
- $`R_2^S = R_2^C`$：(E)、$`\beta_0`$、FAN-LOAD、$`\kappa_C`$ より上の後続の段での $`\le_1`$ の逆向き。
- $`\iota(\mathrm{CH}_2)`$、$`m_F`$、$`x_F`$、$`f_0`$、$`m_3`$、$`c_0`$ の評価と、$`\iota(\mathrm{CH}_3)`$ の上からの評価。
- 最初の到達不能基数（この回は扱っていない）：$`S_*`$ より先は $`\alpha \ge \Gamma_0`$ の容量（予想 LEX-SELF）か別の道。そして $`\theta_0`$ までの $`\Omega`$ の塔。$`\Theta_1`$ を越える $`\mathrm{CH}_2`$。
  SRO より下のすべての標準の行列での段階。
- 名前：$`R(\Theta_{d\omega})`$。$`\Lambda_{\mathrm{fp}2}`$ と $`\Theta_1`$ の間の正確なずれ。符号で書いた届く先の InaccPsi の式。[COVER-ja.md](COVER-ja.md) §9 の残り。
