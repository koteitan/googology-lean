[← Back](README-ja.md) | [English](AUDIT.md) | [Japanese](AUDIT-ja.md)

# $`R_2^+`$：$`\nu_C = L(\omega+1)`$ の依存の表（32 回目の監査）

このページは [SHIFT7-ja.md](SHIFT7-ja.md) §3.1 に属する。[SHIFT7-ja.md](SHIFT7-ja.md) §2.1 の節目が何に立つかを並べる：

```math
\nu_C = \nu_S = L(\omega+1) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+1} + P'),\quad\text{and Wilken's claim in } R_2^C \text{ on } [0, \nu_C]\quad(\text{given FRAG}).
```

表は監査のもので、監査の査読者の直し（T2b2 には R-1、S12 には R-3）を入れた。状態の言葉は [README-ja.md](README-ja.md) §3 のもの。「移し」とは、査読済みの証明を、変えたところを
書き出して走らせ直して証明したこと。「査読」は 32 回目のあとの独立した査読の回数。「監査」と書いた節は監査が 1 行ずつ導き直し、その査読者も同意したので、前より 1 回多い。
ほかの節は、監査は場所と札と仮定だけを確かめた。段の番号は [SHIFT7-ja.md](SHIFT7-ja.md) と同じ（論文より 1 つ大きい）。「FRAG のもと」は、FRAG と FRAG-SUBST、SUBST-COMM、
[W07b] Thm 2.2 のこの計画自身の証明をあわせたもとで、という意味。

**監査の判定**：致命的な点も進行を止める点も無い。節目は「移しで証明済み」の水準で成り立つ。見つかった点はどれも細かい（文章、範囲、引用）。

| 節 | 主張 | 場所 | 状態 | 査読 | 立つもの |
|---|---|---|---|---|---|
| T0 | $`\nu_C = \nu_S = L(\omega+1)`$。$`R_2^C`$ の $`[0, \nu_C]`$ での主張 | [SHIFT7-ja.md](SHIFT7-ja.md) §2.1 | 証明済み、FRAG のもと | 1 と監査 | T1、T2、T3、T4 |
| T1 | 下の半分 $`\nu_C \ge L(\omega+1)`$ | [SHIFT7-ja.md](SHIFT7-ja.md) §1.1 | 証明済み、FRAG のもと | 1 | T1a–T1d |
| T1a | NU-LOW″：$`x \ge L(\omega)`$ の $`\le_1`$ の前の点は $`[m^*, x)`$ にある | [SHIFT3-ja.md](SHIFT3-ja.md) §2.4 | その条件のもとで証明済み、FRAG のもと | 2 | T1b、T1c、S11 |
| T1b | $`P'`$ より下の CAP-0。LOW は偽 | [SHIFT7-ja.md](SHIFT7-ja.md) §1.1 | 証明済み、FRAG のもと | 1 | S1 |
| T1c | CAP-1。段 2 でのちょうどの計算（つなぎ L2） | [SHIFT7-ja.md](SHIFT7-ja.md) §1.1 | 移し、FRAG のもと | 2（監査） | S1、S10 |
| T1d | 段 2 での LONG-CLASS$`^\omega`$、LC-STRICT。MULTI-FAR$`_k`$ | [SHIFT7-ja.md](SHIFT7-ja.md) §1.1、§2.1。[SHIFT3-ja.md](SHIFT3-ja.md) §1 | 証明済み（MULTI-FAR$`_k`$ は FRAG 無し） | 1（LC-STRICT は 2） | S1、S3、T1c |
| T2 | 上の半分 $`\nu_C \le \nu_S \le L(\omega+1)`$（PAIR、UP） | [SHIFT7-ja.md](SHIFT7-ja.md) §2.1 | 証明済み、FRAG のもと | 2（監査） | T2a–T2d |
| T2a | ずらしの判定 SHIFT | [SHIFT-ja.md](SHIFT-ja.md) §1 | 証明済み | 1（その仮定は監査が確かめた） | Wilken 2020、Prop. 21.11 |
| T2b | (C1)、(C2)、(P)：$`L(n) \le_1 L(n+1)`$、$`L(n) \le_1 L(\omega) \le_1 L(\omega+1)`$ | [SHIFT7-ja.md](SHIFT7-ja.md) §2.1 | 移し、FRAG のもと | 2（監査） | T2b1 |
| T2b1 | CROSS-LIM：符号と指数が $`P'`$ 以上のやり直しは $`H(\eta + P')`$ に届く（つなぎ L3） | [SHIFT7-ja.md](SHIFT7-ja.md) §2.1 | 移し、FRAG のもと | 2（監査） | T2b2、T2b3、S2、S10 |
| T2b2 | LONG-RS$`^U`$：長いやり直しの段階 | [SHIFT2-ja.md](SHIFT2-ja.md) §1.1、§2.1 | η のずれが $`\psi_{\Omega_2}(\Omega_2)`$ より下で証明済み、FRAG のもと。その先は段 1 でも査読の注意だけ（R-1） | 1 | S13–S15 |
| T2b3 | どの段でも実現するもの | [SHIFT5-ja.md](SHIFT5-ja.md) §2.2。[SHIFT3-ja.md](SHIFT3-ja.md) §2.4 | 証明済み | 1 / 2 | S11 |
| T2c | (C3)：TC⁺$`^\omega`$、EMB、ONTO-FIN（つなぎ L3） | [SHIFT7-ja.md](SHIFT7-ja.md) §2.1 | 移し、FRAG のもと | 2（監査） | T2c1、T2c2、S1、S12 |
| T2c1 | THETA-EQ$`^{\mathrm{rel}}`$、EQUIV$`^{\mathrm{rel}}`$、EQ-F$`^{\mathrm{rel}}`$ | [SHIFT7-ja.md](SHIFT7-ja.md) §1.1 | 移し | 1 | S3、S6 |
| T2c2 | どの段でも基の取りかえ BC$`^\pi`$。短い符号での TC⁺。READ-EQ | [SHIFT5-ja.md](SHIFT5-ja.md) §1.2、§2.2 | 証明済み（TC⁺ は FRAG のもと） | 1 | S11 |
| T2d | FIRST-PAIR、蓋 CAP、NU-CT | [BREAK-ja.md](BREAK-ja.md) §2 | 証明済み | 1 | S12 |
| T3 | 核の側：$`[0, \nu_C] \subseteq \mathrm{Core}(R_2^C)`$ | [BREAK-ja.md](BREAK-ja.md) §2 | 証明済み | 1 | S12。Carlson 2009 |
| T4 | 名前の側：$`\nu_C \lt \psi_{\Omega_1}(I_\omega)`$、$`L(\omega+1)`$ の標準形 | [SHIFT-ja.md](SHIFT-ja.md) §1。[SHIFT7-ja.md](SHIFT7-ja.md) §2.5 | 証明済み、確かめた（Lean） | 1 | — |
| S1 | LAND$`^\omega`$：$`P'`$ より下のどの長い符号でもちょうどの届く先とピン（FAR-PIN$`^{L,\mathrm{rel}}`$） | [SHIFT7-ja.md](SHIFT7-ja.md) §1.1 | 証明済み、FRAG のもと | 1 | S2、S6–S9 |
| S2 | ちょうどの計算：族、HULL-ARITH、越え方、下からの評価 | [SHIFT6-ja.md](SHIFT6-ja.md) §3 | 移し / 証明済み、FRAG のもと | 1 | S3、S7、S8、T2b2 |
| S3 | THETA$`^\omega`$：$`P'`$ より下のすべての符号の読み方（つなぎ L1） | [SHIFT6-ja.md](SHIFT6-ja.md) §3 | 移し | 2（監査） | S4、S11 |
| S4 | PSI-θ$`^k`$、PSI-W$`^{(k)}`$、PSI-W（つなぎ L1） | [SHIFT6-ja.md](SHIFT6-ja.md) §3.2 | 移し。確かめた（順序だけ） | 2（監査） | S5 |
| S5 | PSI-n、CNST$`^n`$、PSI-θ | [SHIFT3-ja.md](SHIFT3-ja.md) §2.1 | 証明済み | 1 | — |
| S6 | 閉じた点 $`\mathrm{cl}_\nu`$：MONO-cl、AGREE、EQ-cl | [SHIFT6-ja.md](SHIFT6-ja.md) §3.1 | 証明済み | 1 | S7 |
| S7 | EXACT-CL\*、GAP$`_j`$、ENUM | [SHIFT4-ja.md](SHIFT4-ja.md) §2.1 | 証明済み、FRAG のもと | 1 | S13–S15 |
| S8 | FAR-PIN$`^L`$、MULTI-RC$`^L`$、TOP-REG-LAND。下の動くピン、SIM。FAR-PIN$`^{L4}`$ | [SHIFT5-ja.md](SHIFT5-ja.md) §1.1。[SHIFT6-ja.md](SHIFT6-ja.md) §1.2、§2.2 | 移し、FRAG のもと | 1 | S9、S13–S15 |
| S9 | 移し $`T^U`$、FAR-PIN$`^U`$、MULTI-RC$`^U`$ | [SHIFT2-ja.md](SHIFT2-ja.md) §2.1 | 証明済み、FRAG のもと | 1 | S14 |
| S10 | どの段でも道具、TAIL-LEVEL、どの段でも OFF-INF | [SHIFT5-ja.md](SHIFT5-ja.md) §2.2 | 移し（見本の行を確かめた） | 1 | S11 |
| S11 | GEN-ALL。どの段でも D-UNC。SPLIT、DICT、EXT-ETA | [SHIFT5-ja.md](SHIFT5-ja.md) §1.3、§2.2。[SHIFT3-ja.md](SHIFT3-ja.md) §2.4 | 証明済み（EXT-ETA は移し） | 1 / 1 / 2 | — |
| S12 | $`\nu_S`$ より下の SKEL⁺ | [BREAK-ja.md](BREAK-ja.md) §2。[COVER-ja.md](COVER-ja.md) §5.1 | 証明済み | 1（R-3） | — |
| S13 | 定理 FRAG | [RESTARTS-ja.md](RESTARTS-ja.md) §1 | 証明済み | 2（監査） | [W07a]、[W07b]、S16 |
| S14 | FRAG-SUBST。SUBST-ISO、SUBST-COMM | [BREAK-ja.md](BREAK-ja.md) §4 | 証明済み | 2（監査）。1 | S13。[W07a] |
| S15 | 定理 FRAG2 | [RESTARTS-ja.md](RESTARTS-ja.md) §2 | 証明済み | 2（監査） | S13、S12 |
| S16 | [W07b] L.2.1 と Thm 2.2 のこの計画自身の証明（Wilken, AML 45 の代わり） | 初めのほうの回 | 証明済み | 1 | — |

引くもの。どれも監査が論文の本文と照らし合わせた：[W07a] Def 3.26–3.28、L.3.27、L.3.30、L.4.3、Def 5.1、L.5.3、L.5.5–5.7、Cor 5.4、Def 6.1、Def 6.2、L.6.3、L.6.9、L.6.10。[W07b] L.4.3、
L.4.4、Thm 5.3、Cor 5.7、Cor 5.9、Cor 5.10。Wilken 2020 の Prop. 21.6、L.21.7、Prop. 21.11。Carlson 2009 の L.5.5、L.5.7、Thm 14.10。ここで [W07a] は Wilken, "Ordinal arithmetic based on
Skolem hulling", APAL 145 (2007) 130–161、[W07b] は Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175。

数：34 の節。そのうち 11 は移しで証明済み（T1c、T2b、T2b1、T2c、T2c1、S2、S3、S4、S8、S10、S11 の EXT-ETA）。

**いちばん弱い 3 つのつなぎ**（それが崩れたら崩れるものの多さと、確かめの少なさで選んだ）：L1 = S3、S4。L2 = T1c と S10。L3 = T2、T2b、T2b1、T2c。監査はそこに致命的な点も
進行を止める点も見つけなかった。その細かい点と、その査読者の細かい点は [SHIFT7-ja.md](SHIFT7-ja.md) §3.1 にある。鎖が使うのに補題として書かれていないただ 1 つのものは、η のずれが
$`[\psi_{\Omega_2}(\Omega_2), P')`$ にあるときの LONG-RS$`^U`$（R-1）：材料はどれもあり、段 1 で（S1、S2、T1b、だから下の半分が）と段 2 で（T2b1 が）使う。
