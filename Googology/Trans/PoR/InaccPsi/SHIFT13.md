[← Back](README.md) | [English](SHIFT13.md) | [Japanese](SHIFT13-ja.md)

# $`R_2^+`$, the forty-seventh round: the claim in $`R_2^C`$ up to $`Z^\theta`$ and in $`R_2^S`$ up to $`Z^{\mathrm{V}}`$, and in Lean the restart blocks up to $`\Lambda_{\varepsilon\cdot\omega}`$ and LIFT-0 at every level

This page continues [SHIFT12.md](SHIFT12.md) (§3 there is the forty-sixth round); §1 is the forty-seventh round. The status words are those of [README.md](README.md) §3: **proved** means that
an independent referee found the result proved with no fatal or blocking point. A statement with a fatal or blocking point against it is listed under **Not proved**.
A certificate counts only when it was replayed. A result that the referee calls only a restatement of something known, or of the target, is not counted as progress.

## 1. The forty-seventh round

Three papers (2026-10): the multipliers with $`\psi_{\Omega_3}`$-atoms past $`Z^{\mathrm{V}}`$ (§1.1) and the $`R_2^S`$ side past $`Z^{\mathrm{WW}}`$ (§1.2), each refereed once, and the eighth Lean stage
for $`R_2^C`$ (§1.3), whose audit checked the axioms and the definitions (Lean checks the proofs). A result in this section has 1 review unless a count is given. Levels are numbered as in
[SHIFT12.md](SHIFT12.md) §1 (one higher than in the papers).

Notation as in [SHIFT12.md](SHIFT12.md): $`L(e) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + P'\cdot e)`$, $`P' = \psi_{\Omega_2}(\Omega_\omega\cdot 2)`$, $`\theta'_2 = \psi_{\Omega_3}(\Omega_\omega\cdot 2)`$ and
$`G''(\zeta) = \psi_{\Omega_2}(\Omega_\omega\cdot 2 + \theta'_2\cdot\zeta)`$. Also $`\theta = \psi_{\Omega_2}(\Omega_\omega)`$ (called $`P`$ in the papers), $`\theta_2 = \psi_{\Omega_3}(\Omega_\omega)`$,
$`\theta'_3 = \psi_{\Omega_4}(\Omega_\omega\cdot 2)`$, $`\Phi_\Omega = \psi_{\Omega_2}(\Omega_2)`$ and $`\Phi_2 = \psi_{\Omega_3}(\Omega_3)`$ (as in [SHIFT2.md](SHIFT2.md) §2.1).

**The frontier in $`R_2^C`$ moves to $`Z^\theta`$.** Given FRAG, **Wilken's claim holds in $`R_2^C`$ on $`[0, Z^\theta]`$, both halves**, with

```math
Z^\theta = L(\theta'_2\cdot\theta_2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+\theta_2}),\qquad \theta_2 = \psi_{\Omega_3}(\Omega_\omega),
```

and $`\beta_0 \gt Z^\theta`$ and $`T_3^C \gt Z^\theta`$ (§1.1). The point $`L(\theta'_2\cdot\psi_{\Omega_3}(\Omega_3))`$ conjectured in the last round is passed. **In $`R_2^S`$ the claim now holds on
$`[0, Z^{\mathrm{V}})`$**, given FRAG, and the conjecture CAP$`^{\mathrm{WW}}`$ of [SHIFT12.md](SHIFT12.md) §3.2 is proved (§1.2). The step from $`Z^{\mathrm{V}}`$ to

```math
Z^{\mathrm{VG}} = L(\theta'_2\cdot\psi_{\Omega_3}(0) + \omega^{G''(\omega^2)+1}) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+\psi_{\Omega_3}(0)} + \omega^{G''(\omega^2)+1})
```

has a second proof that reads only caps (§1.2), so it has **2 reviews**. In Lean: $`\nu_C`$ is a restart, Theorem BLK$`^O`$ up to $`\Lambda_{\varepsilon\cdot\omega}`$, and LIFT-0 and O$`^C`$ at every level (§1.3).

Papers cited: in §1.1 and §1.2 only through refereed stages: [W07a] and [W07b] (L.2.1, Cor 5.10), Carlson 2009 (L.5.5, L.5.7 (3)), Wilken 2020 (Prop 21.6, Def 21.4, Thm 21.13), [CW12b]
(L.7.5) and [C11] (through LOC-ISO). In §1.3: Carlson 2009 (Lemma 15.11, Thm 14.10 (1), Cor 15.15, Def 5.6), Carlson 2001 (the definition of "respects"), [W07a] and [W07b] through the axioms
of the earlier stages. None uses Wilken, JSL 72 (2007), Carlson, AML 38 (1999), or Wilken, AML 45 (2006).

The minor points of the reviews of the forty-sixth round are applied: m1–m6 of the review of [SHIFT12.md](SHIFT12.md) §3.1 in the paper of §1.1 (m1: the lemmas on the domain of $`L`$ are now
proved at every index), m1–m4 of the review of §3.2 there in the paper of §1.2, and m1, m3 and m5 of the audit of §3.3 there in Lean (§1.3; m2, m4 and m6 were already on
[LEAN.md](LEAN.md) and [REACHES.md](REACHES.md)). The labels of the parts that rest on different inputs are kept apart below (m6 of the review of §3.1 and m4 of the review of §3.2 there).

### 1.1 The multipliers below $`\theta_2`$, and the claim in $`R_2^C`$ on $`[0, Z^\theta]`$

A multiplier is now any $`\zeta \lt \theta_2`$, written in the form with $`\Omega_2, \Omega_3, \dots`$ of the $`n`$-ary tier ([SHIFT3.md](SHIFT3.md) §2.1, one level up); it is normal if $`G''(\zeta)`$ is a
normal form. For a restart $`b = L(\lambda'')`$ of level 3, the reading $`R''_b(\zeta)`$ lowers every $`\Omega_k`$ of that form to $`\Omega_{k-1}`$ (with the collapses) and reads each constant $`c`$ as
$`o_b(c)`$.

- **The domain of $`L`$ at every index** (proved, without FRAG; m1 of the review of [SHIFT12.md](SHIFT12.md) §3.1). The prefix lemma DOWN″, the bound CMAX on the countable constants and the
  criterion "$`\lambda''+u`$ is in the domain of $`L`$ iff the countable constants of $`u`$ lie below $`L(\lambda''+u)`$" ($`u \lt P'`$) hold at every index; each rests only on the definition of the
  domain and monotonicity, and the six uses in [SHIFT12.md](SHIFT12.md) §3.1 were checked again. Minor: the stated reason of CMAX fails for countable subterms inside a countable collapse; the
  result holds by an induction (m1); the two definitions of the countable constants give the same test (m2).
- **THETA″$`^\theta`$** (proved, without FRAG). Every normal multiplier below $`\theta_2`$ has its tier, and $`\zeta \mapsto 1 + R''_b(\zeta)`$ is an order isomorphism from the normal multipliers in the
  domain of $`o_b`$ onto the offsets $`1 \le u \lt \theta`$ with $`\lambda''+u`$ in the domain of $`L`$. So $`o_b(G''(\zeta)) = L(\lambda''+1+R''_b(\zeta))`$, and $`o_b`$ maps the codes below $`G''(\theta_2)`$
  onto $`[0, L(\lambda''+\theta))`$. Without constants $`R''_b`$ is the shift of every index by one. Minor: one monotonicity remark has the wrong direction; an induction closes the step (m3).
- **The links of every code below $`\theta`$** (proved, given FRAG). The pin at a link of any code in $`[\Omega_1, \theta)`$ (for example $`\psi_{\Omega_2}(0)`$, $`\Phi_\Omega`$, $`\varepsilon_{\Phi_\Omega+1}`$,
  $`\psi_{\Omega_2}(\Omega_3)`$) uses the exact base change of the $`n`$-ary terms at the link, in its general form. The far transport, the pins, the top lemma, the long restart step and the crossing
  lemma with threshold $`\theta`$ follow. Minor: the endpoint $`L(\lambda''+\theta)`$ is not covered (its link code is $`\theta`$ itself); no later step uses it, so the lemmas are restricted to points
  below it (m4); cite the general form of the exact base change (m5).
- **EXACT-GS⁺** (proved, without FRAG): the exact base change for the forms below $`\varepsilon_{\Phi+1}`$ without the $`n`$-ary tools. It carries the fallback $`Z^{\mathrm{E}}`$ below.
- **Theorem ENUM-REACH″$`^\theta`$** (proved by transfer, given FRAG): for every restart $`b = L(\lambda'')`$ of level 3 below $`Z^\theta`$, with code $`c''`$: $`r(b) = k''_b(o_b(c''))`$, and for a code of
  a tier $`\zeta \ge \Omega_2^2`$ also $`r(b) \lt L(\lambda''+1+R''_b(\zeta)+\omega^2) \lt L(\lambda''+\theta)`$. Every restart crossed below $`Z^\theta`$ is short. Instances:
  $`r(Z^{\mathrm{V}}) = \delta''_1(N) + \Gamma_{N+1}`$ with $`N = L(\theta'_2\cdot\psi_{\Omega_3}(0)+\psi_{\Omega_2}(0))`$, and $`r(Z^\Phi) = \delta''_1(N) + \Phi^N`$ with $`N = L(\theta'_2\cdot\Phi_2+\Phi_\Omega)`$.
  The value $`r(Z^{\mathrm{V}})`$ was recorded in [SHIFT12.md](SHIFT12.md) §3.1 with a proof that reads a reach above $`Z^{\mathrm{V}}`$, outside the range of its induction (B-1 of §1.2); here the
  induction runs below $`Z^\theta`$, so this value is proved now. $`r(Z^\theta)`$ is open.
- **Theorem C$`^{\theta\sharp}`$ and the claim on $`[0, Z^\theta]`$** (proved by transfer, given FRAG). Every new pair below $`Z^\theta`$ is a $`\tau''`$-$`\delta''`$ pair of level 3 with no new pair inside,
  there is no fan apex and no triple nest, and every $`L(\theta'_2\cdot\zeta)`$ with $`\zeta \lt \theta_2`$ normal is a point with no $`\le_1`$-predecessor that nothing below reaches past. So
  $`\beta_0 \gt Z^\theta`$, $`T_3^C \gt Z^\theta`$, $`[0, Z^\theta] \subseteq \mathrm{Core}(R_2^C)`$, and $`Z^\theta`$ is an InaccPsi normal form with collapse arguments below $`I_\omega`$. On the way:
  $`L(\theta'_2\cdot\psi_{\Omega_3}(1))`$, $`L(\theta'_2\cdot\psi_{\Omega_3}(\Omega_2))`$, $`L(\theta'_2\cdot\psi_{\Omega_3}(\Omega_4))`$. Minor: one reason in the step at the base points is wrong for
  multipliers that are not additively principal; the conclusion holds (m6). The $`R_2^S`$ side at $`Z^\theta`$ is conditional (not counted).
- **Three parts with fewer inputs**, recorded apart: $`(Z^{\mathrm{V}}, Z^\Phi]`$ uses only the tier of the $`\Gamma`$-atoms $`\psi_{\Omega_3}(\beta)`$, $`(Z^\Phi, Z^{\mathrm{E}}]`$ also EXACT-GS⁺, and
  $`(Z^{\mathrm{E}}, Z^\theta]`$ also the $`n`$-ary tools, where

```math
Z^\Phi = L(\theta'_2\cdot\Phi_2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+\Phi_2}),\qquad Z^{\mathrm{E}} = L(\theta'_2\cdot\varepsilon_{\Phi_2+1}) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+\varepsilon_{\Phi_2+1}}).
```

- **CAP-0″ below $`Z^\theta`$** (sharp form), and no long restart of level 3 is crossed below $`Z^\theta`$ (proved, given FRAG).
- **Toward the first long crossing** (proved, without FRAG): for multipliers without constants in $`[\theta_2, \Omega_\omega)`$, the reading READ″ (the copy one level up of READ,
  [SHIFT4.md](SHIFT4.md) §2.2) with its lemmas PLATEAU″-3, ALIGN″, HN″ and MONO″; it gives $`R''(\theta'_3\cdot\omega^2) = G''(\omega^2)`$. **LONG-FIRST″** (proved, as an implication): if the reading of
  the normal multipliers up to $`\theta'_3\cdot\omega^2`$ is $`1 + R''`$ (conjecture THETA″$`^{\mathrm{READ}}`$), the first long restart of level 3 that is crossed is $`L(\lambda''+G''(\omega^2))`$, at the code
  $`G''(\theta'_3\cdot\omega^2)`$. The referee wrote the one-line proof of the normality fact that it uses (m7).
- **Past $`Z^\theta`$** (not counted): the pins at links of codes in $`[\theta, P')`$ are open (their link point lies outside the segment of the link, so they need the relative far pin one level up);
  conjecture: the claim goes on to $`L(\theta'_2\cdot\theta'_2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2\cdot 2})`$.

### 1.2 $`R_2^S`$ on $`[0, Z^{\mathrm{V}})`$, CAP$`^{\mathrm{WW}}`$, and the induction with caps only at $`Z^{\mathrm{V}}`$

Words as in [SHIFT12.md](SHIFT12.md) §2.2; $`\lambda_{\mathrm{WW}}`$ and $`\lambda_{\mathrm{V}}`$ are the indices of $`Z^{\mathrm{WW}}`$ and $`Z^{\mathrm{V}}`$.

- **CAP$`^{\mathrm{WW}}`$** (proved, given FRAG; an instance of ENUM-REACH″$`^{\mathrm{V}}`$ of [SHIFT12.md](SHIFT12.md) §3.1, whose induction runs below $`Z^{\mathrm{V}}`$ and so covers the windows of
  $`Z^{\mathrm{WW}}`$): $`r(Z^{\mathrm{WW}}) = \delta''_1(N) + N\cdot 2`$ with $`N = L(\theta'_2\cdot\Omega_2^2+\Omega_1^2)`$; every $`b = L(\lambda_{\mathrm{WW}} + G''(\omega^2)\cdot k)`$, $`k \ge 1`$, has
  $`r(b) = \delta''_1(R''_1(b)) + 1`$; and $`r(Z^{\mathrm{WWG}}) = \delta''_1(R''_1(b)) + 2`$.
- **The claim in $`R_2^S`$** (proved, given FRAG) on $`[0, Z^{\mathrm{WWG}})`$ (S-COND$`^{\mathrm{WW}}`$ with CAP$`^{\mathrm{WW}}`$; it rests only on the readings below $`\Omega_2^2`$ and the links by sums),
  on $`[0, L(\theta'_2\cdot\Omega_2^\omega))`$ (S-FOLLOW; also the readings below $`\Omega_2^\omega`$, still only the links by sums) and on $`[0, Z^{\mathrm{V}})`$ (S-FOLLOW; also the links of Veblen
  codes); Carlson's criterion holds below $`Z^{\mathrm{V}}`$. With §3.2 of [SHIFT12.md](SHIFT12.md), $`[0, Z^{\mathrm{WW}})`$ has two proofs (2 reviews). Minor: one step of the first part cites
  $`\beta_0 \gt Z^{\mathrm{V}}`$, which rests on the links of Veblen codes; $`\beta_0 \gt Z^{\mathrm{WWG}}`$ is enough there (m1).
- **The base points of $`(Z^{\mathrm{WW}}, Z^{\mathrm{V}})`$** (proved): BASE-TEST″$`^{\mathrm{V}}`$, NEXT-BASE″$`^{\mathrm{V}}`$ and the table with each base point's reach, its cap, the next $`\tau''`$-point
  and the next base point; "first" in one lemma is now proved. Minor: name the base of the cited finiteness lemma (m2); state $`\lambda'' \ge \mu''+\omega^2`$ in one step (m3).
- **The induction with caps only at the base $`Z^{\mathrm{V}}`$** (proved by transfer, given FRAG): $`\beta_0 \gt Z^{\mathrm{VG}}`$, $`T_3^C \gt Z^{\mathrm{VG}}`$ and the claim in $`R_2^C`$ on
  $`[0, Z^{\mathrm{VG}}]`$. It reads no value of $`r(Z^{\mathrm{V}})`$. With §1.1, $`(Z^{\mathrm{V}}, Z^{\mathrm{VG}}]`$ has two proofs. With the base $`L(\theta'_2\cdot\Omega_2^\omega)`$ alone (links by sums
  only) the same gives $`\beta_0 \gt L(\theta'_2\cdot\Omega_2^\omega + \omega^{G''(\omega^2)+1})`$.
- **Not proved (blocking point B-1):** the claim in $`R_2^S`$ on $`[0, L(\lambda_{\mathrm{V}} + G''(\omega^2)))`$ and $`Z^{\mathrm{V}} \in \mathrm{Core}(R_2^S)`$. Both need $`r(Z^{\mathrm{V}}) \lt R''_1(N_{\mathrm{V}})`$,
  $`N_{\mathrm{V}} = L(\lambda_{\mathrm{V}} + \psi_{\Omega_2}(0))`$. The paper took $`r(Z^{\mathrm{V}})`$ from [SHIFT12.md](SHIFT12.md) §3.1, whose proof reads the exact reach of $`N_{\mathrm{V}} \gt Z^{\mathrm{V}}`$,
  outside the range of its induction; so that value is conditional there. ENUM-REACH″$`^\theta`$ of §1.1 proves the value, so the step would follow, but this combination has not been refereed,
  so it is not counted. The reaches of the restarts of code $`G''(\omega^2)`$ above $`Z^{\mathrm{V}}`$ (CAP$`^{\mathrm{V}}`$ (ii)) are a conjecture. Minor: say in the open list that the same input
  blocks $`r(Z^{\mathrm{V}})`$ (m4), and mark the header lines conditional (m5).

### 1.3 Lean, stage 8: $`\nu_C`$ is a restart, the restart blocks up to $`\Lambda_{\varepsilon\cdot\omega}`$, and LIFT-0 and O$`^C`$ at every level

Here $`\varepsilon = \varepsilon_{\rho+1}`$ at the restart in question, and $`\Lambda_{\varepsilon\cdot\omega}`$ is the least restart index below which $`\varepsilon_{x+1}\cdot j`$ is realized cofinally for every $`j \lt \omega`$.
A $`k`$-nest is $`a_0 \lt \dots \lt a_{k-1} \lt b_{k-1} \lt \dots \lt b_0`$ with $`a_i \le_2 b_i`$, and $`T_k`$ is the least top $`b_0`$ of a $`k`$-nest.

- **Files.** Eight new modules of [R2/](R2/) (NuRst, EpsM, BlkGen, ORecM, LamVal, NestK, CitedNest, LiftK). **One new axiom**, in CitedNest: Carlson 2009, Lemma 15.11 with Thm 14.10 (1), for the
  pattern of $`k`$ nested pairs, used as "a $`k`$-nest exists for every $`k`$" (`C09_nestk`). Now 52 axioms in seven files; the theorems of this stage use 51 of them. In the repository nine names of
  BlkGen carry the suffix `Gen` (for example `OffSpecGen`, `blk_genGen`), because BlkG already has the same names. The whole library builds (green, no `sorry`), every Cited\* file builds with
  free variables forbidden, and a control axiom with a free variable fails. Details on [LEAN.md](LEAN.md).
- **$`\nu_C`$ is a restart** (`nuC_restart`), with $`\mathrm{lh}(\rho_L) = \nu_C`$, and $`U_2 = \mathrm{Pred}_1(\rho_L) \cup \{\rho_L, \nu_C\}`$ (`U2_shape`, m3 of the audit of stage 7). No new axiom.
- **BLK$`^O`$ up to $`\Lambda_{\varepsilon\cdot\omega}`$** (`blkM`, `coreM`). EXACT, IMG and RS for the terms $`\varepsilon_{x+1}\cdot n + t`$, a block theorem for any term function with its own RS, and the
  recursive offset over the larger term set. (i)–(iii) of BLK$`^O`$, with the exact reaches and CORE-C, hold for every restart index $`B \le \Lambda_{\varepsilon\cdot\omega}`$, and
  $`\Lambda_{\varepsilon\cdot\omega} \lt \Omega_1`$. No new axiom.
- **The offsets at the frontiers** (`lam_values`): $`\varepsilon+1`$ at $`\Lambda_\varepsilon`$, $`\varepsilon+2`$ at $`\Lambda_{\varepsilon+1}`$, $`\varepsilon\cdot 2+1`$ at $`\Lambda_{\varepsilon\cdot 2}`$ and $`\varepsilon\cdot\omega`$ at
  $`\Lambda_{\varepsilon\cdot\omega}`$, and $`\Lambda_\varepsilon \lt \Lambda_{\varepsilon+1} \lt \Lambda_{\varepsilon\cdot 2} \lt \Lambda_{\varepsilon\cdot\omega} \lt \Omega_1`$. The offset of stage 7 stops being the reach exactly at
  $`\Lambda_{\varepsilon\cdot 2}`$. The InaccPsi names $`\Lambda_{\varepsilon+1} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+E+2})`$, $`\Lambda_{\varepsilon\cdot 2} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+E\cdot 2+1})`$ and
  $`\Lambda_{\varepsilon\cdot\omega} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+E\cdot\omega})`$, $`E = \varepsilon_{\Omega_1+1}`$, are derived on paper only: conjecture (n4 of the audit).
- **Where the first non-standard pair lies** (`nuC_bound`): $`\upsilon_{\Lambda_{\varepsilon\cdot\omega}} \le \rho_L \lt \nu_C \lt \Omega_1`$. There is still no notation bound for $`\nu_C`$.
- **$`k`$-nests, LIFT-0 and O$`^C`$ at every level** (NestK, LiftK). For a given $`k`$-nest, with no new axiom: NEST-UP, $`T_k \lt \Omega_1`$, CAP at $`T_k`$, $`[0, T_k] \subseteq \mathrm{Core}(R_2^C)`$,
  LIFT-0 at level $`k`$ (the pair, shape, reach and gap clauses, and $`T_{k-1} \lt s_k`$) and Theorem O$`^C`$ at level $`k`$; they use only three axioms of Carlson 2009, none of Wilken's papers. With
  `C09_nestk` they hold for every $`k`$ (`liftK`), $`T_1 \lt T_2 \lt T_3 \lt \dots \lt \Omega_1`$, and $`T_2 = \nu_C`$. At level 2 this proves O$`^C`$ again from 3 axioms instead of 39.
- **The audit** rebuilt the bundle, ran it (green, no `sorry`) and printed the axioms of all 116 theorems. No fatal and no blocking point. `C09_nestk` is faithful; the step that is ours (the
  nested structure is a pattern, Carlson 2009, Def 5.6, items 1–7) was checked item by item. The definitions (nests, $`T_k`$, the larger offset, $`\Lambda_{\varepsilon\cdot\omega}`$) are right. Minor:
  `liftK_two` does not use the new axiom (n1); the axiom `C09_nest` of stage 7 is the case $`k = 2`$ of `C09_nestk` (n2, now said in the doc line of LiftK); one doc line of LiftK is in the notation
  of these pages, not a Lean statement (n3, now said there); the names of $`\Lambda_{\varepsilon+1}`$, $`\Lambda_{\varepsilon\cdot 2}`$, $`\Lambda_{\varepsilon\cdot\omega}`$ stay a conjecture (n4).

### 1.4 Status after the forty-seventh round

- **Wilken's claim in $`R_2^C`$**: both halves on $`[0, X_4]`$ without FRAG, and **on $`[0, Z^\theta]`$ given FRAG** (1 review, §1.1; the parts $`(Z^{\mathrm{V}}, Z^\Phi]`$, $`(Z^\Phi, Z^{\mathrm{E}}]`$ and
  $`(Z^{\mathrm{E}}, Z^\theta]`$ rest on more and more inputs), with $`(Z^\Lambda, Z^{\mathrm{LG}}]`$, $`(Z^{\mathrm{FP}}, Z^{\mathrm{FPG}}]`$, $`(Z^{\mathrm{W}}, Z^{\mathrm{WG}}]`$, $`(Z^{\mathrm{WW}}, Z^{\mathrm{WWG}}]`$ and
  $`(Z^{\mathrm{V}}, Z^{\mathrm{VG}}]`$ by two proofs (2 reviews). Above $`Z^\theta`$: not proved.
- **Wilken's claim in $`R_2^S`$**: on $`[0, \upsilon_{\omega^3}]`$, and, given FRAG, **on $`[0, Z^{\mathrm{V}})`$** (1 review, §1.2), with $`[0, Z^{\mathrm{WW}})`$ by two proofs (2 reviews).
  $`\beta_0 \gt Z^\theta`$ given FRAG. (E) is open, and $`\beta_0`$ is not located.
- **Reaches** (given FRAG): at level 3 $`r(b) = k''_b(o_b(c''))`$ for every restart below $`Z^\theta`$; $`r(Z^{\mathrm{WW}})`$, $`r(Z^{\mathrm{V}})`$ and $`r(Z^\Phi)`$ as in §1.1, §1.2; $`r(Z^\theta)`$ is open.
- **LOW: false, given FRAG** ([SHIFT11.md](SHIFT11.md) §1.1, 1 review); not touched in this round. **$`\nu_3`$: not proved**; CAP-0″ holds below $`Z^\theta`$.
- **Lean**: as in [SHIFT12.md](SHIFT12.md) §3.4, and now $`\nu_C`$ is a restart, BLK$`^O`$ and CORE-C up to $`\Lambda_{\varepsilon\cdot\omega}`$, $`\upsilon_{\Lambda_{\varepsilon\cdot\omega}} \le \rho_L`$, and LIFT-0 and
  O$`^C`$ at every level (§1.3).
- The lower-bound program below $`\theta_0`$: not worked on in this round ($`\iota(\mathrm{CH}_5) \ge \psi_{\Omega_1}(S_*)`$; past $`S_*`$ the conjecture LEX-SELF). The step below SRO: no change (done for every
  $`n`$ on all 3,166 sample matrices; only the general statement for all standard matrices below SRO is open).

### 1.5 Checks of the forty-seventh round

Each run was under 60 seconds; none is a proof.

- §1.1. The author: twelve checks of names, the domain of $`L`$, normality (400 multipliers), the readings (order on 16,770 and 19,460 pairs), the tiers, the values, and the reading without
  constants (27,028 pairs), 0 failures. The referee: 440 offsets with 219 prefixes above the author's range at four bases, 260 multipliers with $`\psi_{\Omega_3}`$- and $`\psi_{\Omega_4}`$-atoms, and
  1,541 codes for the cover lemma, 0 failures.
- §1.2. The author: four runs on the caps, the table of base points and the codes above $`Z^{\mathrm{V}}`$, 0 failures (a first run of the second used a wrong cap in the author's own script; the
  proof text was not affected). The referee ran no search: the blocking point is about the range of an induction.
- §1.3. Lean: each of the eight modules alone and all together, green, and a false statement added at the end fails; the audit's own bundle with the axioms of all 116 theorems, green; the
  repository build of the whole library is green, with no `sorry`; all seven Cited\* files build with free variables forbidden, and the control fails.

### 1.6 Open

- Above $`Z^\theta`$: the pins at links of codes in $`[\theta, P')`$ (the relative far pin one level up; conjecture: up to $`L(\theta'_2\cdot\theta'_2)`$), the reading with $`\Omega_\omega`$ in its tuple,
  the conjecture THETA″$`^{\mathrm{READ}}`$, and the crossings of long restarts of level 3 from the code $`G''(\theta'_3\cdot\omega^2)`$; $`r(Z^\theta)`$; then CAP-0″ up to $`L(\Omega_\omega)`$, CAP-1″,
  LONG-CLASS at level 4, (H2$`^{\mathrm{cr}}`$), LEFT⁺ one level up, (H3), NU-CT$`_3`$ and $`\nu_3`$.
- The claim above $`Z^\theta`$ given FRAG in $`R_2^C`$ (above $`X_4`$ without FRAG), and above $`Z^{\mathrm{V}}`$ in $`R_2^S`$ (the step past $`Z^{\mathrm{V}}`$ with $`r(Z^{\mathrm{V}})`$ of §1.1 needs a review;
  then CAP$`^{\mathrm{V}}`$ (ii), the reaches of the restarts of code $`G''(\omega^2)`$ above $`Z^{\mathrm{V}}`$).
- Lean, in order: BLK$`^O`$ at $`\Lambda_{\varepsilon\cdot\omega}`$ and past it (the term $`\omega^{\varepsilon+1}`$, then $`\varepsilon_{x+2}`$ and the Veblen terms in $`x`$); the InaccPsi names of $`\Lambda_\varepsilon`$, $`\Lambda_{\varepsilon+1}`$,
  $`\Lambda_{\varepsilon\cdot 2}`$, $`\Lambda_{\varepsilon\cdot\omega}`$; the rest of LIFT-0 (the closure of $`[0, s_k)`$ under reaches, the reaches in the gaps, Theorem SH); a notation bound for $`\nu_C`$
  (target $`L(\omega+1)`$); the $`R_2^S`$ side.
- $`R_2^S = R_2^C`$: (E), $`\beta_0`$, FAN-LOAD, and the converse for $`\le_1`$ at successor stages above $`\kappa_C`$.
- Bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$, and an upper bound for $`\iota(\mathrm{CH}_3)`$.
- The first inaccessible (not worked on in this round): past $`S_*`$, capacities with $`\alpha \ge \Gamma_0`$ (conjecture LEX-SELF) or another way; then the tower of $`\Omega`$'s up to $`\theta_0`$; $`\mathrm{CH}_2`$ past
  $`\Theta_1`$; the step for all standard matrices below SRO.
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; an InaccPsi formula for the reach in terms of the code; the rest of [COVER.md](COVER.md) §9.
