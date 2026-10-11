[← Back](README.md) | [English](LEAN.md) | [Japanese](LEAN-ja.md)

# $`R_2^+`$ in Lean: $`R_2^C`$, the core, FRAG, and the restart blocks below $`\Phi_\Gamma`$

This page describes the Lean files of the directory [R2/](R2/) (namespace `Googology.Trans.PoR.InaccPsi.R2`), added in the fortieth round ([SHIFT10.md](SHIFT10.md) §3.3, stage 1), the
forty-first round ([SHIFT11.md](SHIFT11.md) §1.3, stage 2) the forty-second round ([SHIFT11.md](SHIFT11.md) §2.3, stage 3), the forty-third round ([SHIFT11.md](SHIFT11.md) §3.3, stage 4) and the forty-fourth round ([SHIFT12.md](SHIFT12.md) §1.3, stage 5). Every file builds as a module with the whole library (`lake build`, green, no `sorry`). The audit of each stage found every axiom
faithful to the paper it cites, every definition right, and every main theorem proved by Lean; it found no fatal and no blocking point.

**What this changes.** Almost every result above $`\upsilon_{\omega\cdot\omega}`$ on the other pages is stated "given FRAG". FRAG is now a Lean theorem whose only non-standard axioms are 20
facts cited from two papers of Wilken (and 7 constants for the objects of those papers). So "given FRAG" can be read as "given these 20 cited facts". The second stage adds INC1, Carlson's theorems on the core and Theorem CP. The third stage adds Lemma L and the structure of $`R_2^C`$ below $`\upsilon_{\omega^3}`$
(the first pair, Theorems B and B″ with TOP, RS and SK3). The fourth stage adds the restart blocks over restart indices that are ordinals: Lemmas TOP$`_\lambda`$ and RS$`_\lambda`$, Theorem BLK$`^\Xi`$, Theorem BLK$`^O`$ with the closed form of OFF-V below $`V_\omega(1)`$, and CORE-C below $`V_\omega(1)`$, with no new axiom. The fifth stage adds five cited facts and, with them, Theorem BLK$`^O`$ at every ordinal level up to $`\Lambda_\Gamma`$ and below $`\Phi_\Gamma`$, and CORE-C below $`\Phi_\Gamma`$. The axioms are in five files, Cited, CitedR1, CitedC09, CitedL and CitedW: 49 axioms in all (10 constants and 39 facts).
These counts, and every count of axioms on this page, leave out Lean's three standard axioms `propext`, `Classical.choice`, `Quot.sound` (so a raw `#print axioms` lists three more).

## 1. The files

| file | content | axioms used |
|---|---|---|
| [R2/Defs.lean](R2/Defs.lean) | $`R_2^C`$ defined from Carlson 2009: closed sets (Def 2.1, 2.3), coverings (Def 5.2), $`\le_1^\infty`$ and $`\le_2^\infty`$ (Def 5.3), $`\le_1`$, $`\le_2`$ by recursion on the right end (Def 5.4); isomorphisms, $`\le_{pw}`$, isominimal sets and the core (Def 2.6) for any interpretation | none |
| [R2/Basic.lean](R2/Basic.lean) | the recursion equations; basic facts of $`\le_1`$, $`\le_2`$; the reach | none |
| [R2/Loc.lean](R2/Loc.lean) | Lemma LOC and its corollary | none |
| [R2/Cited.lean](R2/Cited.lean) | the axioms of stage 1 (§2.1) | — |
| [R2/Points.lean](R2/Points.lean) | $`\upsilon`$-points of $`R_1^+`$, segments, restarts $`\rho_\lambda`$, reaches $`r(\lambda)`$ | cited |
| [R2/Frag.lean](R2/Frag.lean) | Lemma ST, FRAG with one base on the whole domain | cited |
| [R2/FragBase.lean](R2/FragBase.lean) | closure, components, segments, the domains $`D_k`$, one base change on a set, the case analysis | cited |
| [R2/FragM.lean](R2/FragM.lean) | heights, the compression step, Theorem FRAG for any number of bases | cited |
| [R2/Frag2.lean](R2/Frag2.lean) | Theorem FRAG2 for the Lean $`R_2^C`$ | `le1R` only |
| [R2/Arith.lean](R2/Arith.lean) | Carlson 2009, L.4.4, L.4.5 (closed embeddings), L.5.5 (7); components and closed sets | none |
| [R2/CitedC09.lean](R2/CitedC09.lean) | the two axioms from Carlson 2009 (§2.3) | — |
| [R2/CoreC.lean](R2/CoreC.lean) | the core from Thm 14.10 and 14.14: isominimal sets are least, the core is an initial segment, core points have reaches | C09 |
| [R2/Move.lean](R2/Move.lean) | Lemma MOVE; Theorems CP\* and CP | none / C09 |
| [R2/CitedR1.lean](R2/CitedR1.lean) | the eleven axioms on $`R_1^+`$ and $`T^\tau`$ added in stage 2 (§2.2) | — |
| [R2/Ups.lean](R2/Ups.lean) | the Lean $`\upsilon`$ is Wilken's $`\upsilon`$ (Wilken 2020, Def 21.4); $`\upsilon_n`$, $`\upsilon_\omega`$ countable | cited |
| [R2/R1Gap.lean](R2/R1Gap.lean) | the reach of $`R_1^+`$, gaps, $`\lt_1`$-predecessors inside a gap | cited |
| [R2/CCF.lean](R2/CCF.lean) | Theorem CC-F (closed covering copies in $`R_1^+`$) | cited |
| [R2/Inc1.lean](R2/Inc1.lean) | LEFT-AT, FANCOF, PI2-UP, CLEAN-C, NOBAD; Theorem INC1 | cited |
| [R2/BlockC.lean](R2/BlockC.lean) | RIGHT-LIM, LEFT with a limit index, RE-U, SK1 in a block, $`R_2^C = R_1^+`$ for $`\le_1`$ below the first pair, FRAG2 and FRAG with the reduced skeleton | cited |
| [R2/CitedL.lean](R2/CitedL.lean) | the four axioms of stage 3 (§2.4) | — |
| [R2/ChainL.lean](R2/ChainL.lean) | Lemma L (the bound on chains, also inside a gap) | cited (16) |
| [R2/BaseC.lean](R2/BaseC.lean) | the base change and its inverse keep additive principal numbers and $`\le_1`$ of $`R_1^+`$; closed images | cited |
| [R2/Pair1.lean](R2/Pair1.lean) | Theorem A in $`R_2^C`$: the first pair $`\upsilon_\omega \lt_2 \upsilon_{\omega+1}`$; Lemma COMP-C | cited (35) |
| [R2/BlockB.lean](R2/BlockB.lean) | SK1 in a block; Theorem B (the pairs below $`\upsilon_{\omega\cdot\omega}`$) | cited (35) |
| [R2/RstC.lean](R2/RstC.lean) | a restart and its first block: Lemma C″ (a), B″4, TOP | cited (35) |
| [R2/Blk3.lean](R2/Blk3.lean) | every restart below $`\upsilon_{\omega^3}`$: Theorem B″, the pairs below $`\upsilon_{\omega^3}`$, SK3 | cited (35) |
| [R2/RS.lean](R2/RS.lean) | Lemmas RS and RS$`^h`$: the reach of $`\rho_h`$ | cited (41) |
| [R2/RstK.lean](R2/RstK.lean) | a restart context without caps below the restart; the lemmas of stage 3 that do not use the caps; **Lemma TOP with an offset** for the terms $`x\cdot m + k`$ | cited (35) |
| [R2/Off.lean](R2/Off.lean) | $`\Xi`$ (the derivative of $`\upsilon`$), $`\Xi_\omega`$; $`c(\lambda) = -1 + \mathrm{logend}(\lambda)`$ and the offset $`c^*`$; the offset lemma up to $`\Xi_\omega`$ | cited (≤ 14) |
| [R2/BlkX.lean](R2/BlkX.lean) | the block structure along the restart indices for any offset with the needed inputs, without FRAG; TOP$`_\lambda`$ | cited (35) |
| [R2/RSX.lean](R2/RSX.lean) | **Lemma RS with a restart target**; RS$`_\lambda`$; **Theorem BLK$`^\Xi`$**; the reaches at $`\omega^e`$, $`\Xi_n`$, $`\Xi_\omega`$ | cited (41) |
| [R2/OffPhi.lean](R2/OffPhi.lean) | $`\mathrm{logend}`$; $`\Phi_1`$; the offset below $`\Phi_1`$; BLK$`^O`$ below $`\Phi_1`$ | cited (41) |
| [R2/OffV.lean](R2/OffV.lean) | $`V_n`$, $`V_\omega(1)`$, the closed form of OFF-V; **Theorem BLK$`^O`$ below $`V_\omega(1)`$**; the reaches at $`V_n(\alpha)`$ and $`\Phi_1`$ | cited (41) |
| [R2/CoreX.lean](R2/CoreX.lean) | **CORE-C**: $`[0, V_\omega(1)) \subseteq \mathrm{Core}(R_2^C)`$ | cited (35) + C09 |
| [R2/CitedW.lean](R2/CitedW.lean) | the five axioms of stage 5 (§2.5); $`\bar\omega`$, the enumeration of the additive principal numbers that are not $`\varepsilon`$-numbers (a definition) | — |
| [R2/FragX.lean](R2/FragX.lean) | FRAG with one more conclusion: on $`D_1`$ the map is the single base change $`\pi`$ | cited (27) |
| [R2/Exact.lean](R2/Exact.lean) | $`\bar\omega_{\tau+\alpha} = \omega^{\tau+1+\alpha}`$ below the next $`\varepsilon`$-number (no axiom); $`\vartheta^\tau(\gamma) = \omega^{\tau+\gamma}`$; the base change of $`\omega^{r+\gamma}`$, $`r\cdot\gamma`$, $`r\cdot r`$ | cited (≤ 11) |
| [R2/RSG.lean](R2/RSG.lean) | the terms $`x\cdot\gamma + e`$, $`x\cdot x + e`$; **Lemma EXACT**; **Lemma RS with a restart target** for these terms | cited (45) |
| [R2/TopG.lean](R2/TopG.lean) | **Lemma IMG** (a copy does not make these terms smaller); **Lemma TOP$`^O`$** for these terms, without FRAG | cited (36) |
| [R2/BlkG.lean](R2/BlkG.lean) | the block structure along the restart indices for these terms | cited (46) |
| [R2/OffG.lean](R2/OffG.lean) | $`V_\gamma`$ for every ordinal $`\gamma`$, $`\Lambda_\Gamma`$, the level and the offset; **Theorem BLK$`^O`$ up to $`\Lambda_\Gamma`$**; the reaches at $`V_\gamma(\alpha)`$, $`V_\omega(1)`$, $`\Lambda_\Gamma`$; CORE-C there; the interval form of the reach | cited (46) + C09 |
| [R2/OffG2.lean](R2/OffG2.lean) | the Γ-points, their enumeration $`G_\Gamma`$ and its first fixed point $`\Phi_\Gamma`$; **Theorem BLK$`^O`$ below $`\Phi_\Gamma`$**; the reaches at the Γ-points; **CORE-C below $`\Phi_\Gamma`$** | cited (46) + C09 |

Two readings in [R2/Defs.lean](R2/Defs.lean) are equivalent to Carlson's text and are explained there: clauses (c) and (d) of $`\le_2^\infty`$ are one covering (a covering of finite sets is the order
isomorphism), and "any finite structure" ranges over finite closed sets of ordinals with relations (every finite arithmetic structure is isomorphic to one, Carlson 2009, remark after L.4.6).
"Cofinally many below $`c`$" is read strictly (for every $`c' \lt c`$ a copy above $`c'`$), as in the proof of Carlson 2009, L.5.5 (1).

## 2. The axioms

### 2.1 Stage 1 ([R2/Cited.lean](R2/Cited.lean))

No axiom of this file (or of CitedR1) mentions $`R_2^C`$. A misreading of Carlson's definition could only make the Lean $`R_2^C`$ differ from Carlson's; it cannot make the axioms inconsistent. The axioms are about
$`R_1^+ = (\mathrm{Ord}; 0, +, \le, \le_1)`$ and about Wilken's term systems $`T^\tau`$ with the base change $`\pi_{\sigma,\tau}`$, always for $`\varepsilon`$-numbers $`\sigma \lt \tau \lt \Omega_1`$, with $`\Omega_1 = \omega_1`$.

Papers: [W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161; [W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.

**7 constants** (objects of the papers, not defined in Lean): `le1R` ($`\le_1`$ of $`R_1^+`$), `Tset` ($`T^\tau`$), `Par` ($`\mathrm{Par}^\tau`$, [W07a] Def 3.28), `pi` ($`\pi_{\sigma,\tau}`$, [W07a] Def 5.1), `ht` (heights,
[W07a] L.3.27), `Dl` and `Dp` (the terms $`\vartheta^\tau(\Delta_n)`$ and $`\vartheta^\tau(\Delta_n + 1)`$).

**20 facts:**

| axiom | statement (short) | source |
|---|---|---|
| `le1R_trans`, `le1R_le`, `le1R_of_le` | $`\le_1`$ is transitive, inside $`\le`$, and has the interval property | [W07b] L.2.1 and §1 (statement in [W07b] §2) |
| `le1R_two_iff` | for $`a \gt 0`$: $`a \le_1 a\cdot 2`$ iff $`a`$ is an $`\varepsilon`$-number | [W07b], remark after Thm 2.2 |
| `TB_inter_lt` | $`T^\tau[\sigma] \cap \tau = \sigma`$ | [W07a], proof of L.5.3 |
| `pi_lt`, `pi_base`, `pi_Om1` | $`\pi`$ fixes the ordinals below $`\sigma`$, sends $`\tau`$ to $`\sigma`$, fixes $`\Omega_1`$ | [W07a] Def 5.1 (with the proof of L.3.27 and the remark after Def 3.1) |
| `pi_bijOn`, `pi_add`, `pi_ht_Par` | $`\pi`$ is an order isomorphism, keeps $`+`$, heights and parameters | [W07a] L.5.3 (b)–(e), Cor 5.4 |
| `lh_pi` | $`\pi`$ keeps the reach $`\mathrm{lh}`$ of $`R_1^+`$ | [W07b] L.4.4, Thm 5.3, Cor 5.7 |
| `T_inter_Om1` | $`T^\tau \cap \Omega_1`$ is the least $`\alpha \gt \tau`$ with $`\alpha \le_1`$ everything above | [W07b] Cor 5.10 |
| `Par_lt`, `Par_comps` | parameters of small ordinals and of sums | [W07a] Def 3.28 |
| `ht_spec`, `Dl_spec` | heights; the terms $`\vartheta^\tau(\Delta_n)`$ | [W07a] L.3.27, Def 3.26 |
| `Dl_E` | $`\vartheta^\tau(\Delta_n)`$ is an $`\varepsilon`$-number above $`\tau`$ | [W07a] L.4.3, Def 3.28 |
| `Dp_spec` | $`\alpha^+ = \vartheta^\alpha(\Delta)`$ | [W07a] Conv. 4.1, L.6.3 |
| `par_track` | parameters after a change of base | [W07a] L.6.10 with L.6.3 and L.3.30 |

Eight axioms join 2–3 cited clauses into one statement; the audit checked each join. In `par_track` Lean asks closure under components only, the paper under components and partial sums;
adding the partial sums does not change the closure, so the Lean axiom follows from the paper's lemma. Three facts on $`R_1^+`$ (`le1R_trans`, `le1R_of_le`, `le1R_two_iff`) are proved in
Wilken, AML 45 (2006), which we do not have; their statements are in [W07b] §2. The audit found no conflict between the axioms; it found no small model either (a cheap model of the facts on
$`R_1^+`$ fails `Dl_E`), so the consistency rests on the papers' objects.

### 2.2 Stage 2, $`R_1^+`$ and $`T^\tau`$ ([R2/CitedR1.lean](R2/CitedR1.lean))

Same conventions as §2.1 ($`\Omega_1 = \omega_1`$, bases $`1`$ or $`\varepsilon`$-numbers, countable). Paper added: Wilken, "A glimpse of Σ₃-elementarity" (2020).

| axiom | statement (short) | source |
|---|---|---|
| `le1R_refl` | $`\le_1`$ is reflexive | [W07b] L.2.1 |
| `le1R_limit` | if $`a \le_1 b`$ for all $`b \in [a, \lambda)`$, $`\lambda \gt a`$ a limit, then $`a \le_1 \lambda`$ | [W07b] L.2.1 (a) |
| `le1R_lim_P` | if $`a \le_1 b`$ for some $`b \gt a`$, then $`a`$ is a limit of additive principal numbers | [W07b], remark after Thm 2.2 |
| `tauW` (constant), `tauW_normal` | Wilken's points $`\tau_\xi`$ are strictly increasing and continuous | [W07a] Def 9.1 |
| `ltInf1_iff_tauW` | $`a \lt_1 \infty`$ iff $`a = \tau_\rho`$ for some $`\rho`$ | [W07b] Cor 5.10 |
| `T_inter_Om1_one` | $`T^1 \cap \Omega_1`$ is the least $`a \gt 1`$ with $`a \lt_1 \infty`$ | [W07b] Cor 5.10 with [W07a] Thm 3.23 |
| `T_one_bound` | $`T^1 \cap \Omega_1`$ is a supremum of countably many countable ordinals | [W07a] Thm 3.23 with L.3.30 |
| `le1R_copy` | the finite-set criterion for $`a \le_1 b`$ (direction "$`\Rightarrow`$") | Wilken 2020, Prop 21.6 |
| `le1R_loc` | the $`\tau`$-localization of an additive principal number | [W07b] Def 5.8, Cor 5.9 |
| `claim56` | no covering of a certain finite set fixes its lower part | [W07b] Claim 5.6 (proof of Thm 5.3) |

The audit found all of them faithful. The Lean form of `claim56` asks for less (fewer maps count as coverings), so it is weaker than the paper's claim. `le1R_refl`, `le1R_limit` and
`le1R_lim_P` restate results of Wilken, AML 45 (2006), which we do not have; their statements are in [W07b] §2. Wilken 2020 credits Prop 21.6 to Carlson, AML 38 (1999), which we do not
have either, but it reprints the proof, so nothing is taken from that paper. A cheap model of the facts on $`R_1^+`$ breaks `claim56`, so it is no model; the audit found no conflict.

### 2.3 Stage 2, Carlson 2009 ([R2/CitedC09.lean](R2/CitedC09.lean))

| axiom | statement (short) | source |
|---|---|---|
| `C09_thm14_10` | for a finite closed set $`A`$ of $`R_2^C`$ there is $`P^*`$ isomorphic to $`A`$, pointwise below every closed $`Q`$ that is a covering of $`P^*`$, and isominimal | Carlson 2009, Thm 14.10 (1)–(3) |
| `C09_thm14_14` | the core of $`R_2^C`$ is the least $`\kappa`$ with $`\kappa \le_1`$ everything above it, or all of Ord if there is none | Carlson 2009, Thm 14.14 |

These are the first axioms that mention $`R_2^C`$: they would be false if the Lean $`R_2^C`$ differed from Carlson's (both audits found the definitions literal). The Lean form of Thm 14.10
also allows sets without $`0`$; that case follows from the case with $`0`$, since $`0 \le_i b`$ only for $`b = 0`$ and coverings keep $`0`$ out.

### 2.4 Stage 3 ([R2/CitedL.lean](R2/CitedL.lean))

| axiom | statement (short) | source |
|---|---|---|
| `lhT` (constant) | $`\mathrm{lh}^\tau(\alpha)`$, defined for $`\alpha \in T^\tau \cap \Omega_1`$ | [W07b] Def 4.1 |
| `lh_eq_lhT` | for $`\tau \in \{1\} \cup E`$ countable and $`\alpha \in T^\tau`$ additive principal with $`\tau \lt \alpha \lt \Omega_1`$, the reach of $`\alpha`$ in $`R_1^+`$ is $`\mathrm{lh}^\tau(\alpha)`$ | [W07b] Thm 5.3 |
| `ht_lhT_lt` | for such $`\alpha`$ that is an $`\varepsilon`$-number: $`\mathrm{ht}_\alpha(\mathrm{lh}^\tau(\alpha)) \lt \mathrm{ht}_\tau(\alpha)`$ | [W07b] L.4.5 |
| `Par_sub` | $`\mathrm{Par}^\tau(\alpha) \subseteq \tau`$ (stated for $`\tau \in E`$ only; the paper also has $`\tau = 1`$, which is not needed) | [W07a] Def 3.28 |

The audit found all four faithful. "$`\alpha = \vartheta^\tau(\Delta + \eta)`$" of the paper is read as "$`\alpha`$ is additive principal", by the join already in CitedR1, and "$`\Delta \gt 0`$" as
"$`\alpha`$ is an $`\varepsilon`$-number" ([W07a] L.4.3). No new axiom mentions $`R_2^C`$, and no theorem of stage 3 uses an axiom of CitedC09.

### 2.5 Stage 5 ([R2/CitedW.lean](R2/CitedW.lean))

| axiom | statement (short) | source |
|---|---|---|
| `le1R_thm22` | for $`0 \lt \xi \le \alpha`$: $`\alpha \le_1 \alpha + \xi`$ in $`R_1^+`$ iff $`\alpha = \omega^{\alpha'}`$ with $`\alpha' \ne 0`$ and $`\xi \le \mathrm{logend}(\alpha')`$ | [W07b] Thm 2.2 (statement in §2) |
| `vt` (constant) | $`\vartheta^\tau`$ ($`\vartheta_0`$ over the base $`\tau`$) | [W07a] Def 3.22, Conv. 3.25 |
| `vt_wbar` | for $`\tau \in E`$ countable and $`\alpha \lt \Omega_1`$: $`\vartheta^\tau(1+\alpha) = \bar\omega_{\tau+\alpha}`$ | [W07a] L.4.2 ($`m = 0`$) |
| `vt_mem` | for $`\xi \in T^\tau`$, $`\xi \lt \Omega_1`$: $`\vartheta^\tau(\xi) \in T^\tau`$ with the parameters of $`\xi`$ | [W07a] Def 3.22, Def 3.28, L.3.30 |
| `pi_vt` | the base change of a $`\vartheta^\tau`$-term: $`\pi(\vartheta^\tau(\eta)) = \vartheta^\sigma(\pi(\eta))`$ | [W07a] Def 5.1, fourth clause |

The audit found all five faithful and checked them for consistency with the earlier axioms (`le1R_thm22` with $`\xi = \alpha`$ is `le1R_two_iff`, and it agrees with `le1R_lim_P`). **[W07b] Thm 2.2 is
cited from its statement only**: its proof is in Wilken, AML 45 (2006), which is not used. $`\Omega_1`$ of [W07a] is an uncountable regular cardinal above $`\tau`$; here, as in Cited.lean, it is
$`\omega_1`$. `vt_wbar` is stated for every $`\alpha \lt \Omega_1`$, as in the paper ($`\vartheta_0`$ is a function on $`\vartheta_1 \gt \Omega_1`$).

## 3. The theorems

"None" means only Lean's standard axioms `propext`, `Classical.choice`, `Quot.sound` (by `#print axioms`).

| theorem | statement | axioms |
|---|---|---|
| `le1_iff`, `le2_iff` | the recursion equations of Carlson 2009, Def 5.4 | none |
| `le1_refl`, `le1_trans`, `le1_le`, `le1_antisymm`, `le2_refl`, `le2_trans`, `le2_le1`, `le2_le` | $`\le_1`$, $`\le_2`$ are reflexive and transitive, $`\le_2 \subseteq \le_1 \subseteq \le`$ | none |
| `le2_of_le1` | Carlson 2009, L.5.5 (6) | none |
| `le1_of_le_of_le1`, `le1_limit` | interval and limit properties of $`\le_1`$ | none |
| `cof_core`, `le1_cof` | Carlson 2009, L.5.5 (1) | none |
| `exists_closed` | Carlson 2009, L.2.5 for $`(\mathrm{Ord}; 0, +, \le)`$ | none |
| `exists_reach`, `reach_spec` | $`\mathrm{lh}(x)`$ exists unless $`x \le_1`$ every larger ordinal | none |
| `isominimal_congr` | Lemma LOC: whether a finite set is isominimal depends only on the structure up to its largest element | none |
| `core_subset_of_agree` | if $`R`$ and $`R'`$ agree below $`\kappa`$ and $`\mathrm{Core}(R) \subseteq \kappa`$, then $`\mathrm{Core}(R) \subseteq \mathrm{Core}(R')`$ | none |
| `upsPt_inE`, `le1R_lt_ups`, `exists_next` | a $`\upsilon`$-point is an $`\varepsilon`$-number; $`\le_1`$ across a $`\upsilon`$-point; the next $`\upsilon`$-point | cited |
| `st_le1` | Lemma ST: the base change keeps $`\le_1`$ both ways | cited (8) |
| `frag1` | FRAG with one base on the whole domain | cited (16) |
| `frag` | **Theorem FRAG**: for a countable $`\upsilon`$-point $`\kappa`$, countable $`\upsilon`$-points $`b_0 \lt \dots \lt b_{m-1}`$ and $`c_0 \lt \dots \lt c_{m-1}`$ above $`\kappa`$, and a finite $`F \subseteq D_m`$, there is $`\Psi`$ that is the identity below $`\kappa`$, sends $`b_k`$ to $`c_k`$ and the segment of $`b_k`$ into that of $`c_k`$, keeps $`0, +, \le`$ and $`\le_1`$ of $`R_1^+`$ both ways, and keeps $`\upsilon`$-points and $`\varepsilon`$-numbers | cited (all 27) |
| `frag2` | **Theorem FRAG2**: if $`R_2^C`$ is skeletal on $`Y \cup \Psi[Y]`$, a map that keeps $`0, +, \le`$, $`\le_1`$ of $`R_1^+`$ and the $`\upsilon`$-points is an isomorphism of $`R_2^C`$ on $`Y`$ iff it keeps the caps and the pairs of $`\upsilon`$-points | `le1R` |

**Stage 2.**

| theorem | statement | axioms |
|---|---|---|
| `le_of_le_on_indec`, `ext_arithIso`, `ext_closed`, `ext_unique` | Carlson 2009, L.4.4 and L.4.5: an order-preserving map of the additive principal numbers of a closed set extends uniquely to a closed embedding | none |
| `indec_of_lt1`, `indec_of_lt2_right` | Carlson 2009, L.5.5 (7) | none |
| `isominimal_least` | an isominimal set is pointwise below every closed set it covers | Thm 14.10 |
| `core_downward`, `exists_reach_of_core`, `core_subset_of_agree_C` | the core is an initial segment; every core point has a reach; the corollary of LOC without its hypothesis | Thm 14.14 |
| `move` | Lemma MOVE: moving one additive principal point down gives a covering | none |
| `cp_star`, `cp` | Theorems CP\* and CP: an additive principal core point $`u`$ whose reach has $`\le_1`$-predecessors cofinal below $`u`$ is the left end of a pair | Thm 14.10 (`cp'` also Thm 14.14) |
| `upsilon_normal`, `upsPt_iff_upsilon`, `upsilon_succ_T`, `upsilon_omega_lt_Om1` | the Lean $`\upsilon`$ satisfies Wilken 2020, Def 21.4, is normal; $`\upsilon_n`$, $`\upsilon_\omega`$ are countable | cited |
| `ccf` | Theorem CC-F | cited |
| `inc1` | **Theorem INC1**: $`a \le_1 b`$ in $`R_2^C`$ and $`b \lt \Omega_1`$ give $`a \le_1 b`$ in $`R_1^+`$ (no axiom about $`R_2^C`$) | cited (16) |
| `left`, `left_limit`, `fan_right_ups`, `right_lim`, `re_u` | LEFT (a countable $`\lt_2`$-left end is $`\upsilon_\lambda`$, $`\lambda`$ a limit), NOBAD, RIGHT-LIM, RE-U | cited |
| `block_le1_iff`, `le1_iff_le1R_below`, `le1_iff_le1R_upsilon_omega` | SK1 inside a block; $`\le_1`$ of $`R_2^C`$ equals $`\le_1`$ of $`R_1^+`$ below the first $`\lt_2`$-right end and on $`[0, \upsilon_\omega]`$ | cited |
| `frag2_C`, `frag_frag2_C` | FRAG2 with the skeleton hypothesis reduced by INC1 and LEFT; a FRAG map with it | cited |

The proof of INC1 uses [W07b] Cor 5.9 (finitely many $`\lt_1`$-predecessors inside a gap) in place of the project's Lemma L, which makes it simpler. The audit printed the axioms of 101
theorems; every one uses only Lean's three standard axioms and the 40 cited ones.

**Stage 3.** In `rI`, `rstCtx`, `thmB2_C`, `rs_h` and `reach_rst` the Lean index is one less than the paper's (Lean $`h`$ = paper $`h - 1`$): Lean's $`h`$ is the restart $`\rho_{h+1} = \upsilon_{\omega^2(h+1)}`$. The doc lines of these files say so since stage 4, and that of `Par_sub` says that it is stated for $`\tau \in E`$ only.

| theorem | statement | axioms |
|---|---|---|
| `chain_bound`, `chain_bound_gap` | **Lemma L**: for $`\tau \in \{1\} \cup E`$ and $`z_0 \in T^\tau \cap (\tau, \Omega_1)`$, a chain $`z_0 \lt_1 \dots \lt_1 z_k`$ of $`R_1^+`$ has $`k \le \mathrm{ht}_\tau(z_0) + 1`$; the same inside a gap | cited (16) |
| `thmA_C`, `first_pair` | **Theorem A**: $`\upsilon_\omega \lt_2 \upsilon_{\omega+1}`$ is the least pair of $`R_2^C`$, with $`\upsilon_\omega`$ its only left end; $`\le_1 = \le_1`$ of $`R_1^+`$ up to $`\upsilon_{\omega+1}`$; no point at most $`\upsilon_{\omega+1}`$ is $`\le_1`$ to a larger point | cited (35) |
| `comp_c` | **Lemma COMP-C**: the compression of a segment (Theorem CC-F, then the inverse base change) is a covering of $`R_2^C`$ | cited (35) |
| `thmB_C` | **Theorem B**: below $`\upsilon_{\omega\cdot\omega}`$ the pairs are exactly $`(\upsilon_{\omega(j+1)}, \upsilon_{\omega(j+1)+1})`$; caps at the block tops; $`\le_1`$ of $`R_1^+`$ inside the blocks | cited (35) |
| `thmB2_C` | **Theorem B″ with TOP**, for every restart below $`\upsilon_{\omega^3}`$ (its seven clauses, [SHIFT11.md](SHIFT11.md) §2.3) | cited (35) |
| `rs_h`, `reach_rst` | **RS, RS$`^h`$**: $`\rho_h \le_1 \delta_h + 1`$, and $`\mathrm{lh}(\rho_h) = \delta_h + 1`$ | cited (41) |
| `pairs_lt_w3` | the pairs below $`\upsilon_{\omega^3}`$ are exactly $`(\upsilon_\xi, \upsilon_{\xi+1})`$, $`\xi = \omega^2 h + \omega j + \omega`$ | cited (35) |
| `sk3_C` | **SK3**: below $`\upsilon_{\omega^3}`$ every point that is not a $`\upsilon`$-point has $`\le_1`$ of $`R_1^+`$ to every $`\gamma`$ | cited (35) |
| `not_le1_zero` | $`0 \le_1 b`$ in $`R_2^C`$ only for $`b = 0`$ | none |

The audit printed the axioms of the eleven main statements; together they use 41 of the 44 cited axioms. Each module was also checked alone with only the modules it imports, and a
false statement added at the end made that check fail.

**Stage 4.** No new axiom. Here $`\Xi_\alpha`$ is the $`\alpha`$-th nonzero fixed point of $`\iota \mapsto \upsilon_\iota`$, $`V_0 = \upsilon`$, $`V_{n+1}`$ is the derivative of $`V_n`$, $`V_\omega(1) = \sup_n V_{n+1}(1)`$, $`\Phi_1 = V_2(1)`$, and
$`c^*(\lambda) = -1 + \mathrm{logend}(\lambda)`$ below $`\Xi_\omega`$, $`c^*(\Xi_\omega) = \Xi_\omega + 1`$ ([REACHES.md](REACHES.md) §1).

| theorem | statement | axioms |
|---|---|---|
| `RstK.top_gen` | **Lemma TOP with an offset**: in a restart context without caps below $`\rho`$, for a term $`t(x) = x\cdot m + k`$, if no pair above some $`x_0 \lt \rho`$ has a point that reaches past its right end by more than the term allows, then $`\rho`$ is not $`\le_1`$ to any point above $`\delta + t(\rho)`$ | cited (35) |
| `rs_rst` | **Lemma RS with a restart target**: if restarts $`\rho_\mu`$ cofinal below $`\rho_r`$ satisfy $`\rho_\mu \le_1 \delta_\mu + t(\rho_\mu)`$, then $`\rho_r \le_1 \delta_r + t(\rho_r) + 1`$ (by FRAG) | cited (41) |
| `rs_all`, `reach_all` | **RS$`_\lambda`$ and TOP$`_\lambda`$**: $`\mathrm{lh}(\rho_\lambda) = \delta_\lambda + c^*(\lambda)`$ for every restart index $`\lambda \le \Xi_\omega`$ | cited (41) |
| `blkXi` | **Theorem BLK$`^\Xi`$**: (i) the $`\lt_2`$-pairs with right end below $`\upsilon_{\Xi_\omega+\omega^2}`$ are exactly the $`(\upsilon_{\mu+\omega j}, \upsilon_{\mu+\omega j+1})`$; (ii) for $`\lambda \le \Xi_\omega`$, no point below $`\rho_\lambda`$ is $`\le_1`$ to a point at or above it, $`\rho_\lambda`$ has no $`\lt_2`$-successor, and its reach is $`\delta_\lambda + c^*(\lambda)`$; (iii) every point below the bound that is not a $`\upsilon`$-point has the $`\le_1`$ of $`R_1^+`$ | cited (41) |
| `blkPhi`, `blkV` | **Theorem BLK$`^O`$** below $`\Phi_1`$ and below $`V_\omega(1)`$, with the closed form of OFF-V: the offset is $`c(\lambda)`$ at level 0 and $`\rho\cdot n + \mathrm{logend}(\alpha)`$ at $`\lambda = V_n(\alpha)`$ | cited (41) |
| `reach_w3`, `reach_ww`, `reach_Xi`, `reach_XiW`, `reach_XiA`, `reach_Phi1`, `reach_Vn` | the reaches $`\delta + 2`$ at $`\omega^3`$, $`\delta + \omega`$ at $`\omega^\omega`$, $`\delta + \Xi_n`$ at $`\Xi_n`$, $`\delta + \Xi_\omega + 1`$ at $`\Xi_\omega`$, $`\delta + \Xi_\alpha + \mathrm{logend}(\alpha)`$ at $`\Xi_\alpha`$ ($`\alpha \lt \Phi_1`$), $`\delta + \Phi_1\cdot 2`$ at $`\Phi_1`$, $`\delta + V_n(\alpha)\cdot n + \mathrm{logend}(\alpha)`$ at $`V_n(\alpha)`$ | cited (41) |
| `core_Xi`, `core_Phi`, `core_V` | **CORE-C**: $`[0, \upsilon_{\Xi_\omega+\omega^2})`$, $`[0, \Phi_1)`$ and $`[0, V_\omega(1))`$ are contained in $`\mathrm{Core}(R_2^C)`$ (without FRAG) | cited (35) + Thm 14.14 |

The audit printed the axioms of 76 theorems; together they use 42 of the 44 cited axioms (not `le1R_limit` and `C09_thm14_10`). It re-ran each module alone and all together, and found no
fatal and no blocking point. Its three minor points: (i) is about the pairs whose **right** end is below the bound (the paper's statement speaks of left ends; for restarts (ii) excludes the rest);
(iii) covers the points that are not $`\upsilon`$-points, not the $`\upsilon`$-points that are not restarts; and (ii) is stated with `IsReach` (the largest $`\gamma`$ with $`\rho \le_1 \gamma`$), and the interval
form $`\{\gamma : \rho \le_1 \gamma\} = [\rho, \delta + c^*]`$ follows with `le1_of_le_of_le1` of Basic, which uses no axiom (since stage 5 also the theorem `reach_interval`). The paper's recursive offset $`O`$ is not formalized: Lean proves the closed
form directly below $`V_\omega(1)`$. The offset terms are $`x\cdot m + k`$ with $`m`$ finite, so [W07a] L.4.2 and [W07b] Thm 2.2 are not needed; this is why the stage stops at $`V_\omega(1)`$, where the
offset $`\rho\cdot\omega`$ needs the term $`\omega^{x+1}`$.

**Stage 5.** Here $`V_\gamma`$ is the Veblen hierarchy over $`\upsilon`$ for every ordinal $`\gamma`$ (`VG`, built with Mathlib's `veblenWith`; it agrees with the $`V_n`$ and $`V_\omega(1)`$ of stage 4), a Γ-point is a $`\lambda \gt 0`$ with
$`V_\gamma(\lambda) = \lambda`$ for every $`\gamma \lt \lambda`$, $`\Lambda_\Gamma`$ is the least Γ-point (the $`\Lambda_\Gamma`$ of [REACHES.md](REACHES.md) §1), $`G_\Gamma`$ enumerates $`\{0\}`$ and the Γ-points, and $`\Phi_\Gamma`$ is the least $`\alpha \ge 1`$ with
$`G_\Gamma(\alpha) = \alpha`$.

| theorem | statement | axioms |
|---|---|---|
| `fragX` | FRAG, and on $`F \cap D_1`$ the map is the single base change $`\pi`$ (or its inverse, or the identity) | cited (27) |
| `pi_tq` | **Lemma EXACT**: $`\pi(r\cdot\gamma+e) = s\cdot\gamma+e`$ and $`\pi(r\cdot r+e) = s\cdot s+e`$ for $`\gamma, e \lt s`$ | cited (11) |
| `rs_rstG` | **Lemma RS with a restart target** for the terms $`x\cdot\gamma+e`$ and $`x\cdot x+e`$ | cited (45) |
| `RstK.wit_pow`, `RstK.wit_mul`, `RstK.wit_sq` | **Lemma IMG**: a covering copy $`f`$ with $`f(\rho)`$ a $`\upsilon`$-point has $`f(\omega^{\rho+\gamma}) \ge \omega^{f(\rho)+\gamma}`$, $`f(\rho\cdot\gamma) \ge f(\rho)\cdot\gamma`$, $`f(\rho\cdot\rho) \ge f(\rho)^2`$ | cited (35) |
| `RstK.top_tq` | **Lemma TOP$`^O`$** for these terms, without FRAG | cited (36) |
| `blkG` | **Theorem BLK$`^O`$ up to $`\Lambda_\Gamma`$**: (i)–(iii) of BLK$`^\Xi`$ for every restart index $`\lambda \le \Lambda_\Gamma`$ (right ends below $`\upsilon_{\Lambda_\Gamma+\omega^2}`$), with the offset $`c(\lambda)`$ at level 0, $`\rho\cdot\gamma + \mathrm{logend}(\alpha)`$ at $`\lambda = V_\gamma(\alpha)`$, and $`\rho\cdot\rho`$ at $`\Lambda_\Gamma`$ | cited (46) |
| `blkG2` | **Theorem BLK$`^O`$ below $`\Phi_\Gamma`$**: the same with the offset $`\rho^2 + \mathrm{logend}(\alpha)`$ at a Γ-point $`G_\Gamma(\alpha)`$ | cited (46) |
| `reach_VG`, `reach_Vw1`, `reach_LamG`, `reach_GG`, `reach_GG2`, `reach_VG2` | the reaches $`\delta + V_\gamma(\alpha)\cdot\gamma + \mathrm{logend}(\alpha)`$ at $`V_\gamma(\alpha)`$, $`\delta + V_\omega(1)\cdot\omega`$ at $`V_\omega(1)`$, $`\delta + \Lambda_\Gamma^2`$ at $`\Lambda_\Gamma`$, $`\delta + G_\Gamma(\alpha)^2 + \mathrm{logend}(\alpha)`$ at $`G_\Gamma(\alpha)`$ | cited (46) |
| `coreG2` (and `coreG`) | **CORE-C**: $`[0, \Phi_\Gamma) \subseteq \mathrm{Core}(R_2^C)`$ (without FRAG; it contains the range of `coreG`) | cited (36) + Thm 14.14 |
| `LamG_lt_PhiG`, `Vw_lt_LamG` | $`V_\omega(1) \lt \Lambda_\Gamma \lt \Phi_\Gamma \lt \Omega_1`$ | cited (14) |
| `reach_interval` | the interval form $`\{\gamma : \rho \le_1 \gamma\} = [\rho, r]`$ of a reach $`r`$ | none |

The audit printed the axioms of all 160 theorems of the stage; together they use 47 of the 49 cited axioms (not `le1R_limit` and `C09_thm14_10`). It re-ran each module alone and all together, and a
false statement added at the end failed; it found no fatal and no blocking point. Its minor points are written on this page: the counts of the axioms (m1), the citation of Thm 2.2 from its statement
(m2), $`\Omega_1 = \omega_1`$ (m3), and one range for CORE-C (m5). The offset $`\rho^2 + \rho`$ expected at $`\Phi_\Gamma`$ itself is only on paper; it is not a Lean result (m4). The doc lines of RSX,
OffPhi, OffV and BlkX now say what n1–n3 of the audit of stage 4 asked for; their code is unchanged.

The domain $`D_m`$ of `frag` allows parameters in the closure of $`D_{m-1}`$; it contains the domain of the paper proof ([RESTARTS.md](RESTARTS.md) §1), so the Lean theorem is stronger. All bases
are countable, which is the only case used on these pages.

## 4. Not yet in Lean

In order (the paper proofs of these steps exist; see [SHIFT12.md](SHIFT12.md) §1.6):

- BLK$`^O`$ from $`\Phi_\Gamma`$ to $`\Lambda_\varepsilon`$. It needs offset terms in general Cantor normal form with one uniform comparison, or more closed-form layers; or else the recursive offset $`O`$,
  which is not formalized.
- SKEL⁺, CAP, LIFT-0; then Theorem O$`^C`$ (CP is ready), NU-CT and $`\nu_C`$. The block induction in Lean still needs the exact reach of each restart; the next step is a form that does not
  compute reaches.
- The $`R_2^S`$ side is not formalized.
