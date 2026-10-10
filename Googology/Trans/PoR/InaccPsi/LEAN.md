[← Back](README.md) | [English](LEAN.md) | [Japanese](LEAN-ja.md)

# $`R_2^+`$ in Lean: $`R_2^C`$, the core, and FRAG

This page describes the Lean files of the directory [R2/](R2/) (namespace `Googology.Trans.PoR.InaccPsi.R2`), added in the fortieth round ([SHIFT10.md](SHIFT10.md) §3.3). They build with the
whole library (`lake build`, green, no `sorry`). Their audit found every axiom faithful to the paper it cites, every definition right, and every main theorem proved by Lean; it found no fatal
and no blocking point.

**What this changes.** Almost every result above $`\upsilon_{\omega\cdot\omega}`$ on the other pages is stated "given FRAG". FRAG is now a Lean theorem whose only non-standard axioms are 20
facts cited from two papers of Wilken (and 7 constants for the objects of those papers). So "given FRAG" can be read as "given these 20 cited facts".

## 1. The files

| file | content | axioms used |
|---|---|---|
| [R2/Defs.lean](R2/Defs.lean) | $`R_2^C`$ defined from Carlson 2009: closed sets (Def 2.1, 2.3), coverings (Def 5.2), $`\le_1^\infty`$ and $`\le_2^\infty`$ (Def 5.3), $`\le_1`$, $`\le_2`$ by recursion on the right end (Def 5.4); isomorphisms, $`\le_{pw}`$, isominimal sets and the core (Def 2.6) for any interpretation | none |
| [R2/Basic.lean](R2/Basic.lean) | the recursion equations; basic facts of $`\le_1`$, $`\le_2`$; the reach | none |
| [R2/Loc.lean](R2/Loc.lean) | Lemma LOC and its corollary | none |
| [R2/Cited.lean](R2/Cited.lean) | the only axioms (§2) | — |
| [R2/Points.lean](R2/Points.lean) | $`\upsilon`$-points of $`R_1^+`$, segments, restarts $`\rho_\lambda`$, reaches $`r(\lambda)`$ | cited |
| [R2/Frag.lean](R2/Frag.lean) | Lemma ST, FRAG with one base on the whole domain | cited |
| [R2/FragBase.lean](R2/FragBase.lean) | closure, components, segments, the domains $`D_k`$, one base change on a set, the case analysis | cited |
| [R2/FragM.lean](R2/FragM.lean) | heights, the compression step, Theorem FRAG for any number of bases | cited |
| [R2/Frag2.lean](R2/Frag2.lean) | Theorem FRAG2 for the Lean $`R_2^C`$ | `le1R` only |

Two readings in [R2/Defs.lean](R2/Defs.lean) are equivalent to Carlson's text and are explained there: clauses (c) and (d) of $`\le_2^\infty`$ are one covering (a covering of finite sets is the order
isomorphism), and "any finite structure" ranges over finite closed sets of ordinals with relations (every finite arithmetic structure is isomorphic to one, Carlson 2009, remark after L.4.6).
"Cofinally many below $`c`$" is read strictly (for every $`c' \lt c`$ a copy above $`c'`$), as in the proof of Carlson 2009, L.5.5 (1).

## 2. The axioms ([R2/Cited.lean](R2/Cited.lean))

No axiom mentions $`R_2^C`$. A misreading of Carlson's definition could only make the Lean $`R_2^C`$ differ from Carlson's; it cannot make the axioms inconsistent. The axioms are about
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

The domain $`D_m`$ of `frag` allows parameters in the closure of $`D_{m-1}`$; it contains the domain of the paper proof ([RESTARTS.md](RESTARTS.md) §1), so the Lean theorem is stronger. All bases
are countable, which is the only case used on these pages.

## 4. Not yet in Lean

- The link between $`\le_1`$ of $`R_2^C`$ (defined) and $`\le_1`$ of $`R_1^+`$ (the constant `le1R`): first INC1 ([BREAK.md](BREAK.md) §1). FRAG2 takes the skeleton as a hypothesis.
- Carlson 2009, Thm 14.10 and Thm 14.14 (the core is the least $`\kappa`$ with $`\kappa \le_1`$ everything above it); the corollary of LOC takes this as a hypothesis.
- That `upsilon` is Wilken's $`\upsilon`$ (it is defined as the enumeration of $`\{0\}`$ and the points $`\le_1`$ to everything above), and that `reach` is the maximum where it exists.
- The chain to $`\nu_C`$, in order: Carlson 2009, L.4.4–4.5; Lemma MOVE and Theorem CP; INC1; the blocks below $`\upsilon_{\omega^3}`$ (the first uses of FRAG and FRAG2); the restart blocks (BLK$`^\Xi`$, BLK$`^O`$);
  SKEL⁺, CAP, LIFT-0; Theorem O$`^C`$, NU-CT, and the name of $`\nu_C`$. The $`R_2^S`$ side is not formalized.
