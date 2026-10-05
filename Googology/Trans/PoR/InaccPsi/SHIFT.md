[← Back](README.md) | [English](SHIFT.md) | [Japanese](SHIFT-ja.md)

# $`R_2^+`$, the fifteenth and sixteenth rounds: $`\nu_C \ge X_4`$ and $`X_5`$, the shift criterion, schemes K and R, GEN-IND, STAIR2 and ghost tests

This page continues [THETA.md](THETA.md); §1–§7 are the fifteenth round and §8 is the sixteenth. The status words are those of [README.md](README.md) §3: **proved** means that an independent
referee found the result proved with no fatal or blocking point. A statement with a blocking point against it is listed under **Not proved**.
A certificate counts only when it was replayed.

Four papers (2026-10), each refereed once, so a result here has 1 review unless a count is given. **2 reviews** means that the referee of the
fourteenth round proposed or accepted the repair and the referee of this round checked it written out. None of the papers uses Wilken, JSL 72
(2007), Carlson, AML 38 (1999), Wilken, AML 45 (2006), or the equivalence that Carlson 2009, p. 97, announces. No Lean file was added: one paper
(§1) checked a Lean test file of named points with leanman (green, and green in the referee's rerun); it only compares terms (`#eval`, no theorem),
so it counts as a check. The papers number the levels of nested pairs one lower; here they are renumbered as in [THETA.md](THETA.md) §4
(their $`U^1`$ is $`U_2`$ here).

## 1. $`\nu_C \ge X_4`$, and the upper bound for $`\nu_C`$ reduced to two $`\le_1`$-statements

Notation of [THETA.md](THETA.md) §1 and §9.1: $`H(\eta) = \psi_{\Omega_1}(\Omega_\omega + \theta\cdot\eta)`$, $`\theta_2 = \psi_{\Omega_3}(\Omega_\omega)`$, $`G(\zeta) = \psi_{\Omega_2}(\Omega_\omega + \theta_2\cdot\zeta)`$, $`\iota'`$ and $`R`$ as there. New:

```math
G_2 = G(\omega^2) = \psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2+2}),\quad P' = \psi_{\Omega_2}(\Omega_\omega\cdot 2),\quad L(\xi) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + P'\cdot\xi).
```

For a restart $`\lambda`$ with index exponent $`\eta_\lambda = \eta_0 + \omega^{e}`$ (Cantor normal form), $`m_\lambda`$ is $`-1 + e`$ when this is below $`\Omega_2`$, and $`\pi_{\eta_\lambda}`$ otherwise.
A restart is **short** if its reach is below $`\rho_{\lambda+\omega^2}`$, and **long** otherwise. A $`\tau`$-point is a point $`\upsilon_{\lambda+\omega j}`$ with $`j \ge 1`$.

- **The amended formal reach** (proved, 2 reviews). The amendment of [THETA.md](THETA.md) §9.1 is now written out: in the definition of a reflected
  point, in TOP-REG, in the lemma on reaches and in the definition of $`R`$ with its corollary "reach $`\le R`$", every candidate $`y`$ must be $`\gt \delta`$, and in TOP-REG
  $`y \gt \delta_1`$. The reflection lemma becomes (L′): if every $`y'`$ in $`(\delta, y)`$ is reflected, then $`\rho \le_1 y`$ (given FRAG). The old forms are false at every
  restart with $`\mathrm{logend}(\eta_\lambda) = 2`$; the counterexample is $`\lambda = \omega^2`$, whose reach is $`\delta + 1`$.
- **The base case of Lemma L$`_R`$** (proved). This corrects the fourteenth-round referee's remark ([THETA.md](THETA.md) §9.1): at a restart with logend 2 no restart lies
  right below it, so $`\delta`$ is not reflected, and the base case must use the step lemma for block targets with step 1, not the reflection lemma. Same
  conclusion. The other minor points of that review are applied.
- **TOP-REG⁺** (proved, at the level of SKEL⁺; its first referee accepted SKEL⁺ in outline, and SKEL⁺ is now proved, [COVER.md](COVER.md) §5.1). TOP-REG holds at
  every restart below $`\nu_S`$, not only up to $`\Lambda^*`$. The sub-lemmas assume $`\lambda \le \Lambda^*`$ only to get the skeleton facts, and SKEL⁺ gives them on
  $`[0, \nu_S)`$ because $`\nu_S`$ is a restart. (The referee checked each sub-lemma; the paper should list them one by one. Done in the sixteenth round, §8.1.)
- **R-CAP\*** (proved, no FRAG). Every restart below $`\nu_S`$ with $`m_\lambda \lt G_2`$ is short. **LONG-CLASS** (proved; the referee: state it below
  $`\min(\nu_S, \psi_{\Omega_1}(\Omega_\omega\cdot 2))`$, where $`m`$ is defined): so a long restart there has $`m_\lambda \ge G_2`$.
- **Lemma TL and Theorem X4** (proved, no FRAG). With FIRST-PAIR, Lemma GHOST and TAIL ([BREAK.md](BREAK.md) §2), in both cases of NU-CT:

```math
\nu_C \ge X_4 = H(\theta_2\cdot\omega^2 + \omega^{G_2+1}\cdot 2) = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{G_2+1}\cdot 2) \gt X_3.
```

So **Wilken's claim holds in $`R_2^C`$ on $`[0, X_4]`$, both halves** (no FRAG): the core half by $`[0, \nu_C] \subseteq \mathrm{Core}(R_2^C)`$, the names half by Lemmas L
and IS. Also $`\nu_S \ge X_4`$, and in case (A) of NU-CT the left end $`a_0`$ is $`\ge H(\theta_2\cdot\omega^2 + \omega^{G_2+1})`$.

- **SHIFT** (proved). The proof of Wilken 2020, Thm 21.13, one level up, for $`R_2^S`$ with $`+`$: if $`a`$ is the supremum of points $`c_n`$ with $`c_{n+1} \le_1 a`$, and
  every finite piece of $`[a, b)`$ is the image of $`[c_n, c_{n+1})`$ under an embedding $`c_{n+1} \to b`$ that fixes $`c_n`$, then $`a \lt_2 b`$ (Prop 21.11, checked with
  its exact hypotheses).
- **Not proved**: SHIFT at the named pair $`(L(\omega), L(\omega+1))`$. It needs three statements, all open: (C1) and (C2) on long reaches at $`L(n)`$ and $`L(\omega)`$, and
  (C3), the reach condition left open in [BREAK.md](BREAK.md) §8.3. (The referee: (C1) gives only cofinally many $`n`$, so pass to a subsequence; (C2) must
  cover every $`x \lt c_n`$, which holds if $`n`$ is chosen with $`\mathrm{lh}(L(n)) \ge L(\omega+1)`$.)
- **NU-MIN** (proved; $`R_2^C`$). The minimum is attained at the left end of the pair at $`\nu_C`$:

```math
\nu_C = \min\{\, \mathrm{lh}_C(a) : a \text{ additive principal, not a } \tau\text{-point, } \{\alpha \lt a : \alpha \le_1 \mathrm{lh}_C(a)\} \text{ cofinal in } a \,\}.
```

  Carlson's minimality (Thm 14.10 (2)) supplies the $`\lt_2`$-pair, so SHIFT is not needed for an upper bound.
- **CPB and CPB-S** (proved). Let $`a \lt b`$, $`a`$ additive principal and not a $`\tau`$-point. If, in $`R_2^S`$, (P) cofinally many $`\alpha \lt a`$ have $`\alpha \le_1 b`$, and
  (Q) not $`a \le_1 b + 1`$, then $`\nu_C \le b`$. (The referee: exclude $`\mathrm{lh}_C(a) = a`$ in one line.) By Lemma TL, (P) forces $`a = H(\eta_a)`$ with
  $`\eta_a \ge \theta_2\cdot\omega^2 + \omega^{G_2+1}`$ when $`a \le \nu_S`$ is a restart above $`\rho_{\Lambda^*}`$ and below $`\psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ (the referee added the last two hypotheses).
- **Names** (proved, as implications). If (P) and (Q) hold at $`(L(\omega), L(\omega+1))`$, then $`\nu_C \le L(\omega+1) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+1} + P')`$; Conjecture
  NU-NAME ([BREAK.md](BREAK.md) §2) implies (P) and (Q) there ((Q) through CAP, the referee). The claim on $`[0, \nu_C]`$ holds iff $`\nu_C \lt \psi_{\Omega_1}(I_\omega)`$ (from `bounded_inter_Om1`), so any
  named bound below that is enough.
- **Not proved**: an InaccPsi upper bound for $`\nu_C`$, and the claim on $`(X_4, \nu_C]`$. The gap is (P) and (Q) at one named pair. (P) is a lower bound and (Q)
  an upper bound for the reaches of long restarts (zone C), which no current tool gives.

## 2. Native codes: an operator hierarchy below $`\Omega_1^\omega`$, and $`\iota(\mathrm{CH}_2) \ge Z_K`$

Notation of [THETA.md](THETA.md) §2 and §9.2: $`F(\alpha) = \upsilon_{1+\alpha}`$, $`H'(\Delta) = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Delta})`$. A position is an ordinal $`P \lt \Omega_1^\omega`$, written in base
$`\Omega_1`$ with countable coefficients. $`O_1`$ enumerates the fixed points, $`O_{P+1}`$ is the diagonal of $`O_P`$, limits of a coefficient are intersections, and at
$`P = Q + \Omega_1^l\cdot(\mu+1)`$ with $`l \ge 1`$ the operator $`O_P(H)`$ enumerates the $`z`$ with $`O_{Q + \Omega_1^l\cdot\mu + \Omega_1^{l-1}\cdot z}(H)(0) = z`$. The operators $`O_n`$, $`S`$, $`T`$ of
[THETA.md](THETA.md) §9.2 are the positions $`n`$, $`\omega`$, $`\omega+1`$.

- **OP-K, POS, DATA, DOM-K, NO-HIGH-K** (proved; the referee checked every case and the order of the recursion; the referee: DOM-K is the analogue of one direction of
  the comparison of the hull-defined hierarchy, and the link between the two is a conjecture). Every $`O_P`$ is an operator; every
  fixed point of $`\upsilon`$ outside the range of $`O_{\Omega_1^\omega}(F)`$ has a greedy signature of positions; and two fixed points compare by their data when every
  ordinal of the smaller data is below the other point. The order is

```math
\Lambda_T \lt O_{\omega+2}(F)(0) \lt \Lambda_P = O_{\Omega_1}(F)(0) \lt \Lambda_K = O_{\Omega_1^\omega}(F)(0) \lt Z_K,
```

with $`Z_K`$ the least fixed point of $`O_{\Omega_1^\omega}(F)`$.

- **Scheme K, CHAIN-K, CHAIN-TOP, CHAIN-Y, LEX-HOST-K, (MC), the TOP family** (proved). The module of a fixed point is a nest of levels, one level for
  each term of its signature; a level codes each base-$`\Omega_1`$ coefficient of its position by an inner chain, and its upper elements satisfy
  $`u^l \le_1 u^l + u^{l+1} + q^l`$ (decorations refer to the roots $`q^l`$ of the inner chains). A level hosts every level of smaller position (CHAIN-K), and the
  block $`c \le_1 c\cdot 2`$ hosts every level (CHAIN-TOP). The obstruction of [THETA.md](THETA.md) §9.2 becomes one case of LEX-HOST-K.
- **Theorem IDX-K** (proved). Natively, $`\iota(\mathrm{CH}_2) \ge Z_K`$. Also $`\iota \ge \Lambda_P`$ for the block $`[r, x \lt_2 y, c \le_1 c + y]`$ and $`\iota \ge \Lambda_K`$ for
  $`[r, x \lt_2 y, c \le_1 c\cdot 2]`$; that these are the conv patterns of (0,0,0)(1,1,1)(2,1,1)(3,1,1) and (0,0,0)(1,1,1)(2,2,0) is checked only. Both lie above SRO in
  the BMS order, so no known value contradicts these bounds.
- **FRESH, CHAIN-REL** (proved; the referee: the fact that CHAIN and CHAIN⁺ allow parameters below $`x`$ should be stated as its own lemma). A block with
  $`c \le_1 c + A`$, $`A \ge x`$, hosts every relative chain and relative decorated block that uses the outer left end $`x`$. Example: $`V_x \ll [n_0][Y]`$.
- **Not proved**: "CHAIN-REL places a hosted relative code anywhere in the host pair". It holds only for structures that become an ordinary chain or a
  decorated block when $`x`$ is replaced by a fresh point; the relative codes $`N^x(P)`$ are not defined, and their shape is an unstated lemma.
- Conjectured names: $`\Lambda_K = H'(\Omega_1^{\Omega_1^\omega})`$, $`Z_K = H'(\Omega_1^{\Omega_1^\omega} + \Omega_1)`$. Still below $`\Lambda_\varepsilon`$; the progress is on the native route only.
- **Open**: $`\iota(\mathrm{CH}_2) \ge \theta_0`$. Next: (MC) for the fixed points of $`O_{\Omega_1^\omega}(F)`$ (only a sketch), then positions $`\ge \Omega_1^\omega`$: the relative codes, their
  comparison REL-S⁺, and the comparison lemma beyond $`\Omega_1^{\Omega_1^\omega}`$.

## 3. The shapes of $`\Phi_3`$: 2,526 of 3,166

Notation of [THETA.md](THETA.md) §3 and §9.3.

- **GEN-IND** (proved). The GEN obligations are discharged by one strong induction on the run count over a finite closed list of obligation types; every
  use of the hypothesis is at a strictly smaller count (the referee logged all 7 uses on the 5 matrices). It replaces the induction of [THETA.md](THETA.md) §9.3 that
  was not proved, and covers the 5 M1 matrices whose reach recurses through every smaller run length. **LEMMA OPEN′** (proved): several runs that
  share one common shift.
- **NB-B0, NB-VH, NB-DER without slots** (proved). The block $`\beta(0)`$ may be a separate concrete block; base nodes may lie above every block; with no
  family, no main pair is needed.
- **IX-NB with the new cores, IX-NB⁺, IX-NB base1, SUM-GAP, IX-STAIR for type III, IX-STAIR⁺** (proved; the referee closed two missing checks, m1 and m2,
  by finite and symbolic checks on all affected matrices). IX-STAIR never uses the type label, so it applies to 90 matrices of type III.
- The minor points m1–m8 of the fourteenth-round review are applied (the repaired LEMMA SLOT and two other conditions are now checked by the driver
  on all 182 NB matrices).
- **The tally** (checked; $`2{,}526 = 2{,}330 + 196`$, and no earlier entry changed):

| class | matrices | proved for every $`n`$ | given a condition checked for small $`n`$ | $`t = 2`$, given a shape checked for small $`n`$ | open |
|---|---|---|---|---|---|
| I | 581 | 500 | 0 | 0 | 81 |
| SUM | 603 | 553 | 5 | 0 | 45 |
| ROOT | 635 | 587 | 0 | 0 | 48 |
| III | 1,347 | 886 | 0 | 24 | 437 |
| all | 3,166 | 2,526 | 5 | 24 | 611 |

- **Left** (640): $`t = 0`$: M2 63 (anchor-chain families under an $`\Omega`$-level node that is not an index), M3 28, M4 14, M5 15; $`t = 2`$: III 66 (24 where the
  head of the top chain moves; 21 with the chain at a child of the bad root whose core is not of index type or not a staircase; 21 deeper), ROOT 31, I 15,
  SUM 26; $`t = 1`$: 382. M1 is done (258 of 258).

## 4. $`\nu_C = \nu_S`$: one more closed-form layer, (PROF) for all symbols, and ghost tests

Notation of [THETA.md](THETA.md) §4 and §9.4. $`\mathrm{LT}(y)`$ says: some long restart above $`y`$ has a reach whose last Cantor-normal-form term is $`y`$.

- **FRESH′, the skeletons with every $`\upsilon_{\iota+\zeta}`$ ($`\zeta \lt \omega^2`$), TW-MIX′** (proved, 2 reviews). The repairs of the fourteenth-round review, written out:
  the new index is $`\theta'' + \omega^{1+l'}`$; so TW-MULTI and TW-MIX of [THETA.md](THETA.md) §9.4 hold as stated there. (The referee: values must be defined region
  by region in increasing order.)
- **CLOSE, ISO-INV, EPS-VIS, HER** (proved; HER under two bookkeeping hypotheses). Recording the reaches, sums and block data of the top points stops after
  finitely many steps, and these facts survive the isomorphic extension; the referee's example $`\omega^{\rho_a+1}`$ is covered by hereditary copies.
- **KV-Δ, CF-Δ⁺, FRESH-Δ** (proved, relative to the same hypothesis as LADDER). One closed-form layer above the diagonal class: for an index in
  $`\mathrm{Fix}(f_\Delta)`$ outside the critical class $`K^{f_\Delta}`$, with canonical form $`(A, \eta)`$, the offset is $`\rho^{\rho+1} + P_A(\rho) + \mathrm{logend}(\eta)`$. So every long
  restart, every point of $`U_2`$ and $`\nu`$ have indices in $`K^{f_\Delta}`$, and every other restart index has a closed reach below $`\delta\cdot 2`$.
- **LADDER-TAIL, DICT-n, PROF-n** (proved). (PROF) holds for every symbol whose coefficients are below $`u`$, with any number of positions $`\ge u`$. So the item
  "(PROF) with two or more positions" is closed.
- **CAND-2-SHAPE, SEP-RED** (proved, as reductions). An anchor $`b \lt a \le \mathrm{lh}(b)`$ outside the region of $`a`$ is a long restart.
- **OCC, G-SCHEMA, G-TAIL** (proved). CAND-1 with exact tail $`u_m`$ occurs iff $`\mathrm{LT}(u_m)`$. For a $`\Sigma_1`$ pattern $`P`$: $`P`$ at all large $`u_n`$ and not $`P`$ at $`x`$ give
  $`\nu_C \lt \nu_S`$. The $`\Pi_1`$ property "$`y \le_1 z`$ for all $`z \gt y`$, and not $`\mathrm{LT}(y)`$" separates the structure below $`x`$ from the one below $`\nu`$ (a ghost) iff
  $`\mathrm{LT}(u_n)`$ holds for all large $`n`$ and $`\mathrm{LT}(x)`$ fails. (The referee: in OCC a witness above $`u_{m+1}`$ must first be moved below it; "all large $`n`$"
  needs one $`u_N`$ among the parameters.)
- **Not proved** (blocking points): (B1) "SEP and ROOM fail only at restarts with index in $`K^{f_\Delta}`$ or with top data" is false: a small restart that is not
  in the realization can make a run point a term of a reach. (B2) "CAND-2 is equivalent to one pattern" is false: CAND-2 is a countable union of
  patterns, one for each $`j`$. ROOM-RED misses one case (a long restart whose preimage is not a restart) and shows only "if". The list of the residue is
  exhaustive once that case is added. (The referee: the largest plan also moves untwisted small restarts, so the residue is a necessary condition,
  not a list of real obstructions.)
- **Not proved**: $`\nu_C = \nu_S`$, and $`\nu_C \lt \nu_S`$. Neither $`\mathrm{LT}(u_n)`$ nor $`\mathrm{LT}(x)`$ is decided; no long restart has a closed-form reach. Conjecture U-TAIL: no ghost of
  this kind. Open: the map $`T`$ on $`[u^\#, \lambda^\Delta_u)`$, and SEP and ROOM in general.

## 5. Status after the fifteenth round

- Wilken's claim in $`R_2^C`$: both halves hold on $`[0, X_4]`$ with $`X_4 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{G_2+1}\cdot 2)`$, no FRAG; the core half holds on
  $`[0, \nu_C]`$ with $`\nu_C \ge X_4`$. An upper bound for $`\nu_C`$ needs only (P) and (Q) at one named pair.
- The lower-bound program below $`\theta_0`$: the step below SRO is proved for every $`n`$ on 2,526 of the 3,166 sample matrices; $`\iota(\mathrm{CH}_2) \ge Z_K`$ natively.
- Upper bounds: still none by an InaccPsi term for $`\iota(\mathrm{CH}_k)`$, $`m_F`$, $`x_F`$, $`C^*_3`$ or $`\nu_C`$.
- $`\nu_C = \nu_S`$: (PROF) is closed; the residue is SEP and ROOM, which come down to the reaches of long restarts; the test of §4 gives a ghost iff $`\mathrm{LT}`$ differs at
  $`x`$ and at the $`u_n`$.

The sixteenth round changed this status; see §8.5.

## 6. Checks of the fifteenth round

Each run was under 60 seconds; none is a proof.

- §1. The memberships used, that $`X_4`$ is a normal form, and the order $`X_3 \lt X_4 \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2) \lt L(n) \lt L(\omega) \lt L(\omega+1) \lt \psi_{\Omega_1}(I_0) \lt \psi_{\Omega_1}(I_\omega)`$:
  Python and Lean agree. The referee: the rerun is identical, and 6 own test groups found 0 failures.
- §2. 16 blocks (14 new) are patterns, RF, fan-free and L1p-free. Certificates, all replayed: 12 of 16 in the predicted direction, 4 of 6 smaller extra
  pairs, 0 of 6 in the reverse direction. The referee: the rerun is identical; 0 of 14 own reverse searches found, 4 of 4 forward found and replayed.
- §3. The referee: ordered lists with lh and succ agree at $`j = 8`$ for the 14 new NB matrices and at $`j = 8, 9`$ for the 13 new cores; the templates are valid at
  $`n = 8, 9`$ for 43 of the 169 new IX matrices and all 4 IX-STAIR⁺ matrices; the type-III condition holds for $`n \le 8`$ on all 90.
- §4. The referee: 13 strings with the program (12 standard); all 5 new KV-Δ predictions match.

## 7. Open

- Upper bounds: (P) and (Q) at one named pair for $`\nu_C`$ (§1); bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$.
- The first inaccessible: $`H_m`$, through $`\iota(\mathrm{CH}_2) \ge \theta_0`$ (from $`Z_K`$ on: relative codes, REL-S⁺, positions $`\ge \Omega_1^\omega`$); UNIF-FS below SRO on the 640
  matrices of §3.
- $`\nu_C = \nu_S`$: the reaches of long restarts ($`\mathrm{LT}(u_n)`$ and $`\mathrm{LT}(x)`$), SEP and ROOM, and the map $`T`$ on $`[u^\#, \lambda^\Delta_u)`$.
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; names beyond $`X_4`$; the rest of [COVER.md](COVER.md) §9.

The sixteenth round changed this list; the current list is §8.7.

## 8. The sixteenth round: $`\nu_C \ge X_5`$ given FRAG, scheme R, STAIR2 and LT everywhere

Four papers (2026-10), each refereed once, so a result in §8 has 1 review unless a count is given. **2 reviews** here means that the referee of the
fifteenth round checked the result (or proposed its repair) and the referee of this round checked it again as written out. None of the papers uses
Wilken, JSL 72 (2007), Carlson, AML 38 (1999), Wilken, AML 45 (2006), or the equivalence that Carlson 2009, p. 97, announces. No Lean file was added:
one paper (§8.1) checked a Lean test file of named points with leanman (green, and green in the referee's rerun); it only compares terms, so it counts
as a check. Levels are renumbered as in §1–§7 (the papers' $`U^1`$ is $`U_2`$ here). Results that rest on SKEL⁺ inherit its outline level ([COVER.md](COVER.md) §5.1).

### 8.1 $`\nu_C \ge X_5`$ given FRAG; (P) and (Q) still open

Notation of §1. For a restart $`\lambda`$, $`e_\lambda = \mathrm{logend}(\eta_\lambda)`$. For a countable $`\xi \ge 1`$, $`\omega^2\cdot\xi`$ is an **index distance**: the restart $`\lambda + \omega^2\cdot\xi`$ lies that far after $`\lambda`$.

- **The minor points m1–m9 of the fifteenth-round review are applied.** For TOP-REG⁺ the paper now lists each sub-lemma, the setting it states, and
  the clause of SKEL⁺ that supplies it below $`\nu_S`$. So **TOP-REG⁺ has 2 reviews** (at the outline level of SKEL⁺).
- **XA** (proved, no FRAG; the referee: the bound $`\beta`$ must also exceed every reach $`\mathrm{lh}(x) \lt \rho_\nu`$ of a non-restart $`x \in X`$). Let $`\nu`$ be a restart with
  $`\rho_\nu \lt \nu_S`$ and $`X \subseteq \rho_\nu`$ finite. Up to a known reach of $`\rho_\nu`$, the atoms between $`X`$ and the points of the region of $`\nu`$ are the same at every point of a final
  segment of $`\rho_\nu`$, also when $`X`$ has long restarts. So the reflection lemma (L′) and the realizer lemmas of [THETA.md](THETA.md) §9.1 hold for every restart below
  $`\nu_S`$, not only up to $`\Lambda^*`$ (given FRAG).
- **EXACT-C** (proved; "$`\le`$" without FRAG, "$`\ge`$" given FRAG). Every restart $`\nu`$ with $`\rho_\nu \lt \nu_S`$ and countable $`e_\nu`$ has
  $`r(\nu) = \delta_\nu + (-1 + e_\nu)`$, wherever it lies. So a restart with logend 2 reaches exactly $`\delta_\nu + 1`$, and no restart below $`\nu_S`$ reaches exactly $`\delta_\nu`$ of a
  later restart $`\nu`$ (the referee: for uncountable $`e_\nu`$ this needs the step "$`c = 1`$" of the reflection lemma instead).
- **PIN-IDX** (proved, given FRAG). In a copy $`h`$ with $`h(\rho_\lambda) = \rho_\mu`$, the restart at a countable index distance $`\zeta \lt \rho_\mu`$ is pinned: $`h(\rho_{\lambda+\zeta})`$ is a restart
  $`\ge \rho_{\mu+\zeta}`$.
- **TOP-REG-ξ, R-CAP-ξ, LONG-CLASS-ξ** (proved, given FRAG, at the outline level of SKEL⁺ and H-RC, like TOP-REG⁺; one citation corrected by the referee).
  R-CAP\* extends past $`G_2`$: if $`G_2\cdot\xi \le m_\lambda \lt G_2\cdot(\xi+1)`$ with $`\xi`$ countable, then $`r(\lambda) \lt \rho_{\lambda+\omega^2(\xi+1)}`$ (when this point is $`\le \nu_S`$). So a reach
  that passes $`\rho_{\lambda+\omega^2(\xi+1)}`$ needs $`m_\lambda \ge G_2\cdot(\xi+1)`$.
- **HULL-GAP** (proved, no FRAG): for $`\eta \in D'`$, $`C_\eta`$ has no element in $`[G_2\cdot H(\eta), G_2\cdot\Omega_1)`$. **FAR** (proved, given FRAG): a restart that reaches the region at
  every countable index distance below its own point has $`m_\lambda \ge G_2\cdot\Omega_1 = \omega^{G_2+\Omega_1}`$ and $`e_\lambda \ge G_2\cdot\Omega_1`$.
- **LONG-G2** (proved, given FRAG). A restart with $`m_\lambda = G_2`$ (and $`\rho_{\lambda+\omega^2} \lt \nu_S`$) is long, with $`r(\lambda) = \delta_{\lambda+\omega^2} + 1`$. With R-CAP\*: among the
  restarts with $`m_\lambda \le G_2`$, the long ones are exactly those with $`m_\lambda = G_2`$. At $`\Lambda^*`$ this is the value the program gave in the sixth round (before, only
  "$`\ge`$" was proved):

```math
r(\Lambda^*) = \delta_{\Lambda^*+\omega^2} + 1 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta+2} + \omega^{\theta+1} + \theta) + 1.
```

- **Theorem X5** (proved, given FRAG, at the outline level of SKEL⁺ and H-RC). The $`\lt_1`$-predecessors of the left end of the pair at $`\nu_C`$ reach every region at a
  countable index distance below their own point, so FAR applies to them, and then the argument of Theorem X4 gives

```math
\nu_C \ge X_5 = H(\theta_2\cdot\omega^2 + \omega^{G_2\cdot\Omega_1+1} + \omega^{G_2+1}) = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\omega^{G_2+\Omega_1}+1} + \omega^{G_2+1}) \gt X_4 .
```

So **Wilken's claim holds in $`R_2^C`$ on $`[0, X_5]`$, both halves, given FRAG** ($`X_5`$ is a normal form; the core half by $`[0, \nu_C] \subseteq \mathrm{Core}(R_2^C)`$, the names
half by Lemmas L and IS). Without FRAG the range stays $`[0, X_4]`$. Also $`\nu_S \ge X_5`$.

- **CL, P-LOW** (proved; P-LOW given FRAG). (P) at $`(a, b)`$ gives $`a \le_1 b`$, so (P) and (Q) together say $`\mathrm{lh}_S(a) = b`$, and every pair with both has $`b \ge \nu_C \ge X_5`$.
  A restart $`a`$ with $`H(\theta_2\cdot\omega^2) \lt a \lt \min(\nu_S, \psi_{\Omega_1}(\Omega_\omega\cdot 2))`$ and (P) has $`a \ge H(\theta_2\cdot\omega^2 + \omega^{G_2\cdot\Omega_1+1})`$.
- **Q-OBST** (the first part proved; the rest is a remark, the referee). Under (P), every final segment of $`a`$ has a restart that reaches $`b`$. So TOP-REG, TOP-REG⁺ and
  TOP-REG-ξ have a false hypothesis at such a pair, and (Q) cannot come from these bounds on the reaches below $`a`$. The only argument known for (Q) is CAP,
  which uses the nested pair itself.
- **Not proved** (the referee: the leaf is not reached; $`X_5`$ is a lower bound only): an InaccPsi upper bound for $`\nu_C`$; (P) and (Q) at $`(L(\omega), L(\omega+1))`$ or at
  any other named pair; the claim on $`(X_5, \nu_C]`$. The gap: (P) needs lower bounds for reaches over index distances that move with the point
  ($`L(n) \ge \psi_{\Omega_1}(\Omega_\omega\cdot 2)`$ lies outside $`D'`$, where R-CAP\* and R-CAP-ξ are written), and (Q) needs a bound $`\mathrm{lh}_S(a) \le b`$ that is not a bound on the reaches below $`a`$.
- **Conjecture R-CAP-FAR** (outline). The same bound at distances that move with the point. It would give $`\nu_C \ge X_6 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\omega^{G_2\cdot 2}+1} + \omega^{G_2+1})`$.
  Missing: pins whose offsets also move, the link between indices and distances $`\ge \rho_\lambda`$, and the transport of the distance codes.

### 8.2 Native codes: a Veblen-style hierarchy up to $`\Gamma_{\Omega_1+1}`$, and $`\iota(\mathrm{CH}_2) \ge Z_\Xi`$

Notation of §2. Let $`\Xi = \Gamma_{\Omega_1+1}`$. An index $`\Delta \le \Xi`$ is written in base $`\Omega_1`$ with countable coefficients, and its $`\varepsilon`$-numbers above $`\Omega_1`$ as $`\varphi_\alpha(\gamma)`$;
$`K(\Delta)`$ is the finite set of its countable parameters. With $`F`$ at index 0, and for $`1 \le \Delta \le \Xi`$:

```math
B_\Delta = \{\beta \lt \Omega_1 : \theta_{\Delta'}(\beta) = \beta \text{ for every } \Delta' \lt \Delta \text{ with } K(\Delta') \subseteq \beta\},\qquad \theta_\Delta = \text{the enumeration of } B_\Delta .
```

- **The open item of §2 on relative codes** (the referee agrees): "CHAIN-REL places a hosted relative code anywhere in the host pair" is still not proved
  as stated. The part that CHAIN-REL proves is restated, and it matches; so **CHAIN-REL has 2 reviews**. The aim is reached without relative codes:
  a position is coded by an absolute nested code over its parameters, placed inside the pair of its level, and the pair $`x \lt_2 y`$ of each level plays $`\Omega_1`$.
- **CLUB, NF-R, DOM-R, T1-R, NO-HIGH-R** (proved). $`\theta_\Delta`$ is normal; every fixed point $`\zeta`$ of $`\upsilon`$ outside $`B_\Xi`$ is $`\theta_\Delta(\alpha)`$ with $`K(\Delta) \cup \{\alpha\} \subseteq \zeta`$; and
  normal forms compare as below. (The referee: this is a comparison for this hierarchy; that it is the comparison of the hull-defined hierarchy of
  [THETA.md](THETA.md) §9.2 is a conjecture. The same holds for DOM-K of §2.)

```math
\theta_\Delta(\alpha) \lt \theta_{\Delta'}(\alpha') \iff \begin{cases} \Delta \lt \Delta' \text{ and } K(\Delta) \cup \{\alpha\} \subseteq \theta_{\Delta'}(\alpha'), \text{ or}\cr \Delta = \Delta' \text{ and } \alpha \lt \alpha', \text{ or}\cr \Delta' \lt \Delta \text{ and } \theta_\Delta(\alpha) \le \max(K(\Delta') \cup \{\alpha'\}). \end{cases}
```

- **CMP-K** (proved, after a bookkeeping repair by the referee): $`Z_K \le \theta_{\Omega_1^{\Omega_1^\omega}+1}(0) \lt \theta_{\varepsilon_{\Omega_1+1}}(0)`$.
- **The codes of scheme R, LEVEL-HOST, NEST-HOST, ATOM-HOST, HOST-Γ, TOP-HOST, CHAIN-Y-R** (proved; the referee checked that the cases are
  exhaustive and that the recursion is well founded). The code of an exponent $`Q`$ is a chain ($`Q`$ countable), a nest with one level for each base-$`\Omega_1`$
  term ($`Q \ge \Omega_1`$ not an $`\varepsilon`$-number), or an atom $`r \lt x \lt \Gamma(\alpha) \lt \Gamma(\gamma) \lt y \lt u \lt c`$ with $`u \le_1 u + q_\alpha`$ and $`c \le_1 c\cdot 2 + u + q_\gamma`$ ($`Q = \varphi_\alpha(\gamma) \gt \Omega_1`$).
  HOST-Γ is the absolute form of REL-S⁺: a copy of the code of $`Q`$ hosts the code of every $`Q' \lt Q`$, and it uses S⁺ only at countable parameters of the
  host's own term, as the fifteenth-round referee asked. The block $`c \le_1 c\cdot 3`$ hosts every code; $`c \le_1 c + y`$ and $`c \le_1 c\cdot 2`$ host every code without atoms.
- **Theorem IDX-R** (proved). Natively,

```math
\iota(\mathrm{CH}_2) \ge Z_\Xi = \text{the least fixed point of } \theta_\Xi,\qquad Z_K \le \theta_{\Omega_1^{\Omega_1^\omega}+1}(0) \lt \theta_{\varepsilon_{\Omega_1+1}}(0) \lt \theta_\Xi(0) \lt Z_\Xi .
```

  Also $`\iota \ge \theta_{\varepsilon_{\Omega_1+1}}(0)`$ for $`[n_0][Y]`$ and for $`[n_0][\mathrm{TOP}(0)]`$, and $`\iota \ge \theta_\Xi(0)`$ for the block $`[r, x \lt_2 y, c \le_1 c\cdot 3]`$. (The paper proves
  $`\theta_{\varepsilon_{\Omega_1+1}}(0) \le \theta_\Xi(0)`$; the referee adds the one line for "$`\lt`$".)
- Conjectured names: $`\theta_{\varepsilon_{\Omega_1+1}}(0) = H'(\varepsilon_{\Omega_1+1})`$, $`\theta_\Xi(0) = H'(\Gamma_{\Omega_1+1})`$, $`Z_\Xi = H'(\Gamma_{\Omega_1+1} + \Omega_1)`$. Then the native route would pass
  $`\Lambda_\varepsilon = H'(\varepsilon_{\Omega_1+1} + 1)`$; it stays below $`\Theta_1 = H(\theta)`$.
- **Open**: $`\iota(\mathrm{CH}_2) \ge \theta_0`$. Next: $`Z_\Xi`$ itself (only a sketch); indices $`\Delta \ge \Gamma_{\Omega_1+1}`$ (every finite stock of atom kinds stops at a finitary Veblen
  level over $`\Omega_1`$; outline); codes above $`y`$ made of $`\le_1`$-atoms only for the level of $`\psi_{\Omega_2}`$ (no pair may sit above $`y`$).

### 8.3 The shapes of $`\Phi_3`$: 2,589 of 3,166

Notation of §3.

- **The minor points m1–m8 of the fifteenth-round review are applied.** The two checks that the referee had closed by hand (the high nodes against the
  template letters, and the symmetric case of SUM-GAP) are now hypotheses checked by the programs; the reruns are identical (182 NB, 79 IX-NB, 8 SUM-GAP).
  So these repaired checks have **2 reviews**.
- **C1-ID, TAIL-U, REL-OPQ2** (proved). TAIL-U is an informal argument about the program code, like the property (REP). (The referee: that two markers
  for the same level also meet in hash lookups is a checked hypothesis, not a proved one.)
- **STAIR2-V** (proved). A class with $`t = 2`$ where the copies go down two levels per step (a stair): $`\mathrm{conv}(A[n])`$ is given explicitly for every $`n`$. Each step adds
  a fixed set of 4 to 16 new nodes, and the old nodes move by one more stair step. 30 of the 31 open T2-ROOT matrices, and 7 of type III. (The referee: the
  window check should compare each node, not each class; the referee checked it node by node at levels 7 to 11.)
- **NEST-GEN** (proved). The derivation for these classes, by induction on $`n`$, and FS⁺ at every $`n`$.
- **IX-STAIR2, SUM-CORE-2** (proved). Lifting over the new cores: 7 of type I, 10 of type III, 5 of type SUM.
- **BASE-DIRECT** (proved). For $`t = 1`$, a direct base for $`A[0]`$; with the periodic steps proved in an earlier round it proves 4 T1-ROOT matrices. (The referee: the
  cited self-chain theorem must be restated without one hypothesis that fails here and that its proof does not use.)
- **Not proved**: M2 (63 matrices). The hand derivation does not transfer: it would need $`x \le_1 y + a`$ with $`a \gt x`$, but there the reach of $`x`$ is only $`y + p`$ with $`p \lt x`$.
- **The tally** (checked; $`2{,}589 = 2{,}526 + 63`$, and no earlier entry changed):

| class | matrices | proved for every $`n`$ | given a condition checked for small $`n`$ | $`t = 2`$, given a shape checked for small $`n`$ | open |
|---|---|---|---|---|---|
| I | 581 | 507 | 0 | 0 | 74 |
| SUM | 603 | 558 | 5 | 0 | 40 |
| ROOT | 635 | 621 | 0 | 0 | 14 |
| III | 1,347 | 903 | 0 | 24 | 420 |
| all | 3,166 | 2,589 | 5 | 24 | 548 |

- **Left** (577): $`t = 0`$: M2 63, M3 28, M4 14, M5 15; $`t = 2`$: III 49 (24 where the head of the top chain moves; 21 with the chain at a child of the bad root;
  4 deeper), ROOT 1, I 8, SUM 21; $`t = 1`$: 378 (III 308, I 33, SUM 24, ROOT 13).

### 8.4 $`\nu_C = \nu_S`$: LT holds everywhere, so the explicit property of §4 is not a ghost

Notation of §4. Here a restart $`a`$ is **long** if $`\mathrm{lh}(a) \ge \delta_a\cdot 2`$ (as in LT of §4) and **wide** if $`\mathrm{lh}(a) \ge \delta_a\cdot 3`$; §1's "long" (reach $`\ge \rho_{\iota_a+\omega^2}`$) is
called **far** here. $`\rho^+(c)`$ is the least restart above $`c`$.

- **SK⁺, REFL⁺, NU-K3** (proved, given FRAG, at the outline level of SKEL⁺). $`R_2^S`$ is $`\upsilon`$-skeletal on $`[0, \nu_S)`$; (L′) holds for every restart below $`\nu_S`$ when no point
  caps it; wide restarts are cofinal below $`\nu`$.
- **TAIL-MIN** (proved, given FRAG, at the outline level of SKEL⁺ and TOP-REG⁺). Let no point $`u \le c`$ have a reach in $`[\rho^+(c), \nu)`$, let $`1 \le t \le c`$, and let a wide
  restart lie in $`(c, \nu)`$. Let $`a^*`$ be the least restart $`a \gt c`$ such that, for every $`z \lt t`$, the restarts with reach $`\ge \delta\cdot 2 + z`$ are cofinal in $`a`$. Then
  $`\mathrm{lh}(a^*) = \delta_{a^*}\cdot 2 + t`$ exactly, and every restart in $`(c, a^*)`$ has a smaller reach of this form. The same holds with $`\delta\cdot 2`$ replaced by any uniform
  head (HEAD-TAIL; the referee: its clause "not wide" fails for heads $`\ge \delta\cdot 3`$).
- **BASE0-TAIL** (proved; the upper half without FRAG, equality given FRAG). At base 0 the bracket of the formal reach closes: with $`G = G(\omega+1)`$, the restart
  $`\lambda_n = \iota'(\theta_2\cdot(\omega+1) + \omega^{G+n})`$ has reach exactly $`\delta\cdot 2 + n`$ (the fifteenth-round paper had said the upper half was not available).
- **Theorem LT** (proved, at the same level). For every $`y_0 \in U_2`$ other than $`\nu`$, the bases $`y_0 + 1`$ and $`y_0^\#`$ have no cap, so $`\mathrm{LT}(y_0)`$ holds: $`\mathrm{LT}(u_n)`$
  for every $`n`$, and $`\mathrm{LT}(x)`$. So the $`\Pi_1`$ property of §4 is **not a ghost**, and the LT part of Conjecture U-TAIL is a theorem. CAND-1 with exact tail occurs at every level.
- **The repairs of (B1) and (B2) of §4.** (B2): every CAND-2 configuration of level 0 with exact tail is an instance of one of countably many $`\Sigma_1`$ diagrams, and
  G-SCHEMA applies to each (proved). The converse, and "the union is not $`\Sigma_1`$", are not proved. (B1): **not proved** (blocking). The plans are taken over the
  restarts of the regions, but only over the open interval $`(g, u_{m+1})`$ with $`g = u_m^\#`$; $`g`$ itself is a restart whose head term is twisted, and its index is not in $`K^{f_\Delta}`$.
  So the claim that the residue lives only at restarts with index in $`K^{f_\Delta}`$ or with top data is still not proved. Fix: admit $`g`$ to the plans, or show that it is never needed.
- **LONG-FRESH** (proved, as a reduction). The twisted copy of a whole CAND-1 configuration comes down to one placement statement (W): a long copy among the
  anchors, in a gap below the points that cap its reach (open). (The referee: that the needed reach exists is shown only for uniform heads.)
- **Not proved**: $`\nu_C = \nu_S`$, and $`\nu_C \lt \nu_S`$. Open: CAND-2 (it needs an upper bound for the reach of a far restart that lands inside a later region, a far form of
  TOP-REG), the placement (W), (B1) at $`g`$, and the map $`T`$ on $`[u^\#, \lambda^\Delta_u)`$.

### 8.5 Status after the sixteenth round

- Wilken's claim in $`R_2^C`$: both halves hold on $`[0, X_4]`$ without FRAG, and on $`[0, X_5]`$ given FRAG (at the outline level of SKEL⁺ and H-RC); the core half holds on
  $`[0, \nu_C]`$. No InaccPsi upper bound for $`\nu_C`$: (P) and (Q) at a named pair stay open.
- The lower-bound program below $`\theta_0`$: the step below SRO holds for every $`n`$ on 2,589 of the 3,166 sample matrices; natively $`\iota(\mathrm{CH}_2) \ge Z_\Xi`$.
- Upper bounds: still none by an InaccPsi term for $`\iota(\mathrm{CH}_k)`$, $`m_F`$, $`x_F`$, $`C^*_3`$ or $`\nu_C`$.
- $`\nu_C = \nu_S`$: LT holds at $`x`$ and at every $`u_n`$, so the explicit ghost candidate is refuted; left: CAND-2, the placement (W), and (B1) at $`u_m^\#`$.

### 8.6 Checks of the sixteenth round

Each run was under 60 seconds; none is a proof.

- §8.1. The memberships in $`D'`$, the normal forms of $`X_5`$, $`X_6`$ and of the value of $`r(\Lambda^*)`$, HULL-GAP on 5 samples, and the order
  $`X_4 \lt X_5 \lt X_6 \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2) \lt L(1) \lt L(\omega) \lt L(\omega+1) \lt \psi_{\Omega_1}(I_0) \lt \psi_{\Omega_1}(I_\omega)`$: Python and Lean agree. The referee: the Lean rerun is green, and
  216 test points in $`[G_2\cdot\rho, G_2\cdot\Omega_1)`$ hold no element of $`C_\eta`$.
- §8.2. 20 blocks are patterns, RF, fan-free and L1p-free (rerun identical). Certificates, all replayed: 15 of 22 in the predicted direction, 0 of 9 in
  the reverse direction; the referee: 0 of 14 more reverse searches. The search depth is small, so "not found" is weak evidence.
- §8.3. The referee: the step at $`n = 8, \dots, 11`$ for all 38 new matrices; NEST-GEN for $`n \le 12`$ on all 37; TAIL-U with up to 21 instances per hook; the stair tails
  for levels up to 20; the decisions node by node at levels 7 to 11.
- §8.4. For 8 sample values of $`n`$ (and 3 more by the referee): the index of $`\lambda_n`$ is in $`D'`$, its value is a normal form, increasing, and between $`\rho_{\Theta_\delta}`$ and $`\rho_{\Theta_{d\omega}}`$.

### 8.7 Open

- Upper bounds: (P) and (Q) at one named pair for $`\nu_C`$; they need reaches over index distances that move with the point (Conjecture R-CAP-FAR would give $`X_6`$);
  bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$.
- The first inaccessible: $`H_m`$, through $`\iota(\mathrm{CH}_2) \ge \theta_0`$ (from $`Z_\Xi`$ on: $`Z_\Xi`$ itself, indices $`\ge \Gamma_{\Omega_1+1}`$, $`\le_1`$-only codes for the level of $`\psi_{\Omega_2}`$); UNIF-FS below
  SRO on the 577 matrices of §8.3 (first M2).
- $`\nu_C = \nu_S`$: CAND-2 (a far form of TOP-REG), the placement (W), (B1) at $`u_m^\#`$, and the map $`T`$ on $`[u^\#, \lambda^\Delta_u)`$.
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; the exact reaches of restarts with $`G_2 \lt m_\lambda \lt G_2\cdot 2`$ (conjecture: $`\delta_{\lambda+\omega^2} + (n+1)`$
  for $`m_\lambda = G_2 + n`$); names beyond $`X_5`$; the rest of [COVER.md](COVER.md) §9.
