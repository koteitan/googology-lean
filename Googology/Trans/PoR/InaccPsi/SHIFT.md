[← Back](README.md) | [English](SHIFT.md) | [Japanese](SHIFT-ja.md)

# $`R_2^+`$, the fifteenth round: $`\nu_C \ge X_4`$, the shift criterion, scheme K, GEN-IND and ghost tests

This page continues [THETA.md](THETA.md). The status words are those of [README.md](README.md) §3: **proved** means that an independent
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
  $`[0, \nu_S)`$ because $`\nu_S`$ is a restart. (The referee checked each sub-lemma; the paper should list them one by one.)
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
  NU-NAME ([BREAK.md](BREAK.md) §2) implies (P) and (Q) there. The claim on $`[0, \nu_C]`$ holds iff $`\nu_C \lt \psi_{\Omega_1}(I_\omega)`$ (from `bounded_inter_Om1`), so any
  named bound below that is enough.
- **Not proved**: an InaccPsi upper bound for $`\nu_C`$, and the claim on $`(X_4, \nu_C]`$. The gap is (P) and (Q) at one named pair. (P) is a lower bound and (Q)
  an upper bound for the reaches of long restarts (zone C), which no current tool gives.

## 2. Native codes: an operator hierarchy below $`\Omega_1^\omega`$, and $`\iota(\mathrm{CH}_2) \ge Z_K`$

Notation of [THETA.md](THETA.md) §2 and §9.2: $`F(\alpha) = \upsilon_{1+\alpha}`$, $`H'(\Delta) = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\Delta})`$. A position is an ordinal $`P \lt \Omega_1^\omega`$, written in base
$`\Omega_1`$ with countable coefficients. $`O_1`$ enumerates the fixed points, $`O_{P+1}`$ is the diagonal of $`O_P`$, limits of a coefficient are intersections, and at
$`P = Q + \Omega_1^l\cdot(\mu+1)`$ with $`l \ge 1`$ the operator $`O_P(H)`$ enumerates the $`z`$ with $`O_{Q + \Omega_1^l\cdot\mu + \Omega_1^{l-1}\cdot z}(H)(0) = z`$. The operators $`O_n`$, $`S`$, $`T`$ of
[THETA.md](THETA.md) §9.2 are the positions $`n`$, $`\omega`$, $`\omega+1`$.

- **OP-K, POS, DATA, DOM-K, NO-HIGH-K** (proved; the referee checked every case and the order of the recursion). Every $`O_P`$ is an operator; every
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
  $`\mathrm{LT}(u_n)`$ holds for all large $`n`$ and $`\mathrm{LT}(x)`$ fails.
- **Not proved** (blocking points): (B1) "SEP and ROOM fail only at restarts with index in $`K^{f_\Delta}`$ or with top data" is false: a small restart that is not
  in the realization can make a run point a term of a reach. (B2) "CAND-2 is equivalent to one pattern" is false: CAND-2 is a countable union of
  patterns, one for each $`j`$. ROOM-RED misses one case (a long restart whose preimage is not a restart) and shows only "if". The list of the residue is
  exhaustive once that case is added.
- **Not proved**: $`\nu_C = \nu_S`$, and $`\nu_C \lt \nu_S`$. Neither $`\mathrm{LT}(u_n)`$ nor $`\mathrm{LT}(x)`$ is decided; no long restart has a closed-form reach. Conjecture U-TAIL: no ghost of
  this kind. Open: the map $`T`$ on $`[u^\#, \lambda^\Delta_u)`$, and SEP and ROOM in general.

## 5. Status after the fifteenth round

- Wilken's claim in $`R_2^C`$: both halves hold on $`[0, X_4]`$ with $`X_4 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{G_2+1}\cdot 2)`$, no FRAG; the core half holds on
  $`[0, \nu_C]`$ with $`\nu_C \ge X_4`$. An upper bound for $`\nu_C`$ needs only (P) and (Q) at one named pair.
- The lower-bound program below $`\theta_0`$: the step below SRO is proved for every $`n`$ on 2,526 of the 3,166 sample matrices; $`\iota(\mathrm{CH}_2) \ge Z_K`$ natively.
- Upper bounds: still none by an InaccPsi term for $`\iota(\mathrm{CH}_k)`$, $`m_F`$, $`x_F`$, $`C^*_3`$ or $`\nu_C`$.
- $`\nu_C = \nu_S`$: (PROF) is closed; the residue is SEP and ROOM, which come down to the reaches of long restarts; the test of §4 gives a ghost iff $`\mathrm{LT}`$ differs at
  $`x`$ and at the $`u_n`$.

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
