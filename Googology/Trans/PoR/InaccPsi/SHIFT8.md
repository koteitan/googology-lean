[← Back](README.md) | [English](SHIFT8.md) | [Japanese](SHIFT8-ja.md)

# $`R_2^+`$, the thirty-third round: Theorem B$`^\nu`$, the skeleton of the points $`L(e)`$ up to $`L(\Omega_1\cdot\omega)`$, the residue of the audit, and native codes up to $`\psi_{\Omega_1}(\Omega_{\omega+1} + \sigma_{\omega+1})`$

This page continues [SHIFT7.md](SHIFT7.md) (§3 there is the thirty-second round); §1 is the thirty-third round. The status words are those of [README.md](README.md) §3: **proved** means that
an independent referee found the result proved with no fatal or blocking point. A statement with a blocking point against it is listed under **Not proved**.
A certificate counts only when it was replayed. A result that the referee calls only a restatement of something known is not counted as progress.

## 1. The thirty-third round

Three papers (2026-10), each refereed once: a paper that repairs Theorem B$`^\nu`$ and goes on along the skeleton of the points $`L(e)`$ (§1.1), a paper on the residue of the audit and on
$`R_2^S`$ above $`\nu`$ (§1.2), and a paper on native codes (§1.3). A result in this section has 1 review unless a count is given. Theorem B$`^\nu`$ (the claim on $`[0, L(\omega^2)]`$) is proved in
the first two papers independently, so it has **2 reviews**. The minor points of the three reviews of [SHIFT7.md](SHIFT7.md) §3 are applied by these papers, and a referee of this round
checked each repair (**2 reviews**). None of the papers uses Wilken, JSL 72 (2007), Carlson, AML 38 (1999), or Wilken, AML 45 (2006) (the referees checked this). Papers cited, in §1.1 and
§1.2: [W07b] (Cor 5.10, and L.2.1 and Thm 2.2 only through the project's own proof of them), Carlson 2009 (Def 5.3 clause 2, L.2.5, L.5.5, Thm 14.14) and Wilken 2020 (L.21.7, L.21.10,
L.21.12 (1), Prop. 21.6, Prop. 21.11); the referees checked every citation against the paper text. No paper is used in a proved step of §1.3, which does not use FRAG; its facts on
$`\psi`$ come from the Lean development of InaccPsi (the referee checked every cited line with leanman). No Lean file was added: the paper of §1.1 checked its ordinal inputs with a Lean
file that only compares terms (`#eval`, no theorem; green, and identical in the referee's rerun); this counts as a check. Levels are numbered as in [SHIFT7.md](SHIFT7.md) (one higher than in
the papers). "Given FRAG" means given FRAG with FRAG-SUBST, SUBST-COMM and the own proof of [W07b] Thm 2.2.

Notation (as in [SHIFT7.md](SHIFT7.md) §3.2): $`L(e) = H(\eta_e) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + P'\cdot e)`$, $`P' = \psi_{\Omega_2}(\Omega_\omega\cdot 2)`$, and the gap of $`L(e)`$ is $`[L(e), L(e+1))`$; $`\nu = L(\omega+1)`$. A **restart of the
skeleton** is $`L(\lambda'')`$ with $`\lambda''`$ a nonzero multiple of $`\omega^2`$; its pairs are $`\tau''_j = L(\lambda''+\omega\cdot j)`$, $`\delta''_j = L(\lambda''+\omega\cdot j+1)`$ ($`j \ge 1`$), and its **skeleton code** is
$`c''(\lambda'') = -1 + \mathrm{logend}(\lambda'')`$. A **base point** is a $`p`$ with $`\mathrm{lh}(\alpha) \lt p`$ for every $`\alpha \lt p`$. The **cap point** of a restart $`R`$ is $`H(\eta_R + \Lambda_R + \omega^2)`$.

### 1.1 Theorem B$`^\nu`$, and the skeleton of the points $`L(e)`$ up to $`L(\Omega_1\cdot\omega)`$, given FRAG

- **The repairs of the review of [SHIFT7.md](SHIFT7.md) §3.2** (its blocking point B-1 and its minor points m1, m2, m4). DECOUPLE: the clause on $`+`$ is kept only below the cap (m4; proved).
  FRAG2$`^{\mathrm{rel}}`$ (proved, given FRAG): the proof of FRAG2 uses the skeletal hypothesis only in the form "both ends of every $`\lt_2`$-pair are $`\upsilon`$-points", which holds at every countable stage
  of $`R_2^S`$, so FRAG2 holds above $`\nu`$ too, with pairs in the fixed set (m2). BASE-INV$`^{\mathrm{reg}}`$ (proved): for a fixed point $`x`$, either $`\mathrm{lh}(x) \lt \rho_R`$ (the relation to a moved point is false on
  both sides) or $`x \le_1 \rho_R`$ (true on both sides, inside the induction); no reach of a point $`L(e)`$ is needed, so the circular case is gone (m1). GAP-CALC$`^{\mathrm{reg}}`$ (proved by transfer, given FRAG):
  the exact calculus of level 2 holds at every restart $`R`$ inside a gap whose cap point is at most the current bound $`y`$, with no condition on the end of the gap (the region form of CAP-1 in
  [SHIFT7.md](SHIFT7.md) §1.1; this is the repair of B-1).
- **Theorem B$`^\nu`$** (proved by transfer, given FRAG; **2 reviews**, with §1.2). For every $`j \ge 1`$, $`L(\omega\cdot j) \lt_2 L(\omega\cdot j+1)`$ in $`R_2^S`$ and in $`R_2^C`$; these are all the new pairs with right
  end below $`L(\omega^2)`$; every restart below $`L(\omega^2)`$ has an exact reach; $`\beta_0 \gt L(\omega^2)`$; so **Wilken's claim holds in $`R_2^C`$ on $`[0, L(\omega^2)]`$**, with $`L(\omega^2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+2})`$.
  The blocked step LOW$`_j`$ (the least top above the cap $`L(\omega\cdot(j-1)+1)`$ is at least $`L(\omega\cdot j+1)`$) now holds: a $`\le_1`$-predecessor $`u`$ of the left end $`x`$ that lies inside a gap meets
  the region condition, so GAP-CALC$`^{\mathrm{reg}}`$ says that $`u`$ does not cross itself, while it does; so the predecessors are points $`L(e)`$, and $`x = L(e_x)`$ with $`e_x`$ a limit. The side of $`R_2^C`$:
  KAPPA and C-TRANSFER (if $`R_2^S`$ is skeletal for the points $`L(e)`$ below $`Z`$, then $`\beta_0 \gt Z`$).
- **FRAG″** (parts (a)–(c) proved, given FRAG; part (d) and FRAG2″ proved by transfer, below the frontier only, minor point m2). Finitely many points $`L(e_1) \lt \dots \lt L(e_m)`$ move at
  once to $`L(e'_1) \lt \dots \lt L(e'_m)`$, each with its gap, by the η-base changes of BC$`^\pi`$ with lower maps. The composite is the map of Theorem FRAG at the $`\upsilon`$-points of the finite
  hereditary closure (FRAG-SUBST″); it keeps $`0, +, \le, \le_1`$ of $`R_1^+`$, the $`\upsilon`$-points, the restarts and the block tops (SUBST-COMM″), and the exact reaches of the restarts inside
  the gaps (TC⁺″). FRAG2″: it keeps $`\le_2`$ exactly when it keeps the reaches of the moved points $`L(e)`$ and the pairs with a moved end.
- **FIX″, IDX″, TAIL″** (proved; checked by the referee on 67 samples). $`L(\Omega_1\cdot k)`$ is the $`k`$-th fixed point of $`e \mapsto L(e)`$, the supremum of the iterates $`e_{n+1} = L(\Omega_1\cdot(k-1) + e_n)`$;
  the least is $`L(\Omega_1) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+\Omega_1})`$. Below $`\Omega_1\cdot\omega`$, $`L`$ is strictly increasing and continuous on its domain.
- **The restart calculus of the skeleton** (BLOCK″$`_0`$, EXACT-C″, EXACT-Ω″, CAP″; proved by transfer, given FRAG). For a restart $`L(\lambda'')`$ of the skeleton with $`\lambda'' \lt \Omega_1\cdot\omega`$ and
  $`\delta''_1(\lambda'') = L(\lambda''+\omega+1)`$:

```math
r(L(\lambda'')) = \delta''_1(\lambda'') + c''(\lambda'')\ \ (c''(\lambda'') \text{ countable}),\qquad r(L(\Omega_1\cdot k)) = \delta''_1(\Omega_1\cdot k) + L(\Omega_1\cdot k).
```

  For example $`r(L(\omega^2)) = L(\omega^2+\omega+1) + 1`$ and $`r(L(\Omega_1)) = L(\Omega_1+\omega+1) + L(\Omega_1)`$. These are EXACT-C ($`r = \delta + (-1 + e)`$) and the first case of EXACT-W ($`r = \delta + \rho`$) one step up,
  with the skeleton code for $`-1 + e`$ and the point $`L(\lambda'')`$ itself for $`\rho`$.
- **Theorem C″** (proved by transfer, given FRAG). Below $`L(\Omega_1\cdot\omega)`$, $`R_2^S`$ is skeletal for the skeleton of the points $`L(e)`$ (the conjecture SKEL″ of [SHIFT7.md](SHIFT7.md) §3.2 holds
  there): every new pair is a pair $`(\tau''_j, \delta''_j)`$ and contains no new pair; a point $`L(e)`$ that is not a restart of the skeleton reaches exactly its block top; every restart below
  $`L(\Omega_1\cdot\omega)`$ has an exact reach (the codes at level 2 up to $`P' + \Omega_1`$); there is no fan apex and no triple nest below it.
- **The new frontier** (proved by transfer, given FRAG). $`R_2^C = R_2^S`$ on every relation with right end below $`L(\Omega_1\cdot\omega)`$ ($`\beta_0 \gt L(\Omega_1\cdot\omega)`$), the least top of a triple nest lies above it in
  both structures, and **Wilken's claim holds in $`R_2^C`$ on $`[0, L(\Omega_1\cdot\omega)]`$**, both halves (the names half because the point is a normal form, Lemma L):

```math
L(\Omega_1\cdot\omega) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+\Omega_1+1}).
```

- The referee's minor points (none changes a result). The step that gives $`\beta_0 \gt L(\Omega_1\cdot\omega)`$ cites GAP-CALC$`^{\mathrm{reg}}`$ with the frontier itself as the bound, where its hypothesis is false
  (the pairs $`(\tau''_j, \delta''_j)`$ end there); its conclusion holds block by block, which is all that is used (m1). Part (d) of FRAG″ and FRAG2″ are stated for every $`L(e) \lt \psi_{\Omega_1}(\Omega_\omega\cdot 3)`$, but
  proved only below the frontier, where every use lies (m2). The paper lists the residue item R-1 as settled; it is written in §1.2 (m3). One bound $`\Lambda + \omega^2 \lt \omega^m`$ is false for codes $`m \le 2`$;
  the inequalities that are used hold (m4). BASE-INV$`^{\mathrm{reg}}`$ is stated for restarts inside gaps and used at the points $`L(e)`$; the proof is the same (m5). Wording, and an unstated fact
  on the hull for indices outside the domain; $`L(\Omega_1)`$ is not in the domain of $`L`$ (m6, m7). One family of checks is covered by BASE-INV$`^{\mathrm{reg}}`$ but not written out (m8).
- **Not proved** (outline or conjecture). EXACT-W″: $`r(L(\Omega_1\cdot\omega)) = L(\Omega_1\cdot\omega+\omega+1) + L(\Omega_1\cdot\omega) + 1`$ (outline only); with it the frontier would move to
  $`L(\Omega_1^2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+\Omega_1\cdot 2})`$. Skeleton codes from $`\Omega_1\cdot 2`$ on, long restarts of the skeleton, the code $`P_3`$ and $`\nu_3`$: open or conjecture (LIFT$`_2`$: the analysis
  of $`[0, \psi_{\Omega_1}(\Omega_\omega\cdot 2))`$ moves to the skeleton with $`(\Omega_\omega, \theta)`$ replaced by $`(\Omega_\omega\cdot 2, P')`$).

### 1.2 The residue of the audit, and $`R_2^S`$ above $`\nu`$

- **LONG-RS$`^{\mathrm{rel}}`$** (proved, given FRAG, with the referee's m1 and m2; the residue item R-1 of [SHIFT7.md](SHIFT7.md) §3.1). The long-restart step across η-offsets below $`\omega^c`$ for any code
  $`c \lt \Omega_2`$ with $`c`$ at most the code of the restart, at every level and above any cap; its transport is a base change without a copy, the fixed points are handled by XA$`^p`$, and the base
  changes by FRAG2$`^{\mathrm{rel}}`$. CAP-SUPPLY gives its reach hypothesis for every code below $`P'`$. Every use that R-1 names is an instance, among them CROSS-LIM. The referee: XA$`^p`$ is false as
  written, because its bound must also exceed $`\mathrm{lh}(x)`$ for the fixed points $`x`$ that are not restarts (counterexample given; m1); for a restart whose code is a $`\pi`$-code the instance must take
  $`c = D' + 1`$ (m2). Both repairs are one line. So the lemma that the chain to $`\nu_C`$ used without writing it is now written ([AUDIT.md](AUDIT.md)).
- **2.6′ and TC⁺$`^{\mathrm{rel}}`$** (proved by transfer; R-2 and L3-b). The transport identities of the calculus hold for a base change without a copy (a "bare base"), and reaches commute with
  such a base change for every code below $`P'`$. The citations in CROSS-LIM, TC⁺$`^\omega`$ and PAIR$`_j`$ now cite them.
- **The audit rows at level 2** (proved by transfer; L2-a, L1-b, L2-b). One row for each statement moved to level 2, with its replaced input; every step that depends on the index $`\eta`$ is of one of
  six known kinds, each supplied at level 2. The referee checked a sample of the rows, not every one.
- **CNST$`_j`$ past $`\theta`$** (checked; L1-a). With countable constants, and with the forms read directly: 1,597 subforms at the first threshold, 449 and 48 further up, 0 failures; two broken
  versions of the rule fail 1,321 and 542 times. The referee: a new seed, 4,632 subforms, 0 failures, and a structural reason; the order test is only a consistency check (its control is
  insensitive), and the 48 are probably one set of 24 counted twice (m6).
- **AGREE$`^\nu`$** (proved by transfer, given FRAG). $`y^C_\nu = y^S_\nu = L(\omega\cdot 2+1) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+1}\cdot 2 + P')`$: there is no difference between the two structures on $`[\nu, y^C_\nu]`$, and
  $`\beta_0 \gt L(\omega\cdot 2+1)`$. So Theorem A$`^\nu`$ of [SHIFT7.md](SHIFT7.md) §3.2 holds with its exact top. The same text for every $`j`$ gives the second proof of Theorem B$`^\nu`$. $`\beta_0`$ itself is not located.
- The referee's other minor points: $`1 + m = m`$ for infinite $`m`$, the bound still holds (m3); one domain condition follows from CODE-ORD and is not argued (m4); the crossing at $`m^*`$ across two
  levels has no audit row (m5; not used here); wording (m7).

### 1.3 Native codes: the $`\Omega_{\omega+1}`$ unit and $`\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega_{\omega+1} + \sigma_{\omega+1})`$

Write $`S_1 = \Omega_\omega`$, $`S_{m+1} = \psi_{\Omega_{\omega+1}}(\Omega_\omega\cdot S_m)`$ and $`\sigma_{\omega+1} = \sup_m S_m = \psi_{\Omega_{\omega+1}}(\Omega_{\omega+1})`$, as in [SHIFT7.md](SHIFT7.md) §3.3.

- **The minor points of the review of [SHIFT7.md](SHIFT7.md) §3.3 are applied** (**2 reviews**): the example term (m1), the formal decorations $`A(z)`$ (m2), the scope hypothesis of ATOM-SUP (m3), the
  labels "by transfer" (m4), wording (m5, m7), and the hostings without certificate support are marked as proved by hand (m6).
- **The ordinal side** (proved; STAGE$`^{SS}`$ and PUSH$`^{SS}`$ by transfer). The stages in $`[\sigma_{\omega+1}, \Omega_{\omega+1})`$ are bad at every finite level (BAD-INT); the stages $`\Omega_{\omega+1} + T`$ with $`T \lt \sigma_{\omega+1}`$
  are good (GOOD$`^{\omega+1}`$); $`\psi_{\Omega_j}(\Omega_{\omega+1}) = \sup_m \psi_{\Omega_j}(S_m)`$ for every $`j \ge 1`$ (SUP-(ω+1)$`_j`$); the stage systems work with the bad interval left out; and (SUP-W1S)

```math
\psi_{\Omega_1}(\Omega_{\omega+1} + \sigma_{\omega+1}) = \sup_m \psi_{\Omega_1}(\Omega_{\omega+1} + S_m).
```

- **The $`\Omega_{\omega+1}`$ unit** (proved by transfer). The unit $`r \lt x \lt y \lt c`$ with $`x \lt_2 y`$, $`c \le_1 c\cdot 4`$ and $`r, x \le_1 c\cdot 4`$ is the universal top unit of [SHIFT7.md](SHIFT7.md) §3.3 used as the
  top unit of a region; its hosting lemma OMEGA-SUP is the earlier universal hosting lemma word for word (the referee: label it cited), and the top of the module moves to $`c\cdot 5`$. The codes
  keep chain number 3, so with MODULE-RED$`_4`$, natively:

```math
\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega_{\omega+1} + \psi_{\Omega_{\omega+1}}(\Omega_{\omega+1})) \gt \psi_{\Omega_1}(\Omega_{\omega+1} + 1),
```

  and RED-TOWER holds with $`\mathrm{CH}_4`$ below this point. The bound for $`\mathrm{CH}_3`$ stays $`\psi_{\Omega_1}(\varepsilon_{\Omega_\omega+1})`$. These are lower bounds only.
- **The frontier of this route** (FRONTIER, proved given STAGE). Every stage set past $`\Omega_{\omega+1} + \sigma_{\omega+1}`$ contains that stage, whose atom $`\sigma_{\omega+1}`$ has the region's own $`\Omega_{\omega+1}`$ as its
  argument. No existing unit kind codes it (a remark, not a theorem). Conjecture REF: a marker point inside the pair of the unit can stand for $`\Omega_{\omega+1}`$, with chain number 4, up to
  $`\psi_{\Omega_1}(\Omega_{\omega+1}\cdot 2)`$; its hosting lemma REF-SUP is open.
- **Toward $`\theta_0`$, the ordinal side** (proved). SUP-(ρ+1) for every base-free $`\rho`$ (by transfer); $`\psi_{\Omega_1}(\Omega_{\omega\cdot 2}) = \sup_n \psi_{\Omega_1}(\Omega_{\omega+n})`$; $`\psi_{\Omega_1}(\Omega_{\Omega_1}) = \sup_m t_m`$ with
  $`t_{m+1} = \psi_{\Omega_1}(\Omega_{t_m+1})`$ (after the referee's rewrite of one step, m1); and, with $`u_1 = \Omega_1`$, $`u_{m+1} = \Omega_{u_m}`$, $`\psi_{I_0}(0) = \sup_m u_m`$ and $`\theta_0 = \sup_m \psi_{\Omega_1}(u_m)`$. So the native side
  needs two tools before $`\theta_0`$: references to $`\Omega`$ at every index, and $`\Omega`$ units indexed by their own argument codes. Both are open.
- The referee's other minor points: the header overstates SUP-(ρ+1), which is proved for base-free $`\rho`$ only (m2); the $`\Omega_{\omega+1}`$ unit is the top (last) unit of its region (m3); one sentence of
  FRONTIER is false as written and the header says more than FRONTIER (m4); a replaced fact of STAGE$`^{SS}`$ should be stated (m5); labels (m6); the referee's toy certificate is the only
  certificate support of OMEGA-SUP (m7).

### 1.4 Status after the thirty-third round

- Wilken's claim in $`R_2^C`$: both halves hold on $`[0, X_4]`$ without FRAG, and **on $`[0, L(\Omega_1\cdot\omega)]`$ given FRAG, with $`L(\Omega_1\cdot\omega) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+\Omega_1+1})`$** ($`[0, X_{21}]`$ with 2 reviews;
  up to $`\nu_C = \nu_S = L(\omega+1)`$ with 1 review and an audit, the residue of the audit now written, §1.2; from $`\nu_C`$ to $`L(\omega^2)`$ with 2 reviews, two proofs; from $`L(\omega^2)`$ to $`L(\Omega_1\cdot\omega)`$ with
  1 review, §1.1).
- $`R_2^S`$ against $`R_2^C`$: the two agree on every relation with right end below $`L(\Omega_1\cdot\omega)`$, and $`y^C_\nu = y^S_\nu = L(\omega\cdot 2+1)`$ (given FRAG). $`\beta_0`$ is not located.
- Reaches (given FRAG): exact for every restart below $`L(\Omega_1\cdot\omega)`$.
- **LOW: false, given FRAG**; **LOW$`^\infty`$: true, given FRAG** (1 review each; no change).
- The lower-bound program below $`\theta_0`$: native bounds $`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\varepsilon_{\Omega_\omega+1})`$ and $`\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega_{\omega+1} + \sigma_{\omega+1})`$ (1 review each). The step below SRO: no
  change (every $`n`$ on all 3,166 sample matrices; the general statement for all standard matrices below SRO is open).

### 1.5 Checks of the thirty-third round

Each run was under 60 seconds; none is a proof.

- §1.1. Names, normal forms, membership of the indices in the domain, and order of the points of the regions of $`\omega^2`$, $`\omega^3`$, $`\omega^\omega`$, $`\varepsilon_0`$, $`m^*`$, $`\Omega_1`$, $`\Omega_1\cdot 2`$, of the fixed
  points $`L(\Omega_1\cdot k)`$ and of $`L(\Omega_1\cdot\omega)`$; the controls (indices that must not be in the domain) are not; Lean green, identical to Python. The referee: FIX″ on 67 samples, the targets
  of EXACT-C″ on 80 cases, the realizers of CROSS-LIM″ on 10 cases, all hold; the Lean rerun identical.
- §1.2. The numbers above; the referee also checked six $`\pi`$-codes for the premise of m2 (6 of 6) and reran the Lean file of [SHIFT7.md](SHIFT7.md) §3.2 (identical).
- §1.3. Names on two seeds, 111 checks each, 0 failures; six codes with an $`\Omega_{\omega+1}`$ unit and the top have chain number 3, the mutant 4. Certificates (replayed): forward 2 of 5, the top below
  $`\mathrm{CH}_4`$ found; the hostings by the universal unit and two hostings with new argument codes timed out at 45 seconds; reverse 0 of 3. The referee: a new seed, 0 failures; own tests on three
  seeds (about 1,560 bad stages, 6,400 good stages, and the supremum lemmas), 0 failures; a toy certificate found (an $`\Omega_{\omega+1}`$ unit hosts a $`\psi`$ unit), its reverse not found.

### 1.6 Open

- The claim above $`L(\Omega_1\cdot\omega)`$ given FRAG (above $`X_4`$ without FRAG). Next: EXACT-W″ at $`L(\Omega_1\cdot\omega)`$, then $`L(\Omega_1^2)`$; then skeleton codes from $`\Omega_1\cdot 2`$ on, long restarts of
  the skeleton, the code $`P_3`$ and $`\nu_3`$. In $`R_2^S`$: $`o_k = \omega`$ for the levels above $`\nu`$ without FRAG.
- The crossing at $`m^*`$ across two levels as its own step with its audit row (minor m5 of §1.2).
- $`R_2^S = R_2^C`$ above $`L(\Omega_1\cdot\omega)`$, and $`\beta_0`$ itself; the core half in $`R_2^S`$ above $`\upsilon_{\omega^3}`$.
- Bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$, and an upper bound for $`\iota(\mathrm{CH}_3)`$.
- The first inaccessible: chain number 3 past $`\varepsilon_{\Omega_\omega+1}`$; past $`\psi_{\Omega_1}(\Omega_{\omega+1} + \sigma_{\omega+1})`$ the references REF (target $`\psi_{\Omega_1}(\Omega_{\omega+1}\cdot 2)`$), then $`\Omega_{\omega\cdot 2}`$, $`\Omega_{\Omega_1}`$
  and the tower of $`\Omega`$'s up to $`\theta_0`$; $`\mathrm{CH}_2`$ past $`\Theta_1`$; the step for all standard matrices below SRO.
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; an InaccPsi formula for the reach in terms of the code; names above $`\nu`$ for the points that are not
  $`\upsilon`$-points; the rest of [COVER.md](COVER.md) §9.
