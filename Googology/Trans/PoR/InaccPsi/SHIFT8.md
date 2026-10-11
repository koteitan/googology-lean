[← Back](README.md) | [English](SHIFT8.md) | [Japanese](SHIFT8-ja.md)

# $`R_2^+`$, the thirty-third and thirty-fourth rounds: Theorem B$`^\nu`$, the skeleton of the points $`L(e)`$ up to $`L(\varepsilon_{\Phi_\Omega+1})`$, the residue of the audit, Carlson's categoricity theorem for $`R_2^S`$, and native codes up to $`\psi_{\Omega_1}(\Omega_{\omega+1}^2 + \sigma_2)`$

This page continues [SHIFT7.md](SHIFT7.md) (§3 there is the thirty-second round); §1 is the thirty-third round, §2 the thirty-fourth; the thirty-fifth to thirty-seventh rounds are on [SHIFT9.md](SHIFT9.md), the thirty-eighth to fortieth on [SHIFT10.md](SHIFT10.md), the forty-first to forty-third on [SHIFT11.md](SHIFT11.md). The status words are those of [README.md](README.md) §3: **proved** means that
an independent referee found the result proved with no fatal or blocking point. A statement with a blocking point against it is listed under **Not proved**.
A certificate counts only when it was replayed. A result that the referee calls only a restatement of something known is not counted as progress.

**Later (the fortieth round, [SHIFT10.md](SHIFT10.md) §3.2):** the results of this page above $`\nu_C`$ rest on $`\nu_C = \nu_S = L(\omega+1)`$ ([SHIFT7.md](SHIFT7.md) §2.1) and on the exact calculus in the gaps (GAP-CALC$`^{\mathrm{reg}}`$), whose long codes use the old exact long value; they are **not proved as written**: Theorem B$`^\nu`$ and $`L(\omega^2)`$, FRAG″ (d), FRAG2″, Theorem C″ and $`L(\Omega_1\cdot\omega)`$ (§1.1), CAP-SUPPLY (ii) and $`R_2^S`$ above $`\nu`$ (§1.2), $`L(\varepsilon_{\Phi_\Omega+1})`$ (§2.1), and AGREE⁺ with the claim in $`R_2^S`$ (§2.2). They stand: FRAG2$`^{\mathrm{rel}}`$, DECOUPLE, BASE-INV$`^{\mathrm{reg}}`$, FIX″, IDX″, TAIL″, LONG-RS$`^{\mathrm{rel}}`$ as a lemma, Carlson's categoricity theorem with MIN$`^S`$, LEAST, CAT, CAT-$`\beta_0`$, CAT-E, O$`^S`$, C-TRANSFER$`^{\mathrm{RIG}}`$, GHOST-SHAPE, and the native codes. Given FRAG, the claim is proved in $`R_2^C`$ on $`[0, X_{21}]`$. **Later (the forty-first round, [SHIFT11.md](SHIFT11.md) §1.1):** $`\nu_C = \nu_S = L(\omega+1)`$ and the claim on $`[0, \nu_C]`$ are proved again, given FRAG; the exact calculus in the gaps above $`\nu_C`$ is not yet run again, so the results of this page above $`\nu_C`$ stay not proved as written.

**Later (the forty-second round, [SHIFT11.md](SHIFT11.md) §2.1, §2.2):** the gap calculus is run again on the corrected values. Theorem B$`^\nu`$ and $`L(\omega^2)`$, FRAG″ (d), FRAG2″, Theorem C″ and $`L(\Omega_1\cdot\omega)`$, CAP-SUPPLY (ii) and $`L(\varepsilon_{\Phi_\Omega+1})`$ are proved again in $`R_2^C`$, given FRAG (1 review of the re-run). The $`R_2^S`$ side of §1.2 and §2.2 is not re-run line by line (an outline); in $`R_2^S`$ the claim now holds on $`[0, F_\nu)`$, given FRAG ([SHIFT11.md](SHIFT11.md) §2.2). **Later (the forty-third round, [SHIFT11.md](SHIFT11.md) §3.2):** in $`R_2^S`$ the claim holds on $`[0, Z^\Lambda)`$, given FRAG, so the ranges of this page in $`R_2^S`$ are covered.

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
- **Not proved** (outline or conjecture). EXACT-W″: $`r(L(\Omega_1\cdot\omega)) = L(\Omega_1\cdot\omega+\omega+1) + L(\Omega_1\cdot\omega) + 1`$ (outline only; proved in the thirty-fourth round, §2.1); with it the frontier would move to
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

Superseded by §2.4.

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

Superseded by §2.6.

- The claim above $`L(\Omega_1\cdot\omega)`$ given FRAG (above $`X_4`$ without FRAG). Next: EXACT-W″ at $`L(\Omega_1\cdot\omega)`$, then $`L(\Omega_1^2)`$; then skeleton codes from $`\Omega_1\cdot 2`$ on, long restarts of
  the skeleton, the code $`P_3`$ and $`\nu_3`$. In $`R_2^S`$: $`o_k = \omega`$ for the levels above $`\nu`$ without FRAG.
- The crossing at $`m^*`$ across two levels as its own step with its audit row (minor m5 of §1.2).
- $`R_2^S = R_2^C`$ above $`L(\Omega_1\cdot\omega)`$, and $`\beta_0`$ itself; the core half in $`R_2^S`$ above $`\upsilon_{\omega^3}`$.
- Bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$, and an upper bound for $`\iota(\mathrm{CH}_3)`$.
- The first inaccessible: chain number 3 past $`\varepsilon_{\Omega_\omega+1}`$; past $`\psi_{\Omega_1}(\Omega_{\omega+1} + \sigma_{\omega+1})`$ the references REF (target $`\psi_{\Omega_1}(\Omega_{\omega+1}\cdot 2)`$), then $`\Omega_{\omega\cdot 2}`$, $`\Omega_{\Omega_1}`$
  and the tower of $`\Omega`$'s up to $`\theta_0`$; $`\mathrm{CH}_2`$ past $`\Theta_1`$; the step for all standard matrices below SRO.
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; an InaccPsi formula for the reach in terms of the code; names above $`\nu`$ for the points that are not
  $`\upsilon`$-points; the rest of [COVER.md](COVER.md) §9.

## 2. The thirty-fourth round

Three papers (2026-10), each refereed once: a paper on the reach of $`L(\Omega_1\cdot\omega)`$ and on the skeleton codes up to $`\varepsilon_{\Phi_\Omega+1}`$ (§2.1), a paper on $`R_2^S`$ against $`R_2^C`$ with
Carlson's categoricity theorem (§2.2), and a paper on native codes (§2.3). A result in this section has 1 review unless a count is given. The claim on $`[0, Z^+]`$ (notation below) is
proved in the first two papers independently, so the step from $`L(\Omega_1\cdot\omega)`$ to $`Z^+`$ has **2 reviews**. The minor points of the three reviews of §1 are applied by these papers, and a
referee of this round checked each repair (**2 reviews**). None of the papers uses Wilken, JSL 72 (2007), Carlson, AML 38 (1999), or Wilken, AML 45 (2006) (the referees checked this).
Papers cited: in §2.1 only through refereed stages, as in §1; in §2.2 T. J. Carlson, "Categoricity for patterns of order 2", https://arxiv.org/abs/1104.1686 ([C11]: the Categoricity
Theorem, Claim 1 in its proof, Cor 0.8, Cor 0.9), with Carlson 2009 (Def 5.3 clause 2, L.5.5, L.14.9, Thm 14.10, Thm 14.14). [C11] is an arXiv preprint, not refereed; the referee re-did its
Claim 1 and wrote out the step it calls straightforward (the map is well defined on overlaps), and both hold. No paper is used in a proved step of §2.3, which does not use FRAG. No Lean
file was added: the ordinal inputs of §2.1 and §2.2 were checked with Lean files that only compare terms (`#eval`, no theorem; green, identical to Python), and §2.3 checked the
statements of the cited InaccPsi lemmas (`#check`); these count as checks. Levels are numbered as in §1 (one higher than in the papers). "Given FRAG" is as in §1.

Notation (as in §1): $`\Phi_\Omega = \psi_{\Omega_2}(\Omega_2)`$ ([SHIFT2.md](SHIFT2.md) §2), and

```math
Z^+ = L(\Omega_1\cdot\omega+\omega+1) = \delta''_1(\Omega_1\cdot\omega) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+\Omega_1+1} + \omega^{P'+1} + P').
```

For a skeleton code $`c`$ and a point $`b`$, $`c[\Omega_1 := b]`$ is $`c`$ with $`\Omega_1`$ replaced by $`b`$ ($`\Gamma_{\Omega_1+1+\beta} = \psi_{\Omega_2}(\beta)`$ becomes $`\Gamma_{b+1+\beta}`$, and $`\Phi_\Omega`$ the least
fixed point of $`\alpha \mapsto \Gamma_\alpha`$ above $`b`$). The domain of $`L`$ is the set of $`e`$ for which $`\eta_e`$ is the index of a $`\upsilon`$-point.

### 2.1 The reach of $`L(\Omega_1\cdot\omega)`$, and the claim up to $`L(\varepsilon_{\Phi_\Omega+1})`$, given FRAG

- **The repairs of the review of §1.1** (m1–m8; **2 reviews**). (Z3) and part (b) of Theorem C″ are stated block by block: each gap restart uses GAP-CALC$`^{\mathrm{reg}}`$ with the base point and
  the bound of its own block, and C-TRANSFER needs only the conclusion (m1). Part (d) of FRAG″ and FRAG2″ are restricted to the gaps below the frontier (m2). Every use of the long-restart
  step cites LONG-RS$`^{\mathrm{rel}}`$ of §1.2 with the repairs m1 and m2 of its review, also at a base point that is not a bare cap (m3). The bound for small codes, BASE-INV$`^{\mathrm{reg}}`$ for every
  restart, and wording (m4–m8).
- **The domain of $`L`$** (DOM″, DOWN″, COF″, TAIL″, FIX2″; proved). For every $`e \lt \varepsilon_{\Phi_\Omega+1}`$: $`e`$ is in the domain exactly when every countable constant of $`e`$ is below $`L(e)`$ (DOM″).
  The domain is closed under initial parts of normal forms (DOWN″), $`L`$ is continuous at its limits (COF″), the tails of a restart of the skeleton have smaller codes (TAIL″), and
  $`L(\Omega_1^2)`$ is the least fixed point of $`\zeta \mapsto L(\Omega_1\cdot\zeta)`$ (FIX2″).
- **The tools at a base of the skeleton** (proved by transfer). The Veblen and $`\Gamma`$ lemmas of the reading below $`\upsilon^*`$ hold at every $`\upsilon`$-point, with their $`\varepsilon`$-closure (their
  proofs never use the bound $`\upsilon^*`$); the substitution map of FRAG is the projection that these lemmas use. PIN-S″ (without FRAG) and TOP-REG″ (without FRAG, inside the induction) are the
  upper-bound tools at a base $`L(\lambda'')`$.
- **EXACT-W″ at $`L(\Omega_1\cdot\omega)`$** (proved by transfer, given FRAG; the outline of §1.1, now written in full with sums only):

```math
r(L(\Omega_1\cdot\omega)) = Z^+ + L(\Omega_1\cdot\omega) + 1.
```

  More generally $`r(L(\lambda'')) = \delta''_1(\lambda'') + L(\lambda'') + a`$ for every restart of the skeleton below $`L(\Omega_1^2)`$ with code $`\Omega_1 + a`$, $`a`$ countable. So the claim holds on
  $`[0, L(\Omega_1^2)]`$, $`L(\Omega_1^2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+\Omega_1\cdot 2})`$.
- **Theorem EXACT-G″** (proved by transfer, given FRAG, for $`\lambda'' \lt \varepsilon_{\Phi_\Omega+1}`$). For every restart $`L(\lambda'')`$ of the skeleton with $`\lambda'' \lt \varepsilon_{\Phi_\Omega+1}`$ and code $`c = c''(\lambda'')`$:

```math
r(L(\lambda'')) = \delta''_1(\lambda'') + c[\Omega_1 := L(\lambda'')].
```

  For example the code $`\Omega_1\cdot 2`$ gives $`\delta''_1 + L(\lambda'')\cdot 2`$, the code $`\varepsilon_{\Omega_1+1}`$ gives $`\delta''_1 + \varepsilon_{L(\lambda'')+1}`$, and the code $`\Gamma_{\Omega_1+1}`$ gives $`\delta''_1 + \Gamma_{L(\lambda'')+1}`$. This is the
  reading of the codes below $`\Phi_\Omega`$ (Theorem EXACT-V, [SHIFT2.md](SHIFT2.md) §2.1) one step up, with real reaches; the least restart whose offset reaches a given code is also known (ATTAIN″).
- **Theorem C$`^G`$ and the new frontier** (proved by transfer, given FRAG). Below $`L(\varepsilon_{\Phi_\Omega+1})`$, $`R_2^S`$ is skeletal for the skeleton of the points $`L(e)`$: every new pair is a pair
  $`(\tau''_j, \delta''_j)`$ and contains no new pair, every restart has an exact reach, and there is no fan apex and no triple nest. So $`\beta_0 \gt L(\varepsilon_{\Phi_\Omega+1})`$, the least top of a triple nest in $`R_2^C`$
  is above it, and **Wilken's claim holds in $`R_2^C`$ on $`[0, L(\varepsilon_{\Phi_\Omega+1})]`$**, both halves (the names half because the point is a normal form, Lemma L):

```math
L(\varepsilon_{\Phi_\Omega+1}) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+\varepsilon_{\psi_{\Omega_2}(\Omega_2)+1}}).
```

  Between $`L(\Omega_1^2)`$ and this point lie $`L(\varepsilon_{\Omega_1+1})`$, $`L(\psi_{\Omega_2}(0))`$, $`L(\Phi_\Omega)`$ and $`L(\omega^{\Phi_\Omega+2})`$; the first code not covered is $`\varepsilon_{\Phi_\Omega+1}`$, at the point itself.
- The referee's minor points (none changes a result). The proof that the caps are cofinal below the frontier uses the tower $`t_0 = \Omega_1+1`$, $`t_{n+1} = \omega^{t_n}`$, whose supremum gives only
  $`L(\varepsilon_{\Omega_1+1})`$; the tower must start at $`t_0 = \Phi_\Omega+1`$, and the claim stands (m1). EXACT-G″ was stated for every code below $`\varepsilon_{\Phi_\Omega+1}`$, also for indices $`\lambda'' \ge \varepsilon_{\Phi_\Omega+1}`$, where the
  domain lemmas are not available; it is restricted as above, which is all that is used (m2). The step at $`L(\Omega_1\cdot\omega)`$ is a transfer of §1.1, not a citation (m3). One step uses
  $`r(b) \ge \delta''_1`$ before it is proved; what it needs, $`b \le_1 \rho_\lambda \le_1 g`$, holds (m4). Three rows of the checks have wrong labels (m5). The normal forms must fix whether $`p`$ or $`\omega^p`$ is
  written, since $`\Phi_\Omega = \omega^{\Phi_\Omega}`$ (m6). One intermediate point is labelled with codes up to $`\Phi_\Omega+1`$, it covers codes up to $`\Phi_\Omega`$ (m7; this point was itself wrong: since $`-1 + x = x`$ for infinite $`x`$, the label was exact, [SHIFT9.md](SHIFT9.md) §1.1).
- **Not proved.** The Veblen closure above $`\Phi_\Omega`$, which would move the frontier to $`L(\Gamma_{\Phi_\Omega+1})`$: outline. EXACT-O″ (the offset is the order type of the codes below $`c`$ whose constants
  are below $`L(\lambda'')`$) and the long restarts of the skeleton (from the code $`\psi_{\Omega_2}(\Omega_\omega\cdot 2 + \psi_{\Omega_3}(\Omega_\omega\cdot 2)\cdot\omega^2)`$ on): conjectures. The landing calculus of the long
  restarts of the skeleton, the codes below $`P_3`$, and $`\nu_3`$: open. With the calculus for every code below $`P_3`$, the shift criterion one level up would give a triple nest with top
  $`\psi_{\Omega_1}(\Omega_\omega\cdot 3 + \omega^{P_3+1} + P_3)`$, the conjectured $`\nu_3`$ (an upper bound for the least triple nest; not proved).

### 2.2 $`R_2^S`$ against $`R_2^C`$: Carlson's categoricity theorem, and $`\beta_0 \gt Z^+`$

Words as in [THETA.md](THETA.md) §8.2: (E) is $`\kappa_C \le \beta_0`$ (Conjecture CORE-2), (R) is "$`\kappa_C`$ is $`\le_1`$ to everything above it in $`R_2^S`$", AGR is $`\max(\kappa_S, \kappa_C) \le \beta_0`$. $`\sigma_S`$ is the least
ordinal not in $`\mathrm{Core}(R_2^S)`$.

- **MIN$`^S`$ and LEAST** (cited, [C11] Claim 1, through Cor 0.9, which applies the theorem to $`R_2^S`$; the referee re-did the proof; it reads a cover in Claim 1 as the closed image of a covering).
  In $`R_2^S`$ an isominimal set is pointwise below every closed covering of it. So an isominimal set of $`R_2^S`$ is its least copy, and Wilken's and Carlson's cores of $`R_2^S`$ are the same.
  $`R_2^S`$ has arbitrarily long finite chains of $`\le_2`$ (CHAINS$`^S`$, proved by a club argument).
- **Theorem CAT** (cited, [C11] Cor 0.8; the referee wrote out the overlap step, m5) and **f ≤ id** (proved). $`\mathrm{Core}(R_2^S)`$ and $`\mathrm{Core}(R_2^C)`$ are isomorphic in the whole language by a map $`f`$ with
  $`f(x) \le x`$. **CAT-β₀** (proved): $`\beta_0 \ge \sigma_S`$ (the referee: the proof gives this with no condition; the paper states the weaker $`\beta_0 \ge \min(\sigma_S, \kappa_C)`$, m2).
- **CAT-E** (proved). These are equivalent: (E); $`\mathrm{Core}(R_2^S)`$ is an initial segment; the two cores are equal; AGR. So (E) implies (R). Also Theorem CC holds in $`R_2^S`$ in its supremum form
  (CC$`^S`$), and $`f`$ sends the least top of each configuration in $`R_2^S`$ to the one in $`R_2^C`$ (TOPS).
- **O$`^S`$** (proved). At each level, $`o_k = \omega`$ in $`R_2^S`$ is equivalent to the pinning statement of that level, and (E) gives $`o_k = \omega`$ at every level. The referee: this equivalence decides
  neither side; (R) and PINNING are reduced to (E), not proved (m3).
- **C-TRANSFER$`^{\mathrm{RIG}}`$** (proved). The $`R_2^C`$ side of the transfer uses only clause 2 of Carlson 2009, Def 5.3: a first difference at a left end is excluded wherever an $`R_2^S`$ side property RIG
  holds, and RIG is the gap calculus of that left end's own gap.
- **AGREE⁺** (proved by transfer, given FRAG). The block calculus BLOCK″$`_0`$ holds at $`L(\Omega_1\cdot\omega)`$ (§1.1 at the index $`\Omega_1\cdot\omega`$; it never reads the reach of $`L(\Omega_1\cdot\omega)`$). So $`\beta_0 \gt Z^+`$, the least
  top of a triple nest in $`R_2^C`$ is above $`Z^+`$, the claim holds in $`R_2^C`$ on $`[0, Z^+]`$ (the second proof, with §2.1), and **the claim holds in $`R_2^S`$ on $`[0, L(\Omega_1\cdot\omega))`$** (before, up to $`\upsilon_{\omega^3}`$).
- **GHOST-SHAPE** (proved, with the referee's correction m1). If (E) fails, the extra pair $`(\alpha, \beta_0)`$ of $`R_2^C`$ has one of two shapes. Type N: $`\alpha`$ is the last $`\le_1`$-predecessor of $`\beta_0`$, and $`\beta_0`$
  lies strictly inside the $`R_2^S`$ reach of $`\alpha`$; if $`\alpha \lt x_F^C`$ (the least fan apex of $`R_2^C`$), $`\alpha`$ has no $`\lt_2`$-successor in $`(\alpha, \beta_0)`$ in $`R_2^S`$. Type F: $`\alpha`$ is a fan apex of $`R_2^C`$, so
  $`\alpha \ge x_F^C \gt T_\omega`$. Below $`x_F^C`$ only type N is possible, and it is excluded wherever RIG holds. Where $`\beta_0`$ lies is not known (conjecture: $`\beta_0 \ge x_F^C`$).
- The referee's other minor points. Three sentences are labelled proved but are remarks or a conjecture: that clause 2 "cannot see" a $`\Pi`$-type witness, that the fan region is the first place
  where the transfer stops "for a structural reason", and that the left ends in question are nest left ends; what is proved is that in type F every $`\Sigma_2`$ witness meets $`[d, \beta_0)`$, $`d`$ the last
  $`\le_1`$-predecessor of $`\beta_0`$, and that type F needs a fan apex of $`R_2^C`$ (m4). One row of the table of next steps holds only for the least long pair (m6). Remark (m7): Carlson 2009, p. 97, says
  without proof that the $`\Sigma_n`$ definition and Def 5.4 are equivalent, and its remark after Def 5.3 asserts INC; both stay open here.
- **The plan items.** MIN$`^S`$: closed (cited, [C11]); the case P3b is excluded given FRAG, and without FRAG it forces a gap in $`\mathrm{Core}(R_2^S)`$. (R) and PINNING: reduced to (E). (E): open, now
  equivalent to "$`\mathrm{Core}(R_2^S)`$ has no gap". The converse for $`\le_1`$ at successor stages above $`\kappa_C`$: open, and not needed for the cores.

### 2.3 Native codes: digit units, and $`\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega_{\omega+1}^2 + \sigma_2)`$

Write $`\Omega' = \Omega_{\omega+1}`$, $`\psi' = \psi_{\Omega_{\omega+1}}`$, $`\sigma^{(a)} = \psi'(\Omega'\cdot a)`$, $`\sigma_2 = \psi'(\Omega'^2)`$, $`s_1 = \Omega_\omega`$, $`s_{m+1} = \psi'(\Omega'\cdot s_m)`$. Every $`e \lt \Omega'^2`$ is $`\Omega'\cdot a + \delta`$ with
$`a, \delta \lt \Omega'`$; $`a = \omega^{b_1}\cdot k_1 + \dots + \omega^{b_N}\cdot k_N`$ is the **high part**, $`\delta`$ the low part, the $`b_i`$ the positions.

- **The minor points of the review of §1.3 are applied** (**2 reviews**; the claim on certificates is corrected by m1 below).
- **The ordinal side** (proved; LIM, STAGE$`^{SS^2}`$ and PUSH by transfer; the referee checked every step against the Lean statements). Every strongly critical $`\theta \in (\Omega_\omega, \sigma_2)`$ is $`\psi'(\Omega'\cdot a + \delta)`$
  with high part, positions and low part below $`\theta`$ (HIGH); the fixed-point lemmas with their CLAIMs; the supremum lemmas at every level; the good stages below $`\Omega'^2 + \sigma_2`$ are exactly the
  intervals $`[\Omega'\cdot a, \Omega'\cdot a + \sigma^{(a+1)})`$, $`a \lt \sigma_2`$, and $`[\Omega'^2, \Omega'^2 + \sigma_2)`$; and

```math
\psi_{\Omega_1}(\Omega'^2 + \sigma_2) = \sup_m \psi_{\Omega_1}(\Omega'^2 + s_m).
```

- **Digit units and REF-SUP** (proved; the conjecture REF of §1.3 in a changed form). The reference to $`\Omega'`$ is the right end $`y`$ of the unit's own pair, with no separate marker point. The unit of
  $`\psi'(\Omega'\cdot a + \delta)`$ is

```math
r \lt x \lt A(b_N) \lt \dots \lt A(b_1) \lt A(\delta) \lt y \lt v_N \lt \dots \lt v_1 \lt c,\quad x \lt_2 y,\quad v_i \le_1 v_i + d_{b_i},\quad r, x, c \le_1 c\cdot 3 + v_1\cdot k_1 + \dots + v_N\cdot k_N + d_\delta,
```

  with one digit $`v_i`$ for each term of the high part ($`a = 0`$ is the $`\psi`$ unit of [SHIFT7.md](SHIFT7.md) §3.3). REF-SUP: a digit unit hosts every unit of smaller weight; the first difference decides (four
  cases); a new digit comes from R1 at the host digit, a new position code from SUP$`^A`$ at the host's position code, and the guest's $`y`$ goes to the host's $`y`$ together with the pair. The
  $`\Omega'`$ unit hosts every digit unit (OMEGA-SUP$`^D`$), and no $`\Omega'`$ unit has to host another one, so the regress of §1.3 does not arise. Every unit keeps one pair, and the codes have chain number at most 3.
- **The bound** (proved by transfer; it rests, as before, on a stage lemma of an earlier round that was not re-derived). Natively, with $`\mathrm{CH}_4`$:

```math
\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega_{\omega+1}^2 + \psi_{\Omega_{\omega+1}}(\Omega_{\omega+1}^2)) \gt \psi_{\Omega_1}(\Omega_{\omega+1}\cdot 2),
```

  which passes the target of REF, and RED-TOWER holds with $`\mathrm{CH}_4`$ below this point. The bound for $`\mathrm{CH}_3`$ stays $`\psi_{\Omega_1}(\varepsilon_{\Omega_\omega+1})`$. These are lower bounds only.
- **Not proved.** A variant with bare digits is checked only, with no written proof (m4; nothing depends on it). The next atom $`\sigma_2`$ has a high part whose position $`\Omega'`$ is itself $`\ge \Omega'`$
  (proved as a fact on stage sets). Conjecture TREE: digits of digits, with no new pair and chain number 4, up to $`\psi_{\Omega_1}(\varepsilon_{\Omega_{\omega+1}+1})`$. Past it come Veblen and $`\psi_{\Omega_{\omega+2}}`$ nodes inside
  high parts; $`\psi_{\Omega_1}(\Omega_{\omega+2})`$ needs the collapse nodes (a remark, m3), and these probably need a pair above $`y`$, so the chain number would grow (conjecture). $`\Omega`$ units indexed by
  their argument codes: outline only, with no ordinal side. $`\psi_{\Omega_1}(\Omega_{\omega\cdot 2})`$, $`\psi_{\Omega_1}(\Omega_{\Omega_1})`$, the tower of $`\Omega`$'s and $`\theta_0`$: open, so "the first fan needs an inaccessible" stays open.
- The referee's other minor points: the outputs of the two seeds are identical because only counts are printed (m2); one step needs only the monotonicity of $`\psi`$ (m5); new codes may lie among
  the host's unused codes, which is harmless (m6); wording (m7).

### 2.4 Status after the thirty-fourth round

Superseded by [SHIFT10.md](SHIFT10.md) §3.4.

- Wilken's claim in $`R_2^C`$: both halves hold on $`[0, X_4]`$ without FRAG, and **on $`[0, L(\varepsilon_{\Phi_\Omega+1})]`$ given FRAG, with $`L(\varepsilon_{\Phi_\Omega+1}) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+\varepsilon_{\Phi_\Omega+1}})`$** ($`[0, X_{21}]`$ with
  2 reviews; up to $`\nu_C = \nu_S = L(\omega+1)`$ with 1 review and an audit; from $`\nu_C`$ to $`L(\omega^2)`$ with 2 reviews; from $`L(\omega^2)`$ to $`L(\Omega_1\cdot\omega)`$ with 1 review; from $`L(\Omega_1\cdot\omega)`$ to $`Z^+`$
  with 2 reviews, two proofs, §2.1, §2.2; from $`Z^+`$ to $`L(\varepsilon_{\Phi_\Omega+1})`$ with 1 review, §2.1).
- Wilken's claim in $`R_2^S`$: on $`[0, L(\Omega_1\cdot\omega))`$ given FRAG (§2.2); without FRAG up to $`\upsilon_{\omega^3}`$.
- $`R_2^S`$ against $`R_2^C`$: the two agree on every relation with right end at most $`L(\varepsilon_{\Phi_\Omega+1})`$ (given FRAG); $`\beta_0 \ge \sigma_S`$; (E) is equivalent to "the two cores are equal" and implies (R);
  MIN$`^S`$ holds (cited, [C11]). $`\beta_0`$ is not located.
- Reaches (given FRAG): exact for every restart below $`L(\varepsilon_{\Phi_\Omega+1})`$.
- **LOW: false, given FRAG**; **LOW$`^\infty`$: true, given FRAG** (1 review each; no change). The steps PIN and LOW of Conjecture CORE-2: undecided (no change).
- The lower-bound program below $`\theta_0`$: native bounds $`\iota(\mathrm{CH}_3) \ge \psi_{\Omega_1}(\varepsilon_{\Omega_\omega+1})`$ and $`\iota(\mathrm{CH}_4) \ge \psi_{\Omega_1}(\Omega_{\omega+1}^2 + \sigma_2)`$ (1 review each). The step below SRO: no
  change (every $`n`$ on all 3,166 sample matrices; the general statement for all standard matrices below SRO is open).

### 2.5 Checks of the thirty-fourth round

Each run was under 60 seconds; none is a proof.

- §2.1. The domain criterion on 180 indices, initial parts on 140 cases, the order of the reading on 43,200 pairs, 18 regions, 22 targets, and the chain of names from $`L(\Omega_1\cdot\omega)`$ to
  $`L(\varepsilon_{\Phi_\Omega+1})`$ and on to $`\nu_3`$ (normal forms, indices in the domain, increasing); Lean green, identical to Python. The referee: the domain criterion on 1,110 random cases with
  constants at the boundary (290 not in the domain), 0 mismatches; 88 targets of EXACT-G″ at $`\Gamma`$ and $`\Phi`$ codes, 87 valid, the one failure from the referee's own choice of constant, which the proof
  excludes; initial parts on 120 cases; the tower of m1; the Lean rerun identical.
- §2.2. The order of the landmarks from $`L(\Omega_1\cdot\omega)`$ to $`\psi_{\Omega_1}(I_\omega)`$. The referee: 13 indices $`\Omega_1\cdot\omega + e`$ with $`e \lt L(\Omega_1\cdot\omega)`$ in the domain, the domain criterion on 16
  samples, the chain from $`L(\Omega_1\cdot\omega)`$ through $`Z^+`$ to $`\psi_{\Omega_1}(\Omega_\omega\cdot 3)`$ (normal forms, increasing), and a Lean file for it, green and identical to Python.
- §2.3. Names on two seeds, 310 checks each, 0 failures (the referee: a new seed, 310 of 310; and own tests of the good stages, HIGH and the supremum lemmas on two seeds, 0 failures); 12 codes
  with digit units have chain number 3, the mutants 4; the 11 cited Lean lemmas checked (axioms only propext, Classical.choice, Quot.sound). Certificates (replayed): the toy chain
  $`\psi`$ unit, then digit units with high parts $`\omega^0`$, $`\omega^0\cdot 2`$, $`\omega^1`$; a reference unit below the $`\Omega'`$ unit. The referee, with the search method the author's script never reached
  (m1): a digit unit below the $`\Omega'`$ unit (3 moves), two of three full codes with decorations, and new toys for the cases with a new code and a new digit; not found: two new digits in a
  row under the $`\Omega'`$ unit (no certificate support, not a disproof). Reverse certificates: 0 of 6 (author), 0 of 13 (referee).

### 2.6 Open

Superseded by [SHIFT10.md](SHIFT10.md) §3.6.

- The claim above $`L(\varepsilon_{\Phi_\Omega+1})`$ given FRAG (above $`X_4`$ without FRAG). Next: the Veblen closure above $`\Phi_\Omega`$ (frontier $`L(\Gamma_{\Phi_\Omega+1})`$), the offsets EXACT-O″, the long restarts
  of the skeleton and their landing calculus, the codes below $`P_3`$, and $`\nu_3`$. In $`R_2^S`$: the claim above $`L(\Omega_1\cdot\omega)`$; $`o_k = \omega`$ for the levels above $`\nu`$ without FRAG.
- The crossing at $`m^*`$ across two levels as its own step with its audit row (minor m5 of §1.2).
- $`R_2^S = R_2^C`$ above $`L(\varepsilon_{\Phi_\Omega+1})`$: (E), equivalently "$`\mathrm{Core}(R_2^S)`$ has no gap", and $`\beta_0`$ itself; the converse for $`\le_1`$ at successor stages above $`\kappa_C`$.
- Bounds for $`\iota(\mathrm{CH}_2)`$, $`m_F`$, $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$, and an upper bound for $`\iota(\mathrm{CH}_3)`$.
- The first inaccessible: chain number 3 past $`\varepsilon_{\Omega_\omega+1}`$; with chain number 4 past $`\psi_{\Omega_1}(\Omega_{\omega+1}^2 + \sigma_2)`$ the conjecture TREE (to $`\psi_{\Omega_1}(\varepsilon_{\Omega_{\omega+1}+1})`$), then
  collapse nodes for $`\Omega_{\omega+2}`$, $`\Omega`$ units indexed by their argument codes, $`\Omega_{\omega\cdot 2}`$, $`\Omega_{\Omega_1}`$ and the tower of $`\Omega`$'s up to $`\theta_0`$; $`\mathrm{CH}_2`$ past $`\Theta_1`$; the step for all
  standard matrices below SRO.
- Names: $`R(\Theta_{d\omega})`$; the exact offsets between $`\Lambda_{\mathrm{fp}2}`$ and $`\Theta_1`$; an InaccPsi formula for the reach in terms of the code; names above $`\nu`$ for the points that are not
  $`\upsilon`$-points; the rest of [COVER.md](COVER.md) §9.
