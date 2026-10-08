[← Back](README.md) | [English](ROUND1.md) | [Japanese](ROUND1-ja.md)

# $`R_2^+`$, the first round: finite-set tests, toward a chain of length 3, toward the lower bound

These results of the first round (2026-10) were on [README.md](README.md) §3; they were moved here unchanged, to keep that page within the budget of math that GitHub renders.
The status words are those of [README.md](README.md) §3. Lemma HULL, Conjecture C3′, Theorem S and the other results named here without a link are on [README.md](README.md) §3.

## 1. Finite-set tests in $`R_2^S`$

(2026-10.) The language $`\{0, +, \le, \le_1, \le_2\}`$ is read as a finite relational one.

- **T1** ($`\Sigma_1`$). $`\alpha \le_1 \beta`$ iff for all finite $`X \subset \alpha`$ and $`Y \subset [\alpha, \beta)`$ there is
  $`\tilde Y \subset \alpha`$ with $`X \lt \tilde Y`$ and an isomorphism $`X \cup \tilde Y \cong X \cup Y`$ that fixes $`X`$;
  $`\tilde Y`$ can be taken above any $`\rho \lt \alpha`$.
- **Lemma PR.** $`\alpha \lt_1 \beta`$ gives $`\alpha = \omega^a`$ with $`a`$ a limit; $`\alpha \lt_2 \beta`$ gives $`\beta = \omega^\lambda`$ with
  $`\lambda`$ a limit, and $`\alpha`$ the supremum of its $`\lt_1`$-predecessors.
- **T2** ($`\Sigma_2`$, graded form; an "iff", while Wilken 2021, Prop 1.6, and Wilken 2020, Prop 21.11, state only
  "if"). $`\alpha \le_2 \beta`$ iff for all such $`X, Y`$ and every $`k`$ there is a copy $`\tilde Y`$ as in T1 such that every
  extension by at most $`k`$ points below $`\alpha`$ extends the isomorphism into $`\beta`$. The copy can also be taken
  cofinal, with $`y \le_1 \beta \Leftrightarrow \tilde y \le_1 \alpha`$, and closed when $`X \cup Y`$ is closed.
- **Theorem CMP.** $`\alpha \le_i^S \beta`$ implies Carlson's covering condition for $`\le_i`$ ($`i = 1, 2`$), computed inside
  $`R_2^S`$. Carlson 2009, p. 98, announces this without proof. Lemma KEEP: the leading-term map keeps forward
  $`\le_1`$ and $`\le_2`$, because both ends of a $`\lt_2`$-pair are additive principal.

## 2. Toward an explicit chain of length 3

(2026-10, 1 review.) Results on the upper half of Conjecture C3′:
- **Set-theoretic reflection.** ELEM: if $`H`$ is an elementary submodel of some $`H(\vartheta)`$ and $`H \cap \gamma = \delta`$ is an
  ordinal, then $`R_2|\delta`$ is an elementary substructure of $`R_2|\gamma`$ (in $`R_2^S`$ and $`R_2^C`$). CLUB-1: for regular
  uncountable $`\kappa`$, the $`\delta \lt \kappa`$ with $`\delta \le_1 \infty`$ contain a club. CHAINS-S: in $`R_2^S`$ any two of them are
  $`\le_2`$, so $`R_2^S`$ has chains of every finite length among countable ordinals. HIGH: each such $`\delta`$ is above
  $`\omega_1^{CK} \gt \psi_{\Omega_1}(\Lambda)`$, so this never gives a chain inside the range of InaccPsi.
- **$`\le_2`$ at a cardinal.** LOCAL-2: the copy from HULL passes the extension clause of T2 for all extensions below
  $`\pi(\beta)`$ (it needs $`Y \subseteq H`$); it can fail only through points in $`[\pi(\beta), \kappa)`$. CHANG-2 (conditional): a
  Chang-type hull hypothesis gives $`\kappa \le_2 \lambda`$ in $`R_2^S`$, and the hypothesis forces $`\lambda \ge \kappa^+`$. SC2:
  $`V_\kappa \prec_{\Sigma_2} V_\beta`$ gives $`\kappa \le_2 \beta`$ in $`R_2^S`$. I0-NOT-SIGMA2: if $`I_0`$ is the least weakly inaccessible,
  $`V_{I_0}`$ is $`\Sigma_2`$-elementary in no $`V_\beta`$ with $`\beta \ge I_0 + 2`$. REFORM: "$`I_0 \le_2 \lambda`$" is equivalent to a
  statement about two ordinals above $`\omega_1^{CK}`$. Open: whether $`I_0 \le_2 \beta`$ for some $`\beta \gt I_0`$.
- **NO-PROMOTE.** $`\tau = \upsilon_{\omega^2}`$ is an $`\varepsilon`$-number with $`\tau \le_1 \upsilon_{\omega^2+\omega+1}`$ (the restart $`r_{\omega+1}`$
  above $`\tau`$), but $`\{\upsilon_{\omega^2+1}, \upsilon_{\omega^2+\omega}, \upsilon_{\omega^2+\omega+1}\}`$ is not a chain (Lemma TOP and Theorem
  B′′ of R2PLUS; in $`R_2^S`$ without FRAG, in $`R_2^C`$ through EQB′′). So the $`\le_1`$-reach of $`\tau`$ alone cannot prove
  C3′; a proof needs a $`\le_2`$ property of $`c_0`$.
- **Lemma K and COLLAPSE-FAIL.** The collapse of the hull $`\mathrm{Cl}(0, 0) \cap \Omega_2`$ is the substitution
  $`\Omega_1 \mapsto \Gamma_0`$ (proved). $`\Omega_1 \le_1 \varepsilon_{\Omega_1+1}\cdot 2`$ (proved). "Not $`\Gamma_0 \le_1 \varepsilon_{\Gamma_0+1}\cdot 2`$" is
  **not proved**: the review found a blocking point (the proof uses the right end itself as a point of $`Y`$, which
  the test T1 does not allow). The referee proposed a repair, not yet reviewed. If it holds, collapsing an
  InaccPsi hull does not keep $`\le_1`$, so it cannot bring a $`\le_2`$ relation from a cardinal down to a countable value.

## 3. Toward the lower bound

(2026-10, $`R_2^C`$.) Write $`\theta_0 = \psi_{\Omega_1}(\psi_{I_0}(0))`$.

- **Lemma I-FREE.** A countable normal form has no inaccessible symbol iff its value is below $`\theta_0`$. So
  the inaccessible-free terms are exactly the terms below $`\theta_0 \lt \psi_{\Omega_1}(I_0)`$.
- **Lemma OE.** If a map $`F`$ from the normal forms below $`\gamma`$ to pointed patterns makes "the point of the
  least realization of $`F(t)`$" strictly increasing in $`t`$, then $`[0, \gamma) \subseteq \mathrm{Core}(R_2^C)`$.
  **EPS-RED**: $`F`$ is needed only on the terms whose value is an $`\varepsilon`$-number. **FS-OE**: strict increase
  follows from two local steps, "predecessor below $`t`$" and "$`t[n]`$ below $`t`$".
- **RED-BMS.** With Theorem S of [R2PLUS.md](../../BMS/PoR/Trio/R2PLUS.md), the lower bound below $`\gamma`$ follows from an
  order embedding $`\mu`$ of the $`\varepsilon`$-number terms below $`\gamma`$ into the standard trio matrices below $`V`$
  (below $`V_3`$, with FRAG, now proved). **S-RED**: on the matrices of the Lean class `TrioStdL`, strict increase of the point
  of $`\Phi_3`$ reduces to the single statement "the point of $`\Phi_3(A[k])`$ is below that of $`\Phi_3(A)`$ for all
  $`A`$ and $`k`$" (from the Lean theorem `trio_fs` and the termination of BMS).
- **Lemma MU-A.** On a fragment $`G_A`$ of terms (sums; $`\psi_{\Omega_1}`$ of sums of $`\Omega_\omega`$, $`\omega^{\Omega_\omega + c}`$ and
  $`\theta\cdot\omega^e`$), the recursive map $`\mu`$ to trio matrices is strictly increasing.
- **Lemma UNIF-V.** For $`A_m = (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)^m`$, $`m \ge 3`$, and every $`N`$: the point of
  $`\Phi_3(A_m[N])`$ is below that of $`\Phi_3(A_m)`$, given the output shapes of $`\Phi_3`$ (checked for $`m \le 8`$,
  $`N \le 6`$). This extends Theorem V of R2PLUS ($`m = 2`$). For $`m = 3`$ the shapes are now given for all $`N`$ (2026-10,
  1 review), but by a lemma that is written only as a sketch, so $`m = 3`$ is not counted as proved; CORE-C3 does not
  need it.
- **Lemma MU-B** (2026-10, 1 review). A larger fragment $`G_B \supset G_A`$: any countable limit index $`\Omega_\xi`$ (also
  with $`\psi_{\Omega_1}`$-terms inside $`\xi`$), summands $`\omega^{\Omega_\xi\cdot\kappa + c}`$ with countable $`\kappa \ge 1`$ and $`c`$,
  sums of summands with different indices, $`\theta`$-tails, and countable $`\omega^x`$ for
  $`x \ge \psi_{\Omega_1}(\Omega_\omega)`$. The extended map $`\mu_B`$ equals $`\mu`$ on $`G_A`$ and the Lean map `omegaIndexMatrix` on
  $`\psi_{\Omega_1}(\Omega_\xi)`$, $`\xi \lt \varepsilon_0`$ a limit. $`\mu_B`$ is strictly increasing on $`G_B`$, and every image is below SRO.
  Standard images: proved (Lean `trioStdL_omegaIndexMatrix`) only for $`\psi_{\Omega_1}(\Omega_\xi)`$, $`\xi \lt \varepsilon_0`$ a limit;
  elsewhere checked. The review found one blocking point, against the use of MU-B for the core (not against
  MU-B itself): it adds no ordinal to the known part of the core.
  $`G_B`$ has no element in $`[\varepsilon_0, \psi_{\Omega_1}(\Omega_\omega))`$ (proved), so its order type is small (conjecture: about
  the Ackermann ordinal), and Lemma OE gives only $`[0, \mathrm{otp}(G_B))`$. The next step must cover the
  $`\varepsilon`$-numbers between $`\varepsilon_0`$ and $`\psi_{\Omega_1}(\Omega_\omega)`$.
- **Lemma MU-0** (2026-10, 1 review). The normal forms below $`\upsilon_1 = \psi_{\Omega_1}(\Omega_\omega)`$ are order-isomorphic to
  the standard pair sequences (with the empty one) in lexicographic order, by a map $`\mu_0`$ that sends sums to
  concatenations and additive principal terms to sequences with one root. Proved given one citation:
  $`\upsilon_1`$ equals Buchholz's $`\psi_0(\Omega_\omega)`$ (the Lean axiom `core_eq_psi`; its source is Buchholz 1986, not
  Wilken 2007 as first cited), and Lean theorems (`pairOrd_injective`, `range_pairOrd`, `ordOf_append'`, `lemmaR`).
  $`\mu_0`$ is "the value, then the inverse of the pair rank", not a recursion on terms.
- **Lemma MU-B0** (2026-10, 1 review). MU-B holds on $`G_{B0}`$, which is $`G_B`$ with the base widened to every additive
  principal term below $`\upsilon_1`$, with $`\mu_0`$ on the base: $`\mu_B`$ is strictly increasing and every image is below SRO.
  That the images are standard is checked only. **Gap** (proved): $`G_{B0}`$ contains $`[0, \varepsilon_{\upsilon_1+1})`$ and then
  nothing up to $`\upsilon_2 = \psi_{\Omega_1}(\Omega_\omega + \theta)`$. So family (M4) at level 0 adds no ordinal to the proved
  part of the core there (that it adds none at all is plausible, not proved). The next gap is the base one level up
  (arguments $`\Omega_\omega + \zeta`$, $`\zeta \lt \theta`$; Lemma TR1, open).
