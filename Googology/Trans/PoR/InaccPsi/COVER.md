[← Back](README.md) | [English](COVER.md) | [Japanese](COVER-ja.md)

# $`R_2^+`$ by covering minimality: chains of length 3, the least fan, NOLIM in $`R_2^C`$, and the transfer to $`R_2^S`$

This page continues [BREAK.md](BREAK.md). The status words are those of [README.md](README.md) §3: **proved** means that an
independent referee found the result proved with no fatal or blocking point. All results on this page are from 2026-10. They
come from two rounds of four papers, each paper refereed once: the fifth round (§1–§4) and the sixth round (§5). "1 review"
means one referee. "2 reviews" means that two independent papers proved the result and each paper was refereed once. A
statement that its referee found not proved is listed under **Not proved**, even when the rest of its paper is proved. The
papers of the fifth round, and three of the sixth, use Carlson's minimality against coverings (Carlson 2009, Thm 14.10(2)),
the tool of [BREAK.md](BREAK.md) §8.1. None of them uses Wilken, JSL 72 (2007), Carlson,
AML 38 (1999), Wilken, AML 45 (2006), or the equivalence of Carlson's definition with $`\Sigma_n`$-elementarity that Carlson 2009, p. 97,
announces. No result on this page is in Lean; the one Lean lemma used is Lemma CONT (`psi_one_iSup`, [README.md](README.md) §3).

**Notation.** As on [BREAK.md](BREAK.md), with the levels numbered as there ($`U_k`$, $`x_k`$, $`T_k`$, $`\upsilon^k_\zeta`$, $`o_k`$, §8).
$`\mathrm{lh}(a) = \max\{g : a \le_1 g\}`$, $`\mathrm{Pred}_1(e) = \{\alpha \lt e : \alpha \le_1 e\}`$, and $`R(a) = \{d \gt a : a \lt_2 d\}`$ is the set of right ends of $`a`$.
$`\kappa_C`$ is the ordinal $`\mathrm{Core}(R_2^C)`$ (Carlson 2009, Thm 14.14). $`C^*_3 = \{c_0 \lt c_1 \lt c_2\}`$ is the least chain of length 3 of
$`R_2^C`$ and $`m_3`$ its least $`\le_1`$-predecessor ([README.md](README.md) §3). $`x_F`$ is the least fan apex, $`y_1 \lt y_2`$ its two right ends,
$`(f_0, f_1, f_2)`$ the least closed fan, and $`\sigma_F`$, $`\sigma_N`$, $`T_\omega`$, $`x_L`$, $`y_L`$, FF, $`FF_N`$, POINT-SRO, PT, L1p are as in [BREAK.md](BREAK.md) §6
and §7.4. "AP" means additively principal. $`\theta_0 = \psi_{\Omega_1}(\psi_{I_0}(0))`$; by Lemma I-FREE, a countable term needs an inaccessible
exactly when its value is $`\ge \theta_0`$.

## 1. Chains of length 3

An **infinite closed fan** at $`a`$ is a sequence $`d_0 \lt d_1 \lt d_2 \lt \cdots`$ in $`R(a)`$ with $`d_n \le_1 d_{n+1}`$ for every $`n`$. A **closed $`n`$-fan** is the
pattern $`a \lt d_0 \lt \cdots \lt d_{n-1}`$ (all AP) with $`a \lt_2 d_i`$, $`d_i \lt_1 d_j`$ for $`i \lt j`$, and no $`\lt_2`$ among the $`d_i`$. $`\varphi_n`$ is the apex of its
least realization and $`t_n`$ the top. All results of this section are in $`R_2^C`$ unless $`R_2^S`$ is named.

- **Lemma CORE-REACH** (proved, 1 review). If $`a \lt \kappa_C`$, then $`\mathrm{lh}(a)`$ exists and $`\mathrm{lh}(a) \lt \kappa_C`$. So every right end of a point
  of the core, and every limit of such right ends, is in the core; the core hypothesis of Theorem CP ([BREAK.md](BREAK.md) §8.1) holds
  for them by itself.
- **Theorem LEFT-CHAR** (proved, 1 review). For $`0 \lt e \lt \kappa_C`$: $`e`$ is a $`\lt_2`$-left end iff $`e`$ is a limit and $`\mathrm{Pred}_1(e)`$ is
  unbounded in $`e`$. (The referee: the paper says "cofinal"; read loosely, as "some element at or above each point", the
  statement fails at $`c_0 + 1`$. The proof uses the strict reading.)
- **Theorem CP3** (proved, 1 review). For $`a \lt \kappa_C`$ the following are equivalent: (i) $`a`$ is the bottom of a chain of length 3;
  (ii) $`a`$ has an infinite closed fan; (iii) some limit point $`e`$ of $`R(a)`$ has $`\mathrm{Pred}_1(e)`$ unbounded in $`e`$; (iv) some $`e \in R(a)`$
  has this. Given (ii), $`e = \sup_n d_n`$ is a right end of $`a`$ and a left end, and $`\{a, e, f\}`$ is a chain for every $`f`$ with $`e \lt_2 f`$.
  So the condition of Theorem CF ([BREAK.md](BREAK.md) §3) that "the limit of the right ends is a left end", which no finite
  configuration decides, becomes a $`\le_1`$-condition on the right ends of the one point $`a`$: the tree $`(R(a), \lt_1)`$ has an infinite
  ascending branch. CP3 tells which points are bottoms of chains; it does not build or bound one.
- **Corollary LEAST3** (proved, 1 review). (a) $`c_0`$ is the least point with an infinite closed fan. (b) $`c_1`$ is the least limit point $`e`$
  of $`R(c_0)`$ with $`\mathrm{Pred}_1(e)`$ unbounded in $`e`$. (c) $`D^* = \{d : c_0 \lt_2 d,\ d \le_1 c_1,\ d \lt c_1\}`$ has order type exactly $`\omega`$, and
  $`\sup D^* = c_1`$. (d) Let $`Q_0 = C^*_3`$, and let $`Q_{n+1}`$ be $`Q_n`$ with $`c_1`$ 2-reflected downward from $`c_2`$ (Carlson 2009, Def 9.4), with new
  point $`u_{n+1}`$. In the least realization of $`Q_n`$ the point $`u_i`$ is the $`i`$-th element of $`D^*`$, so $`c_1`$ is the supremum of the points made
  by $`n`$ downward 2-reflections. (The same shape as Corollary LEAST of [BREAK.md](BREAK.md) §8.1, with $`(c_1, c_2)`$ in place of $`(x_k, T_k)`$.)
- **NO-BRANCH and PIN-L** (proved, 1 review). For $`a \lt c_0`$ the tree $`(R(a), \lt_1)`$ has no infinite ascending branch. Every isominimal
  set that contains a $`\lt_2`$-left end $`e`$ contains some $`v`$ with $`e \lt_2 v`$; so one that contains $`c_1`$ contains a point $`\ge c_2`$. (This
  extends "an isominimal set that contains $`x_k`$ contains $`T_k`$", [BREAK.md](BREAK.md) §8.1.)
- **Theorem FIN-FAN** (proved, 1 review). $`\varphi_2 = f_0`$, and with $`\varphi_{\lt\omega} = \sup_n \varphi_n`$:

```math
T_\omega \le \sigma_F \lt f_0 = \varphi_2 \lt t_2 \lt \varphi_3 \lt t_3 \lt \cdots, \qquad \varphi_{\lt\omega} \le m_3 \lt c_0 .
```

  $`\varphi_{\lt\omega}`$ is a limit of caps, so it has no $`\lt_1`$-predecessor and lies in no pair (LIM-CAP, [BREAK.md](BREAK.md) §6). So repeating the
  least closed fan never reaches the chain: the chain needs one apex with an infinite closed fan, and that apex is $`c_0`$.
- **Location** (proved, 1 review). Lower bounds only:

```math
c_0 \gt m_3 \ge \varphi_{\lt\omega} \gt f_0 \gt x_F \gt x_L \gt T_\omega, \qquad m_3 \gt \nu_C, \qquad m_3 \ge \Lambda_\varepsilon .
```

  The names of Theorems GEN and GEN-EXT are all below $`\psi_{\Omega_1}(\Omega_\omega\cdot\omega)`$ and cofinal in it (by Lemma CONT). Given H-LIFT
  ($`T_\omega = \psi_{\Omega_1}(\Omega_\omega\cdot\omega)`$, [BREAK.md](BREAK.md) §6), $`c_0`$ lies beyond every GEN and GEN-EXT name. With the conjectured names of
  [BREAK.md](BREAK.md) §7.4, $`c_0 \gt y_L = \psi_{\Omega_1}(\Omega_\omega\cdot\omega + \omega^{P_\omega+1} + P_\omega)`$ (conjecture). No upper bound and no name of $`c_0`$, $`c_1`$, $`c_2`$ is known.
- **The inaccessible** (proved, 1 review). Let $`FF_{cl}`$ be the hypothesis $`\varphi_{\lt\omega} \ge \theta_0`$. FF implies $`FF_{cl}`$ (since $`\sigma_F \lt \varphi_2`$), and so
  does $`FF_N`$. Given $`FF_{cl}`$, $`m_3`$, $`c_0`$, $`c_1`$, $`c_2`$ are $`\ge \theta_0`$, so every InaccPsi name of them contains an inaccessible. $`FF_{cl}`$ asks
  only that one explicit family of patterns without a chain, the least closed $`n`$-fans, climbs to $`\theta_0`$. Also: if the point of
  $`\Phi_3`$((0,0,0)(1,1,1)(2,2,1)) is $`\ge \theta_0`$, then $`x_F`$, $`f_0`$, the $`\varphi_n`$, $`m_3`$ and $`C^*_3`$ need an inaccessible. Its referee accepted this
  only given the identity "that point is $`m_F`$" (§2); this identity is now proved in §2 (1 review). Unconditionally: open.
- **$`R_2^S`$** (proved, 1 review). (i) ⇒ (ii) of CP3 and "⇒" of LEFT-CHAR hold in $`R_2^S`$. **Theorem TR3**: let $`(s_0, s_1, s_2)`$ be the
  lexicographically least chain of length 3 of $`R_2^S`$. If $`s_1 \le \beta_0`$, then $`c_0 \le s_0`$ and $`c_1 \le s_1`$. (Corollary FIRST needed $`s_2 \le \beta_0`$
  for this.) The other halves in $`R_2^S`$ are open, for the two reasons of §4.

## 2. The least fan

$`V_F = \mathrm{Pred}_1(x_F)`$, $`m_F = \min V_F`$, and $`o_F`$ is the order type of $`V_F`$; $`v_\zeta`$ is the $`\zeta`$-th member of $`V_F`$. A **limit member** is a
$`v_\zeta`$ with $`\zeta`$ a limit, and $`s^+`$ is the next member of $`V_F \cup \{x_F\}`$ above $`s`$. PT is the open fan $`x \lt_2 y_1`$, $`x \lt_2 y_2`$, $`y_1 \not\le_1 y_2`$,
whose least realization is the least fan ([BREAK.md](BREAK.md) §7.4); PTm is PT with a point $`m \le_1 x, y_1, y_2`$ added. All results are in $`R_2^C`$.

- **Lemmas ENDS and RE** (proved, 1 review). If $`s \lt x_F`$ and $`s \lt_2 t`$, then $`t \lt x_F`$, $`t \notin V_F`$, and no member of $`V_F`$ lies in $`(s, t)`$.
  If $`s \lt_2 t`$ and $`s`$ has no right end in $`(r, t)`$ for some $`r \in [s, t)`$, then $`\mathrm{lh}(t) = t`$. In particular $`\mathrm{lh}(y_1) = y_1`$ and $`\mathrm{lh}(y_2) = y_2`$.
- **Theorem FS** (proved, 1 review).
  (a) $`V_F`$ is closed and cofinal in $`x_F`$, so $`x_F = \sup V_F`$; every member is AP and has reach $`y_2`$.
  (b) $`\mathrm{Pred}_1(y_1) = \mathrm{Pred}_1(y_2) = V_F \cup \{x_F\}`$.
  (c) The left ends in $`V_F`$ are exactly the limit members. A limit member $`s`$ has exactly one right end $`t_s`$; it satisfies
  $`s \lt t_s \lt s^+`$, $`t_s \notin V_F`$, $`\mathrm{lh}(t_s) = t_s`$ and $`\mathrm{Pred}_1(t_s) = \mathrm{Pred}_1(s) \cup \{s\}`$.
  (d) $`m_F`$ and the successor members are not left ends; $`\mathrm{Pred}_1(m_F) = \emptyset`$.
  (e) The left ends in $`V_F`$ are cofinal in $`x_F`$ (from $`x_F \le_2 y_2`$ and Carlson 2009, Def 5.3, clause 1(d)). So $`o_F = \omega\cdot\lambda`$ with
  $`\lambda`$ a limit; in particular $`o_F \ge \omega^2`$.
  (f) $`m_F \ge \sigma_N`$, and $`m_F`$ is the point of the least realization of PTm, which is the point of $`\Phi_3`$((0,0,0)(1,1,1)(2,2,1)). The
  referee proved this identity directly and re-rendered the diagram of that matrix; so the identity that the referee of
  [BREAK.md](BREAK.md) §7.4 added without a separate review is now reviewed.
  (g) LEAST-F: let $`Q_n`$ be PT with $`n`$ pairs $`u_1 \lt_2 v_1 \lt \cdots \lt u_n \lt_2 v_n \lt x`$ added ($`u_i \le_1`$ every later point). In the least
  realization of $`Q_n`$, $`u_i`$ is $`v_{\omega\cdot i}`$; $`Q_{n+1}`$ comes from $`Q_n`$ by 2-reflecting $`\{x, y_1\}`$ downward from $`y_2`$ to $`x`$. So these points
  have supremum $`v_{\omega^2} \le x_F`$, with equality iff $`o_F = \omega^2`$.
- **Lemma BLOCK, PIN-F, PAIR-CP** (proved, 1 review). BLOCK moves a left end down together with its right end, by a covering; it
  extends Lemma MOVE ([BREAK.md](BREAK.md) §8.1). PIN-F: every isominimal set that contains $`x_F`$ contains both $`y_1`$ and $`y_2`$, or one $`y_i`$ together
  with an indecomposable in $`(x_F, y_i)`$. PAIR-CP: if $`s \lt x_F`$ is a limit of limit members, every isominimal set that contains $`s`$ contains
  $`t_s`$ and an indecomposable in $`(s, t_s)`$.
- **Conjecture** $`o_F = \omega^2`$, that is $`x_F = v_{\omega^2}`$. The paper reduces it to an "interior copy" statement about the gaps. The
  implication is proved, but the referee shows that the statement fails at every limit member below $`x_F`$, so the reduction only
  restates the conjecture. **Now proved** by another route (Theorem OF, §5.2, 1 review).
- **The inaccessible.** Let $`H_m`$ be the hypothesis $`m_F \ge \theta_0`$, that is, the point of $`\Phi_3`$((0,0,0)(1,1,1)(2,2,1)) is $`\ge \theta_0`$.
  Proved (1 review): $`FF_N \Rightarrow H_m \Rightarrow x_F \gt \theta_0`$; POINT-SRO $`\Rightarrow H_m`$, from the replayed certificate
  $`\Phi_3(\mathrm{SRO}) \lt \Phi_3`$((0,0,0)(1,1,1)(2,2,1)); and if the point of $`\Phi_3(\mathrm{SRO})`$ is $`\theta_0`$ (the conjecture of [README.md](README.md) §3),
  then $`m_F \gt \theta_0`$ (from replayed certificates). So whether the first fan needs an inaccessible is one statement about one
  matrix. Open; conjecture: yes. Now $`H_m`$ has an exact equivalent, with no matrix in it (§5.3).
- **Not proved** (blocking point, side claim only). That $`m_F \gt \theta_0`$ refutes a candidate name of the least fan built over the base
  $`\psi_{I_0}(0)`$. The candidate names only $`x_F`$, $`y_1`$, $`y_2`$; the argument adds a clause about its root that the candidate does not
  contain.

## 3. NOLIM in $`R_2^C`$

Notation of [BREAK.md](BREAK.md) §7.3 and §8.4: $`U_2`$, its gaps $`(g, g^+)`$, $`K`$-chains (of long restarts), LIM points, $`b^*(g)`$; $`\nu = \nu_C`$.

- **Lemma PIN-LH** (proved, 1 review; $`R_2^C`$). If $`Z`$ is isominimal, $`b \in Z`$ and $`\mathrm{lh}(b)`$ exists, then $`\mathrm{lh}(b) \in Z`$.
- **Lemma FRAG2→** (proved, 1 review). A FRAG map that satisfies the conditions of FRAG2 ([RESTARTS.md](RESTARTS.md) §2) in the forward direction
  only, on a finite set where the structure is skeletal, is a covering onto its image.
- **Lemma BLOCK-MOVE** (proved, 1 review; $`R_2^C`$). It used SKEL⁺, which the referee accepted only at outline level; SKEL⁺ now has a
  complete proof (§5.1). Let $`Z`$ be finite and closed, $`b \in Z`$ an AP restart with
  $`h = \mathrm{lh}(b) \lt \nu`$, and $`b`$ a LIM point. Then $`Z`$ has a covering $`f^+ \le \mathrm{id}`$ onto a closed set with $`f^+(b) \lt b`$. It is the identity on
  $`Z \cap b`$ and above $`h`$; on $`Z \cap [b, h]`$ it is a FRAG map that sends the restart regions met by $`Z`$ to the regions of a $`K`$-chain
  $`c_1 \lt_1 \cdots \lt_1 c_K`$ below $`b`$, offset for offset. The reach of a moved restart is never used: every image lies below
  $`\mathrm{lh}(c_K) \le \mathrm{lh}(c_i)`$.
- **Theorem NOLIM$`^C`$** (proved, 1 review; through SKEL⁺, §5.1). In $`R_2^C`$ no point of $`(0, \nu) \setminus U_2`$ is a LIM point. So
  $`b^*(g) = g^+`$ in every gap (ITER), and the LIM points in $`(0, \nu]`$ are exactly the members of $`U_2`$. Proof: such a $`b`$ is in the core,
  so in an isominimal set; it is a restart with $`\mathrm{lh}(b) \lt \nu`$; BLOCK-MOVE moves it down by a covering, against Carlson 2009,
  Thm 14.10(2). The referee gave a shorter proof: the same map checks Carlson 2009, Def 5.3, clause 1 for $`b \le_1 \beta`$ for every
  $`\beta \lt \nu`$, so $`b \le_1 \nu`$ and $`b \in U_2`$, with no core bound and no Thm 14.10.
- **Corollary LL$`^C`$** (proved, 1 review; through SKEL⁺, §5.1). In $`R_2^C`$ the supremum of an infinite $`\lt_1`$-chain of restarts below $`\nu`$ is in $`U_2`$
  (the statement LL of [BREAK.md](BREAK.md) §7.3).
- **$`R_2^S`$** (proved, 1 review; through SKEL⁺, §5.1). (a) With no ghost (case (A) of NU-CT), NOLIM holds in $`R_2^S`$ on $`(0, \nu_S)`$. (b) With a
  ghost, every LIM point of $`R_2^S`$ in $`(0, \beta_0)`$ is in $`U_2`$ of $`R_2^C`$; so in cases (P3a) and (P3b) of LOCATE, NOLIM holds in $`R_2^S`$ on
  $`(0, \beta_0)`$. (c) **GHOST-EQ**: $`\nu_C = \nu_S`$ iff NOLIM holds in $`R_2^S`$ and $`o_2 = \omega`$ in $`R_2^S`$. (d) If NOLIM holds in $`R_2^S`$, the only possible
  ghost is case (P3b) (proved, 2 reviews with [BREAK.md](BREAK.md) §8.1).
- **Why the proof does not run in $`R_2^S`$** (the referee's reading). $`\le_1`$ of $`R_2^S`$ needs isomorphic copies, and the map of BLOCK-MOVE
  does not keep the negative facts "this restart is not $`\le_1 z`$". With the referee's shorter proof, this is the only obstacle.

## 4. Covering minimality in $`R_2^S`$

Here $`k \ge 2`$ is a level of $`R_2^S`$, with $`U_k`$, $`x_k`$, $`T_k`$ as in [BREAK.md](BREAK.md) §8, and $`s = \upsilon^k_\omega`$ when $`o_k \gt \omega`$. An **S-covering**
is Carlson's covering (Carlson 2009, Def 5.2) read in $`R_2^S`$; a set is **S-isominimal** if it is isominimal (Def 2.6) in $`R_2^S`$, and
$`\mathrm{Core}_C(R_2^S)`$ is the union of the S-isominimal sets. **MIN$`^S`$** says: every S-isominimal set is pointwise below every closed
S-covering of it (the $`R_2^S`$ form of Thm 14.10(2)).

- **LEX-ISO and ISO-UNION$`^S`$** (proved, 1 review). Every finite closed set has an S-isominimal copy pointwise below it (the
  lexicographically least one). A finite union of S-isominimal sets is S-isominimal.
- **PIN$`^S`$** (proved, 1 review). $`x_k`$, $`T_k`$ and every $`\upsilon^k_n`$ with $`n \lt \omega`$ are in $`\mathrm{Core}_C(R_2^S)`$, with an explicit pinning set.
  No set of this kind pins $`s`$.
- **MOVE$`^S`$** (proved, 1 review). Lemma MOVE holds in $`R_2^S`$ word for word.
- **LOCAL** (proved, 1 review). For sets below $`\beta_0`$ the $`R_2^S`$ form of Thm 14.10(2) holds. So Theorem CP holds in $`R_2^S`$ below $`\beta_0`$,
  and if $`o_k \gt \omega`$, no S-isominimal subset of $`[0, \beta_0)`$ contains $`s`$.
- **DEFECT and NEC** (proved, 1 review; also checked in a model). Let $`o_k \gt \omega`$ and let $`Z`$ be finite and closed with $`s, T_k \in Z`$. For
  every large enough $`\alpha \in U_k \cap s`$, the map $`f^+`$ of MOVE with $`s \mapsto \alpha`$ is an S-isomorphism iff $`B(Z, s)`$ is empty. Here $`B(Z, s)`$ is
  the set of pairs $`(a, b)`$ in $`Z`$ with $`a`$ AP, $`a \gt s`$, $`b = c + s\cdot m + d`$ in normal form (components of $`c`$ above $`s`$, $`m \ge 1`$,
  components of $`d`$ below $`s`$), $`(m, d) \ne (1, 0)`$, and $`c + s \le \mathrm{lh}(a) \lt b`$. NEC: an S-isomorphic copy $`g \le \mathrm{id}`$ with $`g(s) \lt s`$ moves
  every such $`a`$ down. So $`f^+`$ cannot be repaired locally.
- **CP$`^S`$-CLEAN** (proved, 1 review). If $`o_k \gt \omega`$, every S-isominimal set that contains $`s`$ has a point $`\ge \beta_0`$, and together with
  the pinning set it has a pair in $`B`$.
- **Reductions** (proved, 1 review). MIN$`^S`$ implies Theorem CP in $`R_2^S`$. MIN$`^S`$ together with PINNING ($`s \in \mathrm{Core}_C(R_2^S)`$ when
  $`o_k \gt \omega`$) implies $`o_k = \omega`$. $`R_2^S = R_2^C`$ on $`[0, \max Z]`$ implies MIN$`^S`$ at $`Z`$. The referee notes that, given PINNING, MIN$`^S`$
  at the sets that contain $`s`$ is the same as $`o_k = \omega`$; only the global MIN$`^S`$ is a separate target.
- **Level 2, the ghost of case (P3b)** (proved, 1 review). If $`o_2 \gt \omega`$, then $`\beta_0 \le \nu_S`$. In case (P3b), $`\beta_0 = s^+ = \upsilon^2_{\omega+1}`$, the only
  extra relation is $`s \lt_2 s^+`$ in $`R_2^C`$, $`\max \mathrm{Pred}_1(s^+) = s`$ (so LIM2 of [README.md](README.md) §3 does not apply), and every S-isominimal
  set that contains $`s`$ has a point $`\ge s^+`$. So the ghost question is the converse $`C \Rightarrow S`$ at the one pair $`(s, s^+)`$.
- **Conjecture** MIN$`^S`$. It holds wherever the two structures agree; Carlson's proof of Thm 14.10(2) uses his Lemma 14.9, which has no
  known $`R_2^S`$ form.
- **Open**: PINNING (equivalently: is $`\mathrm{Core}_C(R_2^S)`$ an initial segment up to $`\nu_S`$?), and $`o_k = \omega`$ in $`R_2^S`$ for $`k \ge 2`$.

## 5. The sixth round

Four papers, each refereed once. The papers number the levels one lower than these pages; here they are renumbered, so the
first block of nested pairs above $`\nu`$ is level 2, as in §4.

### 5.1 The level-0 description of $`R_2^S`$ at every countable ordinal (SKEL⁺ in full)

Words of [BREAK.md](BREAK.md) §2 and §7.1. A **restart** is $`\upsilon_\lambda`$ with $`\lambda`$ a nonzero multiple of $`\omega^2`$. A **block** is the interval from one
$`\delta`$-point $`\upsilon_{\lambda+\omega j+1}`$ to the next, or from a restart to its first $`\delta`$-point; its **top** is its right end point. A standard
pair has the form $`(\upsilon_{\lambda+\omega j}, \upsilon_{\lambda+\omega j+1})`$ ([BREAK.md](BREAK.md), Notation).

- **Theorem SKEL$`^\infty`$** (proved, 1 review; $`R_2^S`$; no FRAG). For every countable ordinal $`b`$:
  (D0) if $`a \lt_2 b`$ and $`a`$ is not a restart, then $`(a, b)`$ is a standard pair; if $`a`$ is a restart, then $`b`$ is a restart and some
  standard pair lies strictly inside $`(a, b)`$;
  (D1) if $`a \lt b`$ is not a restart, then $`a \le_1 b`$ iff $`b`$ is at most the top of the block of $`a`$ and $`a \le_1 b`$ in $`R_1^+`$;
  (D2) a restart that is not a right end is $`\le_1`$ the top of its first block;
  (D3) every standard pair is a $`\lt_2`$-pair.
  The proof is one induction on $`b`$. It never computes a reach of a restart: a restart $`z`$ enters only through the facts
  $`z \le_1 y`$, which are true for $`y \le \mathrm{lh}(z)`$ and false above. It does not use the stopping point $`\nu_{new}`$. The referee found one
  minor gap (in the comparison lemma the reach of the bottom of the block must be added to the parameters) and gave the fix.
- **Consequences** (proved, 1 review; $`R_2^S`$, every countable ordinal). The $`\lt_1`$-predecessors of $`\alpha`$ are the restarts $`z \lt \alpha`$ with
  $`\mathrm{lh}(z) \ge \alpha`$ and the points $`g`$ of the block of $`\alpha`$ with $`g \lt_1 \alpha`$ in $`R_1^+`$. INC1-S, LEFT, and **RIGHT**: every pair is a
  standard pair or joins two restarts, so every right end is a $`\upsilon`$-point. So Conjecture RIGHT-ISO of [BREAK.md](BREAK.md) §1 is proved in $`R_2^S`$.
- **SKEL⁺** (proved, 1 review). The statement of [BREAK.md](BREAK.md) §2 on $`[0, \nu_{new})`$, with one correction of wording: "the reach of a restart
  is closed in $`R_1^+`$" needs that reach to be below the top of its block. Also $`\nu_{new} \lt \omega_1`$, $`\nu_{new}`$ is a restart whose left end
  is a restart, and $`\nu_{nest} = \nu_{new}`$. The paper of [BREAK.md](BREAK.md) §2 was accepted only at outline level; this is the first proof
  refereed at proof level.
- **SKEL$`^\omega`$** (proved, 1 review). The statement of [BREAK.md](BREAK.md) §7.1, with the same correction in its clause on reaches. Below
  $`\Theta_P`$ the correction changes nothing: there the reach of a restart is below twice its first $`\delta`$-point.
- **$`R_2^C`$** (proved, 1 review). D0–D3 hold in $`R_2^C`$ below $`\beta_0`$, so RIGHT holds there for right ends below $`\beta_0`$. SKEL⁺ holds in $`R_2^C`$
  on $`[0, \nu_C)`$ with no hypothesis ([BREAK.md](BREAK.md) §2 had HC and INC1-nonups), and SKEL$`^\omega`$ below the smaller of $`\beta_0`$ and $`T_\omega`$.
- **Results that used SKEL⁺ or SKEL$`^\omega`$** are now proved (1 review each; each review had found that this was their only input at
  outline level): Theorem HR (a), (c) ([BREAK.md](BREAK.md) §8.2); Theorem RED and its corollary ([BREAK.md](BREAK.md) §8.3); Lemma CH ([BREAK.md](BREAK.md) §8.4);
  BLOCK-MOVE, NOLIM$`^C`$, LL$`^C`$ and the $`R_2^S`$ items of §3, among them GHOST-EQ; TAIL, TAIL-GAP, TOP and the clauses of the level-2
  structure theorem on level 1 and on reaches ([BREAK.md](BREAK.md) §7.1; equality in TAIL and the lower bound in TOP use FRAG, which is
  proved); and "$`T_\omega`$ is a restart, a limit of $`\mathrm{Top}_k`$ for every $`k`$, and its block 0 is standard" ([BREAK.md](BREAK.md) §7.1). The referee of this
  round checked the reviews of the first four; the items of [BREAK.md](BREAK.md) §7.1 rest on the earlier review alone. Not changed: "given
  FRAG, $`T_\omega \le_1 \rho_{T_\omega+\omega^2}`$" is still not proved, although its missing input (the whole region of $`T_\omega`$ is standard) is now
  proved; no value of a reach; $`\nu_C = \nu_S`$.

### 5.2 The least fan has order type $`\omega^2`$ ($`R_2^C`$)

Notation of §2.

- **Lemma BT** (block transfer; proved, 1 review). Let $`Z`$ be finite and closed, $`s \in Z`$ AP with $`s \lt_2 t`$, and let $`\alpha \lt_2 t'`$ with
  $`\max(Z \cap s) \lt \alpha`$ and $`t' \lt s`$. Suppose (T1) $`\alpha \le_1 v`$ for every $`v \in Z`$ with $`s \le_1 v`$;
  (T3) $`t`$ is the only right end of $`s`$ in $`Z`$, and $`t`$ is $`\le_1`$ no larger point of $`Z`$; (T4) the points $`a \lt \alpha`$ with $`a \le_1 b`$ for some
  $`b \ge t`$ are unbounded in $`\alpha`$. Then $`Z`$ has a covering $`f^+ \le \mathrm{id}`$ onto a closed set with $`f^+(s) = \alpha`$; so $`Z`$ is not isominimal.
  The new step: the points of $`Z`$ inside $`(s, t)`$ are not copied down together with $`s`$ (the attempt of §2 that failed). They are
  first 1-reflected below a point $`a`$ of (T4), and then carried up into $`(\alpha, t')`$ by clause 2 of Carlson 2009, Def 5.3 for $`\alpha \le_2 t'`$. The
  paper has one more condition T2; the referee shows that it follows from T1.
- **Theorem OF** (proved, 1 review). $`o_F = \omega^2`$, so $`x_F = v_{\omega^2} = \sup_n v_{\omega\cdot n}`$. If $`o_F \gt \omega^2`$, BT applies to $`s = v_{\omega^2}`$ with $`\alpha`$ a limit
  member and $`t' = t_\alpha`$. This proves the conjecture of §2.
- **PIN-F⁺** (proved, 1 review). Every isominimal set that contains $`x_F`$ contains both $`y_1`$ and $`y_2`$ (the second case of PIN-F does not
  occur).
- **GEN-F** (proved, 1 review). Let $`Q_{n,k}`$ be PT with $`n`$ pairs $`u_1 \lt_2 v_1 \lt \cdots \lt u_n \lt_2 v_n`$ and then $`k`$ points $`w_1 \lt \cdots \lt w_k`$ below $`x`$,
  each $`u_i`$ and $`w_j`$ $`\le_1`$ every later point. In the least realization, $`u_i = v_{\omega\cdot i}`$, $`w_j = v_{\omega\cdot n+j}`$ for $`n \ge 1`$, and $`w_j = v_{j-1}`$
  for $`n = 0`$; so $`m_F = v_0`$. Each $`Q_{n,k}`$ comes from PT by downward 2-reflections (Carlson 2009, Def 9.4) of $`\{x, y_1\}`$ (a new pair)
  and of $`\{x\}`$ (a new member). So every $`\le_1`$-predecessor of $`x_F`$ is the point of an explicit pattern.
- **Shape** (proved, 1 review). $`V_F`$ is closed with order type $`\omega^2`$. Its left ends are the $`v_{\omega\cdot n}`$ ($`n \ge 1`$); each has exactly one right
  end $`t_n`$, with $`v_{\omega\cdot n} \lt t_n \lt v_{\omega\cdot n+1}`$ and $`\mathrm{lh}(t_n) = t_n`$. With §2 this fixes the least fan except its names. In pure $`R_2`$
  the least point with two $`\lt_2`$-successors has the same index $`\omega^2`$ (Wilken 2021, p. 20); the referee notes that this supports only
  the index.
- **Names** (conjecture; normal forms and order checked for four bases). With an unknown base $`B_F`$ and $`P_F = \psi_{\Omega_2}(B_F)`$:
  $`v_{\omega\cdot n} = \psi_{\Omega_1}(B_F + \omega^{P_F+1}\cdot n)`$, $`t_n = \psi_{\Omega_1}(B_F + \omega^{P_F+1}\cdot n + P_F)`$, $`x_F = \psi_{\Omega_1}(B_F + \omega^{P_F+2})`$,
  $`y_i = \psi_{\Omega_1}(B_F + \omega^{P_F+2} + P_F\cdot i)`$. Lemma CONT makes the name of $`x_F`$ the supremum of those of the $`v_{\omega\cdot n}`$, as OF needs.
- **Upper bounds** (proved, 1 review). $`c_2 \lt \kappa_C \le \omega_1^{CK}`$ (Carlson 2009, Thm 15.2). As implications: Wilken's claim gives
  $`c_2 \lt \psi_{\Omega_1}(I_\omega)`$, and the names above with $`B_F \lt I_0`$ give $`y_2 \lt \psi_{\Omega_1}(I_0)`$. No InaccPsi term is proved to bound $`x_F`$, $`f_0`$, $`m_3`$
  or $`c_0`$: covering minimality bounds a least realization only by other points of $`R_2^C`$, never by a term. Open, conjecture yes:
  $`c_0 \lt \psi_{\Omega_1}(I_1)`$.

### 5.3 Whether the first fan needs an inaccessible ($`R_2^C`$)

A pattern is **RF** ("right ends without reach") if no right end $`z`$ of a $`\lt_2`$-pair of it is $`\le_1`$ a larger element of it. $`\mathrm{Core}_F`$ is the
union of the isominimal sets below $`x_F`$. $`FF_{RF}`$ says: every $`\gamma \lt \theta_0`$ lies below the least realization of some RF fan-free
pattern. $`H_m`$ is $`m_F \ge \theta_0`$ (§2).

- **Theorem DOM_RF** (proved, 1 review). Let $`(x; y_1, y_2)`$ be any fan, open or closed, and $`m \le x`$ with $`m \le_1 y_2`$. Every RF fan-free
  pattern has its least realization below $`m`$; in particular below $`m_F`$. (DOM_F of [BREAK.md](BREAK.md) §6 needs a closed fan; in an RF pattern the
  point sent to $`y_1`$ never needs a reach.)
- **Theorem SHARP_F** (proved, 1 review). $`\mathrm{Core}_F = [0, m_F)`$. So $`m_F`$ is the supremum of the points of the RF fan-free patterns, and of the
  caps below $`x_F`$.
- **Corollary** (proved, 1 review). $`H_m \Leftrightarrow FF_{RF} \Leftrightarrow [0, \theta_0) \subseteq \mathrm{Core}_F`$, and $`m_F \gt \theta_0 \Leftrightarrow \theta_0 \in \mathrm{Core}_F`$. Also
  $`FF_N \Rightarrow FF_{RF}`$. So $`H_m`$ is a lower-bound statement about RF fan-free patterns only; no comparison with a matrix is needed.
- **Proposition RR** (proved, 1 review). RR $`= \{x \lt_2 y,\ x \le_1 c,\ y \le_1 c\}`$ is fan-free but not RF, and its point is above $`x_F`$. So
  $`x_F \lt \sigma_F \lt f_0`$ (this settles the open question of [BREAK.md](BREAK.md) §6), and "fan-free caps stay below $`m_F`$" is false; it holds for RF
  patterns only.
- **Lower bound** (proved from one program reading, 1 review). $`\Phi_3(V_3)`$ is RF and fan-free, so $`m_F \gt \upsilon_{\omega^3} = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+3})`$. The
  referee adds (not reviewed separately): PS is RF and fan-free, so $`m_F \gt \nu_C`$.
- **Reduction RED-HM** (proved, 1 review, in the referee's shorter form). The map $`\mu`$ of the lower-bound program below SRO
  ([README.md](README.md) §3: the families (M1)–(M3) and the bases at level $`\ge 1`$) together with the fundamental-sequence step below SRO
  gives $`m_F \gt \theta_0`$, so the first fan needs an inaccessible. The paper also assumed RF_SRO (every $`\Phi_3(M)`$ with $`M \le`$ SRO is RF and
  fan-free; checked, §7). The referee shows that RF_SRO is not needed: the step puts every image below the point of $`\Phi_3(\mathrm{SRO})`$, and
  that point is below $`m_F`$ (by the replayed certificate $`\Phi_3(\mathrm{SRO}) \lt`$ PTm, or by DOM_RF). POINT-SRO $`\Rightarrow H_m`$ now holds without
  that certificate (by DOM_RF, reading $`\Phi_3(\mathrm{SRO})`$ as an RF fan-free pattern).
- **Open**, conjecture yes: the first fan needs $`I_0`$ ($`H_m`$). What is left is exactly the lower-bound program below $`\theta_0`$.

### 5.4 Covering minimality in $`R_2^S`$ up to $`\beta_0`$

Notation of §4, with $`k = 2`$. In case (P3b), $`\beta_0 = s^+ = \upsilon^2_{\omega+1}`$, and the only difference at $`\beta_0`$ is $`s \lt_2 s^+`$ in $`R_2^C`$.

- **Lemma GT** (proved, 1 review). The way to get minimality in $`R_2^S`$ from Carlson 2009, Thm 14.10(2): let $`Z`$ be S-isominimal and let
  $`P^*`$ be the least realization in $`R_2^C`$ of the pattern of $`Z`$ in $`R_2^S`$. If $`P^*`$ lies pointwise below $`Z`$ and the two structures agree on
  the relations among the points of $`P^*`$, then $`P^* = Z`$, $`Z`$ is isominimal in $`R_2^C`$, and $`Z`$ lies pointwise below every closed S-covering
  whose relations hold in $`R_2^C`$.
- **ISO-EQ** (proved, 1 review; case (P3b)). A finite closed $`Z \subseteq [0, \beta_0]`$ is S-isominimal iff it is isominimal in $`R_2^C`$ and does not
  contain both $`s`$ and $`s^+`$.
- **LOCAL⁺** (proved, 1 review; case (P3b)). MIN$`^S`$ holds on the closed interval $`[0, \beta_0]`$ (LOCAL had $`[0, \beta_0)`$). So no S-isominimal
  subset of $`[0, \beta_0]`$ contains $`s`$, every S-isominimal set that contains $`s`$ has a point $`\gt s^+`$, and Theorem CP holds in $`R_2^S`$ on $`[0, \beta_0]`$.
- **INCOMP** (proved, 1 review; case (P3b)). On $`[0, \nu_S]`$ neither structure contains the other: $`s \lt_2 s^+`$ holds in $`R_2^C`$ but not in $`R_2^S`$;
  $`s \le_1 z`$ and $`s^+ \le_1 z`$ hold in $`R_2^S`$ for every $`z \in (s^+, \nu_S]`$ but not in $`R_2^C`$.
- **NOGO-T** (proved, 1 review; case (P3b)). GT never applies to an S-isominimal set that contains $`s`$, and those are the sets where
  MIN$`^S`$ is needed for $`o_2 = \omega`$. The referee: in case (P3b) MOVE$`^S`$ already refutes MIN$`^S`$ at those sets, so NOGO-T does not change
  what has to be proved; and the paper's further claim "any proof must work inside $`R_2^S`$" is a remark about methods, not a theorem.
- **BLOCK-MOVE$`^S`$, NOLIM-COND$`^S`$ and RED** (proved, 1 review; they used SKEL⁺, now proved, §5.1). BLOCK-MOVE of §3 works in $`R_2^S`$ as an
  S-covering. MIN$`^S`$ implies that no LIM point of $`R_2^S`$ in $`(0, \nu_S) \setminus U_2`$ is in $`\mathrm{Core}_C(R_2^S)`$. $`\nu_C = \nu_S`$ follows from MIN$`^S`$ and
  CORE-S, where CORE-S says that every such LIM point, and $`s`$ when $`o_2 \gt \omega`$, is in $`\mathrm{Core}_C(R_2^S)`$ (true if $`\mathrm{Core}_C(R_2^S)`$ is an
  initial segment). The referee: given CORE-S, the instances of MIN$`^S`$ used are equivalent to the conclusion, so RED has content only
  through the global MIN$`^S`$.
- **DESCENT** (proved, 1 review). Carlson's argument of his L.14.6 works in $`R_2^S`$: if every S-covering of $`Z`$ extends to one of $`Z \cup Q`$, then
  $`Z`$ lies pointwise below $`Q`$. The extension property it needs fails at the same place as DEFECT and NEC (§4).
- **Not proved** (false as written, repairable). The remark that one "bad pair" pins nothing: its witness $`a = \omega^{\omega^s}`$ equals $`s`$, since $`s`$
  is an $`\varepsilon`$-number; a correct witness is $`a = \omega^{s\cdot 2}`$.

## 6. Status after the sixth round

- The level-0 description of $`R_2^S`$ holds at every countable ordinal (§5.1). So SKEL⁺, SKEL$`^\omega`$, RIGHT in $`R_2^S`$, NOLIM in $`R_2^C`$, and the
  results of [BREAK.md](BREAK.md) §7.1 and §8 that used them are proved (1 review each).
- The least chain of length 3 ($`R_2^C`$): characterized (CP3, LEAST3), not located. Lower bounds (§1), and $`c_2 \lt \omega_1^{CK}`$ (§5.2); no
  upper bound by an InaccPsi term, and no name. Whether $`C^*_3`$ needs an inaccessible: open; yes given $`FF_{cl}`$, or given $`H_m`$.
- The least fan ($`R_2^C`$): its structure is fixed, with order type $`o_F = \omega^2`$ (§5.2); its names are a conjecture. Whether it needs an
  inaccessible: $`H_m \Leftrightarrow FF_{RF}`$, which the lower-bound program below $`\theta_0`$ would give (§5.3); open.
- NOLIM: proved in $`R_2^C`$. In $`R_2^S`$ it is proved when there is no ghost, and below $`\beta_0`$ in cases (P3a), (P3b) (§3); otherwise open.
  $`\nu_C = \nu_S`$ is equivalent to NOLIM and $`o_2 = \omega`$ in $`R_2^S`$.
- $`o_k = \omega`$ in $`R_2^S`$ ($`k \ge 2`$): open. MIN$`^S`$ holds up to $`\beta_0`$ (§5.4); above $`\beta_0`$ it is open, and no transfer from $`R_2^C`$ can give it
  at the sets that matter.

## 7. Checks

Each run was under 60 seconds; none is a proof. Certificates count only when replayed.

- Chains (§1). The bounds are normal forms and strictly increasing (the referee's rerun gave the same output):
  $`\Lambda_\varepsilon \lt \psi_{\Omega_1}(\Omega_\omega\cdot 2) \lt \psi_{\Omega_1}(\Omega_\omega\cdot\omega) \lt x_L \lt y_L \lt \theta_0 \lt \psi_{\Omega_1}(I_0) \lt \psi_{\Omega_1}(I_1)`$ (with the conjectured
  names of $`x_L`$, $`y_L`$). The referee replayed six rounds of Carlson 2009, Def 9.4 for LEAST3 (d): the new points have exactly
  the claimed relations. The closed $`n`$-fans for $`n \le 8`$ are patterns with no chain of length 3.
- The least fan (§2; $`R_2^C`$; replayed). PTm $`\lt`$ PTL $`\lt`$ PTL2 $`\lt`$ PT, where PTL is PT with one pair $`u \lt_2 v \lt x`$, $`u \le_1`$ every later
  point (point $`u`$), and PTL2 the same with two pairs (point the second $`u`$). L1p $`\lt`$ PTm. $`\Phi_3(\mathrm{SRO}) \lt`$ L1p $`\lt \Phi_3`$((0,0,0)(1,1,1)(2,2,1))
  $`\lt`$ PT, and $`\Phi_3(\mathrm{SRO}) \lt \Phi_3`$((0,0,0)(1,1,1)(2,2,1)) directly. The configurations that ENDS, RE and FS exclude at the least
  fan are certified above $`x_F`$. The referee's 14 searches reproduced these, added four certificates of the same kind, and found
  nothing in the refuting directions. BLOCK on 3,738 random finite models: 0 failures (dropping a needed clause gives failures).
- NOLIM (§3). The referee's model of the skeleton on $`\upsilon`$-points: 60,000 trials, 0 failures. A first run had 2,003 failures, all
  from a fault of the model (reaches that end inside a block, which SKEL⁺ excludes), not counterexamples. The model does not
  include the $`R_1^+`$ part.
- $`R_2^S`$ (§4). The referee's model (ordinals below $`\omega^{\omega\cdot 4}`$, $`o = \omega\cdot 2`$): DEFECT on 12,000 trials (503 with a pair in $`B`$), NEC
  on 149 tests, 0 failures. The model has only the laws that the proofs use.
- Level 0 (§5.1). D0–D3 cannot be tested on program patterns, which carry no $`\upsilon`$-indices. The referee checked the index
  arithmetic of the proof on all indices below $`\omega^3\cdot 4`$: 0 failures.
- Block transfer (§5.2). The referee's random finite models, with the copy searched inside the model (only the steps of BT that are
  not facts about $`R_2`$): 1,669 cases met T1–T3 and found a copy (230 with points inside $`(s, t)`$), 0 failures. Dropping T1 or T3 gives
  failures; dropping T2 never does. The names of §5.2 are normal forms and in the required order for four bases (rerun: same output).
- The first fan (§5.3; replayed). RF_SRO on 18,206 patterns: all 10,633 standard matrices below SRO with at most 7 columns, 1,423
  landmarks, 6,149 images of the map of MU-B0, and SRO; 0 fans and 0 right ends with reach (57 images were too large
  for the program). The scan does flag (0,0,0)(1,1,1)(2,2,1), so it can fail; the referee's rerun on the first two sets gave the same.
  Certificates: PT $`\lt`$ RR, PT $`\lt`$ RRs (RR without $`c`$, with $`y \le_1 y+1`$), PTm $`\lt`$ RRm and PT $`\lt`$ RRm (RRm: RR with a point $`m \le_1 x, y, c`$);
  LP, L2, LNL, two nest patterns and $`\Phi_3(\mathrm{SRO})`$ each below PTm, as DOM_RF predicts. The referee certified seven more RF
  fan-free patterns below PTm, found no certificate in the refuting direction, and certified a non-RF control above PT.
- $`R_2^S`$ (§5.4). Two runs on tiny finite structures gave no information: a finite universe cannot satisfy Carlson 2009, Thm 14.10(1).

## 8. Open

- $`C^*_3`$: an upper bound by an InaccPsi term (conjecture: $`c_0 \lt \psi_{\Omega_1}(I_1)`$) and names; whether $`\varphi_{\lt\omega} \lt m_3`$; whether $`c_0`$ is the least
  apex with closed $`n`$-fans for every $`n`$, and whether it is the least apex with infinitely many $`\lt_2`$-successors; Conjecture CH.
- The inaccessible: $`H_m`$ ($`= FF_{RF}`$; it reduces to the lower-bound program below $`\theta_0`$, §5.3), $`FF_{cl}`$, $`FF_N`$, FF, POINT-SRO.
- The least fan: the names (the base $`B_F`$). Whether $`\sigma_N = m_F`$, and whether $`H_m`$ is equivalent to $`x_F \gt \theta_0`$.
- $`R_2^S`$: (ii) ⇒ (i) of CP3 and "⇐" of LEFT-CHAR; MIN$`^S`$ above $`\beta_0`$; PINNING and CORE-S; $`o_k = \omega`$ for $`k \ge 2`$; NOLIM with a ghost
  above $`\beta_0`$ (and NOLIM$`^*`$); $`\nu_C = \nu_S`$; the names (N-χ) and (N-ν) of [BREAK.md](BREAK.md) §7.3; RIGHT in $`R_2^C`$ above $`\beta_0`$.
