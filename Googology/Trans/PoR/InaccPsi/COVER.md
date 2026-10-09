[← Back](README.md) | [English](COVER.md) | [Japanese](COVER-ja.md)

# $`R_2^+`$ by covering minimality: chains of length 3, the least fan, NOLIM in $`R_2^C`$, the transfer to $`R_2^S`$, and upper bounds

This page continues [BREAK.md](BREAK.md). The status words are those of [README.md](README.md) §3: **proved** means that an
independent referee found the result proved with no fatal or blocking point. All results on this page are from 2026-10. They
come from three rounds of four papers, each paper refereed once: the fifth round (§1–§4), the sixth round (§5) and the seventh
round (§6). The eighth to tenth rounds are on the next page, [FANFREE.md](FANFREE.md), and the eleventh and twelfth on [VEBLEN.md](VEBLEN.md). "1 review"
means one referee. "2 reviews" means that two independent papers proved the result and each paper was refereed once. A
statement that its referee found not proved is listed under **Not proved**, even when the rest of its paper is proved. The
papers of the fifth round, three of the sixth and most of the seventh use Carlson's minimality against coverings (Carlson 2009, Thm 14.10(2)),
the tool of [BREAK.md](BREAK.md) §8.1. None of them uses Wilken, JSL 72 (2007), Carlson,
AML 38 (1999), Wilken, AML 45 (2006), or the equivalence of Carlson's definition with $`\Sigma_n`$-elementarity that Carlson 2009, p. 97,
announces. No result on this page is in Lean; the Lean results used are Lemma CONT (`psi_one_iSup`, [README.md](README.md) §3), Lemma L
and the comparison of terms (`cmp_eq_compare`).

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
  then $`m_F \gt \theta_0`$ (from replayed certificates). So a sufficient condition for the first fan to need an inaccessible is one
  statement about one matrix (the converse, whether $`\theta_0`$ can lie in $`(m_F, x_F]`$, is open). Open; conjecture: yes. Now $`H_m`$ has an exact equivalent, with no matrix in it (§5.3).
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
  extra relation is $`s \lt_2 s^+`$ in $`R_2^C`$, $`\max \mathrm{Pred}_1(s^+) = s`$ (so LIM2 of [THETA.md](THETA.md) §8.2 does not apply), and every S-isominimal
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
  refereed at proof level. (The seventeenth round: with it, H-RC holds at every restart below $`\nu_S`$, so the results of [SHIFT.md](SHIFT.md) §1
  and §8 that were at the outline level of SKEL⁺ rest on no outline, [SHIFT.md](SHIFT.md) §9.1. The eighteenth round: on this basis H-RC over every
  region at a fixed index distance, MULTI-RC\*, is proved in full, [SHIFT2.md](SHIFT2.md) §1.1. The nineteenth round carries it across every η-offset below
  $`\psi_{\Omega_2}(\Omega_2)`$, MULTI-RC$`^U`$, §2.1 there; the twentieth round below $`\psi_{\Omega_2}(\Omega_2^{\Omega_2})`$, §3.1 there; the twenty-first round below $`\psi_{\Omega_2}(\varepsilon_{\Omega_2+1})`$, [SHIFT3.md](SHIFT3.md) §1.1; the twenty-second round below $`\theta`$, §2.1 there; the twenty-third round below $`\psi_{\Omega_2}(\Omega_\omega + \Omega_2)`$, [SHIFT4.md](SHIFT4.md) §1.1, §1.4; the twenty-fourth round to the multipliers $`\zeta \ge \Omega_3`$ below the point $`\hat\zeta_2`$ of §2.2 there, §2.1, §2.2 there; the twenty-fifth round with long prefix restarts below $`\hat\zeta_\varepsilon`$, [SHIFT5.md](SHIFT5.md) §1.1; the twenty-sixth round with the hull cap below $`\hat\zeta_H`$, §2.1 there.)
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
- **Theorem OF** (proved, 1 review). $`o_F = \omega^2`$, so $`x_F = v_{\omega^2} = \sup_n v_{\omega\cdot n}`$ (here $`v_{\omega^2}`$ stands for $`x_F`$; it is not a member of $`V_F`$). If $`o_F \gt \omega^2`$, BT applies to $`s = v_{\omega^2}`$ with $`\alpha`$ a limit
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
  $`c_2 \lt \psi_{\Omega_1}(I_\omega)`$, and the names above with $`B_F \lt I_0`$, all in normal form, give $`y_2 \lt \psi_{\Omega_1}(I_0)`$. No InaccPsi term is proved to bound $`x_F`$, $`f_0`$, $`m_3`$
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
  referee added that PS is RF and fan-free, so $`m_F \gt \nu_C`$; this is now proved in a paper (1 review, §6.4).
- **Reduction RED-HM** (proved, 1 review, in the referee's shorter form). The map $`\mu`$ of the lower-bound program below SRO
  ([README.md](README.md) §3: the families (M1)–(M3) and the bases at level $`\ge 1`$) together with the fundamental-sequence step below SRO
  gives $`m_F \gt \theta_0`$, so the first fan needs an inaccessible. The paper also assumed RF_SRO (every $`\Phi_3(M)`$ with $`M \le`$ SRO is RF and
  fan-free; checked, §8). The referee shows that RF_SRO is not needed: the step puts every image below the point of $`\Phi_3(\mathrm{SRO})`$, and
  that point is below $`m_F`$ (by the replayed certificate $`\Phi_3(\mathrm{SRO}) \lt`$ PTm, or by DOM_RF). POINT-SRO $`\Rightarrow H_m`$ now holds without
  that certificate (by DOM_RF, reading $`\Phi_3(\mathrm{SRO})`$ as an RF fan-free pattern; this rests on one program reading instead).
- **Open**, conjecture yes: $`H_m`$, which implies that the first fan needs $`I_0`$ (the converse is open). What is left is exactly the
  lower-bound program below $`\theta_0`$ (§6.1).

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

## 6. The seventh round

Four papers, each refereed once. As in §5, the papers number the levels one lower than these pages, and here they are
renumbered. When a referee found that a true result adds no reduction (a blocking point about the claimed progress), the
result is listed under **Not counted**, and it is not counted as progress.

### 6.1 Whether the first fan needs an inaccessible: the lower side ($`R_2^C`$)

Notation of §5.3. $`D`$ is the set of countable InaccPsi normal forms with no inaccessible symbol; by Lemma I-FREE their values
are exactly the ordinals below $`\theta_0`$. Patterns are pointed, and $`\iota(S)`$ is the point of the least realization of $`S`$.

- **Proposition KQ** (proved, 1 review; SHARP_F of §5.3 stated again). Every ordinal below $`m_F`$ is itself $`\iota(S)`$ for an RF fan-free
  pattern $`S`$, not only a supremum of such points. So $`H_m`$ says exactly that every value of a term of $`D`$ is such a point.
- **The $`\ll`$-calculus** (proved, 1 review). $`S \ll T`$ means: every copy of $`T`$ has a copy of $`S`$ between its least nonzero element and
  its point. Then $`\iota(S) \lt \iota(T)`$, and $`\ll`$ is transitive. Five rules give $`S \ll T`$, each read off Carlson 2009: reflection at $`\le_1`$
  (L.5.5(1)), transfer at $`\le_2`$ (Def 5.3, clause 2), roots below every left end (L.5.5(2)), transitivity and the interval rule of $`\le_1`$
  (L.5.5(3), (5)), and minimality (Thm 14.10(2)). Lemma GEN: inside a pair $`x \lt_2 y`$ with $`x \le_1 R`$, the configurations that occur
  cofinally below $`x`$ are closed under putting copies inside $`(x, y)`$, adding an upper part below $`R`$, and adding a root. Unlike a
  certificate search, a proof in this calculus can use another comparison as a lemma. The referee: only the soundness of the rules
  is shown, not that every true $`S \ll T`$ can be derived with them.
- **Theorem TOP-SRO** (proved, 1 review). $`A_n \ll \mathrm{SRO}`$ for every $`n`$, where $`A_n`$ is an explicit pattern with $`n+1`$ nested levels of
  pairs. SRO[n] is read as an $`\Omega`$-tower, and $`\theta_0 = \sup_n \psi_{\Omega_1}(\tau_n)`$ with $`\tau_{n+1} = \Omega_{\tau_n}`$ (Lemma CONT); so this is the top step
  of $`\theta_0`$. That $`A_n = \Phi_3(\mathrm{SRO}[n])`$ is checked for $`n \le 4`$ (the program stops at $`n = 5`$). So the statement for $`\Phi_3`$ is proved
  for $`n \le 4`$ (before: certificates for $`n \le 3`$), and for $`n \ge 5`$ it is a conjecture.
- **Uniform limit steps** (proved, 1 review; for explicit patterns, and for $`\Phi_3`$ given the patterns it prints). For every $`n`$:
  NEST(k), $`\Phi_3(M_k[n]) \ll \Phi_3(M_k)`$, where $`M_k`$ is (0,0,0)(1,1,1) followed by $`k`$ copies of (2,1,1) (the index $`\omega^{k+1}`$ against $`\omega^k\cdot n`$);
  H0 for the block SRO[0] (the index $`\Omega_1`$; with a one-line fix by the referee); ZM for (0,0,0)(1,1,1)(2,1,1)(3,0,0)(4,1,1) (the index
  $`\psi_{\Omega_1}(\Omega_\omega)`$); SUB for the indices $`\omega^\omega`$ and $`\omega^{\omega^\omega}`$. And two of the 26 undecided limit jumps of the lower-bound
  program ([README.md](README.md) §3), at their pattern images: LJ1, $`\psi_{\Omega_1}(\Omega_{\psi_{\Omega_1}(1)+\omega}) \lt \psi_{\Omega_1}(\Omega_{\psi_{\Omega_1}(\omega)})`$, and LJ2,
  $`\psi_{\Omega_1}(\Omega_{\psi_{\Omega_1}(\Omega_1\cdot 2)} + \Omega_{\omega\cdot 2}) \lt \psi_{\Omega_1}(\Omega_{\psi_{\Omega_1}(\omega^{\Omega_1+1})})`$. They were undecided because their derivations are deep.
- **Not counted** (blocking point). RED-$`\nu`$: if a map $`\nu`$ from $`D`$ to RF fan-free patterns and a predecessor system on $`D`$ satisfy
  $`\iota(\nu(s)) \lt \iota(\nu(t))`$ for every predecessor $`s`$ of $`t`$, then $`H_m`$. The referee: with "all smaller terms" as predecessors this is
  OE_F of §5.3 (an order-preserving map from $`[0, \theta_0)`$ into the points of RF fan-free patterns), which is equivalent to $`FF_{RF}`$ by
  SHARP_F. So it is true but reduces nothing, and the fundamental sequences of InaccPsi that the paper lists as missing are not
  needed. What is left is a map $`\nu`$ on all of $`D`$ and the comparisons $`\nu(s) \ll \nu(t)`$ for all steps.
- **Not proved.** The remark that the calculus never gives a second point with the same reach is false (the referee gives a
  pattern where it does). The evidence "the patterns just above SRO are still RF and fan-free" is circular: it needs a point of
  such a pattern $`\ge \theta_0`$, which is POINT-SRO, and POINT-SRO already implies $`H_m`$.
- **Open**, conjecture yes: $`H_m`$. It implies $`x_F \gt \theta_0`$ (the first fan needs an inaccessible); the converse, whether $`\theta_0`$ can lie
  in $`(m_F, x_F]`$, is open.

### 6.2 Upper bounds by InaccPsi terms ($`R_2^C`$)

PT$`^*`$ is the set $`\{0, 1, x_F, y_1, y_2\}`$.

- **Lemma UB-COV** (proved, 1 review, for these two sets). Let $`Q`$ be closed and $`f`$ an order-preserving map from the indecomposables
  of PT$`^*`$ (or of $`\{0, 1\} \cup C^*_3`$) onto those of $`Q`$ that keeps every positive atom. Then that set lies pointwise below $`Q`$. Negative
  atoms need not be copied, so the fact that the least fan is open plays no role in upper bounds. (The general form in the paper is
  imprecise: the right end of a $`\lt_1`$-atom may be decomposable.)
- **Lemma CRIT** (proved, 1 review). (a) If $`a \lt b \lt c`$, $`a \lt_2 b`$ and $`a \lt_2 c`$, then $`x_F \le a`$, $`y_1 \le b`$, $`y_2 \le c`$. (b) $`f_0`$ is the least
  $`a`$ such that some $`c`$ has $`a \lt_2 c`$ and a $`\le_1`$-predecessor in $`(a, c)`$. (c) If $`a \lt b \lt c`$, $`a \lt_2 c`$ and $`b \lt_2 c`$, then $`\{a, b, c\}`$ is
  a chain, and $`c_0 \le a`$, $`c_1 \le b`$, $`c_2 \le c`$. So one pair below a bound, with one more point between, is enough. (b) never finds $`x_F`$,
  because the least fan is open.
- **Lemma CORE-SELF** (proved, 1 review). For $`a \lt \kappa_C`$, $`\mathrm{lh}(a) \lt \kappa_C \le \Omega_1`$ (Carlson 2009, Thm 14.14). So no atom joins a point
  of the core to an uncountable ordinal. (The paper adds that inaccessibles can enter an upper bound only as indices in names; this
  does not follow, and the referee lists it as a remark.)
- **Theorem ITER** (proved, 1 review, as an implication). Let $`b`$ be the limit of $`\mathrm{Pred}_1(b) = \{w_\zeta : \zeta \lt o\}`$. If (H0)
  $`w_0 \le \psi_{\Omega_1}(A)`$, and (HQ) $`w_\zeta \le \psi_{\Omega_1}(A + Q\cdot\zeta)`$ implies $`w_{\zeta+1} \le \psi_{\Omega_1}(A + Q\cdot(\zeta+1))`$, then $`b \le \psi_{\Omega_1}(A + Q\cdot o)`$.
- **Remark NO-HALF** (proved, 1 review). A structure of InaccPsi values that satisfies the clauses of Carlson 2009, Def 5.3 gives
  relations of $`R_2^C`$ only where it equals $`R_2^C`$ on the whole initial segment below. So the route "realize all patterns in a hull
  structure, then push down" needs the full analysis of $`R_2^C`$.
- **Not counted** (2 blocking points). UB-GEN (proved from Carlson 2009, L.14.9 and Thm 14.10(2)): $`\iota(P, p) \lt t`$ iff some strictly
  increasing map sends the points $`\le p`$ of the closure of $`P`$ under Carlson's generating rules into $`t`$. That closure is isomorphic to an
  initial segment of $`R_2^C`$, so this is the definition of an upper bound written another way, and no such map is built. TARGETS: (H0)
  and (HQ) with suitable $`A`$, $`Q`$ below $`I_0\cdot\omega`$ give $`x_F \lt \psi_{\Omega_1}(I_0\cdot\omega)`$, and below $`I_1`$ give $`c_0 \lt \psi_{\Omega_1}(I_1)`$. The referee
  proves the converse (take $`A`$ just above the collapse arguments of a name of $`x_F`$, and $`Q = 1`$), so while $`A`$ is free these are not
  sub-goals. They become sub-goals only if $`A`$ is fixed, for example by $`\psi_{\Omega_1}(A) = m_F`$.
- **Open**: $`x_F \lt \psi_{\Omega_1}(I_0\cdot\omega)`$ (the conjectured names of §6.4 give it), $`c_0 \lt \psi_{\Omega_1}(I_1)`$ (conjecture), and every upper bound of $`m_F`$,
  $`x_F`$, $`f_0`$, $`m_3`$, $`c_0`$ by an InaccPsi term.

### 6.3 $`\nu_C = \nu_S`$ as one $`\Sigma_2`$ statement inside the common structure

Notation of §4 and §5.4 with $`k = 2`$, read in $`R_2^C`$: $`x = x_2 = \upsilon^2_\omega`$ (Theorem O$`^C`$), $`\nu = \nu_C`$, and
$`U_2 = \{\upsilon^2_n : n \lt \omega\} \cup \{x, \nu\}`$. Below $`\nu_C`$ the two structures agree (NU-CT); $`R`$ is this common structure on $`\nu_C`$. The
segments are $`S_n = [\upsilon^2_n, \upsilon^2_{n+1})`$ and $`S_\omega = [x, \nu)`$.

- **Theorem EQ** (proved, 1 review; it uses no NOLIM, MIN$`^S`$ or CORE-S). $`\nu_C = \nu_S`$ iff $`x \lt_2^S \nu_C`$ iff $`R|x`$ is $`\Sigma_2`$-elementary in $`R|\nu_C`$
  (for the language $`0, +, \le, \le_1, \le_2`$; this is the definition of $`\le_2`$ in $`R_2^S`$, read in the common structure). If they differ, then $`\beta_0 = \nu_C`$, and the only atom with right end $`\le \beta_0`$ on which the
  structures differ is $`x \lt_2 \nu_C`$. This is the level-2 analogue of $`\upsilon_\omega \lt_2 \upsilon_{\omega+1}`$. The referee: it follows almost directly from
  NU-CT, so it adds little.
- **Lemma CUT** (proved, 1 review). No $`\lt_2`$-pair crosses a point of $`U_2`$, and a point below $`u \in U_2 \setminus \{\nu\}`$ is in $`U_2`$ or has its reach
  below $`u`$. So $`R`$ splits into $`[0, \upsilon^2_0)`$, the segments $`S_n`$ and $`S_\omega`$.
- **Lemma DROP** (proved, 1 review). $`x \lt_2^S \nu`$ iff every $`\Pi_1`$ property with parameters below $`x`$ that holds of a tuple meeting $`S_\omega`$ holds
  of a tuple below $`x`$. Each $`S_n`$ has a $`\Pi_1`$ property with parameters below $`\upsilon^2_n`$ that holds first there. So a ghost is a $`\Pi_1`$
  property whose first instances all lie in $`S_\omega`$.
- **Theorem SEG-RED** (proved, 1 review). Wilken 2020, Prop 21.11, used in its stated direction and restricted to the segments: a
  condition SC implies $`x \lt_2^S \nu`$, so $`\nu_C = \nu_S`$. SC: every finite piece of $`S_\omega`$ has a copy in some $`S_n`$ above the given parameters
  such that every finite extension inside $`S_n`$ can be carried back into $`S_\omega`$, keeping sums with small parameters.
- **LBC ⇒ SC** (proved, 1 review). LBC is a base change $`T : S_n \to S_\omega`$ with $`T(\upsilon^2_n) = x`$ that keeps $`+`$, $`\le_1`$ and $`\le_2`$. RM ⇒ LBC
  (outline only, through FRAG2): beyond Wilken's base changes, LBC asks only that $`T`$ keep the reaches of restarts. The referee: SC
  needs only finite maps, so a finite form of LBC is enough, and it matches the scope of FRAG2 (now at outline level on the
  initial part of each segment, [FANFREE.md](FANFREE.md) §3, and proved below the first limit of critical indices, [FANFREE.md](FANFREE.md) §7.3).
- **BLOCK-SC** (proved, 1 review) and **REGION-SC** (outline only, through FRAG). SC holds when the piece lies in $`[x, x^+)`$, with $`x^+`$ the
  next $`\upsilon`$-point, and the extension lies below the first $`\delta`$-point above $`\upsilon^2_n`$ (BLOCK-SC), or in the whole restart region of
  $`\upsilon^2_n`$ (REGION-SC).
- **Open** (the blocking point, which the paper states itself): SC, LBC, RM, and so $`\nu_C = \nu_S`$. RM says that the reaches of restarts
  correspond between the segments of level 2; it is a conjecture, and the reaches above $`\nu_P`$ are not known. Pieces elsewhere in
  $`S_\omega`$ are not covered, among them the inner pair of the nested configuration whose top is $`\nu_C`$. None of the three sub-goals of the
  plan is proved (refute case (P3b) together with "$`s`$ is in $`\mathrm{Core}_C(R_2^S)`$"; CORE-S; $`o_2 = \omega`$ in $`R_2^S`$). The paper's claim that
  they are detours is a remark about methods, not a theorem.

### 6.4 The names of the least fan ($`R_2^C`$)

Notation of §2 and §5.2.

- **Lemma GAP-F** (proved, 1 review). Let $`v \in V_F`$ and $`v^+`$ the next member. Every RF fan-free pattern has covered copies in $`(v, v^+)`$
  above any finite closed set of parameters $`\le v`$, and $`v \le_1`$ every point of such a copy. (A covered copy keeps the positive atoms; it
  need not be isomorphic.)
- **Corollary GP** (proved, 1 review). Let Gp be PTm with a pair $`p \lt_2 q`$ added. Its least realization has root $`m_F`$, and
  $`m_F \lt p^* \lt q^* \lt v_1`$. So the least $`\lt_2`$-pair above $`m_F`$ lies below $`v_1`$, and $`p^*`$ is the least left end in $`(m_F, v_1)`$.
- **Lower bounds** (proved, 1 review; from NU-CT and PINS, 1 review each).
  $`m_F \gt \nu_C \gt \nu_P \gt \rho_{\Lambda^*} \gt \Lambda_\varepsilon = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta+\varepsilon_{\Omega_1+1}+1})`$ (before: $`m_F \gt \upsilon_{\omega^3}`$, §5.3; now also $`\nu_C \gt \psi_{\Omega_1}(\Omega_\omega + \Omega_2)`$, [THETA.md](THETA.md) §1, and $`\nu_C \ge \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta+3}\cdot 2)`$, §9.1 there, and $`\nu_C \ge X_4`$, [SHIFT.md](SHIFT.md) §1, and $`\nu_C \ge X_5`$ given FRAG, §8.1 there). From one program
  reading each, $`\Phi_3(M)`$ is RF and fan-free, so its point is below $`m_F`$, for M = SRO, (0,0,0)(1,1,1)(2,1,1)(3,1,1), (0,0,0)(1,1,1)(2,2,0),
  and (0,0,0)(1,1,1)(2,2,1)[n] for $`n \le 4`$.
- **Proposition NEED** (proved, 1 review). If $`m_F`$ has an InaccPsi name, then every name of $`m_F`$ contains an inaccessible iff $`H_m`$. With
  $`m_F = \psi_{\Omega_1}(B_F)`$ in normal form: $`B_F \ge \psi_{I_0}(0)`$ iff $`H_m`$. Given POINT-SRO, $`B_F \gt \psi_{I_0}(0)`$. (It uses the comparison of terms,
  which is in Lean: `cmp_eq_compare`.)
- **Lemma INDEX** (proved, 1 review; it follows from the order type alone). If the points of the least fan are one continuous increasing
  sequence starting at $`m_F`$, then the indexing of the names of §5.2 is the only one.
- **Conjecture FNAME**: $`B_F = I_0`$. So $`m_F = \psi_{\Omega_1}(I_0)`$, $`P_F = \psi_{\Omega_2}(I_0)`$, $`v_{\omega\cdot n} = \psi_{\Omega_1}(I_0 + \omega^{P_F+1}\cdot n)`$,
  $`t_n = \psi_{\Omega_1}(I_0 + \omega^{P_F+1}\cdot n + P_F)`$, $`x_F = \psi_{\Omega_1}(I_0 + \omega^{P_F+2})`$, $`y_i = \psi_{\Omega_1}(I_0 + \omega^{P_F+2} + P_F\cdot i)`$. Checked: the 19 names
  are normal forms in the order of the proved shape, and $`\theta_0 \lt m_F \lt \cdots \lt y_2 \lt \psi_{\Omega_1}(I_0\cdot 2) \lt \psi_{\Omega_1}(\varepsilon_{I_0+1}) \lt \psi_{\Omega_1}(I_1)`$
  for these names. The evidence is analogy only: Wilken's index operator for pure $`R_2`$ (Wilken 2021, Def 3.6) with $`\Omega`$ read as $`I_0`$, the
  reading behind Wilken's claim and C3′.
- **Blocking point in the evidence** (the referee). The paper read the trio shapes as "the point of $`\Phi_3`$((0,0,0)(1,1,1)(2,2,2)) is
  $`\psi_{\Omega_1}(\varepsilon_{I_0+1})`$". This is false: $`\Phi_3`$((0,0,0)(1,1,1)(2,2,2)) is a single pair, RF and fan-free, so its point is below $`m_F`$ (DOM_RF; also a
  replayed certificate $`\Phi_3`$((0,0,0)(1,1,1)(2,2,2)) $`\lt`$ PTm). So the point of $`\Phi_3(M)`$ does not increase from (0,0,0)(1,1,1)(2,2,1) to
  (0,0,0)(1,1,1)(2,2,2), and trio shapes above (2,2,1) tell nothing about points of $`R_2^C`$ through $`\Phi_3`$. Also, the checking program did not
  flatten sums; with flat sums the bases $`I_0\cdot 2`$, $`\psi_{I_0}(0)\cdot 2`$ and $`\psi_{I_0}(0) + \Omega_\omega`$ also fit the names of §5.2. So no check singles
  out $`I_0`$.
- **Open**: every upper bound by an InaccPsi term (so no name is proved in either direction); $`H_m`$; whether each gap of $`V_F`$ is no
  richer than a copy of $`\mathrm{Core}_F`$ relative to its bottom.

## 7. Status after the seventh round

- The level-0 description of $`R_2^S`$ holds at every countable ordinal (§5.1). So SKEL⁺, SKEL$`^\omega`$, RIGHT in $`R_2^S`$, NOLIM in $`R_2^C`$, and the
  results of [BREAK.md](BREAK.md) §7.1 and §8 that used them are proved (1 review each).
- The least chain of length 3 ($`R_2^C`$): characterized (CP3, LEAST3), not located. Lower bounds (§1), and $`c_2 \lt \omega_1^{CK}`$ (§5.2). No upper
  bound by an InaccPsi term and no name. An upper bound needs only one pair below the bound with one more point between (CRIT,
  §6.2); the split of the bound into a start and a cost per step is equivalent to the bound itself. Whether $`C^*_3`$ needs an
  inaccessible: open; yes given $`FF_{cl}`$, or given $`H_m`$.
- The least fan ($`R_2^C`$): its structure is fixed, with order type $`o_F = \omega^2`$ (§5.2), and $`m_F \gt \nu_C`$ (§6.4). Its names are a conjecture,
  now with the base $`B_F = I_0`$, supported by analogy only (§6.4).
- The inaccessible: $`H_m \Leftrightarrow FF_{RF}`$ (§5.3), and $`B_F \ge \psi_{I_0}(0) \Leftrightarrow H_m`$ (§6.4). The $`\ll`$-calculus proves the top step at SRO and several uniform
  families of steps, but not all steps (§6.1). $`H_m`$ implies that the first fan needs an inaccessible; the converse is open.
- NOLIM: proved in $`R_2^C`$. In $`R_2^S`$ it is proved when there is no ghost, and below $`\beta_0`$ in cases (P3a), (P3b) (§3); otherwise open.
- $`\nu_C = \nu_S`$ is equivalent to NOLIM and $`o_2 = \omega`$ in $`R_2^S`$ (§3), and to the single $`\Sigma_2`$ statement $`x_2 \lt_2^S \nu_C`$ inside the common structure
  (§6.3). A segment condition SC implies it; SC is proved on the first block of $`x_2`$; in general it needs the reaches of restarts to
  correspond between the segments of level 2 (RM, conjecture).
- $`o_k = \omega`$ in $`R_2^S`$ ($`k \ge 2`$): open. MIN$`^S`$ holds up to $`\beta_0`$ (§5.4). In case (P3b) it is false at the S-isominimal sets that contain $`s`$
  (MOVE$`^S`$), so there the target is to refute (P3b) together with PINNING.

## 8. Checks

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
- The lower side (§6.1). The explicit patterns equal the patterns that $`\Phi_3`$ prints for SRO, $`A_0, \ldots, A_4`$ and 25 more comparisons (the
  referee's rerun: 25 of 25; the paper said 29). Replayed certificates: $`\Phi_3(\mathrm{SRO}[n]) \lt \Phi_3(\mathrm{SRO})`$ for $`n = 1, 2, 3`$, and 11 sample steps. Of the 26
  undecided limit jumps of the lower-bound program, 5 now have replayed certificates (one of them is LJ1), LJ2 is proved by hand, and
  20 stay undecided; none is refuted (all 26 are now proved, [FANFREE.md](FANFREE.md) §1). The referee's searches in the reverse direction on 6 of the 20 (50 s each) found nothing. The
  reading of the indices $`\Omega_\xi`$ as nested blocks of pairs is checked on 1,423 landmarks and 40 members of fundamental sequences.
- Upper bounds (§6.2). The terms $`\Lambda_\varepsilon \lt \theta_0 \lt \psi_{\Omega_1}(I_0) \lt \psi_{\Omega_1}(I_0\cdot\omega) \lt \psi_{\Omega_1}(I_1) \lt \psi_{\Omega_1}(I_\omega)`$ are normal forms and increasing,
  and so are the bounds of ITER for the tested bases (the referee's rerun gave the same output). One line of the check compares a
  term with itself, so it tests nothing.
- The segments (§6.3). The conjectured names of the points of level 2 and the shift from $`S_n`$ to $`S_\omega`$ keep normal form and order: 33
  points, and 798 points in the referee's larger run, 0 failures. This tests only the arithmetic shape, not the relations of $`R_2`$.
- The names of the fan (§6.4). The 19 names are normal forms in the required order (Python and Lean agree; the referee reran both).
  The certificates around GP are replayed, and the three searches in the refuting direction timed out; none was exhausted. The
  referee replayed the certificate $`\Phi_3`$((0,0,0)(1,1,1)(2,2,2)) $`\lt`$ PTm.

## 9. Open

- $`C^*_3`$: an upper bound by an InaccPsi term (conjecture: $`c_0 \lt \psi_{\Omega_1}(I_1)`$) and names; whether $`\varphi_{\lt\omega} \lt m_3`$; whether $`c_0`$ is the least
  apex with closed $`n`$-fans for every $`n`$, and whether it is the least apex with infinitely many $`\lt_2`$-successors; Conjecture CH.
- The inaccessible: $`H_m`$ ($`= FF_{RF} = FF_N`$, and $`m_F = \sup_k \iota(\mathrm{CH}_k)`$, [FANFREE.md](FANFREE.md) §4; what is left is a map from all of $`D`$ to RF fan-free patterns with $`\nu(s) \ll \nu(t)`$ at every step, §6.1; with values without L1p it gives $`\iota(\mathrm{CH}_2) \ge \theta_0`$, [FANFREE.md](FANFREE.md) §7.2; native codes reach the Bachmann–Howard ordinal, [FANFREE.md](FANFREE.md) §10.2, and now $`\upsilon_2\cdot\upsilon_1`$, [VEBLEN.md](VEBLEN.md) §2, then $`\Phi_1`$, §9),
  $`FF_{cl}`$, FF, POINT-SRO; whether $`H_m`$ is equivalent to $`x_F \gt \theta_0`$.
- The least fan: the names (the base $`B_F`$; conjecture $`I_0`$, §6.4), and an upper bound such as $`x_F \lt \psi_{\Omega_1}(I_0\cdot\omega)`$ ($`\sigma_N = m_F`$ is now proved, [FANFREE.md](FANFREE.md) §4).
- $`R_2^S`$: (ii) ⇒ (i) of CP3 and "⇐" of LEFT-CHAR; MIN$`^S`$ above $`\beta_0`$; PINNING and CORE-S; $`o_k = \omega`$ for $`k \ge 2`$; NOLIM with a ghost
  above $`\beta_0`$ (and NOLIM$`^*`$); $`\nu_C = \nu_S`$ (by §6.3: SC, or RM; SC beyond the first limit of critical indices in each segment, [FANFREE.md](FANFREE.md) §7.3; now SC at the long restarts, which the reduction always needs, [FANFREE.md](FANFREE.md) §10.3; directly in $`\Sigma_2`$ form, a local base change and translations with a fixed finite set below the copy, [VEBLEN.md](VEBLEN.md) §4; with that set the reduction fails on the zone of the base change, §11; now (HC) is proved and the reduction repaired, left: a twisted upward rule, [THETA.md](THETA.md) §4); the names (N-χ) and (N-ν) of [BREAK.md](BREAK.md) §7.3; RIGHT in $`R_2^C`$ above
  $`\beta_0`$.
