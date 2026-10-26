import Googology.Trans.PoR.InaccPsi.R2.UiTop
import Googology.Trans.PoR.InaccPsi.R2.UzG

set_option autoImplicit false

/-!
# The bound of `Tᵗ ∩ Ω₂` by `θ = ψ_{Ω₂}(Ω_ω)`: [W07a] Theorem 3.23 with the own step `ϑ_k ↔ ψ_{Ω_{k+1}}` for every `k`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

Conventions as in `R2.CitedSy`, `R2.CitedUc` (`Ω_i = Om i`, `Ω₁ = Om1`, `Ω₂ = OmTwo`, `Tset τ = Tᵗ`; every base `τ` a
countable `ε`-number).  ψ-side (all Lean): `θ_i := ψ_{Ω_{i+1}}(Ω_ω)` (`θ₁ = ConjT.th S`), `K^{(i)}_q := Ul.UlK S i q`,
`Hˡ^{(k)}_γ := Ul.ulH S k γ`, `G := {x | x ∈ K^{(i)}_{θ_i} for every finite i ≥ 1}`.

Literal texts.  (D) Def 3.1, (B) Lemma 3.3, (W) Def 3.4 and Lemma 3.5, (T) Def 3.22, (Θ) Theorem 3.23, (L) Lemma 3.30 as
quoted in `R2.CitedSy` (word for word); and
* (M) Lemma 3.2 (b): "For `α₁ ≤ α₂` and `β₁ ≤ β₂` we have `Cⁿ_m(α₁, β₁) ⊆ Cⁿ_m(α₂, β₂)`."
* (I) Lemma 3.7: "For `m < n` the set `Tⁿ_m` is inductively characterized as follows: • `Ω_m ⊆ Tⁿ_m` • `ξ, η ∈ Tⁿ_m ⇒ ξ
  + η ∈ Tⁿ_m` • `ξ ∈ Tⁿ_m ∩ Ω_{k+2} ⇒ ϑⁿ_k(ξ) ∈ Tⁿ_m` for `m ≤ k < n`."  (Def 3.6: "`Tⁿ_m := Cⁿ_m(Ω_{m+2}, 0)` and set
  `Tⁿ_n := Ω_n` for convenience.")
* (R) Lemma 3.8: "Let `m < n`.  For all `α ∈ Cⁿ_m(0, Ω_{m+1}) ∩ Ω_{m+2}` we have `ϑⁿ_m(α) < Ω_{m+1}` and `ϑⁿ_m(α) ∉
  Cⁿ_m(α, ϑⁿ_m(α))`."  Corollary 3.9: "For `m < n` we have `Tⁿ_m ⊆ Tⁿ_{m+1} = Cⁿ_m(0, Ω_{m+1}) = Cⁿ_m(Ω_{m+2},
  Ω_{m+1})`."
* (Q) Def 3.10: "Let `m < n`.  By recursion on the definition of `Tⁿ_{m+1}` we define `Pⁿ_m(ξ) ⊆_fin Ω_{m+1}` for every
  `ξ ∈ Tⁿ_{m+1}`.  • `Pⁿ_m(ξ) := {ξ₁, …, ξ_r}`, provided `ξ =ANF ξ₁ + ⋯ + ξ_r < Ω_{m+1}` • `Pⁿ_m(ξ) := Pⁿ_m(ξ₁) ∪
  Pⁿ_m(ξ₂)`, if `ξ₁, ξ₂ ∈ Tⁿ_{m+1}` and `ξ =NF ξ₁ + ξ₂ > Ω_{m+1}` • `Pⁿ_m(ξ) := Pⁿ_m(η)`, provided `ξ = ϑⁿ_k(η)`, `η ∈
  Tⁿ_{m+1} ∩ Ω_{k+2}`, `m < k < n`."  Lemma 3.11: "(a) `Pⁿ_m` is well defined.  (b) Let `α < Ω_{m+2}` and `β < Ω_{m+1}`.
  For every `ξ ∈ Tⁿ_{m+1}` we have `ξ ∈ Cⁿ_m(α, β) ⇔ Pⁿ_m(ξ) ⊆ Cⁿ_m(α, β)`."
* (S) Def 3.13: "`Θⁿ_{n−1}(k) := ϑⁿ_{n−1}^{(k)}(0)` and `θⁿ_{n−1} := sup_{k<ω} Θⁿ_{n−1}(k)` … Descending from `m = n −
  2` down to `m = 0` we define `Θⁿ_m(k) := ϑⁿ_m(Θⁿ_{m+1}(k))` and `θⁿ_m := sup_{k<ω} Θⁿ_m(k)`."  Theorem 3.14: "For `m <
  n` we have `Tⁿ_m ∩ Ω_{m+1} = θⁿ_m`."  Convention 3.25: "we will indicate this explicitly in writing `ϑᵗ` and `Tᵗ`
  instead of `ϑ₀` and `T₀`."  (U′) Remark after Corollary 3.15: "Notice that every ordinal in `Tⁿ_m` where `m < n` can
  be identified with a unique notation that uses parameters below `Ω_m`."

Our steps.  Fix `n ≥ 2`; `ϑ_j := ϑⁿ_j`, `T_m := Tⁿ_m`, `P_k := Pⁿ_k`, `C(α, β) := Cⁿ_k(α, β)`.  `ϑ_j` for `j ≥ 1` does
not depend on `τ` (D: `Ω₀ = τ` enters `Cⁿ_m` only for `m = 0`).  `T_{m+1} ∩ Ω_{m+2}` is an ordinal for `m + 1 ≤ n` (S,
`Tⁿ_n = Ω_n`), and `T_m ⊆ T_{m'}` for `m ≤ m'` (R).
* (◇X) **Indices.**  For a normal `f` whose fixed points are limits (`ω^·`; `φ(a, ·)`, `a ≥ 1`; `Hˡ^{(k)}_γ`, whose
  values are strongly critical, `Ul.ulH_SC`, `Ul.ulH_normal`): `idx_f(c) := p + 1 + (c − p)` with `p := max(Fix_f ∩ (c +
  1))` (`Fix_f` is closed), `idx_f(c) := c` if `Fix_f ∩ (c + 1) = ∅`.  (X1) `idx_f` enumerates `Ord ∖ Fix_f`: below a
  fixed point `p` the non-fixed ordinals contain the successors `< p` (order type `p`), and every ordinal in `(p, p′)`,
  `p′` the next fixed point (a limit), is non-fixed.  (X2) `c ≤ idx_f(c) ≤ c + 1` (`Uz.uz_le_idx`); (X3) `idx_f(c) < x`
  for `x ∈ Fix_f`, `c < x`.  So `ω̄_β = ω^{idx_ε(β)}` (W: the additive principal numbers are the `ω^x`, and `ω^x ∈ E ⇔ x
  ∈ E`; `idx_ε := idx_{ω^·}`).  Put `c_a := Ω_k` (`a < Ω_k`), `1` (`a = Ω_k`, or `a > Ω_k` strongly critical), `0`
  (otherwise; `c_a` depends on `k`): the number of non-fixed `y` with `φ(a, y) ≤ max(Ω_k, a)` (`φ(a, Ω_k) = Ω_k` for `a
  < Ω_k`, X1; `φ(a, 0) = a` iff `a` is strongly critical).  `V_k(a, c) := φ(a, idx_a(c_a + c))` (`idx_a :=
  idx_{φ(a,·)}`) enumerates the values `φ(a, y) > max(Ω_k, a)` at non-fixed `y`; `a, Ω_k < V_k(a, c)`, `c ≤ idx_a(c_a +
  c) < V_k(a, c)`. `W_k(γ, c) := Hˡ^{(k)}_γ(idx_γ(c))` (`idx_γ := idx_{Hˡ^{(k)}_γ}`).
* (◇K) **ψ-facts** (Lean, `K = K^{(i)}_q`, `q` strongly critical): `p + 1 + (c − p) ∈ K ⇔ c ∈ K` for the `p` of X at `f
  = φ(a, ·)` (`Uz.uz_idx_veb`, from (FC) `Uz.uz_veb_fc`; `a = 0` is `ω^·`) and at `f = Hˡ^{(s)}_γ`, `i < s`, `q ≤
  Ω_{i+1}`, `γ < Ω_{s+2}` (`Uz.uz_idx_H`, from (FC) `Uw.uw_fc_max`); `Ω_{j+1}·a + c ∈ K ⇔ a, c ∈ K` (`c < Ω_{j+1}`,
  `Uz.uz_parts`); `ω^x ∈ K ⇔ x ∈ K` (`Ul.ulK_dec`, `Ul.UlK.opow`); `φ(a, b) ∈ K ⇔ a, b ∈ K` for `a, b < φ(a, b)`
  (`Uo.uoK_veb`); the components of a member are members (`Uo.uoK_lead_tail`, `Ul.ulK_dec`); `Ω_{j+1} ∈ K`
  (`Us.us_K_Om`); `x < Ω_{k+1}`: `x ∈ K^{(k)}_v ⇔ x < v` for strongly critical `Ω_k < v ≤ Ω_{k+1}` (`Ul.ulK_lt_W`); (L1)
  `Hˡ^{(j)}_γ(y) ∈ K^{(k)}_v ⇔ γ, y ∈ K^{(k)}_v` for `k < j`, `γ < Ω_{j+2}`, `Hˡ^{(j)}_γ(y) ≠ y`, `Hˡ^{(j)}_γ(y) <
  Ω_{j+1}` (`Uz.uz_L1`, every level `γ`, no notation hypothesis).  Hierarchy: `γ ∈ K^{(k)}_{Hˡ^{(k)}_γ(y)}`
  (`Ul.ulH_D_lt`, `Ul.ul_vis`); a value `v` of `Hˡ_γ` is fixed by `Hˡ_{γ'}`, `γ' < γ`, `γ' ∈ K^{(k)}_v`
  (`Uc.ucG_fix_lower`); a strongly critical `v > Ω_k` with `γ ∈ K^{(k)}_v` fixed by every such `Hˡ_{γ'}` is a value of
  `Hˡ_γ` (`Uc.ucG_range`).
* (◇CL) **The collapse by its parameters.**  Let `1 ≤ k < n`, `α ∈ T_{k+1} ∩ Ω_{k+2}`.  (a) If `v` is additive
  principal, `Ω_k < v ≤ Ω_{k+1}`, `P_k(α) ⊆ v`, and `ϑ_k(ξ) < v` for every `ξ ∈ T_{k+1} ∩ α` with `P_k(ξ) ⊆ v`, then
  `ϑ_k(α) ≤ v`: for `v = Ω_{k+1}` by D; else every `u ∈ C(α, v)` lies in `T_{k+1}` (M, R) and has `P_k(u) ⊆ v`, by
  induction on the generation (D): `u < v`; `P_k(u₁ + u₂) ⊆ P_k(u₁) ∪ P_k(u₂)` (Q: `P_k` of a sum is the union over its
  additive components, which are components of `u₁`, `u₂`); `P_k(ϑ_j(x)) = P_k(x)`, `j > k`; `u = ϑ_k(ξ)`, `ξ ∈ C ∩ α`:
  `u < v` by hypothesis, `P_k(u) = {u}` (B (b)).  So `C(α, v) ∩ Ω_{k+1} ⊆ v` (`v` additive principal), `α ∈ C(α, v)`
  (Lemma 3.11 (b)), and D gives `ϑ_k(α) ≤ v`.  (b) `ξ₀ := ϑ_k(α) < Ω_{k+1}` (R), `ξ₀ = C(α, ξ₀) ∩ Ω_{k+1}` (D, B (a)),
  so `P_k(α) ⊆ ξ₀` and, for `ξ ∈ T_{k+1} ∩ α` with `P_k(ξ) ⊆ ξ₀`, `ξ ∈ C(α, ξ₀)` (3.11 (b)), `ϑ_k(ξ) ∈ C ∩ Ω_{k+1} = ξ₀`
  (D, R); `Ω_k = ϑ_k(0) < ξ₀` if `α > 0`.
* (◇D) **The own step `D(k)`, `1 ≤ k < n`, for `ζ ∈ T_{k+1} ∩ Ω_{k+2}`:** (C) `ϑ_k(0) = Ω_k`, `ϑ_k(1 + α) = ω^{idx_ε(Ω_k
  + α)}` (`α < Ω_{k+1}`; W); (V) `ϑ_k(Ω_{k+1}·a + c) = V_k(a, c)` (`1 ≤ a < Ω_{k+1}`, `c < Ω_{k+1}`); (H)
  `ϑ_k(Ω_{k+1}·(Ω_{k+1} + γ) + c) = W_k(γ, c)` (`γ < Ω_{k+2}`, `c < Ω_{k+1}`).  **`VIS(k)`:** for `x ∈ T_{k+1}` and
  strongly critical `v`, `Ω_k < v ≤ Ω_{k+1}`: `P_k(x) ⊆ v ⇔ x ∈ K^{(k)}_v`.  Proof by descending induction on `k`: for
  `k = n − 1`, `T_n ∩ Ω_{n+1} = Ω_n`, only (C) and the first clause of Q occur.  Let `k < n − 1`, `D(j)` known for `k <
  j < n`.  `VIS(k)` by induction on the unique term of `x` (U′; `P_k` is well defined, 3.11 (a), and computed along the
  term by Q): (Q1) `x < Ω_{k+1}`: `P_k(x)` = the additive components, `x ∈ K^{(k)}_v ⇔ x < v` (◇K).  (Q2) `x =NF x₁ +
  x₂`: `x ∈ K ⇔ x₁, x₂ ∈ K` (◇K, components).  (Q3) `x = ϑ_j(η)`, `k < j`, `η ∈ T_{k+1} ⊆ T_{j+1}`, `P_k(x) = P_k(η)`;
  by `D(j)` and ◇K, `x ∈ K ⇔ η ∈ K`: (C) `x = Ω_j` (`η = 0`), or `x = ω^e`, `e = idx_ε(Ω_j + α)`: `x ∈ K ⇔ e ∈ K ⇔ Ω_j +
  α ∈ K ⇔ α ∈ K ⇔ 1 + α ∈ K`; (V) `x = φ(a, y)`, `y = idx_a(c_a + c)`, `a, y < x`: `x ∈ K ⇔ a, y ∈ K ⇔ a, c_a + c ∈ K ⇔
  a, c ∈ K ⇔ η ∈ K` (`c_a ∈ {0, 1, Ω_j} ⊆ K`); (H) `x = Hˡ^{(j)}_γ(y) < Ω_{j+1}` (R), `y = idx_γ(c)` non-fixed: (L1) `x
  ∈ K ⇔ γ, y ∈ K ⇔ γ, c ∈ K ⇔ η ∈ K`; then the i.h. at `η`. `D(k)` by induction on `ζ` (`T_{k+1} ∩ Ω_{k+2}` is an
  ordinal, so the i.h. covers every `ζ' < ζ`).  (◇P) For `ζ = Ω_{k+1}·a + c`, `a =CNF Σ ω^{a_i}·m_i`: `Ω_{k+1}·ω^{a_i} =
  ω^{Ω_{k+1} + a_i} = ϑ_{k+1}(a_i)` (`D(k+1)` (C); `Ω_{k+1} = ϑ_{k+1}(0)`), so `P_k(ζ) = ⋃ comps(a_i) ∪ comps(c)`, and
  `P_k(ζ) ⊆ u ⇔ a, c < u` for an `ε`-number `u`. (V) `v := V_k(a, c)` (an `ε`-number, ◇X).  `≤` by ◇CL (a): `a, c < v`
  (◇X); `ϑ_k(0) = Ω_k < v`; for `ξ = 1 + α' < Ω_{k+1}` with `ξ < v`: `ϑ_k(ξ) = ω^{idx_ε(Ω_k + α')} < v` (X2); for `ξ =
  Ω_{k+1}·a' + c' < ζ` with `a', c' < v`: `(a', c') < (a, c)` lexicographically, `ϑ_k(ξ) = V_k(a', c')` (i.h.) and
  `V_k(a', c') < v` (`a' = a`: `idx_a` and `φ(a, ·)` increase; `a' < a`: `φ(a', v) = v`, `idx_{a'}(c_{a'} + c') < v` by
  X2).  `≥`: if `ξ₀ := ϑ_k(ζ) < v`, ◇CL (b) gives `Ω_k < ξ₀`; `ω^x ≤ ϑ_k(1 + x) < ξ₀` for `Ω_k ≤ x < ξ₀`, so `ξ₀ ∈ E`;
  `a, c < ξ₀` (◇P); for `1 ≤ a' < a`, `c'' < ξ₀`: `V_k(a', c'') = ϑ_k(Ω_{k+1}·a' + c'') < ξ₀` (i.h., ◇CL (b)); a value
  `φ(a', y')` with `y' < ξ₀` is `≤ max(Ω_k, a') < ξ₀`, `= y'`, or `V_k(a', c'')` with `c'' ≤ y'` (X1, X2); so `φ(a', ξ₀)
  = ξ₀` for `a' < a` (normality) and `ξ₀ = φ(a, y₀)` for some `y₀` (`a ≥ 1`), `ξ₀ > max(Ω_k, a)`.  If `y₀` is not fixed,
  `ξ₀ = V_k(a, c₀)`, and `V_k(a, c') < ξ₀` for `c' < c` (i.h., ◇CL (b)) gives `c ≤ c₀`, `v ≤ ξ₀`; if `y₀` is fixed, `ξ₀
  ∈ Fix_a` and `v < φ(a, ξ₀) = ξ₀` (X3).  Contradiction. (H) `v := W_k(γ, c)`, strongly critical, `> Ω_k` (`Ul.ulH_SC`,
  `Ul.ulH_gt`), `c ≤ idx_γ(c) < v` (X2, non-fixed). `≤`: if `v ≥ Ω_{k+1}`, D.  Else ◇CL (a): `γ ∈ K^{(k)}_v` (◇K), `c <
  v`, so `ζ ∈ K^{(k)}_v` (`Uz.uz_parts`) and `P_k(ζ) ⊆ v` (`VIS(k)`); for `ξ < ζ` with `P_k(ξ) ⊆ v`: `ξ < Ω_{k+1}²`
  gives `ϑ_k(ξ) < v` as in (V) (`v` is strongly critical, so closed under `φ`; `a', c' < v` by ◇P, `idx_{a'}(c_{a'} +
  c') < v` by X2); `ξ = Ω_{k+1}·(Ω_{k+1} + γ') + c'` has `γ' ∈ K^{(k)}_v`, `c' < v` (`VIS(k)`, ◇K), `(γ', c') < (γ, c)`
  lexicographically, `ϑ_k(ξ) = W_k(γ', c')` (i.h.) `< v` (`γ' = γ`: `idx_γ`, `Hˡ_γ` increase; `γ' < γ`: `Hˡ_{γ'}(v) = v`
  (`Uc.ucG_fix_lower`) and `idx_{γ'}(c') < v` (X3)).  `≥`: if `ξ₀ := ϑ_k(ζ) < v`: `Ω_k < ξ₀ < Ω_{k+1}` (◇CL (b), R), and
  `ξ₀` is strongly critical (closed under every `φ(a', ·)`, `a' < ξ₀`, as in (V), since `Ω_{k+1}·a' + c'' < Ω_{k+1}² ≤
  ζ`).  `P_k(ζ) ⊆ ξ₀` gives `γ ∈ K^{(k)}_{ξ₀}`, `c < ξ₀` (`VIS(k)`, ◇K).  For `γ' < γ` with `γ' ∈ K^{(k)}_{ξ₀}` and `c'
  < ξ₀`: `ζ' := Ω_{k+1}·(Ω_{k+1} + γ') + c' < ζ` lies in `T_{k+1}`, `P_k(ζ') ⊆ ξ₀` (`VIS(k)`), so `W_k(γ', c') = ϑ_k(ζ')
  < ξ₀` (i.h., ◇CL (b)); every `Hˡ_{γ'}(y')`, `y' < ξ₀`, is `y'` or `W_k(γ', c'')` with `c'' ≤ y'` (X1, X2), hence `<
  ξ₀`, and `Hˡ_{γ'}(ξ₀) = ξ₀` (`Ul.ulH_normal`).  So `ξ₀` is a value of `Hˡ_γ` (`Uc.ucG_range`); the case split of (V)
  with `W_k(γ, c') < ξ₀` (`c' < c`) and X3 contradicts `ξ₀ < v`.
* (◇B) **The bound `Tⁿ₁ ⊆ G`**, along I (`m = 1`): `Ω₁ ⊆ G` (`Uz.uz_G_small`); sums (`Uz.uz_G_add`); `ϑ_k(ξ)`, `1 ≤ k <
  n`, `ξ ∈ T₁ ∩ Ω_{k+2} ∩ G` (`ξ ∈ T_{k+1}`, R), by `D(k)`, with `ξ < θ_k` when `ξ < Ω_{k+1}` (`Uz.uz_G_bound`) and the
  parts of `ξ` in `G` (◇K): (C) `Ω_k ∈ G` (`Uz.uz_G_Om`); `Ω_k + α`, `idx_ε(Ω_k + α) ∈ G` (`Uz.uz_idx_veb` at each
  `θ_i`), `< θ_k` (X2, `θ_k` strongly critical, `Uw.uw_top_q`), and `ω^{idx} = φ(0, idx) ∈ G`, `< θ_k` (`Uz.uz_G_phi`);
  (V) `a, c ∈ G`, `< θ_k`, `idx_a(c_a + c) ∈ G` (`Uz.uz_idx_veb`), `φ(a, idx) ∈ G` (`Uz.uz_G_phi`); (H) `γ, c ∈ G`
  (`Uz.uz_parts`, `Ul.ulK_dec`), `y := idx_γ(c) ∈ K^{(i)}_{θ_i}` for `1 ≤ i < k` (`Uz.uz_idx_H`, `y ≤ c + 1 < Ω_{k+1}`),
  and for `i ≥ k` (`y ≤ c + 1 < θ_k`); `W_k(γ, c) = Hˡ^{(k)}_γ(y) ∈ G` (`Uz.uz_top_hl_ge`, `i₀ = 1 ≤ k`).  Hence `θⁿ₁ =
  Tⁿ₁ ∩ Ω₂ ⊆ θ₁ = ψ_{Ω₂}(Ω_ω)` (S, `Uz.uz_G_bound` at `k = 1`).
* (◇F) **Conclusion.**  `Tᵗ = T₀` (Convention 3.25) `⊆ T₁` by induction on T (`m = 0`): `τ ⊆ Ω₁`; sums; `ϑ₀(ξ) < Ω₁`
  (L); `ϑ_k(ξ)`, `k ≥ 1`, from `ξ ∈ T₁`.  So `η ∈ Tᵗ ∩ Ω₂` gives `η ∈ T₁ ∩ Ω₂ = θ₁ = sup_{n>1} θⁿ₁` (Θ at `m = 1`, T),
  and `θⁿ₁ ≤ ψ_{Ω₂}(Ω_ω)` (◇B): `η < ψ_{Ω₂}(Ω_ω) = ConjT.th S`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

/-- **[W07a] Theorem 3.23 (at `m = 1`), Def 3.22, Def 3.13, Theorem 3.14, the Remark after Corollary 3.15, Def 3.1,
Lemma 3.2 (b), Lemma 3.3, Def 3.4, Lemma 3.5, Def 3.6, Lemma 3.7, Lemma 3.8, Corollary 3.9, Def 3.10, Lemma 3.11 (a)
(b), Convention 3.25, Lemma 3.30** (texts D, M,
B, W, I, R, Q, S, T, Θ, L, and the steps ◇X, ◇K, ◇CL, ◇D, ◇B, ◇F of the module docstring): **every `η ∈ Tᵝ ∩ Ω₂`,
`β` a countable `ε`-number, is below `θ = ψ_{Ω₂}(Ω_ω)`** (`Ui.UiTBound (ConjT.th S)`).

Our steps.  ◇F: `Tᵝ ⊆ T₁`, `T₁ ∩ Ω₂ = θ₁ = sup_n θⁿ₁` (Θ, T); ◇B: `θⁿ₁ = Tⁿ₁ ∩ Ω₂ ⊆ ψ_{Ω₂}(Ω_ω)` for every `n ≥ 2`,
through the own step ◇D (`ϑ_k(1 + α) = ω^{idx_ε(Ω_k + α)}`, `ϑ_k(Ω_{k+1}·a + c) = V_k(a, c)`, `ϑ_k(Ω_{k+1}·(Ω_{k+1} +
γ) + c) = W_k(γ, c)` for every `k ≥ 1`, with `VIS(k)`), whose ψ-facts are the Lean theorems listed in ◇K and ◇B. -/
axiom uzTBound {S : Googology.Notation.InaccPsi.InaccSeq.{0}} :
    Ui.UiTBound (Googology.Notation.InaccPsi.ConjT.th S)

end Googology.Trans.PoR.InaccPsi.R2
