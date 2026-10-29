import Googology.Trans.PoR.InaccPsi.R2.UlUB
import Googology.Trans.PoR.InaccPsi.R2.Cited

set_option autoImplicit false

/-!
# The base change `π_{σ,τ}` on the `ϑ_s`-terms of `[Ω_s, θ_s)` for every finite `s ≥ 2`: one citation, generic in `s`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

This file cites ONE thing, the base change of [W07a] §5 on the terms `ϑ_s(η)`, `s ≥ 2`, read through the ψ-side
dictionary `D(s)`.  The case `s = 1` on `[B₂, θ)` is `R2.CitedVd` (`vdAtom_TB`, `vdPhi_TB`, `vdOpow_TB`), which is not
restated here; the axioms below have `1 < s`.  Conventions as in `R2.CitedVd`, `R2.CitedUz` (`Ω_i = Om i`, `Tset τ =
Tᵗ`, `Par τ = Parᵗ`, `pi σ τ = π_{σ,τ}`, `TB τ σ = Tᵗ[σ]`, bases `σ < τ` countable `ε`-numbers, `φ(a, c) = veblen a c`).
ψ-side (all Lean, `R2.UlUB`, `R2.UiUB`): `W = Ω_{s+1}`, `V = Ω_{s+2}`, `θ_s := ψ_W(Ω_ω) = S.psi (Om ω) (Om (s + 1))`,
`K⁽ⁱ⁾_q := Ul.UlK S i q`, `Hˡ⁽ˢ⁾_γ := Ul.ulH S s γ` (the lifted hierarchy at `W`, every level `γ < V`).

Literal texts (word for word from [W07a]; the extraction drops sub- and superscripts, restored here).
* (D) Def 3.1: "… `ϑⁿ_m(α) := min({ξ < Ω_{m+1} | Cⁿ_m(α, ξ) ∩ Ω_{m+1} ⊆ ξ ∧ α ∈ Cⁿ_m(α, ξ)} ∪ {Ω_{m+1}})`.  Note that
  we have `ϑⁿ_m(0) = Ω_m` for `m < n`."
* (T) Def 3.22: "… We define a function `ϑ_m : θ_{m+1} → Ω_{m+1}` by `ϑ_m(α) := ϑⁿ_m(α)` for `α < θ_{m+1}` where `n > m`
  is large enough to satisfy `α < θⁿ_{m+1}`.  `T_m` is defined inductively as follows: • `Ω_m ⊆ T_m` • `ξ, η ∈ T_m ⇒
  ξ + η ∈ T_m` • `ξ ∈ T_m ∩ Ω_{k+2} ⇒ ϑ_k(ξ) ∈ T_m` for `k ≥ m`."
* (C) Corollary 3.24: "For every `k ≥ m` we have `sup(T_m ∩ Ω_{k+2}) = θ_{k+1}`.  For `m < n` we have `Tⁿ_m ∩ Ω_{m+1}
  = θⁿ_m = ϑ_m(⋯(ϑ_n(0))⋯)`."
* (S) Def 3.28: "• `Subᵗ_m(α) := {α}` for parameters `α < τ` • `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ) ∪ Subᵗ_m(η)` for `ξ, η
  ∈ Tᵗ` s.t. `α =NF ξ + η > τ` • `Subᵗ_m(α) := {α} ∪ Subᵗ_m(ξ)` if `k ≥ m`, `{α}` if `k < m`, for `α = ϑ_k(ξ)` where
  `ξ ∈ Tᵗ ∩ Ω_{k+2}`. … The set of parameters `< τ` used in the unique term denoting some `α ∈ Tᵗ` is denoted by
  `Parᵗ(α) := Subᵗ_0(α) ∩ τ`."
* (L) Lemma 3.30: "For `m < ω` the function `ϑ_m ↾ Tᵗ ∩ Ω_{m+2}` is 1-1 and has values in `P ∩ [Ω_m, Ω_{m+1})`.  Let
  `α, γ ∈ Tᵗ ∩ Ω_{m+2}`.  Then `α^{*m} < ϑ_m(α)` and `ϑ_m(α) < ϑ_m(γ) ⇔ α < γ ∧ α^{*m} < ϑ_m(γ) ∨ ϑ_m(α) ≤ γ^{*m}`."
* (W) Def 3.4: "Let `α ↦ ω̄_α` be the enumeration function of the additive principle numbers which are not epsilon
  numbers."  Lemma 4.2: "For any `m < ω` and any `α < Ω_{m+1}` we have `ϑ_m(1 + α) = ω̄_{Ω_m+α}`."
* (P) Def 5.1: "Let `τ ∈ E` and `Tᵗ` be the notation system over `τ`.  Further, let `σ ∈ {1} ∪ (E ∩ τ)`.  We define
  `Tᵗ[σ] := {α ∈ Tᵗ | Parᵗ(α) ⊆ σ}` and `π_{σ,τ} : Tᵗ[σ] → T^σ` by the following clauses: • `π_{σ,τ}(ξ) := ξ` if `ξ <
  σ` • `π_{σ,τ}(ξ) := π_{σ,τ}(ξ₁) + π_{σ,τ}(ξ₂)` if `ξ =NF ξ₁ + ξ₂ > τ` • `π_{σ,τ}(ξ) := ϑ_k(π_{σ,τ}(η))` if `ξ =
  ϑ_k(η)` for some `k > 0` and `η ∈ Tᵗ[σ] ∩ Ω_{k+2}` • `π_{σ,τ}(ξ) := ϑ^σ(π_{σ,τ}(η))` if `ξ = ϑ^τ(η)` for some `η ∈
  Tᵗ[σ] ∩ Ω₂`."
* (Π) Lemma 5.3: "Let `σ, τ` be as in the above definition.  Then we have (a) For `m < ω` and `ξ ∈ Tᵗ[σ]` we have
  `P^σ_m(π_{σ,τ}(ξ)) = π_{σ,τ}[Pᵗ_m(ξ)]` and `Sub^σ_m(π_{σ,τ}(ξ)) = π_{σ,τ}[Subᵗ_m(ξ)]`.  (b) `π_{σ,τ}` preserves `<`.
  (c) `π_{σ,τ}` preserves ordinal addition.  (d) `π_{σ,τ}` maps `Tᵗ[σ]` onto `T^σ`.  (e) `htᵗ(α) = ht^σ(π_{σ,τ}(α))`
  and `Parᵗ(α) = Par^σ(π_{σ,τ}(α))` for `α ∈ Tᵗ[σ]`."
Nothing is taken from a proof: in particular "`π_{σ,τ}` maps `Tᵗ[σ] ∩ [Ω_k, Ω_{k+1})` into `T^σ ∩ [Ω_k, Ω_{k+1})`",
which [W07a] states only inside the proof of Lemma 5.3, is not cited; it is the Lean theorem `Vs.vs_pi_lt_Om` (from
`vsOm_TB` at `k` and `k + 1` and Π (b), i.e. `R2.pi_bijOn`).  Def 6.2 is not used.

Our steps (`D(s)`, the dictionary ψ ↔ `ϑ_s` on `[Ω_s, θ_s)`, `s ≥ 2` finite).  They are the steps ◇θ, ◇Ω₂, ◇F‴, ◇π‴,
◇π3‴, ◇S of `R2.CitedVd` Part II with `Ω₂, Ω₃, ϑ₁, ϑ₂, K⁽¹⁾, Hˡ` replaced by `Ω_{s+1}, Ω_{s+2}, ϑ_s, ϑ_{s+1}, K⁽ˢ⁾,
Hˡ⁽ˢ⁾`, written out below.  They use the steps ◇X (indices `idx_f`, `c_a`, `V_k`, `W_k`), ◇K (the ψ-facts, Lean),
◇CL, ◇D of `R2.CitedUz` as written there for every `k ≥ 1`, i.e. `D(k)`: (C) `ϑ_k(0) = Ω_k`, `ϑ_k(1 + α) =
ω^{idx_ε(Ω_k + α)}`; (V) `ϑ_k(Ω_{k+1}·a + c) = V_k(a, c) = φ(a, idx_a(c_a + c))` (`1 ≤ a < Ω_{k+1}`, `c < Ω_{k+1}`);
(H) `ϑ_k(Ω_{k+1}·(Ω_{k+1} + γ) + c) = W_k(γ, c) = Hˡ⁽ᵏ⁾_γ(idx_γ(c))` (`γ < Ω_{k+2}`, `c < Ω_{k+1}`), and `VIS(k)`:
`P_k(x) ⊆ v ⇔ x ∈ K⁽ᵏ⁾_v` for strongly critical `v ∈ (Ω_k, Ω_{k+1}]`.  Fix `s ≥ 2`, `ϑ_j := ϑⁿ_j`, `T_m := Tⁿ_m`
for `n` large.
* (◇Ω_s) **`Ω_s` itself.**  `Ω_s = ϑ_s(0)` (D); `0 ∈ Tᵗ` (`Ω₀ = τ ⊆ T₀`, T), so `ϑ_s(0) ∈ Tᵗ` (T, third clause,
  `k = s ≥ 0`); `Subᵗ₀(ϑ_s(0)) = {ϑ_s(0)} ∪ Subᵗ₀(0) = {Ω_s, 0}` (S, `k = s ≥ 0`; `0 < τ` a parameter), so `Parᵗ(Ω_s) =
  {0} ⊆ σ` (`σ ∈ E`, `0 < σ`) and `Ω_s ∈ Tᵗ[σ]` (P).  `π(0) = 0` (P, first clause, `0 < σ`) and `π(Ω_s) = ϑ_s(π(0)) =
  ϑ_s(0) = Ω_s` (P, third clause, `k = s > 0`, `0 ∈ Tᵗ[σ] ∩ Ω_{s+2}`).
* (◇θ_s) **`θ_s = T_s ∩ Ω_{s+1}`, every ordinal below `θ_s` is in some `Tⁿ_s`.**  `≤`: ◇B, ◇F of `R2.CitedUz` with
  `i₀ = s` in place of `1`: `Tⁿ_s ⊆ G_s` along I at `m = s` (`Ω_s ⊆ G_s` by `Uz.uz_G_small`; sums by `Uz.uz_G_add`;
  `ϑ_k(ξ)`, `k ≥ s`, by `D(k)` and `Uz.uz_top_hl_ge` with `i₀ = s ≤ k`), then `Uz.uz_G_bound` at `k = s`
  (`G_s ∩ Ω_{s+1} ⊆ θ_s`, Lean).  (Note: `Tⁿ_s ⊆ Tⁿ₁` is false; [W07a] Cor 3.9 gives `Tⁿ₁ ⊆ Tⁿ_s`.)
  `≥`: `θ_s = sup_n ψ_W(E_n)`, `E_n = ε_{Ω_n+1}` (`Us.us_top_sup`, Lean, every `s`), and `ψ_W(E_n) ∈ T_s` by the chain
  `ψ_{Ω_n}(E_n) = Hˡ⁽ⁿ⁻¹⁾_{E_n}(0)` (`Us.us_top_E`), `ψ_{Ω_{k+1}}(E_n) = Hˡ⁽ᵏ⁾_{ψ_{Ω_{k+2}}(E_n)}(0)` (`Us.us_step_E`) for
  `k = n − 2, …, s` and `D(k)` (H) (`0` is not fixed), `E_n = V_n(1, 0) = ϑ_n(Ω_{n+1})` (`D(n)` (V)); every argument is
  built by `+` and `ϑ_j` from `ϑ_j(0) = Ω_j` (T).  So `θ_s` (ψ-side) is Wilken's `θ_s` (C, `m = k = s`).
* (◇Ω_{s+1}) **The factor `Ω_{s+1}`.**  For `x ∈ Tᵗ ∩ Ω_{s+2}`: `Ω_{s+1}·x ∈ Tᵗ ⇔ x ∈ Tᵗ`, `Parᵗ(Ω_{s+1}·x) ∪ ω =
  Parᵗ(x) ∪ ω`, and for `x ∈ Tᵗ[σ]`: `π(Ω_{s+1}·x) = Ω_{s+1}·π(x)`.  `Ω_{s+1}·x = Σ ω^{Ω_{s+1} + x_i}·k_i` over the
  Cantor terms `ω^{x_i}·k_i` of `x`; `ω^{Ω_{s+1} + x_i} = ϑ_{s+1}(1 + α_i)` with `idx_ε(Ω_{s+1} + α_i) = Ω_{s+1} + x_i`
  (`D(s+1)` (C), ◇X) when `x_i` is not an `ε`-number above `Ω_{s+1}`; if it is, `ω^{Ω_{s+1} + x_i} = x_i`, the summand
  is `x_i·k_i` with the parameters of `x_i`, and `π(x_i)` is again an `ε`-number `> Ω_{s+1}` (◇π_s, ◇π3_s below at
  `s + 1`, Π (b), ◇Ω_s at `s + 1`), so `Ω_{s+1}·π(x_i) = π(x_i)`; `Ω_{s+1} = ϑ_{s+1}(0)`; S and P (third clause, `k =
  s + 1 > 0`), Π (c), and `π(idx_ε(w)) = idx_ε(π w)` (`π` keeps `+`, `<`, maps the `ε`-numbers of `Tᵗ[σ]` (the values of
  the forms (V), (H) and the `Ω_j`) to `ε`-numbers, and is onto `T^σ`, Π (d)).
* (◇F_s) **Fixed points.**  For `λ ∈ Tᵗ ∩ Ω_{s+2}`, `y ∈ Tᵗ ∩ Ω_{s+1}` with `p := max(Fix_λ ∩ (y + 1))` existing
  (`Fix_λ` the fixed points of `Hˡ⁽ˢ⁾_λ`, a closed class): `p ∈ Tᵗ`, `Parᵗ(p) ⊆ Parᵗ(y) ∪ ω`.  By induction on `y`: `p`
  is strongly critical, so `p ≤ lead(y)`, an additive component of `y` (S).  If `lead(y) ∈ Fix_λ`, `p = lead(y)`.  If
  `lead(y)` is not strongly critical (`ω^g`, `g` not an `ε`-number, or `φ(a, c)`, `a, c < φ(a, c)`), then `p ≤ g`,
  resp. `p ≤ max(a, c)` (`p` is strongly critical, closed under `ω^·`, `φ`), and the i.h. at that part of `y`.  If
  `lead(y) = Hˡ⁽ˢ⁾_{λ₂}(y₂)` (normal form) is not in `Fix_λ`: if `λ₂ ∉ K⁽ˢ⁾_p`, `VIS(s)` gives `x ∈ P_s(λ₂)` with `p ≤
  x`, and `x < lead(y)` (`λ₂ ∈ K⁽ˢ⁾_{lead(y)}`, `Ul.ulH_D_lt`), `x` a part of `y` (S along the term `ϑ_s(Ω_{s+1}·
  (Ω_{s+1} + λ₂) + c₂)` of `D(s)` (H)), so `p = max(Fix_λ ∩ (x + 1))` and the i.h. at `x`; otherwise `λ₂ ∈ K⁽ˢ⁾_p`, and
  `λ₂ > λ` would put `lead(y)` in `Fix_λ` (`Uc.ucG_fix_lower`: `λ ∈ K⁽ˢ⁾_p ⊆ K⁽ˢ⁾_{lead(y)}`), so `λ₂ ≤ λ`, `p ∈
  Fix_{λ₂}`, `p < Hˡ⁽ˢ⁾_{λ₂}(y₂)` gives `p ≤ y₂`, a part of `y` (◇X: `y₂`, `c₂` have the same parameters up to finite
  ones): i.h.
* (◇π_s) **Atoms** (`Bases σ τ`): a strongly critical `z ∈ (Ω_s, θ_s)` with `z = Hˡ⁽ˢ⁾_λ(y)`, `λ < Ω_{s+2}`, `y < z`
  (then `λ` is the level of the normal form `Vp.vpLev`: `λ ∈ K⁽ˢ⁾_z`, `Ul.ulH_D_lt`, and a smaller visible level
  would fix `z`).  By ◇θ_s and `D(s)` (H), L (`m = s`, injectivity): `z = ϑ_s(ζ)`, `ζ = Ω_{s+1}·(Ω_{s+1} + λ) + c`, `c`
  the index of `y` (◇X: `y = p + 1 + (c − p)` with `p = max(Fix_λ ∩ (y + 1))`, or `y = c`).  `z ∈ Tᵗ ⇔ ζ ∈ Tᵗ` (T, L)
  with `Parᵗ(z) = Parᵗ(ζ)` (S, `k = s ≥ 0`); `ζ ∈ Tᵗ[σ] ⇔ λ, c ∈ Tᵗ[σ]` (◇Ω_{s+1}, Π (c), and `Ω_{s+1} ∈ Tᵗ[σ]`,
  ◇Ω_s at `s + 1`), and `c ∈ Tᵗ[σ] ⇔ y ∈ Tᵗ[σ]` (◇F_s).  So `z ∈ Tᵗ[σ] ⇔ λ, y ∈ Tᵗ[σ]`.  Then `π(z) = ϑ_s(π ζ)` (P,
  third clause, `k = s > 0`) `= ϑ_s(Ω_{s+1}·(Ω_{s+1} + π λ) + π c)` (◇Ω_{s+1}, Π (c), ◇Ω_s) `= W_s(π λ, π c)` (`D(s)`
  (H) over `σ`; `ϑ_s` does not depend on the base, D) `= Hˡ⁽ˢ⁾_{π λ}(π y)`: `π p ∈ Fix_{π λ}` (`p` is a value
  `W_s(λ'', c'')` with `λ < λ''`, `λ ∈ K⁽ˢ⁾_p`, or a supremum of such, and `π` keeps `<` and `VIS(s)` over `σ`, Π (a)),
  no fixed point of `Hˡ⁽ˢ⁾_{π λ}` lies in `(π p, π y]` (it would be `π q'`, Π (d), with `q' ∈ Fix_λ ∩ (p, y]` by the
  same argument backwards), and `π(p + 1 + d) = π p + 1 + π d` (Π (c)): the index of `π y` is `π c`.
* (◇π3_s) **`ω^g` and `φ(a, c)`** below `θ_s`, by induction on the ordinal, with the atoms read by ◇π_s.  (π2) `Ω_s ≤
  g`, `g` not an `ε`-number (so `ω^g` is additive principal, not an `ε`-number, `> Ω_s`): `ω^g = ω̄_{Ω_s + α} = ϑ_s(1 +
  α)` with `idx_ε(Ω_s + α) = g` (W, `m = s`; ◇X), so `ω^g ∈ Tᵗ ⇔ α ∈ Tᵗ ⇔ g ∈ Tᵗ` with the same parameters up to finite
  ones (T, S; `g = p + 1 + (Ω_s + α − p)` or `g = Ω_s + α`, `p` the largest `ε`-number `≤ Ω_s + α`, in `Tᵗ` with
  parameters within those of `α` as in ◇F_s with `f = ω^·`), and `π(ω^g) = ϑ_s(1 + π α)` (P, third clause; Π (c)) `=
  ω̄_{Ω_s + π α} = ω^{idx_ε(Ω_s + π α)} = ω^{π g}` (`π(idx_ε w) = idx_ε(π w)` as in ◇Ω_{s+1}, `π(Ω_s) = Ω_s`, ◇Ω_s).
  (π3) `φ(a, c)` with `1 ≤ a`, `a, c < φ(a, c)`, `Ω_s < φ(a, c) < θ_s`: `c` is not a fixed point of `φ(a, ·)`, and
  `φ(a, c) > max(Ω_s, a)`, so `c = idx_a(c_a + c')` for a unique `c' < Ω_{s+1}` (◇X: `idx_a` enumerates the non-fixed
  ordinals, `c_a` of them have values `≤ max(Ω_s, a)`), and `φ(a, c) = V_s(a, c') = ϑ_s(Ω_{s+1}·a + c')` (`D(s)` (V)).
  Then `φ(a, c) ∈ Tᵗ[σ] ⇔ a, c' ∈ Tᵗ[σ] ⇔ a, c ∈ Tᵗ[σ]` (T, S, ◇Ω_{s+1}; `c` and `c'` have the same parameters up to
  finite ones, ◇F_s with `f = φ(a, ·)`, `c_a ∈ {0, 1, Ω_s}`), and `π(φ(a, c)) = ϑ_s(Ω_{s+1}·π a + π c')` (P, ◇Ω_{s+1},
  Π (c)) `= V_s(π a, π c') = φ(π a, idx_{π a}(c_{π a} + π c'))`, where `c_{π a} = c_a` (`π a < Ω_s ⇔ a < Ω_s`, `π a =
  Ω_s ⇔ a = Ω_s` by Π (b) and ◇Ω_s; `π a` strongly critical `> Ω_s` iff `a` is: the strongly critical ordinals of
  `Tᵗ ∩ (Ω_s, Ω_{s+1})` are the values (H) of `D(s)`, the others are `ω^g` or `φ(a', c'')` in normal form, and `π`
  keeps each form by ◇π_s, (π2) and the i.h.) and `idx_{π a}(c_a + π c') = π(idx_a(c_a + c')) = π c` (the fixed point
  `p` of `φ(a, ·)` below `c` goes to a fixed point of `φ(π a, ·)` by the i.h. at `p < φ(a, c)`, and none lies in `(π p,
  π c]` by Π (d) backwards).  So `π(φ(a, c)) = φ(π a, π c)`.
* (◇S_s) **The readings do not depend on `S`.**  `θ_s` is Wilken's (◇θ_s); the normal form `z = Hˡ⁽ˢ⁾_λ(y) =
  W_s(λ, c) = ϑ_s(Ω_{s+1}·(Ω_{s+1} + λ) + c)` has a unique argument (L, `m = s`), so `λ`, `y` are `S`-free; `ω^g`,
  `φ(a, c)` mention no `S`.  So each axiom below, stated for every `S`, is one statement about [W07a]'s terms.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Googology.Notation.InaccPsi

/-- **[W07a] Def 3.1 (`ϑⁿ_m(0) = Ω_m`), Def 3.22, Def 3.28, Def 5.1 (first and third clauses)** (texts D, T, S, P, and
the step ◇Ω_s): for bases `σ < τ` and finite `s ≥ 2`: `Ω_s ∈ Tᵗ[σ]` and `π_{σ,τ}(Ω_s) = Ω_s`. -/
axiom vsOm_TB {σ τ s : Ordinal.{0}} (h : Bases σ τ) (hs : s < ω) (hs1 : 1 < s) :
    Om s ∈ TB τ σ ∧ pi σ τ (Om s) = Om s

/-- **[W07a] Def 5.1 (first three clauses), Lemma 5.3 (a)–(d), Def 3.1, Def 3.22, Corollary 3.24, Def 3.28, Lemma
3.30, Lemma 4.2** (texts D, T, C, S, L, W, P, Π, and the steps ◇θ_s, ◇Ω_s, ◇Ω_{s+1}, ◇F_s, ◇π_s, ◇S_s with `D(s)`,
`D(s+1)`, `VIS(s)` of `R2.CitedUz`): for bases `σ < τ`, finite `s ≥ 2`, and an atom `z = Hˡ⁽ˢ⁾_γ(y)` (`γ < Ω_{s+2}`,
`y < z`) below `θ_s = ψ_{Ω_{s+1}}(Ω_ω)`: `z ∈ Tᵗ[σ] ⇔ γ, y ∈ Tᵗ[σ]`, and then `π_{σ,τ}(z) = Hˡ⁽ˢ⁾_{π γ}(π y)`. -/
axiom vsAtom_TB {S : InaccSeq.{0}} {σ τ s γ y : Ordinal.{0}} (h : Bases σ τ) (hs : s < ω) (hs1 : 1 < s)
    (hγ : γ < Om (s + 1 + 1)) (hy : y < Ul.ulH S s γ y) (hz : Ul.ulH S s γ y < S.psi (Om ω) (Om (s + 1))) :
    (Ul.ulH S s γ y ∈ TB τ σ ↔ γ ∈ TB τ σ ∧ y ∈ TB τ σ) ∧
      (γ ∈ TB τ σ → y ∈ TB τ σ → pi σ τ (Ul.ulH S s γ y) = Ul.ulH S s (pi σ τ γ) (pi σ τ y))

/-- **[W07a] Def 5.1 (first three clauses), Lemma 5.3 (a)–(d), Def 3.22, Corollary 3.24, Def 3.28, Lemma 3.30** (texts
T, C, S, L, P, Π, and the steps ◇θ_s, ◇Ω_s, ◇Ω_{s+1}, ◇F_s, ◇π3_s (π3) with `D(s)` (V)): for bases `σ < τ`, finite
`s ≥ 2`, and an `ε`-number `φ(a, c) ∈ (Ω_s, θ_s)` in normal form (`1 ≤ a`, `a, c < φ(a, c)`): `φ(a, c) ∈ Tᵗ[σ] ⇔ a, c ∈
Tᵗ[σ]`, and then `π_{σ,τ}(φ(a, c)) = φ(π a, π c)`. -/
axiom vsPhi_TB {S : InaccSeq.{0}} {σ τ s a c : Ordinal.{0}} (h : Bases σ τ) (hs : s < ω) (hs1 : 1 < s)
    (ha : 1 ≤ a) (haz : a < veblen a c) (hcz : c < veblen a c) (h1 : Om s < veblen a c)
    (hz : veblen a c < S.psi (Om ω) (Om (s + 1))) :
    (veblen a c ∈ TB τ σ ↔ a ∈ TB τ σ ∧ c ∈ TB τ σ) ∧
      (a ∈ TB τ σ → c ∈ TB τ σ → pi σ τ (veblen a c) = veblen (pi σ τ a) (pi σ τ c))

/-- **[W07a] Def 5.1 (first three clauses), Lemma 5.3 (b)–(d), Def 3.4, Lemma 4.2, Def 3.22, Corollary 3.24, Def 3.28,
Lemma 3.30** (texts W, T, C, S, L, P, Π, and the steps ◇θ_s, ◇Ω_s, ◇π3_s (π2) with `D(s)` (C)): for bases `σ < τ`,
finite `s ≥ 2`, and `g ≥ Ω_s`, not an `ε`-number, with `ω^g < θ_s`: `ω^g ∈ Tᵗ[σ] ⇔ g ∈ Tᵗ[σ]`, and then
`π_{σ,τ}(ω^g) = ω^{π g}`. -/
axiom vsOpow_TB {S : InaccSeq.{0}} {σ τ s g : Ordinal.{0}} (h : Bases σ τ) (hs : s < ω) (hs1 : 1 < s)
    (hg : Om s ≤ g) (hgE : ω ^ g ≠ g) (hz : ω ^ g < S.psi (Om ω) (Om (s + 1))) :
    (ω ^ g ∈ TB τ σ ↔ g ∈ TB τ σ) ∧ (g ∈ TB τ σ → pi σ τ (ω ^ g) = ω ^ pi σ τ g)

end Googology.Trans.PoR.InaccPsi.R2
