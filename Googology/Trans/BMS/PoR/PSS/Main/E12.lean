import Googology.Trans.BMS.PoR.PSS.Main.E1T
import Googology.Trans.BMS.PoR.PSS.Main.PL

/-!
# E1 and E2 (`proof/PROOF.md` §4.5; `proof/PROOF-2.md` §12.5; `proof/PROOF-3.md` §14.3)

For a standard epsilon root `N = (0, A)` with fold inputs `Y_1, …, Y_n`
(`foldInputs N`) and `α = o(N)`:

* **E1**: `λ_α = α + o(Y_1) + ⋯ + o(Y_n)`.
* **E2** (value form): for the input `Y` after the prefix `pre`, with
  `ξ = α + o(pre)` and `K = lh(κ^α_ξ)`: if `o(Y) > lead(K)`, then `o(Y)` is
  `α`-`≤₁`-minimal.

**E1.**  By Lemma TR, `α` is the value of `a = 𝒯(N) = ϑ_0(Δ + η)`.  [W07b] Theorem 5.3
with the remark after [W07a] Def 7.5 gives `λ_α = val J(Δ) + ζ_α`, where
`J = t^α_τ ∘ ι_{τ,α}` (`lam_eq_jS`, `Main/TIota.lean`), and `E1_T` (`e1T`,
`Main/E1T.lean`, from CI and NS) computes the right side.

**E2** (`proof/PROOF-3.md` §14.3 with M6).  Let `β = o(Y)`, and suppose `α < β' <₁ β`.  By
[W07b] Cor 5.9 (`cor59`, `τ = 1`) the greatest `<₁`-predecessor `γ` of `β` in `(1, β)` is an
intermediate element of the localization of `𝒯(Y)`, and PL (`pl`, `Main/PL.lean`) gives
`γ ≤ K`.  Let `β_0` be the least `δ > α` with `δ ≤₁ γ`; it is `α`-`≤₁`-minimal, so
`β_0 = κ^α_{ξ'}`.  [W07b] Lemma 3.3 (c) gives `κ^α_{ξ+1} = K + 1 > γ ≥ β_0`, so `ξ' ≤ ξ` and
`lh(κ^α_{ξ'}) ≤ K`.  But `β_0 ≤₁ γ ≤₁ β`, so `β ≤ lh(β_0) ≤ K < β`.
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Phi Forest

/-- **E1** (`proof/PROOF-2.md` §12.5): `λ_{o(N)} = o(N) + o(Y_1) + ⋯ + o(Y_n)`. -/
theorem E1 {N : Tm} (hN : Std N) (heps : isEps N = true) :
    lam (ordOf [N]) = ordOf [N] + ((foldInputs N).map fun Y => ordOf [Y]).sum := by
  have hNeq := std_node_y hN
  have hN' : Std (.node 0 N.cs) := by rw [← hNeq]; exact hN
  have he' : isEps (.node 0 N.cs) = true := by rw [← hNeq]; exact heps
  obtain ⟨hne, -, hT⟩ := trTm_root_eps hN' he'
  have hl : (N.cs.getLast hne).y = 0 + 1 := by
    rw [y_of_eps_child hN heps (List.getLast_mem hne)]
  have ha : NFP (trTm N) := trTm_nfp N
  have h0 : (trTm N).lvl = 0 := by rw [hNeq, hT]; rfl
  have hval : (trTm N).val = ordOf [N] := val_trTm_root hN
  have hΔ : argD (trTm N).arg ≠ [] := by
    rw [hNeq, hT, WP.arg_th, (argD_eps hne hl).1]
    exact (deltaOf_spec hne hl).2.2
  have h1 : 1 < (trTm N).val := by rw [hval]; exact one_lt_ordOf_eps hN heps
  have hE : InE (trTm N).val := by rw [hval]; exact eps_ordOf hN heps
  rw [← hval, lam_eq_jS ha h0 hΔ h1 hE, hval]
  exact e1T hN heps

/-- **E2** (`proof/PROOF-3.md` §14.3, in the value form): a fold input above the
leading term of the reach before it is `o(N)`-`≤₁`-minimal. -/
theorem E2 {N : Tm} (hN : Std N) (heps : isEps N = true) (pre : List Tm) (Y : Tm)
    (post : List Tm) (hsplit : foldInputs N = pre ++ Y :: post) (K : Ordinal.{0})
    (hK : IsLh (kap (ordOf [N]) (ordOf [N] + (pre.map fun Y => ordOf [Y]).sum)) K)
    (hY : lead K < ordOf [Y]) : MinT (ordOf [N]) (ordOf [Y]) := by
  set α := ordOf [N] with hα
  have h1 := one_lt_ordOf_eps hN heps
  have hT : α < T1bound := ordOf_lt_T1bound (stdOrd_single hN)
  have hb := bddAbove_minSet hT
  have hYmem : Y ∈ foldInputs N := by rw [hsplit]; simp
  have hYstd : Std Y := std_foldInputs hN heps Y hYmem
  have hYpr : Pr (ordOf [Y]) := pr_ordOf_single hYstd
  set ξ := α + (pre.map fun Y => ordOf [Y]).sum with hξ
  have hξ0 : 0 < ξ := lt_of_lt_of_le (lt_trans zero_lt_one h1) le_self_add
  -- E1: `ξ + o(Y) ≤ λ_α`
  have hle : ξ + ordOf [Y] ≤ lam α := by
    rw [E1 hN heps, hsplit, sum_map_append, ← add_assoc]
    simp only [List.map_cons, List.sum_cons]
    rw [← add_assoc]
    exact le_self_add
  have hξlam : ξ < lam α := lt_of_lt_of_le (lt_add_of_pos_right ξ hYpr.pos) hle
  have hξθ : ξ < theta α := lt_of_lt_of_le hξlam (lam_spec hb).1
  have hKY : K < ordOf [Y] := lt_of_lead_lt hYpr hY
  have hkK : kap α ξ ≤ K := hK.le
  have hξK : ξ ≤ K := le_trans (le_kap α ξ) hkK
  have hαK : α ≤ K := le_trans le_self_add hξK
  refine ⟨le_trans hαK hKY.le, fun β' hβ' hne => ?_⟩
  by_contra hβα
  push Not at hβα
  -- the term of `o(Y)`
  have hYeq := std_node_y hYstd
  set b := trTm Y with hbdef
  have hbv : b.val = ordOf [Y] := val_trTm_root hYstd
  have hbn : NFP b := trTm_nfp Y
  have hb0 : b.lvl = 0 := by rw [hbdef, trTm_lvl, hYeq]; rfl
  have hβ'lt : β' < ordOf [Y] := lt_of_le_of_ne (le1_le hβ') hne
  have hb1 : 1 < b.val := by rw [hbv]; exact lt_trans h1 (lt_trans hβα hβ'lt)
  rcases cor59 hbn hb0 hb1 with ⟨γ, hγ, hγ1, hγne, hγmax⟩ | hmin
  swap
  · exact absurd (hmin.2 β' (hbv ▸ hβ') (hbv ▸ hne)) (not_le.mpr (lt_trans h1 hβα))
  have hβ'γ : β' ≤ γ.val := hγmax β' (lt_trans h1 hβα) (hbv ▸ hβ'lt) (hbv ▸ hβ')
  have hγK : γ.val ≤ K := pl hN heps pre Y post hsplit K hK hY γ hγ
  have hαγ : α < γ.val := lt_of_lt_of_le hβα hβ'γ
  -- `β_0`: the least `δ > α` with `δ ≤₁ γ`
  set S : Set Ordinal.{0} := {δ | α < δ ∧ le1 δ γ.val} with hS
  have hSne : S.Nonempty := ⟨γ.val, hαγ, le1_refl _⟩
  set β0 := sInf S with hβ0
  have hβ0S : β0 ∈ S := csInf_mem hSne
  have hmin0 : MinT α β0 := by
    refine ⟨hβ0S.1.le, fun δ hδ hδne => ?_⟩
    by_contra hδα
    push Not at hδα
    have hδS : δ ∈ S := ⟨hδα, le1_trans hδ hβ0S.2⟩
    have := csInf_le (OrderBot.bddBelow S) hδS
    exact hδne (le_antisymm (le1_le hδ) this)
  obtain ⟨ξ', hξ'θ, hξ'⟩ := exists_kap_eq hb hmin0
  -- `κ^α_{ξ+1} = K + 1`
  obtain ⟨δ, hδ, hall⟩ := kap_add hb hξ0 hξθ
  have hδK : δ = K := hδ.unique hK
  subst hδK
  have hone : (1 : Ordinal.{0}) < nextL δ :=
    lt_of_le_of_lt (le_trans h1.le hαK) (lt_nextL δ)
  obtain ⟨-, hk1, -⟩ := hall 1 zero_lt_one hone
  have hβ0γ : β0 ≤ γ.val := le1_le hβ0S.2
  have hξ'ξ : ξ' ≤ ξ := by
    by_contra hlt
    push Not at hlt
    have hle1 : ξ + 1 ≤ ξ' := Order.add_one_le_iff.mpr hlt
    have := (kap_strictMono α).monotone hle1
    rw [hk1, hξ'] at this
    exact absurd (lt_of_lt_of_le (Order.lt_add_one_iff.mpr (le_trans hβ0γ hγK)) this)
      (lt_irrefl _)
  have hξ'0 : 0 < ξ' := by
    rcases (zero_le (a := ξ')).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, kap_zero hb] at hξ'
      exact absurd hβ0S.1 (by rw [← hξ']; exact lt_irrefl _)
  -- `lh(κ^α_{ξ'}) ≤ K`
  obtain ⟨δ', hδ', hδ'K⟩ : ∃ δ', IsLh (kap α ξ') δ' ∧ δ' ≤ δ := by
    rcases hξ'ξ.lt_or_eq with hlt | heq
    · obtain ⟨δ', hδ', hall'⟩ := kap_add hb hξ'0 (lt_of_lt_of_le hlt hξθ.le)
      have hone' : (1 : Ordinal.{0}) < nextL δ' := by
        have : 1 < δ' := lt_of_lt_of_le (lt_trans h1 hβ0S.1) (hξ' ▸ hδ'.le)
        exact lt_trans this (lt_nextL δ')
      obtain ⟨-, hk1', -⟩ := hall' 1 zero_lt_one hone'
      refine ⟨δ', hδ', ?_⟩
      have hle1 : ξ' + 1 ≤ ξ := Order.add_one_le_iff.mpr hlt
      have := (kap_strictMono α).monotone hle1
      rw [hk1'] at this
      exact le_trans le_self_add (le_trans this hkK)
    · exact ⟨δ, by rw [heq]; exact hδ, le_rfl⟩
  -- `β_0 ≤₁ o(Y)`
  have hβ0Y : le1 β0 (ordOf [Y]) := le1_trans hβ0S.2 (hbv ▸ hγ1)
  rw [← hξ'] at hβ0Y
  have := hδ'.2 _ hβ0Y
  exact absurd (lt_of_le_of_lt (le_trans this hδ'K) hKY) (lt_irrefl _)

end Googology.Trans.PSS.Main
