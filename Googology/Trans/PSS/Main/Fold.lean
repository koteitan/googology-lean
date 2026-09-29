import Googology.Trans.PSS.Main.Nodes

/-!
# Lemma F and the fold of an epsilon root (`proof/PROOF.md` §4.4, §4.5)

Fix an epsilon number `α ∈ (1, T¹ ∩ Ω_1)`, and write `K(ξ) := lh(κ^α_ξ)`.

**Lemma F** ([W07b] Lemmas 3.3, 3.4 and Theorem 2.2):

* (F1) `α ≤ λ_α` and `K(α) = α · 2` (`lemmaF1`);
* (F2a) for `0 < ξ < λ_α` and `Y ∈ P` with `Y ≤ lead(K(ξ))`:
  `K(ξ + Y) = K(ξ) + Y` (`lemmaF2a`);
* (F2b) for `0 < ξ < λ_α` and `Y ∈ P` with `Y > lead(K(ξ))` that is
  `α`-`≤₁`-minimal: `ξ + Y = Y` and `κ^α_Y = Y`, so `K(ξ + Y) = lh(Y)`
  (`lemmaF2b`);
* (F3) `lh(α) = K(λ_α)` (`lemmaF3`).

**Prop 4.3** (`fold_isLh`): if the fold inputs `Y_1, …, Y_n` of an epsilon root
`N` satisfy E1 (`λ_α = α + o(Y_1) + ⋯ + o(Y_n)`) and E2 (a jump input is
`α`-`≤₁`-minimal), and the reach `F(Y)` of every input `Y > N` is right, then the
fold `S_n = (N, N) ⊕ Y_1 ⊕ ⋯ ⊕ Y_n` has `o(S_n) = lh(o(N))`.  The proof carries
`K(ξ_j) = o(S_j)` along the fold, with `ξ_j = α + o(Y_1) + ⋯ + o(Y_j)`.

E2 is stated in the value form of `proof/PROOF-3.md` §14.3: for the input `Y`
after the prefix `pre`, with `ξ = α + o(pre)` and `K = K(ξ)`, if
`o(Y) > lead(K)` then `o(Y)` is `α`-`≤₁`-minimal.  (In the fold,
`K = o(S_{j-1})`, and `o(Y) > lead(K)` is the jump condition `Y > S_{j-1,1}`.)
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Order Phi Forest

set_option linter.unusedSectionVars false

section LemmaF

variable {α : Ordinal.{0}} (hE : InE α) (h1 : 1 < α) (hT : α < T1bound)
include hE h1 hT

theorem logend_eps : logend α = α := by
  have := logend_add_opow (β := 0) (γ := α) (dvd_zero _)
  rwa [zero_add, hE] at this

/-- **(F1)** `κ^α_α = α · 2 = lh(κ^α_α)` and `α ≤ λ_α`. -/
theorem lemmaF1 : kap α α = α + α ∧ IsLh (α + α) (α + α) ∧ α ≤ lam α := by
  have hb := bddAbove_minSet hT
  have hα0 : 0 < α := lt_trans zero_lt_one h1
  obtain ⟨hmin, heq, hlh⟩ := kap_small hb hα0 (lt_nextL α)
  refine ⟨heq, hlh, le_lam (le_theta_of_minT hb hmin) ?_⟩
  rw [heq]
  exact (le1_add_iff hα0 le_rfl).mpr ⟨α, hE.symm, by rw [logend_eps hE h1 hT]⟩

/-- **(F2a)** -/
theorem lemmaF2a {ξ δ Y : Ordinal.{0}} (hξ0 : 0 < ξ) (hξ : ξ < lam α)
    (hK : IsLh (kap α ξ) δ) (hY : Pr Y) (hYl : Y ≤ lead δ) :
    MinT α (kap α (ξ + Y)) ∧ IsLh (kap α (ξ + Y)) (δ + Y) := by
  have hb := bddAbove_minSet hT
  have hξθ : ξ < theta α := lt_of_lt_of_le hξ (lam_spec hb).1
  obtain ⟨δ', hδ', hall⟩ := kap_add hb hξ0 hξθ
  have e : δ' = δ := hδ'.unique hK
  subst e
  have hδ0 : δ' ≠ 0 := by
    have : 0 < δ' := lt_of_lt_of_le (lt_of_lt_of_le hξ0 (le_kap α ξ)) hK.le
    exact this.ne'
  have hYlt : Y < nextL δ' := lt_of_le_of_lt (le_trans hYl (lead_le hδ0)) (lt_nextL δ')
  obtain ⟨hm, heq, hlh⟩ := hall Y hY.pos hYlt
  exact ⟨hm, heq ▸ hlh⟩

/-- **(F2b)** -/
theorem lemmaF2b {ξ δ Y : Ordinal.{0}} (hξ0 : 0 < ξ) (hK : IsLh (kap α ξ) δ) (hY : Pr Y)
    (hYl : lead δ < Y) (hmin : MinT α Y) : ξ + Y = Y ∧ kap α Y = Y ∧ Y ≤ theta α := by
  have hb := bddAbove_minSet hT
  have hδY : δ < Y := lt_of_lead_lt hY hYl
  have hξY : ξ < Y := lt_of_le_of_lt (le_trans (le_kap α ξ) hK.le) hδY
  obtain ⟨ζ, hζθ, hζ⟩ := exists_kap_eq hb hmin
  have hζ0 : 0 < ζ := by
    rcases (zero_le (a := ζ)).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, kap_zero hb] at hζ
      have : kap α 0 < kap α ξ := kap_strictMono α hξ0
      rw [kap_zero hb] at this
      exact absurd (lt_trans this (lt_of_le_of_lt hK.le hδY)) (by rw [hζ]; exact lt_irrefl _)
  have hkp := kap_principal hb hζ0 hζθ (hζ ▸ hY)
  rw [hζ] at hkp
  subst hkp
  exact ⟨hY.add_eq hξY, hζ, hζθ⟩

/-- **(F3)** `lh(α) = K(λ_α)`. -/
theorem lemmaF3 {δ : Ordinal.{0}} (hK : IsLh (kap α (lam α)) δ) : IsLh α δ :=
  ((lam_spec (bddAbove_minSet hT)).2.2 δ).mpr hK

end LemmaF

/-! ## Prop 4.3: the fold -/

theorem eps_ordOf {N : Tm} (hN : Std N) (heps : isEps N = true) : InE (ordOf [N]) := by
  unfold InE
  have := lemmaR_eps hN heps
  rw [ordOf_single]; exact this.symm

theorem one_lt_ordOf_eps {N : Tm} (hN : Std N) (heps : isEps N = true) : 1 < ordOf [N] := by
  have he := eps_ordOf hN heps
  by_contra h
  push Not at h
  rcases h.lt_or_eq with h | h
  · rw [Order.lt_one_iff.mp h] at he; simp [InE] at he
  · rw [h] at he; simp [InE] at he; exact absurd he (ne_of_gt one_lt_omega0)


section Fold

/-- The invariant of the fold after the prefix `pre`: `S = S_j` is a node whose
first term is at least `N`, and `K(ξ_j) = o(S_j)`. -/
def FoldInv (N : Tm) (pre : List Tm) (S : List Tm) : Prop :=
  StdOrd S ∧ (∃ s1 S', S = s1 :: S' ∧ N ≤ s1) ∧
    IsLh (kap (ordOf [N]) (ordOf [N] + (pre.map fun Y => ordOf [Y]).sum)) (ordOf S)

theorem sum_map_append (l l' : List Tm) :
    ((l ++ l').map fun Y => ordOf [Y]).sum =
      (l.map fun Y => ordOf [Y]).sum + (l'.map fun Y => ordOf [Y]).sum := by
  rw [List.map_append, List.sum_append]

variable {N : Tm} (hN : Std N) (heps : isEps N = true) (F : Tm → List Tm)
  (hFstd : ∀ Y, Std Y → StdOrd (F Y)) (hFne : ∀ Y, F Y ≠ [])
  (hFhead : ∀ Y, ∀ s ∈ (F Y).head?, Y ≤ s)
  (hFL : ∀ Y ∈ foldInputs N, N < Y → IsLh (ordOf [Y]) (ordOf (F Y)))
  (hE1 : lam (ordOf [N]) = ordOf [N] + ((foldInputs N).map fun Y => ordOf [Y]).sum)
  (hE2 : ∀ pre Y post, foldInputs N = pre ++ Y :: post → ∀ K,
    IsLh (kap (ordOf [N]) (ordOf [N] + (pre.map fun Y => ordOf [Y]).sum)) K →
      lead K < ordOf [Y] → MinT (ordOf [N]) (ordOf [Y]))
include hN heps hFstd hFne hFhead hFL hE1 hE2

/-- One step of the fold keeps the invariant. -/
theorem foldInv_step (pre : List Tm) (Y : Tm) (post : List Tm)
    (hsplit : foldInputs N = pre ++ Y :: post) {S : List Tm} (hS : FoldInv N pre S) :
    FoldInv N (pre ++ [Y]) (oplus F S Y) := by
  set α := ordOf [N] with hα
  have hE := eps_ordOf hN heps
  have h1 := one_lt_ordOf_eps hN heps
  have hT : α < T1bound := ordOf_lt_T1bound (stdOrd_single hN)
  obtain ⟨hSstd, ⟨s1, S', rfl, hNs1⟩, hK⟩ := hS
  have hYmem : Y ∈ foldInputs N := by rw [hsplit]; simp
  have hYstd : Std Y := std_foldInputs hN heps Y hYmem
  have hYpr : Pr (ordOf [Y]) := pr_ordOf_single hYstd
  set ξ := α + (pre.map fun Y => ordOf [Y]).sum with hξ
  have hξ0 : 0 < ξ := lt_of_lt_of_le (lt_trans zero_lt_one h1) le_self_add
  have hξ' : α + ((pre ++ [Y]).map fun Y => ordOf [Y]).sum = ξ + ordOf [Y] := by
    rw [sum_map_append, ← add_assoc, hξ]; simp
  have hle : ξ + ordOf [Y] ≤ lam α := by
    rw [hE1, hsplit, sum_map_append, ← add_assoc]
    simp only [List.map_cons, List.sum_cons]
    rw [← add_assoc]
    exact le_self_add
  have hξlam : ξ < lam α := lt_of_lt_of_le (lt_add_of_pos_right ξ hYpr.pos) hle
  have hlead : lead (ordOf (s1 :: S')) = ordOf [s1] := lead_ordOf_cons hSstd
  have hs1std : Std s1 := ((stdOrd_iff _).mp hSstd).2 s1 (by simp)
  rw [oplus_cons]
  split_ifs with hjump
  · -- a jump: E2 and (F2b)
    have hlt : lead (ordOf (s1 :: S')) < ordOf [Y] := by
      rw [hlead]; exact ordOf_single_lt hs1std hYstd hjump
    have hmin := hE2 pre Y post hsplit _ hK hlt
    obtain ⟨hadd, hkap, -⟩ := lemmaF2b hE h1 hT hξ0 hK hYpr hlt hmin
    refine ⟨hFstd Y hYstd, ?_, ?_⟩
    · obtain ⟨s, S'', hs⟩ := List.exists_cons_of_ne_nil (hFne Y)
      refine ⟨s, S'', hs, ?_⟩
      have := hFhead Y s (by rw [hs]; rfl)
      exact le_trans hNs1 (le_trans hjump.le this)
    · rw [hξ', hadd, hkap]
      exact hFL Y hYmem (lt_of_le_of_lt hNs1 hjump)
  · -- no jump: (F2a)
    have hYle : ordOf [Y] ≤ lead (ordOf (s1 :: S')) := by
      rw [hlead]; exact ordOf_single_le hYstd hs1std (not_lt.mp hjump)
    obtain ⟨-, hlh⟩ := lemmaF2a hE h1 hT hξ0 hξlam hK hYpr hYle
    have hhead := head_addT_of_not_lt (S := S') hjump
    obtain ⟨a, l, hal⟩ := List.exists_cons_of_ne_nil (show addT (s1 :: S') [Y] ≠ [] by
      intro h; rw [h] at hhead; simp at hhead)
    rw [hal] at hhead
    simp only [List.head?_cons, Option.some.injEq] at hhead
    refine ⟨stdOrd_addT hSstd (stdOrd_single hYstd), ⟨a, l, hal, hhead ▸ hNs1⟩, ?_⟩
    rw [hξ', ordOf_addT hSstd (stdOrd_single hYstd)]
    exact hlh

theorem foldInv_foldl : ∀ (rest pre : List Tm), foldInputs N = pre ++ rest →
    ∀ {S : List Tm}, FoldInv N pre S → FoldInv N (foldInputs N) (rest.foldl (oplus F) S)
  | [], pre, h, S, hS => by rw [List.append_nil] at h; rw [h]; exact hS
  | Y :: rest, pre, h, S, hS => by
    rw [List.foldl_cons]
    refine foldInv_foldl rest (pre ++ [Y]) (by rw [h]; simp) ?_
    exact foldInv_step hN heps F hFstd hFne hFhead hFL hE1 hE2 pre Y rest h hS

/-- **Prop 4.3.**  The fold computes the reach: `o(S_n) = lh(o(N))`. -/
theorem fold_isLh : IsLh (ordOf [N]) (ordOf ((foldInputs N).foldl (oplus F) [N, N])) := by
  set α := ordOf [N] with hα
  have hE := eps_ordOf hN heps
  have h1 := one_lt_ordOf_eps hN heps
  have hT : α < T1bound := ordOf_lt_T1bound (stdOrd_single hN)
  obtain ⟨hkapα, hlhα, -⟩ := lemmaF1 hE h1 hT
  have hNN : StdOrd [N, N] := (stdOrd_iff _).mpr ⟨by simp, by simpa using hN⟩
  have h0 : FoldInv N [] [N, N] := by
    refine ⟨hNN, ⟨N, [N], rfl, le_rfl⟩, ?_⟩
    simp only [List.map_nil, List.sum_nil, add_zero]
    rw [hkapα, ordOf_cons hNN]
    exact hlhα
  obtain ⟨-, -, hK⟩ := foldInv_foldl hN heps F hFstd hFne hFhead hFL hE1 hE2
    (foldInputs N) [] (by simp) h0
  rw [← hE1] at hK
  exact lemmaF3 hE h1 hT hK

end Fold

end Googology.Trans.PSS.Main
