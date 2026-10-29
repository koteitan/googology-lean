import Googology.Trans.PoR.InaccPsi.R2.VsBase

/-!
# The height residual at every finite `s`: an own-for-`ψ_V` threshold is own for `ψ_W`

`W = Ω_{s+1}`, `V = Ω_{s+2}` (`s` finite), `ψ_π = S.psi · π`, `ulDatT S κ t` / `ulArgsT S κ A t` the leaves of `t`
below `κ` and the collapse arguments of its subterms `≥ κ` (`R2.UlCode`), `m(γ) = ulDat S W γ`.  The statements of
`Vp.vp_code_V`, `Vp.vp_args_WV`, `Vp.vpHt` with `1` replaced by `s`:

* `vs_code_V` (**the code test at `V` of an own-for-`ψ_V` normal form**), `vs_args_WV` (**`ulDatT V t < ψ_V(A)` and
  `ulArgsT V A t` give `ulArgsT W A t`** for a normal form `t`);
* `vsHt` (**an own-for-`ψ_V` `K` of the notation with `ψ_V(K) ≤ γ < ψ_V(K + 1)` (`γ` of the notation) is own for
  `ψ_W`, or `ψ_W(K) ≤ m(γ)`**; no hypothesis beyond `s < ω`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vs

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

theorem vs_s1_lt_W (hs : s < ω) : s + 1 < Om (s + 1) :=
  (Ui.ui_s1_lt_omega hs).trans_le (Vp.vp_omega_le_Om1.trans vs_Om1_le_W)

/-- **The code test at `V` of an own-for-`ψ_V` normal form**: `ulDatT V t < ψ_V(|t|)` and `ulArgsT V |t| t`. -/
theorem vs_code_V (hs : s < ω) {t : Term} (hN : NF t)
    (hown : val S t ∈ S.CSet (val S t) (S.psi (val S t) (Om (s + 1 + 1)))) :
    ulDatT S (Om (s + 1 + 1)) t < S.psi (val S t) (Om (s + 1 + 1)) ∧
      ulArgsT S (Om (s + 1 + 1)) (val S t) t := by
  have hκV : S.InR (Om (s + 1 + 1)) := InR_Om_succ (s + 1)
  have hq1 : S.psi (val S t) (Om (s + 1 + 1)) ≤ Om (s + 1 + 1) := (Ui.ui_psi_lt (s := s + 1) _).le
  exact ul_code_dat hq1 (Us.us_qΛ (i := s + 1) (Ui.ui_s1_lt_omega hs) hq1)
    (fun y hy hyV => lt_psi_of_mem hκV hy hyV) (Ui.ui_psi_SC (s := s + 1) _).1 t hN hown

/-- **The collapse arguments at `W` from those at `V`**: for a normal form `t` with `ulDatT V t < ψ_V(A)` and
`ulArgsT V A t`, `ulArgsT W A t`. -/
theorem vs_args_WV (hs : s < ω) : ∀ t : Term, NF t → ∀ A : Ordinal.{0},
    ulDatT S (Om (s + 1 + 1)) t < S.psi A (Om (s + 1 + 1)) → ulArgsT S (Om (s + 1 + 1)) A t →
      ulArgsT S (Om (s + 1)) A t := by
  have hκV : S.InR (Om (s + 1 + 1)) := InR_Om_succ (s + 1)
  intro t
  induction t with
  | zero => intro _ _ _ _; trivial
  | inacc n => intro _ _ _ _; trivial
  | inaccW => intro _ _ _ _; trivial
  | add a b iha ihb =>
    intro hN A hd ha
    simp only [ulArgsT]
    by_cases hW : val S (add a b) < Om (s + 1)
    · exact Or.inl hW
    refine Or.inr ?_
    have hle_a : val S a ≤ val S (add a b) := by show val S a ≤ val S a + val S b; exact le_self_add
    have hle_b : val S b ≤ val S (add a b) := by show val S b ≤ val S a + val S b; exact le_add_self
    by_cases hV : val S (add a b) < Om (s + 1 + 1)
    · rw [ulDatT_small hV] at hd
      have hsa : val S a < Om (s + 1 + 1) := hle_a.trans_lt hV
      have hsb : val S b < Om (s + 1 + 1) := hle_b.trans_lt hV
      exact ⟨iha hN.1 A (by rw [ulDatT_small hsa]; exact hle_a.trans_lt hd) (Vp.vp_args_small _ hsa),
        ihb hN.2.1 A (by rw [ulDatT_small hsb]; exact hle_b.trans_lt hd) (Vp.vp_args_small _ hsb)⟩
    · simp only [ulDatT, if_neg hV] at hd
      simp only [ulArgsT] at ha
      have ha' := ha.resolve_left hV
      exact ⟨iha hN.1 A ((le_max_left _ _).trans_lt hd) ha'.1, ihb hN.2.1 A ((le_max_right _ _).trans_lt hd) ha'.2⟩
  | phi a b iha ihb =>
    intro hN A hd ha
    simp only [ulArgsT]
    by_cases hW : val S (phi a b) < Om (s + 1)
    · exact Or.inl hW
    refine Or.inr ?_
    have hN' := hN
    obtain ⟨hNa, hNb, hca, hcb⟩ := hN
    have hle_a : val S a ≤ val S (phi a b) := by
      have e := Term.cmp_eq_compare S hNa hN'
      rw [e] at hca; exact (compare_lt_iff_lt.1 hca).le
    have hle_b : val S b ≤ val S (phi a b) := by
      have e := Term.cmp_eq_compare S hNb hN'
      rw [e] at hcb; exact (compare_lt_iff_lt.1 hcb).le
    by_cases hV : val S (phi a b) < Om (s + 1 + 1)
    · rw [ulDatT_small hV] at hd
      have hsa : val S a < Om (s + 1 + 1) := hle_a.trans_lt hV
      have hsb : val S b < Om (s + 1 + 1) := hle_b.trans_lt hV
      exact ⟨iha hNa A (by rw [ulDatT_small hsa]; exact hle_a.trans_lt hd) (Vp.vp_args_small _ hsa),
        ihb hNb A (by rw [ulDatT_small hsb]; exact hle_b.trans_lt hd) (Vp.vp_args_small _ hsb)⟩
    · simp only [ulDatT, if_neg hV] at hd
      simp only [ulArgsT] at ha
      have ha' := ha.resolve_left hV
      exact ⟨iha hNa A ((le_max_left _ _).trans_lt hd) ha'.1, ihb hNb A ((le_max_right _ _).trans_lt hd) ha'.2⟩
  | om a iha =>
    intro hN A hd ha
    simp only [ulArgsT]
    by_cases hW : val S (om a) < Om (s + 1)
    · exact Or.inl hW
    refine Or.inr ?_
    by_cases hV : val S (om a) < Om (s + 1 + 1)
    · have h3 : val S a < s + 1 + 1 := Om_lt_Om.1 hV
      exact Vp.vp_args_small _ ((Order.lt_add_one_iff.1 h3).trans_lt (vs_s1_lt_W hs))
    · simp only [ulDatT, if_neg hV] at hd
      simp only [ulArgsT] at ha
      exact iha hN.1 A hd (ha.resolve_left hV)
  | psiS σ a ihs iha =>
    intro hN A hd ha
    simp only [ulArgsT]
    by_cases hW : val S (psiS σ a) < Om (s + 1)
    · exact Or.inl hW
    refine Or.inr ?_
    have hsem := Term.sem_of_NF (S := S) hN
    by_cases hV : val S (psiS σ a) < Om (s + 1 + 1)
    · have hb := psiS_bounds (S := S) (val S a) (val S σ)
      have hval : val S (psiS σ a) = S.psi (val S a) (Om (val S σ + 1)) := rfl
      have hσ : val S σ = s + 1 := by
        have h1 : Om (s + 1) < Om (val S σ + 1) := (not_lt.1 hW).trans_lt (hval ▸ hb.2)
        have h2 : Om (val S σ) < Om (s + 1 + 1) := hb.1.trans (hval ▸ hV)
        exact le_antisymm (Order.lt_add_one_iff.1 (Om_lt_Om.1 h2)) (Order.lt_add_one_iff.1 (Om_lt_Om.1 h1))
      rw [ulDatT_small hV, hval, hσ] at hd
      have hlt : val S a < A := by
        by_contra hc
        push Not at hc
        exact absurd (psi_mono hκV hc).1 (not_le.2 hd)
      have hσW : val S σ < Om (s + 1) := by rw [hσ]; exact vs_s1_lt_W hs
      refine ⟨hlt, Vp.vp_args_small _ hσW, ?_⟩
      have hown : val S a ∈ S.CSet (val S a) (S.psi (val S a) (Om (s + 1 + 1))) := by
        have h := hsem.2.2
        rwa [hσ] at h
      obtain ⟨hda, haa⟩ := vs_code_V hs hN.2.1 hown
      exact Vp.vp_args_mono hlt.le _ (iha hN.2.1 (val S a) hda haa)
    · simp only [ulDatT, if_neg hV] at hd
      simp only [ulArgsT] at ha
      obtain ⟨hlt, has, haa⟩ := ha.resolve_left hV
      exact ⟨hlt, ihs hN.1 A ((le_max_left _ _).trans_lt hd) has,
        iha hN.2.1 A ((le_max_right _ _).trans_lt hd) haa⟩
  | psiI m a iha =>
    intro hN A hd ha
    simp only [ulArgsT]
    by_cases hW : val S (psiI m a) < Om (s + 1)
    · exact Or.inl hW
    refine Or.inr ?_
    have hfix : Om (val S (psiI m a)) = val S (psiI m a) := InaccSeq.Om_psiI _ _
    have hne : val S (psiI m a) ≠ 0 :=
      (lt_of_le_of_lt zero_le (InaccSeq.Om_one_lt_psiI (S := S) (val S a) m)).ne'
    have hV : ¬ val S (psiI m a) < Om (s + 1 + 1) := not_lt.2 (vs_fix_ge hs hfix hne)
    simp only [ulDatT, if_neg hV] at hd
    simp only [ulArgsT] at ha
    obtain ⟨hlt, haa⟩ := ha.resolve_left hV
    exact ⟨hlt, iha hN.1 A hd haa⟩

/-- **The height residual at every finite `s`, no hypothesis**: an own-for-`ψ_V` `K` of the notation with
`ψ_V(K) ≤ γ < ψ_V(K + 1)` (`γ` of the notation) is own for `ψ_W`, or `ψ_W(K) ≤ m(γ)`. -/
theorem vsHt (hs : s < ω) : ∀ γ K, γ ∈ ⋃ a, S.CSet a 0 → K ∈ ⋃ a, S.CSet a 0 →
    K ∈ S.CSet K (S.psi K (Om (s + 1 + 1))) → S.psi K (Om (s + 1 + 1)) ≤ γ →
    γ < S.psi (K + 1) (Om (s + 1 + 1)) →
      K ∈ S.CSet K (S.psi K (Om (s + 1))) ∨ S.psi K (Om (s + 1)) ≤ ulDat S (Om (s + 1)) γ := by
  intro γ K hγN hKN hown hle hlt
  have hκV : S.InR (Om (s + 1 + 1)) := InR_Om_succ (s + 1)
  by_cases h : S.psi K (Om (s + 1)) ≤ ulDat S (Om (s + 1)) γ
  · exact Or.inr h
  push Not at h
  left
  have hqS : SC (S.psi K (Om (s + 1))) := Ui.ui_psi_SC (s := s) K
  have hq1 : Om s < S.psi K (Om (s + 1)) := Ui.ui_L_lt_psi (s := s) K
  have hqW : S.psi K (Om (s + 1)) ≤ Om (s + 1) := (Ui.ui_psi_lt (s := s) K).le
  have hγq : UlK S s (S.psi K (Om (s + 1))) γ := (Uo.uo_K_iff_dat hs hqS hq1 hqW hγN).2 h
  have htq := vs_gap_K hs hqW hown γ hγq hle hlt
  have hqL : S.psi K (Om (s + 1)) ≤ S.Lam := Us.us_qΛ (i := s) hs hqW
  have hKq : UlK S s (S.psi K (Om (s + 1))) K := Uo.uoArg hqL hκV hown htq (ul_psiW_le_psiV K K)
  obtain ⟨hN, hv⟩ := Bc.bcNf_spec S hKN
  have hdat : ulDatT S (Om (s + 1)) (Bc.bcNf S K) < S.psi K (Om (s + 1)) :=
    Uo.uo_K_code_dat hs hqS hq1 hqW _ hN (by rw [hv]; exact hKq)
  have hownt : val S (Bc.bcNf S K) ∈ S.CSet (val S (Bc.bcNf S K))
      (S.psi (val S (Bc.bcNf S K)) (Om (s + 1 + 1))) := by rw [hv]; exact hown
  obtain ⟨hdV, haV⟩ := vs_code_V hs hN hownt
  rw [hv] at hdV haV
  have haW := vs_args_WV hs _ hN K hdV haV
  have hmem := ul_code_mem (S := S) (κ := Om (s + 1)) (A := K) (q := S.psi K (Om (s + 1))) _ hdat haW
  rwa [hv] at hmem

end Googology.Trans.PoR.InaccPsi.R2.Vs
