import Googology.Trans.PoR.InaccPsi.R2.ZfFin

/-!
# `ϑᵗ` is one-to-one on `Tᵗ ∩ Ω₂` (so a node value determines its level and its countable part)

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

[W07a] Lemma 3.30 says `ϑ₀ ↾ Tᵗ ∩ Ω₂` is 1-1; Lean has the comparison clauses at the separate level ranges.  Here the
injectivity, from: `vt τ 0 = τ` (`Si.siVt_zero`) and `ϑᵗ(1 + α) = ω̄_{τ+α}` (`R2.vt_wbar`, `ω̄` strictly increasing
onto the non-`ε` additive principal numbers) below `Ω₁`; `R2.vt_E_iff` across `Ω₁`; the countable levels by
`Gl.glA_lt_iff`, `Gl.glA_lev`; a level `≥ Ω₁` above by `R2.vdVt_lt` with the strongly critical value
(`Zf.zf_vt_SC`).  So a configuration node `y = ϑᵗ(Ω₁·M + η)` determines `M = ξ / Ω₁` and `η = ξ mod Ω₁`, which is
what keys the enlargement of the configuration by the leaves of the levels of its nodes.

* `zf_lev_T` (the countable level of an argument is in `Tᵗ`), `zf_datIn_any` (the data of any level `1 ≤ M` are read
  in `Tᵗ`), `zf_datLt` (some reading below the value), `zf_vt_ne` (**`ξ < ξ' ⇒ ϑᵗ(ξ) ≠ ϑᵗ(ξ')`**), `zf_vt_inj`
  (**`ϑᵗ(ξ) = ϑᵗ(ξ') ⇒ ξ = ξ'`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

/-- **The countable level of an argument is in `Tᵗ`.** -/
theorem zf_lev_T {τ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM : M < Om1) (hη1 : η < Om1)
    (h : Om1 * M + η ∈ Tset τ) : M ∈ Tset τ := by
  have h' : Om1 * (Om1 * 0 + M) + η ∈ Tset τ := by simpa using h
  exact Rj.rjArgT_beta hτ hτ1 Rj.rj_Om1_pos hM hη1 h'

/-- **The data of a level `1 ≤ M` are read in `Tᵗ`** (`Ω₁·M + η ∈ Tᵗ ∩ Ω₂`). -/
theorem zf_datIn_any (S : InaccSeq.{0}) {τ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hη1 : η < Om1)
    (h : Om1 * M + η ∈ Tset τ) (h2 : Om1 * M + η < OmTwo) : Vd.VdDatIn (· ∈ Tset τ) M := by
  rcases lt_or_ge M Om1 with hM | hM
  · have hB : M < Uc.ucB := hM.trans (Rj.rj_Om1 ▸ Vd.vd_Om1_lt_B : Om1 < Uc.ucB)
    exact Vd.vdDatIn_uc hB (by rw [Uc.ucDat_small hM]; exact zf_lev_T hτ hτ1 hM hη1 h)
  · exact zf_dat_in S hτ hτ1 hM hη1 h h2

/-- **Some reading of the data of a level `1 ≤ M` lies below the value** `ϑᵗ(Ω₁·M + η)`. -/
theorem zf_datLt (S : InaccSeq.{0}) {τ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : 1 ≤ M)
    (hη1 : η < Om1) (h : Om1 * M + η ∈ Tset τ) (h2 : Om1 * M + η < OmTwo) :
    Vd.VdLtIn M (vt τ (Om1 * M + η)) := by
  have hOB : Om1 < Uc.ucB := (Rj.rj_Om1 ▸ Vd.vd_Om1_lt_B : Om1 < Uc.ucB)
  have hηT : η ∈ Tset τ := vzRem_T hτ hτ1 h h2 rfl (dvd_mul_right Om1 M) hη1
  rcases lt_or_ge M Om1 with hM | hM
  · have hMT := zf_lev_T hτ hτ1 hM hη1 h
    have hlt : M < vt τ (Om1 * M + η) := (Gl.glA_facts hτ hτ1 hM1 hMT hM hηT hη1).2.2.2.2.1
    exact Or.inl ⟨hM.trans hOB, by rw [Uc.ucDat_small hM]; exact hlt⟩
  · have hSC := zf_vt_SC S hτ hτ1 hM hη1 h h2
    have hA := (vdLevel_lt hτ hτ1 hM (zf_dat_in S hτ hτ1 hM hη1 h h2) hηT hη1).1
    have hθ : Om1 * M + η < ConjT.th S := uzTBound (S := S) τ hτ hτ1 _ h h2
    have hMθ : M < ConjT.th S := ((Xe.xe_le_mul M).trans le_self_add).trans_lt hθ
    rcases lt_or_ge M Uc.ucB with hB | hB
    · exact Or.inl ⟨hB, hA.1 hB⟩
    · exact Or.inr ⟨S, hB, hMθ, _, hSC, le_rfl, hA.2 S hB hMθ _ hSC le_rfl⟩

/-- **`ξ < ξ'` in `Tᵗ ∩ Ω₂` ⇒ `ϑᵗ(ξ) ≠ ϑᵗ(ξ')`.** -/
theorem zf_vt_ne (S : InaccSeq.{0}) {τ ξ ξ' : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hξ : ξ ∈ Tset τ)
    (hξ2 : ξ < OmTwo) (hξ' : ξ' ∈ Tset τ) (hξ'2 : ξ' < OmTwo) (hlt : ξ < ξ') : vt τ ξ ≠ vt τ ξ' := by
  intro heq
  have hO0 : (Om1 : Ordinal.{0}) ≠ 0 := Rj.rj_Om1_pos.ne'
  rcases lt_or_ge ξ' Om1 with h' | h'
  · -- both countable
    have hmono := enumOrd_strictMono nonEAP_unbounded
    have h1' : 1 ≤ ξ' := Order.one_le_iff_ne_zero.2 (lt_of_le_of_lt zero_le hlt).ne'
    have e' : 1 + (ξ' - 1) = ξ' := Ordinal.add_sub_cancel_of_le h1'
    have hα' : ξ' - 1 < Om1 := (Ordinal.sub_le_self _ _).trans_lt h'
    have hv' : vt τ ξ' = wbar (τ + (ξ' - 1)) := by rw [← vt_wbar hτ hτ1 hα', e']
    rcases eq_or_ne ξ 0 with h0 | h0
    · rw [h0, Si.siVt_zero hτ hτ1, hv'] at heq
      have hm : wbar (τ + (ξ' - 1)) ∈ NonEAP := enumOrd_mem nonEAP_unbounded _
      exact hm.2 (heq ▸ hτ)
    · have h1 : 1 ≤ ξ := Order.one_le_iff_ne_zero.2 h0
      have e : 1 + (ξ - 1) = ξ := Ordinal.add_sub_cancel_of_le h1
      have hα : ξ - 1 < Om1 := (Ordinal.sub_le_self _ _).trans_lt (hlt.trans h')
      have hv : vt τ ξ = wbar (τ + (ξ - 1)) := by rw [← vt_wbar hτ hτ1 hα, e]
      have hαα : ξ - 1 < ξ' - 1 := by
        have : 1 + (ξ - 1) < 1 + (ξ' - 1) := by rw [e, e']; exact hlt
        exact (add_lt_add_iff_left 1).1 this
      rw [hv, hv'] at heq
      exact absurd heq (hmono ((add_lt_add_iff_left τ).2 hαα)).ne
  rcases lt_or_ge ξ Om1 with h | h
  · -- across `Ω₁`
    have hE := (vt_E_iff hτ hτ1 hξ' hξ'2).2 h'
    rw [← heq] at hE
    exact absurd ((vt_E_iff hτ hτ1 hξ hξ2).1 hE) (not_le.2 h)
  -- both `≥ Ω₁`
  have hs : Om1 * (ξ / Om1) + ξ % Om1 = ξ := Ordinal.div_add_mod ξ Om1
  have hs' : Om1 * (ξ' / Om1) + ξ' % Om1 = ξ' := Ordinal.div_add_mod ξ' Om1
  set M := ξ / Om1 with hMdef
  set η := ξ % Om1 with hηdef
  set M' := ξ' / Om1 with hM'def
  set η' := ξ' % Om1 with hη'def
  have hη1 : η < Om1 := Ordinal.mod_lt ξ hO0
  have hη'1 : η' < Om1 := Ordinal.mod_lt ξ' hO0
  have hM1 : 1 ≤ M := (Ordinal.le_div hO0).2 (by rw [mul_one]; exact h)
  have hM'1 : 1 ≤ M' := (Ordinal.le_div hO0).2 (by rw [mul_one]; exact h')
  have hMM' : M ≤ M' := (Ordinal.le_div hO0).2 ((le_self_add.trans hs.le).trans hlt.le)
  rw [← hs] at hξ hξ2 heq hlt
  rw [← hs'] at hξ' hξ'2 heq hlt
  have hηT : η ∈ Tset τ := vzRem_T hτ hτ1 hξ hξ2 rfl (dvd_mul_right Om1 M) hη1
  have hη'T : η' ∈ Tset τ := vzRem_T hτ hτ1 hξ' hξ'2 rfl (dvd_mul_right Om1 M') hη'1
  rcases lt_or_ge M' Om1 with hM'Ω | hM'Ω
  · -- two countable levels
    have hMΩ : M < Om1 := hMM'.trans_lt hM'Ω
    have hMT := zf_lev_T hτ hτ1 hMΩ hη1 hξ
    have hM'T := zf_lev_T hτ hτ1 hM'Ω hη'1 hξ'
    change Gl.glA M η τ = Gl.glA M' η' τ at heq
    rcases hMM'.lt_or_eq with hMl | hMe
    · have hlt' : Gl.glA M η τ < Gl.glA M' η' τ := by
        refine (Gl.glA_lev hτ hτ1 hM1 hMl hM'T hM'Ω hη'T hη'1 hηT hη1).2 ?_
        rw [← heq]; exact (Gl.glA_facts hτ hτ1 hM1 hMT hMΩ hηT hη1).2.2.2.2.2
      exact absurd heq hlt'.ne
    · rw [← hMe] at heq hlt
      have hηη : η < η' := (add_lt_add_iff_left _).1 hlt
      exact absurd heq ((Gl.glA_lt_iff hτ hτ1 hM1 hMT hMΩ hηT hη1 hη'T hη'1).2 hηη).ne
  · -- the larger level is `≥ Ω₁`
    have hMT : Vd.VdDatIn (· ∈ Tset τ) M := zf_datIn_any S hτ hτ1 hη1 hξ hξ2
    have hM'T : Vd.VdDatIn (· ∈ Tset τ) M' := zf_dat_in S hτ hτ1 hM'Ω hη'1 hξ' hξ'2
    have hd : Vd.VdLtIn M (vt τ (Om1 * M' + η')) := heq ▸ zf_datLt S hτ hτ1 hM1 hη1 hξ hξ2
    have hθ : Om1 * M + η < ConjT.th S := uzTBound (S := S) τ hτ hτ1 _ hξ hξ2
    have hηv : η < vt τ (Om1 * M' + η') :=
      heq ▸ Za.za_lt_vt_all hτ hτ1 hM1 (le_self_add.trans_lt hθ) hηT hη1 hξ
    have hlt' := vdVt_lt hτ hτ1 hM'Ω hMM' hMT hηT hη1 hM'T hη'T hη'1 hlt hd hηv
    exact absurd heq hlt'.ne

/-- **`ϑᵗ` is one-to-one on `Tᵗ ∩ Ω₂`** ([W07a] Lemma 3.30, first sentence). -/
theorem zf_vt_inj (S : InaccSeq.{0}) {τ ξ ξ' : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hξ : ξ ∈ Tset τ)
    (hξ2 : ξ < OmTwo) (hξ' : ξ' ∈ Tset τ) (hξ'2 : ξ' < OmTwo) (heq : vt τ ξ = vt τ ξ') : ξ = ξ' := by
  rcases lt_trichotomy ξ ξ' with h | h | h
  · exact absurd heq (zf_vt_ne S hτ hτ1 hξ hξ2 hξ' hξ'2 h)
  · exact h
  · exact absurd heq.symm (zf_vt_ne S hτ hτ1 hξ' hξ'2 hξ hξ2 h)

end Googology.Trans.PoR.InaccPsi.R2.Zf
