import Googology.Trans.PoR.InaccPsi.R2.ZgDiv

/-!
# ZgPi: LEMMA EXACT FOR `ω^{D(ρ)+β}` (THE POWERS ABOVE THE READING OF `B_Γ`)

`ϑˣ(D(x) + γ) = ω^{D(x)+1+γ}` for `γ < D(x)` ([W07a] Lemma 4.2 through `R2.vt_wbar` and `R2.wbar_eq` with the
pseudo-base `D(x)`; `zgVtD`), so `π_{σ,ρ}(ω^{D(ρ)+β}) = ω^{D(σ)+π β}` for `β ∈ Tᵖ[σ]` below `D(ρ)` with `π β < D(σ)`
([W07a] Def 5.1, fourth clause, `R2.pi_vt`; `zgOpowD`): the exponent part of Lemma EXACT for a reading
`D(x)·(1 + yrR d x) + yrR r x` of the offsets `B_Γ·d + r` (through `Yr.yr_dig` with `P = D(ρ)`, `P' = D(σ)`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Lu

/-- **`ϑˣ(D(x) + γ) = ω^{D(x)+1+γ}`** for `γ < D(x)`. -/
theorem zgVtD {x γ : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : γ < ywV 1 0 x) :
    vt x (ywV 1 0 x + γ) = ω ^ (ywV 1 0 x + 1 + γ) := by
  obtain ⟨hxD, -, -⟩ := ywD_closed hx hx1
  obtain ⟨-, hD1, hDE⟩ := zgD_T hx hx1
  set D := ywV 1 0 x with hD
  have hDI := inE_indec hDE
  have hE1 : D + γ < Om1 := (inE_indec Rj.rj_Om1_inE).add_lt hD1 (hγ.trans hD1)
  have hωD : ω ≤ D + γ := (omega0_le_of_isSuccLimit (ev_isSuccLimit_of_inE hDE)).trans le_self_add
  have hxD' : x + D = D := Ordinal.add_of_omega0_opow_le (c := D) (by rw [hDE]; exact hxD) (by rw [hDE])
  calc vt x (D + γ) = vt x (1 + (D + γ)) := by rw [one_add_of_omega0_le hωD]
    _ = wbar (x + (D + γ)) := vt_wbar hx hx1 hE1
    _ = wbar (D + γ) := by rw [← add_assoc, hxD']
    _ = ω ^ (D + 1 + γ) := wbar_eq hDE γ fun β hβ1 hβ2 hβE => by
        have h1γ : 1 + γ < D := hDI.add_lt ((lu_one_lt_E hx).trans hxD) hγ
        have : D + (1 + γ) < β := (inE_indec hβE).add_lt hβ1 (h1γ.trans hβ1)
        rw [← add_assoc] at this
        exact absurd hβ2 (not_le.2 this)

/-- **Lemma EXACT for `ω^{D(ρ)+β}`**: `π_{σ,ρ}(ω^{D(ρ)+β}) = ω^{D(σ)+π β}`. -/
theorem zgOpowD {σ ρ β : Ordinal.{0}} (hB : Bases σ ρ) (hβT : β ∈ TB ρ σ) (hβ : β < ywV 1 0 ρ)
    (hβ' : Googology.Trans.PoR.InaccPsi.R2.pi σ ρ β < ywV 1 0 σ) :
    ω ^ (ywV 1 0 ρ + β) ∈ TB ρ σ ∧
      Googology.Trans.PoR.InaccPsi.R2.pi σ ρ (ω ^ (ywV 1 0 ρ + β)) = ω ^ (ywV 1 0 σ + Googology.Trans.PoR.InaccPsi.R2.pi σ ρ β) := by
  have h1σ : (1 : Ordinal.{0}) < σ := lu_one_lt_E hB.1
  have h0σ : (0 : Ordinal.{0}) < σ := hB.1.pos
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hD := ywV_pi hB (mem_TB_of_lt hB h1σ) ((lu_one_lt_E hB.2.1).trans hρ1) (mem_TB_of_lt hB h0σ)
    (hB.2.1.pos.trans hρ1)
  rw [pi_lt hB h1σ, pi_lt hB h0σ] at hD
  obtain ⟨-, hD1, hDE⟩ := zgD_T hB.2.1 hρ1
  rcases eq_or_ne β 0 with rfl | hβ0
  · rw [add_zero, pi_lt hB h0σ, add_zero, hDE, (zgD_T hB.1 hσ1).2.2]; exact hD
  obtain ⟨γ, hγ⟩ := exists_add_of_le (one_le_iff_ne_zero.2 hβ0)
  have hγT : γ ∈ TB ρ σ := by
    rcases lt_or_ge β ω with hβω | hβω
    · exact mem_TB_of_lt hB ((le_add_self.trans_lt (hγ ▸ hβω)).trans (omega0_lt_inE hB.1))
    · have : γ = β := by
        rw [hγ] at hβω ⊢
        have hγω : ω ≤ γ := by
          by_contra h; push Not at h
          exact absurd hβω (not_le.2 (by
            obtain ⟨n, rfl⟩ := lt_omega0.1 h
            exact_mod_cast natCast_lt_omega0 (1 + n)))
        rw [one_add_of_omega0_le hγω]
      rw [this]; exact hβT
  have hγβ : γ ≤ β := hγ ▸ le_add_self
  obtain ⟨h1T, h1π⟩ : (1 : Ordinal.{0}) ∈ TB ρ σ ∧ Googology.Trans.PoR.InaccPsi.R2.pi σ ρ 1 = 1 :=
    ⟨mem_TB_of_lt hB h1σ, pi_lt hB h1σ⟩
  obtain ⟨-, hπβ⟩ := pi_add hB h1T hγT
  rw [← hγ, h1π] at hπβ
  have hπγ : Googology.Trans.PoR.InaccPsi.R2.pi σ ρ γ < ywV 1 0 σ := le_add_self.trans_lt (hπβ ▸ hβ')
  obtain ⟨hET, hEπ⟩ := pi_add hB hD.1 hγT
  have hE1 : ywV 1 0 ρ + γ < Om1 := (inE_indec Rj.rj_Om1_inE).add_lt hD1 ((hγβ.trans_lt hβ).trans hD1)
  have hv := zgVtD hB.2.1 hρ1 (hγβ.trans_lt hβ)
  rw [add_assoc, ← hγ] at hv
  obtain ⟨hvT, hvP⟩ := vt_mem hB.2.1 hρ1 hET.1 hE1
  refine ⟨by rw [← hv]; exact ⟨hvT, by rw [hvP]; exact hET.2⟩, ?_⟩
  rw [← hv, pi_vt hB hET hE1, hEπ, hD.2, zgVtD hB.1 hσ1 hπγ, add_assoc, hπβ]

end Googology.Trans.PoR.InaccPsi.R2.Zg
