import Googology.Trans.PoR.InaccPsi.R2.GvOm

/-!
# ITERATED UNIONS FROM ANY START; THE FRONTIER `ι(Γ(ε_{G+Ω₁·ω·2}))`

For any start `St` with index `i₀ = P + 1` (`Ω₁ ∣ P`) the iterated starts `gvItG St k` (`gvNext` applied `k` times)
have the indices `P + Ω₁·k + 1` and their unions the bounds `ε_{P+Ω₁·(k+1)}` (`gvItG_i0`, `gvItG_B`); each bound is
located (`R2.GvNx`, `gvLocU`), so ENUM-REACH and CapV hold at every range restart below `ι(Γ(ε_{P+Ω₁·ω}))`
(`gvWG_enum`, `gvWG_capV`).  From the start `gvStω` (`P = G + Ω₁·ω`, `R2.GvOm`) this gives the frontier
**`ι(Γ(ε_{G+Ω₁·ω·2}))`** (`gvW2`).

* `gvItG`, `gvItG_i0`, `gvItG_B`, `gvWG`, `gvWG_codes`, `gvWG_cof`, `gvWG_enum`, `gvWG_capV`, `gv_road_of` (the road
  from ENUM-REACH and CapV below any frontier);
* `gvW2`, `gvW2_enum`, `gvW2_capV`, `gvW2_road` (**THE ROAD**), `gvW2_lt_G1`, `gvW2_le_Om2`, `gvW2_P`,
  `gvW2_fr_order` (**`ι(Γ(ε_{G+Ω₁·ω})) < ι(Γ(ε_{G+Ω₁·ω})·ω) ≤ ι(Γ(ε_{G+Ω₁·ω·2})) ≤ ι(Ω₂)`**).

No new axiom.  New definitions: `gvItG`, `gvWG`, `gvW2`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gv

open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gp
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **The road from ENUM-REACH and CapV below a frontier `F`**: UPPER, LOWER, CapV asked only at `λ ≥ F`. -/
theorem gv_road_of (S : InaccSeq.{0}) (F : Ordinal.{0})
    (hE : ∀ l, CdRange S l → l < F → CdUpper S l ∧ CdLower S l) (hCap : ∀ l, CdRange S l → l < F → CdCapV S l)
    (hU : ∀ l, CdRange S l → F ≤ l → CdUpper S l) (hL : ∀ l, CdRange S l → F ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → F ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  refine goGl.go_road S (fun l hr _ => ?_) (fun l hr _ => ?_) (fun l hr hω _ => ?_) hC hEQ hrest hB2
  · by_cases h : l < F
    · exact (hE l hr h).1
    · exact hU l hr (not_lt.1 h)
  · by_cases h : l < F
    · exact (hE l hr h).2
    · exact hL l hr (not_lt.1 h)
  · by_cases h : l < F
    · exact hCap l hr h
    · exact hV l hr hω (not_lt.1 h)

/-- **The iterated starts from `St`.** -/
noncomputable def gvItG (St : GvSt) : ℕ → GvSt
  | 0 => St
  | k + 1 => gvNext (gvItG St k)

section Gen

variable (St : GvSt) (hI : St.i0 = St.P0 + 1)
include hI

theorem gvItG_i0 : ∀ k : ℕ, (gvItG St k).i0 = St.P0 + Om1 * (k : Ordinal.{0}) + 1
  | 0 => by
    show St.i0 = _
    rw [hI, Nat.cast_zero, mul_zero, add_zero]
  | k + 1 => by
    show (gvItG St k).i0 + Om1 + 1 = _
    rw [gvItG_i0 k, add_assoc (St.P0 + _) 1 Om1, Br.Om1_eq, Fx.fx_Om1_prin.add_eq_right one_lt_Om1, ← Br.Om1_eq,
      add_assoc St.P0, ← mul_add_one (Om1 : Ordinal.{0})]
    push_cast; rfl

/-- **The bound of the `k`-th union from `St`**: `ε_{P+Ω₁·(k+1)}`. -/
theorem gvItG_B (k : ℕ) : (gvUof (gvItG St k)).B = veblen 1 (St.P0 + Om1 * ((k : Ordinal.{0}) + 1)) := by
  rw [gvUof_B, gvItG_i0 St hI, add_assoc (St.P0 + _) 1 Om1, Br.Om1_eq, Fx.fx_Om1_prin.add_eq_right one_lt_Om1,
    ← Br.Om1_eq, add_assoc St.P0, ← mul_add_one (Om1 : Ordinal.{0})]

end Gen

/-- **The frontier bound from `St`**: `ε_{P+Ω₁·ω}`. -/
noncomputable def gvWG (St : GvSt) : Ordinal.{0} := veblen 1 (St.P0 + Om1 * ω)

section Fr

variable (St : GvSt) (hI : St.i0 = St.P0 + 1)
include hI

theorem gvWG_codes {c : Ordinal.{0}} (hc : c < gvWG St) : ∃ k : ℕ, c < (gvUof (gvItG St k)).B := by
  have hl : IsSuccLimit (Om1 * ω : Ordinal.{0}) := isSuccLimit_mul_right gv_Om1_pos isSuccLimit_omega0
  obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ hl)).1 hc
  obtain ⟨d, hd, htd⟩ := (lt_add_iff hl.bot_lt.ne').1 ht
  obtain ⟨m, hm, hdm⟩ := (lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 hd
  obtain ⟨k, rfl⟩ := lt_omega0.1 hm
  refine ⟨k, ?_⟩
  rw [gvItG_B St hI]
  refine hct.trans_le ((isNormal_veblen 1).monotone (htd.trans ((add_le_add_iff_left _).2 ?_)))
  exact hdm.le.trans (mul_le_mul_left' (le_self_add : (k : Ordinal.{0}) ≤ k + 1) _)

/-- **`ι(Γ(ε_{P+Ω₁·ω})) = sup_k ι(Γ(ε_{P+Ω₁·(k+1)})·ω)`.** -/
theorem gvWG_cof (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : l < iota S (gcG (gvWG St))) :
    ∃ k : ℕ, l < iota S (gcG (gvUof (gvItG St k)).B * ω) := by
  have hlim : IsSuccLimit (gcG (gvWG St)) := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (gcG_SC _))
  rw [iota_limit hlim] at hl
  haveI : Nonempty (Iio (gcG (gvWG St))) := ⟨⟨0, hlim.bot_lt⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hl
  have hWl : IsSuccLimit (gvWG St) := ev_isSuccLimit_of_inE (omega0_opow_epsilon _)
  obtain ⟨β, hβ, heβ⟩ := gcG_lt_of_lt_limit hWl e.2
  obtain ⟨k, hk⟩ := gvWG_codes St hI hβ
  refine ⟨k, he.trans_le (iota_mono _ _ ((heβ.trans (gcG_lt hk)).trans_le ?_).le)⟩
  exact le_mul_of_one_le_right' one_lt_omega0.le

/-- **ENUM-REACH at every range restart below `ι(Γ(ε_{P+Ω₁·ω}))`, fixed points included.** -/
theorem gvWG_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (gvWG St))) :
    CdUpper S l ∧ CdLower S l := by
  obtain ⟨k, h⟩ := gvWG_cof St hI S hl
  exact gvLocU_enum (gvItG St k) S hr h

/-- **CapV at every range restart below `ι(Γ(ε_{P+Ω₁·ω}))`.** -/
theorem gvWG_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (gvWG St))) :
    CdCapV S l := by
  obtain ⟨k, h⟩ := gvWG_cof St hI S hl
  exact gvLocU_capV (gvItG St k) S hr h

end Fr

/-! ## From the start `gvStω`: the frontier `ι(Γ(ε_{G+Ω₁·ω·2}))` -/

theorem gvStω_i0 : gvStω.i0 = gvStω.P0 + 1 := rfl

/-- **The new bound** `ε_{G+Ω₁·ω·2} = φ(1, G + Ω₁·ω + Ω₁·ω)`. -/
noncomputable def gvW2 : Ordinal.{0} := veblen 1 (gcG 0 + Om1 * ω + Om1 * ω)

theorem gvW2_eq : gvWG gvStω = gvW2 := rfl

/-- **ENUM-REACH at every range restart below `ι(Γ(ε_{G+Ω₁·ω·2}))`, fixed points included** (UNCONDITIONAL). -/
theorem gvW2_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG gvW2)) :
    CdUpper S l ∧ CdLower S l := gvWG_enum gvStω gvStω_i0 S hr hl

/-- **CapV at every range restart below `ι(Γ(ε_{G+Ω₁·ω·2}))`** (UNCONDITIONAL). -/
theorem gvW2_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG gvW2)) :
    CdCapV S l := gvWG_capV gvStω gvStω_i0 S hr hl

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(ε_{G+Ω₁·ω·2}))` (CapV also `υ_λ < L(ω)`), (CL), EQ,
TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem gvW2_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG gvW2) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG gvW2) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG gvW2) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gv_road_of S _ (fun _ hr h => gvW2_enum S hr h) (fun _ hr h => gvW2_capV S hr h) hU hL hV hC hEQ hrest hB2

theorem gvW2_lt_G1 : gvW2 < gcG 1 := by
  have hE : InE (gcG 1) := Low.opow_eq_self_of_SC (gcG_SC 1)
  have hOw : (Om1 : Ordinal.{0}) * ω < gcG 1 := InE.mul_lt hE gv_Om1_lt_G1 (omega0_lt_inE hE)
  have h1 : gcG 0 + Om1 * ω + Om1 * ω < gcG 1 := (inE_indec hE).add_lt gvWW_ix_lt hOw
  exact (gcG_SC 1).2 1 (one_lt_omega0.trans (omega0_lt_inE hE)) _ h1

/-- **`Γ(ε_{G+Ω₁·ω·2}) < Ω₂`.** -/
theorem gvW2_le_Om2 : gcG gvW2 < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG gvW2 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) (gvW2_lt_G1.trans hG1))
  exact h2.trans Tf.tfBG_lt_Om2

/-- **`P(Γ(ε_{G+Ω₁·ω·2})) < L(0)`.** -/
theorem gvW2_P (S : InaccSeq.{0}) : Pv S (gcG gvW2) < Nc.ncL S 0 := ga_Pv_lt_L0 S gvW2_le_Om2.le

/-- **The order of the frontiers**: `ι(Γ(ε_{G+Ω₁·ω})) < ι(Γ(ε_{G+Ω₁·ω})·ω) ≤ ι(Γ(ε_{G+Ω₁·ω·2})) ≤ ι(Ω₂)`,
`P(Γ(ε_{G+Ω₁·ω·2})) ≤ P(Ω₂) < L(0)`. -/
theorem gvW2_fr_order (S : InaccSeq.{0}) :
    gvWW < gvW2 ∧ iota S (gcG gvWW) < iota S (gcG gvWW * ω) ∧ iota S (gcG gvWW * ω) ≤ iota S (gcG gvW2) ∧
      iota S (gcG gvW2) ≤ iota S (Om (1 + 1)) ∧ Pv S (gcG gvW2) ≤ Pv S (Om (1 + 1)) ∧
      Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hlt : gvWW < gvW2 := by
    refine (isNormal_veblen 1).strictMono (lt_add_of_pos_right _ ?_)
    exact mul_pos gv_Om1_pos omega0_pos
  have hg0 := gvWW_g S
  have hgood : Bt.Good S (gcG gvDω.B) :=
    gs_good (K := gvDω.step.toRS.K) fun Z _ hKZ =>
      GxCl.atom (gsmG_atom (K := gvDω.step.toRS.K) gvWW_lt_S (hg0.trans_le hKZ))
  have hG : InE (gcG gvWW) := Low.opow_eq_self_of_SC (gcG_SC _)
  have hV : InE (gcG gvW2) := Low.opow_eq_self_of_SC (gcG_SC _)
  exact ⟨hlt, cd_iota_lt_of_good hgood (lt_mul_of_one_lt_right hG.pos one_lt_omega0),
    iota_mono _ _ (InE.mul_lt hV (gcG_lt hlt) (omega0_lt_inE hV)).le,
    iota_mono _ _ gvW2_le_Om2.le, Nm.Pv_mono gvW2_le_Om2.le, ga_Pv_lt_L0 S le_rfl⟩

end Googology.Trans.PoR.InaccPsi.R2.Gv
