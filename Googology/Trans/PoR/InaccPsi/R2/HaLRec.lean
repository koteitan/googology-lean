import Googology.Trans.PoR.InaccPsi.R2.HaL

/-!
# HaLRec: THE RECURSION OVER THE `ζ`-INDICES `λ < φ(3, G+1)` AND ITS INVARIANT

`haLU λ` is the start of the gated stage `λ` (index base `Q_λ = φ(2, G + 1 + λ)`, the `ζ`-index `λ` read by the
systems themselves): `GzVD.ofW gwZU` at `0`, the self-read union `Ha.haSU` of the stage `λ` at `λ+1`, the union
`Ha.HaLFam.U` of all earlier starts at a limit `λ`.  `ha_inv`: the invariant `Ha.HaLInv (ν+1)` at every
`ν < φ(3, G+1)`, so every `haLU λ` starts the stage `λ` and later starts extend earlier ones.

* `ha_start0`, `haLStep`, `haLExt`, `haLLimD`, `haLU` (**THE RECURSION**), `haLU_zero`, `haLU_succ`, `haLU_limit`,
  `haLU_succ_eq`, `haLU_lim_eq`, `ha_inv` (**THE INVARIANT AT EVERY `ζ`-INDEX BELOW `φ(3, G+1)`**);
* `haLU_B`, `haLU_self`, `haLPB` (the stage at `λ`), `haLU_start`, `haLU_γ_iff`, `ha_ext`, `haLD` (the systems of
  the stage `λ`), `haLD_B`.

No new axiom.  New definitions: `haLStep`, `haLExt`, `haLLimD`, `haLU`, `haLPB`, `haLD`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ha

open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

theorem ha_zero_lt_T : (0 : Ordinal.{0}) < haT := haT_E.pos

/-- **The union at `ζ_{G+1}` starts the stage `0`.** -/
theorem ha_start0 (h2 : (0 : Ordinal.{0}) < (GzVD.ofW gwZU).B) :
    HaSStart (haPBof (GzVD.ofW gwZU) 0 h2 (ha_j ha_zero_lt_T)) (GzVD.ofW gwZU) where
  ix := by
    show gwZ = veblen 2 (gcG 0 + 1 + 0)
    rw [add_zero]; exact gwZ_eq_veb2
  γ := fun x _ _ => by
    show (0 : Ordinal.{0}) < x ↔ (GzVD.ofW gwZU).g 0 < x
    rw [(GzVD.ofW gwZU).g_zero]
  b := fun x hx hx1 _ => by
    show evZ (lgG x) = glA 2 (lgG x + (GzVD.ofW gwZU).R 0 x) x
    rw [(GzVD.ofW gwZU).R_zero, add_zero]; exact (gw_glA2_eq hx hx1).symm
  Z := fun x hx hx1 => by
    have hg : (haPBof (GzVD.ofW gwZU) 0 h2 (ha_j ha_zero_lt_T)).γP < x := by
      show (GzVD.ofW gwZU).g 0 < x
      rw [(GzVD.ofW gwZU).g_zero]; exact hx.pos
    rw [HaPB.Zst_eq _ hg]
    show evZ (evZ (lgG x)) = evZ (glA 2 (lgG x + (GzVD.ofW gwZU).R 0 x) x)
    rw [(GzVD.ofW gwZU).R_zero, add_zero, gw_glA2_eq hx hx1]

/-! ## The recursion -/

/-- The successor step: the self-read union of the stage `λ` started at `U` (when `U` starts it). -/
noncomputable def haLStep (μ : Ordinal.{0}) (U : GzVD) : GzVD := by
  classical
  exact if h : ∃ (hμ : μ < haT) (h2 : μ < U.B), HaSStart (haPBof U μ h2 (ha_j hμ)) U then
    haSU h.choose_spec.choose_spec else U

/-- The family of the earlier values, extended by the start at `0`. -/
noncomputable def haLExt (l : Ordinal.{0}) (IH : ∀ β, β < l → GzVD) (β : Ordinal.{0}) : GzVD :=
  if h : β < l then IH β h else GzVD.ofW gwZU

open Classical in
/-- The limit step: the union of all earlier starts when the invariant holds. -/
noncomputable def haLLimD (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ β, β < l → GzVD) : GzVD :=
  if H : l < haT ∧ HaLInv l (haLExt l IH) then (HaLFam.mk l (haLExt l IH) hl H.1 H.2).U else GzVD.ofW gwZU

/-- **THE RECURSION OVER THE `ζ`-INDICES**: `haLU λ` is the start of the stage `λ` (the union at `ζ_{G+1+λ}`). -/
noncomputable def haLU (ν : Ordinal.{0}) : GzVD :=
  Ordinal.limitRecOn (motive := fun _ => GzVD) ν (GzVD.ofW gwZU) haLStep haLLimD

theorem haLU_zero : haLU 0 = GzVD.ofW gwZU := by unfold haLU; rw [Ordinal.limitRecOn_zero]

theorem haLU_succ (ν : Ordinal.{0}) : haLU (ν + 1) = haLStep ν (haLU ν) := by
  unfold haLU; rw [Ordinal.limitRecOn_add_one]

theorem haLU_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : haLU l = haLLimD l hl (fun β _ => haLU β) := by
  unfold haLU; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem haLExt_eq {l β : Ordinal.{0}} (h : β < l) : haLExt l (fun β _ => haLU β) β = haLU β := by
  unfold haLExt; rw [dif_pos h]

/-- The successor value when `haLU ν` starts the stage `ν`. -/
theorem haLU_succ_eq {ν : Ordinal.{0}} (hν : ν < haT) (h2 : ν < (haLU ν).B)
    (h : HaSStart (haPBof (haLU ν) ν h2 (ha_j hν)) (haLU ν)) : haLU (ν + 1) = haSU h := by
  rw [haLU_succ]; unfold haLStep
  rw [dif_pos ⟨hν, h2, h⟩]

theorem haLU_lim_eq {l : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l < haT) (H : HaLInv l haLU) :
    haLU l = (HaLFam.mk l (haLExt l fun β _ => haLU β) hl hle (H.congr fun β h => haLExt_eq h)).U := by
  rw [haLU_limit hl]; unfold haLLimD; rw [dif_pos ⟨hle, H.congr fun β h => haLExt_eq h⟩]

theorem ha_B_of_start {D : GzVD} {Bp : HaPB} (h : HaSStart Bp D) : D.B = Bp.Q := by
  rw [D.B_ix, h.ix]; exact Bp.Q_fix

/-- **THE INVARIANT**: every `haLU λ`, `λ < φ(3, G+1)`, starts the stage `λ`, the starts at successors have the
high-gate property, and later starts extend earlier ones. -/
theorem ha_inv : ∀ ν : Ordinal.{0}, ν < haT → HaLInv (ν + 1) haLU := by
  intro ν
  induction ν using Ordinal.limitRecOn with
  | zero =>
    intro _
    have h0 : ∀ μ : Ordinal.{0}, μ < 0 + 1 → μ = 0 := fun μ h => Order.lt_one_iff.1 (by rwa [zero_add] at h)
    have hB0 : (0 : Ordinal.{0}) < (haLU 0).B := by rw [haLU_zero]; exact (GzVD.ofW gwZU).B_pos
    have hst0 : HaSStart (haPBof (haLU 0) 0 hB0 (ha_j ha_zero_lt_T)) (haLU 0) :=
      ha_st_congr haLU_zero hB0 _ (fun h2' => ha_start0 h2')
    refine ⟨fun μ h => ?_, fun μ hμ h h2 => ?_, fun μ h => ?_, fun β γ hβγ h c x _ => ?_, fun β γ hβγ h c _ => ?_⟩
    · rw [h0 μ h, ha_B_of_start hst0]; rfl
    · obtain rfl := h0 μ h; exact hst0
    · exact absurd (h0 (μ + 1) h) (ne_of_gt (lt_of_le_of_lt zero_le (lt_add_one μ)))
    · have hγ := h0 γ h
      have hβ : β = 0 := le_antisymm (hγ ▸ hβγ) zero_le
      rw [hγ, hβ]
    · have hγ := h0 γ h
      have hβ : β = 0 := le_antisymm (hγ ▸ hβγ) zero_le
      rw [hγ, hβ]
  | add_one μ ih =>
    intro hν
    have hμT : μ < haT := (lt_add_one μ).trans hν
    have H := ih hμT
    have h2 : μ < (haLU μ).B := H.self_lt (lt_add_one μ) hμT
    have hst := H.st μ hμT (lt_add_one μ) h2
    set Bp := haPBof (haLU μ) μ h2 (ha_j hμT) with hBp
    have e := haLU_succ_eq hμT h2 hst
    have hBμ : (haLU μ).B = Bp.Q := H.B μ (lt_add_one μ)
    have hB1 : (haLU (μ + 1)).B = veblen 2 (gcG 0 + 1 + (μ + 1)) := by
      rw [e, haSU_B, Bp.evQ]
      show veblen 2 (gcG 0 + 1 + μ + 1) = veblen 2 (gcG 0 + 1 + (μ + 1))
      rw [add_assoc (gcG 0 + 1) μ 1]
    have h1B : μ + 1 < (haLU μ).B := (ev_isSuccLimit_of_inE (haLU μ).B_E).add_one_lt h2
    have hext : ∀ c x, c < (haLU μ).B → (haLU (μ + 1)).R c x = (haLU μ).R c x := fun c x hc => by
      rw [e, haSU_R hst (haS_zero_lt2 (Bp := Bp)) (by rw [haSD_zero]; exact hc) x, haSD_zero]
    have hextg : ∀ c, c < (haLU μ).B → (haLU (μ + 1)).g c = (haLU μ).g c := fun c hc => by
      rw [e, haSU_g hst (haS_zero_lt2 (Bp := Bp)) (by rw [haSD_zero]; exact hc), haSD_zero]
    have hstS : ∀ h2' : μ + 1 < (haLU (μ + 1)).B,
        HaSStart (haPBof (haLU (μ + 1)) (μ + 1) h2' (ha_j hν)) (haLU (μ + 1)) := fun h2' => by
      refine ha_st_congr e h2' (ha_j hν) (fun h2'' => haSU_start hst _ ?_ ?_ ?_)
      · show veblen 2 (gcG 0 + 1 + (μ + 1)) = evZ (veblen 2 (gcG 0 + 1 + μ))
        rw [gz_evZ_veb2, add_assoc (gcG 0 + 1) μ 1]
      · intro x hx hx1
        show (haLU μ).g μ < x ↔ (haSU hst).g (μ + 1) < x
        rw [← e, hextg (μ + 1) h1B]
        exact ⟨fun h => (haLU μ).g_succ x (ev_isSuccLimit_of_inE hx) μ h1B h,
          fun h => ((haLU μ).g_le_succ μ).trans_lt h⟩
      · intro x hx hx1 hγ
        have hg1 : (haLU μ).g (μ + 1) < x := by
          have : (haSU hst).g (μ + 1) < x := hγ
          rw [← e, hextg (μ + 1) h1B] at this; exact this
        have hg : Bp.γP < x := ((haLU μ).g_le_succ μ).trans_lt hg1
        show glA 2 (lgG x + (haSU hst).R (μ + 1) x) x = evZ (glA 2 (lgG x + (haLU μ).R μ x) x)
        rw [← e, hext (μ + 1) x h1B, (haLU μ).R_succ, ← add_assoc]
        exact gz_glA2_succ hx hx1 (Bp.tP_lt x hx hx1 hg)
    refine ⟨fun β h => ?_, fun β hβ h h2' => ?_, fun β h c σ h1 h2' hσ hσ1 hg => ?_,
      fun β γ hβγ h c x hc => ?_, fun β γ hβγ h c hc => ?_⟩
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.B β h'
      · exact hB1
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.st β hβ h' h2'
      · exact hstS h2'
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | h'
      · exact H.high β h' c σ h1 h2' hσ hσ1 hg
      · have hβμ : β = μ := Order.succ_injective (by rw [Order.succ_eq_add_one, Order.succ_eq_add_one]; exact h')
        subst hβμ
        rw [e] at h2' hg ⊢
        refine haSU_high_gate hst h2' ?_ hσ hσ1 hg
        rw [← hBμ]; exact h1
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.cohR β γ hβγ h' c x hc
      · rcases hβγ.lt_or_eq with h'' | rfl
        · have hβμ : β ≤ μ := Order.lt_add_one_iff.1 h''
          have hcμ : c < (haLU μ).B := hc.trans_le (by
            rw [H.B β (lt_of_le_of_lt hβμ (lt_add_one μ)), H.B μ (lt_add_one μ)]
            exact (isNormal_veblen 2).monotone ((add_le_add_iff_left _).2 hβμ))
          rw [hext c x hcμ]; exact H.cohR β μ hβμ (lt_add_one μ) c x hc
        · rfl
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.cohg β γ hβγ h' c hc
      · rcases hβγ.lt_or_eq with h'' | rfl
        · have hβμ : β ≤ μ := Order.lt_add_one_iff.1 h''
          have hcμ : c < (haLU μ).B := hc.trans_le (by
            rw [H.B β (lt_of_le_of_lt hβμ (lt_add_one μ)), H.B μ (lt_add_one μ)]
            exact (isNormal_veblen 2).monotone ((add_le_add_iff_left _).2 hβμ))
          rw [hextg c hcμ]; exact H.cohg β μ hβμ (lt_add_one μ) c hc
        · rfl
  | limit l hl ih =>
    intro hν
    have hIH : ∀ β, β < l → HaLInv (β + 1) haLU := fun β h => ih β h (h.trans hν)
    have H : HaLInv l haLU := ⟨fun μ h => (hIH μ h).B μ (lt_add_one μ),
      fun μ hμ h => (hIH μ h).st μ hμ (lt_add_one μ),
      fun μ h => (hIH (μ + 1) h).high μ (lt_add_one _),
      fun β γ hβγ h => (hIH γ h).cohR β γ hβγ (lt_add_one γ),
      fun β γ hβγ h => (hIH γ h).cohg β γ hβγ (lt_add_one γ)⟩
    have e := haLU_lim_eq hl hν H
    set L := HaLFam.mk l (haLExt l fun β _ => haLU β) hl hν (H.congr fun β h => haLExt_eq h) with hL
    have hF : ∀ β, β < l → L.F β = haLU β := fun β h => haLExt_eq h
    refine ⟨fun β h => ?_, fun β hβ h h2' => ?_, fun β h c σ h1 h2' hσ hσ1 hg => ?_,
      fun β γ hβγ h c x hc => ?_, fun β γ hβγ h c hc => ?_⟩
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.B β h'
      · rw [e]; rfl
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.st β hβ h' h2'
      · exact ha_st_congr e h2' (ha_j hβ) (fun _ => L.U_start)
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | h'
      · exact H.high β h' c σ h1 h2' hσ hσ1 hg
      · exfalso
        rw [← h', ← Order.succ_eq_add_one] at hl
        exact Order.not_isSuccLimit_succ β hl
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.cohR β γ hβγ h' c x hc
      · rcases hβγ.lt_or_eq with h'' | rfl
        · rw [e, L.U_R h'' (by rw [hF β h'']; exact hc) x, hF β h'']
        · rfl
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.cohg β γ hβγ h' c hc
      · rcases hβγ.lt_or_eq with h'' | rfl
        · rw [e, L.U_g h'' (by rw [hF β h'']; exact hc), hF β h'']
        · rfl

/-! ## The main facts -/

section Main

variable {l : Ordinal.{0}} (hl : l < haT)
include hl

/-- **The bound of `haLU λ` is `Q_λ = φ(2, G + 1 + λ)`.** -/
theorem haLU_B : (haLU l).B = veblen 2 (gcG 0 + 1 + l) := (ha_inv l hl).B l (lt_add_one l)

theorem haLU_self : l < (haLU l).B := (ha_inv l hl).self_lt (lt_add_one l) hl

end Main

/-- **The stage at the `ζ`-index `λ`**, `λ` read by `haLU λ`. -/
noncomputable def haLPB (l : Ordinal.{0}) (hl : l < haT) : HaPB := haPBof (haLU l) l (haLU_self hl) (ha_j hl)

/-- **`haLU λ` STARTS THE STAGE `λ`** for every `λ < φ(3, G+1)`. -/
theorem haLU_start {l : Ordinal.{0}} (hl : l < haT) : HaSStart (haLPB l hl) (haLU l) :=
  (ha_inv l hl).st l hl (lt_add_one l) (haLU_self hl)

/-- **The base gate of `haLU λ` lies below a base `x` iff the gate of the code `λ` does.** -/
theorem haLU_γ_iff {l x : Ordinal.{0}} (hl : l < haT) (hx : InE x) (hx1 : x < Om1) :
    (haLU l).γ < x ↔ (haLU l).g l < x := (haLU_start hl).γ x hx hx1

/-- **Later starts extend earlier ones.** -/
theorem ha_ext {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (hγ : γ < haT) :
    (∀ c x, c < (haLU β).B → (haLU γ).R c x = (haLU β).R c x) ∧
    (∀ c, c < (haLU β).B → (haLU γ).g c = (haLU β).g c) :=
  ⟨(ha_inv γ hγ).cohR β γ hβγ (lt_add_one γ), (ha_inv γ hγ).cohg β γ hβγ (lt_add_one γ)⟩

/-- **The systems of the stage `λ`**: `haLD λ d` has the bound `ε_{Q_λ+d}` (`d < evZ(Q_λ)`). -/
noncomputable def haLD (l : Ordinal.{0}) (hl : l < haT) (d : Ordinal.{0}) : GzVD := haSD (haLPB l hl) (haLU l) d

theorem haLD_B {l d : Ordinal.{0}} (hl : l < haT) (hd : d < evZ (haLPB l hl).Q) :
    (haLD l hl d).B = veblen 1 ((haLPB l hl).Q + d) := haS_B (haLU_start hl) hd

end Googology.Trans.PoR.InaccPsi.R2.Ha
