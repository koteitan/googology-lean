import Googology.Trans.PoR.InaccPsi.R2.HdLv

/-!
# HdLvRec: THE GATED RECURSION OVER THE OFFSETS OF A BASE OF LEVEL `ω`

The level-`ω` version of `Hc.HcLvRec`, with the gated `ω`-step `Hd.hdStep` as the step.  For a base `A : Hd.HdA`
of level `ω` and a start `S0` (`HdLvStart A S0`: bound `φ(ω, F+1)`, bound field below `Z_l`, starts the stage at the
offset `0`, high-gate property), `hdLvU A S0 λ` (`λ < N_ω(F)`, every `λ`, read by a code with a gate) is the start of
the stage at the offset `λ`: `S0` at `0`, the `ω`-step at the gated offset pseudo-base `Hd.hdOff A (hdLvU λ) λ` at
`λ+1`, the union `Hd.HdLvFam.U` at a limit.  `hdLv_inv`: the invariant `Hd.HdLvInv A (ν+1)` at every `ν < N_ω(F)`.

* `hdLv_zero_lt_N`, `HdLvStart`, `hdLvStep`, `hdLvExt`, `hdLvLimD`, `hdLvU` (**THE GATED OFFSET RECURSION OF LEVEL
  `ω`**), `hdLv_inv` (**THE INVARIANT**), `hdLvU_B`, `hdLvU_self`, `hdLvU_Zb`, `hdLvU_start`, `hdLvU_γ_iff`,
  `hdLv_ext`, `hdLvU_succ_spec`.

No new axiom.  New definitions: `HdLvStart`, `hdLvStep`, `hdLvExt`, `hdLvLimD`, `hdLvU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hd

open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

theorem hdLv_zero_lt_N (A : HdA) : (0 : Ordinal.{0}) < hcNw A.F := A.N_E.pos

/-- **The start conditions** of the recursion over `A` at `S0`. -/
structure HdLvStart (A : HdA) (S0 : HcVD) : Prop where
  B : S0.B = veblen ω (A.F + 1 + 0)
  Zb : ∀ x, InE x → x < Om1 → S0.Z x ≤ A.Zl x
  st : ∀ (h2 : 0 < S0.B) (hZ : ∀ x, InE x → x < Om1 → S0.Z x ≤ A.Zl x),
    HcSStart (hdLvPB A S0 0 h2 (hdLv_zero_lt_N A) hZ) S0
  high0 : ∀ c σ, A.F ≤ c → c < S0.B → InE σ → σ < Om1 → S0.g c < σ → A.γ < σ

section Rec

variable (A : HdA) (S0 : HcVD)

/-- The successor step: the `ω`-step at the offset pseudo-base `λ` started at `U` (when `U` starts it). -/
noncomputable def hdLvStep (μ : Ordinal.{0}) (U : HcVD) : HcVD := by
  classical
  exact if h : ∃ (hμ : μ < hcNw A.F) (h2 : μ < U.B) (hZ : ∀ x, InE x → x < Om1 → U.Z x ≤ A.Zl x),
      HcSStart (hdLvPB A U μ h2 hμ hZ) U then
    hdStep (hdOff A U μ h.choose_spec.choose h.choose h.choose_spec.choose_spec.choose) U
      h.choose_spec.choose_spec.choose_spec else U

/-- The family of the earlier values, extended by the start at `0`. -/
noncomputable def hdLvExt (l : Ordinal.{0}) (IH : ∀ β, β < l → HcVD) (β : Ordinal.{0}) : HcVD :=
  if h : β < l then IH β h else S0

open Classical in
/-- The limit step: the union of all earlier starts when the invariant holds. -/
noncomputable def hdLvLimD (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ β, β < l → HcVD) : HcVD :=
  if H : l < hcNw A.F ∧ HdLvInv A l (hdLvExt S0 l IH) then
    (HdLvFam.mk l (hdLvExt S0 l IH) hl H.1 H.2).U else S0

/-- **THE GATED OFFSET RECURSION OF LEVEL `ω`.** -/
noncomputable def hdLvU (ν : Ordinal.{0}) : HcVD :=
  Ordinal.limitRecOn (motive := fun _ => HcVD) ν S0 (hdLvStep A) (hdLvLimD A S0)

theorem hdLvU_zero : hdLvU A S0 0 = S0 := by unfold hdLvU; rw [Ordinal.limitRecOn_zero]

theorem hdLvU_succ (ν : Ordinal.{0}) : hdLvU A S0 (ν + 1) = hdLvStep A ν (hdLvU A S0 ν) := by
  unfold hdLvU; rw [Ordinal.limitRecOn_add_one]

theorem hdLvU_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) :
    hdLvU A S0 l = hdLvLimD A S0 l hl (fun β _ => hdLvU A S0 β) := by
  unfold hdLvU; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem hdLvExt_eq {l β : Ordinal.{0}} (h : β < l) :
    hdLvExt S0 l (fun β _ => hdLvU A S0 β) β = hdLvU A S0 β := by
  unfold hdLvExt; rw [dif_pos h]

/-- The successor value when `hdLvU ν` starts the stage at the offset `ν`. -/
theorem hdLvU_succ_eq {ν : Ordinal.{0}} (hν : ν < hcNw A.F) (h2 : ν < (hdLvU A S0 ν).B)
    (hZ : ∀ x, InE x → x < Om1 → (hdLvU A S0 ν).Z x ≤ A.Zl x)
    (h : HcSStart (hdLvPB A (hdLvU A S0 ν) ν h2 hν hZ) (hdLvU A S0 ν)) :
    hdLvU A S0 (ν + 1) = hdStep (hdOff A (hdLvU A S0 ν) ν h2 hν hZ) (hdLvU A S0 ν) h := by
  rw [hdLvU_succ]; unfold hdLvStep
  rw [dif_pos ⟨hν, h2, hZ, h⟩]

theorem hdLvU_lim_eq {l : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l < hcNw A.F)
    (H : HdLvInv A l (hdLvU A S0)) :
    hdLvU A S0 l = (HdLvFam.mk l (hdLvExt S0 l fun β _ => hdLvU A S0 β) hl hle
      (H.congr fun β h => hdLvExt_eq A S0 h)).U := by
  rw [hdLvU_limit A S0 hl]; unfold hdLvLimD; rw [dif_pos ⟨hle, H.congr fun β h => hdLvExt_eq A S0 h⟩]

end Rec

/-- **THE INVARIANT**: every `hdLvU A S0 λ`, `λ < N_ω(F)`, starts the stage at the offset `λ`, has bound field
below `Z_l`, the starts at successors have the high-gate property, and later starts extend earlier ones. -/
theorem hdLv_inv {A : HdA} {S0 : HcVD} (hS : HdLvStart A S0) :
    ∀ ν : Ordinal.{0}, ν < hcNw A.F → HdLvInv A (ν + 1) (hdLvU A S0) := by
  intro ν
  induction ν using Ordinal.limitRecOn with
  | zero =>
    intro _
    have h0 : ∀ μ : Ordinal.{0}, μ < 0 + 1 → μ = 0 := fun μ h => Order.lt_one_iff.1 (by rwa [zero_add] at h)
    refine ⟨fun μ h => ?_, fun μ h => ?_, fun μ hμ h h2 hZ => ?_, fun μ h => ?_, fun β γ hβγ h c x _ => ?_,
      fun β γ hβγ h c _ => ?_⟩
    · rw [h0 μ h, hdLvU_zero]; exact hS.B
    · rw [h0 μ h, hdLvU_zero]; exact hS.Zb
    · obtain rfl := h0 μ h
      exact hdLv_st_congr (hdLvU_zero A S0) h2 hμ hZ (fun h2' hZ' => hS.st h2' hZ')
    · exact absurd (h0 (μ + 1) h) (ne_of_gt (lt_of_le_of_lt zero_le (lt_add_one μ)))
    · have hγ := h0 γ h
      have hβ : β = 0 := le_antisymm (hγ ▸ hβγ) zero_le
      rw [hγ, hβ]
    · have hγ := h0 γ h
      have hβ : β = 0 := le_antisymm (hγ ▸ hβγ) zero_le
      rw [hγ, hβ]
  | add_one μ ih =>
    intro hν
    have hμT : μ < hcNw A.F := (lt_add_one μ).trans hν
    have H := ih hμT
    have h2 : μ < (hdLvU A S0 μ).B := H.self_lt (lt_add_one μ) hμT
    have hZ := H.Zb μ (lt_add_one μ)
    have hst := H.st μ hμT (lt_add_one μ) h2 hZ
    set X := hdOff A (hdLvU A S0 μ) μ h2 hμT hZ with hX
    have e := hdLvU_succ_eq A S0 hμT h2 hZ hst
    have hsp := hdStep_spec X (hdLvU A S0 μ) hst
    have hBμ : (hdLvU A S0 μ).B = X.F := H.B μ (lt_add_one μ)
    have hB1 : (hdLvU A S0 (μ + 1)).B = veblen ω (A.F + 1 + (μ + 1)) := by
      rw [e, hsp.B]
      show hcS (veblen ω (A.F + 1 + μ)) = _
      rw [hcS_veb_eq, add_assoc (A.F + 1) μ 1]
    have hZ1 : ∀ x, InE x → x < Om1 → (hdLvU A S0 (μ + 1)).Z x ≤ A.Zl x := fun x hx hx1 => by
      rw [e, hsp.Z x hx hx1]
      split_ifs with hγ
      · exact (hb_evZ_lt_fix2 (A.Zl_fix x) (X.S_Zo hx hx1 hγ)).le
      · exact le_rfl
    have h1B : μ + 1 < (hdLvU A S0 μ).B := (ev_isSuccLimit_of_inE (hdLvU A S0 μ).B_E).add_one_lt h2
    have hext : ∀ c x, c < (hdLvU A S0 μ).B → (hdLvU A S0 (μ + 1)).R c x = (hdLvU A S0 μ).R c x :=
      fun c x hc => by rw [e]; exact hsp.extR c x hc
    have hextg : ∀ c, c < (hdLvU A S0 μ).B → (hdLvU A S0 (μ + 1)).g c = (hdLvU A S0 μ).g c :=
      fun c hc => by rw [e]; exact hsp.extg c hc
    have hgiff : ∀ x, InE x → x < Om1 → ((hdLvU A S0 μ).g μ < x ↔ (hdLvU A S0 μ).g (μ + 1) < x) :=
      fun x hx _ => ⟨fun h => (hdLvU A S0 μ).g_succ x (ev_isSuccLimit_of_inE hx) μ h1B h,
        fun h => ((hdLvU A S0 μ).g_le_succ μ).trans_lt h⟩
    have hFr1 : ∀ x, InE x → x < Om1 → X.γ < x →
        glA ω (A.Fr x + (hdLvU A S0 (μ + 1)).R (μ + 1) x) x =
          hcS (X.Fr x) := fun x hx hx1 hγ => by
      rw [hext (μ + 1) x h1B, (hdLvU A S0 μ).R_succ, ← add_assoc]
      exact hd_glA_succ hx hx1 (A.t1_lt1 hx hx1 (max_lt_iff.1 hγ).1 (hdOff_R_lt A _ μ h2 hZ hx hx1 hγ))
    have hstS : ∀ (h2' : μ + 1 < (hdLvU A S0 (μ + 1)).B) (hZ' : ∀ x, InE x → x < Om1 →
        (hdLvU A S0 (μ + 1)).Z x ≤ A.Zl x),
        HcSStart (hdLvPB A (hdLvU A S0 (μ + 1)) (μ + 1) h2' hν hZ') (hdLvU A S0 (μ + 1)) := fun h2' hZ' => by
      have hγiff : ∀ x, InE x → x < Om1 →
          ((hdLvU A S0 (μ + 1)).γ < x ↔ max A.γ ((hdLvU A S0 (μ + 1)).g (μ + 1)) < x) := fun x hx hx1 => by
        rw [e, hsp.γ]
        show max A.γ ((hdLvU A S0 μ).g μ) < x ↔ max A.γ ((hdStep X _ hst).g (μ + 1)) < x
        rw [← e, hextg (μ + 1) h1B, max_lt_iff, max_lt_iff]
        exact and_congr_right fun _ => hgiff x hx hx1
      refine ⟨?_, hγiff, fun x hx hx1 hγ => ?_, fun x hx hx1 => ?_⟩
      · refine hc_ix_of_B ?_ hB1
        exact hd_veb_fix1 _
      · have hγ' : X.γ < x := by
          have := (hγiff x hx hx1).2 hγ; rw [e, hsp.γ] at this; exact this
        show (hdLvU A S0 (μ + 1)).b x = glA ω (A.Fr x + (hdLvU A S0 (μ + 1)).R
            (μ + 1) x) x
        rw [hFr1 x hx hx1 hγ', e]; exact hsp.b x hx hx1 hγ'
      · show (hdLvU A S0 (μ + 1)).Z x = HcPB.Zst (hdLvPB A (hdLvU A S0 (μ + 1)) (μ + 1) h2' hν hZ') x
        unfold HcPB.Zst
        have hZe := hsp.Z x hx hx1
        rw [← e] at hZe
        rw [hZe]
        show (if X.γ < x then evZ (hcS (X.Fr x)) else A.Zl x) =
          if max A.γ ((hdLvU A S0 (μ + 1)).g (μ + 1)) < x then
            evZ (glA ω (A.Fr x + (hdLvU A S0 (μ + 1)).R (μ + 1) x) x) else A.Zl x
        have hiff : X.γ < x ↔ max A.γ ((hdLvU A S0 (μ + 1)).g (μ + 1)) < x := by
          rw [← hγiff x hx hx1, e, hsp.γ]
        by_cases hγ : X.γ < x
        · rw [if_pos hγ, if_pos (hiff.1 hγ), hFr1 x hx hx1 hγ]
        · rw [if_neg hγ, if_neg (fun h => hγ (hiff.2 h))]
    refine ⟨fun β h => ?_, fun β h => ?_, fun β hβ h h2' hZ' => ?_, fun β h c σ h1 h2' hσ hσ1 hg => ?_,
      fun β γ hβγ h c x hc => ?_, fun β γ hβγ h c hc => ?_⟩
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.B β h'
      · exact hB1
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.Zb β h'
      · exact hZ1
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.st β hβ h' h2' hZ'
      · exact hstS h2' hZ'
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | h'
      · exact H.high β h' c σ h1 h2' hσ hσ1 hg
      · have hβμ : β = μ := Order.succ_injective (by rw [Order.succ_eq_add_one, Order.succ_eq_add_one]; exact h')
        subst hβμ
        rw [e] at h2' hg ⊢
        rw [hsp.γ]
        refine hsp.high c σ (by rw [← hBμ]; exact h1) ?_ hσ hσ1 hg
        rw [← hsp.B]; exact h2'
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.cohR β γ hβγ h' c x hc
      · rcases hβγ.lt_or_eq with h'' | rfl
        · have hβμ : β ≤ μ := Order.lt_add_one_iff.1 h''
          have hcμ : c < (hdLvU A S0 μ).B := hc.trans_le (by
            rw [H.B β (lt_of_le_of_lt hβμ (lt_add_one μ)), H.B μ (lt_add_one μ)]
            exact (isNormal_veblen _).monotone ((add_le_add_iff_left _).2 hβμ))
          rw [hext c x hcμ]; exact H.cohR β μ hβμ (lt_add_one μ) c x hc
        · rfl
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.cohg β γ hβγ h' c hc
      · rcases hβγ.lt_or_eq with h'' | rfl
        · have hβμ : β ≤ μ := Order.lt_add_one_iff.1 h''
          have hcμ : c < (hdLvU A S0 μ).B := hc.trans_le (by
            rw [H.B β (lt_of_le_of_lt hβμ (lt_add_one μ)), H.B μ (lt_add_one μ)]
            exact (isNormal_veblen _).monotone ((add_le_add_iff_left _).2 hβμ))
          rw [hextg c hcμ]; exact H.cohg β μ hβμ (lt_add_one μ) c hc
        · rfl
  | limit l hl ih =>
    intro hν
    have hIH : ∀ β, β < l → HdLvInv A (β + 1) (hdLvU A S0) := fun β h => ih β h (h.trans hν)
    have H : HdLvInv A l (hdLvU A S0) := ⟨fun μ h => (hIH μ h).B μ (lt_add_one μ),
      fun μ h => (hIH μ h).Zb μ (lt_add_one μ),
      fun μ hμ h => (hIH μ h).st μ hμ (lt_add_one μ),
      fun μ h => (hIH (μ + 1) h).high μ (lt_add_one _),
      fun β γ hβγ h => (hIH γ h).cohR β γ hβγ (lt_add_one γ),
      fun β γ hβγ h => (hIH γ h).cohg β γ hβγ (lt_add_one γ)⟩
    have e := hdLvU_lim_eq A S0 hl hν H
    set L := HdLvFam.mk l (hdLvExt S0 l fun β _ => hdLvU A S0 β) hl hν (H.congr fun β h => hdLvExt_eq A S0 h)
      with hL
    have hF : ∀ β, β < l → L.F β = hdLvU A S0 β := fun β h => hdLvExt_eq A S0 h
    refine ⟨fun β h => ?_, fun β h => ?_, fun β hβ h h2' hZ' => ?_, fun β h c σ h1 h2' hσ hσ1 hg => ?_,
      fun β γ hβγ h c x hc => ?_, fun β γ hβγ h c hc => ?_⟩
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.B β h'
      · rw [e]; rfl
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.Zb β h'
      · rw [e]; exact L.U_Zb
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.st β hβ h' h2' hZ'
      · exact hdLv_st_congr e h2' hβ hZ' (fun _ _ => L.U_start)
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

variable {A : HdA} {S0 : HcVD} (hS : HdLvStart A S0)
include hS

theorem hdLvU_B {l : Ordinal.{0}} (hl : l < hcNw A.F) :
    (hdLvU A S0 l).B = veblen ω (A.F + 1 + l) :=
  (hdLv_inv hS l hl).B l (lt_add_one l)

theorem hdLvU_self {l : Ordinal.{0}} (hl : l < hcNw A.F) : l < (hdLvU A S0 l).B :=
  (hdLv_inv hS l hl).self_lt (lt_add_one l) hl

theorem hdLvU_Zb {l : Ordinal.{0}} (hl : l < hcNw A.F) :
    ∀ x, InE x → x < Om1 → (hdLvU A S0 l).Z x ≤ A.Zl x :=
  (hdLv_inv hS l hl).Zb l (lt_add_one l)

/-- **`hdLvU λ` STARTS THE STAGE AT THE OFFSET `λ`.** -/
theorem hdLvU_start {l : Ordinal.{0}} (hl : l < hcNw A.F) :
    HcSStart (hdLvPB A (hdLvU A S0 l) l (hdLvU_self hS hl) hl (hdLvU_Zb hS hl)) (hdLvU A S0 l) :=
  (hdLv_inv hS l hl).st l hl (lt_add_one l) (hdLvU_self hS hl) (hdLvU_Zb hS hl)

/-- **The base gate of `hdLvU λ` lies below a base `x` iff `max(γ, g(λ))` does.** -/
theorem hdLvU_γ_iff {l x : Ordinal.{0}} (hl : l < hcNw A.F) (hx : InE x) (hx1 : x < Om1) :
    (hdLvU A S0 l).γ < x ↔ max A.γ ((hdLvU A S0 l).g l) < x := (hdLvU_start hS hl).γ x hx hx1

/-- **Later starts extend earlier ones.** -/
theorem hdLv_ext {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (hγ : γ < hcNw A.F) :
    (∀ c x, c < (hdLvU A S0 β).B → (hdLvU A S0 γ).R c x = (hdLvU A S0 β).R c x) ∧
    (∀ c, c < (hdLvU A S0 β).B → (hdLvU A S0 γ).g c = (hdLvU A S0 β).g c) :=
  ⟨(hdLv_inv hS γ hγ).cohR β γ hβγ (lt_add_one γ), (hdLv_inv hS γ hγ).cohg β γ hβγ (lt_add_one γ)⟩

/-- **The specification of the successor**: `hdLvU (λ+1)` is the step at the offset `λ`. -/
theorem hdLvU_succ_spec {l : Ordinal.{0}} (hl : l < hcNw A.F) :
    HdSpec (hdOff A (hdLvU A S0 l) l (hdLvU_self hS hl) hl (hdLvU_Zb hS hl)) (hdLvU A S0 l)
      (hdLvU A S0 (l + 1)) := by
  rw [hdLvU_succ_eq A S0 hl (hdLvU_self hS hl) (hdLvU_Zb hS hl) (hdLvU_start hS hl)]
  exact hdStep_spec _ _ _

end Main

end Googology.Trans.PoR.InaccPsi.R2.Hd
