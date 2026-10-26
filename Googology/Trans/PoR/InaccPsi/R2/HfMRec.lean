import Googology.Trans.PoR.InaccPsi.R2.HfMLv

/-!
# HfMRec: THE GATED RECURSION OVER THE OFFSETS OF A BASE OF EVERY COUNTABLE LEVEL `α`, FOR ANY STEP OF LEVEL `α`

The level-`α` version of `Hd.HdLvRec`, for any step `St` of level `α` with the specification `Hf.HfQSpec` (bound
`hdNx α F`).  For a base `A : Hf.HfB α` and a start `S0` (`HfMStart A S0`), `hfMU St A S0 λ` (`λ < N_α(F)`, read by
a code with a gate) is the start of the stage at the offset `λ`: `S0` at `0`, `St` at the gated offset pseudo-base
`Hf.hfQOff A (hfMU λ) λ` at `λ+1`, the union `Hf.HfMFam.U` at a limit.  `hfM_inv`: the invariant `HfMInv A (ν+1)` at
every `ν < N_α(F)`.  The start condition `high0` asks only the CODE GATE `γ` of `A` (a code `c ∈ [F, S0.B)` with
gate below `σ` forces `γ < σ`), so it holds at `G` (code gate `0`) for every level.

* `hfM_zero_lt_N`, `HfMStart`, `hfMStep`, `hfMExt`, `hfMLimD`, `hfMU` (**THE GATED OFFSET RECURSION, EVERY COUNTABLE
  LEVEL**), `hfM_inv` (**THE INVARIANT**), `hfMU_B`, `hfMU_self`, `hfMU_Zb`, `hfMU_start`, `hfMU_γ_iff`, `hfM_ext`,
  `hfMU_succ_spec`.

No new axiom.  New definitions: `HfMStart`, `hfMStep`, `hfMExt`, `hfMLimD`, `hfMU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hf

open Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He

open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

theorem hfM_zero_lt_N {α : Ordinal.{0}} (A : HfB α) : (0 : Ordinal.{0}) < hcN α A.F := A.N_E.pos

/-- **The start conditions** of the recursion over `A` at `S0`. -/
structure HfMStart {α : Ordinal.{0}} (A : HfB α) (S0 : HcVD) : Prop where
  B : S0.B = veblen α (A.F + 1 + 0)
  Zb : ∀ x, InE x → x < Om1 → S0.Z x ≤ A.Zl x
  st : ∀ (h2 : 0 < S0.B) (hZ : ∀ x, InE x → x < Om1 → S0.Z x ≤ A.Zl x),
    HcSStart (hfMPB A S0 0 h2 (hfM_zero_lt_N A) hZ) S0
  high0 : ∀ c σ, A.F ≤ c → c < S0.B → InE σ → σ < Om1 → S0.g c < σ → A.γ < σ

section Rec

variable {α : Ordinal.{0}} (St : ∀ (Q : HfQ α) (U : HcVD), HcSStart (hfQPB Q) U → HcVD) (A : HfB α) (S0 : HcVD)

/-- The successor step: the step `St` at the offset pseudo-base `λ` started at `U` (when `U` starts it). -/
noncomputable def hfMStep (μ : Ordinal.{0}) (U : HcVD) : HcVD := by
  classical
  exact if h : ∃ (hμ : μ < hcN α A.F) (h2 : μ < U.B) (hZ : ∀ x, InE x → x < Om1 → U.Z x ≤ A.Zl x),
      HcSStart (hfMPB A U μ h2 hμ hZ) U then
    St (hfQOff A U μ h.choose_spec.choose h.choose h.choose_spec.choose_spec.choose) U
      h.choose_spec.choose_spec.choose_spec else U

/-- The family of the earlier values, extended by the start at `0`. -/
noncomputable def hfMExt (l : Ordinal.{0}) (IH : ∀ β, β < l → HcVD) (β : Ordinal.{0}) : HcVD :=
  if h : β < l then IH β h else S0

open Classical in
/-- The limit step: the union of all earlier starts when the invariant holds. -/
noncomputable def hfMLimD (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ β, β < l → HcVD) : HcVD :=
  if H : l < hcN α A.F ∧ HfMInv A l (hfMExt S0 l IH) then
    (HfMFam.mk l (hfMExt S0 l IH) hl H.1 H.2).U else S0

/-- **THE GATED OFFSET RECURSION, EVERY COUNTABLE LEVEL `α`.** -/
noncomputable def hfMU (ν : Ordinal.{0}) : HcVD :=
  Ordinal.limitRecOn (motive := fun _ => HcVD) ν S0 (hfMStep St A) (hfMLimD A S0)

theorem hfMU_zero : hfMU St A S0 0 = S0 := by unfold hfMU; rw [Ordinal.limitRecOn_zero]

theorem hfMU_succ (ν : Ordinal.{0}) : hfMU St A S0 (ν + 1) = hfMStep St A ν (hfMU St A S0 ν) := by
  unfold hfMU; rw [Ordinal.limitRecOn_add_one]

theorem hfMU_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) :
    hfMU St A S0 l = hfMLimD A S0 l hl (fun β _ => hfMU St A S0 β) := by
  unfold hfMU; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem hfMExt_eq {l β : Ordinal.{0}} (h : β < l) :
    hfMExt S0 l (fun β _ => hfMU St A S0 β) β = hfMU St A S0 β := by
  unfold hfMExt; rw [dif_pos h]

/-- The successor value when `hfMU ν` starts the stage at the offset `ν`. -/
theorem hfMU_succ_eq {ν : Ordinal.{0}} (hν : ν < hcN α A.F) (h2 : ν < (hfMU St A S0 ν).B)
    (hZ : ∀ x, InE x → x < Om1 → (hfMU St A S0 ν).Z x ≤ A.Zl x)
    (h : HcSStart (hfMPB A (hfMU St A S0 ν) ν h2 hν hZ) (hfMU St A S0 ν)) :
    hfMU St A S0 (ν + 1) = St (hfQOff A (hfMU St A S0 ν) ν h2 hν hZ) (hfMU St A S0 ν) h := by
  rw [hfMU_succ]; unfold hfMStep
  rw [dif_pos ⟨hν, h2, hZ, h⟩]

theorem hfMU_lim_eq {l : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l < hcN α A.F)
    (H : HfMInv A l (hfMU St A S0)) :
    hfMU St A S0 l = (HfMFam.mk l (hfMExt S0 l fun β _ => hfMU St A S0 β) hl hle
      (H.congr fun β h => hfMExt_eq St A S0 h)).U := by
  rw [hfMU_limit St A S0 hl]; unfold hfMLimD; rw [dif_pos ⟨hle, H.congr fun β h => hfMExt_eq St A S0 h⟩]

end Rec

/-- **THE INVARIANT**: every `hfMU St A S0 λ`, `λ < N_α(F)`, starts the stage at the offset `λ`, has bound field
below `Z_l`, the starts at successors have the high-gate property, and later starts extend earlier ones. -/
theorem hfM_inv {α : Ordinal.{0}} {St : ∀ (Q : HfQ α) (U : HcVD), HcSStart (hfQPB Q) U → HcVD}
    (hSt : ∀ Q U h, HfQSpec Q U (St Q U h)) {A : HfB α} {S0 : HcVD} (hS : HfMStart A S0) :
    ∀ ν : Ordinal.{0}, ν < hcN α A.F → HfMInv A (ν + 1) (hfMU St A S0) := by
  intro ν
  induction ν using Ordinal.limitRecOn with
  | zero =>
    intro _
    have h0 : ∀ μ : Ordinal.{0}, μ < 0 + 1 → μ = 0 := fun μ h => Order.lt_one_iff.1 (by rwa [zero_add] at h)
    refine ⟨fun μ h => ?_, fun μ h => ?_, fun μ hμ h h2 hZ => ?_, fun μ h => ?_, fun β γ hβγ h c x _ => ?_,
      fun β γ hβγ h c _ => ?_⟩
    · rw [h0 μ h, hfMU_zero]; exact hS.B
    · rw [h0 μ h, hfMU_zero]; exact hS.Zb
    · obtain rfl := h0 μ h
      exact hfM_st_congr (hfMU_zero St A S0) h2 hμ hZ (fun h2' hZ' => hS.st h2' hZ')
    · exact absurd (h0 (μ + 1) h) (ne_of_gt (lt_of_le_of_lt zero_le (lt_add_one μ)))
    · have hγ := h0 γ h
      have hβ : β = 0 := le_antisymm (hγ ▸ hβγ) zero_le
      rw [hγ, hβ]
    · have hγ := h0 γ h
      have hβ : β = 0 := le_antisymm (hγ ▸ hβγ) zero_le
      rw [hγ, hβ]
  | add_one μ ih =>
    intro hν
    have hμT : μ < hcN α A.F := (lt_add_one μ).trans hν
    have H := ih hμT
    have h2 : μ < (hfMU St A S0 μ).B := H.self_lt (lt_add_one μ) hμT
    have hZ := H.Zb μ (lt_add_one μ)
    have hst := H.st μ hμT (lt_add_one μ) h2 hZ
    set X := hfQOff A (hfMU St A S0 μ) μ h2 hμT hZ with hX
    have e := hfMU_succ_eq St A S0 hμT h2 hZ hst
    have hsp := hSt X (hfMU St A S0 μ) hst
    have hBμ : (hfMU St A S0 μ).B = X.F := H.B μ (lt_add_one μ)
    have hB1 : (hfMU St A S0 (μ + 1)).B = veblen α (A.F + 1 + (μ + 1)) := by
      rw [e, hsp.B]
      show hdNx α (veblen α (A.F + 1 + μ)) = _
      rw [hdNx_veb, add_assoc (A.F + 1) μ 1]
    have hZ1 : ∀ x, InE x → x < Om1 → (hfMU St A S0 (μ + 1)).Z x ≤ A.Zl x := fun x hx hx1 => by
      rw [e, hsp.Z x hx hx1]
      split_ifs with hγ
      · exact (hb_evZ_lt_fix2 (A.Zl_fix x) (X.S_Zo hx hx1 hγ)).le
      · exact le_rfl
    have h1B : μ + 1 < (hfMU St A S0 μ).B := (ev_isSuccLimit_of_inE (hfMU St A S0 μ).B_E).add_one_lt h2
    have hext : ∀ c x, c < (hfMU St A S0 μ).B → (hfMU St A S0 (μ + 1)).R c x = (hfMU St A S0 μ).R c x :=
      fun c x hc => by rw [e]; exact hsp.extR c x hc
    have hextg : ∀ c, c < (hfMU St A S0 μ).B → (hfMU St A S0 (μ + 1)).g c = (hfMU St A S0 μ).g c :=
      fun c hc => by rw [e]; exact hsp.extg c hc
    have hgiff : ∀ x, InE x → x < Om1 → ((hfMU St A S0 μ).g μ < x ↔ (hfMU St A S0 μ).g (μ + 1) < x) :=
      fun x hx _ => ⟨fun h => (hfMU St A S0 μ).g_succ x (ev_isSuccLimit_of_inE hx) μ h1B h,
        fun h => ((hfMU St A S0 μ).g_le_succ μ).trans_lt h⟩
    have hFr1 : ∀ x, InE x → x < Om1 → X.γ < x →
        glA α (A.Fr x + (hfMU St A S0 (μ + 1)).R (μ + 1) x) x =
          hdNx α (X.Fr x) := fun x hx hx1 hγ => by
      rw [hext (μ + 1) x h1B, (hfMU St A S0 μ).R_succ, ← add_assoc]
      exact hfm_glA_succ A.lv hx hx1 (A.lvN.trans_lt (max_lt_iff.1 hγ).1)
        (A.t1_lt1 hx hx1 (max_lt_iff.1 hγ).1 (hfQOff_R_lt A _ μ h2 hZ hx hx1 hγ))
    have hstS : ∀ (h2' : μ + 1 < (hfMU St A S0 (μ + 1)).B) (hZ' : ∀ x, InE x → x < Om1 →
        (hfMU St A S0 (μ + 1)).Z x ≤ A.Zl x),
        HcSStart (hfMPB A (hfMU St A S0 (μ + 1)) (μ + 1) h2' hν hZ') (hfMU St A S0 (μ + 1)) := fun h2' hZ' => by
      have hγiff : ∀ x, InE x → x < Om1 →
          ((hfMU St A S0 (μ + 1)).γ < x ↔ max A.γN ((hfMU St A S0 (μ + 1)).g (μ + 1)) < x) := fun x hx hx1 => by
        rw [e, hsp.γ]
        show max A.γN ((hfMU St A S0 μ).g μ) < x ↔ max A.γN ((St X _ hst).g (μ + 1)) < x
        rw [← e, hextg (μ + 1) h1B, max_lt_iff, max_lt_iff]
        exact and_congr_right fun _ => hgiff x hx hx1
      refine ⟨?_, hγiff, fun x hx hx1 hγ => ?_, fun x hx hx1 => ?_⟩
      · refine hc_ix_of_B ?_ hB1
        exact veblen_veblen_of_lt A.lv.one_lt _
      · have hγ' : X.γ < x := by
          have := (hγiff x hx hx1).2 hγ; rw [e, hsp.γ] at this; exact this
        show (hfMU St A S0 (μ + 1)).b x = glA α (A.Fr x + (hfMU St A S0 (μ + 1)).R
            (μ + 1) x) x
        rw [hFr1 x hx hx1 hγ', e]; exact hsp.b x hx hx1 hγ'
      · show (hfMU St A S0 (μ + 1)).Z x = HcPB.Zst (hfMPB A (hfMU St A S0 (μ + 1)) (μ + 1) h2' hν hZ') x
        unfold HcPB.Zst
        have hZe := hsp.Z x hx hx1
        rw [← e] at hZe
        rw [hZe]
        show (if X.γ < x then evZ (hdNx α (X.Fr x)) else A.Zl x) =
          if max A.γN ((hfMU St A S0 (μ + 1)).g (μ + 1)) < x then
            evZ (glA α (A.Fr x + (hfMU St A S0 (μ + 1)).R (μ + 1) x) x) else A.Zl x
        have hiff : X.γ < x ↔ max A.γN ((hfMU St A S0 (μ + 1)).g (μ + 1)) < x := by
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
          have hcμ : c < (hfMU St A S0 μ).B := hc.trans_le (by
            rw [H.B β (lt_of_le_of_lt hβμ (lt_add_one μ)), H.B μ (lt_add_one μ)]
            exact (isNormal_veblen _).monotone ((add_le_add_iff_left _).2 hβμ))
          rw [hext c x hcμ]; exact H.cohR β μ hβμ (lt_add_one μ) c x hc
        · rfl
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.cohg β γ hβγ h' c hc
      · rcases hβγ.lt_or_eq with h'' | rfl
        · have hβμ : β ≤ μ := Order.lt_add_one_iff.1 h''
          have hcμ : c < (hfMU St A S0 μ).B := hc.trans_le (by
            rw [H.B β (lt_of_le_of_lt hβμ (lt_add_one μ)), H.B μ (lt_add_one μ)]
            exact (isNormal_veblen _).monotone ((add_le_add_iff_left _).2 hβμ))
          rw [hextg c hcμ]; exact H.cohg β μ hβμ (lt_add_one μ) c hc
        · rfl
  | limit l hl ih =>
    intro hν
    have hIH : ∀ β, β < l → HfMInv A (β + 1) (hfMU St A S0) := fun β h => ih β h (h.trans hν)
    have H : HfMInv A l (hfMU St A S0) := ⟨fun μ h => (hIH μ h).B μ (lt_add_one μ),
      fun μ h => (hIH μ h).Zb μ (lt_add_one μ),
      fun μ hμ h => (hIH μ h).st μ hμ (lt_add_one μ),
      fun μ h => (hIH (μ + 1) h).high μ (lt_add_one _),
      fun β γ hβγ h => (hIH γ h).cohR β γ hβγ (lt_add_one γ),
      fun β γ hβγ h => (hIH γ h).cohg β γ hβγ (lt_add_one γ)⟩
    have e := hfMU_lim_eq St A S0 hl hν H
    set L := HfMFam.mk l (hfMExt S0 l fun β _ => hfMU St A S0 β) hl hν (H.congr fun β h => hfMExt_eq St A S0 h)
      with hL
    have hF : ∀ β, β < l → L.F β = hfMU St A S0 β := fun β h => hfMExt_eq St A S0 h
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
      · exact hfM_st_congr e h2' hβ hZ' (fun _ _ => L.U_start)
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

variable {α : Ordinal.{0}} {St : ∀ (Q : HfQ α) (U : HcVD), HcSStart (hfQPB Q) U → HcVD}
  (hSt : ∀ Q U h, HfQSpec Q U (St Q U h))
  {A : HfB α} {S0 : HcVD} (hS : HfMStart A S0)
include hSt hS

theorem hfMU_B {l : Ordinal.{0}} (hl : l < hcN α A.F) :
    (hfMU St A S0 l).B = veblen α (A.F + 1 + l) :=
  (hfM_inv hSt hS l hl).B l (lt_add_one l)

theorem hfMU_self {l : Ordinal.{0}} (hl : l < hcN α A.F) : l < (hfMU St A S0 l).B :=
  (hfM_inv hSt hS l hl).self_lt (lt_add_one l) hl

theorem hfMU_Zb {l : Ordinal.{0}} (hl : l < hcN α A.F) :
    ∀ x, InE x → x < Om1 → (hfMU St A S0 l).Z x ≤ A.Zl x :=
  (hfM_inv hSt hS l hl).Zb l (lt_add_one l)

/-- **`hfMU λ` STARTS THE STAGE AT THE OFFSET `λ`.** -/
theorem hfMU_start {l : Ordinal.{0}} (hl : l < hcN α A.F) :
    HcSStart (hfMPB A (hfMU St A S0 l) l (hfMU_self hSt hS hl) hl (hfMU_Zb hSt hS hl)) (hfMU St A S0 l) :=
  (hfM_inv hSt hS l hl).st l hl (lt_add_one l) (hfMU_self hSt hS hl) (hfMU_Zb hSt hS hl)

/-- **The base gate of `hfMU λ` lies below a base `x` iff `max(γN, g(λ))` does.** -/
theorem hfMU_γ_iff {l x : Ordinal.{0}} (hl : l < hcN α A.F) (hx : InE x) (hx1 : x < Om1) :
    (hfMU St A S0 l).γ < x ↔ max A.γN ((hfMU St A S0 l).g l) < x := (hfMU_start hSt hS hl).γ x hx hx1

/-- **Later starts extend earlier ones.** -/
theorem hfM_ext {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (hγ : γ < hcN α A.F) :
    (∀ c x, c < (hfMU St A S0 β).B → (hfMU St A S0 γ).R c x = (hfMU St A S0 β).R c x) ∧
    (∀ c, c < (hfMU St A S0 β).B → (hfMU St A S0 γ).g c = (hfMU St A S0 β).g c) :=
  ⟨(hfM_inv hSt hS γ hγ).cohR β γ hβγ (lt_add_one γ), (hfM_inv hSt hS γ hγ).cohg β γ hβγ (lt_add_one γ)⟩

/-- **The specification of the successor**: `hfMU (λ+1)` is the step at the offset `λ`. -/
theorem hfMU_succ_spec {l : Ordinal.{0}} (hl : l < hcN α A.F) :
    HfQSpec (hfQOff A (hfMU St A S0 l) l (hfMU_self hSt hS hl) hl (hfMU_Zb hSt hS hl)) (hfMU St A S0 l)
      (hfMU St A S0 (l + 1)) := by
  rw [hfMU_succ_eq St A S0 hl (hfMU_self hSt hS hl) (hfMU_Zb hSt hS hl) (hfMU_start hSt hS hl)]
  exact hSt _ _ _

end Main

end Googology.Trans.PoR.InaccPsi.R2.Hf
