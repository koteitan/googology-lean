import Googology.Trans.PoR.InaccPsi.R2.HjVLv

/-!
# HjVRec: THE GATED RECURSION OVER THE OFFSETS OF A BASE OF THE LEVEL `L + ν`, FOR ANY STEP OF THAT LEVEL

PORT of `Hi.HiVRec` to a level datum `Λ : Hj.HjLv`: the prefix `Ω₁` of the level `Ω₁ + ν` (read `x + ν`) is replaced
by `Λ.L` (read `Λ.l x`), so every level below is `Λ.L + ν`, read `Λ.l x + ν`.  What differs: the statements carry the
parameter `Λ`; the facts `Ω₁ ≤ L`, `x ≤ ℓ(x) < Γ_{x+1}`, the level gate (`Hj.hjv_cl_gate`) and Lemma EXACT for `ℓ`
come from `Λ`.  With `Λ = Hj.hjL1` it is `Hi.HiVRec` again.

The port of `Hg.HgfMRec` to the level `L + ν` read as `Λ.l x + ν`: for any step `St` of level `L + ν` with the
specification `Hj.HjVSpec` (bound `hdNx (L + ν) F`), a base `A : Hi.HjVB Λ ν` and a start `S0` (`HjVStart A S0`),
`hjVU St A S0 λ` (`λ < N_{L + ν}(F)`, read by a code with a gate) is the start of the stage at the offset `λ`: `S0` at
`0`, `St` at the gated offset pseudo-base `Hj.hjVOff A (hjVU λ) λ` at `λ+1`, the union `Hj.HjVFam.U` at a limit.
`hjV_inv`: the invariant `HjVInv A (ν+1)` at every `ν < N_{L + ν}(F)`.

* `hjV_zero_lt_N`, `HjVStart`, `hjVStep`, `hjVExt`, `hjVLimD`, `hjVU` (**THE GATED OFFSET RECURSION, LEVEL `L + ν`**),
  `hjV_inv` (**THE INVARIANT**), `hjVU_B`, `hjVU_self`, `hjVU_Zb`, `hjVU_start`, `hjVU_γ_iff`, `hjV_ext`,
  `hjVU_succ_spec`.

No new axiom.  New definitions: `HjVStart`, `hjVStep`, `hjVExt`, `hjVLimD`, `hjVU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hj

open Googology.Trans.PoR.InaccPsi.R2.Hi

open Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

variable {Λ : HjLv}

theorem hjV_zero_lt_N {κ : Ordinal.{0}} (A : HjVB Λ κ) : (0 : Ordinal.{0}) < hcN (Λ.L + κ) A.F := A.N_E.pos

/-- **The start conditions** of the recursion over `A` at `S0`. -/
structure HjVStart {κ : Ordinal.{0}} (A : HjVB Λ κ) (S0 : HgVD) : Prop where
  B : S0.B = veblen (Λ.L + κ) (A.F + 1 + 0)
  Zb : ∀ x, InE x → x < Om1 → S0.Z x ≤ A.Zl x
  st : ∀ (h2 : 0 < S0.B) (hZ : ∀ x, InE x → x < Om1 → S0.Z x ≤ A.Zl x),
    HgSStart (hjVMPB A S0 0 h2 (hjV_zero_lt_N A) hZ) S0
  high0 : ∀ c σ, A.F ≤ c → c < S0.B → InE σ → σ < Om1 → S0.g c < σ → A.γ < σ

section Rec

variable {κ : Ordinal.{0}} (St : ∀ (Q : HjVQ Λ κ) (U : HgVD), HgSStart (hjVPB Q) U → HgVD) (A : HjVB Λ κ) (S0 : HgVD)

/-- The successor step: the step `St` at the offset pseudo-base `λ` started at `U` (when `U` starts it). -/
noncomputable def hjVStep (μ : Ordinal.{0}) (U : HgVD) : HgVD := by
  classical
  exact if h : ∃ (hμ : μ < hcN (Λ.L + κ) A.F) (h2 : μ < U.B) (hZ : ∀ x, InE x → x < Om1 → U.Z x ≤ A.Zl x),
      HgSStart (hjVMPB A U μ h2 hμ hZ) U then
    St (hjVOff A U μ h.choose_spec.choose h.choose h.choose_spec.choose_spec.choose) U
      h.choose_spec.choose_spec.choose_spec else U

/-- The family of the earlier values, extended by the start at `0`. -/
noncomputable def hjVExt (l : Ordinal.{0}) (IH : ∀ β, β < l → HgVD) (β : Ordinal.{0}) : HgVD :=
  if h : β < l then IH β h else S0

open Classical in
/-- The limit step: the union of all earlier starts when the invariant holds. -/
noncomputable def hjVLimD (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ β, β < l → HgVD) : HgVD :=
  if H : l < hcN (Λ.L + κ) A.F ∧ HjVInv A l (hjVExt S0 l IH) then
    (HjVFam.mk l (hjVExt S0 l IH) hl H.1 H.2).U else S0

/-- **THE GATED OFFSET RECURSION, EVERY COUNTABLE LEVEL `(Λ.L + κ)`.** -/
noncomputable def hjVU (ν : Ordinal.{0}) : HgVD :=
  Ordinal.limitRecOn (motive := fun _ => HgVD) ν S0 (hjVStep St A) (hjVLimD A S0)

theorem hjVU_zero : hjVU St A S0 0 = S0 := by unfold hjVU; rw [Ordinal.limitRecOn_zero]

theorem hjVU_succ (ν : Ordinal.{0}) : hjVU St A S0 (ν + 1) = hjVStep St A ν (hjVU St A S0 ν) := by
  unfold hjVU; rw [Ordinal.limitRecOn_add_one]

theorem hjVU_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) :
    hjVU St A S0 l = hjVLimD A S0 l hl (fun β _ => hjVU St A S0 β) := by
  unfold hjVU; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem hjVExt_eq {l β : Ordinal.{0}} (h : β < l) :
    hjVExt S0 l (fun β _ => hjVU St A S0 β) β = hjVU St A S0 β := by
  unfold hjVExt; rw [dif_pos h]

/-- The successor value when `hjVU ν` starts the stage at the offset `ν`. -/
theorem hjVU_succ_eq {ν : Ordinal.{0}} (hν : ν < hcN (Λ.L + κ) A.F) (h2 : ν < (hjVU St A S0 ν).B)
    (hZ : ∀ x, InE x → x < Om1 → (hjVU St A S0 ν).Z x ≤ A.Zl x)
    (h : HgSStart (hjVMPB A (hjVU St A S0 ν) ν h2 hν hZ) (hjVU St A S0 ν)) :
    hjVU St A S0 (ν + 1) = St (hjVOff A (hjVU St A S0 ν) ν h2 hν hZ) (hjVU St A S0 ν) h := by
  rw [hjVU_succ]; unfold hjVStep
  rw [dif_pos ⟨hν, h2, hZ, h⟩]

theorem hjVU_lim_eq {l : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l < hcN (Λ.L + κ) A.F)
    (H : HjVInv A l (hjVU St A S0)) :
    hjVU St A S0 l = (HjVFam.mk l (hjVExt S0 l fun β _ => hjVU St A S0 β) hl hle
      (H.congr fun β h => hjVExt_eq St A S0 h)).U := by
  rw [hjVU_limit St A S0 hl]; unfold hjVLimD; rw [dif_pos ⟨hle, H.congr fun β h => hjVExt_eq St A S0 h⟩]

end Rec

/-- **THE INVARIANT**: every `hjVU St A S0 λ`, `λ < N_α(F)`, starts the stage at the offset `λ`, has bound field
below `Z_l`, the starts at successors have the high-gate property, and later starts extend earlier ones. -/
theorem hjV_inv {κ : Ordinal.{0}} {St : ∀ (Q : HjVQ Λ κ) (U : HgVD), HgSStart (hjVPB Q) U → HgVD}
    (hSt : ∀ Q U h, HjVSpec Q U (St Q U h)) {A : HjVB Λ κ} {S0 : HgVD} (hS : HjVStart A S0) :
    ∀ ν : Ordinal.{0}, ν < hcN (Λ.L + κ) A.F → HjVInv A (ν + 1) (hjVU St A S0) := by
  intro ν
  induction ν using Ordinal.limitRecOn with
  | zero =>
    intro _
    have h0 : ∀ μ : Ordinal.{0}, μ < 0 + 1 → μ = 0 := fun μ h => Order.lt_one_iff.1 (by rwa [zero_add] at h)
    refine ⟨fun μ h => ?_, fun μ h => ?_, fun μ hμ h h2 hZ => ?_, fun μ h => ?_, fun β γ hβγ h c x _ => ?_,
      fun β γ hβγ h c _ => ?_⟩
    · rw [h0 μ h, hjVU_zero]; exact hS.B
    · rw [h0 μ h, hjVU_zero]; exact hS.Zb
    · obtain rfl := h0 μ h
      exact hjV_st_congr (hjVU_zero St A S0) h2 hμ hZ (fun h2' hZ' => hS.st h2' hZ')
    · exact absurd (h0 (μ + 1) h) (ne_of_gt (lt_of_le_of_lt zero_le (lt_add_one μ)))
    · have hγ := h0 γ h
      have hβ : β = 0 := le_antisymm (hγ ▸ hβγ) zero_le
      rw [hγ, hβ]
    · have hγ := h0 γ h
      have hβ : β = 0 := le_antisymm (hγ ▸ hβγ) zero_le
      rw [hγ, hβ]
  | add_one μ ih =>
    intro hν
    have hμT : μ < hcN (Λ.L + κ) A.F := (lt_add_one μ).trans hν
    have H := ih hμT
    have h2 : μ < (hjVU St A S0 μ).B := H.self_lt (lt_add_one μ) hμT
    have hZ := H.Zb μ (lt_add_one μ)
    have hst := H.st μ hμT (lt_add_one μ) h2 hZ
    set X := hjVOff A (hjVU St A S0 μ) μ h2 hμT hZ with hX
    have e := hjVU_succ_eq St A S0 hμT h2 hZ hst
    have hsp := hSt X (hjVU St A S0 μ) hst
    have hBμ : (hjVU St A S0 μ).B = X.F := H.B μ (lt_add_one μ)
    have hB1 : (hjVU St A S0 (μ + 1)).B = veblen (Λ.L + κ) (A.F + 1 + (μ + 1)) := by
      rw [e, hsp.B]
      show hdNx (Λ.L + κ) (veblen (Λ.L + κ) (A.F + 1 + μ)) = _
      rw [hdNx_veb, add_assoc (A.F + 1) μ 1]
    have hZ1 : ∀ x, InE x → x < Om1 → (hjVU St A S0 (μ + 1)).Z x ≤ A.Zl x := fun x hx hx1 => by
      rw [e, hsp.Z x hx hx1]
      split_ifs with hγ
      · exact (hb_evZ_lt_fix2 (A.Zl_fix x) (X.S_Zo hx hx1 hγ)).le
      · exact le_rfl
    have h1B : μ + 1 < (hjVU St A S0 μ).B := (ev_isSuccLimit_of_inE (hjVU St A S0 μ).B_E).add_one_lt h2
    have hext : ∀ c x, c < (hjVU St A S0 μ).B → (hjVU St A S0 (μ + 1)).R c x = (hjVU St A S0 μ).R c x :=
      fun c x hc => by rw [e]; exact hsp.extR c x hc
    have hextg : ∀ c, c < (hjVU St A S0 μ).B → (hjVU St A S0 (μ + 1)).g c = (hjVU St A S0 μ).g c :=
      fun c hc => by rw [e]; exact hsp.extg c hc
    have hgiff : ∀ x, InE x → x < Om1 → ((hjVU St A S0 μ).g μ < x ↔ (hjVU St A S0 μ).g (μ + 1) < x) :=
      fun x hx _ => ⟨fun h => (hjVU St A S0 μ).g_succ x (ev_isSuccLimit_of_inE hx) μ h1B h,
        fun h => ((hjVU St A S0 μ).g_le_succ μ).trans_lt h⟩
    have hFr1 : ∀ x, InE x → x < Om1 → X.γ < x →
        glA (Λ.l x + κ) (A.Fr x + (hjVU St A S0 (μ + 1)).R (μ + 1) x) x =
          hdNx (Λ.l x + κ) (X.Fr x) := fun x hx hx1 hγ => by
      rw [hext (μ + 1) x h1B, (hjVU St A S0 μ).R_succ, ← add_assoc]
      exact hjv_glA_succ Λ hx hx1 (A.ν_lt hx hx1 (max_lt_iff.1 hγ).1)
        (A.t1_lt1 hx hx1 (max_lt_iff.1 hγ).1 (hjVOff_R_lt A _ μ h2 hZ hx hx1 hγ))
    have hstS : ∀ (h2' : μ + 1 < (hjVU St A S0 (μ + 1)).B) (hZ' : ∀ x, InE x → x < Om1 →
        (hjVU St A S0 (μ + 1)).Z x ≤ A.Zl x),
        HgSStart (hjVMPB A (hjVU St A S0 (μ + 1)) (μ + 1) h2' hν hZ') (hjVU St A S0 (μ + 1)) := fun h2' hZ' => by
      have hγiff : ∀ x, InE x → x < Om1 →
          ((hjVU St A S0 (μ + 1)).γ < x ↔ max A.γN ((hjVU St A S0 (μ + 1)).g (μ + 1)) < x) := fun x hx hx1 => by
        rw [e, hsp.γ]
        show max A.γN ((hjVU St A S0 μ).g μ) < x ↔ max A.γN ((St X _ hst).g (μ + 1)) < x
        rw [← e, hextg (μ + 1) h1B, max_lt_iff, max_lt_iff]
        exact and_congr_right fun _ => hgiff x hx hx1
      refine ⟨?_, hγiff, fun x hx hx1 hγ => ?_, fun x hx hx1 => ?_⟩
      · refine hg_ix_of_B ?_ hB1
        exact veblen_veblen_of_lt ((hg_one_lt_Om1.trans_le Λ.OL).trans_le le_self_add) _
      · have hγ' : X.γ < x := by
          have := (hγiff x hx hx1).2 hγ; rw [e, hsp.γ] at this; exact this
        show (hjVU St A S0 (μ + 1)).b x = glA (Λ.l x + κ) (A.Fr x + (hjVU St A S0 (μ + 1)).R
            (μ + 1) x) x
        rw [hFr1 x hx hx1 hγ', e]; exact hsp.b x hx hx1 hγ'
      · show (hjVU St A S0 (μ + 1)).Z x = HgPB.Zst (hjVMPB A (hjVU St A S0 (μ + 1)) (μ + 1) h2' hν hZ') x
        unfold HgPB.Zst
        have hZe := hsp.Z x hx hx1
        rw [← e] at hZe
        rw [hZe]
        show (if X.γ < x then evZ (hdNx (Λ.l x + κ) (X.Fr x)) else A.Zl x) =
          if max A.γN ((hjVU St A S0 (μ + 1)).g (μ + 1)) < x then
            evZ (glA (Λ.l x + κ) (A.Fr x + (hjVU St A S0 (μ + 1)).R (μ + 1) x) x) else A.Zl x
        have hiff : X.γ < x ↔ max A.γN ((hjVU St A S0 (μ + 1)).g (μ + 1)) < x := by
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
          have hcμ : c < (hjVU St A S0 μ).B := hc.trans_le (by
            rw [H.B β (lt_of_le_of_lt hβμ (lt_add_one μ)), H.B μ (lt_add_one μ)]
            exact (isNormal_veblen _).monotone ((add_le_add_iff_left _).2 hβμ))
          rw [hext c x hcμ]; exact H.cohR β μ hβμ (lt_add_one μ) c x hc
        · rfl
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.cohg β γ hβγ h' c hc
      · rcases hβγ.lt_or_eq with h'' | rfl
        · have hβμ : β ≤ μ := Order.lt_add_one_iff.1 h''
          have hcμ : c < (hjVU St A S0 μ).B := hc.trans_le (by
            rw [H.B β (lt_of_le_of_lt hβμ (lt_add_one μ)), H.B μ (lt_add_one μ)]
            exact (isNormal_veblen _).monotone ((add_le_add_iff_left _).2 hβμ))
          rw [hextg c hcμ]; exact H.cohg β μ hβμ (lt_add_one μ) c hc
        · rfl
  | limit l hl ih =>
    intro hν
    have hIH : ∀ β, β < l → HjVInv A (β + 1) (hjVU St A S0) := fun β h => ih β h (h.trans hν)
    have H : HjVInv A l (hjVU St A S0) := ⟨fun μ h => (hIH μ h).B μ (lt_add_one μ),
      fun μ h => (hIH μ h).Zb μ (lt_add_one μ),
      fun μ hμ h => (hIH μ h).st μ hμ (lt_add_one μ),
      fun μ h => (hIH (μ + 1) h).high μ (lt_add_one _),
      fun β γ hβγ h => (hIH γ h).cohR β γ hβγ (lt_add_one γ),
      fun β γ hβγ h => (hIH γ h).cohg β γ hβγ (lt_add_one γ)⟩
    have e := hjVU_lim_eq St A S0 hl hν H
    set L := HjVFam.mk l (hjVExt S0 l fun β _ => hjVU St A S0 β) hl hν (H.congr fun β h => hjVExt_eq St A S0 h)
      with hL
    have hF : ∀ β, β < l → L.F β = hjVU St A S0 β := fun β h => hjVExt_eq St A S0 h
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
      · exact hjV_st_congr e h2' hβ hZ' (fun _ _ => L.U_start)
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

variable {κ : Ordinal.{0}} {St : ∀ (Q : HjVQ Λ κ) (U : HgVD), HgSStart (hjVPB Q) U → HgVD}
  (hSt : ∀ Q U h, HjVSpec Q U (St Q U h))
  {A : HjVB Λ κ} {S0 : HgVD} (hS : HjVStart A S0)
include hSt hS

theorem hjVU_B {l : Ordinal.{0}} (hl : l < hcN (Λ.L + κ) A.F) :
    (hjVU St A S0 l).B = veblen (Λ.L + κ) (A.F + 1 + l) :=
  (hjV_inv hSt hS l hl).B l (lt_add_one l)

theorem hjVU_self {l : Ordinal.{0}} (hl : l < hcN (Λ.L + κ) A.F) : l < (hjVU St A S0 l).B :=
  (hjV_inv hSt hS l hl).self_lt (lt_add_one l) hl

theorem hjVU_Zb {l : Ordinal.{0}} (hl : l < hcN (Λ.L + κ) A.F) :
    ∀ x, InE x → x < Om1 → (hjVU St A S0 l).Z x ≤ A.Zl x :=
  (hjV_inv hSt hS l hl).Zb l (lt_add_one l)

/-- **`hjVU λ` STARTS THE STAGE AT THE OFFSET `λ`.** -/
theorem hjVU_start {l : Ordinal.{0}} (hl : l < hcN (Λ.L + κ) A.F) :
    HgSStart (hjVMPB A (hjVU St A S0 l) l (hjVU_self hSt hS hl) hl (hjVU_Zb hSt hS hl)) (hjVU St A S0 l) :=
  (hjV_inv hSt hS l hl).st l hl (lt_add_one l) (hjVU_self hSt hS hl) (hjVU_Zb hSt hS hl)

/-- **The base gate of `hjVU λ` lies below a base `x` iff `max(γN, g(λ))` does.** -/
theorem hjVU_γ_iff {l x : Ordinal.{0}} (hl : l < hcN (Λ.L + κ) A.F) (hx : InE x) (hx1 : x < Om1) :
    (hjVU St A S0 l).γ < x ↔ max A.γN ((hjVU St A S0 l).g l) < x := (hjVU_start hSt hS hl).γ x hx hx1

/-- **Later starts extend earlier ones.** -/
theorem hjV_ext {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (hγ : γ < hcN (Λ.L + κ) A.F) :
    (∀ c x, c < (hjVU St A S0 β).B → (hjVU St A S0 γ).R c x = (hjVU St A S0 β).R c x) ∧
    (∀ c, c < (hjVU St A S0 β).B → (hjVU St A S0 γ).g c = (hjVU St A S0 β).g c) :=
  ⟨(hjV_inv hSt hS γ hγ).cohR β γ hβγ (lt_add_one γ), (hjV_inv hSt hS γ hγ).cohg β γ hβγ (lt_add_one γ)⟩

/-- **The specification of the successor**: `hjVU (λ+1)` is the step at the offset `λ`. -/
theorem hjVU_succ_spec {l : Ordinal.{0}} (hl : l < hcN (Λ.L + κ) A.F) :
    HjVSpec (hjVOff A (hjVU St A S0 l) l (hjVU_self hSt hS hl) hl (hjVU_Zb hSt hS hl)) (hjVU St A S0 l)
      (hjVU St A S0 (l + 1)) := by
  rw [hjVU_succ_eq St A S0 hl (hjVU_self hSt hS hl) (hjVU_Zb hSt hS hl) (hjVU_start hSt hS hl)]
  exact hSt _ _ _

end Main

end Googology.Trans.PoR.InaccPsi.R2.Hj
