import Googology.Trans.PoR.InaccPsi.R2.XlLv

/-!
# XlRec: THE OFFSET RECURSION OF A LEVEL FROM THE BOTTOM, FOR EVERY OFFSET BELOW `N = φ(L+κ+1, 0)`

PORT of `Hn.HnVRec` to a bottom base `Xl.XlB` (base `0` in place of a fixed point `F`).  One recursion
`xlU St A S0 λ` over every ordinal `λ < N`: `S0` (a start of `φ(L+κ, e)`) at `0`, the step `St` at the stage
`φ(L+κ, e + μ)` (the offset `μ` read by the system built so far) at `μ + 1`, the union `Xl.XlFam.U` at a limit `λ`
(the offset `λ` read by the first earlier start containing it).  Every offset is read by the system itself, so its
gate is the code gate of the offset in that system (no bound by `Γ₀`).

* `XlStart` (the start conditions), `xlU` (**THE RECURSION**), `xl_inv` (**THE INVARIANT AT EVERY `λ < N`**),
  `xlU_B` (`B = φ(L+κ, e + λ)`), `xlU_start`, `xlU_γ_iff` (**the gate of the stage `λ` is `max(γN, g(λ))`**),
  `xl_ext`, `xlU_succ_spec`.

No new axiom.  New definitions: `XlStart`, `xlStep`, `xlLimD`, `xlU`.
-/

set_option autoImplicit false


open Googology.Trans.PoR.InaccPsi.R2.Wm Googology.Trans.PoR.InaccPsi.R2.Wh Googology.Trans.PoR.InaccPsi.R2.Ho
open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gf
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd
open Googology.Trans.PoR.InaccPsi.R2.Wo Googology.Trans.PoR.InaccPsi.R2.Wn Googology.Trans.PoR.InaccPsi.R2.Wp
  Googology.Trans.PoR.InaccPsi.R2.Ws Googology.Trans.PoR.InaccPsi.R2.Wt Googology.Trans.PoR.InaccPsi.R2.Wy
  Googology.Trans.PoR.InaccPsi.R2.Wx

open Googology.Trans.PoR.InaccPsi.R2.Xc
open Googology.Trans.PoR.InaccPsi.R2.Xf

open Googology.Trans.PoR.InaccPsi.R2.Xf

namespace Googology.Trans.PoR.InaccPsi.R2.Xl

variable {Λ : HnLv}

theorem xl_zero_lt_N {κ : Ordinal.{0}} (A : XlB Λ κ) : (0 : Ordinal.{0}) < hcN (Λ.L + κ) 0 := A.zero_lt_N

/-- **The start conditions** of the recursion over `A` at `S0`. -/
structure XlStart {κ : Ordinal.{0}} (A : XlB Λ κ) (S0 : HgVD) : Prop where
  B : S0.B = veblen (Λ.L + κ) (A.e + 0)
  Zb : ∀ x, InE x → x < Om1 → S0.Z x ≤ A.Zl x
  st : ∀ (h2 : 0 < S0.B) (hZ : ∀ x, InE x → x < Om1 → S0.Z x ≤ A.Zl x),
    HgSStart (xlMPB A S0 0 h2 (xl_zero_lt_N A) hZ) S0

section Rec

variable {κ : Ordinal.{0}} (St : ∀ (Q : HnVQ Λ κ) (U : HgVD), HgSStart (hnVPB Q) U → HgVD) (A : XlB Λ κ) (S0 : HgVD)

/-- The successor step: the step `St` at the offset pseudo-base `λ` started at `U` (when `U` starts it). -/
noncomputable def xlStep (μ : Ordinal.{0}) (U : HgVD) : HgVD := by
  classical
  exact if h : ∃ (hμ : μ < hcN (Λ.L + κ) 0) (h2 : μ < U.B) (hZ : ∀ x, InE x → x < Om1 → U.Z x ≤ A.Zl x),
      HgSStart (xlMPB A U μ h2 hμ hZ) U then
    St (xlOff A U μ h.choose_spec.choose h.choose h.choose_spec.choose_spec.choose) U
      h.choose_spec.choose_spec.choose_spec else U

open Classical in
/-- The limit step: the union of all earlier starts when the invariant holds. -/
noncomputable def xlLimD (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ β, β < l → HgVD) : HgVD :=
  if H : l < hcN (Λ.L + κ) 0 ∧ XlInv A l (hjVExt S0 l IH) then
    (XlFam.mk l (hjVExt S0 l IH) hl H.1 H.2).U else S0

/-- **THE GATED OFFSET RECURSION, EVERY COUNTABLE LEVEL `(Λ.L + κ)`.** -/
noncomputable def xlU (ν : Ordinal.{0}) : HgVD :=
  Ordinal.limitRecOn (motive := fun _ => HgVD) ν S0 (xlStep St A) (xlLimD A S0)

theorem xlU_zero : xlU St A S0 0 = S0 := by unfold xlU; rw [Ordinal.limitRecOn_zero]

theorem xlU_succ (ν : Ordinal.{0}) : xlU St A S0 (ν + 1) = xlStep St A ν (xlU St A S0 ν) := by
  unfold xlU; rw [Ordinal.limitRecOn_add_one]

theorem xlU_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) :
    xlU St A S0 l = xlLimD A S0 l hl (fun β _ => xlU St A S0 β) := by
  unfold xlU; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem xlExt_eq {l β : Ordinal.{0}} (h : β < l) :
    hjVExt S0 l (fun β _ => xlU St A S0 β) β = xlU St A S0 β := by
  unfold hjVExt; rw [dif_pos h]

/-- The successor value when `xlU ν` starts the stage at the offset `ν`. -/
theorem xlU_succ_eq {ν : Ordinal.{0}} (hν : ν < hcN (Λ.L + κ) 0) (h2 : ν < (xlU St A S0 ν).B)
    (hZ : ∀ x, InE x → x < Om1 → (xlU St A S0 ν).Z x ≤ A.Zl x)
    (h : HgSStart (xlMPB A (xlU St A S0 ν) ν h2 hν hZ) (xlU St A S0 ν)) :
    xlU St A S0 (ν + 1) = St (xlOff A (xlU St A S0 ν) ν h2 hν hZ) (xlU St A S0 ν) h := by
  rw [xlU_succ]; unfold xlStep
  rw [dif_pos ⟨hν, h2, hZ, h⟩]

theorem xlU_lim_eq {l : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l < hcN (Λ.L + κ) 0)
    (H : XlInv A l (xlU St A S0)) :
    xlU St A S0 l = (XlFam.mk l (hjVExt S0 l fun β _ => xlU St A S0 β) hl hle
      (H.congr fun β h => xlExt_eq St A S0 h)).U := by
  rw [xlU_limit St A S0 hl]; unfold xlLimD; rw [dif_pos ⟨hle, H.congr fun β h => xlExt_eq St A S0 h⟩]

end Rec

/-- **THE INVARIANT**: every `xlU St A S0 λ`, `λ < N_α(F)`, starts the stage at the offset `λ`, has bound field
below `Z_l`, the starts at successors have the high-gate property, and later starts extend earlier ones. -/
theorem xl_inv {κ : Ordinal.{0}} {St : ∀ (Q : HnVQ Λ κ) (U : HgVD), HgSStart (hnVPB Q) U → HgVD}
    (hSt : ∀ Q U h, HnVSpec Q U (St Q U h)) {A : XlB Λ κ} {S0 : HgVD} (hS : XlStart A S0) :
    ∀ ν : Ordinal.{0}, ν < hcN (Λ.L + κ) 0 → XlInv A (ν + 1) (xlU St A S0) := by
  intro ν
  induction ν using Ordinal.limitRecOn with
  | zero =>
    intro _
    have h0 : ∀ μ : Ordinal.{0}, μ < 0 + 1 → μ = 0 := fun μ h => Order.lt_one_iff.1 (by rwa [zero_add] at h)
    refine ⟨fun μ h => ?_, fun μ h => ?_, fun μ hμ h h2 hZ => ?_, fun μ h => ?_, fun β γ hβγ h c x _ => ?_,
      fun β γ hβγ h c _ => ?_⟩
    · rw [h0 μ h, xlU_zero]; exact hS.B
    · rw [h0 μ h, xlU_zero]; exact hS.Zb
    · obtain rfl := h0 μ h
      exact xl_st_congr (xlU_zero St A S0) h2 hμ hZ (fun h2' hZ' => hS.st h2' hZ')
    · exact absurd (h0 (μ + 1) h) (ne_of_gt (lt_of_le_of_lt zero_le (lt_add_one μ)))
    · have hγ := h0 γ h
      have hβ : β = 0 := le_antisymm (hγ ▸ hβγ) zero_le
      rw [hγ, hβ]
    · have hγ := h0 γ h
      have hβ : β = 0 := le_antisymm (hγ ▸ hβγ) zero_le
      rw [hγ, hβ]
  | add_one μ ih =>
    intro hν
    have hμT : μ < hcN (Λ.L + κ) 0 := (lt_add_one μ).trans hν
    have H := ih hμT
    have h2 : μ < (xlU St A S0 μ).B := H.self_lt (lt_add_one μ) hμT
    have hZ := H.Zb μ (lt_add_one μ)
    have hst := H.st μ hμT (lt_add_one μ) h2 hZ
    set X := xlOff A (xlU St A S0 μ) μ h2 hμT hZ with hX
    have e := xlU_succ_eq St A S0 hμT h2 hZ hst
    have hsp := hSt X (xlU St A S0 μ) hst
    have hBμ : (xlU St A S0 μ).B = X.F := H.B μ (lt_add_one μ)
    have hB1 : (xlU St A S0 (μ + 1)).B = veblen (Λ.L + κ) (A.e + (μ + 1)) := by
      rw [e, hsp.B]
      show hdNx (Λ.L + κ) (veblen (Λ.L + κ) (A.e + μ)) = _
      rw [hdNx_veb, add_assoc (A.e : Ordinal.{0}) μ 1]
    have hZ1 : ∀ x, InE x → x < Om1 → (xlU St A S0 (μ + 1)).Z x ≤ A.Zl x := fun x hx hx1 => by
      rw [e, hsp.Z x hx hx1]
      split_ifs with hγ
      · exact (hb_evZ_lt_fix2 (A.Zl_fix x) (X.S_Zo hx hx1 hγ)).le
      · exact le_rfl
    have h1B : μ + 1 < (xlU St A S0 μ).B := (ev_isSuccLimit_of_inE (xlU St A S0 μ).B_E).add_one_lt h2
    have hext : ∀ c x, c < (xlU St A S0 μ).B → (xlU St A S0 (μ + 1)).R c x = (xlU St A S0 μ).R c x :=
      fun c x hc => by rw [e]; exact hsp.extR c x hc
    have hextg : ∀ c, c < (xlU St A S0 μ).B → (xlU St A S0 (μ + 1)).g c = (xlU St A S0 μ).g c :=
      fun c hc => by rw [e]; exact hsp.extg c hc
    have hgiff : ∀ x, InE x → x < Om1 → ((xlU St A S0 μ).g μ < x ↔ (xlU St A S0 μ).g (μ + 1) < x) :=
      fun x hx _ => ⟨fun h => (xlU St A S0 μ).g_succ x (ev_isSuccLimit_of_inE hx) μ h1B h,
        fun h => ((xlU St A S0 μ).g_le_succ μ).trans_lt h⟩
    have hFr1 : ∀ x, InE x → x < Om1 → X.γ < x →
        glA (Λ.l x + κ) ((xlU St A S0 (μ + 1)).R (μ + 1) x) x =
          hdNx (Λ.l x + κ) (X.Fr x) := fun x hx hx1 hγ => by
      rw [hext (μ + 1) x h1B, (xlU St A S0 μ).R_succ]
      exact hnv_glA_succ Λ hx hx1 (A.ν_lt hx hx1 (max_lt_iff.1 hγ).1)
        (A.t1_lt1 hx hx1 (max_lt_iff.1 hγ).1 (xlOff_R_lt A _ μ h2 hZ hx hx1 hγ))
    have hstS : ∀ (h2' : μ + 1 < (xlU St A S0 (μ + 1)).B) (hZ' : ∀ x, InE x → x < Om1 →
        (xlU St A S0 (μ + 1)).Z x ≤ A.Zl x),
        HgSStart (xlMPB A (xlU St A S0 (μ + 1)) (μ + 1) h2' hν hZ') (xlU St A S0 (μ + 1)) := fun h2' hZ' => by
      have hγiff : ∀ x, InE x → x < Om1 →
          ((xlU St A S0 (μ + 1)).γ < x ↔ max A.γN ((xlU St A S0 (μ + 1)).g (μ + 1)) < x) := fun x hx hx1 => by
        rw [e, hsp.γ]
        show max A.γN ((xlU St A S0 μ).g μ) < x ↔ max A.γN ((St X _ hst).g (μ + 1)) < x
        rw [← e, hextg (μ + 1) h1B, max_lt_iff, max_lt_iff]
        exact and_congr_right fun _ => hgiff x hx hx1
      refine ⟨?_, hγiff, fun x hx hx1 hγ => ?_, fun x hx hx1 => ?_⟩
      · refine hg_ix_of_B ?_ hB1
        exact veblen_veblen_of_lt ((hg_one_lt_Om1.trans_le Λ.OL).trans_le le_self_add) _
      · have hγ' : X.γ < x := by
          have := (hγiff x hx hx1).2 hγ; rw [e, hsp.γ] at this; exact this
        show (xlU St A S0 (μ + 1)).b x = glA (Λ.l x + κ) ((xlU St A S0 (μ + 1)).R
            (μ + 1) x) x
        rw [hFr1 x hx hx1 hγ', e]; exact hsp.b x hx hx1 hγ'
      · show (xlU St A S0 (μ + 1)).Z x = HgPB.Zst (xlMPB A (xlU St A S0 (μ + 1)) (μ + 1) h2' hν hZ') x
        unfold HgPB.Zst
        have hZe := hsp.Z x hx hx1
        rw [← e] at hZe
        rw [hZe]
        show (if X.γ < x then evZ (hdNx (Λ.l x + κ) (X.Fr x)) else A.Zl x) =
          if max A.γN ((xlU St A S0 (μ + 1)).g (μ + 1)) < x then
            evZ (glA (Λ.l x + κ) ((xlU St A S0 (μ + 1)).R (μ + 1) x) x) else A.Zl x
        have hiff : X.γ < x ↔ max A.γN ((xlU St A S0 (μ + 1)).g (μ + 1)) < x := by
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
          have hcμ : c < (xlU St A S0 μ).B := hc.trans_le (by
            rw [H.B β (lt_of_le_of_lt hβμ (lt_add_one μ)), H.B μ (lt_add_one μ)]
            exact (isNormal_veblen _).monotone ((add_le_add_iff_left _).2 hβμ))
          rw [hext c x hcμ]; exact H.cohR β μ hβμ (lt_add_one μ) c x hc
        · rfl
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.cohg β γ hβγ h' c hc
      · rcases hβγ.lt_or_eq with h'' | rfl
        · have hβμ : β ≤ μ := Order.lt_add_one_iff.1 h''
          have hcμ : c < (xlU St A S0 μ).B := hc.trans_le (by
            rw [H.B β (lt_of_le_of_lt hβμ (lt_add_one μ)), H.B μ (lt_add_one μ)]
            exact (isNormal_veblen _).monotone ((add_le_add_iff_left _).2 hβμ))
          rw [hextg c hcμ]; exact H.cohg β μ hβμ (lt_add_one μ) c hc
        · rfl
  | limit l hl ih =>
    intro hν
    have hIH : ∀ β, β < l → XlInv A (β + 1) (xlU St A S0) := fun β h => ih β h (h.trans hν)
    have H : XlInv A l (xlU St A S0) := ⟨fun μ h => (hIH μ h).B μ (lt_add_one μ),
      fun μ h => (hIH μ h).Zb μ (lt_add_one μ),
      fun μ hμ h => (hIH μ h).st μ hμ (lt_add_one μ),
      fun μ h => (hIH (μ + 1) h).high μ (lt_add_one _),
      fun β γ hβγ h => (hIH γ h).cohR β γ hβγ (lt_add_one γ),
      fun β γ hβγ h => (hIH γ h).cohg β γ hβγ (lt_add_one γ)⟩
    have e := xlU_lim_eq St A S0 hl hν H
    set L := XlFam.mk l (hjVExt S0 l fun β _ => xlU St A S0 β) hl hν (H.congr fun β h => xlExt_eq St A S0 h)
      with hL
    have hF : ∀ β, β < l → L.F β = xlU St A S0 β := fun β h => xlExt_eq St A S0 h
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
      · exact xl_st_congr e h2' hβ hZ' (fun _ _ => L.U_start)
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

variable {κ : Ordinal.{0}} {St : ∀ (Q : HnVQ Λ κ) (U : HgVD), HgSStart (hnVPB Q) U → HgVD}
  (hSt : ∀ Q U h, HnVSpec Q U (St Q U h))
  {A : XlB Λ κ} {S0 : HgVD} (hS : XlStart A S0)
include hSt hS

theorem xlU_B {l : Ordinal.{0}} (hl : l < hcN (Λ.L + κ) 0) :
    (xlU St A S0 l).B = veblen (Λ.L + κ) (A.e + l) :=
  (xl_inv hSt hS l hl).B l (lt_add_one l)

theorem xlU_self {l : Ordinal.{0}} (hl : l < hcN (Λ.L + κ) 0) : l < (xlU St A S0 l).B :=
  (xl_inv hSt hS l hl).self_lt (lt_add_one l) hl

theorem xlU_Zb {l : Ordinal.{0}} (hl : l < hcN (Λ.L + κ) 0) :
    ∀ x, InE x → x < Om1 → (xlU St A S0 l).Z x ≤ A.Zl x :=
  (xl_inv hSt hS l hl).Zb l (lt_add_one l)

/-- **`xlU λ` STARTS THE STAGE AT THE OFFSET `λ`.** -/
theorem xlU_start {l : Ordinal.{0}} (hl : l < hcN (Λ.L + κ) 0) :
    HgSStart (xlMPB A (xlU St A S0 l) l (xlU_self hSt hS hl) hl (xlU_Zb hSt hS hl)) (xlU St A S0 l) :=
  (xl_inv hSt hS l hl).st l hl (lt_add_one l) (xlU_self hSt hS hl) (xlU_Zb hSt hS hl)

/-- **The base gate of `xlU λ` lies below a base `x` iff `max(γN, g(λ))` does.** -/
theorem xlU_γ_iff {l x : Ordinal.{0}} (hl : l < hcN (Λ.L + κ) 0) (hx : InE x) (hx1 : x < Om1) :
    (xlU St A S0 l).γ < x ↔ max A.γN ((xlU St A S0 l).g l) < x := (xlU_start hSt hS hl).γ x hx hx1

/-- **Later starts extend earlier ones.** -/
theorem xl_ext {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (hγ : γ < hcN (Λ.L + κ) 0) :
    (∀ c x, c < (xlU St A S0 β).B → (xlU St A S0 γ).R c x = (xlU St A S0 β).R c x) ∧
    (∀ c, c < (xlU St A S0 β).B → (xlU St A S0 γ).g c = (xlU St A S0 β).g c) :=
  ⟨(xl_inv hSt hS γ hγ).cohR β γ hβγ (lt_add_one γ), (xl_inv hSt hS γ hγ).cohg β γ hβγ (lt_add_one γ)⟩

/-- **The specification of the successor**: `xlU (λ+1)` is the step at the offset `λ`. -/
theorem xlU_succ_spec {l : Ordinal.{0}} (hl : l < hcN (Λ.L + κ) 0) :
    HnVSpec (xlOff A (xlU St A S0 l) l (xlU_self hSt hS hl) hl (xlU_Zb hSt hS hl)) (xlU St A S0 l)
      (xlU St A S0 (l + 1)) := by
  rw [xlU_succ_eq St A S0 hl (xlU_self hSt hS hl) (xlU_Zb hSt hS hl) (xlU_start hSt hS hl)]
  exact hSt _ _ _

end Main

end Googology.Trans.PoR.InaccPsi.R2.Xl
