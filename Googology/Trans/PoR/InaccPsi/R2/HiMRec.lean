import Googology.Trans.PoR.InaccPsi.R2.HiMLv

/-!
# HiMRec: THE GATED OFFSET RECURSION AT THE LEVEL `Ω₁` READ AS `x`, WITH THE TOWER OVER THE GATED BASE AS ITS STEP

The copy of `Hg.HgfMRec` whose level is the base itself and whose step is the union over all levels over the gated
base `Hi.hiOff (F λ) λ` (`Hi.hiQU`, bound `hdNx Ω₁ Q_λ = Q_{λ+1}`).  For a start `S0` at `Q_0 = φ(Ω₁, G+1)`
(`HiMStart`), `hiMU S0 λ` (`λ < N_{Ω₁}(G)`, read by a code with a gate) is the start of the stage at the offset `λ`:
`S0` at `0`, `Hi.hiQU` over `Hi.hiOff (hiMU λ) λ` at `λ+1`, the union `Hi.HiMFam.U` at a limit.  `hiM_inv`: the
invariant `HiMInv (ν+1)` at every `ν < N_{Ω₁}(G)`.  No offset is a constant here: the gate moves the EXACT part of
`P_λ` above `g(λ)`, so the offset `ε₀` (and every offset with gate `≥ ε₀`) is passed.

* `HiMStart`, `hiMStep`, `hiMExt`, `hiMLimD`, `hiMU` (**THE GATED OFFSET RECURSION AT THE LEVEL `Ω₁`**), `hiM_inv`
  (**THE INVARIANT**), `hiMU_B`, `hiMU_self`, `hiMU_Zb`, `hiMU_start`, `hiMU_γ_iff`, `hiM_ext`, `hiMU_succ_eq'`;
* `hgU_hiStart` (**`Hg.hgU`, the system at `φ(Ω₁, G+1)`, starts the recursion**).

No new axiom.  New definitions: `HiMStart`, `hiMStep`, `hiMExt`, `hiMLimD`, `hiMU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hi

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
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

theorem hiN_pos : (0 : Ordinal.{0}) < hiN := hiN_E.pos

/-- **The start conditions** of the recursion at `S0`. -/
structure HiMStart (S0 : HgVD) : Prop where
  B : S0.B = hiQ 0
  Zb : ∀ x, InE x → x < Om1 → S0.Z x ≤ hiZl x
  st : ∀ (h2 : 0 < S0.B) (hZ : ∀ x, InE x → x < Om1 → S0.Z x ≤ hiZl x),
    HiQStart (hiOff S0 0 h2 hiN_pos hZ) S0

section Rec

variable (S0 : HgVD)

/-- The successor step: the union over all levels over the gated base at the offset `λ`, started at `U` (when `U`
starts it). -/
noncomputable def hiMStep (μ : Ordinal.{0}) (U : HgVD) : HgVD := by
  classical
  exact if h : ∃ (hμ : μ < hiN) (h2 : μ < U.B) (hZ : ∀ x, InE x → x < Om1 → U.Z x ≤ hiZl x),
      HiQStart (hiOff U μ h2 hμ hZ) U then
    hiQU (hiOff U μ h.choose_spec.choose h.choose h.choose_spec.choose_spec.choose) U
      h.choose_spec.choose_spec.choose_spec else U

/-- The family of the earlier values, extended by the start at `0`. -/
noncomputable def hiMExt (l : Ordinal.{0}) (IH : ∀ β, β < l → HgVD) (β : Ordinal.{0}) : HgVD :=
  if h : β < l then IH β h else S0

open Classical in
/-- The limit step: the union of all earlier starts when the invariant holds. -/
noncomputable def hiMLimD (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ β, β < l → HgVD) : HgVD :=
  if H : l < hiN ∧ HiMInv l (hiMExt S0 l IH) then
    (HiMFam.mk l (hiMExt S0 l IH) hl H.1 H.2).U else S0

/-- **THE GATED OFFSET RECURSION AT THE LEVEL `Ω₁` READ AS `x`.** -/
noncomputable def hiMU (ν : Ordinal.{0}) : HgVD :=
  Ordinal.limitRecOn (motive := fun _ => HgVD) ν S0 hiMStep (hiMLimD S0)

theorem hiMU_zero : hiMU S0 0 = S0 := by unfold hiMU; rw [Ordinal.limitRecOn_zero]

theorem hiMU_succ (ν : Ordinal.{0}) : hiMU S0 (ν + 1) = hiMStep ν (hiMU S0 ν) := by
  unfold hiMU; rw [Ordinal.limitRecOn_add_one]

theorem hiMU_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) :
    hiMU S0 l = hiMLimD S0 l hl (fun β _ => hiMU S0 β) := by
  unfold hiMU; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem hiMExt_eq {l β : Ordinal.{0}} (h : β < l) :
    hiMExt S0 l (fun β _ => hiMU S0 β) β = hiMU S0 β := by
  unfold hiMExt; rw [dif_pos h]

/-- The successor value when `hiMU ν` starts the stage at the offset `ν`. -/
theorem hiMU_succ_eq {ν : Ordinal.{0}} (hν : ν < hiN) (h2 : ν < (hiMU S0 ν).B)
    (hZ : ∀ x, InE x → x < Om1 → (hiMU S0 ν).Z x ≤ hiZl x)
    (h : HiQStart (hiOff (hiMU S0 ν) ν h2 hν hZ) (hiMU S0 ν)) :
    hiMU S0 (ν + 1) = hiQU (hiOff (hiMU S0 ν) ν h2 hν hZ) (hiMU S0 ν) h := by
  rw [hiMU_succ]; unfold hiMStep
  rw [dif_pos ⟨hν, h2, hZ, h⟩]

theorem hiMU_lim_eq {l : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l < hiN) (H : HiMInv l (hiMU S0)) :
    hiMU S0 l = (HiMFam.mk l (hiMExt S0 l fun β _ => hiMU S0 β) hl hle
      (H.congr fun β h => hiMExt_eq S0 h)).U := by
  rw [hiMU_limit S0 hl]; unfold hiMLimD; rw [dif_pos ⟨hle, H.congr fun β h => hiMExt_eq S0 h⟩]

end Rec

/-- **THE INVARIANT**: every `hiMU S0 λ`, `λ < N_{Ω₁}(G)`, starts the stage at the offset `λ`, has bound field below
`Z_l`, the starts at successors have the high-gate property, and later starts extend earlier ones. -/
theorem hiM_inv {S0 : HgVD} (hS : HiMStart S0) : ∀ ν : Ordinal.{0}, ν < hiN → HiMInv (ν + 1) (hiMU S0) := by
  intro ν
  induction ν using Ordinal.limitRecOn with
  | zero =>
    intro _
    have h0 : ∀ μ : Ordinal.{0}, μ < 0 + 1 → μ = 0 := fun μ h => Order.lt_one_iff.1 (by rwa [zero_add] at h)
    refine ⟨fun μ h => ?_, fun μ h => ?_, fun μ hμ h h2 hZ => ?_, fun μ h => ?_, fun β γ hβγ h c x _ => ?_,
      fun β γ hβγ h c _ => ?_⟩
    · rw [h0 μ h, hiMU_zero]; exact hS.B
    · rw [h0 μ h, hiMU_zero]; exact hS.Zb
    · obtain rfl := h0 μ h
      exact hiM_st_congr (hiMU_zero S0) h2 hμ hZ (fun h2' hZ' => hS.st h2' hZ')
    · exact absurd (h0 (μ + 1) h) (ne_of_gt (lt_of_le_of_lt zero_le (lt_add_one μ)))
    · have hγ := h0 γ h
      have hβ : β = 0 := le_antisymm (hγ ▸ hβγ) zero_le
      rw [hγ, hβ]
    · have hγ := h0 γ h
      have hβ : β = 0 := le_antisymm (hγ ▸ hβγ) zero_le
      rw [hγ, hβ]
  | add_one μ ih =>
    intro hν
    have hμT : μ < hiN := (lt_add_one μ).trans hν
    have H := ih hμT
    have h2 : μ < (hiMU S0 μ).B := H.self_lt (lt_add_one μ) hμT
    have hZ := H.Zb μ (lt_add_one μ)
    have hst := H.st μ hμT (lt_add_one μ) h2 hZ
    set X := hiOff (hiMU S0 μ) μ h2 hμT hZ with hX
    have e := hiMU_succ_eq S0 hμT h2 hZ hst
    have hBμ : (hiMU S0 μ).B = X.Q := H.B μ (lt_add_one μ)
    have hB1 : (hiMU S0 (μ + 1)).B = hiQ (μ + 1) := by
      rw [e, hiQU_B]; exact hiQ_succ μ
    have hZ1 : ∀ x, InE x → x < Om1 → (hiMU S0 (μ + 1)).Z x ≤ hiZl x := fun x hx hx1 => by
      rw [e, hiQU_Z]
      split_ifs with hγ
      · exact (hb_evZ_lt_fix2 (hiZl_fix x) (hiPn_lt_Zl (hiMU S0 μ) h2 hZ hx hx1 hγ)).le
      · exact le_rfl
    have h1B : μ + 1 < (hiMU S0 μ).B := (ev_isSuccLimit_of_inE (hiMU S0 μ).B_E).add_one_lt h2
    have hext : ∀ c x, c < (hiMU S0 μ).B → (hiMU S0 (μ + 1)).R c x = (hiMU S0 μ).R c x :=
      fun c x hc => by rw [e]; exact (hiQU_ext X (hiMU S0 μ) hst hc).1 x
    have hextg : ∀ c, c < (hiMU S0 μ).B → (hiMU S0 (μ + 1)).g c = (hiMU S0 μ).g c :=
      fun c hc => by rw [e]; exact (hiQU_ext X (hiMU S0 μ) hst hc).2
    have hgiff : ∀ x, InE x → x < Om1 → ((hiMU S0 μ).g μ < x ↔ (hiMU S0 μ).g (μ + 1) < x) :=
      fun x hx _ => ⟨fun h => (hiMU S0 μ).g_succ x (ev_isSuccLimit_of_inE hx) μ h1B h,
        fun h => ((hiMU S0 μ).g_le_succ μ).trans_lt h⟩
    have hFr1 : ∀ x, InE x → x < Om1 → X.γ < x →
        hiP (hiMU S0 (μ + 1)) (μ + 1) x = hdNx x (X.P x) := fun x hx hx1 hγ => by
      show glA x (lgG x + (hiMU S0 (μ + 1)).R (μ + 1) x) x = hdNx x (hiP (hiMU S0 μ) μ x)
      rw [hext (μ + 1) x h1B, (hiMU S0 μ).R_succ, hiP_succ (hiMU S0 μ) h2 hZ hx hx1 hγ]
    have hstS : ∀ (h2' : μ + 1 < (hiMU S0 (μ + 1)).B) (hZ' : ∀ x, InE x → x < Om1 →
        (hiMU S0 (μ + 1)).Z x ≤ hiZl x),
        HiQStart (hiOff (hiMU S0 (μ + 1)) (μ + 1) h2' hν hZ') (hiMU S0 (μ + 1)) := fun h2' hZ' => by
      have hγiff : ∀ x, InE x → x < Om1 →
          ((hiMU S0 (μ + 1)).γ < x ↔ (hiMU S0 (μ + 1)).g (μ + 1) < x) := fun x hx hx1 => by
        rw [hextg (μ + 1) h1B, e, hiQU_γ]
        exact hgiff x hx hx1
      refine ⟨?_, hγiff, fun x hx hx1 hγ => ?_, fun x hx hx1 => ?_⟩
      · show (hiMU S0 (μ + 1)).ix = hiQ (μ + 1)
        rw [e, hiQU_ix]; exact hiQ_succ μ
      · have hγ' : X.γ < x := by
          have := (hγiff x hx hx1).2 hγ; rw [e, hiQU_γ] at this; exact this
        show (hiMU S0 (μ + 1)).b x = hiP (hiMU S0 (μ + 1)) (μ + 1) x
        rw [hFr1 x hx hx1 hγ', e]; rfl
      · show (hiMU S0 (μ + 1)).Z x = HgPB.Zst (hiMPB (hiMU S0 (μ + 1)) (μ + 1) h2' hν hZ') x
        unfold HgPB.Zst
        have hZe : (hiMU S0 (μ + 1)).Z x = if X.γ < x then evZ (hdNx x (X.P x)) else X.Zo x := by
          rw [e]; exact hiQU_Z X (hiMU S0 μ) hst x
        rw [hZe]
        show (if X.γ < x then evZ (hdNx x (X.P x)) else hiZl x) =
          if (hiMU S0 (μ + 1)).g (μ + 1) < x then evZ (hiP (hiMU S0 (μ + 1)) (μ + 1) x) else hiZl x
        have hiff : X.γ < x ↔ (hiMU S0 (μ + 1)).g (μ + 1) < x := by
          rw [← hγiff x hx hx1, e, hiQU_γ]
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
        rw [hiQU_γ]
        exact hiQU_high X (hiMU S0 β) hst (by rw [← hBμ]; exact h1) h2' hσ hσ1 hg
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.cohR β γ hβγ h' c x hc
      · rcases hβγ.lt_or_eq with h'' | rfl
        · have hβμ : β ≤ μ := Order.lt_add_one_iff.1 h''
          have hcμ : c < (hiMU S0 μ).B := hc.trans_le (by
            rw [H.B β (lt_of_le_of_lt hβμ (lt_add_one μ)), H.B μ (lt_add_one μ)]
            exact hiQ_le_Q hβμ)
          rw [hext c x hcμ]; exact H.cohR β μ hβμ (lt_add_one μ) c x hc
        · rfl
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.cohg β γ hβγ h' c hc
      · rcases hβγ.lt_or_eq with h'' | rfl
        · have hβμ : β ≤ μ := Order.lt_add_one_iff.1 h''
          have hcμ : c < (hiMU S0 μ).B := hc.trans_le (by
            rw [H.B β (lt_of_le_of_lt hβμ (lt_add_one μ)), H.B μ (lt_add_one μ)]
            exact hiQ_le_Q hβμ)
          rw [hextg c hcμ]; exact H.cohg β μ hβμ (lt_add_one μ) c hc
        · rfl
  | limit l hl ih =>
    intro hν
    have hIH : ∀ β, β < l → HiMInv (β + 1) (hiMU S0) := fun β h => ih β h (h.trans hν)
    have H : HiMInv l (hiMU S0) := ⟨fun μ h => (hIH μ h).B μ (lt_add_one μ),
      fun μ h => (hIH μ h).Zb μ (lt_add_one μ),
      fun μ hμ h => (hIH μ h).st μ hμ (lt_add_one μ),
      fun μ h => (hIH (μ + 1) h).high μ (lt_add_one _),
      fun β γ hβγ h => (hIH γ h).cohR β γ hβγ (lt_add_one γ),
      fun β γ hβγ h => (hIH γ h).cohg β γ hβγ (lt_add_one γ)⟩
    have e := hiMU_lim_eq S0 hl hν H
    set L := HiMFam.mk l (hiMExt S0 l fun β _ => hiMU S0 β) hl hν (H.congr fun β h => hiMExt_eq S0 h)
      with hL
    have hF : ∀ β, β < l → L.F β = hiMU S0 β := fun β h => hiMExt_eq S0 h
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
      · exact hiM_st_congr e h2' hβ hZ' (fun _ _ => L.U_start)
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

variable {S0 : HgVD} (hS : HiMStart S0)
include hS

theorem hiMU_B {l : Ordinal.{0}} (hl : l < hiN) : (hiMU S0 l).B = hiQ l :=
  (hiM_inv hS l hl).B l (lt_add_one l)

theorem hiMU_self {l : Ordinal.{0}} (hl : l < hiN) : l < (hiMU S0 l).B :=
  (hiM_inv hS l hl).self_lt (lt_add_one l) hl

theorem hiMU_Zb {l : Ordinal.{0}} (hl : l < hiN) : ∀ x, InE x → x < Om1 → (hiMU S0 l).Z x ≤ hiZl x :=
  (hiM_inv hS l hl).Zb l (lt_add_one l)

/-- **`hiMU λ` STARTS THE STAGE AT THE OFFSET `λ`.** -/
theorem hiMU_start {l : Ordinal.{0}} (hl : l < hiN) :
    HiQStart (hiOff (hiMU S0 l) l (hiMU_self hS hl) hl (hiMU_Zb hS hl)) (hiMU S0 l) :=
  (hiM_inv hS l hl).st l hl (lt_add_one l) (hiMU_self hS hl) (hiMU_Zb hS hl)

/-- **The base gate of `hiMU λ` lies below a base `x` iff `g(λ)` does.** -/
theorem hiMU_γ_iff {l x : Ordinal.{0}} (hl : l < hiN) (hx : InE x) (hx1 : x < Om1) :
    (hiMU S0 l).γ < x ↔ (hiMU S0 l).g l < x := (hiMU_start hS hl).γ x hx hx1

/-- **Later starts extend earlier ones.** -/
theorem hiM_ext {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (hγ : γ < hiN) :
    (∀ c x, c < (hiMU S0 β).B → (hiMU S0 γ).R c x = (hiMU S0 β).R c x) ∧
    (∀ c, c < (hiMU S0 β).B → (hiMU S0 γ).g c = (hiMU S0 β).g c) :=
  ⟨(hiM_inv hS γ hγ).cohR β γ hβγ (lt_add_one γ), (hiM_inv hS γ hγ).cohg β γ hβγ (lt_add_one γ)⟩

/-- **The successor**: `hiMU (λ+1)` is the union over all levels over the gated base at the offset `λ`. -/
theorem hiMU_succ_eq' {l : Ordinal.{0}} (hl : l < hiN) :
    hiMU S0 (l + 1) = hiQU (hiOff (hiMU S0 l) l (hiMU_self hS hl) hl (hiMU_Zb hS hl)) (hiMU S0 l)
      (hiMU_start hS hl) :=
  hiMU_succ_eq S0 hl (hiMU_self hS hl) (hiMU_Zb hS hl) (hiMU_start hS hl)

/-- **The high-gate property of the successor starts.** -/
theorem hiMU_high {μ c σ : Ordinal.{0}} (hμ : μ + 1 < hiN) (h1 : (hiMU S0 μ).B ≤ c) (h2 : c < (hiMU S0 (μ + 1)).B)
    (hσ : InE σ) (hσ1 : σ < Om1) (hg : (hiMU S0 (μ + 1)).g c < σ) : (hiMU S0 (μ + 1)).γ < σ :=
  (hiM_inv hS (μ + 1) hμ).high μ (lt_add_one _) c σ h1 h2 hσ hσ1 hg

end Main

/-! ## The start `Hg.hgU` at `Q_0 = φ(Ω₁, G+1)` -/

theorem hgU_hiZ {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : hgU.Z x = evZ (hcBR x) := by
  rw [hgU_startF.Z x hx hx1, HgPB.Zst_eq _ hx.pos]
  show evZ (hgFP 0 x) = evZ (hcBR x); rw [hgFP_zero]

theorem hgU_hib {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : hgU.b x = hcBR x := by
  rw [hgU_startF.b x hx hx1 hx.pos]; exact hgFP_zero x

theorem hgU_hiZb (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : hgU.Z x ≤ hiZl x := by
  rw [hgU_hiZ hx hx1]
  have h : hcBR x < hiZl x := by rw [hiZl_eq hx hx1]; exact hc_next_lt_N
  exact (hb_evZ_lt_fix2 (hiZl_fix x) h).le

/-- **`Hg.hgU` (the system at `φ(Ω₁, G+1)`) STARTS THE GATED OFFSET RECURSION AT THE LEVEL `Ω₁`.** -/
theorem hgU_hiStart : HiMStart hgU where
  B := by rw [hiQ_zero]; rfl
  Zb := hgU_hiZb
  st := fun h2 hZ => {
    ix := by show hgU.ix = hiQ 0; rw [hiQ_zero]; rfl
    γ := fun x hx hx1 => by
      show hgU.γ < x ↔ hgU.g 0 < x
      rw [hgU.g_zero, hgU_startF.γ x hx hx1]; rfl
    b := fun x hx hx1 _ => by
      show hgU.b x = hiP hgU 0 x
      unfold hiP
      rw [hgU.R_zero, add_zero, hgU_hib hx hx1, hc_glA_GG hx hx1 (hi_one_le hx hx1) (lgG_facts hx hx1).2.1]; rfl
    Z := fun x hx hx1 => by
      rw [HgPB.Zst_eq _ (show hgU.g 0 < x by rw [hgU.g_zero]; exact hx.pos)]
      show hgU.Z x = evZ (hiP hgU 0 x)
      unfold hiP
      rw [hgU.R_zero, add_zero, hgU_hiZ hx hx1, hc_glA_GG hx hx1 (hi_one_le hx hx1) (lgG_facts hx hx1).2.1]; rfl }

end Googology.Trans.PoR.InaccPsi.R2.Hi
