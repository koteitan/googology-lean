import Googology.Trans.PoR.InaccPsi.R2.HgPB
import Googology.Trans.PoR.InaccPsi.R2.HgS
import Googology.Trans.PoR.InaccPsi.R2.HgSRec
import Googology.Trans.PoR.InaccPsi.R2.HgSU
import Googology.Trans.PoR.InaccPsi.R2.HgX
import Googology.Trans.PoR.InaccPsi.R2.HgLv
import Googology.Trans.PoR.InaccPsi.R2.HgLvRec
import Googology.Trans.PoR.InaccPsi.R2.HgLvTop
import Googology.Trans.PoR.InaccPsi.R2.HgRec
import Googology.Trans.PoR.InaccPsi.R2.HgCh
import Googology.Trans.PoR.InaccPsi.R2.HgdX
import Googology.Trans.PoR.InaccPsi.R2.HgdCh
import Googology.Trans.PoR.InaccPsi.R2.HgdStep
import Googology.Trans.PoR.InaccPsi.R2.HgdLv
import Googology.Trans.PoR.InaccPsi.R2.HgdLvRec
import Googology.Trans.PoR.InaccPsi.R2.HgdLvTop
import Googology.Trans.PoR.InaccPsi.R2.HgdM
import Googology.Trans.PoR.InaccPsi.R2.HgdMLv
import Googology.Trans.PoR.InaccPsi.R2.HgdMRec
import Googology.Trans.PoR.InaccPsi.R2.HgdMTop
import Googology.Trans.PoR.InaccPsi.R2.HgdMSc
import Googology.Trans.PoR.InaccPsi.R2.HgdMRecL
import Googology.Trans.PoR.InaccPsi.R2.HgfM
import Googology.Trans.PoR.InaccPsi.R2.HgfMLv

/-!
# HgfMRec: THE GATED RECURSION OVER THE OFFSETS OF A BASE OF EVERY COUNTABLE LEVEL `α`, FOR ANY STEP OF LEVEL `α`

(Textual copy of `Hf.HfMRec` for `Hg.HgVD`: bound fields `< Γ_{x+2}` in place of `≤ B_x(x)` (`Hc.hcBR`); the proofs
are unchanged except where the bound enters.  Names: prefix `hg`/`Hg` (from `hc`/`Hc`), `hgd`/`Hgd` (from `hd`/`Hd`),
`hgf`/`Hgf` (from `hf`/`Hf`), `hge`/`Hge` (from `he`/`He`).)

The level-`α` version of `Hd.HdLvRec`, for any step `St` of level `α` with the specification `Hg.HgfQSpec` (bound
`hdNx α F`).  For a base `A : Hf.HgfB α` and a start `S0` (`HgfMStart A S0`), `hgfMU St A S0 λ` (`λ < N_α(F)`, read by
a code with a gate) is the start of the stage at the offset `λ`: `S0` at `0`, `St` at the gated offset pseudo-base
`Hg.hgfQOff A (hgfMU λ) λ` at `λ+1`, the union `Hg.HgfMFam.U` at a limit.  `hgfM_inv`: the invariant `HgfMInv A (ν+1)`
at
every `ν < N_α(F)`.  The start condition `high0` asks only the CODE GATE `γ` of `A` (a code `c ∈ [F, S0.B)` with
gate below `σ` forces `γ < σ`), so it holds at `G` (code gate `0`) for every level.

* `hgfM_zero_lt_N`, `HgfMStart`, `hgfMStep`, `hgfMExt`, `hgfMLimD`, `hgfMU` (**THE GATED OFFSET RECURSION, EVERY
  COUNTABLE
  LEVEL**), `hgfM_inv` (**THE INVARIANT**), `hgfMU_B`, `hgfMU_self`, `hgfMU_Zb`, `hgfMU_start`, `hgfMU_γ_iff`,
  `hgfM_ext`,
  `hgfMU_succ_spec`.

No new axiom.  New definitions: `HgfMStart`, `hgfMStep`, `hgfMExt`, `hgfMLimD`, `hgfMU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hg

open Googology.Trans.PoR.InaccPsi.R2.Hc
open Googology.Trans.PoR.InaccPsi.R2.Hd
open Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hf

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

theorem hgfM_zero_lt_N {α : Ordinal.{0}} (A : HgfB α) : (0 : Ordinal.{0}) < hcN α A.F := A.N_E.pos

/-- **The start conditions** of the recursion over `A` at `S0`. -/
structure HgfMStart {α : Ordinal.{0}} (A : HgfB α) (S0 : HgVD) : Prop where
  B : S0.B = veblen α (A.F + 1 + 0)
  Zb : ∀ x, InE x → x < Om1 → S0.Z x ≤ A.Zl x
  st : ∀ (h2 : 0 < S0.B) (hZ : ∀ x, InE x → x < Om1 → S0.Z x ≤ A.Zl x),
    HgSStart (hgfMPB A S0 0 h2 (hgfM_zero_lt_N A) hZ) S0
  high0 : ∀ c σ, A.F ≤ c → c < S0.B → InE σ → σ < Om1 → S0.g c < σ → A.γ < σ

section Rec

variable {α : Ordinal.{0}} (St : ∀ (Q : HgfQ α) (U : HgVD), HgSStart (hgfQPB Q) U → HgVD) (A : HgfB α) (S0 : HgVD)

/-- The successor step: the step `St` at the offset pseudo-base `λ` started at `U` (when `U` starts it). -/
noncomputable def hgfMStep (μ : Ordinal.{0}) (U : HgVD) : HgVD := by
  classical
  exact if h : ∃ (hμ : μ < hcN α A.F) (h2 : μ < U.B) (hZ : ∀ x, InE x → x < Om1 → U.Z x ≤ A.Zl x),
      HgSStart (hgfMPB A U μ h2 hμ hZ) U then
    St (hgfQOff A U μ h.choose_spec.choose h.choose h.choose_spec.choose_spec.choose) U
      h.choose_spec.choose_spec.choose_spec else U

/-- The family of the earlier values, extended by the start at `0`. -/
noncomputable def hgfMExt (l : Ordinal.{0}) (IH : ∀ β, β < l → HgVD) (β : Ordinal.{0}) : HgVD :=
  if h : β < l then IH β h else S0

open Classical in
/-- The limit step: the union of all earlier starts when the invariant holds. -/
noncomputable def hgfMLimD (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ β, β < l → HgVD) : HgVD :=
  if H : l < hcN α A.F ∧ HgfMInv A l (hgfMExt S0 l IH) then
    (HgfMFam.mk l (hgfMExt S0 l IH) hl H.1 H.2).U else S0

/-- **THE GATED OFFSET RECURSION, EVERY COUNTABLE LEVEL `α`.** -/
noncomputable def hgfMU (ν : Ordinal.{0}) : HgVD :=
  Ordinal.limitRecOn (motive := fun _ => HgVD) ν S0 (hgfMStep St A) (hgfMLimD A S0)

theorem hgfMU_zero : hgfMU St A S0 0 = S0 := by unfold hgfMU; rw [Ordinal.limitRecOn_zero]

theorem hgfMU_succ (ν : Ordinal.{0}) : hgfMU St A S0 (ν + 1) = hgfMStep St A ν (hgfMU St A S0 ν) := by
  unfold hgfMU; rw [Ordinal.limitRecOn_add_one]

theorem hgfMU_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) :
    hgfMU St A S0 l = hgfMLimD A S0 l hl (fun β _ => hgfMU St A S0 β) := by
  unfold hgfMU; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem hgfMExt_eq {l β : Ordinal.{0}} (h : β < l) :
    hgfMExt S0 l (fun β _ => hgfMU St A S0 β) β = hgfMU St A S0 β := by
  unfold hgfMExt; rw [dif_pos h]

/-- The successor value when `hgfMU ν` starts the stage at the offset `ν`. -/
theorem hgfMU_succ_eq {ν : Ordinal.{0}} (hν : ν < hcN α A.F) (h2 : ν < (hgfMU St A S0 ν).B)
    (hZ : ∀ x, InE x → x < Om1 → (hgfMU St A S0 ν).Z x ≤ A.Zl x)
    (h : HgSStart (hgfMPB A (hgfMU St A S0 ν) ν h2 hν hZ) (hgfMU St A S0 ν)) :
    hgfMU St A S0 (ν + 1) = St (hgfQOff A (hgfMU St A S0 ν) ν h2 hν hZ) (hgfMU St A S0 ν) h := by
  rw [hgfMU_succ]; unfold hgfMStep
  rw [dif_pos ⟨hν, h2, hZ, h⟩]

theorem hgfMU_lim_eq {l : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l < hcN α A.F)
    (H : HgfMInv A l (hgfMU St A S0)) :
    hgfMU St A S0 l = (HgfMFam.mk l (hgfMExt S0 l fun β _ => hgfMU St A S0 β) hl hle
      (H.congr fun β h => hgfMExt_eq St A S0 h)).U := by
  rw [hgfMU_limit St A S0 hl]; unfold hgfMLimD; rw [dif_pos ⟨hle, H.congr fun β h => hgfMExt_eq St A S0 h⟩]

end Rec

/-- **THE INVARIANT**: every `hgfMU St A S0 λ`, `λ < N_α(F)`, starts the stage at the offset `λ`, has bound field
below `Z_l`, the starts at successors have the high-gate property, and later starts extend earlier ones. -/
theorem hgfM_inv {α : Ordinal.{0}} {St : ∀ (Q : HgfQ α) (U : HgVD), HgSStart (hgfQPB Q) U → HgVD}
    (hSt : ∀ Q U h, HgfQSpec Q U (St Q U h)) {A : HgfB α} {S0 : HgVD} (hS : HgfMStart A S0) :
    ∀ ν : Ordinal.{0}, ν < hcN α A.F → HgfMInv A (ν + 1) (hgfMU St A S0) := by
  intro ν
  induction ν using Ordinal.limitRecOn with
  | zero =>
    intro _
    have h0 : ∀ μ : Ordinal.{0}, μ < 0 + 1 → μ = 0 := fun μ h => Order.lt_one_iff.1 (by rwa [zero_add] at h)
    refine ⟨fun μ h => ?_, fun μ h => ?_, fun μ hμ h h2 hZ => ?_, fun μ h => ?_, fun β γ hβγ h c x _ => ?_,
      fun β γ hβγ h c _ => ?_⟩
    · rw [h0 μ h, hgfMU_zero]; exact hS.B
    · rw [h0 μ h, hgfMU_zero]; exact hS.Zb
    · obtain rfl := h0 μ h
      exact hgfM_st_congr (hgfMU_zero St A S0) h2 hμ hZ (fun h2' hZ' => hS.st h2' hZ')
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
    have h2 : μ < (hgfMU St A S0 μ).B := H.self_lt (lt_add_one μ) hμT
    have hZ := H.Zb μ (lt_add_one μ)
    have hst := H.st μ hμT (lt_add_one μ) h2 hZ
    set X := hgfQOff A (hgfMU St A S0 μ) μ h2 hμT hZ with hX
    have e := hgfMU_succ_eq St A S0 hμT h2 hZ hst
    have hsp := hSt X (hgfMU St A S0 μ) hst
    have hBμ : (hgfMU St A S0 μ).B = X.F := H.B μ (lt_add_one μ)
    have hB1 : (hgfMU St A S0 (μ + 1)).B = veblen α (A.F + 1 + (μ + 1)) := by
      rw [e, hsp.B]
      show hdNx α (veblen α (A.F + 1 + μ)) = _
      rw [hdNx_veb, add_assoc (A.F + 1) μ 1]
    have hZ1 : ∀ x, InE x → x < Om1 → (hgfMU St A S0 (μ + 1)).Z x ≤ A.Zl x := fun x hx hx1 => by
      rw [e, hsp.Z x hx hx1]
      split_ifs with hγ
      · exact (hb_evZ_lt_fix2 (A.Zl_fix x) (X.S_Zo hx hx1 hγ)).le
      · exact le_rfl
    have h1B : μ + 1 < (hgfMU St A S0 μ).B := (ev_isSuccLimit_of_inE (hgfMU St A S0 μ).B_E).add_one_lt h2
    have hext : ∀ c x, c < (hgfMU St A S0 μ).B → (hgfMU St A S0 (μ + 1)).R c x = (hgfMU St A S0 μ).R c x :=
      fun c x hc => by rw [e]; exact hsp.extR c x hc
    have hextg : ∀ c, c < (hgfMU St A S0 μ).B → (hgfMU St A S0 (μ + 1)).g c = (hgfMU St A S0 μ).g c :=
      fun c hc => by rw [e]; exact hsp.extg c hc
    have hgiff : ∀ x, InE x → x < Om1 → ((hgfMU St A S0 μ).g μ < x ↔ (hgfMU St A S0 μ).g (μ + 1) < x) :=
      fun x hx _ => ⟨fun h => (hgfMU St A S0 μ).g_succ x (ev_isSuccLimit_of_inE hx) μ h1B h,
        fun h => ((hgfMU St A S0 μ).g_le_succ μ).trans_lt h⟩
    have hFr1 : ∀ x, InE x → x < Om1 → X.γ < x →
        glA α (A.Fr x + (hgfMU St A S0 (μ + 1)).R (μ + 1) x) x =
          hdNx α (X.Fr x) := fun x hx hx1 hγ => by
      rw [hext (μ + 1) x h1B, (hgfMU St A S0 μ).R_succ, ← add_assoc]
      exact hfm_glA_succ A.lv hx hx1 (A.lvN.trans_lt (max_lt_iff.1 hγ).1)
        (A.t1_lt1 hx hx1 (max_lt_iff.1 hγ).1 (hgfQOff_R_lt A _ μ h2 hZ hx hx1 hγ))
    have hstS : ∀ (h2' : μ + 1 < (hgfMU St A S0 (μ + 1)).B) (hZ' : ∀ x, InE x → x < Om1 →
        (hgfMU St A S0 (μ + 1)).Z x ≤ A.Zl x),
        HgSStart (hgfMPB A (hgfMU St A S0 (μ + 1)) (μ + 1) h2' hν hZ') (hgfMU St A S0 (μ + 1)) := fun h2' hZ' => by
      have hγiff : ∀ x, InE x → x < Om1 →
          ((hgfMU St A S0 (μ + 1)).γ < x ↔ max A.γN ((hgfMU St A S0 (μ + 1)).g (μ + 1)) < x) := fun x hx hx1 => by
        rw [e, hsp.γ]
        show max A.γN ((hgfMU St A S0 μ).g μ) < x ↔ max A.γN ((St X _ hst).g (μ + 1)) < x
        rw [← e, hextg (μ + 1) h1B, max_lt_iff, max_lt_iff]
        exact and_congr_right fun _ => hgiff x hx hx1
      refine ⟨?_, hγiff, fun x hx hx1 hγ => ?_, fun x hx hx1 => ?_⟩
      · refine hg_ix_of_B ?_ hB1
        exact veblen_veblen_of_lt A.lv.one_lt _
      · have hγ' : X.γ < x := by
          have := (hγiff x hx hx1).2 hγ; rw [e, hsp.γ] at this; exact this
        show (hgfMU St A S0 (μ + 1)).b x = glA α (A.Fr x + (hgfMU St A S0 (μ + 1)).R
            (μ + 1) x) x
        rw [hFr1 x hx hx1 hγ', e]; exact hsp.b x hx hx1 hγ'
      · show (hgfMU St A S0 (μ + 1)).Z x = HgPB.Zst (hgfMPB A (hgfMU St A S0 (μ + 1)) (μ + 1) h2' hν hZ') x
        unfold HgPB.Zst
        have hZe := hsp.Z x hx hx1
        rw [← e] at hZe
        rw [hZe]
        show (if X.γ < x then evZ (hdNx α (X.Fr x)) else A.Zl x) =
          if max A.γN ((hgfMU St A S0 (μ + 1)).g (μ + 1)) < x then
            evZ (glA α (A.Fr x + (hgfMU St A S0 (μ + 1)).R (μ + 1) x) x) else A.Zl x
        have hiff : X.γ < x ↔ max A.γN ((hgfMU St A S0 (μ + 1)).g (μ + 1)) < x := by
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
          have hcμ : c < (hgfMU St A S0 μ).B := hc.trans_le (by
            rw [H.B β (lt_of_le_of_lt hβμ (lt_add_one μ)), H.B μ (lt_add_one μ)]
            exact (isNormal_veblen _).monotone ((add_le_add_iff_left _).2 hβμ))
          rw [hext c x hcμ]; exact H.cohR β μ hβμ (lt_add_one μ) c x hc
        · rfl
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.cohg β γ hβγ h' c hc
      · rcases hβγ.lt_or_eq with h'' | rfl
        · have hβμ : β ≤ μ := Order.lt_add_one_iff.1 h''
          have hcμ : c < (hgfMU St A S0 μ).B := hc.trans_le (by
            rw [H.B β (lt_of_le_of_lt hβμ (lt_add_one μ)), H.B μ (lt_add_one μ)]
            exact (isNormal_veblen _).monotone ((add_le_add_iff_left _).2 hβμ))
          rw [hextg c hcμ]; exact H.cohg β μ hβμ (lt_add_one μ) c hc
        · rfl
  | limit l hl ih =>
    intro hν
    have hIH : ∀ β, β < l → HgfMInv A (β + 1) (hgfMU St A S0) := fun β h => ih β h (h.trans hν)
    have H : HgfMInv A l (hgfMU St A S0) := ⟨fun μ h => (hIH μ h).B μ (lt_add_one μ),
      fun μ h => (hIH μ h).Zb μ (lt_add_one μ),
      fun μ hμ h => (hIH μ h).st μ hμ (lt_add_one μ),
      fun μ h => (hIH (μ + 1) h).high μ (lt_add_one _),
      fun β γ hβγ h => (hIH γ h).cohR β γ hβγ (lt_add_one γ),
      fun β γ hβγ h => (hIH γ h).cohg β γ hβγ (lt_add_one γ)⟩
    have e := hgfMU_lim_eq St A S0 hl hν H
    set L := HgfMFam.mk l (hgfMExt S0 l fun β _ => hgfMU St A S0 β) hl hν (H.congr fun β h => hgfMExt_eq St A S0 h)
      with hL
    have hF : ∀ β, β < l → L.F β = hgfMU St A S0 β := fun β h => hgfMExt_eq St A S0 h
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
      · exact hgfM_st_congr e h2' hβ hZ' (fun _ _ => L.U_start)
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

variable {α : Ordinal.{0}} {St : ∀ (Q : HgfQ α) (U : HgVD), HgSStart (hgfQPB Q) U → HgVD}
  (hSt : ∀ Q U h, HgfQSpec Q U (St Q U h))
  {A : HgfB α} {S0 : HgVD} (hS : HgfMStart A S0)
include hSt hS

theorem hgfMU_B {l : Ordinal.{0}} (hl : l < hcN α A.F) :
    (hgfMU St A S0 l).B = veblen α (A.F + 1 + l) :=
  (hgfM_inv hSt hS l hl).B l (lt_add_one l)

theorem hgfMU_self {l : Ordinal.{0}} (hl : l < hcN α A.F) : l < (hgfMU St A S0 l).B :=
  (hgfM_inv hSt hS l hl).self_lt (lt_add_one l) hl

theorem hgfMU_Zb {l : Ordinal.{0}} (hl : l < hcN α A.F) :
    ∀ x, InE x → x < Om1 → (hgfMU St A S0 l).Z x ≤ A.Zl x :=
  (hgfM_inv hSt hS l hl).Zb l (lt_add_one l)

/-- **`hgfMU λ` STARTS THE STAGE AT THE OFFSET `λ`.** -/
theorem hgfMU_start {l : Ordinal.{0}} (hl : l < hcN α A.F) :
    HgSStart (hgfMPB A (hgfMU St A S0 l) l (hgfMU_self hSt hS hl) hl (hgfMU_Zb hSt hS hl)) (hgfMU St A S0 l) :=
  (hgfM_inv hSt hS l hl).st l hl (lt_add_one l) (hgfMU_self hSt hS hl) (hgfMU_Zb hSt hS hl)

/-- **The base gate of `hgfMU λ` lies below a base `x` iff `max(γN, g(λ))` does.** -/
theorem hgfMU_γ_iff {l x : Ordinal.{0}} (hl : l < hcN α A.F) (hx : InE x) (hx1 : x < Om1) :
    (hgfMU St A S0 l).γ < x ↔ max A.γN ((hgfMU St A S0 l).g l) < x := (hgfMU_start hSt hS hl).γ x hx hx1

/-- **Later starts extend earlier ones.** -/
theorem hgfM_ext {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (hγ : γ < hcN α A.F) :
    (∀ c x, c < (hgfMU St A S0 β).B → (hgfMU St A S0 γ).R c x = (hgfMU St A S0 β).R c x) ∧
    (∀ c, c < (hgfMU St A S0 β).B → (hgfMU St A S0 γ).g c = (hgfMU St A S0 β).g c) :=
  ⟨(hgfM_inv hSt hS γ hγ).cohR β γ hβγ (lt_add_one γ), (hgfM_inv hSt hS γ hγ).cohg β γ hβγ (lt_add_one γ)⟩

/-- **The specification of the successor**: `hgfMU (λ+1)` is the step at the offset `λ`. -/
theorem hgfMU_succ_spec {l : Ordinal.{0}} (hl : l < hcN α A.F) :
    HgfQSpec (hgfQOff A (hgfMU St A S0 l) l (hgfMU_self hSt hS hl) hl (hgfMU_Zb hSt hS hl)) (hgfMU St A S0 l)
      (hgfMU St A S0 (l + 1)) := by
  rw [hgfMU_succ_eq St A S0 hl (hgfMU_self hSt hS hl) (hgfMU_Zb hSt hS hl) (hgfMU_start hSt hS hl)]
  exact hSt _ _ _

end Main

end Googology.Trans.PoR.InaccPsi.R2.Hg
