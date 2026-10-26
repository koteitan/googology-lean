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

/-!
# HgdLvRec: THE GATED RECURSION OVER THE OFFSETS OF A BASE OF LEVEL `ω`

(Textual copy of `Hd.HdLvRec` for `Hg.HgVD`: bound fields `< Γ_{x+2}` in place of `≤ B_x(x)` (`Hc.hcBR`); the proofs
are unchanged except where the bound enters.  Names: prefix `hg`/`Hg` (from `hc`/`Hc`), `hgd`/`Hgd` (from `hd`/`Hd`),
`hgf`/`Hgf` (from `hf`/`Hf`), `hge`/`Hge` (from `he`/`He`).)

The level-`ω` version of `Hc.HcLvRec`, with the gated `ω`-step `Hg.hgdStep` as the step.  For a base `A : Hd.HgdA`
of level `ω` and a start `S0` (`HgdLvStart A S0`: bound `φ(ω, F+1)`, bound field below `Z_l`, starts the stage at the
offset `0`, high-gate property), `hgdLvU A S0 λ` (`λ < N_ω(F)`, every `λ`, read by a code with a gate) is the start of
the stage at the offset `λ`: `S0` at `0`, the `ω`-step at the gated offset pseudo-base `Hg.hgdOff A (hgdLvU λ) λ` at
`λ+1`, the union `Hg.HgdLvFam.U` at a limit.  `hgdLv_inv`: the invariant `Hg.HgdLvInv A (ν+1)` at every `ν < N_ω(F)`.

* `hgdLv_zero_lt_N`, `HgdLvStart`, `hgdLvStep`, `hgdLvExt`, `hgdLvLimD`, `hgdLvU` (**THE GATED OFFSET RECURSION OF LEVEL
  `ω`**), `hgdLv_inv` (**THE INVARIANT**), `hgdLvU_B`, `hgdLvU_self`, `hgdLvU_Zb`, `hgdLvU_start`, `hgdLvU_γ_iff`,
  `hgdLv_ext`, `hgdLvU_succ_spec`.

No new axiom.  New definitions: `HgdLvStart`, `hgdLvStep`, `hgdLvExt`, `hgdLvLimD`, `hgdLvU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hg

open Googology.Trans.PoR.InaccPsi.R2.Hc
open Googology.Trans.PoR.InaccPsi.R2.Hd

open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

theorem hgdLv_zero_lt_N (A : HgdA) : (0 : Ordinal.{0}) < hcNw A.F := A.N_E.pos

/-- **The start conditions** of the recursion over `A` at `S0`. -/
structure HgdLvStart (A : HgdA) (S0 : HgVD) : Prop where
  B : S0.B = veblen ω (A.F + 1 + 0)
  Zb : ∀ x, InE x → x < Om1 → S0.Z x ≤ A.Zl x
  st : ∀ (h2 : 0 < S0.B) (hZ : ∀ x, InE x → x < Om1 → S0.Z x ≤ A.Zl x),
    HgSStart (hgdLvPB A S0 0 h2 (hgdLv_zero_lt_N A) hZ) S0
  high0 : ∀ c σ, A.F ≤ c → c < S0.B → InE σ → σ < Om1 → S0.g c < σ → A.γ < σ

section Rec

variable (A : HgdA) (S0 : HgVD)

/-- The successor step: the `ω`-step at the offset pseudo-base `λ` started at `U` (when `U` starts it). -/
noncomputable def hgdLvStep (μ : Ordinal.{0}) (U : HgVD) : HgVD := by
  classical
  exact if h : ∃ (hμ : μ < hcNw A.F) (h2 : μ < U.B) (hZ : ∀ x, InE x → x < Om1 → U.Z x ≤ A.Zl x),
      HgSStart (hgdLvPB A U μ h2 hμ hZ) U then
    hgdStep (hgdOff A U μ h.choose_spec.choose h.choose h.choose_spec.choose_spec.choose) U
      h.choose_spec.choose_spec.choose_spec else U

/-- The family of the earlier values, extended by the start at `0`. -/
noncomputable def hgdLvExt (l : Ordinal.{0}) (IH : ∀ β, β < l → HgVD) (β : Ordinal.{0}) : HgVD :=
  if h : β < l then IH β h else S0

open Classical in
/-- The limit step: the union of all earlier starts when the invariant holds. -/
noncomputable def hgdLvLimD (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ β, β < l → HgVD) : HgVD :=
  if H : l < hcNw A.F ∧ HgdLvInv A l (hgdLvExt S0 l IH) then
    (HgdLvFam.mk l (hgdLvExt S0 l IH) hl H.1 H.2).U else S0

/-- **THE GATED OFFSET RECURSION OF LEVEL `ω`.** -/
noncomputable def hgdLvU (ν : Ordinal.{0}) : HgVD :=
  Ordinal.limitRecOn (motive := fun _ => HgVD) ν S0 (hgdLvStep A) (hgdLvLimD A S0)

theorem hgdLvU_zero : hgdLvU A S0 0 = S0 := by unfold hgdLvU; rw [Ordinal.limitRecOn_zero]

theorem hgdLvU_succ (ν : Ordinal.{0}) : hgdLvU A S0 (ν + 1) = hgdLvStep A ν (hgdLvU A S0 ν) := by
  unfold hgdLvU; rw [Ordinal.limitRecOn_add_one]

theorem hgdLvU_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) :
    hgdLvU A S0 l = hgdLvLimD A S0 l hl (fun β _ => hgdLvU A S0 β) := by
  unfold hgdLvU; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem hgdLvExt_eq {l β : Ordinal.{0}} (h : β < l) :
    hgdLvExt S0 l (fun β _ => hgdLvU A S0 β) β = hgdLvU A S0 β := by
  unfold hgdLvExt; rw [dif_pos h]

/-- The successor value when `hgdLvU ν` starts the stage at the offset `ν`. -/
theorem hgdLvU_succ_eq {ν : Ordinal.{0}} (hν : ν < hcNw A.F) (h2 : ν < (hgdLvU A S0 ν).B)
    (hZ : ∀ x, InE x → x < Om1 → (hgdLvU A S0 ν).Z x ≤ A.Zl x)
    (h : HgSStart (hgdLvPB A (hgdLvU A S0 ν) ν h2 hν hZ) (hgdLvU A S0 ν)) :
    hgdLvU A S0 (ν + 1) = hgdStep (hgdOff A (hgdLvU A S0 ν) ν h2 hν hZ) (hgdLvU A S0 ν) h := by
  rw [hgdLvU_succ]; unfold hgdLvStep
  rw [dif_pos ⟨hν, h2, hZ, h⟩]

theorem hgdLvU_lim_eq {l : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l < hcNw A.F)
    (H : HgdLvInv A l (hgdLvU A S0)) :
    hgdLvU A S0 l = (HgdLvFam.mk l (hgdLvExt S0 l fun β _ => hgdLvU A S0 β) hl hle
      (H.congr fun β h => hgdLvExt_eq A S0 h)).U := by
  rw [hgdLvU_limit A S0 hl]; unfold hgdLvLimD; rw [dif_pos ⟨hle, H.congr fun β h => hgdLvExt_eq A S0 h⟩]

end Rec

/-- **THE INVARIANT**: every `hgdLvU A S0 λ`, `λ < N_ω(F)`, starts the stage at the offset `λ`, has bound field
below `Z_l`, the starts at successors have the high-gate property, and later starts extend earlier ones. -/
theorem hgdLv_inv {A : HgdA} {S0 : HgVD} (hS : HgdLvStart A S0) :
    ∀ ν : Ordinal.{0}, ν < hcNw A.F → HgdLvInv A (ν + 1) (hgdLvU A S0) := by
  intro ν
  induction ν using Ordinal.limitRecOn with
  | zero =>
    intro _
    have h0 : ∀ μ : Ordinal.{0}, μ < 0 + 1 → μ = 0 := fun μ h => Order.lt_one_iff.1 (by rwa [zero_add] at h)
    refine ⟨fun μ h => ?_, fun μ h => ?_, fun μ hμ h h2 hZ => ?_, fun μ h => ?_, fun β γ hβγ h c x _ => ?_,
      fun β γ hβγ h c _ => ?_⟩
    · rw [h0 μ h, hgdLvU_zero]; exact hS.B
    · rw [h0 μ h, hgdLvU_zero]; exact hS.Zb
    · obtain rfl := h0 μ h
      exact hgdLv_st_congr (hgdLvU_zero A S0) h2 hμ hZ (fun h2' hZ' => hS.st h2' hZ')
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
    have h2 : μ < (hgdLvU A S0 μ).B := H.self_lt (lt_add_one μ) hμT
    have hZ := H.Zb μ (lt_add_one μ)
    have hst := H.st μ hμT (lt_add_one μ) h2 hZ
    set X := hgdOff A (hgdLvU A S0 μ) μ h2 hμT hZ with hX
    have e := hgdLvU_succ_eq A S0 hμT h2 hZ hst
    have hsp := hgdStep_spec X (hgdLvU A S0 μ) hst
    have hBμ : (hgdLvU A S0 μ).B = X.F := H.B μ (lt_add_one μ)
    have hB1 : (hgdLvU A S0 (μ + 1)).B = veblen ω (A.F + 1 + (μ + 1)) := by
      rw [e, hsp.B]
      show hcS (veblen ω (A.F + 1 + μ)) = _
      rw [hcS_veb_eq, add_assoc (A.F + 1) μ 1]
    have hZ1 : ∀ x, InE x → x < Om1 → (hgdLvU A S0 (μ + 1)).Z x ≤ A.Zl x := fun x hx hx1 => by
      rw [e, hsp.Z x hx hx1]
      split_ifs with hγ
      · exact (hb_evZ_lt_fix2 (A.Zl_fix x) (X.S_Zo hx hx1 hγ)).le
      · exact le_rfl
    have h1B : μ + 1 < (hgdLvU A S0 μ).B := (ev_isSuccLimit_of_inE (hgdLvU A S0 μ).B_E).add_one_lt h2
    have hext : ∀ c x, c < (hgdLvU A S0 μ).B → (hgdLvU A S0 (μ + 1)).R c x = (hgdLvU A S0 μ).R c x :=
      fun c x hc => by rw [e]; exact hsp.extR c x hc
    have hextg : ∀ c, c < (hgdLvU A S0 μ).B → (hgdLvU A S0 (μ + 1)).g c = (hgdLvU A S0 μ).g c :=
      fun c hc => by rw [e]; exact hsp.extg c hc
    have hgiff : ∀ x, InE x → x < Om1 → ((hgdLvU A S0 μ).g μ < x ↔ (hgdLvU A S0 μ).g (μ + 1) < x) :=
      fun x hx _ => ⟨fun h => (hgdLvU A S0 μ).g_succ x (ev_isSuccLimit_of_inE hx) μ h1B h,
        fun h => ((hgdLvU A S0 μ).g_le_succ μ).trans_lt h⟩
    have hFr1 : ∀ x, InE x → x < Om1 → X.γ < x →
        glA ω (A.Fr x + (hgdLvU A S0 (μ + 1)).R (μ + 1) x) x =
          hcS (X.Fr x) := fun x hx hx1 hγ => by
      rw [hext (μ + 1) x h1B, (hgdLvU A S0 μ).R_succ, ← add_assoc]
      exact hd_glA_succ hx hx1 (A.t1_lt1 hx hx1 (max_lt_iff.1 hγ).1 (hgdOff_R_lt A _ μ h2 hZ hx hx1 hγ))
    have hstS : ∀ (h2' : μ + 1 < (hgdLvU A S0 (μ + 1)).B) (hZ' : ∀ x, InE x → x < Om1 →
        (hgdLvU A S0 (μ + 1)).Z x ≤ A.Zl x),
        HgSStart (hgdLvPB A (hgdLvU A S0 (μ + 1)) (μ + 1) h2' hν hZ') (hgdLvU A S0 (μ + 1)) := fun h2' hZ' => by
      have hγiff : ∀ x, InE x → x < Om1 →
          ((hgdLvU A S0 (μ + 1)).γ < x ↔ max A.γ ((hgdLvU A S0 (μ + 1)).g (μ + 1)) < x) := fun x hx hx1 => by
        rw [e, hsp.γ]
        show max A.γ ((hgdLvU A S0 μ).g μ) < x ↔ max A.γ ((hgdStep X _ hst).g (μ + 1)) < x
        rw [← e, hextg (μ + 1) h1B, max_lt_iff, max_lt_iff]
        exact and_congr_right fun _ => hgiff x hx hx1
      refine ⟨?_, hγiff, fun x hx hx1 hγ => ?_, fun x hx hx1 => ?_⟩
      · refine hg_ix_of_B ?_ hB1
        exact hd_veb_fix1 _
      · have hγ' : X.γ < x := by
          have := (hγiff x hx hx1).2 hγ; rw [e, hsp.γ] at this; exact this
        show (hgdLvU A S0 (μ + 1)).b x = glA ω (A.Fr x + (hgdLvU A S0 (μ + 1)).R
            (μ + 1) x) x
        rw [hFr1 x hx hx1 hγ', e]; exact hsp.b x hx hx1 hγ'
      · show (hgdLvU A S0 (μ + 1)).Z x = HgPB.Zst (hgdLvPB A (hgdLvU A S0 (μ + 1)) (μ + 1) h2' hν hZ') x
        unfold HgPB.Zst
        have hZe := hsp.Z x hx hx1
        rw [← e] at hZe
        rw [hZe]
        show (if X.γ < x then evZ (hcS (X.Fr x)) else A.Zl x) =
          if max A.γ ((hgdLvU A S0 (μ + 1)).g (μ + 1)) < x then
            evZ (glA ω (A.Fr x + (hgdLvU A S0 (μ + 1)).R (μ + 1) x) x) else A.Zl x
        have hiff : X.γ < x ↔ max A.γ ((hgdLvU A S0 (μ + 1)).g (μ + 1)) < x := by
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
          have hcμ : c < (hgdLvU A S0 μ).B := hc.trans_le (by
            rw [H.B β (lt_of_le_of_lt hβμ (lt_add_one μ)), H.B μ (lt_add_one μ)]
            exact (isNormal_veblen _).monotone ((add_le_add_iff_left _).2 hβμ))
          rw [hext c x hcμ]; exact H.cohR β μ hβμ (lt_add_one μ) c x hc
        · rfl
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.cohg β γ hβγ h' c hc
      · rcases hβγ.lt_or_eq with h'' | rfl
        · have hβμ : β ≤ μ := Order.lt_add_one_iff.1 h''
          have hcμ : c < (hgdLvU A S0 μ).B := hc.trans_le (by
            rw [H.B β (lt_of_le_of_lt hβμ (lt_add_one μ)), H.B μ (lt_add_one μ)]
            exact (isNormal_veblen _).monotone ((add_le_add_iff_left _).2 hβμ))
          rw [hextg c hcμ]; exact H.cohg β μ hβμ (lt_add_one μ) c hc
        · rfl
  | limit l hl ih =>
    intro hν
    have hIH : ∀ β, β < l → HgdLvInv A (β + 1) (hgdLvU A S0) := fun β h => ih β h (h.trans hν)
    have H : HgdLvInv A l (hgdLvU A S0) := ⟨fun μ h => (hIH μ h).B μ (lt_add_one μ),
      fun μ h => (hIH μ h).Zb μ (lt_add_one μ),
      fun μ hμ h => (hIH μ h).st μ hμ (lt_add_one μ),
      fun μ h => (hIH (μ + 1) h).high μ (lt_add_one _),
      fun β γ hβγ h => (hIH γ h).cohR β γ hβγ (lt_add_one γ),
      fun β γ hβγ h => (hIH γ h).cohg β γ hβγ (lt_add_one γ)⟩
    have e := hgdLvU_lim_eq A S0 hl hν H
    set L := HgdLvFam.mk l (hgdLvExt S0 l fun β _ => hgdLvU A S0 β) hl hν (H.congr fun β h => hgdLvExt_eq A S0 h)
      with hL
    have hF : ∀ β, β < l → L.F β = hgdLvU A S0 β := fun β h => hgdLvExt_eq A S0 h
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
      · exact hgdLv_st_congr e h2' hβ hZ' (fun _ _ => L.U_start)
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

variable {A : HgdA} {S0 : HgVD} (hS : HgdLvStart A S0)
include hS

theorem hgdLvU_B {l : Ordinal.{0}} (hl : l < hcNw A.F) :
    (hgdLvU A S0 l).B = veblen ω (A.F + 1 + l) :=
  (hgdLv_inv hS l hl).B l (lt_add_one l)

theorem hgdLvU_self {l : Ordinal.{0}} (hl : l < hcNw A.F) : l < (hgdLvU A S0 l).B :=
  (hgdLv_inv hS l hl).self_lt (lt_add_one l) hl

theorem hgdLvU_Zb {l : Ordinal.{0}} (hl : l < hcNw A.F) :
    ∀ x, InE x → x < Om1 → (hgdLvU A S0 l).Z x ≤ A.Zl x :=
  (hgdLv_inv hS l hl).Zb l (lt_add_one l)

/-- **`hgdLvU λ` STARTS THE STAGE AT THE OFFSET `λ`.** -/
theorem hgdLvU_start {l : Ordinal.{0}} (hl : l < hcNw A.F) :
    HgSStart (hgdLvPB A (hgdLvU A S0 l) l (hgdLvU_self hS hl) hl (hgdLvU_Zb hS hl)) (hgdLvU A S0 l) :=
  (hgdLv_inv hS l hl).st l hl (lt_add_one l) (hgdLvU_self hS hl) (hgdLvU_Zb hS hl)

/-- **The base gate of `hgdLvU λ` lies below a base `x` iff `max(γ, g(λ))` does.** -/
theorem hgdLvU_γ_iff {l x : Ordinal.{0}} (hl : l < hcNw A.F) (hx : InE x) (hx1 : x < Om1) :
    (hgdLvU A S0 l).γ < x ↔ max A.γ ((hgdLvU A S0 l).g l) < x := (hgdLvU_start hS hl).γ x hx hx1

/-- **Later starts extend earlier ones.** -/
theorem hgdLv_ext {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (hγ : γ < hcNw A.F) :
    (∀ c x, c < (hgdLvU A S0 β).B → (hgdLvU A S0 γ).R c x = (hgdLvU A S0 β).R c x) ∧
    (∀ c, c < (hgdLvU A S0 β).B → (hgdLvU A S0 γ).g c = (hgdLvU A S0 β).g c) :=
  ⟨(hgdLv_inv hS γ hγ).cohR β γ hβγ (lt_add_one γ), (hgdLv_inv hS γ hγ).cohg β γ hβγ (lt_add_one γ)⟩

/-- **The specification of the successor**: `hgdLvU (λ+1)` is the step at the offset `λ`. -/
theorem hgdLvU_succ_spec {l : Ordinal.{0}} (hl : l < hcNw A.F) :
    HgdSpec (hgdOff A (hgdLvU A S0 l) l (hgdLvU_self hS hl) hl (hgdLvU_Zb hS hl)) (hgdLvU A S0 l)
      (hgdLvU A S0 (l + 1)) := by
  rw [hgdLvU_succ_eq A S0 hl (hgdLvU_self hS hl) (hgdLvU_Zb hS hl) (hgdLvU_start hS hl)]
  exact hgdStep_spec _ _ _

end Main

end Googology.Trans.PoR.InaccPsi.R2.Hg
