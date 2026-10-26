import Googology.Trans.PoR.InaccPsi.R2.HgPB
import Googology.Trans.PoR.InaccPsi.R2.HgS
import Googology.Trans.PoR.InaccPsi.R2.HgSRec
import Googology.Trans.PoR.InaccPsi.R2.HgSU
import Googology.Trans.PoR.InaccPsi.R2.HgX
import Googology.Trans.PoR.InaccPsi.R2.HgLv

/-!
# HgLvRec: THE RECURSION OVER THE OFFSETS OF A BASE OF ANY LEVEL, FOR ANY STEP WITH THE SPECIFICATION

(Textual copy of `Hc.HcLvRec` for `Hg.HgVD`: bound fields `< Γ_{x+2}` in place of `≤ B_x(x)` (`Hc.hcBR`); the proofs
are unchanged except where the bound enters.  Names: prefix `hg`/`Hg` (from `hc`/`Hc`), `hgd`/`Hgd` (from `hd`/`Hd`),
`hgf`/`Hgf` (from `hf`/`Hf`), `hge`/`Hge` (from `he`/`He`).)


A step of level `j+1` takes a pseudo-base `X : Hb.HgX j` and a start `U` of the stage at `X` (`Hg.hgXPB X`) to a
system `T` with the specification `HgSpec X U T`: bound `N_{j+1}(F)`, base gate `γ`, base reading `N_{j+1}(F(x))`,
bound field `evZ(N_{j+1}(F(x)))` above `γ` and `Z_o(x)` below, `T` extends `U`, reads the code `F` as `F(x)` with the
gate of `U`, and every code in `[F, N_{j+1}(F))` with gate below a base forces `γ` below it.  At level `1` the
self-read union `Hg.hgSU` is such a step (`hg_spec_SU`).

For a base `A : Hb.HgA (j+1)` (level `j+2`), a start `S0` (`HgLvStart A S0`) and a step `St` with the specification,
`hgLvU St A S0 λ` (`λ < N_{j+2}(F)`) is the start of the stage at the offset `λ`: `S0` at `0`, `St` applied to the
offset pseudo-base `Hg.hgXoff j A (hgLvU λ) λ` at `λ+1`, the union `Hg.HgLvFam.U` at a limit; `hgLv_inv`: the
invariant `Hg.HgLvInv A (ν+1)` at every `ν < N_{j+2}(F)`.

* `HgSpec`, `hg_spec_SU`, `HgLvStart`, `hgLvStep`, `hgLvExt`, `hgLvLimD`, `hgLvU` (**THE RECURSION, EVERY LEVEL**),
  `hgLv_inv` (**THE INVARIANT**), `hgLvU_B`, `hgLvU_self`, `hgLvU_Zb`, `hgLvU_start`, `hgLvU_γ_iff`, `hgLv_ext`,
  `hgLvU_succ_eq`.

No new axiom.  New definitions: `HgSpec`, `HgLvStart`, `hgLvStep`, `hgLvExt`, `hgLvLimD`, `hgLvU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hg

open Googology.Trans.PoR.InaccPsi.R2.Hc

open Googology.Trans.PoR.InaccPsi.R2.Hb

open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The specification of a step -/

/-- **The specification of a system `T` built from a start `U` of the stage at the pseudo-base `X`.** -/
structure HgSpec {j : ℕ} (X : HgX j) (U T : HgVD) : Prop where
  B : T.B = hbN (j + 1) X.F
  γ : T.γ = X.γ
  b : ∀ x, InE x → x < Om1 → X.γ < x → T.b x = hbN (j + 1) (X.Fr x)
  Z : ∀ x, InE x → x < Om1 → T.Z x = if X.γ < x then evZ (hbN (j + 1) (X.Fr x)) else X.Zo x
  extR : ∀ c x, c < U.B → T.R c x = U.R c x
  extg : ∀ c, c < U.B → T.g c = U.g c
  high : ∀ c σ, X.F ≤ c → c < hbN (j + 1) X.F → InE σ → σ < Om1 → T.g c < σ → X.γ < σ
  RF : ∀ x, InE x → x < Om1 → X.γ < x → T.R X.F x = X.Fr x
  gF : ∀ x, InE x → x < Om1 → (T.g X.F < x ↔ X.γ < x)

theorem hg_B_of_start {D : HgVD} {Bp : HgPB} (h : HgSStart Bp D) : D.B = Bp.Q := by
  rw [D.B_ix, h.ix]; exact Bp.Q_fix

/-- **The self-read union of the stage at a pseudo-base of level `1` has the specification.** -/
theorem hg_spec_SU (X : HgX 0) (U : HgVD) (h : HgSStart (hgXPB X) U) : HgSpec X U (hgSU h) where
  B := by rw [hgSU_B, hbN1_eq]; rfl
  γ := rfl
  b := fun x _ _ _ => by rw [hgSU_b, hbN1_eq]; rfl
  Z := fun x _ _ => by
    rw [hgSU_Z, hbN1_eq]; unfold hgSUZ; rfl
  extR := fun c x hc => by
    rw [hgSU_R h (hgS_zero_lt2 (Bp := hgXPB X)) (by rw [hgSD_zero]; exact hc) x, hgSD_zero]
  extg := fun c hc => by
    rw [hgSU_g h (hgS_zero_lt2 (Bp := hgXPB X)) (by rw [hgSD_zero]; exact hc), hgSD_zero]
  high := fun c σ hFc hc hσ hσ1 hg => by
    rw [hbN1_eq] at hc
    exact hgSU_high_gate h hc hFc hσ hσ1 hg
  RF := fun x hx hx1 hγ => by
    have hQ1 : (1 : Ordinal.{0}) < evZ (hgXPB X).Q := one_lt_omega0.trans (omega0_lt_inE (evZ_E _))
    have hB : U.B = X.F := hg_B_of_start h
    have hc1 : X.F < (hgSD (hgXPB X) U 1).B := by rw [hgS_one_eq, HgVD.step_B, hB]; exact lt_eN _
    rw [hgSU_R h hQ1 hc1, hgS_one_eq, HgVD.step_R, ← hB, HgVD.hR_G, h.b x hx hx1 hγ]; rfl
  gF := fun x hx hx1 => by
    have hQ1 : (1 : Ordinal.{0}) < evZ (hgXPB X).Q := one_lt_omega0.trans (omega0_lt_inE (evZ_E _))
    have hB : U.B = X.F := hg_B_of_start h
    have hc1 : X.F < (hgSD (hgXPB X) U 1).B := by rw [hgS_one_eq, HgVD.step_B, hB]; exact lt_eN _
    rw [hgSU_g h hQ1 hc1, hgS_one_eq, ← hB, HgVD.step_g_B]
    exact h.γ x hx hx1

/-! ## The start and the recursion -/

theorem hgLv_zero_lt_N {j : ℕ} (A : HgA (j + 1)) : (0 : Ordinal.{0}) < hbN (j + 1 + 1) A.F := A.N_E.pos

/-- **The start conditions** of the recursion over `A` at `S0`. -/
structure HgLvStart {j : ℕ} (A : HgA (j + 1)) (S0 : HgVD) : Prop where
  B : S0.B = veblen ((j + 1 + 1 : ℕ) : Ordinal.{0}) (A.F + 1 + 0)
  Zb : ∀ x, InE x → x < Om1 → S0.Z x ≤ A.Zl x
  st : ∀ (h2 : 0 < S0.B) (hZ : ∀ x, InE x → x < Om1 → S0.Z x ≤ A.Zl x),
    HgSStart (hgLvPB A S0 0 h2 (hgLv_zero_lt_N A) hZ) S0
  high0 : ∀ c σ, A.F ≤ c → c < S0.B → InE σ → σ < Om1 → S0.g c < σ → A.γ < σ

section Rec

variable {j : ℕ} (St : ∀ (X : HgX j) (U : HgVD), HgSStart (hgXPB X) U → HgVD) (A : HgA (j + 1)) (S0 : HgVD)

/-- The successor step: the step `St` at the offset pseudo-base `λ` started at `U` (when `U` starts it). -/
noncomputable def hgLvStep (μ : Ordinal.{0}) (U : HgVD) : HgVD := by
  classical
  exact if h : ∃ (hμ : μ < hbN (j + 1 + 1) A.F) (h2 : μ < U.B) (hZ : ∀ x, InE x → x < Om1 → U.Z x ≤ A.Zl x),
      HgSStart (hgLvPB A U μ h2 hμ hZ) U then
    St (hgXoff j A U μ h.choose_spec.choose h.choose h.choose_spec.choose_spec.choose) U
      h.choose_spec.choose_spec.choose_spec else U

/-- The family of the earlier values, extended by the start at `0`. -/
noncomputable def hgLvExt (l : Ordinal.{0}) (IH : ∀ β, β < l → HgVD) (β : Ordinal.{0}) : HgVD :=
  if h : β < l then IH β h else S0

open Classical in
/-- The limit step: the union of all earlier starts when the invariant holds. -/
noncomputable def hgLvLimD (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ β, β < l → HgVD) : HgVD :=
  if H : l < hbN (j + 1 + 1) A.F ∧ HgLvInv A l (hgLvExt S0 l IH) then
    (HgLvFam.mk l (hgLvExt S0 l IH) hl H.1 H.2).U else S0

/-- **THE RECURSION OVER THE OFFSETS OF A BASE OF LEVEL `j+2`**, for the step `St`. -/
noncomputable def hgLvU (ν : Ordinal.{0}) : HgVD :=
  Ordinal.limitRecOn (motive := fun _ => HgVD) ν S0 (hgLvStep St A) (hgLvLimD A S0)

theorem hgLvU_zero : hgLvU St A S0 0 = S0 := by unfold hgLvU; rw [Ordinal.limitRecOn_zero]

theorem hgLvU_succ (ν : Ordinal.{0}) : hgLvU St A S0 (ν + 1) = hgLvStep St A ν (hgLvU St A S0 ν) := by
  unfold hgLvU; rw [Ordinal.limitRecOn_add_one]

theorem hgLvU_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) :
    hgLvU St A S0 l = hgLvLimD A S0 l hl (fun β _ => hgLvU St A S0 β) := by
  unfold hgLvU; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem hgLvExt_eq {l β : Ordinal.{0}} (h : β < l) :
    hgLvExt S0 l (fun β _ => hgLvU St A S0 β) β = hgLvU St A S0 β := by
  unfold hgLvExt; rw [dif_pos h]

/-- The successor value when `hgLvU ν` starts the stage at the offset `ν`. -/
theorem hgLvU_succ_eq {ν : Ordinal.{0}} (hν : ν < hbN (j + 1 + 1) A.F) (h2 : ν < (hgLvU St A S0 ν).B)
    (hZ : ∀ x, InE x → x < Om1 → (hgLvU St A S0 ν).Z x ≤ A.Zl x)
    (h : HgSStart (hgLvPB A (hgLvU St A S0 ν) ν h2 hν hZ) (hgLvU St A S0 ν)) :
    hgLvU St A S0 (ν + 1) = St (hgXoff j A (hgLvU St A S0 ν) ν h2 hν hZ) (hgLvU St A S0 ν) h := by
  rw [hgLvU_succ]; unfold hgLvStep
  rw [dif_pos ⟨hν, h2, hZ, h⟩]

theorem hgLvU_lim_eq {l : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l < hbN (j + 1 + 1) A.F)
    (H : HgLvInv A l (hgLvU St A S0)) :
    hgLvU St A S0 l = (HgLvFam.mk l (hgLvExt S0 l fun β _ => hgLvU St A S0 β) hl hle
      (H.congr fun β h => hgLvExt_eq St A S0 h)).U := by
  rw [hgLvU_limit St A S0 hl]; unfold hgLvLimD; rw [dif_pos ⟨hle, H.congr fun β h => hgLvExt_eq St A S0 h⟩]

end Rec

theorem hg_ix_of_B {T : HgVD} {Q : Ordinal.{0}} (hQ : veblen 1 Q = Q) (hB : T.B = Q) : T.ix = Q := by
  have h : veblen 1 T.ix = veblen 1 Q := by rw [← T.B_ix, hB, hQ]
  exact (veblen_inj).1 h

/-- **THE INVARIANT**: every `hgLvU St A S0 λ`, `λ < N_{j+2}(F)`, starts the stage at the offset `λ`, has bound field
below `Z_l`, the starts at successors have the high-gate property, and later starts extend earlier ones. -/
theorem hgLv_inv {j : ℕ} {St : ∀ (X : HgX j) (U : HgVD), HgSStart (hgXPB X) U → HgVD}
    (hSt : ∀ X U h, HgSpec X U (St X U h)) {A : HgA (j + 1)} {S0 : HgVD} (hS : HgLvStart A S0) :
    ∀ ν : Ordinal.{0}, ν < hbN (j + 1 + 1) A.F → HgLvInv A (ν + 1) (hgLvU St A S0) := by
  intro ν
  induction ν using Ordinal.limitRecOn with
  | zero =>
    intro _
    have h0 : ∀ μ : Ordinal.{0}, μ < 0 + 1 → μ = 0 := fun μ h => Order.lt_one_iff.1 (by rwa [zero_add] at h)
    refine ⟨fun μ h => ?_, fun μ h => ?_, fun μ hμ h h2 hZ => ?_, fun μ h => ?_, fun β γ hβγ h c x _ => ?_,
      fun β γ hβγ h c _ => ?_⟩
    · rw [h0 μ h, hgLvU_zero]; exact hS.B
    · rw [h0 μ h, hgLvU_zero]; exact hS.Zb
    · obtain rfl := h0 μ h
      exact hgLv_st_congr (hgLvU_zero St A S0) h2 hμ hZ (fun h2' hZ' => hS.st h2' hZ')
    · exact absurd (h0 (μ + 1) h) (ne_of_gt (lt_of_le_of_lt zero_le (lt_add_one μ)))
    · have hγ := h0 γ h
      have hβ : β = 0 := le_antisymm (hγ ▸ hβγ) zero_le
      rw [hγ, hβ]
    · have hγ := h0 γ h
      have hβ : β = 0 := le_antisymm (hγ ▸ hβγ) zero_le
      rw [hγ, hβ]
  | add_one μ ih =>
    intro hν
    have hμT : μ < hbN (j + 1 + 1) A.F := (lt_add_one μ).trans hν
    have H := ih hμT
    have h2 : μ < (hgLvU St A S0 μ).B := H.self_lt (lt_add_one μ) hμT
    have hZ := H.Zb μ (lt_add_one μ)
    have hst := H.st μ hμT (lt_add_one μ) h2 hZ
    set X := hgXoff j A (hgLvU St A S0 μ) μ h2 hμT hZ with hX
    have e := hgLvU_succ_eq St A S0 hμT h2 hZ hst
    have hsp := hSt X (hgLvU St A S0 μ) hst
    have hBμ : (hgLvU St A S0 μ).B = X.F := H.B μ (lt_add_one μ)
    have hB1 : (hgLvU St A S0 (μ + 1)).B = veblen ((j + 1 + 1 : ℕ) : Ordinal.{0}) (A.F + 1 + (μ + 1)) := by
      rw [e, hsp.B]
      show hbN (j + 1) (veblen ((j + 1 + 1 : ℕ) : Ordinal.{0}) (A.F + 1 + μ)) = _
      rw [hbN_veb, add_assoc (A.F + 1) μ 1]
    have hZ1 : ∀ x, InE x → x < Om1 → (hgLvU St A S0 (μ + 1)).Z x ≤ A.Zl x := fun x hx hx1 => by
      rw [e, hsp.Z x hx hx1]
      split_ifs with hγ
      · exact (hb_evZ_lt_fix2 (A.Zl_fix (by omega) x) (X.N_Zo hx hx1 hγ)).le
      · exact le_rfl
    have h1B : μ + 1 < (hgLvU St A S0 μ).B := (ev_isSuccLimit_of_inE (hgLvU St A S0 μ).B_E).add_one_lt h2
    have hext : ∀ c x, c < (hgLvU St A S0 μ).B → (hgLvU St A S0 (μ + 1)).R c x = (hgLvU St A S0 μ).R c x :=
      fun c x hc => by rw [e]; exact hsp.extR c x hc
    have hextg : ∀ c, c < (hgLvU St A S0 μ).B → (hgLvU St A S0 (μ + 1)).g c = (hgLvU St A S0 μ).g c :=
      fun c hc => by rw [e]; exact hsp.extg c hc
    have hgiff : ∀ x, InE x → x < Om1 → ((hgLvU St A S0 μ).g μ < x ↔ (hgLvU St A S0 μ).g (μ + 1) < x) :=
      fun x hx _ => ⟨fun h => (hgLvU St A S0 μ).g_succ x (ev_isSuccLimit_of_inE hx) μ h1B h,
        fun h => ((hgLvU St A S0 μ).g_le_succ μ).trans_lt h⟩
    have hFr1 : ∀ x, InE x → x < Om1 → X.γ < x →
        glA ((j + 1 + 1 : ℕ) : Ordinal.{0}) (A.Fr x + (hgLvU St A S0 (μ + 1)).R (μ + 1) x) x =
          hbN (j + 1) (X.Fr x) := fun x hx hx1 hγ => by
      rw [hext (μ + 1) x h1B, (hgLvU St A S0 μ).R_succ, ← add_assoc]
      exact hb_glA_succ hx hx1 (j + 1) (hgXoff_t1_lt1 j A _ μ h2 hZ hx hx1 hγ)
    have hstS : ∀ (h2' : μ + 1 < (hgLvU St A S0 (μ + 1)).B) (hZ' : ∀ x, InE x → x < Om1 →
        (hgLvU St A S0 (μ + 1)).Z x ≤ A.Zl x),
        HgSStart (hgLvPB A (hgLvU St A S0 (μ + 1)) (μ + 1) h2' hν hZ') (hgLvU St A S0 (μ + 1)) := fun h2' hZ' => by
      have hγiff : ∀ x, InE x → x < Om1 →
          ((hgLvU St A S0 (μ + 1)).γ < x ↔ max A.γ ((hgLvU St A S0 (μ + 1)).g (μ + 1)) < x) := fun x hx hx1 => by
        rw [e, hsp.γ]
        show max A.γ ((hgLvU St A S0 μ).g μ) < x ↔ max A.γ ((St X _ hst).g (μ + 1)) < x
        rw [← e, hextg (μ + 1) h1B, max_lt_iff, max_lt_iff]
        exact and_congr_right fun _ => hgiff x hx hx1
      refine ⟨?_, hγiff, fun x hx hx1 hγ => ?_, fun x hx hx1 => ?_⟩
      · refine hg_ix_of_B ?_ hB1
        exact hb_fix_down (j := 1) (by omega) (hb_fix_veb (j + 1) _) |> fun h => by rwa [Nat.cast_one] at h
      · have hγ' : X.γ < x := by
          have := (hγiff x hx hx1).2 hγ; rw [e, hsp.γ] at this; exact this
        show (hgLvU St A S0 (μ + 1)).b x = glA ((j + 1 + 1 : ℕ) : Ordinal.{0}) (A.Fr x + (hgLvU St A S0 (μ + 1)).R
            (μ + 1) x) x
        rw [hFr1 x hx hx1 hγ', e]; exact hsp.b x hx hx1 hγ'
      · show (hgLvU St A S0 (μ + 1)).Z x = HgPB.Zst (hgLvPB A (hgLvU St A S0 (μ + 1)) (μ + 1) h2' hν hZ') x
        unfold HgPB.Zst
        have hZe := hsp.Z x hx hx1
        rw [← e] at hZe
        rw [hZe]
        show (if X.γ < x then evZ (hbN (j + 1) (X.Fr x)) else A.Zl x) =
          if max A.γ ((hgLvU St A S0 (μ + 1)).g (μ + 1)) < x then
            evZ (glA ((j + 1 + 1 : ℕ) : Ordinal.{0}) (A.Fr x + (hgLvU St A S0 (μ + 1)).R (μ + 1) x) x) else A.Zl x
        have hiff : X.γ < x ↔ max A.γ ((hgLvU St A S0 (μ + 1)).g (μ + 1)) < x := by
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
          have hcμ : c < (hgLvU St A S0 μ).B := hc.trans_le (by
            rw [H.B β (lt_of_le_of_lt hβμ (lt_add_one μ)), H.B μ (lt_add_one μ)]
            exact (isNormal_veblen _).monotone ((add_le_add_iff_left _).2 hβμ))
          rw [hext c x hcμ]; exact H.cohR β μ hβμ (lt_add_one μ) c x hc
        · rfl
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.cohg β γ hβγ h' c hc
      · rcases hβγ.lt_or_eq with h'' | rfl
        · have hβμ : β ≤ μ := Order.lt_add_one_iff.1 h''
          have hcμ : c < (hgLvU St A S0 μ).B := hc.trans_le (by
            rw [H.B β (lt_of_le_of_lt hβμ (lt_add_one μ)), H.B μ (lt_add_one μ)]
            exact (isNormal_veblen _).monotone ((add_le_add_iff_left _).2 hβμ))
          rw [hextg c hcμ]; exact H.cohg β μ hβμ (lt_add_one μ) c hc
        · rfl
  | limit l hl ih =>
    intro hν
    have hIH : ∀ β, β < l → HgLvInv A (β + 1) (hgLvU St A S0) := fun β h => ih β h (h.trans hν)
    have H : HgLvInv A l (hgLvU St A S0) := ⟨fun μ h => (hIH μ h).B μ (lt_add_one μ),
      fun μ h => (hIH μ h).Zb μ (lt_add_one μ),
      fun μ hμ h => (hIH μ h).st μ hμ (lt_add_one μ),
      fun μ h => (hIH (μ + 1) h).high μ (lt_add_one _),
      fun β γ hβγ h => (hIH γ h).cohR β γ hβγ (lt_add_one γ),
      fun β γ hβγ h => (hIH γ h).cohg β γ hβγ (lt_add_one γ)⟩
    have e := hgLvU_lim_eq St A S0 hl hν H
    set L := HgLvFam.mk l (hgLvExt S0 l fun β _ => hgLvU St A S0 β) hl hν (H.congr fun β h => hgLvExt_eq St A S0 h)
      with hL
    have hF : ∀ β, β < l → L.F β = hgLvU St A S0 β := fun β h => hgLvExt_eq St A S0 h
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
      · exact hgLv_st_congr e h2' hβ hZ' (fun _ _ => L.U_start)
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

variable {j : ℕ} {St : ∀ (X : HgX j) (U : HgVD), HgSStart (hgXPB X) U → HgVD}
  (hSt : ∀ X U h, HgSpec X U (St X U h)) {A : HgA (j + 1)} {S0 : HgVD} (hS : HgLvStart A S0)
include hSt hS

theorem hgLvU_B {l : Ordinal.{0}} (hl : l < hbN (j + 1 + 1) A.F) :
    (hgLvU St A S0 l).B = veblen ((j + 1 + 1 : ℕ) : Ordinal.{0}) (A.F + 1 + l) :=
  (hgLv_inv hSt hS l hl).B l (lt_add_one l)

theorem hgLvU_self {l : Ordinal.{0}} (hl : l < hbN (j + 1 + 1) A.F) : l < (hgLvU St A S0 l).B :=
  (hgLv_inv hSt hS l hl).self_lt (lt_add_one l) hl

theorem hgLvU_Zb {l : Ordinal.{0}} (hl : l < hbN (j + 1 + 1) A.F) :
    ∀ x, InE x → x < Om1 → (hgLvU St A S0 l).Z x ≤ A.Zl x :=
  (hgLv_inv hSt hS l hl).Zb l (lt_add_one l)

/-- **`hgLvU λ` STARTS THE STAGE AT THE OFFSET `λ`.** -/
theorem hgLvU_start {l : Ordinal.{0}} (hl : l < hbN (j + 1 + 1) A.F) :
    HgSStart (hgLvPB A (hgLvU St A S0 l) l (hgLvU_self hSt hS hl) hl (hgLvU_Zb hSt hS hl)) (hgLvU St A S0 l) :=
  (hgLv_inv hSt hS l hl).st l hl (lt_add_one l) (hgLvU_self hSt hS hl) (hgLvU_Zb hSt hS hl)

/-- **The base gate of `hgLvU λ` lies below a base `x` iff `max(γ, g(λ))` does.** -/
theorem hgLvU_γ_iff {l x : Ordinal.{0}} (hl : l < hbN (j + 1 + 1) A.F) (hx : InE x) (hx1 : x < Om1) :
    (hgLvU St A S0 l).γ < x ↔ max A.γ ((hgLvU St A S0 l).g l) < x := (hgLvU_start hSt hS hl).γ x hx hx1

/-- **Later starts extend earlier ones.** -/
theorem hgLv_ext {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (hγ : γ < hbN (j + 1 + 1) A.F) :
    (∀ c x, c < (hgLvU St A S0 β).B → (hgLvU St A S0 γ).R c x = (hgLvU St A S0 β).R c x) ∧
    (∀ c, c < (hgLvU St A S0 β).B → (hgLvU St A S0 γ).g c = (hgLvU St A S0 β).g c) :=
  ⟨(hgLv_inv hSt hS γ hγ).cohR β γ hβγ (lt_add_one γ), (hgLv_inv hSt hS γ hγ).cohg β γ hβγ (lt_add_one γ)⟩

/-- **The specification of the successor**: `hgLvU (λ+1)` is the step at the offset `λ`. -/
theorem hgLvU_succ_spec {l : Ordinal.{0}} (hl : l < hbN (j + 1 + 1) A.F) :
    HgSpec (hgXoff j A (hgLvU St A S0 l) l (hgLvU_self hSt hS hl) hl (hgLvU_Zb hSt hS hl)) (hgLvU St A S0 l)
      (hgLvU St A S0 (l + 1)) := by
  rw [hgLvU_succ_eq St A S0 hl (hgLvU_self hSt hS hl) (hgLvU_Zb hSt hS hl) (hgLvU_start hSt hS hl)]
  exact hSt _ _ _

end Main

end Googology.Trans.PoR.InaccPsi.R2.Hg
