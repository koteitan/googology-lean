import Googology.Trans.PoR.InaccPsi.R2.HcLv

/-!
# HcLvRec: THE RECURSION OVER THE OFFSETS OF A BASE OF ANY LEVEL, FOR ANY STEP WITH THE SPECIFICATION

(Textual copy of `Hb.HbLvRec` for `Hc.HcVD`: bound fields `≤ B_x(x)` (`Hc.hcBR`) in place of `≤ B_ω(x)`;
the proofs are unchanged.)

A step of level `j+1` takes a pseudo-base `X : Hb.HcX j` and a start `U` of the stage at `X` (`Hc.hcXPB X`) to a
system `T` with the specification `HcSpec X U T`: bound `N_{j+1}(F)`, base gate `γ`, base reading `N_{j+1}(F(x))`,
bound field `evZ(N_{j+1}(F(x)))` above `γ` and `Z_o(x)` below, `T` extends `U`, reads the code `F` as `F(x)` with the
gate of `U`, and every code in `[F, N_{j+1}(F))` with gate below a base forces `γ` below it.  At level `1` the
self-read union `Hc.hcSU` is such a step (`hc_spec_SU`).

For a base `A : Hb.HcA (j+1)` (level `j+2`), a start `S0` (`HcLvStart A S0`) and a step `St` with the specification,
`hcLvU St A S0 λ` (`λ < N_{j+2}(F)`) is the start of the stage at the offset `λ`: `S0` at `0`, `St` applied to the
offset pseudo-base `Hc.hcXoff j A (hcLvU λ) λ` at `λ+1`, the union `Hc.HcLvFam.U` at a limit; `hcLv_inv`: the
invariant `Hc.HcLvInv A (ν+1)` at every `ν < N_{j+2}(F)`.

* `HcSpec`, `hc_spec_SU`, `HcLvStart`, `hcLvStep`, `hcLvExt`, `hcLvLimD`, `hcLvU` (**THE RECURSION, EVERY LEVEL**),
  `hcLv_inv` (**THE INVARIANT**), `hcLvU_B`, `hcLvU_self`, `hcLvU_Zb`, `hcLvU_start`, `hcLvU_γ_iff`, `hcLv_ext`,
  `hcLvU_succ_eq`.

No new axiom.  New definitions: `HcSpec`, `HcLvStart`, `hcLvStep`, `hcLvExt`, `hcLvLimD`, `hcLvU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hc

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
structure HcSpec {j : ℕ} (X : HcX j) (U T : HcVD) : Prop where
  B : T.B = hbN (j + 1) X.F
  γ : T.γ = X.γ
  b : ∀ x, InE x → x < Om1 → X.γ < x → T.b x = hbN (j + 1) (X.Fr x)
  Z : ∀ x, InE x → x < Om1 → T.Z x = if X.γ < x then evZ (hbN (j + 1) (X.Fr x)) else X.Zo x
  extR : ∀ c x, c < U.B → T.R c x = U.R c x
  extg : ∀ c, c < U.B → T.g c = U.g c
  high : ∀ c σ, X.F ≤ c → c < hbN (j + 1) X.F → InE σ → σ < Om1 → T.g c < σ → X.γ < σ
  RF : ∀ x, InE x → x < Om1 → X.γ < x → T.R X.F x = X.Fr x
  gF : ∀ x, InE x → x < Om1 → (T.g X.F < x ↔ X.γ < x)

theorem hc_B_of_start {D : HcVD} {Bp : HcPB} (h : HcSStart Bp D) : D.B = Bp.Q := by
  rw [D.B_ix, h.ix]; exact Bp.Q_fix

/-- **The self-read union of the stage at a pseudo-base of level `1` has the specification.** -/
theorem hc_spec_SU (X : HcX 0) (U : HcVD) (h : HcSStart (hcXPB X) U) : HcSpec X U (hcSU h) where
  B := by rw [hcSU_B, hbN1_eq]; rfl
  γ := rfl
  b := fun x _ _ _ => by rw [hcSU_b, hbN1_eq]; rfl
  Z := fun x _ _ => by
    rw [hcSU_Z, hbN1_eq]; unfold hcSUZ; rfl
  extR := fun c x hc => by
    rw [hcSU_R h (hcS_zero_lt2 (Bp := hcXPB X)) (by rw [hcSD_zero]; exact hc) x, hcSD_zero]
  extg := fun c hc => by
    rw [hcSU_g h (hcS_zero_lt2 (Bp := hcXPB X)) (by rw [hcSD_zero]; exact hc), hcSD_zero]
  high := fun c σ hFc hc hσ hσ1 hg => by
    rw [hbN1_eq] at hc
    exact hcSU_high_gate h hc hFc hσ hσ1 hg
  RF := fun x hx hx1 hγ => by
    have hQ1 : (1 : Ordinal.{0}) < evZ (hcXPB X).Q := one_lt_omega0.trans (omega0_lt_inE (evZ_E _))
    have hB : U.B = X.F := hc_B_of_start h
    have hc1 : X.F < (hcSD (hcXPB X) U 1).B := by rw [hcS_one_eq, HcVD.step_B, hB]; exact lt_eN _
    rw [hcSU_R h hQ1 hc1, hcS_one_eq, HcVD.step_R, ← hB, HcVD.hR_G, h.b x hx hx1 hγ]; rfl
  gF := fun x hx hx1 => by
    have hQ1 : (1 : Ordinal.{0}) < evZ (hcXPB X).Q := one_lt_omega0.trans (omega0_lt_inE (evZ_E _))
    have hB : U.B = X.F := hc_B_of_start h
    have hc1 : X.F < (hcSD (hcXPB X) U 1).B := by rw [hcS_one_eq, HcVD.step_B, hB]; exact lt_eN _
    rw [hcSU_g h hQ1 hc1, hcS_one_eq, ← hB, HcVD.step_g_B]
    exact h.γ x hx hx1

/-! ## The start and the recursion -/

theorem hcLv_zero_lt_N {j : ℕ} (A : HcA (j + 1)) : (0 : Ordinal.{0}) < hbN (j + 1 + 1) A.F := A.N_E.pos

/-- **The start conditions** of the recursion over `A` at `S0`. -/
structure HcLvStart {j : ℕ} (A : HcA (j + 1)) (S0 : HcVD) : Prop where
  B : S0.B = veblen ((j + 1 + 1 : ℕ) : Ordinal.{0}) (A.F + 1 + 0)
  Zb : ∀ x, InE x → x < Om1 → S0.Z x ≤ A.Zl x
  st : ∀ (h2 : 0 < S0.B) (hZ : ∀ x, InE x → x < Om1 → S0.Z x ≤ A.Zl x),
    HcSStart (hcLvPB A S0 0 h2 (hcLv_zero_lt_N A) hZ) S0
  high0 : ∀ c σ, A.F ≤ c → c < S0.B → InE σ → σ < Om1 → S0.g c < σ → A.γ < σ

section Rec

variable {j : ℕ} (St : ∀ (X : HcX j) (U : HcVD), HcSStart (hcXPB X) U → HcVD) (A : HcA (j + 1)) (S0 : HcVD)

/-- The successor step: the step `St` at the offset pseudo-base `λ` started at `U` (when `U` starts it). -/
noncomputable def hcLvStep (μ : Ordinal.{0}) (U : HcVD) : HcVD := by
  classical
  exact if h : ∃ (hμ : μ < hbN (j + 1 + 1) A.F) (h2 : μ < U.B) (hZ : ∀ x, InE x → x < Om1 → U.Z x ≤ A.Zl x),
      HcSStart (hcLvPB A U μ h2 hμ hZ) U then
    St (hcXoff j A U μ h.choose_spec.choose h.choose h.choose_spec.choose_spec.choose) U
      h.choose_spec.choose_spec.choose_spec else U

/-- The family of the earlier values, extended by the start at `0`. -/
noncomputable def hcLvExt (l : Ordinal.{0}) (IH : ∀ β, β < l → HcVD) (β : Ordinal.{0}) : HcVD :=
  if h : β < l then IH β h else S0

open Classical in
/-- The limit step: the union of all earlier starts when the invariant holds. -/
noncomputable def hcLvLimD (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ β, β < l → HcVD) : HcVD :=
  if H : l < hbN (j + 1 + 1) A.F ∧ HcLvInv A l (hcLvExt S0 l IH) then
    (HcLvFam.mk l (hcLvExt S0 l IH) hl H.1 H.2).U else S0

/-- **THE RECURSION OVER THE OFFSETS OF A BASE OF LEVEL `j+2`**, for the step `St`. -/
noncomputable def hcLvU (ν : Ordinal.{0}) : HcVD :=
  Ordinal.limitRecOn (motive := fun _ => HcVD) ν S0 (hcLvStep St A) (hcLvLimD A S0)

theorem hcLvU_zero : hcLvU St A S0 0 = S0 := by unfold hcLvU; rw [Ordinal.limitRecOn_zero]

theorem hcLvU_succ (ν : Ordinal.{0}) : hcLvU St A S0 (ν + 1) = hcLvStep St A ν (hcLvU St A S0 ν) := by
  unfold hcLvU; rw [Ordinal.limitRecOn_add_one]

theorem hcLvU_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) :
    hcLvU St A S0 l = hcLvLimD A S0 l hl (fun β _ => hcLvU St A S0 β) := by
  unfold hcLvU; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem hcLvExt_eq {l β : Ordinal.{0}} (h : β < l) :
    hcLvExt S0 l (fun β _ => hcLvU St A S0 β) β = hcLvU St A S0 β := by
  unfold hcLvExt; rw [dif_pos h]

/-- The successor value when `hcLvU ν` starts the stage at the offset `ν`. -/
theorem hcLvU_succ_eq {ν : Ordinal.{0}} (hν : ν < hbN (j + 1 + 1) A.F) (h2 : ν < (hcLvU St A S0 ν).B)
    (hZ : ∀ x, InE x → x < Om1 → (hcLvU St A S0 ν).Z x ≤ A.Zl x)
    (h : HcSStart (hcLvPB A (hcLvU St A S0 ν) ν h2 hν hZ) (hcLvU St A S0 ν)) :
    hcLvU St A S0 (ν + 1) = St (hcXoff j A (hcLvU St A S0 ν) ν h2 hν hZ) (hcLvU St A S0 ν) h := by
  rw [hcLvU_succ]; unfold hcLvStep
  rw [dif_pos ⟨hν, h2, hZ, h⟩]

theorem hcLvU_lim_eq {l : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l < hbN (j + 1 + 1) A.F)
    (H : HcLvInv A l (hcLvU St A S0)) :
    hcLvU St A S0 l = (HcLvFam.mk l (hcLvExt S0 l fun β _ => hcLvU St A S0 β) hl hle
      (H.congr fun β h => hcLvExt_eq St A S0 h)).U := by
  rw [hcLvU_limit St A S0 hl]; unfold hcLvLimD; rw [dif_pos ⟨hle, H.congr fun β h => hcLvExt_eq St A S0 h⟩]

end Rec

theorem hc_ix_of_B {T : HcVD} {Q : Ordinal.{0}} (hQ : veblen 1 Q = Q) (hB : T.B = Q) : T.ix = Q := by
  have h : veblen 1 T.ix = veblen 1 Q := by rw [← T.B_ix, hB, hQ]
  exact (veblen_inj).1 h

/-- **THE INVARIANT**: every `hcLvU St A S0 λ`, `λ < N_{j+2}(F)`, starts the stage at the offset `λ`, has bound field
below `Z_l`, the starts at successors have the high-gate property, and later starts extend earlier ones. -/
theorem hcLv_inv {j : ℕ} {St : ∀ (X : HcX j) (U : HcVD), HcSStart (hcXPB X) U → HcVD}
    (hSt : ∀ X U h, HcSpec X U (St X U h)) {A : HcA (j + 1)} {S0 : HcVD} (hS : HcLvStart A S0) :
    ∀ ν : Ordinal.{0}, ν < hbN (j + 1 + 1) A.F → HcLvInv A (ν + 1) (hcLvU St A S0) := by
  intro ν
  induction ν using Ordinal.limitRecOn with
  | zero =>
    intro _
    have h0 : ∀ μ : Ordinal.{0}, μ < 0 + 1 → μ = 0 := fun μ h => Order.lt_one_iff.1 (by rwa [zero_add] at h)
    refine ⟨fun μ h => ?_, fun μ h => ?_, fun μ hμ h h2 hZ => ?_, fun μ h => ?_, fun β γ hβγ h c x _ => ?_,
      fun β γ hβγ h c _ => ?_⟩
    · rw [h0 μ h, hcLvU_zero]; exact hS.B
    · rw [h0 μ h, hcLvU_zero]; exact hS.Zb
    · obtain rfl := h0 μ h
      exact hcLv_st_congr (hcLvU_zero St A S0) h2 hμ hZ (fun h2' hZ' => hS.st h2' hZ')
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
    have h2 : μ < (hcLvU St A S0 μ).B := H.self_lt (lt_add_one μ) hμT
    have hZ := H.Zb μ (lt_add_one μ)
    have hst := H.st μ hμT (lt_add_one μ) h2 hZ
    set X := hcXoff j A (hcLvU St A S0 μ) μ h2 hμT hZ with hX
    have e := hcLvU_succ_eq St A S0 hμT h2 hZ hst
    have hsp := hSt X (hcLvU St A S0 μ) hst
    have hBμ : (hcLvU St A S0 μ).B = X.F := H.B μ (lt_add_one μ)
    have hB1 : (hcLvU St A S0 (μ + 1)).B = veblen ((j + 1 + 1 : ℕ) : Ordinal.{0}) (A.F + 1 + (μ + 1)) := by
      rw [e, hsp.B]
      show hbN (j + 1) (veblen ((j + 1 + 1 : ℕ) : Ordinal.{0}) (A.F + 1 + μ)) = _
      rw [hbN_veb, add_assoc (A.F + 1) μ 1]
    have hZ1 : ∀ x, InE x → x < Om1 → (hcLvU St A S0 (μ + 1)).Z x ≤ A.Zl x := fun x hx hx1 => by
      rw [e, hsp.Z x hx hx1]
      split_ifs with hγ
      · exact (hb_evZ_lt_fix2 (A.Zl_fix (by omega) x) (X.N_Zo hx hx1 hγ)).le
      · exact le_rfl
    have h1B : μ + 1 < (hcLvU St A S0 μ).B := (ev_isSuccLimit_of_inE (hcLvU St A S0 μ).B_E).add_one_lt h2
    have hext : ∀ c x, c < (hcLvU St A S0 μ).B → (hcLvU St A S0 (μ + 1)).R c x = (hcLvU St A S0 μ).R c x :=
      fun c x hc => by rw [e]; exact hsp.extR c x hc
    have hextg : ∀ c, c < (hcLvU St A S0 μ).B → (hcLvU St A S0 (μ + 1)).g c = (hcLvU St A S0 μ).g c :=
      fun c hc => by rw [e]; exact hsp.extg c hc
    have hgiff : ∀ x, InE x → x < Om1 → ((hcLvU St A S0 μ).g μ < x ↔ (hcLvU St A S0 μ).g (μ + 1) < x) :=
      fun x hx _ => ⟨fun h => (hcLvU St A S0 μ).g_succ x (ev_isSuccLimit_of_inE hx) μ h1B h,
        fun h => ((hcLvU St A S0 μ).g_le_succ μ).trans_lt h⟩
    have hFr1 : ∀ x, InE x → x < Om1 → X.γ < x →
        glA ((j + 1 + 1 : ℕ) : Ordinal.{0}) (A.Fr x + (hcLvU St A S0 (μ + 1)).R (μ + 1) x) x =
          hbN (j + 1) (X.Fr x) := fun x hx hx1 hγ => by
      rw [hext (μ + 1) x h1B, (hcLvU St A S0 μ).R_succ, ← add_assoc]
      exact hb_glA_succ hx hx1 (j + 1) (hcXoff_t1_lt1 j A _ μ h2 hZ hx hx1 hγ)
    have hstS : ∀ (h2' : μ + 1 < (hcLvU St A S0 (μ + 1)).B) (hZ' : ∀ x, InE x → x < Om1 →
        (hcLvU St A S0 (μ + 1)).Z x ≤ A.Zl x),
        HcSStart (hcLvPB A (hcLvU St A S0 (μ + 1)) (μ + 1) h2' hν hZ') (hcLvU St A S0 (μ + 1)) := fun h2' hZ' => by
      have hγiff : ∀ x, InE x → x < Om1 →
          ((hcLvU St A S0 (μ + 1)).γ < x ↔ max A.γ ((hcLvU St A S0 (μ + 1)).g (μ + 1)) < x) := fun x hx hx1 => by
        rw [e, hsp.γ]
        show max A.γ ((hcLvU St A S0 μ).g μ) < x ↔ max A.γ ((St X _ hst).g (μ + 1)) < x
        rw [← e, hextg (μ + 1) h1B, max_lt_iff, max_lt_iff]
        exact and_congr_right fun _ => hgiff x hx hx1
      refine ⟨?_, hγiff, fun x hx hx1 hγ => ?_, fun x hx hx1 => ?_⟩
      · refine hc_ix_of_B ?_ hB1
        exact hb_fix_down (j := 1) (by omega) (hb_fix_veb (j + 1) _) |> fun h => by rwa [Nat.cast_one] at h
      · have hγ' : X.γ < x := by
          have := (hγiff x hx hx1).2 hγ; rw [e, hsp.γ] at this; exact this
        show (hcLvU St A S0 (μ + 1)).b x = glA ((j + 1 + 1 : ℕ) : Ordinal.{0}) (A.Fr x + (hcLvU St A S0 (μ + 1)).R
            (μ + 1) x) x
        rw [hFr1 x hx hx1 hγ', e]; exact hsp.b x hx hx1 hγ'
      · show (hcLvU St A S0 (μ + 1)).Z x = HcPB.Zst (hcLvPB A (hcLvU St A S0 (μ + 1)) (μ + 1) h2' hν hZ') x
        unfold HcPB.Zst
        have hZe := hsp.Z x hx hx1
        rw [← e] at hZe
        rw [hZe]
        show (if X.γ < x then evZ (hbN (j + 1) (X.Fr x)) else A.Zl x) =
          if max A.γ ((hcLvU St A S0 (μ + 1)).g (μ + 1)) < x then
            evZ (glA ((j + 1 + 1 : ℕ) : Ordinal.{0}) (A.Fr x + (hcLvU St A S0 (μ + 1)).R (μ + 1) x) x) else A.Zl x
        have hiff : X.γ < x ↔ max A.γ ((hcLvU St A S0 (μ + 1)).g (μ + 1)) < x := by
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
          have hcμ : c < (hcLvU St A S0 μ).B := hc.trans_le (by
            rw [H.B β (lt_of_le_of_lt hβμ (lt_add_one μ)), H.B μ (lt_add_one μ)]
            exact (isNormal_veblen _).monotone ((add_le_add_iff_left _).2 hβμ))
          rw [hext c x hcμ]; exact H.cohR β μ hβμ (lt_add_one μ) c x hc
        · rfl
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.cohg β γ hβγ h' c hc
      · rcases hβγ.lt_or_eq with h'' | rfl
        · have hβμ : β ≤ μ := Order.lt_add_one_iff.1 h''
          have hcμ : c < (hcLvU St A S0 μ).B := hc.trans_le (by
            rw [H.B β (lt_of_le_of_lt hβμ (lt_add_one μ)), H.B μ (lt_add_one μ)]
            exact (isNormal_veblen _).monotone ((add_le_add_iff_left _).2 hβμ))
          rw [hextg c hcμ]; exact H.cohg β μ hβμ (lt_add_one μ) c hc
        · rfl
  | limit l hl ih =>
    intro hν
    have hIH : ∀ β, β < l → HcLvInv A (β + 1) (hcLvU St A S0) := fun β h => ih β h (h.trans hν)
    have H : HcLvInv A l (hcLvU St A S0) := ⟨fun μ h => (hIH μ h).B μ (lt_add_one μ),
      fun μ h => (hIH μ h).Zb μ (lt_add_one μ),
      fun μ hμ h => (hIH μ h).st μ hμ (lt_add_one μ),
      fun μ h => (hIH (μ + 1) h).high μ (lt_add_one _),
      fun β γ hβγ h => (hIH γ h).cohR β γ hβγ (lt_add_one γ),
      fun β γ hβγ h => (hIH γ h).cohg β γ hβγ (lt_add_one γ)⟩
    have e := hcLvU_lim_eq St A S0 hl hν H
    set L := HcLvFam.mk l (hcLvExt S0 l fun β _ => hcLvU St A S0 β) hl hν (H.congr fun β h => hcLvExt_eq St A S0 h)
      with hL
    have hF : ∀ β, β < l → L.F β = hcLvU St A S0 β := fun β h => hcLvExt_eq St A S0 h
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
      · exact hcLv_st_congr e h2' hβ hZ' (fun _ _ => L.U_start)
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

variable {j : ℕ} {St : ∀ (X : HcX j) (U : HcVD), HcSStart (hcXPB X) U → HcVD}
  (hSt : ∀ X U h, HcSpec X U (St X U h)) {A : HcA (j + 1)} {S0 : HcVD} (hS : HcLvStart A S0)
include hSt hS

theorem hcLvU_B {l : Ordinal.{0}} (hl : l < hbN (j + 1 + 1) A.F) :
    (hcLvU St A S0 l).B = veblen ((j + 1 + 1 : ℕ) : Ordinal.{0}) (A.F + 1 + l) :=
  (hcLv_inv hSt hS l hl).B l (lt_add_one l)

theorem hcLvU_self {l : Ordinal.{0}} (hl : l < hbN (j + 1 + 1) A.F) : l < (hcLvU St A S0 l).B :=
  (hcLv_inv hSt hS l hl).self_lt (lt_add_one l) hl

theorem hcLvU_Zb {l : Ordinal.{0}} (hl : l < hbN (j + 1 + 1) A.F) :
    ∀ x, InE x → x < Om1 → (hcLvU St A S0 l).Z x ≤ A.Zl x :=
  (hcLv_inv hSt hS l hl).Zb l (lt_add_one l)

/-- **`hcLvU λ` STARTS THE STAGE AT THE OFFSET `λ`.** -/
theorem hcLvU_start {l : Ordinal.{0}} (hl : l < hbN (j + 1 + 1) A.F) :
    HcSStart (hcLvPB A (hcLvU St A S0 l) l (hcLvU_self hSt hS hl) hl (hcLvU_Zb hSt hS hl)) (hcLvU St A S0 l) :=
  (hcLv_inv hSt hS l hl).st l hl (lt_add_one l) (hcLvU_self hSt hS hl) (hcLvU_Zb hSt hS hl)

/-- **The base gate of `hcLvU λ` lies below a base `x` iff `max(γ, g(λ))` does.** -/
theorem hcLvU_γ_iff {l x : Ordinal.{0}} (hl : l < hbN (j + 1 + 1) A.F) (hx : InE x) (hx1 : x < Om1) :
    (hcLvU St A S0 l).γ < x ↔ max A.γ ((hcLvU St A S0 l).g l) < x := (hcLvU_start hSt hS hl).γ x hx hx1

/-- **Later starts extend earlier ones.** -/
theorem hcLv_ext {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (hγ : γ < hbN (j + 1 + 1) A.F) :
    (∀ c x, c < (hcLvU St A S0 β).B → (hcLvU St A S0 γ).R c x = (hcLvU St A S0 β).R c x) ∧
    (∀ c, c < (hcLvU St A S0 β).B → (hcLvU St A S0 γ).g c = (hcLvU St A S0 β).g c) :=
  ⟨(hcLv_inv hSt hS γ hγ).cohR β γ hβγ (lt_add_one γ), (hcLv_inv hSt hS γ hγ).cohg β γ hβγ (lt_add_one γ)⟩

/-- **The specification of the successor**: `hcLvU (λ+1)` is the step at the offset `λ`. -/
theorem hcLvU_succ_spec {l : Ordinal.{0}} (hl : l < hbN (j + 1 + 1) A.F) :
    HcSpec (hcXoff j A (hcLvU St A S0 l) l (hcLvU_self hSt hS hl) hl (hcLvU_Zb hSt hS hl)) (hcLvU St A S0 l)
      (hcLvU St A S0 (l + 1)) := by
  rw [hcLvU_succ_eq St A S0 hl (hcLvU_self hSt hS hl) (hcLvU_Zb hSt hS hl) (hcLvU_start hSt hS hl)]
  exact hSt _ _ _

end Main

end Googology.Trans.PoR.InaccPsi.R2.Hc
