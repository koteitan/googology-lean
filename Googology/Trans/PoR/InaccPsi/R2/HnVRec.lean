import Googology.Trans.PoR.InaccPsi.R2.HnVLv

/-!
# HnVRec (port of HlVRec): THE GATED RECURSION OVER THE OFFSETS OF A BASE OF THE GATED LEVEL `L + ν`

PORT of `Hl.HlVRec` (the same proofs) to the band level datum `Hn.HnLv`.  What differs from `Hl.HlLv`: a level is
`L = Ω₁·u + Ω₁·q` (`q < Ω₁`, any `u`) in place of `L = Ω₁·q`; the code gate `g < Z` is asked for codes in
`[L, Ω₁·u + Ω₁²)` in place of `[L, Ω₁²)`; there is no field `ℓ(x) + x < x·x` (it is a hypothesis of the base `G`
only).  Declarations that do not mention a level datum are imported from `Hl`, not copied.

PORT of `Hj.HjVRec`.

What differs from the source: the level datum is a GATED one (`Hl.HlLv`: Lemma EXACT for the reading `ℓ` only at
base pairs `(σ, ρ)` above the level gate `g`, the hull membership of `L` only at `0 < a`, `g < b`, the code gate
`g < Z` only when a code over `Z` exists at the level); every pseudo-base and base carries `g ≤` its reading gate
(fields `lg`), and the code-gate fields take the extra hypothesis `g < Z`.  Proofs are otherwise those of the source;
names: prefix `hl`/`Hl` in place of `hj`/`Hj`.

No new axiom.  New definitions: `HnVStart`, `hnVStep`, `hnVLimD`, `hnVU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hn

open Googology.Trans.PoR.InaccPsi.R2.Hl

open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk

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

variable {Λ : HnLv}

theorem hnV_zero_lt_N {κ : Ordinal.{0}} (A : HnVB Λ κ) : (0 : Ordinal.{0}) < hcN (Λ.L + κ) A.F := A.N_E.pos

/-- **The start conditions** of the recursion over `A` at `S0`. -/
structure HnVStart {κ : Ordinal.{0}} (A : HnVB Λ κ) (S0 : HgVD) : Prop where
  B : S0.B = veblen (Λ.L + κ) (A.F + 1 + 0)
  Zb : ∀ x, InE x → x < Om1 → S0.Z x ≤ A.Zl x
  st : ∀ (h2 : 0 < S0.B) (hZ : ∀ x, InE x → x < Om1 → S0.Z x ≤ A.Zl x),
    HgSStart (hnVMPB A S0 0 h2 (hnV_zero_lt_N A) hZ) S0
  high0 : ∀ c σ, A.F ≤ c → c < S0.B → InE σ → σ < Om1 → S0.g c < σ → A.γ < σ

section Rec

variable {κ : Ordinal.{0}} (St : ∀ (Q : HnVQ Λ κ) (U : HgVD), HgSStart (hnVPB Q) U → HgVD) (A : HnVB Λ κ) (S0 : HgVD)

/-- The successor step: the step `St` at the offset pseudo-base `λ` started at `U` (when `U` starts it). -/
noncomputable def hnVStep (μ : Ordinal.{0}) (U : HgVD) : HgVD := by
  classical
  exact if h : ∃ (hμ : μ < hcN (Λ.L + κ) A.F) (h2 : μ < U.B) (hZ : ∀ x, InE x → x < Om1 → U.Z x ≤ A.Zl x),
      HgSStart (hnVMPB A U μ h2 hμ hZ) U then
    St (hnVOff A U μ h.choose_spec.choose h.choose h.choose_spec.choose_spec.choose) U
      h.choose_spec.choose_spec.choose_spec else U

open Classical in
/-- The limit step: the union of all earlier starts when the invariant holds. -/
noncomputable def hnVLimD (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ β, β < l → HgVD) : HgVD :=
  if H : l < hcN (Λ.L + κ) A.F ∧ HnVInv A l (hjVExt S0 l IH) then
    (HnVFam.mk l (hjVExt S0 l IH) hl H.1 H.2).U else S0

/-- **THE GATED OFFSET RECURSION, EVERY COUNTABLE LEVEL `(Λ.L + κ)`.** -/
noncomputable def hnVU (ν : Ordinal.{0}) : HgVD :=
  Ordinal.limitRecOn (motive := fun _ => HgVD) ν S0 (hnVStep St A) (hnVLimD A S0)

theorem hnVU_zero : hnVU St A S0 0 = S0 := by unfold hnVU; rw [Ordinal.limitRecOn_zero]

theorem hnVU_succ (ν : Ordinal.{0}) : hnVU St A S0 (ν + 1) = hnVStep St A ν (hnVU St A S0 ν) := by
  unfold hnVU; rw [Ordinal.limitRecOn_add_one]

theorem hnVU_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) :
    hnVU St A S0 l = hnVLimD A S0 l hl (fun β _ => hnVU St A S0 β) := by
  unfold hnVU; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem hnVExt_eq {l β : Ordinal.{0}} (h : β < l) :
    hjVExt S0 l (fun β _ => hnVU St A S0 β) β = hnVU St A S0 β := by
  unfold hjVExt; rw [dif_pos h]

/-- The successor value when `hnVU ν` starts the stage at the offset `ν`. -/
theorem hnVU_succ_eq {ν : Ordinal.{0}} (hν : ν < hcN (Λ.L + κ) A.F) (h2 : ν < (hnVU St A S0 ν).B)
    (hZ : ∀ x, InE x → x < Om1 → (hnVU St A S0 ν).Z x ≤ A.Zl x)
    (h : HgSStart (hnVMPB A (hnVU St A S0 ν) ν h2 hν hZ) (hnVU St A S0 ν)) :
    hnVU St A S0 (ν + 1) = St (hnVOff A (hnVU St A S0 ν) ν h2 hν hZ) (hnVU St A S0 ν) h := by
  rw [hnVU_succ]; unfold hnVStep
  rw [dif_pos ⟨hν, h2, hZ, h⟩]

theorem hnVU_lim_eq {l : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l < hcN (Λ.L + κ) A.F)
    (H : HnVInv A l (hnVU St A S0)) :
    hnVU St A S0 l = (HnVFam.mk l (hjVExt S0 l fun β _ => hnVU St A S0 β) hl hle
      (H.congr fun β h => hnVExt_eq St A S0 h)).U := by
  rw [hnVU_limit St A S0 hl]; unfold hnVLimD; rw [dif_pos ⟨hle, H.congr fun β h => hnVExt_eq St A S0 h⟩]

end Rec

/-- **THE INVARIANT**: every `hnVU St A S0 λ`, `λ < N_α(F)`, starts the stage at the offset `λ`, has bound field
below `Z_l`, the starts at successors have the high-gate property, and later starts extend earlier ones. -/
theorem hnV_inv {κ : Ordinal.{0}} {St : ∀ (Q : HnVQ Λ κ) (U : HgVD), HgSStart (hnVPB Q) U → HgVD}
    (hSt : ∀ Q U h, HnVSpec Q U (St Q U h)) {A : HnVB Λ κ} {S0 : HgVD} (hS : HnVStart A S0) :
    ∀ ν : Ordinal.{0}, ν < hcN (Λ.L + κ) A.F → HnVInv A (ν + 1) (hnVU St A S0) := by
  intro ν
  induction ν using Ordinal.limitRecOn with
  | zero =>
    intro _
    have h0 : ∀ μ : Ordinal.{0}, μ < 0 + 1 → μ = 0 := fun μ h => Order.lt_one_iff.1 (by rwa [zero_add] at h)
    refine ⟨fun μ h => ?_, fun μ h => ?_, fun μ hμ h h2 hZ => ?_, fun μ h => ?_, fun β γ hβγ h c x _ => ?_,
      fun β γ hβγ h c _ => ?_⟩
    · rw [h0 μ h, hnVU_zero]; exact hS.B
    · rw [h0 μ h, hnVU_zero]; exact hS.Zb
    · obtain rfl := h0 μ h
      exact hnV_st_congr (hnVU_zero St A S0) h2 hμ hZ (fun h2' hZ' => hS.st h2' hZ')
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
    have h2 : μ < (hnVU St A S0 μ).B := H.self_lt (lt_add_one μ) hμT
    have hZ := H.Zb μ (lt_add_one μ)
    have hst := H.st μ hμT (lt_add_one μ) h2 hZ
    set X := hnVOff A (hnVU St A S0 μ) μ h2 hμT hZ with hX
    have e := hnVU_succ_eq St A S0 hμT h2 hZ hst
    have hsp := hSt X (hnVU St A S0 μ) hst
    have hBμ : (hnVU St A S0 μ).B = X.F := H.B μ (lt_add_one μ)
    have hB1 : (hnVU St A S0 (μ + 1)).B = veblen (Λ.L + κ) (A.F + 1 + (μ + 1)) := by
      rw [e, hsp.B]
      show hdNx (Λ.L + κ) (veblen (Λ.L + κ) (A.F + 1 + μ)) = _
      rw [hdNx_veb, add_assoc (A.F + 1) μ 1]
    have hZ1 : ∀ x, InE x → x < Om1 → (hnVU St A S0 (μ + 1)).Z x ≤ A.Zl x := fun x hx hx1 => by
      rw [e, hsp.Z x hx hx1]
      split_ifs with hγ
      · exact (hb_evZ_lt_fix2 (A.Zl_fix x) (X.S_Zo hx hx1 hγ)).le
      · exact le_rfl
    have h1B : μ + 1 < (hnVU St A S0 μ).B := (ev_isSuccLimit_of_inE (hnVU St A S0 μ).B_E).add_one_lt h2
    have hext : ∀ c x, c < (hnVU St A S0 μ).B → (hnVU St A S0 (μ + 1)).R c x = (hnVU St A S0 μ).R c x :=
      fun c x hc => by rw [e]; exact hsp.extR c x hc
    have hextg : ∀ c, c < (hnVU St A S0 μ).B → (hnVU St A S0 (μ + 1)).g c = (hnVU St A S0 μ).g c :=
      fun c hc => by rw [e]; exact hsp.extg c hc
    have hgiff : ∀ x, InE x → x < Om1 → ((hnVU St A S0 μ).g μ < x ↔ (hnVU St A S0 μ).g (μ + 1) < x) :=
      fun x hx _ => ⟨fun h => (hnVU St A S0 μ).g_succ x (ev_isSuccLimit_of_inE hx) μ h1B h,
        fun h => ((hnVU St A S0 μ).g_le_succ μ).trans_lt h⟩
    have hFr1 : ∀ x, InE x → x < Om1 → X.γ < x →
        glA (Λ.l x + κ) (A.Fr x + (hnVU St A S0 (μ + 1)).R (μ + 1) x) x =
          hdNx (Λ.l x + κ) (X.Fr x) := fun x hx hx1 hγ => by
      rw [hext (μ + 1) x h1B, (hnVU St A S0 μ).R_succ, ← add_assoc]
      exact hnv_glA_succ Λ hx hx1 (A.ν_lt hx hx1 (max_lt_iff.1 hγ).1)
        (A.t1_lt1 hx hx1 (max_lt_iff.1 hγ).1 (hnVOff_R_lt A _ μ h2 hZ hx hx1 hγ))
    have hstS : ∀ (h2' : μ + 1 < (hnVU St A S0 (μ + 1)).B) (hZ' : ∀ x, InE x → x < Om1 →
        (hnVU St A S0 (μ + 1)).Z x ≤ A.Zl x),
        HgSStart (hnVMPB A (hnVU St A S0 (μ + 1)) (μ + 1) h2' hν hZ') (hnVU St A S0 (μ + 1)) := fun h2' hZ' => by
      have hγiff : ∀ x, InE x → x < Om1 →
          ((hnVU St A S0 (μ + 1)).γ < x ↔ max A.γN ((hnVU St A S0 (μ + 1)).g (μ + 1)) < x) := fun x hx hx1 => by
        rw [e, hsp.γ]
        show max A.γN ((hnVU St A S0 μ).g μ) < x ↔ max A.γN ((St X _ hst).g (μ + 1)) < x
        rw [← e, hextg (μ + 1) h1B, max_lt_iff, max_lt_iff]
        exact and_congr_right fun _ => hgiff x hx hx1
      refine ⟨?_, hγiff, fun x hx hx1 hγ => ?_, fun x hx hx1 => ?_⟩
      · refine hg_ix_of_B ?_ hB1
        exact veblen_veblen_of_lt ((hg_one_lt_Om1.trans_le Λ.OL).trans_le le_self_add) _
      · have hγ' : X.γ < x := by
          have := (hγiff x hx hx1).2 hγ; rw [e, hsp.γ] at this; exact this
        show (hnVU St A S0 (μ + 1)).b x = glA (Λ.l x + κ) (A.Fr x + (hnVU St A S0 (μ + 1)).R
            (μ + 1) x) x
        rw [hFr1 x hx hx1 hγ', e]; exact hsp.b x hx hx1 hγ'
      · show (hnVU St A S0 (μ + 1)).Z x = HgPB.Zst (hnVMPB A (hnVU St A S0 (μ + 1)) (μ + 1) h2' hν hZ') x
        unfold HgPB.Zst
        have hZe := hsp.Z x hx hx1
        rw [← e] at hZe
        rw [hZe]
        show (if X.γ < x then evZ (hdNx (Λ.l x + κ) (X.Fr x)) else A.Zl x) =
          if max A.γN ((hnVU St A S0 (μ + 1)).g (μ + 1)) < x then
            evZ (glA (Λ.l x + κ) (A.Fr x + (hnVU St A S0 (μ + 1)).R (μ + 1) x) x) else A.Zl x
        have hiff : X.γ < x ↔ max A.γN ((hnVU St A S0 (μ + 1)).g (μ + 1)) < x := by
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
          have hcμ : c < (hnVU St A S0 μ).B := hc.trans_le (by
            rw [H.B β (lt_of_le_of_lt hβμ (lt_add_one μ)), H.B μ (lt_add_one μ)]
            exact (isNormal_veblen _).monotone ((add_le_add_iff_left _).2 hβμ))
          rw [hext c x hcμ]; exact H.cohR β μ hβμ (lt_add_one μ) c x hc
        · rfl
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.cohg β γ hβγ h' c hc
      · rcases hβγ.lt_or_eq with h'' | rfl
        · have hβμ : β ≤ μ := Order.lt_add_one_iff.1 h''
          have hcμ : c < (hnVU St A S0 μ).B := hc.trans_le (by
            rw [H.B β (lt_of_le_of_lt hβμ (lt_add_one μ)), H.B μ (lt_add_one μ)]
            exact (isNormal_veblen _).monotone ((add_le_add_iff_left _).2 hβμ))
          rw [hextg c hcμ]; exact H.cohg β μ hβμ (lt_add_one μ) c hc
        · rfl
  | limit l hl ih =>
    intro hν
    have hIH : ∀ β, β < l → HnVInv A (β + 1) (hnVU St A S0) := fun β h => ih β h (h.trans hν)
    have H : HnVInv A l (hnVU St A S0) := ⟨fun μ h => (hIH μ h).B μ (lt_add_one μ),
      fun μ h => (hIH μ h).Zb μ (lt_add_one μ),
      fun μ hμ h => (hIH μ h).st μ hμ (lt_add_one μ),
      fun μ h => (hIH (μ + 1) h).high μ (lt_add_one _),
      fun β γ hβγ h => (hIH γ h).cohR β γ hβγ (lt_add_one γ),
      fun β γ hβγ h => (hIH γ h).cohg β γ hβγ (lt_add_one γ)⟩
    have e := hnVU_lim_eq St A S0 hl hν H
    set L := HnVFam.mk l (hjVExt S0 l fun β _ => hnVU St A S0 β) hl hν (H.congr fun β h => hnVExt_eq St A S0 h)
      with hL
    have hF : ∀ β, β < l → L.F β = hnVU St A S0 β := fun β h => hnVExt_eq St A S0 h
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
      · exact hnV_st_congr e h2' hβ hZ' (fun _ _ => L.U_start)
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
  {A : HnVB Λ κ} {S0 : HgVD} (hS : HnVStart A S0)
include hSt hS

theorem hnVU_B {l : Ordinal.{0}} (hl : l < hcN (Λ.L + κ) A.F) :
    (hnVU St A S0 l).B = veblen (Λ.L + κ) (A.F + 1 + l) :=
  (hnV_inv hSt hS l hl).B l (lt_add_one l)

theorem hnVU_self {l : Ordinal.{0}} (hl : l < hcN (Λ.L + κ) A.F) : l < (hnVU St A S0 l).B :=
  (hnV_inv hSt hS l hl).self_lt (lt_add_one l) hl

theorem hnVU_Zb {l : Ordinal.{0}} (hl : l < hcN (Λ.L + κ) A.F) :
    ∀ x, InE x → x < Om1 → (hnVU St A S0 l).Z x ≤ A.Zl x :=
  (hnV_inv hSt hS l hl).Zb l (lt_add_one l)

/-- **`hnVU λ` STARTS THE STAGE AT THE OFFSET `λ`.** -/
theorem hnVU_start {l : Ordinal.{0}} (hl : l < hcN (Λ.L + κ) A.F) :
    HgSStart (hnVMPB A (hnVU St A S0 l) l (hnVU_self hSt hS hl) hl (hnVU_Zb hSt hS hl)) (hnVU St A S0 l) :=
  (hnV_inv hSt hS l hl).st l hl (lt_add_one l) (hnVU_self hSt hS hl) (hnVU_Zb hSt hS hl)

/-- **The base gate of `hnVU λ` lies below a base `x` iff `max(γN, g(λ))` does.** -/
theorem hnVU_γ_iff {l x : Ordinal.{0}} (hl : l < hcN (Λ.L + κ) A.F) (hx : InE x) (hx1 : x < Om1) :
    (hnVU St A S0 l).γ < x ↔ max A.γN ((hnVU St A S0 l).g l) < x := (hnVU_start hSt hS hl).γ x hx hx1

/-- **Later starts extend earlier ones.** -/
theorem hnV_ext {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (hγ : γ < hcN (Λ.L + κ) A.F) :
    (∀ c x, c < (hnVU St A S0 β).B → (hnVU St A S0 γ).R c x = (hnVU St A S0 β).R c x) ∧
    (∀ c, c < (hnVU St A S0 β).B → (hnVU St A S0 γ).g c = (hnVU St A S0 β).g c) :=
  ⟨(hnV_inv hSt hS γ hγ).cohR β γ hβγ (lt_add_one γ), (hnV_inv hSt hS γ hγ).cohg β γ hβγ (lt_add_one γ)⟩

/-- **The specification of the successor**: `hnVU (λ+1)` is the step at the offset `λ`. -/
theorem hnVU_succ_spec {l : Ordinal.{0}} (hl : l < hcN (Λ.L + κ) A.F) :
    HnVSpec (hnVOff A (hnVU St A S0 l) l (hnVU_self hSt hS hl) hl (hnVU_Zb hSt hS hl)) (hnVU St A S0 l)
      (hnVU St A S0 (l + 1)) := by
  rw [hnVU_succ_eq St A S0 hl (hnVU_self hSt hS hl) (hnVU_Zb hSt hS hl) (hnVU_start hSt hS hl)]
  exact hSt _ _ _

end Main

end Googology.Trans.PoR.InaccPsi.R2.Hn
