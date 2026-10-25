import Googology.Trans.PoR.InaccPsi.R2.HcVRS

/-!
# HcPB: A GATED STAGE WITH AN ABSTRACT INDEX BASE `Q` AND READING `P`, BOUND FIELD BELOW `B_ω`

(Textual copy of `Hb.HbPB` for `Hc.HcVD`: bound fields `≤ B_x(x)` (`Hc.hcBR`) in place of `≤ B_ω(x)`;
the proofs are unchanged.)

`Ha.HaPB` fixes the index base `Q = φ(2, j_Q)` (not a fixed point of `φ(2,·)`), its reading
`P(x) = ϑˣ(Ω₁·2 + t_P(x))` and the low bound field `B₃(x)`.  `HcPB` asks only what the stage machinery uses: a
`ζ`-number `Q` (an `ε`-fixed point; it may be a fixed point of `φ(2,·)`), a reading `P(x)` above the stage gate `γ_P`
(an `ε`-fixed point above `x`, Lemma EXACT for `P(ρ)` and `evZ(P(ρ))`), the code-gate conditions of `[Q, evZ(Q))`, and
a low bound field `Z_l(x)` (a fixed point of `φ(2,·)`, `≤ B_ω(x)`, above `P(x)` when `γ_P < x`).  The bound field of
the stage is `Zst(x) = evZ(P(x))` above the gate and `Z_l(x)` below it.

* `HcPB`, `HcPB.Zst` and the facts of `Ha.HaPB` (`Q_E`, `strip`, `cl_gate`, `Q_gate`, `Zst_BR`, `Zst_fix`, `P_lt`,
  `evP_lt`, …).

No new axiom.  New definitions: `HcPB`, `HcPB.Zst`.
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

/-- **A gated stage with an abstract index base**: a `ζ`-number `Q`, its reading `P(x)` above the stage gate `γ_P`,
the code-gate conditions of `[Q, evZ(Q))`, a low bound field `Z_l`. -/
structure HcPB where
  Q : Ordinal.{0}
  P : Ordinal.{0} → Ordinal.{0}
  Zl : Ordinal.{0} → Ordinal.{0}
  γP : Ordinal.{0}
  γP_lt : γP < Om1
  Q_fix : veblen 1 Q = Q
  G_lt_Q : gcG 0 < Q
  evQ_lt1 : evZ Q < gcG 1
  Q_mem : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → γP < b → Q ∈ S.CSet a b
  evQ_mem : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → γP < b → evZ Q ∈ S.CSet a b
  Q_code : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y, GxCl Z {gcG 0} y → Q ≤ y → y < evZ Q → GxCl Z {gcG 0} Q
  Q_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y, GxCl Z {gcG 0} y → Q ≤ y → y < evZ Q → γP < Z
  evQ_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z {gcG 0} (evZ Q) → γP < Z
  P_fix : ∀ {x}, InE x → x < Om1 → γP < x → veblen 1 (P x) = P x
  P_gt : ∀ {x}, InE x → x < Om1 → γP < x → x < P x
  P_Zl : ∀ x, InE x → x < Om1 → γP < x → P x < Zl x
  Zl_fix : ∀ x, veblen 2 (Zl x) = Zl x
  Zl_BR : ∀ x, InE x → x < Om1 → Zl x ≤ hcBR x
  P_pi : ∀ {σ ρ}, Bases σ ρ → γP < σ → P ρ ∈ TB ρ σ ∧ pi σ ρ (P ρ) = P σ
  evP_pi : ∀ {σ ρ}, Bases σ ρ → γP < σ → evZ (P ρ) ∈ TB ρ σ ∧ pi σ ρ (evZ (P ρ)) = evZ (P σ)

namespace HcPB

variable (Bp : HcPB)

open Classical in
/-- **The bound field of the stage**: `evZ(P(x))` above the gate, `Z_l(x)` at or below it. -/
noncomputable def Zst (x : Ordinal.{0}) : Ordinal.{0} := if Bp.γP < x then evZ (Bp.P x) else Bp.Zl x

theorem Q_E : InE Bp.Q := gz_inE_of_fix Bp.Q_fix

theorem G_le_Q : gcG 0 ≤ Bp.Q := Bp.G_lt_Q.le

theorem Om_lt_Q : Om 1 < Bp.Q := (gcG_Om1_lt 0).trans Bp.G_lt_Q

theorem Q_lt_G1 : Bp.Q < gcG 1 := (lt_evZ _).trans Bp.evQ_lt1

/-- **`φ(1, Q + c)` a code over `Z` (`0 < c < evZ(Q)`) ⇒ the stage gate lies below `Z` and `c` is a code over
`Z`.** -/
theorem strip {Z c : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (hc0 : 0 < c) (hcZ : c < evZ Bp.Q)
    (h : GxCl Z {gcG 0} (veblen 1 (Bp.Q + c))) : Bp.γP < Z ∧ GxCl Z {gcG 0} c := by
  have hOt : Om 1 < Bp.Q + c := Bp.Om_lt_Q.trans_le le_self_add
  have h1 := gr_cl_veb1 hZ1 hOt (gzq_lt_veb Bp.Q_fix hc0 hcZ) h
  have hy : Bp.Q + c < evZ Bp.Q := add_lt_evZ (lt_evZ _) hcZ
  refine ⟨Bp.Q_cl Z hZ hZ1 _ h1 le_self_add hy, ?_⟩
  exact gwY_cl_of_add hZ hZ1 Bp.Q_E Bp.G_le_Q (Bp.Q_code Z hZ hZ1 _ h1 le_self_add hy) h1

/-- **THE CODE-GATE CONDITION OF A UNION INDEX `Q + c`**: `φ(1, Q + c)` a code over `Z` ⇒ `max(γ_P, g_E(c)) < Z`. -/
theorem cl_gate (E : HcVD) {c Z : Ordinal.{0}} (hcB : c < E.B) (hc0 : 0 < c) (hcZ : c < evZ Bp.Q) (hZ : SC Z)
    (hZ1 : Z ≤ Om 1) (h : GxCl Z {gcG 0} (veblen 1 (Bp.Q + c))) : max Bp.γP (E.g c) < Z := by
  obtain ⟨h1, h2⟩ := Bp.strip hZ hZ1 hc0 hcZ h
  have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1
  refine max_lt h1 ?_
  exact E.code_gate Z hZ1' hZ.1 (fun _ _ hu hv => hZ.isPrincipal hu hv) (fun _ _ hu hv => hZ.2 _ hu _ hv)
    {gcG 0} (fun s hs => Or.inl (Set.mem_singleton_iff.1 hs)) c h2 hcB

/-- **`Q` a code over `Z` ⇒ `γ_P < Z`.** -/
theorem Q_gate {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (h : GxCl Z {gcG 0} Bp.Q) : Bp.γP < Z :=
  Bp.Q_cl Z hZ hZ1 Bp.Q h le_rfl (lt_evZ _)

/-- **`evZ(Q)` a code over `Z` ⇒ `γ_P < Z`.** -/
theorem evQ_gate {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (h : GxCl Z {gcG 0} (evZ Bp.Q)) : Bp.γP < Z :=
  Bp.evQ_cl Z hZ hZ1 h

theorem Zl_fix1 (x : Ordinal.{0}) : veblen 1 (Bp.Zl x) = Bp.Zl x := by
  have h := veblen_veblen_of_lt (one_lt_two (α := Ordinal.{0})) (Bp.Zl x)
  rw [Bp.Zl_fix] at h; exact h

theorem Zst_fix (x : Ordinal.{0}) : veblen 1 (Bp.Zst x) = Bp.Zst x := by
  unfold HcPB.Zst
  split_ifs
  · exact epsilon_evZ _
  · exact Bp.Zl_fix1 x

theorem Zst_eq {x : Ordinal.{0}} (h : Bp.γP < x) : Bp.Zst x = evZ (Bp.P x) := by
  unfold HcPB.Zst; rw [if_pos h]

theorem Zst_low {x : Ordinal.{0}} (h : ¬ Bp.γP < x) : Bp.Zst x = Bp.Zl x := by
  unfold HcPB.Zst; rw [if_neg h]

theorem Zst_le_Zl (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : Bp.Zst x ≤ Bp.Zl x := by
  unfold HcPB.Zst
  split_ifs with h
  · exact (hb_evZ_lt_fix2 (Bp.Zl_fix x) (Bp.P_Zl x hx hx1 h)).le
  · exact le_rfl

theorem Zst_BR (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : Bp.Zst x ≤ hcBR x :=
  (Bp.Zst_le_Zl x hx hx1).trans (Bp.Zl_BR x hx hx1)

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : Bp.γP < x)
include hx hx1 hγ

theorem P_lt_BR : Bp.P x < hcBR x := (Bp.P_Zl x hx hx1 hγ).trans_le (Bp.Zl_BR x hx hx1)

theorem P_lt : Bp.P x < gq 1 x := (Bp.P_lt_BR hx hx1 hγ).trans (hcBR_lt1 hx hx1)

theorem evP_Zl : evZ (Bp.P x) < Bp.Zl x := hb_evZ_lt_fix2 (Bp.Zl_fix x) (Bp.P_Zl x hx hx1 hγ)

theorem evP_BR : evZ (Bp.P x) < hcBR x := (Bp.evP_Zl hx hx1 hγ).trans_le (Bp.Zl_BR x hx hx1)

theorem evP_lt : evZ (Bp.P x) < gq 1 x := (Bp.evP_BR hx hx1 hγ).trans (hcBR_lt1 hx hx1)

theorem evP_gt : x < evZ (Bp.P x) := (Bp.P_gt hx hx1 hγ).trans (lt_evZ _)

theorem P_E : InE (Bp.P x) := gz_inE_of_fix (Bp.P_fix hx hx1 hγ)

end Base

end HcPB

end Googology.Trans.PoR.InaccPsi.R2.Hc
