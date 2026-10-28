import Googology.Trans.PoR.InaccPsi.R2.HgQR

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hg

open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Gq
open Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gm
open Googology.Trans.PoR.InaccPsi.R2.Gb
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
open Googology.Trans.PoR.InaccPsi.R2

/-- An abstract base with a gate on hull membership and exact base change. -/
structure HhQB where
  Q : Ordinal.{0}
  P : Ordinal.{0} → Ordinal.{0}
  γ : Ordinal.{0}
  Zo : Ordinal.{0} → Ordinal.{0}
  γ_lt : γ < Om1
  Q_fix : ∀ α, α < Om1 → veblen α Q = Q
  G_lt : gcG 0 < Q
  Q_lt1 : Q < gcG 1
  N_lt1 : ∀ (α : Ordinal.{0}), α < Om1 → hcN α Q < gcG 1
  Q_mem : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → γ < b → Q ∈ S.CSet a b
  N_mem : ∀ (α : Ordinal.{0}), α < Om1 → ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}},
    0 < a → max γ α < b → hcN α Q ∈ S.CSet a b
  Q_code : ∀ (α : Ordinal.{0}), α < Om1 → ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y,
    GxCl Z {gcG 0} y → Q ≤ y → y < hcN α Q → GxCl Z {gcG 0} Q
  Q_cl : ∀ (α : Ordinal.{0}), α < Om1 → ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y,
    GxCl Z {gcG 0} y → Q ≤ y → y < hcN α Q → γ < Z
  N_cl : ∀ (α : Ordinal.{0}), α < Om1 → ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 →
    GxCl Z {gcG 0} (hcN α Q) → max γ α < Z
  P_gt : ∀ (α : Ordinal.{0}) {x}, α < Om1 → InE x → x < Om1 → max γ α < x → x < P x
  P_fix : ∀ (α : Ordinal.{0}) {x}, α < Om1 → InE x → x < Om1 → max γ α < x → veblen α (P x) = P x
  N_Zo : ∀ (α : Ordinal.{0}) {x}, α < Om1 → InE x → x < Om1 → max γ α < x → hcN α (P x) < Zo x
  Zo_fix : ∀ x, veblen 2 (Zo x) = Zo x
  Zo_G1 : ∀ x, InE x → x < Om1 → Zo x < gq 1 x
  P_pi : ∀ (α : Ordinal.{0}) {σ ρ}, α < Om1 → Bases σ ρ → max γ α < σ →
    P ρ ∈ TB ρ σ ∧ pi σ ρ (P ρ) = P σ
  N_pi : ∀ (α : Ordinal.{0}) {σ ρ}, α < Om1 → Bases σ ρ → max γ α < σ →
    hcN α (P ρ) ∈ TB ρ σ ∧ pi σ ρ (hcN α (P ρ)) = hcN α (P σ)

namespace HhQB

variable (B : HhQB)

/-- The base lies above `ε₀`, since it is a fixed point of `φ(1, ·)`. -/
theorem eps0_le_Q : (ε₀ : Ordinal.{0}) ≤ B.Q := by
  have hfix := B.Q_fix 1 (one_lt_omega0.trans (omega0_lt_inE Rj.rj_Om1_inE))
  simpa [hfix] using Googology.Trans.PoR.InaccPsi.R2.Go.go_eps0_le_veb B.Q

theorem P_lt (α x : Ordinal.{0}) (hα : α < Om1) (hx : InE x) (hx1 : x < Om1)
    (hγ : max B.γ α < x) : B.P x < gq 1 x :=
  (hcN_gt α (B.P x)).trans ((B.N_Zo α hα hx hx1 hγ).trans (B.Zo_G1 x hx hx1))

theorem P_T (α x : Ordinal.{0}) (hα : α < Om1) (hx : InE x) (hx1 : x < Om1)
    (hγ : max B.γ α < x) : B.P x ∈ Tset x ∧ B.P x < Om1 :=
  gm1_T hx hx1 (B.P_lt α x hα hx hx1 hγ)

/-- View the gated abstract base as a two-gate base of any countable level. -/
noncomputable def toB (α : Ordinal.{0}) (hα : HfLvl α) : HgfB α where
  F := B.Q
  Fr := B.P
  γ := B.γ
  γN := max B.γ α
  Zo := B.Zo
  lv := hα
  γ_le := le_max_left _ _
  lvN := le_max_right _ _
  γN_lt := max_lt B.γ_lt hα.2
  F_fix := B.Q_fix α hα.2
  G_le := B.G_lt.le
  N_lt1 := B.N_lt1 α hα.2
  F_mem := B.Q_mem
  N_mem := B.N_mem α hα.2
  F_code := B.Q_code α hα.2
  F_cl := B.Q_cl α hα.2
  N_cl := B.N_cl α hα.2
  γN_cl := fun Z hZ hZ1 hγ hα' => max_lt hγ hα'
  Fr_gt := fun hx hx1 hγ => B.P_gt α hα.2 hx hx1 hγ
  Fr_fix := fun hx hx1 hγ => B.P_fix α hα.2 hx hx1 hγ
  N_Zo := fun hx hx1 hγ => B.N_Zo α hα.2 hx hx1 hγ
  Zo_fix := B.Zo_fix
  Zo_G1 := B.Zo_G1
  Fr_pi := B.P_pi α hα.2
  N_pi := B.N_pi α hα.2

@[simp] theorem toB_Q (α : Ordinal.{0}) (hα : HfLvl α) : (B.toB α hα).F = B.Q := rfl

/-- The level-offset base `φ(Ω₁, G+1+ν)` satisfies the gated abstract-base laws. -/
noncomputable def hhFB (ν : Ordinal.{0}) (hν : ν < ε₀) : HhQB where
  Q := Hg.hgFQ ν
  P := Hg.hgFP ν
  γ := 0
  Zo := (Hg.hgFB ν hν).Zo
  γ_lt := by
    have h1 : (1 : Ordinal.{0}) < Om1 := by simpa using Gl.gl_nat_lt_Om1 1
    exact (zero_lt_one : (0 : Ordinal.{0}) < 1).trans h1
  Q_fix := fun α hα => (Hg.hgFB ν hν).Q_fix α hα
  G_lt := (Hg.hgFB ν hν).G_lt
  Q_lt1 := (Hg.hgFB ν hν).Q_lt1
  N_lt1 := fun α hα => (Hg.hgFB ν hν).N_lt1 hα
  Q_mem := fun S {a b} ha hb => by
    simpa [Hg.hgFB] using (Hg.hgFB ν hν).Q_mem S ha
  N_mem := by
    intro α hα S a b ha hb
    exact (Hg.hgFB ν hν).N_mem S hα ha
      (by simpa [max_eq_right (show (0 : Ordinal.{0}) ≤ α from by exact zero_le)] using hb)
  Q_code := fun α hα Z hZ hZ1 y hy hQy hyN => (Hg.hgFB ν hν).Q_code Z hZ hZ1
  Q_cl := fun α hα Z hZ hZ1 y hy hQy hyN => zero_lt_one.trans (gg_one_lt_of_SC hZ)
  N_cl := by
    intro α hα Z hZ hZ1 hN
    have hαZ : α < Z := by
      have hβ1 : α + 1 < Om1 := Gl.gl_Om1_lim.add_one_lt hα
      have hβ : 1 ≤ α + 1 := le_add_self
      have hc := (Hg.hgFB ν hν).cl_lev hβ hβ1 hZ hZ1
      have hN' : GxCl Z {gcG 0} (veblen (α + 1) ((Hg.hgFB ν hν).Q + 1)) := by
        rw [← (Hg.hgFB ν hν).N_eq hα]
        simpa [Hg.hgFB] using hN
      exact (lt_add_one α).trans (hc hN')
    simpa [max_eq_right (show (0 : Ordinal.{0}) ≤ α from by exact zero_le)] using hαZ
  P_gt := by
    intro α x hα hx hx1 hγ
    exact Hg.hgFP_gt hx hx1 ν
  P_fix := by
    intro α x hα hx hx1 hγ
    exact (Hg.hgFB ν hν).P_fix hx hx1 α
      (by simpa [max_eq_right (show (0 : Ordinal.{0}) ≤ α from by exact zero_le)] using hγ)
  N_Zo := by
    intro α x hα hx hx1 hγ
    exact (Hg.hgFB ν hν).N_lt_Zo hx hx1
      (by simpa [max_eq_right (show (0 : Ordinal.{0}) ≤ α from by exact zero_le)] using hγ)
  Zo_fix := (Hg.hgFB ν hν).Zo_fix
  Zo_G1 := fun x hx hx1 => (Hg.hgFB ν hν).Zo_lt1 hx hx1
  P_pi := by
    intro α σ ρ hα hB hγ
    exact (Hg.hgFB ν hν).P_pi hB
  N_pi := by
    intro α σ ρ hα hB hγ
    have hασ : α < σ := by
      simpa [max_eq_right (show (0 : Ordinal.{0}) ≤ α from by exact zero_le)] using hγ
    exact (Hg.hgFB ν hν).NP_pi hB ((ev_isSuccLimit_of_inE hB.1).add_one_lt hασ)

@[simp] theorem hhFB_Q (ν : Ordinal.{0}) (hν : ν < ε₀) : (hhFB ν hν).Q = Hg.hgFQ ν := by
  unfold hhFB
  rfl

/-- The concrete base in the family notation `Qν = φ(Ω₁, G+1+ν)`. -/
theorem hhFB_Q_formula (ν : Ordinal.{0}) (hν : ν < ε₀) :
    (hhFB ν hν).Q = veblen Om1 (gcG 0 + 1 + ν) := by
  rw [hhFB_Q]
  rfl

/-- The concrete gated base has the same level instance as the existing offset base. -/
theorem hhFB_toB (ν : Ordinal.{0}) (hν : ν < ε₀)
    (α : Ordinal.{0}) (hα : HfLvl α) :
    ((hhFB ν hν).toB α hα).F = ((Hg.hgFB ν hν).toB α hα).F ∧
    ((hhFB ν hν).toB α hα).Fr = ((Hg.hgFB ν hν).toB α hα).Fr ∧
    ((hhFB ν hν).toB α hα).γ = ((Hg.hgFB ν hν).toB α hα).γ ∧
    ((hhFB ν hν).toB α hα).γN = ((Hg.hgFB ν hν).toB α hα).γN ∧
    ((hhFB ν hν).toB α hα).Zo = ((Hg.hgFB ν hν).toB α hα).Zo := by
  refine ⟨rfl, rfl, rfl, ?_, rfl⟩
  simp [HhQB.toB, hhFB, Hg.HgQB.toB]

#print axioms hhFB



end HhQB

end Googology.Trans.PoR.InaccPsi.R2.Hg
