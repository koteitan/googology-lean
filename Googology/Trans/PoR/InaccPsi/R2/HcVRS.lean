import Googology.Trans.PoR.InaccPsi.R2.HcVStep
import Googology.Trans.PoR.InaccPsi.R2.GwFr

/-!
# HcVRS: TEXTUAL COPY OF `Gz.GzVRS` (via `Hb.HbV…`) FOR `Hc.HcVD` (readings below `B_x(x)`)

The declarations of `Gz.GzVRS` with `Gz.GzVD` (bound field `Z(x) ≤ B₃(x)`) replaced by `Hc.HcVD` (bound field
`Z(x) ≤ B_x(x)`, `Hc.hcBR`); the proofs are unchanged except where the bound enters (`HcVD.R_lt_gq`,
the field `Z_BR`,
Lemma IMG in `HcVD.toLD` through `Hc.hc_pkg_BR`).

No new axiom.  New definitions: the copies of the definitions of `Gz.GzVRS` (namespace `HcVD`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hc

open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha

open Googology.Trans.PoR.InaccPsi.R2.Gw

open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gp
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

namespace HcVD

variable (D : HcVD)

/-- The codes below `c ≤ B` with gate below `y < Ω₁` are countably many. -/
theorem count {c y : Ordinal.{0}} (hc : c ≤ D.B) (hy : InE y) (hy1 : y < Om1) :
    Countable {b : Iio c // D.g b.1 < y} := by
  have hq1 : gq 1 y < Om (1 : Ordinal.{0}) := by rw [← Br.Om1_eq]; exact (gm1_facts hy hy1).2.2.1
  haveI := Gc.gc_countable hq1
  let f : {b : Iio c // D.g b.1 < y} → Iio (gq 1 y) := fun b =>
    ⟨D.R b.1.1 y, D.R_lt_gq hy hy1 (lt_of_lt_of_le b.1.2 hc) b.2⟩
  refine Function.Injective.countable (f := f) fun b b' hbb => ?_
  have e : D.R b.1.1 y = D.R b'.1.1 y := congrArg Subtype.val hbb
  rcases lt_trichotomy b.1.1 b'.1.1 with h | h | h
  · exact absurd e (D.mono y hy hy1 _ (lt_of_lt_of_le b'.1.2 hc) _ h b'.2 b.2).ne
  · exact Subtype.ext (Subtype.ext h)
  · exact absurd e (D.mono y hy hy1 _ (lt_of_lt_of_le b.1.2 hc) _ h b.2 b'.2).ne'

/-- **The code system of a `HcVD`**: bound `B`, gate `D.g`. -/
noncomputable def toK : GsCS where
  B := D.B
  gt := D.g
  B_V := D.B_V
  gt_zero := D.g_zero
  gt_lt := D.g_lt
  gt_succ := fun b Z hZ hb hg => D.g_succ Z hZ b hb hg
  mem := fun S _ _ c hc hca hg => (D.mem S _ _ (lt_of_le_of_lt zero_le hca) c hc hg).1
  κ := D.γ
  κ_lt := D.γ_lt
  B_mem := fun _ _ _ ha hγb => D.B_mem (lt_of_le_of_lt zero_le ha) hγb
  code_gate := fun Z hZ1 hZ0 hZa hZp c hc hcB => D.code_gate Z hZ1 hZ0 hZa hZp _ (by
    rintro s ⟨c', hc', -, rfl⟩
    rcases eq_or_ne c' 0 with rfl | h0
    · exact Or.inl rfl
    · exact Or.inr (D.B_lt1.le.trans (gcG_le (Order.one_le_iff_ne_zero.2 h0)))) c hc hcB
  count := fun _ _ hc hy hy1 => D.count hc hy hy1

theorem cofE {x c : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hc : c < D.B) (hEc : gfE < c) (hg : D.g c < x)
    {ν : Ordinal.{0}} (hν : ν < D.R c x) : ∃ b, gfE ≤ b ∧ b < c ∧ D.g b < x ∧ ν ≤ D.R b x := by
  obtain ⟨b, hbc, hgb, hνb⟩ := D.cof x hx hx1 c hc hg ν hν
  rcases lt_or_ge b gfE with hbE | hbE
  · refine ⟨gfE, le_rfl, hEc, by rw [D.g_E]; exact hx.pos, ?_⟩
    exact hνb.trans (D.mono x hx hx1 gfE D.E_lt_B b hbE (by rw [D.g_E]; exact hx.pos) hgb).le
  · exact ⟨b, hbE, hbc, hgb, hνb⟩

theorem toLD : ∀ c, IsSuccLimit c → gfE < c → c < D.B → Nonempty (GsmLD D.toK D.R c) := by
  intro c hl hEc hc
  obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := D.ld c hl hc
  have hlg : ∀ x, InE x → x < Om1 → D.g c < x → lg (D.R c x) = T x := fun x hx hx1 hg => by
    obtain ⟨e1, e2, -, -⟩ := hdec x hx hx1 hg
    rw [e1]; exact Ge.lg_add_opow e2
  refine ⟨{
    cp := if gfE ≤ cp then cp else gfE
    lp := lp
    cp_ge := ?_
    cp_lt := ?_
    cp_g := ?_
    dec := ?_
    pkg := ?_ }⟩
  · split_ifs with h
    · exact h
    · exact le_rfl
  · split_ifs with h
    · exact hcp
    · exact hEc
  · show D.g _ ≤ D.g c
    split_ifs with h
    · exact hgcp
    · rw [D.g_E]; exact zero_le
  · intro x hx hx1 hg
    obtain ⟨e1, e2, e3, e4⟩ := hdec x hx hx1 hg
    show D.R c x = _ ∧ _
    rw [hlg x hx hx1 hg]
    refine ⟨e1, e2, e3, ?_⟩
    split_ifs with h
    · exact e4
    · push Not at h
      exact e4.trans (D.mono x hx hx1 gfE D.E_lt_B cp h (by rw [D.g_E]; exact hx.pos)
        (hgcp.trans_lt hg)).le
  · intro ρ τ δ h hg
    show GhPkg (D.g c) ρ δ (fun y => lg (D.R c y))
    have hρE := upsPt_inE h.ρU
    obtain ⟨e1, -, -, -⟩ := hdec ρ hρE h.ρ1 hg
    have hTρ : T ρ < hcBR ρ := by
      have h1 : T ρ ≤ D.R c ρ := by
        rw [e1]; exact (right_le_opow _ one_lt_omega0).trans le_add_self
      exact h1.trans_lt ((D.R_lt_Z ρ hρE h.ρ1 c hc hg).trans_le (D.Z_BR ρ hρE h.ρ1))
    have hP := hc_pkg_BR h (C := ∅) hg (by simp) hTρ
      (Gj.GjEx.of_bases fun σ ρ' hB hgσ => hex σ ρ' hB hgσ)
    exact GhPkg.congr h hP (fun y hyE hy1 hgy => (hlg y hyE hy1 hgy).symm) hg

/-- **THE READING SYSTEM of a `HcVD`.** -/
noncomputable def toRS : GsRS where
  K := D.toK
  R := D.R
  E_lt := D.E_lt_B
  B_lim := D.B_lim
  gt_E := D.g_E
  gt_lowE := D.g_lowE
  R_E := fun x _ _ => D.R_E x
  lt0 := fun c x hx hx1 hc hg => D.R_lt_gq hx hx1 hc hg
  mono := fun b c x hx hx1 hc hbc hgb hgc => D.mono x hx hx1 c hc b hbc hgc hgb
  succ := fun b x _ => D.R_succ b x
  gt_le_succ := D.g_le_succ
  cof := fun _ _ hx hx1 hc hEc hg _ hν => D.cofE hx hx1 hc hEc hg hν
  ex := fun σ ρ c hB hc hg => D.ex σ ρ hB c hc hg
  ld := D.toLD

theorem toRS_gt : D.toRS.K.gt = D.g := rfl

end HcVD

/-! ## Location of the bound of any `HcVD` with gate below `K` -/

section LocZ

variable (D : HcVD) (S : InaccSeq.{0}) (hγ : D.γ < Td.tdK S)
include hγ

theorem hcV_locD_g : D.step.toRS.K.gt D.B < Td.tdK S := by
  rw [HcVD.toRS_gt, HcVD.step_g_B]; exact hγ

/-- **THE BOUND OF EVERY `HcVD` WITH BASE GATE BELOW `K` IS LOCATED**: `Λ⁺ = ι(Γ(B)·ω)`, `P(Γ(B)·ω) < L(0)`. -/
theorem hcV_locD : ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG D.B * ω) ∧
    upsilon (xtB1 X) = Pv S (gcG D.B * ω) ∧ Pv S (gcG D.B * ω) < Nc.ncL S 0 :=
  ⟨gsX D.step.toRS _ D.E_lt_B.le D.B_lt_NB S (hcV_locD_g D S hγ),
    gsX_pkg D.step.toRS _ D.E_lt_B.le D.B_lt_NB S (hcV_locD_g D S hγ),
    gsLoc D.step.toRS _ D.E_lt_B.le D.B_lt_NB S (hcV_locD_g D S hγ)⟩

theorem hcV_locD_enum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG D.B * ω)) :
    CdUpper S l ∧ CdLower S l :=
  gsEnum D.step.toRS _ D.E_lt_B.le D.B_lt_NB S (hcV_locD_g D S hγ) hr hl

theorem hcV_locD_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG D.B * ω)) : CdCapV S l :=
  gsCapV D.step.toRS _ D.E_lt_B.le D.B_lt_NB S (hcV_locD_g D S hγ) hr hl

/-- **Theorem BLK^O below `P(Γ(B)·ω)`**, with the exact reaches. -/
theorem hcV_locD_blk :
    let X := gsX D.step.toRS _ D.E_lt_B.le D.B_lt_NB S (hcV_locD_g D S hγ)
    (∀ c' d, c' < d → d < upsilon (xtB1 X) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 X ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧ d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 X →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec X l)) ∧
    (∀ α < upsilon (xtB1 X), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  gsBlk D.step.toRS _ D.E_lt_B.le D.B_lt_NB S (hcV_locD_g D S hγ)

end LocZ

end Googology.Trans.PoR.InaccPsi.R2.Hc
