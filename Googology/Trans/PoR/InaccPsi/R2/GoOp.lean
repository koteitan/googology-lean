import Googology.Trans.PoR.InaccPsi.R2.GoLim

/-!
# OPERATIONS ON DIGIT SYSTEMS: the step, its `ω`-iterate, and the diagonal of a sequence of operations

A sequence of digit systems whose bases are `φ(1, i(x) + δ_k)` with `δ_k` increasing to a limit `Δ < ε₀` (and whose
bounds, `ba`-offsets move alike) is a chain (`GoSeq.toCh`, `R2.GoLim`): the base of the union is
`ϑˣ(Ω₁ + a(x) + T) = φ(1, i(x) + Δ)` (`go_glA_sup`).  An operation `O : GoOp` maps every digit system `D` to a digit
system extending it whose base index grows by `ω^e` (`e < ε₀`): `stepOp` (the step `GoD.step`, `e = 0`),
`GoOp.U` (**the union of the iterates `O^k(D)`**, `e ↦ e + 1`), and `GoOpSeq.diag` (**the union of `O_k(D)` for a
sequence of operations each extending the previous one**, `e = sup_k e_k`).  So one step and one limit give every
base `ε_{B+ω^e}` of the iteration below.

* `go_lt_add_sup`, `go_opow_mem`, `go_eps0_le`;
* `GoSeq`, `GoSeq.toCh` (**THE CHAIN OF A SEQUENCE**), `GoSeq.bω_eq`;
* `GoOp`, `GoOp.B_eq`, `GoOp.it_*`, `GoOp.chain`, `GoOp.U` (**THE `ω`-ITERATE**), `stepOp` (**THE STEP AS AN
  OPERATION**), `GoExt`, `GoOp.ext_U`, `GoOpSeq`, `GoOpSeq.diag` (**THE DIAGONAL**), `GoOpSeq.ext_diag`.

No new axiom.  New definitions: `GoSeq`, `GoSeq.toCh`, `GoOp`, `GoOp.it`, `GoOp.seq`, `GoOp.chain`, `GoOp.U`,
`stepOp`, `GoExt`, `GoOpSeq`, `GoOpSeq.seq`, `GoOpSeq.diag`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Go

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## Ordinal facts -/

/-- `σ < a + Δ ⇒ σ < a + δ_k` for some `k`, when every `t < Δ` lies below some `δ_k`. -/
theorem go_lt_add_sup {a σ Δ : Ordinal.{0}} {δ : ℕ → Ordinal.{0}} (hΔ : Δ ≠ 0)
    (hcof : ∀ t, t < Δ → ∃ k, t < δ k) (h : σ < a + Δ) : ∃ k, σ < a + δ k := by
  obtain ⟨d, hd, hσ⟩ := (lt_add_iff hΔ).1 h
  obtain ⟨k, hk⟩ := hcof d hd
  exact ⟨k, hσ.trans_lt ((add_lt_add_iff_left a).2 hk)⟩

theorem go_opow_mem {S : InaccSeq.{0}} {a b e : Ordinal.{0}} (he : e ∈ S.CSet a b) : ω ^ e ∈ S.CSet a b := by
  have := CSet.phi_mem (CSet.zero_mem (S := S) a b) he
  rwa [veblen_zero_apply] at this

/-- Every `ε`-number is at least `ε₀`. -/
theorem go_eps0_le {x : Ordinal.{0}} (hx : InE x) : ε₀ ≤ x := epsilon_zero_le_of_omega0_opow_le hx.le

theorem go_eps0_le_veb (F : Ordinal.{0}) : ε₀ ≤ veblen 1 F :=
  (isNormal_veblen 1).monotone zero_le

theorem go_eN_eq {u : Ordinal.{0}} (hu : InE u) : eN u = veblen 1 (evIx u + 1) := by
  conv_lhs => rw [← show veblen 1 (evIx u) = u from epsilon_evIx hu]
  exact go_eN_veb _

theorem go_evIx_veb (t : Ordinal.{0}) : evIx (veblen 1 t) = t := evIx_epsilon t

/-! ## A sequence of digit systems with a common index pattern -/

/-- **A sequence of digit systems** `D k` with bases `φ(1, i(x) + δ_k)`, offsets `a(x) + s_k`, bounds
`φ(1, ix0 + δ_k)`, `δ_k → Δ`, `s_k → T` (constants below `ε₀`), each extending the previous. -/
structure GoSeq where
  D : ℕ → GoD
  ix0 : Ordinal.{0}
  i : Ordinal.{0} → Ordinal.{0}
  a : Ordinal.{0} → Ordinal.{0}
  δ : ℕ → Ordinal.{0}
  s : ℕ → Ordinal.{0}
  Δ : Ordinal.{0}
  T : Ordinal.{0}
  hix : ∀ k, (D k).ix = ix0 + δ k
  hb : ∀ k x, InE x → x < Om1 → (D k).b x = veblen 1 (i x + δ k)
  hba : ∀ k x, (D k).ba x = a x + s k
  coh_R : ∀ k c x, c < (D k).B → (D (k + 1)).R c x = (D k).R c x
  coh_g : ∀ k c, c < (D k).B → (D (k + 1)).g c = (D k).g c
  cf_g : ∀ k, (D (k + 1)).g (D k).B < ε₀
  δ_mono : ∀ k, δ k < δ (k + 1)
  δ_lt : ∀ k, δ k < Δ
  δ_cof : ∀ t, t < Δ → ∃ k, t < δ k
  Δ_lim : IsSuccLimit Δ
  Δ_lt : Δ < ε₀
  s_lt : ∀ k, s k < T
  s_cof : ∀ t, t < T → ∃ k, t < s k
  T_lt : T < ε₀
  ix_mem : ∀ (S : InaccSeq.{0}) (a b : Ordinal.{0}), 0 < a → ix0 + Δ ∈ S.CSet a b
  ix0_lt : ix0 < gcG 1
  a_lt : ∀ x, InE x → x < Om1 → a x < gq 1 x
  a_pi : ∀ σ ρ, Bases σ ρ → a ρ ∈ TB ρ σ ∧ pi σ ρ (a ρ) = a σ

namespace GoSeq

variable (Q : GoSeq)

theorem B_eq (k : ℕ) : (Q.D k).B = veblen 1 (Q.ix0 + Q.δ k) := by rw [(Q.D k).B_ix, Q.hix]

theorem Δ_ne : Q.Δ ≠ 0 := Q.Δ_lim.bot_lt.ne'

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem T_lt1 : Q.a x + Q.T < gq 1 x := by
  have hq := (gm1_facts hx hx1).2.2.2
  exact (inE_indec hq).add_lt (Q.a_lt x hx hx1)
    (Q.T_lt.trans_le ((go_eps0_le hx).trans (gm1_facts hx hx1).2.1.le))

theorem hval (k : ℕ) : glA 1 (Q.a x + Q.s k) x = veblen 1 (Q.i x + Q.δ k + 1) := by
  rw [← Q.hba, ← (Q.D k).b_eN x hx hx1, Q.hb k x hx hx1, go_eN_veb]

/-- **The base of the union**: `ϑˣ(Ω₁ + a(x) + T) = φ(1, i(x) + Δ)`. -/
theorem bω_eq : glA 1 (Q.a x + Q.T) x = veblen 1 (Q.i x + Q.Δ) := by
  have hF : IsSuccLimit (Q.i x + Q.Δ) := isSuccLimit_add _ Q.Δ_lim
  refine go_glA_sup hx hx1 (s := fun k => Q.a x + Q.s k) (f := fun k => Q.i x + Q.δ k + 1) (Q.T_lt1 hx hx1)
    (fun k => (add_lt_add_iff_left _).2 (Q.s_lt k)) (fun σ hσ => ?_) (fun k => ?_) (fun σ hσ => ?_) hF ?_
    (fun k => Q.hval hx hx1 k)
  · exact go_lt_add_sup (lt_of_le_of_lt zero_le (Q.s_lt 0)).ne' Q.s_cof hσ
  · show Q.i x + Q.δ k + 1 < Q.i x + Q.Δ
    rw [add_assoc]; exact (add_lt_add_iff_left _).2 (Q.Δ_lim.add_one_lt (Q.δ_lt k))
  · obtain ⟨k, hk⟩ := go_lt_add_sup Q.Δ_ne Q.δ_cof hσ
    exact ⟨k, hk.trans (lt_add_one _)⟩
  · have h0 := Q.hval hx hx1 0
    have hT0 : Q.a x + Q.s 0 < gq 1 x := ((add_lt_add_iff_left _).2 (Q.s_lt 0)).trans (Q.T_lt1 hx hx1)
    obtain ⟨hT0T, hT01⟩ := gm1_T hx hx1 hT0
    obtain ⟨h1T, h11⟩ := gl_one_T hx hx1
    have ha : Q.a x < veblen 1 (Q.i x + Q.Δ) := by
      have h1 := (glA_facts hx hx1 le_rfl h1T h11 hT0T hT01).2.2.2.2.2
      rw [h0] at h1
      refine (le_self_add.trans_lt h1).trans ((isNormal_veblen 1).strictMono ?_)
      rw [add_assoc]; exact (add_lt_add_iff_left _).2 (Q.Δ_lim.add_one_lt (Q.δ_lt 0))
    exact (inE_indec (omega0_opow_epsilon _)).add_lt ha (Q.T_lt.trans_le (go_eps0_le_veb _))

end Base

/-- **THE CHAIN OF A SEQUENCE**: base `ϑˣ(Ω₁ + a(x) + T) = φ(1, i(x) + Δ)`, bound `φ(1, ix0 + Δ)`. -/
noncomputable def toCh : GoCh where
  D := Q.D
  ixω := Q.ix0 + Q.Δ
  bω := fun x => glA 1 (Q.a x + Q.T) x
  baω := fun x => Q.a x + Q.T + 1
  coh_R := Q.coh_R
  coh_g := Q.coh_g
  B_mono := fun k => by
    rw [Q.B_eq, Q.B_eq]
    exact (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 (Q.δ_mono k))
  B_lt := fun k => by
    rw [Q.B_eq]; exact (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 (Q.δ_lt k))
  B_cof := fun c hc => by
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ Q.Δ_lim)).1 hc
    obtain ⟨k, hk⟩ := go_lt_add_sup Q.Δ_ne Q.δ_cof ht
    exact ⟨k, by rw [Q.B_eq]; exact hct.trans ((isNormal_veblen 1).strictMono hk)⟩
  ix_mem := Q.ix_mem
  ix_lt := by
    have hE : InE (gcG 1) := Low.opow_eq_self_of_SC (gcG_SC 1)
    exact (inE_indec hE).add_lt Q.ix0_lt (Q.Δ_lt.trans_le (go_eps0_le hE))
  cf_g := Q.cf_g
  b_le := fun k x hx hx1 => by
    rw [Q.hb k x hx hx1, Q.bω_eq hx hx1]
    exact (isNormal_veblen 1).monotone ((add_le_add_iff_left _).2 (Q.δ_lt k).le)
  b_sup := fun x hx hx1 ν hν => by
    rw [Q.bω_eq hx hx1] at hν
    obtain ⟨t, ht, hνt⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ Q.Δ_lim)).1 hν
    obtain ⟨k, hk⟩ := go_lt_add_sup Q.Δ_ne Q.δ_cof ht
    exact ⟨k, by rw [Q.hb k x hx hx1]; exact hνt.trans ((isNormal_veblen 1).strictMono hk)⟩
  b_E := fun x hx hx1 => by rw [Q.bω_eq hx hx1]; exact omega0_opow_epsilon _
  b_eN := fun x hx hx1 => by
    obtain ⟨hT, h1⟩ := gm1_T hx hx1 (Q.T_lt1 hx hx1)
    exact glA_eN_one hx hx1 hT h1
  ba_lt := fun x hx hx1 =>
    (ev_isSuccLimit_of_inE (gm1_facts hx hx1).2.2.2).add_one_lt (Q.T_lt1 hx hx1)
  b_Z := fun x hx hx1 => by
    refine go_eN_lt_evZ ?_
    rw [Q.bω_eq hx hx1]
    have hZ := evZ_E (lgG x)
    have hi : Q.i x < evZ (lgG x) := by
      have h0 := (Q.D 0).b_Z x hx hx1
      rw [Q.hb 0 x hx hx1] at h0
      exact (le_self_add.trans (right_le_veblen 1 _)).trans_lt ((lt_eN _).trans h0)
    have hiΔ : Q.i x + Q.Δ < evZ (lgG x) :=
      (inE_indec hZ).add_lt hi (Q.Δ_lt.trans_le (go_eps0_le hZ))
    have := (isNormal_veblen 1).strictMono hiΔ
    rwa [show veblen 1 (evZ (lgG x)) = evZ (lgG x) from epsilon_evZ _] at this
  b_pi := fun σ ρ hB => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hTσ : Q.T < σ := Q.T_lt.trans_le (go_eps0_le hB.1)
    obtain ⟨g1, g2⟩ := Q.a_pi σ ρ hB
    obtain ⟨s1, s2⟩ := pi_add hB g1 (mem_TB_of_lt hB hTσ)
    obtain ⟨o1, o2⟩ := one_TB hB
    have h := glA_pi hB o1 (gl_one_T hB.2.1 hρ1).2 s1 (gm1_T hB.2.1 hρ1 (Q.T_lt1 hB.2.1 hρ1)).2
    rw [o2, s2, g2, pi_lt hB hTσ] at h
    exact h
  ba_pi := fun σ ρ hB => by
    have hTσ : Q.T < σ := Q.T_lt.trans_le (go_eps0_le hB.1)
    obtain ⟨g1, g2⟩ := Q.a_pi σ ρ hB
    obtain ⟨s1, s2⟩ := pi_add hB g1 (mem_TB_of_lt hB hTσ)
    obtain ⟨o1, o2⟩ := one_TB hB
    obtain ⟨t1, t2⟩ := pi_add hB s1 o1
    exact ⟨t1, by rw [t2, s2, g2, o2, pi_lt hB hTσ]⟩

theorem toCh_D : Q.toCh.D = Q.D := rfl

theorem toCh_lim_ix : Q.toCh.lim.ix = Q.ix0 + Q.Δ := rfl

theorem toCh_lim_b {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    Q.toCh.lim.b x = veblen 1 (Q.i x + Q.Δ) := Q.bω_eq hx hx1

theorem toCh_lim_ba (x : Ordinal.{0}) : Q.toCh.lim.ba x = Q.a x + Q.T + 1 := rfl

end GoSeq

end Googology.Trans.PoR.InaccPsi.R2.Go
