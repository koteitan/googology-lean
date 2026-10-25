import Googology.Trans.PoR.InaccPsi.R2.GvFr
import Googology.Trans.PoR.InaccPsi.R2.GvCl

/-!
# A SEQUENCE OF GATED DIGIT SYSTEMS OVER ANY INDEX `P + j` (`Ω₁ ∣ P`)

Port of `Gs.GsSeq` (`R2.GsLim`) with the start index `ix0` no longer fixed to `G`: `ix0 = P + j` with `Ω₁ ∣ P`,
`Ω₁ ≤ P`, `j < Ω₁`.  The code-gate condition of the union (`γ_cl`) comes from `gv_cl_l` (in `R2.GsLim` from
`Gr.gr_cl_Bl`, which needs `ix0 = G`); every other proof is unchanged.  The union is the gated union `Gs.GsCh.lim`.

* `GvSeq`, `GvSeq.B_eq`, `GvSeq.T_lt1`, `GvSeq.x_lt_bω`, `GvSeq.hval`, `GvSeq.bω_eq` (`ϑˣ(Ω₁ + a(x) + T) =
  φ(1, i(x) + Δ)` above the gate), `GvSeq.toCh` (**THE CHAIN OF A SEQUENCE**), `toCh_lim_ix`, `toCh_lim_γ`,
  `toCh_lim_b`, `toCh_lim_ba`.

No new axiom.  New definitions: `GvSeq`, `GvSeq.toCh`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gv

open Googology.Trans.PoR.InaccPsi.R2.Gs

open Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq Googology.Trans.PoR.InaccPsi.R2.Gr

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gq
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## A sequence of gated digit systems with a common index pattern -/

/-- **A sequence of gated digit systems** `D k` with bases `φ(1, i(x) + δ_k)`, offsets `a(x) + s_k`, bounds
`φ(1, ix0 + δ_k)`, `δ_k → Δ`, `s_k → T` (countable constants, `T ≤ γω = Δ`), each extending
the previous. -/
structure GvSeq where
  D : ℕ → GsD
  ix0 : Ordinal.{0}
  i : Ordinal.{0} → Ordinal.{0}
  a : Ordinal.{0} → Ordinal.{0}
  δ : ℕ → Ordinal.{0}
  s : ℕ → Ordinal.{0}
  Δ : Ordinal.{0}
  T : Ordinal.{0}
  γω : Ordinal.{0}
  hix : ∀ k, (D k).ix = ix0 + δ k
  hb : ∀ k x, InE x → x < Om1 → γω < x → (D k).b x = veblen 1 (i x + δ k)
  hba : ∀ k x, (D k).ba x = a x + s k
  coh_R : ∀ k c x, c < (D k).B → (D (k + 1)).R c x = (D k).R c x
  coh_g : ∀ k c, c < (D k).B → (D (k + 1)).g c = (D k).g c
  cf_g : ∀ k, (D (k + 1)).g (D k).B ≤ max γω ε₀
  γ_le : ∀ k, (D k).γ ≤ γω
  γω_lt : γω < Om1
  γω_le : γω ≤ Δ
  Δ_le : Δ ≤ γω
  T_le : T ≤ γω
  δ_mono : ∀ k, δ k < δ (k + 1)
  δ_lt : ∀ k, δ k < Δ
  δ_cof : ∀ t, t < Δ → ∃ k, t < δ k
  Δ_lim : IsSuccLimit Δ
  Δ_lt : Δ < Om1
  s_lt : ∀ k, s k < T
  s_cof : ∀ t, t < T → ∃ k, t < s k
  ix_mem : ∀ (S : InaccSeq.{0}) (a b : Ordinal.{0}), 0 < a → γω < b → ix0 + Δ ∈ S.CSet a b
  ix0_lt : ix0 < gcG 1
  P0 : Ordinal.{0}
  j0 : Ordinal.{0}
  ix0_eq : ix0 = P0 + j0
  P0_dvd : Om 1 ∣ P0
  P0_ge : Om 1 ≤ P0
  j0_lt : j0 < Om 1
  a_lt : ∀ x, InE x → x < Om1 → a x < gq 1 x
  a_pi : ∀ σ ρ, Bases σ ρ → γω < σ → a ρ ∈ TB ρ σ ∧ pi σ ρ (a ρ) = a σ
  i_big : ∀ x, InE x → x < Om1 → lgG x ≤ veblen 1 (i x)

namespace GvSeq

variable (Q : GvSeq)

theorem B_eq (k : ℕ) : (Q.D k).B = veblen 1 (Q.ix0 + Q.δ k) := by rw [(Q.D k).B_ix, Q.hix]

theorem Δ_ne : Q.Δ ≠ 0 := Q.Δ_lim.bot_lt.ne'

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγx : Q.γω < x)
include hx hx1 hγx

theorem T_lt1 : Q.a x + Q.T < gq 1 x := by
  have hq := (gm1_facts hx hx1).2.2.2
  exact (inE_indec hq).add_lt (Q.a_lt x hx hx1) ((Q.T_le.trans_lt hγx).trans (gm1_facts hx hx1).2.1)

/-- `x < φ(1, i(x) + Δ)` above the gate. -/
theorem x_lt_bω : x < veblen 1 (Q.i x + Q.Δ) := by
  have h := (Q.D 0).x_lt_b x hx hx1 ((Q.γ_le 0).trans_lt hγx)
  rw [Q.hb 0 x hx hx1 hγx] at h
  exact h.trans ((isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 (Q.δ_lt 0)))

theorem hval (k : ℕ) : glA 1 (Q.a x + Q.s k) x = veblen 1 (Q.i x + Q.δ k + 1) := by
  rw [← Q.hba, ← (Q.D k).b_eN x hx hx1 ((Q.γ_le k).trans_lt hγx), Q.hb k x hx hx1 hγx, go_eN_veb]

/-- **The base of the union**: `ϑˣ(Ω₁ + a(x) + T) = φ(1, i(x) + Δ)`. -/
theorem bω_eq : glA 1 (Q.a x + Q.T) x = veblen 1 (Q.i x + Q.Δ) := by
  have hF : IsSuccLimit (Q.i x + Q.Δ) := isSuccLimit_add _ Q.Δ_lim
  refine go_glA_sup hx hx1 (s := fun k => Q.a x + Q.s k) (f := fun k => Q.i x + Q.δ k + 1) (Q.T_lt1 hx hx1 hγx)
    (fun k => (add_lt_add_iff_left _).2 (Q.s_lt k)) (fun σ hσ => ?_) (fun k => ?_) (fun σ hσ => ?_) hF ?_
    (fun k => Q.hval hx hx1 hγx k)
  · exact go_lt_add_sup (lt_of_le_of_lt zero_le (Q.s_lt 0)).ne' Q.s_cof hσ
  · show Q.i x + Q.δ k + 1 < Q.i x + Q.Δ
    rw [add_assoc]; exact (add_lt_add_iff_left _).2 (Q.Δ_lim.add_one_lt (Q.δ_lt k))
  · obtain ⟨k, hk⟩ := go_lt_add_sup Q.Δ_ne Q.δ_cof hσ
    exact ⟨k, hk.trans (lt_add_one _)⟩
  · have h0 := Q.hval hx hx1 hγx 0
    have hT0 : Q.a x + Q.s 0 < gq 1 x := ((add_lt_add_iff_left _).2 (Q.s_lt 0)).trans (Q.T_lt1 hx hx1 hγx)
    obtain ⟨hT0T, hT01⟩ := gm1_T hx hx1 hT0
    obtain ⟨h1T, h11⟩ := gl_one_T hx hx1
    have ha : Q.a x < veblen 1 (Q.i x + Q.Δ) := by
      have h1 := (glA_facts hx hx1 le_rfl h1T h11 hT0T hT01).2.2.2.2.2
      rw [h0] at h1
      refine (le_self_add.trans_lt h1).trans ((isNormal_veblen 1).strictMono ?_)
      rw [add_assoc]; exact (add_lt_add_iff_left _).2 (Q.Δ_lim.add_one_lt (Q.δ_lt 0))
    have hTb : Q.T < veblen 1 (Q.i x + Q.Δ) := (Q.T_le.trans_lt hγx).trans (Q.x_lt_bω hx hx1 hγx)
    exact (inE_indec (omega0_opow_epsilon _)).add_lt ha hTb

end Base

/-- **THE CHAIN OF A SEQUENCE**: base `ϑˣ(Ω₁ + a(x) + T) = φ(1, i(x) + Δ)`, bound `φ(1, ix0 + Δ)`, base gate `γω`. -/
noncomputable def toCh : GsCh where
  D := Q.D
  ixω := Q.ix0 + Q.Δ
  bω := fun x => glA 1 (Q.a x + Q.T) x
  baω := fun x => Q.a x + Q.T + 1
  γω := Q.γω
  γω_lt := Q.γω_lt
  γ_cl := fun Z hZ hZ1 h => Q.γω_le.trans_lt (gv_cl_l hZ hZ1 Q.P0_dvd Q.P0_ge Q.j0_lt Q.Δ_ne
    (by rw [← Br.Om1_eq]; exact Q.Δ_lt) (by have h' := h; rw [Q.ix0_eq] at h'; exact h'))
  γ_le := Q.γ_le
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
    exact (inE_indec hE).add_lt Q.ix0_lt (Q.Δ_lt.trans Gs.gs_Om1_lt_gcG1)
  cf_g := Q.cf_g
  b_le := fun k x hx hx1 hγx => by
    rw [Q.hb k x hx hx1 hγx, Q.bω_eq hx hx1 hγx]
    exact (isNormal_veblen 1).monotone ((add_le_add_iff_left _).2 (Q.δ_lt k).le)
  b_sup := fun x hx hx1 hγx ν hν => by
    rw [Q.bω_eq hx hx1 hγx] at hν
    obtain ⟨t, ht, hνt⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ Q.Δ_lim)).1 hν
    obtain ⟨k, hk⟩ := go_lt_add_sup Q.Δ_ne Q.δ_cof ht
    exact ⟨k, by rw [Q.hb k x hx hx1 hγx]; exact hνt.trans ((isNormal_veblen 1).strictMono hk)⟩
  b_E := fun x hx hx1 hγx => by rw [Q.bω_eq hx hx1 hγx]; exact omega0_opow_epsilon _
  b_eN := fun x hx hx1 hγx => by
    obtain ⟨hT, h1⟩ := gm1_T hx hx1 (Q.T_lt1 hx hx1 hγx)
    exact glA_eN_one hx hx1 hT h1
  ba_lt := fun x hx hx1 hγx =>
    (ev_isSuccLimit_of_inE (gm1_facts hx hx1).2.2.2).add_one_lt (Q.T_lt1 hx hx1 hγx)
  b_Z := fun x hx hx1 hγx => by
    refine go_eN_lt_evZ ?_
    rw [Q.bω_eq hx hx1 hγx]
    have hZ := evZ_E (lgG x)
    have hi : Q.i x < evZ (lgG x) := by
      have h0 := (Q.D 0).b_Z x hx hx1 ((Q.γ_le 0).trans_lt hγx)
      rw [Q.hb 0 x hx hx1 hγx] at h0
      exact (le_self_add.trans (right_le_veblen 1 _)).trans_lt ((lt_eN _).trans h0)
    have hiΔ : Q.i x + Q.Δ < evZ (lgG x) :=
      (inE_indec hZ).add_lt hi ((Q.Δ_le.trans_lt hγx).trans (((Q.D 0).x_lt_b x hx hx1 ((Q.γ_le 0).trans_lt hγx)).trans
        ((lt_eN _).trans ((Q.D 0).b_Z x hx hx1 ((Q.γ_le 0).trans_lt hγx)))))
    have := (isNormal_veblen 1).strictMono hiΔ
    rwa [show veblen 1 (evZ (lgG x)) = evZ (lgG x) from epsilon_evZ _] at this
  b_pi := fun σ ρ hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hTσ : Q.T < σ := Q.T_le.trans_lt hγ
    obtain ⟨g1, g2⟩ := Q.a_pi σ ρ hB hγ
    obtain ⟨s1, s2⟩ := pi_add hB g1 (mem_TB_of_lt hB hTσ)
    obtain ⟨o1, o2⟩ := one_TB hB
    have h := glA_pi hB o1 (gl_one_T hB.2.1 hρ1).2 s1 (gm1_T hB.2.1 hρ1 (Q.T_lt1 hB.2.1 hρ1 (hγ.trans hB.2.2.1))).2
    rw [o2, s2, g2, pi_lt hB hTσ] at h
    exact h
  ba_pi := fun σ ρ hB hγ => by
    have hTσ : Q.T < σ := Q.T_le.trans_lt hγ
    obtain ⟨g1, g2⟩ := Q.a_pi σ ρ hB hγ
    obtain ⟨s1, s2⟩ := pi_add hB g1 (mem_TB_of_lt hB hTσ)
    obtain ⟨o1, o2⟩ := one_TB hB
    obtain ⟨t1, t2⟩ := pi_add hB s1 o1
    exact ⟨t1, by rw [t2, s2, g2, o2, pi_lt hB hTσ]⟩

theorem toCh_D : Q.toCh.D = Q.D := rfl

theorem toCh_lim_ix : Q.toCh.lim.ix = Q.ix0 + Q.Δ := rfl

theorem toCh_lim_γ : Q.toCh.lim.γ = Q.γω := rfl

theorem toCh_lim_b {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγx : Q.γω < x) :
    Q.toCh.lim.b x = veblen 1 (Q.i x + Q.Δ) := Q.bω_eq hx hx1 hγx

theorem toCh_lim_ba (x : Ordinal.{0}) : Q.toCh.lim.ba x = Q.a x + Q.T + 1 := rfl

end GvSeq

end Googology.Trans.PoR.InaccPsi.R2.Gv
