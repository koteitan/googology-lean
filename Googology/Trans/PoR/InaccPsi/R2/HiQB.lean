import Googology.Trans.PoR.InaccPsi.R2.HhQB

/-!
# HiQB: A GATED ABSTRACT BASE OF EVERY COUNTABLE LEVEL; THE `ω`-STEP AND THE LEVEL `ω` OVER IT

`Hg.HgQB` is a base with base gate `0`; its readings and Lemma EXACT hold at every base.  `Hg.HhQB` adds a gate `γ`
(readings, membership, EXACT only above `γ`).  `HiQB` is `Hg.HhQB` with the four facts the union over all levels
needs: the next `Ω₁`-point `hdNx x (P(x))` lies below `Γ_{x+2}` and has Lemma EXACT (above `γ`), `hdNx Ω₁ Q` lies in
every hull above `γ`, and a code `hdNx Ω₁ Q` over `Z` forces `γ < Z`.

* `HiQB`, the facts (`Q_fixk`, `Q_fixω`, `veb_lt1`, `N_eq`, `S_eq`, `cl_lev`, `Q_gate`, `NP_glA`, `N_lt_Zo`,
  `S_glA`, `NP_pi`, `S_pi`);
* `HiQB.toP` (**`Q` AS A GATED LEVEL-`ω` PSEUDO-BASE**), `HiQB.toA` (**`Q` AS A GATED BASE OF LEVEL `ω`**); the base
  of every countable level is `Hg.HhQB.toB` (code gate `γ`, reading gate `max(γ, α)`);
* `HiQStart`, `hiQW` (**THE `ω`-STEP AT `Q`**), `hiQW_start`, `hiQT` (**THE SYSTEM AT `φ(ω+1, Q+1)`**), `hiQT_high`.

No new axiom.  New definitions: `HiQB`, `HiQB.toP`, `HiQB.toA`, `HiQStart`, `hiQW`, `hiQT`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hi

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
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **A GATED ABSTRACT BASE OF EVERY COUNTABLE LEVEL**: `Hg.HhQB` with the next `Ω₁`-point read above the gate. -/
structure HiQB extends HhQB where
  Pn_lt : ∀ {x}, InE x → x < Om1 → γ < x → hdNx x (P x) < gq 1 x
  Pn_pi : ∀ {σ ρ}, Bases σ ρ → γ < σ → hdNx ρ (P ρ) ∈ TB ρ σ ∧ pi σ ρ (hdNx ρ (P ρ)) = hdNx σ (P σ)
  Qn_mem : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → γ < b → hdNx Om1 Q ∈ S.CSet a b
  Qn_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z {gcG 0} (hdNx Om1 Q) → γ < Z

namespace HiQB

variable (B : HiQB)

theorem mx {γ α x : Ordinal.{0}} (hγ : γ < x) (hα : α < x) : max γ α < x := max_lt hγ hα

theorem Zo_fix1 (x : Ordinal.{0}) : veblen 1 (B.Zo x) = B.Zo x := hc_fix_down one_le_two (B.Zo_fix x)

theorem Q_fixk (k : ℕ) : veblen (k : Ordinal.{0}) B.Q = B.Q := B.Q_fix k ((natCast_lt_omega0 k).trans
  (omega0_lt_inE gl_Om1_E))

theorem Q_fixω : veblen ω B.Q = B.Q := B.Q_fix ω (omega0_lt_inE gl_Om1_E)

theorem Q_E : InE B.Q := by have := B.Q_fixk 0; rwa [Nat.cast_zero, veblen_zero_apply] at this

/-- `φ(β, Q+1) < Γ_{Ω₁+2}` for every `β < Ω₁`. -/
theorem veb_lt1 {β : Ordinal.{0}} (h : β < Om1) : veblen β (B.Q + 1) < gcG 1 := by
  have hG1 := gcG_SC 1
  have hE := Low.opow_eq_self_of_SC hG1
  have hfix : veblen β (gcG 1) = gcG 1 := gn_veb_fix hG1 ((hgf_om h).trans (gcG_Om1_lt 1))
  have h2 := (isNormal_veblen β).strictMono ((ev_isSuccLimit_of_inE hE).add_one_lt B.Q_lt1)
  rwa [hfix] at h2

/-- **`N_α(Q) = φ(α+1, Q+1)`**, `α < Ω₁`. -/
theorem N_eq {α : Ordinal.{0}} (h : α < Om1) : hcN α B.Q = veblen (α + 1) (B.Q + 1) := by
  have := hcN_veb α B.Q; rwa [B.Q_fix _ (gl_Om1_lim.add_one_lt h)] at this

theorem S_eq : hcS B.Q = veblen ω (B.Q + 1) := by
  have := hcS_veb_eq B.Q; rwa [B.Q_fixω] at this

theorem S_lt_Nw : hcS B.Q < hcNw B.Q := hdS_lt_Nw (hcNw_gt _)

/-- **A code `φ(β, Q+1)` over `Z` (`1 ≤ β < Ω₁`) has `β < Z`.** -/
theorem cl_lev {β : Ordinal.{0}} (h1 : 1 ≤ β) (hβ1 : β < Om1) {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1)
    (h : GxCl Z {gcG 0} (veblen β (B.Q + 1))) : β < Z :=
  he_cl_level h1 (hgf_om hβ1) hZ hZ1 (hd_succ_lt (Order.one_le_iff_ne_zero.1 h1) _)
    (B.G_lt.trans ((lt_add_one _).trans_le (right_le_veblen β _))) h le_rfl
    ((isNormal_veblen β).strictMono (lt_add_one _))

/-- **A code `Q` over `Z` forces the gate below `Z`.** -/
theorem Q_gate {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (h : GxCl Z {gcG 0} B.Q) : B.γ < Z :=
  B.Q_cl 0 gv_Om1_pos Z hZ hZ1 B.Q h le_rfl (hcN_gt 0 B.Q)

/-- **A code `φ(β, Q+1)` over `Z` (`1 ≤ β < Ω₁`) forces `max(γ, β) < Z`.** -/
theorem cl_levG {β : Ordinal.{0}} (h1 : 1 ≤ β) (hβ1 : β < Om1) {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1)
    (h : GxCl Z {gcG 0} (veblen β (B.Q + 1))) : max B.γ β < Z :=
  max_lt (B.Q_gate hZ hZ1 (hd_cl_succ_fix h1 hZ hZ1 B.G_lt.le h)) (B.cl_lev h1 hβ1 hZ hZ1 h)

theorem Q_mem' (S : InaccSeq.{0}) {a b : Ordinal.{0}} (ha : 0 < a) (hb : B.γ < b) : B.Q ∈ S.CSet a b :=
  B.Q_mem S ha hb

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : B.γ < x)
include hx hx1 hγ

theorem P_fixL {α : Ordinal.{0}} (h : α < x) : veblen α (B.P x) = B.P x :=
  B.P_fix α (h.trans hx1) hx hx1 (max_lt hγ h)

theorem P_gtL : x < B.P x := B.P_gt 0 gv_Om1_pos hx hx1 (max_lt hγ hx.pos)

theorem P_ltL : B.P x < gq 1 x := (hdNx_gt x (B.P x)).trans (B.Pn_lt hx hx1 hγ)

theorem P_TL : B.P x ∈ Tset x ∧ B.P x < Om1 := gm1_T hx hx1 (B.P_ltL hx hx1 hγ)

theorem P_fixω : veblen ω (B.P x) = B.P x := B.P_fixL hx hx1 hγ (omega0_lt_inE hx)

theorem P_fixk (k : ℕ) : veblen (k : Ordinal.{0}) (B.P x) = B.P x :=
  B.P_fixL hx hx1 hγ ((natCast_lt_omega0 k).trans (omega0_lt_inE hx))

/-- **`N_α(P(x)) = φ(α+1, P(x)+1) = ϑˣ(Ω₁·(α+1) + P(x))`** for `α + 1 < x`. -/
theorem NP_glA {α : Ordinal.{0}} (h : α + 1 < x) :
    hcN α (B.P x) = veblen (α + 1) (B.P x + 1) ∧ hcN α (B.P x) = glA (α + 1) (B.P x) x := by
  have hfix : veblen (α + 1) (B.P x) = B.P x := B.P_fixL hx hx1 hγ h
  have e : hcN α (B.P x) = veblen (α + 1) (B.P x + 1) := by
    have := hcN_veb α (B.P x); rwa [hfix] at this
  refine ⟨e, ?_⟩
  rw [e, hc_glA_fixG hx hx1 le_add_self (h.trans (gm1_facts hx hx1).2.1) hfix
    (h.trans (B.P_gtL hx hx1 hγ)) (B.P_gtL hx hx1 hγ) (B.P_ltL hx hx1 hγ)]

/-- **`N_α(P(x)) < Z_o(x)`** for `α < x`. -/
theorem N_lt_Zo {α : Ordinal.{0}} (h : α < x) : hcN α (B.P x) < B.Zo x :=
  B.N_Zo α (h.trans hx1) hx hx1 (max_lt hγ h)

/-- **`hcS(P(x)) < Z_o(x)`.** -/
theorem S_lt_Zo : hcS (B.P x) < B.Zo x :=
  (hdS_lt_Nw (hcNw_gt _)).trans (B.N_lt_Zo hx hx1 hγ (omega0_lt_inE hx))

/-- **`hcS(P(x)) = ϑˣ(Ω₁·ω + P(x))`.** -/
theorem S_glA : hcS (B.P x) = glA ω (B.P x) x := by
  rw [← hdNx_om, hfm_glA_fixP ⟨le_rfl, omega0_lt_inE gl_Om1_E⟩ hx hx1 (omega0_lt_inE hx) (B.P_fixω hx hx1 hγ)
    (B.P_gtL hx hx1 hγ) (B.P_ltL hx hx1 hγ)]

/-- **`ϑˣ(Ω₁·α + P(x)) = φ(α, P(x)+1)`** for `1 ≤ α < x`. -/
theorem glA_P {α : Ordinal.{0}} (h1 : 1 ≤ α) (h : α < x) : glA α (B.P x) x = veblen α (B.P x + 1) :=
  hc_glA_fixG hx hx1 h1 (h.trans (gm1_facts hx hx1).2.1) (B.P_fixL hx hx1 hγ h) (h.trans (B.P_gtL hx hx1 hγ))
    (B.P_gtL hx hx1 hγ) (B.P_ltL hx hx1 hγ)

/-- **`φ(β, P(x)+1) < Z_o(x)`** for `β < x`. -/
theorem veb_lt_Zo {β : Ordinal.{0}} (h : β < x) : veblen β (B.P x + 1) < B.Zo x :=
  hc_next_lt_N.trans (B.N_lt_Zo hx hx1 hγ h)

theorem evN_lt_Zo {β : Ordinal.{0}} (h : β < x) : evZ (hcN β (B.P x)) < B.Zo x :=
  hb_evZ_lt_fix2 (B.Zo_fix x) (B.N_lt_Zo hx hx1 hγ h)

end Base

/-- **Lemma EXACT for `N_α(P(ρ))`**, `α + 1 < σ`, `γ < σ`. -/
theorem NP_pi {α σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hγ : B.γ < σ) (h : α + 1 < σ) :
    hcN α (B.P ρ) ∈ TB ρ σ ∧ pi σ ρ (hcN α (B.P ρ)) = hcN α (B.P σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hγρ : B.γ < ρ := hγ.trans hB.2.2.1
  obtain ⟨f1, f2⟩ := B.P_pi 0 gv_Om1_pos hB (max_lt hγ hB.1.pos)
  have hh := glA_pi hB (mem_TB_of_lt hB h) (h.trans hσ1) f1 (B.P_TL hB.2.1 hρ1 hγρ).2
  rw [pi_lt hB h, f2, ← (B.NP_glA hB.2.1 hρ1 hγρ (h.trans hB.2.2.1)).2, ← (B.NP_glA hB.1 hσ1 hγ h).2] at hh
  exact hh

/-- **Lemma EXACT for `hcS(P(ρ))`**, `γ < σ`. -/
theorem S_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hγ : B.γ < σ) :
    hcS (B.P ρ) ∈ TB ρ σ ∧ pi σ ρ (hcS (B.P ρ)) = hcS (B.P σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hγρ : B.γ < ρ := hγ.trans hB.2.2.1
  have hωσ : ω < σ := omega0_lt_inE hB.1
  obtain ⟨f1, f2⟩ := B.P_pi 0 gv_Om1_pos hB (max_lt hγ hB.1.pos)
  have hh := glA_pi hB (mem_TB_of_lt hB hωσ) (hωσ.trans hσ1) f1 (B.P_TL hB.2.1 hρ1 hγρ).2
  rw [pi_lt hB hωσ, f2, ← B.S_glA hB.2.1 hρ1 hγρ, ← B.S_glA hB.1 hσ1 hγ] at hh
  exact hh

/-- **Lemma EXACT for `φ(β, P(ρ)+1) = ϑᵖ(Ω₁·β + P(ρ))`**, every level `1 ≤ β < σ`, `γ < σ`. -/
theorem vebP_pi {β σ ρ : Ordinal.{0}} (h1 : 1 ≤ β) (hβσ : β < σ) (hB : Bases σ ρ) (hγ : B.γ < σ) :
    veblen β (B.P ρ + 1) ∈ TB ρ σ ∧ pi σ ρ (veblen β (B.P ρ + 1)) = veblen β (B.P σ + 1) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hγρ : B.γ < ρ := hγ.trans hB.2.2.1
  obtain ⟨g1, g2⟩ := B.P_pi 0 gv_Om1_pos hB (max_lt hγ hB.1.pos)
  have h := glA_pi hB (mem_TB_of_lt hB hβσ) (hβσ.trans hσ1) g1 (B.P_TL hB.2.1 hρ1 hγρ).2
  rw [pi_lt hB hβσ, g2, B.glA_P hB.2.1 hρ1 hγρ h1 (hβσ.trans hB.2.2.1), B.glA_P hB.1 hσ1 hγ h1 hβσ] at h
  exact h

theorem hdNx_lt1 : hcS B.Q < gcG 1 := by rw [B.S_eq]; exact B.veb_lt1 (omega0_lt_inE gl_Om1_E)

theorem Nw_eq : hcNw B.Q = veblen (ω + 1) (B.Q + 1) := B.N_eq (omega0_lt_inE gl_Om1_E)

/-- **`Q` AS A GATED LEVEL-`ω` PSEUDO-BASE** (gate `γ`, outer low field `Z_o`). -/
noncomputable def toP : HgdP where
  F := B.Q
  Fr := B.P
  γ := B.γ
  Zo := B.Zo
  γ_lt := B.γ_lt
  F_fix := B.Q_fixk
  G_lt := B.G_lt
  S_lt1 := B.hdNx_lt1
  F_mem := fun S _ _ ha hb => B.Q_mem S ha hb
  S_mem := fun S _ _ ha hb => by
    rw [B.S_eq]
    exact CSet.phi_mem (gr_cst_mem ha _ ω (omega0_lt_gamma 1)) (CSet.succ_mem (B.Q_mem S ha hb))
  F_code := fun Z hZ hZ1 y hy hQy hyZ => B.Q_code ω (omega0_lt_inE gl_Om1_E) Z hZ hZ1 y hy hQy
    (hyZ.trans B.S_lt_Nw)
  F_cl := fun Z hZ hZ1 y hy hQy hyZ => B.Q_cl ω (omega0_lt_inE gl_Om1_E) Z hZ hZ1 y hy hQy
    (hyZ.trans B.S_lt_Nw)
  S_cl := fun Z hZ hZ1 h => by
    rw [B.S_eq] at h
    exact B.Q_gate hZ hZ1 (hd_cl_succ_fix hc_one_le_om hZ hZ1 B.G_lt.le h)
  Fr_gt := fun hx hx1 hγ => B.P_gtL hx hx1 hγ
  Fr_fix := fun hx hx1 hγ k => B.P_fixk hx hx1 hγ k
  S_Zo := fun hx hx1 hγ => B.S_lt_Zo hx hx1 hγ
  Zo_fix := B.Zo_fix
  Zo_G1 := fun x hx hx1 => B.Zo_G1 x hx hx1
  Fr_pi := fun hB hγ => B.P_pi 0 gv_Om1_pos hB (max_lt hγ hB.1.pos)
  S_pi := fun hB hγ => B.S_pi hB hγ

/-- **`Q` AS A GATED BASE OF LEVEL `ω`** (gate `γ`, outer low field `Z_o`). -/
noncomputable def toA : HgdA where
  F := B.Q
  Fr := B.P
  γ := B.γ
  Zo := B.Zo
  γ_lt := B.γ_lt
  F_fix := B.Q_fixω
  G_le := B.G_lt.le
  N_lt1 := B.N_lt1 ω (omega0_lt_inE gl_Om1_E)
  F_mem := fun S _ _ ha hb => B.Q_mem S ha hb
  N_mem := fun S _ _ ha hb => by
    rw [B.Nw_eq]
    exact CSet.phi_mem (gr_cst_mem ha _ (ω + 1) hd_om1_lt_gam1) (CSet.succ_mem (B.Q_mem S ha hb))
  F_code := fun Z hZ hZ1 y hy hQy hyZ => B.Q_code ω (omega0_lt_inE gl_Om1_E) Z hZ hZ1 y hy hQy hyZ
  F_cl := fun Z hZ hZ1 y hy hQy hyZ => B.Q_cl ω (omega0_lt_inE gl_Om1_E) Z hZ hZ1 y hy hQy hyZ
  N_cl := fun Z hZ hZ1 h => (max_lt_iff.1 (B.N_cl ω (omega0_lt_inE gl_Om1_E) Z hZ hZ1 h)).1
  Fr_gt := fun hx hx1 hγ => B.P_gtL hx hx1 hγ
  Fr_fix := fun hx hx1 hγ => B.P_fixω hx hx1 hγ
  N_Zo := fun hx hx1 hγ => B.N_lt_Zo hx hx1 hγ (omega0_lt_inE hx)
  Zo_fix := B.Zo_fix
  Zo_G1 := fun x hx hx1 => B.Zo_G1 x hx hx1
  Fr_pi := fun hB hγ => B.P_pi 0 gv_Om1_pos hB (max_lt hγ hB.1.pos)
  N_pi := fun hB hγ => B.NP_pi hB hγ (hd_om1_lt_E hB.1)

end HiQB

/-! ## The `ω`-step and the level `ω` over a gated `Q` -/

/-- **A start of the stage at a gated `Q`**: a system `U` with `U.ix = Q`, base gate below `x` iff `γ` is, base reading
`P(x)` and bound field `evZ(P(x))` above `γ`, `Z_o(x)` below. -/
abbrev HiQStart (B : HiQB) (U : HgVD) : Prop := HgSStart (hgdPB B.toP) U

section Om

variable (B : HiQB) (U : HgVD) (hU : HiQStart B U)

/-- **THE `ω`-STEP AT A GATED `Q`**: the system at `φ(ω, Q+1)`. -/
noncomputable def hiQW : HgVD := hgdStep B.toP U hU

theorem hiQW_spec : HgdSpec B.toP U (hiQW B U hU) := hgdStep_spec B.toP U hU

/-- **The `ω`-step at `Q` starts the gated offset recursion over `Q` at level `ω`.** -/
theorem hiQW_start : HgdLvStart B.toA (hiQW B U hU) where
  B := by rw [add_zero, (hiQW_spec B U hU).B]; exact B.S_eq
  Zb := fun x hx hx1 => by
    rw [(hiQW_spec B U hU).Z x hx hx1]
    show (if B.γ < x then evZ (hcS (B.P x)) else B.Zo x) ≤ B.toA.Zl x
    by_cases h : B.γ < x
    · rw [if_pos h, HgdA.Zl_eq _ h]
      exact (hb_evZ_lt_fix2 (hdNw_fix2 _) (hdS_lt_Nw (hcNw_gt _))).le
    · rw [if_neg h, HgdA.Zl_low _ h]; rfl
  st := fun h2 hZ => {
    ix := by
      show (hiQW B U hU).ix = veblen ω (B.Q + 1 + 0)
      rw [add_zero, ← B.S_eq]; rfl
    γ := fun x hx _ => by
      show (hiQW B U hU).γ < x ↔ max B.γ ((hiQW B U hU).g 0) < x
      rw [(hiQW B U hU).g_zero, max_eq_left zero_le, (hiQW_spec B U hU).γ]; rfl
    b := fun x hx hx1 hg => by
      have hγ : B.γ < x := by
        have : max B.γ ((hiQW B U hU).g 0) < x := hg
        rwa [(hiQW B U hU).g_zero, max_eq_left zero_le] at this
      show (hiQW B U hU).b x = glA ω (B.P x + (hiQW B U hU).R 0 x) x
      rw [(hiQW B U hU).R_zero, add_zero, (hiQW_spec B U hU).b x hx hx1 hγ]; exact B.S_glA hx hx1 hγ
    Z := fun x hx hx1 => by
      unfold HgPB.Zst
      show (hiQW B U hU).Z x = if max B.γ ((hiQW B U hU).g 0) < x then
        evZ (glA ω (B.P x + (hiQW B U hU).R 0 x) x) else B.toA.Zl x
      rw [(hiQW B U hU).g_zero, max_eq_left zero_le, (hiQW B U hU).R_zero, add_zero,
        (hiQW_spec B U hU).Z x hx hx1]
      show (if B.γ < x then evZ (hcS (B.P x)) else B.Zo x) = _
      by_cases h : B.γ < x
      · rw [if_pos h, if_pos h, B.S_glA hx hx1 h]
      · rw [if_neg h, if_neg h, HgdA.Zl_low _ h]; rfl }
  high0 := fun c σ hFc hc hσ hσ1 hg => by
    have h := (hiQW_spec B U hU).high c σ hFc (by rw [← (hiQW_spec B U hU).B]; exact hc) hσ hσ1 hg
    exact h

/-- **THE SYSTEM AT `φ(ω+1, Q+1)` OVER A GATED `Q`**: the union of all gated offsets over `Q` at level `ω`. -/
noncomputable def hiQT : HgVD := hgdLvTU (hiQW_start B U hU)

theorem hiQT_B : (hiQT B U hU).B = hcNw B.Q := rfl

theorem hiQT_γ : (hiQT B U hU).γ = B.γ := rfl

theorem hiQT_b (x : Ordinal.{0}) : (hiQT B U hU).b x = hcNw (B.P x) := rfl

/-- **A code `c ∈ [Q, φ(ω+1, Q+1))` of `hiQT` with gate below `σ` forces `γ < σ`.** -/
theorem hiQT_high {c σ : Ordinal.{0}} (hc : c < (hiQT B U hU).B) (hFc : B.Q ≤ c) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : (hiQT B U hU).g c < σ) : B.γ < σ :=
  hgdLvTU_high (hiQW_start B U hU) hc hFc hσ hσ1 hg

end Om

end Googology.Trans.PoR.InaccPsi.R2.Hi
