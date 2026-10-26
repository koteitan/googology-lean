import Googology.Trans.PoR.InaccPsi.R2.HgfCh
import Googology.Trans.PoR.InaccPsi.R2.HgLoc

/-!
# HgQ: AN ABSTRACT BASE `Q` OF EVERY COUNTABLE LEVEL; THE `ω`-STEP AND THE LEVEL `ω` OVER IT

`G` was the only base of the level recursion (`Hd.hdGA`, `Hf.hfGB`), and its readings `Γ_{x+1}` lie below `B_x(x)`.
An abstract base (`HgQB`) is a point `Q` (`G < Q < Γ_{Ω₁+2}`, a fixed point of every `φ(α, ·)`, `α < Ω₁`, a code
over every strongly critical `Z ≤ Ω₁`, in every hull) with a reading `P(x)` (a fixed point of every `φ(α, ·)`,
`α < x`, above `x`, `hdNx x (P x) < Γ_{x+2}`, Lemma EXACT for `P(ρ)` and for `hdNx ρ (P ρ)`).  Its readings may pass
`B_x(x)`; the systems over it are `Hg.HgVD` (bound field `< Γ_{x+2}`).  Its outer low field is
`Z_o(x) = hdNx x (P x)` (the reading of the next `Ω₁`-point, read with `Ω₁ ↦ x`).

* `hgRegate`, `hgRegateQ` (**RAISING THE BASE GATE OF AN `HgVD`**, a level `α` over `Q`; `He.heRegateG` for `G`);
* `HgQB`, `HgQB.Zo`, the facts (`Q_fixk`, `N_eq`, `N_lt1`, `NP_eq`, `NP_glA`, `NP_pi`, `S_pi`, `cl_lev`);
* `HgQB.toP` (**`Q` AS A LEVEL-`ω` PSEUDO-BASE**), `HgQB.toA` (**`Q` AS A BASE OF LEVEL `ω`**),
  `HgQB.toB α` (**`Q` AS A BASE OF EVERY COUNTABLE LEVEL `α`, TWO GATES**: code gate `0`, reading gate `α`);
* `HgQStart` (a start of the stage at `Q`), `hgQW` (**THE `ω`-STEP AT `Q`**: bound `φ(ω, Q+1)`), `hgQW_start`
  (**it starts the gated offset recursion over `Q` at level `ω`**), `hgQT` (**THE SYSTEM AT `φ(ω+1, Q+1)`**).

No new axiom.  New definitions: `hgRegate`, `hgRegateQ`, `HgQB`, `HgQB.Zo`, `HgQB.toP`, `HgQB.toA`, `HgQB.toB`,
`HgQStart`, `hgQW`, `hgQT`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hg

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

/-! ## Raising the base gate of an `HgVD` -/

/-- **RAISING THE BASE GATE** of an `HgVD` (the copy of `He.heRegate`). -/
noncomputable def hgRegate (T : HgVD) (γ' : Ordinal.{0}) (h1 : T.γ ≤ γ') (h2 : γ' < Om1)
    (h3 : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z {gcG 0} T.B → γ' < Z) (h4 : T.B = gcG 0 → γ' = 0) :
    HgVD :=
  { T with
    γ := γ'
    γ_lt := h2
    γ_cl := h3
    γ_G := h4
    ix_mem := fun S a b ha hb => T.ix_mem S a b ha (h1.trans_lt hb)
    R_lt_b := fun x hx hx1 hγ => T.R_lt_b x hx hx1 (h1.trans_lt hγ)
    b_cof := fun x hx hx1 hγ => T.b_cof x hx hx1 (h1.trans_lt hγ)
    b_E := fun x hx hx1 hγ => T.b_E x hx hx1 (h1.trans_lt hγ)
    x_lt_b := fun x hx hx1 hγ => T.x_lt_b x hx hx1 (h1.trans_lt hγ)
    b_eN := fun x hx hx1 hγ => T.b_eN x hx hx1 (h1.trans_lt hγ)
    ba_lt := fun x hx hx1 hγ => T.ba_lt x hx hx1 (h1.trans_lt hγ)
    b_Z := fun x hx hx1 hγ => T.b_Z x hx hx1 (h1.trans_lt hγ)
    b_pi := fun σ ρ hB hγ => T.b_pi σ ρ hB (h1.trans_lt hγ)
    ba_pi := fun σ ρ hB hγ => T.ba_pi σ ρ hB (h1.trans_lt hγ)
    dig := fun σ ρ hB hγ => T.dig σ ρ hB (h1.trans_lt hγ) }

/-- **THE GATE OF A LEVEL `α` OVER `Q`**: a system with bound `φ(α, Q+1)` (`G < Q`, `1 ≤ α < Ω₁`, base gate `≤ α`)
gets the base gate `α` (`He.he_cl_level`: a code of `φ(α, Q+1)` over `Z` has `α < Z`). -/
noncomputable def hgRegateQ (T : HgVD) {Q α : Ordinal.{0}} (hGQ : gcG 0 < Q) (hα : 1 ≤ α) (hα1 : α < Om1)
    (hB : T.B = veblen α (Q + 1)) (hγ : T.γ ≤ α) : HgVD :=
  hgRegate T α hγ hα1
    (fun Z hZ hZ1 hc => by
      have hα1' : α < Om 1 := by rw [← Br.Om1_eq]; exact hα1
      have hα0 : α ≠ 0 := Order.one_le_iff_ne_zero.1 hα
      rw [hB] at hc
      exact he_cl_level hα hα1' hZ hZ1 (hd_succ_lt hα0 _)
        (hGQ.trans ((lt_add_one _).trans_le (right_le_veblen α _))) hc le_rfl
        ((isNormal_veblen α).strictMono (lt_add_one _)))
    (fun e => by
      exfalso
      rw [hB] at e
      have : gcG 0 < veblen α (Q + 1) := hGQ.trans ((lt_add_one _).trans_le (right_le_veblen α _))
      rw [e] at this; exact lt_irrefl _ this)

theorem hgRegateQ_γ (T : HgVD) {Q α : Ordinal.{0}} (hGQ : gcG 0 < Q) (hα : 1 ≤ α) (hα1 : α < Om1)
    (hB : T.B = veblen α (Q + 1)) (hγ : T.γ ≤ α) : (hgRegateQ T hGQ hα hα1 hB hγ).γ = α := rfl

/-! ## An abstract base of every countable level -/

/-- **AN ABSTRACT BASE OF EVERY COUNTABLE LEVEL**, base gate `0`. -/
structure HgQB where
  Q : Ordinal.{0}
  P : Ordinal.{0} → Ordinal.{0}
  Q_fix : ∀ α, α < Om1 → veblen α Q = Q
  G_lt : gcG 0 < Q
  Q_lt1 : Q < gcG 1
  Q_mem : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → Q ∈ S.CSet a b
  Q_code : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z {gcG 0} Q
  P_fix : ∀ {x}, InE x → x < Om1 → ∀ α, α < x → veblen α (P x) = P x
  P_gt : ∀ {x}, InE x → x < Om1 → x < P x
  Pn_lt : ∀ {x}, InE x → x < Om1 → hdNx x (P x) < gq 1 x
  P_pi : ∀ {σ ρ}, Bases σ ρ → P ρ ∈ TB ρ σ ∧ pi σ ρ (P ρ) = P σ
  Pn_pi : ∀ {σ ρ}, Bases σ ρ → hdNx ρ (P ρ) ∈ TB ρ σ ∧ pi σ ρ (hdNx ρ (P ρ)) = hdNx σ (P σ)
  Qn_mem : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → hdNx Om1 Q ∈ S.CSet a b

namespace HgQB

variable (B : HgQB)

/-- **The outer low field**: `hdNx x (P x)` (at `ε`-number bases). -/
noncomputable def Zo (x : Ordinal.{0}) : Ordinal.{0} := hdNx (max ω x) (B.P x)

theorem Zo_fix (x : Ordinal.{0}) : veblen 2 (B.Zo x) = B.Zo x :=
  hdNx_fix (gw_two_lt_w.trans_le (le_max_left ω x)) _

theorem Zo_fix1 (x : Ordinal.{0}) : veblen 1 (B.Zo x) = B.Zo x :=
  hdNx_fix (one_lt_omega0.trans_le (le_max_left ω x)) _

theorem Zo_eq {x : Ordinal.{0}} (hx : InE x) : B.Zo x = hdNx x (B.P x) := by
  unfold HgQB.Zo; rw [max_eq_right (omega0_lt_inE hx).le]

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

theorem N_lt1 {α : Ordinal.{0}} (h : α < Om1) : hcN α B.Q < gcG 1 := by
  rw [B.N_eq h]; exact B.veb_lt1 (gl_Om1_lim.add_one_lt h)

theorem S_eq : hcS B.Q = veblen ω (B.Q + 1) := by
  have := hcS_veb_eq B.Q; rwa [B.Q_fixω] at this

theorem N_mem (S : InaccSeq.{0}) {α a b : Ordinal.{0}} (h : α < Om1) (ha : 0 < a) (hb : α < b) :
    hcN α B.Q ∈ S.CSet a b := by
  rw [B.N_eq h]
  exact CSet.phi_mem (CSet.succ_mem (he_cst_mem S le_rfl hb)) (CSet.succ_mem (B.Q_mem S ha))

/-- **A code `φ(β, Q+1)` over `Z` (`1 ≤ β < Ω₁`) has `β < Z`.** -/
theorem cl_lev {β : Ordinal.{0}} (h1 : 1 ≤ β) (hβ1 : β < Om1) {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1)
    (h : GxCl Z {gcG 0} (veblen β (B.Q + 1))) : β < Z :=
  he_cl_level h1 (hgf_om hβ1) hZ hZ1 (hd_succ_lt (Order.one_le_iff_ne_zero.1 h1) _)
    (B.G_lt.trans ((lt_add_one _).trans_le (right_le_veblen β _))) h le_rfl
    ((isNormal_veblen β).strictMono (lt_add_one _))

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem P_lt : B.P x < gq 1 x := (hdNx_gt x (B.P x)).trans (B.Pn_lt hx hx1)

theorem Zo_lt1 : B.Zo x < gq 1 x := by rw [B.Zo_eq hx]; exact B.Pn_lt hx hx1

theorem P_T : B.P x ∈ Tset x ∧ B.P x < Om1 := gm1_T hx hx1 (B.P_lt hx hx1)

theorem P_fixω : veblen ω (B.P x) = B.P x := B.P_fix hx hx1 ω (omega0_lt_inE hx)

theorem P_fixk (k : ℕ) : veblen (k : Ordinal.{0}) (B.P x) = B.P x :=
  B.P_fix hx hx1 k ((natCast_lt_omega0 k).trans (omega0_lt_inE hx))

/-- **`N_α(P(x)) = φ(α+1, P(x)+1) = ϑˣ(Ω₁·(α+1) + P(x))`** for `α + 1 < x`. -/
theorem NP_glA {α : Ordinal.{0}} (h : α + 1 < x) :
    hcN α (B.P x) = veblen (α + 1) (B.P x + 1) ∧ hcN α (B.P x) = glA (α + 1) (B.P x) x := by
  have hq := (gm1_facts hx hx1).2.2.2
  have hfix : veblen (α + 1) (B.P x) = B.P x := B.P_fix hx hx1 _ h
  have e : hcN α (B.P x) = veblen (α + 1) (B.P x + 1) := by
    have := hcN_veb α (B.P x); rwa [hfix] at this
  refine ⟨e, ?_⟩
  rw [e, hc_glA_fixG hx hx1 le_add_self (h.trans (gm1_facts hx hx1).2.1) hfix (h.trans (B.P_gt hx hx1))
    (B.P_gt hx hx1) (B.P_lt hx hx1)]

/-- **`N_α(P(x)) < Z_o(x)`** for `α < x`. -/
theorem N_lt_Zo {α : Ordinal.{0}} (h : α < x) : hcN α (B.P x) < B.Zo x := by
  rw [B.Zo_eq hx]; exact hdN_lt_Nx ((ev_isSuccLimit_of_inE hx).add_one_lt h)

/-- **`hcS(P(x)) < Z_o(x)`.** -/
theorem S_lt_Zo : hcS (B.P x) < B.Zo x :=
  (hdS_lt_Nw (hcNw_gt _)).trans (B.N_lt_Zo hx hx1 (omega0_lt_inE hx))

/-- **`hcS(P(x)) = ϑˣ(Ω₁·ω + P(x))`.** -/
theorem S_glA : hcS (B.P x) = glA ω (B.P x) x := by
  rw [← hdNx_om, hfm_glA_fixP ⟨le_rfl, omega0_lt_inE gl_Om1_E⟩ hx hx1 (omega0_lt_inE hx) (B.P_fixω hx hx1)
    (B.P_gt hx hx1) (B.P_lt hx hx1)]

end Base

/-- **Lemma EXACT for `N_α(P(ρ))`**, `α + 1 < σ`. -/
theorem NP_pi {α σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (h : α + 1 < σ) :
    hcN α (B.P ρ) ∈ TB ρ σ ∧ pi σ ρ (hcN α (B.P ρ)) = hcN α (B.P σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨f1, f2⟩ := B.P_pi hB
  have hh := glA_pi hB (mem_TB_of_lt hB h) (h.trans hσ1) f1 (B.P_T hB.2.1 hρ1).2
  rw [pi_lt hB h, f2, ← (B.NP_glA hB.2.1 hρ1 (h.trans hB.2.2.1)).2, ← (B.NP_glA hB.1 hσ1 h).2] at hh
  exact hh

/-- **Lemma EXACT for `hcS(P(ρ))`.** -/
theorem S_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) :
    hcS (B.P ρ) ∈ TB ρ σ ∧ pi σ ρ (hcS (B.P ρ)) = hcS (B.P σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hωσ : ω < σ := omega0_lt_inE hB.1
  obtain ⟨f1, f2⟩ := B.P_pi hB
  have hh := glA_pi hB (mem_TB_of_lt hB hωσ) (hωσ.trans hσ1) f1 (B.P_T hB.2.1 hρ1).2
  rw [pi_lt hB hωσ, f2, ← B.S_glA hB.2.1 hρ1, ← B.S_glA hB.1 hσ1] at hh
  exact hh

theorem hdNx_lt1 : hcS B.Q < gcG 1 := by rw [B.S_eq]; exact B.veb_lt1 (omega0_lt_inE gl_Om1_E)

/-- **`Q` AS A LEVEL-`ω` PSEUDO-BASE** (gate `0`, outer low field `Z_o`). -/
noncomputable def toP : HgdP where
  F := B.Q
  Fr := B.P
  γ := 0
  Zo := B.Zo
  γ_lt := gv_Om1_pos
  F_fix := B.Q_fixk
  G_lt := B.G_lt
  S_lt1 := B.hdNx_lt1
  F_mem := fun S _ _ ha _ => B.Q_mem S ha
  S_mem := fun S _ _ ha _ => by
    rw [B.S_eq]
    exact CSet.phi_mem (gr_cst_mem ha _ ω (omega0_lt_gamma 1)) (CSet.succ_mem (B.Q_mem S ha))
  F_code := fun Z hZ hZ1 _ _ _ _ => B.Q_code Z hZ hZ1
  F_cl := fun _ hZ _ _ _ _ _ => hZ.1
  S_cl := fun _ hZ _ _ => hZ.1
  Fr_gt := fun hx hx1 _ => B.P_gt hx hx1
  Fr_fix := fun hx hx1 _ k => B.P_fixk hx hx1 k
  S_Zo := fun hx hx1 _ => B.S_lt_Zo hx hx1
  Zo_fix := B.Zo_fix
  Zo_G1 := fun _ hx hx1 => B.Zo_lt1 hx hx1
  Fr_pi := fun hB _ => B.P_pi hB
  S_pi := fun hB _ => B.S_pi hB

theorem Nw_eq : hcNw B.Q = veblen (ω + 1) (B.Q + 1) := B.N_eq (omega0_lt_inE gl_Om1_E)

/-- **`Q` AS A BASE OF LEVEL `ω`** (gate `0`, outer low field `Z_o`). -/
noncomputable def toA : HgdA where
  F := B.Q
  Fr := B.P
  γ := 0
  Zo := B.Zo
  γ_lt := gv_Om1_pos
  F_fix := B.Q_fixω
  G_le := B.G_lt.le
  N_lt1 := B.N_lt1 (omega0_lt_inE gl_Om1_E)
  F_mem := fun S _ _ ha _ => B.Q_mem S ha
  N_mem := fun S _ _ ha _ => by
    rw [B.Nw_eq]
    exact CSet.phi_mem (gr_cst_mem ha _ (ω + 1) hd_om1_lt_gam1) (CSet.succ_mem (B.Q_mem S ha))
  F_code := fun Z hZ hZ1 _ _ _ _ => B.Q_code Z hZ hZ1
  F_cl := fun _ hZ _ _ _ _ _ => hZ.1
  N_cl := fun _ hZ _ _ => hZ.1
  Fr_gt := fun hx hx1 _ => B.P_gt hx hx1
  Fr_fix := fun hx hx1 _ => B.P_fixω hx hx1
  N_Zo := fun hx hx1 _ => B.N_lt_Zo hx hx1 (omega0_lt_inE hx)
  Zo_fix := B.Zo_fix
  Zo_G1 := fun _ hx hx1 => B.Zo_lt1 hx hx1
  Fr_pi := fun hB _ => B.P_pi hB
  N_pi := fun hB _ => B.NP_pi hB (hd_om1_lt_E hB.1)

/-- **`Q` AS A BASE OF EVERY COUNTABLE LEVEL `α`, WITH TWO GATES**: code gate `0`, reading gate `α`. -/
noncomputable def toB (α : Ordinal.{0}) (hα : HfLvl α) : HgfB α where
  F := B.Q
  Fr := B.P
  γ := 0
  γN := α
  Zo := B.Zo
  lv := hα
  γ_le := zero_le
  lvN := le_rfl
  γN_lt := hα.2
  F_fix := B.Q_fix α hα.2
  G_le := B.G_lt.le
  N_lt1 := B.N_lt1 hα.2
  F_mem := fun S _ _ ha _ => B.Q_mem S ha
  N_mem := fun S _ _ ha hb => B.N_mem S hα.2 ha hb
  F_code := fun Z hZ hZ1 _ _ _ _ => B.Q_code Z hZ hZ1
  F_cl := fun _ hZ _ _ _ _ _ => hZ.1
  N_cl := fun _ hZ hZ1 h => by
    rw [B.N_eq hα.2] at h
    exact (lt_add_one α).trans (B.cl_lev le_add_self (gl_Om1_lim.add_one_lt hα.2) hZ hZ1 h)
  γN_cl := fun _ _ _ _ h => h
  Fr_gt := fun hx hx1 _ => B.P_gt hx hx1
  Fr_fix := fun hx hx1 h => B.P_fix hx hx1 α h
  N_Zo := fun hx hx1 h => B.N_lt_Zo hx hx1 h
  Zo_fix := B.Zo_fix
  Zo_G1 := fun _ hx hx1 => B.Zo_lt1 hx hx1
  Fr_pi := fun hB _ => B.P_pi hB
  N_pi := fun hB h => B.NP_pi hB ((ev_isSuccLimit_of_inE hB.1).add_one_lt h)

end HgQB

/-! ## The `ω`-step and the level `ω` over `Q` -/

/-- **A start of the stage at `Q`**: a system `U` (base gate `0`) with `U.ix = Q`, base reading `P(x)` and bound
field `evZ(P(x))`. -/
abbrev HgQStart (B : HgQB) (U : HgVD) : Prop := HgSStart (hgdPB B.toP) U

section Om

variable (B : HgQB) (U : HgVD) (hU : HgQStart B U)

/-- **THE `ω`-STEP AT `Q`**: the system at `φ(ω, Q+1)`. -/
noncomputable def hgQW : HgVD := hgdStep B.toP U hU

theorem hgQW_spec : HgdSpec B.toP U (hgQW B U hU) := hgdStep_spec B.toP U hU

/-- **The `ω`-step at `Q` starts the gated offset recursion over `Q` at level `ω`.** -/
theorem hgQW_start : HgdLvStart B.toA (hgQW B U hU) where
  B := by rw [add_zero, (hgQW_spec B U hU).B]; exact B.S_eq
  Zb := fun x hx hx1 => by
    rw [(hgQW_spec B U hU).Z x hx hx1]
    show (if (0 : Ordinal.{0}) < x then evZ (hcS (B.P x)) else B.Zo x) ≤ B.toA.Zl x
    rw [if_pos hx.pos, HgdA.Zl_eq _ hx.pos]
    exact (hb_evZ_lt_fix2 (hdNw_fix2 _) (hdS_lt_Nw (hcNw_gt _))).le
  st := fun h2 hZ => {
    ix := by
      show (hgQW B U hU).ix = veblen ω (B.Q + 1 + 0)
      rw [add_zero, ← B.S_eq]; rfl
    γ := fun x hx _ => by
      show (hgQW B U hU).γ < x ↔ max 0 ((hgQW B U hU).g 0) < x
      rw [(hgQW B U hU).g_zero, max_self, (hgQW_spec B U hU).γ]; rfl
    b := fun x hx hx1 _ => by
      show (hgQW B U hU).b x = glA ω (B.P x + (hgQW B U hU).R 0 x) x
      rw [(hgQW B U hU).R_zero, add_zero, (hgQW_spec B U hU).b x hx hx1 hx.pos]; exact B.S_glA hx hx1
    Z := fun x hx hx1 => by
      unfold HgPB.Zst
      show (hgQW B U hU).Z x = if max 0 ((hgQW B U hU).g 0) < x then
        evZ (glA ω (B.P x + (hgQW B U hU).R 0 x) x) else B.toA.Zl x
      rw [(hgQW B U hU).g_zero, max_self, if_pos hx.pos, (hgQW B U hU).R_zero, add_zero,
        (hgQW_spec B U hU).Z x hx hx1]
      show (if (0 : Ordinal.{0}) < x then evZ (hcS (B.P x)) else B.Zo x) = _
      rw [if_pos hx.pos, B.S_glA hx hx1] }
  high0 := fun _ _ _ _ hσ _ _ => hσ.pos

/-- **THE SYSTEM AT `φ(ω+1, Q+1)`**: the union of all gated offsets over `Q` at level `ω`. -/
noncomputable def hgQT : HgVD := hgdLvTU (hgQW_start B U hU)

theorem hgQT_B : (hgQT B U hU).B = hcNw B.Q := rfl

theorem hgQT_γ : (hgQT B U hU).γ = 0 := rfl

theorem hgQT_b (x : Ordinal.{0}) : (hgQT B U hU).b x = hcNw (B.P x) := rfl

end Om

end Googology.Trans.PoR.InaccPsi.R2.Hg
