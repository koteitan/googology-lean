import Googology.Trans.PoR.InaccPsi.R2.HiQU

/-!
# HiOff: THE GATED OFFSETS OF THE LEVEL `Ω₁` READ AS `x`: `Q_λ = φ(Ω₁, G+1+λ)`, `λ < N_{Ω₁}(G) = φ(Ω₁+1, G+1)`

`Hg.hgFB ν` is the base `φ(Ω₁, G+1+ν)` for a CONSTANT offset `ν < ε₀` (its reading moves `ν` as a constant, so
`ν < σ` at every base `σ`, the wall `ν = ε₀`).  Here the offset `λ < N_{Ω₁}(G)` is a code read by a system `E`
(an `Hg.HgVD` with `λ < E.B` and bound field below the low field `Z_l(x) = N_x(Γ_{x+1}) = φ(x+1, Γ_{x+1}+1)`), and
the gate is the gate `g_E(λ)` of the code:

* the reading `P_λ(x) = ϑˣ(Ω₁·x + Γ_{x+1} + λ(x))` has the CLOSED FORM `φ(x, Γ_{x+1}+1+λ(x))` below `Z_l(x)`
  (`hi_cf`, from `Hc.hc_glAV` at the level `β = x`: no fixed point of `φ(x, ·)` lies in `(Γ_{x+1}, Z_l(x))`);
* Lemma EXACT for `P_λ(ρ)`, `hdNx ρ (P_λ(ρ)) = P_{λ+1}(ρ)` and `N_α(P_λ(ρ))` above the gate (`hiP_pi`, `hiPn_pi`,
  `hiNP_pi`: `Gl.glA_pi` with `π(ρ) = σ`, the base `Γ_{ρ+1}` and the code `λ` moved by `E`);
* the code-gate conditions of `[Q_λ, hdNx Ω₁ Q_λ)` (a code there forces the code `λ`, hence `g_E(λ) < Z`);
* `hiOff E λ` : `Hi.HiQB` (**THE GATED BASE AT THE OFFSET `λ`**, gate `g_E(λ)`, low field `Z_l`).

No new axiom.  New definitions: `hiN`, `hiZl`, `hiQ`, `hiP`, `hiOff`.
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

/-! ## The bound `N_{Ω₁}(G)` and the points `Q_λ` -/

/-- **`N_{Ω₁}(G) = φ(Ω₁+1, G+1)`**, the least fixed point of `φ(Ω₁, ·)` above `G = Γ_{Ω₁+1}`. -/
noncomputable def hiN : Ordinal.{0} := hcN Om1 (gcG 0)

/-- **`Q_λ = φ(Ω₁, G+1+λ)`.** -/
noncomputable def hiQ (l : Ordinal.{0}) : Ordinal.{0} := veblen Om1 (gcG 0 + 1 + l)

theorem hiN_E : InE hiN := hcN_E _ _

theorem hiN_lim : IsSuccLimit hiN := ev_isSuccLimit_of_inE hiN_E

theorem hiG_lt_N : gcG 0 < hiN := hcN_gt _ _

theorem hiN_fix : veblen Om1 hiN = hiN := hcN_fix _ _

theorem hi_Om1_succ_lt_G : Om1 + 1 < gcG 0 := (ev_isSuccLimit_of_inE gr_G_inE).add_one_lt (hg_Om1_lt_G 0)

/-- **`N_{Ω₁}(G) = φ(Ω₁+1, G+1)`.** -/
theorem hiN_eq : hiN = veblen (Om1 + 1) (gcG 0 + 1) := by
  have hfix : veblen (Om1 + 1) (gcG 0) = gcG 0 := gn_veb_fix (gcG_SC 0) hi_Om1_succ_lt_G
  have := hcN_veb Om1 (gcG 0); rwa [hfix] at this

theorem hiN_lt1 : hiN < gcG 1 := by
  have hG1 := gcG_SC 1
  have hE := Low.opow_eq_self_of_SC hG1
  have hfix : veblen (Om1 + 1) (gcG 1) = gcG 1 :=
    gn_veb_fix hG1 ((ev_isSuccLimit_of_inE hE).add_one_lt (hg_Om1_lt_G 1))
  rw [hiN_eq]
  have h2 := (isNormal_veblen (Om1 + 1)).strictMono ((ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt zero_lt_one))
  rwa [hfix] at h2

theorem hiN_mem (S : InaccSeq.{0}) {a b : Ordinal.{0}} (ha : 0 < a) : hiN ∈ S.CSet a b := by
  rw [hiN_eq, Br.Om1_eq]
  exact CSet.phi_mem (CSet.succ_mem (CSet.Om_mem (CSet.one_mem _ _))) (CSet.succ_mem (gmS_G0_mem S ha))

section Q

variable {l : Ordinal.{0}} (hlN : l < hiN)
include hlN

theorem hi_j_lt_N : gcG 0 + 1 + l < hiN := (inE_indec hiN_E).add_lt (hiN_lim.add_one_lt hiG_lt_N) hlN

theorem hi_j_lt : gcG 0 + 1 + l < veblen Om1 (gcG 0 + 1 + l) := by
  rcases (right_le_veblen Om1 (gcG 0 + 1 + l)).lt_or_eq with h | h
  · exact h
  · exfalso
    have hGj : gcG 0 < gcG 0 + 1 + l := (lt_add_one _).trans_le le_self_add
    exact absurd (hcN_le h.symm hGj) (not_le.2 (hi_j_lt_N hlN))

theorem hi_lt_Q : l < hiQ l := le_add_self.trans_lt (hi_j_lt hlN)

theorem hiQ_lt_N : hiQ l < hiN := by
  have h := (isNormal_veblen Om1).strictMono (hi_j_lt_N hlN)
  rwa [hiN_fix] at h

theorem hiQ1_lt_N : veblen Om1 (gcG 0 + 1 + l + 1) < hiN := by
  have h := (isNormal_veblen Om1).strictMono (hiN_lim.add_one_lt (hi_j_lt_N hlN))
  rwa [hiN_fix] at h

end Q

theorem hiG_lt_Q (l : Ordinal.{0}) : gcG 0 < hiQ l :=
  ((lt_add_one _).trans_le le_self_add).trans_le (right_le_veblen _ _)

theorem hiQ_lt_Q {ν l : Ordinal.{0}} (h : ν < l) : hiQ ν < hiQ l :=
  (isNormal_veblen _).strictMono ((add_lt_add_iff_left _).2 h)

theorem hiQ_le_Q {ν l : Ordinal.{0}} (h : ν ≤ l) : hiQ ν ≤ hiQ l :=
  (isNormal_veblen _).monotone ((add_le_add_iff_left _).2 h)

theorem hiQ_succ (l : Ordinal.{0}) : hdNx Om1 (hiQ l) = hiQ (l + 1) := by
  unfold hiQ; rw [hdNx_veb, ← add_assoc]

theorem hiQ_E (l : Ordinal.{0}) : InE (hiQ l) := gg_veblen_eps gv_Om1_pos.ne'

theorem hiQ_zero : hiQ 0 = hgB := by unfold hiQ hgB; rw [add_zero]

theorem hi_cover {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlN : l < hiN) : ∃ ν, ν < l ∧ l < hiQ ν := by
  have h := hi_lt_Q hlN
  obtain ⟨t, ht, hlt⟩ := ((isNormal_veblen _).lt_iff_exists_lt (isSuccLimit_add _ hl)).1 h
  obtain ⟨d, hf, htd⟩ := (lt_add_iff hl.bot_lt.ne').1 ht
  exact ⟨d, hf, hlt.trans_le ((isNormal_veblen _).monotone htd)⟩

theorem hiQ_cof {l c : Ordinal.{0}} (hl : IsSuccLimit l) (hc : c < hiQ l) : ∃ d, d < l ∧ c < hiQ d := by
  have hlim : IsSuccLimit (gcG 0 + 1 + l) := isSuccLimit_add _ hl
  obtain ⟨t, ht, hct⟩ := ((isNormal_veblen Om1).lt_iff_exists_lt hlim).1 hc
  obtain ⟨d, hf, htd⟩ := (lt_add_iff hl.bot_lt.ne').1 ht
  exact ⟨d, hf, hct.trans_le ((isNormal_veblen Om1).monotone htd)⟩

/-! ## The low field and the closed form at the level `x` -/

/-- **The low field `Z_l(x) = N_x(Γ_{x+1}) = φ(x+1, Γ_{x+1}+1)`** (read with `max(ω, x)` so that it is a fixed point of
`φ(2, ·)` at every `x`). -/
noncomputable def hiZl (x : Ordinal.{0}) : Ordinal.{0} := hcN (max ω x) (lgG x)

theorem hiZl_fix (x : Ordinal.{0}) : veblen 2 (hiZl x) = hiZl x :=
  hc_fix_down ((show (2 : Ordinal.{0}) ≤ ω from (by exact_mod_cast (natCast_lt_omega0 2).le)).trans
    (le_max_left _ _)) (hcN_fix _ _)

theorem hiZl_fix1 (x : Ordinal.{0}) : veblen 1 (hiZl x) = hiZl x := hc_fix_down one_le_two (hiZl_fix x)

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem hi_one_le : (1 : Ordinal.{0}) ≤ x := one_lt_omega0.le.trans (omega0_lt_inE hx).le

theorem hiZl_eq : hiZl x = hcN x (lgG x) := by unfold hiZl; rw [max_eq_right (omega0_lt_inE hx).le]

theorem hi_x1_lt_G : x + 1 < lgG x :=
  (ev_isSuccLimit_of_inE (lgG_facts hx hx1).2.2.2.1).add_one_lt (lgG_facts hx hx1).2.1

/-- **`Z_l(x) = φ(x+1, Γ_{x+1}+1) = ϑˣ(Ω₁·(x+1) + Γ_{x+1})`.** -/
theorem hiZl_glA : hiZl x = glA (x + 1) (lgG x) x := by
  have hfix : veblen (x + 1) (lgG x) = lgG x := hc_G_fix hx hx1 le_add_self (hi_x1_lt_G hx hx1)
  have e : hcN x (lgG x) = veblen (x + 1) (lgG x + 1) := by
    have := hcN_veb x (lgG x); rwa [hfix] at this
  rw [hiZl_eq hx hx1, e, hc_glA_fixG hx hx1 le_add_self ((hi_x1_lt_G hx hx1).trans (mg_lgG_lt_G1 hx hx1)) hfix
    (hi_x1_lt_G hx hx1) (lgG_facts hx hx1).2.1 (mg_lgG_lt_G1 hx hx1)]

/-- **`ϑˣ(Ω₁·β + t) < Γ_{x+2}`** for `β, t < Γ_{x+2}`. -/
theorem hi_glA_lt1 {β t : Ordinal.{0}} (hβ : β < gq 1 x) (ht : t < gq 1 x) : glA β t x < gq 1 x :=
  lgVt_lt_low hx hx1 (gm1_T hx hx1 hβ).1 (gm1_T hx hx1 hβ).2 (gm1_T hx hx1 ht).1 (gm1_T hx hx1 ht).2
    (gm1_one_T hx hx1).1 (gm1_one_T hx hx1).2 hβ ht

theorem hiZl_lt1 : hiZl x < gq 1 x := by
  rw [hiZl_glA hx hx1]
  exact hi_glA_lt1 hx hx1 ((ev_isSuccLimit_of_inE (gm1_facts hx hx1).2.2.2).add_one_lt (gm1_facts hx hx1).2.1)
    (mg_lgG_lt_G1 hx hx1)

theorem hiG_lt_Zl : lgG x < hiZl x := by rw [hiZl_eq hx hx1]; exact hcN_gt _ _

theorem hiZl_E : InE (hiZl x) := hcN_E _ _

theorem hi_j_lt_Zl {r : Ordinal.{0}} (hr : r < hiZl x) : lgG x + 1 + r < hiZl x :=
  (inE_indec (hiZl_E hx hx1)).add_lt ((ev_isSuccLimit_of_inE (hiZl_E hx hx1)).add_one_lt (hiG_lt_Zl hx hx1)) hr

/-- **No fixed point of `φ(x, ·)` lies in `(Γ_{x+1}, Z_l(x))`.** -/
theorem hi_nofix {j : Ordinal.{0}} (hGj : lgG x < j) (hj : j < hiZl x) : j < veblen x j := by
  rcases (right_le_veblen x j).lt_or_eq with h | h
  · exact h
  · exfalso
    have := hcN_le h.symm hGj
    rw [← hiZl_eq hx hx1] at this
    exact absurd hj (not_lt.2 this)

/-- **THE CLOSED FORM AT THE LEVEL `x`**: `ϑˣ(Ω₁·x + Γ_{x+1} + r) = φ(x, Γ_{x+1}+1+r)` for `r < Z_l(x)`
(`Hc.hc_glAV` at `β = x`). -/
theorem hi_cf {r : Ordinal.{0}} (hr : r < hiZl x) : glA x (lgG x + r) x = veblen x (lgG x + 1 + r) := by
  have hq := (gm1_facts hx hx1).2.2.2
  have hxq : x < gq 1 x := (gm1_facts hx hx1).2.1
  have hGq := mg_lgG_lt_G1 hx hx1
  have hG0 := hc_glA_GG hx hx1 (hi_one_le hx hx1) (lgG_facts hx hx1).2.1
  have hjr := hi_j_lt_Zl hx hx1 hr
  have hrq : lgG x + r < gq 1 x :=
    (add_le_add le_self_add le_rfl |>.trans_lt (by rw [add_assoc] at hjr ⊢; exact hjr) |>.trans
      (hiZl_lt1 hx hx1) : lgG x + r < gq 1 x)
  exact hc_glAV hx hx1 (hi_one_le hx hx1) hxq hGq hG0 r hrq (fun ν' hν' _ =>
    hi_nofix hx hx1 ((lt_add_one _).trans_le le_self_add)
      ((add_le_add le_rfl hν').trans_lt hjr))

theorem hi_cf_lt {r : Ordinal.{0}} (hr : r < hiZl x) : veblen x (lgG x + 1 + r) < hiZl x := by
  have h := (isNormal_veblen x).strictMono (hi_j_lt_Zl hx hx1 hr)
  rwa [hiZl_eq hx hx1, hcN_fix, ← hiZl_eq hx hx1] at h

end Base

/-! ## The reading `P_λ(x)` of an offset read by a system `E` -/

/-- **`P_λ(x) = ϑˣ(Ω₁·x + Γ_{x+1} + λ(x))`** (`λ(x) = E.R λ x`). -/
noncomputable def hiP (E : HgVD) (l x : Ordinal.{0}) : Ordinal.{0} := glA x (lgG x + E.R l x) x

section Read

variable (E : HgVD) {l : Ordinal.{0}} (hlB : l < E.B) (hZ : ∀ x, InE x → x < Om1 → E.Z x ≤ hiZl x)

section At

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : E.g l < x)
include hlB hZ hx hx1 hg

theorem hiR_lt : E.R l x < hiZl x := (E.R_lt_Z x hx hx1 l hlB hg).trans_le (hZ x hx hx1)

theorem hiR1_lt : E.R l x + 1 < hiZl x :=
  (ev_isSuccLimit_of_inE (hiZl_E hx hx1)).add_one_lt (hiR_lt E hlB hZ hx hx1 hg)

theorem hiP_eq : hiP E l x = veblen x (lgG x + 1 + E.R l x) := hi_cf hx hx1 (hiR_lt E hlB hZ hx hx1 hg)

theorem hiP_lt_Zl : hiP E l x < hiZl x := by
  rw [hiP_eq E hlB hZ hx hx1 hg]; exact hi_cf_lt hx hx1 (hiR_lt E hlB hZ hx hx1 hg)

/-- **`hdNx x (P_λ(x)) = ϑˣ(Ω₁·x + Γ_{x+1} + λ(x) + 1)`.** -/
theorem hiP_succ : hdNx x (hiP E l x) = glA x (lgG x + (E.R l x + 1)) x := by
  rw [hiP_eq E hlB hZ hx hx1 hg, hdNx_veb, hi_cf hx hx1 (hiR1_lt E hlB hZ hx hx1 hg), add_assoc (lgG x + 1)]

theorem hiPn_lt_Zl : hdNx x (hiP E l x) < hiZl x := by
  rw [hiP_eq E hlB hZ hx hx1 hg, hdNx_veb, add_assoc (lgG x + 1)]
  exact hi_cf_lt hx hx1 (hiR1_lt E hlB hZ hx hx1 hg)

theorem hiP_gt : x < hiP E l x := by
  rw [hiP_eq E hlB hZ hx hx1 hg]
  exact (lgG_facts hx hx1).2.1.trans (((lt_add_one _).trans_le le_self_add).trans_le (right_le_veblen _ _))

theorem hiP_fix {α : Ordinal.{0}} (h : α < x) : veblen α (hiP E l x) = hiP E l x := by
  rw [hiP_eq E hlB hZ hx hx1 hg]; exact veblen_veblen_of_lt h _

theorem hiP_lt1 : hiP E l x < gq 1 x := (hiP_lt_Zl E hlB hZ hx hx1 hg).trans (hiZl_lt1 hx hx1)

theorem hiP_T : hiP E l x ∈ Tset x ∧ hiP E l x < Om1 := gm1_T hx hx1 (hiP_lt1 E hlB hZ hx hx1 hg)

theorem hit_lt1 : lgG x + E.R l x < gq 1 x :=
  (inE_indec (gm1_facts hx hx1).2.2.2).add_lt (mg_lgG_lt_G1 hx hx1)
    ((hiR_lt E hlB hZ hx hx1 hg).trans (hiZl_lt1 hx hx1))

theorem hit1_lt1 : lgG x + (E.R l x + 1) < gq 1 x :=
  (inE_indec (gm1_facts hx hx1).2.2.2).add_lt (mg_lgG_lt_G1 hx hx1)
    ((hiR1_lt E hlB hZ hx hx1 hg).trans (hiZl_lt1 hx hx1))

/-- **`N_α(P_λ(x)) < hdNx x (P_λ(x))`** for `α < x`. -/
theorem hiN_lt_Pn {α : Ordinal.{0}} (h : α < x) : hcN α (hiP E l x) < hdNx x (hiP E l x) :=
  hdN_lt_Nx ((ev_isSuccLimit_of_inE hx).add_one_lt h)

/-- **`N_α(P_λ(x)) = ϑˣ(Ω₁·(α+1) + P_λ(x))`** for `α + 1 < x`. -/
theorem hiNP_glA {α : Ordinal.{0}} (h : α + 1 < x) : hcN α (hiP E l x) = glA (α + 1) (hiP E l x) x := by
  have hfix : veblen (α + 1) (hiP E l x) = hiP E l x := hiP_fix E hlB hZ hx hx1 hg h
  have e : hcN α (hiP E l x) = veblen (α + 1) (hiP E l x + 1) := by
    have := hcN_veb α (hiP E l x); rwa [hfix] at this
  rw [e, hc_glA_fixG hx hx1 le_add_self (h.trans (gm1_facts hx hx1).2.1) hfix
    (h.trans (hiP_gt E hlB hZ hx hx1 hg)) (hiP_gt E hlB hZ hx hx1 hg) (hiP_lt1 E hlB hZ hx hx1 hg)]

end At

include hlB in
theorem hit_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hg : E.g l < σ) :
    lgG ρ + E.R l ρ ∈ TB ρ σ ∧ pi σ ρ (lgG ρ + E.R l ρ) = lgG σ + E.R l σ := by
  obtain ⟨g1, g2⟩ : lgG ρ ∈ TB ρ σ ∧ pi σ ρ (lgG ρ) = lgG σ := Go.goGl.ba_pi σ ρ hB
  obtain ⟨e1, e2⟩ := E.ex σ ρ hB l hlB hg
  obtain ⟨s1, s2⟩ := pi_add hB g1 e1
  rw [g2, e2] at s2
  exact ⟨s1, s2⟩

include hlB in
theorem hit1_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hg : E.g l < σ) :
    lgG ρ + (E.R l ρ + 1) ∈ TB ρ σ ∧ pi σ ρ (lgG ρ + (E.R l ρ + 1)) = lgG σ + (E.R l σ + 1) := by
  obtain ⟨t1, t2⟩ := hit_pi E hlB hB hg
  have h1σ : (1 : Ordinal.{0}) < σ := one_lt_omega0.trans (omega0_lt_inE hB.1)
  obtain ⟨u1, u2⟩ := pi_add hB t1 (mem_TB_of_lt hB h1σ)
  rw [t2, pi_lt hB h1σ] at u2
  rw [← add_assoc, ← add_assoc]
  exact ⟨u1, u2⟩

include hlB hZ in
/-- **Lemma EXACT for `P_λ(ρ)`** (the level `ρ` goes to `σ`, the base `Γ_{ρ+1}` to `Γ_{σ+1}`, `λ` is moved by `E`). -/
theorem hiP_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hg : E.g l < σ) :
    hiP E l ρ ∈ TB ρ σ ∧ pi σ ρ (hiP E l ρ) = hiP E l σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  obtain ⟨s1, s2⟩ := hit_pi E hlB hB hg
  obtain ⟨r1, r2⟩ := pi_base hB
  have h := glA_pi hB r1 hρ1 s1 (gm1_T hB.2.1 hρ1 (hit_lt1 E hlB hZ hB.2.1 hρ1 (hg.trans hB.2.2.1))).2
  rw [r2, s2] at h
  exact h

include hlB hZ in
/-- **Lemma EXACT for `hdNx ρ (P_λ(ρ))`.** -/
theorem hiPn_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hg : E.g l < σ) :
    hdNx ρ (hiP E l ρ) ∈ TB ρ σ ∧ pi σ ρ (hdNx ρ (hiP E l ρ)) = hdNx σ (hiP E l σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hgρ : E.g l < ρ := hg.trans hB.2.2.1
  obtain ⟨s1, s2⟩ := hit1_pi E hlB hB hg
  obtain ⟨r1, r2⟩ := pi_base hB
  have h := glA_pi hB r1 hρ1 s1 (gm1_T hB.2.1 hρ1 (hit1_lt1 E hlB hZ hB.2.1 hρ1 hgρ)).2
  rw [r2, s2] at h
  rw [hiP_succ E hlB hZ hB.2.1 hρ1 hgρ, hiP_succ E hlB hZ hB.1 hσ1 hg]
  exact h

include hlB hZ in
/-- **Lemma EXACT for `N_α(P_λ(ρ))`**, `α + 1 < σ`. -/
theorem hiNP_pi {α σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hg : E.g l < σ) (h : α + 1 < σ) :
    hcN α (hiP E l ρ) ∈ TB ρ σ ∧ pi σ ρ (hcN α (hiP E l ρ)) = hcN α (hiP E l σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hgρ : E.g l < ρ := hg.trans hB.2.2.1
  obtain ⟨f1, f2⟩ := hiP_pi E hlB hZ hB hg
  have hh := glA_pi hB (mem_TB_of_lt hB h) (h.trans hσ1) f1 (hiP_T E hlB hZ hB.2.1 hρ1 hgρ).2
  rw [pi_lt hB h, f2, ← hiNP_glA E hlB hZ hB.2.1 hρ1 hgρ (h.trans hB.2.2.1),
    ← hiNP_glA E hlB hZ hB.1 hσ1 hg h] at hh
  exact hh

end Read

/-! ## The code-gate conditions of `[Q_λ, hdNx Ω₁ Q_λ)` -/

section Gate

variable (E : HgVD) {l : Ordinal.{0}} (hlB : l < E.B) (hlN : l < hiN)

include hlN in
/-- **A code `y ∈ [Q_λ, hdNx Ω₁ Q_λ)` over `Z` forces the code `G + 1 + λ`.** -/
theorem hi_cl_j {Z y : Ordinal.{0}} (hZ1 : Z ≤ Om 1) (hy : GxCl Z {gcG 0} y) (hQy : hiQ l ≤ y)
    (hyN : y < hdNx Om1 (hiQ l)) : GxCl Z {gcG 0} (gcG 0 + 1 + l) := by
  have hj := hi_j_lt hlN
  have hGQ := hiG_lt_Q l
  unfold hiQ at hQy hyN hGQ
  rw [hdNx_veb] at hyN
  rw [Br.Om1_eq] at hj hGQ hQy hyN
  exact hd_cl_lev (by rw [← Br.Om1_eq]; exact hg_one_lt_Om1.le) hZ1 hj hGQ hy hQy hyN

include hlB hlN in
/-- **A code `y ∈ [Q_λ, hdNx Ω₁ Q_λ)` over a strongly critical `Z ≤ Ω₁` forces `g_E(λ) < Z`.** -/
theorem hi_gate_of {Z y : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (hy : GxCl Z {gcG 0} y) (hQy : hiQ l ≤ y)
    (hyN : y < hdNx Om1 (hiQ l)) : E.g l < Z := by
  have h := hi_cl_j hlN hZ1 hy hQy hyN
  have hl := hcX_cl_idx hZ hZ1 gr_G_inE le_rfl (GxCl.atom (Set.mem_singleton _)) h
  have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1
  exact E.code_gate Z hZ1' hZ.1 (fun _ _ hu hv => hZ.isPrincipal hu hv) (fun _ _ hu hv => hZ.2 _ hu _ hv)
    {gcG 0} (fun s hs => Or.inl (Set.mem_singleton_iff.1 hs)) l hl hlB

include hlN in
theorem hi_Q_code {Z y : Ordinal.{0}} (hZ1 : Z ≤ Om 1) (hy : GxCl Z {gcG 0} y) (hQy : hiQ l ≤ y)
    (hyN : y < hdNx Om1 (hiQ l)) : GxCl Z {gcG 0} (hiQ l) := by
  have h := hi_cl_j hlN hZ1 hy hQy hyN
  unfold hiQ; rw [Br.Om1_eq]
  exact GxCl.phi GxCl.om h

theorem hiQ_fix {α : Ordinal.{0}} (hα : α < Om1) (l : Ordinal.{0}) : veblen α (hiQ l) = hiQ l :=
  veblen_veblen_of_lt hα _

theorem hiN_eqQ {α : Ordinal.{0}} (hα : α < Om1) (l : Ordinal.{0}) :
    hcN α (hiQ l) = veblen (α + 1) (hiQ l + 1) := by
  have := hcN_veb α (hiQ l); rwa [hiQ_fix (gl_Om1_lim.add_one_lt hα) l] at this

theorem hi_NQ_lt_Nx {α : Ordinal.{0}} (hα : α < Om1) (l : Ordinal.{0}) : hcN α (hiQ l) < hdNx Om1 (hiQ l) :=
  hdN_lt_Nx (gl_Om1_lim.add_one_lt hα)

end Gate

/-! ## The gated base at the offset `λ` -/

section Off

variable (E : HgVD) (l : Ordinal.{0}) (hlB : l < E.B) (hlN : l < hiN)
  (hZ : ∀ x, InE x → x < Om1 → E.Z x ≤ hiZl x)

include hlB hlN hZ in
/-- **THE GATED BASE AT THE OFFSET `λ`**: `Q_λ = φ(Ω₁, G+1+λ)`, reading `P_λ(x) = ϑˣ(Ω₁·x + Γ_{x+1} + λ(x))`, gate
`g_E(λ)`, low field `Z_l(x)`. -/
noncomputable def hiOff : HiQB where
  Q := hiQ l
  P := hiP E l
  γ := E.g l
  Zo := hiZl
  γ_lt := E.g_lt l hlB
  Q_fix := fun α hα => hiQ_fix hα l
  G_lt := hiG_lt_Q l
  Q_lt1 := (hiQ_lt_N hlN).trans hiN_lt1
  N_lt1 := fun α hα => (hcN_le (hc_fix_down (by rw [Br.Om1_eq] at hα ⊢; exact hα.le) hiN_fix)
    (hiQ_lt_N hlN)).trans_lt hiN_lt1
  Q_mem := fun S {a b} ha hb => by
    unfold hiQ; rw [Br.Om1_eq]
    exact CSet.phi_mem (CSet.Om_mem (CSet.one_mem _ _))
      (CSet.add_mem (CSet.succ_mem (gmS_G0_mem S ha)) (E.mem S a b ha l hlB hb).1)
  N_mem := fun α hα S {a b} ha hb => by
    rw [hiN_eqQ hα l]
    have hQ : hiQ l ∈ S.CSet a b := by
      unfold hiQ; rw [Br.Om1_eq]
      exact CSet.phi_mem (CSet.Om_mem (CSet.one_mem _ _))
        (CSet.add_mem (CSet.succ_mem (gmS_G0_mem S ha)) (E.mem S a b ha l hlB (max_lt_iff.1 hb).1).1)
    exact CSet.phi_mem (CSet.succ_mem (he_cst_mem S le_rfl (max_lt_iff.1 hb).2)) (CSet.succ_mem hQ)
  Q_code := fun α hα Z hZ hZ1 y hy hQy hyN =>
    hi_Q_code hlN hZ1 hy hQy (hyN.trans (hi_NQ_lt_Nx hα l))
  Q_cl := fun α hα Z hZ hZ1 y hy hQy hyN =>
    hi_gate_of E hlB hlN hZ hZ1 hy hQy (hyN.trans (hi_NQ_lt_Nx hα l))
  N_cl := fun α hα Z hZ hZ1 hN => by
    rw [hiN_eqQ hα l] at hN
    have hα1 : α + 1 < Om 1 := by rw [← Br.Om1_eq]; exact gl_Om1_lim.add_one_lt hα
    have hαZ : α + 1 < Z := he_cl_level le_add_self hα1 hZ hZ1
      (hd_succ_lt (lt_of_le_of_lt zero_le (lt_add_one α)).ne' _)
      ((hiG_lt_Q l).trans ((lt_add_one _).trans_le (right_le_veblen _ _))) hN le_rfl
      ((isNormal_veblen _).strictMono (lt_add_one _))
    have hQ := hd_cl_succ_fix le_add_self hZ hZ1 (hiG_lt_Q l).le hN
    exact max_lt (hi_gate_of E hlB hlN hZ hZ1 hQ le_rfl (hdNx_gt _ _)) ((lt_add_one α).trans hαZ)
  P_gt := fun α hα x hx hx1 hγ => hiP_gt E hlB hZ hx hx1 (max_lt_iff.1 hγ).1
  P_fix := fun α hα x hx hx1 hγ => hiP_fix E hlB hZ hx hx1 (max_lt_iff.1 hγ).1 (max_lt_iff.1 hγ).2
  N_Zo := fun α hα x hx hx1 hγ => (hiN_lt_Pn E hlB hZ hx hx1 (max_lt_iff.1 hγ).1 (max_lt_iff.1 hγ).2).trans
    (hiPn_lt_Zl E hlB hZ hx hx1 (max_lt_iff.1 hγ).1)
  Zo_fix := hiZl_fix
  Zo_G1 := fun x hx hx1 => hiZl_lt1 hx hx1
  P_pi := fun α hα σ ρ hB hγ => hiP_pi E hlB hZ hB (max_lt_iff.1 hγ).1
  N_pi := fun α hα σ ρ hB hγ => hiNP_pi E hlB hZ hB (max_lt_iff.1 hγ).1
    ((ev_isSuccLimit_of_inE hB.1).add_one_lt (max_lt_iff.1 hγ).2)
  Pn_lt := fun hx hx1 hγ => (hiPn_lt_Zl E hlB hZ hx hx1 hγ).trans (hiZl_lt1 hx hx1)
  Pn_pi := fun hB hγ => hiPn_pi E hlB hZ hB hγ
  Qn_mem := fun S {a b} ha hb => by
    rw [hiQ_succ]; unfold hiQ; rw [Br.Om1_eq]
    exact CSet.phi_mem (CSet.Om_mem (CSet.one_mem _ _))
      (CSet.add_mem (CSet.succ_mem (gmS_G0_mem S ha)) (CSet.succ_mem (E.mem S a b ha l hlB hb).1))
  Qn_cl := fun Z hZ hZ1 h => by
    have hQ1 : GxCl Z {gcG 0} (gcG 0 + 1 + l + 1) := by
      rw [hiQ_succ] at h
      have hl1 : l + 1 < hiN := hiN_lim.add_one_lt hlN
      have := hi_cl_j hl1 hZ1 h le_rfl (hdNx_gt _ _)
      rwa [← add_assoc] at this
    have hj := ha_cl_succ hZ.1 (fun s hs => by rw [Set.mem_singleton_iff.1 hs]; exact ev_isSuccLimit_of_inE gr_G_inE)
      hQ1 _ rfl
    have hl := hcX_cl_idx hZ hZ1 gr_G_inE le_rfl (GxCl.atom (Set.mem_singleton _)) hj
    have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1
    exact E.code_gate Z hZ1' hZ.1 (fun _ _ hu hv => hZ.isPrincipal hu hv) (fun _ _ hu hv => hZ.2 _ hu _ hv)
      {gcG 0} (fun s hs => Or.inl (Set.mem_singleton_iff.1 hs)) l hl hlB

theorem hiOff_Q : (hiOff E l hlB hlN hZ).Q = hiQ l := rfl

theorem hiOff_P (x : Ordinal.{0}) : (hiOff E l hlB hlN hZ).P x = hiP E l x := rfl

theorem hiOff_γ : (hiOff E l hlB hlN hZ).γ = E.g l := rfl

theorem hiOff_Zo : (hiOff E l hlB hlN hZ).Zo = hiZl := rfl

end Off

end Googology.Trans.PoR.InaccPsi.R2.Hi
