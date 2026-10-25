import Googology.Trans.PoR.InaccPsi.R2.HdG

/-!
# HdNx: THE NEXT POINT OF A VEBLEN LEVEL `μ`, AND THE READINGS AT A CONSTANT LEVEL `ω ≤ μ < ε₀`

For a level `μ`, `hdNx μ Q` is the least point of `range φ(μ, ·)` above `Q`: `hdNx μ (φ(μ, a)) = φ(μ, a+1)`,
`hdNx (μ+1) = N_μ` (the next fixed point of `φ(μ, ·)`), `hdNx ω = Hc.hcS`, and at a limit level `λ` with an
increasing cofinal sequence `β_k → λ` the points `N_{β_k}(Q)` are cofinal in `hdNx λ Q` (`hdNx_cof`).  A constant
level `ω ≤ μ < ε₀` (`HdLvl μ`) lies below every `ε`-number base, so it is read as itself and needs no gate.  At such a
level and an `ε`-number base `x`:

* `hdm_glA_P`, `hdm_glA_fix` (`ϑˣ(Ω₁·μ + t)` is a point of `range φ(μ, ·)`), `hdm_glA_succ`
  (**`ϑˣ(Ω₁·μ + t + 1) = hdNx μ (ϑˣ(Ω₁·μ + t))`**), `hdm_glA_fixP` (`ϑˣ(Ω₁·μ + P) = hdNx μ P` at a fixed point `P` of
  `φ(μ, ·)`), `hdm_lvglAV` (**the closed form `ϑˣ(Ω₁·μ + P + r) = φ(μ, i₀ + r)` below `N_μ(P)`**), `hdm_glA_lt`;
* `hdm_glA_pi` (Lemma EXACT for `ϑᵖ(Ω₁·μ + t)` from Lemma EXACT for `t`).

No new axiom.  New definitions: `hdNx`, `HdLvl`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hd

open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The next point of a level -/

/-- **The least point of `range φ(μ, ·)` above `Q`.** -/
noncomputable def hdNx (μ Q : Ordinal.{0}) : Ordinal.{0} := veblen μ (sInf {i | Q < veblen μ i})

theorem hdNx_ne (μ Q : Ordinal.{0}) : ({i | Q < veblen μ i} : Set Ordinal.{0}).Nonempty :=
  ⟨Q + 1, (lt_add_one Q).trans_le (right_le_veblen μ _)⟩

theorem hdNx_gt (μ Q : Ordinal.{0}) : Q < hdNx μ Q := csInf_mem (hdNx_ne μ Q)

theorem hdNx_min {μ Q i : Ordinal.{0}} (h : Q < veblen μ i) : hdNx μ Q ≤ veblen μ i :=
  (isNormal_veblen μ).monotone (csInf_le' h)

theorem hdNx_LuP (μ Q : Ordinal.{0}) : LuP μ (hdNx μ Q) := ⟨_, rfl⟩

theorem hdNx_le {μ Q v : Ordinal.{0}} (hv : LuP μ v) (hQv : Q < v) : hdNx μ Q ≤ v := by
  obtain ⟨i, rfl⟩ := hv; exact hdNx_min hQv

theorem hdNx_fix {μ β : Ordinal.{0}} (hβ : β < μ) (Q : Ordinal.{0}) : veblen β (hdNx μ Q) = hdNx μ Q :=
  veblen_veblen_of_lt hβ _

theorem hdNx_E {μ : Ordinal.{0}} (hμ : μ ≠ 0) (Q : Ordinal.{0}) : InE (hdNx μ Q) := gg_veblen_eps hμ

/-- **`hdNx μ (φ(μ, a)) = φ(μ, a+1)`.** -/
theorem hdNx_veb (μ a : Ordinal.{0}) : hdNx μ (veblen μ a) = veblen μ (a + 1) := by
  refine le_antisymm (hdNx_min ((isNormal_veblen μ).strictMono (lt_add_one a))) ?_
  obtain ⟨i, hi⟩ := hdNx_LuP μ (veblen μ a)
  have h := hdNx_gt μ (veblen μ a)
  rw [← hi] at h ⊢
  exact (isNormal_veblen μ).monotone (Order.add_one_le_of_lt ((isNormal_veblen μ).strictMono.lt_iff_lt.1 h))

/-- **`hdNx (μ+1) = N_μ`.** -/
theorem hdNx_succ (μ Q : Ordinal.{0}) : hdNx (μ + 1) Q = hcN μ Q :=
  le_antisymm (hdNx_le (hc_LuP_of_fix (hcN_fix μ Q)) (hcN_gt μ Q))
    (hcN_le (hc_fix_of_LuP (hdNx_LuP _ Q)) (hdNx_gt _ Q))

/-- **`hdNx ω = hcS`.** -/
theorem hdNx_om (Q : Ordinal.{0}) : hdNx ω Q = hcS Q :=
  le_antisymm (hdNx_le (hcS_LuP Q) (hcS_gt Q))
    (hcS_le (fun k => hdNx_fix (natCast_lt_omega0 k) Q) (hdNx_gt _ Q))

/-- **At a fixed point `P` of `φ(μ, ·)`: `hdNx μ P = φ(μ, P+1)`.** -/
theorem hdNx_fixP {μ P : Ordinal.{0}} (hP : veblen μ P = P) : hdNx μ P = veblen μ (P + 1) := by
  conv_lhs => rw [← hP]
  exact hdNx_veb μ P

/-- **`hdNx μ Q < N_μ(P)`** for `Q < N_μ(P)`. -/
theorem hdNx_lt_N {μ P Q : Ordinal.{0}} (hQ : Q < hcN μ P) : hdNx μ Q < hcN μ P := by
  have h1 : hdNx μ Q ≤ veblen μ (Q + 1) := hdNx_min ((lt_add_one Q).trans_le (right_le_veblen _ _))
  have h2 := (isNormal_veblen μ).strictMono ((hcN_lim μ P).add_one_lt hQ)
  rw [hcN_fix] at h2
  exact h1.trans_lt h2

/-- **`N_β(Q) < hdNx λ Q`** for `β + 1 < λ` (the next fixed point of `φ(β, ·)` lies below the next point of level
`λ`). -/
theorem hdN_lt_Nx {β l Q : Ordinal.{0}} (h : β + 1 < l) : hcN β Q < hdNx l Q := by
  have h1 : hcN β Q < hcN (β + 1) Q := by
    have hle := hcN_le (veblen_veblen_of_lt (lt_add_one β) (Q + 1)) ((lt_add_one Q).trans_le (right_le_veblen _ _))
    have h2 : Q + 1 < hcN (β + 1) Q := (hcN_lim _ Q).add_one_lt (hcN_gt _ Q)
    have h3 := (isNormal_veblen (β + 1)).strictMono h2
    rw [hcN_fix] at h3
    exact hle.trans_lt h3
  exact h1.trans_le (hcN_le (hdNx_fix h Q) (hdNx_gt l Q))

/-- **Cofinality at a limit level**: along an increasing sequence `β_k` cofinal in a limit `λ`, every
`c < hdNx λ Q` lies below some `N_{β_k}(Q)`. -/
theorem hdNx_cof {l Q : Ordinal.{0}} (hl : IsSuccLimit l) {β : ℕ → Ordinal.{0}} (hβl : ∀ k, β k < l)
    (hmono : ∀ k, β k ≤ β (k + 1)) (hcof : ∀ t, t < l → ∃ k, t < β k) {c : Ordinal.{0}} (hc : c < hdNx l Q) :
    ∃ k, c < hcN (β k) Q := by
  have hmono' : ∀ {j k : ℕ}, j ≤ k → β j ≤ β k := fun {j k} h => by
    induction k, h using Nat.le_induction with
    | base => exact le_rfl
    | succ k _ ih => exact ih.trans (hmono k)
  have hbdd : BddAbove (Set.range fun k : ℕ => hcN (β k) Q) := Ordinal.bddAbove_range _
  set s := ⨆ k : ℕ, hcN (β k) Q with hs
  have hfix : ∀ b, b < l → veblen b s = s := by
    intro b hb
    obtain ⟨k0, hk0⟩ := hcof b hb
    rw [hs, (isNormal_veblen b).map_iSup hbdd]
    refine le_antisymm (Ordinal.iSup_le fun n => ?_) (Ordinal.iSup_le fun n => ?_)
    · have hle : veblen b (hcN (β n) Q) ≤ veblen b (hcN (β (n + k0)) Q) :=
        (isNormal_veblen b).monotone (hcN_mono (hmono' (Nat.le_add_right n k0)) Q)
      rw [hc_fix_down (hk0.le.trans (hmono' (Nat.le_add_left k0 n))) (hcN_fix _ Q)] at hle
      exact hle.trans (le_ciSup hbdd (n + k0))
    · exact (right_le_veblen b _).trans (le_ciSup (Ordinal.bddAbove_range _) n)
  have hLuP : LuP l s := by
    unfold LuP; rw [mem_range_veblen hl.bot_lt.ne']; exact hfix
  have hQs : Q < s := (hcN_gt (β 0) Q).trans_le (le_ciSup hbdd 0)
  exact (lt_ciSup_iff hbdd).1 (hc.trans_le (hdNx_le hLuP hQs))

/-! ## Constant levels `ω ≤ μ < ε₀` -/

/-- **A constant level**: `ω ≤ μ < ε₀` (below every `ε`-number base, read as itself, no gate). -/
def HdLvl (μ : Ordinal.{0}) : Prop := ω ≤ μ ∧ μ < ε₀

namespace HdLvl

variable {μ : Ordinal.{0}} (hμ : HdLvl μ)
include hμ

theorem ne : μ ≠ 0 := (omega0_pos.trans_le hμ.1).ne'

theorem one_le : 1 ≤ μ := one_lt_omega0.le.trans hμ.1

theorem one_lt : 1 < μ := one_lt_omega0.trans_le hμ.1

theorem two_lt : 2 < μ := (show (2 : Ordinal.{0}) < ω from by exact_mod_cast natCast_lt_omega0 2).trans_le hμ.1

theorem lt_E {x : Ordinal.{0}} (hx : InE x) : μ < x := hμ.2.trans_le (gc_eps0_le hx)

theorem lt_gam1 : μ < gamma 1 := hμ.2.trans hc_eps0_lt_gam1

theorem succ : HdLvl (μ + 1) := ⟨hμ.1.trans le_self_add, hc_eps0_lim.add_one_lt hμ.2⟩

theorem mem (S : InaccSeq.{0}) {a : Ordinal.{0}} (ha : 0 < a) (b : Ordinal.{0}) : μ ∈ S.CSet a b :=
  gr_cst_mem ha b μ hμ.lt_gam1

theorem small {Z : Ordinal.{0}} (hZ : SC Z) : μ < Z := hμ.lt_E (Low.opow_eq_self_of_SC hZ)

/-- **A point of `range φ(μ, ·)` is a fixed point of `φ(1, ·)` and `φ(2, ·)`.** -/
theorem fix1 {v : Ordinal.{0}} (hv : LuP μ v) : veblen 1 v = v := by
  obtain ⟨a, rfl⟩ := hv; exact veblen_veblen_of_lt hμ.one_lt a

theorem fix2 {v : Ordinal.{0}} (hv : LuP μ v) : veblen 2 v = v := by
  obtain ⟨a, rfl⟩ := hv; exact veblen_veblen_of_lt hμ.two_lt a

theorem fixk {v : Ordinal.{0}} (hv : LuP μ v) (k : ℕ) : veblen (k : Ordinal.{0}) v = v := by
  obtain ⟨a, rfl⟩ := hv; exact veblen_veblen_of_lt ((natCast_lt_omega0 k).trans_le hμ.1) a

/-- **A fixed point of `φ(μ, ·)` lies in `range φ(μ, ·)`.** -/
theorem LuP_of_fix {P : Ordinal.{0}} (hP : veblen μ P = P) : LuP μ P := ⟨P, hP⟩

end HdLvl

section Base

variable {μ : Ordinal.{0}} (hμ : HdLvl μ) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hμ hx hx1

theorem hdm_lev_q : μ < gq 1 x := hμ.lt_E (gm1_facts hx hx1).2.2.2

theorem hdm_lev_T : μ ∈ Tset x ∧ μ < Om1 := gm1_T hx hx1 (hdm_lev_q hμ hx hx1)

theorem hdm_glA_P {t : Ordinal.{0}} (ht : t < gq 1 x) : LuP μ (glA μ t x) := by
  obtain ⟨htT, ht1⟩ := gm1_T hx hx1 ht
  obtain ⟨hμT, hμ1⟩ := hdm_lev_T hμ hx hx1
  exact glA_P hx hx1 hμ.one_le hμT hμ1 htT ht1

theorem hdm_glA_facts {t : Ordinal.{0}} (ht : t < gq 1 x) :
    x < glA μ t x ∧ glA μ t x < Om1 ∧ t < glA μ t x := by
  obtain ⟨htT, ht1⟩ := gm1_T hx hx1 ht
  obtain ⟨hμT, hμ1⟩ := hdm_lev_T hμ hx hx1
  obtain ⟨-, hxa, ha1, -, -, hta⟩ := glA_facts hx hx1 hμ.one_le hμT hμ1 htT ht1
  exact ⟨hxa, ha1, hta⟩

/-- **`ϑˣ(Ω₁·μ + t + 1) = hdNx μ (ϑˣ(Ω₁·μ + t))`.** -/
theorem hdm_glA_succ {t : Ordinal.{0}} (ht : t + 1 < gq 1 x) : glA μ (t + 1) x = hdNx μ (glA μ t x) := by
  obtain ⟨i, hi⟩ := hdm_glA_P hμ hx hx1 ((lt_add_one t).trans ht)
  rw [hc_glA_succV hx hx1 hμ.one_le (hdm_lev_q hμ hx hx1) ht hi.symm, ← hdNx_veb, hi]

/-- **`ϑˣ(Ω₁·μ + P) = hdNx μ P`** at a fixed point `P ∈ (x, Γ_{x+2})` of `φ(μ, ·)`. -/
theorem hdm_glA_fixP {P : Ordinal.{0}} (hP : veblen μ P = P) (hxP : x < P) (hPq : P < gq 1 x) :
    glA μ P x = hdNx μ P := by
  rw [hdNx_fixP hP]
  exact hc_glA_fixG hx hx1 hμ.one_le (hdm_lev_q hμ hx hx1) hP (hμ.lt_E hx |>.trans hxP) hxP hPq

/-- **THE CLOSED FORM BELOW `N_μ(P)`**: `ϑˣ(Ω₁·μ + P) = hdNx μ P`, `φ(μ, i₀) = hdNx μ P` ⇒
`ϑˣ(Ω₁·μ + P + r) = φ(μ, i₀ + r)` for `r < N_μ(P)`. -/
theorem hdm_lvglAV {P r i0 : Ordinal.{0}} (hP0 : glA μ P x = hdNx μ P) (hPq : P < gq 1 x) (hNq : hcN μ P < gq 1 x)
    (hi0 : veblen μ i0 = hdNx μ P) (hr : r < hcN μ P) : glA μ (P + r) x = veblen μ (i0 + r) := by
  have hNE := hcN_E μ P
  have hSN : hdNx μ P < hcN μ P := hdNx_lt_N (hcN_gt μ P)
  have hi0H : i0 < hcN μ P := (right_le_veblen μ i0).trans_lt (by rw [hi0]; exact hSN)
  have hir : i0 + r < hcN μ P := (inE_indec hNE).add_lt hi0H hr
  have hlt : veblen μ (i0 + r) < hcN μ P := by
    have := (isNormal_veblen μ).strictMono hir; rwa [hcN_fix] at this
  have hrq : P + r < gq 1 x := (inE_indec (gm1_facts hx hx1).2.2.2).add_lt hPq (hr.trans hNq)
  have hPi : P < veblen μ i0 := by rw [hi0]; exact hdNx_gt μ P
  exact hc_glAV hx hx1 hμ.one_le (hdm_lev_q hμ hx hx1) hPq (by rw [hP0, hi0]) r hrq (fun ν' h' _ =>
    hc_nofixG hPi le_self_add (((isNormal_veblen _).monotone ((add_le_add_iff_left _).2 h')).trans_lt hlt))

/-- **`ϑˣ(Ω₁·μ + P + r) < N_μ(P)`** for `r < N_μ(P)`. -/
theorem hdm_glA_lt {P r : Ordinal.{0}} (hP0 : glA μ P x = hdNx μ P) (hPq : P < gq 1 x) (hNq : hcN μ P < gq 1 x)
    (hr : r < hcN μ P) : glA μ (P + r) x < hcN μ P := by
  obtain ⟨i0, hi0⟩ := hdNx_LuP μ P
  rw [hdm_lvglAV hμ hx hx1 hP0 hPq hNq hi0 hr]
  have hNE := hcN_E μ P
  have hi0H : i0 < hcN μ P := (right_le_veblen μ i0).trans_lt (by rw [hi0]; exact hdNx_lt_N (hcN_gt μ P))
  have hir : i0 + r < hcN μ P := (inE_indec hNE).add_lt hi0H hr
  have := (isNormal_veblen μ).strictMono hir; rwa [hcN_fix] at this

end Base

/-- **Lemma EXACT for `ϑᵖ(Ω₁·μ + t)`** from Lemma EXACT for `t`. -/
theorem hdm_glA_pi {μ σ ρ t : Ordinal.{0}} (hμ : HdLvl μ) (hB : Bases σ ρ) (ht : t ∈ TB ρ σ) (htq : t < gq 1 ρ) :
    glA μ t ρ ∈ TB ρ σ ∧ pi σ ρ (glA μ t ρ) = glA μ (pi σ ρ t) σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hμσ : μ < σ := hμ.lt_E hB.1
  have h := glA_pi hB (mem_TB_of_lt hB hμσ) (hdm_lev_T hμ hB.2.1 hρ1).2 ht (gm1_T hB.2.1 hρ1 htq).2
  rw [pi_lt hB hμσ] at h
  exact h

end Googology.Trans.PoR.InaccPsi.R2.Hd
