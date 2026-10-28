import Googology.Trans.PoR.InaccPsi.R2.HiLoc

/-!
# HiV: THE LEVELS `Ω₁ + ν` READ AS `x + ν`: THE LEVEL GATE AND THE READINGS `ϑˣ(Ω₁·(x+ν) + t)`

For a constant `ν < Ω₁` the level `Ω₁ + ν` is a code over `Z` iff `ν < Z`, and it is read as `x + ν` at every
`ε`-number base `x > ν`.

* the level gate: `hi_cl_rem` (**a code `y ∈ [Ω₁, Ω₁·2)` over `Z` has `y - Ω₁ < Z`**), `hi_cl_lvl` (**a code in
  `[φ(a, j), φ(a, j+1))` forces the level `a` to be a code**), `hiv_cl_gate` (**a code in `[φ(Ω₁+ν, j),
  φ(Ω₁+ν, j+1))` over `Z` has `ν < Z`**);
* the readings at the level `x + ν` (`ν < x`): `hiv_q`, `hiv_glA_P`, `hiv_glA_facts`, `hiv_glA_succ`,
  `hiv_glA_fixP`, `hiv_lvglAV` (the closed form below `N_{x+ν}(P)`), `hiv_glA_lt`, `hiv_glA_pi` (**Lemma EXACT for
  `ϑᵖ(Ω₁·(ρ+ν) + t)`: the level `ρ+ν` goes to `σ+ν`**).

No new axiom.  No new definition.
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
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The level gate -/

/-- **A code `y ∈ [Ω₁, Ω₁·2)` over a strongly critical `Z ≤ Ω₁` has `y - Ω₁ < Z`.** -/
theorem hi_cl_rem {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) {y : Ordinal.{0}}
    (hy : GxCl Z {gcG 0} y) (hOy : Om 1 ≤ y)
    (hy2 : y < Om 1 + Om 1) : y - Om 1 < Z := by
  have hOE : InE (Om 1) := by rw [← Br.Om1_eq]; exact gl_Om1_E
  have hOP : Indec (Om 1) := inE_indec hOE
  have hZ0 : 0 < Z := hZ.1
  induction hy with
  | small h => exact absurd hOy (not_le.2 (h.trans_le hZ1))
  | om => rw [Ordinal.sub_self]; exact hZ0
  | atom h =>
    rw [Set.mem_singleton_iff] at h
    exfalso
    rw [h] at hy2
    have hG : Om 1 + Om 1 < gcG 0 := (inE_indec gr_G_inE).add_lt (gcG_Om1_lt 0) (gcG_Om1_lt 0)
    exact absurd hy2 (not_lt.2 hG.le)
  | @add u v hu hv ihu ihv =>
    rcases lt_or_ge u (Om 1) with huO | huO
    · -- `u` countable: `v ≥ Ω₁` and `u + v = v`
      have hvO : Om 1 ≤ v := by
        by_contra hv'
        exact absurd hOy (not_le.2 (hOP.add_lt huO (not_le.1 hv')))
      obtain ⟨w, rfl⟩ := exists_add_of_le hvO
      have e : u + (Om 1 + w) = Om 1 + w := by rw [← add_assoc, Fp.fp_absorb hOE huO]
      rw [e] at hy2 ⊢
      exact ihv hvO hy2
    · have hv1 : v < Om 1 := by
        obtain ⟨w, rfl⟩ := exists_add_of_le huO
        by_contra hv'
        have : Om 1 + Om 1 ≤ Om 1 + w + v := by
          rw [add_assoc]; exact add_le_add le_rfl (le_add_left (not_lt.1 hv'))
        exact absurd hy2 (not_lt.2 this)
      have hu2 : u < Om 1 + Om 1 := lt_of_le_of_lt le_self_add hy2
      have h1 := ihu huO hu2
      have h2 : v < Z := he_cl_cnt hZ hv hv1
      obtain ⟨w, rfl⟩ := exists_add_of_le huO
      rw [Ordinal.add_sub_cancel] at h1
      rw [add_assoc, Ordinal.add_sub_cancel]
      exact hZ.isPrincipal h1 h2
  | @phi c b _ _ _ _ =>
    have hp : Indec (veblen c b) := by
      rcases eq_or_ne c 0 with hc | hc
      · rw [hc, veblen_zero_apply]; exact indec_opow b
      · exact inE_indec (gg_veblen_eps hc)
    have e : veblen c b = Om 1 := by
      refine le_antisymm (not_lt.1 fun hlt => ?_) hOy
      obtain ⟨w, hw⟩ := exists_add_of_le hOy
      have hw1 : w < Om 1 := by
        by_contra hw'
        have : Om 1 + Om 1 ≤ veblen c b := by rw [hw]; exact add_le_add le_rfl (not_lt.1 hw')
        exact absurd hy2 (not_lt.2 this)
      have hw0 : w < veblen c b := hw1.trans hlt
      have := hp.add_lt hlt hw0
      rw [← hw] at this
      exact lt_irrefl _ this
    rw [e, Ordinal.sub_self]; exact hZ0

/-- **A code in `[φ(a, j), φ(a, j+1))` forces the level `a` to be a code** (`a ≥ 1`, `j` not a fixed point of
`φ(a, ·)`, `G < φ(a, j)`). -/
theorem hi_cl_lvl {a : Ordinal.{0}} (ha : 1 ≤ a) {Z j : Ordinal.{0}} (hZ1 : Z ≤ Om 1) (hj : j < veblen a j)
    (hGQ : gcG 0 < veblen a j) {y : Ordinal.{0}} (hy : GxCl Z {gcG 0} y)
    (hQy : veblen a j ≤ y) (hyZ : y < veblen a (j + 1)) : GxCl Z {gcG 0} a := by
  have hFE : InE (veblen a j) := gg_veblen_eps (Order.one_le_iff_ne_zero.1 ha)
  have hOF : Om 1 < veblen a j := (gcG_Om1_lt 0).trans hGQ
  induction hy with
  | small h => exact absurd (hQy.trans_lt (h.trans_le hZ1)) (not_lt.2 hOF.le)
  | om => exact absurd hQy (not_le.2 hOF)
  | atom h =>
    rw [Set.mem_singleton_iff] at h
    rw [h] at hQy; exact absurd hQy (not_le.2 hGQ)
  | @add u v hu hv ihu ihv =>
    rcases le_or_gt (veblen a j) u with hFu | huF
    · exact ihu hFu (lt_of_le_of_lt le_self_add hyZ)
    · rcases le_or_gt (veblen a j) v with hFv | hvF
      · exact ihv hFv (lt_of_le_of_lt le_add_self hyZ)
      · exact absurd hQy (not_le.2 ((inE_indec hFE).add_lt huF hvF))
  | @phi c b hc hb ihc ihb =>
    have hbyZ : b < veblen a (j + 1) := lt_of_le_of_lt (right_le_veblen c b) hyZ
    rcases lt_or_ge c a with hca | hca
    · refine ihb ?_ hbyZ
      refine not_lt.1 fun hbF => ?_
      have hlt : veblen c b < veblen a j := by
        have h1 : veblen c b < veblen c (veblen a j) := (isNormal_veblen c).strictMono hbF
        rwa [veblen_veblen_of_lt hca] at h1
      exact absurd hQy (not_le.2 hlt)
    · rcases hca.lt_or_eq with hca' | hca'
      · exfalso
        have e3 : veblen a (veblen c b) = veblen c b := veblen_veblen_of_lt hca' b
        have h1 : j ≤ veblen c b := by
          have : veblen a j ≤ veblen a (veblen c b) := by rw [e3]; exact hQy
          exact (isNormal_veblen _).strictMono.le_iff_le.1 this
        have h2 : veblen c b < j + 1 := by
          have : veblen a (veblen c b) < veblen a (j + 1) := by rw [e3]; exact hyZ
          exact (isNormal_veblen _).strictMono.lt_iff_lt.1 this
        have e : veblen c b = j := le_antisymm (Order.lt_add_one_iff.1 h2) h1
        have : veblen a j = j := by rw [← e]; exact e3
        exact absurd this hj.ne'
      · exact hca' ▸ hc

theorem hiv_L1 (ν : Ordinal.{0}) : (1 : Ordinal.{0}) ≤ Om1 + ν := hg_one_lt_Om1.le.trans le_self_add

theorem hiv_L0 (ν : Ordinal.{0}) : Om1 + ν ≠ 0 := (zero_lt_one.trans_le (hiv_L1 ν)).ne'

/-- **THE LEVEL GATE**: a code over a strongly critical `Z ≤ Ω₁` in `[φ(Ω₁+ν, j), φ(Ω₁+ν, j+1))` (`ν < Ω₁`, `j` not a
fixed point, `G < φ(Ω₁+ν, j)`) has `ν < Z`. -/
theorem hiv_cl_gate {ν : Ordinal.{0}} (hν : ν < Om1) {Z j : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1)
    (hj : j < veblen (Om1 + ν) j) (hGQ : gcG 0 < veblen (Om1 + ν) j) {y : Ordinal.{0}} (hy : GxCl Z {gcG 0} y)
    (hQy : veblen (Om1 + ν) j ≤ y) (hyZ : y < veblen (Om1 + ν) (j + 1)) : ν < Z := by
  have h := hi_cl_lvl (hiv_L1 ν) hZ1 hj hGQ hy hQy hyZ
  rw [Br.Om1_eq] at h hν
  have h2 := hi_cl_rem hZ hZ1 h le_self_add ((add_lt_add_iff_left _).2 hν)
  rwa [Ordinal.add_sub_cancel] at h2

/-! ## The readings at the level `x + ν` -/

section Base

variable {ν x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hνx : ν < x)
include hx hx1 hνx

theorem hiv_q : x + ν < gq 1 x :=
  (inE_indec (gm1_facts hx hx1).2.2.2).add_lt (gm1_facts hx hx1).2.1 (hνx.trans (gm1_facts hx hx1).2.1)

theorem hiv_T : x + ν ∈ Tset x ∧ x + ν < Om1 := gm1_T hx hx1 (hiv_q hx hx1 hνx)

theorem hiv_one : (1 : Ordinal.{0}) ≤ x + ν := (hi_one_le hx hx1).trans le_self_add

theorem hiv_glA_P {t : Ordinal.{0}} (ht : t < gq 1 x) : LuP (x + ν) (glA (x + ν) t x) := by
  obtain ⟨htT, ht1⟩ := gm1_T hx hx1 ht
  obtain ⟨hT, h1⟩ := hiv_T hx hx1 hνx
  exact glA_P hx hx1 (hiv_one hx hx1 hνx) hT h1 htT ht1

theorem hiv_glA_facts {t : Ordinal.{0}} (ht : t < gq 1 x) :
    x + ν < glA (x + ν) t x ∧ glA (x + ν) t x < Om1 ∧ t < glA (x + ν) t x := by
  obtain ⟨htT, ht1⟩ := gm1_T hx hx1 ht
  obtain ⟨hT, h1⟩ := hiv_T hx hx1 hνx
  obtain ⟨-, -, ha1, -, hβa, hta⟩ := glA_facts hx hx1 (hiv_one hx hx1 hνx) hT h1 htT ht1
  exact ⟨hβa, ha1, hta⟩

/-- **`ϑˣ(Ω₁·(x+ν) + t + 1) = hdNx (x+ν) (ϑˣ(Ω₁·(x+ν) + t))`.** -/
theorem hiv_glA_succ {t : Ordinal.{0}} (ht : t + 1 < gq 1 x) :
    glA (x + ν) (t + 1) x = hdNx (x + ν) (glA (x + ν) t x) := by
  obtain ⟨i, hi⟩ := hiv_glA_P hx hx1 hνx ((lt_add_one t).trans ht)
  rw [hc_glA_succV hx hx1 (hiv_one hx hx1 hνx) (hiv_q hx hx1 hνx) ht hi.symm, ← hdNx_veb, hi]

/-- **`ϑˣ(Ω₁·(x+ν) + P) = hdNx (x+ν) P`** at a fixed point `P ∈ (x+ν, Γ_{x+2})` of `φ(x+ν, ·)`. -/
theorem hiv_glA_fixP {P : Ordinal.{0}} (hP : veblen (x + ν) P = P) (hxP : x + ν < P) (hPq : P < gq 1 x) :
    glA (x + ν) P x = hdNx (x + ν) P := by
  rw [hdNx_fixP hP]
  exact hc_glA_fixG hx hx1 (hiv_one hx hx1 hνx) (hiv_q hx hx1 hνx) hP hxP (le_self_add.trans_lt hxP) hPq

/-- **THE CLOSED FORM BELOW `N_{x+ν}(P)`**. -/
theorem hiv_lvglAV {P r i0 : Ordinal.{0}} (hP0 : glA (x + ν) P x = hdNx (x + ν) P) (hPq : P < gq 1 x)
    (hNq : hcN (x + ν) P < gq 1 x) (hi0 : veblen (x + ν) i0 = hdNx (x + ν) P) (hr : r < hcN (x + ν) P) :
    glA (x + ν) (P + r) x = veblen (x + ν) (i0 + r) := by
  have hNE := hcN_E (x + ν) P
  have hSN : hdNx (x + ν) P < hcN (x + ν) P := hdNx_lt_N (hcN_gt (x + ν) P)
  have hi0H : i0 < hcN (x + ν) P := (right_le_veblen (x + ν) i0).trans_lt (by rw [hi0]; exact hSN)
  have hir : i0 + r < hcN (x + ν) P := (inE_indec hNE).add_lt hi0H hr
  have hlt : veblen (x + ν) (i0 + r) < hcN (x + ν) P := by
    have := (isNormal_veblen (x + ν)).strictMono hir; rwa [hcN_fix] at this
  have hrq : P + r < gq 1 x := (inE_indec (gm1_facts hx hx1).2.2.2).add_lt hPq (hr.trans hNq)
  have hPi : P < veblen (x + ν) i0 := by rw [hi0]; exact hdNx_gt (x + ν) P
  exact hc_glAV hx hx1 (hiv_one hx hx1 hνx) (hiv_q hx hx1 hνx) hPq (by rw [hP0, hi0]) r hrq (fun ν' h' _ =>
    hc_nofixG hPi le_self_add (((isNormal_veblen _).monotone ((add_le_add_iff_left _).2 h')).trans_lt hlt))

/-- **`ϑˣ(Ω₁·(x+ν) + P + r) < N_{x+ν}(P)`** for `r < N_{x+ν}(P)`. -/
theorem hiv_glA_lt {P r : Ordinal.{0}} (hP0 : glA (x + ν) P x = hdNx (x + ν) P) (hPq : P < gq 1 x)
    (hNq : hcN (x + ν) P < gq 1 x) (hr : r < hcN (x + ν) P) : glA (x + ν) (P + r) x < hcN (x + ν) P := by
  obtain ⟨i0, hi0⟩ := hdNx_LuP (x + ν) P
  rw [hiv_lvglAV hx hx1 hνx hP0 hPq hNq hi0 hr]
  have hNE := hcN_E (x + ν) P
  have hi0H : i0 < hcN (x + ν) P :=
    (right_le_veblen (x + ν) i0).trans_lt (by rw [hi0]; exact hdNx_lt_N (hcN_gt (x + ν) P))
  have hir : i0 + r < hcN (x + ν) P := (inE_indec hNE).add_lt hi0H hr
  have := (isNormal_veblen (x + ν)).strictMono hir; rwa [hcN_fix] at this

/-- **`N_{x+ν}(P) = ϑˣ(Ω₁·(x+ν+1) + P)`** at a fixed point `P ∈ (x+ν, Γ_{x+2})` of `φ(x+ν+1, ·)`. -/
theorem hiv_N_glA {P : Ordinal.{0}} (hP : veblen (x + ν + 1) P = P) (hxP : x + ν + 1 < P) (hPq : P < gq 1 x) :
    hcN (x + ν) P = glA (x + ν + 1) P x := by
  have hq1 : x + ν + 1 < gq 1 x := (ev_isSuccLimit_of_inE (gm1_facts hx hx1).2.2.2).add_one_lt (hiv_q hx hx1 hνx)
  have e : hcN (x + ν) P = veblen (x + ν + 1) (P + 1) := by
    have := hcN_veb (x + ν) P; rwa [hP] at this
  rw [e, hc_glA_fixG hx hx1 ((hiv_one hx hx1 hνx).trans le_self_add) hq1 hP hxP
    ((le_self_add.trans le_self_add).trans_lt hxP) hPq]

end Base

/-- **Lemma EXACT for `ϑᵖ(Ω₁·(ρ+ν) + t)`**: `π(ϑᵖ(Ω₁·(ρ+ν) + t)) = ϑ^σ(Ω₁·(σ+ν) + π(t))` (`ν < σ`). -/
theorem hiv_glA_pi {ν σ ρ t : Ordinal.{0}} (hB : Bases σ ρ) (hνσ : ν < σ) (ht : t ∈ TB ρ σ) (htq : t < gq 1 ρ) :
    glA (ρ + ν) t ρ ∈ TB ρ σ ∧ pi σ ρ (glA (ρ + ν) t ρ) = glA (σ + ν) (pi σ ρ t) σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  obtain ⟨r1, r2⟩ := pi_base hB
  obtain ⟨u1, u2⟩ := pi_add hB r1 (mem_TB_of_lt hB hνσ)
  rw [r2, pi_lt hB hνσ] at u2
  have h := glA_pi hB u1 (hiv_T hB.2.1 hρ1 (hνσ.trans hB.2.2.1)).2 ht (gm1_T hB.2.1 hρ1 htq).2
  rw [u2] at h
  exact h

/-- **Lemma EXACT for `ρ + ν + 1`**. -/
theorem hiv_lev1_pi {ν σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hνσ : ν < σ) :
    ρ + ν + 1 ∈ TB ρ σ ∧ pi σ ρ (ρ + ν + 1) = σ + ν + 1 := by
  obtain ⟨r1, r2⟩ := pi_base hB
  obtain ⟨u1, u2⟩ := pi_add hB r1 (mem_TB_of_lt hB hνσ)
  rw [r2, pi_lt hB hνσ] at u2
  have h1σ : (1 : Ordinal.{0}) < σ := one_lt_omega0.trans (omega0_lt_inE hB.1)
  obtain ⟨w1, w2⟩ := pi_add hB u1 (mem_TB_of_lt hB h1σ)
  rw [u2, pi_lt hB h1σ] at w2
  exact ⟨w1, w2⟩

end Googology.Trans.PoR.InaccPsi.R2.Hi
