import Googology.Trans.PoR.InaccPsi.R2.RkMove
import Googology.Trans.PoR.InaccPsi.R2.VcComp
import Googology.Trans.PoR.InaccPsi.R2.EvZ
import Googology.Trans.PoR.InaccPsi.R2.CitedSs
import Googology.Trans.PoR.InaccPsi.R2.Exact
import Googology.Trans.PoR.InaccPsi.R2.TzTh

/-!
# QcSub: THE SUBSTITUTION `Ω₁ ↦ e` IN A CODE BELOW `ε_{Ω₁+1}`, AND ITS BASE CHANGE

`ε_{Ω₁+1} = Gg.ggE`, `Θ_y = Gg.ggTh y` (the order type of the codes over `y`; for a strongly critical `y` it is the
substitution `Ω₁ ↦ y`, `Rk.rkB_Th`).  The reach at a level `Ω₁ ≤ M < ε_{Ω₁+1}` is `rjL(Θ_α(Ω₁·M)) + ζ` (`Rj.rj_lh`).
For Lemma IMG at a point of a generic level the same substitution is needed at an `ε`-number `e` that need not be
strongly critical (the image `f(E)` of a copy, and the points `u` with `π(u) = f(E)`).  Here it is defined on the Cantor
normal form, for every `e`:

* `qcSub e z` (**`z` with `Ω₁` replaced by `e`**: `z` below `Ω₁`, `e` at `Ω₁`, and `ω^{qcSub e g}·k + qcSub e r` at
  `z = ω^g·k + r ∈ (Ω₁, ε_{Ω₁+1})`), `qcSub_small`, `qcSub_Om1`, `qcSub_big`, `qcSub_lt_Om1`;
* `qcSub_eq_th` (**`qcSub y z = Θ_y(z)`** for a strongly critical `y < Ω₁` and a code `z < ε_{Ω₁+1}` over `y`);
* `qc_pi_sub` (**THE BASE CHANGE: `π(qcSub u z) = qcSub (π u) (π z)`**, `qcSub u z ∈ Tᵖ[σ]`, for `u, z ∈ Tᵖ[σ]`,
  `u < Ω₁`, `z < ε_{Ω₁+1}`, `υ`-points `σ < ρ`).

No new axiom.  New definition: `qcSub`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj

/-- **`z` with `Ω₁` replaced by `e`**, on the Cantor normal form of `z < ε_{Ω₁+1}`. -/
noncomputable def qcSub (e z : Ordinal.{0}) : Ordinal.{0} :=
  if hz : Om1 < z ∧ z < ggE then
    have : log ω z < z := rj_log_lt hz.1 hz.2
    have : z % ω ^ log ω z < z := rj_mod_lt (rj_Om1_pos.trans hz.1).ne'
    ω ^ qcSub e (log ω z) * (z / ω ^ log ω z) + qcSub e (z % ω ^ log ω z)
  else if z = Om1 then e else z
termination_by z

theorem qcSub_big {e z : Ordinal.{0}} (h1 : Om1 < z) (h2 : z < ggE) :
    qcSub e z = ω ^ qcSub e (log ω z) * (z / ω ^ log ω z) + qcSub e (z % ω ^ log ω z) := by
  rw [qcSub, dif_pos ⟨h1, h2⟩]

theorem qcSub_Om1 (e : Ordinal.{0}) : qcSub e Om1 = e := by
  rw [qcSub, dif_neg (fun h => lt_irrefl _ h.1), if_pos rfl]

theorem qcSub_small {e z : Ordinal.{0}} (h : z < Om1) : qcSub e z = z := by
  rw [qcSub, dif_neg (fun hz => absurd hz.1 (not_lt.2 h.le)), if_neg h.ne]

theorem qc_Om1_SC : SC (Om1 : Ordinal.{0}) := by rw [rj_Om1]; exact SC_Om one_ne_zero

/-- A point of `(Ω₁, ε_{Ω₁+1})` is not an `ε`-number. -/
theorem qc_not_eps {z : Ordinal.{0}} (h1 : Om1 < z) (h2 : z < ggE) : ω ^ z ≠ z := fun h =>
  absurd (csInf_le' (⟨h, by rw [← rj_Om1]; exact h1⟩ : z ∈ {b : Ordinal.{0} | ω ^ b = b ∧ Om 1 < b}) :
    ggE ≤ z) (not_le.2 h2)

theorem qc_ggE_lt_B : ggE < Uc.ucB := ggE_le_ggGam.trans_lt (Tz.tz_gg_lt_X.trans Uc.uc_X_lt_B)

/-- **The substitution of a countable `u` is countable.** -/
theorem qcSub_lt_Om1 {u : Ordinal.{0}} (hu : u < Om1) : ∀ z, z < ggE → qcSub u z < Om1 := by
  have hS := qc_Om1_SC
  have hE : InE (Om1 : Ordinal.{0}) := Low.opow_eq_self_of_SC hS
  have hI : Indec (Om1 : Ordinal.{0}) := Lq.lq_SC_indec hS
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hzE
  rcases lt_trichotomy z Om1 with h | rfl | h
  · rw [qcSub_small h]; exact h
  · rw [qcSub_Om1]; exact hu
  · have hz0 : z ≠ 0 := (rj_Om1_pos.trans h).ne'
    have hgz := rj_log_lt h hzE
    have hrz := rj_mod_lt hz0
    rw [qcSub_big h hzE]
    obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt z one_lt_omega0)
    rw [hk]
    have hg := IH _ hgz (hgz.trans hzE)
    have hw : ω ^ qcSub u (log ω z) < Om1 := by
      have := hS.2 0 hS.1 _ hg; rwa [veblen_zero_apply] at this
    exact hI.add_lt (InE.mul_lt hE hw ((natCast_lt_omega0 k).trans (omega0_lt_inE hE)))
      (IH _ hrz (hrz.trans hzE))

/-- **`qcSub y z = Θ_y(z)`** for a strongly critical `y < Ω₁` and a code `z < ε_{Ω₁+1}` over `y`. -/
theorem qcSub_eq_th {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) :
    ∀ z, GgCl y z → z < ggE → qcSub y z = ggTh y z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hz hzE
  rcases lt_trichotomy z (Om 1) with h | rfl | h
  · have hzy : z < y := hz.lt_of_lt_Om1 hy h
    rw [qcSub_small (by rw [rj_Om1]; exact h), ggTh_small hzy.le]
  · rw [← rj_Om1, qcSub_Om1, rj_Om1, ggTh_Om1 hy hy1]
  · have hz0 : z ≠ 0 := (lt_of_le_of_lt zero_le h).ne'
    have h' : Om1 < z := by rw [rj_Om1]; exact h
    obtain ⟨hsub, hlog⟩ := ggDec hy z hz
    set g := log ω z with hg
    have hgz : g < z := rj_log_lt h' hzE
    obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt z one_lt_omega0)
    have hdec : ω ^ g * k + z % ω ^ g = z := by
      have := Ordinal.div_add_mod z (ω ^ g); rwa [hk] at this
    have hwk : GgCl y (ω ^ g * k) := GgCl.mul_nat hy.1 (GgCl.opow hy.1 hlog) k
    have hle : ω ^ g * k ≤ z := by
      conv_rhs => rw [← hdec]
      exact le_self_add
    have hr : GgCl y (z % ω ^ g) := by
      have e : z - ω ^ g * k = z % ω ^ g := by
        nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
      rw [← e]; exact hsub _ hwk hle
    have hrz : z % ω ^ g < z := rj_mod_lt hz0
    have hkC : GgCl y (k : Ordinal.{0}) := Ph.ph_cl_nat hy k
    have hThk : ggTh y (k : Ordinal.{0}) = k :=
      ggTh_small (((natCast_lt_omega0 k).trans (Lw.lw_omega_lt_SC hy)).le)
    have hThz : ggTh y z = ω ^ ggTh y g * k + ggTh y (z % ω ^ g) := by
      conv_lhs => rw [← hdec]
      rw [ggTh_add hy hwk, Ph.phTh_opow_mul hy hlog k hkC, hThk]
    rw [qcSub_big h' hzE, ← hg, hk, hThz, IH g hgz hlog (hgz.trans hzE), IH _ hrz hr (hrz.trans hzE)]

/-- **THE BASE CHANGE OF THE SUBSTITUTION**: `π(qcSub u z) = qcSub (π u) (π z)` and `qcSub u z ∈ Tᵖ[σ]`, for
`u, z ∈ Tᵖ[σ]`, `u < Ω₁`, `z < ε_{Ω₁+1}` (`υ`-points `σ < ρ`). -/
theorem qc_pi_sub {σ ρ u : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) (hu : u ∈ TB ρ σ)
    (hu1 : u < Om1) :
    ∀ z, z < ggE → z ∈ TB ρ σ → qcSub u z ∈ TB ρ σ ∧ pi σ ρ (qcSub u z) = qcSub (pi σ ρ u) (pi σ ρ z) := by
  obtain ⟨hOT, hOπ⟩ := pi_Om1 hB
  obtain ⟨hET, hEπ⟩ := ssE_TB hB
  have hmono := (pi_bijOn hB).2
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hzE hzT
  rcases lt_trichotomy z Om1 with h | rfl | h
  · have hπz : pi σ ρ z < Om1 := by rw [← hOπ]; exact hmono hzT hOT h
    rw [qcSub_small h, qcSub_small hπz]
    exact ⟨hzT, rfl⟩
  · rw [qcSub_Om1, hOπ, qcSub_Om1]
    exact ⟨hu, rfl⟩
  · have hz0 : z ≠ 0 := (rj_Om1_pos.trans h).ne'
    have hgz := rj_log_lt h hzE
    have hrz := rj_mod_lt hz0
    obtain ⟨-, hlogπ, hdivπ, hmodπ, hgT, hrT, -⟩ :=
      Vc.vc_pi_cnf hB h (hzE.trans qc_ggE_lt_B) (qc_not_eps h hzE) hzT
    have hπ1 : Om1 < pi σ ρ z := by rw [← hOπ]; exact hmono hOT hzT h
    have hπE : pi σ ρ z < ggE := by rw [← hEπ]; exact hmono hzT hET hzE
    obtain ⟨hgsT, hgsπ⟩ := IH _ hgz (hgz.trans hzE) hgT
    obtain ⟨hrsT, hrsπ⟩ := IH _ hrz (hrz.trans hzE) hrT
    have hγ1 : qcSub u (log ω z) < Om1 := qcSub_lt_Om1 hu1 _ (hgz.trans hzE)
    obtain ⟨hwT, hwπ⟩ := pi_opowZ hσ hρ hB hgsT hγ1
    obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt z one_lt_omega0)
    obtain ⟨hwkT, hwkπ⟩ := pi_mul_nat hB hwT hwπ k
    obtain ⟨hsT, hsπ⟩ := pi_add hB hwkT hrsT
    rw [qcSub_big h hzE, hk]
    refine ⟨hsT, ?_⟩
    rw [hsπ, hwkπ, hgsπ, hrsπ, qcSub_big hπ1 hπE, hdivπ, hk, hmodπ, hlogπ]

end Googology.Trans.PoR.InaccPsi.R2.Qc
