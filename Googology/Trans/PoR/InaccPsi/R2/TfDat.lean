import Googology.Trans.PoR.InaccPsi.R2.CitedLq
import Googology.Trans.PoR.InaccPsi.R2.RjCode
import Googology.Trans.PoR.InaccPsi.R2.LqGam

/-!
# The data of a level below `B_Γ`: Veblen normal forms over `Ω₁` and the atoms `Γ_ν = ψ_{Ω₂}(ν − (Ω₁ + 1))`

`Ω₁ = Om1`, `Γ = Ordinal.gamma` (`Γ_ν` the `ν`-th strongly critical ordinal), `B_Γ = tfBG` the least fixed point
of `Γ` above `Ω₁` (`Γ_{B_Γ} = B_Γ`).  Below `B_Γ` every strongly critical ordinal `z > Ω₁` is `Γ_ν` with `Ω₁ < ν <
z` (`tf_idx_lt`), i.e. the atom `ψ_{Ω₂}(c)`, `c = ν − (Ω₁ + 1)` (`Γ_{Ω₁+1+c}`); every other `ε`-number `z ∈ (Ω₁,
B_Γ)` is `φ(a, b)` with `a, b < z`; every other `z` is read by its Cantor normal form.

* `tf_gamma_lt` (**`Γ` maps `c.ord` into itself for a regular uncountable `c`**), `tf_gamma_Om1` (`Γ_{Ω₁} = Ω₁`),
  `tf_ggGam` (`Γ_{Ω₁+1} = ψ_{Ω₂}(0)`, the least strongly critical ordinal above `Ω₁`), `tfBG_lt_Om2` (`B_Γ < Ω₂`);
* `tfDat` (**the data of a level**: `z` below `Ω₁`, `0` at `Ω₁` and from `B_Γ` on, the larger data of `invVeblen₁ z`,
  `invVeblen₂ z` at the non-strongly-critical `ε`-numbers of `(Ω₁, B_Γ)`, the data of `ν − (Ω₁ + 1)` at an atom
  `Γ_ν`, the larger data of `log_ω z`, `z mod ω^{log_ω z}` at the other `z ∈ (Ω₁, B_Γ)`), its clauses, `tfDat_lt_Om1`,
  `tfDat_eq_rj` (**`tfDat = rjDat` below `ε_{Ω₁+1}`**), `tfDat_gg` (`tfDat Γ_{Ω₁+1} = 0`), `tfDat_E` (`tfDat
  ε_{Ω₁+1} = 1`), `tfDat_Om1_succ`;
* small facts for the instances of `R2.CitedTf`: `tf_one_lt`, `tf_T_lt` (ordinals below the base are in `Tᵗ`),
  `tf_E_eq` (`ε_{Ω₁+1} = φ(1, Ω₁ + 1)`), `tf_Om1_add_E`, `tf_Om1_mul_E` (`Ω₁·ε_{Ω₁+1} = ε_{Ω₁+1}`), `tf_E_arg_lt`,
  `tf_Om1_succ_TB` (`Ω₁ + 1 ∈ Tᵗ[σ]`, `π(Ω₁ + 1) = Ω₁ + 1`), `tf_M_le` (`Ω₁·M' + η' < Ω₁·M + η`, `η < Ω₁` ⇒ `M' ≤ M`).

No new axiom.  New definitions: `tfBG`, `tfIdx`, `tfDat`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tf

open Ordinal Order Set Cardinal Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj

/-! ## `Γ` below a regular cardinal -/

/-- **`Γ` maps `c.ord` into itself** for a regular uncountable cardinal `c`. -/
theorem tf_gamma_lt {c : Cardinal.{0}} (hc : c.IsRegular) (hunc : ℵ₀ < c) :
    ∀ i < c.ord, gamma i < c.ord := by
  have hcof : ℵ₀ < (c.ord).cof := by rw [hc.cof_ord]; exact hunc
  have hv : ∀ i < c.ord, veblen i 0 < c.ord := fun i hi =>
    veblen_lt_ord_of_isRegular hc hunc i hi 0 (omega0_pos.trans (omega0_lt_ord.2 hunc))
  intro i
  induction i using limitRecOn with
  | zero =>
    intro h0
    rw [gamma_zero_eq_nfp]
    exact nfp_lt_ord hcof hv h0
  | add_one b hb =>
    intro hb'
    rw [← Order.succ_eq_add_one, gamma_succ_eq_nfp]
    exact nfp_lt_ord hcof hv ((isSuccLimit_ord hc.1).succ_lt (hb ((Order.lt_succ b).trans hb')))
  | limit b hb H =>
    intro hb'
    rw [isNormal_gamma.apply_of_isSuccLimit hb]
    refine iSup_lt_ord_big hc ?_ fun i => H i.1 i.2 (i.2.trans hb')
    rw [Cardinal.mk_Iio_ordinal, Cardinal.lift_lt]
    exact lt_ord.1 hb'

theorem tf_reg1 : (ℵ_ (1 : Ordinal.{0})).IsRegular := by
  have := isRegular_aleph_add_one (0 : Ordinal.{0}); rwa [zero_add] at this

theorem tf_unc1 : ℵ₀ < ℵ_ (1 : Ordinal.{0}) := by rw [← aleph_zero]; exact aleph_lt_aleph.2 zero_lt_one

theorem tf_Om1_ord : (Om1 : Ordinal.{0}) = (ℵ_ (1 : Ordinal.{0})).ord := by rw [rj_Om1]; exact Om_eq_ord one_ne_zero

/-- **`Γ_{Ω₁} = Ω₁`.** -/
theorem tf_gamma_Om1 : gamma (Om1 : Ordinal.{0}) = Om1 := by
  have hSC : SC (Om1 : Ordinal.{0}) := by rw [rj_Om1]; exact SC_Om one_ne_zero
  obtain ⟨ν, hν⟩ := mem_range_gamma.2 hSC.veblen_zero
  rcases (show ν ≤ Om1 from hν ▸ isNormal_gamma.strictMono.le_apply).lt_or_eq with h | rfl
  · exfalso
    have := tf_gamma_lt tf_reg1 tf_unc1 ν (by rw [← tf_Om1_ord]; exact h)
    rw [hν, ← tf_Om1_ord] at this
    exact lt_irrefl _ this
  · exact hν

/-- `Ω₁ < Γ_ν` iff `Ω₁ < ν`. -/
theorem tf_Om1_lt_gamma {ν : Ordinal.{0}} : Om1 < gamma ν ↔ Om1 < ν := by
  have e : (Om1 : Ordinal.{0}) < gamma ν ↔ gamma Om1 < gamma ν := by rw [tf_gamma_Om1]
  rw [e, gamma_lt_gamma]

/-- **`Γ_{Ω₁+1}` is the least strongly critical ordinal above `Ω₁`.** -/
theorem tf_ggGam : ggGam = gamma (Om1 + 1) := by
  apply le_antisymm
  · exact ggGam_le (Lq.lq_gamma_SC _) (by rw [← rj_Om1]; exact tf_Om1_lt_gamma.2 (lt_add_one _))
  · obtain ⟨ν, hν⟩ := mem_range_gamma.2 ggGam_spec.1.veblen_zero
    have h1 : Om1 < ν := by rw [← tf_Om1_lt_gamma, hν, rj_Om1]; exact ggGam_spec.2
    rw [← hν]; exact gamma_le_gamma.2 (Order.add_one_le_of_lt h1)

/-! ## `B_Γ` and the index -/

/-- **`B_Γ`**: the least fixed point of `Γ` above `Ω₁`. -/
noncomputable def tfBG : Ordinal.{0} := nfp gamma (Om1 + 1)

theorem tfBG_fix : gamma tfBG = tfBG := nfp_fp isNormal_gamma _

theorem tfBG_gt : (Om1 : Ordinal.{0}) < tfBG := (lt_add_one _).trans_le (le_nfp _ _)

theorem tfBG_le {b : Ordinal.{0}} (hb : gamma b = b) (h : Om1 < b) : tfBG ≤ b :=
  nfp_le_fp monotone_gamma (Order.add_one_le_of_lt h) hb.le

theorem tfBG_SC : SC tfBG := by rw [← tfBG_fix]; exact Lq.lq_gamma_SC _

/-- **`B_Γ < Ω₂`.** -/
theorem tfBG_lt_Om2 : tfBG < Om (1 + 1 : Ordinal.{0}) := by
  have h2 : (1 + 1 : Ordinal.{0}) ≠ 0 := by rw [one_add_one_eq_two]; exact two_ne_zero
  have hreg : (ℵ_ (1 + 1 : Ordinal.{0})).IsRegular := isRegular_aleph_add_one 1
  have hunc : ℵ₀ < ℵ_ (1 + 1 : Ordinal.{0}) := by rw [← aleph_zero]; exact aleph_lt_aleph.2 (pos_iff_ne_zero.2 h2)
  rw [Om_eq_ord h2]
  refine nfp_lt_ord (by rw [hreg.cof_ord]; exact hunc) (tf_gamma_lt hreg hunc) ?_
  rw [← Om_eq_ord h2]
  exact SC.add_one_lt gg_SC_Om2 (by rw [rj_Om1]; exact gg_Om1_lt_Om2)

/-- `Γ_{Ω₁+1} < B_Γ`. -/
theorem tf_gg_lt_BG : ggGam < tfBG := by
  rw [tf_ggGam, ← tfBG_fix]
  refine gamma_lt_gamma.2 (lt_of_le_of_ne (Order.add_one_le_of_lt tfBG_gt) fun e => ?_)
  exact SC.ne_add_one tfBG_SC Om1 e.symm

theorem tf_E_lt_BG : ggE < tfBG :=
  (ggE_le (Low.opow_eq_self_of_SC ggGam_spec.1) ggGam_spec.2).trans_lt tf_gg_lt_BG

/-- The index of a value of `Γ`. -/
noncomputable def tfIdx (z : Ordinal.{0}) : Ordinal.{0} := sInf {ν | gamma ν = z}

theorem tfIdx_gamma (ν : Ordinal.{0}) : tfIdx (gamma ν) = ν := by
  have hm : gamma (tfIdx (gamma ν)) = gamma ν := csInf_mem (s := {μ | gamma μ = gamma ν}) ⟨ν, rfl⟩
  exact gamma_inj.1 hm

/-- **Below `B_Γ` a value `Γ_ν > Ω₁` is not a fixed point: `ν < Γ_ν`.** -/
theorem tf_idx_lt {ν : Ordinal.{0}} (h1 : Om1 < gamma ν) (h2 : gamma ν < tfBG) : ν < gamma ν := by
  refine lt_of_le_of_ne isNormal_gamma.strictMono.le_apply fun e => ?_
  have hfix : gamma (gamma ν) = gamma ν := by rw [← e]; exact e.symm
  exact absurd (tfBG_le hfix h1) (not_le.2 h2)

/-! ## The data -/

theorem tf_log_lt {z : Ordinal.{0}} (h1 : Om1 < z) (hE : ω ^ z ≠ z) : log ω z < z := by
  refine lt_of_le_of_ne (log_le_self ω z) fun e => hE ?_
  have hz0 : z ≠ 0 := (rj_Om1_pos.trans h1).ne'
  have hle : ω ^ z ≤ z := by
    have := opow_log_le_self ω hz0; rwa [e] at this
  exact le_antisymm hle (right_le_opow z one_lt_omega0)

theorem tf_inv2_lt {z : Ordinal.{0}} (hE : ω ^ z = z) : invVeblen₂ z < z := by
  have := invVeblen₂_lt z; rwa [hE] at this

/-- An `ε`-number `z > Ω₁` with `invVeblen₁ z = z` is a value of `Γ`. -/
theorem tf_SC_gamma {z : Ordinal.{0}} (h1 : Om1 < z) (hI : ¬ invVeblen₁ z < z) : gamma (tfIdx z) = z := by
  have he : invVeblen₁ z = z := le_antisymm (invVeblen₁_le z) (not_lt.1 hI)
  rcases invVeblen₁_eq_iff.1 he with h0 | ⟨ν, hν⟩
  · exact absurd h0 (rj_Om1_pos.trans h1).ne'
  · rw [← hν, tfIdx_gamma]

theorem tf_atom_lt {z : Ordinal.{0}} (h1 : Om1 < z) (h2 : z < tfBG) (hI : ¬ invVeblen₁ z < z) :
    tfIdx z - (Om1 + 1) < z := by
  have hg := tf_SC_gamma h1 hI
  have := tf_idx_lt (ν := tfIdx z) (by rw [hg]; exact h1) (by rw [hg]; exact h2)
  rw [hg] at this
  exact (Ordinal.sub_le_self _ _).trans_lt this

/-- **The countable data of a level `z < B_Γ`** on its normal form over `Ω₁` and the atoms `Γ_ν`
(`ψ_{Ω₂}(ν − (Ω₁ + 1))`, data of `ν − (Ω₁ + 1)`).  Junk value `0` from `B_Γ` on. -/
noncomputable def tfDat (z : Ordinal.{0}) : Ordinal.{0} :=
  if hz : Om1 < z ∧ z < tfBG then
    if hE : ω ^ z = z then
      if hI : invVeblen₁ z < z then
        have : invVeblen₂ z < z := tf_inv2_lt hE
        max (tfDat (invVeblen₁ z)) (tfDat (invVeblen₂ z))
      else
        have : tfIdx z - (Om1 + 1) < z := tf_atom_lt hz.1 hz.2 hI
        tfDat (tfIdx z - (Om1 + 1))
    else
      have : log ω z < z := tf_log_lt hz.1 hE
      have : z % ω ^ log ω z < z := rj_mod_lt (rj_Om1_pos.trans hz.1).ne'
      max (tfDat (log ω z)) (tfDat (z % ω ^ log ω z))
  else if z < Om1 then z else 0
termination_by z

theorem tfDat_small {z : Ordinal.{0}} (h : z < Om1) : tfDat z = z := by
  rw [tfDat, dif_neg (fun hz => absurd hz.1 (not_lt.2 h.le)), if_pos h]

theorem tfDat_Om1 : tfDat Om1 = 0 := by
  rw [tfDat, dif_neg (fun hz => absurd hz.1 (lt_irrefl _)), if_neg (lt_irrefl _)]

theorem tfDat_big {z : Ordinal.{0}} (h : tfBG ≤ z) : tfDat z = 0 := by
  rw [tfDat, dif_neg (fun hz => absurd hz.2 (not_lt.2 h)),
    if_neg (fun h' => absurd (h'.trans tfBG_gt) (not_lt.2 h))]

/-- The Cantor clause. -/
theorem tfDat_cnf {z : Ordinal.{0}} (h1 : Om1 < z) (h2 : z < tfBG) (hE : ω ^ z ≠ z) :
    tfDat z = max (tfDat (log ω z)) (tfDat (z % ω ^ log ω z)) := by
  rw [tfDat, dif_pos ⟨h1, h2⟩, dif_neg hE]

/-- The Veblen clause. -/
theorem tfDat_phi {z : Ordinal.{0}} (h1 : Om1 < z) (h2 : z < tfBG) (hE : ω ^ z = z) (hI : invVeblen₁ z < z) :
    tfDat z = max (tfDat (invVeblen₁ z)) (tfDat (invVeblen₂ z)) := by
  rw [tfDat, dif_pos ⟨h1, h2⟩, dif_pos hE, dif_pos hI]

/-- The atom clause, at the index. -/
theorem tfDat_atom {z : Ordinal.{0}} (h1 : Om1 < z) (h2 : z < tfBG) (hE : ω ^ z = z) (hI : ¬ invVeblen₁ z < z) :
    tfDat z = tfDat (tfIdx z - (Om1 + 1)) := by
  rw [tfDat, dif_pos ⟨h1, h2⟩, dif_pos hE, dif_neg hI]

/-- **The atom clause**: `tfDat Γ_ν = tfDat (ν − (Ω₁ + 1))` for `Ω₁ < ν`, `Γ_ν < B_Γ`. -/
theorem tfDat_gamma {ν : Ordinal.{0}} (h1 : Om1 < ν) (h2 : gamma ν < tfBG) :
    tfDat (gamma ν) = tfDat (ν - (Om1 + 1)) := by
  have hz1 : Om1 < gamma ν := tf_Om1_lt_gamma.2 h1
  have hE : ω ^ gamma ν = gamma ν := Low.opow_eq_self_of_SC (Lq.lq_gamma_SC ν)
  have hI : ¬ invVeblen₁ (gamma ν) < gamma ν := by rw [invVeblen₁_gamma]; exact lt_irrefl _
  rw [tfDat_atom hz1 h2 hE hI, tfIdx_gamma]

/-- **The data is countable.** -/
theorem tfDat_lt_Om1 : ∀ z : Ordinal.{0}, tfDat z < Om1 := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  by_cases hz : Om1 < z ∧ z < tfBG
  · by_cases hE : ω ^ z = z
    · by_cases hI : invVeblen₁ z < z
      · rw [tfDat_phi hz.1 hz.2 hE hI]
        exact max_lt (IH _ hI) (IH _ (tf_inv2_lt hE))
      · have hg := tf_SC_gamma hz.1 hI
        have h1 : Om1 < tfIdx z := by rw [← tf_Om1_lt_gamma, hg]; exact hz.1
        have e := tfDat_gamma h1 (by rw [hg]; exact hz.2)
        rw [hg] at e
        rw [e]; exact IH _ (tf_atom_lt hz.1 hz.2 hI)
    · rw [tfDat_cnf hz.1 hz.2 hE]
      exact max_lt (IH _ (tf_log_lt hz.1 hE)) (IH _ (rj_mod_lt (rj_Om1_pos.trans hz.1).ne'))
  · rw [tfDat, dif_neg hz]
    split_ifs with h
    · exact h
    · exact rj_Om1_pos

/-- **`tfDat = rjDat` below `ε_{Ω₁+1}`.** -/
theorem tfDat_eq_rj : ∀ z : Ordinal.{0}, z < ggE → tfDat z = rjDat z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hzE
  rcases lt_trichotomy z Om1 with h | rfl | h
  · rw [tfDat_small h, rjDat_small h]
  · rw [tfDat_Om1, rjDat_Om1]
  have hE : ω ^ z ≠ z := fun e => absurd (ggE_le e (by rw [← rj_Om1]; exact h)) (not_le.2 hzE)
  have hl := tf_log_lt h hE
  have hm := rj_mod_lt (rj_Om1_pos.trans h).ne'
  rw [tfDat_cnf h (hzE.trans tf_E_lt_BG) hE, rjDat_eq h hzE, IH _ hl (hl.trans hzE), IH _ hm (hm.trans hzE)]

/-- `tfDat Γ_{Ω₁+1} = 0`. -/
theorem tfDat_gg : tfDat ggGam = 0 := by
  have h := tfDat_gamma (ν := Om1 + 1) (lt_add_one _) (by rw [← tf_ggGam]; exact tf_gg_lt_BG)
  rw [← tf_ggGam, Ordinal.sub_self, tfDat_small rj_Om1_pos] at h
  exact h

/-! ## Small facts used by the instances of the generic citation -/

theorem tf_one_lt {τ : Ordinal.{0}} (hτ : InE τ) : (1 : Ordinal.{0}) < τ := by
  by_contra h
  rcases (not_lt.1 h).lt_or_eq with h0 | h1
  · rw [Order.lt_one_iff] at h0
    have := hτ; unfold InE at this; rw [h0, opow_zero] at this; exact one_ne_zero this
  · have := hτ; unfold InE at this; rw [h1, opow_one] at this
    exact absurd this (ne_of_gt one_lt_omega0)

/-- Ordinals below the base are in `Tᵗ`. -/
theorem tf_T_lt {τ x : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hx : x < τ) : x ∈ Tset τ := by
  obtain ⟨m, hm, -, -, hiff⟩ := T_inter_Om1 hτ hτ1
  exact (hiff x (hx.trans hτ1)).2 (hx.trans hm)

theorem tf_veblen1_Om1 : veblen 1 (Om1 : Ordinal.{0}) = Om1 := by
  have hSC : SC (Om1 : Ordinal.{0}) := by rw [rj_Om1]; exact SC_Om one_ne_zero
  exact SC.veblen_right hSC (lt_of_lt_of_le one_lt_omega0 (omega0_le_omega 1))

/-- **`ε_{Ω₁+1} = φ(1, Ω₁ + 1)`.** -/
theorem tf_E_eq : ggE = veblen 1 (Om1 + 1) := by
  have hE1 : Om1 < veblen 1 (Om1 + 1 : Ordinal.{0}) := by
    conv_lhs => rw [← tf_veblen1_Om1]
    exact veblen_lt_veblen_iff_right.2 (lt_add_one _)
  apply le_antisymm
  · refine ggE_le ?_ (by rw [← rj_Om1]; exact hE1)
    rw [← veblen_zero_apply]; exact veblen_veblen_of_lt zero_lt_one _
  · have hE : ω ^ ggE = ggE := ggE_spec.1
    have hle : 1 ≤ invVeblen₁ ggE := by
      rw [Order.one_le_iff_pos, pos_iff_ne_zero]
      intro h0
      have : ggE < veblen 0 ggE := lt_veblen_iff_invVeblen₁_le.2 (by rw [h0])
      rw [veblen_zero_apply, hE] at this; exact lt_irrefl _ this
    obtain ⟨y, hy⟩ := mem_range_veblen_iff_le_invVeblen₁.2 hle
    rw [hE] at hy
    have hy1 : Om1 < y := by
      rw [← veblen_lt_veblen_iff_right (o := 1), tf_veblen1_Om1, hy, rj_Om1]; exact ggE_spec.2
    rw [← hy]; exact veblen_le_veblen_iff_right.2 (Order.add_one_le_of_lt hy1)

theorem tf_Om1_add_E : (Om1 : Ordinal.{0}) + ggE = ggE := by
  conv_rhs => rw [← ggE_spec.1]
  conv_lhs => rw [← ggE_spec.1]
  exact Ordinal.add_of_omega0_opow_le (by rw [ggE_spec.1, rj_Om1]; exact ggE_spec.2) le_rfl

/-- `Ω₁·ε_{Ω₁+1} = ε_{Ω₁+1}`. -/
theorem tf_Om1_mul_E : (Om1 : Ordinal.{0}) * ggE = ggE := by
  have h1 : ω ^ (Om1 : Ordinal.{0}) = Om1 := rj_Om1_opow
  conv_lhs => rw [← h1, ← ggE_spec.1]
  rw [← opow_add, tf_Om1_add_E, ggE_spec.1]

theorem tf_one_lt_Om1 : (1 : Ordinal.{0}) < Om1 := tf_one_lt (τ := Om1) rj_Om1_opow

/-- `tfDat (Ω₁ + 1) = 1`. -/
theorem tfDat_Om1_succ : tfDat (Om1 + 1) = 1 := by
  have hz : (Om1 : Ordinal.{0}) < Om1 + 1 := lt_add_one _
  have hB : (Om1 : Ordinal.{0}) + 1 < tfBG := SC.add_one_lt tfBG_SC tfBG_gt
  have h1 := tf_one_lt_Om1
  have hE : ω ^ (Om1 + 1 : Ordinal.{0}) ≠ Om1 + 1 := by
    intro e
    have hP := isPrincipal_add_omega0_opow (Om1 + 1 : Ordinal.{0})
    rw [e] at hP
    exact lt_irrefl _ (hP (lt_add_one _) (h1.trans (lt_add_one _)))
  have hw : (Om1 : Ordinal.{0}) + 1 = ω ^ (Om1 : Ordinal.{0}) * 1 + 1 := by rw [mul_one, rj_Om1_opow]
  have h1w : (1 : Ordinal.{0}) < ω ^ (Om1 : Ordinal.{0}) := by rw [rj_Om1_opow]; exact h1
  have hl : log ω (Om1 + 1 : Ordinal.{0}) = Om1 := by
    rw [hw, log_opow_mul_add one_lt_omega0 one_ne_zero h1w, log_one_right, add_zero]
  have hm : (Om1 + 1 : Ordinal.{0}) % ω ^ log ω (Om1 + 1) = 1 := by
    rw [hl]; conv_lhs => rw [hw]
    rw [mul_add_mod_self, Ordinal.mod_eq_of_lt h1w]
  rw [tfDat_cnf hz hB hE, hm, hl, tfDat_Om1, tfDat_small h1, max_eq_right zero_le]

/-- `tfDat ε_{Ω₁+1} = 1`. -/
theorem tfDat_E : tfDat ggE = 1 := by
  have hE1 : Om1 < ggE := by rw [rj_Om1]; exact ggE_spec.2
  have h1 := tf_one_lt_Om1
  have hc : (Om1 : Ordinal.{0}) + 1 < veblen 1 (Om1 + 1) := by
    rw [← tf_E_eq]
    calc (Om1 : Ordinal.{0}) + 1 < Om1 + ggE := (add_lt_add_iff_left _).2 (h1.trans hE1)
      _ = ggE := tf_Om1_add_E
  have hI : invVeblen₁ ggE < ggE := by
    rw [tf_E_eq, invVeblen₁_veblen hc, ← tf_E_eq]; exact h1.trans hE1
  rw [tfDat_phi hE1 tf_E_lt_BG ggE_spec.1 hI, tf_E_eq, invVeblen₁_veblen hc, invVeblen₂_veblen one_ne_zero hc,
    tfDat_small h1, tfDat_Om1_succ, max_self]

/-- `Ω₁ + 1 < φ(1, Ω₁ + 1)`. -/
theorem tf_E_arg_lt : (Om1 : Ordinal.{0}) + 1 < veblen 1 (Om1 + 1) := by
  have hE1 : Om1 < ggE := by rw [rj_Om1]; exact ggE_spec.2
  rw [← tf_E_eq]
  calc (Om1 : Ordinal.{0}) + 1 < Om1 + ggE := (add_lt_add_iff_left _).2 (tf_one_lt_Om1.trans hE1)
    _ = ggE := tf_Om1_add_E

/-- `ε_{Ω₁+1}` and `Ω₁ + 1` in `Tᵗ[σ]` with `π_{σ,τ}(Ω₁ + 1) = Ω₁ + 1`. -/
theorem tf_Om1_succ_TB {σ τ : Ordinal.{0}} (h : Bases σ τ) :
    (Om1 : Ordinal.{0}) + 1 ∈ TB τ σ ∧ pi σ τ (Om1 + 1) = Om1 + 1 := by
  have h1σ : (1 : Ordinal.{0}) < σ := tf_one_lt h.1
  have h1 : (1 : Ordinal.{0}) ∈ TB τ σ := (TB_inter_lt h (h1σ.trans h.2.2.1)).2 h1σ
  obtain ⟨hO, hOp⟩ := pi_Om1 h
  obtain ⟨hs, hsp⟩ := pi_add h hO h1
  exact ⟨hs, by rw [hsp, hOp, pi_lt h h1σ]⟩

/-- From `Ω₁·M' + η' < Ω₁·M + η` with `η < Ω₁`: `M' ≤ M`. -/
theorem tf_M_le {M' η' M η : Ordinal.{0}} (hηΩ : η < Om1) (harg : Om1 * M' + η' < Om1 * M + η) : M' ≤ M := by
  by_contra h
  have h1 : Om1 * M + η < Om1 * M' := by
    calc Om1 * M + η < Om1 * M + Om1 := (add_lt_add_iff_left _).2 hηΩ
      _ = Om1 * (M + 1) := by rw [mul_add_one]
      _ ≤ Om1 * M' := mul_le_mul_right (Order.add_one_le_of_lt (not_le.1 h)) _
  exact absurd (h1.trans_le le_self_add) (not_lt.2 harg.le)

end Googology.Trans.PoR.InaccPsi.R2.Tf
