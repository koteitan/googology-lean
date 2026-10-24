import Googology.Trans.PoR.InaccPsi.R2.TfDat
import Googology.Trans.PoR.InaccPsi.R2.RhFn

/-!
# The data of a level below `X`: Veblen normal forms over `Ω₁` and the atoms `F_β(y)`

`Ω₁ = Om1`, `F_β = Rh.rhF β = veblenWith Γ β` (`F₀ = Γ`, `F_{β+1}` enumerates the fixed points of `F_β`, `F_λ` the
common fixed points of the `F_β`, `β < λ`), `B_Γ = Tf.tfBG` (the least fixed point of `Γ` above `Ω₁`), `g(β) = F_β(0)`
(`tlG`, a normal function), `X = tlX` (**the least fixed point of `g` above `Ω₁`**; `B_Γ < X < Ω₂`).  Below `X` every
strongly critical `z > Ω₁` has the **normal form** `z = F_λ(y)` with `λ = tlLev z` (the least `β` with `F_β(z) ≠ z`)
and `λ, y < z` (`tl_nf`); `λ = 0` gives the atoms `Γ_ν` of `R2.TfDat`, `λ ≥ 1` the new atoms (the values of `F_λ`
above `Ω₁` that are not fixed points of `F_λ`).

* `tl_rhF_lt` (**`F_β` maps `c.ord` into itself for a regular uncountable `c`**, both arguments), `tlG`, `tlG_normal`,
  `tlX`, `tlX_fix`, `tlX_gt`, `tlX_le`, `tlX_SC`, `tlX_lt_Om2`, `tlX_lt_OmTwo`, `tl_gamma_X`, `tl_BG_lt_X` (**`B_Γ <
  X`**), `tl_lt_G` (`z < F_z(0)` for `Ω₁ < z < X`);
* `tlLev`, `tlI` (the level and the index of a strongly critical `z`), `tlLev_spec`, `tl_nf` (**the normal form**),
  `tlLev_F` (**`tlLev (F_β(y)) = β` when `y < F_β(y)`**), `tlLev_gamma`, `tlI_rhF`;
* `tlDat` (**the data of a level**: `z` below `Ω₁`, `0` at `Ω₁` and from `X` on; the larger data of `invVeblen₁ z`,
  `invVeblen₂ z` at the non-strongly-critical `ε`-numbers of `(Ω₁, X)`; the data of `ν − (Ω₁ + 1)` at an atom `Γ_ν`
  (`λ = 0`); the larger data of `λ` and `y` at an atom `F_λ(y)`, `λ ≥ 1`; the larger data of `log_ω z`, `z mod
  ω^{log_ω z}` at the other `z ∈ (Ω₁, X)`), its clauses `tlDat_small`, `tlDat_Om1`, `tlDat_big`, `tlDat_cnf`,
  `tlDat_phi`, `tlDat_gamma`, `tlDat_F`, `tlDat_lt_Om1`, and `tlDat_eq_tf` (**`tlDat = Tf.tfDat` below `B_Γ`**).

No new axiom.  New definitions: `tlG`, `tlX`, `tlLev`, `tlI`, `tlDat`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tl

open Ordinal Order Set Cardinal Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Tf
  Googology.Trans.PoR.InaccPsi.R2.Rh

/-! ## `F_β` below a regular cardinal -/

/-- **`F_β(y) < c.ord` for `β, y < c.ord`**, `c` regular uncountable. -/
theorem tl_rhF_lt {c : Cardinal.{0}} (hc : c.IsRegular) (hunc : ℵ₀ < c) :
    ∀ β < c.ord, ∀ y < c.ord, rhF β y < c.ord := by
  intro β
  induction β using WellFoundedLT.induction with
  | ind β ih =>
  intro hβ y hy
  rcases eq_or_ne β 0 with rfl | h0
  · rw [rhF_zero]; exact tf_gamma_lt hc hunc y hy
  · have hveb : rhF β = derivFamily fun i : Iio β => rhF i.1 := veblenWith_of_ne_zero gamma h0
    rw [hveb]
    refine derivFamily_lt_ord_big hc hunc ?_ ?_ hy
    · rw [Cardinal.mk_Iio_ordinal, Cardinal.lift_lt]; exact lt_ord.1 hβ
    · intro i b hb; exact ih i.1 i.2 (i.2.trans hβ) b hb

/-! ## The bound `X` -/

/-- `g(β) = F_β(0)`. -/
noncomputable def tlG (β : Ordinal.{0}) : Ordinal.{0} := rhF β 0

theorem tlG_normal : Order.IsNormal tlG := by
  unfold tlG rhF; exact isNormal_veblenWith_zero isNormal_gamma gamma_pos

/-- **`X`**: the least fixed point of `β ↦ F_β(0)` above `Ω₁`. -/
noncomputable def tlX : Ordinal.{0} := nfp tlG (Om1 + 1)

theorem tlX_fix : tlG tlX = tlX := nfp_fp tlG_normal _

theorem tlX_rhF : rhF tlX 0 = tlX := tlX_fix

theorem tlX_gt : (Om1 : Ordinal.{0}) < tlX := (lt_add_one _).trans_le (le_nfp _ _)

theorem tlX_le {b : Ordinal.{0}} (hb : tlG b = b) (h : Om1 < b) : tlX ≤ b :=
  nfp_le_fp tlG_normal.strictMono.monotone (Order.add_one_le_of_lt h) hb.le

theorem tlX_SC : SC tlX := by rw [← tlX_rhF]; exact rhF_SC _ _

theorem tlX_pos : (0 : Ordinal.{0}) < tlX := rj_Om1_pos.trans tlX_gt

/-- **`X < Ω₂`.** -/
theorem tlX_lt_Om2 : tlX < Om (1 + 1 : Ordinal.{0}) := by
  have h2 : (1 + 1 : Ordinal.{0}) ≠ 0 := by rw [one_add_one_eq_two]; exact two_ne_zero
  have hreg : (ℵ_ (1 + 1 : Ordinal.{0})).IsRegular := isRegular_aleph_add_one 1
  have hunc : ℵ₀ < ℵ_ (1 + 1 : Ordinal.{0}) := by rw [← aleph_zero]; exact aleph_lt_aleph.2 (pos_iff_ne_zero.2 h2)
  rw [Om_eq_ord h2]
  refine nfp_lt_ord (by rw [hreg.cof_ord]; exact hunc)
    (fun i hi => tl_rhF_lt hreg hunc i hi 0 (omega0_pos.trans (omega0_lt_ord.2 hunc))) ?_
  rw [← Om_eq_ord h2]
  exact SC.add_one_lt gg_SC_Om2 (by rw [rj_Om1]; exact gg_Om1_lt_Om2)

theorem tlX_lt_OmTwo : (tlX : Ordinal.{0}) < OmTwo := by
  have h := tlX_lt_Om2
  rw [Om_of_ne_zero (by norm_num), one_add_one_eq_two] at h
  exact h

/-- `Γ_X = X`. -/
theorem tl_gamma_X : gamma tlX = tlX := by
  have h := rhF_fix_lower (j := 0) (β := tlX) tlX_pos 0
  rw [rhF_zero, tlX_rhF] at h
  exact h

/-- **`B_Γ < X`.** -/
theorem tl_BG_lt_X : tfBG < tlX := by
  refine lt_of_le_of_ne (tfBG_le tl_gamma_X tlX_gt) fun e => ?_
  -- `B_Γ` is not a fixed point of `F₁`
  have hfix : ∀ j < (1 : Ordinal.{0}), rhF j tfBG = tfBG := by
    intro j hj
    rw [Order.lt_one_iff] at hj
    rw [hj, rhF_zero]; exact tfBG_fix
  obtain ⟨e', he'⟩ := rhF_range tfBG_SC hfix
  have h1 : tfBG ≤ rhF 1 (Om1 + 1) := by
    refine tfBG_le (by rw [← rhF_zero]; exact rhF_fix_lower zero_lt_one _) ?_
    exact (lt_add_one _).trans_le (rhF_le_self 1 _)
  have he'le : e' ≤ Om1 + 1 := by rw [← he'] at h1; exact (rhF_le 1).1 h1
  have he'lt : e' < tfBG := he'le.trans_lt (SC.add_one_lt tfBG_SC tfBG_gt)
  have hne : rhF 1 tfBG ≠ tfBG := by
    intro h
    have := (rhF_lt 1).2 he'lt
    rw [he', h] at this
    exact lt_irrefl _ this
  apply hne
  have h1X : (1 : Ordinal.{0}) < tlX := tf_one_lt_Om1.trans tlX_gt
  have := rhF_fix_lower h1X 0
  rw [tlX_rhF] at this
  rw [e]; exact this

/-- `z < F_z(0)` for `Ω₁ < z < X`. -/
theorem tl_lt_G {z : Ordinal.{0}} (h1 : Om1 < z) (h2 : z < tlX) : z < tlG z :=
  lt_of_le_of_ne tlG_normal.strictMono.le_apply fun e => absurd (tlX_le e.symm h1) (not_le.2 h2)

/-! ## The level and the index -/

/-- The level of a strongly critical `z`: the least `β` with `F_β(z) ≠ z`. -/
noncomputable def tlLev (z : Ordinal.{0}) : Ordinal.{0} := sInf {β | rhF β z ≠ z}

/-- The index of `z` in `F_β`. -/
noncomputable def tlI (β z : Ordinal.{0}) : Ordinal.{0} := sInf {y | rhF β y = z}

theorem tlI_spec {β z : Ordinal.{0}} (h : ∃ y, rhF β y = z) : rhF β (tlI β z) = z := csInf_mem h

theorem tlI_rhF (β y : Ordinal.{0}) : tlI β (rhF β y) = y :=
  (rhF_normal β).strictMono.injective (tlI_spec ⟨y, rfl⟩)

theorem tlI_zero (z : Ordinal.{0}) : tlI 0 z = tfIdx z := by
  unfold tlI tfIdx; rw [rhF_zero]

/-- **The level of a strongly critical `z ∈ (Ω₁, X)`**: `λ = tlLev z < z`, `F_λ(z) ≠ z`, `F_β(z) = z` for `β < λ`. -/
theorem tlLev_spec {z : Ordinal.{0}} (hSC : SC z) (h1 : Om1 < z) (h2 : z < tlX) :
    tlLev z < z ∧ rhF (tlLev z) z ≠ z ∧ ∀ β < tlLev z, rhF β z = z := by
  have hne : rhF z z ≠ z := by
    intro e
    have : tlG z ≤ rhF z z := (rhF_le z).2 zero_le
    rw [e] at this
    exact absurd (tl_lt_G h1 h2) (not_lt.2 this)
  have hmem : tlLev z ∈ {β | rhF β z ≠ z} := csInf_mem ⟨z, hne⟩
  have hle : tlLev z ≤ z := csInf_le' hne
  have hlow : ∀ β < tlLev z, rhF β z = z := fun β hβ => by
    by_contra h; exact absurd (csInf_le' h) (not_le.2 hβ)
  refine ⟨lt_of_le_of_ne hle fun e => ?_, hmem, hlow⟩
  obtain ⟨y, hy⟩ := rhF_range hSC hlow
  rw [e] at hy
  have h0 := (rhF_le z).2 (zero_le : (0 : Ordinal.{0}) ≤ y)
  rw [hy] at h0
  exact absurd (tl_lt_G h1 h2) (not_lt.2 h0)

/-- **The normal form**: a strongly critical `z ∈ (Ω₁, X)` is `F_λ(y)` with `λ = tlLev z`, `y = tlI λ z`, `λ, y < z`. -/
theorem tl_nf {z : Ordinal.{0}} (hSC : SC z) (h1 : Om1 < z) (h2 : z < tlX) :
    rhF (tlLev z) (tlI (tlLev z) z) = z ∧ tlI (tlLev z) z < z ∧ tlLev z < z := by
  obtain ⟨hl, hne, hlow⟩ := tlLev_spec hSC h1 h2
  obtain ⟨e, he⟩ := rhF_range hSC hlow
  have hI := tlI_spec ⟨e, he⟩
  refine ⟨hI, lt_of_le_of_ne ?_ fun eq => ?_, hl⟩
  · calc tlI (tlLev z) z ≤ rhF (tlLev z) (tlI (tlLev z) z) := rhF_le_self _ _
      _ = z := hI
  · rw [eq] at hI; exact hne hI

/-- **`tlLev (F_β(y)) = β`** when `F_β(y)` is not a fixed point of `F_β` (`y < F_β(y)`). -/
theorem tlLev_F {β y : Ordinal.{0}} (hy : y < rhF β y) : tlLev (rhF β y) = β := by
  have hne : rhF β (rhF β y) ≠ rhF β y := fun e =>
    absurd ((rhF_normal β).strictMono.injective e) (ne_of_gt hy)
  refine le_antisymm (csInf_le' hne) (not_lt.1 fun hlt => ?_)
  have hmem : tlLev (rhF β y) ∈ {b | rhF b (rhF β y) ≠ rhF β y} := csInf_mem ⟨β, hne⟩
  exact hmem (rhF_fix_lower hlt y)

/-- `tlLev Γ_ν = 0` for `ν < Γ_ν`. -/
theorem tlLev_gamma {ν : Ordinal.{0}} (hν : ν < gamma ν) : tlLev (gamma ν) = 0 := by
  have h := tlLev_F (β := 0) (y := ν) (by rw [rhF_zero]; exact hν)
  rwa [rhF_zero] at h

/-! ## The data -/

theorem tl_SC_of {z : Ordinal.{0}} (h1 : Om1 < z) (hI : ¬ invVeblen₁ z < z) : SC z := by
  rw [← tf_SC_gamma h1 hI]; exact Lq.lq_gamma_SC _

theorem tl_atom0_lt {z : Ordinal.{0}} (h1 : Om1 < z) (h2 : z < tlX) (hI : ¬ invVeblen₁ z < z)
    (h0 : tlLev z = 0) : tfIdx z - (Om1 + 1) < z := by
  have h := (tl_nf (tl_SC_of h1 hI) h1 h2).2.1
  rw [h0, tlI_zero] at h
  exact (Ordinal.sub_le_self _ _).trans_lt h

/-- **The countable data of a level `z < X`** on its normal form over `Ω₁` and the atoms `F_λ(y)` (`λ = 0`: the
atom `Γ_ν`, data of `ν − (Ω₁ + 1)` as in `Tf.tfDat`; `λ ≥ 1`: the larger data of `λ` and `y`).  Junk value `0` from
`X` on. -/
noncomputable def tlDat (z : Ordinal.{0}) : Ordinal.{0} :=
  if hz : Om1 < z ∧ z < tlX then
    if hE : ω ^ z = z then
      if hI : invVeblen₁ z < z then
        have : invVeblen₂ z < z := tf_inv2_lt hE
        max (tlDat (invVeblen₁ z)) (tlDat (invVeblen₂ z))
      else
        if h0 : tlLev z = 0 then
          have : tfIdx z - (Om1 + 1) < z := tl_atom0_lt hz.1 hz.2 hI h0
          tlDat (tfIdx z - (Om1 + 1))
        else
          have : tlLev z < z := (tl_nf (tl_SC_of hz.1 hI) hz.1 hz.2).2.2
          have : tlI (tlLev z) z < z := (tl_nf (tl_SC_of hz.1 hI) hz.1 hz.2).2.1
          max (tlDat (tlLev z)) (tlDat (tlI (tlLev z) z))
    else
      have : log ω z < z := tf_log_lt hz.1 hE
      have : z % ω ^ log ω z < z := rj_mod_lt (rj_Om1_pos.trans hz.1).ne'
      max (tlDat (log ω z)) (tlDat (z % ω ^ log ω z))
  else if z < Om1 then z else 0
termination_by z

theorem tlDat_small {z : Ordinal.{0}} (h : z < Om1) : tlDat z = z := by
  rw [tlDat, dif_neg (fun hz => absurd hz.1 (not_lt.2 h.le)), if_pos h]

theorem tlDat_Om1 : tlDat Om1 = 0 := by
  rw [tlDat, dif_neg (fun hz => absurd hz.1 (lt_irrefl _)), if_neg (lt_irrefl _)]

theorem tlDat_big {z : Ordinal.{0}} (h : tlX ≤ z) : tlDat z = 0 := by
  rw [tlDat, dif_neg (fun hz => absurd hz.2 (not_lt.2 h)),
    if_neg (fun h' => absurd (h'.trans tlX_gt) (not_lt.2 h))]

/-- The Cantor clause. -/
theorem tlDat_cnf {z : Ordinal.{0}} (h1 : Om1 < z) (h2 : z < tlX) (hE : ω ^ z ≠ z) :
    tlDat z = max (tlDat (log ω z)) (tlDat (z % ω ^ log ω z)) := by
  rw [tlDat, dif_pos ⟨h1, h2⟩, dif_neg hE]

/-- The Veblen clause. -/
theorem tlDat_phi {z : Ordinal.{0}} (h1 : Om1 < z) (h2 : z < tlX) (hE : ω ^ z = z) (hI : invVeblen₁ z < z) :
    tlDat z = max (tlDat (invVeblen₁ z)) (tlDat (invVeblen₂ z)) := by
  rw [tlDat, dif_pos ⟨h1, h2⟩, dif_pos hE, dif_pos hI]

/-- The atom clause at level `0`. -/
theorem tlDat_atom0 {z : Ordinal.{0}} (h1 : Om1 < z) (h2 : z < tlX) (hE : ω ^ z = z) (hI : ¬ invVeblen₁ z < z)
    (h0 : tlLev z = 0) : tlDat z = tlDat (tfIdx z - (Om1 + 1)) := by
  rw [tlDat, dif_pos ⟨h1, h2⟩, dif_pos hE, dif_neg hI, dif_pos h0]

/-- The atom clause at a level `λ ≥ 1`. -/
theorem tlDat_atomF {z : Ordinal.{0}} (h1 : Om1 < z) (h2 : z < tlX) (hE : ω ^ z = z) (hI : ¬ invVeblen₁ z < z)
    (h0 : tlLev z ≠ 0) : tlDat z = max (tlDat (tlLev z)) (tlDat (tlI (tlLev z) z)) := by
  rw [tlDat, dif_pos ⟨h1, h2⟩, dif_pos hE, dif_neg hI, dif_neg h0]

theorem tl_SC_facts {z : Ordinal.{0}} (hSC : SC z) : ω ^ z = z ∧ ¬ invVeblen₁ z < z := by
  obtain ⟨ν, rfl⟩ := Lq.lq_SC_gamma hSC
  exact ⟨Low.opow_eq_self_of_SC hSC, by rw [invVeblen₁_gamma]; exact lt_irrefl _⟩

/-- **The atom clause at level `0`**: `tlDat Γ_ν = tlDat (ν − (Ω₁ + 1))` for `Ω₁ < ν < Γ_ν < X`. -/
theorem tlDat_gamma {ν : Ordinal.{0}} (h1 : Om1 < ν) (hν : ν < gamma ν) (h2 : gamma ν < tlX) :
    tlDat (gamma ν) = tlDat (ν - (Om1 + 1)) := by
  have hz1 : Om1 < gamma ν := tf_Om1_lt_gamma.2 h1
  obtain ⟨hE, hI⟩ := tl_SC_facts (Lq.lq_gamma_SC ν)
  rw [tlDat_atom0 hz1 h2 hE hI (tlLev_gamma hν), tfIdx_gamma]

/-- **The atom clause at a level `β ≥ 1`**: `tlDat (F_β(y)) = max (tlDat β) (tlDat y)` for `Ω₁ < F_β(y) < X`,
`y < F_β(y)`. -/
theorem tlDat_F {β y : Ordinal.{0}} (hβ : β ≠ 0) (h1 : Om1 < rhF β y) (h2 : rhF β y < tlX) (hy : y < rhF β y) :
    tlDat (rhF β y) = max (tlDat β) (tlDat y) := by
  obtain ⟨hE, hI⟩ := tl_SC_facts (rhF_SC β y)
  have hl := tlLev_F hy
  rw [tlDat_atomF h1 h2 hE hI (by rw [hl]; exact hβ), hl, tlI_rhF]

/-- **The data is countable.** -/
theorem tlDat_lt_Om1 : ∀ z : Ordinal.{0}, tlDat z < Om1 := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  by_cases hz : Om1 < z ∧ z < tlX
  · by_cases hE : ω ^ z = z
    · by_cases hI : invVeblen₁ z < z
      · rw [tlDat_phi hz.1 hz.2 hE hI]
        exact max_lt (IH _ hI) (IH _ (tf_inv2_lt hE))
      · obtain ⟨hI', hl, -⟩ := tl_nf (tl_SC_of hz.1 hI) hz.1 hz.2
        by_cases h0 : tlLev z = 0
        · rw [tlDat_atom0 hz.1 hz.2 hE hI h0]
          exact IH _ (tl_atom0_lt hz.1 hz.2 hI h0)
        · rw [tlDat_atomF hz.1 hz.2 hE hI h0]
          exact max_lt (IH _ (tl_nf (tl_SC_of hz.1 hI) hz.1 hz.2).2.2) (IH _ hl)
    · rw [tlDat_cnf hz.1 hz.2 hE]
      exact max_lt (IH _ (tf_log_lt hz.1 hE)) (IH _ (rj_mod_lt (rj_Om1_pos.trans hz.1).ne'))
  · rw [tlDat, dif_neg hz]
    split_ifs with h
    · exact h
    · exact rj_Om1_pos

/-- **`tlDat = Tf.tfDat` below `B_Γ`.** -/
theorem tlDat_eq_tf : ∀ z : Ordinal.{0}, z < tfBG → tlDat z = tfDat z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hzB
  rcases lt_trichotomy z Om1 with h | rfl | h
  · rw [tlDat_small h, tfDat_small h]
  · rw [tlDat_Om1, tfDat_Om1]
  have hzX : z < tlX := hzB.trans tl_BG_lt_X
  by_cases hE : ω ^ z = z
  · by_cases hI : invVeblen₁ z < z
    · rw [tlDat_phi h hzX hE hI, tfDat_phi h hzB hE hI, IH _ hI (hI.trans hzB),
        IH _ (tf_inv2_lt hE) ((tf_inv2_lt hE).trans hzB)]
    · have hg := tf_SC_gamma h hI
      have hν : tfIdx z < z := by
        have := tf_idx_lt (ν := tfIdx z) (by rw [hg]; exact h) (by rw [hg]; exact hzB)
        rwa [hg] at this
      have h0 : tlLev z = 0 := by
        have := tlLev_gamma (ν := tfIdx z) (by rw [hg]; exact hν)
        rwa [hg] at this
      have hlt := tl_atom0_lt h hzX hI h0
      rw [tlDat_atom0 h hzX hE hI h0, tfDat_atom h hzB hE hI, IH _ hlt (hlt.trans hzB)]
  · have hl := tf_log_lt h hE
    have hm := rj_mod_lt (rj_Om1_pos.trans h).ne'
    rw [tlDat_cnf h hzX hE, tfDat_cnf h hzB hE, IH _ hl (hl.trans hzB), IH _ hm (hm.trans hzB)]

end Googology.Trans.PoR.InaccPsi.R2.Tl
