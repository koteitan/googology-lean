import Googology.Trans.PoR.InaccPsi.R2.SsLev

/-!
# The levels `Φ_μ` on the generic data: every level `μ`, data `ssDat(Ω₁ + μ)`

`ssDatL μ = Ss.ssDat (Ω₁ + μ)` (**the data of the level `μ`** on Veblen normal forms, `R2.SsDat`), `Rk.rkP` the
levels of `R2.RkFn` with the data `Rk.rkDat μ = Rj.rjDat (Ω₁ + μ)`, which stops at `ε_{Ω₁+1}` (junk `0` from there
on).  The definition of `R2.RkFn` with the generic data:

* `ssP μ` (**the `μ`-th level**: the enumeration of the strongly critical `v > ssDatL μ` that are fixed points of
  every `ssP j`, `j < μ`, with `ssDatL j < v`), `ssP_props` (normal, range `ssC μ`), `ssP_SC`, `ssDatL_lt_ssP`,
  `ssP_fix_lower`, `ssP_range`, `ssP_fix_mono`, `ssP_ne_self_of_dat`, `ssDatL_lt_fix`;
* `ssDatL_eq` (**`ssDatL μ = rkDat μ` for `μ < ε_{Ω₁+1}`**), `ssDatL_E` (`ssDatL ε_{Ω₁+1} = 1`), `ssP_eq_rkP`
  (**`ssP μ = Rk.rkP μ` for every `μ ≤ ε_{Ω₁+1}`**: the new hierarchy extends the old one, which is correct up to
  `ε_{Ω₁+1}`; beyond, `ssP` reads the countable leaves of the Veblen normal form of `Ω₁ + μ`).

No new axiom.  New definitions: `ssDatL`, `ssP`, `ssC`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ss

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Rj

/-- **The data of the level `μ`** on Veblen normal forms: `ssDat (Ω₁ + μ)`. -/
noncomputable def ssDatL (μ : Ordinal.{0}) : Ordinal.{0} := ssDat (Om1 + μ)

theorem ssDatL_zero : ssDatL 0 = 0 := by unfold ssDatL; rw [add_zero, ssDat_Om1]

/-- **The `μ`-th level** `Φ_μ`: the enumeration of the strongly critical `v > ssDatL μ` that are fixed points of every
`Φ_j`, `j < μ`, with `ssDatL j < v`. -/
noncomputable def ssP (μ : Ordinal.{0}) : Ordinal.{0} → Ordinal.{0} :=
  enumOrd {v | SC v ∧ ssDatL μ < v ∧ ∀ j : Iio μ, ssDatL j.1 < v → ssP j.1 v = v}
termination_by μ
decreasing_by exact j.2

/-- The set enumerated by `Φ_μ`. -/
def ssC (μ : Ordinal.{0}) : Set Ordinal.{0} :=
  {v | SC v ∧ ssDatL μ < v ∧ ∀ j < μ, ssDatL j < v → ssP j v = v}

theorem ssP_eq (μ : Ordinal.{0}) : ssP μ = enumOrd (ssC μ) := by
  rw [ssP]
  congr 1
  ext v
  simp only [mem_setOf_eq, ssC]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, fun j hj => c ⟨j, hj⟩⟩, fun ⟨a, b, c⟩ => ⟨a, b, fun j => c j.1 j.2⟩⟩

/-- **`Φ_μ` is normal and its range is `ssC μ`.** -/
theorem ssP_props (μ : Ordinal.{0}) : Order.IsNormal (ssP μ) ∧ range (ssP μ) = ssC μ := by
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  -- unbounded
  have hunb : ¬ BddAbove (ssC μ) := by
    rintro ⟨b, hb⟩
    rcases eq_or_ne μ 0 with rfl | hμ0
    · have hv : gamma (b + 1) ∈ ssC 0 :=
        ⟨lq_gamma_SC _, by rw [ssDatL_zero]; exact gamma_pos, fun j hj => absurd hj (not_lt.2 zero_le)⟩
      exact absurd ((lt_add_one b).trans_le (lq_le_gamma _)) (not_lt.2 (hb hv))
    · have h0 : (0 : Ordinal.{0}) < μ := pos_iff_ne_zero.2 hμ0
      set f : Iio μ → Ordinal.{0} → Ordinal.{0} := fun j => ssP j.1 with hf
      have hN : ∀ j : Iio μ, Order.IsNormal (f j) := fun j => (IH j.1 j.2).1
      set v := nfpFamily f (b + ssDatL μ + 1) with hvdef
      have hfix : ∀ j : Iio μ, ssP j.1 v = v := fun j => nfpFamily_fp (hN j) _
      have hle : b + ssDatL μ + 1 ≤ v := le_nfpFamily f _
      have hv0 : v ∈ range (ssP 0) := ⟨v, hfix ⟨0, h0⟩⟩
      rw [(IH 0 h0).2] at hv0
      have hv : v ∈ ssC μ :=
        ⟨hv0.1, (le_add_self.trans_lt (lt_add_one _)).trans_le hle, fun j hj _ => hfix ⟨j, hj⟩⟩
      exact absurd ((le_self_add.trans_lt (lt_add_one _)).trans_le hle) (not_lt.2 (hb hv))
  -- closed under suprema
  have hcl : ∀ t ⊆ ssC μ, t.Nonempty → BddAbove t → sSup t ∈ ssC μ := by
    intro t ht hne hbd
    by_cases hst : sSup t ∈ t
    · exact ht hst
    obtain ⟨v0, hv0⟩ := hne
    have hlt : ∀ v ∈ t, v < sSup t := fun v hv =>
      lt_of_le_of_ne (le_csSup hbd hv) fun e => hst (e ▸ hv)
    refine ⟨Rk.rk_SC_sSup (fun v hv => (ht hv).1) ⟨v0, hv0⟩ hbd,
      (ht hv0).2.1.trans_le (le_csSup hbd hv0), fun j hj hdj => ?_⟩
    set t' := {v ∈ t | ssDatL j < v} with ht'
    obtain ⟨w0, hw0, hjw0⟩ := (lt_csSup_iff hbd ⟨v0, hv0⟩).1 hdj
    have hne' : t'.Nonempty := ⟨w0, hw0, hjw0⟩
    have hbd' : BddAbove t' := hbd.mono fun v hv => hv.1
    have hsup : sSup t' = sSup t := by
      refine le_antisymm (csSup_le_csSup hbd hne' fun v hv => hv.1) (csSup_le ⟨v0, hv0⟩ fun v hv => ?_)
      obtain ⟨w, hw, hvw⟩ := (lt_csSup_iff hbd ⟨v0, hv0⟩).1 (max_lt (hlt v hv) hdj)
      exact (le_max_left _ _ |>.trans (hvw.le)).trans
        (le_csSup hbd' ⟨hw, (le_max_right _ _).trans_lt hvw⟩)
    have hNj := (IH j hj).1
    rw [← hsup, hNj.map_sSup hne' hbd']
    congr 1
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [(ht hv.1).2.2 j hj hv.2]; exact hv
    · intro hy
      exact ⟨y, hy, (ht hy.1).2.2 j hj hy.2⟩
  rw [ssP_eq]
  exact ⟨isNormal_enumOrd hcl hunb, range_enumOrd hunb⟩

theorem ssP_normal (μ : Ordinal.{0}) : Order.IsNormal (ssP μ) := (ssP_props μ).1

theorem ssP_range_eq (μ : Ordinal.{0}) : range (ssP μ) = ssC μ := (ssP_props μ).2

theorem ssP_mem (μ o : Ordinal.{0}) : ssP μ o ∈ ssC μ := by rw [← ssP_range_eq]; exact ⟨o, rfl⟩

theorem ssP_lt_iff (μ : Ordinal.{0}) {a b : Ordinal.{0}} : ssP μ a < ssP μ b ↔ a < b :=
  (ssP_normal μ).strictMono.lt_iff_lt

theorem ssP_le_iff (μ : Ordinal.{0}) {a b : Ordinal.{0}} : ssP μ a ≤ ssP μ b ↔ a ≤ b :=
  (ssP_normal μ).strictMono.le_iff_le

theorem ssP_le_self (μ o : Ordinal.{0}) : o ≤ ssP μ o := (ssP_normal μ).strictMono.le_apply

/-- **The values of `Φ_μ` are strongly critical.** -/
theorem ssP_SC (μ o : Ordinal.{0}) : SC (ssP μ o) := (ssP_mem μ o).1

/-- **The values of `Φ_μ` lie above the data of `μ`.** -/
theorem ssDatL_lt_ssP (μ o : Ordinal.{0}) : ssDatL μ < ssP μ o := (ssP_mem μ o).2.1

/-- **A value `v` of `Φ_μ` is a fixed point of every `Φ_j`, `j < μ`, with `ssDatL j < v`.** -/
theorem ssP_fix_lower {j μ v : Ordinal.{0}} (h : j < μ) (hv : v ∈ range (ssP μ)) (hj : ssDatL j < v) :
    ssP j v = v := by
  rw [ssP_range_eq] at hv; exact hv.2.2 j h hj

/-- **A value of `Φ_μ`**: a strongly critical `v` with `ssDatL μ < v` that is a fixed point of every `Φ_j`, `j < μ`,
`ssDatL j < v`. -/
theorem ssP_range {μ v : Ordinal.{0}} (hSC : SC v) (hμ : ssDatL μ < v)
    (hfix : ∀ j < μ, ssDatL j < v → ssP j v = v) : ∃ e, ssP μ e = v := by
  have : v ∈ range (ssP μ) := by rw [ssP_range_eq]; exact ⟨hSC, hμ, hfix⟩
  exact this

/-- **A fixed point of `Φ_μ` is a fixed point of every `Φ_j`, `j ≤ μ`, with `ssDatL j < x`.** -/
theorem ssP_fix_mono {j μ x : Ordinal.{0}} (h : j ≤ μ) (hx : ssP μ x = x) (hj : ssDatL j < x) : ssP j x = x := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact hx
  · exact ssP_fix_lower hlt ⟨x, hx⟩ hj

/-- **`τ ≤ ssDatL μ` is not a fixed point of `Φ_μ`.** -/
theorem ssP_ne_self_of_dat {μ τ : Ordinal.{0}} (hτ : τ ≤ ssDatL μ) : ssP μ τ ≠ τ := fun h =>
  absurd (hτ.trans_lt (ssDatL_lt_ssP μ τ)) (by rw [h]; exact lt_irrefl _)

/-- A fixed point `p` of `Φ_μ` lies above `ssDatL μ`. -/
theorem ssDatL_lt_fix {μ p : Ordinal.{0}} (hp : ssP μ p = p) : ssDatL μ < p := by
  rw [← hp]; exact ssDatL_lt_ssP μ p

/-- A value of `Φ_μ` is closed under the lower levels. -/
theorem ss_clo_val (μ o : Ordinal.{0}) :
    ∀ j < μ, ssDatL j < ssP μ o → ∀ z < ssP μ o, ssP j z < ssP μ o := fun j hj hd z hz => by
  have h := (ssP_lt_iff j).2 hz
  rwa [ssP_fix_lower hj ⟨o, rfl⟩ hd] at h


/-! ## Agreement with `Rk.rkP` up to `ε_{Ω₁+1}` -/

/-- **`ssDatL μ = rkDat μ` for `μ < ε_{Ω₁+1}`.** -/
theorem ssDatL_eq {μ : Ordinal.{0}} (hμ : μ < ggE) : ssDatL μ = Rk.rkDat μ := by
  unfold ssDatL Rk.rkDat
  exact ssDat_eq_rj _ (Rk.rk_Om1_add_lt hμ)

/-- **`ssDatL ε_{Ω₁+1} = 1`**: `ε_{Ω₁+1} = φ(1, Ω₁ + 1)` has the leaf `1`. -/
theorem ssDatL_E : ssDatL ggE = 1 := by
  unfold ssDatL
  rw [ss_Om1_add_E]
  have hE : ω ^ ggE = ggE := Rk.rk_E_inE
  have hG : ggE < ggGam := by
    refine lt_of_le_of_ne ggE_le_ggGam fun e => ?_
    have hSC : SC ggE := e ▸ ggGam_spec.1
    have h2 : Om 1 + 1 < ggE := (ev_isSuccLimit_of_inE Rk.rk_E_inE).add_one_lt Rk.rk_Om1_E
    have := hSC.2 1 (gg_one_lt_of_SC hSC) (Om 1 + 1) h2
    rw [← Rk.rk_E_eq] at this
    exact lt_irrefl _ this
  have hv : Om 1 + 1 < veblen 1 (Om 1 + 1) := by
    rw [← Rk.rk_E_eq]; exact (ev_isSuccLimit_of_inE Rk.rk_E_inE).add_one_lt Rk.rk_Om1_E
  rw [ssDat_eq_phi rj_Om1_lt_E hG hE]
  conv_lhs => rw [Rk.rk_E_eq]
  rw [invVeblen₁_veblen hv, invVeblen₂_veblen one_ne_zero hv, ← rj_Om1]
  have h1 : (1 : Ordinal.{0}) < Om1 := by rw [rj_Om1]; exact gg_one_lt_of_SC (SC_Om one_ne_zero)
  have hO1 : Om1 + 1 < ggE := Rk.rk_E_inE.add_lt rj_Om1_lt_E (h1.trans rj_Om1_lt_E)
  rw [ssDat_small h1, ssDat_eq_rj _ hO1, rjDat_Om1_add one_ne_zero h1, max_self]

/-- **`ssP μ = Rk.rkP μ` for every `μ ≤ ε_{Ω₁+1}`.** -/
theorem ssP_eq_rkP : ∀ μ : Ordinal.{0}, μ ≤ ggE → ssP μ = Rk.rkP μ := by
  intro μ
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμ
  rw [ssP_eq, Rk.rkP_eq]
  congr 1
  ext v
  simp only [ssC, Rk.rkC, mem_setOf_eq]
  have hdat : ∀ w, SC w → (ssDatL μ < w ↔ Rk.rkDat μ < w) := by
    intro w hw
    rcases lt_or_eq_of_le hμ with hlt | rfl
    · rw [ssDatL_eq hlt]
    · rw [ssDatL_E, ssDatE]
      exact ⟨fun _ => hw.1, fun _ => gg_one_lt_of_SC hw⟩
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, (hdat v h1).1 h2, fun j hj hd => ?_⟩
    have hjE : j < ggE := hj.trans_le hμ
    rw [← IH j hj hjE.le]; exact h3 j hj (by rw [ssDatL_eq hjE]; exact hd)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, (hdat v h1).2 h2, fun j hj hd => ?_⟩
    have hjE : j < ggE := hj.trans_le hμ
    rw [IH j hj hjE.le]; exact h3 j hj (by rw [← ssDatL_eq hjE]; exact hd)

end Googology.Trans.PoR.InaccPsi.R2.Ss
