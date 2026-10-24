import Googology.Trans.PoR.InaccPsi.R2.TlCit
import Googology.Trans.PoR.InaccPsi.R2.TlCl

/-!
# The levels `Φ_μ` on the data `Tl.tlDatL`, for every `μ < X`

`tlDatL μ = Tl.tlDat (Ω₁ + μ)` (**the data of the level `μ`** on the normal forms over `Ω₁` and the atoms `F_β(y)`,
`R2.TlDat`), `X = Tl.tlX`, `B_Γ = Tf.tfBG`.  `Tf.tfP` (the levels on `Tf.tfDatL`) is correct below `B_Γ` only
(`Tf.tfDat` is the junk value `0` from `B_Γ` on).  The same definition on the data `tlDatL`:

* `tlP μ` (**the `μ`-th level**: the enumeration of the strongly critical `v > tlDatL μ` that are fixed points of
  every `tlP j`, `j < μ`, with `tlDatL j < v`), `tlP_props` (**`Φ_μ` is normal**), `tlP_SC`, `tlDatL_lt_tlP`,
  `tlP_fix_lower`, `tlP_range`, `tlP_fix_mono`, `tlP_ne_self_of_dat`, `tlDatL_lt_fix`, `tl_clo_val`;
* `tlP_eq_tfP` (**`tlP μ = Tf.tfP μ` for every `μ < B_Γ`**: the new hierarchy extends the old one), `tlP_zero_eq`
  (`Φ₀ = Γ`);
* `tl_code_lvlL` (**`tlDatL μ < b` makes `μ < X` a code over the strongly critical `b`**).

No new axiom.  New definitions: `tlP`, `tlC`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tl

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb
  Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Ri
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Rk
  Googology.Trans.PoR.InaccPsi.R2.Tf

theorem tlDatL_zero : tlDatL 0 = 0 := by unfold tlDatL; rw [add_zero, tlDat_Om1]

/-- **The `μ`-th level** `Φ_μ`: the enumeration of the strongly critical `v > tlDatL μ` that are fixed points of every
`Φ_j`, `j < μ`, with `tlDatL j < v`. -/
noncomputable def tlP (μ : Ordinal.{0}) : Ordinal.{0} → Ordinal.{0} :=
  enumOrd {v | SC v ∧ tlDatL μ < v ∧ ∀ j : Iio μ, tlDatL j.1 < v → tlP j.1 v = v}
termination_by μ
decreasing_by exact j.2

/-- The set enumerated by `Φ_μ`. -/
def tlC (μ : Ordinal.{0}) : Set Ordinal.{0} :=
  {v | SC v ∧ tlDatL μ < v ∧ ∀ j < μ, tlDatL j < v → tlP j v = v}

theorem tlP_eq (μ : Ordinal.{0}) : tlP μ = enumOrd (tlC μ) := by
  rw [tlP]
  congr 1
  ext v
  simp only [mem_setOf_eq, tlC]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, fun j hj => c ⟨j, hj⟩⟩, fun ⟨a, b, c⟩ => ⟨a, b, fun j => c j.1 j.2⟩⟩

/-- **`Φ_μ` is normal and its range is `tlC μ`.** -/
theorem tlP_props (μ : Ordinal.{0}) : Order.IsNormal (tlP μ) ∧ range (tlP μ) = tlC μ := by
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  -- unbounded
  have hunb : ¬ BddAbove (tlC μ) := by
    rintro ⟨b, hb⟩
    rcases eq_or_ne μ 0 with rfl | hμ0
    · have hv : gamma (b + 1) ∈ tlC 0 :=
        ⟨lq_gamma_SC _, by rw [tlDatL_zero]; exact gamma_pos, fun j hj => absurd hj (not_lt.2 zero_le)⟩
      exact absurd ((lt_add_one b).trans_le (lq_le_gamma _)) (not_lt.2 (hb hv))
    · have h0 : (0 : Ordinal.{0}) < μ := pos_iff_ne_zero.2 hμ0
      set f : Iio μ → Ordinal.{0} → Ordinal.{0} := fun j => tlP j.1 with hf
      have hN : ∀ j : Iio μ, Order.IsNormal (f j) := fun j => (IH j.1 j.2).1
      set v := nfpFamily f (b + tlDatL μ + 1) with hvdef
      have hfix : ∀ j : Iio μ, tlP j.1 v = v := fun j => nfpFamily_fp (hN j) _
      have hle : b + tlDatL μ + 1 ≤ v := le_nfpFamily f _
      have hv0 : v ∈ range (tlP 0) := ⟨v, hfix ⟨0, h0⟩⟩
      rw [(IH 0 h0).2] at hv0
      have hv : v ∈ tlC μ :=
        ⟨hv0.1, (le_add_self.trans_lt (lt_add_one _)).trans_le hle, fun j hj _ => hfix ⟨j, hj⟩⟩
      exact absurd ((le_self_add.trans_lt (lt_add_one _)).trans_le hle) (not_lt.2 (hb hv))
  -- closed under suprema
  have hcl : ∀ t ⊆ tlC μ, t.Nonempty → BddAbove t → sSup t ∈ tlC μ := by
    intro t ht hne hbd
    by_cases hst : sSup t ∈ t
    · exact ht hst
    obtain ⟨v0, hv0⟩ := hne
    have hlt : ∀ v ∈ t, v < sSup t := fun v hv =>
      lt_of_le_of_ne (le_csSup hbd hv) fun e => hst (e ▸ hv)
    refine ⟨Rk.rk_SC_sSup (fun v hv => (ht hv).1) ⟨v0, hv0⟩ hbd,
      (ht hv0).2.1.trans_le (le_csSup hbd hv0), fun j hj hdj => ?_⟩
    set t' := {v ∈ t | tlDatL j < v} with ht'
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
  rw [tlP_eq]
  exact ⟨isNormal_enumOrd hcl hunb, range_enumOrd hunb⟩

theorem tlP_normal (μ : Ordinal.{0}) : Order.IsNormal (tlP μ) := (tlP_props μ).1

theorem tlP_range_eq (μ : Ordinal.{0}) : range (tlP μ) = tlC μ := (tlP_props μ).2

theorem tlP_mem (μ o : Ordinal.{0}) : tlP μ o ∈ tlC μ := by rw [← tlP_range_eq]; exact ⟨o, rfl⟩

theorem tlP_lt_iff (μ : Ordinal.{0}) {a b : Ordinal.{0}} : tlP μ a < tlP μ b ↔ a < b :=
  (tlP_normal μ).strictMono.lt_iff_lt

theorem tlP_le_iff (μ : Ordinal.{0}) {a b : Ordinal.{0}} : tlP μ a ≤ tlP μ b ↔ a ≤ b :=
  (tlP_normal μ).strictMono.le_iff_le

theorem tlP_le_self (μ o : Ordinal.{0}) : o ≤ tlP μ o := (tlP_normal μ).strictMono.le_apply

/-- **The values of `Φ_μ` are strongly critical.** -/
theorem tlP_SC (μ o : Ordinal.{0}) : SC (tlP μ o) := (tlP_mem μ o).1

/-- **The values of `Φ_μ` lie above the data of `μ`.** -/
theorem tlDatL_lt_tlP (μ o : Ordinal.{0}) : tlDatL μ < tlP μ o := (tlP_mem μ o).2.1

/-- **A value `v` of `Φ_μ` is a fixed point of every `Φ_j`, `j < μ`, with `tlDatL j < v`.** -/
theorem tlP_fix_lower {j μ v : Ordinal.{0}} (h : j < μ) (hv : v ∈ range (tlP μ)) (hj : tlDatL j < v) :
    tlP j v = v := by
  rw [tlP_range_eq] at hv; exact hv.2.2 j h hj

/-- **A value of `Φ_μ`**: a strongly critical `v` with `tlDatL μ < v` that is a fixed point of every `Φ_j`, `j < μ`,
`tlDatL j < v`. -/
theorem tlP_range {μ v : Ordinal.{0}} (hSC : SC v) (hμ : tlDatL μ < v)
    (hfix : ∀ j < μ, tlDatL j < v → tlP j v = v) : ∃ e, tlP μ e = v := by
  have : v ∈ range (tlP μ) := by rw [tlP_range_eq]; exact ⟨hSC, hμ, hfix⟩
  exact this

/-- **A fixed point of `Φ_μ` is a fixed point of every `Φ_j`, `j ≤ μ`, with `tlDatL j < x`.** -/
theorem tlP_fix_mono {j μ x : Ordinal.{0}} (h : j ≤ μ) (hx : tlP μ x = x) (hj : tlDatL j < x) : tlP j x = x := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact hx
  · exact tlP_fix_lower hlt ⟨x, hx⟩ hj

/-- **`τ ≤ tlDatL μ` is not a fixed point of `Φ_μ`.** -/
theorem tlP_ne_self_of_dat {μ τ : Ordinal.{0}} (hτ : τ ≤ tlDatL μ) : tlP μ τ ≠ τ := fun h =>
  absurd (hτ.trans_lt (tlDatL_lt_tlP μ τ)) (by rw [h]; exact lt_irrefl _)

/-- A fixed point `p` of `Φ_μ` lies above `tlDatL μ`. -/
theorem tlDatL_lt_fix {μ p : Ordinal.{0}} (hp : tlP μ p = p) : tlDatL μ < p := by
  rw [← hp]; exact tlDatL_lt_tlP μ p

/-- A value of `Φ_μ` is closed under the lower levels. -/
theorem tl_clo_val (μ o : Ordinal.{0}) :
    ∀ j < μ, tlDatL j < tlP μ o → ∀ z < tlP μ o, tlP j z < tlP μ o := fun j hj hd z hz => by
  have h := (tlP_lt_iff j).2 hz
  rwa [tlP_fix_lower hj ⟨o, rfl⟩ hd] at h




/-! ## Agreement with `Tf.tfP` below `B_Γ` -/

/-- **`tlP μ = Tf.tfP μ` for every `μ < B_Γ`.** -/
theorem tlP_eq_tfP : ∀ μ : Ordinal.{0}, μ < tfBG → tlP μ = tfP μ := by
  intro μ
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμ
  rw [tlP_eq, tfP_eq]
  congr 1
  ext v
  simp only [tlC, tfC, mem_setOf_eq]
  rw [tlDatL_eq_tf hμ]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun j hj hd => ?_⟩
    rw [← IH j hj (hj.trans hμ)]; exact h3 j hj (by rw [tlDatL_eq_tf (hj.trans hμ)]; exact hd)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun j hj hd => ?_⟩
    rw [IH j hj (hj.trans hμ)]; exact h3 j hj (by rw [← tlDatL_eq_tf (hj.trans hμ)]; exact hd)

/-- `Φ₀ = Γ`. -/
theorem tlP_zero_eq : tlP 0 = gamma := by
  rw [tlP_eq_tfP 0 (rj_Om1_pos.trans tfBG_gt), tfP_zero_eq]

/-- **`tlDatL μ < b` makes `μ < X` a code over a strongly critical `b`.** -/
theorem tl_code_lvlL {μ b : Ordinal.{0}} (hb : SC b) (hμ : μ < tlX) (hd : tlDatL μ < b) : TlCl b μ :=
  tl_code_lvl hb hμ hd

end Googology.Trans.PoR.InaccPsi.R2.Tl
