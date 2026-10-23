import Googology.Trans.PoR.InaccPsi.R2.RkCode
import Googology.Trans.PoR.InaccPsi.R2.RiFn

/-!
# The levels `Φ_μ` for every `μ`, generic in the level: the hierarchy above the `Ω₁·Ω₁` levels of `R2.RiFn`

`rkDat μ = rjDat (Ω₁ + μ)` (`Rk.rkDat`).  The level `μ` is the level of the `ϑᵗ`-terms `ϑᵗ(Ω₁·(Ω₁ + μ) + η)`.

* `rkP μ` (**the `μ`-th level**, by well-founded recursion on `μ`): the enumeration (`Ordinal.enumOrd`) of the set
  `rkC μ` of the strongly critical `v` with `rkDat μ < v` that are fixed points of every `Φ_j`, `j < μ`, with
  `rkDat j < v`;
* `rkP_props` (**`Φ_μ` is normal and its range is `rkC μ`**: `rkC μ` is closed under suprema, since the lower levels
  are normal, and unbounded, by `Ordinal.nfpFamily` of the lower levels); `rkP_zero` (**`Φ_0 = Γ_`**);
* `rkP_SC`, `rkDat_lt_rkP` (**the values lie above the data**), `rkP_fix_lower` (**a value `v` of `Φ_μ` is a fixed
  point of every `Φ_j`, `j < μ`, `rkDat j < v`**), `rkP_range` (**a strongly critical `v > rkDat μ` that is a fixed
  point of every `Φ_j`, `j < μ`, `rkDat j < v`, is a value of `Φ_μ`**), `rkP_fix_mono`, `rkP_ne_self_of_dat`.

No new axiom.  New definitions: `rkP`, `rkC`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rh

/-- **The `μ`-th level** `Φ_μ`: the enumeration of the strongly critical `v > rkDat μ` that are fixed points of every
`Φ_j`, `j < μ`, with `rkDat j < v`. -/
noncomputable def rkP (μ : Ordinal.{0}) : Ordinal.{0} → Ordinal.{0} :=
  enumOrd {v | SC v ∧ rkDat μ < v ∧ ∀ j : Iio μ, rkDat j.1 < v → rkP j.1 v = v}
termination_by μ
decreasing_by exact j.2

/-- The set enumerated by `Φ_μ`. -/
def rkC (μ : Ordinal.{0}) : Set Ordinal.{0} :=
  {v | SC v ∧ rkDat μ < v ∧ ∀ j < μ, rkDat j < v → rkP j v = v}

theorem rkP_eq (μ : Ordinal.{0}) : rkP μ = enumOrd (rkC μ) := by
  rw [rkP]
  congr 1
  ext v
  simp only [mem_setOf_eq, rkC]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, fun j hj => c ⟨j, hj⟩⟩, fun ⟨a, b, c⟩ => ⟨a, b, fun j => c j.1 j.2⟩⟩

theorem rk_SC_sSup {t : Set Ordinal.{0}} (ht : ∀ v ∈ t, SC v) (hne : t.Nonempty) (hb : BddAbove t) :
    SC (sSup t) := by
  obtain ⟨v0, hv0⟩ := hne
  refine ⟨(ht v0 hv0).1.trans_le (le_csSup hb hv0), fun a ha b hb' => ?_⟩
  obtain ⟨v1, hv1, hav⟩ := (lt_csSup_iff hb ⟨v0, hv0⟩).1 ha
  obtain ⟨v2, hv2, hbv⟩ := (lt_csSup_iff hb ⟨v0, hv0⟩).1 hb'
  rcases le_total v1 v2 with h | h
  · exact ((ht v2 hv2).2 a (hav.trans_le h) b hbv).trans_le (le_csSup hb hv2)
  · exact ((ht v1 hv1).2 a hav b (hbv.trans_le h)).trans_le (le_csSup hb hv1)

/-- **`Φ_μ` is normal and its range is `rkC μ`.** -/
theorem rkP_props (μ : Ordinal.{0}) : Order.IsNormal (rkP μ) ∧ range (rkP μ) = rkC μ := by
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  -- unbounded
  have hunb : ¬ BddAbove (rkC μ) := by
    rintro ⟨b, hb⟩
    rcases eq_or_ne μ 0 with rfl | hμ0
    · have hv : gamma (b + 1) ∈ rkC 0 :=
        ⟨lq_gamma_SC _, by rw [rkDat_zero]; exact gamma_pos, fun j hj => absurd hj (not_lt.2 zero_le)⟩
      exact absurd ((lt_add_one b).trans_le (lq_le_gamma _)) (not_lt.2 (hb hv))
    · have h0 : (0 : Ordinal.{0}) < μ := pos_iff_ne_zero.2 hμ0
      set f : Iio μ → Ordinal.{0} → Ordinal.{0} := fun j => rkP j.1 with hf
      have hN : ∀ j : Iio μ, Order.IsNormal (f j) := fun j => (IH j.1 j.2).1
      set v := nfpFamily f (b + rkDat μ + 1) with hvdef
      have hfix : ∀ j : Iio μ, rkP j.1 v = v := fun j => nfpFamily_fp (hN j) _
      have hle : b + rkDat μ + 1 ≤ v := le_nfpFamily f _
      have hv0 : v ∈ range (rkP 0) := ⟨v, hfix ⟨0, h0⟩⟩
      rw [(IH 0 h0).2] at hv0
      have hv : v ∈ rkC μ :=
        ⟨hv0.1, (le_add_self.trans_lt (lt_add_one _)).trans_le hle, fun j hj _ => hfix ⟨j, hj⟩⟩
      exact absurd ((le_self_add.trans_lt (lt_add_one _)).trans_le hle) (not_lt.2 (hb hv))
  -- closed under suprema
  have hcl : ∀ t ⊆ rkC μ, t.Nonempty → BddAbove t → sSup t ∈ rkC μ := by
    intro t ht hne hbd
    by_cases hst : sSup t ∈ t
    · exact ht hst
    obtain ⟨v0, hv0⟩ := hne
    have hlt : ∀ v ∈ t, v < sSup t := fun v hv =>
      lt_of_le_of_ne (le_csSup hbd hv) fun e => hst (e ▸ hv)
    refine ⟨rk_SC_sSup (fun v hv => (ht hv).1) ⟨v0, hv0⟩ hbd,
      (ht hv0).2.1.trans_le (le_csSup hbd hv0), fun j hj hdj => ?_⟩
    set t' := {v ∈ t | rkDat j < v} with ht'
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
  rw [rkP_eq]
  exact ⟨isNormal_enumOrd hcl hunb, range_enumOrd hunb⟩

theorem rkP_normal (μ : Ordinal.{0}) : Order.IsNormal (rkP μ) := (rkP_props μ).1

theorem rkP_range_eq (μ : Ordinal.{0}) : range (rkP μ) = rkC μ := (rkP_props μ).2

theorem rkP_mem (μ o : Ordinal.{0}) : rkP μ o ∈ rkC μ := by rw [← rkP_range_eq]; exact ⟨o, rfl⟩

theorem rkP_lt_iff (μ : Ordinal.{0}) {a b : Ordinal.{0}} : rkP μ a < rkP μ b ↔ a < b :=
  (rkP_normal μ).strictMono.lt_iff_lt

theorem rkP_le_iff (μ : Ordinal.{0}) {a b : Ordinal.{0}} : rkP μ a ≤ rkP μ b ↔ a ≤ b :=
  (rkP_normal μ).strictMono.le_iff_le

theorem rkP_le_self (μ o : Ordinal.{0}) : o ≤ rkP μ o := (rkP_normal μ).strictMono.le_apply

/-- **The values of `Φ_μ` are strongly critical.** -/
theorem rkP_SC (μ o : Ordinal.{0}) : SC (rkP μ o) := (rkP_mem μ o).1

/-- **The values of `Φ_μ` lie above the data of `μ`.** -/
theorem rkDat_lt_rkP (μ o : Ordinal.{0}) : rkDat μ < rkP μ o := (rkP_mem μ o).2.1

/-- **A value `v` of `Φ_μ` is a fixed point of every `Φ_j`, `j < μ`, with `rkDat j < v`.** -/
theorem rkP_fix_lower {j μ v : Ordinal.{0}} (h : j < μ) (hv : v ∈ range (rkP μ)) (hj : rkDat j < v) :
    rkP j v = v := by
  rw [rkP_range_eq] at hv; exact hv.2.2 j h hj

/-- **A value of `Φ_μ`**: a strongly critical `v` with `rkDat μ < v` that is a fixed point of every `Φ_j`, `j < μ`,
`rkDat j < v`. -/
theorem rkP_range {μ v : Ordinal.{0}} (hSC : SC v) (hμ : rkDat μ < v)
    (hfix : ∀ j < μ, rkDat j < v → rkP j v = v) : ∃ e, rkP μ e = v := by
  have : v ∈ range (rkP μ) := by rw [rkP_range_eq]; exact ⟨hSC, hμ, hfix⟩
  exact this

/-- **A fixed point of `Φ_μ` is a fixed point of every `Φ_j`, `j ≤ μ`, with `rkDat j < x`.** -/
theorem rkP_fix_mono {j μ x : Ordinal.{0}} (h : j ≤ μ) (hx : rkP μ x = x) (hj : rkDat j < x) : rkP j x = x := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact hx
  · exact rkP_fix_lower hlt ⟨x, hx⟩ hj

/-- **`Φ_0 = Γ_`.** -/
theorem rkP_zero : rkP 0 = gamma := by
  have hC : rkC 0 = range gamma := by
    ext v
    refine ⟨fun hv => lq_SC_gamma hv.1, ?_⟩
    rintro ⟨e, rfl⟩
    exact ⟨lq_gamma_SC e, by rw [rkDat_zero]; exact gamma_pos,
      fun j hj => absurd hj (not_lt.2 zero_le)⟩
  rw [rkP_eq, hC, enumOrd_range isNormal_gamma.strictMono]

/-- **`τ ≤ rkDat μ` is not a fixed point of `Φ_μ`.** -/
theorem rkP_ne_self_of_dat {μ τ : Ordinal.{0}} (hτ : τ ≤ rkDat μ) : rkP μ τ ≠ τ := fun h =>
  absurd (hτ.trans_lt (rkDat_lt_rkP μ τ)) (by rw [h]; exact lt_irrefl _)

/-- A fixed point `p` of `Φ_μ` lies above `rkDat μ`. -/
theorem rkDat_lt_fix {μ p : Ordinal.{0}} (hp : rkP μ p = p) : rkDat μ < p := by
  rw [← hp]; exact rkDat_lt_rkP μ p

/-- A value of `Φ_μ` is closed under the lower levels. -/
theorem rk_clo_val (μ o : Ordinal.{0}) :
    ∀ j < μ, rkDat j < rkP μ o → ∀ z < rkP μ o, rkP j z < rkP μ o := fun j hj hd z hz => by
  have h := (rkP_lt_iff j).2 hz
  rwa [rkP_fix_lower hj ⟨o, rfl⟩ hd] at h

end Googology.Trans.PoR.InaccPsi.R2.Rk
