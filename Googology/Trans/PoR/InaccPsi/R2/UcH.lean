import Googology.Trans.PoR.InaccPsi.R2.UcCmp

/-!
# The hierarchy `H_γ` of the levels `γ < ε_{Ω₂+1}`, and `H_β = F_β` above `max(Ω₁, β)` for `β < Ω₂`

`Ω₂ = OmTwo`, `E₂ = Uc.ucE = ε_{Ω₂+1}`, `ucC γ` the largest base-`Ω₂` component of `γ` (`R2.UcCmp`), `F_β = Rh.rhF β =
veblenWith Γ β`.  A generic hierarchy on a data function `d` and a floor `L`:

* `ucG d L μ` (**the `μ`-th level**: the enumeration of the strongly critical `v > L` with `d μ < v` that are fixed
  points of every `ucG d L j`, `j < μ`, with `d j < v`), `ucG_props` (**normal**, range `ucGC d L μ`), `ucG_SC`,
  `ucG_L_lt`, `ucG_d_lt`, `ucG_fix_lower`, `ucG_range`, `ucG_fix_mono`, `ucG_lt_iff`, `ucG_le_iff`, `ucG_le_self`,
  `ucG_fix_succ` (a fixed point of level `γ` is a value of level `γ + 1`), `ucG_ne_self`;
* `ucH γ := ucG ucC Ω₁ γ` (**the levels one cardinal up**: values `> Ω₁`, all components of `γ` below the value);
* `uc_range_F` (**for `β < Ω₂` and `v > max(Ω₁, β)`: `v ∈ ran H_β ↔ v ∈ ran F_β`**), `ucS` (the start: the least `s`
  with `F_β(s) > max(Ω₁, β)`), `ucH_eq_F` (**`H_β(y) = F_β(s_β + y)`**), `ucH_fix_iff_F` (**`H_β(v) = v ↔ F_β(v) = v`
  for `v > max(Ω₁, β)`**).

No new axiom.  New definitions: `ucG`, `ucGC`, `ucH`, `ucS`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Rh

/-- **The generic `μ`-th level** on a data function `d` and a floor `L`. -/
noncomputable def ucG (d : Ordinal.{0} → Ordinal.{0}) (L : Ordinal.{0}) (μ : Ordinal.{0}) :
    Ordinal.{0} → Ordinal.{0} :=
  enumOrd {v | SC v ∧ L < v ∧ d μ < v ∧ ∀ j : Iio μ, d j.1 < v → ucG d L j.1 v = v}
termination_by μ
decreasing_by exact j.2

/-- The set enumerated by `ucG d L μ`. -/
def ucGC (d : Ordinal.{0} → Ordinal.{0}) (L : Ordinal.{0}) (μ : Ordinal.{0}) : Set Ordinal.{0} :=
  {v | SC v ∧ L < v ∧ d μ < v ∧ ∀ j < μ, d j < v → ucG d L j v = v}

variable {d : Ordinal.{0} → Ordinal.{0}} {L : Ordinal.{0}}

/-- A bounded nonempty set of strongly critical ordinals has a strongly critical supremum. -/
theorem uc_SC_sSup {t : Set Ordinal.{0}} (ht : ∀ v ∈ t, SC v) (hne : t.Nonempty) (hb : BddAbove t) :
    SC (sSup t) := by
  obtain ⟨v0, hv0⟩ := hne
  refine ⟨(ht v0 hv0).1.trans_le (le_csSup hb hv0), fun a ha b hb' => ?_⟩
  obtain ⟨v1, hv1, hav⟩ := (lt_csSup_iff hb ⟨v0, hv0⟩).1 ha
  obtain ⟨v2, hv2, hbv⟩ := (lt_csSup_iff hb ⟨v0, hv0⟩).1 hb'
  rcases le_total v1 v2 with h | h
  · exact ((ht v2 hv2).2 a (hav.trans_le h) b hbv).trans_le (le_csSup hb hv2)
  · exact ((ht v1 hv1).2 a hav b (hbv.trans_le h)).trans_le (le_csSup hb hv1)

theorem ucG_eq (μ : Ordinal.{0}) : ucG d L μ = enumOrd (ucGC d L μ) := by
  rw [ucG]
  congr 1
  ext v
  simp only [mem_setOf_eq, ucGC]
  exact ⟨fun ⟨a, b, c, e⟩ => ⟨a, b, c, fun j hj => e ⟨j, hj⟩⟩,
    fun ⟨a, b, c, e⟩ => ⟨a, b, c, fun j => e j.1 j.2⟩⟩

/-- **`ucG d L μ` is normal and its range is `ucGC d L μ`.** -/
theorem ucG_props (μ : Ordinal.{0}) : Order.IsNormal (ucG d L μ) ∧ range (ucG d L μ) = ucGC d L μ := by
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  have hunb : ¬ BddAbove (ucGC d L μ) := by
    rintro ⟨b, hb⟩
    rcases eq_or_ne μ 0 with rfl | hμ0
    · have hw : b + L + d 0 + 1 ≤ gamma (b + L + d 0 + 1) := Lq.lq_le_gamma _
      have h1 : b + L ≤ b + L + d 0 := le_self_add
      have hL : L < gamma (b + L + d 0 + 1) := ((le_add_self.trans h1).trans_lt (lt_add_one _)).trans_le hw
      have hd : d 0 < gamma (b + L + d 0 + 1) := (le_add_self.trans_lt (lt_add_one _)).trans_le hw
      have hb' : b < gamma (b + L + d 0 + 1) := ((le_self_add.trans h1).trans_lt (lt_add_one _)).trans_le hw
      have hv : gamma (b + L + d 0 + 1) ∈ ucGC d L 0 :=
        ⟨Lq.lq_gamma_SC _, hL, hd, fun j hj => absurd hj (not_lt.2 zero_le)⟩
      exact absurd hb' (not_lt.2 (hb hv))
    · have h0 : (0 : Ordinal.{0}) < μ := pos_iff_ne_zero.2 hμ0
      set f : Iio μ → Ordinal.{0} → Ordinal.{0} := fun j => ucG d L j.1 with hf
      have hN : ∀ j : Iio μ, Order.IsNormal (f j) := fun j => (IH j.1 j.2).1
      set v := nfpFamily f (b + L + d μ + 1) with hvdef
      have hfix : ∀ j : Iio μ, ucG d L j.1 v = v := fun j => nfpFamily_fp (hN j) _
      have hle : b + L + d μ + 1 ≤ v := le_nfpFamily f _
      have hv0 : v ∈ range (ucG d L 0) := ⟨v, hfix ⟨0, h0⟩⟩
      rw [(IH 0 h0).2] at hv0
      have hLv : L < v := ((le_add_self.trans le_self_add).trans_lt (lt_add_one _)).trans_le hle
      have hdv : d μ < v := (le_add_self.trans_lt (lt_add_one _)).trans_le hle
      have hv : v ∈ ucGC d L μ := ⟨hv0.1, hLv, hdv, fun j hj _ => hfix ⟨j, hj⟩⟩
      exact absurd (((le_self_add.trans le_self_add).trans_lt (lt_add_one _)).trans_le hle)
        (not_lt.2 (hb hv))
  have hcl : ∀ t ⊆ ucGC d L μ, t.Nonempty → BddAbove t → sSup t ∈ ucGC d L μ := by
    intro t ht hne hbd
    by_cases hst : sSup t ∈ t
    · exact ht hst
    obtain ⟨v0, hv0⟩ := hne
    have hlt : ∀ v ∈ t, v < sSup t := fun v hv =>
      lt_of_le_of_ne (le_csSup hbd hv) fun e => hst (e ▸ hv)
    refine ⟨uc_SC_sSup (fun v hv => (ht hv).1) ⟨v0, hv0⟩ hbd,
      (ht hv0).2.1.trans_le (le_csSup hbd hv0), (ht hv0).2.2.1.trans_le (le_csSup hbd hv0),
      fun j hj hdj => ?_⟩
    set t' := {v ∈ t | d j < v} with ht'
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
      rw [(ht hv.1).2.2.2 j hj hv.2]; exact hv
    · intro hy
      exact ⟨y, hy, (ht hy.1).2.2.2 j hj hy.2⟩
  rw [ucG_eq]
  exact ⟨isNormal_enumOrd hcl hunb, range_enumOrd hunb⟩

theorem ucG_normal (μ : Ordinal.{0}) : Order.IsNormal (ucG d L μ) := (ucG_props μ).1

theorem ucG_range_eq (μ : Ordinal.{0}) : range (ucG d L μ) = ucGC d L μ := (ucG_props μ).2

theorem ucG_mem (μ o : Ordinal.{0}) : ucG d L μ o ∈ ucGC d L μ := by rw [← ucG_range_eq]; exact ⟨o, rfl⟩

theorem ucG_lt_iff (μ : Ordinal.{0}) {a b : Ordinal.{0}} : ucG d L μ a < ucG d L μ b ↔ a < b :=
  (ucG_normal μ).strictMono.lt_iff_lt

theorem ucG_le_iff (μ : Ordinal.{0}) {a b : Ordinal.{0}} : ucG d L μ a ≤ ucG d L μ b ↔ a ≤ b :=
  (ucG_normal μ).strictMono.le_iff_le

theorem ucG_le_self (μ o : Ordinal.{0}) : o ≤ ucG d L μ o := (ucG_normal μ).strictMono.le_apply

theorem ucG_SC (μ o : Ordinal.{0}) : SC (ucG d L μ o) := (ucG_mem μ o).1

theorem ucG_L_lt (μ o : Ordinal.{0}) : L < ucG d L μ o := (ucG_mem μ o).2.1

theorem ucG_d_lt (μ o : Ordinal.{0}) : d μ < ucG d L μ o := (ucG_mem μ o).2.2.1

/-- **A value `v` of level `μ` is a fixed point of every level `j < μ` with `d j < v`.** -/
theorem ucG_fix_lower {j μ v : Ordinal.{0}} (h : j < μ) (hv : v ∈ range (ucG d L μ)) (hj : d j < v) :
    ucG d L j v = v := by
  rw [ucG_range_eq] at hv; exact hv.2.2.2 j h hj

/-- **The values of level `μ`**: the strongly critical `v > L`, `d μ < v`, fixed by every lower level `j` with
`d j < v`. -/
theorem ucG_range {μ v : Ordinal.{0}} (hSC : SC v) (hL : L < v) (hμ : d μ < v)
    (hfix : ∀ j < μ, d j < v → ucG d L j v = v) : ∃ e, ucG d L μ e = v := by
  have : v ∈ range (ucG d L μ) := by rw [ucG_range_eq]; exact ⟨hSC, hL, hμ, hfix⟩
  exact this

theorem ucG_fix_mono {j μ x : Ordinal.{0}} (h : j ≤ μ) (hx : ucG d L μ x = x) (hj : d j < x) :
    ucG d L j x = x := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact hx
  · exact ucG_fix_lower hlt ⟨x, hx⟩ hj

/-- **A fixed point of level `γ` is a value of level `γ + 1`** (when `d (γ + 1)` is below it). -/
theorem ucG_fix_succ {γ v : Ordinal.{0}} (hv : ucG d L γ v = v) (hd : d (γ + 1) < v) :
    ∃ e, ucG d L (γ + 1) e = v := by
  have hm := ucG_mem (d := d) (L := L) γ v
  rw [hv] at hm
  refine ucG_range hm.1 hm.2.1 hd fun j hj hdj => ?_
  rcases eq_or_lt_of_le (Order.lt_add_one_iff.1 hj) with rfl | hlt
  · exact hv
  · exact hm.2.2.2 j hlt hdj

theorem ucG_ne_self {μ τ : Ordinal.{0}} (hτ : τ ≤ d μ) : ucG d L μ τ ≠ τ := fun h =>
  absurd (hτ.trans_lt (ucG_d_lt μ τ)) (by rw [h]; exact lt_irrefl _)

/-! ## The levels one cardinal up -/

/-- **`H_γ`**: the levels `γ < E₂` with the data `ucC` (largest component) and the floor `Ω₁`. -/
noncomputable def ucH (γ : Ordinal.{0}) : Ordinal.{0} → Ordinal.{0} := ucG ucC Om1 γ

theorem ucH_SC (γ o : Ordinal.{0}) : SC (ucH γ o) := ucG_SC γ o

theorem ucH_gt (γ o : Ordinal.{0}) : Om1 < ucH γ o := ucG_L_lt γ o

theorem ucH_C_lt (γ o : Ordinal.{0}) : ucC γ < ucH γ o := ucG_d_lt γ o

theorem ucH_lt_iff (γ : Ordinal.{0}) {a b : Ordinal.{0}} : ucH γ a < ucH γ b ↔ a < b := ucG_lt_iff γ

theorem ucH_le_self (γ o : Ordinal.{0}) : o ≤ ucH γ o := ucG_le_self γ o

theorem ucH_normal (γ : Ordinal.{0}) : Order.IsNormal (ucH γ) := ucG_normal γ

/-! ## `H_β = F_β` above `max(Ω₁, β)` for `β < Ω₂` -/

/-- The start of `H_β` inside `F_β`: the least `s` with `F_β(s) > max(Ω₁, β)`. -/
noncomputable def ucS (β : Ordinal.{0}) : Ordinal.{0} := sInf {s | max Om1 β < rhF β s}

theorem ucS_spec (β : Ordinal.{0}) : max Om1 β < rhF β (ucS β) := by
  have hne : {s | max Om1 β < rhF β s}.Nonempty :=
    ⟨max Om1 β + 1, (lt_add_one _).trans_le (rhF_le_self β _)⟩
  exact csInf_mem hne

theorem ucS_le {β s : Ordinal.{0}} (h : max Om1 β < rhF β s) : ucS β ≤ s := csInf_le' h

theorem ucS_lt {β v : Ordinal.{0}} (hv : max Om1 β < v) (hSC : SC v) : ucS β < v := by
  have h1 : ucS β ≤ max Om1 β + 1 := ucS_le ((lt_add_one _).trans_le (rhF_le_self β _))
  exact h1.trans_lt (hSC.add_one_lt hv)

/-- The statement of the comparison at level `β`. -/
def UcAgree (β : Ordinal.{0}) : Prop :=
  (∀ v, max Om1 β < v → (v ∈ range (ucH β) ↔ v ∈ range (rhF β))) ∧ ucH β = fun y => rhF β (ucS β + y)

/-- The fixed points agree once the enumerations do. -/
theorem uc_fix_of_agree {β : Ordinal.{0}} (h : UcAgree β) {v : Ordinal.{0}} (hv : max Om1 β < v) :
    ucH β v = v ↔ rhF β v = v := by
  have hS : ∀ {w : Ordinal.{0}}, SC w → max Om1 β < w → ucS β + w = w := fun hw hlt =>
    (isPrincipal_add_iff_add_left_eq_self.1 hw.isPrincipal) _ (ucS_lt hlt hw)
  constructor
  · intro e
    have hSC : SC v := by rw [← e]; exact ucH_SC β v
    have e' := e
    rw [h.2] at e'
    simp only at e'
    rwa [hS hSC hv] at e'
  · intro e
    have hSC : SC v := by rw [← e]; exact rhF_SC β v
    rw [h.2]
    simp only
    rw [hS hSC hv, e]

/-- **For `β < Ω₂`, `H_β` and `F_β` agree above `max(Ω₁, β)`**: same values, `H_β(y) = F_β(s_β + y)`. -/
theorem uc_agree : ∀ β : Ordinal.{0}, β < OmTwo → UcAgree β := by
  intro β
  induction β using WellFoundedLT.induction with
  | ind β IH =>
  intro hβ
  have hfixj : ∀ j < β, ∀ v, max Om1 β < v → (ucH j v = v ↔ rhF j v = v) := fun j hj v hv =>
    uc_fix_of_agree (IH j hj (hj.trans hβ)) ((max_le_max le_rfl hj.le).trans_lt hv)
  have hran : ∀ v, max Om1 β < v → (v ∈ range (ucH β) ↔ v ∈ range (rhF β)) := by
    intro v hv
    constructor
    · rintro hvr
      have hm : v ∈ ucGC ucC Om1 β := by
        unfold ucH at hvr; rw [ucG_range_eq] at hvr; exact hvr
      refine rhF_range hm.1 fun j hj => (hfixj j hj v hv).1 (hm.2.2.2 j hj ?_)
      rw [ucC_small (hj.trans hβ)]
      exact (hj.trans_le (le_max_right _ _)).trans hv
    · rintro ⟨y, rfl⟩
      refine ucG_range (rhF_SC β y) ((le_max_left _ _).trans_lt hv) ?_ fun j hj _ =>
        (hfixj j hj _ hv).2 (rhF_fix_lower hj y)
      rw [ucC_small hβ]; exact (le_max_right _ _).trans_lt hv
  refine ⟨hran, ?_⟩
  -- the enumeration
  have hmono : StrictMono fun y => rhF β (ucS β + y) := fun a b hab =>
    (rhF_lt β).2 ((add_lt_add_iff_left _).2 hab)
  have hrange : range (ucH β) = range fun y => rhF β (ucS β + y) := by
    ext v
    constructor
    · intro hvr
      have hv : max Om1 β < v := by
        obtain ⟨o, rfl⟩ := hvr
        rw [max_lt_iff]
        refine ⟨ucH_gt β o, ?_⟩
        have := ucH_C_lt β o
        rwa [ucC_small hβ] at this
      obtain ⟨y, rfl⟩ := (hran v hv).1 hvr
      have hs : ucS β ≤ y := ucS_le hv
      exact ⟨y - ucS β, by simp only; rw [Ordinal.add_sub_cancel_of_le hs]⟩
    · rintro ⟨y, rfl⟩
      have hv : max Om1 β < rhF β (ucS β + y) :=
        (ucS_spec β).trans_le ((rhF_le β).2 le_self_add)
      exact (hran _ hv).2 ⟨_, rfl⟩
  have e1 : enumOrd (range (ucH β)) = ucH β := enumOrd_range (ucH_normal β).strictMono
  have e2 : enumOrd (range fun y => rhF β (ucS β + y)) = fun y => rhF β (ucS β + y) := enumOrd_range hmono
  rw [← e1, hrange, e2]

theorem ucH_eq_F {β : Ordinal.{0}} (hβ : β < OmTwo) (y : Ordinal.{0}) : ucH β y = rhF β (ucS β + y) := by
  rw [(uc_agree β hβ).2]

theorem ucH_fix_iff_F {β v : Ordinal.{0}} (hβ : β < OmTwo) (hv : max Om1 β < v) : ucH β v = v ↔ rhF β v = v :=
  uc_fix_of_agree (uc_agree β hβ) hv

theorem uc_range_F {β v : Ordinal.{0}} (hβ : β < OmTwo) (hv : max Om1 β < v) :
    v ∈ range (ucH β) ↔ v ∈ range (rhF β) := (uc_agree β hβ).1 v hv

end Googology.Trans.PoR.InaccPsi.R2.Uc
