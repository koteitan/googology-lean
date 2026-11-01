import Googology.Trans.PoR.InaccPsi.R2.XhName

/-!
# Xh: the layers of (B-lo) by the atoms `Γ(c)`

Region (A) is "below `ι(Γ(B)·ω)` for some `B < Γ(1)`" (the systems `Hg.HgVD` over the base `G = Γ(0)`, bound
`< Γ(1)`).  Past (A) and below `ι(Ω₂)`, the restarts are sorted by the least atom index `c` whose frontiers
`ι(Γ(B)·ω)`, `B < Γ(c+1)`, pass them: the LAYER `c`.

* `XhPast S c λ` (`ι(Γ(B)·ω) ≤ λ` for every `B < Γ(c)`), `XhLay S c λ` (`XhPast S c λ ∧ ¬ XhPast S (c+1) λ`);
* `xhPast_anti`, `xhPast_lim` (continuity at limit `c`: `Γ(c) = sup_{c'<c} Γ(c')`), `xhPast_one` (`XhPast S 1` is
  `Wj.WjNotA`), `xhA_iff` (region (A) is `¬ XhPast S 1`);
* `xhLay_exists` (**every (B-lo) restart lies in a layer `c` with `1 ≤ c < Ω₂`**), `xhLay_unique`,
  `xhLay_bound` (a layer-`c` restart is below `ι(Γ(B)·ω)` for some `B < Γ(c+1)`), `xhLay_notA`;
* `xhRegBlo_of_lay` (**the reduction**: a property on every layer `c ≥ 1` below `ι(Ω₂)` holds on (B-lo)),
  `xhLay_name` (on names: a layer-`c` restart has `Γ(B)·ω ≤ η` for `B < Γ(c)` and `η < Γ(B)·ω` for some
  `B < Γ(c+1)`).

No new axiom.  New definitions: `XhPast`, `XhLay`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2

variable {S : InaccSeq.{0}}

/-- Past every frontier `ι(Γ(B)·ω)` with `B < Γ(c)`. -/
def XhPast (S : InaccSeq.{0}) (c l : Ordinal.{0}) : Prop :=
  ∀ B, B < Gc.gcG c → Bt.iota S (Gc.gcG B * ω) ≤ l

/-- **The layer `c`**: past every frontier with `B < Γ(c)`, not past every frontier with `B < Γ(c+1)`. -/
def XhLay (S : InaccSeq.{0}) (c l : Ordinal.{0}) : Prop := XhPast S c l ∧ ¬ XhPast S (c + 1) l

theorem xhPast_anti {c c' l : Ordinal.{0}} (h : c ≤ c') (hp : XhPast S c' l) : XhPast S c l :=
  fun B hB => hp B (hB.trans_le (Gc.gcG_le h))

theorem xhPast_lim {c l : Ordinal.{0}} (hc : IsSuccLimit c) (h : ∀ c', c' < c → XhPast S c' l) :
    XhPast S c l := fun B hB => by
  obtain ⟨c', hc', hB'⟩ := Gc.gcG_lt_of_lt_limit hc hB
  exact h c' hc' B hB'

theorem xhPast_one {l : Ordinal.{0}} : XhPast S 1 l ↔ Wj.WjNotA S l := Iff.rfl

/-- Region (A) is `¬ XhPast S 1`. -/
theorem xhA_iff {l : Ordinal.{0}} :
    (∃ B, B < Gc.gcG 1 ∧ l < Bt.iota S (Gc.gcG B * ω)) ↔ ¬ XhPast S 1 l := by
  constructor
  · rintro ⟨B, hB, hl⟩ hp; exact absurd (hp B hB) (not_le.2 hl)
  · intro h; by_contra hc; push Not at hc; exact h hc

theorem xhLay_unique {c c' l : Ordinal.{0}} (h : XhLay S c l) (h' : XhLay S c' l) : c = c' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact h.2 (xhPast_anti (Order.add_one_le_of_lt hlt) h'.1)
  · exact h'.2 (xhPast_anti (Order.add_one_le_of_lt hlt) h.1)

theorem xhLay_bound {c l : Ordinal.{0}} (h : XhLay S c l) :
    ∃ B, B < Gc.gcG (c + 1) ∧ l < Bt.iota S (Gc.gcG B * ω) := by
  by_contra hc
  push Not at hc
  exact h.2 hc

theorem xhLay_notA {c l : Ordinal.{0}} (hc : 1 ≤ c) (h : XhLay S c l) : Wj.WjNotA S l :=
  xhPast_anti hc h.1

/-- **Every (B-lo) restart lies in a layer `c`, `1 ≤ c < Ω₂`.** -/
theorem xhLay_exists {l : Ordinal.{0}} (hr : Cd.CdRange S l) (hN : Wj.WjNotA S l)
    (hι : l < Bt.iota S (Om (1 + 1))) : ∃ c, 1 ≤ c ∧ c < Om (1 + 1) ∧ XhLay S c l := by
  obtain ⟨hl, -, hlt, -⟩ := hr
  obtain ⟨hg, hιη, -⟩ := Wj.wjEta_spec (S := S) hl.1 hlt
  set η := Cd.cdEta S l with hηdef
  have hη : η < Om (1 + 1) := by
    by_contra h
    push Not at h
    have := Bt.iota_mono (S := S) _ _ h
    rw [hιη] at this
    exact absurd hι (not_lt.2 this)
  -- not past at `η + 2`
  have hnot : ¬ XhPast S (η + 1 + 1) l := by
    intro hp
    have hB : η + 1 < Gc.gcG (η + 1 + 1) :=
      (Order.lt_add_one_iff.2 le_rfl).trans_le (Gc.gcG_strictMono.le_apply)
    have h1 := hp (η + 1) hB
    have h2 : η < Gc.gcG (η + 1) * ω :=
      (Order.lt_add_one_iff.2 le_rfl).trans_le
        (Gc.gcG_strictMono.le_apply.trans (Ordinal.le_mul_left _ omega0_pos))
    have h3 := Cd.cd_iota_lt_of_good hg h2
    rw [hιη] at h3
    exact absurd h1 (not_le.2 h3)
  set C := {c : Ordinal.{0} | ¬ XhPast S c l} with hC
  have hne : C.Nonempty := ⟨_, hnot⟩
  set c0 := sInf C with hc0
  have hc0C : ¬ XhPast S c0 l := csInf_mem hne
  have hbelow : ∀ c', c' < c0 → XhPast S c' l := fun c' hc' => by
    by_contra h; exact absurd (csInf_le' h) (not_le.2 hc')
  have hc0le : c0 ≤ η + 1 + 1 := csInf_le' hnot
  rcases zero_or_succ_or_isSuccLimit c0 with h0 | ⟨d, hd⟩ | hlim
  · exact absurd (xhPast_anti (h0 ▸ zero_le) (xhPast_one.2 hN)) (h0 ▸ hc0C)
  · rw [Order.succ_eq_add_one] at hd
    have hdlt : d < c0 := hd ▸ Order.lt_add_one_iff.2 le_rfl
    refine ⟨d, ?_, ?_, hbelow d hdlt, hd ▸ hc0C⟩
    · rw [Order.one_le_iff_ne_zero]
      rintro rfl
      rw [zero_add] at hd
      exact hc0C (hd ▸ xhPast_one.2 hN)
    · have h1 : d < η + 1 + 1 := hdlt.trans_le hc0le
      exact (Order.lt_add_one_iff.1 h1).trans_lt (xhOm2_lim hη)
  · exact absurd (xhPast_lim hlim hbelow) hc0C

/-- **The reduction of (B-lo) to the layers.** -/
theorem xhRegBlo_of_lay (P : Ordinal.{0} → Prop)
    (h : ∀ c, 1 ≤ c → c < Om (1 + 1) → ∀ l, Cd.CdRange S l → XhLay S c l → l < Bt.iota S (Om (1 + 1)) → P l) :
    ∀ l, Cd.CdRange S l → Wj.WjNotA S l → upsilon l < Nc.ncL S 0 →
      Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) → l < Bt.iota S (Om (1 + 1)) → P l := by
  intro l hr hN _ _ hι
  obtain ⟨c, h1, h2, hL⟩ := xhLay_exists hr hN hι
  exact h c h1 h2 l hr hL hι

/-- **A layer-`c` restart below `ι(Ω₂)` is a (B-lo) restart** (for `c ≥ 1`). -/
theorem xhBlo_of_lay {c l : Ordinal.{0}} (hc : 1 ≤ c) (hr : Cd.CdRange S l) (hL : XhLay S c l)
    (hι : l < Bt.iota S (Om (1 + 1))) :
    Wj.WjNotA S l ∧ upsilon l < Nc.ncL S 0 ∧ Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) ∧
      l < Bt.iota S (Om (1 + 1)) := by
  have hN := xhLay_notA hc hL
  have h := (xhBlo_iff hr).1
  obtain ⟨hl, -, hlt, -⟩ := hr
  obtain ⟨hg, hιη, hpv⟩ := Wj.wjEta_spec (S := S) hl.1 hlt
  have hη : Cd.cdEta S l < Om (1 + 1) := by
    by_contra h'
    push Not at h'
    have := Bt.iota_mono (S := S) _ _ h'
    rw [hιη] at this
    exact absurd hι (not_lt.2 this)
  have hB : ∀ B, B < Gc.gcG 1 → Gc.gcG B * ω ≤ Cd.cdEta S l := fun B hB => by
    by_contra h'
    push Not at h'
    have := Cd.cd_iota_lt_of_good hg h'
    rw [hιη] at this
    exact absurd (hN B hB) (not_le.2 this)
  have hη0 : Cd.cdEta S l ≠ 0 := by
    intro h0
    have h1 := hB 0 (Gc.gcG_SC 1).1
    rw [h0] at h1
    exact absurd h1 (not_le.2 (mul_pos (Gc.gcG_SC 0).1 omega0_pos))
  refine ⟨hN, ?_, (xhExp_le hη0).trans_lt hη, hι⟩
  rw [← hpv]; exact (Nm.Pv_mono (S := S) hη.le).trans_lt (Ga.ga_Pv_lt_L0 S le_rfl)

/-- **The layer on names.** -/
theorem xhLay_name {c l : Ordinal.{0}} (hr : Cd.CdRange S l) (hL : XhLay S c l) :
    (∀ B, B < Gc.gcG c → Gc.gcG B * ω ≤ Cd.cdEta S l) ∧
      ∃ B, B < Gc.gcG (c + 1) ∧ Cd.cdEta S l < Gc.gcG B * ω := by
  obtain ⟨hl, -, hlt, -⟩ := hr
  obtain ⟨hg, hιη, -⟩ := Wj.wjEta_spec (S := S) hl.1 hlt
  refine ⟨fun B hB => ?_, ?_⟩
  · by_contra h'
    push Not at h'
    have := Cd.cd_iota_lt_of_good hg h'
    rw [hιη] at this
    exact absurd (hL.1 B hB) (not_le.2 this)
  · obtain ⟨B, hB, hlB⟩ := xhLay_bound hL
    refine ⟨B, hB, ?_⟩
    by_contra h'
    push Not at h'
    have := Bt.iota_mono (S := S) _ _ h'
    rw [hιη] at this
    exact absurd hlB (not_lt.2 this)

end Googology.Trans.PoR.InaccPsi.R2.Xh
