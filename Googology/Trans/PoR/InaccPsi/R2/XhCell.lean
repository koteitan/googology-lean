import Googology.Trans.PoR.InaccPsi.R2.XhLay

/-!
# Xh: the cells of region (B): a base and an offset of type (A) or of a layer `c`

Every region-(B) name is `β + ζ` with a base `β ∈ {0} ∪ {Ω₂·q : 1 ≤ q} ∪ {b_k} ∪ {b_ω}` and an offset `ζ < Ω₂`
(`Xh.xhBhi_off`, `Xh.xhWin_off`), and the code depends on `ζ` only.  The offsets are sorted like the names of
(A) ∪ (B-lo):

* `XhNmA ζ` (`ζ < Γ(B)·ω` for some `B < Γ(1)`: an (A)-type offset), `XhNmPast c ζ`, `XhNmLay c ζ`;
* `xhNm_split` (**every `ζ < Ω₂` is of type (A) or lies in a layer `c`, `1 ≤ c < Ω₂`**), `xhNmLay_unique`;
* `xhPast_iff_name` / `xhLay_iff_name` (the index layers of `Xh.XhLay` are the name layers of the name);
* the reductions `xhBhi_red` ((B-hi) from its (A)-type cell and its layer cells), `xhWinB_red` (the windows'
  non-(A) offsets from the layer cells, `ξ = k` and `ξ = ω`).

No new axiom.  New definitions: `XhNmA`, `XhNmPast`, `XhNmLay`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2

variable {S : InaccSeq.{0}}

/-- An (A)-type name or offset: below `Γ(B)·ω` for some `B < Γ(1)`. -/
def XhNmA (ζ : Ordinal.{0}) : Prop := ∃ B, B < Gc.gcG 1 ∧ ζ < Gc.gcG B * ω

/-- A name or offset past every `Γ(B)·ω`, `B < Γ(c)`. -/
def XhNmPast (c ζ : Ordinal.{0}) : Prop := ∀ B, B < Gc.gcG c → Gc.gcG B * ω ≤ ζ

/-- **The name layer `c`.** -/
def XhNmLay (c ζ : Ordinal.{0}) : Prop := XhNmPast c ζ ∧ ¬ XhNmPast (c + 1) ζ

theorem xhNmPast_anti {c c' ζ : Ordinal.{0}} (h : c ≤ c') (hp : XhNmPast c' ζ) : XhNmPast c ζ :=
  fun B hB => hp B (hB.trans_le (Gc.gcG_le h))

theorem xhNmA_iff {ζ : Ordinal.{0}} : XhNmA ζ ↔ ¬ XhNmPast 1 ζ := by
  constructor
  · rintro ⟨B, hB, hl⟩ hp; exact absurd (hp B hB) (not_le.2 hl)
  · intro h; by_contra hc; apply h; intro B hB; by_contra h'; exact hc ⟨B, hB, not_le.1 h'⟩

theorem xhNmLay_unique {c c' ζ : Ordinal.{0}} (h : XhNmLay c ζ) (h' : XhNmLay c' ζ) : c = c' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact h.2 (xhNmPast_anti (Order.add_one_le_of_lt hlt) h'.1)
  · exact h'.2 (xhNmPast_anti (Order.add_one_le_of_lt hlt) h.1)

/-- **Every `ζ < Ω₂` is of type (A) or in a layer `c`, `1 ≤ c < Ω₂`.** -/
theorem xhNm_split {ζ : Ordinal.{0}} (hζ : ζ < Om (1 + 1)) :
    XhNmA ζ ∨ ∃ c, 1 ≤ c ∧ c < Om (1 + 1) ∧ XhNmLay c ζ := by
  by_cases hA : XhNmA ζ
  · exact Or.inl hA
  right
  have h1 : XhNmPast 1 ζ := by by_contra h; exact hA (xhNmA_iff.2 h)
  have hnot : ¬ XhNmPast (ζ + 1 + 1) ζ := by
    intro hp
    have hB : ζ + 1 < Gc.gcG (ζ + 1 + 1) :=
      (Order.lt_add_one_iff.2 le_rfl).trans_le (Gc.gcG_strictMono.le_apply)
    have h2 : ζ < Gc.gcG (ζ + 1) * ω :=
      (Order.lt_add_one_iff.2 le_rfl).trans_le
        (Gc.gcG_strictMono.le_apply.trans (Ordinal.le_mul_left _ omega0_pos))
    exact absurd (hp (ζ + 1) hB) (not_le.2 h2)
  set C := {c : Ordinal.{0} | ¬ XhNmPast c ζ} with hC
  have hne : C.Nonempty := ⟨_, hnot⟩
  set c0 := sInf C with hc0
  have hc0C : ¬ XhNmPast c0 ζ := csInf_mem hne
  have hbelow : ∀ c', c' < c0 → XhNmPast c' ζ := fun c' hc' => by
    by_contra h; exact absurd (csInf_le' h) (not_le.2 hc')
  have hc0le : c0 ≤ ζ + 1 + 1 := csInf_le' hnot
  rcases zero_or_succ_or_isSuccLimit c0 with h0 | ⟨d, hd⟩ | hlim
  · exact absurd (xhNmPast_anti (h0 ▸ zero_le) h1) (h0 ▸ hc0C)
  · rw [Order.succ_eq_add_one] at hd
    have hdlt : d < c0 := hd ▸ Order.lt_add_one_iff.2 le_rfl
    refine ⟨d, ?_, ?_, hbelow d hdlt, hd ▸ hc0C⟩
    · rw [Order.one_le_iff_ne_zero]
      rintro rfl
      rw [zero_add] at hd
      exact hc0C (hd ▸ h1)
    · exact (Order.lt_add_one_iff.1 (hdlt.trans_le hc0le)).trans_lt (xhOm2_lim hζ)
  · refine absurd (fun B hB => ?_) hc0C
    obtain ⟨c', hc', hB'⟩ := Gc.gcG_lt_of_lt_limit hlim hB
    exact hbelow c' hc' B hB'

/-- **The index layers are the name layers.** -/
theorem xhPast_iff_name {c l : Ordinal.{0}} (hr : Cd.CdRange S l) :
    XhPast S c l ↔ XhNmPast c (Cd.cdEta S l) := by
  obtain ⟨hl, -, hlt, -⟩ := hr
  obtain ⟨hg, hιη, -⟩ := Wj.wjEta_spec (S := S) hl.1 hlt
  constructor
  · intro h B hB
    by_contra h'
    push Not at h'
    have := Cd.cd_iota_lt_of_good hg h'
    rw [hιη] at this
    exact absurd (h B hB) (not_le.2 this)
  · intro h B hB
    rw [← hιη]; exact Bt.iota_mono (S := S) _ _ (h B hB)

theorem xhLay_iff_name {c l : Ordinal.{0}} (hr : Cd.CdRange S l) :
    XhLay S c l ↔ XhNmLay c (Cd.cdEta S l) := by
  unfold XhLay XhNmLay
  rw [xhPast_iff_name hr, xhPast_iff_name hr]

/-- **The reduction of (B-hi) to its cells** (base `Ω₂·q`, offset of type (A) or in a layer `c`). -/
theorem xhBhi_red (P : Ordinal.{0} → Prop)
    (hA : ∀ l q ζ, Cd.CdRange S l → Cd.cdEta S l = Om (1 + 1) * q + ζ → 1 ≤ q → ζ ≠ 0 → ζ < Om (1 + 1) →
      Cd.cdEta S l < Om ω → XhNmA ζ → P l)
    (hL : ∀ c, 1 ≤ c → c < Om (1 + 1) → ∀ l q ζ, Cd.CdRange S l → Cd.cdEta S l = Om (1 + 1) * q + ζ → 1 ≤ q →
      ζ ≠ 0 → ζ < Om (1 + 1) → Cd.cdEta S l < Om ω → XhNmLay c ζ → P l) :
    ∀ l, Cd.CdRange S l → Wj.WjNotA S l → upsilon l < Nc.ncL S 0 →
      Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) → Bt.iota S (Om (1 + 1)) ≤ l → P l := by
  intro l hr hN h0 he hι
  obtain ⟨h2, hw, -⟩ := (xhBhi_iff hr).1 ⟨hN, h0, he, hι⟩
  obtain ⟨q, ζ, e, hq, hζ0, hζ, -, -⟩ := xhBhi_off h2 he
  rcases xhNm_split hζ with hz | ⟨c, hc1, hc2, hz⟩
  · exact hA l q ζ hr e hq hζ0 hζ hw hz
  · exact hL c hc1 hc2 l q ζ hr e hq hζ0 hζ hw hz

/-- **The reduction of the non-(A) offsets of `(L(ξ), L(ξ+1))` to the layer cells** (`ξ = k`: the windows,
`ξ = ω`: the top window). -/
theorem xhWinB_red (P : Ordinal.{0} → Prop) (ξ : Ordinal.{0})
    (hL : ∀ c, 1 ≤ c → c < Om (1 + 1) → ∀ l, Cd.CdRange S l → Nc.ncL S ξ < upsilon l →
      upsilon l < Nc.ncL S (ξ + 1) → XhNmLay c (Cd.cdEta S l - Wj.wjBase S ξ) → P l) :
    ∀ l, Cd.CdRange S l → Nc.ncL S ξ < upsilon l → upsilon l < Nc.ncL S (ξ + 1) →
      ¬ XhNmA (Cd.cdEta S l - Wj.wjBase S ξ) → P l := by
  intro l hr h1 h2 hnA
  obtain ⟨ζ, e, -, hζP, -, -⟩ := xhWin_off hr h1 h2
  have hz : Cd.cdEta S l - Wj.wjBase S ξ = ζ := by rw [e]; exact Ordinal.add_sub_cancel _ _
  have hζ2 : Cd.cdEta S l - Wj.wjBase S ξ < Om (1 + 1) := hz ▸ hζP.trans Wj.wjPp_lt_Om2
  rcases xhNm_split hζ2 with hA | ⟨c, hc1, hc2, hc⟩
  · exact absurd hA hnA
  · exact hL c hc1 hc2 l hr h1 h2 hc

end Googology.Trans.PoR.InaccPsi.R2.Xh
