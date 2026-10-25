import Googology.Trans.PoR.InaccPsi.R2.TrPi

/-!
# The segment move `mv b c` on the low-parameter points, and its cocycle

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`R2.mv b c` is the base change between two countable `υ`-points: `π_{c,b}` if `c < b`, `π_{b,c}⁻¹` if `b < c`, the
identity if `b = c`.  For an `ε`-number `κ` below both, `TrLowT b κ := Tᵇ[κ] ∩ Ω₁` (the points below `κ` and the
points of `seg(b)` whose parameters lie below `κ`).  Here, once for all three cases:

* `trMv_cases`, `trMv_maps` (`mv b c` maps `TrLowT b κ` into `TrLowT c κ`), `trMv_lt` (identity below `κ`),
  `trMv_base` (`b ↦ c`), `trMv_mono`, `trMv_add`, `trMv_inv` (`mv c b ∘ mv b c = id`), `trMv_image` (onto),
  `trMv_ge`, `trMv_gt`, `trMv_inSeg` (`seg(b)` into `seg(c)`), `trMv_le1` (`≤₁` on `R₁⁺`), `trMv_E`, `trMv_indec`;
* `trMv_comp` (**the cocycle `mv c d ∘ mv b c = mv b d` on `TrLowT b κ`**: the carry from `b` to `d` through any
  intermediate segment base `c` is the single base change `mv b d`); `trMv_comp_pi` (the case `d < c < b`:
  `π_{d,c} ∘ π_{c,b} = π_{d,b}`).

No new axiom.  New definition: `TrLowT` (a set).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Googology.Trans.PoR.InaccPsi.R2.Tr

open Ordinal Set Googology.Trans.PoR.InaccPsi.R2

/-- `Tᵇ[κ] ∩ Ω₁`: the points below `κ` and the points of `seg(b)` with parameters below `κ`. -/
def TrLowT (b κ : Ordinal.{0}) : Set Ordinal.{0} := {x | x ∈ TB b κ ∧ x < Om1}

section Pair

variable {κ b c : Ordinal.{0}} (hb : UpsPt b) (hb1 : b < Om1) (hc : UpsPt c) (hc1 : c < Om1)
  (hκb : κ < b) (hκc : κ < c)

/-- The three cases of `mv b c`. -/
theorem trMv_cases (hb1 : b < Om1) (hc1 : c < Om1) (hb : UpsPt b) (hc : UpsPt c) :
    (c < b ∧ Bases c b ∧ mv b c = pi c b) ∨ (b = c ∧ mv b c = id) ∨
      (b < c ∧ Bases b c ∧ mv b c = up b c) := by
  rcases lt_trichotomy c b with h | rfl | h
  · exact Or.inl ⟨h, ⟨upsPt_inE hc, upsPt_inE hb, h, hb1⟩, by simp [mv, h]⟩
  · exact Or.inr (Or.inl ⟨rfl, by simp [mv]⟩)
  · exact Or.inr (Or.inr ⟨h, ⟨upsPt_inE hb, upsPt_inE hc, h, hc1⟩,
      by simp [mv, h, not_lt.2 h.le]⟩)

include hb hb1 hc hc1 hκb hκc

/-- `mv b c` maps `TrLowT b κ` into `TrLowT c κ`. -/
theorem trMv_maps {x : Ordinal.{0}} (hx : x ∈ TrLowT b κ) : mv b c x ∈ TrLowT c κ := by
  rcases trMv_cases hb1 hc1 hb hc with ⟨h, hB, e⟩ | ⟨rfl, e⟩ | ⟨h, hB, e⟩ <;> rw [e]
  · exact ⟨trPi_TB hB hκc.le hx.1, down_lt_Om1 hB (trTB_mono hκc.le hx.1) hx.2⟩
  · exact hx
  · exact ⟨trUp_TB hB hx.1, up_lt_Om1 hB hx.1.1 hx.2⟩

/-- `mv b c` is the identity below `κ`. -/
theorem trMv_lt {x : Ordinal.{0}} (hx : x < κ) : mv b c x = x := by
  rcases trMv_cases hb1 hc1 hb hc with ⟨h, hB, e⟩ | ⟨rfl, e⟩ | ⟨h, hB, e⟩ <;> rw [e]
  · exact pi_lt hB (hx.trans hκc)
  · rfl
  · exact up_lt hB (hx.trans hκb)

omit hκb hκc in
/-- `mv b c b = c`. -/
theorem trMv_base : mv b c b = c := by
  rcases trMv_cases hb1 hc1 hb hc with ⟨h, hB, e⟩ | ⟨rfl, e⟩ | ⟨h, hB, e⟩ <;> rw [e]
  · exact (pi_base hB).2
  · rfl
  · exact up_base hB

theorem trMv_mono : StrictMonoOn (mv b c) (TrLowT b κ) := by
  rcases trMv_cases hb1 hc1 hb hc with ⟨h, hB, e⟩ | ⟨rfl, e⟩ | ⟨h, hB, e⟩ <;> rw [e]
  · exact down_mono hB (fun x hx => trTB_mono hκc.le hx.1)
  · exact strictMono_id.strictMonoOn _
  · exact up_mono hB (fun x hx => hx.1.1)

theorem trMv_add : ∀ x ∈ TrLowT b κ, ∀ y ∈ TrLowT b κ, ∀ z ∈ TrLowT b κ,
    (x + y = z ↔ mv b c x + mv b c y = mv b c z) := by
  rcases trMv_cases hb1 hc1 hb hc with ⟨h, hB, e⟩ | ⟨rfl, e⟩ | ⟨h, hB, e⟩ <;> rw [e]
  · exact down_add hB (fun x hx => trTB_mono hκc.le hx.1)
  · exact fun _ _ _ _ _ _ => Iff.rfl
  · exact up_add hB (fun x hx => hx.1.1)

/-- `mv c b ∘ mv b c = id` on `TrLowT b κ`. -/
theorem trMv_inv {x : Ordinal.{0}} (hx : x ∈ TrLowT b κ) : mv c b (mv b c x) = x := by
  rcases trMv_cases hb1 hc1 hb hc with ⟨h, hB, e⟩ | ⟨rfl, e⟩ | ⟨h, hB, e⟩
  · have e' : mv c b = up c b := by simp [mv, h, not_lt.2 h.le]
    rw [e, e']; exact up_pi hB (trTB_mono hκc.le hx.1)
  · rw [e]; simp
  · have e' : mv c b = pi b c := by simp [mv, h]
    rw [e, e']; exact (up_spec hB hx.1.1).2

/-- `mv b c` maps `TrLowT b κ` onto `TrLowT c κ`. -/
theorem trMv_image : mv b c '' TrLowT b κ = TrLowT c κ := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩; exact trMv_maps hb hb1 hc hc1 hκb hκc hx
  · intro hw
    exact ⟨mv c b w, trMv_maps hc hc1 hb hb1 hκc hκb hw, trMv_inv hc hc1 hb hb1 hκc hκb hw⟩

/-- `b < x` gives `c < mv b c x`. -/
theorem trMv_gt {x : Ordinal.{0}} (hx : x ∈ TrLowT b κ) (hbx : b < x) : c < mv b c x := by
  rcases trMv_cases hb1 hc1 hb hc with ⟨h, hB, e⟩ | ⟨rfl, e⟩ | ⟨h, hB, e⟩ <;> rw [e]
  · exact down_gt hB (trTB_mono hκc.le hx.1) hbx
  · exact hbx
  · exact up_gt hB hx.1.1 hbx

theorem trMv_ge {x : Ordinal.{0}} (hx : x ∈ TrLowT b κ) (hbx : b ≤ x) : c ≤ mv b c x := by
  rcases hbx.lt_or_eq with h | rfl
  · exact (trMv_gt hb hb1 hc hc1 hκb hκc hx h).le
  · exact (trMv_base hb hb1 hc hc1).ge

/-- `mv b c` maps `seg(b) ∩ Tᵇ[κ]` into `seg(c)`. -/
theorem trMv_inSeg {x : Ordinal.{0}} (hx : x ∈ TrLowT b κ) (hs : InSeg b x) : InSeg c (mv b c x) := by
  have hm := trMv_maps hb hb1 hc hc1 hκb hκc hx
  exact (inSeg_iff hc hc1).2 ⟨trMv_ge hb hb1 hc hc1 hκb hκc hx hs.1, hm.2, hm.1.1⟩

/-- `mv b c` keeps `≤₁` (`R₁⁺`) from points above `b`. -/
theorem trMv_le1 {x y : Ordinal.{0}} (hx : x ∈ TrLowT b κ) (hy : y ∈ TrLowT b κ) (hbx : b < x) :
    le1R x y ↔ le1R (mv b c x) (mv b c y) := by
  rcases trMv_cases hb1 hc1 hb hc with ⟨h, hB, e⟩ | ⟨rfl, e⟩ | ⟨h, hB, e⟩ <;> rw [e]
  · exact st_le1 hB (trTB_mono hκc.le hx.1) hbx hx.2 (trTB_mono hκc.le hy.1)
  · exact Iff.rfl
  · exact up_le1 hB hx.1.1 hbx hx.2 hy.1.1

/-- `mv b c` keeps `ε`-numbers above `b`. -/
theorem trMv_E {x : Ordinal.{0}} (hx : x ∈ TrLowT b κ) (hbx : b < x) : InE x ↔ InE (mv b c x) := by
  rcases trMv_cases hb1 hc1 hb hc with ⟨h, hB, e⟩ | ⟨rfl, e⟩ | ⟨h, hB, e⟩ <;> rw [e]
  · exact down_E hB (trTB_mono hκc.le hx.1) hbx hx.2
  · exact Iff.rfl
  · exact up_E hB hx.1.1 hbx hx.2

/-- `mv b c` keeps indecomposability. -/
theorem trMv_indec {x : Ordinal.{0}} (hx : x ∈ TrLowT b κ) (hI : Indec x) : Indec (mv b c x) := by
  rcases trMv_cases hb1 hc1 hb hc with ⟨h, hB, e⟩ | ⟨rfl, e⟩ | ⟨h, hB, e⟩ <;> rw [e]
  · exact down_indec hB (trTB_mono hκc.le hx.1) hx.2 hI
  · exact hI
  · exact up_indec hB hx.1.1 hx.2 hI

end Pair

/-- **The cocycle of segment moves: `mv c d ∘ mv b c = mv b d` on `Tᵇ[κ] ∩ Ω₁`.** -/
theorem trMv_comp {κ b c d : Ordinal.{0}} (hb : UpsPt b) (hb1 : b < Om1) (hc : UpsPt c) (hc1 : c < Om1)
    (hd : UpsPt d) (hd1 : d < Om1) (hκb : κ < b) (hκc : κ < c) (hκd : κ < d) {x : Ordinal.{0}}
    (hx : x ∈ TrLowT b κ) : mv c d (mv b c x) = mv b d x := by
  refine trEqOn_of_image (A := TrLowT b κ) (f := fun u => mv c d (mv b c u)) ?_
    (trMv_mono hb hb1 hd hd1 hκb hκd) ?_ hx
  · intro u hu v hv huv
    exact trMv_mono hc hc1 hd hd1 hκc hκd (trMv_maps hb hb1 hc hc1 hκb hκc hu)
      (trMv_maps hb hb1 hc hc1 hκb hκc hv) (trMv_mono hb hb1 hc hc1 hκb hκc hu hv huv)
  · rw [show (fun u => mv c d (mv b c u)) = mv c d ∘ mv b c from rfl, Set.image_comp,
      trMv_image hb hb1 hc hc1 hκb hκc, trMv_image hc hc1 hd hd1 hκc hκd,
      trMv_image hb hb1 hd hd1 hκb hκd]

/-- The cocycle in the case `d < c < b`: `π_{d,c} ∘ π_{c,b} = π_{d,b}` on `Tᵇ[κ] ∩ Ω₁`. -/
theorem trMv_comp_pi {κ b c d : Ordinal.{0}} (hb : UpsPt b) (hb1 : b < Om1) (hc : UpsPt c)
    (hd : UpsPt d) (hκd : κ < d) (hdc : d < c) (hcb : c < b) {x : Ordinal.{0}}
    (hx : x ∈ TrLowT b κ) : pi d c (pi c b x) = pi d b x := by
  have hc1 : c < Om1 := hcb.trans hb1
  have hd1 : d < Om1 := hdc.trans hc1
  have e1 : mv b c = pi c b := by simp [mv, hcb]
  have e2 : mv c d = pi d c := by simp [mv, hdc]
  have e3 : mv b d = pi d b := by simp [mv, hdc.trans hcb]
  have := trMv_comp hb hb1 hc hc1 hd hd1 (hκd.trans (hdc.trans hcb)) (hκd.trans hdc) hκd hx
  rwa [e1, e2, e3] at this

end Googology.Trans.PoR.InaccPsi.R2.Tr
