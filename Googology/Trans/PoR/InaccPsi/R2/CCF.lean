import Googology.Trans.PoR.InaccPsi.R2.CitedR1

/-!
# Theorem CC-F: closed covering copies in `R₁⁺`

The project's Theorem CC-F (the covering form of the closed-copy criterion that INC1 uses): if
`p ≤₁ q` in `R₁⁺`, `X ⊆ p` and `Y ⊆ [p, q)` are finite, `0 ∈ X` and `X ∪ Y` is closed, then there is a
map `ψ` that fixes `X`, is a closed embedding of the arithmetic part of `X ∪ Y` (onto a closed set),
moves `Y` into `(max X, p)`, and keeps `≤₁` of `R₁⁺` forward.

Proof: take the isomorphic copy `φ` of the finite-set criterion (`le1R_copy`, [G20] Prop 21.6), and
replace each component of a point by the largest Cantor normal form component of its `φ`-image
(`ψ = ext (mc ∘ φ)`, [C09] Lemma 4.5).  `≤₁` forward uses [W07b] Thm 2.2 (`le1R_lim_P`): a proper
`≤₁`-left end is additive principal, so `ψ` and `φ` agree there.

* `mc x`: the largest component of `x` (`mc 0 = 0`); `mc_lt_of_add_eq`: `c + d = d`, `c ≠ 0` give
  `mc c < mc d`.
* `ccf`: Theorem CC-F.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- The largest Cantor normal form component of `x` (`0` for `x = 0`). -/
noncomputable def mc (x : Ordinal.{0}) : Ordinal.{0} := (pc x).headD 0

theorem pc_ne_nil {x : Ordinal.{0}} (hx : x ≠ 0) : pc x ≠ [] := fun h =>
  hx (by rw [← pc_sum x, h]; rfl)

theorem mc_mem {x : Ordinal.{0}} (hx : x ≠ 0) : mc x ∈ pc x := by
  obtain ⟨a, l, hal⟩ := List.exists_cons_of_ne_nil (pc_ne_nil hx)
  unfold mc; rw [hal]; simp

theorem mc_indec {x : Ordinal.{0}} (hx : x ≠ 0) : Indec (mc x) := indec_of_mem_pc (mc_mem hx)

theorem mc_le (x : Ordinal.{0}) : mc x ≤ x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [mc, pc_zero]
  · exact le_of_mem_pc (mc_mem hx)

theorem mc_of_indec {x : Ordinal.{0}} (hx : Indec x) : mc x = x := by simp [mc, pc_indec hx]

/-- `c + d = d` with `c ≠ 0` gives `mc c < mc d`. -/
theorem mc_lt_of_add_eq {c d : Ordinal.{0}} (hc : c ≠ 0) (h : c + d = d) : mc c < mc d := by
  have hd : d ≠ 0 := by
    rintro rfl; rw [add_zero] at h; exact hc h
  have h1 : addL (pc c) (pc d) = pc d := by rw [← pc_add, h]
  obtain ⟨hh, t, hdt⟩ := List.exists_cons_of_ne_nil (pc_ne_nil hd)
  obtain ⟨a, s, hcs⟩ := List.exists_cons_of_ne_nil (pc_ne_nil hc)
  rw [hdt, hcs] at h1
  simp only [addL] at h1
  have h2 : (a :: s).takeWhile (fun b => decide (hh ≤ b)) = [] := List.append_left_eq_self.1 h1
  have h3 : ¬ hh ≤ a := by
    intro hle
    rw [List.takeWhile_cons_of_pos (by simpa using hle)] at h2
    exact List.cons_ne_nil _ _ h2
  unfold mc; rw [hdt, hcs]; simpa using not_le.1 h3

/-- **Theorem CC-F.** -/
theorem ccf {p q : Ordinal.{0}} (h : le1R p q) (X Y : Finset Ordinal.{0}) (hX : ∀ x ∈ X, x < p)
    (hY : ∀ y ∈ Y, p ≤ y ∧ y < q) (h0 : (0 : Ordinal.{0}) ∈ X) (hXY : Closed ↑(X ∪ Y)) :
    ∃ ψ : Ordinal.{0} → Ordinal.{0}, ArithIso ↑(X ∪ Y) (ψ '' ↑(X ∪ Y)) ψ ∧
      Closed (ψ '' ↑(X ∪ Y)) ∧ (∀ x ∈ X, ψ x = x) ∧ (∀ y ∈ Y, (∀ x ∈ X, x < ψ y) ∧ ψ y < p) ∧
      (∀ u ∈ X ∪ Y, ∀ w ∈ X ∪ Y, le1R u w → le1R (ψ u) (ψ w)) := by
  classical
  obtain ⟨Yt, hYt, φ, hbij, hfix, hmono, hadd, hle1⟩ := le1R_copy h X Y hX hY
  have hφ : ArithIso ↑(X ∪ Y) ↑(X ∪ Yt) φ :=
    ⟨hbij, hmono, fun x hx y hy z hz => hadd x hx y hy z hz⟩
  have h0A : (0 : Ordinal.{0}) ∈ X ∪ Y := Finset.mem_union_left _ h0
  have hφ0 : φ 0 = 0 := hfix 0 h0
  have hφne : ∀ a ∈ X ∪ Y, a ≠ 0 → φ a ≠ 0 := fun a ha ha0 e =>
    ha0 (hbij.injOn ha h0A (e.trans hφ0.symm))
  set f : Ordinal.{0} → Ordinal.{0} := fun a => mc (φ a) with hfdef
  have hf : StrictMonoOn f (IndecIn ↑(X ∪ Y)) := by
    intro a ha b hb hab
    have hsum : a + b = b := hb.2.add_eq hab
    have := (hadd a ha.1 b hb.1 b hb.1).1 hsum
    exact mc_lt_of_add_eq (hφne a ha.1 ha.2.ne_zero) this
  have hfI : ∀ a ∈ IndecIn (↑(X ∪ Y) : Set Ordinal.{0}), Indec (f a) := fun a ha =>
    mc_indec (hφne a ha.1 ha.2.ne_zero)
  have hψ : ArithIso ↑(X ∪ Y) (ext f '' ↑(X ∪ Y)) (ext f) := ext_arithIso hXY hf hfI
  have hψc : Closed (ext f '' ↑(X ∪ Y)) := ext_closed hXY hf hfI
  have hfixX : ∀ x ∈ X, ext f x = x := by
    intro x hx
    apply ext_fix
    intro a ha
    have haA : a ∈ X ∪ Y := hXY.pc_mem x (Finset.mem_union_left _ hx) a ha
    have hax : a ≤ x := le_of_mem_pc ha
    have haX : a ∈ X := by
      rcases Finset.mem_union.1 haA with h' | h'
      · exact h'
      · exact absurd (lt_of_le_of_lt hax (hX x hx)) (not_lt.2 (hY a h').1)
    show mc (φ a) = a
    rw [hfix a haX, mc_of_indec (indec_of_mem_pc ha)]
  have hψφ : ∀ z ∈ (↑(X ∪ Y) : Set Ordinal.{0}), ext f z ≤ φ z :=
    le_of_le_on_indec hXY hψ hφ (fun a _ hI => by rw [ext_indec hI]; exact mc_le _)
  refine ⟨ext f, hψ, hψc, hfixX, fun y hy => ⟨fun x hx => ?_, ?_⟩, fun u hu w hw huw => ?_⟩
  · have hxy : x < y := lt_of_lt_of_le (hX x hx) (hY y hy).1
    have := (ext_lt_iff hXY hf hfI (Finset.mem_union_left _ hx)
      (Finset.mem_union_right _ hy)).2 hxy
    rwa [hfixX x hx] at this
  · have hyA : y ∈ X ∪ Y := Finset.mem_union_right _ hy
    refine lt_of_le_of_lt (hψφ y hyA) ?_
    have hm := hbij.mapsTo hyA
    rcases Finset.mem_union.1 hm with h' | h'
    · exact hX _ h'
    · exact hYt _ h'
  · rcases eq_or_lt_of_le (le1R_le huw) with e | huw'
    · subst e; exact le1R_refl _
    have hφuw := (hle1 u hu w hw).1 huw
    have hφlt : φ u < φ w := hmono hu hw huw'
    obtain ⟨hpos, hlim⟩ := le1R_lim_P hφuw hφlt
    have hφuI : Indec (φ u) := indec_of_limit hpos hlim
    obtain ⟨hpos', hlim'⟩ := le1R_lim_P huw huw'
    have huI : Indec u := indec_of_limit hpos' hlim'
    have hψu : ext f u = φ u := by rw [ext_indec huI]; exact mc_of_indec hφuI
    have hψlt : ext f u < ext f w := (ext_lt_iff hXY hf hfI hu hw).2 huw'
    rw [hψu] at hψlt ⊢
    exact le1R_of_le hψlt.le (hψφ w hw) hφuw

end Googology.Trans.PoR.InaccPsi.R2
