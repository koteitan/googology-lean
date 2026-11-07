import Googology.Trans.PoR.InaccPsi.R2.GgOtp

/-!
# The reading over `y` commutes with the Veblen function: `Θ_y(φ(a, b)) = φ(Θ_y(a), Θ_y(b))`

`GgCl y` the codes over `y` (generated from `[0, y)` and `Ω₁` by `+` and `φ`), `Θ_y = ggTh y` the reading (the order
type of the codes below a given ordinal).  For a strongly critical `y < Ω₁`, `Θ_y` keeps `+` and `ω^·`
(`Gg.ggTh_add`, `Gg.ggTh_opow`); here also `φ`.  The codes are closed under the inverse Veblen functions
(`gg_invVeblen`), and a code fixed by every `φ(a', ·)` with a code `a' < a` is a value `φ(a, e)` with a code `e`
(`gg_range`: the leading Veblen index of the code is a code, not below `a`).  Then by induction on `a` and `b`:
`Θ_y(φ(a, b))` is fixed by every `φ(β, ·)`, `β < Θ_y(a)` (each `β` is a reading `Θ_y(a')`, `a' < a`), so it is
`φ(Θ_y(a), B')`, and `B' = Θ_y(b)` because the values `φ(Θ_y(a), B'')`, `B'' < B'`, are the readings of the codes
`φ(a, e)`, `e < b`.

* `gg_inj` (**`Θ_y` is injective on the codes**), `gg_invVeblen` (**`invVeblen₁ c`, `invVeblen₂ c` are codes**),
  `gg_range`;
* `ggTh_veblen` (**`Θ_y(φ(a, b)) = φ(Θ_y(a), Θ_y(b))`** for codes `a`, `b` over a strongly critical `y < Ω₁`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gg

open Ordinal Order Set Googology.Notation.InaccPsi

variable {y : Ordinal.{0}}

/-- **`Θ_y` is injective on the codes.** -/
theorem gg_inj {c d : Ordinal.{0}} (hc : GgCl y c) (hd : GgCl y d) (h : ggTh y c = ggTh y d) : c = d := by
  rcases lt_trichotomy c d with hlt | heq | hgt
  · exact absurd h (ggTh_lt hc hlt).ne
  · exact heq
  · exact absurd h.symm (ggTh_lt hd hgt).ne

/-- **The codes are closed under the inverse Veblen functions.** -/
theorem gg_invVeblen (hy0 : 0 < y) : ∀ c, GgCl y c → GgCl y (invVeblen₁ c) ∧ GgCl y (invVeblen₂ c) := by
  intro c hc
  induction hc with
  | @small x hx =>
    exact ⟨GgCl.small ((invVeblen₁_le x).trans_lt hx), GgCl.small ((invVeblen₂_le x).trans_lt hx)⟩
  | om =>
    have hS : SC (Om (1 : Ordinal.{0})) := SC_Om one_ne_zero
    have hG : Om (1 : Ordinal.{0}) ∈ range Γ_ := mem_range_gamma.2 hS.veblen_zero
    obtain ⟨o, ho⟩ := hG
    rw [← ho, invVeblen₁_gamma, invVeblen₂_gamma, ho]
    exact ⟨GgCl.om, GgCl.zero hy0⟩
  | @add x z hx hz ihx ihz =>
    rcases (right_le_opow (x + z) one_lt_omega0).lt_or_eq with hlt | heq
    · rw [invVeblen₁_of_lt_opow hlt, invVeblen₂_of_lt_opow hlt]
      exact ⟨GgCl.zero hy0, GgCl.add hx hz⟩
    · -- an `ε`-number `x + z`: the sum is `z` (or `x` with `z = 0`)
      have hP : Indec (x + z) := inE_indec heq.symm
      rcases eq_or_ne z 0 with rfl | hz0
      · simpa using ihx
      · have hxs : x < x + z := lt_add_of_pos_right x (pos_iff_ne_zero.2 hz0)
        have hzs : z = x + z := by
          refine le_antisymm le_add_self ?_
          by_contra h
          push Not at h
          exact lt_irrefl _ (hP.add_lt hxs h)
        rw [← hzs]; exact ihz
  | @phi x z hx hz ihx ihz =>
    rcases (right_le_veblen x z).lt_or_eq with hlt | heq
    · rcases eq_or_ne x 0 with rfl | hx0
      · -- `ω^z` with `z < ω^z` is no `ε`-number
        rw [veblen_zero_apply] at hlt ⊢
        have hnE : ω ^ z < ω ^ ω ^ z := (opow_lt_opow_iff_right one_lt_omega0).2 hlt
        rw [invVeblen₁_of_lt_opow hnE, invVeblen₂_of_lt_opow hnE]
        exact ⟨GgCl.zero hy0, GgCl.opow hy0 hz⟩
      · rw [invVeblen₁_veblen hlt, invVeblen₂_veblen hx0 hlt]
        exact ⟨hx, hz⟩
    · rw [← heq]; exact ihz

/-- **A code fixed by every `φ(a', ·)`, `a'` a code below `a ≠ 0`, is a value `φ(a, e)` with a code `e`.** -/
theorem gg_range (hy0 : 0 < y) {a c : Ordinal.{0}} (ha0 : a ≠ 0) (hc : GgCl y c)
    (hfix : ∀ a', GgCl y a' → a' < a → veblen a' c = c) : ∃ e, GgCl y e ∧ veblen a e = c := by
  have hE : ω ^ c = c := by
    have := hfix 0 (GgCl.zero hy0) (pos_iff_ne_zero.2 ha0); rwa [veblen_zero_apply] at this
  obtain ⟨hdC, heC⟩ := gg_invVeblen hy0 c hc
  have hdec : veblen (invVeblen₁ c) (invVeblen₂ c) = c := by rw [veblen_invVeblen₁_invVeblen₂, hE]
  have had : a ≤ invVeblen₁ c := by
    by_contra h
    push Not at h
    have h1 := hfix _ hdC h
    have h2 := lt_veblen_invVeblen₁ c
    rw [h1] at h2
    exact lt_irrefl _ h2
  rcases had.lt_or_eq with hlt | heq
  · refine ⟨c, hc, ?_⟩
    rw [← hdec, veblen_veblen_of_lt hlt]
  · exact ⟨invVeblen₂ c, heC, by rw [heq]; exact hdec⟩

/-- **`Θ_y(φ(a, b)) = φ(Θ_y(a), Θ_y(b))`** for codes `a`, `b` over a strongly critical `y < Ω₁`. -/
theorem ggTh_veblen (hy : SC y) : ∀ a, GgCl y a → ∀ b, GgCl y b →
    ggTh y (veblen a b) = veblen (ggTh y a) (ggTh y b) := by
  have hy0 : 0 < y := hy.1
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IHa =>
  intro ha b
  induction b using WellFoundedLT.induction with
  | ind b IHb =>
  intro hb
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [veblen_zero_apply, ggTh_opow hy hb, ggTh_small (zero_le : (0 : Ordinal.{0}) ≤ y), veblen_zero_apply]
  have hc : GgCl y (veblen a b) := GgCl.phi ha hb
  have hA0 : ggTh y a ≠ 0 := by
    have h := ggTh_lt (GgCl.zero hy0) (pos_iff_ne_zero.2 ha0)
    rw [ggTh_small zero_le] at h
    exact h.ne'
  -- the reading is fixed by every `φ(β, ·)`, `β < Θ_y(a)`
  have hfix : ∀ β < ggTh y a, veblen β (ggTh y (veblen a b)) = ggTh y (veblen a b) := by
    intro β hβ
    obtain ⟨a', ha'C, ha'a, e⟩ := ggTh_onto hβ
    rw [← e, ← IHa a' ha'a ha'C (veblen a b) hc, veblen_veblen_of_lt ha'a]
  obtain ⟨B', hB'⟩ := (mem_range_veblen hA0).2 hfix
  suffices hBB : B' = ggTh y b by rw [← hB', hBB]
  apply le_antisymm
  · -- `B' ≤ Θ_y(b)`
    by_contra hlt
    push Not at hlt
    have h1 : veblen (ggTh y a) (ggTh y b) < ggTh y (veblen a b) := by
      rw [← hB']; exact veblen_lt_veblen_iff_right.2 hlt
    obtain ⟨c, hcC, hca, ec⟩ := ggTh_onto h1
    have hcfix : ∀ a', GgCl y a' → a' < a → veblen a' c = c := by
      intro a' ha'C ha'a
      have h2 : ggTh y (veblen a' c) = ggTh y c := by
        rw [IHa a' ha'a ha'C c hcC, ec, veblen_veblen_of_lt (ggTh_lt ha'C ha'a)]
      exact gg_inj (GgCl.phi ha'C hcC) hcC h2
    obtain ⟨e, heC, rfl⟩ := gg_range hy0 ha0 hcC hcfix
    have heb : e < b := veblen_lt_veblen_iff_right.1 hca
    rw [IHb e heb heC] at ec
    have h3 : ggTh y e = ggTh y b := (isNormal_veblen _).strictMono.injective ec
    exact absurd h3 (ggTh_lt heC heb).ne
  · -- `Θ_y(b) ≤ B'`
    refine le_of_forall_lt fun B'' hB'' => ?_
    obtain ⟨e, heC, heb, ee⟩ := ggTh_onto hB''
    have h3 : ggTh y (veblen a e) < ggTh y (veblen a b) :=
      ggTh_lt (GgCl.phi ha heC) (veblen_lt_veblen_iff_right.2 heb)
    rw [IHb e heb heC, ee, ← hB'] at h3
    exact veblen_lt_veblen_iff_right.1 h3

end Googology.Trans.PoR.InaccPsi.R2.Gg
