import Googology.Trans.PoR.InaccPsi.R2.Points

/-!
# Lemma ST and Lemma FRAG with one base (`m = 1`)

Lemma ST and Theorem FRAG of the project's paper proof, for `m = 1`.  Axioms only from `R2.Cited`.

* `st_le1` (**Lemma ST (b)**): one base change `π_{σ,τ}` keeps and reflects `≤₁` of `R₁⁺` on
  `Tᵗ[σ] ∩ (τ, Ω₁)` against `Tᵗ[σ]`.
* `Move`: the properties of a base move `b ↦ c` above a `υ`-point `κ` on the domain
  `D(κ, b) = κ ∪ (seg(b) ∩ Ω₁ ∩ Tᵇ[κ])`; `move_down` (`c < b`, `Ψ = π_{c,b}`), `move_up`
  (`b < c`, `Ψ = π_{b,c}⁻¹`), `move_id`.
* `frag1` (**Theorem FRAG, `m = 1`**): the move is the identity below `κ`, sends `b` to `c` and
  `seg(b)` into `seg(c)`, is an isomorphism of `(D; 0, +, ≤, ≤₁)` onto its image (`R₁⁺`), and
  sends `υ`-points to `υ`-points and other ordinals to other ordinals.  Cases D1–D4 of
  the paper proof (F-d).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- **Lemma ST (b)** (the paper proof): for `σ < τ` in `E` (countable), `x ∈ Tᵗ[σ] ∩ (τ, Ω₁)` and
`y ∈ Tᵗ[σ]`: `x ≤₁ y ⇔ π_{σ,τ}(x) ≤₁ π_{σ,τ}(y)`. -/
theorem st_le1 {σ τ : Ordinal.{0}} (h : Bases σ τ) {x y : Ordinal.{0}} (hx : x ∈ TB τ σ)
    (h1 : τ < x) (h2 : x < Om1) (hy : y ∈ TB τ σ) :
    le1R x y ↔ le1R (pi σ τ x) (pi σ τ y) := by
  obtain ⟨l, hl, hlT, hpl⟩ := lh_pi h hx h1 h2
  have hm := (pi_bijOn h).2
  have key : ∀ a r z, IsLh1 a r → (le1R a z ↔ a ≤ z ∧ z ≤ r) := fun a r z hr =>
    ⟨fun h => ⟨le1R_le h, hr.2 z h⟩, fun h => le1R_of_le h.1 h.2 hr.1⟩
  rw [key x l y hl, key _ _ _ hpl, hm.le_iff_le hx hy, hm.le_iff_le hy hlT]

/-- The domain of a one-base FRAG move: `κ ∪ (seg(b) ∩ Ω₁ ∩ Tᵇ[κ])` (the paper proof, `D₁`). -/
def Dom1 (κ b mb : Ordinal.{0}) : Set Ordinal.{0} :=
  {x | x < κ} ∪ {x | b ≤ x ∧ x < mb ∧ x < Om1 ∧ x ∈ TB b κ}

/-- The properties of a base move `b ↦ c` on `Dom1 κ b mb` (`mc = c^∞`). -/
structure Move (κ b c mb mc : Ordinal.{0}) (Ψ : Ordinal.{0} → Ordinal.{0}) : Prop where
  fix : ∀ x, x < κ → Ψ x = x
  base : Ψ b = c
  seg : ∀ x ∈ Dom1 κ b mb, b ≤ x → c ≤ Ψ x ∧ Ψ x < mc ∧ Ψ x < Om1
  mono : StrictMonoOn Ψ (Dom1 κ b mb)
  add : ∀ x ∈ Dom1 κ b mb, ∀ y ∈ Dom1 κ b mb, ∀ z ∈ Dom1 κ b mb,
    (x + y = z ↔ Ψ x + Ψ y = Ψ z)
  le1 : ∀ x ∈ Dom1 κ b mb, ∀ y ∈ Dom1 κ b mb, b < x → (le1R x y ↔ le1R (Ψ x) (Ψ y))

theorem mem_Dom1_seg {κ b mb x : Ordinal.{0}} (hκb : κ < b) (hx : x ∈ Dom1 κ b mb)
    (hbx : b ≤ x) : b ≤ x ∧ x < mb ∧ x < Om1 ∧ x ∈ TB b κ := by
  rcases hx with hx | hx
  · exact absurd (lt_of_lt_of_le (hx.trans hκb) hbx) (lt_irrefl _)
  · exact hx

/-- `c < b`: the move `π_{c,b}`. -/
theorem move_down {κ b c mb mc : Ordinal.{0}} (hb : UpsPt b) (hc : UpsPt c)
    (hκc : κ < c) (hcb : c < b) (hb1 : b < Om1)
    (hTc : ∀ a, a < Om1 → (a ∈ Tset c ↔ a < mc)) :
    Move κ b c mb mc (pi c b) := by
  have hB : Bases c b := ⟨upsPt_inE hc, upsPt_inE hb, hcb, hb1⟩
  have hm := (pi_bijOn hB).2
  have hsub : Dom1 κ b mb ⊆ TB b c := by
    rintro x (hx | ⟨_, _, _, hxT, hxP⟩)
    · exact (TB_inter_lt hB (hx.trans (hκc.trans hcb))).2 (hx.trans hκc)
    · exact ⟨hxT, hxP.trans (Set.Iio_subset_Iio hκc.le)⟩
  have hbase := pi_base hB
  have hOm := pi_Om1 hB
  refine ⟨fun x hx => pi_lt hB (hx.trans hκc), hbase.2, ?_, hm.mono hsub, ?_, ?_⟩
  · intro x hx hbx
    have hxT := hsub hx
    obtain ⟨-, -, hx1, -⟩ := mem_Dom1_seg (hκc.trans hcb) hx hbx
    have h1 : c ≤ pi c b x :=
      calc c = pi c b b := hbase.2.symm
        _ ≤ pi c b x := (hm.le_iff_le hbase.1 hxT).2 hbx
    have h2 : pi c b x < Om1 := by
      rw [← hOm.2]; exact (hm.lt_iff_lt hxT hOm.1).2 hx1
    exact ⟨h1, (hTc _ h2).1 ((pi_bijOn hB).1.mapsTo hxT), h2⟩
  · intro x hx y hy z hz
    have hxT := hsub hx; have hyT := hsub hy; have hzT := hsub hz
    obtain ⟨hxyT, hpxy⟩ := pi_add hB hxT hyT
    constructor
    · intro h; rw [← hpxy, h]
    · intro h
      rw [← hpxy] at h
      exact (pi_bijOn hB).1.injOn hxyT hzT h
  · intro x hx y hy hbx
    obtain ⟨-, -, hx1, -⟩ := mem_Dom1_seg (hκc.trans hcb) hx hbx.le
    exact st_le1 hB (hsub hx) hbx hx1 (hsub hy)

/-- `b < c`: the move `π_{b,c}⁻¹`. -/
theorem move_up {κ b c mb mc : Ordinal.{0}} (hκ : UpsPt κ) (hb : UpsPt b) (hc : UpsPt c)
    (hκb : κ < b) (hbc : b < c) (hc1 : c < Om1)
    (hTc : ∀ a, a < Om1 → (a ∈ Tset c ↔ a < mc)) :
    Move κ b c mb mc (Function.invFunOn (pi b c) (TB c b)) := by
  set Ψ := Function.invFunOn (pi b c) (TB c b) with hΨ
  have hB : Bases b c := ⟨upsPt_inE hb, upsPt_inE hc, hbc, hc1⟩
  have hBk : Bases κ b := ⟨upsPt_inE hκ, upsPt_inE hb, hκb, hbc.trans hc1⟩
  have hbij := (pi_bijOn hB).1
  have hm := (pi_bijOn hB).2
  have hsubT : ∀ x ∈ Dom1 κ b mb, x ∈ Tset b := by
    rintro x (hx | ⟨_, _, _, hxT, _⟩)
    · exact ((TB_inter_lt hBk (hx.trans hκb)).2 hx).1
    · exact hxT
  have hmem : ∀ x ∈ Tset b, Ψ x ∈ TB c b ∧ pi b c (Ψ x) = x := by
    intro x hx
    have hex : ∃ a ∈ TB c b, pi b c a = x := hbij.surjOn hx
    exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩
  have hinv : ∀ y ∈ TB c b, Ψ (pi b c y) = y := by
    intro y hy
    have h := hmem _ (hbij.mapsTo hy)
    exact hbij.injOn h.1 hy h.2
  have hbase := pi_base hB
  have hOm := pi_Om1 hB
  have hD : ∀ x ∈ Dom1 κ b mb, Ψ x ∈ TB c b ∧ pi b c (Ψ x) = x :=
    fun x hx => hmem x (hsubT x hx)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxT : x ∈ TB c b := (TB_inter_lt hB ((hx.trans hκb).trans hbc)).2 (hx.trans hκb)
    have := hinv x hxT
    rwa [pi_lt hB (hx.trans hκb)] at this
  · have := hinv c hbase.1
    rwa [hbase.2] at this
  · intro x hx hbx
    obtain ⟨-, -, hx1, -⟩ := mem_Dom1_seg hκb hx hbx
    obtain ⟨hyT, hpy⟩ := hD x hx
    have h1 : c ≤ Ψ x := by
      by_contra hlt
      have := (hm.lt_iff_lt hyT hbase.1).2 (not_le.1 hlt)
      rw [hpy, hbase.2] at this
      exact absurd hbx (not_le.2 this)
    have h2 : Ψ x < Om1 := by
      by_contra hge
      have := (hm.le_iff_le hOm.1 hyT).2 (not_lt.1 hge)
      rw [hpy, hOm.2] at this
      exact absurd hx1 (not_lt.2 this)
    exact ⟨h1, (hTc _ h2).1 hyT.1, h2⟩
  · intro x hx y hy hxy
    obtain ⟨hxT, hpx⟩ := hD x hx
    obtain ⟨hyT, hpy⟩ := hD y hy
    by_contra hle
    have := (hm.le_iff_le hyT hxT).2 (not_lt.1 hle)
    rw [hpx, hpy] at this
    exact absurd hxy (not_lt.2 this)
  · intro x hx y hy z hz
    obtain ⟨hxT, hpx⟩ := hD x hx
    obtain ⟨hyT, hpy⟩ := hD y hy
    obtain ⟨hzT, hpz⟩ := hD z hz
    obtain ⟨hxyT, hpxy⟩ := pi_add hB hxT hyT
    constructor
    · intro h
      refine hbij.injOn hxyT hzT ?_
      rw [hpxy, hpx, hpy, hpz, h]
    · intro h
      have := congrArg (pi b c) h
      rw [hpxy, hpx, hpy, hpz] at this
      exact this
  · intro x hx y hy hbx
    obtain ⟨-, -, hx1, -⟩ := mem_Dom1_seg hκb hx hbx.le
    obtain ⟨hxT, hpx⟩ := hD x hx
    obtain ⟨hyT, hpy⟩ := hD y hy
    have hcx : c < Ψ x := by
      have h1 : c ≤ Ψ x := by
        by_contra hlt
        have := (hm.lt_iff_lt hxT hbase.1).2 (not_le.1 hlt)
        rw [hpx, hbase.2] at this
        exact absurd hbx.le (not_le.2 this)
      rcases eq_or_lt_of_le h1 with h | h
      · exfalso
        have := congrArg (pi b c) h
        rw [hpx, hbase.2] at this
        exact absurd this hbx.ne
      · exact h
    have hx1' : Ψ x < Om1 := by
      by_contra hge
      have := (hm.le_iff_le hOm.1 hxT).2 (not_lt.1 hge)
      rw [hpx, hOm.2] at this
      exact absurd hx1 (not_lt.2 this)
    have := st_le1 hB hxT hcx hx1' hyT
    rw [hpx, hpy] at this
    exact this.symm

/-- `b = c`: the identity. -/
theorem move_id {κ b mb : Ordinal.{0}} (hκb : κ < b) : Move κ b b mb mb id := by
  refine ⟨fun _ _ => rfl, rfl, ?_, fun _ _ _ _ h => h, fun _ _ _ _ _ _ => Iff.rfl,
    fun _ _ _ _ _ => Iff.rfl⟩
  intro x hx hbx
  obtain ⟨-, hxm, hx1, -⟩ := mem_Dom1_seg hκb hx hbx
  exact ⟨hbx, hxm, hx1⟩

/-- **Theorem FRAG with one base** (the paper proof, `m = 1`).  Let `κ` be a `υ`-point (so
`κ ∈ E`) and `b, c > κ` countable `υ`-points.  There is `Ψ` on
`D = κ ∪ (seg(b) ∩ Ω₁ ∩ Tᵇ[κ])` with
(F-a) `Ψ = id` on `κ`; (F-b) `Ψ(b) = c`, `Ψ[D ∩ seg(b)] ⊆ seg(c)`;
(F-c) `Ψ` is an isomorphism of `(D; 0, +, ≤)` onto its image;
(F-d) `x ≤₁ y ⇔ Ψ x ≤₁ Ψ y` (`R₁⁺`) on `D`; (F-e) `Ψ x` is a `υ`-point iff `x` is. -/
theorem frag1 {κ b c : Ordinal.{0}} (hκ : UpsPt κ) (hb : UpsPt b) (hc : UpsPt c)
    (hκb : κ < b) (hκc : κ < c) (hb1 : b < Om1) (hc1 : c < Om1) :
    ∃ mb mc : Ordinal.{0}, ∃ Ψ : Ordinal.{0} → Ordinal.{0}, IsNext b mb ∧ IsNext c mc ∧
      (∀ x, x < κ → Ψ x = x) ∧ Ψ b = c ∧
      (∀ x ∈ Dom1 κ b mb, b ≤ x → c ≤ Ψ x ∧ Ψ x < mc) ∧
      ArithIso (Dom1 κ b mb) (Ψ '' Dom1 κ b mb) Ψ ∧
      (∀ x ∈ Dom1 κ b mb, ∀ y ∈ Dom1 κ b mb, le1R x y ↔ le1R (Ψ x) (Ψ y)) ∧
      (∀ x ∈ Dom1 κ b mb, UpsPt (Ψ x) ↔ UpsPt x) := by
  obtain ⟨mb, hmb, -⟩ := exists_next hb hb1
  obtain ⟨mc, hmc, hTc⟩ := exists_next hc hc1
  have hMove : ∃ Ψ, Move κ b c mb mc Ψ := by
    rcases lt_trichotomy c b with hcb | rfl | hbc
    · exact ⟨_, move_down hb hc hκc hcb hb1 hTc⟩
    · rw [hmb.unique hmc]; exact ⟨_, move_id hκb⟩
    · exact ⟨_, move_up hκ hb hc hκb hbc hc1 hTc⟩
  obtain ⟨Ψ, hM⟩ := hMove
  have hbD : b ∈ Dom1 κ b mb :=
    Or.inr ⟨le_rfl, hmb.1, hb1, (pi_base ⟨upsPt_inE hκ, upsPt_inE hb, hκb, hb1⟩).1⟩
  -- a point of `D` is below `κ` or in `seg(b)`
  have hcases : ∀ x ∈ Dom1 κ b mb, x < κ ∨ b ≤ x := by
    rintro x (hx | hx)
    · exact Or.inl hx
    · exact Or.inr hx.1
  refine ⟨mb, mc, Ψ, hmb, hmc, hM.fix, hM.base, fun x hx hbx => ⟨(hM.seg x hx hbx).1,
    (hM.seg x hx hbx).2.1⟩, ⟨hM.mono.injOn.bijOn_image, hM.mono, hM.add⟩, ?_, ?_⟩
  · intro x hx y hy
    rcases hcases x hx with hxk | hbx <;> rcases hcases y hy with hyk | hby
    · rw [hM.fix x hxk, hM.fix y hyk]
    · -- D1
      rw [hM.fix x hxk, le1R_lt_ups hκ hxk (hκb.le.trans hby),
        le1R_lt_ups hκ hxk (hκc.le.trans (hM.seg y hy hby).1)]
    · -- `y < κ < b ≤ x`
      have h1 : ¬ le1R x y := fun h => absurd (le1R_le h)
        (not_le.2 (lt_of_lt_of_le (hyk.trans hκb) hbx))
      have h2 : ¬ le1R (Ψ x) (Ψ y) := by
        rw [hM.fix y hyk]
        exact fun h => absurd (le1R_le h)
          (not_le.2 (lt_of_lt_of_le (hyk.trans hκc) (hM.seg x hx hbx).1))
      exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
    · rcases eq_or_lt_of_le hbx with rfl | hbx'
      · -- D3: `x = b`
        rw [hM.base]
        exact ⟨fun _ => hc.2 _ (hM.seg y hy hby).1, fun _ => hb.2 _ hby⟩
      · -- D4
        exact hM.le1 x hx y hy hbx'
  · intro x hx
    rcases hcases x hx with hxk | hbx
    · rw [hM.fix x hxk]
    · rcases eq_or_lt_of_le hbx with rfl | hbx'
      · rw [hM.base]; exact ⟨fun _ => hb, fun _ => hc⟩
      · have hxm := (mem_Dom1_seg hκb hx hbx).2.1
        have hΨc : c < Ψ x := by rw [← hM.base]; exact hM.mono hbD hx hbx'
        exact ⟨fun h => absurd h (not_upsPt_gap hmc hΨc (hM.seg x hx hbx).2.1),
          fun h => absurd h (not_upsPt_gap hmb hbx' hxm)⟩

end Googology.Trans.PoR.InaccPsi.R2
