import Googology.Trans.PoR.InaccPsi.R2.Defs

/-!
# `R₂^C`: the recursion equations and the basic facts on `≤₁`, `≤₂`

All proved from the definitions of `R2.Defs` ([C09] Def 2.3, 5.2–5.4), with no axiom.

* `le1_iff`, `le2_iff`: the equations of [C09] Def 5.4, `α ≤ₙ β ⇔ α ≤ₙ^∞ β in R₂`.
* `le1_le`, `le2_le1`, `le1_refl`, `le2_refl`, `le1_antisymm` ([C09] Lemma 5.5 (3)–(6), part).
* `le1_of_le_of_le1` (the interval property: `α ≤ β ≤ γ`, `α ≤₁ γ` ⇒ `α ≤₁ β`).
* `le1_of_cofinal`, `le1_limit` (`α ≤₁ β` for all `β ∈ [α, λ)`, `λ` a limit ⇒ `α ≤₁ λ`).
* `le1_trans` ([C09] Lemma 5.5 (3), "straightforward"; with [C09] Lemma 2.5, `exists_closed`).
* `IsReach`, `LtInf`, `ltInf_iff`, `exists_reach`: the reach `lh(α) = max{γ | α ≤₁ γ}` exists
  unless `α ≤₁ γ` for every `γ ≥ α`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-! ## Closed sets -/

theorem DecompIn.mono {A B : Set Ordinal.{0}} (hAB : A ⊆ B) {x : Ordinal.{0}}
    (h : DecompIn A x) : DecompIn B x := by
  rcases h with h | ⟨y, hy, z, hz, h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨y, hAB hy, z, hAB hz, h1, h2, h3⟩

theorem Closed.union {A B : Set Ordinal.{0}} (hA : Closed A) (hB : Closed B) :
    Closed (A ∪ B) := by
  intro x hx hd
  rcases hx with hx | hx
  · exact (hA x hx hd).mono Set.subset_union_left
  · exact (hB x hx hd).mono Set.subset_union_right

theorem closed_empty : Closed (∅ : Set Ordinal.{0}) := by
  intro x hx; simp at hx

/-- One ordinal lies in a finite closed set of ordinals `≤` it. -/
theorem exists_closed_single (x : Ordinal.{0}) :
    ∃ C : Finset Ordinal.{0}, x ∈ C ∧ Closed ↑C ∧ ∀ c ∈ C, c ≤ x := by
  induction x using WellFoundedLT.induction with
  | ind x IH =>
    by_cases hd : ∃ y z, y < x ∧ z < x ∧ y + z = x
    · obtain ⟨y, z, hy, hz, hyz⟩ := hd
      obtain ⟨Cy, hyC, hCy, hby⟩ := IH y hy
      obtain ⟨Cz, hzC, hCz, hbz⟩ := IH z hz
      refine ⟨insert x (Cy ∪ Cz), by simp, ?_, ?_⟩
      · intro c hc hdc
        simp only [Finset.coe_insert, Finset.coe_union, Set.mem_insert_iff, Set.mem_union,
          Finset.mem_coe] at hc
        rcases hc with rfl | hc | hc
        · exact Or.inr ⟨y, by simp [hyC], z, by simp [hzC], hy, hz, hyz⟩
        · refine (hCy c hc hdc).mono ?_
          intro w hw; simp only [Finset.coe_insert, Finset.coe_union]; simp_all
        · refine (hCz c hc hdc).mono ?_
          intro w hw; simp only [Finset.coe_insert, Finset.coe_union]; simp_all
      · intro c hc
        simp only [Finset.mem_insert, Finset.mem_union] at hc
        rcases hc with rfl | hc | hc
        · exact le_rfl
        · exact (hby c hc).trans hy.le
        · exact (hbz c hc).trans hz.le
    · refine ⟨{x}, by simp, ?_, by simp⟩
      intro c hc hdc
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hc
      subst hc
      rcases hdc with h0 | h
      · exact Or.inl h0
      · exact absurd h hd

/-- **[C09] Lemma 2.5** (for `R₀`): every finite set lies in a finite closed set; here
every element of the closed set is at most some element of the given set. -/
theorem exists_closed (S : Finset Ordinal.{0}) :
    ∃ C : Finset Ordinal.{0}, S ⊆ C ∧ Closed ↑C ∧ ∀ c ∈ C, ∃ s ∈ S, c ≤ s := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simpa using closed_empty, by simp⟩
  | insert s S _ ih =>
    obtain ⟨C, hSC, hC, hb⟩ := ih
    obtain ⟨Cs, hsC, hCs, hbs⟩ := exists_closed_single s
    refine ⟨Cs ∪ C, ?_, ?_, ?_⟩
    · intro w hw
      simp only [Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · exact Finset.mem_union_left _ hsC
      · exact Finset.mem_union_right _ (hSC hw)
    · rw [Finset.coe_union]; exact hCs.union hC
    · intro c hc
      rcases Finset.mem_union.1 hc with hc | hc
      · exact ⟨s, by simp, hbs c hc⟩
      · obtain ⟨t, ht, hct⟩ := hb c hc
        exact ⟨t, Finset.mem_insert_of_mem ht, hct⟩

/-! ## Arithmetic isomorphisms and coverings -/

theorem add_self_eq_self {a : Ordinal.{0}} (h : a + a = a) : a = 0 := by
  have : a + a = a + 0 := by rw [add_zero]; exact h
  exact (add_left_cancel_iff).1 this

theorem ArithIso.map_zero {A B : Set Ordinal.{0}} {h : Ordinal.{0} → Ordinal.{0}}
    (hh : ArithIso A B h) (h0 : (0 : Ordinal.{0}) ∈ A) : h 0 = 0 :=
  add_self_eq_self ((hh.2.2 0 h0 0 h0 0 h0).1 (add_zero 0))

/-- The image of a closed subset under an arithmetic isomorphism onto a closed set is
closed. -/
theorem closed_image {A B S : Set Ordinal.{0}} {h : Ordinal.{0} → Ordinal.{0}}
    (hh : ArithIso A B h) (hB : Closed B) (hSA : S ⊆ A) (hS : Closed S) :
    Closed (h '' S) := by
  rintro z ⟨s, hs, rfl⟩ hdz
  have hsA := hSA hs
  by_cases hz0 : h s = 0
  · exact Or.inl hz0
  rcases hB (h s) (hh.1.mapsTo hsA) hdz with h0 | ⟨u, hu, v, hv, hu1, hv1, huv⟩
  · exact Or.inl h0
  obtain ⟨u', hu'A, rfl⟩ := hh.1.surjOn hu
  obtain ⟨v', hv'A, rfl⟩ := hh.1.surjOn hv
  have hsum : u' + v' = s := (hh.2.2 u' hu'A v' hv'A s hsA).2 huv
  have hu's : u' < s := (hh.2.1.lt_iff_lt hu'A hsA).1 hu1
  have hv's : v' < s := (hh.2.1.lt_iff_lt hv'A hsA).1 hv1
  rcases hS s hs (Or.inr ⟨u', v', hu's, hv's, hsum⟩) with h0 | ⟨p, hp, q, hq, hp1, hq1, hpq⟩
  · subst h0; exact absurd (hh.map_zero hsA) hz0
  · refine Or.inr ⟨h p, ⟨p, hp, rfl⟩, h q, ⟨q, hq, rfl⟩, ?_, ?_, ?_⟩
    · exact hh.2.1 (hSA hp) hsA hp1
    · exact hh.2.1 (hSA hq) hsA hq1
    · exact ((hh.2.2 p (hSA hp) q (hSA hq) s hsA).1 hpq)

theorem ArithIso.comp {A B C : Set Ordinal.{0}} {g f : Ordinal.{0} → Ordinal.{0}}
    (hg : ArithIso A B g) (hf : ArithIso B C f) : ArithIso A C (f ∘ g) := by
  refine ⟨hf.1.comp hg.1, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hf.2.1 (hg.1.mapsTo hx) (hg.1.mapsTo hy) (hg.2.1 hx hy hxy)
  · intro x hx y hy z hz
    rw [hg.2.2 x hx y hy z hz]
    exact hf.2.2 _ (hg.1.mapsTo hx) _ (hg.1.mapsTo hy) _ (hg.1.mapsTo hz)

theorem Cov.comp {R₁ R₂ R₃ : Str} {A B C : Set Ordinal.{0}} {g f : Ordinal.{0} → Ordinal.{0}}
    (hg : Cov R₁ R₂ A B g) (hf : Cov R₂ R₃ B C f) : Cov R₁ R₃ A C (f ∘ g) := by
  refine ⟨hg.1.comp hf.1, ?_, ?_⟩
  · intro x hx y hy hr
    exact hf.2.1 _ (hg.1.1.mapsTo hx) _ (hg.1.1.mapsTo hy) (hg.2.1 x hx y hy hr)
  · intro x hx y hy hr
    exact hf.2.2 _ (hg.1.1.mapsTo hx) _ (hg.1.1.mapsTo hy) (hg.2.2 x hx y hy hr)

theorem Cov.restrict {R R' : Str} {A B S : Set Ordinal.{0}} {h : Ordinal.{0} → Ordinal.{0}}
    (hh : Cov R R' A B h) (hSA : S ⊆ A) : Cov R R' S (h '' S) h := by
  refine ⟨⟨⟨fun x hx => ⟨x, hx, rfl⟩, hh.1.1.injOn.mono hSA, fun y hy => hy⟩,
    hh.1.2.1.mono hSA, fun x hx y hy z hz => hh.1.2.2 x (hSA hx) y (hSA hy) z (hSA hz)⟩,
    fun x hx y hy => hh.2.1 x (hSA hx) y (hSA hy),
    fun x hx y hy => hh.2.2 x (hSA hx) y (hSA hy)⟩

theorem Cov.id (R : Str) (A : Set Ordinal.{0}) : Cov R R A A id :=
  ⟨⟨Set.bijOn_id A, fun _ _ _ _ h => h, fun _ _ _ _ _ _ => Iff.rfl⟩,
    fun _ _ _ _ h => h, fun _ _ _ _ h => h⟩

/-- A strictly increasing bijection of `A` onto `B` fixes a common initial part `S` of `A`
and `B`. -/
theorem fix_initial {A B S : Set Ordinal.{0}} {h : Ordinal.{0} → Ordinal.{0}}
    (hb : Set.BijOn h A B) (hm : StrictMonoOn h A) (hSA : S ⊆ A) (hSB : S ⊆ B)
    (hA : ∀ x ∈ A, x ∉ S → ∀ s ∈ S, s < x) (hB : ∀ x ∈ B, x ∉ S → ∀ s ∈ S, s < x) :
    ∀ s ∈ S, h s = s := by
  intro s
  induction s using WellFoundedLT.induction with
  | ind s IH =>
    intro hs
    rcases lt_trichotomy (h s) s with hlt | heq | hgt
    · exfalso
      have hhsB : h s ∈ B := hb.mapsTo (hSA hs)
      have hhsS : h s ∈ S := by
        by_contra hn; exact absurd (hB _ hhsB hn s hs) (not_lt.2 hlt.le)
      have := IH (h s) hlt hhsS
      have := hb.injOn (hSA hhsS) (hSA hs) this
      exact absurd this hlt.ne
    · exact heq
    · exfalso
      obtain ⟨t, htA, hts⟩ := hb.surjOn (hSB hs)
      have htlt : t < s := (hm.lt_iff_lt htA (hSA hs)).1 (by rw [hts]; exact hgt)
      have htS : t ∈ S := by
        by_contra hn; exact absurd (hA t htA hn s hs) (not_lt.2 htlt.le)
      have := IH t htlt htS
      rw [hts] at this
      exact absurd this htlt.ne'

/-! ## Congruence: `≤ₙ^∞` only reads the relations below the right end -/

/-- `R` and `R'` agree on all pairs below `b`. -/
def Agree (R R' : Str) (b : Ordinal.{0}) : Prop :=
  ∀ x y, x < b → y < b → (R.le1 x y ↔ R'.le1 x y) ∧ (R.le2 x y ↔ R'.le2 x y)

theorem Agree.symm {R R' : Str} {b : Ordinal.{0}} (h : Agree R R' b) : Agree R' R b :=
  fun x y hx hy => ⟨(h x y hx hy).1.symm, (h x y hx hy).2.symm⟩

theorem Cov.congr {P R R' : Str} {b : Ordinal.{0}} (hA : Agree R R' b) {A B : Set Ordinal.{0}}
    (hB : ∀ y ∈ B, y < b) {h : Ordinal.{0} → Ordinal.{0}} (hc : Cov P R A B h) :
    Cov P R' A B h := by
  refine ⟨hc.1, fun x hx y hy hr => ?_, fun x hx y hy hr => ?_⟩
  · exact ((hA _ _ (hB _ (hc.1.1.mapsTo hx)) (hB _ (hc.1.1.mapsTo hy))).1).1 (hc.2.1 x hx y hy hr)
  · exact ((hA _ _ (hB _ (hc.1.1.mapsTo hx)) (hB _ (hc.1.1.mapsTo hy))).2).1 (hc.2.2 x hx y hy hr)

theorem Cov.congr_src {P R R' : Str} {b : Ordinal.{0}} (hA : Agree R R' b) {A B : Set Ordinal.{0}}
    (hAb : ∀ y ∈ A, y < b) {h : Ordinal.{0} → Ordinal.{0}} (hc : Cov R P A B h) :
    Cov R' P A B h := by
  refine ⟨hc.1, fun x hx y hy hr => ?_, fun x hx y hy hr => ?_⟩
  · exact hc.2.1 x hx y hy (((hA _ _ (hAb _ hx) (hAb _ hy)).1).2 hr)
  · exact hc.2.2 x hx y hy (((hA _ _ (hAb _ hx) (hAb _ hy)).2).2 hr)

theorem Cov.congr_both {R R' : Str} {b : Ordinal.{0}} (hA : Agree R R' b) {A B : Set Ordinal.{0}}
    (hAb : ∀ y ∈ A, y < b) (hB : ∀ y ∈ B, y < b) {h : Ordinal.{0} → Ordinal.{0}}
    (hc : Cov R R A B h) : Cov R' R' A B h :=
  (hc.congr_src hA hAb).congr hA hB

theorem mem_union_lt {X Y : Finset Ordinal.{0}} {b : Ordinal.{0}} (hX : ∀ x ∈ X, x < b)
    (hY : ∀ y ∈ Y, y < b) : ∀ z ∈ (↑(X ∪ Y) : Set Ordinal.{0}), z < b := by
  intro z hz
  rcases Finset.mem_union.1 (Finset.mem_coe.1 hz) with h | h
  · exact hX z h
  · exact hY z h

theorem Inf1.congr {R R' : Str} {a b : Ordinal.{0}} (hA : Agree R R' b) (h : Inf1 R a b) :
    Inf1 R' a b := by
  obtain ⟨hab, H⟩ := h
  refine ⟨hab, fun X Y hX hY hXY => ?_⟩
  obtain ⟨Yt, h1, h2, h3, f, hf⟩ := H X Y hX hY hXY
  refine ⟨Yt, h1, h2, h3, f, hf.congr_both hA ?_ ?_⟩
  · exact mem_union_lt (fun x hx => lt_of_lt_of_le (hX x hx) hab) (fun y hy => (hY y hy).2)
  · exact mem_union_lt (fun x hx => lt_of_lt_of_le (hX x hx) hab)
      (fun y hy => lt_of_lt_of_le (h1 y hy) hab)

theorem CofCov.congr {R R' : Str} {c : Ordinal.{0}} (hA : Agree R R' c) {X Z : Finset Ordinal.{0}}
    {P : Str} (hX : ∀ x ∈ X, x < c) (h : CofCov R X Z P c) : CofCov R' X Z P c := by
  intro c' hc'
  obtain ⟨Y, h1, h2, f, hf⟩ := h c' hc'
  exact ⟨Y, h1, h2, f, hf.congr hA (mem_union_lt hX (fun y hy => (h1 y hy).2))⟩

theorem Inf2.congr {R R' : Str} {t t' : Ordinal.{0} → Prop} {a b : Ordinal.{0}}
    (hA : Agree R R' b) (ht : ∀ y, a ≤ y → y < b → (t y ↔ t' y)) (h : Inf2 R t a b) :
    Inf2 R' t' a b := by
  obtain ⟨hab, H1, H2⟩ := h
  refine ⟨hab, fun X Y hX hY hXY => ?_, fun X hX Z P hZ hC => ?_⟩
  · obtain ⟨Yt, h1, h2, h3, f, hf, hd⟩ := H1 X Y hX hY hXY
    have hXb : ∀ x ∈ X, x < b := fun x hx => lt_of_lt_of_le (hX x hx) hab
    refine ⟨Yt, h1, h2, h3, f, hf.congr_both hA (mem_union_lt hXb (fun y hy => (hY y hy).2))
      (mem_union_lt hXb (fun y hy => lt_of_lt_of_le (h1 y hy) hab)), ?_⟩
    intro y hy hty
    have hab' : a < b := lt_of_le_of_lt (hY y hy).1 (hY y hy).2
    have hfy : f y < a := by
      have hmem : f y ∈ (↑(X ∪ Yt) : Set Ordinal.{0}) :=
        hf.1.1.mapsTo (by simp [hy])
      rcases Finset.mem_union.1 (Finset.mem_coe.1 hmem) with h' | h'
      · exact hX _ h'
      · exact h1 _ h'
    exact ((hA _ _ (hfy.trans hab') hab').1).1
      (hd y hy ((ht y (hY y hy).1 (hY y hy).2).2 hty))
  · rcases eq_or_lt_of_le hab with rfl | hab'
    · exact (H2 X hX Z P hZ (hC.congr hA.symm hX)).congr hA hX
    · have hXb : ∀ x ∈ X, x < b := fun x hx => (hX x hx).trans hab'
      have hAa : Agree R R' a := fun x y hx hy => hA x y (hx.trans hab') (hy.trans hab')
      exact (H2 X hX Z P hZ (hC.congr hAa.symm hX)).congr hA hXb

/-! ## The recursion equations ([C09] Def 5.4) -/

theorem col_eq (b : Ordinal.{0}) :
    col b = fun a => (Inf1 (below b fun y _ => col y) a b,
      Inf2 (below b fun y _ => col y) (fun y => Inf1 (below b fun y _ => col y) y b) a b) :=
  (wellFounded_lt (α := Ordinal.{0})).fix_eq _ b

theorem agree_below (b : Ordinal.{0}) : Agree (below b fun y _ => col y) R2C b := by
  intro x y _ hy
  exact ⟨⟨fun ⟨_, h⟩ => h, fun h => ⟨hy, h⟩⟩, ⟨fun ⟨_, h⟩ => h, fun h => ⟨hy, h⟩⟩⟩

/-- **[C09] Def 5.4** for `≤₁`: `α ≤₁ β ⇔ α ≤₁^∞ β in R₂`. -/
theorem le1_iff {a b : Ordinal.{0}} : le1 a b ↔ Inf1 R2C a b := by
  unfold le1
  rw [col_eq b]
  exact ⟨fun h => h.congr (agree_below b), fun h => h.congr (agree_below b).symm⟩

/-- **[C09] Def 5.4** for `≤₂`: `α ≤₂ β ⇔ α ≤₂^∞ β in R₂` (clause 1(d) reads `y ≤₁ β`). -/
theorem le2_iff {a b : Ordinal.{0}} : le2 a b ↔ Inf2 R2C (fun y => le1 y b) a b := by
  unfold le2
  rw [col_eq b]
  constructor
  · intro h
    exact h.congr (agree_below b) (fun y _ _ => by
      show _ ↔ le1 y b
      rw [le1_iff]
      exact ⟨fun h => h.congr (agree_below b), fun h => h.congr (agree_below b).symm⟩)
  · intro h
    exact h.congr (agree_below b).symm (fun y _ _ => by
      show le1 y b ↔ _
      rw [le1_iff]
      exact ⟨fun h => h.congr (agree_below b).symm, fun h => h.congr (agree_below b)⟩)

/-! ## Basic facts ([C09] Lemma 5.5, parts) -/

/-- [C09] Lemma 5.5 (5): `≤₁` respects `≤`. -/
theorem le1_le {a b : Ordinal.{0}} (h : le1 a b) : a ≤ b := (le1_iff.1 h).1

/-- [C09] Lemma 5.5 (6), first remark: `≤₂ ⊆ ≤₁`. -/
theorem le2_le1 {a b : Ordinal.{0}} (h : le2 a b) : le1 a b := by
  obtain ⟨hab, H1, _⟩ := le2_iff.1 h
  refine le1_iff.2 ⟨hab, fun X Y hX hY hXY => ?_⟩
  obtain ⟨Yt, h1, h2, h3, f, hf, _⟩ := H1 X Y hX hY hXY
  exact ⟨Yt, h1, h2, h3, f, hf⟩

theorem le2_le {a b : Ordinal.{0}} (h : le2 a b) : a ≤ b := le1_le (le2_le1 h)

theorem empty_of_Ico_self {Y : Finset Ordinal.{0}} {a : Ordinal.{0}}
    (hY : ∀ y ∈ Y, a ≤ y ∧ y < a) : Y = ∅ := by
  ext y; simp only [Finset.notMem_empty, iff_false]
  intro hy; exact absurd (hY y hy).2 (not_lt.2 (hY y hy).1)

/-- [C09] Lemma 5.5 (3): `≤₁` is reflexive. -/
theorem le1_refl (a : Ordinal.{0}) : le1 a a := by
  refine le1_iff.2 ⟨le_rfl, fun X Y _ hY hXY => ?_⟩
  obtain rfl := empty_of_Ico_self hY
  exact ⟨∅, by simp, by simp, hXY, id, Cov.id _ _⟩

/-- [C09] Lemma 5.5 (4): `≤₂` is reflexive. -/
theorem le2_refl (a : Ordinal.{0}) : le2 a a := by
  refine le2_iff.2 ⟨le_rfl, fun X Y _ hY hXY => ?_, fun _ _ _ _ _ h => h⟩
  obtain rfl := empty_of_Ico_self hY
  exact ⟨∅, by simp, by simp, hXY, id, Cov.id _ _, by simp⟩

theorem le1_antisymm {a b : Ordinal.{0}} (h1 : le1 a b) (h2 : le1 b a) : a = b :=
  le_antisymm (le1_le h1) (le1_le h2)

/-- **Interval property** ([W07b] Lemma 2.1 (b) for `R₁`; here for `R₂^C`, from the
definition): `α ≤ β ≤ γ` and `α ≤₁ γ` give `α ≤₁ β`. -/
theorem le1_of_le_of_le1 {a b c : Ordinal.{0}} (hab : a ≤ b) (hbc : b ≤ c) (h : le1 a c) :
    le1 a b := by
  obtain ⟨_, H⟩ := le1_iff.1 h
  exact le1_iff.2 ⟨hab, fun X Y hX hY hXY =>
    H X Y hX (fun y hy => ⟨(hY y hy).1, lt_of_lt_of_le (hY y hy).2 hbc⟩) hXY⟩

/-- Cofinality: if every `y ∈ [α, s)` lies below some `t` with `α ≤₁ t`, then `α ≤₁ s`. -/
theorem le1_of_cofinal {a s : Ordinal.{0}} (has : a ≤ s)
    (h : ∀ y, a ≤ y → y < s → ∃ t, y < t ∧ le1 a t) : le1 a s := by
  refine le1_iff.2 ⟨has, fun X Y hX hY hXY => ?_⟩
  have key : ∀ Y' : Finset Ordinal.{0}, (∀ y ∈ Y', a ≤ y ∧ y < s) →
      ∃ t, le1 a t ∧ ∀ y ∈ Y', y < t := by
    intro Y'
    classical
    induction Y' using Finset.induction_on with
    | empty => exact fun _ => ⟨a, le1_refl a, by simp⟩
    | insert y Y' _ ih =>
      intro hY'
      obtain ⟨t, ht, htY⟩ := ih (fun z hz => hY' z (Finset.mem_insert_of_mem hz))
      obtain ⟨t', hyt', ht'⟩ := h y (hY' y (by simp)).1 (hY' y (by simp)).2
      refine ⟨max t t', ?_, ?_⟩
      · rcases le_total t t' with htt | htt
        · rw [max_eq_right htt]; exact ht'
        · rw [max_eq_left htt]; exact ht
      · intro z hz
        rcases Finset.mem_insert.1 hz with rfl | hz
        · exact lt_of_lt_of_le hyt' (le_max_right _ _)
        · exact lt_of_lt_of_le (htY z hz) (le_max_left _ _)
  obtain ⟨t, ht, htY⟩ := key Y hY
  exact (le1_iff.1 ht).2 X Y hX (fun y hy => ⟨(hY y hy).1, htY y hy⟩) hXY

/-- **Limit property** ([W07b] Lemma 2.1 (a) for `R₁`; here for `R₂^C`, from the
definition): `α ≤₁ β` for every `β ∈ [α, λ)`, `λ` a limit above `α`, gives `α ≤₁ λ`. -/
theorem le1_limit {a l : Ordinal.{0}} (hl : Order.IsSuccLimit l) (hal : a < l)
    (h : ∀ b, a ≤ b → b < l → le1 a b) : le1 a l :=
  le1_of_cofinal hal.le fun y hay hyl =>
    ⟨Order.succ y, Order.lt_succ y, h _ (hay.trans (Order.le_succ y)) (hl.succ_lt hyl)⟩

/-- **[C09] Lemma 5.5 (3)**: `≤₁` is transitive. -/
theorem le1_trans {a b c : Ordinal.{0}} (hab : le1 a b) (hbc : le1 b c) : le1 a c := by
  classical
  obtain ⟨hab', Hab⟩ := le1_iff.1 hab
  obtain ⟨hbc', Hbc⟩ := le1_iff.1 hbc
  refine le1_iff.2 ⟨hab'.trans hbc', fun X Y hX hY hXY => ?_⟩
  rcases eq_or_lt_of_le hab' with rfl | hlt
  · exact Hbc X Y hX hY hXY
  -- the part of `Y` below `b` goes into the fixed set
  set Y1 := Y.filter (· < b) with hY1
  set Y2 := Y.filter (fun y => b ≤ y) with hY2
  obtain ⟨Xp, hsub, hXpC, hXpb⟩ := exists_closed (insert a (X ∪ Y1))
  have haXp : a ∈ Xp := hsub (by simp)
  have hXXp : ∀ x ∈ X, x ∈ Xp := fun x hx => hsub (by simp [hx])
  have hY1Xp : ∀ y ∈ Y, y < b → y ∈ Xp := fun y hy hyb => hsub (by simp [hY1, hy, hyb])
  have hXp_lt : ∀ x ∈ Xp, x < b := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := hXpb x hx
    refine lt_of_le_of_lt hxs ?_
    simp only [Finset.mem_insert, Finset.mem_union, hY1, Finset.mem_filter] at hs
    rcases hs with rfl | hs | hs
    · exact hlt
    · exact (hX s hs).trans hlt
    · exact hs.2
  have hY2b : ∀ y ∈ Y2, b ≤ y ∧ y < c := by
    intro y hy
    simp only [hY2, Finset.mem_filter] at hy
    exact ⟨hy.2, (hY y hy.1).2⟩
  have hXYsub : (↑(X ∪ Y) : Set Ordinal.{0}) ⊆ ↑(Xp ∪ Y2) := by
    intro z hz
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hz ⊢
    rcases hz with hz | hz
    · exact Or.inl (hXXp z hz)
    · by_cases hzb : z < b
      · exact Or.inl (hY1Xp z hz hzb)
      · exact Or.inr (by simp [hY2, hz, not_lt.1 hzb])
  have hclosed : Closed ↑(Xp ∪ Y2) := by
    intro z hz hdz
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hz) with hz | hz
    · exact (hXpC z hz hdz).mono (by simp)
    · have hzY : z ∈ Y := (Finset.mem_filter.1 hz).1
      exact (hXY z (by simp [hzY]) hdz).mono hXYsub
  obtain ⟨Yt2, hYt2b, hXpYt2, hcl2, h2, hcov2⟩ := Hbc Xp Y2 hXp_lt hY2b hclosed
  have hfix : ∀ x ∈ (↑Xp : Set Ordinal.{0}), h2 x = x := by
    refine fix_initial hcov2.1.1 hcov2.1.2.1 (by simp) (by simp) ?_ ?_
    · intro x hx hxn s hs
      rcases Finset.mem_union.1 (Finset.mem_coe.1 hx) with hx | hx
      · exact absurd hx hxn
      · exact lt_of_lt_of_le (hXp_lt s hs) (hY2b x hx).1
    · intro x hx hxn s hs
      rcases Finset.mem_union.1 (Finset.mem_coe.1 hx) with hx | hx
      · exact absurd hx hxn
      · exact hXpYt2 s hs x hx
  -- the moved set `Y' = h2[Y] ⊆ [a, b)`
  set Yp := Y.image h2 with hYpdef
  have hYp : ∀ y ∈ Yp, a ≤ y ∧ y < b := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    by_cases hyb : y < b
    · rw [hfix y (hY1Xp y hy hyb)]; exact ⟨(hY y hy).1, hyb⟩
    · have hyY2 : y ∈ Y2 := by simp [hY2, hy, not_lt.1 hyb]
      have hmem : h2 y ∈ (↑(Xp ∪ Yt2) : Set Ordinal.{0}) := hcov2.1.1.mapsTo (by simp [hyY2])
      rcases Finset.mem_union.1 (Finset.mem_coe.1 hmem) with hm | hm
      · exfalso
        have h22 : h2 (h2 y) = h2 y := hfix _ hm
        have := hcov2.1.1.injOn (by simp [hm]) (by simp [hyY2]) h22
        exact absurd (this ▸ hXp_lt _ hm) hyb
      · exact ⟨(hXpYt2 a haXp _ hm).le, hYt2b _ hm⟩
  have himg : (↑(X ∪ Yp) : Set Ordinal.{0}) = h2 '' ↑(X ∪ Y) := by
    rw [← Finset.coe_image, Finset.image_union, hYpdef]
    congr 2
    conv_lhs => rw [← Finset.image_id (s := X)]
    exact (Finset.image_congr (fun x hx => (hfix x (hXXp x hx)).symm))
  have hclW : Closed ↑(X ∪ Yp) := by
    rw [himg]; exact closed_image hcov2.1 hcl2 hXYsub hXY
  have hcovW : Cov R2C R2C ↑(X ∪ Y) ↑(X ∪ Yp) h2 := by
    rw [himg]; exact hcov2.restrict hXYsub
  obtain ⟨Yt, h1a, h1b, h1c, h1, hcov1⟩ := Hab X Yp hX hYp hclW
  exact ⟨Yt, h1a, h1b, h1c, h1 ∘ h2, hcovW.comp hcov1⟩

/-! ## The reach -/

/-- `r = lh(α)` in `R` ([W07b] Def 3.1): `r` is the largest ordinal with `α ≤₁ r`. -/
def IsReach (R : Str) (a r : Ordinal.{0}) : Prop := R.le1 a r ∧ ∀ g, R.le1 a g → g ≤ r

/-- `α <₁ ∞` in `R` ([W07b] Def 3.1): `lh(α) = ∞`, i.e. `max{β | α ≤₁ β}` does not exist. -/
def LtInf (R : Str) (a : Ordinal.{0}) : Prop := ¬ ∃ r, IsReach R a r

/-- In `R₂^C`, the reach exists as soon as `α ≤₁ γ` fails for some `γ`. -/
theorem exists_reach {a g : Ordinal.{0}} (hag : a ≤ g) (hg : ¬ le1 a g) :
    ∃ r, IsReach R2C a r := by
  set S := {t | le1 a t} with hS
  have hbdd : BddAbove S := by
    refine ⟨g, fun t ht => ?_⟩
    by_contra hlt
    exact hg (le1_of_le_of_le1 hag (not_le.1 hlt).le ht)
  have haS : a ∈ S := le1_refl a
  refine ⟨sSup S, ?_, fun t ht => le_csSup hbdd ht⟩
  refine le1_of_cofinal (le_csSup hbdd haS) fun y _ hy => ?_
  obtain ⟨t, ht, hyt⟩ := exists_lt_of_lt_csSup ⟨a, haS⟩ hy
  exact ⟨t, hyt, ht⟩

/-- In `R₂^C`: `α <₁ ∞` iff `α ≤₁ γ` for every `γ ≥ α`. -/
theorem ltInf_iff {a : Ordinal.{0}} : LtInf R2C a ↔ ∀ g, a ≤ g → le1 a g := by
  constructor
  · intro h g hag
    by_contra hg
    exact h (exists_reach hag hg)
  · rintro h ⟨r, hr, hmax⟩
    have := hmax (Order.succ r) (h _ ((le1_le hr).trans (Order.le_succ r)))
    exact absurd this (not_le.2 (Order.lt_succ r))

/-! ## Cofinal copies ([C09] Lemma 5.5 (1), (2)) -/

/-- The cofinal form of a copy clause: if every `X ∪ Y` has a copy `X ∪ Ỹ` below `a`, with a
covering that satisfies `Q`, then the copy can be taken above any `a' < a`, by a covering that
fixes `X` ([C09] Lemma 5.5 (1), (2): enlarge `X` to a closed `X⁺ ∋ a'`, [C09] Lemma 2.5). -/
theorem cof_core {a b a' : Ordinal.{0}} (ha' : a' < a) (Q : Ordinal.{0} → Ordinal.{0} → Prop)
    (H : ∀ X Y : Finset Ordinal.{0}, (∀ x ∈ X, x < a) → (∀ y ∈ Y, a ≤ y ∧ y < b) →
      Closed ↑(X ∪ Y) → ∃ Yt : Finset Ordinal.{0}, (∀ y ∈ Yt, y < a) ∧
        (∀ x ∈ X, ∀ y ∈ Yt, x < y) ∧ Closed ↑(X ∪ Yt) ∧
        ∃ h, Cov R2C R2C ↑(X ∪ Y) ↑(X ∪ Yt) h ∧ ∀ y ∈ Y, Q y (h y))
    (X Y : Finset Ordinal.{0}) (hX : ∀ x ∈ X, x < a) (hY : ∀ y ∈ Y, a ≤ y ∧ y < b)
    (hXY : Closed ↑(X ∪ Y)) :
    ∃ Yt : Finset Ordinal.{0}, (∀ y ∈ Yt, a' < y ∧ y < a) ∧ (∀ x ∈ X, ∀ y ∈ Yt, x < y) ∧
      Closed ↑(X ∪ Yt) ∧ ∃ h, Cov R2C R2C ↑(X ∪ Y) ↑(X ∪ Yt) h ∧ (∀ x ∈ X, h x = x) ∧
        ∀ y ∈ Y, h y ∈ Yt ∧ Q y (h y) := by
  classical
  obtain ⟨Xp, hsub, hXpC, hXpb⟩ := exists_closed (insert a' X)
  have ha'Xp : a' ∈ Xp := hsub (by simp)
  have hXXp : ∀ x ∈ X, x ∈ Xp := fun x hx => hsub (by simp [hx])
  have hXp_lt : ∀ x ∈ Xp, x < a := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := hXpb x hx
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact lt_of_le_of_lt hxs ha'
    · exact lt_of_le_of_lt hxs (hX s hs)
  have hXYsub : (↑(X ∪ Y) : Set Ordinal.{0}) ⊆ ↑(Xp ∪ Y) := by
    intro z hz
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hz ⊢
    rcases hz with hz | hz
    · exact Or.inl (hXXp z hz)
    · exact Or.inr hz
  have hclosed : Closed ↑(Xp ∪ Y) := by
    intro z hz hdz
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hz) with hz | hz
    · exact (hXpC z hz hdz).mono (by simp)
    · exact (hXY z (by simp [hz]) hdz).mono hXYsub
  obtain ⟨Yt0, hYt0a, hXpYt0, hcl0, h, hcov, hQ⟩ := H Xp Y hXp_lt hY hclosed
  have hfix : ∀ x ∈ (↑Xp : Set Ordinal.{0}), h x = x := by
    refine fix_initial hcov.1.1 hcov.1.2.1 (by simp) (by simp) ?_ ?_
    · intro x hx hxn s hs
      rcases Finset.mem_union.1 (Finset.mem_coe.1 hx) with hx | hx
      · exact absurd hx hxn
      · exact lt_of_lt_of_le (hXp_lt s hs) (hY x hx).1
    · intro x hx hxn s hs
      rcases Finset.mem_union.1 (Finset.mem_coe.1 hx) with hx | hx
      · exact absurd hx hxn
      · exact hXpYt0 s hs x hx
  have hYmap : ∀ y ∈ Y, h y ∈ Yt0 := by
    intro y hy
    have hmem : h y ∈ (↑(Xp ∪ Yt0) : Set Ordinal.{0}) := hcov.1.1.mapsTo (by simp [hy])
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hmem) with hm | hm
    · exfalso
      have h22 : h (h y) = h y := hfix _ hm
      have := hcov.1.1.injOn (by simp [hm]) (by simp [hy]) h22
      exact absurd (this ▸ hXp_lt _ hm) (not_lt.2 (hY y hy).1)
    · exact hm
  set Yt := Y.image h with hYtdef
  have himg : (↑(X ∪ Yt) : Set Ordinal.{0}) = h '' ↑(X ∪ Y) := by
    rw [← Finset.coe_image, Finset.image_union, hYtdef]
    congr 2
    conv_lhs => rw [← Finset.image_id (s := X)]
    exact (Finset.image_congr (fun x hx => (hfix x (hXXp x hx)).symm))
  refine ⟨Yt, ?_, ?_, ?_, h, ?_, fun x hx => hfix x (hXXp x hx),
    fun y hy => ⟨Finset.mem_image_of_mem h hy, hQ y hy⟩⟩
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    exact ⟨hXpYt0 a' ha'Xp _ (hYmap y hy), hYt0a _ (hYmap y hy)⟩
  · intro x hx z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    exact hXpYt0 x (hXXp x hx) _ (hYmap y hy)
  · rw [himg]; exact closed_image hcov.1 hcl0 hXYsub hXY
  · rw [himg]; exact hcov.restrict hXYsub

/-- **[C09] Lemma 5.5 (1)**: if `α ≤₁ β`, the copies `Ỹ` of `Y ⊆ [α, β)` over `X ⊆ α` can be taken
cofinally below `α`, by a covering that fixes `X`. -/
theorem le1_cof {a b a' : Ordinal.{0}} (h : le1 a b) (ha' : a' < a) (X Y : Finset Ordinal.{0})
    (hX : ∀ x ∈ X, x < a) (hY : ∀ y ∈ Y, a ≤ y ∧ y < b) (hXY : Closed ↑(X ∪ Y)) :
    ∃ Yt : Finset Ordinal.{0}, (∀ y ∈ Yt, a' < y ∧ y < a) ∧ (∀ x ∈ X, ∀ y ∈ Yt, x < y) ∧
      Closed ↑(X ∪ Yt) ∧ ∃ f, Cov R2C R2C ↑(X ∪ Y) ↑(X ∪ Yt) f ∧ (∀ x ∈ X, f x = x) ∧
        ∀ y ∈ Y, f y ∈ Yt := by
  obtain ⟨_, H⟩ := le1_iff.1 h
  obtain ⟨Yt, h1, h2, h3, f, hf, hfix, hY'⟩ := cof_core ha' (fun _ _ => True)
    (fun X Y hX hY hXY => by
      obtain ⟨Yt, h1, h2, h3, f, hf⟩ := H X Y hX hY hXY
      exact ⟨Yt, h1, h2, h3, f, hf, fun _ _ => trivial⟩) X Y hX hY hXY
  exact ⟨Yt, h1, h2, h3, f, hf, hfix, fun y hy => (hY' y hy).1⟩

/-- **[C09] Lemma 5.5 (4)**: `≤₂` is transitive. -/
theorem le2_trans {a b c : Ordinal.{0}} (hab : le2 a b) (hbc : le2 b c) : le2 a c := by
  classical
  obtain ⟨hab', H1ab, H2ab⟩ := le2_iff.1 hab
  obtain ⟨hbc', H1bc, H2bc⟩ := le2_iff.1 hbc
  rcases eq_or_lt_of_le hab' with rfl | hlt
  · exact hbc
  refine le2_iff.2 ⟨hab'.trans hbc', fun X Y hX hY hXY => ?_, fun X hX Z P hZ hC => ?_⟩
  · set Y1 := Y.filter (· < b) with hY1
    set Y2 := Y.filter (fun y => ¬ y < b) with hY2
    have hYeq : Y1 ∪ Y2 = Y := Finset.filter_union_filter_not_eq _ _
    have hX1 : ∀ x ∈ X ∪ Y1, x < b := by
      intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · exact (hX x hx).trans hlt
      · exact (Finset.mem_filter.1 hx).2
    have hY2b : ∀ y ∈ Y2, b ≤ y ∧ y < c := by
      intro y hy
      obtain ⟨hyY, hyb⟩ := Finset.mem_filter.1 hy
      exact ⟨not_lt.1 hyb, (hY y hyY).2⟩
    have e1 : (X ∪ Y1) ∪ Y2 = X ∪ Y := by rw [Finset.union_assoc, hYeq]
    have hcl : Closed ↑((X ∪ Y1) ∪ Y2) := by rw [e1]; exact hXY
    obtain ⟨Yt2, h2a, h2b, h2c, h2, hcov2, hfix2, hmap2⟩ :=
      cof_core hlt (fun y z => le1 y c → le1 z b) H1bc (X ∪ Y1) Y2 hX1 hY2b hcl
    set Yp := Y1 ∪ Yt2 with hYpdef
    have hYp : ∀ y ∈ Yp, a ≤ y ∧ y < b := by
      intro y hy
      rcases Finset.mem_union.1 hy with hy | hy
      · obtain ⟨hyY, hyb⟩ := Finset.mem_filter.1 hy
        exact ⟨(hY y hyY).1, hyb⟩
      · exact ⟨(h2a y hy).1.le, (h2a y hy).2⟩
    have e2 : (X ∪ Y1) ∪ Yt2 = X ∪ Yp := by rw [Finset.union_assoc]
    have hclp : Closed ↑(X ∪ Yp) := by rw [← e2]; exact h2c
    rw [e1, e2] at hcov2
    obtain ⟨Yt, h1a, h1b, h1c, h1, hcov1, hd1⟩ := H1ab X Yp hX hYp hclp
    refine ⟨Yt, h1a, h1b, h1c, h1 ∘ h2, hcov2.comp hcov1, ?_⟩
    intro y hy hyc
    by_cases hyb : y < b
    · have hyY1 : y ∈ Y1 := Finset.mem_filter.2 ⟨hy, hyb⟩
      have hfy : h2 y = y := hfix2 y (Finset.mem_union_right _ hyY1)
      show le1 (h1 (h2 y)) a
      rw [hfy]
      have hyb1 : le1 y b := le1_of_le_of_le1 hyb.le hbc' hyc
      exact hd1 y (Finset.mem_union_left _ hyY1) hyb1
    · have hyY2 : y ∈ Y2 := Finset.mem_filter.2 ⟨hy, hyb⟩
      obtain ⟨hm, hq⟩ := hmap2 y hyY2
      exact hd1 (h2 y) (Finset.mem_union_right _ hm) (hq hyc)
  · exact H2bc X (fun x hx => (hX x hx).trans hlt) Z P hZ (H2ab X hX Z P hZ hC)

/-- **[C09] Lemma 5.5 (6)**: `≤₂` respects `≤₁`: `α ≤ β ≤ γ`, `α ≤₂ γ`, `β ≤₁ γ` give
`α ≤₂ β`. -/
theorem le2_of_le1 {a b c : Ordinal.{0}} (hab : a ≤ b) (hbc : b ≤ c) (h : le2 a c)
    (h1 : le1 b c) : le2 a b := by
  obtain ⟨_, H1, H2⟩ := le2_iff.1 h
  refine le2_iff.2 ⟨hab, fun X Y hX hY hXY => ?_, fun X hX Z P hZ hC => ?_⟩
  · obtain ⟨Yt, ha, hb, hc, f, hf, hd⟩ := H1 X Y hX
      (fun y hy => ⟨(hY y hy).1, lt_of_lt_of_le (hY y hy).2 hbc⟩) hXY
    exact ⟨Yt, ha, hb, hc, f, hf, fun y hy hyb => hd y hy (le1_trans hyb h1)⟩
  · have hCc := H2 X hX Z P hZ hC
    rcases eq_or_lt_of_le hbc with rfl | hbc'
    · exact hCc
    intro b' hb'
    obtain ⟨Y, hY, hXY, g, hg⟩ := hCc b hbc'
    have hXb : ∀ x ∈ X, x < b := fun x hx => lt_of_lt_of_le (hX x hx) hab
    obtain ⟨Yt, h1', -, h3', f, hf, -, -⟩ := le1_cof h1 hb' X Y hXb
      (fun y hy => ⟨(hY y hy).1.le, (hY y hy).2⟩) hXY
    exact ⟨Yt, h1', h3', f ∘ g, hg.comp hf⟩

end Googology.Trans.PoR.InaccPsi.R2
