import Googology.Trans.PoR.InaccPsi.R2.R1Gap
import Googology.Trans.PoR.InaccPsi.R2.CCF
import Googology.Trans.PoR.InaccPsi.R2.FragBase

/-!
# INC1: `≤₁` of `R₂^C` is contained in `≤₁` of `R₁⁺` (countable right ends)

The project's Theorem INC1 for `R₂^C`, with the proof of its paper version (INC1-LOC-C with Lemma
CLEAN-C and CC-F, Lemma LEFT-AT, Lemma FANCOF, PI2-UP, NOBAD):

* `left_at` (**Lemma LEFT-AT**): if `α <₂ β` in `R₂^C`, `α` is countable and INC1 holds at the right
  end `α`, then `α` is a `υ`-point.  (A `<₁`-predecessor set inside a gap is finite, [W07b] Cor 5.9,
  but `α <₂ β` makes the `R₂^C`-predecessors of `α` cofinal, [C09] Def 5.3 clause (d).)
* `fancof` (**Lemma FANCOF**): a point with two `<₂`-successors `x < b` has `<₂`-pairs cofinally below.
* `pairs_up` (**PI2-UP**): `<₂`-pairs cofinal below `v` and `v ≤₂ b` give `<₂`-pairs cofinal below
  `b` ([C09] Def 5.3, clause 2).
* `ups_of_pairs`: below the least failure of INC1, a point with `<₂`-pairs cofinally below it is a
  `υ`-point (LEFT-AT at every left end; `υ`-points form a closed class).
* `Block.clean` (**Lemma CLEAN-C**, for any block `[x, g0]` with no `<₂`-relation into it), `LeastFail.caseA_false` (Case A, against [W07b] Claim 5.6),
  `LeastFail.caseB_false` (Case B, a bad right end; NOBAD).
* `inc1` (**Theorem INC1**): `a ≤₁ b` in `R₂^C` and `b < Ω₁` give `a ≤₁ b` in `R₁⁺`.

Countability: the cited facts on `Tᵗ` are for `τ < Ω₁ = ω₁`, so INC1 is proved for countable right
ends; every application in the project is countable.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-- INC1 at the right end `g`: every `y ≤₁ g` in `R₂^C` has `y ≤₁ g` in `R₁⁺`. -/
def Inc1At (g : Ordinal.{0}) : Prop := ∀ y, le1 y g → le1R y g

/-- A proper `≤₁`-left end of `R₂^C` is `> 1` ([C09] Lemma 5.5 (7)(a)). -/
theorem one_lt_of_lt1 {a b : Ordinal.{0}} (h : le1 a b) (hab : a < b) : 1 < a := by
  obtain ⟨p, -, hpa, hp⟩ := exists_indec_of_lt1 h hab (indec_of_lt1 h hab).pos
  exact lt_of_le_of_lt (one_le_iff_pos.2 hp.pos) hpa

theorem closed_singleton_of_indec {a : Ordinal.{0}} (hI : Indec a) :
    Closed ↑((∅ : Finset Ordinal.{0}) ∪ {a}) :=
  closed_of_indec (fun x hx => by simp at hx; rw [hx]; exact hI)

/-- **Lemma LEFT-AT** (`R₂^C`). -/
theorem left_at {α β : Ordinal.{0}} (h : le2 α β) (hαβ : α < β) (hα1 : α < Om1)
    (hinc : Inc1At α) : UpsPt α := by
  classical
  have h1 := le2_le1 h
  have hI := indec_of_lt1 h1 hαβ
  by_contra hnu
  obtain ⟨τ, m, hg⟩ := exists_gap (one_lt_of_lt1 h1 hαβ) hα1 hnu
  obtain ⟨F, hFα, hF⟩ := preds_finite hg hα1 hI
  have hsupF : F.sup id < α := by
    rw [Finset.sup_lt_iff hI.pos]; exact hFα
  have hcα : max τ (F.sup id) < α := max_lt hg.base_lt hsupF
  obtain ⟨_, H1, _⟩ := le2_iff.1 h
  obtain ⟨Yt, hYt, -, -, f, -, -, hY⟩ := cof_core hcα (fun y z => le1 y β → le1 z α)
    (fun X Y hX hY hXY => H1 X Y hX hY hXY) ∅ {α} (by simp) (by simp [hαβ])
    (closed_singleton_of_indec hI)
  obtain ⟨hfY, hq⟩ := hY α (by simp)
  have hyR : le1R (f α) α := hinc _ (hq h1)
  have hmem := hF (f α) (lt_of_le_of_lt (le_max_left _ _) (hYt _ hfY).1) (hYt _ hfY).2 hyR
  have hle : f α ≤ max τ (F.sup id) :=
    le_trans (Finset.le_sup (f := id) hmem) (le_max_right _ _)
  exact absurd (hYt _ hfY).1 (not_lt.2 hle)

/-- **Lemma FANCOF** (`R₂^C`): if `v <₂ x < b` and `v <₂ b`, then `<₂`-pairs are cofinal below `v`. -/
theorem fancof {v x b : Ordinal.{0}} (hvx : le2 v x) (hvx' : v < x) (hxb : x < b)
    (hvb : le2 v b) : ∀ z < v, ∃ p q, z < p ∧ p < q ∧ q < v ∧ le2 p q := by
  classical
  intro z hz
  have hvI := indec_of_lt1 (le2_le1 hvx) hvx'
  have hxI := (indec_of_lt2_right hvx hvx').1
  obtain ⟨C, -, hC, hCb⟩ := exists_closed {z}
  have hCv : ∀ c ∈ C, c < v := fun c hc => by
    obtain ⟨s, hs, hcs⟩ := hCb c hc
    rw [Finset.mem_singleton.1 hs] at hcs
    exact lt_of_le_of_lt hcs hz
  have hcl : Closed ↑(C ∪ {v, x}) := by
    rw [Finset.coe_union]
    refine hC.union (closed_of_indec fun w hw => ?_)
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact hvI
    · exact hxI
  have hY : ∀ y ∈ ({v, x} : Finset Ordinal.{0}), v ≤ y ∧ y < b := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact ⟨le_rfl, lt_trans hvx' hxb⟩
    · exact ⟨hvx'.le, hxb⟩
  obtain ⟨Yt, hYt, -, -, f, hf, -, hYm⟩ := le1_cof (le2_le1 hvb) hz C {v, x} hCv hY hcl
  have hfv := hYm v (by simp)
  have hfx := hYm x (by simp)
  exact ⟨f v, f x, (hYt _ hfv).1, hf.1.2.1 (by simp) (by simp) hvx', (hYt _ hfx).2,
    hf.2.2 v (by simp) x (by simp) hvx⟩

/-- **PI2-UP** (`R₂^C`): `<₂`-pairs cofinal below `v` and `v <₂ b` give `<₂`-pairs cofinal below `b`
([C09] Def 5.3, clause 2, for the pattern of one pair). -/
theorem pairs_up {v b : Ordinal.{0}} (hvb : le2 v b) (hvb' : v < b)
    (hcof : ∀ z < v, ∃ p q, z < p ∧ p < q ∧ q < v ∧ le2 p q) :
    ∀ z < b, ∃ p q, z < p ∧ p < q ∧ q < b ∧ le2 p q := by
  classical
  have hvI := indec_of_lt1 (le2_le1 hvb) hvb'
  obtain ⟨p0, q0, -, hpq0, -, h20⟩ := hcof 0 hvI.pos
  have hp0I := indec_of_lt1 (le2_le1 h20) hpq0
  have hq0I := (indec_of_lt2_right h20 hpq0).1
  have hmemZ : ∀ w, w ∈ (↑({p0, q0} : Finset Ordinal.{0}) : Set Ordinal.{0}) ↔ w = p0 ∨ w = q0 :=
    fun w => by simp
  have hZ : Closed ↑({p0, q0} : Finset Ordinal.{0}) := closed_of_indec fun w hw => by
    rcases (hmemZ w).1 hw with rfl | rfl
    · exact hp0I
    · exact hq0I
  -- a covering of the pattern `{p0 <₂ q0}` onto any pair `p <₂ q`
  have hpair : ∀ p q, p < q → le2 p q →
      ∃ g, Cov R2C R2C ↑({p0, q0} : Finset Ordinal.{0}) ↑({p, q} : Finset Ordinal.{0}) g := by
    intro p q hpq h2
    have hpI := indec_of_lt1 (le2_le1 h2) hpq
    have hqI := (indec_of_lt2_right h2 hpq).1
    set f : Ordinal.{0} → Ordinal.{0} := fun t => if t = p0 then p else q with hfdef
    have hfp : ext f p0 = p := by rw [ext_indec hp0I]; simp [f]
    have hfq : ext f q0 = q := by rw [ext_indec hq0I]; simp [f, hpq0.ne']
    have hf : StrictMonoOn f (IndecIn ↑({p0, q0} : Finset Ordinal.{0})) := by
      intro a ha c hc hac
      rcases (hmemZ a).1 ha.1 with rfl | rfl <;> rcases (hmemZ c).1 hc.1 with rfl | rfl
      · exact absurd hac (lt_irrefl _)
      · simp [f, hpq0.ne']; exact hpq
      · exact absurd (hac.trans hpq0) (lt_irrefl _)
      · exact absurd hac (lt_irrefl _)
    have hfI : ∀ a ∈ IndecIn (↑({p0, q0} : Finset Ordinal.{0}) : Set Ordinal.{0}), Indec (f a) :=
      fun a _ => by
        simp only [f]
        split_ifs
        · exact hpI
        · exact hqI
    have himg : ext f '' ↑({p0, q0} : Finset Ordinal.{0}) = ↑({p, q} : Finset Ordinal.{0}) := by
      ext w
      simp only [Set.mem_image, Finset.coe_insert, Finset.coe_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨t, ht, rfl⟩
        rcases ht with rfl | rfl
        · exact Or.inl hfp
        · exact Or.inr hfq
      · rintro (rfl | rfl)
        · exact ⟨p0, Or.inl rfl, hfp⟩
        · exact ⟨q0, Or.inr rfl, hfq⟩
    refine ⟨ext f, ?_⟩
    rw [← himg]
    refine ⟨ext_arithIso hZ hf hfI, ?_, ?_⟩
    · intro a ha c hc hac
      change le1 a c at hac
      change le1 (ext f a) (ext f c)
      rcases (hmemZ a).1 ha with rfl | rfl <;> rcases (hmemZ c).1 hc with rfl | rfl
      · exact le1_refl _
      · rw [hfp, hfq]; exact le2_le1 h2
      · exact absurd (le1_le hac) (not_le.2 hpq0)
      · exact le1_refl _
    · intro a ha c hc hac
      change le2 a c at hac
      change le2 (ext f a) (ext f c)
      rcases (hmemZ a).1 ha with rfl | rfl <;> rcases (hmemZ c).1 hc with rfl | rfl
      · exact le2_refl _
      · rw [hfp, hfq]; exact h2
      · exact absurd (le2_le hac) (not_le.2 hpq0)
      · exact le2_refl _
  obtain ⟨_, -, H2⟩ := le2_iff.1 hvb
  have hcofv : CofCov R2C ∅ {p0, q0} R2C v := by
    intro c hc
    obtain ⟨p, q, hcp, hpq, hqv, h2⟩ := hcof c hc
    obtain ⟨g, hg⟩ := hpair p q hpq h2
    have hpI := indec_of_lt1 (le2_le1 h2) hpq
    have hqI := (indec_of_lt2_right h2 hpq).1
    refine ⟨{p, q}, ?_, ?_, g, by simpa using hg⟩
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact ⟨hcp, lt_trans hpq hqv⟩
      · exact ⟨lt_trans hcp hpq, hqv⟩
    · rw [Finset.empty_union]
      exact closed_of_indec fun w hw => by
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl
        · exact hpI
        · exact hqI
  have hcofb := H2 ∅ (by simp) {p0, q0} R2C hZ hcofv
  intro z hz
  obtain ⟨Y, hY, -, g, hg⟩ := hcofb z hz
  have hgp := hg.1.1.mapsTo ((hmemZ p0).2 (Or.inl rfl))
  have hgq := hg.1.1.mapsTo ((hmemZ q0).2 (Or.inr rfl))
  simp only [Finset.empty_union, Finset.mem_coe] at hgp hgq
  exact ⟨g p0, g q0, (hY _ hgp).1, hg.1.2.1 ((hmemZ p0).2 (Or.inl rfl)) ((hmemZ q0).2 (Or.inr rfl))
    hpq0, (hY _ hgq).2, hg.2.2 p0 ((hmemZ p0).2 (Or.inl rfl)) q0 ((hmemZ q0).2 (Or.inr rfl)) h20⟩

/-- Below a point `g0` where INC1 holds at every smaller right end, a point with `<₂`-pairs
cofinally below it is a `υ`-point (LEFT-AT at the left ends; the `υ`-points form a closed class). -/
theorem ups_of_pairs {b g0 : Ordinal.{0}} (hb : 0 < b) (hbg : b ≤ g0) (hg0 : g0 < Om1)
    (hinc : ∀ g < g0, Inc1At g) (hcof : ∀ z < b, ∃ p q, z < p ∧ p < q ∧ q < b ∧ le2 p q) :
    UpsPt b := by
  refine upsPt_of_cofinal hb fun c hc => ?_
  obtain ⟨p, q, hcp, hpq, hqb, h2⟩ := hcof c hc
  have hpb : p < b := hpq.trans hqb
  exact ⟨p, hcp, hpb, left_at h2 hpq (lt_trans (lt_of_lt_of_le hpb hbg) hg0)
    (hinc p (lt_of_lt_of_le hpb hbg))⟩

/-- A block `[x, g0]`: `x` indecomposable in the gap `(τ, m)`, `x ≤₁ g0` in `R₂^C`, `g0 ≤ m`
countable, and INC1 at every right end below `g0`. -/
structure Block (g0 x τ m : Ordinal.{0}) : Prop where
  g0_lt : g0 < Om1
  x_lt : x < g0
  le1x : le1 x g0
  inc : ∀ g < g0, Inc1At g
  xI : Indec x
  gap : Gap τ m x
  g0_le_m : g0 ≤ m

/-- The setting at the least right end `g0` where INC1 fails, with a failing left point `x` in the
gap `(τ, m)`. -/
structure LeastFail (g0 x τ m : Ordinal.{0}) : Prop extends Block g0 x τ m where
  notR : ¬ le1R x g0

namespace Block

variable {g0 x τ m : Ordinal.{0}}

theorem le1_x (hF : Block g0 x τ m) {g : Ordinal.{0}} (hxg : x ≤ g) (hg : g ≤ g0) : le1 x g :=
  le1_of_le_of_le1 hxg hg hF.le1x

theorem not_ups (hF : Block g0 x τ m) {b : Ordinal.{0}} (hxb : x ≤ b) (hb : b < g0) :
    ¬ UpsPt b :=
  hF.gap.noUps b (lt_of_lt_of_le hF.gap.base_lt hxb) (lt_of_lt_of_le hb hF.g0_le_m)

/-- No `<₂`-left end in `[x, g0)` (LEFT-AT: it would be a `υ`-point inside the gap). -/
theorem no_left (hF : Block g0 x τ m) {a b : Ordinal.{0}} (hxa : x ≤ a) (hag : a < g0)
    (hab : a < b) : ¬ le2 a b := fun h =>
  hF.not_ups hxa hag (left_at h hab (lt_trans hag hF.g0_lt) (hF.inc a hag))

/-- **Lemma CLEAN-C** (in Case A): for `x < p < q ≤ g0`, `p ≤₁ q` in `R₁⁺` gives `p ≤₁ q` in
`R₂^C`. -/
theorem clean (hF : Block g0 x τ m) (hA : ∀ v < x, ∀ b, x < b → b < g0 → ¬ le2 v b) :
    ∀ q, q ≤ g0 → ∀ p, x < p → p < q → le1R p q → le1 p q := by
  classical
  intro q
  induction q using WellFoundedLT.induction with
  | ind q IH =>
  intro hqg p hxp hpq hR
  refine le1_iff.2 ⟨hpq.le, fun X Y hX hY hXY => ?_⟩
  set X2 : Finset Ordinal.{0} := X ∪ {0, x} with hX2def
  have hx0 : (0 : Ordinal.{0}) < p := lt_of_le_of_lt zero_le hxp
  have hX2 : ∀ w ∈ X2, w < p := by
    intro w hw
    simp only [X2, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with hw | rfl | rfl
    · exact hX w hw
    · exact hx0
    · exact hxp
  have hxX2 : x ∈ X2 := by simp [X2]
  have hX2Y : Closed ↑(X2 ∪ Y) := by
    have he : (↑(X2 ∪ Y) : Set Ordinal.{0}) = ↑(X ∪ Y) ∪ ({0, x} : Set Ordinal.{0}) := by
      ext w; simp only [X2, Finset.coe_union, Finset.coe_insert, Finset.coe_singleton,
        Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe]; tauto
    rw [he]
    refine hXY.union fun w hw hd => ?_
    rcases hw with rfl | hw
    · exact Or.inl rfl
    · rw [Set.mem_singleton_iff.1 hw] at hd ⊢; exact absurd hd hF.xI
  obtain ⟨ψ, hψ, hψc, hfix, hYψ, hψR⟩ := ccf hR X2 Y hX2 hY (by simp [X2]) hX2Y
  have hX2lt : ∀ a ∈ X2 ∪ Y, ∀ b ∈ X2, a < b → a ∈ X2 := by
    intro a ha b hb hab
    rcases Finset.mem_union.1 ha with h | h
    · exact h
    · exact absurd (lt_trans hab (hX2 b hb)) (not_lt.2 (hY a h).1)
  have hcov : Cov R2C R2C ↑(X2 ∪ Y) (ψ '' ↑(X2 ∪ Y)) ψ := by
    refine ⟨hψ, ?_, ?_⟩
    · intro a ha b hb hab
      change le1 a b at hab
      change le1 (ψ a) (ψ b)
      rcases eq_or_lt_of_le (le1_le hab) with rfl | hab'
      · exact le1_refl _
      rcases Finset.mem_union.1 hb with hbX | hbY
      · rw [hfix a (hX2lt a ha b hbX hab'), hfix b hbX]; exact hab
      · obtain ⟨hψb1, hψbp⟩ := hYψ b hbY
        have hxψb : x < ψ b := hψb1 x hxX2
        have hψbq : ψ b < q := lt_trans hψbp hpq
        have hψbg : ψ b ≤ g0 := hψbq.le.trans hqg
        have hbg : b < g0 := lt_of_lt_of_le (hY b hbY).2 hqg
        rcases Finset.mem_union.1 ha with haX | haY
        · rw [hfix a haX]
          rcases lt_trichotomy a x with hax | hax | hxa
          · have hax1 : le1 a x := le1_of_le_of_le1 hax.le (hxp.le.trans (hY b hbY).1) hab
            exact le1_trans hax1 (hF.le1_x hxψb.le hψbg)
          · rw [hax]; exact hF.le1_x hxψb.le hψbg
          · have hRab : le1R a b := hF.inc b hbg a hab
            have hRψ := hψR a (Finset.mem_union_left _ haX) b (Finset.mem_union_right _ hbY) hRab
            rw [hfix a haX] at hRψ
            exact IH (ψ b) hψbq hψbg a hxa (hψb1 a haX) hRψ
        · have hRab : le1R a b := hF.inc b hbg a hab
          have hRψ := hψR a ha b hb hRab
          have hxψa : x < ψ a := (hYψ a haY).1 x hxX2
          have hψab : ψ a < ψ b := hψ.2.1 ha hb hab'
          exact IH (ψ b) hψbq hψbg (ψ a) hxψa hψab hRψ
    · intro a ha b hb hab
      change le2 a b at hab
      change le2 (ψ a) (ψ b)
      rcases eq_or_lt_of_le (le2_le hab) with rfl | hab'
      · exact le2_refl _
      rcases Finset.mem_union.1 hb with hbX | hbY
      · rw [hfix a (hX2lt a ha b hbX hab'), hfix b hbX]; exact hab
      · exfalso
        have hbg : b < g0 := lt_of_lt_of_le (hY b hbY).2 hqg
        have hxb : x < b := lt_of_lt_of_le hxp (hY b hbY).1
        rcases lt_or_ge a x with hax | hxa
        · exact hA a hax b hxb hbg hab
        · exact hF.no_left hxa (lt_trans hab' hbg) hab' hab
  have hsub : (↑(X ∪ Y) : Set Ordinal.{0}) ⊆ ↑(X2 ∪ Y) := by
    intro w hw
    simp only [X2, Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.coe_insert,
      Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
    tauto
  have hfixX : ∀ w ∈ X, ψ w = w := fun w hw => hfix w (Finset.mem_union_left _ hw)
  have himg : ψ '' ↑(X ∪ Y) = ↑(X ∪ Y.image ψ) := by
    ext w
    simp only [Set.mem_image, Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro ⟨t, ht, rfl⟩
      rcases ht with ht | ht
      · left; rw [hfixX t ht]; exact ht
      · right; exact ⟨t, ht, rfl⟩
    · rintro (hw | ⟨t, ht, rfl⟩)
      · exact ⟨w, Or.inl hw, hfixX w hw⟩
      · exact ⟨t, Or.inr ht, rfl⟩
  refine ⟨Y.image ψ, ?_, ?_, ?_, ψ, ?_⟩
  · intro y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    exact (hYψ t ht).2
  · intro w hw y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    exact (hYψ t ht).1 w (Finset.mem_union_left _ hw)
  · rw [← himg]; exact closed_image hψ hψc hsub hXY
  · rw [← himg]; exact hcov.restrict hsub

end Block

namespace LeastFail

variable {g0 x τ m : Ordinal.{0}}

/-- **Case B**: a `<₂`-relation `v <₂ b` with `v < x < b < g0` is impossible (NOBAD). -/
theorem caseB_false (hF : LeastFail g0 x τ m) {v b : Ordinal.{0}} (hvx : v < x) (hxb : x < b)
    (hbg : b < g0) (h2 : le2 v b) : False := by
  have hxb1 : le1 x b := hF.toBlock.le1_x hxb.le hbg.le
  have hvx2 : le2 v x := le2_of_le1 hvx.le hxb.le h2 hxb1
  have hcofb := pairs_up h2 (lt_trans hvx hxb) (fancof hvx2 hvx hxb h2)
  have hbU := ups_of_pairs (lt_of_le_of_lt zero_le (lt_trans hvx hxb)) hbg.le hF.g0_lt hF.inc hcofb
  exact hF.toBlock.not_ups hxb.le hbg hbU

/-- **Case A** is impossible: the covering given by `x ≤₁ g0` in `R₂^C` is an `R₁⁺`-covering of the
sets of [W07b] Claim 5.6. -/
theorem caseA_false (hF : LeastFail g0 x τ m)
    (hA : ∀ v < x, ∀ b, x < b → b < g0 → ¬ le2 v b) : False := by
  classical
  have hx1 : x < Om1 := lt_trans hF.x_lt hF.g0_lt
  -- Step 1: the base `σ` of [W07b] Claim 5.6
  obtain ⟨σ, hσE, hσ1, hσT, hσx, hσmin⟩ : ∃ σ, (σ = 1 ∨ InE σ) ∧ σ < Om1 ∧ x ∈ Tset σ ∧
      σ < x ∧ ∀ d, le1R d x → d < x → d ≤ σ := by
    rcases greatest_pred hF.gap hx1 hF.xI with hmin | ⟨σ, hτσ, hσx, hσR, hσmax⟩
    · exact ⟨τ, hF.gap.base_E, hF.gap.base_Om1, hF.gap.mem_T hF.gap.lt_next hx1,
        hF.gap.base_lt, hmin⟩
    · have hσ0 : 0 < σ := lt_of_le_of_lt zero_le hτσ
      have hσσ : σ * 2 ≤ x := by rw [mul_two_eq]; exact (hF.xI.add_lt hσx hσx).le
      have hσE : InE σ := (le1R_two_iff hσ0).1
        (le1R_of_le (by rw [mul_two_eq]; exact le_self_add) hσσ hσR)
      have hσ1 : σ < Om1 := lt_trans hσx hx1
      obtain ⟨m', hσm', hm', hmin', hT'⟩ := T_inter_Om1 hσE hσ1
      have hxm' : x < m' := by
        by_contra hle
        exact hF.gap.noUps m' (lt_trans hτσ hσm')
          (lt_of_le_of_lt (not_lt.1 hle) hF.gap.lt_next) ⟨lt_of_le_of_lt zero_le hσm', hm'⟩
      exact ⟨σ, Or.inr hσE, hσ1, (hT' x hx1).2 hxm', hσx, hσmax⟩
  obtain ⟨l, hl, X, Z, hX, hZ, -, -, hno⟩ := claim56 hσE hσ1 hσT hσx hx1 hF.xI hσmin
  have hlg : l < g0 := by
    by_contra hle
    exact hF.notR (le1R_of_le hF.x_lt.le (not_lt.1 hle) hl.1)
  obtain ⟨W, hsub, hW, hWb⟩ := exists_closed (X ∪ Z)
  set Xp := W.filter (· < x) with hXpdef
  set Zp := W.filter (fun w => ¬ w < x) with hZpdef
  have hWeq : Xp ∪ Zp = W := Finset.filter_union_filter_not_eq _ _
  have hXp : ∀ w ∈ Xp, w < x := fun w hw => (Finset.mem_filter.1 hw).2
  have hZp : ∀ w ∈ Zp, x ≤ w ∧ w < g0 := by
    intro w hw
    obtain ⟨hwW, hwx⟩ := Finset.mem_filter.1 hw
    refine ⟨not_lt.1 hwx, ?_⟩
    obtain ⟨s, hs, hws⟩ := hWb w hwW
    rcases Finset.mem_union.1 hs with hsX | hsZ
    · exact absurd (lt_of_le_of_lt hws (hX s hsX)) hwx
    · exact lt_of_le_of_lt (hws.trans (hZ s hsZ).2) hlg
  have hcl : Closed ↑(Xp ∪ Zp) := by rw [hWeq]; exact hW
  obtain ⟨Zt, hZt, hXZt, -, f, hf, hfix, hZm⟩ :=
    le1_cof hF.le1x hF.xI.pos Xp Zp hXp hZp hcl
  have hXsub : ∀ w ∈ X, w ∈ Xp := fun w hw =>
    Finset.mem_filter.2 ⟨hsub (Finset.mem_union_left _ hw), hX w hw⟩
  have hZsub : ∀ w ∈ Z, w ∈ Zp := fun w hw =>
    Finset.mem_filter.2 ⟨hsub (Finset.mem_union_right _ hw), not_lt.2 (hZ w hw).1⟩
  have hsub2 : (↑(X ∪ Z) : Set Ordinal.{0}) ⊆ ↑(Xp ∪ Zp) := by
    intro w hw
    rcases Finset.mem_union.1 hw with h | h
    · exact Finset.mem_union_left _ (hXsub w h)
    · exact Finset.mem_union_right _ (hZsub w h)
  apply hno
  refine ⟨f, ⟨hf.1.2.1.mono hsub2, fun a ha b hb c hc => hf.1.2.2 a (hsub2 ha) b (hsub2 hb) c
    (hsub2 hc), fun a ha b hb hab => ?_⟩, fun w hw => hfix w (hXsub w hw),
    fun w hw z hz => hXZt w (hXsub w hw) _ (hZm z (hZsub z hz)),
    fun z hz => (hZt _ (hZm z (hZsub z hz))).2⟩
  have ha' := hsub2 ha
  have hb' := hsub2 hb
  rcases eq_or_lt_of_le (le1R_le hab) with rfl | hab'
  · exact le1R_refl _
  rcases Finset.mem_union.1 hb' with hbX | hbZ
  · have haX : a ∈ Xp := by
      rcases Finset.mem_union.1 ha' with h | h
      · exact h
      · exact absurd (lt_trans hab' (hXp b hbX)) (not_lt.2 (hZp a h).1)
    rw [hfix a haX, hfix b hbX]; exact hab
  · have hfbZt := hZm b hbZ
    have hfbx : f b < x := (hZt _ hfbZt).2
    have hfbb : f b ≤ b := (lt_of_lt_of_le hfbx (hZp b hbZ).1).le
    rcases Finset.mem_union.1 ha' with haX | haZ
    · rw [hfix a haX]
      exact le1R_of_le (hXZt a haX _ hfbZt).le hfbb hab
    · have hab1 : le1 a b := by
        rcases eq_or_lt_of_le (hZp a haZ).1 with hax | hxa
        · rw [← hax]; exact hF.toBlock.le1_x (hZp b hbZ).1 (hZp b hbZ).2.le
        · exact hF.toBlock.clean hA b (hZp b hbZ).2.le a hxa hab' hab
      have hcov1 : le1 (f a) (f b) := hf.2.1 a ha' b hb' hab1
      exact hF.inc (f b) (lt_trans hfbx hF.x_lt) (f a) hcov1

end LeastFail

/-- **Theorem INC1** (`R₂^C`, countable right ends): `a ≤₁ b` in `R₂^C` gives `a ≤₁ b` in `R₁⁺`. -/
theorem inc1 {a b : Ordinal.{0}} (hb : b < Om1) (h : le1 a b) : le1R a b := by
  classical
  by_contra hfail
  set S := {g | g < Om1 ∧ ∃ y, le1 y g ∧ ¬ le1R y g} with hSdef
  have hne : S.Nonempty := ⟨b, hb, a, h, hfail⟩
  set g0 := sInf S with hg0def
  obtain ⟨hg0, x, hx, hxf⟩ : g0 ∈ S := csInf_mem hne
  have hinc : ∀ g < g0, Inc1At g := fun g hg y hy => by
    by_contra hn
    exact absurd (csInf_le' (show g ∈ S from ⟨lt_trans hg hg0, y, hy, hn⟩)) (not_le.2 hg)
  have hxg : x < g0 := lt_of_le_of_ne (le1_le hx) (fun e => hxf (e ▸ le1R_refl x))
  have hxI := indec_of_lt1 hx hxg
  have hnu : ¬ UpsPt x := fun hu => hxf (hu.2 g0 hxg.le)
  obtain ⟨τ, m, hgap⟩ := exists_gap (one_lt_of_lt1 hx hxg) (lt_trans hxg hg0) hnu
  have hr1 : ∀ g, x ≤ g → g < g0 → le1R x g := fun g hxg' hg =>
    hinc g hg x (le1_of_le_of_le1 hxg' hg.le hx)
  have hg0m : g0 ≤ m := by
    by_contra hlt
    exact hgap.not_le1R hgap.base_lt hgap.lt_next le_rfl (hr1 m hgap.lt_next.le (not_le.1 hlt))
  have hF : LeastFail g0 x τ m := ⟨⟨hg0, hxg, hx, hinc, hxI, hgap, hg0m⟩, hxf⟩
  by_cases hB : ∃ v < x, ∃ b', x < b' ∧ b' < g0 ∧ le2 v b'
  · obtain ⟨v, hvx, b', hxb, hbg, h2⟩ := hB
    exact hF.caseB_false hvx hxb hbg h2
  · exact hF.caseA_false fun v hv b' hxb hbg h2 => hB ⟨v, hv, b', hxb, hbg, h2⟩

/-- **Corollary LEFT** (`R₂^C`, countable): every countable `<₂`-left end is a `υ`-point. -/
theorem left {α β : Ordinal.{0}} (h : le2 α β) (hαβ : α < β) (hα1 : α < Om1) : UpsPt α :=
  left_at h hαβ hα1 fun _ hy => inc1 hα1 hy

/-- **Corollary NOBAD** (`R₂^C`, countable): if `v <₂ x < b`, `v <₂ b` (a fan), then `b` is a
`υ`-point. -/
theorem fan_right_ups {v x b : Ordinal.{0}} (hvx : le2 v x) (hvx' : v < x) (hxb : x < b)
    (hvb : le2 v b) (hb1 : b < Om1) : UpsPt b :=
  ups_of_pairs (lt_of_le_of_lt zero_le (lt_trans hvx' hxb)) le_rfl hb1
    (fun g hg _ hy => inc1 (lt_trans hg hb1) hy)
    (pairs_up hvb (lt_trans hvx' hxb) (fancof hvx hvx' hxb hvb))

end Googology.Trans.PoR.InaccPsi.R2
