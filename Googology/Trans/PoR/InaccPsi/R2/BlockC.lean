import Googology.Trans.PoR.InaccPsi.R2.Inc1
import Googology.Trans.PoR.InaccPsi.R2.Frag2

/-!
# First uses of INC1 with FRAG and FRAG2 in `R₂^C`

All for countable ordinals (the cited facts on `Tᵗ` are for `τ < Ω₁`):

* `le2_preds_cofinal`: a `<₂`-left end has cofinally many `≤₁`-predecessors ([C09] Def 5.3, clause
  1 (d)).
* `right_lim` (**RIGHT-LIM**): a countable `β > 0` whose `≤₁`-predecessors are cofinal in `β` is a
  `υ`-point.
* `left_limit` (**LEFT**, with the index): a countable `<₂`-left end is `υ_λ` with `λ` a limit.
* `re_u` (**RE-U**, the `υ`-point part): if `<₂`-pairs are cofinal below `α` and `α <₂ β`, `β`
  countable, then `β` is a `υ`-point.
* `le1_le_lh1`: the `R₂^C`-reach of a countable point is at most its `R₁⁺`-reach (INC1).
* `block_le1_iff` (**SK1 inside a block**): in a block `[x, g]` (`x ≤₁ g` in `R₂^C`, `x`
  indecomposable inside the gap `(τ, m)`, `g ≤ m`, countable) into which no `<₂`-relation from below
  `x` points, `p ≤₁ q` in `R₂^C` iff in `R₁⁺`, for `x < p < q ≤ g` (Lemma CLEAN-C with INC1).
* `le1_iff_le1R_below`, `upsilon_omega_le_left`, `le1_iff_le1R_upsilon_omega`: `≤₁` of `R₂^C` is
  `≤₁` of `R₁⁺` up to the least `<₂`-right end; every `<₂`-left end is `≥ υ_ω`; so `R₂^C` and `R₁⁺`
  have the same `≤₁` on `[0, υ_ω]`.
* `SkeletalC`, `skeletal_of_skeletalC`: the skeleton hypothesis of FRAG2 reduced by INC1 and LEFT to
  its two lower-bound halves (`R₁⁺ ⇒ R₂^C` for non-`υ` left ends, and the caps) and RIGHT for the
  `<₂`-right ends.
* `frag2_C`: Theorem FRAG2 with the reduced hypothesis; `frag_frag2_C`: a FRAG map (Theorem FRAG,
  `frag`) is an isomorphism of `R₂^C` on `F` iff it keeps the caps (C1) and the pairs (C2), given the
  reduced skeleton on `F ∪ Ψ[F]`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-- A `<₂`-left end `α` has cofinally many `≤₁`-predecessors ([C09] Def 5.3, clause 1 (d) with
`Y = {α}`). -/
theorem le2_preds_cofinal {α β : Ordinal.{0}} (h : le2 α β) (hαβ : α < β) :
    ∀ c < α, ∃ y, c < y ∧ y < α ∧ le1 y α := by
  classical
  intro c hc
  have h1 := le2_le1 h
  have hI := indec_of_lt1 h1 hαβ
  obtain ⟨_, H1, _⟩ := le2_iff.1 h
  obtain ⟨Yt, hYt, -, -, f, -, -, hY⟩ := cof_core hc (fun y z => le1 y β → le1 z α)
    (fun X Y hX hY hXY => H1 X Y hX hY hXY) ∅ {α} (by simp) (by simp [hαβ])
    (closed_singleton_of_indec hI)
  obtain ⟨hfY, hq⟩ := hY α (by simp)
  exact ⟨f α, (hYt _ hfY).1, (hYt _ hfY).2, hq h1⟩

/-- **RIGHT-LIM** (`R₂^C`, countable). -/
theorem right_lim {β : Ordinal.{0}} (hβ1 : β < Om1) (hβ0 : 0 < β)
    (hcof : ∀ c < β, ∃ y, c < y ∧ y < β ∧ le1 y β) : UpsPt β := by
  classical
  have hlimI : ∀ c < β, ∃ p, c < p ∧ p < β ∧ Indec p := fun c hc => by
    obtain ⟨y, hcy, hyβ, hy⟩ := hcof c hc
    exact ⟨y, hcy, hyβ, indec_of_lt1 hy hyβ⟩
  have hI : Indec β := indec_of_limit hβ0 hlimI
  by_contra hnu
  have h1β : 1 < β := by
    obtain ⟨p, -, hpβ, hp⟩ := hlimI 0 hβ0
    exact lt_of_le_of_lt (one_le_iff_pos.2 hp.pos) hpβ
  obtain ⟨τ, m, hg⟩ := exists_gap h1β hβ1 hnu
  obtain ⟨F, hFα, hF⟩ := preds_finite hg hβ1 hI
  have hsupF : F.sup id < β := by
    rw [Finset.sup_lt_iff hI.pos]; exact hFα
  obtain ⟨y, hcy, hyβ, hy⟩ := hcof _ (max_lt hg.base_lt hsupF)
  have hmem := hF y (lt_of_le_of_lt (le_max_left _ _) hcy) hyβ (inc1 hβ1 hy)
  exact absurd hcy (not_lt.2 (le_trans (Finset.le_sup (f := id) hmem) (le_max_right _ _)))

/-- **LEFT** (`R₂^C`, countable): a `<₂`-left end is `υ_λ` with `λ` a limit. -/
theorem left_limit {α β : Ordinal.{0}} (h : le2 α β) (hαβ : α < β) (hα1 : α < Om1) :
    ∃ l, IsSuccLimit l ∧ α = upsilon l := by
  obtain ⟨ι, hι, rfl⟩ := upsPt_iff_upsilon.1 (left h hαβ hα1)
  refine ⟨ι, ?_, rfl⟩
  rcases zero_or_succ_or_isSuccLimit ι with h0 | ⟨ξ, rfl⟩ | hl
  · exact absurd h0 hι.ne'
  · exfalso
    have hn := upsilon_isNext ξ
    obtain ⟨y, hcy, hyα, hy⟩ := le2_preds_cofinal h hαβ _ hn.1
    exact not_le1R_gap hn hcy hyα le_rfl (inc1 hα1 hy)
  · exact hl

/-- **RE-U** (`R₂^C`, countable; the `υ`-point part). -/
theorem re_u {α β : Ordinal.{0}} (hcof : ∀ z < α, ∃ p q, z < p ∧ p < q ∧ q < α ∧ le2 p q)
    (h : le2 α β) (hαβ : α < β) (hβ1 : β < Om1) : UpsPt β :=
  ups_of_pairs (lt_of_le_of_lt zero_le hαβ) le_rfl hβ1
    (fun _ hg _ hy => inc1 (lt_trans hg hβ1) hy) (pairs_up h hαβ hcof)

/-- The `R₂^C`-reach of a countable point is at most its `R₁⁺`-reach. -/
theorem le1_le_lh1 {a l g : Ordinal.{0}} (hl : IsLh1 a l) (hg1 : g < Om1) (h : le1 a g) :
    g ≤ l :=
  hl.2 g (inc1 hg1 h)

/-- **SK1 inside a block**. -/
theorem block_le1_iff {g x τ m : Ordinal.{0}} (hg1 : g < Om1) (hxg : x < g) (hx : le1 x g)
    (hxI : Indec x) (hgap : Gap τ m x) (hgm : g ≤ m)
    (hA : ∀ v < x, ∀ b, x < b → b < g → ¬ le2 v b) {p q : Ordinal.{0}} (hxp : x < p)
    (hpq : p < q) (hqg : q ≤ g) : le1 p q ↔ le1R p q := by
  have hB : Block g x τ m :=
    ⟨hg1, hxg, hx, fun _ hh _ hy => inc1 (lt_trans hh hg1) hy, hxI, hgap, hgm⟩
  exact ⟨fun h => inc1 (lt_of_le_of_lt hqg hg1) h, hB.clean hA q hqg p hxp hpq⟩

/-- The skeleton hypothesis of FRAG2 after INC1 and LEFT: (SK1⇐) for a non-`υ` left end, `R₁⁺`
gives `R₂^C`; (SK2) the caps; (SK3, right half) a `<₂`-right end is a `υ`-point. -/
def SkeletalC (cap : Ordinal.{0} → Ordinal.{0}) (Z : Set Ordinal.{0}) : Prop :=
  ∀ a ∈ Z, ∀ b ∈ Z, a < b →
    (¬ UpsPt a → le1R a b → le1 a b) ∧ (UpsPt a → (le1 a b ↔ b ≤ cap a)) ∧
      (le2 a b → UpsPt b)

theorem skeletal_of_skeletalC {cap : Ordinal.{0} → Ordinal.{0}} {Z : Set Ordinal.{0}}
    (hZ : ∀ z ∈ Z, z < Om1) (h : SkeletalC cap Z) : Skeletal cap Z := by
  intro a ha b hb hab
  obtain ⟨h1, h2, h3⟩ := h a ha b hb hab
  exact ⟨fun hU => ⟨inc1 (hZ b hb), h1 hU⟩, h2,
    fun h2' => ⟨left h2' hab (hZ a ha), h3 h2'⟩⟩

/-- **Theorem FRAG2** for `R₂^C` with the reduced skeleton hypothesis. -/
theorem frag2_C {cap : Ordinal.{0} → Ordinal.{0}} {Y : Finset Ordinal.{0}}
    {Ψ : Ordinal.{0} → Ordinal.{0}} (hmono : StrictMonoOn Ψ ↑Y)
    (hle1R : ∀ x ∈ Y, ∀ y ∈ Y, le1R x y ↔ le1R (Ψ x) (Ψ y))
    (hups : ∀ x ∈ Y, UpsPt (Ψ x) ↔ UpsPt x)
    (hcount : ∀ z ∈ (↑Y ∪ Ψ '' ↑Y : Set Ordinal.{0}), z < Om1)
    (hSK : SkeletalC cap (↑Y ∪ Ψ '' ↑Y)) :
    ((∀ x ∈ Y, ∀ y ∈ Y, le1 x y ↔ le1 (Ψ x) (Ψ y)) ∧
      (∀ x ∈ Y, ∀ y ∈ Y, le2 x y ↔ le2 (Ψ x) (Ψ y))) ↔
    (∀ u ∈ Y, ∀ z ∈ Y, UpsPt u → u < z →
      ((z ≤ cap u ↔ Ψ z ≤ cap (Ψ u)) ∧ (le2 u z ↔ le2 (Ψ u) (Ψ z)))) :=
  frag2 hmono hle1R hups (skeletal_of_skeletalC hcount hSK)

/-- **FRAG with FRAG2 in `R₂^C`**: for the data of Theorem FRAG there is a map `Ψ` with the
conclusions of FRAG, and, whenever the reduced skeleton holds on `F ∪ Ψ[F]`, `Ψ` is an isomorphism of
`R₂^C` on `F` iff it keeps the caps (C1) and the pairs (C2). -/
theorem frag_frag2_C {m : ℕ} {κ : Ordinal.{0}} {b c : ℕ → Ordinal.{0}} (hb : Chain κ b m)
    (hc : Chain κ c m) (F : Finset Ordinal.{0}) (hF : ↑F ⊆ DD κ b m) :
    ∃ Ψ, FragConcl κ b c m F Ψ ∧ ∀ cap : Ordinal.{0} → Ordinal.{0},
      SkeletalC cap (↑F ∪ Ψ '' ↑F) →
      (((∀ x ∈ F, ∀ y ∈ F, le1 x y ↔ le1 (Ψ x) (Ψ y)) ∧
        (∀ x ∈ F, ∀ y ∈ F, le2 x y ↔ le2 (Ψ x) (Ψ y))) ↔
      (∀ u ∈ F, ∀ z ∈ F, UpsPt u → u < z →
        ((z ≤ cap u ↔ Ψ z ≤ cap (Ψ u)) ∧ (le2 u z ↔ le2 (Ψ u) (Ψ z))))) := by
  obtain ⟨Ψ, hΨ⟩ := frag hb hc F hF
  obtain ⟨Q1, Q2, -, Q4, Q5, Q6, -⟩ := id hΨ
  have hcount : ∀ z ∈ (↑F ∪ Ψ '' ↑F : Set Ordinal.{0}), z < Om1 := by
    rintro z (hz | ⟨x, hx, rfl⟩)
    · exact DD_lt_Om1 hb (hF hz)
    · rcases mem_DD (hF hx) with h | ⟨k, hk, hs, -, -⟩
      · rw [Q1 x hx h]; exact h.trans hb.kap1
      · exact (Q2 k hk x hx hs).2.1
  exact ⟨Ψ, hΨ, fun cap hSK => frag2_C Q4.2.1 Q5 Q6 hcount hSK⟩

/-- **`R₂^C` agrees with `R₁⁺` below the first `<₂`-right end** (for `≤₁`): if no `<₂`-pair `c <₂ d`
has `d < B`, `B` countable, then `a ≤₁ b` in `R₂^C` iff in `R₁⁺`, for all `b ≤ B`.  (The `R₁⁺ ⇒ R₂^C`
direction copies by Theorem CC-F; every copy is a covering of `R₂^C` because no `≤₂`-atom has its
right end below `B`.) -/
theorem le1_iff_le1R_below {B : Ordinal.{0}} (hB : B < Om1)
    (hno : ∀ c d, c < d → d < B → ¬ le2 c d) : ∀ b ≤ B, ∀ a, le1 a b ↔ le1R a b := by
  classical
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hbB a
  refine ⟨fun h => inc1 (lt_of_le_of_lt hbB hB) h, fun hR => ?_⟩
  rcases eq_or_lt_of_le (le1R_le hR) with rfl | hab
  · exact le1_refl _
  refine le1_iff.2 ⟨hab.le, fun X Y hX hY hXY => ?_⟩
  set X2 : Finset Ordinal.{0} := X ∪ {0} with hX2def
  have hX2 : ∀ w ∈ X2, w < a := by
    intro w hw
    simp only [X2, Finset.mem_union, Finset.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact hX w hw
    · exact (le1R_lim_P hR hab).1
  have hX2Y : Closed ↑(X2 ∪ Y) := by
    have he : (↑(X2 ∪ Y) : Set Ordinal.{0}) = ↑(X ∪ Y) ∪ ({0} : Set Ordinal.{0}) := by
      ext w; simp only [X2, Finset.coe_union, Finset.coe_singleton, Set.mem_union,
        Set.mem_singleton_iff, Finset.mem_coe]; tauto
    rw [he]
    exact hXY.union closed_singleton_zero
  obtain ⟨ψ, hψ, hψc, hfix, hYψ, hψR⟩ := ccf hR X2 Y hX2 hY (by simp [X2]) hX2Y
  have hX2lt : ∀ c ∈ X2 ∪ Y, ∀ d ∈ X2, c < d → c ∈ X2 := by
    intro c hc d hd hcd
    rcases Finset.mem_union.1 hc with h | h
    · exact h
    · exact absurd (lt_trans hcd (hX2 d hd)) (not_lt.2 (hY c h).1)
  have hcov : Cov R2C R2C ↑(X2 ∪ Y) (ψ '' ↑(X2 ∪ Y)) ψ := by
    refine ⟨hψ, ?_, ?_⟩
    · intro c hc d hd hcd
      change le1 c d at hcd
      change le1 (ψ c) (ψ d)
      rcases eq_or_lt_of_le (le1_le hcd) with rfl | hcd'
      · exact le1_refl _
      rcases Finset.mem_union.1 hd with hdX | hdY
      · rw [hfix c (hX2lt c hc d hdX hcd'), hfix d hdX]; exact hcd
      · have hdb : d < b := (hY d hdY).2
        have hRcd : le1R c d := inc1 (lt_of_lt_of_le (lt_of_lt_of_le hdb hbB) hB.le) hcd
        have hRψ := hψR c hc d hd hRcd
        have hψdb : ψ d < b := lt_trans (hYψ d hdY).2 hab
        exact (IH (ψ d) hψdb (hψdb.le.trans hbB) (ψ c)).2 hRψ
    · intro c hc d hd hcd
      change le2 c d at hcd
      change le2 (ψ c) (ψ d)
      rcases eq_or_lt_of_le (le2_le hcd) with rfl | hcd'
      · exact le2_refl _
      rcases Finset.mem_union.1 hd with hdX | hdY
      · rw [hfix c (hX2lt c hc d hdX hcd'), hfix d hdX]; exact hcd
      · exact absurd hcd (hno c d hcd' (lt_of_lt_of_le (hY d hdY).2 hbB))
  have hsub : (↑(X ∪ Y) : Set Ordinal.{0}) ⊆ ↑(X2 ∪ Y) := by
    intro w hw
    simp only [X2, Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.coe_singleton,
      Set.mem_singleton_iff] at hw ⊢
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

/-- Every countable `<₂`-pair `c <₂ d` has `υ_ω ≤ c` (LEFT with the limit index). -/
theorem upsilon_omega_le_left {c d : Ordinal.{0}} (h : le2 c d) (hcd : c < d) (hc1 : c < Om1) :
    upsilon ω ≤ c := by
  obtain ⟨l, hl, rfl⟩ := left_limit h hcd hc1
  exact upsilon_normal.strictMono.monotone (omega0_le_of_isSuccLimit hl)

/-- **`R₂^C = R₁⁺` up to `υ_ω`** (for `≤₁`; no `<₂`-pair has its right end `≤ υ_ω`). -/
theorem le1_iff_le1R_upsilon_omega : ∀ b ≤ upsilon ω, ∀ a, le1 a b ↔ le1R a b :=
  have hω := upsilon_omega_lt_Om1
  le1_iff_le1R_below hω fun c d hcd hd h2 =>
    absurd (lt_of_le_of_lt (upsilon_omega_le_left h2 hcd (lt_trans (lt_trans hcd hd) hω)) hcd)
      (not_lt.2 hd.le)

end Googology.Trans.PoR.InaccPsi.R2
