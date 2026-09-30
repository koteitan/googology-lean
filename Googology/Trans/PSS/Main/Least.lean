import Googology.Trans.PSS.Main.BarClosure

/-!
# Theorem LEAST: `o[V_M]` lies pointwise below every isomorphic copy

**Theorem LEAST** (`ordV_least`): for a standard node `M` and
`X = o[V_M]`, every isomorphism `g` of `X` onto a set of ordinals (`IsoVia`, keeping `<`, the
graph of `+` and `≤₁` both ways) satisfies `g(β) ≥ β` on `X`.

Proof: Theorem S⁺ (`splus`) at the base `σ = 1` with `S = X` and `h = g`.  `X` is closed,
contains `0` and `1`, is closed under `lh` (Lemma L) and under bar (`barClosure`), and
`bar(y)` is a witness for every principal `y > 1` in `X`: for `y ∉ E` by Fact BAR
(`factBar`, `factBar1`), for `y ∈ E` by [CW12] Lemma 5.7.1 (`lemma571_eps`).

So `X` is isominimal, and `ι(Φ(M)) = o(M)` follows without the Core Structure Theorem
(`iotaPat_eq_least` in `Main/Iso.lean`).
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Order Phi Forest

/-- `bar(y)` is a witness of Theorem S⁺ for every principal `y ∈ (1, T¹ ∩ Ω_1)`. -/
theorem witS_barO {y : Ordinal.{0}} (_hP : Pr y) (h1 : 1 < y) (hT : y < T1bound) :
    WitS y (barO y) := by
  refine ⟨fun hE l hl hy => ?_, fun hE γ hγ hbγ hγy => lemma571_eps hE hT hγ hbγ hγy⟩
  rcases l with _ | ⟨ζ, _ | ⟨ζ2, l⟩⟩
  · simp at hy; rw [hy] at h1; exact absurd h1 (lt_irrefl _)
  · -- one summand: `bar(y) ≥ 1`
    simp only [List.dropLast_singleton, List.sum_nil, opow_zero]
    simp only [List.sum_cons, List.sum_nil, add_zero] at hy
    have hζP : Pr ζ := hl.1 ζ (by simp)
    have hζE : ¬ InE ζ := fun hζ => hE (by rw [hy, hζ]; exact hζ)
    rcases factBar1 hζP hζE (hy ▸ hT) with ⟨e, -⟩ | ⟨hb, -, -⟩
    · rw [hy, e]
    · rw [hy]; exact hb.one_lt.le
  · -- at least two summands: Fact BAR
    rw [hy, factBar hl (by simp) (hy ▸ hT)]

/-- **Theorem LEAST**. -/
theorem ordV_least {M : List Tm} (hM : StdOrd M) {X : Finset Ordinal.{0}}
    (hX : (X : Set Ordinal.{0}) = ordOf '' {x | InV M x}) {Y : Set Ordinal.{0}}
    {g : Ordinal.{0} → Ordinal.{0}} (hg : IsoVia X Y g) : ∀ β ∈ X, β ≤ g β := by
  have memX : ∀ {β : Ordinal.{0}}, β ∈ X ↔ β ∈ ordOf '' {x | InV M x} := by
    intro β; rw [← hX]; rfl
  have hC := closed_ordV hM
  -- a principal element above `1` is the ordinal of a one-root node
  have single : ∀ {v : List Tm}, InV M v → Pr (ordOf v) → ∃ t, v = [t] ∧ Std t := by
    intro v hv hP
    have hvs := stdOrd_of_inV hM hv
    rcases v with _ | ⟨t, _ | ⟨t', S⟩⟩
    · rw [ordOf_nil] at hP; exact absurd rfl hP.2
    · exact ⟨t, rfl, ((stdOrd_iff _).mp hvs).2 t (by simp)⟩
    · exact absurd hP (not_pr_of_two hvs)
  refine splus (σ := 1) ⟨le_rfl, memX.mpr ⟨[Tm.node 0 []], InV.one, ordOf_leaf_eq⟩,
    memX.mpr ⟨[], InV.nil, ordOf_nil⟩, ?_, ?_, ?_, ?_, hg.2.1, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := memX.mp hx
    exact ordOf_lt_T1bound (stdOrd_of_inV hM hv)
  · intro l hl hs
    obtain ⟨h1, h2⟩ := hC.2 l hl (memX.mp hs)
    exact ⟨fun x hx => memX.mpr (h1 x hx), fun i => memX.mpr (h2 i)⟩
  · intro y hy hP _
    obtain ⟨v, hv, rfl⟩ := memX.mp hy
    obtain ⟨t, rfl, ht⟩ := single hv hP
    exact ⟨ordOf (lh t), memX.mpr ⟨lh t, InV.lh hv, rfl⟩, lemmaL ht⟩
  · intro y hy hP h1
    obtain ⟨v, hv, rfl⟩ := memX.mp hy
    obtain ⟨t, rfl, ht⟩ := single hv hP
    have hT := ordOf_lt_T1bound (stdOrd_of_inV hM hv)
    obtain ⟨w, hw, e⟩ := barClosure hM hv h1
    exact ⟨barO (ordOf [t]), memX.mpr ⟨w, hw, e⟩, barO_lt hP h1 hT, witS_barO hP h1 hT⟩
  · intro a ha b hb hab
    exact ((hg.2.2.1 a ha b hb (a + b) hab).mp rfl).symm
  · intro x hx hx1
    rcases hx1.lt_or_eq with h0 | rfl
    · rw [Order.lt_one_iff.mp h0]; exact zero_le
    · have h0X : (0 : Ordinal.{0}) ∈ (X : Set Ordinal.{0}) := memX.mpr ⟨[], InV.nil, ordOf_nil⟩
      have := hg.2.1 h0X hx zero_lt_one
      exact Order.one_le_iff_pos.mpr (lt_of_le_of_lt zero_le this)
  · intro y hy w hw _ _ hyw _
    exact (hg.2.2.2 y hy w hw).mp hyw

end Googology.Trans.PSS.Main
