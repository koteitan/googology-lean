import Googology.Trans.PSS.Main.Pattern

/-!
# Isominimal copies: Lemma 6.1 and the uniqueness of `ι`

* `bij_strictMono_unique`: two strictly increasing bijections of a set of
  ordinals onto the same set agree (a well-order has one isomorphism onto a given
  well-order).
* `PwLe.antisymm`: `≤_pw` is antisymmetric.
* **Lemma 6.1** (`lemma61`, the sandwich, `proof/PROOF.md` §6): if `X` is finite and
  closed, `h` is the isomorphism of `X` onto its isominimal copy, and `α` lies in
  an isominimal `Z ⊆ X`, then `h(α) = α`.
* `iotaPat_eq`: if `f` is an isomorphism of a structure `P` onto a finite closed set
  `X` of ordinals, and `h` one of `X` onto an isominimal set, then
  `ι(P)` at `a` is `h(f(a))`.
-/

namespace Googology.Trans.PSS.Main

open Ordinal Function

/-! ## Strictly increasing bijections -/

theorem bij_strictMono_unique {A B : Set Ordinal.{0}} {f g : Ordinal.{0} → Ordinal.{0}}
    (hf : Set.BijOn f A B) (hf' : StrictMonoOn f A) (hg : Set.BijOn g A B)
    (hg' : StrictMonoOn g A) : ∀ a ∈ A, f a = g a := by
  intro a
  induction a using WellFoundedLT.induction with
  | _ a IH =>
    intro ha
    rcases lt_trichotomy (f a) (g a) with h | h | h
    · exfalso
      obtain ⟨a', ha', e⟩ := hg.surjOn (hf.mapsTo ha)
      have ha'a : a' < a := by
        by_contra h'
        push Not at h'
        have := hg'.monotoneOn ha ha' h'
        rw [e] at this
        exact absurd h (not_lt.mpr this)
      have := IH a' ha'a ha'
      rw [e] at this
      exact absurd (hf.injOn ha' ha this) (ne_of_lt ha'a)
    · exact h
    · exfalso
      obtain ⟨a', ha', e⟩ := hf.surjOn (hg.mapsTo ha)
      have ha'a : a' < a := by
        by_contra h'
        push Not at h'
        have := hf'.monotoneOn ha ha' h'
        rw [e] at this
        exact absurd h (not_lt.mpr this)
      have := IH a' ha'a ha'
      rw [e] at this
      exact absurd (hg.injOn ha' ha this.symm) (ne_of_lt ha'a)

theorem bij_strictMono_self {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}}
    (hf : Set.BijOn f A A) (hf' : StrictMonoOn f A) : ∀ a ∈ A, f a = a :=
  bij_strictMono_unique hf hf' (Set.bijOn_id A) strictMonoOn_id

theorem StrictMonoOn.invFunOn {A B : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}}
    (hf : Set.BijOn f A B) (hf' : StrictMonoOn f A) : StrictMonoOn (Function.invFunOn f A) B := by
  intro y hy y' hy' h
  have hx := Function.invFunOn_mem (hf.surjOn hy)
  have hx' := Function.invFunOn_mem (hf.surjOn hy')
  have e := Function.invFunOn_eq (hf.surjOn hy)
  have e' := Function.invFunOn_eq (hf.surjOn hy')
  by_contra hle
  push Not at hle
  have := hf'.monotoneOn hx' hx hle
  rw [e, e'] at this
  exact absurd h (not_lt.mpr this)

theorem PwLe.antisymm {A B : Set Ordinal.{0}} (h1 : PwLe A B) (h2 : PwLe B A) : A = B := by
  obtain ⟨f, hf, hf', hfa⟩ := h1
  obtain ⟨g, hg, hg', hgb⟩ := h2
  have hgf : ∀ a ∈ A, g (f a) = a :=
    bij_strictMono_self (hg.comp hf) (fun a ha b hb h => hg' (hf.mapsTo ha) (hf.mapsTo hb) (hf' ha hb h))
  have hfix : ∀ a ∈ A, f a = a := fun a ha =>
    le_antisymm (by have := hgb (f a) (hf.mapsTo ha); rwa [hgf a ha] at this) (hfa a ha)
  ext x
  constructor
  · intro hx; rw [← hfix x hx]; exact hf.mapsTo hx
  · intro hx
    obtain ⟨a, ha, rfl⟩ := hf.surjOn hx
    rw [hfix a ha]; exact ha

/-! ## Isomorphisms of sets of ordinals -/

theorem IsoVia.covering {X Y : Set Ordinal.{0}} {h : Ordinal.{0} → Ordinal.{0}}
    (hh : IsoVia X Y h) : CoveringVia X Y h :=
  ⟨hh.1, hh.2.1, hh.2.2.1, fun a ha b hb h => (hh.2.2.2 a ha b hb).mp h⟩

theorem IsoVia.symm {X Y : Set Ordinal.{0}} {h : Ordinal.{0} → Ordinal.{0}}
    (hh : IsoVia X Y h) : IsoVia Y X (Function.invFunOn h X) := by
  obtain ⟨hb, hm, hadd, hle⟩ := hh
  set g := Function.invFunOn h X
  have hgX : ∀ y ∈ Y, g y ∈ X := fun y hy => Function.invFunOn_mem (hb.surjOn hy)
  have hhg : ∀ y ∈ Y, h (g y) = y := fun y hy => Function.invFunOn_eq (hb.surjOn hy)
  refine ⟨(hb.invOn_invFunOn.symm).bijOn hb.surjOn.mapsTo_invFunOn hb.mapsTo,
    StrictMonoOn.invFunOn hb hm, ?_, ?_⟩
  · intro a ha b hb' c hc
    rw [hadd _ (hgX a ha) _ (hgX b hb') _ (hgX c hc), hhg a ha, hhg b hb', hhg c hc]
  · intro a ha b hb'
    rw [hle _ (hgX a ha) _ (hgX b hb'), hhg a ha, hhg b hb']

theorem IsoVia.left_inv {X Y : Set Ordinal.{0}} {h : Ordinal.{0} → Ordinal.{0}}
    (hh : IsoVia X Y h) {a : Ordinal.{0}} (ha : a ∈ X) : Function.invFunOn h X (h a) = a :=
  hh.1.injOn (Function.invFunOn_mem ⟨a, ha, rfl⟩) ha (Function.invFunOn_eq ⟨a, ha, rfl⟩)

theorem IsoVia.restrict {X Y Z : Set Ordinal.{0}} {h : Ordinal.{0} → Ordinal.{0}}
    (hh : IsoVia X Y h) (hZ : Z ⊆ X) : IsoVia Z (h '' Z) h :=
  ⟨⟨Set.mapsTo_image _ _, hh.1.injOn.mono hZ, Set.surjOn_image _ _⟩, hh.2.1.mono hZ,
    fun a ha b hb c hc => hh.2.2.1 a (hZ ha) b (hZ hb) c (hZ hc),
    fun a ha b hb => hh.2.2.2 a (hZ ha) b (hZ hb)⟩

/-! ## Lemma 6.1 -/

/-- The isomorphism onto the isominimal copy lowers every point: `h(q) ≤ q`
([CW12] Core Structure Theorem (2): the copy is `≤_pw` below the covering `X`). -/
theorem isominimal_copy_le {X Y : Finset Ordinal.{0}} (hX : ClosedSet (X : Set Ordinal.{0}))
    (hY : Isominimal Y) {h : Ordinal.{0} → Ordinal.{0}} (hh : IsoVia X Y h) :
    ∀ q ∈ (X : Set Ordinal.{0}), h q ≤ q := by
  have hs := hh.symm
  obtain ⟨f, hf, hf', hfy⟩ := pwLe_of_covering hY hX ⟨_, hs.covering⟩
  have e := bij_strictMono_unique hf hf' hs.1 hs.2.1
  intro q hq
  have hy : h q ∈ (Y : Set Ordinal.{0}) := hh.1.mapsTo hq
  have := hfy (h q) hy
  rw [e (h q) hy, hh.left_inv hq] at this
  exact this

/-- **Lemma 6.1** (the sandwich, `proof/PROOF.md` §6).  Let `X` be a finite closed
set, `h` an isomorphism of `X` onto an isominimal set, `Z ⊆ X` isominimal and
`α ∈ Z`.  Then `h(α) = α`. -/
theorem lemma61 {X Y Z : Finset Ordinal.{0}} (hX : ClosedSet (X : Set Ordinal.{0}))
    (hY : Isominimal Y) {h : Ordinal.{0} → Ordinal.{0}} (hh : IsoVia X Y h) (hZX : Z ⊆ X)
    (hZ : Isominimal Z) : ∀ α ∈ (Z : Set Ordinal.{0}), h α = α := by
  have hZX' : (Z : Set Ordinal.{0}) ⊆ X := by simpa using hZX
  have hle := isominimal_copy_le hX hY hh
  -- `h[Z]` is a copy of `Z` below `Z`, hence `Z`
  have hiso : IsoVia (Z : Set Ordinal.{0}) ((Z.image h : Finset Ordinal.{0}) : Set Ordinal.{0}) h := by
    rw [Finset.coe_image]; exact hh.restrict hZX'
  have hpw : PwLe ((Z.image h : Finset Ordinal.{0}) : Set Ordinal.{0}) Z := by
    have hs := hiso.symm
    refine ⟨_, hs.1, hs.2.1, fun y hy => ?_⟩
    rw [Finset.coe_image] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    rw [hiso.left_inv ha]
    exact hle a (hZX' ha)
  have e : Z.image h = Z := hZ.2 _ ⟨h, hiso⟩ hpw
  -- so `h` maps `Z` onto `Z` and is the identity there
  have hbij : Set.BijOn h Z Z := by
    have := hiso.1
    rwa [e] at this
  exact bij_strictMono_self hbij (hh.2.1.mono hZX')

/-! ## The isominimal realization is unique -/

theorem Pat.IsoVia.comp {α : Type} {P : Pat α} {X Y : Set Ordinal.{0}} {f : α → Ordinal.{0}}
    {h : Ordinal.{0} → Ordinal.{0}} (hf : P.IsoVia X f) (hh : Main.IsoVia X Y h) :
    P.IsoVia Y (h ∘ f) := by
  obtain ⟨hfb, hflt, hfadd, hfle⟩ := hf
  obtain ⟨hhb, hhm, hhadd, hhle⟩ := hh
  refine ⟨hhb.comp hfb, fun a ha b hb => ?_, fun a ha b hb c hc => ?_, fun a ha b hb => ?_⟩
  · rw [hflt a ha b hb]
    exact ⟨fun h' => hhm (hfb.mapsTo ha) (hfb.mapsTo hb) h',
      fun h' => (hhm.lt_iff_lt (hfb.mapsTo ha) (hfb.mapsTo hb)).mp h'⟩
  · rw [hfadd a ha b hb c hc]
    exact hhadd _ (hfb.mapsTo ha) _ (hfb.mapsTo hb) _ (hfb.mapsTo hc)
  · rw [hfle a ha b hb]
    exact hhle _ (hfb.mapsTo ha) _ (hfb.mapsTo hb)

/-- Two isomorphisms of `P` onto sets of ordinals give an isomorphism of the sets. -/
theorem Pat.IsoVia.trans_symm {α : Type} [Nonempty α] {P : Pat α} {Y₁ Y₂ : Set Ordinal.{0}}
    {g₁ g₂ : α → Ordinal.{0}} (h₁ : P.IsoVia Y₁ g₁) (h₂ : P.IsoVia Y₂ g₂) :
    Main.IsoVia Y₁ Y₂ (g₂ ∘ Function.invFunOn g₁ P.U) := by
  obtain ⟨b₁, lt₁, add₁, le₁⟩ := h₁
  obtain ⟨b₂, lt₂, add₂, le₂⟩ := h₂
  set k := Function.invFunOn g₁ P.U
  have hk : ∀ y ∈ Y₁, k y ∈ P.U := fun y hy => Function.invFunOn_mem (b₁.surjOn hy)
  have hgk : ∀ y ∈ Y₁, g₁ (k y) = y := fun y hy => Function.invFunOn_eq (b₁.surjOn hy)
  have hkb : Set.BijOn k Y₁ P.U :=
    (b₁.invOn_invFunOn.symm).bijOn b₁.surjOn.mapsTo_invFunOn b₁.mapsTo
  refine ⟨b₂.comp hkb, fun y hy y' hy' h => ?_, fun a ha b hb c hc => ?_, fun a ha b hb => ?_⟩
  · show g₂ (k y) < g₂ (k y')
    rw [← lt₂ _ (hk y hy) _ (hk y' hy'), lt₁ _ (hk y hy) _ (hk y' hy'), hgk y hy, hgk y' hy']
    exact h
  · show a + b = c ↔ g₂ (k a) + g₂ (k b) = g₂ (k c)
    rw [← add₂ _ (hk a ha) _ (hk b hb) _ (hk c hc), add₁ _ (hk a ha) _ (hk b hb) _ (hk c hc),
      hgk a ha, hgk b hb, hgk c hc]
  · show Main.le1 a b ↔ Main.le1 (g₂ (k a)) (g₂ (k b))
    rw [← le₂ _ (hk a ha) _ (hk b hb), le₁ _ (hk a ha) _ (hk b hb), hgk a ha, hgk b hb]

/-- Isomorphic isominimal sets are equal ([CW12] Core Structure Theorem (2)). -/
theorem isominimal_unique {Y₁ Y₂ : Finset Ordinal.{0}} (h₁ : Isominimal Y₁) (h₂ : Isominimal Y₂)
    {k : Ordinal.{0} → Ordinal.{0}} (hk : IsoVia Y₁ Y₂ k) : Y₁ = Y₂ := by
  have p₁ := pwLe_of_covering h₁ h₂.1 ⟨k, hk.covering⟩
  have p₂ := pwLe_of_covering h₂ h₁.1 ⟨_, hk.symm.covering⟩
  exact_mod_cast PwLe.antisymm p₁ p₂

/-- Two isomorphisms of `P` onto the same set of ordinals agree. -/
theorem Pat.IsoVia.unique {α : Type} [Nonempty α] {P : Pat α} {Y : Set Ordinal.{0}} {g₁ g₂ : α → Ordinal.{0}}
    (h₁ : P.IsoVia Y g₁) (h₂ : P.IsoVia Y g₂) : ∀ a ∈ P.U, g₁ a = g₂ a := by
  have hk := h₁.trans_symm h₂
  have hid := bij_strictMono_self hk.1 hk.2.1
  intro a ha
  have := hid (g₁ a) (h₁.1.mapsTo ha)
  simp only [Function.comp] at this
  rw [h₁.1.injOn (Function.invFunOn_mem ⟨a, ha, rfl⟩) ha
    (Function.invFunOn_eq ⟨a, ha, rfl⟩)] at this
  exact this.symm

/-- **`ι` is well defined**: for an isomorphism `f` of `P` onto a finite closed set
`X` of ordinals, and an isomorphism `h` of `X` onto an isominimal set,
`ι(P)` at `a` is `h(f(a))`. -/
theorem iotaPat_eq {α : Type} [Nonempty α] {P : Pat α} {X Y : Finset Ordinal.{0}} {f : α → Ordinal.{0}}
    (hf : P.IsoVia X f) (hY : Isominimal Y) {h : Ordinal.{0} → Ordinal.{0}}
    (hh : IsoVia X Y h) {a : α} (ha : a ∈ P.U) : iotaPat P a = h (f a) := by
  have hc : P.IsoVia Y (h ∘ f) := hf.comp hh
  have hex : ∃ (Y : Finset Ordinal.{0}) (g : α → Ordinal.{0}), Isominimal Y ∧ P.IsoVia Y g :=
    ⟨Y, h ∘ f, hY, hc⟩
  unfold iotaPat
  rw [dif_pos hex]
  obtain ⟨hY', hg'⟩ := hex.choose_spec.choose_spec
  have e : hex.choose = Y := isominimal_unique hY' hY (hg'.trans_symm hc)
  have hg'' : P.IsoVia Y hex.choose_spec.choose := e ▸ hg'
  exact hg''.unique hc a ha

end Googology.Trans.PSS.Main
