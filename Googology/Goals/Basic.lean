import Googology.Core.Goals
import Googology.Rank

/-!
# Goal records for translations

The record types of the second and third tables of the README (section 7.4 of
`spec.md`).  They talk about ordinals and ranks, so they live outside `Core`.

* `OrdGoals`: a translation `o` of a notation into the ordinals.
* `TransGoals`: a translation `F` from one notation to another, on the states
  `dom`.

As in `Googology/Core/Goals.lean`, the objects the propositions talk about are
parameters of the type, and the fields are labels and `Goal` values.
-/

namespace Googology

/-- The goals of a translation `o` into the ordinals: the columns of the
second table.  `X` is the set of ordinals the image should be, and `lt` the
order the notation puts on its states; both are defined without `o`. -/
structure OrdGoals {Idx : Type} (sys : Idx → Rewrite)
    (std : (i : Idx) → (sys i).Std)
    (o : (i : Idx) → (sys i).State → Ordinal.{0})
    (X : Idx → Set Ordinal.{0})
    (lt : (i : Idx) → (sys i).State → (sys i).State → Prop) where
  /-- The row label in `README.md`. -/
  labelEn : String
  /-- The row label in `README-ja.md`. -/
  labelJa : String
  /-- Injective on the standard forms. -/
  injective : Goal (∀ i a b, (std i).Standard a → (std i).Standard b →
      o i a = o i b → a = b)
  /-- The image of the standard forms is `X`. -/
  surjective : Goal (∀ i, {α | ∃ a, (std i).Standard a ∧ o i a = α} = X i)
  /-- One step lowers the value. -/
  decreasing : Goal (∀ i a b, (std i).Standard a → (std i).Standard b →
      (sys i).Rel b a → o i b < o i a)
  /-- The value is the rank. -/
  rank : Goal (∀ i, ∃ h : (std i).WF,
      ∀ a (ha : (std i).Standard a), o i a = (std i).rank h a ha)
  /-- The order on the states is the order of the values. -/
  order : Goal (∀ i a b, (std i).Standard a → (std i).Standard b →
      (lt i a b ↔ o i a < o i b))

/-- The goals of a translation `F` from `R` to `Q`, on the states `dom`: the
six marks of a cell of the third table.  With `dom i := fun _ => True` the
fields are the propositions of section 6 of `spec.md` word for word. -/
structure TransGoals {Idx : Type} (R Q : Idx → Rewrite)
    (dom : (i : Idx) → (R i).State → Prop)
    (F : (i : Idx) → (R i).State → (Q i).State) where
  /-- The row label (the source) in `README.md`. -/
  sourceEn : String
  /-- The row label (the source) in `README-ja.md`. -/
  sourceJa : String
  /-- The column label (the target) in `README.md`. -/
  targetEn : String
  /-- The column label (the target) in `README-ja.md`. -/
  targetJa : String
  /-- One step goes to one step. -/
  preserves : Goal (∀ i a b, dom i a → dom i b →
      (R i).Rel b a → (Q i).Rel (F i b) (F i a))
  /-- The map commutes with expansion, up to a renumbering of brackets. -/
  commutes : Goal (∃ ρ : Idx → Nat → Nat, ∀ i,
      (∀ a k, dom i a → dom i ((R i).step a k) ∧
        F i ((R i).step a k) = (Q i).step (F i a) (ρ i k)) ∧
      (∀ a, dom i a → (Q i).halted (F i a) → (R i).halted a))
  /-- Injective. -/
  injective : Goal (∀ i a b, dom i a → dom i b → F i a = F i b → a = b)
  /-- Surjective onto the states of the target. -/
  surjective : Goal (∀ i c, ∃ a, dom i a ∧ F i a = c)
  /-- The rank is the same on both sides. -/
  rank : Goal (∀ i, ∃ (hR : (R i).WF) (hQ : (Q i).WF),
      ∀ a, dom i a → Rewrite.rank hQ (F i a) = Rewrite.rank hR a)

/-- The lines of an `OrdGoals` record, one per column of the second table. -/
@[macro_inline] def OrdGoals.lines {Idx : Type} {sys : Idx → Rewrite}
    {std : (i : Idx) → (sys i).Std} {o : (i : Idx) → (sys i).State → Ordinal.{0}}
    {X : Idx → Set Ordinal.{0}} {lt : (i : Idx) → (sys i).State → (sys i).State → Prop}
    (g : OrdGoals sys std o X lt) (name : String) : List AuditLine :=
  [ ⟨"ordinal", name, g.labelEn, g.labelJa, "", "", "defined", .proved⟩,
    ⟨"ordinal", name, g.labelEn, g.labelJa, "", "", "injective", g.injective.status⟩,
    ⟨"ordinal", name, g.labelEn, g.labelJa, "", "", "surjective", g.surjective.status⟩,
    ⟨"ordinal", name, g.labelEn, g.labelJa, "", "", "decreasing", g.decreasing.status⟩,
    ⟨"ordinal", name, g.labelEn, g.labelJa, "", "", "rank", g.rank.status⟩,
    ⟨"ordinal", name, g.labelEn, g.labelJa, "", "", "order", g.order.status⟩ ]

/-- The lines of a `TransGoals` record, one per mark of a cell of the third
table. -/
@[macro_inline] def TransGoals.lines {Idx : Type} {R Q : Idx → Rewrite}
    {dom : (i : Idx) → (R i).State → Prop} {F : (i : Idx) → (R i).State → (Q i).State}
    (g : TransGoals R Q dom F) (name : String) : List AuditLine :=
  [ ⟨"between", name, g.sourceEn, g.sourceJa, g.targetEn, g.targetJa, "defined", .proved⟩,
    ⟨"between", name, g.sourceEn, g.sourceJa, g.targetEn, g.targetJa, "preserves",
      g.preserves.status⟩,
    ⟨"between", name, g.sourceEn, g.sourceJa, g.targetEn, g.targetJa, "commutes",
      g.commutes.status⟩,
    ⟨"between", name, g.sourceEn, g.sourceJa, g.targetEn, g.targetJa, "injective",
      g.injective.status⟩,
    ⟨"between", name, g.sourceEn, g.sourceJa, g.targetEn, g.targetJa, "surjective",
      g.surjective.status⟩,
    ⟨"between", name, g.sourceEn, g.sourceJa, g.targetEn, g.targetJa, "rank",
      g.rank.status⟩ ]

end Googology
