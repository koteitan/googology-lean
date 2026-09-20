import Googology.Core.Rewrite

/-!
# Translations, in general

Translations come in a hierarchy.  The weaker ones are cheaper to build; the
stronger ones give more.

| structure | what it asks for | what it gives |
|---|---|---|
| `OrdHom` | preserves the order | well-foundedness transfers |
| `Sim` | one step maps to one step | well-foundedness and termination transfer |
| `StepHom` | commutes with expansion | becomes a `Sim` |
| `Equiv` | mutually inverse `Sim`s | well-foundedness and termination are equivalent |
| `Eval` | expansion system to an order | termination; changing the target system |

Only the general theory lives here.  Concrete translations between named
systems go in `Googology/Trans/`.
-/

namespace Googology

/-! ## Order-preserving maps -/

/-- A strictly monotone map.  Neither injectivity nor surjectivity is asked
for. -/
structure OrdHom {A : Type u} {B : Type v} (ltA : A → A → Prop) (ltB : B → B → Prop) where
  /-- The underlying map. -/
  map : A → B
  /-- The map preserves the order. -/
  map_lt : ∀ {a b}, ltA a b → ltB (map a) (map b)

namespace OrdHom

variable {A : Type u} {B : Type v} {C : Type w} {ltA : A → A → Prop} {ltB : B → B → Prop} {ltC : C → C → Prop}

/-- The identity. -/
def refl (lt : A → A → Prop) : OrdHom lt lt := ⟨id, fun h => h⟩

/-- Composition. -/
def comp (f : OrdHom ltA ltB) (g : OrdHom ltB ltC) : OrdHom ltA ltC :=
  ⟨g.map ∘ f.map, fun h => g.map_lt (f.map_lt h)⟩

/-- If the target is well founded, so is the source.  No injectivity or
surjectivity is needed. -/
theorem wf (f : OrdHom ltA ltB) (h : WellFounded ltB) : WellFounded ltA :=
  Subrelation.wf (fun hab => f.map_lt hab) (InvImage.wf f.map h)

/-- Under trichotomy of the source order and irreflexivity of the target
order, the map is injective. -/
theorem injective (f : OrdHom ltA ltB)
    (tri : ∀ a b : A, ltA a b ∨ a = b ∨ ltA b a)
    (irr : ∀ b : B, ¬ ltB b b) : Function.Injective f.map := by
  intro a b hab
  rcases tri a b with h | h | h
  · exact absurd (hab ▸ f.map_lt h) (irr _)
  · exact h
  · exact absurd (hab ▸ f.map_lt h) (irr _)

end OrdHom

/-! ## Translations between expansion systems -/

/-- A simulation: one step maps to one step. -/
structure Sim (R Q : Rewrite) where
  /-- The underlying map. -/
  map : R.State → Q.State
  /-- One step maps to one step. -/
  map_rel : ∀ a b, R.Rel b a → Q.Rel (map b) (map a)

namespace Sim

variable {R Q P : Rewrite}

/-- The identity. -/
def refl (R : Rewrite) : Sim R R := ⟨id, fun _ _ h => h⟩

/-- Composition. -/
def comp (f : Sim R Q) (g : Sim Q P) : Sim R P :=
  ⟨g.map ∘ f.map, fun a b h => g.map_rel _ _ (f.map_rel a b h)⟩

/-- If the target is well founded, so is the source. -/
theorem wf (f : Sim R Q) (h : Q.WF) : R.WF :=
  R.wf_of_measure Q.Rel h f.map f.map_rel

/-- If the target is well founded, the source terminates. -/
theorem terminates (f : Sim R Q) (h : Q.WF) : R.Terminates :=
  R.terminates_of_wf (f.wf h)

/-- Termination transfers backwards along a simulation. -/
theorem terminates_transfer (f : Sim Q R) (h : R.Terminates) : Q.Terminates := by
  intro c hc
  apply Classical.byContradiction
  intro hno
  have hnh : ∀ n, ¬ Q.halted (c n) := fun n hn => hno ⟨n, hn⟩
  have hrel : ∀ n, R.Rel (f.map (c (n + 1))) (f.map (c n)) :=
    fun n => f.map_rel (c n) (c (n + 1)) ⟨hnh n, hc n⟩
  obtain ⟨n, hn⟩ := h (fun n => f.map (c n)) (fun n => (hrel n).2)
  exact (hrel n).1 hn

end Sim

/-- A translation commuting with expansion: it preserves fundamental
sequences.  `reindex` renumbers brackets; pass `id` when the numbering is
unchanged. -/
structure StepHom (R Q : Rewrite) where
  /-- The underlying map. -/
  map : R.State → Q.State
  /-- Renumbering of brackets. -/
  reindex : Nat → Nat
  /-- The map commutes with expansion. -/
  map_step : ∀ s k, map (R.step s k) = Q.step (map s) (reindex k)
  /-- A halting image comes from a halting state. -/
  map_halted : ∀ s, Q.halted (map s) → R.halted s

/-- Commuting with expansion yields a simulation. -/
def StepHom.toSim {R Q : Rewrite} (f : StepHom R Q) : Sim R Q where
  map := f.map
  map_rel := by
    rintro a b ⟨hna, k, rfl⟩
    exact ⟨fun h => hna (f.map_halted a h), f.reindex k, f.map_step a k⟩

/-- Mutually inverse translations. -/
structure Equiv (R Q : Rewrite) where
  /-- The forward simulation. -/
  toFun : Sim R Q
  /-- The backward simulation. -/
  invFun : Sim Q R
  /-- Going forth and back is the identity. -/
  left_inv : ∀ s, invFun.map (toFun.map s) = s
  /-- Going back and forth is the identity. -/
  right_inv : ∀ s, toFun.map (invFun.map s) = s

/-- Well-foundedness is equivalent on both sides. -/
theorem Equiv.wf_iff {R Q : Rewrite} (e : Equiv R Q) : R.WF ↔ Q.WF :=
  ⟨fun h => e.invFun.wf h, fun h => e.toFun.wf h⟩

/-- Termination is equivalent on both sides. -/
theorem Equiv.terminates_iff {R Q : Rewrite} (e : Equiv R Q) :
    R.Terminates ↔ Q.Terminates :=
  ⟨fun h => e.invFun.terminates_transfer h, fun h => e.toFun.terminates_transfer h⟩

/-! ## Evaluation: from an expansion system into an order

This is where the two halves above meet. -/

/-- An evaluation: the witness of termination itself. -/
structure Eval (R : Rewrite) {W : Type v} (lt : W → W → Prop) where
  /-- The value assigned to a state. -/
  val : R.State → W
  /-- One step strictly decreases the value. -/
  val_lt : ∀ a b, R.Rel b a → lt (val b) (val a)

namespace Eval

variable {R Q : Rewrite} {W : Type v} {X : Type w} {ltW : W → W → Prop} {ltX : X → X → Prop}

/-- An evaluation into a well-founded order makes the system well founded. -/
theorem wf (e : Eval R ltW) (h : WellFounded ltW) : R.WF :=
  R.wf_of_measure ltW h e.val e.val_lt

/-- An evaluation into a well-founded order makes the system terminate. -/
theorem terminates (e : Eval R ltW) (h : WellFounded ltW) : R.Terminates :=
  R.terminates_of_wf (e.wf h)

/-- An evaluation composed with an order-preserving map is an evaluation.
This is how one changes the target notation system. -/
def compOrd (e : Eval R ltW) (f : OrdHom ltW ltX) : Eval R ltX where
  val := f.map ∘ e.val
  val_lt := fun a b h => f.map_lt (e.val_lt a b h)

/-- A simulation pulls an evaluation of the target back to the source. -/
def ofSim (s : Sim R Q) (e : Eval Q ltW) : Eval R ltW where
  val := e.val ∘ s.map
  val_lt := fun a b h => e.val_lt _ _ (s.map_rel a b h)

end Eval
end Googology
