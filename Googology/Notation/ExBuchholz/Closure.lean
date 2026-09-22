import Googology.Notation.ExBuchholz.FS

/-!
# Towards the closure of `OT` under the fundamental sequence

`step_lt` says one expansion step decreases.  The last thing `exb.WF` needs is
that it keeps a term standard — Buchholz's Lemma 3.3 for the extended system.

Buchholz proves 3.3 through a relation written `b ⊲_z a`, which says that `b`
is below `a` and that everything `G` sees in `b` is bounded by what it sees in
any `c` between them, together with `z`.  The chain is

| | statement | here |
|---|---|---|
| 3.4 | `b ⊲_z a`, `G_u a < a`, `G_u z < b` ⟹ `G_u b < b` | not yet |
| 3.5 | `b₀ ⊲_z b` ⟹ `a + b₀ ⊲_z a + b` and `ψ_u(b₀) ⊲_z ψ_u(b)` | sum half done |
| 3.6 | `z ∈ dom a` ⟹ `a[z] ⊲_z a` | not yet |
| 3.3 | `a, z ∈ OT`, `z ∈ dom a` ⟹ `a[z] ∈ OT` | not yet |

3.4 is the one that does the work: it turns "bounded relative to `z`" into the
standard-form condition outright.  Its proof takes a subterm of `b` of minimal
length violating the condition and derives a contradiction.

This file has the vocabulary — concatenation, `G°`, the ordering on the lists
`G` returns, and `⊲` itself — and the sum half of 3.5.
-/

namespace Googology.Notation.ExBuchholz.Term

/-- Concatenation of terms, which is `+` on the ordinals they name. -/
def addT : Term → Term → Term
  | nil, y => y
  | cons a b t, y => cons a b (addT t y)

@[simp] theorem addT_nil_left (y : Term) : addT nil y = y := rfl
@[simp] theorem addT_cons (a b t y : Term) :
    addT (cons a b t) y = cons a b (addT t y) := rfl
@[simp] theorem addT_nil_right : ∀ x : Term, addT x nil = x
  | nil => rfl
  | cons a b t => by rw [addT_cons, addT_nil_right t]

theorem cons_eq_addT (a b t : Term) : cons a b t = addT (psi a b) t := rfl

theorem G_addT (u x y : Term) : G u (addT x y) = G u x ++ G u y := by
  induction x with
  | nil => simp [G]
  | cons a b t _ _ iht =>
    rw [addT_cons, G_cons, G_cons, iht, List.append_assoc]

/-- `G° u t` is `G u t` with `0` thrown in, as Buchholz writes it. -/
def G0 (u t : Term) : List Term := nil :: G u t

/-- `M ≼ M'`: every member of `M` is at most some member of `M'`. -/
def listLe (M M' : List Term) : Prop := ∀ x ∈ M, ∃ y ∈ M', x ≤ y

theorem listLe_refl (M : List Term) : listLe M M :=
  fun x hx => ⟨x, hx, le_refl x⟩

theorem listLe_append_left {M M' N : List Term} (h : listLe M M') :
    listLe M (M' ++ N) :=
  fun x hx => let ⟨y, hy, hle⟩ := h x hx; ⟨y, List.mem_append_left _ hy, hle⟩

theorem listLe_append_right {M N N' : List Term} (h : listLe M N') :
    listLe M (N ++ N') :=
  fun x hx => let ⟨y, hy, hle⟩ := h x hx; ⟨y, List.mem_append_right _ hy, hle⟩

theorem listLe_of_append {M M' N : List Term} (h₁ : listLe M N) (h₂ : listLe M' N) :
    listLe (M ++ M') N := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h₁ x hx
  · exact h₂ x hx

/-- Buchholz's `b ⊲_z a`: `b` is below `a`, and everything `G` sees in `b` is
bounded by what it sees in any `c` between them, together with `z`. -/
def Trian (z b a : Term) : Prop :=
  b < a ∧ ∀ u c : Term, b < c → c ≤ a → listLe (G u b) (G u c ++ G0 u z)

theorem Trian.lt {z b a : Term} (h : Trian z b a) : b < a := h.1

theorem addT_lt (a : Term) {x y : Term} (h : x < y) : addT a x < addT a y := by
  induction a with
  | nil => exact h
  | cons p q a' _ _ iha =>
    exact cons_lt_cons_iff.mpr (Or.inr ⟨rfl, iha⟩)

/-- Anything strictly between `a + b₀` and `a + b` is `a + c₀` for some `c₀`
strictly between. -/
theorem addT_between : ∀ a : Term, ∀ {b₀ b c : Term}, addT a b₀ < c → c ≤ addT a b →
    ∃ c₀, c = addT a c₀ ∧ b₀ < c₀ ∧ c₀ ≤ b := by
  intro a
  induction a with
  | nil => intro b₀ b c h₁ h₂; exact ⟨c, rfl, h₁, h₂⟩
  | cons p q a' _ _ iha =>
    intro b₀ b c h₁ h₂
    cases c with
    | nil => exact absurd h₁ (not_lt_nil _)
    | cons r s c' =>
      rcases cons_lt_cons_iff.mp h₁ with hlt | ⟨heq, hrest⟩
      · exfalso
        rcases le_iff_lt_or_eq.mp h₂ with h | h
        · rcases cons_lt_cons_iff.mp h with h' | ⟨h', _⟩
          · exact lt_irrefl _ (lt_trans hlt h')
          · rw [h'] at hlt; exact lt_irrefl _ hlt
        · injection h with h1 h2 _
          rw [h1, h2] at hlt
          exact lt_irrefl _ hlt
      · injection heq with e1 e2 _
        subst e1; subst e2
        have hc' : c' ≤ addT a' b := by
          rcases le_iff_lt_or_eq.mp h₂ with h | h
          · rcases cons_lt_cons_iff.mp h with h' | ⟨_, h'⟩
            · exact absurd h' (lt_irrefl _)
            · exact le_of_lt h'
          · injection h with _ _ e3
            exact e3 ▸ le_refl _
        obtain ⟨c₀, rfl, hb, hb'⟩ := iha hrest hc'
        exact ⟨c₀, rfl, hb, hb'⟩

/-- **Buchholz 3.5, the sum half.** -/
theorem Trian.addT_left (a : Term) {z b₀ b : Term} (h : Trian z b₀ b) :
    Trian z (addT a b₀) (addT a b) := by
  refine ⟨addT_lt a h.1, ?_⟩
  intro u c hlt hle
  obtain ⟨c₀, rfl, h1, h2⟩ := addT_between a hlt hle
  rw [G_addT, G_addT]
  refine listLe_of_append (listLe_append_left (listLe_append_left (listLe_refl _))) ?_
  intro x hx
  obtain ⟨y, hy, hle'⟩ := h.2 u c₀ h1 h2 x hx
  rcases List.mem_append.mp hy with hy | hy
  · exact ⟨y, List.mem_append_left _ (List.mem_append_right _ hy), hle'⟩
  · exact ⟨y, List.mem_append_right _ hy, hle'⟩

end Googology.Notation.ExBuchholz.Term
