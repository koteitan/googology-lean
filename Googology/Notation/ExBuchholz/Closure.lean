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
| 3.4 | `b ⊲_z a`, `G_u a < a`, `G_u z < b` ⟹ `G_u b < b` | **done** |
| 3.5 | `b₀ ⊲_z b` ⟹ `a + b₀ ⊲_z a + b` and `ψ_u(b₀) ⊲_z ψ_u(b)` | **done** |
| 3.6 | `z ∈ dom a` ⟹ `a[z] ⊲_z a` | pieces in place, not assembled |
| 3.3 | `a, z ∈ OT`, `z ∈ dom a` ⟹ `a[z] ∈ OT` | not yet |

3.4 is the one that does the work: it turns "bounded relative to `z`" into the
standard-form condition outright.  Buchholz argues by taking a subterm of `b`
of minimal length that violates the condition; here it is an induction on
`size`, whose conclusion is a disjunction — either the goal already holds, or
the condition holds at this subterm — which avoids needing a choice of minimal
element.

Each half of 3.5 rests on a decomposition lemma saying what a term strictly
between two others has to look like: `addT_between` for sums and `psi_between`
for collapses.
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

/-- Anything strictly between `ψ_u(b₀)` and `ψ_u(b)` has `ψ_u` at its head,
with an argument between. -/
theorem psi_between {u b₀ b c : Term} (h₁ : psi u b₀ < c) (h₂ : c ≤ psi u b) :
    ∃ c₀ c₁, c = cons u c₀ c₁ ∧ b₀ ≤ c₀ ∧ c₀ ≤ b := by
  cases c with
  | nil => exact absurd h₁ (not_lt_nil _)
  | cons r s c₁ =>
    have hle_rs : psi r s ≤ psi u b := by
      rcases le_iff_lt_or_eq.mp h₂ with hB | hB
      · rcases cons_lt_cons_iff.mp hB with hB' | ⟨_, hB''⟩
        · exact le_of_lt hB'
        · exact absurd hB'' (not_lt_nil _)
      · injection hB with e1 e2 _
        exact e1 ▸ e2 ▸ le_refl _
    rcases cons_lt_cons_iff.mp h₁ with hA | ⟨hA, _⟩
    · rcases psi_lt_psi_iff.mp hA with hlt1 | ⟨e1, hlt1⟩
      · exfalso
        rcases le_iff_lt_or_eq.mp hle_rs with h' | h'
        · rcases psi_lt_psi_iff.mp h' with h'' | ⟨e', _⟩
          · exact lt_irrefl u (lt_trans hlt1 h'')
          · exact lt_irrefl u (e' ▸ hlt1)
        · injection h' with e' _ _
          exact lt_irrefl u (e' ▸ hlt1)
      · subst e1
        refine ⟨s, c₁, rfl, le_of_lt hlt1, ?_⟩
        rcases le_iff_lt_or_eq.mp hle_rs with h' | h'
        · rcases psi_lt_psi_iff.mp h' with h'' | ⟨_, h''⟩
          · exact absurd h'' (lt_irrefl u)
          · exact le_of_lt h''
        · injection h' with _ e2 _
          exact e2 ▸ le_refl _
    · injection hA with e1 e2 _
      subst e1
      refine ⟨s, c₁, rfl, e2 ▸ le_refl _, ?_⟩
      rcases le_iff_lt_or_eq.mp hle_rs with h' | h'
      · rcases psi_lt_psi_iff.mp h' with h'' | ⟨_, h''⟩
        · exact absurd h'' (lt_irrefl u)
        · exact le_of_lt h''
      · injection h' with _ e2 _
        exact e2 ▸ le_refl _

theorem G_psi_of_le {v u b : Term} (h : v ≤ u) :
    G v (psi u b) = b :: (G v u ++ G v b) := by
  rw [psi, G_cons, if_pos h]
  simp [G]

theorem G_psi_of_not_le {v u b : Term} (h : ¬ v ≤ u) : G v (psi u b) = [] := by
  rw [psi, G_cons, if_neg h]
  simp [G]

/-- **Buchholz 3.5, the collapse half.** -/
theorem Trian.psi_left (u : Term) {z b₀ b : Term} (h : Trian z b₀ b) :
    Trian z (psi u b₀) (psi u b) := by
  refine ⟨psi_lt_psi_iff.mpr (Or.inr ⟨rfl, h.1⟩), ?_⟩
  intro v c hlt hle
  obtain ⟨c₀, c₁, rfl, hb0, hb1⟩ := psi_between hlt hle
  by_cases hvu : v ≤ u
  · rw [G_psi_of_le hvu, G_cons, if_pos hvu]
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨c₀, List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..)), hb0⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact ⟨x, List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_append_left _ hx))), le_refl x⟩
    · rcases le_iff_lt_or_eq.mp hb0 with hb | rfl
      · obtain ⟨y, hy, hle'⟩ := h.2 v c₀ hb hb1 x hx
        rcases List.mem_append.mp hy with hy | hy
        · exact ⟨y, List.mem_append_left _ (List.mem_append_left _
            (List.mem_cons_of_mem _ (List.mem_append_right _ hy))), hle'⟩
        · exact ⟨y, List.mem_append_right _ hy, hle'⟩
      · exact ⟨x, List.mem_append_left _ (List.mem_append_left _
          (List.mem_cons_of_mem _ (List.mem_append_right _ hx))), le_refl x⟩
  · rw [G_psi_of_not_le hvu]
    intro x hx; cases hx

/-! ## Buchholz 3.4 -/

theorem G0_lt {u z b : Term} (hz : ∀ x ∈ G u z, x < b) (hb : nil < b) :
    ∀ x ∈ G0 u z, x < b := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hb
  · exact hz x hx

/-- Step 1 of Buchholz 3.4: what `G` sees in `b` is bounded by `a`. -/
theorem G_lt_of_Trian {u z b a : Term} (hba : Trian z b a)
    (ha : ∀ x ∈ G u a, x < a) (hz : ∀ x ∈ G u z, x < b) :
    ∀ x ∈ G u b, x < a := by
  have hane : nil < a := by
    cases a with
    | nil => exact absurd hba.1 (not_lt_nil _)
    | cons _ _ _ => exact nil_lt_cons _ _ _
  have hbne : nil < b ∨ b = nil := by
    cases b with
    | nil => exact Or.inr rfl
    | cons _ _ _ => exact Or.inl (nil_lt_cons _ _ _)
  intro x hx
  obtain ⟨y, hy, hle⟩ := hba.2 u a hba.1 (le_refl a) x hx
  rcases List.mem_append.mp hy with hy | hy
  · exact lt_of_le_of_lt' hle (ha y hy)
  · rcases List.mem_cons.mp hy with rfl | hy
    · exact lt_of_le_of_lt' hle hane
    · rcases hbne with h | rfl
      · exact lt_of_le_of_lt' hle (lt_trans (hz y hy) hba.1)
      · exact absurd (hz y hy) (not_lt_nil _)

/-- **Buchholz 3.4.**  The relation `⊲` upgrades to the standard-form
condition outright. -/
theorem Trian.G_lt {u z b a : Term} (hba : Trian z b a)
    (ha : ∀ x ∈ G u a, x < a) (hz : ∀ x ∈ G u z, x < b) :
    ∀ x ∈ G u b, x < b := by
  have hstep1 := G_lt_of_Trian hba ha hz
  have key : ∀ n : Nat, ∀ d : Term, size d ≤ n → (∀ y ∈ G u d, y < a) →
      (∀ y ∈ G u b, y < b) ∨ (∀ y ∈ G u d, y < b) := by
    intro n
    induction n with
    | zero =>
      intro d hsz _
      cases d with
      | nil => exact Or.inr (fun y hy => absurd hy (List.not_mem_nil))
      | cons _ _ _ => simp only [size_cons] at hsz; omega
    | succ n ih =>
      intro d hsz hda
      cases d with
      | nil => exact Or.inr (fun y hy => absurd hy (List.not_mem_nil))
      | cons v c t =>
        simp only [size_cons] at hsz
        have hsub : ∀ w, (∀ y ∈ G u w, y ∈ G u (cons v c t)) → ∀ y ∈ G u w, y < a :=
          fun w hw y hy => hda y (hw y hy)
        have hGt : ∀ y ∈ G u t, y ∈ G u (cons v c t) := by
          intro y hy; rw [G_cons]; exact List.mem_append_right _ hy
        rcases ih t (by omega) (hsub t hGt) with h | ht
        · exact Or.inl h
        by_cases huv : u ≤ v
        · have hGv : ∀ y ∈ G u v, y ∈ G u (cons v c t) := by
            intro y hy; rw [G_cons, if_pos huv]
            exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_append_left _ hy))
          have hGc : ∀ y ∈ G u c, y ∈ G u (cons v c t) := by
            intro y hy; rw [G_cons, if_pos huv]
            exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_append_right _ hy))
          rcases ih v (by omega) (hsub v hGv) with h | hv
          · exact Or.inl h
          rcases ih c (by omega) (hsub c hGc) with h | hc
          · exact Or.inl h
          have hcmem : c ∈ G u (cons v c t) := by
            rw [G_cons, if_pos huv]; exact List.mem_append_left _ (List.mem_cons_self ..)
          have hca : c < a := hda c hcmem
          have hbne : nil < b ∨ b = nil := by
            cases b with
            | nil => exact Or.inr rfl
            | cons _ _ _ => exact Or.inl (nil_lt_cons _ _ _)
          rcases lt_trichotomy c b with hcb | rfl | hbc
          · refine Or.inr ?_
            intro y hy
            rw [G_cons, if_pos huv] at hy
            rcases List.mem_append.mp hy with hy | hy
            · rcases List.mem_cons.mp hy with rfl | hy
              · exact hcb
              rcases List.mem_append.mp hy with hy | hy
              · exact hv y hy
              · exact hc y hy
            · exact ht y hy
          · exact Or.inl hc
          · refine Or.inl ?_
            intro y hy
            obtain ⟨w, hw, hle⟩ := hba.2 u c hbc (le_of_lt hca) y hy
            rcases List.mem_append.mp hw with hw | hw
            · exact lt_of_le_of_lt' hle (hc w hw)
            · rcases hbne with hb0 | rfl
              · exact lt_of_le_of_lt' hle (G0_lt hz hb0 w hw)
              · exact absurd hy (List.not_mem_nil)
        · refine Or.inr ?_
          intro y hy
          rw [G_cons, if_neg huv] at hy
          exact ht y (by simpa using hy)
  rcases key (size b) b (Nat.le_refl _) hstep1 with h | h <;> exact h

/-! ## The pieces 3.6 is assembled from

3.6 follows `fs` branch by branch, and each branch needs one of these.

| branch of `fs` | what it needs |
|---|---|
| `X = 1`, the step is `0` | `Trian_nil` |
| `X = ψ_u(0)` with `u` a successor, the step is the index | `Trian_self` |
| `dom X₂ = 1`, the step is a repeated collapse | `Trian.of_nil`, `Trian.repeatPrin`, `Trian.psi_left` |
| `dom X₂` an `ω`-limit or below `X`, the step is inside the argument | `Trian.psi_left` |
| `X` a sum, the step is in the last summand | `Trian.addT_left` |

The branch not covered is the one where the index has to be rebuilt from the
subscript of `dom X₂`; Buchholz's case 4 computes `G` there by hand.
-/

/-- `0 ⊲_z a` for any nonzero `a`: `G` sees nothing in `0`. -/
theorem Trian_nil {z a : Term} (h : nil < a) : Trian z nil a :=
  ⟨h, fun _ _ _ _ x hx => absurd hx (List.not_mem_nil)⟩

/-- `z ⊲_z a` whenever `z < a`: what `G` sees in `z` is in `G° z` already. -/
theorem Trian_self {z a : Term} (h : z < a) : Trian z z a :=
  ⟨h, fun u _ _ _ x hx =>
    ⟨x, List.mem_append_right _ (List.mem_cons_of_mem _ hx), le_refl x⟩⟩

/-- `⊲_0` is the strongest of the family: `G° 0` sits inside every `G° z`. -/
theorem Trian.of_nil {z b a : Term} (h : Trian nil b a) : Trian z b a := by
  refine ⟨h.1, fun u c hlt hle x hx => ?_⟩
  obtain ⟨y, hy, hle'⟩ := h.2 u c hlt hle x hx
  rcases List.mem_append.mp hy with hy | hy
  · exact ⟨y, List.mem_append_left _ hy, hle'⟩
  · rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨nil, List.mem_append_right _ (List.mem_cons_self ..), hle'⟩
    · exact absurd hy (List.not_mem_nil)

theorem G_repeatPrin (u A B : Term) :
    ∀ k, ∀ y ∈ G u (repeatPrin A B k), y ∈ G u (psi A B)
  | 0 => fun y hy => absurd hy (List.not_mem_nil)
  | k + 1 => by
      intro y hy
      rw [show repeatPrin A B (k+1) = cons A B (repeatPrin A B k) from rfl, G_cons] at hy
      rcases List.mem_append.mp hy with hy | hy
      · rw [psi, G_cons]; exact List.mem_append_left _ hy
      · exact G_repeatPrin u A B k y hy

theorem cons_le_cons {a b t u : Term} (h : t ≤ u) : cons a b t ≤ cons a b u := by
  rcases le_iff_lt_or_eq.mp h with h | rfl
  · exact le_of_lt (cons_lt_cons_iff.mpr (Or.inr ⟨rfl, h⟩))
  · exact le_refl _

theorem psi_le_repeatPrin (A B : Term) :
    ∀ k, 0 < k → psi A B ≤ repeatPrin A B k
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | _ + 1, _ => cons_le_cons (nil_le _)

/-- A repeated collapse inherits `⊲` from one copy. -/
theorem Trian.repeatPrin {z A B a : Term} (h : Trian z (psi A B) a) :
    ∀ k, repeatPrin A B k < a → Trian z (repeatPrin A B k) a := by
  intro k hlt
  refine ⟨hlt, fun u c hc hca x hx => ?_⟩
  cases k with
  | zero => exact absurd hx (List.not_mem_nil)
  | succ k =>
    have hple : psi A B < c :=
      lt_of_le_of_lt' (psi_le_repeatPrin A B (k+1) (Nat.succ_pos k)) hc
    exact h.2 u c hple hca x (G_repeatPrin u A B (k+1) x hx)

end Googology.Notation.ExBuchholz.Term
