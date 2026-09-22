import Googology.Core
import Googology.Notation.ExBuchholz.Sum

/-!
# Fundamental sequences

Following p進大好きbot's article, the system carries two total recursive maps

```
dom : T → T          the shape of the limit a term is
[ ] : T × T → T      the fundamental sequence
```

`dom X` is `0` for zero, `X` itself when the sequence is indexed by the terms
below `X`, `1` for a successor, `ω` for an `ω`-limit, and otherwise the term
whose values index the sequence.

`dom` never calls `[ ]`, so it is an ordinary structural recursion and comes
first.

`[ ]` is the harder half: its recursion is not structural.  Three of its calls
shrink the term, one shrinks the index, and one reads the subscript out of
`dom X₂` — which `size_dom_le` keeps inside `X`.  The measure is therefore the
pair `(size X, size Y)`, ordered lexicographically.  The call that keeps `X`
fixed is guarded by `Y` being a numeral, and a numeral's predecessor is
structurally smaller, so that one decreases in the index.
-/

namespace Googology.Notation.ExBuchholz.Term

/-- `dom X` names the shape of the limit `X` is: `0` for a zero, `X` itself for
a successor-like collapse, `1` for a successor, `ω` for an `ω`-limit, and
otherwise the term whose values index the fundamental sequence.

It does not call `[ ]`, so it is an ordinary structural recursion. -/
def dom : Term → Term
  | nil => nil
  | cons X₁ X₂ nil =>
      if dom X₂ = nil then
        (if dom X₁ = nil then cons X₁ X₂ nil
         else if dom X₁ = t1 then cons X₁ X₂ nil
         else dom X₁)
      else if dom X₂ = t1 then tw
      else if dom X₂ = tw then tw
      else if dom X₂ < cons X₁ X₂ nil then dom X₂
      else tw
  | cons _ _ t => dom t

@[simp] theorem dom_nil : dom nil = nil := rfl

@[simp] theorem size_tw : size tw = 2 := rfl

set_option linter.unusedSimpArgs false in
/-- `dom` never grows a term. -/
theorem size_dom_le : ∀ X : Term, size (dom X) ≤ size X := by
  intro X
  induction X with
  | nil => simp [dom]
  | cons a b t iha ihb iht =>
    cases t with
    | cons c d u =>
      have h : dom (cons a b (cons c d u)) = dom (cons c d u) := rfl
      rw [h]; simp only [size_cons] at iht ⊢; omega
    | nil =>
      cases b with
      | nil =>
        rw [dom]
        split
        · split
          · simp only [size_cons, size_nil] <;> omega
          · split <;> simp only [size_cons, size_nil] <;> omega
        · exact absurd rfl ‹¬ dom nil = nil›
      | cons p q r =>
        simp only [size_cons] at ihb
        rw [dom]
        split
        · split
          · simp only [size_cons, size_nil] <;> omega
          · split <;> simp only [size_cons, size_nil] <;> omega
        · split
          · simp only [size_tw, size_cons, size_nil] <;> omega
          · split
            · simp only [size_tw, size_cons, size_nil] <;> omega
            · split <;> simp only [size_tw, size_cons, size_nil] <;> omega

@[simp] theorem dom_tw : dom tw = tw := rfl

/-- Only `0` has `dom` equal to `0`. -/
theorem dom_ne_nil : ∀ {W : Term}, W ≠ nil → dom W ≠ nil := by
  intro W
  induction W with
  | nil => intro h; exact absurd rfl h
  | cons a b t iha ihb iht =>
    intro _
    cases t with
    | cons c d u => exact iht (fun h => Term.noConfusion h)
    | nil =>
      rw [dom]
      split
      · split
        · exact fun h => Term.noConfusion h
        · split
          · exact fun h => Term.noConfusion h
          · assumption
      · split
        · exact fun h => Term.noConfusion h
        · split
          · exact fun h => Term.noConfusion h
          · split
            · assumption
            · exact fun h => Term.noConfusion h

theorem dom_eq_nil_iff {W : Term} : dom W = nil ↔ W = nil := by
  constructor
  · intro h
    cases W with
    | nil => rfl
    | cons a b t => exact absurd h (dom_ne_nil (fun hh => Term.noConfusion hh))
  · rintro rfl; rfl

/-- `dom W` is `0`, `ω`, or a principal term with argument `0`. -/
theorem dom_shape : ∀ W : Term,
    dom W = nil ∨ dom W = tw ∨ ∃ Z, dom W = cons Z nil nil := by
  intro W
  induction W with
  | nil => exact Or.inl rfl
  | cons a b t iha ihb iht =>
    cases t with
    | cons c d u => exact iht
    | nil =>
      rw [dom]
      split
      · split
        · next h1 _ =>
          exact Or.inr (Or.inr ⟨a, by rw [dom_eq_nil_iff.mp h1]⟩)
        · split
          · next h1 _ _ =>
            exact Or.inr (Or.inr ⟨a, by rw [dom_eq_nil_iff.mp h1]⟩)
          · exact iha
      · split
        · exact Or.inr (Or.inl rfl)
        · split
          · exact Or.inr (Or.inl rfl)
          · split
            · exact ihb
            · exact Or.inr (Or.inl rfl)

/-! ## Order facts the descent uses -/

theorem lt_of_lt_of_le' {x y z : Term} (h₁ : x < y) (h₂ : y ≤ z) : x < z := by
  rcases le_iff_lt_or_eq.mp h₂ with h | rfl
  · exact lt_trans h₁ h
  · exact h₁

theorem psi_le_cons (a b t : Term) : psi a b ≤ cons a b t := by
  cases t with
  | nil => exact le_refl _
  | cons c d r => exact le_of_lt (cons_lt_cons_iff.mpr (Or.inr ⟨rfl, nil_lt_cons _ _ _⟩))

/-- A principal standard form is above its own subscript. -/
theorem sub_lt_psi : ∀ a b : Term, OT (psi a b) → a < psi a b := by
  intro a
  induction a with
  | nil => intro b _; exact nil_lt_cons _ _ _
  | cons a₁ a₂ s ih1 _ _ =>
    intro b hOT
    refine cons_lt_cons_iff.mpr (Or.inl (psi_lt_psi_iff.mpr (Or.inl ?_)))
    exact lt_of_lt_of_le' (ih1 a₂ (OT_head (OT_fst hOT))) (psi_le_cons a₁ a₂ s)

/-- The tail of a standard form is below it. -/
theorem tail_lt : ∀ t a b : Term, OT (cons a b t) → t < cons a b t := by
  intro t
  induction t with
  | nil => intro a b _; exact nil_lt_cons _ _ _
  | cons c d s _ _ ihs =>
    intro a b hOT
    rcases le_iff_lt_or_eq.mp (OT_headLe_tail hOT) with h | h
    · exact cons_lt_cons_iff.mpr (Or.inl h)
    · exact cons_lt_cons_iff.mpr (Or.inr ⟨h, ihs c d (OT_tail hOT)⟩)

/-- `G` sees nothing in a standard form that does not reach its own level. -/
theorem G_eq_nil_of_le : ∀ X u : Term, OT X → X ≤ u → G u X = [] := by
  intro X
  induction X with
  | nil => intro u _ _; rfl
  | cons a b t _ _ iht =>
    intro u hOT hle
    have hau : ¬ u ≤ a :=
      not_le_of_lt (lt_of_lt_of_le'
        (lt_of_lt_of_le' (sub_lt_psi a b (OT_head hOT)) (psi_le_cons a b t)) hle)
    rw [G_cons, if_neg hau, List.nil_append]
    exact iht u (OT_tail hOT) (le_of_lt (lt_of_lt_of_le' (tail_lt t a b hOT) hle))

/-- A sum is below a principal term exactly when its head is. -/
theorem cons_lt_psi_iff {a b t c d : Term} :
    cons a b t < psi c d ↔ psi a b < psi c d := by
  rw [cons_lt_cons_iff]
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact h
    · exact absurd h (not_lt_nil t)
  · exact Or.inl

/-- Only `0` is below `1`. -/
theorem lt_one_iff {Y : Term} : Y < t1 ↔ Y = nil := by
  constructor
  · intro h
    cases Y with
    | nil => rfl
    | cons a b t =>
      rw [cons_lt_cons_iff] at h
      rcases h with h | ⟨_, h⟩
      · rcases psi_lt_psi_iff.mp h with h' | ⟨_, h'⟩
        · exact absurd h' (not_lt_nil _)
        · exact absurd h' (not_lt_nil _)
      · exact absurd h (not_lt_nil _)
  · rintro rfl; rfl

/-! ## The fundamental sequence -/

/-- The subscript of a principal term; `0` for `0`. -/
def subOf : Term → Term
  | nil => nil
  | cons Z _ _ => Z

theorem size_subOf_le (X : Term) : size (subOf X) ≤ size X := by
  cases X <;> simp [subOf, size_cons] <;> omega

/-- Is the term a numeral `1 + ⋯ + 1`? -/
def isNum : Term → Bool
  | nil => true
  | cons nil nil t => isNum t
  | _ => false

/-- The value of a numeral. -/
def numVal : Term → Nat
  | nil => 0
  | cons nil nil t => numVal t + 1
  | _ => 0

/-- One less, for a numeral. -/
def numPred : Term → Term
  | cons nil nil t => t
  | _ => nil

theorem size_numPred_lt {X : Term} (h : X ≠ nil) : size (numPred X) < size X := by
  cases X with
  | nil => exact absurd rfl h
  | cons a b t =>
    cases a with
    | nil =>
      cases b with
      | nil => simp [numPred, size_cons]
      | cons _ _ _ => simp [numPred, size_cons]
    | cons _ _ _ => simp [numPred, size_cons]

/-- `n` copies of the principal term `ψ_A(B)`, as a sum. -/
def repeatPrin (A B : Term) : Nat → Term
  | 0 => nil
  | k + 1 => cons A B (repeatPrin A B k)

/-- A repeated principal term stays below any principal term it is below. -/
theorem repeatPrin_lt {A B c d : Term} (h : psi A B < psi c d) :
    ∀ n, repeatPrin A B n < psi c d
  | 0 => nil_lt_cons c d nil
  | _ + 1 => cons_lt_psi_iff.mpr h

set_option linter.unusedVariables false in
/-- The fundamental sequence `X[Y]`, following the reference. -/
def fs : Term → Term → Term
  | nil, _ => nil
  | cons X₁ X₂ (cons c d u), Y => cons X₁ X₂ (fs (cons c d u) Y)
  | cons X₁ X₂ nil, Y =>
      if dom X₂ = nil then
        (if dom X₁ = nil then nil
         else if dom X₁ = t1 then Y
         else cons (fs X₁ Y) nil nil)
      else if dom X₂ = t1 then
        (if isNum Y then repeatPrin X₁ (fs X₂ nil) (numVal Y) else nil)
      else if dom X₂ = tw then
        cons X₁ (fs X₂ Y) nil
      else if dom X₂ < cons X₁ X₂ nil then
        cons X₁ (fs X₂ Y) nil
      else
        if h : Y ≠ nil ∧ isNum Y = true then
          (match fs (cons X₁ X₂ nil) (numPred Y) with
           | cons x₁' Γ nil =>
               if x₁' = X₁ then
                 cons X₁ (fs X₂ (cons (fs (subOf (dom X₂)) nil) Γ nil)) nil
               else cons X₁ (fs X₂ (cons (fs (subOf (dom X₂)) nil) nil nil)) nil
           | _ => cons X₁ (fs X₂ (cons (fs (subOf (dom X₂)) nil) nil nil)) nil)
        else cons X₁ (fs X₂ (cons (fs (subOf (dom X₂)) nil) nil nil)) nil
termination_by X Y => (size X, size Y)
decreasing_by
  all_goals first
    | exact Prod.Lex.left _ _ (by simp only [size_cons]; omega)
    | exact Prod.Lex.left _ _ (by
        have h1 := size_subOf_le (dom X₂)
        have h2 := size_dom_le X₂
        simp only [size_cons]
        omega)
    | exact Prod.Lex.right _ (size_numPred_lt h.1)

#guard numVal t2 = 2
#guard isNum t2
#guard !isNum tw
#guard numPred t2 = t1
#guard repeatPrin nil nil 2 = t2

/-! ### Fundamental sequences, checked against known values -/

/-- `3` as a term. -/
abbrev t3 : Term := cons nil nil t2
/-- `ε₀ = ψ_0(Ω)`. -/
abbrev te : Term := psi nil tW
/-- `ω^ω = ψ_0(ω)`. -/
abbrev tww : Term := psi nil tw

#guard fs t0 t3 = t0            -- 0[n] = 0
#guard fs t1 t0 = t0            -- 1[0] = 0
#guard fs t2 t0 = t1            -- 2[0] = 1
#guard fs t3 t0 = t2            -- 3[0] = 2
#guard fs tw t0 = t0            -- ω[0] = 0
#guard fs tw t1 = t1            -- ω[1] = 1
#guard fs tw t2 = t2            -- ω[2] = 2
#guard fs tw t3 = t3            -- ω[3] = 3
#guard fs tW t2 = t2            -- Ω[Y] = Y
#guard fs tW tw = tw
#guard fs tww t2 = psi nil t2   -- (ω^ω)[2] = ω^2
#guard fs te t0 = tw            -- ε₀[0] = ω
#guard fs te t1 = tww           -- ε₀[1] = ω^ω
#guard fs te t2 = psi nil tww   -- ε₀[2] = ω^(ω^ω)

/-! ### Sanity checks against the reference -/

#guard dom t0 = t0                    -- 0
#guard dom t1 = t1                    -- 1 is a successor
#guard dom t2 = t1                    -- so is 2
#guard dom tw = tw                    -- ω is its own index
#guard dom tW = tW                    -- Ω is indexed by the terms below it
#guard dom (psi nil tW) = tw          -- ε₀ has cofinality ω
#guard dom (psi nil (psi nil tW)) = tw

/-! ## The fundamental sequence descends -/

set_option linter.unusedVariables false in
theorem fs_lt_aux : ∀ n : Nat, ∀ X Y : Term, size X ≤ n → Y < dom X → fs X Y < X := by
  intro n
  induction n with
  | zero =>
    intro X Y hsz hY
    cases X with
    | nil => exact absurd hY (not_lt_nil Y)
    | cons a b t => simp only [size_cons] at hsz; omega
  | succ n ih =>
  intro X Y hsz hY
  cases X with
  | nil => exact absurd hY (not_lt_nil Y)
  | cons X₁ X₂ t =>
    cases t with
    | cons c d u =>
      simp only [size_cons] at hsz
      have hd : dom (cons X₁ X₂ (cons c d u)) = dom (cons c d u) := rfl
      rw [hd] at hY
      have hlt := ih (cons c d u) Y (by simp only [size_cons]; omega) hY
      show fs (cons X₁ X₂ (cons c d u)) Y < cons X₁ X₂ (cons c d u)
      rw [fs]
      exact cons_lt_cons_iff.mpr (Or.inr ⟨rfl, hlt⟩)
    | nil =>
      simp only [size_cons] at hsz
      rw [fs]
      split
      · rename_i h1
        subst_vars
        have hX₂ : X₂ = nil := dom_eq_nil_iff.mp h1
        subst hX₂
        split
        · exact nil_lt_cons _ _ _
        · split
          · rename_i h2 h3
            have hd : dom (cons X₁ nil nil) = cons X₁ nil nil := by rw [dom]; simp_all
            rw [hd] at hY
            exact hY
          · rename_i h2 h3
            have hd : dom (cons X₁ nil nil) = dom X₁ := by rw [dom]; simp_all
            rw [hd] at hY
            have hlt := ih X₁ Y (by omega) hY
            exact cons_lt_cons_iff.mpr (Or.inl (psi_lt_psi_iff.mpr (Or.inl hlt)))
      · rename_i h1
        split
        · rename_i h2
          have hfs : fs X₂ nil < X₂ := by
            refine ih X₂ nil (by omega) ?_
            rw [h2]; exact nil_lt_cons _ _ _
          split
          · exact repeatPrin_lt (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, hfs⟩)) _
          · exact nil_lt_cons _ _ _
        · rename_i h2
          split
          · rename_i h3
            have hd : dom (cons X₁ X₂ nil) = tw := by rw [dom]; simp_all
            rw [hd] at hY
            rw [← h3] at hY
            have hlt := ih X₂ Y (by omega) hY
            exact cons_lt_cons_iff.mpr (Or.inl (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, hlt⟩)))
          · rename_i h3
            split
            · rename_i h4
              have hd : dom (cons X₁ X₂ nil) = dom X₂ := by rw [dom]; simp_all
              rw [hd] at hY
              have hlt := ih X₂ Y (by omega) hY
              exact cons_lt_cons_iff.mpr (Or.inl (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, hlt⟩)))
            · rename_i h4
              -- dom X₂ = cons Z nil nil with Z ≠ nil
              obtain ⟨Z, hZ⟩ : ∃ Z, dom X₂ = cons Z nil nil := by
                rcases dom_shape X₂ with h | h | h
                · exact absurd h h1
                · exact absurd h h3
                · exact h
              have hZne : Z ≠ nil := by
                intro hz; subst hz; exact h2 hZ
              have hZs : size Z < size X₂ := by
                have h5 := size_dom_le X₂
                rw [hZ] at h5; simp only [size_cons, size_nil] at h5; omega
              have hz0 : fs Z nil < Z := by
                refine ih Z nil (by omega) ?_
                have := dom_ne_nil hZne
                cases hd : dom Z with
                | nil => exact absurd hd this
                | cons _ _ _ => exact nil_lt_cons _ _ _
              have hsub : subOf (dom X₂) = Z := by rw [hZ]; rfl
              have key : ∀ Γ : Term,
                  fs X₂ (cons (fs (subOf (dom X₂)) nil) Γ nil) < X₂ := by
                intro Γ
                refine ih X₂ _ (by omega) ?_
                rw [hsub, hZ]
                exact psi_lt_psi_iff.mpr (Or.inl hz0)
              split
              · split
                · split
                  · exact cons_lt_cons_iff.mpr
                      (Or.inl (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, key _⟩)))
                  · exact cons_lt_cons_iff.mpr
                      (Or.inl (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, key _⟩)))
                · exact cons_lt_cons_iff.mpr
                    (Or.inl (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, key _⟩)))
              · exact cons_lt_cons_iff.mpr
                  (Or.inl (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, key _⟩)))

/-- **The fundamental sequence descends.** -/
theorem fs_lt {X Y : Term} (h : Y < dom X) : fs X Y < X :=
  fs_lt_aux (size X) X Y (Nat.le_refl _) h

/-! ## Below Ω: successors and ω-limits -/

/-- The numeral `n`, as a term. -/
def numeral (n : Nat) : Term := repeatPrin nil nil n

#guard numeral 0 = t0
#guard numeral 3 = t3


/-- A term below `Ω` has `0` as its leading subscript. -/
theorem sub_eq_nil_of_lt_tW {a b t : Term} (h : cons a b t < tW) : a = nil := by
  rcases cons_lt_cons_iff.mp h with h1 | ⟨_, h1⟩
  · rcases psi_lt_psi_iff.mp h1 with h2 | ⟨_, h2⟩
    · exact lt_one_iff.mp h2
    · exact absurd h2 (not_lt_nil _)
  · exact absurd h1 (not_lt_nil _)

/-- **Below `Ω`, a standard form other than `0` is a successor or an
`ω`-limit.** -/
theorem dom_eq_one_or_tw : ∀ X : Term, OT X → X < tW → X ≠ nil →
    dom X = t1 ∨ dom X = tw := by
  intro X
  induction X with
  | nil => intro _ _ h; exact absurd rfl h
  | cons a b t _ _ iht =>
    intro hOT hlt _
    cases t with
    | cons c d u =>
      have hhead : psi c d ≤ psi a b := OT_tail_head_le hOT
      have hab : psi a b < psi t1 nil := by
        rcases cons_lt_cons_iff.mp hlt with h1 | ⟨_, h1⟩
        · exact h1
        · exact absurd h1 (not_lt_nil _)
      refine iht (OT_tail hOT) ?_ (fun h => Term.noConfusion h)
      exact cons_lt_cons_iff.mpr (Or.inl (lt_of_le_of_lt' hhead hab))
    | nil =>
      have ha : a = nil := sub_eq_nil_of_lt_tW hlt
      subst ha
      rw [dom]
      split
      · rename_i h1
        have hb : b = nil := dom_eq_nil_iff.mp h1
        subst hb
        exact Or.inl rfl
      · rename_i h1
        split
        · exact Or.inr rfl
        · rename_i h2
          split
          · exact Or.inr rfl
          · rename_i h3
            split
            · rename_i h4
              exfalso
              obtain ⟨Z, hZ⟩ : ∃ Z, dom b = cons Z nil nil := by
                rcases dom_shape b with h | h | h
                · exact absurd h h1
                · exact absurd h h3
                · exact h
              rw [hZ] at h4
              rcases psi_lt_psi_iff.mp h4 with h5 | ⟨h5, _⟩
              · exact absurd h5 (not_lt_nil _)
              · exact h2 (by rw [hZ, h5])
            · exact Or.inr rfl

theorem numeral_lt_tw (n : Nat) : numeral n < tw := by
  cases n with
  | zero => exact nil_lt_cons _ _ _
  | succ k =>
    show cons nil nil (numeral k) < cons nil t1 nil
    exact cons_lt_cons_iff.mpr (Or.inl (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, nil_lt_cons _ _ _⟩)))

/-- The index to expand at: `0` at a successor, the numeral `n` otherwise. -/
def idx (X : Term) (n : Nat) : Term := if dom X = t1 then nil else numeral n

theorem idx_lt_dom {X : Term} (hOT : OT X) (hlt : X < tW) (hne : X ≠ nil) (n : Nat) :
    idx X n < dom X := by
  rcases dom_eq_one_or_tw X hOT hlt hne with h | h
  · rw [idx, if_pos h, h]; exact nil_lt_cons _ _ _
  · have hne' : dom X ≠ t1 := by rw [h]; decide
    rw [idx, if_neg hne', h]
    exact numeral_lt_tw n

/-- **One expansion step strictly decreases a countable standard form.** -/
theorem step_lt {X : Term} (hOT : OT X) (hlt : X < tW) (hne : X ≠ nil) (n : Nat) :
    fs X (idx X n) < X :=
  fs_lt (idx_lt_dom hOT hlt hne n)

/-! ## Towards closure

`step_lt` says the step decreases.  What is still missing for `exb.WF` is that
it keeps a term standard.  The sum branch of that is below, together with the
facts about `G` the other branches will read.  The branch that is not here is
the one for a collapse at a limit, and it needs a substitution lemma for `G`:
from `G a b < b`, conclude `G a (b[W]) < b[W]`.  That does not follow from the
inequality alone, since `b[W] < b`; it has to be read off the shape of `b[W]`,
which is why Buchholz states it separately.
-/

/-- A larger subscript collects less: `G` is antitone in its first argument. -/
theorem G_subset_of_le {a a' : Term} (h : a ≤ a') :
    ∀ t : Term, ∀ z ∈ G a' t, z ∈ G a t := by
  intro t
  induction t with
  | nil => intro z hz; cases hz
  | cons c d r ihc ihd ihr =>
    intro z hz
    rw [G_cons] at hz ⊢
    rcases List.mem_append.mp hz with hz | hz
    · refine List.mem_append_left _ ?_
      split at hz
      · next hac =>
        rw [if_pos (le_trans h hac)]
        rcases List.mem_cons.mp hz with rfl | hz
        · exact List.mem_cons_self ..
        refine List.mem_cons_of_mem _ ?_
        rcases List.mem_append.mp hz with hz | hz
        · exact List.mem_append_left _ (ihc z hz)
        · exact List.mem_append_right _ (ihd z hz)
      · cases hz
    · exact List.mem_append_right _ (ihr z hz)

/-- Standardness of a collapse is inherited by any larger subscript. -/
theorem OT_psi_of_le {a a' b : Term} (h : a ≤ a') (hOT : OT (psi a b))
    (ha' : OT a') : OT (psi a' b) := by
  have hb : OT b := OT_snd hOT
  have hG : ∀ z ∈ G a b, z < b := OT_G_lt hOT
  simp only [OT, isOT, descHead, head?, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq]
  exact ⟨⟨⟨⟨ha', hb⟩, fun z hz => hG z (G_subset_of_le h b z hz)⟩, trivial⟩, trivial⟩

theorem descHead_of_headLe {a b t : Term} (h : HeadLe (psi a b) t) :
    descHead a b t = true := by
  cases t with
  | nil => rfl
  | cons c d u => exact decide_eq_true h

/-- Expanding a tail keeps it below the head. -/
theorem headLe_fs {p t Y : Term} (h : HeadLe p t) (hY : Y < dom t) :
    HeadLe p (fs t Y) :=
  headLe_of_lt h (fs_lt hY)

/-- **The sum branch of the closure**: expanding the tail of a standard form
keeps it standard, granting that the tail stays standard. -/
theorem OT_cons_fs {X₁ X₂ t Y : Term} (hOT : OT (cons X₁ X₂ t))
    (ht : OT (fs t Y)) (hY : Y < dom t) : OT (cons X₁ X₂ (fs t Y)) := by
  simp only [OT, isOT, Bool.and_eq_true] at hOT ⊢
  exact ⟨⟨hOT.1.1, ht⟩,
    descHead_of_headLe (headLe_fs (OT_headLe_tail (by
      simp only [OT, isOT, Bool.and_eq_true]; exact hOT)) hY)⟩

/-- A numeral is the numeral of its value. -/
theorem eq_numeral_numVal : ∀ Y : Term, isNum Y = true → Y = numeral (numVal Y) := by
  intro Y
  induction Y with
  | nil => intro _; rfl
  | cons a b t _ _ iht =>
    intro h
    cases a with
    | cons _ _ _ => simp [isNum] at h
    | nil =>
      cases b with
      | cons _ _ _ => simp [isNum] at h
      | nil =>
        have ht : isNum t = true := h
        show cons nil nil t = numeral (numVal t + 1)
        rw [show numeral (numVal t + 1) = cons nil nil (numeral (numVal t)) from rfl, ← iht ht]

/-- A standard form below `ω` is a numeral. -/
theorem eq_numeral_of_lt_tw : ∀ {Y : Term}, OT Y → Y < tw → ∃ n : Nat, Y = numeral n := by
  intro Y
  induction Y with
  | nil => intro _ _; exact ⟨0, rfl⟩
  | cons a b t _ _ iht =>
    intro hOT hlt
    have hab : psi a b < psi nil t1 := by
      rcases cons_lt_cons_iff.mp hlt with h | ⟨_, h⟩
      · exact h
      · exact absurd h (not_lt_nil t)
    have ha : a = nil := by
      rcases psi_lt_psi_iff.mp hab with h | ⟨h, _⟩
      · exact absurd h (not_lt_nil a)
      · exact h
    have hb : b = nil := by
      rcases psi_lt_psi_iff.mp hab with h | ⟨_, h⟩
      · exact absurd h (not_lt_nil a)
      · exact lt_one_iff.mp h
    subst ha; subst hb
    have hhead : HeadLe (psi nil nil) t := OT_headLe_tail hOT
    have ht : t < tw := by
      cases t with
      | nil => exact nil_lt_cons _ _ _
      | cons c d s =>
        have : psi c d ≤ psi nil nil := hhead
        exact cons_lt_psi_iff.mpr
          (lt_of_le_of_lt' this (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, nil_lt_cons _ _ _⟩)))
    obtain ⟨k, hk⟩ := iht (OT_tail hOT) ht
    exact ⟨k + 1, by rw [hk]; rfl⟩

/-- `dom` stays inside `OT`: it is built from subterms of a standard form. -/
theorem OT_dom : ∀ {X : Term}, OT X → OT (dom X) := by
  intro X
  induction X with
  | nil => intro _; exact rfl
  | cons X₁ X₂ t ih1 ih2 iht =>
    intro hOT
    cases t with
    | cons c d u =>
      show OT (dom (cons c d u))
      exact iht (OT_tail hOT)
    | nil =>
      rw [dom]
      split
      · rename_i h1
        have hX₂ : X₂ = nil := dom_eq_nil_iff.mp h1
        subst hX₂
        split
        · exact hOT
        · split
          · exact hOT
          · exact ih1 (OT_fst hOT)
      · split
        · decide
        · split
          · decide
          · split
            · exact ih2 (OT_snd hOT)
            · decide

/-! ## Monotonicity in the index, and the tower of Buchholz's case 4 -/

theorem fs_mono_aux : ∀ n : Nat, ∀ X Y₁ Y₂ : Term, size X ≤ n →
    dom X ≠ nil → dom X ≠ t1 → dom X ≠ tw →
    Y₁ < Y₂ → fs X Y₁ < fs X Y₂ := by
  intro n
  induction n with
  | zero =>
    intro X Y₁ Y₂ hsz h0 _ _ _
    cases X with
    | nil => exact absurd rfl h0
    | cons a b t => simp only [size_cons] at hsz; omega
  | succ n ih =>
  intro X Y₁ Y₂ hsz h0 h1 hw hY
  cases X with
  | nil => exact absurd rfl h0
  | cons X₁ X₂ t =>
    cases t with
    | cons c d u =>
      simp only [size_cons] at hsz
      have hd : dom (cons X₁ X₂ (cons c d u)) = dom (cons c d u) := rfl
      rw [hd] at h0 h1 hw
      have hlt := ih (cons c d u) Y₁ Y₂ (by simp only [size_cons]; omega) h0 h1 hw hY
      show fs (cons X₁ X₂ (cons c d u)) Y₁ < fs (cons X₁ X₂ (cons c d u)) Y₂
      rw [fs, fs]
      exact cons_lt_cons_iff.mpr (Or.inr ⟨rfl, hlt⟩)
    | nil =>
      simp only [size_cons] at hsz
      by_cases e1 : dom X₂ = nil
      · have hX₂ : X₂ = nil := dom_eq_nil_iff.mp e1
        subst hX₂
        by_cases g1 : dom X₁ = nil
        · have hX₁ : X₁ = nil := dom_eq_nil_iff.mp g1
          subst hX₁
          exact absurd (by rw [dom]; simp_all) h1
        · by_cases g2 : dom X₁ = t1
          · have e₁ : fs (cons X₁ nil nil) Y₁ = Y₁ := by rw [fs]; simp_all
            have e₂ : fs (cons X₁ nil nil) Y₂ = Y₂ := by rw [fs]; simp_all
            rw [e₁, e₂]; exact hY
          · have hd : dom (cons X₁ nil nil) = dom X₁ := by rw [dom]; simp_all
            rw [hd] at hw
            have e₁ : fs (cons X₁ nil nil) Y₁ = psi (fs X₁ Y₁) nil := by rw [fs]; simp_all
            have e₂ : fs (cons X₁ nil nil) Y₂ = psi (fs X₁ Y₂) nil := by rw [fs]; simp_all
            rw [e₁, e₂]
            exact psi_lt_psi_iff.mpr (Or.inl (ih X₁ Y₁ Y₂ (by omega) g1 g2 hw hY))
      · by_cases e2 : dom X₂ = t1
        · exact absurd (by rw [dom]; simp_all) hw
        · by_cases e3 : dom X₂ = tw
          · exact absurd (by rw [dom]; simp_all) hw
          · by_cases e4 : dom X₂ < cons X₁ X₂ nil
            · have hd : dom (cons X₁ X₂ nil) = dom X₂ := by rw [dom]; simp_all
              rw [hd] at hw
              have f₁ : fs (cons X₁ X₂ nil) Y₁ = psi X₁ (fs X₂ Y₁) := by rw [fs]; simp_all
              have f₂ : fs (cons X₁ X₂ nil) Y₂ = psi X₁ (fs X₂ Y₂) := by rw [fs]; simp_all
              rw [f₁, f₂]
              exact psi_lt_psi_iff.mpr
                (Or.inr ⟨rfl, ih X₂ Y₁ Y₂ (by omega) e1 e2 hw hY⟩)
            · exact absurd (by rw [dom]; simp_all) hw

/-- **Buchholz 3.2(b)**: where the domain is indexed by terms — that is, where
it is neither `0`, nor `1`, nor `ω` — the fundamental sequence is strictly
increasing in its index. -/
theorem fs_mono {X Y₁ Y₂ : Term}
    (h0 : dom X ≠ nil) (h1 : dom X ≠ t1) (hw : dom X ≠ tw) (hY : Y₁ < Y₂) :
    fs X Y₁ < fs X Y₂ :=
  fs_mono_aux (size X) X Y₁ Y₂ (Nat.le_refl _) h0 h1 hw hY

/-- On a domain indexed by terms, a nonzero index gives a nonzero value. -/
theorem fs_ne_nil {X Y : Term}
    (h0 : dom X ≠ nil) (h1 : dom X ≠ t1) (hw : dom X ≠ tw) (hY : Y ≠ nil) :
    fs X Y ≠ nil := by
  cases X with
  | nil => exact absurd rfl h0
  | cons X₁ X₂ t =>
    cases t with
    | cons c d u =>
      show fs (cons X₁ X₂ (cons c d u)) Y ≠ nil
      rw [fs]; exact fun h => Term.noConfusion h
    | nil =>
      by_cases e1 : dom X₂ = nil
      · have hX₂ : X₂ = nil := dom_eq_nil_iff.mp e1
        subst hX₂
        by_cases g1 : dom X₁ = nil
        · have hX₁ : X₁ = nil := dom_eq_nil_iff.mp g1
          subst hX₁
          exact absurd (by rw [dom]; simp_all) h1
        · by_cases g2 : dom X₁ = t1
          · have he : fs (cons X₁ nil nil) Y = Y := by rw [fs]; simp_all
            rw [he]; exact hY
          · have he : fs (cons X₁ nil nil) Y = psi (fs X₁ Y) nil := by rw [fs]; simp_all
            rw [he]; exact fun h => Term.noConfusion h
      · by_cases e2 : dom X₂ = t1
        · exact absurd (by rw [dom]; simp_all) hw
        · by_cases e3 : dom X₂ = tw
          · exact absurd (by rw [dom]; simp_all) hw
          · by_cases e4 : dom X₂ < cons X₁ X₂ nil
            · have he : fs (cons X₁ X₂ nil) Y = psi X₁ (fs X₂ Y) := by rw [fs]; simp_all
              rw [he]; exact fun h => Term.noConfusion h
            · exact absurd (by rw [dom]; simp_all) hw

/-- In the configuration of Buchholz's case 4 the domain is a collapse
`ψ_Z(0)` with `Z ≠ 0`, so `Z` has a fundamental sequence of its own and
`Z[0] < Z`. -/
theorem subOf_dom_ne_nil {W : Term} (h0 : dom W ≠ nil) (h1 : dom W ≠ t1)
    (hw : dom W ≠ tw) : subOf (dom W) ≠ nil := by
  intro hZ
  rcases dom_shape W with h | h | ⟨A, h⟩
  · exact absurd h h0
  · exact absurd h hw
  · rw [h] at hZ; simp only [subOf] at hZ; subst hZ; exact absurd h h1

theorem subOf_fs_lt {W : Term} (h0 : dom W ≠ nil) (h1 : dom W ≠ t1)
    (hw : dom W ≠ tw) : fs (subOf (dom W)) nil < subOf (dom W) :=
  fs_lt (lt_of_le_of_ne (nil_le _)
    (fun h => dom_ne_nil (subOf_dom_ne_nil h0 h1 hw) h.symm))

theorem isNum_numeral : ∀ n : Nat, isNum (numeral n) = true
  | 0 => rfl
  | k + 1 => isNum_numeral k

/-- The tower of indices Buchholz's case 4 runs through: `W₀ = ψ_{Z₀}(0)` and
`W_{i+1} = ψ_{Z₀}(B[W_i])`, where `Z₀ = Z[0]` for `dom B = ψ_Z(0)`. -/
def tower (Z₀ B : Term) : Nat → Term
  | 0 => psi Z₀ nil
  | i + 1 => psi Z₀ (fs B (tower Z₀ B i))

/-- In the configuration of case 4, expanding at the numeral `n` runs the
tower `n` times: `(ψ_{X₁}(X₂))[n̲] = ψ_{X₁}(X₂[W_n])`. -/
theorem fs_numeral {X₁ X₂ : Term}
    (e1 : dom X₂ ≠ nil) (e2 : dom X₂ ≠ t1) (e3 : dom X₂ ≠ tw)
    (e4 : ¬ (dom X₂ < cons X₁ X₂ nil)) : ∀ n : Nat,
    fs (cons X₁ X₂ nil) (numeral n)
      = psi X₁ (fs X₂ (tower (fs (subOf (dom X₂)) nil) X₂ n)) := by
  intro n
  induction n with
  | zero =>
    rw [fs]
    simp only [if_neg e1, if_neg e2, if_neg e3, if_neg e4]
    rw [dif_neg (by intro h; exact h.1 rfl)]
    rfl
  | succ k ihk =>
    have hc : (numeral (k + 1)) ≠ nil ∧ isNum (numeral (k + 1)) = true :=
      ⟨fun h => Term.noConfusion h, isNum_numeral (k + 1)⟩
    rw [fs]
    simp only [if_neg e1, if_neg e2, if_neg e3, if_neg e4, dif_pos hc]
    rw [show numPred (numeral (k + 1)) = numeral k from rfl, ihk]
    simp only [psi, if_true]
    rfl

/-- The tower climbs. -/
theorem tower_lt {Z₀ B : Term} (e1 : dom B ≠ nil) (e2 : dom B ≠ t1) (e3 : dom B ≠ tw) :
    ∀ i : Nat, tower Z₀ B i < tower Z₀ B (i + 1) := by
  intro i
  induction i with
  | zero =>
    show psi Z₀ nil < psi Z₀ (fs B (tower Z₀ B 0))
    refine psi_lt_psi_iff.mpr (Or.inr ⟨rfl, ?_⟩)
    exact lt_of_le_of_ne (nil_le _)
      (fun h => fs_ne_nil e1 e2 e3 (fun h' => Term.noConfusion h') h.symm)
  | succ k ihk =>
    show psi Z₀ (fs B (tower Z₀ B k)) < psi Z₀ (fs B (tower Z₀ B (k + 1)))
    exact psi_lt_psi_iff.mpr (Or.inr ⟨rfl, fs_mono e1 e2 e3 ihk⟩)

/-- So do the values it produces. -/
theorem tower_val_lt {Z₀ B : Term} (e1 : dom B ≠ nil) (e2 : dom B ≠ t1)
    (e3 : dom B ≠ tw) (i : Nat) :
    fs B (tower Z₀ B i) < fs B (tower Z₀ B (i + 1)) :=
  fs_mono e1 e2 e3 (tower_lt e1 e2 e3 i)

theorem tower_val_le_zero {Z₀ B : Term} (e1 : dom B ≠ nil) (e2 : dom B ≠ t1)
    (e3 : dom B ≠ tw) : ∀ i : Nat, fs B (tower Z₀ B 0) ≤ fs B (tower Z₀ B i)
  | 0 => le_refl _
  | i + 1 => le_trans (tower_val_le_zero e1 e2 e3 i)
      (le_of_lt (tower_val_lt e1 e2 e3 i))

/-- Every rung of the tower is an admissible index for `B`. -/
theorem tower_lt_dom {B : Term} (e1 : dom B ≠ nil) (e2 : dom B ≠ t1)
    (e3 : dom B ≠ tw) : ∀ i : Nat, tower (fs (subOf (dom B)) nil) B i < dom B := by
  have hlt : fs (subOf (dom B)) nil < subOf (dom B) := subOf_fs_lt e1 e2 e3
  intro i
  rcases dom_shape B with h | h | ⟨Z, h⟩
  · exact absurd h e1
  · exact absurd h e3
  · have hZ : subOf (dom B) = Z := by rw [h]; rfl
    rw [hZ] at hlt
    rw [h]
    cases i with
    | zero => exact psi_lt_psi_iff.mpr (Or.inl hlt)
    | succ k => exact psi_lt_psi_iff.mpr (Or.inl hlt)

theorem OT_psi_nil {a : Term} (h : OT a) : OT (psi a nil) :=
  OT_psi_of_le (nil_le a) (by decide) h

/-- The tower's first index is an admissible index. -/
theorem W0_lt_dom {X : Term} (h0 : dom X ≠ nil) (h1 : dom X ≠ t1) (hw : dom X ≠ tw) :
    psi (fs (subOf (dom X)) nil) nil < dom X := by
  rcases dom_shape X with h | h | ⟨Z, h⟩
  · exact absurd h h0
  · exact absurd h hw
  · have hlt := subOf_fs_lt h0 h1 hw
    rw [h] at hlt ⊢
    simp only [subOf] at hlt ⊢
    exact psi_lt_psi_iff.mpr (Or.inl hlt)

/-- The subscript of `dom X` is a standard form. -/
theorem OT_subOf_dom {X : Term} (hOT : OT X) (h0 : dom X ≠ nil) (hw : dom X ≠ tw) :
    OT (subOf (dom X)) := by
  rcases dom_shape X with h | h | ⟨Z, h⟩
  · exact absurd h h0
  · exact absurd h hw
  · have hz := OT_dom hOT
    rw [h] at hz ⊢
    simp only [subOf] at hz ⊢
    exact OT_fst hz

/-- The standard-form condition for a principal term, as a constructor. -/
theorem OT_psi_of {a b : Term} (ha : OT a) (hb : OT b)
    (hG : ∀ x ∈ G a b, x < b) : OT (psi a b) := by
  have h1 : (G a b).all (fun x => decide (x < b)) = true :=
    List.all_eq_true.mpr (fun x hx => decide_eq_true (hG x hx))
  show isOT (cons a b nil) = true
  rw [isOT]
  simp only [h1, Bool.and_true, Bool.true_and, descHead, head?, isOT]
  rw [show isOT a = true from ha, show isOT b = true from hb]
  rfl

/-- A finite repeat of a principal standard form is standard. -/
theorem OT_repeatPrin {a b : Term} (h : OT (psi a b)) :
    ∀ k : Nat, OT (repeatPrin a b k)
  | 0 => rfl
  | k + 1 => by
    have ih : isOT (repeatPrin a b k) = true := OT_repeatPrin h k
    have hG : (G a b).all (fun x => decide (x < b)) = true :=
      List.all_eq_true.mpr (fun x hx => decide_eq_true (OT_G_lt h x hx))
    have ha : isOT a = true := OT_fst h
    have hb : isOT b = true := OT_snd h
    show isOT (cons a b (repeatPrin a b k)) = true
    rw [isOT]
    have hd : descHead a b (repeatPrin a b k) = true := by
      cases k with
      | zero => rfl
      | succ j => simp [repeatPrin, descHead, head?, le_refl]
    simp only [ha, hb, hG, hd, ih, Bool.and_true, Bool.true_and]

/-- The subscript of `dom X` is strictly smaller than `X`. -/
theorem size_subOf_dom_lt {X : Term} (h0 : dom X ≠ nil) :
    size (subOf (dom X)) < size X := by
  have hX : X ≠ nil := fun h => h0 (by rw [h]; rfl)
  have hle := size_dom_le X
  rcases dom_shape X with h | h | ⟨Z, h⟩
  · exact absurd h h0
  · rw [h]
    simp only [subOf, size]
    cases X with
    | nil => exact absurd rfl hX
    | cons a b t => simp only [size_cons]; omega
  · rw [h] at hle ⊢
    simp only [subOf, size_cons] at hle ⊢
    omega

/-- `G` sees nothing in a standard form whose subscripts all stay below `u`. -/
theorem G_eq_nil_of_lt_psi : ∀ Y u : Term, OT Y → Y < psi u nil → G u Y = [] := by
  intro Y
  induction Y with
  | nil => intro u _ _; rfl
  | cons a b t _ _ iht =>
    intro u hOT hlt
    have hab : psi a b < psi u nil := cons_lt_psi_iff.mp hlt
    have hau : ¬ u ≤ a := by
      rcases psi_lt_psi_iff.mp hab with h | ⟨_, h⟩
      · exact not_le_of_lt h
      · exact absurd h (not_lt_nil b)
    rw [G_cons, if_neg hau, List.nil_append]
    refine iht u (OT_tail hOT) ?_
    cases t with
    | nil => exact nil_lt_cons _ _ _
    | cons c d s => exact cons_lt_psi_iff.mpr (lt_of_le_of_lt' (OT_headLe_tail hOT) hab)

/-- `G` sees only `0` in a numeral. -/
theorem G_numeral_eq_nil : ∀ (k : Nat) (u x : Term), x ∈ G u (numeral k) → x = nil := by
  intro k
  induction k with
  | zero => intro u x hx; exact absurd hx List.not_mem_nil
  | succ j ih =>
    intro u x hx
    rw [show numeral (j + 1) = cons nil nil (numeral j) from rfl, G_cons] at hx
    rcases List.mem_append.mp hx with hx | hx
    · by_cases h : u ≤ nil
      · rw [if_pos h, G_nil] at hx
        rcases List.mem_cons.mp hx with h' | hx
        · exact h'
        · exact absurd hx List.not_mem_nil
      · rw [if_neg h] at hx; exact absurd hx List.not_mem_nil
    · exact ih u x hx

theorem nil_lt_of_ne {X : Term} (h : X ≠ nil) : nil < X :=
  lt_of_le_of_ne (nil_le X) (fun hx => h hx.symm)

/-- `1` is the least nonzero term. -/
theorem one_le : ∀ X : Term, X ≠ nil → t1 ≤ X := by
  intro X hX
  cases X with
  | nil => exact absurd rfl hX
  | cons c d t =>
    by_cases hc : c = nil
    · subst hc
      by_cases hd : d = nil
      · subst hd
        cases t with
        | nil => exact le_refl _
        | cons e f s =>
          exact le_of_lt (cons_lt_cons_iff.mpr (Or.inr ⟨rfl, nil_lt_cons _ _ _⟩))
      · exact le_of_lt (cons_lt_cons_iff.mpr
          (Or.inl (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, nil_lt_of_ne hd⟩))))
    · exact le_of_lt (cons_lt_cons_iff.mpr
        (Or.inl (psi_lt_psi_iff.mpr (Or.inl (nil_lt_of_ne hc)))))

/-- `ω` is at most any principal term with a nonzero argument. -/
theorem tw_le_psi {a b : Term} (hb : b ≠ nil) : tw ≤ psi a b := by
  by_cases ha : a = nil
  · subst ha
    rcases le_iff_lt_or_eq.mp (one_le b hb) with h | h
    · exact le_of_lt (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, h⟩))
    · exact h ▸ le_refl _
  · exact le_of_lt (psi_lt_psi_iff.mpr (Or.inl (nil_lt_of_ne ha)))

/-- The domain of a standard form does not exceed it. -/
theorem dom_le : ∀ X : Term, OT X → dom X ≤ X := by
  intro X
  induction X with
  | nil => intro _; exact le_refl _
  | cons a b t iha ihb iht =>
    intro hOT
    cases t with
    | cons c d r =>
      exact le_of_lt (lt_of_le_of_lt' (iht (OT_tail hOT)) (tail_lt (cons c d r) a b hOT))
    | nil =>
      by_cases e1 : dom b = nil
      · have hb : b = nil := dom_eq_nil_iff.mp e1
        subst hb
        by_cases g1 : dom a = nil
        · rw [show dom (cons a nil nil) = cons a nil nil from by rw [dom]; simp_all]
          exact le_refl _
        · by_cases g2 : dom a = t1
          · rw [show dom (cons a nil nil) = cons a nil nil from by rw [dom]; simp_all]
            exact le_refl _
          · rw [show dom (cons a nil nil) = dom a from by rw [dom]; simp_all]
            refine le_of_lt (lt_of_le_of_lt' (iha (OT_fst hOT)) ?_)
            exact sub_lt_psi a nil (OT_head hOT)
      · have hbne : b ≠ nil := fun h => e1 (by rw [h]; rfl)
        by_cases e2 : dom b = t1
        · rw [show dom (cons a b nil) = tw from by rw [dom]; simp_all]
          exact tw_le_psi hbne
        · by_cases e3 : dom b = tw
          · rw [show dom (cons a b nil) = tw from by rw [dom]; simp_all]
            exact tw_le_psi hbne
          · by_cases e4 : dom b < cons a b nil
            · rw [show dom (cons a b nil) = dom b from by rw [dom]; simp_all]
              exact le_of_lt e4
            · rw [show dom (cons a b nil) = tw from by rw [dom]; simp_all]
              exact tw_le_psi hbne

/-- The subscript of the domain of a standard form is strictly below it. -/
theorem subOf_dom_lt {X : Term} (hOT : OT X) (hX : X ≠ nil) : subOf (dom X) < X := by
  have hd : dom X ≠ nil := dom_ne_nil hX
  have hdOT : OT (dom X) := OT_dom hOT
  cases hdd : dom X with
  | nil => exact absurd hdd hd
  | cons c d t =>
    simp only [subOf]
    refine lt_of_lt_of_le' (sub_lt_psi c d (by rw [hdd] at hdOT; exact OT_head hdOT)) ?_
    refine le_trans (psi_le_cons c d t) ?_
    rw [← hdd]
    exact dom_le X hOT

/-- What `G` sees in the domain of a standard form, at a level the domain's
own subscript reaches, it already sees in the form itself. -/
theorem G_dom_subset : ∀ W Z' u : Term, OT W → dom W = psi Z' nil → u ≤ Z' →
    ∀ x ∈ G u (dom W), x ∈ G u W := by
  intro W
  induction W with
  | nil => intro Z' u _ hd _; exact absurd hd (fun h => Term.noConfusion h)
  | cons a b t iha ihb iht =>
    intro Z' u hOT hd hu x hx
    cases t with
    | cons c d r =>
      rw [G_cons]
      exact List.mem_append_right _ (iht Z' u (OT_tail hOT) hd hu x hx)
    | nil =>
      by_cases e1 : dom b = nil
      · have hb : b = nil := dom_eq_nil_iff.mp e1
        subst hb
        by_cases g1 : dom a = nil
        · rw [show dom (cons a nil nil) = cons a nil nil from by rw [dom]; simp_all] at hx
          exact hx
        · by_cases g2 : dom a = t1
          · rw [show dom (cons a nil nil) = cons a nil nil from by rw [dom]; simp_all] at hx
            exact hx
          · have hdX : dom (cons a nil nil) = dom a := by rw [dom]; simp_all
            rw [hdX] at hd hx
            have hane : a ≠ nil := fun h => g1 (by rw [h]; rfl)
            have hZa : Z' < a := by
              have hs := subOf_dom_lt (OT_fst hOT) hane
              rw [hd] at hs
              simpa [subOf] using hs
            have hua : u ≤ a := le_trans hu (le_of_lt hZa)
            rw [G_cons, if_pos hua]
            exact List.mem_append_left _ (List.mem_cons_of_mem _
              (List.mem_append_left _ (iha Z' u (OT_fst hOT) hd hu x hx)))
      · by_cases e2 : dom b = t1
        · have hdX : dom (cons a b nil) = tw := by rw [dom]; simp_all
          rw [hdX] at hd
          exact absurd hd (by intro h; injection h with _ h2 _; exact Term.noConfusion h2)
        · by_cases e3 : dom b = tw
          · have hdX : dom (cons a b nil) = tw := by rw [dom]; simp_all
            rw [hdX] at hd
            exact absurd hd (by intro h; injection h with _ h2 _; exact Term.noConfusion h2)
          · by_cases e4 : dom b < cons a b nil
            · have hdX : dom (cons a b nil) = dom b := by rw [dom]; simp_all
              rw [hdX] at hd hx
              have hZa : Z' ≤ a := by
                rw [hd] at e4
                rcases psi_lt_psi_iff.mp (cons_lt_psi_iff.mp e4) with h | ⟨h, _⟩
                · exact le_of_lt h
                · exact h ▸ le_refl _
              have hua : u ≤ a := le_trans hu hZa
              rw [G_cons, if_pos hua]
              exact List.mem_append_left _ (List.mem_cons_of_mem _
                (List.mem_append_right _ (ihb Z' u (OT_snd hOT) hd hu x hx)))
            · have hdX : dom (cons a b nil) = tw := by rw [dom]; simp_all
              rw [hdX] at hd
              exact absurd hd (by intro h; injection h with _ h2 _; exact Term.noConfusion h2)

/-! ## As an expansion system -/

/-- Extended Buchholz terms as an expansion system: one step is the
fundamental sequence at the numeral `n`.

Well-foundedness is **not** proved, but `step_lt` above is most of it: one step
strictly decreases any standard form below `Ω` other than `0`.  What is left is
that `OT` and `· < Ω` are preserved by the step, so that the state can be
restricted to the countable standard forms and `valHom` with `OrdHom.wf`
applied. -/
def exb : Rewrite where
  State := Term
  step := fun X n => fs X (idx X n)
  halted := fun X => X = nil

example : Prop := exb.Terminates

end Googology.Notation.ExBuchholz.Term
