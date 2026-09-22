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
