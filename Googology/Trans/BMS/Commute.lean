import Googology.Trans.BMS.ExBuchholz

/-!
# Expansion and the fundamental sequence

`BMS/ExBuchholz.lean` reads a one-row matrix as an extended Buchholz term, and
`BMS/OneRow.lean` says what `BM4.expand` does to one row.  This file joins
them: `expandL` is that expansion written on the entries, and `read_expandL`
says the reading turns it into `[ ]`,

    read b (expandL N b l) = (read b l)[idx (read b l) (N + 1)].

The `N + 1` is the two systems' counting: `A[N]` writes `N + 1` copies of the
bad part, while `ψ_0(Z+1)[n]` writes `n` copies of `ψ_0(Z)`.  A `StepHom`
carries exactly this, in its `reindex`.

The proof runs on three facts about an all-zero-subscript term.  `dom_read`
says such a term is `0` when the matrix is empty, a successor when the matrix
ends at its own level, and an `ω`-limit otherwise — the fourth clause of `[ ]`,
the one with the tower, never fires.  `read_append` says reading is additive,
so a matrix laid end to end reads as a sum.  And `Col` is preserved, so the
three cases of `expandL` line up with the three clauses of `[ ]`: end the
block and the term loses its last summand, repeat the block and the term
becomes `n` copies, go higher and the term follows one level in.

What is still missing for a `StepHom` is the index bookkeeping between `expandL`
and `BM4.expand` on `BM4.Arr 1`.
-/

namespace Googology.Trans.BMS

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

/-- A chain at one level is a chain at any lower one. -/
theorem chain_mono {b b' : Nat} (h : b' ≤ b) :
    ∀ (prev : Nat) (s : List Nat), Chain b prev s → Chain b' prev s := by
  intro prev s
  induction s generalizing prev with
  | nil => intro _; exact trivial
  | cons c r ih => intro hc; exact ⟨le_trans h hc.1, hc.2.1, ih c hc.2.2⟩

theorem head_dropWhile_not {p : Nat → Bool} : ∀ (l : List Nat) (x : Nat),
    (l.dropWhile p).head? = some x → p x = false := by
  intro l
  induction l with
  | nil => intro x h; simp at h
  | cons c r ih =>
    intro x h
    by_cases hc : p c
    · rw [List.dropWhile_cons, if_pos hc] at h; exact ih x h
    · rw [List.dropWhile_cons, if_neg hc] at h
      simp only [List.head?_cons, Option.some.injEq] at h
      subst h; simpa using hc

/-- **Reading is additive.**  Two matrices at the same level, laid end to end,
read as the sum of what each reads as. -/
theorem read_append : ∀ (l₁ : List Nat) (b : Nat), Col b l₁ → ∀ l₂ : List Nat, Col b l₂ →
    read b (l₁ ++ l₂) = addT (read b l₁) (read b l₂) := by
  intro l₁
  induction hn : l₁.length using Nat.strong_induction_on generalizing l₁ with
  | _ n ih =>
    cases l₁ with
    | nil => intro b _ l₂ _; rw [List.nil_append, read_nil, addT_nil_left]
    | cons a rest =>
      intro b hc l₂ h2
      obtain ⟨ha, hch⟩ := hc
      subst ha
      have hsplit : rest ++ l₂
          = rest.takeWhile (fun x => decide (a < x))
            ++ (rest.dropWhile (fun x => decide (a < x)) ++ l₂) := by
        rw [← List.append_assoc, List.takeWhile_append_dropWhile]
      have hall : ∀ x ∈ rest.takeWhile (fun x => decide (a < x)), decide (a < x) = true :=
        fun x hx => List.mem_takeWhile_imp (p := fun y => decide (a < y)) hx
      have hhead : ∀ x, (rest.dropWhile (fun x => decide (a < x)) ++ l₂).head? = some x →
          decide (a < x) = false := by
        intro x hx
        cases hd : rest.dropWhile (fun x => decide (a < x)) with
        | cons c r =>
          rw [hd, List.cons_append] at hx
          simp only [List.head?_cons, Option.some.injEq] at hx
          subst hx
          exact head_dropWhile_not rest c (by rw [hd]; rfl)
        | nil =>
          rw [hd, List.nil_append] at hx
          cases l₂ with
          | nil => simp at hx
          | cons c r =>
            obtain ⟨hcb, _⟩ := h2
            subst hcb
            simp only [List.head?_cons, Option.some.injEq] at hx
            subst hx; simp
      rw [List.cons_append, read_cons, hsplit,
        takeWhile_append_of_all _ _ hall hhead, dropWhile_append_of_all _ _ hall hhead,
        ih (rest.dropWhile (fun x => decide (a < x))).length
          (by subst hn; simp only [List.length_cons]
              exact Nat.lt_succ_of_le (List.dropWhile_sublist _).length_le) _ rfl _
          (col_dropWhile rest a a hch) l₂ h2,
        read_cons, addT_cons]

/-! ### Where a matrix ends -/

/-- The last entry. -/
def lastOf : List Nat → Option Nat
  | [] => none
  | [a] => some a
  | _ :: (c :: r) => lastOf (c :: r)

@[simp] theorem lastOf_singleton (a : Nat) : lastOf [a] = some a := rfl

theorem lastOf_cons : ∀ (a : Nat) (l : List Nat), l ≠ [] → lastOf (a :: l) = lastOf l := by
  intro a l h
  cases l with
  | nil => exact absurd rfl h
  | cons c r => rw [lastOf]

theorem lastOf_append : ∀ (l₁ l₂ : List Nat), l₂ ≠ [] → lastOf (l₁ ++ l₂) = lastOf l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro _ _; rw [List.nil_append]
  | cons a r ih =>
    intro l₂ h
    rw [List.cons_append, lastOf_cons a (r ++ l₂) (by cases r <;> simp_all), ih l₂ h]

theorem mem_of_lastOf : ∀ (l : List Nat) (x : Nat), lastOf l = some x → x ∈ l := by
  intro l
  induction l with
  | nil => intro x h; simp [lastOf] at h
  | cons a r ih =>
    intro x h
    cases r with
    | nil => rw [lastOf_singleton] at h; simp_all
    | cons c t => rw [lastOf_cons a _ (by simp)] at h; exact List.mem_cons_of_mem a (ih x h)

theorem eq_concat_of_lastOf : ∀ (l : List Nat) (x : Nat), lastOf l = some x →
    l = l.dropLast ++ [x] := by
  intro l
  induction l with
  | nil => intro x h; simp [lastOf] at h
  | cons a r ih =>
    intro x h
    cases r with
    | nil => rw [lastOf_singleton] at h; rw [← Option.some.inj h]; rfl
    | cons c t =>
      rw [lastOf_cons a _ (by simp)] at h
      have := ih x h
      rw [show (a :: c :: t).dropLast = a :: (c :: t).dropLast from rfl, List.cons_append]
      exact congrArg (a :: ·) this

/-! ### Entries of a matrix -/

theorem chain_ge : ∀ (l : List Nat) (b prev : Nat), Chain b prev l → ∀ x ∈ l, b ≤ x := by
  intro l
  induction l with
  | nil => intro _ _ _ x hx; exact absurd hx (by simp)
  | cons c r ih =>
    intro b prev h x hx
    obtain ⟨h1, _, h3⟩ := chain_cons h
    rcases List.mem_cons.mp hx with he | hm
    · exact he ▸ h1
    · exact ih b c h3 x hm

theorem col_ge : ∀ (l : List Nat) (b : Nat), Col b l → ∀ x ∈ l, b ≤ x := by
  intro l b h x hx
  cases l with
  | nil => exact absurd hx (by simp)
  | cons a r =>
    obtain ⟨ha, hch⟩ := h
    subst ha
    rcases List.mem_cons.mp hx with he | hm
    · exact Nat.le_of_eq he.symm
    · exact chain_ge r a a hch x hm

theorem chain_dropLast : ∀ (l : List Nat) (b prev : Nat), Chain b prev l →
    Chain b prev l.dropLast := by
  intro l
  induction l with
  | nil => intro _ _ _; exact trivial
  | cons c r ih =>
    intro b prev h
    obtain ⟨h1, h2, h3⟩ := chain_cons h
    cases r with
    | nil => exact trivial
    | cons d t =>
      rw [show (c :: d :: t).dropLast = c :: (d :: t).dropLast from rfl]
      exact ⟨h1, h2, ih b c h3⟩

/-! ### What kind of limit a matrix names -/

/-- **A matrix names a successor exactly when it ends at its own level.**  It
names `0` when it is empty, and an `ω`-limit otherwise; nothing an all-zero
subscript term names is a limit of any other kind. -/
theorem dom_read : ∀ (l : List Nat) (b : Nat), Col b l →
    dom (read b l) = if l = [] then nil else if lastOf l = some b then t1 else tw := by
  intro l
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    cases l with
    | nil => intro b _; rw [read_nil, dom_nil, if_pos rfl]
    | cons a rest =>
      intro b hc
      obtain ⟨ha, hch⟩ := hc
      subst ha
      rw [if_neg (by simp)]
      cases hlo : rest.dropWhile (fun x => decide (a < x)) with
      | cons c lo' =>
        have hne : rest ≠ [] := by
          intro he; rw [he] at hlo; simp [List.dropWhile] at hlo
        have hsp : rest = rest.takeWhile (fun x => decide (a < x)) ++ (c :: lo') := by
          rw [← hlo, List.takeWhile_append_dropWhile]
        have hL : read a (c :: lo')
            = cons nil (read (a + 1) ((lo').takeWhile (fun x => decide (a < x))))
                (read a ((lo').dropWhile (fun x => decide (a < x)))) := read_cons a c lo'
        rw [read_cons, hlo, hL, dom, ← hL, lastOf_cons a rest hne,
          show lastOf rest = lastOf (c :: lo') by rw [hsp]; exact lastOf_append _ _ (by simp),
          ih (c :: lo').length
            (by subst hn; rw [hsp]; simp only [List.length_cons, List.length_append]; omega)
            _ rfl _ (by rw [← hlo]; exact col_dropWhile rest a a hch),
          ]
        · exact if_neg (by simp)
        · simp
      | nil =>
        have hrest : rest = rest.takeWhile (fun x => decide (a < x)) := by
          have h0 : rest.takeWhile (fun x => decide (a < x))
              ++ rest.dropWhile (fun x => decide (a < x)) = rest :=
            List.takeWhile_append_dropWhile
          rw [hlo, List.append_nil] at h0
          exact h0.symm
        rw [read_cons, hlo, read_nil]
        cases hhi : rest.takeWhile (fun x => decide (a < x)) with
        | nil =>
          rw [read_nil, dom]
          have : rest = [] := by rw [hrest, hhi]
          subst this
          simp [lastOf]
        | cons d hi' =>
          have hcolhi : Col (a + 1) (d :: hi') := by
            rw [← hhi]; exact col_takeWhile rest a a (Nat.le_refl _) hch
          have hdom := ih (d :: hi').length
            (by subst hn; rw [hrest, hhi]; simp) _ rfl _ hcolhi
          rw [if_neg (by simp)] at hdom
          rw [dom, hdom]
          have hlast : lastOf (a :: rest) ≠ some a := by
            rw [lastOf_cons a rest (by rw [hrest, hhi]; simp),
              show rest = d :: hi' by rw [hrest, hhi]]
            intro he
            have := col_ge _ _ hcolhi _ (mem_of_lastOf _ _ he)
            omega
          rw [if_neg hlast]
          split
          · rw [if_neg (by decide), if_pos (by rfl)]
          · rw [if_neg (by decide), if_neg (by decide), if_pos (by rfl)]


/-! ### More on matrices -/

theorem chain_of_col : ∀ {b c prev : Nat} {l : List Nat}, Col c l → b ≤ c → c ≤ prev + 1 →
    Chain b prev l := by
  intro b c prev l h h1 h2
  cases l with
  | nil => exact trivial
  | cons d r =>
    obtain ⟨hd, hch⟩ := h
    subst hd
    exact ⟨h1, h2, chain_mono h1 d r hch⟩

theorem col_dropLast : ∀ (l : List Nat) (b : Nat), Col b l → Col b l.dropLast := by
  intro l b h
  cases l with
  | nil => exact trivial
  | cons a r =>
    obtain ⟨ha, hch⟩ := h
    subst ha
    cases r with
    | nil => exact trivial
    | cons c t => exact ⟨rfl, chain_dropLast (c :: t) a a hch⟩

theorem chain_append : ∀ (l₁ : List Nat) (b prev : Nat), Chain b prev l₁ → b ≤ prev →
    ∀ l₂ : List Nat, Col b l₂ → Chain b prev (l₁ ++ l₂) := by
  intro l₁
  induction l₁ with
  | nil => intro b prev _ hp l₂ h2; exact chain_of_col h2 (Nat.le_refl b) (by omega)
  | cons c r ih =>
    intro b prev h _ l₂ h2
    obtain ⟨h1, h3, h4⟩ := chain_cons h
    exact ⟨h1, h3, ih b c h4 h1 l₂ h2⟩

theorem col_append : ∀ (l₁ l₂ : List Nat) (b : Nat), Col b l₁ → Col b l₂ →
    Col b (l₁ ++ l₂) := by
  intro l₁ l₂ b h1 h2
  cases l₁ with
  | nil => exact h2
  | cons a r =>
    obtain ⟨ha, hch⟩ := h1
    subst ha
    exact ⟨rfl, chain_append r a a hch (Nat.le_refl a) l₂ h2⟩

theorem col_flatten : ∀ (k : Nat) (blk : List Nat) (b : Nat), Col b blk →
    Col b (List.replicate k blk).flatten := by
  intro k
  induction k with
  | zero => intro _ _ _; exact trivial
  | succ m ih =>
    intro blk b h
    rw [List.replicate_succ, List.flatten_cons]
    exact col_append _ _ b h (ih blk b h)

theorem takeWhile_all {p : Nat → Bool} (l : List Nat) (h : ∀ x ∈ l, p x = true) :
    l.takeWhile p = l := by
  have := takeWhile_append_of_all (p := p) l [] h (by intro x hx; simp at hx)
  rwa [List.append_nil] at this

theorem dropWhile_all {p : Nat → Bool} (l : List Nat) (h : ∀ x ∈ l, p x = true) :
    l.dropWhile p = [] := by
  have := dropWhile_append_of_all (p := p) l [] h (by intro x hx; simp at hx)
  rwa [List.append_nil] at this

/-! ### Expansion, on the entries -/

/-- **One-row expansion, written on the entries.**  At the top level the last
entry sits in the last block, so expansion works there and leaves the rest
alone.  Inside a block: if the block ends at its own level, the block is
repeated `N + 1` times with that last entry dropped; otherwise expansion
recurses one level up. -/
def expandL (N : Nat) : Nat → List Nat → List Nat
  | _, [] => []
  | b, _ :: rest =>
      if rest.dropWhile (fun x => decide (b < x)) = [] then
        (if rest.takeWhile (fun x => decide (b < x)) = [] then []
         else if lastOf (rest.takeWhile (fun x => decide (b < x))) = some (b + 1) then
           (List.replicate (N + 1)
             (b :: (rest.takeWhile (fun x => decide (b < x))).dropLast)).flatten
         else b :: expandL N (b + 1) (rest.takeWhile (fun x => decide (b < x))))
      else b :: (rest.takeWhile (fun x => decide (b < x))
        ++ expandL N b (rest.dropWhile (fun x => decide (b < x))))
  termination_by _ s => s.length
  decreasing_by
    all_goals simp only [List.length_cons]
    · exact Nat.lt_succ_of_le (List.takeWhile_sublist _).length_le
    · exact Nat.lt_succ_of_le (List.dropWhile_sublist _).length_le

@[simp] theorem expandL_nil (N b : Nat) : expandL N b [] = [] := by rw [expandL]

theorem expandL_cons (N b a : Nat) (rest : List Nat) :
    expandL N b (a :: rest) =
      if rest.dropWhile (fun x => decide (b < x)) = [] then
        (if rest.takeWhile (fun x => decide (b < x)) = [] then []
         else if lastOf (rest.takeWhile (fun x => decide (b < x))) = some (b + 1) then
           (List.replicate (N + 1)
             (b :: (rest.takeWhile (fun x => decide (b < x))).dropLast)).flatten
         else b :: expandL N (b + 1) (rest.takeWhile (fun x => decide (b < x))))
      else b :: (rest.takeWhile (fun x => decide (b < x))
        ++ expandL N b (rest.dropWhile (fun x => decide (b < x)))) := by
  rw [expandL]

theorem mem_flatten_replicate : ∀ (k : Nat) (blk : List Nat) (x : Nat),
    x ∈ (List.replicate k blk).flatten → x ∈ blk := by
  intro k
  induction k with
  | zero => intro _ x hx; simp at hx
  | succ m ih =>
    intro blk x hx
    rw [List.replicate_succ, List.flatten_cons, List.mem_append] at hx
    exact hx.elim id (ih blk x)

/-- Expansion stays at the level it was given. -/
theorem mem_expandL (N : Nat) : ∀ (l : List Nat) (b : Nat), Col b l →
    ∀ x ∈ expandL N b l, b ≤ x := by
  intro l
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    cases l with
    | nil => intro b _ x hx; simp at hx
    | cons a rest =>
      intro b hc x hx
      obtain ⟨ha, hch⟩ := hc
      subst ha
      have hhilen : (rest.takeWhile (fun x => decide (a < x))).length < n := by
        subst hn; simp only [List.length_cons]
        exact Nat.lt_succ_of_le (List.takeWhile_sublist _).length_le
      have hlolen : (rest.dropWhile (fun x => decide (a < x))).length < n := by
        subst hn; simp only [List.length_cons]
        exact Nat.lt_succ_of_le (List.dropWhile_sublist _).length_le
      rw [expandL_cons] at hx
      split at hx
      · split at hx
        · simp at hx
        · split at hx
          · rcases List.mem_cons.mp (mem_flatten_replicate _ _ x hx) with he | hm
            · omega
            · have := List.mem_takeWhile_imp (p := fun y => decide (a < y))
                (List.dropLast_sublist _ |>.subset hm)
              simp at this; omega
          · rcases List.mem_cons.mp hx with he | hm
            · omega
            · have := ih _ hhilen _ rfl (a + 1)
                (col_takeWhile rest a a (Nat.le_refl _) hch) x hm
              omega
      · rcases List.mem_cons.mp hx with he | hm
        · omega
        · rcases List.mem_append.mp hm with h1 | h2
          · have := List.mem_takeWhile_imp (p := fun y => decide (a < y)) h1
            simp at this; omega
          · exact ih _ hlolen _ rfl a (col_dropWhile rest a a hch) x h2

/-- Expansion starts where it was given, when it starts at all. -/
theorem head_expandL (N : Nat) : ∀ (l : List Nat) (b : Nat),
    expandL N b l = [] ∨ (expandL N b l).head? = some b := by
  intro l b
  cases l with
  | nil => exact Or.inl (expandL_nil N b)
  | cons a rest =>
    rw [expandL_cons]
    split
    · split
      · exact Or.inl rfl
      · split
        · rename_i h1 _
          refine Or.inr ?_
          rw [List.replicate_succ, List.flatten_cons, List.cons_append]
          rfl
        · exact Or.inr rfl
    · exact Or.inr rfl


/-! ### Small facts about terms -/

theorem numVal_numeral : ∀ n : Nat, numVal (numeral n) = n
  | 0 => rfl
  | k + 1 => by
      rw [show numeral (k + 1) = cons nil nil (numeral k) from rfl, numVal, numVal_numeral k]

theorem addT_t1_cons : ∀ P : Term, ∃ x y u, addT P t1 = cons x y u
  | nil => ⟨nil, nil, nil, rfl⟩
  | cons x y t => ⟨x, y, addT t t1, rfl⟩

/-- Taking one away from a sum that ends in `1`. -/
theorem fs_addT_t1 : ∀ P : Term, fs (addT P t1) nil = P := by
  intro P
  induction P with
  | nil => rw [addT_nil_left, fs]; simp
  | cons x y t _ _ iht =>
    obtain ⟨p, q, u, hu⟩ := addT_t1_cons t
    rw [addT_cons, hu, fs, show cons p q u = addT t t1 from hu.symm, iht]

theorem read_singleton (b : Nat) : read b [b] = t1 := by
  rw [read_cons]; simp

/-- Reading a block repeated `k` times gives `k` copies of what the block
reads as. -/
theorem read_flatten_replicate : ∀ (k : Nat) (blk : List Nat) (b : Nat) (P : Term),
    Col b blk → read b blk = cons nil P nil →
    read b ((List.replicate k blk).flatten) = repeatPrin nil P k := by
  intro k
  induction k with
  | zero => intro _ b _ _ _; rw [List.replicate_zero, List.flatten_nil, read_nil, repeatPrin]
  | succ m ih =>
    intro blk b P hcol hread
    rw [List.replicate_succ, List.flatten_cons,
      read_append blk b hcol _ (col_flatten m blk b hcol), hread,
      ih blk b P hcol hread, addT_cons, addT_nil_left, repeatPrin]


/-! ### One block, on the term side

A matrix that is one block reads as a single principal term `ψ_0(H)`, and with
all subscripts `0` the only shapes `H` can have are `0`, a successor and an
`ω`-limit.  These are the three clauses of `[ ]` that the translation meets. -/

theorem dom_t1 : dom t1 = t1 := by rw [dom]; simp

theorem fs_t1_nil : fs t1 nil = nil := by rw [fs]; simp

theorem idx_of_dom_t1 {X : Term} (h : dom X = t1) (k : Nat) : idx X k = nil := by
  rw [idx, if_pos h]

theorem idx_of_dom_tw {X : Term} (h : dom X = tw) (k : Nat) : idx X k = numeral k := by
  rw [idx, if_neg (by rw [h]; decide)]

theorem dom_block_succ {H : Term} (h : dom H = t1) : dom (cons nil H nil) = tw := by
  rw [dom, if_neg (by rw [h]; decide), if_pos h]

theorem fs_block_succ {H : Term} (h : dom H = t1) (k : Nat) :
    fs (cons nil H nil) (numeral k) = repeatPrin nil (fs H nil) k := by
  rw [fs, if_neg (by rw [h]; decide), if_pos h]
  simp only [isNum_numeral, numVal_numeral, if_true]

theorem dom_block_lim {H : Term} (h : dom H = tw) : dom (cons nil H nil) = tw := by
  rw [dom, if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_pos h]

theorem fs_block_lim {H : Term} (h : dom H = tw) (Y : Term) :
    fs (cons nil H nil) Y = cons nil (fs H Y) nil := by
  rw [fs, if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_pos h]


theorem dom_sum (H P Q : Term) : dom (cons nil H (cons nil P Q)) = dom (cons nil P Q) := by
  rw [dom]
  · simp

theorem idx_sum (H P Q : Term) (k : Nat) :
    idx (cons nil H (cons nil P Q)) k = idx (cons nil P Q) k := by
  rw [idx, idx, dom_sum]

theorem fs_sum (H P Q Y : Term) :
    fs (cons nil H (cons nil P Q)) Y = cons nil H (fs (cons nil P Q) Y) := by
  rw [fs]

/-! ### The commutation -/

/-- **The reading commutes with expansion.**  Expanding a one-row matrix at
`N` and reading the result gives the `(N + 1)`-st member of the fundamental
sequence of the ordinal the matrix read as. -/
theorem read_expandL (N : Nat) : ∀ (l : List Nat) (b : Nat), Col b l →
    read b (expandL N b l) = fs (read b l) (idx (read b l) (N + 1)) := by
  intro l
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    cases l with
    | nil => intro b _; rw [expandL_nil, read_nil, fs]
    | cons a rest =>
      intro b hc
      obtain ⟨ha, hch⟩ := hc
      subst ha
      have hcolhi : Col (a + 1) (rest.takeWhile (fun x => decide (a < x))) :=
        col_takeWhile rest a a (Nat.le_refl _) hch
      have hcollo : Col a (rest.dropWhile (fun x => decide (a < x))) :=
        col_dropWhile rest a a hch
      have hhilen : (rest.takeWhile (fun x => decide (a < x))).length < n := by
        subst hn; simp only [List.length_cons]
        exact Nat.lt_succ_of_le (List.takeWhile_sublist _).length_le
      have hlolen : (rest.dropWhile (fun x => decide (a < x))).length < n := by
        subst hn; simp only [List.length_cons]
        exact Nat.lt_succ_of_le (List.dropWhile_sublist _).length_le
      rw [expandL_cons]
      by_cases hlo : rest.dropWhile (fun x => decide (a < x)) = []
      · -- one block: the whole matrix is `a` followed by entries above `a`
        rw [if_pos hlo]
        have hR : read a (a :: rest)
            = cons nil (read (a + 1) (rest.takeWhile (fun x => decide (a < x)))) nil := by
          rw [read_cons, hlo, read_nil]
        by_cases hhi : rest.takeWhile (fun x => decide (a < x)) = []
        · -- the matrix is `[a]`, which reads as `1`
          rw [if_pos hhi, read_nil, hR, hhi, read_nil,
            idx_of_dom_t1 (show dom t1 = t1 from dom_t1), fs_t1_nil]
        · rw [if_neg hhi]
          have hdom := dom_read _ (a + 1) hcolhi
          rw [if_neg hhi] at hdom
          by_cases hl1 : lastOf (rest.takeWhile (fun x => decide (a < x))) = some (a + 1)
          · -- the block ends at its own level, so it names a successor
            rw [if_pos hl1]
            rw [if_pos hl1] at hdom
            have hcolD : Col (a + 1) ((rest.takeWhile (fun x => decide (a < x))).dropLast) :=
              col_dropLast _ _ hcolhi
            have hcolB : Col a (a :: (rest.takeWhile (fun x => decide (a < x))).dropLast) :=
              ⟨rfl, chain_of_col hcolD (by omega) (by omega)⟩
            have hallD : ∀ x ∈ (rest.takeWhile (fun x => decide (a < x))).dropLast,
                decide (a < x) = true := by
              intro x hx
              have := col_ge _ _ hcolD x hx
              exact decide_eq_true (by omega)
            have hblk : read a (a :: (rest.takeWhile (fun x => decide (a < x))).dropLast)
                = cons nil
                    (read (a + 1) ((rest.takeWhile (fun x => decide (a < x))).dropLast)) nil := by
              rw [read_cons, takeWhile_all _ hallD, dropWhile_all _ hallD, read_nil]
            have hH : read (a + 1) (rest.takeWhile (fun x => decide (a < x)))
                = addT (read (a + 1)
                    ((rest.takeWhile (fun x => decide (a < x))).dropLast)) t1 := by
              conv_lhs => rw [eq_concat_of_lastOf _ _ hl1]
              rw [read_append _ _ hcolD _ (show Col (a + 1) [a + 1] from ⟨rfl, trivial⟩),
                read_singleton]
            rw [read_flatten_replicate _ _ a _ hcolB hblk, hR,
              idx_of_dom_tw (dom_block_succ hdom), fs_block_succ hdom, hH, fs_addT_t1]
          · -- the block goes higher, so it names an ω-limit
            rw [if_neg hl1]
            rw [if_neg hl1] at hdom
            have hallE : ∀ x ∈ expandL N (a + 1) (rest.takeWhile (fun x => decide (a < x))),
                decide (a < x) = true := by
              intro x hx
              have := mem_expandL N _ (a + 1) hcolhi x hx
              exact decide_eq_true (by omega)
            rw [read_cons, takeWhile_all _ hallE, dropWhile_all _ hallE, read_nil,
              ih _ hhilen _ rfl _ hcolhi, idx_of_dom_tw hdom, hR,
              idx_of_dom_tw (dom_block_lim hdom), fs_block_lim hdom]
      · -- more than one block: expansion happens in the last one
        rw [if_neg hlo]
        have hall : ∀ x ∈ rest.takeWhile (fun x => decide (a < x)), decide (a < x) = true :=
          fun x hx => List.mem_takeWhile_imp (p := fun y => decide (a < y)) hx
        have hhead : ∀ x, (expandL N a (rest.dropWhile (fun x => decide (a < x)))).head?
            = some x → decide (a < x) = false := by
          intro x hx
          rcases head_expandL N (rest.dropWhile (fun x => decide (a < x))) a with he | he
          · rw [he] at hx; simp at hx
          · rw [he] at hx
            simp only [Option.some.injEq] at hx
            subst hx; simp
        obtain ⟨c, lo', hlo'⟩ : ∃ c lo', rest.dropWhile (fun x => decide (a < x)) = c :: lo' := by
          cases hd : rest.dropWhile (fun x => decide (a < x)) with
          | nil => exact absurd hd hlo
          | cons c lo' => exact ⟨c, lo', rfl⟩
        have hL : read a (c :: lo')
            = cons nil (read (a + 1) (lo'.takeWhile (fun x => decide (a < x))))
                (read a (lo'.dropWhile (fun x => decide (a < x)))) := read_cons a c lo'
        rw [read_cons, takeWhile_append_of_all _ _ hall hhead,
          dropWhile_append_of_all _ _ hall hhead, ih _ hlolen _ rfl _ hcollo,
          read_cons, hlo', hL, idx_sum, fs_sum]


end Googology.Trans.BMS
