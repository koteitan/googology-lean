import Googology.Trans.BMS.EntriesR
import Googology.Trans.BMS.Entries2

/-!
# The three rules are one rule

`expandL` is the one-row expansion, `expand2L` the two-row one, and `expandRL`
the one for any number of rows.  Each was proved to be `BM4.expand` on its own
shape, so they must agree where they overlap — and this file says so outright:
`expandRL_one` and `expandRL_two`.

The argument is short because every list is the entries of an array.  `ofList`
and `ofList2` build one, `listEta` says the entries come back, and the two
bridge theorems then say the two rules compute the same array's expansion.
There is no standardness hypothesis except the one `entries_expand` already
needs.

The rest of the file packages the general rule the way `BMS/Prim.lean` and
`BMS/Pair.lean` package one and two rows: `bmsL r` is the system with `r + 1`
rows on the entries, `bmsL_terminates` carries `Notation.BMS.bms_terminates`
across, and `bmsLStd` names the generators.
-/

namespace Googology.Trans.BMS

open BM4

/-- A list is the list of its own entries. -/
theorem listEta {α : Type} [Inhabited α] : ∀ l : List α,
    (List.range l.length).map (fun i => l[i]!) = l := by
  intro l
  induction l with
  | nil => rw [List.length_nil, List.range_zero, List.map_nil]
  | cons a t ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    refine congrArg (a :: ·) (Eq.trans (List.map_congr_left ?_) ih)
    intro i _
    show (a :: t)[i + 1]! = t[i]!
    rfl

/-- The one-row array with these entries. -/
def ofList (l : List Nat) : Arr 1 := ⟨l.length, fun i _ => l[i]!⟩

@[simp] theorem entries_ofList (l : List Nat) : entries (ofList l) = l := by
  rw [entries, show (ofList l).len = l.length from rfl]
  exact listEta l

/-- The two-row array with these entries. -/
def ofList2 (l : List (Nat × Nat)) : Arr 2 :=
  ⟨l.length, fun i k => if k = 0 then (l[i]!).1 else (l[i]!).2⟩

@[simp] theorem entries2_ofList2 (l : List (Nat × Nat)) : entries2 (ofList2 l) = l := by
  rw [entries2, show (ofList2 l).len = l.length from rfl]
  rw [show (fun i => ((ofList2 l).col i 0, (ofList2 l).col i 1)) = (fun i => l[i]!) from by
    funext i
    show (if (0 : Nat) = 0 then (l[i]!).1 else (l[i]!).2,
      if (1 : Nat) = 0 then (l[i]!).1 else (l[i]!).2) = l[i]!
    simp]
  exact listEta l

/-- One row, read through the general definition. -/
theorem entriesR_one (A : Arr 1) : entriesR A = (entries A).map (fun a => [a]) := by
  rw [entriesR, entries, List.map_map]
  rfl

/-- Two rows, read through the general definition. -/
theorem entriesR_two (A : Arr 2) : entriesR A = (entries2 A).map (fun x => [x.1, x.2]) := by
  rw [entriesR, entries2, List.map_map]
  rfl

/-- **One row through the general rule is the one-row rule.** -/
theorem expandRL_one (N : Nat) (l : List Nat) (hc : Col 0 l) :
    expandRL 1 N (l.map (fun a => [a])) = (expandL N 0 l).map (fun a => [a]) := by
  have h1 : entriesR (ofList l) = l.map (fun a => [a]) := by
    rw [entriesR_one, entries_ofList]
  have h2 := entriesR_expand (r := 1) Nat.zero_lt_one (ofList l) N
  rw [h1, entriesR_one, entries_expand' (ofList l) N (by rw [entries_ofList]; exact hc),
    entries_ofList] at h2
  exact h2.symm

/-- **Two rows through the general rule is the two-row rule.** -/
theorem expandRL_two (N : Nat) (l : List (Nat × Nat)) :
    expandRL 2 N (l.map (fun x => [x.1, x.2]))
      = (expand2L N l).map (fun x => [x.1, x.2]) := by
  have h1 : entriesR (ofList2 l) = l.map (fun x => [x.1, x.2]) := by
    rw [entriesR_two, entries2_ofList2]
  have h2 := entriesR_expand (r := 2) (by omega) (ofList2 l) N
  rw [h1, entriesR_two, entries2_expand, entries2_ofList2] at h2
  exact h2.symm

/-! ### The system, on the entries -/

open Pat in
/-- **A run of expansions, computed on the entries, ends**, at any number of
rows. -/
theorem expandRL_terminates {r : Nat} (hr : 0 < r) (A : Arr r) (hA : Std r A)
    (f : Nat → List (List Nat)) (h0 : f 0 = entriesR A)
    (hf : ∀ n, ∃ k, f (n + 1) = expandRL r k (f n)) : ∃ n, f n = [] := by
  choose k hk using hf
  let g : Nat → Arr r := fun n => Nat.rec A (fun m B => expand B (k m)) n
  have hgStd : ∀ n, Std r (g n) := by
    intro n
    induction n with
    | zero => exact hA
    | succ m ih => exact Std.step (k m) ih
  have hgf : ∀ n, entriesR (g n) = f n := by
    intro n
    induction n with
    | zero => exact h0.symm
    | succ m ih =>
      show entriesR (expand (g m) (k m)) = f (m + 1)
      rw [entriesR_expand hr, ih, ← hk m]
  obtain ⟨n, hn⟩ := Googology.Notation.BMS.bms_terminates r
    (fun n => ⟨g n, hgStd n⟩) (fun n => ⟨k n, rfl⟩)
  refine ⟨n, ?_⟩
  rw [← hgf n, entriesR]
  have hl : (g n).len = 0 := hn
  rw [hl, List.range_zero, List.map_nil]

open Pat in
/-- The state of the system with `r + 1` rows: the entries of a standard
array. -/
def BmsState (r : Nat) : Type :=
  {l : List (List Nat) // ∃ A : Arr (r + 1), Std (r + 1) A ∧ entriesR A = l}

open Pat in
theorem bmsL_step_ok {r : Nat} (l : BmsState r) (N : Nat) :
    ∃ A : Arr (r + 1), Std (r + 1) A ∧ entriesR A = expandRL (r + 1) N l.1 := by
  obtain ⟨A, hA, hl⟩ := l.2
  exact ⟨expand A N, Std.step N hA, by rw [entriesR_expand (Nat.succ_pos r), hl]⟩

/-- **Bashicu matrices with `r + 1` rows, on the entries.**  The step is a
function that runs; `Notation.BMS.bms` is not. -/
def bmsL (r : Nat) : Rewrite where
  State := BmsState r
  step := fun l N => ⟨expandRL (r + 1) N l.1, bmsL_step_ok l N⟩
  halted := fun l => l.1 = []

@[simp] theorem bmsL_step_val {r : Nat} (l : BmsState r) (N : Nat) :
    ((bmsL r).step l N : BmsState r).1 = expandRL (r + 1) N l.1 := rfl

/-- **It terminates**, for every number of rows. -/
theorem bmsL_terminates (r : Nat) : (bmsL r).Terminates := by
  intro f hf
  obtain ⟨A, hA, h0⟩ := (f 0).2
  exact expandRL_terminates (Nat.succ_pos r) A hA (fun n => (f n).1) h0.symm
    (fun n => by obtain ⟨k, hk⟩ := hf n; exact ⟨k, congrArg Subtype.val hk⟩)

open Pat in
theorem entriesR_stair (r n : Nat) :
    entriesR (stair r n) = (List.range (n + 1)).map (fun i => List.replicate r i) := by
  rw [entriesR, show (stair r n).len = n + 1 from rfl]
  refine List.map_congr_left (fun i _ => ?_)
  show List.map (fun _ => i) (List.range r) = List.replicate r i
  rw [List.map_const', List.length_range]

open Pat in
/-- The generators `(0,…,0)(1,…,1)⋯(n,…,n)`. -/
def bmsLStd (r : Nat) : (bmsL r).Std where
  Standard := fun _ => True
  gen := fun n => ⟨(List.range (n + 1)).map (fun i => List.replicate (r + 1) i),
    ⟨stair (r + 1) n, Std.init n, entriesR_stair (r + 1) n⟩⟩
  gen_std := fun _ => trivial
  step_std := fun _ _ _ => trivial


/-- **From a generator, any expansion sequence ends**, at any number of
rows. -/
theorem bmsLStd_terminates (r : Nat) : (bmsLStd r).Terminates :=
  (bmsLStd r).of_terminates (bmsL_terminates r)

/-- **The general system is well founded**, at any number of rows. -/
theorem bmsL_wf (r : Nat) : (bmsL r).WF := Rewrite.wf_of_terminates (bmsL_terminates r)

/-- So it carries the rank of its own expansion as an ordinal measure. -/
noncomputable def bmsLRankEval (r : Nat) :
    Eval (bmsL r) (· < · : Ordinal.{0} → Ordinal.{0} → Prop) :=
  Rewrite.rankEval (bmsL_wf r)

end Googology.Trans.BMS
