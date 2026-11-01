import Googology.Notation.SSOSS.Tree

/-!
Serialization uses the same last-unit-first convention as `Tree`.
`raiseBits` restores one `1` to each run, including empty runs between zeros.
No normal-form assumption is made here: distinct trees can serialize to the
same sequence if their block boundaries are not canonical.
-/

namespace Googology.Notation.SSOSS

def raiseBit (n : ℕ) : List ℕ := if n = 0 then [0, 1] else [1]

def raiseBits (s : List ℕ) : List ℕ := 1 :: s.flatMap raiseBit

/-- The equivalent lift that puts the extra `1` before each zero. -/
def liftBit (n : ℕ) : List ℕ := if n = 0 then [1, 0] else [1]

def liftBits (s : List ℕ) : List ℕ := s.flatMap liftBit

theorem raiseBits_eq (s : List ℕ) : raiseBits s = liftBits s ++ [1] := by
  induction s with
  | nil => rfl
  | cons n s ih =>
    unfold raiseBits liftBits at ih ⊢
    by_cases hn : n = 0 <;>
      simp_all [raiseBit, liftBit]

@[simp] theorem liftBits_append (s t : List ℕ) :
    liftBits (s ++ t) = liftBits s ++ liftBits t := by
  simp [liftBits]

@[simp] theorem liftBits_zero : liftBits [0] = [1,0] := rfl
@[simp] theorem liftBits_one : liftBits [1] = [1] := rfl

def flat : List U → List ℕ
  | [] => []
  | .z :: rest => flat rest ++ [0]
  | .b u :: rest => flat rest ++ raiseBits (flat u)
termination_by t => sizeOf t
decreasing_by all_goals simp_wf <;> omega

@[simp] theorem flat_nil : flat [] = [] := by rw [flat]
@[simp] theorem flat_z (t : List U) : flat (.z :: t) = flat t ++ [0] := by rw [flat]
@[simp] theorem flat_b (u t : List U) :
    flat (.b u :: t) = flat t ++ raiseBits (flat u) := by rw [flat]

theorem flat_append (s t : List U) : flat (s ++ t) = flat t ++ flat s := by
  induction s with
  | nil => simp
  | cons u s ih => cases u <;> simp [ih, List.append_assoc]

theorem flat_replicate_z (k : ℕ) : flat (List.replicate k .z) = List.replicate k 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, flat_z, ih, List.replicate_succ']

theorem flat_flatten_replicate (t : List U) (k : ℕ) :
    flat (List.replicate k t).flatten = (List.replicate k (flat t)).flatten := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, flat_append, ih,
      List.replicate_succ']
    simp

def encode (t : List U) : List ℕ := [0, 0] ++ flat t

/-- Between two maximal blocks there must be at least two external zeros.
One zero is permitted at the start of the entire serialized list. -/
def BlockGap : List U → Prop
  | [] => True
  | [.z] => True
  | .z :: .z :: _ => True
  | _ => False

/-- Trees respecting the maximal-block parsing convention, at every depth.
This is a syntactic condition, independent of `Seq.cut` and standardness. -/
inductive Canonical : List U → Prop
  | nil : Canonical []
  | zero {t : List U} : Canonical t → Canonical (.z :: t)
  | block {u P : List U} : Canonical u → Canonical P → BlockGap P →
      Canonical (.b u :: P)

@[simp] theorem encode_z (t : List U) : encode (.z :: t) = encode t ++ [0] := by
  simp [encode]

theorem flat_tower (n : ℕ) : flat (tower n) = List.replicate n 1 := by
  induction n with
  | zero => simp [tower]
  | succ n ih =>
    simp only [tower, flat_b, flat_nil, List.nil_append, ih, raiseBits]
    simp [List.flatMap_replicate, raiseBit, List.replicate_succ]

end Googology.Notation.SSOSS
