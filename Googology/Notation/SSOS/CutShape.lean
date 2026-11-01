import Googology.Notation.SSOS.CutReduction
import Googology.Notation.SSOS.ShapeExpansion
import Googology.Notation.SSOS.SequenceOrdinal

/-!
# The cut of a `StdShape` tree (stage 2), and the standard forms

Main results (no `sorry`, no new axiom):

* `cutCorrect_of_stdShape`: for every `StdShape (.b u :: P)`, the actual cut equals the
  tree cut (`CutCorrect u P`).
* `standard_shape`: every standard form is `[]`, `[0]`, or `encode t` with `StdShape t`.
* `cutCorrect_of_standard`: goal A of the second request.
* `o_fs_lt_of_standard`, `o_fs_sup_of_standard`: for every standard limit form, the
  expansion terms have smaller values and their supremum is the value. No `CutCorrect`
  assumption.

Proof idea. Put `S = E ++ raiseBits s` (`E = encode P` ends with `0,0`, `s = flat u`) and
`S' = [0,0] ++ s` (`= encode u` when `u` is a block). The suffixes of `S` after its zeros at
positions `≥ |E|-1` are `0 :: raiseBits s` and the `raiseBits` images of the suffixes of `S'`
after its zeros, through the position map `cpos`. `raiseBits` is strictly monotone on 0/1
lists, and `cpos` also carries `lastZero` (= `p 1`) and `shortZero` (= `p 2`). So for
`u = .b w :: rest` the argmax of `S'` (the cut of `encode u`, by induction) moves to `S`
(`argmax_transfer`). For `u = []` or `u = .z :: _` the cut is the start of the block, which
needs `Dom (flat u)`: every suffix after a zero is smaller than the whole list
(`argmax_base`). `Dom` holds for `StdShape` forests (`stdShape_dom`): they are words
`B₁ 00 B₂ 00 … Bₖ 0^e` with non-increasing blocks `Bᵢ = raiseBits (flat uᵢ)`.
-/

namespace Googology.Notation.SSOS
theorem flatMap_raiseBit_lt_iff (s t : List ℕ) (hs : Binary s) (ht : Binary t) :
    s.flatMap raiseBit < t.flatMap raiseBit ↔ s < t := by
  induction s generalizing t with
  | nil =>
    cases t with
    | nil => simp
    | cons b t => simp [raiseBit]; split <;> simp
  | cons a s ih =>
    have ha := hs a (by simp)
    have hs' : Binary s := fun k hk => hs k (List.mem_cons_of_mem _ hk)
    cases t with
    | nil => simp [List.not_lt_nil]
    | cons b t =>
      have hb := ht b (by simp)
      have ht' : Binary t := fun k hk => ht k (List.mem_cons_of_mem _ hk)
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        simp [raiseBit, List.cons_lt_cons_iff, ih t hs' ht']

theorem raiseBits_lt_iff (s t : List ℕ) (hs : Binary s) (ht : Binary t) :
    raiseBits s < raiseBits t ↔ s < t := by
  simp only [raiseBits, List.cons_lt_cons_iff, lt_irrefl, false_or, true_and]
  exact flatMap_raiseBit_lt_iff s t hs ht

theorem raiseBits_le_iff (s t : List ℕ) (hs : Binary s) (ht : Binary t) :
    raiseBits s ≤ raiseBits t ↔ s ≤ t := by
  rw [← not_lt, ← not_lt, raiseBits_lt_iff t s ht hs]

theorem raiseBits_inj (s t : List ℕ) (hs : Binary s) (ht : Binary t)
    (h : raiseBits s = raiseBits t) : s = t := by
  rcases lt_trichotomy s t with hl | he | hl
  · exact absurd h (ne_of_lt ((raiseBits_lt_iff s t hs ht).2 hl))
  · exact he
  · exact absurd h.symm (ne_of_lt ((raiseBits_lt_iff t s ht hs).2 hl))

theorem binary_drop (s : List ℕ) (hs : Binary s) (k : ℕ) : Binary (s.drop k) :=
  fun n hn => hs n (List.mem_of_mem_drop hn)

theorem binary_take (s : List ℕ) (hs : Binary s) (k : ℕ) : Binary (s.take k) :=
  fun n hn => hs n (List.mem_of_mem_take hn)

theorem oneRun_flatMap_raiseBit (s : List ℕ) (hs : Binary s) :
    Seq.oneRun (s.flatMap raiseBit) = Seq.oneRun s := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    have ha := hs a (by simp)
    have hs' : Binary s := fun k hk => hs k (List.mem_cons_of_mem _ hk)
    rcases ha with rfl | rfl
    · simp [raiseBit, Seq.oneRun]
    · simp [raiseBit, Seq.oneRun, ih hs']

theorem oneRun_raiseBits (s : List ℕ) (hs : Binary s) :
    Seq.oneRun (raiseBits s) = Seq.oneRun s + 1 := by
  simp [raiseBits, Seq.oneRun, oneRun_flatMap_raiseBit s hs]

theorem length_liftBits_le (s t : List ℕ) :
    (liftBits s).length ≤ (liftBits (s ++ t)).length := by
  simp [liftBits_append]

theorem length_liftBits_take_lt (s : List ℕ) (k k' : ℕ) (hk : k < k') (hk' : k' ≤ s.length) :
    (liftBits (s.take k)).length < (liftBits (s.take k')).length := by
  induction s generalizing k k' with
  | nil => simp at hk'; omega
  | cons a s ih =>
    cases k' with
    | zero => omega
    | succ k' =>
      cases k with
      | zero =>
        simp only [List.take_zero, List.take_succ_cons, liftBits, List.flatMap_nil,
          List.flatMap_cons, List.length_nil, List.length_append]
        unfold liftBit; split <;> simp
      | succ k =>
        have := ih k k' (by omega) (by simpa using hk')
        simp only [List.take_succ_cons, liftBits, List.flatMap_cons, List.length_append] at this ⊢
        omega

theorem liftBits_zero_pos (s : List ℕ) (j : ℕ) (h : (liftBits s)[j]? = some 0) :
    ∃ k, k < s.length ∧ s[k]? = some 0 ∧ (liftBits (s.take (k+1))).length = j+1 := by
  induction s generalizing j with
  | nil => simp [liftBits] at h
  | cons a s ih =>
    by_cases ha : a = 0
    · subst ha
      have hl : liftBits (0 :: s) = 1 :: 0 :: liftBits s := by simp [liftBits, liftBit]
      rw [hl] at h
      rcases j with _ | _ | j
      · simp at h
      · exact ⟨0, by simp, by simp, by simp [liftBits, liftBit]⟩
      · simp only [List.getElem?_cons_succ] at h
        obtain ⟨k, hk, hz, hlen⟩ := ih j h
        refine ⟨k+1, by simp; omega, by simpa using hz, ?_⟩
        simp only [List.take_succ_cons, liftBits, List.flatMap_cons, List.length_append] at hlen ⊢
        simp [liftBit] at hlen ⊢; omega
    · have hl : liftBits (a :: s) = 1 :: liftBits s := by simp [liftBits, liftBit, ha]
      rw [hl] at h
      rcases j with _ | j
      · simp at h
      · simp only [List.getElem?_cons_succ] at h
        obtain ⟨k, hk, hz, hlen⟩ := ih j h
        refine ⟨k+1, by simp; omega, by simpa using hz, ?_⟩
        simp only [List.take_succ_cons, liftBits, List.flatMap_cons, List.length_append] at hlen ⊢
        simp [liftBit, ha] at hlen ⊢; omega


open Googology.Notation.SSOS.Seq

theorem entry_append_left' (A B : List ℕ) (i : ℕ) (h1 : 1 ≤ i) (h : i ≤ A.length) :
    entry (A ++ B) i = entry A i := by
  simp only [entry]
  rw [List.getElem?_append_left (by omega)]

theorem entry_append_right' (A B : List ℕ) (i : ℕ) (h : A.length < i) :
    entry (A ++ B) i = entry B (i - A.length) := by
  simp only [entry]
  rw [List.getElem?_append_right (by omega)]
  congr 2; omega

theorem entry_mid (A B : List ℕ) (a : ℕ) : entry (A ++ a :: B) (A.length + 1) = a := by
  simp [entry]

/-- position in `E ++ raiseBits s` of the zero that precedes `raiseBits (s.drop k)` -/
def cp (E s : List ℕ) (k : ℕ) : ℕ := E.length + (liftBits (s.take k)).length

theorem raiseBits_split (s : List ℕ) (k : ℕ) :
    raiseBits s = liftBits (s.take k) ++ (liftBits (s.drop k) ++ [1]) := by
  rw [raiseBits_eq, ← List.append_assoc, ← liftBits_append, List.take_append_drop]

theorem drop_cp (E s : List ℕ) (k : ℕ) :
    (E ++ raiseBits s).drop (cp E s k) = raiseBits (s.drop k) := by
  rw [raiseBits_split s k, ← List.append_assoc, cp, ← List.length_append, List.drop_left,
    ← raiseBits_eq]

theorem suf_cp (E s : List ℕ) (k : ℕ) :
    suf (E ++ raiseBits s) (cp E s k + 1) = raiseBits (s.drop k) := by
  simp [suf, drop_cp]

theorem entry_cp_zero (E s : List ℕ) (hE : ∃ E0, E = E0 ++ [0,0]) :
    entry (E ++ raiseBits s) (cp E s 0) = 0 := by
  obtain ⟨E0, rfl⟩ := hE
  have h : E0 ++ [0,0] ++ raiseBits s = (E0 ++ [0]) ++ 0 :: raiseBits s := by simp
  rw [h, cp]
  convert entry_mid (E0 ++ [0]) (raiseBits s) 0 using 2
  simp [liftBits]

theorem entry_cp (E s : List ℕ) (k : ℕ) (_hk : k < s.length) (hz : s[k]? = some 0) :
    entry (E ++ raiseBits s) (cp E s (k+1)) = 0 := by
  have htake : s.take (k+1) = s.take k ++ [0] := by
    rw [List.take_add_one, hz]; rfl
  have hl : liftBits (s.take (k+1)) = liftBits (s.take k) ++ [1,0] := by
    rw [htake, liftBits_append]; rfl
  have hS : E ++ raiseBits s =
      (E ++ liftBits (s.take k) ++ [1]) ++ 0 :: (liftBits (s.drop (k+1)) ++ [1]) := by
    rw [raiseBits_split s (k+1), hl]; simp
  rw [hS, cp, hl]
  convert entry_mid (E ++ liftBits (s.take k) ++ [1]) (liftBits (s.drop (k+1)) ++ [1]) 0 using 2
  simp; omega

theorem entry_E_pred (E s : List ℕ) (hE : ∃ E0, E = E0 ++ [0,0]) :
    entry (E ++ raiseBits s) (E.length - 1) = 0 := by
  obtain ⟨E0, rfl⟩ := hE
  have h : E0 ++ [0,0] ++ raiseBits s = E0 ++ 0 :: (0 :: raiseBits s) := by simp
  rw [h]
  convert entry_mid E0 (0 :: raiseBits s) 0 using 2
  simp

theorem drop_E_pred (E s : List ℕ) (hE : ∃ E0, E = E0 ++ [0,0]) :
    (E ++ raiseBits s).drop (E.length - 1) = 0 :: raiseBits s := by
  obtain ⟨E0, rfl⟩ := hE
  have h : E0 ++ [0,0] ++ raiseBits s = (E0 ++ [0]) ++ (0 :: raiseBits s) := by simp
  rw [h]
  convert (List.drop_left (l₁ := E0 ++ [0]) (l₂ := 0 :: raiseBits s)) using 2
  simp

theorem cp_lt_cp (E s : List ℕ) (k k' : ℕ) (hk : k < k') (hk' : k' ≤ s.length) :
    cp E s k < cp E s k' := by
  have := length_liftBits_take_lt s k k' hk hk'
  simp only [cp]; omega

theorem cp_lt_length (E s : List ℕ) (k : ℕ) :
    cp E s k < (E ++ raiseBits s).length := by
  have h : (liftBits (s.take k)).length ≤ (liftBits s).length := by
    conv_rhs => rw [← List.take_append_drop k s]
    exact length_liftBits_le _ _
  simp [cp, raiseBits_eq]; omega

theorem onesAfter_cp (E s : List ℕ) (hs : Binary s) (k : ℕ) :
    onesAfter (E ++ raiseBits s) (cp E s k) = oneRun (s.drop k) + 1 := by
  rw [onesAfter, suf_cp, oneRun_raiseBits _ (binary_drop s hs k)]

theorem onesAfter_E_pred (E s : List ℕ) (hE : ∃ E0, E = E0 ++ [0,0]) :
    onesAfter (E ++ raiseBits s) (E.length - 1) = 0 := by
  rw [onesAfter, suf, Nat.add_sub_cancel, drop_E_pred E s hE]
  simp [oneRun]

/-- every zero of `E ++ raiseBits s` after `|E|` is some `cp E s (k+1)` with `s[k] = 0` -/
theorem zero_cover (E s : List ℕ) (i : ℕ)
    (hgt : E.length < i) (hiL : i < (E ++ raiseBits s).length)
    (hz : entry (E ++ raiseBits s) i = 0) :
    ∃ k, k < s.length ∧ s[k]? = some 0 ∧ i = cp E s (k+1) := by
  rw [entry_append_right' _ _ _ hgt, raiseBits_eq] at hz
  have hlen : i - E.length ≤ (liftBits s).length := by
    simp [raiseBits_eq] at hiL; omega
  have hz' : (liftBits s)[i - E.length - 1]? = some 0 := by
    simp only [entry] at hz
    rw [List.getElem?_append_left (by omega)] at hz
    rw [List.getElem?_eq_getElem (by omega)] at hz ⊢
    simpa using hz
  obtain ⟨k, hk, hk0, hkl⟩ := liftBits_zero_pos s _ hz'
  exact ⟨k, hk, hk0, by simp only [cp]; omega⟩


theorem entry_S'_ge3 (s : List ℕ) (m : ℕ) (h : 3 ≤ m) :
    entry ([0,0] ++ s) m = (s[m-3]?).getD 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
  simp [entry]

theorem drop_S' (s : List ℕ) (m : ℕ) (h : 2 ≤ m) : ([0,0] ++ s).drop m = s.drop (m-2) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  simp

def cpos (E s : List ℕ) (m : ℕ) : ℕ := if m ≤ 1 then E.length - 1 else cp E s (m-2)

theorem len_E (E : List ℕ) (hE : ∃ E0, E = E0 ++ [0,0]) : 2 ≤ E.length := by
  obtain ⟨E0, rfl⟩ := hE; simp

theorem cpos_zero (E s : List ℕ) (hE : ∃ E0, E = E0 ++ [0,0]) (m : ℕ) (h1 : 1 ≤ m)
    (hm : m ≤ ([0,0] ++ s).length) (hz : entry ([0,0] ++ s) m = 0) :
    entry (E ++ raiseBits s) (cpos E s m) = 0 ∧ cpos E s m < (E ++ raiseBits s).length := by
  rcases (show m = 1 ∨ m = 2 ∨ 3 ≤ m by omega) with rfl | rfl | h3
  · refine ⟨by simpa [cpos] using entry_E_pred E s hE, ?_⟩
    have h2 := len_E E hE
    have h3 : 1 ≤ (raiseBits s).length := by simp [raiseBits]
    simp only [cpos, le_refl, if_true, List.length_append]; omega
  · exact ⟨by simpa [cpos] using entry_cp_zero E s hE, by simpa [cpos] using cp_lt_length E s 0⟩
  · have hm3 : m - 3 < s.length := by simp at hm; omega
    rw [entry_S'_ge3 s m h3, List.getElem?_eq_getElem hm3] at hz
    have hz' : s[m-3]? = some 0 := by rw [List.getElem?_eq_getElem hm3]; simpa using hz
    have hc : cpos E s m = cp E s (m - 3 + 1) := by
      simp only [cpos]; rw [if_neg (by omega)]; congr 1; omega
    rw [hc]
    exact ⟨entry_cp E s (m-3) hm3 hz', cp_lt_length E s _⟩

theorem cpos_cover (E s : List ℕ) (hE : ∃ E0, E = E0 ++ [0,0]) (i : ℕ)
    (hi1 : E.length - 1 ≤ i) (hiL : i < (E ++ raiseBits s).length)
    (hz : entry (E ++ raiseBits s) i = 0) :
    ∃ m, 1 ≤ m ∧ m ≤ ([0,0] ++ s).length ∧ entry ([0,0] ++ s) m = 0 ∧ cpos E s m = i := by
  have h2 := len_E E hE
  rcases (show i = E.length - 1 ∨ i = E.length ∨ E.length < i by omega) with h | h | h
  · exact ⟨1, le_rfl, by simp, by simp [entry], by simp [cpos, h]⟩
  · exact ⟨2, by omega, by simp, by simp [entry], by simp [cpos, cp, liftBits, h]⟩
  · obtain ⟨k, hk, hk0, hi⟩ := zero_cover E s i h hiL hz
    refine ⟨k+3, by omega, by simp; omega, ?_, ?_⟩
    · rw [entry_S'_ge3 s _ (by omega)]; simp [hk0]
    · simp [cpos, hi]

theorem cpos_lt (E s : List ℕ) (hE : ∃ E0, E = E0 ++ [0,0]) (m m' : ℕ) (h1 : 1 ≤ m)
    (h : m < m') (hm' : m' ≤ ([0,0] ++ s).length) : cpos E s m < cpos E s m' := by
  have h2 := len_E E hE
  by_cases hm : m ≤ 1
  · have : cpos E s m = E.length - 1 := by simp [cpos, hm]
    rw [this]; simp only [cpos]; rw [if_neg (by omega)]; simp only [cp]; omega
  · simp only [cpos]; rw [if_neg hm, if_neg (by omega)]
    exact cp_lt_cp E s _ _ (by omega) (by simp at hm'; omega)

theorem cpos_le (E s : List ℕ) (hE : ∃ E0, E = E0 ++ [0,0]) (m m' : ℕ) (h1 : 1 ≤ m)
    (h : m ≤ m') (hm' : m' ≤ ([0,0] ++ s).length) : cpos E s m ≤ cpos E s m' := by
  rcases Nat.lt_or_eq_of_le h with h | rfl
  · exact (cpos_lt E s hE m m' h1 h hm').le
  · exact le_rfl

theorem cpos_lt_iff (E s : List ℕ) (hE : ∃ E0, E = E0 ++ [0,0]) (m m' : ℕ) (h1 : 1 ≤ m)
    (h1' : 1 ≤ m') (hm : m ≤ ([0,0] ++ s).length) (hm' : m' ≤ ([0,0] ++ s).length) :
    cpos E s m < cpos E s m' ↔ m < m' := by
  constructor
  · intro hc; by_contra hn
    exact absurd hc (not_lt.2 (cpos_le E s hE m' m h1' (by omega) hm))
  · intro h; exact cpos_lt E s hE m m' h1 h hm'

theorem cpos_onesAfter_one (E s : List ℕ) (hE : ∃ E0, E = E0 ++ [0,0]) :
    onesAfter (E ++ raiseBits s) (cpos E s 1) = 0 := by
  simpa [cpos] using onesAfter_E_pred E s hE

theorem onesAfter_S'_one (s : List ℕ) : onesAfter ([0,0] ++ s) 1 = 0 := by
  simp [onesAfter, suf, oneRun]

theorem cpos_onesAfter (E s : List ℕ) (hs : Binary s) (m : ℕ) (h2 : 2 ≤ m) :
    onesAfter (E ++ raiseBits s) (cpos E s m) = onesAfter ([0,0] ++ s) m + 1 := by
  simp only [cpos]; rw [if_neg (by omega), onesAfter_cp E s hs]
  simp only [onesAfter, suf, Nat.add_sub_cancel, drop_S' s m h2]

theorem cpos_suf (E s : List ℕ) (m : ℕ) (h2 : 2 ≤ m) :
    suf (E ++ raiseBits s) (cpos E s m + 1) = raiseBits (suf ([0,0] ++ s) (m+1)) := by
  simp only [cpos]; rw [if_neg (by omega), suf_cp]
  simp only [suf, Nat.add_sub_cancel, drop_S' s m h2]

theorem cpos_suf_one (E s : List ℕ) (hE : ∃ E0, E = E0 ++ [0,0]) :
    suf (E ++ raiseBits s) (cpos E s 1 + 1) = 0 :: raiseBits s := by
  have h2 := len_E E hE
  simp only [cpos, le_refl, if_true, suf, Nat.add_sub_cancel]
  exact drop_E_pred E s hE


theorem cpos_one_le (E s : List ℕ) (hE : ∃ E0, E = E0 ++ [0,0]) (m : ℕ) (h1 : 1 ≤ m)
    (hm : m ≤ ([0,0] ++ s).length) : E.length - 1 ≤ cpos E s m := by
  have := cpos_le E s hE 1 m le_rfl h1 hm
  simpa [cpos] using this

theorem binary_suf' (S : List ℕ) (hb : Binary S) (i : ℕ) : Binary (suf S i) :=
  fun n hn => hb n (List.mem_of_mem_drop hn)

section transfer
variable (E s : List ℕ) (hE : ∃ E0, E = E0 ++ [0,0]) (hs : Binary s)
  (hS : BinaryLimit (E ++ raiseBits s)) (hS' : BinaryLimit ([0,0] ++ s))
include hE hs hS hS'

omit hs in
theorem p_one_transfer : p (E ++ raiseBits s) 1 = cpos E s (p ([0,0] ++ s) 1) := by
  have sp := p_one_spec_binary _ hS
  have sp' := p_one_spec_binary _ hS'
  have cz := cpos_zero E s hE _ (by omega) sp'.2.1.le sp'.2.2.1
  have h1 := cpos_one_le E s hE _ (by omega) sp'.2.1.le
  have h2 := len_E E hE
  apply le_antisymm
  · by_cases hlow : p (E ++ raiseBits s) 1 < E.length - 1
    · omega
    · obtain ⟨m, hm1, hmL, hmz, hmc⟩ :=
        cpos_cover E s hE _ (by omega) sp.2.1 sp.2.2.1
      have hmlt : m < ([0,0] ++ s).length := by
        rcases Nat.lt_or_eq_of_le hmL with h | h
        · exact h
        · rw [h, hS'.last] at hmz; contradiction
      rw [← hmc]
      exact cpos_le E s hE _ _ hm1 (sp'.2.2.2 m hm1 hmlt hmz) sp'.2.1.le
  · exact sp.2.2.2 _ (by omega) cz.2 cz.1

theorem p_two_transfer : p (E ++ raiseBits s) 2 = cpos E s (p ([0,0] ++ s) 2) := by
  have sp := p_one_spec_binary _ hS
  have sp' := p_one_spec_binary _ hS'
  have sq := p_two_short_zero_spec _ hS
  have sq' := p_two_short_zero_spec _ hS'
  have hp1 := p_one_transfer E s hE hS hS'
  have h2 := len_E E hE
  have hLS' := sp'.2.1
  have hone : onesAfter (E ++ raiseBits s) (p (E ++ raiseBits s) 1) =
      onesAfter ([0,0] ++ s) (p ([0,0] ++ s) 1) + 1 := by
    rw [hp1]; exact cpos_onesAfter E s hs _ sp'.1
  have hpos' : 1 ≤ onesAfter ([0,0] ++ s) (p ([0,0] ++ s) 1) := by
    rw [onesAfter_p_one _ hS']; omega
  apply le_antisymm
  · by_cases hlow : p (E ++ raiseBits s) 2 < E.length - 1
    · have := cpos_one_le E s hE _ sq'.1 (by omega)
      omega
    · obtain ⟨m, hm1, hmL, hmz, hmc⟩ :=
        cpos_cover E s hE _ (by omega) (by omega) sq.2.2.1
      have hmlt : m < ([0,0] ++ s).length := by
        rcases Nat.lt_or_eq_of_le hmL with h | h
        · exact h
        · rw [h, hS'.last] at hmz; contradiction
      have hm1' : m < p ([0,0] ++ s) 1 := by
        have : cpos E s m < cpos E s (p ([0,0] ++ s) 1) := by rw [hmc, ← hp1]; exact sq.2.1
        exact (cpos_lt_iff E s hE _ _ hm1 (by omega) hmL sp'.2.1.le).1 this
      have hrun : onesAfter ([0,0] ++ s) m < onesAfter ([0,0] ++ s) (p ([0,0] ++ s) 1) := by
        by_cases hm2 : m = 1
        · subst hm2; rw [onesAfter_S'_one]; omega
        · have h := sq.2.2.2.1
          rw [← hmc, cpos_onesAfter E s hs m (by omega), hone] at h
          omega
      rw [← hmc]
      exact cpos_le E s hE _ _ hm1 (sq'.2.2.2.2 m hm1 hm1' hmz hrun) (by omega)
  · have hq1 := sq'.1
    have cz := cpos_zero E s hE _ hq1 (by omega) sq'.2.2.1
    have hc1 := cpos_one_le E s hE _ hq1 (by omega)
    apply sq.2.2.2.2 _ (by omega) _ cz.1
    · by_cases hq : p ([0,0] ++ s) 2 = 1
      · rw [hq, cpos_onesAfter_one E s hE, hone]; omega
      · rw [cpos_onesAfter E s hs _ (by omega), hone]; have := sq'.2.2.2.1; omega
    · rw [hp1]; exact cpos_lt E s hE _ _ hq1 sq'.2.1 sp'.2.1.le

theorem argmax_transfer (r' : ℕ) (h : IsZeroArgmax ([0,0] ++ s) (p ([0,0] ++ s) 2) r')
    (hr' : 2 ≤ r') :
    IsZeroArgmax (E ++ raiseBits s) (p (E ++ raiseBits s) 2) (cpos E s r') := by
  obtain ⟨hqr, hrL, hrz, hmax⟩ := h
  have hp2 := p_two_transfer E s hE hs hS hS'
  have sq' := p_two_short_zero_spec _ hS'
  have cz := cpos_zero E s hE r' (by omega) hrL.le hrz
  have h2 := len_E E hE
  refine ⟨?_, cz.2, cz.1, ?_⟩
  · rw [hp2]; exact cpos_le E s hE _ _ sq'.1 hqr hrL.le
  · intro j hj hjL hjz
    have hc1 := cpos_one_le E s hE _ sq'.1 (by omega)
    obtain ⟨m, hm1, hmL, hmz, hmc⟩ := cpos_cover E s hE j (by rw [hp2] at hj; omega) hjL hjz
    have hmlt : m < ([0,0] ++ s).length := by
      rcases Nat.lt_or_eq_of_le hmL with h | h
      · exact h
      · rw [h, hS'.last] at hmz; contradiction
    have hqm : p ([0,0] ++ s) 2 ≤ m := by
      by_contra hn
      have := cpos_lt E s hE m (p ([0,0] ++ s) 2) hm1 (by omega) (by omega)
      rw [hmc, ← hp2] at this; omega
    obtain ⟨hle, heq⟩ := hmax m hqm hmlt hmz
    have hrsuf := cpos_suf E s r' hr'
    subst hmc
    by_cases hm2 : m = 1
    · subst hm2
      rw [cpos_suf_one E s hE, hrsuf]
      have hlt : (0 :: raiseBits s) < raiseBits (suf ([0,0] ++ s) (r'+1)) := by
        simp [raiseBits, List.cons_lt_cons_iff]
      exact ⟨hlt.le, fun he => absurd he (ne_of_lt hlt)⟩
    · have hb := binary_suf' _ hS'.binary
      rw [cpos_suf E s m (by omega), hrsuf]
      refine ⟨(raiseBits_le_iff _ _ (hb _) (hb _)).2 hle, fun he => ?_⟩
      exact cpos_le E s hE _ _ hm1 (heq (raiseBits_inj _ _ (hb _) (hb _) he)) hrL.le

end transfer


/-- every suffix that follows a zero is lexicographically smaller than the whole list -/
def Dom (s : List ℕ) : Prop := ∀ x y, s = x ++ 0 :: y → y < s

theorem argmax_base (E s : List ℕ) (hE : ∃ E0, E = E0 ++ [0,0]) (hs : Binary s)
    (hS : BinaryLimit (E ++ raiseBits s)) (hshape : s = [] ∨ ∃ s0, s = s0 ++ [0])
    (hdom : Dom s) :
    IsZeroArgmax (E ++ raiseBits s) (p (E ++ raiseBits s) 2) E.length := by
  have sp := p_one_spec_binary _ hS
  have sq := p_two_short_zero_spec _ hS
  have h2 := len_E E hE
  have hlen : (E ++ raiseBits s).length = E.length + (liftBits s).length + 1 := by
    simp [raiseBits_eq]; omega
  have hlast0 : entry (E ++ raiseBits s) ((E ++ raiseBits s).length - 1) = 0 := by
    rcases hshape with rfl | ⟨s0, rfl⟩
    · have := entry_cp_zero E [] hE
      simpa [cp, liftBits, raiseBits] using this
    · have hk : s0.length < (s0 ++ [0]).length := by simp
      have := entry_cp E (s0 ++ [0]) s0.length hk (by simp)
      convert this using 2
      rw [hlen, cp, List.take_of_length_le (by simp)]; omega
  have hp1 : p (E ++ raiseBits s) 1 = (E ++ raiseBits s).length - 1 := by
    have := sp.2.2.2 _ (by omega) (by omega) hlast0
    omega
  have hone : onesAfter (E ++ raiseBits s) (p (E ++ raiseBits s) 1) = 1 := by
    rw [onesAfter_p_one _ hS]; omega
  have hlow : E.length - 1 ≤ p (E ++ raiseBits s) 2 := by
    apply sq.2.2.2.2 _ (by omega) (by omega) (entry_E_pred E s hE)
    rw [onesAfter_E_pred E s hE, hone]; omega
  have hup : p (E ++ raiseBits s) 2 ≤ E.length := by
    by_contra hn
    obtain ⟨m, hm1, hmL, hmz, hmc⟩ :=
      cpos_cover E s hE _ (by omega) (by omega) sq.2.2.1
    have hm2 : 2 ≤ m := by
      by_contra h1
      have : m = 1 := by omega
      subst this; simp [cpos] at hmc; omega
    have h := sq.2.2.2.1
    rw [← hmc, cpos_onesAfter E s hs m hm2, hone] at h
    omega
  have hE0 : cp E s 0 = E.length := by simp [cp, liftBits]
  have hsufE : suf (E ++ raiseBits s) (E.length + 1) = raiseBits s := by
    simpa [hE0] using suf_cp E s 0
  refine ⟨hup, by simpa [hE0] using cp_lt_length E s 0,
    by simpa [hE0] using entry_cp_zero E s hE, ?_⟩
  intro j hj hjL hjz
  obtain ⟨m, hm1, hmL, hmz, hmc⟩ := cpos_cover E s hE j (by omega) hjL hjz
  subst hmc
  rcases (show m = 1 ∨ m = 2 ∨ 3 ≤ m by omega) with rfl | rfl | h3
  · rw [cpos_suf_one E s hE, hsufE]
    have hlt : (0 :: raiseBits s) < raiseBits s := by
      simp [raiseBits, List.cons_lt_cons_iff]
    exact ⟨hlt.le, fun he => absurd he (ne_of_lt hlt)⟩
  · have : cpos E s 2 = E.length := by simp [cpos, hE0]
    rw [this]; exact ⟨le_rfl, fun _ => le_rfl⟩
  · have hm3 : m - 3 < s.length := by simp at hmL; omega
    rw [entry_S'_ge3 s m h3, List.getElem?_eq_getElem hm3] at hmz
    have hz : s[m-3] = 0 := by simpa using hmz
    have hdec : s = s.take (m-3) ++ 0 :: s.drop (m-2) := by
      conv_lhs => rw [← List.take_append_drop (m-3) s]
      rw [List.drop_eq_getElem_cons hm3, hz, show m - 3 + 1 = m - 2 by omega]
    have hlt := hdom _ _ hdec
    have hsuf : suf ([0,0] ++ s) (m+1) = s.drop (m-2) := by
      simp only [suf, Nat.add_sub_cancel, drop_S' s m (by omega)]
    rw [cpos_suf E s m (by omega), hsufE, hsuf]
    have hlt' := (raiseBits_lt_iff _ _ (binary_drop s hs _) hs).2 hlt
    exact ⟨hlt'.le, fun he => absurd he (ne_of_lt hlt')⟩

theorem encode_block (u P : List U) : encode (.b u :: P) = encode P ++ raiseBits (flat u) := by
  simp [encode]

theorem blockGap_tail (P : List U) (h : BlockGap P) : ∃ E0, encode P = E0 ++ [0,0] := by
  unfold BlockGap at h
  match P, h with
  | [], _ => exact ⟨[], by simp [encode]⟩
  | [.z], _ => exact ⟨[0], by simp [encode]⟩
  | .z :: .z :: Q, _ => exact ⟨[0,0] ++ flat Q, by simp [encode]⟩


theorem cpos_parts (E : List ℕ) (w rest : List U) :
    cpos E (flat (.b w :: rest)) (encode rest ++ (parts w).1).length =
      (E ++ (parts (.b w :: rest)).1).length := by
  have horig := parts_original w
  have hs : flat (.b w :: rest) = flat rest ++ (parts w).1 ++ ((parts w).2 ++ [1]) := by
    rw [flat_b, horig]; simp [List.append_assoc]
  have hlen : (encode rest ++ (parts w).1).length = (flat rest ++ (parts w).1).length + 2 := by
    simp [encode]
  rw [hlen]
  simp only [cpos]
  rw [if_neg (by omega), Nat.add_sub_cancel, cp, hs, List.take_left]
  simp [parts, liftBits_append]

theorem cutCorrect_block (w rest : List U) (ih : CutCorrect w rest)
    (P : List U) (hP : BlockGap P) : CutCorrect (.b w :: rest) P := by
  have hS' := binaryLimit_encode_block w rest
  rw [cutCorrect_iff_shortZero_argmax, ← p_two_binary _ hS'] at ih
  rw [cutCorrect_iff_shortZero_argmax, ← p_two_binary _ (binaryLimit_encode_block _ _),
    encode_block]
  have hS := binaryLimit_encode_block (.b w :: rest) P
  rw [encode_block] at hS
  have henc : encode (.b w :: rest) = [0,0] ++ flat (.b w :: rest) := rfl
  rw [henc] at ih hS'
  have hr' : 2 ≤ (encode rest ++ (parts w).1).length := by simp [encode]
  have := argmax_transfer (encode P) (flat (.b w :: rest)) (blockGap_tail P hP)
    (binary_flat _) hS hS' _ ih hr'
  rwa [cpos_parts] at this

theorem cutCorrect_of_stdShape_of_dom (hdom : ∀ t, StdShape t → Dom (flat t)) :
    ∀ u, StdShape u → ∀ P, BlockGap P → CutCorrect u P := by
  intro u hu
  induction hu with
  | nil =>
    intro P hP
    rw [cutCorrect_iff_shortZero_argmax, ← p_two_binary _ (binaryLimit_encode_block _ _),
      encode_block]
    have := argmax_base (encode P) [] (blockGap_tail P hP) (by intro n hn; simp at hn)
      (by simpa [encode_block] using binaryLimit_encode_block [] P) (Or.inl rfl)
      (by intro x y h; simp at h)
    simpa [parts] using this
  | @zero t ht ih =>
    intro P hP
    rw [cutCorrect_iff_shortZero_argmax, ← p_two_binary _ (binaryLimit_encode_block _ _),
      encode_block]
    have := argmax_base (encode P) (flat (.z :: t)) (blockGap_tail P hP)
      (binary_flat _) (by simpa [encode_block] using binaryLimit_encode_block (.z :: t) P)
      (Or.inr ⟨flat t, by simp⟩) (hdom _ (.zero ht))
    simpa [parts] using this
  | @single w hw ihw =>
    intro P hP
    exact cutCorrect_block w [] (ihw [] trivial) P hP
  | @next w v Q hw hQ hcmp ihw ihQ =>
    intro P hP
    exact cutCorrect_block w _ (ihw (.z :: .z :: .b v :: Q) (by simp [BlockGap])) P hP


/-! ## Dom for StdShape forests -/

def AfterZeroOne (B : List ℕ) : Prop := ∀ x y, B = x ++ 0 :: y → ∃ y', y = 1 :: y'

def Blk (B : List ℕ) : Prop := (∃ B', B = 1 :: B') ∧ AfterZeroOne B ∧ Dom B

def Low (T : List ℕ) : Prop := T = [] ∨ T = [0] ∨ ∃ R, T = 0 :: 0 :: R

theorem afterZeroOne_tail {b : ℕ} {B : List ℕ} (h : AfterZeroOne (b :: B)) : AfterZeroOne B :=
  fun x y hx => h (b :: x) y (by simp [hx])

theorem lt_append_of_lt (y B T T' : List ℕ) (hlt : y < B) (hB : AfterZeroOne B)
    (hT : Low T) : y ++ T < B ++ T' := by
  induction y generalizing B with
  | nil =>
    cases B with
    | nil => exact absurd hlt (List.not_lt_nil _)
    | cons b B' =>
      simp only [List.nil_append, List.cons_append]
      by_cases hb : b = 0
      · subst hb
        obtain ⟨y', hy'⟩ := hB [] B' rfl
        subst hy'
        rcases hT with rfl | rfl | ⟨R, rfl⟩ <;> simp [List.cons_lt_cons_iff]
      · have hb' : 0 < b := Nat.pos_of_ne_zero hb
        rcases hT with rfl | rfl | ⟨R, rfl⟩ <;> simp [List.cons_lt_cons_iff, hb']
  | cons a y ih =>
    cases B with
    | nil => exact absurd hlt (List.not_lt_nil _)
    | cons b B' =>
      rw [List.cons_lt_cons_iff] at hlt
      simp only [List.cons_append, List.cons_lt_cons_iff]
      rcases hlt with h | ⟨rfl, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨rfl, ih B' h (afterZeroOne_tail hB)⟩

theorem lt_append_nonempty (p q : List ℕ) (hq : q ≠ []) : p < p ++ q := by
  obtain ⟨a, q, rfl⟩ := List.exists_cons_of_ne_nil hq
  simpa using List.Lex.append_left (· < ·) (List.nil_lt_cons a q) p

theorem dom_replicate (e : ℕ) : Dom (List.replicate e 0) := by
  intro x y h
  have hy : ∀ n ∈ y, n = 0 := by
    intro n hn
    have : n ∈ List.replicate e 0 := by rw [h]; simp [hn]
    exact List.eq_of_mem_replicate this
  have hlen : y.length < e := by
    have := congrArg List.length h; simp at this; omega
  rw [List.eq_replicate_of_mem hy]
  have : List.replicate e 0 = List.replicate y.length 0 ++ List.replicate (e - y.length) 0 := by
    rw [List.replicate_append_replicate]; congr; omega
  rw [this]
  exact lt_append_nonempty _ _ (by simp; omega)

theorem lt_one_cons (y R : List ℕ) (hy : y = [] ∨ ∃ y', y = 0 :: y') : y < 1 :: R := by
  rcases hy with rfl | ⟨y', rfl⟩
  · exact List.nil_lt_cons _ _
  · simp [List.cons_lt_cons_iff]

def W : List (List ℕ) → ℕ → List ℕ
  | [], e => List.replicate e 0
  | [B], e => B ++ List.replicate e 0
  | B :: C :: Bs, e => B ++ 0 :: 0 :: W (C :: Bs) e

def tl (Bs : List (List ℕ)) (e : ℕ) : List ℕ :=
  match Bs with
  | [] => List.replicate e 0
  | C :: Cs => 0 :: 0 :: W (C :: Cs) e

theorem W_cons (B : List ℕ) (Bs : List (List ℕ)) (e : ℕ) : W (B :: Bs) e = B ++ tl Bs e := by
  cases Bs <;> rfl

theorem low_tl (Bs : List (List ℕ)) (e : ℕ) : Low (tl Bs e) := by
  cases Bs with
  | nil =>
    rcases e with _ | _ | e
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨List.replicate e 0, by simp [tl, List.replicate_succ]⟩)
  | cons C Cs => exact Or.inr (Or.inr ⟨_, rfl⟩)

def Desc : List (List ℕ) → Prop
  | [] => True
  | [_] => True
  | B :: C :: Bs => C ≤ B ∧ Desc (C :: Bs)

theorem replicate_lt (e : ℕ) (R : List ℕ) : List.replicate e 0 < 0 :: 0 :: 1 :: R := by
  rcases e with _ | _ | _ | e <;> simp [List.replicate_succ, List.cons_lt_cons_iff]

theorem W_lt (e : ℕ) : ∀ (Bs : List (List ℕ)) (B C : List ℕ), Desc (B :: C :: Bs) →
    (∀ X ∈ B :: C :: Bs, Blk X) → W (C :: Bs) e < W (B :: C :: Bs) e := by
  intro Bs
  induction Bs with
  | nil =>
    intro B C hD hB
    have hCB : C ≤ B := hD.1
    have hBk := hB B (by simp)
    have hCk := hB C (by simp)
    show C ++ List.replicate e 0 < B ++ 0 :: 0 :: (C ++ List.replicate e 0)
    rcases lt_or_eq_of_le hCB with hlt | rfl
    · exact lt_append_of_lt _ _ _ _ hlt hBk.2.1 (low_tl [] e)
    · obtain ⟨C', rfl⟩ := hCk.1
      exact List.Lex.append_left (· < ·) (replicate_lt e _) _
  | cons D Ds ih =>
    intro B C hD hB
    have hCB : C ≤ B := hD.1
    have hBk := hB B (by simp)
    rw [W_cons C, show W (B :: C :: D :: Ds) e = B ++ 0 :: 0 :: W (C :: D :: Ds) e from rfl]
    rcases lt_or_eq_of_le hCB with hlt | rfl
    · exact lt_append_of_lt _ _ _ _ hlt hBk.2.1 (low_tl _ e)
    · apply List.Lex.append_left (· < ·)
      show 0 :: 0 :: W (D :: Ds) e < 0 :: 0 :: W (C :: D :: Ds) e
      simp only [List.cons_lt_cons_iff, lt_irrefl, false_or, true_and]
      exact ih C D hD.2 (fun X hX => hB X (List.mem_cons_of_mem _ hX))

theorem dom_W (e : ℕ) : ∀ Bs : List (List ℕ), Desc Bs → (∀ B ∈ Bs, Blk B) → Dom (W Bs e) := by
  intro Bs
  induction Bs with
  | nil => intro _ _; exact dom_replicate e
  | cons B Bs ih =>
    intro hD hB x y h
    have hBk := hB B (by simp)
    obtain ⟨⟨B', hB'⟩, haz, hdom⟩ := hBk
    rw [W_cons] at h ⊢
    rcases List.append_eq_append_iff.mp h with ⟨a', _, hT⟩ | ⟨c', hBx, hy⟩
    · -- the zero lies in the tail
      cases Bs with
      | nil =>
        have hy0 : ∀ n ∈ y, n = 0 := by
          intro n hn
          have : n ∈ List.replicate e 0 := by
            change n ∈ tl [] e; rw [hT]; simp [hn]
          exact List.eq_of_mem_replicate this
        rw [hB']
        apply lt_one_cons
        cases y with
        | nil => exact Or.inl rfl
        | cons n y => exact Or.inr ⟨y, by rw [hy0 n (by simp)]⟩
      | cons C Cs =>
        change 0 :: 0 :: W (C :: Cs) e = a' ++ 0 :: y at hT
        rcases a' with _ | ⟨a1, _ | ⟨a2, a''⟩⟩
        · simp at hT
          rw [hB', ← hT]
          exact lt_one_cons _ _ (Or.inr ⟨_, rfl⟩)
        · simp at hT
          obtain ⟨-, hW⟩ := hT
          rw [← hW]
          have := W_lt e Cs B C hD hB
          rwa [W_cons B] at this
        · simp at hT
          obtain ⟨-, -, hW⟩ := hT
          have hD' : Desc (C :: Cs) := by cases Cs <;> exact hD.2
          have hlt1 := ih hD' (fun X hX => hB X (List.mem_cons_of_mem _ hX)) a'' y hW
          have hlt2 := W_lt e Cs B C hD hB
          rw [W_cons B] at hlt2
          exact hlt1.trans hlt2
    · rcases c' with _ | ⟨c, c''⟩
      · -- the zero is the first entry of the tail
        simp at hy
        rw [hB']
        apply lt_one_cons
        rcases low_tl Bs e with h0 | h0 | ⟨R, h0⟩
        · rw [h0] at hy; simp at hy
        · rw [h0] at hy; simp at hy; exact Or.inl hy
        · rw [h0] at hy; simp at hy; exact Or.inr ⟨R, hy⟩
      · -- the zero lies inside B
        simp at hy
        obtain ⟨rfl, rfl⟩ := hy
        exact lt_append_of_lt _ _ _ _ (hdom x c'' hBx) haz (low_tl Bs e)

theorem flatMap_raiseBit_zero (c x y : List ℕ) (hc : Binary c)
    (h : c.flatMap raiseBit = x ++ 0 :: y) : ∃ x' y', c = x' ++ 0 :: y' ∧ y = raiseBits y' := by
  induction c generalizing x with
  | nil => simp at h
  | cons a c ih =>
    have ha := hc a (by simp)
    have hc' : Binary c := fun k hk => hc k (List.mem_cons_of_mem _ hk)
    rcases ha with rfl | rfl
    · simp only [List.flatMap_cons, raiseBit] at h
      rcases x with _ | ⟨x1, _ | ⟨x2, xs⟩⟩
      · simp at h; exact ⟨[], c, rfl, by rw [← h]; rfl⟩
      · simp at h
      · simp at h
        obtain ⟨-, -, h⟩ := h
        obtain ⟨x', y', hc'', hy⟩ := ih xs hc' h
        exact ⟨0 :: x', y', by simp [hc''], hy⟩
    · simp only [List.flatMap_cons, raiseBit, if_neg one_ne_zero, List.cons_append,
        List.nil_append] at h
      rcases x with _ | ⟨x1, xs⟩
      · simp at h
      · simp at h
        obtain ⟨-, h⟩ := h
        obtain ⟨x', y', hc'', hy⟩ := ih xs hc' h
        exact ⟨1 :: x', y', by simp [hc''], hy⟩

theorem raiseBits_zero (c x y : List ℕ) (hc : Binary c) (h : raiseBits c = x ++ 0 :: y) :
    ∃ x' y', c = x' ++ 0 :: y' ∧ y = raiseBits y' := by
  rcases x with _ | ⟨x1, xs⟩
  · simp [raiseBits] at h
  · simp only [raiseBits, List.cons_append, List.cons.injEq] at h
    exact flatMap_raiseBit_zero c xs y hc h.2

theorem blk_raiseBits (c : List ℕ) (hc : Binary c) (hd : Dom c) : Blk (raiseBits c) := by
  refine ⟨⟨_, rfl⟩, ?_, ?_⟩
  · intro x y h
    obtain ⟨x', y', -, rfl⟩ := raiseBits_zero c x y hc h
    exact ⟨_, rfl⟩
  · intro x y h
    obtain ⟨x', y', hc', rfl⟩ := raiseBits_zero c x y hc h
    have hy' : Binary y' := fun n hn => hc n (by rw [hc']; simp [hn])
    exact (raiseBits_lt_iff _ _ hy' hc).2 (hd x' y' hc')

theorem W_succ : ∀ (Bs : List (List ℕ)) (e : ℕ), W Bs (e+1) = W Bs e ++ [0]
  | [], e => by simp [W, List.replicate_succ']
  | [B], e => by simp [W, List.replicate_succ']
  | B :: C :: Bs, e => by simp [W, W_succ (C :: Bs) e]

theorem W_snoc : ∀ (Bs : List (List ℕ)) (U : List ℕ), Bs ≠ [] →
    W (Bs ++ [U]) 0 = W Bs 0 ++ 0 :: 0 :: U
  | [], _, h => absurd rfl h
  | [B], U, _ => by simp [W]
  | B :: C :: Bs, U, _ => by
    simp only [List.cons_append, W]
    rw [← List.cons_append, W_snoc (C :: Bs) U (by simp)]
    simp

theorem desc_snoc : ∀ (Bs : List (List ℕ)) (U V : List ℕ), Desc Bs →
    Bs.getLast? = some V → U ≤ V → Desc (Bs ++ [U])
  | [], _, _, _, h, _ => by simp at h
  | [B], U, V, _, h, hUV => by
    simp at h; subst h; exact ⟨hUV, trivial⟩
  | B :: C :: Bs, U, V, hD, h, hUV => by
    refine ⟨hD.1, ?_⟩
    have := desc_snoc (C :: Bs) U V hD.2 (by simpa [List.getLast?_cons_cons] using h) hUV
    simpa using this

theorem stdShape_rep {t : List U} (h : StdShape t) :
    ∃ Bs e, flat t = W Bs e ∧ Desc Bs ∧ (∀ B ∈ Bs, Blk B) ∧
      (∀ v P, t = .b v :: P → e = 0 ∧ Bs.getLast? = some (raiseBits (flat v))) := by
  induction h with
  | nil => exact ⟨[], 0, by simp [W], trivial, by simp, by intro v P h; cases h⟩
  | @zero t ht ih =>
    obtain ⟨Bs, e, hf, hD, hB, -⟩ := ih
    exact ⟨Bs, e+1, by simp [W_succ, hf], hD, hB, by intro v P h; cases h⟩
  | @single u hu ih =>
    obtain ⟨Bs, e, hf, hD, hB, -⟩ := ih
    have hdom : Dom (flat u) := hf ▸ dom_W e Bs hD hB
    refine ⟨[raiseBits (flat u)], 0, by simp [W], trivial, ?_, ?_⟩
    · intro B hBm; simp at hBm; subst hBm; exact blk_raiseBits _ (binary_flat u) hdom
    · intro v P h; simp at h; obtain ⟨rfl, rfl⟩ := h; simp
  | @next u v P hu hP hcmp ihu ihP =>
    obtain ⟨Bs, e, hf, hD, hB, hlast⟩ := ihP
    obtain ⟨he, hl⟩ := hlast v P rfl
    subst he
    obtain ⟨Bu, eu, hfu, hDu, hBu, -⟩ := ihu
    have hdom : Dom (flat u) := hfu ▸ dom_W eu Bu hDu hBu
    have hne : Bs ≠ [] := by intro h; simp [h] at hl
    refine ⟨Bs ++ [raiseBits (flat u)], 0, ?_, desc_snoc Bs _ _ hD hl hcmp, ?_, ?_⟩
    · rw [W_snoc Bs _ hne, ← hf]; simp
    · intro B hBm
      simp at hBm
      rcases hBm with hBm | rfl
      · exact hB B hBm
      · exact blk_raiseBits _ (binary_flat u) hdom
    · intro v' P' h; simp at h; obtain ⟨rfl, -⟩ := h; simp

theorem stdShape_dom {t : List U} (h : StdShape t) : Dom (flat t) := by
  obtain ⟨Bs, e, hf, hD, hB, -⟩ := stdShape_rep h
  rw [hf]; exact dom_W e Bs hD hB

theorem cutCorrect_of_stdShape (u P : List U) (h : StdShape (.b u :: P)) : CutCorrect u P := by
  have hc := h.canonical
  have hP : BlockGap P := by cases hc with | block _ _ hg => exact hg
  exact cutCorrect_of_stdShape_of_dom (fun t ht => stdShape_dom ht) u h.child P hP


/-! ## Standard forms -/

theorem encode_block_last (u P : List U) :
    ∃ X, encode (.b u :: P) = X ++ [1] := ⟨_, encode_parts u P⟩

theorem block_of_pos (t : List U) (h : 0 < entry (encode t) (encode t).length) :
    ∃ u P, t = .b u :: P := by
  match t with
  | [] => simp [encode, entry] at h
  | .z :: t' => rw [encode_z, Seq.entry_append_last] at h; omega
  | .b u :: P => exact ⟨u, P, rfl⟩

theorem standard_shape {S : List ℕ} (h : Standard S) :
    S = [] ∨ S = [0] ∨ ∃ t, StdShape t ∧ encode t = S := by
  induction h with
  | tower n =>
    exact Or.inr (Or.inr ⟨tower n, StdShape.tower n, by simp [encode, flat_tower]⟩)
  | @expand S hS hpos k hk ih =>
    rcases ih with rfl | rfl | ⟨t, ht, rfl⟩
    · simp [entry] at hpos
    · simp [entry] at hpos
    · obtain ⟨u, P, rfl⟩ := block_of_pos t hpos
      refine Or.inr (Or.inr ⟨E (.b u :: P) k, ht.E u P k hk, ?_⟩)
      exact (fs_encode u P (cutCorrect_of_stdShape u P ht) k hk).symm
  | @erase S hS ih =>
    rcases ih with h0 | h0 | ⟨t, ht, he⟩
    · simp at h0
    · left; simpa using h0
    · match t, ht, he with
      | [], _, he =>
        right; left
        simp [encode] at he
        have := congrArg List.dropLast he
        simpa using this.symm
      | .z :: t', ht, he =>
        rw [encode_z] at he
        exact Or.inr (Or.inr ⟨t', ht.erase, List.append_cancel_right he⟩)
      | .b u :: P, _, he =>
        obtain ⟨X, hX⟩ := encode_block_last u P
        rw [hX] at he
        have := congrArg List.getLast? he
        simp at this

/-- Goal A of the second request. -/
theorem cutCorrect_of_standard (u P : List U) (hc : Canonical (.b u :: P))
    (hs : Standard (encode (.b u :: P))) : CutCorrect u P := by
  rcases standard_shape hs with h | h | ⟨t, ht, he⟩
  · simp [encode] at h
  · simp [encode] at h
  · have := encode_injective ht.canonical hc he
    subst this
    exact cutCorrect_of_stdShape u P ht

theorem standard_block {S : List ℕ} (hS : Standard S) (hpos : 0 < entry S S.length) :
    ∃ u P, StdShape (.b u :: P) ∧ encode (.b u :: P) = S := by
  rcases standard_shape hS with rfl | rfl | ⟨t, ht, rfl⟩
  · simp [entry] at hpos
  · simp [entry] at hpos
  · obtain ⟨u, P, rfl⟩ := block_of_pos t hpos
    exact ⟨u, P, ht, rfl⟩

/-- Every term of the expansion of a standard limit form has a smaller value. -/
theorem o_fs_lt_of_standard {S : List ℕ} (hS : Standard S) (hpos : 0 < entry S S.length)
    (k : ℕ) (hk : 1 ≤ k) : o (Seq.fs S k) < o S := by
  obtain ⟨u, P, ht, rfl⟩ := standard_block hS hpos
  exact o_fs_lt_of_cutCorrect u P ht.canonical (cutCorrect_of_stdShape u P ht) k hk

/-- The value of a standard limit form is the supremum of its expansion terms. -/
theorem o_fs_sup_of_standard {S : List ℕ} (hS : Standard S) (hpos : 0 < entry S S.length) :
    o S = ⨆ n : ℕ, o (Seq.fs S (n + 1)) := by
  obtain ⟨u, P, ht, rfl⟩ := standard_block hS hpos
  exact o_fs_sup_of_cutCorrect u P ht.canonical (cutCorrect_of_stdShape u P ht)


end Googology.Notation.SSOS
