import Googology.Trans.BMS.Pair
import PSS.Standard
import Bijectivity.«21-ordinal-bijectivity»

/-!
# Pair sequences: pss-proof's expansion is `expand2L`

[koteitan/pss-proof](https://github.com/koteitan/pss-proof) defines the pair
sequence system in its own words: `PSS.oper M n` is the fundamental sequence
`M[n]`, and `Bijectivity.CTPS` is the set of standard pair sequences that start
at `(0,0)`.  This repository has its own two-row rule, `BMS.expand2L`, proved
equal to `BM4.expand` on the entries (`BMS/Entries2.lean`).

This file shows that the two rules agree, with the bracket shifted by one:

* `oper_succ_eq_expand2L`: `PSS.oper M (N + 1) = expand2L N M` for every pair
  sequence `M` of length at least `2` that is `Good`.  `Good` asks that the
  first column has first entry `0`, and that a column whose first entry is `0`
  is `(0,0)`.  Every standard pair sequence is `Good` (`good_of_ctps`), so
  `oper_succ_eq_expand2L_of_ctps` states it for `CTPS`.
* At length `1` they differ: `PSS.oper [(0,0)] n = [(0,0)]` (pss-proof halts
  there), while `expand2L N [(0,0)] = []`.

The standard sets then correspond:

* `isPair_iff`: a list is the entries of a standard two-row array (a state of
  `pairL`) exactly when it is `[]` or in `CTPS`.  The generators match too:
  `pairStd_gen` says `pairStd.gen n` is `diagSeq 0 n`.
* `pairL_step_eq_oper`: on a state of length at least `2`, the step of `pairL`
  at `N` is `PSS.oper` at `N + 1`.

The proof compares the two rules case by case.  pss-proof tests the parent
relations with fuelled Boolean functions (`le0`, `nextrel0`, `nextrel1`); here
they are shown to be `AncL`, `ParL` and `ParL1` of `BMS/Anc.lean` and
`BMS/Entries2.lean`.  Two differences in the rules need `Good`:

* pss-proof takes the row-`1` parent whenever the last second entry is
  positive, and drops the last column if there is none; `expand2L` falls back
  to the row-`0` parent.  Under `Good` the row-`1` parent always exists when
  the last second entry is positive (`parAt1_ne_none`).
* pss-proof adds the increment to every column of the bad part; `expand2L`
  only to row-`0` descendants of the bad root.  Every column of the bad part is
  one (`desc_of_anc`), so this needs nothing.
-/

namespace Googology.Trans.PSS

open Googology.Trans.BMS

/-! ### Entries -/

theorem getElem!_pair_eq (M : List (ℕ × ℕ)) (j : ℕ) :
    M[j]! = (M[j]?).getD (0, 0) := by
  by_cases h : j < M.length
  · rw [getElem!_pos M j h, List.getElem?_eq_getElem h]; rfl
  · rw [getElem!_neg M j h, List.getElem?_eq_none (by omega)]; rfl

theorem entry_zero (M : List (ℕ × ℕ)) (j : ℕ) : _root_.PSS.entry M 0 j = (M[j]!).1 := by
  rw [getElem!_pair_eq, _root_.PSS.entry]
  cases M[j]? <;> rfl

theorem entry_one (M : List (ℕ × ℕ)) (j : ℕ) : _root_.PSS.entry M 1 j = (M[j]!).2 := by
  rw [getElem!_pair_eq, _root_.PSS.entry]
  cases M[j]? <;> rfl

theorem map_fst_getElem! (M : List (ℕ × ℕ)) (j : ℕ) :
    (M.map Prod.fst)[j]! = (M[j]!).1 := by
  by_cases h : j < M.length
  · rw [getElem!_pos _ j (by simpa using h), getElem!_pos M j h, List.getElem_map]
  · rw [getElem!_neg _ j (by simpa using h), getElem!_neg M j h]; rfl

theorem entry_zero' (M : List (ℕ × ℕ)) (j : ℕ) :
    _root_.PSS.entry M 0 j = (M.map Prod.fst)[j]! := by
  rw [entry_zero, map_fst_getElem!]

/-! ### Ancestors -/

theorem AncL_lt {l : List ℕ} {a b : ℕ} (h : AncL l a b) : a < b := by
  induction h with
  | single hp => exact hp.1
  | tail _ hp ih => exact lt_trans ih hp.1

/-- Every column strictly between a row-`0` ancestor and its descendant has a
larger first entry than the ancestor. -/
theorem AncL_gt {l : List ℕ} {p i : ℕ} (h : AncL l p i) :
    ∀ x, p < x → x ≤ i → l[p]! < l[x]! := by
  induction h with
  | @single i hp =>
    intro x h1 h2
    rcases Nat.lt_or_ge x i with hx | hx
    · exact lt_of_lt_of_le hp.2.1 (hp.2.2 x h1 hx)
    · rw [show x = i by omega]; exact hp.2.1
  | @tail j i hpj hp ih =>
    intro x h1 h2
    have hpj' := AncL_lt hpj
    rcases Nat.lt_or_ge j x with hx | hx
    · have hjx : l[j]! < l[x]! := by
        rcases Nat.lt_or_ge x i with hxi | hxi
        · exact lt_of_lt_of_le hp.2.1 (hp.2.2 x hx hxi)
        · rw [show x = i by omega]; exact hp.2.1
      exact lt_trans (ih j hpj' le_rfl) hjx
    · exact ih x h1 hx

theorem parAux_none (l : List ℕ) (x : ℕ) : ∀ k, parAux l x k = none → ∀ j < k, x ≤ l[j]! := by
  intro k
  induction k with
  | zero => intro _ j hj; omega
  | succ m ih =>
    intro h j hj
    rw [parAux] at h
    by_cases hm : l[m]! < x
    · rw [if_pos hm] at h; exact absurd h (by simp)
    · rw [if_neg hm] at h
      rcases Nat.lt_or_ge j m with hjm | hjm
      · exact ih h j hjm
      · rw [show j = m by omega]; omega

theorem lastAux_none (cand : ℕ → Bool) (v : ℕ → ℕ) (x : ℕ) :
    ∀ k, lastAux cand v x k = none → ∀ j < k, cand j = true → x ≤ v j := by
  intro k
  induction k with
  | zero => intro _ j hj; omega
  | succ m ih =>
    intro h j hj hc
    rw [lastAux] at h
    by_cases hm : (cand m && decide (v m < x)) = true
    · rw [if_pos hm] at h; exact absurd h (by simp)
    · rw [if_neg hm] at h
      rcases Nat.lt_or_ge j m with hjm | hjm
      · exact ih h j hjm hc
      · rw [show j = m by omega] at hc ⊢
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, not_lt] at hm
        exact hm hc

/-- A column whose first entry stays above that of `p` all the way from `p` is
a row-`0` descendant of `p`, or `p` itself. -/
theorem desc_of_gt {l : List ℕ} {p : ℕ} :
    ∀ x, p ≤ x → (∀ y, p < y → y ≤ x → l[p]! < l[y]!) → p = x ∨ AncL l p x := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hpx hgt
    rcases Nat.eq_or_lt_of_le hpx with he | hlt
    · exact Or.inl he
    right
    cases hq : parAt l x with
    | none =>
      have := parAux_none l l[x]! x hq p hlt
      have := hgt x hlt le_rfl
      omega
    | some y =>
      have hy := (parAt_eq_some l x y).mp hq
      have hpy : p ≤ y := by
        by_contra hc
        have := hy.2.2 p (by omega) hlt
        have := hgt x hlt le_rfl
        omega
      rcases ih y hy.1 hpy (fun z h1 h2 => hgt z h1 (by have := hy.1; omega)) with he | ha
      · exact Relation.TransGen.single (he ▸ hy)
      · exact Relation.TransGen.tail ha hy

/-- **Every column of the bad part descends from the bad root.** -/
theorem desc_of_anc {l : List ℕ} {p i : ℕ} (h : AncL l p i) :
    ∀ x, p ≤ x → x ≤ i → p = x ∨ AncL l p x := fun x h1 h2 =>
  desc_of_gt x h1 (fun y hy1 hy2 => AncL_gt h y hy1 (le_trans hy2 h2))

/-- With first entry `0` in front, a column with positive first entry has a
row-`0` ancestor with first entry `0`. -/
theorem anc_zero_exists {l : List ℕ} (h0 : l[0]! = 0) :
    ∀ x, 0 < l[x]! → ∃ c, AncL l c x ∧ l[c]! = 0 := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hx
    have hx0 : 0 < x := by
      rcases Nat.eq_zero_or_pos x with h | h
      · rw [h, h0] at hx; omega
      · exact h
    cases hq : parAt l x with
    | none =>
      have := parAux_none l l[x]! x hq 0 hx0
      omega
    | some y =>
      have hy := (parAt_eq_some l x y).mp hq
      rcases Nat.eq_zero_or_pos l[y]! with hy0 | hy0
      · exact ⟨y, Relation.TransGen.single hy, hy0⟩
      · obtain ⟨c, hc, hc0⟩ := ih y hy.1 hy0
        exact ⟨c, Relation.TransGen.tail hc hy, hc0⟩

/-! ### The fuelled relations of pss-proof -/

theorem nextrel0_iff (M : List (ℕ × ℕ)) (j0 j1 : ℕ) :
    _root_.PSS.nextrel0 M j0 j1 = true ↔ j1 < M.length ∧ ParL (M.map Prod.fst) j0 j1 := by
  simp only [_root_.PSS.nextrel0, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_lt,
    ParL, entry_zero', _root_.PSS.Lng]
  constructor
  · rintro ⟨⟨⟨⟨_, h2⟩, h3⟩, h4⟩, h5⟩
    refine ⟨h2, h3, h4, fun j' a b => ?_⟩
    rcases h5 j' b with h | h
    · omega
    · exact h
  · rintro ⟨h2, h3, h4, h5⟩
    refine ⟨⟨⟨⟨by omega, h2⟩, h3⟩, h4⟩, fun j hj => ?_⟩
    by_cases hj0 : j ≤ j0
    · exact Or.inl hj0
    · exact Or.inr (h5 j (by omega) hj)

theorem le0Aux_sound (M : List (ℕ × ℕ)) :
    ∀ fuel a b, _root_.PSS.le0Aux M fuel a b = true → a = b ∨ AncL (M.map Prod.fst) a b := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b h
    simp only [_root_.PSS.le0Aux, beq_iff_eq] at h
    exact Or.inl h
  | succ f ih =>
    intro a b h
    simp only [_root_.PSS.le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
      List.mem_range, Bool.and_eq_true] at h
    rcases h with h | ⟨j, _, hn, hl⟩
    · exact Or.inl h
    · have hp := ((nextrel0_iff M j b).mp hn).2
      rcases ih a j hl with he | ha
      · exact Or.inr (Relation.TransGen.single (he ▸ hp))
      · exact Or.inr (Relation.TransGen.tail ha hp)

theorem le0Aux_complete (M : List (ℕ × ℕ)) :
    ∀ fuel a b, b < M.length → b ≤ a + fuel → (a = b ∨ AncL (M.map Prod.fst) a b) →
      _root_.PSS.le0Aux M fuel a b = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b _ hb h
    rcases h with h | h
    · simp [_root_.PSS.le0Aux, h]
    · have := AncL_lt h; omega
  | succ f ih =>
    intro a b hbM hb h
    simp only [_root_.PSS.le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
      List.mem_range, Bool.and_eq_true]
    rcases h with h | h
    · exact Or.inl h
    · right
      obtain ⟨j, hr, hj⟩ := Relation.TransGen.tail'_iff.mp h
      have hjb := hj.1
      refine ⟨j, hjb, (nextrel0_iff M j b).mpr ⟨hbM, hj⟩, ?_⟩
      have hr' := Relation.reflTransGen_iff_eq_or_transGen.mp hr
      have haj : a ≤ j := by
        rcases hr' with he | ht
        · omega
        · exact le_of_lt (AncL_lt ht)
      refine ih a j (by omega) (by omega) ?_
      rcases hr' with he | ht
      · exact Or.inl he.symm
      · exact Or.inr ht

theorem le0_iff (M : List (ℕ × ℕ)) (a b : ℕ) :
    _root_.PSS.le0 M a b = true ↔
      a < M.length ∧ b < M.length ∧ (a = b ∨ AncL (M.map Prod.fst) a b) := by
  simp only [_root_.PSS.le0, Bool.and_eq_true, decide_eq_true_eq, _root_.PSS.Lng]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, le0Aux_sound M _ a b h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, le0Aux_complete M _ a b h2 (by omega) h3⟩

theorem nextrel1_iff (M : List (ℕ × ℕ)) (j0 j1 : ℕ) :
    _root_.PSS.nextrel1 M j0 j1 = true ↔ j1 < M.length ∧ ParL1 M j0 j1 := by
  simp only [_root_.PSS.nextrel1, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not, not_lt, ParL1, entry_one, le0_iff, _root_.PSS.Lng]
  constructor
  · rintro ⟨⟨⟨⟨⟨_, h2⟩, h3⟩, h4⟩, ⟨_, _, h5⟩⟩, h6⟩
    have hanc : AncL (M.map Prod.fst) j0 j1 := by
      rcases h5 with h | h
      · omega
      · exact h
    refine ⟨h2, h3, hanc, h4, fun j' a b hc => ?_⟩
    rcases h6 j' (by omega) with (h | h) | h
    · omega
    · exact absurd ((le0_iff M j' j1).mpr ⟨by omega, by omega, Or.inr hc⟩) (by simp [h])
    · exact h
  · rintro ⟨h2, h3, hanc, h4, h5⟩
    refine ⟨⟨⟨⟨⟨by omega, h2⟩, h3⟩, h4⟩, ⟨by omega, h2, Or.inr hanc⟩⟩, fun j hj => ?_⟩
    by_cases hj0 : j ≤ j0
    · exact Or.inl (Or.inl hj0)
    by_cases hl : j < M.length ∧ j1 < M.length ∧ (j = j1 ∨ AncL (M.map Prod.fst) j j1)
    · right
      rcases hl.2.2 with he | ha
      · rw [he]
      · exact h5 j (by omega) (AncL_lt ha) ha
    · refine Or.inl (Or.inr ?_)
      cases hh : _root_.PSS.le0 M j j1
      · rfl
      · exact absurd ((le0_iff M j j1).mp hh) hl

/-! ### The parents lists of pss-proof -/

theorem range_filter_single (P : ℕ → Bool) (p : ℕ) (hP : ∀ j, P j = true ↔ j = p) :
    ∀ n, (List.range n).filter P = if p < n then [p] else [] := by
  intro n
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.filter_append, ih]
    by_cases hm : m = p
    · subst hm
      rw [if_neg (Nat.lt_irrefl m), if_pos (Nat.lt_succ_self m)]
      simp [(hP m).mpr rfl]
    · have hPm : P m = false := by
        cases h : P m
        · rfl
        · exact absurd ((hP m).mp h) hm
      have hf : List.filter P [m] = [] := by simp [hPm]
      rw [hf, List.append_nil]
      by_cases hpm : p < m
      · rw [if_pos hpm, if_pos (by omega)]
      · rw [if_neg hpm, if_neg (by omega)]

theorem ParL1_unique {l : List (ℕ × ℕ)} {i j j' : ℕ} (h : ParL1 l j i) (h' : ParL1 l j' i) :
    j = j' := by
  rcases lt_trichotomy j j' with hlt | he | hgt
  · have := h.2.2.2 j' hlt h'.1 h'.2.1
    have := h'.2.2.1
    omega
  · exact he
  · have := h'.2.2.2 j hgt h.1 h.2.1
    have := h.2.2.1
    omega

theorem parents_zero_some {M : List (ℕ × ℕ)} {i p : ℕ} (hi : i < M.length)
    (h : parAt (M.map Prod.fst) i = some p) : _root_.PSS.parents M 0 i = [p] := by
  have hp := (parAt_eq_some _ _ _).mp h
  unfold _root_.PSS.parents
  rw [range_filter_single _ p ?_ _, if_pos (by have := hp.1; simp only [_root_.PSS.Lng]; omega)]
  intro j
  simp only [_root_.PSS.nextR, ↓reduceIte]
  rw [nextrel0_iff]
  constructor
  · rintro ⟨_, hj⟩; exact parAt_unique h hj
  · rintro rfl; exact ⟨hi, hp⟩

theorem parents_zero_none {M : List (ℕ × ℕ)} {i : ℕ}
    (h : parAt (M.map Prod.fst) i = none) : _root_.PSS.parents M 0 i = [] := by
  unfold _root_.PSS.parents
  rw [List.filter_eq_nil_iff]
  intro j _ hj
  simp only [_root_.PSS.nextR, ↓reduceIte] at hj
  rw [nextrel0_iff, ← parAt_eq_some, h] at hj
  exact absurd hj.2 (by simp)

theorem parents_one_some {M : List (ℕ × ℕ)} {i p : ℕ} (hi : i < M.length)
    (h : parAt1 M i = some p) : _root_.PSS.parents M 1 i = [p] := by
  have hp := (parAt1_eq_some _ _ _).mp h
  unfold _root_.PSS.parents
  rw [range_filter_single _ p ?_ _, if_pos (by have := hp.1; simp only [_root_.PSS.Lng]; omega)]
  intro j
  simp only [_root_.PSS.nextR, one_ne_zero, ↓reduceIte]
  rw [nextrel1_iff]
  constructor
  · rintro ⟨_, hj⟩; exact ParL1_unique hj hp
  · rintro rfl; exact ⟨hi, hp⟩

theorem parents_one_none {M : List (ℕ × ℕ)} {i : ℕ}
    (h : parAt1 M i = none) : _root_.PSS.parents M 1 i = [] := by
  unfold _root_.PSS.parents
  rw [List.filter_eq_nil_iff]
  intro j _ hj
  simp only [_root_.PSS.nextR, one_ne_zero, ↓reduceIte] at hj
  rw [nextrel1_iff, ← parAt1_eq_some, h] at hj
  exact absurd hj.2 (by simp)

/-! ### Good pair sequences -/

/-- A column whose first entry is `0` is `(0,0)`. -/
def Inv (M : List (ℕ × ℕ)) : Prop := ∀ q ∈ M, q.1 = 0 → q.2 = 0

/-- The first column has first entry `0`, and `Inv` holds.  Every standard
pair sequence is `Good` (`good_of_ctps`). -/
def Good (M : List (ℕ × ℕ)) : Prop := (M[0]!).1 = 0 ∧ Inv M

theorem Inv.getElem! {M : List (ℕ × ℕ)} (h : Inv M) (j : ℕ) (h0 : (M[j]!).1 = 0) :
    (M[j]!).2 = 0 := by
  by_cases hj : j < M.length
  · rw [getElem!_pos M j hj] at h0 ⊢
    exact h _ (List.getElem_mem hj) h0
  · rw [getElem!_neg M j hj]; rfl

/-- **Under `Good`, a positive second entry has a row-`1` parent.** -/
theorem parAt1_ne_none {M : List (ℕ × ℕ)} (hG : Good M) (i : ℕ) (hi : 0 < (M[i]!).2) :
    parAt1 M i ≠ none := by
  have h1 : 0 < (M[i]!).1 := by
    rcases Nat.eq_zero_or_pos (M[i]!).1 with h | h
    · have := hG.2.getElem! i h; omega
    · exact h
  have hl0 : (M.map Prod.fst)[0]! = 0 := by rw [map_fst_getElem!]; exact hG.1
  obtain ⟨c, hc, hc0⟩ := anc_zero_exists hl0 i (by rw [map_fst_getElem!]; exact h1)
  intro hn
  unfold parAt1 at hn
  have := lastAux_none _ _ _ i hn c (AncL_lt hc) ((ancAtB_iff _ _ _).mpr hc)
  have : (M[c]!).2 = 0 := hG.2.getElem! c (by rw [← map_fst_getElem!]; exact hc0)
  omega

/-! ### Lists -/

theorem take_eq_map (M : List (ℕ × ℕ)) (p : ℕ) (hp : p ≤ M.length) :
    M.take p = (List.range p).map (fun i => M[i]!) := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_map, List.length_range]; omega
  · intro n h1 h2
    simp only [List.getElem_take, List.getElem_map, List.getElem_range]
    rw [getElem!_pos M n (by simp only [List.length_take] at h1; omega)]

theorem flatMap_range_eq {α : Type} (f : ℕ → ℕ → α) (p L : ℕ) (hL : 0 < L) :
    ∀ n, (List.range n).flatMap (fun k => (List.range' p L).map (fun j => f k j))
      = (List.range (n * L)).map (fun t => f (t / L) (p + t % L)) := by
  intro n
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, ih, Nat.succ_mul, List.range_add,
      List.map_append, List.flatMap_singleton, List.map_map, List.range'_eq_map_range,
      List.map_map]
    congr 1
    refine List.map_congr_left (fun s hs => ?_)
    have hs := List.mem_range.mp hs
    simp only [Function.comp_apply]
    have hd : (m * L + s) / L = m := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt hs, Nat.zero_add]
    have hm : (m * L + s) % L = s := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
    rw [hd, hm]

/-! ### The two rules agree -/

theorem oper_succ_eq_expand2L (M : List (ℕ × ℕ)) (hG : Good M) (hL : 2 ≤ M.length)
    (N : ℕ) : _root_.PSS.oper M (N + 1) = expand2L N M := by
  have hne : M ≠ [] := by rintro rfl; simp at hL
  have hPred : _root_.PSS.Pred M = M.dropLast := by
    rw [_root_.PSS.Pred, if_neg (by simp only [_root_.PSS.Lng]; omega)]
  have hemp : M.isEmpty = false := by simpa using hne
  unfold _root_.PSS.oper
  simp only [_root_.PSS.Lng]
  rw [if_neg (by omega)]
  have hi : M.length - 1 < M.length := by omega
  cases h1 : parAt1 M (M.length - 1) with
  | some p =>
    have hb : badRootL M = some (p, true) := by simp [badRootL, hemp, h1]
    have hp := (parAt1_eq_some M _ p).mp h1
    have hpi := hp.1
    have h2 := hp.2.2.1
    have h00 : ¬ ((decide (_root_.PSS.entry M 0 (M.length - 1) = 0)
        && decide (_root_.PSS.entry M 1 (M.length - 1) = 0)) = true) := by
      rw [entry_one]; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
    have hidx : _root_.PSS.idx1 M (M.length - 1) = 1 := by
      unfold _root_.PSS.idx1; rw [if_pos (by rw [entry_one]; omega)]
    have hpar := parents_one_some hi h1
    have hhas : _root_.PSS.hasParent M 1 (M.length - 1) = true := by
      unfold _root_.PSS.hasParent; rw [hpar]; rfl
    have hparent : _root_.PSS.parent M 1 (M.length - 1) = p := by
      unfold _root_.PSS.parent; rw [hpar]; rfl
    rw [if_neg h00]
    simp only [hidx, hhas, hparent, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      Nat.lt_irrefl, zero_lt_one, mul_zero, add_zero]
    unfold expand2L
    rw [hb]
    simp only [Bool.true_and]
    have hL0 : 0 < M.length - 1 - p := by omega
    rw [take_eq_map M p (by omega),
      flatMap_range_eq (fun k j => (_root_.PSS.entry M 0 j
        + k * (_root_.PSS.entry M 0 (M.length - 1) - _root_.PSS.entry M 0 p),
        _root_.PSS.entry M 1 j)) p _ hL0 (N + 1)]
    congr 1
    refine List.map_congr_left (fun t _ => ?_)
    have hmod := Nat.mod_lt t hL0
    have hd := desc_of_anc hp.2.1 (p + t % (M.length - 1 - p)) (by omega) (by omega)
    rw [if_pos (by
      rw [Bool.or_eq_true, beq_iff_eq, ancAtB_iff]; exact hd)]
    simp only [entry_zero, entry_one]
  | none =>
    cases h0 : parAt (M.map Prod.fst) (M.length - 1) with
    | none =>
      have hb : badRootL M = none := by simp [badRootL, hemp, h1, h0]
      have hhas : _root_.PSS.hasParent M (_root_.PSS.idx1 M (M.length - 1)) (M.length - 1)
          = false := by
        unfold _root_.PSS.hasParent _root_.PSS.idx1
        split_ifs
        · rw [parents_one_none h1]; rfl
        · rw [parents_zero_none h0]; rfl
      unfold expand2L
      rw [hb, hhas]
      simp only [Bool.not_false, ↓reduceIte, ite_self]
      exact hPred
    | some p =>
      have hb : badRootL M = some (p, false) := by simp [badRootL, hemp, h1, h0]
      have hp := (parAt_eq_some _ _ p).mp h0
      have hpi := hp.1
      have h1lt := hp.2.1
      rw [map_fst_getElem!, map_fst_getElem!] at h1lt
      have h2z : (M[M.length - 1]!).2 = 0 := by
        by_contra hc
        exact parAt1_ne_none hG _ (by omega) h1
      have h00 : ¬ ((decide (_root_.PSS.entry M 0 (M.length - 1) = 0)
          && decide (_root_.PSS.entry M 1 (M.length - 1) = 0)) = true) := by
        rw [entry_zero]; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
      have hidx : _root_.PSS.idx1 M (M.length - 1) = 0 := by
        unfold _root_.PSS.idx1; rw [if_neg (by rw [entry_one]; omega)]
      have hpar := parents_zero_some hi h0
      have hhas : _root_.PSS.hasParent M 0 (M.length - 1) = true := by
        unfold _root_.PSS.hasParent; rw [hpar]; rfl
      have hparent : _root_.PSS.parent M 0 (M.length - 1) = p := by
        unfold _root_.PSS.parent; rw [hpar]; rfl
      rw [if_neg h00]
      simp only [hidx, hhas, hparent, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        Nat.lt_irrefl, Nat.not_lt_zero, mul_zero, add_zero]
      unfold expand2L
      rw [hb]
      simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      have hL0 : 0 < M.length - 1 - p := by omega
      rw [take_eq_map M p (by omega),
        flatMap_range_eq (fun _ j => (_root_.PSS.entry M 0 j, _root_.PSS.entry M 1 j)) p _
          hL0 (N + 1)]
      congr 1
      refine List.map_congr_left (fun t _ => ?_)
      rw [entry_zero, entry_one]

/-! ### Length one -/

/-- At length `1` pss-proof halts. -/
theorem oper_single (n : ℕ) : _root_.PSS.oper [(0, 0)] n = [(0, 0)] := rfl

/-- At length `1` this repository's rule goes to the empty list. -/
theorem expand2L_single (N : ℕ) : expand2L N [(0, 0)] = [] := by
  simp [expand2L, badRootL, parAt1, lastAux, parAt, parAux]

theorem expand2L_nil (N : ℕ) : expand2L N [] = [] := by
  simp [expand2L, badRootL]

/-! ### Standard pair sequences are good -/

theorem inv_oper {M : List (ℕ × ℕ)} (hM : Inv M) (n : ℕ) : Inv (_root_.PSS.oper M n) := by
  have hPred : Inv (_root_.PSS.Pred M) := by
    unfold _root_.PSS.Pred
    split_ifs
    · exact hM
    · exact fun q hq => hM q (List.mem_of_mem_dropLast hq)
  have hidx : ¬ 1 < _root_.PSS.idx1 M (M.length - 1) := by
    unfold _root_.PSS.idx1; split_ifs <;> omega
  unfold _root_.PSS.oper
  simp only [_root_.PSS.Lng, hidx, if_false, mul_zero, add_zero]
  split_ifs
  · exact hM
  · exact hPred
  · exact hPred
  all_goals
    intro q hq
    rw [List.mem_append] at hq
    rcases hq with hq | hq
    · exact hM q (List.mem_of_mem_take hq)
    · obtain ⟨k, _, hk⟩ := List.mem_flatMap.mp hq
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hk
      intro h0
      dsimp only at h0 ⊢
      have h0' : (M[j]!).1 = 0 := by
        rw [← entry_zero]; exact (Nat.add_eq_zero_iff.mp h0).1
      rw [entry_one]
      exact hM.getElem! j h0'

theorem inv_diagSeq (u v : ℕ) : Inv (_root_.PSS.diagSeq u v) := by
  intro q hq
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hq
  exact id

theorem inv_of_stps {M : List (ℕ × ℕ)} (h : _root_.PSS.STPS M) : Inv M := by
  induction h with
  | diag u v _ => exact inv_diagSeq u v
  | oper _ n _ ih => exact inv_oper ih n

/-- **Every standard pair sequence of pss-proof is `Good`.** -/
theorem good_of_ctps {M : List (ℕ × ℕ)} (h : Bijectivity.CTPS M) : Good M := by
  refine ⟨?_, inv_of_stps h.1⟩
  have hh := h.2
  cases M with
  | nil => rfl
  | cons a l =>
    simp only [List.headD_cons] at hh
    rw [getElem!_pos _ 0 (by simp)]
    simp [hh]

/-- **The main theorem on the standard pair sequences.** -/
theorem oper_succ_eq_expand2L_of_ctps {M : List (ℕ × ℕ)} (h : Bijectivity.CTPS M)
    (hL : 2 ≤ M.length) (N : ℕ) : _root_.PSS.oper M (N + 1) = expand2L N M :=
  oper_succ_eq_expand2L M (good_of_ctps h) hL N

/-! ### The standard sets -/

/-- Being the entries of a standard two-row array: the values of `PairState`. -/
def IsPair (l : List (ℕ × ℕ)) : Prop := ∃ A : BM4.Arr 2, Pat.Std 2 A ∧ entries2 A = l

theorem diagSeq_eq (n : ℕ) :
    _root_.PSS.diagSeq 0 n = (List.range (n + 1)).map (fun i => (i, i)) := by
  rw [_root_.PSS.diagSeq, List.range_eq_range', Nat.sub_zero]

/-- The generators of `pairStd` are the diagonal sequences of pss-proof. -/
theorem pairStd_gen (n : ℕ) : (pairStd.gen n).1 = _root_.PSS.diagSeq 0 n := by
  rw [diagSeq_eq]; rfl

theorem isPair_diagSeq (n : ℕ) : IsPair (_root_.PSS.diagSeq 0 n) :=
  ⟨Pat.stair 2 n, Pat.Std.init n, by rw [entries2_stair, diagSeq_eq]⟩

theorem isPair_nil : IsPair [] := by
  refine ⟨BM4.expand (Pat.stair 2 0) 0, Pat.Std.step 0 (Pat.Std.init 0), ?_⟩
  rw [entries2_expand, entries2_stair]
  exact expand2L_single 0

theorem isPair_oper {M : List (ℕ × ℕ)} (hC : Bijectivity.CTPS M) (hP : IsPair M) {n : ℕ}
    (hn : 1 ≤ n) : IsPair (_root_.PSS.oper M n) := by
  by_cases hL : 2 ≤ M.length
  · obtain ⟨A, hA, hl⟩ := hP
    rw [show n = (n - 1) + 1 by omega, oper_succ_eq_expand2L_of_ctps hC hL]
    exact ⟨BM4.expand A (n - 1), Pat.Std.step _ hA, by rw [entries2_expand, hl]⟩
  · have : _root_.PSS.oper M n = M := by
      unfold _root_.PSS.oper
      simp only [_root_.PSS.Lng]
      rw [if_pos (by omega)]
    rw [this]; exact hP

theorem isPair_expand : ∀ (a : List ℕ) (M : List (ℕ × ℕ)), Bijectivity.CTPS M → IsPair M →
    (∀ n ∈ a, 1 ≤ n) → IsPair (Bijectivity.expand M a) := by
  intro a
  induction a with
  | nil => intro M _ hP _; exact hP
  | cons n a ih =>
    intro M hC hP ha
    have hn := ha n (by simp)
    exact ih _ (Bijectivity.ctps_oper hC hn) (isPair_oper hC hP hn)
      (fun m hm => ha m (by simp [hm]))

/-- **Every standard pair sequence of pss-proof is a state of `pairL`.** -/
theorem isPair_of_ctps {M : List (ℕ × ℕ)} (h : Bijectivity.CTPS M) : IsPair M := by
  obtain ⟨v, a, ha, rfl⟩ := (Bijectivity.ctps_iff_leExpPS M).mp h
  exact isPair_expand a _ (Bijectivity.ctps_diagSeq v) (isPair_diagSeq v) ha

theorem ctps_of_std {A : BM4.Arr 2} (h : Pat.Std 2 A) :
    entries2 A = [] ∨ Bijectivity.CTPS (entries2 A) := by
  induction h with
  | init n =>
    right
    rw [entries2_stair, ← diagSeq_eq]
    exact Bijectivity.ctps_diagSeq n
  | @step A N _ ih =>
    rw [entries2_expand]
    rcases ih with h | h
    · left; rw [h]; exact expand2L_nil N
    · by_cases hL : 2 ≤ (entries2 A).length
      · right
        rw [← oper_succ_eq_expand2L_of_ctps h hL]
        exact Bijectivity.ctps_oper h (by omega)
      · left
        have hG := good_of_ctps h
        generalize entries2 A = M at hG hL ⊢
        match M, hL, hG with
        | [], _, _ => exact expand2L_nil N
        | [(a, b)], _, hG =>
          have ha : a = 0 := by simpa using hG.1
          have hb : b = 0 := hG.2 (a, b) (by simp) ha
          subst ha hb
          exact expand2L_single N
        | _ :: _ :: _, hL, _ => exact absurd (by simp) hL

/-- **The states of `pairL` are the standard pair sequences of pss-proof, and
`[]`.** -/
theorem isPair_iff (l : List (ℕ × ℕ)) : IsPair l ↔ l = [] ∨ Bijectivity.CTPS l := by
  constructor
  · rintro ⟨A, hA, rfl⟩; exact ctps_of_std hA
  · rintro (rfl | h)
    · exact isPair_nil
    · exact isPair_of_ctps h

/-- The step of `pairL` is pss-proof's `oper`, with the bracket shifted by one,
on every state of length at least `2`. -/
theorem pairL_step_eq_oper (l : PairState) (N : ℕ) (h : 2 ≤ l.1.length) :
    (pairL.step l N : PairState).1 = _root_.PSS.oper l.1 (N + 1) := by
  rw [pairL_step_val]
  obtain ⟨A, hA, hl⟩ := l.2
  rcases ctps_of_std hA with h0 | hC
  · rw [← hl, h0] at h; simp at h
  · rw [hl] at hC
    exact (oper_succ_eq_expand2L_of_ctps hC h N).symm

end Googology.Trans.PSS
