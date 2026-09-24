import Googology.Trans.DBMS.ThreeRowUpperNCComm

/-!
# The invariants `Low2` and `R1` on the reached matrices

`ThreeRowUpperNCComm.lean` proves that the nested raise `t3n` commutes with
expansion, `(t3n C)[N] = t3n (C[N])`, for three-row `C` with `Low2 C`, `R1 C`
and `¬ RaisedPar C`.  This file proves the first two on every matrix reached
from `(cgen 2 4)[v]` (`SReach`):

* `low2_of_sReach`: a column with row-`1` entry `≤ 1` has row-`2` entry `0`.
  An expansion copies row `2` and never lowers row `1`
  (`expandRL_col_source`), and the start
  `(0,0,0)(1,1,0)(2,2,1)(3,3,1)⋯` has the property.
* `r1_of_sReach`, `r0_of_sReach`: a column's row-`0` parent has row-`0` entry
  one less, and row-`1` entry at least one less.  These are the row-`1`
  discipline `r1ok` of koteitan/trio (ported in `TrioCof/`), which trio's
  expansion `oper` keeps on every sequence (`r1ok_oper`).  On the reached
  matrices `expandRL 3` is `oper` (`expandRL_toL_of`), because trio's other
  invariants `blockok 0`, `z0ok`, `noninc` hold as well and give the last
  column a parent in its lowest nonzero row (`hp_last`).

With these, `expandRL_t3n_of_sReach`: on `SReach`, outside `RaisedPar`,
`t3n` commutes with expansion.
-/

namespace Googology.Trans.DBMS

open Googology.Trans.BMS
open Googology.Trans.BMS.TrioCofinal (toL ofL colL trioGen toL_entry toL_length expandRL_toL_of
  ParR0_eq expandRL_short)

/-! ### Trio's invariants -/

/-- The invariants of koteitan/trio that `oper` keeps. -/
def TInv (M : TrioCof.TrioSeq) : Prop :=
  TrioCof.blockok 0 M ∧ TrioCof.z0ok M ∧ TrioCof.noninc M ∧ TrioCof.r1ok M

theorem tInv_nil : TInv [] := by
  refine ⟨⟨fun h => absurd rfl h, fun p hp => by simp at hp, TrioCof.steps1_nil⟩, ?_, ?_, ?_⟩
  · intro j hj; simp at hj
  · intro j hj; simp at hj
  · intro j hj; simp at hj

theorem tInv_oper {M : TrioCof.TrioSeq} (h : TInv M) {n : Nat} (hn : 1 ≤ n) :
    TInv (TrioCof.oper M n) :=
  ⟨TrioCof.blockok_oper h.1 hn, TrioCof.z0ok_oper h.2.1, TrioCof.noninc_oper h.2.2.1,
    TrioCof.r1ok_oper h.2.2.2⟩

/-- **On `TInv` the two expansions agree**, so `TInv` passes to every expansion. -/
theorem expandRL_toL_tInv {M : TrioCof.TrioSeq} (h : TInv M) (N : Nat) :
    ∃ M', expandRL 3 N (toL M) = toL M' ∧ TInv M' := by
  by_cases hlen : 1 < M.length
  · refine ⟨TrioCof.oper M (N + 1), expandRL_toL_of N hlen ?_, tInv_oper h (by omega)⟩
    intro hz
    refine TrioCof.hp_last h.1 h.2.1 h.2.2.1 (by omega) ?_
    intro he
    apply hz
    refine ⟨?_, ?_, ?_⟩
    · show (M.getD (M.length - 1) (0, 0, 0)).1 = 0
      rw [he]
    · show (M.getD (M.length - 1) (0, 0, 0)).2.1 = 0
      rw [he]
    · show (M.getD (M.length - 1) (0, 0, 0)).2.2 = 0
      rw [he]
  · refine ⟨[], ?_, tInv_nil⟩
    rw [expandRL_short _ (by rw [toL_length]; omega)]
    rfl

/-! ### The start -/

/-- The start `(0,0,0)(1,1,0)(2,2,1)(3,3,1)⋯(v+2,v+2,1)` as a trio sequence. -/
def startT (v : Nat) : TrioCof.TrioSeq :=
  (List.range (v + 3)).map (fun j => (j, j, if j ≤ 1 then 0 else 1))

theorem startT_getD (v : Nat) {j : Nat} (hj : j < v + 3) :
    (startT v).getD j (0, 0, 0) = (j, j, if j ≤ 1 then 0 else 1) := by
  rw [startT, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  rfl

@[simp] theorem startT_length (v : Nat) : (startT v).length = v + 3 := by simp [startT]

theorem toL_startT (v : Nat) : toL (startT v) = lift 3 (trioGen (v + 1)) := by
  rw [lift_trioGen_succ, toL, startT, List.map_map, map_range_succ_front, map_range_succ_front,
    map_range_succ_front]
  simp only [Function.comp, List.map_cons, List.cons.injEq]
  refine ⟨rfl, rfl, rfl, List.map_congr_left (fun i _ => ?_)⟩
  simp [colL]

theorem tInv_startT (v : Nat) : TInv (startT v) := by
  refine ⟨⟨fun _ => ?_, fun p _ => Nat.zero_le _, ?_⟩, ?_, ?_, ?_⟩
  · rw [startT, List.range_succ_eq_map]; rfl
  · rw [TrioCof.steps1_iff]
    intro j hj
    rw [startT_length] at hj
    rw [startT_getD v hj, startT_getD v (by omega)]
    try omega
  · intro j hj h0
    rw [startT_length] at hj
    rw [startT_getD v hj] at h0 ⊢
    simp only at h0
    subst h0
    simp
  · intro j hj
    rw [startT_length] at hj
    rw [startT_getD v hj]
    simp only
    split <;> omega
  · intro j hj h0
    rw [startT_length] at hj
    rw [startT_getD v hj] at h0
    simp only at h0
    refine ⟨j - 1, by omega, ?_, fun l a b => by omega, ?_⟩
    · rw [startT_getD v hj, startT_getD v (by omega)]
      simp only
      omega
    · rw [startT_getD v hj, startT_getD v (by omega)]
      simp only
      omega

/-- **Every reached matrix is a trio sequence with trio's invariants.** -/
theorem sReach_tInv {C : List (List Nat)} (h : SReach C) : ∃ M, C = toL M ∧ TInv M := by
  induction h with
  | gen v =>
    exact ⟨startT v, by rw [expandRL_cgen_two_four, toL_startT], tInv_startT v⟩
  | step N _ ih =>
    obtain ⟨M, rfl, hM⟩ := ih
    obtain ⟨M', e, hM'⟩ := expandRL_toL_tInv hM N
    exact ⟨M', e, hM'⟩

/-! ### `R1` and the row-`0` step -/

theorem entry_zero_eq (M : TrioCof.TrioSeq) (j : Nat) :
    TrioCof.entry M 0 j = (M.getD j (0, 0, 0)).1 := rfl
theorem entry_one_eq (M : TrioCof.TrioSeq) (j : Nat) :
    TrioCof.entry M 1 j = (M.getD j (0, 0, 0)).2.1 := rfl

/-- On `r1ok`, the row-`0` parent is one below in row `0` and at most one below
in row `1`. -/
theorem parR0_of_r1ok {M : TrioCof.TrioSeq} (h : TrioCof.r1ok M) {p v : Nat}
    (hp : ParR (toL M) 0 p v) :
    TrioCof.entry M 0 p + 1 = TrioCof.entry M 0 v ∧
      TrioCof.entry M 1 v ≤ TrioCof.entry M 1 p + 1 := by
  rw [ParR0_eq] at hp
  obtain ⟨_, hv, hpv, h0, hbetween⟩ := hp
  rw [entry_zero_eq, entry_zero_eq] at h0
  obtain ⟨k, hkv, hk0, hkb, hk1⟩ := h v hv (by omega)
  have hkp : k = p := by
    rcases Nat.lt_trichotomy k p with hlt | heq | hgt
    · have := hkb p hlt hpv
      omega
    · exact heq
    · have := hbetween k ⟨hgt, hkv⟩
      rw [entry_zero_eq, entry_zero_eq] at this
      omega
  subst hkp
  rw [entry_zero_eq, entry_zero_eq, entry_one_eq, entry_one_eq]
  exact ⟨hk0, hk1⟩

/-- A column's row-`0` parent has row-`0` entry one less. -/
def R0 (C : List (List Nat)) : Prop :=
  ∀ p v, ParR C 0 p v → (C[p]!)[0]! + 1 = (C[v]!)[0]!

theorem r0_r1_of_sReach {C : List (List Nat)} (h : SReach C) : R0 C ∧ R1 C := by
  obtain ⟨M, rfl, hM⟩ := sReach_tInv h
  refine ⟨fun p v hp => ?_, fun p v hp => ?_⟩
  · have := (parR0_of_r1ok hM.2.2.2 hp).1
    rw [TrioCofinal.toL_e0, TrioCofinal.toL_e0]
    exact this
  · have := (parR0_of_r1ok hM.2.2.2 hp).2
    rw [TrioCofinal.toL_e1, TrioCofinal.toL_e1]
    exact this

theorem r1_of_sReach {C : List (List Nat)} (h : SReach C) : R1 C := (r0_r1_of_sReach h).2
theorem r0_of_sReach {C : List (List Nat)} (h : SReach C) : R0 C := (r0_r1_of_sReach h).1

/-! ### `Low2` -/

/-- **Every column of an expansion has a source column** with the same row-`2`
entry and a row-`1` entry no larger (or is past the end). -/
theorem expandRL_col_source (N : Nat) (l : List (List Nat)) (i : Nat) :
    (((expandRL 3 N l)[i]!)[1]! = 0 ∧ ((expandRL 3 N l)[i]!)[2]! = 0) ∨
      ∃ j : Nat, (l[j]!)[1]! ≤ ((expandRL 3 N l)[i]!)[1]! ∧
        ((expandRL 3 N l)[i]!)[2]! = (l[j]!)[2]! := by
  cases hb : badRootR 3 l with
  | none =>
    rw [expandRL, hb]
    dsimp only
    rw [getElem!_dropLast']
    split
    · exact Or.inr ⟨i, le_rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  | some p =>
    have hp : p + 1 < l.length := badRootR_lt hb
    have hm3 : m0L 3 l < 3 := m0L_lt (by norm_num) l
    by_cases hip : i < p
    · rw [expandRL_get_pre hb N hip]
      exact Or.inr ⟨i, le_rfl, rfl⟩
    · obtain ⟨t, rfl⟩ : ∃ t, i = p + t := ⟨i - p, by omega⟩
      by_cases ht : t < (N + 1) * (l.length - 1 - p)
      · refine Or.inr ⟨p + t % (l.length - 1 - p), ?_, ?_⟩
        · rw [expandRL_get_copy hb N ht 1 (by omega)]
          omega
        · rw [expandRL_get_copy hb N ht 2 (by omega), if_neg (by omega), Nat.add_zero]
      · have hlen := expandRL_length_some hb N
        rw [getElem!_neg _ (p + t) (by omega)]
        exact Or.inl ⟨rfl, rfl⟩

theorem low2_expandRL {l : List (List Nat)} (h : Low2 l) (N : Nat) : Low2 (expandRL 3 N l) := by
  intro i hi
  rcases expandRL_col_source N l i with ⟨_, h2⟩ | ⟨j, hj1, hj2⟩
  · exact h2
  · rw [hj2]
    exact h j (by omega)

theorem low2_start (v : Nat) : Low2 (lift 3 (trioGen (v + 1))) := by
  intro i hi
  rw [← toL_startT, TrioCofinal.toL_e1] at hi
  rw [← toL_startT, TrioCofinal.toL_e2]
  by_cases hiv : i < v + 3
  · have e1 : TrioCof.entry (startT v) 1 i = i := by
      rw [entry_one_eq, startT_getD v hiv]
    have e2 : TrioCof.entry (startT v) 2 i = if i ≤ 1 then 0 else 1 := by
      show ((startT v).getD i (0, 0, 0)).2.2 = _
      rw [startT_getD v hiv]
    rw [e1] at hi
    rw [e2, if_pos hi]
  · show ((startT v).getD i (0, 0, 0)).2.2 = 0
    rw [List.getD_eq_default _ _ (by rw [startT_length]; omega)]

theorem low2_of_sReach {C : List (List Nat)} (h : SReach C) : Low2 C := by
  induction h with
  | gen v => rw [expandRL_cgen_two_four]; exact low2_start v
  | step N _ ih => exact low2_expandRL ih N

/-! ### The commutation on the reached matrices -/

/-- **On `SReach`, outside `RaisedPar`, `t3n` commutes with expansion.** -/
theorem expandRL_t3n_of_sReach {C : List (List Nat)} (h : SReach C) (hnp : ¬ RaisedPar C)
    (N : Nat) : expandRL 3 N (t3n C) = t3n (expandRL 3 N C) :=
  expandRL_t3n h.valid (low2_of_sReach h) (r1_of_sReach h) hnp N

end Googology.Trans.DBMS

#print axioms Googology.Trans.DBMS.low2_of_sReach
#print axioms Googology.Trans.DBMS.r0_r1_of_sReach
#print axioms Googology.Trans.DBMS.expandRL_t3n_of_sReach
