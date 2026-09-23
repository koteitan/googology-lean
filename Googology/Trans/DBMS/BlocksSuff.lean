import Googology.Trans.DBMS.BlocksStd

/-!
# Which lists of blocks are standard: the sufficient direction

`BlocksStd.lean` proves that a DBMS standard form with `r + 1` rows is a list
of blocks `blkR M₀ ++ ⋯ ++ blkR Mₖ` whose contents lie in the content system
`CReach r`, each reached from every earlier one by steps of BM4 (`DChain`), and
reduces the converse to `DupProp r`.  This file proves the converse, for every
number of rows, so in particular `DupProp 2`.

* `rt_prefix`: `[0]` removes the last column, so `A ++ B` reaches `A`.
* `rt_zero_last`: in the content system, `Q ++ [c]` reaches `Q ++ [0⃗]`
  (`0⃗` the zero column).  If `c` is not zero, `(Q ++ [c])[1] = Q ++ x :: X'`,
  which reaches `Q ++ [x]` of smaller rank; induction on the rank.
* `rt_append_zero`: if `X` reaches `M ≠ X`, then `X` reaches `M ++ [0⃗]`.  The
  last step is `M = Y[N]`; if the last column of `Y` is zero then
  `M ++ [0⃗] = Y`, and otherwise `Y[N + 1] = M ++ z :: Z'` reaches `M ++ [z]`,
  which reaches `M ++ [0⃗]`.
* `dstdL_of_dchain` (**sufficient**): every list of blocks of the chain form is
  standard.  A run `X, X, …, X` of `n + 1` equal contents is
  `(blkR (X ++ [0⃗]))[n]`; passing from `X` to the next content `Y ≠ X`, the
  last block `blkR X` is replaced by `blkR (Y ++ [0⃗])`, reached from `X` by
  `rt_append_zero`.
* `dupProp` (`DupProp r` for every `r`), `dstdL_iff_dchain`, and at three rows
  `dupProp_two`, `dstdL_three_iff`.
-/

namespace Googology.Trans.DBMS

open BM4
open Googology.Notation.DBMS
open Googology.Trans.BMS
open Ordinal Order

/-- `[0]` removes the last column: a list reaches each of its prefixes. -/
theorem rt_prefix {r : Nat} (A : List (List Nat)) : ∀ B : List (List Nat), Valid r (A ++ B) →
    Relation.ReflTransGen (CStep r) (A ++ B) A := by
  intro B
  induction B using List.reverseRecOn with
  | nil => intro _; rw [List.append_nil]
  | append_singleton B b ih =>
    intro hv
    have hv' : Valid r (A ++ B) := fun v hv0 => hv v (by
      rcases List.mem_append.mp hv0 with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_append_left _ h))
    have hs : CStep r (A ++ (B ++ [b])) (A ++ B) :=
      ⟨0, by rw [expandRL_zero (r + 1) _ hv, ← List.append_assoc, List.dropLast_concat]⟩
    exact Relation.ReflTransGen.head hs (ih hv')

theorem eq_zcol_of_isZ {v : List Nat} (h : IsZ v) : v = zcol v.length := by
  apply List.ext_getElem (by simp [zcol])
  intro i h1 _
  have := h i
  rw [getElem!_pos v i h1] at this
  simp [zcol, this]

theorem dropLast_append_zcol {r : Nat} {Y : List (List Nat)} (hv : Valid r Y) (hne : Y ≠ [])
    (hlast : IsZ (Y[Y.length - 1]!)) : Y.dropLast ++ [zcol (r + 1)] = Y := by
  have hpos : 0 < Y.length := List.length_pos_iff.mpr hne
  have hg : Y[Y.length - 1]! = Y.getLast hne := by
    rw [getElem!_pos Y _ (by omega), List.getLast_eq_getElem]
  have hl : (Y.getLast hne).length = r + 1 := hv _ (List.getLast_mem hne)
  have hz : Y.getLast hne = zcol (r + 1) := by
    rw [← hl]; exact eq_zcol_of_isZ (by rw [← hg]; exact hlast)
  conv_rhs => rw [← List.dropLast_append_getLast hne]
  rw [hz]

theorem rt_zero_last_aux (r : Nat) (o : Ordinal.{0}) : ∀ (Q : List (List Nat)) (c : List Nat),
    rkL r (Q ++ [c]) = o → CReach r (Q ++ [c]) →
    Relation.ReflTransGen (CStep r) (Q ++ [c]) (Q ++ [zcol (r + 1)]) := by
  induction o using WellFoundedLT.induction with
  | _ o ih =>
  intro Q c ho hC
  have hv := hC.valid
  have hcl : c.length = r + 1 := hv c (by simp)
  have hlastEq : (Q ++ [c])[(Q ++ [c]).length - 1]! = c := by
    rw [List.length_append, List.length_singleton, Nat.add_sub_cancel,
      getElem!_pos _ _ (by simp)]
    simp
  by_cases hz : IsZ c
  · have hc : c = zcol (r + 1) := by rw [eq_zcol_of_isZ hz, hcl]
    rw [hc]
  · have hne : Q ++ [c] ≠ [] := by simp
    obtain ⟨p, hb⟩ := badRootR_isSome (r + 1) hC.rooted hne (by rw [hlastEq]; exact hz)
    obtain ⟨X, hX, he⟩ := expandRL_succ_append (r + 1) 0 (Q ++ [c]) hb
    rw [expandRL_zero (r + 1) _ hv, List.dropLast_concat] at he
    obtain ⟨x, X', rfl⟩ := List.exists_cons_of_ne_nil hX
    have h1 : CStep r (Q ++ [c]) (Q ++ x :: X') := ⟨1, he.symm⟩
    have hC1 : CReach r (Q ++ x :: X') := by rw [← he]; exact CReach.step _ hC
    have h2 : Relation.ReflTransGen (CStep r) (Q ++ x :: X') (Q ++ [x]) := by
      have := rt_prefix (r := r) (Q ++ [x]) X' (by simpa using hC1.valid)
      simpa using this
    have hC2 : CReach r (Q ++ [x]) := hC1.of_rt h2
    have hlt : rkL r (Q ++ [x]) < o := by
      rw [← ho]
      calc rkL r (Q ++ [x]) ≤ rkL r (Q ++ x :: X') := (rkL_le_of_rt hC1.valid h2).1
        _ < rkL r (Q ++ [c]) := by rw [← he]; exact rkL_lt hv hne _
    exact Relation.ReflTransGen.head h1 (h2.trans (ih _ hlt Q x rfl hC2))

/-- **The last column can be lowered to the zero column**: in the content
system, `Q ++ [c]` reaches `Q ++ [0⃗]`. -/
theorem rt_zero_last {r : Nat} {Q : List (List Nat)} {c : List Nat} (hC : CReach r (Q ++ [c])) :
    Relation.ReflTransGen (CStep r) (Q ++ [c]) (Q ++ [zcol (r + 1)]) :=
  rt_zero_last_aux r _ Q c rfl hC

/-- **A content reached properly can be followed by a zero column**: if `X`
reaches `M ≠ X`, then `X` reaches `M ++ [0⃗]`. -/
theorem rt_append_zero {r : Nat} {X M : List (List Nat)} (hX : CReach r X)
    (h : Relation.ReflTransGen (CStep r) X M) (hne : M ≠ X) :
    Relation.ReflTransGen (CStep r) X (M ++ [zcol (r + 1)]) := by
  induction h with
  | refl => exact absurd rfl hne
  | @tail Y M hXY hYM ih =>
    obtain ⟨N, rfl⟩ := hYM
    have hY : CReach r Y := hX.of_rt hXY
    by_cases hY0 : Y = []
    · subst hY0
      rw [expandRL_nil] at hne ⊢
      exact ih hne
    · by_cases hlast : IsZ (Y[Y.length - 1]!)
      · have e : expandRL (r + 1) N Y = Y.dropLast := by
          rw [expandRL, badRootR_none_of_isZ (r + 1) hlast]
        rw [e, dropLast_append_zcol hY.valid hY0 hlast]
        exact hXY
      · obtain ⟨p, hb⟩ := badRootR_isSome (r + 1) hY.rooted hY0 hlast
        obtain ⟨Z, hZ, he⟩ := expandRL_succ_append (r + 1) N Y hb
        obtain ⟨z, Z', hZe⟩ := List.exists_cons_of_ne_nil hZ
        subst hZe
        have hC1 : CReach r (expandRL (r + 1) N Y ++ z :: Z') := by
          rw [← he]; exact CReach.step _ hY
        have h2 : Relation.ReflTransGen (CStep r) (expandRL (r + 1) N Y ++ z :: Z')
            (expandRL (r + 1) N Y ++ [z]) := by
          have := rt_prefix (r := r) (expandRL (r + 1) N Y ++ [z]) Z' (by simpa using hC1.valid)
          simpa using this
        have hC2 : CReach r (expandRL (r + 1) N Y ++ [z]) := hC1.of_rt h2
        exact ((hXY.tail ⟨N + 1, he.symm⟩).trans h2).trans (rt_zero_last hC2)

/-- A block whose content ends in a zero column expands to copies of the block
without it. -/
theorem dstdL_rep_of_zero {r : Nat} {P X : List (List Nat)} (hX : CReach r (X ++ [zcol (r + 1)]))
    (h : DStdL r (P ++ blkR (r + 1) (X ++ [zcol (r + 1)]))) (n : Nat) :
    DStdL r (P ++ blocksR r (List.replicate (n + 1) X)) := by
  have hn := h.expand n
  have hl : (X ++ [zcol (r + 1)])[(X ++ [zcol (r + 1)]).length - 1]! = zcol (r + 1) := by
    rw [List.length_append, List.length_singleton, Nat.add_sub_cancel,
      getElem!_pos _ _ (by simp)]
    simp
  rw [expandRL_append (r + 1) n _ _ (by rw [blkR_get0, zcol_get]) (by simp [blkR]),
    expandRL_blkR_zero (r + 1) n (Nat.succ_pos r) hX.valid (by simp)
      (by rw [hl]; exact isZ_zcol _), List.dropLast_concat, repN_blkR] at hn
  exact hn

theorem dstdL_chain_rep {r : Nat} : ∀ (Ms : List (List (List Nat))) (P X : List (List Nat)),
    (∀ n, DStdL r (P ++ blocksR r (List.replicate (n + 1) X))) → DChain r (X :: Ms) →
    DStdL r (P ++ blocksR r (X :: Ms))
  | [], P, X, h, _ => by simpa using h 0
  | Y :: Ms, P, X, h, hc => by
    have hX : CReach r X := hc.1 X (by simp)
    have hXY : Relation.ReflTransGen (CStep r) X Y := List.rel_of_pairwise_cons hc.2 (by simp)
    have hc' : DChain r (Y :: Ms) := hc.sublist (List.sublist_cons_self _ _)
    rw [blocksR_cons, ← List.append_assoc]
    by_cases hYX : Y = X
    · subst hYX
      refine dstdL_chain_rep Ms (P ++ blkR (r + 1) Y) Y (fun n => ?_) hc'
      have := h (n + 1)
      rw [List.replicate_succ, blocksR_cons, ← List.append_assoc] at this
      exact this
    · have hZ := rt_append_zero hX hXY hYX
      have h1 : DStdL r ((P ++ blkR (r + 1) X) ++ blkR (r + 1) X) := by
        have := h 1
        simpa [blocksR, List.replicate] using this
      have h2 := dstdL_append_blkR_rt hX h1 hZ
      exact dstdL_chain_rep Ms (P ++ blkR (r + 1) X) Y
        (fun n => dstdL_rep_of_zero (hX.of_rt hZ) h2 n) hc'

theorem cgen_dropLast (r m : Nat) : (cgen r (m + 1)).dropLast = cgen r m := by
  simp [cgen, List.range_succ]

/-- **Sufficient**: a list of blocks whose contents lie in the content system,
each reached from every earlier one, is a DBMS standard form, at every number
of rows. -/
theorem dstdL_of_dchain {r : Nat} {Ms : List (List (List Nat))} (h : DChain r Ms) :
    DStdL r (blocksR r Ms) := by
  cases Ms with
  | nil => exact dstdL_nil r
  | cons X Ms =>
    have hX : CReach r X := h.1 X (by simp)
    obtain ⟨m, hm⟩ := hX.exists_rt
    have hstep : CStep r (cgen r (m + 1)) (cgen r m) :=
      ⟨0, by rw [expandRL_zero (r + 1) _ (valid_cgen r (m + 1)), cgen_dropLast]⟩
    have hrt : Relation.ReflTransGen (CStep r) (cgen r (m + 1)) X :=
      Relation.ReflTransGen.head hstep hm
    have hne : X ≠ cgen r (m + 1) := by
      intro he
      have h1 := (rkL_le_of_rt (valid_cgen r m) hm).1
      rw [he] at h1
      exact absurd (lt_of_le_of_lt h1 (rkL_cgen_lt_succ r m)) (lt_irrefl _)
    have hZ := rt_append_zero (CReach.gen (m + 1)) hrt hne
    have h0 := dstdL_append_blkR_rt (P := []) (CReach.gen (m + 1))
      (by simpa using dstdL_blkR_cgen r (m + 1)) hZ
    have := dstdL_chain_rep Ms [] X
      (fun n => dstdL_rep_of_zero ((CReach.gen _).of_rt hZ) (by simpa using h0) n) h
    simpa using this

/-- **Duplication holds at every number of rows.** -/
theorem dupProp (r : Nat) : DupProp r :=
  dupProp_of_suff (fun _ h => dstdL_of_dchain h)

/-- **The characterization in the reach form, at every number of rows.** -/
theorem dstdL_iff_dchain (r : Nat) (l : List (List Nat)) :
    DStdL r l ↔ ∃ Ms, DChain r Ms ∧ l = blocksR r Ms :=
  dstdL_iff_dchain_of_dup (dupProp r) l

/-- **Three rows: duplication.** -/
theorem dupProp_two : DupProp 2 := dupProp 2

/-- **Three rows: the characterization in the reach form.**  A list of columns
is a standard form of three-row DBMS exactly when it is a list of blocks whose
contents lie in the content system `C₃`, each reached from every earlier one. -/
theorem dstdL_three_iff (l : List (List Nat)) :
    DStdL 2 l ↔ ∃ Ms, DChain 2 Ms ∧ l = blocksR 2 Ms :=
  dstdL_three_iff_of_dup dupProp_two l

end Googology.Trans.DBMS
