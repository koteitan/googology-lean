import Googology.Trans.BMS.TrioTree
import Googology.Trans.BMS.TrioStd
import Googology.Notation.ExBuchholz.System
import Googology.Notation.ExBuchholz.Onto

/-!
# The trio matrices below `ψ_0(Ω_2)` are standard forms

`TrioTree.lean` writes the trio map of
[koteitan/trio](https://github.com/koteitan/trio) on the countable standard
forms whose subscripts are `0` or `1` as a structural recursion `trioE` (what
`TrioRules.trioMatrixL` computes there at nesting depth at most `200`, proved in
`TrioTreeRules.lean` as `trioMatrixL_eq_trioE`), and proves
that it keeps the order.  This file proves the other half of what
`TrioStd.lean` proves below `ε₀`:

  `trioE_std`: for standard `α < Ω` with every subscript `0` or `1`,
  `trioE α` is the entries of a standard three-row array.

All such `α` lie below `ψ_0(Ω_2)` (`TrioTree.lt_bho_of_frag`).  Below `ε₀` this
is `TrioStd.omegaIndexMatrix_std` again (`TrioTree.trioE_allNil`).

## How the proof goes

`TrioStd.lean` inducts along the one-row expansions of `α`.  That does not
carry over: above `ε₀` the trio matrix of `ψ_0(Ω_{α[n]})` is in general not a
prefix of an expansion of the matrix of `ψ_0(Ω_α)` (at `α = ε₀·ω = ψ_0(Ω+1)`,
`α[n] = ε₀·n` is a row of `n` add units, while the matrix of `α` expands into
one add unit whose tree has `n` roots).  The proof works on the matrices
instead, in three layers.

* **Trees.**  `treeB x t` writes a term as a tree: a summand `ψ_ν(b)` is the
  column `(x, ν, 0)` followed by the tree of `b` at `x + 1`.  One expansion of
  the tree of `G` has the tree of the fundamental sequence `G[n]` as a prefix
  (`treeStep`, `nodeStep`), whatever stands before it.  The last summand
  decides: `ψ_ν(b + 1)` copies the node (`expandRL_copy_block`), a last summand
  of limit `ω` expands inside, and an argument whose limit is indexed by the
  countable terms (`dom b = Ω`) ends along its last summands in a leaf `Ω` at
  some depth `d` below a chain of `ψ_1` nodes (`hole`, `hole_anc`); then the
  node is nested `n + 1` times, each copy `d + 1` columns to the right
  (`expandRL_diag`), which is Buchholz's diagonal `ψ_0(b)[n]`.  So by the
  descent of `Reach.lean` (`exists_le_fs_idx`, `OTLt_wf`) every standard tree
  below `G` is reachable from the tree of `G` (`treeReach`), and every tree of
  the fragment is reachable under the first digit from the top `ψ_0(Ω_2)`,
  whose tree `(3,0,0)(4,1,0)(5,2,0)` expands to the chains of `ψ_1`
  (`first_unit`, `expandRL_top`, `reach3_top6`).
* **Multiply units.**  The last unit's list of trees comes down to anything
  below it in the dictionary order (`mulDesc`), by four moves on the last
  tree: lower it (`move_tree`), turn `δ + 1` into `δ, …, δ` (`move_copy`),
  and at the unit level turn a bare final digit into copies of the unit
  (`move_units`, from `expandRL_digit_unitE`: the trees ride along without
  their `y` changing, since each leaf `Ω` has a `ψ_0` node as a row-0
  ancestor, `AncP`) and a unit without digits into units `1` (`move_ones`).
* **Add units.**  Every descending row of units is reachable (`unitFill`,
  `reach_units`), and `trioE α` is such a row (`trioE_eq`, `descU_dataOf`,
  `unitsOK_dataOf`).

Nothing here is taken from the Lean files of koteitan/trio.
-/

namespace Googology.Trans.BMS.TrioTreeStd

open BM4 Pat
open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term
open Googology.Trans.BMS.TrioStd
open Googology.Trans.BMS.TrioTree

/-! ### Terms: appending, the last summand, the fragment -/

/-- The sum `s + v`, written as appending the summands. -/
def appT : Term → Term → Term
  | nil, v => v
  | cons a b t, v => cons a b (appT t v)

theorem appT_nil_right : ∀ s : Term, appT s nil = s
  | nil => rfl
  | cons a b t => by rw [appT, appT_nil_right t]

theorem treeB_appT (x : Nat) : ∀ s v : Term, treeB x (appT s v) = treeB x s ++ treeB x v
  | nil, _ => rfl
  | cons a b t, v => by rw [appT, treeB, treeB, treeB_appT x t v, List.append_assoc]

theorem size_appT : ∀ s v : Term, size (appT s v) = size s + size v
  | nil, _ => by simp [appT]
  | cons a b t, v => by rw [appT, size_cons, size_cons, size_appT t v]; omega

theorem appT_psi_eq_cons (s c d : Term) : ∃ e f w, appT s (psi c d) = cons e f w := by
  cases s with
  | nil => exact ⟨c, d, nil, rfl⟩
  | cons a b t => exact ⟨a, b, _, rfl⟩

/-- Every nonzero term is a sum followed by a last principal term. -/
theorem snoc_view : ∀ t : Term, t ≠ nil → ∃ s c d, t = appT s (psi c d)
  | nil, h => absurd rfl h
  | cons a b u, _ => by
    by_cases hu : u = nil
    · subst hu; exact ⟨nil, a, b, rfl⟩
    · obtain ⟨s, c, d, rfl⟩ := snoc_view u hu
      exact ⟨cons a b s, c, d, rfl⟩

theorem fs_appT (Y : Term) : ∀ s c d : Term, fs (appT s (psi c d)) Y = appT s (fs (psi c d) Y)
  | nil, _, _ => rfl
  | cons a b t, c, d => by
    obtain ⟨e, f, w, hw⟩ := appT_psi_eq_cons t c d
    rw [appT, hw, fs, ← hw, fs_appT Y t c d, appT]

theorem dom_appT : ∀ s c d : Term, dom (appT s (psi c d)) = dom (psi c d)
  | nil, _, _ => rfl
  | cons a b t, c, d => by
    obtain ⟨e, f, w, hw⟩ := appT_psi_eq_cons t c d
    rw [appT, hw, show dom (cons a b (cons e f w)) = dom (cons e f w) from rfl, ← hw,
      dom_appT t c d]

theorem idx_appT (s c d : Term) (n : Nat) : idx (appT s (psi c d)) n = idx (psi c d) n := by
  rw [idx, idx, dom_appT]

theorem OT_appT_last : ∀ s c d : Term, OT (appT s (psi c d)) → OT (psi c d)
  | nil, _, _, h => h
  | cons _ _ t, c, d, h => OT_appT_last t c d (OT_tail h)

/-- A countable term of the fragment: summands `ψ_0(b)`, every subscript
`0` or `1`. -/
def CtS : Term → Prop
  | nil => True
  | cons a b t => a = nil ∧ Sub01 b ∧ CtS t

theorem sub01_of_ctS : ∀ t : Term, CtS t → Sub01 t
  | nil, _ => trivial
  | cons _ _ t, h => ⟨Or.inl h.1, h.2.1, sub01_of_ctS t h.2.2⟩

theorem topNil_of_ctS : ∀ t : Term, CtS t → TopNil t
  | nil, _ => trivial
  | cons _ _ t, h => ⟨h.1, topNil_of_ctS t h.2.2⟩

theorem ctS_of : ∀ t : Term, TopNil t → Sub01 t → CtS t
  | nil, _, _ => trivial
  | cons _ _ t, h, hs => ⟨h.1, hs.2.1, ctS_of t h.2 hs.2.2⟩

theorem sub01_appT : ∀ s v : Term, Sub01 (appT s v) ↔ Sub01 s ∧ Sub01 v
  | nil, v => by simp [appT, Sub01]
  | cons a b t, v => by
    simp only [appT, Sub01, sub01_appT t v, and_assoc]

theorem ctS_appT : ∀ s v : Term, CtS (appT s v) ↔ CtS s ∧ CtS v
  | nil, v => by simp [appT, CtS]
  | cons a b t, v => by
    simp only [appT, CtS, ctS_appT t v, and_assoc]

theorem ctS_of_allNil (t : Term) (h : AllNil t) : CtS t :=
  ctS_of t (topNil_of_allNil t h) (sub01_of_allNil t h)

theorem sub01_repeatPrin {ν b : Term} (hν : ν = nil ∨ ν = t1) (hb : Sub01 b) :
    ∀ n, Sub01 (repeatPrin ν b n)
  | 0 => trivial
  | n + 1 => ⟨hν, hb, sub01_repeatPrin hν hb n⟩

theorem topNil_repeatPrin (b : Term) : ∀ n, TopNil (repeatPrin nil b n)
  | 0 => trivial
  | n + 1 => ⟨rfl, topNil_repeatPrin b n⟩

/-! ### `dom` and `fs` on the fragment -/

theorem tW_not_lt_psi0 (b : Term) : ¬ tW < cons nil b nil := by
  intro h
  rcases psi_lt_psi_iff.mp h with h | ⟨h, _⟩
  · exact not_lt_nil _ h
  · exact Term.noConfusion h

theorem tW_lt_psi1 {b : Term} (hb : b ≠ nil) : tW < cons t1 b nil := by
  refine psi_lt_psi_iff.mpr (Or.inr ⟨rfl, ?_⟩)
  cases b with
  | nil => exact absurd rfl hb
  | cons _ _ _ => exact nil_lt_cons _ _ _

theorem dom_t1 : dom t1 = t1 := by decide
theorem dom_tW : dom tW = tW := by decide

theorem fs_t1_nil : fs t1 nil = nil := by
  rw [fs]; simp [dom]

theorem fs_tW (Y : Term) : fs tW Y = Y := fs_psi_nil_of_one dom_t1

/-- **The shape of a limit in the fragment**: a successor, an `ω`-limit, or
indexed by the countable terms (`Ω`). -/
theorem dom_sub01 : ∀ t : Term, Sub01 t → t ≠ nil → dom t = t1 ∨ dom t = tw ∨ dom t = tW
  | nil, _, h => absurd rfl h
  | cons a b u, h, _ => by
    cases u with
    | cons c d w =>
      rw [show dom (cons a b (cons c d w)) = dom (cons c d w) from rfl]
      exact dom_sub01 _ h.2.2 (fun h => Term.noConfusion h)
    | nil =>
      by_cases hb0 : b = nil
      · subst hb0
        rcases h.1 with rfl | rfl
        · exact Or.inl dom_t1
        · exact Or.inr (Or.inr dom_tW)
      · rcases h.1 with rfl | rfl
        · right; left
          rcases dom_sub01 b h.2.1 hb0 with e | e | e
          · exact dom_psi_of_one e
          · exact dom_psi_of_tw e
          · exact dom_psi_of_case4 (by rw [e]; decide) (by rw [e]; decide) (by rw [e]; decide)
              (by rw [e]; exact tW_not_lt_psi0 b)
        · rcases dom_sub01 b h.2.1 hb0 with e | e | e
          · exact Or.inr (Or.inl (dom_psi_of_one e))
          · exact Or.inr (Or.inl (dom_psi_of_tw e))
          · right; right
            rw [dom_psi_of_lt (by rw [e]; decide) (by rw [e]; decide) (by rw [e]; decide)
              (by rw [e]; exact tW_lt_psi1 hb0), e]

theorem dom_psi0_sub01 {b : Term} (hb : Sub01 b) (hne : b ≠ nil) : dom (psi nil b) = tw := by
  rcases dom_sub01 b hb hne with e | e | e
  · exact dom_psi_of_one e
  · exact dom_psi_of_tw e
  · exact dom_psi_of_case4 (by rw [e]; decide) (by rw [e]; decide) (by rw [e]; decide)
      (by rw [e]; exact tW_not_lt_psi0 b)

/-! ### Trees -/

theorem treeB_len (x : Nat) : ∀ t : Term, ∀ c ∈ treeB x t, c.length = 3
  | nil => by intro c hc; simp [treeB] at hc
  | cons a b u => by
    intro c hc
    rw [treeB, List.mem_append, List.mem_cons] at hc
    rcases hc with (rfl | h) | h
    · rfl
    · exact treeB_len (x + 1) b c h
    · exact treeB_len x u c h

theorem treeB_ge (t : Term) : ∀ (x : Nat), ∀ col ∈ treeB x t, x ≤ col[0]! := by
  induction t with
  | nil => intro x col hc; simp [treeB] at hc
  | cons a b u _ ihb ihu =>
    intro x col hc
    rw [treeB, List.mem_append, List.mem_cons] at hc
    rcases hc with (rfl | h) | h
    · simp
    · have := ihb (x + 1) col h; omega
    · exact ihu x col h

theorem treeB_repeatPrin (x : Nat) (ν b : Term) : ∀ n : Nat,
    treeB x (repeatPrin ν b n)
      = (List.replicate n ([x, subY ν, 0] :: treeB (x + 1) b)).flatten
  | 0 => rfl
  | n + 1 => by
    show ([x, subY ν, 0] :: treeB (x + 1) b) ++ treeB x (repeatPrin ν b n) = _
    rw [treeB_repeatPrin x ν b n, List.replicate_succ, List.flatten_cons]

/-- Move a column `d` to the right. -/
def shiftC (d : Nat) (col : List Nat) : List Nat := [col[0]! + d, col[1]!, col[2]!]

theorem shiftC_shiftC (a b : Nat) (col : List Nat) :
    shiftC a (shiftC b col) = shiftC (b + a) col := by
  simp [shiftC]; omega

theorem treeB_shift (d : Nat) (t : Term) : ∀ x : Nat,
    (treeB x t).map (shiftC d) = treeB (x + d) t := by
  induction t with
  | nil => intro x; rfl
  | cons a b u _ ihb ihu =>
    intro x
    rw [treeB, treeB, List.map_append, List.map_cons, ihb, ihu,
      show x + 1 + d = x + d + 1 by omega]
    simp [shiftC]

/-! ### A `ψ_0` node whose argument ends in `Ω` -/

/-- **The hole.**  An argument whose limit is indexed by the countable terms
ends, along its last summands, in a leaf `Ω` at some depth `d`: its tree is a
prefix and the column `(x + d, 1, 0)`, and `b[Y]` puts the tree of `Y` in
place of that column. -/
theorem hole : ∀ (m : Nat) (b : Term), size b ≤ m → Sub01 b → dom b = tW →
    ∃ d, ∀ x, treeB x b = (treeB x b).dropLast ++ [[x + d, 1, 0]] ∧
      ∀ Y, treeB x (fs b Y) = (treeB x b).dropLast ++ treeB (x + d) Y ∧
        (Sub01 Y → Sub01 (fs b Y))
  | 0, b, hs, _, hd => by
    cases b with
    | nil => rw [dom_nil] at hd; exact absurd hd (by decide)
    | cons _ _ _ => simp at hs
  | m + 1, b, hs, hS, hd => by
    have hb0 : b ≠ nil := by intro e; subst e; rw [dom_nil] at hd; exact absurd hd (by decide)
    obtain ⟨s, c, e, rfl⟩ := snoc_view b hb0
    obtain ⟨hs1, hlast⟩ := (sub01_appT _ _).mp hS
    rw [dom_appT] at hd
    have hc : c = t1 := by
      rcases hlast.1 with rfl | rfl
      · exfalso
        by_cases he : e = nil
        · subst he; rw [dom_t1] at hd; exact absurd hd (by decide)
        · rw [dom_psi0_sub01 hlast.2.1 he] at hd; exact absurd hd (by decide)
      · rfl
    subst hc
    by_cases he : e = nil
    · subst he
      refine ⟨0, fun x => ⟨?_, fun Y => ⟨?_, fun hY => ?_⟩⟩⟩
      · rw [treeB_appT]
        show treeB x s ++ [[x, 1, 0]] = (treeB x s ++ [[x, 1, 0]]).dropLast ++ [[x + 0, 1, 0]]
        simp
      · rw [fs_appT, fs_tW, treeB_appT, treeB_appT]
        show treeB x s ++ treeB x Y = (treeB x s ++ [[x, 1, 0]]).dropLast ++ treeB (x + 0) Y
        simp
      · rw [fs_appT, fs_tW]; exact (sub01_appT _ _).mpr ⟨hs1, hY⟩
    · have hde : dom e = tW := by
        rcases dom_sub01 e hlast.2.1 he with h' | h' | h'
        · rw [dom_psi_of_one h'] at hd; exact absurd hd (by decide)
        · rw [dom_psi_of_tw h'] at hd; exact absurd hd (by decide)
        · exact h'
      have hfs : ∀ Y, fs (psi t1 e) Y = psi t1 (fs e Y) := fun Y =>
        fs_psi_of_lt (by rw [hde]; decide) (by rw [hde]; decide) (by rw [hde]; decide)
          (by rw [hde]; exact tW_lt_psi1 he)
      have hsz : size e ≤ m := by simp only [size_appT, size_cons, size_nil] at hs; omega
      obtain ⟨d, hH⟩ := hole m e hsz hlast.2.1 hde
      refine ⟨d + 1, fun x => ?_⟩
      obtain ⟨h1, h2⟩ := hH (x + 1)
      have et : treeB x (appT s (psi t1 e))
          = (treeB x s ++ [x, 1, 0] :: (treeB (x + 1) e).dropLast) ++ [[x + (d + 1), 1, 0]] := by
        rw [treeB_appT]
        show treeB x s ++ (([x, subY t1, 0] :: treeB (x + 1) e) ++ []) = _
        rw [List.append_nil, h1]
        simp only [List.cons_append, List.append_assoc]
        rw [show x + 1 + d = x + (d + 1) by omega]
        simp [subY]
      have edl : (treeB x (appT s (psi t1 e))).dropLast
          = treeB x s ++ [x, 1, 0] :: (treeB (x + 1) e).dropLast := by
        rw [et, List.dropLast_concat]
      refine ⟨by rw [edl]; exact et, fun Y => ⟨?_, fun hY => ?_⟩⟩
      · rw [fs_appT, hfs, treeB_appT, edl]
        show treeB x s ++ (([x, subY t1, 0] :: treeB (x + 1) (fs e Y)) ++ []) = _
        rw [List.append_nil, (h2 Y).1, show x + 1 + d = x + (d + 1) by omega]
        simp [subY]
      · rw [fs_appT, hfs]
        exact (sub01_appT _ _).mpr ⟨hs1, ⟨Or.inr rfl, (h2 Y).2 hY, trivial⟩⟩

/-- A step to a parent never leaves a block that starts at the least `x` of
everything after an earlier block of columns at least as far right. -/
theorem anc0_stays (S C : List (List Nat)) (z : Nat) (hS : ∀ col ∈ S, z ≤ col[0]!)
    (hC : (C[0]!)[0]! = z) : ∀ i j, S.length ≤ i → AncR (S ++ C) 0 j i → S.length ≤ j := by
  have step : ∀ i j, S.length ≤ i → ParR (S ++ C) 0 j i → S.length ≤ j := by
    intro i j hi hp
    by_contra hj
    have hj' : j < S.length := by omega
    obtain ⟨h1, h2, h3⟩ := hp
    have hxj : z ≤ ((S ++ C)[j]!)[0]! := by
      rw [getElem!_append_left _ _ hj']
      exact hS _ (by rw [getElem!_pos S j hj']; exact List.getElem_mem _)
    have hSC : ((S ++ C)[S.length]!)[0]! = z := by
      rw [show S.length = S.length + 0 by rfl, getElem!_append_right]; exact hC
    rcases Nat.lt_or_ge S.length i with hlt | hge
    · have := h3 S.length (by omega) hlt
      rw [hSC] at this; omega
    · have hi : i = S.length := by omega
      subst hi
      rw [hSC] at h2; omega
  intro i j hi h
  induction h with
  | single hr => exact step _ _ hi hr
  | tail _ hr ih => exact ih (step _ _ hi hr)

/-- **Along the hole, the row-0 ancestors of the leaf `Ω` are `ψ_1` nodes.** -/
theorem hole_anc : ∀ (m : Nat) (b : Term), size b ≤ m → Sub01 b → dom b = tW → ∀ x j,
    j + 1 < (treeB x b).length →
      AncR (treeB x b) 0 j ((treeB x b).length - 1) → ((treeB x b)[j]!)[1]! = 1
  | 0, b, hs, _, hd => by
    cases b with
    | nil => rw [dom_nil] at hd; exact absurd hd (by decide)
    | cons _ _ _ => simp at hs
  | m + 1, b, hs, hS, hd => by
    intro x j hj hA
    have hb0 : b ≠ nil := by intro e; subst e; rw [dom_nil] at hd; exact absurd hd (by decide)
    obtain ⟨s, c, e, rfl⟩ := snoc_view b hb0
    obtain ⟨hs1, hlast⟩ := (sub01_appT _ _).mp hS
    rw [dom_appT] at hd
    have hc : c = t1 := by
      rcases hlast.1 with rfl | rfl
      · exfalso
        by_cases he : e = nil
        · subst he; rw [dom_t1] at hd; exact absurd hd (by decide)
        · rw [dom_psi0_sub01 hlast.2.1 he] at hd; exact absurd hd (by decide)
      · rfl
    subst hc
    have eT : treeB x (appT s (psi t1 e)) = treeB x s ++ ([x, 1, 0] :: treeB (x + 1) e) := by
      rw [treeB_appT]
      show treeB x s ++ (([x, subY t1, 0] :: treeB (x + 1) e) ++ []) = _
      rw [List.append_nil]; rfl
    rw [eT] at hj hA ⊢
    have hlen : (treeB x s ++ [x, 1, 0] :: treeB (x + 1) e).length - 1
        = (treeB x s).length + (treeB (x + 1) e).length := by simp
    rw [hlen] at hA
    have hjS := anc0_stays (treeB x s) ([x, 1, 0] :: treeB (x + 1) e) x (treeB_ge s x) rfl _ j
      (by omega) hA
    obtain ⟨j', rfl⟩ : ∃ j', j = (treeB x s).length + j' := ⟨j - (treeB x s).length, by omega⟩
    rw [getElem!_append_right]
    have hA' := (ancR_shift (treeB x s) _ 0 j' _).mp hA
    cases j' with
    | zero => rfl
    | succ k =>
      have e1 : ∀ i, ([x, 1, 0] :: treeB (x + 1) e)[i + 1]! = (treeB (x + 1) e)[i]! := fun i => by
        rw [show i + 1 = [[x, 1, 0]].length + i from by simp; omega]
        exact getElem!_append_right [[x, 1, 0]] _ i
      rw [e1]
      by_cases he : e = nil
      · subst he; simp [treeB] at hj
      · have hde : dom e = tW := by
          rcases dom_sub01 e hlast.2.1 he with h' | h' | h'
          · rw [dom_psi_of_one h'] at hd; exact absurd hd (by decide)
          · rw [dom_psi_of_tw h'] at hd; exact absurd hd (by decide)
          · exact h'
        have hsz : size e ≤ m := by simp only [size_appT, size_cons, size_nil] at hs; omega
        have hA'' : AncR ([[x, 1, 0]] ++ treeB (x + 1) e) 0 ([[x, 1, 0]].length + k)
            ([[x, 1, 0]].length + ((treeB (x + 1) e).length - 1)) := by
          have hl : 0 < (treeB (x + 1) e).length := by simp at hj; omega
          rw [show [[x, 1, 0]].length + ((treeB (x + 1) e).length - 1)
            = (treeB (x + 1) e).length from by simp; omega]
          simpa [Nat.add_comm] using hA'
        have := (ancR_shift [[x, 1, 0]] _ 0 k _).mp hA''
        exact hole_anc m e hsz hlast.2.1 hde (x + 1) k (by simp at hj; omega) this

theorem m0L_three_one {l : List (List Nat)} (h1 : (parAtR l 1 (l.length - 1)).isSome = true)
    (h2 : parAtR l 2 (l.length - 1) = none) : m0L 3 l = 1 := by
  rw [m0L, show 3 - 1 = 1 + 1 from rfl, Nat.findGreatest_of_not (by rw [h2]; simp)]
  exact Nat.findGreatest_eq h1

/-- **A `ψ_0` node whose argument ends in a hole expands to a nest**: every
copy is the node and the tree before the hole, `d + 1` columns further right. -/
theorem expandRL_diag (M x d : Nat) (A T : List (List Nat))
    (hT : ∀ col ∈ T, col.length = 3 ∧ x + 1 ≤ col[0]!)
    (hanc : ∀ j, j < T.length → AncR (T ++ [[x + 1 + d, 1, 0]]) 0 j T.length → (T[j]!)[1]! = 1) :
    expandRL 3 M (A ++ ([x, 0, 0] :: T ++ [[x + 1 + d, 1, 0]]))
      = A ++ ((List.range (M + 1)).map
          (fun c => ([x, 0, 0] :: T).map (shiftC (c * (d + 1))))).flatten := by
  set B : List (List Nat) := [x, 0, 0] :: T ++ [[x + 1 + d, 1, 0]] with hB
  have hlen : B.length = T.length + 2 := by simp [hB]
  have hL : B.length - 1 = T.length + 1 := by omega
  have hB0 : B[0]! = [x, 0, 0] := rfl
  have hBlast : B[T.length + 1]! = [x + 1 + d, 1, 0] := by
    rw [hB, show T.length + 1 = ([x, 0, 0] :: T).length + 0 by simp, List.cons_append,
      ← List.cons_append, getElem!_append_right]; rfl
  have hBT : ∀ j, j < T.length → B[j + 1]! = T[j]! := by
    intro j hj
    rw [hB, show ([x, 0, 0] :: T ++ [[x + 1 + d, 1, 0]])
        = [[x, 0, 0]] ++ (T ++ [[x + 1 + d, 1, 0]]) from rfl,
      show j + 1 = [[x, 0, 0]].length + j by simp; omega, getElem!_append_right,
      getElem!_append_left _ _ hj]
  have hx : ∀ j, 0 < j → j < B.length → x < (B[j]!)[0]! := by
    intro j h1 h2
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    by_cases hk : k < T.length
    · rw [hBT k hk]
      have := (hT (T[k]!) (by rw [getElem!_pos T k hk]; exact List.getElem_mem _)).2; omega
    · have : k = T.length := by omega
      subst this; rw [hBlast]; simp; omega
  have hanc0 : ∀ j, 0 < j → j < B.length → AncR B 0 0 j :=
    anc0_of_min B (fun j h1 h2 => by rw [hB0]; exact hx j h1 h2)
  have hp1 : ParR B 1 0 (T.length + 1) := by
    refine ⟨by omega, hanc0 _ (by omega) (by omega), by rw [hB0, hBlast]; simp,
      fun j' hj1 hj2 hj3 => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, j' = k + 1 := ⟨j' - 1, by omega⟩
    have hk : k < T.length := by omega
    have hA : AncR (T ++ [[x + 1 + d, 1, 0]]) 0 k T.length := by
      have := (ancR_shift [[x, 0, 0]] (T ++ [[x + 1 + d, 1, 0]]) 0 k T.length).mp
        (by simpa [Nat.add_comm, hB] using hj3)
      exact this
    rw [hBlast, hBT k hk, hanc k hk hA]
    simp
  have hpar1 : parAtR B 1 (B.length - 1) = some 0 := by
    rw [hL]; exact (parAtR_eq_some _ _ _ _).mpr hp1
  have hpar2 : parAtR B 2 (B.length - 1) = none :=
    parAtR_none_of_zero (k := 1) (by rw [hL, hBlast]; rfl)
  have hm : m0L 3 B = 1 := m0L_three_one (by rw [hpar1]; rfl) hpar2
  have hb : badRootR 3 B = some 0 := by rw [badRootR_eq (by simp [hB]), hm, hpar1]
  have hmA : m0L 3 (A ++ B) = 1 := by
    have hl : (A ++ B).length - 1 = A.length + (B.length - 1) := by
      rw [List.length_append]; omega
    refine m0L_three_one ?_ ?_
    · rw [hl, parAtR_shift hpar1]; rfl
    · refine parAtR_none_of_zero (k := 1) ?_
      rw [hl, getElem!_append_right, hL, hBlast]; rfl
  rw [expandRL_append_local 3 M A B 0 hb (by rw [hm, hmA])]
  congr 1
  rw [expandRL_some 3 M B 0 hb, hm, List.take_zero, List.nil_append, Nat.sub_zero, hL]
  refine congrArg List.flatten (List.map_congr_left (fun c _ => ?_))
  have hR : [x, 0, 0] :: T = (List.range (T.length + 1)).map (fun s => B[s]!) := by
    conv_lhs => rw [← listEta ([x, 0, 0] :: T)]
    rw [List.length_cons]
    refine List.map_congr_left (fun s hs => ?_)
    have hs' := List.mem_range.mp hs
    rw [hB, List.cons_append, ← List.cons_append, getElem!_append_left _ _ (by simp; omega)]
  rw [hR, List.map_map]
  refine List.map_congr_left (fun s hs => ?_)
  have hs' := List.mem_range.mp hs
  have ha : ((0 == 0 + s) || ancAtR B 0 0 (0 + s)) = true := by
    rcases Nat.eq_zero_or_pos s with rfl | hpos
    · simp
    · rw [(ancAtR_iff _ _ _ _).mpr (hanc0 _ (by omega) (by omega))]; simp
  have hlen3 : (B[s]!).length = 3 := by
    rcases Nat.eq_zero_or_pos s with rfl | hpos
    · rw [hB0]; rfl
    · obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
      rw [hBT k (by omega)]
      exact (hT _ (by rw [getElem!_pos T k (by omega)]; exact List.getElem_mem _)).1
  simp only [Function.comp_apply, Nat.zero_add, List.range_succ, List.range_zero,
    List.nil_append, List.map_cons, List.map_nil, List.map_append] at ha ⊢
  rw [hB0, hBlast]
  simp only [ha, shiftC]
  simp
  omega

/-! ### One expansion inside a tree -/

theorem treeB_psi (x : Nat) (ν b : Term) : treeB x (psi ν b) = [x, subY ν, 0] :: treeB (x + 1) b := by
  show ([x, subY ν, 0] :: treeB (x + 1) b) ++ [] = _
  rw [List.append_nil]

theorem tower_succ (b : Term) (n : Nat) :
    Term.tower nil b (n + 1) = psi nil (fs b (Term.tower nil b n)) := rfl

theorem map_shiftC_zero : ∀ U : List (List Nat), (∀ col ∈ U, col.length = 3) →
    U.map (shiftC 0) = U
  | [], _ => rfl
  | col :: U, h => by
    rw [List.map_cons, map_shiftC_zero U (fun c hc => h c (List.mem_cons_of_mem _ hc))]
    congr 1
    have hl := h col (List.mem_cons_self ..)
    match col, hl with
    | [p, q, r], _ => simp [shiftC]

/-- The tree of the tower a hole runs through. -/
theorem treeB_tower (b : Term) (d : Nat) (T : Nat → List (List Nat))
    (hH : ∀ x Y, treeB x (fs b Y) = T x ++ treeB (x + d) Y)
    (hT : ∀ x, T (x + (d + 1)) = (T x).map (shiftC (d + 1)))
    (hl : ∀ x, ∀ col ∈ T x, col.length = 3) :
    ∀ (n x : Nat), treeB x (Term.tower nil b n)
      = ((List.range n).map (fun c => ([x, 0, 0] :: T (x + 1)).map (shiftC (c * (d + 1))))).flatten
        ++ [[x + n * (d + 1), 0, 0]]
  | 0, x => by simp [Term.tower, treeB, subY]
  | n + 1, x => by
    rw [tower_succ, treeB_psi, hH, treeB_tower b d T hH hT hl n (x + 1 + d), List.range_succ_eq_map,
      List.map_cons, List.flatten_cons, List.map_map]
    have hU : ([x, 0, 0] :: T (x + 1)).map (shiftC (0 * (d + 1))) = [x, 0, 0] :: T (x + 1) := by
      rw [Nat.zero_mul]
      refine map_shiftC_zero _ (fun col hc => ?_)
      rcases List.mem_cons.mp hc with rfl | hc
      · rfl
      · exact hl _ col hc
    have hshift : ∀ c, ([x + 1 + d, 0, 0] :: T (x + 1 + d + 1)).map (shiftC (c * (d + 1)))
        = ([x, 0, 0] :: T (x + 1)).map (shiftC ((c + 1) * (d + 1))) := by
      intro c
      rw [show x + 1 + d + 1 = (x + 1) + (d + 1) by omega, hT (x + 1), List.map_cons,
        List.map_cons, List.map_map]
      congr 1
      · simp only [shiftC]; simp; ring
      · refine List.map_congr_left (fun col _ => ?_)
        simp only [Function.comp_apply, shiftC_shiftC]
        congr 1; ring
    rw [hU]
    simp only [subY, hshift, Function.comp_def, Nat.succ_eq_add_one]
    rw [show x + 1 + d + n * (d + 1) = x + (n + 1) * (d + 1) by ring]
    simp only [List.cons_append, List.append_assoc]

theorem dom_psi1_sub01 {e : Term} (he : Sub01 e) (hne : e ≠ nil) :
    dom (psi t1 e) = tw ∨ dom (psi t1 e) = tW := by
  rcases dom_sub01 e he hne with h | h | h
  · exact Or.inl (dom_psi_of_one h)
  · exact Or.inl (dom_psi_of_tw h)
  · right
    rw [dom_psi_of_lt (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide)
      (by rw [h]; exact tW_lt_psi1 hne), h]

theorem fs_psi_hole {b : Term} (hd : dom b = tW) (n : Nat) :
    fs (psi nil b) (numeral n) = Term.tower nil b (n + 1) := by
  rw [fs_numeral (by rw [hd]; decide) (by rw [hd]; decide) (by rw [hd]; decide)
    (by rw [hd]; exact tW_not_lt_psi0 _) n, hd, show subOf tW = t1 from rfl, fs_t1_nil]
  rfl

theorem sub01_tower {b : Term} (hS : ∀ Y, Sub01 Y → Sub01 (fs b Y)) :
    ∀ n, Sub01 (Term.tower nil b n)
  | 0 => ⟨Or.inl rfl, trivial, trivial⟩
  | n + 1 => ⟨Or.inl rfl, hS _ (sub01_tower hS n), trivial⟩

/-- **One step of the fundamental sequence at a node is reachable from the
node**, whatever stands before it. -/
theorem nodeStep : ∀ (m : Nat) (ν b : Term), size b ≤ m → (ν = nil ∨ ν = t1) → Sub01 b →
    dom (psi ν b) = tw → ∀ (A : List (List Nat)) (x n : Nat), Reach3 (A ++ treeB x (psi ν b)) →
      Reach3 (A ++ treeB x (fs (psi ν b) (numeral n))) ∧ Sub01 (fs (psi ν b) (numeral n)) ∧
        (ν = nil → TopNil (fs (psi ν b) (numeral n)))
  | 0, ν, b, hs, hν, _, hd => by
    cases b with
    | nil =>
      rcases hν with rfl | rfl
      · rw [dom_t1] at hd; exact absurd hd (by decide)
      · rw [dom_tW] at hd; exact absurd hd (by decide)
    | cons _ _ _ => simp at hs
  | m + 1, ν, b, hs, hν, hS, hd => by
    intro A x n h
    have hb0 : b ≠ nil := by
      intro e; subst e
      rcases hν with rfl | rfl
      · rw [dom_t1] at hd; exact absurd hd (by decide)
      · rw [dom_tW] at hd; exact absurd hd (by decide)
    obtain ⟨s, c, e, rfl⟩ := snoc_view b hb0
    obtain ⟨hs1, hlast⟩ := (sub01_appT _ _).mp hS
    have hTnode : ∀ u, treeB x (psi ν (appT s u))
        = ([x, subY ν, 0] :: treeB (x + 1) s) ++ treeB (x + 1) u := by
      intro u; rw [treeB_psi, treeB_appT]; rfl
    rcases dom_sub01 (psi c e) hlast (fun h => Term.noConfusion h) with hde | hde | hde
    · -- the argument ends in `1`: the node is copied
      have hce : c = nil ∧ e = nil := by
        by_cases he : e = nil
        · subst he
          rcases hlast.1 with rfl | rfl
          · exact ⟨rfl, rfl⟩
          · rw [dom_tW] at hde; exact absurd hde (by decide)
        · rcases hlast.1 with rfl | rfl
          · rw [dom_psi0_sub01 hlast.2.1 he] at hde; exact absurd hde (by decide)
          · rcases dom_psi1_sub01 hlast.2.1 he with h' | h' <;> rw [h'] at hde <;>
              exact absurd hde (by decide)
      obtain ⟨rfl, rfl⟩ := hce
      have hdb : dom (appT s t1) = t1 := by rw [dom_appT, dom_t1]
      rw [fs_psi_of_one_numeral hdb, fs_appT, fs_t1_nil, appT_nil_right]
      refine ⟨?_, sub01_repeatPrin hν hs1 n, fun h => by subst h; exact topNil_repeatPrin s n⟩
      rw [treeB_repeatPrin]
      rw [hTnode] at h
      have h' : Reach3 (A ++ ([x, subY ν, 0] :: treeB (x + 1) s ++ [[x + 1, 0, 0]])) := by
        simpa [List.append_assoc] using h
      cases n with
      | zero =>
        simp only [List.replicate_zero, List.flatten_nil, List.append_nil]
        exact reach3_prefix _ A h'
      | succ N =>
        have hE := expandRL_copy_block N A [x, subY ν, 0] (treeB (x + 1) s) (x + 1)
          (reach3_wf h') (by simp) (treeB_ge s (x + 1))
        have := reach3_expand h' N
        rw [hE] at this
        exact this
    · -- the argument ends in a node of limit `ω`: expand inside it
      have hdb : dom (appT s (psi c e)) = tw := by rw [dom_appT]; exact hde
      rw [fs_psi_of_tw hdb, fs_appT]
      have he0 : e ≠ nil := by
        intro h0; subst h0
        rcases hlast.1 with rfl | rfl
        · rw [dom_t1] at hde; exact absurd hde (by decide)
        · rw [dom_tW] at hde; exact absurd hde (by decide)
      have hsz : size e ≤ m := by simp only [size_appT, size_cons, size_nil] at hs; omega
      rw [hTnode] at h
      obtain ⟨h1, h2, _⟩ := nodeStep m c e hsz hlast.1 hlast.2.1 hde _ (x + 1) n
        (by rw [← List.append_assoc] at h; exact h)
      refine ⟨?_, ⟨hν, (sub01_appT _ _).mpr ⟨hs1, h2⟩, trivial⟩, fun _ => ⟨by assumption, trivial⟩⟩
      rw [treeB_psi, treeB_appT]
      simpa [List.append_assoc] using h1
    · -- the argument ends in a hole: the node nests
      have hdb : dom (appT s (psi c e)) = tW := by rw [dom_appT]; exact hde
      have hνn : ν = nil := by
        rcases hν with rfl | rfl
        · rfl
        · exfalso
          rw [dom_psi_of_lt (by rw [hdb]; decide) (by rw [hdb]; decide) (by rw [hdb]; decide)
            (by rw [hdb]; exact tW_lt_psi1 hb0), hdb] at hd
          exact absurd hd (by decide)
      subst hνn
      set b := appT s (psi c e) with hbdef
      obtain ⟨d, hH⟩ := hole (size b) b le_rfl hS hdb
      rw [fs_psi_hole hdb]
      have hSt : ∀ Y, Sub01 Y → Sub01 (fs b Y) := fun Y hY => ((hH 0).2 Y).2 hY
      refine ⟨?_, sub01_tower hSt (n + 1), fun _ => ⟨rfl, trivial⟩⟩
      set T : Nat → List (List Nat) := fun z => (treeB z b).dropLast with hTdef
      have hHT : ∀ z Y, treeB z (fs b Y) = T z ++ treeB (z + d) Y := fun z Y => ((hH z).2 Y).1
      have hTs : ∀ z, T (z + (d + 1)) = (T z).map (shiftC (d + 1)) := by
        intro z
        simp only [hTdef]
        rw [← treeB_shift, List.map_dropLast]
      have hTl : ∀ z, ∀ col ∈ T z, col.length = 3 := fun z col hc =>
        treeB_len z b col (List.dropLast_subset _ hc)
      have hTg : ∀ col ∈ T (x + 1), col.length = 3 ∧ x + 1 ≤ col[0]! := fun col hc =>
        ⟨hTl _ col hc, treeB_ge b (x + 1) col (List.dropLast_subset _ hc)⟩
      have hsplit : treeB (x + 1) b = T (x + 1) ++ [[x + 1 + d, 1, 0]] := (hH (x + 1)).1
      have hanc : ∀ j, j < (T (x + 1)).length →
          AncR (T (x + 1) ++ [[x + 1 + d, 1, 0]]) 0 j (T (x + 1)).length →
            ((T (x + 1))[j]!)[1]! = 1 := by
        intro j hj hA
        have hlen : (treeB (x + 1) b).length = (T (x + 1)).length + 1 := by rw [hsplit]; simp
        have := hole_anc (size b) b le_rfl hS hdb (x + 1) j (by omega)
          (by rw [hlen, Nat.add_sub_cancel, hsplit]; exact hA)
        rwa [hsplit, getElem!_append_left _ _ hj] at this
      have h' : Reach3 (A ++ ([x, 0, 0] :: T (x + 1) ++ [[x + 1 + d, 1, 0]])) := by
        rw [treeB_psi, hsplit] at h; simpa using h
      have hE := expandRL_diag (n + 1) x d A (T (x + 1)) hTg hanc
      have := reach3_expand h' (n + 1)
      rw [hE, List.range_succ, List.map_append, List.flatten_append] at this
      rw [treeB_tower b d T hHT hTs hTl (n + 1) x]
      refine reach3_prefix ((T (x + 1)).map (shiftC ((n + 1) * (d + 1)))) _ ?_
      simpa [List.append_assoc, shiftC] using this

/-- **One step of the fundamental sequence of a countable tree is reachable
from the tree**, whatever stands before it, and stays in the fragment. -/
theorem treeStep : ∀ G : Term, CtS G → ∀ (A : List (List Nat)) (x n : Nat),
    Reach3 (A ++ treeB x G) → Reach3 (A ++ treeB x (fs G (idx G n))) ∧ CtS (fs G (idx G n))
  | nil, _, A, x, n, h => by rw [show fs nil (idx nil n) = nil by rw [fs]]; exact ⟨h, trivial⟩
  | cons a b (cons c d w), hC, A, x, n, h => by
    obtain ⟨rfl, hb, hu⟩ := hC
    have hfs : ∀ Y, fs (cons nil b (cons c d w)) Y = cons nil b (fs (cons c d w) Y) := by
      intro Y; rw [fs]
    have hidx : idx (cons nil b (cons c d w)) n = idx (cons c d w) n := rfl
    have hA : Reach3 ((A ++ ([x, 0, 0] :: treeB (x + 1) b)) ++ treeB x (cons c d w)) := by
      rw [List.append_assoc]; exact h
    obtain ⟨h1, h2⟩ := treeStep (cons c d w) hu _ x n hA
    rw [hidx, hfs]
    refine ⟨?_, ⟨rfl, hb, h2⟩⟩
    show Reach3 (A ++ (([x, subY nil, 0] :: treeB (x + 1) b) ++ treeB x _))
    rw [← List.append_assoc]; exact h1
  | cons a b nil, hC, A, x, n, h => by
    obtain ⟨rfl, hb, _⟩ := hC
    by_cases hb0 : b = nil
    · subst hb0
      have hidx : idx (psi nil nil) n = nil := by rw [idx, if_pos dom_t1]
      rw [hidx, fs_t1_nil]
      rw [show treeB x nil = [] from rfl, List.append_nil]
      exact ⟨reach3_prefix [[x, 0, 0]] A (h : Reach3 (A ++ [[x, 0, 0]])), trivial⟩
    · have hd := dom_psi0_sub01 hb hb0
      rw [idx, hd, if_neg (by decide)]
      obtain ⟨h1, h2, h3⟩ := nodeStep (size b) nil b le_rfl (Or.inl rfl) hb hd A x n h
      exact ⟨h1, ctS_of _ (h3 rfl) h2⟩

/-! ### Everything below a tree is reachable from it -/

theorem ctS_lt_tW {G : Term} (h : CtS G) : G < tW := by
  cases G with
  | nil => exact nil_lt_cons _ _ _
  | cons a b t =>
    obtain ⟨rfl, _, _⟩ := h
    exact cons_lt_psi_iff.mpr (psi_lt_psi_iff.mpr (Or.inl (nil_lt_cons _ _ _)))

/-- **Every standard term below a countable tree of the fragment is reachable
from it**, behind the same prefix. -/
theorem treeReach : ∀ G : Term, OT G → CtS G → ∀ (A : List (List Nat)) (x : Nat),
    Reach3 (A ++ treeB x G) → ∀ t : Term, OT t → t ≤ G → Reach3 (A ++ treeB x t) := by
  intro G
  induction G using WellFounded.induction OTLt_wf with
  | _ G ih =>
    intro hOT hC A x hR t ht hle
    rcases le_iff_lt_or_eq.mp hle with h | h
    · have hGne : G ≠ nil := fun e => by subst e; exact not_lt_nil _ h
      have hGc : G < tW := ctS_lt_tW hC
      obtain ⟨n, hn⟩ := exists_le_fs_idx hOT hGc hGne ht h
      obtain ⟨h1, h2⟩ := treeStep G hC A x n hR
      have hOT' := (step_ok hOT hGc n).1
      exact ih _ ⟨hOT', hOT, step_lt hOT hGc hGne n⟩ hOT' h2 A x h1 t ht hn
    · subst h; exact hR

/-- A tree that everything in the fragment below it is reachable from. -/
def TopOK (G : Term) : Prop := OT G ∧ CtS G

theorem treeReach_top {G : Term} (hG : TopOK G) (A : List (List Nat)) (x : Nat)
    (hR : Reach3 (A ++ treeB x G)) (t : Term) (ht : OT t) (_hC : CtS t) (hle : t ≤ G) :
    Reach3 (A ++ treeB x t) :=
  treeReach G hG.1 hG.2 A x hR t ht hle

/-! ### The top: `ψ_0(Ω_2)` -/

/-- `ψ_0(Ω_2)`, above every countable term of the fragment. -/
abbrev gTop : Term := psi nil (psi t2 nil)

theorem OT_gTop : OT gTop := by decide

theorem ctS_lt_gTop {t : Term} (h : CtS t) : t < gTop := by
  cases t with
  | nil => exact nil_lt_cons _ _ _
  | cons a b u =>
    obtain ⟨rfl, hb, _⟩ := h
    refine cons_lt_psi_iff.mpr (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, ?_⟩))
    cases b with
    | nil => exact nil_lt_cons _ _ _
    | cons a' b' u' =>
      refine cons_lt_psi_iff.mpr (psi_lt_psi_iff.mpr (Or.inl ?_))
      rcases hb.1 with rfl | rfl
      · exact nil_lt_cons _ _ _
      · decide

theorem fs_t2_nil : fs t2 nil = t1 := by
  have : fs (cons nil nil t1) nil = cons nil nil (fs t1 nil) := by rw [fs]
  rw [show t2 = cons nil nil t1 from rfl, this, fs_t1_nil]

/-- `ψ_1` applied `n + 1` times to `0`. -/
theorem treeB_tower1 (x : Nat) : ∀ n : Nat,
    treeB x (Term.tower t1 (psi t2 nil) n) = (List.range (n + 1)).map (fun k => [x + k, 1, 0])
  | 0 => rfl
  | n + 1 => by
    have e : Term.tower t1 (psi t2 nil) (n + 1) = psi t1 (Term.tower t1 (psi t2 nil) n) := by
      show psi t1 (fs (psi t2 nil) _) = _
      rw [fs_psi_nil_of_one (by decide)]
    rw [e, treeB_psi, treeB_tower1 (x + 1) n, map_range_succ' (fun k => [x + k, 1, 0]) (n + 1)]
    refine congrArg₂ List.cons rfl (List.map_congr_left (fun k _ => ?_))
    show [x + 1 + k, 1, 0] = [x + (k + 1), 1, 0]
    congr 1; omega

theorem sub01_tower1 : ∀ n : Nat, Sub01 (Term.tower t1 (psi t2 nil) n)
  | 0 => ⟨Or.inr rfl, trivial, trivial⟩
  | n + 1 => by
    show Sub01 (psi t1 (fs (psi t2 nil) _))
    rw [fs_psi_nil_of_one (by decide)]
    exact ⟨Or.inr rfl, sub01_tower1 n, trivial⟩

theorem fs_gTop (n : Nat) :
    fs gTop (idx gTop n) = psi nil (Term.tower t1 (psi t2 nil) n) := by
  have d2 : dom (psi t2 nil) = psi t2 nil := dom_psi_nil_of_one (by decide)
  have d0 : dom gTop = tw :=
    dom_psi_of_case4 (by rw [d2]; decide) (by rw [d2]; decide) (by rw [d2]; decide)
      (by rw [d2]; decide)
  rw [idx, d0, if_neg (by decide),
    fs_numeral (by rw [d2]; decide) (by rw [d2]; decide) (by rw [d2]; decide)
      (by rw [d2]; decide) n, d2, show subOf (psi t2 nil) = t2 from rfl, fs_t2_nil,
    fs_psi_nil_of_one (by decide)]

/-- `(0,0,0)(1,1,1)(2,1,1)(3,0,0)(4,1,0)(5,2,0)`, the trio matrix of
`ψ_0(Ω_{ψ_0(Ω_2)})`, is reachable. -/
theorem reach3_top6 : Reach3 [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,0],[5,2,0]] := by
  have g2 : Reach3 [[0,0,0],[1,1,1],[2,2,2]] := reach3_gen 2
  have s1 : Reach3 [[0,0,0],[1,1,1],[2,2,1]] := by
    have := reach3_expand g2 1
    rwa [show expandRL 3 1 [[0,0,0],[1,1,1],[2,2,2]] = [[0,0,0],[1,1,1],[2,2,1]] by decide] at this
  have s2 : Reach3 [[0,0,0],[1,1,1],[2,2,0]] := by
    have := reach3_expand s1 1
    rw [show expandRL 3 1 [[0,0,0],[1,1,1],[2,2,1]] = [[0,0,0],[1,1,1],[2,2,0],[3,3,1]]
      by decide] at this
    exact reach3_prefix [[3,3,1]] _ this
  have s3 : Reach3 [[0,0,0],[1,1,1],[2,1,1],[3,1,1]] := by
    have := reach3_expand s2 2
    rwa [show expandRL 3 2 [[0,0,0],[1,1,1],[2,2,0]] = [[0,0,0],[1,1,1],[2,1,1],[3,1,1]]
      by decide] at this
  have s4 : Reach3 [[0,0,0],[1,1,1],[2,1,1],[3,1,0]] := by
    have := reach3_expand s3 1
    rw [show expandRL 3 1 [[0,0,0],[1,1,1],[2,1,1],[3,1,1]]
      = [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[4,2,1],[5,2,1]] by decide] at this
    exact reach3_prefix [[4,2,1],[5,2,1]] _ this
  have s5 : Reach3 [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,1]] := by
    have := reach3_expand s4 1
    rw [show expandRL 3 1 [[0,0,0],[1,1,1],[2,1,1],[3,1,0]]
      = [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,1],[5,1,1]] by decide] at this
    exact reach3_prefix [[5,1,1]] _ this
  have := reach3_expand s5 2
  rwa [show expandRL 3 2 [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,1]]
    = [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,0],[5,2,0]] by decide] at this

/-- **`(x,0,0)(x+1,1,0)(x+2,2,0)` expands to a chain of `ψ_1`s.** -/
theorem expandRL_top (N x : Nat) (A : List (List Nat)) :
    expandRL 3 N (A ++ [[x, 0, 0], [x + 1, 1, 0], [x + 2, 2, 0]])
      = A ++ ([x, 0, 0] :: (List.range (N + 1)).map (fun c => [x + 1 + c, 1, 0])) := by
  set B : List (List Nat) := [[x + 1, 1, 0], [x + 2, 2, 0]] with hB
  have h0 : ParR B 0 0 1 := ⟨by omega, by simp [hB], fun j' h1 h2 => by omega⟩
  have h1 : ParR B 1 0 1 := ⟨by omega, .single h0, by simp [hB], fun j' h1 h2 => by omega⟩
  have hp1 : parAtR B 1 (B.length - 1) = some 0 := (parAtR_eq_some _ _ _ _).mpr h1
  have hp2 : parAtR B 2 (B.length - 1) = none := parAtR_none_of_zero (k := 1) (by simp [hB])
  have hm : m0L 3 B = 1 := m0L_three_one (by rw [hp1]; rfl) hp2
  have hb : badRootR 3 B = some 0 := by rw [badRootR_eq (by simp [hB]), hm, hp1]
  set A' := A ++ [[x, 0, 0]] with hA'
  have hmA : m0L 3 (A' ++ B) = 1 := by
    have hl : (A' ++ B).length - 1 = A'.length + (B.length - 1) := by
      rw [List.length_append]; simp [hB]
    refine m0L_three_one ?_ ?_
    · rw [hl, parAtR_shift hp1]; rfl
    · refine parAtR_none_of_zero (k := 1) ?_
      rw [hl, getElem!_append_right]; simp [hB]
  have e : A ++ [[x, 0, 0], [x + 1, 1, 0], [x + 2, 2, 0]] = A' ++ B := by simp [hA', hB]
  have e2 : A ++ ([x, 0, 0] :: (List.range (N + 1)).map (fun c => [x + 1 + c, 1, 0]))
      = A' ++ ((List.range (N + 1)).map (fun c => [[x + 1 + c, 1, 0]])).flatten := by
    rw [flatten_map_single]; simp [hA']
  rw [e, e2, expandRL_append_local 3 N A' B 0 hb (by rw [hm, hmA]), expandRL_some 3 N B 0 hb, hm]
  congr 1
  simp only [List.take_zero, List.nil_append]
  refine congrArg List.flatten (List.map_congr_left (fun c _ => ?_))
  simp [hB, List.range_succ]

/-- **Every tree of the fragment under the first digit is reachable.** -/
theorem first_unit (γ : Term) (hOT : OT γ) (hC : CtS γ) :
    Reach3 ([[0, 0, 0], [1, 1, 1], [2, 1, 1]] ++ treeB 3 γ) := by
  have hGc : gTop < tW := by decide
  obtain ⟨n, hn⟩ := exists_le_fs_idx OT_gTop hGc (by decide) hOT (ctS_lt_gTop hC)
  have hOT' := (step_ok OT_gTop hGc n).1
  rw [fs_gTop] at hn hOT'
  refine treeReach _ hOT' ⟨rfl, sub01_tower1 n, trivial⟩ _ 3 ?_ γ hOT hn
  have := reach3_expand reach3_top6 n
  rw [show [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,0],[5,2,0]]
    = [[0,0,0],[1,1,1],[2,1,1]] ++ [[3,0,0],[3 + 1,1,0],[3 + 2,2,0]] from rfl,
    expandRL_top] at this
  rw [treeB_psi, treeB_tower1]
  exact this

/-! ### Every `Ω` has a `ψ_0` ancestor -/

theorem parR0_append_left (l m : List (List Nat)) {j' j : Nat} (hj : j < l.length) :
    ParR (l ++ m) 0 j' j ↔ ParR l 0 j' j := by
  have e : ∀ k, k < l.length → (l ++ m)[k]! = l[k]! := fun k hk => getElem!_append_left l m hk
  simp only [ParR]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, fun k hk1 hk2 => ?_⟩
    · rwa [e j' (by omega), e j hj] at h2
    · have := h3 k hk1 hk2
      rwa [e k (by omega), e j hj] at this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, fun k hk1 hk2 => ?_⟩
    · rwa [e j' (by omega), e j hj]
    · rw [e k (by omega), e j hj]
      exact h3 k hk1 hk2

theorem ancR0_append_left (l m : List (List Nat)) (j' j : Nat) (hj : j < l.length) :
    AncR (l ++ m) 0 j' j ↔ AncR l 0 j' j := by
  constructor
  · intro h
    induction h with
    | single hr => exact .single ((parR0_append_left l m hj).mp hr)
    | tail h1 hr ih =>
      have := ParR_lt hr
      exact .tail (ih (by omega)) ((parR0_append_left l m hj).mp hr)
  · intro h
    induction h with
    | single hr => exact .single ((parR0_append_left l m hj).mpr hr)
    | tail h1 hr ih =>
      have := ParR_lt hr
      exact .tail (ih (by omega)) ((parR0_append_left l m hj).mpr hr)

/-- Every column with `y = 1` and `z = 0` has a row-0 ancestor with `y = 0`. -/
def AncP (l : List (List Nat)) : Prop :=
  ∀ j, j < l.length → (l[j]!)[1]! = 1 → (l[j]!)[2]! = 0 →
    ∃ j', j' < j ∧ AncR l 0 j' j ∧ (l[j']!)[1]! = 0

theorem ancP_append {l m : List (List Nat)} (hl : AncP l) (hm : AncP m) : AncP (l ++ m) := by
  intro j hj h1 h2
  by_cases hjl : j < l.length
  · rw [getElem!_append_left _ _ hjl] at h1 h2
    obtain ⟨j', hj', hp, hy⟩ := hl j hjl h1 h2
    exact ⟨j', hj', (ancR0_append_left l m j' j hjl).mpr hp,
      by rw [getElem!_append_left _ _ (by omega)]; exact hy⟩
  · obtain ⟨i, rfl⟩ : ∃ i, j = l.length + i := ⟨j - l.length, by omega⟩
    rw [getElem!_append_right] at h1 h2
    obtain ⟨i', hi', hp, hy⟩ := hm i (by rw [List.length_append] at hj; omega) h1 h2
    exact ⟨l.length + i', by omega, (ancR_shift l m 0 i' i).mpr hp,
      by rw [getElem!_append_right]; exact hy⟩

theorem ancP_node {x : Nat} {T : List (List Nat)} (hge : ∀ col ∈ T, x + 1 ≤ col[0]!) :
    AncP ([x, 0, 0] :: T) := by
  intro j hj h1 _
  cases j with
  | zero => simp at h1
  | succ i =>
    refine ⟨0, by omega, anc0_of_min _ (fun k hk1 hk2 => ?_) _ (by omega) hj, rfl⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have e : ([x, 0, 0] :: T)[k' + 1]! = T[k']! := by
      rw [show k' + 1 = [[x, 0, 0]].length + k' from by simp; omega]
      exact getElem!_append_right [[x, 0, 0]] T k'
    rw [e]
    have := hge (T[k']!) (by rw [getElem!_pos T k' (by simp at hk2; omega)]; exact List.getElem_mem _)
    have h0 : (([x, 0, 0] :: T)[0]!)[0]! = x := rfl
    rw [h0]; omega

theorem ancP_treeB : ∀ (t : Term) (x : Nat), CtS t → AncP (treeB x t)
  | nil, _, _ => by intro j hj; simp [treeB] at hj
  | cons a b u, x, h => by
    obtain ⟨rfl, _, hu⟩ := h
    rw [treeB]
    exact ancP_append (ancP_node (treeB_ge b (x + 1))) (ancP_treeB u x hu)

theorem ancP_digit (d : List Nat) (hd : d[2]! = 1) : AncP [d] := by
  intro j hj _ h2
  cases j with
  | zero =>
    have h2' : d[2]! = 0 := h2
    rw [hd] at h2'; exact absurd h2' (by decide)
  | succ i => simp at hj

/-! ### An add unit with trees that ends in a digit -/

/-- A column after the root: a digit, or a tree column `(x, v, 0)` with
`v ≤ 1` right of the digits. -/
def TailColE (a y : Nat) (col : List Nat) : Prop :=
  col = [a + 2, y + 1, 1] ∨ ∃ x v, a + 3 ≤ x ∧ v ≤ 1 ∧ col = [x, v, 0]

def BodyColE (a y : Nat) (col : List Nat) : Prop := col = [a + 1, y + 1, 1] ∨ TailColE a y col

/-- Copy `c` of a column of the bad part: `x` goes up by `2c`, and `y` by `c`
for the root and the digits only. -/
def ascColE (a c : Nat) (col : List Nat) : List Nat :=
  [col[0]! + c * 2, if col[0]! < a + 3 then col[1]! + c * 1 else col[1]!, col[2]!]

theorem bodyColE_x {a y : Nat} {col : List Nat} (h : BodyColE a y col) : a < col[0]! := by
  rcases h with rfl | rfl | ⟨x, v, hx, _, rfl⟩
  · simp
  · simp
  · simp; omega

theorem bodyColE_y {a y : Nat} {col : List Nat} (h : BodyColE a y col) (hx : col[0]! < a + 3) :
    col[1]! = y + 1 := by
  rcases h with rfl | rfl | ⟨x, v, hx', _, rfl⟩
  · simp
  · simp
  · simp at hx; omega

theorem bodyColE_tree {a y : Nat} {col : List Nat} (h : BodyColE a y col) (hx : a + 3 ≤ col[0]!) :
    col[1]! ≤ 1 ∧ col[2]! = 0 := by
  rcases h with rfl | rfl | ⟨x, v, _, hv, rfl⟩
  · simp at hx
  · simp at hx
  · simp; exact hv

/-- **An add unit with trees that ends in a digit expands to copies of itself
without the digit**, each lifted by `(2, 1)` in its root and digits and by
`(2, 0)` in its trees. -/
theorem expandRL_digit_unitE (N a y : Nat) (A D : List (List Nat))
    (hD : ∀ col ∈ D, TailColE a y col) (hOm : AncP D) :
    expandRL 3 N (A ++ (([a, y, 0] :: [a + 1, y + 1, 1] :: D) ++ [[a + 2, y + 1, 1]]))
      = A ++ ((List.range (N + 1)).map (fun c =>
          [a + c * 2, y + c * 1, 0] :: ([a + 1, y + 1, 1] :: D).map (ascColE a c))).flatten := by
  set P0 : List (List Nat) := [a, y, 0] :: [a + 1, y + 1, 1] :: D with hP0
  set B : List (List Nat) := P0 ++ [[a + 2, y + 1, 1]] with hB
  have hlen : B.length = D.length + 3 := by simp [hB, hP0]
  have hlast : B[B.length - 1]! = [a + 2, y + 1, 1] := by
    rw [show B.length - 1 = P0.length + 0 by simp [hB, hP0], hB, getElem!_append_right]; rfl
  have hB0 : B[0]! = [a, y, 0] := by
    rw [hB, getElem!_append_left _ _ (by simp [hP0])]; rfl
  have hcol : ∀ j, 1 ≤ j → j < B.length → BodyColE a y (B[j]!) := by
    intro j h1 h2
    have hm := getElem!_mem_drop B h1 h2
    generalize B[j]! = col at hm ⊢
    rw [hB, hP0] at hm
    simp only [List.cons_append, List.drop_succ_cons, List.drop_zero, List.mem_cons,
      List.mem_append] at hm
    rcases hm with h | h | h
    · exact Or.inl h
    · exact Or.inr (hD _ h)
    · simp at h; exact Or.inr (Or.inl h)
  have hx0 : (B[0]!)[0]! = a := by rw [hB0]; rfl
  have hanc0 : ∀ j, 0 < j → j < B.length → AncR B 0 0 j :=
    anc0_of_min B (fun j h1 h2 => by rw [hx0]; exact bodyColE_x (hcol j h1 h2))
  have hp1 : ∀ j, 0 < j → j < B.length → (B[j]!)[0]! < a + 3 → ParR B 1 0 j := by
    intro j h1 h2 h3
    refine ⟨h1, hanc0 j h1 h2, ?_, fun j' hj1 hj2 hj3 => ?_⟩
    · rw [bodyColE_y (hcol j h1 h2) h3, hB0]; simp
    · have hx := anc0_lt hj3
      rw [bodyColE_y (hcol j h1 h2) h3,
        bodyColE_y (hcol j' hj1 (by omega)) (by omega)]
  -- the tree columns: `B = [anchor, root] ++ (D ++ [digit])`
  have hBsplit : B = [[a, y, 0], [a + 1, y + 1, 1]] ++ (D ++ [[a + 2, y + 1, 1]]) := by
    simp [hB, hP0]
  have hBD : ∀ i, i < D.length → B[2 + i]! = D[i]! := by
    intro i hi
    rw [hBsplit, show 2 + i = [[a, y, 0], [a + 1, y + 1, 1]].length + i from rfl,
      getElem!_append_right, getElem!_append_left _ _ hi]
  have hnot1 : ∀ j, 0 < j → j < B.length → a + 3 ≤ (B[j]!)[0]! → ¬ AncR B 1 0 j := by
    intro j h1 h2 h3
    obtain ⟨hv, hz⟩ := bodyColE_tree (hcol j h1 h2) h3
    rcases Nat.lt_or_ge ((B[j]!)[1]!) 1 with hv0 | hv1
    · exact not_ancR_of_zero (k := 0) (by rw [Nat.zero_add]; omega)
    · have hv1' : (B[j]!)[1]! = 1 := by omega
      -- `j` is inside `D`
      have hj2 : 2 ≤ j := by
        by_contra hc
        have : j = 1 := by omega
        subst this
        simp [hBsplit] at h3
      obtain ⟨i, rfl⟩ : ∃ i, j = 2 + i := ⟨j - 2, by omega⟩
      have hi : i < D.length := by
        by_contra hc
        have : i = D.length := by omega
        subst this
        rw [hBsplit, show 2 + D.length = [[a, y, 0], [a + 1, y + 1, 1]].length + (D.length + 0)
          from by simp, getElem!_append_right, getElem!_append_right] at h3
        simp at h3
      rw [hBD i hi] at hv1' hz
      obtain ⟨i', hi', hp, hy⟩ := hOm i hi hv1' hz
      have hpB : AncR B 0 (2 + i') (2 + i) := by
        rw [hBsplit]
        exact (ancR_shift _ _ 0 i' i).mpr ((ancR0_append_left D _ i' i hi).mpr hp)
      have hyB : (B[2 + i']!)[1]! = 0 := by rw [hBD i' (by omega)]; exact hy
      intro hA
      obtain ⟨p, hp1, hp2⟩ := Relation.TransGen.tail'_iff.mp hA
      obtain ⟨hpl, _, hpy, hpbetween⟩ := hp2
      rw [hBD i hi, hv1'] at hpy
      rw [hBD i hi, hv1'] at hpbetween
      simp only [Nat.zero_add] at hpy
      rcases Nat.lt_or_ge p (2 + i') with hlt | hge
      · have := hpbetween (2 + i') hlt (by omega) hpB
        rw [hyB] at this; omega
      · rcases Relation.reflTransGen_iff_eq_or_transGen.mp hp1 with he | ht
        · omega
        · exact not_ancR_of_zero (k := 0) (by rw [Nat.zero_add]; omega) ht
  have hL : B.length - 1 = D.length + 2 := by omega
  have hlastx : (B[B.length - 1]!)[0]! < a + 3 := by rw [hlast]; simp
  have hp1l : ParR B 1 0 (B.length - 1) := hp1 _ (by omega) (by omega) hlastx
  have hp2 : ParR B 2 0 (B.length - 1) := by
    refine ⟨by omega, .single hp1l, by rw [hB0, hlast]; simp, fun j' hj1 hj2 hj3 => ?_⟩
    exfalso
    obtain ⟨c, hc1, hc2⟩ := Relation.TransGen.tail'_iff.mp hj3
    have hc0 := parR_unique hc2 hp1l
    subst hc0
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hc1 with he | ht
    · omega
    · have := tg_lt (fun _ _ h => ParR_lt h) ht; omega
  have hpar2 : parAtR B 2 (B.length - 1) = some 0 := (parAtR_eq_some _ _ _ _).mpr hp2
  have hm : m0L 3 B = 2 := m0L_three_two (by rw [hpar2]; rfl)
  have hb : badRootR 3 B = some 0 := by
    rw [badRootR_eq (by simp [hB]), hm]; exact hpar2
  have hlast' : B[D.length + 2]! = [a + 2, y + 1, 1] := by rw [← hL]; exact hlast
  rw [expandRL_append_local 3 N A B 0 hb (by rw [hm, m0L_append_two hpar2])]
  congr 1
  rw [expandRL_some 3 N B 0 hb, hm, List.take_zero, List.nil_append, Nat.sub_zero, hL]
  refine congrArg List.flatten (List.map_congr_left (fun c _ => ?_))
  rw [show List.range (D.length + 2) = 0 :: (List.range (D.length + 1)).map Nat.succ from
    List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · rw [hlast']; simp [hB0, List.range_succ]
  · have hR : [a + 1, y + 1, 1] :: D
        = (List.range (D.length + 1)).map (fun s => B[s + 1]!) := by
      conv_lhs => rw [← listEta ([a + 1, y + 1, 1] :: D)]
      rw [List.length_cons]
      refine List.map_congr_left (fun s hs => ?_)
      have hs' := List.mem_range.mp hs
      rw [hB, getElem!_append_left _ _ (by simp [hP0]; omega)]
      rfl
    rw [hR, List.map_map]
    refine List.map_congr_left (fun s hs => ?_)
    have hs' := List.mem_range.mp hs
    have hbc := hcol (s + 1) (by omega) (by omega)
    have ha0 : ancAtR B 0 0 (s + 1) = true := by
      rw [ancAtR_iff]; exact hanc0 _ (by omega) (by omega)
    have ha1 : ancAtR B 1 0 (s + 1) = decide ((B[s + 1]!)[0]! < a + 3) := by
      by_cases hx : (B[s + 1]!)[0]! < a + 3
      · rw [decide_eq_true hx, ancAtR_iff]
        exact .single (hp1 _ (by omega) (by omega) hx)
      · rw [decide_eq_false hx, Bool.eq_false_iff, ne_eq, ancAtR_iff]
        exact hnot1 _ (by omega) (by omega) (by omega)
    have hbeq : (0 == s + 1) = false := by simp
    simp only [Function.comp_apply, Nat.zero_add]
    simp only [List.range_succ, List.range_zero, List.nil_append,
      List.map_cons, List.map_nil, List.cons_append, hbeq, ha0, ha1,
      Bool.false_or, hB0, hlast']
    generalize B[s + 1]! = col at hbc
    rcases hbc with rfl | rfl | ⟨x, v, hx, hv, rfl⟩
    · simp [ascColE]
    · simp [ascColE]
    · have hnx : ¬ x < a + 3 := by omega
      simp [ascColE, hnx]

/-! ### The layout of units with trees -/

/-- Multiply units with the trees `L`. -/
def mulL (x0 y : Nat) : List Term → List (List Nat)
  | [] => []
  | γ :: L => ([x0 + 1, y, 1] :: treeB (x0 + 2) γ) ++ mulL x0 y L

/-- An add unit whose multiply units have the trees `L`. -/
def unitM (rp1 i : Nat) (L : List Term) : List (List Nat) :=
  [rp1, i - 1, 0] :: [rp1 + 1, i, 1] :: mulL (rp1 + 1) i L

/-- A row of units: `none` is a unit `1`, `some L` an add unit with the trees
`L`; laid out as `addUnits` of `Trio.lean`. -/
def unitsM (rp1 lastX : Nat) (pz : Bool) (i : Nat) : List (Option (List Term)) → List (List Nat)
  | [] => []
  | none :: S =>
      if pz then [lastX + 1, i, 0] :: unitsM rp1 (lastX + 1) true (i + 1) S
      else [rp1, i - 1, 0] :: [rp1 + 1, i, 0] :: unitsM rp1 (rp1 + 1) true (i + 1) S
  | some L :: S => unitM rp1 i L ++ unitsM (rp1 + 2) (rp1 + 1) false (i + 1) S

theorem mulL_append (x0 y : Nat) : ∀ L L' : List Term,
    mulL x0 y (L ++ L') = mulL x0 y L ++ mulL x0 y L'
  | [], _ => rfl
  | γ :: L, L' => by rw [List.cons_append, mulL, mulL, mulL_append x0 y L L', List.append_assoc]

theorem mulL_single (x0 y : Nat) (γ : Term) :
    mulL x0 y [γ] = [x0 + 1, y, 1] :: treeB (x0 + 2) γ := by
  rw [mulL, mulL, List.append_nil]

theorem mulL_replicate (x0 y : Nat) (δ : Term) : ∀ n : Nat,
    mulL x0 y (List.replicate n δ) = (List.replicate n ([x0 + 1, y, 1] :: treeB (x0 + 2) δ)).flatten
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, mulL, mulL_replicate x0 y δ n, List.replicate_succ, List.flatten_cons]

theorem unitM_append (rp1 i : Nat) (L L' : List Term) :
    unitM rp1 i (L ++ L') = unitM rp1 i L ++ mulL (rp1 + 1) i L' := by
  rw [unitM, unitM, mulL_append]; rfl

theorem unitsM_lastX (rp1 l1 l2 i : Nat) (S : List (Option (List Term))) :
    unitsM rp1 l1 false i S = unitsM rp1 l2 false i S := by
  cases S with
  | nil => rfl
  | cons u S =>
    cases u with
    | none => simp [unitsM]
    | some L => simp [unitsM]

theorem unitsM_replicate_some (L : List Term) : ∀ (n rp1 lastX : Nat) (pz : Bool) (i : Nat),
    unitsM rp1 lastX pz i (List.replicate n (some L))
      = ((List.range n).map (fun c => unitM (rp1 + c * 2) (i + c) L)).flatten
  | 0, _, _, _, _ => rfl
  | n + 1, rp1, lastX, pz, i => by
    rw [List.replicate_succ, unitsM, unitsM_replicate_some L n, List.range_succ_eq_map,
      List.map_cons, List.flatten_cons, List.map_map]
    congr 2
    refine List.map_congr_left (fun c _ => ?_)
    simp only [Function.comp_apply, Nat.succ_eq_add_one]
    rw [show rp1 + (c + 1) * 2 = rp1 + 2 + c * 2 by ring, show i + (c + 1) = i + 1 + c by omega]

theorem unitsM_append_some (L : List Term) (S : List (Option (List Term))) :
    ∀ (k rp1 lastX : Nat) (pz : Bool) (i : Nat),
    unitsM rp1 lastX pz i (List.replicate (k + 1) (some L) ++ S)
      = unitsM rp1 lastX pz i (List.replicate (k + 1) (some L))
        ++ unitsM (rp1 + (k + 1) * 2) 0 false (i + (k + 1)) S
  | 0, rp1, lastX, pz, i => by
    show unitM rp1 i L ++ unitsM (rp1 + 2) (rp1 + 1) false (i + 1) S
      = (unitM rp1 i L ++ unitsM (rp1 + 2) (rp1 + 1) false (i + 1) [])
        ++ unitsM (rp1 + (0 + 1) * 2) 0 false (i + (0 + 1)) S
    rw [unitsM_lastX _ (rp1 + 1) 0, show unitsM (rp1 + 2) (rp1 + 1) false (i + 1) [] = [] from rfl,
      List.append_nil, show rp1 + (0 + 1) * 2 = rp1 + 2 by omega]
  | k + 1, rp1, lastX, pz, i => by
    rw [List.replicate_succ, List.cons_append, unitsM, unitsM,
      unitsM_append_some L S k (rp1 + 2) (rp1 + 1) false (i + 1), List.append_assoc]
    rw [show rp1 + 2 + (k + 1) * 2 = rp1 + (k + 1 + 1) * 2 by ring,
      show i + 1 + (k + 1) = i + (k + 1 + 1) by omega]

theorem unitsM_chain : ∀ (n rp1 lastX i : Nat),
    unitsM rp1 lastX true i (List.replicate n none)
      = (List.range n).map (fun t => [lastX + 1 + t, i + t, 0])
  | 0, _, _, _ => rfl
  | n + 1, rp1, lastX, i => by
    rw [List.replicate_succ, unitsM, if_pos rfl, unitsM_chain n, map_range_succ']
    refine congrArg₂ List.cons (list3_eq (by omega) (by omega) rfl)
      (List.map_congr_left (fun t _ => list3_eq (by omega) (by omega) rfl))

theorem unitsM_ones (rp1 lastX y N : Nat) :
    unitsM rp1 lastX false (y + 1) (List.replicate (N + 1) none)
      = (List.range (N + 1 + 1)).map (fun t => [rp1 + t, y + t, 0]) := by
  rw [List.replicate_succ, unitsM, if_neg Bool.false_ne_true, unitsM_chain, map_range_succ',
    map_range_succ']
  refine congrArg₂ List.cons (list3_eq (by omega) (by omega) rfl)
    (congrArg₂ List.cons (list3_eq (by omega) (by omega) rfl)
      (List.map_congr_left (fun t _ => list3_eq (by omega) (by omega) rfl)))

theorem treeB_shape (t : Term) : ∀ (x : Nat), ∀ col ∈ treeB x t,
    ∃ x' v, x ≤ x' ∧ v ≤ 1 ∧ col = [x', v, 0] := by
  induction t with
  | nil => intro x col h; simp [treeB] at h
  | cons a b u _ ihb ihu =>
    intro x col h
    rw [treeB, List.mem_append, List.mem_cons] at h
    rcases h with (rfl | h) | h
    · refine ⟨x, subY a, le_rfl, ?_, rfl⟩
      cases a <;> simp [subY]
    · obtain ⟨x', v, h1, h2, rfl⟩ := ihb (x + 1) col h
      exact ⟨x', v, by omega, h2, rfl⟩
    · exact ihu x col h

theorem ancP_mulL (x0 y : Nat) : ∀ L : List Term, (∀ γ ∈ L, CtS γ) → AncP (mulL x0 y L)
  | [], _ => by intro j hj; simp [mulL] at hj
  | γ :: L, h => by
    rw [mulL]
    exact ancP_append (ancP_append (ancP_digit _ rfl)
      (ancP_treeB γ (x0 + 2) (h γ (List.mem_cons_self ..))))
      (ancP_mulL x0 y L (fun g hg => h g (List.mem_cons_of_mem _ hg)))

theorem tailColE_mulL (a y : Nat) : ∀ L : List Term, ∀ col ∈ mulL (a + 1) (y + 1) L,
    TailColE a y col
  | [], col, h => by simp [mulL] at h
  | γ :: L, col, h => by
    rw [mulL, List.mem_append, List.mem_cons] at h
    rcases h with (rfl | h) | h
    · exact Or.inl rfl
    · obtain ⟨x', v, h1, h2, rfl⟩ := treeB_shape γ (a + 1 + 2) col h
      exact Or.inr ⟨x', v, by omega, h2, rfl⟩
    · exact tailColE_mulL a y L col h

theorem asc_mulL (a y c : Nat) : ∀ L : List Term,
    (mulL (a + 1) (y + 1) L).map (ascColE a c) = mulL (a + 1 + c * 2) (y + 1 + c) L
  | [] => rfl
  | γ :: L => by
    rw [mulL, mulL, List.map_append, List.map_cons, asc_mulL a y c L]
    congr 2
    · simp [ascColE]; omega
    · rw [show a + 1 + c * 2 + 2 = a + 1 + 2 + c * 2 by omega, ← treeB_shift (c * 2) γ]
      refine List.map_congr_left (fun col hcol => ?_)
      obtain ⟨x', v, h1, _, rfl⟩ := treeB_shape γ (a + 1 + 2) col hcol
      have : ¬ x' < a + 3 := by omega
      simp [ascColE, this, shiftC]

/-! ### Four moves on the last unit -/

/-- **Move 1**: the last tree comes down to anything below it. -/
theorem move_tree (P : List (List Nat)) (rp1 i : Nat) (C : List Term) (G : Term) (hG : TopOK G)
    (h : Reach3 (P ++ unitM rp1 i (C ++ [G]))) (t : Term) (ht : OT t) (hC : CtS t)
    (hle : t ≤ G) : Reach3 (P ++ unitM rp1 i (C ++ [t])) := by
  have e : ∀ u : Term, P ++ unitM rp1 i (C ++ [u])
      = (P ++ (unitM rp1 i C ++ [[rp1 + 1 + 1, i, 1]])) ++ treeB (rp1 + 1 + 2) u := by
    intro u
    rw [unitM_append, mulL_single]; simp
  rw [e] at h ⊢
  exact treeReach_top hG _ _ h t ht hC hle

theorem treeB_appT_one (x : Nat) (δ : Term) : treeB x (appT δ t1) = treeB x δ ++ [[x, 0, 0]] := by
  rw [treeB_appT]; rfl

/-- **Move 2**: a last tree `δ + 1` becomes `N + 1` multiply units `δ`. -/
theorem move_copy (P : List (List Nat)) (rp1 i : Nat) (C : List Term) (δ : Term) (N : Nat)
    (h : Reach3 (P ++ unitM rp1 i (C ++ [appT δ t1]))) :
    Reach3 (P ++ unitM rp1 i (C ++ List.replicate (N + 1) δ)) := by
  have e : P ++ unitM rp1 i (C ++ [appT δ t1])
      = (P ++ unitM rp1 i C) ++ ([rp1 + 1 + 1, i, 1] :: treeB (rp1 + 1 + 2) δ
          ++ [[rp1 + 1 + 2, 0, 0]]) := by
    rw [unitM_append, mulL_single, treeB_appT_one]; simp
  rw [e] at h
  have hE := expandRL_copy_block N (P ++ unitM rp1 i C) [rp1 + 1 + 1, i, 1]
    (treeB (rp1 + 1 + 2) δ) (rp1 + 1 + 2) (reach3_wf h) (by simp) (treeB_ge δ _)
  have := reach3_expand h N
  rw [hE] at this
  rw [unitM_append, mulL_replicate, ← List.append_assoc]
  exact this

/-- **Move 3**: an add unit ending in a bare digit becomes `N + 1` add units. -/
theorem move_units (P : List (List Nat)) (rp1 lastX i : Nat) (hi : 1 ≤ i) (L : List Term)
    (hL : ∀ γ ∈ L, CtS γ) (N : Nat) (h : Reach3 (P ++ unitM rp1 i (L ++ [nil]))) :
    Reach3 (P ++ unitsM rp1 lastX false i (List.replicate (N + 1) (some L))) := by
  obtain ⟨y, rfl⟩ : ∃ y, i = y + 1 := ⟨i - 1, by omega⟩
  have e : P ++ unitM rp1 (y + 1) (L ++ [nil])
      = P ++ (([rp1, y, 0] :: [rp1 + 1, y + 1, 1] :: mulL (rp1 + 1) (y + 1) L)
          ++ [[rp1 + 2, y + 1, 1]]) := by
    rw [unitM_append, mulL_single]; simp [unitM, treeB]
  rw [e] at h
  have hE := expandRL_digit_unitE N rp1 y P (mulL (rp1 + 1) (y + 1) L)
    (tailColE_mulL rp1 y L) (ancP_mulL _ _ L hL)
  have := reach3_expand h N
  rw [hE] at this
  rw [unitsM_replicate_some]
  convert this using 3
  refine List.map_congr_left (fun c _ => ?_)
  rw [List.map_cons, asc_mulL, unitM, show rp1 + c * 2 + 1 = rp1 + 1 + c * 2 by omega]
  simp [ascColE]

/-- **Move 4**: an add unit with no multiply units becomes a chain of `N + 1`
units `1`. -/
theorem move_ones (P : List (List Nat)) (rp1 lastX i : Nat) (hi : 1 ≤ i) (N : Nat)
    (h : Reach3 (P ++ unitM rp1 i [])) :
    Reach3 (P ++ unitsM rp1 lastX false i (List.replicate (N + 1) none)) := by
  obtain ⟨y, rfl⟩ : ∃ y, i = y + 1 := ⟨i - 1, by omega⟩
  have e : P ++ unitM rp1 (y + 1) [] = P ++ [[rp1, y, 0], [rp1 + 1, y + 1, 1]] := by
    simp [unitM, mulL]
  rw [e] at h
  have := reach3_expand h (N + 1)
  rw [expandRL_anchor_root] at this
  rw [unitsM_ones]
  exact this

/-! ### Descending lists of trees and of units -/

/-- The trees do not increase. -/
def DescL : List Term → Prop
  | [] => True
  | [_] => True
  | a :: b :: l => b ≤ a ∧ DescL (b :: l)

/-- Every tree is a standard form of the fragment. -/
def AllOK (L : List Term) : Prop := ∀ γ ∈ L, OT γ ∧ CtS γ

/-- The dictionary order on lists of trees, a prefix counting as smaller. -/
def LeL : List Term → List Term → Prop
  | [], _ => True
  | _ :: _, [] => False
  | a :: l, b :: m => a < b ∨ (a = b ∧ LeL l m)

/-- The order on units: a unit `1` is below every add unit. -/
def LeU : Option (List Term) → Option (List Term) → Prop
  | none, _ => True
  | some _, none => False
  | some L', some L => LeL L' L

/-- The units do not increase. -/
def DescU : List (Option (List Term)) → Prop
  | [] => True
  | [_] => True
  | a :: b :: l => LeU b a ∧ DescU (b :: l)

/-- Every add unit has descending trees of the fragment. -/
def UnitsOK (S : List (Option (List Term))) : Prop := ∀ L, some L ∈ S → AllOK L ∧ DescL L

theorem descL_tail : ∀ {a : Term} {l : List Term}, DescL (a :: l) → DescL l
  | _, [], _ => trivial
  | _, _ :: _, h => h.2

theorem descL_snoc_nil : ∀ L : List Term, DescL L → DescL (L ++ [nil])
  | [], _ => trivial
  | [a], _ => ⟨nil_le a, trivial⟩
  | _ :: b :: l, h => ⟨h.1, descL_snoc_nil (b :: l) h.2⟩

theorem allOK_snoc_nil {L : List Term} (h : AllOK L) : AllOK (L ++ [nil]) := by
  intro γ hγ
  rcases List.mem_append.mp hγ with h' | h'
  · exact h γ h'
  · simp at h'; subst h'; exact ⟨rfl, trivial⟩

theorem leL_snoc_nil : ∀ L' L : List Term, LeL L' L → L' ≠ L → LeL (L' ++ [nil]) L
  | [], [], _, hne => absurd rfl hne
  | [], b :: m, _, _ => by
    show nil < b ∨ (nil = b ∧ LeL [] m)
    cases b with
    | nil => exact Or.inr ⟨rfl, trivial⟩
    | cons _ _ _ => exact Or.inl (nil_lt_cons _ _ _)
  | _ :: _, [], h, _ => absurd h id
  | a :: l, b :: m, h, hne => by
    rcases h with h | ⟨rfl, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨rfl, leL_snoc_nil l m h (fun e => hne (by rw [e]))⟩

theorem descU_none : ∀ S : List (Option (List Term)), DescU (none :: S) →
    S = List.replicate S.length none
  | [], _ => rfl
  | u :: S, h => by
    cases u with
    | none => rw [List.length_cons, List.replicate_succ, ← descU_none S h.2]
    | some L => exact absurd h.1 id

theorem appT_one_le : ∀ δ' δ : Term, δ' < δ → appT δ' t1 ≤ δ
  | nil, δ, h => one_le δ (fun e => by subst e; exact not_lt_nil _ h)
  | cons _ _ _, nil, h => absurd h (not_lt_nil _)
  | cons a b u, cons c d w, h => by
    rcases cons_lt_cons_iff.mp h with h1 | ⟨h1, h2⟩
    · exact le_of_lt (cons_lt_cons_iff.mpr (Or.inl h1))
    · injection h1 with e1 e2
      subst e1 e2
      rcases le_iff_lt_or_eq.mp (appT_one_le u w h2) with h3 | h3
      · exact le_of_lt (cons_lt_cons_iff.mpr (Or.inr ⟨rfl, h3⟩))
      · show cons a b (appT u t1) ≤ cons a b w
        rw [h3]; exact le_refl _

theorem OT_appT_one : ∀ δ : Term, OT δ → CtS δ → OT (appT δ t1)
  | nil, _, _ => by decide
  | cons a b u, h, hC => by
    obtain ⟨rfl, _, hu⟩ := hC
    refine OT_cons_of (OT_head h) (OT_appT_one u (OT_tail h) hu) ?_
    cases u with
    | nil => exact psi_le_psi_of_le (nil_le b)
    | cons c d w => exact OT_tail_head_le h

theorem ctS_appT_one {δ : Term} (h : CtS δ) : CtS (appT δ t1) :=
  (ctS_appT _ _).mpr ⟨h, ⟨rfl, trivial, trivial⟩⟩

theorem lt_appT_one : ∀ δ : Term, δ < appT δ t1
  | nil => nil_lt_cons _ _ _
  | cons _ _ u => cons_lt_cons_iff.mpr (Or.inr ⟨rfl, lt_appT_one u⟩)

/-! ### Filling the last unit -/

/-- **From a last tree `δ + 1`, any descending run `δ, …, δ, S` with `S ≤ δ`.** -/
theorem mulFill (P : List (List Nat)) (rp1 i : Nat) : ∀ (S C : List Term) (δ : Term) (j : Nat),
    Reach3 (P ++ unitM rp1 i (C ++ [appT δ t1])) → OT δ → CtS δ → DescL (δ :: S) → AllOK S →
    Reach3 (P ++ unitM rp1 i (C ++ (List.replicate (j + 1) δ ++ S))) := by
  intro S
  induction S with
  | nil =>
    intro C δ j h _ _ _ _
    rw [List.append_nil]
    exact move_copy P rp1 i C δ j h
  | cons ε S ih =>
    intro C δ j h hOT hC hD hA
    obtain ⟨hle, hD'⟩ := hD
    have hε := hA ε (List.mem_cons_self ..)
    have hA' : AllOK S := fun g hg => hA g (List.mem_cons_of_mem _ hg)
    rcases le_iff_lt_or_eq.mp hle with hlt | rfl
    · have h1 := move_copy P rp1 i C δ (j + 1) h
      rw [List.replicate_succ', ← List.append_assoc] at h1
      have h2 := move_tree P rp1 i (C ++ List.replicate (j + 1) δ) δ ⟨hOT, hC⟩ h1
        (appT ε t1) (OT_appT_one ε hε.1 hε.2) (ctS_appT_one hε.2) (appT_one_le ε δ hlt)
      have h3 := ih (C ++ List.replicate (j + 1) δ) ε 0 h2 hε.1 hε.2 hD' hA'
      rw [List.append_assoc] at h3
      simpa using h3
    · have h1 := ih C ε (j + 1) h hOT hC hD' hA'
      rw [List.replicate_succ', List.append_assoc] at h1
      simpa using h1

/-- **The last unit comes down to anything below it.** -/
theorem mulDesc (P : List (List Nat)) (rp1 i : Nat) : ∀ (L' C L : List Term),
    Reach3 (P ++ unitM rp1 i (C ++ L)) → (∀ γ ∈ L, TopOK γ) → DescL L' → AllOK L' → LeL L' L →
    Reach3 (P ++ unitM rp1 i (C ++ L')) := by
  intro L'
  induction L' with
  | nil =>
    intro C L h _ _ _ _
    rw [List.append_nil]
    rw [unitM_append, ← List.append_assoc] at h
    exact reach3_prefix _ _ h
  | cons γ' S ih =>
    intro C L h hT hD hA hle
    cases L with
    | nil => exact absurd hle id
    | cons γ R =>
      have hγ' := hA γ' (List.mem_cons_self ..)
      rcases hle with hlt | ⟨rfl, hle'⟩
      · have h0 : Reach3 (P ++ unitM rp1 i (C ++ [γ'])) := by
          have : Reach3 (P ++ unitM rp1 i (C ++ [γ])) := by
            rw [show C ++ γ :: R = (C ++ [γ]) ++ R by simp, unitM_append,
              ← List.append_assoc] at h
            exact reach3_prefix _ _ h
          exact move_tree P rp1 i C γ (hT γ (List.mem_cons_self ..)) this γ' hγ'.1 hγ'.2
            (le_of_lt hlt)
        have h1 : Reach3 (P ++ unitM rp1 i (C ++ [appT γ' t1])) := by
          have : Reach3 (P ++ unitM rp1 i (C ++ [γ])) := by
            rw [show C ++ γ :: R = (C ++ [γ]) ++ R by simp, unitM_append,
              ← List.append_assoc] at h
            exact reach3_prefix _ _ h
          exact move_tree P rp1 i C γ (hT γ (List.mem_cons_self ..)) this (appT γ' t1)
            (OT_appT_one γ' hγ'.1 hγ'.2) (ctS_appT_one hγ'.2) (appT_one_le γ' γ hlt)
        have := mulFill P rp1 i S C γ' 0 h1 hγ'.1 hγ'.2 hD
          (fun g hg => hA g (List.mem_cons_of_mem _ hg))
        simpa using this
      · have := ih (C ++ [γ']) R (by simpa using h)
          (fun g hg => hT g (List.mem_cons_of_mem _ hg)) (descL_tail hD)
          (fun g hg => hA g (List.mem_cons_of_mem _ hg)) hle'
        simpa using this

/-- **From a last unit `β + 1`, any descending row of units `β, …, β, S` with
`S ≤ β`.** -/
theorem unitFill : ∀ (S : List (Option (List Term))) (P : List (List Nat)) (rp1 i : Nat)
    (L : List Term) (j : Nat), 1 ≤ i → Reach3 (P ++ unitM rp1 i (L ++ [nil])) → AllOK L →
    DescL L → DescU (some L :: S) → UnitsOK S →
    Reach3 (P ++ unitsM rp1 0 false i (List.replicate (j + 1) (some L) ++ S)) := by
  intro S
  induction S with
  | nil =>
    intro P rp1 i L j hi h hA _ _ _
    rw [List.append_nil]
    exact move_units P rp1 0 i hi L (fun g hg => (hA g hg).2) j h
  | cons u S ih =>
    intro P rp1 i L j hi h hA hD hDU hU
    obtain ⟨hle, hDU'⟩ := hDU
    have hTop : ∀ γ ∈ L, TopOK γ := fun g hg => hA g hg
    have h1 := move_units P rp1 0 i hi L (fun g hg => (hA g hg).2) (j + 1) h
    rw [List.replicate_succ', unitsM_append_some L _ j, unitsM, unitsM_lastX _ _ 0,
      show unitsM (rp1 + (j + 1) * 2 + 2) (rp1 + (j + 1) * 2 + 1) false (i + (j + 1) + 1) [] = []
        from rfl, List.append_nil, ← List.append_assoc] at h1
    set P' := P ++ unitsM rp1 0 false i (List.replicate (j + 1) (some L)) with hP'
    rw [unitsM_append_some L _ j, ← List.append_assoc]
    cases u with
    | none =>
      have h2 := mulDesc P' (rp1 + (j + 1) * 2) (i + (j + 1)) [] [] L (by simpa using h1) hTop
        trivial (by intro g hg; simp at hg) trivial
      rw [List.nil_append] at h2
      have hS := descU_none S hDU'
      rw [hS, ← List.replicate_succ]
      exact move_ones P' _ 0 _ (by omega) S.length h2
    | some L' =>
      by_cases hL : L' = L
      · subst hL
        have := ih P rp1 i L' (j + 1) hi h hA hD hDU'
          (fun g hg => hU g (List.mem_cons_of_mem _ hg))
        rw [List.replicate_succ', List.append_assoc] at this
        rw [unitsM_append_some L' _ j, ← List.append_assoc] at this
        exact this
      · have hUL := hU L' (List.mem_cons_self ..)
        have h2 := mulDesc P' (rp1 + (j + 1) * 2) (i + (j + 1)) (L' ++ [nil]) [] L
          (by simpa using h1) hTop (descL_snoc_nil L' hUL.2) (allOK_snoc_nil hUL.1)
          (leL_snoc_nil L' L hle hL)
        rw [List.nil_append] at h2
        have := ih P' (rp1 + (j + 1) * 2) (i + (j + 1)) L' 0 (by omega) h2 hUL.1 hUL.2 hDU'
          (fun g hg => hU g (List.mem_cons_of_mem _ hg))
        rw [unitsM_lastX _ _ 0] at this
        exact this

/-! ### Every descending row of units is reachable -/

/-- **Every descending row of units whose trees are standard countable terms
of the fragment is the entries of a standard three-row array.** -/
theorem reach_units (D : List (Option (List Term))) (hD : DescU D) (hU : UnitsOK D) :
    Reach3 (unitsM 0 0 false 1 D) := by
  have hfirst : ∀ γ, OT γ → CtS γ → Reach3 ([] ++ unitM 0 1 [γ]) := by
    intro γ hOT hC
    have e : [] ++ unitM 0 1 [γ] = [[0, 0, 0], [1, 1, 1], [2, 1, 1]] ++ treeB 3 γ := by
      rw [List.nil_append, unitM, mulL_single]; rfl
    rw [e]; exact first_unit γ hOT hC
  cases D with
  | nil =>
    exact reach3_prefix [[0, 0, 0]] [] (reach3_gen 0 : Reach3 [[0, 0, 0]])
  | cons u S =>
    cases u with
    | none =>
      have hS := descU_none S hD
      have h0 : Reach3 ([] ++ unitM 0 1 []) := (reach3_gen 1 : Reach3 [[0, 0, 0], [1, 1, 1]])
      have := move_ones [] 0 0 1 le_rfl S.length h0
      rw [List.nil_append, List.replicate_succ, ← hS] at this
      exact this
    | some L =>
      have hL := hU L (List.mem_cons_self ..)
      have h1 : Reach3 ([] ++ unitM 0 1 (L ++ [nil])) := by
        cases L with
        | nil => exact hfirst nil rfl trivial
        | cons γ R =>
          have hγ := hL.1 γ (List.mem_cons_self ..)
          have hT := hfirst (appT γ t1) (OT_appT_one γ hγ.1 hγ.2) (ctS_appT_one hγ.2)
          have := mulDesc [] 0 1 ((γ :: R) ++ [nil]) [] [appT γ t1] (by simpa using hT)
            (fun g hg => by
              simp at hg; subst hg
              exact ⟨OT_appT_one γ hγ.1 hγ.2, ctS_appT_one hγ.2⟩)
            (descL_snoc_nil _ hL.2) (allOK_snoc_nil hL.1) (Or.inl (lt_appT_one γ))
          simpa using this
      have := unitFill S [] 0 1 L 0 le_rfl h1 hL.1 hL.2 hD
        (fun g hg => hU g (List.mem_cons_of_mem _ hg))
      simpa using this

/-! ### The trio matrices are such rows -/

/-- The arguments of the summands. -/
def argsOf : Term → List Term
  | nil => []
  | cons _ g t => g :: argsOf t

/-- The units of `trioE α`. -/
def dataOf : Term → List (Option (List Term))
  | nil => []
  | cons _ b t => (if b == nil then none else some (argsOf (peelE b))) :: dataOf t

theorem mulUnitsE_eq (x0 y : Nat) : ∀ t : Term, mulUnitsE x0 y t = mulL x0 y (argsOf t)
  | nil => rfl
  | cons _ g t => by rw [mulUnitsE, argsOf, mulL, mulUnitsE_eq x0 y t]

theorem addUnitsE_eq : ∀ (α : Term) (rp1 lastX : Nat) (pz : Bool) (i : Nat),
    addUnitsE rp1 lastX pz i α = unitsM rp1 lastX pz i (dataOf α)
  | nil, _, _, _, _ => rfl
  | cons a b t, rp1, lastX, pz, i => by
    rw [addUnitsE, dataOf]
    by_cases hb : b = nil
    · subst hb
      simp only [beq_self_eq_true, if_true, unitsM]
      split <;> rw [addUnitsE_eq t]
    · have hb' : (b == nil) = false := by simpa using hb
      simp only [hb', Bool.false_eq_true, if_false, unitsM]
      rw [addUnitsE_eq t, bodyE, mulUnitsE_eq]
      rfl

theorem trioE_eq (α : Term) : trioE α = unitsM 0 0 false 1 (dataOf α) :=
  addUnitsE_eq α 0 0 false 1

theorem leL_refl : ∀ L : List Term, LeL L L
  | [] => trivial
  | _ :: L => Or.inr ⟨rfl, leL_refl L⟩

theorem argsOf_le : ∀ s t : Term, TopNil s → TopNil t → s ≤ t → LeL (argsOf s) (argsOf t)
  | nil, _, _, _, _ => trivial
  | cons _ _ _, nil, _, _, h => absurd (eq_nil_of_le_nil' h) (fun e => Term.noConfusion e)
  | cons a g u, cons a' g' u', hs, ht, h => by
    obtain ⟨rfl, hu⟩ := hs
    obtain ⟨rfl, hu'⟩ := ht
    rcases le_iff_lt_or_eq.mp h with h | h
    · rcases TrioMono.cons_lt_cases h with h | ⟨rfl, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨rfl, argsOf_le u u' hu hu' (le_of_lt h2)⟩
    · rw [h]; exact leL_refl _

/-- The arguments of a standard sum of `ψ_0`s do not increase. -/
theorem descL_argsOf : ∀ t : Term, OT t → TopNil t → DescL (argsOf t)
  | nil, _, _ => trivial
  | cons a g nil, _, _ => trivial
  | cons a g (cons c d w), hOT, hT => by
    obtain ⟨rfl, hT'⟩ := hT
    have hc : c = nil := hT'.1
    subst hc
    exact ⟨psi_le_psi_nil (OT_tail_head_le hOT), descL_argsOf _ (OT_tail hOT) hT'⟩

theorem allOK_argsOf : ∀ t : Term, OT t → (∀ g ∈ argsOf t, CtS g) → AllOK (argsOf t)
  | nil, _, _ => by intro γ h; simp [argsOf] at h
  | cons a g u, hOT, hC => by
    intro γ h
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨OT_snd hOT, hC γ (List.mem_cons_self ..)⟩
    · exact allOK_argsOf u (OT_tail hOT) (fun g' hg' => hC g' (List.mem_cons_of_mem _ hg')) γ h

theorem argsOf_dropLastT : ∀ t : Term, ∃ R, argsOf t = argsOf (dropLastT t) ++ R
  | nil => ⟨[], rfl⟩
  | cons a g u => by
    rw [dropLastT]
    split
    · exact ⟨[g], by rename_i h; rw [beq_iff_eq.mp h]; rfl⟩
    · obtain ⟨R, hR⟩ := argsOf_dropLastT u
      exact ⟨R, by rw [argsOf, argsOf, hR]; rfl⟩

theorem descL_prefix : ∀ L R : List Term, DescL (L ++ R) → DescL L
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | _ :: b :: l, R, h => ⟨h.1, descL_prefix (b :: l) R h.2⟩

theorem OT_dropLastT : ∀ t : Term, OT t → OT (dropLastT t)
  | nil, h => h
  | cons a g u, h => by
    rw [dropLastT]
    split
    · rfl
    · rename_i hu
      have hu' : u ≠ nil := fun e => hu (by rw [e]; rfl)
      obtain ⟨c, d, w, rfl⟩ : ∃ c d w, u = cons c d w := by
        cases u with
        | nil => exact absurd rfl hu'
        | cons c d w => exact ⟨c, d, w, rfl⟩
      refine OT_cons_of (OT_head h) (OT_dropLastT _ (OT_tail h)) ?_
      rw [dropLastT]
      split
      · trivial
      · exact OT_tail_head_le h

theorem topNil_dropLastT : ∀ t : Term, TopNil t → TopNil (dropLastT t)
  | nil, h => h
  | cons a g u, h => by
    rw [dropLastT]
    split
    · trivial
    · exact ⟨h.1, topNil_dropLastT u h.2⟩

theorem unitOK_of {b : Term} (hOT : OT (psi nil b)) (hE : Sub01 b) :
    AllOK (argsOf (peelE b)) ∧ DescL (argsOf (peelE b)) := by
  have hOTb : OT b := OT_snd hOT
  by_cases hA : AllNil b
  · rw [peelE_of_allNil hA]
    have hT : TopNil b := topNil_of_allNil b hA
    have hC : ∀ g ∈ argsOf b, CtS g := by
      intro g hg
      suffices ∀ t : Term, AllNil t → ∀ g ∈ argsOf t, AllNil g by
        exact ctS_of_allNil g (this b hA g hg)
      intro t
      induction t with
      | nil => intro _ g hg; simp [argsOf] at hg
      | cons a g' u _ _ ihu =>
        intro h g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact h.2.1
        · exact ihu h.2.2 g hg
    have hOKb := allOK_argsOf b hOTb hC
    have hDb := descL_argsOf b hOTb hT
    unfold peelOne
    split
    · obtain ⟨R, hR⟩ := argsOf_dropLastT b
      refine ⟨fun γ hγ => hOKb γ (by rw [hR]; exact List.mem_append_left _ hγ), ?_⟩
      rw [hR] at hDb; exact descL_prefix _ _ hDb
    · exact ⟨hOKb, hDb⟩
  · rw [peelE_of_not hA]
    exact ⟨fun γ hγ => by
      simp [argsOf] at hγ; subst hγ; exact ⟨hOT, rfl, hE, trivial⟩, trivial⟩

theorem unitsOK_dataOf : ∀ α : Term, OT α → CtS α → UnitsOK (dataOf α)
  | nil, _, _ => by intro L h; simp [dataOf] at h
  | cons a b t, hOT, hC => by
    obtain ⟨rfl, hb, ht⟩ := hC
    intro L hL
    rw [dataOf] at hL
    rcases List.mem_cons.mp hL with h | h
    · by_cases hb0 : b = nil
      · subst hb0; simp at h
      · have hb' : (b == nil) = false := by simpa using hb0
        rw [hb'] at h
        simp only [Bool.false_eq_true, if_false, Option.some.injEq] at h
        subst h
        exact unitOK_of (OT_head hOT) hb
    · exact unitsOK_dataOf t (OT_tail hOT) ht L h

theorem descU_dataOf : ∀ α : Term, OT α → CtS α → DescU (dataOf α)
  | nil, _, _ => trivial
  | cons a b nil, _, _ => trivial
  | cons a b (cons c b' w), hOT, hC => by
    obtain ⟨rfl, hb, rfl, hb', hw⟩ := hC
    refine ⟨?_, descU_dataOf _ (OT_tail hOT) ⟨rfl, hb', hw⟩⟩
    have hle : b' ≤ b := psi_le_psi_nil (OT_tail_head_le hOT)
    show LeU (if b' == nil then none else some (argsOf (peelE b')))
      (if b == nil then none else some (argsOf (peelE b)))
    by_cases hb0' : b' = nil
    · subst hb0'; simp [LeU]
    · have hb0 : b ≠ nil := fun e => by subst e; exact hb0' (eq_nil_of_le_nil' hle)
      have e1 : (b' == nil) = false := by simpa using hb0'
      have e2 : (b == nil) = false := by simpa using hb0
      simp only [e1, e2, Bool.false_eq_true, if_false, LeU]
      have hAb := argOK_of_OT (OT_head hOT) hb
      have hAb' := argOK_of_OT (OT_head (OT_tail hOT)) hb'
      refine argsOf_le _ _ (topNil_peelE b') (topNil_peelE b) ?_
      rcases le_iff_lt_or_eq.mp hle with h | rfl
      · exact le_of_lt (peelE_lt hAb' hAb hb0' h)
      · exact le_refl _

/-! ### The theorem -/

/-- **The trio matrix `trioE α` is a standard form** for every standard
countable `α` whose subscripts are all `0` or `1` (all of these are below
`ψ_0(Ω_2)`): it is the entries of a three-row array reached from a generator
by expansions. -/
theorem trioE_std {α : Term} (hOT : OT α) (hc : α < tW) (hS : Sub01 α) :
    ∃ A : BM4.Arr 3, Pat.Std 3 A ∧ entriesR A = trioE α := by
  have hC : CtS α := ctS_of α (topNil_of_lt_tW hOT hc) hS
  rw [trioE_eq]
  exact reach_units _ (descU_dataOf α hOT hC) (unitsOK_dataOf α hOT hC)

end Googology.Trans.BMS.TrioTreeStd
