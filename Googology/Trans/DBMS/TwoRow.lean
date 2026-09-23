import Googology.Trans.DBMS.TwoRowBlock
import Googology.Trans.DBMS.Entries
import Googology.Trans.PSS.Rank

/-!
# Two-row DBMS into the ordinals

`dbmsL2` is DBMS with two rows on the entries, a state being the list of pairs
of a standard two-row DBMS array; `dbmsL2Std` names the generators
`(0,0)(1,0)(2,1)⋯(n,n-1)`.  It is the array system `dbms 2` (`dbmsToL2`,
bracket for bracket, onto, same ranks) and the list system `dbmsL 1`
(`dbmsL2ToL`, one to one and onto, same ranks).

**The standard forms.**  `TwoRowBlock.lean` cuts a matrix into blocks
`blk M = (0,0)` followed by `M` with its first row raised by one.
`dreach2_iff_dform`: a list is a standard two-row DBMS matrix exactly when it
is `blk M₀ ++ blk M₁ ++ ⋯ ++ blk Mₖ` with every `Mᵢ` a standard pair sequence
(a state of `pairL`, possibly empty) and `o(M₀) ≥ o(M₁) ≥ ⋯ ≥ o(Mₖ)`, where
`o = pairOrdL` is the ordinal of pair sequences (`Trans/PSS/Rank.lean`).

**The ordinal.**

    dOrdL (blk M₀ ++ ⋯ ++ blk Mₖ) = ω^o(M₀) + ω^o(M₁) + ⋯ + ω^o(Mₖ)

So the block of the empty sequence, `(0,0)`, is `1`; `(0,0)(1,0)` is `ω`; the
generator `(0,0)(1,0)(2,1)` is `ω^ε₀ = ε₀`.  The six columns of the ordinal
table:

* defined: `dbmsL2OrdEval`, with `dOrdL`.
* injective: `dbmsL2OrdEval_injective` — uniqueness of Cantor normal form
  (`oSum_inj`) and injectivity of `pairOrdL`.
* surjective: `dbmsL2Ord_image` — onto the ordinals below `ψ_0(Ω_ω)`, the same
  set as the pair sequences.  It needs that `ψ_0(Ω_ω)` is closed under
  `x ↦ ω^x` (`opow_lt_psi_Omega_omega`): a countable `x` in `C_0(Ω_ω)` lies in
  some `C_0(Ω_k)`, and then `ω^x ≤ ψ_0(Ω_k + x) < ψ_0(Ω_ω)`.
* decreases on expansion: `dbmsL2OrdEval.val_lt`.
* equals the rank: `rank_dbmsL2_eq`.  Expansion changes only the last block
  (`dOrdL_step`): the block of `[]` is removed (`α + 1 ↦ α`); a block of `M`
  without bad root turns into `N + 1` copies of the block of `M[N]`
  (`ω^(β+1) ↦ ω^β·(N+1)`); any other block of `M` turns into the block of
  `M[N]`, and then `o(M)` is a limit (`pairOrdL_isSuccLimit`), so
  `ω^o(M[N])` is cofinal in `ω^o(M)`.
* order-preserving: `ltPS_iff_dOrdL_lt`, for the lexicographic order `<ₚ` of
  koteitan/pss-proof, the order used for the pair sequences.

The same ordinal on the arrays: `rank_dbms2_eq`.
-/

namespace Googology.Trans.DBMS

open BM4
open Googology.Notation.DBMS
open Googology.Trans.BMS
open Googology.Trans.PSS
open Bijectivity (CTPS)

/-! ### Splitting a list into its blocks -/

/-- One step of reading a list from the right: a column with first entry `0`
closes a block. -/
def splitStep (x : ℕ × ℕ) (acc : List (ℕ × ℕ) × List (List (ℕ × ℕ))) :
    List (ℕ × ℕ) × List (List (ℕ × ℕ)) :=
  if x.1 = 0 then ([], acc.1 :: acc.2) else ((x.1 - 1, x.2) :: acc.1, acc.2)

/-- The blocks of a list, read from the right. -/
def splitBlocks (D : List (ℕ × ℕ)) : List (ℕ × ℕ) × List (List (ℕ × ℕ)) :=
  D.foldr splitStep ([], [])

/-- The pair sequences of the blocks of a list. -/
def blocksOf (D : List (ℕ × ℕ)) : List (List (ℕ × ℕ)) := (splitBlocks D).2

theorem splitBlocks_sh_append (M R : List (ℕ × ℕ)) :
    splitBlocks (sh M ++ R) = (M ++ (splitBlocks R).1, (splitBlocks R).2) := by
  induction M with
  | nil => rfl
  | cons x M ih =>
    show splitStep (shc x) (splitBlocks (sh M ++ R)) = _
    rw [ih]
    simp [splitStep, shc]

theorem splitBlocks_blocks (Ms : List (List (ℕ × ℕ))) : splitBlocks (blocks Ms) = ([], Ms) := by
  induction Ms with
  | nil => rfl
  | cons M Ms ih =>
    rw [blocks_cons]
    show splitStep (0, 0) (splitBlocks (sh M ++ blocks Ms)) = _
    rw [splitBlocks_sh_append, ih]
    simp [splitStep]

@[simp] theorem blocksOf_blocks (Ms : List (List (ℕ × ℕ))) : blocksOf (blocks Ms) = Ms := by
  rw [blocksOf, splitBlocks_blocks]

/-! ### The system -/

/-- The entries of a standard two-row DBMS array. -/
def DReach2 (l : List (ℕ × ℕ)) : Prop := ∃ A : Arr 2, DStd 2 A ∧ entries2 A = l

theorem entries2_dstair (n : ℕ) :
    entries2 (dstair 2 n) = (List.range (n + 1)).map (fun i => (i, i - 1)) := by
  rw [entries2, show (dstair 2 n).len = n + 1 from rfl]
  simp

theorem dreach2_gen (n : ℕ) : DReach2 ((List.range (n + 1)).map (fun i => (i, i - 1))) :=
  ⟨dstair 2 n, DStd.init n, entries2_dstair n⟩

theorem dreach2_expand {l : List (ℕ × ℕ)} (h : DReach2 l) (N : ℕ) :
    DReach2 (expand2L N l) := by
  obtain ⟨A, hA, rfl⟩ := h
  exact ⟨expand A N, DStd.step N hA, entries2_expand A N⟩

/-- The state of two-row DBMS: the entries of a standard two-row DBMS array,
as a list of pairs. -/
def DbmsState2 : Type := {l : List (ℕ × ℕ) // DReach2 l}

/-- **Two-row DBMS on the entries.**  The step is `expand2L`, the two-row rule
that `entries2_expand` proves to be `BM4.expand`. -/
def dbmsL2 : Rewrite where
  State := DbmsState2
  step := fun l N => ⟨expand2L N l.1, dreach2_expand l.2 N⟩
  halted := fun l => l.1 = []

@[simp] theorem dbmsL2_step_val (l : DbmsState2) (N : ℕ) :
    ((dbmsL2.step l N : DbmsState2)).1 = expand2L N l.1 := rfl

/-- The generators `(0,0)(1,0)(2,1)⋯(n,n-1)`. -/
def dbmsL2Std : dbmsL2.Std where
  Standard := fun _ => True
  gen := fun n => ⟨(List.range (n + 1)).map (fun i => (i, i - 1)), dreach2_gen n⟩
  gen_std := fun _ => trivial
  step_std := fun _ _ _ => trivial

/-! ### Pair sequences: what is needed of them -/

/-- The pair sequence `(0,0)(1,1)⋯(n-1,n-1)`, empty at `n = 0`. -/
def pairGenL (n : ℕ) : List (ℕ × ℕ) := (List.range n).map (fun i => (i, i))

theorem isPair_pairGenL : ∀ n, IsPair (pairGenL n)
  | 0 => isPair_nil
  | k + 1 => (pairStd.gen k).2

/-- A DBMS generator is one block, of a pair sequence generator. -/
theorem dstair_eq_blk (n : ℕ) :
    (List.range (n + 1)).map (fun i => (i, i - 1)) = blk (pairGenL n) := by
  rw [List.range_succ_eq_map, List.map_cons, blk, sh, pairGenL, List.map_map, List.map_map]
  simp [shc, Function.comp_def]

theorem good_of_isPair {M : List (ℕ × ℕ)} (h : IsPair M) (hne : M ≠ []) : Good M :=
  good_of_ctps (((isPair_iff M).mp h).resolve_left hne)

theorem hpos_of_isPair {M : List (ℕ × ℕ)} (h : IsPair M) (hne : M ≠ []) :
    ∀ i, 0 < (M[i]!).2 → parAt1 M i ≠ none :=
  fun i hi => parAt1_ne_none (good_of_isPair h hne) i hi

theorem isPair_expand2L {M : List (ℕ × ℕ)} (h : IsPair M) (N : ℕ) : IsPair (expand2L N M) :=
  pair_step_ok ⟨M, h⟩ N

theorem pairOrdL_expand2L_lt {M : List (ℕ × ℕ)} (h : IsPair M) (hne : M ≠ []) (N : ℕ) :
    pairOrdL (expand2L N M) < pairOrdL M :=
  pairOrdEval.val_lt ⟨M, h⟩ (pairL.step ⟨M, h⟩ N) ⟨hne, N, rfl⟩

instance instIsWellFoundedPairLTwoRow : IsWellFounded pairL.State pairL.Rel := ⟨pairL_wf⟩

/-- **The ordinal of a pair sequence is reached by its expansions.** -/
theorem pairOrdL_cofinal {M : List (ℕ × ℕ)} (h : IsPair M) (hne : M ≠ []) {c : Ordinal.{0}}
    (hc : c < pairOrdL M) : ∃ N, c ≤ pairOrdL (expand2L N M) := by
  have hr := rank_pairL_eq ⟨M, h⟩
  rw [Rewrite.rank_eq_iSup_nat (show ¬ pairL.halted ⟨M, h⟩ from hne)] at hr
  rw [← hr] at hc
  obtain ⟨N, hN⟩ := (Ordinal.lt_iSup_iff).mp hc
  refine ⟨N, ?_⟩
  rw [rank_pairL_eq] at hN
  exact Order.lt_succ_iff.mp hN

/-- **With no bad root, the ordinal is a successor.** -/
theorem pairOrdL_of_badRoot_none {M : List (ℕ × ℕ)} (h : IsPair M) (hne : M ≠ [])
    (hb : badRootL M = none) (N : ℕ) :
    pairOrdL M = Order.succ (pairOrdL (expand2L N M)) := by
  have hs : ∀ k, expand2L k M = expand2L N M := fun k => by rw [expand2L, hb, expand2L, hb]
  have := Rewrite.rank_succ_of_const_step (R := pairL) (a := ⟨M, h⟩)
    (b := pairL.step ⟨M, h⟩ N) hne (fun k => Subtype.ext (hs k))
  rw [rank_pairL_eq, rank_pairL_eq] at this
  exact this

theorem ltPS_append_cons : ∀ (X : List (ℕ × ℕ)) (y : ℕ × ℕ) (r : List (ℕ × ℕ)),
    Bijectivity.ltPS X (X ++ y :: r)
  | [], _, _ => trivial
  | _ :: X, y, r => Or.inr (Or.inr ⟨rfl, rfl, ltPS_append_cons X y r⟩)

/-- **With a bad root, a larger bracket gives a longer expansion.** -/
theorem expand2L_succ_prefix {M : List (ℕ × ℕ)} {p : ℕ} {b : Bool} (hb : badRootL M = some (p, b))
    (N : ℕ) : ∃ y r, expand2L (N + 1) M = expand2L N M ++ y :: r := by
  have hp := badRootL_lt hb
  rw [expand2L, hb, expand2L, hb]
  dsimp only
  rw [show (N + 1 + 1) * (M.length - 1 - p) = (N + 1) * (M.length - 1 - p) + (M.length - 1 - p)
    by ring, List.range_add, List.map_append, List.map_map, ← List.append_assoc]
  obtain ⟨s, hs⟩ : ∃ s, M.length - 1 - p = s + 1 := ⟨M.length - 1 - p - 1, by omega⟩
  rw [hs, List.range_succ_eq_map, List.map_cons]
  exact ⟨_, _, rfl⟩

theorem pairOrdL_expand2L_strictMono {M : List (ℕ × ℕ)} (h : IsPair M) {p : ℕ} {b : Bool}
    (hb : badRootL M = some (p, b)) (N : ℕ) :
    pairOrdL (expand2L N M) < pairOrdL (expand2L (N + 1) M) := by
  obtain ⟨y, r, he⟩ := expand2L_succ_prefix hb N
  have := ltPS_append_cons (expand2L N M) y r
  rw [← he] at this
  exact (ltPS_iff_pairOrdL_lt (isPair_expand2L h N) (isPair_expand2L h (N + 1))).mp this

/-! ### The standard forms are lists of blocks -/

/-- The pair sequences are standard and their ordinals do not increase. -/
def DForm (D : List (ℕ × ℕ)) : Prop :=
  ∃ Ms : List (List (ℕ × ℕ)), (∀ M ∈ Ms, IsPair M) ∧
    Ms.Pairwise (fun a b => pairOrdL b ≤ pairOrdL a) ∧ D = blocks Ms

theorem dform_gen (n : ℕ) : DForm ((List.range (n + 1)).map (fun i => (i, i - 1))) :=
  ⟨[pairGenL n], by simpa using isPair_pairGenL n, List.pairwise_singleton _ _,
    by rw [blocks_singleton, dstair_eq_blk]⟩

/-- **Expansion keeps the form.** -/
theorem dform_expand {D : List (ℕ × ℕ)} (h : DForm D) (N : ℕ) : DForm (expand2L N D) := by
  obtain ⟨Ms, hP, hS, rfl⟩ := h
  rcases List.eq_nil_or_concat Ms with rfl | ⟨Ms', M, rfl⟩
  · exact ⟨[], by simp, List.Pairwise.nil, by simp [expand2L_nil]⟩
  rw [List.concat_eq_append] at hP hS ⊢
  rw [expand2L_blocks_last]
  have hP' : ∀ M' ∈ Ms', IsPair M' := fun M' hM' => hP M' (by simp [hM'])
  have hM : IsPair M := hP M (by simp)
  obtain ⟨hS', -, hcross⟩ := List.pairwise_append.mp hS
  have hcross' : ∀ a ∈ Ms', pairOrdL M ≤ pairOrdL a := fun a ha => hcross a ha M (by simp)
  by_cases hne : M = []
  · subst hne
    refine ⟨Ms', hP', hS', ?_⟩
    rw [show blk [] = [(0, 0)] from rfl, expand2L_single, List.append_nil]
  have hlt := pairOrdL_expand2L_lt hM hne N
  cases hb : badRootL M with
  | none =>
    refine ⟨Ms' ++ List.replicate (N + 1) (expand2L N M), ?_, ?_, ?_⟩
    · intro M' hM'
      rcases List.mem_append.mp hM' with h1 | h1
      · exact hP' M' h1
      · rw [List.eq_of_mem_replicate h1]; exact isPair_expand2L hM N
    · refine List.pairwise_append.mpr ⟨hS', List.pairwise_replicate.mpr (Or.inr le_rfl), ?_⟩
      intro a ha b' hb'
      rw [List.eq_of_mem_replicate hb']
      exact le_trans hlt.le (hcross' a ha)
    · rw [expand2L_blk_none hne (hpos_of_isPair hM hne) hb, repN_blocks, blocks_append]
  | some pb =>
    obtain ⟨p, b⟩ := pb
    refine ⟨Ms' ++ [expand2L N M], ?_, ?_, ?_⟩
    · intro M' hM'
      rcases List.mem_append.mp hM' with h1 | h1
      · exact hP' M' h1
      · rw [List.mem_singleton.mp h1]; exact isPair_expand2L hM N
    · refine List.pairwise_append.mpr ⟨hS', List.pairwise_singleton _ _, ?_⟩
      intro a ha b' hb'
      rw [List.mem_singleton.mp hb']
      exact le_trans hlt.le (hcross' a ha)
    · rw [expand2L_blk_some (hpos_of_isPair hM hne) hb, blocks_append, blocks_singleton]

/-- **Every standard form of two-row DBMS is a list of blocks of standard pair
sequences whose ordinals do not increase.** -/
theorem dform_of_dreach2 {D : List (ℕ × ℕ)} (h : DReach2 D) : DForm D := by
  obtain ⟨A, hA, rfl⟩ := h
  induction hA with
  | init n => rw [entries2_dstair]; exact dform_gen n
  | step N _ ih => rw [entries2_expand]; exact dform_expand ih N


/-! ### Sums of powers of `ω` -/

open Ordinal in
/-- `ω^x₀ + ω^x₁ + ⋯`. -/
noncomputable def oSum (xs : List Ordinal.{0}) : Ordinal.{0} := (xs.map (fun x => ω ^ x)).sum

open Ordinal

@[simp] theorem oSum_nil : oSum [] = 0 := rfl

theorem oSum_cons (x : Ordinal.{0}) (xs : List Ordinal.{0}) :
    oSum (x :: xs) = ω ^ x + oSum xs := by
  simp [oSum]

theorem oSum_append (xs ys : List Ordinal.{0}) : oSum (xs ++ ys) = oSum xs + oSum ys := by
  simp [oSum, List.sum_append]

theorem oSum_singleton (x : Ordinal.{0}) : oSum [x] = ω ^ x := by simp [oSum]

theorem oSum_replicate (x : Ordinal.{0}) : ∀ n : ℕ, oSum (List.replicate n x) = ω ^ x * n
  | 0 => by simp
  | n + 1 => by
    rw [List.replicate_succ', oSum_append, oSum_replicate x n, oSum_singleton, Nat.cast_succ,
      mul_add_one]

theorem opow_le_oSum {xs : List Ordinal.{0}} {x : Ordinal.{0}} (h : x ∈ xs) :
    ω ^ x ≤ oSum xs := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
    rw [oSum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_self_add
    · exact le_trans (ih h) le_add_self

theorem oSum_lt_of_principal {P : Ordinal.{0}} (hP : Ordinal.IsPrincipal (· + ·) P)
    (h0 : 0 < P) : ∀ xs : List Ordinal.{0}, (∀ x ∈ xs, ω ^ x < P) → oSum xs < P
  | [], _ => h0
  | x :: xs, h => by
    rw [oSum_cons]
    exact hP (h x (by simp)) (oSum_lt_of_principal hP h0 xs (fun y hy => h y (by simp [hy])))

theorem oSum_lt_opow {c : Ordinal.{0}} (xs : List Ordinal.{0}) (h : ∀ x ∈ xs, x < c) :
    oSum xs < ω ^ c :=
  oSum_lt_of_principal (isPrincipal_add_omega0_opow c) (opow_pos c omega0_pos) xs
    (fun x hx => (opow_lt_opow_iff_right one_lt_omega0).mpr (h x hx))

/-- **A non-increasing list is determined by its sum** (uniqueness of Cantor
normal form). -/
theorem oSum_inj : ∀ {xs ys : List Ordinal.{0}}, xs.Pairwise (fun a b => b ≤ a) →
    ys.Pairwise (fun a b => b ≤ a) → oSum xs = oSum ys → xs = ys
  | [], [], _, _, _ => rfl
  | [], y :: ys, _, _, h => by
    rw [oSum_nil, oSum_cons] at h
    exact absurd h.symm (ne_of_gt (lt_of_lt_of_le (opow_pos y omega0_pos) le_self_add))
  | x :: xs, [], _, _, h => by
    rw [oSum_nil, oSum_cons] at h
    exact absurd h (ne_of_gt (lt_of_lt_of_le (opow_pos x omega0_pos) le_self_add))
  | x :: xs, y :: ys, hx, hy, h => by
    have bound : ∀ (z : Ordinal.{0}) (zs : List Ordinal.{0}), (z :: zs).Pairwise (fun a b => b ≤ a) →
        oSum (z :: zs) < ω ^ Order.succ z := fun z zs hz =>
      oSum_lt_opow _ (fun w hw => Order.lt_succ_iff.mpr (by
        rcases List.mem_cons.mp hw with rfl | hw
        · exact le_rfl
        · exact List.rel_of_pairwise_cons hz hw))
    have hxy : x = y := by
      rcases lt_trichotomy x y with hlt | heq | hlt
      · exfalso
        have h1 := bound x xs hx
        have h2 : ω ^ Order.succ x ≤ oSum (y :: ys) :=
          le_trans (opow_le_opow_right omega0_pos (Order.succ_le_of_lt hlt))
            (opow_le_oSum (by simp))
        rw [h] at h1
        exact absurd h1 (not_lt.mpr h2)
      · exact heq
      · exfalso
        have h1 := bound y ys hy
        have h2 : ω ^ Order.succ y ≤ oSum (x :: xs) :=
          le_trans (opow_le_opow_right omega0_pos (Order.succ_le_of_lt hlt))
            (opow_le_oSum (by simp))
        rw [← h] at h1
        exact absurd h1 (not_lt.mpr h2)
    subst hxy
    rw [oSum_cons, oSum_cons] at h
    rw [oSum_inj (List.Pairwise.of_cons hx) (List.Pairwise.of_cons hy)
      ((add_right_inj _).mp h)]

/-- **Every ordinal is such a sum** (Cantor normal form). -/
theorem exists_oSum (β : Ordinal.{0}) :
    ∃ es : List Ordinal.{0}, es.Pairwise (fun a b => b ≤ a) ∧ oSum es = β := by
  induction β using WellFoundedLT.induction with
  | _ β ih =>
    rcases eq_or_ne β 0 with rfl | hβ
    · exact ⟨[], List.Pairwise.nil, rfl⟩
    set e := Ordinal.log ω β
    have hle : ω ^ e ≤ β := Ordinal.opow_log_le_self ω hβ
    have hlt : β < ω ^ Order.succ e := Ordinal.lt_opow_succ_log_self one_lt_omega0 β
    set r := β - ω ^ e
    have hβr : ω ^ e + r = β := Ordinal.add_sub_cancel_of_le hle
    have hrle : r ≤ β := by rw [← hβr]; exact le_add_self
    have hr : r < β := by
      refine lt_of_le_of_ne hrle (fun hrb => ?_)
      rw [hrb] at hβr
      have := (Ordinal.add_eq_right_iff_mul_omega0_le).mp hβr
      rw [← Ordinal.opow_succ] at this
      exact absurd hlt (not_lt.mpr this)
    obtain ⟨es, hes, hsum⟩ := ih r hr
    refine ⟨e :: es, List.pairwise_cons.mpr ⟨fun f hf => ?_, hes⟩, by rw [oSum_cons, hsum, hβr]⟩
    have h1 : ω ^ f < ω ^ Order.succ e :=
      lt_of_le_of_lt (le_trans (hsum ▸ opow_le_oSum hf) hrle) hlt
    exact Order.lt_succ_iff.mp ((opow_lt_opow_iff_right one_lt_omega0).mp h1)

/-! ### The ordinal of a two-row DBMS matrix -/

/-- **The ordinal of a two-row DBMS matrix**: `ω^(o M₀) + ω^(o M₁) + ⋯`, where
`M₀, M₁, …` are the pair sequences of its blocks and `o` is the ordinal of
pair sequences (`pairOrdL`). -/
noncomputable def dOrdL (D : List (ℕ × ℕ)) : Ordinal.{0} := oSum ((blocksOf D).map pairOrdL)

theorem dOrdL_blocks (Ms : List (List (ℕ × ℕ))) :
    dOrdL (blocks Ms) = oSum (Ms.map pairOrdL) := by
  rw [dOrdL, blocksOf_blocks]

theorem dOrdL_nil : dOrdL [] = 0 := by
  rw [← blocks_nil, dOrdL_blocks]; rfl

theorem dOrdL_blk (M : List (ℕ × ℕ)) : dOrdL (blk M) = ω ^ pairOrdL M := by
  rw [← blocks_singleton, dOrdL_blocks]; simp [oSum_singleton]

theorem pairOrdL_ne_zero {M : List (ℕ × ℕ)} (hne : M ≠ []) : pairOrdL M ≠ 0 :=
  ne_of_gt (pairOrdL_pos hne)

/-- The ordinal of a pair sequence whose last step has a bad root is a limit. -/
theorem pairOrdL_isSuccLimit {M : List (ℕ × ℕ)} (h : IsPair M) (hne : M ≠ []) {p : ℕ} {b : Bool}
    (hb : badRootL M = some (p, b)) : Order.IsSuccLimit (pairOrdL M) := by
  rw [Ordinal.isSuccLimit_iff]
  refine ⟨pairOrdL_ne_zero hne, Order.isSuccPrelimit_iff_succ_lt.mpr (fun c hc => ?_)⟩
  obtain ⟨N, hN⟩ := pairOrdL_cofinal h hne hc
  exact lt_of_le_of_lt (Order.succ_le_of_lt (lt_of_le_of_lt hN
    (pairOrdL_expand2L_strictMono h hb N))) (pairOrdL_expand2L_lt h hne (N + 1))

/-- **One step lowers the ordinal, and the steps reach every smaller
ordinal.** -/
theorem dOrdL_step {D : List (ℕ × ℕ)} (hD : DForm D) (hne : D ≠ []) :
    (∀ N, dOrdL (expand2L N D) < dOrdL D) ∧
      ∀ β < dOrdL D, ∃ N, β ≤ dOrdL (expand2L N D) := by
  obtain ⟨Ms, hP, hS, rfl⟩ := hD
  rcases List.eq_nil_or_concat Ms with rfl | ⟨Ms', M, rfl⟩
  · exact absurd rfl hne
  rw [List.concat_eq_append] at hP hS ⊢
  have hM : IsPair M := hP M (by simp)
  set o' := oSum (Ms'.map pairOrdL)
  have hD : dOrdL (blocks (Ms' ++ [M])) = o' + ω ^ pairOrdL M := by
    rw [dOrdL_blocks, List.map_append, oSum_append]; simp [oSum_singleton, o']
  have hE : ∀ N X, expand2L N (blocks (Ms' ++ [M])) = blocks Ms' ++ X →
      ∀ Xs, X = blocks Xs → dOrdL (expand2L N (blocks (Ms' ++ [M])))
        = o' + oSum (Xs.map pairOrdL) := by
    intro N X hX Xs hXs
    rw [hX, hXs, ← blocks_append, dOrdL_blocks, List.map_append, oSum_append]
  -- the general shape of the argument after the prefix
  have key : ∀ (Y : ℕ → Ordinal.{0}), (∀ N, dOrdL (expand2L N (blocks (Ms' ++ [M]))) = o' + Y N) →
      (∀ N, Y N < ω ^ pairOrdL M) → (∀ γ < ω ^ pairOrdL M, ∃ N, γ ≤ Y N) →
      (∀ N, dOrdL (expand2L N (blocks (Ms' ++ [M]))) < dOrdL (blocks (Ms' ++ [M]))) ∧
      ∀ β < dOrdL (blocks (Ms' ++ [M])), ∃ N, β ≤ dOrdL (expand2L N (blocks (Ms' ++ [M]))) := by
    intro Y hY hlt hcof
    refine ⟨fun N => ?_, fun β hβ => ?_⟩
    · rw [hY, hD]; exact (add_lt_add_iff_left o').mpr (hlt N)
    · rw [hD] at hβ
      rcases lt_or_ge β o' with h1 | h1
      · exact ⟨0, by rw [hY]; exact le_trans h1.le le_self_add⟩
      · have hγ : β - o' < ω ^ pairOrdL M := by
          rw [← add_lt_add_iff_left o', Ordinal.add_sub_cancel_of_le h1]; exact hβ
        obtain ⟨N, hN⟩ := hcof _ hγ
        refine ⟨N, ?_⟩
        rw [hY, ← Ordinal.add_sub_cancel_of_le h1]
        exact add_le_add_right hN o'
  by_cases hMe : M = []
  · subst hMe
    have hX : ∀ N, expand2L N (blocks (Ms' ++ [[]])) = blocks Ms' ++ [] := fun N => by
      rw [expand2L_blocks_last, show blk [] = [(0, 0)] from rfl, expand2L_single]
    refine key (fun _ => 0) (fun N => by rw [hE N [] (hX N) [] rfl]; simp) (fun N => ?_)
      (fun γ hγ => ⟨0, ?_⟩)
    · rw [pairOrdL_nil, opow_zero]; exact zero_lt_one
    · rw [pairOrdL_nil, opow_zero, Order.lt_one_iff] at hγ; rw [hγ]
  have hpos := hpos_of_isPair hM hMe
  cases hb : badRootL M with
  | none =>
    have hX : ∀ N, expand2L N (blocks (Ms' ++ [M])) =
        blocks Ms' ++ blocks (List.replicate (N + 1) (expand2L N M)) := fun N => by
      rw [expand2L_blocks_last, expand2L_blk_none hMe hpos hb, repN_blocks]
    have hconst : ∀ N, expand2L N M = expand2L 0 M := fun N => by
      rw [expand2L, hb, expand2L, hb]
    set b := pairOrdL (expand2L 0 M)
    have hsucc : pairOrdL M = Order.succ b := pairOrdL_of_badRoot_none hM hMe hb 0
    refine key (fun N => ω ^ b * ((N + 1 : ℕ) : Ordinal.{0}))
      (fun N => by
        rw [hE N _ (hX N) _ rfl, List.map_replicate, oSum_replicate, hconst N])
      (fun N => ?_) (fun γ hγ => ?_)
    · rw [hsucc, Ordinal.opow_succ]
      exact (mul_lt_mul_iff_right₀ (opow_pos b omega0_pos)).mpr (natCast_lt_omega0 _)
    · rw [hsucc, Ordinal.opow_succ] at hγ
      obtain ⟨c, hc, hγc⟩ := (Ordinal.lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).mp hγ
      obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hc
      refine ⟨n, le_trans hγc.le ?_⟩
      exact mul_le_mul_right (by exact_mod_cast Nat.le_succ n) _
  | some pb =>
    obtain ⟨p, bb⟩ := pb
    have hX : ∀ N, expand2L N (blocks (Ms' ++ [M])) = blocks Ms' ++ blocks [expand2L N M] :=
      fun N => by rw [expand2L_blocks_last, expand2L_blk_some hpos hb, blocks_singleton]
    refine key (fun N => ω ^ pairOrdL (expand2L N M))
      (fun N => by rw [hE N _ (hX N) _ rfl]; simp [oSum_singleton])
      (fun N => (opow_lt_opow_iff_right one_lt_omega0).mpr (pairOrdL_expand2L_lt hM hMe N))
      (fun γ hγ => ?_)
    obtain ⟨c, hc, hγc⟩ := (Ordinal.lt_opow_of_isSuccLimit omega0_ne_zero
      (pairOrdL_isSuccLimit hM hMe hb)).mp hγ
    obtain ⟨N, hN⟩ := pairOrdL_cofinal hM hMe hc
    exact ⟨N, le_trans hγc.le (opow_le_opow_right omega0_pos hN)⟩

theorem dform_state (l : DbmsState2) : DForm l.1 := dform_of_dreach2 l.2

/-- **The ordinal translation of two-row DBMS.** -/
noncomputable def dbmsL2OrdEval : Eval dbmsL2 (· < · : Ordinal.{0} → Ordinal.{0} → Prop) where
  val l := dOrdL l.1
  val_lt a b h := by
    obtain ⟨hna, N, rfl⟩ := h
    exact (dOrdL_step (dform_state a) hna).1 N

theorem dbmsL2OrdEval_val (l : DbmsState2) : dbmsL2OrdEval.val l = dOrdL l.1 := rfl

/-- **Two-row DBMS on the entries is well founded.** -/
theorem dbmsL2_wf : dbmsL2.WF := dbmsL2OrdEval.wf Ordinal.lt_wf

instance instIsWellFoundedDbmsL2 : IsWellFounded dbmsL2.State dbmsL2.Rel := ⟨dbmsL2_wf⟩

/-- **The rank of a two-row DBMS matrix is its ordinal.** -/
theorem rank_dbmsL2_eq (l : dbmsL2.State) :
    IsWellFounded.rank dbmsL2.Rel l = dOrdL l.1 := by
  induction l using WellFounded.induction dbmsL2_wf with
  | _ l IH =>
    refine le_antisymm (Eval.rank_le dbmsL2OrdEval l) ?_
    refine le_of_forall_lt (fun β hβ => ?_)
    have hne : l.1 ≠ [] := by
      intro h
      rw [h, dOrdL_nil] at hβ
      exact absurd hβ (not_lt_zero)
    obtain ⟨N, hN⟩ := (dOrdL_step (dform_state l) hne).2 β hβ
    have hrel : dbmsL2.Rel (dbmsL2.step l N) l := ⟨hne, N, rfl⟩
    calc β ≤ dOrdL (dbmsL2.step l N).1 := hN
      _ = IsWellFounded.rank dbmsL2.Rel (dbmsL2.step l N) := (IH _ hrel).symm
      _ < IsWellFounded.rank dbmsL2.Rel l := IsWellFounded.rank_lt_of_rel hrel

/-! ### Injective -/

theorem pairOrdL_inj {M M' : List (ℕ × ℕ)} (h : IsPair M) (h' : IsPair M')
    (he : pairOrdL M = pairOrdL M') : M = M' :=
  congrArg Subtype.val (pairOrd_injective (a₁ := ⟨M, h⟩) (a₂ := ⟨M', h'⟩) he)

theorem map_pairOrdL_inj : ∀ {Ms Ms' : List (List (ℕ × ℕ))}, (∀ M ∈ Ms, IsPair M) →
    (∀ M ∈ Ms', IsPair M) → Ms.map pairOrdL = Ms'.map pairOrdL → Ms = Ms'
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | M :: Ms, M' :: Ms', hP, hP', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [pairOrdL_inj (hP M (by simp)) (hP' M' (by simp)) h.1,
      map_pairOrdL_inj (fun N hN => hP N (by simp [hN])) (fun N hN => hP' N (by simp [hN])) h.2]

/-- **Two matrices of the form with the same ordinal are the same matrix.** -/
theorem dOrdL_inj {D D' : List (ℕ × ℕ)} (hD : DForm D) (hD' : DForm D')
    (h : dOrdL D = dOrdL D') : D = D' := by
  obtain ⟨Ms, hP, hS, rfl⟩ := hD
  obtain ⟨Ms', hP', hS', rfl⟩ := hD'
  rw [dOrdL_blocks, dOrdL_blocks] at h
  have := oSum_inj (List.pairwise_map.mpr hS) (List.pairwise_map.mpr hS') h
  rw [map_pairOrdL_inj hP hP' this]

/-- **Distinct two-row DBMS matrices name distinct ordinals.** -/
theorem dbmsL2OrdEval_injective {a b : DbmsState2}
    (h : dbmsL2OrdEval.val a = dbmsL2OrdEval.val b) : a = b :=
  Subtype.ext (dOrdL_inj (dform_state a) (dform_state b) h)


/-! ### `ψ_0(Ω_ω)` is closed under `x ↦ ω^x` -/

section Closure

open Googology.Notation.ExBuchholz.Ord

theorem natCast_mem_CSet {a : Ordinal.{0}} (ha : 0 < a) : ∀ k : ℕ, (k : Ordinal.{0}) ∈ CSet 0 a
  | 0 => by simpa using CSet.zero_mem 0 a
  | k + 1 => by
    rw [Nat.cast_succ]
    refine CSet.add_mem (natCast_mem_CSet ha k) ?_
    have := CSet.psi_mem (v := 0) (u := 0) ha (CSet.zero_mem 0 a) (CSet.zero_mem 0 a)
    rwa [psi_zero_arg, Omega_zero] at this

theorem Omega_mem_CSet {a : Ordinal.{0}} (ha : 0 < a) (k : ℕ) : Ω_ (k : Ordinal.{0}) ∈ CSet 0 a := by
  have := CSet.psi_mem (v := 0) ha (natCast_mem_CSet ha k) (CSet.zero_mem 0 a)
  rwa [psi_zero_arg] at this

theorem exists_lt_Omega_nat {e : Ordinal.{0}} (h : e < Ω_ ω) : ∃ k : ℕ, e < Ω_ (k : Ordinal.{0}) := by
  rw [Omega_of_ne_zero omega0_ne_zero] at h
  obtain ⟨c, hc, hec⟩ := (Ordinal.isNormal_omega.lt_iff_exists_lt isSuccLimit_omega0).mp h
  obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hc
  refine ⟨n + 1, lt_of_lt_of_le hec ?_⟩
  rw [Omega_of_ne_zero (by exact_mod_cast Nat.succ_ne_zero n)]
  exact Ordinal.omega_le_omega.mpr (by exact_mod_cast Nat.le_succ n)

theorem Omega_nat_mono {m n : ℕ} (h : m ≤ n) : Ω_ (m : Ordinal.{0}) ≤ Ω_ (n : Ordinal.{0}) :=
  Omega_mono (by exact_mod_cast h)

/-- **`C_0(Ω_ω)` is the union of the `C_0(Ω_k)`**: a derivation uses finitely
many arguments, each below some `Ω_k`. -/
theorem exists_mem_CSet_Omega_nat {x : Ordinal.{0}} (hx : x ∈ CSet 0 (Ω_ ω)) :
    ∃ k : ℕ, x ∈ CSet 0 (Ω_ (k : Ordinal.{0})) := by
  induction hx with
  | @small y h => exact ⟨0, mem_CSet_of_lt_Omega h⟩
  | @add p q _ _ ihp ihq =>
    obtain ⟨k1, h1⟩ := ihp
    obtain ⟨k2, h2⟩ := ihq
    refine ⟨max k1 k2, CSet.add_mem ?_ ?_⟩
    · exact CSet_mono 0 (Omega_nat_mono (le_max_left k1 k2)) h1
    · exact CSet_mono 0 (Omega_nat_mono (le_max_right k1 k2)) h2
  | @coll u e _ _ ihu ihe =>
    obtain ⟨k1, h1⟩ := ihu
    obtain ⟨k2, h2⟩ := ihe
    obtain ⟨k3, h3⟩ := exists_lt_Omega_nat e.2
    refine ⟨max k1 (max k2 k3), ?_⟩
    show psi e.1 u ∈ _
    refine CSet.psi_mem (lt_of_lt_of_le h3 (Omega_nat_mono (by omega))) ?_ ?_
    · exact CSet_mono 0 (Omega_nat_mono (by omega)) h1
    · exact CSet_mono 0 (Omega_nat_mono (by omega)) h2

/-- An additively principal ordinal above every `ω^y` with `y < x` is at
least `ω^x`. -/
theorem opow_le_of_principal {F x : Ordinal.{0}} (hF : Ordinal.IsPrincipal (· + ·) F)
    (hF0 : 0 < F) (h : ∀ y < x, ω ^ y < F) : ω ^ x ≤ F := by
  rcases Ordinal.isPrincipal_add_iff_zero_or_omega0_opow.mp hF with h0 | ⟨g, rfl⟩
  · exact absurd h0 (ne_of_gt hF0)
  · refine opow_le_opow_right omega0_pos (le_of_not_gt (fun hg => ?_))
    exact absurd (h g hg) (lt_irrefl _)

/-- **`ω^x ≤ ψ_0(Ω_k + x)`** for a countable `x` in `C_0(Ω_k)`. -/
theorem opow_le_psi_Omega_add (k : ℕ) : ∀ x : Ordinal.{0}, x ∈ CSet 0 (Ω_ (k : Ordinal.{0})) →
    x.card ≤ Cardinal.aleph 0 → ω ^ x ≤ psi (Ω_ (k : Ordinal.{0}) + x) 0 := by
  intro x
  induction x using WellFoundedLT.induction with
  | _ x ih =>
    intro hx hc
    refine opow_le_of_principal (isPrincipal_add_psi _ 0) (psi_pos _ 0) (fun y hy => ?_)
    have hyC : y ∈ CSet 0 (Ω_ (k : Ordinal.{0})) := mem_CSet_of_le hx y hy.le hc
    have hyc : y.card ≤ Cardinal.aleph 0 := le_trans (Ordinal.card_le_card hy.le) hc
    refine lt_of_le_of_lt (ih y hy hyC hyc) (lt_psi_of_mem ?_ (card_psi_le _ 0))
    have hpos : 0 < Ω_ (k : Ordinal.{0}) + x := lt_of_lt_of_le (Omega_pos _) le_self_add
    refine CSet.psi_mem ((add_lt_add_iff_left _).mpr hy) (CSet.zero_mem 0 _) ?_
    exact CSet.add_mem (Omega_mem_CSet hpos k) (CSet_mono 0 le_self_add hyC)

/-- **`ω^x < ψ_0(Ω_ω)` for every `x < ψ_0(Ω_ω)`.** -/
theorem opow_lt_psi_Omega_omega {x : Ordinal.{0}} (h : x < psi (Ω_ ω) 0) :
    ω ^ x < psi (Ω_ ω) 0 := by
  have hx : x ∈ CSet 0 (Ω_ ω) := mem_CSet_of_lt_psi h
  have hc : x.card ≤ Cardinal.aleph 0 :=
    le_trans (Ordinal.card_le_card h.le) (by simpa using card_psi_le (Ω_ ω) 0)
  obtain ⟨k, hk⟩ := exists_mem_CSet_Omega_nat hx
  refine lt_of_le_of_lt (opow_le_psi_Omega_add k x hk hc) (lt_psi_of_mem ?_ (card_psi_le _ 0))
  have hΩ : Ω_ (k : Ordinal.{0}) < Ω_ ω := by
    have h1 : Ω_ (k : Ordinal.{0}) < Ω_ ((k : Ordinal.{0}) + 1) := by
      have := psi_lt_Omega_succ 0 (k : Ordinal.{0})
      rwa [psi_zero_arg] at this
    exact lt_of_lt_of_le h1 (Omega_mono (by
      rw [← Nat.cast_succ]; exact (natCast_lt_omega0 _).le))
  have hxΩ : x < Ω_ ω := lt_of_lt_of_le (lt_trans h (psi_zero_lt_Omega_one _))
    (Omega_mono one_lt_omega0.le)
  refine CSet.psi_mem (isPrincipal_add_Omega ω hΩ hxΩ) (CSet.zero_mem 0 _) ?_
  exact CSet.add_mem (Omega_mem_CSet (Omega_pos ω) k) hx

end Closure

theorem isPrincipal_add_val_psiOmegaOmega :
    Ordinal.IsPrincipal (· + ·) (Notation.ExBuchholz.Term.val psiOmegaOmega) := by
  rw [val_psiOmegaOmega]
  exact Notation.ExBuchholz.Ord.isPrincipal_add_psi _ 0

theorem opow_lt_val_psiOmegaOmega {x : Ordinal.{0}}
    (h : x < Notation.ExBuchholz.Term.val psiOmegaOmega) :
    ω ^ x < Notation.ExBuchholz.Term.val psiOmegaOmega := by
  rw [val_psiOmegaOmega] at h ⊢
  exact opow_lt_psi_Omega_omega h

/-! ### Surjective -/

theorem pairOrdL_lt_val {M : List (ℕ × ℕ)} (h : IsPair M) :
    pairOrdL M < Notation.ExBuchholz.Term.val psiOmegaOmega := by
  have : pairOrdEval.val ⟨M, h⟩ ∈ Set.range pairOrdEval.val := ⟨_, rfl⟩
  rw [range_pairOrd] at this
  exact this

theorem exists_pair_of_lt {e : Ordinal.{0}} (h : e < Notation.ExBuchholz.Term.val psiOmegaOmega) :
    ∃ M, IsPair M ∧ pairOrdL M = e := by
  rw [← Set.mem_Iio, ← range_pairOrd] at h
  obtain ⟨l, hl⟩ := h
  exact ⟨l.1, l.2, hl⟩

theorem exists_pairs_of_lt : ∀ es : List Ordinal.{0},
    (∀ e ∈ es, e < Notation.ExBuchholz.Term.val psiOmegaOmega) →
    ∃ Ms : List (List (ℕ × ℕ)), (∀ M ∈ Ms, IsPair M) ∧ Ms.map pairOrdL = es
  | [], _ => ⟨[], by simp, rfl⟩
  | e :: es, h => by
    obtain ⟨M, hM, hMe⟩ := exists_pair_of_lt (h e (by simp))
    obtain ⟨Ms, hMs, hMse⟩ := exists_pairs_of_lt es (fun f hf => h f (by simp [hf]))
    exact ⟨M :: Ms, by simp [hM]; exact hMs, by simp [hMe, hMse]⟩

/-- **The block of a standard pair sequence is a standard two-row DBMS
matrix**: a pair sequence step is a DBMS step on its block. -/
theorem dreach2_blk {M : List (ℕ × ℕ)} (h : IsPair M) : DReach2 (blk M) := by
  obtain ⟨A, hA, rfl⟩ := h
  induction hA with
  | init n =>
    rw [entries2_stair, show (List.range (n + 1)).map (fun i => (i, i)) = pairGenL (n + 1)
      from rfl, ← dstair_eq_blk]
    exact dreach2_gen (n + 1)
  | @step A N hA ih =>
    rw [entries2_expand]
    by_cases hne : entries2 A = []
    · rw [hne, expand2L_nil]; rw [hne] at ih; exact ih
    have hP : IsPair (entries2 A) := ⟨A, hA, rfl⟩
    have hpos := hpos_of_isPair hP hne
    cases hb : badRootL (entries2 A) with
    | none =>
      have h1 := expand2L_blk_none hne hpos hb 0
      rw [show repN (0 + 1) (blk (expand2L 0 (entries2 A))) = blk (expand2L 0 (entries2 A))
        from rfl] at h1
      rw [show expand2L N (entries2 A) = expand2L 0 (entries2 A) by
        rw [expand2L, hb, expand2L, hb], ← h1]
      exact dreach2_expand ih 0
    | some pb =>
      obtain ⟨p, b⟩ := pb
      rw [← expand2L_blk_some hpos hb]
      exact dreach2_expand ih N

/-- **A matrix of the form is reached from any standard matrix with a larger
or equal ordinal.** -/
theorem dreach2_of_le : ∀ (E : DbmsState2) {D : List (ℕ × ℕ)}, DForm D →
    dOrdL D ≤ dOrdL E.1 → DReach2 D := by
  intro E
  induction E using WellFounded.induction dbmsL2_wf with
  | _ E IH =>
    intro D hD hle
    rcases hle.lt_or_eq with hlt | heq
    · have hne : E.1 ≠ [] := by
        intro h
        rw [h, dOrdL_nil] at hlt
        exact absurd hlt not_lt_zero
      obtain ⟨N, hN⟩ := (dOrdL_step (dform_state E) hne).2 _ hlt
      exact IH (dbmsL2.step E N) ⟨hne, N, rfl⟩ hD hN
    · rw [dOrdL_inj hD (dform_state E) heq]
      exact E.2

/-- The ordinal of a matrix of the form is below `ψ_0(Ω_ω)`. -/
theorem dOrdL_lt_val {D : List (ℕ × ℕ)} (hD : DForm D) :
    dOrdL D < Notation.ExBuchholz.Term.val psiOmegaOmega := by
  obtain ⟨Ms, hP, -, rfl⟩ := hD
  rw [dOrdL_blocks]
  refine oSum_lt_of_principal isPrincipal_add_val_psiOmegaOmega
    (lt_of_lt_of_le omega0_pos omega0_le_val_psiOmegaOmega) _ (fun x hx => ?_)
  obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hx
  exact opow_lt_val_psiOmegaOmega (pairOrdL_lt_val (hP M hM))

/-- **The standard two-row DBMS matrices are exactly the lists of blocks of
standard pair sequences with non-increasing ordinals.** -/
theorem dreach2_iff_dform (D : List (ℕ × ℕ)) : DReach2 D ↔ DForm D := by
  refine ⟨dform_of_dreach2, fun hD => ?_⟩
  obtain ⟨M, hM, hMe⟩ := exists_pair_of_lt (dOrdL_lt_val hD)
  refine dreach2_of_le ⟨blk M, dreach2_blk hM⟩ hD ?_
  show dOrdL D ≤ dOrdL (blk M)
  rw [dOrdL_blk, hMe]
  exact Ordinal.right_le_opow _ one_lt_omega0

/-- **The ordinals of the two-row DBMS matrices are exactly the ordinals below
`ψ_0(Ω_ω)`.** -/
theorem dbmsL2Ord_image :
    {α | ∃ a, dbmsL2Std.Standard a ∧ dbmsL2OrdEval.val a = α}
      = Set.Iio (Notation.ExBuchholz.Term.val psiOmegaOmega) := by
  ext α
  constructor
  · rintro ⟨a, -, rfl⟩
    exact dOrdL_lt_val (dform_state a)
  · intro hα
    obtain ⟨es, hes, hsum⟩ := exists_oSum α
    have hlt : ∀ e ∈ es, e < Notation.ExBuchholz.Term.val psiOmegaOmega := fun e he =>
      lt_of_le_of_lt (le_trans (Ordinal.right_le_opow e one_lt_omega0)
        (hsum ▸ opow_le_oSum he)) hα
    obtain ⟨Ms, hP, hMs⟩ := exists_pairs_of_lt es hlt
    have hD : DForm (blocks Ms) := ⟨Ms, hP, List.pairwise_map.mp (hMs ▸ hes), rfl⟩
    refine ⟨⟨blocks Ms, (dreach2_iff_dform _).mpr hD⟩, trivial, ?_⟩
    show dOrdL (blocks Ms) = α
    rw [dOrdL_blocks, hMs, hsum]


/-! ### Order-preserving -/

theorem ltPS_append_left : ∀ (X A B : List (ℕ × ℕ)),
    Bijectivity.ltPS (X ++ A) (X ++ B) ↔ Bijectivity.ltPS A B
  | [], _, _ => Iff.rfl
  | p :: X, A, B => by
    show (p.1 < p.1 ∨ (p.1 = p.1 ∧ p.2 < p.2) ∨ (p.1 = p.1 ∧ p.2 = p.2 ∧
      Bijectivity.ltPS (X ++ A) (X ++ B))) ↔ _
    rw [ltPS_append_left X A B]
    simp

/-- The list is empty or starts a block. -/
def StartsZero (X : List (ℕ × ℕ)) : Prop := ∀ x ∈ X.head?, x.1 = 0

theorem startsZero_blocks : ∀ Rs : List (List (ℕ × ℕ)), StartsZero (blocks Rs)
  | [] => by simp [StartsZero]
  | R :: Rs => by
    rw [blocks_cons]
    intro x hx
    simp [blk] at hx
    rw [← hx]

/-- **Two different raised pair sequences, each followed by the start of a
block, compare as the pair sequences do.** -/
theorem ltPS_of_sh : ∀ (M1 M2 X Y : List (ℕ × ℕ)), StartsZero Y → M1 ≠ M2 →
    Bijectivity.ltPS (sh M1 ++ X) (sh M2 ++ Y) → Bijectivity.ltPS M1 M2
  | [], [], _, _, _, hne, _ => absurd rfl hne
  | [], _ :: _, _, _, _, _, _ => trivial
  | p :: M1, [], X, Y, hY, _, h => by
    cases Y with
    | nil => exact absurd h (by simp [sh, Bijectivity.ltPS])
    | cons y Y =>
      have hy : y.1 = 0 := hY y (by simp)
      simp only [sh, List.map_cons, List.cons_append, List.map_nil, List.nil_append,
        Bijectivity.ltPS, shc, hy] at h
      omega
  | p :: M1, q :: M2, X, Y, hY, hne, h => by
    simp only [sh, List.map_cons, List.cons_append, Bijectivity.ltPS, shc] at h
    show p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2) ∨ (p.1 = q.1 ∧ p.2 = q.2 ∧ Bijectivity.ltPS M1 M2)
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl ⟨by omega, h2⟩)
    · have hp : p = q := Prod.ext (by omega) h2
      subst hp
      have hne' : M1 ≠ M2 := fun he => hne (by rw [he])
      exact Or.inr (Or.inr ⟨rfl, rfl, ltPS_of_sh M1 M2 X Y hY hne' h3⟩)

theorem oSum_lt_succ_head {x : Ordinal.{0}} {xs : List Ordinal.{0}}
    (h : (x :: xs).Pairwise (fun a b => b ≤ a)) : oSum (x :: xs) < ω ^ Order.succ x :=
  oSum_lt_opow _ (fun w hw => Order.lt_succ_iff.mpr (by
    rcases List.mem_cons.mp hw with rfl | hw
    · exact le_rfl
    · exact List.rel_of_pairwise_cons h hw))

/-- **The lexicographic order on the matrices is the order of the ordinals**,
one direction. -/
theorem dOrdL_lt_of_ltPS : ∀ {Ms1 Ms2 : List (List (ℕ × ℕ))}, (∀ M ∈ Ms1, IsPair M) →
    (∀ M ∈ Ms2, IsPair M) → Ms1.Pairwise (fun a b => pairOrdL b ≤ pairOrdL a) →
    Bijectivity.ltPS (blocks Ms1) (blocks Ms2) → dOrdL (blocks Ms1) < dOrdL (blocks Ms2)
  | [], [], _, _, _, h => absurd h (by simp [Bijectivity.ltPS])
  | [], M :: Ms, _, _, _, _ => by
    rw [dOrdL_blocks, dOrdL_blocks, List.map_cons, oSum_cons]
    exact lt_of_lt_of_le (opow_pos _ omega0_pos) le_self_add
  | M :: Ms, [], _, _, _, h => by
    rw [blocks_cons, blocks_nil] at h
    exact absurd h (by simp [blk, Bijectivity.ltPS])
  | M1 :: Ms1, M2 :: Ms2, hP1, hP2, hS, h => by
    rw [blocks_cons, blocks_cons, blk, blk, List.cons_append, List.cons_append] at h
    have h' : Bijectivity.ltPS (sh M1 ++ blocks Ms1) (sh M2 ++ blocks Ms2) :=
      (ltPS_append_left [(0, 0)] _ _).mp h
    rw [dOrdL_blocks, dOrdL_blocks, List.map_cons, List.map_cons]
    by_cases hM : M1 = M2
    · subst hM
      have := dOrdL_lt_of_ltPS (fun M hM => hP1 M (by simp [hM]))
        (fun M hM => hP2 M (by simp [hM])) (List.Pairwise.of_cons hS)
        ((ltPS_append_left (sh M1) _ _).mp h')
      rw [dOrdL_blocks, dOrdL_blocks] at this
      rw [oSum_cons, oSum_cons]
      exact (add_lt_add_iff_left _).mpr this
    · have hlt := (ltPS_iff_pairOrdL_lt (hP1 M1 (by simp)) (hP2 M2 (by simp))).mp
        (ltPS_of_sh M1 M2 _ _ (startsZero_blocks Ms2) hM h')
      refine lt_of_lt_of_le (oSum_lt_succ_head ?_) ?_
      · exact (List.pairwise_map (R := fun a b : Ordinal.{0} => b ≤ a) (f := pairOrdL)
          (l := M1 :: Ms1)).mpr hS
      · exact le_trans (opow_le_opow_right omega0_pos (Order.succ_le_of_lt hlt))
          (opow_le_oSum (by simp))

/-- **Order-preserving**: for two-row DBMS matrices, the lexicographic order
`<ₚ` of pss-proof is the order of the ordinals. -/
theorem ltPS_iff_dOrdL_lt (a b : DbmsState2) :
    Bijectivity.ltPS a.1 b.1 ↔ dbmsL2OrdEval.val a < dbmsL2OrdEval.val b := by
  have fwd : ∀ a b : DbmsState2, Bijectivity.ltPS a.1 b.1 →
      dbmsL2OrdEval.val a < dbmsL2OrdEval.val b := by
    intro a b h
    obtain ⟨Ms1, hP1, hS1, h1⟩ := dform_state a
    obtain ⟨Ms2, hP2, -, h2⟩ := dform_state b
    show dOrdL a.1 < dOrdL b.1
    rw [h1, h2] at h ⊢
    exact dOrdL_lt_of_ltPS hP1 hP2 hS1 h
  refine ⟨fwd a b, fun h => ?_⟩
  rcases ltPS_trichotomy a.1 b.1 with h1 | h1 | h1
  · exact h1
  · exact absurd h (by rw [Subtype.ext h1]; exact lt_irrefl _)
  · exact absurd h (not_lt.mpr (fwd b a h1).le)


/-! ### The same system as the arrays and as `dbmsL 1` -/

/-- The entries of a standard two-row DBMS array. -/
def toL2 (A : (dbms 2).State) : DbmsState2 := ⟨entries2 A.1, A.1, A.2, rfl⟩

/-- **The entries are a translation** from the arrays `dbms 2` onto
`dbmsL2`, bracket for bracket. -/
def dbmsToL2 : StepHom (dbms 2) dbmsL2 where
  map := toL2
  reindex := id
  map_step := fun A N => Subtype.ext (entries2_expand A.1 N)
  map_halted := fun A h => by
    have hL := entries2_length A.1
    rw [show entries2 A.1 = [] from h] at hL
    exact hL.symm

theorem dbmsToL2_surjective (l : DbmsState2) : ∃ A, dbmsToL2.map A = l := by
  obtain ⟨A, hA, hl⟩ := l.2
  exact ⟨⟨A, hA⟩, Subtype.ext hl⟩

theorem dbmsToL2_halted_iff (A : (dbms 2).State) :
    (dbms 2).halted A ↔ dbmsL2.halted (dbmsToL2.map A) := by
  show A.1.len = 0 ↔ entries2 A.1 = []
  rw [← List.length_eq_zero_iff, entries2_length]

instance instIsWellFoundedDbms2 : IsWellFounded (dbms 2).State (dbms 2).Rel := ⟨dbms_wf 2⟩

/-- **An array has the rank of its matrix.** -/
theorem rank_dbmsToL2 (A : (dbms 2).State) :
    IsWellFounded.rank dbmsL2.Rel (dbmsToL2.map A) = IsWellFounded.rank (dbms 2).Rel A :=
  dbmsToL2.rank_map (fun k => ⟨k, rfl⟩) dbmsToL2_halted_iff A

/-- **So the rank of a standard two-row DBMS array is the ordinal of its
entries.** -/
theorem rank_dbms2_eq (A : (dbms 2).State) :
    IsWellFounded.rank (dbms 2).Rel A = dOrdL (entries2 A.1) := by
  rw [← rank_dbmsToL2, rank_dbmsL2_eq]
  rfl

theorem dreach_colOf {l : List (ℕ × ℕ)} (h : DReach2 l) :
    ∃ A : Arr (1 + 1), DStd (1 + 1) A ∧ entriesR A = l.map colOf := by
  obtain ⟨A, hA, rfl⟩ := h
  exact ⟨A, hA, entriesR_two A⟩

/-- `dbmsL2` → `dbmsL 1`: each pair written as a column of two entries. -/
def dbmsL2ToL : StepHom dbmsL2 (dbmsL 1) where
  map := fun l => ⟨l.1.map colOf, dreach_colOf l.2⟩
  reindex := id
  map_step := fun l N => Subtype.ext (expandRL_two N l.1).symm
  map_halted := fun _ h => List.map_eq_nil_iff.mp h

theorem dbmsL2ToL_injective {a b : DbmsState2} (h : dbmsL2ToL.map a = dbmsL2ToL.map b) :
    a = b :=
  Subtype.ext (map_colOf_injective (congrArg Subtype.val h))

theorem dbmsL2ToL_surjective (c : (dbmsL 1).State) : ∃ a, dbmsL2ToL.map a = c := by
  obtain ⟨A, hA, hc⟩ := c.2
  refine ⟨⟨entries2 A, A, hA, rfl⟩, Subtype.ext ?_⟩
  show (entries2 A).map colOf = c.1
  rw [← hc, entriesR_two]
  rfl

instance instIsWellFoundedDbmsLOne : IsWellFounded (dbmsL 1).State (dbmsL 1).Rel := ⟨dbmsL_wf 1⟩

/-- **`dbmsL 1` and `dbmsL2` have the same ranks.** -/
theorem rank_dbmsL2ToL (l : DbmsState2) :
    IsWellFounded.rank (dbmsL 1).Rel (dbmsL2ToL.map l) = IsWellFounded.rank dbmsL2.Rel l :=
  dbmsL2ToL.rank_map (fun k => ⟨k, rfl⟩) (fun _ => List.map_eq_nil_iff.symm) l

end Googology.Trans.DBMS
