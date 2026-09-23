import Googology.Trans.DBMS.ThreeRow

/-!
# Which lists of blocks are standard

`Blocks.lean` (`dblocks_of_state`) shows that every standard form of DBMS with
`r + 1` rows is a list of blocks

    blkR M₀ ++ blkR M₁ ++ ⋯ ++ blkR Mₖ

with every content `Mᵢ` in the content system `CReach r`.  This file is about
the converse: which lists of blocks are standard.  At two rows the answer is
`TwoRow.lean` (`dreach2_iff_dform`): the contents are standard pair sequences
and `o(M₀) ≥ o(M₁) ≥ ⋯`.

**The conjecture at three rows** (and at every number of rows):

    blkR M₀ ++ ⋯ ++ blkR Mₖ is standard
      ⟺ every Mᵢ ∈ CReach r and rank(M₀) ≥ rank(M₁) ≥ ⋯ ≥ rank(Mₖ),

`rank = rkL r`, the rank of the rule of BM4 on all matrices.  Numerically (with
`rank` replaced by the lexicographic order of the blocks, which is the rank
order on the standard forms tested) it holds on every list of blocks of at most
8 columns at three rows: all 3-row DBMS standard forms with at most 8 columns
were enumerated (by extending standard prefixes, standardness by yaBMS
`-s -v DBMS`), and among all 43597 lists of at least one block, built from the
single-block standard forms and of at most 8 columns, "standard" and "the
blocks do not increase" agree on every one.  The reach form below agrees with
the lexicographic order too: on the 72 contents of at most 4 columns, `M'` is
reached from `M` (search up to 9 columns, brackets `[0]`–`[3]`) exactly when
`M ≥ M'` lexicographically.

**What is proved here**, for every number of rows `r + 1` (so for three rows
at `r = 2`):

* `dchain_of_dstdL` (**necessary, strong form**): a standard form is a list of
  blocks whose contents lie in `CReach r` and each content is **reached** from
  every earlier one by steps of BM4 (`Relation.ReflTransGen (CStep r)`).
* `drank_of_dstdL` (**necessary, rank form**): so the ranks do not increase,
  `rank(M₀) ≥ rank(M₁) ≥ ⋯`.
* `dstdL_blkR` (**sufficient for one block**): the block of any content in
  `CReach r` is standard.
* `dstdL_append_blkR_rt`: the last block of a standard form can be replaced by
  the block of any content reached from it.
* `dstdL_of_dchain_of_dup` (**sufficient, up to one property**): if standard
  forms can **duplicate** their last block (`DupProp r`: for contents
  `M₀, …, Mₖ` of the chain form, `blkR M₀ ++ ⋯ ++ blkR Mₖ` standard ⟹
  `blkR M₀ ++ ⋯ ++ blkR Mₖ ++ blkR Mₖ` standard), then every list of blocks as
  in `dchain_of_dstdL` is standard (`dstdL_iff_dchain_of_dup`).  Conversely
  that sufficiency gives `DupProp r` (`dupProp_of_suff`), so the reach form of
  the characterization is equivalent to `DupProp r`.
* `dstdL_iff_drank_of_inj` (**the characterization, up to injectivity**): if
  the rank is one to one on `CReach r` (`RkInj r`), then a list of blocks is
  standard exactly when its contents lie in `CReach r` and their ranks do not
  increase.  The proof is the one of `TwoRow.lean`: a standard generator lies
  above, the rank descends to the target, and Cantor normal form with `RkInj`
  says the matrix reached is the target.

`DupProp r` is proved for every `r` in `BlocksSuff.lean` (`dupProp`), so the
reach form is a characterization for every number of rows (`dstdL_iff_dchain`).
`RkInj 2` is not proved.
-/

namespace Googology.Trans.DBMS

open BM4
open Googology.Notation.DBMS
open Googology.Trans.BMS
open Ordinal Order

/-! ### Standard, on the entries -/

/-- A list of columns is a DBMS standard form with `r + 1` rows. -/
def DStdL (r : Nat) (l : List (List Nat)) : Prop :=
  ∃ A : Arr (r + 1), DStd (r + 1) A ∧ entriesR A = l

theorem DStdL.expand {r : Nat} {l : List (List Nat)} (h : DStdL r l) (N : Nat) :
    DStdL r (expandRL (r + 1) N l) :=
  dbmsL_step_ok ⟨l, h⟩ N

theorem dstdL_blkR_cgen (r n : Nat) : DStdL r (blkR (r + 1) (cgen r n)) :=
  ⟨dstair (r + 1) n, DStd.init n, entriesR_dstair_blkR r n⟩

theorem dstdL_nil (r : Nat) : DStdL r [] := by
  have h := (dstdL_blkR_cgen r 0).expand 0
  simpa [cgen, blkR, expandRL_single] using h

/-- The list of blocks of the contents `Ms`. -/
def blocksR (r : Nat) (Ms : List (List (List Nat))) : List (List Nat) :=
  (Ms.map (blkR (r + 1))).flatten

@[simp] theorem blocksR_nil (r : Nat) : blocksR r [] = [] := rfl

@[simp] theorem blocksR_cons (r : Nat) (M : List (List Nat)) (Ms : List (List (List Nat))) :
    blocksR r (M :: Ms) = blkR (r + 1) M ++ blocksR r Ms := by
  simp [blocksR]

@[simp] theorem blocksR_append (r : Nat) (Ms Ms' : List (List (List Nat))) :
    blocksR r (Ms ++ Ms') = blocksR r Ms ++ blocksR r Ms' := by
  simp [blocksR]

/-! ### Steps of the content system -/

/-- One step of BM4 on contents. -/
def CStep (r : Nat) (M M' : List (List Nat)) : Prop := ∃ N, M' = expandRL (r + 1) N M

theorem CReach.of_rt {r : Nat} {M M' : List (List Nat)} (h : CReach r M)
    (h' : Relation.ReflTransGen (CStep r) M M') : CReach r M' := by
  induction h' with
  | refl => exact h
  | tail _ hs ih =>
    obtain ⟨N, rfl⟩ := hs
    exact CReach.step N ih

theorem CReach.exists_rt {r : Nat} {M : List (List Nat)} (h : CReach r M) :
    ∃ n, Relation.ReflTransGen (CStep r) (cgen r n) M := by
  induction h with
  | gen n => exact ⟨n, Relation.ReflTransGen.refl⟩
  | step N _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n, hn.tail ⟨N, rfl⟩⟩

/-- Steps do not raise the rank. -/
theorem rkL_le_of_rt {r : Nat} {a b : List (List Nat)} (ha : Valid r a)
    (h : Relation.ReflTransGen (CStep r) a b) : rkL r b ≤ rkL r a ∧ Valid r b := by
  induction h with
  | refl => exact ⟨le_rfl, ha⟩
  | @tail b c _ hs ih =>
    obtain ⟨N, rfl⟩ := hs
    by_cases hb : b = []
    · rw [hb, expandRL_nil]; rw [hb] at ih; exact ih
    · exact ⟨le_trans (rkL_lt ih.2 hb N).le ih.1, valid_expandRL ih.2 N⟩

/-! ### The necessary direction -/

/-- **Contents in the content system, each reached from every earlier one.** -/
def DChain (r : Nat) (Ms : List (List (List Nat))) : Prop :=
  (∀ M ∈ Ms, CReach r M) ∧ Ms.Pairwise (Relation.ReflTransGen (CStep r))

/-- **Contents in the content system, with ranks that do not increase.** -/
def DRank (r : Nat) (Ms : List (List (List Nat))) : Prop :=
  (∀ M ∈ Ms, CReach r M) ∧ Ms.Pairwise (fun a b => rkL r b ≤ rkL r a)

theorem DChain.drank {r : Nat} {Ms : List (List (List Nat))} (h : DChain r Ms) : DRank r Ms :=
  ⟨h.1, h.2.imp_of_mem (fun ha _ hab => (rkL_le_of_rt (h.1 _ ha).valid hab).1)⟩

/-- Expanding a list of blocks of the chain form gives one of the chain form. -/
theorem dchain_expand {r : Nat} {Ms : List (List (List Nat))} (h : DChain r Ms) (N : Nat) :
    ∃ Ms', DChain r Ms' ∧ expandRL (r + 1) N (blocksR r Ms) = blocksR r Ms' := by
  obtain ⟨hMs, hP⟩ := h
  rcases List.eq_nil_or_concat Ms with rfl | ⟨Ms', M, rfl⟩
  · exact ⟨[], ⟨by simp, List.Pairwise.nil⟩, by simp [expandRL_nil]⟩
  rw [List.concat_eq_append] at hMs hP ⊢
  have hM : CReach r M := hMs M (by simp)
  have hMs' : ∀ M' ∈ Ms', CReach r M' := fun M' h => hMs M' (by simp [h])
  obtain ⟨hP', -, hcross⟩ := List.pairwise_append.mp hP
  have hcross' : ∀ a ∈ Ms', Relation.ReflTransGen (CStep r) a M :=
    fun a ha => hcross a ha M (by simp)
  rw [blocksR_append, show blocksR r [M] = blkR (r + 1) M by simp,
    expandRL_append (r + 1) N _ _ (by rw [blkR_get0, zcol_get]) (by simp [blkR])]
  by_cases hne : M = []
  · subst hne
    exact ⟨Ms', ⟨hMs', hP'⟩, by simp only [blkR, List.map_nil, expandRL_single, List.append_nil]⟩
  by_cases hlast : IsZ (M[M.length - 1]!)
  · have hX : CStep r M M.dropLast := ⟨0, (expandRL_zero (r + 1) M hM.valid).symm⟩
    have hXR : CReach r M.dropLast := by
      rw [← expandRL_zero (r + 1) M hM.valid]; exact CReach.step 0 hM
    rw [expandRL_blkR_zero (r + 1) N (Nat.succ_pos r) hM.valid hne hlast, repN_blkR]
    refine ⟨Ms' ++ List.replicate (N + 1) M.dropLast, ⟨fun M' h => ?_, ?_⟩, by simp [blocksR]⟩
    · rcases List.mem_append.mp h with h | h
      · exact hMs' M' h
      · rw [List.eq_of_mem_replicate h]; exact hXR
    · refine List.pairwise_append.mpr ⟨hP', List.pairwise_replicate.mpr
        (Or.inr Relation.ReflTransGen.refl), fun a ha b hb => ?_⟩
      rw [List.eq_of_mem_replicate hb]
      exact (hcross' a ha).tail hX
  · rw [expandRL_blkR_ne (r + 1) N (Nat.succ_pos r) hM.rooted hne hlast]
    refine ⟨Ms' ++ [expandRL (r + 1) N M], ⟨fun M' h => ?_, ?_⟩, by simp [blocksR]⟩
    · rcases List.mem_append.mp h with h | h
      · exact hMs' M' h
      · rw [List.mem_singleton.mp h]; exact CReach.step N hM
    · refine List.pairwise_append.mpr ⟨hP', List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
      rw [List.mem_singleton.mp hb]
      exact (hcross' a ha).tail ⟨N, rfl⟩

/-- **Necessary, strong form**: every standard form is a list of blocks whose
contents lie in the content system, each reached by steps of BM4 from every
earlier one. -/
theorem dchain_of_dstdL {r : Nat} {l : List (List Nat)} (h : DStdL r l) :
    ∃ Ms, DChain r Ms ∧ l = blocksR r Ms := by
  obtain ⟨A, hA, rfl⟩ := h
  induction hA with
  | init n =>
    exact ⟨[cgen r n], ⟨fun M h => by rw [List.mem_singleton.mp h]; exact CReach.gen n,
      List.pairwise_singleton _ _⟩, by rw [entriesR_dstair_blkR]; simp⟩
  | step N _ ih =>
    obtain ⟨Ms, hMs, he⟩ := ih
    rw [entriesR_expand (Nat.succ_pos r), he]
    exact dchain_expand hMs N

/-- **Necessary, rank form**: the ranks of the contents do not increase. -/
theorem drank_of_dstdL {r : Nat} {l : List (List Nat)} (h : DStdL r l) :
    ∃ Ms, DRank r Ms ∧ l = blocksR r Ms := by
  obtain ⟨Ms, hMs, he⟩ := dchain_of_dstdL h
  exact ⟨Ms, hMs.drank, he⟩

/-! ### Sufficient: one block, and replacing the last block -/

/-- **The last block can be replaced by the block of one step of its content.** -/
theorem dstdL_append_blkR_step {r : Nat} {P M : List (List Nat)} (hM : CReach r M)
    (h : DStdL r (P ++ blkR (r + 1) M)) (N : Nat) :
    DStdL r (P ++ blkR (r + 1) (expandRL (r + 1) N M)) := by
  have happ : ∀ K, expandRL (r + 1) K (P ++ blkR (r + 1) M)
      = P ++ expandRL (r + 1) K (blkR (r + 1) M) :=
    fun K => expandRL_append (r + 1) K _ _ (by rw [blkR_get0, zcol_get]) (by simp [blkR])
  by_cases hne : M = []
  · subst hne; rw [expandRL_nil]; exact h
  by_cases hlast : IsZ (M[M.length - 1]!)
  · have e1 : expandRL (r + 1) N M = M.dropLast := by
      rw [expandRL, badRootR_none_of_isZ (r + 1) hlast]
    have h0 := h.expand 0
    rw [happ, expandRL_blkR_zero (r + 1) 0 (Nat.succ_pos r) hM.valid hne hlast] at h0
    rw [e1]
    simpa [repN] using h0
  · have hN := h.expand N
    rwa [happ, expandRL_blkR_ne (r + 1) N (Nat.succ_pos r) hM.rooted hne hlast] at hN

/-- **The last block can be replaced by the block of any content reached from
its content.** -/
theorem dstdL_append_blkR_rt {r : Nat} {P M M' : List (List Nat)} (hM : CReach r M)
    (h : DStdL r (P ++ blkR (r + 1) M)) (hr : Relation.ReflTransGen (CStep r) M M') :
    DStdL r (P ++ blkR (r + 1) M') := by
  induction hr with
  | refl => exact h
  | @tail b c hab hs ih =>
    obtain ⟨N, rfl⟩ := hs
    exact dstdL_append_blkR_step (hM.of_rt hab) ih N

/-- **Sufficient for one block**: the block of a content in the content system
is a standard form. -/
theorem dstdL_blkR {r : Nat} {M : List (List Nat)} (hM : CReach r M) :
    DStdL r (blkR (r + 1) M) := by
  obtain ⟨n, hn⟩ := hM.exists_rt
  have h := dstdL_append_blkR_rt (P := []) (CReach.gen n) (by simpa using dstdL_blkR_cgen r n) hn
  simpa using h

/-! ### Sufficient, up to duplicating the last block -/

/-- **Duplication**: a standard list of blocks of the chain form can repeat its
last block. -/
def DupProp (r : Nat) : Prop :=
  ∀ (Ms : List (List (List Nat))) (M : List (List Nat)), DChain r (Ms ++ [M]) →
    DStdL r (blocksR r (Ms ++ [M])) → DStdL r (blocksR r (Ms ++ [M, M]))

theorem DChain.sublist {r : Nat} {Ms Ms' : List (List (List Nat))} (h : DChain r Ms')
    (hs : Ms.Sublist Ms') : DChain r Ms :=
  ⟨fun M hM => h.1 M (hs.subset hM), h.2.sublist hs⟩

theorem dstdL_of_dchain_aux {r : Nat} (hd : DupProp r) : ∀ (Ms Qs : List (List (List Nat)))
    (X : List (List Nat)), DChain r (Qs ++ X :: Ms) → DStdL r (blocksR r (Qs ++ [X])) →
    DStdL r (blocksR r (Qs ++ X :: Ms)) := by
  intro Ms
  induction Ms with
  | nil => intro Qs X _ h; exact h
  | cons Y Ms ih =>
    intro Qs X hc h
    have hc1 : DChain r (Qs ++ [X]) :=
      hc.sublist (List.Sublist.append_left (List.singleton_sublist.mpr (by simp)) Qs)
    have hXY : Relation.ReflTransGen (CStep r) X Y := by
      have := (List.pairwise_append.mp hc.2).2.1
      exact List.rel_of_pairwise_cons this (by simp)
    have hX : CReach r X := hc.1 X (by simp)
    have h2 := hd Qs X hc1 h
    rw [show Qs ++ [X, X] = (Qs ++ [X]) ++ [X] by simp, blocksR_append,
      show blocksR r [X] = blkR (r + 1) X by simp] at h2
    have h3 := dstdL_append_blkR_rt hX h2 hXY
    rw [show blkR (r + 1) Y = blocksR r [Y] by simp, ← blocksR_append] at h3
    have h4 := ih (Qs ++ [X]) Y (by simpa using hc) h3
    simpa using h4

/-- **Sufficient, given duplication**: a list of blocks whose contents lie in
the content system, each reached from every earlier one, is standard. -/
theorem dstdL_of_dchain_of_dup {r : Nat} (hd : DupProp r) {Ms : List (List (List Nat))}
    (h : DChain r Ms) : DStdL r (blocksR r Ms) := by
  cases Ms with
  | nil => exact dstdL_nil r
  | cons X Ms =>
    have hX : CReach r X := h.1 X (by simp)
    exact dstdL_of_dchain_aux hd Ms [] X (by simpa using h) (by simpa using dstdL_blkR hX)

/-- **The characterization in the reach form, given duplication.** -/
theorem dstdL_iff_dchain_of_dup {r : Nat} (hd : DupProp r) (l : List (List Nat)) :
    DStdL r l ↔ ∃ Ms, DChain r Ms ∧ l = blocksR r Ms := by
  refine ⟨dchain_of_dstdL, ?_⟩
  rintro ⟨Ms, hMs, rfl⟩
  exact dstdL_of_dchain_of_dup hd hMs

/-- **And duplication is needed**: if every list of the chain form is standard,
standard forms can duplicate their last block. -/
theorem dupProp_of_suff {r : Nat} (h : ∀ Ms, DChain r Ms → DStdL r (blocksR r Ms)) :
    DupProp r := by
  intro Ms M hc _
  refine h _ ⟨fun M' hM' => ?_, ?_⟩
  · rw [show Ms ++ [M, M] = (Ms ++ [M]) ++ [M] by simp] at hM'
    rcases List.mem_append.mp hM' with h1 | h1
    · exact hc.1 M' h1
    · rw [List.mem_singleton.mp h1]; exact hc.1 M (by simp)
  · rw [show Ms ++ [M, M] = (Ms ++ [M]) ++ [M] by simp]
    refine List.pairwise_append.mpr ⟨hc.2, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    rw [List.mem_singleton.mp hb]
    rcases List.mem_append.mp ha with h1 | h1
    · exact (List.pairwise_append.mp hc.2).2.2 a h1 M (by simp)
    · rw [List.mem_singleton.mp h1]

/-! ### Sufficient, up to injectivity of the rank -/

/-- **The rank is one to one on the content system.** -/
def RkInj (r : Nat) : Prop :=
  ∀ M M', CReach r M → CReach r M' → rkL r M = rkL r M' → M = M'

theorem rkL_blocksR (r : Nat) {Ms : List (List (List Nat))} (h : ∀ M ∈ Ms, CReach r M) :
    rkL r (blocksR r Ms) = oSum (Ms.map (rkL r)) := by
  rw [blocksR, rkL_blocks r Ms h, oSum, List.map_map]
  rfl

theorem rkL_cgen_lt_succ (r n : Nat) : rkL r (cgen r n) < rkL r (cgen r (n + 1)) := by
  have h : Rewrite.rank (dbmsL_wf r) (genL r n) < Rewrite.rank (dbmsL_wf r) (genL r (n + 1)) := by
    rw [Rewrite.rank_def, Rewrite.rank_def]; exact rank_gen_lt_succ r n
  rw [rank_genL_eq, rank_genL_eq] at h
  exact (opow_lt_opow_iff_right one_lt_omega0).mp h

theorem rkL_cgen_mono (r : Nat) {m n : Nat} (h : m ≤ n) : rkL r (cgen r m) ≤ rkL r (cgen r n) := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact le_trans ih (rkL_cgen_lt_succ r _).le

theorem CReach.exists_lt_cgen {r : Nat} {M : List (List Nat)} (h : CReach r M) :
    ∃ n, rkL r M < rkL r (cgen r n) := by
  obtain ⟨n, hn⟩ := h.exists_rt
  exact ⟨n + 1, lt_of_le_of_lt (rkL_le_of_rt (valid_cgen r n) hn).1 (rkL_cgen_lt_succ r n)⟩

theorem exists_lt_cgen_all {r : Nat} : ∀ Ms : List (List (List Nat)), (∀ M ∈ Ms, CReach r M) →
    ∃ n, ∀ M ∈ Ms, rkL r M < rkL r (cgen r n)
  | [], _ => ⟨0, by simp⟩
  | M :: Ms, h => by
    obtain ⟨n1, h1⟩ := exists_lt_cgen_all Ms (fun M' hM' => h M' (by simp [hM']))
    obtain ⟨n2, h2⟩ := (h M (by simp)).exists_lt_cgen
    refine ⟨max n1 n2, fun M' hM' => ?_⟩
    rcases List.mem_cons.mp hM' with rfl | hM'
    · exact lt_of_lt_of_le h2 (rkL_cgen_mono r (le_max_right _ _))
    · exact lt_of_lt_of_le (h1 M' hM') (rkL_cgen_mono r (le_max_left _ _))

/-- A list of blocks has a smaller rank than some generator. -/
theorem exists_gen_above {r : Nat} {Ms : List (List (List Nat))} (h : ∀ M ∈ Ms, CReach r M) :
    ∃ n, rkL r (blocksR r Ms) < rkL r (genL r n).1 := by
  obtain ⟨n, hn⟩ := exists_lt_cgen_all Ms h
  refine ⟨n, ?_⟩
  rw [← rank_dbmsL_eq_rkL, rank_genL_eq, rkL_blocksR r h]
  exact oSum_lt_opow _ (fun x hx => by
    obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hx
    exact hn M hM)

theorem map_eq_of_injOn {α : Type} {β : Type 1} {P : α → Prop} {f : α → β}
    (hf : ∀ a b, P a → P b → f a = f b → a = b) :
    ∀ {xs ys : List α}, (∀ x ∈ xs, P x) → (∀ y ∈ ys, P y) → xs.map f = ys.map f → xs = ys
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: xs, y :: ys, hx, hy, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hf x y (hx x (by simp)) (hy y (by simp)) h.1,
      map_eq_of_injOn hf (fun x' h' => hx x' (by simp [h'])) (fun y' h' => hy y' (by simp [h'])) h.2]

theorem valid_of_state {r : Nat} (E : (dbmsL r).State) : Valid r E.1 :=
  ((dbmsLSim r).map E).2

/-- **Descent**: under injectivity, a list of blocks of the rank form whose rank
is at most that of a standard form is standard. -/
theorem dstdL_of_le {r : Nat} (hinj : RkInj r) : ∀ (E : (dbmsL r).State)
    (Ms : List (List (List Nat))), DRank r Ms → rkL r (blocksR r Ms) ≤ rkL r E.1 →
    DStdL r (blocksR r Ms) := by
  intro E
  induction E using WellFounded.induction (dbmsL_wf r) with
  | _ E IH =>
    intro Ms hMs hle
    rcases hle.lt_or_eq with hlt | heq
    · have hne : E.1 ≠ [] := by
        intro h
        rw [h, rkL_nil] at hlt
        exact absurd hlt not_lt_zero
      rw [rkL_step (valid_of_state E) hne] at hlt
      have hex : ∃ N, rkL r (blocksR r Ms) < succ (rkL r (expandRL (r + 1) N E.1)) := by
        by_contra hc
        push Not at hc
        exact absurd (Ordinal.iSup_le hc) (not_le.mpr hlt)
      obtain ⟨N, hN⟩ := hex
      exact IH ((dbmsL r).step E N) ⟨hne, N, rfl⟩ Ms hMs (Order.lt_succ_iff.mp hN)
    · obtain ⟨Es, hEs, he⟩ := drank_of_dstdL (show DStdL r E.1 from E.2)
      rw [he, rkL_blocksR r hMs.1, rkL_blocksR r hEs.1] at heq
      have hmap := oSum_inj (List.pairwise_map.mpr hMs.2) (List.pairwise_map.mpr hEs.2) heq
      have hMsEs : Ms = Es := map_eq_of_injOn (P := CReach r) (f := rkL r) hinj hMs.1 hEs.1 hmap
      rw [hMsEs, ← he]
      exact E.2

/-- **Sufficient, given injectivity**: a list of blocks whose contents lie in
the content system with ranks that do not increase is standard. -/
theorem dstdL_of_drank_of_inj {r : Nat} (hinj : RkInj r) {Ms : List (List (List Nat))}
    (h : DRank r Ms) : DStdL r (blocksR r Ms) := by
  obtain ⟨n, hn⟩ := exists_gen_above h.1
  exact dstdL_of_le hinj (genL r n) Ms h hn.le

/-- **The characterization, given injectivity of the rank on the content
system.** -/
theorem dstdL_iff_drank_of_inj {r : Nat} (hinj : RkInj r) (l : List (List Nat)) :
    DStdL r l ↔ ∃ Ms, DRank r Ms ∧ l = blocksR r Ms := by
  refine ⟨drank_of_dstdL, ?_⟩
  rintro ⟨Ms, hMs, rfl⟩
  exact dstdL_of_drank_of_inj hinj hMs

/-! ### Three rows -/

/-- **Three rows, necessary**: a standard form of three-row DBMS is a list of
blocks whose contents lie in the content system `C₃` generated by
`(0,0,0)(1,1,0)(2,2,1)⋯`, each reached from every earlier one, so with ranks
`rank(M₀) ≥ rank(M₁) ≥ ⋯`. -/
theorem dstdL_three_necessary {l : List (List Nat)} (h : DStdL 2 l) :
    ∃ Ms, DChain 2 Ms ∧ DRank 2 Ms ∧ l = blocksR 2 Ms := by
  obtain ⟨Ms, hMs, he⟩ := dchain_of_dstdL h
  exact ⟨Ms, hMs, hMs.drank, he⟩

/-- **Three rows, sufficient for one block.** -/
theorem dstdL_three_blkR {M : List (List Nat)} (h : CReach 2 M) : DStdL 2 (blkR 3 M) :=
  dstdL_blkR h

/-- **Three rows, the characterization given injectivity of the rank on `C₃`.** -/
theorem dstdL_three_iff_of_inj (hinj : RkInj 2) (l : List (List Nat)) :
    DStdL 2 l ↔ ∃ Ms, DRank 2 Ms ∧ l = blocksR 2 Ms :=
  dstdL_iff_drank_of_inj hinj l

/-- **Three rows, the reach form of the characterization given duplication.** -/
theorem dstdL_three_iff_of_dup (hd : DupProp 2) (l : List (List Nat)) :
    DStdL 2 l ↔ ∃ Ms, DChain 2 Ms ∧ l = blocksR 2 Ms :=
  dstdL_iff_dchain_of_dup hd l

end Googology.Trans.DBMS
