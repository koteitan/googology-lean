import Googology.Trans.BMS.Same
import Googology.Trans.BMS.Eps0
import Googology.Trans.BMS.ZeroRow
import Googology.Trans.BMS.Append

/-!
# The rank of the system is the ordinal of the term

A well-founded system carries a canonical ordinal measure of its own, the rank
of its one-step relation (`Googology/Rank.lean`), and it needs no notation
system to define.  The primitive sequence system also carries `primEval`, the
value of the extended Buchholz term the matrix reads as.  **They are the
same measure**: `rank_prim_eq_val`.

One direction is the descent, which `primEval` already states.  The other is
cofinality, and it is where `val` being onto below `ε₀` is used: an ordinal
`β` below the term's value is the value of some standard form `Y`, `Y` is then
below the term, and `Cofinal.exists_le_fs` puts `Y` under some `X[n]`.  So
nothing below the value escapes the supremum over the expansions.

That is what licenses reading `Rewrite.rankEval` as "the ordinal this matrix
names" at numbers of rows where no reading is available: at one row, where
both are defined, they agree.

`rank_pairGen` is the first use of that licence.  Two rows have no reading,
but the generator `(0,0)(1,1)` expands into one-row matrices with a zero row
underneath, and `BMS/Embed.lean` carries their ordinals across unchanged, so
its rank comes out as `ε₀` — the pair sequence system starts where the
primitive sequence system ends.  That is also the value the correspondence
tables give `(0,0)(1,1)`.

`rank_appendState` takes it further.  `BMS/Append.lean` says expansion never
reaches back across a column whose row-`0` entry is `0`, so the rank is
additive over those blocks, and `n` copies of `(0,0)(1,1)` have rank `ε₀·n`.
`(0,0)(1,1)(1,0)` expands into exactly those, so its rank is `ε₀·ω` — the
tables' third two-row entry, and again a theorem rather than an assumption.
-/

namespace Googology.Trans.BMS
open Ordinal
open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

theorem val_le_val {x y : Term} (hx : OT x) (hy : OT y) (h : x ≤ y) : val x ≤ val y := by
  rcases le_iff_lt_or_eq.mp h with hlt | rfl
  · exact (val_lt_val hx hy hlt).le
  · exact le_refl _

instance instIsWellFoundedPrim : IsWellFounded prim.State prim.Rel := ⟨prim_wf⟩

/-- **The rank of the primitive sequence system is the value of the term.** -/
theorem rank_prim_eq_val : ∀ l : PrimState,
    IsWellFounded.rank prim.Rel l = val (read 0 l.1) := by
  intro l
  induction l using WellFounded.induction prim_wf with
  | _ l IH =>
    rw [IsWellFounded.rank_eq]
    refine le_antisymm ?_ ?_
    · refine Ordinal.iSup_le ?_
      rintro ⟨m, hna, N, rfl⟩
      show Order.succ (IsWellFounded.rank prim.Rel (prim.step l N)) ≤ _
      rw [IH _ ⟨hna, N, rfl⟩]
      exact Order.succ_le_of_lt (primEval.val_lt l (prim.step l N) ⟨hna, N, rfl⟩)
    · refine le_of_forall_lt (fun β hβ => ?_)
      have hX : OT (read 0 l.1) := l.2.2
      have hAX : AllNil (read 0 l.1) := allNil_read 0 l.1
      have hβ0 : β < Ord.eps0 := lt_trans hβ (val_read_lt_eps0 hX)
      obtain ⟨Y, hOTY, hAY, hvY⟩ := exists_OT_of_lt_eps0 hβ0
      have hYX : Y < read 0 l.1 := lt_of_val_lt hOTY hX (by rw [hvY]; exact hβ)
      obtain ⟨n, hn⟩ := exists_le_fs (read 0 l.1) Y hX hOTY hAX hAY hYX
      have hnil : ¬ prim.halted l := by
        intro h
        have : read 0 l.1 = nil := by
          show read 0 l.1 = nil
          rw [show l.1 = [] from h, read_nil]
        rw [this, val_nil] at hβ
        exact absurd hβ (by simp)
      have hrel : prim.Rel (prim.step l n) l := ⟨hnil, n, rfl⟩
      refine Ordinal.lt_iSup_iff.mpr ⟨⟨prim.step l n, hrel⟩, ?_⟩
      show β < Order.succ (IsWellFounded.rank prim.Rel (prim.step l n))
      refine lt_of_le_of_lt ?_ (Order.lt_succ _)
      rw [IH _ hrel]
      show β ≤ val (read 0 (expandL n 0 l.1))
      rw [read_expandL n l.1 0 l.2.1, ← hvY]
      exact val_le_val hOTY (Term.step_ok hX (read_lt_tW 0 l.1) (n + 1)).1 hn

/-- **The two measures on the primitive sequence system are one measure.** -/
theorem primRankEval_val (l : PrimState) : primRankEval.val l = primEval.val l :=
  rank_prim_eq_val l

/-! ### The same for the arrays -/

theorem entries_eq_nil_iff {A : BM4.Arr 1} : entries A = [] ↔ A.len = 0 := by
  constructor
  · intro h
    have hL := entries_length A
    rw [h] at hL
    exact hL.symm
  · intro h
    rw [entries, h, List.range_zero, List.map_nil]

instance instIsWellFoundedBms : IsWellFounded (Googology.Notation.BMS.bms 1).State
    (Googology.Notation.BMS.bms 1).Rel :=
  ⟨bmsHom.toSim.wf prim_wf⟩

/-- **The rank of one-row BMS is the ordinal the matrix names.**  The reading
is a `StepHom` that does not renumber the brackets, so `StepHom.rank_map`
carries `rank_prim_eq_val` across. -/
theorem rank_bms_eq_val (A : (Googology.Notation.BMS.bms 1).State) :
    IsWellFounded.rank (Googology.Notation.BMS.bms 1).Rel A = bmsOrdEval.val A := by
  have h := bmsHom.rank_map (fun k => ⟨k, rfl⟩)
    (fun s => by
      show s.1.len = 0 ↔ entries s.1 = []
      exact entries_eq_nil_iff.symm) A
  rw [← h]
  exact rank_prim_eq_val (bmsHom.map A)

/-! ### Two rows, at the generator

No reading of a two-row matrix is available, so the rank is the only ordinal
a two-row state carries.  At `(0,0)(1,1)` it can still be computed, because
that generator expands into one-row matrices with a zero row underneath, and
`BMS/Embed.lean` says those carry the one-row ordinals unchanged. -/

instance instIsWellFoundedPair : IsWellFounded pairL.State pairL.Rel := ⟨pairL_wf⟩

/-- Writing a zero row under a one-row matrix does not change its rank. -/
theorem rank_toPairS (l : PrimState) :
    IsWellFounded.rank pairL.Rel (toPairS l) = IsWellFounded.rank prim.Rel l :=
  primHomPair.rank_map (fun k => ⟨k, rfl⟩)
    (fun s => by
      show s.1 = [] ↔ withZero s.1 = []
      rw [withZero, List.map_eq_nil_iff]) l

/-- The one-row generator `(0)(1)⋯(n)`, as a state. -/
def primGen (n : Nat) : PrimState := ⟨List.range (n + 1), col_range n, OT_read_range n⟩

theorem OT_twr : ∀ n : Nat, OT (twr n)
  | 0 => rfl
  | _ + 1 => OT_of_desc _ (allNil_twr _) (descAll_twr _)

theorem val_twr_lt_eps0 (n : Nat) : val (twr n) < Ord.eps0 := by
  rw [← val_te0]
  exact val_lt_val (OT_twr n) OT_te0 (allNil_lt_e0 _ (allNil_twr n))

/-- **The towers the one-row generators read as are the towers of `ω`.** -/
theorem val_twr_succ (n : Nat) : val (twr (n + 1)) = (ω : Ordinal) ^ val (twr n) := by
  rw [show twr (n + 1) = psi nil (twr n) from rfl, val_psi, val_nil]
  exact Ord.psi_zero_eq_opow _ (val_twr_lt_eps0 n)

/-- **So the one-row generator `(0)(1)⋯(n)` names the `n + 1`-st tower.** -/
theorem rank_primGen (n : Nat) :
    IsWellFounded.rank prim.Rel (primGen n) = val (twr (n + 1)) := by
  rw [rank_prim_eq_val]
  show val (read 0 (List.range (n + 1))) = _
  rw [read_range_eq_twr]

/-- `(0)` names `1`. -/
theorem rank_primGen_zero : IsWellFounded.rank prim.Rel (primGen 0) = 1 := by
  rw [rank_primGen, val_twr_succ, show val (twr 0) = 0 from rfl, Ordinal.opow_zero]

/-- `(0)(1)` names `ω`. -/
theorem rank_primGen_one : IsWellFounded.rank prim.Rel (primGen 1) = Ordinal.omega0 := by
  rw [rank_primGen, val_twr_succ, val_twr_succ, show val (twr 0) = 0 from rfl,
    Ordinal.opow_zero, Ordinal.opow_one]

/-- The two-row generator `(0,0)(1,1)`, as a state. -/
def pairGen : PairState :=
  ⟨[(0, 0), (1, 1)], ⟨Pat.stair 2 1, Pat.Std.init 1, by rw [entries2_stair]; rfl⟩⟩

theorem step_pairGen (N : Nat) : pairL.step pairGen N = toPairS (primGen N) :=
  Subtype.ext (expand2L_gen N)

theorem rank_step_pairGen (N : Nat) :
    IsWellFounded.rank pairL.Rel (pairL.step pairGen N) = val (read 0 (List.range (N + 1))) := by
  rw [step_pairGen, rank_toPairS]
  exact rank_prim_eq_val (primGen N)

/-- **The pair sequence generator `(0,0)(1,1)` has rank `ε₀`.**  So the two-row
system starts where the one-row system ends, and the correspondence table's
`(0,0)(1,1) = ε₀` is a theorem here, not an assumption. -/
theorem rank_pairGen : IsWellFounded.rank pairL.Rel pairGen = Ord.eps0 := by
  have hnh : ¬ pairL.halted pairGen := by
    show ¬ ([(0, 0), (1, 1)] : List (Nat × Nat)) = []
    simp
  rw [IsWellFounded.rank_eq]
  refine le_antisymm ?_ ?_
  · refine Ordinal.iSup_le ?_
    rintro ⟨m, _, N, rfl⟩
    show Order.succ (IsWellFounded.rank pairL.Rel (pairL.step pairGen N)) ≤ Ord.eps0
    rw [rank_step_pairGen N]
    exact Order.succ_le_of_lt (val_read_lt_eps0 (OT_read_range N))
  · refine le_of_forall_lt (fun β hβ => ?_)
    obtain ⟨Y, hOTY, hAY, hvY⟩ := exists_OT_of_lt_eps0 hβ
    obtain ⟨m, hm⟩ := exists_lt_twr Y hAY
    cases m with
    | zero => exact absurd hm (by rw [twr]; exact not_lt_nil Y)
    | succ k =>
      have hrel : pairL.Rel (pairL.step pairGen k) pairGen := ⟨hnh, k, rfl⟩
      refine Ordinal.lt_iSup_iff.mpr ⟨⟨pairL.step pairGen k, hrel⟩, ?_⟩
      show β < Order.succ (IsWellFounded.rank pairL.Rel (pairL.step pairGen k))
      refine lt_of_le_of_lt ?_ (Order.lt_succ _)
      rw [rank_step_pairGen k, read_range_eq_twr k, ← hvY]
      exact (val_lt_val hOTY (by rw [← read_range_eq_twr k]; exact OT_read_range k) hm).le

/-! ### Every number of rows, at the generator

The same computation runs at every number of rows, because `expandRL_gen` says
the two-column generator with `r + 2` rows expands into the generators with
`r + 1` rows and a zero row underneath, and `rank_zeroRow` says that row costs
nothing.  So the `r + 2`-row system starts exactly where the `r + 1`-row
generators end. -/

instance instIsWellFoundedBmsL (r : Nat) : IsWellFounded (bmsL r).State (bmsL r).Rel :=
  ⟨bmsL_wf r⟩

/-- **The general system at one row has that rank too.**  `bmsL 0` is `prim`
written with one-element columns. -/
theorem rank_bmsL_zero (l : (bmsL 0).State) :
    IsWellFounded.rank (bmsL 0).Rel l = val (read 0 (l.1.map (fun c => c.head!))) := by
  have h := primOfBmsHom.rank_map (fun k => ⟨k, rfl⟩)
    (fun s => by
      show s.1 = [] ↔ s.1.map (fun c => c.head!) = []
      rw [List.map_eq_nil_iff]) l
  rw [← h]
  exact rank_prim_eq_val (primOfBmsHom.map l)

theorem step_gen_eq (r N : Nat) :
    (bmsL (r + 1)).step ((bmsLStd (r + 1)).gen 1) N
      = (bmsL_homSucc r).map ((bmsLStd r).gen N) := by
  refine Subtype.ext ?_
  show expandRL (r + 1 + 1) N ((List.range 2).map (fun i => List.replicate (r + 1 + 1) i))
    = zeroRow ((List.range (N + 1)).map (fun i => List.replicate (r + 1) i))
  rw [show (List.range 2).map (fun i => List.replicate (r + 1 + 1) i)
      = [List.replicate (r + 1 + 1) 0, List.replicate (r + 1 + 1) 1] from rfl]
  exact expandRL_gen (r + 1) N (Nat.succ_pos r)

theorem rank_step_gen (r N : Nat) :
    IsWellFounded.rank (bmsL (r + 1)).Rel ((bmsL (r + 1)).step ((bmsLStd (r + 1)).gen 1) N)
      = IsWellFounded.rank (bmsL r).Rel ((bmsLStd r).gen N) := by
  rw [step_gen_eq]
  exact rank_zeroRow r ((bmsLStd r).gen N)

theorem not_halted_gen (r : Nat) : ¬ (bmsL (r + 1)).halted ((bmsLStd (r + 1)).gen 1) := by
  show ¬ (List.range 2).map (fun i => List.replicate (r + 1 + 1) i) = []
  simp

/-- **Every generator of the `r + 1`-row system is below the `r + 2`-row
generator.** -/
theorem rank_gen_lt (r N : Nat) :
    IsWellFounded.rank (bmsL r).Rel ((bmsLStd r).gen N)
      < IsWellFounded.rank (bmsL (r + 1)).Rel ((bmsLStd (r + 1)).gen 1) := by
  rw [← rank_step_gen r N]
  exact IsWellFounded.rank_lt_of_rel ⟨not_halted_gen r, N, rfl⟩

/-- **And it is exactly their limit.**  At `r = 0` that limit is `ε₀`, which
is `rank_pairGen`. -/
theorem rank_gen_eq_iSup (r : Nat) :
    IsWellFounded.rank (bmsL (r + 1)).Rel ((bmsLStd (r + 1)).gen 1)
      = ⨆ N : ℕ, Order.succ (IsWellFounded.rank (bmsL r).Rel ((bmsLStd r).gen N)) := by
  rw [IsWellFounded.rank_eq]
  refine le_antisymm (Ordinal.iSup_le ?_) (Ordinal.iSup_le (fun N => ?_))
  · rintro ⟨m, _, N, rfl⟩
    show Order.succ (IsWellFounded.rank (bmsL (r + 1)).Rel
      ((bmsL (r + 1)).step ((bmsLStd (r + 1)).gen 1) N)) ≤ _
    rw [rank_step_gen r N]
    exact Ordinal.le_iSup (fun N : ℕ =>
      Order.succ (IsWellFounded.rank (bmsL r).Rel ((bmsLStd r).gen N))) N
  · rw [← rank_step_gen r N]
    exact Ordinal.le_iSup
      (fun b : {b // (bmsL (r + 1)).Rel b ((bmsLStd (r + 1)).gen 1)} =>
        Order.succ (IsWellFounded.rank (bmsL (r + 1)).Rel b.1))
      ⟨(bmsL (r + 1)).step ((bmsLStd (r + 1)).gen 1) N, not_halted_gen r, N, rfl⟩

/-! ### The successors

A matrix whose last column has no parent drops that column, whatever the
bracket, so it is a successor and its rank says so. -/

/-- **Dropping a column that has no parent takes the rank down by one.** -/
theorem rank_dropLast {r : Nat} (l : (bmsL r).State) (hna : ¬ (bmsL r).halted l)
    (h : badRootR (r + 1) l.1 = none) :
    IsWellFounded.rank (bmsL r).Rel l
      = Order.succ (IsWellFounded.rank (bmsL r).Rel ((bmsL r).step l 0)) := by
  refine Rewrite.rank_succ_of_const_step hna (fun k => Subtype.ext ?_)
  show expandRL (r + 1) k l.1 = expandRL (r + 1) 0 l.1
  rw [expandRL, expandRL, h]

/-! ### Two concrete two-row ordinals

`bmsAllL` has no standardness condition, so a matrix can be written down and
its rank read off.  For a standard matrix the two systems agree, because the
inclusion is a `StepHom` with the brackets unchanged. -/

/-- The standard matrices inside all matrices, as a `StepHom`. -/
def bmsLHomAll (r : Nat) : StepHom (bmsL r) (bmsAllL r) where
  map := fun l => ⟨l.1, by
    obtain ⟨A, _, hA⟩ := l.2
    rw [← hA]
    exact entriesR_col_len A⟩
  reindex := id
  map_step := fun _ _ => Subtype.ext rfl
  map_halted := fun _ h => h

instance instIsWellFoundedBmsAllL (r : Nat) :
    IsWellFounded (bmsAllL r).State (bmsAllL r).Rel := ⟨bmsAllL_wf r⟩

theorem rank_bmsAllL_of_bmsL (r : Nat) (l : (bmsL r).State) :
    IsWellFounded.rank (bmsAllL r).Rel ((bmsLHomAll r).map l)
      = IsWellFounded.rank (bmsL r).Rel l :=
  (bmsLHomAll r).rank_map (fun k => ⟨k, rfl⟩) (fun _ => Iff.rfl) l

theorem rank_bmsL_of_pairL (l : PairState) :
    IsWellFounded.rank (bmsL 1).Rel (bmsOfPairHom.map l)
      = IsWellFounded.rank pairL.Rel l :=
  bmsOfPairHom.rank_map (fun k => ⟨k, rfl⟩)
    (fun s => by
      show s.1 = [] ↔ s.1.map (fun x => [x.1, x.2]) = []
      rw [List.map_eq_nil_iff]) l

/-- `(0,0)(1,1)`. -/
def genAll : (bmsAllL 1).State := ⟨[[0, 0], [1, 1]], by decide⟩

/-- **`(0,0)(1,1)` has rank `ε₀`**, now written as a matrix. -/
theorem rank_genAll : IsWellFounded.rank (bmsAllL 1).Rel genAll = Ord.eps0 := by
  have h : genAll = (bmsLHomAll 1).map (bmsOfPairHom.map pairGen) := Subtype.ext rfl
  rw [h, rank_bmsAllL_of_bmsL, rank_bmsL_of_pairL, rank_pairGen]

/-! ### The rank is additive over blocks -/

/-- Two matrices, one after the other. -/
def appendState {r : Nat} (A B : (bmsAllL r).State) : (bmsAllL r).State :=
  ⟨A.1 ++ B.1, fun c hc => by
    rcases List.mem_append.mp hc with h | h
    · exact A.2 c h
    · exact B.2 c h⟩

/-- **The rank is additive over blocks**: a matrix that starts a block — its
first column has row-`0` entry `0` — contributes its own rank, whatever
stands in front of it. -/
theorem rank_appendState (r : Nat) : ∀ B : (bmsAllL r).State,
    ((B.1[0]!)[0]! = 0 ∨ B.1 = []) → ∀ A : (bmsAllL r).State,
      IsWellFounded.rank (bmsAllL r).Rel (appendState A B)
        = IsWellFounded.rank (bmsAllL r).Rel A + IsWellFounded.rank (bmsAllL r).Rel B := by
  intro B
  induction B using WellFounded.induction (bmsAllL_wf r) with
  | _ B IH =>
    intro hB0 A
    by_cases hBnil : B.1 = []
    · have hA : appendState A B = A := Subtype.ext (by
        show A.1 ++ B.1 = A.1
        rw [hBnil, List.append_nil])
      rw [hA, Rewrite.rank_halted (show (bmsAllL r).halted B from hBnil), add_zero]
    · have h0 : (B.1[0]!)[0]! = 0 := hB0.resolve_right hBnil
      have hnh : ¬ (bmsAllL r).halted B := hBnil
      have hnhAB : ¬ (bmsAllL r).halted (appendState A B) := by
        show ¬ A.1 ++ B.1 = []
        intro hc
        exact hBnil (List.append_eq_nil_iff.mp hc).2
      rw [Rewrite.rank_eq_iSup_nat hnhAB, Rewrite.rank_eq_iSup_nat hnh, add_iSup]
      refine iSup_congr (fun N => ?_)
      have hstep : (bmsAllL r).step (appendState A B) N
          = appendState A ((bmsAllL r).step B N) :=
        Subtype.ext (expandRL_append (r + 1) N A.1 B.1 h0 hBnil)
      rw [hstep, IH ((bmsAllL r).step B N) ⟨hnh, N, rfl⟩ ?_ A, Order.succ_eq_add_one,
        Order.succ_eq_add_one, add_assoc]
      exact (head_expandRL (r + 1) N (Nat.succ_pos r) B.1 h0).symm

/-- A single all-zero column, `(0,0)`. -/
def zeroCol : (bmsAllL 1).State := ⟨[[0, 0]], by decide⟩

/-- **`(0,0)` has rank `1`.**  It has no parent, so every bracket empties
it. -/
theorem rank_zeroCol : IsWellFounded.rank (bmsAllL 1).Rel zeroCol = 1 := by
  have hnil : ∀ c ∈ ([] : List (List Nat)), c.length = 1 + 1 := by simp
  rw [Rewrite.rank_succ_of_const_step
      (show ¬ ([[0, 0]] : List (List Nat)) = [] by simp)
      (b := (⟨[], hnil⟩ : (bmsAllL 1).State)) (fun k => Subtype.ext (by
        show expandRL 2 k [[0, 0]] = []
        rfl)),
    Rewrite.rank_halted (show (⟨[], hnil⟩ : (bmsAllL 1).State).1 = [] from rfl),
    Order.succ_eq_add_one, zero_add]

/-- **A zero column at the end adds one.** -/
theorem rank_append_zeroCol (A : (bmsAllL 1).State) :
    IsWellFounded.rank (bmsAllL 1).Rel (appendState A zeroCol)
      = IsWellFounded.rank (bmsAllL 1).Rel A + 1 := by
  rw [rank_appendState 1 zeroCol (Or.inl rfl) A, rank_zeroCol]

/-- `(0,0)(1,1)(0,0)`. -/
def succAll : (bmsAllL 1).State := ⟨[[0, 0], [1, 1], [0, 0]], by decide⟩

/-- **`(0,0)(1,1)(0,0)` has rank `ε₀ + 1`.**  Its last column is a block of
its own, and that block has rank `1` — `./bms` drops it at `[0]`, `[1]` and
`[2]` — so the correspondence tables' `ε₀ + 1` is a theorem too. -/
theorem rank_succAll :
    IsWellFounded.rank (bmsAllL 1).Rel succAll = Ord.eps0 + 1 := by
  rw [show succAll = appendState genAll zeroCol from rfl, rank_append_zeroCol, rank_genAll]

/-! ### `(0,0)(1,1)(1,0)` has rank `ε₀·ω` -/

/-- `n` copies of `(0,0)(1,1)`. -/
def blockRep : Nat → List (List Nat)
  | 0 => []
  | n + 1 => blockRep n ++ [[0, 0], [1, 1]]

theorem blockRep_col_len : ∀ n, ∀ c ∈ blockRep n, c.length = 1 + 1 := by
  intro n
  induction n with
  | zero => intro c hc; exact absurd hc (by simp [blockRep])
  | succ m ih =>
    intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact ih c h
    · rcases List.mem_cons.mp h with rfl | h2
      · rfl
      · rcases List.mem_cons.mp h2 with rfl | h3
        · rfl
        · exact absurd h3 (by simp)

def blockRepState (n : Nat) : (bmsAllL 1).State := ⟨blockRep n, blockRep_col_len n⟩

theorem blockRepState_succ (n : Nat) :
    blockRepState (n + 1) = appendState (blockRepState n) genAll := rfl

/-- **`n` copies of `(0,0)(1,1)` have rank `ε₀·n`.** -/
theorem rank_blockRepState (n : Nat) :
    IsWellFounded.rank (bmsAllL 1).Rel (blockRepState n) = Ord.eps0 * (n : Ordinal) := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, mul_zero]
    exact Rewrite.rank_halted (show (blockRepState 0).1 = [] from rfl)
  | succ m ih =>
    rw [blockRepState_succ, rank_appendState 1 genAll (Or.inl rfl) (blockRepState m), ih,
      rank_genAll, Nat.cast_succ, mul_add, mul_one]

theorem map_range_blockRep : ∀ n : Nat,
    (List.range (n * 2)).map (fun t => if t % 2 = 0 then ([0, 0] : List Nat) else [1, 1])
      = blockRep n := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [show (m + 1) * 2 = m * 2 + 2 from by ring, List.range_add, List.map_append, ih,
      show List.range 2 = [0, 1] from rfl]
    simp only [List.map_cons, List.map_nil]
    rw [Nat.add_zero, show m * 2 % 2 = 0 from by omega, if_pos rfl,
      show (m * 2 + 1) % 2 = 1 from by omega, if_neg (by omega)]
    rfl

/-- `(0,0)(1,1)(1,0)`. -/
def omegaAll : (bmsAllL 1).State := ⟨[[0, 0], [1, 1], [1, 0]], by decide⟩

theorem step_omegaAll (N : Nat) : (bmsAllL 1).step omegaAll N = blockRepState (N + 1) := by
  refine Subtype.ext ?_
  show expandRL 2 N [[0, 0], [1, 1], [1, 0]] = blockRep (N + 1)
  rw [expandRL, show badRootR 2 [[0, 0], [1, 1], [1, 0]] = some 0 from rfl]
  dsimp only
  rw [show ([[0, 0], [1, 1], [1, 0]] : List (List Nat)).length - 1 - 0 = 2 from rfl,
    List.range_zero, List.map_nil, List.nil_append,
    show m0L 2 [[0, 0], [1, 1], [1, 0]] = 0 from rfl]
  refine Eq.trans (List.map_congr_left (fun t _ => ?_)) (map_range_blockRep (N + 1))
  simp only [Nat.not_lt_zero, decide_false, Bool.false_and, Nat.zero_add]
  rcases (by omega : t % 2 = 0 ∨ t % 2 = 1) with h | h
  · rw [h, if_pos rfl]
    rfl
  · rw [h, if_neg (by omega)]
    rfl

/-- **`(0,0)(1,1)(1,0)` has rank `ε₀·ω`.**  Its expansions are `N + 1` copies
of `(0,0)(1,1)`, and the rank is additive over them. -/
theorem rank_omegaAll :
    IsWellFounded.rank (bmsAllL 1).Rel omegaAll = Ord.eps0 * Ordinal.omega0 := by
  rw [Rewrite.rank_eq_iSup_nat (show ¬ (bmsAllL 1).halted omegaAll from by
    show ¬ ([[0, 0], [1, 1], [1, 0]] : List (List Nat)) = []
    simp)]
  refine le_antisymm (Ordinal.iSup_le (fun N => ?_)) ?_
  · rw [step_omegaAll, rank_blockRepState]
    refine Order.succ_le_of_lt ?_
    exact (mul_lt_mul_iff_of_pos_left Ord.eps0_pos).mpr (Ordinal.natCast_lt_omega0 (N + 1))
  · rw [← Ordinal.iSup_natCast, Ordinal.mul_iSup]
    refine Ordinal.iSup_le (fun n => ?_)
    refine le_trans ?_ (Ordinal.le_iSup
      (fun N : ℕ => Order.succ (IsWellFounded.rank (bmsAllL 1).Rel
        ((bmsAllL 1).step omegaAll N))) n)
    rw [step_omegaAll, rank_blockRepState]
    refine le_trans ?_ (Order.le_succ _)
    exact mul_le_mul_right (by exact_mod_cast Nat.le_succ n) _

end Googology.Trans.BMS
