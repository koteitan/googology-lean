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

/-! ### Repetition multiplies by `ω`

`BMS/Append.lean` says that when `m₀` is `0` the expansion is the good part
and then the bad part repeated `N + 1` times.  The rank of that is the good
part's rank plus the bad part's times `N + 1`, so the matrix itself has the
bad part's rank times `ω`. -/

theorem repN_col_len {r : Nat} (G : (bmsAllL r).State) :
    ∀ n, ∀ c ∈ repN n G.1, c.length = r + 1 := by
  intro n
  induction n with
  | zero => intro c hc; exact absurd hc (by simp [repN])
  | succ m ih =>
    intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact ih c h
    · exact G.2 c h

/-- `n` copies of a matrix. -/
def repNState {r : Nat} (n : Nat) (G : (bmsAllL r).State) : (bmsAllL r).State :=
  ⟨repN n G.1, repN_col_len G n⟩

theorem repNState_succ {r : Nat} (n : Nat) (G : (bmsAllL r).State) :
    repNState (n + 1) G = appendState (repNState n G) G := rfl

theorem repNState_head {r : Nat} {G : (bmsAllL r).State} (hG0 : (G.1[0]!)[0]! = 0) :
    ∀ n, (((repNState n G).1)[0]!)[0]! = 0 ∨ (repNState n G).1 = []
  | 0 => Or.inr rfl
  | n + 1 => by
    rcases eq_or_ne (repN n G.1) [] with h | h
    · refine Or.inl ?_
      show ((repN n G.1 ++ G.1)[0]!)[0]! = 0
      rw [h, List.nil_append]
      exact hG0
    · refine Or.inl ?_
      show ((repN n G.1 ++ G.1)[0]!)[0]! = 0
      rw [getElem!_append_left _ _ (List.length_pos_iff.mpr h)]
      rcases repNState_head hG0 n with h2 | h2
      · exact h2
      · exact absurd h2 h

/-- **`n` copies have `n` times the rank.** -/
theorem rank_repNState {r : Nat} (G : (bmsAllL r).State) (hG0 : (G.1[0]!)[0]! = 0) :
    ∀ n : Nat, IsWellFounded.rank (bmsAllL r).Rel (repNState n G)
      = IsWellFounded.rank (bmsAllL r).Rel G * (n : Ordinal) := by
  intro n
  induction n with
  | zero =>
    rw [Nat.cast_zero, mul_zero]
    exact Rewrite.rank_halted (show (repNState 0 G).1 = [] from rfl)
  | succ m ih =>
    rw [repNState_succ, rank_appendState r G (Or.inl hG0) (repNState m G), ih, Nat.cast_succ,
      mul_add, mul_one]

/-- **A matrix whose expansions are a fixed part and a block repeated has that
block's rank times `ω`.** -/
theorem rank_mul_omega0 {r : Nat} (M P G : (bmsAllL r).State)
    (hM : ¬ (bmsAllL r).halted M) (hG0 : (G.1[0]!)[0]! = 0) (hGne : G.1 ≠ [])
    (hstep : ∀ N, (bmsAllL r).step M N = appendState P (repNState (N + 1) G)) :
    IsWellFounded.rank (bmsAllL r).Rel M
      = IsWellFounded.rank (bmsAllL r).Rel P
        + IsWellFounded.rank (bmsAllL r).Rel G * Ordinal.omega0 := by
  have hGpos : 0 < IsWellFounded.rank (bmsAllL r).Rel G := Rewrite.rank_pos hGne
  have hval : ∀ N : Nat, IsWellFounded.rank (bmsAllL r).Rel ((bmsAllL r).step M N)
      = IsWellFounded.rank (bmsAllL r).Rel P
        + IsWellFounded.rank (bmsAllL r).Rel G * ((N : Ordinal) + 1) := by
    intro N
    rw [hstep N, rank_appendState r (repNState (N + 1) G) (repNState_head hG0 (N + 1)) P,
      rank_repNState G hG0 (N + 1), Nat.cast_succ]
  rw [Rewrite.rank_eq_iSup_nat hM]
  refine le_antisymm (Ordinal.iSup_le (fun N => ?_)) ?_
  · rw [hval N]
    refine Order.succ_le_of_lt ?_
    rw [← Ordinal.iSup_natCast, Ordinal.mul_iSup, add_iSup]
    refine lt_of_lt_of_le ?_ (Ordinal.le_iSup
      (fun n : ℕ => IsWellFounded.rank (bmsAllL r).Rel P
        + IsWellFounded.rank (bmsAllL r).Rel G * (n : Ordinal)) (N + 2))
    rw [add_lt_add_iff_left]
    refine (mul_lt_mul_iff_of_pos_left hGpos).mpr ?_
    push_cast
    rw [add_lt_add_iff_left]
    exact one_lt_two
  · rw [← Ordinal.iSup_natCast, Ordinal.mul_iSup, add_iSup]
    refine Ordinal.iSup_le (fun n => ?_)
    refine le_trans ?_ (Ordinal.le_iSup
      (fun N : ℕ => Order.succ (IsWellFounded.rank (bmsAllL r).Rel ((bmsAllL r).step M N))) n)
    rw [hval n]
    refine le_trans ?_ (Order.le_succ _)
    exact (add_le_add_iff_left _).mpr (mul_le_mul_right le_self_add _)

/-! ### Three matrices whose rank is a multiple of `ω` -/

/-- The empty matrix. -/
def emptyAll : (bmsAllL 1).State := ⟨[], by simp⟩

theorem rank_emptyAll : IsWellFounded.rank (bmsAllL 1).Rel emptyAll = 0 :=
  Rewrite.rank_halted rfl

theorem appendState_col_len {r : Nat} (P G : (bmsAllL r).State) {c : List Nat}
    (hc : c.length = r + 1) : ∀ x ∈ P.1 ++ G.1 ++ [c], x.length = r + 1 := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · rcases List.mem_append.mp h with h2 | h2
    · exact P.2 x h2
    · exact G.2 x h2
  · rw [List.mem_singleton.mp h]
    exact hc

/-- **The rank of `P ++ G ++ [c]`, when the last column has its bad root at
`P`'s end and `m₀` is `0`.**  Then the expansion is `P` and `G` repeated, so
the rank is `P`'s plus `G`'s times `ω`.  For a concrete matrix both
hypotheses are `rfl`. -/
theorem rank_split_mul_omega0 {r : Nat} (P G : (bmsAllL r).State) {c : List Nat}
    (hc : c.length = r + 1) (hG0 : (G.1[0]!)[0]! = 0) (hGne : G.1 ≠ [])
    (hbad : badRootR (r + 1) (P.1 ++ G.1 ++ [c]) = some P.1.length)
    (hm0 : m0L (r + 1) (P.1 ++ G.1 ++ [c]) = 0) :
    IsWellFounded.rank (bmsAllL r).Rel ⟨P.1 ++ G.1 ++ [c], appendState_col_len P G hc⟩
      = IsWellFounded.rank (bmsAllL r).Rel P
        + IsWellFounded.rank (bmsAllL r).Rel G * Ordinal.omega0 := by
  have hlen : (P.1 ++ G.1 ++ [c]).length = P.1.length + G.1.length + 1 := by
    rw [List.length_append, List.length_append]
    rfl
  have hgood : (List.range P.1.length).map (fun i => (P.1 ++ G.1 ++ [c])[i]!) = P.1 := by
    refine Eq.trans (List.map_congr_left (fun i hi => ?_)) (listEta P.1)
    have hi' : i < P.1.length := List.mem_range.mp hi
    rw [getElem!_append_left (P.1 ++ G.1) [c] (by rw [List.length_append]; omega),
      getElem!_append_left P.1 G.1 hi']
  have hseg : (List.range ((P.1 ++ G.1 ++ [c]).length - 1 - P.1.length)).map
      (fun i => (P.1 ++ G.1 ++ [c])[P.1.length + i]!) = G.1 := by
    rw [hlen, show P.1.length + G.1.length + 1 - 1 - P.1.length = G.1.length from by omega]
    refine Eq.trans (List.map_congr_left (fun i hi => ?_)) (listEta G.1)
    have hi' : i < G.1.length := List.mem_range.mp hi
    rw [getElem!_append_left (P.1 ++ G.1) [c] (by rw [List.length_append]; omega),
      getElem!_append_right P.1 G.1 i]
  refine rank_mul_omega0 ⟨P.1 ++ G.1 ++ [c], appendState_col_len P G hc⟩ P G ?_ hG0 hGne
    (fun N => ?_)
  · show ¬ P.1 ++ G.1 ++ [c] = []
    intro h
    exact absurd (List.append_eq_nil_iff.mp h).2 (by simp)
  · refine Subtype.ext ?_
    show expandRL (r + 1) N (P.1 ++ G.1 ++ [c]) = P.1 ++ repN (N + 1) G.1
    rw [expandRL_of_m0_zero (r + 1) N (P.1 ++ G.1 ++ [c]) P.1.length hbad hm0
      (appendState_col_len P G hc), hgood, hseg]

/-- `(0,0)(1,0)` — the two-row form of `(0)(1)`. -/
def omegaCol : (bmsAllL 1).State := ⟨[[0, 0], [1, 0]], by decide⟩

theorem step_omegaCol (N : Nat) :
    (bmsAllL 1).step omegaCol N = appendState emptyAll (repNState (N + 1) zeroCol) := by
  refine Subtype.ext ?_
  show expandRL 2 N [[0, 0], [1, 0]] = [] ++ repN (N + 1) [[0, 0]]
  rw [expandRL_of_m0_zero 2 N _ 0 rfl rfl (by decide)]
  rfl

/-- **`(0,0)(1,0)` has rank `ω`**, the same as `(0)(1)` — as the zero row
demands. -/
theorem rank_omegaCol :
    IsWellFounded.rank (bmsAllL 1).Rel omegaCol = Ordinal.omega0 := by
  rw [rank_mul_omega0 omegaCol emptyAll zeroCol (show ¬ ([[0, 0], [1, 0]] : List (List Nat)) = [] by simp) rfl (by simp [zeroCol])
      step_omegaCol, rank_emptyAll, rank_zeroCol, zero_add, one_mul]

/-- `(0,0)(1,1)(1,0)`. -/
def omegaAll : (bmsAllL 1).State := ⟨[[0, 0], [1, 1], [1, 0]], by decide⟩

theorem step_omegaAll (N : Nat) :
    (bmsAllL 1).step omegaAll N = appendState emptyAll (repNState (N + 1) genAll) := by
  refine Subtype.ext ?_
  show expandRL 2 N [[0, 0], [1, 1], [1, 0]] = [] ++ repN (N + 1) [[0, 0], [1, 1]]
  rw [expandRL_of_m0_zero 2 N _ 0 rfl rfl (by decide)]
  rfl

/-- **`(0,0)(1,1)(1,0)` has rank `ε₀·ω`.**  Its expansions are `N + 1` copies
of `(0,0)(1,1)`. -/
theorem rank_omegaAll :
    IsWellFounded.rank (bmsAllL 1).Rel omegaAll = Ord.eps0 * Ordinal.omega0 := by
  rw [rank_mul_omega0 omegaAll emptyAll genAll (show ¬ ([[0, 0], [1, 1], [1, 0]] : List (List Nat)) = [] by simp) rfl (by simp [genAll])
      step_omegaAll, rank_emptyAll, rank_genAll, zero_add]

/-- `(0,0)(1,1)(0,0)(1,0)`. -/
def sumAll : (bmsAllL 1).State := ⟨[[0, 0], [1, 1], [0, 0], [1, 0]], by decide⟩

theorem step_sumAll (N : Nat) :
    (bmsAllL 1).step sumAll N = appendState genAll (repNState (N + 1) zeroCol) := by
  refine Subtype.ext ?_
  show expandRL 2 N [[0, 0], [1, 1], [0, 0], [1, 0]] = [[0, 0], [1, 1]] ++ repN (N + 1) [[0, 0]]
  rw [expandRL_of_m0_zero 2 N _ 2 rfl rfl (by decide)]
  rfl

/-- `(0,0)(1,0)(1,0)` — the two-row form of `(0)(1)(1)`. -/
def omegaSqCol : (bmsAllL 1).State := ⟨[[0, 0], [1, 0], [1, 0]], by decide⟩

/-- **`(0,0)(1,0)(1,0)` has rank `ω²`**, as `(0)(1)(1)` does. -/
theorem rank_omegaSqCol :
    IsWellFounded.rank (bmsAllL 1).Rel omegaSqCol = Ordinal.omega0 * Ordinal.omega0 := by
  have h : omegaSqCol
      = ⟨emptyAll.1 ++ omegaCol.1 ++ [[1, 0]], appendState_col_len emptyAll omegaCol rfl⟩ :=
    Subtype.ext rfl
  rw [h, rank_split_mul_omega0 emptyAll omegaCol rfl rfl (by simp [omegaCol]) rfl rfl,
    rank_emptyAll, rank_omegaCol, zero_add]

/-- `(0,0)(1,1)(0,0)(1,0)(1,0)`. -/
def sumSqAll : (bmsAllL 1).State := ⟨[[0, 0], [1, 1], [0, 0], [1, 0], [1, 0]], by decide⟩

/-- **`(0,0)(1,1)(0,0)(1,0)(1,0)` has rank `ε₀ + ω²`.**  Here both parts are
matrices whose rank is already known. -/
theorem rank_sumSqAll : IsWellFounded.rank (bmsAllL 1).Rel sumSqAll
    = Ord.eps0 + Ordinal.omega0 * Ordinal.omega0 := by
  have h : sumSqAll
      = ⟨genAll.1 ++ omegaCol.1 ++ [[1, 0]], appendState_col_len genAll omegaCol rfl⟩ :=
    Subtype.ext rfl
  rw [h, rank_split_mul_omega0 genAll omegaCol rfl rfl (by simp [omegaCol]) rfl rfl,
    rank_genAll, rank_omegaCol]

/-- `(0,0)(1,1)(1,0)(1,0)`. -/
def omegaSqAll : (bmsAllL 1).State := ⟨[[0, 0], [1, 1], [1, 0], [1, 0]], by decide⟩

theorem step_omegaSqAll (N : Nat) :
    (bmsAllL 1).step omegaSqAll N = appendState emptyAll (repNState (N + 1) omegaAll) := by
  refine Subtype.ext ?_
  show expandRL 2 N [[0, 0], [1, 1], [1, 0], [1, 0]]
    = [] ++ repN (N + 1) [[0, 0], [1, 1], [1, 0]]
  rw [expandRL_of_m0_zero 2 N _ 0 rfl rfl (by decide)]
  rfl

/-- **`(0,0)(1,1)(1,0)(1,0)` has rank `ε₀·ω²`.**  The block that repeats is
itself one whose rank was computed this way, so the family goes on. -/
theorem rank_omegaSqAll : IsWellFounded.rank (bmsAllL 1).Rel omegaSqAll
    = Ord.eps0 * Ordinal.omega0 * Ordinal.omega0 := by
  rw [rank_mul_omega0 omegaSqAll emptyAll omegaAll
      (show ¬ ([[0, 0], [1, 1], [1, 0], [1, 0]] : List (List Nat)) = [] by simp) rfl
      (by simp [omegaAll]) step_omegaSqAll, rank_emptyAll, rank_omegaAll, zero_add]

/-- **`(0,0)(1,1)(0,0)(1,0)` has rank `ε₀ + ω`.**  Here the good part is not
empty: the first block stays and the second is the one that repeats. -/
theorem rank_sumAll :
    IsWellFounded.rank (bmsAllL 1).Rel sumAll = Ord.eps0 + Ordinal.omega0 := by
  rw [rank_mul_omega0 sumAll genAll zeroCol (show ¬ ([[0, 0], [1, 1], [0, 0], [1, 0]] : List (List Nat)) = [] by simp) rfl (by simp [zeroCol])
      step_sumAll, rank_genAll, rank_zeroCol, one_mul]

/-! ### The same ordinals, named as terms

The two-row ranks above are values of extended Buchholz terms, so the
question "which ordinal does this matrix name" has an answer in the notation
system for them, not only in the ordinals. -/

theorem rank_genAll_val : IsWellFounded.rank (bmsAllL 1).Rel genAll = val te0 := by
  rw [rank_genAll, val_te0]

theorem rank_omegaCol_val : IsWellFounded.rank (bmsAllL 1).Rel omegaCol = val tw := by
  rw [rank_omegaCol, val_tw]

theorem rank_omegaAll_val : IsWellFounded.rank (bmsAllL 1).Rel omegaAll = val tew := by
  rw [rank_omegaAll, val_tew]

theorem rank_omegaSqAll_val : IsWellFounded.rank (bmsAllL 1).Rel omegaSqAll = val tew2 := by
  rw [rank_omegaSqAll, val_tew2]

theorem rank_omegaSqCol_val : IsWellFounded.rank (bmsAllL 1).Rel omegaSqCol = val tw2 := by
  rw [rank_omegaSqCol, val_tw2]

theorem rank_succAll_val : IsWellFounded.rank (bmsAllL 1).Rel succAll = val te0_one := by
  rw [rank_succAll, val_te0_one]

theorem rank_sumAll_val : IsWellFounded.rank (bmsAllL 1).Rel sumAll = val te0_w := by
  rw [rank_sumAll, val_te0_w]

end Googology.Trans.BMS
