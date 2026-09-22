import Googology.Trans.BMS.Zero

/-!
# A row of zeros underneath, at every number of rows

`BMS/Zero.lean` says a row of zeros underneath changes nothing, for one row
inside two.  This file says the same at every number of rows, and on the
entries, where the rule runs: `expandRL_zeroRow`.

The argument is the one `BMS/Zero.lean` makes, with the row number a variable.
Row `r`'s entries are all `0`, so no column has a parent there, so `m₀` is
unchanged and the bad root is the same column; every row below `r` sees the
same entries and the same ancestors, so the column map is the same; and row
`r` of the result is `0` again because `m₀ < r` sends it to the copy.

`bmsL_homSucc` and `bmsAllL_homSucc` are what come out — `bmsL r` inside
`bmsL (r + 1)`, standard matrices and all matrices.  The standard side needs
one more fact, `expandRL_gen`: the generator `(0,…,0)(1,…,1)` with `r + 2`
rows expands at `N` to `(0,…,0)(1,…,1)⋯(N,…,N)` with `r + 1` rows and a row of
zeros underneath.  So the zero row of a standard matrix is standard too, by
induction over reachability.

Iterating the step gives `bmsL_simLe`: `r ≤ s` puts `bmsL r` inside `bmsL s`,
with `s - r` rows of zeros underneath, which `bmsL_simAdd_map` states.
-/

namespace Googology.Trans.BMS

open BM4 Pat

/-! ### Writing the row -/

/-- A matrix with a row of zeros underneath. -/
def zeroRow (l : List (List Nat)) : List (List Nat) := l.map (fun c => c ++ [0])

@[simp] theorem zeroRow_length (l : List (List Nat)) : (zeroRow l).length = l.length := by
  rw [zeroRow, List.length_map]

theorem zeroRow_nil_iff (l : List (List Nat)) : zeroRow l = [] ↔ l = [] := by
  rw [zeroRow, List.map_eq_nil_iff]

theorem zeroRow_append (x y : List (List Nat)) : zeroRow (x ++ y) = zeroRow x ++ zeroRow y := by
  rw [zeroRow, zeroRow, zeroRow, List.map_append]

theorem zeroRow_map {α : Type} (f : α → List Nat) (s : List α) :
    zeroRow (s.map f) = s.map (fun a => f a ++ [0]) := by
  rw [zeroRow, List.map_map]
  rfl

theorem zeroRow_col_len {r : Nat} {l : List (List Nat)} (h : ∀ c ∈ l, c.length = r) :
    ∀ c ∈ zeroRow l, c.length = r + 1 := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  rw [List.length_append, h d hd]
  rfl

/-- Below row `r`, the entries are the ones that were there. -/
theorem zeroRow_getElem {r : Nat} {l : List (List Nat)} (h : ∀ c ∈ l, c.length = r)
    {k : Nat} (hk : k < r) (i : Nat) : ((zeroRow l)[i]!)[k]! = (l[i]!)[k]! := by
  by_cases hi : i < l.length
  · have hlen : (l[i]!).length = r := h _ (getElem!_mem l i hi)
    rw [zeroRow, getElem!_map _ l i hi,
      getElem!_pos (l[i]! ++ [0]) k (by rw [List.length_append, hlen]; omega),
      getElem!_pos (l[i]!) k (by rw [hlen]; exact hk),
      List.getElem_append_left (by rw [hlen]; exact hk)]
  · rw [getElem!_neg (zeroRow l) i (by rw [zeroRow_length]; exact hi), getElem!_neg l i hi]

/-- Row `r` is `0`. -/
theorem zeroRow_getElem_last {r : Nat} {l : List (List Nat)} (h : ∀ c ∈ l, c.length = r)
    (i : Nat) : ((zeroRow l)[i]!)[r]! = 0 := by
  by_cases hi : i < l.length
  · have hlen : (l[i]!).length = r := h _ (getElem!_mem l i hi)
    rw [zeroRow, getElem!_map _ l i hi,
      getElem!_pos (l[i]! ++ [0]) r (by rw [List.length_append, hlen]; simp),
      List.getElem_append_right (Nat.le_of_eq hlen)]
    simp
  · rw [getElem!_neg (zeroRow l) i (by rw [zeroRow_length]; exact hi)]
    rfl

/-! ### The rule does not see it -/

/-- A parent is strictly above its child, in its own row. -/
theorem ParR_entry {l : List (List Nat)} {k j i : Nat} (h : ParR l k j i) :
    (l[j]!)[k]! < (l[i]!)[k]! := by
  cases k with
  | zero => rw [ParR] at h; exact h.2.1
  | succ m => rw [ParR] at h; exact h.2.2.1

/-- **Below row `r`, the parent is the parent it was.** -/
theorem parAtR_zeroRow {r : Nat} {l : List (List Nat)} (h : ∀ c ∈ l, c.length = r) :
    ∀ k, k < r → parAtR (zeroRow l) k = parAtR l k := by
  intro k
  induction k with
  | zero =>
    intro hk
    funext i
    simp only [parAtR, zeroRow_getElem h hk]
  | succ m ih =>
    intro hk
    have hm := ih (by omega)
    funext i
    simp only [parAtR, hm, zeroRow_getElem h hk]

/-- **In row `r` there is no parent**, because every entry there is `0`. -/
theorem parAtR_zeroRow_last {r : Nat} {l : List (List Nat)} (h : ∀ c ∈ l, c.length = r)
    (i : Nat) : parAtR (zeroRow l) r i = none := by
  by_contra hc
  obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hc
  have hlt := ParR_entry ((parAtR_eq_some _ _ _ _).mp hj)
  rw [zeroRow_getElem_last h, zeroRow_getElem_last h] at hlt
  omega

theorem ancAtR_zeroRow {r : Nat} {l : List (List Nat)} (h : ∀ c ∈ l, c.length = r)
    {k : Nat} (hk : k < r) (p i : Nat) : ancAtR (zeroRow l) k p i = ancAtR l k p i := by
  rw [ancAtR, ancAtR, parAtR_zeroRow h k hk]

theorem m0L_lt {r : Nat} (hr : 0 < r) (l : List (List Nat)) : m0L r l < r := by
  have h1 : m0L r l ≤ r - 1 := Nat.findGreatest_le (r - 1)
  omega

/-- **The maximal parent row is unchanged.** -/
theorem m0L_zeroRow {r : Nat} (hr : 0 < r) {l : List (List Nat)} (h : ∀ c ∈ l, c.length = r) :
    m0L (r + 1) (zeroRow l) = m0L r l := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  rw [m0L, m0L, show m + 1 + 1 - 1 = m + 1 from rfl, show m + 1 - 1 = m from rfl,
    Nat.findGreatest, if_neg (by rw [parAtR_zeroRow_last h]; simp)]
  exact findGreatest_congr m (fun k hk => by
    rw [parAtR_zeroRow h k (by omega), zeroRow_length])

/-- **And so is the bad root.** -/
theorem badRootR_zeroRow {r : Nat} (hr : 0 < r) {l : List (List Nat)}
    (h : ∀ c ∈ l, c.length = r) : badRootR (r + 1) (zeroRow l) = badRootR r l := by
  rw [badRootR, badRootR]
  by_cases he : l.isEmpty
  · rw [if_pos he, if_pos (show (zeroRow l).isEmpty = true by
      simp only [List.isEmpty_iff] at he ⊢
      rw [zeroRow_nil_iff]
      exact he)]
  · rw [if_neg he, if_neg (show ¬ (zeroRow l).isEmpty = true by
      simp only [List.isEmpty_iff] at he ⊢
      intro hz
      exact he ((zeroRow_nil_iff l).mp hz)),
      m0L_zeroRow hr h, zeroRow_length, parAtR_zeroRow h _ (m0L_lt hr l)]

/-- **A row of zeros underneath changes nothing**, at every number of rows. -/
theorem expandRL_zeroRow {r : Nat} (hr : 0 < r) (N : Nat) (l : List (List Nat))
    (h : ∀ c ∈ l, c.length = r) :
    expandRL (r + 1) N (zeroRow l) = zeroRow (expandRL r N l) := by
  cases hb : badRootR r l with
  | none =>
    rw [expandRL, badRootR_zeroRow hr h, hb]
    conv_rhs => rw [expandRL, hb]
    dsimp only
    rw [zeroRow, zeroRow, List.map_dropLast]
  | some p =>
    have hp : p + 1 < l.length := badRootR_lt hb
    rw [expandRL, badRootR_zeroRow hr h, hb]
    conv_rhs => rw [expandRL, hb]
    dsimp only
    rw [zeroRow_length, m0L_zeroRow hr h, zeroRow_append, zeroRow_map, zeroRow_map]
    congr 1
    · refine List.map_congr_left (fun i hi => ?_)
      rw [zeroRow, getElem!_map _ l i (by have := List.mem_range.mp hi; omega)]
    · refine List.map_congr_left (fun t _ => ?_)
      rw [List.range_succ, List.map_append, List.map_singleton]
      congr 1
      · refine List.map_congr_left (fun k hk0 => ?_)
        have hk : k < r := List.mem_range.mp hk0
        simp only [zeroRow_getElem h hk, ancAtR_zeroRow h hk]
      · rw [show decide (r < m0L r l) = false from
          decide_eq_false (by have := m0L_lt hr l; omega), Bool.false_and,
          if_neg (by simp), zeroRow_getElem_last h]

/-! ### The generator -/

theorem getElem!_replicate {a n k : Nat} (hk : k < n) : (List.replicate n a)[k]! = a := by
  rw [getElem!_pos _ k (by rw [List.length_replicate]; exact hk), List.getElem_replicate]

/-- In the generator `(0,…,0)(1,…,1)`, column `0` is the parent of column `1`
in every row. -/
theorem parR_gen (s : Nat) : ∀ k, k < s →
    ParR [List.replicate s 0, List.replicate s 1] k 0 1 := by
  intro k
  induction k with
  | zero =>
    intro hk
    rw [ParR]
    refine ⟨by omega, ?_, fun j' a b => by omega⟩
    show (List.replicate s 0)[0]! < (List.replicate s 1)[0]!
    rw [getElem!_replicate hk, getElem!_replicate hk]
    omega
  | succ m ih =>
    intro hk
    rw [ParR]
    refine ⟨by omega, Relation.TransGen.single (ih (by omega)), ?_, fun j' a b _ => by omega⟩
    show (List.replicate s 0)[m + 1]! < (List.replicate s 1)[m + 1]!
    rw [getElem!_replicate hk, getElem!_replicate hk]
    omega

theorem m0L_gen (s : Nat) (hs : 0 < s) :
    m0L s [List.replicate s 0, List.replicate s 1] = s - 1 := by
  have hsome : (parAtR [List.replicate s 0, List.replicate s 1] (s - 1)
      (([List.replicate s 0, List.replicate s 1] : List (List Nat)).length - 1)).isSome = true := by
    rw [show (([List.replicate s 0, List.replicate s 1] : List (List Nat)).length - 1) = 1 from rfl,
      Option.isSome_iff_exists]
    exact ⟨0, (parAtR_eq_some _ _ _ _).mpr (parR_gen s (s - 1) (by omega))⟩
  have hle : s - 1 ≤ m0L s [List.replicate s 0, List.replicate s 1] :=
    Nat.le_findGreatest (Nat.le_refl _) hsome
  have hge : m0L s [List.replicate s 0, List.replicate s 1] ≤ s - 1 :=
    Nat.findGreatest_le (s - 1)
  omega

theorem badRootR_gen (s : Nat) (hs : 0 < s) :
    badRootR s [List.replicate s 0, List.replicate s 1] = some 0 := by
  rw [badRootR, if_neg (by simp), m0L_gen s hs,
    show (([List.replicate s 0, List.replicate s 1] : List (List Nat)).length - 1) = 1 from rfl,
    parAtR_eq_some]
  exact parR_gen s (s - 1) (by omega)

theorem map_range_succ_ite (s t : Nat) :
    (List.range (s + 1)).map (fun k => if k < s then t else 0) = List.replicate s t ++ [0] := by
  rw [List.range_succ, List.map_append, List.map_singleton, if_neg (Nat.lt_irrefl s)]
  congr 1
  rw [List.map_congr_left (g := fun _ => t) (fun k hk => if_pos (List.mem_range.mp hk)),
    List.map_const', List.length_range]

/-- **The generator with `s + 1` rows expands to the generators with `s` rows,
with a row of zeros underneath.** -/
theorem expandRL_gen (s N : Nat) (hs : 0 < s) :
    expandRL (s + 1) N [List.replicate (s + 1) 0, List.replicate (s + 1) 1]
      = zeroRow ((List.range (N + 1)).map (fun i => List.replicate s i)) := by
  rw [expandRL, badRootR_gen (s + 1) (by omega), zeroRow_map]
  dsimp only
  rw [show (([List.replicate (s + 1) 0, List.replicate (s + 1) 1] : List (List Nat)).length
      - 1 - 0) = 1 from rfl, List.range_zero, List.map_nil, List.nil_append, Nat.mul_one,
    m0L_gen (s + 1) (by omega), show s + 1 - 1 = s from rfl]
  refine List.map_congr_left (fun t _ => ?_)
  rw [← map_range_succ_ite s t]
  refine List.map_congr_left (fun k hk0 => ?_)
  have hk : k < s + 1 := List.mem_range.mp hk0
  rw [show t % 1 = 0 from Nat.mod_one t, Nat.add_zero]
  by_cases hks : k < s
  · rw [if_pos (by rw [decide_eq_true hks]; rfl), if_pos hks]
    show (List.replicate (s + 1) 0)[k]! + t / 1 * ((List.replicate (s + 1) 1)[k]!
      - (List.replicate (s + 1) 0)[k]!) = t
    rw [getElem!_replicate hk, getElem!_replicate hk, Nat.div_one]
    omega
  · rw [if_neg (by
      rw [show decide (k < s) = false from decide_eq_false hks, Bool.false_and]
      simp), if_neg hks]
    show (List.replicate (s + 1) 0)[k]! = 0
    rw [getElem!_replicate hk]

/-! ### The systems -/

/-- **A standard matrix with a row of zeros underneath is standard.** -/
theorem exists_std_zeroRow (r : Nat) : ∀ A : Arr (r + 1), Std (r + 1) A →
    ∃ B : Arr (r + 2), Std (r + 2) B ∧ entriesR B = zeroRow (entriesR A) := by
  intro A hA
  induction hA with
  | init n =>
    refine ⟨expand (stair (r + 2) 1) n, Std.step n (Std.init 1), ?_⟩
    rw [entriesR_expand (by omega), entriesR_stair, entriesR_stair,
      show (List.range 2).map (fun i => List.replicate (r + 2) i)
        = [List.replicate (r + 2) 0, List.replicate (r + 2) 1] from rfl,
      show r + 2 = (r + 1) + 1 from rfl, expandRL_gen (r + 1) n (by omega)]
  | @step A0 N _ ih =>
    obtain ⟨B, hB, hE⟩ := ih
    refine ⟨expand B N, Std.step N hB, ?_⟩
    rw [entriesR_expand (by omega), hE,
      expandRL_zeroRow (r := r + 1) (by omega) N (entriesR A0) (entriesR_col_len A0),
      entriesR_expand (by omega)]

/-- **Bashicu matrices with `r + 1` rows sit inside those with `r + 2`
rows**, by writing a row of zeros underneath.  The brackets are not
renumbered. -/
def bmsL_homSucc (r : Nat) : StepHom (bmsL r) (bmsL (r + 1)) where
  map := fun l => ⟨zeroRow l.1, by
    obtain ⟨A, hA, hE⟩ := l.2
    obtain ⟨B, hB, hEB⟩ := exists_std_zeroRow r A hA
    exact ⟨B, hB, by rw [hEB, hE]⟩⟩
  reindex := id
  map_step := fun l N => Subtype.ext (by
    obtain ⟨A, _, hE⟩ := l.2
    exact (expandRL_zeroRow (r := r + 1) (by omega) N l.1
      (by rw [← hE]; exact entriesR_col_len A)).symm)
  map_halted := fun l h => (zeroRow_nil_iff l.1).mp h

/-- **And so do all matrices**, standard or not. -/
def bmsAllL_homSucc (r : Nat) : StepHom (bmsAllL r) (bmsAllL (r + 1)) where
  map := fun l => ⟨zeroRow l.1, zeroRow_col_len l.2⟩
  reindex := id
  map_step := fun l N =>
    Subtype.ext (expandRL_zeroRow (r := r + 1) (by omega) N l.1 l.2).symm
  map_halted := fun l h => (zeroRow_nil_iff l.1).mp h

/-! ### The whole hierarchy -/

/-- **`r + 1` rows sit inside `r + d + 1`**, by writing `d` rows of zeros
underneath. -/
def bmsL_simAdd (r : Nat) : ∀ d : Nat, Sim (bmsL r) (bmsL (r + d))
  | 0 => Sim.refl _
  | d + 1 => (bmsL_simAdd r d).comp (bmsL_homSucc (r + d)).toSim

/-- And that is what the map does. -/
theorem bmsL_simAdd_map (r : Nat) : ∀ (d : Nat) (l : (bmsL r).State),
    ((bmsL_simAdd r d).map l).1 = zeroRow^[d] l.1 := by
  intro d
  induction d with
  | zero => intro l; rfl
  | succ m ih =>
    intro l
    rw [Function.iterate_succ_apply', ← ih l]
    rfl

/-- **So the number of rows only goes up.** -/
def bmsL_simLe {r s : Nat} (h : r ≤ s) : Sim (bmsL r) (bmsL s) :=
  Nat.add_sub_cancel' h ▸ bmsL_simAdd r (s - r)

/-- The same for all matrices, standard or not. -/
def bmsAllL_simAdd (r : Nat) : ∀ d : Nat, Sim (bmsAllL r) (bmsAllL (r + d))
  | 0 => Sim.refl _
  | d + 1 => (bmsAllL_simAdd r d).comp (bmsAllL_homSucc (r + d)).toSim

/-- And the same conclusion. -/
def bmsAllL_simLe {r s : Nat} (h : r ≤ s) : Sim (bmsAllL r) (bmsAllL s) :=
  Nat.add_sub_cancel' h ▸ bmsAllL_simAdd r (s - r)

end Googology.Trans.BMS
