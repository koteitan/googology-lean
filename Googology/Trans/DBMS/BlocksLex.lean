import Googology.Trans.DBMS.BlocksSuff

/-!
# Reaching and the dictionary order on the contents

`BlocksSuff.lean` (`dstdL_iff_dchain`) says that a list of columns is a DBMS
standard form with `r + 1` rows exactly when it is a list of blocks
`blkR M₀ ++ ⋯ ++ blkR Mₖ` whose contents lie in the content system
`CReach r`, each content reached from every earlier one by steps of BM4
(`DChain`).  This file compares "reached" with the dictionary order on the
contents: the order of `List (List Nat)`, a list of columns, each column
compared as a list, a proper prefix counted as smaller (the order `List.lt`
used in `TrioMono.lean`; `≤` is the linear order of Mathlib on lists).

**Proved, at every number of rows:**

* `expandRL_lt_self`: **one step goes down in the dictionary order**,
  `l[N] < l` for every nonempty `l` whose columns have the height of the rule.
  `[0]` removes the last column (a proper prefix); for `N ≥ 1` the expansion
  agrees with `l` up to the last column `c` of `l`, and there it has the first
  column of the first ascended copy of the bad part, which agrees with `c`
  above the row `m₀` and is the bad root's entry `< c[m₀]` at row `m₀`.
* `le_of_rt`, `lt_of_rt`: so **reaching goes down**: if `M` reaches `M'`
  then `M' ≤ M`, and `M' < M` when `M' ≠ M`.  Reaching is antisymmetric
  (`eq_of_rt_of_rt`).
* `dlex_of_dstdL` (**necessary, dictionary form**): a standard form is a list
  of blocks whose contents lie in `CReach r` and do not increase in the
  dictionary order.

**The converse is reduced to one property**, `LexReach r`: a content reaches
every content of `CReach r` below it in the dictionary order.  Equivalent forms:

* `lexReach_iff_total`: reaching is total on `CReach r`;
* `lexReach_iff_lexCof`: `LexCof r`, every content below `M` is at most some
  one-step expansion `M[N]` (the fundamental sequence is cofinal among the
  contents below `M`);
* `lexReach_iff_dstdL_iff_dlex`: **the characterization of standard forms in
  the dictionary order holds exactly when `LexReach r` does.**

Given `LexReach r`: `rt_iff_le` (`M` reaches `M'` iff `M' ≤ M`) and
`dstdL_iff_dlex_of_lexReach` (standard iff the contents do not increase in the
dictionary order).  At three rows these are `dstdL_three_dlex` (necessary,
proved), `rt_iff_le_three_of_lexReach` and `dstdL_three_iff_dlex_of_lexReach`.
**`LexReach 2` is not proved.**  Numerically it holds on the contents of at
most four columns (see `BlocksStd.lean`), and `LexCof 2` holds on the 1157
contents of at most 7 columns found from `cgen 2 n` (`n ≤ 7`) by expansions
`[0]`–`[4]` through lists of at most 7 columns: for all 668746 pairs `X < M`
of them some `M[N]` with `N ≤ 9` is `≥ X`.
-/

namespace Googology.Trans.DBMS

open BM4
open Googology.Notation.DBMS
open Googology.Trans.BMS
open Ordinal Order

/-! ### Entries go down along ancestors -/

theorem ParR_entry_lt {l : List (List Nat)} {k j i : Nat} (h : ParR l k j i) :
    (l[j]!)[k]! < (l[i]!)[k]! := by
  cases k with
  | zero => exact h.2.1
  | succ m => exact h.2.2.1

theorem AncR_entry_lt {l : List (List Nat)} {k j i : Nat} (h : AncR l k j i) :
    (l[j]!)[k]! < (l[i]!)[k]! := by
  induction h with
  | single hp => exact ParR_entry_lt hp
  | tail _ hp ih => exact lt_trans ih (ParR_entry_lt hp)

theorem AncR_of_succ {l : List (List Nat)} {k j i : Nat} (h : AncR l (k + 1) j i) :
    AncR l k j i := by
  induction h with
  | single hp => exact hp.2.1
  | tail _ hp ih => exact ih.trans hp.2.1

theorem AncR_of_le {l : List (List Nat)} {k m j i : Nat} (hkm : k ≤ m) (h : AncR l m j i) :
    AncR l k j i := by
  induction hkm with
  | refl => exact h
  | step _ ih => exact ih (AncR_of_succ (by assumption))

theorem AncR_of_ParR_lt {l : List (List Nat)} {m k j i : Nat} (h : ParR l m j i) (hk : k < m) :
    AncR l k j i := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  exact AncR_of_le (by omega) h.2.1

/-! ### Lists in the dictionary order -/

theorem lt_append_of_ne_nil {α : Type} [LT α] : ∀ (A : List α) {B : List α}, B ≠ [] → A < A ++ B
  | [], B, hB => by
    obtain ⟨b, B', rfl⟩ := List.exists_cons_of_ne_nil hB
    exact List.nil_lt_cons _ _
  | a :: A, B, hB => List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, lt_append_of_ne_nil A hB⟩)

theorem append_lt_append_left' {α : Type} [LT α] : ∀ (p : List α) {x y : List α},
    x < y → p ++ x < p ++ y
  | [], _, _, h => h
  | _ :: p, _, _, h => List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, append_lt_append_left' p h⟩)

/-- Two columns agreeing above row `m` and smaller at row `m`. -/
theorem col_lt_of_getElem! : ∀ (m : Nat) (u v : List Nat), m < u.length → m < v.length →
    (∀ k, k < m → u[k]! = v[k]!) → u[m]! < v[m]! → u < v
  | _, [], _, h, _, _, _ => absurd h (by simp)
  | _, _ :: _, [], _, h, _, _ => absurd h (by simp)
  | 0, a :: u, b :: v, _, _, _, hm => List.cons_lt_cons_iff.mpr (Or.inl hm)
  | m + 1, a :: u, b :: v, hu, hv, hk, hm => by
    have h0 : a = b := hk 0 (by omega)
    refine List.cons_lt_cons_iff.mpr (Or.inr ⟨h0, ?_⟩)
    exact col_lt_of_getElem! m u v (by simpa using hu) (by simpa using hv)
      (fun k hk' => hk (k + 1) (by omega)) hm

/-! ### One step goes down -/

theorem getElem!_append_map_range {α : Type} [Inhabited α] (p n t i : Nat) (g F : Nat → α)
    (ht : t < n) (hi : i = p + t) : ((List.range p).map g ++ (List.range n).map F)[i]! = F t := by
  subst hi
  rw [getElem!_pos _ _ (by simp only [List.length_append, List.length_map, List.length_range]; omega),
    List.getElem_append_right (by simp)]
  simp

theorem expandRL_succ_eq_dropLast_append (r N : Nat) (l : List (List Nat)) {p : Nat}
    (hlen : ∀ v ∈ l, v.length = r) (hb : badRootR r l = some p) :
    ∃ Z, Z ≠ [] ∧ expandRL r (N + 1) l = l.dropLast ++ Z := by
  induction N with
  | zero =>
    obtain ⟨X, hX, he⟩ := expandRL_succ_append r 0 l hb
    exact ⟨X, hX, by rw [he, expandRL_zero r l hlen]⟩
  | succ N ih =>
    obtain ⟨Z, hZ, he⟩ := ih
    obtain ⟨X, _, he'⟩ := expandRL_succ_append r (N + 1) l hb
    exact ⟨Z ++ X, by simp [hZ], by rw [he', he, List.append_assoc]⟩

/-- **One step goes down in the dictionary order.** -/
theorem expandRL_lt_self (r N : Nat) {l : List (List Nat)} (hlen : ∀ v ∈ l, v.length = r)
    (hne : l ≠ []) : expandRL r N l < l := by
  have hlast : l = l.dropLast ++ [l[l.length - 1]!] := by
    have hpos : 0 < l.length := List.length_pos_iff.mpr hne
    conv_lhs => rw [← List.dropLast_append_getLast hne]
    rw [List.getLast_eq_getElem, getElem!_pos l _ (by omega)]
  cases N with
  | zero =>
    rw [expandRL_zero r l hlen]
    conv_rhs => rw [hlast]
    exact lt_append_of_ne_nil _ (by simp)
  | succ N =>
  cases hb : badRootR r l with
  | none =>
    rw [expandRL, hb]
    conv_rhs => rw [hlast]
    exact lt_append_of_ne_nil _ (by simp)
  | some p =>
    have hp : p + 1 < l.length := badRootR_lt hb
    have hpar := badRootR_ParR hb
    set m := m0L r l with hm
    set cl := l[l.length - 1]! with hc
    set s := l.length - 1 - p with hs
    have hspos : 0 < s := by omega
    obtain ⟨Z, hZ, hE⟩ := expandRL_succ_eq_dropLast_append r N l hlen hb
    obtain ⟨z, Z', rfl⟩ := List.exists_cons_of_ne_nil hZ
    -- the column at index `l.length - 1` of the expansion
    have hz : (expandRL r (N + 1) l)[l.length - 1]! = z := by
      have hL : l.length - 1 = l.dropLast.length := by simp
      rw [hE, hL, getElem!_pos _ _ (by simp)]
      simp
    have hz2 : (expandRL r (N + 1) l)[l.length - 1]! =
        (List.range r).map (fun k =>
          if decide (k < m) && ((p == p + s % s) || ancAtR l k p (p + s % s)) then
            (l[p + s % s]!)[k]! + (s / s) * (cl[k]! - (l[p]!)[k]!)
          else (l[p + s % s]!)[k]!) := by
      rw [expandRL, hb]
      dsimp only
      exact getElem!_append_map_range (α := List Nat) p ((N + 1 + 1) * s) s _ _ _
        (lt_of_lt_of_le (by omega : s < 2 * s) (Nat.mul_le_mul_right s (by omega))) (by omega)
    simp only [Nat.mod_self, Nat.div_self hspos, Nat.add_zero, Nat.one_mul] at hz2
    have hcm : (l[p]!)[m]! < cl[m]! := ParR_entry_lt hpar
    have hcl : cl.length = r := hlen cl (getElem!_mem l _ (by omega))
    have hmr : m < r := by
      by_contra hmr
      rw [getElem!_neg cl m (by omega)] at hcm
      exact absurd hcm (Nat.not_lt_zero _)
    have hzc : z < cl := by
      rw [← hz, hz2]
      refine col_lt_of_getElem! m _ cl (by simpa using hmr) (by omega) (fun k hk => ?_) ?_
      · rw [getElem!_map_range_nat, if_pos (by omega)]
        have ha : (l[p]!)[k]! < cl[k]! := AncR_entry_lt (AncR_of_ParR_lt hpar hk)
        rw [if_pos (by simp [hk])]
        omega
      · rw [getElem!_map_range_nat, if_pos hmr]
        simp only [lt_irrefl, decide_false, Bool.false_and]
        simpa using hcm
    rw [hE]
    conv_rhs => rw [hlast]
    exact append_lt_append_left' _ (List.cons_lt_cons_iff.mpr (Or.inl hzc))

theorem expandRL_le_self (r N : Nat) {l : List (List Nat)} (hlen : ∀ v ∈ l, v.length = r) :
    expandRL r N l ≤ l := by
  by_cases hne : l = []
  · subst hne; rw [expandRL_nil]
  · exact le_of_lt (expandRL_lt_self r N hlen hne)

/-! ### Reaching goes down -/

/-- **Reaching goes down in the dictionary order.** -/
theorem rt_lex_le {r : Nat} {M M' : List (List Nat)} (hv : Valid r M)
    (h : Relation.ReflTransGen (CStep r) M M') : M' ≤ M := by
  induction h with
  | refl => exact le_rfl
  | @tail b c hab hs ih =>
    obtain ⟨N, rfl⟩ := hs
    exact le_trans (expandRL_le_self (r + 1) N (rkL_le_of_rt hv hab).2) ih

theorem rt_lex_lt {r : Nat} {M M' : List (List Nat)} (hv : Valid r M)
    (h : Relation.ReflTransGen (CStep r) M M') (hne : M' ≠ M) : M' < M :=
  lt_of_le_of_ne (rt_lex_le hv h) hne

/-- **Reaching is antisymmetric.** -/
theorem eq_of_rt_of_rt {r : Nat} {M M' : List (List Nat)} (hv : Valid r M)
    (h : Relation.ReflTransGen (CStep r) M M') (h' : Relation.ReflTransGen (CStep r) M' M) :
    M = M' :=
  le_antisymm (rt_lex_le ((rkL_le_of_rt hv h).2) h') (rt_lex_le hv h)

/-! ### The converse, as one property -/

/-- **A content reaches every content below it in the dictionary order.** -/
def LexReach (r : Nat) : Prop :=
  ∀ M M', CReach r M → CReach r M' → M' ≤ M → Relation.ReflTransGen (CStep r) M M'

/-- **Reaching is total on the content system.** -/
def ReachTotal (r : Nat) : Prop :=
  ∀ M M', CReach r M → CReach r M' →
    Relation.ReflTransGen (CStep r) M M' ∨ Relation.ReflTransGen (CStep r) M' M

/-- **The fundamental sequence is cofinal**: every content below `M` in the
dictionary order is at most some `M[N]`. -/
def LexCof (r : Nat) : Prop :=
  ∀ M X, CReach r M → CReach r X → X < M → ∃ N, X ≤ expandRL (r + 1) N M

/-- `LexReach r` is the statement "reaching is the dictionary order" on the
content system. -/
theorem lexReach_iff_rt_iff_le (r : Nat) : LexReach r ↔ ∀ M M', CReach r M → CReach r M' →
    (Relation.ReflTransGen (CStep r) M M' ↔ M' ≤ M) :=
  ⟨fun h M M' hM hM' => ⟨rt_lex_le hM.valid, h M M' hM hM'⟩,
    fun h M M' hM hM' => (h M M' hM hM').mpr⟩

/-- **Given `LexReach r`, reaching is the dictionary order.** -/
theorem rt_iff_le {r : Nat} (h : LexReach r) {M M' : List (List Nat)} (hM : CReach r M)
    (hM' : CReach r M') : Relation.ReflTransGen (CStep r) M M' ↔ M' ≤ M :=
  (lexReach_iff_rt_iff_le r).mp h M M' hM hM'

theorem lexReach_iff_total (r : Nat) : LexReach r ↔ ReachTotal r := by
  constructor
  · intro h M M' hM hM'
    rcases le_total M' M with hle | hle
    · exact Or.inl (h M M' hM hM' hle)
    · exact Or.inr (h M' M hM' hM hle)
  · intro h M M' hM hM' hle
    rcases h M M' hM hM' with h1 | h1
    · exact h1
    · have := le_antisymm hle (rt_lex_le hM'.valid h1)
      rw [this]

theorem lexCof_of_lexReach {r : Nat} (h : LexReach r) : LexCof r := by
  intro M X hM hX hlt
  have hrt := h M X hM hX hlt.le
  rcases Relation.ReflTransGen.cases_head hrt with he | ⟨c, ⟨N, rfl⟩, hc⟩
  · exact absurd he (ne_of_gt hlt)
  · exact ⟨N, rt_lex_le (valid_expandRL hM.valid N) hc⟩

theorem lexReach_of_lexCof_aux {r : Nat} (h : LexCof r) (o : Ordinal.{0}) :
    ∀ M M', rkL r M = o → CReach r M → CReach r M' → M' ≤ M →
      Relation.ReflTransGen (CStep r) M M' := by
  induction o using WellFoundedLT.induction with
  | _ o ih =>
  intro M M' ho hM hM' hle
  rcases lt_or_eq_of_le hle with hlt | heq
  · obtain ⟨N, hN⟩ := h M M' hM hM' hlt
    have hne : M ≠ [] := by
      rintro rfl
      exact absurd hlt (List.not_lt_nil _)
    have hlt' : rkL r (expandRL (r + 1) N M) < o := by
      rw [← ho]; exact rkL_lt hM.valid hne N
    exact Relation.ReflTransGen.head ⟨N, rfl⟩
      (ih _ hlt' _ M' rfl (CReach.step N hM) hM' hN)
  · rw [heq]

theorem lexReach_of_lexCof {r : Nat} (h : LexCof r) : LexReach r :=
  fun M M' hM hM' hle => lexReach_of_lexCof_aux h _ M M' rfl hM hM' hle

theorem lexReach_iff_lexCof (r : Nat) : LexReach r ↔ LexCof r :=
  ⟨lexCof_of_lexReach, lexReach_of_lexCof⟩

/-! ### Standard forms in the dictionary order -/

/-- **Contents in the content system that do not increase in the dictionary
order.** -/
def DLex (r : Nat) (Ms : List (List (List Nat))) : Prop :=
  (∀ M ∈ Ms, CReach r M) ∧ Ms.Pairwise (fun a b => b ≤ a)

theorem DChain.dlex {r : Nat} {Ms : List (List (List Nat))} (h : DChain r Ms) : DLex r Ms :=
  ⟨h.1, h.2.imp_of_mem (fun ha _ hab => rt_lex_le (h.1 _ ha).valid hab)⟩

theorem DLex.dchain {r : Nat} (hr : LexReach r) {Ms : List (List (List Nat))} (h : DLex r Ms) :
    DChain r Ms :=
  ⟨h.1, h.2.imp_of_mem (fun ha hb hab => hr _ _ (h.1 _ ha) (h.1 _ hb) hab)⟩

/-- **Necessary, dictionary form**: the contents of a standard form do not
increase in the dictionary order. -/
theorem dlex_of_dstdL {r : Nat} {l : List (List Nat)} (h : DStdL r l) :
    ∃ Ms, DLex r Ms ∧ l = blocksR r Ms := by
  obtain ⟨Ms, hMs, he⟩ := dchain_of_dstdL h
  exact ⟨Ms, hMs.dlex, he⟩

/-- **The characterization in the dictionary order, given `LexReach r`.** -/
theorem dstdL_iff_dlex_of_lexReach {r : Nat} (hr : LexReach r) (l : List (List Nat)) :
    DStdL r l ↔ ∃ Ms, DLex r Ms ∧ l = blocksR r Ms := by
  refine ⟨dlex_of_dstdL, ?_⟩
  rintro ⟨Ms, hMs, rfl⟩
  exact dstdL_of_dchain (hMs.dchain hr)

/-! ### The list of blocks determines the contents -/

/-- Undo `up0` on a nonempty column. -/
def down0 (v : List Nat) : List Nat := (v[0]! - 1) :: v.tail

theorem down0_up0 (v : List Nat) (hv : v ≠ []) : down0 (up0 v) = v := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hv
  simp [down0, up0]

theorem map_up0_inj {r : Nat} {M M' : List (List Nat)} (hM : Valid r M) (hM' : Valid r M')
    (h : M.map up0 = M'.map up0) : M = M' := by
  have e : ∀ X : List (List Nat), Valid r X → (X.map up0).map down0 = X := by
    intro X hX
    rw [List.map_map]
    conv_rhs => rw [← List.map_id X]
    refine List.map_congr_left (fun v hv => ?_)
    exact down0_up0 v (by intro he; have := hX v hv; rw [he] at this; simp at this)
  rw [← e M hM, ← e M' hM', h]

theorem split_up0 : ∀ (A A' R R' : List (List Nat)), (∀ v ∈ A, (v[0]!) ≠ 0) →
    (∀ v ∈ A', (v[0]!) ≠ 0) → (∀ v ∈ R.head?, v[0]! = 0) → (∀ v ∈ R'.head?, v[0]! = 0) →
    A ++ R = A' ++ R' → A = A' ∧ R = R'
  | [], [], _, _, _, _, _, _, h => ⟨rfl, by simpa using h⟩
  | [], a' :: A', R, R', _, hA', hR, _, h => by
    rw [List.nil_append] at h
    subst h
    exact absurd (hR a' rfl) (hA' a' (by simp))
  | a :: A, [], R, R', hA, _, _, hR', h => by
    rw [List.nil_append] at h
    subst h
    exact absurd (hR' a rfl) (hA a (by simp))
  | a :: A, a' :: A', R, R', hA, hA', hR, hR', h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := split_up0 A A' R R' (fun v hv => hA v (by simp [hv]))
      (fun v hv => hA' v (by simp [hv])) hR hR' h.2
    exact ⟨by rw [h.1, h1], h2⟩

theorem blocksR_head (r : Nat) (Ms : List (List (List Nat))) :
    ∀ v ∈ (blocksR r Ms).head?, v[0]! = 0 := by
  intro v hv
  cases Ms with
  | nil => simp at hv
  | cons M Ms =>
    rw [blocksR_cons, blkR] at hv
    simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hv
    rw [← hv, zcol_get]

theorem up0_ne_zero (M : List (List Nat)) : ∀ v ∈ M.map up0, v[0]! ≠ 0 := by
  intro v hv
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hv
  rw [up0_get0]; omega

/-- **The list of blocks determines the contents.** -/
theorem blocksR_inj {r : Nat} : ∀ {Ms Ms' : List (List (List Nat))}, (∀ M ∈ Ms, Valid r M) →
    (∀ M ∈ Ms', Valid r M) → blocksR r Ms = blocksR r Ms' → Ms = Ms'
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp [blkR] at h
  | _ :: _, [], _, _, h => by simp [blkR] at h
  | M :: Ms, M' :: Ms', hv, hv', h => by
    rw [blocksR_cons, blocksR_cons, blkR, blkR, List.cons_append, List.cons_append,
      List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := split_up0 _ _ _ _ (up0_ne_zero M) (up0_ne_zero M')
      (blocksR_head r Ms) (blocksR_head r Ms') h.2
    rw [map_up0_inj (hv M (by simp)) (hv' M' (by simp)) h1,
      blocksR_inj (fun X hX => hv X (by simp [hX])) (fun X hX => hv' X (by simp [hX])) h2]

/-- **The characterization in the dictionary order holds exactly when
`LexReach r` does.** -/
theorem lexReach_iff_dstdL_iff_dlex (r : Nat) :
    LexReach r ↔ ∀ l, DStdL r l ↔ ∃ Ms, DLex r Ms ∧ l = blocksR r Ms := by
  refine ⟨fun h l => dstdL_iff_dlex_of_lexReach h l, fun H M M' hM hM' hle => ?_⟩
  have hd : DLex r [M, M'] := ⟨by
    intro X hX
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl
    · exact hM
    · exact hM', by simpa using hle⟩
  obtain ⟨Ms, hMs, he⟩ := dchain_of_dstdL ((H _).mpr ⟨[M, M'], hd, rfl⟩)
  have hEq := blocksR_inj (r := r) (fun X hX => (hd.1 X hX).valid)
    (fun X hX => (hMs.1 X hX).valid) he
  rw [← hEq] at hMs
  simpa using hMs.2

/-! ### Three rows -/

/-- **Three rows, necessary, dictionary form**: the contents of a standard form
of three-row DBMS lie in `C₃` and do not increase in the dictionary order. -/
theorem dstdL_three_dlex {l : List (List Nat)} (h : DStdL 2 l) :
    ∃ Ms, (∀ M ∈ Ms, CReach 2 M) ∧ Ms.Pairwise (fun a b => b ≤ a) ∧ l = blocksR 2 Ms := by
  obtain ⟨Ms, ⟨h1, h2⟩, he⟩ := dlex_of_dstdL h
  exact ⟨Ms, h1, h2, he⟩

/-- **Three rows: reaching goes down in the dictionary order.** -/
theorem rt_lex_le_three {M M' : List (List Nat)} (hM : CReach 2 M)
    (h : Relation.ReflTransGen (CStep 2) M M') : M' ≤ M :=
  rt_lex_le hM.valid h

/-- **Three rows, given `LexReach 2`: reaching is the dictionary order.** -/
theorem rt_iff_le_three_of_lexReach (h : LexReach 2) {M M' : List (List Nat)}
    (hM : CReach 2 M) (hM' : CReach 2 M') :
    Relation.ReflTransGen (CStep 2) M M' ↔ M' ≤ M :=
  rt_iff_le h hM hM'

/-- **Three rows, given `LexReach 2`: standard iff the contents do not
increase in the dictionary order.** -/
theorem dstdL_three_iff_dlex_of_lexReach (h : LexReach 2) (l : List (List Nat)) :
    DStdL 2 l ↔
      ∃ Ms, (∀ M ∈ Ms, CReach 2 M) ∧ Ms.Pairwise (fun a b => b ≤ a) ∧ l = blocksR 2 Ms := by
  rw [dstdL_iff_dlex_of_lexReach h l]
  constructor
  · rintro ⟨Ms, ⟨h1, h2⟩, he⟩; exact ⟨Ms, h1, h2, he⟩
  · rintro ⟨Ms, h1, h2, he⟩; exact ⟨Ms, ⟨h1, h2⟩, he⟩

/-- **Three rows: the characterization in the dictionary order is equivalent
to `LexReach 2`**, and so to the totality of reaching on `C₃`
(`lexReach_iff_total`) and to the cofinality of the fundamental sequences
(`lexReach_iff_lexCof`). -/
theorem lexReach_two_iff :
    LexReach 2 ↔ ∀ l, DStdL 2 l ↔
      ∃ Ms, (∀ M ∈ Ms, CReach 2 M) ∧ Ms.Pairwise (fun a b => b ≤ a) ∧ l = blocksR 2 Ms := by
  rw [lexReach_iff_dstdL_iff_dlex]
  refine forall_congr' (fun l => iff_congr Iff.rfl ?_)
  constructor
  · rintro ⟨Ms, ⟨h1, h2⟩, he⟩; exact ⟨Ms, h1, h2, he⟩
  · rintro ⟨Ms, h1, h2, he⟩; exact ⟨Ms, ⟨h1, h2⟩, he⟩

end Googology.Trans.DBMS
