/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/ControlDominates.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Control
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Bridge
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.VerticalRoots
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.CanonicalFrontier
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Domain

set_option backward.do.legacy false

/-!
# Proof of `ControlDominates`

For a node `u` of a column with a left leg, let `q = Q(u)` be the highest node of the leg
column whose row is at most the row of `u` (`Frame.Q`; this is the node that
`Reserve.highestAtMost` reads). The key of the leg atom of `u` is the template

  `K(u)[k] = col(root_k(q))` if `jump(row u, row q) ≤ k`, and `⊤` otherwise

(scales `k = D, …, 0`, compared lexicographically from scale `D`). For a real node `u`
with an upper neighbour `v` and raw parent `p` (the real edge `u → p`, key `E(u)`):

* (A) `K(u) ≤ E(u)` pointwise: `p` is reached from `q` along the numerical parent search,
  so `row p ≤ row q ≤ row u`, `jump(u, q) ≤ jump(u, p) = d`, and for `k ≥ d`,
  `col(root_k(q)) ≤ col(root_k(u)) = col(root_k(p))` (`scaleRoot_candidate_column_le`).
* (B) `E(u) < K(v)`: `Q(v)` lies in the column of `p` at or above `p`, `row v = row u + ω^d`
  and `jump(p, v) = d + 1`; Phyrion's strong vertical theorem (`Normal.rootVertical`)
  compares the root prefixes of `p` and `Q(v)`.

Hence the leg keys strictly increase up every column (`leg_lt_above`), and every leg atom
of the last column below the top has a key below the control, which is the key of the leg
atom of the top node (`controlDominates`).
-/

namespace OmegaY.Official.Classification.ControlProof

open Canonical Reserve Official Descent Geometry

/-! ## Keys given by an entry function -/

/-- The key template with entry `f k` at scale `k` (entries listed from scale `D`). -/
def genKey (D : Nat) (f : Nat → Option Nat) : RawKey := (List.range (D + 1)).reverse.map f

theorem genKey_get {D i : Nat} (f : Nat → Option Nat) (hi : i < D + 1) :
    (genKey D f)[i]? = some (f (D - i)) := by
  unfold genKey
  rw [List.getElem?_map, List.getElem?_reverse (by simp only [List.length_range]; omega),
    List.length_range, List.getElem?_range (by omega)]
  rw [show D + 1 - 1 - i = D - i by omega]
  rfl

theorem keyLt_genKey {D k : Nat} {f g : Nat → Option Nat} (hk : k ≤ D)
    (hhi : ∀ k', k < k' → k' ≤ D → f k' = g k') (hlt : entryLt (f k) (g k) = true) :
    keyLt (D + 1) (genKey D f) (genKey D g) = true := by
  apply keyLt_spec.mpr
  refine ⟨D - k, by omega, ?_, ?_⟩
  · intro j hj
    rw [genKey_get f (by omega), genKey_get g (by omega), hhi (D - j) (by omega) (by omega)]
  · rw [genKey_get f (by omega), genKey_get g (by omega)]
    simp only [Option.getD_some]
    rw [show D - (D - k) = k by omega]
    exact hlt

/-- The order of key entries, `⊤ = none` largest. -/
def EntryLe (x y : Option Nat) : Prop := x = y ∨ entryLt x y = true

theorem entryLe_none (x : Option Nat) : EntryLe x none := by
  cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem entryLe_some {a b : Nat} (h : a ≤ b) : EntryLe (some a) (some b) := by
  rcases Nat.lt_or_eq_of_le h with h | h
  · exact Or.inr (by simp [entryLt, h])
  · exact Or.inl (by rw [h])

/-- Pointwise comparison of entries gives the lexicographic comparison. -/
theorem keyLe_genKey {D : Nat} {f g : Nat → Option Nat}
    (h : ∀ k, k ≤ D → EntryLe (f k) (g k)) :
    keyLe (D + 1) (genKey D f) (genKey D g) = true := by
  unfold keyLe
  by_cases hall : ∀ k, k ≤ D → f k = g k
  · have hEq : keyEq (D + 1) (genKey D f) (genKey D g) = true := by
      apply keyEq_spec.mpr
      intro j hj
      rw [genKey_get f hj, genKey_get g hj, hall _ (by omega)]
    simp [hEq]
  · have hex : ∃ i, i < D + 1 ∧ f (D - i) ≠ g (D - i) := by
      apply Classical.byContradiction
      intro hn
      apply hall
      intro k hk
      by_contra hne
      exact hn ⟨D - k, by omega, by rwa [show D - (D - k) = k by omega]⟩
    classical
    have hi : Nat.find hex < D + 1 ∧ f (D - Nat.find hex) ≠ g (D - Nat.find hex) :=
      Nat.find_spec hex
    have hmin : ∀ j, j < Nat.find hex → f (D - j) = g (D - j) := by
      intro j hj
      by_contra hne
      exact Nat.find_min hex hj ⟨by omega, hne⟩
    have hlt : keyLt (D + 1) (genKey D f) (genKey D g) = true := by
      apply keyLt_spec.mpr
      refine ⟨Nat.find hex, hi.1, ?_, ?_⟩
      · intro j hj
        rw [genKey_get f (by omega), genKey_get g (by omega), hmin j hj]
      · rw [genKey_get f hi.1, genKey_get g hi.1]
        simp only [Option.getD_some]
        rcases h (D - Nat.find hex) (by omega) with he | hl
        · exact absurd he hi.2
        · exact hl
    simp [hlt]

/-! ## Leg keys in a normal frame -/

section FrameKeys

variable {F : Frame}

/-- The entry at scale `k` of the key of a hypothetical edge from a row `h` to `q`. -/
def fent (hF : F.Ordered) (h : Row) (q : F.Node) (k : Nat) : Option Nat :=
  if Row.jump h (F.height q) ≤ k then some (Frame.scaleRoot hF k q).1.val else none

theorem height_le_of_index (hF : F.Ordered) {a b : F.Node} (hc : a.1 = b.1)
    (hi : a.2.val ≤ b.2.val) : F.height a ≤ F.height b := by
  rcases a with ⟨c, i⟩
  rcases b with ⟨d, j⟩
  dsimp only at hc hi
  subst d
  exact (hF.rows_strict c).monotone hi

theorem height_lt_of_index (hF : F.Ordered) {a b : F.Node} (hc : a.1 = b.1)
    (hi : a.2.val < b.2.val) : F.height a < F.height b := by
  rcases a with ⟨c, i⟩
  rcases b with ⟨d, j⟩
  dsimp only at hc hi
  subst d
  exact hF.rows_strict c hi

theorem node_eq_of_index {a b : F.Node} (hc : a.1 = b.1) (hi : a.2.val = b.2.val) : a = b := by
  rcases a with ⟨c, i⟩
  rcases b with ⟨d, j⟩
  dsimp only at hc hi
  subst d
  obtain rfl := Fin.ext hi
  rfl

theorem upper_eq_of_index {u v : F.Node} (hc : u.1 = v.1) (hi : v.2.val = u.2.val + 1) :
    F.upper u = some v := by
  rcases u with ⟨c, i⟩
  rcases v with ⟨d, j⟩
  dsimp only at hc hi
  subst d
  have hlt : i.val + 1 < F.length c := by rw [← hi]; exact j.isLt
  have he : j = ⟨i.val + 1, hlt⟩ := Fin.ext hi
  simp only [Frame.upper, dif_pos hlt, he]

/-- (A) The leg key of `u` is pointwise at most the key of the real edge from `u`. -/
theorem leg_le_edge (hF : F.Normal) {u p q : F.Node} (hReal : Frame.Real u)
    (hRaw : F.rawParent u = some p) (hQ : F.Q u = some q) (k : Nat) :
    EntryLe (fent hF.toOrdered (F.height u) q k) (fent hF.toOrdered (F.height u) p k) := by
  have hP : F.P u = some p := (hF.rawParent_eq_P hReal).symm.trans hRaw
  obtain ⟨q', hQ', trace⟩ := (Frame.P_iff hF.toOrdered).mp hP
  have hqq : q' = q := Option.some.inj (hQ'.symm.trans hQ)
  subst hqq
  have hpq := trace.height_le hF.toOrdered
  have hqu := Frame.Q_height_le hF.toOrdered hQ
  have hJ : Row.jump (F.height u) (F.height q') ≤ Row.jump (F.height u) (F.height p) := by
    have := (Row.jump_le_between hpq hqu (d := Row.jump (F.height u) (F.height p))
      (by rw [Row.jump_comm])).2
    rwa [Row.jump_comm] at this
  unfold fent
  by_cases hk : Row.jump (F.height u) (F.height p) ≤ k
  · rw [if_pos hk, if_pos (hJ.trans hk)]
    apply entryLe_some
    rw [← Frame.scaleRoot_eq_of_raw hF.toOrdered hRaw hk]
    exact hF.scaleRoot_candidate_column_le hReal hQ k
  · rw [if_neg hk]
    exact entryLe_none _

/-- (B) The key of the real edge from `u` is below the leg key of the node above `u`. -/
theorem edge_lt_leg (hF : F.Normal) {D : Nat}
    (hSup : ∀ w : F.Node, ∀ i, D < i → Row.coeff (F.height w) i = 0)
    {u v p q : F.Node} (hReal : Frame.Real u) (hUp : F.upper u = some v)
    (hRaw : F.rawParent u = some p) (hQ : F.Q v = some q) :
    keyLt (D + 1) (genKey D (fent hF.toOrdered (F.height u) p))
      (genKey D (fent hF.toOrdered (F.height v) q)) = true := by
  have hO := hF.toOrdered
  obtain ⟨p', hP', hRow, _, hStored⟩ := hF.upper_step u v hReal hUp
  have hpp : p' = p :=
    Option.some.inj (((hF.rawParent_eq_P hReal).trans hP').symm.trans hRaw)
  rw [hpp] at hP' hRow hStored
  have hPReal : Frame.Real p := Frame.real_of_value_pos hO (Frame.P_value hO hP').1
  have hdD : Row.jump (F.height u) (F.height p) ≤ D :=
    (Frame.RealStoredEdge.mk u v p hReal hUp hRaw).degree_le hF.rawRowGeometry (hSup v)
  obtain ⟨left, hLeftStored, _, _, hqcol, hidx, hqv, _⟩ := Frame.Q_spec hO hQ
  have hleft : left = p := by
    apply Option.some.inj
    rw [← F.lookup_ref left, ← F.lookup_ref p]
    exact congrArg F.lookup (Option.some.inj (hLeftStored.symm.trans hStored))
  rw [hleft] at hqcol hidx
  have hpq : F.height p ≤ F.height q := height_le_of_index hO hqcol.symm hidx
  have hPV : Row.jump (F.height p) (F.height v) = Row.jump (F.height u) (F.height p) + 1 := by
    rw [hRow]
    unfold Row.B
    rw [Row.bump_eq_of_jump_le (le_refl (Row.jump (F.height u) (F.height p)))]
    exact Row.jump_bump _ _
  have hmax := Row.jump_max hpq hqv
  have hsomeP : ∀ k, Row.jump (F.height u) (F.height p) ≤ k →
      fent hO (F.height u) p k = some (Frame.scaleRoot hO k p).1.val := by
    intro k hk
    unfold fent
    rw [if_pos hk]
  have hsomeQ : ∀ k, Row.jump (F.height q) (F.height v) ≤ k →
      fent hO (F.height v) q k = some (Frame.scaleRoot hO k q).1.val := by
    intro k hk
    unfold fent
    rw [if_pos (by rw [Row.jump_comm]; exact hk)]
  by_cases hJ : Row.jump (F.height q) (F.height v) ≤ Row.jump (F.height u) (F.height p)
  · -- `p` lies strictly below `Q(v)` and their rows differ at exponent `d`
    have hpqJ : Row.jump (F.height p) (F.height q) = Row.jump (F.height u) (F.height p) + 1 := by
      omega
    have hidx' : p.2.val < q.2.val := by
      rcases Nat.lt_or_eq_of_le hidx with h | h
      · exact h
      · exfalso
        have he := node_eq_of_index hqcol.symm h
        rw [he, Row.jump_self] at hpqJ
        omega
    have hVert := hF.rootVertical hSup hPReal hqcol.symm hidx'
      (Row.jump (F.height u) (F.height p)) (by omega)
    obtain ⟨i, hdi, hiD, hHigher, hAt⟩ := Frame.rootPrefix_lt_witness hO hVert
    apply keyLt_genKey hiD
    · intro k' hk' hk'D
      rw [hsomeP k' (by omega), hsomeQ k' (by omega), hHigher k' hk' hk'D]
    · rw [hsomeP i hdi, hsomeQ i (by omega)]
      simpa [entryLt] using hAt
  · have hJeq : Row.jump (F.height q) (F.height v) = Row.jump (F.height u) (F.height p) + 1 := by
      omega
    have hnoneQ : fent hO (F.height v) q (Row.jump (F.height u) (F.height p)) = none := by
      unfold fent
      rw [if_neg (by rw [Row.jump_comm]; omega)]
    by_cases heq : ∀ k', Row.jump (F.height u) (F.height p) < k' → k' ≤ D →
        (Frame.scaleRoot hO k' p).1 = (Frame.scaleRoot hO k' q).1
    · apply keyLt_genKey hdD
      · intro k' hk' hk'D
        rw [hsomeP k' (by omega), hsomeQ k' (by omega), heq k' hk' hk'D]
      · rw [hsomeP _ (le_refl _), hnoneQ]
        rfl
    · have hidx' : p.2.val < q.2.val := by
        rcases Nat.lt_or_eq_of_le hidx with h | h
        · exact h
        · exfalso
          have he := node_eq_of_index hqcol.symm h
          exact heq (fun k' _ _ => by rw [he])
      have hpos : 0 < Row.jump (F.height p) (F.height q) := by
        have hlt := height_lt_of_index hO hqcol.symm hidx'
        exact Nat.pos_of_ne_zero (fun h0 => ne_of_lt hlt (Row.jump_eq_zero.mp h0))
      have hVert := hF.rootVertical hSup hPReal hqcol.symm hidx' 0 hpos
      have hle := Frame.rootPrefix_le_coarser hO
        (Nat.zero_le (Row.jump (F.height u) (F.height p) + 1)) hVert.le
      have hlt : Frame.rootPrefix hO D (Row.jump (F.height u) (F.height p) + 1) p <
          Frame.rootPrefix hO D (Row.jump (F.height u) (F.height p) + 1) q := by
        refine lt_of_le_of_ne hle ?_
        intro he
        apply heq
        intro k' hk' hk'D
        have hc := congrArg (fun r => Row.coeff r k') he
        simp only [Frame.coeff_rootPrefix] at hc
        rw [if_pos ⟨by omega, hk'D⟩, if_pos ⟨by omega, hk'D⟩] at hc
        exact Fin.ext hc
      obtain ⟨i, hdi, hiD, hHigher, hAt⟩ := Frame.rootPrefix_lt_witness hO hlt
      apply keyLt_genKey hiD
      · intro k' hk' hk'D
        rw [hsomeP k' (by omega), hsomeQ k' (by omega), hHigher k' hk' hk'D]
      · rw [hsomeP i (by omega), hsomeQ i (by omega)]
        simpa [entryLt] using hAt

/-- (C) The leg key of `u` is below the leg key of the node above `u`. -/
theorem leg_lt_upper (hF : F.Normal) {D : Nat}
    (hSup : ∀ w : F.Node, ∀ i, D < i → Row.coeff (F.height w) i = 0)
    {u v qu qv : F.Node} (hReal : Frame.Real u) (hUp : F.upper u = some v)
    (hQu : F.Q u = some qu) (hQv : F.Q v = some qv) :
    keyLt (D + 1) (genKey D (fent hF.toOrdered (F.height u) qu))
      (genKey D (fent hF.toOrdered (F.height v) qv)) = true := by
  obtain ⟨p, hP, _, _, _⟩ := hF.upper_step u v hReal hUp
  have hRaw : F.rawParent u = some p := (hF.rawParent_eq_P hReal).trans hP
  exact keyLt_of_keyLe_of_keyLt
    (keyLe_genKey (fun k _ => leg_le_edge hF hReal hRaw hQu k))
    (edge_lt_leg hF hSup hReal hUp hRaw hQv)

/-- (D) The leg keys strictly increase up every column. -/
theorem leg_lt_above (hF : F.Normal) {D : Nat}
    (hSup : ∀ w : F.Node, ∀ i, D < i → Row.coeff (F.height w) i = 0) :
    ∀ (n : Nat) {u w qu qw : F.Node}, Frame.Real u → u.1 = w.1 →
      w.2.val = u.2.val + n + 1 → F.Q u = some qu → F.Q w = some qw →
      keyLt (D + 1) (genKey D (fent hF.toOrdered (F.height u) qu))
        (genKey D (fent hF.toOrdered (F.height w) qw)) = true := by
  intro n
  induction n with
  | zero =>
      intro u w qu qw hReal hc hi hQu hQw
      exact leg_lt_upper hF hSup hReal (upper_eq_of_index hc (by omega)) hQu hQw
  | succ n ih =>
      intro u w qu qw hReal hc hi hQu hQw
      have hlen : u.2.val + 1 < F.length u.1 := by
        have hw := w.2.isLt
        have hwl : F.length w.1 = F.length u.1 := by rw [hc]
        omega
      let v : F.Node := ⟨u.1, ⟨u.2.val + 1, hlen⟩⟩
      have hUp : F.upper u = some v := upper_eq_of_index rfl rfl
      obtain ⟨p, _, _, _, hStored⟩ := hF.upper_step u v hReal hUp
      obtain ⟨qv, hQv⟩ := Frame.Q_exists_of_left hF.toOrdered ⟨_, hStored⟩
      have hvReal : Frame.Real v := by
        show 0 < u.2.val + 1
        omega
      exact keyLt_trans (leg_lt_upper hF hSup hReal hUp hQu hQv)
        (ih hvReal hc (by show w.2.val = u.2.val + 1 + n + 1; omega) hQv hQw)

end FrameKeys

/-! ## The executable leg atoms of a canonical mountain -/

section Bridge

variable {M : Mountain}

theorem cell?_ref (u : (Frame.ofMountain M).Node) :
    cell? M (Frame.ref u) = some ((Frame.ofMountain M).cell u) := by
  rcases u with ⟨c, i⟩
  have hc : c.val < M.size := c.isLt
  have hi : i.val < M[c.val].size := i.isLt
  simp only [cell?, Frame.ref, Frame.cell, Frame.ofMountain, Array.getElem?_eq_getElem hc,
    Option.bind_eq_bind, Option.bind_some, Array.getElem?_eq_getElem hi]

theorem rawParent_ref (u : (Frame.ofMountain M).Node) :
    Reserve.rawParent M (Frame.ref u) =
      ((Frame.ofMountain M).upper u).bind fun v => ((Frame.ofMountain M).cell v).left := by
  rcases u with ⟨c, i⟩
  have hc : c.val < M.size := c.isLt
  unfold Frame.upper
  split
  · rename_i h
    have h' : i.val + 1 < M[c.val].size := h
    simp only [Reserve.rawParent, Frame.ref, Frame.cell, Frame.ofMountain,
      Array.getElem?_eq_getElem hc, Option.bind_eq_bind, Option.bind_some,
      Array.getElem?_eq_getElem h']
  · rename_i h
    have h' : ¬ i.val + 1 < M[c.val].size := h
    simp only [Reserve.rawParent, Frame.ref, Array.getElem?_eq_getElem hc,
      Option.bind_eq_bind, Option.bind_some, Array.getElem?_eq_none (Nat.le_of_not_lt h'),
      Option.bind_none]

/-- The executable scale root is the scale root of the frame. -/
theorem scaleRoot_bridge (hF : (Frame.ofMountain M).Ordered) (k : Nat) :
    ∀ (fuel : Nat) (u : (Frame.ofMountain M).Node), u.1.val < fuel →
      Reserve.scaleRoot M k fuel (Frame.ref u) = Frame.ref (Frame.scaleRoot hF k u) := by
  intro fuel
  induction fuel with
  | zero => intro u hu; omega
  | succ fuel ih =>
    intro u hu
    rw [Reserve.scaleRoot, rawParent_ref, cell?_ref]
    cases hUp : (Frame.ofMountain M).upper u with
    | none =>
        have hsp : (Frame.ofMountain M).scaleParent k u = none := by
          simp [Frame.scaleParent, Frame.rawParent, hUp]
        rw [Frame.scaleRoot_eq_of_none hF hsp]
        rfl
    | some v =>
        simp only [Option.bind_some]
        cases hl : ((Frame.ofMountain M).cell v).left with
        | none =>
            have hsp : (Frame.ofMountain M).scaleParent k u = none := by
              simp [Frame.scaleParent, Frame.rawParent, hUp, hl]
            rw [Frame.scaleRoot_eq_of_none hF hsp]
        | some stored =>
            obtain ⟨left, hlk, hlc, _⟩ := hF.stored_valid v stored hl
            have hst : Frame.ref left = stored := Frame.lookup_spec hlk
            subst hst
            have hraw : (Frame.ofMountain M).rawParent u = some left :=
              Frame.rawParent_eq_of_upper_left hUp hl
            have hvcol := (Frame.upper_spec hUp).1
            have hcolLt : left.1.val < u.1.val := by
              have : v.1.val = u.1.val := congrArg Fin.val hvcol
              omega
            simp only [cell?_ref]
            by_cases hj : Row.jump ((Frame.ofMountain M).height u)
                ((Frame.ofMountain M).height left) ≤ k
            · rw [if_pos ⟨hj, hcolLt⟩, ih left (by omega),
                Frame.scaleRoot_eq_of_raw hF hraw hj]
            · rw [if_neg (fun h => hj h.1)]
              have hsp : (Frame.ofMountain M).scaleParent k u = none := by
                simp [Frame.scaleParent, hraw, hj]
              rw [Frame.scaleRoot_eq_of_none hF hsp]

theorem keyAt_bridge (hF : (Frame.ofMountain M).Ordered) (D : Nat) (row : Row)
    (q : (Frame.ofMountain M).Node) :
    keyAt M D row (Frame.ref q) = genKey D (fent hF row q) := by
  unfold keyAt
  rw [cell?_ref]
  simp only [genKey]
  apply List.map_congr_left
  intro k _
  unfold fent
  rw [scaleRoot_bridge hF k ((Frame.ref q).column + 1) q (by simp [Frame.ref])]
  rfl

theorem getLast?_filter_range {n j : Nat} {P : Nat → Bool}
    (h : ((List.range n).filter P).getLast? = some j) :
    j < n ∧ P j = true ∧ ∀ x, x < n → P x = true → x ≤ j := by
  have hmem := List.mem_of_getLast? h
  rw [List.mem_filter, List.mem_range] at hmem
  refine ⟨hmem.1, hmem.2, ?_⟩
  intro x hx hPx
  have hsorted : ((List.range n).filter P).Pairwise (· < ·) :=
    List.Pairwise.filter _ List.pairwise_lt_range
  obtain ⟨l', hl'⟩ := List.getLast?_eq_some_iff.mp h
  have hxmem : x ∈ (List.range n).filter P := List.mem_filter.mpr ⟨List.mem_range.mpr hx, hPx⟩
  rw [hl'] at hsorted hxmem
  rcases List.mem_append.mp hxmem with hx' | hx'
  · exact le_of_lt ((List.pairwise_append.mp hsorted).2.2 x hx' j (by simp))
  · simp only [List.mem_singleton] at hx'
    omega

/-- The node read by `highestAtMost` for the leg of `u` is `Q(u)`. -/
theorem Q_of_highestAtMost (hF : (Frame.ofMountain M).Ordered)
    {u : (Frame.ofMountain M).Node} {l p : Ref}
    (hl : ((Frame.ofMountain M).cell u).left = some l)
    (hp : highestAtMost M l.column ((Frame.ofMountain M).height u) = some p) :
    ∃ q, (Frame.ofMountain M).Q u = some q ∧ Frame.ref q = p := by
  obtain ⟨left, hlk, _, hrow⟩ := hF.stored_valid u l hl
  have hlref : Frame.ref left = l := Frame.lookup_spec hlk
  subst hlref
  have hc : left.1.val < M.size := left.1.isLt
  simp only [highestAtMost, Frame.ref, Array.getElem?_eq_getElem hc, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at hp
  obtain ⟨j, hj, rfl⟩ := hp
  obtain ⟨hjn, hPj, hmax⟩ := getLast?_filter_range hj
  have hP : ∀ x (hx : x < M[left.1.val].size), 0 < x →
      (M[left.1.val][x]'hx).row ≤ (Frame.ofMountain M).height u →
      (0 < x && (match M[left.1.val][x]? with
        | some c => decide (c.row ≤ (Frame.ofMountain M).height u)
        | none => false)) = true := by
    intro x hx hx0 hxr
    simp only [Array.getElem?_eq_getElem hx, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hx0, hxr⟩
  simp only [Array.getElem?_eq_getElem hjn, Bool.and_eq_true, decide_eq_true_eq] at hPj
  let i : Fin ((Frame.ofMountain M).length left.1) := ⟨j, hjn⟩
  have hileft : left.2.val ≤ j := by
    by_cases h0 : left.2.val = 0
    · omega
    · apply hmax _ left.2.isLt
      exact hP _ left.2.isLt (by omega) hrow
  have hielig : i ∈ (Frame.ofMountain M).eligible u left :=
    Frame.mem_eligible.mpr ⟨hileft, hPj.2⟩
  have hq := Frame.Q_eq_of_maximal (by rw [hl]) i hielig (by
    intro i' hi'
    obtain ⟨_, hi'row⟩ := Frame.mem_eligible.mp hi'
    show i'.val ≤ j
    by_cases h0 : i'.val = 0
    · omega
    · apply hmax _ i'.isLt
      exact hP _ i'.isLt (by omega) hi'row)
  exact ⟨_, hq, rfl⟩

/-- The key of an executable leg atom is the frame leg key at `Q(u)`. -/
theorem legAtom_bridge (hF : (Frame.ofMountain M).Ordered) {D : Nat}
    (u : (Frame.ofMountain M).Node) {a : RawAtom} (ha : legAtom? M D (Frame.ref u) = some a) :
    ∃ q, (Frame.ofMountain M).Q u = some q ∧
      a.key = genKey D (fent hF ((Frame.ofMountain M).height u) q) := by
  unfold legAtom? at ha
  rw [cell?_ref] at ha
  simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at ha
  obtain ⟨l, hl, p, hp, rfl⟩ := ha
  obtain ⟨q, hQ, hqp⟩ := Q_of_highestAtMost hF hl hp
  subst hqp
  exact ⟨q, hQ, keyAt_bridge hF D _ q⟩

theorem node_of_cell? {v : Ref} {cv : Cell} (h : cell? M v = some cv) :
    ∃ u : (Frame.ofMountain M).Node, Frame.ref u = v ∧ (Frame.ofMountain M).cell u = cv := by
  simp only [cell?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨col, hcol, hcv⟩ := h
  obtain ⟨hc, rfl⟩ := Array.getElem?_eq_some_iff.mp hcol
  obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp hcv
  exact ⟨⟨⟨v.column, hc⟩, ⟨v.index, hi⟩⟩, rfl, rfl⟩

end Bridge

/-! ## The control dominates the last column -/

/-- **`ControlDominates`**: for a legal `s` with `DegreeOK s D` and `root? M D = some ρ`,
every leg atom of a node of the last column below the top has a key below `ρ.control`. -/
theorem controlDominates : ControlDominates := by
  intro s D M ρ col t v cv a hb hdeg hr hcol ht hcv hvc hrow ha
  have hF := build_normal_of_success hb
  have hO := hF.toOrdered
  have hV := build_valid_of_success hb
  -- degrees are at most `D`
  have hSup : ∀ w : (Frame.ofMountain M).Node, ∀ i, D < i →
      Row.coeff ((Frame.ofMountain M).height w) i = 0 := by
    have hdM := hdeg M hb
    simp only [degreeAtMost, List.all_eq_true, decide_eq_true_eq] at hdM
    intro w i hi
    have hw1 : w.1.val < M.size := w.1.isLt
    have hw2 : w.2.val < M[w.1.val].size := w.2.isLt
    have hlen := hdM M[w.1.val] (Array.getElem_mem_toList hw1) M[w.1.val][w.2.val]
      (Array.getElem_mem_toList hw2)
    have hlen' : len ((Frame.ofMountain M).height w) ≤ D + 1 := hlen
    exact coeff_eq_zero_of_len_le (by omega)
  -- the control is the key of the leg atom of the top node
  have hctl : ∃ b, legAtom? M D ⟨M.size - 1, col.size - 1⟩ = some b ∧ ρ.control = b.key := by
    unfold root? at hr
    rw [hcol] at hr
    simp only at hr
    split at hr
    · cases hr
    · split at hr
      · cases hr
      · split at hr
        · cases hr
        · split at hr
          · cases hr
          · rename_i b hb'
            split at hr
            · cases hr
              exact ⟨b, hb', rfl⟩
            · cases hr
  obtain ⟨b, hb', hcb⟩ := hctl
  rw [hcb]
  -- the columns and indices
  obtain ⟨hcs, hcolEq⟩ := column_of_getElem? hcol
  obtain ⟨_, htop⟩ := back?_spec ht
  have hvcell : col[v.index]? = some cv := by
    simp only [cell?, hvc, hcol, Option.bind_eq_bind, Option.bind_some] at hcv
    exact hcv
  have hvlt : v.index < col.size := (Array.getElem?_eq_some_iff.mp hvcell).1
  have hvne : v.index ≠ col.size - 1 := by
    intro he
    rw [he, htop] at hvcell
    cases hvcell
    exact lt_irrefl _ hrow
  have hv0 : v.index ≠ 0 := by
    intro h0
    obtain ⟨_, _, l, hcu, hl, _⟩ := legAtom?_spec ha
    rw [hcv] at hcu
    cases hcu
    have hCV := hV (M.size - 1) hcs
    rw [hcolEq] at hCV
    have hph := hCV.phantom
    rw [← h0, hvcell] at hph
    cases hph
    simp [Canonical.phantom] at hl
  obtain ⟨cw, hcw⟩ : ∃ cw, cell? M ⟨M.size - 1, col.size - 1⟩ = some cw :=
    ⟨t, by simp only [cell?, hcol, Option.bind_eq_bind, Option.bind_some]; exact htop⟩
  obtain ⟨u, hu, _⟩ := node_of_cell? hcv
  obtain ⟨w, hw, _⟩ := node_of_cell? hcw
  rw [← hu] at ha
  rw [← hw] at hb'
  obtain ⟨qu, hQu, hka⟩ := legAtom_bridge hO u ha
  obtain ⟨qw, hQw, hkb⟩ := legAtom_bridge hO w hb'
  rw [hka, hkb]
  have hu1 : u.1.val = M.size - 1 := by rw [← hvc, ← hu]; rfl
  have hu2 : u.2.val = v.index := by rw [← hu]; rfl
  have hw1 : w.1.val = M.size - 1 := by
    have := congrArg Ref.column hw
    exact this
  have hw2 : w.2.val = col.size - 1 := by
    have := congrArg Ref.index hw
    exact this
  have huw : u.1 = w.1 := Fin.ext (by rw [hu1, hw1])
  exact leg_lt_above hF hSup (w.2.val - u.2.val - 1) (show 0 < u.2.val by omega) huw
    (by omega) hQu hQw

/-- **Well-foundedness of the official expansion from the two remaining statements**:
`ControlDominates` is proved above. -/
theorem wellFounded_of_block_keys (hrec : Dimension.BlockReconstruction) (h5 : KeyLeRest) :
    WellFounded Descent.Step :=
  wellFounded_of_block hrec controlDominates h5

end OmegaY.Official.Classification.ControlProof

#print axioms OmegaY.Official.Classification.ControlProof.wellFounded_of_block_keys
#print axioms OmegaY.Official.Classification.ControlProof.controlDominates
