/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/KeyWitness.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
Port change: in `legAtom?_exists` one bound `pcol[1].row ≤ cv.row` is proved by `exact hprow.le.trans …` instead of `rw [hprow]`.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Witness
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.BottomLegs

set_option backward.do.legacy false

/-!
# The canonical witness, keys only

`WitnessOK` (`Witness.lean`) asks for the columns of the witness atom (child and
parent) and for key inequalities. The columns follow from the rule itself:

* the origin of an emitted node is a real node of the source column `x` (or of `x'`
  for the upper part), and the emitted leg column is the column of the origin's left
  endpoint, or `x - 1` for a node of the bottom row (`emitsT_good`, `bottom_left`);
* the output leg column is its image `φ_i` (`assemble_spec`, `legColumn`);
* the block arithmetic of `X = x + w·i` (`block_cases`).

`witnessHolds_of_keys` proves this, so the only open statement of the classification
is `KeyWitnessHolds`: key inequalities between the output leg atom of a node and the
input leg atom of its origin (`KeyOK`). `wellFounded_of_keys` assembles the chain.
-/

namespace OmegaY.Official.Classification
open Canonical Reserve Official Descent

theorem mem_realNodes {M : Mountain} {c : Nat} {p : Ref × Cell} (h : p ∈ realNodes M c) :
    p.1.column = c ∧ 1 ≤ p.1.index ∧ cell? M p.1 = some p.2 := by
  unfold realNodes at h
  cases hcol : M[c]? with
  | none => simp [hcol] at h
  | some col =>
      simp only [hcol, List.mem_map] at h
      obtain ⟨q, hq, rfl⟩ := h
      obtain ⟨m, hm, hqm⟩ := List.getElem_of_mem hq
      simp only [List.length_drop, List.length_zip, List.length_range, Array.length_toList] at hm
      rw [List.getElem_drop, List.getElem_zip] at hqm
      subst hqm
      simp only [List.getElem_range, Array.getElem_toList]
      refine ⟨by simp, by omega, ?_⟩
      simp [cell?, hcol]

theorem nodeAt_spec {M : Mountain} {c : Nat} {ρ : Row} {p : Ref × Cell}
    (h : nodeAt M c ρ = some p) :
    p.1.column = c ∧ 1 ≤ p.1.index ∧ cell? M p.1 = some p.2 ∧ official p.2.row = ρ := by
  unfold nodeAt at h
  have hmem := List.mem_of_find?_eq_some h
  have hpred := List.find?_some h
  simp only [beq_iff_eq] at hpred
  exact ⟨(mem_realNodes hmem).1, (mem_realNodes hmem).2.1, (mem_realNodes hmem).2.2, hpred⟩

theorem leftColumn_ok {cell : Cell} {v : Nat} (h : leftColumn cell = .ok v) :
    ∃ l : Ref, cell.left = some l ∧ l.column = v := by
  cases hl : cell.left with
  | none =>
      simp [leftColumn, Expansion.leftOf, hl, liftE, Except.mapError, bind, Except.bind] at h
  | some l =>
      simp [leftColumn, Expansion.leftOf, hl, liftE, Except.mapError, bind, Except.bind,
        pure, Except.pure] at h
      exact ⟨l, rfl, h⟩

theorem mem_of_mapM {α β ε : Type} {f : α → Except ε β} {xs : List α} {ys : List β}
    (h : xs.mapM f = .ok ys) {y : β} (hy : y ∈ ys) : ∃ x ∈ xs, f x = .ok y := by
  obtain ⟨hlen, hall⟩ := mapM_except_spec f xs ys h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
  exact ⟨xs[i], List.getElem_mem _, hall i (by omega) hi⟩

/-- What the traced rule records about one emitted node: its origin is a real node of
the source column (`x`, or `x'` for the upper part), and the emitted leg column is the
column of the origin's left endpoint, except for a node of the bottom row, which has
no emitted leg. -/
def Good (ctx : Context) (p : Emit × Origin) : Prop :=
  p.2.src.column = (if p.2.isUpper then upperColumn ctx else ctx.x) ∧ 1 ≤ p.2.src.index ∧
    ∃ cv, cell? ctx.source p.2.src = some cv ∧
      ((∃ l : Ref, cv.left = some l ∧ p.1.leftColumn = some l.column) ∨
        (p.1.leftColumn = none ∧ official cv.row = 0 ∧ p.2.isUpper = false))

theorem levelOneT_good {ctx : Context} {it : Item} {ps : List (Emit × Origin)}
    (h : levelOneT ctx it = .ok ps) : ∀ p ∈ ps, Good ctx p := by
  unfold levelOneT at h
  cases hsrc : nodeAt ctx.source ctx.x it.source with
  | none => simp [hsrc, pure, Except.pure] at h; subst h; simp
  | some q =>
      obtain ⟨srcRef, src⟩ := q
      obtain ⟨hsc, hsi, hscell, hsrow⟩ := nodeAt_spec hsrc
      simp only at hsc hsi hscell hsrow
      simp only [hsrc] at h
      cases hC : it.clean with
      | some C =>
          simp only [hC] at h
          cases hcs : nodeAt ctx.source ctx.x C with
          | none => simp [hcs, throw, throwThe, MonadExceptOf.throw] at h
          | some q' =>
              obtain ⟨csRef, cs⟩ := q'
              obtain ⟨hcc, hci, hccell, _⟩ := nodeAt_spec hcs
              simp only at hcc hci hccell
              simp only [hcs, bind, Except.bind, pure, Except.pure] at h
              cases hlc : leftColumn cs with
              | error e => rw [hlc] at h; cases h
              | ok v =>
                  rw [hlc] at h
                  cases h
                  obtain ⟨l, hl, hlv⟩ := leftColumn_ok hlc
                  intro p hp
                  simp only [List.mem_singleton] at hp
                  subst hp
                  refine ⟨by simp [Origin.src, Origin.isUpper, hcc], by simpa [Origin.src] using hci,
                    cs, by simpa [Origin.src] using hccell, Or.inl ⟨l, hl, by simp [hlv]⟩⟩
      | none =>
          simp only [hC] at h
          by_cases h0 : it.source = 0
          · rw [if_pos h0] at h
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            intro p hp
            simp only [List.mem_singleton] at hp
            subst hp
            refine ⟨by simp [Origin.src, Origin.isUpper, hsc], by simpa [Origin.src] using hsi,
              src, by simpa [Origin.src] using hscell, Or.inr ⟨rfl, by rw [hsrow, h0], rfl⟩⟩
          · rw [if_neg h0] at h
            simp only [bind, Except.bind, pure, Except.pure] at h
            cases hlc : leftColumn src with
            | error e => rw [hlc] at h; cases h
            | ok v =>
                rw [hlc] at h
                cases h
                obtain ⟨l, hl, hlv⟩ := leftColumn_ok hlc
                intro p hp
                simp only [List.mem_singleton] at hp
                subst hp
                refine ⟨by simp [Origin.src, Origin.isUpper, hsc], by simpa [Origin.src] using hsi,
                  src, by simpa [Origin.src] using hscell, Or.inl ⟨l, hl, by simp [hlv]⟩⟩

theorem runItemT_good (ctx : Context) :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), runItemT ctx d it = .ok ps →
      ∀ p ∈ ps, Good ctx p
  | 0, _, ps, h => by simp [runItemT, pure, Except.pure] at h; subst h; simp
  | 1, it, ps, h => levelOneT_good (by simpa [runItemT] using h)
  | d + 2, it, ps, h => by
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i children _
        split at h
        · cases h
        · rename_i outs houts
          cases h
          intro p hp
          obtain ⟨out, hout, hpo⟩ := List.mem_flatten.mp hp
          obtain ⟨c, _, hc⟩ := mem_of_mapM houts hout
          exact runItemT_good ctx (d + 1) c out hc p hpo

theorem emitsT_good {ctx : Context} {τ : Row} {es : List (Emit × Origin)}
    (h : emitsT ctx τ = .ok es) : ∀ p ∈ es, Good ctx p := by
  unfold emitsT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i lower hlower
    split at h
    · cases h
    · rename_i upper hupper
      cases h
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · unfold lowerT at hlower
        simp only [bind, Except.bind, pure, Except.pure] at hlower
        split at hlower
        · cases hlower
        · rename_i outs houts
          cases hlower
          obtain ⟨out, hout, hpo⟩ := List.mem_flatten.mp hp
          obtain ⟨q, _, hq⟩ := mem_of_mapM houts hout
          exact runItemT_good ctx q.1 q.2 out hq p hpo
      · unfold upperT at hupper
        obtain ⟨q, hq, hqp⟩ := mem_of_mapM hupper hp
        obtain ⟨hqc, hqi, hqcell⟩ := mem_realNodes (List.mem_of_mem_filter hq)
        simp only [bind, Except.bind, pure, Except.pure] at hqp
        cases hlc : leftColumn q.2 with
        | error e => rw [hlc] at hqp; cases hqp
        | ok v =>
            rw [hlc] at hqp
            cases hqp
            obtain ⟨l, hl, hlv⟩ := leftColumn_ok hlc
            refine ⟨by simp [Origin.src, Origin.isUpper, hqc], by simpa [Origin.src] using hqi,
              q.2, by simpa [Origin.src] using hqcell, Or.inl ⟨l, hl, by simp [hlv]⟩⟩

/-! ## Arithmetic of blocks -/

theorem block_cases {cr x0 n i x X : Nat} (hcr : cr < x0) (hx : x ∈ blockColumns cr x0 n i)
    (hX : X = x + (x0 - cr) * i) :
    ∃ P, (x0 - cr) * i = P ∧ X = x + P ∧
      ((x = x0 ∧ blockOf x0 (x0 - cr) X * (x0 - cr) = P) ∨
        (cr < x ∧ x < x0 ∧ x0 - cr ≤ P ∧ blockOf x0 (x0 - cr) X * (x0 - cr) + (x0 - cr) = P)) := by
  refine ⟨(x0 - cr) * i, rfl, hX, ?_⟩
  have hw : 0 < x0 - cr := by omega
  unfold blockColumns at hx
  split at hx
  · rename_i hi0
    subst hi0
    simp only [List.mem_singleton] at hx
    subst hx
    left
    simp [blockOf, hX]
  · rename_i hi0
    simp only [List.mem_range'_1] at hx
    have hxle : x ≤ x0 := by split at hx <;> omega
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hP : (x0 - cr) * (j + 1) = j * (x0 - cr) + (x0 - cr) := by
      rw [Nat.mul_succ, Nat.mul_comm]
    by_cases hxx : x = x0
    · left
      refine ⟨hxx, ?_⟩
      have : X - x0 = (j + 1) * (x0 - cr) := by rw [hX, Nat.mul_comm]; omega
      simp only [blockOf, this, Nat.mul_div_cancel _ hw]
      exact Nat.mul_comm _ _
    · right
      refine ⟨by omega, by omega, by rw [hP]; omega, ?_⟩
      have : X - x0 = (x - cr) + j * (x0 - cr) := by rw [hX, hP]; omega
      simp only [blockOf, this, Nat.add_mul_div_right _ _ hw,
        Nat.div_eq_of_lt (show x - cr < x0 - cr by omega), Nat.zero_add]
      rw [hP]

/-! ## Source atoms -/

theorem cell?_spec {M : Mountain} {v : Ref} {cv : Cell} (h : cell? M v = some cv) :
    ∃ colv, M[v.column]? = some colv ∧ colv[v.index]? = some cv := by
  unfold cell? at h
  cases hc : M[v.column]? with
  | none => simp [hc] at h
  | some colv => exact ⟨colv, rfl, by simpa [hc] using h⟩

theorem one_le_row {M : Mountain} (hV : MountainValid M) {v : Ref} {cv : Cell}
    (h : cell? M v = some cv) (hidx : 1 ≤ v.index) : (1 : Row) ≤ cv.row := by
  obtain ⟨colv, hcolv, hcv⟩ := cell?_spec h
  obtain ⟨hc, hcolEq⟩ := column_of_getElem? hcolv
  have hCV := hV v.column hc
  rw [hcolEq] at hCV
  have hsz := hCV.size_ge_two
  have hb1 : colv[1]? = some colv[1] := Array.getElem?_eq_getElem (by omega)
  have hrow1 := hCV.bottom_row colv[1] hb1
  by_cases h1 : v.index = 1
  · rw [h1, hb1] at hcv
    cases hcv
    rw [hrow1]
  · have := hCV.rows_strict 1 v.index colv[1] cv hb1 hcv (by omega)
    rw [hrow1] at this
    exact le_of_lt this

theorem index_one_of_official_zero {M : Mountain} (hV : MountainValid M) {v : Ref} {cv : Cell}
    (h : cell? M v = some cv) (hidx : 1 ≤ v.index) (h0 : official cv.row = 0) :
    v.index = 1 := by
  obtain ⟨colv, hcolv, hcv⟩ := cell?_spec h
  obtain ⟨hc, hcolEq⟩ := column_of_getElem? hcolv
  have hCV := hV v.column hc
  rw [hcolEq] at hCV
  have hsz := hCV.size_ge_two
  have hb1 : colv[1]? = some colv[1] := Array.getElem?_eq_getElem (by omega)
  have hrow1 := hCV.bottom_row colv[1] hb1
  by_contra h1
  have := hCV.rows_strict 1 v.index colv[1] cv hb1 hcv (by omega)
  rw [hrow1] at this
  exact official_ne_zero_of_one_lt this h0

theorem bottom_left {M : Mountain} {s : List Nat} (hM : build s = .ok M) {v : Ref} {cv : Cell}
    (h : cell? M v = some cv) (hidx : v.index = 1) (hc0 : v.column ≠ 0) :
    cv.left = some ⟨v.column - 1, 0⟩ := by
  obtain ⟨colv, hcolv, hcv⟩ := cell?_spec h
  obtain ⟨hc, hcolEq⟩ := column_of_getElem? hcolv
  obtain ⟨bottom, hb, hbl⟩ := build_bottom_legs hM v.column hc
  rw [hcolEq, ← hidx, hcv] at hb
  cases hb
  simpa [hc0] using hbl

theorem legAtom?_exists {M : Mountain} (hV : MountainValid M) (D : Nat) {v : Ref} {cv : Cell}
    {l : Ref} (h : cell? M v = some cv) (hidx : 1 ≤ v.index) (hl : cv.left = some l) :
    ∃ a, legAtom? M D v = some a ∧ a.parent = l.column ∧ a.child = v.column ∧
      a ∈ atoms M D ∧ l.column < v.column := by
  obtain ⟨colv, hcolv, hcv⟩ := cell?_spec h
  obtain ⟨hc, hcolEq⟩ := column_of_getElem? hcolv
  have hCV := hV v.column hc
  rw [hcolEq] at hCV
  obtain ⟨hlc, parent, hparent, _⟩ := hCV.stored_valid v.index cv l hcv hl
  obtain ⟨pcol, hpcol, _⟩ := cellAt_ok_iff.mp hparent
  obtain ⟨hpc, hpcolEq⟩ := column_of_getElem? hpcol
  have hPV := hV l.column hpc
  rw [hpcolEq] at hPV
  have hps : 1 < pcol.size := by have := hPV.size_ge_two; omega
  have hp1 : pcol[1]? = some pcol[1] := Array.getElem?_eq_getElem hps
  have hprow := hPV.bottom_row pcol[1] hp1
  obtain ⟨p, hp⟩ := highestAtMost_some (row := cv.row) hpcol hPV.size_ge_two
    (by exact hprow.le.trans (one_le_row hV h hidx))
  have hleg : legAtom? M D v = some ⟨l.column, v.column, keyAt M D cv.row p⟩ := by
    simp only [legAtom?, h, hl, Option.bind_eq_bind, Option.bind_some]
    rw [hp]
    rfl
  have hvi : v.index < colv.size := (Array.getElem?_eq_some_iff.mp hcv).1
  refine ⟨_, hleg, rfl, rfl, ?_, hlc⟩
  exact mem_atoms hc (by omega) hcolv hvi (by omega) hleg

/-! ## Keys only -/

/-- The key part of `WitnessOK`. -/
def KeyOK (D cr w x0 : Nat) (Kc : RawKey) (X : Nat) (o : Origin) (e a : RawAtom) : Prop :=
  if X = x0 + blockOf x0 w X * w ∧ o.isUpper = false then
    keyLe (D + 1) e.key (mapKey cr (blockOf x0 w X * w) a.key) = true ∧
      keyLt (D + 1) e.key (mapKey cr (blockOf x0 w X * w) Kc) = true
  else
    keyLe (D + 1) e.key (mapKey cr ((blockOf x0 w X + 1) * w) a.key) = true

/-- **The remaining statement.** For every node of every copied column, the key of its
output leg atom is bounded by the (mapped) key of the leg atom of its origin, and at a
block boundary (outside the upper part) strictly by the mapped control. -/
def KeyWitnessHolds : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), SpliceCase s n D M out ρ → DegreeOK s D →
    Official.expandDiagram s n = .ok R → Canonical.build out = .ok R →
    M[M.size - 1]? = some col → col.back? = some t →
    ∀ X x i (_ : ρ.x0 ≤ X) (hXR : X < R.size), X = x + (ρ.x0 - ρ.cr) * i → i < n + 1 →
      x ∈ blockColumns ρ.cr ρ.x0 n i →
      copyColumn (ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) (official t.row) = .ok R[X] →
      ∀ es, emitsT (ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) (official t.row) = .ok es →
      ∀ k (hk : k < es.length) e a, legAtom? R D ⟨X, k + 1⟩ = some e →
        legAtom? M D es[k].2.src = some a →
        KeyOK D ρ.cr (ρ.x0 - ρ.cr) ρ.x0 ρ.control X es[k].2 e a

theorem witnessHolds_of_keys (hK : KeyWitnessHolds) : WitnessHolds := by
  intro s n D M out ρ R col t hc hdeg hR hRb hcol ht X x i hX0 hXR hXeq hi hx hcopy es hes k hk
    e he
  obtain ⟨_, _, _, _, hx0, hcrx, _⟩ := spliceCase_data hc hR
  have hV := build_valid_of_success hc.build
  obtain ⟨es', hes', hasm⟩ := copyColumn_emitsT hcopy
  have hee : es' = es := Except.ok.inj (hes'.symm.trans hes)
  subst hee
  obtain ⟨_, hcells⟩ := assemble_spec hasm
  obtain ⟨cell, hcellX, _, ref, hrefl, hrefc⟩ := hcells k (by simpa using hk)
  obtain ⟨heX, cu, l', hcu, hl', hep⟩ := legAtom?_spec he
  have hcu' : cell? R ⟨X, k + 1⟩ = some cell := by
    simp only [cell?, Array.getElem?_eq_getElem hXR, Option.bind_eq_bind, Option.bind_some]
    exact hcellX
  rw [hcu'] at hcu
  cases hcu
  rw [hrefl] at hl'
  cases hl'
  simp only [List.getElem_map] at hrefc
  obtain ⟨hvcol, hvidx, cv, hcv, hleft⟩ := emitsT_good hes es'[k] (List.getElem_mem hk)
  obtain ⟨P, hPdef, hXP, hcase⟩ := block_cases hcrx hx hXeq
  simp only [ctxAt, upperColumn] at hvcol
  have hxpos : ρ.cr < x := by rcases hcase with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  -- the left leg of the origin and the emitted leg column
  obtain ⟨l, hl, hlφ⟩ : ∃ l : Ref, cv.left = some l ∧
      legColumn (ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) es'[k].1 =
        (if ρ.cr ≤ l.column then l.column + P else l.column) := by
    rcases hleft with ⟨l, hl, hlc⟩ | ⟨hnone, h0, hup⟩
    · refine ⟨l, hl, ?_⟩
      simp only [legColumn, hlc, ctxAt, hPdef]
    · rw [hup] at hvcol
      simp only [Bool.false_eq_true, if_false] at hvcol
      have hi1 := index_one_of_official_zero hV hcv hvidx h0
      have hbl := bottom_left hc.build hcv hi1 (by omega)
      refine ⟨_, hbl, ?_⟩
      simp only [legColumn, hnone, ctxAt, Array.size_extract]
      rw [hvcol]
      simp only [show ρ.cr ≤ x - 1 by omega, if_true]
      omega
  obtain ⟨a, ha, hap, hac, hamem, hlv⟩ := legAtom?_exists hV D hcv hvidx hl
  refine ⟨a, hamem, ha, ?_⟩
  have hkey := hK s n D M out ρ R col t hc hdeg hR hRb hcol ht X x i hX0 hXR hXeq hi hx hcopy
    es' hes k hk e a he ha
  rw [hrefc, hlφ] at hep
  unfold WitnessOK
  unfold KeyOK at hkey
  generalize blockOf ρ.x0 (ρ.x0 - ρ.cr) X * (ρ.x0 - ρ.cr) = bw at hkey hcase ⊢
  by_cases hcond : X = ρ.x0 + bw ∧ es'[k].2.isUpper = false
  · rw [if_pos hcond] at hkey ⊢
    obtain ⟨hk1, hk2⟩ := hkey
    rw [hcond.2] at hvcol
    simp only [Bool.false_eq_true, if_false] at hvcol
    have hxx : x = ρ.x0 := by rcases hcase with ⟨h1, _⟩ | ⟨_, _, _, h4⟩ <;> omega
    refine ⟨by omega, ?_, hk1, hk2⟩
    unfold mapColumn
    rw [hep, hap]
    rcases hcase with ⟨_, h2⟩ | ⟨_, _, _, h4⟩
    · split <;> split <;> omega
    · omega
  · rw [if_neg hcond] at hkey ⊢
    refine ⟨?_, ?_, ?_, hkey⟩
    · rcases hcase with ⟨h1, h2⟩ | ⟨_, h2, _, _⟩
      · have hup : es'[k].2.isUpper = true := by
          by_contra hne
          exact hcond ⟨by omega, by simpa using hne⟩
        rw [hup] at hvcol
        simp only [if_true, h1, if_true] at hvcol
        omega
      · simp only [show ¬ x = ρ.x0 by omega, if_false, ite_self] at hvcol
        omega
    · rcases hcase with ⟨h1, h2⟩ | ⟨_, h2, _, _⟩
      · have hup : es'[k].2.isUpper = true := by
          by_contra hne
          exact hcond ⟨by omega, by simpa using hne⟩
        rw [hup] at hvcol
        simp only [if_true, h1, if_true] at hvcol
        omega
      · simp only [show ¬ x = ρ.x0 by omega, if_false, ite_self] at hvcol
        omega
    · rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
      · have hup : es'[k].2.isUpper = true := by
          by_contra hne
          exact hcond ⟨by omega, by simpa using hne⟩
        rw [hup] at hvcol
        simp only [if_true, h1, if_true] at hvcol
        left
        rw [hep, hap]
        split <;> omega
      · simp only [show ¬ x = ρ.x0 by omega, if_false, ite_self] at hvcol
        rw [hep, hap]
        by_cases hlc : ρ.cr ≤ l.column
        · rw [if_pos hlc]
          exact Or.inr ⟨by omega, by omega, by omega⟩
        · rw [if_neg hlc]
          exact Or.inl ⟨by omega, rfl⟩

/-- **Well-foundedness from the open statements.** -/
theorem wellFounded_of_keys (h1 : Reconstructs) (h2 : DegreePreserved) (h3 : LengthOK)
    (h4 : KeyWitnessHolds) : WellFounded Step :=
  wellFounded_of_witness h1 h2 h3 (witnessHolds_of_keys h4)

end OmegaY.Official.Classification

#print axioms OmegaY.Official.Classification.witnessHolds_of_keys
#print axioms OmegaY.Official.Classification.wellFounded_of_keys
