/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/KeyBlockZero.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.KeyShift

set_option backward.do.legacy false

/-!
# `KeyLeShift` in block `0`

Block `0` builds one column, `X = x₀`, from the column `x₀` of `M(s)`. There the lift
`Δ = (h_κ - h_ρ)·i` is `0`, so every item keeps its target equal to its source, has no
offset and no cut bottom, and copies a root row only on level `1`, where the copied row
is the source row itself (`childItems_block0`: case 2 with `i = 0` puts the root row
`row(ρ)` only in the slot `h_ρ` of a level-2 region, and that slot is the single row
`row(ρ)`). Cases 3 and 4 never occur.

Hence every node of the lower part sits at the row of its origin (`emitsT_block0`), with
the leg of its origin. The leg column is left of `x₀`, where the output agrees with
`M(s)`, so the output leg atom has exactly the key of the leg atom of its origin
(`keyLe_block0`). The upper part of column `x₀` copies the root column `cr`, whose legs
are left of `cr`: that case is excluded from `KeyLeShift` (it is
`KeyUpper.keyOK_upper_low`).
-/

namespace OmegaY.Official.Classification.Proofs

open Canonical Reserve Official Descent Classification

/-- The items of block `0`: the target is the source, no offset, no cut bottom, and a
copied root row only on level `1`, where it is the source row itself. -/
def Id0 (d : Nat) (it : Item) : Prop :=
  it.target = it.source ∧ it.offset = 0 ∧ it.cutBottom = false ∧
    (it.clean = none ∨ (d = 1 ∧ it.clean = some it.source))

theorem childItems_block0 {ctx : Context} {d : Nat} {it : Item} {cs : List Item}
    (hb : ctx.block = 0) (hd : 2 ≤ d) (hI : Id0 d it)
    (h : childItems ctx d it = .ok cs) : ∀ c ∈ cs, Id0 (d - 1) c := by
  obtain ⟨hT, hO, hC, hcl⟩ := hI
  have hcl' : it.clean = none := by rcases hcl with h' | ⟨h', _⟩; exact h'; omega
  unfold childItems at h
  simp only [bind, Except.bind, pure, Except.pure, hb, hcl', hC, hT, Nat.cast_zero, mul_zero,
    add_zero, sub_zero, Int.toNat_natCast, ne_eq, not_true_eq_false, false_and, decide_false,
    Bool.false_eq_true, not_false_eq_true, if_true, Option.isSome_none, hO, or_self,
    if_false] at h
  have hreg : ∀ r cl, topIn ctx.source ctx.rootColumn d it.source = some (r, cl) →
      inRegion d it.source (official cl.row) = true := fun r cl h' => topIn_inRegion h'
  generalize topIn ctx.source ctx.rootColumn d it.source = rho at h hreg
  split at h
  · cases h; simp
  · split at h
    · cases h
    · rename_i v hv
      split at h
      · cases h
        intro c hc
        simp only [List.mem_map, List.mem_range] at hc
        obtain ⟨j, _, rfl⟩ := hc
        exact ⟨rfl, rfl, rfl, Or.inl rfl⟩
      · rename_i hasc
        cases h
        intro c hc
        simp only [List.mem_map, List.mem_range] at hc
        obtain ⟨j, _, rfl⟩ := hc
        split
        · exact ⟨rfl, rfl, rfl, Or.inl rfl⟩
        · rename_i h1
          by_cases hd2 : d = 2
          · subst hd2
            simp only [if_true]
            split
            · rename_i h2
              obtain ⟨r, cl, rfl⟩ : ∃ r cl, rho = some (r, cl) := by
                cases rho with
                | none => simp [ascends, pure, Except.pure] at hv; subst hv; simp at hasc
                | some p => exact ⟨p.1, p.2, rfl⟩
              have hr := hreg r cl rfl
              simp only [heightOf] at h1 h2 ⊢
              have hj : j = height 2 (official cl.row) := by omega
              subst hj
              refine ⟨rfl, rfl, by simp, Or.inr ⟨rfl, ?_⟩⟩
              simp only [Option.some.injEq]
              apply Row.ext
              intro k
              rw [inRegion_iff] at hr
              by_cases hk : k = 0
              · subst hk
                rw [coeff_slot_at (le_refl 2)]
                rfl
              · rw [coeff_slot_high (le_refl 2) (by omega), hr k (by omega)]
            · exact ⟨rfl, rfl, rfl, Or.inl rfl⟩
          · simp only [hd2, if_false, add_zero]
            split
            · rename_i h2
              exfalso
              omega
            · exact ⟨rfl, rfl, rfl, Or.inl rfl⟩

/-- An emitted node of block `0` sits at the row of its origin. -/
def RowOK (ctx : Context) (p : Emit × Origin) : Prop :=
  ∃ cv, cell? ctx.source p.2.src = some cv ∧ official cv.row = p.1.row

theorem levelOneT_block0 {ctx : Context} {it : Item} (hI : Id0 1 it)
    {ps : List (Emit × Origin)} (h : levelOneT ctx it = .ok ps) : ∀ p ∈ ps, RowOK ctx p := by
  obtain ⟨hT, _, _, hcl⟩ := hI
  unfold levelOneT at h
  cases hsrc : nodeAt ctx.source ctx.x it.source with
  | none => simp [hsrc, pure, Except.pure] at h; subst h; simp
  | some q =>
      obtain ⟨srcRef, src⟩ := q
      obtain ⟨_, _, hscell, hsrow⟩ := nodeAt_spec hsrc
      simp only at hscell hsrow
      simp only [hsrc] at h
      rcases hcl with hC | ⟨_, hC⟩
      · simp only [hC] at h
        split at h
        · simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          intro p hp
          simp only [List.mem_singleton] at hp
          subst hp
          exact ⟨src, by simpa [Origin.src] using hscell, by rw [hsrow, hT]⟩
        · simp only [bind, Except.bind, pure, Except.pure] at h
          split at h
          · cases h
          · cases h
            intro p hp
            simp only [List.mem_singleton] at hp
            subst hp
            exact ⟨src, by simpa [Origin.src] using hscell, by rw [hsrow, hT]⟩
      · simp only [hC, hsrc, bind, Except.bind, pure, Except.pure] at h
        split at h
        · cases h
        · cases h
          intro p hp
          simp only [List.mem_singleton] at hp
          subst hp
          exact ⟨src, by simpa [Origin.src] using hscell, by rw [hsrow, hT]⟩

theorem runItemT_block0 {ctx : Context} (hb : ctx.block = 0) :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), Id0 d it →
      runItemT ctx d it = .ok ps → ∀ p ∈ ps, RowOK ctx p
  | 0, _, ps, _, h => by simp [runItemT, pure, Except.pure] at h; subst h; simp
  | 1, it, ps, hI, h => levelOneT_block0 hI (by simpa [runItemT] using h)
  | d + 2, it, ps, hI, h => by
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i children hch
        split at h
        · cases h
        · rename_i outs houts
          cases h
          intro p hp
          obtain ⟨out, hout, hpo⟩ := List.mem_flatten.mp hp
          obtain ⟨c, hc, hco⟩ := mem_of_mapM houts hout
          have hIc := childItems_block0 hb (by omega) hI hch c hc
          exact runItemT_block0 hb (d + 1) c out hIc hco p hpo

/-- **Block `0`.** Every emitted node of the lower part sits at the row of its origin. -/
theorem emitsT_block0 {ctx : Context} {τ : Row} (hb : ctx.block = 0)
    {es : List (Emit × Origin)} (h : emitsT ctx τ = .ok es) :
    ∀ p ∈ es, p.2.isUpper = false → RowOK ctx p := by
  unfold emitsT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i lower hlower
    split at h
    · cases h
    · rename_i upper hupper
      cases h
      intro p hp hup
      rcases List.mem_append.mp hp with hp | hp
      · unfold lowerT at hlower
        simp only [bind, Except.bind, pure, Except.pure] at hlower
        split at hlower
        · cases hlower
        · rename_i outs houts
          cases hlower
          obtain ⟨out, hout, hpo⟩ := List.mem_flatten.mp hp
          obtain ⟨q, hq, hqo⟩ := mem_of_mapM houts hout
          refine runItemT_block0 hb q.1 q.2 out ?_ hqo p hpo
          simp only [lowerItems, List.mem_flatMap, List.mem_reverse, List.mem_range,
            List.mem_map] at hq
          obtain ⟨_, _, _, _, rfl⟩ := hq
          exact ⟨rfl, rfl, rfl, Or.inl rfl⟩
      · unfold upperT at hupper
        obtain ⟨q, _, hqp⟩ := mem_of_mapM hupper hp
        simp only [bind, Except.bind, pure, Except.pure] at hqp
        split at hqp
        · cases hqp
        · cases hqp
          simp [Origin.isUpper] at hup

theorem mapKey_zero (cr : Nat) (K : RawKey) : mapKey cr 0 K = K := by
  unfold mapKey
  conv_rhs => rw [← List.map_id K]
  apply List.map_congr_left
  intro o _
  cases o with
  | none => rfl
  | some v => simp

/-- **`KeyLeShift` in block `0`.** The column `x₀` of the output copies the lower part
of the column `x₀` of `M(s)` row by row with the same legs, and the legs lie in the
common prefix: the output leg atom has the key of the leg atom of its origin. -/
theorem keyLe_block0 {s out : List Nat} {n D : Nat} {M : Mountain} {ρ : Root}
    {R : Mountain} {t : Cell}
    (hc : SpliceCase s n D M out ρ) (hR : Official.expandDiagram s n = .ok R)
    {X x i : Nat} (hXR : X < R.size) (hXeq : X = x + (ρ.x0 - ρ.cr) * i)
    (hx : x ∈ blockColumns ρ.cr ρ.x0 n i) (hi0 : i = 0)
    (hcopy : copyColumn (ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) (official t.row) = .ok R[X])
    {es : List (Emit × Origin)}
    (hes : emitsT (ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) (official t.row) = .ok es)
    {k : Nat} (hk : k < es.length) {e a : RawAtom}
    (he : legAtom? R D ⟨X, k + 1⟩ = some e) (ha : legAtom? M D es[k].2.src = some a)
    (hnot : ¬ (es[k].2.isUpper = true ∧ a.parent < ρ.cr)) :
    keyLe (D + 1) e.key (mapKey ρ.cr ((ρ.x0 - ρ.cr) * i) a.key) = true := by
  subst hi0
  rw [mul_zero, mapKey_zero]
  obtain ⟨_, _, _, _, _, hcrx, hinv⟩ := spliceCase_data hc hR
  have hA := hinv.1
  have hV := build_valid_of_success hc.build
  have hxx : x = ρ.x0 := by simpa [blockColumns] using hx
  subst hxx
  simp only [mul_zero, add_zero] at hXeq
  subst hXeq
  obtain ⟨hvcol, hvidx, cv, hcv, hleft⟩ := emitsT_good hes es[k] (List.getElem_mem hk)
  have hapar := legAtom_parent_lt hV ha
  -- the origin is not in the upper part
  have hlow : es[k].2.isUpper = false := by
    by_contra hup
    simp only [Bool.not_eq_false] at hup
    rw [hup] at hvcol
    simp only [if_true, upperColumn, ctxAt, if_true] at hvcol
    exact hnot ⟨hup, by rw [hvcol] at hapar; exact hapar⟩
  rw [hlow] at hvcol
  simp only [Bool.false_eq_true, if_false, ctxAt] at hvcol
  obtain ⟨cv', hcv', hrowv⟩ := emitsT_block0 (by rfl) hes es[k] (List.getElem_mem hk) hlow
  simp only [ctxAt] at hcv hcv'
  rw [hcv] at hcv'
  cases hcv'
  -- the assembled cell
  obtain ⟨es', hes', hasm⟩ := copyColumn_emitsT hcopy
  have hee : es' = es := Except.ok.inj (hes'.symm.trans hes)
  subst hee
  obtain ⟨_, hcells⟩ := assemble_spec hasm
  obtain ⟨cell, hcellX, hrow, ref, hrefl, hrefc⟩ := hcells k (by simpa using hk)
  simp only [List.getElem_map] at hrow hrefc
  -- the leg of the origin and of the output node
  obtain ⟨l, hl, hrefl'⟩ : ∃ l : Ref, cv.left = some l ∧ ref.column = l.column := by
    rcases hleft with ⟨l, hl, hlc⟩ | ⟨hnone, h0, _⟩
    · refine ⟨l, hl, ?_⟩
      rw [hrefc]
      simp only [legColumn, hlc, ctxAt, mul_zero, add_zero, ite_self]
    · have hi1 := index_one_of_official_zero hV hcv hvidx h0
      have hbl := bottom_left hc.build hcv hi1 (by omega)
      refine ⟨_, hbl, ?_⟩
      rw [hrefc]
      simp only [legColumn, hnone, ctxAt, Array.size_extract]
      rw [hvcol]
      omega
  have hlx : l.column < ρ.x0 := by
    have := left_lt_of_valid hV hcv hl
    omega
  have hrow' : cell.row = cv.row := by
    rw [hrow, ← hrowv, stored_official (one_le_row hV hcv hvidx)]
  have hcu : cell? R ⟨ρ.x0, k + 1⟩ = some cell := by
    simp only [cell?, Array.getElem?_eq_getElem hXR, Option.bind_eq_bind, Option.bind_some]
    exact hcellX
  have hhigh : highestAtMost R l.column cv.row = highestAtMost M l.column cv.row :=
    (highestAtMost_congr hA hlx cv.row).symm
  unfold legAtom? at he ha
  simp only [hcu, hrefl, Option.bind_eq_bind, Option.bind_some, hrow', hrefl'] at he
  simp only [hcv, hl, Option.bind_eq_bind, Option.bind_some] at ha
  rw [hhigh] at he
  cases hp : highestAtMost M l.column cv.row with
  | none => rw [hp] at ha; cases ha
  | some p =>
      rw [hp] at ha he
      simp only [Option.bind_some, Option.pure_def, Option.some.injEq] at ha he
      subst ha he
      have hpc := (highestAtMost_cell hp).1
      rw [keyAt_congr hA D cv.row (show p.column < ρ.x0 by omega)]
      exact keyLe_refl _ _

end OmegaY.Official.Classification.Proofs
