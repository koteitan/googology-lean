/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Assemble.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Trace
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FinishSupport
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.Selection

set_option backward.do.legacy false

/-!
# The assembled column

`Official.assemble` turns the emitted nodes of a column into cells and finishes the
values with Phyrion's `Expansion.finish`. Because the emitted rows are strictly
increasing (checked by `assemble`), the finished column keeps their order: its real
cell `k + 1` has the stored row of the `k`-th emitted node and the left endpoint the
rule computed for it (`assemble_spec`). The column of that left endpoint is
`legColumn ctx em`: the image `φ_i(p)` of the source leg `p`, or the column left of
the new column for a bottom node.
-/

namespace OmegaY.Official.Classification

open Canonical Official

/-! ## Rows -/

theorem isFinite_iff (r : Row) : isFinite r = true ↔ ∀ i, 1 ≤ i → r.coeff i = 0 := by
  simp only [isFinite, decide_eq_true_eq, len_le_one_iff]

theorem finite_lt_infinite {a b : Row} (ha : ∀ i, 1 ≤ i → a.coeff i = 0)
    (hb : ¬ ∀ i, 1 ≤ i → b.coeff i = 0) : a < b := by
  push Not at hb
  obtain ⟨i0, hi0, hne⟩ := hb
  have hmem : i0 ∈ b.coeffs.support := Finsupp.mem_support_iff.mpr hne
  have hne' : b.coeffs.support.Nonempty := ⟨i0, hmem⟩
  set i := b.coeffs.support.max' hne' with hi
  have hi0le : i0 ≤ i := Finset.le_max' _ _ hmem
  have himem : i ∈ b.coeffs.support := Finset.max'_mem _ _
  refine Row.lt_iff.mpr ⟨i, ?_, ?_⟩
  · intro j hj
    rw [ha j (by omega)]
    by_contra hbj
    have hjmem : j ∈ b.coeffs.support := Finsupp.mem_support_iff.mpr (Ne.symm hbj)
    have := Finset.le_max' _ _ hjmem
    omega
  · rw [ha i (by omega)]
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp himem)

theorem stored_mono {a b : Row} (h : a ≤ b) : stored a ≤ stored b := by
  unfold stored
  by_cases ha : isFinite a = true
  · by_cases hb : isFinite b = true
    · rw [if_pos ha, if_pos hb]
      have ha' := (isFinite_iff a).mp ha
      have hb' := (isFinite_iff b).mp hb
      have h0 : a.coeff 0 ≤ b.coeff 0 := by
        by_contra hlt
        have hba : b < a := Row.lt_iff.mpr ⟨0, fun j hj => by
          rw [ha' j (by omega), hb' j (by omega)], by omega⟩
        exact absurd h (not_le.mpr hba)
      apply Row.le_of_coeff_le
      intro i
      simp only [Row.coeff_nat]
      split <;> omega
    · rw [if_pos ha, if_neg hb]
      apply le_of_lt
      apply finite_lt_infinite _ (fun h' => hb ((isFinite_iff b).mpr h'))
      intro i hi
      simp only [Row.coeff_nat]
      split <;> omega
  · by_cases hb : isFinite b = true
    · exfalso
      have hba := finite_lt_infinite ((isFinite_iff b).mp hb)
        (fun h' => ha ((isFinite_iff a).mpr h'))
      exact absurd h (not_le.mpr hba)
    · rw [if_neg ha, if_neg hb]
      exact h

/-! ## Loops of `assemble` -/

theorem forIn_check_ok {α ε : Type} (Q : α → Prop) [DecidablePred Q]
    (bad : Except ε (ForInStep PUnit)) (hbad : ∀ r, bad ≠ Except.ok r) :
    ∀ (xs : List α) (r : PUnit),
      forIn xs PUnit.unit (fun x _ => if ¬ Q x then bad else Except.ok (ForInStep.yield PUnit.unit))
        = Except.ok r → ∀ x ∈ xs, Q x := by
  intro xs
  induction xs with
  | nil => intro _ _ x hx; simp at hx
  | cons a as ih =>
      intro r h x hx
      simp only [List.forIn_cons] at h
      by_cases hQ : Q a
      · rw [if_neg (not_not.mpr hQ)] at h
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hQ
        · exact ih r h x hx
      · rw [if_pos hQ] at h
        cases hb : bad with
        | error e => rw [hb] at h; cases h
        | ok s => exact absurd hb (hbad s)

theorem pairwise_of_zip_tail {l : List Emit}
    (h : ∀ p ∈ l.zip l.tail, p.1.row < p.2.row) : (l.map Emit.row).Pairwise (· < ·) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have hl : ∀ p ∈ l.zip l.tail, p.1.row < p.2.row := by
        intro p hp
        cases l with
        | nil => simp at hp
        | cons b l' =>
            apply h
            simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]
            exact Or.inr hp
      have ihl := ih hl
      simp only [List.map_cons, List.pairwise_cons]
      refine ⟨?_, ihl⟩
      cases l with
      | nil => simp
      | cons b l' =>
          have hab : a.row < b.row := h (a, b) (by simp)
          intro y hy
          simp only [List.map_cons, List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact hab
          · simp only [List.map_cons, List.pairwise_cons] at ihl
            exact lt_trans hab (ihl.1 y hy)

/-! ## The shape of an assembled column -/

/-- The column of the left endpoint of an emitted node in the output. -/
def legColumn (ctx : Context) (em : Emit) : Nat :=
  match em.leftColumn with
  | some p => if ctx.rootColumn ≤ p then p + ctx.width * ctx.block else p
  | none => ctx.result.size - 1

theorem assemble_spec {ctx : Context} {emits : List Emit} {col : Column}
    (h : assemble ctx emits = .ok col) :
    col.size = emits.length + 1 ∧ ∀ k (hk : k < emits.length), ∃ cell : Cell,
      col[k + 1]? = some cell ∧ cell.row = stored emits[k].row ∧
      ∃ ref : Ref, cell.left = some ref ∧ ref.column = legColumn ctx emits[k] := by
  unfold assemble at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  by_cases hE : emits.isEmpty = true
  · rw [if_pos hE] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  · rw [if_neg hE] at h
    split at h
    · cases h
    · rename_i u hloop
      have hrows := forIn_check_ok (fun pair : Emit × Emit => pair.1.row < pair.2.row)
        (Except.error Error.rowsNotIncreasing) (fun r h' => by cases h') _ _ hloop
      split at h
      · cases h
      · rename_i cells hcells
        obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ hcells
        -- each cell has the stored row and the computed left endpoint
        have hcell : ∀ k (hk : k < emits.length) (hk' : k < cells.length),
            cells[k].row = stored emits[k].row ∧
            ∃ ref : Ref, cells[k].left = some ref ∧ ref.column = legColumn ctx emits[k] := by
          intro k hk hk'
          have hf := hall k hk hk'
          unfold legColumn
          split at hf
          · rename_i p hp
            simp only [hp]
            split at hf
            · cases hf
            · rename_i ref href
              rw [(Except.ok.inj hf).symm]
              refine ⟨rfl, ref, rfl, ?_⟩
              simp only [liftE, Except.mapError] at href
              split at href
              · cases href
              · rename_i r hr
                cases href
                obtain ⟨_, hcolq⟩ : ∃ nodes, ctx.result[if ctx.rootColumn ≤ p then
                    p + ctx.width * ctx.block else p]? = some nodes := by
                  unfold Expansion.below at hr
                  simp only [bind, Except.bind] at hr
                  split at hr
                  · cases hr
                  · rename_i nodes hn
                    unfold Expansion.columnAt at hn
                    split at hn
                    · rename_i c hc
                      exact ⟨nodes, by rw [hc, Except.ok.inj hn]⟩
                    · cases hn
                exact (Expansion.below_result hcolq hr).1
          · rename_i hp
            simp only [hp]
            split at hf
            · rw [(Except.ok.inj hf).symm]
              exact ⟨rfl, _, rfl, rfl⟩
            · simp [throw, throwThe, MonadExceptOf.throw] at hf
        simp only [liftE, Except.mapError] at h
        split at h
        · cases h
        · rename_i c hfin
          have hc : c = col := Except.ok.inj h
          subst hc
          have hshape := (Expansion.finish_success_spec hfin).1
          have hsorted : (phantom :: cells).Pairwise
              (fun a b : Cell => decide (a.row ≤ b.row) = true) := by
            have hr := pairwise_of_zip_tail hrows
            have hcr : cells.map Cell.row = emits.map (fun em => stored em.row) := by
              apply List.ext_getElem (by simp [hlen])
              intro k hk1 hk2
              simp only [List.getElem_map]
              exact (hcell k (by simpa using hk2) (by simpa using hk1)).1
            simp only [List.pairwise_cons, decide_eq_true_eq]
            refine ⟨fun a _ => by simp [phantom, Row.zero_le], ?_⟩
            have : (cells.map Cell.row).Pairwise (· ≤ ·) := by
              rw [hcr, List.pairwise_map]
              rw [List.pairwise_map] at hr
              exact hr.imp (fun hlt => stored_mono (le_of_lt hlt))
            rw [List.pairwise_map] at this
            exact this.imp (fun h' => by simpa using h')
          rw [List.mergeSort_of_pairwise hsorted] at hshape
          obtain ⟨hrowsEq, hleftsEq⟩ := hshape
          have hsize : c.size = cells.length + 1 := by
            have := congrArg List.length hrowsEq
            simp only [List.length_map, List.length_cons, Array.length_toList] at this
            omega
          refine ⟨by omega, ?_⟩
          intro k hk
          have hk' : k < cells.length := by omega
          have hkc : k + 1 < c.size := by omega
          obtain ⟨hrow, ref, hleft, hrefc⟩ := hcell k hk hk'
          refine ⟨c[k + 1], Array.getElem?_eq_getElem hkc, ?_, ref, ?_, hrefc⟩
          · have := congrArg (fun l => l[k + 1]?) hrowsEq
            simp only [List.getElem?_map, List.getElem?_cons_succ, Array.getElem?_toList,
              List.getElem?_eq_getElem hk', Array.getElem?_eq_getElem hkc, Option.map_some,
              Option.some.injEq] at this
            rw [← this, hrow]
          · have := congrArg (fun l => l[k + 1]?) hleftsEq
            simp only [List.getElem?_map, List.getElem?_cons_succ, Array.getElem?_toList,
              List.getElem?_eq_getElem hk', Array.getElem?_eq_getElem hkc, Option.map_some,
              Option.some.injEq] at this
            rw [← this, hleft]

end OmegaY.Official.Classification
