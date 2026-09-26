/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/KeyUpper.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.KeyWitness

set_option backward.do.legacy false

/-!
# The keys of the upper part with a leg left of the root column

A node of the upper part (rows `≥ τ`, notes/03 §2.5) is a copy of a node `v` of the
source column `x'` at the same row, with the same leg column `ℓ`. When `ℓ < cr`, the
leg column lies in the common prefix of the input and output mountains, so the output
leg atom has the same key as the leg atom of `v`, and the column map does not move it
(`keyOK_upper_low`). In the numerical tests every upper-part node at a block boundary
has `ℓ < cr`; inside a block most have `ℓ ≥ cr`.
-/

namespace OmegaY.Official.Classification

open Canonical Reserve Official Descent

theorem stored_official {r : Row} (h : (1 : Row) ≤ r) : stored (official r) = r := by
  unfold official
  by_cases hf : isFinite r = true
  · rw [if_pos hf]
    have hf' := (isFinite_iff r).mp hf
    have h0 : 1 ≤ r.coeff 0 := by
      by_contra hlt
      have hr1 : r < (1 : Row) := Row.lt_iff.mpr ⟨0, fun j hj => by
        rw [hf' j (by omega)]
        change 0 = Row.coeff ((1 : Nat) : Row) j
        rw [Row.coeff_nat]; simp; omega, by
        change r.coeff 0 < Row.coeff ((1 : Nat) : Row) 0
        rw [Row.coeff_nat]; simp; omega⟩
      exact absurd h (not_le.mpr hr1)
    have hcast : isFinite ((r.coeff 0 - 1 : Nat) : Row) = true := by
      rw [isFinite_iff]
      intro i hi
      rw [Row.coeff_nat]
      simp; omega
    unfold stored
    rw [if_pos hcast]
    apply Row.ext
    intro i
    rw [Row.coeff_nat, Row.coeff_nat]
    by_cases hi : i = 0
    · subst hi; simp; omega
    · simp [hi, hf' i (by omega)]
  · rw [if_neg hf]
    unfold stored
    rw [if_neg hf]

theorem mapKey_of_lt {cr sh : Nat} {K : RawKey} (h : ∀ v, some v ∈ K → v < cr) :
    mapKey cr sh K = K := by
  unfold mapKey
  conv_rhs => rw [← List.map_id K]
  apply List.map_congr_left
  intro o ho
  cases o with
  | none => rfl
  | some v => simp [h v ho]

theorem runItemT_not_upper (ctx : Context) :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), runItemT ctx d it = .ok ps →
      ∀ p ∈ ps, p.2.isUpper = false
  | 0, _, ps, h => by simp [runItemT, pure, Except.pure] at h; subst h; simp
  | 1, it, ps, h => by
      simp only [runItemT] at h
      unfold levelOneT at h
      intro p hp
      split at h
      · simp [pure, Except.pure] at h; subst h; simp at hp
      · split at h
        · split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · simp only [bind, Except.bind, pure, Except.pure] at h
            split at h
            · cases h
            · cases h
              simp only [List.mem_singleton] at hp
              subst hp
              rfl
        · split at h
          · simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            simp only [List.mem_singleton] at hp
            subst hp
            rfl
          · simp only [bind, Except.bind, pure, Except.pure] at h
            split at h
            · cases h
            · cases h
              simp only [List.mem_singleton] at hp
              subst hp
              rfl
  | d + 2, it, ps, h => by
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i outs houts
          cases h
          intro p hp
          obtain ⟨out, hout, hpo⟩ := List.mem_flatten.mp hp
          obtain ⟨c, _, hc⟩ := mem_of_mapM houts hout
          exact runItemT_not_upper ctx (d + 1) c out hc p hpo

/-- An upper-part emit copies the row of its origin. -/
theorem emitsT_upper_row {ctx : Context} {τ : Row} {es : List (Emit × Origin)}
    (h : emitsT ctx τ = .ok es) :
    ∀ p ∈ es, p.2.isUpper = true → ∃ cv, cell? ctx.source p.2.src = some cv ∧
      p.1.row = official cv.row := by
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
          obtain ⟨q, _, hq⟩ := mem_of_mapM houts hout
          rw [runItemT_not_upper ctx q.1 q.2 out hq p hpo] at hup
          cases hup
      · unfold upperT at hupper
        obtain ⟨q, hq, hqp⟩ := mem_of_mapM hupper hp
        obtain ⟨_, _, hqcell⟩ := mem_realNodes (List.mem_of_mem_filter hq)
        simp only [bind, Except.bind, pure, Except.pure] at hqp
        cases hlc : leftColumn q.2 with
        | error e => rw [hlc] at hqp; cases hqp
        | ok v =>
            rw [hlc] at hqp
            cases hqp
            exact ⟨q.2, by simpa [Origin.src] using hqcell, rfl⟩

/-- **The upper part with a leg left of the root column.** -/
theorem keyOK_upper_low {s out : List Nat} {n D : Nat} {M : Mountain} {ρ : Root}
    {R : Mountain} {t : Cell}
    (hc : SpliceCase s n D M out ρ) (hR : Official.expandDiagram s n = .ok R)
    {X x i : Nat} (hXR : X < R.size)
    (hcopy : copyColumn (ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) (official t.row) = .ok R[X])
    {es : List (Emit × Origin)}
    (hes : emitsT (ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) (official t.row) = .ok es)
    {k : Nat} (hk : k < es.length) {e a : RawAtom}
    (he : legAtom? R D ⟨X, k + 1⟩ = some e) (ha : legAtom? M D es[k].2.src = some a)
    (hup : es[k].2.isUpper = true) (hlow : a.parent < ρ.cr) :
    KeyOK D ρ.cr (ρ.x0 - ρ.cr) ρ.x0 ρ.control X es[k].2 e a := by
  obtain ⟨_, _, _, _, _, hcrx, hinv⟩ := spliceCase_data hc hR
  have hA := hinv.1
  have hV := build_valid_of_success hc.build
  obtain ⟨es', hes', hasm⟩ := copyColumn_emitsT hcopy
  have hee : es' = es := Except.ok.inj (hes'.symm.trans hes)
  subst hee
  obtain ⟨_, hcells⟩ := assemble_spec hasm
  obtain ⟨cell, hcellX, hrow, ref, hrefl, hrefc⟩ := hcells k (by simpa using hk)
  simp only [List.getElem_map] at hrow hrefc
  obtain ⟨hvcol, hvidx, cv, hcv, hleft⟩ := emitsT_good hes es'[k] (List.getElem_mem hk)
  obtain ⟨cv', hcv', hrowv⟩ := emitsT_upper_row hes es'[k] (List.getElem_mem hk) hup
  simp only [ctxAt] at hcv hcv'
  rw [hcv] at hcv'
  cases hcv'
  -- the origin's leg
  obtain ⟨l, hl, hlc⟩ : ∃ l : Ref, cv.left = some l ∧ es'[k].1.leftColumn = some l.column := by
    rcases hleft with h' | ⟨_, _, hnu⟩
    · exact h'
    · rw [hup] at hnu; cases hnu
  obtain ⟨a', ha', hap, _, _, _⟩ := legAtom?_exists hV D hcv hvidx hl
  rw [ha] at ha'
  cases ha'
  -- the output node has the row and the leg of its origin
  have hrow' : cell.row = cv.row := by
    rw [hrow, hrowv, stored_official (one_le_row hV hcv hvidx)]
  have hrefc' : ref.column = l.column := by
    rw [hrefc]
    simp only [legColumn, hlc, ctxAt]
    by_cases hh : ρ.cr ≤ l.column
    · omega
    · simp [hh]
  have hcu : cell? R ⟨X, k + 1⟩ = some cell := by
    simp only [cell?, Array.getElem?_eq_getElem hXR, Option.bind_eq_bind, Option.bind_some]
    exact hcellX
  -- both keys are computed in the common prefix
  have hlx : l.column < ρ.x0 := by omega
  have hhigh : highestAtMost R l.column cv.row = highestAtMost M l.column cv.row :=
    (highestAtMost_congr hA hlx cv.row).symm
  unfold legAtom? at he ha
  simp only [hcu, hrefl, Option.bind_eq_bind, Option.bind_some, hrow', hrefc'] at he
  simp only [hcv, hl, Option.bind_eq_bind, Option.bind_some] at ha
  rw [hhigh] at he
  cases hp : highestAtMost M l.column cv.row with
  | none => rw [hp] at ha; cases ha
  | some p =>
      rw [hp] at ha he
      simp only [Option.bind_some, Option.pure_def, Option.some.injEq] at ha he
      subst ha he
      have hpc := (highestAtMost_cell hp).1
      have hkey : keyAt R D cv.row p = keyAt M D cv.row p :=
        (keyAt_congr hA D cv.row (show p.column < ρ.x0 by omega)).symm
      unfold KeyOK
      rw [if_neg (by simp [hup])]
      simp only
      rw [hkey, mapKey_of_lt (fun v hv => by have := keyAt_entry hv; omega)]
      exact keyLe_refl _ _

end OmegaY.Official.Classification

#print axioms OmegaY.Official.Classification.keyOK_upper_low
