/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/KeyShift.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Bridge

set_option backward.do.legacy false

/-!
# `KeyLeRest` with one shift per block

`Control.KeyLeRest` bounds the key of the output leg atom `e` of a node of the copied
column `X = x + w·i` by the key of the leg atom `a` of its origin, mapped with
`μ_b` (`b·w`) at a block boundary outside the upper part and with `μ_{b+1}`
(`(b+1)·w`) otherwise, where `b = ⌊(X - x₀)/w⌋`.

In every case that `KeyLeRest` asks about, this shift is `w·i`, the shift of the
block `i` that produced the column (`keyOK3_of_shift`):

* at a boundary `X = x₀ + b·w` outside the upper part, the source column is `x = x₀`
  and `b = i`;
* inside a block (`cr < x < x₀`), `b + 1 = i`;
* the remaining case, an upper-part node of a boundary column, has its origin in the
  root column `cr` (`upperColumn`), so its leg is left of `cr`: this is the case
  `KeyLeRest` excludes (it is `KeyUpper.keyOK_upper_low`).

So `KeyLeRest` follows from `KeyLeShift`: `key(e) ≤ φ_i(key(a))`, where `φ_i` is the
column map of block `i` (`c ↦ c` for `c < cr`, `c ↦ c + w·i` otherwise), the same map
that places the legs of the copied column (`Assemble.legColumn`).
-/

namespace OmegaY.Official.Classification.Proofs

open Canonical Reserve Official Descent Classification

/-- **`KeyLeRest` with the block shift `w·i`.** -/
def KeyLeShift : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), SpliceCase s n D M out ρ → DegreeOK s D →
    Official.expandDiagram s n = .ok R → Canonical.build out = .ok R →
    M[M.size - 1]? = some col → col.back? = some t →
    ∀ X x i (_ : ρ.x0 ≤ X) (hXR : X < R.size), X = x + (ρ.x0 - ρ.cr) * i → i < n + 1 →
      x ∈ blockColumns ρ.cr ρ.x0 n i →
      copyColumn (ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) (official t.row) = .ok R[X] →
      ∀ es, emitsT (ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) (official t.row) = .ok es →
      ∀ k (hk : k < es.length) e a, legAtom? R D ⟨X, k + 1⟩ = some e →
        legAtom? M D es[k].2.src = some a →
        ¬ (es[k].2.isUpper = true ∧ a.parent < ρ.cr) →
        keyLe (D + 1) e.key (mapKey ρ.cr ((ρ.x0 - ρ.cr) * i) a.key) = true

/-- The leg of a leg atom is left of its node. -/
theorem legAtom_parent_lt {M : Mountain} (hV : MountainValid M) {D : Nat} {u : Ref}
    {a : RawAtom} (h : legAtom? M D u = some a) : a.parent < u.column := by
  obtain ⟨_, cu, l, hcu, hl, hap⟩ := legAtom?_spec h
  rw [hap]
  exact left_lt_of_valid hV hcu hl

/-- The shift of `KeyOK3` is the block shift `w·i` in every case that `KeyLeRest`
asks about. -/
theorem keyOK3_of_shift {s out : List Nat} {n D : Nat} {M R : Mountain} {ρ : Root}
    {t : Cell} (hc : SpliceCase s n D M out ρ) (hR : Official.expandDiagram s n = .ok R)
    {X x i : Nat} (hXeq : X = x + (ρ.x0 - ρ.cr) * i) (hx : x ∈ blockColumns ρ.cr ρ.x0 n i)
    {es : List (Emit × Origin)}
    (hes : emitsT (ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) (official t.row) = .ok es)
    {k : Nat} (hk : k < es.length) {e a : RawAtom}
    (ha : legAtom? M D es[k].2.src = some a)
    (hnot : ¬ (es[k].2.isUpper = true ∧ a.parent < ρ.cr))
    (hkey : keyLe (D + 1) e.key (mapKey ρ.cr ((ρ.x0 - ρ.cr) * i) a.key) = true) :
    KeyOK3 D ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X es[k].2 e a := by
  obtain ⟨_, _, _, _, _, hcrx, _⟩ := spliceCase_data hc hR
  have hV := build_valid_of_success hc.build
  obtain ⟨P, hPdef, hXP, hcase⟩ := block_cases hcrx hx hXeq
  rw [hPdef] at hkey
  obtain ⟨hvcol, _, _⟩ := emitsT_good hes es[k] (List.getElem_mem hk)
  have hapar := legAtom_parent_lt hV ha
  unfold KeyOK3
  generalize blockOf ρ.x0 (ρ.x0 - ρ.cr) X = b at hcase ⊢
  by_cases hcond : X = ρ.x0 + b * (ρ.x0 - ρ.cr) ∧ es[k].2.isUpper = false
  · rw [if_pos hcond]
    have hbw : b * (ρ.x0 - ρ.cr) = P := by
      rcases hcase with ⟨_, h2⟩ | ⟨h1, _, _, h4⟩
      · exact h2
      · omega
    rw [hbw]
    exact hkey
  · rw [if_neg hcond]
    rcases hcase with ⟨h1, h2⟩ | ⟨_, _, _, h4⟩
    · exfalso
      have hup : es[k].2.isUpper = true := by
        by_contra hne
        exact hcond ⟨by omega, by simpa using hne⟩
      rw [hup] at hvcol
      simp only [if_true, upperColumn, ctxAt, h1, if_true] at hvcol
      exact hnot ⟨hup, by rw [hvcol] at hapar; exact hapar⟩
    · have : (b + 1) * (ρ.x0 - ρ.cr) = P := by rw [Nat.add_mul, one_mul]; exact h4
      rw [this]
      exact hkey

/-- **`KeyLeRest` from `KeyLeShift`.** -/
theorem keyLeRest_of_shift (h : KeyLeShift) : KeyLeRest := by
  intro s n D M out ρ R col t hc hdeg hR hRb hcol ht X x i hX0 hXR hXeq hi hx hcopy es hes k hk
    e a he ha hnot
  exact keyOK3_of_shift hc hR hXeq hx hes hk ha hnot
    (h s n D M out ρ R col t hc hdeg hR hRb hcol ht X x i hX0 hXR hXeq hi hx hcopy es hes k hk
      e a he ha hnot)

end OmegaY.Official.Classification.Proofs
