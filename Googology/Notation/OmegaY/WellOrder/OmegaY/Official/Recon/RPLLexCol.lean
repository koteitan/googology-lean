/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/RPLLexCol.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RPLLexBase

set_option backward.do.legacy false

/-!
# The order of the origins in a copied column

For the emits `es` of a copied column of a block `i ≥ 1` (`emitsT`), with origins read in
`M(s)`:

* the official rows of the origins do not decrease (`orow_mono`, from `emitsT_order`);
* two emits whose origins have the same official row have the same origin (`src_eq_of_row`):
  lower origins are nodes of the column `x` below `τ`, upper origins nodes of the column read by
  the upper part at or above `τ`;
* so the emits of one origin are consecutive (`contig`), and after the last emit of an origin `v`
  comes an emit of the node `v⁺` above `v`, if `v⁺` has one (`succ`);
* the rank of an emit among the emits of its origin (`rk`, a count in a prefix) and the number
  `cnt v` of emits of `v` decide whether the next emit has the same origin (`next_same`,
  `next_other`).
-/

namespace OmegaY.Official.Recon.RPLLex

open Canonical Expansion Geometry Frame Classification
open Reserve (cell?)
open Classification.Proofs.ChainCorr (cutOrigin)
open Classification.Proofs.ChainCorr.Inner (SrcRel emitsT_order index_le_of_row_le ref_ext)
open Classification.Proofs.CopyShape.NoMA (NNC)

/-! ## Counting in prefixes -/

/-- The number of emits with origin `v`. -/
def cnt (es : List (Emit × Origin)) (v : Ref) : Nat := es.countP (fun e => decide (e.2.src = v))

/-- The rank of the emit `a` among the emits with origin `v` (counting `a`). -/
def rk (es : List (Emit × Origin)) (v : Ref) (a : Nat) : Nat :=
  (es.take (a + 1)).countP (fun e => decide (e.2.src = v))

theorem cnt_split (es : List (Emit × Origin)) (v : Ref) (a : Nat) :
    cnt es v = rk es v a + (es.drop (a + 1)).countP (fun e => decide (e.2.src = v)) := by
  unfold cnt rk
  rw [← List.countP_append, List.take_append_drop]

theorem rk_succ (es : List (Emit × Origin)) (v : Ref) {a : Nat} (ha : a + 1 < es.length) :
    rk es v (a + 1) = rk es v a + (if es[a + 1].2.src = v then 1 else 0) := by
  unfold rk
  rw [List.take_succ, List.countP_append, List.getElem?_eq_getElem ha]
  simp

theorem rk_le_cnt (es : List (Emit × Origin)) (v : Ref) (a : Nat) : rk es v a ≤ cnt es v := by
  rw [cnt_split es v a]; omega

/-- A later emit with origin `v` when the rank is below the count. -/
theorem later_of_rk_lt {es : List (Emit × Origin)} {v : Ref} {a : Nat}
    (h : rk es v a < cnt es v) : ∃ b, ∃ hb : b < es.length, a < b ∧ es[b].2.src = v := by
  rw [cnt_split es v a] at h
  have hpos : 0 < (es.drop (a + 1)).countP (fun e => decide (e.2.src = v)) := by omega
  obtain ⟨e, he, hev⟩ := List.countP_pos_iff.mp hpos
  obtain ⟨k, hk, hke⟩ := List.getElem_of_mem he
  simp only [List.length_drop] at hk
  refine ⟨a + 1 + k, by omega, by omega, ?_⟩
  rw [List.getElem_drop] at hke
  rw [hke]
  simpa using hev

/-- No later emit with origin `v` when the rank is the count. -/
theorem no_later_of_rk_eq {es : List (Emit × Origin)} {v : Ref} {a : Nat}
    (h : rk es v a = cnt es v) : ∀ b (hb : b < es.length), a < b → es[b].2.src ≠ v := by
  intro b hb hab hbv
  rw [cnt_split es v a] at h
  have h0 : (es.drop (a + 1)).countP (fun e => decide (e.2.src = v)) = 0 := by omega
  rw [List.countP_eq_zero] at h0
  have hmem : es[b] ∈ es.drop (a + 1) := by
    have : es[b] = (es.drop (a + 1))[b - (a + 1)]'(by simp; omega) := by
      rw [List.getElem_drop]; congr 1; omega
    rw [this]; exact List.getElem_mem _
  have := h0 _ hmem
  simp [hbv] at this

/-- The rank of the first emit of an origin is `1`. -/
theorem rk_first {es : List (Emit × Origin)} {v : Ref} {a : Nat} (ha : a < es.length)
    (hv : es[a].2.src = v) (hfirst : ∀ b (hb : b < es.length), b < a → es[b].2.src ≠ v) :
    rk es v a = 1 := by
  unfold rk
  rw [List.take_succ, List.countP_append, List.getElem?_eq_getElem ha]
  have h0 : (es.take a).countP (fun e => decide (e.2.src = v)) = 0 := by
    rw [List.countP_eq_zero]
    intro e he hev
    obtain ⟨k, hk, hke⟩ := List.getElem_of_mem he
    simp only [List.length_take] at hk
    rw [List.getElem_take] at hke
    have := hfirst k (by omega) (by omega)
    rw [hke] at this
    simp at hev
    exact this hev
  rw [h0]
  simp [hv]

/-! ## The facts of a copied column -/

/-- The facts of the emits of a copied column of a block `i ≥ 1` used here. -/
structure ColOK (ctx : Context) (τ : Row) (es : List (Emit × Origin)) : Prop where
  hes : emitsT ctx τ = .ok es
  hV : MountainValid ctx.source
  nnc : es.Pairwise NNC
  cov : ∀ (p : Ref) (c : Cell), p.column = ctx.x → 1 ≤ p.index → cell? ctx.source p = some c →
    (official c.row < τ ∨ upperColumn ctx = ctx.x) →
      ∃ q ∈ es, q.2.src = p ∧ cutOrigin q.2 = false

section Col

variable {ctx : Context} {τ : Row} {es : List (Emit × Origin)}

theorem ColOK.cell (C : ColOK ctx τ es) {a : Nat} (ha : a < es.length) :
    ∃ c, cell? ctx.source es[a].2.src = some c := by
  obtain ⟨_, _, c, hc, _⟩ := emitsT_good C.hes es[a] (List.getElem_mem ha)
  exact ⟨c, hc⟩

theorem ColOK.one_le (C : ColOK ctx τ es) {a : Nat} (ha : a < es.length) {c : Cell}
    (hc : cell? ctx.source es[a].2.src = some c) : (1 : Row) ≤ c.row := by
  obtain ⟨_, hidx, _⟩ := emitsT_good C.hes es[a] (List.getElem_mem ha)
  exact one_le_row C.hV hc hidx

/-- The upper emits are exactly the emits whose origin is at or above `τ`. -/
theorem ColOK.upper_iff (C : ColOK ctx τ es) {a : Nat} (ha : a < es.length) {c : Cell}
    (hc : cell? ctx.source es[a].2.src = some c) :
    es[a].2.isUpper = true ↔ τ ≤ official c.row := by
  obtain ⟨lo, us, hlo, hus, hsplit⟩ := LowerPB.emitsT_split C.hes
  have hmem : es[a] ∈ lo ++ us := by rw [← hsplit]; exact List.getElem_mem ha
  rcases List.mem_append.mp hmem with h | h
  · have hnu := (LowerPB.lowerT_good hlo _ h).2
    obtain ⟨c', hc', hlt⟩ := (Classification.Proofs.ChainCorr.CopyMonoProof.lowerT_mono hlo).2 _ h
    rw [hc] at hc'
    obtain rfl := Option.some.inj hc'
    rw [hnu]
    constructor
    · intro h; cases h
    · intro h; exact absurd (lt_of_lt_of_le hlt h) (lt_irrefl _)
  · have hu := CrossPlain.upperT_isUpper hus _ h
    obtain ⟨c', hc', hle⟩ :=
      (Classification.Proofs.ChainCorr.CopyMonoProof.upperT_mono C.hV hus).2 _ h
    rw [hc] at hc'
    obtain rfl := Option.some.inj hc'
    exact ⟨fun _ => hle, fun _ => hu⟩

/-- The column of the origin of an emit. -/
theorem ColOK.col (C : ColOK ctx τ es) {a : Nat} (ha : a < es.length) :
    es[a].2.src.column = (if es[a].2.isUpper then upperColumn ctx else ctx.x) :=
  (emitsT_good C.hes es[a] (List.getElem_mem ha)).1

/-- **The official rows of the origins do not decrease.** -/
theorem ColOK.orow_mono (C : ColOK ctx τ es) {a b : Nat} (ha : a < es.length)
    (hb : b < es.length) (hab : a ≤ b) {c c' : Cell} (hc : cell? ctx.source es[a].2.src = some c)
    (hc' : cell? ctx.source es[b].2.src = some c') : official c.row ≤ official c'.row := by
  rcases Nat.lt_or_eq_of_le hab with h | h
  · have hrel := List.pairwise_iff_getElem.mp (emitsT_order C.hV C.hes) a b ha hb h c c' hc hc'
    rcases hrel with h' | ⟨h', _⟩
    · exact h'.le
    · exact h'.le
  · subst h
    rw [hc] at hc'
    obtain rfl := Option.some.inj hc'
    exact le_rfl

/-- **The same official row gives the same origin.** -/
theorem ColOK.src_eq_of_row (C : ColOK ctx τ es) {a b : Nat} (ha : a < es.length)
    (hb : b < es.length) {c c' : Cell} (hc : cell? ctx.source es[a].2.src = some c)
    (hc' : cell? ctx.source es[b].2.src = some c') (hr : official c.row = official c'.row) :
    es[a].2.src = es[b].2.src := by
  have hu : es[a].2.isUpper = es[b].2.isUpper := by
    have h1 := C.upper_iff ha hc
    have h2 := C.upper_iff hb hc'
    rw [hr] at h1
    cases ha' : es[a].2.isUpper <;> cases hb' : es[b].2.isUpper
    · rfl
    · exfalso
      rw [ha'] at h1
      rw [hb'] at h2
      have := h1.mpr (h2.mp rfl)
      cases this
    · exfalso
      rw [ha'] at h1
      rw [hb'] at h2
      have := h2.mpr (h1.mp rfl)
      cases this
    · rfl
  have hcol : es[a].2.src.column = es[b].2.src.column := by rw [C.col ha, C.col hb, hu]
  have h1 := C.one_le ha hc
  have h2 := C.one_le hb hc'
  have e1 : c.row ≤ c'.row := CrossUpperSim.le_of_official_le h2 hr.le
  have e2 : c'.row ≤ c.row := CrossUpperSim.le_of_official_le h1 hr.ge
  have i1 := index_le_of_row_le C.hV hcol hc hc' e1
  have i2 := index_le_of_row_le C.hV hcol.symm hc' hc e2
  exact ref_ext hcol (by omega)

/-- **The emits of one origin are consecutive.** -/
theorem ColOK.contig (C : ColOK ctx τ es) {a m b : Nat} (hb : b < es.length) (ham : a ≤ m)
    (hmb : m ≤ b) (hab : es[a].2.src = es[b].2.src) :
    es[m].2.src = es[a].2.src := by
  have ha : a < es.length := by omega
  have hm : m < es.length := by omega
  obtain ⟨c, hc⟩ := C.cell ha
  obtain ⟨cm, hcm⟩ := C.cell hm
  have hc' : cell? ctx.source es[b].2.src = some c := by rw [← hab]; exact hc
  have h1 := C.orow_mono ha hm ham hc hcm
  have h2 := C.orow_mono hm hb hmb hcm hc'
  exact C.src_eq_of_row hm ha hcm hc (le_antisymm h2 h1)

/-- **The next origin.** After an emit of `v`, an emit with another origin has the origin `v⁺`
when `v⁺` has an emit. -/
theorem ColOK.succ (C : ColOK ctx τ es) {a p : Nat} (ha : a + 1 < es.length)
    (hp : p < es.length) {v : Ref} (hv : es[a].2.src = v) (hne : es[a + 1].2.src ≠ v)
    (hpv : es[p].2.src = ⟨v.column, v.index + 1⟩) : es[a + 1].2.src = ⟨v.column, v.index + 1⟩ := by
  have ha' : a < es.length := by omega
  obtain ⟨cv, hcva⟩ := C.cell ha'
  obtain ⟨cn, hcn⟩ := C.cell ha
  obtain ⟨cp, hcpp⟩ := C.cell hp
  have hcv : cell? ctx.source v = some cv := by rw [← hv]; exact hcva
  have hcp : cell? ctx.source ⟨v.column, v.index + 1⟩ = some cp := by rw [← hpv]; exact hcpp
  have hcv1 : (1 : Row) ≤ cv.row := C.one_le ha' hcva
  have hcn1 : (1 : Row) ≤ cn.row := C.one_le ha hcn
  -- `v` is strictly below `v⁺`
  have hvlt : cv.row < cp.row := by
    by_contra hn
    push Not at hn
    have := index_le_of_row_le C.hV (a := ⟨v.column, v.index + 1⟩) (b := v) rfl hcp hcv hn
    simp at this
  have hcp1 : (1 : Row) ≤ cp.row := le_trans hcv1 hvlt.le
  have hovlt : official cv.row < official cp.row := Recon.official_strictMono hcv1 hvlt
  -- `p` is after `a`
  have hap : a < p := by
    by_contra hn
    push Not at hn
    have := C.orow_mono hp ha' hn hcpp hcva
    exact absurd (lt_of_lt_of_le hovlt this) (lt_irrefl _)
  have h1 := C.orow_mono ha' ha (by omega) hcva hcn
  have h2 := C.orow_mono ha hp (by omega) hcn hcpp
  -- the origin of `a + 1` is in the column of `v`
  have hcol : es[a + 1].2.src.column = v.column := by
    cases h3 : es[a + 1].2.isUpper
    · have hτn : ¬ τ ≤ official cn.row := by
        intro h
        have := (C.upper_iff ha hcn).mpr h
        rw [h3] at this
        cases this
      have hva : es[a].2.isUpper = false := by
        cases h5 : es[a].2.isUpper
        · rfl
        · exfalso
          exact hτn (le_trans ((C.upper_iff ha' hcva).mp h5) h1)
      have e1 := C.col ha
      have e2 := C.col ha'
      rw [h3] at e1
      rw [hva, hv] at e2
      simp only [Bool.false_eq_true, if_false] at e1 e2
      rw [e1, e2]
    · have hτn : τ ≤ official cn.row := (C.upper_iff ha hcn).mp h3
      have hpu : es[p].2.isUpper = true := (C.upper_iff hp hcpp).mpr (le_trans hτn h2)
      have e1 := C.col ha
      have e2 := C.col hp
      rw [h3] at e1
      rw [hpu, hpv] at e2
      simp only [if_true] at e1 e2
      rw [e1, ← e2]
  have i1 := index_le_of_row_le C.hV hcol.symm hcv hcn (CrossUpperSim.le_of_official_le hcn1 h1)
  have i2 := index_le_of_row_le C.hV (a := es[a + 1].2.src) (b := ⟨v.column, v.index + 1⟩)
    hcol hcn hcp (CrossUpperSim.le_of_official_le hcp1 h2)
  simp only at i2
  by_cases hidx : es[a + 1].2.src.index = v.index + 1
  · exact ref_ext hcol hidx
  · exfalso
    exact hne (ref_ext hcol (by omega))

/-- **The next emit has the same origin** when the rank is below the count. -/
theorem ColOK.next_same (C : ColOK ctx τ es) {a : Nat} (ha : a < es.length) {v : Ref}
    (hv : es[a].2.src = v) (hlt : rk es v a < cnt es v) :
    ∃ ha1 : a + 1 < es.length, es[a + 1].2.src = v := by
  obtain ⟨b, hb, hab, hbv⟩ := later_of_rk_lt hlt
  have ha1 : a + 1 < es.length := by omega
  exact ⟨ha1, (C.contig hb (by omega) (by omega) (hv.trans hbv.symm)).trans hv⟩

/-- **The next emit has another origin** when the rank is the count. -/
theorem ColOK.next_other {a : Nat} (ha1 : a + 1 < es.length) {v : Ref}
    (heq : rk es v a = cnt es v) : es[a + 1].2.src ≠ v :=
  no_later_of_rk_eq heq (a + 1) ha1 (by omega)

/-- If the next emit has the same origin, the rank is below the count. -/
theorem rk_lt_of_next {es : List (Emit × Origin)} {a : Nat} (ha1 : a + 1 < es.length) {v : Ref}
    (hv : es[a + 1].2.src = v) : rk es v a < cnt es v := by
  have h1 := rk_succ es v ha1
  have h2 := rk_le_cnt es v (a + 1)
  rw [if_pos hv] at h1
  omega

end Col

end OmegaY.Official.Recon.RPLLex
