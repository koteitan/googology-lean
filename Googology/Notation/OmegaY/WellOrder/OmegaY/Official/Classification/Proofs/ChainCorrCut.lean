/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/ChainCorrCut.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrRegions

set_option backward.do.legacy false

/-!
# The two gap-copy regions from a lexicographic chain correspondence

`ChainCorrRegions.lean` proves five region lemmas from the entrywise key bound
`keyLe_keyAt_of_scale`. The two gap-copy regions (`RegionCutBoundary`,
`RegionCutInner`: a copy of the root row with `b = 1`) do not have an entrywise bound:
the output key can be larger at small scales, and the jump `d_e` of the output key
template can exceed the jump `d_a` of the origin's. The key is below only
lexicographically: the first scale (from the top) where the two keys differ has a
strictly smaller output entry.

This file

* proves the **lexicographic key bound** `keyLe_keyAt_of_lex` (and its special case with one
  strict scale, `keyLe_keyAt_of_strict`): at every scale `k` where the origin's key has an
  entry, either the output entry is at most the image of the origin's, or some higher
  scale `k' > k` has a strictly smaller output entry;
* proves a **lexicographic simulation theorem** `lex_of_sim` (the analogue of
  `bound_of_sim`): each step of the chain of `M(s)` is matched, or a higher scale has a
  strictly smaller root (`Wit`);
* reduces `RegionCutBoundary` and `RegionCutInner` to `StepInner` (open,
  `ChainCorrRegions.lean`) and five open statements about gap copies (`StepCut`, `CutLeg`,
  `CutJump`, `CutStartCopy`, `CutStartRoot`): `keyLeRegion_of_cut`,
  `regionCutBoundary_of_chains`, `regionCutInner_of_chains` (`CutLeg` is proved in
  `ChainCorrCutLeg.lean`);
* states well-foundedness from the reconstruction and the ten chain statements
  (`wellFounded_of_all_chains`).

## The open statements

Fix a block `i ≥ 1`, `w = x₀ - cr`, `B = cr + w·i` (the boundary column of the block)
and `φ = mapColumn cr (w·i)`. `CutNode i v m`: `v` is the node of an inner column
`y + w·i` (`cr < y < x₀`) whose origin is the gap copy (`b = 1`) of `m`.
`Wit k v m`: some scale `k < k' ≤ D` has `col root_R(k', v) < φ(col root_M(k', m))`.

For a node `u` of a gap-copy region, with origin `o`, leg `l` of `o`, `pa` the highest node
of column `l` at or below the row of `o` and `pe` the highest node of column `φ(l)` at or
below the row of `u`; `d_e = jump(row u, row pe)`, `d_a = jump(row o, row pa)`:

* `StepCut`: from a `CutNode` pair `(v, m)`, a step `m → m'` of the scale-`k` chain of
  `M(s)` (`k ≤ D`) is matched by the chain of `v` (`Next`, with `CopyNode ∪ CutNode`), or
  `Wit k v m`.
* `CutLeg`: `l ≥ cr`. **Proved** in `ChainCorrCutLeg.lean` (`cutLeg`).
* `CutJump`: `d_e ≤ d_a`, or some scale `k' ≥ max(d_e, d_a)` (`k' ≤ D`) has
  `col root_R(k', pe) < φ(col root_M(k', pa))`.
* `CutStartCopy`: for `l > cr`, `CutNode i pe pa` (`pe` is the gap copy of `pa`).
* `CutStartRoot`: for `l = cr`, the chain of `pe` reaches the next node of the chain of
  `pa` at every scale `d_a ≤ k ≤ D` (the statement `StartRoot`, for gap copies).

## Numerical tests

The statements were tested with `reference/official/cut-regions.cjs` (the rule of
`omegay-trace.cjs`, as `chain-corr.cjs`), with the smallest key dimension
`D = max degree of M(s), M(s[n])` and with `D + 1` (`--extraD 1`). Counts: node-scale pairs for `StepCut`,
nodes otherwise. No failure:

| sample | expansions | `StepCut` (matched / `Wit`) | `CutLeg`, `CutJump` | `CutStartCopy` | `CutStartRoot` |
|---|---:|---:|---:|---:|---:|
| standard S1–S3, S6, `n = 1,2,3` | 39090 | 2243590 / 90374 | 925614 | 579105 | 346509 |
| legal, length ≤ 6, entries ≤ 6 | 23325 | 634821 / 60709 | 225731 | 127549 | 98182 |
| legal, length ≤ 5, entries ≤ 8 | 12285 | 1950058 / 229242 | 467536 | 304226 | 163310 |
| random legal (`--random 20000,10,10,7`) | 37926 | 22883611 / 2351237 | 3941178 | 2960694 | 980484 |

Observed shape (standard samples): comparing `key(e)` with `φ(key(a))` scale by scale from
the top, the entries are equal down to the highest scale `k_h ≥ d_a` where the root of `pa`
is at or right of `cr`; there the output root is strictly left of `B` (so strictly below the
image `≥ B`), or all entries are equal. `StepCut` is matched at every scale where the root
of `m` is left of `cr`; the `Wit` cases are at smaller scales, and on the standard samples
the first witness scale `k'` always has the root of `m` at or right of `cr` and the root of
`v` strictly left of `B` (the chain of `v` crosses the boundary column; on random legal
sequences 20 of 2351237 first witnesses are of another kind). The witness of `CutJump`
always has this crossing form. In `CutStartCopy`, `pa` is always the node `(l, C)` of the
root row. `d_e > d_a` happens only in the strict case.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr

open Canonical Reserve Official Descent Classification Proofs

/-! ## Lexicographic key bounds -/

/-- **Lexicographic bound from entries.** At every index the entries are equal, or the
entry of `a` is strictly smaller, or an earlier index has a strictly smaller entry of `a`. -/
theorem keyLe_of_lexEntries {m : Nat} {a b : RawKey}
    (h : ∀ j, j < m → a[j]? = b[j]? ∨
      (∃ x y, a[j]? = some x ∧ b[j]? = some y ∧ entryLt x y = true) ∨
      ∃ j', j' < j ∧ ∃ x y, a[j']? = some x ∧ b[j']? = some y ∧ entryLt x y = true) :
    keyLe m a b = true := by
  by_cases hall : ∀ j, j < m → a[j]? = b[j]?
  · simp only [keyLe, Bool.or_eq_true]
    exact Or.inl (keyEq_spec.mpr hall)
  · push Not at hall
    have hex : ∃ j, j < m ∧ a[j]? ≠ b[j]? := hall
    classical
    let j := Nat.find hex
    have hj : j < m ∧ a[j]? ≠ b[j]? := Nat.find_spec hex
    have hmin : ∀ i, i < j → a[i]? = b[i]? := by
      intro i hi
      by_contra hne
      exact Nat.find_min hex hi ⟨by omega, hne⟩
    simp only [keyLe, Bool.or_eq_true]
    right
    rcases h j hj.1 with heq | ⟨x, y, hx, hy, hlt⟩ | ⟨j', hj', x, y, hx, hy, hlt⟩
    · exact absurd heq hj.2
    · exact keyLt_spec.mpr ⟨j, hj.1, hmin, by rw [hx, hy]; exact hlt⟩
    · exfalso
      have hxy := hmin j' hj'
      rw [hx, hy] at hxy
      obtain rfl := Option.some.inj hxy
      rw [entryLt_irrefl] at hlt
      exact Bool.false_ne_true hlt

/-- **Lexicographic key bound.** At every scale `k ≥ d_a` (where the origin's key has an
entry), either `d_e ≤ k` and the root of `pe` is at or left of the image of the root of
`pa`, or a higher scale `k' > k` (with both entries present) has a strictly smaller root. -/
theorem keyLe_keyAt_of_lex {R M : Mountain} {D cr sh : Nat} {θ σ : Row} {pe pa : Ref}
    {ce ca : Cell} (hce : cell? R pe = some ce) (hca : cell? M pa = some ca)
    (h : ∀ k, Row.jump σ ca.row ≤ k → k ≤ D →
      (Row.jump θ ce.row ≤ k ∧
        (root R k pe).column ≤ mapColumn cr sh (root M k pa).column) ∨
      ∃ k', k < k' ∧ k' ≤ D ∧ Row.jump θ ce.row ≤ k' ∧ Row.jump σ ca.row ≤ k' ∧
        (root R k' pe).column < mapColumn cr sh (root M k' pa).column) :
    keyLe (D + 1) (keyAt R D θ pe) (mapKey cr sh (keyAt M D σ pa)) = true := by
  unfold root at h
  apply keyLe_of_lexEntries
  intro j hj
  rw [getElem?_mapKey, getElem?_keyAt hce j hj, getElem?_keyAt hca j hj]
  simp only [Option.map_some]
  by_cases ha : Row.jump σ ca.row ≤ D - j
  · rw [if_pos ha]
    rcases h (D - j) ha (by omega) with ⟨he, hle⟩ | ⟨k', hk', hk'D, he', ha', hlt⟩
    · rw [if_pos he]
      simp only [Option.map_some]
      rcases Nat.lt_or_eq_of_le hle with hlt | heq
      · right; left
        exact ⟨_, _, rfl, rfl, by simp only [entryLt, mapColumn] at hlt ⊢; exact decide_eq_true hlt⟩
      · left
        rw [heq]
    · right; right
      refine ⟨D - k', by omega, ?_⟩
      rw [getElem?_mapKey, getElem?_keyAt hce _ (by omega), getElem?_keyAt hca _ (by omega)]
      have hDk : D - (D - k') = k' := by omega
      rw [hDk, if_pos he', if_pos ha']
      simp only [Option.map_some]
      exact ⟨_, _, rfl, rfl, by simp only [entryLt, mapColumn] at hlt ⊢; exact decide_eq_true hlt⟩
  · rw [if_neg ha]
    simp only [Option.map_none]
    by_cases he : Row.jump θ ce.row ≤ D - j
    · rw [if_pos he]
      right; left
      exact ⟨_, _, rfl, rfl, rfl⟩
    · rw [if_neg he]
      left
      rfl

/-- **One strict scale.** The keys agree (entrywise at most) above the scale `k₀`, and at
`k₀` (where both keys have entries) the output root is strictly left of the image; the
lower scales are arbitrary. -/
theorem keyLe_keyAt_of_strict {R M : Mountain} {D cr sh : Nat} {θ σ : Row} {pe pa : Ref}
    {ce ca : Cell} (hce : cell? R pe = some ce) (hca : cell? M pa = some ca) {k₀ : Nat}
    (hk₀ : k₀ ≤ D) (he : Row.jump θ ce.row ≤ k₀) (ha : Row.jump σ ca.row ≤ k₀)
    (habove : ∀ k, k₀ < k → k ≤ D →
      (root R k pe).column ≤ mapColumn cr sh (root M k pa).column)
    (hstrict : (root R k₀ pe).column < mapColumn cr sh (root M k₀ pa).column) :
    keyLe (D + 1) (keyAt R D θ pe) (mapKey cr sh (keyAt M D σ pa)) = true := by
  apply keyLe_keyAt_of_lex hce hca
  intro k _ hkD
  rcases Nat.lt_trichotomy k k₀ with hlt | rfl | hgt
  · exact Or.inr ⟨k₀, hlt, hk₀, he, ha, hstrict⟩
  · exact Or.inl ⟨he, le_of_lt hstrict⟩
  · exact Or.inl ⟨by omega, habove k hgt hkD⟩

/-! ## Lexicographic simulation -/

theorem reach_mono {M : Mountain} {k k' : Nat} {p q : Ref} (h : ScaleReach M k p q)
    (hk : k ≤ k') : ScaleReach M k' p q := by
  induction h with
  | refl p => exact ScaleReach.refl p
  | step hpar hc hcp hj hlt _ ih => exact ScaleReach.step hpar hc hcp (le_trans hj hk) hlt ih

/-- A higher scale `k' ∈ (k, D]` where the root of `v` is strictly left of the image of the
root of `m`. -/
def Wit (R M : Mountain) (D k cr sh : Nat) (v m : Ref) : Prop :=
  ∃ k', k < k' ∧ k' ≤ D ∧ (root R k' v).column < mapColumn cr sh (root M k' m).column

/-- A witness moves back along the two scale-`k` chains. -/
theorem wit_of_reach {R M : Mountain} {D k cr sh : Nat} {v v' m m' : Ref}
    (hv : ScaleReach R k v v') (hm : ScaleReach M k m m') (h : Wit R M D k cr sh v' m') :
    Wit R M D k cr sh v m := by
  obtain ⟨k', hk, hkD, hlt⟩ := h
  refine ⟨k', hk, hkD, ?_⟩
  rw [root_of_reach (reach_mono hv hk.le), root_of_reach (reach_mono hm hk.le)]
  exact hlt

theorem next_mono {R M : Mountain} {k cr sh : Nat} {Cp Cq : Ref → Ref → Prop}
    (hpq : ∀ v m, Cp v m → Cq v m) {v m' : Ref} (h : Next R M k cr sh Cp v m') :
    Next R M k cr sh Cq v m' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun hc => ?_⟩
  obtain ⟨v', hr, hcp⟩ := h3 hc
  exact ⟨v', hr, hpq _ _ hcp⟩

/-- **The lexicographic simulation theorem.** As `bound_of_sim`, but a step of the chain of
`M` may instead be answered by a witness at a higher scale. -/
theorem lex_of_sim {R M : Mountain} {D k cr sh B : Nat} (hA : AgreeBelow M R B) (hcrB : cr ≤ B)
    (Cp : Ref → Ref → Prop)
    (hcol : ∀ v m, Cp v m → v.column ≤ mapColumn cr sh m.column)
    (hstep : ∀ v m m', Cp v m → MStep M k m m' →
      Next R M k cr sh Cp v m' ∨ Wit R M D k cr sh v m) :
    ∀ v m, Cp v m → (root R k v).column ≤ mapColumn cr sh (root M k m).column ∨
      Wit R M D k cr sh v m := by
  intro v m hvm
  induction hmc : m.column using Nat.strong_induction_on generalizing v m with
  | _ c ih =>
    by_cases hs : ∃ m', MStep M k m m'
    · obtain ⟨m', hst⟩ := hs
      rcases hstep v m m' hvm hst with ⟨hlow, hroot, hcopy⟩ | hw
      · have hlt : m'.column < c := hmc ▸ hst.column_lt
        rcases Nat.lt_trichotomy m'.column cr with h | h | h
        · left
          rw [root_of_step hst, root_of_reach (hlow h), root_congr hA k (by omega)]
          exact le_mapColumn _ _ _
        · left
          obtain ⟨v', hreach, hv', hnext⟩ := hroot h
          rw [root_of_step hst, root_of_reach hreach]
          exact bound_root hA hcrB h hv' hnext
        · obtain ⟨v', hreach, hcp⟩ := hcopy h
          rcases ih m'.column hlt v' m' hcp rfl with hb | hw
          · left
            rw [root_of_step hst, root_of_reach hreach]
            exact hb
          · right
            exact wit_of_reach hreach hst.reach hw
      · exact Or.inr hw
    · push Not at hs
      left
      rw [root_of_noStep hs]
      exact le_trans (root_column_le R k v) (hcol v m hvm)

/-! ## Gap copies in the expansion -/

/-- `v` is the node of an inner column `y + w·i` of block `i` whose origin is the gap copy
(`b = 1`) of `m`. -/
def CutNode (M R : Mountain) (n cr x0 : Nat) (τ : Row) (i : Nat) (v m : Ref) : Prop :=
  ∃ y es j, cr < y ∧ y < x0 ∧ y ∈ blockColumns cr x0 n i ∧ v.column = y + (x0 - cr) * i ∧
    v.index = j + 1 ∧ emitsT (ctxAt M R y i cr (x0 - cr) x0 v.column) τ = .ok es ∧
    ∃ hj : j < es.length, es[j].2.src = m ∧ cutOrigin es[j].2 = true

/-- A copy (`CopyNode`) or a gap copy (`CutNode`). -/
def CutRel (M R : Mountain) (n cr x0 : Nat) (τ : Row) (i : Nat) (v m : Ref) : Prop :=
  CopyNode M R n cr x0 τ i v m ∨ CutNode M R n cr x0 τ i v m

theorem cutNode_column {M R : Mountain} {n cr x0 : Nat} {τ : Row} {i : Nat} {v m : Ref}
    (h : CutNode M R n cr x0 τ i v m) :
    v.column = mapColumn cr ((x0 - cr) * i) m.column := by
  obtain ⟨y, es, j, hcy, hyx, _, hv, _, hes, hj, hsrc, _⟩ := h
  obtain ⟨hcol, _⟩ := emitsT_good hes es[j] (List.getElem_mem hj)
  have hm : m.column = y := by
    rw [← hsrc, hcol]
    have hne : ¬ y = x0 := by omega
    split
    · simp [upperColumn, ctxAt, hne]
    · simp [ctxAt]
  rw [hm, mapColumn_of_ge (by omega), hv]

theorem cutRel_column {M R : Mountain} {n cr x0 : Nat} {τ : Row} {i : Nat} {v m : Ref}
    (h : CutRel M R n cr x0 τ i v m) :
    v.column ≤ mapColumn cr ((x0 - cr) * i) m.column := by
  rcases h with h | h
  · exact le_of_eq (copyNode_column h)
  · exact le_of_eq (cutNode_column h)

/-- (open) One step of the chain of `M(s)` from the origin of a gap copy is matched by the
chain of the output from the copy, or a higher scale has a strictly smaller root. -/
def StepCut : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), SpliceCase s n D M out ρ → DegreeOK s D →
    Official.expandDiagram s n = .ok R → Canonical.build out = .ok R →
    M[M.size - 1]? = some col → col.back? = some t →
    ∀ i, 0 < i → i < n + 1 → ∀ v m, CutNode M R n ρ.cr ρ.x0 (official t.row) i v m →
      ∀ k m', k ≤ D → MStep M k m m' →
        Next R M k ρ.cr ((ρ.x0 - ρ.cr) * i) (CutRel M R n ρ.cr ρ.x0 (official t.row) i) v m' ∨
        Wit R M D k ρ.cr ((ρ.x0 - ρ.cr) * i) v m

/-- (open) The leg of a gap copy's origin is at or right of `cr`. -/
def CutLeg : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = true →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      ρ.cr ≤ l.column

/-- (open) The jump of the output key template is at most the origin's, or a scale at or
above both jumps has a strictly smaller root. -/
def CutJump : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = true →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      Row.jump cu.row cpe.row ≤ Row.jump cv.row cpa.row ∨
      ∃ k', Row.jump cu.row cpe.row ≤ k' ∧ Row.jump cv.row cpa.row ≤ k' ∧ k' ≤ D ∧
        (root R k' pe).column < mapColumn ρ.cr ((ρ.x0 - ρ.cr) * i) (root M k' pa).column

/-- (open) For a leg right of `cr`, the parent of the output key template is the gap copy
of the parent of the origin's key template. -/
def CutStartCopy : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = true →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      ρ.cr < l.column → CutNode M R n ρ.cr ρ.x0 (official t.row) i pe pa

/-- (open) For the leg `cr`, the chain of the output parent reaches the next node of the
chain of the origin's parent, at every scale where the origin's key has an entry. -/
def CutStartRoot : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = true →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      l.column = ρ.cr → ∀ k m'', Row.jump cv.row cpa.row ≤ k → k ≤ D → MStep M k pa m'' →
        ScaleReach R k pe m''

/-! ## The reduction -/

/-- **A gap-copy region lemma from the lexicographic chain correspondence.** -/
theorem keyLeRegion_of_cut (sel : Nat → Nat → Origin → Prop)
    (hsel : ∀ x x0 o, sel x x0 o → cutOrigin o = true)
    (hStep : StepInner) (hCut : StepCut) (hLeg : CutLeg) (hJump : CutJump)
    (hCopy : CutStartCopy) (hRoot : CutStartRoot) : KeyLeRegion sel := by
  intro s n D M out ρ R col t hc hdeg hRun hRb hcol ht X x i hX0 hXR hXeq hi hx hipos hcopy es
    hes j hj e a he ha hnot hs _
  have hS : Site s n D M out ρ R t X x i es :=
    ⟨hc, hdeg, hRun, hRb, ⟨col, hcol, ht⟩, hX0, hXR, hXeq, hi, hx, hipos,
      ⟨R[X], Array.getElem?_eq_getElem hXR, hcopy⟩, hes⟩
  have hnc := hsel _ _ _ hs
  obtain ⟨_, _, _, _, _, hcrx, hinv⟩ := spliceCase_data hc hRun
  have hA : AgreeBelow M R ρ.x0 := hinv.1
  -- unfold the two leg atoms
  unfold legAtom? at he ha
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at he ha
  obtain ⟨cu, hcu, ref, href, pe, hpe, rfl⟩ := he
  obtain ⟨cv, hcv, l, hl, pa, hpa, rfl⟩ := ha
  obtain ⟨hpec, cpe, hcpe⟩ := highestAtMost_cell hpe
  obtain ⟨hpac, cpa, hcpa⟩ := highestAtMost_cell hpa
  have hL : Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa :=
    ⟨hcu, href, hcv, hl, hpe, hpa, hcpe, hcpa⟩
  have hcrl := hLeg s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL
  have himg := leg_image hS hj hL
  apply keyLe_keyAt_of_lex hcpe hcpa
  intro k hk hkD
  by_cases hde : Row.jump cu.row cpe.row ≤ k
  · rcases Nat.lt_or_eq_of_le hcrl with hlt | heq
    · -- a leg right of the root column: the lexicographic simulation
      have hcp := hCopy s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hlt
      have hsim := lex_of_sim (D := D) hA (le_of_lt hcrx)
        (CutRel M R n ρ.cr ρ.x0 (official t.row) i) (fun v m h => cutRel_column h)
        (by
          rintro v m m' (hvm | hvm) hst
          · exact Or.inl (next_mono (fun _ _ h => Or.inl h)
              (hStep s n D M out ρ R col t hc hdeg hRun hRb hcol ht i hipos hi v m hvm k m' hst))
          · exact hCut s n D M out ρ R col t hc hdeg hRun hRb hcol ht i hipos hi v m hvm k m' hkD
              hst)
        pe pa (Or.inr hcp)
      rcases hsim with hb | ⟨k', hk', hk'D, hlt'⟩
      · exact Or.inl ⟨hde, hb⟩
      · exact Or.inr ⟨k', hk', hk'D, by omega, by omega, hlt'⟩
    · -- the leg is the root column
      have hpe' : pe.column ≤ ρ.cr + (ρ.x0 - ρ.cr) * i := by
        rw [hpec, himg, ← heq, mapColumn_of_ge (le_refl _)]
      exact Or.inl ⟨hde, bound_root hA (le_of_lt hcrx) (by rw [hpac]; exact heq.symm) hpe'
        (fun m'' hst => hRoot s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL
          heq.symm k m'' hk hkD hst)⟩
  · rcases hJump s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL with
      hle | ⟨k', h1, h2, h3, h4⟩
    · omega
    · exact Or.inr ⟨k', by omega, h3, h1, h2, h4⟩

theorem regionCutBoundary_of_chains (hStep : StepInner) (hCut : StepCut) (hLeg : CutLeg)
    (hJump : CutJump) (hCopy : CutStartCopy) (hRoot : CutStartRoot) : RegionCutBoundary :=
  keyLeRegion_of_cut _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl)
    hStep hCut hLeg hJump hCopy hRoot

theorem regionCutInner_of_chains (hStep : StepInner) (hCut : StepCut) (hLeg : CutLeg)
    (hJump : CutJump) (hCopy : CutStartCopy) (hRoot : CutStartRoot) : RegionCutInner :=
  keyLeRegion_of_cut _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl)
    hStep hCut hLeg hJump hCopy hRoot

/-- **Well-foundedness of the official expansion** from the reconstruction and the chain
correspondence (the five statements of `ChainCorrRegions.lean` and the five gap-copy
statements of this file). -/
theorem wellFounded_of_all_chains (hrec : Dimension.BlockReconstruction) (hStep : StepInner)
    (hLeg : StartLeg) (hJump : StartJump) (hCopy : StartCopy) (hRoot : StartRoot)
    (hCut : StepCut) (hCLeg : CutLeg) (hCJump : CutJump) (hCCopy : CutStartCopy)
    (hCRoot : CutStartRoot) : WellFounded Step :=
  wellFounded_of_chains hrec hStep hLeg hJump hCopy hRoot
    (regionCutBoundary_of_chains hStep hCut hCLeg hCJump hCCopy hCRoot)
    (regionCutInner_of_chains hStep hCut hCLeg hCJump hCCopy hCRoot)

end OmegaY.Official.Classification.Proofs.ChainCorr

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.keyLe_keyAt_of_lex
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.keyLeRegion_of_cut
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.wellFounded_of_all_chains
