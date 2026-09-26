/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CutPartsStep.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutPartsStart

set_option backward.do.legacy false

/-!
# `StepCut` from the start statements and a lookup at the top of a run

`StepCut` (`ChainCorrCut.lean`) asks: for a gap copy `v` (block `i ≥ 1`, inner column
`y + w·i`, `cr < y < x₀`) of a node `m = (y, C)` of `M(s)` and a step `m → m'` of the scale-`k`
chain of `M(s)` (`k ≤ D`), the scale-`k` chain of the output from `v` matches the step
(`Next`, with copies and gap copies), or a higher scale has a strictly smaller root (`Wit`).

## The argument (`stepCut_of_parts`)

By strong induction on the column of `m`. The node `v = (X, j + 1)` is the emit `j` of its
column, with origin `.clean m true`.

* **Inside a run** (the emit `j + 1` is again a gap copy of `m`). Both emits have the leg column
  `φ(l)` of `m`, so the raw parent of `v` is the highest node of `φ(l)` at or below the row of
  `v` (the output is canonical, `canon_rawParent_hAM`): it is the node `pe` of the start
  statements at `v`, with `pa` the highest node of `l` at or below `C`. Let
  `d_e = jump(row v, row pe)`; `d_a = 0` (`CutPaRow`).
  * `d_e ≤ k`: the chain of `v` steps to `pe`. For `l > cr`, `pe` is the gap copy of `pa`
    (`CutStartCopy`), and the chain of `M(s)` from `pa` reaches `m'` (`CutGenReach`): the walk
    lemma `walk` follows it, using `StepInner` at copies and the induction hypothesis at gap
    copies (`pa` is left of `m`). For `l = cr`, `pe` is in the boundary column and its chain
    follows the chain of `pa` (`CutStartRoot`).
  * `d_e > k`: `CutJump` gives a scale `k' ≥ d_e` where the root of `pe` is strictly left of the
    image of the root of `pa`; the roots of `v` and `m` at `k'` are those of `pe` and `pa`.
* **At the top of a run**: `CutTopLookup` states the raw parent of `v` directly (the same kind
  of lookup as `LegLookup` of `StepInner`), with a jump at most the jump of `m → m'`.

## The open statements used

`StepInner` (`ChainCorrRegions.lean`), the three start statements `CutStartCopy`,
`CutStartRoot`, `CutJump` (reduced in `CutPartsStart.lean`), `CutPaRow` (`CutPartsStart.lean`)
and the two statements of this file:

* `CutGenReach`: for a gap copy of an inner column, the scale-`k` chain of `M(s)` from `pa`
  reaches the next node `m'` of the scale-`k` chain from the origin. (Numerically the chain from
  `pa` usually stays in the row `C` until `m'`; on 40 node-scale pairs of the random sample it
  first leaves `C` from the root column, e.g. `(1,9,5,6,3,8,10,8)[1]`, so the statement is at
  scale `k`, not `0`.)
* `CutTopLookup`: at the top of a run of gap copies of `m` in an inner column, the raw parent
  `pe'` of `v` exists, `jump(row v, row pe') ≤ jump(row m, row m')`, and `pe' = m'` (left of
  `cr`), `pe'` is in the boundary column and its chain follows the chain of `m'` at the scales of
  the step `m → m'` (in `cr`), or `pe'` is a copy or gap copy of `m'` (right of `cr`).

## Numerical tests (`reference/official/cut-parts.cjs`)

Counts: node-scale pairs for `CutGenReach`, gap copies otherwise. No failure. `InRunParent` is
the fact proved here that inside a run the raw parent of `v` is `pe`. (`CutPaRow` and
`CutGenReach` are proved in `CutPartsPaRow.lean` and `CutPartsGen.lean`; `CutTopLookup` is
reduced in `CutPartsTop.lean`.)

| sample | `CutGenReach` | `CutTopLookup` (`m'` `<`/`=`/`>` `cr`) | `InRunParent` |
|---|---:|---:|---:|
| standard S1–S3, S6, `n = 1,2,3` | 2333964 | 0 / 36504 / 40812 | 652059 |
| legal, length ≤ 6, entries ≤ 6 | 695530 | 0 / 19476 / 6306 | 136714 |
| legal, length ≤ 5, entries ≤ 8 | 2179300 | 0 / 14946 / 4740 | 347215 |
| random legal (`--random 20000,10,10,7`) | 25234848 | 24 / 51624 / 28512 | 3256395 |
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.CutParts

open Canonical Reserve Official Descent Classification Proofs

/-! ## The statements -/

/-- For a gap copy of an inner column, the scale-`k` chain of `M(s)` from `pa` reaches the next
node of the scale-`k` chain from the origin (proved: `cutGenReach`, `CutPartsGen.lean`). -/
def CutGenReach : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es → x < ρ.x0 →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = true →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
    ∀ k m', k ≤ D → MStep M k es[j].2.src m' → ScaleReach M k pa m'

/-- (open) At the top of a run of gap copies in an inner column, the raw parent of the node
matches the raw parent of the origin, with no larger jump. -/
def CutTopLookup : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es → x < ρ.x0 →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = true →
    (∀ hj' : j + 1 < es.length, es[j + 1].2 ≠ es[j].2) →
    ∀ m', rawParent M es[j].2.src = some m' →
    ∃ pe, rawParent R ⟨X, j + 1⟩ = some pe ∧
      (∀ cu cm cpe cm' : Cell, cell? R ⟨X, j + 1⟩ = some cu → cell? M es[j].2.src = some cm →
        cell? R pe = some cpe → cell? M m' = some cm' →
        Row.jump cu.row cpe.row ≤ Row.jump cm.row cm'.row) ∧
      (m'.column < ρ.cr → pe = m') ∧
      (m'.column = ρ.cr → pe.column = ρ.cr + (ρ.x0 - ρ.cr) * i ∧
        ∀ k m'', k ≤ D → MStep M k es[j].2.src m' → MStep M k m' m'' → ScaleReach R k pe m'') ∧
      (ρ.cr < m'.column → CutRel M R n ρ.cr ρ.x0 (official t.row) i pe m')

/-! ## Chains -/

/-- A chain left of a column where two mountains agree is a chain of both. -/
theorem reach_agree {M R : Mountain} {B k : Nat} (hA : AgreeBelow M R B) {p q : Ref}
    (h : ScaleReach M k p q) (hp : p.column < B) : ScaleReach R k p q := by
  induction h with
  | refl p => exact ScaleReach.refl p
  | @step p p' q c cp hpar hc hcp hj hlt _ ih =>
      have hpar' : rawParent R p = some p' := by rw [← rawParent_congr hA hp]; exact hpar
      have hc' : cell? R p = some c := by rw [← cell?_congr hA hp]; exact hc
      have hcp' : cell? R p' = some cp := by rw [← cell?_congr hA (by omega)]; exact hcp
      exact ScaleReach.step hpar' hc' hcp' hj hlt (ih (by omega))

theorem next_of_reach {R M : Mountain} {k cr sh : Nat} {Cp : Ref → Ref → Prop} {v v' m' : Ref}
    (hr : ScaleReach R k v v') (h : Next R M k cr sh Cp v' m') : Next R M k cr sh Cp v m' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun h => ScaleReach.trans hr (h1 h), fun h => ?_, fun h => ?_⟩
  · obtain ⟨v'', hr', hc, hn⟩ := h2 h
    exact ⟨v'', ScaleReach.trans hr hr', hc, hn⟩
  · obtain ⟨v'', hr', hc⟩ := h3 h
    exact ⟨v'', ScaleReach.trans hr hr', hc⟩

/-- A witness moves along chains that meet at a node of `M`. -/
theorem wit_of_meet {R M : Mountain} {D k cr sh : Nat} {v v' m a m' : Ref}
    (hv : ScaleReach R k v v') (hm : ScaleReach M k m m') (ha : ScaleReach M k a m')
    (h : Wit R M D k cr sh v' a) : Wit R M D k cr sh v m := by
  obtain ⟨k', hk, hkD, hlt⟩ := h
  refine ⟨k', hk, hkD, ?_⟩
  rw [root_of_reach (reach_mono hv hk.le), root_of_reach (reach_mono hm hk.le),
    ← root_of_reach (reach_mono ha hk.le)]
  exact hlt

/-- **The walk.** If every step of the chain of `M` from a `Cp`-related node (right of `cr`) is
matched or answered by a witness, the whole chain up to a node `m'` is. -/
theorem walk {R M : Mountain} {D k cr sh B c1 : Nat} (hA : AgreeBelow M R B) (hcrB : cr ≤ B)
    (Cp : Ref → Ref → Prop) (hcp : ∀ v a, Cp v a → cr < a.column)
    (hstep : ∀ v a a', Cp v a → a.column ≤ c1 → MStep M k a a' →
      Next R M k cr sh Cp v a' ∨ Wit R M D k cr sh v a) {m' : Ref} :
    ∀ a, ScaleReach M k a m' → ∀ v, Cp v a → a.column ≤ c1 →
      Next R M k cr sh Cp v m' ∨ Wit R M D k cr sh v a := by
  intro a hr
  induction hr with
  | refl a =>
      intro v hva _
      have hc := hcp v a hva
      left
      exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega),
        fun _ => ⟨v, ScaleReach.refl v, hva⟩⟩
  | @step a a' q c cp hpar hc hcp' hj hlt hrest ih =>
      intro v hva hac
      have hst : MStep M k a a' := ⟨hpar, c, cp, hc, hcp', hj, hlt⟩
      rcases hstep v a a' hva hac hst with ⟨hlow, hroot, hcopy⟩ | hw
      · have hq := hrest.column_le
        rcases Nat.lt_trichotomy a'.column cr with h | h | h
        · left
          have hr1 := hlow h
          have hr2 := reach_agree hA hrest (by omega)
          exact ⟨fun _ => ScaleReach.trans hr1 hr2, fun h' => absurd h' (by omega),
            fun h' => absurd h' (by omega)⟩
        · obtain ⟨v', hr1, hv', hnext⟩ := hroot h
          cases hrest with
          | refl =>
              left
              exact ⟨fun h' => absurd h' (by omega), fun _ => ⟨v', hr1, hv', hnext⟩,
                fun h' => absurd h' (by omega)⟩
          | @step _ a'' _ c' cp'' hpar' hc' hcp'' hj' hlt' hrest' =>
              left
              have hst' : MStep M k a' a'' := ⟨hpar', c', cp'', hc', hcp'', hj', hlt'⟩
              have hr2 := hnext a'' hst'
              have hr3 := reach_agree hA hrest' (by omega)
              have hq' := hrest'.column_le
              exact ⟨fun _ => ScaleReach.trans hr1 (ScaleReach.trans hr2 hr3),
                fun h' => absurd h' (by omega), fun h' => absurd h' (by omega)⟩
        · obtain ⟨v', hr1, hcpv⟩ := hcopy h
          rcases ih v' hcpv (by omega) with hn | hw
          · exact Or.inl (next_of_reach hr1 hn)
          · exact Or.inr (wit_of_reach hr1 hst.reach hw)
      · exact Or.inr hw

/-! ## The site of a gap copy -/

theorem site_of_emits {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {col : Column} {t : Cell} (hS : Inner.Setting s n D M out ρ R col t) {i : Nat}
    (hi0 : 0 < i) (hi : i < n + 1) {X y : Nat} {es : List (Emit × Origin)} (hcy : ρ.cr < y)
    (hyx : y < ρ.x0) (hyb : y ∈ blockColumns ρ.cr ρ.x0 n i) (hvc : X = y + (ρ.x0 - ρ.cr) * i)
    (hes : emitsT (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) (official t.row) = .ok es) :
    Site s n D M out ρ R t X y i es := by
  obtain ⟨col', t', hcol', ht', _, hcrx, hinv⟩ := spliceCase_data hS.splice hS.run
  have hcc : col' = col := Option.some.inj (hcol'.symm.trans hS.hcol)
  subst hcc
  have htt : t' = t := Option.some.inj (ht'.symm.trans hS.ht)
  subst htt
  have hRs : R.size = ρ.x0 + n * (ρ.x0 - ρ.cr) := by
    rw [build_size hS.canon]
    exact Reconstruction.expand_length_splice hS.splice.build hS.splice.run hS.splice.root
      hS.splice.copies
  have hwi : (ρ.x0 - ρ.cr) * i ≤ n * (ρ.x0 - ρ.cr) := by
    rw [Nat.mul_comm n]; exact Nat.mul_le_mul_left _ (by omega)
  have hw1 : ρ.x0 - ρ.cr ≤ (ρ.x0 - ρ.cr) * i := Nat.le_mul_of_pos_right _ hi0
  have hXR : X < R.size := by omega
  have hX0 : ρ.x0 ≤ X := by omega
  obtain ⟨i', x', _, hx', hXeq, hcopy⟩ := hinv.2.2 X hXR hX0
  obtain ⟨hii, hxx⟩ := Inner.block_unique hcrx hcy hyx hx' (hvc.symm.trans hXeq) hi0
  subst hii
  subst hxx
  exact ⟨hS.splice, hS.deg, hS.run, hS.canon, ⟨col', hS.hcol, hS.ht⟩, hX0, hXR, hvc, hi, hyb,
    hi0, ⟨R[X], Array.getElem?_eq_getElem hXR, hcopy⟩, hes⟩

theorem hAM_of_left {M : Mountain} (hV : MountainValid M) {v : Ref} {cv : Cell} {l : Ref}
    (h : cell? M v = some cv) (hidx : 1 ≤ v.index) (hl : cv.left = some l) :
    ∃ p, highestAtMost M l.column cv.row = some p := by
  obtain ⟨a, ha, _⟩ := legAtom?_exists hV 0 h hidx hl
  unfold legAtom? at ha
  simp only [h, hl, Option.bind_eq_bind, Option.bind_some] at ha
  cases hp : highestAtMost M l.column cv.row with
  | none => rw [hp] at ha; simp at ha
  | some p => exact ⟨p, rfl⟩

theorem ref_mk {v : Ref} {X j : Nat} (hX : v.column = X) (hj : v.index = j + 1) :
    v = ⟨X, j + 1⟩ := by
  cases v
  simp_all

/-! ## The reduction -/

/-- `StepCut` at one scale, by strong induction on the column of the origin. -/
theorem stepCut_at (hStep : StepInner) (hCopy : CutStartCopy) (hRoot : CutStartRoot)
    (hJump : CutJump) (hRow : CutPaRow) (hGen : CutGenReach) (hTop : CutTopLookup)
    {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root} {R : Mountain}
    {col : Column} {t : Cell} (hS : Inner.Setting s n D M out ρ R col t) {i : Nat}
    (hi0 : 0 < i) (hi : i < n + 1) {k : Nat} (hkD : k ≤ D) :
    ∀ c v m, m.column = c → CutNode M R n ρ.cr ρ.x0 (official t.row) i v m →
      ∀ m', MStep M k m m' →
        Next R M k ρ.cr ((ρ.x0 - ρ.cr) * i) (CutRel M R n ρ.cr ρ.x0 (official t.row) i) v m' ∨
        Wit R M D k ρ.cr ((ρ.x0 - ρ.cr) * i) v m := by
  have hV := build_valid_of_success hS.splice.build
  have hVR := build_valid_of_success hS.canon
  obtain ⟨_, _, _, _, _, hcrx, hinv⟩ := spliceCase_data hS.splice hS.run
  have hA : AgreeBelow M R ρ.x0 := hinv.1
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro v m hmc hvm m' hst
  obtain ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, hsrc, hcut⟩ := hvm
  have hS' := site_of_emits hS hi0 hi hcy hyx hyb hvc hes
  have hv : v = ⟨v.column, j + 1⟩ := ref_mk rfl hvi
  have ho : es[j].2 = .clean m true := by
    revert hsrc hcut
    generalize es[j].2 = o
    intro hsrc hcut
    cases o with
    | clean r b =>
        cases b
        · simp [cutOrigin] at hcut
        · simp only [Origin.src] at hsrc
          rw [hsrc]
    | plain r => simp [cutOrigin] at hcut
    | upper r => simp [cutOrigin] at hcut
  have hvat : Inner.CopyAt M R n ρ.cr ρ.x0 (official t.row) i v (.clean m true) :=
    ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, ho⟩
  obtain ⟨cu, ref, cv, l, hcu, href, hcv, hl, hrefc⟩ := Inner.copyAt_left hS hi0 hi hvat
  simp only [Origin.src] at hcv
  have hpar := hst.1
  have hsrcm : es[j].2.src = m := by rw [ho]; rfl
  obtain ⟨_, hm1, _⟩ := emitsT_good hes es[j] (List.getElem_mem hj)
  rw [hsrcm] at hm1
  by_cases hrun : ∃ hj' : j + 1 < es.length, es[j + 1].2 = es[j].2
  · -- inside a run: the raw parent of `v` is `pe`
    obtain ⟨hj1, hrun⟩ := hrun
    have hupat : Inner.CopyAt M R n ρ.cr ρ.x0 (official t.row) i (Inner.up v) (.clean m true) :=
      ⟨y, es, j + 1, hcy, hyx, hyb, hvc, by simp [Inner.up, hvi], hes, hj1, by rw [hrun, ho]⟩
    obtain ⟨cu', ref', cv', l', hcu', href', hcv', hl', hrefc'⟩ :=
      Inner.copyAt_left hS hi0 hi hupat
    simp only [Origin.src] at hcv'
    have hcvv : cv' = cv := Option.some.inj (hcv'.symm.trans hcv)
    subst cv'
    have hll : l' = l := Option.some.inj (hl'.symm.trans hl)
    subst l'
    have hraw : rawParent R v = some ref' := Inner.rawParent_eq_some.mpr ⟨cu', hcu', href'⟩
    have hv0 : 0 < v.index := by omega
    have hham := Inner.canon_rawParent_hAM hS.canon hv0 hcu hraw
    have hcolr : ref'.column = ref.column := by rw [hrefc, hrefc']
    rw [hcolr] at hham
    obtain ⟨pa, hpa⟩ := hAM_of_left hV hcv hm1 hl
    obtain ⟨_, cpe, hcpe⟩ := highestAtMost_cell hham
    obtain ⟨hpac, cpa, hcpa⟩ := highestAtMost_cell hpa
    have hcu0 : cell? R ⟨v.column, j + 1⟩ = some cu := by rw [← hv]; exact hcu
    have hL : Legs M R v.column j es[j].2 cu cv ref l ref' pa cpe cpa :=
      ⟨hcu0, href, by rw [hsrcm]; exact hcv, hl, hham, hpa, hcpe, hcpa⟩
    have hrow := hRow s n D M out ρ R t v.column y i es hS' j hj (by rw [ho]; rfl) cu cv ref l
      ref' pa cpe cpa hL
    have hda : Row.jump cv.row cpa.row = 0 := by rw [hrow, Row.jump_self]
    have hgen := hGen s n D M out ρ R t v.column y i es hS' hyx j hj (by rw [ho]; rfl) cu cv ref l
      ref' pa cpe cpa hL k m' hkD (by rw [hsrcm]; exact hst)
    have hcrl := cutLeg s n D M out ρ R t v.column y i es hS' j hj (by rw [ho]; rfl) cu cv ref l
      ref' pa cpe cpa hL
    have himg := leg_image hS' hj hL
    by_cases hde : Row.jump cu.row cpe.row ≤ k
    · have hreach : ScaleReach R k v ref' := Inner.reach_one hVR hraw hcu hcpe hde
      rcases Nat.lt_or_eq_of_le hcrl with hlt | heq
      · -- a leg right of `cr`: the walk from the gap copy `pe` of `pa`
        have hcp := hCopy s n D M out ρ R t v.column y i es hS' j hj (by rw [ho]; rfl) cu cv ref l
          ref' pa cpe cpa hL hlt
        have hlm : l.column < m.column := by
          have := left_lt_of_valid hV hcv hl
          omega
        have hw := walk (D := D) hA (le_of_lt hcrx) (CutRel M R n ρ.cr ρ.x0 (official t.row) i)
          (c1 := pa.column)
          (fun v a h => by
            have := cutRel_column h
            rcases h with h | h
            · obtain ⟨y', _, _, hcy', _, _, hvc', _, hes', hj', hsrc', _⟩ := h
              obtain ⟨hsc, _⟩ := emitsT_good hes' _ (List.getElem_mem hj')
              rw [hsrc'] at hsc
              have hne : ¬ y' = ρ.x0 := by omega
              have : a.column = y' := by
                rw [hsc]
                split
                · simp [upperColumn, ctxAt, hne]
                · simp [ctxAt]
              omega
            · obtain ⟨y', _, _, hcy', _, _, hvc', _, hes', hj', hsrc', _⟩ := h
              obtain ⟨hsc, _⟩ := emitsT_good hes' _ (List.getElem_mem hj')
              rw [hsrc'] at hsc
              have hne : ¬ y' = ρ.x0 := by omega
              have : a.column = y' := by
                rw [hsc]
                split
                · simp [upperColumn, ctxAt, hne]
                · simp [ctxAt]
              omega)
          (by
            intro v' a a' hva hac hst'
            rcases hva with hva | hva
            · exact Or.inl (next_mono (fun _ _ h => Or.inl h)
                (hStep s n D M out ρ R col t hS.splice hS.deg hS.run hS.canon hS.hcol hS.ht i hi0 hi
                  v' a hva k a' hst'))
            · have hpa' : pa.column = l.column := hpac
              exact ih a.column (by omega) v' a rfl hva a' hst')
          pa hgen ref' (Or.inr hcp) (le_refl _)
        rcases hw with hn | hw
        · exact Or.inl (next_of_reach hreach hn)
        · exact Or.inr (wit_of_meet hreach hst.reach hgen hw)
      · -- the leg is the root column
        have hpacol : pa.column = ρ.cr := by rw [hpac, heq]
        have hpecol : ref'.column = ρ.cr + (ρ.x0 - ρ.cr) * i := by
          rw [hcolr, himg, ← heq, mapColumn_of_ge (le_refl _)]
        have hnext := fun kk m'' (h1 : Row.jump cv.row cpa.row ≤ kk) (h2 : kk ≤ D)
            (h3 : MStep M kk pa m'') =>
          hRoot s n D M out ρ R t v.column y i es hS' j hj (by rw [ho]; rfl) cu cv ref l ref' pa
            cpe cpa hL heq.symm kk m'' h1 h2 h3
        left
        cases hgen with
        | refl =>
            exact ⟨fun h => absurd h (by omega),
              fun _ => ⟨ref', hreach, le_of_eq hpecol,
                fun m'' h => hnext k m'' (by omega) hkD h⟩,
              fun h => absurd h (by omega)⟩
        | @step _ p' _ c' cp' hpar' hc' hcp' hj' hlt' hrest =>
            have hst' : MStep M k pa p' := ⟨hpar', c', cp', hc', hcp', hj', hlt'⟩
            have hr2 := hnext k p' (by omega) hkD hst'
            have hr3 := reach_agree hA hrest (by omega)
            have hq := hrest.column_le
            exact ⟨fun _ => ScaleReach.trans hreach (ScaleReach.trans hr2 hr3),
              fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
    · -- the chain of `v` stops: the witness of `CutJump`
      right
      rcases hJump s n D M out ρ R t v.column y i es hS' j hj (by rw [ho]; rfl) cu cv ref l ref'
        pa cpe cpa hL with hle | ⟨k', h1, _, h3, h4⟩
      · omega
      · refine ⟨k', by omega, h3, ?_⟩
        have hr' : ScaleReach R k' v ref' := Inner.reach_one hVR hraw hcu hcpe h1
        have hk' : k ≤ k' := by omega
        rw [root_of_reach hr', root_of_reach (reach_mono hst.reach hk'),
          ← root_of_reach (reach_mono hgen hk')]
        exact h4
  · -- at the top of a run
    have hnot : ∀ hj' : j + 1 < es.length, es[j + 1].2 ≠ es[j].2 := fun hj' h => hrun ⟨hj', h⟩
    obtain ⟨pe, hraw, hjmp, hlow, hroot, hcopy⟩ :=
      hTop s n D M out ρ R t v.column y i es hS' hyx j hj (by rw [ho]; rfl) hnot m'
        (by rw [hsrcm]; exact hpar)
    rw [← hv] at hraw
    obtain ⟨cm, cm', hcm, hcm', hjm, -⟩ := hst.2
    obtain ⟨_, ⟨cpe, hcpe⟩, _⟩ := Inner.rawParent_cells hVR hraw
    have hle := hjmp cu cm cpe cm' (by rw [← hv]; exact hcu) (by rw [hsrcm]; exact hcm) hcpe hcm'
    have hreach : ScaleReach R k v pe := Inner.reach_one hVR hraw hcu hcpe (by omega)
    left
    refine ⟨fun h => by rw [← hlow h]; exact hreach, fun h => ?_, fun h => ⟨pe, hreach, hcopy h⟩⟩
    obtain ⟨hpc, hn⟩ := hroot h
    exact ⟨pe, hreach, le_of_eq hpc, fun m'' h' => hn k m'' hkD (by rw [hsrcm]; exact hst) h'⟩

/-- **`StepCut` from the start statements, `StepInner`, `CutPaRow`, `CutGenReach` and
`CutTopLookup`.** -/
theorem stepCut_of_parts (hStep : StepInner) (hCopy : CutStartCopy) (hRoot : CutStartRoot)
    (hJump : CutJump) (hRow : CutPaRow) (hGen : CutGenReach) (hTop : CutTopLookup) :
    StepCut := by
  intro s n D M out ρ R col t hc hdeg hRun hRb hcol ht i hi0 hi v m hvm k m' hkD hst
  exact stepCut_at hStep hCopy hRoot hJump hRow hGen hTop ⟨hc, hdeg, hRun, hRb, hcol, ht⟩ hi0 hi
    hkD m.column v m rfl hvm m' hst

/-! ## The gap-copy regions and well-foundedness -/

/-- **The four gap-copy statements of `ChainCorrCut.lean`** from `StepInner`, the block profile
(`CopyOrder`, `CopyFirst`), `BoundaryChain` and the seven open statements of the `CutParts`
files. -/
theorem cut_statements (hStep : StepInner) (hA : CopyOrder) (hC2 : CopyFirst)
    (hBC : BoundaryChain) (hRow : CutPaRow) (hGen : CutGenReach) (hTop : CutTopLookup)
    (hLow : CutRunLow) (hHigh : CutRunHigh) (hOR : CutOriginReach) (hJT : CutJumpTop) :
    StepCut ∧ CutJump ∧ CutStartCopy ∧ CutStartRoot := by
  have hCopy := cutStartCopy_of_parts hA hC2 hLow hHigh
  have hRoot := cutStartRoot_of_parts hBC hOR
  have hJump := cutJump_of_top hJT
  exact ⟨stepCut_of_parts hStep hCopy hRoot hJump hRow hGen hTop, hJump, hCopy, hRoot⟩

/-- **Well-foundedness of the official expansion** from the reconstruction, the five statements
of `ChainCorrRegions.lean`, the block profile, `BoundaryChain` and the seven open gap-copy
statements. -/
theorem wellFounded_of_cut_parts (hrec : Dimension.BlockReconstruction) (hStep : StepInner)
    (hLeg : StartLeg) (hJ : StartJump) (hCopy : StartCopy) (hRoot : StartRoot)
    (hA : CopyOrder) (hC2 : CopyFirst) (hBC : BoundaryChain) (hRow : CutPaRow)
    (hGen : CutGenReach) (hTop : CutTopLookup) (hLow : CutRunLow) (hHigh : CutRunHigh)
    (hOR : CutOriginReach) (hJT : CutJumpTop) : WellFounded Step := by
  obtain ⟨h1, h2, h3, h4⟩ := cut_statements hStep hA hC2 hBC hRow hGen hTop hLow hHigh hOR hJT
  exact wellFounded_of_chains_cut hrec hStep hLeg hJ hCopy hRoot h1 h2 h3 h4

end OmegaY.Official.Classification.Proofs.ChainCorr.CutParts

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.CutParts.walk
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.CutParts.stepCut_of_parts
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.CutParts.cut_statements
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.CutParts.wellFounded_of_cut_parts
