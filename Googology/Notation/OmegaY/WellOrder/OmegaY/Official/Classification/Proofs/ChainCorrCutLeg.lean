/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/ChainCorrCutLeg.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrCut
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RowLawSource

set_option backward.do.legacy false

/-!
# The leg of a copy of the root row

A copy of the root row (origin `.clean r b`, `b = 0` or `b = 1`) in block `i ≥ 1` has as
origin the node `(x, C)` of the source column `x > cr`, where `C` is the row of the top `ρ`
of the root column in a region `S` in which `x` ascends (`A(S, x)`, notes/03 §2.4). This
file proves that the leg of `(x, C)` is at or right of the root column `cr`
(`cleanLeg`), hence the open statement `CutLeg` of `ChainCorrCut.lean` (`cutLeg`). The same
theorem covers the clean copies (`b = 0`), i.e. the case of `StartLeg`
(`ChainCorrRegions.lean`) whose origin is a copy of the root row.

## The argument

* Every item with a copied root row `C` carries the ascension test that introduced it: the
  node `a = (x, Z)` at the reference row `Z` exists and the in-row parents from `a` reach the
  column `cr` exactly (`reachesRoot`). Case 2 and case 3 set `C = row ρ` after the test;
  case 4 keeps `C` (`childItems_asc`, `emitsT_cleanAsc`).
* Since `x > cr`, the in-row parent `q = P(a)` exists and `q.column ≥ cr`
  (`reachesRoot_column`, `weakParent_of_reachesRoot`).
* If the finite coefficient of `C` is positive, `Z = C - 1` and the node above `a` has the
  row `bump Z 0 = C` (the row law of the canonical mountain), so it is `(x, C)` and its leg
  is `q` (`leg_of_ascension`).
* Otherwise `Z = C`, `a = (x, C)` and `q` is the raw parent of `(x, C)` (the left end of the
  edge above it). In a canonical mountain the raw parent of a real node `u` lies at or left
  of the leg of `u`: the parent search for the node above `u` starts in the leg column of `u`
  and only moves left (`rawParent_column_le_left`, from `Frame.P_iff` and `Hit.column_le`).
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr

open Canonical Reserve Official Descent Classification Proofs

/-! ## Raw parents lie at or left of the leg -/

/-- **In a canonical mountain, the raw parent of a real node is at or left of its leg.** -/
theorem rawParent_column_le_left {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M)
    {u q l : Ref} {cu : Cell} (hcu : cell? M u = some cu) (hu : 0 < u.index)
    (hl : cu.left = some l) (hraw : Reserve.rawParent M u = some q) : q.column ≤ l.column := by
  have hF := build_normal_of_success hb
  have hO := hF.toOrdered
  obtain ⟨nu, hnu, hcell⟩ := ControlProof.node_of_cell? hcu
  have h1 := ControlProof.rawParent_ref (M := M) nu
  rw [hnu, hraw] at h1
  cases hup : (Geometry.Frame.ofMountain M).upper nu with
  | none => rw [hup] at h1; cases h1
  | some v =>
    rw [hup, Option.bind_some] at h1
    obtain ⟨np, hlk, _, _⟩ := hO.stored_valid v q h1.symm
    have hnp : Geometry.Frame.ref np = q := Geometry.Frame.lookup_spec hlk
    have hleft' : ((Geometry.Frame.ofMountain M).cell v).left = some (Geometry.Frame.ref np) := by
      rw [hnp]
      exact h1.symm
    have hrawF := Geometry.Frame.rawParent_eq_of_upper_left hup hleft'
    have hReal : Geometry.Frame.Real nu := by
      show 0 < nu.2.val
      have : u.index = nu.2.val := by rw [← hnu]; rfl
      omega
    have hP : (Geometry.Frame.ofMountain M).P nu = some np :=
      (hF.rawParent_eq_P hReal).symm.trans hrawF
    obtain ⟨qq, hQ, hit⟩ := (Geometry.Frame.P_iff hO).mp hP
    obtain ⟨left, hls, _, _, hqc, _⟩ := Geometry.Frame.Q_spec hO hQ
    rw [hcell, hl] at hls
    have hlq : l = Geometry.Frame.ref left := Option.some.inj hls
    have hcl := hit.column_le hO
    rw [← hnp, hlq]
    show np.1.val ≤ left.1.val
    rw [← hqc]
    exact hcl

/-! ## The ascension test -/

theorem reachesRoot_column {M : Mountain} {cr : Nat} :
    ∀ {f : Nat} {q : Ref}, reachesRoot M cr f q = .ok true → cr ≤ q.column
  | 0, q, h => by simp [reachesRoot, throw, throwThe, MonadExceptOf.throw] at h
  | f + 1, q, h => by
      by_cases hq : q.column ≤ cr
      · simp only [reachesRoot, if_pos hq, pure, Except.pure, Except.ok.injEq,
          decide_eq_true_eq] at h
        omega
      · omega

/-- The in-row parent of a node right of `cr` from which the in-row parents reach `cr`. -/
theorem weakParent_of_reachesRoot {M : Mountain} {cr f : Nat} {a : Ref} (ha : cr < a.column)
    (h : reachesRoot M cr f a = .ok true) :
    ∃ q, Expansion.weakParent M a = .ok (some q) ∧ cr ≤ q.column := by
  cases f with
  | zero => simp [reachesRoot, throw, throwThe, MonadExceptOf.throw] at h
  | succ f =>
    unfold reachesRoot at h
    rw [if_neg (by omega)] at h
    simp only [bind, Except.bind] at h
    cases hw : liftE (Expansion.weakParent M a) with
    | error e => rw [hw] at h; cases h
    | ok wp =>
      rw [hw] at h
      cases wp with
      | none => simp only [pure, Except.pure] at h; cases h
      | some q =>
        simp only at h
        exact ⟨q, Reconstruction.liftE_ok hw, reachesRoot_column h⟩

/-- Two real nodes of one column with the same official row are equal. -/
theorem realNodes_eq_of_official {M : Mountain} (hV : MountainValid M) {c : Nat}
    {p q : Ref × Cell} (hp : p ∈ realNodes M c) (hq : q ∈ realNodes M c)
    (h : official p.2.row = official q.2.row) : p = q := by
  have strict : ∀ {p q : Ref × Cell}, p ∈ realNodes M c → q ∈ realNodes M c →
      p.1.index < q.1.index → official p.2.row < official q.2.row := by
    intro p q hp hq hlt
    obtain ⟨col, k, hc, hcell, hp1⟩ := Recon.mem_realNodes_iff.mp hp
    obtain ⟨col', k', hc', hcell', hq1⟩ := Recon.mem_realNodes_iff.mp hq
    have hcc : col' = col := Option.some.inj (hc'.symm.trans hc)
    subst hcc
    obtain ⟨hcs, hcol⟩ := Array.getElem?_eq_some_iff.mp hc
    have hCV : ColumnValid M c col' := hcol ▸ hV c hcs
    rw [hp1, hq1] at hlt
    simp only at hlt
    have hrow := hCV.rows_strict (k + 1) (k' + 1) _ _ hcell hcell' hlt
    exact Recon.official_strictMono (Recon.realNodes_row_one_le hV hp) hrow
  rcases Nat.lt_trichotomy p.1.index q.1.index with hlt | heq | hgt
  · exact absurd h (ne_of_lt (strict hp hq hlt))
  · exact Recon.realNodes_index_eq hp hq heq
  · exact absurd h.symm (ne_of_lt (strict hq hp hgt))

/-- **The leg of the node `(x, C)` after an ascension test.** If the node `(x, Z)` at the
reference row `Z` of `C` passes the test (its in-row parents reach `cr` exactly) and
`x > cr`, the leg of `(x, C)` is at or right of `cr`. -/
theorem leg_of_ascension {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M)
    {cr x : Nat} (hx : cr < x) {C : Row} {ref : Ref} {cl : Cell}
    (hn : nodeAt M x (referenceRow C) = some (ref, cl))
    (hr : reachesRoot M cr (x + 1) ref = .ok true)
    {csRef : Ref} {cs : Cell} (hcs : nodeAt M x C = some (csRef, cs)) {l : Ref}
    (hl : cs.left = some l) : cr ≤ l.column := by
  have hV := build_valid_of_success hb
  have hcert := Recon.certified_of_build hb
  obtain ⟨hmem, hrow⟩ := Recon.RowLaw.nodeAt_spec hn
  obtain ⟨hcolx, hidx⟩ := Recon.RowLaw.realNodes_column hmem
  simp only at hcolx hidx hrow
  obtain ⟨q, hw, hq⟩ := weakParent_of_reachesRoot (by rw [hcolx]; exact hx) hr
  obtain ⟨col, cell', upper, parentCell, hcol, hcell, hup, hleft, hpc, hprow⟩ :=
    Recon.RowLaw.weakParent_some hw
  obtain ⟨col0, k, hc0, hck, hp1⟩ := Recon.mem_realNodes_iff.mp hmem
  simp only at hp1
  rw [hp1] at hcol hcell hup
  simp only at hcol hcell hup
  have hcc : col0 = col := Option.some.inj (hc0.symm.trans hcol)
  subst hcc
  have hce : cell' = cl := Option.some.inj (hcell.symm.trans hck)
  subst hce
  by_cases h0 : 0 < C.coeff 0
  · -- the node above the reference node is `(x, C)`, and its leg is the in-row parent
    have hxs : x < M.size := (Array.getElem?_eq_some_iff.mp hc0).1
    have hcolEq : M[x] = col0 := (Array.getElem?_eq_some_iff.mp hc0).2
    have hG := hcert.geometry x hxs
    rw [hcolEq] at hG
    obtain ⟨ref2, parent2, hleft2, hcell2, _, hrow2⟩ := hG (k + 1) cell' upper hck hup
      (by omega)
    have href2 : ref2 = q := Option.some.inj (hleft2.symm.trans hleft)
    subst href2
    have hpe : parent2 = parentCell := by
      have := hcell2.symm.trans hpc
      cases this
      rfl
    subst hpe
    rw [hprow] at hrow2
    have hCV := hcert.valid x hxs
    rw [hcolEq] at hCV
    have hlow : (1 : Row) ≤ cell'.row :=
      Expansion.row_one_le_of_ne_zero (ne_of_gt (hCV.rows_strict 0 (k + 1) phantom cell'
        hCV.phantom hck (by omega)))
    have hupmem : ((⟨x, k + 1 + 1⟩ : Ref), upper) ∈ realNodes M x :=
      Recon.mem_realNodes_iff.mpr ⟨col0, k + 1, hc0, hup, rfl⟩
    have hupRow : official upper.row = C := by
      rw [hrow2, Row.B_self, Recon.RowLaw.official_bump hlow 0, hrow]
      exact Recon.RowLaw.referenceRow_bump h0
    obtain ⟨hcsmem, hcsrow⟩ := Recon.RowLaw.nodeAt_spec hcs
    have heq := realNodes_eq_of_official hV hcsmem hupmem (by simp only; rw [hcsrow, hupRow])
    have hcsu : cs = upper := congrArg Prod.snd heq
    rw [hcsu, hleft] at hl
    rw [← Option.some.inj hl]
    exact hq
  · -- the reference row is `C` itself: `q` is the raw parent of `(x, C)`
    have hZ : referenceRow C = C := by
      unfold referenceRow
      rw [if_neg h0]
    rw [hZ, hcs] at hn
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
    have hraw : Reserve.rawParent M csRef = some q := by
      rw [hp1]
      simp only [Reserve.rawParent, hc0, Option.bind_eq_bind, Option.bind_some, hup, hleft]
    have hcsc : cell? M csRef = some cs := by
      rw [hp1]
      simpa [cell?, hc0] using hck
    have hle := rawParent_column_le_left hb hcsc (by rw [hp1]; simp) hl hraw
    omega

/-! ## Items with a copied root row carry their ascension test -/

/-- The ascension test of a copied root row `C` in the column `ctx.x`. -/
def AscClean (ctx : Context) (C : Row) : Prop :=
  ∃ ref cl, nodeAt ctx.source ctx.x (referenceRow C) = some (ref, cl) ∧
    reachesRoot ctx.source ctx.rootColumn (ctx.x + 1) ref = .ok true

/-- Every copied root row of an item passed its ascension test. -/
def ItemAsc (ctx : Context) (it : Item) : Prop := ∀ C, it.clean = some C → AscClean ctx C

theorem ascClean_of_ascends {ctx : Context} {r : Ref} {cl : Cell}
    (h : ascends ctx (some (r, cl)) = .ok true) : AscClean ctx (official cl.row) := by
  unfold ascends at h
  simp only at h
  cases hn : nodeAt ctx.source ctx.x (referenceRow (official cl.row)) with
  | none => rw [hn] at h; simp [pure, Except.pure] at h
  | some p =>
    obtain ⟨ref, c⟩ := p
    rw [hn] at h
    exact ⟨ref, c, hn, h⟩

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
theorem childItems_asc {ctx : Context} {d : Nat} {it : Item} {cs : List Item}
    (h : childItems ctx d it = .ok cs) (hit : ItemAsc ctx it) : ∀ c ∈ cs, ItemAsc ctx c := by
  unfold childItems at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  generalize topIn ctx.source ctx.rootColumn d it.source = rho at h
  split at h
  · obtain rfl := Except.ok.inj h
    simp
  · split at h
    · cases h
    · rename_i v hv
      split at h
      · split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · obtain rfl := Except.ok.inj h
          intro c hc
          simp only [List.mem_map, List.mem_range] at hc
          obtain ⟨j, _, rfl⟩ := hc
          intro C' hC'
          simp at hC'
      · rename_i hasc
        have hvt : v = true := by simpa using hasc
        subst hvt
        have hsome : ∃ r cl, rho = some (r, cl) := by
          cases rho with
          | none => simp [ascends, pure, Except.pure] at hv
          | some p => exact ⟨p.1, p.2, rfl⟩
        obtain ⟨r, cl, rfl⟩ := hsome
        have hrho := ascClean_of_ascends hv
        simp only at h
        split at h
        · rename_i hclean
          split at h
          · obtain rfl := Except.ok.inj h
            intro c hc
            simp only [List.mem_map, List.mem_range] at hc
            obtain ⟨j, _, rfl⟩ := hc
            (try split_ifs) <;> intro C' hC' <;>
              simp only [Option.some.injEq, reduceCtorEq] at hC' <;> (try subst hC') <;>
              first | exact hrho | exact hit _ hclean
          · obtain rfl := Except.ok.inj h
            intro c hc
            simp only [List.mem_map, List.mem_filter, List.mem_range] at hc
            obtain ⟨j, _, rfl⟩ := hc
            (try split_ifs) <;> intro C' hC' <;>
              simp only [Option.some.injEq, reduceCtorEq] at hC' <;> (try subst hC') <;>
              first | exact hrho | exact hit _ hclean
        · rename_i C hclean
          split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · split at h
            · cases h
            · split at h
              · simp [throw, throwThe, MonadExceptOf.throw] at h
              · obtain rfl := Except.ok.inj h
                intro c hc
                simp only [List.mem_map, List.mem_range] at hc
                obtain ⟨j, _, rfl⟩ := hc
                (try split_ifs) <;> intro C' hC' <;>
                  simp only [Option.some.injEq, reduceCtorEq] at hC' <;> (try subst hC') <;>
                  first | exact hrho | exact hit _ hclean

/-- The origin of a copy of the root row is the node `(x, C)` of a row `C` that passed its
ascension test. -/
def CleanAsc (ctx : Context) (p : Emit × Origin) : Prop :=
  ∀ r b, p.2 = .clean r b → ∃ C cs, nodeAt ctx.source ctx.x C = some (r, cs) ∧ AscClean ctx C

theorem levelOneT_cleanAsc {ctx : Context} {it : Item} (hit : ItemAsc ctx it)
    {ps : List (Emit × Origin)} (h : levelOneT ctx it = .ok ps) : ∀ p ∈ ps, CleanAsc ctx p := by
  unfold levelOneT at h
  cases hsrc : nodeAt ctx.source ctx.x it.source with
  | none => simp [hsrc, pure, Except.pure] at h; subst h; simp
  | some q =>
      obtain ⟨srcRef, src⟩ := q
      simp only [hsrc] at h
      cases hC : it.clean with
      | some C =>
          simp only [hC] at h
          cases hcs : nodeAt ctx.source ctx.x C with
          | none => simp [hcs, throw, throwThe, MonadExceptOf.throw] at h
          | some q' =>
              obtain ⟨csRef, cs⟩ := q'
              simp only [hcs, bind, Except.bind, pure, Except.pure] at h
              split at h
              · cases h
              · cases h
                intro p hp
                simp only [List.mem_singleton] at hp
                subst hp
                intro r b hrb
                simp only [Origin.clean.injEq] at hrb
                obtain ⟨rfl, _⟩ := hrb
                exact ⟨C, cs, hcs, hit C hC⟩
      | none =>
          simp only [hC] at h
          split at h
          · simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            intro p hp
            simp only [List.mem_singleton] at hp
            subst hp
            intro r b hrb
            cases hrb
          · simp only [bind, Except.bind, pure, Except.pure] at h
            split at h
            · cases h
            · cases h
              intro p hp
              simp only [List.mem_singleton] at hp
              subst hp
              intro r b hrb
              cases hrb

theorem runItemT_cleanAsc (ctx : Context) :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), ItemAsc ctx it →
      runItemT ctx d it = .ok ps → ∀ p ∈ ps, CleanAsc ctx p
  | 0, _, ps, _, h => by simp [runItemT, pure, Except.pure] at h; subst h; simp
  | 1, it, ps, hit, h => levelOneT_cleanAsc hit (by simpa [runItemT] using h)
  | d + 2, it, ps, hit, h => by
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
          exact runItemT_cleanAsc ctx (d + 1) c out (childItems_asc hch hit c hc) hco p hpo

theorem lowerItems_asc (ctx : Context) (τ : Row) : ∀ p ∈ lowerItems τ, ItemAsc ctx p.2 := by
  intro p hp
  simp only [lowerItems, List.mem_flatMap, List.mem_reverse, List.mem_range, List.mem_map] at hp
  obtain ⟨k, _, j, _, rfl⟩ := hp
  intro C hC
  simp at hC

/-- **Every copy of the root row passed its ascension test.** -/
theorem emitsT_cleanAsc {ctx : Context} {τ : Row} {es : List (Emit × Origin)}
    (h : emitsT ctx τ = .ok es) : ∀ p ∈ es, CleanAsc ctx p := by
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
          obtain ⟨q, hq, hqo⟩ := mem_of_mapM houts hout
          exact runItemT_cleanAsc ctx q.1 q.2 out (lowerItems_asc ctx τ q hq) hqo p hpo
      · unfold upperT at hupper
        obtain ⟨q, _, hqp⟩ := mem_of_mapM hupper hp
        simp only [bind, Except.bind, pure, Except.pure] at hqp
        split at hqp
        · cases hqp
        · cases hqp
          intro r b hrb
          cases hrb

/-! ## The leg of a copy of the root row -/

/-- **The leg of the origin of a copy of the root row (`b = 0` or `b = 1`) in a block
`i ≥ 1` is at or right of the root column.** -/
theorem cleanLeg {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} {X x i : Nat} {es : List (Emit × Origin)}
    (hS : Site s n D M out ρ R t X x i es) {j : Nat} (hj : j < es.length) {r : Ref} {b : Bool}
    (ho : es[j].2 = .clean r b) {cu cv : Cell} {ref l pe pa : Ref} {cpe cpa : Cell}
    (hL : Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa) : ρ.cr ≤ l.column := by
  obtain ⟨hcx, _⟩ := mem_blockColumns_pos hS.xMem hS.iPos
  obtain ⟨C, cs, hcs, ref', cl', hn, hr⟩ :=
    emitsT_cleanAsc hS.emits es[j] (List.getElem_mem hj) r b ho
  simp only [ctxAt] at hcs hn hr
  -- the origin's cell is the cell of `(x, C)`
  obtain ⟨_, _, hcscell, _⟩ := Classification.nodeAt_spec hcs
  have hsrc : es[j].2.src = r := by rw [ho]; rfl
  have hcv := hL.hcv
  rw [hsrc] at hcv
  have hcvs : cv = cs := Option.some.inj (hcv.symm.trans hcscell)
  subst hcvs
  exact leg_of_ascension hS.splice.build hcx hn hr hcs hL.hl

/-- **`CutLeg` holds.** -/
theorem cutLeg : CutLeg := by
  intro s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL
  have ho : ∃ r, es[j].2 = .clean r true := by
    generalize es[j].2 = o at hcut
    cases o with
    | clean r b => cases b <;> simp_all [cutOrigin]
    | plain r => simp [cutOrigin] at hcut
    | upper r => simp [cutOrigin] at hcut
  obtain ⟨r, ho⟩ := ho
  exact cleanLeg hS hj ho hL

/-- **The two gap-copy regions** from `StepInner` and the four remaining gap-copy
statements (`CutLeg` is proved). -/
theorem regionCutBoundary_of_chains' (hStep : StepInner) (hCut : StepCut) (hJump : CutJump)
    (hCopy : CutStartCopy) (hRoot : CutStartRoot) : RegionCutBoundary :=
  regionCutBoundary_of_chains hStep hCut cutLeg hJump hCopy hRoot

theorem regionCutInner_of_chains' (hStep : StepInner) (hCut : StepCut) (hJump : CutJump)
    (hCopy : CutStartCopy) (hRoot : CutStartRoot) : RegionCutInner :=
  regionCutInner_of_chains hStep hCut cutLeg hJump hCopy hRoot

/-- **Well-foundedness of the official expansion** from the reconstruction, the five
statements of `ChainCorrRegions.lean` and the four open gap-copy statements. -/
theorem wellFounded_of_chains_cut (hrec : Dimension.BlockReconstruction) (hStep : StepInner)
    (hLeg : StartLeg) (hJump : StartJump) (hCopy : StartCopy) (hRoot : StartRoot)
    (hCut : StepCut) (hCJump : CutJump) (hCCopy : CutStartCopy) (hCRoot : CutStartRoot) :
    WellFounded Step :=
  wellFounded_of_all_chains hrec hStep hLeg hJump hCopy hRoot hCut cutLeg hCJump hCCopy hCRoot

end OmegaY.Official.Classification.Proofs.ChainCorr

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.rawParent_column_le_left
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.cleanLeg
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.cutLeg
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.wellFounded_of_chains_cut
