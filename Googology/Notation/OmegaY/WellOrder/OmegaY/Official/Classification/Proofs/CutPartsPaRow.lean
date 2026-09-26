/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CutPartsPaRow.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
Port change: in `index_pos_of_one_le` the last step uses `lt_of_lt_of_eq` instead of `rw … at hlt`.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutPartsStart
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrStartLegJump

set_option backward.do.legacy false

/-!
# `CutPaRow`: the node `pa` of a copy of the root row is at the row of the origin

`CutPaRow` (`CutPartsStart.lean`) says: for a gap copy with origin `o = (x, C)` and leg `l`,
the highest node `pa` of the column `l` of `M(s)` at or below the row of `o` is at that row.
This file proves it for every copy of the root row (`b = 0` or `b = 1`, `paRow_of_clean`),
hence `CutPaRow` (`cutPaRow`).

## The argument

The origin `(x, C)` of a copy of the root row passed its ascension test
(`ChainCorrCutLeg.lean`): the node `a = (x, Z)` at the reference row `Z` of `C` exists and the
in-row parents from `a` reach the column `cr` exactly. Also `C` is the row of a node of the
root column (the top `ρ` of the root column in the region, `LegJump.CleanTop`;
`emitsT_cleanRow`).

* If the finite coefficient of `C` is `0`, then `Z = C`, `a = (x, C)`, and its in-row parent
  `q` is its raw parent, at the row `C`. In a canonical mountain the parent search for the node
  above `u` starts at the highest node of the leg column of `u` at or below the row of `u` and
  the rows along the search do not increase (`Frame.Hit.height_le`,
  `ControlProof.Q_of_highestAtMost`), so `row q ≤ row pa` (`rawParent_row_le_hAM`). With
  `row pa ≤ C = row q`, `row pa = C`.
* Otherwise `Z = C - 1`, `(x, C)` is the node above `a`, and its leg is `q = P(a)`, at the row
  `Z`. If `q` is right of `cr`, the in-row parents continue from `q`: the node above `q` exists
  and is at the row `bump Z 0 = C` (the row law). If `q` is in the root column, the node of the
  root column at the row `C` exists by `CleanTop`. Either way the column `l` has a node at the
  row `C`, so `row pa = C`.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.CutParts

open Canonical Reserve Official Descent Classification Proofs

/-! ## The copied root row is a row of the root column -/

/-- A copy of the root row has as origin the node `(x, C)` of a row `C` of a node of the root
column. -/
def CleanRow (ctx : Context) (p : Emit × Origin) : Prop :=
  ∀ r b, p.2 = .clean r b → ∃ ρ ∈ realNodes ctx.source ctx.rootColumn, ∃ C cs,
    nodeAt ctx.source ctx.x C = some (r, cs) ∧ official ρ.2.row = C

theorem levelOneT_cleanRow {ctx : Context} {it : Item} (hit : LegJump.CleanTop ctx 1 it)
    {ps : List (Emit × Origin)} (h : levelOneT ctx it = .ok ps) : ∀ p ∈ ps, CleanRow ctx p := by
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
                obtain ⟨ρ, hρ, hρrow⟩ := hit C hC
                exact ⟨ρ, (Recon.RowLaw.topIn_spec hρ).1, C, cs, hcs, hρrow⟩
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

theorem runItemT_cleanRow (ctx : Context) :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), LegJump.CleanTop ctx d it →
      runItemT ctx d it = .ok ps → ∀ p ∈ ps, CleanRow ctx p
  | 0, _, ps, _, h => by simp [runItemT, pure, Except.pure] at h; subst h; simp
  | 1, it, ps, hit, h => levelOneT_cleanRow hit (by simpa [runItemT] using h)
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
          exact runItemT_cleanRow ctx (d + 1) c out (LegJump.childItems_cleanTop hch hit c hc)
            hco p hpo

theorem lowerItems_cleanTop (ctx : Context) (τ : Row) :
    ∀ p ∈ lowerItems τ, LegJump.CleanTop ctx p.1 p.2 := by
  intro p hp
  simp only [lowerItems, List.mem_flatMap, List.mem_reverse, List.mem_range, List.mem_map] at hp
  obtain ⟨k, _, j, _, rfl⟩ := hp
  intro C hC
  simp at hC

/-- **Every copy of the root row copies a row of the root column.** -/
theorem emitsT_cleanRow {ctx : Context} {τ : Row} {es : List (Emit × Origin)}
    (h : emitsT ctx τ = .ok es) : ∀ p ∈ es, CleanRow ctx p := by
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
          exact runItemT_cleanRow ctx q.1 q.2 out (lowerItems_cleanTop ctx τ q hq) hqo p hpo
      · unfold upperT at hupper
        obtain ⟨q, _, hqp⟩ := mem_of_mapM hupper hp
        simp only [bind, Except.bind, pure, Except.pure] at hqp
        split at hqp
        · cases hqp
        · cases hqp
          intro r b hrb
          cases hrb

/-! ## Rows in a column -/

theorem row_le_of_index_le {M : Mountain} (hV : MountainValid M) {c a b : Nat} {x y : Cell}
    (hx : cell? M ⟨c, a⟩ = some x) (hy : cell? M ⟨c, b⟩ = some y) (h : a ≤ b) :
    x.row ≤ y.row := by
  rcases Nat.lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (cell_row_lt hV hx hy h)
  · rw [hx] at hy
    cases hy
    exact le_refl _

/-- If the column `c` has a real node at the row `row`, the highest node of `c` at or below
`row` is at `row`. -/
theorem hAM_row_of_node {M : Mountain} (hV : MountainValid M) {c : Nat} {row : Row}
    {pa w : Ref} {cpa cw : Cell} (hpa : highestAtMost M c row = some pa)
    (hcpa : cell? M pa = some cpa) (hw : w.column = c) (hw0 : 0 < w.index)
    (hcw : cell? M w = some cw) (hrow : cw.row = row) : cpa.row = row := by
  obtain ⟨hpac, _, col, hcol, _, hparow, hmax⟩ := highestAtMost_spec hpa
  obtain ⟨col', hcol', hwI, hcwe⟩ := cell?_column hcw
  rw [hw] at hcol'
  have hcc : col' = col := Option.some.inj (hcol'.symm.trans hcol)
  subst hcc
  have hle := hmax w.index hwI hw0 (by rw [hcwe, hrow])
  have hw' : cell? M ⟨c, w.index⟩ = some cw := by rw [← hw]; exact hcw
  have hpa' : cell? M ⟨c, pa.index⟩ = some cpa := by rw [← hpac]; exact hcpa
  have h1 := row_le_of_index_le hV hw' hpa' hle
  obtain ⟨col'', hcol'', hpI, hcpe⟩ := cell?_column hcpa
  rw [hpac] at hcol''
  have hcc' : col'' = col' := Option.some.inj (hcol''.symm.trans hcol')
  subst hcc'
  apply le_antisymm
  · rw [← hcpe]; exact hparow
  · rw [← hrow]; exact h1

/-! ## The raw parent is not above the node read in the leg column -/

/-- **In a canonical mountain the raw parent of a real node `u` is not above the highest node
of the leg column of `u` at or below the row of `u`.** -/
theorem rawParent_row_le_hAM {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M)
    {u q l pa : Ref} {cu cq cpa : Cell} (hcu : cell? M u = some cu) (hu : 0 < u.index)
    (hl : cu.left = some l) (hpa : highestAtMost M l.column cu.row = some pa)
    (hcpa : cell? M pa = some cpa) (hraw : Reserve.rawParent M u = some q)
    (hcq : cell? M q = some cq) : cq.row ≤ cpa.row := by
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
    have hh := hit.height_le hO
    have hl' : ((Geometry.Frame.ofMountain M).cell nu).left = some l := by rw [hcell]; exact hl
    have hpa' : highestAtMost M l.column ((Geometry.Frame.ofMountain M).height nu) = some pa := by
      simp only [Geometry.Frame.height, hcell]
      exact hpa
    obtain ⟨q', hQ', hq'⟩ := ControlProof.Q_of_highestAtMost hO hl' hpa'
    have hqq : qq = q' := Option.some.inj (hQ.symm.trans hQ')
    subst hqq
    have e1 : (Geometry.Frame.ofMountain M).height qq = cpa.row := by
      have := ControlProof.cell?_ref (M := M) qq
      rw [hq', hcpa] at this
      simp only [Geometry.Frame.height]
      rw [← Option.some.inj this]
    have e2 : (Geometry.Frame.ofMountain M).height np = cq.row := by
      have := ControlProof.cell?_ref (M := M) np
      rw [hnp, hcq] at this
      simp only [Geometry.Frame.height]
      rw [← Option.some.inj this]
    rw [← e1, ← e2]
    exact hh

/-! ## `CutPaRow` -/

/-- The first step of the ascension test from a node right of `cr`. -/
theorem reachesRoot_next {M : Mountain} {cr f : Nat} {a : Ref} (ha : cr < a.column)
    (h : reachesRoot M cr (f + 1) a = .ok true) :
    ∃ q, Expansion.weakParent M a = .ok (some q) ∧ reachesRoot M cr f q = .ok true := by
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
      exact ⟨q, Reconstruction.liftE_ok hw, h⟩

theorem index_pos_of_one_le {M : Mountain} (hV : MountainValid M) {v : Ref} {cv : Cell}
    (h : cell? M v = some cv) (h1 : (1 : Row) ≤ cv.row) : 0 < v.index := by
  by_contra h0
  have hv0 : v.index = 0 := by omega
  obtain ⟨colv, hcolv, hcv⟩ := cell?_spec h
  obtain ⟨hc, hcolEq⟩ := column_of_getElem? hcolv
  have hCV := hV v.column hc
  rw [hcolEq] at hCV
  rw [hv0, hCV.phantom] at hcv
  cases hcv
  have hsz := hCV.size_ge_two
  have hb1 : colv[1]? = some colv[1] := Array.getElem?_eq_getElem (by omega)
  have hlt := hCV.rows_strict 0 1 phantom colv[1] hCV.phantom hb1 (by omega)
  exact absurd h1 (not_le.mpr (lt_of_lt_of_eq hlt (hCV.bottom_row colv[1] hb1)))

theorem official_inj' {a b : Row} (ha : (1 : Row) ≤ a) (hb : (1 : Row) ≤ b)
    (h : official a = official b) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (ne_of_lt (Recon.official_strictMono ha hab))
  · exact hab
  · exact absurd h.symm (ne_of_lt (Recon.official_strictMono hb hab))

theorem hAM_row_le {M : Mountain} {c : Nat} {row : Row} {pa : Ref} {cpa : Cell}
    (hpa : highestAtMost M c row = some pa) (hcpa : cell? M pa = some cpa) : cpa.row ≤ row := by
  obtain ⟨hpac, _, col, hcol, _, hparow, _⟩ := highestAtMost_spec hpa
  obtain ⟨col', hcol', _, hcpe⟩ := cell?_column hcpa
  rw [hpac] at hcol'
  have hcc : col' = col := Option.some.inj (hcol'.symm.trans hcol)
  subst hcc
  rw [← hcpe]
  exact hparow

/-- **The node `pa` of a copy of the root row is at the row of the origin.** -/
theorem paRow_of_clean {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} {X x i : Nat} {es : List (Emit × Origin)}
    (hS : Site s n D M out ρ R t X x i es) {j : Nat} (hj : j < es.length) {r : Ref} {b : Bool}
    (ho : es[j].2 = .clean r b) {cu cv : Cell} {ref l pe pa : Ref} {cpe cpa : Cell}
    (hL : Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa) : cpa.row = cv.row := by
  have hb := hS.splice.build
  have hV := build_valid_of_success hb
  obtain ⟨hcx, _⟩ := mem_blockColumns_pos hS.xMem hS.iPos
  obtain ⟨C, cs, hcs, ref0, cl0, hn, hr⟩ :=
    emitsT_cleanAsc hS.emits es[j] (List.getElem_mem hj) r b ho
  obtain ⟨ρ0, hρ0, C', cs', hcs', hρrow⟩ :=
    emitsT_cleanRow hS.emits es[j] (List.getElem_mem hj) r b ho
  simp only [ctxAt] at hcs hn hr hρ0 hcs'
  -- the origin's cell is the cell of `(x, C)`
  obtain ⟨hrx, hr1, hcscell, hcsrow⟩ := Classification.nodeAt_spec hcs
  obtain ⟨_, _, hcscell', hcsrow'⟩ := Classification.nodeAt_spec hcs'
  simp only at hrx hr1 hcscell hcsrow hcscell' hcsrow'
  have hccs : cs' = cs := Option.some.inj (hcscell'.symm.trans hcscell)
  subst cs'
  have hCC : C' = C := hcsrow'.symm.trans hcsrow
  subst C'
  have hsrc : es[j].2.src = r := by rw [ho]; rfl
  have hcv := hL.hcv
  rw [hsrc] at hcv
  have hcvs : cv = cs := Option.some.inj (hcv.symm.trans hcscell)
  subst cv
  have hl := hL.hl
  have hcs1 : (1 : Row) ≤ cs.row := one_le_row hV hcscell hr1
  -- the reference node and its in-row parent
  obtain ⟨hmem, hrow⟩ := Recon.RowLaw.nodeAt_spec hn
  obtain ⟨hcolx, hidx⟩ := Recon.RowLaw.realNodes_column hmem
  simp only at hcolx hidx hrow
  have hax : ρ.cr < ref0.column := by rw [hcolx]; exact hcx
  obtain ⟨q, hw, hq⟩ := weakParent_of_reachesRoot hax hr
  obtain ⟨col, cell', upper, parentCell, hcol, hcell, hup, hleft, hpc, hprow⟩ :=
    Recon.RowLaw.weakParent_some hw
  have hc0 : cell? M ref0 = some cell' := by simp [cell?, hcol, hcell]
  have hcl0 : cl0 = cell' := by
    have := (mem_realNodes (M := M) hmem).2.2
    exact Option.some.inj (this.symm.trans hc0)
  subst cl0
  have hcup : cell? M (Inner.up ref0) = some upper := by simp [cell?, Inner.up, hcol, hup]
  obtain ⟨colq, hcolq, hcq⟩ := cellAt_ok_iff.mp hpc
  have hcellq : cell? M q = some parentCell := by simp [cell?, hcolq, hcq]
  have hraw : Reserve.rawParent M ref0 = some q := by
    simp only [Reserve.rawParent, hcol, Option.bind_eq_bind, Option.bind_some, hup, hleft]
  have hc'1 : (1 : Row) ≤ cell'.row := one_le_row hV hc0 hidx
  by_cases h0 : 0 < C.coeff 0
  · -- `(x, C)` is the node above the reference node; its leg is `q`
    -- the target: a node of the column `l` at the row of the origin
    suffices hw : ∃ w cw, w.column = l.column ∧ 0 < w.index ∧ cell? M w = some cw ∧
        cw.row = cs.row by
      obtain ⟨w, cw, hwc, hw0, hcw, hrow⟩ := hw
      exact hAM_row_of_node hV hL.hpa hL.hcpa hwc hw0 hcw hrow
    have hB := Inner.canon_rowLaw hb (by omega) hc0 hcup hleft hcellq
    rw [hprow, Row.B_self] at hB
    have hupRow : official upper.row = C := by
      rw [hB, Recon.RowLaw.official_bump hc'1 0, hrow]
      exact Recon.RowLaw.referenceRow_bump h0
    have hup1 : (1 : Row) ≤ upper.row := one_le_row hV hcup (by simp [Inner.up])
    have hupcs : upper.row = cs.row :=
      official_inj' hup1 hcs1 (by rw [hupRow, hcsrow])
    -- `(x, C)` is the node above `ref0`
    have hupr : Inner.up ref0 = r := by
      have hcol' : (Inner.up ref0).column = r.column := by simp [Inner.up, hcolx, hrx]
      exact Inner.cell?_eq_of_index hV hcol' hcup hcscell hupcs
    have hlq : l = q := by
      rw [← hupr] at hcscell
      have hcu' : cs = upper := Option.some.inj (hcscell.symm.trans hcup)
      subst hcu'
      exact Option.some.inj (hl.symm.trans hleft)
    subst l
    rcases Nat.lt_or_eq_of_le hq with hqlt | hqeq
    · -- the in-row parents continue from `q`: the node above `q` is at the row `C`
      obtain ⟨q', hw', hr'⟩ := reachesRoot_next hax hr
      have hqq : q' = q := by
        rw [hw] at hw'
        exact (Option.some.inj (Except.ok.inj hw')).symm
      subst q'
      obtain ⟨p2, hw2, _⟩ := weakParent_of_reachesRoot hqlt hr'
      obtain ⟨col2, cell2, upper2, par2, hcol2, hcell2, hup2, hleft2, hpc2, hprow2⟩ :=
        Recon.RowLaw.weakParent_some hw2
      have hc2 : cell? M q = some cell2 := by simp [cell?, hcol2, hcell2]
      have hc2e : cell2 = parentCell := Option.some.inj (hc2.symm.trans hcellq)
      subst cell2
      have hcup2 : cell? M (Inner.up q) = some upper2 := by simp [cell?, Inner.up, hcol2, hup2]
      obtain ⟨colp, hcolp, hcp⟩ := cellAt_ok_iff.mp hpc2
      have hcellp : cell? M p2 = some par2 := by simp [cell?, hcolp, hcp]
      have hq1 : (1 : Row) ≤ parentCell.row := by rw [hprow]; exact hc'1
      have hq0 := index_pos_of_one_le hV hcellq hq1
      have hB2 := Inner.canon_rowLaw hb hq0 hcellq hcup2 hleft2 hcellp
      rw [hprow2, Row.B_self] at hB2
      have hup2Row : official upper2.row = C := by
        rw [hB2, Recon.RowLaw.official_bump hq1 0, hprow, hrow]
        exact Recon.RowLaw.referenceRow_bump h0
      have hup21 : (1 : Row) ≤ upper2.row := one_le_row hV hcup2 (by simp [Inner.up])
      exact ⟨Inner.up q, upper2, rfl, by simp [Inner.up], hcup2,
        official_inj' hup21 hcs1 (by rw [hup2Row, hcsrow])⟩
    · -- `q` is in the root column: the node of the root column at the row `C`
      obtain ⟨hρc, hρi⟩ := Recon.RowLaw.realNodes_column hρ0
      have hρcell := (mem_realNodes (M := M) hρ0).2.2
      have hρ1 : (1 : Row) ≤ ρ0.2.row := Recon.realNodes_row_one_le hV hρ0
      exact ⟨ρ0.1, ρ0.2, by rw [hρc, hqeq], by omega, hρcell,
        official_inj' hρ1 hcs1 (by rw [hCC, hcsrow])⟩
  · -- the reference row is `C` itself: `q` is the raw parent of `(x, C)`, at the row `C`
    have hZ : referenceRow C = C := by
      unfold referenceRow
      rw [if_neg h0]
    rw [hZ] at hn
    rw [hn] at hcs
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hcs)
    have hle := rawParent_row_le_hAM hb hc0 (by omega) hl hL.hpa hL.hcpa hraw hcellq
    rw [hprow] at hle
    exact le_antisymm (hAM_row_le hL.hpa hL.hcpa) hle

/-- **`CutPaRow` holds.** -/
theorem cutPaRow : CutPaRow := by
  intro s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL
  have ho : ∃ r, es[j].2 = .clean r true := by
    generalize es[j].2 = o at hcut
    cases o with
    | clean r b => cases b <;> simp_all [cutOrigin]
    | plain r => simp [cutOrigin] at hcut
    | upper r => simp [cutOrigin] at hcut
  obtain ⟨r, ho⟩ := ho
  exact paRow_of_clean hS hj ho hL

end OmegaY.Official.Classification.Proofs.ChainCorr.CutParts

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.CutParts.rawParent_row_le_hAM
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.CutParts.emitsT_cleanRow
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.CutParts.paRow_of_clean
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.CutParts.cutPaRow
