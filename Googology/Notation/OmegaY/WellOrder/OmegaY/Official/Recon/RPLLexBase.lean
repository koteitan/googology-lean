/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/RPLLexBase.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.Pk4Main
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LRCJump
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.PBStageBBndSim

set_option backward.do.legacy false

/-!
# `Lex` in the output from the parent columns alone

In the output `R` of `s[n]` the row law (`RowLawHolds`, from the proved `JumpLawHolds`), the
parent bound (`ParentBelowHolds`, proved) and the highest-below property of stored parents
(`hb_run`) hold in every new column; in an old column they hold because `M(s)` is normal.
So for a real node `a` with the node `a⁺` above it and the stored parent `p` of `a` (the stored
left end of `a⁺`):

* `row p ≤ row a` and `row a⁺ = B(row a, row p)` (`localLaw`);
* `p` is the highest node of its column at or below `row a` (it is below `row a⁺ > row a`).

Hence the row of `a⁺` and the stored parent `p` depend only on `row a` and the column of `p`
(`same_parent`). Two nodes with the same row therefore compare by `Lex` as soon as the columns
of the stored parents along the two columns compare (`lex_of_legs`): the rows stay equal while
the parent columns are equal, `Lex.left` applies at the first smaller column, and `Lex.top`
when the first column ends.

`LegsOK R cz a cw b K`: for `m < K` the nodes `(cz, a + m)` and `(cw, b + m)` have stored
parents in the same column, and at `m = K` either `(cz, a + K)` is the top of its column or
both have stored parents and the first is in a smaller column.
-/

namespace OmegaY.Official.Recon.RPLLex

open Canonical Expansion Geometry Frame Classification
open Classification.ControlProof (node_eq_of_index)

/-! ## The local law of a node of the output -/

section Local

variable {s : List Nat} {n : Nat} {R : Mountain}

theorem arr_of_cell {r : Ref} {x : Cell} (h : Reserve.cell? R r = some x) (hc : r.column < R.size) :
    R[r.column][r.index]? = some x := by
  unfold Reserve.cell? at h
  rw [Array.getElem?_eq_getElem hc] at h
  simpa using h

theorem cellAt_of_cell {r : Ref} {x : Cell} (h : Reserve.cell? R r = some x) :
    cellAt R r = .ok x := by
  unfold Reserve.cell? at h
  unfold cellAt
  cases hcol : R[r.column]? with
  | none => rw [hcol] at h; cases h
  | some col =>
    rw [hcol] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    simp only [h]

theorem cellAt_node (A : (Frame.ofMountain R).Node) :
    cellAt R (Frame.ref A) = .ok ((Frame.ofMountain R).cell A) :=
  cellAt_of_cell (LowerChainRecon.cell?_ref A)

/-- **The local law** of a real node of a new column. -/
theorem localLaw_new (hrun : Official.expandDiagram s n = .ok R) {Z Z' A : (Frame.ofMountain R).Node}
    (hx : s.length - 1 ≤ Z.1.val) (hZ : Real Z) (hZu : (Frame.ofMountain R).upper Z = some Z')
    (hraw : (Frame.ofMountain R).rawParent Z = some A) :
    (Frame.ofMountain R).height A ≤ (Frame.ofMountain R).height Z ∧
      (Frame.ofMountain R).height Z' =
        Row.B ((Frame.ofMountain R).height Z) ((Frame.ofMountain R).height A) := by
  refine ⟨LowerPB.StageB.parentBelowHolds s n R hrun Z A hx hZ hraw, ?_⟩
  obtain ⟨up, hup, hleft⟩ := rawParent_spec hraw
  rw [hZu] at hup
  obtain rfl := Option.some.inj hup
  obtain ⟨h1, h2⟩ := upper_spec hZu
  have hRL := RowLaw.rowLawHolds_of_jumpLaw LRC.jumpLawHolds
  have hZ0 : 0 < Z.2.val := hZ
  have hl : R[Z.1.val][Z.2.val]? = some ((Frame.ofMountain R).cell Z) :=
    arr_of_cell (r := Frame.ref Z) (LowerChainRecon.cell?_ref Z) Z.1.isLt
  have hu : R[Z.1.val][Z.2.val + 1]? = some ((Frame.ofMountain R).cell Z') := by
    have h3 := LowerChainRecon.cell?_ref Z'
    rw [LowerChainRecon.above_of_upper hZu] at h3
    exact arr_of_cell (r := ⟨Z.1.val, Z.2.val + 1⟩) h3 Z.1.isLt
  exact hRL s n R hrun Z.1.val Z.1.isLt hx Z.2.val _ _ _ _ hl hu hZ0 hleft (cellAt_node A)

/-- **The local law** of a real node of an old column. -/
theorem localLaw_old (hrun : Official.expandDiagram s n = .ok R) {Z Z' A : (Frame.ofMountain R).Node}
    (hx : Z.1.val < s.length - 1) (hZ : Real Z) (hZu : (Frame.ofMountain R).upper Z = some Z')
    (hraw : (Frame.ofMountain R).rawParent Z = some A) :
    (Frame.ofMountain R).height A ≤ (Frame.ofMountain R).height Z ∧
      (Frame.ofMountain R).height Z' =
        Row.B ((Frame.ofMountain R).height Z) ((Frame.ofMountain R).height A) := by
  obtain ⟨M, hM, hMs, hI, hB⟩ := run_basic hrun
  have hF := hB.valid.toOrdered
  have hNM : (Frame.ofMountain M).Normal := build_normal_of_legal (build_success_legal hM) hM
  have hG := hNM.toOrdered
  obtain ⟨up1, hUp, hLeft⟩ := rawParent_spec hraw
  rw [hZu] at hUp
  obtain rfl := Option.some.inj hUp
  obtain ⟨hc1, hc2⟩ := upper_spec hZu
  have hAZ : A.1.val < Z.1.val := rawParent_column_lt hF hraw
  have hag : ∀ c, c < M.size - 1 → R[c]? = M[c]? := hI.2.1
  obtain ⟨z, hz1, hz2, hzc⟩ := CrossUpper.twin_of_agree (hag _ (by omega)) Z rfl
  obtain ⟨z', hz'1, hz'2, hz'c⟩ := CrossUpper.twin_of_agree (hag _ (by rw [hc1]; omega)) Z' rfl
  obtain ⟨a, ha1, ha2, hac⟩ := CrossUpper.twin_of_agree (hag _ (by omega)) A rfl
  have hzu : (Frame.ofMountain M).upper z = some z' :=
    Classification.ControlProof.upper_eq_of_index (Fin.ext (by rw [hz1, hz'1, hc1]))
      (by rw [hz'2, hz2, hc2])
  have href : Frame.ref A = Frame.ref a := by
    change (⟨A.1.val, A.2.val⟩ : Ref) = ⟨a.1.val, a.2.val⟩
    rw [ha1, ha2]
  have hrawG : (Frame.ofMountain M).rawParent z = some a :=
    rawParent_eq_of_upper_left hzu (by rw [hz'c, hLeft, href])
  have hzr : Real z := by unfold Real at hZ ⊢; omega
  obtain ⟨p, hP, hrow, _, _⟩ := hNM.upper_step z z' hzr hzu
  have hpa : p = a := Option.some.inj (hP.symm.trans ((hNM.rawParent_eq_P hzr).symm.trans hrawG))
  subst hpa
  have eA : (Frame.ofMountain R).height A = (Frame.ofMountain M).height p := by
    change ((Frame.ofMountain R).cell A).row = ((Frame.ofMountain M).cell p).row
    rw [hac]
  have eU : (Frame.ofMountain R).height Z' = (Frame.ofMountain M).height z' := by
    change ((Frame.ofMountain R).cell Z').row = ((Frame.ofMountain M).cell z').row
    rw [hz'c]
  have eZ : (Frame.ofMountain R).height Z = (Frame.ofMountain M).height z := by
    change ((Frame.ofMountain R).cell Z).row = ((Frame.ofMountain M).cell z).row
    rw [hzc]
  refine ⟨?_, ?_⟩
  · rw [eA, eZ]; exact P_height_le hG hP
  · rw [eU, eZ, eA]; exact hrow

/-- **The local law** of a real node of the output. -/
theorem localLaw (hrun : Official.expandDiagram s n = .ok R) {Z Z' A : (Frame.ofMountain R).Node}
    (hZ : Real Z) (hZu : (Frame.ofMountain R).upper Z = some Z')
    (hraw : (Frame.ofMountain R).rawParent Z = some A) :
    (Frame.ofMountain R).height A ≤ (Frame.ofMountain R).height Z ∧
      (Frame.ofMountain R).height Z' =
        Row.B ((Frame.ofMountain R).height Z) ((Frame.ofMountain R).height A) := by
  by_cases hx : Z.1.val < s.length - 1
  · exact localLaw_old hrun hx hZ hZu hraw
  · exact localLaw_new hrun (by omega) hZ hZu hraw

/-- **The same parent.** Two real nodes of the output with the same row whose stored parents
are in the same column have the same stored parent, and the nodes above them have the same
row. -/
theorem same_parent (hrun : Official.expandDiagram s n = .ok R)
    {a b a' b' pa pb : (Frame.ofMountain R).Node} (ha : Real a) (hb : Real b)
    (hh : (Frame.ofMountain R).height a = (Frame.ofMountain R).height b)
    (hau : (Frame.ofMountain R).upper a = some a') (hbu : (Frame.ofMountain R).upper b = some b')
    (hpa : (Frame.ofMountain R).rawParent a = some pa)
    (hpb : (Frame.ofMountain R).rawParent b = some pb) (hc : pa.1 = pb.1) :
    pa = pb ∧ (Frame.ofMountain R).height a' = (Frame.ofMountain R).height b' := by
  obtain ⟨hla, hra⟩ := localLaw hrun ha hau hpa
  obtain ⟨hlb, hrb⟩ := localLaw hrun hb hbu hpb
  have HBa := CrossUpper.hb_run hrun a ha a' pa hau hpa
  have HBb := CrossUpper.hb_run hrun b hb b' pb hbu hpb
  have i1 : pa.2.val ≤ pb.2.val := HBb.2 pa hc (by
    rw [hrb]; exact lt_of_le_of_lt (hla.trans (le_of_eq hh)) (Row.lt_B _ _))
  have i2 : pb.2.val ≤ pa.2.val := HBa.2 pb hc.symm (by
    rw [hra]; exact lt_of_le_of_lt (hlb.trans (le_of_eq hh.symm)) (Row.lt_B _ _))
  have hpp : pa = pb := node_eq_of_index hc (by omega)
  subst hpp
  exact ⟨rfl, by rw [hra, hrb, hh]⟩

end Local

/-! ## `Lex` from the parent columns -/

/-- The parent columns along two columns compare (see the module doc). -/
def LegsOK (R : Mountain) (cz a cw b : Nat) : Nat → Prop
  | 0 => Reserve.cell? R ⟨cz, a + 1⟩ = none ∨
      ∃ p q, Reserve.rawParent R ⟨cz, a⟩ = some p ∧ Reserve.rawParent R ⟨cw, b⟩ = some q ∧
        p.column < q.column
  | K + 1 => ∃ p q, Reserve.rawParent R ⟨cz, a⟩ = some p ∧ Reserve.rawParent R ⟨cw, b⟩ = some q ∧
      p.column = q.column ∧ LegsOK R cz (a + 1) cw (b + 1) K

theorem upper_none_of_cell {R : Mountain} {z : (Frame.ofMountain R).Node}
    (h : Reserve.cell? R ⟨z.1.val, z.2.val + 1⟩ = none) : (Frame.ofMountain R).upper z = none := by
  cases hu : (Frame.ofMountain R).upper z with
  | none => rfl
  | some z' =>
    exfalso
    have hc := LowerChainRecon.cell?_ref z'
    rw [LowerChainRecon.above_of_upper hu] at hc
    simp only [Classification.Proofs.ChainCorr.LowerChain.above, Frame.ref] at hc
    rw [hc] at h
    cases h

theorem rawParent_nodes {R : Mountain} (hF : (Frame.ofMountain R).Ordered)
    {z : (Frame.ofMountain R).Node} {p : Ref}
    (h : Reserve.rawParent R (Frame.ref z) = some p) :
    ∃ z' P, (Frame.ofMountain R).upper z = some z' ∧ (Frame.ofMountain R).rawParent z = some P ∧
      Frame.ref P = p := by
  rw [Classification.ControlProof.rawParent_ref] at h
  cases hup : (Frame.ofMountain R).upper z with
  | none => rw [hup] at h; cases h
  | some z' =>
    rw [hup, Option.bind_some] at h
    obtain ⟨P, hPl, _, _⟩ := hF.stored_valid z' p h
    have hPr : Frame.ref P = p := lookup_spec hPl
    exact ⟨z', P, rfl, rawParent_eq_of_upper_left hup (by rw [hPr]; exact h), hPr⟩

/-- **`Lex` from the parent columns.** -/
theorem lex_of_legs {s : List Nat} {n : Nat} {R : Mountain}
    (hrun : Official.expandDiagram s n = .ok R) (hF : (Frame.ofMountain R).Ordered) :
    ∀ (K a b cz cw : Nat), LegsOK R cz a cw b K →
      ∀ z w : (Frame.ofMountain R).Node, Frame.ref z = ⟨cz, a⟩ → Frame.ref w = ⟨cw, b⟩ →
        Real z → Real w → (Frame.ofMountain R).height z = (Frame.ofMountain R).height w →
        Lex (Frame.ofMountain R) z w := by
  intro K
  induction K with
  | zero =>
    intro a b cz cw hL z w hz hw _ _ _
    rcases hL with hnone | ⟨p, q, hp, hq, hlt⟩
    · apply Lex.top
      apply upper_none_of_cell
      have h1 : z.1.val = cz := congrArg Ref.column hz
      have h2 : z.2.val = a := congrArg Ref.index hz
      rw [h1, h2]; exact hnone
    · rw [← hz] at hp
      rw [← hw] at hq
      obtain ⟨_, P, _, hP, hPr⟩ := rawParent_nodes hF hp
      obtain ⟨_, Q, _, hQ, hQr⟩ := rawParent_nodes hF hq
      refine Lex.left hP hQ ?_
      have e1 : P.1.val = p.column := by rw [← hPr]; rfl
      have e2 : Q.1.val = q.column := by rw [← hQr]; rfl
      omega
  | succ K ih =>
    intro a b cz cw hL z w hz hw hzr hwr hh
    obtain ⟨p, q, hp, hq, hpq, hL'⟩ := hL
    rw [← hz] at hp
    rw [← hw] at hq
    obtain ⟨z', P, hzu, hP, hPr⟩ := rawParent_nodes hF hp
    obtain ⟨w', Q, hwu, hQ, hQr⟩ := rawParent_nodes hF hq
    have hc : P.1 = Q.1 := by
      apply Fin.ext
      have e1 : P.1.val = p.column := by rw [← hPr]; rfl
      have e2 : Q.1.val = q.column := by rw [← hQr]; rfl
      omega
    obtain ⟨hPQ, hh'⟩ := same_parent hrun hzr hwr hh hzu hwu hP hQ hc
    subst hPQ
    refine Lex.same hzu hwu hP hQ hh' (ih (a + 1) (b + 1) cz cw hL' z' w' ?_ ?_
      (real_of_upper hzu) (real_of_upper hwu) hh')
    · rw [LowerChainRecon.above_of_upper hzu, hz]; rfl
    · rw [LowerChainRecon.above_of_upper hwu, hw]; rfl

end OmegaY.Official.Recon.RPLLex

#print axioms OmegaY.Official.Recon.RPLLex.same_parent
#print axioms OmegaY.Official.Recon.RPLLex.lex_of_legs
