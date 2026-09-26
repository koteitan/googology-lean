/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/JumpLawAscend.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
Port change: in `refRow_node` a hypothesis is beta-reduced before a rewrite.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawUpper
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.RowShadow
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.WeakParentPaths

set_option backward.do.legacy false

/-!
# Ascension along the leg of an edge

The ascension test `Official.ascends` follows in-row parents (`Expansion.weakParent`) from
the node at the reference row until the column is at most `c_r` (`reachesRoot`).

For an edge `u → u⁺` of a canonical column `x` with leg `l` and parent row `p`, Phyrion's
row shadow (`Canonical.build_P_rowShadow`) says: every node `w` of the column `l` at a row
`≤ p` is reached from the node of `x` at the same row by in-row parents
(`source_shadow`, as an executable `ForwardWeakPath`). Hence `reachesRoot` from that node of
`x` passes through `w` (`reach_path`):

* `ascends_of_leg`: if the leg column `l > c_r` ascends in a region whose reference row is at
  most `p`, so does `x`;
* `ascends_of_root_leg`: if the leg is the root column itself, `x` ascends in every region
  whose reference row is a row of `c_r` at most `p`.
-/

namespace OmegaY.Official.Recon.JumpLaw

open Canonical Expansion Dimension RowLaw Geometry Reserve

/-! ## `reachesRoot` along weak paths -/

theorem reachesRoot_mono {M : Mountain} {cr : Nat} :
    ∀ (f : Nat) (a : Ref) (b : Bool), reachesRoot M cr f a = .ok b →
      ∀ f', f ≤ f' → reachesRoot M cr f' a = .ok b
  | 0, _, _, h, _, _ => by simp [reachesRoot, throw, throwThe, MonadExceptOf.throw] at h
  | f + 1, a, b, h, f', hf => by
    obtain ⟨f'', rfl⟩ : ∃ f'', f' = f'' + 1 := ⟨f' - 1, by omega⟩
    unfold reachesRoot at h ⊢
    split
    · rename_i hc
      rw [if_pos hc] at h
      exact h
    · rename_i hc
      rw [if_neg hc] at h
      simp only [bind, Except.bind] at h ⊢
      cases hw : liftE (Expansion.weakParent M a) with
      | error e => rw [hw] at h; cases h
      | ok r =>
        rw [hw] at h
        simp only at h ⊢
        cases r with
        | none => exact h
        | some p => exact reachesRoot_mono f p b h f'' (by omega)

theorem forwardWeakPath_column_le {M : Mountain} {w : Ref} :
    ∀ {v : Ref}, ForwardWeakPath M w v → w.column ≤ v.column
  | _, .root => le_rfl
  | _, .step prev edge => by
    have h1 := forwardWeakPath_column_le prev
    obtain ⟨_, _, _, _, _, _, _, _, hlt, _, _⟩ := edge
    omega

/-- **`reachesRoot` along a weak path.** -/
theorem reach_path {M : Mountain} {cr : Nat} {w : Ref} (hw : cr ≤ w.column) {fw : Nat}
    (hwr : reachesRoot M cr fw w = .ok true) :
    ∀ {v : Ref}, ForwardWeakPath M w v → ∀ f, fw + (v.column - w.column) ≤ f →
      reachesRoot M cr f v = .ok true
  | _, .root, f, hf => reachesRoot_mono fw w true hwr f (by omega)
  | current, .step (parent := parent) prev edge, f, hf => by
    have hpw := forwardWeakPath_column_le prev
    have hedge := edge
    obtain ⟨_, _, _, _, _, _, _, _, hlt, _, _⟩ := hedge
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have ih := reach_path hw hwr prev f' (by omega)
    unfold reachesRoot
    rw [if_neg (by omega)]
    have hwp : Expansion.weakParent M current = .ok (some parent) := weakParent_iff_twoLeg.mpr edge
    simp only [bind, Except.bind, liftE, Except.mapError, hwp]
    exact ih

/-! ## The row shadow of an edge -/

/-- **Row shadow of a canonical edge.** Every node of the leg column at a row at most the
parent row is reached, through in-row parents, from the node of the column at the same row. -/
theorem source_shadow {s : List Nat} {M : Mountain} (hb : build s = .ok M) {c : Nat}
    {q : Ref × Cell} (hq : q ∈ realNodes M c) (hθ : official q.2.row ≠ 0) {l : Nat} {ps : Row}
    (hl : leftColumn q.2 = .ok l) (hps : HighestBelow (rowsOf M l) (official q.2.row) ps)
    {w : Ref × Cell} (hw : w ∈ realNodes M l) (hwle : official w.2.row ≤ ps) :
    ∃ v ∈ realNodes M c, official v.2.row = official w.2.row ∧ ForwardWeakPath M w.1 v.1 := by
  have hV := build_valid_of_success hb
  have hN := build_normal_of_success hb
  have hO := hN.toOrdered
  obtain ⟨col, j, hcol, hcell, hq1⟩ := mem_realNodes_iff.mp hq
  obtain ⟨hcs, hcolEq⟩ := Array.getElem?_eq_some_iff.mp hcol
  have hCV : ColumnValid M c col := hcolEq ▸ hV c hcs
  have hj : 1 ≤ j := by
    by_contra hn
    have h0 : j = 0 := by omega
    subst h0
    apply hθ
    rw [hCV.bottom_row q.2 hcell]
    exact official_one
  have hjlt : j + 1 < col.size := (Array.getElem?_eq_some_iff.mp hcell).1
  -- the stored leg
  obtain ⟨ref, hleft⟩ : ∃ ref, q.2.left = some ref := by
    cases h : q.2.left with
    | some r => exact ⟨r, rfl⟩
    | none =>
      simp [leftColumn, Expansion.leftOf, h, liftE, Except.mapError, bind, Except.bind] at hl
  rw [leftColumn_of hleft] at hl
  obtain rfl := Except.ok.inj hl
  -- frame nodes of the edge
  have hcs' : c < M.size := hcs
  have hjs : j < M[c].size := by rw [hcolEq]; omega
  have hj1s : j + 1 < M[c].size := by rw [hcolEq]; omega
  let nu : (Frame.ofMountain M).Node := ⟨⟨c, hcs'⟩, ⟨j, hjs⟩⟩
  let nv : (Frame.ofMountain M).Node := ⟨⟨c, hcs'⟩, ⟨j + 1, hj1s⟩⟩
  have hup : (Frame.ofMountain M).upper nu = some nv :=
    Classification.ControlProof.upper_eq_of_index rfl rfl
  have hnvcell : (Frame.ofMountain M).cell nv = q.2 := by
    show M[c][j + 1] = q.2
    have := hcell
    rw [← hcolEq] at this
    exact Option.some.inj ((Array.getElem?_eq_getElem hj1s).symm.trans this)
  have hleft' : ((Frame.ofMountain M).cell nv).left = some ref := by rw [hnvcell]; exact hleft
  obtain ⟨np, hlk, _, _⟩ := hO.stored_valid nv ref hleft'
  have hnp : Frame.ref np = ref := Frame.lookup_spec hlk
  have hleft'' : ((Frame.ofMountain M).cell nv).left = some (Frame.ref np) := by
    rw [hnp]; exact hleft'
  have hrawF : (Frame.ofMountain M).rawParent nu = some np :=
    Frame.rawParent_eq_of_upper_left hup hleft''
  have hP : (Frame.ofMountain M).P nu = some np :=
    (hN.rawParent_eq_P (show Frame.Real nu from hj)).symm.trans hrawF
  have hshadow := Canonical.build_P_rowShadow (build_success_legal hb) hb hP
  -- the parent row is `ps`
  obtain ⟨σ, l', ps', _, _, _, hl', _, hHB', _, _⟩ := source_edge hb hq hθ
  rw [leftColumn_of hleft] at hl'
  obtain rfl := Except.ok.inj hl'
  obtain rfl := highestBelow_unique hps hHB'
  -- the parent cell and its official row
  have hpcell : cell? M ref = some ((Frame.ofMountain M).cell np) := by
    rw [← hnp]; exact Classification.ControlProof.cell?_ref np
  have hvcell : cell? M ⟨c, j + 1⟩ = some q.2 := by simp [cell?, hcol, hcell]
  have hraw : rawParent M ⟨c, j⟩ = some ref := by simp [rawParent, hcol, hcell, hleft]
  obtain ⟨cp, hcp, hcplt, hcpmax⟩ := Classification.Proofs.canonical_rawParent_highest_below
    (build_success_legal hb) hb hvcell hraw
  rw [hpcell] at hcp
  obtain rfl := Option.some.inj hcp
  -- the parent column
  have hrs : ref.column < M.size := by have := np.1.isLt; rw [← hnp]; exact this
  obtain ⟨cq, hcq⟩ : ∃ cq, M[ref.column]? = some cq :=
    ⟨M[ref.column], Array.getElem?_eq_getElem hrs⟩
  have hCVq : ColumnValid M ref.column cq := by
    have := hV ref.column hrs
    rwa [(Array.getElem?_eq_some_iff.mp hcq).2] at this
  have hpc' : cq[ref.index]? = some ((Frame.ofMountain M).cell np) := by
    simpa [cell?, hcq] using hpcell
  have hq1r : (1 : Row) ≤ q.2.row := realNodes_row_one_le hV hq
  have hlowlt : col[j].row < q.2.row := hCV.rows_strict _ _ _ _
    (Array.getElem?_eq_getElem (by omega)) hcell (by omega)
  have hlow1 : (1 : Row) ≤ col[j].row :=
    row_one_le_of_ne_zero (ne_of_gt (hCV.rows_strict 0 j phantom _ hCV.phantom
      (Array.getElem?_eq_getElem (by omega)) (by omega)))
  have hidx : 1 ≤ ref.index := by
    obtain ⟨b1, hb1⟩ : ∃ b1, cq[1]? = some b1 :=
      ⟨cq[1]'(by have := hCVq.size_ge_two; omega),
        Array.getElem?_eq_getElem (by have := hCVq.size_ge_two; omega)⟩
    exact hcpmax 1 b1 (by simp [cell?, hcq, hb1]) (by
      rw [hCVq.bottom_row b1 hb1]; exact lt_of_le_of_lt hlow1 hlowlt)
  have hmem : (ref, (Frame.ofMountain M).cell np) ∈ realNodes M ref.column := by
    refine mem_realNodes_iff.mpr ⟨cq, ref.index - 1, hcq, ?_, ?_⟩
    · rw [show ref.index - 1 + 1 = ref.index by omega]
      exact hpc'
    · cases ref; simp only [Ref.mk.injEq, true_and]; simp at hidx; omega
  have hcp1 : (1 : Row) ≤ ((Frame.ofMountain M).cell np).row := realNodes_row_one_le hV hmem
  -- `ps` is the official row of the parent
  have hpsrow : ps = official ((Frame.ofMountain M).cell np).row := by
    apply highestBelow_unique hHB'
    refine ⟨List.mem_map.mpr ⟨_, hmem, rfl⟩, official_strictMono hcp1 hcplt, ?_⟩
    intro r hr hrθ
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hr
    obtain ⟨col', j', hcol', hcell', _⟩ := mem_realNodes_iff.mp hq'
    have hq'r : (1 : Row) ≤ q'.2.row := realNodes_row_one_le hV hq'
    have hlt : q'.2.row < q.2.row := by
      by_contra hn
      exact absurd hrθ (not_lt.mpr (official_mono hq1r (not_lt.mp hn)))
    have hjj := hcpmax (j' + 1) q'.2 (by simp [cell?, hcol', hcell']) hlt
    apply official_mono hq'r
    have hcc : cq = col' := Option.some.inj (hcq.symm.trans hcol')
    subst hcc
    rcases Nat.eq_or_lt_of_le hjj with he | hlt'
    · rw [he] at hcell'
      rw [Option.some.inj (hcell'.symm.trans hpc')]
    · exact (hCVq.rows_strict _ _ _ _ hcell' hpc' hlt').le
  -- the frame node of `w`
  obtain ⟨wcol, wk, hwcol, hwcell, hw1⟩ := mem_realNodes_iff.mp hw
  have hwcs : ref.column < M.size := (Array.getElem?_eq_some_iff.mp hwcol).1
  have hwk : wk + 1 < M[ref.column].size := by
    rw [(Array.getElem?_eq_some_iff.mp hwcol).2]; exact (Array.getElem?_eq_some_iff.mp hwcell).1
  let nw : (Frame.ofMountain M).Node := ⟨⟨ref.column, hwcs⟩, ⟨wk + 1, hwk⟩⟩
  have hnwcell : (Frame.ofMountain M).cell nw = w.2 := by
    show M[ref.column][wk + 1] = w.2
    have := hwcell
    rw [← (Array.getElem?_eq_some_iff.mp hwcol).2] at this
    exact Option.some.inj ((Array.getElem?_eq_getElem hwk).symm.trans this)
  have hnwReal : Frame.Real nw := by show 0 < wk + 1; omega
  have hnwcol : nw.1 = np.1 := by
    apply Fin.ext
    show ref.column = np.1.val
    rw [← hnp]; rfl
  have hheight : (Frame.ofMountain M).height nw ≤ (Frame.ofMountain M).height np := by
    unfold Frame.height
    rw [hnwcell]
    by_contra hn
    have := official_strictMono hcp1 (lt_of_not_ge hn)
    rw [← hpsrow] at this
    exact absurd hwle (not_le.mpr this)
  obtain ⟨v, hvReal, hvcol, _, hvh, hpath⟩ := hshadow nw hnwReal hnwcol hheight
  have hfwp := (forwardWeakPath_iff_same_row_parentPath hN hnwReal).mpr ⟨hpath, hvh⟩
  refine ⟨(Frame.ref v, (Frame.ofMountain M).cell v), ?_, ?_, ?_⟩
  · have hv1 : v.1.val = c := by rw [hvcol]
    refine mem_realNodes_iff.mpr ⟨col, v.2.val - 1, hcol, ?_, ?_⟩
    · rw [show v.2.val - 1 + 1 = v.2.val by unfold Frame.Real at hvReal; omega]
      have := Classification.ControlProof.cell?_ref v
      simp only [cell?, Frame.ref, hv1, hcol, Option.bind_eq_bind, Option.bind_some] at this
      exact this
    · simp only [Frame.ref, Ref.mk.injEq, hv1, true_and]
      unfold Frame.Real at hvReal; omega
  · show official ((Frame.ofMountain M).height v) = official w.2.row
    rw [hvh]
    unfold Frame.height
    rw [hnwcell]
  · have hrefw : Frame.ref nw = w.1 := by
      rw [hw1]; rfl
    rw [← hrefw]
    exact hfwp

end OmegaY.Official.Recon.JumpLaw

namespace OmegaY.Official.Recon.JumpLaw

open Canonical Expansion Dimension RowLaw Geometry Reserve

/-! ## Ascension transfer -/

theorem official_inj_of_one_le {a b : Row} (ha : (1 : Row) ≤ a) (hb : (1 : Row) ≤ b)
    (h : official a = official b) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (ne_of_lt (official_strictMono ha hab))
  · exact hab
  · exact absurd h.symm (ne_of_lt (official_strictMono hb hab))

/-- Two nodes of a canonical column with the same official row are equal. -/
theorem realNodes_eq_of_row {s : List Nat} {M : Mountain} (hb : build s = .ok M) {c : Nat}
    {p q : Ref × Cell} (hp : p ∈ realNodes M c) (hq : q ∈ realNodes M c)
    (h : official p.2.row = official q.2.row) : p = q := by
  have hV := build_valid_of_success hb
  have hrow := official_inj_of_one_le (realNodes_row_one_le hV hp) (realNodes_row_one_le hV hq) h
  apply realNodes_index_eq hp hq
  rcases Nat.lt_trichotomy p.1.index q.1.index with hlt | he | hlt
  · have := realNodes_row_le hV hp hq hlt.le
    have h2 : p.2.row < q.2.row := by
      obtain ⟨col, k, hc, hk, hp1⟩ := mem_realNodes_iff.mp hp
      obtain ⟨col', k', hc', hk', hq1⟩ := mem_realNodes_iff.mp hq
      have hcc : col = col' := Option.some.inj (hc.symm.trans hc')
      subst hcc
      obtain ⟨hcs, hcolEq⟩ := Array.getElem?_eq_some_iff.mp hc
      have hCV : ColumnValid M c col := hcolEq ▸ hV c hcs
      rw [hp1, hq1] at hlt
      exact hCV.rows_strict _ _ _ _ hk hk' (by simpa using hlt)
    rw [hrow] at h2
    exact absurd h2 (lt_irrefl _)
  · exact he
  · have h2 : q.2.row < p.2.row := by
      obtain ⟨col, k, hc, hk, hp1⟩ := mem_realNodes_iff.mp hp
      obtain ⟨col', k', hc', hk', hq1⟩ := mem_realNodes_iff.mp hq
      have hcc : col = col' := Option.some.inj (hc.symm.trans hc')
      subst hcc
      obtain ⟨hcs, hcolEq⟩ := Array.getElem?_eq_some_iff.mp hc
      have hCV : ColumnValid M c col := hcolEq ▸ hV c hcs
      rw [hp1, hq1] at hlt
      exact hCV.rows_strict _ _ _ _ hk' hk (by simpa using hlt)
    rw [hrow] at h2
    exact absurd h2 (lt_irrefl _)

theorem nodeAt_eq_of_mem {s : List Nat} {M : Mountain} (hb : build s = .ok M) {c : Nat}
    {v : Ref × Cell} (hv : v ∈ realNodes M c) : nodeAt M c (official v.2.row) = some v := by
  obtain ⟨p, hp⟩ := nodeAt_of_mem hv
  obtain ⟨hpm, hprow⟩ := nodeAt_spec hp
  rw [hp, realNodes_eq_of_row hb hpm hv hprow]

/-- **Ascension along a leg `l > c_r`.** -/
theorem ascends_of_leg {s : List Nat} {M : Mountain} (hb : build s = .ok M)
    {ctxX ctxY : Context} (hsX : ctxX.source = M) (hsY : ctxY.source = M)
    (hroot : ctxX.rootColumn = ctxY.rootColumn)
    {q : Ref × Cell} (hq : q ∈ realNodes M ctxX.x) (hθ : official q.2.row ≠ 0) {l : Nat} {ps : Row}
    (hl : leftColumn q.2 = .ok l) (hps : HighestBelow (rowsOf M l) (official q.2.row) ps)
    (hY : ctxY.x = l) (hlcr : ctxY.rootColumn ≤ l) {rho : Option (Ref × Cell)}
    (hZ : ∀ ρ, rho = some ρ → referenceRow (official ρ.2.row) < official q.2.row)
    (hasc : ascends ctxY rho = .ok true) : ascends ctxX rho = .ok true := by
  unfold ascends at hasc ⊢
  cases hrho : rho with
  | none => rw [hrho] at hasc; cases hasc
  | some ρ =>
    obtain ⟨ρref, ρc⟩ := ρ
    rw [hrho] at hasc
    simp only at hasc ⊢
    have hZ' := hZ _ hrho
    simp only at hZ'
    cases hn : nodeAt ctxY.source ctxY.x (referenceRow (official ρc.row)) with
    | none => rw [hn] at hasc; cases hasc
    | some w =>
      rw [hn] at hasc
      obtain ⟨wref, wc⟩ := w
      simp only at hasc
      obtain ⟨hwm, hwrow⟩ := nodeAt_spec hn
      rw [hsY, hY] at hwm
      simp only at hwrow hwm
      have hwle : official wc.row ≤ ps :=
        hps.2.2 _ (List.mem_map.mpr ⟨_, hwm, rfl⟩) (by rw [hwrow]; exact hZ')
      obtain ⟨v, hv, hvrow, hpath⟩ := source_shadow hb hq hθ hl hps hwm hwle
      have hnv := nodeAt_eq_of_mem hb hv
      rw [hvrow, hwrow] at hnv
      rw [hsX, hnv]
      simp only
      have hwcol : wref.column = l := (realNodes_column hwm).1
      have hvcol : v.1.column = ctxX.x := (realNodes_column hv).1
      rw [hsY, hY] at hasc
      rw [hroot]
      have hlx : l < ctxX.x := by
        obtain ⟨_, l', _, _, _, _, hl', hlc, _⟩ := source_edge hb hq hθ
        rw [hl] at hl'
        obtain rfl := Except.ok.inj hl'
        exact hlc
      apply reach_path (fw := l + 1) (by rw [hwcol]; exact hlcr) hasc hpath
      omega

/-- The reference row of a node is a row of its column, at most its row. -/
theorem refRow_node {s : List Nat} {M : Mountain} (hb : build s = .ok M) {c : Nat}
    {ρ : Ref × Cell} (hρ : ρ ∈ realNodes M c) :
    ∃ w ∈ realNodes M c, official w.2.row = referenceRow (official ρ.2.row) ∧
      official w.2.row ≤ official ρ.2.row := by
  by_cases h0 : 0 < (official ρ.2.row).coeff 0
  · have hne : official ρ.2.row ≠ 0 := by
      intro h; rw [h] at h0; simp at h0
    obtain ⟨σ, _, ps, hσmem, hσlt, _, _, _, _, _, hθ⟩ := source_edge hb hρ hne
    have he : Row.jump σ ps = 0 := by
      by_contra hn
      have := congrArg (fun r : Row => r.coeff 0) hθ
      beta_reduce at this
      rw [Row.coeff_bump_low (show 0 < Row.jump σ ps by omega)] at this
      omega
    rw [he] at hθ
    have hbump := referenceRow_bump h0
    rw [hθ] at hbump
    have hσ : referenceRow (Row.bump σ 0) = σ := by
      have := (bump_eq_bump hbump).2
      exact Row.jump_eq_zero.mp (by omega)
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hσmem
    refine ⟨w, hw, ?_, hσlt.le⟩
    rw [hθ, hσ]
  · refine ⟨ρ, hρ, ?_, le_rfl⟩
    unfold referenceRow
    rw [if_neg h0]

/-- **Ascension along the root leg.** -/
theorem ascends_of_root_leg {s : List Nat} {M : Mountain} (hb : build s = .ok M)
    {ctxX : Context} (hsX : ctxX.source = M)
    {q : Ref × Cell} (hq : q ∈ realNodes M ctxX.x) (hθ : official q.2.row ≠ 0) {ps : Row}
    (hl : leftColumn q.2 = .ok ctxX.rootColumn)
    (hps : HighestBelow (rowsOf M ctxX.rootColumn) (official q.2.row) ps)
    {ρ : Ref × Cell} (hρ : ρ ∈ realNodes M ctxX.rootColumn) (hρps : official ρ.2.row ≤ ps) :
    ascends ctxX (some ρ) = .ok true := by
  obtain ⟨w, hw, hwrow, hwle⟩ := refRow_node hb hρ
  obtain ⟨v, hv, hvrow, hpath⟩ := source_shadow hb hq hθ hl hps hw (hwle.trans hρps)
  have hnv := nodeAt_eq_of_mem hb hv
  rw [hvrow, hwrow] at hnv
  unfold ascends
  obtain ⟨ρref, ρc⟩ := ρ
  simp only at hnv ⊢
  rw [hsX, hnv]
  simp only
  have hwcol : w.1.column = ctxX.rootColumn := (realNodes_column hw).1
  have hlx : ctxX.rootColumn < ctxX.x := by
    obtain ⟨_, l', _, _, _, _, hl', hlc, _⟩ := source_edge hb hq hθ
    rw [hl] at hl'
    obtain rfl := Except.ok.inj hl'
    exact hlc
  have hvcol : v.1.column = ctxX.x := (realNodes_column hv).1
  apply reach_path (fw := 1) (by rw [hwcol]) _ hpath
  · omega
  · unfold reachesRoot
    rw [if_pos (by omega)]
    simp [hwcol, pure, Except.pure]

end OmegaY.Official.Recon.JumpLaw
