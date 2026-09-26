/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/TSQAscUp.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TSQPaO
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.LiftLegRightProof

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `AscUp` from a value inequality about `M(s)` (`TSQ`)

`AscUp` (`TSQPaO.lean`, about `M(s)` alone): for `o = (x, C)` (`c_r < x ≤ x₀`, below `row t`) with
its leg `l > c_r`, a node `pa = (l, C)`, a node `o⁺` above `o` below `row t` and a node
`g = (c_r, C)`: if `l` passes the ascension test of `C`, so does `x`.

* **Finite coefficient of `C` positive** (`ascUp_pos`, proved): the reference row is `Z = C - 1`,
  the node `w = (x, Z)` below `o` exists (the row law: `row o = B(row w, row P(w))` has a
  positive finite coefficient only if `P(w)` is at the row of `w`), its in-row parent is
  `P(w) = (l, Z)` (the left end of `o`), and the test from `x` continues as the test from `l`.
* **Finite coefficient of `C` zero** (`ascUp_zero`): the test from `x` starts at `o` itself. The
  candidate of `o⁺` is `Q(o) = pa`, and the parent `P(o)` is the first node of the search from
  `pa` with a value below `v(o)`. The test from `l` is a path of numerical parents at the row
  `C` from `pa` to `g` (`LiftLegPf.reach_path`). If `v(g) < v(o)`, the search stops on this path
  (`hit_before`), so `P(o)` is on it, at the row `C`, and the test from `x` follows the path to
  `g`. The inequality `v(g) < v(o)` is the open statement
  - `RootValue` (**open**, about `M(s)` alone, numerically checked).

  Without the node `o⁺` the value of `o` is `1` and the inequality fails; this is the known
  counterexample of `TopStartLoRight`. For a column `c` other than the root column the
  inequality fails in general (the search may skip `(c, C)`), so `RootValue` is a property of
  the root column of the last column.

Results: `hit_before`, `ascUp_of_rootValue : RootValue → AscUp`,
`topStartPaOUp_of_rootValue : RootValue → TopStartPaOUp`.
-/

namespace OmegaY.Official.Recon.TSQ

open Canonical Expansion Classification Reserve
open OmegaY.Geometry OmegaY.Geometry.Frame

/-- **Open (about `M(s)` alone).** In the setting of `AscUp` with a zero finite coefficient of
`C` (so the ascension test of `C` starts at the node of the row `C` itself), if the test from
`pa = (l, C)` passes, the node `g = (c_r, C)` has a smaller value than `o`. -/
def RootValue : Prop :=
  ∀ (s : List Nat) (M : Mountain) (t : Cell) (root : Ref), Recon.Top s M t root →
    ∀ (x k : Nat) (co : Cell) (l : Ref), root.column < x → x ≤ M.size - 1 → 1 ≤ k →
      Reserve.cell? M ⟨x, k⟩ = some co → co.row < t.row → co.left = some l →
      root.column < l.column →
      (∃ c', Reserve.cell? M ⟨x, k + 1⟩ = some c' ∧ c'.row < t.row) →
      referenceRow (official co.row) = official co.row →
      ∀ pa cpa, Reserve.highestAtMost M l.column co.row = some pa →
        Reserve.cell? M pa = some cpa → cpa.row = co.row →
        reachesRoot M root.column (l.column + 1) pa = .ok true →
      ∀ g cg, g.column = root.column → Reserve.cell? M g = some cg → cg.row = co.row →
        cg.value < co.value

/-! ## The search stops on a parent path -/

/-- **A search that meets a node of small value on a parent path stops before it.** If the
numerical parents lead from `q` to `g` and `0 < v(g) < θ`, the first hit of the search from `q`
with threshold `θ` is on this path (the rest of the path leads from it to `g`). -/
theorem hit_before {F : Frame} (hF : F.Ordered) {θ : Nat} :
    ∀ {q g : F.Node}, ParentPath F q g → 0 < F.value g → F.value g < θ →
      ∀ {p : F.Node}, Hit F θ q p → ParentPath F p g := by
  intro q g hpath
  induction hpath with
  | refl u =>
    intro hg0 hgθ p h
    cases h with
    | here _ _ => exact .refl _
    | next hrej _ _ => exact absurd ⟨hg0, hgθ⟩ hrej
  | @cons u q1 g hP rest ih =>
    intro hg0 hgθ p h
    cases h with
    | here _ _ => exact .cons hP rest
    | @next _ y' _ hrej hQ hrest =>
      have hv := P_value hF hP
      have hθu : θ ≤ F.value u := by
        by_contra hn
        exact hrej ⟨lt_trans hv.1 hv.2, lt_of_not_ge hn⟩
      obtain ⟨r, h1, h2⟩ := hrest.loosen hθu
      have hPr : F.P u = some r := (P_iff hF).mpr ⟨y', hQ, h1⟩
      have hr : r = q1 := Option.some.inj (hPr.symm.trans hP)
      subst hr
      exact ih hg0 hgθ h2

/-! ## Rows -/

theorem bump0_inj {a b : Row} (h : Row.bump a 0 = Row.bump b 0) : a = b := by
  apply Recon.row_ext
  intro i
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have h1 := congrArg (fun r : Row => r.coeff 0) h
    simp only [Recon.RowLaw.bump_coeff_at] at h1
    omega
  · have h1 := congrArg (fun r : Row => r.coeff i) h
    simp only [Recon.RowLaw.bump_coeff_high hi] at h1
    exact h1

/-! ## The two cases -/

variable {M : Mountain}

theorem ref_inj' {u v : (Frame.ofMountain M).Node} (h : Frame.ref u = Frame.ref v) : u = v := by
  have h1 : u.1 = v.1 := Fin.ext (congrArg Ref.column h)
  exact ControlProof.node_eq_of_index h1 (congrArg Ref.index h)

/-- **`AscUp` when the finite coefficient of `C` is positive** (no value inequality needed). -/
theorem ascUp_pos {s : List Nat} (hb : Canonical.build s = .ok M) {cr x k : Nat} {co : Cell}
    {l : Ref} (hcx : cr < x) (hk : 1 ≤ k) (hco : Reserve.cell? M ⟨x, k⟩ = some co)
    (hl : co.left = some l) (h0 : 0 < (official co.row).coeff 0) {ref' : Ref} {cl' : Cell}
    (hn' : nodeAt M l.column (referenceRow (official co.row)) = some (ref', cl'))
    (hr' : reachesRoot M cr (l.column + 1) ref' = .ok true) :
    ∃ ref cl, nodeAt M x (referenceRow (official co.row)) = some (ref, cl) ∧
      reachesRoot M cr (x + 1) ref = .ok true := by
  have hN := build_normal_of_success hb
  have hO := hN.toOrdered
  have hV := build_valid_of_success hb
  obtain ⟨oN, hoN, hocell⟩ := ControlProof.node_of_cell? hco
  have hoc : oN.1.val = x := congrArg Ref.column hoN
  have hoi : oN.2.val = k := congrArg Ref.index hoN
  have hoR : Real oN := by show 0 < oN.2.val; omega
  have hoh : (Frame.ofMountain M).height oN = co.row := by
    show ((Frame.ofMountain M).cell oN).row = co.row; rw [hocell]
  have hco1 : (1 : Row) ≤ co.row := by rw [← hoh]; exact one_le_height hO hoR
  -- `o` is not the bottom node
  have hlen1 : 1 < (Frame.ofMountain M).length oN.1 := by have := hO.length_ge_two oN.1; omega
  let bN : (Frame.ofMountain M).Node := ⟨oN.1, ⟨1, hlen1⟩⟩
  have hbR : Real bN := by show 0 < 1; omega
  have hbh : (Frame.ofMountain M).height bN = 1 := hO.bottom_row oN.1 hlen1
  have hblt : (Frame.ofMountain M).height bN < (Frame.ofMountain M).height oN := by
    rw [hbh]
    rcases lt_or_eq_of_le (show (1 : Row) ≤ (Frame.ofMountain M).height oN by
      rw [hoh]; exact hco1) with h | h
    · exact h
    · exfalso
      rw [hoh] at h
      rw [← h, Classification.official_one] at h0
      simp at h0
  obtain ⟨wN, hwR, hwu, hwc, _⟩ := real_lower_of_height_lt hO hbR hblt
  obtain ⟨pN, hP, hrowB, _, hleft⟩ := hN.upper_step wN oN hwR hwu
  have hlp : l = Frame.ref pN := by
    have h1 : ((Frame.ofMountain M).cell oN).left = some l := by rw [hocell]; exact hl
    exact Option.some.inj (h1.symm.trans hleft)
  -- the row law: `P(w)` is at the row of `w`
  have hw1 : (1 : Row) ≤ (Frame.ofMountain M).height wN := one_le_height hO hwR
  have hjump : Row.jump ((Frame.ofMountain M).height wN) ((Frame.ofMountain M).height pN) = 0 := by
    by_contra hne
    have hpos : 0 < Row.jump ((Frame.ofMountain M).height wN) ((Frame.ofMountain M).height pN) :=
      Nat.pos_of_ne_zero hne
    rw [hoh, Row.B] at hrowB
    rw [hrowB, Recon.RowLaw.official_bump hw1, Recon.RowLaw.bump_coeff_low hpos] at h0
    exact lt_irrefl _ h0
  have hph : (Frame.ofMountain M).height pN = (Frame.ofMountain M).height wN :=
    (Row.jump_eq_zero.mp hjump).symm
  have hrow0 : co.row = Row.bump ((Frame.ofMountain M).height wN) 0 := by
    rw [← hoh, hrowB, hph, Row.B_self]
  have hZ : referenceRow (official co.row) = official ((Frame.ofMountain M).height wN) := by
    apply bump0_inj
    rw [Recon.RowLaw.referenceRow_bump h0, hrow0, Recon.RowLaw.official_bump hw1]
  -- the nodes at the reference row
  have hwx : wN.1.val = x := by rw [hwc]; exact hoc
  have hnw : nodeAt M x (referenceRow (official co.row)) =
      some (Frame.ref wN, (Frame.ofMountain M).cell wN) := by
    rw [hZ]
    have := Classification.Proofs.CutGap.nodeAt_of_cell hV (ControlProof.cell?_ref (M := M) wN) hwR
    simpa [Frame.ref, hwx, Frame.height] using this
  have hpR : Real pN := real_of_value_pos hO (P_value hO hP).1
  have hpl : (Frame.ref pN).column = l.column := by rw [hlp]
  have hnp : nodeAt M l.column (referenceRow (official co.row)) =
      some (Frame.ref pN, (Frame.ofMountain M).cell pN) := by
    rw [hZ, ← hph, ← hpl]
    have := Classification.Proofs.CutGap.nodeAt_of_cell hV (ControlProof.cell?_ref (M := M) pN) hpR
    simpa [Frame.height] using this
  rw [hnp] at hn'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn')
  refine ⟨Frame.ref wN, _, hnw, ?_⟩
  have hw := Classification.Proofs.CutGap.weakParent_of_P hb hP hph
  have hpc : pN.1.val < wN.1.val := P_column_lt hO hP
  rw [show x + 1 = x + 1 from rfl, Classification.Proofs.CutGap.reachesRoot_step (by show cr < wN.1.val; omega) hw,
    Classification.Proofs.CutGap.reachesRoot_fuel x (l.column + 1) _ (by show pN.1.val < x; omega)
      (by rw [← hpl]; show pN.1.val < pN.1.val + 1; omega)]
  exact hr'

/-- **`AscUp` when the finite coefficient of `C` is zero, given `v(g) < v(o)`.** -/
theorem ascUp_zero {s : List Nat} (hb : Canonical.build s = .ok M) {cr x k : Nat} {co : Cell}
    {l : Ref} (hcx : cr < x) (hk : 1 ≤ k) (hco : Reserve.cell? M ⟨x, k⟩ = some co)
    (hl : co.left = some l) (hab : ∃ c', Reserve.cell? M ⟨x, k + 1⟩ = some c')
    (hZ : referenceRow (official co.row) = official co.row)
    {pa : Ref} {cpa : Cell} (hpa : Reserve.highestAtMost M l.column co.row = some pa)
    (hcpa : Reserve.cell? M pa = some cpa) (hparow : cpa.row = co.row)
    (hr' : reachesRoot M cr (l.column + 1) pa = .ok true)
    {g : Ref} {cg : Cell} (hgc : g.column = cr) (hcg : Reserve.cell? M g = some cg)
    (hgrow : cg.row = co.row) (hval : cg.value < co.value) :
    ∃ ref cl, nodeAt M x (referenceRow (official co.row)) = some (ref, cl) ∧
      reachesRoot M cr (x + 1) ref = .ok true := by
  have hN := build_normal_of_success hb
  have hO := hN.toOrdered
  have hV := build_valid_of_success hb
  obtain ⟨oN, hoN, hocell⟩ := ControlProof.node_of_cell? hco
  have hoc : oN.1.val = x := congrArg Ref.column hoN
  have hoi : oN.2.val = k := congrArg Ref.index hoN
  have hoR : Real oN := by show 0 < oN.2.val; omega
  have hoh : (Frame.ofMountain M).height oN = co.row := by
    show ((Frame.ofMountain M).cell oN).row = co.row; rw [hocell]
  -- `P(o)` and the search from `Q(o) = pa`
  obtain ⟨c', hc'⟩ := hab
  obtain ⟨opN, hopN, _⟩ := ControlProof.node_of_cell? hc'
  have hup : (Frame.ofMountain M).upper oN = some opN :=
    LowerChainRecon.upper_of_above (by rw [hopN, hoN]; rfl)
  obtain ⟨p, hP, _, _, _⟩ := hN.upper_step oN opN hoR hup
  obtain ⟨q, hQ, hit⟩ := (P_iff hO).mp hP
  have hl' : ((Frame.ofMountain M).cell oN).left = some l := by rw [hocell]; exact hl
  have hpa' : highestAtMost M l.column ((Frame.ofMountain M).height oN) = some pa := by
    rw [hoh]; exact hpa
  obtain ⟨q', hQ', hq'⟩ := ControlProof.Q_of_highestAtMost hO hl' hpa'
  have hqq : q = q' := Option.some.inj (hQ.symm.trans hQ')
  subst hqq
  obtain ⟨paN, hpaN, hpacell⟩ := ControlProof.node_of_cell? hcpa
  have hqpa : q = paN := ref_inj' (hq'.trans hpaN.symm)
  subst hqpa
  have hpaR : Real q := Q_real hO hoR hQ
  have hpah : (Frame.ofMountain M).height q = co.row := by
    show ((Frame.ofMountain M).cell q).row = co.row; rw [hpacell, hparow]
  -- the test from `l`: a parent path at the row `C` from `pa` to the root column
  obtain ⟨r, hrc, hrh, hpath⟩ :=
    LowerPB.LiftLegPf.reach_path hb (l.column + 1) q hpaR (by rw [hq']; exact hr')
  obtain ⟨gN, hgN, hgcell⟩ := ControlProof.node_of_cell? hcg
  have hrg : r = gN := by
    apply node_eq_of_column_height hO
    · exact Fin.ext (by rw [hrc, ← hgc]; exact (congrArg Ref.column hgN).symm)
    · show (Frame.ofMountain M).height r = ((Frame.ofMountain M).cell gN).row
      rw [hrh, hpah, hgcell, hgrow]
  subst hrg
  -- the search stops on the path
  have hgv : (Frame.ofMountain M).value r < (Frame.ofMountain M).value oN := by
    show ((Frame.ofMountain M).cell r).value < ((Frame.ofMountain M).cell oN).value
    rw [hgcell, hocell]; exact hval
  have hrR : Real r := Recon.LowerPB.Cone.real_of_one_le_height hO (by rw [hrh]; exact one_le_height hO hpaR)
  have hg0 : 0 < (Frame.ofMountain M).value r := hO.real_positive r hrR
  have hpr := hit_before hO hpath hg0 hgv hit
  have hph1 : (Frame.ofMountain M).height p ≤ (Frame.ofMountain M).height q := hit.height_le hO
  have hph2 : (Frame.ofMountain M).height r ≤ (Frame.ofMountain M).height p := hpr.height_le hO
  have hph : (Frame.ofMountain M).height p = (Frame.ofMountain M).height oN := by
    apply le_antisymm
    · rw [hoh, ← hpah]; exact hph1
    · rw [hoh, ← hpah, ← hrh]; exact hph2
  have hw := Classification.Proofs.CutGap.weakParent_of_P hb hP hph
  have hpc : p.1.val < oN.1.val := P_column_lt hO hP
  have hrp : (Frame.ofMountain M).height r = (Frame.ofMountain M).height p := by
    rw [hph, hrh, hpah, hoh]
  refine ⟨⟨x, k⟩, co, ?_, ?_⟩
  · rw [hZ]; exact Classification.Proofs.CutGap.nodeAt_of_cell hV hco hk
  · rw [← hoN, Classification.Proofs.CutGap.reachesRoot_step (by show cr < oN.1.val; omega) hw,
      Classification.Proofs.CutGap.reachesRoot_fuel x ((Frame.ref p).column + 1) _ (by show p.1.val < x; omega)
        (by show p.1.val < p.1.val + 1; omega),
      Classification.Proofs.CutGap.reachesRoot_path hb hpr hrp (by rw [hrc])]
    have hrcol : (Frame.ref r).column = cr := hrc
    unfold reachesRoot
    rw [if_pos (le_of_eq hrcol)]
    simp [hrcol, pure, Except.pure]

/-- **`AscUp` from `RootValue`.** -/
theorem ascUp_of_rootValue (hRV : RootValue) : AscUp := by
  intro s M t root hTop x k co l hcx hxx hk hco hlo hl hlr hpa hab hg ref' cl' hn' hr'
  have hb := hTop.build
  have hV := build_valid_of_success hb
  by_cases h0 : 0 < (official co.row).coeff 0
  · exact ascUp_pos hb hcx hk hco hl h0 hn' hr'
  · have hZ : referenceRow (official co.row) = official co.row := by
      unfold referenceRow; rw [if_neg h0]
    obtain ⟨pa, cpa, hpa, hcpa, hparow⟩ := hpa
    obtain ⟨g, cg, hgc, _, hcg, hgrow⟩ := hg
    obtain ⟨hpac, hpa0, _⟩ := Classification.Proofs.ChainCorr.highestAtMost_spec hpa
    have hnpa := Classification.Proofs.CutGap.nodeAt_of_cell hV hcpa hpa0
    rw [hpac, hparow, ← hZ] at hnpa
    rw [hnpa] at hn'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn')
    have hval := hRV s M t root hTop x k co l hcx hxx hk hco hlo hl hlr hab hZ pa cpa hpa hcpa
      hparow hr' g cg hgc hcg hgrow
    obtain ⟨c', hc', _⟩ := hab
    exact ascUp_zero hb hcx hk hco hl ⟨c', hc'⟩ hZ hpa hcpa hparow hr' hgc hcg hgrow hval

/-- **`TopStartPaOUp` from `RootValue`.** -/
theorem topStartPaOUp_of_rootValue (hRV : RootValue) : TopStartFixParts.TopStartPaOUp :=
  topStartPaOUp_of_ascUp (ascUp_of_rootValue hRV)

end OmegaY.Official.Recon.TSQ

#print axioms OmegaY.Official.Recon.TSQ.hit_before
#print axioms OmegaY.Official.Recon.TSQ.ascUp_pos
#print axioms OmegaY.Official.Recon.TSQ.ascUp_zero
#print axioms OmegaY.Official.Recon.TSQ.ascUp_of_rootValue
#print axioms OmegaY.Official.Recon.TSQ.topStartPaOUp_of_rootValue
