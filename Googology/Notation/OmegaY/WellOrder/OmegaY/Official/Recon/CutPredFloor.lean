/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CutPredFloor.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.RootInterval
import Googology.Notation.OmegaY.WellOrder.OmegaY.Rows.Intervals

set_option backward.do.legacy false

/-!
# The parents of the last column stay above the rows of the root column

Let `t` be the top of the last column `x₀` of a canonical mountain, `lower` the node below it
and `root = P lower` its root, in the column `c_r`. For every node `q` of `x₀` below `t`
(`q ≤ lower`) with parent `p = P q`:

  every node `w` of `c_r` with `row w ≤ row q` has `row w ≤ row p`   (`last_parent_floor`).

## Proof

It is enough to take `w` the highest node of `c_r` with `row w ≤ row q`. Every node of `c_r`
below the top row is at most the root (father bound, `index_le_root`). By Phyrion's same-row
shadow (`P_rowShadow`) of the top edge, the node of `x₀` at the row of any node `z ≤ root` of
`c_r` reaches `z` by numerical parents at that row.

* `row w = row q`: the shadow path from `q` to `w` starts with `P q = p`, at the row of `w`.
* `w` is the root: `q` is in the root interval of the root with cap `τ = row t`; by
  `root_interval_parent` the parent stays in the interval unless `τ ≤ row q⁺`, and then `q`
  is `lower`, whose parent is the root.
* otherwise the cap is the row of the node `w⁺` above `w`. If `p` left the interval, then
  `row w⁺ ≤ row q⁺`, so `q⁺` is the node of `x₀` at the row of `w⁺`, and the shadow path of
  `w⁺` starts at `q⁺`: `P q⁺` is in a column `≥ c_r`. But `P q⁺` is found from the candidate
  `Q q⁺ ∈ {p, p⁺}` (`candidate_after_upper`), which is left of `c_r`.
-/

namespace OmegaY.Official.Recon.CutPredMD

open OmegaY.Geometry OmegaY.Geometry.Frame

variable {F : Frame}

theorem height_lt_of_index_lt (hF : F.Ordered) {u v : F.Node} (hc : u.1 = v.1)
    (hi : u.2.val < v.2.val) : F.height u < F.height v := by
  rcases u with ⟨c, i⟩
  rcases v with ⟨d, j⟩
  dsimp only at hc
  subst hc
  exact hF.rows_strict c hi

theorem height_le_of_index_le (hF : F.Ordered) {u v : F.Node} (hc : u.1 = v.1)
    (hi : u.2.val ≤ v.2.val) : F.height u ≤ F.height v := by
  rcases u with ⟨c, i⟩
  rcases v with ⟨d, j⟩
  dsimp only at hc
  subst hc
  exact (hF.rows_strict c).monotone hi

theorem index_lt_of_height_lt (hF : F.Ordered) {u v : F.Node} (hc : u.1 = v.1)
    (h : F.height u < F.height v) : u.2.val < v.2.val := by
  by_contra hn
  exact absurd (height_le_of_index_le hF hc.symm (by omega)) (not_le.mpr h)

theorem node_eq_of_index {u v : F.Node} (hc : u.1 = v.1) (hi : u.2.val = v.2.val) : u = v := by
  rcases u with ⟨c, i⟩
  rcases v with ⟨d, j⟩
  dsimp only at hc hi
  subst hc
  have : i = j := Fin.ext hi
  subst this
  rfl

theorem upper_of_lt {u : F.Node} (h : u.2.val + 1 < F.length u.1) :
    F.upper u = some ⟨u.1, ⟨u.2.val + 1, h⟩⟩ := by
  simp [Frame.upper, h]

theorem lt_length_of_col {u : F.Node} {c : Fin F.width} (h : u.1 = c) :
    u.2.val < F.length c := by
  subst h
  exact u.2.isLt

theorem parentPath_first {u w : F.Node} (h : ParentPath F u w) (hne : u ≠ w) :
    ∃ n, F.P u = some n ∧ ParentPath F n w := by
  cases h with
  | refl => exact absurd rfl hne
  | cons hp rest => exact ⟨_, hp, rest⟩

theorem bump_zero_le_of_lt {a b : Row} (h : a < b) : Row.bump a 0 ≤ b :=
  (Row.bump_mono_exponent a (Nat.zero_le _)).trans (Row.bump_last_le h)

/-- The node above the root is not below the top row (father bound). -/
theorem root_barrier (hF : F.Normal) {lower top root : F.Node}
    (hP : F.P lower = some root) (hU : F.upper lower = some top) :
    ∀ u, F.upper root = some u → F.height top ≤ F.height u := by
  intro u hu
  have hrootreal : Real root := real_of_value_pos hF.toOrdered (P_value hF.toOrdered hP).1
  have hval := hF.upper_nontrivial root u hrootreal hu
  have hfb := father_upper_bound hF hP hval
  rwa [aboveHeight_of_upper hU, aboveHeight_of_upper hu] at hfb

/-- Every node of the root column below the top row is at most the root. -/
theorem root_index_le (hF : F.Normal) {lower top root : F.Node}
    (hP : F.P lower = some root) (hU : F.upper lower = some top) :
    ∀ w : F.Node, w.1 = root.1 → F.height w < F.height top → w.2.val ≤ root.2.val := by
  intro w hwc hwt
  by_contra hn
  have hlen : root.2.val + 1 < F.length root.1 := by
    have := lt_length_of_col hwc
    omega
  have h1 := root_barrier hF hP hU _ (upper_of_lt hlen)
  have h2 : F.height (⟨root.1, ⟨root.2.val + 1, hlen⟩⟩ : F.Node) ≤ F.height w :=
    height_le_of_index_le hF.toOrdered hwc.symm (by dsimp only; omega)
  exact absurd (lt_of_le_of_lt (h1.trans h2) hwt) (lt_irrefl _)

/-- **The parents of the last column.** -/
theorem last_parent_floor (hF : F.Normal) {lower top root : F.Node}
    (hP : F.P lower = some root) (hU : F.upper lower = some top)
    {q p : F.Node} (hqc : q.1 = lower.1) (hql : q.2.val ≤ lower.2.val)
    (hp : F.P q = some p) :
    ∀ w : F.Node, w.1 = root.1 → Real w → F.height w ≤ F.height q →
      F.height w ≤ F.height p := by
  have hO := hF.toOrdered
  have hPv := P_value hO hP
  have hrootreal : Real root := real_of_value_pos hO hPv.1
  have hcol : root.1.val < lower.1.val := P_column_lt hO hP
  obtain ⟨htc, hti⟩ := upper_spec hU
  have hlt_top : F.height lower < F.height top :=
    height_lt_of_index_lt hO htc.symm (by omega)
  have hq_low : F.height q ≤ F.height lower := height_le_of_index_le hO hqc hql
  have hq_top : F.height q < F.height top := lt_of_le_of_lt hq_low hlt_top
  have hbar := root_barrier hF hP hU
  have index_le_root := root_index_le hF hP hU
  -- the same-row shadow of the top edge
  have hsh := P_rowShadow hF hP
  -- the core, for a highest node `w`
  have core : ∀ w : F.Node, w.1 = root.1 → Real w → F.height w ≤ F.height q →
      (w.2.val = root.2.val ∨
        ∃ h : w.2.val + 1 < F.length w.1,
          F.height q < F.height (⟨w.1, ⟨w.2.val + 1, h⟩⟩ : F.Node)) →
      F.height w ≤ F.height p := by
    intro w hwc hwr hwq hmax
    have hwi := index_le_root w hwc (lt_of_le_of_lt hwq hq_top)
    have hwroot : F.height w ≤ F.height root := height_le_of_index_le hO hwc hwi
    have hqlen : q.2.val + 1 < F.length q.1 := by
      have := lt_length_of_col (htc.trans hqc.symm)
      omega
    have hUq := upper_of_lt hqlen
    rcases lt_or_eq_of_le hwq with hlt | heq
    · by_cases hwe' : w.2.val = root.2.val
      · -- `w` is the root
        have hwe : w = root := node_eq_of_index hwc hwe'
        subst hwe
        by_cases hqe : q.2.val = lower.2.val
        · have : q = lower := node_eq_of_index hqc hqe
          subst this
          rw [Option.some.inj (hp.symm.trans hP)]
        · obtain ⟨v, hvr, hvc, _, hvh, hvp⟩ := hsh w hwr rfl le_rfl
          have hu : RootInterval F w (F.height top) q :=
            ⟨⟨v, hvr, hvc.trans hqc.symm, hvh, hvp⟩, le_of_lt hlt, hq_top⟩
          rcases root_interval_parent hF hwr (lt_of_le_of_lt (bump_zero_le_of_lt hlt) hq_top)
            hbar hp hu with hin | ⟨_, hb⟩
          · exact hin.2.1
          · rw [aboveHeight_of_upper hUq] at hb
            have : F.height (⟨q.1, ⟨q.2.val + 1, hqlen⟩⟩ : F.Node) ≤ F.height lower :=
              height_le_of_index_le hO hqc (by dsimp only; omega)
            exact absurd (lt_of_le_of_lt (hb.trans this) hlt_top) (lt_irrefl _)
      · -- `w` is below the root, with a node `w⁺` above `q`
        have hwlt : w.2.val < root.2.val := lt_of_le_of_ne hwi hwe'
        obtain ⟨hlen, hq_wp⟩ : ∃ h : w.2.val + 1 < F.length w.1,
            F.height q < F.height (⟨w.1, ⟨w.2.val + 1, h⟩⟩ : F.Node) := by
          rcases hmax with h | h
          · exact absurd h hwe'
          · exact h
        have hUw : F.upper w = some ⟨w.1, ⟨w.2.val + 1, hlen⟩⟩ := upper_of_lt hlen
        have hwpc : (⟨w.1, ⟨w.2.val + 1, hlen⟩⟩ : F.Node).1 = root.1 := hwc
        have hwp_root : F.height (⟨w.1, ⟨w.2.val + 1, hlen⟩⟩ : F.Node) ≤ F.height root :=
          height_le_of_index_le hO hwpc (by dsimp only; omega)
        obtain ⟨v, hvr, hvc, _, hvh, hvp⟩ := hsh w hwr hwc hwroot
        have hu : RootInterval F w (F.height (⟨w.1, ⟨w.2.val + 1, hlen⟩⟩ : F.Node)) q :=
          ⟨⟨v, hvr, hvc.trans hqc.symm, hvh, hvp⟩, le_of_lt hlt, hq_wp⟩
        have hbarw : ∀ u, F.upper w = some u →
            F.height (⟨w.1, ⟨w.2.val + 1, hlen⟩⟩ : F.Node) ≤ F.height u := by
          intro u hu'
          rw [hUw] at hu'
          rw [Option.some.inj hu']
        rcases root_interval_parent hF hwr (lt_of_le_of_lt (bump_zero_le_of_lt hlt) hq_wp)
          hbarw hp hu with hin | ⟨hbefore, hb⟩
        · exact hin.2.1
        · exfalso
          rw [aboveHeight_of_upper hUq] at hb
          have hwpr : Real (⟨w.1, ⟨w.2.val + 1, hlen⟩⟩ : F.Node) := by
            unfold Real; dsimp only; omega
          obtain ⟨y, _, hyc, _, hyh, hyp⟩ := hsh _ hwpr hwpc hwp_root
          have hyc' : y.1 = (⟨q.1, ⟨q.2.val + 1, hqlen⟩⟩ : F.Node).1 := hyc.trans hqc.symm
          have hyi : q.2.val < y.2.val :=
            index_lt_of_height_lt hO (hqc.trans hyc.symm) (hq_wp.trans_eq hyh.symm)
          have hle1 : F.height (⟨q.1, ⟨q.2.val + 1, hqlen⟩⟩ : F.Node) ≤ F.height y :=
            height_le_of_index_le hO hyc'.symm (by dsimp only; omega)
          have hyq : y = ⟨q.1, ⟨q.2.val + 1, hqlen⟩⟩ :=
            node_eq_of_column_height hO hyc' (le_antisymm (hyh.trans_le hb) hle1)
          have hne : y ≠ ⟨w.1, ⟨w.2.val + 1, hlen⟩⟩ := by
            intro h
            have := congrArg (fun z : F.Node => z.1.val) h
            simp only at this
            rw [hyc, hwc] at this
            omega
          obtain ⟨n, hn, rest⟩ := parentPath_first hyp hne
          rw [hyq] at hn
          have h1 : w.1.val ≤ n.1.val := rest.column_le hO
          obtain ⟨c, hQ, hit⟩ := (P_iff hO).mp hn
          have h2 : n.1.val ≤ c.1.val := hit.column_le hO
          have h3 : c.1.val = p.1.val := by
            rcases candidate_after_upper hF hp hUq with hs | ⟨pp, hpp, _, hs⟩
            · rw [Option.some.inj (hQ.symm.trans hs)]
            · rw [Option.some.inj (hQ.symm.trans hs), (upper_spec hpp).1]
          have h4 : p.1.val < w.1.val := hbefore.1
          omega
    · -- `row w = row q`: the shadow path starts at `q`
      obtain ⟨v, _, hvc, _, hvh, hvp⟩ := hsh w hwr hwc hwroot
      have hvq : v = q := node_eq_of_column_height hO (hvc.trans hqc.symm) (hvh.trans heq)
      have hne : v ≠ w := by
        intro h
        have := congrArg (fun z : F.Node => z.1.val) h
        try simp only at this
        rw [hvc, hwc] at this
        omega
      obtain ⟨n, hn, rest⟩ := parentPath_first hvp hne
      rw [hvq, hp] at hn
      rw [← Option.some.inj hn] at rest
      exact rest.height_le hO
  -- climb to the highest node
  have main : ∀ n, ∀ w : F.Node, root.2.val - w.2.val = n → w.1 = root.1 → Real w →
      F.height w ≤ F.height q → F.height w ≤ F.height p := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro w hn hwc hwr hwq
      have hwi := index_le_root w hwc (lt_of_le_of_lt hwq hq_top)
      rcases lt_or_eq_of_le hwi with hlt | heq
      · have hlen : w.2.val + 1 < F.length w.1 := by
          have := lt_length_of_col hwc.symm
          omega
        by_cases hle : F.height (⟨w.1, ⟨w.2.val + 1, hlen⟩⟩ : F.Node) ≤ F.height q
        · have h1 := ih (root.2.val - (w.2.val + 1)) (by omega) ⟨w.1, ⟨w.2.val + 1, hlen⟩⟩ rfl
            hwc (by unfold Real; dsimp only; omega) hle
          exact (height_le_of_index_le (u := w) (v := ⟨w.1, ⟨w.2.val + 1, hlen⟩⟩) hO rfl
            (Nat.le_succ _)).trans h1
        · exact core w hwc hwr hwq (Or.inr ⟨hlen, lt_of_not_ge hle⟩)
      · exact core w hwc hwr hwq (Or.inl heq)
  exact fun w => main _ w rfl

/-! ## The last column rises through every region of a root row -/

/-- **Rise.** For a node `w` of the root column and `D` with `bump (row w) D ≤ τ`, the last
column has a node `y` (at or below the top) with `bump (row w) D ≤ row y` that agrees with
`row w` in the coefficients above `D`. -/
theorem last_column_rise (hF : F.Normal) {lower top root : F.Node}
    (hP : F.P lower = some root) (hU : F.upper lower = some top)
    {w : F.Node} (hwc : w.1 = root.1) (hwr : Real w) {D : Nat}
    (hcap : Row.bump (F.height w) D ≤ F.height top) :
    ∃ y : F.Node, y.1 = lower.1 ∧ Real y ∧ Row.bump (F.height w) D ≤ F.height y ∧
      ∀ k, D < k → (F.height y).coeff k = (F.height w).coeff k := by
  classical
  have hO := hF.toOrdered
  obtain ⟨htc, hti⟩ := upper_spec hU
  have hwt : F.height w < F.height top := lt_of_lt_of_le (Row.lt_bump _ _) hcap
  have hwroot : F.height w ≤ F.height root :=
    height_le_of_index_le hO hwc (root_index_le hF hP hU w hwc hwt)
  obtain ⟨v, hvr, hvc, hvl, hvh, _⟩ := P_rowShadow hF hP w hwr hwc hwroot
  have hvi : v.2.val ≤ lower.2.val := by
    by_contra hn
    exact absurd (height_lt_of_index_lt hO (hvc.symm) (by omega)) (not_lt.mpr hvl)
  have hlen_top : top.2.val < F.length lower.1 := lt_length_of_col htc
  -- the first index above `v` whose node reaches `bump (row w) D`
  let Pj : Nat → Prop := fun j => ∃ h : j < F.length lower.1,
    Row.bump (F.height w) D ≤ F.height (⟨lower.1, ⟨j, h⟩⟩ : F.Node) ∧ v.2.val < j
  have hex : ∃ j, Pj j := ⟨top.2.val, hlen_top, by
    have e : (⟨lower.1, ⟨top.2.val, hlen_top⟩⟩ : F.Node) = top :=
      node_eq_of_index htc.symm rfl
    rw [e]
    exact hcap, by omega⟩
  obtain ⟨hjlen, hjb, hjv⟩ := Nat.find_spec hex
  set j := Nat.find hex with hj
  have hjtop : j ≤ top.2.val := Nat.find_min' hex ⟨hlen_top, by
    have e : (⟨lower.1, ⟨top.2.val, hlen_top⟩⟩ : F.Node) = top :=
      node_eq_of_index htc.symm rfl
    rw [e]
    exact hcap, by omega⟩
  -- the node `q` just below it
  have hqlen : j - 1 < F.length lower.1 := by omega
  set q : F.Node := ⟨lower.1, ⟨j - 1, hqlen⟩⟩ with hq
  have hqr : Real q := by unfold Real; dsimp only [q]; have := hvr; unfold Real at this; omega
  have hqv : F.height w ≤ F.height q := by
    rw [← hvh]
    exact height_le_of_index_le hO hvc (by dsimp only [q]; omega)
  have hqb : F.height q < Row.bump (F.height w) D := by
    by_cases hjv' : j - 1 = v.2.val
    · have e : q = v := node_eq_of_index hvc.symm (by dsimp only [q]; omega)
      rw [e, hvh]
      exact Row.lt_bump _ _
    · have hnot := Nat.find_min hex (show j - 1 < j by omega)
      by_contra hn
      exact hnot ⟨hqlen, le_of_not_gt hn, by omega⟩
  have hUq : F.upper q = some ⟨lower.1, ⟨j, hjlen⟩⟩ := by
    have h1 : q.2.val + 1 < F.length q.1 := by dsimp only [q]; omega
    rw [upper_of_lt h1]
    congr 2
    exact Fin.ext (by dsimp only [q]; omega)
  have hval := hF.upper_nontrivial q _ hqr hUq
  obtain ⟨p, hp⟩ := hF.parent_exists hval
  have hpw : F.height w ≤ F.height p :=
    last_parent_floor hF hP hU (q := q) rfl (by dsimp only [q]; omega) hp w hwc hwr hqv
  have hpq : F.height p ≤ F.height q := P_height_le hO hp
  have hjump : Row.jump (F.height q) (F.height p) ≤ D :=
    Row.jump_le_of_same_interval hqv hqb hpw (lt_of_le_of_lt hpq hqb)
  have hrow : F.height (⟨lower.1, ⟨j, hjlen⟩⟩ : F.Node) =
      Row.bump (F.height q) (Row.jump (F.height q) (F.height p)) := by
    rw [← aboveHeight_of_upper hUq, hF.above_row hp]
    rfl
  have hwq : Row.jump (F.height w) (F.height q) ≤ D := Row.jump_le_of_lt_bump hqv hqb
  refine ⟨⟨lower.1, ⟨j, hjlen⟩⟩, rfl, by unfold Real; dsimp only; omega, hjb, ?_⟩
  intro k hk
  rw [hrow, Row.coeff_bump_high (lt_of_le_of_lt hjump hk)]
  exact (Row.coeff_eq_of_jump_le hwq hk.le).symm

end OmegaY.Official.Recon.CutPredMD

#print axioms OmegaY.Official.Recon.CutPredMD.last_parent_floor
#print axioms OmegaY.Official.Recon.CutPredMD.last_column_rise
