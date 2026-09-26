/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/LegRowMatchTop.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RootCut
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.RootInterval
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RowLawSource
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RowLawRows

set_option backward.do.legacy false

/-!
# The top of the last column is above the top of the root column in every region

`topAboveRoot`: in `M(s)` with top `t` of the last column `x₀` (row `τ`) and root `r = left(t)`
in column `c_r`, let `S` be a region of level `d + 2` below `τ` that contains a node of `c_r`,
and `ρ` the top of `c_r` in `S`. Then the top `κ` of `x₀` in `S` is strictly higher than `ρ`:
its coefficient `d` (the height in `S`) is larger.

`Top.cut_pos` (`RootCut.lean`) is the case of the regions `[0, ω^{d+1})` with `h_ρ = 0`.

Proof (in the frame of `M(s)`). The node `ρ` is not above `r` (the node above `r` is at
least as high as `t`, `father_upper_bound`), so the row shadow of the edge `t⁻ → r` gives a node
`v` of `x₀` at the row of `ρ` with a numerical-parent path to `ρ` (`P_rowShadow`). Suppose `κ`
has the height of `ρ`. Let `cap` be the row of the node `ρ⁺` above `ρ` (if `ρ ≠ r`) or `τ` (if
`ρ = r`); it is not in `S` and above `ρ`, hence above every row of `S`. `κ` lies in the root
interval of `ρ` with cap `cap` (cone witness `v`), so its parent `p` either stays in the
interval (`root_interval_parent`), or leaves it to the left of `c_r` with `cap ≤ row κ⁺`.

* In the interval: `row ρ ≤ row p ≤ row κ`, and `ρ, κ` agree at the exponents `≥ d`, so `p` does
  too; the row `B(row κ, row p)` of `κ⁺` then agrees with `κ` at the exponents `≥ d + 1`, so
  `κ⁺` is in `S`, against the choice of `κ`.
* Leaving, `ρ = r`: `κ⁺` is at least as high as `t`, so `κ = t⁻` and `p = r`, which is not left
  of `c_r`.
* Leaving, `ρ ≠ r`: the row shadow gives a node `v'` of `x₀` at the row of `ρ⁺` with a path to
  `ρ⁺`; it is `κ⁺`, so the parent of `κ⁺` is at or right of `c_r`; the parent of a node is not
  left of the parent of the node above it (`candidate_after_upper`), a contradiction.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.LegJump.TopRoot

open Canonical Geometry Frame Official Recon Expansion Dimension

/-! ## Rows -/

/-- The coefficients of `a` and `b` agree at every exponent `≥ e`. -/
def AgreeGe (e : Nat) (a b : Row) : Prop := ∀ k, e ≤ k → a.coeff k = b.coeff k

theorem inRegion_official_iff {d : Nat} {S r : Row} :
    inRegion (d + 2) S (official r) = true ↔ AgreeGe (d + 1) r S := by
  rw [RowLaw.inRegion_iff']
  constructor
  · intro h k hk
    rw [← coeff_official_pos r (by omega)]
    exact h k (by omega)
  · intro h k hk
    rw [coeff_official_pos r (by omega)]
    exact h k (by omega)

/-- A row outside a region and above one of its rows is above all of its rows. -/
theorem lt_of_out {e : Nat} {a b c S : Row} (ha : AgreeGe e a S) (hc : AgreeGe e c S)
    (hb : ¬ AgreeGe e b S) (hab : a < b) : c < b := by
  obtain ⟨i, hi, hlt⟩ := Row.lt_iff.mp hab
  have hie : e ≤ i := by
    by_contra hn
    apply hb
    intro k hk
    rw [← ha k hk]
    exact (hi k (by omega)).symm
  refine Row.lt_iff.mpr ⟨i, ?_, ?_⟩
  · intro j hj
    rw [hc j (by omega), ← ha j (by omega)]
    exact hi j hj
  · rw [hc i hie, ← ha i hie]
    exact hlt

/-- The row `B(a, p)` agrees with `a` above the jump. -/
theorem agree_B {e : Nat} {a p : Row} (h : Row.jump a p ≤ e) : AgreeGe (e + 1) (Row.B a p) a := by
  intro k hk
  unfold Row.B
  exact Row.coeff_bump_high (by omega)

theorem agree_bump_zero {e : Nat} (he : 1 ≤ e) (a : Row) : AgreeGe e (Row.bump a 0) a := by
  intro k hk
  exact Row.coeff_bump_high (by omega)

theorem official_inj {a b : Row} (ha : (1 : Row) ≤ a) (hb : (1 : Row) ≤ b)
    (h : official a = official b) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (ne_of_lt (official_strictMono ha hab))
  · exact hab
  · exact absurd h.symm (ne_of_lt (official_strictMono hb hab))

/-- Two real rows of a region of level `d + 2` with the same height agree at `≥ d`. -/
theorem agree_of_height {d : Nat} {S a b : Row} (ha1 : (1 : Row) ≤ a) (hb1 : (1 : Row) ≤ b)
    (ha : inRegion (d + 2) S (official a) = true) (hb : inRegion (d + 2) S (official b) = true)
    (hh : (official a).coeff d = (official b).coeff d) : AgreeGe d a b := by
  have hoff : ∀ k, d ≤ k → (official a).coeff k = (official b).coeff k := by
    intro k hk
    rcases Nat.eq_or_lt_of_le hk with rfl | hlt
    · exact hh
    · rw [RowLaw.inRegion_iff'.mp ha k (by omega), RowLaw.inRegion_iff'.mp hb k (by omega)]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have he : a = b := official_inj ha1 hb1 (row_ext (fun k => hoff k (Nat.zero_le _)))
    subst he
    intro _ _
    rfl
  · intro k hk
    rw [← coeff_official_pos a (by omega), ← coeff_official_pos b (by omega)]
    exact hoff k hk

/-! ## Frames -/

theorem height_lt_iff {F : Frame} (hF : F.Ordered) {u v : F.Node} (hc : u.1 = v.1) :
    F.height u < F.height v ↔ u.2.val < v.2.val := by
  rcases u with ⟨cu, iu⟩
  rcases v with ⟨cv, iv⟩
  dsimp only at hc
  subst hc
  exact (hF.rows_strict cu).lt_iff_lt

theorem height_le_iff {F : Frame} (hF : F.Ordered) {u v : F.Node} (hc : u.1 = v.1) :
    F.height u ≤ F.height v ↔ u.2.val ≤ v.2.val := by
  rcases u with ⟨cu, iu⟩
  rcases v with ⟨cv, iv⟩
  dsimp only at hc
  subst hc
  exact (hF.rows_strict cu).le_iff_le

theorem node_eq_of_index {F : Frame} {u v : F.Node} (hc : u.1 = v.1) (hi : u.2.val = v.2.val) :
    u = v := by
  rcases u with ⟨cu, iu⟩
  rcases v with ⟨cv, iv⟩
  dsimp only at hc hi
  subst hc
  have : iu = iv := Fin.ext hi
  subst this
  rfl

theorem upper_of_lt {F : Frame} {u : F.Node} (h : u.2.val + 1 < F.length u.1) :
    F.upper u = some ⟨u.1, ⟨u.2.val + 1, h⟩⟩ := by
  simp [Frame.upper, h]

/-- The parent of a node is not left of the parent of the node above it. -/
theorem col_P_upper_le {F : Frame} (hF : F.Normal) {u v p p' : F.Node}
    (hp : F.P u = some p) (hv : F.upper u = some v) (hp' : F.P v = some p') :
    p'.1.val ≤ p.1.val := by
  obtain ⟨q, hQ, trace⟩ := (P_iff hF.toOrdered).mp hp'
  have hq := trace.column_le hF.toOrdered
  rcases candidate_after_upper hF hp hv with hs | ⟨pp, hpp, _, hs⟩
  · rw [Option.some.inj (hQ.symm.trans hs)] at hq
    exact hq
  · rw [Option.some.inj (hQ.symm.trans hs)] at hq
    rw [(upper_spec hpp).1] at hq
    exact hq

theorem parentPath_cases {F : Frame} {u p : F.Node} (h : ParentPath F u p) :
    u = p ∨ ∃ q, F.P u = some q ∧ ParentPath F q p := by
  cases h with
  | refl => exact Or.inl rfl
  | cons hq rest => exact Or.inr ⟨_, hq, rest⟩

/-! ## The theorem -/

set_option maxHeartbeats 800000 in
/-- **The top of `x₀` is above the top of the root column in every region below `τ`.** -/
theorem topAboveRoot {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}
    (h : Top s M t root) {d : Nat} {S : Row}
    (hS : ∀ r, inRegion (d + 2) S r = true → r < official t.row)
    {ρ : Ref × Cell} (hρ : topIn M root.column (d + 2) S = some ρ) :
    ∃ κ, topIn M (M.size - 1) (d + 2) S = some κ ∧
      (official ρ.2.row).coeff d < (official κ.2.row).coeff d := by
  have hV := build_valid_of_success h.build
  have hb := h.build
  have ht1 := h.row_one_le
  obtain ⟨hρmem, hρin, hρmax⟩ := RowLaw.topIn_spec hρ
  have hρ1 : (1 : Row) ≤ ρ.2.row := realNodes_row_one_le hV hρmem
  have hρlt : ρ.2.row < t.row := row_lt_of_official ht1 (hS _ hρin)
  have htout : inRegion (d + 2) S (official t.row) ≠ true := fun hin =>
    lt_irrefl _ (hS _ hin)
  obtain ⟨middle, last, hs, hlast, p, hinit, htop, hroot⟩ := h.preparation
  subst hinit
  subst htop
  subst hroot
  obtain ⟨g⟩ := p.root_geometry hlast
  have hN := build_normal_of_success p.initial_build
  have hF := hN.toOrdered
  have hsz := Canonical.build_size p.initial_build
  have hx0 : g.topNode.1.val = p.initial.size - 1 := by
    rw [g.top_column, hsz]; simp
  have hlowcol : g.lower.1 = g.topNode.1 := (upper_spec g.lower_upper).1.symm
  have hlowidx : g.topNode.2.val = g.lower.2.val + 1 := (upper_spec g.lower_upper).2
  have hRootCol : g.rootNode.1.val = p.root.column := congrArg Ref.column g.root_ref
  have htopRow : (Frame.ofMountain p.initial).height g.topNode = p.lastTop.row :=
    congrArg Cell.row g.top_cell
  have hcrx : p.root.column < p.initial.size - 1 := h.lt
  -- the frame node `w` of `ρ`
  obtain ⟨w, hwcol, hwreal, hwref, hwcell⟩ := frameNode_of_realNodes hρmem
  have hwh : (Frame.ofMountain p.initial).height w = ρ.2.row := congrArg Cell.row hwcell
  have hwr : w.1 = g.rootNode.1 := Fin.ext (hwcol.trans hRootCol.symm)
  -- `w` is not above the root
  have hwle : w.2.val ≤ g.rootNode.2.val := by
    by_contra hn
    have hup : g.rootNode.2.val + 1 < (Frame.ofMountain p.initial).length g.rootNode.1 := by
      have := w.2.isLt
      have hl : (Frame.ofMountain p.initial).length w.1 =
          (Frame.ofMountain p.initial).length g.rootNode.1 := by rw [hwr]
      omega
    have hU := upper_of_lt hup
    have hfb := father_upper_bound_nodes hN g.lower_parent g.lower_upper hU
    have hle : (Frame.ofMountain p.initial).height ⟨g.rootNode.1, ⟨_, hup⟩⟩ ≤
        (Frame.ofMountain p.initial).height w :=
      (height_le_iff hF (by exact hwr.symm)).mpr (by dsimp only; omega)
    rw [htopRow] at hfb
    exact absurd (hfb.trans hle) (not_le.mpr (hwh ▸ hρlt))
  have hwleR : (Frame.ofMountain p.initial).height w ≤
      (Frame.ofMountain p.initial).height g.rootNode :=
    (height_le_iff hF hwr).mpr hwle
  -- the row shadow of `t⁻ → r` at `ρ`
  obtain ⟨v, hvreal, hvcol, _, hvh, hvpath⟩ :=
    P_rowShadow hN g.lower_parent w hwreal hwr hwleR
  have hvcol' : v.1 = g.topNode.1 := hvcol.trans hlowcol
  have hvmem := realNodes_of_frameNode v hvreal
  have hvx0 : v.1.val = p.initial.size - 1 := by rw [hvcol', hx0]
  rw [hvx0] at hvmem
  have hvin : inRegion (d + 2) S
      (official ((Frame.ofMountain p.initial).cell v).row) = true := by
    change inRegion (d + 2) S (official ((Frame.ofMountain p.initial).height v)) = true
    rw [hvh, hwh]
    exact hρin
  obtain ⟨κ, hκ⟩ := filter_last_exists
    (P := fun q => inRegion (d + 2) S (official q.2.row)) hvmem hvin
  have hκ' : topIn p.initial (p.initial.size - 1) (d + 2) S = some κ := hκ
  refine ⟨κ, hκ', ?_⟩
  obtain ⟨hκmem, hκin, hκmax⟩ := filter_last_max hκ
  have hκin : inRegion (d + 2) S (official κ.2.row) = true := hκin
  have hκmax' : ∀ q ∈ realNodes p.initial (p.initial.size - 1),
      inRegion (d + 2) S (official q.2.row) = true → q.1.index ≤ κ.1.index := hκmax
  have hκ1 : (1 : Row) ≤ κ.2.row := realNodes_row_one_le hV hκmem
  have hvκ : official ((Frame.ofMountain p.initial).cell v).row ≤ official κ.2.row :=
    RowLaw.topIn_row_max p.initial_build hκ' hvmem hvin
  have hge : (official ρ.2.row).coeff d ≤ (official κ.2.row).coeff d := by
    have := RowLaw.coeff_le_of_inRegion hvin hκin hvκ
    change (official ((Frame.ofMountain p.initial).height v)).coeff d ≤ _ at this
    rwa [hvh, hwh] at this
  by_contra hnot
  have heq : (official ρ.2.row).coeff d = (official κ.2.row).coeff d := by omega
  have hagree : AgreeGe d κ.2.row ρ.2.row :=
    agree_of_height hκ1 hρ1 hκin hρin heq.symm
  -- the frame node `k` of `κ`
  obtain ⟨k, hkcol, hkreal, hkref, hkcell⟩ := frameNode_of_realNodes hκmem
  have hkh : (Frame.ofMountain p.initial).height k = κ.2.row := congrArg Cell.row hkcell
  have hkt : k.1 = g.topNode.1 := Fin.ext (hkcol.trans hx0.symm)
  have hvk : v.2.val ≤ k.2.val := by
    have := hκmax' _ hvmem hvin
    have hr1 : (Frame.ref v).index = v.2.val := rfl
    have hr2 : κ.1.index = k.2.val := by rw [← hkref]; rfl
    simpa [hr1, hr2] using this
  have hkne : k.2.val ≠ g.topNode.2.val := by
    intro he
    have hkeq : k = g.topNode := node_eq_of_index hkt he
    apply htout
    rw [← g.top_cell, ← hkeq, hkcell]
    exact hκin
  have hktop : k.2.val < g.topNode.2.val := by
    have := g.top_last
    have := g.topNode.2.isLt
    have hl : (Frame.ofMountain p.initial).length k.1 =
        (Frame.ofMountain p.initial).length g.topNode.1 := by rw [hkt]
    have := k.2.isLt
    omega
  have hkup : k.2.val + 1 < (Frame.ofMountain p.initial).length k.1 := by
    have hl : (Frame.ofMountain p.initial).length k.1 =
        (Frame.ofMountain p.initial).length g.topNode.1 := by rw [hkt]
    have := g.topNode.2.isLt
    omega
  set kp : (Frame.ofMountain p.initial).Node := ⟨k.1, ⟨k.2.val + 1, hkup⟩⟩ with hkpdef
  have hUk : (Frame.ofMountain p.initial).upper k = some kp := upper_of_lt hkup
  obtain ⟨pk, hpk, hkpB, _, _⟩ := hN.upper_step k kp hkreal hUk
  -- `κ⁺` is not in `S`
  have hkpout : ¬ AgreeGe (d + 1) ((Frame.ofMountain p.initial).height kp) S := by
    intro hin
    have hkpmem := realNodes_of_frameNode kp (show Real kp from Nat.succ_pos _)
    have hkpx : kp.1.val = p.initial.size - 1 := by
      change k.1.val = _; rw [hkt, hx0]
    rw [hkpx] at hkpmem
    have := hκmax' _ hkpmem (inRegion_official_iff.mpr hin)
    have hr2 : κ.1.index = k.2.val := by rw [← hkref]; rfl
    change k.2.val + 1 ≤ κ.1.index at this
    omega
  have hSw : AgreeGe (d + 1) ((Frame.ofMountain p.initial).height w) S := by
    rw [hwh]; exact inRegion_official_iff.mp hρin
  have hSk : AgreeGe (d + 1) ((Frame.ofMountain p.initial).height k) S := by
    rw [hkh]; exact inRegion_official_iff.mp hκin
  have hwk : (Frame.ofMountain p.initial).height w ≤ (Frame.ofMountain p.initial).height k := by
    rw [← hvh]
    exact (height_le_iff hF (hvcol'.trans hkt.symm)).mpr hvk
  -- the common argument for a cap
  have key : ∀ cap : Row, ¬ AgreeGe (d + 1) cap S →
      (Frame.ofMountain p.initial).height w < cap →
      (∀ up, (Frame.ofMountain p.initial).upper w = some up →
        cap ≤ (Frame.ofMountain p.initial).height up) →
      (BeforeRoot (Frame.ofMountain p.initial) w pk →
        cap ≤ (Frame.ofMountain p.initial).height kp → False) → False := by
    intro cap hcapout hwcap hbar hexit
    have hkcap : (Frame.ofMountain p.initial).height k < cap := lt_of_out hSw hSk hcapout hwcap
    have hcap0 : Row.bump ((Frame.ofMountain p.initial).height w) 0 < cap := by
      refine lt_of_out hSw ?_ hcapout hwcap
      intro j hj
      rw [agree_bump_zero (by omega) _ j hj]
      exact hSw j hj
    have hkIn : RootInterval (Frame.ofMountain p.initial) w cap k :=
      ⟨⟨v, hvreal, hvcol'.trans hkt.symm, hvh, hvpath⟩, hwk, hkcap⟩
    rcases root_interval_parent hN hwreal hcap0 hbar hpk hkIn with hin | ⟨hbefore, hbarrier⟩
    · have hwp := hin.2.1
      have hpk_le := P_height_le hF hpk
      have hjwk : Row.jump ((Frame.ofMountain p.initial).height w)
          ((Frame.ofMountain p.initial).height k) ≤ d := by
        rw [Row.jump_le_iff]
        intro j hj
        rw [hwh, hkh]
        exact (hagree j hj).symm
      have hjpk := (Row.jump_le_between hwp hpk_le hjwk).2
      rw [Row.jump_comm] at hjpk
      have hB := agree_B hjpk
      apply hkpout
      intro j hj
      rw [hkpB, hB j hj]
      exact hSk j hj
    · rw [aboveHeight_of_upper hUk] at hbarrier
      exact hexit hbefore hbarrier
  rcases Nat.eq_or_lt_of_le hwle with hwR | hwR
  · -- `ρ = r`: the cap is `τ`
    have hweq : w = g.rootNode := node_eq_of_index hwr hwR
    refine key p.lastTop.row ?_ (hwh ▸ hρlt) ?_ ?_
    · intro hin
      exact htout (inRegion_official_iff.mpr hin)
    · intro up hup
      rw [hweq] at hup
      rw [← htopRow]
      exact father_upper_bound_nodes hN g.lower_parent g.lower_upper hup
    · intro hbefore hcap
      have hkpt : kp = g.topNode := by
        apply node_eq_of_index (show kp.1 = g.topNode.1 from hkt)
        have h1 : g.topNode.2.val ≤ kp.2.val := by
          rw [← htopRow] at hcap
          exact (height_le_iff hF (show g.topNode.1 = kp.1 from hkt.symm)).mp hcap
        change k.2.val + 1 = _
        change g.topNode.2.val ≤ k.2.val + 1 at h1
        omega
      have hklow : k = g.lower := by
        apply node_eq_of_index (hkt.trans hlowcol.symm)
        have h2 : kp.2.val = g.topNode.2.val := congrArg (fun z => z.2.val) hkpt
        have h3 : kp.2.val = k.2.val + 1 := rfl
        omega
      rw [hklow, g.lower_parent] at hpk
      have hpe := Option.some.inj hpk
      have := hbefore.1
      rw [← hpe, hweq] at this
      exact lt_irrefl _ this
  · -- `ρ` below `r`: the cap is the row of `ρ⁺`
    have hwup : w.2.val + 1 < (Frame.ofMountain p.initial).length w.1 := by
      have := g.rootNode.2.isLt
      have hl : (Frame.ofMountain p.initial).length w.1 =
          (Frame.ofMountain p.initial).length g.rootNode.1 := by rw [hwr]
      omega
    set wp : (Frame.ofMountain p.initial).Node := ⟨w.1, ⟨w.2.val + 1, hwup⟩⟩ with hwpdef
    have hUw : (Frame.ofMountain p.initial).upper w = some wp := upper_of_lt hwup
    have hwwp : (Frame.ofMountain p.initial).height w < (Frame.ofMountain p.initial).height wp :=
      (height_lt_iff (u := w) (v := wp) hF rfl).mpr (by show w.2.val < w.2.val + 1; omega)
    -- `ρ⁺` is not in `S`
    have hwpout : ¬ AgreeGe (d + 1) ((Frame.ofMountain p.initial).height wp) S := by
      intro hin
      have hwpmem := realNodes_of_frameNode wp (show Real wp from Nat.succ_pos _)
      have hwpc : wp.1.val = p.root.column := hwcol
      rw [hwpc] at hwpmem
      have := hρmax _ hwpmem (inRegion_official_iff.mpr hin)
      have hr2 : ρ.1.index = w.2.val := by rw [← hwref]; rfl
      change w.2.val + 1 ≤ ρ.1.index at this
      omega
    refine key ((Frame.ofMountain p.initial).height wp) hwpout hwwp ?_ ?_
    · intro up hup
      rw [hUw] at hup
      rw [Option.some.inj hup]
    · intro hbefore hcap
      -- the row shadow at `ρ⁺`
      have hwpR : (Frame.ofMountain p.initial).height wp ≤
          (Frame.ofMountain p.initial).height g.rootNode :=
        (height_le_iff hF (show wp.1 = g.rootNode.1 from hwr)).mpr
          (by show w.2.val + 1 ≤ g.rootNode.2.val; omega)
      obtain ⟨v', hv'real, hv'col, _, hv'h, hv'path⟩ :=
        P_rowShadow hN g.lower_parent wp (Nat.succ_pos _) hwr hwpR
      have hv'col' : v'.1 = k.1 := hv'col.trans (hlowcol.trans hkt.symm)
      have hkv' : k.2.val < v'.2.val := by
        rw [← height_lt_iff hF hv'col'.symm, hv'h]
        exact lt_of_out hSw hSk hwpout hwwp
      have hv'kp : v'.2.val ≤ kp.2.val := by
        rw [← height_le_iff hF (show v'.1 = kp.1 from hv'col'), hv'h]
        exact hcap
      have hv'eq : v' = kp := by
        apply node_eq_of_index (show v'.1 = kp.1 from hv'col')
        have h3 : kp.2.val = k.2.val + 1 := rfl
        omega
      rw [hv'eq] at hv'path
      have h1 : k.1.val = p.initial.size - 1 := by rw [hkt, hx0]
      have h2 : wp.1.val = p.root.column := hwcol
      have h0 : kp.1.val = k.1.val := rfl
      rcases parentPath_cases hv'path with he | ⟨q, hP, rest⟩
      · have : kp.1.val = wp.1.val := congrArg (fun z => z.1.val) he
        omega
      · have hqcol := rest.column_le hF
        have hmono := col_P_upper_le hN hpk hUk hP
        have := hbefore.1
        have h4 : wp.1.val = w.1.val := rfl
        omega

end OmegaY.Official.Classification.Proofs.ChainCorr.LegJump.TopRoot

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegJump.TopRoot.topAboveRoot
