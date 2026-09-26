/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/TSQRootValueParts.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TSQAscUp
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StartRootPartsX0

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `RootValue` in two of its three cases (`TSQ`)

`RootValue` (`TSQAscUp.lean`, about `M(s)` alone): `o = (x, C)` (`c_r < x ≤ x₀`, `row o < τ`, the
finite coefficient of `C` zero), `o⁺` below `τ`, the leg `l > c_r` of `o`, `pa = (l, C)` whose
in-row chain reaches the column `c_r` (at `g = (c_r, C)`). Then `v(g) < v(o)`.

Write `P` for the numerical parent. `Q(o) = pa`, and `P(o)` is the first node of the search from
`pa` with a value below `v(o)`; it lies on the chain of `pa`, which passes through `g`.

* **`g` has no node above it below `τ`** (`value_lt_of_barrier`, a frame statement). Take the root
  interval of `g` with the cap `τ` (`Geometry.RootInterval`): `pa` is inside, and if
  `v(o) ≤ v(g)` then `P(o)` is not (a node of the interval at the row `C` on the chain of `pa` is
  on the path to `g`, so its value is at least `v(g)`). The first exit of the chain of `pa`
  (`ParentPath.root_interval_exit`, with `root_interval_parent`) gives
  `row o⁺ = B(C, row P(o)) ≥ τ`, a contradiction.
* **`C = 0`** (`value_lt_bottom`). The bottom row is a sequence with the nearest-smaller-left
  parents: the search from a bottom node visits the bottom nodes of all columns to its left one
  by one (`Q_bottom`, `hit_bottom`). The node `t⁻` below `t` has `P(t⁻) = r` (the root), so its
  row shadow (`P_rowShadow`) gives a path of numerical parents at the bottom row from the bottom
  node of `x₀` to `g`. Every bottom node strictly between two consecutive nodes of this path was
  rejected by the search of the right one (`bottom_path_value`), so `v(g) < v(o)`.
* **`C > 0` and `g⁺` below `τ`**: left open as `RootValueHi`.

Results:

* `value_lt_of_barrier`, `Q_bottom`, `hit_bottom`, `bottom_path_value`;
* `rootValue_of_hi : RootValueHi → RootValue`;
* `topStartPaOUp_of_rootValueHi : RootValueHi → TopStartPaOUp`.
-/

namespace OmegaY.Official.Recon.TSQ.RVP

open Canonical Expansion Classification Reserve
open OmegaY.Geometry OmegaY.Geometry.Frame

/-! ## The barrier case (a frame statement) -/

section Barrier

variable {F : Frame}

/-- **The barrier case.** `pa = Q(o)` at the row of `o` has a path of numerical parents to `g`
at the same row, the nodes above `g` are at or above the cap `τ`, and `o⁺` is below `τ`. Then
`v(g) < v(o)`. -/
theorem value_lt_of_barrier (hF : F.Normal) {o pa g p : F.Node} {τ : Row}
    (hP : F.P o = some p) (hQ : F.Q o = some pa) (hpah : F.height pa = F.height o)
    (hgh : F.height g = F.height o) (hpath : ParentPath F pa g) (hgR : Real g)
    (hbar : ∀ up, F.upper g = some up → τ ≤ F.height up)
    (hcap : Row.bump (F.height g) 0 < τ) (hup : F.aboveHeight o < τ) :
    F.value g < F.value o := by
  have hO := hF.toOrdered
  by_contra hle
  have hle' : F.value o ≤ F.value g := Nat.le_of_not_lt hle
  obtain ⟨q, hQ', trace⟩ := (P_iff hO).mp hP
  have hqe : q = pa := Option.some.inj (hQ'.symm.trans hQ)
  subst hqe
  have hoR : Real o := real_of_value_pos hO (lt_trans (P_value hO hP).1 (P_value hO hP).2)
  have hqR : Real q := Q_real hO hoR hQ
  have path := trace.parentPath hO (hO.real_positive q hqR)
  have hoτ : F.height o < τ :=
    lt_trans (Classification.Proofs.ChainCorr.SRX0.height_lt_above hF hP) hup
  have hq : RootInterval F g τ q :=
    ⟨⟨q, hqR, rfl, hpah.trans hgh.symm, hpath⟩, le_of_eq (hgh.trans hpah.symm),
      hpah ▸ hoτ⟩
  have hp : ¬ RootInterval F g τ p := by
    rintro ⟨⟨low, _, hlc, hlh, hlp⟩, hge, _⟩
    have hph : F.height p ≤ F.height q := path.height_le hO
    have heq : F.height p = F.height g :=
      le_antisymm (hph.trans (le_of_eq (hpah.trans hgh.symm))) hge
    have hlow : low = p := node_eq_of_column_height hO hlc (hlh.trans heq.symm)
    subst hlow
    have h1 := hlp.value_le hO
    have h2 := trace.result.2
    omega
  obtain ⟨_, hB⟩ := path.root_interval_exit hF
    (fun z r _ hzr hz => root_interval_parent hF hgR hcap hbar hzr hz)
    (Q_column_lt hO hQ) (le_of_eq hpah) hq hp
  rw [← hF.above_row hP] at hB
  exact absurd (lt_of_le_of_lt hB hup) (lt_irrefl _)

end Barrier

/-! ## The bottom row -/

section Bottom

variable {M : Mountain}

/-- **The candidate of a bottom node** is the bottom node of the previous column. -/
theorem Q_bottom {s : List Nat} (hb : Canonical.build s = .ok M)
    {u : (Frame.ofMountain M).Node} (hu : u.2.val = 1) (hc : 0 < u.1.val) :
    ∃ w, (Frame.ofMountain M).Q u = some w ∧ w.1.val = u.1.val - 1 ∧ w.2.val = 1 := by
  have hO := (build_normal_of_success hb).toOrdered
  have hlen : 1 < (Frame.ofMountain M).length u.1 := by have := u.2.isLt; omega
  have hleft := build_bottom_left hb u.1 hlen
  have hu' : u.2 = ⟨1, hlen⟩ := Fin.ext hu
  let c' : Fin (Frame.ofMountain M).width := ⟨u.1.val - 1, by have := u.1.isLt; omega⟩
  have hl2 := hO.length_ge_two c'
  let lft : (Frame.ofMountain M).Node := ⟨c', ⟨0, by omega⟩⟩
  have hcl : ((Frame.ofMountain M).cell u).left = some (Frame.ref lft) := by
    show ((Frame.ofMountain M).cells u.1 u.2).left = _
    rw [hu', hleft, if_neg (by omega)]
    rfl
  have hu1 : (Frame.ofMountain M).height u = 1 := by
    show ((Frame.ofMountain M).cells u.1 u.2).row = 1
    rw [hu']
    exact hO.bottom_row u.1 hlen
  let i1 : Fin ((Frame.ofMountain M).length lft.1) :=
    ⟨1, by show 1 < (Frame.ofMountain M).length c'; omega⟩
  have hi1 : (Frame.ofMountain M).height ⟨lft.1, i1⟩ = 1 :=
    hO.bottom_row c' (by show 1 < (Frame.ofMountain M).length c'; omega)
  have hQ := Q_eq_of_maximal hcl i1 (mem_eligible.mpr ⟨by show 0 ≤ 1; omega,
    by rw [hi1, hu1]⟩) (by
      intro j hj
      obtain ⟨_, hjr⟩ := mem_eligible.mp hj
      rw [hu1] at hjr
      by_contra hn
      have hlt : i1 < j := lt_of_not_ge hn
      have := hO.rows_strict lft.1 hlt
      change (Frame.ofMountain M).height ⟨lft.1, i1⟩ < (Frame.ofMountain M).height ⟨lft.1, j⟩
        at this
      rw [hi1] at this
      exact absurd (lt_of_lt_of_le this hjr) (lt_irrefl _))
  exact ⟨_, hQ, rfl, rfl⟩

/-- **The search from a bottom node** stays at the bottom row and rejects every bottom node from
its start down to (not including) its hit. -/
theorem hit_bottom {s : List Nat} (hb : Canonical.build s = .ok M) {θ : Nat} :
    ∀ {q p : (Frame.ofMountain M).Node}, Hit (Frame.ofMountain M) θ q p → q.2.val = 1 →
      p.2.val = 1 ∧ ∀ z : (Frame.ofMountain M).Node, z.2.val = 1 → p.1.val < z.1.val →
        z.1.val ≤ q.1.val → θ ≤ (Frame.ofMountain M).value z := by
  have hO := (build_normal_of_success hb).toOrdered
  intro q p h
  induction h with
  | here _ _ =>
    intro hq
    exact ⟨hq, fun z _ h1 h2 => absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)⟩
  | @next u q' p hrej hQ _ ih =>
    intro hu
    have hc := Q_column_lt hO hQ
    obtain ⟨w, hw, hwc, hw1⟩ := Q_bottom hb hu (by omega)
    have hwq : q' = w := Option.some.inj (hQ.symm.trans hw)
    subst hwq
    obtain ⟨hp1, hrest⟩ := ih hw1
    refine ⟨hp1, fun z hz1 hpz hzu => ?_⟩
    rcases Nat.lt_or_ge z.1.val u.1.val with hlt | hge
    · exact hrest z hz1 hpz (by omega)
    · have hzu' : z = u := ControlProof.node_eq_of_index (Fin.ext (by omega)) (by omega)
      subst hzu'
      have hpos := hO.real_positive z (by show 0 < z.2.val; omega)
      by_contra hn
      exact hrej ⟨hpos, Nat.lt_of_not_ge hn⟩

/-- **Nearest smaller values at the bottom row.** Along a path of numerical parents from a
bottom node `n` to `g`, every bottom node strictly right of `g` and at or left of `n` has a value
above `v(g)`. -/
theorem bottom_path_value {s : List Nat} (hb : Canonical.build s = .ok M) :
    ∀ {n g : (Frame.ofMountain M).Node}, ParentPath (Frame.ofMountain M) n g → n.2.val = 1 →
      ∀ z : (Frame.ofMountain M).Node, z.2.val = 1 → g.1.val < z.1.val → z.1.val ≤ n.1.val →
        (Frame.ofMountain M).value g < (Frame.ofMountain M).value z := by
  have hO := (build_normal_of_success hb).toOrdered
  intro n g path
  induction path with
  | refl _ =>
    intro _ z _ h1 h2
    exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)
  | @cons n n1 g hP rest ih =>
    intro hn z hz1 hgz hzn
    obtain ⟨q0, hQ0, hit⟩ := (P_iff hO).mp hP
    have hc := Q_column_lt hO hQ0
    obtain ⟨w, hw, hwc, hw1⟩ := Q_bottom hb hn (by omega)
    have hwq : q0 = w := Option.some.inj (hQ0.symm.trans hw)
    subst hwq
    obtain ⟨hn11, hrej⟩ := hit_bottom hb hit hw1
    have hgn1 := rest.value_le hO
    have hn1n := (P_value hO hP).2
    rcases Nat.lt_or_ge n1.1.val z.1.val with hlt | hge
    · rcases Nat.lt_or_ge z.1.val n.1.val with hzl | hzg
      · have := hrej z hz1 hlt (by omega)
        omega
      · have hzn' : z = n := ControlProof.node_eq_of_index (Fin.ext (by omega)) (by omega)
        subst hzn'
        omega
    · exact ih hn11 z hz1 hgz hge

end Bottom

/-! ## The residual case -/

/-- **Open (about `M(s)` alone).** `RootValue` when the row `C` is not the bottom row and `g`
has a node above it below `τ`. -/
def RootValueHi : Prop :=
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
        co.row ≠ 1 →
        (∃ ca, Reserve.cell? M (Classification.Proofs.ChainCorr.LowerChain.above g) = some ca ∧
          ca.row < t.row) →
        cg.value < co.value

/-! ## `RootValue` from `RootValueHi` -/

variable {M : Mountain}

/-- **`RootValue` from its residual case `RootValueHi`.** -/
theorem rootValue_of_hi (hHi : RootValueHi) : RootValue := by
  intro s M t root hTop x k co l hcx hxx hk hco hlo hl hlr hab hZ pa cpa hpa hcpa hparow hr' g cg
    hgc hcg hgrow
  by_cases hbar : ∃ ca, Reserve.cell? M (Classification.Proofs.ChainCorr.LowerChain.above g) =
      some ca ∧ ca.row < t.row
  · by_cases hC : co.row = 1
    · -- the bottom row
      have hb := hTop.build
      have hN := build_normal_of_success hb
      have hO := hN.toOrdered
      obtain ⟨oN, hoN, hocell⟩ := ControlProof.node_of_cell? hco
      obtain ⟨gN, hgN, hgcell⟩ := ControlProof.node_of_cell? hcg
      have hoh : (Frame.ofMountain M).height oN = 1 := by
        show ((Frame.ofMountain M).cell oN).row = 1; rw [hocell, hC]
      have hgh : (Frame.ofMountain M).height gN = 1 := by
        show ((Frame.ofMountain M).cell gN).row = 1; rw [hgcell, hgrow, hC]
      have hbot : ∀ w : (Frame.ofMountain M).Node, Real w →
          (Frame.ofMountain M).height w = 1 → w.2.val = 1 := by
        intro w hw hw1
        by_contra hn
        have hlen1 : 1 < (Frame.ofMountain M).length w.1 := by
          have := hO.length_ge_two w.1; omega
        have hlt : (⟨1, hlen1⟩ : Fin _) < w.2 := by
          show 1 < w.2.val; unfold Real at hw; omega
        have := hO.rows_strict w.1 hlt
        change ((Frame.ofMountain M).cells w.1 ⟨1, hlen1⟩).row < (Frame.ofMountain M).height w
          at this
        rw [hO.bottom_row w.1 hlen1, hw1] at this
        exact lt_irrefl _ this
      have hoR : Real oN := by
        show 0 < oN.2.val
        have := congrArg Ref.index hoN; simp [Frame.ref] at this; omega
      have hgR : Real gN :=
        Recon.LowerPB.Cone.real_of_one_le_height hO (by rw [hgh])
      have ho1 := hbot oN hoR hoh
      have hg1 := hbot gN hgR hgh
      -- the node below the top of the last column and its parent `r`
      have hrl := hTop.lt
      have hsz : M.size - 1 < M.size := by omega
      have htop := hTop.top
      rw [Array.getElem?_eq_getElem hsz] at htop
      simp only [Option.bind_some, Array.back?] at htop
      obtain ⟨hTi, hTt⟩ := Array.getElem?_eq_some_iff.mp htop
      have hT2 : 2 ≤ M[M.size - 1].size := by
        by_contra hn
        have h1 : M[M.size - 1].size - 1 = 1 := by
          have := hO.length_ge_two ⟨M.size - 1, hsz⟩
          change 2 ≤ M[M.size - 1].size at this
          omega
        have htrow : t.row = 1 := by
          rw [← hTt]
          simp only [h1]
          exact hO.bottom_row ⟨M.size - 1, hsz⟩ (by show 1 < M[M.size - 1].size; omega)
        exact hTop.real (by rw [htrow]; exact Classification.official_one)
      let x0 : Fin (Frame.ofMountain M).width := ⟨M.size - 1, hsz⟩
      have hyl : M[M.size - 1].size - 2 < (Frame.ofMountain M).length x0 := by
        show M[M.size - 1].size - 2 < M[M.size - 1].size
        omega
      let ny : (Frame.ofMountain M).Node := ⟨x0, ⟨M[M.size - 1].size - 2, hyl⟩⟩
      have hT3 : 3 ≤ M[M.size - 1].size := by
        by_contra hn
        have h2 : M[M.size - 1].size = 2 := by omega
        have htrow : t.row = 1 := by
          rw [← hTt]
          simp only [h2]
          exact hO.bottom_row ⟨M.size - 1, hsz⟩ (by show 1 < M[M.size - 1].size; omega)
        exact hTop.real (by rw [htrow]; exact Classification.official_one)
      have hyreal : Frame.Real ny := by show 0 < M[M.size - 1].size - 2; omega
      have hrawy0 : Reserve.rawParent M ⟨M.size - 1, M[M.size - 1].size - 2⟩ = some root := by
        unfold Reserve.rawParent
        rw [Array.getElem?_eq_getElem hsz]
        simp only [Option.bind_eq_bind, Option.bind_some]
        rw [show M[M.size - 1].size - 2 + 1 = M[M.size - 1].size - 1 by omega, htop]
        simpa using hTop.left
      have hrawy : ((Frame.ofMountain M).upper ny).bind
          (fun v => ((Frame.ofMountain M).cell v).left) = some root :=
        (ControlProof.rawParent_ref ny).symm.trans hrawy0
      obtain ⟨nr, hPy, hnr⟩ : ∃ nr, (Frame.ofMountain M).P ny = some nr ∧ Frame.ref nr = root := by
        cases hup : (Frame.ofMountain M).upper ny with
        | none => rw [hup] at hrawy; cases hrawy
        | some up =>
          rw [hup] at hrawy
          simp only [Option.bind_some] at hrawy
          obtain ⟨nr, hlk, _, _⟩ := hO.stored_valid up root hrawy
          have hnr := Frame.lookup_spec hlk
          have hleft : ((Frame.ofMountain M).cell up).left = some (Frame.ref nr) := by
            rw [hnr]; exact hrawy
          refine ⟨nr, ?_, hnr⟩
          rw [← hN.rawParent_eq_P hyreal]
          exact Frame.rawParent_eq_of_upper_left hup hleft
      have hnrR : Real nr := real_of_value_pos hO (P_value hO hPy).1
      have hgcol : gN.1 = nr.1 := by
        apply Fin.ext
        have h1 := congrArg Ref.column hgN
        have h2 := congrArg Ref.column hnr
        simp only [Frame.ref] at h1 h2
        rw [h1, h2, hgc]
      obtain ⟨v, _, hvc, _, hvh, hvpath⟩ := P_rowShadow hN hPy gN hgR hgcol
        (by rw [hgh]; exact one_le_height hO hnrR)
      have hvR : Real v :=
        Recon.LowerPB.Cone.real_of_one_le_height hO (by rw [hvh, hgh])
      have hv1 := hbot v hvR (hvh.trans hgh)
      have hval := bottom_path_value hb hvpath hv1 oN ho1
        (by
          have h1 := congrArg Ref.column hgN
          have h2 := congrArg Ref.column hoN
          simp only [Frame.ref] at h1 h2
          omega)
        (by
          have h2 := congrArg Ref.column hoN
          simp only [Frame.ref] at h2
          have : v.1.val = M.size - 1 := by rw [hvc]
          omega)
      have hgv : (Frame.ofMountain M).value gN = cg.value := by
        show ((Frame.ofMountain M).cell gN).value = _; rw [hgcell]
      have hov : (Frame.ofMountain M).value oN = co.value := by
        show ((Frame.ofMountain M).cell oN).value = _; rw [hocell]
      rw [← hgv, ← hov]
      exact hval
    · exact hHi s M t root hTop x k co l hcx hxx hk hco hlo hl hlr hab hZ pa cpa hpa hcpa hparow
        hr' g cg hgc hcg hgrow hC hbar
  · -- the barrier case
    have hb := hTop.build
    have hN := build_normal_of_success hb
    have hO := hN.toOrdered
    obtain ⟨oN, hoN, hocell⟩ := ControlProof.node_of_cell? hco
    have hoR : Real oN := by
      show 0 < oN.2.val
      have := congrArg Ref.index hoN; simp [Frame.ref] at this; omega
    have hoh : (Frame.ofMountain M).height oN = co.row := by
      show ((Frame.ofMountain M).cell oN).row = co.row; rw [hocell]
    obtain ⟨c', hc', hc't⟩ := hab
    obtain ⟨opN, hopN, hopcell⟩ := ControlProof.node_of_cell? hc'
    have hup : (Frame.ofMountain M).upper oN = some opN :=
      LowerChainRecon.upper_of_above (by rw [hopN, hoN]; rfl)
    obtain ⟨p, hP, _, _, _⟩ := hN.upper_step oN opN hoR hup
    have hl' : ((Frame.ofMountain M).cell oN).left = some l := by rw [hocell]; exact hl
    have hpa' : highestAtMost M l.column ((Frame.ofMountain M).height oN) = some pa := by
      rw [hoh]; exact hpa
    obtain ⟨q, hQ, hq'⟩ := ControlProof.Q_of_highestAtMost hO hl' hpa'
    obtain ⟨paN, hpaN, hpacell⟩ := ControlProof.node_of_cell? hcpa
    have hqpa : q = paN := TSQ.ref_inj' (hq'.trans hpaN.symm)
    subst hqpa
    have hpaR : Real q := Q_real hO hoR hQ
    have hpah : (Frame.ofMountain M).height q = (Frame.ofMountain M).height oN := by
      show ((Frame.ofMountain M).cell q).row = _; rw [hpacell, hparow, hoh]
    obtain ⟨r, hrc, hrh, hpath⟩ :=
      LowerPB.LiftLegPf.reach_path hb (l.column + 1) q hpaR (by rw [hq']; exact hr')
    obtain ⟨gN, hgN, hgcell⟩ := ControlProof.node_of_cell? hcg
    have hrg : r = gN := by
      apply node_eq_of_column_height hO
      · exact Fin.ext (by rw [hrc, ← hgc]; exact (congrArg Ref.column hgN).symm)
      · show (Frame.ofMountain M).height r = ((Frame.ofMountain M).cell gN).row
        rw [hrh, hpah, hgcell, hgrow, hoh]
    subst hrg
    have hgh : (Frame.ofMountain M).height r = (Frame.ofMountain M).height oN := hrh.trans hpah
    have hrR : Real r :=
      Recon.LowerPB.Cone.real_of_one_le_height hO (by rw [hgh]; exact one_le_height hO hoR)
    have hopr : (Frame.ofMountain M).height opN = c'.row := by
      show ((Frame.ofMountain M).cell opN).row = _; rw [hopcell]
    have habove : (Frame.ofMountain M).aboveHeight oN < t.row := by
      rw [aboveHeight_of_upper hup, hopr]; exact hc't
    have hoop : (Frame.ofMountain M).height oN < (Frame.ofMountain M).height opN := by
      obtain ⟨hc1, hc2⟩ := upper_spec hup
      exact ControlProof.height_lt_of_index hO hc1.symm (by omega)
    have hcap : Row.bump ((Frame.ofMountain M).height r) 0 < t.row := by
      rw [hgh]
      exact lt_of_le_of_lt (LowerPB.LiftLegPf.bump0_le_of_lt hoop) (by rw [hopr]; exact hc't)
    have hbar' : ∀ up, (Frame.ofMountain M).upper r = some up →
        t.row ≤ (Frame.ofMountain M).height up := by
      intro up hup'
      by_contra hn
      apply hbar
      refine ⟨(Frame.ofMountain M).cell up, ?_, lt_of_not_ge hn⟩
      have href := LowerChainRecon.above_of_upper hup'
      rw [← hgN, ← href]
      exact ControlProof.cell?_ref up
    have hval := value_lt_of_barrier hN hP hQ hpah hgh hpath hrR hbar' hcap habove
    have hgv : (Frame.ofMountain M).value r = cg.value := by
      show ((Frame.ofMountain M).cell r).value = _; rw [hgcell]
    have hov : (Frame.ofMountain M).value oN = co.value := by
      show ((Frame.ofMountain M).cell oN).value = _; rw [hocell]
    rw [← hgv, ← hov]
    exact hval

/-- **`TopStartPaOUp` from `RootValueHi`.** -/
theorem topStartPaOUp_of_rootValueHi (hHi : RootValueHi) : TopStartFixParts.TopStartPaOUp :=
  topStartPaOUp_of_rootValue (rootValue_of_hi hHi)

end OmegaY.Official.Recon.TSQ.RVP

#print axioms OmegaY.Official.Recon.TSQ.RVP.value_lt_of_barrier
#print axioms OmegaY.Official.Recon.TSQ.RVP.Q_bottom
#print axioms OmegaY.Official.Recon.TSQ.RVP.hit_bottom
#print axioms OmegaY.Official.Recon.TSQ.RVP.bottom_path_value
#print axioms OmegaY.Official.Recon.TSQ.RVP.rootValue_of_hi
#print axioms OmegaY.Official.Recon.TSQ.RVP.topStartPaOUp_of_rootValueHi
