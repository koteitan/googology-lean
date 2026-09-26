/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/StartRootPartsX0.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StartRootPartsOriginLower
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainsCanonParent

set_option backward.do.legacy false

/-!
# `X0Reach` (proved)

`X0Reach` (`StartRootPartsOriginLower.lean`) is a statement about the canonical mountain
`M = M(s)` alone: for a node `ν` of the last column `x₀` below its top `t`, and `q` the highest
node of the root column `cr` at or below the row of `ν`, the scale-`k` chain of `ν` reaches the
next node `m''` of the scale-`k` chain of `q`.

## The proof

Write `P` for the numerical parent (the raw parent of a real node) and say that the `P`-chain of
`z` *hits* column `a` when some node of the chain of `z` is in column `a`.

1. **Hitting is inherited downward in a column** (`hits_down`). If `y` and `w` are in the same
   column `c`, `w` at or below `y`, and the chain of `y` hits a column `a < c`, then so does the
   chain of `w`. Induction on `c`, then on the distance from `w` to `y`. For `w' = w⁺` (at or
   below `y`, so its chain hits `a`) and `x = P w`, the search for `P w'` starts at
   `Q w' ∈ {x, x⁺}` (`candidate_after_upper`), and `P w'` is on the `P`-chain of `Q w'`
   (`Hit.parentPath`). If `Q w' = x`, the chain of `x` hits `a`. If `Q w' = x⁺`, the chain of
   `x⁺` hits `a`, and `x` is below `x⁺` in the column of `x` (left of `c`): induction.
2. **A node of a chain is the highest of its column below the upper node** (`path_above_le`).
   If `P w = x` and `L` is on the chain of `x` with an upper node `L⁺`, then
   `row w⁺ ≤ row L⁺` (Phyrion's father upper bound, iterated). So `L` is the highest node of its
   column at or below any row in `[row L, row w⁺)`.
3. **`X0Reach`.** The node `y` just below `t` has `P y = root`, in column `cr`. By 1 the chain of
   `ν` hits `cr` at a node `L`, and by 2 `L = q`. Every node on the chain from `ν` to `q` has its
   row in `[row q, row ν] ⊆ [row q, row q⁺)` with `row q⁺ = B(row q, row m'') =
   bump(row q, jump(row q, row m''))` (2 again), so every step has jump at most
   `jump(row q, row m'') ≤ k`. Then one more step `q → m''`.

The numerical form of 1–2 (for every edge `u → u⁺` of `M(s)` with parent `p` and every `w` at or
below `u`, the chain of `w` lands in the column of `p` exactly at the highest node at or below
the row of `w`) was checked before the proof (see the report of this change).
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.SRX0

open Canonical Reserve Official Descent Classification Proofs
open Geometry
open ChainCorr.Inner

/-! ## In a normal frame -/

section FrameHits

variable {F : Geometry.Frame}

/-- The numerical-parent chain of `z` meets column `a`. -/
def Hits (F : Geometry.Frame) (z : F.Node) (a : Nat) : Prop :=
  ∃ L : F.Node, Frame.ParentPath F z L ∧ L.1.val = a

theorem hits_cons {w x : F.Node} {a : Nat} (hp : F.P w = some x) (h : Hits F x a) :
    Hits F w a := by
  obtain ⟨L, hL, hLa⟩ := h
  exact ⟨L, .cons hp hL, hLa⟩

theorem path_value_pos (hF : F.Ordered) {x L : F.Node} (path : Frame.ParentPath F x L)
    (hx : 0 < F.value x) : 0 < F.value L := by
  induction path with
  | refl => exact hx
  | cons hp _ ih => exact ih (Frame.P_value hF hp).1

/-- **Hitting a column is inherited downward in a column.** -/
theorem hits_down (hF : F.Normal) {a : Nat} :
    ∀ c, ∀ (y w : F.Node), y.1.val = c → w.1 = y.1 → Frame.Real w →
      w.2.val ≤ y.2.val → a < c → Hits F y a → Hits F w a := by
  intro c
  induction c using Nat.strongRecOn with
  | ind c outer =>
    intro y w hyc hwy hw hle hac hy
    obtain ⟨n, hn⟩ : ∃ n, y.2.val = w.2.val + n := ⟨y.2.val - w.2.val, by omega⟩
    clear hle
    induction n generalizing w with
    | zero =>
      have : w = y := ControlProof.node_eq_of_index hwy (by omega)
      subst this
      exact hy
    | succ n ih =>
      have hlen : w.2.val + 1 < F.length w.1 := by
        have h1 := y.2.isLt
        have h2 : F.length w.1 = F.length y.1 := by rw [hwy]
        omega
      let w' : F.Node := ⟨w.1, ⟨w.2.val + 1, hlen⟩⟩
      have hup : F.upper w = some w' := ControlProof.upper_eq_of_index rfl rfl
      have hw'real : Frame.Real w' := by
        show 0 < w.2.val + 1
        omega
      have hw' : Hits F w' a := ih w' hwy hw'real (by show y.2.val = w.2.val + 1 + n; omega)
      obtain ⟨x, hPx, _, _, _⟩ := hF.upper_step w w' hw hup
      obtain ⟨L, hpath, hLa⟩ := hw'
      have hw'c : w'.1.val = c := by rw [← hyc, ← hwy]
      cases hpath with
      | refl => omega
      | @cons _ p' _ hP' rest =>
        obtain ⟨qq, hQ, hit⟩ := (Frame.P_iff hF.toOrdered).mp hP'
        have hqreal := Frame.Q_real hF.toOrdered hw'real hQ
        have hqpath := hit.parentPath hF.toOrdered (hF.real_positive qq hqreal)
        have hqL := hqpath.trans rest
        rcases Frame.candidate_after_upper hF hPx hup with hsame | ⟨xp, hxp, _, hsame⟩
        · have he : qq = x := Option.some.inj (hQ.symm.trans hsame)
          subst he
          exact hits_cons hPx ⟨L, hqL, hLa⟩
        · have he : qq = xp := Option.some.inj (hQ.symm.trans hsame)
          subst he
          have hxpc : qq.1 = x.1 := (Frame.upper_spec hxp).1
          have hxpi : qq.2.val = x.2.val + 1 := (Frame.upper_spec hxp).2
          have hxc : x.1.val < c := by
            have := Frame.P_column_lt hF.toOrdered hPx
            rw [hwy, hyc] at this
            exact this
          have haq : a ≤ qq.1.val := by
            have := hqL.column_le hF.toOrdered
            omega
          rw [hxpc] at haq
          rcases Nat.lt_or_eq_of_le haq with hlt | heq
          · have hxreal : Frame.Real x :=
              Frame.real_of_value_pos hF.toOrdered (Frame.P_value hF.toOrdered hPx).1
            exact hits_cons hPx (outer x.1.val hxc qq x (by rw [hxpc]) hxpc.symm hxreal
              (by omega) hlt ⟨L, hqL, hLa⟩)
          · exact ⟨x, .cons hPx (.refl x), heq.symm⟩

/-- Iterated father upper bound along a chain. -/
theorem path_above_le' (hF : F.Normal) {x L : F.Node} (path : Frame.ParentPath F x L)
    (hL : 1 < F.value L) : F.aboveHeight x ≤ F.aboveHeight L := by
  induction path with
  | refl => exact le_rfl
  | cons hp rest ih =>
    exact (Frame.father_upper_bound hF hp
      (lt_of_lt_of_le hL (rest.value_le hF.toOrdered))).trans (ih hL)

/-- **A node `L` of the chain of `P w` with an upper node lies at or above `w⁺`.** -/
theorem path_above_le (hF : F.Normal) {w x L Lp : F.Node} (hp : F.P w = some x)
    (path : Frame.ParentPath F x L) (hLp : F.upper L = some Lp) :
    F.aboveHeight w ≤ F.height Lp := by
  have hxpos := (Frame.P_value hF.toOrdered hp).1
  have hLreal := Frame.real_of_value_pos hF.toOrdered (path_value_pos hF.toOrdered path hxpos)
  have hLval := hF.upper_nontrivial L Lp hLreal hLp
  have h1 := Frame.father_upper_bound hF hp (lt_of_lt_of_le hLval (path.value_le hF.toOrdered))
  rw [← Frame.aboveHeight_of_upper hLp]
  exact h1.trans (path_above_le' hF path hLval)

/-- The row of a node with a parent is below its upper row. -/
theorem height_lt_above (hF : F.Normal) {w x : F.Node} (hp : F.P w = some x) :
    F.height w < F.aboveHeight w := by
  obtain ⟨v, hv⟩ := hF.upper_of_parent hp
  rw [Frame.aboveHeight_of_upper hv]
  obtain ⟨hc, hi⟩ := Frame.upper_spec hv
  exact ControlProof.height_lt_of_index hF.toOrdered hc.symm (by omega)

/-- **The highest node.** A node `L` on the chain of `P w` is the highest node of its column
at or below the row of `w`. -/
theorem path_highest (hF : F.Normal) {w x L z : F.Node} (hp : F.P w = some x)
    (path : Frame.ParentPath F x L) (hz : z.1 = L.1) (hzh : F.height z ≤ F.height w) :
    z.2.val ≤ L.2.val := by
  by_contra hn
  have hlen : L.2.val + 1 < F.length L.1 := by
    have h1 := z.2.isLt
    have h2 : F.length z.1 = F.length L.1 := by rw [hz]
    omega
  let Lp : F.Node := ⟨L.1, ⟨L.2.val + 1, hlen⟩⟩
  have hLp : F.upper L = some Lp := ControlProof.upper_eq_of_index rfl rfl
  have h1 := path_above_le hF hp path hLp
  have h2 : F.height Lp ≤ F.height z :=
    ControlProof.height_le_of_index hF.toOrdered hz.symm (by show L.2.val + 1 ≤ z.2.val; omega)
  have h3 := height_lt_above hF hp
  exact absurd (lt_of_lt_of_le h3 (h1.trans (h2.trans hzh))) (lt_irrefl _)

end FrameHits

/-! ## In the executable canonical mountain -/

section Mountain

variable {M : Mountain}

theorem reserve_rawParent_of_frame {u p : (Frame.ofMountain M).Node}
    (h : (Frame.ofMountain M).rawParent u = some p) :
    Reserve.rawParent M (Frame.ref u) = some (Frame.ref p) := by
  obtain ⟨up, hup, hleft⟩ := Frame.rawParent_spec h
  rw [ControlProof.rawParent_ref, hup]
  simpa only [Option.bind_some] using hleft

/-- A chain of numerical parents whose rows stay in `[row L, bump (row L) d)` is a scale-`k`
chain for every `k ≥ d`. -/
theorem reach_of_path (hF : (Frame.ofMountain M).Normal) {k d : Nat} {L : (Frame.ofMountain M).Node}
    (hdk : d ≤ k) :
    ∀ {u : (Frame.ofMountain M).Node}, Frame.ParentPath (Frame.ofMountain M) u L →
      Frame.Real u →
      (Frame.ofMountain M).height u < Row.bump ((Frame.ofMountain M).height L) d →
      ScaleReach M k (Frame.ref u) (Frame.ref L) := by
  intro u path
  induction path with
  | refl => intro _ _; exact ScaleReach.refl _
  | @cons u z L' hp rest ih =>
    intro hu hub
    have hO := hF.toOrdered
    have hzh : (Frame.ofMountain M).height z ≤ (Frame.ofMountain M).height u :=
      Frame.P_height_le hO hp
    have hLz := rest.height_le hO
    have hzreal : Frame.Real z := Frame.real_of_value_pos hO (Frame.P_value hO hp).1
    have hraw : (Frame.ofMountain M).rawParent u = some z := (hF.rawParent_eq_P hu).trans hp
    have hj1 : Row.jump ((Frame.ofMountain M).height L') ((Frame.ofMountain M).height u) ≤ d :=
      Row.jump_le_of_lt_bump (hLz.trans hzh) hub
    have hj2 := (Row.jump_le_between hLz hzh hj1).2
    refine ScaleReach.step (reserve_rawParent_of_frame hraw) (ControlProof.cell?_ref u)
      (ControlProof.cell?_ref z) ?_ (Frame.P_column_lt hO hp) (ih hzreal (lt_of_le_of_lt hzh hub))
    rw [Row.jump_comm]
    exact hj2.trans hdk

end Mountain

/-! ## `X0Reach` -/

/-- **`X0Reach` holds.** -/
theorem x0Reach : SRParts.X0Reach := by
  intro s M t root hTop ν cν hνc hν1 hcν hlt q hq kk m'' hst
  obtain ⟨νc, νi⟩ := ν
  simp only at hνc hν1
  subst hνc
  have hB := hTop.build
  have hF : (Frame.ofMountain M).Normal := build_normal_of_success hB
  have hO := hF.toOrdered
  -- the last column and its top
  have hrl := hTop.lt
  have hsz : M.size - 1 < M.size := by omega
  have htop := hTop.top
  rw [Array.getElem?_eq_getElem hsz] at htop
  simp only [Option.bind_some, Array.back?] at htop
  obtain ⟨hTi, hTt⟩ := Array.getElem?_eq_some_iff.mp htop
  -- `ν` in the last column
  obtain ⟨_, hνi, hνcell⟩ := canon_cell?_some_iff.mp hcν
  have hνi' : νi < M[M.size - 1].size := hνi
  have hνT : νi + 1 < M[M.size - 1].size := by
    by_contra hn
    have hνe : νi = M[M.size - 1].size - 1 := by omega
    have h1 : M[M.size - 1][νi]? = some cν := by
      rw [Array.getElem?_eq_getElem hνi']
      exact congrArg some hνcell
    rw [hνe, htop] at h1
    have : t = cν := Option.some.inj h1
    subst this
    exact lt_irrefl _ hlt
  -- the node `y` just below `t`
  let x0 : Fin (Frame.ofMountain M).width := ⟨M.size - 1, hsz⟩
  have hyl : M[M.size - 1].size - 2 < (Frame.ofMountain M).length x0 := by
    show M[M.size - 1].size - 2 < M[M.size - 1].size
    omega
  let ny : (Frame.ofMountain M).Node := ⟨x0, ⟨M[M.size - 1].size - 2, hyl⟩⟩
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
  have hyP : ∃ nr, (Frame.ofMountain M).P ny = some nr ∧ Frame.ref nr = root := by
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
      rw [← hF.rawParent_eq_P hyreal]
      exact Frame.rawParent_eq_of_upper_left hup hleft
  obtain ⟨nr, hPy, hnr⟩ := hyP
  let nν : (Frame.ofMountain M).Node := ⟨x0, ⟨νi, hνi'⟩⟩
  have hνref : Frame.ref nν = ⟨M.size - 1, νi⟩ := rfl
  have hνreal : Frame.Real nν := by show 0 < νi; omega
  have hcr : root.column < M.size - 1 := hrl
  have hhit : Hits (Frame.ofMountain M) nν root.column := by
    have hy : Hits (Frame.ofMountain M) ny root.column :=
      ⟨nr, .cons hPy (.refl nr), by rw [← hnr]; rfl⟩
    exact hits_down hF (M.size - 1) ny nν rfl rfl hνreal
      (by show νi ≤ M[M.size - 1].size - 2; omega) hcr hy
  obtain ⟨L, hpath, hLc⟩ := hhit
  cases hpath with
  | refl =>
    have : (M.size - 1 : Nat) = root.column := hLc
    omega
  | @cons _ x _ hPν rest =>
    -- `L` is `q`
    have hLh : (Frame.ofMountain M).height L ≤ (Frame.ofMountain M).height nν :=
      (rest.height_le hO).trans (Frame.P_height_le hO hPν)
    have hνcell' : (Frame.ofMountain M).cell nν = cν := hνcell
    have hLreal : Frame.Real L := Frame.real_of_value_pos hO
      (path_value_pos hO rest (Frame.P_value hO hPν).1)
    have hqL : q = Frame.ref L := by
      have hL' : highestAtMost M root.column cν.row = some (Frame.ref L) := by
        refine highestAtMost_of_max (cp := (Frame.ofMountain M).cell L) hLc hLreal
          (ControlProof.cell?_ref L) ?_ ?_
        · rw [← hνcell']; exact hLh
        · intro j c hjc hj0 hjrow
          obtain ⟨hc', hj', hcell⟩ := canon_cell?_some_iff.mp hjc
          let z : (Frame.ofMountain M).Node := ⟨⟨root.column, hc'⟩, ⟨j, hj'⟩⟩
          have hz : z.1 = L.1 := Fin.ext hLc.symm
          have := path_highest hF hPν rest hz (by
            show (M[root.column][j]).row ≤ ((Frame.ofMountain M).cell nν).row
            rw [hcell, hνcell']; exact hjrow)
          exact this
      rw [hL'] at hq
      exact (Option.some.inj hq).symm
    subst hqL
    -- the upper node of `q` and the bound on the rows
    obtain ⟨hrawq, cq, cm, hcq, hcm, hjq, hmcol⟩ := hst
    have hq' : ∃ nm, (Frame.ofMountain M).rawParent L = some nm ∧ Frame.ref nm = m'' := by
      rw [ControlProof.rawParent_ref] at hrawq
      cases hup : (Frame.ofMountain M).upper L with
      | none => rw [hup] at hrawq; cases hrawq
      | some up =>
        rw [hup] at hrawq
        simp only [Option.bind_some] at hrawq
        obtain ⟨nm, hlk, _, _⟩ := hO.stored_valid up m'' hrawq
        have hnm := Frame.lookup_spec hlk
        have hleft : ((Frame.ofMountain M).cell up).left = some (Frame.ref nm) := by
          rw [hnm]; exact hrawq
        exact ⟨nm, Frame.rawParent_eq_of_upper_left hup hleft, hnm⟩
    obtain ⟨nm, hrawL, hnm⟩ := hq'
    obtain ⟨Lp, hLp⟩ : ∃ Lp, (Frame.ofMountain M).upper L = some Lp := by
      cases hup : (Frame.ofMountain M).upper L with
      | none => rw [Frame.rawParent_none_of_upper_none hup] at hrawL; cases hrawL
      | some Lp => exact ⟨Lp, rfl⟩
    obtain ⟨_, hLpB⟩ := hF.raw_B hLreal hLp hrawL
    have habove := path_above_le hF hPν rest hLp
    have hbelow := height_lt_above hF hPν
    have hcqL : cq = (Frame.ofMountain M).cell L := by
      have := ControlProof.cell?_ref L
      rw [hcq] at this
      exact Option.some.inj this
    have hcmn : cm = (Frame.ofMountain M).cell nm := by
      have := ControlProof.cell?_ref nm
      rw [hnm, hcm] at this
      exact Option.some.inj this
    have hbump : (Frame.ofMountain M).height nν <
        Row.bump ((Frame.ofMountain M).height L)
          (Row.jump ((Frame.ofMountain M).height L) ((Frame.ofMountain M).height nm)) := by
      have := lt_of_lt_of_le hbelow habove
      rw [hLpB] at this
      exact this
    have hjk : Row.jump ((Frame.ofMountain M).height L) ((Frame.ofMountain M).height nm) ≤ kk := by
      have := hjq
      rw [hcqL, hcmn] at this
      exact this
    have hreach := reach_of_path hF hjk (.cons hPν rest) hνreal hbump
    rw [hνref] at hreach
    exact ScaleReach.trans hreach
      (MStep.reach ⟨hrawq, cq, cm, hcq, hcm, hjq, hmcol⟩)

end OmegaY.Official.Classification.Proofs.ChainCorr.SRX0

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.SRX0.hits_down
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.SRX0.x0Reach
