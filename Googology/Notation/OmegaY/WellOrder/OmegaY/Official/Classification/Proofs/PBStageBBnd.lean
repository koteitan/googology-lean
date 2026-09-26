/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/PBStageBBnd.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.PBStageBChildren

set_option backward.do.legacy false

/-!
# Tools for the boundary column (stage B)

Facts about `M(s)` and about the item trees used for the boundary column `B = c_r + w·i`:

* `below_bump`: consecutive nodes of a column: the upper row is a bump of the lower row;
  `bottom_official`: the bottom node has the official row `0`; `col0_only`: the first column has
  only its bottom node.
* `topBump`: the top row `τ` of the last column is `bump a J` for the row `a` of the node below
  the top, and `a` agrees with the root row above `J`.
* `fill`: a column has a node in every slot of a region at or below the slot of any of its nodes.
* `children_target`, `runItemT_target`: an item emits only rows of its target region.
* `coverAll`: a gap-copy item (or a cut-bottom item) of a copy of a column that has the needed
  nodes emits every row of the boundary column in its target region.
-/

namespace OmegaY.Official.Classification.Proofs.CopyShape.PBStageB

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr ChainCorr.CopyMonoProof

/-! ## Consecutive nodes of a column -/

section Frame

open Geometry Geometry.Frame

variable {s : List Nat} {M : Mountain}

theorem below_bump (hb : Canonical.build s = .ok M) {c k : Nat} {cu : Cell} (hk : 2 ≤ k)
    (hcu : cell? M ⟨c, k⟩ = some cu) :
    ∃ cl J, cell? M ⟨c, k - 1⟩ = some cl ∧ (1 : Row) ≤ cl.row ∧
      official cu.row = Row.bump (official cl.row) J := by
  have hN := build_normal_of_success hb
  have hO := hN.toOrdered
  obtain ⟨hc, hki, hkc⟩ := Proofs.canon_cell?_some_iff.mp hcu
  let nv : (Frame.ofMountain M).Node := ⟨⟨c, hc⟩, ⟨k, hki⟩⟩
  let nu : (Frame.ofMountain M).Node :=
    ⟨⟨c, hc⟩, ⟨k - 1, by change k - 1 < M[c].size; have : k < M[c].size := hki; omega⟩⟩
  have hnu : Frame.Real nu := by show 0 < k - 1; omega
  have hup : (Frame.ofMountain M).upper nu = some nv :=
    ControlProof.upper_eq_of_index rfl (show k = k - 1 + 1 by omega)
  obtain ⟨p, _, hh, _, _⟩ := hN.upper_step nu nv hnu hup
  have h1 : (1 : Row) ≤ (Frame.ofMountain M).height nu := Frame.one_le_height hO hnu
  refine ⟨(Frame.ofMountain M).cell nu, Row.jump ((Frame.ofMountain M).height nu)
    ((Frame.ofMountain M).height p), ControlProof.cell?_ref nu, h1, ?_⟩
  have hnvc : (Frame.ofMountain M).cell nv = cu := hkc
  have : cu.row = Row.bump ((Frame.ofMountain M).cell nu).row
      (Row.jump ((Frame.ofMountain M).height nu) ((Frame.ofMountain M).height p)) := by
    rw [← hnvc]; exact hh
  rw [this]
  exact Recon.RowLaw.official_bump h1 _

theorem bottom_official (hb : Canonical.build s = .ok M) {c : Nat} {cb : Cell}
    (h : cell? M ⟨c, 1⟩ = some cb) : official cb.row = 0 := by
  have hO := (build_normal_of_success hb).toOrdered
  obtain ⟨hc, hki, hkc⟩ := Proofs.canon_cell?_some_iff.mp h
  have hrow : cb.row = 1 := by rw [← hkc]; exact hO.bottom_row ⟨c, hc⟩ hki
  rw [hrow]
  decide

/-- **The first column has only its bottom node.** -/
theorem col0_only (hb : Canonical.build s = .ok M) {k : Nat} {c : Cell}
    (h : cell? M ⟨0, k⟩ = some c) (hk : 1 ≤ k) : k = 1 := by
  by_contra hne
  have hN := build_normal_of_success hb
  have hV := build_valid_of_success hb
  obtain ⟨hc, hki, _⟩ := Proofs.canon_cell?_some_iff.mp h
  let nv : (Frame.ofMountain M).Node := ⟨⟨0, hc⟩, ⟨k, hki⟩⟩
  let nu : (Frame.ofMountain M).Node :=
    ⟨⟨0, hc⟩, ⟨k - 1, by change k - 1 < M[0].size; have : k < M[0].size := hki; omega⟩⟩
  have hnu : Frame.Real nu := by show 0 < k - 1; omega
  have hup : (Frame.ofMountain M).upper nu = some nv :=
    ControlProof.upper_eq_of_index rfl (show k = k - 1 + 1 by omega)
  have h1 := hN.upper_nontrivial nu nv hnu hup
  have h2 := MountainValid.first_values hV nu hnu rfl
  omega

end Frame

/-! ## The top row of the last column -/

section TopRow

open Geometry Geometry.Frame

/-- **The top row `τ` is a bump of the row below it, which agrees with the root row above the
jump.** -/
theorem topBump {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}
    (hTop : Recon.Top s M t root) :
    ∃ (rc : Cell) (a : Row) (J : Nat), cell? M root = some rc ∧ 1 ≤ root.index ∧
      official t.row = Row.bump a J ∧ (∀ q, J ≤ q → a.coeff q = (official rc.row).coeff q) ∧
      official rc.row ≤ a := by
  have hb := hTop.build
  have hN := build_normal_of_success hb
  have hO := hN.toOrdered
  obtain ⟨k, hk, htk⟩ := Recon.LowerPB.top_node hTop
  have hk2 : 2 ≤ k := by
    by_contra hn
    have hk1 : k = 1 := by omega
    subst hk1
    exact hTop.real (bottom_official hb htk)
  obtain ⟨hc, hki, hkc⟩ := Proofs.canon_cell?_some_iff.mp htk
  let nt : (Frame.ofMountain M).Node := ⟨⟨M.size - 1, hc⟩, ⟨k, hki⟩⟩
  let nu : (Frame.ofMountain M).Node :=
    ⟨⟨M.size - 1, hc⟩, ⟨k - 1, by
      change k - 1 < M[M.size - 1].size; have : k < M[M.size - 1].size := hki; omega⟩⟩
  have hnu : Frame.Real nu := by show 0 < k - 1; omega
  have hup : (Frame.ofMountain M).upper nu = some nt :=
    ControlProof.upper_eq_of_index rfl (show k = k - 1 + 1 by omega)
  obtain ⟨p, hP, hh, _, hleft⟩ := hN.upper_step nu nt hnu hup
  have hntc : (Frame.ofMountain M).cell nt = t := hkc
  have hroot : Frame.ref p = root := by
    rw [hntc, hTop.left] at hleft
    exact (Option.some.inj hleft).symm
  have hp : Frame.Real p := real_of_value_pos hO (P_value hO hP).1
  have h1 : (1 : Row) ≤ (Frame.ofMountain M).height nu := Frame.one_le_height hO hnu
  have h1p : (1 : Row) ≤ (Frame.ofMountain M).height p := Frame.one_le_height hO hp
  refine ⟨(Frame.ofMountain M).cell p, official ((Frame.ofMountain M).cell nu).row,
    Row.jump ((Frame.ofMountain M).height nu) ((Frame.ofMountain M).height p), ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hroot]; exact ControlProof.cell?_ref p
  · rw [← hroot]; exact hp
  · have : t.row = Row.bump ((Frame.ofMountain M).cell nu).row
        (Row.jump ((Frame.ofMountain M).height nu) ((Frame.ofMountain M).height p)) := by
      rw [← hntc]; exact hh
    rw [this]
    exact Recon.RowLaw.official_bump h1 _
  · intro q hq
    have hag := Row.jump_le_iff.mp (le_refl (Row.jump ((Frame.ofMountain M).height nu)
      ((Frame.ofMountain M).height p))) q hq
    rcases Nat.eq_zero_or_pos q with rfl | hq1
    · have hJ : Row.jump ((Frame.ofMountain M).height nu) ((Frame.ofMountain M).height p) = 0 := by
        omega
      have heq := Row.jump_eq_zero.mp hJ
      show (official ((Frame.ofMountain M).cell nu).row).coeff 0 =
        (official ((Frame.ofMountain M).cell p).row).coeff 0
      have : ((Frame.ofMountain M).cell nu).row = ((Frame.ofMountain M).cell p).row := heq
      rw [this]
    · rw [Recon.coeff_official_pos _ hq1, Recon.coeff_official_pos _ hq1]
      exact hag
  · exact Recon.official_mono h1p (P_height_le hO hP)

end TopRow

/-! ## Nodes in the slots below a node -/

/-- **A column has a node in every slot at or below the slot of one of its nodes.** -/
theorem fill {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M) {c d : Nat}
    {S : Row} :
    ∀ (k : Nat) (cu : Cell), 1 ≤ k → cell? M ⟨c, k⟩ = some cu →
      inRegion (d + 2) S (official cu.row) = true →
      ∀ j, j ≤ (official cu.row).coeff d →
        ∃ q ∈ realNodes M c, inRegion (d + 1) (slot (d + 2) S j) (official q.2.row) = true := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro cu hk hcu hin j hj
    rcases Nat.lt_or_eq_of_le hj with hlt | heq
    · rcases Nat.lt_or_ge k 2 with hk1 | hk2
      · have hk1' : k = 1 := by omega
        subst hk1'
        rw [bottom_official hb hcu] at hlt
        simp at hlt
      · obtain ⟨cl, J, hcl, _, hrow⟩ := below_bump hb hk2 hcu
        have hJ : J ≤ d := by
          by_contra hn
          rw [hrow, Recon.RowLaw.bump_coeff_low (by omega)] at hlt
          omega
        have hinl : inRegion (d + 2) S (official cl.row) = true := by
          rw [Recon.RowLaw.inRegion_iff'] at hin ⊢
          intro q hq
          rw [← hin q hq, hrow, Recon.RowLaw.bump_coeff_high (by omega)]
        have hjl : j ≤ (official cl.row).coeff d := by
          rw [hrow] at hlt
          rcases Nat.lt_or_eq_of_le hJ with hJl | hJe
          · rw [Recon.RowLaw.bump_coeff_high hJl] at hlt; omega
          · subst hJe; rw [Recon.RowLaw.bump_coeff_at] at hlt; omega
        exact ih (k - 1) (by omega) cl (by omega) hcl hinl j hjl
    · refine ⟨(⟨c, k⟩, cu), mem_realNodes_of_cell' (p := ⟨c, k⟩) hcu hk, ?_⟩
      exact Recon.RowLaw.inRegion_slot_iff.mpr ⟨hin, heq.symm⟩

/-! ## Emits lie in the target of their item -/

theorem children_target {ctx : Context} {d : Nat} {it : Item} {cs : List Item}
    (h : ChildCase ctx d it cs) : ∀ c ∈ cs, ∃ j, c.target = slot (d + 2) it.target j := by
  intro c hc
  cases h with
  | none _ => simp at hc
  | case1 a ha hasc hcl hoff hcb =>
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
      exact ⟨j, rfl⟩
  | case2 a ha ρr ρc hρ hasc hcl hcb L e hL he =>
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
      refine ⟨j, ?_⟩
      unfold c2
      split_ifs <;> rfl
  | case3 a ha ρr ρc hρ hasc hcl hcb e he =>
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
      refine ⟨j - height (d + 2) (official ρc.row), ?_⟩
      unfold c3
      split_ifs <;> rfl
  | case4 a ha ρr ρc hρ hasc C hcl csRef cs0 hcs g hg hbnd =>
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
      refine ⟨j, ?_⟩
      unfold c4
      split_ifs <;> rfl

theorem levelOneT_target {ctx : Context} {it : Item} {ps : List (Emit × Origin)}
    (h : levelOneT ctx it = .ok ps) : ∀ p ∈ ps, p.1.row = it.target := by
  unfold levelOneT at h
  cases hsrc : nodeAt ctx.source ctx.x it.source with
  | none => simp [hsrc, pure, Except.pure] at h; subst h; simp
  | some q =>
      simp only [hsrc] at h
      cases hC : it.clean with
      | some C =>
          simp only [hC] at h
          cases hcs : nodeAt ctx.source ctx.x C with
          | none => simp [hcs, throw, throwThe, MonadExceptOf.throw] at h
          | some q' =>
              simp only [hcs, bind, Except.bind, pure, Except.pure] at h
              split at h
              · cases h
              · cases h; intro p hp; simp only [List.mem_singleton] at hp; subst hp; rfl
      | none =>
          simp only [hC] at h
          split at h
          · simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h; intro p hp; simp only [List.mem_singleton] at hp; subst hp; rfl
          · simp only [bind, Except.bind, pure, Except.pure] at h
            split at h
            · cases h
            · cases h; intro p hp; simp only [List.mem_singleton] at hp; subst hp; rfl

theorem runItemT_step' {ctx : Context} {d : Nat} {it : Item} {ps : List (Emit × Origin)}
    (h : runItemT ctx (d + 2) it = .ok ps) :
    ∃ cs outs, childItems ctx (d + 2) it = .ok cs ∧ cs.mapM (runItemT ctx (d + 1)) = .ok outs ∧
      ps = outs.flatten := by
  simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i cs hcs
    split at h
    · cases h
    · rename_i outs houts
      cases h
      exact ⟨cs, outs, hcs, houts, rfl⟩

/-- **The emits of an item lie in its target region.** -/
theorem runItemT_target (ctx : Context) :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), runItemT ctx (d + 1) it = .ok ps →
      ∀ p ∈ ps, inRegion (d + 1) it.target p.1.row = true
  | 0, it, ps, h => by
      intro p hp
      rw [levelOneT_target (by simpa [runItemT] using h) p hp]
      exact inRegion_self 1 it.target
  | d + 1, it, ps, h => by
      intro p hp
      obtain ⟨cs, outs, hch, hm, rfl⟩ := runItemT_step' h
      obtain ⟨out, hout, hpo⟩ := List.mem_flatten.mp hp
      obtain ⟨c, hc, hcout⟩ := mem_of_mapM hm hout
      have h1 := runItemT_target ctx d c out hcout p hpo
      obtain ⟨j, hj⟩ := children_target (childItems_cases hch) c hc
      rw [hj] at h1
      exact Recon.RowLaw.inRegion_of_slot h1

/-- A level-one item whose source row (and copied row) is a node of the column emits its
target row. -/
theorem levelOne_emits_target {ctx : Context} {it : Item} {ps : List (Emit × Origin)}
    (h : levelOneT ctx it = .ok ps) (hs : ∃ q, nodeAt ctx.source ctx.x it.source = some q) :
    ∃ p ∈ ps, p.1.row = it.target := by
  obtain ⟨q, hq⟩ := hs
  unfold levelOneT at h
  rw [hq] at h
  simp only at h
  cases hC : it.clean with
  | some C =>
      simp only [hC] at h
      cases hcs : nodeAt ctx.source ctx.x C with
      | none => simp [hcs, throw, throwThe, MonadExceptOf.throw] at h
      | some q' =>
          simp only [hcs, bind, Except.bind, pure, Except.pure] at h
          split at h
          · cases h
          · cases h; exact ⟨_, List.mem_singleton_self _, rfl⟩
  | none =>
      simp only [hC] at h
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h; exact ⟨_, List.mem_singleton_self _, rfl⟩
      · simp only [bind, Except.bind, pure, Except.pure] at h
        split at h
        · cases h
        · cases h; exact ⟨_, List.mem_singleton_self _, rfl⟩

/-! ## Covering the boundary column -/

theorem mapM_ok_of_mem' {α β ε : Type} {f : α → Except ε β} {xs : List α} {ys : List β}
    (h : xs.mapM f = .ok ys) {x : α} (hx : x ∈ xs) : ∃ y ∈ ys, f x = .ok y := by
  obtain ⟨hlen, hall⟩ := mapM_except_spec f xs ys h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  exact ⟨ys[i]'(by omega), List.getElem_mem _, hall i hi (by omega)⟩

/-- The column `x` has a node at the official row `r`. -/
def XNode (M : Mountain) (x : Nat) (r : Row) : Prop := ∃ q ∈ realNodes M x, official q.2.row = r

/-- The items that cover the boundary column: gap-copy items, cut-bottom items, and clean items
of the root row `0`. -/
def InvCov (ctx : Context) (M : Mountain) (cr d : Nat) (it : Item) : Prop :=
  (∃ C, it.clean = some C ∧ it.cutBottom = true ∧ rootTop ctx d it.source = some C ∧
    XNode M ctx.x C ∧ ∀ csRef cs g, nodeAt M ctx.x C = some (csRef, cs) →
      generations M cr C (ctx.x + 1) csRef cs 0 = .ok g → it.offset ≤ g) ∨
  (it.clean = none ∧ it.cutBottom = true ∧
    ∃ ρ : Ref × Cell, topIn M cr d it.source = some ρ ∧ XNode M ctx.x (official ρ.2.row)) ∨
  (∃ C, it.clean = some C ∧ it.cutBottom = false ∧ (∀ q, C.coeff q = 0) ∧
    rootTop ctx d it.source = some C ∧ XNode M ctx.x C)

theorem xnode_nodeAt {M : Mountain} {x : Nat} {r : Row} (h : XNode M x r) :
    ∃ q, nodeAt M x r = some q := by
  obtain ⟨q, hq, hr⟩ := h
  obtain ⟨p, hp⟩ := Recon.RowLaw.nodeAt_of_mem hq
  rw [hr] at hp
  exact ⟨p, hp⟩

theorem xnode_top {M : Mountain} (hV : MountainValid M) {x d : Nat} {S r : Row}
    (h : XNode M x r) (hin : inRegion (d + 2) S r = true) :
    ∃ a, topIn M x (d + 2) S = some a ∧ r.coeff d ≤ (official a.2.row).coeff d := by
  obtain ⟨q, hq, hr⟩ := h
  obtain ⟨hqc, hq1, hqcell⟩ := Classification.mem_realNodes hq
  have hin' : inRegion (d + 2) S (official q.2.row) = true := by rw [hr]; exact hin
  cases ha : topIn M x (d + 2) S with
  | none => exact absurd ha (topIn_ne_none_of_node hqc hq1 hqcell hin')
  | some a =>
      refine ⟨a, rfl, ?_⟩
      have hle := le_top_of_node hV hqc hq1 hqcell hin' ha
      rw [hr] at hle
      exact Recon.RowLaw.coeff_le_of_inRegion hin (topIn_inRegion ha) hle

theorem rootTop_of_topIn {ctx : Context} {M : Mountain} {cr d : Nat} {S : Row}
    {ρ : Ref × Cell} (hs : ctx.source = M) (hr : ctx.rootColumn = cr)
    (h : topIn M cr d S = some ρ) : rootTop ctx d S = some (official ρ.2.row) := by
  unfold rootTop; rw [hs, hr, h]; rfl

theorem topIn_of_rootTop {ctx : Context} {M : Mountain} {cr d : Nat} {S C : Row}
    (hs : ctx.source = M) (hr : ctx.rootColumn = cr) (h : rootTop ctx d S = some C) :
    ∃ ρ : Ref × Cell, topIn M cr d S = some ρ ∧ official ρ.2.row = C := by
  unfold rootTop at h
  rw [hs, hr] at h
  cases ht : topIn M cr d S with
  | none => rw [ht] at h; cases h
  | some ρ => rw [ht] at h; exact ⟨ρ, rfl, Option.some.inj h⟩

/-- **A covering item emits every row of the boundary column in its target region.** -/
theorem coverAll {ctx : Context} {M R : Mountain} {cr B : Nat} (hVM : MountainValid M)
    (hVR : MountainValid R) (hs : ctx.source = M) (hr : ctx.rootColumn = cr)
    (hblk : ctx.block ≠ 0)
    (hbnd : ∀ d T, topIn ctx.result ctx.boundary d T = topIn R B d T) :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), runItemT ctx (d + 1) it = .ok ps →
      InvCov ctx M cr (d + 1) it → ∀ z ∈ realNodes R B,
        inRegion (d + 1) it.target (official z.2.row) = true →
        ∃ p ∈ ps, p.1.row = official z.2.row
  | 0, it, ps, h, hI, z, _, hz => by
      have h1 : levelOneT ctx it = .ok ps := by simpa [runItemT] using h
      have hzt : official z.2.row = it.target := inRegion_one hz
      have hsrc : ∃ q, nodeAt ctx.source ctx.x it.source = some q := by
        rw [hs]
        rcases hI with ⟨C, _, _, hrt, hX, _⟩ | ⟨_, _, ρ, hρ, hX⟩ | ⟨C, _, _, _, hrt, hX⟩
        · have := inRegion_one (rootTop_mem hrt); rw [← this]; exact xnode_nodeAt hX
        · have := inRegion_one (topIn_inRegion hρ); rw [← this]; exact xnode_nodeAt hX
        · have := inRegion_one (rootTop_mem hrt); rw [← this]; exact xnode_nodeAt hX
      obtain ⟨p, hp, hpr⟩ := levelOne_emits_target h1 hsrc
      exact ⟨p, hp, hpr.trans hzt.symm⟩
  | d + 1, it, ps, h, hI, z, hzB, hz => by
      obtain ⟨cs, outs, hch, hm, rfl⟩ := runItemT_step' h
      have hcase := childItems_cases hch
      -- the top of the boundary column in the target region
      obtain ⟨hzc, hz1, hzcell⟩ := Classification.mem_realNodes hzB
      obtain ⟨b, hbt, hjz⟩ : ∃ b, topIn R B (d + 2) it.target = some b ∧
          (official z.2.row).coeff d ≤ (official b.2.row).coeff d := by
        cases hb : topIn R B (d + 2) it.target with
        | none => exact absurd hb (topIn_ne_none_of_node hzc hz1 hzcell hz)
        | some b =>
            refine ⟨b, rfl, ?_⟩
            have hle := le_top_of_node hVR hzc hz1 hzcell hz hb
            exact Recon.RowLaw.coeff_le_of_inRegion hz (topIn_inRegion hb) hle
      have hB : heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) =
          (official b.2.row).coeff d := by rw [hbnd, hbt]; rfl
      -- the child of the slot of `z`, and its output
      have hfin : ∀ c ∈ cs, InvCov ctx M cr (d + 1) c →
          inRegion (d + 1) c.target (official z.2.row) = true →
          ∃ p ∈ outs.flatten, p.1.row = official z.2.row := by
        intro c hc hIc hzc'
        obtain ⟨out, hout, hcout⟩ := mapM_ok_of_mem' hm hc
        obtain ⟨p, hp, hpr⟩ := coverAll hVM hVR hs hr hblk hbnd d c out hcout hIc z hzB hzc'
        exact ⟨p, List.mem_flatten.mpr ⟨out, hout, hp⟩, hpr⟩
      have hzslot : ∀ T, inRegion (d + 2) T (official z.2.row) = true →
          inRegion (d + 1) (slot (d + 2) T ((official z.2.row).coeff d)) (official z.2.row) =
            true := fun T hT => slot_mem hT
      rcases hI with ⟨C, hcl, hcb, hrt, hX, hgo⟩ | ⟨hcl, hcb, ρ, hρ, hX⟩ |
          ⟨C, hcl, hcb, hC0, hrt, hX⟩
      · -- a gap-copy item
        obtain ⟨ρ, hρ, hρC⟩ := topIn_of_rootTop hs hr hrt
        cases hcase with
        | none hn =>
            obtain ⟨a, ha, _⟩ := xnode_top hVM hX (by rw [← hρC]; exact topIn_inRegion hρ)
            rw [hs, ha] at hn; cases hn
        | case1 _ _ _ hcl' _ _ => rw [hcl] at hcl'; cases hcl'
        | case2 _ _ _ _ _ _ hcl' _ _ _ _ _ => rw [hcl] at hcl'; cases hcl'
        | case3 _ _ _ _ _ _ hcl' _ _ _ => rw [hcl] at hcl'; cases hcl'
        | case4 a ha ρr ρc hρ' hasc C' hcl' csRef cs0 hcs g hg hbd =>
            rw [hcl] at hcl'
            obtain rfl := Option.some.inj hcl'
            rw [hs, hr, hρ] at hρ'
            obtain rfl := Option.some.inj hρ'
            rw [hs] at hcs
            rw [hs, hr] at hg
            have hog := hgo csRef cs0 g hcs hg
            have hrts := rootTop_slot hrt
            rw [← hρC] at hrts
            refine hfin (c4 it.source it.target C d (height (d + 2) (official ρc.row))
              (heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target)) it.offset
              it.cutBottom ((official z.2.row).coeff d))
              (List.mem_map.mpr ⟨_, List.mem_range.mpr ?_, rfl⟩) ?_ ?_
            · rw [if_neg hblk, hB]; omega
            · refine Or.inl ⟨C, ?_, ?_, ?_, hX, ?_⟩
              · unfold c4; rw [hcb]; rfl
              · unfold c4; rw [hcb]; rfl
              · unfold c4; rw [hcb]; rw [← hρC]; exact hrts
              · intro csRef' cs' g' hcs' hg'
                rw [hcs] at hcs'
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hcs')
                have hgg : g' = g := Except.ok.inj (hg'.symm.trans hg)
                subst hgg
                unfold c4; rw [hcb]
                simp only [if_true]
                rw [hB]
                omega
            · unfold c4; rw [hcb]
              exact hzslot _ hz
      · -- a cut-bottom item
        cases hcase with
        | none hn =>
            obtain ⟨a, ha, _⟩ := xnode_top hVM hX (topIn_inRegion hρ)
            rw [hs, ha] at hn; cases hn
        | case1 _ _ _ _ _ hcb' => rw [hcb] at hcb'; cases hcb'
        | case2 _ _ _ _ _ _ _ hcb' _ _ _ _ => rw [hcb] at hcb'; cases hcb'
        | case4 _ _ _ _ _ _ C' hcl' _ _ _ _ _ _ => rw [hcl] at hcl'; cases hcl'
        | case3 a ha ρr ρc hρ' hasc _ _ e he =>
            rw [hs, hr, hρ] at hρ'
            obtain rfl := Option.some.inj hρ'
            obtain ⟨a', ha', haσ⟩ := xnode_top hVM hX (topIn_inRegion hρ)
            rw [hs, ha'] at ha
            obtain rfl := Option.some.inj ha
            have he1 : e = 0 ∨ e = 1 := by rw [he]; split <;> simp
            have hrts := rootTop_slot (rootTop_of_topIn hs hr hρ)
            have htps := ChainCorr.Inner.topIn_slot hρ
            have hjz' := hjz
            refine hfin (c3 it.source it.target (official ρc.row) d
              (height (d + 2) (official ρc.row))
              (heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target)) e
              ((official z.2.row).coeff d + height (d + 2) (official ρc.row)))
              (List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨List.mem_range.mpr ?_, by simp⟩, rfl⟩)
              ?_ ?_
            · have haσ' : (official ρc.row).coeff d ≤ (official a'.2.row).coeff d := haσ
              rw [if_neg hblk, hB]
              show (official z.2.row).coeff d + (official ρc.row).coeff d <
                (official b.2.row).coeff d + (official a'.2.row).coeff d + 1
              omega
            · unfold c3
              by_cases h2 : (((official z.2.row).coeff d + height (d + 2) (official ρc.row) : Nat) :
                  Int) < (heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) : Int) +
                  (height (d + 2) (official ρc.row) : Int) + e
              · rw [if_pos h2]
                refine Or.inl ⟨official ρc.row, rfl, rfl, hrts, hX, ?_⟩
                intro _ _ _ _ _; exact Nat.zero_le _
              · rw [if_neg h2]
                rw [hB] at h2
                have hjzeq : (official z.2.row).coeff d = (official b.2.row).coeff d := by
                  rcases he1 with he0 | he0 <;> rw [he0] at h2 <;> omega
                have hidx : (official z.2.row).coeff d + height (d + 2) (official ρc.row) -
                    heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) =
                    height (d + 2) (official ρc.row) := by rw [hB]; omega
                refine Or.inr (Or.inl ⟨rfl, ?_, (ρr, ρc), ?_, hX⟩)
                · exact decide_eq_true (by rw [hB]; omega)
                · show topIn M cr (d + 1) (slot (d + 2) it.source
                    ((official z.2.row).coeff d + height (d + 2) (official ρc.row) -
                      heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target))) =
                    some (ρr, ρc)
                  rw [hidx]
                  exact htps
            · unfold c3
              split_ifs
              · rw [show (official z.2.row).coeff d + height (d + 2) (official ρc.row) -
                    height (d + 2) (official ρc.row) = (official z.2.row).coeff d by omega]
                exact hzslot _ hz
              · rw [show (official z.2.row).coeff d + height (d + 2) (official ρc.row) -
                    height (d + 2) (official ρc.row) = (official z.2.row).coeff d by omega]
                exact hzslot _ hz
      · -- a clean item of the root row `0`
        obtain ⟨ρ, hρ, hρC⟩ := topIn_of_rootTop hs hr hrt
        cases hcase with
        | none hn =>
            obtain ⟨a, ha, _⟩ := xnode_top hVM hX (by rw [← hρC]; exact topIn_inRegion hρ)
            rw [hs, ha] at hn; cases hn
        | case1 _ _ _ hcl' _ _ => rw [hcl] at hcl'; cases hcl'
        | case2 _ _ _ _ _ _ hcl' _ _ _ _ _ => rw [hcl] at hcl'; cases hcl'
        | case3 _ _ _ _ _ _ hcl' _ _ _ => rw [hcl] at hcl'; cases hcl'
        | case4 a ha ρr ρc hρ' hasc C' hcl' csRef cs0 hcs g hg hbd =>
            rw [hcl] at hcl'
            obtain rfl := Option.some.inj hcl'
            rw [hs, hr, hρ] at hρ'
            obtain rfl := Option.some.inj hρ'
            have hoff : it.offset = 0 := by
              by_contra hne
              exact hbd ⟨by rw [hcb]; simp, Or.inr hne⟩
            have hρC' : official ρc.row = C := hρC
            have hR0 : height (d + 2) (official ρc.row) = 0 := by
              show (official ρc.row).coeff d = 0
              rw [hρC']; exact hC0 d
            have hrts := rootTop_slot hrt
            rw [← hρC] at hrts
            refine hfin (c4 it.source it.target C d (height (d + 2) (official ρc.row))
              (heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target)) it.offset
              it.cutBottom ((official z.2.row).coeff d))
              (List.mem_map.mpr ⟨_, List.mem_range.mpr ?_, rfl⟩) ?_ ?_
            · rw [if_neg hblk, hB, hoff]; omega
            · unfold c4
              rw [hcb]
              simp only [Bool.false_eq_true, if_false]
              rw [if_neg (by omega)]
              by_cases hz0 : (official z.2.row).coeff d = 0
              · have hd : decide (height (d + 2) (official ρc.row) < (official z.2.row).coeff d) =
                    false := decide_eq_false (by omega)
                rw [hd]
                refine Or.inr (Or.inr ⟨C, rfl, rfl, hC0, ?_, hX⟩)
                rw [← hρC]; exact hrts
              · have hd : decide (height (d + 2) (official ρc.row) < (official z.2.row).coeff d) =
                    true := decide_eq_true (by omega)
                rw [hd]
                refine Or.inl ⟨C, rfl, rfl, ?_, hX, ?_⟩
                · rw [← hρC]; exact hrts
                · intro _ _ _ _ _
                  simp only
                  rw [hB, hoff]
                  omega
            · unfold c4
              rw [hcb]
              simp only [Bool.false_eq_true, if_false]
              rw [if_neg (by omega)]
              exact hzslot _ hz

end OmegaY.Official.Classification.Proofs.CopyShape.PBStageB
