/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/StartRootPartsPa.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StartRootPartsX0
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeMD

set_option backward.do.legacy false

/-!
# `PaLookup` from the column-shape facts MA and MH

`PaLookup` (`StartRootPartsOriginLower.lean`): for a node `u` of block `i ≥ 1` that is not a
gap copy, with origin `o = (x, σ)` whose leg is the root column `cr`, let `pa` be the highest
node of `cr` at or below `σ` and `pe` the highest node of the boundary column
`B = x₀ + w·(i - 1)` at or below the row of `u`. If the origin `ν` of `pe` is not an upper
origin, then `pa` is also the highest node of `cr` at or below the row of `ν`.

`paLookup_of_facts` proves it from the column-shape facts `MAHolds`, `MHHolds`
(`CopyShape.lean`; `MDHolds` is proved), which give the row map `Φ` of a block
(`CopyShape.column_shape`). The other ingredients are proved here:

* **The rows of the root column are fixed** (`Φ_fix`, `rowOK_fix`). If `r` is the official
  row of a node of `cr`, the row map of every block sends `r` to `r`: in each region
  containing `r` the top `ρ` of `cr` is at or above `r`, so `Φ` takes its first branch
  (`r ≤ row ρ`) at every level.
* **The last column shadows the root column** (`x0_shadow`, from Phyrion's row shadow
  `P_rowShadow`): every node of `cr` below `t` has a node of `x₀` at the same row.
* **The first copy of such a node in `B` is at its own row** (`bfirst`): block `0` copies at
  the row of the origin (`b0_profile`); a block `m ≥ 1` copies every node of `x₀` below `τ`
  (`emitsT_shape`), the first copy is not a gap copy (`NCB`), and its row is `Φ` of the
  origin row, fixed by `rowOK_fix`.

## The proof

Write `r_c` for the official row of a node `c`.

1. `r_pa ≤ r_ν`. The row of `u` is `Φ(σ) ≥ Φ(r_pa) = r_pa`. If `r_pa ≥ τ`, `B` has an upper
   copy of `pa` at `r_pa`, at or below `u`, so `pe` would be an upper copy. Otherwise `B` has
   a copy of the shadow of `pa` at the row `r_pa`, at or below `pe`; the origin rows of `B`
   do not decrease (`emitsT_mono`), so `r_pa ≤ r_ν`.
2. No node `c` of `cr` has `σ < r_c ≤ r_ν`. Otherwise `r_c < τ`; the first copy of the shadow
   `p_c` of `c` in `B` is at the row `r_c = Φ(r_c) > Φ(σ) = row u ≥ row pe`, so after `pe`;
   the origin rows do not decrease, so `r_ν = r_c` and `ν = p_c`: `pe` is a copy of `p_c`
   before its first copy.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.SRPa

open Canonical Reserve Official Descent Classification Proofs
open Geometry
open ChainCorr.Inner ChainCorr.SRParts ChainCorr.SRX0 CopyShape

/-! ## The rows of the root column are fixed by the row map -/

theorem Φ_fix {s : List Nat} (E : Env) (hb : Canonical.build s = .ok E.M) {c : Ref} {cc : Cell}
    (hc : (c, cc) ∈ realNodes E.M E.cr) :
    ∀ d (S : Row), inRegion (d + 1) S (official cc.row) = true →
      Φ E false (d + 1) S S (official cc.row) = official cc.row
  | 0, S, h => by rw [Φ_one]; exact (inRegion_one h).symm
  | d + 1, S, h => by
    cases htop : topIn E.M E.cr (d + 2) S with
    | none =>
      exfalso
      obtain ⟨a, ha⟩ := Recon.filter_last_exists
        (P := fun p => inRegion (d + 2) S (official p.2.row)) hc h
      unfold topIn at htop
      rw [htop] at ha
      cases ha
    | some a =>
      obtain ⟨ρr, ρc⟩ := a
      have hle : official cc.row ≤ official ρc.row := Recon.RowLaw.topIn_row_max hb htop hc h
      rw [ΦF_low htop hle]
      exact Φ_fix E hb hc d _ (ChainCorr.CopyMonoProof.mem_slot_height h)

/-- The official row of a node of the root column satisfies `RowOK` with itself, in every
block. -/
theorem rowOK_fix {s : List Nat} (E : Env) (hb : Canonical.build s = .ok E.M) (τ : Row)
    {c : Ref} {cc : Cell} (hc : (c, cc) ∈ realNodes E.M E.cr) :
    CopyShape.RowOK E τ (official cc.row) (official cc.row) := by
  by_cases hlt : official cc.row < τ
  · obtain ⟨p, hp, hin⟩ := Recon.JumpLaw.lowerItems_cover τ hlt
    obtain ⟨k, j, _, _, rfl⟩ := Recon.RowLaw.mem_lowerItems hp
    exact Or.inl ⟨hlt, _, hp, hin, (Φ_fix E hb hc k _ hin).symm⟩
  · exact Or.inr ⟨not_lt.mp hlt, rfl⟩

/-! ## The last column shadows the root column -/

/-- **The shadow.** A node of the root column below `t` has a node of the last column at the
same row. -/
theorem x0_shadow {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}
    (hTop : Recon.Top s M t root) {c : Ref} {cc : Cell} (hcc : c.column = root.column)
    (hc1 : 1 ≤ c.index) (hc : cell? M c = some cc) (hlt : official cc.row < official t.row) :
    ∃ p cp, p.column = M.size - 1 ∧ 1 ≤ p.index ∧ cell? M p = some cp ∧ cp.row = cc.row := by
  have hB := hTop.build
  have hF : (Frame.ofMountain M).Normal := build_normal_of_success hB
  have hO := hF.toOrdered
  have hV := build_valid_of_success hB
  have hrl := hTop.lt
  have hsz : M.size - 1 < M.size := by omega
  have htop := hTop.top
  rw [Array.getElem?_eq_getElem hsz] at htop
  simp only [Option.bind_some, Array.back?] at htop
  obtain ⟨hTi, hTt⟩ := Array.getElem?_eq_some_iff.mp htop
  let x0 : Fin (Frame.ofMountain M).width := ⟨M.size - 1, hsz⟩
  have hlen2 : 2 ≤ M[M.size - 1].size := hO.length_ge_two x0
  -- `t` is not the bottom node
  have hT3 : 3 ≤ M[M.size - 1].size := by
    by_contra hn
    have hT : M[M.size - 1].size - 1 = 1 := by omega
    have hbot := hO.bottom_row x0 (show 1 < M[M.size - 1].size by omega)
    have : t.row = 1 := by
      rw [← hTt]
      have h' : (M[M.size - 1][1]'(by omega)).row = 1 := hbot
      simpa only [hT] using h'
    exact hTop.real (by rw [this]; exact official_one)
  have htcell : cell? M ⟨M.size - 1, M[M.size - 1].size - 1⟩ = some t := by
    simp only [cell?, Array.getElem?_eq_getElem hsz, Option.bind_eq_bind, Option.bind_some]
    exact htop
  have ht1 : (1 : Row) ≤ t.row := one_le_row hV htcell (by show 1 ≤ M[M.size - 1].size - 1; omega)
  have hlt' : cc.row < t.row := by
    by_contra hn
    exact absurd (Recon.official_mono ht1 (not_lt.mp hn)) (not_le.mpr hlt)
  -- the node `y` just below `t`
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
  have hvt : cell? M ⟨(⟨M.size - 1, M[M.size - 1].size - 2⟩ : Ref).column,
      (⟨M.size - 1, M[M.size - 1].size - 2⟩ : Ref).index + 1⟩ = some t := by
    simp only
    rw [show M[M.size - 1].size - 2 + 1 = M[M.size - 1].size - 1 by omega]
    exact htcell
  obtain ⟨_, _, _, hmax⟩ := canonical_rawParent_highest_below (build_success_legal hB) hB hvt
    hrawy0
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
      rw [← hF.rawParent_eq_P hyreal]
      exact Frame.rawParent_eq_of_upper_left hup hleft
  -- the frame node of `c`, at or below the root
  obtain ⟨hcs, hci, hccell⟩ := canon_cell?_some_iff.mp hc
  let nc : (Frame.ofMountain M).Node := canonNodeOf c hcs hci
  have hidx : c.index ≤ root.index := hmax c.index cc (by rw [← hcc]; exact hc) hlt'
  have hnc1 : nc.1 = nr.1 := by
    apply Fin.ext
    show c.column = nr.1.val
    rw [hcc, ← hnr]
    rfl
  have hh : (Frame.ofMountain M).height nc ≤ (Frame.ofMountain M).height nr :=
    ControlProof.height_le_of_index hO hnc1 (by
      show c.index ≤ nr.2.val
      rw [show nr.2.val = root.index by rw [← hnr]; rfl]
      exact hidx)
  obtain ⟨v, hvreal, hvc, _, hvh, _⟩ := Frame.P_rowShadow hF hPy nc (show 0 < c.index by omega)
    hnc1 hh
  refine ⟨Frame.ref v, (Frame.ofMountain M).cell v, ?_, hvreal, ControlProof.cell?_ref v, ?_⟩
  · show v.1.val = M.size - 1
    rw [hvc]
  · show (Frame.ofMountain M).height v = cc.row
    rw [hvh]
    show (M[c.column][c.index]).row = cc.row
    rw [hccell]

/-! ## The copies of `x₀` -/

theorem x0_mem_blockColumns {cr x0 n m : Nat} (hcr : cr < x0) (hm0 : 0 < m) (hm : m < n) :
    x0 ∈ blockColumns cr x0 n m := by
  unfold blockColumns
  rw [if_neg (by omega), if_pos hm]
  simp only [List.mem_range'_1]
  omega

/-- Lower emits come before upper emits. -/
theorem lower_before_upper {ctx : Context} {τ : Row} {es : List (Emit × Origin)}
    (h : emitsT ctx τ = .ok es) {a b : Nat} (ha : a < es.length) (hb : b < es.length)
    (hla : es[a].2.isUpper = false) (hub : es[b].2.isUpper = true) : a < b := by
  obtain ⟨lo, us, hlo, hus, hsplit⟩ := emitsT_split h
  have hLnot := lowerT_notUpper' hlo
  have hUup := (upperT_run hus).2
  subst hsplit
  have hal : a < lo.length := by
    by_contra hn
    have hn' : lo.length ≤ a := by omega
    rw [List.getElem_append_right hn'] at hla
    rw [hUup _ (List.getElem_mem _)] at hla
    cases hla
  have hbl : lo.length ≤ b := by
    by_contra hn
    have hn' : b < lo.length := by omega
    rw [List.getElem_append_left hn'] at hub
    rw [hLnot _ (List.getElem_mem _)] at hub
    cases hub
  omega

/-- **The first copy.** A node `p` of `x₀` below `τ` at the row of a node of the root column
is copied into the copy of `x₀` of every block `m < n`, and its first copy is at the
official row of `p`. -/
theorem bfirst (hMA : MAHolds) (hMH : MHHolds) {s : List Nat} {n D : Nat} {M : Mountain}
    {out : List Nat} {ρ : Root} {R : Mountain} {t : Cell} (hd : SpliceData s n D M out ρ R t)
    {m : Nat} (hm : m < n) {esB : List (Emit × Origin)}
    (hes : blockEmits M R ρ.cr ρ.x0 (official t.row) m ρ.x0 = .ok esB)
    {p : Ref} {cp : Cell} (hpc : p.column = ρ.x0) (hp1 : 1 ≤ p.index) (hcp : cell? M p = some cp)
    (hτ : official cp.row < official t.row)
    {c : Ref} {cc : Cell} (hcc : c.column = ρ.cr) (hc1 : 1 ≤ c.index) (hc : cell? M c = some cc)
    (hrow : cc.row = cp.row) :
    ∃ k, ∃ hk : k < esB.length, esB[k].2.src = p ∧ esB[k].1.row = official cp.row ∧
      ∀ k' (hk' : k' < esB.length), k' < k → esB[k'].2.src ≠ p := by
  classical
  have hV := build_valid_of_success hd.splice.build
  obtain ⟨_, hcrx, _, _⟩ := spliceData_facts hd
  have hes' : emitsT (bctx M R ρ.cr ρ.x0 m) (official t.row) = .ok esB := hes
  have hcmem : (c, cc) ∈ realNodes M ρ.cr := by
    have := mem_realNodes_of_cell' hc hc1
    rwa [hcc] at this
  -- some emit has the origin `p`
  have hex : ∃ k, ∃ hk : k < esB.length, esB[k].2.src = p := by
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0
      obtain ⟨h1, _, _, h4, _⟩ := b0_profile hd hm hes
      obtain ⟨j, hj, hjl, hjrow⟩ := h4 p cp hpc hp1 hcp hτ
      refine ⟨j, hj, ?_⟩
      obtain ⟨cμ, hcμ, hoff⟩ := h1 j hj
      obtain ⟨hsc, hs1, _⟩ := bsrc hes hj
      rw [hjl] at hsc
      simp only [Bool.false_eq_true, if_false] at hsc
      exact ref_eq_of_official hV (by rw [hsc, hpc]) hs1 hp1 hcμ hcp (hoff.trans hjrow)
    · have hbnd : ∀ d T, topIn (bctx M R ρ.cr ρ.x0 m).result (bctx M R ρ.cr ρ.x0 m).boundary d T =
          topIn R (ρ.cr + (ρ.x0 - ρ.cr) * m) d T := by
        intro d T
        exact topIn_extract' (by show ρ.cr + (ρ.x0 - ρ.cr) * m < ρ.x0 + (ρ.x0 - ρ.cr) * m; omega)
      have hy := x0_mem_blockColumns hcrx hm0 hm
      obtain ⟨_, _, h3⟩ := emitsT_shape (bctx M R ρ.cr ρ.x0 m) (official t.row) R
        (ρ.cr + (ρ.x0 - ρ.cr) * m) hV (show 1 ≤ m from hm0) hbnd
        (hMA s n D M out ρ R t hd m hm0 (by omega) ρ.x0 hy)
        (mdHolds s n D M out ρ R t hd m hm0 (by omega) ρ.x0 hy)
        (hMH s n D M out ρ R t hd m hm0 (by omega) ρ.x0 hy) hes'
      obtain ⟨q, hq, hqs, _⟩ := h3 p cp hpc hp1 hcp (Or.inl hτ)
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hq
      exact ⟨k, hk, hqs⟩
  -- the first one
  let k0 := Nat.find hex
  obtain ⟨hk0, hk0s⟩ := Nat.find_spec hex
  have hmin : ∀ k' (hk' : k' < esB.length), k' < k0 → esB[k'].2.src ≠ p :=
    fun k' hk' hlt heq => Nat.find_min hex hlt ⟨hk', heq⟩
  refine ⟨k0, hk0, hk0s, ?_, hmin⟩
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · subst hm0
    obtain ⟨h1, _⟩ := b0_profile hd hm hes
    obtain ⟨cμ, hcμ, hoff⟩ := h1 k0 hk0
    rw [hk0s, hcp] at hcμ
    cases hcμ
    exact hoff.symm
  · have hy := x0_mem_blockColumns hcrx hm0 hm
    obtain ⟨hrows, hncb, _⟩ := column_shape hMA mdHolds hMH hd hm0 (by omega) hy hes
    -- the first copy is not a gap copy
    have hnc : cutOrigin esB[k0].2 = false := by
      cases hcut : cutOrigin esB[k0].2 with
      | false => rfl
      | true =>
        exfalso
        have hbnd : ∀ d T, topIn (bctx M R ρ.cr ρ.x0 m).result
            (bctx M R ρ.cr ρ.x0 m).boundary d T = topIn R (ρ.cr + (ρ.x0 - ρ.cr) * m) d T := by
          intro d T
          exact topIn_extract' (by
            show ρ.cr + (ρ.x0 - ρ.cr) * m < ρ.x0 + (ρ.x0 - ρ.cr) * m; omega)
        obtain ⟨_, _, h3⟩ := emitsT_shape (bctx M R ρ.cr ρ.x0 m) (official t.row) R
          (ρ.cr + (ρ.x0 - ρ.cr) * m) hV (show 1 ≤ m from hm0) hbnd
          (hMA s n D M out ρ R t hd m hm0 (by omega) ρ.x0 hy)
          (mdHolds s n D M out ρ R t hd m hm0 (by omega) ρ.x0 hy)
          (hMH s n D M out ρ R t hd m hm0 (by omega) ρ.x0 hy) hes'
        obtain ⟨q, hq, hqs, hqc⟩ := h3 p cp hpc hp1 hcp (Or.inl hτ)
        obtain ⟨kq, hkq, rfl⟩ := List.getElem_of_mem hq
        have hle : k0 ≤ kq := by
          by_contra hn
          exact hmin kq hkq (by omega) hqs
        rcases Nat.lt_or_eq_of_le hle with hlt | heq
        · exact List.pairwise_iff_getElem.mp hncb k0 kq hk0 hkq hlt hcut hqc (hk0s.trans hqs.symm)
        · subst heq
          rw [hcut] at hqc
          cases hqc
    have hr1 := hrows _ (List.getElem_mem hk0) hnc cp (by rw [hk0s]; exact hcp)
    have hr2 := rowOK_fix ⟨M, R, ρ.cr, ρ.x0, ρ.cr + (ρ.x0 - ρ.cr) * m, m⟩ hd.splice.build
      (official t.row) hcmem
    rw [hrow] at hr2
    exact (rowOK_cmp hr1 hr2).2 rfl

/-! ## `PaLookup` -/

/-- **`PaLookup` from the column-shape facts MA and MH.** -/
theorem paLookup_of_facts (hMA : MAHolds) (hMH : MHHolds) : SRParts.PaLookup := by
  intro s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL heq esB hesB k hk
    hpek hlow cν hcν
  have hd := hS.data
  have hb := hS.splice.build
  have hV := build_valid_of_success hb
  obtain ⟨root, hTop, hrc, hx0⟩ := data_top hd
  obtain ⟨_, hcrx, _, _⟩ := spliceData_facts hd
  have hipos := hS.iPos
  have hm : i - 1 < n := by have := hS.iLt; omega
  have hesB' : emitsT (bctx M R ρ.cr ρ.x0 (i - 1)) (official t.row) = .ok esB := hesB
  -- the row of `u`
  have hblx : blockEmits M R ρ.cr ρ.x0 (official t.row) i x = .ok es := by
    simp only [blockEmits, ← hS.Xeq]
    exact hS.emits
  have hRowU := (column_shape hMA mdHolds hMH hd hipos hS.iLt hS.xMem hblx).1 es[j]
    (List.getElem_mem hj) hnc cv hL.hcv
  obtain ⟨colX, hRX, hcopy⟩ := hS.copy
  obtain ⟨_, hcellsX⟩ := cells_of_copy hRX hcopy hS.emits
  obtain ⟨cellu, hcellu, hrowu⟩ := hcellsX j hj
  have hcu : cu = cellu := Option.some.inj (hL.hcu.symm.trans hcellu)
  subst hcu
  -- `pe` is the node `k + 1` of `B`
  have himg := leg_image hS hj hL
  rw [heq, mapColumn_of_ge (le_refl _), boundary_eq hcrx hipos] at himg
  have hpecol : pe.column = ρ.x0 + (ρ.x0 - ρ.cr) * (i - 1) := by
    rw [(highestAtMost_spec hL.hpe).1, himg]
  obtain ⟨_, _, _, _, _, hBc⟩ := bcol hd hm hesB
  have hpe_max : ∀ k' (hk' : k' < esB.length), esB[k'].1.row ≤ es[j].1.row → k' ≤ k := by
    intro k' hk' hle
    obtain ⟨cb, hcb, hcbr, _⟩ := hBc k' hk'
    have := hAM_max hL.hpe (q := ⟨ρ.x0 + (ρ.x0 - ρ.cr) * (i - 1), k' + 1⟩) (by rw [himg])
      (by show 0 < k' + 1; omega) hcb (by rw [hcbr, hrowu]; exact stored_mono hle)
    show k' ≤ k
    have h2 : (⟨ρ.x0 + (ρ.x0 - ρ.cr) * (i - 1), k' + 1⟩ : Ref).index ≤ pe.index := this
    simp only at h2
    omega
  have hpe_le : esB[k].1.row ≤ es[j].1.row := by
    have hpeq : pe = ⟨ρ.x0 + (ρ.x0 - ρ.cr) * (i - 1), k + 1⟩ := ref_eq_of hpecol hpek
    obtain ⟨cb, hcb, hcbr, _⟩ := hBc k hk
    have hcpe : cpe = cb := by
      have := hL.hcpe
      rw [hpeq, hcb] at this
      exact (Option.some.inj this).symm
    have := hAM_le hL.hpe hL.hcpe
    rw [hcpe, hcbr, hrowu] at this
    exact stored_le_iff.mp this
  -- the origin `ν` of `pe`
  obtain ⟨hνc, hν1, _⟩ := bsrc hesB hk
  rw [hlow] at hνc
  simp only [Bool.false_eq_true, if_false] at hνc
  obtain ⟨cν', hcν', hντ⟩ := lower_src_lt hesB' hk hlow
  change cell? M _ = some cν' at hcν'
  rw [hcν] at hcν'
  cases hcν'
  have hmono := CopyMonoProof.emitsT_mono hV hesB'
  have hmono' : ∀ k1 k2 (h1 : k1 < esB.length) (h2 : k2 < esB.length), k1 ≤ k2 →
      ∀ c1 c2, cell? M esB[k1].2.src = some c1 → cell? M esB[k2].2.src = some c2 →
        official c1.row ≤ official c2.row := by
    intro k1 k2 h1 h2 h12 c1 c2 hc1 hc2
    rcases Nat.lt_or_eq_of_le h12 with hlt | heq'
    · exact List.pairwise_iff_getElem.mp hmono k1 k2 h1 h2 hlt c1 c2 hc1 hc2
    · subst heq'
      rw [hc1] at hc2
      cases hc2
      exact le_refl _
  -- facts on `pa` and the origin of `u`
  obtain ⟨hpacol', hpa1, _⟩ := highestAtMost_spec hL.hpa
  have hpacol : pa.column = ρ.cr := by rw [hpacol', heq]
  have hpamem : (pa, cpa) ∈ realNodes M ρ.cr := by
    have := mem_realNodes_of_cell' hL.hcpa hpa1
    rwa [hpacol] at this
  have hpa_le : cpa.row ≤ cv.row := hAM_le hL.hpa hL.hcpa
  obtain ⟨_, hsrc1, _⟩ := emitsT_good hS.emits es[j] (List.getElem_mem hj)
  have hcv1 : (1 : Row) ≤ cv.row := one_le_row hV hL.hcv hsrc1
  have hcν1 : (1 : Row) ≤ cν.row := one_le_row hV hcν hν1
  let Ei : Env := ⟨M, R, ρ.cr, ρ.x0, ρ.cr + (ρ.x0 - ρ.cr) * i, i⟩
  -- (a) `row pa ≤ row ν`
  have ha : cpa.row ≤ cν.row := by
    have hFa := rowOK_fix Ei hb (official t.row) hpamem
    have hoff : official cpa.row ≤ official cv.row := Recon.official_mono (one_le_row hV hL.hcpa
      (by omega)) hpa_le
    have hle1 : official cpa.row ≤ es[j].1.row := by
      rcases lt_or_eq_of_le hoff with hlt | heq'
      · exact ((rowOK_cmp hFa hRowU).1 hlt).le
      · exact le_of_eq ((rowOK_cmp hFa hRowU).2 heq')
    have hoffν : official cpa.row ≤ official cν.row := by
      by_cases hup : official t.row ≤ official cpa.row
      · exfalso
        obtain ⟨k', hk', hup', hrow'⟩ := upper_cover hesB' pa cpa
          (by simp [upperColumn, bctx, ctxAt, hpacol]) (by omega) hL.hcpa hup
        have h1 := hpe_max k' hk' (by rw [hrow']; exact hle1)
        have h2 := lower_before_upper hesB' hk hk' hlow hup'
        omega
      · obtain ⟨p, cp, hpc, hp1, hcp, hcpr⟩ := x0_shadow hTop (by rw [hpacol, hrc]) (by omega)
          hL.hcpa (lt_of_not_ge hup)
        rw [← hx0] at hpc
        obtain ⟨k', hk', hsrc', hrow', _⟩ := bfirst hMA hMH hd hm hesB hpc hp1 hcp
          (by rw [hcpr]; exact lt_of_not_ge hup) hpacol (by omega) hL.hcpa hcpr.symm
        have h1 := hpe_max k' hk' (by rw [hrow', hcpr]; exact hle1)
        have := hmono' k' k hk' hk h1 cp cν (by rw [hsrc']; exact hcp) hcν
        rwa [hcpr] at this
    by_contra hn
    exact absurd (Recon.official_strictMono hcν1 (lt_of_not_ge hn)) (not_lt.mpr hoffν)
  -- (b) no node of `cr` strictly between `σ` and `row ν`
  have hbmax : ∀ jj cc, cell? M ⟨ρ.cr, jj⟩ = some cc → 0 < jj → cc.row ≤ cν.row →
      jj ≤ pa.index := by
    intro jj cc hcc hjj hccle
    have hle : cc.row ≤ cv.row := by
      by_contra hn
      have hσ : official cv.row < official cc.row := Recon.official_strictMono hcv1 (lt_of_not_ge hn)
      have hccν : official cc.row ≤ official cν.row := Recon.official_mono
        (one_le_row hV hcc (by show 1 ≤ jj; omega)) hccle
      have hcτ : official cc.row < official t.row := lt_of_le_of_lt hccν hντ
      obtain ⟨p, cp, hpc, hp1, hcp, hcpr⟩ := x0_shadow hTop (c := ⟨ρ.cr, jj⟩) (by simp [hrc])
        (by show 1 ≤ jj; omega) hcc hcτ
      rw [← hx0] at hpc
      obtain ⟨k2, hk2, hsrc2, hrow2, hfirst⟩ := bfirst hMA hMH hd hm hesB hpc hp1 hcp
        (by rw [hcpr]; exact hcτ) (c := ⟨ρ.cr, jj⟩) rfl (by show 1 ≤ jj; omega) hcc hcpr.symm
      have hccmem : ((⟨ρ.cr, jj⟩ : Ref), cc) ∈ realNodes M ρ.cr :=
        mem_realNodes_of_cell' hcc (by show 1 ≤ jj; omega)
      have hFc := rowOK_fix Ei hb (official t.row) hccmem
      have hu_lt : es[j].1.row < official cc.row := (rowOK_cmp hRowU hFc).1 hσ
      have hkk2 : k < k2 := by
        by_contra hn'
        have := emit_le hd hm hesB hk2 hk (by omega)
        rw [hrow2, hcpr] at this
        exact absurd (lt_of_le_of_lt this (lt_of_le_of_lt hpe_le hu_lt)) (lt_irrefl _)
      have hνle := hmono' k k2 hk hk2 hkk2.le cν cp hcν (by rw [hsrc2]; exact hcp)
      rw [hcpr] at hνle
      have hνeq : esB[k].2.src = p := ref_eq_of_official hV (by rw [hνc, hpc]) hν1 hp1 hcν hcp
        (by rw [hcpr]; exact le_antisymm hνle hccν)
      exact hfirst k hk hkk2 hνeq
    exact hAM_max hL.hpa (q := ⟨ρ.cr, jj⟩) (by simp [heq]) hjj hcc hle
  exact highestAtMost_of_max hpacol hpa1 hL.hcpa ha hbmax

end OmegaY.Official.Classification.Proofs.ChainCorr.SRPa

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.SRPa.x0_shadow
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.SRPa.bfirst
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.SRPa.paLookup_of_facts
