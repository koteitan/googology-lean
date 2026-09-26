/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/TopChainMain.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TopChainStart
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TopChainLowExp

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# The shared family `TopStep`, `TopStart` from open pieces

`TopStep` and `TopStart` (`LowerChain.lean`) are proved here except for the pieces below. All
of them are about the lower part (rows below `row t`); everything at or above `row t` is proved.

## `TopStep`

For the top copy `Z` of a node `z` of an inner column `y` of block `i ≥ 1`, the node `z⁺` above
`z`, and the stored parent `a` of `z` (the stored left end of `z⁺`):

* `row z⁺ ≥ row t`: proved (`topStepHi`, `TopChainHi.lean`);
* `row z⁺ < row t`, `col a < c_r`: proved (`lo_left`: `A = a`, the jump from the proved
  `LowerPairsLeft`);
* `row z⁺ < row t`, `col a > c_r`: the stand-in part is proved (`lo_right`: `A` is the top copy
  of `a`); the jump bound is `TopStepLoJump` (**open**), which follows from the jump law of the
  output (`topStepLoJump_of_jumpLaw`, with the proved `lowExpCopy`), hence from the stage-B
  statements `LowerRowsCopy` and `LowerRowsBoundary` (`topStepLoJump_of_rows`);
* `row z⁺ < row t`, `col a = c_r`: `TopStepLoRoot` (**open**).

`topStep_of_parts : TopStepLoRoot → TopStepLoJump → TopStep`.

## `TopStart`

For the top copy `u` of an origin `o` with the leg `l`:

* `row o ≥ row t`: proved (`topStartHi`);
* `row o < row t`, `l < c_r`: proved (`topStartLoLeft`);
* `row o < row t`, `l > c_r`, `u` not a gap copy, and no node of `l` at the row of `o`: proved
  (`topStartLoRightNC`, `pe` is the top copy of `pa`);
* `row o < row t`, `l > c_r`, `u` a gap copy or a node of `l` at the row of `o`:
  `TopStartLoRight` (**open**);
* `row o < row t`, `l = c_r`: `TopStartLoRoot` (**open**).

`topStart_of_parts : TopStartLoRoot → TopStartLoRight → TopStart`.

## Numerical tests (`reference/official/top-chain.cjs`)

No failure of any open piece on: all legal sequences of length `≤ 6` with entries `≤ 12`
(`n = 1, 2, 3`, 720307 expansions), `samples/known-counterexamples.json`,
`samples/legbelowtop-bad64.json`, and random legal sequences with entries up to 20 and 40
(see the final report of this task for the counts).
-/

namespace OmegaY.Official.Recon.TopChain

open Canonical Expansion Geometry Frame Classification
open CrossUpperSim CrossUpper
open Classification.Proofs.ChainCorr (MStep cutOrigin)
open Classification.Proofs (ScaleReach)
open Classification.Proofs.ChainCorr.LowerChain (CopyOf TopNode Stand TopStep TopStart above
  IsTopAt)
open LowerChainRecon (node_of_cell ref_inj reserve_rawParent_of_frame frame_rawParent_of_reserve)

/-- **Open.** `TopStep` below `row t` when the stored parent of `z` is in the root column. -/
def TopStepLoRoot : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i : Nat),
    Official.expandDiagram s n = .ok R → Recon.Top s M t root → 0 < i → i ≤ n →
    ∀ Z z, TopNode M R n root.column (M.size - 1) (official t.row) t.row i Z z →
    ∀ a cz ca, Reserve.rawParent M z = some a → Reserve.cell? M z = some cz →
      Reserve.cell? M a = some ca →
      (∀ c', Reserve.cell? M (above z) = some c' → c'.row < t.row) →
      a.column = root.column →
      ∃ A, MStep R (Row.jump cz.row ca.row) Z A ∧
        Stand M R n root.column (M.size - 1) (official t.row) t.row i A a

/-- **Open.** The jump bound of the step below `row t` from a top copy when the stored parent
of `z` is right of the root column. -/
def TopStepLoJump : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i : Nat),
    Official.expandDiagram s n = .ok R → Recon.Top s M t root → 0 < i → i ≤ n →
    ∀ Z z, TopNode M R n root.column (M.size - 1) (official t.row) t.row i Z z →
    ∀ a cz ca, Reserve.rawParent M z = some a → Reserve.cell? M z = some cz →
      Reserve.cell? M a = some ca →
      (∀ c', Reserve.cell? M (above z) = some c' → c'.row < t.row) →
      root.column < a.column →
      ∀ A cZ cA, Reserve.rawParent R Z = some A → Reserve.cell? R Z = some cZ →
        Reserve.cell? R A = some cA → Row.jump cZ.row cA.row ≤ Row.jump cz.row ca.row

/-- **`TopStep` from `TopStepLoRoot` and `TopStepLoJump`.** -/
theorem topStep_of_parts (hRoot : TopStepLoRoot) (hJump : TopStepLoJump) : TopStep := by
  intro s n R M t root i hrun hTop hi0 hin Z z hTN a cz ca hraw hcz hca
  have hi1 : 1 ≤ i := hi0
  -- the node above `z`
  by_cases hθ : ∃ c', Reserve.cell? M (above z) = some c' ∧ t.row ≤ c'.row
  · exact topStepHi hrun hTop hi0 hin hTN hraw hcz hca hθ
  have hlo : ∀ c', Reserve.cell? M (above z) = some c' → c'.row < t.row := by
    intro c' hc'
    by_contra hn
    exact hθ ⟨c', hc', le_of_not_gt hn⟩
  rcases Nat.lt_trichotomy a.column root.column with hl | he | hg
  · obtain ⟨ZN, VN, A, zN, z'N, aN, lo, us, jz, hZ, hz, ha, C⟩ :=
      lo_core hrun hTop hi1 hin hTN hraw hcz hca hlo
    subst hZ hz ha
    obtain ⟨hAa, hj⟩ := lo_left C hl
    refine ⟨Frame.ref A, ⟨reserve_rawParent_of_frame C.Araw, (Frame.ofMountain R).cell ZN,
      (Frame.ofMountain R).cell A, LowerChainRecon.cell?_ref ZN, LowerChainRecon.cell?_ref A, ?_,
      rawParent_column_lt C.E.FR C.Araw⟩, ?_⟩
    · have e1 : cz = (Frame.ofMountain M).cell zN := by
        rw [LowerChainRecon.cell?_ref] at hcz; exact (Option.some.inj hcz).symm
      have e2 : ca = (Frame.ofMountain M).cell aN := by
        rw [LowerChainRecon.cell?_ref] at hca; exact (Option.some.inj hca).symm
      subst e1 e2
      exact le_of_eq hj
    · rw [hAa]
      exact ⟨fun _ => rfl, fun h => absurd h (by simp only [Frame.ref] at hl ⊢; omega),
        fun h => absurd h (by simp only [Frame.ref] at hl ⊢; omega)⟩
  · exact hRoot s n R M t root i hrun hTop hi0 hin Z z hTN a cz ca hraw hcz hca hlo he
  · obtain ⟨ZN, VN, A, zN, z'N, aN, lo, us, jz, hZ, hz, ha, C⟩ :=
      lo_core hrun hTop hi1 hin hTN hraw hcz hca hlo
    subst hZ hz ha
    have hTA := lo_right C hg
    refine ⟨Frame.ref A, ⟨reserve_rawParent_of_frame C.Araw, (Frame.ofMountain R).cell ZN,
      (Frame.ofMountain R).cell A, LowerChainRecon.cell?_ref ZN, LowerChainRecon.cell?_ref A, ?_,
      rawParent_column_lt C.E.FR C.Araw⟩, ?_⟩
    · exact hJump s n R M t root i hrun hTop hi0 hin _ _ hTN _ cz ca hraw hcz hca hlo hg _ _ _
        (reserve_rawParent_of_frame C.Araw) (LowerChainRecon.cell?_ref ZN)
        (LowerChainRecon.cell?_ref A)
    · exact ⟨fun h => absurd h (by simp only [Frame.ref] at hg ⊢; omega),
        fun h => absurd h (by simp only [Frame.ref] at hg ⊢; omega), fun _ => hTA⟩

/-! ## `TopStart` -/

/-- **Open.** `TopStart` for an origin below `row t` whose leg is the root column. -/
def TopStartLoRoot : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i x : Nat),
    Official.expandDiagram s n = .ok R → Recon.Top s M t root → 0 < i → i ≤ n →
    x ∈ blockColumns root.column (M.size - 1) n i →
    ∀ es, emitsT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
        (x + (M.size - 1 - root.column) * i)) (official t.row) = .ok es →
    ∀ j (hj : j < es.length), IsTopAt es j →
    ∀ cu cv l pe pa,
      Reserve.cell? R ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ = some cu →
      Reserve.cell? M es[j].2.src = some cv → cv.left = some l →
      Reserve.highestAtMost M l.column cv.row = some pa →
      Reserve.highestAtMost R (Reserve.mapColumn root.column ((M.size - 1 - root.column) * i)
        l.column) cu.row = some pe →
      cv.row < t.row → l.column = root.column →
      Stand M R n root.column (M.size - 1) (official t.row) t.row i pe pa

/-- **Open.** `TopStart` for an origin below `row t` whose leg is right of the root column,
when the top copy `u` is a gap copy or the leg column has a node at the row of the origin. -/
def TopStartLoRight : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i x : Nat),
    Official.expandDiagram s n = .ok R → Recon.Top s M t root → 0 < i → i ≤ n →
    x ∈ blockColumns root.column (M.size - 1) n i →
    ∀ es, emitsT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
        (x + (M.size - 1 - root.column) * i)) (official t.row) = .ok es →
    ∀ j (hj : j < es.length), IsTopAt es j →
    ∀ cu cv l pe pa,
      Reserve.cell? R ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ = some cu →
      Reserve.cell? M es[j].2.src = some cv → cv.left = some l →
      Reserve.highestAtMost M l.column cv.row = some pa →
      Reserve.highestAtMost R (Reserve.mapColumn root.column ((M.size - 1 - root.column) * i)
        l.column) cu.row = some pe →
      cv.row < t.row → root.column < l.column →
      (cutOrigin es[j].2 = true ∨ ∃ cp, Reserve.cell? M pa = some cp ∧ cp.row = cv.row) →
      Stand M R n root.column (M.size - 1) (official t.row) t.row i pe pa

/-- **`TopStart` from `TopStartLoRoot` and `TopStartLoRight`.** -/
theorem topStart_of_parts (hRoot : TopStartLoRoot) (hRight : TopStartLoRight) : TopStart := by
  intro s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv hl hpa hpe
  by_cases hθ : t.row ≤ cv.row
  · exact topStartHi hrun hTop hi0 hin hx hes hj hcu hcv hl hpa hpe hθ
  have hlo : cv.row < t.row := lt_of_not_ge hθ
  rcases Nat.lt_trichotomy l.column root.column with hll | hle | hlg
  · exact topStartLoLeft hrun hTop hi0 hin hx hes hj hcu hcv hl hpa hpe hlo hll
  · exact hRoot s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv hl
      hpa hpe hlo hle
  · cases hcut : cutOrigin es[j].2
    · obtain ⟨_, _, col, hcol, hp, hprow, _⟩ :=
        Classification.Proofs.ChainCorr.highestAtMost_spec hpa
      obtain ⟨hpc, _⟩ := Classification.Proofs.ChainCorr.highestAtMost_spec hpa
      have hcp : Reserve.cell? M pa = some col[pa.index] := by
        simp only [Reserve.cell?, hpc, hcol, Option.bind_eq_bind, Option.bind_some]
        exact Array.getElem?_eq_getElem hp
      rcases lt_or_eq_of_le hprow with hlt | heq
      · refine topStartLoRightNC hrun hTop hi0 hin hx hes hj hcu hcv hl hpa hpe hlo hlg hcut ?_
        intro cp hcp'
        rw [hcp] at hcp'
        rw [← Option.some.inj hcp']
        exact hlt
      · exact hRight s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv
          hl hpa hpe hlo hlg (Or.inr ⟨_, hcp, heq⟩)
    · exact hRight s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv
        hl hpa hpe hlo hlg (Or.inl hcut)

/-- **The shared family from the four open pieces.** -/
theorem topStep_topStart_of_parts (hSR : TopStepLoRoot) (hSJ : TopStepLoJump)
    (hTR : TopStartLoRoot) (hTRi : TopStartLoRight) : TopStep ∧ TopStart :=
  ⟨topStep_of_parts hSR hSJ, topStart_of_parts hTR hTRi⟩

/-! ## `TopStepLoJump` from the jump law and a row property of the copies -/

/-- A row property of the copies (proved below, `lowExpCopy`). Below `row t`: the node `V`
above the top copy `Z` of `z` has no non-zero coefficient at or below an exponent `k` where the
node `z⁺` above `z` has none (the lowest non-zero exponent of `row V` is at most that of
`row z⁺`). -/
def LowExpCopy : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i : Nat),
    Official.expandDiagram s n = .ok R → Recon.Top s M t root → 0 < i → i ≤ n →
    ∀ Z z, TopNode M R n root.column (M.size - 1) (official t.row) t.row i Z z →
    ∀ a cz ca, Reserve.rawParent M z = some a → Reserve.cell? M z = some cz →
      Reserve.cell? M a = some ca →
      (∀ c', Reserve.cell? M (above z) = some c' → c'.row < t.row) →
      ∀ cV cz', Reserve.cell? R (above Z) = some cV → Reserve.cell? M (above z) = some cz' →
        ∀ k, (∀ k', k' ≤ k → cV.row.coeff k' = 0) → ∀ k', k' ≤ k → cz'.row.coeff k' = 0

/-- **`LowExpCopy` holds** (the row map does not raise the lowest non-zero exponent,
`TopChainLE.Ψ_lowExp`). -/
theorem lowExpCopy : LowExpCopy := by
  intro s n R M t root i hrun hTop hi0 hin Z z hTN a cz ca hraw hcz hca hlo cV cz' hcV hcz'
  have hi1 : 1 ≤ i := hi0
  obtain ⟨ZN, VN, A, zN, z'N, aN, lo, us, jz, hZ, hz, ha, C⟩ :=
    lo_core hrun hTop hi1 hin hTN hraw hcz hca hlo
  subst hZ hz ha
  have E := C.E
  have hG := E.G
  have e1 : cV = (Frame.ofMountain R).cell VN := by
    rw [← LowerChainRecon.above_of_upper C.Vu, LowerChainRecon.cell?_ref] at hcV
    exact (Option.some.inj hcV).symm
  have e2 : cz' = (Frame.ofMountain M).cell z'N := by
    rw [← LowerChainRecon.above_of_upper C.zu, LowerChainRecon.cell?_ref] at hcz'
    exact (Option.some.inj hcz').symm
  subst e1 e2
  -- the row of `V` is the image of the row of `z⁺`
  have hVmem : lo[jz + 1]'C.jzl ∈ lo := List.getElem_mem _
  have hVcut : LowerPB.cutO (lo[jz + 1]'C.jzl).2 = false := by
    rw [Proofs.CopyShape.Found.cutO_eq]; exact C.Vcut
  have hVc : Reserve.cell? M (lo[jz + 1]'C.jzl).2.src = some ((Frame.ofMountain M).cell z'N) := by
    rw [C.Vsrc]; exact LowerChainRecon.cell?_ref z'N
  obtain ⟨q, hq, hreg, hform⟩ := Proofs.CopyShape.ProfileLeg.lowerT_formula hrun hTop hi1 hin
    C.D.bctx C.D.hlo _ hVmem hVcut _ hVc
  obtain ⟨kk, jj, _, _, hkj⟩ := Recon.RowLaw.mem_lowerItems hq
  rw [hkj] at hreg hform
  simp only at hreg hform
  set r := official ((Frame.ofMountain M).cell z'N).row with hr
  set top := Proofs.CopyShape.InnerRow.topA (ctxAt M R zN.1.val i root.column
    (M.size - 1 - root.column) (M.size - 1) (zN.1.val + (M.size - 1 - root.column) * i))
  set E' := Proofs.CopyShape.ProfileLeg.blockEnv M R root.column i
  have hT : Proofs.CopyShape.ProfileLeg.TopOK E' top := Proofs.CopyShape.ProfileLeg.topOK_topA rfl rfl
  have hΨ : ∀ k0, r.coeff k0 ≠ 0 → ∃ k', k' ≤ k0 ∧ (lo[jz + 1]'C.jzl).1.row.coeff k' ≠ 0 := by
    intro k0 hk0
    rw [hform]
    by_cases hlt : k0 < kk
    · exact (Proofs.CopyShape.TopChainLE.Ψ_lowExp E' top hT kk _ _ r hreg).1 k0 hlt hk0
    · refine ⟨k0, le_rfl, ?_⟩
      have h1 := (Classification.inRegion_iff _ _ _).mp
        (Proofs.CopyShape.ProfileLeg.Ψ_mem E' top kk false (slot (kk + 2) (official t.row) jj)
          (slot (kk + 2) (official t.row) jj) r) k0 (by omega)
      have h2 := (Classification.inRegion_iff _ _ _).mp hreg k0 (by omega)
      rw [h1, ← h2]
      exact hk0
  -- `z⁺` is above the bottom
  obtain ⟨hz'1, hz'2⟩ := upper_spec C.zu
  have hzz' : (Frame.ofMountain M).height zN < (Frame.ofMountain M).height z'N :=
    Classification.ControlProof.height_lt_of_index hG hz'1.symm (by omega)
  have hr0 : (0 : Row) < r :=
    lt_of_le_of_lt (Row.zero_le _) (official_lt_frame hG C.zr hzz')
  have hz'r : (1 : Row) ≤ (Frame.ofMountain M).height z'N := one_le_height hG (by
    show 0 < z'N.2.val; omega)
  have hst := Proofs.CopyShape.TopChainLE.stored_lowExp hr0 hΨ
  intro k hV k' hk'
  have hV' : ∀ k', k' ≤ k → (stored (lo[jz + 1]'C.jzl).1.row).coeff k' = 0 := by
    intro k'' hk''
    have := hV k'' hk''
    rw [show ((Frame.ofMountain R).cell VN).row = (Frame.ofMountain R).height VN from rfl,
      C.Vrow] at this
    exact this
  have := hst k hV' k' hk'
  have hs : stored (official ((Frame.ofMountain M).cell z'N).row) =
      ((Frame.ofMountain M).cell z'N).row := Classification.stored_official hz'r
  rw [hr, hs] at this
  exact this

/-- **`TopStepLoJump` from the jump law of the output and `LowExpCopy`.** The jump law
`RowLaw.JumpLawHolds` follows from the stage-B statements `LowerRowsCopy` and
`LowerRowsBoundary` (`LowerLeftDone.jumpLawHolds_of_lowerRowsCases`). -/
theorem topStepLoJump_of_jumpLaw (hJ : RowLaw.JumpLawHolds) (hL : LowExpCopy) :
    TopStepLoJump := by
  intro s n R M t root i hrun hTop hi0 hin Z z hTN a cz ca hraw hcz hca hlo hag A' cZ cA hA' hcZ
    hcA
  have hi1 : 1 ≤ i := hi0
  obtain ⟨ZN, VN, A, zN, z'N, aN, lo, us, jz, hZ, hz, ha, C⟩ :=
    lo_core hrun hTop hi1 hin hTN hraw hcz hca hlo
  subst hZ hz ha
  have E := C.E
  have hG := E.G
  -- the stored parent is `A`
  have hAA : A' = Frame.ref A := by
    have := reserve_rawParent_of_frame C.Araw
    exact Option.some.inj (hA'.symm.trans this)
  subst hAA
  have e1 : cZ = (Frame.ofMountain R).cell ZN := by
    rw [LowerChainRecon.cell?_ref] at hcZ; exact (Option.some.inj hcZ).symm
  have e2 : cA = (Frame.ofMountain R).cell A := by
    rw [LowerChainRecon.cell?_ref] at hcA; exact (Option.some.inj hcA).symm
  have e3 : cz = (Frame.ofMountain M).cell zN := by
    rw [LowerChainRecon.cell?_ref] at hcz; exact (Option.some.inj hcz).symm
  have e4 : ca = (Frame.ofMountain M).cell aN := by
    rw [LowerChainRecon.cell?_ref] at hca; exact (Option.some.inj hca).symm
  subst e1 e2 e3 e4
  -- the bump of `V` over `Z`
  obtain ⟨hV1, hV2⟩ := upper_spec C.Vu
  obtain ⟨up, hup, hleft⟩ := rawParent_spec C.Araw
  rw [C.Vu] at hup
  obtain rfl := Option.some.inj hup
  have hc : ZN.1.val < R.size := ZN.1.isLt
  have hl : R[ZN.1.val][ZN.2.val]? = some ((Frame.ofMountain R).cell ZN) := by
    have := LowerChainRecon.cell?_ref ZN
    simpa [Reserve.cell?, Frame.ref, Array.getElem?_eq_getElem hc] using this
  have hu : R[ZN.1.val][ZN.2.val + 1]? = some ((Frame.ofMountain R).cell VN) := by
    have := LowerChainRecon.cell?_ref VN
    simp only [Reserve.cell?, Frame.ref, hV1, hV2, Array.getElem?_eq_getElem hc,
      Option.bind_eq_bind, Option.bind_some] at this
    exact this
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  have hx : s.length - 1 ≤ ZN.1.val := by rw [← E.Ms, C.Zc]; have := C.cy; omega
  have hZr : 0 < ZN.2.val := by rw [C.Zi]; omega
  obtain ⟨e, he⟩ := RowLaw.bumpChainHolds s n R hrun ZN.1.val hc hx ZN.2.val _ _ hl hu hZr
  have hcell : cellAt R (Frame.ref A) = .ok ((Frame.ofMountain R).cell A) := by
    have := LowerChainRecon.cell?_ref A
    rw [cellAt_ok_iff]
    unfold Reserve.cell? at this
    cases hcol : R[(Frame.ref A).column]? with
    | none => rw [hcol] at this; cases this
    | some col =>
      rw [hcol] at this
      exact ⟨col, rfl, by simpa using this⟩
  have hj := hJ s n R hrun ZN.1.val hc hx ZN.2.val _ _ _ _ e hl hu hZr hleft hcell he
  rw [hj]
  -- the row law of `M`
  have hM := m_rowLaw E C.zr C.zu C.zraw
  by_contra hne
  have hlt : Row.jump ((Frame.ofMountain M).height zN) ((Frame.ofMountain M).height aN) < e :=
    lt_of_not_ge hne
  set e' := Row.jump ((Frame.ofMountain M).height zN) ((Frame.ofMountain M).height aN)
  have hVc : Reserve.cell? R (above (Frame.ref ZN)) = some ((Frame.ofMountain R).cell VN) := by
    rw [← LowerChainRecon.above_of_upper C.Vu]; exact LowerChainRecon.cell?_ref VN
  have hz'c : Reserve.cell? M (above (Frame.ref zN)) = some ((Frame.ofMountain M).cell z'N) := by
    rw [← LowerChainRecon.above_of_upper C.zu]; exact LowerChainRecon.cell?_ref z'N
  have hzero := hL s n R M t root i hrun hTop hi0 hin _ _ hTN _ _ _ hraw
    (LowerChainRecon.cell?_ref zN) (LowerChainRecon.cell?_ref aN) hlo _ _ hVc hz'c e'
    (fun k' hk' => by
      rw [he]
      exact Row.coeff_bump_low (by omega)) e' le_rfl
  change ((Frame.ofMountain M).height z'N).coeff e' = 0 at hzero
  rw [hM, Row.coeff_bump_at] at hzero
  omega

/-- **`TopStepLoJump` from the stage-B row laws** (`LowExpCopy` is proved). -/
theorem topStepLoJump_of_rows (hC : JumpLawLower.LowerRowsCopy)
    (hB : JumpLawLower.LowerRowsBoundary) : TopStepLoJump :=
  topStepLoJump_of_jumpLaw (LowerLeftDone.jumpLawHolds_of_lowerRowsCases hC hB) lowExpCopy

/-- **The shared family from `TopStepLoRoot`, `TopStartLoRoot`, `TopStartLoRight` and the
stage-B row laws `LowerRowsCopy`, `LowerRowsBoundary`.** -/
theorem topStep_topStart_of_rows (hSR : TopStepLoRoot) (hTR : TopStartLoRoot)
    (hTRi : TopStartLoRight) (hC : JumpLawLower.LowerRowsCopy)
    (hB : JumpLawLower.LowerRowsBoundary) : TopStep ∧ TopStart :=
  topStep_topStart_of_parts hSR (topStepLoJump_of_rows hC hB) hTR hTRi

end OmegaY.Official.Recon.TopChain

#print axioms OmegaY.Official.Recon.TopChain.topStepHi
#print axioms OmegaY.Official.Recon.TopChain.topStartHi
#print axioms OmegaY.Official.Recon.TopChain.lo_core
#print axioms OmegaY.Official.Recon.TopChain.lo_left
#print axioms OmegaY.Official.Recon.TopChain.lo_right
#print axioms OmegaY.Official.Recon.TopChain.topStep_of_parts
#print axioms OmegaY.Official.Recon.TopChain.topStartLoLeft
#print axioms OmegaY.Official.Recon.TopChain.topStartLoRightNC
#print axioms OmegaY.Official.Recon.TopChain.topStart_of_parts
#print axioms OmegaY.Official.Recon.TopChain.topStep_topStart_of_parts
#print axioms OmegaY.Official.Recon.TopChain.topStepLoJump_of_jumpLaw
#print axioms OmegaY.Official.Recon.TopChain.lowExpCopy
#print axioms OmegaY.Official.Recon.TopChain.topStep_topStart_of_rows
