/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/SeamReduce.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TopChainMain
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StartRootPartsX0
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LRCJump

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# The seam: `TopStepLoRoot`, `TopStartLoRoot`, `BoundaryChain` from one chain statement

Notation: `c_r = col root`, `x₀ = |M| - 1`, `w = x₀ - c_r`, `τ = official (row t)`,
`B_i = c_r + w·i = x₀ + w·(i - 1)` the boundary column of block `i ≥ 1` (the copy of `x₀` made
by block `i - 1`).

* `BoundaryChainD` is `BoundaryChain` for the diagram `R = expandDiagram s n` (no canonicity of
  `R` is assumed): the scale-`k` chain of a node of `B_i` reaches every node left of `c_r` that the
  scale-`k` chain of its origin reaches in `M(s)`.
* `boundaryChain_of_diag : BoundaryChainD → BoundaryChain`.
* `rootJump`: the jump bound of `TopStepLoRoot` (the proof of `topStepLoJump_of_jumpLaw` does not
  use the side of the stored parent; the jump law is proved, `LRC.jumpLawHolds`).
* `StepRootLookup`, `StartRootLookup`: the stand-in `A` (resp. `pe`) in `B_i` is a lower node whose
  origin `ν` (a node of `x₀` below `τ`) has `hAM(c_r, row ν) = a` (resp. `pa`).
* `StepRootTop`, `StartRootTop`: the second clause of `Stand` (when the node above `a` is at or
  above `τ`).
* `topStepLoRoot_of_parts`, `topStartLoRoot_of_parts`: the third clause of `Stand` from
  `BoundaryChainD`, the lookup and the proved `SRX0.x0Reach`.
-/

namespace OmegaY.Official.Recon.TopChain.Seam

open Canonical Expansion Geometry Frame Classification
open CrossUpperSim CrossUpper
open Classification.Proofs.ChainCorr (MStep cutOrigin blockEmits)
open Classification.Proofs (ScaleReach)
open Classification.Proofs.ChainCorr.LowerChain (CopyOf TopNode Stand TopStep TopStart above
  IsTopAt)
open LowerChainRecon (node_of_cell ref_inj reserve_rawParent_of_frame frame_rawParent_of_reserve)

/-! ## The statements -/

/-- **(core)** `BoundaryChain` for the diagram of a run. -/
def BoundaryChainD : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref),
    Official.expandDiagram s n = .ok R → Recon.Top s M t root →
    ∀ i, 0 < i → i ≤ n →
    ∀ esB, blockEmits M R root.column (M.size - 1) (official t.row) (i - 1) (M.size - 1) =
        .ok esB →
      ∀ k (hk : k < esB.length) kk (m : Ref), m.column < root.column →
        ScaleReach M kk esB[k].2.src m →
        ScaleReach R kk ⟨M.size - 1 + (M.size - 1 - root.column) * (i - 1), k + 1⟩ m

/-- The jump bound of the step from a top copy below `τ`, for any column of the stored parent. -/
def TopStepLoJumpAll : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i : Nat),
    Official.expandDiagram s n = .ok R → Recon.Top s M t root → 0 < i → i ≤ n →
    ∀ Z z, TopNode M R n root.column (M.size - 1) (official t.row) t.row i Z z →
    ∀ a cz ca, Reserve.rawParent M z = some a → Reserve.cell? M z = some cz →
      Reserve.cell? M a = some ca →
      (∀ c', Reserve.cell? M (above z) = some c' → c'.row < t.row) →
      ∀ A cZ cA, Reserve.rawParent R Z = some A → Reserve.cell? R Z = some cZ →
        Reserve.cell? R A = some cA → Row.jump cZ.row cA.row ≤ Row.jump cz.row ca.row

/-- The lookup of the stand-in of a stored parent in the root column. -/
def StepRootLookup : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i : Nat),
    Official.expandDiagram s n = .ok R → Recon.Top s M t root → 0 < i → i ≤ n →
    ∀ Z z, TopNode M R n root.column (M.size - 1) (official t.row) t.row i Z z →
    ∀ a cz ca, Reserve.rawParent M z = some a → Reserve.cell? M z = some cz →
      Reserve.cell? M a = some ca →
      (∀ c', Reserve.cell? M (above z) = some c' → c'.row < t.row) →
      a.column = root.column →
      ∀ A, Reserve.rawParent R Z = some A →
        ∃ esB k, ∃ hk : k < esB.length,
          blockEmits M R root.column (M.size - 1) (official t.row) (i - 1) (M.size - 1) =
            .ok esB ∧
          A = ⟨M.size - 1 + (M.size - 1 - root.column) * (i - 1), k + 1⟩ ∧
          ∃ cν, Reserve.cell? M esB[k].2.src = some cν ∧ esB[k].2.src.column = M.size - 1 ∧
            1 ≤ esB[k].2.src.index ∧ cν.row < t.row ∧
            Reserve.highestAtMost M root.column cν.row = some a

/-- The second clause of `Stand` for the step from a top copy with the stored parent in the root
column. -/
def StepRootTop : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i : Nat),
    Official.expandDiagram s n = .ok R → Recon.Top s M t root → 0 < i → i ≤ n →
    ∀ Z z, TopNode M R n root.column (M.size - 1) (official t.row) t.row i Z z →
    ∀ a cz ca, Reserve.rawParent M z = some a → Reserve.cell? M z = some cz →
      Reserve.cell? M a = some ca →
      (∀ c', Reserve.cell? M (above z) = some c' → c'.row < t.row) →
      a.column = root.column →
      ∀ A, Reserve.rawParent R Z = some A →
      ∀ ca', Reserve.cell? M (above a) = some ca' → t.row ≤ ca'.row →
        ∃ cA, Reserve.cell? R (above A) = some cA ∧ cA.row = ca'.row

/-- The lookup of the start in the root column. -/
def StartRootLookup : Prop :=
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
        ∃ esB k, ∃ hk : k < esB.length,
          blockEmits M R root.column (M.size - 1) (official t.row) (i - 1) (M.size - 1) =
            .ok esB ∧
          pe = ⟨M.size - 1 + (M.size - 1 - root.column) * (i - 1), k + 1⟩ ∧
          ∃ cν, Reserve.cell? M esB[k].2.src = some cν ∧ esB[k].2.src.column = M.size - 1 ∧
            1 ≤ esB[k].2.src.index ∧ cν.row < t.row ∧
            Reserve.highestAtMost M root.column cν.row = some pa

/-- The second clause of `Stand` for the start in the root column.

**FALSE** (review 2026-09-24): counterexample `(1,13,29,4,18,25,15)[1]` (JS indices, no phantom):
`c_r = 3`, `x₀ = 6`, `τ = ω·2`, `u = (8,4)` the top copy of `o = (5,3)` (row `ω`, leg `c_r`),
`pa = (3,2)`, the node above `pa` is `(3,3)` of row `ω² ≥ τ`, `pe = (6,3)`, and the node above
`pe` is `(6,4)` of row `ω+1 ≠ ω²`. This is the known counterexample of `TopStartLoRoot`. -/
def StartRootTop : Prop :=
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
      ∀ ca, Reserve.cell? M (above pa) = some ca → t.row ≤ ca.row →
        ∃ cA, Reserve.cell? R (above pe) = some cA ∧ cA.row = ca.row

/-! ## `BoundaryChain` -/

theorem boundaryChain_of_diag (h : BoundaryChainD) :
    Classification.Proofs.ChainCorr.BoundaryChain := by
  intro s n D M out ρ R t hd i hi0 hin esB hes k hk kk m hm hr
  obtain ⟨root, hTop, hroot, hx0⟩ := Classification.Proofs.ChainCorr.SRParts.data_top hd
  have hes' : blockEmits M R root.column (M.size - 1) (official t.row) (i - 1) (M.size - 1) =
      .ok esB := by rw [hroot, ← hx0]; exact hes
  have := h s n R M t root hd.run hTop i hi0 (by omega) esB hes' k hk kk m (by rw [hroot]; exact hm)
    hr
  rw [hroot, ← hx0] at this
  exact this

/-! ## The jump bound -/

theorem rootJump (hJ : RowLaw.JumpLawHolds) (hL : LowExpCopy) : TopStepLoJumpAll := by
  intro s n R M t root i hrun hTop hi0 hin Z z hTN a cz ca hraw hcz hca hlo A' cZ cA hA' hcZ hcA
  have hi1 : 1 ≤ i := hi0
  obtain ⟨ZN, VN, A, zN, z'N, aN, lo, us, jz, hZ, hz, ha, C⟩ :=
    lo_core hrun hTop hi1 hin hTN hraw hcz hca hlo
  subst hZ hz ha
  have E := C.E
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

/-- **The jump bound of `TopStepLoRoot`** (no hypothesis). -/
theorem topStepLoJumpAll : TopStepLoJumpAll := rootJump LRC.jumpLawHolds lowExpCopy

/-! ## The root-column steps -/

/-- The chain clause from the lookup, `X0Reach` and `BoundaryChainD`. -/
theorem reach_of_lookup (hB : BoundaryChainD) {s : List Nat} {n : Nat} {R M : Mountain}
    {t : Cell} {root : Ref} (hrun : Official.expandDiagram s n = .ok R)
    (hTop : Recon.Top s M t root) {i : Nat} (hi0 : 0 < i) (hin : i ≤ n)
    {esB : List (Emit × Origin)} {k : Nat} (hk : k < esB.length)
    (hes : blockEmits M R root.column (M.size - 1) (official t.row) (i - 1) (M.size - 1) =
      .ok esB)
    {cν : Cell} (hcν : Reserve.cell? M esB[k].2.src = some cν)
    (hνc : esB[k].2.src.column = M.size - 1) (hν1 : 1 ≤ esB[k].2.src.index)
    (hνt : cν.row < t.row) {a : Ref} (ha : Reserve.highestAtMost M root.column cν.row = some a) :
    ∀ b ca cb, Reserve.rawParent M a = some b → Reserve.cell? M a = some ca →
      Reserve.cell? M b = some cb →
      ScaleReach R (Row.jump ca.row cb.row)
        ⟨M.size - 1 + (M.size - 1 - root.column) * (i - 1), k + 1⟩ b := by
  intro b ca cb hb hca hcb
  have hVM := build_valid_of_success hTop.build
  have hlt := (Classification.Proofs.ChainCorr.Inner.rawParent_cells hVM hb).2.2
  have hac : a.column = root.column :=
    (Classification.Proofs.ChainCorr.highestAtMost_spec ha).1
  have hst : MStep M (Row.jump ca.row cb.row) a b := ⟨hb, ca, cb, hca, hcb, le_rfl, hlt⟩
  have hM := Classification.Proofs.ChainCorr.SRX0.x0Reach s M t root hTop _ cν hνc hν1 hcν hνt a
    ha _ b hst
  exact hB s n R M t root hrun hTop i hi0 hin esB hes k hk _ b (by omega) hM

/-- **`TopStepLoRoot` from `BoundaryChainD`, `StepRootLookup` and `StepRootTop`.** -/
theorem topStepLoRoot_of_parts (hB : BoundaryChainD) (hL : StepRootLookup)
    (hT : StepRootTop) : TopStepLoRoot := by
  intro s n R M t root i hrun hTop hi0 hin Z z hTN a cz ca hraw hcz hca hlo he
  have hi1 : 1 ≤ i := hi0
  obtain ⟨ZN, VN, A, zN, z'N, aN, lo, us, jz, hZ, hz, ha, C⟩ :=
    lo_core hrun hTop hi1 hin hTN hraw hcz hca hlo
  have hAraw : Reserve.rawParent R Z = some (Frame.ref A) := by
    rw [← hZ]; exact reserve_rawParent_of_frame C.Araw
  have hcZ : Reserve.cell? R Z = some ((Frame.ofMountain R).cell ZN) := by
    rw [← hZ]; exact LowerChainRecon.cell?_ref ZN
  have hcA := LowerChainRecon.cell?_ref A
  have hlt : (Frame.ref A).column < Z.column := by
    rw [← hZ]; exact rawParent_column_lt C.E.FR C.Araw
  refine ⟨Frame.ref A, ⟨hAraw, _, _, hcZ, hcA, topStepLoJumpAll s n R M t root i hrun hTop hi0
    hin Z z hTN a cz ca hraw hcz hca hlo _ _ _ hAraw hcZ hcA, hlt⟩, ?_⟩
  refine ⟨fun h => absurd he (by omega), fun _ => ⟨?_, ?_, ?_⟩, fun h => absurd he (by omega)⟩
  · have hAc := C.Ac
    rw [← ha] at he
    simp only [Frame.ref] at he ⊢
    rw [hAc, shiftCol_of_le (le_of_eq he.symm), he]
  · intro ca' hca' hθ
    exact hT s n R M t root i hrun hTop hi0 hin Z z hTN a cz ca hraw hcz hca hlo he _ hAraw ca'
      hca' hθ
  · obtain ⟨esB, k, hk, hes, hAeq, cν, hcν, hνc, hν1, hνt, hpa⟩ :=
      hL s n R M t root i hrun hTop hi0 hin Z z hTN a cz ca hraw hcz hca hlo he _ hAraw
    rw [hAeq]
    exact reach_of_lookup hB hrun hTop hi0 hin hk hes hcν hνc hν1 hνt hpa

/-- **`TopStartLoRoot` from `BoundaryChainD`, `StartRootLookup` and `StartRootTop`.** -/
theorem topStartLoRoot_of_parts (hB : BoundaryChainD) (hL : StartRootLookup)
    (hT : StartRootTop) : TopStartLoRoot := by
  intro s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv hl hpa
    hpe hlo he
  have hpac : pa.column = root.column := by
    rw [(Classification.Proofs.ChainCorr.highestAtMost_spec hpa).1, he]
  refine ⟨fun h => absurd hpac (by omega), fun _ => ⟨?_, ?_, ?_⟩,
    fun h => absurd hpac (by omega)⟩
  · rw [(Classification.Proofs.ChainCorr.highestAtMost_spec hpe).1, he,
      Classification.Proofs.ChainCorr.mapColumn_of_ge (le_refl _)]
  · intro ca hca hθ
    exact hT s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv hl
      hpa hpe hlo he ca hca hθ
  · obtain ⟨esB, k, hk, hesB, hpeq, cν, hcν, hνc, hν1, hνt, hpa'⟩ :=
      hL s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv hl hpa
        hpe hlo he
    rw [hpeq]
    exact reach_of_lookup hB hrun hTop hi0 hin hk hesB hcν hνc hν1 hνt hpa'

end OmegaY.Official.Recon.TopChain.Seam

#print axioms OmegaY.Official.Recon.TopChain.Seam.boundaryChain_of_diag
#print axioms OmegaY.Official.Recon.TopChain.Seam.topStepLoJumpAll
#print axioms OmegaY.Official.Recon.TopChain.Seam.topStepLoRoot_of_parts
#print axioms OmegaY.Official.Recon.TopChain.Seam.topStartLoRoot_of_parts
