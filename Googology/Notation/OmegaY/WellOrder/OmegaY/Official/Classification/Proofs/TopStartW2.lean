/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/TopStartW2.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TSQFinal
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CPNMain

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# The weaker start `TopStart''` (proved)

`TopStart'` (`TopStartFix.lean`) is false: its strong clause (`HasAboveLow → Stand pe pa`)
fails for `s = (1,4,18,56,18)`, `n = 1` (JS indices `u = (6,5)`, the plain top copy of
`o = (3,4)` at the row `ω`, `o⁺ = (3,5)` at the row `ω² < τ = ω² + 1`, leg `l = 2 > c_r = 1`,
`pa = (2,3)` at the row of `o`): `pe = (5,4)` is the clean copy of `pa`, and the gap copy
`(5,5)` of `pa` lies above it, so `pe` is not the top copy of `pa`
(`reference/official/top-start-fix.cjs`: `TopStartUp [o<tau, l>cr, plain] FAIL`). The same
happens for `(1,21,5,20,59,20)[1]`. Its piece `TopStartPaOUp` is false there, and the statement
`RootValueIn` it was reduced to is false in Lean (`TSQRootValueInFalse.lean`).

## The corrected statement

`StandQ i A a` is `Stand i A a` with the clause right of `c_r` weakened from `TopNode` to
`Rel = CopyNode ∨ TopNode` (the other two clauses, in particular the clause on the node above `a`
in the root column, are kept). `TopStart''` (same hypotheses as `TopStart'`) concludes

* `StandW pe pa` (the first part of `TopStart'`, unchanged), and
* `StandQ pe pa` when the origin `o` has a node above it below `row t` (`HasAboveLow`).

`TopStart' → TopStart''` (`topStart''_of_topStart'`).

## Proof

The split of `TopStartFixParts.topStart'_of_parts`: the cases `row o ≥ τ`, `l < c_r` and
(`l > c_r`, `u` not a gap copy, no node of `l` at the row of `o`) give the full `Stand`
(`topStartHi`, `topStartLoLeft`, `topStartLoRightNC`); the root case `l = c_r` is
`TopStartLoRootW` (from `CutParentNT`, `TSQ.topStartLoRootW_of_cutParent`) and `StartRootTopUp`
(`TSQ.BTL.startRootTopUp`); the case `l > c_r` with `u` a gap copy is `TopStartCutRight`
(`TSQ.topStartCutRight`); the case `l > c_r` with `pa` at the row of `o` and `u` not a gap copy
is `TopStartFixParts.startPaORel` (`pe` is a non-gap copy of `pa`, so `Rel pe pa`). The false
piece `TopStartPaOUp` is not needed.

* `topStart''_of_parts : TopStartLoRootW → StartRootTopUp → TopStartCutRight → TopStart''`;
* **`topStart''_holds : TopStart''`** (no hypothesis).
-/

namespace OmegaY.Official.Recon.TopStartW2

open Canonical Expansion Geometry Frame Classification
open Classification.Proofs.ChainCorr (MStep cutOrigin CopyNode)
open Classification.Proofs (ScaleReach)
open Classification.Proofs.ChainCorr.LowerChain (CopyOf TopNode Stand Rel TopStep above IsTopAt)
open Classification.Proofs.ChainCorr.TopStartFix (TopStart' StandW HasAboveLow standW_of_stand)
open TopChain

/-! ## Definitions -/

/-- **The stand-in relation of the strong clause**: `Stand` with `Rel` (a non-gap copy or the top
copy) in place of `TopNode` right of `c_r`. -/
def StandQ (M R : Mountain) (n cr x0 : Nat) (τ θ : Row) (i : Nat) (A a : Ref) : Prop :=
  (a.column < cr → A = a) ∧
  (a.column = cr → A.column = cr + (x0 - cr) * i ∧
    (∀ ca, Reserve.cell? M (above a) = some ca → θ ≤ ca.row →
      ∃ cA, Reserve.cell? R (above A) = some cA ∧ cA.row = ca.row) ∧
    (∀ b ca cb, Reserve.rawParent M a = some b → Reserve.cell? M a = some ca →
      Reserve.cell? M b = some cb → ScaleReach R (Row.jump ca.row cb.row) A b)) ∧
  (cr < a.column → Rel M R n cr x0 τ θ i A a)

/-- **`TopStart''`** (same hypotheses as `TopStart'`): `pe` stands for `pa` in the weak sense
`StandW`, and in the sense `StandQ` when the origin has a node above it below `row t`. -/
def TopStart'' : Prop :=
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
      StandW M R n root.column (M.size - 1) (official t.row) t.row i pe pa ∧
      (HasAboveLow M t.row es[j].2.src →
        StandQ M R n root.column (M.size - 1) (official t.row) t.row i pe pa)

/-! ## Elementary facts -/

theorem standQ_of_stand {M R : Mountain} {n cr x0 : Nat} {τ θ : Row} {i : Nat} {A a : Ref}
    (h : Stand M R n cr x0 τ θ i A a) : StandQ M R n cr x0 τ θ i A a :=
  ⟨h.1, h.2.1, fun hc => Or.inr (h.2.2 hc)⟩

theorem standW_of_standQ {M R : Mountain} {n cr x0 : Nat} {τ θ : Row} {i : Nat} {A a : Ref}
    (h : StandQ M R n cr x0 τ θ i A a) : StandW M R n cr x0 τ θ i A a :=
  ⟨h.1, fun hc => ⟨(h.2.1 hc).1, (h.2.1 hc).2.2⟩, h.2.2⟩

theorem standQ_of_right {M R : Mountain} {n cr x0 : Nat} {τ θ : Row} {i : Nat} {A a : Ref}
    (hc : cr < a.column) (h : Rel M R n cr x0 τ θ i A a) : StandQ M R n cr x0 τ θ i A a :=
  ⟨fun h' => absurd h' (by omega), fun h' => absurd h' (by omega), fun _ => h⟩

/-- The old (false) `TopStart'` implies `TopStart''`. -/
theorem topStart''_of_topStart' (h : TopStart') : TopStart'' := by
  intro s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv hl hpa hpe
  obtain ⟨h1, h2⟩ := h s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu
    hcv hl hpa hpe
  exact ⟨h1, fun hab => standQ_of_stand (h2 hab)⟩

/-! ## `TopStart''` from the proved pieces -/

/-- **`TopStart''` from `TopStartLoRootW`, `StartRootTopUp` and `TopStartCutRight`.** -/
theorem topStart''_of_parts (hW : TopStartFixParts.TopStartLoRootW)
    (hU : TopStartFixParts.StartRootTopUp) (hCut : TopStartFixParts.TopStartCutRight) :
    TopStart'' := by
  intro s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv hl hpa hpe
  have full : Stand M R n root.column (M.size - 1) (official t.row) t.row i pe pa →
      StandW M R n root.column (M.size - 1) (official t.row) t.row i pe pa ∧
      (HasAboveLow M t.row es[j].2.src →
        StandQ M R n root.column (M.size - 1) (official t.row) t.row i pe pa) :=
    fun h => ⟨standW_of_stand h, fun _ => standQ_of_stand h⟩
  have hpac : pa.column = l.column := (Classification.Proofs.ChainCorr.highestAtMost_spec hpa).1
  have right : root.column < l.column →
      Rel M R n root.column (M.size - 1) (official t.row) t.row i pe pa →
      StandW M R n root.column (M.size - 1) (official t.row) t.row i pe pa ∧
      (HasAboveLow M t.row es[j].2.src →
        StandQ M R n root.column (M.size - 1) (official t.row) t.row i pe pa) := by
    intro hlg hR
    have hc : root.column < pa.column := by rw [hpac]; exact hlg
    exact ⟨TopStartFixParts.standW_of_right hc hR, fun _ => standQ_of_right hc hR⟩
  by_cases hθ : t.row ≤ cv.row
  · exact full (topStartHi hrun hTop hi0 hin hx hes hj hcu hcv hl hpa hpe hθ)
  have hlo : cv.row < t.row := lt_of_not_ge hθ
  rcases Nat.lt_trichotomy l.column root.column with hll | hle | hlg
  · exact full (topStartLoLeft hrun hTop hi0 hin hx hes hj hcu hcv hl hpa hpe hlo hll)
  · -- the root column: the weak part and the clause on the node above `pa`
    have hSW := hW s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv
      hl hpa hpe hlo hle
    refine ⟨hSW, fun hab => ⟨hSW.1, fun hc => ?_, hSW.2.2⟩⟩
    obtain ⟨hcol, hch⟩ := hSW.2.1 hc
    exact ⟨hcol, hU s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv
      hl hpa hpe hlo hle hab, hch⟩
  · cases hcut : cutOrigin es[j].2
    · obtain ⟨hpc, _, col, hcol, hp, hprow, _⟩ :=
        Classification.Proofs.ChainCorr.highestAtMost_spec hpa
      have hcp : Reserve.cell? M pa = some col[pa.index] := by
        simp only [Reserve.cell?, hpc, hcol, Option.bind_eq_bind, Option.bind_some]
        exact Array.getElem?_eq_getElem hp
      rcases lt_or_eq_of_le hprow with hlt | heq
      · refine full
          (topStartLoRightNC hrun hTop hi0 hin hx hes hj hcu hcv hl hpa hpe hlo hlg hcut ?_)
        intro cp hcp'
        rw [hcp] at hcp'
        rw [← Option.some.inj hcp']
        exact hlt
      · -- `pa` at the row of `o`: `pe` is a non-gap copy of `pa`
        exact right hlg (Or.inl (TopStartFixParts.startPaORel hrun hTop hi0 hin hx hes hj hcu
          hcv hl hpa hpe hlo hlg hcut ⟨_, hcp, heq⟩))
    · exact right hlg (hCut s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe
        pa hcu hcv hl hpa hpe hlo hlg hcut).1

/-- **`TopStart''` holds.** -/
theorem topStart''_holds : TopStart'' :=
  topStart''_of_parts (TSQ.topStartLoRootW_of_cutParent TopChain.Seam.CPN.cutParentNT)
    TSQ.BTL.startRootTopUp TSQ.topStartCutRight

end OmegaY.Official.Recon.TopStartW2

#print axioms OmegaY.Official.Recon.TopStartW2.topStart''_of_topStart'
#print axioms OmegaY.Official.Recon.TopStartW2.topStart''_of_parts
#print axioms OmegaY.Official.Recon.TopStartW2.topStart''_holds
