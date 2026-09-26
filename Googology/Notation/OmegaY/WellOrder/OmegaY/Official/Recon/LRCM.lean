/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/LRCM.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LRCTop

set_option backward.do.legacy false

/-!
# Facts about the source mountain for the copy case

* `gen_shift`, `gen_step`: counting generations of a root row `C` from `x` gives one more than
  from the leg column `l` of the node `(x, C)` (the argument of `LowerCopyClean.lean`).
* `anch_of`: the anchor facts `Anch` for the origin node `(x, a)` of `θ`, from `ascLeg`,
  `ascLegLe` and `gen_step`.
* `reach_of_inTree`: the items of the tree are reached (for (MD), (MH)).
-/

namespace OmegaY.Official.Recon.LRC

open Canonical Expansion Dimension RowLaw JumpLaw JumpLawLower
open Classification Classification.Proofs.ChainCorr Reserve

theorem gen_shift (M : Mountain) (cr : Nat) (C : Row) :
    ∀ f r c g0 a, generations M cr C f r c g0 = .ok a →
      ∀ f' g0' b, generations M cr C f' r c g0' = .ok b → a + g0' = b + g0
  | 0, _, _, _, _, h => by simp [generations, throw, throwThe, MonadExceptOf.throw] at h
  | f + 1, r, c, g0, a, h => by
    intro f' g0' b h'
    cases f' with
    | zero => simp [generations, throw, throwThe, MonadExceptOf.throw] at h'
    | succ f' =>
      unfold generations at h h'
      by_cases hc : r.column ≤ cr
      · rw [if_pos hc] at h h'
        simp only [pure, Except.pure, Except.ok.injEq] at h h'
        omega
      · rw [if_neg hc] at h h'
        simp only [bind, Except.bind] at h h'
        cases hl : leftColumn c with
        | error e => rw [hl] at h; cases h
        | ok p =>
          rw [hl] at h h'
          simp only at h h'
          by_cases hp : p < r.column
          · rw [if_neg (by omega)] at h h'
            cases hn : nodeAt M p C with
            | none => rw [hn] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
            | some q =>
              obtain ⟨r2, c2⟩ := q
              rw [hn] at h h'
              simp only at h h'
              have := gen_shift M cr C f r2 c2 (g0 + 1) a h f' (g0' + 1) b h'
              omega
          · rw [if_pos (by omega)] at h
            simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **One generation step.** -/
theorem gen_step {M : Mountain} {cr : Nat} {C : Row} {fx fy : Nat} {rx : Ref} {cx : Cell}
    {gx gy l : Nat} {ry : Ref} {cy : Cell}
    (hx : generations M cr C fx rx cx 0 = .ok gx) (hcx : cr < rx.column)
    (hl : leftColumn cx = .ok l) (hlx : l < rx.column) (hny : nodeAt M l C = some (ry, cy))
    (hy : generations M cr C fy ry cy 0 = .ok gy) : gx = gy + 1 := by
  cases fx with
  | zero => simp [generations, throw, throwThe, MonadExceptOf.throw] at hx
  | succ fx =>
    unfold generations at hx
    rw [if_neg (by omega)] at hx
    simp only [bind, Except.bind, hl] at hx
    rw [if_neg (by omega), hny] at hx
    have := gen_shift M cr C fx ry cy 1 gx hx fy 0 gy hy
    omega

/-- The node of a column at a given official row is unique. -/
theorem nodeAt_eq_of_mem {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M) {c : Nat}
    {p q : Ref × Cell} (hp : p ∈ realNodes M c) (hq : nodeAt M c (official p.2.row) = some q) :
    q = p := by
  have hV := build_valid_of_success hb
  obtain ⟨hqm, hqr⟩ := RowLaw.nodeAt_spec hq
  exact realNodes_eq_of_official hV hqm hp hqr

/-- **The anchor facts** for the origin node `(x, a)` of `θ` with leg column `l`, `c_r < l < x`. -/
theorem anch_of {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i x l : Nat}
    (h : CS s n R M t root i x l) {u : Ref × Cell} (hu : u ∈ realNodes M x)
    (hleg : leftColumn u.2 = .ok l) :
    Anch (colCtx M R root i x) (colCtx M R root i l) (official u.2.row) := by
  have hb := h.ncx.top.build
  obtain ⟨huc, hu1, hucell⟩ := Classification.mem_realNodes hu
  have hcell : cell? M ⟨x, u.1.index⟩ = some u.2 := by rw [← huc]; exact hucell
  obtain ⟨lref, hlref, hlc⟩ := Classification.leftColumn_ok hleg
  have hxgt := h.xgt
  refine ⟨?_, ?_, ?_⟩
  · intro d S ρr ρc hρ hlt
    exact Proofs.CopyShape.AscLeg.ascLeg hb hxgt hu1 hcell hlref (by rw [hlc]; exact h.lgt.le) hρ hlt
      _ _ rfl rfl rfl rfl rfl hlc.symm
  · intro d S ρr ρc hρ hle
    exact Proofs.CopyShape.AscLeg.ascLegLe hb hxgt hu1 hcell hlref (by rw [hlc]; exact h.lgt.le) hρ
      hle _ _ rfl rfl rfl rfl rfl hlc.symm
  · intro refx cx gx refy cy gy hnx hgx hny hgy
    have hq := nodeAt_eq_of_mem hb hu hnx
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq
    exact gen_step hgx (by rw [huc]; exact hxgt) hleg (by rw [huc]; exact h.llt) hny hgy

/-- The items of the tree are reached. -/
theorem reach_of_desc {ctx : Context} {τ : Row} {d : Nat} {A : Item} {d' : Nat} {B : Item}
    (hD : Desc ctx d A d' B) (hA : Proofs.CopyShape.Reach ctx τ d A) :
    Proofs.CopyShape.Reach ctx τ d' B := by
  induction hD with
  | refl => exact hA
  | step hcs hc _ ih => exact ih (Proofs.CopyShape.Reach.child hA hcs hc)

theorem reach_of_inTree {ctx : Context} {τ : Row} {d : Nat} {B : Item}
    (h : InTree ctx τ d B) : Proofs.CopyShape.Reach ctx τ d B := by
  obtain ⟨F, hF, hD⟩ := h
  exact reach_of_desc hD (Proofs.CopyShape.Reach.top hF)

end OmegaY.Official.Recon.LRC
