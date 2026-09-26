/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/StepInnerCleanParent.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StepInnerCleanNext
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrCutLeg

set_option backward.do.legacy false

/-!
# `CleanParent` (`ChainCorrStepInner.lean`)

`ChainCorr.Inner.CleanParent`: for a clean copy (`b = 0`) in block `i ≥ 1` of the node
`a = (y, C)` of `M(s)` and a step `a → m'` of the scale-`k` chain of `M(s)`
(`m' = π(a⁺)`), `m'` is on the generation chain `a → g₁ → g₂ → …` of `a` in the row `C`
(`GenStep`: the next node is the node of the leg column at the row `C`), or the chain reaches
`g = (c_r, C)` and `a → m'` is the step `g → m'`.

## The proof

The parent search of the canonical mountain (Phyrion's `Frame.P`, the first node with a smaller
value along the candidate steps `Frame.Q`) starting from `a` follows the generation chain as
long as the leg column has a node on the row `C`: a candidate step at an equal row is a
`GenStep` (`genStep_of_Q`, `Q_of_genStep`).

The row `C` of a clean copy is the row of a node of the root column (`RootAsc`, carried by the
items like `ChainCorr.AscClean`), and it passed the ascension test: the in-row parents
(`P` at the same row) from the node `(y, Z)` at the reference row `Z` reach the column `c_r`
exactly.

* `C₀ = 0` (`Z = C`): the in-row parent of `a` is `π(a⁺)` itself, at the row `C` and at or
  right of `c_r`; a search that ends on the row of its start stays on that row, so it walks the
  generation chain (`inrow_chain`). The step lands on the chain.
* `C₀ > 0` (`Z = C - 1`): the node above each node `(c, Z)` of the in-row chain is `(c, C)`
  (row law `B(Z, Z) = Z + 1`), and its leg is the next node of the in-row chain. So the
  generation chain of `a` reaches `g = (c_r, C)` (`chain_to_root`). The search from `a` either
  stops on the chain (`walk`), or it passes `g` with `v(g) ≥ v(a)` and continues as the
  search from `g` with the smaller threshold `v(a)`. It then stops at `π(g⁺)` exactly when
  `v(π(g⁺)) < v(a)` (Phyrion's `Hit.loosen`): this value condition is the open statement
  `ViaRoot`.

## Result

* **`cleanParent_of_viaRoot : ViaRoot → CleanParent`** (proved).
* `ViaRoot` (open): for a clean copy (`b = 0`) of `a` whose generation chain reaches
  `g = (c_r, C)`: if `v(g) ≥ v(a)`, then `v(π(g⁺)) < v(a)`.

Numerical check (`reference/official/step-inner-viaroot.cjs`): the premise `v(g) ≥ v(a)` is rare.
Standard S1–S3, S6, legal `≤ 6, ≤ 6` and legal `≤ 5, ≤ 8`: no case (always `v(g) < v(a)`, 122784
clean copies). Random `20000,10,10,s` for `s = 7, 11, 13, 41, 43, 47`: 96 cases, all with
`C₀ > 0`, `v(g) = v(a)` and the search from `a` passing `g`; no failure. In every tested case
`v(g) ≤ v(a)` holds, which would give `ViaRoot` at once (then `v(g) = v(a)`, and the two searches
from the candidate of `g` have the same threshold).

All declarations are in the namespace `ChainCorr.Inner.Clean`.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.Inner.Clean

open Canonical Reserve Official Descent Classification Proofs
open Recon Recon.RowLaw

/-! ## The copied row is a row of the root column that passed its ascension test -/

/-- `C` passed the ascension test and is the row of a node of the root column. -/
def RootAsc (ctx : Context) (C : Row) : Prop :=
  ChainCorr.AscClean ctx C ∧ ∃ p ∈ realNodes ctx.source ctx.rootColumn, official p.2.row = C

/-- Every copied row of an item is a `RootAsc` row. -/
def ItemRootAsc (ctx : Context) (it : Item) : Prop := ∀ C, it.clean = some C → RootAsc ctx C

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
theorem childItems_rootAsc {ctx : Context} {d : Nat} {it : Item} {cs : List Item}
    (h : childItems ctx d it = .ok cs) (hit : ItemRootAsc ctx it) :
    ∀ c ∈ cs, ItemRootAsc ctx c := by
  unfold childItems at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  generalize hrhoEq : topIn ctx.source ctx.rootColumn d it.source = rho at h
  split at h
  · obtain rfl := Except.ok.inj h
    simp
  · split at h
    · cases h
    · rename_i v hv
      split at h
      · split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · obtain rfl := Except.ok.inj h
          intro c hc
          simp only [List.mem_map, List.mem_range] at hc
          obtain ⟨j, _, rfl⟩ := hc
          intro C' hC'
          simp at hC'
      · rename_i hasc
        have hvt : v = true := by simpa using hasc
        subst hvt
        have hsome : ∃ r cl, rho = some (r, cl) := by
          cases rho with
          | none => simp [ascends, pure, Except.pure] at hv
          | some p => exact ⟨p.1, p.2, rfl⟩
        obtain ⟨r, cl, rfl⟩ := hsome
        have hrho : RootAsc ctx (official cl.row) :=
          ⟨ChainCorr.ascClean_of_ascends hv, (r, cl), (topIn_spec hrhoEq).1, rfl⟩
        simp only at h
        split at h
        · rename_i hclean
          split at h
          · obtain rfl := Except.ok.inj h
            intro c hc
            simp only [List.mem_map, List.mem_range] at hc
            obtain ⟨j, _, rfl⟩ := hc
            (try split_ifs) <;> intro C' hC' <;>
              simp only [Option.some.injEq, reduceCtorEq] at hC' <;> (try subst hC') <;>
              first | exact hrho | exact hit _ hclean
          · obtain rfl := Except.ok.inj h
            intro c hc
            simp only [List.mem_map, List.mem_filter, List.mem_range] at hc
            obtain ⟨j, _, rfl⟩ := hc
            (try split_ifs) <;> intro C' hC' <;>
              simp only [Option.some.injEq, reduceCtorEq] at hC' <;> (try subst hC') <;>
              first | exact hrho | exact hit _ hclean
        · rename_i C hclean
          split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · split at h
            · cases h
            · split at h
              · simp [throw, throwThe, MonadExceptOf.throw] at h
              · obtain rfl := Except.ok.inj h
                intro c hc
                simp only [List.mem_map, List.mem_range] at hc
                obtain ⟨j, _, rfl⟩ := hc
                (try split_ifs) <;> intro C' hC' <;>
                  simp only [Option.some.injEq, reduceCtorEq] at hC' <;> (try subst hC') <;>
                  first | exact hrho | exact hit _ hclean

/-- The origin of a copy of the root row is the node `(x, C)` of a `RootAsc` row `C`. -/
def CleanRoot (ctx : Context) (p : EO) : Prop :=
  ∀ r b, p.2 = .clean r b → ∃ C cs, nodeAt ctx.source ctx.x C = some (r, cs) ∧ RootAsc ctx C

theorem levelOneT_cleanRoot {ctx : Context} {it : Item} (hit : ItemRootAsc ctx it)
    {ps : List EO} (h : levelOneT ctx it = .ok ps) : ∀ p ∈ ps, CleanRoot ctx p := by
  intro p hp r b hrb
  rcases levelOneT_out h with ⟨_, rfl⟩ | ⟨e, rfl, _, _, hk⟩
  · simp at hp
  · simp only [List.mem_singleton] at hp
    subst hp
    rcases hk with ⟨_, r', her⟩ | ⟨C, csRef, cs, hC, hcs, hec⟩
    · rw [her] at hrb; cases hrb
    · rw [hec] at hrb
      obtain ⟨rfl, _⟩ := Origin.clean.inj hrb
      exact ⟨C, cs, hcs, hit C hC⟩

theorem runItemT_cleanRoot (ctx : Context) :
    ∀ (d : Nat) (it : Item) (ps : List EO), ItemRootAsc ctx it →
      runItemT ctx d it = .ok ps → ∀ p ∈ ps, CleanRoot ctx p
  | 0, _, ps, _, h => by simp [runItemT, pure, Except.pure] at h; subst h; simp
  | 1, it, ps, hit, h => levelOneT_cleanRoot hit (by simpa [runItemT] using h)
  | d + 2, it, ps, hit, h => by
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i children hch
        split at h
        · cases h
        · rename_i outs houts
          cases h
          intro p hp
          obtain ⟨out, hout, hpo⟩ := List.mem_flatten.mp hp
          obtain ⟨c, hc, hco⟩ := mem_of_mapM houts hout
          exact runItemT_cleanRoot ctx (d + 1) c out (childItems_rootAsc hch hit c hc) hco p hpo

/-- **The origin of every copy of the root row is a node on a `RootAsc` row.** -/
theorem emitsT_cleanRoot {ctx : Context} {τ : Row} {es : List EO}
    (h : emitsT ctx τ = .ok es) : ∀ p ∈ es, CleanRoot ctx p := by
  unfold emitsT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i lower hlower
    split at h
    · cases h
    · rename_i upper hupper
      cases h
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · unfold lowerT at hlower
        simp only [bind, Except.bind, pure, Except.pure] at hlower
        split at hlower
        · cases hlower
        · rename_i outs houts
          cases hlower
          obtain ⟨out, hout, hpo⟩ := List.mem_flatten.mp hp
          obtain ⟨q, hq, hqo⟩ := mem_of_mapM houts hout
          refine runItemT_cleanRoot ctx q.1 q.2 out ?_ hqo p hpo
          obtain ⟨k, j, _, _, rfl⟩ := mem_lowerItems hq
          intro C hC
          simp at hC
      · unfold upperT at hupper
        obtain ⟨q, _, hqp⟩ := mem_of_mapM hupper hp
        simp only [bind, Except.bind, pure, Except.pure] at hqp
        split at hqp
        · cases hqp
        · cases hqp
          intro r b hrb
          cases hrb

/-! ## Raw parents, candidate steps and generation steps in the frame -/

section FrameBridge

open Geometry Geometry.Frame

variable {M : Mountain}

theorem P_of_rawParent (hN : (Frame.ofMountain M).Normal) {u : (Frame.ofMountain M).Node}
    (hu : Frame.Real u) {q : Ref} (h : Reserve.rawParent M (Frame.ref u) = some q) :
    ∃ p, (Frame.ofMountain M).P u = some p ∧ Frame.ref p = q := by
  have h1 := ControlProof.rawParent_ref (M := M) u
  rw [h] at h1
  cases hup : (Frame.ofMountain M).upper u with
  | none => rw [hup] at h1; cases h1
  | some v =>
    rw [hup, Option.bind_some] at h1
    obtain ⟨np, hlk, _, _⟩ := hN.toOrdered.stored_valid v q h1.symm
    have hnp : Frame.ref np = q := Frame.lookup_spec hlk
    have hleft : ((Frame.ofMountain M).cell v).left = some (Frame.ref np) := by
      rw [hnp]; exact h1.symm
    have hraw := Frame.rawParent_eq_of_upper_left hup hleft
    exact ⟨np, (hN.rawParent_eq_P hu).symm.trans hraw, hnp⟩

theorem rawParent_of_P (hN : (Frame.ofMountain M).Normal) {u p : (Frame.ofMountain M).Node}
    (hu : Frame.Real u) (hP : (Frame.ofMountain M).P u = some p) :
    Reserve.rawParent M (Frame.ref u) = some (Frame.ref p) := by
  obtain ⟨v, hv⟩ := hN.upper_of_parent hP
  obtain ⟨p', hp', _, _, hleft⟩ := hN.upper_step u v hu hv
  have : p' = p := Option.some.inj (hp'.symm.trans hP)
  subst this
  have h1 := ControlProof.rawParent_ref (M := M) u
  rw [hv, Option.bind_some, hleft] at h1
  exact h1

theorem genStep_of_Q (hO : (Frame.ofMountain M).Ordered) {cr : Nat}
    {u q : (Frame.ofMountain M).Node} (hu : Frame.Real u) (hQ : (Frame.ofMountain M).Q u = some q)
    (hh : (Frame.ofMountain M).height q = (Frame.ofMountain M).height u) (hc : cr < u.1.val) :
    GenStep M cr (Frame.ref u) (Frame.ref q) := by
  obtain ⟨left, hleft, _, _, hcol, _, _, _⟩ := Frame.Q_spec hO hQ
  have hq := Frame.Q_real hO hu hQ
  refine ⟨hc, hq, (Frame.ofMountain M).cell u, (Frame.ofMountain M).cell q, Frame.ref left,
    ControlProof.cell?_ref u, hleft, ?_, ControlProof.cell?_ref q, hh⟩
  show q.1.val = left.1.val
  rw [hcol]

theorem Q_of_genStep (hO : (Frame.ofMountain M).Ordered) {cr : Nat}
    {u : (Frame.ofMountain M).Node} {b : Ref} (h : GenStep M cr (Frame.ref u) b) :
    ∃ nb : (Frame.ofMountain M).Node, Frame.ref nb = b ∧ (Frame.ofMountain M).Q u = some nb ∧
      (Frame.ofMountain M).height nb = (Frame.ofMountain M).height u := by
  obtain ⟨_, _, ca, cb, l, hca, hl, hbl, hcb, hrow⟩ := h
  have hcu : (Frame.ofMountain M).cell u = ca :=
    Option.some.inj ((ControlProof.cell?_ref u).symm.trans hca)
  obtain ⟨left, hlk, _, hlh⟩ := hO.stored_valid u l (by rw [hcu]; exact hl)
  have hlref : Frame.ref left = l := Frame.lookup_spec hlk
  obtain ⟨nb, hnb, hcellb⟩ := ControlProof.node_of_cell? hcb
  have hhb : (Frame.ofMountain M).height nb = (Frame.ofMountain M).height u := by
    show ((Frame.ofMountain M).cell nb).row = ((Frame.ofMountain M).cell u).row
    rw [hcellb, hcu, hrow]
  refine ⟨nb, hnb, ?_, hhb⟩
  have hcol : nb.1 = left.1 := by
    apply Fin.ext
    have e1 : nb.1.val = b.column := by rw [← hnb]; rfl
    have e2 : left.1.val = l.column := by rw [← hlref]; rfl
    rw [e1, e2, hbl]
  have hleft : ((Frame.ofMountain M).cell u).left = some (Frame.ref left) := by
    rw [hcu, hlref]; exact hl
  obtain ⟨nc, ni⟩ := nb
  simp only at hcol
  subst hcol
  apply Frame.Q_eq_of_maximal hleft ni
  · rw [Frame.mem_eligible]
    refine ⟨?_, hhb.le⟩
    by_contra hn
    have hlt := hO.rows_strict left.1 (lt_of_not_ge hn)
    have : (Frame.ofMountain M).height ⟨left.1, ni⟩ < (Frame.ofMountain M).height left := hlt
    rw [hhb] at this
    exact absurd (lt_of_lt_of_le this hlh) (lt_irrefl _)
  · intro j hj
    have hjh := (Frame.mem_eligible.mp hj).2
    rw [← hhb] at hjh
    exact (hO.rows_strict left.1).le_iff_le.mp hjh

end FrameBridge

/-! ## Walking the generation chain -/

section Walk

open Geometry Geometry.Frame

variable {M : Mountain}

/-- A search that ends on the row of its start stays on that row: it walks the generation
chain. -/
theorem inrow_hit (hO : (Frame.ofMountain M).Ordered) {cr thr : Nat}
    {q p : (Frame.ofMountain M).Node} (hit : Hit (Frame.ofMountain M) thr q p) :
    ∀ u : (Frame.ofMountain M).Node, Frame.Real u → (Frame.ofMountain M).Q u = some q →
      (Frame.ofMountain M).height p = (Frame.ofMountain M).height u → cr ≤ p.1.val →
      Relation.TransGen (GenStep M cr) (Frame.ref u) (Frame.ref p) := by
  induction hit with
  | here _ _ =>
      intro u hu hQ hh hc
      exact .single (genStep_of_Q hO hu hQ hh (lt_of_le_of_lt hc (Q_column_lt hO hQ)))
  | @next q q' p _ hQ' rest ih =>
      intro u hu hQ hh hc
      have h1 := rest.height_le hO
      have h2 := Q_height_le hO hQ'
      have h3 := Q_height_le hO hQ
      have hqu : (Frame.ofMountain M).height q = (Frame.ofMountain M).height u :=
        le_antisymm h3 (hh ▸ h1.trans h2)
      have hcq : p.1.val ≤ q'.1.val := rest.column_le hO
      have hcq' := Q_column_lt hO hQ'
      have hcu := Q_column_lt hO hQ
      have hstep := genStep_of_Q (cr := cr) hO hu hQ hqu (by omega)
      have hq : Frame.Real q := Q_real hO hu hQ
      exact .head hstep (ih q hq hQ' (hh.trans hqu.symm) hc)

/-- **The walk.** A search from `x` with the threshold `thr` along the generation chain
`x →⁺ g` stops on the chain after `x`, or it rejects `g` and continues from the candidate
of `g`. -/
theorem walk (hO : (Frame.ofMountain M).Ordered) {cr thr : Nat} {x g : Ref}
    (hxg : Relation.TransGen (GenStep M cr) x g) :
    ∀ nx : (Frame.ofMountain M).Node, Frame.ref nx = x →
      ∀ q p, (Frame.ofMountain M).Q nx = some q → Hit (Frame.ofMountain M) thr q p →
      Relation.TransGen (GenStep M cr) x (Frame.ref p) ∨
        ∃ ng : (Frame.ofMountain M).Node, Frame.ref ng = g ∧
          ¬ (0 < (Frame.ofMountain M).value ng ∧ (Frame.ofMountain M).value ng < thr) ∧
          ∃ q', (Frame.ofMountain M).Q ng = some q' ∧ Hit (Frame.ofMountain M) thr q' p := by
  induction hxg using Relation.TransGen.head_induction_on with
  | single h =>
      intro nx hnx q p hQ hit
      subst hnx
      obtain ⟨nb, hnb, hQb, _⟩ := Q_of_genStep hO h
      have hqb : q = nb := Option.some.inj (hQ.symm.trans hQb)
      subst hqb
      cases hit with
      | here _ _ => exact Or.inl (.single (hnb ▸ h))
      | next hrej hQ' rest => exact Or.inr ⟨q, hnb, hrej, _, hQ', rest⟩
  | head h _ ih =>
      intro nx hnx q p hQ hit
      subst hnx
      obtain ⟨nb, hnb, hQb, _⟩ := Q_of_genStep hO h
      have hqb : q = nb := Option.some.inj (hQ.symm.trans hQb)
      subst hqb
      cases hit with
      | here _ _ => exact Or.inl (.single (hnb ▸ h))
      | next hrej hQ' rest =>
          rcases ih q hnb _ p hQ' rest with h' | h'
          · exact Or.inl (.head h h')
          · exact Or.inr h'

/-- The generation chain stays on its row. -/
theorem chain_row {cr : Nat} {a g : Ref} (h : Relation.TransGen (GenStep M cr) a g) :
    ∀ ca, cell? M a = some ca → ∃ cg, cell? M g = some cg ∧ cg.row = ca.row := by
  induction h with
  | single hab =>
      intro ca hca
      obtain ⟨_, _, ca', cb, _, hca', _, _, hcb, hrow⟩ := hab
      rw [hca] at hca'
      obtain rfl := Option.some.inj hca'
      exact ⟨cb, hcb, hrow⟩
  | tail _ hbc ih =>
      intro ca hca
      obtain ⟨cb, hcb, hrowb⟩ := ih ca hca
      obtain ⟨_, _, cb', cc, _, hcb', _, _, hcc, hrow⟩ := hbc
      rw [hcb] at hcb'
      obtain rfl := Option.some.inj hcb'
      exact ⟨cc, hcc, hrow.trans hrowb⟩

end Walk

/-! ## The generation chain of a row `C` with `C₀ > 0` reaches the root column -/

section Chain

open Geometry Geometry.Frame

variable {M : Mountain}

theorem official_inj' {a b : Row} (ha : (1 : Row) ≤ a) (hb : (1 : Row) ≤ b)
    (h : official a = official b) : a = b := by
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact absurd h (ne_of_lt (official_strictMono ha hlt))
  · exact heq
  · exact absurd h.symm (ne_of_lt (official_strictMono hb hgt))

theorem bump_le_B (a b : Row) : Row.bump a 0 ≤ Row.B a b :=
  Row.bump_mono_exponent a (Nat.zero_le _)

/-- A frame node of a real cell has row at least `1`. -/
theorem one_le_row_of_cell {s : List Nat} (hb : Canonical.build s = .ok M) {r : Ref} {c : Cell}
    (hc : cell? M r = some c) (hr : 1 ≤ r.index) : (1 : Row) ≤ c.row := by
  have hN := build_normal_of_success hb
  obtain ⟨u, hu, hcu⟩ := ControlProof.node_of_cell? hc
  have hreal : Frame.Real u := by
    show 0 < u.2.val
    have : u.2.val = r.index := by rw [← hu]; rfl
    omega
  have := Frame.one_le_height hN.toOrdered hreal
  rw [← hcu]
  exact this

/-- The row law at a real node of a canonical mountain whose upper node exists. -/
theorem upper_row {s : List Nat} (hb : Canonical.build s = .ok M) {r : Ref} {c cu : Cell}
    (hc : cell? M r = some c) (hr : 1 ≤ r.index) (hcu : cell? M (up r) = some cu) :
    ∃ q cq, cu.left = some q ∧ cell? M q = some cq ∧ cu.row = Row.B c.row cq.row ∧
      1 ≤ q.index ∧ q.column < r.column := by
  have hN := build_normal_of_success hb
  have hO := hN.toOrdered
  obtain ⟨u, hu, hcell⟩ := ControlProof.node_of_cell? hc
  obtain ⟨v, hv, hvcell⟩ := ControlProof.node_of_cell? hcu
  have hreal : Frame.Real u := by
    show 0 < u.2.val
    have : u.2.val = r.index := by rw [← hu]; rfl
    omega
  have hup : (Frame.ofMountain M).upper u = some v := by
    apply ControlProof.upper_eq_of_index
    · apply Fin.ext
      have e1 : v.1.val = (up r).column := by rw [← hv]; rfl
      have e2 : u.1.val = r.column := by rw [← hu]; rfl
      rw [e1, e2]; rfl
    · have e1 : v.2.val = (up r).index := by rw [← hv]; rfl
      have e2 : u.2.val = r.index := by rw [← hu]; rfl
      rw [e1, e2]; rfl
  obtain ⟨p, hP, hrow, _, hleft⟩ := hN.upper_step u v hreal hup
  have hpreal : Frame.Real p :=
    Frame.real_of_value_pos hO (Frame.P_value hO hP).1
  refine ⟨Frame.ref p, (Frame.ofMountain M).cell p, by rw [← hvcell]; exact hleft,
    ControlProof.cell?_ref p, ?_, hpreal, ?_⟩
  · have : cu.row = (Frame.ofMountain M).height v := by rw [← hvcell]; rfl
    rw [this, hrow, ← hcell]
    rfl
  · have := Frame.P_column_lt hO hP
    have e2 : u.1.val = r.column := by rw [← hu]; rfl
    show p.1.val < r.column
    omega

/-- **The generation chain of a row `C = Z + 1` reaches the root column.** If the in-row
parents from the node `r` on the row `Z` reach the column `cr` exactly, then the node above
`r` is on the row `C` and its generation chain in the row `C` reaches the column `cr`. -/
theorem chain_to_root {s : List Nat} (hb : Canonical.build s = .ok M) {cr : Nat} {Z C : Row}
    (hZC : Row.bump Z 0 = C) (hroot : ∃ p ∈ realNodes M cr, official p.2.row = C) :
    ∀ (f : Nat) (r : Ref) (cl : Cell), cell? M r = some cl → 1 ≤ r.index →
      official cl.row = Z → cr < r.column → reachesRoot M cr f r = .ok true →
      ∃ cu, cell? M (up r) = some cu ∧ official cu.row = C ∧
        ∃ g, Relation.TransGen (GenStep M cr) (up r) g ∧ g.column = cr := by
  have hV := build_valid_of_success hb
  intro f
  induction f with
  | zero =>
      intro r cl _ _ _ _ h
      simp [reachesRoot, throw, throwThe, MonadExceptOf.throw] at h
  | succ f ih =>
      intro r cl hcl hr1 hZ hcr h
      unfold reachesRoot at h
      rw [if_neg (by omega)] at h
      simp only [bind, Except.bind] at h
      cases hw : liftE (Expansion.weakParent M r) with
      | error e => rw [hw] at h; cases h
      | ok wp =>
        rw [hw] at h
        cases wp with
        | none => simp only [pure, Except.pure] at h; cases h
        | some q =>
          simp only at h
          have hqcr := ChainCorr.reachesRoot_column h
          obtain ⟨col, cell, upper, parentCell, hcol, hcell, hup, hleft, hpc, hprow⟩ :=
            Recon.RowLaw.weakParent_some (Reconstruction.liftE_ok hw)
          have hcellr : cell? M r = some cell := by simp [cell?, hcol, hcell]
          have hcc : cell = cl := Option.some.inj (hcellr.symm.trans hcl)
          subst hcc
          have hupr : cell? M (up r) = some upper := by simp [cell?, up, hcol, hup]
          have hqc : cell? M q = some parentCell := by
            obtain ⟨column, h1, h2⟩ := cellAt_ok_iff.mp hpc
            simp [cell?, h1, h2]
          obtain ⟨q', cq', hleft', hq', hrowu, hq1, _⟩ := upper_row hb hcellr hr1 hupr
          rw [hleft] at hleft'
          obtain rfl := Option.some.inj hleft'
          rw [hqc] at hq'
          obtain rfl := Option.some.inj hq'
          have hone := one_le_row_of_cell hb hcellr hr1
          have hurow : upper.row = Row.bump cell.row 0 := by rw [hrowu, hprow, Row.B_self]
          have hofu : official upper.row = C := by
            rw [hurow, official_bump hone, hZ, hZC]
          have hqZ : official parentCell.row = Z := by rw [hprow]; exact hZ
          refine ⟨upper, hupr, hofu, ?_⟩
          rcases Nat.lt_or_ge cr q.column with hlt | hge
          · -- the chain continues from `q`
            obtain ⟨cu', hcu', hofu', g, hg, hgc⟩ := ih q parentCell hqc hq1 hqZ hlt h
            have hrowq : cu'.row = upper.row :=
              official_inj' (one_le_row_of_cell hb hcu' (by simp [up]))
                (one_le_row_of_cell hb hupr (by simp [up])) (hofu'.trans hofu.symm)
            have hstep : GenStep M cr (up r) (up q) :=
              ⟨by simp only [up]; exact hcr, by simp [up], upper, cu', q, hupr, hleft,
                by simp [up], hcu', hrowq⟩
            exact ⟨g, .head hstep hg, hgc⟩
          · -- `q` is on the root column
            have hqcol : q.column = cr := by omega
            obtain ⟨p, hpmem, hprow'⟩ := hroot
            obtain ⟨hpc, hp1⟩ := realNodes_column hpmem
            have hqmem : (q, parentCell) ∈ realNodes M cr := by
              rw [mem_realNodes_iff]
              unfold cell? at hqc
              cases hcolq : M[q.column]? with
              | none => rw [hcolq] at hqc; cases hqc
              | some colq =>
                  rw [hcolq] at hqc
                  simp only [Option.bind_eq_bind, Option.bind_some] at hqc
                  refine ⟨colq, q.index - 1, by rw [← hqcol]; exact hcolq, ?_, ?_⟩
                  · rw [show q.index - 1 + 1 = q.index by omega]; exact hqc
                  · show q = ⟨cr, q.index - 1 + 1⟩
                    cases q
                    simp only at hqcol hq1 ⊢
                    subst hqcol
                    congr 1
                    omega
            -- `p` is above `q`
            have hpq : q.index < p.1.index := by
              by_contra hn
              have hle := realNodes_row_le hV hpmem hqmem (by simp only; omega)
              have := official_mono (realNodes_row_one_le hV hpmem) hle
              rw [hprow', hqZ, ← hZC] at this
              exact absurd this (not_le.mpr (Row.lt_bump _ _))
            -- the node above `q`
            obtain ⟨colp, kp, hcolp, hcellp, hp1'⟩ := mem_realNodes_iff.mp hpmem
            have hqcell : ∃ cq, cell? M (up q) = some cq := by
              have hks : kp + 1 < colp.size := (Array.getElem?_eq_some_iff.mp hcellp).1
              have hidx : p.1.index = kp + 1 := by rw [hp1']
              refine ⟨colp[q.index + 1]'(by omega), ?_⟩
              simp only [cell?, up, hqcol, hcolp, Option.bind_eq_bind, Option.bind_some]
              exact Array.getElem?_eq_getElem _
            obtain ⟨cq, hcq⟩ := hqcell
            obtain ⟨_, cpq, _, _, hrowq, _, _⟩ := upper_row hb hqc hq1 hcq
            have hlo : upper.row ≤ cq.row := by
              rw [hrowq, hurow, ← hprow]
              exact bump_le_B _ _
            have hhi : cq.row ≤ p.2.row := by
              have hcqmem : ((up q), cq) ∈ realNodes M cr := by
                rw [mem_realNodes_iff]
                refine ⟨colp, q.index, hcolp, ?_, ?_⟩
                · simp only [cell?, up, hqcol, hcolp, Option.bind_eq_bind, Option.bind_some] at hcq
                  exact hcq
                · simp [up, hqcol]
              exact realNodes_row_le hV hcqmem hpmem (by simp only [up]; omega)
            have hpu : p.2.row = upper.row :=
              official_inj' (realNodes_row_one_le hV hpmem) (one_le_row_of_cell hb hupr
                (by simp [up])) (hprow'.trans hofu.symm)
            have hrowq' : cq.row = upper.row := le_antisymm (hpu ▸ hhi) hlo
            have hstep : GenStep M cr (up r) (up q) :=
              ⟨by simp only [up]; exact hcr, by simp [up], upper, cq, q, hupr, hleft,
                by simp [up], hcq, hrowq'⟩
            exact ⟨up q, .single hstep, by simp [up, hqcol]⟩

end Chain

/-! ## `CleanParent` -/

/-- (open) **The value condition at the root column.** For a clean copy (`b = 0`) of a node
`a` with a node above it, whose generation chain reaches `g` in the root column: if
`v(g) ≥ v(a)`, then the raw parent of `g` has a value smaller than `v(a)`. -/
def ViaRoot : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), Setting s n D M out ρ R col t →
    ∀ i, 0 < i → i < n + 1 → ∀ v a,
      CopyAt M R n ρ.cr ρ.x0 (official t.row) i v (.clean a false) →
      (∃ m, rawParent M a = some m) →
      ∀ g, Relation.TransGen (GenStep M ρ.cr) a g → g.column = ρ.cr →
      ∀ (ca cg : Cell), cell? M a = some ca → cell? M g = some cg → ca.value ≤ cg.value →
      ∀ pg cpg, rawParent M g = some pg → cell? M pg = some cpg → cpg.value < ca.value

open Geometry Geometry.Frame in
/-- **`CleanParent` from `ViaRoot`.** -/
theorem cleanParent_of_viaRoot (hVR : ViaRoot) : CleanParent := by
  intro s n D M out ρ R col t hS i hi0 hi v a hva k m' hst
  have hva' := hva
  obtain ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, ho⟩ := hva'
  have hes' : emitsT (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i))
      (official t.row) = .ok es := by rw [← hvc]; exact hes
  obtain ⟨C, cs, hcs, ⟨ref, cl, hn, hr⟩, hroot⟩ :=
    emitsT_cleanRoot hes' es[j] (List.getElem_mem hj) a false ho
  simp only [ctxAt] at hcs hn hr hroot
  have hb := hS.splice.build
  have hN := build_normal_of_success hb
  have hO := hN.toOrdered
  obtain ⟨hac, ha1, hacell, harow⟩ := Classification.nodeAt_spec hcs
  simp only at hac ha1 hacell harow
  obtain ⟨na, hna, hnacell⟩ := ControlProof.node_of_cell? hacell
  have hareal : Frame.Real na := by
    show 0 < na.2.val
    have : na.2.val = a.index := by rw [← hna]; rfl
    omega
  have hst' := hst
  obtain ⟨hpar, cm, cm', hcm, hcm', hjk, hlt⟩ := hst'
  obtain ⟨nm', hPa, hnm'⟩ := P_of_rawParent hN hareal (hna ▸ hpar)
  obtain ⟨q0, hQ0, hit0⟩ := (P_iff hO).mp hPa
  by_cases h0 : 0 < C.coeff 0
  · -- `C₀ > 0`: the chain reaches the root column
    have hZC := Recon.RowLaw.referenceRow_bump h0
    obtain ⟨hrc, hr1, hrcell, hrrow⟩ := Classification.nodeAt_spec hn
    simp only at hrc hr1 hrcell hrrow
    obtain ⟨cu, hcu, hofu, g, hg, hgc⟩ :=
      chain_to_root hb hZC hroot (y + 1) ref cl hrcell hr1 hrrow (by rw [hrc]; exact hcy) hr
    -- the node above `ref` is `a`
    have hupa : up ref = a := by
      obtain ⟨hmem, _⟩ := Recon.RowLaw.nodeAt_spec hcs
      have hupmem : (up ref, cu) ∈ realNodes M y := by
        rw [mem_realNodes_iff]
        unfold cell? at hcu
        cases hcolr : M[ref.column]? with
        | none => simp [up, hcolr] at hcu
        | some colr =>
            simp only [up, hcolr, Option.bind_eq_bind, Option.bind_some] at hcu
            refine ⟨colr, ref.index, by rw [← hrc]; exact hcolr, hcu, ?_⟩
            simp [up, hrc]
      have := ChainCorr.realNodes_eq_of_official (build_valid_of_success hb) hupmem hmem
        (by simp only; rw [hofu, harow])
      exact congrArg Prod.fst this
    rw [hupa] at hg
    rcases walk hO hg na hna q0 nm' hQ0 hit0 with hon | ⟨ng, hng, hrej, q', hQ', hit'⟩
    · exact Or.inl (hnm' ▸ hon)
    · -- the search passes `g`: it stops at the raw parent of `g`
      right
      have hgreal : Frame.Real ng := by
        obtain ⟨_, hi1⟩ := transGen_head hg
        have hgi : ∀ {x z : Ref}, Relation.TransGen (GenStep M ρ.cr) x z → 1 ≤ z.index := by
          intro x z hxz
          induction hxz with
          | single h => exact h.2.1
          | tail _ h _ => exact h.2.1
        show 0 < ng.2.val
        have : ng.2.val = g.index := by rw [← hng]; rfl
        have := hgi hg
        omega
      have hvpos : 0 < (Frame.ofMountain M).value ng := hO.real_positive ng hgreal
      have hvge : (Frame.ofMountain M).value na ≤ (Frame.ofMountain M).value ng := by
        by_contra hn'
        exact hrej ⟨hvpos, lt_of_not_ge hn'⟩
      obtain ⟨va, hvaU⟩ := hN.upper_of_parent hPa
      have hva1 := hN.upper_nontrivial na va hareal hvaU
      obtain ⟨vg, hvg⟩ := hN.upper_exists ng hgreal (by omega)
      obtain ⟨pg, hPg, _, _, _⟩ := hN.upper_step ng vg hgreal hvg
      have hrawg := rawParent_of_P hN hgreal hPg
      rw [hng] at hrawg
      -- the value condition
      obtain ⟨cg, hcg, hcgrow⟩ := chain_row hg cs hacell
      have hcgF : (Frame.ofMountain M).cell ng = cg := by
        have := ControlProof.cell?_ref ng
        rw [hng, hcg] at this
        exact (Option.some.inj this).symm
      have hcsF : (Frame.ofMountain M).cell na = cs := hnacell
      have hlt' := hVR s n D M out ρ R col t hS i hi0 hi v a hva ⟨m', hpar⟩ g hg hgc cs cg hacell
        hcg (by rw [← hcsF, ← hcgF]; exact hvge) (Frame.ref pg) ((Frame.ofMountain M).cell pg)
        hrawg (ControlProof.cell?_ref pg)
      -- the search from the candidate of `g` with the threshold `v(a)` stops at `P(g)`
      obtain ⟨r0, hwide, htail⟩ := hit'.loosen hvge
      have hPg' : (Frame.ofMountain M).P ng = some r0 := (P_iff hO).mpr ⟨q', hQ', hwide⟩
      have hr0 : r0 = pg := Option.some.inj (hPg'.symm.trans hPg)
      subst hr0
      have hacc : 0 < (Frame.ofMountain M).value r0 ∧
          (Frame.ofMountain M).value r0 < (Frame.ofMountain M).value na := by
        refine ⟨(P_value hO hPg).1, ?_⟩
        show ((Frame.ofMountain M).cell r0).value < ((Frame.ofMountain M).cell na).value
        rw [hcsF]
        exact hlt'
      have hm : nm' = r0 := by
        cases htail with
        | here _ _ => rfl
        | next hrej' _ _ => exact absurd hacc hrej'
      subst hm
      refine ⟨g, hg, hgc, ?_, cg, cm', hcg, hcm', ?_, ?_⟩
      · rw [← hnm']; exact hrawg
      · have hcma : cm = cs := Option.some.inj (hcm.symm.trans hacell)
        subst hcma
        rw [hcgrow]
        exact hjk
      · have := P_column_lt hO hPg
        rw [← hnm']
        show nm'.1.val < g.column
        rw [← hng]
        exact this
  · -- `C₀ = 0`: the raw parent of `a` is its in-row parent, on the chain
    left
    have hZ : referenceRow C = C := by
      unfold referenceRow
      rw [if_neg h0]
    rw [hZ, hcs] at hn
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
    obtain ⟨q, hw, hqcr⟩ := ChainCorr.weakParent_of_reachesRoot (by rw [hac]; exact hcy) hr
    obtain ⟨col', cell, upper, parentCell, hcol, hcell, hup, hleft, hpc, hprow⟩ :=
      Recon.RowLaw.weakParent_some hw
    have hraw : Reserve.rawParent M a = some q := by
      simp only [Reserve.rawParent, hcol, Option.bind_eq_bind, Option.bind_some, hup, hleft]
    have hqm : q = m' := Option.some.inj (hraw.symm.trans hpar)
    subst hqm
    have hcellr : cell? M a = some cell := by simp [cell?, hcol, hcell]
    have hcc : cell = cs := Option.some.inj (hcellr.symm.trans hacell)
    subst hcc
    have hqc : cell? M q = some parentCell := by
      obtain ⟨column, h1, h2⟩ := cellAt_ok_iff.mp hpc
      simp [cell?, h1, h2]
    have hnm'cell : (Frame.ofMountain M).cell nm' = parentCell := by
      have := ControlProof.cell?_ref nm'
      rw [hnm', hqc] at this
      exact (Option.some.inj this).symm
    have hh : (Frame.ofMountain M).height nm' = (Frame.ofMountain M).height na := by
      show ((Frame.ofMountain M).cell nm').row = ((Frame.ofMountain M).cell na).row
      rw [hnm'cell, hnacell, hprow]
    have hc : ρ.cr ≤ nm'.1.val := by
      have : nm'.1.val = q.column := by rw [← hnm']; rfl
      omega
    have := inrow_hit (cr := ρ.cr) hO hit0 na hareal hQ0 hh hc
    rw [hna, hnm'] at this
    exact this

#print axioms cleanParent_of_viaRoot

end OmegaY.Official.Classification.Proofs.ChainCorr.Inner.Clean
