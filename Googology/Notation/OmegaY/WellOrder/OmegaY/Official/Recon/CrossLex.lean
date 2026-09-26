/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CrossLex.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.ChainSplit

set_option backward.do.legacy false

/-!
# The cross case of the chain condition without values

`CrossChainHolds` (`ChainSplit.lean`) asks, in a new column, when the candidate `q = Q u`
is not in the column of the stored parent `p = π(u⁺)`, for a chain of stored parents
from `q` to a node `c` with `π(c⁺) = p` and `v(u) ≤ v(c)`. The values of the output are
computed from the top of each column (`Expansion.finish`), so the value inequality is a
global statement. This file replaces it by a statement about stored parents and rows
only.

## The comparison `Lex`

Since `π(u⁺) = π(c⁺) = p`, `v(u) = v(u⁺) + v(p)` and `v(c) = v(c⁺) + v(p)`, so
`v(u) ≤ v(c)` is `v(u⁺) ≤ v(c⁺)`. The two nodes `u⁺` and `c⁺` have the same stored left
endpoint `p`; when they also have the same row, they have the same candidate `Q`
(`Q_congr`). If both columns are recognised above them (every stored parent is the
answer of the canonical search `P`), the canonical search compares their values:

* a larger value stops the search from the common candidate at or before a smaller one
  (`Hit.column_le_of_le`), so if the parent of `u⁺⁺` is left of the parent of `c⁺⁺`,
  then `v(u⁺) < v(c⁺)`;
* if the two parents are equal, the comparison moves one node up in both columns.

`Lex z w` is this comparison read on the stored parents only: `z` is a top, or the
parent of `z⁺` is left of the parent of `w⁺`, or the two parents are equal, `z⁺` and
`w⁺` have the same row, and `Lex z⁺ w⁺`. `Lex.value_le` proves `v(z) ≤ v(w)` from it.

## The reduction

`CrossLexHolds`: in a new column, when `Q u` is not in the column of `p = π(u⁺)`, there
is a chain of stored parents from `Q u` to a node `c` with `π(c⁺) = p`, `row c⁺ = row u⁺`
and `Lex u⁺ c⁺`. No value occurs in it.

`chainHolds_of_lex : ParentBelowHolds → CrossLexHolds → ChainHolds`, by induction over
the columns and, inside a column, from the top down: the nodes above `u⁺` and the
columns left of `u` are recognised by the induction hypothesis. Hence also
`crossChainHolds_of_lex : ParentBelowHolds → CrossLexHolds → CrossChainHolds`.

## Numerical check

`reference/official/cross-lex.cjs` checks `CrossLexHolds` (with the chain and `c` as
found in the output) on every new node, `n = 1, 2, 3`, with no failure:

| sample | expansions | cross nodes |
|---|---:|---:|
| standard S1–S3, S6 | 39090 | 110874 |
| legal, length ≤ 6, entries ≤ 6 | 23325 | 49368 |
| legal, length ≤ 5, entries ≤ 8 | 12285 | 28176 |
| random legal (`--random 20000,10,10,7`) | 37926 | 123066 |

`CrossLexTest.lean` checks it on the 474 fixtures with `#guard` (1062 cross nodes).
-/

namespace OmegaY.Official.Recon

open Canonical Expansion Geometry Frame

/-! ## Two searches from the same candidate -/

/-- A search with a smaller threshold stops at or after the stop of a search with a larger
threshold from the same candidate: its answer is not right of the other answer. -/
theorem Hit.column_le_of_le {F : Frame} (hF : F.Ordered) {big small : Nat} {s b : F.Node}
    (hb : Hit F small s b) (hle : small ≤ big) :
    ∀ {a : F.Node}, Hit F big s a → b.1.val ≤ a.1.val := by
  induction hb with
  | here hpos hsmall =>
    intro a ha
    cases ha with
    | here _ _ => exact le_rfl
    | next hrej _ _ => exact absurd ⟨hpos, lt_of_lt_of_le hsmall hle⟩ hrej
  | next hrej hQ rest ih =>
    intro a ha
    cases ha with
    | here _ _ => exact (rest.column_le hF).trans (Q_column_lt hF hQ).le
    | next _ hQ' rest' =>
      have he := Option.some.inj (hQ.symm.trans hQ')
      subst he
      exact ih rest'

/-- The candidate depends only on the stored left endpoint and the row. -/
theorem Q_congr {F : Frame} {z w : F.Node} (hl : (F.cell z).left = (F.cell w).left)
    (hh : F.height z = F.height w) : F.Q z = F.Q w := by
  unfold Q eligible
  rw [hl, hh]

/-! ## Recognised nodes -/

/-- A real node whose stored parent is the answer of the canonical search. -/
def Recognised (F : Frame) (a : F.Node) : Prop :=
  Real a → ∀ b, F.rawParent a = some b → F.P a = some b

/-- The value of the top of a column is `1`. -/
theorem value_top {R : Mountain} (hT : MountainTops R) {z : (Frame.ofMountain R).Node}
    (hz : (Frame.ofMountain R).upper z = none) : (Frame.ofMountain R).value z = 1 := by
  obtain ⟨cell, hback, hv⟩ := hT z.1.val z.1.isLt
  have hlast : z.2.val + 1 = R[z.1.val].size := by
    unfold Frame.upper at hz
    split at hz
    · cases hz
    · rename_i h
      have := z.2.isLt
      change z.2.val < R[z.1.val].size at this
      change ¬ z.2.val + 1 < R[z.1.val].size at h
      omega
  rw [Array.back?_eq_getElem?] at hback
  have hidx : R[z.1.val].size - 1 = z.2.val := by omega
  have h2 : R[z.1.val][z.2.val]? = some cell := by rw [← hidx]; exact hback
  have : R[z.1.val][z.2.val] = cell := by
    have h3 := Array.getElem?_eq_getElem (xs := R[z.1.val]) z.2.isLt
    rw [h2] at h3
    exact (Option.some.inj h3).symm
  change R[z.1.val][z.2.val].value = 1
  rw [this, hv]

/-! ## The comparison -/

/-- The comparison of the columns above two nodes, read on stored parents and rows. -/
inductive Lex (F : Frame) : F.Node → F.Node → Prop
  | top {z w : F.Node} (hz : F.upper z = none) : Lex F z w
  | left {z w a b : F.Node} (ha : F.rawParent z = some a) (hb : F.rawParent w = some b)
      (hab : a.1.val < b.1.val) : Lex F z w
  | same {z w z' w' a : F.Node} (hz : F.upper z = some z') (hw : F.upper w = some w')
      (ha : F.rawParent z = some a) (hb : F.rawParent w = some a)
      (hh : F.height z' = F.height w') (rest : Lex F z' w') : Lex F z w

theorem real_of_upper {F : Frame} {z z' : F.Node} (h : F.upper z = some z') : Real z' := by
  obtain ⟨_, h2⟩ := upper_spec h
  unfold Real
  omega

theorem upper_left {F : Frame} {z z' a : F.Node} (hz : F.upper z = some z')
    (ha : F.rawParent z = some a) : (F.cell z').left = some (ref a) := by
  obtain ⟨up, hup, hl⟩ := rawParent_spec ha
  rw [hz] at hup
  obtain rfl := Option.some.inj hup
  exact hl

/-- **Values from the comparison.** If `z` and `w` are real, have the same candidate, and
every node at or above them in their columns is recognised, then `Lex z w` gives
`v(z) ≤ v(w)`. -/
theorem Lex.value_le {R : Mountain} (hV : MountainValid R) (hS : MountainSums R)
    (hT : MountainTops R) {z w : (Frame.ofMountain R).Node}
    (h : Lex (Frame.ofMountain R) z w) :
    Real z → Real w → (Frame.ofMountain R).Q z = (Frame.ofMountain R).Q w →
    (∀ z' : (Frame.ofMountain R).Node, z'.1 = z.1 → z.2.val ≤ z'.2.val →
      Recognised (Frame.ofMountain R) z') →
    (∀ w' : (Frame.ofMountain R).Node, w'.1 = w.1 → w.2.val ≤ w'.2.val →
      Recognised (Frame.ofMountain R) w') →
    (Frame.ofMountain R).value z ≤ (Frame.ofMountain R).value w := by
  have hF := hV.toOrdered
  induction h with
  | top hz =>
    intro _ hw _ _ _
    rw [value_top hT hz]
    exact hF.real_positive _ hw
  | @left z w a b ha hb hab =>
    intro hz hw hQ hrz hrw
    have hPa := hrz z rfl le_rfl hz a ha
    have hPb := hrw w rfl le_rfl hw b hb
    obtain ⟨q, hq, hita⟩ := (P_iff hF).mp hPa
    obtain ⟨q', hq', hitb⟩ := (P_iff hF).mp hPb
    rw [hQ, hq'] at hq
    obtain rfl := Option.some.inj hq
    by_contra hlt
    have hle : (Frame.ofMountain R).value w ≤ (Frame.ofMountain R).value z := by omega
    have := Hit.column_le_of_le hF hitb hle hita
    omega
  | @same z w z' w' a hz hw ha hb hh rest ih =>
    intro hzr hwr _ hrz hrw
    obtain ⟨a1, ha1, _, _, _, hvz, _⟩ := hS.rawParent_upper hV hzr hz
    obtain ⟨a2, ha2, _, _, _, hvw, _⟩ := hS.rawParent_upper hV hwr hw
    rw [ha] at ha1
    rw [hb] at ha2
    obtain rfl := Option.some.inj ha1
    obtain rfl := Option.some.inj ha2
    have hQ' : (Frame.ofMountain R).Q z' = (Frame.ofMountain R).Q w' :=
      Q_congr (by rw [upper_left hz ha, upper_left hw hb]) hh
    obtain ⟨hz1, hz2⟩ := upper_spec hz
    obtain ⟨hw1, hw2⟩ := upper_spec hw
    have := ih (real_of_upper hz) (real_of_upper hw) hQ'
      (fun y hy hyi => hrz y (hy.trans hz1) (by omega))
      (fun y hy hyi => hrw y (hy.trans hw1) (by omega))
    omega

/-! ## Chains of stored parents -/

theorem RawChain.column_le {F : Frame} (hF : F.Ordered) {a c : F.Node} (h : RawChain F a c) :
    c.1.val ≤ a.1.val := by
  induction h with
  | here _ => exact le_rfl
  | step hraw _ ih => exact ih.trans (rawParent_column_lt hF hraw).le

/-- A chain with values to a different node ends with a stored-parent step from a node of
value at least the threshold. -/
theorem ChainTo.last {F : Frame} {th : Nat} {a p : F.Node} (h : ChainTo F th a p) (hne : a ≠ p) :
    ∃ c, RawChain F a c ∧ F.rawParent c = some p ∧ th ≤ F.value c := by
  induction h with
  | here _ => exact absurd rfl hne
  | @step a b p hv hraw rest ih =>
    by_cases hbp : b = p
    · subst hbp
      exact ⟨a, .here a, hraw, hv⟩
    · obtain ⟨c, hc, hcp, hcv⟩ := ih hbp
      exact ⟨c, .step hraw hc, hcp, hcv⟩

/-! ## The statement without values -/

/-- **Open.** The cross case of the chain condition, on stored parents and rows only: in a
new column, when the candidate `Q u` is not in the column of the stored parent `p` of the
node `u⁺` above `u`, a chain of stored parents runs from `Q u` to a node `c` with
`π(c⁺) = p`, `row c⁺ = row u⁺`, and `Lex u⁺ c⁺`. -/
def CrossLexHolds : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ u p q : (Frame.ofMountain R).Node, s.length - 1 ≤ u.1.val → Real u →
      (Frame.ofMountain R).rawParent u = some p → (Frame.ofMountain R).Q u = some q →
      q.1 ≠ p.1 →
      ∃ c up cp, RawChain (Frame.ofMountain R) q c ∧
        (Frame.ofMountain R).rawParent c = some p ∧
        (Frame.ofMountain R).upper u = some up ∧ (Frame.ofMountain R).upper c = some cp ∧
        (Frame.ofMountain R).height up = (Frame.ofMountain R).height cp ∧
        Lex (Frame.ofMountain R) up cp

/-! ## The induction -/

/-- The chain condition at a new node, from the recognition of the nodes before it. -/
theorem chainOK_step (hPB : ParentBelowHolds) (hL : CrossLexHolds) {s : List Nat} {n : Nat}
    {R : Mountain} (hrun : Official.expandDiagram s n = .ok R) (hB : Basic R)
    {u p : (Frame.ofMountain R).Node} (hx : s.length - 1 ≤ u.1.val) (hu : Real u)
    (hraw : (Frame.ofMountain R).rawParent u = some p)
    (hleft : ∀ a : (Frame.ofMountain R).Node, a.1.val < u.1.val →
      Recognised (Frame.ofMountain R) a)
    (habove : ∀ a : (Frame.ofMountain R).Node, a.1 = u.1 → u.2.val < a.2.val →
      Recognised (Frame.ofMountain R) a) :
    ChainOK (Frame.ofMountain R) u p := by
  have hF := hB.valid.toOrdered
  obtain ⟨q, hq⟩ := Q_exists_new hrun hx hu
  by_cases hcol : q.1 = p.1
  · obtain ⟨up, hUp, hmax⟩ := rawParent_max hrun hx hu hraw
    have hlt : (Frame.ofMountain R).height u < (Frame.ofMountain R).height up := by
      obtain ⟨hc1, hc2⟩ := upper_spec hUp
      obtain ⟨uc, ui⟩ := u
      obtain ⟨vc, vi⟩ := up
      simp only at hc1 hc2
      subst hc1
      exact hF.rows_strict _ (show ui < vi by change ui.val < vi.val; omega)
    have he := Q_eq_of_same_column hF hq hcol (hPB s n R hrun u p hx hu hraw)
      (fun z hz hzu => hmax z hz (lt_of_le_of_lt hzu hlt))
    subst he
    exact ⟨q, hq, .here q⟩
  · obtain ⟨c, up, cp, hc, hcp, hup, hcpu, hh, hlex⟩ := hL s n R hrun u p q hx hu hraw hq hcol
    have hqr := Q_real hF hu hq
    have hcr := (hc.value_le hB.valid hB.sums hqr).1
    have hcu : c.1.val < u.1.val :=
      lt_of_le_of_lt (hc.column_le hF) (Q_column_lt hF hq)
    obtain ⟨p1, hp1, _, _, _, hvu, _⟩ := hB.sums.rawParent_upper hB.valid hu hup
    obtain ⟨p2, hp2, _, _, _, hvc, _⟩ := hB.sums.rawParent_upper hB.valid hcr hcpu
    rw [hraw] at hp1
    rw [hcp] at hp2
    obtain rfl := Option.some.inj hp1
    obtain rfl := Option.some.inj hp2
    have hQ : (Frame.ofMountain R).Q up = (Frame.ofMountain R).Q cp :=
      Q_congr (by rw [upper_left hup hraw, upper_left hcpu hcp]) hh
    obtain ⟨hu1, hu2⟩ := upper_spec hup
    obtain ⟨hc1, hc2⟩ := upper_spec hcpu
    have hle := hlex.value_le hB.valid hB.sums hB.tops (real_of_upper hup)
      (real_of_upper hcpu) hQ
      (fun z hz hzi => habove z (hz.trans hu1) (by omega))
      (fun w hw _ => hleft w (by rw [hw, hc1]; exact hcu))
    refine chainOK_of_rawChain hB.valid hB.sums hu hq hc hcp ?_
    omega

/-- **The chain condition from `ParentBelowHolds` and `CrossLexHolds`.** -/
theorem chainHolds_of_lex (hPB : ParentBelowHolds) (hL : CrossLexHolds) : ChainHolds := by
  intro s n R hrun
  obtain ⟨M, hM, hMs, hI, hB⟩ := run_basic hrun
  have hF := hB.valid.toOrdered
  -- recognition of every node, by induction over the columns and from the top down
  have hrec : ∀ (col : Nat) (a : (Frame.ofMountain R).Node), a.1.val = col →
      Recognised (Frame.ofMountain R) a := by
    intro col
    induction col using Nat.strongRecOn with
    | ind col ihc =>
      have hleft : ∀ a : (Frame.ofMountain R).Node, a.1.val < col →
          Recognised (Frame.ofMountain R) a := fun a ha => ihc a.1.val ha a rfl
      by_cases hcx : col < s.length - 1
      · intro a ha hreal b hb
        have hG := prefix_geometry hM hI a.1.val a.1.isLt (by omega)
        exact P_of_columnGeometry hB.valid hG hreal hb
      · -- inside the column, from the top down
        have key : ∀ (k : Nat) (a : (Frame.ofMountain R).Node), a.1.val = col →
            (Frame.ofMountain R).length a.1 - a.2.val = k → Recognised (Frame.ofMountain R) a := by
          intro k
          induction k using Nat.strongRecOn with
          | ind k ihk =>
            intro a ha hk hreal b hb
            have hchain : ChainOK (Frame.ofMountain R) a b := by
              refine chainOK_step hPB hL hrun hB (by omega) hreal hb
                (fun a' ha' => hleft a' (by omega)) ?_
              intro a' ha' hi
              obtain ⟨ac, ai⟩ := a'
              simp only at ha' hi
              subst ha'
              refine ihk _ ?_ ⟨a.1, ai⟩ ha rfl
              show (Frame.ofMountain R).length a.1 - ai.val < k
              have h1 := ai.isLt
              have h2 := a.2.isLt
              omega
            obtain ⟨up, hUp, _⟩ := rawParent_spec hb
            obtain ⟨b', hb', _, hpos, hlt, _, _⟩ := hB.sums.rawParent_upper hB.valid hreal hUp
            rw [hb] at hb'
            obtain rfl := Option.some.inj hb'
            refine P_of_chain hF ?_ hchain ⟨hpos, hlt⟩
            intro a' b'' ha' hr' hraw'
            exact hleft a' (by omega) hr' b'' hraw'
        exact fun a ha => key _ a ha rfl
  intro u p hx hu hraw
  exact chainOK_step hPB hL hrun hB hx hu hraw
    (fun a _ => hrec a.1.val a rfl) (fun a _ _ => hrec a.1.val a rfl)

/-- **`CrossChainHolds` from `ParentBelowHolds` and `CrossLexHolds`.** -/
theorem crossChainHolds_of_lex (hPB : ParentBelowHolds) (hL : CrossLexHolds) :
    CrossChainHolds := by
  intro s n R hrun u p q hx hu hraw hq hcol
  obtain ⟨q', hq', hchain⟩ := chainHolds_of_lex hPB hL s n R hrun u p hx hu hraw
  rw [hq] at hq'
  obtain rfl := Option.some.inj hq'
  exact hchain.last (fun h => hcol (by rw [h]))

end OmegaY.Official.Recon

#print axioms OmegaY.Official.Recon.chainHolds_of_lex
#print axioms OmegaY.Official.Recon.crossChainHolds_of_lex
