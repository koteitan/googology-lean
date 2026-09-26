/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CrossUpperNormal.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossLex
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.CanonicalFrontier

set_option backward.do.legacy false

/-!
# The cross case of `Lex` in a normal frame

In a normal frame (a canonical mountain, `Frame.Normal`) the stored parent of every real
node is the answer of the canonical search `P`. This file proves the statement of
`CrossLexHolds` for every node of a normal frame (`normal_crossLex`):

  if `u` is real, `u⁺` is the node above `u`, `p = π(u⁺)` and `q = Q u ≠ p`, then the
  stored parents from `q` reach a node `c` with `π(c⁺) = p`, `row c⁺ = row u⁺`,
  `Lex u⁺ c⁺` and `v(u) ≤ v(c)`.

It is used for the source mountain `M(s)` in `CrossUpper.lean`.

## The rows

Let `q₀ = u, q₁ = Q u, q₂ = Q q₁, …` be the search of `P u`; it stops at `p`. For every
node `z ≠ p` of this search, `row u < B(row z, row p)` (`inv_step`, by induction along
the search). Assume it for `y` and let `z = Q y ≠ p`. Then `v(z) ≥ v(u) > 1`, so `z` has
an upper node `z⁺` with `row z⁺ = B(row z, row P z)`, and `P z` is on the search between
`z` and `p`, so `row z⁺ ≤ B(row z, row p)`. If `B(row z, row p) ≤ row u < B(row y, row p)`,
then `B(row z, row p) ≤ row y` (`B_le_of_lt`), so `row z⁺ ≤ row y`, against the
maximality of `z = Q y`. For the last node `c` before `p` on the chain of stored parents
(which runs inside the search), `B(row c, row p) = B(row u, row p)` then follows from
`Row.B_eq_of_between`.

## `Lex`

`normal_lex_of_value`: if `z`, `w` are real, have the same stored left endpoint and row,
and `v(z) ≤ v(w)`, then `Lex z w`. The two searches start at the same candidate; the one
with the smaller threshold stops at or before the other one (`Hit.column_le_of_le`); if
they stop at the same column they stop at the same node and the comparison moves up.
-/

namespace OmegaY.Official.Recon.CrossUpper

open Canonical Geometry Frame

/-! ## Searches -/

theorem Hit.unique {F : Frame} {th : Nat} {s a b : F.Node} (ha : Hit F th s a)
    (hb : Hit F th s b) : a = b := by
  induction ha generalizing b with
  | here hpos hsmall =>
    cases hb with
    | here _ _ => rfl
    | next hrej _ _ => exact absurd ⟨hpos, hsmall⟩ hrej
  | next hrej hQ rest ih =>
    cases hb with
    | here hpos hsmall => exact absurd ⟨hpos, hsmall⟩ hrej
    | next _ hQ' rest' =>
      have he := Option.some.inj (hQ.symm.trans hQ')
      subst he
      exact ih rest'

theorem Hit.eq_of_column {F : Frame} (hF : F.Ordered) {th : Nat} {x y : F.Node}
    (h : Hit F th x y) (hc : x.1.val = y.1.val) : x = y := by
  cases h with
  | here _ _ => rfl
  | next _ hQ rest =>
    have h1 := rest.column_le hF
    have h2 := Q_column_lt hF hQ
    omega

theorem Hit.same_of_column {F : Frame} (hF : F.Ordered) {small big : Nat} {s a b : F.Node}
    (ha : Hit F big s a) (hb : Hit F small s b) (hle : small ≤ big)
    (hc : a.1.val = b.1.val) : a = b := by
  obtain ⟨r, hr, hrb⟩ := hb.loosen hle
  have := Hit.unique ha hr
  subst this
  exact Hit.eq_of_column hF hrb hc

/-- Candidate steps. -/
inductive QReach (F : Frame) : F.Node → F.Node → Prop
  | refl (a : F.Node) : QReach F a a
  | cons {a b c : F.Node} (hq : F.Q a = some b) (rest : QReach F b c) : QReach F a c

theorem QReach.trans {F : Frame} {a b c : F.Node} (h1 : QReach F a b) (h2 : QReach F b c) :
    QReach F a c := by
  induction h1 with
  | refl _ => exact h2
  | cons hq _ ih => exact .cons hq (ih h2)

theorem QReach.height_le {F : Frame} (hF : F.Ordered) {a b : F.Node} (h : QReach F a b) :
    F.height b ≤ F.height a := by
  induction h with
  | refl _ => exact le_rfl
  | cons hq _ ih => exact ih.trans (Q_height_le hF hq)

theorem QReach.column_le {F : Frame} (hF : F.Ordered) {a b : F.Node} (h : QReach F a b) :
    b.1.val ≤ a.1.val := by
  induction h with
  | refl _ => exact le_rfl
  | cons hq _ ih => exact ih.trans (Q_column_lt hF hq).le

theorem QReach.eq_of_column {F : Frame} (hF : F.Ordered) {a b : F.Node} (h : QReach F a b)
    (hc : a.1.val = b.1.val) : a = b := by
  cases h with
  | refl _ => rfl
  | cons hq rest =>
    have h1 := rest.column_le hF
    have h2 := Q_column_lt hF hq
    omega

theorem Hit.qreach {F : Frame} {th : Nat} {s p : F.Node} (h : Hit F th s p) : QReach F s p := by
  induction h with
  | here _ _ => exact .refl _
  | next _ hQ _ ih => exact .cons hQ ih

theorem ParentPath.qreach {F : Frame} (hF : F.Ordered) {a c : F.Node} (h : ParentPath F a c) :
    QReach F a c := by
  induction h with
  | refl _ => exact .refl _
  | cons hp _ ih =>
    obtain ⟨q, hq, hit⟩ := (P_iff hF).mp hp
    exact (QReach.cons hq (Hit.qreach hit)).trans ih

/-- A node reached by candidate steps from a node of a search is in that search, or after
its end. -/
theorem Hit.or_reach {F : Frame} {th : Nat} {a p z : F.Node} (hh : Hit F th a p)
    (hr : QReach F a z) : Hit F th z p ∨ QReach F p z := by
  induction hr generalizing p with
  | refl _ => exact Or.inl hh
  | @cons a b z hq rest ih =>
    cases hh with
    | here _ _ => exact Or.inr (.cons hq rest)
    | next _ hQ hit =>
      have he := Option.some.inj (hq.symm.trans hQ)
      subst he
      exact ih hit

/-- The last step of a path of numerical parents. -/
theorem ParentPath.last {F : Frame} {a p : F.Node} (h : ParentPath F a p) (hne : a ≠ p) :
    ∃ c, ParentPath F a c ∧ F.P c = some p := by
  induction h with
  | refl _ => exact absurd rfl hne
  | @cons a b p hab rest ih =>
    by_cases hbp : b = p
    · subst hbp
      exact ⟨a, .refl a, hab⟩
    · obtain ⟨c, hc, hcp⟩ := ih hbp
      exact ⟨c, .cons hab hc, hcp⟩

theorem ParentPath.real {F : Frame} (hF : F.Ordered) {a c : F.Node} (h : ParentPath F a c)
    (ha : Real a) : Real c := by
  induction h with
  | refl _ => exact ha
  | cons hp _ ih => exact ih (real_of_value_pos hF (P_value hF hp).1)

/-- In a normal frame a path of numerical parents is a chain of stored parents. -/
theorem ParentPath.rawChain {F : Frame} (hF : F.Normal) {a c : F.Node} (h : ParentPath F a c)
    (ha : Real a) : RawChain F a c := by
  induction h with
  | refl _ => exact .here _
  | cons hp _ ih =>
    have hb := real_of_value_pos hF.toOrdered (P_value hF.toOrdered hp).1
    exact .step ((hF.rawParent_eq_P ha).trans hp) (ih hb)

theorem QReach.real {F : Frame} (hF : F.Ordered) {a b : F.Node} (h : QReach F a b)
    (ha : Real a) : Real b := by
  induction h with
  | refl _ => exact ha
  | cons hq _ ih => exact ih (Q_real hF ha hq)

/-! ## Rows -/

/-- If `p ≤ z ≤ y` and `B(z, p) < B(y, p)`, then `B(z, p) ≤ y`. -/
theorem B_le_of_lt {z y p : Row} (hpz : p ≤ z) (hzy : z ≤ y) (h : Row.B z p < Row.B y p) :
    Row.B z p ≤ y := by
  unfold Row.B at h ⊢
  have hjm : Row.jump y p = max (Row.jump y z) (Row.jump z p) := by
    rw [Row.jump_comm y p, Row.jump_max hpz hzy, Row.jump_comm p z, Row.jump_comm z y,
      max_comm]
  by_cases hj : Row.jump y z ≤ Row.jump z p
  · exfalso
    rw [hjm, max_eq_right hj, Row.bump_eq_of_jump_le hj] at h
    exact lt_irrefl _ h
  · have hne : z ≠ y := by
      intro he
      subst he
      simp at hj
    have hzy' : z < y := lt_of_le_of_ne hzy hne
    have h1 := Row.bump_last_le hzy'
    have h2 : Row.jump z p ≤ Row.jump z y - 1 := by
      rw [Row.jump_comm z y]
      omega
    exact (Row.bump_mono_exponent z h2).trans h1

/-- **One step of the search.** -/
theorem inv_step {F : Frame} (hF : F.Normal) {u p y z : F.Node} (hv : 1 < F.value u)
    (hy : Real y) (hinv : F.height u < Row.B (F.height y) (F.height p))
    (hq : F.Q y = some z) (hz : Hit F (F.value u) z p) (hzp : z ≠ p) :
    F.height u < Row.B (F.height z) (F.height p) := by
  have hO := hF.toOrdered
  have hzr : Real z := Q_real hO hy hq
  cases hz with
  | here _ _ => exact absurd rfl hzp
  | @next _ z' _ hrej hQz rest =>
    have hvz : F.value u ≤ F.value z := by
      by_contra hn
      exact hrej ⟨hO.real_positive z hzr, by omega⟩
    obtain ⟨zp, hzup⟩ := hF.upper_exists z hzr (by omega)
    obtain ⟨r, hPz, hrow, _, _⟩ := hF.upper_step z zp hzr hzup
    obtain ⟨q1, hq1, hit⟩ := (P_iff hO).mp hPz
    have he := Option.some.inj (hq1.symm.trans hQz)
    subst he
    obtain ⟨r', hr', hr'p⟩ := rest.loosen hvz
    have := Hit.unique hit hr'
    subst this
    have hpr : F.height p ≤ F.height r := hr'p.height_le hO
    have hrz : F.height r ≤ F.height z := (hit.height_le hO).trans (Q_height_le hO hQz)
    have hpz : F.height p ≤ F.height z := hpr.trans hrz
    have hzy : F.height z ≤ F.height y := Q_height_le hO hq
    by_contra hcon
    have hcon' : Row.B (F.height z) (F.height p) ≤ F.height u := le_of_not_gt hcon
    have h1 : Row.B (F.height z) (F.height r) ≤ Row.B (F.height z) (F.height p) := by
      rw [Row.B_max hrz hpr]
      exact le_max_left _ _
    have h3 := B_le_of_lt hpz hzy (lt_of_le_of_lt hcon' hinv)
    have h4 := Q_upper_gt hO hq hzup
    rw [hrow] at h4
    exact absurd (lt_of_lt_of_le h4 (h1.trans h3)) (lt_irrefl _)

/-- **Along the search.** -/
theorem inv_reach {F : Frame} (hF : F.Normal) {u p : F.Node} (hv : 1 < F.value u) :
    ∀ {y z : F.Node}, QReach F y z → Real y → Hit F (F.value u) y p →
      F.height u < Row.B (F.height y) (F.height p) → Hit F (F.value u) z p → z ≠ p →
      F.height u < Row.B (F.height z) (F.height p) := by
  intro y z hr
  induction hr with
  | refl _ => intro _ _ h _ _; exact h
  | @cons y b z hq rest ih =>
    intro hy hyp hinv hz hzp
    have hO := hF.toOrdered
    cases hyp with
    | here _ _ =>
      exfalso
      have h1 := rest.column_le hO
      have h2 := Q_column_lt hO hq
      have h3 := hz.column_le hO
      omega
    | @next _ b' _ _ hQ hb =>
      have he := Option.some.inj (hq.symm.trans hQ)
      subst he
      have hbp : b ≠ p := by
        intro hbp
        subst hbp
        have h1 := rest.column_le hO
        have h3 := hz.column_le hO
        exact hzp (rest.eq_of_column hO (by omega)).symm
      exact ih (Q_real hO hy hq) hb (inv_step hF hv hy hinv hq hb hbp) hz hzp

/-! ## `Lex` from values -/

/-- **`Lex` in a normal frame from the values.** -/
theorem normal_lex_of_value {F : Frame} (hF : F.Normal) :
    ∀ (k : Nat) (z w : F.Node), F.length z.1 - z.2.val = k → Real z → Real w →
      (F.cell z).left = (F.cell w).left → F.height z = F.height w →
      F.value z ≤ F.value w → Lex F z w := by
  intro k
  induction k with
  | zero =>
    intro z w hk _ _ _ _ _
    have := z.2.isLt
    omega
  | succ k ih =>
    intro z w hk hz hw hl hh hvle
    have hO := hF.toOrdered
    cases hzu : F.upper z with
    | none => exact .top hzu
    | some z1 =>
      have hvz := hF.upper_nontrivial z z1 hz hzu
      obtain ⟨w1, hwu⟩ := hF.upper_exists w hw (by omega)
      obtain ⟨a, hPa, hra, hva, hla⟩ := hF.upper_step z z1 hz hzu
      obtain ⟨b, hPb, hrb, hvb, hlb⟩ := hF.upper_step w w1 hw hwu
      have hQ : F.Q z = F.Q w := Q_congr hl hh
      obtain ⟨s, hs, hita⟩ := (P_iff hO).mp hPa
      obtain ⟨s', hs', hitb⟩ := (P_iff hO).mp hPb
      rw [hQ, hs'] at hs
      have he := Option.some.inj hs
      subst he
      have hab : a.1.val ≤ b.1.val := Hit.column_le_of_le hO hita hvle hitb
      have hraw_a : F.rawParent z = some a := (hF.rawParent_eq_P hz).trans hPa
      have hraw_b : F.rawParent w = some b := (hF.rawParent_eq_P hw).trans hPb
      rcases lt_or_eq_of_le hab with hlt | heq
      · exact .left hraw_a hraw_b hlt
      · have hba : b = a := Hit.same_of_column hO hitb hita hvle heq.symm
        subst hba
        have hpv := P_value hO hPa
        refine .same hzu hwu hraw_a hraw_b (by rw [hra, hrb, hh]) ?_
        obtain ⟨hz1c, hz1i⟩ := upper_spec hzu
        refine ih z1 w1 ?_ (real_of_upper hzu) (real_of_upper hwu) (by rw [hla, hlb]) (by
          rw [hra, hrb, hh]) (by rw [hva, hvb]; omega)
        obtain ⟨c1, i1⟩ := z1
        simp only at hz1c hz1i
        subst hz1c
        show F.length z.1 - i1.val = k
        omega

/-! ## The cross case -/

/-- **`CrossLexHolds` in a normal frame.** -/
theorem normal_crossLex {F : Frame} (hF : F.Normal) {u up p q : F.Node} (hu : Real u)
    (hup : F.upper u = some up) (hraw : F.rawParent u = some p) (hq : F.Q u = some q)
    (hne : q ≠ p) :
    ∃ c cp, RawChain F q c ∧ F.rawParent c = some p ∧ F.upper c = some cp ∧
      F.height up = F.height cp ∧ Lex F up cp ∧ F.value u ≤ F.value c := by
  have hO := hF.toOrdered
  have hPu : F.P u = some p := (hF.rawParent_eq_P hu).symm.trans hraw
  have hv := hF.upper_nontrivial u up hu hup
  obtain ⟨q', hq', trace⟩ := (P_iff hO).mp hPu
  rw [hq] at hq'
  have he := Option.some.inj hq'
  subst he
  have hqr := Q_real hO hu hq
  have path := trace.parentPath hO (hO.real_positive q hqr)
  obtain ⟨c, hqc, hcp⟩ := ParentPath.last path hne
  have hcr : Real c := ParentPath.real hO hqc hqr
  have hreach : QReach F u c := .cons hq (ParentPath.qreach hO hqc)
  have hhitu : Hit F (F.value u) u p := .next (by omega) hq trace
  have hhitc : Hit F (F.value u) c p := by
    rcases Hit.or_reach hhitu hreach with h | h
    · exact h
    · have h1 := h.column_le hO
      have h2 := P_column_lt hO hcp
      omega
  have hcne : c ≠ p := by
    intro h
    subst h
    have := P_column_lt hO hcp
    omega
  have hinv := inv_reach hF hv hreach hu hhitu (Row.lt_B _ _) hhitc hcne
  have hvc : F.value u ≤ F.value c := by
    cases hhitc with
    | here _ _ => exact absurd rfl hcne
    | next hrej _ _ =>
      by_contra hn
      exact hrej ⟨hO.real_positive c hcr, by omega⟩
  obtain ⟨cp, hcup⟩ := hF.upper_exists c hcr (by omega)
  obtain ⟨p1, hp1, hrowc, hvcp, hlc⟩ := hF.upper_step c cp hcr hcup
  rw [hcp] at hp1
  have e1 : p1 = p := (Option.some.inj hp1).symm
  rw [e1] at hrowc hvcp hlc
  obtain ⟨p2, hp2, hrowu, hvup, hlu⟩ := hF.upper_step u up hu hup
  rw [hPu] at hp2
  have e2 : p2 = p := (Option.some.inj hp2).symm
  rw [e2] at hrowu hvup hlu
  have hcu : F.height c ≤ F.height u := hreach.height_le hO
  have hpc : F.height p ≤ F.height c := hhitc.height_le hO
  have hrows : F.height up = F.height cp := by
    rw [hrowu, hrowc]
    exact Row.B_eq_of_between hcu hpc hinv
  refine ⟨c, cp, ParentPath.rawChain hF hqc hqr, (hF.rawParent_eq_P hcr).trans hcp, hcup, hrows, ?_, hvc⟩
  have hpv := P_value hO hPu
  exact normal_lex_of_value hF _ up cp rfl (real_of_upper hup) (real_of_upper hcup)
    (by rw [hlu, hlc]) hrows (by rw [hvup, hvcp]; omega)

/-- In a normal frame the stored parents going up a column do not move right: the parent
of `z⁺⁺` is at or left of the parent of `z⁺`. -/
theorem normal_rawParent_column_up {F : Frame} (hF : F.Normal) {z z1 a b : F.Node}
    (_hz : Real z) (hzu : F.upper z = some z1) (ha : F.rawParent z = some a)
    (hb : F.rawParent z1 = some b) : b.1.val ≤ a.1.val := by
  have hO := hF.toOrdered
  have hz1 : Real z1 := real_of_upper hzu
  have hPb : F.P z1 = some b := (hF.rawParent_eq_P hz1).symm.trans hb
  obtain ⟨q, hq, hit⟩ := (P_iff hO).mp hPb
  obtain ⟨left, hleft, _, _, hql, _⟩ := Q_spec hO hq
  have hla := upper_left hzu ha
  rw [hla] at hleft
  have hl2 : F.lookup (ref a) = F.lookup (ref left) := by rw [Option.some.inj hleft]
  rw [lookup_ref, lookup_ref] at hl2
  obtain rfl := Option.some.inj hl2
  have h1 := hit.column_le hO
  rw [hql] at h1
  exact h1

end OmegaY.Official.Recon.CrossUpper

#print axioms OmegaY.Official.Recon.CrossUpper.normal_crossLex
#print axioms OmegaY.Official.Recon.CrossUpper.normal_rawParent_column_up
