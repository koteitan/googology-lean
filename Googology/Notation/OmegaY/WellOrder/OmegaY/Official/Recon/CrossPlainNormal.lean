/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CrossPlainNormal.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossLex
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.FatherUpperBound
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.CanonicalFrontier

set_option backward.do.legacy false

/-!
# The cross case in a normal frame

`CrossLexHolds` (`CrossLex.lean`) is a statement about the output mountain of an expansion.
This file proves the same statement in a **normal frame** (`Frame.Normal`, Phyrion's exact
local rules: every real node with a node above has its stored parent equal to the numerical
parent `P`, the row law `row u⁺ = B(row u, row P u)` and the value law
`v(u⁺) = v(u) - v(P u)`). Every canonical mountain `M(s)` is normal
(`Canonical.build_normal_of_success`), so this is the statement for the input mountain.

Let `s₀` be a real node with a node `s⁺` above it, `p = π(s⁺)` its stored parent and
`q₀ = Q s₀` its candidate. For every chain of stored parents `q₀ → … → c` with `π(c⁺) = p`
(`normal_crossLex`):

* `v(s₀) ≤ v(c)`: along the chain the canonical search from `q₀` with the threshold `v(s₀)`
  is not finished (`chain_facts`, by the determinism of the search, `Hit.unique`);
* `row c⁺ = row s⁺`: the rows above the chain do not decrease (Phyrion's father upper
  bound `father_upper_bound`), so `row s₀ < row q₀⁺ ≤ row c⁺`; with
  `row p ≤ row c ≤ row s₀` the two rows `B(row c, row p)` and `B(row s₀, row p)` are equal
  (`Row.B_eq_of_between`);
* `Lex s⁺ c⁺`: in a normal frame the comparison `Lex` follows from the values
  (`lex_of_value_le`): the parents of two nodes with the same stored left end and row are
  found by the same search, with the smaller threshold stopping at or after the larger one.

No hypothesis beyond `Frame.Normal` is used.
-/

namespace OmegaY.Official.Recon.CrossPlain

open Canonical Geometry Frame

variable {F : Frame}

/-! ## Threshold searches -/

/-- A threshold search is deterministic. -/
theorem Hit.unique {th : Nat} {a b b' : F.Node} (h : Hit F th a b) (h' : Hit F th a b') :
    b = b' := by
  induction h generalizing b' with
  | here hpos hsmall =>
    cases h' with
    | here _ _ => rfl
    | next hrej _ _ => exact absurd ⟨hpos, hsmall⟩ hrej
  | next hrej hQ rest ih =>
    cases h' with
    | here hpos hsmall => exact absurd ⟨hpos, hsmall⟩ hrej
    | next _ hQ' rest' =>
      have he := Option.some.inj (hQ.symm.trans hQ')
      subst he
      exact ih rest'

/-- A search that moves ends strictly left of its start. -/
theorem Hit.column_lt_of_ne (hF : F.Ordered) {th : Nat} {a b : F.Node} (h : Hit F th a b)
    (hne : a ≠ b) : b.1.val < a.1.val := by
  cases h with
  | here _ _ => exact absurd rfl hne
  | next _ hQ rest => exact lt_of_le_of_lt (rest.column_le hF) (Q_column_lt hF hQ)

/-- A search from `a` that does not stop at `a` has a threshold at most `v(a)` (for a real
`a`). -/
theorem hit_threshold_le (hF : F.Ordered) {th : Nat} {a b : F.Node} (h : Hit F th a b)
    (hne : a ≠ b) (ha : Real a) : th ≤ F.value a := by
  cases h with
  | here _ _ => exact absurd rfl hne
  | next hrej _ _ =>
    by_contra hlt
    exact hrej ⟨hF.real_positive a ha, by omega⟩

/-! ## `Lex` from values -/

/-- **`Lex` from values in a normal frame.** Two real nodes with the same stored left end and
the same row, the first of value at most the second, satisfy `Lex`. -/
theorem lex_of_value_le (hF : F.Normal) :
    ∀ (k : Nat) (z w : F.Node), F.length z.1 - z.2.val = k → Real z → Real w →
      (F.cell z).left = (F.cell w).left → F.height z = F.height w →
      F.value z ≤ F.value w → Lex F z w := by
  have hO := hF.toOrdered
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro z w hk hz hw hl hh hv
    cases hzu : F.upper z with
    | none => exact Lex.top hzu
    | some z' =>
      have hz1 := hF.upper_nontrivial z z' hz hzu
      obtain ⟨w', hwu⟩ := hF.upper_exists w hw (by omega)
      obtain ⟨a, hPa, hza, hva, hla⟩ := hF.upper_step z z' hz hzu
      obtain ⟨b, hPb, hwb, hvb, hlb⟩ := hF.upper_step w w' hw hwu
      have hQ : F.Q z = F.Q w := Q_congr hl hh
      obtain ⟨q, hq, hita⟩ := (P_iff hO).mp hPa
      obtain ⟨q', hq', hitb⟩ := (P_iff hO).mp hPb
      rw [hQ, hq'] at hq
      obtain rfl := Option.some.inj hq
      have hraz : F.rawParent z = some a := rawParent_eq_of_upper_left hzu hla
      have hrbw : F.rawParent w = some b := rawParent_eq_of_upper_left hwu hlb
      have hcol : a.1.val ≤ b.1.val := Hit.column_le_of_le hO hita hv hitb
      rcases Nat.lt_or_eq_of_le hcol with hlt | heq
      · exact Lex.left hraz hrbw hlt
      · -- the same column: the same parent
        obtain ⟨r, hr, hra⟩ := hita.loosen hv
        have hrb : r = b := Hit.unique hr hitb
        subst hrb
        have hab : a = r := by
          by_contra hne
          have := Hit.column_lt_of_ne hO hra (Ne.symm hne)
          omega
        subst hab
        have hh' : F.height z' = F.height w' := by rw [hza, hwb, hh]
        obtain ⟨hz'1, hz'2⟩ := upper_spec hzu
        have hk' : F.length z'.1 - z'.2.val < k := by
          have h1 : z'.2.val < F.length z'.1 := z'.2.isLt
          have h2 : F.length z'.1 = F.length z.1 := by rw [hz'1]
          omega
        refine Lex.same hzu hwu hraz hrbw hh' ?_
        exact ih _ hk' z' w' rfl (real_of_upper hzu) (real_of_upper hwu)
          (by rw [hla, hlb]) hh' (by rw [hva, hvb]; omega)

/-! ## The chain from the candidate -/

/-- Along a chain of stored parents from a node `a` whose search with threshold `th > 1`
ends at `pM`, to a node `c` with `π(c⁺) = pM`: the search is not finished at `c`
(`th ≤ v(c)`), `c` is real, its row is at most the row of `a`, and the row above does not
decrease. -/
theorem chain_facts (hF : F.Normal) {th : Nat} (hth : 1 < th) {pM : F.Node} :
    ∀ {a c : F.Node}, RawChain F a c → F.rawParent c = some pM → Real a →
      Hit F th a pM →
      th ≤ F.value c ∧ Real c ∧ F.height c ≤ F.height a ∧
        F.aboveHeight a ≤ F.aboveHeight c := by
  have hO := hF.toOrdered
  intro a c hchain
  induction hchain with
  | here c =>
    intro hcp hc hhit
    have hne : c ≠ pM := by
      intro he
      have := rawParent_column_lt hO hcp
      rw [he] at this
      omega
    exact ⟨hit_threshold_le hO hhit hne hc, hc, le_rfl, le_rfl⟩
  | @step a b c hraw rest ih =>
    intro hcp ha hhit
    have hcolc := rawParent_column_lt hO hcp
    have hcb := rest.column_le hO
    have hba := rawParent_column_lt hO hraw
    have hne : a ≠ pM := by
      intro he
      rw [he] at hba
      omega
    have hta := hit_threshold_le hO hhit hne ha
    have hPb : F.P a = some b := (hF.rawParent_eq_P ha).symm.trans hraw
    -- the search continues at `b`
    have hnext : ∃ qa, F.Q a = some qa ∧ Hit F th qa pM := by
      cases hhit with
      | here _ _ => exact absurd rfl hne
      | next _ hQ rest' => exact ⟨_, hQ, rest'⟩
    obtain ⟨qa, hqa, hitq⟩ := hnext
    obtain ⟨qa', hqa', hitb⟩ := (P_iff hO).mp hPb
    rw [hqa] at hqa'
    obtain rfl := Option.some.inj hqa'
    obtain ⟨r, hr, hrp⟩ := hitq.loosen hta
    have hrb : r = b := Hit.unique hr hitb
    subst hrb
    have hbreal : Real r := real_of_value_pos hO (P_value hO hPb).1
    obtain ⟨h1, h2, h3, h4⟩ := ih hcp hbreal hrp
    have hbne : r ≠ pM := by
      intro he
      rw [he] at hcb
      omega
    have htb := hit_threshold_le hO hrp hbne hbreal
    refine ⟨h1, h2, h3.trans (P_height_le hO hPb), ?_⟩
    exact (father_upper_bound hF hPb (by omega)).trans h4

/-- **The cross case in a normal frame.** For a real node `s₀` with the node `s⁺` above it,
the stored parent `pM = π(s⁺)` and the candidate `q₀ = Q s₀`, every chain of stored parents
`q₀ → … → c` with `π(c⁺) = pM` has `v(s₀) ≤ v(c)`, `row c⁺ = row s⁺` and `Lex s⁺ c⁺`. -/
theorem normal_crossLex (hF : F.Normal) {s0 sp pM q0 cm cmp : F.Node} (hs0 : Real s0)
    (hsp : F.upper s0 = some sp) (hpM : F.rawParent s0 = some pM) (hq0 : F.Q s0 = some q0)
    (hc : RawChain F q0 cm) (hcm : F.rawParent cm = some pM)
    (hcmp : F.upper cm = some cmp) :
    F.value s0 ≤ F.value cm ∧ F.height sp = F.height cmp ∧ Lex F sp cmp := by
  have hO := hF.toOrdered
  have hP : F.P s0 = some pM := (hF.rawParent_eq_P hs0).symm.trans hpM
  obtain ⟨q1, hq1, hhit⟩ := (P_iff hO).mp hP
  rw [hq0] at hq1
  obtain rfl := Option.some.inj hq1
  have hvals := P_value hO hP
  have hth : 1 < F.value s0 := by omega
  have hq0r : Real q0 := Q_real hO hs0 hq0
  obtain ⟨hv, hcr, hhc, habove⟩ := chain_facts hF hth hc hcm hq0r hhit
  -- the row above the candidate is above the row of `s₀`
  have hq0ne : q0 ≠ pM := by
    intro he
    have h1 := rawParent_column_lt hO hcm
    have h2 := hc.column_le hO
    rw [he] at h2
    omega
  have hq0v := hit_threshold_le hO hhit hq0ne hq0r
  obtain ⟨q0p, hq0p⟩ := hF.upper_exists q0 hq0r (by omega)
  have hgt : F.height s0 < F.aboveHeight q0 := by
    rw [aboveHeight_of_upper hq0p]
    exact Q_upper_gt hO hq0 hq0p
  have hgt' : F.height s0 < F.height cmp := by
    rw [← aboveHeight_of_upper hcmp]
    exact lt_of_lt_of_le hgt habove
  obtain ⟨hpc, hcmpB⟩ := hF.raw_B hcr hcmp hcm
  obtain ⟨_, hspB⟩ := hF.raw_B hs0 hsp hpM
  have hcs : F.height cm ≤ F.height s0 := hhc.trans (Q_height_le hO hq0)
  have hrow : F.height sp = F.height cmp := by
    rw [hspB, hcmpB]
    rw [hcmpB] at hgt'
    exact Row.B_eq_of_between hcs hpc hgt'
  refine ⟨hv, hrow, ?_⟩
  obtain ⟨a1, hPa1, _, hva1, hla1⟩ := hF.upper_step s0 sp hs0 hsp
  obtain ⟨a2, hPa2, _, hva2, hla2⟩ := hF.upper_step cm cmp hcr hcmp
  rw [hP] at hPa1
  obtain rfl := Option.some.inj hPa1
  have hPc : F.P cm = some pM := (hF.rawParent_eq_P hcr).symm.trans hcm
  rw [hPc] at hPa2
  obtain rfl := Option.some.inj hPa2
  exact lex_of_value_le hF _ sp cmp rfl (real_of_upper hsp) (real_of_upper hcmp)
    (by rw [hla1, hla2]) hrow (by rw [hva1, hva2]; omega)

/-- The chain exists: in a normal frame, when the candidate is not the parent, the chain of
stored parents from the candidate reaches a node whose stored parent is the parent. -/
theorem normal_chain_exists (hF : F.Normal) {s0 pM q0 : F.Node} (hs0 : Real s0)
    (hpM : F.rawParent s0 = some pM) (hq0 : F.Q s0 = some q0) (hne : q0 ≠ pM) :
    ∃ cm, RawChain F q0 cm ∧ F.rawParent cm = some pM := by
  have hO := hF.toOrdered
  have hP : F.P s0 = some pM := (hF.rawParent_eq_P hs0).symm.trans hpM
  obtain ⟨q1, hq1, hhit⟩ := (P_iff hO).mp hP
  rw [hq0] at hq1
  obtain rfl := Option.some.inj hq1
  have hq0r : Real q0 := Q_real hO hs0 hq0
  -- follow the parent path of the search
  have key : ∀ (k : Nat) (a : F.Node), a.1.val = k → Real a → a ≠ pM →
      Hit F (F.value s0) a pM → ∃ cm, RawChain F a cm ∧ F.rawParent cm = some pM := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro a hk ha hane hhit
      have hta := hit_threshold_le hO hhit hane ha
      have hvals := P_value hO hP
      obtain ⟨qa, hqa, hitq⟩ : ∃ qa, F.Q a = some qa ∧ Hit F (F.value s0) qa pM := by
        cases hhit with
        | here _ _ => exact absurd rfl hane
        | next _ hQ rest' => exact ⟨_, hQ, rest'⟩
      obtain ⟨r, hr, hrp⟩ := hitq.loosen hta
      have hPa : F.P a = some r := (P_iff hO).mpr ⟨qa, hqa, hr⟩
      have hraw : F.rawParent a = some r := (hF.rawParent_eq_P ha).trans hPa
      by_cases hrp' : r = pM
      · subst hrp'
        exact ⟨a, .here a, hraw⟩
      · have hrreal : Real r := real_of_value_pos hO (P_value hO hPa).1
        have hlt : r.1.val < k := by rw [← hk]; exact P_column_lt hO hPa
        obtain ⟨cm, hc, hcm⟩ := ih r.1.val hlt r rfl hrreal hrp' hrp
        exact ⟨cm, .step hraw hc, hcm⟩
  exact key _ q0 rfl hq0r hne hhit

end OmegaY.Official.Recon.CrossPlain

#print axioms OmegaY.Official.Recon.CrossPlain.lex_of_value_le
#print axioms OmegaY.Official.Recon.CrossPlain.normal_crossLex
#print axioms OmegaY.Official.Recon.CrossPlain.normal_chain_exists
