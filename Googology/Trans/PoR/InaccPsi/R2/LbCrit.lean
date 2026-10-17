import Googology.Trans.PoR.InaccPsi.R2.NcCPB
import Googology.Trans.PoR.InaccPsi.R2.VzW

/-!
# Exact criteria for a lower bound `X ≤ ν_C`, restarts only

`ν_C` is the least right end of a non-standard `<₂`-pair of `R₂^C` (`nuC`), `ρ_L <₂ ν_C` the first such
pair (`pairs_cof_nuC`), `B₀ = Λ_B + ω²` the frontier of BLK^O in `R2.VzW` (`vzSpec2`).

* `lbReach_unique`: a reach is unique;
* `lbFirst0`, `lbFirstB`, `lbFirst` (**the first non-standard pair, all its data**): `ρ_L = υ_L` with `L` a
  restart index, `ρ_L <₂ ν_C = lh(ρ_L)`, not `ρ_L ≤₁ ν_C + 1`, and its `≤₁`-predecessors of `ν_C` below
  `ρ_L` are restarts `υ_μ`, each with reach exactly `ν_C`, cofinal in `ρ_L` and finitely many below every
  `s < ρ_L` (Theorem O^C at `k = 2`, `oC2`); above a BLK^O frontier `B` (any `OffSpecGen O B`, `lbFirstB`)
  also `B ≤ L` and `B ≤ μ`; `lbFirst` is the case `B = B₀`;
* `lbLe_iff_noSucc` (**NOSUCC**): `X ≤ ν_C` iff no restart has a `<₂`-successor below `X`;
* `lbLe_iff_PQ` (**the (P)/(Q) form**): `X ≤ ν_C` iff every restart `ρ_λ` and every `r < X` with (P) at
  `(ρ_λ, r)` have `ρ_λ ≤₁ r + 1` (a restart that is a limit of `≤₁`-predecessors of `r` reaches past `r`);
* `lbLe_iff_reach` (**NU-MIN, restart form**): `X ≤ ν_C` iff no restart `ρ_λ` with reach `r < X` has
  `{α < ρ_λ | α ≤₁ r}` cofinal in `ρ_λ`;
* `lbLe_iff_rstB`, `lbLe_iff_rst` (**the same with restart witnesses, above a frontier**): it suffices to
  look at limits `λ ≥ B` of restart indices and at restart witnesses `υ_μ`;
* `lbLe_of_capsB`, `lbLe_of_caps` (**the form for a reach calculus**): upper bounds `cap(μ)` of the reaches
  of the restarts in `[B, X)`, lower bounds `ρ_λ ≤₁ lo(λ)` at the limit restarts there, and the ordinal
  comparison "`X ≤ lo(λ)` or `cap(μ) < lo(λ)` for all restarts `μ` cofinally below `λ`" give `X ≤ ν_C`;
  `lbCaps_of_le` (**converse**): with exact reaches (`cap = lo = lh`) the comparison holds when `X ≤ ν_C`.

No new axiom, no new definition.

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lb

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Nc

/-- A reach is unique. -/
theorem lbReach_unique {a r r' : Ordinal.{0}} (h : IsReach R2C a r) (h' : IsReach R2C a r') :
    r = r' :=
  le_antisymm (h'.2 r h.1) (h.2 r' h'.1)

/-- **The first non-standard pair, with all its data** (frontier-free). -/
theorem lbFirst0 : ∃ l, IsRestartIdx l ∧ upsilon l < nuC ∧
    le2 (upsilon l) nuC ∧ IsReach R2C (upsilon l) nuC ∧ ¬ le1 (upsilon l) (nuC + 1) ∧
    NcCofPred (upsilon l) nuC ∧
    (∀ y < upsilon l, le1 y nuC → ∃ μ, IsRestartIdx μ ∧ y = upsilon μ ∧
      IsReach R2C (upsilon μ) nuC) ∧
    (∀ s < upsilon l, Set.Finite {u | u < s ∧ le1 u nuC}) := by
  obtain ⟨⟨l, hl, hlν, h2, -⟩, -⟩ := pairs_cof_nuC
  have h1 := le2_le1 h2
  have hU := U2_below hl hlν h2
  refine ⟨l, hl, hlν, h2, reach_U2 hlν.le h1, nuC_cap _ hlν.le _ (Order.lt_succ nuC), ?_, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨y, hγy, hyl, hy⟩ := hU.2.1 γ hγ
    exact ⟨y, hγy, hyl, le1_trans hy h1⟩
  · intro y hy hy1
    obtain ⟨μ, hμ, rfl⟩ := hU.2.2 y hy ((hU.1 y hy).1 hy1)
    exact ⟨μ, hμ, rfl, reach_U2 (hy.trans hlν).le hy1⟩
  · intro s hs
    refine (oC2 hl hlν h2 s hs).subset ?_
    rintro u ⟨hus, hu1⟩
    exact ⟨hus, (hU.1 u (hus.trans hs)).1 hu1⟩

/-- **The first non-standard pair above a BLK^O frontier `B`** (any general offset specification
`OffSpecGen O B`): `B ≤ L`, and every `≤₁`-predecessor `υ_μ < ρ_L` of `ν_C` has `B ≤ μ`. -/
theorem lbFirstB {O : Ordinal.{0} → Ordinal.{0}} {B : Ordinal.{0}} (hS : OffSpecGen O B) :
    ∃ l, IsRestartIdx l ∧ B ≤ l ∧ upsilon l < nuC ∧
    le2 (upsilon l) nuC ∧ IsReach R2C (upsilon l) nuC ∧ ¬ le1 (upsilon l) (nuC + 1) ∧
    NcCofPred (upsilon l) nuC ∧
    (∀ y < upsilon l, le1 y nuC → ∃ μ, IsRestartIdx μ ∧ B ≤ μ ∧ y = upsilon μ ∧
      IsReach R2C (upsilon μ) nuC) ∧
    (∀ s < upsilon l, Set.Finite {u | u < s ∧ le1 u nuC}) := by
  obtain ⟨⟨l, hl, hlν, h2, -⟩, -⟩ := pairs_cof_nuC
  have h1 := le2_le1 h2
  have hU := U2_below hl hlν h2
  have hB := left_ge_of_spec hS hl hlν h2
  have hBν : upsilon B ≤ nuC := (upsilon_normal.strictMono.monotone hB).trans hlν.le
  refine ⟨l, hl, hB, hlν, h2, reach_U2 hlν.le h1, nuC_cap _ hlν.le _ (Order.lt_succ nuC), ?_, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨y, hγy, hyl, hy⟩ := hU.2.1 γ hγ
    exact ⟨y, hγy, hyl, le1_trans hy h1⟩
  · intro y hy hy1
    obtain ⟨μ, hμ, rfl⟩ := hU.2.2 y hy ((hU.1 y hy).1 hy1)
    refine ⟨μ, hμ, ?_, rfl, reach_U2 (hy.trans hlν).le hy1⟩
    by_contra hlt
    exact (good_BGen hS).below _ (upsilon_normal.strictMono (not_le.1 hlt)) nuC hBν hy1
  · intro s hs
    refine (oC2 hl hlν h2 s hs).subset ?_
    rintro u ⟨hus, hu1⟩
    exact ⟨hus, (hU.1 u (hus.trans hs)).1 hu1⟩

/-- **The first non-standard pair above the frontier `B₀ = Λ_B + ω²`** of `R2.VzW`. -/
theorem lbFirst : ∃ l, IsRestartIdx l ∧ VzLam + ω * ω ≤ l ∧ upsilon l < nuC ∧
    le2 (upsilon l) nuC ∧ IsReach R2C (upsilon l) nuC ∧ ¬ le1 (upsilon l) (nuC + 1) ∧
    NcCofPred (upsilon l) nuC ∧
    (∀ y < upsilon l, le1 y nuC → ∃ μ, IsRestartIdx μ ∧ VzLam + ω * ω ≤ μ ∧ y = upsilon μ ∧
      IsReach R2C (upsilon μ) nuC) ∧
    (∀ s < upsilon l, Set.Finite {u | u < s ∧ le1 u nuC}) :=
  lbFirstB vzSpec2

/-- A restart `υ_λ` is indecomposable and not a `τ`-point. -/
theorem lbRst_ok {l : Ordinal.{0}} (hl : IsRestartIdx l) :
    Indec (upsilon l) ∧ ¬ NcTauPt (upsilon l) :=
  ⟨indec_of_upsPt (upsPt_upsilon (pos_iff_ne_zero.2 hl.1)), ncRestart_not_tau hl⟩

/-- **NOSUCC**: `X ≤ ν_C` iff no restart has a `<₂`-successor below `X`. -/
theorem lbLe_iff_noSucc (X : Ordinal.{0}) :
    X ≤ nuC ↔ ∀ l, IsRestartIdx l → ∀ d, upsilon l < d → d < X → ¬ le2 (upsilon l) d := by
  constructor
  · intro hX l hl d hld hdX h2
    exact noSucc_C hl d hld (lt_of_lt_of_le hdX hX) h2
  · intro H
    by_contra hlt
    obtain ⟨l, hl, hlν, h2, -⟩ := lbFirst0
    exact H l hl nuC hlν (not_le.1 hlt) h2

/-- **The (P)/(Q) form**: `X ≤ ν_C` iff for every restart `ρ_λ` and every `r < X`, `ρ_λ ≤ r`, (P) at
`(ρ_λ, r)` gives `ρ_λ ≤₁ r + 1`. -/
theorem lbLe_iff_PQ (X : Ordinal.{0}) :
    X ≤ nuC ↔ ∀ l, IsRestartIdx l → ∀ r, upsilon l ≤ r → r < X →
      NcCofPred (upsilon l) r → le1 (upsilon l) (r + 1) := by
  constructor
  · intro hX l hl r hlr hrX hP
    by_contra hQ
    have := ncCpb (lbRst_ok hl).1 (lbRst_ok hl).2 hlr hP hQ
    exact absurd (this.trans_lt hrX) (not_lt.2 hX)
  · intro H
    by_contra hlt
    obtain ⟨l, hl, hlν, -, -, hQ, hP, -⟩ := lbFirst0
    exact hQ (H l hl nuC hlν.le (not_le.1 hlt) hP)

/-- **NU-MIN, restart form**: `X ≤ ν_C` iff no restart `ρ_λ` with reach `r < X` has its
`≤₁`-predecessors of `r` cofinal in `ρ_λ`. -/
theorem lbLe_iff_reach (X : Ordinal.{0}) :
    X ≤ nuC ↔ ∀ l, IsRestartIdx l → ∀ r, r < X → IsReach R2C (upsilon l) r →
      ¬ NcCofPred (upsilon l) r := by
  constructor
  · intro hX l hl r hrX hr hP
    have := ncCpb_reach (lbRst_ok hl).1 (lbRst_ok hl).2 hr hP
    exact absurd (this.trans_lt hrX) (not_lt.2 hX)
  · intro H
    by_contra hlt
    obtain ⟨l, hl, -, -, hr, -, hP, -⟩ := lbFirst0
    exact H l hl nuC (not_le.1 hlt) hr hP

/-- Cofinality in `ρ_λ` from cofinality of restart indices in `λ`. -/
theorem lbCof_of_idx {l r : Ordinal.{0}} (hl : IsRestartIdx l)
    (h : ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ le1 (upsilon μ) r) :
    NcCofPred (upsilon l) r := by
  intro γ hγ
  obtain ⟨_, ⟨ι, hι, rfl⟩, hγι⟩ := (lt_isLUB_iff (upsilon_limit (ri_lim hl))).1 hγ
  obtain ⟨μ, -, hιμ, hμl, h1⟩ := h ι hι
  exact ⟨upsilon μ, hγι.trans (upsilon_normal.strictMono hιμ), upsilon_normal.strictMono hμl, h1⟩

/-- **The restart form, above a frontier `B`** (any `OffSpecGen O B`): `X ≤ ν_C` iff every limit `λ ≥ B` of restart indices
with reach `r < X` has a bound `ν < λ` above which no restart `υ_μ`, `μ < λ`, is `≤₁ r`. -/
theorem lbLe_iff_rstB {O : Ordinal.{0} → Ordinal.{0}} {B : Ordinal.{0}} (hS : OffSpecGen O B)
    (X : Ordinal.{0}) :
    X ≤ nuC ↔ ∀ l, IsRestartIdx l → B ≤ l →
      (∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l) →
      ∀ r, r < X → IsReach R2C (upsilon l) r →
      ∃ ν < l, ∀ μ, IsRestartIdx μ → ν < μ → μ < l → ¬ le1 (upsilon μ) r := by
  constructor
  · intro hX l hl _ _ r hrX hr
    by_contra hall
    push Not at hall
    refine (lbLe_iff_reach X).1 hX l hl r hrX hr (lbCof_of_idx hl fun ν hν => ?_)
    obtain ⟨μ, hμ, h1, h2, h3⟩ := hall ν hν
    exact ⟨μ, hμ, h1, h2, h3⟩
  · intro H
    by_contra hlt
    obtain ⟨l, hl, hB, hlν, -, hr, -, hP, hW, -⟩ := lbFirstB hS
    have hwit : ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ le1 (upsilon μ) nuC := by
      intro ν hν
      obtain ⟨y, hνy, hyl, hy⟩ := hP (upsilon ν) (upsilon_normal.strictMono hν)
      obtain ⟨μ, hμ, -, rfl, -⟩ := hW y hyl hy
      exact ⟨μ, hμ, upsilon_normal.strictMono.lt_iff_lt.1 hνy,
        upsilon_normal.strictMono.lt_iff_lt.1 hyl, hy⟩
    obtain ⟨ν, hν, hno⟩ := H l hl hB (fun ν hν => by
      obtain ⟨μ, hμ, h1, h2, -⟩ := hwit ν hν; exact ⟨μ, hμ, h1, h2⟩) nuC (not_le.1 hlt) hr
    obtain ⟨μ, hμ, h1, h2, h3⟩ := hwit ν hν
    exact hno μ hμ h1 h2 h3

/-- **The form for a reach calculus**: caps of the restarts in `[B, X)` (`OffSpecGen O B`), lower bounds at the limit
restarts there, and an ordinal comparison give `X ≤ ν_C`. -/
theorem lbLe_of_capsB {O : Ordinal.{0} → Ordinal.{0}} {B : Ordinal.{0}} (hS : OffSpecGen O B)
    {X : Ordinal.{0}} (cap lo : Ordinal.{0} → Ordinal.{0})
    (hcap : ∀ μ, IsRestartIdx μ → B ≤ μ → upsilon μ < X →
      ∀ g, le1 (upsilon μ) g → g ≤ cap μ)
    (hlo : ∀ l, IsRestartIdx l → B ≤ l → upsilon l < X →
      (∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l) → le1 (upsilon l) (lo l))
    (harith : ∀ l, IsRestartIdx l → B ≤ l → upsilon l < X →
      (∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l) →
      X ≤ lo l ∨ ∃ ν < l, ∀ μ, IsRestartIdx μ → ν < μ → μ < l → cap μ < lo l) :
    X ≤ nuC := by
  by_contra hlt
  have hνX : nuC < X := not_le.1 hlt
  obtain ⟨l, hl, hB, hlν, -, hr, -, hP, hW, -⟩ := lbFirstB hS
  have hwit : ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ B ≤ μ ∧ ν < μ ∧ μ < l ∧
      le1 (upsilon μ) nuC := by
    intro ν hν
    obtain ⟨y, hνy, hyl, hy⟩ := hP (upsilon ν) (upsilon_normal.strictMono hν)
    obtain ⟨μ, hμ, hBμ, rfl, -⟩ := hW y hyl hy
    exact ⟨μ, hμ, hBμ, upsilon_normal.strictMono.lt_iff_lt.1 hνy,
      upsilon_normal.strictMono.lt_iff_lt.1 hyl, hy⟩
  have hlim : ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l := fun ν hν => by
    obtain ⟨μ, hμ, -, h1, h2, -⟩ := hwit ν hν; exact ⟨μ, hμ, h1, h2⟩
  have hlX : upsilon l < X := hlν.trans hνX
  have hlo1 := hlo l hl hB hlX hlim
  have hloν : lo l ≤ nuC := hr.2 _ hlo1
  rcases harith l hl hB hlX hlim with hXlo | ⟨ν, hν, hcmp⟩
  · exact absurd (hloν.trans_lt hνX) (not_lt.2 hXlo)
  · obtain ⟨μ, hμ, hBμ, h1, h2, h3⟩ := hwit ν hν
    have hμX : upsilon μ < X := (upsilon_normal.strictMono h2).trans hlX
    have := hcap μ hμ hBμ hμX nuC h3
    exact absurd ((hcmp μ hμ h1 h2).trans_le (hloν.trans this)) (lt_irrefl _)

/-- **The restart form, above the frontier `B₀ = Λ_B + ω²`**: `X ≤ ν_C` iff every limit `λ ≥ B₀` of
restart indices with reach `r < X` has a bound `ν < λ` above which no restart `υ_μ`, `μ < λ`, is `≤₁ r`. -/
theorem lbLe_iff_rst (X : Ordinal.{0}) :
    X ≤ nuC ↔ ∀ l, IsRestartIdx l → VzLam + ω * ω ≤ l →
      (∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l) →
      ∀ r, r < X → IsReach R2C (upsilon l) r →
      ∃ ν < l, ∀ μ, IsRestartIdx μ → ν < μ → μ < l → ¬ le1 (upsilon μ) r :=
  lbLe_iff_rstB vzSpec2 X

/-- **The form for a reach calculus, above `B₀ = Λ_B + ω²`**: caps of the restarts in `[B₀, X)`, lower
bounds at the limit restarts there, and an ordinal comparison give `X ≤ ν_C`. -/
theorem lbLe_of_caps {X : Ordinal.{0}} (cap lo : Ordinal.{0} → Ordinal.{0})
    (hcap : ∀ μ, IsRestartIdx μ → VzLam + ω * ω ≤ μ → upsilon μ < X →
      ∀ g, le1 (upsilon μ) g → g ≤ cap μ)
    (hlo : ∀ l, IsRestartIdx l → VzLam + ω * ω ≤ l → upsilon l < X →
      (∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l) → le1 (upsilon l) (lo l))
    (harith : ∀ l, IsRestartIdx l → VzLam + ω * ω ≤ l → upsilon l < X →
      (∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l) →
      X ≤ lo l ∨ ∃ ν < l, ∀ μ, IsRestartIdx μ → ν < μ → μ < l → cap μ < lo l) :
    X ≤ nuC :=
  lbLe_of_capsB vzSpec2 cap lo hcap hlo harith

/-- **Converse of `lbLe_of_caps`**: with exact reaches `R` (`cap = lo = R`) the comparison holds at
every restart `λ` with `υ_λ < X` when `X ≤ ν_C`. -/
theorem lbCaps_of_le {X : Ordinal.{0}} (hX : X ≤ nuC) (R : Ordinal.{0} → Ordinal.{0})
    (hR : ∀ l, IsRestartIdx l → upsilon l < X → IsReach R2C (upsilon l) (R l)) :
    ∀ l, IsRestartIdx l → upsilon l < X →
      X ≤ R l ∨ ∃ ν < l, ∀ μ, IsRestartIdx μ → ν < μ → μ < l → R μ < R l := by
  intro l hl hlX
  rcases le_or_gt X (R l) with h | hRX
  · exact Or.inl h
  right
  by_contra hall
  push Not at hall
  refine (lbLe_iff_reach X).1 hX l hl (R l) hRX (hR l hl hlX) (lbCof_of_idx hl fun ν hν => ?_)
  obtain ⟨μ, hμ, h1, h2, h3⟩ := hall ν hν
  have hμX : upsilon μ < X := (upsilon_normal.strictMono h2).trans hlX
  have hμl : upsilon μ ≤ R l :=
    ((upsilon_normal.strictMono h2).le).trans (le1_le (hR l hl hlX).1)
  exact ⟨μ, hμ, h1, h2, le1_of_le_of_le1 hμl h3 (hR μ hμ hμX).1⟩

end Googology.Trans.PoR.InaccPsi.R2.Lb
