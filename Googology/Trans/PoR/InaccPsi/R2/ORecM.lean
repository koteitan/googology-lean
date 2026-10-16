import Googology.Trans.PoR.InaccPsi.R2.EpsM
import Googology.Trans.PoR.InaccPsi.R2.BlkGen

/-!
# The recursive offset with the terms `ε_{x+1}·n + t`, and Theorem BLK^O up to `Λ_{ε·ω}`

The project's recursive offset (its paper's Definition 2.2) over the terms `OTM`: a term `t` of `OT`,
or `ε_{x+1}·(m+1) + t` (`t` in `OT`); so every Cantor normal form in `x` below `ε_{x+1}·ω`.
`OrecM(λ) = sup ({1} ∪ {u(ρ_λ) + 1 : u realized cofinally below λ, constants below ρ_λ})`.

* `OrecM_le` (`OrecM(λ) ≤ ε_{ρ+1}·ω`), `OrecM_succ` (`= 1` at successor restart indices);
* `OrecM_eq_OrecE` (**`OrecM = OrecE` below `Λ_{ε·2}`**), `OrecM_LamE2`
  (`OrecM(Λ_{ε·2}) = ε_{ρ+1}·2 + 1`), `OrecE_lt_OrecM_LamE2` (`OrecE(Λ_{ε·2}) < OrecM(Λ_{ε·2})`: the
  stage-7 offset stops at `Λ_{ε·2}`);
* `CofEw`, `LamEw` (`Λ_{ε·ω}`: the least restart index below which `ε_{x+1}·n` is realized cofinally
  for every `n < ω`), `OrecM_lt_w` (below `Λ_{ε·ω}` the value is `< ε_{ρ+1}·ω`);
* `topIn_OrecM` (the input of Lemma TOP: the value `ε_{ρ+1}·n + v` is a term not realized cofinally,
  with the IMG package `RstK.pkg_ot`, `RstK.pkg_eNm` or `RstK.pkg_eMt`), `rsIn_OrecM` (the input of
  Lemma RS, with `rs_rstT` and `rs_rstM`), `specM`;
* `blkM` (**Theorem BLK^O with `OrecM` below `υ_B` for every `B ≤ Λ_{ε·ω}`**, `ω² ∣ B`, `B < Ω₁`),
  `coreM`, `LamEw_lt_Om1` (`Λ_{ε·ω} < Ω₁`, [C09] Cor 15.15), `reach_OrecM`
  (`lh(ρ_λ) = δ_λ + OrecM(λ)` for every restart index `λ < Λ_{ε·ω}`), `LamE2_lt_LamEw`,
  `reach_LamE2` (`lh(ρ_{Λ_{ε·2}}) = δ + ε_{ρ+1}·2 + 1`), `OrecM_LamEw` (`OrecM(Λ_{ε·ω}) = ε_{ρ+1}·ω`).

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order OT

/-! ## Terms below `ε_{x+1}·ω` -/

/-- Offset terms below `ε_{x+1}·ω`: a term `t` of `OT` (`tm0 t`), or `ε_{x+1}·(m+1) + t` (`tmE m t`). -/
inductive OTM : Type 1
  | tm0 : OT → OTM
  | tmE : ℕ → OT → OTM

open OTM

/-- The value of a term at `x`. -/
noncomputable def evM : OTM → Ordinal.{0} → Ordinal.{0}
  | tm0 t, x => ev t x
  | tmE m t, x => eN x * nS m + ev t x

/-- All constants below `s`. -/
def CBM : OTM → Ordinal.{0} → Prop
  | tm0 t, s => CB t s
  | tmE _ t, s => CB t s

theorem eN_mul_omega_pos (x : Ordinal.{0}) : 0 < eN x * ω :=
  mul_pos (eN_E x).pos omega0_pos

theorem eN_mul_nS_lt (x : Ordinal.{0}) (m : ℕ) : eN x * nS m < eN x * ω :=
  (mul_lt_mul_iff_right₀ (eN_E x).pos).2 (nS_lt_omega m)

theorem evM_lt {u : OTM} {x : Ordinal.{0}} (h : CBM u x) : evM u x < eN x * ω := by
  cases u with
  | tm0 t =>
    exact lt_of_lt_of_le (ev_lt_eN h) (by
      calc eN x = eN x * 1 := (mul_one _).symm
        _ ≤ eN x * ω := mul_le_mul_right one_lt_omega0.le _)
  | tmE m t =>
    calc eN x * nS m + ev t x < eN x * nS m + eN x := (add_lt_add_iff_left _).2 (ev_lt_eN h)
      _ = eN x * nS (m + 1) := (mul_nS_succ _ m).symm
      _ < eN x * ω := eN_mul_nS_lt x (m + 1)

/-- `ε·j ≤ ε·n + v` with `v < ε` gives `j ≤ n`. -/
theorem nat_le_of_mul_le {e v : Ordinal.{0}} (hv : v < e) {j n : ℕ}
    (h : e * (j : Ordinal.{0}) ≤ e * (n : Ordinal.{0}) + v) : j ≤ n := by
  by_contra hlt
  push Not at hlt
  have h1 : e * ((n + 1 : ℕ) : Ordinal.{0}) ≤ e * (j : Ordinal.{0}) :=
    mul_le_mul_right (by exact_mod_cast hlt) e
  have h2 : e * (n : Ordinal.{0}) + v < e * ((n + 1 : ℕ) : Ordinal.{0}) := by
    rw [Nat.cast_succ, mul_add_one]; exact (add_lt_add_iff_left _).2 hv
  exact absurd (h.trans_lt (h2.trans_le h1)) (lt_irrefl _)

/-! ## The recursion -/

/-- `u` is realized cofinally below `λ` by the offsets `O`. -/
def CofRealM (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) (u : OTM) : Prop :=
  ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ CBM u (upsilon μ) ∧ evM u (upsilon μ) ≤ O μ

/-- The set whose supremum is `OrecM(λ)`. -/
def OSetM (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Set Ordinal.{0} :=
  insert 1 {w | ∃ u, CBM u (upsilon l) ∧ CofRealM O l u ∧ w = evM u (upsilon l) + 1}

theorem OSetM_congr {O O' : Ordinal.{0} → Ordinal.{0}} {l : Ordinal.{0}}
    (h : ∀ μ < l, O μ = O' μ) : OSetM O l = OSetM O' l := by
  have key : ∀ u, CofRealM O l u ↔ CofRealM O' l u := by
    intro u
    constructor
    · intro hc ν hν
      obtain ⟨μ, h1, h2, h3, h4, h5⟩ := hc ν hν
      exact ⟨μ, h1, h2, h3, h4, by rw [← h μ h3]; exact h5⟩
    · intro hc ν hν
      obtain ⟨μ, h1, h2, h3, h4, h5⟩ := hc ν hν
      exact ⟨μ, h1, h2, h3, h4, by rw [h μ h3]; exact h5⟩
  ext w
  simp only [OSetM, Set.mem_insert_iff, Set.mem_setOf_eq, key]

/-- **The recursive offset over `OTM`**, by well-founded recursion. -/
noncomputable def OrecM : Ordinal.{0} → Ordinal.{0} :=
  Ordinal.lt_wf.fix (fun l IH => sSup (OSetM (fun μ => if h : μ < l then IH μ h else 0) l))

theorem OrecM_eq (l : Ordinal.{0}) : OrecM l = sSup (OSetM OrecM l) := by
  show Ordinal.lt_wf.fix _ l = _
  rw [WellFounded.fix_eq]
  rw [OSetM_congr (O' := OrecM) (fun μ hμ => by simp only [hμ, dite_true]; rfl)]

theorem OSetM_bdd (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) :
    ∀ w ∈ OSetM O l, w ≤ eN (upsilon l) * ω := by
  intro w hw
  rcases hw with rfl | ⟨u, hCB, -, rfl⟩
  · exact one_le_iff_pos.2 (eN_mul_omega_pos _)
  · exact add_one_le_of_lt (evM_lt hCB)

theorem OSetM_bddAbove (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) :
    BddAbove (OSetM O l) := ⟨_, OSetM_bdd O l⟩

/-- `OrecM(λ) ≤ ε_{ρ_λ+1}·ω`. -/
theorem OrecM_le (l : Ordinal.{0}) : OrecM l ≤ eN (upsilon l) * ω := by
  rw [OrecM_eq]; exact csSup_le ⟨1, Set.mem_insert _ _⟩ (OSetM_bdd _ l)

theorem one_le_OrecM (l : Ordinal.{0}) : 1 ≤ OrecM l := by
  rw [OrecM_eq]; exact le_csSup (OSetM_bddAbove _ l) (Set.mem_insert _ _)

theorem lt_OrecM_of_cof {l : Ordinal.{0}} {u : OTM} (hCB : CBM u (upsilon l))
    (hc : CofRealM OrecM l u) : evM u (upsilon l) < OrecM l := by
  have h1 : evM u (upsilon l) + 1 ≤ OrecM l := by
    rw [OrecM_eq]
    exact le_csSup (OSetM_bddAbove _ l) (Set.mem_insert_of_mem _ ⟨u, hCB, hc, rfl⟩)
  exact lt_of_lt_of_le (lt_add_one _) h1

theorem lt_OrecM {l z : Ordinal.{0}} (hz : z < OrecM l) :
    z = 0 ∨ ∃ u, CBM u (upsilon l) ∧ CofRealM OrecM l u ∧ z ≤ evM u (upsilon l) := by
  rw [OrecM_eq] at hz
  obtain ⟨w, hw, hzw⟩ := (lt_csSup_iff (OSetM_bddAbove _ l) ⟨1, Set.mem_insert _ _⟩).1 hz
  rcases hw with rfl | ⟨u, hCB, hc, rfl⟩
  · left; exact le_antisymm (Order.lt_add_one_iff.1 (by rw [zero_add]; exact hzw)) zero_le
  · right; exact ⟨u, hCB, hc, Order.lt_add_one_iff.1 hzw⟩

/-- `OrecM = 1` at a successor restart index. -/
theorem OrecM_succ {l : Ordinal.{0}} (hl : IsRestartIdx l) (h2 : cL l < 2) : OrecM l = 1 := by
  obtain ⟨l0, hl0, rfl⟩ := succ_ri hl h2
  have hww : 0 < ω * ω := mul_pos omega0_pos omega0_pos
  have hS : OSetM OrecM (l0 + ω * ω) = {1} := by
    ext w
    simp only [OSetM, Set.mem_insert_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro (h | ⟨u, -, hc, -⟩)
      · exact h
      · exfalso
        obtain ⟨μ, hμ, h1, h3, -, -⟩ := hc l0 (lt_add_of_pos_right l0 hww)
        exact absurd h3 (not_lt.2 (next_mult (mult_of hl0) (ri_iff.1 hμ).2 h1))
    · intro h; exact Or.inl h
  rw [OrecM_eq, hS, csSup_singleton]

/-! ## `OrecM = OrecE` below `Λ_{ε·2}` -/

theorem evM_tmE0 (t : OT) (x : Ordinal.{0}) : evM (tmE 0 t) x = eN x + ev t x := by
  simp [evM, nS]

theorem two_le_tmE (x : Ordinal.{0}) (m : ℕ) (t : OT) :
    eN x + eN x ≤ evM (tmE (m + 1) t) x := by
  show eN x + eN x ≤ eN x * nS (m + 1) + ev t x
  rw [mul_nS_succ]
  exact (add_le_add (le_mul_nS _ m) le_rfl).trans le_self_add

/-- **`OrecM = OrecE` below `Λ_{ε·2}`** (at every restart index): below `Λ_{ε·2}` no term
`ε_{x+1}·n + t` with `n ≥ 2` is realized cofinally. -/
theorem OrecM_eq_OrecE : ∀ l, IsRestartIdx l → l < LamE2 → OrecM l = OrecE l := by
  intro l
  induction l using WellFoundedLT.induction with
  | ind l IH =>
  intro hl hlE
  have key : ∀ μ, IsRestartIdx μ → μ < l → OrecM μ = OrecE μ := fun μ hμ hμl =>
    IH μ hμl hμ (hμl.trans hlE)
  have hS : OSetM OrecM l = OSetS SF OrecE l := by
    ext w
    simp only [OSetM, OSetS, Set.mem_insert_iff, Set.mem_setOf_eq]
    constructor
    · rintro (h | ⟨u, hCB, hc, rfl⟩)
      · exact Or.inl h
      cases u with
      | tm0 t =>
        refine Or.inr ⟨OTE.ot t, trivial, hCB, fun ν hν => ?_, rfl⟩
        obtain ⟨μ, hμ, h1, h2, h3, h4⟩ := hc ν hν
        exact ⟨μ, hμ, h1, h2, h3, by rw [← key μ hμ h2]; exact h4⟩
      | tmE m t =>
        rcases m with _ | m
        · refine Or.inr ⟨OTE.e t, trivial, hCB, fun ν hν => ?_, by rw [evM_tmE0]; rfl⟩
          obtain ⟨μ, hμ, h1, h2, h3, h4⟩ := hc ν hν
          refine ⟨μ, hμ, h1, h2, h3, ?_⟩
          rw [← key μ hμ h2]
          show eN _ + ev t _ ≤ _
          rw [← evM_tmE0]; exact h4
        · exfalso
          refine not_cofE2_of_lt hl hlE (fun ν hν => ?_)
          obtain ⟨μ, hμ, h1, h2, -, h4⟩ := hc ν hν
          exact ⟨μ, hμ, h1, h2, by rw [← key μ hμ h2]; exact (two_le_tmE _ m t).trans h4⟩
    · rintro (h | ⟨u, -, hCB, hc, rfl⟩)
      · exact Or.inl h
      cases u with
      | ot t =>
        refine Or.inr ⟨tm0 t, hCB, fun ν hν => ?_, rfl⟩
        obtain ⟨μ, hμ, h1, h2, h3, h4⟩ := hc ν hν
        exact ⟨μ, hμ, h1, h2, h3, by rw [key μ hμ h2]; exact h4⟩
      | e t =>
        refine Or.inr ⟨tmE 0 t, hCB, fun ν hν => ?_, by rw [evM_tmE0]; rfl⟩
        obtain ⟨μ, hμ, h1, h2, h3, h4⟩ := hc ν hν
        refine ⟨μ, hμ, h1, h2, h3, ?_⟩
        rw [key μ hμ h2, evM_tmE0]; exact h4
  rw [OrecM_eq, hS]
  exact (OrecS_eq SF l).symm

/-- **`OrecM(Λ_{ε·2}) = ε_{ρ+1}·2 + 1`** (`ρ = ρ_{Λ_{ε·2}}`). -/
theorem OrecM_LamE2 : OrecM LamE2 = eN (upsilon LamE2) + eN (upsilon LamE2) + 1 := by
  obtain ⟨hl, hcof⟩ := LamE2_spec LamE2_lt_Om1
  have hl0 : 0 < LamE2 := pos_iff_ne_zero.2 hl.1
  have hρ0 : 0 < upsilon LamE2 := (upsPt_upsilon hl0).1
  apply le_antisymm
  · rw [OrecM_eq]
    refine csSup_le ⟨1, Set.mem_insert _ _⟩ ?_
    rintro w (rfl | ⟨u, hCB, hc, rfl⟩)
    · exact le_add_self
    cases u with
    | tm0 t =>
      exact add_le_add ((ev_lt_eN hCB).le.trans le_self_add) le_rfl
    | tmE m t =>
      obtain ⟨μ, hμ, -, h2, h3, h4⟩ := hc 0 hl0
      have hμ0 : 0 < μ := pos_iff_ne_zero.2 hμ.1
      rw [OrecM_eq_OrecE μ hμ h2] at h4
      have h5 := h4.trans (OrecS_le SF μ)
      rcases m with _ | m
      · show eN _ * nS 0 + ev t _ + 1 ≤ _
        have : eN (upsilon LamE2) * nS 0 = eN (upsilon LamE2) := by simp [nS]
        rw [this]
        exact add_le_add (add_le_add le_rfl (ev_lt_eN hCB).le) le_rfl
      rcases m with _ | m
      · -- `ε·2 + t`: `t(ρ_μ) = 0`, so `t(ρ) = 0`
        have ht0 : ev t (upsilon LamE2) = 0 := by
          by_contra hne
          have h1 : 1 ≤ ev t (upsilon LamE2) := one_le_iff_ne_zero.2 hne
          have h1μ := (uni_one (Bases_ups hμ0 h2 LamE2_lt_Om1) h3).1 h1
          have e2 : eN (upsilon μ) * nS 1 = eN (upsilon μ) + eN (upsilon μ) := by
            rw [mul_nS_succ]; simp [nS]
          have : eN (upsilon μ) + eN (upsilon μ) + 1 ≤ eN (upsilon μ) + eN (upsilon μ) + 0 := by
            rw [add_zero]
            refine (add_le_add le_rfl h1μ).trans ?_
            show _ ≤ _
            have := h5
            simp only [evM] at this
            rw [e2] at this
            exact this
          exact absurd ((add_le_add_iff_left _).1 this) (by simp)
        show eN _ * nS 1 + ev t _ + 1 ≤ _
        rw [ht0, add_zero, mul_nS_succ]
        simp [nS]
      · exfalso
        have h6 := (two_le_tmE (upsilon μ) (m + 1) t)
        have e3 : evM (tmE (m + 1 + 1) t) (upsilon μ) =
            eN (upsilon μ) * nS (m + 1) + eN (upsilon μ) + ev t (upsilon μ) := by
          show eN _ * nS (m + 1 + 1) + _ = _
          rw [mul_nS_succ]
        have h7 : eN (upsilon μ) + eN (upsilon μ) + eN (upsilon μ) ≤
            evM (tmE (m + 1 + 1) t) (upsilon μ) := by
          rw [e3]
          refine le_self_add.trans' ?_
          refine add_le_add ?_ le_rfl
          have := two_le_tmE (upsilon μ) m (k 0)
          simpa [evM] using this
        have h8 := h7.trans h5
        have hpos := (eN_E (upsilon μ)).pos
        have : eN (upsilon μ) + eN (upsilon μ) < eN (upsilon μ) + eN (upsilon μ) + eN (upsilon μ) :=
          lt_add_of_pos_right _ hpos
        exact absurd (h8.trans_lt this) (lt_irrefl _)
  · have hc : CofRealM OrecM LamE2 (tmE 1 (k 0)) := by
      intro ν hν
      obtain ⟨μ, hμ, h1, h2, h3⟩ := hcof ν hν
      refine ⟨μ, hμ, h1, h2, (upsPt_upsilon (pos_iff_ne_zero.2 hμ.1)).1, ?_⟩
      rw [OrecM_eq_OrecE μ hμ h2]
      show eN _ * nS 1 + ev (k 0) _ ≤ _
      rw [mul_nS_succ]; simpa [nS] using h3
    have := lt_OrecM_of_cof (show CBM (tmE 1 (k 0)) (upsilon LamE2) from hρ0) hc
    have e : evM (tmE 1 (k 0)) (upsilon LamE2) = eN (upsilon LamE2) + eN (upsilon LamE2) := by
      show eN _ * nS 1 + ev (k 0) _ = _
      rw [mul_nS_succ]; simp [nS]
    rw [e] at this
    exact add_one_le_of_lt this

/-- **The stage-7 offset stops at `Λ_{ε·2}`**: `OrecE(Λ_{ε·2}) ≤ ε_{ρ+1}·2 < OrecM(Λ_{ε·2})`. -/
theorem OrecE_lt_OrecM_LamE2 : OrecE LamE2 < OrecM LamE2 := by
  rw [OrecM_LamE2]
  exact lt_of_le_of_lt (OrecS_le SF _) (lt_add_one _)

/-! ## The frontier `Λ_{ε·ω}` -/

/-- `ε_{x+1}·j` is realized cofinally below `λ` for every `j < ω`. -/
def CofEw (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Prop :=
  ∀ j : ℕ, ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ eN (upsilon μ) * (j : Ordinal.{0}) ≤ O μ

/-- `Λ_{ε·ω}`: the least restart index below which `ε_{x+1}·j` is realized cofinally by `OrecM` for
every `j < ω` (`Ω₁` if there is none). -/
noncomputable def LamEw : Ordinal.{0} := sInf (insert Om1 {l | IsRestartIdx l ∧ CofEw OrecM l})

theorem LamEw_le_Om1 : LamEw ≤ Om1 := csInf_le (OrderBot.bddBelow _) (Set.mem_insert _ _)

theorem not_cofEw_of_lt {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlE : l < LamEw) :
    ¬ CofEw OrecM l := fun h =>
  absurd (csInf_le (OrderBot.bddBelow _) (Set.mem_insert_of_mem _
    (show l ∈ {l | IsRestartIdx l ∧ CofEw OrecM l} from ⟨hl, h⟩))) (not_le.2 hlE)

theorem LamEw_spec (h : LamEw < Om1) : IsRestartIdx LamEw ∧ CofEw OrecM LamEw := by
  rcases csInf_mem (s := insert Om1 {l | IsRestartIdx l ∧ CofEw OrecM l})
    ⟨Om1, Set.mem_insert _ _⟩ with h' | h'
  · exact absurd (h' ▸ h : Om1 < Om1) (lt_irrefl _)
  · exact h'

/-- If `ε_{ρ+1}·(j+1) < OrecM(λ)` then `ε_{x+1}·(j+1)` is realized cofinally below `λ`. -/
theorem cof_of_lt_OrecM {l : Ordinal.{0}} (j : ℕ) (h : eN (upsilon l) * nS j < OrecM l) :
    ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ eN (upsilon μ) * nS j ≤ OrecM μ := by
  have hpos := (eN_E (upsilon l)).pos
  rcases lt_OrecM h with h0 | ⟨u, hCB, hc, hz⟩
  · exact absurd h0 (mul_pos hpos (nS_pos j)).ne'
  cases u with
  | tm0 t =>
    exact absurd ((le_mul_nS _ j).trans hz) (not_le.2 (ev_lt_eN hCB))
  | tmE m t =>
    have hjm : j + 1 ≤ m + 1 := nat_le_of_mul_le (ev_lt_eN hCB) hz
    intro ν hν
    obtain ⟨μ, hμ, h1, h2, -, h4⟩ := hc ν hν
    refine ⟨μ, hμ, h1, h2, le_trans ?_ (le_self_add.trans h4)⟩
    exact mul_le_mul_right (by exact_mod_cast hjm) _

/-- **Below `Λ_{ε·ω}` the value is `< ε_{ρ+1}·ω`**. -/
theorem OrecM_lt_w {l : Ordinal.{0}} (hno : ¬ CofEw OrecM l) : OrecM l < eN (upsilon l) * ω := by
  rcases (OrecM_le l).lt_or_eq with h | h
  · exact h
  exfalso
  apply hno
  intro j ν hν
  obtain ⟨μ, hμ, h1, h2, h3⟩ := cof_of_lt_OrecM j (by rw [h]; exact eN_mul_nS_lt _ j) ν hν
  refine ⟨μ, hμ, h1, h2, le_trans ?_ h3⟩
  exact mul_le_mul_right (by exact_mod_cast Nat.le_succ j) _

/-! ## The inputs of Lemmas TOP and RS -/

/-- **The input of Lemma TOP** at a restart index `λ` below which `ε_{x+1}·j` is not realized
cofinally for some `j`. -/
theorem topIn_OrecM {l : Ordinal.{0}} (hl : IsRestartIdx l) (hE : ¬ CofEw OrecM l) :
    TopInH OrecM l := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  have hρE : InE (upsilon l) := upsPt_inE hρU
  set e := eN (upsilon l) with he
  have he0 : e ≠ 0 := (eN_E _).pos.ne'
  have hlt := OrecM_lt_w hE
  have hone : 1 ≤ OrecM l := one_le_OrecM l
  have notcof : ∀ u, CBM u (upsilon l) → OrecM l = evM u (upsilon l) →
      ¬ CofRealM OrecM l u := fun u hCB hev hc =>
    absurd (lt_OrecM_of_cof hCB hc) (by rw [hev]; exact lt_irrefl _)
  -- `OrecM(λ) = ε·q + v`, `q < ω`, `v < ε`
  set q := OrecM l / e with hq
  set v := OrecM l % e with hv
  have hdm : e * q + v = OrecM l := div_add_mod _ _
  have hvlt : v < e := mod_lt _ he0
  have hqw : q < ω := (lt_mul_iff_div_lt he0).1 hlt
  obtain ⟨n, hn⟩ := lt_omega0.1 hqw
  obtain ⟨t0, hCB, hev⟩ := rep hρE v hvlt
  obtain ⟨m0, hm0, hm0c⟩ := cmax t0 _ hCB hρU.1
  -- the common part: from a term not realized cofinally to the bound below `λ`
  have mk : ∀ u : OTM, CBM u (upsilon l) → OrecM l = evM u (upsilon l) →
      (∀ μ, IsRestartIdx μ → CB t0 (upsilon μ) → CBM u (upsilon μ)) →
      ∃ x0, x0 < upsilon l ∧ ∀ μ, IsRestartIdx μ → μ < l → x0 < upsilon μ →
        OrecM μ < evM u (upsilon μ) := by
    intro u hCBu hevu hcb
    have hnot := notcof u hCBu hevu
    unfold CofRealM at hnot
    push Not at hnot
    obtain ⟨ν, hνl, hν⟩ := hnot
    have hνρ : upsilon ν < upsilon l := upsilon_normal.strictMono hνl
    refine ⟨max (upsilon ν) m0, max_lt hνρ hm0, fun μ hμ hμl hx0 => ?_⟩
    have hνμ : ν < μ := upsilon_normal.strictMono.lt_iff_lt.1 (lt_of_le_of_lt (le_max_left _ _) hx0)
    have hCBμ : CB t0 (upsilon μ) :=
      (cb_iff t0 _).2 (fun c hc => lt_of_le_of_lt ((hm0c c hc).trans (le_max_right _ _)) hx0)
    exact hν μ hμ hνμ hμl (hcb μ hμ hCBμ)
  rcases n with _ | m
  · -- a term of `OT`
    have hO : OrecM l = ev t0 (upsilon l) := by
      rw [← hdm, hn, Nat.cast_zero, mul_zero, zero_add, ← hev]
    obtain ⟨x0, hx0, hb⟩ := mk (tm0 t0) hCB hO (fun μ _ h => h)
    exact ⟨ev t0, x0, hO, hx0, hb, fun R => R.pkg_ot hCB (by rw [← hO]; exact hone)⟩
  rcases eq_or_ne v 0 with hv0 | hv0
  · -- `ε·n`
    have hO : OrecM l = evM (tmE m (k 0)) (upsilon l) := by
      show _ = e * nS m + ev (k 0) _
      rw [ev_k, add_zero, ← hdm, hn, hv0, add_zero]
    obtain ⟨x0, hx0, hb⟩ := mk (tmE m (k 0)) hρU.1 hO
      (fun μ hμ _ => (upsPt_upsilon (pos_iff_ne_zero.2 hμ.1)).1)
    refine ⟨fun x => eN x * nS m, x0, ?_, hx0, fun μ hμ hμl hx => ?_, fun R => R.pkg_eNm m⟩
    · rw [hO]; show e * nS m + ev (k 0) _ = _; rw [ev_k, add_zero]
    · have := hb μ hμ hμl hx
      simpa [evM, ev_k] using this
  · -- `ε·n + v`, `v ≥ 1`
    have hO : OrecM l = evM (tmE m t0) (upsilon l) := by
      show _ = e * nS m + ev t0 _
      rw [hev, ← hdm, hn]
    obtain ⟨x0, hx0, hb⟩ := mk (tmE m t0) hCB hO (fun μ _ h => h)
    exact ⟨fun x => eN x * nS m + ev t0 x, x0, hO, hx0, hb,
      fun R => R.pkg_eMt m hCB (by rw [hev]; exact one_le_iff_ne_zero.2 hv0)⟩

/-- **The input of Lemma RS at a limit restart index `λ`** for `OrecM`. -/
theorem rsIn_OrecM {l : Ordinal.{0}} (hl : IsRestartIdx l) (h2 : 2 ≤ cL l) : RsInGen OrecM l := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρ0 : 0 < upsilon l := (upsPt_upsilon hl0).1
  intro z hz
  rcases lt_OrecM hz with rfl | ⟨u, hCB, hc, hzu⟩
  · refine ⟨ev (k 0), zero_le, fun R htg => rs_rstT R hρ0 htg, fun ν hν => ?_⟩
    obtain ⟨μ, hμ, h1, h3, -⟩ := cL_dense hl le_rfl (lt_of_lt_of_le one_lt_two h2) ν hν
    exact ⟨μ, hμ, h1, h3, by rw [ev_k]; exact zero_le⟩
  · refine ⟨evM u, hzu, fun R htg => ?_, fun ν hν => ?_⟩
    · cases u with
      | tm0 t => exact rs_rstT R hCB htg
      | tmE m t => exact rs_rstM R m hCB htg
    · obtain ⟨μ, hμ, h1, h3, -, h5⟩ := hc ν hν
      exact ⟨μ, hμ, h1, h3, h5⟩

theorem OrecM_lt_δ {l : Ordinal.{0}} (hl : IsRestartIdx l) : OrecM l < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have h1 : upsilon l < upsilon (l + ω) :=
    upsilon_normal.strictMono (lt_add_of_pos_right l omega0_pos)
  have h2 : upsilon (l + ω) < upsilon (l + ω + 1) := upsilon_normal.strictMono (lt_add_one _)
  have hτE : InE (upsilon (l + ω)) := upsPt_inE (upsPt_upsilon (lt_of_lt_of_le hl0 le_self_add))
  have hδE : InE (upsilon (l + ω + 1)) :=
    upsPt_inE (upsPt_upsilon (lt_of_lt_of_le hl0 (le_self_add.trans le_self_add)))
  have he : eN (upsilon l) < upsilon (l + ω + 1) := lt_of_le_of_lt (eN_le h1 hτE) h2
  have hE := eN_E (upsilon l)
  have hw : eN (upsilon l) * ω = ω ^ (eN (upsilon l) + 1) := by
    rw [opow_add, opow_one]
    have : ω ^ eN (upsilon l) = eN (upsilon l) := hE
    rw [this]
  have hδlim : eN (upsilon l) + 1 < upsilon (l + ω + 1) :=
    (inE_indec hδE).add_lt he (lt_of_lt_of_le one_lt_omega0 (by
      have : ω ^ (1 : Ordinal.{0}) ≤ ω ^ upsilon (l + ω + 1) :=
        opow_le_opow_right omega0_pos (one_le_iff_pos.2 hδE.pos)
      rwa [opow_one, hδE] at this))
  refine lt_of_le_of_lt (OrecM_le l) ?_
  rw [hw]
  have := (opow_lt_opow_iff_right one_lt_omega0).2 hδlim
  rwa [hδE] at this

/-- **`OrecM` is a general offset specification up to `B`** when no restart index below `B` has
`ε_{x+1}·j` realized cofinally for every `j`. -/
theorem specM {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1)
    (hB : ∀ l, IsRestartIdx l → l < B → ¬ CofEw OrecM l) : OffSpecGen OrecM B where
  mult := hm
  cnt := hc
  le := fun _ hl _ => OrecM_lt_δ hl
  one := fun l _ _ => one_le_OrecM l
  top := fun l hl hlB => topIn_OrecM hl (hB l hl hlB)
  succ := fun _ hl _ h2 => OrecM_succ hl h2
  rs := fun _ hl _ h2 => rsIn_OrecM hl h2

theorem specM_of_le {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamEw) :
    OffSpecGen OrecM B :=
  specM hm hc (fun _ hl hlB => not_cofEw_of_lt hl (lt_of_lt_of_le hlB hB))

/-! ## Theorem BLK^O up to `Λ_{ε·ω}` -/

/-- **Theorem BLK^O with `OrecM` below `υ_B` for every `B ≤ Λ_{ε·ω}`** (`ω² ∣ B`, `B < Ω₁`) in
`R₂^C`: (i) the `<₂`-pairs with right end below `υ_B` are the standard pairs; (ii) every restart
`ρ_λ` (`λ < B`) has no `<₁`-predecessor, no `<₂`-successor, and reach `δ_λ + OrecM(λ)`; (iii) every
point below `υ_B` that is not a `υ`-point has its `R₁⁺` reach. -/
theorem blkM {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamEw) :
    (∀ c d, c < d → d < upsilon B → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < B ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < B →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + OrecM l)) ∧
    (∀ α < upsilon B, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  blk_genGen (specM_of_le hm hc hB)

/-- **CORE-C up to `Λ_{ε·ω}`**: `[0, υ_B) ⊆ Core(R₂^C)` for every `B ≤ Λ_{ε·ω}`. -/
theorem coreM {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamEw) :
    Set.Iio (upsilon B) ⊆ Core R2C :=
  core_genGen (specM_of_le hm hc hB)

/-- **`Λ_{ε·ω} < Ω₁`** (the core is countable, [C09] Cor 15.15). -/
theorem LamEw_lt_Om1 : LamEw < Om1 := by
  rcases LamEw_le_Om1.lt_or_eq with h | h
  · exact h
  · exfalso
    exact not_core_all (fun B hm hc => coreM hm hc (by rw [h]; exact hc.le))

/-- **The exact reach of every restart below `Λ_{ε·ω}`** in `R₂^C`: `lh(ρ_λ) = δ_λ + OrecM(λ)`. -/
theorem reach_OrecM {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlE : l < LamEw) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + OrecM l) := by
  obtain ⟨hl2, -⟩ := LamEw_spec LamEw_lt_Om1
  exact (blkM (ri_iff.1 hl2).2 LamEw_lt_Om1 le_rfl).2.1 l hl hlE |>.2.2

theorem coreM_LamEw : Set.Iio (upsilon LamEw) ⊆ Core R2C :=
  coreM (ri_iff.1 (LamEw_spec LamEw_lt_Om1).1).2 LamEw_lt_Om1 le_rfl

/-- **`Λ_{ε·2} < Λ_{ε·ω}`**. -/
theorem LamE2_lt_LamEw : LamE2 < LamEw := by
  obtain ⟨hl, hc⟩ := LamEw_spec LamEw_lt_Om1
  by_contra hle
  push Not at hle
  obtain ⟨μ, hμ, -, hμl, h4⟩ := hc 3 0 (pos_iff_ne_zero.2 hl.1)
  have hμE : μ < LamE2 := lt_of_lt_of_le hμl hle
  rw [OrecM_eq_OrecE μ hμ hμE] at h4
  have h5 := h4.trans (OrecS_le SF μ)
  have hpos := (eN_E (upsilon μ)).pos
  have e3 : eN (upsilon μ) * ((3 : ℕ) : Ordinal.{0}) =
      eN (upsilon μ) + eN (upsilon μ) + eN (upsilon μ) := by
    rw [show ((3 : ℕ) : Ordinal.{0}) = 1 + 1 + 1 by norm_num, mul_add_one, mul_add_one, mul_one]
  rw [e3] at h5
  exact absurd (h5.trans_lt (lt_add_of_pos_right _ hpos)) (lt_irrefl _)

theorem LamE_lt_LamEw : LamE < LamEw := LamE_lt_LamE2.trans LamE2_lt_LamEw

/-- **The reach at `Λ_{ε·2}`**: `lh(ρ_{Λ_{ε·2}}) = δ + ε_{ρ+1}·2 + 1` (`ρ = ρ_{Λ_{ε·2}}`). -/
theorem reach_LamE2 :
    IsReach R2C (upsilon LamE2)
      (upsilon (LamE2 + ω + 1) + (eN (upsilon LamE2) + eN (upsilon LamE2) + 1)) := by
  rw [← OrecM_LamE2]
  exact reach_OrecM (LamE2_spec LamE2_lt_Om1).1 LamE2_lt_LamEw

/-- **`OrecM(Λ_{ε·ω}) = ε_{ρ+1}·ω`** (`ρ = ρ_{Λ_{ε·ω}}`): at `Λ_{ε·ω}` the value is the atom
`ω^{ε_{ρ+1}+1}`, which is not a term of `OTM`. -/
theorem OrecM_LamEw : OrecM LamEw = eN (upsilon LamEw) * ω := by
  obtain ⟨hl, hc⟩ := LamEw_spec LamEw_lt_Om1
  have hl0 : 0 < LamEw := pos_iff_ne_zero.2 hl.1
  have hρ0 : 0 < upsilon LamEw := (upsPt_upsilon hl0).1
  set e := eN (upsilon LamEw) with he
  have he0 : e ≠ 0 := (eN_E _).pos.ne'
  refine le_antisymm (OrecM_le _) ?_
  by_contra hlt
  push Not at hlt
  obtain ⟨n, hn⟩ := lt_omega0.1 ((lt_mul_iff_div_lt he0).1 hlt)
  have h1 : OrecM LamEw < e * nS n := by
    have := lt_mul_succ_div (OrecM LamEw) he0
    rwa [hn, succ_eq_add_one, show ((n : Ordinal.{0}) + 1) = nS n by simp [nS]] at this
  have hcof : CofRealM OrecM LamEw (tmE n (k 0)) := by
    intro ν hν
    obtain ⟨μ, hμ, h2, h3, h4⟩ := hc (n + 1) ν hν
    refine ⟨μ, hμ, h2, h3, (upsPt_upsilon (pos_iff_ne_zero.2 hμ.1)).1, ?_⟩
    show eN _ * nS n + ev (k 0) _ ≤ _
    rw [ev_k, add_zero]; exact h4
  have h2 := lt_OrecM_of_cof (show CBM (tmE n (k 0)) (upsilon LamEw) from hρ0) hcof
  have : evM (tmE n (k 0)) (upsilon LamEw) = e * nS n := by
    show eN _ * nS n + ev (k 0) _ = _
    rw [ev_k, add_zero]
  rw [this] at h2
  exact absurd (h1.trans h2) (lt_irrefl _)

end Googology.Trans.PoR.InaccPsi.R2
