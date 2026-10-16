import Googology.Trans.PoR.InaccPsi.R2.EpsE
import Googology.Trans.PoR.InaccPsi.R2.LamLt

/-!
# The recursive offset with the term `ε_{x+1}`, and Theorem BLK^O past `Λ_ε`

The project's recursive offset (its paper's Definition 2.2) over a set `S` of offset terms
(`OTE`: the terms `t` of `OT`, and the terms `ε_{x+1} + t`, `t` in `OT`):
`O_S(λ) = sup ({1} ∪ {u(ρ_λ) + 1 : u ∈ S realized cofinally below λ, constants below ρ_λ})`.

* `S = SD` (the terms of `OT` and the single term `ε_{x+1} = ε_{x+1} + 0`): the paper's `O` (up to the
  `1` added at successor indices and the form `ω^{x+t}` of the exponentials, as for `Orec`).
* `S = SF` (all of `OTE`): every Cantor normal form in `x` below `ε_{x+1}·2`; `OrecE = O_SF`.

Results (all for restart indices, all countable):

* `OrecS_le` (`O_S(λ) ≤ ε_{ρ+1}·2`), `OrecS_succ` (`O_S = 1` at successor restart indices);
* `OrecE_eq_Orec` (`OrecE = Orec` below `Λ_ε`), `OrecE_LamE` (`OrecE(Λ_ε) = ε_{ρ+1} + 1`, the value of
  the paper's `O` at `Λ_ε`);
* `LamE1`, `LamE2`: the least restart indices below which `ε_{x+1} + 1`, resp. `ε_{x+1}·2`, is realized
  cofinally by `OrecE`; `LamE_lt_LamE1`, `LamE1_lt_LamE2`, `LamE2_lt_Om1`;
* `topIn_OrecE`, `rsIn_OrecE`, `OffSpecE`, `blkE` (**Theorem BLK^O with `OrecE` for every `B ≤ Λ_{ε·2}`**,
  `ω² ∣ B`, `B < Ω₁`), `reach_OrecE` (`lh(ρ_λ) = δ_λ + OrecE(λ)` for every restart index `λ < Λ_{ε·2}`),
  `coreE` (`[0, υ_B) ⊆ Core(R₂^C)`), `reach_LamE` (`lh(ρ_{Λ_ε}) = δ + ε_{ρ+1} + 1`);
* `OrecD_eq_OrecE` (the paper's `O` equals `OrecE` below `Λ_{ε+1}`), `OrecD_LamE1`,
  `OrecE_LamE1`, `reach_LamE1` (at `Λ_{ε+1}` the paper's `O` is `ε_{ρ+1} + 1`, while
  `lh(ρ) = δ + OrecE(Λ_{ε+1}) ≥ δ + ε_{ρ+1} + 2`: the paper's `O` is the reach exactly below `Λ_{ε+1}`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order OT

/-! ## Terms with `ε_{x+1}` -/

/-- Offset terms with `ε_{x+1}`: a term `t` of `OT`, or `ε_{x+1} + t`. -/
inductive OTE : Type 1
  | ot : OT → OTE
  | e : OT → OTE

open OTE

/-- The value of a term at `x`. -/
noncomputable def evE : OTE → Ordinal.{0} → Ordinal.{0}
  | ot t, x => ev t x
  | e t, x => eN x + ev t x

/-- All constants below `s`. -/
def CBE : OTE → Ordinal.{0} → Prop
  | ot t, s => CB t s
  | e t, s => CB t s

@[simp] theorem evE_ot (t : OT) (x : Ordinal.{0}) : evE (ot t) x = ev t x := rfl
@[simp] theorem evE_e (t : OT) (x : Ordinal.{0}) : evE (e t) x = eN x + ev t x := rfl
@[simp] theorem CBE_ot (t : OT) (s : Ordinal.{0}) : CBE (ot t) s = CB t s := rfl
@[simp] theorem CBE_e (t : OT) (s : Ordinal.{0}) : CBE (e t) s = CB t s := rfl

theorem evE_lt {u : OTE} {x : Ordinal.{0}} (h : CBE u x) : evE u x < eN x + eN x := by
  cases u with
  | ot t => exact lt_of_lt_of_le (ev_lt_eN h) le_self_add
  | e t => exact (add_lt_add_iff_left _).2 (ev_lt_eN h)

/-- The full set of terms. -/
def SF : OTE → Prop := fun _ => True

/-- The paper's terms: those of `OT` and `ε_{x+1}` (`= ε_{x+1} + 0`). -/
def SD : OTE → Prop
  | ot _ => True
  | e t => t = k 0

/-! ## The recursion over a set of terms -/

/-- `u` is realized cofinally below `λ` by the offsets `O`. -/
def CofRealE (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) (u : OTE) : Prop :=
  ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ CBE u (upsilon μ) ∧ evE u (upsilon μ) ≤ O μ

/-- The set whose supremum is `O_S(λ)`. -/
def OSetS (S : OTE → Prop) (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Set Ordinal.{0} :=
  insert 1 {w | ∃ u, S u ∧ CBE u (upsilon l) ∧ CofRealE O l u ∧ w = evE u (upsilon l) + 1}

theorem OSetS_congr {S : OTE → Prop} {O O' : Ordinal.{0} → Ordinal.{0}} {l : Ordinal.{0}}
    (h : ∀ μ < l, O μ = O' μ) : OSetS S O l = OSetS S O' l := by
  have key : ∀ u, CofRealE O l u ↔ CofRealE O' l u := by
    intro u
    constructor
    · intro hc ν hν
      obtain ⟨μ, h1, h2, h3, h4, h5⟩ := hc ν hν
      exact ⟨μ, h1, h2, h3, h4, by rw [← h μ h3]; exact h5⟩
    · intro hc ν hν
      obtain ⟨μ, h1, h2, h3, h4, h5⟩ := hc ν hν
      exact ⟨μ, h1, h2, h3, h4, by rw [h μ h3]; exact h5⟩
  ext w
  simp only [OSetS, Set.mem_insert_iff, Set.mem_setOf_eq, key]

/-- **The recursive offset over `S`**, by well-founded recursion. -/
noncomputable def OrecS (S : OTE → Prop) : Ordinal.{0} → Ordinal.{0} :=
  Ordinal.lt_wf.fix (fun l IH => sSup (OSetS S (fun μ => if h : μ < l then IH μ h else 0) l))

theorem OrecS_eq (S : OTE → Prop) (l : Ordinal.{0}) : OrecS S l = sSup (OSetS S (OrecS S) l) := by
  show Ordinal.lt_wf.fix _ l = _
  rw [WellFounded.fix_eq]
  rw [OSetS_congr (O' := OrecS S) (fun μ hμ => by simp only [hμ, dite_true]; rfl)]

/-- `OrecE = O_SF`. -/
noncomputable def OrecE : Ordinal.{0} → Ordinal.{0} := OrecS SF

/-- The paper's `O` (with `1` added): `O_SD`. -/
noncomputable def OrecD : Ordinal.{0} → Ordinal.{0} := OrecS SD

theorem OSetS_bdd (S : OTE → Prop) (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) :
    ∀ w ∈ OSetS S O l, w ≤ eN (upsilon l) + eN (upsilon l) := by
  intro w hw
  rcases hw with rfl | ⟨u, -, hCB, -, rfl⟩
  · exact one_le_iff_pos.2 (lt_of_lt_of_le (eN_E _).pos le_self_add)
  · exact add_one_le_of_lt (evE_lt hCB)

theorem OSetS_bddAbove (S : OTE → Prop) (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) :
    BddAbove (OSetS S O l) := ⟨_, OSetS_bdd S O l⟩

/-- `O_S(λ) ≤ ε_{ρ_λ+1}·2`. -/
theorem OrecS_le (S : OTE → Prop) (l : Ordinal.{0}) :
    OrecS S l ≤ eN (upsilon l) + eN (upsilon l) := by
  rw [OrecS_eq]; exact csSup_le ⟨1, Set.mem_insert _ _⟩ (OSetS_bdd S _ l)

theorem one_le_OrecS (S : OTE → Prop) (l : Ordinal.{0}) : 1 ≤ OrecS S l := by
  rw [OrecS_eq]; exact le_csSup (OSetS_bddAbove S _ l) (Set.mem_insert _ _)

theorem lt_OrecS_of_cof {S : OTE → Prop} {l : Ordinal.{0}} {u : OTE} (hS : S u)
    (hCB : CBE u (upsilon l)) (hc : CofRealE (OrecS S) l u) : evE u (upsilon l) < OrecS S l := by
  have h1 : evE u (upsilon l) + 1 ≤ OrecS S l := by
    rw [OrecS_eq]
    exact le_csSup (OSetS_bddAbove S _ l) (Set.mem_insert_of_mem _ ⟨u, hS, hCB, hc, rfl⟩)
  exact lt_of_lt_of_le (lt_add_one _) h1

theorem lt_OrecS {S : OTE → Prop} {l z : Ordinal.{0}} (hz : z < OrecS S l) :
    z = 0 ∨ ∃ u, S u ∧ CBE u (upsilon l) ∧ CofRealE (OrecS S) l u ∧ z ≤ evE u (upsilon l) := by
  rw [OrecS_eq] at hz
  obtain ⟨w, hw, hzw⟩ := (lt_csSup_iff (OSetS_bddAbove S _ l) ⟨1, Set.mem_insert _ _⟩).1 hz
  rcases hw with rfl | ⟨u, hS, hCB, hc, rfl⟩
  · left; exact le_antisymm (Order.lt_add_one_iff.1 (by rw [zero_add]; exact hzw)) zero_le
  · right; exact ⟨u, hS, hCB, hc, Order.lt_add_one_iff.1 hzw⟩

/-- `O_S = 1` at a successor restart index. -/
theorem OrecS_succ (S : OTE → Prop) {l : Ordinal.{0}} (hl : IsRestartIdx l) (h2 : cL l < 2) :
    OrecS S l = 1 := by
  obtain ⟨l0, hl0, rfl⟩ := succ_ri hl h2
  have hww : 0 < ω * ω := mul_pos omega0_pos omega0_pos
  have hS : OSetS S (OrecS S) (l0 + ω * ω) = {1} := by
    ext w
    simp only [OSetS, Set.mem_insert_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro (h | ⟨u, -, -, hc, -⟩)
      · exact h
      · exfalso
        obtain ⟨μ, hμ, h1, h3, -, -⟩ := hc l0 (lt_add_of_pos_right l0 hww)
        exact absurd h3 (not_lt.2 (next_mult (mult_of hl0) (ri_iff.1 hμ).2 h1))
    · intro h; exact Or.inl h
  rw [OrecS_eq, hS, csSup_singleton]

/-! ## Uniformity of the value `≥ 1` -/

theorem one_lt_inE {s : Ordinal.{0}} (hs : InE s) : 1 < s := by
  have hsE : ω ^ s = s := hs
  have : ω ^ (1 : Ordinal.{0}) ≤ ω ^ s := opow_le_opow_right omega0_pos (one_le_iff_pos.2 hs.pos)
  rw [opow_one, hsE] at this
  exact lt_of_lt_of_le one_lt_omega0 this

/-- For `ε`-numbers `s < r < Ω₁` and a term `t` with constants below `s`: `1 ≤ t(r) ↔ 1 ≤ t(s)`. -/
theorem uni_one {s r : Ordinal.{0}} (hB : Bases s r) {t : OT} (ht : CB t s) :
    1 ≤ ev t r ↔ 1 ≤ ev t s := by
  exact uni_le hB (t := k 1) (one_lt_inE hB.1) ht

/-! ## `OrecE` below and at `Λ_ε` -/

/-- **`OrecE = Orec` below `Λ_ε`** (at every restart index): below `Λ_ε` no term `ε_{x+1} + t` is
realized cofinally. -/
theorem OrecE_eq_Orec : ∀ l, IsRestartIdx l → l < LamE → OrecE l = Orec l := by
  intro l
  induction l using WellFoundedLT.induction with
  | ind l IH =>
  intro hl hlE
  have key : ∀ μ, IsRestartIdx μ → μ < l → OrecE μ = Orec μ := fun μ hμ hμl =>
    IH μ hμl hμ (hμl.trans hlE)
  have hS : OSetS SF OrecE l = OSet Orec l := by
    ext w
    simp only [OSetS, OSet, Set.mem_insert_iff, Set.mem_setOf_eq]
    constructor
    · rintro (h | ⟨u, -, hCB, hc, rfl⟩)
      · exact Or.inl h
      cases u with
      | ot t =>
        refine Or.inr ⟨t, hCB, fun ν hν => ?_, rfl⟩
        obtain ⟨μ, hμ, h1, h2, h3, h4⟩ := hc ν hν
        exact ⟨μ, hμ, h1, h2, h3, by rw [← key μ hμ h2]; exact h4⟩
      | e t =>
        exfalso
        refine not_cofE_of_lt hl hlE (fun ν hν => ?_)
        obtain ⟨μ, hμ, h1, h2, -, h4⟩ := hc ν hν
        exact ⟨μ, hμ, h1, h2, by rw [← key μ hμ h2]; exact le_self_add.trans h4⟩
    · rintro (h | ⟨t, hCB, hc, rfl⟩)
      · exact Or.inl h
      · refine Or.inr ⟨ot t, trivial, hCB, fun ν hν => ?_, rfl⟩
        obtain ⟨μ, hμ, h1, h2, h3, h4⟩ := hc ν hν
        exact ⟨μ, hμ, h1, h2, h3, by rw [key μ hμ h2]; exact h4⟩
  show OrecS SF l = Orec l
  rw [OrecS_eq, Orec_eq]
  unfold Ostep
  rw [← hS]; rfl

theorem Bases_ups {μ l : Ordinal.{0}} (hμ0 : 0 < μ) (hμl : μ < l) (hl1 : l < Om1) :
    Bases (upsilon μ) (upsilon l) :=
  ⟨upsPt_inE (upsPt_upsilon hμ0), upsPt_inE (upsPt_upsilon (hμ0.trans hμl)),
    upsilon_normal.strictMono hμl, ups_lt_Om1 l hl1⟩

/-- **`OrecE(Λ_ε) = ε_{ρ+1} + 1`** (`ρ = ρ_{Λ_ε}`), the value of the paper's `O` at `Λ_ε`. -/
theorem OrecE_LamE : OrecE LamE = eN (upsilon LamE) + 1 := by
  obtain ⟨hl, hcof⟩ := LamE_spec
  have hl0 : 0 < LamE := pos_iff_ne_zero.2 hl.1
  have hρ0 : 0 < upsilon LamE := (upsPt_upsilon hl0).1
  apply le_antisymm
  · show OrecS SF LamE ≤ _
    rw [OrecS_eq]
    refine csSup_le ⟨1, Set.mem_insert _ _⟩ ?_
    rintro w (rfl | ⟨u, -, hCB, hc, rfl⟩)
    · exact le_add_self
    cases u with
    | ot t => exact (add_one_le_of_lt (ev_lt_eN hCB)).trans le_self_add
    | e t =>
      have ht0 : ev t (upsilon LamE) = 0 := by
        by_contra hne
        have h1 : 1 ≤ ev t (upsilon LamE) := one_le_iff_ne_zero.2 hne
        obtain ⟨μ, hμ, -, h2, h3, h4⟩ := hc 0 hl0
        have hμ0 : 0 < μ := pos_iff_ne_zero.2 hμ.1
        have h1μ := (uni_one (Bases_ups hμ0 h2 LamE_lt_Om1) h3).1 h1
        rw [evE_e, show OrecS SF μ = Orec μ from OrecE_eq_Orec μ hμ h2] at h4
        have h5 := h4.trans (Orec_le_eN μ)
        have : eN (upsilon μ) + 1 ≤ eN (upsilon μ) + 0 := by
          rw [add_zero]; exact (add_le_add le_rfl h1μ).trans h5
        exact absurd ((add_le_add_iff_left _).1 this) (by simp)
      simp only [evE_e, ht0, add_zero]; exact le_rfl
  · show OrecS SF LamE ≥ _
    have hc : CofRealE (OrecS SF) LamE (e (k 0)) := by
      intro ν hν
      obtain ⟨μ, hμ, h1, h2, h3⟩ := hcof ν hν
      refine ⟨μ, hμ, h1, h2, (upsPt_upsilon (pos_iff_ne_zero.2 hμ.1)).1, ?_⟩
      show eN (upsilon μ) + 0 ≤ OrecE μ
      rw [add_zero, OrecE_eq_Orec μ hμ h2]; exact h3
    have := lt_OrecS_of_cof (S := SF) trivial (show CBE (e (k 0)) (upsilon LamE) from hρ0) hc
    simp only [evE_e, ev_k, add_zero] at this
    exact add_one_le_of_lt this

/-! ## The frontiers `Λ_{ε+1}` and `Λ_{ε·2}` -/

/-- `ε_{x+1} + 1` is realized cofinally below `λ`. -/
def CofE1 (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Prop :=
  ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ eN (upsilon μ) + 1 ≤ O μ

/-- `ε_{x+1}·2` is realized cofinally below `λ`. -/
def CofE2 (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Prop :=
  ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ eN (upsilon μ) + eN (upsilon μ) ≤ O μ

/-- `Λ_{ε+1}`: the least restart index below which `ε_{x+1} + 1` is realized cofinally by `OrecE`
(`Ω₁` if there is none). -/
noncomputable def LamE1 : Ordinal.{0} := sInf (insert Om1 {l | IsRestartIdx l ∧ CofE1 OrecE l})

/-- `Λ_{ε·2}`: the least restart index below which `ε_{x+1}·2` is realized cofinally by `OrecE`
(`Ω₁` if there is none). -/
noncomputable def LamE2 : Ordinal.{0} := sInf (insert Om1 {l | IsRestartIdx l ∧ CofE2 OrecE l})

theorem LamE1_le_Om1 : LamE1 ≤ Om1 := csInf_le (OrderBot.bddBelow _) (Set.mem_insert _ _)
theorem LamE2_le_Om1 : LamE2 ≤ Om1 := csInf_le (OrderBot.bddBelow _) (Set.mem_insert _ _)

theorem not_cofE1_of_lt {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlE : l < LamE1) :
    ¬ CofE1 OrecE l := fun h =>
  absurd (csInf_le (OrderBot.bddBelow _) (Set.mem_insert_of_mem _
    (show l ∈ {l | IsRestartIdx l ∧ CofE1 OrecE l} from ⟨hl, h⟩))) (not_le.2 hlE)

theorem not_cofE2_of_lt {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlE : l < LamE2) :
    ¬ CofE2 OrecE l := fun h =>
  absurd (csInf_le (OrderBot.bddBelow _) (Set.mem_insert_of_mem _
    (show l ∈ {l | IsRestartIdx l ∧ CofE2 OrecE l} from ⟨hl, h⟩))) (not_le.2 hlE)

theorem LamE1_spec (h : LamE1 < Om1) : IsRestartIdx LamE1 ∧ CofE1 OrecE LamE1 := by
  rcases csInf_mem (s := insert Om1 {l | IsRestartIdx l ∧ CofE1 OrecE l})
    ⟨Om1, Set.mem_insert _ _⟩ with h' | h'
  · exact absurd (h' ▸ h : Om1 < Om1) (lt_irrefl _)
  · exact h'

theorem LamE2_spec (h : LamE2 < Om1) : IsRestartIdx LamE2 ∧ CofE2 OrecE LamE2 := by
  rcases csInf_mem (s := insert Om1 {l | IsRestartIdx l ∧ CofE2 OrecE l})
    ⟨Om1, Set.mem_insert _ _⟩ with h' | h'
  · exact absurd (h' ▸ h : Om1 < Om1) (lt_irrefl _)
  · exact h'

/-- **`Λ_ε < Λ_{ε+1}`**: at and below `Λ_ε` no restart realizes `ε_{x+1} + 1`. -/
theorem LamE_lt_LamE1 : LamE < LamE1 := by
  by_contra hle
  push Not at hle
  rcases LamE1_le_Om1.lt_or_eq with h1 | h1
  · obtain ⟨hl, hc⟩ := LamE1_spec h1
    obtain ⟨μ, hμ, -, hμl, h4⟩ := hc 0 (pos_iff_ne_zero.2 hl.1)
    have hμE : μ < LamE := lt_of_lt_of_le hμl hle
    rw [OrecE_eq_Orec μ hμ hμE] at h4
    exact absurd (h4.trans (Orec_le_eN μ)) (not_le.2 (lt_add_one _))
  · rw [h1] at hle; exact absurd LamE_lt_Om1 (not_lt.2 hle)

/-- At a restart index `μ < Ω₁` with `ε_{ρ_μ+1}·2 ≤ OrecE(μ)`, the term `ε_{x+1} + 1` is realized
cofinally below `μ`. -/
theorem cofE1_of_two {μ : Ordinal.{0}} (hμ1 : μ < Om1)
    (h : eN (upsilon μ) + eN (upsilon μ) ≤ OrecE μ) : CofE1 OrecE μ := by
  have hlt : eN (upsilon μ) + 1 < OrecE μ :=
    lt_of_lt_of_le ((add_lt_add_iff_left _).2 (one_lt_inE (eN_E _))) h
  rcases lt_OrecS (S := SF) hlt with h0 | ⟨u, -, hCB, hc, hz⟩
  · exact absurd h0 (ne_of_gt (lt_of_lt_of_le (eN_E _).pos le_self_add))
  cases u with
  | ot t =>
    exact absurd (lt_of_le_of_lt (le_self_add.trans hz) (ev_lt_eN hCB)) (lt_irrefl _)
  | e t =>
    have h1 : 1 ≤ ev t (upsilon μ) := (add_le_add_iff_left _).1 hz
    intro ν hν
    obtain ⟨μ', hμ', h2, h3, h4, h5⟩ := hc ν hν
    have hμ'0 : 0 < μ' := pos_iff_ne_zero.2 hμ'.1
    have h1' := (uni_one (Bases_ups hμ'0 h3 hμ1) h4).1 h1
    exact ⟨μ', hμ', h2, h3, (add_le_add le_rfl h1').trans h5⟩

end Googology.Trans.PoR.InaccPsi.R2
