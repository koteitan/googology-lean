import Googology.Trans.PoR.InaccPsi.R2.EpsQ
import Googology.Trans.PoR.InaccPsi.R2.LamVal

/-!
# The recursive offset with the terms `ε_{x+1}·q + t`, and Theorem BLK^O at `Λ_{ε·ω}` and up to `Λ_{ε·x}`

The project's recursive offset (its paper's Definition 2.2) over the terms `OTQ`: a term `t` of `OT`, or
`ε_{x+1}·q + t` with a constant `0 < q` below the base (`t` in `OT`); so every Cantor normal form in `x`
below `ε_{x+1}·x = ω^{ε_{x+1}+x}`.  `OrecQ(λ) = sup ({1} ∪ {u(ρ_λ) + 1 : u realized cofinally below λ,
constants below ρ_λ})`.  Stage 8 (`OTM`, `OrecM`) had `q < ω`.

* `OrecQ_le` (`OrecQ(λ) ≤ ε_{ρ+1}·ρ` at a restart index), `OrecQ_succ` (`= 1` at successor restart
  indices);
* `OrecQ_eq_OrecM` (**`OrecQ = OrecM` at every restart index `λ ≤ Λ_{ε·ω}`**: below `Λ_{ε·ω}` no term
  `ε_{x+1}·q + t` with `q ≥ ω` is realized cofinally), `OrecQ_LamEw` (`OrecQ(Λ_{ε·ω}) = ε_{ρ+1}·ω`);
* `CofQ`, `LamQ` (`Λ_{ε·x}`: the least restart index `λ` below which `ε_{x+1}·q` is realized cofinally
  for every constant `0 < q < ρ_λ`), `OrecQ_lt_top` (below `Λ_{ε·x}` the value is `< ε_{ρ+1}·ρ`),
  `LamEw_lt_LamQ`;
* `topIn_OrecQ` (the input of Lemma TOP: the value `ε_{ρ+1}·q + v` is a term not realized cofinally,
  with the IMG packages `RstK.pkg_ot`, `RstK.pkg_eQ`, `RstK.pkg_eQt`), `rsIn_OrecQ` (the input of
  Lemma RS, with `rs_rstT` and `rs_rstQ`), `specQ`;
* `blkQ` (**Theorem BLK^O with `OrecQ` below `υ_B` for every `B ≤ Λ_{ε·x}`**, `ω² ∣ B`, `B < Ω₁`),
  `coreQ`, `LamQ_lt_Om1` (`Λ_{ε·x} < Ω₁`, [C09] Cor 15.15), `reach_OrecQ` (`lh(ρ_λ) = δ_λ + OrecQ(λ)`
  for every restart index `λ < Λ_{ε·x}`);
* `reach_LamEw` (**the reach at `Λ_{ε·ω}`**: `lh(ρ) = δ + ε_{ρ+1}·ω`, `ρ = ρ_{Λ_{ε·ω}}`), `blk_LamEw`
  (BLK^O below `υ_{Λ_{ε·ω}+ω²}`, the block of the restart `ρ_{Λ_{ε·ω}}` included), `OrecQ_LamQ`
  (`OrecQ(Λ_{ε·x}) = ε_{ρ+1}·ρ = ω^{ε_{ρ+1}+ρ}`, `ρ = ρ_{Λ_{ε·x}}`; the atom has `x` in its exponent);
* `upsQ_le_nuC`, `left_ge_LamQ`, `nuC_boundQ` (**`υ_{Λ_{ε·x}} ≤ ρ_L < ν_C`**).

No new axiom.

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order OT

/-! ## `ε`-numbers -/

theorem ups_omega_lt {l : Ordinal.{0}} (hl0 : 0 < l) : ω < upsilon l :=
  omega0_lt_inE (upsPt_inE (upsPt_upsilon hl0))

/-- `ε·q ≤ ε·q' + v` with `v < ε` gives `q ≤ q'`. -/
theorem le_of_mul_le {e v q q' : Ordinal.{0}} (hv : v < e) (h : e * q ≤ e * q' + v) : q ≤ q' := by
  by_contra hlt
  push Not at hlt
  have h1 : e * (q' + 1) ≤ e * q := mul_le_mul_right (add_one_le_of_lt hlt) e
  have h2 : e * q' + v < e * (q' + 1) := by rw [mul_add_one]; exact (add_lt_add_iff_left _).2 hv
  exact absurd (h.trans_lt (h2.trans_le h1)) (lt_irrefl _)

/-! ## Terms below `ε_{x+1}·x` -/

/-- Offset terms below `ε_{x+1}·x`: a term `t` of `OT` (`tq0 t`), or `ε_{x+1}·q + t` with a constant `q`
(`tqE q t`). -/
inductive OTQ : Type 1
  | tq0 : OT → OTQ
  | tqE : Ordinal.{0} → OT → OTQ

open OTQ

/-- The value of a term at `x`. -/
noncomputable def evQ : OTQ → Ordinal.{0} → Ordinal.{0}
  | tq0 t, x => ev t x
  | tqE q t, x => eN x * q + ev t x

/-- All constants below `s` (and the multiplier `q` positive). -/
def CBQ : OTQ → Ordinal.{0} → Prop
  | tq0 t, s => CB t s
  | tqE q t, s => 0 < q ∧ q < s ∧ CB t s

theorem evQ_lt_add {u : OTQ} {x : Ordinal.{0}} (h : CBQ u x) : evQ u x < eN x * x + eN x := by
  cases u with
  | tq0 t => exact lt_of_lt_of_le (ev_lt_eN h) le_add_self
  | tqE q t =>
    obtain ⟨-, hqx, ht⟩ := h
    calc eN x * q + ev t x < eN x * q + eN x := (add_lt_add_iff_left _).2 (ev_lt_eN ht)
      _ ≤ eN x * x + eN x := add_le_add (mul_le_mul_right hqx.le _) le_rfl

theorem evQ_lt {u : OTQ} {x : Ordinal.{0}} (hx : InE x) (h : CBQ u x) : evQ u x < eN x * x := by
  cases u with
  | tq0 t => exact lt_of_lt_of_le (ev_lt_eN h) (le_mul_pos _ hx.pos)
  | tqE q t =>
    obtain ⟨-, hqx, ht⟩ := h
    have hq1 : q + 1 ≤ x :=
      ((inE_indec hx).add_lt hqx (one_lt_omega0.trans (omega0_lt_inE hx))).le
    calc eN x * q + ev t x < eN x * q + eN x := (add_lt_add_iff_left _).2 (ev_lt_eN ht)
      _ = eN x * (q + 1) := (mul_add_one _ _).symm
      _ ≤ eN x * x := mul_le_mul_right hq1 _

/-! ## The recursion -/

/-- `u` is realized cofinally below `λ` by the offsets `O`. -/
def CofRealQ (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) (u : OTQ) : Prop :=
  ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ CBQ u (upsilon μ) ∧ evQ u (upsilon μ) ≤ O μ

/-- The set whose supremum is `OrecQ(λ)`. -/
def OSetQ (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Set Ordinal.{0} :=
  insert 1 {w | ∃ u, CBQ u (upsilon l) ∧ CofRealQ O l u ∧ w = evQ u (upsilon l) + 1}

theorem OSetQ_congr {O O' : Ordinal.{0} → Ordinal.{0}} {l : Ordinal.{0}}
    (h : ∀ μ < l, O μ = O' μ) : OSetQ O l = OSetQ O' l := by
  have key : ∀ u, CofRealQ O l u ↔ CofRealQ O' l u := by
    intro u
    constructor
    · intro hc ν hν
      obtain ⟨μ, h1, h2, h3, h4, h5⟩ := hc ν hν
      exact ⟨μ, h1, h2, h3, h4, by rw [← h μ h3]; exact h5⟩
    · intro hc ν hν
      obtain ⟨μ, h1, h2, h3, h4, h5⟩ := hc ν hν
      exact ⟨μ, h1, h2, h3, h4, by rw [h μ h3]; exact h5⟩
  ext w
  simp only [OSetQ, Set.mem_insert_iff, Set.mem_setOf_eq, key]

/-- **The recursive offset over `OTQ`**, by well-founded recursion. -/
noncomputable def OrecQ : Ordinal.{0} → Ordinal.{0} :=
  Ordinal.lt_wf.fix (fun l IH => sSup (OSetQ (fun μ => if h : μ < l then IH μ h else 0) l))

theorem OrecQ_eq (l : Ordinal.{0}) : OrecQ l = sSup (OSetQ OrecQ l) := by
  show Ordinal.lt_wf.fix _ l = _
  rw [WellFounded.fix_eq]
  rw [OSetQ_congr (O' := OrecQ) (fun μ hμ => by simp only [hμ, dite_true]; rfl)]

theorem OSetQ_bdd (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) :
    ∀ w ∈ OSetQ O l, w ≤ eN (upsilon l) * upsilon l + eN (upsilon l) := by
  intro w hw
  rcases hw with rfl | ⟨u, hCB, -, rfl⟩
  · exact one_le_iff_pos.2 (lt_of_lt_of_le (eN_E _).pos le_add_self)
  · exact add_one_le_of_lt (evQ_lt_add hCB)

theorem OSetQ_bddAbove (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) :
    BddAbove (OSetQ O l) := ⟨_, OSetQ_bdd O l⟩

/-- `OrecQ(λ) ≤ ε_{ρ+1}·ρ` at a restart index (`ρ = ρ_λ`). -/
theorem OrecQ_le {l : Ordinal.{0}} (hl : IsRestartIdx l) :
    OrecQ l ≤ eN (upsilon l) * upsilon l := by
  have hρE : InE (upsilon l) := upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 hl.1))
  rw [OrecQ_eq]
  refine csSup_le ⟨1, Set.mem_insert _ _⟩ ?_
  rintro w (rfl | ⟨u, hCB, -, rfl⟩)
  · exact one_le_iff_pos.2 (mul_pos (eN_E _).pos hρE.pos)
  · exact add_one_le_of_lt (evQ_lt hρE hCB)

theorem one_le_OrecQ (l : Ordinal.{0}) : 1 ≤ OrecQ l := by
  rw [OrecQ_eq]; exact le_csSup (OSetQ_bddAbove _ l) (Set.mem_insert _ _)

theorem lt_OrecQ_of_cof {l : Ordinal.{0}} {u : OTQ} (hCB : CBQ u (upsilon l))
    (hc : CofRealQ OrecQ l u) : evQ u (upsilon l) < OrecQ l := by
  have h1 : evQ u (upsilon l) + 1 ≤ OrecQ l := by
    rw [OrecQ_eq]
    exact le_csSup (OSetQ_bddAbove _ l) (Set.mem_insert_of_mem _ ⟨u, hCB, hc, rfl⟩)
  exact lt_of_lt_of_le (lt_add_one _) h1

theorem lt_OrecQ {l z : Ordinal.{0}} (hz : z < OrecQ l) :
    z = 0 ∨ ∃ u, CBQ u (upsilon l) ∧ CofRealQ OrecQ l u ∧ z ≤ evQ u (upsilon l) := by
  rw [OrecQ_eq] at hz
  obtain ⟨w, hw, hzw⟩ := (lt_csSup_iff (OSetQ_bddAbove _ l) ⟨1, Set.mem_insert _ _⟩).1 hz
  rcases hw with rfl | ⟨u, hCB, hc, rfl⟩
  · left; exact le_antisymm (Order.lt_add_one_iff.1 (by rw [zero_add]; exact hzw)) zero_le
  · right; exact ⟨u, hCB, hc, Order.lt_add_one_iff.1 hzw⟩

/-- `OrecQ = 1` at a successor restart index. -/
theorem OrecQ_succ {l : Ordinal.{0}} (hl : IsRestartIdx l) (h2 : cL l < 2) : OrecQ l = 1 := by
  obtain ⟨l0, hl0, rfl⟩ := succ_ri hl h2
  have hww : 0 < ω * ω := mul_pos omega0_pos omega0_pos
  have hS : OSetQ OrecQ (l0 + ω * ω) = {1} := by
    ext w
    simp only [OSetQ, Set.mem_insert_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro (h | ⟨u, -, hc, -⟩)
      · exact h
      · exfalso
        obtain ⟨μ, hμ, h1, h3, -, -⟩ := hc l0 (lt_add_of_pos_right l0 hww)
        exact absurd h3 (not_lt.2 (next_mult (mult_of hl0) (ri_iff.1 hμ).2 h1))
    · intro h; exact Or.inl h
  rw [OrecQ_eq, hS, csSup_singleton]

/-! ## `OrecQ = OrecM` up to `Λ_{ε·ω}` -/

/-- At a restart index `λ ≤ Λ_{ε·ω}` the two recursions read the same terms, given equal values below. -/
theorem OSetQ_eq_M {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlE : l ≤ LamEw)
    (key : ∀ μ, IsRestartIdx μ → μ < l → OrecQ μ = OrecM μ) :
    OSetQ OrecQ l = OSetM OrecM l := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hωρ : ω < upsilon l := ups_omega_lt hl0
  ext w
  simp only [OSetQ, OSetM, Set.mem_insert_iff, Set.mem_setOf_eq]
  constructor
  · rintro (h | ⟨u, hCB, hc, rfl⟩)
    · exact Or.inl h
    cases u with
    | tq0 t =>
      refine Or.inr ⟨OTM.tm0 t, hCB, fun ν hν => ?_, rfl⟩
      obtain ⟨μ, hμ, h1, h2, h3, h4⟩ := hc ν hν
      exact ⟨μ, hμ, h1, h2, h3, by rw [← key μ hμ h2]; exact h4⟩
    | tqE q t =>
      obtain ⟨hq0, hqρ, ht⟩ := hCB
      rcases lt_or_ge q ω with hqω | hωq
      · obtain ⟨n, rfl⟩ := lt_omega0.1 hqω
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by
          have : 0 < n := by exact_mod_cast hq0
          omega⟩
        refine Or.inr ⟨OTM.tmE m t, ht, fun ν hν => ?_, rfl⟩
        obtain ⟨μ, hμ, h1, h2, h3, h4⟩ := hc ν hν
        exact ⟨μ, hμ, h1, h2, h3.2.2, by rw [← key μ hμ h2]; exact h4⟩
      · exfalso
        obtain ⟨μ, hμ, -, hμl, h3, h4⟩ := hc 0 hl0
        rw [key μ hμ hμl] at h4
        have h5 : eN (upsilon μ) * ω ≤ OrecM μ :=
          ((mul_le_mul_right hωq _).trans le_self_add).trans h4
        exact absurd h5 (not_le.2 (OrecM_lt_w (not_cofEw_of_lt hμ (lt_of_lt_of_le hμl hlE))))
  · rintro (h | ⟨u, hCB, hc, rfl⟩)
    · exact Or.inl h
    cases u with
    | tm0 t =>
      refine Or.inr ⟨tq0 t, hCB, fun ν hν => ?_, rfl⟩
      obtain ⟨μ, hμ, h1, h2, h3, h4⟩ := hc ν hν
      exact ⟨μ, hμ, h1, h2, h3, by rw [key μ hμ h2]; exact h4⟩
    | tmE m t =>
      refine Or.inr ⟨tqE (nS m) t, ⟨nS_pos m, (nS_lt_omega m).trans hωρ, hCB⟩, fun ν hν => ?_, rfl⟩
      obtain ⟨μ, hμ, h1, h2, h3, h4⟩ := hc ν hν
      have hωμ : ω < upsilon μ := ups_omega_lt (pos_iff_ne_zero.2 hμ.1)
      exact ⟨μ, hμ, h1, h2, ⟨nS_pos m, (nS_lt_omega m).trans hωμ, h3⟩,
        by rw [key μ hμ h2]; exact h4⟩

/-- **`OrecQ = OrecM` at every restart index `λ ≤ Λ_{ε·ω}`.** -/
theorem OrecQ_eq_OrecM : ∀ l, IsRestartIdx l → l ≤ LamEw → OrecQ l = OrecM l := by
  intro l
  induction l using WellFoundedLT.induction with
  | ind l IH =>
  intro hl hlE
  rw [OrecQ_eq, OrecM_eq,
    OSetQ_eq_M hl hlE (fun μ hμ hμl => IH μ hμl hμ (hμl.le.trans hlE))]

/-- **`OrecQ(Λ_{ε·ω}) = ε_{ρ+1}·ω`** (`ρ = ρ_{Λ_{ε·ω}}`). -/
theorem OrecQ_LamEw : OrecQ LamEw = eN (upsilon LamEw) * ω := by
  rw [OrecQ_eq_OrecM _ (LamEw_spec LamEw_lt_Om1).1 le_rfl, OrecM_LamEw]

/-! ## The frontier `Λ_{ε·x}` -/

/-- `ε_{x+1}·q` is realized cofinally below `λ` for every constant `0 < q < ρ_λ`. -/
def CofQ (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Prop :=
  ∀ q, 0 < q → q < upsilon l → ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ q < upsilon μ ∧
    eN (upsilon μ) * q ≤ O μ

/-- `Λ_{ε·x}`: the least restart index `λ` below which `ε_{x+1}·q` is realized cofinally by `OrecQ` for
every constant `0 < q < ρ_λ` (`Ω₁` if there is none). -/
noncomputable def LamQ : Ordinal.{0} := sInf (insert Om1 {l | IsRestartIdx l ∧ CofQ OrecQ l})

theorem LamQ_le_Om1 : LamQ ≤ Om1 := csInf_le (OrderBot.bddBelow _) (Set.mem_insert _ _)

theorem not_cofQ_of_lt {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlQ : l < LamQ) :
    ¬ CofQ OrecQ l := fun h =>
  absurd (csInf_le (OrderBot.bddBelow _) (Set.mem_insert_of_mem _
    (show l ∈ {l | IsRestartIdx l ∧ CofQ OrecQ l} from ⟨hl, h⟩))) (not_le.2 hlQ)

theorem LamQ_spec (h : LamQ < Om1) : IsRestartIdx LamQ ∧ CofQ OrecQ LamQ := by
  rcases csInf_mem (s := insert Om1 {l | IsRestartIdx l ∧ CofQ OrecQ l})
    ⟨Om1, Set.mem_insert _ _⟩ with h' | h'
  · exact absurd (h' ▸ h : Om1 < Om1) (lt_irrefl _)
  · exact h'

/-- **Below `Λ_{ε·x}` the value is `< ε_{ρ+1}·ρ`.** -/
theorem OrecQ_lt_top {l : Ordinal.{0}} (hl : IsRestartIdx l) (hno : ¬ CofQ OrecQ l) :
    OrecQ l < eN (upsilon l) * upsilon l := by
  rcases (OrecQ_le hl).lt_or_eq with h | h
  · exact h
  exfalso
  apply hno
  intro q hq0 hqρ ν hν
  have hepos := (eN_E (upsilon l)).pos
  have hlt : eN (upsilon l) * q < OrecQ l := by
    rw [h]; exact (mul_lt_mul_iff_right₀ hepos).2 hqρ
  rcases lt_OrecQ hlt with h0 | ⟨u, hCB, hc, hz⟩
  · exact absurd h0 (mul_pos hepos hq0).ne'
  cases u with
  | tq0 t =>
    exact absurd ((le_mul_pos _ hq0).trans hz) (not_le.2 (ev_lt_eN hCB))
  | tqE q' t =>
    have hqq : q ≤ q' := le_of_mul_le (ev_lt_eN hCB.2.2) hz
    obtain ⟨μ, hμ, h1, h2, h3, h4⟩ := hc ν hν
    exact ⟨μ, hμ, h1, h2, lt_of_le_of_lt hqq h3.2.1,
      ((mul_le_mul_right hqq _).trans le_self_add).trans h4⟩

/-- No restart index `λ ≤ Λ_{ε·ω}` has `ε_{x+1}·ω` realized cofinally below it. -/
theorem not_cofQ_le_LamEw {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlE : l ≤ LamEw) :
    ¬ CofQ OrecQ l := by
  intro hc
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  obtain ⟨μ, hμ, -, hμl, -, h4⟩ := hc ω omega0_pos (ups_omega_lt hl0) 0 hl0
  rw [OrecQ_eq_OrecM μ hμ (hμl.le.trans hlE)] at h4
  exact absurd h4 (not_le.2 (OrecM_lt_w (not_cofEw_of_lt hμ (lt_of_lt_of_le hμl hlE))))

/-! ## The inputs of Lemmas TOP and RS -/

/-- **The input of Lemma TOP** at a restart index `λ < Λ_{ε·x}`. -/
theorem topIn_OrecQ {l : Ordinal.{0}} (hl : IsRestartIdx l) (hE : ¬ CofQ OrecQ l) :
    TopInH OrecQ l := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  have hρE : InE (upsilon l) := upsPt_inE hρU
  set e := eN (upsilon l) with he
  have he0 : e ≠ 0 := (eN_E _).pos.ne'
  have hlt := OrecQ_lt_top hl hE
  have hone : 1 ≤ OrecQ l := one_le_OrecQ l
  have notcof : ∀ u, CBQ u (upsilon l) → OrecQ l = evQ u (upsilon l) →
      ¬ CofRealQ OrecQ l u := fun u hCB hev hc =>
    absurd (lt_OrecQ_of_cof hCB hc) (by rw [hev]; exact lt_irrefl _)
  set q := OrecQ l / e with hq
  set v := OrecQ l % e with hv
  have hdm : e * q + v = OrecQ l := div_add_mod _ _
  have hvlt : v < e := mod_lt _ he0
  have hqρ : q < upsilon l := (lt_mul_iff_div_lt he0).1 hlt
  obtain ⟨t0, hCB, hev⟩ := rep hρE v hvlt
  obtain ⟨m0, hm0, hm0c⟩ := cmax t0 _ hCB hρU.1
  have mk : ∀ u : OTQ, CBQ u (upsilon l) → OrecQ l = evQ u (upsilon l) →
      (∀ μ, IsRestartIdx μ → CB t0 (upsilon μ) → q < upsilon μ → CBQ u (upsilon μ)) →
      ∃ x0, x0 < upsilon l ∧ ∀ μ, IsRestartIdx μ → μ < l → x0 < upsilon μ →
        OrecQ μ < evQ u (upsilon μ) := by
    intro u hCBu hevu hcb
    have hnot := notcof u hCBu hevu
    unfold CofRealQ at hnot
    push Not at hnot
    obtain ⟨ν, hνl, hν⟩ := hnot
    have hνρ : upsilon ν < upsilon l := upsilon_normal.strictMono hνl
    refine ⟨max (max (upsilon ν) m0) q, max_lt (max_lt hνρ hm0) hqρ, fun μ hμ hμl hx0 => ?_⟩
    have hνμ : ν < μ := upsilon_normal.strictMono.lt_iff_lt.1
      (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hx0)
    have hCBμ : CB t0 (upsilon μ) :=
      (cb_iff t0 _).2 (fun c hc => lt_of_le_of_lt ((hm0c c hc).trans
        ((le_max_right _ _).trans (le_max_left _ _))) hx0)
    have hqμ : q < upsilon μ := lt_of_le_of_lt (le_max_right _ _) hx0
    exact hν μ hμ hνμ hμl (hcb μ hμ hCBμ hqμ)
  rcases eq_or_ne q 0 with hq0 | hq0
  · -- a term of `OT`
    have hO : OrecQ l = ev t0 (upsilon l) := by
      rw [← hdm, hq0, mul_zero, zero_add, ← hev]
    obtain ⟨x0, hx0, hb⟩ := mk (tq0 t0) hCB hO (fun μ _ h _ => h)
    exact ⟨ev t0, x0, hO, hx0, hb, fun R => R.pkg_ot hCB (by rw [← hO]; exact hone)⟩
  have hqpos : 0 < q := pos_iff_ne_zero.2 hq0
  rcases eq_or_ne v 0 with hv0 | hv0
  · -- `ε·q`
    have hO : OrecQ l = evQ (tqE q (k 0)) (upsilon l) := by
      show _ = e * q + ev (k 0) _
      rw [ev_k, add_zero, ← hdm, hv0, add_zero]
    obtain ⟨x0, hx0, hb⟩ := mk (tqE q (k 0)) ⟨hqpos, hqρ, hρU.1⟩ hO
      (fun μ hμ _ hqμ => ⟨hqpos, hqμ, (upsPt_upsilon (pos_iff_ne_zero.2 hμ.1)).1⟩)
    refine ⟨fun x => eN x * q, x0, ?_, hx0, fun μ hμ hμl hx => ?_, fun R => R.pkg_eQ q hqpos hqρ⟩
    · rw [hO]; show e * q + ev (k 0) _ = _; rw [ev_k, add_zero]
    · have := hb μ hμ hμl hx
      simpa [evQ, ev_k] using this
  · -- `ε·q + v`, `v ≥ 1`
    have hO : OrecQ l = evQ (tqE q t0) (upsilon l) := by
      show _ = e * q + ev t0 _
      rw [hev, ← hdm]
    obtain ⟨x0, hx0, hb⟩ := mk (tqE q t0) ⟨hqpos, hqρ, hCB⟩ hO
      (fun μ _ h hqμ => ⟨hqpos, hqμ, h⟩)
    exact ⟨fun x => eN x * q + ev t0 x, x0, hO, hx0, hb,
      fun R => R.pkg_eQt hqpos hqρ hCB (by rw [hev]; exact one_le_iff_ne_zero.2 hv0)⟩

/-- **The input of Lemma RS at a limit restart index `λ`** for `OrecQ`. -/
theorem rsIn_OrecQ {l : Ordinal.{0}} (hl : IsRestartIdx l) (h2 : 2 ≤ cL l) : RsInGen OrecQ l := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρ0 : 0 < upsilon l := (upsPt_upsilon hl0).1
  intro z hz
  rcases lt_OrecQ hz with rfl | ⟨u, hCB, hc, hzu⟩
  · refine ⟨ev (k 0), zero_le, fun R htg => rs_rstT R hρ0 htg, fun ν hν => ?_⟩
    obtain ⟨μ, hμ, h1, h3, -⟩ := cL_dense hl le_rfl (lt_of_lt_of_le one_lt_two h2) ν hν
    exact ⟨μ, hμ, h1, h3, by rw [ev_k]; exact zero_le⟩
  · refine ⟨evQ u, hzu, fun R htg => ?_, fun ν hν => ?_⟩
    · cases u with
      | tq0 t => exact rs_rstT R hCB htg
      | tqE q t => exact rs_rstQ R hCB.1 hCB.2.1 hCB.2.2 htg
    · obtain ⟨μ, hμ, h1, h3, -, h5⟩ := hc ν hν
      exact ⟨μ, hμ, h1, h3, h5⟩

theorem OrecQ_lt_δ {l : Ordinal.{0}} (hl : IsRestartIdx l) : OrecQ l < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have h1 : upsilon l < upsilon (l + ω) :=
    upsilon_normal.strictMono (lt_add_of_pos_right l omega0_pos)
  have h2 : upsilon (l + ω) < upsilon (l + ω + 1) := upsilon_normal.strictMono (lt_add_one _)
  have hτE : InE (upsilon (l + ω)) := upsPt_inE (upsPt_upsilon (lt_of_lt_of_le hl0 le_self_add))
  have hδE : InE (upsilon (l + ω + 1)) :=
    upsPt_inE (upsPt_upsilon (lt_of_lt_of_le hl0 (le_self_add.trans le_self_add)))
  have he : eN (upsilon l) < upsilon (l + ω + 1) := lt_of_le_of_lt (eN_le h1 hτE) h2
  exact lt_of_le_of_lt (OrecQ_le hl) (mul_lt_inE hδE he (h1.trans h2))

/-- **`OrecQ` is a general offset specification up to `B`** when no restart index below `B` has
`ε_{x+1}·q` realized cofinally for every constant `q`. -/
theorem specQ {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1)
    (hB : ∀ l, IsRestartIdx l → l < B → ¬ CofQ OrecQ l) : OffSpecGen OrecQ B where
  mult := hm
  cnt := hc
  le := fun _ hl _ => OrecQ_lt_δ hl
  one := fun l _ _ => one_le_OrecQ l
  top := fun l hl hlB => topIn_OrecQ hl (hB l hl hlB)
  succ := fun _ hl _ h2 => OrecQ_succ hl h2
  rs := fun _ hl _ h2 => rsIn_OrecQ hl h2

theorem specQ_of_le {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamQ) :
    OffSpecGen OrecQ B :=
  specQ hm hc (fun _ hl hlB => not_cofQ_of_lt hl (lt_of_lt_of_le hlB hB))

/-! ## Theorem BLK^O up to `Λ_{ε·x}` -/

/-- **Theorem BLK^O with `OrecQ` below `υ_B` for every `B ≤ Λ_{ε·x}`** (`ω² ∣ B`, `B < Ω₁`) in `R₂^C`:
(i) the `<₂`-pairs with right end below `υ_B` are the standard pairs; (ii) every restart `ρ_λ` (`λ < B`)
has no `<₁`-predecessor, no `<₂`-successor, and reach `δ_λ + OrecQ(λ)`; (iii) every point below `υ_B`
that is not a `υ`-point has its `R₁⁺` reach. -/
theorem blkQ {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamQ) :
    (∀ c d, c < d → d < upsilon B → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < B ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < B →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + OrecQ l)) ∧
    (∀ α < upsilon B, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  blk_genGen (specQ_of_le hm hc hB)

/-- **CORE-C up to `Λ_{ε·x}`**: `[0, υ_B) ⊆ Core(R₂^C)` for every `B ≤ Λ_{ε·x}`. -/
theorem coreQ {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamQ) :
    Set.Iio (upsilon B) ⊆ Core R2C :=
  core_genGen (specQ_of_le hm hc hB)

/-- **`Λ_{ε·x} < Ω₁`** (the core is countable, [C09] Cor 15.15). -/
theorem LamQ_lt_Om1 : LamQ < Om1 := by
  rcases LamQ_le_Om1.lt_or_eq with h | h
  · exact h
  · exfalso
    exact not_core_all (fun B hm hc => coreQ hm hc (by rw [h]; exact hc.le))

theorem LamQ_ri : IsRestartIdx LamQ := (LamQ_spec LamQ_lt_Om1).1

/-- **The exact reach of every restart below `Λ_{ε·x}`** in `R₂^C`: `lh(ρ_λ) = δ_λ + OrecQ(λ)`. -/
theorem reach_OrecQ {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlQ : l < LamQ) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + OrecQ l) :=
  (blkQ (ri_iff.1 LamQ_ri).2 LamQ_lt_Om1 le_rfl).2.1 l hl hlQ |>.2.2

theorem coreQ_LamQ : Set.Iio (upsilon LamQ) ⊆ Core R2C :=
  coreQ (ri_iff.1 LamQ_ri).2 LamQ_lt_Om1 le_rfl

/-- **`Λ_{ε·ω} < Λ_{ε·x}`.** -/
theorem LamEw_lt_LamQ : LamEw < LamQ := by
  by_contra hle
  push Not at hle
  have h1 : LamQ < Om1 := lt_of_le_of_lt hle LamEw_lt_Om1
  obtain ⟨hl, hc⟩ := LamQ_spec h1
  exact not_cofQ_le_LamEw hl hle hc

/-- **The reach at `Λ_{ε·ω}`**: `lh(ρ) = δ + ε_{ρ+1}·ω` (`ρ = ρ_{Λ_{ε·ω}}`, `δ = υ_{Λ_{ε·ω}+ω+1}`). -/
theorem reach_LamEw :
    IsReach R2C (upsilon LamEw) (upsilon (LamEw + ω + 1) + eN (upsilon LamEw) * ω) := by
  rw [← OrecQ_LamEw]
  exact reach_OrecQ (LamEw_spec LamEw_lt_Om1).1 LamEw_lt_LamQ

/-- **Theorem BLK^O at `Λ_{ε·ω}`**: BLK^O below `υ_{Λ_{ε·ω}+ω²}`, i.e. with the block of the restart
`ρ_{Λ_{ε·ω}}` (whose offset is `ε_{ρ+1}·ω`). -/
theorem blk_LamEw :
    (∀ c d, c < d → d < upsilon (LamEw + ω * ω) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < LamEw + ω * ω ∧
      c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < LamEw + ω * ω →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + OrecQ l)) ∧
    (∀ α < upsilon (LamEw + ω * ω), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) := by
  have hEw := (LamEw_spec LamEw_lt_Om1).1
  have hle : LamEw + ω * ω ≤ LamQ :=
    next_mult (ri_iff.1 hEw).2 (ri_iff.1 LamQ_ri).2 LamEw_lt_LamQ
  exact blkQ (dvd_add (ri_iff.1 hEw).2 (dvd_refl _)) (lt_of_le_of_lt hle LamQ_lt_Om1) hle

/-- **`OrecQ(Λ_{ε·x}) = ε_{ρ+1}·ρ = ω^{ε_{ρ+1}+ρ}`** (`ρ = ρ_{Λ_{ε·x}}`): at `Λ_{ε·x}` the value is the
atom `ω^{ε_{x+1}+x}`, whose exponent contains `x`; it is not a term of `OTQ`. -/
theorem OrecQ_LamQ : OrecQ LamQ = eN (upsilon LamQ) * upsilon LamQ := by
  obtain ⟨hl, hc⟩ := LamQ_spec LamQ_lt_Om1
  have hl0 : 0 < LamQ := pos_iff_ne_zero.2 hl.1
  have hρE : InE (upsilon LamQ) := upsPt_inE (upsPt_upsilon hl0)
  set e := eN (upsilon LamQ) with he
  have he0 : e ≠ 0 := (eN_E _).pos.ne'
  refine le_antisymm (OrecQ_le hl) ?_
  by_contra hlt
  push Not at hlt
  set q := OrecQ LamQ / e with hq
  have hqρ : q < upsilon LamQ := (lt_mul_iff_div_lt he0).1 hlt
  have hq1ρ : q + 1 < upsilon LamQ :=
    (inE_indec hρE).add_lt hqρ (one_lt_omega0.trans (omega0_lt_inE hρE))
  have h1 : OrecQ LamQ < e * (q + 1) := by
    have := lt_mul_succ_div (OrecQ LamQ) he0
    rwa [succ_eq_add_one] at this
  have hpos : (0 : Ordinal.{0}) < q + 1 := lt_of_lt_of_le zero_lt_one le_add_self
  have hcof : CofRealQ OrecQ LamQ (tqE (q + 1) (k 0)) := by
    intro ν hν
    obtain ⟨μ, hμ, h2, h3, h4, h5⟩ := hc (q + 1) hpos hq1ρ ν hν
    refine ⟨μ, hμ, h2, h3, ⟨hpos, h4, (upsPt_upsilon (pos_iff_ne_zero.2 hμ.1)).1⟩, ?_⟩
    show eN _ * (q + 1) + ev (k 0) _ ≤ _
    rw [ev_k, add_zero]; exact h5
  have h2 := lt_OrecQ_of_cof (show CBQ (tqE (q + 1) (k 0)) (upsilon LamQ) from
    ⟨hpos, hq1ρ, (upsPt_upsilon hl0).1⟩) hcof
  have : evQ (tqE (q + 1) (k 0)) (upsilon LamQ) = e * (q + 1) := by
    show eN _ * (q + 1) + ev (k 0) _ = _
    rw [ev_k, add_zero]
  rw [this] at h2
  exact absurd (h1.trans h2) (lt_irrefl _)

/-- `ε_{ρ+1}·ρ = ω^{ε_{ρ+1}+ρ}`. -/
theorem OrecQ_LamQ_atom : OrecQ LamQ = ω ^ (eN (upsilon LamQ) + upsilon LamQ) := by
  have hρE : InE (upsilon LamQ) := upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 LamQ_ri.1))
  have hρ' : ω ^ upsilon LamQ = upsilon LamQ := hρE
  rw [OrecQ_LamQ, ← eN_mul_opow, hρ']

/-! ## Where the first non-standard pair lies -/

/-- **`υ_B ≤ ν_C`** for every `B ≤ Λ_{ε·x}` (`ω² ∣ B`, `B < Ω₁`). -/
theorem upsQ_le_nuC {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamQ) :
    upsilon B ≤ nuC := by
  refine le_nuC (ups_lt_Om1 B hc).le (fun c d hcd hd h2 => ?_)
  obtain ⟨μ, j, hμ, -, rfl, rfl⟩ := ((blkQ hm hc hB).1 c d hcd hd).1 h2
  exact ⟨μ, j, hμ, rfl, rfl⟩

/-- **The left end of the first non-standard pair lies at or above `ρ_{Λ_{ε·x}}`**: if `ρ_L <₂ ν_C` then
`Λ_{ε·x} ≤ L`. -/
theorem left_ge_LamQ {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlν : upsilon l < nuC)
    (h2 : le2 (upsilon l) nuC) : LamQ ≤ l :=
  left_ge_of_spec (specQ_of_le (ri_iff.1 LamQ_ri).2 LamQ_lt_Om1 le_rfl) hl hlν h2

/-- **Where the first non-standard pair lies**: `ρ_L <₂ ν_C = ρ_ξ` with `Λ_{ε·x} ≤ L < ξ` restart indices,
`υ_{Λ_{ε·x}} ≤ ρ_L < ν_C < Ω₁`. -/
theorem nuC_boundQ : ∃ L ξ, IsRestartIdx L ∧ IsRestartIdx ξ ∧ LamQ ≤ L ∧ L < ξ ∧
    upsilon LamQ ≤ upsilon L ∧ upsilon L < nuC ∧ nuC = upsilon ξ ∧ nuC < Om1 ∧
    le2 (upsilon L) nuC := by
  obtain ⟨L, ξ, hL, hξ, hLξ, he, h2, -, -, -⟩ := level2_restart
  have hLν : upsilon L < nuC := by rw [he]; exact upsilon_normal.strictMono hLξ
  have hle := left_ge_LamQ hL hLν h2
  exact ⟨L, ξ, hL, hξ, hle, hLξ, upsilon_normal.strictMono.monotone hle, hLν, he, nuC_lt_Om1, h2⟩

end Googology.Trans.PoR.InaccPsi.R2
