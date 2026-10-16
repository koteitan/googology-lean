import Googology.Trans.PoR.InaccPsi.R2.EpsX
import Googology.Trans.PoR.InaccPsi.R2.ORecQ

/-!
# The recursive offset below `ε_{x+1}²`, and Theorem BLK^O at `Λ_{ε·x}` and up to `Λ_{ε²}`

The project's recursive offset (its paper's Definition 2.2) over the terms `OTX`: a term `t` of `OT`, or
`evL L + s` (a nonempty sum of atoms `ω^{ε_{x+1}+tᵢ(x)}`, `tᵢ, s` in `OT`); so every Cantor normal form in
`x` below `ε_{x+1}·ε_{x+1} = ω^{ε_{x+1}·2}`.  `OrecX(λ) = sup ({1} ∪ {u(ρ_λ) + 1 : u realized cofinally
below λ, constants below ρ_λ})`.  It extends `OrecQ` (stage 9, `R2.ORecQ`: constant multipliers).

* `OrecX_le` (`OrecX(λ) ≤ ω^{ε_{ρ+1}·2}`), `OrecX_succ`;
* `CofX`, `LamX` (`Λ_{ε²}`: the least restart index `λ` below which every atom `ω^{ε_{x+1}+t(x)}`,
  `t` in `OT`, is realized cofinally), `OrecX_lt_top` (below `Λ_{ε²}` the value is `< ω^{ε_{ρ+1}·2}`);
* `topIn_OrecX` (the input of Lemma TOP: the value `ε_{ρ+1}·q + v` is `evL L + s` for the list `L` of
  the IMG package `RstK.pkgL`, not realized cofinally), `rsIn_OrecX` (the input of Lemma RS, with
  `rs_rstT` and `rs_rstX`), `specX`;
* `blkOX` (**Theorem BLK^O with `OrecX` below `υ_B` for every `B ≤ Λ_{ε²}`**), `coreOX`, `LamX_lt_Om1`,
  `reach_OrecX` (`lh(ρ_λ) = δ_λ + OrecX(λ)` for every restart index `λ < Λ_{ε²}`);
* `isReach_unique`, `OrecX_eq_OrecQ` (the two offsets agree below `Λ_{ε·x}`: a reach is unique),
  `LamQ_lt_LamX`, `OrecX_LamQ` (`OrecX(Λ_{ε·x}) = ε_{ρ+1}·ρ`), `reach_LamQ` (**the reach at `Λ_{ε·x}`**:
  `lh(ρ) = δ + ε_{ρ+1}·ρ`), `OrecX_LamX` (`OrecX(Λ_{ε²}) = ε_{ρ+1}·ε_{ρ+1} = ω^{ε_{ρ+1}·2}`);
* `upsX_le_nuC`, `left_ge_LamX`, `nuC_boundX` (**`υ_{Λ_{ε²}} ≤ ρ_L < ν_C`**).

No new axiom.

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order OT

/-! ## Helpers -/

/-- A restart index is a limit. -/
theorem ri_limit {l : Ordinal.{0}} (hl : IsRestartIdx l) : IsSuccLimit l := by
  obtain ⟨q, hq⟩ := (ri_iff.1 hl).2
  have hq0 : q ≠ 0 := by intro h0; rw [h0, mul_zero] at hq; exact hl.1 hq
  rw [hq]
  exact isSuccLimit_mul_left (isSuccLimit_mul_right omega0_pos isSuccLimit_omega0)
    (pos_iff_ne_zero.2 hq0)

/-- Below `ρ_λ` (`λ` a restart index) every point is below some `υ_ν`, `ν < λ`. -/
theorem exists_ups_gt {l m : Ordinal.{0}} (hl : IsRestartIdx l) (hm : m < upsilon l) :
    ∃ ν < l, m < upsilon ν := by
  obtain ⟨_, ⟨ι, hι, rfl⟩, hκι⟩ := (lt_isLUB_iff (upsilon_limit (ri_limit hl))).1 hm
  exact ⟨ι, hι, hκι⟩

/-- A reach is unique. -/
theorem isReach_unique {R : Str} {a r1 r2 : Ordinal.{0}} (h1 : IsReach R a r1) (h2 : IsReach R a r2) :
    r1 = r2 :=
  le_antisymm (h2.2 r1 h1.1) (h1.2 r2 h2.1)

/-- A common bound for the constants of a list of terms. -/
theorem cmaxL : ∀ (L : List OT) (s : Ordinal.{0}), CBL L s → 0 < s →
    ∃ m < s, ∀ t ∈ L, ∀ c ∈ cs t, c ≤ m
  | [], s, _, hs => ⟨0, hs, fun t ht => by simp at ht⟩
  | t :: L, s, h, hs => by
    obtain ⟨m1, hm1, hc1⟩ := cmax t s (h t List.mem_cons_self) hs
    obtain ⟨m2, hm2, hc2⟩ := cmaxL L s (fun u hu => h u (List.mem_cons_of_mem _ hu)) hs
    refine ⟨max m1 m2, max_lt hm1 hm2, fun u hu c hc => ?_⟩
    rcases List.mem_cons.1 hu with rfl | hu
    · exact (hc1 c hc).trans (le_max_left _ _)
    · exact (hc2 u hu c hc).trans (le_max_right _ _)

/-- A member atom is at most the sum. -/
theorem atom_le_evL {x : Ordinal.{0}} : ∀ {L : List OT} {t : OT}, t ∈ L →
    ω ^ (eN x + ev t x) ≤ evL L x
  | [], _, ht => by simp at ht
  | u :: L, t, ht => by
    rw [evL_cons]
    rcases List.mem_cons.1 ht with rfl | ht
    · exact le_add_self
    · exact (atom_le_evL ht).trans le_self_add

/-- If an atom `ω^{ε+β}` is at most `evL L x + w` with `w < ε`, some exponent of `L` is `≥ β`. -/
theorem exists_ge_of_atom_le {x β w : Ordinal.{0}} {L : List OT} (hw : w < eN x)
    (h : ω ^ (eN x + β) ≤ evL L x + w) : ∃ t ∈ L, β ≤ ev t x := by
  by_contra hno
  push Not at hno
  have hL : evL L x < ω ^ (eN x + β) := by
    clear h
    induction L with
    | nil => exact opow_pos _ omega0_pos
    | cons t L ih =>
      rw [evL_cons]
      exact isPrincipal_add_omega0_opow _ (ih (fun u hu => hno u (List.mem_cons_of_mem _ hu)))
        ((opow_lt_opow_iff_right one_lt_omega0).2
          ((add_lt_add_iff_left _).2 (hno t List.mem_cons_self)))
  have := isPrincipal_add_omega0_opow _ hL (hw.trans_le (eN_le_atom x β))
  exact absurd h (not_le.2 this)

theorem eN_sq (x : Ordinal.{0}) : ω ^ (eN x + eN x) = eN x * eN x := by
  rw [opow_add]; have h : ω ^ eN x = eN x := eN_E x; rw [h]

/-! ## Terms below `ε_{x+1}²` -/

/-- Offset terms below `ε_{x+1}²`: a term `t` of `OT` (`tx0 t`), or `evL L + s` (`txL L s`). -/
inductive OTX : Type 1
  | tx0 : OT → OTX
  | txL : List OT → OT → OTX

open OTX

/-- The value of a term at `x`. -/
noncomputable def evX : OTX → Ordinal.{0} → Ordinal.{0}
  | tx0 t, x => ev t x
  | txL L s, x => evL L x + ev s x

/-- All constants below `s` (and the list of atoms nonempty). -/
def CBX : OTX → Ordinal.{0} → Prop
  | tx0 t, s => CB t s
  | txL L t, s => L ≠ [] ∧ CBL L s ∧ CB t s

theorem evX_lt {u : OTX} {x : Ordinal.{0}} (h : CBX u x) : evX u x < ω ^ (eN x + eN x) := by
  cases u with
  | tx0 t =>
    exact (ev_lt_eN h).trans_le ((le_self_add).trans (right_le_opow _ one_lt_omega0))
  | txL L t =>
    exact isPrincipal_add_omega0_opow _ (evL_lt L h.2.1)
      ((ev_lt_eN h.2.2).trans_le ((le_self_add).trans (right_le_opow _ one_lt_omega0)))

/-! ## The recursion -/

/-- `u` is realized cofinally below `λ` by the offsets `O`. -/
def CofRealX (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) (u : OTX) : Prop :=
  ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ CBX u (upsilon μ) ∧ evX u (upsilon μ) ≤ O μ

/-- The set whose supremum is `OrecX(λ)`. -/
def OSetX (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Set Ordinal.{0} :=
  insert 1 {w | ∃ u, CBX u (upsilon l) ∧ CofRealX O l u ∧ w = evX u (upsilon l) + 1}

theorem OSetX_congr {O O' : Ordinal.{0} → Ordinal.{0}} {l : Ordinal.{0}}
    (h : ∀ μ < l, O μ = O' μ) : OSetX O l = OSetX O' l := by
  have key : ∀ u, CofRealX O l u ↔ CofRealX O' l u := by
    intro u
    constructor
    · intro hc ν hν
      obtain ⟨μ, h1, h2, h3, h4, h5⟩ := hc ν hν
      exact ⟨μ, h1, h2, h3, h4, by rw [← h μ h3]; exact h5⟩
    · intro hc ν hν
      obtain ⟨μ, h1, h2, h3, h4, h5⟩ := hc ν hν
      exact ⟨μ, h1, h2, h3, h4, by rw [h μ h3]; exact h5⟩
  ext w
  simp only [OSetX, Set.mem_insert_iff, Set.mem_setOf_eq, key]

/-- **The recursive offset over `OTX`**, by well-founded recursion. -/
noncomputable def OrecX : Ordinal.{0} → Ordinal.{0} :=
  Ordinal.lt_wf.fix (fun l IH => sSup (OSetX (fun μ => if h : μ < l then IH μ h else 0) l))

theorem OrecX_eq (l : Ordinal.{0}) : OrecX l = sSup (OSetX OrecX l) := by
  show Ordinal.lt_wf.fix _ l = _
  rw [WellFounded.fix_eq]
  rw [OSetX_congr (O' := OrecX) (fun μ hμ => by simp only [hμ, dite_true]; rfl)]

theorem OSetX_bdd (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) :
    ∀ w ∈ OSetX O l, w ≤ ω ^ (eN (upsilon l) + eN (upsilon l)) := by
  intro w hw
  rcases hw with rfl | ⟨u, hCB, -, rfl⟩
  · exact one_le_iff_pos.2 (opow_pos _ omega0_pos)
  · exact add_one_le_of_lt (evX_lt hCB)

theorem OSetX_bddAbove (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) :
    BddAbove (OSetX O l) := ⟨_, OSetX_bdd O l⟩

/-- `OrecX(λ) ≤ ω^{ε_{ρ+1}·2}`. -/
theorem OrecX_le (l : Ordinal.{0}) : OrecX l ≤ ω ^ (eN (upsilon l) + eN (upsilon l)) := by
  rw [OrecX_eq]; exact csSup_le ⟨1, Set.mem_insert _ _⟩ (OSetX_bdd _ l)

theorem one_le_OrecX (l : Ordinal.{0}) : 1 ≤ OrecX l := by
  rw [OrecX_eq]; exact le_csSup (OSetX_bddAbove _ l) (Set.mem_insert _ _)

theorem lt_OrecX_of_cof {l : Ordinal.{0}} {u : OTX} (hCB : CBX u (upsilon l))
    (hc : CofRealX OrecX l u) : evX u (upsilon l) < OrecX l := by
  have h1 : evX u (upsilon l) + 1 ≤ OrecX l := by
    rw [OrecX_eq]
    exact le_csSup (OSetX_bddAbove _ l) (Set.mem_insert_of_mem _ ⟨u, hCB, hc, rfl⟩)
  exact lt_of_lt_of_le (lt_add_one _) h1

theorem lt_OrecX {l z : Ordinal.{0}} (hz : z < OrecX l) :
    z = 0 ∨ ∃ u, CBX u (upsilon l) ∧ CofRealX OrecX l u ∧ z ≤ evX u (upsilon l) := by
  rw [OrecX_eq] at hz
  obtain ⟨w, hw, hzw⟩ := (lt_csSup_iff (OSetX_bddAbove _ l) ⟨1, Set.mem_insert _ _⟩).1 hz
  rcases hw with rfl | ⟨u, hCB, hc, rfl⟩
  · left; exact le_antisymm (Order.lt_add_one_iff.1 (by rw [zero_add]; exact hzw)) zero_le
  · right; exact ⟨u, hCB, hc, Order.lt_add_one_iff.1 hzw⟩

/-- `OrecX = 1` at a successor restart index. -/
theorem OrecX_succ {l : Ordinal.{0}} (hl : IsRestartIdx l) (h2 : cL l < 2) : OrecX l = 1 := by
  obtain ⟨l0, hl0, rfl⟩ := succ_ri hl h2
  have hww : 0 < ω * ω := mul_pos omega0_pos omega0_pos
  have hS : OSetX OrecX (l0 + ω * ω) = {1} := by
    ext w
    simp only [OSetX, Set.mem_insert_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro (h | ⟨u, -, hc, -⟩)
      · exact h
      · exfalso
        obtain ⟨μ, hμ, h1, h3, -, -⟩ := hc l0 (lt_add_of_pos_right l0 hww)
        exact absurd h3 (not_lt.2 (next_mult (mult_of hl0) (ri_iff.1 hμ).2 h1))
    · intro h; exact Or.inl h
  rw [OrecX_eq, hS, csSup_singleton]

/-! ## The frontier `Λ_{ε²}` -/

/-- Every atom `ω^{ε_{x+1}+t(x)}` (`t` in `OT`, constants below `ρ_λ`) is realized cofinally below `λ`. -/
def CofX (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Prop :=
  ∀ t : OT, CB t (upsilon l) → ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ CB t (upsilon μ) ∧
    ω ^ (eN (upsilon μ) + ev t (upsilon μ)) ≤ O μ

/-- `Λ_{ε²}`: the least restart index below which every atom `ω^{ε_{x+1}+t(x)}` is realized cofinally
by `OrecX` (`Ω₁` if there is none). -/
noncomputable def LamX : Ordinal.{0} := sInf (insert Om1 {l | IsRestartIdx l ∧ CofX OrecX l})

theorem LamX_le_Om1 : LamX ≤ Om1 := csInf_le (OrderBot.bddBelow _) (Set.mem_insert _ _)

theorem not_cofX_of_lt {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlX : l < LamX) :
    ¬ CofX OrecX l := fun h =>
  absurd (csInf_le (OrderBot.bddBelow _) (Set.mem_insert_of_mem _
    (show l ∈ {l | IsRestartIdx l ∧ CofX OrecX l} from ⟨hl, h⟩))) (not_le.2 hlX)

theorem LamX_spec (h : LamX < Om1) : IsRestartIdx LamX ∧ CofX OrecX LamX := by
  rcases csInf_mem (s := insert Om1 {l | IsRestartIdx l ∧ CofX OrecX l})
    ⟨Om1, Set.mem_insert _ _⟩ with h' | h'
  · exact absurd (h' ▸ h : Om1 < Om1) (lt_irrefl _)
  · exact h'

/-- **Below `Λ_{ε²}` the value is `< ω^{ε_{ρ+1}·2}`.** -/
theorem OrecX_lt_top {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) (hno : ¬ CofX OrecX l) :
    OrecX l < ω ^ (eN (upsilon l) + eN (upsilon l)) := by
  rcases (OrecX_le l).lt_or_eq with h | h
  · exact h
  exfalso
  apply hno
  intro t ht ν hν
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρ0 : 0 < upsilon l := (upsPt_upsilon hl0).1
  have hlt : ω ^ (eN (upsilon l) + ev t (upsilon l)) < OrecX l := by
    rw [h]; exact atom_lt_sq (ev_lt_eN ht)
  rcases lt_OrecX hlt with h0 | ⟨u, hCB, hc, hz⟩
  · exact absurd h0 (opow_pos _ omega0_pos).ne'
  cases u with
  | tx0 s =>
    exact absurd ((eN_le_atom _ _).trans hz) (not_le.2 (ev_lt_eN hCB))
  | txL L s =>
    obtain ⟨t', ht'L, hge⟩ := exists_ge_of_atom_le (ev_lt_eN hCB.2.2) hz
    obtain ⟨m0, hm0, hm0c⟩ := cmax t _ ht hρ0
    obtain ⟨ν0, hν0l, hν0⟩ := exists_ups_gt hl hm0
    obtain ⟨μ, hμ, h1, h2, h3, h4⟩ := hc (max ν ν0) (max_lt hν hν0l)
    have hμ0 : 0 < μ := pos_iff_ne_zero.2 hμ.1
    have hν0μ : upsilon ν0 < upsilon μ :=
      upsilon_normal.strictMono (lt_of_le_of_lt (le_max_right _ _) h1)
    have htμ : CB t (upsilon μ) :=
      (cb_iff t _).2 (fun c hc => lt_of_le_of_lt (hm0c c hc) (hν0.trans hν0μ))
    have ht'μ : CB t' (upsilon μ) := h3.2.1 t' ht'L
    have hB := Bases_ups hμ0 h2 hl1
    have hge' : ev t (upsilon μ) ≤ ev t' (upsilon μ) := (uni_le hB htμ ht'μ).1 hge
    refine ⟨μ, hμ, lt_of_le_of_lt (le_max_left _ _) h1, h2, htμ, ?_⟩
    calc ω ^ (eN (upsilon μ) + ev t (upsilon μ))
        ≤ ω ^ (eN (upsilon μ) + ev t' (upsilon μ)) :=
          (opow_le_opow_iff_right one_lt_omega0).2 (add_le_add le_rfl hge')
      _ ≤ evL L (upsilon μ) := atom_le_evL ht'L
      _ ≤ evX (txL L s) (upsilon μ) := le_self_add
      _ ≤ OrecX μ := h4

/-! ## The inputs of Lemmas TOP and RS -/

/-- **The input of Lemma TOP** at a restart index `λ < Λ_{ε²}`. -/
theorem topIn_OrecX {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) (hE : ¬ CofX OrecX l) :
    TopInH OrecX l := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  have hρE : InE (upsilon l) := upsPt_inE hρU
  set e := eN (upsilon l) with he
  have he0 : e ≠ 0 := (eN_E _).pos.ne'
  have hlt := OrecX_lt_top hl hl1 hE
  rw [eN_sq] at hlt
  have hone : 1 ≤ OrecX l := one_le_OrecX l
  have notcof : ∀ u, CBX u (upsilon l) → OrecX l = evX u (upsilon l) →
      ¬ CofRealX OrecX l u := fun u hCB hev hc =>
    absurd (lt_OrecX_of_cof hCB hc) (by rw [hev]; exact lt_irrefl _)
  set q := OrecX l / e with hq
  set v := OrecX l % e with hv
  have hdm : e * q + v = OrecX l := div_add_mod _ _
  have hvlt : v < e := mod_lt _ he0
  have hqe : q < e := (lt_mul_iff_div_lt he0).1 hlt
  obtain ⟨t0, hCB, hev⟩ := rep hρE v hvlt
  obtain ⟨m0, hm0, hm0c⟩ := cmax t0 _ hCB hρU.1
  have mk : ∀ u : OTX, CBX u (upsilon l) → OrecX l = evX u (upsilon l) → ∀ m1, m1 < upsilon l →
      (∀ μ, IsRestartIdx μ → CB t0 (upsilon μ) → m1 < upsilon μ → CBX u (upsilon μ)) →
      ∃ x0, x0 < upsilon l ∧ ∀ μ, IsRestartIdx μ → μ < l → x0 < upsilon μ →
        OrecX μ < evX u (upsilon μ) := by
    intro u hCBu hevu m1 hm1 hcb
    have hnot := notcof u hCBu hevu
    unfold CofRealX at hnot
    push Not at hnot
    obtain ⟨ν, hνl, hν⟩ := hnot
    have hνρ : upsilon ν < upsilon l := upsilon_normal.strictMono hνl
    refine ⟨max (max (upsilon ν) m0) m1, max_lt (max_lt hνρ hm0) hm1, fun μ hμ hμl hx0 => ?_⟩
    have hνμ : ν < μ := upsilon_normal.strictMono.lt_iff_lt.1
      (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hx0)
    have hCBμ : CB t0 (upsilon μ) :=
      (cb_iff t0 _).2 (fun c hc => lt_of_le_of_lt ((hm0c c hc).trans
        ((le_max_right _ _).trans (le_max_left _ _))) hx0)
    have hm1μ : m1 < upsilon μ := lt_of_le_of_lt (le_max_right _ _) hx0
    exact hν μ hμ hνμ hμl (hcb μ hμ hCBμ hm1μ)
  rcases eq_or_ne q 0 with hq0 | hq0
  · -- a term of `OT`
    have hO : OrecX l = ev t0 (upsilon l) := by
      rw [← hdm, hq0, mul_zero, zero_add, ← hev]
    obtain ⟨x0, hx0, hb⟩ := mk (tx0 t0) hCB hO 0 hρU.1 (fun μ _ h _ => h)
    exact ⟨ev t0, x0, hO, hx0, hb, fun R => R.pkg_ot hCB (by rw [← hO]; exact hone)⟩
  have hqpos : 0 < q := pos_iff_ne_zero.2 hq0
  -- the list of atoms for `ε·q`: from the IMG package `RstK.pkgL` when the restart context holds
  -- (then the package is that of this list), and from the Cantor normal form otherwise
  obtain ⟨L, hL, hCL, heL, hpk⟩ : ∃ L : List OT, L ≠ [] ∧ CBL L (upsilon l) ∧
      evL L (upsilon l) = e * q ∧ (RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)) →
        ImgPkg (upsilon l) (upsilon (l + ω + 1)) (evL L)) := by
    by_cases hR : RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1))
    · obtain ⟨L, h1, h2, h3, h4⟩ := hR.pkgL q hqpos hqe
      exact ⟨L, h1, h2, h3, fun _ => h4⟩
    · have key : ∀ q, 0 < q → q < e → ∃ L : List OT, L ≠ [] ∧ CBL L (upsilon l) ∧
          evL L (upsilon l) = e * q := by
        intro q
        induction q using WellFoundedLT.induction with
        | ind q IH =>
        intro hq0 hqe
        obtain ⟨q'', hgs, -, hq''⟩ := lg_split hq0.ne'
        have hze : lg q < e := lt_of_le_of_lt (lg_le hq0.ne') hqe
        obtain ⟨t, ct, et⟩ := rep hρE (lg q) hze
        have hval : e * q = e * q'' + ω ^ (e + ev t (upsilon l)) := by
          rw [et, he, ← eN_mul_opow, ← mul_add, ← hgs]
        rcases eq_or_ne q'' 0 with h0 | h0
        · refine ⟨[t], by simp, fun u hu => by simp at hu; rw [hu]; exact ct, ?_⟩
          rw [evL_cons, evL_nil, zero_add, hval, h0, mul_zero, zero_add]
        obtain ⟨L, hL, cL, eL⟩ := IH q'' hq'' (pos_iff_ne_zero.2 h0) (hq''.trans hqe)
        refine ⟨t :: L, by simp, fun u hu => ?_, ?_⟩
        · rcases List.mem_cons.1 hu with rfl | hu
          · exact ct
          · exact cL u hu
        · rw [evL_cons, eL, hval]
      obtain ⟨L, h1, h2, h3⟩ := key q hqpos hqe
      exact ⟨L, h1, h2, h3, fun R => absurd R hR⟩
  obtain ⟨mL, hmL, hmLc⟩ := cmaxL L _ hCL hρU.1
  have hCLμ : ∀ μ, mL < upsilon μ → CBL L (upsilon μ) := fun μ h t ht =>
    (cb_iff t _).2 (fun c hc => lt_of_le_of_lt (hmLc t ht c hc) h)
  rcases eq_or_ne v 0 with hv0 | hv0
  · -- `ε·q`
    have hO : OrecX l = evX (txL L (k 0)) (upsilon l) := by
      show _ = evL L _ + ev (k 0) _
      rw [ev_k, add_zero, heL, ← hdm, hv0, add_zero]
    obtain ⟨x0, hx0, hb⟩ := mk (txL L (k 0)) ⟨hL, hCL, hρU.1⟩ hO mL hmL
      (fun μ hμ _ h => ⟨hL, hCLμ μ h, (upsPt_upsilon (pos_iff_ne_zero.2 hμ.1)).1⟩)
    refine ⟨evL L, x0, ?_, hx0, fun μ hμ hμl hx => ?_, fun R => ?_⟩
    · rw [hO]; show evL L _ + ev (k 0) _ = _; rw [ev_k, add_zero]
    · have := hb μ hμ hμl hx
      simpa [evX, ev_k] using this
    · exact hpk R
  · -- `ε·q + v`, `v ≥ 1`
    have hO : OrecX l = evX (txL L t0) (upsilon l) := by
      show _ = evL L _ + ev t0 _
      rw [hev, heL, ← hdm]
    obtain ⟨x0, hx0, hb⟩ := mk (txL L t0) ⟨hL, hCL, hCB⟩ hO mL hmL
      (fun μ _ h hm => ⟨hL, hCLμ μ hm, h⟩)
    exact ⟨fun x => evL L x + ev t0 x, x0, hO, hx0, hb, fun R => R.pkgLt hL (hpk R) hCB
      (by rw [hev]; exact one_le_iff_ne_zero.2 hv0)⟩

/-- **The input of Lemma RS at a limit restart index `λ`** for `OrecX`. -/
theorem rsIn_OrecX {l : Ordinal.{0}} (hl : IsRestartIdx l) (h2 : 2 ≤ cL l) : RsInGen OrecX l := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρ0 : 0 < upsilon l := (upsPt_upsilon hl0).1
  intro z hz
  rcases lt_OrecX hz with rfl | ⟨u, hCB, hc, hzu⟩
  · refine ⟨ev (k 0), zero_le, fun R htg => rs_rstT R hρ0 htg, fun ν hν => ?_⟩
    obtain ⟨μ, hμ, h1, h3, -⟩ := cL_dense hl le_rfl (lt_of_lt_of_le one_lt_two h2) ν hν
    exact ⟨μ, hμ, h1, h3, by rw [ev_k]; exact zero_le⟩
  · refine ⟨evX u, hzu, fun R htg => ?_, fun ν hν => ?_⟩
    · cases u with
      | tx0 t => exact rs_rstT R hCB htg
      | txL L t => exact rs_rstX R hCB.1 hCB.2.1 hCB.2.2 htg
    · obtain ⟨μ, hμ, h1, h3, -, h5⟩ := hc ν hν
      exact ⟨μ, hμ, h1, h3, h5⟩

theorem OrecX_lt_δ {l : Ordinal.{0}} (hl : IsRestartIdx l) : OrecX l < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have h1 : upsilon l < upsilon (l + ω) :=
    upsilon_normal.strictMono (lt_add_of_pos_right l omega0_pos)
  have h2 : upsilon (l + ω) < upsilon (l + ω + 1) := upsilon_normal.strictMono (lt_add_one _)
  have hτE : InE (upsilon (l + ω)) := upsPt_inE (upsPt_upsilon (lt_of_lt_of_le hl0 le_self_add))
  have hδE : InE (upsilon (l + ω + 1)) :=
    upsPt_inE (upsPt_upsilon (lt_of_lt_of_le hl0 (le_self_add.trans le_self_add)))
  have he : eN (upsilon l) < upsilon (l + ω + 1) := lt_of_le_of_lt (eN_le h1 hτE) h2
  have h3 := (opow_lt_opow_iff_right one_lt_omega0).2 ((inE_indec hδE).add_lt he he)
  have hδ' : ω ^ upsilon (l + ω + 1) = upsilon (l + ω + 1) := hδE
  rw [hδ'] at h3
  exact lt_of_le_of_lt (OrecX_le l) h3

/-- **`OrecX` is a general offset specification up to `B`** when no restart index below `B` has every
atom realized cofinally. -/
theorem specX {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1)
    (hB : ∀ l, IsRestartIdx l → l < B → ¬ CofX OrecX l) : OffSpecGen OrecX B where
  mult := hm
  cnt := hc
  le := fun _ hl _ => OrecX_lt_δ hl
  one := fun l _ _ => one_le_OrecX l
  top := fun l hl hlB => topIn_OrecX hl (hlB.trans hc) (hB l hl hlB)
  succ := fun _ hl _ h2 => OrecX_succ hl h2
  rs := fun _ hl _ h2 => rsIn_OrecX hl h2

theorem specX_of_le {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamX) :
    OffSpecGen OrecX B :=
  specX hm hc (fun _ hl hlB => not_cofX_of_lt hl (lt_of_lt_of_le hlB hB))

/-! ## Theorem BLK^O up to `Λ_{ε²}` -/

/-- **Theorem BLK^O with `OrecX` below `υ_B` for every `B ≤ Λ_{ε²}`** (`ω² ∣ B`, `B < Ω₁`) in `R₂^C`:
(i) the `<₂`-pairs with right end below `υ_B` are the standard pairs; (ii) every restart `ρ_λ` (`λ < B`)
has no `<₁`-predecessor, no `<₂`-successor, and reach `δ_λ + OrecX(λ)`; (iii) every point below `υ_B`
that is not a `υ`-point has its `R₁⁺` reach. -/
theorem blkOX {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamX) :
    (∀ c d, c < d → d < upsilon B → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < B ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < B →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + OrecX l)) ∧
    (∀ α < upsilon B, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  blk_genGen (specX_of_le hm hc hB)

/-- **CORE-C up to `Λ_{ε²}`**: `[0, υ_B) ⊆ Core(R₂^C)` for every `B ≤ Λ_{ε²}`. -/
theorem coreOX {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamX) :
    Set.Iio (upsilon B) ⊆ Core R2C :=
  core_genGen (specX_of_le hm hc hB)

/-- **`Λ_{ε²} < Ω₁`** (the core is countable, [C09] Cor 15.15). -/
theorem LamX_lt_Om1 : LamX < Om1 := by
  rcases LamX_le_Om1.lt_or_eq with h | h
  · exact h
  · exfalso
    exact not_core_all (fun B hm hc => coreOX hm hc (by rw [h]; exact hc.le))

theorem LamX_ri : IsRestartIdx LamX := (LamX_spec LamX_lt_Om1).1

/-- **The exact reach of every restart below `Λ_{ε²}`** in `R₂^C`: `lh(ρ_λ) = δ_λ + OrecX(λ)`. -/
theorem reach_OrecX {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlX : l < LamX) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + OrecX l) :=
  (blkOX (ri_iff.1 LamX_ri).2 LamX_lt_Om1 le_rfl).2.1 l hl hlX |>.2.2

theorem coreOX_LamX : Set.Iio (upsilon LamX) ⊆ Core R2C :=
  coreOX (ri_iff.1 LamX_ri).2 LamX_lt_Om1 le_rfl

/-! ## Comparing with `OrecQ`; the values at `Λ_{ε·x}` and `Λ_{ε²}` -/

/-- **`OrecX = OrecQ` below both frontiers** (the reach is unique). -/
theorem OrecX_eq_OrecQ {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlX : l < LamX) (hlQ : l < LamQ) :
    OrecX l = OrecQ l :=
  (add_left_cancel_iff).1 (isReach_unique (reach_OrecX hl hlX) (reach_OrecQ hl hlQ))

/-- **`Λ_{ε·x} < Λ_{ε²}`.** -/
theorem LamQ_lt_LamX : LamQ < LamX := by
  by_contra hle
  push Not at hle
  obtain ⟨hl, hc⟩ := LamX_spec LamX_lt_Om1
  have hl0 : 0 < LamX := pos_iff_ne_zero.2 hl.1
  have hρ0 : 0 < upsilon LamX := (upsPt_upsilon hl0).1
  obtain ⟨μ, hμ, -, hμl, -, h5⟩ := hc (xw (k 0)) hρ0 0 hl0
  have hμ0 : 0 < μ := pos_iff_ne_zero.2 hμ.1
  have hμE : InE (upsilon μ) := upsPt_inE (upsPt_upsilon hμ0)
  have hμE' : ω ^ upsilon μ = upsilon μ := hμE
  rw [OrecX_eq_OrecQ hμ hμl (lt_of_lt_of_le hμl hle)] at h5
  have h6 := OrecQ_lt_top hμ (not_cofQ_of_lt hμ (lt_of_lt_of_le hμl hle))
  simp only [ev_xw, ev_k, add_zero, hμE'] at h5
  rw [← eN_mul_opow, hμE'] at h5
  exact absurd h5 (not_le.2 h6)

/-- **`OrecX(Λ_{ε·x}) = ε_{ρ+1}·ρ`** (`ρ = ρ_{Λ_{ε·x}}`). -/
theorem OrecX_LamQ : OrecX LamQ = eN (upsilon LamQ) * upsilon LamQ := by
  obtain ⟨hl, hc⟩ := LamQ_spec LamQ_lt_Om1
  have hl0 : 0 < LamQ := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  have hρE : InE (upsilon LamQ) := upsPt_inE hρU
  have hρ' : ω ^ upsilon LamQ = upsilon LamQ := hρE
  set e := eN (upsilon LamQ) with he
  have he0 : e ≠ 0 := (eN_E _).pos.ne'
  have hlim : e * upsilon LamQ = ω ^ (e + upsilon LamQ) := by rw [← eN_mul_opow, hρ']
  -- on `μ < Λ_{ε·x}` the two offsets agree
  have hQX : ∀ μ, IsRestartIdx μ → μ < LamQ → OrecX μ = OrecQ μ := fun μ hμ hμl =>
    OrecX_eq_OrecQ hμ (hμl.trans LamQ_lt_LamX) hμl
  apply le_antisymm
  · rw [OrecX_eq]
    refine csSup_le ⟨1, Set.mem_insert _ _⟩ ?_
    rintro w (rfl | ⟨u, hCB, hcu, rfl⟩)
    · exact one_le_iff_pos.2 (mul_pos (eN_E _).pos hρE.pos)
    have hlimit : IsSuccLimit (ω ^ (e + upsilon LamQ)) := by
      have : ω ^ (e + upsilon LamQ) = ω ^ (e + upsilon LamQ) := rfl
      exact isSuccLimit_opow_left isSuccLimit_omega0 (lt_of_lt_of_le hρE.pos le_add_self).ne'
    rw [hlim]
    refine (Order.add_one_le_iff_of_not_isMax (not_isMax _)).2 ?_
    cases u with
    | tx0 t =>
      exact (ev_lt_eN hCB).trans_le (eN_le_atom _ _)
    | txL L s =>
      -- every exponent of `L` is below `ρ` at `ρ`
      have hexp : ∀ t ∈ L, ev t (upsilon LamQ) < upsilon LamQ := by
        intro t ht
        by_contra hge
        push Not at hge
        obtain ⟨m0, hm0, hm0c⟩ := cmaxL L _ hCB.2.1 hρU.1
        obtain ⟨ν0, hν0l, hν0⟩ := exists_ups_gt hl hm0
        obtain ⟨μ, hμ, h1, h2, h3, h4⟩ := hcu ν0 hν0l
        have hμ0 : 0 < μ := pos_iff_ne_zero.2 hμ.1
        have hμE : InE (upsilon μ) := upsPt_inE (upsPt_upsilon hμ0)
        have hμE' : ω ^ upsilon μ = upsilon μ := hμE
        have hB := Bases_ups hμ0 h2 LamQ_lt_Om1
        have htμ : CB t (upsilon μ) := h3.2.1 t ht
        have hge' : ev (xw (k 0)) (upsilon μ) ≤ ev t (upsilon μ) :=
          (uni_le hB (show CB (xw (k 0)) (upsilon μ) from (upsPt_upsilon hμ0).1) htμ).1
            (by simp only [ev_xw, ev_k, add_zero, hρ']; exact hge)
        simp only [ev_xw, ev_k, add_zero, hμE'] at hge'
        have h6 := OrecQ_lt_top hμ (not_cofQ_of_lt hμ h2)
        rw [← hQX μ hμ h2] at h6
        have h7 : eN (upsilon μ) * upsilon μ ≤ evX (txL L s) (upsilon μ) := by
          rw [← hμE', eN_mul_opow, hμE']
          exact ((opow_le_opow_iff_right one_lt_omega0).2 (add_le_add le_rfl hge')).trans
            ((atom_le_evL ht).trans le_self_add)
        exact absurd (h7.trans h4) (not_le.2 h6)
      have hL : evL L (upsilon LamQ) < ω ^ (e + upsilon LamQ) := by
        have : ∀ L' : List OT, (∀ t ∈ L', ev t (upsilon LamQ) < upsilon LamQ) →
            evL L' (upsilon LamQ) < ω ^ (e + upsilon LamQ) := by
          intro L'
          induction L' with
          | nil => exact fun _ => opow_pos _ omega0_pos
          | cons t L' ih =>
            intro hh
            rw [evL_cons]
            exact isPrincipal_add_omega0_opow _ (ih (fun u hu => hh u (List.mem_cons_of_mem _ hu)))
              ((opow_lt_opow_iff_right one_lt_omega0).2
                ((add_lt_add_iff_left _).2 (hh t List.mem_cons_self)))
        exact this L hexp
      exact isPrincipal_add_omega0_opow _ hL ((ev_lt_eN hCB.2.2).trans_le (eN_le_atom _ _))
  · by_contra hlt
    push Not at hlt
    rw [hlim] at hlt
    set X := OrecX LamQ with hX
    have hX' : X < e * upsilon LamQ := by rw [hlim]; exact hlt
    set q := X / e with hq
    have hqρ : q < upsilon LamQ := (lt_mul_iff_div_lt he0).1 hX'
    have hq1ρ : q + 1 < upsilon LamQ :=
      (inE_indec hρE).add_lt hqρ (one_lt_omega0.trans (omega0_lt_inE hρE))
    have h1 : X < e * (q + 1) := by
      have := lt_mul_succ_div X he0
      rwa [succ_eq_add_one] at this
    set β := q + 1 with hβ
    have hβω : β ≤ ω ^ β := right_le_opow _ one_lt_omega0
    have hωβρ : ω ^ β < upsilon LamQ := by
      have := (opow_lt_opow_iff_right one_lt_omega0).2 hq1ρ
      rwa [hρ'] at this
    have hcof : CofRealX OrecX LamQ (txL [k β] (k 0)) := by
      intro ν hν
      obtain ⟨μ, hμ, h2, h3, h4, h5⟩ := hc (ω ^ β) (opow_pos _ omega0_pos) hωβρ ν hν
      refine ⟨μ, hμ, h2, h3, ⟨by simp, fun t ht => ?_, (upsPt_upsilon (pos_iff_ne_zero.2 hμ.1)).1⟩, ?_⟩
      · simp at ht; rw [ht]; exact lt_of_le_of_lt hβω h4
      · rw [hQX μ hμ h3]
        show evL [k β] _ + ev (k 0) _ ≤ _
        simp only [evL_cons, evL_nil, ev_k, zero_add, add_zero]
        rw [← eN_mul_opow]; exact h5
    have h2 := lt_OrecX_of_cof (show CBX (txL [k β] (k 0)) (upsilon LamQ) from
      ⟨by simp, fun t ht => by simp at ht; rw [ht]; exact hq1ρ, (upsPt_upsilon hl0).1⟩) hcof
    have h3 : evX (txL [k β] (k 0)) (upsilon LamQ) = e * ω ^ β := by
      show evL [k β] _ + ev (k 0) _ = _
      simp only [evL_cons, evL_nil, ev_k, zero_add, add_zero]
      rw [← eN_mul_opow]
    rw [h3] at h2
    have h4 : e * β ≤ e * ω ^ β := mul_le_mul_right hβω e
    exact absurd ((h1.trans_le h4).trans h2) (lt_irrefl _)

/-- **The reach at `Λ_{ε·x}`**: `lh(ρ) = δ + ε_{ρ+1}·ρ` (`ρ = ρ_{Λ_{ε·x}}`). -/
theorem reach_LamQ :
    IsReach R2C (upsilon LamQ) (upsilon (LamQ + ω + 1) + eN (upsilon LamQ) * upsilon LamQ) := by
  rw [← OrecX_LamQ]
  exact reach_OrecX LamQ_ri LamQ_lt_LamX

/-- **`OrecX(Λ_{ε²}) = ε_{ρ+1}·ε_{ρ+1} = ω^{ε_{ρ+1}·2}`** (`ρ = ρ_{Λ_{ε²}}`): the next atom is
`ω^{ε_{x+1}·2}`, whose exponent is not of the form `ε_{x+1} + t(x)`. -/
theorem OrecX_LamX : OrecX LamX = eN (upsilon LamX) * eN (upsilon LamX) := by
  obtain ⟨hl, hc⟩ := LamX_spec LamX_lt_Om1
  have hl0 : 0 < LamX := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  have hρE : InE (upsilon LamX) := upsPt_inE hρU
  set e := eN (upsilon LamX) with he
  have he0 : e ≠ 0 := (eN_E _).pos.ne'
  refine le_antisymm (by rw [← eN_sq]; exact OrecX_le _) ?_
  by_contra hlt
  push Not at hlt
  set X := OrecX LamX with hX
  set q := X / e with hq
  have hqe : q < e := (lt_mul_iff_div_lt he0).1 hlt
  have hq1e : q + 1 < e :=
    (inE_indec (eN_E _)).add_lt hqe (one_lt_omega0.trans (omega0_lt_inE (eN_E _)))
  have h1 : X < e * (q + 1) := by
    have := lt_mul_succ_div X he0
    rwa [succ_eq_add_one] at this
  obtain ⟨t, ct, et⟩ := rep hρE (q + 1) hq1e
  have hcof : CofRealX OrecX LamX (txL [t] (k 0)) := by
    intro ν hν
    obtain ⟨μ, hμ, h2, h3, h4, h5⟩ := hc t ct ν hν
    refine ⟨μ, hμ, h2, h3, ⟨by simp, fun u hu => by simp at hu; rw [hu]; exact h4,
      (upsPt_upsilon (pos_iff_ne_zero.2 hμ.1)).1⟩, ?_⟩
    show evL [t] _ + ev (k 0) _ ≤ _
    simpa using h5
  have h2 := lt_OrecX_of_cof (show CBX (txL [t] (k 0)) (upsilon LamX) from
    ⟨by simp, fun u hu => by simp at hu; rw [hu]; exact ct, hρU.1⟩) hcof
  have h3 : evX (txL [t] (k 0)) (upsilon LamX) = e * ω ^ (q + 1) := by
    show evL [t] _ + ev (k 0) _ = _
    simp only [evL_cons, evL_nil, ev_k, zero_add, add_zero, et]
    rw [← eN_mul_opow]
  rw [h3] at h2
  have h4 : e * (q + 1) ≤ e * ω ^ (q + 1) := mul_le_mul_right (right_le_opow _ one_lt_omega0) e
  exact absurd ((h1.trans_le h4).trans h2) (lt_irrefl _)

/-! ## Where the first non-standard pair lies -/

/-- **`υ_B ≤ ν_C`** for every `B ≤ Λ_{ε²}` (`ω² ∣ B`, `B < Ω₁`). -/
theorem upsX_le_nuC {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamX) :
    upsilon B ≤ nuC := by
  refine le_nuC (ups_lt_Om1 B hc).le (fun c d hcd hd h2 => ?_)
  obtain ⟨μ, j, hμ, -, rfl, rfl⟩ := ((blkOX hm hc hB).1 c d hcd hd).1 h2
  exact ⟨μ, j, hμ, rfl, rfl⟩

/-- **The left end of the first non-standard pair lies at or above `ρ_{Λ_{ε²}}`**: if `ρ_L <₂ ν_C` then
`Λ_{ε²} ≤ L`. -/
theorem left_ge_LamX {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlν : upsilon l < nuC)
    (h2 : le2 (upsilon l) nuC) : LamX ≤ l :=
  left_ge_of_spec (specX_of_le (ri_iff.1 LamX_ri).2 LamX_lt_Om1 le_rfl) hl hlν h2

/-- **Where the first non-standard pair lies**: `ρ_L <₂ ν_C = ρ_ξ` with `Λ_{ε²} ≤ L < ξ` restart indices,
`υ_{Λ_{ε²}} ≤ ρ_L < ν_C < Ω₁`. -/
theorem nuC_boundX : ∃ L ξ, IsRestartIdx L ∧ IsRestartIdx ξ ∧ LamX ≤ L ∧ L < ξ ∧
    upsilon LamX ≤ upsilon L ∧ upsilon L < nuC ∧ nuC = upsilon ξ ∧ nuC < Om1 ∧
    le2 (upsilon L) nuC := by
  obtain ⟨L, ξ, hL, hξ, hLξ, he, h2, -, -, -⟩ := level2_restart
  have hLν : upsilon L < nuC := by rw [he]; exact upsilon_normal.strictMono hLξ
  have hle := left_ge_LamX hL hLν h2
  exact ⟨L, ξ, hL, hξ, hle, hLξ, upsilon_normal.strictMono.monotone hle, hLν, he, nuC_lt_Om1, h2⟩

end Googology.Trans.PoR.InaccPsi.R2
