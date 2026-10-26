import Googology.Trans.PoR.InaccPsi.R2.HeG1

/-!
# HeGate: PIECES OF A TWO-GATE DISCIPLINE FOR CONSTANT LEVELS `μ ≥ ε₀`, AND THE EXACT WALL OF ONE GATE

The level recursion of `Hd` (`Hd.HdLvl μ`: `ω ≤ μ < ε₀`) reads a level `μ` as itself at every `ε`-number base.  At a
level `μ ≥ ε₀` this fails at the base `ε₀` itself, so the readings need a gate `≥ μ`; with ONE gate the start of the
level recursion over the base `G = Γ_{Ω₁+1}` (gate `0` as a code) breaks (`he_high0_fails`: the high-gate condition
of `Hd.HdMStart` forces every base gate below `ε₀`).  Here are the pieces a second (level) gate needs, all proved:

* `heFs` (**A FUNDAMENTAL SEQUENCE FOR EVERY COUNTABLE LIMIT**, from `Gc.gc_countable`; replaces `Gp.gpFs`, which
  stops at `ε₀`), `heFs_lt`, `heFs_mono`, `heFs_mono'`, `heFs_cof`;
* `he_cl_cnt` (a countable code over a strongly critical `Z ≤ Ω₁` lies below `Z`), `he_cl_level` (**THE LEVEL OF A
  CODE**: a code in `[φ(a, j), φ(a, j+1))` with `j` not a fixed point, `G < φ(a, j)`, `a` countable has `a < Z`;
  replaces `Hd.HdLvl.small` and gives the code-gate condition `μ < Z` of a level read through a gate);
* `he_glA_pi` (**LEMMA EXACT FOR `ϑᵖ(Ω₁·μ + t)` AT EVERY LEVEL `μ < σ`**; replaces `Hd.hdm_glA_pi`), `he_cst_mem`
  (a level below the gate lies in every hull `C(a, b)` with the gate below `b`; replaces `Hd.HdLvl.mem`);
* `heRegate` (**RAISING THE BASE GATE** of a system: the fields that ask `γ < x` get weaker), `heRegateG` (**THE
  GATE OF A LEVEL AT `G`**: the top of a chain with bound `φ(α, G+1)` gets the base gate `α`, a gate of its bound by
  `he_cl_level`; the start a base of level `α ≥ ε₀` at `G` needs, as `Hc.HcSStart` asks the same gate as the stage);
* `he_high0_fails` (**THE WALL OF ONE GATE**: for a start `S0` above `G` and a base gate `γ ≥ ε₀`, the condition
  `∀ c σ, G ≤ c < S0.B, σ ∈ E ∩ Ω₁, g(c) < σ ⇒ γ < σ` fails at `c = G`, `σ = ε₀`).

No new axiom.  New definitions: `heFs`, `heRegate`, `heRegateG`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.He

open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Gp Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Gv
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gb
  Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Notation.InaccPsi.InaccSeq

/-! ## Fundamental sequences for countable limits -/

/-- A surjection of `ℕ` onto the ordinals below a countable `λ > 0`. -/
theorem he_surj {l : Ordinal.{0}} (hl : l < Om (1 : Ordinal.{0})) (h0 : 0 < l) :
    ∃ f : ℕ → Ordinal.{0}, (∀ k, f k < l) ∧ ∀ t, t < l → ∃ k, f k = t := by
  haveI := gc_countable hl
  haveI : Nonempty (Iio l) := ⟨⟨0, h0⟩⟩
  obtain ⟨f, hf⟩ := exists_surjective_nat (Iio l)
  refine ⟨fun k => (f k).1, fun k => (f k).2, fun t ht => ?_⟩
  obtain ⟨k, hk⟩ := hf ⟨t, ht⟩
  exact ⟨k, by show (f k).1 = t; rw [hk]⟩

open Classical in
/-- **The fundamental sequence of a countable limit `λ`** (an arbitrary one). -/
noncomputable def heFs (l : Ordinal.{0}) : ℕ → Ordinal.{0} :=
  if h : l < Om (1 : Ordinal.{0}) ∧ 0 < l then gpUp (Classical.choose (he_surj h.1 h.2)) else fun _ => 0

section Fs

variable {l : Ordinal.{0}} (hl : IsSuccLimit l) (hl1 : l < Om (1 : Ordinal.{0}))
include hl hl1

theorem heFs_eq : heFs l = gpUp (Classical.choose (he_surj hl1 hl.bot_lt)) := by
  unfold heFs; rw [dif_pos ⟨hl1, hl.bot_lt⟩]

theorem heFs_lt (k : ℕ) : heFs l k < l := by
  rw [heFs_eq hl hl1]
  exact gpUp_lt hl (Classical.choose_spec (he_surj hl1 hl.bot_lt)).1 k

theorem heFs_mono (k : ℕ) : heFs l k < heFs l (k + 1) := by
  rw [heFs_eq hl hl1]; exact gpUp_mono _ k

/-- **Cofinality**: every `t < λ` lies below some `heFs λ k`. -/
theorem heFs_cof (t : Ordinal.{0}) (ht : t < l) : ∃ k, t < heFs l k := by
  rw [heFs_eq hl hl1]
  obtain ⟨k, hk⟩ := (Classical.choose_spec (he_surj hl1 hl.bot_lt)).2 t ht
  refine ⟨k + 1, ?_⟩
  rw [← hk]
  exact (gpUp_ge _ k).trans_lt (gpUp_mono _ k)

theorem heFs_mono' {j k : ℕ} (h : j ≤ k) : heFs l j ≤ heFs l k := by
  induction k, h using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact ih.trans (heFs_mono hl hl1 k).le

end Fs

/-! ## The level of a code -/

/-- **A countable code over a strongly critical `Z ≤ Ω₁` lies below `Z`.** -/
theorem he_cl_cnt {Z : Ordinal.{0}} (hZ : SC Z) {y : Ordinal.{0}} (hy : GxCl Z {gcG 0} y) (hy1 : y < Om 1) :
    y < Z := by
  induction hy with
  | small h => exact h
  | om => exact absurd hy1 (lt_irrefl _)
  | atom h =>
    rw [Set.mem_singleton_iff] at h
    rw [h] at hy1; exact absurd hy1 (not_lt.2 (gcG_Om1_lt 0).le)
  | @add u v _ _ ihu ihv =>
    exact hZ.isPrincipal (ihu (le_self_add.trans_lt hy1)) (ihv (le_add_self.trans_lt hy1))
  | @phi c b _ _ ihc ihb =>
    exact hZ.2 _ (ihc ((left_le_veblen c b).trans_lt hy1)) _ (ihb ((right_le_veblen c b).trans_lt hy1))

/-- **THE LEVEL OF A CODE**: a code over `Z` in `[φ(a, j), φ(a, j+1))` (`1 ≤ a < Ω₁`, `j` not a fixed point of
`φ(a, ·)`, `G < φ(a, j)`) has `a < Z`. -/
theorem he_cl_level {a : Ordinal.{0}} (ha : 1 ≤ a) (ha1 : a < Om 1) {Z j : Ordinal.{0}} (hZ : SC Z)
    (hZ1 : Z ≤ Om 1) (hj : j < veblen a j) (hGQ : gcG 0 < veblen a j) {y : Ordinal.{0}} (hy : GxCl Z {gcG 0} y)
    (hQy : veblen a j ≤ y) (hyZ : y < veblen a (j + 1)) : a < Z := by
  have hFE : InE (veblen a j) := gg_veblen_eps (Order.one_le_iff_ne_zero.1 ha)
  have hOF : Om 1 < veblen a j := (gcG_Om1_lt 0).trans hGQ
  induction hy with
  | small h => exact absurd hQy (not_le.2 (h.trans_le (hZ1.trans hOF.le)))
  | om => exact absurd hQy (not_le.2 hOF)
  | atom h =>
    rw [Set.mem_singleton_iff] at h
    rw [h] at hQy; exact absurd hQy (not_le.2 hGQ)
  | @add u v hu hv ihu ihv =>
    rcases le_or_gt (veblen a j) u with hFu | huF
    · exact ihu hFu (lt_of_le_of_lt le_self_add hyZ)
    · rcases le_or_gt (veblen a j) v with hFv | hvF
      · exact ihv hFv (lt_of_le_of_lt le_add_self hyZ)
      · exact absurd hQy (not_le.2 ((inE_indec hFE).add_lt huF hvF))
  | @phi c b hc hb ihc ihb =>
    have hbyZ : b < veblen a (j + 1) := lt_of_le_of_lt (right_le_veblen c b) hyZ
    rcases lt_or_ge c a with hca | hca
    · refine ihb ?_ hbyZ
      refine not_lt.1 fun hbF => ?_
      have hlt : veblen c b < veblen a j := by
        have h1 : veblen c b < veblen c (veblen a j) := (isNormal_veblen c).strictMono hbF
        rwa [veblen_veblen_of_lt hca] at h1
      exact absurd hQy (not_le.2 hlt)
    · rcases hca.lt_or_eq with hca' | hca'
      · exfalso
        have e3 : veblen a (veblen c b) = veblen c b := veblen_veblen_of_lt hca' b
        have h1 : j ≤ veblen c b := by
          have : veblen a j ≤ veblen a (veblen c b) := by rw [e3]; exact hQy
          exact (isNormal_veblen _).strictMono.le_iff_le.1 this
        have h2 : veblen c b < j + 1 := by
          have : veblen a (veblen c b) < veblen a (j + 1) := by rw [e3]; exact hyZ
          exact (isNormal_veblen _).strictMono.lt_iff_lt.1 this
        have e : veblen c b = j := le_antisymm (Order.lt_add_one_iff.1 h2) h1
        have : veblen a j = j := by rw [← e]; exact e3
        exact absurd this hj.ne'
      · subst hca'
        exact he_cl_cnt hZ hc ha1

/-! ## Readings of a level below a gate -/

/-- **LEMMA EXACT FOR `ϑᵖ(Ω₁·μ + t)` AT EVERY LEVEL `1 ≤ μ < σ`** from Lemma EXACT for `t`. -/
theorem he_glA_pi {μ σ ρ t : Ordinal.{0}} (hμσ : μ < σ) (hB : Bases σ ρ) (ht : t ∈ TB ρ σ) (htq : t < gq 1 ρ) :
    glA μ t ρ ∈ TB ρ σ ∧ pi σ ρ (glA μ t ρ) = glA μ (pi σ ρ t) σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hμρ : μ < ρ := hμσ.trans hB.2.2.1
  have hμT : μ ∈ Tset ρ ∧ μ < Om1 := ⟨mem_T_of_le hB.2.1 hρ1 hμρ.le, hμρ.trans hρ1⟩
  have h := glA_pi hB (mem_TB_of_lt hB hμσ) hμT.2 ht (gm1_T hB.2.1 hρ1 htq).2
  rw [pi_lt hB hμσ] at h
  exact h

/-- **A level below the gate lies in every hull `C(a, b)` with the gate below `b`.** -/
theorem he_cst_mem (S : InaccSeq.{0}) {μ γ a b : Ordinal.{0}} (hμγ : μ ≤ γ) (hγb : γ < b) : μ ∈ S.CSet a b :=
  CSet.of_lt (hμγ.trans_lt hγb)

/-! ## The wall of one gate -/

/-- **THE WALL OF ONE GATE**: for a start `S0` with `G < S0.B` and a base gate `γ ≥ ε₀`, the high-gate condition of
the start (the field `high0` of `Hd.HdMStart` at a base `F = G`) fails: at `c = G` (gate `0`) and `σ = ε₀`. -/
theorem he_high0_fails (S0 : HcVD) (hGB : gcG 0 < S0.B) {γ : Ordinal.{0}} (hγ : ε₀ ≤ γ) :
    ¬ ∀ c σ, gcG 0 ≤ c → c < S0.B → InE σ → σ < Om1 → S0.g c < σ → γ < σ := by
  intro H
  have hg : S0.g (gcG 0) < ε₀ := by rw [S0.g_G0 hGB]; exact hc_eps0_E.pos
  have := H (gcG 0) ε₀ le_rfl hGB hc_eps0_E gv_eps0_lt_Om1 hg
  exact absurd hγ (not_le.2 this)


/-! ## Raising the base gate of a system -/

/-- **RAISING THE BASE GATE**: the same system `T` with base gate `γ' ≥ T.γ` (every field that asks `γ < x` gets
weaker; `γ'` must be a gate of the bound `B`). -/
noncomputable def heRegate (T : HcVD) (γ' : Ordinal.{0}) (h1 : T.γ ≤ γ') (h2 : γ' < Om1)
    (h3 : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z {gcG 0} T.B → γ' < Z) (h4 : T.B = gcG 0 → γ' = 0) :
    HcVD :=
  { T with
    γ := γ'
    γ_lt := h2
    γ_cl := h3
    γ_G := h4
    ix_mem := fun S a b ha hb => T.ix_mem S a b ha (h1.trans_lt hb)
    R_lt_b := fun x hx hx1 hγ => T.R_lt_b x hx hx1 (h1.trans_lt hγ)
    b_cof := fun x hx hx1 hγ => T.b_cof x hx hx1 (h1.trans_lt hγ)
    b_E := fun x hx hx1 hγ => T.b_E x hx hx1 (h1.trans_lt hγ)
    x_lt_b := fun x hx hx1 hγ => T.x_lt_b x hx hx1 (h1.trans_lt hγ)
    b_eN := fun x hx hx1 hγ => T.b_eN x hx hx1 (h1.trans_lt hγ)
    ba_lt := fun x hx hx1 hγ => T.ba_lt x hx hx1 (h1.trans_lt hγ)
    b_Z := fun x hx hx1 hγ => T.b_Z x hx hx1 (h1.trans_lt hγ)
    b_pi := fun σ ρ hB hγ => T.b_pi σ ρ hB (h1.trans_lt hγ)
    ba_pi := fun σ ρ hB hγ => T.ba_pi σ ρ hB (h1.trans_lt hγ)
    dig := fun σ ρ hB hγ => T.dig σ ρ hB (h1.trans_lt hγ) }

section Regate

variable (T : HcVD) (γ' : Ordinal.{0}) (h1 : T.γ ≤ γ') (h2 : γ' < Om1)
  (h3 : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z {gcG 0} T.B → γ' < Z) (h4 : T.B = gcG 0 → γ' = 0)

theorem heRegate_γ : (heRegate T γ' h1 h2 h3 h4).γ = γ' := rfl
theorem heRegate_B : (heRegate T γ' h1 h2 h3 h4).B = T.B := rfl
theorem heRegate_R : (heRegate T γ' h1 h2 h3 h4).R = T.R := rfl
theorem heRegate_g : (heRegate T γ' h1 h2 h3 h4).g = T.g := rfl
theorem heRegate_b : (heRegate T γ' h1 h2 h3 h4).b = T.b := rfl
theorem heRegate_Z : (heRegate T γ' h1 h2 h3 h4).Z = T.Z := rfl
theorem heRegate_ix : (heRegate T γ' h1 h2 h3 h4).ix = T.ix := rfl

end Regate

/-- **THE GATE OF A LEVEL AT `G`**: a system with bound `φ(α, G+1)` (`1 ≤ α < Ω₁`, base gate `≤ α`) has the base
gate `α` raised (`he_cl_level`: a code of `φ(α, G+1)` over `Z` has `α < Z`). -/
noncomputable def heRegateG (T : HcVD) {α : Ordinal.{0}} (hα : 1 ≤ α) (hα1 : α < Om1) (hB : T.B = veblen α (gcG 0 + 1))
    (hγ : T.γ ≤ α) : HcVD :=
  heRegate T α hγ hα1
    (fun Z hZ hZ1 hc => by
      have hα1' : α < Om 1 := by rw [← Br.Om1_eq]; exact hα1
      have hα0 : α ≠ 0 := Order.one_le_iff_ne_zero.1 hα
      rw [hB] at hc
      exact he_cl_level hα hα1' hZ hZ1 (hd_succ_lt hα0 _)
        (((lt_add_one _).trans_le (right_le_veblen α _))) hc le_rfl
        ((isNormal_veblen α).strictMono (lt_add_one _)))
    (fun e => by
      exfalso
      rw [hB] at e
      have : gcG 0 < veblen α (gcG 0 + 1) := (lt_add_one _).trans_le (right_le_veblen α _)
      rw [e] at this; exact lt_irrefl _ this)

theorem heRegateG_γ (T : HcVD) {α : Ordinal.{0}} (hα : 1 ≤ α) (hα1 : α < Om1) (hB : T.B = veblen α (gcG 0 + 1))
    (hγ : T.γ ≤ α) : (heRegateG T hα hα1 hB hγ).γ = α := rfl

end Googology.Trans.PoR.InaccPsi.R2.He
