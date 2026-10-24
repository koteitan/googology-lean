import Googology.Trans.PoR.InaccPsi.R2.GnE1

/-!
# THE CODES `ε_{Γ_{Ω₁+1}+1}·k + c'` AS A READING SYSTEM: the code `ε_{Γ_{Ω₁+1}+1}` located, frontiers and the road up
to `ι(Γ_{ε_{Γ_{Ω₁+1}+1}·ω})`

* `neRS` (**THE READING SYSTEM** below `ε_{G+1}·ω`: code system `neCS`, reading `neR`, last terms `neLD`, cofinal
  codes `ε_{G+1}·(k+1)`, gate `0`);
* `ne_spec` (**the gated layer of every code `c = ε_{G+1}·k + c'`**: top `ϑˣ(Ω₁·Ω₁ + ε_{Γ_{x+1}+1}·k + c'(x))`),
  `ne_loc`, `neE1_loc` (**THE CODE `ε_{Γ_{Ω₁+1}+1}` LOCATED**: top `Γ_{x+1+ε_{Γ_{x+1}+1}}`,
  `Λ⁺ = ι(Γ_{Ω₁+1+ε_{Γ_{Ω₁+1}+1}}·ω)`, `P(⋯) < L(0)`);
* `neW_sup` (**`sup = ι(Γ_{ε_{Γ_{Ω₁+1}+1}·ω})`, `P(Γ_{ε_{Γ_{Ω₁+1}+1}·ω}) < L(0)`**), `neFam_blk`, `neFam_enum`,
  `neFam_capV`, `neFam_road`, `ne_fr_order` (**`ι(Γ_{ε_{G+1}}) < ι(Γ_{ε_{G+1}}·ω) < ι(Γ_{ε_{G+1}·ω}) < ι(Ω₂)`**).

No new axiom.  New definition: `neRS`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gn

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

theorem neG_mulk (k : ℕ) : neG (gnB * ((k + 1 : ℕ) : Ordinal.{0})) = 0 := by
  have := neG_split (k + 1) gnB_E.pos
  rw [add_zero] at this; rw [this, gnG_zero]

theorem ne_E1_le_mulk (k : ℕ) : gnB ≤ gnB * ((k + 1 : ℕ) : Ordinal.{0}) :=
  le_mul_of_one_le_right' (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))

/-- **THE READING SYSTEM of the codes below `ε_{Γ_{Ω₁+1}+1}·ω`.** -/
noncomputable def neRS : GmRS where
  K := neCS
  R := neR
  E_lt := ne_E_lt_B
  B_lim := neB_lim
  gt_E := neG_E
  gt_lowE := fun _ hc => neG_lowE hc
  R_E := fun x _ _ => neR_E x
  lt0 := fun _ _ hx hx1 hc hg => neR_lt1 hx hx1 hc hg
  mono := fun _ _ _ hx hx1 hc hbc hgb hgc => neR_mono hx hx1 hc hbc hgb hgc
  succ := fun b x _ => neR_succ b x
  gt_le_succ := neG_le_succ
  cof := fun _ _ hx hx1 hc hEc hg _ hν => neR_cofE hx hx1 hc hEc hg hν
  ex := fun _ _ _ hB hc hg => neR_pi hB hc hg
  ld := neLD
  cf := fun k => gnB * ((k + 1 : ℕ) : Ordinal.{0})
  cf_ge := fun k => ((gfE_lt_G0.trans gn_G0_lt_B).le).trans (ne_E1_le_mulk k)
  cf_lt := fun k => (mul_lt_mul_iff_right₀ gnB_E.pos).2 (natCast_lt_omega0 _)
  cf_g := fun k => by show neG _ < ε₀; rw [neG_mulk]; exact epsilon_pos 0
  cf_mono := fun k => (mul_lt_mul_iff_right₀ gnB_E.pos).2 (by exact_mod_cast Nat.lt_succ_self (k + 1))
  cf_cof := fun c hc => by
    obtain ⟨k, c', hc', rfl⟩ := ne_split hc
    refine ⟨k, ?_⟩
    show gnB * k + c' < gnB * ((k + 1 : ℕ) : Ordinal.{0})
    rw [Nat.cast_succ, mul_add_one]; exact (add_lt_add_iff_left _).2 hc'

theorem neRS_V : neRS.K.V = gcG neB := rfl

/-- **THE GATED LAYER OF EVERY CODE `c ∈ [ε_{Ω₁+1}, ε_{G+1}·ω)`**: gate `neG c`, top `ϑˣ(Ω₁·Ω₁ + c(x))` at every
`ε`-number base `x < Ω₁` above the gate, `c(x) = ε_{Γ_{x+1}+1}·k + c'(x)` for `c = ε_{G+1}·k + c'`. -/
theorem ne_spec : ∀ c, gfE ≤ c → c < neB → ∃ B : GdB, B.g = neG c ∧
    ∀ x, InE x → x < Om1 → neG c < x → B.K.E x = gq (neR c x) x ∧ B.K.sys.top x = gq (neR c x) x :=
  fun c h hc => ⟨neRS.gmL c h hc, neRS.gmL_g h hc, fun _ hx hx1 hg =>
    ⟨neRS.gmL_E h hc hx hx1 hg, neRS.gmL_top h hc hx hx1 hg⟩⟩

/-- **Every code `c ∈ [ε_{Ω₁+1}, ε_{G+1}·ω)` with gate below `ε₀` located**: `Λ⁺ = ι(Γ_{Ω₁+1+c}·ω)`,
`P(Γ_{Ω₁+1+c}·ω) < L(0)`. -/
theorem ne_loc {c : Ordinal.{0}} (h : gfE ≤ c) (hc : c < neB) (hg : neG c < ε₀) (S : InaccSeq.{0}) :
    xtB1 (neRS.gmX c h hc hg) = iota S (gcG c * ω) ∧
    upsilon (xtB1 (neRS.gmX c h hc hg)) = Pv S (gcG c * ω) ∧ Pv S (gcG c * ω) < Nc.ncL S 0 :=
  neRS.gmLoc c h hc hg S

theorem neE1_ge : gfE ≤ gnB := (gfE_lt_G0.trans gn_G0_lt_B).le

theorem neE1_g : neG gnB = 0 := by
  have := neG_mulk 0
  rwa [Nat.cast_one, mul_one] at this

/-- **THE CODE `ε_{Γ_{Ω₁+1}+1}` LOCATED** (the first `φ`-code above `Γ_{Ω₁+1}`, where `R2.GnHI` stops): its layer has
gate `0`, top `ϑˣ(Ω₁·Ω₁ + ε_{Γ_{x+1}+1}) = Γ_{x+1+ε_{Γ_{x+1}+1}}` at every `ε`-number base,
`Λ⁺ = ι(Γ_{Ω₁+1+ε_{Γ_{Ω₁+1}+1}}·ω)`, `υ` of it `= P(⋯) < L(0)`. -/
theorem neE1_loc (S : InaccSeq.{0}) :
    (∀ x, InE x → x < Om1 → (neRS.gmL gnB neE1_ge ne_E1_lt_B).K.sys.top x = gq (eN (lgG x)) x) ∧
    xtB1 (neRS.gmX gnB neE1_ge ne_E1_lt_B (by show neG _ < ε₀; rw [neE1_g]; exact epsilon_pos 0)) =
      iota S (gcG gnB * ω) ∧
    upsilon (xtB1 (neRS.gmX gnB neE1_ge ne_E1_lt_B (by show neG _ < ε₀; rw [neE1_g]; exact epsilon_pos 0))) =
      Pv S (gcG gnB * ω) ∧ Pv S (gcG gnB * ω) < Nc.ncL S 0 := by
  refine ⟨fun x hx hx1 => ?_, neRS.gmLoc _ _ _ _ S⟩
  have hg : neG gnB < x := by rw [neE1_g]; exact hx.pos
  rw [neRS.gmL_top _ _ hx hx1 hg]
  show gq (neR gnB x) x = _
  have e : gnB = gnB * ((1 : ℕ) : Ordinal.{0}) + 0 := by rw [Nat.cast_one, mul_one, add_zero]
  rw [e, neR_split 1 gnB_E.pos x, gnR_zero, add_zero, Nat.cast_one, mul_one]

/-- **`sup = ι(Γ_{ε_{Γ_{Ω₁+1}+1}·ω})`, `υ` of it `= P(Γ_{ε_{Γ_{Ω₁+1}+1}·ω}) < L(0)`.** -/
theorem neW_sup (S : InaccSeq.{0}) : (neRS.gmFam S).famSup = iota S (gcG neB) ∧
    upsilon (neRS.gmFam S).famSup = Pv S (gcG neB) ∧ Pv S (gcG neB) < Nc.ncL S 0 := neRS.gmFam_sup S

/-- **Theorem BLK^O below `P(Γ_{ε_{G+1}·ω})`**, with the exact reaches. -/
theorem neFam_blk (S : InaccSeq.{0}) :
    (∀ c d, c < d → d < upsilon (neRS.gmFam S).famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < (neRS.gmFam S).famSup ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < (neRS.gmFam S).bd k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + (neRS.gmFam S).off k l)) ∧
    (∀ α < upsilon (neRS.gmFam S).famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  neRS.gmFam_blk S

/-- **ENUM-REACH at every range restart below `ι(Γ_{ε_{Γ_{Ω₁+1}+1}·ω})`, fixed points included.** -/
theorem neFam_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG neB)) :
    CdUpper S l ∧ CdLower S l := neRS.gmFam_enum S hr hl

/-- **CapV at every range restart below `ι(Γ_{ε_{Γ_{Ω₁+1}+1}·ω})`.** -/
theorem neFam_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG neB)) :
    CdCapV S l := neRS.gmFam_capV S hr hl

/-- **THE ROAD past every code below `ε_{Γ_{Ω₁+1}+1}·ω`**: UPPER, LOWER and CapV asked only at
`λ ≥ ι(Γ_{ε_{Γ_{Ω₁+1}+1}·ω})` (CapV also `υ_λ < L(ω)`), (CL), EQ, TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`,
`L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem neFam_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG neB) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG neB) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG neB) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  neRS.gmFam_road S hU hL hV hC hEQ hrest hB2

/-- **The order of the frontiers**: `ι(Γ_{ε_{G+1}}) < ι(Γ_{ε_{G+1}}·ω) < ι(Γ_{ε_{G+1}·ω}) < ι(Ω₂)` (`G = Γ_{Ω₁+1}`), and
`P(Γ_{ε_{G+1}·ω}) < P(Ω₂) < L(0)`. -/
theorem ne_fr_order (S : InaccSeq.{0}) :
    iota S (gcG gnB) < iota S (gcG gnB * ω) ∧ iota S (gcG gnB * ω) < iota S (gcG neB) ∧
      iota S (gcG neB) < iota S (Om (1 + 1)) ∧ Pv S (gcG neB) < Pv S (Om (1 + 1)) ∧
      Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have h1 : iota S (gcG gnB) < iota S (gcG gnB * ω) :=
    cd_iota_lt_of_good (gmV_good gnK S) (lt_mul_of_one_lt_right (gcG_SC _).1 one_lt_omega0)
  obtain ⟨h2, h3, h4, h5⟩ := neRS.gm_fr_order ne_E1_lt_B (by show neG _ < ε₀; rw [neE1_g]; exact epsilon_pos 0) S
  exact ⟨h1, h2, h3, h4, h5⟩

end Googology.Trans.PoR.InaccPsi.R2.Gn
