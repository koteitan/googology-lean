import Googology.Trans.PoR.InaccPsi.R2.GmG0S

/-!
# THE READING SYSTEM PAST `Γ_{Ω₁+1}` AND ITS FRONTIERS: the code `Γ_{Ω₁+1}` located, `sup = ι(Γ_{Γ_{Ω₁+1}·ω})`

* `mgRS` (**THE READING SYSTEM** of the codes below `Γ_{Ω₁+1}·ω`: code system `mgCS`, reading `mgR`, last terms
  `mgLD`, cofinal codes `Γ_{Ω₁+1}·(k+1)`, gate `0`);
* `mg_spec` (**the gated layer of every code `c = Γ_{Ω₁+1}·k + c'`**: gate `glG c'`, top
  `ϑˣ(Ω₁·Ω₁ + Γ_{x+1}·k + c'(x)) = Γ_{x+1+Γ_{x+1}·k+c'(x)}`), `mg_loc` (**every such code with gate below `ε₀`
  located**: `Λ⁺ = ι(Γ_{Ω₁+1+c}·ω)`, `P(⋯) < L(0)`), `mg_G0_read`, `mg_G0_loc` (**THE CODE `Γ_{Ω₁+1}`**: reading
  `Γ_{x+1}`, `Λ⁺ = ι(Γ_{Γ_{Ω₁+1}}·ω)`, `P(⋯) < L(0)`);
* `mgW_sup` (**`sup = ι(Γ_{Γ_{Ω₁+1}·ω})`, `P(Γ_{Γ_{Ω₁+1}·ω}) < L(0)`**), `mgFam_blk`, `mgFam_enum`, `mgFam_capV`,
  `mgFam_road`, `mg_fr_order` (**`ι(Γ_{Γ_{Ω₁+1}}) < ι(Γ_{Γ_{Ω₁+1}}·ω) < ι(Γ_{Γ_{Ω₁+1}·ω}) < ι(Ω₂)`**).

No new axiom.  New definition: `mgRS`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gm

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

theorem mgG_mulk (n : ℕ) : mgG (gcG 0 * n) = 0 := by
  have := mgG_split n gl_G0_E.pos
  rw [add_zero] at this; rw [this, glG_zero]

theorem mgR_mulk (n : ℕ) (x : Ordinal.{0}) : mgR (gcG 0 * n) x = lgG x * n := by
  have := mgR_split n gl_G0_E.pos x
  rw [add_zero, glR_zero, add_zero] at this; exact this

theorem mg_mulk_lt (n : ℕ) : gcG 0 * (n : Ordinal.{0}) < mgB :=
  (mul_lt_mul_iff_right₀ gl_G0_E.pos).2 (natCast_lt_omega0 n)

/-- **THE READING SYSTEM of the codes below `Γ_{Ω₁+1}·ω`.** -/
noncomputable def mgRS : GmRS where
  K := mgCS
  R := mgR
  E_lt := mg_E_lt_B
  B_lim := mgB_lim
  gt_E := mgG_E
  gt_lowE := fun _ hc => mgG_lowE hc
  R_E := fun x _ _ => mgR_E x
  lt0 := fun _ _ hx hx1 hc hg => mgR_lt1 hx hx1 hc hg
  mono := fun _ _ _ hx hx1 hc hbc hgb hgc => mgR_mono hx hx1 hc hbc hgb hgc
  succ := fun b x _ => mgR_succ b x
  gt_le_succ := mgG_le_succ
  cof := fun _ _ hx hx1 hc hEc hg _ hν => mgR_cofE hx hx1 hc hEc hg hν
  ex := fun _ _ _ hB hc hg => mgR_pi hB hc hg
  ld := mgLD
  cf := fun k => gcG 0 * ((k + 1 : ℕ) : Ordinal.{0})
  cf_ge := fun k => by rw [Nat.cast_succ, mul_add_one]; exact gfE_lt_G0.le.trans le_add_self
  cf_lt := fun k => mg_mulk_lt (k + 1)
  cf_g := fun k => by show mgG _ < ε₀; rw [mgG_mulk]; exact epsilon_pos 0
  cf_mono := fun k => (mul_lt_mul_iff_right₀ gl_G0_E.pos).2 (by exact_mod_cast Nat.lt_succ_self (k + 1))
  cf_cof := fun c hc => by
    obtain ⟨k, c', hc', rfl⟩ := mg_split hc
    refine ⟨k, ?_⟩
    show gcG 0 * k + c' < gcG 0 * ((k + 1 : ℕ) : Ordinal.{0})
    rw [Nat.cast_succ, mul_add_one]; exact (add_lt_add_iff_left _).2 hc'

theorem mgRS_V : mgRS.K.V = gcG mgB := rfl

/-- **THE GATED LAYER OF EVERY CODE `c ∈ [ε_{Ω₁+1}, Γ_{Ω₁+1}·ω)`**: gate `mgG c`, top `ϑˣ(Ω₁·Ω₁ + c(x))` at every
`ε`-number base `x < Ω₁` above the gate, `c(x) = Γ_{x+1}·k + c'(x)` for `c = Γ_{Ω₁+1}·k + c'`. -/
theorem mg_spec : ∀ c, gfE ≤ c → c < mgB → ∃ B : GdB, B.g = mgG c ∧
    ∀ x, InE x → x < Om1 → mgG c < x → B.K.E x = gq (mgR c x) x ∧ B.K.sys.top x = gq (mgR c x) x :=
  fun c h hc => ⟨mgRS.gmL c h hc, mgRS.gmL_g h hc, fun _ hx hx1 hg =>
    ⟨mgRS.gmL_E h hc hx hx1 hg, mgRS.gmL_top h hc hx hx1 hg⟩⟩

/-- **Every code `c ∈ [ε_{Ω₁+1}, Γ_{Ω₁+1}·ω)` with gate below `ε₀` located**: `Λ⁺ = ι(Γ_{Ω₁+1+c}·ω)`,
`υ` of it `= P(Γ_{Ω₁+1+c}·ω) < L(0)`. -/
theorem mg_loc {c : Ordinal.{0}} (h : gfE ≤ c) (hc : c < mgB) (hg : mgG c < ε₀) (S : InaccSeq.{0}) :
    xtB1 (mgRS.gmX c h hc hg) = iota S (gcG c * ω) ∧
    upsilon (xtB1 (mgRS.gmX c h hc hg)) = Pv S (gcG c * ω) ∧ Pv S (gcG c * ω) < Nc.ncL S 0 :=
  mgRS.gmLoc c h hc hg S

theorem mg_G0_one : gcG 0 = gcG 0 * ((1 : ℕ) : Ordinal.{0}) := by rw [Nat.cast_one, mul_one]

/-- **The code `Γ_{Ω₁+1}` reads `Γ_{x+1}`, gate `0`; its layer has top `Γ_{x+1+Γ_{x+1}} = ϑˣ(Ω₁·Ω₁ + Γ_{x+1})`.** -/
theorem mg_G0_read : mgG (gcG 0) = 0 ∧ ∀ x, mgR (gcG 0) x = lgG x := by
  refine ⟨?_, fun x => ?_⟩
  · rw [mg_G0_one]; exact mgG_mulk 1
  · rw [mg_G0_one, mgR_mulk 1, Nat.cast_one, mul_one]

/-- **THE CODE `Γ_{Ω₁+1}` LOCATED** (round 83 stopped there): its layer (top `ϑˣ(Ω₁·Ω₁ + Γ_{x+1})`) has
`Λ⁺ = ι(Γ_{Γ_{Ω₁+1}}·ω)`, `P(Γ_{Γ_{Ω₁+1}}·ω) < L(0)`. -/
theorem mg_G0_loc (S : InaccSeq.{0}) :
    ∃ (h1 : gfE ≤ gcG 0) (h2 : gcG 0 < mgB) (h3 : mgG (gcG 0) < ε₀),
      (∀ x, InE x → x < Om1 → (mgRS.gmL (gcG 0) h1 h2).K.sys.top x = gq (lgG x) x) ∧
      xtB1 (mgRS.gmX (gcG 0) h1 h2 h3) = iota S (gcG (gcG 0) * ω) ∧
      Pv S (gcG (gcG 0) * ω) < Nc.ncL S 0 := by
  have h3 : mgG (gcG 0) < ε₀ := by rw [mg_G0_read.1]; exact epsilon_pos 0
  obtain ⟨l1, -, l3⟩ := mg_loc gfE_lt_G0.le mg_G0_lt_B h3 S
  refine ⟨gfE_lt_G0.le, mg_G0_lt_B, h3, fun x hx hx1 => ?_, l1, l3⟩
  have hg : mgRS.K.gt (gcG 0) < x := by show mgG _ < x; rw [mg_G0_read.1]; exact hx.pos
  rw [mgRS.gmL_top gfE_lt_G0.le mg_G0_lt_B hx hx1 hg]
  show gq (mgR (gcG 0) x) x = _
  rw [mg_G0_read.2]

/-- **`sup = ι(Γ_{Γ_{Ω₁+1}·ω})`, `υ` of it `= P(Γ_{Γ_{Ω₁+1}·ω}) < L(0)`.** -/
theorem mgW_sup (S : InaccSeq.{0}) : (mgRS.gmFam S).famSup = iota S (gcG mgB) ∧
    upsilon (mgRS.gmFam S).famSup = Pv S (gcG mgB) ∧ Pv S (gcG mgB) < Nc.ncL S 0 :=
  mgRS.gmFam_sup S

/-- **Theorem BLK^O below `υ_{ι(Γ_{Γ_{Ω₁+1}·ω})} = P(Γ_{Γ_{Ω₁+1}·ω})`**, with the exact reaches. -/
theorem mgFam_blk (S : InaccSeq.{0}) :
    (∀ c d, c < d → d < upsilon (mgRS.gmFam S).famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < (mgRS.gmFam S).famSup ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < (mgRS.gmFam S).bd k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + (mgRS.gmFam S).off k l)) ∧
    (∀ α < upsilon (mgRS.gmFam S).famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  mgRS.gmFam_blk S

/-- **ENUM-REACH at every range restart below `ι(Γ_{Γ_{Ω₁+1}·ω})`, fixed points included.** -/
theorem mgFam_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG mgB)) :
    CdUpper S l ∧ CdLower S l := mgRS.gmFam_enum S hr hl

/-- **CapV at every range restart below `ι(Γ_{Γ_{Ω₁+1}·ω})`.** -/
theorem mgFam_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG mgB)) :
    CdCapV S l := mgRS.gmFam_capV S hr hl

/-- **THE ROAD past every code below `Γ_{Ω₁+1}·ω`**: UPPER, LOWER and CapV asked only at `λ ≥ ι(Γ_{Γ_{Ω₁+1}·ω})`
(CapV also `υ_λ < L(ω)`), (CL), EQ, TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the
reaches. -/
theorem mgFam_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG mgB) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG mgB) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG mgB) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  mgRS.gmFam_road S hU hL hV hC hEQ hrest hB2

/-- **The order of the frontiers**: `ι(Γ_{Γ_{Ω₁+1}}) < ι(Γ_{Γ_{Ω₁+1}}·ω) < ι(Γ_{Γ_{Ω₁+1}·ω}) < ι(Ω₂)`, and
`P(Γ_{Γ_{Ω₁+1}·ω}) < P(Ω₂) < L(0)`. -/
theorem mg_fr_order (S : InaccSeq.{0}) :
    iota S (gcG (gcG 0)) < iota S (gcG (gcG 0) * ω) ∧ iota S (gcG (gcG 0) * ω) < iota S (gcG mgB) ∧
      iota S (gcG mgB) < iota S (Om (1 + 1)) ∧ Pv S (gcG mgB) < Pv S (Om (1 + 1)) ∧
      Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hg : mgRS.K.gt (gcG 0) < ε₀ := by show mgG _ < ε₀; rw [mg_G0_read.1]; exact epsilon_pos 0
  obtain ⟨h1, h2, h3, h4⟩ := mgRS.gm_fr_order (c := gcG 0) mg_G0_lt_B hg S
  have hE : InE (gcG (gcG 0)) := geG_E (gcG 0)
  have h0 : gcG (gcG 0) < gcG (gcG 0) * ω := by
    conv_lhs => rw [← mul_one (gcG (gcG 0))]
    exact (mul_lt_mul_iff_right₀ hE.pos).2 one_lt_omega0
  exact ⟨cd_iota_lt_of_good (gmS_V_good S) h0, h1, h2, h3, h4⟩

end Googology.Trans.PoR.InaccPsi.R2.Gm
