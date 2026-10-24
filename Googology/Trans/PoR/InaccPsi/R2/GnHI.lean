import Googology.Trans.PoR.InaccPsi.R2.GnHL

/-!
# HEREDITARY CODES TO THE BASE `Γ_{Ω₁+1}` AS A READING SYSTEM: layers, frontiers and the road up to
`ι(Γ_{ε_{Γ_{Ω₁+1}+1}})`

The code system `gnK` (`R2.GnHX`), the hereditary reading `gnR` and the last terms (`R2.GnHL`) form a reading system
`gnRS : Gm.GmRS` with the cofinal codes `G, G^G, G^{G^G}, …` (gate `0`, `G = Γ_{Ω₁+1}`).  The generic results of
`R2.GmRS`, `R2.GmCodes`, `R2.GmLoc` give, for every code `c < ε_{G+1}`:

* `gn_spec` (**the gated layer of `c`**: gate `gnG c`, top `ϑˣ(Ω₁·Ω₁ + c(x)) = Γ_{x+1+c(x)}`, `c(x)` the hereditary
  reading with `G ↦ Γ_{x+1}`, `Ω₁ ↦ x`);
* `gnGk_loc` (**THE CODES `Γ_{Ω₁+1}^k`, `2 ≤ k < ω`, LOCATED**), `gnGw_loc` (**THE CODE `Γ_{Ω₁+1}^ω` LOCATED**, where
  round 84 stopped: top `Γ_{x+1+Γ_{x+1}^ω}`, `Λ⁺ = ι(Γ_{Ω₁+1+Γ_{Ω₁+1}^ω}·ω)`), `gnGG_loc` (**THE CODE
  `Γ_{Ω₁+1}^{Γ_{Ω₁+1}}` LOCATED**), `gnTw_loc` (every tower `G^{G^{⋯}}`);
* `gnW_sup` (**`sup = ι(Γ_{ε_{Γ_{Ω₁+1}+1}})`, `P(Γ_{ε_{Γ_{Ω₁+1}+1}}) < L(0)`**), `gnFam_enum` (**ENUM-REACH**, fixed
  points included), `gnFam_capV` (**CapV**), `gnFam_blk` (**BLK^O and the exact reaches**) below it, `gnFam_road`
  (**THE ROAD** with UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ_{ε_{Γ_{Ω₁+1}+1}})`), `gn_fr_order`.

No new axiom.  New definition: `gnRS`.
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

theorem gnR_succ_all (b x : Ordinal.{0}) : gnR (b + 1) x = gnR b x + 1 := by
  rcases lt_or_ge (b + 1) gnB with h | h
  · exact gnR_succ b h x
  · have hb : gnB ≤ b := by
      by_contra hb; push Not at hb; exact absurd (gnB_lim.add_one_lt hb) (not_lt.2 h)
    rw [gnR_high h, gnR_high hb]

theorem gnG_le_succ_all (b : Ordinal.{0}) : gnG b ≤ gnG (b + 1) := by
  rcases lt_or_ge (b + 1) gnB with h | h
  · exact gnG_le_succ b h
  · have hb : gnB ≤ b := by
      by_contra hb; push Not at hb; exact absurd (gnB_lim.add_one_lt hb) (not_lt.2 h)
    rw [gnG_high h, gnG_high hb]

/-- The gate of a power `G^k` (`1 ≤ k < ε_{G+1}`) is the gate of its exponent (`0` when finite). -/
theorem gnG_pow {k : Ordinal.{0}} (hk : k ≠ 0) (hkB : k < gnB) : gnG (gcG 0 ^ k) = gnQ k := by
  have e : gcG 0 ^ k = gcG 0 ^ k * 1 + 0 := by rw [mul_one, add_zero]
  rw [e, gnG_cnf hk one_ne_zero gn_one_lt (opow_pos _ gl_G0_E.pos) (by rw [← e]; exact gnB_gt_pow hkB), glQ_one,
    gnG_zero, max_eq_left zero_le, max_eq_left zero_le]

theorem gnR_pow {k : Ordinal.{0}} (hk : k ≠ 0) (hkB : k < gnB) (x : Ordinal.{0}) :
    gnR (gcG 0 ^ k) x = lgG x ^ gnR k x := by
  have e : gcG 0 ^ k = gcG 0 ^ k * 1 + 0 := by rw [mul_one, add_zero]
  rw [e, gnR_cnf hk one_ne_zero gn_one_lt (opow_pos _ gl_G0_E.pos) (by rw [← e]; exact gnB_gt_pow hkB),
    glR_one, mul_one, gnR_zero, add_zero]

theorem gnTw_g : ∀ n : ℕ, gnG (gnTw n) = 0
  | 0 => gnG_G
  | n + 1 => by
    show gnG (gcG 0 ^ gnTw n) = 0
    have h0 : gnTw n ≠ 0 := (gl_G0_E.pos.trans_le (gnTw_ge n)).ne'
    rw [gnG_pow h0 (gnTw_lt n)]
    unfold gnQ
    rw [if_neg (not_lt.2 ((omega0_lt_inE gl_G0_E).le.trans (gnTw_ge n))), gnTw_g n]

/-- **THE READING SYSTEM of the hereditary codes to the base `Γ_{Ω₁+1}` below `ε_{Γ_{Ω₁+1}+1}`.** -/
noncomputable def gnRS : GmRS where
  K := gnK
  R := gnR
  E_lt := gfE_lt_G0.trans gn_G0_lt_B
  B_lim := gnB_lim
  gt_E := by show gnG gfE = 0; rw [gnG_low gfE_lt_G0, glG_E]
  gt_lowE := fun c hc => by show gnG c = gtc c; rw [gnG_low (hc.trans gfE_lt_G0), glG_low hc]
  R_E := fun x _ _ => by rw [gnR_low gfE_lt_G0, glR_E]
  lt0 := fun _ _ hx hx1 hc hg => gnR_lt1 hx hx1 hc hg
  mono := fun b c _ hx hx1 hc hbc hgb hgc => gnR_mono hx hx1 c hc b hbc hgc hgb
  succ := fun b x _ => gnR_succ_all b x
  gt_le_succ := gnG_le_succ_all
  cof := fun _ _ hx hx1 hc hEc hg _ hν => gnR_cofE hx hx1 hc hEc hg hν
  ex := fun _ _ c hB hc hg => gnR_pi hB c hc hg
  ld := gnLD
  cf := gnTw
  cf_ge := fun k => gfE_lt_G0.le.trans (gnTw_ge k)
  cf_lt := gnTw_lt
  cf_g := fun n => by show gnG _ < ε₀; rw [gnTw_g n]; exact epsilon_pos 0
  cf_mono := gnTw_strict
  cf_cof := fun _ hc => gnTw_cof hc

theorem gnRS_V : gnRS.K.V = gcG gnB := rfl

/-- **THE GENERIC THEOREM for every hereditary code `c ∈ [ε_{Ω₁+1}, ε_{Γ_{Ω₁+1}+1})`**: a gated base package with
gate `gnG c` whose top is `ϑˣ(Ω₁·Ω₁ + c(x)) = Γ_{x+1+c(x)}` at every `ε`-number base `x < Ω₁` above the gate. -/
theorem gn_spec : ∀ c, gfE ≤ c → c < gnB → ∃ B : GdB, B.g = gnG c ∧
    ∀ x, InE x → x < Om1 → gnG c < x → B.K.E x = gq (gnR c x) x ∧ B.K.sys.top x = gq (gnR c x) x :=
  fun c h hc => ⟨gnRS.gmL c h hc, gnRS.gmL_g h hc, fun _ hx hx1 hg =>
    ⟨gnRS.gmL_E h hc hx hx1 hg, gnRS.gmL_top h hc hx hx1 hg⟩⟩

/-- **Every code with gate below `ε₀` located**: `Λ⁺ = ι(Γ_{Ω₁+1+c}·ω)`, `υ` of it `= P(⋯) < L(0)`. -/
theorem gn_loc {c : Ordinal.{0}} (h : gfE ≤ c) (hc : c < gnB) (hg : gnG c < ε₀) (S : InaccSeq.{0}) :
    xtB1 (gnRS.gmX c h hc hg) = iota S (gcG c * ω) ∧
    upsilon (xtB1 (gnRS.gmX c h hc hg)) = Pv S (gcG c * ω) ∧ Pv S (gcG c * ω) < Nc.ncL S 0 :=
  gnRS.gmLoc c h hc hg S

theorem gnGk_ge (k : ℕ) : gfE ≤ gcG 0 ^ ((k + 1 : ℕ) : Ordinal.{0}) :=
  gfE_lt_G0.le.trans (by
    calc gcG 0 = gcG 0 ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ _ := opow_le_opow_right gl_G0_E.pos (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)))

theorem gnGk_lt (k : ℕ) : gcG 0 ^ ((k + 1 : ℕ) : Ordinal.{0}) < gnB :=
  gnB_gt_pow ((gn_nat_lt_G0 _).trans gn_G0_lt_B)

theorem gnGk_g (k : ℕ) : gnG (gcG 0 ^ ((k + 1 : ℕ) : Ordinal.{0})) = 0 := by
  rw [gnG_pow (by exact_mod_cast Nat.succ_ne_zero k) ((gn_nat_lt_G0 _).trans gn_G0_lt_B), gnQ_nat]

/-- **THE CODES `Γ_{Ω₁+1}^{k+1}` LOCATED**: the layer has gate `0`, top `Γ_{x+1+Γ_{x+1}^{k+1}}` at every
`ε`-number base, `Λ⁺ = ι(Γ_{Ω₁+1+Γ_{Ω₁+1}^{k+1}}·ω)`, `P(⋯) < L(0)`. -/
theorem gnGk_loc (k : ℕ) (S : InaccSeq.{0}) :
    (∀ x, InE x → x < Om1 →
      (gnRS.gmL _ (gnGk_ge k) (gnGk_lt k)).K.sys.top x = gq (lgG x ^ ((k + 1 : ℕ) : Ordinal.{0})) x) ∧
    xtB1 (gnRS.gmX _ (gnGk_ge k) (gnGk_lt k) (by show gnG _ < ε₀; rw [gnGk_g k]; exact epsilon_pos 0)) =
      iota S (gcG (gcG 0 ^ ((k + 1 : ℕ) : Ordinal.{0})) * ω) ∧
    Pv S (gcG (gcG 0 ^ ((k + 1 : ℕ) : Ordinal.{0})) * ω) < Nc.ncL S 0 := by
  obtain ⟨h1, -, h3⟩ := gn_loc (gnGk_ge k) (gnGk_lt k) (by rw [gnGk_g k]; exact epsilon_pos 0) S
  refine ⟨fun x hx hx1 => ?_, h1, h3⟩
  have hg : gnG (gcG 0 ^ ((k + 1 : ℕ) : Ordinal.{0})) < x := by rw [gnGk_g k]; exact hx.pos
  rw [gnRS.gmL_top _ _ hx hx1 hg]
  show gq (gnR (gcG 0 ^ ((k + 1 : ℕ) : Ordinal.{0})) x) x = _
  rw [gnR_pow (by exact_mod_cast Nat.succ_ne_zero k) ((gn_nat_lt_G0 _).trans gn_G0_lt_B), gnR_nat]

theorem gnGw_ge : gfE ≤ gcG 0 ^ ω :=
  gfE_lt_G0.le.trans (by
    calc gcG 0 = gcG 0 ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ _ := opow_le_opow_right gl_G0_E.pos one_lt_omega0.le)

theorem gn_omega_lt_G0 : ω < gcG 0 := omega_lt_Om1.trans gl_Om1_lt_G0

theorem gnGw_lt : gcG 0 ^ ω < gnB := gnB_gt_pow (gn_omega_lt_G0.trans gn_G0_lt_B)

theorem gnGw_g : gnG (gcG 0 ^ ω) = ω := by
  rw [gnG_pow omega0_ne_zero (gn_omega_lt_G0.trans gn_G0_lt_B)]
  unfold gnQ
  rw [if_neg (lt_irrefl ω), gnG_low gn_omega_lt_G0, glG_low (omega_lt_Om1.trans Om1_lt_eW),
    (rdc_const omega_lt_Om1 0).2]

/-- **THE CODE `Γ_{Ω₁+1}^ω` LOCATED** (where round 84 stopped: its logend `Γ_{y+1}·ω = ω^{Γ_{y+1}+1}` needs Lemma IMG
above `Γ_{y+1}`, `R2.GnImg`): the layer of `G^ω` has gate `ω`, top `Γ_{x+1+Γ_{x+1}^ω}` at every `ε`-number base
`x > ω`, `Λ⁺ = ι(Γ_{Ω₁+1+Γ_{Ω₁+1}^ω}·ω)`, `υ` of it `= P(⋯) < L(0)`. -/
theorem gnGw_loc (S : InaccSeq.{0}) :
    (∀ x, InE x → x < Om1 → ω < x →
      (gnRS.gmL (gcG 0 ^ ω) gnGw_ge gnGw_lt).K.sys.top x = gq (lgG x ^ ω) x) ∧
    xtB1 (gnRS.gmX (gcG 0 ^ ω) gnGw_ge gnGw_lt (by show gnG _ < ε₀; rw [gnGw_g]; exact omega0_lt_epsilon 0)) =
      iota S (gcG (gcG 0 ^ ω) * ω) ∧
    upsilon (xtB1 (gnRS.gmX (gcG 0 ^ ω) gnGw_ge gnGw_lt
      (by show gnG _ < ε₀; rw [gnGw_g]; exact omega0_lt_epsilon 0))) = Pv S (gcG (gcG 0 ^ ω) * ω) ∧
    Pv S (gcG (gcG 0 ^ ω) * ω) < Nc.ncL S 0 := by
  refine ⟨fun x hx hx1 hωx => ?_, gnRS.gmLoc _ _ _ _ S⟩
  have hg : gnG (gcG 0 ^ ω) < x := by rw [gnGw_g]; exact hωx
  rw [gnRS.gmL_top _ _ hx hx1 hg]
  show gq (gnR (gcG 0 ^ ω) x) x = _
  rw [gnR_pow omega0_ne_zero (gn_omega_lt_G0.trans gn_G0_lt_B), gnR_low gn_omega_lt_G0,
    glR_low (omega_lt_Om1.trans Om1_lt_eW), (rdc_const omega_lt_Om1 x).1]

/-- **Every tower `G^{G^{⋯}}` located**: its layer has gate `0` and top `Γ_{x+1+(tower at x)}`,
`Λ⁺ = ι(Γ_{Ω₁+1+tower}·ω)`, `υ` of it `= P(⋯) < L(0)`. -/
theorem gnTw_loc (n : ℕ) (S : InaccSeq.{0}) :
    xtB1 (gnRS.gmXk n) = iota S (gcG (gnTw n) * ω) ∧
    upsilon (xtB1 (gnRS.gmXk n)) = Pv S (gcG (gnTw n) * ω) ∧ Pv S (gcG (gnTw n) * ω) < Nc.ncL S 0 :=
  gnRS.gmLoc _ _ _ _ S

/-- **THE CODE `Γ_{Ω₁+1}^{Γ_{Ω₁+1}}` LOCATED**: its layer has top `Γ_{x+1+Γ_{x+1}^{Γ_{x+1}}}` at every `ε`-number base,
`Λ⁺ = ι(Γ_{Ω₁+1+G^G}·ω)`, `P(⋯) < L(0)`. -/
theorem gnGG_loc (S : InaccSeq.{0}) :
    (∀ x, InE x → x < Om1 →
      (gnRS.gmL (gcG 0 ^ gcG 0) (gfE_lt_G0.le.trans (gnTw_ge 1)) (gnTw_lt 1)).K.sys.top x = gq (lgG x ^ lgG x) x) ∧
    xtB1 (gnRS.gmXk 1) = iota S (gcG (gcG 0 ^ gcG 0) * ω) ∧ Pv S (gcG (gcG 0 ^ gcG 0) * ω) < Nc.ncL S 0 := by
  obtain ⟨h1, -, h3⟩ := gnTw_loc 1 S
  refine ⟨fun x hx hx1 => ?_, h1, h3⟩
  have hg : gnG (gcG 0 ^ gcG 0) < x := by
    show gnG (gnTw 1) < x
    rw [gnTw_g 1]; exact hx.pos
  rw [gnRS.gmL_top _ _ hx hx1 hg]
  show gq (gnR (gcG 0 ^ gcG 0) x) x = _
  rw [gnR_pow mg_G0_ne gn_G0_lt_B, gnR_G]

/-- **`sup = ι(Γ_{ε_{Γ_{Ω₁+1}+1}})`, `υ` of it `= P(Γ_{ε_{Γ_{Ω₁+1}+1}}) < L(0)`.** -/
theorem gnW_sup (S : InaccSeq.{0}) : (gnRS.gmFam S).famSup = iota S (gcG gnB) ∧
    upsilon (gnRS.gmFam S).famSup = Pv S (gcG gnB) ∧ Pv S (gcG gnB) < Nc.ncL S 0 := gnRS.gmFam_sup S

/-- **Theorem BLK^O below `υ_{ι(Γ_{ε_{G+1}})} = P(Γ_{ε_{G+1}})`**, with the exact reaches. -/
theorem gnFam_blk (S : InaccSeq.{0}) :
    (∀ c d, c < d → d < upsilon (gnRS.gmFam S).famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < (gnRS.gmFam S).famSup ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < (gnRS.gmFam S).bd k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + (gnRS.gmFam S).off k l)) ∧
    (∀ α < upsilon (gnRS.gmFam S).famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  gnRS.gmFam_blk S

/-- **ENUM-REACH at every range restart below `ι(Γ_{ε_{Γ_{Ω₁+1}+1}})`, fixed points included.** -/
theorem gnFam_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG gnB)) :
    CdUpper S l ∧ CdLower S l := gnRS.gmFam_enum S hr hl

/-- **CapV at every range restart below `ι(Γ_{ε_{Γ_{Ω₁+1}+1}})`.** -/
theorem gnFam_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG gnB)) :
    CdCapV S l := gnRS.gmFam_capV S hr hl

/-- **THE ROAD past every hereditary code to the base `Γ_{Ω₁+1}`**: UPPER, LOWER and CapV asked only at
`λ ≥ ι(Γ_{ε_{Γ_{Ω₁+1}+1}})` (CapV also `υ_λ < L(ω)`), (CL), EQ, TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`,
`L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem gnFam_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG gnB) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG gnB) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG gnB) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gnRS.gmFam_road S hU hL hV hC hEQ hrest hB2

theorem gn_mqB_lt_B : mqB < gnB := by
  have h2 : mqB = gcG 0 ^ (2 : Ordinal.{0}) := by
    unfold mqB; rw [show (2 : Ordinal.{0}) = 1 + 1 from (one_add_one_eq_two).symm, opow_add, opow_one]
  rw [h2]; exact gnB_gt_pow ((by exact_mod_cast gn_nat_lt_G0 2 : (2 : Ordinal.{0}) < gcG 0).trans gn_G0_lt_B)

/-- **The order of the frontiers**: `ι(Γ_{Γ_{Ω₁+1}²}) < ι(Γ_{Ω₁+1+Γ_{Ω₁+1}^ω}·ω) < ι(Γ_{ε_{Γ_{Ω₁+1}+1}}) < ι(Ω₂)`, and
`P(Γ_{ε_{Γ_{Ω₁+1}+1}}) < P(Ω₂) < L(0)`. -/
theorem gn_fr_order (S : InaccSeq.{0}) :
    iota S (gcG mqB) < iota S (gcG (gcG 0 ^ ω) * ω) ∧ iota S (gcG (gcG 0 ^ ω) * ω) < iota S (gcG gnB) ∧
      iota S (gcG gnB) < iota S (Om (1 + 1)) ∧ Pv S (gcG gnB) < Pv S (Om (1 + 1)) ∧
      Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hBw : mqB < gcG 0 ^ ω := by
    have h2 : mqB = gcG 0 ^ (2 : Ordinal.{0}) := by
      unfold mqB; rw [show (2 : Ordinal.{0}) = 1 + 1 from (one_add_one_eq_two).symm, opow_add, opow_one]
    rw [h2]; exact (opow_lt_opow_iff_right gn_one_lt).2 (nat_lt_omega0 2)
  have h1 : iota S (gcG mqB) < iota S (gcG (gcG 0 ^ ω) * ω) :=
    cd_iota_lt_of_good (gmV_good mqCS S)
      ((gcG_lt hBw).trans (lt_mul_of_one_lt_right (gcG_SC _).1 one_lt_omega0))
  obtain ⟨h2, h3, h4, h5⟩ := gnRS.gm_fr_order gnGw_lt (by show gnG _ < ε₀; rw [gnGw_g]; exact omega0_lt_epsilon 0) S
  exact ⟨h1, h2, h3, h4, h5⟩

end Googology.Trans.PoR.InaccPsi.R2.Gn
