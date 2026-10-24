import Googology.Trans.PoR.InaccPsi.R2.GjHL

/-!
# HEREDITARY CODES BELOW `ε_{Ω₁+2}` AS A READING SYSTEM: layers, frontiers and the road up to `ι(Γ_{Ω₁+1+ε_{Ω₁+2}})`

The code system `jhK` (`R2.GjHX`), the hereditary reading `jhR` and the last terms (`R2.GjHL`) form a reading system
`jhRS` (`R2.GiRS`) with the cofinal codes `E, E^E, E^{E^E}, …` (gate `0`).  The generic results of `R2.GiRS`,
`R2.GiCodes`, `R2.GiLoc` give, for every code `c < ε_{Ω₁+2} = ε_{E+1}` (`E = ε_{Ω₁+1}`):

* `jh_spec` (**the gated layer of `c`**: gate `jhG c`, top `ϑˣ(Ω₁·Ω₁ + c(x)) = Γ_{x+1+c(x)}`, `c(x)` the hereditary
  reading with `E ↦ ε_{x+1}`, `Ω₁ ↦ x`);
* `jhEw_loc` (**THE CODE `ε_{Ω₁+1}^ω` LOCATED**, where round 80 stopped), `jhEE_loc` (**THE CODE
  `ε_{Ω₁+1}^{ε_{Ω₁+1}}` LOCATED**: top `Γ_{x+1+ε_{x+1}^{ε_{x+1}}}`, `Λ⁺ = ι(Γ_{Ω₁+1+E^E}·ω)`), `jhTw_loc` (every tower
  `E^{E^{⋯}}`);
* `jhW_sup` (**`sup = ι(Γ_{Ω₁+1+ε_{Ω₁+2}})`, `P(Γ_{Ω₁+1+ε_{Ω₁+2}}) < L(0)`**), `jhW_fr_order` (past
  `ι(Γ_{Ω₁+1+E^E})`), `jhFam_enum` (**ENUM-REACH**), `jhFam_capV` (**CapV**) below `ι(Γ_{Ω₁+1+ε_{Ω₁+2}})`,
  `jhFam_road` (**THE ROAD** with UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ_{Ω₁+1+ε_{Ω₁+2}})`); `jhRS.giBlk`,
  `jhRS.giFam_blk` (BLK^O and the exact reaches) are the generic theorems at `RS := jhRS`.

No new axiom.  New definition: `jhRS`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gj

open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gi
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd

theorem jhR_succ_all (b x : Ordinal.{0}) : jhR (b + 1) x = jhR b x + 1 := by
  rcases lt_or_ge (b + 1) jhB with h | h
  · exact jhR_succ b h x
  · have hb : jhB ≤ b := by
      by_contra hb; push Not at hb; exact absurd (jhB_lim.add_one_lt hb) (not_lt.2 h)
    rw [jhR_high h, jhR_high hb]

theorem jhG_le_succ_all (b : Ordinal.{0}) : jhG b ≤ jhG (b + 1) := by
  rcases lt_or_ge (b + 1) jhB with h | h
  · exact jhG_le_succ b h
  · have hb : jhB ≤ b := by
      by_contra hb; push Not at hb; exact absurd (jhB_lim.add_one_lt hb) (not_lt.2 h)
    rw [jhG_high h, jhG_high hb]

/-- The gate of a power `E^k` (`1 ≤ k < ε_{Ω₁+2}`) is the gate of its exponent (`0` when finite). -/
theorem jhG_pow {k : Ordinal.{0}} (hk : k ≠ 0) (hkB : k < jhB) : jhG (gfE ^ k) = jhQ k := by
  have e : gfE ^ k = gfE ^ k * 1 + 0 := by rw [mul_one, add_zero]
  rw [e, jhG_cnf hk one_ne_zero gw_one_lt (opow_pos _ eW_E.pos) (by rw [← e]; exact jhB_gt_pow hkB), giQ_one,
    jhG_zero, max_eq_left zero_le, max_eq_left zero_le]

theorem jhR_pow {k : Ordinal.{0}} (hk : k ≠ 0) (hkB : k < jhB) (x : Ordinal.{0}) :
    jhR (gfE ^ k) x = eN x ^ jhR k x := by
  have e : gfE ^ k = gfE ^ k * 1 + 0 := by rw [mul_one, add_zero]
  rw [e, jhR_cnf hk one_ne_zero gw_one_lt (opow_pos _ eW_E.pos) (by rw [← e]; exact jhB_gt_pow hkB),
    (rdc_const gf_one_lt_Om1 x).1, mul_one, jhR_zero, add_zero]

theorem jhTw_g : ∀ n : ℕ, jhG (jhTw n) = 0
  | 0 => jhG_E
  | n + 1 => by
    show jhG (gfE ^ jhTw n) = 0
    have h0 : jhTw n ≠ 0 := (eW_E.pos.trans_le (jhTw_ge n)).ne'
    rw [jhG_pow h0 (jhTw_lt n)]
    unfold jhQ
    rw [if_neg (not_lt.2 ((omega_lt_Om1.trans Om1_lt_eW).le.trans (jhTw_ge n))), jhTw_g n]

/-- **THE READING SYSTEM of the hereditary codes below `ε_{Ω₁+2}`.** -/
noncomputable def jhRS : GiRS where
  K := jhK
  R := jhR
  E_lt := gfE_lt_jhB
  B_lim := jhB_lim
  gt_E := jhG_E
  gt_lowE := fun _ hc => jhG_low hc
  R_E := jhR_E
  lt0 := fun _ _ hx hx1 hc hg => jhR_lt0 hx hx1 hc hg
  mono := fun b c _ hx hc hbc hgb hgc => jhR_mono hx c hc b hbc hgc hgb
  succ := jhR_succ_all
  gt_le_succ := jhG_le_succ_all
  cof := fun _ _ hx hx1 hc hEc hg _ hν => jhR_cofE hx hx1 hc hEc hg hν
  ex := fun _ _ c hB hc hg => jhR_pi hB c hc hg
  ld := jhLD_ne
  cf := jhTw
  cf_ge := jhTw_ge
  cf_lt := jhTw_lt
  cf_g := fun n => by rw [show jhK.gt = jhG from rfl, jhTw_g n]; exact epsilon_pos 0
  cf_mono := jhTw_strict
  cf_cof := fun _ hc => jhTw_cof hc

theorem jhRS_V : jhRS.K.V = gcG jhB := rfl

/-- **THE GENERIC THEOREM for every hereditary code `c ∈ [ε_{Ω₁+1}, ε_{Ω₁+2})`**: a gated base package (a gated layer
with EXACT, IMG, RS and the top witness as fields) with gate `jhG c` whose top is `ϑˣ(Ω₁·Ω₁ + c(x)) = Γ_{x+1+c(x)}` at
every `ε`-number base `x < Ω₁` above the gate. -/
theorem jh_spec : ∀ c, gfE ≤ c → c < jhB → ∃ B : GdB, B.g = jhG c ∧
    ∀ x, InE x → x < Om1 → jhG c < x → B.K.E x = gq (jhR c x) x ∧ B.K.sys.top x = gq (jhR c x) x :=
  fun c h hc => ⟨jhRS.giL c h hc, jhRS.giL_g h hc, fun x hx hx1 hg =>
    ⟨jhRS.giL_E h hc hx hx1 hg, jhRS.giL_top h hc hx hx1 hg⟩⟩

/-- **Every tower `E^{E^{⋯}}` located**: its layer has gate `0` and top `Γ_{x+1+(tower at x)}`,
`Λ⁺ = ι(Γ_{Ω₁+1+tower}·ω)`, `υ` of it `= P(⋯) < L(0)`. -/
theorem jhTw_loc (n : ℕ) (S : InaccSeq.{0}) :
    xtB1 (jhRS.giXk n) = iota S (gcG (jhTw n) * ω) ∧
    upsilon (xtB1 (jhRS.giXk n)) = Pv S (gcG (jhTw n) * ω) ∧ Pv S (gcG (jhTw n) * ω) < Nc.ncL S 0 :=
  jhRS.giLoc _ _ _ _ S

/-- **THE CODE `ε_{Ω₁+1}^{ε_{Ω₁+1}}` LOCATED** (the first code whose exponent is not a code of `R2.GfSub`): its layer
has top `Γ_{x+1+ε_{x+1}^{ε_{x+1}}}` at every `ε`-number base, `Λ⁺ = ι(Γ_{Ω₁+1+E^E}·ω)`, `P(⋯) < L(0)`. -/
theorem jhEE_loc (S : InaccSeq.{0}) :
    (∀ x, InE x → x < Om1 → (jhRS.giL (gfE ^ gfE) (jhTw_ge 1) (jhTw_lt 1)).K.sys.top x = gq (eN x ^ eN x) x) ∧
    xtB1 (jhRS.giXk 1) = iota S (gcG (gfE ^ gfE) * ω) ∧ Pv S (gcG (gfE ^ gfE) * ω) < Nc.ncL S 0 := by
  obtain ⟨h1, -, h3⟩ := jhTw_loc 1 S
  refine ⟨fun x hx hx1 => ?_, h1, h3⟩
  have hg : jhG (gfE ^ gfE) < x := by
    show jhG (jhTw 1) < x
    rw [jhTw_g 1]; exact hx.pos
  rw [jhRS.giL_top _ _ hx hx1 hg]
  show gq (jhR (gfE ^ gfE) x) x = _
  rw [jhR_pow gfE_ne gfE_lt_jhB, jhR_E]

theorem jhEw_ge : gfE ≤ gfE ^ ω := by
  calc gfE = gfE ^ (1 : Ordinal.{0}) := (opow_one _).symm
    _ ≤ _ := opow_le_opow_right eW_E.pos one_lt_omega0.le

theorem jhEw_lt : gfE ^ ω < jhB := jhB_gt_pow ((omega_lt_Om1.trans Om1_lt_eW).trans gfE_lt_jhB)

theorem jhEw_g : jhG (gfE ^ ω) = ω := by
  have hωE : ω < gfE := omega_lt_Om1.trans Om1_lt_eW
  rw [jhG_pow omega0_ne_zero (hωE.trans gfE_lt_jhB)]
  unfold jhQ
  rw [if_neg (lt_irrefl ω), jhG_low hωE, (rdc_const omega_lt_Om1 0).2]

/-- **THE CODE `ε_{Ω₁+1}^ω` LOCATED** (where round 80 stopped: its logend `ω^{ε_{x+1}+1}` needs Lemma IMG for a
specified function, `Gj.gjPkg_of_ex`): the layer of `E^ω` has gate `ω`, top `Γ_{x+1+ε_{x+1}^ω}` at every `ε`-number base
`x > ω`, `Λ⁺ = ι(Γ_{Ω₁+1+E^ω}·ω)`, `υ` of it `= P(Γ_{Ω₁+1+E^ω}·ω) < L(0)`. -/
theorem jhEw_loc (S : InaccSeq.{0}) :
    (∀ x, InE x → x < Om1 → ω < x →
      (jhRS.giL (gfE ^ ω) jhEw_ge jhEw_lt).K.sys.top x = gq (eN x ^ ω) x) ∧
    xtB1 (jhRS.giX (gfE ^ ω) jhEw_ge jhEw_lt (by show jhG _ < ε₀; rw [jhEw_g]; exact omega0_lt_epsilon 0)) =
      iota S (gcG (gfE ^ ω) * ω) ∧
    upsilon (xtB1 (jhRS.giX (gfE ^ ω) jhEw_ge jhEw_lt
      (by show jhG _ < ε₀; rw [jhEw_g]; exact omega0_lt_epsilon 0))) = Pv S (gcG (gfE ^ ω) * ω) ∧
    Pv S (gcG (gfE ^ ω) * ω) < Nc.ncL S 0 := by
  refine ⟨fun x hx hx1 hωx => ?_, jhRS.giLoc _ _ _ _ S⟩
  have hg : jhG (gfE ^ ω) < x := by rw [jhEw_g]; exact hωx
  rw [jhRS.giL_top _ _ hx hx1 hg]
  show gq (jhR (gfE ^ ω) x) x = _
  have hωE : ω < gfE := omega_lt_Om1.trans Om1_lt_eW
  rw [jhR_pow omega0_ne_zero (hωE.trans gfE_lt_jhB), jhR_low hωE, (rdc_const omega_lt_Om1 x).1]

/-- **`sup = ι(Γ_{Ω₁+1+ε_{Ω₁+2}})`, `υ` of it `= P(Γ_{Ω₁+1+ε_{Ω₁+2}}) < L(0)`.** -/
theorem jhW_sup (S : InaccSeq.{0}) : (jhRS.giFam S).famSup = iota S (gcG jhB) ∧
    upsilon (jhRS.giFam S).famSup = Pv S (gcG jhB) ∧ Pv S (gcG jhB) < Nc.ncL S 0 := jhRS.giFam_sup S

/-- **ENUM-REACH at every range restart below `ι(Γ_{Ω₁+1+ε_{Ω₁+2}})`, fixed points included.** -/
theorem jhFam_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG jhB)) :
    CdUpper S l ∧ CdLower S l := jhRS.giFam_enum S hr hl

/-- **CapV at every range restart below `ι(Γ_{Ω₁+1+ε_{Ω₁+2}})`.** -/
theorem jhFam_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG jhB)) :
    CdCapV S l := jhRS.giFam_capV S hr hl

/-- **THE ROAD past every hereditary code below `ε_{Ω₁+2}`**: UPPER, LOWER and CapV asked only at
`λ ≥ ι(Γ_{Ω₁+1+ε_{Ω₁+2}})` (CapV also `υ_λ < L(ω)`), (CL), EQ, TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`,
`L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem jhFam_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG jhB) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG jhB) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG jhB) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  jhRS.giFam_road S hU hL hV hC hEQ hrest hB2

/-- **The order of the frontiers**: `ι(Γ_{Ω₁+1+E^E}) < ι(Γ_{Ω₁+1+c}·ω) < ι(Γ_{Ω₁+1+ε_{Ω₁+2}}) < ι(Ω₂)` for every
hereditary code `c ∈ [E^E, ε_{Ω₁+2})` with gate below `ε₀`, and `P(Γ_{Ω₁+1+ε_{Ω₁+2}}) < P(Ω₂) < L(0)`. -/
theorem jhW_fr_order {c : Ordinal.{0}} (hBc : gfE ^ gfE ≤ c) (hc : c < jhB) (hg : jhG c < ε₀)
    (S : InaccSeq.{0}) :
    iota S (gcG (gfE ^ gfE)) < iota S (gcG c * ω) ∧ iota S (gcG c * ω) < iota S (gcG jhB) ∧
      iota S (gcG jhB) < iota S (Om (1 + 1)) ∧ Pv S (gcG jhB) < Pv S (Om (1 + 1)) ∧
      Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hgV : Bt.Good S (gcG (gfE ^ gfE)) :=
    gi_good (K := jhK) fun Z hZ => jhRS.giL_atom (jhTw_lt 1)
      (by show jhG (jhTw 1) < Z; rw [jhTw_g 1]; exact hZ.1)
  have hla : gcG (gfE ^ gfE) < gcG c * ω := (gcG_le hBc).trans_lt (lt_mul_of_one_lt_right (gcG_SC _).1 one_lt_omega0)
  exact ⟨cd_iota_lt_of_good hgV hla, jhRS.gi_fr_order hc hg S⟩

end Googology.Trans.PoR.InaccPsi.R2.Gj
