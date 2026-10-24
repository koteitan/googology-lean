import Googology.Trans.PoR.InaccPsi.R2.GiLim

/-!
# THE CODES BELOW `ε_{Ω₁+1}²` AS A READING SYSTEM: layers, frontiers and the road up to `ι(Γ_{Ω₁+1+ε_{Ω₁+1}²})`

The code system `giK` (`R2.GiSq`) with the reading `giR c x = ε_{x+1}·γ(x) + a(x)` (`R2.GiRdg`) and the last terms of
`R2.GiLim` form a reading system `giRS2` (`R2.GiRS`), with the cofinal codes `ε_{Ω₁+1}·Ω₁^{Ω₁^{⋯}}` (gate `≤ 1`).  The
generic results of `R2.GiRS`, `R2.GiCodes`, `R2.GiLoc` then give, for every code `c = ε_{Ω₁+1}·γ + a`
(`1 ≤ γ < ε_{Ω₁+1}`, `a < ε_{Ω₁+1}`):

* `giL_spec` (**the gated layer of `c`**: gate `giG c`, top `Γ_{x+1+ε_{x+1}·γ(x)+a(x)}`), `giRS2.giL_codes`
  (its top reads `Γ_{Ω₁+1+c}`), `giRS2.giLoc` (**`Λ⁺ = ι(Γ_{Ω₁+1+c}·ω)`** for gates below `ε₀`), `giRS2.giEnum`,
  `giRS2.giCapV`, `giRS2.giBlk`;
* `giW_loc` (**THE CODE `ε_{Ω₁+1}·ω` IS LOCATED**: the layer of the code `ε_{Ω₁+1}·ω` has the top of `Gh.ghWB` and
  `Λ⁺ = ι(Γ_{Ω₁+1+ε_{Ω₁+1}·ω}·ω)`);
* `giSq_sup` (**`sup = ι(Γ_{Ω₁+1+ε_{Ω₁+1}²})`, `P(Γ_{Ω₁+1+ε_{Ω₁+1}²}) < L(0)`**), `giRS2.giFam_enum`,
  `giRS2.giFam_capV`, `giRS2.giFam_blk`, `giRS2.giFam_road` (THE ROAD with UPPER, LOWER, CapV asked only at
  `λ ≥ ι(Γ_{Ω₁+1+ε_{Ω₁+1}²})`), `giSq_fr_order`.

No new axiom.  New definition: `giRS2`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gi

open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The cofinal codes `ε_{Ω₁+1}·ghTw k` -/

theorem ghTw_ge_code : ∀ k : ℕ, (fun a : Ordinal.{0} => ω ^ a)^[k] (Om1 + 1) ≤ ghTw (k + 2)
  | 0 => by
    show Om1 + 1 ≤ ghTw (0 + 1 + 1)
    rw [ghTw_succ, ghTw_succ, show ghTw 0 = 1 from rfl, opow_one]
    have h11 : (1 : Ordinal.{0}) + 1 ≤ Om1 := by
      rw [show (1 : Ordinal.{0}) + 1 = ((2 : ℕ) : Ordinal.{0}) by norm_num]
      exact ((natCast_lt_omega0 2).trans omega_lt_Om1).le
    calc Om1 + 1 ≤ Om1 + Om1 := add_le_add le_rfl (one_le_iff_pos.2 (zero_lt_one.trans gf_one_lt_Om1))
      _ = Om1 * (1 + 1) := by rw [mul_add_one, mul_one]
      _ ≤ Om1 * Om1 := mul_le_mul_left' h11 Om1
      _ = Om1 ^ ((1 : Ordinal.{0}) + 1) := by rw [opow_add, opow_one]
      _ ≤ Om1 ^ Om1 := opow_le_opow_right (zero_lt_one.trans gf_one_lt_Om1) h11
  | k + 1 => by
    rw [Function.iterate_succ_apply', ghTw_succ (k + 2)]
    calc ω ^ ((fun a : Ordinal.{0} => ω ^ a)^[k] (Om1 + 1)) ≤ ω ^ ghTw (k + 2) :=
          opow_le_opow_right omega0_pos (ghTw_ge_code k)
      _ ≤ Om1 ^ ghTw (k + 2) := opow_le_opow_left _ omega_lt_Om1.le

/-- **The `Ω₁`-tower is cofinal in `ε_{Ω₁+1}`.** -/
theorem ghTw_cofE {β : Ordinal.{0}} (hβ : β < gfE) : ∃ k : ℕ, β < ghTw k := by
  obtain ⟨k, hk⟩ := lt_nfp_iff.1 hβ
  exact ⟨k + 2, hk.trans_le (ghTw_ge_code k)⟩

theorem ghTw_pos (k : ℕ) : ghTw k ≠ 0 := by
  cases k with
  | zero => exact one_ne_zero
  | succ k => rw [ghTw_succ]; exact opow_ne_zero _ Om1_ne'

theorem ghTw_strict (k : ℕ) : ghTw k < ghTw (k + 1) := by
  rw [ghTw_succ]; exact lt_Om1_pow (ghTw_lt k)

theorem giTw_le (k : ℕ) : gfE ≤ gfE * ghTw k := gi_E_le_mul (ghTw_pos k)

theorem giTw_lt (k : ℕ) : gfE * ghTw k < giB := (mul_lt_mul_iff_right₀ eW_E.pos).2 (ghTw_lt k)

theorem giTw_g (k : ℕ) : giG (gfE * ghTw k) < ε₀ := by
  have e : gfE * ghTw k = gfE * ghTw k + 0 := by rw [add_zero]
  rw [e, giQ_code eW_E.pos, gtc_zero, max_eq_left zero_le]
  exact (giQ_le _).trans_lt ((ghTw_gtc k).trans_lt (one_lt_omega0.trans (omega0_lt_epsilon 0)))

theorem giB_lim : IsSuccLimit giB := by
  rw [giB_eq]; exact ph_opow_lim (add_pos eW_E.pos eW_E.pos).ne'

/-- **The codes `ε_{Ω₁+1}·ghTw k` are cofinal in `ε_{Ω₁+1}²`.** -/
theorem giTw_cof {c : Ordinal.{0}} (hc : c < giB) : ∃ k : ℕ, c < gfE * ghTw k := by
  obtain ⟨k, hk⟩ := ghTw_cofE (gi_div_lt hc)
  refine ⟨k, ?_⟩
  calc c < gfE * (c / gfE + 1) := by
        rw [mul_add_one]
        conv_lhs => rw [← gi_dec c]
        exact (add_lt_add_iff_left _).2 (gh_mod_lt c)
    _ ≤ gfE * ghTw k := mul_le_mul_left' (Order.add_one_le_of_lt hk) _

/-- **THE READING SYSTEM of the codes below `ε_{Ω₁+1}²`.** -/
noncomputable def giRS2 : GiRS where
  K := giK
  R := giR
  E_lt := gfE_lt_giB
  B_lim := giB_lim
  gt_E := giG_E
  gt_lowE := fun _ hc => giG_lt_E hc
  R_E := giR_E
  lt0 := fun _ _ hx hx1 hc hg => giR_lt0 hx hx1 hc hg
  mono := fun _ _ _ hx hc hbc hgb hgc => giR_mono hx hc hbc hgb hgc
  succ := fun _ x => giR_succ x
  gt_le_succ := giG_le_succ
  cof := fun _ _ hx hx1 hc hEc hg _ hν => giR_cof hx hx1 hc hEc hg hν
  ex := fun _ _ _ hB hc hg => giR_pi hB hc hg
  ld := fun _ hl hEc hc => giLD_ne hl hEc hc
  cf := fun k => gfE * ghTw k
  cf_ge := giTw_le
  cf_lt := giTw_lt
  cf_g := giTw_g
  cf_mono := fun k => (mul_lt_mul_iff_right₀ eW_E.pos).2 (ghTw_strict k)
  cf_cof := fun _ hc => giTw_cof hc

theorem giRS2_K : giRS2.K = giK := rfl

theorem giRS2_V : giRS2.K.V = gcG giB := rfl

/-- **THE GENERIC THEOREM for every code `c = ε_{Ω₁+1}·γ + a`, `1 ≤ γ < ε_{Ω₁+1}`, `a < ε_{Ω₁+1}`**: a gated base
package (a gated layer with EXACT, IMG, RS and the top witness as fields) with gate `giG c` whose top is
`ϑˣ(Ω₁·Ω₁ + ε_{x+1}·γ(x) + a(x)) = Γ_{x+1+ε_{x+1}·γ(x)+a(x)}` at every `ε`-number base `x < Ω₁` above the gate. -/
theorem giL_spec : ∀ γ a : Ordinal.{0}, 1 ≤ γ → γ < gfE → a < gfE → ∃ B : GdB, B.g = giG (gfE * γ + a) ∧
    ∀ x, InE x → x < Om1 → giG (gfE * γ + a) < x →
      B.K.E x = gq (eN x * rdc γ x + rdc a x) x ∧ B.K.sys.top x = gq (eN x * rdc γ x + rdc a x) x := by
  intro γ a hγ1 hγ ha
  have h : gfE ≤ gfE * γ + a := (gi_E_le_mul (one_le_iff_ne_zero.1 hγ1)).trans le_self_add
  have hc : gfE * γ + a < giB := by
    calc gfE * γ + a < gfE * γ + gfE := (add_lt_add_iff_left _).2 ha
      _ = gfE * (γ + 1) := by rw [mul_add_one]
      _ ≤ gfE * gfE := mul_le_mul_left' (Order.add_one_le_of_lt hγ) _
  refine ⟨giRS2.giL _ h hc, giRS2.giL_g h hc, fun x hx hx1 hg => ?_⟩
  rw [← giR_code ha x]
  exact ⟨giRS2.giL_E h hc hx hx1 hg, giRS2.giL_top h hc hx hx1 hg⟩

/-! ## The code `ε_{Ω₁+1}·ω` (the layer `Gh.ghWB`) -/

theorem giW_le : gfE ≤ ghE := gfE_lt_ghE.le

theorem giW_lt : ghE < giB := by
  rw [ghE]; exact (mul_lt_mul_iff_right₀ eW_E.pos).2 (omega_lt_Om1.trans Om1_lt_eW)

theorem giW_g : giG ghE < ε₀ := by
  have e : ghE = gfE * ω + 0 := by rw [ghE, add_zero]
  rw [e, giQ_code eW_E.pos, gtc_zero, max_eq_left zero_le]
  unfold giQ
  rw [if_neg (lt_irrefl ω), (rdc_const omega_lt_Om1 0).2]
  exact omega0_lt_epsilon 0

/-- **THE CODE `ε_{Ω₁+1}·ω` IS LOCATED**: the layer of the code `ε_{Ω₁+1}·ω` has the top `ϑˣ(Ω₁·Ω₁ + ε_{x+1}·ω) =
Γ_{x+1+ε_{x+1}·ω}` of `Gh.ghWB` at every `ε`-number base, and `Λ⁺ = ι(Γ_{Ω₁+1+ε_{Ω₁+1}·ω}·ω)`, `ρ` of it
`= P(Γ_{Ω₁+1+ε_{Ω₁+1}·ω}·ω) < L(0)`. -/
theorem giW_loc (S : InaccSeq.{0}) :
    (∀ x, InE x → x < Om1 → (giRS2.giX ghE giW_le giW_lt giW_g).top x = ghWB.K.sys.top x) ∧
    xtB1 (giRS2.giX ghE giW_le giW_lt giW_g) = iota S (ghV * ω) ∧
    upsilon (xtB1 (giRS2.giX ghE giW_le giW_lt giW_g)) = Pv S (ghV * ω) ∧ Pv S (ghV * ω) < Nc.ncL S 0 := by
  refine ⟨fun x hx hx1 => ?_, giRS2.giLoc ghE giW_le giW_lt giW_g S⟩
  rw [giRS2.giX_top ghE giW_le giW_lt giW_g hx hx1, ghWB_top hx hx1]
  have e : ghE = gfE * ω + 0 := by rw [ghE, add_zero]
  rw [e]
  show gq (giR (gfE * ω + 0) x) x = gq (eN x * ω) x
  rw [giR_code eW_E.pos, rdc_zero, add_zero, (rdc_const omega_lt_Om1 x).1]

/-- **`sup = ι(Γ_{Ω₁+1+ε_{Ω₁+1}²})`, `υ` of it `= P(Γ_{Ω₁+1+ε_{Ω₁+1}²}) < L(0)`.** -/
theorem giSq_sup (S : InaccSeq.{0}) : (giRS2.giFam S).famSup = iota S (gcG giB) ∧
    upsilon (giRS2.giFam S).famSup = Pv S (gcG giB) ∧ Pv S (gcG giB) < Nc.ncL S 0 := giRS2.giFam_sup S

/-- **The order of the frontiers**: `ι(Γ_{Ω₁+1+ε_{Ω₁+1}·ω}) < ι(Γ_{Ω₁+1+c}·ω) < ι(Γ_{Ω₁+1+ε_{Ω₁+1}²}) < ι(Ω₂)` for
every code `c ∈ [ε_{Ω₁+1}·ω, ε_{Ω₁+1}²)` with gate below `ε₀`, and `P(Γ_{Ω₁+1+ε_{Ω₁+1}²}) < P(Ω₂) < L(0)` (past the
last frontier `ι(Γ_{Ω₁+1+ε_{Ω₁+1}·ω})` of `R2.GhLoc`). -/
theorem giSq_fr_order {c : Ordinal.{0}} (hWc : ghE ≤ c) (hc : c < giB) (hg : giG c < ε₀) (S : InaccSeq.{0}) :
    iota S ghV < iota S (gcG c * ω) ∧ iota S (gcG c * ω) < iota S (gcG giB) ∧
      iota S (gcG giB) < iota S (Om (1 + 1)) ∧ Pv S (gcG giB) < Pv S (Om (1 + 1)) ∧
      Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hgV : Bt.Good S ghV := gi_good (K := giK) fun Z hZ => giRS2.giL_atom giW_lt (ge_gx giW_g (gg_SC_eps hZ))
  have hla : ghV < gcG c * ω := (gcG_le hWc).trans_lt (lt_mul_of_one_lt_right (gcG_SC _).1 one_lt_omega0)
  exact ⟨cd_iota_lt_of_good hgV hla, giRS2.gi_fr_order hc hg S⟩

end Googology.Trans.PoR.InaccPsi.R2.Gi
