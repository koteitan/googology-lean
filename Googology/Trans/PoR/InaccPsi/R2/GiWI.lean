import Googology.Trans.PoR.InaccPsi.R2.GiWl

/-!
# THE CODES BELOW `ε_{Ω₁+1}^ω` AS A READING SYSTEM: layers, frontiers and the road up to `ι(Γ_{Ω₁+1+ε_{Ω₁+1}^ω})`

The code system `gwK` (`R2.GiWp`), the reading `gwR` (`R2.GiWr`, `R2.GiWx`, `R2.GiWp`) and the last terms (`R2.GiWl`)
form a reading system `gwRS` (`R2.GiRS`) with the cofinal codes `ε_{Ω₁+1}^{k+1}` (gate `0`).  The generic results then
give, for every code `c = ε_{Ω₁+1}^k·d + r < ε_{Ω₁+1}^ω`:

* `gw_spec` (**the gated layer of `c`**: gate `gwG c`, top `ϑˣ(Ω₁·Ω₁ + c(x)) = Γ_{x+1+ε_{x+1}^k·d(x)+r(x)}`),
  `gwRS.giL_codes` (its top reads `Γ_{Ω₁+1+c}`), `gwRS.giLoc` (**`Λ⁺ = ι(Γ_{Ω₁+1+c}·ω)`** for gates below `ε₀`),
  `gwRS.giEnum`, `gwRS.giCapV`, `gwRS.giBlk`;
* `gwW_sup` (**`sup = ι(Γ_{Ω₁+1+ε_{Ω₁+1}^ω})`, `P(Γ_{Ω₁+1+ε_{Ω₁+1}^ω}) < L(0)`**), `gwRS.giFam_enum`,
  `gwRS.giFam_capV`, `gwRS.giFam_blk`, `gwRS.giFam_road` (THE ROAD with UPPER, LOWER, CapV asked only at
  `λ ≥ ι(Γ_{Ω₁+1+ε_{Ω₁+1}^ω})`), `gwW_fr_order` (past `ι(Γ_{Ω₁+1+ε_{Ω₁+1}²})` of `R2.GiSqI`).

No new axiom.  New definition: `gwRS`.
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

theorem gwE_lt : gfE < gwB := by
  calc gfE = gfE ^ (1 : Ordinal.{0}) := (opow_one _).symm
    _ < gwB := gw_pow_lt one_lt_omega0

theorem gwB_lim : IsSuccLimit gwB := by
  rw [gwB_eq]; exact ph_opow_lim (gfE_lt_ghE.trans_le' zero_le |>.ne')

theorem gwCf_ge (k : ℕ) : gfE ≤ gfE ^ ((k + 1 : ℕ) : Ordinal.{0}) := by
  calc gfE = gfE ^ (1 : Ordinal.{0}) := (opow_one _).symm
    _ ≤ _ := opow_le_opow_right eW_E.pos (by exact_mod_cast Nat.succ_pos k)

theorem gwCf_lt (k : ℕ) : gfE ^ ((k + 1 : ℕ) : Ordinal.{0}) < gwB := gw_pow_lt (natCast_lt_omega0 _)

theorem gwCf_g (k : ℕ) : gwG (gfE ^ ((k + 1 : ℕ) : Ordinal.{0})) < ε₀ := by
  have hk : ((k + 1 : ℕ) : Ordinal.{0}) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have e : gfE ^ ((k + 1 : ℕ) : Ordinal.{0}) = gfE ^ ((k + 1 : ℕ) : Ordinal.{0}) * 1 + 0 := by rw [mul_one, add_zero]
  rw [e, gwG_cnf hk one_ne_zero gw_one_lt (opow_pos _ eW_E.pos), giQ_one, gwG_zero, max_self]
  exact epsilon_pos 0

theorem gwCf_mono (k : ℕ) : gfE ^ ((k + 1 : ℕ) : Ordinal.{0}) < gfE ^ ((k + 1 + 1 : ℕ) : Ordinal.{0}) :=
  (opow_lt_opow_iff_right gw_one_lt).2 (by exact_mod_cast Nat.lt_succ_self (k + 1))

theorem gwCf_cof {c : Ordinal.{0}} (hc : c < gwB) : ∃ k : ℕ, c < gfE ^ ((k + 1 : ℕ) : Ordinal.{0}) := by
  rcases eq_or_ne c 0 with rfl | hc0
  · exact ⟨0, opow_pos _ eW_E.pos⟩
  obtain ⟨n, hn⟩ := lt_omega0.1 ((lt_opow_iff_log_lt gw_one_lt hc0).1 hc)
  exact ⟨n, (lt_opow_iff_log_lt gw_one_lt hc0).2 (by rw [hn]; exact_mod_cast Nat.lt_succ_self n)⟩

/-- **THE READING SYSTEM of the codes below `ε_{Ω₁+1}^ω`.** -/
noncomputable def gwRS : GiRS where
  K := gwK
  R := gwR
  E_lt := gwE_lt
  B_lim := gwB_lim
  gt_E := gwG_E
  gt_lowE := fun _ hc => gwG_low hc
  R_E := gwR_E
  lt0 := fun _ _ hx hx1 hc hg => gwR_lt0 hx hx1 hc hg
  mono := fun b c _ hx _ hbc hgb hgc => gwR_mono hx c hgc b hbc hgb
  succ := gwR_succ
  gt_le_succ := gwG_le_succ
  cof := fun _ _ hx hx1 hc hEc hg _ hν => gwR_cofE hx hx1 hc hEc hg hν
  ex := fun _ _ c hB hc hg => gwR_pi hB c hc hg
  ld := gwLD_ne
  cf := fun k => gfE ^ ((k + 1 : ℕ) : Ordinal.{0})
  cf_ge := gwCf_ge
  cf_lt := gwCf_lt
  cf_g := gwCf_g
  cf_mono := gwCf_mono
  cf_cof := fun _ hc => gwCf_cof hc

theorem gwRS_V : gwRS.K.V = gcG gwB := rfl

/-- **THE GENERIC THEOREM for every code `c ∈ [ε_{Ω₁+1}, ε_{Ω₁+1}^ω)`**: a gated base package (a gated layer with
EXACT, IMG, RS and the top witness as fields) with gate `gwG c` whose top is `ϑˣ(Ω₁·Ω₁ + c(x)) = Γ_{x+1+c(x)}`,
`c(x) = ε_{x+1}^k·d(x) + r(x)`, at every `ε`-number base `x < Ω₁` above the gate. -/
theorem gw_spec : ∀ c, gfE ≤ c → c < gwB → ∃ B : GdB, B.g = gwG c ∧
    ∀ x, InE x → x < Om1 → gwG c < x → B.K.E x = gq (gwR c x) x ∧ B.K.sys.top x = gq (gwR c x) x :=
  fun c h hc => ⟨gwRS.giL c h hc, gwRS.giL_g h hc, fun x hx hx1 hg =>
    ⟨gwRS.giL_E h hc hx hx1 hg, gwRS.giL_top h hc hx hx1 hg⟩⟩

/-- **`sup = ι(Γ_{Ω₁+1+ε_{Ω₁+1}^ω})`, `υ` of it `= P(Γ_{Ω₁+1+ε_{Ω₁+1}^ω}) < L(0)`.** -/
theorem gwW_sup (S : InaccSeq.{0}) : (gwRS.giFam S).famSup = iota S (gcG gwB) ∧
    upsilon (gwRS.giFam S).famSup = Pv S (gcG gwB) ∧ Pv S (gcG gwB) < Nc.ncL S 0 := gwRS.giFam_sup S

/-- **The order of the frontiers**: `ι(Γ_{Ω₁+1+ε_{Ω₁+1}²}) < ι(Γ_{Ω₁+1+c}·ω) < ι(Γ_{Ω₁+1+ε_{Ω₁+1}^ω}) < ι(Ω₂)` for
every code `c ∈ [ε_{Ω₁+1}², ε_{Ω₁+1}^ω)` with gate below `ε₀`, and `P(Γ_{Ω₁+1+ε_{Ω₁+1}^ω}) < P(Ω₂) < L(0)`. -/
theorem gwW_fr_order {c : Ordinal.{0}} (hBc : giB ≤ c) (hc : c < gwB) (hg : gwG c < ε₀) (S : InaccSeq.{0}) :
    iota S (gcG giB) < iota S (gcG c * ω) ∧ iota S (gcG c * ω) < iota S (gcG gwB) ∧
      iota S (gcG gwB) < iota S (Om (1 + 1)) ∧ Pv S (gcG gwB) < Pv S (Om (1 + 1)) ∧
      Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have e2 : gfE ^ (2 : Ordinal.{0}) = giB := by
    rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, opow_add, opow_one, giB]
  have h2ω : (2 : Ordinal.{0}) < ω := by exact_mod_cast natCast_lt_omega0 2
  have hBB : giB < gwB := by rw [← e2]; exact gw_pow_lt h2ω
  have hgB : gwG giB = 0 := by
    have e : giB = gfE ^ (2 : Ordinal.{0}) * 1 + 0 := by rw [mul_one, add_zero, e2]
    rw [e, gwG_cnf (by norm_num) one_ne_zero gw_one_lt (opow_pos _ eW_E.pos), giQ_one, gwG_zero, max_self]
  have hgV : Bt.Good S (gcG giB) :=
    gi_good (K := gwK) fun Z hZ => gwRS.giL_atom hBB (by rw [show gwRS.K.gt = gwG from rfl, hgB]; exact hZ.1)
  have hla : gcG giB < gcG c * ω := (gcG_le hBc).trans_lt (lt_mul_of_one_lt_right (gcG_SC _).1 one_lt_omega0)
  exact ⟨cd_iota_lt_of_good hgV hla, gwRS.gi_fr_order hc hg S⟩

end Googology.Trans.PoR.InaccPsi.R2.Gi
