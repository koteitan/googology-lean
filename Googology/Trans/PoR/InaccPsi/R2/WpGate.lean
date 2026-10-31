import Googology.Trans.PoR.InaccPsi.R2.WmArith
import Googology.Trans.PoR.InaccPsi.R2.WnLv

/-!
# WpGate: `ω`-SEQUENCES OF (A2) LEVELS WITH THE GATE BOUND `glG ℓ_k ≤ glG ℓ`

`Wm.WmFs` asks the members' gates `gtc ℓ_k ≤ gtc ℓ` below `ε_{Ω₁+1}`.  `WpFs` is the same with the (A2) gate
`Gl.glG` and the bound `G`; below `ε_{Ω₁+1}` the two agree (`wpFs_of_wm`).  What is new is the gate of a coefficient
change in the base-`e` Cantor normal form that `Gl.glG` reads (`e = guE v` an `ε`-number code):

* `wp_E_opow` (**`e^j = Ω₁^{e·j}`** for an `ε`-number `e > Ω₁`), `wp_mod_mod`, `wp_mul_cancel_dvd`;
* `wp_glG_coef` (**THE GATE OF A SMALLER LAST COEFFICIENT**: `Ω₁^{e+1} ∣ A`, `0 < c' ≤ c < Ω₁`,
  `A + Ω₁^e·c < G` ⇒ `glG (A + Ω₁^e·c') ≤ glG (A + Ω₁^e·c)`; induction on the code through `Gl.glG_cnf`);
* `WpFs`, `wpFs_of_wm` (**every `Wm.WmFs` level below `ε_{Ω₁+1}` is `WpFs`**), `wpFs_coef` (**EVERY (A2)
  COEFFICIENT-LIMIT LEVEL `P + Ω₁^e·c` HAS AN `ω`-SEQUENCE**), `wpFs_Bn` (**the cofinal levels `Gl.glBn n` have one**:
  `Gl.glCfn n k`, gate `0`).

No new axiom.  New definition: `WpFs`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wp

open Googology.Trans.PoR.InaccPsi.R2.Wh Googology.Trans.PoR.InaccPsi.R2.Ho
open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gf
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd
open Googology.Trans.PoR.InaccPsi.R2.Wm Googology.Trans.PoR.InaccPsi.R2.Wn Googology.Trans.PoR.InaccPsi.R2.Gk

/-! ## Arithmetic -/

/-- **`e^j = Ω₁^{e·j}`** for an `ε`-number `e > Ω₁`. -/
theorem wp_E_opow {e : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (j : Ordinal.{0}) : e ^ j = Om1 ^ (e * j) := by
  have h1 : Om1 * e = e := by
    have := wn_Om1_mul_pow he hOe one_ne_zero; rwa [opow_one] at this
  have h2 : Om1 ^ e = e := by
    conv_lhs => rw [← gl_Om1_E]
    rw [← opow_mul, h1]; exact he
  rw [opow_mul, h2]

/-- `m ∣ M ⇒ (v mod M) mod m = v mod m`. -/
theorem wp_mod_mod {m M : Ordinal.{0}} (h : m ∣ M) (v : Ordinal.{0}) : (v % M) % m = v % m := by
  obtain ⟨k, rfl⟩ := h
  conv_rhs => rw [← Ordinal.div_add_mod v (m * k)]
  rw [mul_assoc, Ordinal.mul_add_mod_self]

/-- `x·y ∣ x·z` with `x ≠ 0` ⇒ `y ∣ z`. -/
theorem wp_mul_cancel_dvd {x y z : Ordinal.{0}} (hx : x ≠ 0) (h : x * y ∣ x * z) : y ∣ z := by
  obtain ⟨q, hq⟩ := h
  rw [mul_assoc] at hq
  exact ⟨q, (mul_right_injective₀ hx hq)⟩

/-- `(m·q + t) / m = q`, `(m·q + t) mod m = t` for `t < m`. -/
theorem wp_divmod {m q t : Ordinal.{0}} (ht : t < m) : (m * q + t) / m = q ∧ (m * q + t) % m = t := by
  have hm : m ≠ 0 := (zero_le.trans_lt ht).ne'
  refine ⟨?_, ?_⟩
  · rw [Ordinal.mul_add_div _ hm, Ordinal.div_eq_zero_of_lt ht, add_zero]
  · rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt ht]

theorem wp_pow_lt_succ {e c : Ordinal.{0}} (hc : c < Om1) : Om1 ^ e * c < Om1 ^ (e + 1) := wm_term_lt hc

/-! ## The gate of a smaller last coefficient -/

/-- **THE GATE OF A SMALLER LAST COEFFICIENT**: for `v = A + Ω₁^e·c < G` with `Ω₁^{e+1} ∣ A` and `0 < c' ≤ c < Ω₁`,
`glG (A + Ω₁^e·c') ≤ glG v`. -/
theorem wp_glG_coef : ∀ v, v < gcG 0 → ∀ A e c c' : Ordinal.{0}, v = A + Om1 ^ e * c → Om1 ^ (e + 1) ∣ A →
    c' ≠ 0 → c' ≤ c → c < Om1 → glG (A + Om1 ^ e * c') ≤ glG v := by
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hvG A e c c' hv hA hc0 hcc hcO
  have hc0' : c ≠ 0 := (pos_iff_ne_zero.2 hc0 |>.trans_le hcc).ne'
  have hkv : A + Om1 ^ e * c' ≤ v := by
    rw [hv]; exact add_le_add le_rfl (mul_le_mul_left' hcc _)
  rcases lt_or_ge v gfE with hvE | hvE
  · -- below `ε_{Ω₁+1}`: the gate is `gtc`
    have hkE : A + Om1 ^ e * c' < gfE := hkv.trans_lt hvE
    rw [glG_low hvE, glG_low hkE]
    have h1 := wm_gtc_tail (t := 0) (by rw [add_zero]; exact hkE) hA hc0 (hcc.trans_lt hcO) (wm_pow_pos e)
    have h2 := wm_gtc_tail (t := 0) (by rw [add_zero, ← hv]; exact hvE) hA hc0' hcO (wm_pow_pos e)
    rw [add_zero] at h1 h2
    rw [h1, hv, h2]
    exact max_le_max le_rfl (max_le_max (max_le_max le_rfl hcc) le_rfl)
  -- above: the base-`e₀` normal form
  obtain ⟨hk, hd0, hdE, hr, hdec, -, hrv, -⟩ := gl_parts hvE
  have hE : InE (guE v) := guE_E v
  have hOe : Om1 < guE v := gl_Om1_lt_E hvE
  set e₀ := guE v with he₀
  set j := log e₀ v
  set d := v / e₀ ^ j
  set r := v % e₀ ^ j
  have hvN : v < eN e₀ := gl_lt_eN hvE
  have hpow := wp_E_opow hE hOe j
  have hdvA : ∀ f, f ≤ e + 1 → Om1 ^ f ∣ A := fun f hf => (opow_dvd_opow Om1 hf).trans hA
  have hpj0 : e₀ ^ j ≠ 0 := opow_ne_zero _ hE.pos.ne'
  have hjv : e₀ ^ j ≤ v := by
    rw [← hdec]; exact (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0)).trans le_self_add
  rcases lt_or_ge e (e₀ * j) with hej | hej
  · -- the last coefficient lies in the rest `r`
    set m := Om1 ^ (e + 1) with hm
    have hm0 : m ≠ 0 := opow_ne_zero _ wh_Om1_pos.ne'
    have hmM : m ∣ e₀ ^ j := by rw [hpow]; exact opow_dvd_opow Om1 (add_one_le_of_lt hej)
    have hT : Om1 ^ e * c < m := wp_pow_lt_succ hcO
    obtain ⟨a, ha⟩ := hA
    have hvm : v % m = Om1 ^ e * c := by rw [hv, ha]; exact (wp_divmod hT).2
    have hvd : v / m = a := by rw [hv, ha]; exact (wp_divmod hT).1
    have hrm : r % m = Om1 ^ e * c := by rw [wp_mod_mod hmM v]; exact hvm
    have hr' : r = m * (r / m) + Om1 ^ e * c := by rw [← hrm]; exact (Ordinal.div_add_mod r m).symm
    -- `A = e₀^j·d + m·(r/m)`
    have hAeq : A = e₀ ^ j * d + m * (r / m) := by
      obtain ⟨q, hq⟩ := hmM
      have h1 : v = m * (q * d + r / m) + Om1 ^ e * c := by
        rw [mul_add, ← mul_assoc, ← hq, add_assoc, ← hr', hdec]
      have h2 : v / m = q * d + r / m := by rw [h1]; exact (wp_divmod hT).1
      rw [ha, ← hvd, h2, mul_add, ← mul_assoc, ← hq]
    have hr'lt : m * (r / m) + Om1 ^ e * c' ≤ r := by
      conv_rhs => rw [hr']
      exact add_le_add le_rfl (mul_le_mul_left' hcc _)
    have hkeq : A + Om1 ^ e * c' = e₀ ^ j * d + (m * (r / m) + Om1 ^ e * c') := by rw [hAeq, add_assoc]
    have hkB : e₀ ^ j * d + (m * (r / m) + Om1 ^ e * c') < gcG 0 := by rw [← hkeq]; exact hkv.trans_lt hvG
    have hkN : e₀ ^ j * d + (m * (r / m) + Om1 ^ e * c') < eN e₀ := by rw [← hkeq]; exact hkv.trans_lt hvN
    have hrB : e₀ ^ j * d + r < gcG 0 := by rw [hdec]; exact hvG
    have hrN : e₀ ^ j * d + r < eN e₀ := by rw [hdec]; exact hvN
    have hA'm : m ∣ m * (r / m) := dvd_mul_right _ _
    have IHr := IH r hrv (hrv.trans hvG) (m * (r / m)) e c c' hr' hA'm hc0 hcc hcO
    rw [hkeq, glG_cnf hE hOe hk hd0 hdE (hr'lt.trans_lt hr) hkN hkB]
    conv_rhs => rw [← hdec, glG_cnf hE hOe hk hd0 hdE hr hrN hrB]
    exact max_le_max le_rfl (max_le_max le_rfl IHr)
  · -- the last coefficient lies in the digit `d`
    set f := e - e₀ * j
    have hef : e = e₀ * j + f := (Ordinal.add_sub_cancel_of_le hej).symm
    have hsplit : Om1 ^ e = e₀ ^ j * Om1 ^ f := by rw [hef, opow_add, ← hpow]
    have hdA : e₀ ^ j ∣ A := by rw [hpow]; exact hdvA _ (hej.trans le_self_add)
    obtain ⟨a, ha⟩ := hdA
    have hvv : v = e₀ ^ j * (a + Om1 ^ f * c) := by rw [hv, ha, hsplit, mul_add, mul_assoc]
    have hd : d = a + Om1 ^ f * c := by
      show v / e₀ ^ j = _
      rw [hvv, Ordinal.mul_div_cancel _ hpj0]
    have hr0 : r = 0 := by
      show v % e₀ ^ j = 0
      rw [hvv]; exact Ordinal.mod_eq_zero_of_dvd (dvd_mul_right _ _)
    have haf : Om1 ^ (f + 1) ∣ a := by
      have h1 : Om1 ^ (e + 1) = e₀ ^ j * Om1 ^ (f + 1) := by rw [hef, add_assoc, opow_add, ← hpow]
      rw [h1, ha] at hA
      exact wp_mul_cancel_dvd hpj0 hA
    set dk := a + Om1 ^ f * c'
    have hdk : dk ≤ d := by rw [hd]; exact add_le_add le_rfl (mul_le_mul_left' hcc _)
    have hdk0 : dk ≠ 0 := by
      refine (lt_of_lt_of_le (mul_pos (wm_pow_pos f) (pos_iff_ne_zero.2 hc0)) le_add_self).ne'
    have hkeq : A + Om1 ^ e * c' = e₀ ^ j * dk + 0 := by rw [add_zero, ha, hsplit, mul_add, mul_assoc]
    have hkB : e₀ ^ j * dk + 0 < gcG 0 := by rw [← hkeq]; exact hkv.trans_lt hvG
    have hkN : e₀ ^ j * dk + 0 < eN e₀ := by rw [← hkeq]; exact hkv.trans_lt hvN
    have hrB : e₀ ^ j * d + r < gcG 0 := by rw [hdec]; exact hvG
    have hrN : e₀ ^ j * d + r < eN e₀ := by rw [hdec]; exact hvN
    have hp0 : (0 : Ordinal.{0}) < e₀ ^ j := pos_iff_ne_zero.2 hpj0
    rw [hkeq, glG_cnf hE hOe hk hdk0 (hdk.trans_lt hdE) hp0 hkN hkB]
    conv_rhs => rw [← hdec, glG_cnf hE hOe hk hd0 hdE hr hrN hrB]
    refine max_le_max le_rfl (max_le_max ?_ (by rw [hr0]))
    by_cases h1 : dk < ω
    · rw [show glQ dk = 0 from if_pos h1]; exact zero_le
    · have h2 : ¬ d < ω := fun h => h1 (hdk.trans_lt h)
      rw [show glQ dk = glG dk from if_neg h1, show glQ d = glG d from if_neg h2]
      have hdv : d < v := hdE.trans_le (gl_E_le hvE)
      exact IH d hdv (hdv.trans hvG) a f c c' hd haf hc0 hcc hcO

/-! ## `ω`-sequences of (A2) levels -/

/-- **AN `ω`-SEQUENCE OF (A2) LEVELS FOR `ℓ`**: levels `ℓ_k` (multiples of `Ω₁`, `≥ Ω₁`), strictly increasing, below
`ℓ`, cofinal with room for `+1`, with gates `glG ℓ_k ≤ glG ℓ` (`Wm.WmFs` with `Gl.glG`). -/
def WpFs (ℓ : Ordinal.{0}) : Prop :=
  ∃ ls : ℕ → Ordinal.{0}, (∀ k, Om1 ≤ ls k ∧ Om1 ∣ ls k) ∧ (∀ k, ls k < ls (k + 1)) ∧ (∀ k, ls k < ℓ) ∧
    (∀ t, t < ℓ → ∃ k, t + 1 < ls k) ∧ ∀ k, glG (ls k) ≤ glG ℓ

/-- **Below `ε_{Ω₁+1}` every `Wm.WmFs` sequence is a `WpFs` sequence** (`glG = gtc` there). -/
theorem wpFs_of_wm {ℓ : Ordinal.{0}} (hℓ : ℓ < gfE) (h : WmFs ℓ) : WpFs ℓ := by
  obtain ⟨ls, h1, h2, h3, h4, h5⟩ := h
  refine ⟨ls, h1, h2, h3, h4, fun k => ?_⟩
  rw [glG_low ((h3 k).trans hℓ), glG_low hℓ]; exact h5 k

/-- **EVERY (A2) COEFFICIENT-LIMIT LEVEL `P + Ω₁^e·c` HAS AN `ω`-SEQUENCE** (`1 ≤ e`, `c < Ω₁` a limit,
`Ω₁^{e+1} ∣ P`, `P + Ω₁^e·c < G`): `ℓ_k = P + Ω₁^e·(c_k + 1)`, `c_k = heFs c k`; gates by `wp_glG_coef`. -/
theorem wpFs_coef {P e c : Ordinal.{0}} (he : 1 ≤ e) (hc : IsSuccLimit c) (hcO : c < Om1)
    (hP : Om1 ^ (e + 1) ∣ P) (hG : P + Om1 ^ e * c < gcG 0) : WpFs (P + Om1 ^ e * c) := by
  have hc1 : c < Om (1 : Ordinal.{0}) := hl_om hcO
  set cs := heFs c with hcs
  have hck : ∀ k, cs k + 1 < c := fun k => hc.add_one_lt (heFs_lt hc hc1 k)
  have hlt : ∀ k, P + Om1 ^ e * (cs k + 1) < P + Om1 ^ e * c := fun k =>
    (add_lt_add_iff_left P).2 (mul_lt_mul_of_pos_left (hck k) (wm_pow_pos e))
  have hPd : Om1 ∣ P := (wm_Om1_dvd_pow (le_add_self : (1 : Ordinal.{0}) ≤ e + 1)).trans hP
  refine ⟨fun k => P + Om1 ^ e * (cs k + 1), fun k => ⟨?_, ?_⟩, fun k => ?_, hlt, fun t ht => ?_, fun k => ?_⟩
  · exact (wm_Om1_le_pow he).trans ((le_mul_of_one_le_right' le_add_self).trans le_add_self)
  · exact dvd_add hPd (Dvd.dvd.mul_right (wm_Om1_dvd_pow he) _)
  · exact (add_lt_add_iff_left P).2 (mul_lt_mul_of_pos_left
      (wm_succ_lt (heFs_mono hc hc1 k)) (wm_pow_pos e))
  · exact wm_cof_mul (wm_pow_pos e) (heFs_cof hc hc1) ht
  · exact wp_glG_coef _ hG P e c (cs k + 1) rfl hP (wm_add_one_pos _).ne' (hck k).le hcO

theorem wp_Om1_dvd_E {e : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) : Om1 ∣ e := by
  have := wn_Om1_mul_pow he hOe one_ne_zero
  rw [opow_one] at this
  exact ⟨e, this.symm⟩

theorem wp_glCfn_E (n k : ℕ) : InE (glCfn n k) := by
  cases n with
  | zero => exact glPsi_E (by exact_mod_cast (show (1 : ℕ) ≤ k + 1 by omega)) 0
  | succ n =>
    show InE (veblen (glCfn n k) 0)
    exact Wj.wjVeb_inE (eW_E.pos.trans_le ((glBn_spec n).2.2.2.2.1 k).1)

/-- **THE COFINAL LEVELS `glBn n` HAVE AN `ω`-SEQUENCE** (`Gl.glCfn n k`: `ε`-numbers in `[ε_{Ω₁+1}, glBn n)`, gate
`0`, cofinal). -/
theorem wpFs_Bn (n : ℕ) : WpFs (glBn n) := by
  obtain ⟨-, -, -, -, hcf, hcof⟩ := glBn_spec n
  refine ⟨glCfn n, fun k => ⟨Om1_lt_eW.le.trans (hcf k).1, wp_Om1_dvd_E (wp_glCfn_E n k)
    (Om1_lt_eW.trans_le (hcf k).1)⟩, fun k => (hcf k).2.2.2, fun k => (hcf k).2.1, fun t ht => ?_,
    fun k => by rw [(hcf k).2.2.1]; exact zero_le⟩
  obtain ⟨k, hk⟩ := hcof (t + 1) ((ev_isSuccLimit_of_inE (glBn_spec n).2.2.1).add_one_lt ht)
  exact ⟨k, hk⟩

end Googology.Trans.PoR.InaccPsi.R2.Wp
