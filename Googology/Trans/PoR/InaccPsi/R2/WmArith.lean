import Googology.Trans.PoR.InaccPsi.R2.WhSucc

/-!
# WmArith: LEVEL ARITHMETIC FOR THE `ω`-LIMIT STEPS OF THE LEVEL-CODE INDUCTION

The levels are the codes `ℓ` with `Ω₁ ≤ ℓ`, `Ω₁ ∣ ℓ`, `ℓ < ε_{Ω₁+1}` (gate `Gf.gtc`).  An `ω`-limit step at `ℓ` needs a
sequence of levels `ℓ_k` increasing to `ℓ` (cofinal with room for `+1`) whose gates stay `≤ gtc ℓ` (`WmFs ℓ`).

* `wm_gtc_cat` (**the gate of a concatenation**: `Ω₁^f ∣ P`, `t < Ω₁^f` ⇒ `gtc (P + t) = max (gtc P) (gtc t)`),
  `wm_gtc_term`, `wm_gtc_tail` (`gtc (A + (Ω₁^e·d + t))` for `Ω₁^{e+1} ∣ A`, `t < Ω₁^e`);
* `wm_cof_mul` (**cofinality of `A + B·(c_k + 1)` in `A + B·c`**), `wm_cof_pow` (**of `A + Ω₁^{e_k}` in `A + Ω₁^e`**);
* `WmFs ℓ` (**an `ω`-sequence of levels for `ℓ` with gates `≤ gtc ℓ`**), `WmExpFs e` (an `ω`-sequence of exponents
  for a limit exponent `e`), `wmFs_coef` (**every coefficient-limit level `P + Ω₁^e·c` has one**), `wmFs_exp`
  (**every exponent-limit level `P + Ω₁^e` whose exponent has one has one**), `wmExpFs_digit` (a limit exponent whose
  last digit is a countable limit has one), `wmExpFs_lim` (a limit exponent `E + Ω₁^f·d' + Ω₁^f` with `f` having one).

No new axiom.  New definitions: `WmFs`, `WmExpFs`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wm

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

theorem wm_Om1_pos' : (0 : Ordinal.{0}) < Om1 := wh_Om1_pos

theorem wm_add_one_pos (a : Ordinal.{0}) : 0 < a + 1 := zero_le.trans_lt (lt_add_one a)

theorem wm_succ_lt {a b : Ordinal.{0}} (h : a < b) : a + 1 < b + 1 := (add_one_le_of_lt h).trans_lt (lt_add_one b)

theorem wm_pow_pos (e : Ordinal.{0}) : (0 : Ordinal.{0}) < Om1 ^ e := opow_pos _ wh_Om1_pos

/-! ## Gates of concatenations -/

/-- **The gate of a concatenation**: `Ω₁^f ∣ P`, `t < Ω₁^f` ⇒ `gtc (P + t) = max (gtc P) (gtc t)`. -/
theorem wm_gtc_cat : ∀ P, P < gfE → ∀ f t : Ordinal.{0}, Om1 ^ f ∣ P → t < Om1 ^ f →
    gtc (P + t) = max (gtc P) (gtc t) := by
  intro P
  induction P using WellFoundedLT.induction with
  | ind P IH =>
  intro hPW f t hdv ht
  rcases eq_or_ne P 0 with rfl | hP0
  · rw [zero_add, gtc_zero, max_eq_right zero_le]
  obtain ⟨hq0, hqO, hr, hdec, hrl, -⟩ := parts hP0
  have hlW : log Om1 P < gfE := (log_lt hP0 hPW).trans hPW
  have hfl : f ≤ log Om1 P := le_log_of_opow_le wh_one_lt_Om1 (Ordinal.le_of_dvd hP0 hdv)
  have htl : t < Om1 ^ log Om1 P := ht.trans_le (opow_le_opow_right wh_Om1_pos hfl)
  have hdr : Om1 ^ f ∣ P % Om1 ^ log Om1 P := by
    have h1 : Om1 ^ f ∣ Om1 ^ log Om1 P * (P / Om1 ^ log Om1 P) :=
      Dvd.dvd.mul_right (opow_dvd_opow Om1 hfl) _
    exact (Ordinal.dvd_add_iff h1).1 (by rw [hdec]; exact hdv)
  have hrt : P % Om1 ^ log Om1 P + t < Om1 ^ log Om1 P := (Om1_pow_indec _).add_lt hr htl
  have IHr := IH _ hrl (hrl.trans hPW) f t hdr ht
  have e : P + t = Om1 ^ log Om1 P * (P / Om1 ^ log Om1 P) + (P % Om1 ^ log Om1 P + t) := by
    rw [← add_assoc, hdec]
  have eP : gtc P = max (max (gtc (log Om1 P)) (P / Om1 ^ log Om1 P)) (gtc (P % Om1 ^ log Om1 P)) :=
    gtc_dec hP0 hPW
  rw [e, (rdc_cnf hlW hq0.ne' hqO hrt 0).2, IHr, eP]
  exact (max_assoc _ _ _).symm

/-- **The gate of a term** `Ω₁^e·d` (`0 < d < Ω₁`). -/
theorem wm_gtc_term {e d : Ordinal.{0}} (he : e < gfE) (hd0 : d ≠ 0) (hd : d < Om1) :
    gtc (Om1 ^ e * d) = max (gtc e) d := by
  have h := (rdc_cnf (r := 0) he hd0 hd (wm_pow_pos e) 0).2
  rwa [add_zero, gtc_zero, max_eq_left zero_le] at h

theorem wm_term_lt {e d : Ordinal.{0}} (hd : d < Om1) : Om1 ^ e * d < Om1 ^ (e + 1) := by
  rw [opow_add, opow_one]; exact mul_lt_mul_of_pos_left hd (wm_pow_pos e)

theorem wm_le_pow (e : Ordinal.{0}) : e ≤ Om1 ^ e := right_le_opow e wh_one_lt_Om1

/-- **The gate of `A + (Ω₁^e·d + t)`** for `Ω₁^{e+1} ∣ A`, `0 < d < Ω₁`, `t < Ω₁^e`. -/
theorem wm_gtc_tail {A e d t : Ordinal.{0}} (hW : A + (Om1 ^ e * d + t) < gfE) (hA : Om1 ^ (e + 1) ∣ A)
    (hd0 : d ≠ 0) (hd : d < Om1) (ht : t < Om1 ^ e) :
    gtc (A + (Om1 ^ e * d + t)) = max (gtc A) (max (max (gtc e) d) (gtc t)) := by
  have hAW : A < gfE := le_self_add.trans_lt hW
  have hTW : Om1 ^ e * d + t < gfE := le_add_self.trans_lt hW
  have heW : e < gfE := ((wm_le_pow e).trans ((le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0)).trans
    le_self_add)).trans_lt hTW
  have hTl : Om1 ^ e * d + t < Om1 ^ (e + 1) := by
    rw [opow_add, opow_one]
    calc Om1 ^ e * d + t < Om1 ^ e * d + Om1 ^ e := (add_lt_add_iff_left _).2 ht
    _ = Om1 ^ e * (d + 1) := by rw [mul_add_one]
    _ ≤ Om1 ^ e * Om1 := mul_le_mul_left' (add_one_le_of_lt hd) _
  rw [wm_gtc_cat A hAW (e + 1) _ hA hTl, (rdc_cnf heW hd0 hd ht 0).2]

/-- **The gate of `A + t`** for `Ω₁^{e+1} ∣ A`, `t < Ω₁^e` (`d = 0`). -/
theorem wm_gtc_tail0 {A e t : Ordinal.{0}} (hW : A + t < gfE) (hA : Om1 ^ (e + 1) ∣ A) (ht : t < Om1 ^ e) :
    gtc (A + t) = max (gtc A) (gtc t) :=
  wm_gtc_cat A (le_self_add.trans_lt hW) (e + 1) t hA
    (ht.trans ((opow_lt_opow_iff_right wh_one_lt_Om1).2 (lt_add_one e)))

/-- **The gate of a power** `Ω₁^e`. -/
theorem wm_gtc_pow {e : Ordinal.{0}} (he : e < gfE) : gtc (Om1 ^ e) = max (gtc e) 1 := by
  have h := wm_gtc_term he one_ne_zero wh_one_lt_Om1
  rwa [mul_one] at h

/-! ## Cofinality -/

/-- **Cofinality of `A + B·(c_k + 1)` in `A + B·c`** for a cofinal sequence `c_k` in `c`. -/
theorem wm_cof_mul {A B c t : Ordinal.{0}} {cs : ℕ → Ordinal.{0}} (hB : 0 < B)
    (hcof : ∀ s, s < c → ∃ k, s < cs k) (ht : t < A + B * c) : ∃ k, t + 1 < A + B * (cs k + 1) := by
  rcases lt_or_ge t A with h | h
  · refine ⟨0, (add_one_le_of_lt h).trans_lt ?_⟩
    exact lt_add_of_pos_right _ (mul_pos hB (wm_add_one_pos _))
  · obtain ⟨s, rfl⟩ : ∃ s, t = A + s := ⟨t - A, (Ordinal.add_sub_cancel_of_le h).symm⟩
    have hs : s < B * c := (add_lt_add_iff_left A).1 ht
    have hq : s / B < c := (Ordinal.div_lt hB.ne').2 hs
    obtain ⟨k, hk⟩ := hcof _ hq
    refine ⟨k, ?_⟩
    rw [add_assoc]
    refine (add_lt_add_iff_left A).2 ?_
    have h1 : s < B * (s / B + 1) := by
      have := Ordinal.lt_mul_succ_div s hB.ne'; rwa [succ_eq_add_one] at this
    calc s + 1 ≤ B * (s / B + 1) := add_one_le_of_lt h1
    _ ≤ B * cs k := mul_le_mul_left' (add_one_le_of_lt hk) _
    _ < B * (cs k + 1) := mul_lt_mul_of_pos_left (lt_add_one _) hB

/-- **Cofinality of `A + Ω₁^{e_k}` in `A + Ω₁^e`** (`e` a limit, `e_k` cofinal in `e`). -/
theorem wm_cof_pow {A e t : Ordinal.{0}} {es : ℕ → Ordinal.{0}} (he : IsSuccLimit e)
    (hcof : ∀ s, s < e → ∃ k, s < es k) (ht : t < A + Om1 ^ e) : ∃ k, t + 1 < A + Om1 ^ es k := by
  rcases lt_or_ge t A with h | h
  · refine ⟨0, (add_one_le_of_lt h).trans_lt (lt_add_of_pos_right _ (wm_pow_pos _))⟩
  · obtain ⟨s, rfl⟩ : ∃ s, t = A + s := ⟨t - A, (Ordinal.add_sub_cancel_of_le h).symm⟩
    have hs : s < Om1 ^ e := (add_lt_add_iff_left A).1 ht
    obtain ⟨c', hc', hsc⟩ := (lt_opow_of_isSuccLimit wh_Om1_pos.ne' he).1 hs
    obtain ⟨k, hk⟩ := hcof _ hc'
    refine ⟨k, ?_⟩
    rw [add_assoc]
    exact (add_lt_add_iff_left A).2 ((add_one_le_of_lt hsc).trans_lt
      ((opow_lt_opow_iff_right wh_one_lt_Om1).2 hk))

/-! ## Sequences of levels -/

/-- **An `ω`-SEQUENCE OF LEVELS FOR `ℓ`**: levels `ℓ_k` (multiples of `Ω₁`, `≥ Ω₁`), strictly increasing, below `ℓ`,
cofinal with room for `+1`, with gates `≤ gtc ℓ`. -/
def WmFs (ℓ : Ordinal.{0}) : Prop :=
  ∃ ls : ℕ → Ordinal.{0}, (∀ k, Om1 ≤ ls k ∧ Om1 ∣ ls k) ∧ (∀ k, ls k < ls (k + 1)) ∧ (∀ k, ls k < ℓ) ∧
    (∀ t, t < ℓ → ∃ k, t + 1 < ls k) ∧ ∀ k, gtc (ls k) ≤ gtc ℓ

/-- **An `ω`-SEQUENCE OF EXPONENTS FOR `e`**: `1 ≤ e_k`, strictly increasing, below `e`, cofinal, gates `≤ gtc e`. -/
def WmExpFs (e : Ordinal.{0}) : Prop :=
  ∃ es : ℕ → Ordinal.{0}, (∀ k, 1 ≤ es k) ∧ (∀ k, es k < es (k + 1)) ∧ (∀ k, es k < e) ∧
    (∀ s, s < e → ∃ k, s < es k) ∧ ∀ k, gtc (es k) ≤ gtc e

theorem wm_Om1_dvd_pow {e : Ordinal.{0}} (he : 1 ≤ e) : Om1 ∣ Om1 ^ e := by
  have := opow_dvd_opow Om1 he; rwa [opow_one] at this

theorem wm_Om1_le_pow {e : Ordinal.{0}} (he : 1 ≤ e) : Om1 ≤ Om1 ^ e := by
  have := opow_le_opow_right wh_Om1_pos he; rwa [opow_one] at this

section Coef

variable {P e c : Ordinal.{0}} (he : 1 ≤ e) (hc : IsSuccLimit c) (hcO : c < Om1) (hP : Om1 ^ (e + 1) ∣ P)
  (hW : P + Om1 ^ e * c < gfE)
include he hc hcO hP hW

/-- **EVERY COEFFICIENT-LIMIT LEVEL `P + Ω₁^e·c` HAS AN `ω`-SEQUENCE**: `ℓ_k = P + Ω₁^e·(c_k + 1)`, `c_k = heFs c k`. -/
theorem wmFs_coef : WmFs (P + Om1 ^ e * c) := by
  have hc1 : c < Om (1 : Ordinal.{0}) := hl_om hcO
  set cs := heFs c with hcs
  have hck : ∀ k, cs k + 1 < c := fun k => hc.add_one_lt (heFs_lt hc hc1 k)
  have hlt : ∀ k, P + Om1 ^ e * (cs k + 1) < P + Om1 ^ e * c := fun k =>
    (add_lt_add_iff_left P).2 (mul_lt_mul_of_pos_left (hck k) (wm_pow_pos e))
  have hPd : Om1 ∣ P := (wm_Om1_dvd_pow (le_add_self : (1 : Ordinal.{0}) ≤ e + 1)).trans hP
  have hc0 : c ≠ 0 := hc.ne_bot
  have hgl : gtc (P + Om1 ^ e * c) = max (gtc P) (max (max (gtc e) c) 0) := by
    have := wm_gtc_tail (t := 0) (by rwa [add_zero]) hP hc0 hcO (wm_pow_pos e)
    rwa [add_zero, gtc_zero] at this
  refine ⟨fun k => P + Om1 ^ e * (cs k + 1), fun k => ⟨?_, ?_⟩, fun k => ?_, hlt, fun t ht => ?_, fun k => ?_⟩
  · exact (wm_Om1_le_pow he).trans ((le_mul_of_one_le_right' le_add_self).trans le_add_self)
  · exact dvd_add hPd (Dvd.dvd.mul_right (wm_Om1_dvd_pow he) _)
  · exact (add_lt_add_iff_left P).2 (mul_lt_mul_of_pos_left
      (wm_succ_lt (heFs_mono hc hc1 k)) (wm_pow_pos e))
  · exact wm_cof_mul (wm_pow_pos e) (heFs_cof hc hc1) ht
  · show gtc (P + Om1 ^ e * (cs k + 1)) ≤ _
    have hkW : P + (Om1 ^ e * (cs k + 1) + 0) < gfE := by rw [add_zero]; exact (hlt k).trans hW
    have h := wm_gtc_tail hkW hP (wm_add_one_pos _).ne' ((hck k).trans hcO) (wm_pow_pos e)
    rw [add_zero, gtc_zero] at h
    rw [h, hgl]
    exact max_le_max le_rfl (max_le_max (max_le_max le_rfl (hck k).le) le_rfl)

end Coef

/-- **The parts of `P` below `Ω₁^{e+1}`**: `Ω₁^e ∣ P` ⇒ `P = A + Ω₁^e·m` with `Ω₁^{e+1} ∣ A`, `m < Ω₁`. -/
theorem wm_split {P e : Ordinal.{0}} (hP : Om1 ^ e ∣ P) :
    ∃ A m, Om1 ^ (e + 1) ∣ A ∧ m < Om1 ∧ P = A + Om1 ^ e * m := by
  have hdiv : Om1 ^ (e + 1) ∣ Om1 ^ (e + 1) * (P / Om1 ^ (e + 1)) := dvd_mul_right _ _
  have hr : Om1 ^ e ∣ P % Om1 ^ (e + 1) := by
    have h1 : Om1 ^ e ∣ Om1 ^ (e + 1) * (P / Om1 ^ (e + 1)) :=
      (opow_dvd_opow Om1 (le_self_add)).trans hdiv
    exact (Ordinal.dvd_add_iff h1).1 (by rw [Ordinal.div_add_mod]; exact hP)
  obtain ⟨m, hm⟩ := hr
  have hlt : P % Om1 ^ (e + 1) < Om1 ^ (e + 1) := Ordinal.mod_lt _ (opow_ne_zero _ wh_Om1_pos.ne')
  refine ⟨_, m, hdiv, ?_, ?_⟩
  · rw [hm, opow_add, opow_one] at hlt
    exact (mul_lt_mul_iff_right₀ (wm_pow_pos e)).1 hlt
  · rw [← hm, Ordinal.div_add_mod]

section Exp

variable {P e : Ordinal.{0}} (he : IsSuccLimit e) (hP : Om1 ^ e ∣ P) (hW : P + Om1 ^ e < gfE)
  (hE : WmExpFs e)
include he hP hW hE

/-- **EVERY EXPONENT-LIMIT LEVEL `P + Ω₁^e` WHOSE EXPONENT HAS AN `ω`-SEQUENCE HAS ONE**: `ℓ_k = P + Ω₁^{e_k}`. -/
theorem wmFs_exp : WmFs (P + Om1 ^ e) := by
  obtain ⟨es, h1, hmono, hlt, hcof, hg⟩ := hE
  obtain ⟨A, m, hA, hm, rfl⟩ := wm_split hP
  have he1 : 1 ≤ e := (one_le_iff_pos.2 he.bot_lt)
  have hlk : ∀ k, A + Om1 ^ e * m + Om1 ^ es k < A + Om1 ^ e * m + Om1 ^ e := fun k =>
    (add_lt_add_iff_left _).2 ((opow_lt_opow_iff_right wh_one_lt_Om1).2 (hlt k))
  have hAd : Om1 ∣ A := (wm_Om1_dvd_pow (le_add_self : (1 : Ordinal.{0}) ≤ e + 1)).trans hA
  have hmd : Om1 ∣ Om1 ^ e * m := Dvd.dvd.mul_right (wm_Om1_dvd_pow he1) _
  have heW : e < gfE := (wm_le_pow e).trans_lt (le_add_self.trans_lt hW)
  -- the gate of `ℓ = A + Ω₁^e·(m+1)`
  have eL : A + Om1 ^ e * m + Om1 ^ e = A + (Om1 ^ e * (m + 1) + 0) := by
    rw [add_zero, mul_add_one, add_assoc]
  have hm1 : m + 1 < Om1 := gl_Om1_lim.add_one_lt hm
  have hgl : gtc (A + Om1 ^ e * m + Om1 ^ e) = max (gtc A) (max (gtc e) (m + 1)) := by
    rw [eL, wm_gtc_tail (by rw [← eL]; exact hW) hA (wm_add_one_pos _).ne' hm1 (wm_pow_pos e), gtc_zero,
      max_eq_left zero_le]
  refine ⟨fun k => A + Om1 ^ e * m + Om1 ^ es k, fun k => ⟨?_, ?_⟩, fun k => ?_, hlk, fun t ht => ?_,
    fun k => ?_⟩
  · exact (wm_Om1_le_pow (h1 k)).trans le_add_self
  · exact dvd_add (dvd_add hAd hmd) (wm_Om1_dvd_pow (h1 k))
  · exact (add_lt_add_iff_left _).2 ((opow_lt_opow_iff_right wh_one_lt_Om1).2 (hmono k))
  · exact wm_cof_pow he hcof ht
  · show gtc (A + Om1 ^ e * m + Om1 ^ es k) ≤ gtc (A + Om1 ^ e * m + Om1 ^ e)
    have hkW : A + Om1 ^ e * m + Om1 ^ es k < gfE := (hlk k).trans hW
    have hekW : es k < gfE := (hlt k).trans heW
    have htk : Om1 ^ es k < Om1 ^ e := (opow_lt_opow_iff_right wh_one_lt_Om1).2 (hlt k)
    rw [hgl]
    rcases eq_or_ne m 0 with rfl | hm0
    · rw [mul_zero, add_zero] at hkW ⊢
      rw [wm_gtc_tail0 hkW hA htk, wm_gtc_pow hekW, zero_add]
      exact max_le_max le_rfl (max_le_max (hg k) (le_refl 1))
    · have hkW' : A + (Om1 ^ e * m + Om1 ^ es k) < gfE := by rw [← add_assoc]; exact hkW
      rw [add_assoc, wm_gtc_tail hkW' hA hm0 hm htk, wm_gtc_pow hekW]
      exact max_le_max le_rfl (max_le (max_le (le_max_left _ _) ((le_self_add : m ≤ m + 1).trans (le_max_right _ _)))
        (max_le ((hg k).trans (le_max_left _ _)) ((one_le_iff_pos.2 (wm_add_one_pos m)).trans (le_max_right _ _))))

end Exp

/-! ## Exponents with an `ω`-sequence -/

/-- **A limit exponent whose last digit is a countable limit has an `ω`-sequence**: `e = E + Ω₁^f·d`,
`Ω₁^{f+1} ∣ E`, `d < Ω₁` a limit; `e_k = E + Ω₁^f·(d_k + 1)`. -/
theorem wmExpFs_digit {E f d : Ordinal.{0}} (hd : IsSuccLimit d) (hdO : d < Om1) (hE : Om1 ^ (f + 1) ∣ E)
    (hW : E + Om1 ^ f * d < gfE) : WmExpFs (E + Om1 ^ f * d) := by
  have hd1 : d < Om (1 : Ordinal.{0}) := hl_om hdO
  have hdk : ∀ k, heFs d k + 1 < d := fun k => hd.add_one_lt (heFs_lt hd hd1 k)
  have hlt : ∀ k, E + Om1 ^ f * (heFs d k + 1) < E + Om1 ^ f * d := fun k =>
    (add_lt_add_iff_left E).2 (mul_lt_mul_of_pos_left (hdk k) (wm_pow_pos f))
  have hgl : gtc (E + Om1 ^ f * d) = max (gtc E) (max (max (gtc f) d) 0) := by
    have := wm_gtc_tail (t := 0) (by rwa [add_zero]) hE hd.ne_bot hdO (wm_pow_pos f)
    rwa [add_zero, gtc_zero] at this
  refine ⟨fun k => E + Om1 ^ f * (heFs d k + 1), fun k => ?_, fun k => ?_, hlt, fun s hs => ?_, fun k => ?_⟩
  · exact (one_le_iff_pos.2 (mul_pos (wm_pow_pos f) (wm_add_one_pos _))).trans le_add_self
  · exact (add_lt_add_iff_left E).2 (mul_lt_mul_of_pos_left
      (wm_succ_lt (heFs_mono hd hd1 k)) (wm_pow_pos f))
  · obtain ⟨k, hk⟩ := wm_cof_mul (wm_pow_pos f) (heFs_cof hd hd1) hs
    exact ⟨k, (lt_add_one s).trans hk⟩
  · show gtc (E + Om1 ^ f * (heFs d k + 1)) ≤ _
    have hkW : E + (Om1 ^ f * (heFs d k + 1) + 0) < gfE := by rw [add_zero]; exact (hlt k).trans hW
    have h := wm_gtc_tail hkW hE (wm_add_one_pos _).ne' ((hdk k).trans hdO) (wm_pow_pos f)
    rw [add_zero, gtc_zero] at h
    rw [h, hgl]
    exact max_le_max le_rfl (max_le_max (max_le_max le_rfl (hdk k).le) le_rfl)

/-- **A limit exponent `E + Ω₁^f·d' + Ω₁^f` with a limit `f` that has an `ω`-sequence has one**:
`e_k = E + Ω₁^f·d' + Ω₁^{f_k}`. -/
theorem wmExpFs_lim {E f d' : Ordinal.{0}} (hf : IsSuccLimit f) (hd' : d' < Om1) (hE : Om1 ^ (f + 1) ∣ E)
    (hW : E + Om1 ^ f * d' + Om1 ^ f < gfE) (hF : WmExpFs f) : WmExpFs (E + Om1 ^ f * d' + Om1 ^ f) := by
  have hP : Om1 ^ f ∣ E + Om1 ^ f * d' :=
    dvd_add (dvd_trans (opow_dvd_opow Om1 le_self_add) hE) (dvd_mul_right _ _)
  obtain ⟨ls, hlev, hmono, hlt, hcof, hg⟩ := wmFs_exp hf hP hW hF
  refine ⟨ls, fun k => (one_le_iff_pos.2 wh_Om1_pos).trans (hlev k).1, hmono, hlt, fun s hs => ?_, hg⟩
  obtain ⟨k, hk⟩ := hcof s hs
  exact ⟨k, (lt_add_one s).trans hk⟩

end Googology.Trans.PoR.InaccPsi.R2.Wm
