import Googology.Trans.PoR.InaccPsi.R2.GiWc

/-!
# THE READING OF THE CODES BELOW `ε_{Ω₁+1}^ω`: order, cofinality, Lemma EXACT at every pair of bases; the code system

For `c = E^k·d + r` (`E = ε_{Ω₁+1}`) the reading is `gwR c x = ε_{x+1}^k·d(x) + r(x)` (`R2.GiWc`).

* `gw_mulOm_mem`, `gw_mem` (**every code lies in every hull containing its gate**), `gwB_mem`, `gwG_succ`,
  `gwG_le_succ`;
* `gwR_bound` (`c < E^k ⇒ c(x) < ε_{x+1}^k`), `gwR_lt0` (**below `Γ_{x+1}`**), `gwR_mono` (**strictly increasing**),
  `gwR_succ`, `gwR_E`, `gw_cofPow`, `gwR_cof` (**every `ν` below a reading is at most the reading of a smaller code with
  gate below `x`**);
* `gw_eAtomK_pi` (**Lemma EXACT for the atom `ω^{ε_{ρ+1}·n+β}`** at every pair of bases: `n = 1` is `gi_eAtom_pi`,
  `n ≥ 2` is `ϑ^ρ(ε_{ρ+1} + β')` with `β' = ε_{ρ+1}·(n-1) + β` (`vt_eN2`, [W07a] Lemma 4.2), the clause
  `π(ϑ^ρ(ξ)) = ϑ^σ(π ξ)`), `gw_eNr_pi` (`π(ε_{ρ+1}^n·γ(ρ)) = ε_{σ+1}^n·γ(σ)`), `gwR_pi` (**Lemma EXACT for every code
  below `ε_{Ω₁+1}^ω`**);
* `gw_count`, `gwK` (**THE CODE SYSTEM below `ε_{Ω₁+1}^ω`**).

No new axiom.  New definition: `gwK`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gi

open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Gd Googology.Trans.PoR.InaccPsi.R2.Gb

/-! ## Hulls and gates -/

/-- `ω^e·q` lies in every hull containing `e` and the digits of the code `q < ε_{Ω₁+1}`. -/
theorem gw_mulOm_mem {S : InaccSeq.{0}} {a b e : Ordinal.{0}} (he : e ∈ S.CSet a b) :
    ∀ q, q < gfE → gtc q < b → ω ^ e * q ∈ S.CSet a b := by
  intro q
  induction q using WellFoundedLT.induction with
  | ind q IH =>
  intro hqW hg
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [mul_zero]; exact CSet.zero_mem _ _
  obtain ⟨-, -, -, hdec, hrq, -⟩ := parts hq0
  obtain ⟨gl, gq, gr⟩ := gtc_parts hq0 hqW
  have hlq := log_lt hq0 hqW
  obtain ⟨-, hlO⟩ := gfW_mem (S := S) (a := a) (b := b) _ (hlq.trans hqW) (gl.trans_lt hg)
  have hr := IH _ hrq (hrq.trans hqW) (gr.trans_lt hg)
  have ee : ω ^ e * q = ω ^ (e + Om1 * log Om1 q) * (q / Om1 ^ log Om1 q) + ω ^ e * (q % Om1 ^ log Om1 q) := by
    conv_lhs => rw [← hdec]
    rw [mul_add, ← mul_assoc, opow_add, ← Om1_pow_eq]
  rw [ee]
  exact CSet.add_mem (gfMul_mem (CSet.add_mem he hlO) _ (gq.trans_lt hg)) hr

theorem gw_nat_of_lt {c : Ordinal.{0}} (hc : c < gwB) (hEc : gfE ≤ c) : ∃ n : ℕ, log gfE c = n :=
  lt_omega0.1 (gw_log_lt hc hEc)

/-- **Every code `c < ε_{Ω₁+1}^ω` lies in every hull containing its gate.** -/
theorem gw_mem {S : InaccSeq.{0}} {a b : Ordinal.{0}} : ∀ c, c < gwB → gwG c < b → c ∈ S.CSet a b := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  rcases lt_or_ge c gfE with hcE | hcE
  · rw [gwG_low hcE] at hg; exact gfW_mem' hcE hg
  obtain ⟨-, -, hdE, -, hdec⟩ := gw_parts hcE
  obtain ⟨n, hn⟩ := gw_nat_of_lt hc hcE
  rw [gwG_dec hcE] at hg
  have hrc : c % gfE ^ log gfE c < c := mod_opow_log_lt_self gfE (gw_ne_of_le hcE)
  have hr := IH _ hrc (hrc.trans hc) ((le_max_right _ _).trans_lt hg)
  rw [← hdec]
  refine CSet.add_mem ?_ hr
  have heE : gfE * (n : Ordinal.{0}) ∈ S.CSet a b := lg_cset_mul_nat gfW_inC n
  have hpow : gfE ^ log gfE c = ω ^ (gfE * (n : Ordinal.{0})) := by rw [hn, gw_pow_eq]
  have hgd := (le_max_left _ _).trans_lt hg
  set d := c / gfE ^ log gfE c with hd
  rw [hpow]
  by_cases hω : d < ω
  · obtain ⟨m, hm⟩ := lt_omega0.1 hω
    rw [hm]
    have := CSet.phi_mem (CSet.zero_mem (S := S) a b) heE
    rw [veblen_zero_apply] at this
    exact lg_cset_mul_nat this m
  · have h1 : giQ d = gtc d := by unfold giQ; rw [if_neg hω]
    exact gw_mulOm_mem heE _ hdE (by rw [← h1]; exact hgd)

theorem gwB_mem {S : InaccSeq.{0}} {a b : Ordinal.{0}} : gwB ∈ S.CSet a b := by
  rw [gwB_eq]
  have := CSet.phi_mem (CSet.zero_mem (S := S) a b) (ghE_inC (S := S) (a := a) (b := b))
  rwa [veblen_zero_apply] at this

theorem gw_succ_lt {k r : Ordinal.{0}} (hk : k ≠ 0) (hr : r < gfE ^ k) : r + 1 < gfE ^ k :=
  gw_pow_indec hk _ _ hr (by
    calc (1 : Ordinal.{0}) < gfE := gw_one_lt
      _ = gfE ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ gfE ^ k := opow_le_opow_right eW_E.pos (one_le_iff_ne_zero.2 hk))

/-- The normal form of `b + 1` for `b ≥ ε_{Ω₁+1}`. -/
theorem gw_succ_cnf {b : Ordinal.{0}} (hEb : gfE ≤ b) :
    b + 1 = gfE ^ log gfE b * (b / gfE ^ log gfE b) + (b % gfE ^ log gfE b + 1) ∧
      b % gfE ^ log gfE b + 1 < gfE ^ log gfE b := by
  obtain ⟨hk, -, -, hr, hdec⟩ := gw_parts hEb
  exact ⟨by conv_lhs => rw [← hdec]
            rw [add_assoc], gw_succ_lt hk hr⟩

theorem gwG_succ {Z : Ordinal.{0}} (hZ : IsSuccLimit Z) : ∀ b, gwG b < Z → gwG (b + 1) < Z := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hg
  rcases lt_or_ge b gfE with hbE | hbE
  · rw [gwG_low hbE] at hg
    rw [gwG_low (succ_lt_eW hbE)]
    exact (rdc_succ b hbE 0).2.2.trans_lt (hZ.add_one_lt hg)
  obtain ⟨hk, hd0, hdE, hr, -⟩ := gw_parts hbE
  obtain ⟨e, hr1⟩ := gw_succ_cnf hbE
  rw [gwG_dec hbE] at hg
  have hrb : b % gfE ^ log gfE b < b := mod_opow_log_lt_self gfE (gw_ne_of_le hbE)
  rw [e, gwG_cnf hk hd0 hdE hr1]
  exact max_lt ((le_max_left _ _).trans_lt hg) (IH _ hrb ((le_max_right _ _).trans_lt hg))

theorem gwG_le_succ : ∀ b, gwG b ≤ gwG (b + 1) := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  rcases lt_or_ge b gfE with hbE | hbE
  · rw [gwG_low hbE, gwG_low (succ_lt_eW hbE)]; exact (rdc_succ b hbE 0).2.1
  obtain ⟨hk, hd0, hdE, hr, -⟩ := gw_parts hbE
  obtain ⟨e, hr1⟩ := gw_succ_cnf hbE
  have hrb : b % gfE ^ log gfE b < b := mod_opow_log_lt_self gfE (gw_ne_of_le hbE)
  rw [gwG_dec hbE, e, gwG_cnf hk hd0 hdE hr1]
  exact max_le_max le_rfl (IH _ hrb)

/-! ## The reading -/

theorem gw_eNpow (x k : Ordinal.{0}) : eN x ^ k = ω ^ (eN x * k) := by
  rw [opow_mul, show ω ^ eN x = eN x from eN_E x]

theorem gwR_succ : ∀ b x : Ordinal.{0}, gwR (b + 1) x = gwR b x + 1 := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro x
  rcases lt_or_ge b gfE with hbE | hbE
  · rw [gwR_low hbE, gwR_low (succ_lt_eW hbE), (rdc_succ b hbE x).1]
  obtain ⟨hk, hd0, hdE, hr, hdec⟩ := gw_parts hbE
  obtain ⟨e, hr1⟩ := gw_succ_cnf hbE
  have hrb : b % gfE ^ log gfE b < b := mod_opow_log_lt_self gfE (gw_ne_of_le hbE)
  rw [e, gwR_cnf hk hd0 hdE hr1, IH _ hrb x, gwR_dec hbE x, add_assoc]

theorem gwR_E (x : Ordinal.{0}) : gwR gfE x = eN x := by
  have e : gfE = gfE ^ (1 : Ordinal.{0}) * 1 + 0 := by rw [opow_one, mul_one, add_zero]
  rw [e, gwR_cnf one_ne_zero one_ne_zero gw_one_lt (opow_pos _ eW_E.pos), opow_one, (rdc_const gf_one_lt_Om1 x).1,
    mul_one, gwR_low eW_E.pos, rdc_zero, add_zero]

theorem gwG_E : gwG gfE = 0 := by
  have e : gfE = gfE ^ (1 : Ordinal.{0}) * 1 + 0 := by rw [opow_one, mul_one, add_zero]
  rw [e, gwG_cnf one_ne_zero one_ne_zero gw_one_lt (opow_pos _ eW_E.pos), giQ_one, gwG_zero, max_self]

section Base

variable {x : Ordinal.{0}} (hx : InE x)
include hx

theorem gw_parts_g {c : Ordinal.{0}} (hcE : gfE ≤ c) (hg : gwG c < x) :
    gtc (c / gfE ^ log gfE c) < x ∧ gwG (c % gfE ^ log gfE c) < x := by
  obtain ⟨-, -, hdE, -, -⟩ := gw_parts hcE
  rw [gwG_dec hcE] at hg
  exact ⟨gtc_lt_of_giQ (omega0_lt_inE hx) ((le_max_left _ _).trans_lt hg) hdE, (le_max_right _ _).trans_lt hg⟩

/-- **`c < E^k ⇒ c(x) < ε_{x+1}^k`.** -/
theorem gwR_bound : ∀ c, gwG c < x → ∀ k : Ordinal.{0}, k ≠ 0 → c < gfE ^ k → gwR c x < eN x ^ k := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hg k hk hck
  have h1k : eN x ≤ eN x ^ k := by
    calc eN x = eN x ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ eN x ^ k := opow_le_opow_right (eN_E x).pos (one_le_iff_ne_zero.2 hk)
  rcases lt_or_ge c gfE with hcE | hcE
  · rw [gwG_low hcE] at hg
    rw [gwR_low hcE]; exact (rdc_lt_eN hx c hg).trans_le h1k
  obtain ⟨hj, hd0, hdE, hr, -⟩ := gw_parts hcE
  obtain ⟨g1, g2⟩ := gw_parts_g hx hcE hg
  have hjk : log gfE c < k := (lt_opow_iff_log_lt gw_one_lt (gw_ne_of_le hcE)).1 hck
  have hrc : c % gfE ^ log gfE c < c := mod_opow_log_lt_self gfE (gw_ne_of_le hcE)
  have hrr := IH _ hrc g2 _ hj hr
  rw [gwR_dec hcE]
  calc eN x ^ log gfE c * rdc (c / gfE ^ log gfE c) x + gwR (c % gfE ^ log gfE c) x
      < eN x ^ log gfE c * rdc (c / gfE ^ log gfE c) x + eN x ^ log gfE c := (add_lt_add_iff_left _).2 hrr
    _ = eN x ^ log gfE c * (rdc (c / gfE ^ log gfE c) x + 1) := by rw [mul_add_one]
    _ ≤ eN x ^ log gfE c * eN x := mul_le_mul_left' (Order.add_one_le_of_lt (rdc_lt_eN hx _ g1)) _
    _ = eN x ^ (log gfE c + 1) := by rw [opow_add, opow_one]
    _ ≤ eN x ^ k := opow_le_opow_right (eN_E x).pos (Order.add_one_le_of_lt hjk)

theorem gw_lead_le {c : Ordinal.{0}} (hcE : gfE ≤ c) : eN x ^ log gfE c ≤ gwR c x := by
  obtain ⟨-, hd0, hdE, -, -⟩ := gw_parts hcE
  rw [gwR_dec hcE]
  calc eN x ^ log gfE c = eN x ^ log gfE c * 1 := (mul_one _).symm
    _ ≤ eN x ^ log gfE c * rdc (c / gfE ^ log gfE c) x :=
        mul_le_mul_left' (one_le_iff_pos.2 (rdc_pos hx hd0 hdE)) _
    _ ≤ _ := le_self_add

/-- **The reading is strictly increasing.** -/
theorem gwR_mono : ∀ c, gwG c < x → ∀ b, b < c → gwG b < x → gwR b x < gwR c x := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hgc b hbc hgb
  rcases lt_or_ge c gfE with hcE | hcE
  · have hbE := hbc.trans hcE
    rw [gwG_low hcE] at hgc
    rw [gwG_low hbE] at hgb
    rw [gwR_low hcE, gwR_low hbE]
    exact rdc_mono hx hcE hbc hgc hgb
  have hjc : log gfE c ≠ 0 := (gw_parts hcE).1
  have h1 : eN x ≤ eN x ^ log gfE c := by
    calc eN x = eN x ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ eN x ^ log gfE c := opow_le_opow_right (eN_E x).pos (one_le_iff_ne_zero.2 hjc)
  rcases lt_or_ge b gfE with hbE | hbE
  · rw [gwG_low hbE] at hgb
    rw [gwR_low hbE]
    exact ((rdc_lt_eN hx b hgb).trans_le h1).trans_le (gw_lead_le hx hcE)
  have hkk : log gfE b ≤ log gfE c := log_mono_right _ hbc.le
  rcases hkk.lt_or_eq with hlt | heq
  · have hb1 : b < gfE ^ (log gfE b + 1) :=
      (lt_opow_iff_log_lt gw_one_lt (gw_ne_of_le hbE)).2 (lt_add_one _)
    calc gwR b x < eN x ^ (log gfE b + 1) := gwR_bound hx b hgb _ (lt_of_le_of_lt zero_le (lt_add_one _)).ne' hb1
      _ ≤ eN x ^ log gfE c := opow_le_opow_right (eN_E x).pos (Order.add_one_le_of_lt hlt)
      _ ≤ gwR c x := gw_lead_le hx hcE
  obtain ⟨hk, hd0, hdE, hr, hdec⟩ := gw_parts hcE
  obtain ⟨-, hd0', hdE', hr', hdec'⟩ := gw_parts hbE
  obtain ⟨g1, g2⟩ := gw_parts_g hx hcE hgc
  obtain ⟨g1', g2'⟩ := gw_parts_g hx hbE hgb
  rw [heq] at hd0' hdE' hr' hdec' g1' g2'
  set k := log gfE c with hkdef
  set d := c / gfE ^ k
  set r := c % gfE ^ k
  set d' := b / gfE ^ k
  set r' := b % gfE ^ k
  have hdd : d' ≤ d := by
    by_contra hlt
    push Not at hlt
    have : c < b := by
      calc c = gfE ^ k * d + r := hdec.symm
        _ < gfE ^ k * d + gfE ^ k := (add_lt_add_iff_left _).2 hr
        _ = gfE ^ k * (d + 1) := by rw [mul_add_one]
        _ ≤ gfE ^ k * d' := mul_le_mul_left' (Order.add_one_le_of_lt hlt) _
        _ ≤ b := by rw [← hdec']; exact le_self_add
    exact absurd hbc (not_lt.2 this.le)
  have eb : gwR b x = eN x ^ k * rdc d' x + gwR r' x := by rw [gwR_dec hbE, heq]
  have ec : gwR c x = eN x ^ k * rdc d x + gwR r x := gwR_dec hcE x
  rw [eb, ec]
  rcases hdd.lt_or_eq with hd | hd
  · have hrb := gwR_bound hx r' g2' k hk hr'
    calc eN x ^ k * rdc d' x + gwR r' x < eN x ^ k * rdc d' x + eN x ^ k := (add_lt_add_iff_left _).2 hrb
      _ = eN x ^ k * (rdc d' x + 1) := by rw [mul_add_one]
      _ ≤ eN x ^ k * rdc d x := mul_le_mul_left' (Order.add_one_le_of_lt (rdc_mono hx hdE hd g1 g1')) _
      _ ≤ _ := le_self_add
  · have hrr : r' < r := by
      have hb' : b = gfE ^ k * d + r' := by rw [← hd]; exact hdec'.symm
      have hc' : c = gfE ^ k * d + r := hdec.symm
      have h3 := hbc
      rw [hb', hc'] at h3
      exact (add_lt_add_iff_left _).1 h3
    have hrc : r < c := mod_opow_log_lt_self gfE (gw_ne_of_le hcE)
    rw [hd]
    exact (add_lt_add_iff_left _).2 (IH r hrc g2 r' hrr g2')

theorem gwR_lt0 (hx1 : x < Om1) {c : Ordinal.{0}} (hc : c < gwB) (hg : gwG c < x) : gwR c x < gq 0 x := by
  have hE := (gfq0_facts hx hx1).2.2.2
  have he := gh_eN_lt_gq0 hx hx1
  rcases lt_or_ge c gfE with hcE | hcE
  · rw [gwG_low hcE] at hg; rw [gwR_low hcE]; exact (rdc_lt_eN hx c hg).trans he
  obtain ⟨n, hn⟩ := gw_nat_of_lt hc hcE
  have hb1 : c < gfE ^ ((n : Ordinal.{0}) + 1) := by
    rw [← hn]; exact (lt_opow_iff_log_lt gw_one_lt (gw_ne_of_le hcE)).2 (lt_add_one _)
  refine (gwR_bound hx c hg _ (lt_of_le_of_lt zero_le (lt_add_one _)).ne' hb1).trans ?_
  rw [gw_eNpow]
  have hn1 : (n : Ordinal.{0}) + 1 < ω := by
    have := natCast_lt_omega0 (n + 1); push_cast at this; exact this
  have h2 : eN x * ((n : Ordinal.{0}) + 1) < gq 0 x :=
    hE.mul_lt he (hn1.trans (omega0_lt_inE hE))
  have := (opow_lt_opow_iff_right one_lt_omega0).2 h2
  rwa [show ω ^ gq 0 x = gq 0 x from hE] at this

end Base

end Googology.Trans.PoR.InaccPsi.R2.Gi
