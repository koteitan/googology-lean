import Googology.Trans.PoR.InaccPsi.R2.GkU1

/-!
# CODES BELOW `ζ_{Ω₁+1}`: the reading is strictly increasing

One well-founded induction proves, at every `ε`-number `x` and for the codes with gates below `x`, both

* `GuMo x c`: the codes below `c` read below `c(x)`, and
* `GuTop x c`: a code `c ≥ ε_{Ω₁+1}` reads below the NEXT pseudo-base `ε_{x+ν(x)+1}` (`ν = guN c`).

Codes of a lower bracket read below the pseudo-base of a higher one (`gu_lt_base`); inside one bracket the argument
of `R2.GjHR` (`E^k·d + r`, now `E = ε_{Ω₁+ν}` arbitrary) applies (`gu_bound_of`).

* `guA_succ`, `guA_le`, `guA_lt`, `gu_pow_lt_eN`, `gu_lt_pow` (`k < E^k` for `k < ε_{E+1}`);
* `GuMo`, `GuTop`, `gu_lt_base`, `gu_bound_of`, `gu_mono_top` (**the induction**), `guR_mono`, `guR_top`,
  `guR_lt_base` (**codes below `ε_{Ω₁+m}` read below `ε_{x+m(x)}`**).

No new axiom.  New definitions: `GuMo`, `GuTop`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gk

open Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Gi
open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2

theorem guA_succ (x : Ordinal.{0}) {m : Ordinal.{0}} (hm : 1 ≤ m) : guA x (m + 1) = eN (guA x m) := by
  have e : m + 1 - 1 = m - 1 + 1 := by
    conv_lhs => rw [← Ordinal.add_sub_cancel_of_le hm]
    rw [add_assoc, Ordinal.add_sub_cancel]
  rw [guA, guA, e, evA_add_one]

theorem guA_sub_lt {m m' : Ordinal.{0}} (hm : 1 ≤ m) (hmm : m < m') : m - 1 < m' - 1 := by
  have h1 : 1 ≤ m' := hm.trans hmm.le
  have e1 := Ordinal.add_sub_cancel_of_le hm
  have e2 := Ordinal.add_sub_cancel_of_le h1
  rw [← e1, ← e2] at hmm
  exact (add_lt_add_iff_left _).1 hmm

theorem guA_lt (x : Ordinal.{0}) {m m' : Ordinal.{0}} (hm : 1 ≤ m) (hmm : m < m') : guA x m < guA x m' :=
  evA_lt_iff.2 (guA_sub_lt hm hmm)

theorem guA_le (x : Ordinal.{0}) {m m' : Ordinal.{0}} (hm : 1 ≤ m) (hmm : m ≤ m') : guA x m ≤ guA x m' := by
  rcases hmm.lt_or_eq with h | h
  · exact (guA_lt x hm h).le
  · rw [h]

theorem gu_eN_le_guA (x : Ordinal.{0}) {m : Ordinal.{0}} (hm : 1 ≤ m) : eN x ≤ guA x m := by
  rw [← guA_one]; exact guA_le x le_rfl hm

theorem gu_pow_lt_eN {B y : Ordinal.{0}} (hB : InE B) (hy : y < eN B) : B ^ y < eN B := by
  rw [gu_pow_eq hB]
  exact (eN_E B).opow_lt ((eN_E B).mul_lt (lt_eN B) hy)

/-- `k < E^k` for every `k < ε_{E+1}` (`E` an `ε`-number). -/
theorem gu_lt_pow {E k : Ordinal.{0}} (hE : InE E) (hk : k < eN E) : k < E ^ k := by
  have hE1 : (1 : Ordinal.{0}) < E := Lu.lu_one_lt_E hE
  rcases eq_or_ne k 0 with rfl | hk0
  · rw [opow_zero]; exact zero_lt_one
  rcases (right_le_opow k hE1).lt_or_eq with h | h
  · exact h
  exfalso
  have hkE : InE k := by
    refine le_antisymm ?_ (right_le_opow k one_lt_omega0)
    calc ω ^ k ≤ ω ^ (E * k) := opow_le_opow_right omega0_pos (le_mul_right k hE.pos)
      _ = E ^ k := (gu_pow_eq hE k).symm
      _ = k := h.symm
  rcases lt_or_ge E k with hEk | hkE'
  · exact absurd ((eN_le hEk hkE).trans_lt hk) (lt_irrefl _)
  · have : k < E ^ k := by
      rcases hkE'.lt_or_eq with hlt | heq
      · calc k < E := hlt
          _ = E ^ (1 : Ordinal.{0}) := (opow_one _).symm
          _ ≤ E ^ k := opow_le_opow_right hE.pos (one_le_iff_ne_zero.2 hk0)
      · rw [heq]; exact (opow_lt_opow_iff_right hE1).2 hE1 |>.trans_le' (by rw [opow_one])
    exact absurd h this.ne

/-- The readings of the codes below `j` are below the reading of `j`. -/
def GuMo (x j : Ordinal.{0}) : Prop := ∀ b, b < j → guG j < x → guG b < x → guR b x < guR j x

/-- A code `c ≥ ε_{Ω₁+1}` reads below the next pseudo-base `ε_{x+ν(x)+1}`. -/
def GuTop (x c : Ordinal.{0}) : Prop := gfE ≤ c → guG c < x → guR c x < guA x (guR (guN c) x + 1)

section Mono

variable {x : Ordinal.{0}} (hx : InE x)
include hx

/-- **Codes below `ε_{Ω₁+m}` read below `ε_{x+m(x)}`**, given the top bound at `b` and the order at `m`. -/
theorem gu_lt_base {b m : Ordinal.{0}} (hm1 : 1 ≤ m) (hmB : m < guB) (hgm : guG m < x) (hbm : b < evA Om1 m)
    (hgb : guG b < x) (hTb : GuTop x b) (hMm : GuMo x m) : guR b x < guA x (guR m x) := by
  have hωx := omega0_lt_inE hx
  have hRm : 1 ≤ guR m x := one_le_iff_pos.2 (guR_pos hx m (one_le_iff_ne_zero.1 hm1) hmB)
  rcases lt_or_ge b gfE with hbE | hbE
  · rw [guG_low hbE] at hgb
    rw [guR_low hbE]
    exact (rdc_lt_eN hx b hgb).trans_le (gu_eN_le_guA x hRm)
  have hbB : b < guB := hbm.trans (gu_evA_lt hmB)
  obtain ⟨hn1, hnb, -, -, -⟩ := guN_spec hbE hbB
  have hnm : guN b < m := evA_lt_iff.1 (lt_of_le_of_lt hnb hbm)
  obtain ⟨g0, -, -, -⟩ := gu_parts_g hωx hbE hbB hgb
  have h1 := hTb hbE hgb
  have h2 : guR (guN b) x < guR m x := hMm _ hnm hgm g0
  have hRn : 1 ≤ guR (guN b) x + 1 := le_add_self
  exact h1.trans_le (guA_le x hRn (add_one_le_of_lt h2))

/-- **`c < E^κ ⇒ c(x) < ε_{x+n(x)}^{κ(x)}`** (`E = ε_{Ω₁+n}`, `c < ε_{E+1}`), once the order and the top bound hold
below a bound `N > c, κ, n`. -/
theorem gu_bound_of {N n : Ordinal.{0}} (hM : ∀ j, j < N → GuMo x j) (hT : ∀ j, j < N → GuTop x j)
    (hn1 : 1 ≤ n) (hnN : n < N) (hnB : n < guB) (hgn : guG n < x) : ∀ c, c < N → c < guB → guG c < x →
    c < evA Om1 (n + 1) → ∀ κ, κ ≠ 0 → κ < N → κ < guB → guG κ < x → c < evA Om1 n ^ κ →
    guR c x < guA x (guR n x) ^ guR κ x := by
  have hωx := omega0_lt_inE hx
  set E := evA Om1 n with hEdef
  have hE : InE E := evA_E _ _
  set B := guA x (guR n x) with hBdef
  have hBE : InE B := guA_E _ _
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcN hcB hg hcn κ hκ hκN hκB hgκ hcκ
  have hBκ : B ≤ B ^ guR κ x := by
    calc B = B ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ B ^ guR κ x := opow_le_opow_right hBE.pos (one_le_iff_pos.2 (guR_pos hx κ hκ hκB))
  rcases lt_or_ge c E with hcE | hcE
  · exact (gu_lt_base hx hn1 hnB hgn hcE hg (hT c hcN) (hM n hnN)).trans_le hBκ
  have hgfc : gfE ≤ c := (by rw [← gu_evA_one, hEdef]; exact evA_le_iff.2 hn1 : gfE ≤ E).trans hcE
  have hNc : guN c = n := guN_eq hcE hcn
  have hEc : guE c = E := by rw [guE, hNc]
  obtain ⟨hj, hd0, hdE, hr, -, hjc, hrc, hdc⟩ := gu_parts hgfc hcB
  obtain ⟨-, g0, g1, g2⟩ := gu_parts_g hωx hgfc hcB hg
  rw [hEc] at hj hd0 hdE hr hjc hrc hdc g0 g1 g2
  have hjk : log E c < κ := (lt_opow_iff_log_lt (Lu.lu_one_lt_E hE) (hE.pos.trans_le hcE).ne').1 hcκ
  have hrr := IH _ hrc (hrc.trans hcN) (hrc.trans hcB) g2 ((hrc.trans hcn)) _ hj (hjc.trans hcN)
    (hjc.trans hcB) g0 hr
  have hjx : guR (log E c) x < guR κ x := hM κ hκN _ hjk hgκ g0
  have hdB : guR (c / E ^ log E c) x < B :=
    gu_lt_base hx hn1 hnB hgn hdE g1 (hT _ (hdc.trans hcN)) (hM n hnN)
  rw [guR_dec hgfc hcB, hNc, hEc]
  calc B ^ guR (log E c) x * guR (c / E ^ log E c) x + guR (c % E ^ log E c) x
      < B ^ guR (log E c) x * guR (c / E ^ log E c) x + B ^ guR (log E c) x :=
        (add_lt_add_iff_left _).2 hrr
    _ = B ^ guR (log E c) x * (guR (c / E ^ log E c) x + 1) := by rw [mul_add_one]
    _ ≤ B ^ guR (log E c) x * B := mul_le_mul_right (add_one_le_of_lt hdB) _
    _ = B ^ (guR (log E c) x + 1) := by rw [opow_add, opow_one]
    _ ≤ B ^ guR κ x := opow_le_opow_right hBE.pos (add_one_le_of_lt hjx)

/-- **THE INDUCTION**: the order and the top bound at every code below `ζ_{Ω₁+1}`. -/
theorem gu_mono_top : ∀ c, c < guB → GuMo x c ∧ GuTop x c := by
  have hωx := omega0_lt_inE hx
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcB
  have hM : ∀ j, j < c → GuMo x j := fun j hj => (IH j hj (hj.trans hcB)).1
  have hT : ∀ j, j < c → GuTop x j := fun j hj => (IH j hj (hj.trans hcB)).2
  -- the top bound at `c`
  have hTc : GuTop x c := by
    intro hgfc hg
    obtain ⟨hn1, -, hcn, hnB, hnc⟩ := guN_spec hgfc hcB
    obtain ⟨hk, -, hdE, hr, -, hkc, hrc, hdc⟩ := gu_parts hgfc hcB
    obtain ⟨g0n, g0, g1, g2⟩ := gu_parts_g hωx hgfc hcB hg
    have hEc : guE c = evA Om1 (guN c) := rfl
    rw [hEc] at hk hdE hr hkc hrc hdc g0 g1 g2
    set n := guN c with hndef
    set E := evA Om1 n with hEdef
    have hE : InE E := evA_E _ _
    set k := log E c with hkdef
    set B := guA x (guR n x) with hBdef
    have hBE : InE B := guA_E _ _
    have hcN' : c < eN E := by rw [hEdef, ← evA_add_one]; exact hcn
    have hrr : guR (c % E ^ k) x < B ^ guR k x :=
      gu_bound_of hx hM hT hn1 hnc hnB g0n _ hrc (hrc.trans hcB) g2 (hrc.trans hcn) k hk hkc
        (hkc.trans hcB) g0 hr
    have hdB : guR (c / E ^ k) x < B := gu_lt_base hx hn1 hnB g0n hdE g1 (hT _ hdc) (hM n hnc)
    have hkB : guR k x < eN B := by
      rcases lt_or_ge k E with hkE | hkE
      · exact (gu_lt_base hx hn1 hnB g0n hkE g0 (hT _ hkc) (hM n hnc)).trans (lt_eN B)
      · have hgk : gfE ≤ k := (by rw [← gu_evA_one, hEdef]; exact evA_le_iff.2 hn1 : gfE ≤ E).trans hkE
        have hNk : guN k = n := guN_eq hkE (hkc.trans hcn)
        have := hT k hkc hgk g0
        rwa [hNk, guA_succ x (gu_one_le_N hx hgfc hcB)] at this
    have hlt : guR c x < B ^ (guR k x + 1) := by
      rw [guR_dec hgfc hcB]
      calc B ^ guR k x * guR (c / E ^ k) x + guR (c % E ^ k) x
          < B ^ guR k x * guR (c / E ^ k) x + B ^ guR k x := (add_lt_add_iff_left _).2 hrr
        _ = B ^ guR k x * (guR (c / E ^ k) x + 1) := by rw [mul_add_one]
        _ ≤ B ^ guR k x * B := mul_le_mul_right (add_one_le_of_lt hdB) _
        _ = B ^ (guR k x + 1) := by rw [opow_add, opow_one]
    rw [guA_succ x (gu_one_le_N hx hgfc hcB)]
    exact hlt.trans (gu_pow_lt_eN hBE ((ev_isSuccLimit_of_inE (eN_E B)).add_one_lt hkB))
  refine ⟨fun b hbc hgc hgb => ?_, hTc⟩
  rcases lt_or_ge c gfE with hcE | hcE
  · have hbE := hbc.trans hcE
    rw [guG_low hcE] at hgc
    rw [guG_low hbE] at hgb
    rw [guR_low hcE, guR_low hbE]
    exact rdc_mono hx hcE hbc hgc hgb
  obtain ⟨hn1, -, hcn, hnB, hnc⟩ := guN_spec hcE hcB
  obtain ⟨gcn, gck, gcd, gcr⟩ := gu_parts_g hωx hcE hcB hgc
  have hlead := gu_lead hx hcE hcB
  rcases lt_or_ge b gfE with hbE | hbE
  · rw [guG_low hbE] at hgb
    rw [guR_low hbE]
    exact ((rdc_lt_eN hx b hgb).trans_le (gu_eN_le_guA x (gu_one_le_N hx hcE hcB))).trans_le hlead.2
  have hbB : b < guB := hbc.trans hcB
  obtain ⟨hn1b, hnbb, -, -, hnbl⟩ := guN_spec hbE hbB
  obtain ⟨gbn, gbk, gbd, gbr⟩ := gu_parts_g hωx hbE hbB hgb
  have hnn : guN b ≤ guN c := by
    have := lt_of_le_of_lt hnbb (hbc.trans hcn)
    exact Order.lt_add_one_iff.1 (evA_lt_iff.1 this)
  rcases hnn.lt_or_eq with hnlt | hneq
  · have h1 := hT b hbc hbE hgb
    have h2 : guR (guN b) x < guR (guN c) x := hM _ hnc _ hnlt gcn gbn
    exact (h1.trans_le (guA_le x le_add_self (add_one_le_of_lt h2))).trans_le hlead.2
  -- the same bracket
  set n := guN c with hndef
  set E := evA Om1 n with hEdef
  have hE : InE E := evA_E _ _
  have hEb : guE b = E := by rw [guE, hneq]
  have hEc : guE c = E := rfl
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc, hdc⟩ := gu_parts hcE hcB
  obtain ⟨hk', hd0', hdE', hr', hdec', hkb, hrb, hdb⟩ := gu_parts hbE hbB
  rw [hEc] at hk hd0 hdE hr hdec hkc hrc hdc gck gcd gcr hlead
  rw [hEb] at hk' hd0' hdE' hr' hdec' hkb hrb hdb gbk gbd gbr
  rw [hneq] at gbn
  set B := guA x (guR n x) with hBdef
  have hBE : InE B := guA_E _ _
  have hE1 : (1 : Ordinal.{0}) < E := Lu.lu_one_lt_E hE
  have hbn : b < evA Om1 (n + 1) := hbc.trans hcn
  have hkk : log E b ≤ log E c := log_mono_right _ hbc.le
  have hRb : guR b x = B ^ guR (log E b) x * guR (b / E ^ log E b) x + guR (b % E ^ log E b) x := by
    rw [guR_dec hbE hbB, hEb, hneq]
  have hRc : guR c x = B ^ guR (log E c) x * guR (c / E ^ log E c) x + guR (c % E ^ log E c) x := by
    rw [guR_dec hcE hcB]; rfl
  have hpowc : B ^ guR (log E c) x ≤ guR c x := by
    refine le_trans ?_ hlead.1
    calc B ^ guR (log E c) x = B ^ guR (log E c) x * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_right (one_le_iff_pos.2 (guR_pos hx _ hd0 (hdc.trans hcB))) _
  rcases hkk.lt_or_eq with hlt | heq
  · have hs1 : log E b + 1 ≤ log E c := add_one_le_of_lt hlt
    have hs1c : log E b + 1 < c := lt_of_le_of_lt hs1 hkc
    have hs1B : log E b + 1 < guB := hs1c.trans hcB
    have hgs : guG (log E b + 1) < x := guG_succ (ev_isSuccLimit_of_inE hx) _ hs1B gbk
    have hb1 : b < E ^ (log E b + 1) := (lt_opow_iff_log_lt hE1 (hE.pos.trans_le (by
      rw [← hEb]; exact (guN_spec hbE hbB).2.1)).ne').2 (lt_add_one _)
    have hmono : guR (log E b) x < guR (log E c) x := hM _ hkc _ hlt gck gbk
    have hbd := gu_bound_of hx hM hT hn1 hnc hnB gcn b hbc hbB hgb hbn _
      (lt_of_le_of_lt zero_le (lt_add_one _)).ne' hs1c hs1B hgs hb1
    rw [guR_succ _ hs1B] at hbd
    exact (hbd.trans_le (opow_le_opow_right hBE.pos (add_one_le_of_lt hmono))).trans_le hpowc
  set k := log E c with hkdef
  rw [heq] at hd0' hdE' hr' hdec' hRb gbd gbr hrb
  set d := c / E ^ k
  set r := c % E ^ k
  set d' := b / E ^ k
  set r' := b % E ^ k
  have hdd : d' ≤ d := by
    by_contra hlt
    push Not at hlt
    have : c < b := by
      calc c = E ^ k * d + r := hdec.symm
        _ < E ^ k * d + E ^ k := (add_lt_add_iff_left _).2 hr
        _ = E ^ k * (d + 1) := by rw [mul_add_one]
        _ ≤ E ^ k * d' := mul_le_mul_right (add_one_le_of_lt hlt) _
        _ ≤ b := by rw [← hdec']; exact le_self_add
    exact absurd hbc (not_lt.2 this.le)
  rw [hRb, hRc]
  rcases hdd.lt_or_eq with hd | hd
  · have hr'c : r' < c := hrb.trans hbc
    have hrb' := gu_bound_of hx hM hT hn1 hnc hnB gcn r' hr'c (hr'c.trans hcB) gbr (hr'c.trans hcn) k hk hkc
      (hkc.trans hcB) gck hr'
    calc B ^ guR k x * guR d' x + guR r' x < B ^ guR k x * guR d' x + B ^ guR k x :=
          (add_lt_add_iff_left _).2 hrb'
      _ = B ^ guR k x * (guR d' x + 1) := by rw [mul_add_one]
      _ ≤ B ^ guR k x * guR d x := mul_le_mul_right (add_one_le_of_lt (hM _ hdc _ hd gcd gbd)) _
      _ ≤ _ := le_self_add
  · have hrr : r' < r := by
      have hb' : b = E ^ k * d + r' := by rw [← hd]; exact hdec'.symm
      have hc' : c = E ^ k * d + r := hdec.symm
      have h3 := hbc
      rw [hb', hc'] at h3
      exact (add_lt_add_iff_left _).1 h3
    rw [hd]
    exact (add_lt_add_iff_left _).2 (hM r hrc r' hrr gcr gbr)

theorem guR_mono {b c : Ordinal.{0}} (hc : c < guB) (hbc : b < c) (hgc : guG c < x) (hgb : guG b < x) :
    guR b x < guR c x := (gu_mono_top hx c hc).1 b hbc hgc hgb

theorem guR_top {c : Ordinal.{0}} (hc : c < guB) (h1 : gfE ≤ c) (hg : guG c < x) :
    guR c x < guA x (guR (guN c) x + 1) := (gu_mono_top hx c hc).2 h1 hg

/-- **Codes below `ε_{Ω₁+m}` read below `ε_{x+m(x)}`.** -/
theorem guR_lt_base {b m : Ordinal.{0}} (hm1 : 1 ≤ m) (hmB : m < guB) (hgm : guG m < x) (hbm : b < evA Om1 m)
    (hgb : guG b < x) : guR b x < guA x (guR m x) :=
  gu_lt_base hx hm1 hmB hgm hbm hgb (gu_mono_top hx b (hbm.trans (gu_evA_lt hmB))).2 (gu_mono_top hx m hmB).1

end Mono

end Googology.Trans.PoR.InaccPsi.R2.Gk
