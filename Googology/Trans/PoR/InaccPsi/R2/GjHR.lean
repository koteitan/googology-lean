import Googology.Trans.PoR.InaccPsi.R2.GjHG

/-!
# HEREDITARY CODES BELOW `ε_{Ω₁+2}`: the order of the readings

* `jhR_succ`, `jh_lead_le`, `jhR_bound_of` (**`c < E^κ ⇒ c(x) < ε_{x+1}^{κ(x)}`** once the readings of the codes below a
  bound `N > c, κ` are increasing), `jhR_mono` (**the reading is strictly increasing**, by induction on the code, the
  exponents being smaller codes), `jhR_bound`, `jhR_lt0` (**below `Γ_{x+1}`**), `jhR_lt_eNN` (**below `ε_{x+2}`**).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gj

open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gi
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Gd Googology.Trans.PoR.InaccPsi.R2.Gb

theorem jhR_succ : ∀ b, b + 1 < jhB → ∀ x : Ordinal.{0}, jhR (b + 1) x = jhR b x + 1 := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb1 x
  have hbB : b < jhB := (lt_add_one b).trans hb1
  rcases lt_or_ge b gfE with hbE | hbE
  · rw [jhR_low hbE, jhR_low (succ_lt_eW hbE), (rdc_succ b hbE x).1]
  obtain ⟨hk, hd0, hdE, hr, -, -, hrb⟩ := jh_parts hbE hbB
  obtain ⟨e, hr1⟩ := jh_succ_cnf hbE hbB
  have hr1B : b % gfE ^ log gfE b + 1 < jhB := lt_of_le_of_lt (by rw [e]; exact le_add_self) hb1
  rw [e, jhR_cnf hk hd0 hdE hr1 (e ▸ hb1), IH _ hrb hr1B x, jhR_dec hbE hbB x, add_assoc]

/-- The readings of the codes below `j` are below the reading of `j`. -/
def JhMonoAt (x j : Ordinal.{0}) : Prop := ∀ b, b < j → jhG j < x → jhG b < x → jhR b x < jhR j x

section Base

variable {x : Ordinal.{0}} (hx : InE x)
include hx

theorem jh_parts_g {c : Ordinal.{0}} (hcE : gfE ≤ c) (hcB : c < jhB) (hg : jhG c < x) :
    jhG (log gfE c) < x ∧ gtc (c / gfE ^ log gfE c) < x ∧ jhG (c % gfE ^ log gfE c) < x := by
  obtain ⟨-, -, hdE, -, -, -, -⟩ := jh_parts hcE hcB
  rw [jhG_dec hcE hcB] at hg
  have hωx := omega0_lt_inE hx
  exact ⟨jhG_of_Q hωx ((le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hg)),
    gtc_lt_of_giQ hωx ((le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hg)) hdE,
    (le_max_right _ _).trans_lt hg⟩

theorem jh_lead_le {c : Ordinal.{0}} (hcE : gfE ≤ c) (hcB : c < jhB) :
    eN x ^ jhR (log gfE c) x ≤ jhR c x := by
  obtain ⟨-, hd0, hdE, -, -, -, -⟩ := jh_parts hcE hcB
  rw [jhR_dec hcE hcB]
  calc eN x ^ jhR (log gfE c) x = eN x ^ jhR (log gfE c) x * 1 := (mul_one _).symm
    _ ≤ eN x ^ jhR (log gfE c) x * rdc (c / gfE ^ log gfE c) x :=
        mul_le_mul_left' (one_le_iff_pos.2 (rdc_pos hx hd0 hdE)) _
    _ ≤ _ := le_self_add

theorem jh_eN_le_pow {k : Ordinal.{0}} (hk : k ≠ 0) (hkB : k < jhB) : eN x ≤ eN x ^ jhR k x := by
  calc eN x = eN x ^ (1 : Ordinal.{0}) := (opow_one _).symm
    _ ≤ eN x ^ jhR k x := opow_le_opow_right (eN_E x).pos (one_le_iff_pos.2 (jhR_pos hx hk hkB))

/-- **`c < E^κ ⇒ c(x) < ε_{x+1}^{κ(x)}`**, once the readings are increasing at the codes below a bound `N > c, κ`. -/
theorem jhR_bound_of {N : Ordinal.{0}} (hN : ∀ j, j < N → JhMonoAt x j) : ∀ c, c < N → c < jhB → jhG c < x →
    ∀ κ, κ ≠ 0 → κ < N → κ < jhB → jhG κ < x → c < gfE ^ κ → jhR c x < eN x ^ jhR κ x := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcN hcB hg κ hκ hκN hκB hgκ hcκ
  rcases lt_or_ge c gfE with hcE | hcE
  · rw [jhG_low hcE] at hg
    rw [jhR_low hcE]; exact (rdc_lt_eN hx c hg).trans_le (jh_eN_le_pow hx hκ hκB)
  obtain ⟨hj, hd0, hdE, hr, -, hjc, hrc⟩ := jh_parts hcE hcB
  obtain ⟨g0, g1, g2⟩ := jh_parts_g hx hcE hcB hg
  have hjk : log gfE c < κ := (lt_opow_iff_log_lt gw_one_lt (gw_ne_of_le hcE)).1 hcκ
  have hrr := IH _ hrc (hrc.trans hcN) (hrc.trans hcB) g2 _ hj (hjc.trans hcN) (hjc.trans hcB) g0 hr
  have hjx : jhR (log gfE c) x < jhR κ x := hN κ hκN _ hjk hgκ g0
  rw [jhR_dec hcE hcB]
  calc eN x ^ jhR (log gfE c) x * rdc (c / gfE ^ log gfE c) x + jhR (c % gfE ^ log gfE c) x
      < eN x ^ jhR (log gfE c) x * rdc (c / gfE ^ log gfE c) x + eN x ^ jhR (log gfE c) x :=
        (add_lt_add_iff_left _).2 hrr
    _ = eN x ^ jhR (log gfE c) x * (rdc (c / gfE ^ log gfE c) x + 1) := by rw [mul_add_one]
    _ ≤ eN x ^ jhR (log gfE c) x * eN x := mul_le_mul_left' (Order.add_one_le_of_lt (rdc_lt_eN hx _ g1)) _
    _ = eN x ^ (jhR (log gfE c) x + 1) := by rw [opow_add, opow_one]
    _ ≤ eN x ^ jhR κ x := opow_le_opow_right (eN_E x).pos (Order.add_one_le_of_lt hjx)

/-- **The reading is strictly increasing.** -/
theorem jhR_mono : ∀ c, c < jhB → JhMonoAt x c := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcB b hbc hgc hgb
  have hIH : ∀ j, j < c → JhMonoAt x j := fun j hj => IH j hj (hj.trans hcB)
  rcases lt_or_ge c gfE with hcE | hcE
  · have hbE := hbc.trans hcE
    rw [jhG_low hcE] at hgc
    rw [jhG_low hbE] at hgb
    rw [jhR_low hcE, jhR_low hbE]
    exact rdc_mono hx hcE hbc hgc hgb
  obtain ⟨hjc0, -, -, -, -, hjc, -⟩ := jh_parts hcE hcB
  obtain ⟨gc0, gc1, gc2⟩ := jh_parts_g hx hcE hcB hgc
  rcases lt_or_ge b gfE with hbE | hbE
  · rw [jhG_low hbE] at hgb
    rw [jhR_low hbE]
    exact ((rdc_lt_eN hx b hgb).trans_le (jh_eN_le_pow hx hjc0 (hjc.trans hcB))).trans_le (jh_lead_le hx hcE hcB)
  have hbB : b < jhB := hbc.trans hcB
  obtain ⟨-, -, -, -, -, hjb, -⟩ := jh_parts hbE hbB
  obtain ⟨gb0, gb1, gb2⟩ := jh_parts_g hx hbE hbB hgb
  have hkk : log gfE b ≤ log gfE c := log_mono_right _ hbc.le
  rcases hkk.lt_or_eq with hlt | heq
  · have hb1 : b < gfE ^ (log gfE b + 1) :=
      (lt_opow_iff_log_lt gw_one_lt (gw_ne_of_le hbE)).2 (lt_add_one _)
    have hs1 : log gfE b + 1 ≤ log gfE c := Order.add_one_le_of_lt hlt
    have hs1c : log gfE b + 1 < c := lt_of_le_of_lt hs1 hjc
    have hs1B : log gfE b + 1 < jhB := hs1c.trans hcB
    have hgs : jhG (log gfE b + 1) < x := jhG_succ (ev_isSuccLimit_of_inE hx) _ hs1B gb0
    have hmono : jhR (log gfE b) x < jhR (log gfE c) x := hIH _ hjc _ hlt gc0 gb0
    calc jhR b x < eN x ^ jhR (log gfE b + 1) x :=
          jhR_bound_of hx hIH b hbc hbB hgb _ (lt_of_le_of_lt zero_le (lt_add_one _)).ne' hs1c hs1B hgs hb1
      _ = eN x ^ (jhR (log gfE b) x + 1) := by rw [jhR_succ _ hs1B]
      _ ≤ eN x ^ jhR (log gfE c) x := opow_le_opow_right (eN_E x).pos (Order.add_one_le_of_lt hmono)
      _ ≤ jhR c x := jh_lead_le hx hcE hcB
  obtain ⟨hk, hd0, hdE, hr, hdec, -, hrc⟩ := jh_parts hcE hcB
  obtain ⟨-, hd0', hdE', hr', hdec', -, hrb⟩ := jh_parts hbE hbB
  rw [heq] at hd0' hdE' hr' hdec' gb1 gb2 hrb
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
  have eb : jhR b x = eN x ^ jhR k x * rdc d' x + jhR r' x := by rw [jhR_dec hbE hbB, heq]
  have ec : jhR c x = eN x ^ jhR k x * rdc d x + jhR r x := jhR_dec hcE hcB x
  rw [eb, ec]
  rcases hdd.lt_or_eq with hd | hd
  · have hr'c : r' < c := hrb.trans hbc
    have hrb' := jhR_bound_of hx hIH r' hr'c (hr'c.trans hcB) gb2 k hk hjc (hjc.trans hcB) gc0 hr'
    calc eN x ^ jhR k x * rdc d' x + jhR r' x < eN x ^ jhR k x * rdc d' x + eN x ^ jhR k x :=
          (add_lt_add_iff_left _).2 hrb'
      _ = eN x ^ jhR k x * (rdc d' x + 1) := by rw [mul_add_one]
      _ ≤ eN x ^ jhR k x * rdc d x := mul_le_mul_left' (Order.add_one_le_of_lt (rdc_mono hx hdE hd gc1 gb1)) _
      _ ≤ _ := le_self_add
  · have hrr : r' < r := by
      have hb' : b = gfE ^ k * d + r' := by rw [← hd]; exact hdec'.symm
      have hc' : c = gfE ^ k * d + r := hdec.symm
      have h3 := hbc
      rw [hb', hc'] at h3
      exact (add_lt_add_iff_left _).1 h3
    rw [hd]
    exact (add_lt_add_iff_left _).2 (hIH r hrc r' hrr gc2 gb2)

/-- **`c < E^κ ⇒ c(x) < ε_{x+1}^{κ(x)}`.** -/
theorem jhR_bound {c κ : Ordinal.{0}} (hcB : c < jhB) (hg : jhG c < x) (hκ : κ ≠ 0) (hκB : κ < jhB)
    (hgκ : jhG κ < x) (hcκ : c < gfE ^ κ) : jhR c x < eN x ^ jhR κ x :=
  jhR_bound_of hx (fun j hj => jhR_mono hx j hj) c hcB hcB hg κ hκ hκB hκB hgκ hcκ

/-- `c(x) < ε_{x+1}^{(log_E c)(x)+1}`. -/
theorem jhR_lt_succ {c : Ordinal.{0}} (hcE : gfE ≤ c) (hcB : c < jhB) (hg : jhG c < x) :
    jhR c x < eN x ^ (jhR (log gfE c) x + 1) := by
  obtain ⟨-, -, -, -, -, hjc, -⟩ := jh_parts hcE hcB
  obtain ⟨g0, -, -⟩ := jh_parts_g hx hcE hcB hg
  have hs1B : log gfE c + 1 < jhB := lt_of_le_of_lt (Order.add_one_le_of_lt hjc) hcB
  have hgs : jhG (log gfE c + 1) < x := jhG_succ (ev_isSuccLimit_of_inE hx) _ hs1B g0
  have hb1 : c < gfE ^ (log gfE c + 1) :=
    (lt_opow_iff_log_lt gw_one_lt (gw_ne_of_le hcE)).2 (lt_add_one _)
  rw [← jhR_succ _ hs1B]
  exact jhR_bound hx hcB hg (lt_of_le_of_lt zero_le (lt_add_one _)).ne' hs1B hgs hb1

/-- **The readings lie below every `ε`-number `u > ε_{x+1}`** (`Γ_{x+1}`, `ε_{x+2}`, …). -/
theorem jhR_lt_E {u : Ordinal.{0}} (hu : InE u) (heu : eN x < u) : ∀ c, c < jhB → jhG c < x → jhR c x < u := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcB hg
  rcases lt_or_ge c gfE with hcE | hcE
  · rw [jhG_low hcE] at hg; rw [jhR_low hcE]; exact (rdc_lt_eN hx c hg).trans heu
  obtain ⟨-, -, -, -, -, hjc, -⟩ := jh_parts hcE hcB
  obtain ⟨g0, -, -⟩ := jh_parts_g hx hcE hcB hg
  have hK := IH _ hjc (hjc.trans hcB) g0
  refine (jhR_lt_succ hx hcE hcB hg).trans ?_
  rw [gw_eNpow]
  have h2 : eN x * (jhR (log gfE c) x + 1) < u :=
    hu.mul_lt heu ((inE_indec hu).add_lt hK (one_lt_omega0.trans (omega0_lt_inE hu)))
  have := (opow_lt_opow_iff_right one_lt_omega0).2 h2
  rwa [show ω ^ u = u from hu] at this

theorem jhR_lt0 (hx1 : x < Om1) {c : Ordinal.{0}} (hc : c < jhB) (hg : jhG c < x) : jhR c x < gq 0 x :=
  jhR_lt_E hx (gfq0_facts hx hx1).2.2.2 (gh_eN_lt_gq0 hx hx1) c hc hg

theorem jhR_lt_eNN {c : Ordinal.{0}} (hc : c < jhB) (hg : jhG c < x) : jhR c x < eN (eN x) :=
  jhR_lt_E hx (eN_E _) (lt_eN _) c hc hg

end Base

end Googology.Trans.PoR.InaccPsi.R2.Gj
