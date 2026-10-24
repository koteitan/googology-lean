import Googology.Trans.PoR.InaccPsi.R2.GjHC

/-!
# HEREDITARY CODES BELOW `ε_{Ω₁+2}`: gates and hulls

* `jhG_lt_Om1`, `jhG_of_Q` (the gate of an exponent below `Z > ω` is the gate of the code), `jh_add` (**the gate of a
  sum**), `jh_div` (**`y/E` and `y mod E` keep the gate of a code `y ≥ E`**), `jh_code_gate` (**a code below `ε_{Ω₁+2}`
  over `Z`, atoms above `ε_{Ω₁+2}`, has its gate below `Z`**: `ω^y ∈ [E, ε_{E+1})` is `E^{y/E}·ω^{y mod E}`; the only
  `ε`-number in `[E, ε_{E+1})` is `E`);
* `jh_mulE` (**`E·k` is a code with `(E·k)(x) = ε_{x+1}·k(x)` and gate at most that of `k`**), `jh_mulE_lt_pow`
  (`E·k < E^k` for `k ≥ 2`);
* `jh_mem` (**every code lies in every hull containing its gate**), `jhB_eq` (`ε_{Ω₁+2} = φ(1, Ω₁+2)`), `jhB_mem`,
  `jhG_succ`, `jhG_le_succ`.

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gj

open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gi
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Gd

theorem jhG_lt_Om1 : ∀ c, c < jhB → jhG c < Om1 := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc
  rcases lt_or_ge c gfE with hcE | hcE
  · rw [jhG_low hcE]; exact gtc_lt_Om1 c hcE
  obtain ⟨-, -, hdE, -, -, hlc, hrc⟩ := jh_parts hcE hc
  rw [jhG_dec hcE hc]
  exact max_lt (max_lt ((jhQ_le _).trans_lt (IH _ hlc (hlc.trans hc)))
    ((giQ_le _).trans_lt (gtc_lt_Om1 _ hdE))) (IH _ hrc (hrc.trans hc))

/-- The gate of a code below `Z > ω` from the gate of it as an exponent. -/
theorem jhG_of_Q {k Z : Ordinal.{0}} (hωZ : ω < Z) (h : jhQ k < Z) : jhG k < Z := by
  unfold jhQ at h
  split_ifs at h with hk
  · obtain ⟨n, rfl⟩ := lt_omega0.1 hk
    have hn : (n : Ordinal.{0}) < Om1 := (natCast_lt_omega0 n).trans omega_lt_Om1
    rw [jhG_low (hn.trans Om1_lt_eW), (rdc_const hn 0).2]
    exact (natCast_lt_omega0 n).trans hωZ
  · exact h

/-- **The gate of a sum** of codes below `ε_{Ω₁+2}`, below every `Z > ω` closed under `+`. -/
theorem jh_add {Z : Ordinal.{0}} (hZ : ∀ u v, u < Z → v < Z → u + v < Z) (hωZ : ω < Z) :
    ∀ x y, x + y < jhB → jhG x < Z → jhG y < Z → jhG (x + y) < Z := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro y hxy hgx hgy
  have hxB : x < jhB := lt_of_le_of_lt le_self_add hxy
  have hyB : y < jhB := lt_of_le_of_lt le_add_self hxy
  rcases lt_or_ge x gfE with hxE | hxE
  · rcases lt_or_ge y gfE with hyE | hyE
    · rw [jhG_low hxE] at hgx
      rw [jhG_low hyE] at hgy
      rw [jhG_low (eW_indec.add_lt hxE hyE)]
      exact gtc_add hZ x y hxE hyE hgx hgy
    · have e : x + y = y := add_of_omega0_opow_le (b := gfE) (by rw [eW_E]; exact hxE) (by rw [eW_E]; exact hyE)
      rw [e]; exact hgy
  obtain ⟨hk, hd0, hdE, hr, hdec, -, hrx⟩ := jh_parts hxE hxB
  set k := log gfE x with hkdef
  set d := x / gfE ^ k with hddef
  set r := x % gfE ^ k with hrdef
  rw [jhG_dec hxE hxB] at hgx
  have hgk : jhQ k < Z := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hgx)
  have hgd : gtc d < Z := gtc_lt_of_giQ hωZ ((le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hgx)) hdE
  have hgr : jhG r < Z := (le_max_right _ _).trans_lt hgx
  rcases lt_or_ge y (gfE ^ k) with hyk | hyk
  · have hry : r + y < gfE ^ k := gw_pow_indec hk _ _ hr hyk
    have e : x + y = gfE ^ k * d + (r + y) := by rw [← hdec, add_assoc]
    rw [e, jhG_cnf hk hd0 hdE hry (e ▸ hxy)]
    have hrB : r + y < jhB := lt_of_le_of_lt (add_le_add hrx.le le_rfl) hxy
    exact max_lt ((le_max_left _ _).trans_lt hgx) (IH r hrx y hrB hgr hgy)
  rcases lt_or_ge y (gfE ^ (k + 1)) with hyk1 | hyk1
  · have hEk : gfE ≤ gfE ^ k := by
      calc gfE = gfE ^ (1 : Ordinal.{0}) := (opow_one _).symm
        _ ≤ gfE ^ k := opow_le_opow_right eW_E.pos (one_le_iff_ne_zero.2 hk)
    have hyE : gfE ≤ y := hEk.trans hyk
    have hky : log gfE y = k := by
      refine le_antisymm ?_ (le_log_of_opow_le gw_one_lt hyk)
      exact Order.lt_add_one_iff.1 ((lt_opow_iff_log_lt gw_one_lt (gw_ne_of_le hyE)).1 hyk1)
    obtain ⟨-, hd0', hdE', hr', hdec', -, -⟩ := jh_parts hyE hyB
    rw [hky] at hd0' hdE' hr' hdec'
    rw [jhG_dec hyE hyB, hky] at hgy
    set d' := y / gfE ^ k with hd'def
    set r' := y % gfE ^ k with hr'def
    have hgd' : gtc d' < Z :=
      gtc_lt_of_giQ hωZ ((le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hgy)) hdE'
    have hrω : r < ω ^ (gfE * k) := by rw [← gw_pow_eq]; exact hr
    have hab : r + gfE ^ k * d' = gfE ^ k * d' := by
      rw [gw_pow_eq]
      exact add_of_omega0_opow_le hrω (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0'))
    have e : x + y = gfE ^ k * (d + d') + r' := by
      rw [← hdec, ← hdec', add_assoc, ← add_assoc r, hab, ← add_assoc, ← mul_add]
    have hdd : d + d' < gfE := eW_indec.add_lt hdE hdE'
    rw [e, jhG_cnf hk (by
      intro h0; exact hd0 (Ordinal.add_eq_zero_iff.1 h0).1) hdd hr' (e ▸ hxy)]
    exact max_lt (max_lt hgk ((giQ_le _).trans_lt (gtc_add hZ d d' hdE hdE' hgd hgd')))
      ((le_max_right _ _).trans_lt hgy)
  · have hxk : x < gfE ^ (k + 1) := by
      rw [hkdef]; exact (lt_opow_iff_log_lt gw_one_lt (gw_ne_of_le hxE)).2 (lt_add_one _)
    have e : x + y = y := add_of_omega0_opow_le (b := gfE * (k + 1)) (by rw [← gw_pow_eq]; exact hxk)
      (by rw [← gw_pow_eq]; exact hyk1)
    rw [e]; exact hgy

/-- `E^a = E·E^{a'}` with `1 + a' = a`. -/
theorem jh_pow_split {a : Ordinal.{0}} (ha : a ≠ 0) : gfE ^ a = gfE * gfE ^ (a - 1) ∧ 1 + (a - 1) = a := by
  have e : 1 + (a - 1) = a := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 ha)
  refine ⟨?_, e⟩
  conv_lhs => rw [← e]
  rw [opow_add, opow_one]

/-- **`y/E` and `y mod E` keep the gate** of a code `E ≤ y < ε_{Ω₁+2}` (below every `Z > ω`). -/
theorem jh_div {Z : Ordinal.{0}} (hωZ : ω < Z) : ∀ y, gfE ≤ y → y < jhB → jhG y < Z →
    jhQ (y / gfE) < Z ∧ gtc (y % gfE) < Z := by
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hyE hyB hg
  obtain ⟨ha, hd0, hdE, hr, hdec, -, hry⟩ := jh_parts hyE hyB
  set a := log gfE y with hadef
  set d := y / gfE ^ a with hddef
  set r := y % gfE ^ a with hrdef
  rw [jhG_dec hyE hyB] at hg
  have hga : jhQ a < Z := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hg)
  have hgd : giQ d < Z := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hg)
  have hgr : jhG r < Z := (le_max_right _ _).trans_lt hg
  obtain ⟨hsp, e1⟩ := jh_pow_split ha
  have hy : y = gfE * (gfE ^ (a - 1) * d) + r := by rw [← hdec, hsp, mul_assoc]
  have hrB : r < jhB := hry.trans hyB
  constructor
  · have hdiv : y / gfE = gfE ^ (a - 1) * d + r / gfE := by
      rw [hy, Ordinal.mul_add_div _ gfE_ne]
    rcases eq_or_ne (a - 1) 0 with ha1 | ha1
    · have hrE : r < gfE := by
        have := hr; rw [hsp, ha1, opow_zero, mul_one] at this; exact this
      rw [hdiv, ha1, opow_zero, one_mul, Ordinal.div_eq_zero_of_lt hrE, add_zero, jhQ_low hdE]
      exact hgd
    · have hrq : r / gfE < gfE ^ (a - 1) := by
        rw [← Ordinal.lt_mul_iff_div_lt gfE_ne, ← hsp]; exact hr
      have hdB : y / gfE < jhB := lt_of_le_of_lt (Ordinal.div_le_of_le_mul (le_mul_right y eW_E.pos)) hyB
      have hEq : gfE ≤ y / gfE := by
        rw [hdiv]
        calc gfE = gfE ^ (1 : Ordinal.{0}) := (opow_one _).symm
          _ ≤ gfE ^ (a - 1) := opow_le_opow_right eW_E.pos (one_le_iff_ne_zero.2 ha1)
          _ ≤ gfE ^ (a - 1) * d := le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0)
          _ ≤ _ := le_self_add
      have hQ : jhQ (y / gfE) = jhG (y / gfE) := by
        unfold jhQ; rw [if_neg (not_lt.2 ((omega_lt_Om1.trans Om1_lt_eW).le.trans hEq))]
      rw [hQ, hdiv, jhG_cnf ha1 hd0 hdE hrq (hdiv ▸ hdB)]
      refine max_lt (max_lt (by rw [← jhQ_one_add, e1]; exact hga) hgd) ?_
      rcases lt_or_ge r gfE with hrE | hrE
      · rw [Ordinal.div_eq_zero_of_lt hrE, jhG_zero]; exact (omega0_pos).trans hωZ
      · exact jhG_of_Q hωZ (IH r hry hrE hrB hgr).1
  · have hmod : y % gfE = r % gfE := by rw [hy, Ordinal.mul_add_mod_self]
    rw [hmod]
    rcases lt_or_ge r gfE with hrE | hrE
    · rw [Ordinal.mod_eq_of_lt hrE, ← jhG_low hrE]; exact hgr
    · exact (IH r hry hrE hrB hgr).2

/-- **The gate of a code below `ε_{Ω₁+2}`**: a code over `Z` (atoms above `ε_{Ω₁+2}`) has its gate below `Z`. -/
theorem jh_code_gate {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ1 : Z ≤ Om1) (hZ0 : 0 < Z)
    (hZa : ∀ u v, u < Z → v < Z → u + v < Z) (hZp : ∀ u v, u < Z → v < Z → veblen u v < Z)
    (hAt : ∀ s ∈ At, jhB < s) {c : Ordinal.{0}} (hc : GxCl Z At c) : c < jhB → jhG c < Z := by
  have hAt' : ∀ s ∈ At, gfE < s := fun s hs => gfE_lt_jhB.trans (hAt s hs)
  have hZw : ∀ u, u < Z → ω ^ u < Z := fun u hu => by
    have := hZp 0 u hZ0 hu; rwa [veblen_zero_apply] at this
  have h1Z : (1 : Ordinal.{0}) < Z := by
    have := hZw 0 hZ0; rwa [opow_zero] at this
  have hωZ : ω < Z := by
    have := hZw 1 h1Z; rwa [opow_one] at this
  have hsmall : ∀ x, GxCl Z At x → x < gfE → jhG x < Z := fun x hx h => by
    rw [jhG_low h]; exact gfCode_gate hZ1 hZ0 hZa hZp hAt' hx h
  induction hc with
  | @small x h => exact fun _ => hsmall _ (GxCl.small h) ((h.trans_le hZ1).trans Om1_lt_eW)
  | om => exact fun _ => hsmall _ GxCl.om (by rw [← Br.Om1_eq]; exact Om1_lt_eW)
  | @atom s hs => exact fun h => absurd (hAt s hs) (not_lt.2 h.le)
  | @add x y hx hy ihx ihy =>
    intro h
    exact jh_add hZa hωZ x y h (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y hx hy ihx ihy =>
    intro h
    rcases lt_or_ge (veblen x y) gfE with hlt | hge
    · exact hsmall _ (GxCl.phi hx hy) hlt
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [veblen_zero_apply] at h hge ⊢
      have hyB : y < jhB := lt_of_le_of_lt (right_le_opow y one_lt_omega0) h
      have hEy : gfE ≤ y := by
        rw [← show ω ^ gfE = gfE from eW_E] at hge
        exact (opow_le_opow_iff_right one_lt_omega0).1 hge
      set m := y / gfE with hm
      set y' := y % gfE with hy'
      have hm0 : m ≠ 0 := ((Ordinal.div_pos gfE_ne).2 hEy).ne'
      have hy'E : y' < gfE := gh_mod_lt y
      have ew : ω ^ y = gfE ^ m * ω ^ y' + 0 := by
        rw [add_zero, gw_pow_eq]
        conv_lhs => rw [← gi_dec y]
        rw [opow_add]
      have hw0 : ω ^ y' ≠ 0 := opow_ne_zero _ omega0_ne_zero
      have hwE : ω ^ y' < gfE := by
        rw [← show ω ^ gfE = gfE from eW_E]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hy'E
      obtain ⟨hgm, hgy'⟩ := jh_div hωZ y hEy hyB (ihy hyB)
      rw [ew, jhG_cnf hm0 hw0 hwE (opow_pos _ eW_E.pos) (ew ▸ h), jhG_zero]
      exact max_lt (max_lt hgm ((giQ_le _).trans_lt (gtc_opow hZw hy'E hgy'))) hZ0
    · have hE : ω ^ veblen x y = veblen x y := by
        have := veblen_veblen_of_lt (pos_iff_ne_zero.2 hx0) y
        rwa [veblen_zero_apply] at this
      have heq : veblen x y = gfE := by
        rcases hge.lt_or_eq with hlt | heq
        · exact absurd ((eN_le hlt hE).trans_lt h) (lt_irrefl _)
        · exact heq.symm
      rw [heq, jhG_E]; exact hZ0

/-! ## `E·k` -/

theorem jhR_pos {x : Ordinal.{0}} (hx : InE x) {c : Ordinal.{0}} (hc0 : c ≠ 0) (hcB : c < jhB) : 0 < jhR c x := by
  rcases lt_or_ge c gfE with hcE | hcE
  · rw [jhR_low hcE]; exact rdc_pos hx hc0 hcE
  obtain ⟨-, hd0, hdE, -, -, -, -⟩ := jh_parts hcE hcB
  rw [jhR_dec hcE hcB]
  exact lt_of_lt_of_le (mul_pos (opow_pos _ (eN_E x).pos) (rdc_pos hx hd0 hdE)) le_self_add

/-- **An infinite code has an infinite reading.** -/
theorem jh_omega_le_jhR {x a : Ordinal.{0}} (hx : InE x) (ha : ω ≤ a) (haB : a < jhB) : ω ≤ jhR a x := by
  rcases lt_or_ge a gfE with haE | haE
  · rw [jhR_low haE]
    rcases lt_or_ge a Om1 with ha1 | ha1
    · rw [(rdc_const ha1 x).1]; exact ha
    have ha0 : a ≠ 0 := (lt_of_lt_of_le omega0_pos ha).ne'
    obtain ⟨hq, -, -, -, -, -⟩ := parts ha0
    have hl0 : log Om1 a ≠ 0 :=
      (lt_of_lt_of_le zero_lt_one (le_log_of_opow_le gf_one_lt_Om1 (by rw [opow_one]; exact ha1))).ne'
    have hlE : log Om1 a < gfE := (log_le_self Om1 a).trans_lt haE
    rw [rdc_dec ha0 haE]
    calc ω ≤ x := (omega0_lt_inE hx).le
      _ = x ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ x ^ rdc (log Om1 a) x := opow_le_opow_right hx.pos (one_le_iff_pos.2 (rdc_pos hx hl0 hlE))
      _ ≤ x ^ rdc (log Om1 a) x * (a / Om1 ^ log Om1 a) := le_mul_of_one_le_right' (one_le_iff_pos.2 hq)
      _ ≤ _ := le_self_add
  obtain ⟨hk, hd0, hdE, -, -, hlc, -⟩ := jh_parts haE haB
  rw [jhR_dec haE haB]
  calc ω ≤ eN x := omega0_le_eN x
    _ = eN x ^ (1 : Ordinal.{0}) := (opow_one _).symm
    _ ≤ eN x ^ jhR (log gfE a) x :=
        opow_le_opow_right (eN_E x).pos (one_le_iff_pos.2 (jhR_pos hx hk (hlc.trans haB)))
    _ ≤ eN x ^ jhR (log gfE a) x * rdc (a / gfE ^ log gfE a) x :=
        le_mul_of_one_le_right' (one_le_iff_pos.2 (rdc_pos hx hd0 hdE))
    _ ≤ _ := le_self_add

theorem jhR_one_add {x a : Ordinal.{0}} (hx : InE x) (haB : a < jhB) : jhR (1 + a) x = 1 + jhR a x := by
  rcases lt_or_ge a ω with haω | haω
  · obtain ⟨n, hn⟩ := lt_omega0.1 haω
    have : (1 : Ordinal.{0}) + n = ((1 + n : ℕ) : Ordinal.{0}) := by push_cast; rfl
    rw [hn, this, jhR_nat, jhR_nat]; push_cast; rfl
  · rw [jh_one_add haω, jh_one_add (jh_omega_le_jhR hx haω haB)]

/-- **`E·k` as a code**: for a code `1 ≤ k < ε_{Ω₁+2}`, `E·k < ε_{Ω₁+2}`, its gate is at most that of `k`, and its
reading is `ε_{x+1}·k(x)` at every `ε`-number `x`. -/
theorem jh_mulE : ∀ k, k ≠ 0 → k < jhB → gfE * k < jhB ∧ jhG (gfE * k) ≤ jhG k ∧
    ∀ x, InE x → jhR (gfE * k) x = eN x * jhR k x := by
  intro k
  induction k using WellFoundedLT.induction with
  | ind k IH =>
  intro hk0 hkB
  have hB : gfE * k < jhB := jhB_E.mul_lt gfE_lt_jhB hkB
  refine ⟨hB, ?_⟩
  rcases lt_or_ge k gfE with hkE | hkE
  · have e : gfE * k = gfE ^ (1 : Ordinal.{0}) * k + 0 := by rw [opow_one, add_zero]
    have hc := jhG_cnf one_ne_zero hk0 hkE (opow_pos _ eW_E.pos) (e ▸ hB)
    refine ⟨?_, fun x _ => ?_⟩
    · rw [e, hc, jhG_low hkE, jhG_zero, max_eq_left zero_le]
      have : jhQ 1 = 0 := by exact_mod_cast jhQ_nat 1
      rw [this, max_eq_right zero_le]; exact giQ_le k
    · rw [e, jhR_cnf one_ne_zero hk0 hkE (opow_pos _ eW_E.pos) (e ▸ hB), jhR_one, opow_one, jhR_zero, add_zero,
        jhR_low hkE]
  obtain ⟨ha, hd0, hdE, hr, hdec, hak, hrk⟩ := jh_parts hkE hkB
  set a := log gfE k with hadef
  set d := k / gfE ^ a with hddef
  set r := k % gfE ^ a with hrdef
  have hrB : r < jhB := hrk.trans hkB
  have h1a : 1 + a ≠ 0 := (lt_of_lt_of_le zero_lt_one le_self_add).ne'
  have hEr : gfE * r < gfE ^ (1 + a) := by
    rw [opow_add, opow_one]; exact (mul_lt_mul_iff_right₀ eW_E.pos).2 hr
  have e : gfE * k = gfE ^ (1 + a) * d + gfE * r := by
    rw [← hdec, mul_add, ← mul_assoc, opow_add, opow_one]
  have hc := jhG_cnf h1a hd0 hdE hEr (e ▸ hB)
  have hgEr : jhG (gfE * r) ≤ jhG r := by
    rcases eq_or_ne r 0 with h0 | h0
    · rw [h0, mul_zero]
    · exact (IH r hrk h0 hrB).2.1
  refine ⟨?_, fun x hx => ?_⟩
  · rw [e, hc, jhQ_one_add, jhG_dec hkE hkB]
    exact max_le_max le_rfl hgEr
  · rw [e, jhR_cnf h1a hd0 hdE hEr (e ▸ hB), jhR_dec hkE hkB]
    have hRr : jhR (gfE * r) x = eN x * jhR r x := by
      rcases eq_or_ne r 0 with h0 | h0
      · rw [h0, mul_zero, jhR_zero, mul_zero]
      · exact (IH r hrk h0 hrB).2.2 x hx
    rw [hRr, jhR_one_add hx (hak.trans hkB), opow_add, opow_one, mul_assoc, ← mul_add]

/-- `E·k < E^k` for every code `2 ≤ k < ε_{Ω₁+2}` (`E·k` is not an `ε`-number). -/
theorem jh_mulE_lt_pow {k : Ordinal.{0}} (hk : 1 < k) (hkB : k < jhB) : gfE * k < gfE ^ k := by
  rw [gw_pow_eq]
  rcases (right_le_opow (gfE * k) one_lt_omega0).lt_or_eq with h | h
  · exact h
  exfalso
  have hE : InE (gfE * k) := h.symm
  have hlt : gfE < gfE * k := lt_mul_of_one_lt_right eW_E.pos hk
  exact absurd ((eN_le hlt hE).trans_lt (jhB_E.mul_lt gfE_lt_jhB hkB)) (lt_irrefl _)

/-- **Every code `c < ε_{Ω₁+2}` lies in every hull containing its gate.** -/
theorem jh_mem {S : InaccSeq.{0}} {a b : Ordinal.{0}} : ∀ c, c < jhB → jhG c < b → c ∈ S.CSet a b := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  rcases lt_or_ge c gfE with hcE | hcE
  · rw [jhG_low hcE] at hg; exact gfW_mem' hcE hg
  obtain ⟨hk, hd0, hdE, -, hdec, hkc, hrc⟩ := jh_parts hcE hc
  rw [jhG_dec hcE hc] at hg
  have hr := IH _ hrc (hrc.trans hc) ((le_max_right _ _).trans_lt hg)
  rw [← hdec]
  refine CSet.add_mem ?_ hr
  set k := log gfE c with hkdef
  have hgk : jhQ k < b := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hg)
  have heE : gfE * k ∈ S.CSet a b := by
    by_cases hω : k < ω
    · obtain ⟨n, hn⟩ := lt_omega0.1 hω
      rw [hn]; exact lg_cset_mul_nat gfW_inC n
    · have hQ : jhQ k = jhG k := by unfold jhQ; rw [if_neg hω]
      have hk1 : 1 < k := lt_of_lt_of_le one_lt_omega0 (not_lt.1 hω)
      have hkB : k < jhB := hkc.trans hc
      obtain ⟨hB, hg', -⟩ := jh_mulE k hk hkB
      have hlt : gfE * k < c := (jh_mulE_lt_pow hk1 hkB).trans_le (by
        rw [← hdec]; exact (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0)).trans le_self_add)
      exact IH _ hlt hB (hg'.trans_lt (hQ ▸ hgk))
  have hpow : gfE ^ k = ω ^ (gfE * k) := gw_pow_eq _
  have hgd := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hg)
  set d := c / gfE ^ k with hd
  rw [hpow]
  by_cases hω : d < ω
  · obtain ⟨m, hm⟩ := lt_omega0.1 hω
    rw [hm]
    have := CSet.phi_mem (CSet.zero_mem (S := S) a b) heE
    rw [veblen_zero_apply] at this
    exact lg_cset_mul_nat this m
  · have h1 : giQ d = gtc d := by unfold giQ; rw [if_neg hω]
    exact gw_mulOm_mem heE _ hdE (by rw [← h1]; exact hgd)

/-- `ε_{Ω₁+2} = φ(1, Ω₁+2)`. -/
theorem jhB_eq : jhB = veblen 1 (Om1 + 1 + 1) := by
  have h := evA_add_one gfE 0
  rw [evA_zero eW_E, zero_add] at h
  rw [jhB, ← h, evA, eW_eq, evIx_epsilon]

theorem jhB_mem {S : InaccSeq.{0}} {a b : Ordinal.{0}} : jhB ∈ S.CSet a b := by
  have hO : Om1 ∈ S.CSet a b := by rw [Br.Om1_eq]; exact CSet.Om_mem (CSet.one_mem _ _)
  rw [jhB_eq]
  exact CSet.phi_mem (CSet.one_mem _ _) (CSet.succ_mem (CSet.succ_mem hO))

theorem jh_succ_cnf {b : Ordinal.{0}} (hEb : gfE ≤ b) (hbB : b < jhB) :
    b + 1 = gfE ^ log gfE b * (b / gfE ^ log gfE b) + (b % gfE ^ log gfE b + 1) ∧
      b % gfE ^ log gfE b + 1 < gfE ^ log gfE b := gw_succ_cnf hEb

theorem jhG_succ {Z : Ordinal.{0}} (hZ : IsSuccLimit Z) : ∀ b, b + 1 < jhB → jhG b < Z → jhG (b + 1) < Z := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb1 hg
  have hbB : b < jhB := (lt_add_one b).trans hb1
  rcases lt_or_ge b gfE with hbE | hbE
  · rw [jhG_low hbE] at hg
    rw [jhG_low (succ_lt_eW hbE)]
    exact (rdc_succ b hbE 0).2.2.trans_lt (hZ.add_one_lt hg)
  obtain ⟨hk, hd0, hdE, hr, -, -, hrb⟩ := jh_parts hbE hbB
  obtain ⟨e, hr1⟩ := jh_succ_cnf hbE hbB
  rw [jhG_dec hbE hbB] at hg
  have hr1B : b % gfE ^ log gfE b + 1 < jhB := lt_of_le_of_lt (by rw [e]; exact le_add_self) hb1
  rw [e, jhG_cnf hk hd0 hdE hr1 (e ▸ hb1)]
  exact max_lt ((le_max_left _ _).trans_lt hg) (IH _ hrb hr1B ((le_max_right _ _).trans_lt hg))

theorem jhG_le_succ : ∀ b, b + 1 < jhB → jhG b ≤ jhG (b + 1) := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb1
  have hbB : b < jhB := (lt_add_one b).trans hb1
  rcases lt_or_ge b gfE with hbE | hbE
  · rw [jhG_low hbE, jhG_low (succ_lt_eW hbE)]; exact (rdc_succ b hbE 0).2.1
  obtain ⟨hk, hd0, hdE, hr, -, -, hrb⟩ := jh_parts hbE hbB
  obtain ⟨e, hr1⟩ := jh_succ_cnf hbE hbB
  have hr1B : b % gfE ^ log gfE b + 1 < jhB := lt_of_le_of_lt (by rw [e]; exact le_add_self) hb1
  rw [jhG_dec hbE hbB, e, jhG_cnf hk hd0 hdE hr1 (e ▸ hb1)]
  exact max_le_max le_rfl (IH _ hrb hr1B)

end Googology.Trans.PoR.InaccPsi.R2.Gj
