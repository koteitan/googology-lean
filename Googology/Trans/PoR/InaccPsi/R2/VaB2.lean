import Googology.Trans.PoR.InaccPsi.R2.VaR
import Googology.Trans.PoR.InaccPsi.R2.ZmNx

/-!
# VaB2: TOOLS PAST `Γ_{B_Γ+1}` — THE NEXT FIXED POINT `B₂` OF `Γ`, NO CLOSED POINT BETWEEN `D(x)` AND `D₂(x)`

`B₂ = vaB2` is the least fixed point of `Γ` above `B_Γ`; its reading is `D₂(x) = ϑˣ(Ω₁·(Ω₁+1) + 1)` (`Yw.ywV 1 1`),
the closed point after `D(x)`.

* `vaB2`, `vaB2_fix`, `va_BG_lt_B2`, `va_B2_min` (**no fixed point of `Γ` in `(B_Γ, B₂)`**);
* `va_D2_facts`, `va_nonclosed` (**every `p ∈ Tˣ ∩ (D(x), D₂(x))` has `σ < p` with `p < gq σ x`**: a closed point is a
  point of some level `j ≥ 1` (`Yw.ywC_rep`), and below `D₂(x)` that is `D(x)`, `Yw.ywV_lt_inv`);
* `va_off_gate` (**the offset `j − (B_Γ+1)` of an atom index `B_Γ < j` keeps its gate up to `ω`**);
* `va_eN_gq` (**`ε_{gq(I)+1} = ϑˣ(Ω₁ + gq(I))`**), `va_lt_D2` (**every code below `B₂` reads below `D₂(x)`**).

No new axiom.  New definition: `vaB2`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Va

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Zm
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Xk Googology.Trans.PoR.InaccPsi.R2.Gm
  Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Rh

/-! ## The bound `Γ_{B_Γ+1}` and the atoms below it -/

/-- **The bound** `Γ_{B_Γ+1}`, the least strongly critical ordinal above `B_Γ`. -/
noncomputable def vaU : Ordinal.{0} := gcG (tfBG + 1)

theorem va_BG_lt_U : tfBG < vaU := by
  unfold vaU; conv_lhs => rw [← zb_gcG_BG]
  exact gcG_lt (lt_add_one _)

theorem va_G_le_BG : gcG 0 ≤ tfBG := by rw [← zb_gcG_BG]; exact gcG_le zero_le

/-- **Below `Γ_{B_Γ+1}` the only atom `≥ B_Γ` is `B_Γ`.** -/
theorem va_atom_cases {e : Ordinal.{0}} (hBe : tfBG ≤ e) (heU : e < vaU) : e = tfBG ∨ ¬ YhAt e := by
  by_cases hA : YhAt e
  · left
    obtain ⟨j, rfl⟩ := yhAt_iff.1 hA
    have h1 : tfBG ≤ j := by
      rw [← zb_gcG_BG] at hBe; exact gcG_strictMono.le_iff_le.1 hBe
    have h2 : j < tfBG + 1 := gcG_strictMono.lt_iff_lt.1 heU
    rw [le_antisymm (Order.lt_add_one_iff.1 h2) h1, zb_gcG_BG]
  · exact Or.inr hA

theorem va_QE_BG : yrQE tfBG = 0 := by
  have hA : YhAt tfBG := by rw [← zb_gcG_BG]; exact yhAt_gcG _
  have hJ : yhJ tfBG = tfBG := by have h := yhJ_gcG tfBG; rwa [zb_gcG_BG] at h
  exact yrQE_atom_fix hA (by rw [hJ]; exact lt_irrefl _)

/-! ## The next fixed point of `Γ` -/

/-- **`B₂`**: the least fixed point of `Γ` above `B_Γ`. -/
noncomputable def vaB2 : Ordinal.{0} := nfp gamma (tfBG + 1)

theorem vaB2_fix : gamma vaB2 = vaB2 := nfp_fp isNormal_gamma _

theorem va_BG_lt_B2 : tfBG < vaB2 := (lt_add_one _).trans_le (le_nfp _ _)

/-- **No fixed point of `Γ` in `(B_Γ, B₂)`.** -/
theorem va_B2_min {y : Ordinal.{0}} (h1 : tfBG < y) (hfix : gamma y = y) : vaB2 ≤ y :=
  nfp_le_fp isNormal_gamma.strictMono.monotone (Order.add_one_le_of_lt h1) hfix.le

theorem va_U_le_B2 : vaU ≤ vaB2 := by
  have hSC : SC vaB2 := by have := Lq.lq_gamma_SC vaB2; rwa [vaB2_fix] at this
  obtain ⟨j, hj⟩ := yhAt_iff.1 ⟨hSC, tfBG_gt.trans va_BG_lt_B2⟩
  have hjB : tfBG < j := by
    have h := va_BG_lt_B2; rw [hj, ← zb_gcG_BG] at h; exact gcG_strictMono.lt_iff_lt.1 h
  rw [hj]; exact gcG_le (Order.add_one_le_of_lt hjB)

/-- **`B₂ < X`.** -/
theorem va_B2_lt_X : vaB2 < tlX := by
  have hXE : InE tlX := Low.opow_eq_self_of_SC tlX_SC
  have h1X : (1 : Ordinal.{0}) < tlX := lu_one_lt_E hXE
  have hfX : rhF 1 tlX = tlX := by
    have h := Rh.rhF_fix_lower h1X 0; rwa [tlX_rhF] at h
  have hO2 : Om1 + 1 + 1 < tlX :=
    (ev_isSuccLimit_of_inE hXE).add_one_lt ((ev_isSuccLimit_of_inE hXE).add_one_lt tlX_gt)
  have hF2 : rhF 1 (Om1 + 1 + 1) < tlX := by
    rw [← hfX]; exact (Rh.rhF_normal 1).strictMono hO2
  have hfix : gamma (rhF 1 (Om1 + 1 + 1)) = rhF 1 (Om1 + 1 + 1) := by
    have h := Rh.rhF_fix_lower zero_lt_one (Om1 + 1 + 1); rwa [Rh.rhF_zero] at h
  have hBF : tfBG < rhF 1 (Om1 + 1 + 1) := by
    rw [tl_BG_eq]; exact (Rh.rhF_normal 1).strictMono (lt_add_one _)
  exact (va_B2_min hBF hfix).trans_lt hF2

/-- **Below `B₂` the atoms `≥ B_Γ` are `B_Γ` and the atoms `Γ(j)`, `B_Γ < j < Γ(j)`.** -/
theorem va_atom_cases2 {e : Ordinal.{0}} (hBe : tfBG ≤ e) (heB : e < vaB2) :
    e = tfBG ∨ (YhAt e ∧ tfBG < yhJ e ∧ yhJ e < e) ∨ ¬ YhAt e := by
  by_cases hA : YhAt e
  · obtain ⟨j, rfl⟩ := yhAt_iff.1 hA
    have h1 : tfBG ≤ j := by
      rw [← zb_gcG_BG] at hBe; exact gcG_strictMono.le_iff_le.1 hBe
    rcases h1.lt_or_eq with h1 | h1
    · refine Or.inr (Or.inl ⟨hA, by rw [yhJ_gcG]; exact h1, ?_⟩)
      rw [yhJ_gcG]
      refine lt_of_le_of_ne (gcG_strictMono.le_apply) fun he => ?_
      have hjE : Om1 + 1 + j = j := by
        obtain ⟨d, hd⟩ := exists_add_of_le h1.le
        have hBE : InE tfBG := Low.opow_eq_self_of_SC tfBG_SC
        rw [hd, ← add_assoc, gl_absorb hBE tfBG_gt]
      have hfix : gamma j = j := by rw [← hjE, ← tf_gcG, hjE]; exact he.symm
      exact absurd heB (not_lt.2 ((va_B2_min h1 hfix).trans (le_of_eq he)))
    · left; rw [← h1, zb_gcG_BG]
  · exact Or.inr (Or.inr hA)

/-- **Past `B_Γ` below `B₂` the largest fixed point of `Γ` below `j` is `B_Γ`.** -/
theorem va_fpG_BG {j : Ordinal.{0}} (hj : tfBG < j) (hjB : j < vaB2) : VaFixG j ∧ vaFpG j = tfBG := by
  refine ⟨⟨tfBG, tfBG_fix, tfBG_gt, hj⟩, ?_⟩
  have hset : {F | gamma F = F ∧ Om1 < F ∧ F < j} = {tfBG} := by
    ext F
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hF, hOF, hFj⟩
      refine le_antisymm ?_ (tfBG_le hF hOF)
      by_contra hc
      exact absurd (hFj.trans hjB) (not_lt.2 (va_B2_min (not_le.1 hc) hF))
    · rintro rfl; exact ⟨tfBG_fix, tfBG_gt, hj⟩
  unfold vaFpG; rw [hset, csSup_singleton]

theorem vI_high {j : Ordinal.{0}} (hj : tfBG < j) (hjB : j < vaB2) (x : Ordinal.{0}) :
    vI j x = ywV 1 0 x + vR (j - (tfBG + 1)) x := by
  obtain ⟨hF, hp⟩ := va_fpG_BG hj hjB
  unfold vI; rw [if_pos hF, hp, vR_BG]

/-- **Below `B₂` the only fixed-point atom is `B_Γ`.** -/
theorem va_fix_atom_BG {e : Ordinal.{0}} (hA : YhAt e) (hi : ¬ yhJ e < e) (heB : e < vaB2) : e = tfBG := by
  obtain ⟨j, rfl⟩ := yhAt_iff.1 hA
  rw [yhJ_gcG] at hi
  have hjj : j = gcG j := le_antisymm (gcG_strictMono.le_apply) (not_lt.1 hi)
  have hE : InE (gcG j) := Low.opow_eq_self_of_SC (gcG_SC j)
  have hO : Om1 < gcG j := hA.2
  have hjE : InE j := by rw [hjj]; exact hE
  have hjO : Om1 < j := by rw [hjj]; exact hO
  have h1 : Om1 + 1 + j = j := gl_absorb hjE hjO
  have hfix : gamma (gcG j) = gcG j := by
    rw [← hjj]
    conv_lhs => rw [← h1]
    rw [← tf_gcG]; exact hjj.symm
  rcases (tfBG_le hfix hO).lt_or_eq with h | h
  · exact absurd heB (not_lt.2 (va_B2_min h hfix))
  · exact h.symm

/-! ## The closed point after `D(x)` -/

section D2

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem va_D2_facts : ywV 1 0 x < ywV 1 1 x ∧ ywV 1 1 x ∈ Tset x ∧ ywV 1 1 x < Om1 ∧ InE (ywV 1 1 x) ∧
    ywV 1 1 x < ywX x := by
  obtain ⟨h1T, h1Ω⟩ := yw_one hx hx1
  obtain ⟨hvT, -, hv1, hvE, -, -, -⟩ := ywV_facts hx hx1 h1T h1Ω h1T h1Ω
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have h1X : (1 : Ordinal.{0}) < ywX x := (lu_one_lt_E hx).trans (ywX_facts hx hx1).2.1
  exact ⟨ywV_lt_same hx hx1 h0T h1T h1Ω h1T h1Ω zero_lt_one, hvT, hv1, hvE,
    ywV_lt_X hx hx1 h1T h1Ω h1T h1Ω h1X h1X⟩

/-- **No closed point between `D(x)` and `D₂(x)`**: every `p ∈ Tˣ ∩ (D(x), D₂(x))` is below `gq σ x` for some
`σ < p`. -/
theorem va_nonclosed {p : Ordinal.{0}} (hpT : p ∈ Tset x) (hDp : ywV 1 0 x < p) (hpD : p < ywV 1 1 x) :
    ∃ σ, σ ∈ Tset x ∧ σ < Om1 ∧ σ < p ∧ p < gq σ x := by
  obtain ⟨-, -, hD21, -, hD2X⟩ := va_D2_facts hx hx1
  have hp1 : p < Om1 := hpD.trans hD21
  have hxp : x < p := (zmD_facts hx hx1).2.1.trans hDp
  by_contra hcon
  push Not at hcon
  -- `p` is closed
  have hcl : YwClosed x p := by
    intro σ hσT hσp
    have hσ1 : σ < Om1 := hσp.trans hp1
    refine lt_of_le_of_ne (hcon σ hσT hσ1 hσp) fun he => ?_
    obtain ⟨hs1T, hs11⟩ := gl_T_succ hx hx1 hσT hσ1
    obtain ⟨-, -, -, hqE, -⟩ := geq_facts hx hx1 hσT hσ1
    have hσ1p : σ + 1 < p := by
      rw [← he]; exact (ev_isSuccLimit_of_inE hqE).add_one_lt (gmq_gt hx hx1 hσT hσ1)
    have := hcon (σ + 1) hs1T hs11 hσ1p
    rw [← he] at this
    exact absurd (gmq_lt hx hx1 hs1T hs11 (lt_add_one σ)) (not_lt.2 this)
  obtain ⟨j, σ, hjT, hjΩ, hσT, hσΩ, hj1, hv⟩ :=
    ywC_rep hx hx1 le_rfl hpT hxp (hpD.trans hD2X) ((ywC_one_iff hx hx1).2 hcl)
  obtain ⟨h1T, h1Ω⟩ := yw_one hx hx1
  have h1p : (1 : Ordinal.{0}) < p := (lu_one_lt_E hx).trans hxp
  rw [← hv] at h1p hpD hDp
  rcases ywV_lt_inv hx hx1 hjT hjΩ hσT hσΩ h1T h1Ω h1T h1Ω h1p h1p hpD with h | ⟨rfl, hσ⟩
  · exact absurd hj1 (not_le.2 h)
  · rw [Order.lt_one_iff] at hσ
    rw [hσ] at hDp
    exact lt_irrefl _ hDp

end D2

/-! ## The gate of the offset of an atom index -/

theorem va_nat_gate (n : ℕ) : yrG n = n := by rw [yrG_low (yh_nat_lt_G n), glG_nat]

/-- **The offset `j − (B_Γ+1)` keeps the gate of `j` up to `ω`.** -/
theorem va_off_gate {j : Ordinal.{0}} (hj : tfBG < j) : yrG (j - (tfBG + 1)) ≤ max ω (yrG j) := by
  have hBE : InE tfBG := Low.opow_eq_self_of_SC tfBG_SC
  have hB0 : tfBG ≠ 0 := hBE.pos.ne'
  rcases le_or_gt (tfBG * ω) j with hbig | hsmall
  · -- the prefix is absorbed
    have e : tfBG + 1 + j = j := by
      rw [add_assoc]
      have h1 : (1 : Ordinal.{0}) + j = j := one_add_of_omega0_le
        ((omega0_le_of_isSuccLimit (ev_isSuccLimit_of_inE hBE)).trans ((Ordinal.le_mul_left _ omega0_pos).trans hbig))
      rw [h1]; exact add_eq_right_iff_mul_omega0_le.2 hbig
    rw [Ordinal.sub_eq_of_add_eq e]; exact le_max_right _ _
  -- `j = B_Γ·m + r`, `1 ≤ m < ω`, `r < B_Γ`
  set m := j / tfBG with hm
  set r := j % tfBG with hr
  have hdec : tfBG * m + r = j := Ordinal.div_add_mod j tfBG
  have hrB : r < tfBG := Ordinal.mod_lt j hB0
  have hmω : m < ω := (Ordinal.lt_mul_iff_div_lt hB0).1 hsmall
  obtain ⟨n, hn⟩ := lt_omega0.1 hmω
  have hm1 : 1 ≤ m := by
    rw [hm, ← Ordinal.mul_le_iff_le_div hB0, mul_one]; exact hj.le
  have hGB : gcG 0 ≤ tfBG := va_G_le_BG
  have hgate : ∀ k : ℕ, 1 ≤ k → yrG (tfBG * k + r) = yrG r := by
    intro k hk
    have hk0 : (k : Ordinal.{0}) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hk)
    have hkB : (k : Ordinal.{0}) < tfBG := (natCast_lt_omega0 k).trans (omega0_lt_inE hBE)
    have hv : tfBG ^ (1 : Ordinal.{0}) * k + r < eN tfBG := by
      rw [opow_one]
      exact (inE_indec (eN_E tfBG)).add_lt (mul_lt_inE (eN_E tfBG) (lt_eN _) (hkB.trans (lt_eN _)))
        (hrB.trans (lt_eN _))
    have h := yrG_cnf hBE hGB one_ne_zero hk0 hkB (by rw [opow_one]; exact hrB) hv
    rw [opow_one] at h
    rw [h, va_QE_BG, yrQ_one, yrQ_nat, max_eq_right zero_le, max_eq_right zero_le, max_eq_right zero_le]
  have hjr : yrG j = yrG r := by
    rw [← hdec, hn]; exact hgate n (by exact_mod_cast hn ▸ hm1)
  rw [hjr]
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · -- `m = 1`: `j = B_Γ + r`, the offset is `r` up to a finite part
    have hn1 : n = 1 := by
      have : 1 ≤ n := by exact_mod_cast hn ▸ hm1
      omega
    rw [hn1, Nat.cast_one] at hn
    have e : j - (tfBG + 1) = r - 1 := by
      rw [← hdec, hn, mul_one, Ordinal.add_sub_add_cancel]
    rw [e]
    rcases lt_or_ge r ω with hrω | hrω
    · obtain ⟨k, hk⟩ := lt_omega0.1 hrω
      rw [hk]
      have : ((k : Ordinal.{0}) - 1) < ω := (Ordinal.sub_le_self _ _).trans_lt (natCast_lt_omega0 k)
      obtain ⟨k', hk'⟩ := lt_omega0.1 this
      rw [hk', va_nat_gate]; exact (natCast_lt_omega0 k').le.trans (le_max_left _ _)
    · have e2 : r - 1 = r := Ordinal.sub_eq_of_add_eq (one_add_of_omega0_le hrω)
      rw [e2]; exact le_max_right _ _
  · -- `m ≥ 2`: the offset is `B_Γ·(m−1) + r`
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have e : j - (tfBG + 1) = tfBG * ((k + 1 : ℕ) : Ordinal.{0}) + r := by
      refine Ordinal.sub_eq_of_add_eq ?_
      have hω' : ω ≤ tfBG * ((k + 1 : ℕ) : Ordinal.{0}) :=
        (omega0_le_of_isSuccLimit (ev_isSuccLimit_of_inE hBE)).trans
          (Ordinal.le_mul_left _ (by exact_mod_cast Nat.succ_pos k))
      have e2 : (1 : Ordinal.{0}) + ((k + 1 : ℕ) : Ordinal.{0}) = ((k + 2 : ℕ) : Ordinal.{0}) := by
        rw [← Nat.cast_one, ← Nat.cast_add]; congr 1; omega
      calc tfBG + 1 + (tfBG * ((k + 1 : ℕ) : Ordinal.{0}) + r)
          = tfBG + (1 + tfBG * ((k + 1 : ℕ) : Ordinal.{0})) + r := by
            rw [← add_assoc (tfBG + 1), add_assoc tfBG 1]
        _ = tfBG + tfBG * ((k + 1 : ℕ) : Ordinal.{0}) + r := by rw [one_add_of_omega0_le hω']
        _ = tfBG * (1 + ((k + 1 : ℕ) : Ordinal.{0})) + r := by rw [mul_one_add]
        _ = j := by rw [e2, ← hn]; exact hdec
    rw [e, hgate (k + 1) (by omega)]; exact le_max_right _ _

/-! ## `ε_{gq(I)+1} = ϑˣ(Ω₁ + gq(I))` -/

theorem va_eN_gq {x I : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hIT : I ∈ Tset x) (hI1 : I < Om1) :
    eN (gq I x) = glA 1 (gq I x) x := by
  obtain ⟨hqT, hxq, hq1, hqE, -⟩ := geq_facts hx hx1 hIT hI1
  obtain ⟨h1T, h11⟩ := gl_one_T hx hx1
  obtain ⟨-, -, -, haE, -, hta⟩ := glA_facts hx hx1 le_rfl h1T h11 hqT hq1
  refine le_antisymm (eN_le hta haE) ?_
  have hP1 : LuP 1 (eN (gq I x)) := by
    have h := vzP_one.2 (eN_E (gq I x)); unfold VzP at h; rwa [Nat.cast_one] at h
  have h1q : (1 : Ordinal.{0}) < gq I x := lu_one_lt_E hqE
  refine glA_min hx hx1 le_rfl h1T h11 hqT hq1 hP1 (hxq.trans (lt_eN _)) (lt_eN _) (h1q.trans (lt_eN _))
    (fun σ hσ => ?_)
  exact (xkA_lt hx hx1 hIT hI1 h1q hσ).trans (lt_eN _)

/-! ## Every code below `B₂` reads below `D₂(x)` -/

/-- **Every code below `B₂` (gate below `x`) reads below `D₂(x)`.** -/
theorem va_lt_D2 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    ∀ c, c < vaB2 → yrG c < x → vR c x < ywV 1 1 x := by
  obtain ⟨hDD2, hD2T, hD21, hD2E, -⟩ := va_D2_facts hx hx1
  obtain ⟨h1T, h1Ω⟩ := yw_one hx hx1
  have hcl : YwClosed x (ywV 1 1 x) := ywV_closed hx hx1 zero_lt_one h1T h1Ω h1T h1Ω
  have hωx : ω < x := omega0_lt_inE hx
  have hglA : ∀ a t, a < ywV 1 1 x → t < ywV 1 1 x → glA a t x < ywV 1 1 x := by
    intro a t ha ht
    have hmT : max a t ∈ Tset x := vz_T_down hx hx1 hD2T hD21 (max_lt ha ht).le
    have hm1 : max a t < Om1 := (max_lt ha ht).trans hD21
    have hq := gmq_gt hx hx1 hmT hm1
    exact (xkA_lt hx hx1 hmT hm1 ((le_max_left _ _).trans_lt hq) ((le_max_right _ _).trans_lt hq)).trans
      (hcl _ hmT (max_lt ha ht))
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  by_cases hcB : c < tfBG
  · rw [vR_yr c hcB x]; exact (zmYr.lt c x hx hx1 hcB hg).trans hDD2
  have hcB' : tfBG ≤ c := not_lt.1 hcB
  have hGc : gcG 0 ≤ c := va_G_le_BG.trans hcB'
  obtain ⟨-, -, -, -, -, hlog, hmod, hdiv⟩ := gl_parts (yh_gfE_le hGc)
  rw [yrG_dec hGc] at hg
  have hgQE : yrQE (guE c) < x := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hg)
  have hgk : yrG (log (guE c) c) < x :=
    yrG_of_Q hωx ((le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hg))
  have hgd : yrG (c / guE c ^ log (guE c) c) < x :=
    yrG_of_Q hωx ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hg))
  have hgr : yrG (c % guE c ^ log (guE c) c) < x := (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hg)
  have hec : guE c ≤ c := gl_E_le (yh_gfE_le hGc)
  have hA : vA (guE c) x < ywV 1 1 x := by
    by_cases hAt : YhAt (guE c)
    · by_cases hJ : yhJ (guE c) < guE c
      · rw [vA_atom hAt hJ]
        have hJc : yhJ (guE c) < c := hJ.trans_le hec
        have hgJ : yrG (yhJ (guE c)) < x := by
          rw [yrQE_atom hAt hJ] at hgQE; exact yrG_of_Q hωx hgQE
        have hIlt : vI (yhJ (guE c)) x < ywV 1 1 x := by
          by_cases hjB : tfBG < yhJ (guE c)
          · rw [vI_high hjB (hJc.trans hc)]
            have hgo : yrG (yhJ (guE c) - (tfBG + 1)) < x := (va_off_gate hjB).trans_lt (max_lt hωx hgJ)
            have ho : yhJ (guE c) - (tfBG + 1) < c := (Ordinal.sub_le_self _ _).trans_lt hJc
            exact (inE_indec hD2E).add_lt hDD2 (IH _ ho (ho.trans hc) hgo)
          · rw [vI_low hjB]; exact IH _ hJc (hJc.trans hc) hgJ
        exact hcl _ (vz_T_down hx hx1 hD2T hD21 hIlt.le) hIlt
      · rw [va_fix_atom_BG hAt hJ ((hec.trans_lt hc)), vA_BG]; exact hDD2
    · rw [vA_psi hAt]
      have hK := yh_lev_lt hGc hAt
      have hI := yh_idx_lt hGc hAt
      rw [yrQE_psi hAt] at hgQE
      exact hglA _ _ (IH _ hK (hK.trans hc) (yrG_of_Q hωx ((le_max_left _ _).trans_lt hgQE)))
        (IH _ hI (hI.trans hc) (yrG_of_Q hωx ((le_max_right _ _).trans_lt hgQE)))
  rw [vR_dec hGc]
  exact (inE_indec hD2E).add_lt (InE.mul_lt hD2E (zm_opow_lt hD2E hA (IH _ hlog (hlog.trans hc) hgk))
    (IH _ hdiv (hdiv.trans hc) hgd)) (IH _ hmod (hmod.trans hc) hgr)

end Googology.Trans.PoR.InaccPsi.R2.Va
