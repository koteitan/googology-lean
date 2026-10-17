import Googology.Trans.PoR.InaccPsi.R2.CxCross
import Googology.Trans.PoR.InaccPsi.R2.RzLow
import Googology.Trans.PoR.InaccPsi.R2.LhSk

/-!
# EQ and TC below `L(n+1)`: the caps of the range, the points off `υ`, the restarts below `B₀`

`L(ξ) = Nc.ncL S ξ`, `c_n = L(n+1)` (`Bc.bcC`), `B_n = Bc.bcB S n`, `η_ξ = Ω_ω + P'·ξ`,
`cap(λ) = P(η_λ + ω^{e(η_λ)})` (`cdCapB`), `r(λ) = k_λ(Θ_λ(m_λ))` (`cdR`), `m* = L(0)`.

* `cxEta_window` (**the window of a level-2 name**): `x < η_{n+1}` and `x ≠ η_k` for every `k`
  give `x + ω^{e(x)} ≤ η_{n+1}`;
* `cxCap_le`: a restart `λ` of the range with `ρ_λ < L(n+1)` has `cap(λ) ≤ L(n+1)`;
  `cxR_lt_of_below`: with CapV at `λ`, `r(λ) < L(n+1)`;
* `CxEQtop S` (EQ at the restarts above `L(n+1)` only) and `cxEQ_of_top`: CapV below `L(ω)` and
  `CxEQtop` give `CdEQ` (below `L(n+1)` the predicted values stay below `L(n+1)`; `L(n+1)` is not in
  the range);
* `cxTCAt_of_le1`: a point `x < L(n+1)` with `x ≤₁ L(ω+1)` satisfies the (TC) clause;
* `cxGap_B0`: a restart `λ < B₀` with `ρ_λ < L(n+1)` has its reach below `L(n+1)`;
  `cxGap_off`: so has every point `x < L(n+1)` off `υ` when `L(ω) ≤ ν_C` (`Lh.lhSk_all`);
* `CxUpsRest S` (the `υ`-points below `L(n+1)` that are not restarts: reach below `L(n+1)` or
  `≤₁ L(ω+1)`), `cxTC_below`: UPPER, LOWER, CapV below `L(ω)`, `L(ω) ≤ ν_C`, (CL), `T`,
  `m* ≤₁ L(ω+1)` and `CxUpsRest` give, at every `x < L(n+1)`, a reach below `L(n+1)` or the (TC)
  clause;
* `CxTCtop S` (TCrest on `(L(n+1), L(n+2))` only) and `cxTCrest_of`: the part below `L(n+1)`, `T`,
  (CL) and `CxTCtop` give `CdTCrest`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Cx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

theorem cxExp_zero : cdExp (0 : Ordinal.{0}) = 0 := by
  unfold cdExp
  have hu : {e : Ordinal.{0} | ω ^ e ∣ (0 : Ordinal.{0})} = Set.univ := by
    ext e; simp
  rw [hu]; exact csSup_of_not_bddAbove not_bddAbove_univ |>.trans (by simp)

/-- **The window of a level-2 name**: `x < Ω_ω + P'·(n+1)`, `x ≠ Ω_ω + P'·k` for every `k`
give `x + ω^{e(x)} ≤ Ω_ω + P'·(n+1)`. -/
theorem cxEta_window {x : Ordinal.{0}} (n : ℕ)
    (hx : x < Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}))
    (hne : ∀ k : ℕ, x ≠ Om ω + Nc.ncPp S * (k : Ordinal.{0})) :
    x + ω ^ cdExp x ≤ Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) := by
  have hSC : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero
  have hOw : ω ^ Om (ω : Ordinal.{0}) = Om ω := Low.opow_eq_self_of_SC hSC
  have hPo : ω ^ Nc.ncPp S = Nc.ncPp S := Lw.lw_Pp_opow S
  have hP0 : Nc.ncPp S ≠ 0 := (Qq.qqPp_pos (S := S)).ne'
  rcases lt_or_ge x (Om ω) with hxO | hxO
  · have hpow : ω ^ cdExp x < Om ω := by
      rcases eq_or_ne x 0 with h0 | h0
      · rw [h0, cxExp_zero, opow_zero]
        exact (one_lt_omega0.trans_le (Ordinal.le_mul_left ω omega0_pos)).trans (Pp.ppSC_ww hSC)
      · exact (le_of_dvd h0 (cdExp_dvd h0)).trans_lt hxO
    exact (hSC.isPrincipal hxO hpow).le.trans le_self_add
  · obtain ⟨x', rfl⟩ := exists_add_of_le hxO
    have hx' : x' < Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) := (add_lt_add_iff_left _).1 hx
    have hdec : Nc.ncPp S * (x' / Nc.ncPp S) + x' % Nc.ncPp S = x' := Ordinal.div_add_mod x' _
    have hr : x' % Nc.ncPp S < Nc.ncPp S := Ordinal.mod_lt x' hP0
    have hq : x' / Nc.ncPp S < ((n + 1 : ℕ) : Ordinal.{0}) := (Ordinal.lt_mul_iff_div_lt hP0).1 hx'
    obtain ⟨k, hk⟩ : ∃ k : ℕ, x' / Nc.ncPp S = (k : Ordinal.{0}) :=
      lt_omega0.1 (hq.trans (natCast_lt_omega0 _))
    have hkn : k + 1 ≤ n + 1 := by
      have : (k : Ordinal.{0}) < ((n + 1 : ℕ) : Ordinal.{0}) := hk ▸ hq
      exact_mod_cast this
    rw [hk] at hdec
    have hr0 : x' % Nc.ncPp S ≠ 0 := by
      intro h0
      apply hne k
      rw [← hdec, h0, add_zero]
    have hdO : ω ^ Nc.ncPp S ∣ Om ω := by
      rw [← hOw]; exact opow_dvd_opow ω (cdPp_lt_Om_omega S).le
    have hd : ω ^ Nc.ncPp S ∣ Om ω + Nc.ncPp S * (k : Ordinal.{0}) :=
      dvd_add hdO (by rw [hPo]; exact dvd_mul_right _ _)
    have h1 : Om ω + Nc.ncPp S * (k : Ordinal.{0}) < Om ω + x' := by
      rw [← hdec, ← add_assoc]; exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hr0)
    have h2 : Om ω + x' < Om ω + Nc.ncPp S * (k : Ordinal.{0}) + ω ^ Nc.ncPp S := by
      rw [← hdec, ← add_assoc, hPo]; exact (add_lt_add_iff_left _).2 hr
    obtain ⟨-, hw⟩ := cdWin hd h1 h2
    refine hw.le.trans ?_
    rw [hPo, add_assoc, ← mul_add_one]
    have : (k : Ordinal.{0}) + 1 = ((k + 1 : ℕ) : Ordinal.{0}) := (Nat.cast_succ k).symm
    rw [this]
    gcongr

/-- **The cap of a restart of the range below `L(n+1)` is at most `L(n+1)`.** -/
theorem cxCap_le {l : Ordinal.{0}} (hr : CdRange S l) (n : ℕ)
    (hlt : upsilon l < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) :
    cdCapB S l ≤ Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) := by
  have hLeq := Lw.lw_L_eq S ((n + 1 : ℕ) : Ordinal.{0})
  obtain ⟨-, -, hηt, hpv⟩ := cdEta_pv_spec (S := S)
    (η0 := Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0})) hr.1.1 (hLeq ▸ hlt)
  have hne : ∀ k : ℕ, cdEta S l ≠ Om ω + Nc.ncPp S * (k : Ordinal.{0}) := by
    intro k hk
    have hρ : upsilon l = Nc.ncL S (k : Ordinal.{0}) := by rw [← hpv, hk, Lw.lw_L_eq]
    have hc : cdCode S l = Nc.ncPp S := by
      cases k with
      | zero => exact (cdCode_L0 (by simpa using hρ)).2
      | succ j => exact cdCode_L j hρ
    exact absurd hr.2.2.2 (by rw [hc]; exact lt_irrefl _)
  unfold cdCapB
  rw [hLeq]
  exact Pv_mono (cxEta_window n hηt hne)

/-- **The predicted value of a restart of the range below `L(n+1)`** is below `L(n+1)` (with CapV). -/
theorem cxR_lt_of_below {l : Ordinal.{0}} (hr : CdRange S l) (hV : CdCapV S l) (n : ℕ)
    (hlt : upsilon l < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) :
    cdR S l < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) :=
  lt_of_lt_of_le hV (cxCap_le hr n hlt)

/-- **EQ at the restarts above `L(n+1)`**: for `λ` of the range with `L(n+1) < ρ_λ` and
`r(λ) < L(n+2)`, `B_n ρ_λ = ρ_{lam}`, `B_n(r(λ)) = r(lam)` for some `lam` of the range. -/
def CxEQtop (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l, CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    ∃ l', CdRange S l' ∧ Bc.bcB S n (upsilon l) = upsilon l' ∧ Bc.bcB S n (cdR S l) = cdR S l'

/-- **EQ from EQ above `L(n+1)`** and CapV below `L(ω)`. -/
theorem cxEQ_of_top (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l)
    (h : CxEQtop S) : CdEQ S := by
  intro n l hl hge hlt
  rcases lt_trichotomy (upsilon l) (Bc.bcC S n) with hb | he | ha
  · exfalso
    have hω : upsilon l < Nc.ncL S ω := hb.trans (Bc.bcC_lt S n)
    exact absurd (cxR_lt_of_below hl (hV l hl hω) n hb) (not_lt.2 hge)
  · exfalso
    have hc := cdCode_L n he
    exact absurd hl.2.2.2 (by rw [hc]; exact lt_irrefl _)
  · exact h n l hl ha hlt

/-- **(TC) at a point below `L(n+1)` with `x ≤₁ L(ω+1)`** (`B_n = id` below `L(n+1)`). -/
theorem cxTCAt_of_le1 {n : ℕ} {x : Ordinal.{0}} (hx : x < Bc.bcC S n)
    (h : le1 x (Nc.ncL S (ω + 1))) : CdTCAt S n x := by
  refine Or.inr fun z h1 h2 => ⟨le1_of_le_of_le1 h1 (h2.le.trans (cxC_lt_L1 n).le) h, ?_⟩
  have hBx : Bc.bcB S n x = x := Bc.bcB_fix' S n x hx
  have hxz : x ≤ Bc.bcB S n z := by
    rw [← hBx]; exact (Bc.bcB_mono' S n).monotoneOn (hx.trans (cxC_lt n)) h2 h1
  rw [hBx]
  exact le1_of_le_of_le1 hxz (Bc.bcB_bound' S n z h2).le h

/-- `l < s`, `ω·ω ∣ s` give `l + ω·ω ≤ s`. -/
theorem cxAdd_ww_le {l s : Ordinal.{0}} (hd : (ω : Ordinal.{0}) * ω ∣ s) (h : l < s) :
    l + (ω : Ordinal.{0}) * ω ≤ s := by
  obtain ⟨q, rfl⟩ := hd
  have hw : (ω : Ordinal.{0}) * ω ≠ 0 := (mul_pos omega0_pos omega0_pos).ne'
  have hdm := Ordinal.div_add_mod l ((ω : Ordinal.{0}) * ω)
  have hmod : l % ((ω : Ordinal.{0}) * ω) < (ω : Ordinal.{0}) * ω := Ordinal.mod_lt l hw
  have hq : l / ((ω : Ordinal.{0}) * ω) < q := by
    by_contra hge
    push Not at hge
    have : (ω : Ordinal.{0}) * ω * q ≤ l := by
      rw [← hdm]; exact (mul_le_mul_right hge _).trans le_self_add
    exact absurd h (not_lt.2 this)
  have hww : (ω : Ordinal.{0}) * ω = ω ^ (2 : Ordinal.{0}) := by
    rw [show (2 : Ordinal.{0}) = 1 + 1 from one_add_one_eq_two.symm, opow_add, opow_one]
  have habs : l % ((ω : Ordinal.{0}) * ω) + (ω : Ordinal.{0}) * ω = (ω : Ordinal.{0}) * ω := by
    rw [hww] at hmod ⊢
    exact Ordinal.add_of_omega0_opow_le hmod le_rfl
  calc l + (ω : Ordinal.{0}) * ω
      = (ω : Ordinal.{0}) * ω * (l / ((ω : Ordinal.{0}) * ω)) + (ω : Ordinal.{0}) * ω := by
        conv_lhs => rw [← hdm]
        rw [add_assoc, habs]
    _ = (ω : Ordinal.{0}) * ω * (l / ((ω : Ordinal.{0}) * ω) + 1) := (mul_add_one _ _).symm
    _ ≤ (ω : Ordinal.{0}) * ω * q := mul_le_mul_right (Order.add_one_le_of_lt hq) _

/-- `L(n+1) = υ_λ` with `λ` a restart index, and every `υ_ξ ≤ x < L(n+1)` has `υ_{ξ+1} ≤ L(n+1)`. -/
theorem cxUps_succ_le {n : ℕ} {ξ x : Ordinal.{0}} (h1 : upsilon ξ ≤ x) (h2 : x < Bc.bcC S n) :
    upsilon (ξ + 1) ≤ Bc.bcC S n := by
  obtain ⟨lam, -, hlam⟩ := Pp.ppL_succ_restart (S := S) n
  have hlt : upsilon ξ < upsilon lam := by
    have : upsilon ξ < Bc.bcC S n := h1.trans_lt h2
    rwa [show Bc.bcC S n = upsilon lam from hlam] at this
  have hξ : ξ < lam := upsilon_normal.strictMono.lt_iff_lt.1 hlt
  show upsilon (ξ + 1) ≤ Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})
  rw [hlam]
  exact upsilon_normal.strictMono.monotone (Order.add_one_le_of_lt hξ)

/-- **A restart below `B₀` and below `L(n+1)` has its reach below `L(n+1)`** (`lh(ρ_λ) = δ_λ + O(λ)`). -/
theorem cxGap_B0 {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < cdB0) {n : ℕ}
    (hlt : upsilon l < Bc.bcC S n) : ∃ r < Bc.bcC S n, IsReach R2C (upsilon l) r := by
  refine ⟨_, ?_, reach_allGen vzSpec2 hl hlB⟩
  obtain ⟨lam, hlamr, hlam⟩ := Pp.ppL_succ_restart (S := S) n
  have hlt' : upsilon l < upsilon lam := by
    rwa [show Bc.bcC S n = upsilon lam from hlam] at hlt
  have hllam : l < lam := upsilon_normal.strictMono.lt_iff_lt.1 hlt'
  have hdvd : (ω : Ordinal.{0}) * ω ∣ lam := by
    have := hlamr.2; rwa [pow_two] at this
  have hidx : l + ω + 1 + 1 < lam := by
    have h3 : (ω : Ordinal.{0}) + 1 + 1 < ω * ω := by
      have h2ω : (1 + 1 : Ordinal.{0}) < ω := by
        rw [one_add_one_eq_two]; exact_mod_cast natCast_lt_omega0 2
      calc (ω : Ordinal.{0}) + 1 + 1 = ω + (1 + 1) := add_assoc _ _ _
        _ < ω + ω := (add_lt_add_iff_left _).2 h2ω
        _ = ω * 2 := (Ordinal.mul_two _).symm
        _ < ω * ω := mul_lt_mul_of_pos_left (by exact_mod_cast natCast_lt_omega0 2) omega0_pos
    calc l + ω + 1 + 1 = l + (ω + 1 + 1) := by simp only [add_assoc]
      _ < l + ω * ω := (add_lt_add_iff_left _).2 h3
      _ ≤ lam := cxAdd_ww_le hdvd hllam
  have hlt2 : upsilon (l + ω + 1) + VzOrec l < upsilon (l + ω + 1 + 1) :=
    Rz.rz_delta_add_lt (vzSpec2.le l hl hlB)
  show upsilon (l + ω + 1) + VzOrec l < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})
  rw [hlam]
  exact hlt2.trans (upsilon_normal.strictMono hidx)

/-- **A point off `υ` below `L(n+1)` has its reach below `L(n+1)`**, when `L(ω) ≤ ν_C`. -/
theorem cxGap_off (hlow : Nc.ncL S ω ≤ nuC) {n : ℕ} {x : Ordinal.{0}} (hx : x < Bc.bcC S n)
    (hU : ¬ UpsPt x) : ∃ r < Bc.bcC S n, IsReach R2C x r := by
  have hxC : x < nuC := (hx.trans (Bc.bcC_lt S n)).trans_le hlow
  obtain ⟨ξ, r, h1, -, hr, -, hr2, -⟩ := Lh.lhSk_all hxC hU
  exact ⟨r, hr2.trans_le (cxUps_succ_le h1 hx), hr⟩

/-- **The `υ`-points below `L(n+1)` that are not restarts**: each has a reach below `L(n+1)` or is
`≤₁ L(ω+1)`. -/
def CxUpsRest (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ x < Bc.bcC S n, UpsPt x → (∀ l, IsRestartIdx l → x ≠ upsilon l) →
    (∃ r < Bc.bcC S n, IsReach R2C x r) ∨ le1 x (Nc.ncL S (ω + 1))

/-- **(TC) below `L(n+1)`**: UPPER, LOWER, CapV below `L(ω)`, `L(ω) ≤ ν_C`, (CL), `T`,
`m* ≤₁ L(ω+1)` and `CxUpsRest` give, at every `x < L(n+1)`, a reach below `L(n+1)` or the (TC)
clause. -/
theorem cxTC_below (hU : CdUPPER S) (hL : CdLOWER S)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l) (hlow : Nc.ncL S ω ≤ nuC)
    (hC : CdCL S) (hT : CxT S) (hm : le1 (Nc.ncL S 0) (Nc.ncL S (ω + 1))) (hups : CxUpsRest S) :
    ∀ n : ℕ, ∀ x < Bc.bcC S n, (∃ r < Bc.bcC S n, IsReach R2C x r) ∨ CdTCAt S n x := by
  intro n x hx
  by_cases hUx : UpsPt x
  swap
  · exact Or.inl (cxGap_off hlow hx hUx)
  by_cases hres : ∃ l, IsRestartIdx l ∧ x = upsilon l
  swap
  · push Not at hres
    rcases hups n x hx hUx hres with h | h
    · exact Or.inl h
    · exact Or.inr (cxTCAt_of_le1 hx h)
  obtain ⟨l, hl, rfl⟩ := hres
  rcases lt_or_ge l cdB0 with hlB | hlB
  · exact Or.inl (cxGap_B0 hl hlB hx)
  by_cases hk : ∃ k : ℕ, upsilon l = Nc.ncL S (k : Ordinal.{0})
  · obtain ⟨k, hk⟩ := hk
    refine Or.inr (cxTCAt_of_le1 hx ?_)
    rw [hk]
    cases k with
    | zero => simpa using hm
    | succ j => exact ((Pp.ppP_of_cross hC hT).2 j).2
  push Not at hk
  have hlω : upsilon l < Nc.ncL S ω := hx.trans (Bc.bcC_lt S n)
  have hr : CdRange S l := by
    rcases lt_or_ge (upsilon l) (cdMstar S) with hlev | hlev
    · exact cdRange_level1 hl hlB hlev
    · exact (cdRange_iff_level2 hl hlB hlev hlω).2 hk
  exact Or.inl ⟨cdR S l, cxR_lt_of_below hr (hV l hr hlω) n hx, cdEnum_exact hU hL hr⟩

/-- **TCrest on `(L(n+1), L(n+2))`.** -/
def CxTCtop (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ x, Bc.bcC S n < x → x < Bc.bcC S (n + 1) →
    (∃ l, CdRange S l ∧ x = upsilon l ∧ cdR S l < Bc.bcC S (n + 1)) ∨ CdTCAt S n x

/-- **TCrest from its part below `L(n+1)`, `T`, (CL) and its part on `(L(n+1), L(n+2))`.** -/
theorem cxTCrest_of
    (hbelow : ∀ n : ℕ, ∀ x < Bc.bcC S n, (∃ r < Bc.bcC S n, IsReach R2C x r) ∨ CdTCAt S n x)
    (hT : CxT S) (hC : CdCL S) (htop : CxTCtop S) : CdTCrest S := by
  intro n x hx
  rcases lt_trichotomy x (Bc.bcC S n) with hb | he | ha
  · rcases hbelow n x hb with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rw [he]; exact Or.inr (Or.inr ((cxTCAt_L_iff hT n).2 (hC n)))
  · rcases htop n x ha hx with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

end Googology.Trans.PoR.InaccPsi.R2.Cx
