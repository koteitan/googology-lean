import Googology.Trans.PoR.InaccPsi.R2.TcFn

/-!
# CL, UB, INV, CONV and EQ at every level `μ < Γ'` of the hierarchy `tcP`

`ψ = S.psi`, `Φ_μ = Tc.tcP μ` (data `tcDatL μ = tcDat(Ω₁ + μ)`, `R2.TcFn`), `u_μ = Ω₁^μ = Le.leOe μ`, `Γ' = lgGam'`
(the least strongly critical ordinal above `Γ_{Ω₁+1}`), `RiDg q e` (all digits of `e` below `q`).  An argument `B` is
*own* when `B ∈ Cl(B, ψ_{Ω₁}(B))`.  The proofs of `R2.SvLev`, `R2.SvCL`, `R2.SvPsi` (levels `< Γ_{Ω₁+1}`) with the
levels `< Γ'` and the codes `LgCl` (atom `Γ_{Ω₁+1}`):

* `TcLev q x` (**every level `j < Γ'` of `x` has `tcDatL j < q`**), `tc_dig_opow_lvl`, `tc_lvl_of_cl`, `tc_eps_lev`,
  `tc_diglev` (**every member `x` of `Cl(a, q)` has all its digits below `q`, all its levels `j < Γ'` with `tcDatL j <
  q`, and is a code `LgCl q x` when `x < Γ'`**, for a strongly critical `q`, once every collapse `ψ_{Ω₁}(e)`, `e < a`,
  of a member `e` with these properties is below `q`; the collapse `ψ_{Ω₂}(0) = Γ_{Ω₁+1}` is the atom);
* `TcClo`, `TcCL`, `TcUB`, `tc_CL_UB` (**CL(μ) and UB(μ) at every level `μ ≤ Γ'`**: `ψ_{Ω₁}(B + u_μ·D) ≤ Φ_μ(c + D)`
  for `u_μ ∣ B`, `ψ_{Ω₁}(B) ≤ Φ_μ(c)`, `D ≤ Ω₁`), `tc_UB`, `tc_inv` (INV(μ));
* `tc_conv` (**CONV(μ): `u_{μ+1} ∣ B` for every own `B` with `ψ_{Ω₁}(B)` a fixed point of `Φ_μ`**, `μ < Γ'`),
  `tc_conv_iff`, `tc_eq` (**EQ(μ): `ψ_{Ω₁}(B + u_μ·D) = Φ_μ(c + D)` and `D < ψ_{Ω₁}(B + u_μ·D)`** when `d < Φ_μ(c+d)`
  for every `d ≤ D`, `B` own, `u_μ ∣ B`, `Φ_μ(c) = ψ_{Ω₁}(B)`, `tcDatL μ < ψ_{Ω₁}(B)`, `μ < Γ'`), `tc_valid` (the
  converse), `tc_dvd_eps`.

No new axiom.  New definitions: the statement names `TcLev`, `TcClo`, `TcCL`, `TcUB`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb
  Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Ri
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Rk

variable {S : InaccSeq.{0}}


/-- The levels condition on `x` below `q`: every level `j < Γ'` of `x` has `tcDatL j < q`. -/
def TcLev (q x : Ordinal.{0}) : Prop :=
  ∀ j, j < lgGam' → x / Le.leOe j % Om 1 ≠ 0 → tcDatL j < q

/-- The data of a level is countable. -/
theorem tc_datL_lt (j : Ordinal.{0}) : tcDatL j < Om 1 := by rw [← Rj.rj_Om1]; exact tcDat_lt_Om1 _

theorem tc_G'_inE : InE (lgGam' : Ordinal.{0}) := Low.opow_eq_self_of_SC tc_SC_G'

theorem tc_Om1'_lt_G' : Om (1 : Ordinal.{0}) < lgGam' := by rw [← rj_Om1]; exact tc_Om1_lt_G'

theorem tc_Om1_mul_succ_lt {j : Ordinal.{0}} (hj : j < lgGam') : Om 1 * j + Om 1 < lgGam' := by
  rw [← mul_add_one]
  exact tc_G'_inE.mul_lt tc_Om1'_lt_G' (tc_G'_inE.add_lt hj (gg_one_lt_of_SC tc_SC_G'))

/-- **A level `j < Γ'` of `ω^y` is `y / Ω₁`, and `y < Γ'`.** -/
theorem tc_dig_opow_lvl {j y : Ordinal.{0}} (hj : j < lgGam') (h : ω ^ y / Le.leOe j % Om 1 ≠ 0) :
    y / Om 1 = j ∧ y < lgGam' := by
  obtain ⟨hlo, hhi⟩ := ri_dig_opow_ne h
  have hye : Om 1 * j + (y - Om 1 * j) = y := Ordinal.add_sub_cancel_of_le hlo
  have hr : y - Om 1 * j < Om 1 := by rw [← hye] at hhi; exact (add_lt_add_iff_left _).1 hhi
  refine ⟨by rw [← hye]; exact (ri_lvl hr).1, hhi.trans (tc_Om1_mul_succ_lt hj)⟩

/-- **`tcDatL (y / Ω₁) < q` for a code `y` over a strongly critical `q`.** -/
theorem tc_lvl_of_cl {q y : Ordinal.{0}} (hq : SC q) (hy : LgCl q y) : tcDatL (y / Om 1) < q := by
  unfold tcDatL
  rw [Rj.rj_Om1]
  exact tc_cl_dat hq _ (LgCl.add LgCl.om (tc_cl_div hq y hy))

/-- **An `ε`-number `p ≥ Ω₁` that is a code over `q` when `p < Γ_{Ω₁+1}` has all its levels below `q`.** -/
theorem tc_eps_lev {q p : Ordinal.{0}} (hq : SC q) (hp : ω ^ p = p) (hcl : p < lgGam' → LgCl q p) :
    TcLev q p := by
  intro j hj hd
  rw [← hp] at hd
  obtain ⟨hjy, hyG⟩ := tc_dig_opow_lvl hj hd
  rw [← hjy]
  exact tc_lvl_of_cl hq (hcl hyG)

/-- **The digits and the levels below `Γ_{Ω₁+1}` of the members of `Cl(a, q)`**, and the codes among them below
`Γ_{Ω₁+1}`, for a strongly critical `q`, once every collapse `ψ_{Ω₁}(e)`, `e < a`, of a member `e` with digits and
levels below `q` is below `q`. -/
theorem tc_diglev {a q : Ordinal.{0}} (hq : SC q)
    (hcoll : ∀ e, e < a → e ∈ S.CSet a q → RiDg q e → TcLev q e → S.psi e (Om 1) < q) :
    ∀ x, x ∈ S.CSet a q → RiDg q x ∧ TcLev q x ∧ (x < lgGam' → LgCl q x) := by
  have hqI : Indec q := lq_SC_indec hq
  have h1q : (1 : Ordinal.{0}) < q := by
    have := hq.2 0 hq.1 0 hq.1; rwa [veblen_zero_apply, opow_zero] at this
  have hopq : ∀ f, f < q → ω ^ f < q := fun f hf => by
    have := hq.2 0 hq.1 f hf; rwa [veblen_zero_apply] at this
  have hsmallD : ∀ v, v < q → RiDg q v := fun v hv j => (rhk_dig_le j v).trans_lt hv
  have hcount : ∀ v, v < Om 1 → TcLev q v := by
    intro v hv j _ h
    rw [ri_dig_count hv h, tcDatL_zero]; exact hq.1
  have hepsD : ∀ p, ω ^ p = p → Om 1 ≤ p → RiDg q p := by
    intro p hp h j
    have h1 := rhk_dig_opow j p
    rw [hp, lq_mod_indec (inE_indec hp) h, opow_zero] at h1
    exact h1.trans_lt h1q
  have hsmall : ∀ v, v < q → v < Om 1 → RiDg q v ∧ TcLev q v ∧ (v < lgGam' → LgCl q v) :=
    fun v hv hv1 => ⟨hsmallD v hv, hcount v hv1, fun _ => LgCl.small hv⟩
  have hbig : ∀ p, lgGam' ≤ p → (p < lgGam' → LgCl q p) := fun p hp h => absurd h (not_lt.2 hp)
  have hbigE : ∀ p, ω ^ p = p → lgGam' ≤ p → RiDg q p ∧ TcLev q p ∧ (p < lgGam' → LgCl q p) := fun p hp hG =>
    ⟨hepsD p hp (tc_Om1'_lt_G'.le.trans hG), tc_eps_lev hq hp (hbig p hG), hbig p hG⟩
  have hSCbig : ∀ p, SC p → Om 1 < p → RiDg q p ∧ TcLev q p ∧ (p < lgGam' → LgCl q p) := by
    intro p hp h1
    have hcl : p < lgGam' → LgCl q p := fun h => by
      rcases (ggGam_le hp h1).lt_or_eq with hlt | heq
      · exact absurd (lgGam'_le hp hlt) (not_le.2 h)
      · rw [← heq]; exact LgCl.gam
    exact ⟨hepsD p (Low.opow_eq_self_of_SC hp) h1.le, tc_eps_lev hq (Low.opow_eq_self_of_SC hp) hcl, hcl⟩
  intro x hx
  induction hx with
  | @small x hxb =>
    refine ⟨hsmallD x hxb, ?_, fun _ => LgCl.small hxb⟩
    rcases lt_or_ge x (Om 1) with h1 | h1
    · exact hcount x h1
    · intro j _ _
      exact (tc_datL_lt j).trans_le (h1.trans hxb.le)
  | zero => exact hsmall 0 hq.1 rb_Om1_indec.pos
  | inacc n =>
    exact hSCbig _ (SC_I (S := S) n) (gg_Om1_lt_I S n)
  | inaccW =>
    exact hSCbig _ (SC_Iw (S := S)) (gg_Om1_lt_Iw S)
  | @add x y _ _ ihx ihy =>
    refine ⟨fun j => (rhk_dig_add j x y).trans_lt (hqI.add_lt (ihx.1 j) (ihy.1 j)), ?_, fun h => ?_⟩
    · intro j hj h
      by_cases hx0 : x / Le.leOe j % Om 1 = 0
      · by_cases hy0 : y / Le.leOe j % Om 1 = 0
        · exfalso
          have := rhk_dig_add j x y
          rw [hx0, hy0, add_zero] at this
          exact h (le_antisymm this zero_le)
        · exact ihy.2.1 j hj hy0
      · exact ihx.2.1 j hj hx0
    · exact LgCl.add (ihx.2.2 (lt_of_le_of_lt le_self_add h)) (ihy.2.2 (lt_of_le_of_lt le_add_self h))
  | @phi x y _ _ ihx ihy =>
    by_cases hv : veblen x y < Om 1
    · have hx1 : x < Om 1 := (left_le_veblen x y).trans_lt hv
      have hy1 : y < Om 1 := (right_le_veblen x y).trans_lt hv
      have hxq : x < q := by have := ihx.1 0; rwa [rhk_dig_zero, Ordinal.mod_eq_of_lt hx1] at this
      have hyq : y < q := by have := ihy.1 0; rwa [rhk_dig_zero, Ordinal.mod_eq_of_lt hy1] at this
      exact hsmall _ (hq.2 x hxq y hyq) hv
    · push Not at hv
      have hcl : veblen x y < lgGam' → LgCl q (veblen x y) := fun h =>
        LgCl.phi (ihx.2.2 ((left_le_veblen x y).trans_lt h)) (ihy.2.2 ((right_le_veblen x y).trans_lt h))
      rcases eq_or_ne x 0 with rfl | hx0
      · refine ⟨fun j => ?_, fun j hj h => ?_, hcl⟩
        · rw [veblen_zero_apply]
          have hy0 := ihy.1 0
          rw [rhk_dig_zero] at hy0
          exact (rhk_dig_opow j y).trans_lt (hopq _ hy0)
        · rw [veblen_zero_apply] at h
          obtain ⟨hjy, hyG⟩ := tc_dig_opow_lvl hj h
          rw [← hjy]
          exact tc_lvl_of_cl hq (ihy.2.2 hyG)
      · exact ⟨hepsD _ (Tp.tpVeblen_fix (pos_iff_ne_zero.2 hx0)) hv,
          tc_eps_lev hq (Tp.tpVeblen_fix (pos_iff_ne_zero.2 hx0)) hcl, hcl⟩
  | @om x hx1 _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero]; exact hsmall 0 hq.1 rb_Om1_indec.pos
    · have hcl : Om x < lgGam' → LgCl q (Om x) := fun h => by
        have h2 : x < 1 + 1 := Om_lt_Om.1 (h.trans_le (lgGam'_le_Om2 S))
        rcases (Order.lt_add_one_iff.1 h2).lt_or_eq with h0 | h1
        · rw [Order.lt_one_iff] at h0; exact absurd h0 hx0
        · rw [h1]; exact LgCl.om
      exact ⟨hepsD _ (Low.opow_eq_self_of_SC (SC_Om hx0)) (Om_le_Om.2 (one_le_iff_ne_zero.2 hx0)),
        tc_eps_lev hq (Low.opow_eq_self_of_SC (SC_Om hx0)) hcl, hcl⟩
  | @coll π e hπ _ heC _ ihe =>
    show RiDg q (S.psi e.1 π) ∧ TcLev q (S.psi e.1 π) ∧ (S.psi e.1 π < lgGam' → LgCl q (S.psi e.1 π))
    by_cases hπ1 : π = Om 1
    · subst hπ1
      exact hsmall _ (hcoll e.1 e.2 heC ihe.1 ihe.2.1) (psi_lt Low.InR_Om_one _)
    · have hge : Om 1 ≤ S.psi e.1 π := Mx.mxOm1_le_psi hπ hπ1
      have hne : Om 1 ≠ S.psi e.1 π := fun h' =>
        psi_notMem hπ e.1 (h' ▸ CSet.Om_mem (CSet.one_mem _ _))
      exact hSCbig _ (SC_psi hπ e.1) (lt_of_le_of_ne hge hne)



/-- `q` is closed under every `Φ_j`, `j < μ`, with `tcDatL j < q`. -/
def TcClo (μ q : Ordinal.{0}) : Prop := ∀ j < μ, tcDatL j < q → ∀ z < q, tcP j z < q

/-- **CL(μ)** for `tcP`. -/
def TcCL (S : InaccSeq.{0}) (μ : Ordinal.{0}) : Prop :=
  ∀ B e q : Ordinal.{0}, Le.leOe μ ∣ B → SC q → TcClo μ q → S.psi B (Om 1) < q → e < Le.leOe μ →
    RiDg q e → TcLev q e → S.psi (B + e) (Om 1) < q

/-- **UB(μ)** for `tcP`: `ψ_{Ω₁}(B + u_μ·D) ≤ Φ_μ(c + D)` for `u_μ ∣ B`, `ψ_{Ω₁}(B) ≤ Φ_μ(c)`, `D ≤ Ω₁`. -/
def TcUB (S : InaccSeq.{0}) (μ : Ordinal.{0}) : Prop :=
  ∀ B c D : Ordinal.{0}, Le.leOe μ ∣ B → S.psi B (Om 1) ≤ tcP μ c → D ≤ Om 1 →
    S.psi (B + Le.leOe μ * D) (Om 1) ≤ tcP μ (c + D)

theorem tc_CL_zero : TcCL S 0 := by
  intro B e q _ _ _ hBq he _ _
  rw [Le.leOe_zero, Order.lt_one_iff] at he
  rw [he, add_zero]; exact hBq

/-- The digits and levels of `e % u_μ` from those of `e`, when `u_{j+1} ∣ e - e % u_μ` below `μ`. -/
theorem tc_rem_dl {μ q a t : Ordinal.{0}} (hq : SC q) (hdvd : Le.leOe μ ∣ a) (hdg : RiDg q (a + t))
    (hlv : TcLev q (a + t)) (ht : t < Le.leOe μ) : RiDg q t ∧ TcLev q t := by
  have hdig : ∀ j : Ordinal.{0}, j < μ → (a + t) / Le.leOe j % Om 1 = t / Le.leOe j % Om 1 := fun j hj =>
    rhk_dig_add_dvd j ((rhU_dvd_succ hj).trans hdvd)
  have hzero : ∀ j : Ordinal.{0}, μ ≤ j → t / Le.leOe j % Om 1 = 0 := fun j hj => by
    rw [Ordinal.div_eq_zero_of_lt (ht.trans_le (rhU_le hj)), Ordinal.zero_mod]
  refine ⟨fun j => ?_, fun j hj h => ?_⟩
  · rcases lt_or_ge j μ with hjk | hjk
    · rw [← hdig j hjk]; exact hdg j
    · rw [hzero j hjk]; exact hq.1
  · rcases lt_or_ge j μ with hjk | hjk
    · exact hlv j hj (by rw [hdig j hjk]; exact h)
    · exact absurd (hzero j hjk) h

/-- **INV(μ)** from CL(μ). -/
theorem tc_INV {μ : Ordinal.{0}} (hCL : TcCL S μ) {B D q : Ordinal.{0}} (hB : Le.leOe μ ∣ B)
    (hq : SC q) (hcl : TcClo μ q) (hBq : S.psi B (Om 1) < q) (hD : D ≤ Om 1)
    (hprev : ∀ d, d < D → d < q → S.psi (B + Le.leOe μ * d) (Om 1) < q) :
    S.psi (B + Le.leOe μ * D) (Om 1) ≤ q := by
  rcases le_or_gt (Om 1) q with h1 | h1
  · exact (psi_lt Low.InR_Om_one _).le.trans h1
  set u := Le.leOe μ with hudef
  have hu0 : u ≠ 0 := rhU_ne μ
  have hcoll : ∀ e, e < B + u * D → e ∈ S.CSet (B + u * D) q → RiDg q e → TcLev q e →
      S.psi e (Om 1) < q := by
    intro e he _ hdg hlv
    rcases lt_or_ge e B with heB | heB
    · exact lt_of_le_of_lt (psi_mono Low.InR_Om_one heB.le).1 hBq
    set e1 := e - B with he1def
    have hee : B + e1 = e := Ordinal.add_sub_cancel_of_le heB
    have he1 : e1 < u * D := by rw [← hee] at he; exact (add_lt_add_iff_left B).1 he
    have hdD : e1 / u < D := (Ordinal.lt_mul_iff_div_lt hu0).1 he1
    have hdΩ : e1 / u < Om 1 := hdD.trans_le hD
    have her : u * (e1 / u) + e1 % u = e1 := Ordinal.div_add_mod e1 u
    have hrlt : e1 % u < u := Ordinal.mod_lt _ hu0
    obtain ⟨m, hm⟩ := hB
    have he_eq : e = u * (m + e1 / u) + e1 % u := by
      rw [← hee]
      conv_lhs => rw [← her, hm]
      rw [← add_assoc, ← mul_add]
    have hdiv : e / u = m + e1 / u := by
      rw [he_eq, Ordinal.mul_add_div _ hu0, Ordinal.div_eq_zero_of_lt hrlt, add_zero]
    have hdq : e1 / u < q := by
      refine lt_of_le_of_lt ?_ (hdg μ)
      rw [← hudef, hdiv]; exact rd_le_mod_add m hdΩ
    have hPd := hprev _ hdD hdq
    have hee2 : B + u * (e1 / u) + e1 % u = e := by rw [add_assoc, her, hee]
    have hdvd' : u ∣ B + u * (e1 / u) := by rw [hm, ← mul_add]; exact dvd_mul_right _ _
    rw [← hee2] at hdg hlv
    obtain ⟨hdg2, hlv2⟩ := tc_rem_dl hq hdvd' hdg hlv hrlt
    have := hCL _ _ q hdvd' hq hcl hPd hrlt hdg2 hlv2
    rwa [hee2] at this
  have hinv := tc_diglev (S := S) hq hcoll
  refine psi_le_of_good (CSet.Om_mem (CSet.one_mem _ _)) fun x hx hx1 => ?_
  have := (hinv x hx).1 0
  rwa [rhk_dig_zero, Ordinal.mod_eq_of_lt hx1] at this

/-- **UB(μ)** from CL(μ). -/
theorem tc_UB_of {μ : Ordinal.{0}} (hCL : TcCL S μ) : TcUB S μ := by
  intro B c D hB hc
  induction D using WellFoundedLT.induction with
  | ind D IH =>
  intro hD
  rcases eq_or_ne D 0 with rfl | hD0
  · rw [mul_zero, add_zero, add_zero]; exact hc
  have hprev : ∀ d, d < D → d < tcP μ (c + D) →
      S.psi (B + Le.leOe μ * d) (Om 1) < tcP μ (c + D) := fun d hd _ =>
    (IH d hd (hd.le.trans hD)).trans_lt ((tcP_lt_iff μ).2 ((add_lt_add_iff_left c).2 hd))
  exact tc_INV hCL hB (tcP_SC μ _) (tc_clo_val μ _)
    (hc.trans_lt ((tcP_lt_iff μ).2 (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hD0)))) hD hprev

/-- **CL(μ+1)** from CL(μ) and UB(μ), `μ < Γ_{Ω₁+1}`. -/
theorem tc_CL_succ {μ : Ordinal.{0}} (hμ : μ < lgGam') (hCL : TcCL S μ) (hUB : TcUB S μ) :
    TcCL S (μ + 1) := by
  intro B e q hB hq hcl hBq he hdg hlv
  set u := Le.leOe μ with hudef
  have hu0 : u ≠ 0 := rhU_ne μ
  have hqI : Indec q := lq_SC_indec hq
  have her : u * (e / u) + e % u = e := Ordinal.div_add_mod e u
  have hrlt : e % u < u := Ordinal.mod_lt _ hu0
  have hdΩ : e / u < Om 1 := by
    rw [Le.leOe_succ] at he; exact (Ordinal.lt_mul_iff_div_lt hu0).1 he
  have hdig : e / u % Om 1 = e / u := Ordinal.mod_eq_of_lt hdΩ
  have hdq : e / u < q := by have := hdg μ; rwa [← hudef, hdig] at this
  have hBk : u ∣ B := (rhU_dvd le_self_add).trans hB
  have hP : S.psi (B + u * (e / u)) (Om 1) < q := by
    rcases eq_or_ne (e / u) 0 with h0 | h0
    · rw [h0, mul_zero, add_zero]; exact hBq
    have hdat : tcDatL μ < q := hlv μ hμ (by rw [← hudef, hdig]; exact h0)
    have hle := hUB B (S.psi B (Om 1)) (e / u) hBk (tcP_le_self μ _) hdΩ.le
    exact hle.trans_lt (hcl μ (lt_add_one μ) hdat _ (hqI.add_lt hBq hdq))
  have hdvd' : u ∣ B + u * (e / u) := dvd_add hBk (dvd_mul_right _ _)
  have hdg' : RiDg q (u * (e / u) + e % u) := by rw [her]; exact hdg
  have hlv' : TcLev q (u * (e / u) + e % u) := by rw [her]; exact hlv
  obtain ⟨hdg2, hlv2⟩ := tc_rem_dl hq (dvd_mul_right u (e / u)) hdg' hlv' hrlt
  have := hCL _ _ q hdvd' hq (fun j hj => hcl j (hj.trans (lt_add_one μ))) hP hrlt hdg2 hlv2
  rwa [add_assoc, her] at this

/-- **CL(λ)** at a limit `λ` from CL(j), `j < λ`. -/
theorem tc_CL_lim {l : Ordinal.{0}} (hl : IsSuccLimit l) (h : ∀ j < l, TcCL S j) : TcCL S l := by
  intro B e q hB hq hcl hBq he hdg hlv
  obtain ⟨j, hj, hej⟩ := rhU_lt_lim hl he
  exact h j hj B e q ((rhU_dvd hj.le).trans hB) hq (fun i hi => hcl i (hi.trans hj)) hBq hej hdg hlv

/-- **CL(μ) and UB(μ) at every level `μ ≤ Γ_{Ω₁+1}` of `ssP`.** -/
theorem tc_CL_UB (μ : Ordinal.{0}) : μ ≤ lgGam' → TcCL S μ ∧ TcUB S μ := by
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμ
  have hCL : TcCL S μ := by
    rcases zero_or_succ_or_isSuccLimit μ with h0 | ⟨j, rfl⟩ | hl
    · rw [h0]; exact tc_CL_zero
    · rw [Order.succ_eq_add_one] at IH hμ ⊢
      have hj : j < lgGam' := (lt_add_one j).trans_le hμ
      have h := IH j (lt_add_one j) hj.le
      exact tc_CL_succ hj h.1 h.2
    · exact tc_CL_lim hl fun j hj => (IH j hj (hj.le.trans hμ)).1
  exact ⟨hCL, tc_UB_of hCL⟩

/-- **`ψ_{Ω₁}(B + u_μ·D) ≤ Φ_μ(c + D)`** for `u_μ ∣ B`, `ψ_{Ω₁}(B) ≤ Φ_μ(c)`, `D ≤ Ω₁`, at every level
`μ ≤ Γ_{Ω₁+1}` of `ssP`. -/
theorem tc_UB {μ : Ordinal.{0}} (hμ : μ ≤ lgGam') : TcUB S μ := (tc_CL_UB μ hμ).2

/-- **INV(μ)** at every level `μ ≤ Γ_{Ω₁+1}` of `ssP`. -/
theorem tc_inv {μ B D q : Ordinal.{0}} (hμ : μ ≤ lgGam') (hB : Le.leOe μ ∣ B)
    (hq : SC q) (hcl : TcClo μ q) (hBq : S.psi B (Om 1) < q) (hD : D ≤ Om 1)
    (hprev : ∀ d, d < D → d < q → S.psi (B + Le.leOe μ * d) (Om 1) < q) :
    S.psi (B + Le.leOe μ * D) (Om 1) ≤ q :=
  tc_INV (tc_CL_UB μ hμ).1 hB hq hcl hBq hD hprev



/-- `u_μ ∈ Cl(a, b)` from `tcDatL μ < b`, `b` strongly critical, `μ < Γ_{Ω₁+1}`. -/
theorem tc_U_mem {μ a b : Ordinal.{0}} (ha : 0 < a) (hb : SC b) (hμ : μ < lgGam') (h : tcDatL μ < b) :
    Le.leOe μ ∈ S.CSet a b := tcU_mem ha hb (tc_code_lvl hb hμ h)

/-- `u_μ·D ∈ Cl(a, b)` from `tcDatL μ < b`, `D < b`, `b` strongly critical, `μ < Γ_{Ω₁+1}`. -/
theorem tc_U_mul_mem {μ a b D : Ordinal.{0}} (ha : 0 < a) (hb : SC b) (hμ : μ < lgGam') (h : tcDatL μ < b)
    (hD : D < b) : Le.leOe μ * D ∈ S.CSet a b := tcU_mul_mem ha hb (tc_code_lvl hb hμ h) hD

/-- **CONV(μ)**: `u_{μ+1} ∣ B` for every own `B` with `ψ_{Ω₁}(B)` a fixed point of `Φ_μ`, `μ < Γ_{Ω₁+1}`. -/
theorem tc_conv {μ : Ordinal.{0}} (hμ : μ < lgGam') {B : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1)))
    (hfix : tcP μ (S.psi B (Om 1)) = S.psi B (Om 1)) : Le.leOe (μ + 1) ∣ B := by
  set p := S.psi B (Om 1) with hpdef
  have hpSC : SC p := SC_psi Low.InR_Om_one B
  have hcoll : ∀ e, e < B → e ∈ S.CSet B p → RiDg p e → TcLev p e → S.psi e (Om 1) < p :=
    fun e he heC _ _ => lt_psi_of_mem Low.InR_Om_one
      (CSet.psi_mem he Low.InR_Om_one (mem_CSet_psi Low.InR_Om_one B) heC) (psi_lt Low.InR_Om_one _)
  have hdl := tc_diglev (S := S) hpSC hcoll B hown
  refine ri_dvd_of_dig (μ + 1) fun j hj => ?_
  have hjμ : j ≤ μ := Order.lt_add_one_iff.1 hj
  have hjΩ : j < lgGam' := hjμ.trans_lt hμ
  induction j using WellFoundedLT.induction with
  | ind j IHj =>
  by_contra hd0
  have hdj : tcDatL j < p := hdl.2.1 j hjΩ hd0
  have hfj : tcP j p = p := tcP_fix_mono hjμ hfix hdj
  have huj : Le.leOe j ∣ B := ri_dvd_of_dig j fun i hi =>
    IHj i hi (hi.trans hj) (hi.le.trans hjμ) (hi.trans hjΩ)
  set u := Le.leOe j with hudef
  set u2 := Le.leOe (j + 1) with hu2def
  have hu2 : u2 = u * Om 1 := Le.leOe_succ j
  have hupos : 0 < u := rhU_pos j
  have h0 := rd_Om1_ne
  obtain ⟨m, hm⟩ := huj
  set D0 := m % Om 1 with hD0
  set B0 := u2 * (m / Om 1) with hB0
  have hBe : B0 + u * D0 = B := by
    rw [hm, hB0, hD0, hu2, mul_assoc, ← mul_add, Ordinal.div_add_mod]
  have hD0lt : D0 < Om 1 := Ordinal.mod_lt m h0
  have hmdiv : B / u = m := by rw [hm, Ordinal.mul_div_cancel _ (rhU_ne _)]
  have hD00 : D0 ≠ 0 := by rw [hD0, ← hmdiv]; exact hd0
  have hD0p : D0 < p := by have := hdl.1 j; rwa [← hudef, hmdiv] at this
  have hlt' : u * D0 < u2 := by rw [hu2]; exact (mul_lt_mul_iff_right₀ hupos).2 hD0lt
  have hBdiv : B / u2 = m / Om 1 := by
    calc B / u2 = (u2 * (m / Om 1) + u * D0) / u2 := by rw [← hB0, hBe]
      _ = m / Om 1 := by
        rw [Ordinal.mul_add_div _ (rhU_ne (j + 1)), Ordinal.div_eq_zero_of_lt hlt', add_zero]
  have hB0m : B0 ∈ S.CSet B p := by
    have := rh_mod_mem (S := S) (m := j + 1) le_add_self B hown
    rwa [← hu2def, hBdiv] at this
  have hB0B : B0 < B := by
    rw [← hBe]; exact lt_add_of_pos_right _ (mul_pos hupos (pos_iff_ne_zero.2 hD00))
  have hB0p : S.psi B0 (Om 1) < p := psi_lt_psi_of_mem Low.InR_Om_one hB0B hB0m
  have hle := tc_UB (S := S) hjΩ.le B0 (S.psi B0 (Om 1)) D0
    (by rw [hB0]; exact (rhU_dvd le_self_add).trans (dvd_mul_right _ _)) (tcP_le_self _ _) hD0lt.le
  rw [hBe] at hle
  have hlt : S.psi B0 (Om 1) + D0 < p := (lq_SC_indec hpSC).add_lt hB0p hD0p
  have h2 : tcP j (S.psi B0 (Om 1) + D0) < p := by
    conv_rhs => rw [← hfj]
    exact (tcP_lt_iff j).2 hlt
  exact absurd (hle.trans_lt h2) (lt_irrefl _)

/-- **FWD and CONV together**: for an own `B ≠ 0` with `tcDatL μ < ψ_{Ω₁}(B)`, `μ < Γ_{Ω₁+1}`: `ψ_{Ω₁}(B)` is a
fixed point of `Φ_μ` iff `u_{μ+1} ∣ B`. -/
theorem tc_conv_iff {μ B : Ordinal.{0}} (hμ : μ < lgGam') (hown : B ∈ S.CSet B (S.psi B (Om 1))) (hB0 : B ≠ 0)
    (hd : tcDatL μ < S.psi B (Om 1)) :
    tcP μ (S.psi B (Om 1)) = S.psi B (Om 1) ↔ Le.leOe (μ + 1) ∣ B :=
  ⟨tc_conv hμ hown, fun h => tcFwdAll μ hμ B hown h hB0 hd⟩

/-- **EQ(μ)**: `ψ_{Ω₁}(B + u_μ·D) = Φ_μ(c + D)`, and `D < ψ_{Ω₁}(B + u_μ·D)`, when `d < Φ_μ(c+d)` for every `d ≤ D`,
for an own `B` with `u_μ ∣ B`, `Φ_μ(c) = ψ_{Ω₁}(B)` and `tcDatL μ < ψ_{Ω₁}(B)` (`μ < Γ_{Ω₁+1}`). -/
theorem tc_eq {μ : Ordinal.{0}} (hμ : μ < lgGam')
    {B c : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1))) (hB : Le.leOe μ ∣ B)
    (hc : tcP μ c = S.psi B (Om 1)) (hdB : tcDatL μ < S.psi B (Om 1)) :
    ∀ D, D < Om 1 → (∀ d, d ≤ D → d < tcP μ (c + d)) →
      D < S.psi (B + Le.leOe μ * D) (Om 1) ∧ S.psi (B + Le.leOe μ * D) (Om 1) = tcP μ (c + D) := by
  set u := Le.leOe μ with hudef
  have hupos : 0 < u := rhU_pos μ
  intro D
  induction D using WellFoundedLT.induction with
  | ind D IH =>
  intro hDΩ hcond
  have hIH : ∀ d, d < D → S.psi (B + u * d) (Om 1) = tcP μ (c + d) :=
    fun d hd => (IH d hd (hd.trans hDΩ) fun d' hd' => hcond d' (hd'.trans hd.le)).2
  have heq : S.psi (B + u * D) (Om 1) = tcP μ (c + D) := by
    rcases eq_or_ne D 0 with rfl | hD0
    · rw [mul_zero, add_zero, add_zero, hc]
    set v := S.psi (B + u * D) (Om 1) with hv
    have hvSC : SC v := SC_psi Low.InR_Om_one _
    have hBv : S.psi B (Om 1) < v :=
      rh_psi_lt_of_own hown (lt_add_of_pos_right _ (mul_pos hupos (pos_iff_ne_zero.2 hD0)))
    have hdv : tcDatL μ < v := hdB.trans hBv
    have hlt : ∀ d, d < D → tcP μ (c + d) < v := by
      intro d hd
      have hle : S.psi (B + u * d) (Om 1) ≤ v :=
        (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left B).2 (mul_le_mul_right hd.le _))).1
      have hdv' : d < v := (hcond d hd.le).trans_le (by rw [← hIH d hd]; exact hle)
      have hmem : B + u * d ∈ S.CSet (B + u * D) v :=
        CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add : B ≤ B + u * D)).2 hown)
          (tc_U_mul_mem (lt_of_lt_of_le (mul_pos hupos (pos_iff_ne_zero.2 hD0)) le_add_self)
            (SC_psi Low.InR_Om_one _) hμ hdv hdv')
      rw [← hIH d hd]
      exact psi_lt_psi_of_mem Low.InR_Om_one
        ((add_lt_add_iff_left B).2 ((mul_lt_mul_iff_right₀ hupos).2 hd)) hmem
    apply le_antisymm
    · exact tc_UB hμ.le B c D hB hc.ge hDΩ.le
    · rcases zero_or_succ_or_isSuccLimit D with h0 | ⟨d0, rfl⟩ | hlim
      · exact absurd h0 hD0
      · rw [Order.succ_eq_add_one] at hlt hDΩ ⊢
        have hd0v : d0 < v := (hcond d0 (Order.le_succ d0)).trans (hlt d0 (lt_add_one d0))
        have hDv : d0 + 1 < v := hvSC.add_one_lt hd0v
        have hown1 : B + u * (d0 + 1) ∈ S.CSet (B + u * (d0 + 1)) v :=
          CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add : B ≤ B + u * (d0 + 1))).2 hown)
            (tc_U_mul_mem (lt_of_lt_of_le (mul_pos hupos (lt_of_le_of_lt zero_le (lt_add_one d0))) le_add_self)
              (SC_psi Low.InR_Om_one _) hμ hdv hDv)
        have hne : B + u * (d0 + 1) ≠ 0 :=
          (lt_of_lt_of_le (mul_pos hupos (lt_of_le_of_lt zero_le (lt_add_one d0))) le_add_self).ne'
        have hfix : ∀ j < μ, tcDatL j < v → tcP j v = v := fun j hj hdj =>
          tcFwdAll j (hj.trans hμ) _ hown1 ((rhU_dvd_succ hj).trans (dvd_add hB (dvd_mul_right _ _))) hne hdj
        obtain ⟨e, he⟩ := tcP_range hvSC hdv hfix
        rw [← he]
        refine (tcP_le_iff μ).2 (not_lt.1 fun hlt' => ?_)
        have hle : e ≤ c + d0 := by
          rw [← add_assoc] at hlt'; exact Order.lt_add_one_iff.1 hlt'
        have := ((tcP_le_iff μ).2 hle).trans_lt (hlt d0 (lt_add_one d0))
        rw [he] at this
        exact lt_irrefl _ this
      · refine not_lt.1 fun hlt' => ?_
        obtain ⟨e, he, hve⟩ := ((tcP_normal μ).lt_iff_exists_lt (isSuccLimit_add c hlim)).1 hlt'
        rcases lt_or_ge e c with hec | hce
        · have : tcP μ e < v := ((tcP_lt_iff μ).2 hec).trans_le (by rw [hc]; exact hBv.le)
          exact absurd hve (not_lt.2 this.le)
        · have hσe : c + (e - c) = e := Ordinal.add_sub_cancel_of_le hce
          have hσ : e - c < D := by rw [← hσe] at he; exact (add_lt_add_iff_left c).1 he
          have := hlt _ hσ
          rw [hσe] at this
          exact absurd hve (not_lt.2 this.le)
  exact ⟨by rw [heq]; exact hcond D le_rfl, heq⟩

/-- **A valid `D` has `d < Φ_μ(c+d)` for every `d ≤ D`** (`u_μ ∣ B`, `Φ_μ(c) = ψ_{Ω₁}(B)`, `μ ≤ Γ_{Ω₁+1}`). -/
theorem tc_valid {μ B c D : Ordinal.{0}} (hμ : μ ≤ lgGam') (hB : Le.leOe μ ∣ B)
    (hc : tcP μ c = S.psi B (Om 1))
    (hv : D < S.psi (B + Le.leOe μ * D) (Om 1)) : ∀ d, d ≤ D → d < tcP μ (c + d) := by
  intro d hd
  by_contra hle
  push Not at hle
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact absurd hle (not_le.2 (tcP_SC _ _).1)
  have hDΩ : D ≤ Om 1 := hv.le.trans (psi_lt Low.InR_Om_one _).le
  have hprev : ∀ d'', d'' < D → d'' < tcP μ (c + d) →
      S.psi (B + Le.leOe μ * d'') (Om 1) < tcP μ (c + d) := fun d'' hd'' hq =>
    (tc_UB hμ B c d'' hB hc.ge (hd''.le.trans hDΩ)).trans_lt
      ((tcP_lt_iff μ).2 ((add_lt_add_iff_left c).2 (hq.trans_le hle)))
  have h := tc_inv (S := S) hμ hB (tcP_SC μ (c + d)) (tc_clo_val μ _)
    (by rw [← hc]; exact (tcP_lt_iff μ).2 (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hd0))) hDΩ hprev
  exact absurd ((h.trans hle).trans hd) (not_le.2 hv)

/-- An `ε`-number `p ≥ Γ_{Ω₁+1}` is a multiple of every `u_μ`, `μ ≤ Γ_{Ω₁+1}`. -/
theorem tc_dvd_eps {μ p : Ordinal.{0}} (hμ : μ ≤ lgGam') (hp : ω ^ p = p) (hG : lgGam' ≤ p) :
    Le.leOe μ ∣ p := by
  have hI : Indec p := inE_indec hp
  have hk : Om 1 * μ ≤ p := by
    have hGG : Om 1 * lgGam' = lgGam' := by
      conv_lhs => rw [← Bt.Om1_opow, ← tc_G'_inE]
      rw [← opow_add, Ordinal.add_of_omega0_opow_le (by rw [tc_G'_inE]; exact tc_Om1'_lt_G') tc_G'_inE.le,
        tc_G'_inE]
    calc Om 1 * μ ≤ Om 1 * lgGam' := mul_le_mul_right hμ _
      _ = lgGam' := hGG
      _ ≤ p := hG
  refine rh_dvd_of_indec μ hI ?_
  unfold Le.leOe
  rw [← hp]
  exact opow_le_opow_right omega0_pos hk

end Googology.Trans.PoR.InaccPsi.R2.Tc
