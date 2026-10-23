import Googology.Trans.PoR.InaccPsi.R2.RkPsi
import Googology.Trans.PoR.InaccPsi.R2.RiB
import Googology.Trans.PoR.InaccPsi.R2.MxB

/-!
# `B_n` at a level `μ < ε_{Ω₁+1}`: the image level `B_n μ`, `u_μ`, and `ψ_{Ω₁}(B + u_μ·D)`

`B_n = Bc.bcB S n`, `c_n = L(n+1) = Bc.bcC S n`, `u_μ = Ω₁^μ = Le.leOe μ`, `σ = bcSig (bcPre (n+1)) bcPreW`,
`rkDat μ = rjDat (Ω₁ + μ)`.  The image level is **`B_n μ` itself**: on the codes `B_n` moves the countable leaves and
keeps `Ω₁`, `+` and `ω^·`.

* `rk_E_eq` (`ε_{Ω₁+1} = φ(1, Ω₁ + 1)`), `rkB_E` (**`B_n ε_{Ω₁+1} = ε_{Ω₁+1}`**);
* `rkB_cl` (**a code `μ` over `x < L(ω)` is in the domain of `B_n`, and `B_n μ` is a code over `B_n x`**),
  `rkB_lt_E`, `rkB_dat_lt` (**`rkDat μ < x ⇒ rkDat (B_n μ) < B_n x`**), `rkB_succ`;
* `rkB_Om1mul` (**`B_n(Ω₁·μ) = Ω₁·B_n μ`**), `rkB_Oe` (**`B_n(u_μ) = u_{B_n μ}`**), `rkB_Oe_mul`
  (**`B_n(u_μ·D) = u_{B_n μ}·B_n D`**) for codes over `c_{n+1}` and countable `D < c_{n+1}`;
* `rkB_psi` (**`B_n(ψ_{Ω₁}(B + u_μ·D)) = ψ_{Ω₁}(B' + u_{B_n μ}·B_n D)`**), `rk_dvd_sig`, `rkB_dvd`
  (**`u_μ ∣ B` gives `u_{B_n μ} ∣ B'`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Lq
  Googology.Trans.PoR.InaccPsi.R2.Rb Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rh
  Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mv

variable {S : InaccSeq.{0}}

/-- **`ε_{Ω₁+1} = φ(1, Ω₁ + 1)`.** -/
theorem rk_E_eq : (ggE : Ordinal.{0}) = veblen 1 (Om 1 + 1) := by
  have hv : ω ^ veblen 1 (Om 1 + 1) = veblen 1 (Om 1 + 1) := Tp.tpVeblen_fix zero_lt_one
  refine le_antisymm (ggE_le hv ((lt_add_one _).trans_le (right_le_veblen _ _))) ?_
  obtain ⟨c, hc⟩ := (mem_range_veblen (o := 1) one_ne_zero).2 fun b hb => by
    rw [Order.lt_one_iff] at hb; rw [hb, veblen_zero_apply]; exact rk_E_inE
  rw [← hc]
  refine (veblen_le_veblen_iff_right).2 (Order.add_one_le_of_lt (not_le.1 fun hcO => ?_))
  have hO : SC (Om 1 : Ordinal.{0}) := SC_Om one_ne_zero
  have hle : veblen 1 c ≤ Om 1 := by
    rcases hcO.lt_or_eq with h | h
    · exact (hO.2 1 (gg_one_lt_of_SC hO) c h).le
    · rw [h]
      refine ((isNormal_veblen 1).le_iff_forall_le (Om_isSuccLimit one_ne_zero)).2 fun b hb => ?_
      exact (hO.2 1 (gg_one_lt_of_SC hO) b hb).le
  rw [hc] at hle
  exact absurd rk_Om1_E (not_lt.2 hle)

theorem rk_one_D : MvD S (1 : Ordinal.{0}) := mvD_of_lt (Ri.ri_one_lt_L S)

/-- **`B_n ε_{Ω₁+1} = ε_{Ω₁+1}`.** -/
theorem rkB_E {n : ℕ} : MvD S ggE ∧ Bc.bcB S n ggE = ggE := by
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  obtain ⟨hDO1, hBO1⟩ := mvB_add (k := n) hDO (rk_one_D (S := S))
  rw [hBO, mwB_one] at hBO1
  have hv : ω ^ veblen 1 (Om 1 + 1) = veblen 1 (Om 1 + 1) := Tp.tpVeblen_fix zero_lt_one
  have hlim : IsSuccLimit (veblen 1 (Om 1 + 1)) := ev_isSuccLimit_of_inE hv
  have hO1 : (1 : Ordinal.{0}) < Om 1 := gg_one_lt_of_SC (SC_Om one_ne_zero)
  have hOv : Om 1 < veblen 1 (Om 1 + 1) := (lt_add_one _).trans_le (right_le_veblen _ _)
  have h2 : Om 1 + 1 < veblen 1 (Om 1 + 1) := hlim.add_one_lt hOv
  have h1 : (1 : Ordinal.{0}) < veblen 1 (Om 1 + 1) := hO1.trans hOv
  obtain ⟨hD, hB⟩ := mwB_phi (k := n) (rk_one_D (S := S)) hDO1 h1 h2
  rw [mwB_one, hBO1, ← rk_E_eq] at hB
  rw [← rk_E_eq] at hD
  exact ⟨hD, hB⟩

/-- **A code over `x < L(ω)` is in the domain of `B_n`, and its image is a code over `B_n x`.** -/
theorem rkB_cl {n : ℕ} {x : Ordinal.{0}} (hxL : x < Nc.ncL S ω) :
    ∀ μ, GgCl x μ → MvD S μ ∧ GgCl (Bc.bcB S n x) (Bc.bcB S n μ) := by
  intro μ hμ
  induction hμ with
  | @small a ha =>
    exact ⟨mvD_of_lt (ha.trans hxL), GgCl.small ((Bc.bcB_lt_iff (ha.trans hxL) hxL).2 ha)⟩
  | om =>
    obtain ⟨hD, hB⟩ := mvB_Om1 (S := S) (k := n)
    exact ⟨hD, by rw [hB]; exact GgCl.om⟩
  | @add a b _ _ iha ihb =>
    obtain ⟨hD, hB⟩ := mvB_add (k := n) iha.1 ihb.1
    exact ⟨hD, by rw [hB]; exact GgCl.add iha.2 ihb.2⟩
  | @phi a b _ _ iha ihb =>
    by_cases h : a < veblen a b ∧ b < veblen a b
    · obtain ⟨hD, hB⟩ := mwB_phi (k := n) iha.1 ihb.1 h.1 h.2
      exact ⟨hD, by rw [hB]; exact GgCl.phi iha.2 ihb.2⟩
    · rcases not_and_or.1 h with h' | h'
      · have e : veblen a b = a := le_antisymm (not_lt.1 h') (left_le_veblen a b)
        rw [e]; exact iha
      · have e : veblen a b = b := le_antisymm (not_lt.1 h') (right_le_veblen a b)
        rw [e]; exact ihb

/-- `B_n μ < ε_{Ω₁+1}` for a code `μ < ε_{Ω₁+1}` over `x < L(ω)`. -/
theorem rkB_lt_E {n : ℕ} {x μ : Ordinal.{0}} (hxL : x < Nc.ncL S ω) (hμ : GgCl x μ) (hμE : μ < ggE) :
    Bc.bcB S n μ < ggE := by
  obtain ⟨hDE, hBE⟩ := rkB_E (S := S) (n := n)
  have := (mvB_lt_iff (k := n) (rkB_cl (n := n) hxL μ hμ).1 hDE).2 hμE
  rwa [hBE] at this

/-- **`rkDat μ < x ⇒ rkDat (B_n μ) < B_n x`** for a strongly critical `x < L(ω)` and `μ < ε_{Ω₁+1}`. -/
theorem rkB_dat_lt {n : ℕ} {x μ : Ordinal.{0}} (hx : SC x) (hxL : x < Nc.ncL S ω) (hμE : μ < ggE)
    (h : rkDat μ < x) : rkDat (Bc.bcB S n μ) < Bc.bcB S n x :=
  rkDat_lt_of_cl ((mxB_SC_iff hxL).2 hx) (rkB_cl (n := n) hxL μ ((rkDat_lt_iff hx hμE).1 h)).2

/-- `B_n(μ + 1) = B_n μ + 1` in the domain. -/
theorem rkB_succ {n : ℕ} {μ : Ordinal.{0}} (hD : MvD S μ) : Bc.bcB S n (μ + 1) = Bc.bcB S n μ + 1 := by
  rw [(mvB_add (k := n) hD (rk_one_D (S := S))).2, mwB_one]

/-- **`B_n(Ω₁·μ) = Ω₁·B_n μ`** for a code `μ` over a strongly critical `c < L(ω)`. -/
theorem rkB_Om1mul {n : ℕ} {c : Ordinal.{0}} (hc : SC c) (hcL : c < Nc.ncL S ω) :
    ∀ μ, GgCl c μ → MvD S (Om 1 * μ) ∧ Bc.bcB S n (Om 1 * μ) = Om 1 * Bc.bcB S n μ := by
  intro μ
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμ
  rcases eq_or_ne μ 0 with rfl | hμ0
  · rw [mul_zero, Bc.bcB_zero, mul_zero]; exact ⟨mvD_of_lt ((Lw.lw_L_SC S ω).1), rfl⟩
  obtain ⟨hsub, hlog⟩ := ggDec hc μ hμ
  set g := log ω μ with hg
  have hwg : ω ^ g ≤ μ := opow_log_le_self ω hμ0
  have ht : GgCl c (μ - ω ^ g) := hsub _ (GgCl.opow hc.1 hlog) hwg
  have htlt : μ - ω ^ g < μ := Ph.ph_sub_log_lt hμ0
  have hdec : ω ^ g + (μ - ω ^ g) = μ := Ordinal.add_sub_cancel_of_le hwg
  have hDg := (rkB_cl (n := n) hcL g hlog).1
  have hDt := (rkB_cl (n := n) hcL _ ht).1
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  obtain ⟨hDOg, hBOg⟩ := mvB_add (k := n) hDO hDg
  obtain ⟨hDe, hBe⟩ := Ld.ldB_opow (n := n) hDOg
  obtain ⟨hDw, hBw⟩ := Ld.ldB_opow (n := n) hDg
  obtain ⟨hDt2, hBt2⟩ := IH _ htlt ht
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDe hDt2
  obtain ⟨-, hBμ⟩ := mvB_add (k := n) hDw hDt
  rw [hdec] at hBμ
  have hO : ω ^ (Om 1 : Ordinal.{0}) = Om 1 := Bt.Om1_opow
  have e : Om 1 * μ = ω ^ (Om 1 + g) + Om 1 * (μ - ω ^ g) := by
    conv_lhs => rw [← hdec]
    rw [mul_add, opow_add, hO]
  rw [e]
  refine ⟨hDs, ?_⟩
  rw [hBs, hBe, hBOg, hBO, hBt2, hBμ, hBw, opow_add, hO, mul_add]

/-- **`B_n(u_μ) = u_{B_n μ}`** for a code `μ` over a strongly critical `c < L(ω)`. -/
theorem rkB_Oe {n : ℕ} {c μ : Ordinal.{0}} (hc : SC c) (hcL : c < Nc.ncL S ω) (hμ : GgCl c μ) :
    MvD S (Le.leOe μ) ∧ Bc.bcB S n (Le.leOe μ) = Le.leOe (Bc.bcB S n μ) := by
  obtain ⟨hDK, hBK⟩ := rkB_Om1mul (n := n) hc hcL μ hμ
  obtain ⟨hD, hB⟩ := Ld.ldB_opow (n := n) hDK
  unfold Le.leOe; rw [hB, hBK]; exact ⟨hD, rfl⟩

/-- **`B_n(u_μ·D) = u_{B_n μ}·B_n D`** for a code `μ` over `c_{n+1}` and a countable `D < c_{n+1}`. -/
theorem rkB_Oe_mul {n : ℕ} {μ D : Ordinal.{0}} (hμ : GgCl (Bc.bcC S (n + 1)) μ) (hD1 : D < Om 1)
    (hDc : D < Bc.bcC S (n + 1)) :
    MvD S (Le.leOe μ * D) ∧ Bc.bcB S n (Le.leOe μ * D) = Le.leOe (Bc.bcB S n μ) * Bc.bcB S n D := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hcS : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  rcases eq_or_ne μ 0 with rfl | hμ0
  · rw [Le.leOe_zero, one_mul, Bc.bcB_zero, Le.leOe_zero, one_mul]
    exact ⟨mvD_of_lt (hDc.trans hLw), rfl⟩
  obtain ⟨hDK, hBK⟩ := rkB_Om1mul (n := n) hcS hLw μ hμ
  have h := Le.leB_mulOp2 (n := n) hDK (fun z => z < Om 1 ∧ z < Bc.bcC S (n + 1))
    (fun z hz => mvD_of_lt (hz.2.trans hLw))
    (fun z hz _ => ⟨⟨(log_le_self ω z).trans_lt hz.1, (log_le_self ω z).trans_lt hz.2⟩,
      ⟨(Ordinal.sub_le_self _ _).trans_lt hz.1, (Ordinal.sub_le_self _ _).trans_lt hz.2⟩⟩)
    (fun z hz => hz.1.trans_le (le_mul_left _ (pos_iff_ne_zero.2 hμ0))) D ⟨hD1, hDc⟩
  rw [hBK] at h
  exact h

/-- **`B_n(ψ_{Ω₁}(B + u_μ·D)) = ψ_{Ω₁}(B' + u_{B_n μ}·B_n D)`** for a code `μ` over `c_{n+1}`, an own `B` in the
window and an own `B + u_μ·D` with a countable `D < c_{n+1}`, with `B = α_{n+1} + |r|`, `B' = α_ω + |σ r|` own and
`B_n(ψ_{Ω₁}(B)) = ψ_{Ω₁}(B')`. -/
theorem rkB_psi {n : ℕ} {μ : Ordinal.{0}} (hμ : GgCl (Bc.bcC S (n + 1)) μ)
    {B D : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1)))
    (hlo : Bc.bcC S n ≤ S.psi B (Om 1))
    (hown1 : B + Le.leOe μ * D ∈ S.CSet (B + Le.leOe μ * D) (S.psi (B + Le.leOe μ * D) (Om 1)))
    (hhi : S.psi (B + Le.leOe μ * D) (Om 1) < Bc.bcC S (n + 1)) (hD1 : D < Om 1)
    (hDc : D < Bc.bcC S (n + 1)) :
    ∃ r : Term, bcD S r ∧ B = bcAlpha S (n + 1) + val S r ∧
      bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) ∈
        S.CSet (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r))
          (S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r)) (Om 1)) ∧
      Bc.bcB S n (S.psi B (Om 1)) = S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r)) (Om 1) ∧
      Bc.bcB S n (S.psi (B + Le.leOe μ * D) (Om 1)) =
        S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) + Le.leOe (Bc.bcB S n μ) *
          Bc.bcB S n D) (Om 1) := by
  obtain ⟨hDm, hBm⟩ := rkB_Oe_mul hμ hD1 hDc
  obtain ⟨r, h1, h2, h3, h4, h5⟩ := rdB_psi_baseD hown hlo hown1 hhi hDm
  exact ⟨r, h1, h2, h3, h4, by rw [h5, hBm]⟩

/-- **`σ` maps `u_μ ∣ |r|` to `u_{B_n μ} ∣ |σ r|`** on its domain. -/
theorem rk_dvd_sig {n : ℕ} {μ : Ordinal.{0}} (hμ : GgCl (Bc.bcC S (n + 1)) μ) {r : Term}
    (hr : bcD S r) (h : Le.leOe μ ∣ val S r) :
    Le.leOe (Bc.bcB S n μ) ∣ val S (bcSig (bcPre (n + 1)) bcPreW r) := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  obtain ⟨hDu, hBu⟩ := rkB_Oe (n := n) (Lw.lw_L_SC S _) hLw hμ
  have hle : ∀ v : Term, bcD S v → Le.leOe μ ≤ val S v →
      Le.leOe (Bc.bcB S n μ) ≤ val S (bcSig (bcPre (n + 1)) bcPreW v) := fun v hv hlv => by
    have hDv := mvD_of_term hv
    rw [← mvB_term (k := n) hv, ← hBu]
    exact not_lt.1 fun hlt => absurd ((mvB_lt_iff hDv hDu).1 hlt) (not_lt.2 hlv)
  by_cases h0 : r = Term.zero
  · subst h0; rw [bcSig_zero]; exact dvd_zero _
  have hN' := bc_NF (k := n) hr
  have h0' : bcSig (bcPre (n + 1)) bcPreW r ≠ Term.zero := bcSig_ne_zero h0
  rw [rd_dvd_iff_last (rhU_indec _) hN' h0', rbLast_sig]
  exact hle _ (rbLast_D hr) ((rd_dvd_iff_last (rhU_indec μ) hr.1 h0).1 h)

theorem rk_dvd_alpha {μ : Ordinal.{0}} (hμ : μ ≤ ggE) (j : ℕ) : Le.leOe μ ∣ bcAlpha S j := by
  have h1 : Le.leOe μ ∣ Om (ω : Ordinal.{0}) :=
    rk_dvd_eps hμ (Low.opow_eq_self_of_SC (SC_Om omega0_pos.ne')) (Om_lt_Om.2 one_lt_omega0)
  have h2 : Le.leOe μ ∣ Nc.ncPp S := rk_dvd_eps hμ (Low.opow_eq_self_of_SC (Nc.ncPp_SC S)) rb_Om1_lt_Pp
  exact dvd_add (dvd_add h1 h1) (dvd_mul_of_dvd_left h2 _)

theorem rk_dvd_alphaW {μ : Ordinal.{0}} (hμ : μ ≤ ggE) : Le.leOe μ ∣ bcAlphaW S := by
  have h1 : Le.leOe μ ∣ Om (ω : Ordinal.{0}) :=
    rk_dvd_eps hμ (Low.opow_eq_self_of_SC (SC_Om omega0_pos.ne')) (Om_lt_Om.2 one_lt_omega0)
  refine dvd_add (dvd_add h1 h1) ?_
  have hE : ω ^ Nc.ncPp S = Nc.ncPp S := Low.opow_eq_self_of_SC (Nc.ncPp_SC S)
  have h2 : Le.leOe μ ∣ Nc.ncPp S := rk_dvd_eps hμ hE rb_Om1_lt_Pp
  have hI : Indec (ω ^ (Nc.ncPp S + 1)) :=
    indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩
  refine rh_dvd_of_indec μ hI ((Ordinal.le_of_dvd (inE_indec hE).ne_zero h2).trans ?_)
  conv_lhs => rw [← hE]
  exact opow_le_opow_right omega0_pos le_self_add

/-- **`u_μ ∣ B` gives `u_{B_n μ} ∣ B'`** for `B = α_{n+1} + |r|`, `B' = α_ω + |σ r|`, `μ < ε_{Ω₁+1}` a code over
`c_{n+1}`. -/
theorem rkB_dvd {n : ℕ} {μ : Ordinal.{0}} (hμE : μ < ggE) (hμ : GgCl (Bc.bcC S (n + 1)) μ)
    {B : Ordinal.{0}} {r : Term} (hr : bcD S r)
    (hB : B = bcAlpha S (n + 1) + val S r) (h : Le.leOe μ ∣ B) :
    Le.leOe (Bc.bcB S n μ) ∣ bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  rw [hB, rd_dvd_add_left (rk_dvd_alpha hμE.le _)] at h
  rw [rd_dvd_add_left (rk_dvd_alphaW (rkB_lt_E hLw hμ hμE).le)]
  exact rk_dvd_sig hμ hr h

end Googology.Trans.PoR.InaccPsi.R2.Rk
