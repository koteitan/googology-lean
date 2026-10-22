import Googology.Trans.PoR.InaccPsi.R2.RhMove
import Googology.Trans.PoR.InaccPsi.R2.RiPsi

/-!
# `B_n` at a level `μ < Ω₁·Ω₁`: the image level, `u_μ`, `ψ_{Ω₁}(B + u_μ·D)`, and the reach `lqL`

`B_n = Bc.bcB S n`, `c_n = L(n+1) = Bc.bcC S n`, `u_μ = Ω₁^μ = Le.leOe μ`, `σ = bcSig (bcPre (n+1)) bcPreW`.

* `riLB S n μ = Ω₁·B_n(μ/Ω₁) + B_n(μ mod Ω₁)` (**the image level**); `riLB_lvl`, `riLB_lt`, `riLB_dat`
  (`riDat (riLB n μ) = B_n(riDat μ)`), `riLB_succ`, `riP_LB` (`Φ_{riLB n μ} = H^{B_n(μ/Ω₁)}_{B_n(μ mod Ω₁)}`);
* `riB_Om1mul`, `riB_Oe` (**`B_n(u_μ) = u_{riLB n μ}`**), `riB_Oe_mul` (**`B_n(u_μ·D) = u_{riLB n μ}·B_n D`**), for
  `riDat μ < c_{n+1}` (`D` countable, `D < c_{n+1}`);
* `riB_psi` (**`B_n(ψ_{Ω₁}(B + u_μ·D)) = ψ_{Ω₁}(B' + u_{riLB n μ}·B_n D)`**, `B = α_{n+1} + |r|`, `B' = α_ω + |σ r|`),
  `ri_u_le_sig`, `ri_dvd_sig`, `riB_dvd` (**`u_μ ∣ B` gives `u_{riLB n μ} ∣ B'`**);
* `riB_log` (`B_n(log_ω γ) = log_ω(B_n γ)`), `riB_lqL` (**`B_n(lqL(x, γ, β)) = lqL(B_n x, B_n γ, B_n β)`** for an
  `ε`-number `x < L(ω)`, `γ, β < x`).

No new axiom.  New definition: `riLB`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ri

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Lq
  Googology.Trans.PoR.InaccPsi.R2.Rb Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rh
  Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}}

/-- **The image level** `Ω₁·B_n(μ/Ω₁) + B_n(μ mod Ω₁)`. -/
noncomputable def riLB (S : InaccSeq.{0}) (n : ℕ) (μ : Ordinal.{0}) : Ordinal.{0} :=
  Om 1 * Bc.bcB S n (μ / Om 1) + Bc.bcB S n (μ % Om 1)

theorem ri_L_lt_Om1 (S : InaccSeq.{0}) : Nc.ncL S ω < Om 1 := InaccSeq.psi_lt Low.InR_Om_one _

theorem ri_one_lt_L (S : InaccSeq.{0}) : (1 : Ordinal.{0}) < Nc.ncL S ω := by
  have := Mw.mw_nat_lt_L (S := S) 1; rwa [Nat.cast_one] at this

/-- `B_n` is monotone below `L(ω)`. -/
theorem riB_mono {n : ℕ} {a b : Ordinal.{0}} (hb : b < Nc.ncL S ω) (h : a ≤ b) :
    Bc.bcB S n a ≤ Bc.bcB S n b := by
  rcases h.lt_or_eq with h' | h'
  · exact ((Bc.bcB_lt_iff (h'.trans hb) hb).2 h').le
  · rw [h']

section Lvl

variable {n : ℕ} {μ : Ordinal.{0}} (hμc : riDat μ < Bc.bcC S (n + 1))
include hμc

theorem riLB_dL : riDat μ < Nc.ncL S ω := hμc.trans (Bc.bcC_lt S (n + 1))

theorem riLB_qL : μ / Om 1 < Nc.ncL S ω := (riDat_div_le μ).trans_lt (riLB_dL hμc)

theorem riLB_rL : μ % Om 1 < Nc.ncL S ω := (riDat_mod_le μ).trans_lt (riLB_dL hμc)

theorem riLB_q_lt : Bc.bcB S n (μ / Om 1) < Om 1 := rhB_lt_Om1 ((riDat_div_le μ).trans_lt hμc)

theorem riLB_r_lt : Bc.bcB S n (μ % Om 1) < Om 1 := rhB_lt_Om1 ((riDat_mod_le μ).trans_lt hμc)

theorem riLB_lvl : riLB S n μ / Om 1 = Bc.bcB S n (μ / Om 1) ∧ riLB S n μ % Om 1 = Bc.bcB S n (μ % Om 1) :=
  ri_lvl (riLB_r_lt hμc)

theorem riLB_lt : riLB S n μ < Om 1 * Om 1 := by
  unfold riLB
  calc Om 1 * Bc.bcB S n (μ / Om 1) + Bc.bcB S n (μ % Om 1)
      < Om 1 * Bc.bcB S n (μ / Om 1) + Om 1 := (add_lt_add_iff_left _).2 (riLB_r_lt hμc)
    _ = Om 1 * (Bc.bcB S n (μ / Om 1) + 1) := by rw [mul_add_one]
    _ ≤ Om 1 * Om 1 := mul_le_mul_right (Order.add_one_le_of_lt (riLB_q_lt hμc)) _

theorem riLB_dat : riDat (riLB S n μ) = Bc.bcB S n (riDat μ) := by
  unfold riLB; rw [riDat_lvl (riLB_r_lt hμc)]
  unfold riDat
  rcases le_total (μ / Om 1) (μ % Om 1) with h | h
  · rw [max_eq_right h, max_eq_right (riB_mono (riLB_rL hμc) h)]
  · rw [max_eq_left h, max_eq_left (riB_mono (riLB_qL hμc) h)]

theorem riP_LB : riP (riLB S n μ) = riH (Bc.bcB S n (μ / Om 1)) (Bc.bcB S n (μ % Om 1)) :=
  riP_lvl (riLB_r_lt hμc)

/-- `riDat (riLB n μ) < B_n x` for `riDat μ < x < L(ω)`. -/
theorem riLB_dat_lt {x : Ordinal.{0}} (hx : riDat μ < x) (hxL : x < Nc.ncL S ω) :
    riDat (riLB S n μ) < Bc.bcB S n x := by
  rw [riLB_dat hμc]; exact (Bc.bcB_lt_iff (hx.trans hxL) hxL).2 hx

/-- **`riLB n (μ + 1) = riLB n μ + 1`.** -/
theorem riLB_succ : riLB S n (μ + 1) = riLB S n μ + 1 := by
  have hr1 : μ % Om 1 + 1 < Om 1 := (Om_isSuccLimit one_ne_zero).add_one_lt (ri_mod_lt μ)
  have he : μ + 1 = Om 1 * (μ / Om 1) + (μ % Om 1 + 1) := by rw [← add_assoc, ri_div_mod]
  have hl := ri_lvl (a := μ / Om 1) hr1
  rw [← he] at hl
  unfold riLB
  rw [hl.1, hl.2, Bc.bcB_add (riLB_rL hμc) (ri_one_lt_L S), mwB_one, add_assoc]

/-- `B_n(Ω₁·μ) = Ω₁·riLB n μ`. -/
theorem riB_Om1mul : Mv.MvD S (Om 1 * μ) ∧ Bc.bcB S n (Om 1 * μ) = Om 1 * riLB S n μ := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hqc : μ / Om 1 < Bc.bcC S (n + 1) := (riDat_div_le μ).trans_lt hμc
  have hrc : μ % Om 1 < Bc.bcC S (n + 1) := (riDat_mod_le μ).trans_lt hμc
  have hq1 : μ / Om 1 < Om 1 := hqc.trans (hLw.trans (ri_L_lt_Om1 S))
  have hr1 : μ % Om 1 < Om 1 := ri_mod_lt μ
  obtain ⟨hDO, hBO⟩ := Mv.mvB_Om1 (S := S) (k := n)
  obtain ⟨hDK, hBK⟩ := Mv.mvB_add (S := S) (k := n) hDO hDO
  rw [hBO] at hBK
  have hP := Le.leB_mulOp2 (n := n) hDK (fun z => z < Om 1 ∧ z < Bc.bcC S (n + 1))
    (fun z hz => Mv.mvD_of_lt (hz.2.trans hLw))
    (fun z hz _ => ⟨⟨(log_le_self ω z).trans_lt hz.1, (log_le_self ω z).trans_lt hz.2⟩,
      ⟨(Ordinal.sub_le_self _ _).trans_lt hz.1, (Ordinal.sub_le_self _ _).trans_lt hz.2⟩⟩)
    (fun z hz => hz.1.trans_le le_self_add) (μ / Om 1) ⟨hq1, hqc⟩
  rw [hBK] at hP
  obtain ⟨hD2, hB2⟩ := Le.leB_mulOm1 (S := S) (n := n) hr1 hrc
  obtain ⟨hD3, hB3⟩ := Mv.mvB_add (S := S) (k := n) hP.1 hD2
  have hE : ω ^ (Om 1 : Ordinal.{0}) = Om 1 := Bt.Om1_opow
  have e : Om 1 * μ = ω ^ (Om 1 + Om 1) * (μ / Om 1) + Om 1 * (μ % Om 1) := by
    rw [opow_add, hE]
    conv_lhs => rw [← ri_div_mod μ]
    rw [mul_add, mul_assoc]
  rw [e]
  refine ⟨hD3, ?_⟩
  rw [hB3, hP.2, hB2]
  unfold riLB
  rw [opow_add, hE, mul_add, mul_assoc]

/-- **`B_n(u_μ) = u_{riLB n μ}`.** -/
theorem riB_Oe : Mv.MvD S (Le.leOe μ) ∧ Bc.bcB S n (Le.leOe μ) = Le.leOe (riLB S n μ) := by
  obtain ⟨hDK, hBK⟩ := riB_Om1mul hμc
  obtain ⟨hD, hB⟩ := Ld.ldB_opow (n := n) hDK
  unfold Le.leOe; rw [hB, hBK]; exact ⟨hD, rfl⟩

/-- **`B_n(u_μ·D) = u_{riLB n μ}·B_n D`** for `1 ≤ μ`, a countable `D < c_{n+1}`. -/
theorem riB_Oe_mul (hμ1 : 1 ≤ μ) {D : Ordinal.{0}} (hD1 : D < Om 1) (hDc : D < Bc.bcC S (n + 1)) :
    Mv.MvD S (Le.leOe μ * D) ∧ Bc.bcB S n (Le.leOe μ * D) = Le.leOe (riLB S n μ) * Bc.bcB S n D := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  obtain ⟨hDK, hBK⟩ := riB_Om1mul hμc
  have h := Le.leB_mulOp2 (n := n) hDK (fun z => z < Om 1 ∧ z < Bc.bcC S (n + 1))
    (fun z hz => Mv.mvD_of_lt (hz.2.trans hLw))
    (fun z hz _ => ⟨⟨(log_le_self ω z).trans_lt hz.1, (log_le_self ω z).trans_lt hz.2⟩,
      ⟨(Ordinal.sub_le_self _ _).trans_lt hz.1, (Ordinal.sub_le_self _ _).trans_lt hz.2⟩⟩)
    (fun z hz => hz.1.trans_le (le_mul_left _ (Order.one_le_iff_pos.1 hμ1))) D ⟨hD1, hDc⟩
  rw [hBK] at h
  exact h

end Lvl

/-! ## `ψ_{Ω₁}(B + u_μ·D)` and `σ` -/

/-- **`B_n(ψ_{Ω₁}(B + u_μ·D)) = ψ_{Ω₁}(B' + u_{riLB n μ}·B_n D)`** (`1 ≤ μ`, `riDat μ < c_{n+1}`) for an own `B` in
the window and an own `B + u_μ·D` with a countable `D < c_{n+1}`, with `B = α_{n+1} + |r|`, `B' = α_ω + |σ r|` own and
`B_n(ψ_{Ω₁}(B)) = ψ_{Ω₁}(B')`. -/
theorem riB_psi {n : ℕ} {μ : Ordinal.{0}} (hμ1 : 1 ≤ μ) (hμc : riDat μ < Bc.bcC S (n + 1))
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
        S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) + Le.leOe (riLB S n μ) *
          Bc.bcB S n D) (Om 1) := by
  obtain ⟨hDm, hBm⟩ := riB_Oe_mul hμc hμ1 hD1 hDc
  obtain ⟨r, h1, h2, h3, h4, h5⟩ := rdB_psi_baseD hown hlo hown1 hhi hDm
  exact ⟨r, h1, h2, h3, h4, by rw [h5, hBm]⟩

/-- **`σ` maps `u_μ ≤ |v|` to `u_{riLB n μ} ≤ |σ v|`** on its domain. -/
theorem ri_u_le_sig {n : ℕ} {μ : Ordinal.{0}} (hμc : riDat μ < Bc.bcC S (n + 1)) {v : Term}
    (hv : bcD S v) (h : Le.leOe μ ≤ val S v) :
    Le.leOe (riLB S n μ) ≤ val S (bcSig (bcPre (n + 1)) bcPreW v) := by
  obtain ⟨hDu, hBu⟩ := riB_Oe (n := n) hμc
  have hDv := Mv.mvD_of_term hv
  rw [← Mv.mvB_term (k := n) hv, ← hBu]
  exact not_lt.1 fun hlt => absurd ((Mv.mvB_lt_iff hDv hDu).1 hlt) (not_lt.2 h)

/-- **`σ` maps `u_μ ∣ |r|` to `u_{riLB n μ} ∣ |σ r|`** on its domain. -/
theorem ri_dvd_sig {n : ℕ} {μ : Ordinal.{0}} (hμc : riDat μ < Bc.bcC S (n + 1)) {r : Term}
    (hr : bcD S r) (h : Le.leOe μ ∣ val S r) :
    Le.leOe (riLB S n μ) ∣ val S (bcSig (bcPre (n + 1)) bcPreW r) := by
  by_cases h0 : r = Term.zero
  · subst h0; rw [bcSig_zero]; exact dvd_zero _
  have hN' := bc_NF (k := n) hr
  have h0' : bcSig (bcPre (n + 1)) bcPreW r ≠ Term.zero := bcSig_ne_zero h0
  rw [rd_dvd_iff_last (rhU_indec _) hN' h0', rbLast_sig]
  exact ri_u_le_sig hμc (rbLast_D hr) ((rd_dvd_iff_last (rhU_indec μ) hr.1 h0).1 h)

theorem ri_dvd_alpha {μ : Ordinal.{0}} (hμ : μ ≤ Om 1 * Om 1) (j : ℕ) : Le.leOe μ ∣ bcAlpha S j := by
  have h1 : Le.leOe μ ∣ Om (ω : Ordinal.{0}) :=
    ri_dvd_eps hμ (Low.opow_eq_self_of_SC (SC_Om omega0_pos.ne')) (Om_lt_Om.2 one_lt_omega0)
  have h2 : Le.leOe μ ∣ Nc.ncPp S := ri_dvd_eps hμ (Low.opow_eq_self_of_SC (Nc.ncPp_SC S)) rb_Om1_lt_Pp
  exact dvd_add (dvd_add h1 h1) (dvd_mul_of_dvd_left h2 _)

theorem ri_dvd_alphaW {μ : Ordinal.{0}} (hμ : μ ≤ Om 1 * Om 1) : Le.leOe μ ∣ bcAlphaW S := by
  have h1 : Le.leOe μ ∣ Om (ω : Ordinal.{0}) :=
    ri_dvd_eps hμ (Low.opow_eq_self_of_SC (SC_Om omega0_pos.ne')) (Om_lt_Om.2 one_lt_omega0)
  refine dvd_add (dvd_add h1 h1) ?_
  have hE : ω ^ Nc.ncPp S = Nc.ncPp S := Low.opow_eq_self_of_SC (Nc.ncPp_SC S)
  have h2 : Le.leOe μ ∣ Nc.ncPp S := ri_dvd_eps hμ hE rb_Om1_lt_Pp
  have hI : Indec (ω ^ (Nc.ncPp S + 1)) :=
    indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩
  refine rh_dvd_of_indec μ hI ((Ordinal.le_of_dvd (inE_indec hE).ne_zero h2).trans ?_)
  conv_lhs => rw [← hE]
  exact opow_le_opow_right omega0_pos le_self_add

/-- **`u_μ ∣ B` gives `u_{riLB n μ} ∣ B'`** for `B = α_{n+1} + |r|`, `B' = α_ω + |σ r|`. -/
theorem riB_dvd {n : ℕ} {μ : Ordinal.{0}} (hμΩ : μ ≤ Om 1 * Om 1) (hμc : riDat μ < Bc.bcC S (n + 1))
    (hLB : riLB S n μ ≤ Om 1 * Om 1) {B : Ordinal.{0}} {r : Term} (hr : bcD S r)
    (hB : B = bcAlpha S (n + 1) + val S r) (h : Le.leOe μ ∣ B) :
    Le.leOe (riLB S n μ) ∣ bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) := by
  rw [hB, rd_dvd_add_left (ri_dvd_alpha hμΩ _)] at h
  rw [rd_dvd_add_left (ri_dvd_alphaW hLB)]
  exact ri_dvd_sig hμc hr h

/-! ## `B_n` and the reach `lqL` -/

/-- **`B_n(log_ω γ) = log_ω(B_n γ)`** for `γ < L(ω)`. -/
theorem riB_log {n : ℕ} {γ : Ordinal.{0}} (hγ : γ < Nc.ncL S ω) :
    Bc.bcB S n (log ω γ) = log ω (Bc.bcB S n γ) := by
  have hLSC := Lw.lw_L_SC S ω
  rcases eq_or_ne γ 0 with rfl | hγ0
  · rw [log_zero_right, Bc.bcB_zero, log_zero_right]
  set g := log ω γ with hg
  have hgL : g < Nc.ncL S ω := (log_le_self ω γ).trans_lt hγ
  have hg1L : g + 1 < Nc.ncL S ω := hLSC.add_one_lt hgL
  have hopL : ∀ a, a < Nc.ncL S ω → ω ^ a < Nc.ncL S ω := fun a ha => by
    have := hLSC.2 0 hLSC.1 a ha; rwa [veblen_zero_apply] at this
  obtain ⟨-, h1⟩ := Ld.ldB_opow (S := S) (n := n) (Mv.mvD_of_lt hgL)
  obtain ⟨-, h2⟩ := Ld.ldB_opow (S := S) (n := n) (Mv.mvD_of_lt hg1L)
  rw [Bc.bcB_add hgL (ri_one_lt_L S), mwB_one] at h2
  have hlo : ω ^ g ≤ γ := opow_log_le_self ω hγ0
  have hhi : γ < ω ^ (g + 1) := lt_opow_succ_log_self one_lt_omega0 γ
  have hBγ0 : Bc.bcB S n γ ≠ 0 := by
    intro e
    have := (Bc.bcB_lt_iff (k := n) (lt_of_le_of_lt zero_le hγ) hγ).2 (pos_iff_ne_zero.2 hγ0)
    rw [Bc.bcB_zero, e] at this
    exact lt_irrefl _ this
  refine ((log_eq_iff one_lt_omega0 hBγ0 _).2 ⟨?_, ?_⟩).symm
  · rw [← h1]; exact riB_mono hγ hlo
  · rw [← h2]; exact (Bc.bcB_lt_iff hγ (hopL _ hg1L)).2 hhi

/-- **`B_n(lqL(x, γ, β)) = lqL(B_n x, B_n γ, B_n β)`** for an `ε`-number `x < L(ω)` and `1 ≤ γ < x`, `β < x`. -/
theorem riB_lqL {n : ℕ} {x γ β : Ordinal.{0}} (hE : InE x) (hxL : x < Nc.ncL S ω) (hγ1 : 1 ≤ γ) (hγx : γ < x)
    (hβx : β < x) :
    Bc.bcB S n (lqL x γ β) = lqL (Bc.bcB S n x) (Bc.bcB S n γ) (Bc.bcB S n β) := by
  have hLSC := Lw.lw_L_SC S ω
  have hLI : Indec (Nc.ncL S ω) := lq_SC_indec hLSC
  have hLE : InE (Nc.ncL S ω) := Low.opow_eq_self_of_SC hLSC
  have hγL : γ < Nc.ncL S ω := hγx.trans hxL
  have hβL : β < Nc.ncL S ω := hβx.trans hxL
  have hmulL : ∀ a b, a < Nc.ncL S ω → b < Nc.ncL S ω → a * b < Nc.ncL S ω := fun a b ha hb =>
    InE.mul_lt hLE ha hb
  have hopL : ∀ a, a < Nc.ncL S ω → ω ^ a < Nc.ncL S ω := fun a ha => by
    have := hLSC.2 0 hLSC.1 a ha; rwa [veblen_zero_apply] at this
  have hγ0 : γ ≠ 0 := (lt_of_lt_of_le zero_lt_one hγ1).ne'
  set g := log ω γ with hg
  have hgL : g < Nc.ncL S ω := (log_le_self ω γ).trans_lt hγL
  have hBg : Bc.bcB S n g = log ω (Bc.bcB S n γ) := riB_log hγL
  have hxg : x * ω ^ g < Nc.ncL S ω := hmulL _ _ hxL (hopL _ hgL)
  have hY : Bc.bcB S n (x * x * ω ^ g) = Bc.bcB S n x * Bc.bcB S n x * ω ^ log ω (Bc.bcB S n γ) := by
    rw [mul_assoc, mxB_mul hE _ (hmulL _ _ hxL hxg), mxB_mul_opow hE hxg, hBg, mul_assoc]
  have hYL : x * x * ω ^ g < Nc.ncL S ω := by rw [mul_assoc]; exact hmulL _ _ hxL hxg
  have hx2L : x * 2 < Nc.ncL S ω := by rw [mul_two_eq]; exact hLI.add_lt hxL hxL
  have hcL : x * 2 + g < Nc.ncL S ω := hLI.add_lt hx2L hgL
  have hc0 : x * 2 + g ≠ 0 := (lt_of_lt_of_le (mul_pos hE.pos (by norm_num)) le_self_add).ne'
  have hlg : Bc.bcB S n (lg (x * 2 + g)) = lg (Bc.bcB S n x * 2 + log ω (Bc.bcB S n γ)) := by
    rw [← Tp.tpLgB hc0 hcL, Bc.bcB_add hx2L hgL, hBg, mul_two_eq, Bc.bcB_add hxL hxL, mul_two_eq]
  have hxγL : x * γ < Nc.ncL S ω := hmulL _ _ hxL hγL
  have hXinL : x * γ + β < Nc.ncL S ω := hLI.add_lt hxγL hβL
  have hXL : x * (x * γ + β) < Nc.ncL S ω := hmulL _ _ hxL hXinL
  have hX : Bc.bcB S n (x * (x * γ + β)) =
      Bc.bcB S n x * (Bc.bcB S n x * Bc.bcB S n γ + Bc.bcB S n β) := by
    rw [mxB_mul hE _ hXL, Bc.bcB_add hxγL hβL, mxB_mul hE _ hxγL]
  have hYX : x * x * ω ^ g ≤ x * (x * γ + β) := by
    rw [mul_assoc]
    exact mul_le_mul_right ((mul_le_mul_right (opow_log_le_self ω hγ0) x).trans le_self_add) x
  have hdL : x * (x * γ + β) - x * x * ω ^ g < Nc.ncL S ω := (Ordinal.sub_le_self _ _).trans_lt hXL
  have hsub : Bc.bcB S n (x * (x * γ + β) - x * x * ω ^ g) =
      Bc.bcB S n (x * (x * γ + β)) - Bc.bcB S n (x * x * ω ^ g) := by
    have h := Bc.bcB_add (k := n) hYL hdL
    rw [Ordinal.add_sub_cancel_of_le hYX] at h
    rw [h, Ordinal.add_sub_cancel]
  have hlgL : lg (x * 2 + g) < Nc.ncL S ω := (lg_le hc0).trans_lt hcL
  unfold lqL
  rw [← hg, Bc.bcB_add (hLI.add_lt hYL hlgL) hdL, Bc.bcB_add hYL hlgL, hY, hlg, hsub, hX, hY]

end Googology.Trans.PoR.InaccPsi.R2.Ri
