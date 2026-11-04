import Googology.Trans.PoR.InaccPsi.R2.ZeTerm
import Googology.Trans.PoR.InaccPsi.R2.ZeName
import Googology.Trans.PoR.InaccPsi.R2.YzRng
import Googology.Trans.PoR.InaccPsi.R2.TeCode

/-!
# The gap restarts: `Ye.YeGapRng` (every code) from CapV in `(L(ω), L(ω+1))`

Notation as in `R2.YeGap`, `R2.ZeTerm`: a gap point `a` of a far window `(n, λ, λ')` at a cofinal index `p`
(`Ye.YeGapPt`: `B_n q ≤ a < B_n p` for `q < p`), `σ = bcSig (bcPre (n+1)) bcPreW` the term map of `B_n`,
`α_{n+1} = A_{Ω_ω+P'·(n+1)}`, `α_ω = A_{Ω_ω+P'·ω}`, `cap(μ) = P(η_μ + ω^{e(η_μ)})`.

* `zeGap_win` (**the cap window of `B_n p`**): at a restart `p = ρ_κ` there are `q < p` and `x ≤ B_n q` such that
  every restart `ρ_μ ∈ (x, B_n p)` has `cap(μ) ≤ B_n p`.  Proof: the good name `η_κ = β + ω^E` (`ω^E ∣ β`);
  `ι(β) < κ` (`Ze.zeIota_prefix_lt`), so a good name `ζ` in `[β, η_κ)` with `c_n ≤ P(ζ) < p` exists; the argument
  term of `P(η_κ)` is `α_{n+1}` followed by `ρ` (`Ze.zeB_term`), `ρ = I + L` with `L` its last summand
  (`Ze.zeVal_split`); `|L| ∣ α_{n+1} + |I|`, and `A_{η_κ} = A_β + θ·ω^E` force `|L| = θ·ω^E`,
  `α_{n+1} + |I| = A_β` (`Ze.ze_cancel_last`); `σ` keeps the split: `B_n p = P(β' + ω^d)` with
  `A_{β'} = α_ω + |σ(I)|`; `x = P(β') ≤ B_n P(ζ)` because `|I| ≤ |ρ_ζ|` and `σ` is monotone (`Bc.bc_lt_iff`);
  a restart `ρ_μ ∈ (x, B_n p)` has its good name in `(β', β' + ω^d)`, so `cap(μ) ≤ P(β' + ω^d) = B_n p`.
* `zeGapRng` (**`Ye.YeGapRng S`**, under ENUM-REACH and CapV in `(L(ω), L(ω+1))`): a gap restart
  `ρ_{l₀}` lies above `x`, it is a range restart above `L(ω)` (`Te.teCode_hi_iff`), and CapV gives
  `r(l₀) < cap(l₀) ≤ B_n p`.  `zeGapRngHi` (**`Yz.YzGapRngHi S`**, the leaf `skGapRngHi`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ze

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Bt

variable {S : InaccSeq.{0}}

/-- **The cap window of `B_n p`** at a restart `p = ρ_κ` of a gap configuration. -/
theorem zeGap_win {n : ℕ} {l l' p a κ : Ordinal.{0}} (hP : Ye.YeGapPt S n l l' p a)
    (hκ : IsRestartIdx κ) (hpκ : p = upsilon κ) :
    ∃ x q, q < p ∧ x ≤ Bc.bcB S n q ∧ ∀ μ, IsRestartIdx μ → x < upsilon μ →
      upsilon μ < Bc.bcB S n p → cdCapB S μ ≤ Bc.bcB S n p := by
  obtain ⟨hW, hfar, hp, -, -, -, -, -⟩ := hP
  obtain ⟨hpC, -, -, hδp, -⟩ := Xw.xwWin hW hfar hp
  have hcp : Bc.bcC S n < p := hW.2.1.trans ((cdRho_lt_delta l).trans hδp)
  set P' := Nc.ncPp S with hP'
  set N := Om ω + P' * ((n + 1 : ℕ) : Ordinal.{0}) with hN
  have hcN : Bc.bcC S n = Pv S N := Lw.lw_L_eq S _
  have hcN1 : Bc.bcC S (n + 1) = Pv S (N + P') := by
    have : N + P' = Om ω + P' * ((n + 1 + 1 : ℕ) : Ordinal.{0}) := by
      rw [hN, add_assoc, ← mul_add_one]; push_cast; rfl
    rw [this]; exact Lw.lw_L_eq S _
  have hlT : upsilon κ < Pv S (N + P') := hpκ ▸ hcN1 ▸ hpC
  -- the good name of `κ`
  obtain ⟨hg, hικ, -, hpv⟩ := cdEta_pv_spec (S := S) hκ.1 hlT
  set ηκ := cdEta S κ with hηκ
  have hη0 : ηκ ≠ 0 := by
    intro h0
    rw [h0, iota_zero] at hικ
    exact (ri_lim hκ).succ_ne 0 (by rw [succ_eq_add_one, zero_add]; exact hικ)
  obtain ⟨β, hdec, hdvd⟩ := cdExp_decomp hη0
  set E := cdExp ηκ with hE
  have hιβ : iota S β < κ := by
    have := zeIota_prefix_lt hdvd (hdec ▸ hg)
    rwa [← hdec, hικ] at this
  have hpP : Pv S ηκ = p := hpv.trans hpκ.symm
  -- `N < η_κ < N + P'`
  have hNη : N < ηκ := by
    by_contra h; push Not at h
    have := Pv_mono (S := S) h
    rw [hpP, ← hcN] at this
    exact absurd hcp (not_lt.2 this)
  have hηNP : ηκ < N + P' := by
    by_contra h; push Not at h
    have := Pv_mono (S := S) h
    rw [hpP, ← hcN1] at this
    exact absurd hpC (not_lt.2 this)
  -- a good name `ζ ∈ [β, η_κ)` with `c_n ≤ P(ζ)`
  have hιN : iota S N < κ := by
    have h1 : upsilon (iota S N) = Pv S N := ups_iota S N
    have h2 : upsilon (iota S N) < upsilon κ := by rw [h1, ← hcN, ← hpκ]; exact hcp
    exact upsilon_normal.strictMono.lt_iff_lt.1 h2
  set ξ := max (iota S β) (iota S N) + 1 with hξ
  have hξκ : ξ < κ := by
    rw [hξ, ← succ_eq_add_one]; exact (ri_lim hκ).succ_lt (max_lt hιβ hιN)
  obtain ⟨hgg, hιg, -⟩ := cdEta_spec (S := S) (Order.one_le_iff_ne_zero.2 (by rw [hξ]; exact
    (add_pos_of_nonneg_of_pos zero_le one_pos).ne')) (hξκ.trans_eq hικ.symm)
  set ζg := cdEta S ξ with hζg
  have hPg : Pv S ζg = upsilon ξ := by
    calc Pv S ζg = upsilon (iota S ζg) := (ups_iota S ζg).symm
      _ = upsilon ξ := by rw [hιg]
  have hβg : β ≤ ζg := by
    by_contra h; push Not at h
    have h1 := iota_mono (S := S) β ζg h.le
    rw [hιg] at h1
    exact absurd (h1.trans_lt (Order.lt_add_one_iff.2 (le_max_left _ _))) (lt_irrefl _)
  have hcg : Bc.bcC S n ≤ Pv S ζg := by
    rw [hPg, hcN]
    calc Pv S N = upsilon (iota S N) := (ups_iota S N).symm
      _ ≤ upsilon ξ := upsilon_normal.monotone ((le_max_right _ _).trans le_self_add)
  have hgp : Pv S ζg < p := by
    rw [hPg, hpκ]; exact upsilon_normal.strictMono hξκ
  -- the argument terms
  obtain ⟨ρ1, hD1, hA1, hB1⟩ := zeB_term hg (hpP ▸ hcp.le) (hpP ▸ hpC)
  obtain ⟨ρg, hDg, hAg, hBg⟩ := zeB_term hgg hcg (hgp.trans hpC)
  have hα : bcAlpha S (n + 1) = ConjT.Aη S N := by
    rw [Sf.sfAlpha_eq]
  -- `|ρ1| = θ·ζκ`
  obtain ⟨ζκ, hζκ⟩ := exists_add_of_le hNη.le
  have hζκ0 : ζκ ≠ 0 := by rintro rfl; rw [add_zero] at hζκ; exact (ne_of_gt hNη) hζκ
  have hζP : ζκ < P' := by
    have := hηNP; rw [hζκ] at this; exact (add_lt_add_iff_left N).1 this
  have hvρ : val S ρ1 = ConjT.th S * ζκ := by
    have e1 : ConjT.Aη S ηκ = ConjT.Aη S N + ConjT.th S * ζκ := by rw [hζκ, Bt.A_add]
    rw [hA1, hα] at e1
    exact add_left_cancel e1
  have hρ0 : ρ1 ≠ Term.zero := by
    rintro rfl
    have : (0 : Ordinal.{0}) = ConjT.th S * ζκ := by rw [← hvρ]; rfl
    exact (mul_pos (ConjT.SC_th S).1 (pos_iff_ne_zero.2 hζκ0)).ne' this.symm
  -- the split at the last summand
  have hsplit : val S ρ1 = val S (zeInit ρ1) + val S (zeLast ρ1) :=
    zeVal_split (S := S) (fun t => t) (fun _ _ => rfl) rfl ρ1
  obtain ⟨hLN, hLP, -⟩ := zeLast_spec (S := S) hD1.1 hρ0
  have hPdvd : val S (zeLast ρ1) ∣ val S (zeInit ρ1) := zeLast_dvd hD1.1 hρ0
  have hPpr := isPrincipal_val S hLN hLP
  have hP0 : val S (zeLast ρ1) ≠ 0 := val_ne_zero S hLN (NF.ne_zero_of_isPrin hLP)
  obtain ⟨g, hgv⟩ := exists_opow_of_principal hPpr hP0
  -- `ω^g ∣ α_{n+1}`
  have hθo : ω ^ ConjT.th S = ConjT.th S := Sf.sfTh_opow S
  have hPo : ω ^ P' = P' := Lw.lw_Pp_opow S
  have hθP : ConjT.th S * P' = ω ^ (ConjT.th S + P') := by
    conv_lhs => rw [← hθo, ← hPo]
    rw [← opow_add]
  have hWo : ω ^ Om (ω : Ordinal.{0}) = Om ω := Low.opow_eq_self_of_SC (SC_Om omega0_ne_zero)
  have h12 : (1 + 1 : Ordinal.{0}) < ω := by
    rw [one_add_one_eq_two]; exact_mod_cast natCast_lt_omega0 2
  have hPW : P' < Om ω := (cdPp_lt_Om2 S).trans (Om_lt_Om.2 h12)
  have hθPW : ConjT.th S + P' < Om ω :=
    (SC_Om omega0_ne_zero).isPrincipal (Sf.sfTh_lt_OmW S) hPW
  have hgl : g < ConjT.th S + P' := by
    have h1 : ω ^ g ≤ val S ρ1 := by rw [← hgv, hsplit]; exact le_add_self
    have h2 : val S ρ1 < ConjT.th S * P' := by
      rw [hvρ]; exact (mul_lt_mul_iff_right₀ (ConjT.SC_th S).1).2 hζP
    rw [hθP] at h2
    exact (opow_lt_opow_iff_right one_lt_omega0).1 (h1.trans_lt h2)
  have hgW : ω ^ g ∣ Om ω := by rw [← hWo]; exact opow_dvd_opow ω (hgl.trans hθPW).le
  have hgα : ω ^ g ∣ bcAlpha S (n + 1) := by
    rw [hα]
    unfold ConjT.Aη
    refine dvd_add hgW ?_
    rw [hN, mul_add]
    refine dvd_add ?_ ?_
    · have e : ConjT.th S * Om ω = ω ^ (ConjT.th S + Om ω) := by
        conv_lhs => rw [← hθo, ← hWo]
        rw [← opow_add]
      rw [e]; exact opow_dvd_opow ω ((hgl.trans hθPW).le.trans le_add_self)
    rw [← mul_assoc, hθP]
    exact Dvd.dvd.mul_right (opow_dvd_opow ω hgl.le) _
  have hX : ω ^ g ∣ bcAlpha S (n + 1) + val S (zeInit ρ1) := dvd_add hgα (hgv ▸ hPdvd)
  -- `θ·ω^E ∣ A_β`
  have hEζ : E = cdExp ζκ := by rw [hE, hζκ]; exact ze_exp_add N hζκ0
  have hEP : E < P' := by
    rw [hEζ]
    exact ((right_le_opow _ one_lt_omega0).trans (ze_opow_exp_le hζκ0)).trans_lt hζP
  have hθE : ConjT.th S * ω ^ E = ω ^ (ConjT.th S + E) := by
    conv_lhs => rw [← hθo]
    rw [← opow_add]
  have hQβ : ω ^ (ConjT.th S + E) ∣ ConjT.Aη S β := by
    unfold ConjT.Aη
    refine dvd_add ?_ ?_
    · rw [← hWo]
      exact opow_dvd_opow ω (((add_lt_add_iff_left _).2 hEP).trans hθPW).le
    · rw [← hθE]; exact mul_dvd_mul_left _ hdvd
  have heq : bcAlpha S (n + 1) + val S (zeInit ρ1) + ω ^ g = ConjT.Aη S β + ω ^ (ConjT.th S + E) := by
    rw [add_assoc, ← hgv, ← hsplit, ← hA1, ← hθE, ← Bt.A_add, ← hdec]
  obtain ⟨hgE, hXβ⟩ := ze_cancel_last hX hQβ heq
  -- `θ`-divisibility of the parts
  have hθα : ConjT.th S ∣ bcAlpha S (n + 1) := by rw [hα]; exact Sf.sfTh_dvd_A S N
  have hθI : ConjT.th S ∣ val S (zeInit ρ1) := by
    have h1 : ConjT.th S ∣ bcAlpha S (n + 1) + val S (zeInit ρ1) := hXβ ▸ Sf.sfTh_dvd_A S β
    exact (dvd_add_iff hθα).1 h1
  have hθL : ConjT.th S ∣ val S (zeLast ρ1) := by
    rw [hgv, hgE, ← hθE]; exact dvd_mul_right _ _
  -- the `σ` side
  have hσsplit : val S (bcSig (bcPre (n + 1)) bcPreW ρ1) =
      val S (bcSig (bcPre (n + 1)) bcPreW (zeInit ρ1)) + val S (bcSig (bcPre (n + 1)) bcPreW (zeLast ρ1)) :=
    zeVal_split (S := S) (bcSig (bcPre (n + 1)) bcPreW) (fun a b => bcSig_add a b) (bcSig_zero) ρ1
  obtain ⟨ζ2, hζ2⟩ := Sf.sfSig_dvd n (zeInit_D hD1) hθI
  obtain ⟨δ2, hδ2⟩ := Sf.sfSig_dvd_prin n (zeLast_D hD1) hLP hθL
  have hσLN : NF (bcSig (bcPre (n + 1)) bcPreW (zeLast ρ1)) := bc_NF (zeLast_D hD1)
  have hσLP : (bcSig (bcPre (n + 1)) bcPreW (zeLast ρ1)).isPrin = true := by rw [isPrin_bcSig]; exact hLP
  have hσpr := isPrincipal_val S hσLN hσLP
  have hσ0 := val_ne_zero S hσLN (NF.ne_zero_of_isPrin hσLP)
  obtain ⟨h, hhv⟩ := exists_opow_of_principal hσpr hσ0
  have hδ0 : δ2 ≠ 0 := by rintro rfl; rw [mul_zero] at hδ2; exact hσ0 hδ2
  have hθh : ConjT.th S ≤ h := by
    have h1 : ConjT.th S ≤ ω ^ h := by
      rw [← hhv, hδ2]; exact le_mul_of_one_le_right zero_le (Order.one_le_iff_ne_zero.2 hδ0)
    rw [← hθo] at h1
    exact (opow_le_opow_iff_right one_lt_omega0).1 h1
  obtain ⟨d, hd⟩ := exists_add_of_le hθh
  have hδω : δ2 = ω ^ d := by
    have h1 : ConjT.th S * δ2 = ConjT.th S * ω ^ d := by
      rw [← hδ2, hhv, hd, opow_add, hθo]
    exact (mul_right_inj' (ConjT.SC_th S).1.ne').1 h1
  set N' := Om ω + P' * ω with hN'
  set β' := N' + ζ2 with hβ'
  have hAβ' : ConjT.Aη S β' = bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW (zeInit ρ1)) := by
    rw [hβ', Bt.A_add, ← Sf.sfAlphaW_eq S, hζ2]
  have hBp : Bc.bcB S n p = Pv S (β' + ω ^ d) := by
    rw [← hpP, hB1, hσsplit, hδ2, hδω, ← add_assoc, ← hAβ', ← Bt.A_add]
  refine ⟨Pv S β', Pv S ζg, hgp, ?_, ?_⟩
  · -- `x = P(β') ≤ B_n P(ζ)`
    rw [hBg]
    show S.psi (ConjT.Aη S β') (Om 1) ≤ _
    rw [hAβ']
    refine (psi_mono Low.InR_Om_one ((add_le_add_iff_left _).2 ?_)).1
    refine not_lt.1 fun hlt => ?_
    have h1 := (bc_lt_iff (k := n) hDg (zeInit_D hD1)).1 hlt
    have h2 : bcAlpha S (n + 1) + val S (zeInit ρ1) ≤ bcAlpha S (n + 1) + val S ρg := by
      rw [hXβ, ← hAg]; exact ConjT.A_mono S hβg
    exact absurd ((add_le_add_iff_left _).1 h2) (not_le.2 h1)
  · -- the window
    intro μ hμ hx hμB
    have hBL : Bc.bcB S n p < Nc.ncL S (ω + 1) := Bc.bcB_bound' S n p hpC
    have hμT : upsilon μ < Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
      rw [← Lw.lw_L_eq S]; exact hμB.trans hBL
    obtain ⟨-, -, -, hpvμ⟩ := cdEta_pv_spec (S := S) hμ.1 hμT
    have hb1 : β' < cdEta S μ := by
      by_contra h; push Not at h
      have := Pv_mono (S := S) h
      rw [hpvμ] at this
      exact absurd hx (not_lt.2 this)
    have hb2 : cdEta S μ < β' + ω ^ d := by
      by_contra h; push Not at h
      have := Pv_mono (S := S) h
      rw [hpvμ, ← hBp] at this
      exact absurd hμB (not_lt.2 this)
    obtain ⟨γ, hγ⟩ := exists_add_of_le hb1.le
    have hγ0 : γ ≠ 0 := by rintro rfl; rw [add_zero] at hγ; exact (ne_of_gt hb1) hγ
    have hγd : γ < ω ^ d := by rw [hγ] at hb2; exact (add_lt_add_iff_left β').1 hb2
    have hexp : cdExp (cdEta S μ) = cdExp γ := by rw [hγ]; exact ze_exp_add β' hγ0
    unfold cdCapB
    rw [hexp, hγ, add_assoc, hBp]
    refine Pv_mono ((add_le_add_iff_left β').2 ?_)
    exact (isPrincipal_add_omega0_opow d hγd ((ze_opow_exp_le hγ0).trans_lt hγd)).le

/-- **`Ye.YeGapRng S`** (gap restarts of every code) from CapV in `(L(ω), L(ω+1))` and ENUM-REACH. -/
theorem zeGapRng (hV : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hU : CdUPPER S) (hL : CdLOWER S) : Ye.YeGapRng S := by
  intro n l l' p l₀ κ hP hl₀ hκ hpκ
  obtain ⟨x, q, hqp, hxq, hwin⟩ := zeGap_win hP hκ hpκ
  obtain ⟨hW, hfar, hp, hI, -, -, ha, hgap⟩ := hP
  obtain ⟨hpC, -, -, hδp, -⟩ := Xw.xwWin hW hfar hp
  have hcp : Bc.bcC S n < p := hW.2.1.trans ((cdRho_lt_delta l).trans hδp)
  have hBlt : ∀ {a b : Ordinal.{0}}, a < Bc.bcC S (n + 1) → b < Bc.bcC S (n + 1) → a < b →
      Bc.bcB S n a < Bc.bcB S n b := fun ha hb hab =>
    (Bc.bcB_lt_iff (ha.trans (Bc.bcC_lt S (n + 1))) (hb.trans (Bc.bcC_lt S (n + 1)))).2 hab
  have hpr : IsPrincipal (· + ·) p := (indec_iff.1 hI).2
  have h1p : (1 : Ordinal.{0}) < p := by
    have h1c : (1 : Ordinal.{0}) < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) :=
      one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _))
    exact h1c.trans hcp
  have hsucc : ∀ y < p, y + 1 < p := fun y hy => hpr hy h1p
  -- `x < ρ_{l₀}`
  have hxl : x < upsilon l₀ :=
    hxq.trans_lt ((hBlt (hqp.trans hpC) ((hsucc q hqp).trans hpC) (lt_add_one q)).trans_le
      (hgap (q + 1) (hsucc q hqp)))
  have hcap := hwin l₀ hl₀ hxl ha
  -- `ρ_{l₀}` is a range restart above `L(ω)`
  have hB0c : Bc.bcB S n (Bc.bcC S n) = Nc.ncL S ω := by
    rw [show Bc.bcC S n = Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) from rfl, Bc.bcB_base]
  have hLl : Nc.ncL S ω < upsilon l₀ := by
    rw [← hB0c]
    exact (hBlt (hcp.trans hpC) ((hsucc _ hcp).trans hpC) (lt_add_one _)).trans_le
      (hgap _ (hsucc _ hcp))
  have hω1 : upsilon l₀ < Nc.ncL S (ω + 1) := ha.trans (Bc.bcB_bound' S n p hpC)
  have hB0 : cdB0 ≤ l₀ := by
    have h0 : upsilon cdB0 < upsilon l₀ :=
      Fp.fpB0_lt_M.trans (((Rl.rlM_lt_L1 (S := S)).trans_le ((le_of_eq (by unfold Bc.bcC; simp)).trans
        (Bc.bcC_mono S (Nat.zero_le n)))).trans ((Bc.bcC_lt S n).trans hLl))
    exact (Tp.tpUps_lt_iff.1 h0).le
  have hPp : cdCode S l₀ < Nc.ncPp S := by
    by_contra h
    push Not at h
    rcases (Te.teCode_hi_iff hl₀.1 hω1).1 h with ⟨k, hk⟩ | hk
    · exact absurd (hk ▸ Qq.qqL_lt_omega S k) (not_lt.2 hLl.le)
    · exact absurd hk (ne_of_gt hLl)
  have hR : CdRange S l₀ := ⟨hl₀, hB0, hω1, hPp⟩
  exact ⟨_, cdEnum_exact hU hL hR, (hV l₀ hR hLl).trans_le hcap⟩

/-- **`Yz.YzGapRngHi S`** (the leaf `skGapRngHi`) from CapV in `(L(ω), L(ω+1))` and ENUM-REACH. -/
theorem zeGapRngHi (hV : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hU : CdUPPER S) (hL : CdLOWER S) : Yz.YzGapRngHi S :=
  Yz.yzGapRngHi_of (zeGapRng hV hU hL)

end Googology.Trans.PoR.InaccPsi.R2.Ze
