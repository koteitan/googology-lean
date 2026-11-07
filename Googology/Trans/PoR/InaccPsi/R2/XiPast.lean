import Googology.Trans.PoR.InaccPsi.R2.XiLay
import Googology.Trans.PoR.InaccPsi.R2.ZuRef

/-!
# XiPast: EVERY LAYER BELOW `θ` FROM LEMMA IMG AT THE READINGS

`θ = ConjT.th S = ψ_{Ω₂}(Ω_ω)` is the supremum of the codes `T_n = ψ_{Ω₂}(ε_{Ω_n+1})` (`Us.us_top_sup`), which have
no countable parameters (they lie in every `K⁽⁰⁾_q`, so `P₀(T_n) ⊆ Γ₀`).  With the gate `Γ₀` (`< tdK S`, ε₀ below it),
the layer of `T_n` (`Xi.xiB`) serves every atom index `B` with `Γ(B) ≤ T_n`, and the `T_n` are cofinal in `θ`, which
is closed under `Γ` (`Zu.zuGcG_lt_th`):

* `XiImgAll` (**LEMMA IMG AT EVERY READING OF A CODE BELOW `θ`**, a hypothesis);
* `xiT`, `xiT_K`, `xiT_lt`, `xiT_cof`, `xiT_SC`, `xiT_gE`, `xiT_par`, `xiLH_T`;
* `xi_past` (**`Zm.ZmPastAt S c` for every layer `c < θ`**, given `XiImgAll S`).

No new axiom.  New definitions: `XiImgAll`, `xiT`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xi

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **LEMMA IMG AT EVERY READING OF A CODE BELOW `θ`**: in every restart context `RstK ρ τ δ` with `Γ₀ < ρ`, every
code `Ω₁ ≤ c < θ` visible at `ρ` has the image property at `R_ρ(c)`. -/
def XiImgAll (S : InaccSeq.{0}) : Prop :=
  ∀ ρ τ δ c : Ordinal.{0}, RstK ρ τ δ → gamma 0 < ρ → WDom S ρ c → Om1 ≤ c → c < ConjT.th S →
    Gn.GnI ρ δ (xiR ρ c)

variable {S : InaccSeq.{0}}

/-- The cofinal codes `T_n = ψ_{Ω₂}(ε_{Ω_n+1})`. -/
noncomputable def xiT (S : InaccSeq.{0}) (n : ℕ) : Ordinal.{0} :=
  S.psi (veblen 1 (Om (n : Ordinal.{0}) + 1)) (Om (1 + 1))

theorem xiT_K (n : ℕ) (v : Ordinal.{0}) : Ul.UlK S 0 v (xiT S n) := by
  have hne : Om (1 + 1 : Ordinal.{0}) ≠ Om (0 + 1) := by
    refine (Om_lt_Om.2 ?_).ne'
    rw [zero_add]; exact (lt_add_one (1 : Ordinal.{0}))
  refine Ul.UlK.coll (InR_Om_succ 1) hne (Us.us_K_Om (r := 1) one_lt_omega0) ?_
  exact Ul.UlK.phi Ul.UlK.one (Ul.UlK.add (Ul.UlK.om (Ul.UlK.nat n)) Ul.UlK.one)

theorem xiT_lt (n : ℕ) : xiT S n < ConjT.th S := (Us.us_top_sup (S := S) 1).2 n

theorem xiT_cof {z : Ordinal.{0}} (hz : z < ConjT.th S) : ∃ n : ℕ, z < xiT S n :=
  (Us.us_top_sup (S := S) 1).1 z hz

theorem xiT_SC (n : ℕ) : SC (xiT S n) := SC_psi (InR_Om_succ 1) _

theorem xiT_gE (n : ℕ) : Gg.ggE < xiT S n := by
  have hG : Gg.ggE < Gg.ggGam := by
    refine lt_of_le_of_ne Gg.ggE_le_ggGam fun e => ?_
    have hSC : SC Gg.ggE := e ▸ Gg.ggGam_spec.1
    have h2 : Om 1 + 1 < Gg.ggE := (ev_isSuccLimit_of_inE Rk.rk_E_inE).add_one_lt Rk.rk_Om1_E
    have := hSC.2 1 (Gg.gg_one_lt_of_SC hSC) (Om 1 + 1) h2
    rw [← Rk.rk_E_eq] at this
    exact lt_irrefl _ this
  exact hG.trans_le (Gg.ggGam_le (xiT_SC n) (psiS_bounds _ 1).1)

theorem xiT_par (n : ℕ) : ∀ p ∈ wP (xiT S n), p ≤ gamma 0 := by
  have hG1 : gamma 0 < Om1 := by
    rw [Rj.rj_Om1]; exact (Gr.gr_gam0_lt_tdK S).trans Td.tdK_lt_Om1
  have hO : (Om1 : Ordinal.{0}) ≤ xiT S n := by rw [Rj.rj_Om1]; exact (psiS_bounds _ 1).1.le
  intro p hp
  exact (((wP_spec S).2.2 _ _ hO (xiT_lt n) (Lq.lq_gamma_SC 0) hG1.le).2 (xiT_K n _) p hp).le

theorem xiLH_T (hI : XiImgAll S) (n : ℕ) : XiLH S (gamma 0) (xiT S n) where
  th := xiT_lt n
  eps := Low.opow_eq_self_of_SC (xiT_SC n)
  gE := xiT_gE n
  par := xiT_par n
  ge := epsilon_zero_le_of_omega0_opow_le (Low.opow_eq_self_of_SC (Lq.lq_gamma_SC 0)).le
  img := fun ρ τ δ c h hg hd hc1 hcT => hI ρ τ δ c h hg hd hc1 (hcT.trans_lt (xiT_lt n))

/-- **EVERY LAYER BELOW `θ`**: `Zm.ZmPastAt S c` for every `c < θ`, given Lemma IMG at the readings. -/
theorem xi_past (hI : XiImgAll S) : ∀ c, c < ConjT.th S → Zm.ZmPastAt S c := by
  intro c hc
  refine ⟨Qt.qtU S, Qt.qtU_ok S, fun B hB => ?_⟩
  have hc1 : c + 1 < ConjT.th S := (ConjT.SC_th S).isSuccLimit.add_one_lt hc
  have hB1 : B < ConjT.th S := hB.trans (Zu.zuGcG_lt_th S hc1)
  obtain ⟨n, hn⟩ := xiT_cof (Zu.zuGcG_lt_th S hB1)
  exact xi_layA (xiLH_T hI n) (Gr.gr_gam0_lt_tdK S) hn.le

end Googology.Trans.PoR.InaccPsi.R2.Xi
