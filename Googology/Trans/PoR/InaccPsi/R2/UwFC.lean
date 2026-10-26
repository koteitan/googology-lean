import Googology.Trans.PoR.InaccPsi.R2.UwN

/-!
# (FC): the fixed points of a lifted level below a member are dominated by a member

`W = Ω_{s+1}`, `V = Ω_{s+2}` (`s` finite), `ψ = S.psi · W`, `ψ_V = S.psi · V`, `Hˡ_γ = Ul.ulH S s γ`; `i < s`,
`X = Ul.UlK S i q` (`q` strongly critical, `q ≤ Ω_{i+1}`).

* `uw_fc` (**(FC)**: for every level `γ < V`, every `y ∈ X` below `W`, every fixed point `p ≤ y` of `Hˡ_γ`, some fixed
  point `p'` of `Hˡ_γ` with `p ≤ p' ≤ y` is in `X`; by well-founded induction on `y` along its Cantor and Veblen parts;
  at a strongly critical `y = ψ(e)` that is not fixed, the last exponent `k` of `e` is `≤ γ`, so `W^{k+1}` divides the
  own argument of `p`, and `p ≤ ψ(B) < y` with `B = W^{k+1}·(e / W^{k+1}) ∈ X`);
* `uw_fc_max` (**the largest fixed point below a member is a member**: if `p ≤ y` is a fixed point of `Hˡ_γ` and every
  fixed point `≤ y` is `≤ p`, then `p ∈ X`).

No hypothesis on `γ` beyond `γ < V`.  No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul
  Googology.Trans.PoR.InaccPsi.R2.Uo Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Us

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

/-- `ep ≤ w·(e / w)` for a multiple `ep ≤ e` of `w ≠ 0`. -/
theorem uw_le_trunc {w e ep : Ordinal.{0}} (hw : w ≠ 0) (hd : w ∣ ep) (hle : ep ≤ e) : ep ≤ w * (e / w) := by
  obtain ⟨m, rfl⟩ := hd
  exact mul_le_mul_right ((Ordinal.mul_le_iff_le_div hw).1 hle) w

/-- **(FC)**: for `i < s`, `q` strongly critical, `q ≤ Ω_{i+1}`, `γ < V`: for every `y ∈ K^{(i)}_q` below `W` and every
fixed point `p ≤ y` of `Hˡ_γ`, some fixed point `p'` of `Hˡ_γ` with `p ≤ p' ≤ y` is in `K^{(i)}_q`. -/
theorem uw_fc (hs : s < ω) {i q γ : Ordinal.{0}} (his : i < s) (hq : SC q) (hqL : q ≤ Om (i + 1))
    (hγV : γ < Om (s + 1 + 1)) :
    ∀ y, UlK S i q y → y < Om (s + 1) → ∀ p, ulH S s γ p = p → p ≤ y →
      ∃ p', UlK S i q p' ∧ ulH S s γ p' = p' ∧ p ≤ p' ∧ p' ≤ y := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  have hκV : S.InR (Om (s + 1 + 1)) := InR_Om_succ (s + 1)
  have hi : i < ω := his.trans hs
  have hqΛ : q ≤ S.Lam := us_qΛ hi hqL
  have hW1 : (1 : Ordinal.{0}) < Om (s + 1) := Ui.ui_one_lt_SC (Ui.ui_SC_W s)
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hy hyW p hp hpy
  have hpSC : SC p := by rw [← hp]; exact ulH_SC γ p
  have hpL : Om s < p := by rw [← hp]; exact ulH_gt γ p
  have hy0 : y ≠ 0 := fun e => by rw [e] at hpy; exact absurd hpy (not_le.2 hpSC.1)
  have hdesc : ∀ y', y' < y → UlK S i q y' → p ≤ y' →
      ∃ p', UlK S i q p' ∧ ulH S s γ p' = p' ∧ p ≤ p' ∧ p' ≤ y := fun y' hy' hK hpy' => by
    obtain ⟨p', a, b, c, d⟩ := IH y' hy' hK (hy'.trans hyW) p hp hpy'
    exact ⟨p', a, b, c, d.trans hy'.le⟩
  by_cases ht : tail y = 0
  · have hly : lead y = y := by have := lead_add_tail hy0; rwa [ht, add_zero] at this
    set b := log ω y with hbdef
    have hbK : UlK S i q b := (ulK_dec hq y hy).2
    have hyb : ω ^ b = y := hly
    rcases (log_le_self ω y).lt_or_eq with hlt | heq
    · refine hdesc b hlt hbK (not_lt.1 fun hbp => ?_)
      have := hpSC.2 0 hpSC.1 b hbp
      rw [veblen_zero_apply, hyb] at this
      exact absurd hpy (not_le.2 this)
    have hE : InE y := by
      show ω ^ y = y
      conv_lhs => rw [← heq]
      exact hyb
    by_cases hSC : SC y
    swap
    · obtain ⟨hdec, ha, hb, -⟩ := Mx.mxDec hE (pos_iff_ne_zero.2 hy0) hSC
      have hK := uoK_veb (S := S) (s := i) (q := q) (by rw [hdec]; exact hy) (by rw [hdec]; exact ha)
        (by rw [hdec]; exact hb)
      by_cases h1 : p ≤ invVeblen₁ y
      · exact hdesc _ ha hK.1 h1
      by_cases h2 : p ≤ invVeblen₂ y
      · exact hdesc _ hb hK.2 h2
      have := hpSC.2 _ (not_le.1 h1) _ (not_le.1 h2)
      rw [hdec] at this
      exact absurd hpy (not_le.2 this)
    -- the strongly critical case `y = ψ(e)`
    have hyB : y < S.psi S.Lam (Om (s + 1)) := uw_lt_psiLam hqΛ (uw_q_le his hqL _) hy hyW
    obtain ⟨e, hown, hye⟩ := Ui.ui_own_of_SC hs hSC (hpL.trans_le hpy) hyB
    by_cases hfix : ulH S s γ y = y
    · exact ⟨y, hy, hfix, hpy, le_rfl⟩
    have hpy' : p < y := lt_of_le_of_ne hpy fun h => hfix (h ▸ hp)
    obtain ⟨ep, hownp, hpe⟩ := Ui.ui_own_of_SC hs hpSC hpL (hpy'.trans_le hye.symm.le)
    have hepe : ep < e := (Ui.ui_own_lt_iff hownp hown).1 (by rw [hpe, hye]; exact hpy')
    have he0 : e ≠ 0 := fun h => by rw [h] at hepe; exact absurd hepe (not_lt.2 zero_le)
    have hfixp : ulH S s γ (S.psi ep (Om (s + 1))) = S.psi ep (Om (s + 1)) := by rw [hpe]; exact hp
    have hdp : Om (s + 1) ^ (γ + 1) ∣ ep := ul_conv hs γ ep hownp hfixp
    have hγp : γ ≤ S.psi ep (Om (s + 1 + 1)) := us_val_le hs hownp hfixp
    have hVle : S.psi ep (Om (s + 1 + 1)) ≤ S.psi e (Om (s + 1 + 1)) := (psi_mono hκV hepe.le).1
    rcases (hγp.trans hVle).lt_or_eq with hγe | hγe
    swap
    · -- `γ = ψ_V(e)`: then `ψ_V(ep) = ψ_V(e)` with both own, so `ep = e`
      exfalso
      have heq2 : S.psi ep (Om (s + 1 + 1)) = S.psi e (Om (s + 1 + 1)) :=
        le_antisymm hVle (by rw [← hγe]; exact hγp)
      have hownpV : ep ∈ S.CSet ep (S.psi ep (Om (s + 1 + 1))) :=
        CSet_mono le_rfl ((Ui.ui_psi_lt ep).le.trans (psiS_bounds ep (s + 1)).1.le) hownp
      have hownV : e ∈ S.CSet e (S.psi e (Om (s + 1 + 1))) :=
        CSet_mono le_rfl ((Ui.ui_psi_lt e).le.trans (psiS_bounds e (s + 1)).1.le) hown
      exact hepe.ne (Ui.ui_own_unique (s := s + 1) hownpV hownV heq2)
    -- `γ < ψ_V(e)`: `γ` is visible at `y`, so `W^{γ+1} ∤ e`, and the last exponent `k` of `e` is `≤ γ`
    have hγK : UlK S s (S.psi e (Om (s + 1))) γ := by
      have h1 : UlK S s p γ := (ul_vis hpSC).1 (by rw [← hp]; exact ulH_D_lt γ p)
      rw [hye]; exact h1.mono hpy
    have hγC := uoDV hs e γ hown hγK hγe
    have hnd : ¬ Om (s + 1) ^ (γ + 1) ∣ e := fun hd =>
      hfix (by rw [← hye]; exact uo_fwd hs γ hγV e hown hd he0 hγC)
    obtain ⟨k, hk, hk1⟩ := us_last hW1 he0
    have hkγ : k ≤ γ := not_lt.1 fun hγk => hnd ((opow_dvd_opow _ (Order.add_one_le_of_lt hγk)).trans hk)
    set w := Om (s + 1) ^ (k + 1) with hwdef
    have hw0 : w ≠ 0 := (Ui.ui_W_pos s _).ne'
    set B := w * (e / w) with hBdef
    have hdk : w ∣ ep := (opow_dvd_opow _ (add_le_add_left hkγ 1)).trans hdp
    have hepB : ep ≤ B := uw_le_trunc hw0 hdk hepe.le
    have hBe : B < e := by
      have hdm : B + e % w = e := Ordinal.div_add_mod e w
      have hr0 : e % w ≠ 0 := fun h0 => by
        have heB : e = B := by rw [← hdm, h0, add_zero]
        exact hk1 ⟨e / w, heB⟩
      conv_rhs => rw [← hdm]
      exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hr0)
    have hBC : B ∈ S.CSet e (S.psi e (Om (s + 1))) := Ui.ui_mod_mem le_add_self e hown
    have hψB : S.psi B (Om (s + 1)) < y := by rw [← hye]; exact psi_lt_psi_of_mem hκ hBe hBC
    have hpB : p ≤ S.psi B (Om (s + 1)) := by rw [← hpe]; exact (psi_mono hκ hepB).1
    have heK : UlK S i q e := uoArg hqΛ hκ hown (by rw [hye]; exact hy) (uw_q_le his hqL e)
    have hkK : UlK S i q k := us_dig_exp hs hq heK k (us_dig_ne hk hk1)
    have hk1K : UlK S i q (k + 1) := UlK.add hkK UlK.one
    have hBK : UlK S i q B := by
      have hWk1 : UlK S i q (Om (s + 1) * (k + 1)) := by
        have := ulK_opow_mul hq (us_K_Om hs) (k + 1) hk1K; rwa [Ui.ui_W_opow s] at this
      have h1 : UlK S i q (e / w) := by rw [hwdef, Ui.ui_W_eq s (k + 1)]; exact ulK_div hq e heK _ hWk1
      exact us_K_Wmul hs hq hk1K h1
    exact hdesc _ hψB (UlK.coll hκ (us_W_ne_Om his.ne) (us_K_Om hs) hBK) hpB
  · have hly : lead y < y := by
      have e1 := lead_add_tail hy0
      conv_rhs => rw [← e1]
      exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 ht)
    have hty : tail y < y := tail_lt hy0
    obtain ⟨hlK, htK⟩ := uoK_lead_tail hq hy hy0
    by_cases h1 : p ≤ lead y
    · exact hdesc _ hly hlK h1
    by_cases h2 : p ≤ tail y
    · exact hdesc _ hty htK h2
    have hP : lead y + tail y < p := hpSC.isPrincipal (not_le.1 h1) (not_le.1 h2)
    rw [lead_add_tail hy0] at hP
    exact absurd hpy (not_le.2 hP)

/-- **The largest fixed point of `Hˡ_γ` below a member is a member**: for `y ∈ K^{(i)}_q` below `W` and a fixed point
`p ≤ y` of `Hˡ_γ` with every fixed point `≤ y` below `p`: `p ∈ K^{(i)}_q`. -/
theorem uw_fc_max (hs : s < ω) {i q γ y p : Ordinal.{0}} (his : i < s) (hq : SC q) (hqL : q ≤ Om (i + 1))
    (hγV : γ < Om (s + 1 + 1)) (hy : UlK S i q y) (hyW : y < Om (s + 1)) (hp : ulH S s γ p = p) (hpy : p ≤ y)
    (hmax : ∀ p', ulH S s γ p' = p' → p' ≤ y → p' ≤ p) : UlK S i q p := by
  obtain ⟨p', hK, hf, h1, h2⟩ := uw_fc hs his hq hqL hγV y hy hyW p hp hpy
  rw [le_antisymm (hmax p' hf h2) h1] at hK
  exact hK

end Googology.Trans.PoR.InaccPsi.R2.Uw
