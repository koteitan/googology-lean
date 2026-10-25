import Googology.Trans.PoR.InaccPsi.R2.UsRun

/-!
# Visibility of a value of a lifted level one threshold down, at a fixed-point base and at an atom base

`W = Ω_{s+1}`, `V = Ω_{s+2}` (`s` finite), `ψ = S.psi · W`, `Hˡ_γ = Ul.ulH S s γ`; `i < s`, `K = Ul.UlK S i q` (the
visibility closure one threshold down, `q` strongly critical, `q ≤ Ω_{i+1}`).  A value `Hˡ_γ(y)` with `y` not a fixed
point is in `K` iff its data are, when the run of `y` starts at a fixed point of `Hˡ_γ` or at the first value of an atom
level:

* `us_vis_fix` (**fixed-point base**: for own `B` with `p = ψ(B)` a fixed point of `Hˡ_γ`, `γ < V`, `0 < D < W` with
  `d < Hˡ_γ(p + d)` for `d ≤ D`: `Hˡ_γ(p + D) ∈ K ↔ γ ∈ K ∧ p ∈ K ∧ D ∈ K`);
* `us_vis_atom` (**atom base**: for own `x ≠ 0` with `V ∣ x`, `0 < D < W` with `d < Hˡ_{ψ_V x}(d)` for `d ≤ D`:
  `Hˡ_{ψ_V(x)}(D) ∈ K ↔ ψ_V(x) ∈ K ∧ D ∈ K`), `us_vis_atom0` (`Hˡ_{ψ_V(x)}(0) ∈ K ↔ ψ_V(x) ∈ K`);
* `us_lev_K` (**the level of every non-fixed value is visible one threshold down**: `ψ(B) = Hˡ_γ(c)` not a fixed
  point of `Hˡ_γ`, `ψ(B) ∈ K` give `γ ∈ K`; any base).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Us

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Uo
  Googology.Trans.PoR.InaccPsi.R2.Uc

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

theorem us_qΛ {i q : Ordinal.{0}} (hi : i < ω) (hqL : q ≤ Om (i + 1)) : q ≤ S.Lam :=
  hqL.trans (lt_Lam_of_mem zero_le (Ui.ui_W_mem hi 0 0)).le

theorem us_q_le_psi {i q : Ordinal.{0}} (his : i < s) (hqL : q ≤ Om (i + 1)) (e : Ordinal.{0}) :
    q ≤ S.psi e (Om (s + 1)) :=
  hqL.trans ((Om_le_Om.2 (Order.add_one_le_of_lt his)).trans (Ui.ui_L_lt_psi e).le)

/-- **Visibility at a fixed-point base**: `Hˡ_γ(p + D) ∈ K ↔ γ ∈ K ∧ p ∈ K ∧ D ∈ K` for `p = ψ(B)` (`B` own) a fixed
point of `Hˡ_γ`, `γ < V`, `0 < D < W` valid. -/
theorem us_vis_fix (hs : s < ω) {i q γ B D : Ordinal.{0}} (his : i < s) (hq : SC q) (hqL : q ≤ Om (i + 1))
    (hγV : γ < Om (s + 1 + 1)) (hown : B ∈ S.CSet B (S.psi B (Om (s + 1))))
    (hfix : ulH S s γ (S.psi B (Om (s + 1))) = S.psi B (Om (s + 1))) (hD0 : D ≠ 0) (hD : D < Om (s + 1))
    (hcond : ∀ d, d ≤ D → d < ulH S s γ (S.psi B (Om (s + 1)) + d)) :
    UlK S i q (ulH S s γ (S.psi B (Om (s + 1)) + D)) ↔
      UlK S i q γ ∧ UlK S i q (S.psi B (Om (s + 1))) ∧ UlK S i q D := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  have hi : i < ω := his.trans hs
  obtain ⟨hDψ, heq⟩ := us_run_fix hs hγV hown hfix hD hcond
  have hγC := (us_fix_lt hs hown hfix).2
  set e := B + Om (s + 1) ^ γ * D with hedef
  have hBe : B ≤ e := le_self_add
  have hownE : e ∈ S.CSet e (S.psi e (Om (s + 1))) := by
    have hγe : γ ∈ S.CSet e (S.psi e (Om (s + 1))) := (psi_mono hκ hBe).2 hγC
    exact CSet.add_mem ((psi_mono hκ hBe).2 hown) (ul_Wpow_mem hs hγe (CSet.of_lt hDψ))
  have hdvd : Om (s + 1) ^ (γ + 1) ∣ B := ul_conv hs γ B hown hfix
  rw [← heq]
  constructor
  · intro hz
    obtain ⟨hγK, hDK, -, hpK⟩ := us_run_K hs his hq hqL hownE hdvd hD0 hD hz
    exact ⟨hγK, hpK, hDK⟩
  · rintro ⟨hγK, hpK, hDK⟩
    have hBK : UlK S i q B := uoArg (us_qΛ hi hqL) hκ hown hpK (us_q_le_psi his hqL B)
    exact us_run_K' hs his.ne hq hBK hγK hDK

/-- **Visibility at an atom base**: for own `x ≠ 0` with `V ∣ x` and `0 < D < W` valid at the level `ψ_V(x)`:
`Hˡ_{ψ_V(x)}(D) ∈ K ↔ ψ_V(x) ∈ K ∧ D ∈ K`. -/
theorem us_vis_atom (hs : s < ω) {i q x D : Ordinal.{0}} (his : i < s) (hq : SC q) (hqL : q ≤ Om (i + 1))
    (hown : x ∈ S.CSet x (S.psi x (Om (s + 1)))) (hx0 : x ≠ 0) (hVx : Om (s + 1 + 1) ∣ x) (hD0 : D ≠ 0)
    (hD : D < Om (s + 1)) (hcond : ∀ d, d ≤ D → d < ulH S s (S.psi x (Om (s + 1 + 1))) d) :
    UlK S i q (ulH S s (S.psi x (Om (s + 1 + 1))) D) ↔
      UlK S i q (S.psi x (Om (s + 1 + 1))) ∧ UlK S i q D := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  have hκV : S.InR (Om (s + 1 + 1)) := InR_Om_succ (s + 1)
  have hi : i < ω := his.trans hs
  have hs1 : s + 1 < ω := Ui.ui_s1_lt_omega hs
  set γ := S.psi x (Om (s + 1 + 1)) with hγdef
  have hγV : γ < Om (s + 1 + 1) := Ui.ui_psi_lt x
  have h0 : ulH S s γ 0 = S.psi x (Om (s + 1)) := us_bv_atom hs hown hx0 hVx
  have hcond0 : ∀ d, d ≤ D → d < ulH S s γ (0 + d) := fun d hd => by rw [zero_add]; exact hcond d hd
  have heq : S.psi (x + Om (s + 1) ^ γ * D) (Om (s + 1)) = ulH S s γ D := by
    have := us_run hs hγV hown h0 hD hcond0; rwa [zero_add] at this
  set e := x + Om (s + 1) ^ γ * D with hedef
  have hxe : x < e := lt_add_of_pos_right x (mul_pos (Ui.ui_W_pos s γ) (pos_iff_ne_zero.2 hD0))
  have hxC : x ∈ S.CSet e (S.psi e (Om (s + 1))) := (psi_mono hκ hxe.le).2 hown
  have hγC : γ ∈ S.CSet e (S.psi e (Om (s + 1))) := CSet.psi_mem hxe hκV (Ui.ui_W_mem hs1 _ _) hxC
  have hDψ : D < S.psi e (Om (s + 1)) := by rw [heq]; exact hcond D le_rfl
  have hownE : e ∈ S.CSet e (S.psi e (Om (s + 1))) := CSet.add_mem hxC (ul_Wpow_mem hs hγC (CSet.of_lt hDψ))
  have hdvd : Om (s + 1) ^ (γ + 1) ∣ x := (us_W_dvd_V s (Order.add_one_le_of_lt hγV)).trans hVx
  have hownV : x ∈ S.CSet x (S.psi x (Om (s + 1 + 1))) :=
    CSet_mono le_rfl (Ui.ui_psi_lt x |>.le.trans (psiS_bounds x (s + 1)).1.le) hown
  have hqγ : q ≤ γ := hqL.trans ((Om_le_Om.2 (Order.add_one_le_of_lt (his.trans (Order.lt_add_one_iff.2 le_rfl))))
    |>.trans (psiS_bounds x (s + 1)).1.le)
  rw [← heq]
  constructor
  · intro hz
    obtain ⟨-, hDK, hxK, -⟩ := us_run_K hs his hq hqL hownE hdvd hD0 hD hz
    have hne : Om (s + 1 + 1) ≠ Om (i + 1) := (Om_lt_Om.2 ((Order.add_one_le_of_lt his).trans_lt
      ((Order.lt_add_one_iff.2 le_rfl).trans (Order.lt_add_one_iff.2 le_rfl)))).ne'
    exact ⟨UlK.coll hκV hne (us_K_Om hs1) hxK, hDK⟩
  · rintro ⟨hγK, hDK⟩
    have hxK : UlK S i q x := uoArg (us_qΛ hi hqL) hκV hownV hγK hqγ
    exact us_run_K' hs his.ne hq hxK hγK hDK

/-- **The first value of an atom level, one threshold down**: `Hˡ_{ψ_V(x)}(0) ∈ K ↔ ψ_V(x) ∈ K` for own `x ≠ 0`, `V ∣
x`. -/
theorem us_vis_atom0 (hs : s < ω) {i q x : Ordinal.{0}} (his : i < s) (hqL : q ≤ Om (i + 1))
    (hown : x ∈ S.CSet x (S.psi x (Om (s + 1)))) (hx0 : x ≠ 0) (hVx : Om (s + 1 + 1) ∣ x) :
    UlK S i q (ulH S s (S.psi x (Om (s + 1 + 1))) 0) ↔ UlK S i q (S.psi x (Om (s + 1 + 1))) := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  have hκV : S.InR (Om (s + 1 + 1)) := InR_Om_succ (s + 1)
  have hi : i < ω := his.trans hs
  have hs1 : s + 1 < ω := Ui.ui_s1_lt_omega hs
  have hownV : x ∈ S.CSet x (S.psi x (Om (s + 1 + 1))) :=
    CSet_mono le_rfl (Ui.ui_psi_lt x |>.le.trans (psiS_bounds x (s + 1)).1.le) hown
  have hne : Om (s + 1 + 1) ≠ Om (i + 1) := (Om_lt_Om.2 ((Order.add_one_le_of_lt his).trans_lt
    ((Order.lt_add_one_iff.2 le_rfl).trans (Order.lt_add_one_iff.2 le_rfl)))).ne'
  rw [us_bv_atom hs hown hx0 hVx]
  constructor
  · intro hz
    have hxK : UlK S i q x := uoArg (us_qΛ hi hqL) hκ hown hz (us_q_le_psi his hqL x)
    exact UlK.coll hκV hne (us_K_Om hs1) hxK
  · intro hγK
    have hqγ : q ≤ S.psi x (Om (s + 1 + 1)) := hqL.trans ((Om_le_Om.2 (Order.add_one_le_of_lt
      (his.trans (Order.lt_add_one_iff.2 le_rfl)))).trans (psiS_bounds x (s + 1)).1.le)
    have hxK : UlK S i q x := uoArg (us_qΛ hi hqL) hκV hownV hγK hqγ
    exact UlK.coll hκ (us_W_ne_Om his.ne) (us_K_Om hs) hxK

/-- **The level of a value is visible one threshold down**: if `ψ(B)` (`B` own) is a value of `Hˡ_γ`, `γ < V`, not a
fixed point of `Hˡ_γ`, and `ψ(B) ∈ K`, then `γ ∈ K`. -/
theorem us_lev_K (hs : s < ω) {i q γ B c : Ordinal.{0}} (his : i < s) (hq : SC q) (hqL : q ≤ Om (i + 1))
    (hγV : γ < Om (s + 1 + 1)) (hown : B ∈ S.CSet B (S.psi B (Om (s + 1))))
    (hc : ulH S s γ c = S.psi B (Om (s + 1))) (hnf : ulH S s γ (S.psi B (Om (s + 1))) ≠ S.psi B (Om (s + 1)))
    (hz : UlK S i q (S.psi B (Om (s + 1)))) : UlK S i q γ := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  have hκV : S.InR (Om (s + 1 + 1)) := InR_Om_succ (s + 1)
  have hi : i < ω := his.trans hs
  have hs1 : s + 1 < ω := Ui.ui_s1_lt_omega hs
  have hBK : UlK S i q B := uoArg (us_qΛ hi hqL) hκ hown hz (us_q_le_psi his hqL B)
  have hSC := Ui.ui_psi_SC (S := S) (s := s) B
  rcases (us_val_le hs hown hc).lt_or_eq with hlt | heq
  · have hdvd : Om (s + 1) ^ γ ∣ B := us_dvd_val hs hown hc
    have hK : UlK S s (S.psi B (Om (s + 1))) γ := (ul_vis hSC).1 (by rw [← hc]; exact ulH_D_lt γ c)
    rcases eq_or_ne B 0 with hB0 | hB0
    · -- `ψ(0) = Hˡ_0(0)` is a value of level `0` only
      rcases eq_or_ne γ 0 with hγ0 | hγ0
      · rw [hγ0]; exact UlK.zero
      exfalso
      have hp0 : S.psi B (Om (s + 1)) = ulH S s 0 0 := by rw [hB0, us_psi0 hs]
      have hf0 := ucG_fix_lower (pos_iff_ne_zero.2 hγ0) ⟨c, hc⟩ ((ulD_le_self 0).trans_lt hSC.1)
      rw [hp0] at hf0
      exact us_val0_ne hf0
    have hnd : ¬ Om (s + 1) ^ (γ + 1) ∣ B := fun hd =>
      hnf (uo_fwd hs γ hγV B hown hd hB0 (uoDV hs B γ hown hK hlt))
    exact us_dig_exp hs hq hBK γ (us_dig_ne hdvd hnd)
  · rw [heq]
    have hownV : B ∈ S.CSet B (S.psi B (Om (s + 1 + 1))) :=
      CSet_mono le_rfl (Ui.ui_psi_lt B |>.le.trans (psiS_bounds B (s + 1)).1.le) hown
    have hne : Om (s + 1 + 1) ≠ Om (i + 1) := (Om_lt_Om.2 ((Order.add_one_le_of_lt his).trans_lt
      ((Order.lt_add_one_iff.2 le_rfl).trans (Order.lt_add_one_iff.2 le_rfl)))).ne'
    exact UlK.coll hκV hne (us_K_Om hs1) hBK

end Googology.Trans.PoR.InaccPsi.R2.Us
