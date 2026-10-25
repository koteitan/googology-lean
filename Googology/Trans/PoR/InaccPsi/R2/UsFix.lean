import Googology.Trans.PoR.InaccPsi.R2.UsBV

/-!
# Fixed points and values of a lifted level read off the own argument: the converse of FWD

`W = Ω_{s+1}`, `V = Ω_{s+2}` (`s` finite), `ψ = S.psi · W`, `Hˡ_γ = Ul.ulH S s γ`, `K_q = Ul.UlK S s q`, *own*:
`B ∈ Cl(B, ψ B)`.  FWD (`Uo.uo_fwd`) asks `W^{γ+1} ∣ B` and `γ ∈ Cl(B, ψ B)`; CONV (`Ul.ul_conv`) gives back only
the divisibility.  With the first value of an atom level (`Us.us_bv_atom`) the other half comes back too:

* `us_last_K` (the last nonzero base-`W` digit of an own `B ≠ 0`: its exponent `k` is in `K_{ψ B}`, and `k <
  ψ_V(B)` when `k < V`; `V ∣ B` when `k ≥ V`);
* `us_fix_lt` (**converse of FWD**: if `ψ(B)` is a fixed point of `Hˡ_γ`, then `γ < ψ_V(B)` and `γ ∈ Cl(B,
  ψ B)`), `us_fix_iff` (**`Hˡ_γ(ψ B) = ψ B ↔ W^{γ+1} ∣ B ∧ γ < ψ_V(B) ∧ γ ∈ K_{ψ B}`** for own `B ≠ 0`, `γ < V`);
* `us_val_le` (**a value `ψ(B)` of `Hˡ_γ` has `γ ≤ ψ_V(B)`**), `us_dvd_range` (**divisibility from the range**: if
  `ψ(B)` is fixed by every `Hˡ_j`, `j < γ`, visible at `ψ(B)`, then `W^γ ∣ B`; any level `γ`);
* `us_run_fix` (**the `ψ`-link from a fixed-point base with no hull hypothesis**: for own `B` with `ψ(B)` a fixed
  point of `Hˡ_γ`, `γ < V`, `D < W` valid: `ψ(B + W^γ·D) = Hˡ_γ(ψ B + D)`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Us

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Uo
  Googology.Trans.PoR.InaccPsi.R2.Uc

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

/-- **The last nonzero digit of an own argument**: `W^k ∣ B`, `¬ W^{k+1} ∣ B`, `k ∈ K_{ψ B}`, and `k < ψ_V(B)` when
`k < V`. -/
theorem us_last_K (hs : s < ω) {B : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om (s + 1)))) (hB0 : B ≠ 0) :
    ∃ k, Om (s + 1) ^ k ∣ B ∧ ¬ Om (s + 1) ^ (k + 1) ∣ B ∧ UlK S s (S.psi B (Om (s + 1))) k ∧
      (k < Om (s + 1 + 1) → k < S.psi B (Om (s + 1 + 1))) := by
  have hs1 : s + 1 < ω := Ui.ui_s1_lt_omega hs
  obtain ⟨k, hk, hk1⟩ := us_last (Ui.ui_one_lt_SC (Ui.ui_SC_W s)) hB0
  have hdig := us_dig_ne hk hk1
  have hBK : UlK S s (S.psi B (Om (s + 1))) B := ul_K_of_mem hown
  refine ⟨k, hk, hk1, us_dig_exp hs (Ui.ui_psi_SC B) hBK k hdig, fun hkV => ?_⟩
  have hownV : B ∈ S.CSet B (S.psi B (Om (s + 1 + 1))) :=
    CSet_mono le_rfl (Ui.ui_psi_lt B |>.le.trans (psiS_bounds B (s + 1)).1.le) hown
  have hBK1 : UlK S (s + 1) (S.psi B (Om (s + 1 + 1))) B := ul_K_of_mem hownV
  exact ulK_lt_W hs1 (Ui.ui_psi_SC B) (Ui.ui_L_lt_psi B) (us_dig_exp hs (Ui.ui_psi_SC B) hBK1 k hdig) hkV

theorem us_V_dvd_of_le {B k : Ordinal.{0}} (hk : Om (s + 1) ^ k ∣ B) (hVk : Om (s + 1 + 1) ≤ k) :
    Om (s + 1 + 1) ∣ B := by
  have := (opow_dvd_opow (Om (s + 1)) hVk).trans hk
  rwa [us_W_V s] at this

/-- A value of `Hˡ_l` at index `0` is not a fixed point of `Hˡ_l`. -/
theorem us_val0_ne {l : Ordinal.{0}} : ulH S s l (ulH S s l 0) ≠ ulH S s l 0 := fun h => by
  have h2 : ulH S s l 0 < ulH S s l (ulH S s l 0) := (ulH_lt_iff (S := S) (s := s) l).2 (ulH_SC l 0).1
  rw [h] at h2
  exact lt_irrefl _ h2

/-- **The converse of FWD**: if `ψ(B)` is a fixed point of `Hˡ_γ` (`B` own), then `γ < ψ_V(B)` and
`γ ∈ Cl(B, ψ B)`. -/
theorem us_fix_lt (hs : s < ω) {B γ : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om (s + 1))))
    (hfix : ulH S s γ (S.psi B (Om (s + 1))) = S.psi B (Om (s + 1))) :
    γ < S.psi B (Om (s + 1 + 1)) ∧ γ ∈ S.CSet B (S.psi B (Om (s + 1))) := by
  set p := S.psi B (Om (s + 1)) with hpdef
  have hpSC : SC p := Ui.ui_psi_SC B
  have hdγ : ulD S s γ < p := by rw [← hfix]; exact ulH_D_lt γ p
  have hlt : γ < S.psi B (Om (s + 1 + 1)) := by
    rcases eq_or_ne B 0 with hB0 | hB0
    · exfalso
      have hp0 : p = ulH S s 0 0 := by rw [hpdef, hB0, us_psi0 hs]
      have hf0 : ulH S s 0 p = p := ucG_fix_mono zero_le hfix ((ulD_le_self 0).trans_lt hpSC.1)
      rw [hp0] at hf0
      exact us_val0_ne hf0
    obtain ⟨k, hk, hk1, hkK, hkψ⟩ := us_last_K hs hown hB0
    rcases lt_or_ge k (Om (s + 1 + 1)) with hkV | hVk
    · refine lt_of_lt_of_le (not_le.1 fun hkγ => ?_) (hkψ hkV).le
      exact hk1 (ul_conv hs k B hown (ucG_fix_mono hkγ hfix ((ul_vis hpSC).2 hkK)))
    · have hVB := us_V_dvd_of_le hk hVk
      have hbv := us_bv_atom hs hown hB0 hVB
      refine not_le.1 fun hle => ?_
      have hK : UlK S s p (S.psi B (Om (s + 1 + 1))) :=
        UlK.coll (InR_Om_succ (s + 1)) (Om_lt_Om.2 (Order.lt_add_one_iff.2 le_rfl)).ne'
          (us_K_Om (Ui.ui_s1_lt_omega hs)) (ul_K_of_mem hown)
      have hbv' : ulH S s (S.psi B (Om (s + 1 + 1))) 0 = p := hbv
      have hf : ulH S s (S.psi B (Om (s + 1 + 1))) p = p := ucG_fix_mono hle hfix ((ul_vis hpSC).2 hK)
      rw [← hbv'] at hf
      exact us_val0_ne hf
  exact ⟨hlt, uoDV hs B γ hown ((ul_vis hpSC).1 hdγ) hlt⟩

/-- **FWD and its converse**: for own `B ≠ 0` and `γ < V`, `ψ(B)` is a fixed point of `Hˡ_γ` iff `W^{γ+1} ∣ B`,
`γ < ψ_V(B)` and `γ ∈ K_{ψ B}`. -/
theorem us_fix_iff (hs : s < ω) {B γ : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om (s + 1)))) (hB0 : B ≠ 0)
    (hγV : γ < Om (s + 1 + 1)) :
    ulH S s γ (S.psi B (Om (s + 1))) = S.psi B (Om (s + 1)) ↔
      Om (s + 1) ^ (γ + 1) ∣ B ∧ γ < S.psi B (Om (s + 1 + 1)) ∧ UlK S s (S.psi B (Om (s + 1))) γ := by
  constructor
  · intro hfix
    refine ⟨ul_conv hs γ B hown hfix, (us_fix_lt hs hown hfix).1, ?_⟩
    exact (ul_vis (Ui.ui_psi_SC B)).1 (by rw [← hfix]; exact ulH_D_lt γ _)
  · rintro ⟨hd, hlt, hK⟩
    exact uo_fwd hs γ hγV B hown hd hB0 (uoDV hs B γ hown hK hlt)

/-- **A value `ψ(B)` of `Hˡ_γ`** (`B` own, `γ < V`) **has `γ ≤ ψ_V(B)`.** -/
theorem us_val_le (hs : s < ω) {B γ o : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om (s + 1))))
    (hval : ulH S s γ o = S.psi B (Om (s + 1))) : γ ≤ S.psi B (Om (s + 1 + 1)) := by
  set p := S.psi B (Om (s + 1)) with hpdef
  have hpSC : SC p := Ui.ui_psi_SC B
  have hpR : p ∈ range (ulH S s γ) := ⟨o, hval⟩
  rcases eq_or_ne B 0 with hB0 | hB0
  · rcases eq_or_ne γ 0 with hγ0 | hγ0
    · rw [hγ0]; exact zero_le
    exfalso
    have hp0 : p = ulH S s 0 0 := by rw [hpdef, hB0, us_psi0 hs]
    have hf0 : ulH S s 0 p = p := ucG_fix_lower (pos_iff_ne_zero.2 hγ0) hpR ((ulD_le_self 0).trans_lt hpSC.1)
    rw [hp0] at hf0
    exact us_val0_ne hf0
  obtain ⟨k, hk, hk1, hkK, hkψ⟩ := us_last_K hs hown hB0
  rcases lt_or_ge k (Om (s + 1 + 1)) with hkV | hVk
  · refine (not_lt.1 fun hkγ => ?_).trans (hkψ hkV).le
    exact hk1 (ul_conv hs k B hown (ucG_fix_lower hkγ hpR ((ul_vis hpSC).2 hkK)))
  · have hbv := us_bv_atom hs hown hB0 (us_V_dvd_of_le hk hVk)
    refine not_lt.1 fun hlt => ?_
    have hK : UlK S s p (S.psi B (Om (s + 1 + 1))) :=
      UlK.coll (InR_Om_succ (s + 1)) (Om_lt_Om.2 (Order.lt_add_one_iff.2 le_rfl)).ne'
        (us_K_Om (Ui.ui_s1_lt_omega hs)) (ul_K_of_mem hown)
    have hbv' : ulH S s (S.psi B (Om (s + 1 + 1))) 0 = p := hbv
    have hf : ulH S s (S.psi B (Om (s + 1 + 1))) p = p := ucG_fix_lower hlt hpR ((ul_vis hpSC).2 hK)
    rw [← hbv'] at hf
    exact us_val0_ne hf

/-- **Divisibility from the range**: if `ψ(B)` (`B` own) is fixed by every `Hˡ_j`, `j < γ`, visible at `ψ(B)`, then
`W^γ ∣ B` (any level `γ`). -/
theorem us_dvd_range (hs : s < ω) {B γ : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om (s + 1))))
    (hfix : ∀ j < γ, ulD S s j < S.psi B (Om (s + 1)) → ulH S s j (S.psi B (Om (s + 1))) = S.psi B (Om (s + 1))) :
    Om (s + 1) ^ γ ∣ B := by
  rcases eq_or_ne B 0 with hB0 | hB0
  · rw [hB0]; exact dvd_zero _
  by_contra hnd
  obtain ⟨k, hk, hk1, hkK, -⟩ := us_last_K hs hown hB0
  have hkγ : k < γ := by
    by_contra hc
    exact hnd ((opow_dvd_opow _ (not_lt.1 hc)).trans hk)
  exact hk1 (ul_conv hs k B hown (hfix k hkγ ((ul_vis (Ui.ui_psi_SC B)).2 hkK)))

/-- **The `ψ`-link from a fixed-point base, with no hull hypothesis**: for own `B` with `ψ(B)` a fixed point of `Hˡ_γ`,
`γ < V`, and `D < W` with `d < Hˡ_γ(ψ B + d)` for every `d ≤ D`: `D < ψ(B + W^γ·D) = Hˡ_γ(ψ B + D)`. -/
theorem us_run_fix (hs : s < ω) {γ B D : Ordinal.{0}} (hγV : γ < Om (s + 1 + 1))
    (hown : B ∈ S.CSet B (S.psi B (Om (s + 1))))
    (hfix : ulH S s γ (S.psi B (Om (s + 1))) = S.psi B (Om (s + 1))) (hD : D < Om (s + 1))
    (hcond : ∀ d, d ≤ D → d < ulH S s γ (S.psi B (Om (s + 1)) + d)) :
    D < S.psi (B + Om (s + 1) ^ γ * D) (Om (s + 1)) ∧
      S.psi (B + Om (s + 1) ^ γ * D) (Om (s + 1)) = ulH S s γ (S.psi B (Om (s + 1)) + D) := by
  have hdvd : Om (s + 1) ^ γ ∣ B := (opow_dvd_opow _ le_self_add).trans (ul_conv hs γ B hown hfix)
  exact uo_eq_all hs hγV hown hdvd (us_fix_lt hs hown hfix).2 hfix hD hcond

end Googology.Trans.PoR.InaccPsi.R2.Us
