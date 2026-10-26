import Googology.Trans.PoR.InaccPsi.R2.UwFV
import Googology.Trans.PoR.InaccPsi.R2.UwFC

/-!
# (L1): a non-fixed value of a lifted level is visible one threshold down iff its level and its index are

`W = Ω_{s+1}`, `V = Ω_{s+2}` (`s` finite), `ψ = S.psi · W`, `Hˡ_γ = Ul.ulH S s γ`; `i < s`, `X = Ul.UlK S i q`
(`q` strongly critical, `q ≤ Ω_{i+1}`).

* `uw_base` (**the base of a non-fixed index `y`**: either `d < Hˡ_γ(d)` for every `d ≤ y` (base `0`), or a fixed point
  `p < y` of `Hˡ_γ`, the largest fixed point `≤ y`, with `d < Hˡ_γ(p + d)` for every `d ≤ y − p`);
* `uw_L1_mp`, `uw_L1_mpr`, `uw_L1` (**(L1)**: for a level `γ < V` of the notation and an index `y` with
  `Hˡ_γ(y) ≠ y` and `Hˡ_γ(y) < W`: `Hˡ_γ(y) ∈ X ↔ γ ∈ X ∧ y ∈ X`; base `0` from (FV) `Uw.uw_fv` and the run
  `Us.us_run`, base `p` from (FC) `Uw.uw_fc_max` and `Us.us_vis_fix`; the level from `Us.us_lev_K`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul
  Googology.Trans.PoR.InaccPsi.R2.Uo Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Us

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

/-- **The base of a non-fixed index**: for `Hˡ_γ(y) ≠ y`, either `d < Hˡ_γ(d)` for every `d ≤ y`, or there is a fixed
point `p < y` of `Hˡ_γ` above every fixed point `≤ y`, with `d < Hˡ_γ(p + d)` for every `d ≤ y − p`. -/
theorem uw_base {γ y : Ordinal.{0}} (hnf : ulH S s γ y ≠ y) :
    (∀ d, d ≤ y → d < ulH S s γ (0 + d)) ∨
      ∃ p, ulH S s γ p = p ∧ p < y ∧ (∀ p', ulH S s γ p' = p' → p' ≤ y → p' ≤ p) ∧
        ∀ d, d ≤ y - p → d < ulH S s γ (p + d) := by
  have hgt : ∀ d, ulH S s γ d = d → Om s < d := fun d hd => by rw [← hd]; exact ulH_gt γ d
  have hfixle : ∀ d, ¬ d < ulH S s γ d → ulH S s γ d = d := fun d h =>
    le_antisymm (not_lt.1 h) (ulH_le_self γ d)
  by_cases hy : y ≤ Om s
  · left
    intro d hd
    rw [zero_add]; exact (hd.trans hy).trans_lt (ulH_gt γ d)
  obtain ⟨p, hp, hpy, hmax⟩ := Ui.ui_base_below (ulH_normal (S := S) (s := s) γ) (not_le.1 hy) hnf
  rcases hp with rfl | ⟨hLp, hpf⟩
  · left
    intro d hd
    rw [zero_add]
    refine not_le.1 fun h => ?_
    have hfd : ulH S s γ d = d := le_antisymm h (ulH_le_self γ d)
    have hdy : d < y := lt_of_le_of_ne hd fun e => hnf (e ▸ hfd)
    exact absurd (hmax d hfd (hgt d hfd) hdy) (not_le.2 (hgt d hfd))
  · right
    refine ⟨p, hpf, hpy, fun p' hp' hp'y => ?_, fun d hd => ?_⟩
    · exact hmax p' hp' (hgt p' hp') (lt_of_le_of_ne hp'y fun e => hnf (e ▸ hp'))
    · refine not_le.1 fun h => ?_
      have hfd : ulH S s γ (p + d) = p + d := le_antisymm (h.trans le_add_self) (ulH_le_self γ _)
      have hpdy : p + d ≤ y := by
        have := add_le_add_right hd p
        rwa [Ordinal.add_sub_cancel_of_le hpy.le] at this
      have hlt : p + d < y := lt_of_le_of_ne hpdy fun e => hnf (e ▸ hfd)
      have hle : p + d ≤ p + 0 := by rw [add_zero]; exact hmax _ hfd (hgt _ hfd) hlt
      have hd0 : d = 0 := le_antisymm ((add_le_add_iff_left p).1 hle) zero_le
      rw [hd0, add_zero] at h
      exact absurd h (not_le.2 (zero_le.trans_lt (ulH_gt γ _)))

/-- **(L1), reading back**: if `Hˡ_γ(y) ≠ y`, `Hˡ_γ(y) < W` and `Hˡ_γ(y) ∈ K^{(i)}_q` (level `γ < V` of the notation,
`i < s`, `q` strongly critical, `q ≤ Ω_{i+1}`), then `γ, y ∈ K^{(i)}_q`. -/
theorem uw_L1_mp (hs : s < ω) {i q γ y : Ordinal.{0}} (his : i < s) (hq : SC q) (hqL : q ≤ Om (i + 1))
    (hγV : γ < Om (s + 1 + 1)) (hγN : γ ∈ ⋃ a, S.CSet a 0) (hW : ulH S s γ y < Om (s + 1))
    (hnf : ulH S s γ y ≠ y) (hz : UlK S i q (ulH S s γ y)) : UlK S i q γ ∧ UlK S i q y := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  have hκV : S.InR (Om (s + 1 + 1)) := InR_Om_succ (s + 1)
  have hi : i < ω := his.trans hs
  have hs1 : s + 1 < ω := Ui.ui_s1_lt_omega hs
  have hqΛ : q ≤ S.Lam := us_qΛ hi hqL
  have hyW : y < Om (s + 1) := (ulH_le_self γ y).trans_lt hW
  have hzB : ulH S s γ y < S.psi S.Lam (Om (s + 1)) := uw_lt_psiLam hqΛ (uw_q_le his hqL _) hz hW
  obtain ⟨Bz, hownz, hBz⟩ := Ui.ui_own_of_SC hs (ulH_SC (S := S) (s := s) γ y) (ulH_gt γ y) hzB
  have hnfz : ulH S s γ (S.psi Bz (Om (s + 1))) ≠ S.psi Bz (Om (s + 1)) := by
    rw [hBz]; intro h; exact hnf ((ulH_normal (S := S) (s := s) γ).strictMono.injective h)
  have hγK : UlK S i q γ := us_lev_K hs his hq hqL hγV hownz hBz.symm hnfz (by rw [hBz]; exact hz)
  refine ⟨hγK, ?_⟩
  rcases uw_base hnf with hc0 | ⟨p, hpf, hpy, -, hcond⟩
  · rcases eq_or_ne y 0 with hy0 | hy0
    · rw [hy0]; exact UlK.zero
    obtain ⟨B0, hown0, hB0K, h0, halt⟩ := uw_fv hs his hq hqL hγV hγN hγK
    have heq := us_run hs hγV hown0 h0 hyW hc0
    rw [zero_add] at heq
    set e := B0 + Om (s + 1) ^ γ * y with hedef
    have hpos : 0 < Om (s + 1) ^ γ * y := mul_pos (Ui.ui_W_pos s γ) (pos_iff_ne_zero.2 hy0)
    have hBe : B0 < e := lt_add_of_pos_right B0 hpos
    have hB0C : B0 ∈ S.CSet e (S.psi e (Om (s + 1))) := (psi_mono hκ hBe.le).2 hown0
    have hγCe : γ ∈ S.CSet e (S.psi e (Om (s + 1))) := by
      rcases halt with hC | hA
      · exact (psi_mono hκ hBe.le).2 hC
      · rw [hA]; exact CSet.psi_mem hBe hκV (Ui.ui_W_mem hs1 _ _) hB0C
    have hyψ : y < S.psi e (Om (s + 1)) := by
      have := hc0 y le_rfl; rwa [zero_add, ← heq] at this
    have hownE : e ∈ S.CSet e (S.psi e (Om (s + 1))) :=
      CSet.add_mem hB0C (ul_Wpow_mem hs hγCe (CSet.of_lt hyψ))
    have heK : UlK S i q e := uoArg hqΛ hκ hownE (by rw [heq]; exact hz) (uw_q_le his hqL e)
    have hsub : UlK S i q (Om (s + 1) ^ γ * y) := by
      have := (ulK_dec hq e heK).1 B0 hB0K hBe.le
      rwa [hedef, Ordinal.add_sub_cancel] at this
    have hWγK : UlK S i q (Om (s + 1) * γ) := by
      have := ulK_opow_mul hq (us_K_Om hs) γ hγK; rwa [Ui.ui_W_opow s] at this
    have hdiv := ulK_div hq _ hsub _ hWγK
    rwa [← Ui.ui_W_eq s γ, Ordinal.mul_div_cancel y (Ui.ui_W_pos s γ).ne'] at hdiv
  · have hpB : p < S.psi S.Lam (Om (s + 1)) := hpy.trans ((ulH_le_self γ y).trans_lt hzB)
    have hpSC : SC p := by rw [← hpf]; exact ulH_SC γ p
    have hpL : Om s < p := by rw [← hpf]; exact ulH_gt γ p
    obtain ⟨Bp, hownp, hBp⟩ := Ui.ui_own_of_SC hs hpSC hpL hpB
    have hD0 : y - p ≠ 0 := fun h => absurd (Ordinal.sub_eq_zero_iff_le.1 h) (not_le.2 hpy)
    have hD : y - p < Om (s + 1) := (Ordinal.sub_le_self y p).trans_lt hyW
    have hfix : ulH S s γ (S.psi Bp (Om (s + 1))) = S.psi Bp (Om (s + 1)) := by rw [hBp]; exact hpf
    have hcond' : ∀ d, d ≤ y - p → d < ulH S s γ (S.psi Bp (Om (s + 1)) + d) := by rw [hBp]; exact hcond
    have hiff := us_vis_fix hs his hq hqL hγV hownp hfix hD0 hD hcond'
    rw [hBp, Ordinal.add_sub_cancel_of_le hpy.le] at hiff
    obtain ⟨-, hpK, hDK⟩ := hiff.1 hz
    have := UlK.add hpK hDK
    rwa [Ordinal.add_sub_cancel_of_le hpy.le] at this

/-- **(L1), forward**: `γ, y ∈ K^{(i)}_q` give `Hˡ_γ(y) ∈ K^{(i)}_q` when `Hˡ_γ(y) ≠ y` and `y < W` (level `γ < V` of
the notation, `i < s`, `q` strongly critical, `q ≤ Ω_{i+1}`). -/
theorem uw_L1_mpr (hs : s < ω) {i q γ y : Ordinal.{0}} (his : i < s) (hq : SC q) (hqL : q ≤ Om (i + 1))
    (hγV : γ < Om (s + 1 + 1)) (hγN : γ ∈ ⋃ a, S.CSet a 0) (hyW : y < Om (s + 1)) (hnf : ulH S s γ y ≠ y)
    (hγK : UlK S i q γ) (hyK : UlK S i q y) : UlK S i q (ulH S s γ y) := by
  have hi : i < ω := his.trans hs
  have hqΛ : q ≤ S.Lam := us_qΛ hi hqL
  rcases uw_base hnf with hc0 | ⟨p, hpf, hpy, hmax, hcond⟩
  · obtain ⟨B0, hown0, hB0K, h0, -⟩ := uw_fv hs his hq hqL hγV hγN hγK
    have heq := us_run hs hγV hown0 h0 hyW hc0
    rw [zero_add] at heq
    rw [← heq]; exact us_run_K' hs his.ne hq hB0K hγK hyK
  · have hpK : UlK S i q p := uw_fc_max hs his hq hqL hγV hyK hyW hpf hpy.le hmax
    have hpW : p < Om (s + 1) := hpy.trans hyW
    have hpB : p < S.psi S.Lam (Om (s + 1)) := uw_lt_psiLam hqΛ (uw_q_le his hqL _) hpK hpW
    have hpSC : SC p := by rw [← hpf]; exact ulH_SC γ p
    have hpL : Om s < p := by rw [← hpf]; exact ulH_gt γ p
    obtain ⟨Bp, hownp, hBp⟩ := Ui.ui_own_of_SC hs hpSC hpL hpB
    have hD0 : y - p ≠ 0 := fun h => absurd (Ordinal.sub_eq_zero_iff_le.1 h) (not_le.2 hpy)
    have hD : y - p < Om (s + 1) := (Ordinal.sub_le_self y p).trans_lt hyW
    have hfix : ulH S s γ (S.psi Bp (Om (s + 1))) = S.psi Bp (Om (s + 1)) := by rw [hBp]; exact hpf
    have hcond' : ∀ d, d ≤ y - p → d < ulH S s γ (S.psi Bp (Om (s + 1)) + d) := by rw [hBp]; exact hcond
    have hiff := us_vis_fix hs his hq hqL hγV hownp hfix hD0 hD hcond'
    rw [hBp, Ordinal.add_sub_cancel_of_le hpy.le] at hiff
    exact hiff.2 ⟨hγK, hpK, (ulK_dec hq y hyK).1 p hpK hpy.le⟩

/-- **(L1)**: for `i < s`, `q` strongly critical, `q ≤ Ω_{i+1}`, a level `γ < V` of the notation and an index `y` with
`Hˡ_γ(y) ≠ y` and `Hˡ_γ(y) < W`: `Hˡ_γ(y) ∈ K^{(i)}_q ↔ γ ∈ K^{(i)}_q ∧ y ∈ K^{(i)}_q`. -/
theorem uw_L1 (hs : s < ω) {i q γ y : Ordinal.{0}} (his : i < s) (hq : SC q) (hqL : q ≤ Om (i + 1))
    (hγV : γ < Om (s + 1 + 1)) (hγN : γ ∈ ⋃ a, S.CSet a 0) (hW : ulH S s γ y < Om (s + 1))
    (hnf : ulH S s γ y ≠ y) : UlK S i q (ulH S s γ y) ↔ UlK S i q γ ∧ UlK S i q y :=
  ⟨uw_L1_mp hs his hq hqL hγV hγN hW hnf, fun h =>
    uw_L1_mpr hs his hq hqL hγV hγN ((ulH_le_self γ y).trans_lt hW) hnf h.1 h.2⟩

end Googology.Trans.PoR.InaccPsi.R2.Uw
