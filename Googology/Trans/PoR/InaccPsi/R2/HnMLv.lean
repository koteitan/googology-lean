import Googology.Trans.PoR.InaccPsi.R2.HnWG

/-!
# HnMLv: THE BAND LEVEL DATUM `Ω₁·Ω₁ + Ω₁·M` READ AS `x·x + x·M`, FOR EVERY `M < Ω₁`

The level `Ω₁·Ω₁ + Ω₁·M` (`M < Ω₁`) is read as `x·x + x·M` (`Hm.hmBandLevel`); Lemma EXACT is `Hm.hmLayer_exact`
(needs `M < σ`), so the datum is gated as `Hl.hlMLv`: gate `Hl.hlGt M` (`0` for `M < ε₀`, `M` otherwise), reading
`x·x` at or below the gate.  The code gate: a code `y ∈ [Ω₁·Ω₁ + Ω₁·M, Ω₁·Ω₁·2)` over a strongly critical `Z` has
`M ≤ (y mod Ω₁²)/Ω₁ < Z` (`hn_band_coef_ge`, `Hm.hmSq_gate_cube_remcoef`) — this is the field `g_cl` of `Hn.HnLv` with
the band `u = Ω₁`, built from `Hm.HmBandLv` / `Hm.hmBandLevel`.

* `hn_band_coef_ge`, `hn_band_cl` (**THE BAND GATE `M < Z` FROM A CODE IN THE BAND**);
* `hnRd`, `hnMLv M` (**THE BAND LEVEL DATUM**), `hnMLv_L`, `hnMLv_l`, `hnMLv_g`;
* `hn_NB_of` (`ℓ(x) + x < x·x·2` for a reading `x·x + x·μ` whose gate forces `μ < x`), `hnMLv_NB`;
* `hn_cof1` (cofinality of `A + a·M_k` in `A + a·M`).

What differs from `Hl.hlMLv`: the band prefix `Ω₁·Ω₁` (reading `x·x`), the code gate over `[L, Ω₁·Ω₁·2)` from the band
coefficient, the hull membership through `Hl.hl_OO_mem`.  No new axiom.  New definitions: `hnRd`, `hnMLv`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hn

open Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The band coefficient -/

/-- **On `[Ω₁·Ω₁ + Ω₁·M, Ω₁·Ω₁·2)` the `Ω₁`-coefficient of the remainder mod `Ω₁²` is at least `M`.** -/
theorem hn_band_coef_ge {M y : Ordinal.{0}} (hlo : Om 1 * Om 1 + Om 1 * M ≤ y)
    (hhi : y < Om 1 * Om 1 + Om 1 * Om 1) : M ≤ (y % (Om 1 * Om 1)) / Om 1 := by
  have hΩ : 0 < Om 1 := gw_Om_pos
  have hB0 : Om 1 * Om 1 ≠ 0 := (mul_pos hΩ hΩ).ne'
  have hq : y / (Om 1 * Om 1) = 1 := by
    apply le_antisymm
    · have hlt : y / (Om 1 * Om 1) < 2 := by
        apply (Ordinal.lt_mul_iff_div_lt hB0).1
        rwa [mul_two_eq]
      exact (Order.lt_succ_iff).1 (by simpa using hlt)
    · exact (Ordinal.le_div hB0).2 (by rw [mul_one]; exact le_self_add.trans hlo)
  have hd := Ordinal.div_add_mod y (Om 1 * Om 1)
  rw [hq, mul_one] at hd
  rw [← hd] at hlo
  exact (Ordinal.le_div hΩ.ne').2 ((add_le_add_iff_left _).1 hlo)

/-- **THE BAND GATE**: a code `y ∈ [Ω₁·Ω₁ + Ω₁·M, Ω₁·Ω₁·2)` over a strongly critical `Z ≤ Ω₁` has `M < Z`. -/
theorem hn_band_cl {Z y M : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (hy : GxCl Z {gcG 0} y)
    (hlo : Om 1 * Om 1 + Om 1 * M ≤ y) (hhi : y < Om 1 * Om 1 + Om 1 * Om 1) : M < Z :=
  (hn_band_coef_ge hlo hhi).trans_lt (Hm.hmSq_gate_cube_remcoef hZ hZ1 hy)

/-! ## The band level datum -/

open Classical in
/-- **The reading of the band level `Ω₁·Ω₁ + Ω₁·M`**: `x·x + x·M` above the gate, `x·x` at or below it. -/
noncomputable def hnRd (M x : Ordinal.{0}) : Ordinal.{0} := if hlGt M < x then x * x + x * M else x * x

theorem hnRd_eq {M x : Ordinal.{0}} (h : hlGt M < x) : hnRd M x = x * x + x * M := by unfold hnRd; rw [if_pos h]

theorem hn_OOM_lt {M : Ordinal.{0}} (hM : M < Om1) (α : Ordinal.{0}) : (Om1 : Ordinal.{0}) * Om1 + Om1 * M < gcG α :=
  (inE_indec (Low.opow_eq_self_of_SC (gcG_SC α))).add_lt (hl_OO_lt_G α)
    (InE.mul_lt (Low.opow_eq_self_of_SC (gcG_SC α)) (hg_Om1_lt_G α) (hM.trans (hg_Om1_lt_G α)))

/-- **THE BAND LEVEL DATUM `Ω₁·Ω₁ + Ω₁·M`, READ AS `x·x + x·M`** (above the gate `hlGt M`), for `M < Ω₁`. -/
noncomputable def hnMLv (M : Ordinal.{0}) (hM : M < Om1) : HnLv where
  L := Om1 * Om1 + Om1 * M
  l := hnRd M
  u := Om1
  q := M
  g := hlGt M
  g_lt := (hlGt_le M).trans_lt hM
  q_lt := hM
  OL := (le_mul_of_one_le_right' hg_one_lt_Om1.le).trans le_self_add
  L_G := hn_OOM_lt hM 0
  L_eq := by rw [← Br.Om1_eq]
  g_cl := fun _ y hZ hZ1 hy hMy hy2 => (hlGt_le M).trans_lt (hn_band_cl hZ hZ1 hy
    (by simpa only [Br.Om1_eq] using hMy) (by simpa only [Br.Om1_eq] using hy2))
  L_mem := fun S a b ha hb => by
    refine CSet.add_mem (hl_OO_mem S a b) ?_
    by_cases he : M < ε₀
    · exact hk_mul_mem S a b M he
    · unfold hlGt at hb; rw [if_neg he] at hb; exact hl_mul_mem S a b M hb
  l_ge := fun x => by
    unfold hnRd; split_ifs
    · exact (hn_le_sq x).trans le_self_add
    · exact hn_le_sq x
  l_lt := fun x hx hx1 => by
    unfold hnRd; split_ifs with h
    · exact (inE_indec (lgG_facts hx hx1).2.2.2.1).add_lt (hl_sq_lt hx hx1)
        (InE.mul_lt (lgG_facts hx hx1).2.2.2.1 (lgG_facts hx hx1).2.1 ((hl_gt_E hx h).trans (lgG_facts hx hx1).2.1))
    · exact hl_sq_lt hx hx1
  l_pi := fun σ ρ hB hg => by
    rw [hnRd_eq hg, hnRd_eq (hg.trans hB.2.2.1)]
    exact Hm.hmLayer_exact hB (hl_gt_E hB.1 hg)

theorem hnMLv_L (M : Ordinal.{0}) (hM : M < Om1) : (hnMLv M hM).L = Om1 * Om1 + Om1 * M := rfl

theorem hnMLv_l (M : Ordinal.{0}) (hM : M < Om1) {x : Ordinal.{0}} (hx : hlGt M < x) :
    (hnMLv M hM).l x = x * x + x * M := hnRd_eq hx

theorem hnMLv_g (M : Ordinal.{0}) (hM : M < Om1) : (hnMLv M hM).g = hlGt M := rfl

/-! ## The outer-field bound -/

/-- **`ℓ(x) + x < x·x·2`** for a reading `x·x + x·μ` whose gate forces `μ < x`. -/
theorem hn_NB_of {Λ : HnLv} {μ : Ordinal.{0}} (hμ : ∀ x, InE x → Λ.g < x → μ < x)
    (hl : ∀ x, Λ.g < x → Λ.l x = x * x + x * μ) : HnNB Λ := fun x hx _ hg => by
  rw [hl x hg]
  have hμx := hμ x hx hg
  have hlx := ev_isSuccLimit_of_inE hx
  calc x * x + x * μ + x < x * x + x * (μ + 2) := Hm.hmLayer_next_bound hx
  _ < x * x + x * x := (add_lt_add_iff_left _).2 (mul_lt_mul_of_pos_left
      (by rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, ← add_assoc]
          exact hlx.add_one_lt (hlx.add_one_lt hμx)) hx.pos)
  _ = x * x * 2 := (mul_two_eq _).symm

theorem hnMLv_NB (M : Ordinal.{0}) (hM : M < Om1) : HnNB (hnMLv M hM) :=
  hn_NB_of (fun _ hx hg => hl_gt_E hx hg) (fun _ hg => hnMLv_l M hM hg)

/-! ## Cofinality with a prefix -/

theorem hn_sq_succ {x b : Ordinal.{0}} (hx : InE x) (hb : b < x * x) : b + 1 < x * x :=
  (hl_sq_indec hx).add_lt hb ((one_lt_omega0.trans (omega0_lt_inE hx)).trans (hl_lt_sq hx))

/-- **`A + a·M_k` is cofinal in `A + a·M`** (`A` closed under successor, `M_k` cofinal in `M`):
`b < A + a·M ⇒ b + 1 < A + a·M_k`. -/
theorem hn_cof1 {A a b M : Ordinal.{0}} {Ms : ℕ → Ordinal.{0}} (hA : ∀ b, b < A → b + 1 < A) (ha : 0 < a)
    (hmono : ∀ k, Ms k < Ms (k + 1)) (hcof : ∀ t, t < M → ∃ k, t < Ms k) (hb : b < A + a * M) :
    ∃ k, b + 1 < A + a * Ms k := by
  rcases lt_or_ge b A with h | h
  · exact ⟨0, (hA b h).trans_le le_self_add⟩
  · obtain ⟨b', rfl⟩ := exists_add_of_le h
    have hb' : b' < a * M := (add_lt_add_iff_left A).1 hb
    obtain ⟨k, hk⟩ := hk_mul_cof1 ha hmono hcof hb'
    exact ⟨k, by rw [add_assoc]; exact (add_lt_add_iff_left A).2 hk⟩

end Googology.Trans.PoR.InaccPsi.R2.Hn
