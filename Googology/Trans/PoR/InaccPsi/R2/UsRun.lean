import Googology.Trans.PoR.InaccPsi.R2.UsFix

/-!
# The run of a lifted level from any value base, and the visibility of its data one threshold down

`W = Ω_{s+1}`, `V = Ω_{s+2}` (`s` finite), `ψ = S.psi · W`, `Hˡ_γ = Ul.ulH S s γ`, *own*: `B ∈ Cl(B, ψ B)`.
`Uo.uo_eq_all` starts a run `ψ(B + W^γ·D) = Hˡ_γ(c + D)` at a base `ψ(B) = Hˡ_γ(c)` with `γ ∈ Cl(B, ψ B)`; by
`Us.us_val_le` every value base has `γ ≤ ψ_V(B)`, and the case `γ = ψ_V(B)` (the first value of an atom level,
`Us.us_bv_atom`) is the one `uo_eq_all` does not cover.  Here:

* `us_dvd_val` (`W^γ ∣ B` for a value base), `us_second` (**the second value**: for a value base with `γ = ψ_V(B)`,
  `ψ(B + W^γ) = Hˡ_γ(c + 1)` and `B + W^γ` is own), `us_run` (**the run from every value base**: `ψ(B + W^γ·D) =
  Hˡ_γ(c + D)` for own `B`, `ψ(B) = Hˡ_γ(c)`, `γ < V`, `D < W` valid; no hull hypothesis);
* `us_run_K` (**reading the data back one threshold down**: for `i < s`, `q` strongly critical, `q ≤ Ω_{i+1}`, an
  own `e = B + W^γ·D` with `W^{γ+1} ∣ B`, `0 < D < W`: if `ψ(e) ∈ K^{(i)}_q` then `γ`, `D`, `B`
  and `ψ(B)` are in `K^{(i)}_q`), `us_run_K'` (the converse: `B, γ, D ∈ K^{(i)}_q` give `ψ(B + W^γ·D) ∈ K^{(i)}_q`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Us

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Uo
  Googology.Trans.PoR.InaccPsi.R2.Uc

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

/-- `W^γ ∣ B` for an own `B` whose collapse is a value of `Hˡ_γ`. -/
theorem us_dvd_val (hs : s < ω) {B γ c : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om (s + 1))))
    (hc : ulH S s γ c = S.psi B (Om (s + 1))) : Om (s + 1) ^ γ ∣ B :=
  us_dvd_range hs hown fun _ hj hd => ucG_fix_lower hj ⟨c, hc⟩ hd

/-- **The second value at an atom base**: for own `B` with `ψ(B) = Hˡ_γ(c)` and `γ = ψ_V(B)`: `B + W^γ` is own, `γ ∈
Cl(B + W^γ, ψ(B + W^γ))`, and `ψ(B + W^γ) = Hˡ_γ(c + 1)`. -/
theorem us_second (hs : s < ω) {B γ c : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om (s + 1))))
    (hc : ulH S s γ c = S.psi B (Om (s + 1))) (hγ : γ = S.psi B (Om (s + 1 + 1))) :
    B + Om (s + 1) ^ γ ∈ S.CSet (B + Om (s + 1) ^ γ) (S.psi (B + Om (s + 1) ^ γ) (Om (s + 1))) ∧
      γ ∈ S.CSet (B + Om (s + 1) ^ γ) (S.psi (B + Om (s + 1) ^ γ) (Om (s + 1))) ∧
      S.psi (B + Om (s + 1) ^ γ) (Om (s + 1)) = ulH S s γ (c + 1) := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  have hκV : S.InR (Om (s + 1 + 1)) := InR_Om_succ (s + 1)
  have hs1 : s + 1 < ω := Ui.ui_s1_lt_omega hs
  set B1 := B + Om (s + 1) ^ γ with hB1def
  have hγV : γ < Om (s + 1 + 1) := by rw [hγ]; exact Ui.ui_psi_lt B
  have hdvd : Om (s + 1) ^ γ ∣ B := us_dvd_val hs hown hc
  have hBB1 : B < B1 := lt_add_of_pos_right B (Ui.ui_W_pos s γ)
  have hBC : B ∈ S.CSet B1 (S.psi B1 (Om (s + 1))) := (psi_mono hκ hBB1.le).2 hown
  have hγC : γ ∈ S.CSet B1 (S.psi B1 (Om (s + 1))) := by
    rw [hγ]; exact CSet.psi_mem hBB1 hκV (Ui.ui_W_mem hs1 _ _) hBC
  have hown1 : B1 ∈ S.CSet B1 (S.psi B1 (Om (s + 1))) := by
    have hW := ul_Wpow_mem (S := S) hs hγC (CSet.one_mem _ _)
    rw [mul_one] at hW
    exact CSet.add_mem hBC hW
  refine ⟨hown1, hγC, ?_⟩
  have hSC1 : SC (S.psi B1 (Om (s + 1))) := Ui.ui_psi_SC B1
  -- (i) `ψ(B₁)` is a value of `Hˡ_γ` above `Hˡ_γ(c)`
  have hR : ∃ o, ulH S s γ o = S.psi B1 (Om (s + 1)) := by
    refine ucG_range (d := ulD S s) (L := Om s) (μ := γ) hSC1 (Ui.ui_L_lt_psi B1)
      ((ul_vis hSC1).2 (ul_K_of_mem hγC)) fun j hj hdj => ?_
    have hjV : j < S.psi B1 (Om (s + 1 + 1)) :=
      hj.trans_le (by rw [hγ]; exact (psi_mono hκV hBB1.le).1)
    have hjC := uoDV hs B1 j hown1 ((ul_vis hSC1).1 hdj) hjV
    have hd1 : Om (s + 1) ^ (j + 1) ∣ B1 :=
      dvd_add ((opow_dvd_opow _ (Order.add_one_le_of_lt hj)).trans hdvd)
        (opow_dvd_opow _ (Order.add_one_le_of_lt hj))
    exact uo_fwd hs j (hj.trans hγV) B1 hown1 hd1 (hBB1.trans_le' zero_le).ne' hjC
  obtain ⟨o, ho⟩ := hR
  have hlt : S.psi B (Om (s + 1)) < S.psi B1 (Om (s + 1)) := Ui.ui_psi_lt_of_own hown hBB1
  have hco : c < o := by
    rw [← hc, ← ho] at hlt; exact (ulH_lt_iff (S := S) (s := s) γ).1 hlt
  apply le_antisymm _ (by rw [← ho]; exact (ulH_le_iff (S := S) (s := s) γ).2 (Order.add_one_le_of_lt hco))
  -- (ii) no value of `Hˡ_γ` strictly between
  refine not_lt.1 fun hu => ?_
  set u := ulH S s γ (c + 1) with hudef
  have huSC : SC u := ulH_SC γ _
  obtain ⟨e, hown_e, he⟩ := Ui.ui_own_of_SC hs huSC (ulH_gt γ _) hu
  have heB1 : e < B1 := (Ui.ui_own_lt_iff hown_e hown1).1 (by rw [he]; exact hu)
  have hBe : B < e := by
    refine (Ui.ui_own_lt_iff hown hown_e).1 ?_
    rw [he, ← hc]; exact (ulH_lt_iff (S := S) (s := s) γ).2 (Order.lt_add_one_iff.2 le_rfl)
  have hde : Om (s + 1) ^ γ ∣ e := us_dvd_val hs hown_e (c := c + 1) (by rw [he])
  have hsplit : e = B + (e - B) := (Ordinal.add_sub_cancel_of_le hBe.le).symm
  have hd2 : Om (s + 1) ^ γ ∣ e - B := by
    have := hde; rw [hsplit] at this; exact (Ordinal.dvd_add_iff hdvd).1 this
  have hpos : e - B ≠ 0 := by
    intro h0; rw [h0, add_zero] at hsplit; exact absurd hsplit hBe.ne'
  have hsmall : e - B < Om (s + 1) ^ γ := by
    have := heB1; rw [hsplit] at this; exact (add_lt_add_iff_left B).1 this
  exact absurd (Ordinal.le_of_dvd hpos hd2) (not_le.2 hsmall)

/-- **The run from every value base**: for own `B` with `ψ(B) = Hˡ_γ(c)`, `γ < V`, `D < W` and `d < Hˡ_γ(c + d)` for
every `d ≤ D`: `ψ(B + W^γ·D) = Hˡ_γ(c + D)`. -/
theorem us_run (hs : s < ω) {γ B c D : Ordinal.{0}} (hγV : γ < Om (s + 1 + 1))
    (hown : B ∈ S.CSet B (S.psi B (Om (s + 1)))) (hc : ulH S s γ c = S.psi B (Om (s + 1)))
    (hD : D < Om (s + 1)) (hcond : ∀ d, d ≤ D → d < ulH S s γ (c + d)) :
    S.psi (B + Om (s + 1) ^ γ * D) (Om (s + 1)) = ulH S s γ (c + D) := by
  have hdvd : Om (s + 1) ^ γ ∣ B := us_dvd_val hs hown hc
  have hSC := Ui.ui_psi_SC (S := S) (s := s) B
  rcases (us_val_le hs hown hc).lt_or_eq with hlt | heq
  · have hK : UlK S s (S.psi B (Om (s + 1))) γ := (ul_vis hSC).1 (by rw [← hc]; exact ulH_D_lt γ c)
    exact (uo_eq_all hs hγV hown hdvd (uoDV hs B γ hown hK hlt) hc hD hcond).2
  rcases eq_or_ne D 0 with hD0 | hD0
  · rw [hD0, mul_zero, add_zero, add_zero, hc]
  obtain ⟨hown1, hγC, h1⟩ := us_second hs hown hc heq
  have h1D : 1 ≤ D := one_le_iff_ne_zero.2 hD0
  set D' := D - 1 with hD'def
  have hDD : 1 + D' = D := Ordinal.add_sub_cancel_of_le h1D
  have hD'W : D' < Om (s + 1) := (Ordinal.sub_le_self D 1).trans_lt hD
  have hd1 : Om (s + 1) ^ γ ∣ B + Om (s + 1) ^ γ := dvd_add hdvd dvd_rfl
  have hcond' : ∀ d, d ≤ D' → d < ulH S s γ (c + 1 + d) := fun d hd => by
    have h := hcond (1 + d) (by rw [← hDD]; exact add_le_add_right hd 1)
    rw [← add_assoc] at h
    exact le_add_self.trans_lt h
  have h := (uo_eq_all hs hγV hown1 hd1 hγC h1.symm hD'W hcond').2
  rw [add_assoc B, ← mul_one_add, hDD, add_assoc c, hDD] at h
  exact h

/-! ## The data one threshold down -/

theorem us_W_ne_Om {i : Ordinal.{0}} (hi : i ≠ s) : Om (s + 1) ≠ Om (i + 1) := fun h => by
  have h1 : Order.succ s = Order.succ i := by rw [Order.succ_eq_add_one, Order.succ_eq_add_one]; exact Om_inj.1 h
  exact hi (Order.succ_injective h1).symm

/-- `W^γ·D ∈ K^{(i)}_q` and `W^{γ+1}·(e / W^{γ+1}) ∈ K^{(i)}_q` from their parts (any threshold `i`). -/
theorem us_K_Wmul {i q γ D : Ordinal.{0}} (hs : s < ω) (hq : SC q) (hγ : UlK S i q γ) (hD : UlK S i q D) :
    UlK S i q (Om (s + 1) ^ γ * D) := by
  have hW : UlK S i q (Om (s + 1)) := us_K_Om hs
  have hWγ : UlK S i q (Om (s + 1) * γ) := by
    have := ulK_opow_mul hq hW γ hγ
    rwa [Ui.ui_W_opow s] at this
  rw [Ui.ui_W_eq s]; exact ulK_opow_mul hq hWγ D hD

/-- **Reading the run back one threshold down**: for `i < s`, `q` strongly critical, `q ≤ Ω_{i+1}`, and
an own `e = B + W^γ·D` with `W^{γ+1} ∣ B` and `0 < D < W`: if `ψ(e) ∈ K^{(i)}_q`, then `γ`, `D`, `B` and `ψ(B)` are
in `K^{(i)}_q`. -/
theorem us_run_K (hs : s < ω) {i q B γ D : Ordinal.{0}} (his : i < s) (hq : SC q)
    (hqL : q ≤ Om (i + 1)) (hown : B + Om (s + 1) ^ γ * D ∈
      S.CSet (B + Om (s + 1) ^ γ * D) (S.psi (B + Om (s + 1) ^ γ * D) (Om (s + 1))))
    (hB : Om (s + 1) ^ (γ + 1) ∣ B) (hD0 : D ≠ 0) (hD : D < Om (s + 1))
    (hz : UlK S i q (S.psi (B + Om (s + 1) ^ γ * D) (Om (s + 1)))) :
    UlK S i q γ ∧ UlK S i q D ∧ UlK S i q B ∧ UlK S i q (S.psi B (Om (s + 1))) := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  have hi : i < ω := his.trans hs
  have hqΛ : q ≤ S.Lam := hqL.trans (lt_Lam_of_mem zero_le (Ui.ui_W_mem hi 0 0)).le
  set e := B + Om (s + 1) ^ γ * D with hedef
  have hWγ0 : Om (s + 1) ^ γ ≠ 0 := (Ui.ui_W_pos s γ).ne'
  have hdig : e / Om (s + 1) ^ γ % Om (s + 1) = D := by
    obtain ⟨t, ht⟩ := hB
    have e1 : e = Om (s + 1) ^ γ * (Om (s + 1) * t + D) := by
      rw [hedef, ht, Ui.ui_W_succ s, mul_add, mul_assoc]
    rw [e1, Ordinal.mul_div_cancel _ hWγ0, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hD]
  have heK : UlK S i q e := by
    have hqψ : q ≤ S.psi e (Om (s + 1)) := hqL.trans (by
      have h1 : Om (i + 1) ≤ Om s := Om_le_Om.2 (Order.add_one_le_of_lt his)
      exact h1.trans (Ui.ui_L_lt_psi e).le)
    exact uoArg hqΛ hκ hown hz hqψ
  have hγK : UlK S i q γ := us_dig_exp hs hq heK γ (by rw [hdig]; exact hD0)
  have hDK : UlK S i q D := by
    have hW : UlK S i q (Om (s + 1)) := us_K_Om hs
    have hWγ : UlK S i q (Om (s + 1) * γ) := by
      have := ulK_opow_mul hq hW γ hγK; rwa [Ui.ui_W_opow s] at this
    have h1 : UlK S i q (e / Om (s + 1) ^ γ) := by rw [Ui.ui_W_eq s]; exact ulK_div hq e heK _ hWγ
    have h2 := ulK_mod hq _ h1 (Om (s + 1))
    rwa [Ui.ui_W_opow s, hdig] at h2
  have hBK : UlK S i q B := by
    have hW : UlK S i q (Om (s + 1)) := us_K_Om hs
    have hγ1 : UlK S i q (γ + 1) := UlK.add hγK UlK.one
    have hWγ1 : UlK S i q (Om (s + 1) * (γ + 1)) := by
      have := ulK_opow_mul hq hW (γ + 1) hγ1; rwa [Ui.ui_W_opow s] at this
    have hBeq : B = Om (s + 1) ^ (γ + 1) * (e / Om (s + 1) ^ (γ + 1)) := by
      obtain ⟨t, ht⟩ := hB
      have hpos : Om (s + 1) ^ (γ + 1) ≠ 0 := (Ui.ui_W_pos s _).ne'
      have hlt : Om (s + 1) ^ γ * D < Om (s + 1) ^ (γ + 1) := by
        rw [Ui.ui_W_succ s]; exact (mul_lt_mul_iff_right₀ (Ui.ui_W_pos s γ)).2 hD
      have : e / Om (s + 1) ^ (γ + 1) = t := by
        rw [hedef, ht, Ordinal.mul_add_div _ hpos, Ordinal.div_eq_zero_of_lt hlt, add_zero]
      rw [this, ht]
    rw [hBeq, Ui.ui_W_eq s]
    exact ulK_opow_mul hq hWγ1 _ (ulK_div hq e heK _ hWγ1)
  exact ⟨hγK, hDK, hBK, UlK.coll hκ (us_W_ne_Om his.ne) (us_K_Om hs) hBK⟩

/-- **The converse**: `B, γ, D ∈ K^{(i)}_q` give `ψ_W(B + W^γ·D) ∈ K^{(i)}_q` (`i ≠ s`). -/
theorem us_run_K' (hs : s < ω) {i q B γ D : Ordinal.{0}} (his : i ≠ s) (hq : SC q) (hB : UlK S i q B)
    (hγ : UlK S i q γ) (hD : UlK S i q D) : UlK S i q (S.psi (B + Om (s + 1) ^ γ * D) (Om (s + 1))) :=
  UlK.coll (InR_Om_succ s) (us_W_ne_Om his) (us_K_Om hs) (UlK.add hB (us_K_Wmul hs hq hγ hD))

end Googology.Trans.PoR.InaccPsi.R2.Us
