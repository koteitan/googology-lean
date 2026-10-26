import Googology.Trans.PoR.InaccPsi.R2.UwN

/-!
# (FV): the first value of a lifted level is visible one threshold down

`W = Ω_{s+1}`, `V = Ω_{s+2}` (`s` finite), `ψ = S.psi · W`, `ψ_V = S.psi · V`, `Hˡ_γ = Ul.ulH S s γ`; `i < s`,
`X = Ul.UlK S i q` (`q` strongly critical, `q ≤ Ω_{i+1}`); *own* means own at `W`: `e ∈ Cl(e, ψ e)`.  For a level
`γ < V` of the notation (`γ ∈ ⋃ a, Cl(a, 0)`):

* `uw_hull_iff` (**`γ ∈ Cl(e, ψ e) ↔ ulDat W γ < ψ(e) ∧ γ < ψ_V(e)`** for own `e`);
* `uw_supp` (**the support of `γ`**: for `γ ∈ X` some own `e₀ ∈ X` has `γ ∈ Cl(e, ψ e) ↔ e₀ ≤ e` for every own `e`;
  `e₀ = max(e_d, M(e_V))` with `e_d` the least collapse above the datum `d = ulDat W γ` and `e_V` the least
  `ψ_V`-collapse above `γ`, both from `Uw.uw_next`);
* `uw_round` (**the rounding to a multiple of `W^γ`**: `x = e₀` if `W^γ ∣ e₀ ≠ 0`, else `x = W^γ·(e₀ / W^γ) + W^γ`;
  `x` is own, in `X`, nonzero, divisible by `W^γ`, `≥ e₀`, and below every nonzero multiple of `W^γ` that is `≥ e₀`);
* `uw_fv` (**(FV)**: for `γ ∈ X` of the notation, `γ < V`, `Hˡ_γ(0) = ψ(x)` with `x` own, `x ∈ X`, and `γ ∈ Cl(x, ψ x)`
  or `γ = ψ_V(x)`), `uw_fv_K` (**`Hˡ_γ(0) ∈ X`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul
  Googology.Trans.PoR.InaccPsi.R2.Uo Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Us

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

/-- **The hull test for a level `γ < V` of the notation**: for own `e`,
`γ ∈ Cl(e, ψ e) ↔ ulDat W γ < ψ(e) ∧ γ < ψ_V(e)`. -/
theorem uw_hull_iff (hs : s < ω) {γ e : Ordinal.{0}} (hγV : γ < Om (s + 1 + 1)) (hγN : γ ∈ ⋃ a, S.CSet a 0)
    (hown : e ∈ S.CSet e (S.psi e (Om (s + 1)))) :
    γ ∈ S.CSet e (S.psi e (Om (s + 1))) ↔
      ulDat S (Om (s + 1)) γ < S.psi e (Om (s + 1)) ∧ γ < S.psi e (Om (s + 1 + 1)) := by
  have hSC := Ui.ui_psi_SC (S := S) (s := s) e
  have hL := Ui.ui_L_lt_psi (S := S) (s := s) e
  have hW := (Ui.ui_psi_lt (S := S) (s := s) e).le
  constructor
  · intro h
    exact ⟨(uo_K_iff_dat hs hSC hL hW hγN).1 (ul_K_of_mem h),
      ul_lt_psiV h le_rfl (ul_psiW_le_psiV (s := s) e e) hγV⟩
  · rintro ⟨h1, h2⟩
    exact uoDV hs e γ hown ((uo_K_iff_dat hs hSC hL hW hγN).2 h1) h2

/-- The larger of two own members. -/
theorem uw_max {P Q : Ordinal.{0} → Prop} {e1 e2 : Ordinal.{0}} (h1 : P e1 ∧ Q e1) (h2 : P e2 ∧ Q e2) :
    P (max e1 e2) ∧ Q (max e1 e2) := by
  rcases le_total e1 e2 with h | h
  · rw [max_eq_right h]; exact h2
  · rw [max_eq_left h]; exact h1

/-- **The support of a level**: for `γ ∈ K^{(i)}_q` of the notation, `γ < V`, some own `e₀ ∈ K^{(i)}_q` has
`γ ∈ Cl(e, ψ e) ↔ e₀ ≤ e` for every own `e`. -/
theorem uw_supp (hs : s < ω) {i q γ : Ordinal.{0}} (his : i < s) (hq : SC q) (hqL : q ≤ Om (i + 1))
    (hγV : γ < Om (s + 1 + 1)) (hγN : γ ∈ ⋃ a, S.CSet a 0) (hγK : UlK S i q γ) :
    ∃ e0, UlK S i q e0 ∧ e0 ∈ S.CSet e0 (S.psi e0 (Om (s + 1))) ∧
      ∀ e, e ∈ S.CSet e (S.psi e (Om (s + 1))) → (γ ∈ S.CSet e (S.psi e (Om (s + 1))) ↔ e0 ≤ e) := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  have hi : i < ω := his.trans hs
  have hqΛ : q ≤ S.Lam := us_qΛ hi hqL
  have hs1 : s + 1 < ω := Ui.ui_s1_lt_omega hs
  obtain ⟨hN, hv⟩ := Bc.bcNf_spec S hγN
  have hdK : UlK S i q (ulDat S (Om (s + 1)) γ) := uw_dat_K his hs hq hqL _ hN (by rw [hv]; exact hγK)
  have hdW : ulDat S (Om (s + 1)) γ < Om (s + 1) := ulDat_lt (Ui.ui_SC_W s).1 γ
  obtain ⟨ed, hedK, hedO, hed⟩ := uw_next hs his hq hqL _ hdK hdW
  obtain ⟨eV, heVK, -, heV⟩ := uw_next (r := s + 1) hs1 (his.trans (lt_add_one s)) hq hqL γ hγK hγV
  have heVL : eV < S.Lam := lt_Lam_of_mem hqΛ (uw_K_CSet hqΛ heVK)
  set m := S.M eV (S.psi eV (Om (s + 1))) eV with hmdef
  have hmK : UlK S i q m := uoM_mem hqΛ heVK (uw_q_le his hqL eV)
  have hmO : m ∈ S.CSet m (S.psi m (Om (s + 1))) := M_mem_self hκ heVL
  obtain ⟨hK0, hO0⟩ := uw_max (P := UlK S i q) (Q := fun e => e ∈ S.CSet e (S.psi e (Om (s + 1))))
    ⟨hedK, hedO⟩ ⟨hmK, hmO⟩
  refine ⟨max ed m, hK0, hO0, fun e he => ?_⟩
  have hownV : e ∈ S.CSet e (S.psi e (Om (s + 1 + 1))) :=
    CSet_mono le_rfl ((Ui.ui_psi_lt e).le.trans (psiS_bounds e (s + 1)).1.le) he
  rw [uw_hull_iff hs hγV hγN he, hed e he, heV e hownV, max_le_iff]
  have hm : eV ≤ e ↔ m ≤ e :=
    ⟨fun h => uw_M_least hκ heVL he h, fun h => (M_spec (e := eV) (g := S.psi eV (Om (s + 1))) heVL).2.trans h⟩
  rw [hm]

/-- **The rounding to a multiple of `W^γ`**: from an own `e₀ ∈ K^{(i)}_q` with `γ ∈ Cl(e₀, ψ e₀)`, `γ ≠ 0`, `γ ∈
K^{(i)}_q`: an own `x ∈ K^{(i)}_q`, `x ≠ 0`, `W^γ ∣ x`, `e₀ ≤ x`, below every nonzero multiple of `W^γ`
that is `≥ e₀`. -/
theorem uw_round (hs : s < ω) {i q γ e0 : Ordinal.{0}} (hq : SC q) (hγ0 : γ ≠ 0) (hγK : UlK S i q γ)
    (he0K : UlK S i q e0) (he0 : e0 ∈ S.CSet e0 (S.psi e0 (Om (s + 1))))
    (hγC : γ ∈ S.CSet e0 (S.psi e0 (Om (s + 1)))) :
    ∃ x, x ∈ S.CSet x (S.psi x (Om (s + 1))) ∧ UlK S i q x ∧ x ≠ 0 ∧ Om (s + 1) ^ γ ∣ x ∧ e0 ≤ x ∧
      ∀ e, e ≠ 0 → Om (s + 1) ^ γ ∣ e → e0 ≤ e → x ≤ e := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  set u := Om (s + 1) ^ γ with hudef
  have hupos : 0 < u := Ui.ui_W_pos s γ
  have hu0 : u ≠ 0 := hupos.ne'
  have hWγK : UlK S i q (Om (s + 1) * γ) := by
    have := ulK_opow_mul hq (us_K_Om hs) γ hγK; rwa [Ui.ui_W_opow s] at this
  have huK : UlK S i q u := by have := us_K_Wmul (S := S) hs hq hγK UlK.one; rwa [mul_one] at this
  by_cases hA : u ∣ e0 ∧ e0 ≠ 0
  · exact ⟨e0, he0, he0K, hA.2, hA.1, le_rfl, fun e _ _ h => h⟩
  set T := u * (e0 / u) with hTdef
  have hdm : T + e0 % u = e0 := Ordinal.div_add_mod e0 u
  have hmlt : e0 % u < u := Ordinal.mod_lt e0 hu0
  have he0x : e0 ≤ T + u := by
    conv_lhs => rw [← hdm]
    exact ((add_lt_add_iff_left T).2 hmlt).le
  have hTK : UlK S i q T := by
    have h1 : UlK S i q (e0 / u) := by rw [hudef, Ui.ui_W_eq s γ]; exact ulK_div hq e0 he0K _ hWγK
    exact us_K_Wmul hs hq hγK h1
  have hmono := psi_mono hκ he0x
  have hγx := hmono.2 hγC
  have he0x' := hmono.2 he0
  have hTx : T ∈ S.CSet (T + u) (S.psi (T + u) (Om (s + 1))) :=
    Ui.ui_mod_mem (one_le_iff_ne_zero.2 hγ0) e0 he0x'
  have hux : u ∈ S.CSet (T + u) (S.psi (T + u) (Om (s + 1))) := by
    have := ul_Wpow_mem hs hγx (CSet.one_mem _ _); rwa [mul_one] at this
  refine ⟨T + u, CSet.add_mem hTx hux, UlK.add hTK huK, (hupos.trans_le le_add_self).ne',
    dvd_add (dvd_mul_right _ _) dvd_rfl, he0x, fun e he hd hle => ?_⟩
  obtain ⟨k, rfl⟩ := hd
  have hk : e0 / u < k := by
    refine not_le.1 fun hk' => ?_
    have h1 : u * k ≤ T := mul_le_mul_right hk' u
    rcases not_and_or.1 hA with hnd | hz
    · have hr0 : e0 % u ≠ 0 := fun h => by
        have he0T : e0 = T := by rw [← hdm, h, add_zero]
        exact hnd ⟨e0 / u, he0T⟩
      have hTe : T < e0 := by
        conv_rhs => rw [← hdm]
        exact lt_add_of_pos_right T (pos_iff_ne_zero.2 hr0)
      exact absurd (hle.trans h1) (not_le.2 hTe)
    · have hz' : e0 = 0 := not_not.1 hz
      rw [hz', Ordinal.zero_div] at hk'
      have hk0 : k = 0 := le_antisymm hk' zero_le
      exact he (by rw [hk0, mul_zero])
  calc T + u = u * (e0 / u + 1) := by rw [mul_add_one]
    _ ≤ u * k := mul_le_mul_right (Order.add_one_le_of_lt hk) u

/-- **(FV) The first value of a lifted level, one threshold down**: for `i < s`, `q` strongly critical, `q ≤ Ω_{i+1}`,
and a level `γ < V` of the notation with `γ ∈ K^{(i)}_q`: `Hˡ_γ(0) = ψ(x)` with `x` own, `x ∈ K^{(i)}_q`, and
`γ ∈ Cl(x, ψ x)` or `γ = ψ_V(x)`. -/
theorem uw_fv (hs : s < ω) {i q γ : Ordinal.{0}} (his : i < s) (hq : SC q) (hqL : q ≤ Om (i + 1))
    (hγV : γ < Om (s + 1 + 1)) (hγN : γ ∈ ⋃ a, S.CSet a 0) (hγK : UlK S i q γ) :
    ∃ x, x ∈ S.CSet x (S.psi x (Om (s + 1))) ∧ UlK S i q x ∧ ulH S s γ 0 = S.psi x (Om (s + 1)) ∧
      (γ ∈ S.CSet x (S.psi x (Om (s + 1))) ∨ γ = S.psi x (Om (s + 1 + 1))) := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  have hκV : S.InR (Om (s + 1 + 1)) := InR_Om_succ (s + 1)
  have hi : i < ω := his.trans hs
  have hqΛ : q ≤ S.Lam := us_qΛ hi hqL
  rcases eq_or_ne γ 0 with rfl | hγ0
  · exact ⟨0, CSet.zero_mem _ _, UlK.zero, us_psi0 hs, Or.inl (CSet.zero_mem _ _)⟩
  obtain ⟨e0, he0K, he0O, he0⟩ := uw_supp hs his hq hqL hγV hγN hγK
  have hγC0 : γ ∈ S.CSet e0 (S.psi e0 (Om (s + 1))) := (he0 e0 he0O).2 le_rfl
  obtain ⟨xs, hxO, hxK, hx0, hxd, hex, hxmin⟩ := uw_round hs hq hγ0 hγK he0K he0O hγC0
  have hγC : γ ∈ S.CSet xs (S.psi xs (Om (s + 1))) := (he0 xs hxO).2 hex
  set b := S.psi xs (Om (s + 1)) with hbdef
  have hbSC : SC b := Ui.ui_psi_SC xs
  have hbL : Om s < b := Ui.ui_L_lt_psi xs
  have hγψ : γ < S.psi xs (Om (s + 1 + 1)) := ul_lt_psiV hγC le_rfl (ul_psiW_le_psiV (s := s) xs xs) hγV
  have hrange : b ∈ range (ulH S s γ) := by
    refine ucG_range (d := ulD S s) (L := Om s) (μ := γ) hbSC hbL ((ul_vis hbSC).2 (ul_K_of_mem hγC))
      fun j hj hdj => ?_
    have hjK : UlK S s b j := (ul_vis hbSC).1 hdj
    have hjC : j ∈ S.CSet xs b := uoDV hs xs j hxO hjK (hj.trans hγψ)
    have hdj : Om (s + 1) ^ (j + 1) ∣ xs := (opow_dvd_opow _ (Order.add_one_le_of_lt hj)).trans hxd
    exact uo_fwd hs j (hj.trans hγV) xs hxO hdj hx0 hjC
  have hle : ulH S s γ 0 ≤ b := by
    obtain ⟨o, ho⟩ := hrange
    rw [← ho]; exact (ulH_le_iff (S := S) (s := s) γ).2 zero_le
  rcases hle.lt_or_eq with hlt | heq
  swap
  · exact ⟨xs, hxO, hxK, heq, Or.inl hγC⟩
  obtain ⟨x, hown, hx⟩ := Ui.ui_own_of_SC hs (ulH_SC (S := S) (s := s) γ 0) (ulH_gt γ 0) hlt
  have hc : ulH S s γ 0 = S.psi x (Om (s + 1)) := hx.symm
  have hxd' : Om (s + 1) ^ γ ∣ x := us_dvd_val hs hown hc
  rcases (us_val_le hs hown hc).lt_or_eq with hγlt | hγeq
  · exfalso
    have hK : UlK S s (S.psi x (Om (s + 1))) γ :=
      (ul_vis (Ui.ui_psi_SC x)).1 (by rw [← hc]; exact ulH_D_lt γ 0)
    have hγCx := uoDV hs x γ hown hK hγlt
    have hx0' : x ≠ 0 := by
      intro h0
      have hp0 : S.psi x (Om (s + 1)) = ulH S s 0 0 := by rw [h0, us_psi0 hs]
      have hf0 := ucG_fix_lower (pos_iff_ne_zero.2 hγ0) ⟨0, hc⟩ ((ulD_le_self 0).trans_lt (Ui.ui_psi_SC x).1)
      rw [hp0] at hf0
      exact us_val0_ne hf0
    have hxx := hxmin x hx0' hxd' ((he0 x hown).1 hγCx)
    exact absurd ((psi_mono hκ hxx).1.trans_lt (hx.trans_lt hlt)) (lt_irrefl _)
  · have hownV : x ∈ S.CSet x (S.psi x (Om (s + 1 + 1))) :=
      CSet_mono le_rfl ((Ui.ui_psi_lt x).le.trans (psiS_bounds x (s + 1)).1.le) hown
    have hxK' : UlK S i q x :=
      uoArg hqΛ hκV hownV (hγeq ▸ hγK) (uw_q_le (his.trans (lt_add_one s)) hqL x)
    exact ⟨x, hown, hxK', hc, Or.inr hγeq⟩

/-- **(FV)**: `γ ∈ K^{(i)}_q ⇒ Hˡ_γ(0) ∈ K^{(i)}_q` for a level `γ < V` of the notation (`i < s`, `q` strongly critical,
`q ≤ Ω_{i+1}`). -/
theorem uw_fv_K (hs : s < ω) {i q γ : Ordinal.{0}} (his : i < s) (hq : SC q) (hqL : q ≤ Om (i + 1))
    (hγV : γ < Om (s + 1 + 1)) (hγN : γ ∈ ⋃ a, S.CSet a 0) (hγK : UlK S i q γ) : UlK S i q (ulH S s γ 0) := by
  obtain ⟨x, -, hxK, hx, -⟩ := uw_fv hs his hq hqL hγV hγN hγK
  rw [hx]; exact UlK.coll (InR_Om_succ s) (us_W_ne_Om his.ne) (us_K_Om hs) hxK

end Googology.Trans.PoR.InaccPsi.R2.Uw
