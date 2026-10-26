import Googology.Trans.PoR.InaccPsi.R2.UzDat

/-!
# (FV) for every level visible one threshold down (no notation hypothesis)

`W = Ω_{s+1}`, `V = Ω_{s+2}` (`s` finite), `ψ = S.psi · W`, `ψ_V = S.psi · V`, `Hˡ_γ = Ul.ulH S s γ`; `i < s`,
`X = Ul.UlK S i q` (`q` strongly critical, `q ≤ Ω_{i+1}`); *own* means own at `W`: `e ∈ Cl(e, ψ e)`.  For every level
`γ ∈ X`, `γ < V` (the parameters of `γ` below `q` are arbitrary; `γ` need not be in `⋃ a, Cl(a, 0)`):

* `uz_hull_iff` (**`γ ∈ Cl(e, ψ e) ↔ γ ∈ K^{(s)}_{ψ(e)} ∧ γ < ψ_V(e)`** for own `e`, every `γ < V`);
* `uz_supp` (**the support of `γ`**: some own `e₀ ∈ X` has `γ ∈ Cl(e, ψ e) ↔ e₀ ≤ e` for every own `e`; the datum of
  `Uz.uz_dat` replaces the normal-form datum of `Uw.uw_supp`);
* `uz_fv` (**(FV)**: `Hˡ_γ(0) = ψ(x)` with `x` own, `x ∈ X`, and `γ ∈ Cl(x, ψ x)` or `γ = ψ_V(x)`), `uz_fv_K`
  (**`Hˡ_γ(0) ∈ X`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul
  Googology.Trans.PoR.InaccPsi.R2.Uo Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Us
  Googology.Trans.PoR.InaccPsi.R2.Uw

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

/-- **The hull test for every level `γ < V`**: for own `e`, `γ ∈ Cl(e, ψ e) ↔ γ ∈ K^{(s)}_{ψ(e)} ∧ γ < ψ_V(e)`. -/
theorem uz_hull_iff (hs : s < ω) {γ e : Ordinal.{0}} (hγV : γ < Om (s + 1 + 1))
    (hown : e ∈ S.CSet e (S.psi e (Om (s + 1)))) :
    γ ∈ S.CSet e (S.psi e (Om (s + 1))) ↔
      UlK S s (S.psi e (Om (s + 1))) γ ∧ γ < S.psi e (Om (s + 1 + 1)) :=
  ⟨fun h => ⟨ul_K_of_mem h, ul_lt_psiV h le_rfl (ul_psiW_le_psiV (s := s) e e) hγV⟩,
    fun h => uoDV hs e γ hown h.1 h.2⟩

/-- **The support of a level**: for `γ ∈ K^{(i)}_q`, `γ < V`, some own `e₀ ∈ K^{(i)}_q` has
`γ ∈ Cl(e, ψ e) ↔ e₀ ≤ e` for every own `e`. -/
theorem uz_supp (hs : s < ω) {i q γ : Ordinal.{0}} (his : i < s) (hq : SC q) (hqL : q ≤ Om (i + 1))
    (hγV : γ < Om (s + 1 + 1)) (hγK : UlK S i q γ) :
    ∃ e0, UlK S i q e0 ∧ e0 ∈ S.CSet e0 (S.psi e0 (Om (s + 1))) ∧
      ∀ e, e ∈ S.CSet e (S.psi e (Om (s + 1))) → (γ ∈ S.CSet e (S.psi e (Om (s + 1))) ↔ e0 ≤ e) := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  have hi : i < ω := his.trans hs
  have hqΛ : q ≤ S.Lam := us_qΛ hi hqL
  have hs1 : s + 1 < ω := Ui.ui_s1_lt_omega hs
  obtain ⟨z, hzK, hzW, hz⟩ := uz_dat hs his hqL hγK
  obtain ⟨ed, hedK, hedO, hed⟩ := uw_next hs his hq hqL z hzK hzW
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
  rw [uz_hull_iff hs hγV he, hz _ (Ui.ui_psi_SC e) (Ui.ui_L_lt_psi e) (Ui.ui_psi_lt e).le, hed e he,
    heV e hownV, max_le_iff]
  have hm : eV ≤ e ↔ m ≤ e :=
    ⟨fun h => uw_M_least hκ heVL he h, fun h => (M_spec (e := eV) (g := S.psi eV (Om (s + 1))) heVL).2.trans h⟩
  rw [hm]

/-- **(FV) The first value of a lifted level, one threshold down, for every visible level**: for `i < s`, `q` strongly
critical, `q ≤ Ω_{i+1}`, and a level `γ ∈ K^{(i)}_q`, `γ < V`: `Hˡ_γ(0) = ψ(x)` with `x` own, `x ∈ K^{(i)}_q`, and
`γ ∈ Cl(x, ψ x)` or `γ = ψ_V(x)`. -/
theorem uz_fv (hs : s < ω) {i q γ : Ordinal.{0}} (his : i < s) (hq : SC q) (hqL : q ≤ Om (i + 1))
    (hγV : γ < Om (s + 1 + 1)) (hγK : UlK S i q γ) :
    ∃ x, x ∈ S.CSet x (S.psi x (Om (s + 1))) ∧ UlK S i q x ∧ ulH S s γ 0 = S.psi x (Om (s + 1)) ∧
      (γ ∈ S.CSet x (S.psi x (Om (s + 1))) ∨ γ = S.psi x (Om (s + 1 + 1))) := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  have hκV : S.InR (Om (s + 1 + 1)) := InR_Om_succ (s + 1)
  have hi : i < ω := his.trans hs
  have hqΛ : q ≤ S.Lam := us_qΛ hi hqL
  rcases eq_or_ne γ 0 with rfl | hγ0
  · exact ⟨0, CSet.zero_mem _ _, UlK.zero, us_psi0 hs, Or.inl (CSet.zero_mem _ _)⟩
  obtain ⟨e0, he0K, he0O, he0⟩ := uz_supp hs his hq hqL hγV hγK
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

/-- **(FV)**: `γ ∈ K^{(i)}_q ⇒ Hˡ_γ(0) ∈ K^{(i)}_q` for every level `γ < V` (`i < s`, `q` strongly critical,
`q ≤ Ω_{i+1}`). -/
theorem uz_fv_K (hs : s < ω) {i q γ : Ordinal.{0}} (his : i < s) (hq : SC q) (hqL : q ≤ Om (i + 1))
    (hγV : γ < Om (s + 1 + 1)) (hγK : UlK S i q γ) : UlK S i q (ulH S s γ 0) := by
  obtain ⟨x, -, hxK, hx, -⟩ := uz_fv hs his hq hqL hγV hγK
  rw [hx]; exact UlK.coll (InR_Om_succ s) (us_W_ne_Om his.ne) (us_K_Om hs) hxK

end Googology.Trans.PoR.InaccPsi.R2.Uz
