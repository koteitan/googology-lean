import Googology.Trans.PoR.InaccPsi.R2.TiB

/-!
# The first value of `Φ_μ` above a point `m`, and its move under `B_n`, at every level `μ < B_Γ`

`ψ = S.psi`, `Φ_μ = Tf.tfP μ`, `u_μ = Ω₁^μ`, `B_n = Bc.bcB S n`, `c_n = L(n+1)`, `B_Γ = Tf.tfBG`.  The proofs of
`R2.TcLeast` (levels `< Γ'`) at the levels `< B_Γ`:

* `ti_least` (**for an own `K` with `ψ_{Ω₁}(K) ≤ m < ψ_{Ω₁}(K + 1)` and `tfDatL μ ≤ m`: `ψ_{Ω₁}(K + u_μ)` is the least
  value of `Φ_μ` above `m`**; `K + u_μ` is own), `ti_first` (its index), `ti_K_of` (such a `K` above a strongly
  critical `τ ≤ m < L(ω)`);
* `ti_B_least` (**`B_n` maps `ψ_{Ω₁}(K)`, `ψ_{Ω₁}(K + 1)`, `ψ_{Ω₁}(K + u_μ)` to `ψ_{Ω₁}(K')`, `ψ_{Ω₁}(K' + 1)`,
  `ψ_{Ω₁}(K' + u_{B_n μ})`**, `K'` own, for a code `μ` over `c_{n+1}`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ti

open Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Tc
  Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb
  Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Ri
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rk
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2.Bc

variable {S : InaccSeq.{0}}


/-- **The first value of `Φ_μ` above `m`**: for an own `K` with `ψ_{Ω₁}(K) ≤ m < ψ_{Ω₁}(K + 1)` and `tfDatL μ ≤ m`
(`μ < B_Γ`), `ψ_{Ω₁}(K + u_μ)` is a value of `Φ_μ` above `m`, below every value of `Φ_μ` above `m`; `K + u_μ` is
own. -/
theorem ti_least {μ K m : Ordinal.{0}} (hμG : μ < tfBG)
    (hown : K ∈ S.CSet K (S.psi K (Om 1)))
    (hcm : S.psi K (Om 1) ≤ m) (hm1 : m < S.psi (K + 1) (Om 1)) (hdm : tfDatL μ ≤ m) :
    S.psi (K + Le.leOe μ) (Om 1) ∈ range (tfP μ) ∧ m < S.psi (K + Le.leOe μ) (Om 1) ∧
      (∀ v ∈ range (tfP μ), m < v → S.psi (K + Le.leOe μ) (Om 1) ≤ v) ∧
      K + Le.leOe μ ∈ S.CSet (K + Le.leOe μ) (S.psi (K + Le.leOe μ) (Om 1)) := by
  set u := Le.leOe μ with hudef
  set E := K + u with hEdef
  have hu0 : u ≠ 0 := rhU_ne μ
  have h1u : (1 : Ordinal.{0}) ≤ u := one_le_iff_ne_zero.2 hu0
  have hmE : m < S.psi E (Om 1) :=
    hm1.trans_le (psi_mono (S := S) Low.InR_Om_one (add_le_add_right h1u K)).1
  have hμE : tfDatL μ < S.psi E (Om 1) := hdm.trans_lt hmE
  have hownE : E ∈ S.CSet E (S.psi E (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hown)
      (tf_U_mem (SC_psi Low.InR_Om_one _) (by rw [Rj.rj_Om1]; exact (psi_lt Low.InR_Om_one _).le) hμG hμE le_add_self)
  have hdvdE : u ∣ E := rh_dvd_add_self μ K
  have hE0 : E ≠ 0 := (lt_of_lt_of_le (rhU_pos μ) le_add_self).ne'
  have hfixE : ∀ j < μ, tfDatL j < S.psi E (Om 1) → tfP j (S.psi E (Om 1)) = S.psi E (Om 1) :=
    fun j hj hd => tfFwdAll j (hj.trans hμG) E hownE ((rhU_dvd_succ hj).trans hdvdE) hE0 hd
  have hval : S.psi E (Om 1) ∈ range (tfP μ) := by
    rw [tfP_range_eq]; exact ⟨SC_psi Low.InR_Om_one E, hμE, hfixE⟩
  have hnone : ∀ v, m < v → v < S.psi E (Om 1) → v ∈ range (tfP μ) → False := by
    intro v hmv hvE hvR
    have hvSC : SC v := by rw [tfP_range_eq] at hvR; exact hvR.1
    have hvF : ∀ j < μ, tfDatL j < v → tfP j v = v := fun j hj hd => tfP_fix_lower hj hvR hd
    obtain ⟨V, hownV, hV⟩ := rb_own_of_SC hvSC hvE
    have hdvdV : u ∣ V := ti_dvd_of_range hμG.le hownV (by rw [hV]; exact hvF)
    have hown1 : K + 1 ∈ S.CSet (K + 1) (S.psi (K + 1) (Om 1)) :=
      CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hown) (CSet.one_mem _ _)
    have hc1 : S.psi (K + 1) (Om 1) ≤ v := by
      refine not_lt.1 fun hlt => ?_
      have hcv : S.psi K (Om 1) < S.psi V (Om 1) := by rw [hV]; exact hcm.trans_lt hmv
      have h1 := compare_psi Low.InR_Om_one hown hownV
      rw [compare_lt_iff_lt.2 hcv] at h1
      have hBV : K < V := compare_lt_iff_lt.1 h1.symm
      have h2 := compare_psi Low.InR_Om_one hownV hown1
      rw [hV, compare_lt_iff_lt.2 hlt] at h2
      have hV1 : V < K + 1 := compare_lt_iff_lt.1 h2.symm
      exact absurd (Order.lt_add_one_iff.1 hV1) (not_le.2 hBV)
    have hBV : K < V := by
      have h1 := compare_psi Low.InR_Om_one hown1 hownV
      rcases hc1.lt_or_eq with hlt | heq
      · rw [hV, compare_lt_iff_lt.2 hlt] at h1
        exact (lt_add_one K).trans (compare_lt_iff_lt.1 h1.symm)
      · rw [← hV] at heq
        rw [← rh_own_inj hown1 hownV heq]; exact lt_add_one K
    have hVE : V < E := by
      have h1 := compare_psi Low.InR_Om_one hownV hownE
      rw [hV, compare_lt_iff_lt.2 hvE] at h1
      exact compare_lt_iff_lt.1 h1.symm
    set T := u * (K / u) with hTdef
    have hTB : T ≤ K := Ordinal.mul_div_le K u
    have hET : E = T + u := by
      rw [hEdef, hTdef]
      calc K + u = u * (K / u) + (K % u + u) := by rw [← add_assoc, Ordinal.div_add_mod]
        _ = u * (K / u) + u := by
            have := rdk_absorb (rhU_indec μ) (Ordinal.mod_lt K hu0) (le_refl (1 : Ordinal.{0}))
            rw [mul_one] at this; rw [this]
    have hTV : T ≤ V := hTB.trans hBV.le
    have hTd : u ∣ T := dvd_mul_right _ _
    have hVT : V = T + (V - T) := (Ordinal.add_sub_cancel_of_le hTV).symm
    have hdd : u ∣ V - T := by
      have := hdvdV
      rw [hVT] at this
      exact (Ordinal.dvd_add_iff hTd).1 this
    have hlt : V - T < u := by
      have := hVE
      rw [hET, hVT] at this
      exact (add_lt_add_iff_left T).1 this
    have h0 : V - T = 0 := by
      by_contra hne
      exact absurd (Ordinal.le_of_dvd hne hdd) (not_le.2 hlt)
    rw [h0, add_zero] at hVT
    exact absurd (hVT ▸ hTB) (not_le.2 hBV)
  exact ⟨hval, hmE, fun v hv hmv => not_lt.1 fun hlt => hnone v hmv hlt hv, hownE⟩

/-- **The index of the first value**: under the hypotheses of `ti_least`, `ψ_{Ω₁}(K + u_μ) = Φ_μ(c₀)` with
`Φ_μ(c) ≤ m` for every `c < c₀`. -/
theorem ti_first {μ K m : Ordinal.{0}} (hμG : μ < tfBG)
    (hown : K ∈ S.CSet K (S.psi K (Om 1)))
    (hcm : S.psi K (Om 1) ≤ m) (hm1 : m < S.psi (K + 1) (Om 1)) (hdm : tfDatL μ ≤ m) :
    ∃ c0, tfP μ c0 = S.psi (K + Le.leOe μ) (Om 1) ∧ ∀ c < c0, tfP μ c ≤ m := by
  obtain ⟨⟨c0, hc0⟩, -, hmin, -⟩ := ti_least (S := S) hμG hown hcm hm1 hdm
  refine ⟨c0, hc0, fun c hc => not_lt.1 fun hlt => ?_⟩
  have h1 := hmin _ ⟨c, rfl⟩ hlt
  rw [← hc0] at h1
  exact absurd ((tfP_le_iff μ).1 h1) (not_le.2 hc)

/-- **An own `K` with `τ ≤ ψ_{Ω₁}(K) ≤ m < ψ_{Ω₁}(K + 1)`** for a strongly critical `τ ≤ m < L(ω)`. -/
theorem ti_K_of {τ m : Ordinal.{0}} (hτ : SC τ) (hτm : τ ≤ m) (hmL : m < Nc.ncL S ω) :
    ∃ K, K ∈ S.CSet K (S.psi K (Om 1)) ∧ τ ≤ S.psi K (Om 1) ∧ S.psi K (Om 1) ≤ m ∧
      m < S.psi (K + 1) (Om 1) := by
  obtain ⟨eτ, heτ⟩ := lq_SC_gamma hτ
  have hg0 : gamma 0 ≤ m := ((gamma_le_gamma.2 zero_le).trans_eq heτ).trans hτm
  obtain ⟨e0, hce, hme⟩ := rh_gamma_below hg0
  have hτc : τ ≤ gamma e0 := by
    rw [← heτ]
    refine gamma_le_gamma.2 (Order.lt_add_one_iff.1 (gamma_lt_gamma.1 ?_))
    rw [heτ]; exact hτm.trans_lt hme
  have hcW : gamma e0 < S.psi (bcAlphaW S) (Om 1) := by
    rw [← Bc.ncL_omega_eq S]; exact hce.trans_lt hmL
  obtain ⟨K, hownc, hBc⟩ := rb_own_of_SC (lq_gamma_SC e0) hcW
  have hms : m < S.psi (K + 1) (Om 1) := by
    have hcs : gamma e0 < S.psi (K + 1) (Om 1) := by
      rw [← hBc]; exact rh_psi_lt_of_own hownc (lt_add_one K)
    obtain ⟨e, he⟩ := lq_SC_gamma (SC_psi Low.InR_Om_one (K + 1))
    rw [← he] at hcs ⊢
    have h1 : e0 < e := gamma_lt_gamma.1 hcs
    exact hme.trans_le (gamma_le_gamma.2 (Order.add_one_le_of_lt h1))
  exact ⟨K, hownc, by rw [hBc]; exact hτc, by rw [hBc]; exact hce, hms⟩

/-- **The move of the first value**: for a code `μ` over `c_{n+1}` and an own `K` with `c_n ≤ ψ_{Ω₁}(K)`,
`ψ_{Ω₁}(K + u_μ) < c_{n+1}`: `B_n` maps `ψ_{Ω₁}(K)`, `ψ_{Ω₁}(K + 1)`, `ψ_{Ω₁}(K + u_μ)` to `ψ_{Ω₁}(K')`,
`ψ_{Ω₁}(K' + 1)`, `ψ_{Ω₁}(K' + u_{B_n μ})` for an own `K'`. -/
theorem ti_B_least {n : ℕ} {μ K : Ordinal.{0}} (hμ : TfCl (Bc.bcC S (n + 1)) μ)
    (hown : K ∈ S.CSet K (S.psi K (Om 1))) (hlo : Bc.bcC S n ≤ S.psi K (Om 1))
    (hownE : K + Le.leOe μ ∈ S.CSet (K + Le.leOe μ) (S.psi (K + Le.leOe μ) (Om 1)))
    (hEX : S.psi (K + Le.leOe μ) (Om 1) < Bc.bcC S (n + 1)) :
    ∃ K', K' ∈ S.CSet K' (S.psi K' (Om 1)) ∧ Bc.bcB S n (S.psi K (Om 1)) = S.psi K' (Om 1) ∧
      Bc.bcB S n (S.psi (K + 1) (Om 1)) = S.psi (K' + 1) (Om 1) ∧
      Bc.bcB S n (S.psi (K + Le.leOe μ) (Om 1)) = S.psi (K' + Le.leOe (Bc.bcB S n μ)) (Om 1) := by
  have hcS : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  have h1Lw : (1 : Ordinal.{0}) < Nc.ncL S ω := Ri.ri_one_lt_L S
  have hown1 : K + 1 ∈ S.CSet (K + 1) (S.psi (K + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hown) (CSet.one_mem _ _)
  have h1X : S.psi (K + 1) (Om 1) < Bc.bcC S (n + 1) :=
    ((psi_mono (S := S) Low.InR_Om_one (add_le_add_right (one_le_iff_ne_zero.2 (rhU_ne μ)) K)).1).trans_lt hEX
  obtain ⟨hDu, hBu⟩ := tiB_Oe (S := S) (n := n) hcS (Bc.bcC_lt S (n + 1)) (Tc.tcB_c_le n) hμ
  obtain ⟨r, -, -, hownB', hBc', hBE⟩ := rdB_psi_baseD hown hlo hownE hEX hDu
  obtain ⟨r2, -, -, hownB2, hBc2, hB1⟩ := rdB_psi_baseD hown hlo hown1 h1X (mvD_of_lt h1Lw)
  set K' := bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) with hK'def
  set K2 := bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r2) with hK2def
  have hK2eq : K2 = K' := rh_own_inj hownB2 hownB' (hBc2.symm.trans hBc')
  rw [hK2eq, Mw.mwB_one] at hB1
  rw [hBu] at hBE
  exact ⟨K', hownB', hBc', hB1, hBE⟩

end Googology.Trans.PoR.InaccPsi.R2.Ti
