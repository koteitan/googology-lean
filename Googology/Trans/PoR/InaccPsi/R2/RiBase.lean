import Googology.Trans.PoR.InaccPsi.R2.RhBase
import Googology.Trans.PoR.InaccPsi.R2.RiB

/-!
# The base of a level `μ` with `riDat μ ≥ τ`: `b₀(μ) = ψ_{Ω₁}(K_c + u_μ)` and `B_n b₀(μ) = b₀(riLB n μ)`

`ψ = S.psi`, `Φ_μ = Ri.riP μ`, `u_μ = Ω₁^μ`, `riDat μ = max(μ/Ω₁, μ mod Ω₁)`, `B_n = Bc.bcB S n`,
`μ' = riLB S n μ`.

* `riC0 μ` (`0` if `riDat μ < Φ_μ(0)`, else `1`), `riC0_spec` (**`b₀(μ) = Φ_μ(c₀(μ))` is the least value of `Φ_μ`
  above `riDat μ`**);
* `ri_dvd_of_range` (**`u_μ ∣ B` for an own `B` whose collapse is a fixed point of every `Φ_j`, `j < μ`,
  `riDat j < ψ_{Ω₁}(B)`**: the digits of `B` below `μ` vanish, by `Ri.ri_conv` or by the levels of `Cl(B, ψ_{Ω₁}(B))`);
* `ri_least` (**`b₀(μ) = ψ_{Ω₁}(K_c + u_μ)`** for `μ < Ω₁·Ω₁`, `c = ψ_{Ω₁}(K_c) ≤ riDat μ < ψ_{Ω₁}(K_c + 1)`);
* `riBase` (**`B_n(b₀(μ)) = b₀(riLB n μ)`** at every level `μ < Ω₁·Ω₁` with `c_n ≤ Γ(0)`-point `≤ riDat μ` and
  `b₀(μ) < c_{n+1}`, unconditionally: as `Rh.rhBase`, with `Ri.riB_Oe` for `B_n(u_μ)`).

No new axiom.  New definition: `riC0`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ri

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb
  Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2.Bc
  Googology.Trans.PoR.InaccPsi.R2.Rh

variable {S : InaccSeq.{0}}

/-- `c₀(μ)`: `0` if `riDat μ < Φ_μ(0)`, else `1`. -/
noncomputable def riC0 (μ : Ordinal.{0}) : Ordinal.{0} := if riDat μ < riP μ 0 then 0 else 1

theorem riC0_spec (μ : Ordinal.{0}) :
    riDat μ < riP μ (riC0 μ) ∧ (∀ c < riC0 μ, riP μ c ≤ riDat μ) ∧ riC0 μ ≤ 1 := by
  unfold riC0
  by_cases h : riDat μ < riP μ 0
  · rw [if_pos h]
    exact ⟨h, fun c hc => absurd hc (not_lt.2 zero_le), zero_le⟩
  · rw [if_neg h]
    refine ⟨(riDat_le_riP μ 0).trans_lt ((riP_lt_iff μ).2 zero_lt_one), fun c hc => ?_, le_rfl⟩
    rw [Order.lt_one_iff] at hc
    rw [hc]; exact not_lt.1 h

/-- **`u_μ ∣ B`** for an own `B` whose collapse is a fixed point of every `Φ_j`, `j < μ`, `riDat j < ψ_{Ω₁}(B)`
(`μ ≤ Ω₁·Ω₁`). -/
theorem ri_dvd_of_range {μ B : Ordinal.{0}} (hμΩ : μ ≤ Om 1 * Om 1) (hown : B ∈ S.CSet B (S.psi B (Om 1)))
    (hfix : ∀ j < μ, riDat j < S.psi B (Om 1) → riP j (S.psi B (Om 1)) = S.psi B (Om 1)) :
    Le.leOe μ ∣ B := by
  set p := S.psi B (Om 1) with hpdef
  have hpSC : SC p := SC_psi Low.InR_Om_one B
  have hcoll : ∀ e, e < B → e ∈ S.CSet B p → RiDg p e → RiLev p e → S.psi e (Om 1) < p :=
    fun e he heC _ _ => lt_psi_of_mem Low.InR_Om_one
      (CSet.psi_mem he Low.InR_Om_one (mem_CSet_psi Low.InR_Om_one B) heC) (psi_lt Low.InR_Om_one _)
  have hdl := ri_diglev (S := S) hpSC hcoll B hown
  refine ri_dvd_of_dig μ fun j hj => ?_
  have hjΩ : j < Om 1 * Om 1 := hj.trans_le hμΩ
  by_cases hd : riDat j < p
  · exact ri_dig_zero_of_dvd (ri_conv hjΩ hown (hfix j hj hd))
  · by_contra hd0
    exact hd (hdl.2 j hjΩ hd0)

/-- `u_μ ∣ a + u_μ`. -/
theorem ri_dvd_add_self (μ a : Ordinal.{0}) : Le.leOe μ ∣ a + Le.leOe μ := rh_dvd_add_self μ a

/-- **`b₀(μ) = Φ_μ(c₀(μ)) = ψ_{Ω₁}(K_c + u_μ)`** (`μ < Ω₁·Ω₁`) for an own `K_c` with
`ψ_{Ω₁}(K_c) ≤ riDat μ < ψ_{Ω₁}(K_c + 1)`; `K_c + u_μ` is own. -/
theorem ri_least {μ Kc : Ordinal.{0}} (hμΩ : μ < Om 1 * Om 1)
    (hown : Kc ∈ S.CSet Kc (S.psi Kc (Om 1)))
    (hcμ : S.psi Kc (Om 1) ≤ riDat μ) (hμs : riDat μ < S.psi (Kc + 1) (Om 1)) :
    riP μ (riC0 μ) = S.psi (Kc + Le.leOe μ) (Om 1) ∧
      Kc + Le.leOe μ ∈ S.CSet (Kc + Le.leOe μ) (S.psi (Kc + Le.leOe μ) (Om 1)) := by
  set u := Le.leOe μ with hudef
  set E := Kc + u with hEdef
  have hu0 : u ≠ 0 := rhU_ne μ
  have h1u : (1 : Ordinal.{0}) ≤ u := one_le_iff_ne_zero.2 hu0
  have hμE : riDat μ < S.psi E (Om 1) :=
    hμs.trans_le (psi_mono (S := S) Low.InR_Om_one (add_le_add_right h1u Kc)).1
  have hownE : E ∈ S.CSet E (S.psi E (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hown) (riU_mem hμE)
  have hdvdE : u ∣ E := ri_dvd_add_self μ Kc
  have hE0 : E ≠ 0 := (lt_of_lt_of_le (rhU_pos μ) le_add_self).ne'
  -- `ψ_{Ω₁}(E)` is a value of `Φ_μ`
  have hfixE : ∀ j < μ, riDat j < S.psi E (Om 1) → riP j (S.psi E (Om 1)) = S.psi E (Om 1) :=
    fun j hj hd => ri_fwd j (hj.trans hμΩ) E hownE ((rhU_dvd_succ hj).trans hdvdE) hE0 hd
  obtain ⟨eE, heE⟩ := riP_range (SC_psi Low.InR_Om_one E) (psi_lt Low.InR_Om_one _) hμE hfixE
  -- no value of `Φ_μ` in `(riDat μ, ψ_{Ω₁}(E))`
  have hnone : ∀ v, riDat μ < v → v < S.psi E (Om 1) →
      (∀ j < μ, riDat j < v → riP j v = v) → SC v → False := by
    intro v hμv hvE hvF hvSC
    obtain ⟨V, hownV, hV⟩ := rb_own_of_SC hvSC hvE
    have hdvdV : u ∣ V := ri_dvd_of_range hμΩ.le hownV (by rw [hV]; exact hvF)
    have hown1 : Kc + 1 ∈ S.CSet (Kc + 1) (S.psi (Kc + 1) (Om 1)) :=
      CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hown) (CSet.one_mem _ _)
    have hc1 : S.psi (Kc + 1) (Om 1) ≤ v := by
      refine not_lt.1 fun hlt => ?_
      have hcv : S.psi Kc (Om 1) < S.psi V (Om 1) := by rw [hV]; exact hcμ.trans_lt hμv
      have h1 := compare_psi Low.InR_Om_one hown hownV
      rw [compare_lt_iff_lt.2 hcv] at h1
      have hBV : Kc < V := compare_lt_iff_lt.1 h1.symm
      have h2 := compare_psi Low.InR_Om_one hownV hown1
      rw [hV, compare_lt_iff_lt.2 hlt] at h2
      have hV1 : V < Kc + 1 := compare_lt_iff_lt.1 h2.symm
      exact absurd (Order.lt_add_one_iff.1 hV1) (not_le.2 hBV)
    have hBV : Kc < V := by
      have h1 := compare_psi Low.InR_Om_one hown1 hownV
      rcases hc1.lt_or_eq with hlt | heq
      · rw [hV, compare_lt_iff_lt.2 hlt] at h1
        exact (lt_add_one Kc).trans (compare_lt_iff_lt.1 h1.symm)
      · rw [← hV] at heq
        rw [← rh_own_inj hown1 hownV heq]; exact lt_add_one Kc
    have hVE : V < E := by
      have h1 := compare_psi Low.InR_Om_one hownV hownE
      rw [hV, compare_lt_iff_lt.2 hvE] at h1
      exact compare_lt_iff_lt.1 h1.symm
    set T := u * (Kc / u) with hTdef
    have hTB : T ≤ Kc := Ordinal.mul_div_le Kc u
    have hET : E = T + u := by
      rw [hEdef, hTdef]
      calc Kc + u = u * (Kc / u) + (Kc % u + u) := by rw [← add_assoc, Ordinal.div_add_mod]
        _ = u * (Kc / u) + u := by
            have := rdk_absorb (rhU_indec μ) (Ordinal.mod_lt Kc hu0) (le_refl (1 : Ordinal.{0}))
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
  obtain ⟨hc0, hmin0, -⟩ := riC0_spec μ
  refine ⟨le_antisymm ?_ ?_, hownE⟩
  · rw [← heE]
    refine (riP_le_iff μ).2 (not_lt.1 fun hlt => ?_)
    have := hmin0 eE hlt
    rw [heE] at this
    exact absurd hμE (not_lt.2 this)
  · refine not_lt.1 fun hlt => hnone _ hc0 hlt (fun j hj hd => riP_fix_lower hj ⟨_, rfl⟩ hd) (riP_SC μ _)

/-- **`B_n(b₀(μ)) = b₀(riLB n μ)`** at every level `μ < Ω₁·Ω₁` with a strongly critical `τ` such that
`c_n ≤ τ ≤ riDat μ`, and `b₀(μ) < c_{n+1}`. -/
theorem riBase {n : ℕ} {μ τ : Ordinal.{0}} (hμΩ : μ < Om 1 * Om 1) (hτSC : SC τ)
    (hc : Bc.bcC S n ≤ τ) (hτμ : τ ≤ riDat μ) (hb0 : riP μ (riC0 μ) < Bc.bcC S (n + 1)) :
    Bc.bcB S n (riP μ (riC0 μ)) = riP (riLB S n μ) (riC0 (riLB S n μ)) := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Qq.qqL_lt_omega S (n + 1 + 1)
  have hμb : riDat μ < riP μ (riC0 μ) := (riC0_spec μ).1
  have hdX : riDat μ < Bc.bcC S (n + 1) := hμb.trans hb0
  have hdL : riDat μ < Nc.ncL S ω := hdX.trans hLw
  -- `c = Γ(e₀)` the largest strongly critical point `≤ riDat μ`
  obtain ⟨eτ, heτ⟩ := lq_SC_gamma hτSC
  have hg0 : gamma 0 ≤ riDat μ := ((gamma_le_gamma.2 zero_le).trans_eq heτ).trans hτμ
  obtain ⟨e0, hce, hμe⟩ := rh_gamma_below hg0
  set c := gamma e0 with hcdef
  have hτc : τ ≤ c := by
    rw [← heτ]
    refine gamma_le_gamma.2 (Order.lt_add_one_iff.1 (gamma_lt_gamma.1 ?_))
    rw [heτ]; exact hτμ.trans_lt hμe
  have hcW : c < S.psi (bcAlphaW S) (Om 1) := by
    rw [← Bc.ncL_omega_eq S]; exact hce.trans_lt hdL
  obtain ⟨Kc, hownc, hBc⟩ := rb_own_of_SC (lq_gamma_SC e0) hcW
  have hown1 : Kc + 1 ∈ S.CSet (Kc + 1) (S.psi (Kc + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hownc) (CSet.one_mem _ _)
  have hμs : riDat μ < S.psi (Kc + 1) (Om 1) := by
    have hcs : c < S.psi (Kc + 1) (Om 1) := by
      rw [hcdef, ← hBc]; exact rh_psi_lt_of_own hownc (lt_add_one Kc)
    obtain ⟨e, he⟩ := lq_SC_gamma (SC_psi Low.InR_Om_one (Kc + 1))
    rw [← he] at hcs ⊢
    have h1 : e0 < e := gamma_lt_gamma.1 hcs
    exact hμe.trans_le (gamma_le_gamma.2 (Order.add_one_le_of_lt h1))
  obtain ⟨hleast, hownE⟩ := ri_least hμΩ hownc (by rw [hBc]; exact hce) hμs
  rw [hleast] at hb0 ⊢
  have hlo : Bc.bcC S n ≤ S.psi Kc (Om 1) := by rw [hBc]; exact hc.trans hτc
  have hEX : S.psi (Kc + Le.leOe μ) (Om 1) < Bc.bcC S (n + 1) := hb0
  have h1X : S.psi (Kc + 1) (Om 1) < Bc.bcC S (n + 1) :=
    ((psi_mono (S := S) Low.InR_Om_one (add_le_add_right (one_le_iff_ne_zero.2 (rhU_ne μ)) Kc)).1).trans_lt
      hEX
  have h1Lw : (1 : Ordinal.{0}) < Nc.ncL S ω := ri_one_lt_L S
  obtain ⟨hDu, hBu⟩ := riB_Oe (S := S) (n := n) hdX
  obtain ⟨r, -, -, hownB', hBc', hBE⟩ := rdB_psi_baseD hownc hlo hownE hEX hDu
  obtain ⟨r2, -, -, hownB2, hBc2, hB1⟩ := rdB_psi_baseD hownc hlo hown1 h1X (mvD_of_lt h1Lw)
  set B' := bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) with hB'def
  set B2 := bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r2) with hB2def
  have hB2eq : B2 = B' := rh_own_inj hownB2 hownB' (hBc2.symm.trans hBc')
  rw [hB2eq, mwB_one] at hB1
  rw [hBu] at hBE
  rw [hBE]
  -- `B_n c ≤ riDat μ' < ψ_{Ω₁}(B' + 1)`
  have hcL : c < Nc.ncL S ω := hce.trans_lt hdL
  have h1L : S.psi (Kc + 1) (Om 1) < Nc.ncL S ω := h1X.trans hLw
  have hc' : S.psi B' (Om 1) ≤ riDat (riLB S n μ) := by
    rw [riLB_dat hdX, ← hBc', hBc]
    exact riB_mono hdL hce
  have hμ' : riDat (riLB S n μ) < S.psi (B' + 1) (Om 1) := by
    rw [riLB_dat hdX, ← hB1]; exact (Bc.bcB_lt_iff hdL h1L).2 hμs
  exact (ri_least (riLB_lt hdX) hownB' hc' hμ').1.symm

end Googology.Trans.PoR.InaccPsi.R2.Ri
