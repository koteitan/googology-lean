import Googology.Trans.PoR.InaccPsi.R2.RkB
import Googology.Trans.PoR.InaccPsi.R2.RiBase

/-!
# The data of the image level, and the base `b₀(μ) = Φ_μ(0)` of a level with `rkDat μ ≥ τ`

`ψ = S.psi`, `Φ_μ = Rk.rkP μ`, `u_μ = Ω₁^μ`, `rkDat μ = rjDat (Ω₁ + μ)`, `B_n = Bc.bcB S n`, `c = c_{n+1}`.

* `rkB_rjDat` (**`rjDat (B_n z) = B_n (rjDat z)`** for a code `z < ε_{Ω₁+1}` over `c_{n+1}`: `B_n` keeps the hereditary
  normal form and moves the leaves), `rkB_dat` (**`rkDat (B_n μ) = B_n (rkDat μ)`**);
* `rk_dvd_of_range` (**`u_μ ∣ B`** for an own `B` whose collapse is a fixed point of every `Φ_j`, `j < μ`,
  `rkDat j < ψ_{Ω₁}(B)`), `rk_least` (**`Φ_μ(0) = ψ_{Ω₁}(K_c + u_μ)`** for `ψ_{Ω₁}(K_c) ≤ rkDat μ < ψ_{Ω₁}(K_c + 1)`;
  the values of `Φ_μ` all lie above `rkDat μ`, so the base index is `0`);
* `rkBase` (**`B_n(Φ_μ(0)) = Φ_{B_n μ}(0)`** at every level `μ < ε_{Ω₁+1}` with a strongly critical `τ`, `c_n ≤ τ ≤
  rkDat μ`, and `Φ_μ(0) < c_{n+1}`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb
  Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2.Bc
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj

variable {S : InaccSeq.{0}}

/-- `B_n(ω^g·k) = ω^{B_n g}·k` in the domain. -/
theorem rkB_opow_nat {n : ℕ} {g : Ordinal.{0}} (hg : MvD S g) :
    ∀ k : ℕ, MvD S (ω ^ g * k) ∧ Bc.bcB S n (ω ^ g * k) = ω ^ Bc.bcB S n g * k
  | 0 => by rw [Nat.cast_zero, mul_zero, mul_zero, Bc.bcB_zero]
            exact ⟨mvD_of_lt (Lw.lw_L_SC S ω).1, rfl⟩
  | k + 1 => by
    obtain ⟨hD, hB⟩ := rkB_opow_nat (n := n) hg k
    obtain ⟨hDw, hBw⟩ := Ld.ldB_opow (n := n) hg
    obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hD hDw
    rw [Nat.cast_succ, mul_add_one, mul_add_one]
    exact ⟨hDs, by rw [hBs, hB, hBw]⟩

/-- **`rjDat (B_n z) = B_n (rjDat z)`** for a code `z < ε_{Ω₁+1}` over `c_{n+1}`. -/
theorem rkB_rjDat {n : ℕ} :
    ∀ z, GgCl (Bc.bcC S (n + 1)) z → z < ggE → rjDat (Bc.bcB S n z) = Bc.bcB S n (rjDat z) := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hc : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hz hzE
  have hDz := (rkB_cl (n := n) hLw z hz).1
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  rcases lt_trichotomy z Om1 with h | rfl | h
  · have hzc : z < Bc.bcC S (n + 1) := hz.lt_of_lt_Om1 hc (by rw [← rj_Om1]; exact h)
    rw [rjDat_small h, rjDat_small (by rw [rj_Om1]; exact rhB_lt_Om1 hzc)]
  · rw [rj_Om1, hBO, ← rj_Om1, rjDat_Om1, Bc.bcB_zero]
  · have hz0 : z ≠ 0 := (rj_Om1_pos.trans h).ne'
    obtain ⟨hsub, hlog⟩ := ggDec hc z hz
    set g := log ω z with hg
    have hgz : g < z := rj_log_lt h hzE
    obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt z one_lt_omega0)
    have hk0 : k ≠ 0 := by
      intro e
      have h1 := Ordinal.div_opow_log_pos ω hz0
      rw [hk, e, Nat.cast_zero] at h1
      exact lt_irrefl _ h1
    have hdec : ω ^ g * k + z % ω ^ g = z := by
      have := Ordinal.div_add_mod z (ω ^ g); rwa [hk] at this
    have hrg : z % ω ^ g < ω ^ g := Ordinal.mod_lt z (opow_pos _ omega0_pos).ne'
    have hwk : GgCl (Bc.bcC S (n + 1)) (ω ^ g * k) := GgCl.mul_nat hc.1 (GgCl.opow hc.1 hlog) k
    have hle : ω ^ g * k ≤ z := by
      conv_rhs => rw [← hdec]
      exact le_self_add
    have hr : GgCl (Bc.bcC S (n + 1)) (z % ω ^ g) := by
      have e : z - ω ^ g * k = z % ω ^ g := by
        nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
      rw [← e]; exact hsub _ hwk hle
    have hrz : z % ω ^ g < z := rj_mod_lt hz0
    have hDg := (rkB_cl (n := n) hLw g hlog).1
    have hDr := (rkB_cl (n := n) hLw _ hr).1
    obtain ⟨hDw, hBw⟩ := rkB_opow_nat (n := n) hDg k
    obtain ⟨-, hBz⟩ := mvB_add (k := n) hDw hDr
    rw [hdec] at hBz
    obtain ⟨hDog, hBog⟩ := Ld.ldB_opow (n := n) hDg
    have hBr : Bc.bcB S n (z % ω ^ g) < ω ^ Bc.bcB S n g := by
      rw [← hBog]; exact (mvB_lt_iff hDr hDog).2 hrg
    have hBzE : Bc.bcB S n z < ggE := rkB_lt_E hLw hz hzE
    have hOz : Om1 < Bc.bcB S n z := by
      have := (mvB_lt_iff (k := n) hDO hDz).2 (by rw [← rj_Om1]; exact h)
      rwa [hBO, ← rj_Om1] at this
    have hlogB : log ω (Bc.bcB S n z) = Bc.bcB S n g := by
      rw [hBz, hBw, log_opow_mul_add one_lt_omega0 (by exact_mod_cast hk0) hBr,
        Ordinal.log_eq_zero (natCast_lt_omega0 k), add_zero]
    have hmodB : Bc.bcB S n z % ω ^ log ω (Bc.bcB S n z) = Bc.bcB S n (z % ω ^ g) := by
      rw [hlogB, hBz, hBw, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hBr]
    have hdg : rjDat g < Bc.bcC S (n + 1) := rk_cl_dat hc g hlog
    have hdr : rjDat (z % ω ^ g) < Bc.bcC S (n + 1) := rk_cl_dat hc _ hr
    rw [rjDat_eq hOz hBzE, hmodB, hlogB, IH g hgz hlog (hgz.trans hzE), IH _ hrz hr (hrz.trans hzE),
      rjDat_eq h hzE]
    rcases le_total (rjDat g) (rjDat (z % ω ^ g)) with hle' | hle'
    · rw [max_eq_right hle', max_eq_right (Ri.riB_mono (hdr.trans hLw) hle')]
    · rw [max_eq_left hle', max_eq_left (Ri.riB_mono (hdg.trans hLw) hle')]

/-- **`rkDat (B_n μ) = B_n (rkDat μ)`** for a code `μ < ε_{Ω₁+1}` over `c_{n+1}`. -/
theorem rkB_dat {n : ℕ} {μ : Ordinal.{0}} (hμ : GgCl (Bc.bcC S (n + 1)) μ) (hμE : μ < ggE) :
    rkDat (Bc.bcB S n μ) = Bc.bcB S n (rkDat μ) := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hD := (rkB_cl (n := n) hLw μ hμ).1
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  have e : Bc.bcB S n (Om1 + μ) = Om1 + Bc.bcB S n μ := by
    rw [rj_Om1, (mvB_add (k := n) hDO hD).2, hBO]
  unfold rkDat
  rw [← e]
  exact rkB_rjDat _ (by rw [rj_Om1]; exact GgCl.add GgCl.om hμ) (rk_Om1_add_lt hμE)

/-- **`u_μ ∣ B`** for an own `B` whose collapse is a fixed point of every `Φ_j`, `j < μ`, `rkDat j < ψ_{Ω₁}(B)`
(`μ ≤ ε_{Ω₁+1}`). -/
theorem rk_dvd_of_range {μ B : Ordinal.{0}} (hμΩ : μ ≤ ggE) (hown : B ∈ S.CSet B (S.psi B (Om 1)))
    (hfix : ∀ j < μ, rkDat j < S.psi B (Om 1) → rkP j (S.psi B (Om 1)) = S.psi B (Om 1)) :
    Le.leOe μ ∣ B := by
  set p := S.psi B (Om 1) with hpdef
  have hpSC : SC p := SC_psi Low.InR_Om_one B
  have hcoll : ∀ e, e < B → e ∈ S.CSet B p → Ri.RiDg p e → RkLev p e → S.psi e (Om 1) < p :=
    fun e he heC _ _ => lt_psi_of_mem Low.InR_Om_one
      (CSet.psi_mem he Low.InR_Om_one (mem_CSet_psi Low.InR_Om_one B) heC) (psi_lt Low.InR_Om_one _)
  have hdl := rk_diglev (S := S) hpSC hcoll B hown
  refine Ri.ri_dvd_of_dig μ fun j hj => ?_
  have hjΩ : j < ggE := hj.trans_le hμΩ
  by_cases hd : rkDat j < p
  · exact Ri.ri_dig_zero_of_dvd (rk_conv hjΩ hown (hfix j hj hd))
  · by_contra hd0
    exact hd (hdl.2.1 j hjΩ hd0)

/-- **`Φ_μ(0) = ψ_{Ω₁}(K_c + u_μ)`** (`μ < ε_{Ω₁+1}`) for an own `K_c` with `ψ_{Ω₁}(K_c) ≤ rkDat μ < ψ_{Ω₁}(K_c + 1)`;
`K_c + u_μ` is own. -/
theorem rk_least {μ Kc : Ordinal.{0}} (hμΩ : μ < ggE)
    (hown : Kc ∈ S.CSet Kc (S.psi Kc (Om 1)))
    (hcμ : S.psi Kc (Om 1) ≤ rkDat μ) (hμs : rkDat μ < S.psi (Kc + 1) (Om 1)) :
    rkP μ 0 = S.psi (Kc + Le.leOe μ) (Om 1) ∧
      Kc + Le.leOe μ ∈ S.CSet (Kc + Le.leOe μ) (S.psi (Kc + Le.leOe μ) (Om 1)) := by
  set u := Le.leOe μ with hudef
  set E := Kc + u with hEdef
  have hu0 : u ≠ 0 := rhU_ne μ
  have h1u : (1 : Ordinal.{0}) ≤ u := one_le_iff_ne_zero.2 hu0
  have hμE : rkDat μ < S.psi E (Om 1) :=
    hμs.trans_le (psi_mono (S := S) Low.InR_Om_one (add_le_add_right h1u Kc)).1
  have hownE : E ∈ S.CSet E (S.psi E (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hown)
      (rkU_mem' (SC_psi Low.InR_Om_one _) hμΩ hμE)
  have hdvdE : u ∣ E := rh_dvd_add_self μ Kc
  have hE0 : E ≠ 0 := (lt_of_lt_of_le (rhU_pos μ) le_add_self).ne'
  have hfixE : ∀ j < μ, rkDat j < S.psi E (Om 1) → rkP j (S.psi E (Om 1)) = S.psi E (Om 1) :=
    fun j hj hd => rk_fwd j (hj.trans hμΩ) E hownE ((rhU_dvd_succ hj).trans hdvdE) hE0 hd
  obtain ⟨eE, heE⟩ := rkP_range (SC_psi Low.InR_Om_one E) hμE hfixE
  have hnone : ∀ v, rkDat μ < v → v < S.psi E (Om 1) →
      (∀ j < μ, rkDat j < v → rkP j v = v) → SC v → False := by
    intro v hμv hvE hvF hvSC
    obtain ⟨V, hownV, hV⟩ := rb_own_of_SC hvSC hvE
    have hdvdV : u ∣ V := rk_dvd_of_range hμΩ.le hownV (by rw [hV]; exact hvF)
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
  refine ⟨le_antisymm ?_ ?_, hownE⟩
  · rw [← heE]; exact (rkP_le_iff μ).2 zero_le
  · refine not_lt.1 fun hlt => hnone _ (rkDat_lt_rkP μ 0) hlt
      (fun j hj hd => rkP_fix_lower hj ⟨_, rfl⟩ hd) (rkP_SC μ _)

/-- **`B_n(Φ_μ(0)) = Φ_{B_n μ}(0)`** at every level `μ < ε_{Ω₁+1}` with a strongly critical `τ` such that
`c_n ≤ τ ≤ rkDat μ`, and `Φ_μ(0) < c_{n+1}`. -/
theorem rkBase {n : ℕ} {μ τ : Ordinal.{0}} (hμΩ : μ < ggE) (hτSC : SC τ)
    (hc : Bc.bcC S n ≤ τ) (hτμ : τ ≤ rkDat μ) (hb0 : rkP μ 0 < Bc.bcC S (n + 1)) :
    Bc.bcB S n (rkP μ 0) = rkP (Bc.bcB S n μ) 0 := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Qq.qqL_lt_omega S (n + 1 + 1)
  have hμb : rkDat μ < rkP μ 0 := rkDat_lt_rkP μ 0
  have hdX : rkDat μ < Bc.bcC S (n + 1) := hμb.trans hb0
  have hdL : rkDat μ < Nc.ncL S ω := hdX.trans hLw
  have hcS : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  have hμC : GgCl (Bc.bcC S (n + 1)) μ := (rkDat_lt_iff hcS hμΩ).1 hdX
  obtain ⟨eτ, heτ⟩ := lq_SC_gamma hτSC
  have hg0 : gamma 0 ≤ rkDat μ := ((gamma_le_gamma.2 zero_le).trans_eq heτ).trans hτμ
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
  have hμs : rkDat μ < S.psi (Kc + 1) (Om 1) := by
    have hcs : c < S.psi (Kc + 1) (Om 1) := by
      rw [hcdef, ← hBc]; exact rh_psi_lt_of_own hownc (lt_add_one Kc)
    obtain ⟨e, he⟩ := lq_SC_gamma (SC_psi Low.InR_Om_one (Kc + 1))
    rw [← he] at hcs ⊢
    have h1 : e0 < e := gamma_lt_gamma.1 hcs
    exact hμe.trans_le (gamma_le_gamma.2 (Order.add_one_le_of_lt h1))
  obtain ⟨hleast, hownE⟩ := rk_least hμΩ hownc (by rw [hBc]; exact hce) hμs
  rw [hleast] at hb0 ⊢
  have hlo : Bc.bcC S n ≤ S.psi Kc (Om 1) := by rw [hBc]; exact hc.trans hτc
  have hEX : S.psi (Kc + Le.leOe μ) (Om 1) < Bc.bcC S (n + 1) := hb0
  have h1X : S.psi (Kc + 1) (Om 1) < Bc.bcC S (n + 1) :=
    ((psi_mono (S := S) Low.InR_Om_one (add_le_add_right (one_le_iff_ne_zero.2 (rhU_ne μ)) Kc)).1).trans_lt
      hEX
  have h1Lw : (1 : Ordinal.{0}) < Nc.ncL S ω := Ri.ri_one_lt_L S
  obtain ⟨hDu, hBu⟩ := rkB_Oe (S := S) (n := n) hcS (Bc.bcC_lt S (n + 1)) hμC
  obtain ⟨r, -, -, hownB', hBc', hBE⟩ := rdB_psi_baseD hownc hlo hownE hEX hDu
  obtain ⟨r2, -, -, hownB2, hBc2, hB1⟩ := rdB_psi_baseD hownc hlo hown1 h1X (mvD_of_lt h1Lw)
  set B' := bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) with hB'def
  set B2 := bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r2) with hB2def
  have hB2eq : B2 = B' := rh_own_inj hownB2 hownB' (hBc2.symm.trans hBc')
  rw [hB2eq, mwB_one] at hB1
  rw [hBu] at hBE
  rw [hBE]
  have h1L : S.psi (Kc + 1) (Om 1) < Nc.ncL S ω := h1X.trans hLw
  have hc' : S.psi B' (Om 1) ≤ rkDat (Bc.bcB S n μ) := by
    rw [rkB_dat hμC hμΩ, ← hBc', hBc]
    exact Ri.riB_mono hdL hce
  have hμ' : rkDat (Bc.bcB S n μ) < S.psi (B' + 1) (Om 1) := by
    rw [rkB_dat hμC hμΩ, ← hB1]; exact (Bc.bcB_lt_iff hdL h1L).2 hμs
  exact (rk_least (rkB_lt_E (Bc.bcC_lt S (n + 1)) hμC hμΩ) hownB' hc' hμ').1.symm

end Googology.Trans.PoR.InaccPsi.R2.Rk
