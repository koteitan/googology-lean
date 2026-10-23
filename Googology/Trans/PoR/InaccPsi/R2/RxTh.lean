import Googology.Trans.PoR.InaccPsi.R2.RxMono

/-!
# The block step at every offset below `θ`: `RuBlkHi`, `RpReadAll`, `RgCoverAt`

`θ = ψ_{Ω₂}(Ω_ω)`, `θ₂ = ψ_{Ω₃}(Ω_ω)`, `G(z) = ψ_{Ω₂}(Ω_ω + θ₂·z)` (`Lc.lcG`), `G' = Ls.lsG S (k+1)`, `A = A_{η_μ}`,
`Â = A + θ·x`, `β = Ω_ω + θ₂·x`, `ρ_μ = υ_μ`, `Θ = gxTh ρ_μ (ldAtR μ)` (`= Θ_μ` below `Ω₂`), `RxE` the domain of
the level shift, `κ = rxL S ρ_μ (ldAtR μ) W` (`Ω_k ↦ Ω_{k+1}`, `ψ_{Ω_{k+1}}(d) ↦ ψ_{Ω_{k+2}}(κ d)` at every finite
level `k ≥ 1`, `Θ⁻¹` below `Ω₁`), `W = min(Θ(Ω₂), Ω₁)`.

* `rxL_lt_OmW` (`κ x < Ω_ω`), `rxL_memH` (**`κ x ∈ Cl(a, b)`** for a member `x` over `T ≤ W`, `Ω_ω ≤ a`, when
  every `Θ⁻¹(g)`, `g < T`, is in `Cl(a, b)`), `rxL_lt_th2` (**`κ x < θ₂` for `x < θ`**);
* `rxCofTh` (**the members over `2` are cofinal in `θ`**), `rxDvdTh` (`θ ∣ A_η + θ·x`);
* `rxBlkTh` (**THE BLOCK STEP BELOW `θ`**: at a Range restart `μ` with code `G' + 1`, for `x + 1 < ρ_μ`, the
  reading of the base `υ_{μ+x} ≤ Θ_μ(G(x))` gives, for every `ζ < θ`, an atom `t < G(x+1)` of `μ` with
  `ψ_{Ω₁}(A + θ·x + ζ) ≤ Θ_μ(t)`; the atoms are `ψ_{Ω₂}(β + κ w)` for the members `w ≥ ζ` over `2`, the tails of
  the hulls are members (`Rx.rxN_of_HCl`), and `κ` is strictly increasing and keeps the hulls (`Rx.rxMT`));
* `rxBlkHi` (**`Ru.RuBlkHi` is a theorem**), `rxBlkAt` (`Rp.RpBlkAt` from the base reading), `rxReadAll`
  (**`Rp.RpReadAll S k` for every `k`, unconditionally**), `rxCover` (**`Rg.RgCoverAt` at `m* = L(0)` and at every
  `L(n+1)`**), `rxSupAt` (`Ra.RaSupAt` there), `rxRoadT` (**the road `Ru.ruRoad` without its `RuBlkHi`
  hypothesis**), `rxOut_iff_T`, `rxNu_iff_T` (**`L(ω+1) ≤ ν_C ⇔ L(ω) ≤₁ L(ω+1)`** under UPPER, LOWER, CapV and
  the gap at `L(ω)`), `rxRoad_nu` (`Ru.ruRoad_nu` without `RuBlkHi`), `rxRoadRa` (`Ra.raRoad_T` without its
  `RaSupAt` hypotheses).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

theorem RxE.mono {T T' x : Ordinal.{0}} (h : T ≤ T') (hx : RxE S T x) : RxE S T' x := ⟨hx.1.mono h, hx.2⟩

theorem rxFix_not_ltW {x : Ordinal.{0}} (hS : SC x) (hfix : Om x = x) : ¬ x < Om ω := fun h => by
  rw [← hfix] at h
  exact absurd ((Lw.lw_omega_lt_SC hS).trans (Om_lt_Om.1 h)) (lt_irrefl _)

section K

variable {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1) (hAt : GxAt At)
include hZ hZ1 hAt

/-- **`κ x < Ω_ω`.** -/
theorem rxL_lt_OmW {x : Ordinal.{0}} (hx : RxE S (rxW Z At) x) : rxL S Z At (rxW Z At) x < Om ω := by
  obtain ⟨n, hn⟩ := rxOmW_nat hx.2.2
  have h1 : x < Om ((n : Ordinal.{0}) + 1) := hn.trans (Om_lt_Om.2 (lt_add_one _))
  refine (rxL_lt_lev hZ hZ1 hAt x hx n h1).trans (Om_lt_Om.2 ?_)
  exact_mod_cast (show ((n + 1 + 1 : ℕ) : Ordinal.{0}) < ω from natCast_lt_omega0 _)

/-- **`κ x ∈ Cl(a, b)`** for a member `x` over `T ≤ W`, `Ω_ω ≤ a`, when every `ruInv g`, `g < T`, is in it. -/
theorem rxL_memH {T a b : Ordinal.{0}} (hT : SC T) (hTW : T ≤ rxW Z At) (ha : Om ω ≤ a)
    (hinv : ∀ g, g < T → ruInv Z At g ∈ S.CSet a b) :
    ∀ x, RxE S T x → rxL S Z At (rxW Z At) x ∈ S.CSet a b := by
  have hW1 := rxW_le_Om1 (Z := Z) (At := At)
  have hT1 : T ≤ Om 1 := hTW.trans hW1
  refine rxMs_ind (S := S) (T := rxW Z At) fun x IH hx => ?_
  have hxW : RxE S (rxW Z At) x := hx.mono hTW
  rcases lt_or_ge x (Om 1) with h1 | h1
  · rw [(rxL_small hZ hZ1 hAt hxW h1).1]; exact hinv x (rxE_lt_T hT hx h1)
  by_cases hΩ : ∃ j : ℕ, x = Om (j : Ordinal.{0})
  · obtain ⟨j, rfl⟩ := hΩ
    have hj : 1 ≤ j := by
      by_contra h0
      have : j = 0 := by omega
      subst this
      rw [Nat.cast_zero, Om_zero] at h1; exact absurd h1 (not_le.2 (Om_pos one_ne_zero))
    rw [rxL_Om hj]; exact rxC_Om_succ _ _ j
  have h1' : Om 1 < x := lt_of_le_of_ne h1 fun e => hΩ ⟨1, by rw [Nat.cast_one]; exact e.symm⟩
  by_cases hS : SC x
  · obtain ⟨j, hj, d, hdE, hdn, rfl, -⟩ := rxE_atom hT1 hx hS h1' hΩ
    obtain ⟨hK, hdh⟩ := rxL_psiE hj (hdE.mono hTW) hdn
    rw [hK]
    exact CSet.psi_mem ((rxL_lt_OmW hZ hZ1 hAt (hdE.mono hTW)).trans_le ha) (InR_Om_succ _)
      (rxC_Om_succ2 _ _ j) (IH d (rxMs_lt_stage (rxE_lt_Lam hdE) hdh) hdE)
  by_cases hε : ω ^ x = x
  · obtain ⟨hv, -, ha', hb⟩ := rxVeb h1' hε hS
    obtain ⟨haE, hbE, -, -⟩ := rxE_veb hx hv hb
    obtain ⟨-, -, hha, hhb⟩ := rxE_veb hxW hv hb
    rw [rxL_veb hxW h1' hε hS]
    exact CSet.phi_mem (IH _ (rxMs_lt_val hha ha') haE) (IH _ (rxMs_lt_val hhb hb) hbE)
  · have hlt := ruLog_lt h1' hε
    have hrlt : x % ω ^ log ω x < x := mod_opow_log_lt_self ω ((Om_pos one_ne_zero).trans h1').ne'
    obtain ⟨hlE, -⟩ := rxE_log hx
    obtain ⟨hrE, -⟩ := rxE_rem hx
    obtain ⟨-, hlh⟩ := rxE_log hxW
    obtain ⟨-, hrh⟩ := rxE_rem hxW
    obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
    rw [rxL_gt hxW h1' hlt, hn]
    have h1m := IH _ (rxMs_lt_val hlh hlt) hlE
    have h2m := IH _ (rxMs_lt_val hrh hrlt) hrE
    have hop : ω ^ rxL S Z At (rxW Z At) (log ω x) ∈ S.CSet a b := by
      have := CSet.phi_mem (S := S) (CSet.zero_mem a b) h1m; rwa [veblen_zero_apply] at this
    exact CSet.add_mem (ConjT.mul_nat_mem S hop n) h2m

/-- **`κ x < θ₂` for `x < θ`.** -/
theorem rxL_lt_th2 : ∀ x, RxE S (rxW Z At) x → x < ConjT.th S →
    rxL S Z At (rxW Z At) x < S.psi (Om ω) (Om (1 + 1 + 1)) := by
  have hW := rxW_SC hZ hZ1 hAt
  have hW1 := rxW_le_Om1 (Z := Z) (At := At)
  have hX : SC (S.psi (Om ω) (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) _
  have h2X : Om (1 + 1 : Ordinal.{0}) < S.psi (Om ω) (Om (1 + 1 + 1)) :=
    (psiS_bounds (S := S) (Om ω) (1 + 1)).1
  have hθ2 : ConjT.th S < Om (1 + 1) := psi_lt (InR_Om_succ 1) _
  refine rxMs_ind (S := S) (T := rxW Z At) fun x IH hx hxθ => ?_
  rcases lt_or_ge x (Om 1) with h1 | h1
  · obtain ⟨e, h2, -⟩ := rxL_small hZ hZ1 hAt hx h1
    rw [e]; exact h2.trans h2X
  by_cases hΩ : ∃ j : ℕ, x = Om (j : Ordinal.{0})
  · obtain ⟨j, rfl⟩ := hΩ
    have hj1 : (j : Ordinal.{0}) < 1 + 1 := Om_lt_Om.1 (hxθ.trans hθ2)
    have hj : 1 ≤ j := by
      by_contra h0
      have : j = 0 := by omega
      subst this
      rw [Nat.cast_zero, Om_zero] at h1; exact absurd h1 (not_le.2 (Om_pos one_ne_zero))
    have hj' : j = 1 := by
      have : j < 2 := by
        have h3 : (j : Ordinal.{0}) < 2 := by rwa [one_add_one_eq_two] at hj1
        exact_mod_cast h3
      omega
    subst hj'
    rw [rxL_Om le_rfl, Nat.cast_one]; exact h2X
  have h1' : Om 1 < x := lt_of_le_of_ne h1 fun e => hΩ ⟨1, by rw [Nat.cast_one]; exact e.symm⟩
  by_cases hS : SC x
  · obtain ⟨j, hj, d, hdE, hdn, rfl, -⟩ := rxE_atom hW1 hx hS h1' hΩ
    have hb := psiS_bounds (S := S) d (j : Ordinal.{0})
    have hj' : j = 1 := by
      have h3 : (j : Ordinal.{0}) < 1 + 1 := Om_lt_Om.1 (hb.1.trans (hxθ.trans hθ2))
      have : j < 2 := by
        have h4 : (j : Ordinal.{0}) < 2 := by rwa [one_add_one_eq_two] at h3
        exact_mod_cast h4
      omega
    subst hj'
    obtain ⟨hK, -⟩ := rxL_psiE le_rfl hdE hdn
    rw [hK]
    simp only [Nat.cast_one]
    have hdW := rxL_lt_OmW hZ hZ1 hAt hdE
    refine psi_lt_psi_of_mem (InR_Om_succ (1 + 1)) hdW ?_
    refine rxL_memH hZ hZ1 hAt hW le_rfl le_rfl (fun g hg => CSet.of_lt ?_) d hdE
    exact (ruInv_spec (hg.trans_le (min_le_left _ _))).2.1.trans h2X
  · exact rxL_step_lt hX hx h1' hS fun y hyE hym hyx => IH y hym hyE (hyx.trans hxθ)

end K

/-- **The members over `2` are cofinal in `θ`.** -/
theorem rxCofTh {ζ : Ordinal.{0}} (h : ζ < ConjT.th S) : ∃ w, RxN S 2 w ∧ ζ ≤ w ∧ w < ConjT.th S := by
  have h2 : (2 : Ordinal.{0}) ≤ Om 1 := ruTwo_le Ph.ph_SC_Om1
  have hθSC := ConjT.SC_th S
  by_contra hno
  push Not at hno
  have hall : ∀ w, RxN S 2 w → w < ConjT.th S → w < ζ := fun w hw hwθ => by
    by_contra hc
    push Not at hc
    exact absurd hwθ (not_lt.2 (hno w hw hc))
  set C := {w | RxN S (2 : Ordinal.{0}) w ∧ w < ConjT.th S} with hC
  have hne : C.Nonempty := ⟨0, RxN.zero, hθSC.1⟩
  have hbdd : BddAbove C := ⟨ζ, fun w hw => (hall w hw.1 hw.2).le⟩
  set σ := sSup C with hσ
  have hsζ : σ ≤ ζ := csSup_le hne fun w hw => (hall w hw.1 hw.2).le
  have hθ2 : ConjT.th S < Om (1 + 1) := psi_lt (InR_Om_succ 1) _
  have hcode : ∀ x ∈ S.CSet (Om ω) σ, x < Om ω → ∃ w, RxN S 2 w ∧ w ∈ S.CSet (Om ω) (ConjT.th S) ∧
      w < Om ω ∧ x ≤ w ∧ (x < Om (1 + 1) → w < ConjT.th S) := by
    intro x hx
    induction hx with
    | small h =>
      intro _
      obtain ⟨w, ⟨hw, hwθ⟩, hxw⟩ := exists_lt_of_lt_csSup hne h
      exact ⟨w, hw, CSet.of_lt hwθ, hwθ.trans (hθ2.trans (Om_lt_Om.2 (by
        rw [one_add_one_eq_two]; exact_mod_cast natCast_lt_omega0 2))), hxw.le, fun _ => hwθ⟩
    | zero => exact fun _ => ⟨0, RxN.zero, CSet.zero_mem _ _, Om_pos omega0_ne_zero, le_rfl,
        fun _ => hθSC.1⟩
    | inacc n => exact fun h => absurd h (rxFix_not_ltW (SC_I (S := S) n) (Om_I n))
    | inaccW => exact fun h => absurd h (rxFix_not_ltW (SC_Iw (S := S)) S.Om_Iw)
    | @add u v _ _ ihu ihv =>
      intro h
      obtain ⟨w1, hw1, hc1, hl1, hu, hθ1⟩ := ihu (lt_of_le_of_lt le_self_add h)
      obtain ⟨w2, hw2, hc2, hl2, hv, hθ2'⟩ := ihv (lt_of_le_of_lt le_add_self h)
      refine ⟨w1 + w2, RxN.add hw1 hw2, CSet.add_mem hc1 hc2,
        (SC_Om omega0_ne_zero).isPrincipal hl1 hl2, add_le_add hu hv, fun h2' => ?_⟩
      exact hθSC.isPrincipal (hθ1 (lt_of_le_of_lt le_self_add h2')) (hθ2' (lt_of_le_of_lt le_add_self h2'))
    | @phi u v _ _ ihu ihv =>
      intro h
      obtain ⟨w1, hw1, hc1, hl1, hu, hθ1⟩ := ihu (lt_of_le_of_lt (left_le_veblen u v) h)
      obtain ⟨w2, hw2, hc2, hl2, hv, hθ2'⟩ := ihv (lt_of_le_of_lt (right_le_veblen u v) h)
      refine ⟨veblen w1 w2, RxN.phi hw1 hw2, CSet.phi_mem hc1 hc2, (SC_Om omega0_ne_zero).2 _ hl1 _ hl2,
        (veblen_left_monotone v hu).trans (veblen_le_veblen_iff_right.2 hv), fun h2' => ?_⟩
      exact hθSC.2 _ (hθ1 (lt_of_le_of_lt (left_le_veblen u v) h2')) _
        (hθ2' (lt_of_le_of_lt (right_le_veblen u v) h2'))
    | @om p _ _ =>
      intro h
      obtain ⟨k, hk⟩ := lt_omega0.1 (Om_lt_Om.1 h)
      subst hk
      refine ⟨Om (k : Ordinal.{0}), RxN.om (rxN_nat k), rxC_Om_nat _ _ k, h, le_rfl, fun h2' => ?_⟩
      have hk1 : (k : Ordinal.{0}) ≤ 1 := Order.lt_add_one_iff.1 (Om_lt_Om.1 h2')
      exact (Om_le_Om.2 hk1).trans_lt (psiS_bounds (S := S) _ 1).1
    | @coll π y hπ _ _ _ ihy =>
      intro h
      show ∃ w, RxN S 2 w ∧ w ∈ S.CSet (Om ω) (ConjT.th S) ∧ w < Om ω ∧ S.psi y.1 π ≤ w ∧
        (S.psi y.1 π < Om (1 + 1) → w < ConjT.th S)
      change S.psi y.1 π < Om ω at h
      rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
      · exact absurd h (rxFix_not_ltW (SC_psi (InR_I n) _) (Om_psiI _ n))
      · obtain ⟨k, rfl⟩ := lt_omega0.1 (Om_lt_Om.1 ((psiS_bounds (S := S) y.1 s).1.trans h))
        rcases Nat.eq_zero_or_pos k with hk0 | hk
        · subst hk0
          refine ⟨Om 1, by simpa using RxN.om (rxN_nat (S := S) (T := 2) 1), by
            simpa using rxC_Om_nat (S := S) (Om ω) (ConjT.th S) 1, Om_lt_Om.2 one_lt_omega0, ?_,
            fun _ => (psiS_bounds (S := S) _ 1).1⟩
          exact (psi_lt (S := S) (InR_Om_succ _) y.1).le.trans_eq (by simp)
        · obtain ⟨w, hw, hwC, hwW, hyw, -⟩ := ihy y.2
          have hwN : RxN S 2 (S.psi w (Om ((k : Ordinal.{0}) + 1))) :=
            rxN_psi h2 w hw _ (InR_Om_succ _) (rxNat_ne_one hk) (RxN.om (RxN.succ (rxN_nat k)))
          have hwC' : S.psi w (Om ((k : Ordinal.{0}) + 1)) ∈ S.CSet (Om ω) (ConjT.th S) := by
            rcases lt_or_ge (S.psi w (Om ((k : Ordinal.{0}) + 1))) (ConjT.th S) with hl | hl
            · exact CSet.of_lt hl
            · exact CSet.psi_mem hwW (InR_Om_succ _) (rxC_Om_succ _ _ k) hwC
          refine ⟨_, hwN, hwC', (psi_lt (InR_Om_succ _) _).trans (Om_lt_Om.2 ?_),
            (psi_mono (S := S) (InR_Om_succ _) hyw).1, fun h2' => ?_⟩
          · exact_mod_cast (show ((k + 1 : ℕ) : Ordinal.{0}) < ω from natCast_lt_omega0 _)
          · have hk1 : k = 1 := by
              have h3 : (k : Ordinal.{0}) < 1 + 1 :=
                Om_lt_Om.1 ((psiS_bounds (S := S) y.1 (k : Ordinal.{0})).1.trans h2')
              have : k < 2 := by
                have h4 : (k : Ordinal.{0}) < 2 := by rwa [one_add_one_eq_two] at h3
                exact_mod_cast h4
              omega
            subst hk1
            simp only [Nat.cast_one]
            exact psi_lt_psi_of_mem (InR_Om_succ 1) hwW hwC
  have hP : ConjT.th S ≤ σ := by
    refine psi_le_of_good (mxOm2_mem _ _) fun x hx hx2 => ?_
    obtain ⟨w, hw, -, -, hxw, hwθ⟩ := hcode x hx (hx2.trans (Om_lt_Om.2 (by
      rw [one_add_one_eq_two]; exact_mod_cast natCast_lt_omega0 2)))
    have hwθ' := hwθ hx2
    have hw1 : w + 1 ∈ C := ⟨RxN.succ hw, hθSC.add_one_lt hwθ'⟩
    exact hxw.trans_lt ((lt_add_one w).trans_le (le_csSup hbdd hw1))
  exact absurd (hP.trans hsζ) (not_le.2 h)

/-- `θ ∣ A_η + θ·x`. -/
theorem rxDvdTh (η x : Ordinal.{0}) : ConjT.th S ∣ ConjT.Aη S η + ConjT.th S * x := by
  have hG := ConjT.SC_th S
  have hW2 : Om (1 + 1 : Ordinal.{0}) ≤ Om ω := by
    refine (Om_lt_Om.2 ?_).le
    rw [one_add_one_eq_two]; exact_mod_cast natCast_lt_omega0 2
  have hW : ConjT.th S ∣ Om ω := by
    rw [← gg_SC_eps hG, ← gg_SC_eps (SC_Om (omega0_ne_zero : (ω : Ordinal.{0}) ≠ 0))]
    exact opow_dvd_opow ω ((psi_lt (S := S) (InR_Om_succ 1) _).le.trans hW2)
  unfold ConjT.Aη
  exact dvd_add (dvd_add hW (dvd_mul_right _ _)) (dvd_mul_right _ _)

/-- **THE BLOCK STEP BELOW `θ`.** -/
theorem rxBlkTh {μ x : Ordinal.{0}} {k : ℕ} (hR : CdRange S μ) (hc : cdCode S μ = Ls.lsG S (k + 1) + 1)
    (hx : x + 1 < upsilon μ) (hP : upsilon (μ + x) ≤ cdTheta S μ (Lc.lcG S x)) :
    ∀ ζ, ζ < ConjT.th S → ∃ t ∈ Ls.lsAt S (ConjT.Aη S (cdEta S μ)) (upsilon μ), t < Lc.lcG S (x + 1) ∧
      S.psi (ConjT.Aη S (cdEta S μ) + (ConjT.th S * x + ζ)) (Om 1) ≤ cdTheta S μ t := by
  have hX : upsilon μ < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by rw [← Lw.lw_L_eq]; exact hR.2.2.1
  obtain ⟨hZ, hZ1⟩ := Le.leRho hR.1 hX
  have hAt : GxAt (ldAtR S μ) := ldAt_GxAt _ _
  have hxρ : x < upsilon μ := (lt_add_one x).trans hx
  have hx1 : x < Om 1 := Rg.rgGam_lt hR hxρ
  have hθ2SC : SC (Lc.lcTh S 2) := Ls.lsTh_SC 2
  have hθSC := ConjT.SC_th S
  set A := ConjT.Aη S (cdEta S μ) with hAdef
  set β := Om ω + Lc.lcTh S 2 * x with hβdef
  set Â := A + ConjT.th S * x with hÂdef
  set Z2 := gxTh (upsilon μ) (ldAtR S μ) (Om (1 + 1)) with hZ2def
  set W := rxW (upsilon μ) (ldAtR S μ) with hWdef
  set κ := rxL S (upsilon μ) (ldAtR S μ) W with hκdef
  have hW : SC W := rxW_SC hZ hZ1 hAt
  have hW1 : W ≤ Om 1 := min_le_right _ _
  have hTh : ∀ m, m ≤ Om (1 + 1) → cdTheta S μ m = gxTh (upsilon μ) (ldAtR S μ) m :=
    fun m hm => ldTheta hR.1 hX hm
  have hβA : β < A := ruExp_lt hR hc hxρ
  have hβ1A : Om ω + Lc.lcTh S 2 * (x + 1) < A := ruExp_lt hR hc hx
  have hWβ : Om ω ≤ β := le_self_add
  have hWA : Om ω ≤ A := hWβ.trans hβA.le
  have hmemβ : ∀ a b, Om ω < a → x < b → β ∈ S.CSet a b := fun a b ha hb => Rp.rpThx_mem ha hb
  have hβH : β ∈ cdHull S μ := by
    rcases eq_or_ne x 0 with h0 | h0
    · rw [hβdef, h0, mul_zero, add_zero]; exact ConjT.OmW_mem S _ _
    · refine hmemβ _ _ ?_ hxρ
      exact hWβ.trans_lt hβA
  have hθW : ConjT.th S < Om ω := (psi_lt (InR_Om_succ 1) _).trans (Om_lt_Om.2 (by
    rw [one_add_one_eq_two]; exact_mod_cast natCast_lt_omega0 2))
  have hEθ : ∀ {T ζ : Ordinal.{0}}, RxN S T ζ → ζ < ConjT.th S → RxE S T ζ :=
    fun hN hζ => ⟨hN, CSet.of_lt hζ, hζ.trans hθW⟩
  -- the codes `κ ζ` lie in the hull, below `θ₂`
  have hκH : ∀ ζ, RxE S W ζ → κ ζ ∈ cdHull S μ :=
    fun ζ hζ => rxL_memH hZ hZ1 hAt hW le_rfl hWA (fun g hg => by
      obtain ⟨hcode, hlt2, -⟩ := ruInv_spec (hg.trans_le (min_le_left _ _))
      exact (ldHull_iff hR.1 hX hlt2).2 hcode) ζ hζ
  have hκ2 : ∀ ζ, RxE S W ζ → ζ < ConjT.th S → κ ζ < Lc.lcTh S 2 := fun ζ hζ hζθ => by
    rw [rxTh2_eq]; exact rxL_lt_th2 hZ hZ1 hAt ζ hζ hζθ
  have hκθ : ∀ ζ, RxE S W ζ → ζ < ConjT.th S → β + κ ζ < Om ω + Lc.lcTh S 2 * (x + 1) :=
    fun ζ hζ hζθ => by
      rw [mul_add_one, ← add_assoc]
      exact (add_lt_add_iff_left _).2 (hκ2 ζ hζ hζθ)
  have hat : ∀ ζ, RxE S W ζ → ζ < ConjT.th S → S.psi (β + κ ζ) (Om (1 + 1)) ∈ ldAtR S μ :=
    fun ζ hζ hζθ => ⟨_, CSet.add_mem hβH (hκH ζ hζ), (hκθ ζ hζ hζθ).trans hβ1A, rfl⟩
  have hβat : S.psi β (Om (1 + 1)) ∈ ldAtR S μ := ⟨β, hβH, hβA, rfl⟩
  have hbase : S.psi Â (Om 1) ≤ gxTh (upsilon μ) (ldAtR S μ) (S.psi β (Om (1 + 1))) := by
    rw [← hTh _ (psi_lt (InR_Om_succ 1) _).le, ← Rg.rgUps_eq hR hxρ.le]; exact hP
  have hβmem : ∀ ζ, RxE S W ζ → ζ ≠ 0 → β ∈ S.CSet (β + κ ζ) (S.psi (β + κ ζ) (Om (1 + 1))) :=
    fun ζ hζ h0 => hmemβ _ _ (hWβ.trans_lt (lt_add_of_pos_right β (rxL_pos hZ hZ1 hAt hζ h0)))
      (hx1.trans (psiS_bounds (S := S) _ 1).1)
  have hpos : ∀ ζ, RxE S W ζ → ζ ≠ 0 →
      S.psi β (Om (1 + 1)) < S.psi (β + κ ζ) (Om (1 + 1)) := fun ζ hζ h0 =>
    psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right β (rxL_pos hZ hZ1 hAt hζ h0))
      (hβmem ζ hζ h0)
  have hcl : ∀ ζ, RxE S W ζ ∧ ζ < ConjT.th S →
      gxTh (upsilon μ) (ldAtR S μ) (S.psi (β + κ ζ) (Om (1 + 1))) < Om 1 → ∀ e,
      HCl S (Â + ζ) (gxTh (upsilon μ) (ldAtR S μ) (S.psi (β + κ ζ) (Om (1 + 1)))) e →
      Â ≤ e → e < Â + ζ → (RxE S W (e - Â) ∧ e - Â < ConjT.th S) ∧
        β + κ (e - Â) ∈ S.CSet (β + κ ζ) (S.psi (β + κ ζ) (Om (1 + 1))) := by
    intro ζ hζ hcnt e he h1 h2
    set t := S.psi (β + κ ζ) (Om (1 + 1)) with htdef
    set Tt := gxTh (upsilon μ) (ldAtR S μ) t with hTtdef
    have htSC : SC Tt :=
      gxTh_SC hZ hAt (SC_psi (InR_Om_succ 1) _) (hZ1.trans (psiS_bounds (S := S) _ 1).1)
    have hTZ : Tt ≤ Z2 := gxTh_mono (psi_lt (InR_Om_succ 1) _).le
    have hTW : Tt ≤ W := le_min hTZ hcnt.le
    have e1 : e = Â + (e - Â) := (Ordinal.add_sub_cancel_of_le h1).symm
    have hlt : e - Â < ζ := Ry.rySub_lt h1 h2
    have hltθ : e - Â < ConjT.th S := hlt.trans hζ.2
    have hm : e % ConjT.th S = e - Â := by
      conv_lhs => rw [e1]
      rw [ldModK_add_lt hθSC Â hltθ, Ordinal.mod_eq_zero_of_dvd (rxDvdTh (cdEta S μ) x), zero_add]
    have hN : RxN S Tt (e - Â) := by
      rw [← hm]; exact rxN_of_HCl hcnt.le (ruHCl_modK hθSC he)
    have hET : RxE S Tt (e - Â) := hEθ hN hltθ
    refine ⟨⟨hET.mono hTW, hltθ⟩, CSet.add_mem ?_ ?_⟩
    · have hζ0 : ζ ≠ 0 := fun h => by rw [h] at hlt; exact absurd hlt (not_lt.2 zero_le)
      exact hβmem ζ hζ.1 hζ0
    · exact rxL_memH hZ hZ1 hAt htSC hTW (hWβ.trans le_self_add)
        (fun g hg' => CSet.of_lt (ruInv_spec hg').2.1) _ hET
  have hLift := rxLift hZ hZ1 hAt hβat hbase (D := {ζ | RxE S W ζ ∧ ζ < ConjT.th S})
    (fun ζ hζ ζ' hζ' h => rxL_mono hZ hZ1 hAt hζ'.1 hζ.1 h) (fun ζ hζ => hat ζ hζ.1 hζ.2)
    (fun ζ hζ h0 => hpos ζ hζ.1 h0) hcl
  intro ζ hζE
  obtain ⟨w, hw, hn, hwθ⟩ := rxCofTh hζE
  have hwD : RxE S W w := hEθ (hw.mono (ruTwo_le hW)) hwθ
  set t := S.psi (β + κ w) (Om (1 + 1)) with htdef
  have hG1 : Lc.lcG S (x + 1) = S.psi (Om ω + Lc.lcTh S 2 * (x + 1)) (Om (1 + 1)) := rfl
  have htlt : t < Lc.lcG S (x + 1) := by
    rw [hG1]
    refine psi_lt_psi_of_mem (InR_Om_succ 1) (hκθ w hwD hwθ) (CSet.add_mem ?_ ?_)
    · refine hmemβ _ _ ?_ (hx1.trans (psiS_bounds (S := S) _ 1).1)
      exact lt_add_of_pos_right _ (mul_pos hθ2SC.1 (lt_of_le_of_lt zero_le (lt_add_one x)))
    · set T1 := gxTh (upsilon μ) (ldAtR S μ) (Lc.lcG S (x + 1)) with hT1def
      have hT1SC : SC T1 :=
        gxTh_SC hZ hAt (SC_psi (InR_Om_succ 1) _) (hZ1.trans (psiS_bounds (S := S) _ 1).1)
      have hTZ : T1 ≤ Z2 := gxTh_mono (Lc.lcG_lt_Om2 _).le
      have hmSC : SC (min T1 (Om 1)) := by
        rcases le_total T1 (Om 1) with h | h
        · rw [min_eq_left h]; exact hT1SC
        · rw [min_eq_right h]; exact Ph.ph_SC_Om1
      have hmW : min T1 (Om 1) ≤ W := min_le_min_right _ hTZ
      exact rxL_memH hZ hZ1 hAt hmSC hmW le_self_add
        (fun g hg' => CSet.of_lt (ruInv_spec (hg'.trans_le (min_le_left _ _))).2.1) w
        (hEθ (hw.mono (ruTwo_le hmSC)) hwθ)
  refine ⟨t, ?_, htlt, ?_⟩
  · rw [Le.leAt_eq]; exact hat w hwD hwθ
  · rw [hTh t (psi_lt (InR_Om_succ 1) _).le, ← add_assoc]
    exact (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left Â).2 hn)).1.trans
      (hLift w ⟨hwD, hwθ⟩)

/-- **`Ru.RuBlkHi` is a theorem** (given the base reading). -/
theorem rxBlkHi {μ x : Ordinal.{0}} {k : ℕ} (hR : CdRange S μ) (hc : cdCode S μ = Ls.lsG S (k + 1) + 1)
    (hx : x + 1 < upsilon μ) (hP : upsilon (μ + x) ≤ cdTheta S μ (Lc.lcG S x)) : RuBlkHi S μ x :=
  fun ζ _ hζ => rxBlkTh hR hc hx hP ζ hζ

/-- **`Rp.RpBlkAt`** from the base reading. -/
theorem rxBlkAt {μ x : Ordinal.{0}} {k : ℕ} (hR : CdRange S μ) (hc : cdCode S μ = Ls.lsG S (k + 1) + 1)
    (hx : x + 1 < upsilon μ) (hP : upsilon (μ + x) ≤ cdTheta S μ (Lc.lcG S x)) : Rp.RpBlkAt S μ x :=
  fun ζ hζ => rxBlkTh hR hc hx hP ζ hζ

/-- **`Rp.RpReadAll S k` for every `k`.** -/
theorem rxReadAll (k : ℕ) : Rp.RpReadAll S k :=
  Rp.rpReadAll_of_blkAt fun _ hR _ hc _ hx hP => rxBlkAt hR hc hx hP

/-- **`Rg.RgCoverAt` at `m* = L(0)` and at every `L(n+1)`.** -/
theorem rxCover (k : ℕ) :
    Rg.RgCoverAt S (Nc.ncL S 0) ∧ ∀ n : ℕ, Rg.RgCoverAt S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) :=
  Rp.rpCover_of_read (rxReadAll (S := S) k)

/-- **`Ra.RaSupAt` at `m* = L(0)` and at every `L(n+1)`.** -/
theorem rxSupAt : Ra.RaSupAt S (Nc.ncL S 0) ∧ ∀ n : ℕ, Ra.RaSupAt S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) :=
  ⟨Rg.rgSupAt_of_cover (rxCover (S := S) 0).1, fun n => Rg.rgSupAt_of_cover ((rxCover (S := S) 0).2 n)⟩

/-- **The road `Ru.ruRoad` without its `RuBlkHi` hypothesis.** -/
theorem rxRoadT {k : ℕ} (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S)
    (h0 : Lr.LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Nc.ncL S 0)))
    (hn : ∀ n : ℕ, Lr.LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
    (hout : Rp.RpLnOut S)
    (hgap : Lr.LrGap S (Nc.ncL S ω) (Nc.ncL S (ω + 1)) (upsilon (Nc.ncL S ω + Nc.ncL S ω)))
    (hmove : Cx.CxStdMoveTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  ruRoad (k := k) hU hO hL hV hVt hEQ htop (fun _ hR _ hc _ hx hP => rxBlkHi hR hc hx hP) h0 hn hout hgap hmove

/-- **Under UPPER, LOWER, CapV and the gap at `L(ω)`: `RpLnOut ⇔ T`** (`Ru.ruOut_iff_T` without `RuBlkHi`). -/
theorem rxOut_iff_T (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hgap : Lr.LrGap S (Nc.ncL S ω) (Nc.ncL S (ω + 1)) (upsilon (Nc.ncL S ω + Nc.ncL S ω))) :
    Rp.RpLnOut S ↔ Cx.CxT S :=
  ruOut_iff_T (k := 0) hU hL hV hVt (fun _ hR _ hc _ hx hP => rxBlkHi hR hc hx hP) hgap

/-- **Under UPPER, LOWER, CapV and the gap at `L(ω)`: `L(ω+1) ≤ ν_C ⇔ L(ω) ≤₁ L(ω+1)`.** -/
theorem rxNu_iff_T (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hgap : Lr.LrGap S (Nc.ncL S ω) (Nc.ncL S (ω + 1)) (upsilon (Nc.ncL S ω + Nc.ncL S ω))) :
    Nc.ncL S (ω + 1) ≤ nuC ↔ Cx.CxT S :=
  (ruOut_iff_nu hU hV hVt).symm.trans (rxOut_iff_T hU hL hV hVt hgap)

/-- **The road with `L(ω+1) ≤ ν_C`** (`Ru.ruRoad_nu` without `RuBlkHi`). -/
theorem rxRoad_nu {k : ℕ} (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S)
    (h0 : Lr.LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Nc.ncL S 0)))
    (hn : ∀ n : ℕ, Lr.LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
    (hν : Nc.ncL S (ω + 1) ≤ nuC)
    (hgap : Lr.LrGap S (Nc.ncL S ω) (Nc.ncL S (ω + 1)) (upsilon (Nc.ncL S ω + Nc.ncL S ω)))
    (hmove : Cx.CxStdMoveTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  ruRoad_nu (k := k) hU hO hL hV hVt hEQ htop (fun _ hR _ hc _ hx hP => rxBlkHi hR hc hx hP) h0 hn hν hgap
    hmove

/-- **The road `Ra.raRoad_T` without its `RaSupAt` hypotheses** (at `L(ω)` only `T` is asked). -/
theorem rxRoadRa (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S) (hups : Cx.CxUpsRestTop S)
    (h0 : Lr.LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Nc.ncL S 0)))
    (hn : ∀ n : ℕ, Lr.LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
    (hT : Cx.CxT S) (hmove : Cx.CxStdMoveTop S) (hstd : Cx.CxStdPairTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Ra.raRoad_T hU hO hL hV hEQ htop hups rxSupAt.1 rxSupAt.2 h0 hn hT hmove hstd

end Googology.Trans.PoR.InaccPsi.R2.Rx
