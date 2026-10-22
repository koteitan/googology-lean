import Googology.Trans.PoR.InaccPsi.R2.RhMove4

/-!
# The base property of `B_n`: `B_n(F_β(c₀(β))) = F_{B_n β}(c₀(B_n β))`, proved

`ψ = S.psi`, `F_β = Rh.rhF β`, `u_β = Ω₁^β`, `c₀(β) = Rh.rhC0 β`, `b₀(β) = F_β(c₀(β))` the least value of `F_β`
above `β`, `B_n = Bc.bcB S n`, `Γ_ = Ordinal.gamma` (its range is the class of strongly critical ordinals).

* `rh_dvd_add_self` (`u ∣ a + u` for `u = u_β`), `rh_own_inj` (own arguments with equal collapses are equal);
* `rh_least` (**`b₀(β) = ψ_{Ω₁}(K_c + u_β)`** for `β ≥ 1`, where `c = ψ_{Ω₁}(K_c)` is a strongly critical point with
  `c ≤ β < ψ_{Ω₁}(K_c + 1)`, i.e. the largest strongly critical point `≤ β`: `ψ_{Ω₁}(K_c + u_β)` is a value of `F_β`
  above `β` (`Rh.rh_fwd`), and a value `ψ_{Ω₁}(V)` of `F_β` in `(β, ψ_{Ω₁}(K_c + u_β))` would have `u_β ∣ V` and
  `K_c < V < u_β·(K_c / u_β) + u_β`);
* `rh_gamma_below` (**`Γ(e₀) ≤ β < Γ(e₀ + 1)`** for some `e₀`, once `Γ(0) ≤ β`);
* `rhBase` (**`Rh.RhBase S`, unconditionally**): `c = Γ(e₀)`, `B_n c = ψ_{Ω₁}(K_c')`,
  `B_n(ψ_{Ω₁}(K_c + 1)) = ψ_{Ω₁}(K_c' + 1)` and `B_n(ψ_{Ω₁}(K_c + u_β)) = ψ_{Ω₁}(K_c' + u_{B_n β})` (`Rd.rdB_psi_baseD`,
  `Le.leB_Oe1`), so `B_n c ≤ B_n β < ψ_{Ω₁}(K_c' + 1)` and `rh_least` at `B_n β`;
* `rhLhTopC_of_G` (**`Rh.RhLhTopG` alone gives `Rh.RhLhTopC`**), `rhLhTopW_of_G` (**… gives `Rd.RdLhTopW`**),
  `rhLhTopFix_of_G`, `rhSfLhTG`, `rhRoadG2` (the road `Rb.rbRoad` with `RhLhTopG` only).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb
  Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2.Bc

variable {S : InaccSeq.{0}}

/-- `u_β ∣ a + u_β`. -/
theorem rh_dvd_add_self (β a : Ordinal.{0}) : Le.leOe β ∣ a + Le.leOe β := by
  set u := Le.leOe β
  have hu := rhU_indec β
  refine ⟨a / u + 1, ?_⟩
  calc a + u = u * (a / u) + (a % u + u) := by rw [← add_assoc, Ordinal.div_add_mod]
    _ = u * (a / u) + u := by
        have := rdk_absorb hu (Ordinal.mod_lt a hu.ne_zero) (le_refl (1 : Ordinal.{0}))
        rw [mul_one] at this; rw [this]
    _ = u * (a / u + 1) := by rw [mul_add, mul_one]

/-- Own arguments with equal collapses are equal. -/
theorem rh_own_inj {a b : Ordinal.{0}} (ha : a ∈ S.CSet a (S.psi a (Om 1))) (hb : b ∈ S.CSet b (S.psi b (Om 1)))
    (h : S.psi a (Om 1) = S.psi b (Om 1)) : a = b := by
  have hc := compare_psi Low.InR_Om_one ha hb
  rw [h, compare_eq_iff_eq.2 rfl] at hc
  exact compare_eq_iff_eq.1 hc.symm

/-- **`b₀(β) = F_β(c₀(β)) = ψ_{Ω₁}(K_c + u_β)`** (`β ≥ 1`) for an own `K_c` with `ψ_{Ω₁}(K_c) ≤ β < ψ_{Ω₁}(K_c + 1)`;
`K_c + u_β` is own. -/
theorem rh_least {β Kc : Ordinal.{0}} (hβ1 : 1 ≤ β) (hown : Kc ∈ S.CSet Kc (S.psi Kc (Om 1)))
    (hcβ : S.psi Kc (Om 1) ≤ β) (hβs : β < S.psi (Kc + 1) (Om 1)) :
    rhF β (rhC0 β) = S.psi (Kc + Le.leOe β) (Om 1) ∧
      Kc + Le.leOe β ∈ S.CSet (Kc + Le.leOe β) (S.psi (Kc + Le.leOe β) (Om 1)) := by
  set u := Le.leOe β with hudef
  set E := Kc + u with hEdef
  have hu0 : u ≠ 0 := rhU_ne β
  have h1u : (1 : Ordinal.{0}) ≤ u := one_le_iff_ne_zero.2 hu0
  have hβ0 : β ≠ 0 := (lt_of_lt_of_le zero_lt_one hβ1).ne'
  have hβE : β < S.psi E (Om 1) :=
    hβs.trans_le (psi_mono (S := S) Low.InR_Om_one (add_le_add_right h1u Kc)).1
  have hownE : E ∈ S.CSet E (S.psi E (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hown) (rhU_mem hβE)
  have hdvdE : u ∣ E := rh_dvd_add_self β Kc
  have hE0 : E ≠ 0 := (lt_of_lt_of_le (rhU_pos β) le_add_self).ne'
  -- `ψ_{Ω₁}(E)` is a value of `F_β`
  have hfixE : ∀ j < β, rhF j (S.psi E (Om 1)) = S.psi E (Om 1) := fun j hj =>
    rh_fwd j E hownE ((rhU_dvd_succ hj).trans hdvdE) hE0 (hj.trans hβE)
  obtain ⟨eE, heE⟩ := rhF_range (SC_psi Low.InR_Om_one E) hfixE
  -- no value of `F_β` in `(β, ψ_{Ω₁}(E))`
  have hnone : ∀ v, β < v → v < S.psi E (Om 1) → (∀ j < β, rhF j v = v) → SC v → False := by
    intro v hβv hvE hvF hvSC
    obtain ⟨V, hownV, hV⟩ := rb_own_of_SC hvSC hvE
    have hdvdV : u ∣ V := rh_dvd_of_range hβ0 hownV (by rw [hV]; exact hvF)
    have hown1 : Kc + 1 ∈ S.CSet (Kc + 1) (S.psi (Kc + 1) (Om 1)) :=
      CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hown) (CSet.one_mem _ _)
    have hc1 : S.psi (Kc + 1) (Om 1) ≤ v := by
      refine not_lt.1 fun hlt => ?_
      have hcv : S.psi Kc (Om 1) < S.psi V (Om 1) := by rw [hV]; exact hcβ.trans_lt hβv
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
            have := rdk_absorb (rhU_indec β) (Ordinal.mod_lt Kc hu0) (le_refl (1 : Ordinal.{0}))
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
  obtain ⟨hc0, hmin0, -⟩ := rhC0_spec β
  refine ⟨le_antisymm ?_ ?_, hownE⟩
  · -- `F_β(c₀) ≤ ψ_{Ω₁}(E)`: `ψ_{Ω₁}(E) = F_β(e)` with `e ≥ c₀`
    rw [← heE]
    refine (rhF_le β).2 (not_lt.1 fun hlt => ?_)
    have := hmin0 eE hlt
    rw [heE] at this
    exact absurd hβE (not_lt.2 this)
  · refine not_lt.1 fun hlt => hnone _ hc0 hlt (fun j hj => rhF_fix_lower hj _) (rhF_SC β _)

/-- **`Γ(e₀) ≤ β < Γ(e₀ + 1)`** for some `e₀`, once `Γ(0) ≤ β`. -/
theorem rh_gamma_below {β : Ordinal.{0}} (h0 : gamma 0 ≤ β) : ∃ e0, gamma e0 ≤ β ∧ β < gamma (e0 + 1) := by
  classical
  have hex : ∃ e, β < gamma e := ⟨β + 1, (lt_add_one β).trans_le (lq_le_gamma _)⟩
  obtain ⟨e1, he1, hmin⟩ := WellFounded.has_min wellFounded_lt {e | β < gamma e} hex
  have hle : ∀ e < e1, gamma e ≤ β := fun e he => not_lt.1 fun h => hmin e h he
  rcases zero_or_succ_or_isSuccLimit e1 with hz | ⟨e0, rfl⟩ | hl
  · rw [hz] at he1; exact absurd h0 (not_le.2 he1)
  · rw [Order.succ_eq_add_one] at he1 hle
    exact ⟨e0, hle e0 (lt_add_one e0), he1⟩
  · exact absurd ((isNormal_gamma.le_iff_forall_le hl).2 fun e he => hle e he) (not_le.2 he1)

/-- **`Rh.RhBase S`: `B_n(F_β(c₀(β))) = F_{B_n β}(c₀(B_n β))`** at every level `β` of a window. -/
theorem rhBase : RhBase S := by
  intro n ξ ξ' β hc hτβ hb0 hξ1lt hBξ hBξ1
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Qq.qqL_lt_omega S (n + 1 + 1)
  have hβb : β < rhF β (rhC0 β) := (rhC0_spec β).1
  have hβX : β < Bc.bcC S (n + 1) := (hβb.trans hb0).trans hξ1lt
  have hβL : β < Nc.ncL S ω := hβX.trans hLw
  have hOm : Nc.ncL S ω < Om 1 := InaccSeq.psi_lt Low.InR_Om_one _
  have hβΩ : β < Om 1 := hβL.trans hOm
  have hωC : (ω : Ordinal.{0}) < Bc.bcC S n := Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)
  have hτL : upsilon ξ < Nc.ncL S ω := hτβ.trans hβL
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    rw [upsilon_zero] at hc
    exact absurd (lt_of_lt_of_le (omega0_pos.trans hωC) hc) (lt_irrefl _)
  have hτL0 : upsilon ξ < Nm.Pv S (Om ω + Nc.ncPp S * ω) := by rw [← Lw.lw_L_eq S]; exact hτL
  have hτSC : SC (upsilon ξ) := mvUps_SC hξ0 hτL0
  have hβ1 : 1 ≤ β :=
    one_le_iff_ne_zero.2 ((lt_of_le_of_lt zero_le (hτSC.1.trans hτβ))).ne'
  -- `c = Γ(e₀)` the largest strongly critical point `≤ β`
  obtain ⟨eτ, heτ⟩ := lq_SC_gamma hτSC
  have hg0 : gamma 0 ≤ β := ((gamma_le_gamma.2 zero_le).trans_eq heτ).trans hτβ.le
  obtain ⟨e0, hce, hβe⟩ := rh_gamma_below hg0
  set c := gamma e0 with hcdef
  have hτc : upsilon ξ ≤ c := by
    rw [← heτ]
    refine gamma_le_gamma.2 (Order.lt_add_one_iff.1 (gamma_lt_gamma.1 ?_))
    rw [heτ]; exact hτβ.trans hβe
  have hcW : c < S.psi (bcAlphaW S) (Om 1) := by
    rw [← Bc.ncL_omega_eq S]; exact hce.trans_lt hβL
  obtain ⟨Kc, hownc, hBc⟩ := rb_own_of_SC (lq_gamma_SC e0) hcW
  -- `β < ψ_{Ω₁}(K_c + 1)`
  have hown1 : Kc + 1 ∈ S.CSet (Kc + 1) (S.psi (Kc + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hownc) (CSet.one_mem _ _)
  have hβs : β < S.psi (Kc + 1) (Om 1) := by
    have hcs : c < S.psi (Kc + 1) (Om 1) := by
      rw [hcdef, ← hBc]; exact rh_psi_lt_of_own hownc (lt_add_one Kc)
    obtain ⟨e, he⟩ := lq_SC_gamma (SC_psi Low.InR_Om_one (Kc + 1))
    rw [← he] at hcs ⊢
    have h1 : e0 < e := gamma_lt_gamma.1 hcs
    exact hβe.trans_le (gamma_le_gamma.2 (Order.add_one_le_of_lt h1))
  obtain ⟨hleast, hownE⟩ := rh_least hβ1 hownc (by rw [hBc]; exact hce) hβs
  rw [hleast] at hb0 ⊢
  have hlo : Bc.bcC S n ≤ S.psi Kc (Om 1) := by rw [hBc]; exact hc.trans hτc
  have hEX : S.psi (Kc + Le.leOe β) (Om 1) < Bc.bcC S (n + 1) := hb0.trans hξ1lt
  have h1X : S.psi (Kc + 1) (Om 1) < Bc.bcC S (n + 1) :=
    ((psi_mono (S := S) Low.InR_Om_one (add_le_add_right (one_le_iff_ne_zero.2 (rhU_ne β)) Kc)).1).trans_lt hEX
  have h1Lw : (1 : Ordinal.{0}) < Nc.ncL S ω := by
    have := mw_nat_lt_L (S := S) 1; rwa [Nat.cast_one] at this
  obtain ⟨hDu, hBu⟩ := Le.leB_Oe1 (S := S) (n := n) hβΩ hβX
  obtain ⟨r, -, -, hownB', hBc', hBE⟩ := rdB_psi_baseD hownc hlo hownE hEX hDu
  obtain ⟨r2, -, -, hownB2, hBc2, hB1⟩ := rdB_psi_baseD hownc hlo hown1 h1X (mvD_of_lt h1Lw)
  set B' := bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) with hB'def
  set B2 := bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r2) with hB2def
  have hB2eq : B2 = B' := rh_own_inj hownB2 hownB' (hBc2.symm.trans hBc')
  rw [hB2eq, mwB_one] at hB1
  rw [hBu] at hBE
  rw [hBE]
  -- `B_n c ≤ B_n β < ψ_{Ω₁}(B' + 1)`
  have hcL : c < Nc.ncL S ω := hce.trans_lt hβL
  have h1L : S.psi (Kc + 1) (Om 1) < Nc.ncL S ω := h1X.trans hLw
  have hc' : S.psi B' (Om 1) ≤ Bc.bcB S n β := by
    rw [← hBc', hBc]
    rcases hce.lt_or_eq with hlt | heq
    · exact ((Bc.bcB_lt_iff hcL hβL).2 hlt).le
    · exact (congrArg (Bc.bcB S n) heq).le
  have hβ' : Bc.bcB S n β < S.psi (B' + 1) (Om 1) := by
    rw [← hB1]; exact (Bc.bcB_lt_iff hβL h1L).2 hβs
  have hβ'1 : 1 ≤ Bc.bcB S n β := by
    rcases hβ1.lt_or_eq with hlt | heq
    · have := (Bc.bcB_lt_iff (k := n) h1Lw hβL).2 hlt
      rw [mwB_one] at this; exact this.le
    · rw [← heq, mwB_one]
  exact (rh_least hβ'1 hownB' hc' hβ').1.symm

/-! ## The move at the fixed points of the levels below `τ`: only the points fixed by every `F_j`, `j < x`, are left -/

/-- **`Rh.RhLhTopG` alone gives `Rh.RhLhTopC`.** -/
theorem rhLhTopC_of_G (hG : RhLhTopG S) : RhLhTopC S := rhLhTopC_of rhBase hG

/-- **`Rh.RhLhTopG` gives `Rd.RdLhTopW`.** -/
theorem rhLhTopW_of_G (hG : RhLhTopG S) : RdLhTopW S := rhLhTopW_of_BG rhBase hG

/-- **`Rh.RhLhTopG` gives `Rb.RbLhTopFix`.** -/
theorem rhLhTopFix_of_G (hG : RhLhTopG S) : RbLhTopFix S := rhLhTopFix_of_BG rhBase hG

/-- **`Rh.RhLhTopG` gives `Sf.SfLhTMove`.** -/
theorem rhSfLhTG (hG : RhLhTopG S) : Sf.SfLhTMove S := rhSfLhTBG rhBase hG

/-- `Rd.RdLhTopW` gives `Rh.RhLhTopG` (so the two hypotheses are equivalent). -/
theorem rhLhTopG_of_W (h : RdLhTopW S) : RhLhTopG S := by
  intro n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hxSC hG
  refine h n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hxSC fun k => ?_
  have hkx : (k : Ordinal.{0}) < x := (natCast_lt_omega0 k).trans (omega0_lt_inE hE)
  rw [← rhF_nat]; exact hG _ hkx

/-- **The road `Rb.rbRoad` (= `Rd.rdRoadW`) with `RhLhTopG` in place of `Rd.RdLhTopW`.** -/
theorem rhRoadG2 (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hG : RhLhTopG S) (hth : Nc.ncL S (ω + 1) ≤ nuC → MxThMoveW S)
    (hhi : Nc.ncL S (ω + 1) ≤ nuC → MxEQth S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rhRoadBG hU hO hL hV hN rhBase hG hth hhi

end Googology.Trans.PoR.InaccPsi.R2.Rh
