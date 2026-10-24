import Googology.Trans.PoR.InaccPsi.R2.SsTh

/-!
# `B_n` moves `ϑ^β(ε_{Ω₁+1} + e)` at every level-closed base `β`: the first case of `Sp.SpVtTopAll`

`B_n = Bc.bcB S n`, `c_n = L(n+1) = Bc.bcC S n`, `ϑ^β = vt β`, `E₁ = ε_{Ω₁+1} = Gg.ggE`, `Φ_{E₁} = Rk.rkP E₁` (the
enumeration of the level-closed points), `SpLC` the level-closed ordinals.

* `ssB_arg` (**`B_n(E₁ + e) = E₁ + B_n e`** for `e < L(ω)`);
* `ssVt_core` (**the move at the level `E₁`**: for a level-closed base `t` with `c_n ≤ t < x = ϑᵗ(E₁ + η) < u <
  c_{n+1}`, `[0, u) ⊆ Tᵗ`, `[0, B_n u) ⊆ T^{B_n t}`, `B_n t` level-closed, `η ∈ Tᵗ ∩ Ω₁`: **`B_n x = ϑ^{B_n t}(E₁ +
  B_n η)`**; `x = Φ_{E₁}(c + 1 + δ) = ψ_{Ω₁}(A_t + E₁·(1 + δ))` from the base `t = Φ_{E₁}(c) = ψ_{Ω₁}(A_t)`
  (`Ss.ssK_enum`, `Ss.ssEq`), or `x = Φ_{E₁}(p + 1 + δ) = ψ_{Ω₁}(B_p + E₁·(1 + δ))` from the largest fixed point `p
  ∈ (t, x)` of `Φ_{E₁}` (`Ss.ssK_enum_fix2`, `Ss.ssConv`, `Ss.ssFwd`); `B_n` moves `ψ_{Ω₁}` (`Rk.rkB_psi` at
  `μ = E₁`) and keeps `u_{E₁}`, `u_{E₁+1}` dividing (`Ss.ssB_dvd0`, `Ss.ssB_dvd1`));
* `ssWin` (**the window of a level-closed `β ∈ [c_n, c_{n+1})`**: `Tᵝ ∩ Ω₁ = u`, `T^{B_n β} ∩ Ω₁ = B_n u` with `u <
  c_{n+1}`, for `υ`-points and for the others);
* `ssVtE1` (**`B_n(ϑ^β(E₁ + e)) = ϑ^{B_n β}(E₁ + B_n e)` for every level-closed `β < c_{n+1}` and `e ∈ Tᵝ ∩ Ω₁`**,
  with no hypothesis), `ssVtTopE1` (**`Sm.SmVtTop` on the arguments `[E₁, E₁ + Ω₁)`**);
* `SsVtTopHi S` (a hypothesis name: `Sm.SmVtTop` on the arguments `[E₁ + Ω₁, Ω₂)` at every level-closed base),
  `ssVtTopAll_iff` (**`Sp.SpVtTopAll S ↔ SsVtTopHi S`**).

No new axiom.  New definition: the hypothesis name `SsVtTopHi`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ss

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb Googology.Trans.PoR.InaccPsi.R2.Rd
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Rh
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rk Googology.Trans.PoR.InaccPsi.R2.Sp

variable {S : InaccSeq.{0}}

/-- **`B_n(E₁ + e) = E₁ + B_n e`** for `e < L(ω)`. -/
theorem ssB_arg {n : ℕ} {e : Ordinal.{0}} (heL : e < Nc.ncL S ω) :
    MvD S (ggE + e) ∧ Bc.bcB S n (ggE + e) = ggE + Bc.bcB S n e := by
  obtain ⟨hD, hB, -⟩ := ssB_E1 (S := S) (n := n)
  obtain ⟨h1, h2⟩ := mvB_add (k := n) hD (mvD_of_lt heL)
  exact ⟨h1, by rw [h2, hB]⟩

/-- A non-fixed index of `Φ_{E₁}`: for `Φ_{E₁}(c) = t` with no fixed point of `Φ_{E₁}` in `(t, x)`, `x = Φ_{E₁}(y)`
not a fixed point, every `z ∈ (c, y]` has `z < Φ_{E₁}(z)`. -/
theorem ss_nofix_idx {t x y c : Ordinal.{0}} (hy : rkP ggE y = x) (hnf : rkP ggE x ≠ x)
    (hct : rkP ggE c = t) (hnofix : ∀ z, t < z → z < x → z < rkP ggE z) :
    ∀ z, c < z → z ≤ y → z < rkP ggE z := by
  intro z hcz hzy
  refine lt_of_le_of_ne (rkP_le_self ggE z) fun hz => ?_
  have htz : t < z := by rw [← hct, hz]; exact (rkP_lt_iff ggE).2 hcz
  have hzx : z ≤ x := by rw [← hy, hz]; exact (rkP_le_iff ggE).2 hzy
  rcases eq_or_lt_of_le hzx with e | hlt
  · rw [← e] at hnf; exact hnf hz.symm
  · have := hnofix z htz hlt
    rw [← hz] at this
    exact lt_irrefl _ this

/-- **The move at the level `E₁` at a level-closed base `t`**: for `x = ϑᵗ(E₁ + η)` with `c_n ≤ t < c_{n+1}`,
`x < u < c_{n+1}`, `[0, u) ⊆ Tᵗ`, `[0, B_n u) ⊆ T^{B_n t}`, `t` and `B_n t` level-closed, `η ∈ Tᵗ ∩ Ω₁`:
**`B_n x = ϑ^{B_n t}(E₁ + B_n η)`**. -/
theorem ssVt_core {n : ℕ} {t u η : Ordinal.{0}} (hc : Bc.bcC S n ≤ t) (htc : t < Bc.bcC S (n + 1))
    (hx2 : vt t (ggE + η) < u) (huc : u < Bc.bcC S (n + 1)) (hTm : ∀ a, a < u → a ∈ Tset t)
    (hTm' : ∀ a, a < Bc.bcB S n u → a ∈ Tset (Bc.bcB S n t))
    (ht : SpLC t) (ht' : SpLC (Bc.bcB S n t)) (hη : η ∈ Tset t) (hηΩ : η < Om1) :
    Bc.bcB S n (vt t (ggE + η)) = vt (Bc.bcB S n t) (ggE + Bc.bcB S n η) := by
  set x := vt t (ggE + η) with hxdef
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have ht1 : t < Om1 := (Rt.rt_lt_Om1 htc).1
  have ht'1 : Bc.bcB S n t < Om1 := (Rt.rt_lt_Om1 htc).2
  have hu1 : u < Om1 := (Rt.rt_lt_Om1 huc).1
  have hu1' : Bc.bcB S n u < Om1 := (Rt.rt_lt_Om1 huc).2
  have htSC : SC t := ht.1
  have ht'SC : SC (Bc.bcB S n t) := ht'.1
  have hxX : x < Bc.bcC S (n + 1) := hx2.trans huc
  have hxL : x < Nc.ncL S ω := hxX.trans hLw
  have htL : t < Nc.ncL S ω := htc.trans hLw
  have hhi' : Bc.bcB S n x < Bc.bcB S n u := (Bc.bcB_lt_iff hxL (huc.trans hLw)).2 hx2
  have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω := Ri.ri_one_lt_L S
  have hO1 : Om1 = Om 1 := Br.Om1_eq
  have hx1' : x < Om 1 := by rw [← hO1]; exact hx2.trans hu1
  have hBx1 : Bc.bcB S n x < Om 1 := by rw [← hO1]; exact hhi'.trans hu1'
  obtain ⟨-, -, -, htx, -, -, hηx⟩ := ssK_facts htSC ht1 hη hηΩ
  rw [← hxdef] at htx hηx
  have hxSC : SC x := ssK_SC htSC ht1 hη hηΩ
  -- `x = Φ_{E₁}(y)`, not a fixed point of `Φ_{E₁}`
  obtain ⟨y, hy⟩ := ssK_range htSC ht1 ht.2 hη hηΩ
  rw [← hxdef] at hy
  have hnf : rkP ggE x ≠ x := by
    intro hfx
    have hLE := ssK_le htSC ht1 η hη hηΩ
    have h3 : t + η + 1 < x := hxSC.add_one_lt ((lq_SC_indec hxSC).add_lt htx hηx)
    have h4 : rkP ggE (t + η + 1) < x := by
      conv_rhs => rw [← hfx]
      exact (rkP_lt_iff ggE).2 h3
    exact absurd hLE (not_le.2 h4)
  have hyx : y < x := by
    refine lt_of_le_of_ne (hy ▸ rkP_le_self ggE y) fun e => hnf ?_
    rw [← e] at hy ⊢; rw [hy]
  -- the base `t = Φ_{E₁}(c) = ψ_{Ω₁}(A_t)` and its image `B_n t = Φ_{E₁}(c')`
  obtain ⟨c, hct⟩ := ssLC_iff.1 ht
  obtain ⟨c', hct'⟩ := ssLC_iff.1 ht'
  have htW : t < S.psi (bcAlphaW S) (Om 1) := by rw [← Bc.ncL_omega_eq S]; exact htL
  obtain ⟨At, hownA, hpvA⟩ := rb_own_of_SC htSC htW
  have hdvdA : Le.leOe ggE ∣ At := spLC_dvd hownA (by rw [hpvA]; exact ht)
  have hcE : GgCl (Bc.bcC S (n + 1)) ggE := spE_cl (gg_one_lt_of_SC (Lw.lw_L_SC S _))
  obtain ⟨-, hBE, -⟩ := ssB_E1 (S := S) (n := n)
  -- the largest fixed point `p` of `Φ_{E₁}` below `x`, or `t`
  obtain ⟨p, hbase, hpx, hmax⟩ := rh_base_below (rkP_normal ggE) htx hnf
  have htp : t ≤ p := by
    rcases hbase with e | ⟨h, -⟩
    · exact e.ge
    · exact h.le
  have hnofix : ∀ z, p < z → z < x → z < rkP ggE z := by
    intro z hpz hzx
    by_contra h
    push Not at h
    have hz := le_antisymm h (rkP_le_self ggE z)
    exact absurd (hmax z hz (lt_of_le_of_lt htp hpz) hzx) (not_le.2 hpz)
  have hpL : p < Nc.ncL S ω := hpx.trans hxL
  -- the common part: from an index `c₀` with `Φ_{E₁}(c₀) = ψ_{Ω₁}(B₀) ≤ p`, `c₀ < y`
  have common : ∀ (c0 B0 : Ordinal.{0}), B0 ∈ S.CSet B0 (S.psi B0 (Om 1)) → Le.leOe ggE ∣ B0 →
      rkP ggE c0 = S.psi B0 (Om 1) → rkP ggE c0 = p → Bc.bcC S n ≤ S.psi B0 (Om 1) → c0 < y →
      ∃ δ, c0 + 1 + δ = y ∧ δ < x ∧ (∀ σ, σ ≤ δ → c0 + 1 + σ < rkP ggE (c0 + 1 + σ)) ∧
        ∃ B', B' ∈ S.CSet B' (S.psi B' (Om 1)) ∧ Le.leOe ggE ∣ B' ∧
          Bc.bcB S n (S.psi B0 (Om 1)) = S.psi B' (Om 1) ∧
          (∀ c1, rkP ggE c1 = S.psi B' (Om 1) →
            Bc.bcB S n x = rkP ggE (c1 + 1 + Bc.bcB S n δ) ∧
            ∀ σ, σ ≤ Bc.bcB S n δ → c1 + 1 + σ < rkP ggE (c1 + 1 + σ)) ∧
          (∀ r : Term, bcD S r → B0 = bcAlpha S (n + 1) + val S r →
            B' = bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) → True) := by
    intro c0 B0 hown0 hdvd0 hc0 hc0p hlo hcy
    have hnfi := ss_nofix_idx hy hnf hc0p hnofix
    set D := y - c0 with hDdef
    have hcD : c0 + D = y := Ordinal.add_sub_cancel_of_le hcy.le
    have hD0 : D ≠ 0 := by
      rintro h0; rw [h0, add_zero] at hcD; exact absurd hcD hcy.ne
    set δ := D - 1 with hδdef
    have hδ : 1 + δ = D := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hD0)
    have hcδy : c0 + 1 + δ = y := by rw [add_assoc, hδ, hcD]
    have hDx : D < x := (Ordinal.sub_le_self y c0).trans_lt hyx
    have hDL : D < Nc.ncL S ω := hDx.trans hxL
    have hδx : δ < x := (Ordinal.sub_le_self D 1).trans_lt hDx
    have hδL : δ < Nc.ncL S ω := hδx.trans hxL
    have hcondD : ∀ d, d ≤ D → d < rkP ggE (c0 + d) := by
      intro d hd
      rcases eq_or_ne d 0 with rfl | hd0
      · exact (rkP_SC ggE _).1
      have h1 : c0 < c0 + d := lt_add_of_pos_right _ (pos_iff_ne_zero.2 hd0)
      have h2 : c0 + d ≤ y := by rw [← hcD]; exact (add_le_add_iff_left c0).2 hd
      exact le_add_self.trans_lt (hnfi _ h1 h2)
    obtain ⟨hval, hψ⟩ := ssEq hown0 hdvd0 hc0 D (hDx.trans hx1') hcondD
    have hψx : S.psi (B0 + Le.leOe ggE * D) (Om 1) = x := by rw [hψ, hcD, hy]
    have hown1 : B0 + Le.leOe ggE * D ∈ S.CSet (B0 + Le.leOe ggE * D) (S.psi (B0 + Le.leOe ggE * D) (Om 1)) :=
      CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add : B0 ≤ B0 + Le.leOe ggE * D)).2 hown0)
        (ssU_mul_mem (SC_psi Low.InR_Om_one _) hval)
    obtain ⟨r, hDr, hBr, hownB', hB0', hBx⟩ := rkB_psi (n := n) hcE hown0 hlo hown1
      (by rw [hψx]; exact hxX) (hDx.trans hx1') (hDx.trans hxX)
    set B' := bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) with hB'def
    have hdvd' : Le.leOe ggE ∣ B' := ssB_dvd0 hDr hBr hdvd0
    rw [hψx, hBE] at hBx
    have hBDx : Bc.bcB S n D < Bc.bcB S n x := (Bc.bcB_lt_iff hDL hxL).2 hDx
    have hval' : Bc.bcB S n D < S.psi (B' + Le.leOe ggE * Bc.bcB S n D) (Om 1) := by
      rw [← hBx]; exact hBDx
    have hBD : Bc.bcB S n D = 1 + Bc.bcB S n δ := by rw [← hδ, Bc.bcB_add h1L hδL, mwB_one]
    refine ⟨δ, hcδy, hδx, fun σ hσ => ?_, B', hownB', hdvd', hB0', fun c1 hc1 => ?_, fun _ _ _ _ => trivial⟩
    · refine hnfi _ ((lt_add_one c0).trans_le le_self_add) ?_
      rw [← hcδy]; exact (add_le_add_iff_left _).2 hσ
    · have hcondD' := rk_valid le_rfl hdvd' hc1 hval'
      have hBxF : Bc.bcB S n x = rkP ggE (c1 + Bc.bcB S n D) := by
        rw [hBx]; exact (ssEq hownB' hdvd' hc1 _ (hBDx.trans hBx1) hcondD').2
      refine ⟨by rw [hBxF, hBD, add_assoc], fun σ hσ => ?_⟩
      have h1 := hcondD' (1 + σ) (by rw [hBD]; exact (add_le_add_iff_left 1).2 hσ)
      have h2 : c1 < rkP ggE (c1 + (1 + σ)) :=
        (rkP_le_self ggE c1).trans_lt
          ((rkP_lt_iff ggE).2 (lt_add_of_pos_right _ (lt_of_lt_of_le zero_lt_one le_self_add)))
      rw [add_assoc]
      exact (lq_SC_indec (rkP_SC ggE _)).add_lt h2 h1
  rcases hbase with hpt | ⟨htp', hpp⟩
  · -- `p = t`: `x = Φ_{E₁}(c + 1 + δ) = ϑᵗ(E₁ + δ)`
    have hcy : c < y := (rkP_lt_iff ggE).1 (by rw [hct, hy]; exact htx)
    obtain ⟨δ, hcδy, hδx, hcond, B', hownB', hdvd', hBt', himg, -⟩ :=
      common c At hownA hdvdA (hct.trans hpvA.symm) (by rw [hct, hpt]) (by rw [hpvA]; exact hc) hcy
    rw [hpvA] at hBt'
    obtain ⟨hBxF, hcond'⟩ := himg c' (hct'.trans hBt')
    have hδT : δ ∈ Tset t := hTm _ (hδx.trans hx2)
    have hδ1 : δ < Om1 := (hδx.trans hx2).trans hu1
    have hvx : vt t (ggE + δ) = x := by rw [ssK_enum htSC ht1 ht.2 hct δ hδT hδ1 hcond, hcδy, hy]
    have hηδ : η = δ := ssK_inj htSC ht1 hη hηΩ hδT hδ1 (by rw [hvx])
    have hδL : δ < Nc.ncL S ω := hδx.trans hxL
    have hBδx : Bc.bcB S n δ < Bc.bcB S n x := (Bc.bcB_lt_iff hδL hxL).2 hδx
    have hBδT : Bc.bcB S n δ ∈ Tset (Bc.bcB S n t) := hTm' _ (hBδx.trans hhi')
    have hBδ1 : Bc.bcB S n δ < Om1 := (hBδx.trans hhi').trans hu1'
    rw [hηδ, ssK_enum ht'SC ht'1 ht'.2 hct' _ hBδT hBδ1 hcond', hBxF]
  · -- `p > t` a fixed point of `Φ_{E₁}`: `x = Φ_{E₁}(p + 1 + δ) = ϑᵗ(E₁ + (p + δ))`
    have hpSC : SC p := hpp ▸ rkP_SC ggE p
    have hpW : p < S.psi (bcAlphaW S) (Om 1) := by rw [← Bc.ncL_omega_eq S]; exact hpL
    obtain ⟨Bp, hownp, hBp⟩ := rb_own_of_SC hpSC hpW
    have hdvd2p : Le.leOe (ggE + 1) ∣ Bp := ssConv hownp (by rw [hBp]; exact hpp)
    have hdvd1p : Le.leOe ggE ∣ Bp := (rhU_dvd le_self_add).trans hdvd2p
    have hpy : p < y := (rkP_lt_iff ggE).1 (by rw [hpp, hy]; exact hpx)
    obtain ⟨δ, hpδy, hδx, hcond, B', hownB', hdvd', hBp', himg, -⟩ :=
      common p Bp hownp hdvd1p (hpp.trans hBp.symm) hpp (by rw [hBp]; exact hc.trans htp'.le) hpy
    -- `u_{E₁+1} ∣ B'`: redo the image of `B_p` with its term
    have hDp : MvD S p := mvD_of_lt hpL
    have hpX : p < Bc.bcC S (n + 1) := hpx.trans hxX
    obtain ⟨r, hDr, hBr, hownB'', hBp'', -⟩ := rkB_psi (n := n) (D := 0) hcE hownp
      (by rw [hBp]; exact hc.trans htp'.le) (by rw [mul_zero, add_zero]; exact hownp)
      (by rw [mul_zero, add_zero, hBp]; exact hpX) (lt_of_le_of_lt zero_le (by rw [← hO1]; exact hu1))
      (lt_of_le_of_lt zero_le huc)
    have hdvd2' := ssB_dvd1 hDr hBr hdvd2p
    set B'' := bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) with hB''def
    have hB''0 : B'' ≠ 0 := by
      rw [hB''def]
      exact (lt_of_lt_of_le (lt_of_le_of_lt zero_le (Bc.bcAlpha_lt_W S 0)) le_self_add).ne'
    have hpp'' : rkP ggE (S.psi B'' (Om 1)) = S.psi B'' (Om 1) := ssFwd hownB'' hdvd2' hB''0
    rw [hBp] at hBp' hBp''
    have heq : S.psi B' (Om 1) = S.psi B'' (Om 1) := hBp'.symm.trans hBp''
    set p' := Bc.bcB S n p with hp'def
    have hpp' : rkP ggE p' = p' := by rw [hBp'']; exact hpp''
    obtain ⟨hBxF, hcond'⟩ := himg p' (by rw [hpp', hBp'])
    have ht'p' : Bc.bcB S n t < p' := (Bc.bcB_lt_iff htL hpL).2 htp'
    have hδL : δ < Nc.ncL S ω := hδx.trans hxL
    have hpδx : p + δ < x := by
      refine lt_of_le_of_lt ?_ hyx
      rw [← hpδy, add_assoc]; exact (add_le_add_iff_left p).2 le_add_self
    have hpδT : p + δ ∈ Tset t := hTm _ (hpδx.trans hx2)
    have hpδ1 : p + δ < Om1 := (hpδx.trans hx2).trans hu1
    have hvx : vt t (ggE + (p + δ)) = x := by
      rw [ssK_enum_fix2 htSC ht1 ht.2 hpp htp' δ hpδT hpδ1 hcond, hpδy, hy]
    have hηδ : η = p + δ := ssK_inj htSC ht1 hη hηΩ hpδT hpδ1 (by rw [hvx])
    have hBpδ : Bc.bcB S n (p + δ) = p' + Bc.bcB S n δ := Bc.bcB_add hpL hδL
    have hpδx' : p' + Bc.bcB S n δ < Bc.bcB S n x := by
      rw [← hBpδ]; exact (Bc.bcB_lt_iff (hpδx.trans hxL) hxL).2 hpδx
    have hpδT' : p' + Bc.bcB S n δ ∈ Tset (Bc.bcB S n t) := hTm' _ (hpδx'.trans hhi')
    have hpδ1' : p' + Bc.bcB S n δ < Om1 := (hpδx'.trans hhi').trans hu1'
    rw [hηδ, hBpδ, ssK_enum_fix2 ht'SC ht'1 ht'.2 hpp' ht'p' _ hpδT' hpδ1' hcond', hBxF]

/-! ## The window of a base and the first case of `Sp.SpVtTopAll` -/

/-- **The window of an `ε`-number `β ∈ [c_n, c_{n+1})`**: `Tᵝ ∩ Ω₁ = u` and `T^{B_n β} ∩ Ω₁ = B_n u` for some
`u < c_{n+1}` (`u = υ_{ξ+1}` for `β = υ_ξ` by `Sm.smPrem`, and the window of `Sp.spWin` otherwise). -/
theorem ssWin {n : ℕ} {β : Ordinal.{0}} (hβE : InE β) (hc : Bc.bcC S n ≤ β) (hβc : β < Bc.bcC S (n + 1)) :
    ∃ u, u < Bc.bcC S (n + 1) ∧ (∀ a, a < Om1 → (a ∈ Tset β ↔ a < u)) ∧
      (∀ a, a < Om1 → (a ∈ Tset (Bc.bcB S n β) ↔ a < Bc.bcB S n u)) := by
  by_cases hU : UpsPt β
  · obtain ⟨ι, hι0, rfl⟩ := upsPt_iff_upsilon.1 hU
    obtain ⟨hι0', hι1c, ι', hB0, hB1⟩ := Sm.smPrem hc hβc
    have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
    have hu1 : upsilon (ι + 1) < Om1 := (Rt.rt_lt_Om1 hι1c).1
    have hu1' : upsilon (ι' + 1) < Om1 := by rw [← hB1]; exact (Rt.rt_lt_Om1 hι1c).2
    have hLω : Nc.ncL S ω ≤ Bc.bcB S n (upsilon ι) := by
      have e : Bc.bcB S n (Bc.bcC S n) = Nc.ncL S ω := Bc.bcB_base (S := S) n
      rw [← e]; exact Ri.riB_mono (hβc.trans hLw) hc
    have hι'0 : ι' ≠ 0 := by
      rintro rfl
      rw [hB0, upsilon_zero] at hLω
      exact absurd (lt_of_lt_of_le (Lw.lw_L_SC S ω).1 hLω) (lt_irrefl _)
    refine ⟨upsilon (ι + 1), hι1c, fun a ha => ?_, fun a ha => ?_⟩
    · have h := upsilon_succ_T ι (by rw [succ_eq_add_one]; exact hu1) a ha
      rw [if_neg hι0'] at h
      rw [h, succ_eq_add_one]
    · have h := upsilon_succ_T ι' (by rw [succ_eq_add_one]; exact hu1') a ha
      rw [if_neg hι'0] at h
      rw [hB0, h, succ_eq_add_one, hB1]
  · obtain ⟨z, z', -, -, -, hz1c, -, hB1, hTw, hTw'⟩ := spWin hβE hc hβc hU
    exact ⟨upsilon (z + 1), hz1c, hTw, by rw [hB1]; exact hTw'⟩

/-- **`B_n(ϑ^β(E₁ + e)) = ϑ^{B_n β}(E₁ + B_n e)`** for every level-closed `β < c_{n+1}` and `e ∈ Tᵝ ∩ Ω₁`
(no hypothesis): `ssVt_core` with the window `ssWin` for `β ≥ c_n`; below `c_n`, `B_n` fixes everything. -/
theorem ssVtE1 {n : ℕ} {β e : Ordinal.{0}} (hβ : SpLC β) (hβc : β < Bc.bcC S (n + 1)) (he : e ∈ Tset β)
    (he1 : e < Om1) : Bc.bcB S n (vt β (ggE + e)) = vt (Bc.bcB S n β) (ggE + Bc.bcB S n e) := by
  have hβE : InE β := gg_SC_eps hβ.1
  have hβ1 : β < Om1 := (Rt.rt_lt_Om1 hβc).1
  obtain ⟨-, -, hxT, hβx, hx1, -, hex⟩ := ssK_facts hβ.1 hβ1 he he1
  rcases le_or_gt (Bc.bcC S n) β with hc | hc
  · obtain ⟨u, huc, hTw, hTw'⟩ := ssWin hβE hc hβc
    have hu1 : u < Om1 := (Rt.rt_lt_Om1 huc).1
    have hu1' : Bc.bcB S n u < Om1 := (Rt.rt_lt_Om1 huc).2
    exact ssVt_core hc hβc ((hTw _ hx1).1 hxT) huc (fun a ha => (hTw a (ha.trans hu1)).2 ha)
      (fun a ha => (hTw' a (ha.trans hu1')).2 ha) hβ (spLC_img hβ hc hβc) he he1
  · obtain ⟨m, -, -, hmin, hTm, -⟩ := T_next (Or.inr hβE) hβ1
    have hmc : m ≤ Bc.bcC S n := hmin _ hc (Rt.rt_c_inf n)
    have hxc : vt β (ggE + e) < Bc.bcC S n := ((hTm _ hx1).1 hxT).trans_le hmc
    rw [Bc.bcB_fix' S n _ hxc, Bc.bcB_fix' S n _ hc, Bc.bcB_fix' S n _ (hex.trans hxc)]

/-- **`Sm.SmVtTop` on the arguments `[E₁, E₁ + Ω₁)`** at every level-closed base `β < c_{n+1}`, with no hypothesis. -/
theorem ssVtTopE1 {n : ℕ} {β : Ordinal.{0}} (hβ : SpLC β) (hβc : β < Bc.bcC S (n + 1)) :
    ∀ η ∈ Tset β, ggE ≤ η → η < ggE + Om1 →
      Bc.bcB S n (vt β η) = vt (Bc.bcB S n β) (Bc.bcB S n η) := by
  intro η hη hEη hη1
  have hβE : InE β := gg_SC_eps hβ.1
  have hβ1 : β < Om1 := (Rt.rt_lt_Om1 hβc).1
  set e := η - ggE with hedef
  have hηe : ggE + e = η := Ordinal.add_sub_cancel_of_le hEη
  have he1 : e < Om1 := by rw [← hηe] at hη1; exact (add_lt_add_iff_left _).1 hη1
  have heT : e ∈ Tset β := vzRem_T hβE hβ1 hη (by rw [← hηe] at hη ⊢; exact ss_arg_lt he1) hηe.symm
    ⟨ggE, ss_Om1_mul_E.symm⟩ he1
  obtain ⟨-, -, hxT, -, hx1, -, hex⟩ := ssK_facts hβ.1 hβ1 heT he1
  have hxc : vt β (ggE + e) < Bc.bcC S (n + 1) := Si.si_T_lt_c hβE hβc hxT hx1
  have heL : e < Nc.ncL S ω := (hex.trans hxc).trans (Bc.bcC_lt S (n + 1))
  rw [← hηe, (ssB_arg (n := n) heL).2]
  exact ssVtE1 hβ hβc heT he1

/-- **`B_n` commutes with `ϑ^β` on the arguments `[E₁ + Ω₁, Ω₂)` at every level-closed base `β < c_{n+1}`** (a
hypothesis name: what is left of `Sp.SpVtTopAll`). -/
def SsVtTopHi (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ β, SpLC β → β < Bc.bcC S (n + 1) → ∀ η ∈ Tset β, ggE + Om1 ≤ η → η < OmTwo →
    Bc.bcB S n (vt β η) = vt (Bc.bcB S n β) (Bc.bcB S n η)

/-- **`Sp.SpVtTopAll S ↔ SsVtTopHi S`**: the arguments `[E₁, E₁ + Ω₁)` are `ssVtTopE1`. -/
theorem ssVtTopAll_iff : SpVtTopAll S ↔ SsVtTopHi S := by
  constructor
  · intro h n β hβ hβc η hη hη1 hη2
    exact h n β hβ hβc η hη ((le_self_add).trans hη1) hη2
  · intro h n β hβ hβc η hη hEη hη2
    rcases lt_or_ge η (ggE + Om1) with hlo | hhi
    · exact ssVtTopE1 hβ hβc η hη hEη hlo
    · exact h n β hβ hβc η hη hhi hη2

end Googology.Trans.PoR.InaccPsi.R2.Ss
