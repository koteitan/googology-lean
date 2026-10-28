import Googology.Trans.PoR.InaccPsi.R2.VjB

/-!
# `B_n` moves `ϑ^β(Δ_μ + η)` at EVERY level `μ < θ` and every level-closed base `β`, with no hypothesis

`B_n = Bc.bcB S n`, `c_n = L(n+1) = Bc.bcC S n`, `ϑ^β = vt β`, `Δ_μ = Ω₁·(Ω₁ + μ)`, `Φ_μ = Ul.ulH S 0 μ`,
`d = Ul.ulD S 0`, `δ_μ = Vd.vdDat S (Ω₁ + μ)`, `μ' = B_n μ`, `θ = ConjT.th S`, `SpLC` the level-closed ordinals.  The
proof of `Uf.ufVt_core` / `Uf.ufVtE` with the ϑ-side of `R2.VjTh` (every level below `θ`, from `R2.CitedVd`) and the
`ψ_{Ω₁}`-side of `R2.VjB`; the data are compared only at strongly critical points, the base point of the first value
is `max(t, uiDat μ)` (`uiDat` moves with `B_n`, `Uo.uoDat_B`):

* `vj_dat_iff` (`d(z) < v ↔ uiDat z < v` at a strongly critical `v ≤ Ω₁`, `z` of the notation), `vj_B_not`,
  `vj_OmW_le_of_psi`;
* `vjVt_core` (**the move over a level-closed `t ∈ [c_n, c_{n+1})` with a window**), `vjVtE` (**`B_n(ϑ^β(Δ_μ + η)) =
  ϑ^{B_n β}(Δ_{μ'} + B_n η)` for every level-closed `β < c_{n+1}`, every `μ < θ` with `δ_μ ∈ Tᵝ`, `η ∈ Tᵝ ∩ Ω₁`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Rh
  Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rb Googology.Trans.PoR.InaccPsi.R2.Gg

variable {S : InaccSeq.{0}}

/-- `d(z) < v ↔ uiDat z < v` at a strongly critical `v ≤ Ω₁` for `z` of the notation. -/
theorem vj_dat_iff {z v : Ordinal.{0}} (hz : z ∈ ⋃ a, S.CSet a 0) (hv : SC v) (hv1 : v ≤ Om 1) :
    ulD S 0 z < v ↔ Ui.uiDat S z < v := by
  rw [← Vd.vd_dat_ui hz hv hv1, Vd.vdD_eq]

theorem vj_B_not {n : ℕ} (x : Ordinal.{0}) : Bc.bcB S n x ∈ ⋃ a, S.CSet a 0 := by
  unfold Bc.bcB; exact mem_iUnion.2 (Term.exists_mem_CSet S _)

/-- **`ψ_{Ω₁}(α_ω) ≤ ψ_{Ω₁}(K)` gives `K ≥ Ω_ω`.** -/
theorem vj_OmW_le_of_psi {K : Ordinal.{0}} (h : S.psi (bcAlphaW S) (Om 1) ≤ S.psi K (Om 1)) : Om ω ≤ K := by
  by_contra hK
  push Not at hK
  have h1 : S.psi K (Om 1) ≤ S.psi (Om ω) (Om 1) := (psi_mono Low.InR_Om_one hK.le).1
  have hlt : (Om ω : Ordinal.{0}) < bcAlphaW S := by
    unfold bcAlphaW
    exact (lt_add_of_pos_right _ (SC_Om omega0_ne_zero).1).trans_le le_self_add
  have h2 : S.psi (Om ω) (Om 1) < S.psi (bcAlphaW S) (Om 1) :=
    psi_lt_psi_of_mem Low.InR_Om_one hlt (ConjT.OmW_mem S _ _)
  exact absurd h (not_le.2 (h1.trans_lt h2))

/-- A strongly critical value `w ≤ Ω₁` above `uiDat z` is above `d(z)`, and `w ≤ uiDat z` gives `w ≤ d(z)`. -/
theorem vj_le_dat {z w : Ordinal.{0}} (hz : z ∈ ⋃ a, S.CSet a 0) (hw : SC w) (hw1 : w ≤ Om 1)
    (h : w ≤ Ui.uiDat S z) : w ≤ ulD S 0 z :=
  not_lt.1 fun hlt => absurd ((vj_dat_iff hz hw hw1).1 hlt) (not_lt.2 h)

/-- **The move at every level `μ < θ` over a level-closed base `t ∈ [c_n, c_{n+1})` with a window `u`.** -/
theorem vjVt_core {n : ℕ} {μ t u η : Ordinal.{0}}
    (hc : Bc.bcC S n ≤ t) (htc : t < Bc.bcC S (n + 1))
    (hx2 : vt t (Om1 * (Om1 + μ) + η) < u) (huc : u < Bc.bcC S (n + 1)) (hTm : ∀ a, a < u → a ∈ Tset t)
    (hTm' : ∀ a, a < Bc.bcB S n u → a ∈ Tset (Bc.bcB S n t))
    (ht : Sp.SpLC t) (ht' : Sp.SpLC (Bc.bcB S n t)) (hμθ : μ < ConjT.th S)
    (hμT : Vd.vdDat S (Om1 + μ) ∈ Tset t) (hη : η ∈ Tset t) (hηΩ : η < Om1) :
    Bc.bcB S n (vt t (Om1 * (Om1 + μ) + η)) =
      vt (Bc.bcB S n t) (Om1 * (Om1 + Bc.bcB S n μ) + Bc.bcB S n η) := by
  set x := vt t (Om1 * (Om1 + μ) + η) with hxdef
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
  have huL : u < Nc.ncL S ω := huc.trans hLw
  have hhi' : Bc.bcB S n x < Bc.bcB S n u := (Bc.bcB_lt_iff hxL huL).2 hx2
  have hcS : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω := Ri.ri_one_lt_L S
  have hO1 : (Om1 : Ordinal.{0}) = Om 1 := Rj.rj_Om1
  obtain ⟨-, -, hxT, htx, hx1, -, hdx, hηx⟩ := vjK_facts htSC ht1 hμθ hμT hη hηΩ
  rw [← hxdef] at hxT htx hx1 hdx hηx
  have hxSC : SC x := vjK_SC htSC ht1 hμθ hμT hη hηΩ
  have hdc : ulD S 0 μ < Bc.bcC S (n + 1) := hdx.trans hxX
  obtain ⟨hμN, huic, -⟩ := vjD_lev hcS hLw.le hdc
  obtain ⟨hDμ, hμ'θ, -⟩ := vj_B_lvl hμθ hdc
  have hμ'N : Bc.bcB S n μ ∈ ⋃ a, S.CSet a 0 := vj_B_not μ
  have hBxSC : SC (Bc.bcB S n x) := (Mx.mxB_SC_iff hxL).2 hxSC
  have hBx1 : Bc.bcB S n x < Om1 := hhi'.trans hu1'
  have hd'x : ulD S 0 (Bc.bcB S n μ) < Bc.bcB S n x := (vj_datB hDμ hxSC hxX).2 hdx
  have hμ'T : Vd.vdDat S (Om1 + Bc.bcB S n μ) ∈ Tset (Bc.bcB S n t) :=
    hTm' _ (((vj_datv hBxSC hBx1.le).2 hd'x).trans hhi')
  have hηL : η < Nc.ncL S ω := hηx.trans hxL
  have hBηx : Bc.bcB S n η < Bc.bcB S n x := (Bc.bcB_lt_iff hηL hxL).2 hηx
  have hBηT : Bc.bcB S n η ∈ Tset (Bc.bcB S n t) := hTm' _ (hBηx.trans hhi')
  have hBη1 : Bc.bcB S n η < Om1 := (hBηx.trans hhi').trans hu1'
  -- `x = Φ_μ(y)`, not a fixed point of `Φ_μ`
  obtain ⟨y, hy⟩ := vjK_range htSC ht1 hμθ hμT hη hηΩ
  rw [← hxdef] at hy
  have hnf : ulH S 0 μ x ≠ x := by
    intro hfx
    have hLE := vjK_le htSC ht1 μ hμθ hμT η hη hηΩ
    have h3 : t + η + 1 < x := hxSC.add_one_lt ((Lq.lq_SC_indec hxSC).add_lt htx hηx)
    have h4 : ulH S 0 μ (t + η + 1) < x := by
      conv_rhs => rw [← hfx]
      exact (ulH_lt_iff μ).2 h3
    exact absurd hLE (not_le.2 h4)
  have hyx : y < x := by
    refine lt_of_le_of_ne (hy ▸ ulH_le_self μ y) fun e => hnf ?_
    rw [← e] at hy ⊢; rw [hy]
  have huix : Ui.uiDat S μ < x := (vj_dat_iff hμN hxSC (hO1 ▸ hx1.le)).1 hdx
  set m0 := max t (Ui.uiDat S μ) with hm0
  have hm0x : m0 < x := max_lt htx huix
  have hm0L : m0 < Nc.ncL S ω := hm0x.trans hxL
  have huiL : Ui.uiDat S μ < Nc.ncL S ω := huix.trans hxL
  -- the data at strongly critical points above `m0`
  have hdmv : ∀ v, SC v → v ≤ Om 1 → m0 < v → ulD S 0 μ < v := fun v hv hv1 hmv =>
    (vj_dat_iff hμN hv hv1).2 ((le_max_right _ _).trans_lt hmv)
  have hminc : ∀ w, SC w → w ≤ Om 1 → w ≤ m0 → w ≤ t ∨ w ≤ ulD S 0 μ := fun w hw hw1 h => by
    rcases le_max_iff.1 h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (vj_le_dat hμN hw hw1 h')
  obtain ⟨p, hbase, hpx, hmax⟩ := rh_base_below (ulH_normal μ) hm0x hnf
  have hnofix : ∀ z, p < z → z < x → z < ulH S 0 μ z := by
    intro z hpz hzx
    by_contra h
    push Not at h
    have hz := le_antisymm h (ulH_le_self μ z)
    have hm0z : m0 < z := by
      rcases hbase with e | ⟨h', -⟩
      · rw [← e]; exact hpz
      · exact h'.trans hpz
    exact absurd (hmax z hz hm0z hzx) (not_le.2 hpz)
  have hxO : x ≤ Om 1 := hO1 ▸ hx1.le
  rcases hbase with hpm | ⟨hm0p, hpp⟩
  · -- no fixed point of `Φ_μ` in `(m0, x)`: the first value `ψ_{Ω₁}(K + u_μ)` above `m0`
    obtain ⟨K, hownK, htK, hKm, hmK⟩ := Ti.ti_K_of (S := S) htSC (le_max_left _ _) hm0L
    have hKW : Om ω ≤ K := vj_OmW_le_of_lo (hc.trans htK)
    obtain ⟨-, hmE, -, hownE⟩ := vj_leastP (S := S) hμθ hownK hKW hKm hmK hdmv
    obtain ⟨c0, hc0, hmin⟩ := vj_firstP (S := S) hμθ hownK hKW hKm hmK hdmv
    have hc0y : c0 ≤ y := by
      refine not_lt.1 fun hlt => ?_
      have := hmin y hlt
      rw [hy] at this
      exact absurd hm0x (not_lt.2 this)
    set Ds := y - c0 with hDsdef
    have hcD : c0 + Ds = y := Ordinal.add_sub_cancel_of_le hc0y
    have hnf0 : ∀ σ, σ ≤ Ds → c0 + σ < ulH S 0 μ (c0 + σ) := by
      intro σ hσ
      have hzy : c0 + σ ≤ y := by rw [← hcD]; exact (add_le_add_iff_left c0).2 hσ
      refine lt_of_le_of_ne (ulH_le_self μ _) fun hz => ?_
      have hpz : p < c0 + σ := by
        rw [hpm]
        calc m0 < S.psi (K + Le.leOe μ) (Om 1) := hmE
          _ = ulH S 0 μ c0 := hc0.symm
          _ ≤ ulH S 0 μ (c0 + σ) := (ulH_le_iff μ).2 le_self_add
          _ = c0 + σ := hz.symm
      have := hnofix _ hpz (hzy.trans_lt hyx)
      rw [← hz] at this; exact lt_irrefl _ this
    have hDsx : Ds < x := (Ordinal.sub_le_self y c0).trans_lt hyx
    have hDsT : Ds ∈ Tset t := hTm _ (hDsx.trans hx2)
    have hDs1 : Ds < Om1 := (hDsx.trans hx2).trans hu1
    have hc0x : ulH S 0 μ c0 ≤ x := by rw [← hy, ← hcD]; exact (ulH_le_iff μ).2 le_self_add
    have hc0τ : t < ulH S 0 μ c0 := (le_max_left _ _).trans_lt (by rw [hc0]; exact hmE)
    have hc0d : ulD S 0 μ < ulH S 0 μ c0 :=
      hdmv _ (ulH_SC μ c0) (hc0x.trans hxO) (by rw [hc0]; exact hmE)
    have hmin' : ∀ c < c0, ulH S 0 μ c ≤ t ∨ ulH S 0 μ c ≤ ulD S 0 μ := fun c hc =>
      hminc _ (ulH_SC μ c) (((ulH_le_iff μ).2 hc.le).trans (hc0x.trans hxO)) (hmin c hc)
    have hvx : vt t (Om1 * (Om1 + μ) + Ds) = x := by
      rw [vjK_enum0 htSC ht1 hμθ hμT hc0τ hc0d hmin' Ds hDsT hDs1
        (fun σ hσ => le_add_self.trans_lt (hnf0 σ hσ)), hcD, hy]
    have hηD : η = Ds := vjK_inj htSC ht1 hμθ hμT hη hηΩ hDsT hDs1 (by rw [hvx])
    -- the move of the first value
    have hlo : Bc.bcC S n ≤ S.psi K (Om 1) := hc.trans htK
    have hEX : S.psi (K + Le.leOe μ) (Om 1) < Bc.bcC S (n + 1) := by rw [← hc0]; exact hc0x.trans_lt hxX
    obtain ⟨K', hownK', hBK, hBK1, hBKu⟩ := vj_B_least hDμ hownK hlo hownE hEX
    have hKL : S.psi K (Om 1) < Nc.ncL S ω := hKm.trans_lt hm0L
    have hK1L : S.psi (K + 1) (Om 1) < Nc.ncL S ω :=
      ((psi_mono (S := S) Low.InR_Om_one (add_le_add_right (one_le_iff_ne_zero.2 (rhU_ne μ)) K)).1).trans_lt
        (hEX.trans hLw)
    set m0' := max (Bc.bcB S n t) (Ui.uiDat S (Bc.bcB S n μ)) with hm0'
    have hBm0 : Bc.bcB S n m0 = m0' := by
      rw [hm0', (Uo.uoDat_B (n := n) hDμ).2, hm0, Ti.ti_B_max htL huiL]
    have hK'm : S.psi K' (Om 1) ≤ m0' := by rw [← hBK, ← hBm0]; exact Ri.riB_mono hm0L hKm
    have hmK' : m0' < S.psi (K' + 1) (Om 1) := by
      rw [← hBK1, ← hBm0]; exact (Bc.bcB_lt_iff hm0L hK1L).2 hmK
    have hdm' : ∀ v, SC v → v ≤ Om 1 → m0' < v → ulD S 0 (Bc.bcB S n μ) < v := fun v hv hv1 hmv =>
      (vj_dat_iff hμ'N hv hv1).2 ((le_max_right _ _).trans_lt hmv)
    have hK'W : Om ω ≤ K' := vj_OmW_le_of_psi (by
      rw [← hBK, ← Bc.ncL_omega_eq S, ← Bc.bcB_base n]; exact Ri.riB_mono hKL hlo)
    obtain ⟨-, hmE', -, -⟩ := vj_leastP (S := S) hμ'θ hownK' hK'W hK'm hmK' hdm'
    obtain ⟨c0', hc0', hmin'0⟩ := vj_firstP (S := S) hμ'θ hownK' hK'W hK'm hmK' hdm'
    have hBc0x : ulH S 0 (Bc.bcB S n μ) c0' ≤ Om 1 := by
      rw [hc0', ← hBKu]
      exact (Ri.riB_mono hxL (by rw [← hc0]; exact hc0x)).trans (hO1 ▸ hBx1.le)
    have hc0τ' : Bc.bcB S n t < ulH S 0 (Bc.bcB S n μ) c0' :=
      (le_max_left _ _).trans_lt (by rw [hc0']; exact hmE')
    have hc0d' : ulD S 0 (Bc.bcB S n μ) < ulH S 0 (Bc.bcB S n μ) c0' :=
      hdm' _ (ulH_SC _ _) hBc0x (by rw [hc0']; exact hmE')
    have hmin'' : ∀ c < c0', ulH S 0 (Bc.bcB S n μ) c ≤ Bc.bcB S n t ∨
        ulH S 0 (Bc.bcB S n μ) c ≤ ulD S 0 (Bc.bcB S n μ) := fun c hc => by
      rcases le_max_iff.1 (hmin'0 c hc) with h' | h'
      · exact Or.inl h'
      · exact Or.inr (vj_le_dat hμ'N (ulH_SC _ _) (((ulH_le_iff _).2 hc.le).trans hBc0x) h')
    rcases eq_or_ne Ds 0 with hD0 | hD0
    · -- `x` is the first value itself
      have hx0 : x = S.psi (K + Le.leOe μ) (Om 1) := by rw [← hy, ← hcD, hD0, add_zero, hc0]
      have h0 := vjK_enum0 ht'SC ht'1 hμ'θ hμ'T hc0τ' hc0d' hmin'' 0
        (mem_T_of_le (gg_SC_eps ht'SC) ht'1 zero_le) (lt_of_le_of_lt zero_le ht'1)
        (fun σ hσ => by rw [nonpos_iff_eq_zero.1 hσ]; exact (ulH_SC _ _).1)
      rw [add_zero, add_zero] at h0
      rw [hηD, hD0, Bc.bcB_zero, add_zero, h0, hc0', hx0, hBKu]
    · set δ := Ds - 1 with hδdef
      have hδ : 1 + δ = Ds := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hD0)
      have hcδ : c0 + 1 + δ = y := by rw [add_assoc, hδ, hcD]
      have hcond : ∀ σ, σ ≤ δ → c0 + 1 + σ < ulH S 0 μ (c0 + 1 + σ) := by
        intro σ hσ
        have := hnf0 (1 + σ) (by rw [← hδ]; exact (add_le_add_iff_left 1).2 hσ)
        rwa [← add_assoc] at this
      obtain ⟨B', -, -, hB0', himg⟩ := vj_B_run hμθ hdc hownE (rh_dvd_add_self μ K) hc0
        (hlo.trans (psi_mono (S := S) Low.InR_Om_one le_self_add).1)
        (by rw [← hc0]; exact hc0d) (by rw [hcδ, hy]; exact hxX) hcond
      have hc1 : ulH S 0 (Bc.bcB S n μ) c0' = S.psi B' (Om 1) := by rw [hc0', ← hBKu, hB0']
      obtain ⟨hBxF, hcond'⟩ := himg c0' hc1
      rw [hcδ, hy] at hBxF
      have hδL : δ < Nc.ncL S ω := ((Ordinal.sub_le_self Ds 1).trans_lt hDsx).trans hxL
      have hBη : Bc.bcB S n η = 1 + Bc.bcB S n δ := by
        rw [hηD, ← hδ, Bc.bcB_add h1L hδL, Mw.mwB_one]
      have hval' : ∀ σ, σ ≤ 1 + Bc.bcB S n δ → σ < ulH S 0 (Bc.bcB S n μ) (c0' + σ) := by
        intro σ hσ
        rcases eq_or_ne σ 0 with rfl | hσ0
        · exact (ulH_SC _ _).1
        have he : 1 + (σ - 1) = σ := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hσ0)
        have hσ' : σ - 1 ≤ Bc.bcB S n δ := by rw [← he] at hσ; exact (add_le_add_iff_left 1).1 hσ
        have := hcond' _ hσ'
        rw [add_assoc, he] at this
        exact le_add_self.trans_lt this
      rw [hBxF, vjK_enum0 ht'SC ht'1 hμ'θ hμ'T hc0τ' hc0d' hmin'' _ hBηT hBη1
        (by rw [hBη]; exact hval'), hBη, add_assoc]
  · -- `p > m0` a fixed point of `Φ_μ`: `x = Φ_μ(p + 1 + δ) = ϑᵗ(Δ_μ + (p + δ))`
    have htp : t < p := (le_max_left _ _).trans_lt hm0p
    have hdp : ulD S 0 μ < p := vj_datL_lt_fix hpp
    have hpSC : SC p := hpp ▸ ulH_SC μ p
    have hpL : p < Nc.ncL S ω := hpx.trans hxL
    have hpX : p < Bc.bcC S (n + 1) := hpx.trans hxX
    have hpW : p < S.psi (bcAlphaW S) (Om 1) := by rw [← Bc.ncL_omega_eq S]; exact hpL
    obtain ⟨Bp, hownp, hBp⟩ := rb_own_of_SC hpSC hpW
    have hdvd2p : Le.leOe (μ + 1) ∣ Bp := vj_conv hownp (by rw [hBp]; exact hpp)
    have hdvd1p : Le.leOe μ ∣ Bp := (rhU_dvd le_self_add).trans hdvd2p
    have hpy : p < y := (ulH_lt_iff μ).1 (by rw [hpp, hy]; exact hpx)
    set D := y - p with hDdef
    have hpD : p + D = y := Ordinal.add_sub_cancel_of_le hpy.le
    have hD0 : D ≠ 0 := by
      rintro h0; rw [h0, add_zero] at hpD; exact absurd hpD hpy.ne
    set δ := D - 1 with hδdef
    have hδ : 1 + δ = D := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hD0)
    have hpδy : p + 1 + δ = y := by rw [add_assoc, hδ, hpD]
    have hpδx : p + δ < x := by
      refine lt_of_le_of_lt ?_ hyx
      rw [← hpδy, add_assoc]; exact (add_le_add_iff_left p).2 le_add_self
    have hcond : ∀ σ, σ ≤ δ → p + 1 + σ < ulH S 0 μ (p + 1 + σ) := by
      intro σ hσ
      refine hnofix _ (lt_of_lt_of_le (lt_add_one p) le_self_add) (lt_of_le_of_lt ?_ hyx)
      rw [← hpδy]; exact (add_le_add_iff_left _).2 hσ
    have hlo : Bc.bcC S n ≤ S.psi Bp (Om 1) := by rw [hBp]; exact hc.trans htp.le
    obtain ⟨B', -, -, hB0', himg⟩ := vj_B_run hμθ hdc hownp hdvd1p (hpp.trans hBp.symm) hlo
      (by rw [hBp]; exact hdp) (by rw [hpδy, hy]; exact hxX) hcond
    have hpp' : ulH S 0 (Bc.bcB S n μ) (Bc.bcB S n p) = Bc.bcB S n p := by
      have := vj_B_fix hμθ hdc hownp hlo (by rw [hBp]; exact hpX) (by rw [hBp]; exact hpp)
      rwa [hBp] at this
    have hc1 : ulH S 0 (Bc.bcB S n μ) (Bc.bcB S n p) = S.psi B' (Om 1) := by rw [hpp', ← hBp, hB0']
    obtain ⟨hBxF, hcond'⟩ := himg _ hc1
    rw [hpδy, hy] at hBxF
    have hpδT : p + δ ∈ Tset t := hTm _ (hpδx.trans hx2)
    have hpδ1 : p + δ < Om1 := (hpδx.trans hx2).trans hu1
    have hvx : vt t (Om1 * (Om1 + μ) + (p + δ)) = x := by
      rw [vjK_enum_fix2 htSC ht1 hμθ hμT hpp htp δ hpδT hpδ1 hcond, hpδy, hy]
    have hηδ : η = p + δ := vjK_inj htSC ht1 hμθ hμT hη hηΩ hpδT hpδ1 (by rw [hvx])
    have hδL : δ < Nc.ncL S ω := (le_add_self.trans_lt hpδx).trans hxL
    have hBpδ : Bc.bcB S n (p + δ) = Bc.bcB S n p + Bc.bcB S n δ := Bc.bcB_add hpL hδL
    have ht'p' : Bc.bcB S n t < Bc.bcB S n p := (Bc.bcB_lt_iff htL hpL).2 htp
    have hpδx' : Bc.bcB S n p + Bc.bcB S n δ < Bc.bcB S n x := by
      rw [← hBpδ]; exact (Bc.bcB_lt_iff (hpδx.trans hxL) hxL).2 hpδx
    have hpδT' : Bc.bcB S n p + Bc.bcB S n δ ∈ Tset (Bc.bcB S n t) := hTm' _ (hpδx'.trans hhi')
    have hpδ1' : Bc.bcB S n p + Bc.bcB S n δ < Om1 := (hpδx'.trans hhi').trans hu1'
    rw [hηδ, hBpδ, vjK_enum_fix2 ht'SC ht'1 hμ'θ hμ'T hpp' ht'p' _ hpδT' hpδ1' hcond', hBxF]

/-- **`B_n(ϑ^β(Δ_μ + η)) = ϑ^{B_n β}(Δ_{B_n μ} + B_n η)`** for every level-closed `β < c_{n+1}`, every level
`μ < θ` with `δ_μ ∈ Tᵝ`, and `η ∈ Tᵝ ∩ Ω₁`.  No hypothesis. -/
theorem vjVtE {n : ℕ} {β μ η : Ordinal.{0}} (hβ : Sp.SpLC β) (hβc : β < Bc.bcC S (n + 1))
    (hμθ : μ < ConjT.th S) (hμT : Vd.vdDat S (Om1 + μ) ∈ Tset β) (hη : η ∈ Tset β) (hηΩ : η < Om1) :
    Bc.bcB S n (vt β (Om1 * (Om1 + μ) + η)) =
      vt (Bc.bcB S n β) (Om1 * (Om1 + Bc.bcB S n μ) + Bc.bcB S n η) := by
  have hβE : InE β := gg_SC_eps hβ.1
  have hβ1 : β < Om1 := (Rt.rt_lt_Om1 hβc).1
  obtain ⟨-, -, hxT, -, hx1, -, hdx, hηx⟩ := vjK_facts hβ.1 hβ1 hμθ hμT hη hηΩ
  rcases le_or_gt (Bc.bcC S n) β with hc | hc
  · obtain ⟨u, huc, hTw, hTw'⟩ := Ss.ssWin hβE hc hβc
    have hu1 : u < Om1 := (Rt.rt_lt_Om1 huc).1
    have hu1' : Bc.bcB S n u < Om1 := (Rt.rt_lt_Om1 huc).2
    exact vjVt_core hc hβc ((hTw _ hx1).1 hxT) huc (fun a ha => (hTw a (ha.trans hu1)).2 ha)
      (fun a ha => (hTw' a (ha.trans hu1')).2 ha) hβ (Sp.spLC_img hβ hc hβc) hμθ hμT hη hηΩ
  · -- below `c_n`: `B_n` fixes the value, the base, the level and `η`
    obtain ⟨m, -, -, hmin, hTm, -⟩ := T_next (Or.inr hβE) hβ1
    have hmc : m ≤ Bc.bcC S n := hmin _ hc (Rt.rt_c_inf n)
    have hxc : vt β (Om1 * (Om1 + μ) + η) < Bc.bcC S n := ((hTm _ hx1).1 hxT).trans_le hmc
    have hdc : ulD S 0 μ < Bc.bcC S n := hdx.trans hxc
    have hcS : SC (Bc.bcC S n) := Lw.lw_L_SC S _
    obtain ⟨hμN, huic, -⟩ := vjD_lev hcS (Bc.bcC_lt S n).le hdc
    have hBμ : Bc.bcB S n μ = μ := vjB_fix_dat hμN huic
    rw [Bc.bcB_fix' S n _ hxc, Bc.bcB_fix' S n _ hc, Bc.bcB_fix' S n _ (hηx.trans hxc), hBμ]

end Googology.Trans.PoR.InaccPsi.R2.Vj
