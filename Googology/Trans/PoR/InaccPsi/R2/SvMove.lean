import Googology.Trans.PoR.InaccPsi.R2.SvLeast

/-!
# `B_n` moves `ϑ^β(Δ_μ + η)` at every level `E₁ ≤ μ < M` and every level-closed base `β`, under `SvCit M`

`B_n = Bc.bcB S n`, `c_n = L(n+1) = Bc.bcC S n`, `ϑ^β = vt β`, `Δ_μ = Ω₁·(Ω₁ + μ)`, `Φ_μ = Ss.ssP μ`, `μ' = B_n μ`,
`SpLC` the level-closed ordinals.  `R2.SsMove` moves the level `E₁` (`B_n E₁ = E₁`); here every level `E₁ ≤ μ < M` of
the package `SvCit M` (`R2.SvCit`), with `μ' = B_n μ` in general different from `μ`:

* `svVt_core` (**the move**: for a level-closed `t ∈ [c_n, c_{n+1})` with a window `u` (`x = ϑᵗ(Δ_μ + η) < u <
  c_{n+1}`, `[0, u) ⊆ Tᵗ`, `[0, B_n u) ⊆ T^{B_n t}`), `B_n t` level-closed, `ssDatL μ ∈ Tᵗ`, `η ∈ Tᵗ ∩ Ω₁`, `μ' < M`:
  **`B_n x = ϑ^{B_n t}(Δ_{μ'} + B_n η)`**): `x` is a value of `Φ_μ` and not a fixed point (`Sv.svK_range`,
  `Sv.svK_le`); either the largest fixed point `p` of `Φ_μ` in `(max(t, ssDatL μ), x)` exists, `x = Φ_μ(p + 1 + δ)`
  (`Sv.svK_enum_fix2`), or `x = Φ_μ(c₀ + δ)` from the first value `Φ_μ(c₀) = ψ_{Ω₁}(K + u_μ)` above `max(t, ssDatL
  μ)` (`Sv.sv_least`, `Sv.svK_enum0`); `B_n` moves the run (`Sv.sv_B_run`, `Sv.sv_B_fix`, `Sv.sv_B_least`) and the
  target is read back at the base `B_n t`;
* `svVtE` (**`B_n(ϑ^β(Δ_μ + η)) = ϑ^{B_n β}(Δ_{μ'} + B_n η)` for every level-closed `β < c_{n+1}`**, `E₁ ≤ μ < M`
  with `ssDatL μ ∈ Tᵝ`, `η ∈ Tᵝ ∩ Ω₁`, given `μ' < M`: the window `Ss.ssWin`; below `c_n`, `B_n` fixes everything).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Sv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb
  Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Ri
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rk Googology.Trans.PoR.InaccPsi.R2.Ss
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2.Bc
  Googology.Trans.PoR.InaccPsi.R2.Sp

variable {S : InaccSeq.{0}}

/-- `B_n(max a b) = max(B_n a, B_n b)` below `L(ω)`. -/
theorem sv_B_max {n : ℕ} {a b : Ordinal.{0}} (ha : a < Nc.ncL S ω) (hb : b < Nc.ncL S ω) :
    Bc.bcB S n (max a b) = max (Bc.bcB S n a) (Bc.bcB S n b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (Ri.riB_mono hb h)]
  · rw [max_eq_left h, max_eq_left (Ri.riB_mono ha h)]

/-- `E₁ ≤ B_n μ` for `E₁ ≤ μ` in the domain. -/
theorem sv_B_geE {n : ℕ} {μ : Ordinal.{0}} (hD : MvD S μ) (hEμ : ggE ≤ μ) : ggE ≤ Bc.bcB S n μ := by
  obtain ⟨hDE, hBE⟩ := rkB_E (S := S) (n := n)
  rcases hEμ.lt_or_eq with h | h
  · have := (mvB_lt_iff (k := n) hDE hD).2 h
    rw [hBE] at this; exact this.le
  · rw [← h, hBE]

/-- Validity from the absence of fixed points: `σ < Φ(c + σ)` once `c + σ < Φ(c + σ)`. -/
theorem sv_valid_of {μ c D : Ordinal.{0}} (h : ∀ σ, σ ≤ D → c + σ < ssP μ (c + σ)) :
    ∀ σ, σ ≤ D → σ < ssP μ (c + σ) := fun σ hσ => le_add_self.trans_lt (h σ hσ)

/-- Validity at `1 + δ` from the absence of fixed points at the indices `c + 1 + σ`, `σ ≤ δ`. -/
theorem sv_valid_one {μ c δ : Ordinal.{0}} (h : ∀ σ, σ ≤ δ → c + 1 + σ < ssP μ (c + 1 + σ)) :
    ∀ σ, σ ≤ 1 + δ → σ < ssP μ (c + σ) := by
  intro σ hσ
  rcases eq_or_ne σ 0 with rfl | hσ0
  · exact (ssP_SC μ _).1
  have he : 1 + (σ - 1) = σ := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hσ0)
  have hσ' : σ - 1 ≤ δ := by rw [← he] at hσ; exact (add_le_add_iff_left 1).1 hσ
  have := h _ hσ'
  rw [add_assoc, he] at this
  exact le_add_self.trans_lt this

/-- **The move at every level `E₁ ≤ μ < M` over a level-closed base `t ∈ [c_n, c_{n+1})` with a window `u`.** -/
theorem svVt_core {M : Ordinal.{0}} (hC : SvCit M) (hMG : M ≤ ggGam) {n : ℕ} {μ t u η : Ordinal.{0}}
    (hc : Bc.bcC S n ≤ t) (htc : t < Bc.bcC S (n + 1))
    (hx2 : vt t (Om1 * (Om1 + μ) + η) < u) (huc : u < Bc.bcC S (n + 1)) (hTm : ∀ a, a < u → a ∈ Tset t)
    (hTm' : ∀ a, a < Bc.bcB S n u → a ∈ Tset (Bc.bcB S n t))
    (ht : SpLC t) (ht' : SpLC (Bc.bcB S n t)) (hEμ : ggE ≤ μ) (hμM : μ < M) (hμ'M : Bc.bcB S n μ < M)
    (hμT : ssDatL μ ∈ Tset t) (hη : η ∈ Tset t) (hηΩ : η < Om1) :
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
  obtain ⟨-, -, hxT, htx, hx1, -, hdx, hηx⟩ := svK_facts hC hMG htSC ht1 hEμ hμM hμT hη hηΩ
  rw [← hxdef] at hxT htx hx1 hdx hηx
  have hμG : μ < ggGam := hμM.trans_le hMG
  have hμC : GgCl (Bc.bcC S (n + 1)) μ := ss_code_lvl hcS hμG (hdx.trans hxX)
  obtain ⟨hDμ, -, hμ'G, -⟩ := sv_B_lvl hμC
  have hEμ' : ggE ≤ Bc.bcB S n μ := sv_B_geE hDμ hEμ
  have hd' : ssDatL (Bc.bcB S n μ) = Bc.bcB S n (ssDatL μ) := sv_B_datL hμC
  have hdL : ssDatL μ < Nc.ncL S ω := hdx.trans hxL
  have hηL : η < Nc.ncL S ω := hηx.trans hxL
  have hBdx : Bc.bcB S n (ssDatL μ) < Bc.bcB S n x := (Bc.bcB_lt_iff hdL hxL).2 hdx
  have hμ'T : ssDatL (Bc.bcB S n μ) ∈ Tset (Bc.bcB S n t) := by rw [hd']; exact hTm' _ (hBdx.trans hhi')
  have hBηx : Bc.bcB S n η < Bc.bcB S n x := (Bc.bcB_lt_iff hηL hxL).2 hηx
  have hBηT : Bc.bcB S n η ∈ Tset (Bc.bcB S n t) := hTm' _ (hBηx.trans hhi')
  have hBη1 : Bc.bcB S n η < Om1 := (hBηx.trans hhi').trans hu1'
  -- `x = Φ_μ(y)`, not a fixed point of `Φ_μ`
  obtain ⟨y, hy⟩ := svK_range hC hMG htSC ht1 ht.2 hEμ hμM hμT hη hηΩ
  rw [← hxdef] at hy
  have hnf : ssP μ x ≠ x := by
    intro hfx
    have hLE := svK_le hC hMG htSC ht1 μ hEμ hμM hμT η hη hηΩ
    have h3 : t + η + 1 < x := (svK_SC hC hMG htSC ht1 hEμ hμM hμT hη hηΩ).add_one_lt
      ((lq_SC_indec (svK_SC hC hMG htSC ht1 hEμ hμM hμT hη hηΩ)).add_lt htx hηx)
    have h4 : ssP μ (t + η + 1) < x := by
      conv_rhs => rw [← hfx]
      exact (ssP_lt_iff μ).2 h3
    exact absurd hLE (not_le.2 h4)
  have hyx : y < x := by
    refine lt_of_le_of_ne (hy ▸ ssP_le_self μ y) fun e => hnf ?_
    rw [← e] at hy ⊢; rw [hy]
  set m0 := max t (ssDatL μ) with hm0
  have hm0x : m0 < x := max_lt htx hdx
  have hm0L : m0 < Nc.ncL S ω := hm0x.trans hxL
  obtain ⟨p, hbase, hpx, hmax⟩ := rh_base_below (ssP_normal μ) hm0x hnf
  have hnofix : ∀ z, p < z → z < x → z < ssP μ z := by
    intro z hpz hzx
    by_contra h
    push Not at h
    have hz := le_antisymm h (ssP_le_self μ z)
    have hm0z : m0 < z := by
      rcases hbase with e | ⟨h', -⟩
      · rw [← e]; exact hpz
      · exact h'.trans hpz
    exact absurd (hmax z hz hm0z hzx) (not_le.2 hpz)
  rcases hbase with hpm | ⟨hm0p, hpp⟩
  · -- no fixed point of `Φ_μ` in `(m0, x)`: the first value `ψ_{Ω₁}(K + u_μ)` above `m0`
    obtain ⟨K, hownK, htK, hKm, hmK⟩ := sv_K_of (S := S) htSC (le_max_left _ _) hm0L
    have hdm : ssDatL μ ≤ m0 := le_max_right _ _
    obtain ⟨-, hmE, -, hownE⟩ := sv_least (S := S) hμG hownK hKm hmK hdm
    obtain ⟨c0, hc0, hmin⟩ := sv_first (S := S) hμG hownK hKm hmK hdm
    have hc0y : c0 ≤ y := by
      refine not_lt.1 fun hlt => ?_
      have := hmin y hlt
      rw [hy] at this
      exact absurd hm0x (not_lt.2 this)
    set Ds := y - c0 with hDsdef
    have hcD : c0 + Ds = y := Ordinal.add_sub_cancel_of_le hc0y
    have hnf0 : ∀ σ, σ ≤ Ds → c0 + σ < ssP μ (c0 + σ) := by
      intro σ hσ
      have hzy : c0 + σ ≤ y := by rw [← hcD]; exact (add_le_add_iff_left c0).2 hσ
      refine lt_of_le_of_ne (ssP_le_self μ _) fun hz => ?_
      have hpz : p < c0 + σ := by
        rw [hpm]
        calc m0 < S.psi (K + Le.leOe μ) (Om 1) := hmE
          _ = ssP μ c0 := hc0.symm
          _ ≤ ssP μ (c0 + σ) := (ssP_le_iff μ).2 le_self_add
          _ = c0 + σ := hz.symm
      have := hnofix _ hpz (hzy.trans_lt hyx)
      rw [← hz] at this; exact lt_irrefl _ this
    have hDsx : Ds < x := (Ordinal.sub_le_self y c0).trans_lt hyx
    have hDsT : Ds ∈ Tset t := hTm _ (hDsx.trans hx2)
    have hDs1 : Ds < Om1 := (hDsx.trans hx2).trans hu1
    have hc0τ : t < ssP μ c0 := (le_max_left _ _).trans_lt (by rw [hc0]; exact hmE)
    have hc0d : ssDatL μ < ssP μ c0 := (le_max_right _ _).trans_lt (by rw [hc0]; exact hmE)
    have hvx : vt t (Om1 * (Om1 + μ) + Ds) = x := by
      rw [svK_enum0 hC hMG htSC ht1 ht.2 hEμ hμM hμT hc0τ hc0d (fun c hc => le_max_iff.1 (hmin c hc)) Ds hDsT
        hDs1 (sv_valid_of hnf0), hcD, hy]
    have hηD : η = Ds := svK_inj hC hMG htSC ht1 hEμ hμM hμT hη hηΩ hDsT hDs1 (by rw [hvx])
    -- the move of the first value
    have hlo : Bc.bcC S n ≤ S.psi K (Om 1) := hc.trans htK
    have hc0x : ssP μ c0 ≤ x := by rw [← hy, ← hcD]; exact (ssP_le_iff μ).2 le_self_add
    have hEX : S.psi (K + Le.leOe μ) (Om 1) < Bc.bcC S (n + 1) := by rw [← hc0]; exact hc0x.trans_lt hxX
    obtain ⟨K', hownK', hBK, hBK1, hBKu⟩ := sv_B_least hμC hownK hlo hownE hEX
    have hKL : S.psi K (Om 1) < Nc.ncL S ω := hKm.trans_lt hm0L
    have hK1L : S.psi (K + 1) (Om 1) < Nc.ncL S ω :=
      ((psi_mono (S := S) Low.InR_Om_one (add_le_add_right (one_le_iff_ne_zero.2 (rhU_ne μ)) K)).1).trans_lt
        (hEX.trans hLw)
    set m0' := max (Bc.bcB S n t) (ssDatL (Bc.bcB S n μ)) with hm0'
    have hBm0 : Bc.bcB S n m0 = m0' := by rw [hm0', hd', hm0, sv_B_max htL hdL]
    have hK'm : S.psi K' (Om 1) ≤ m0' := by rw [← hBK, ← hBm0]; exact Ri.riB_mono hm0L hKm
    have hmK' : m0' < S.psi (K' + 1) (Om 1) := by
      rw [← hBK1, ← hBm0]; exact (Bc.bcB_lt_iff hm0L hK1L).2 hmK
    have hdm' : ssDatL (Bc.bcB S n μ) ≤ m0' := le_max_right _ _
    obtain ⟨-, hmE', -, -⟩ := sv_least (S := S) hμ'G hownK' hK'm hmK' hdm'
    obtain ⟨c0', hc0', hmin'⟩ := sv_first (S := S) hμ'G hownK' hK'm hmK' hdm'
    have hc0τ' : Bc.bcB S n t < ssP (Bc.bcB S n μ) c0' := (le_max_left _ _).trans_lt (by rw [hc0']; exact hmE')
    have hc0d' : ssDatL (Bc.bcB S n μ) < ssP (Bc.bcB S n μ) c0' :=
      (le_max_right _ _).trans_lt (by rw [hc0']; exact hmE')
    have hmin'' : ∀ c < c0', ssP (Bc.bcB S n μ) c ≤ Bc.bcB S n t ∨
        ssP (Bc.bcB S n μ) c ≤ ssDatL (Bc.bcB S n μ) := fun c hc => le_max_iff.1 (hmin' c hc)
    rcases eq_or_ne Ds 0 with hD0 | hD0
    · -- `x` is the first value itself
      have hx0 : x = S.psi (K + Le.leOe μ) (Om 1) := by rw [← hy, ← hcD, hD0, add_zero, hc0]
      have h0 := svK_enum0 hC hMG ht'SC ht'1 ht'.2 hEμ' hμ'M hμ'T hc0τ' hc0d' hmin'' 0
        (mem_T_of_le (gg_SC_eps ht'SC) ht'1 zero_le) (lt_of_le_of_lt zero_le ht'1)
        (fun σ hσ => by rw [nonpos_iff_eq_zero.1 hσ]; exact (ssP_SC _ _).1)
      rw [add_zero, add_zero] at h0
      rw [hηD, hD0, Bc.bcB_zero, add_zero, h0, hc0', hx0, hBKu]
    · set δ := Ds - 1 with hδdef
      have hδ : 1 + δ = Ds := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hD0)
      have hcδ : c0 + 1 + δ = y := by rw [add_assoc, hδ, hcD]
      have hcond : ∀ σ, σ ≤ δ → c0 + 1 + σ < ssP μ (c0 + 1 + σ) := by
        intro σ hσ
        have := hnf0 (1 + σ) (by rw [← hδ]; exact (add_le_add_iff_left 1).2 hσ)
        rwa [← add_assoc] at this
      obtain ⟨B', -, -, hB0', himg⟩ := sv_B_run hμC hownE (rh_dvd_add_self μ K) hc0
        (hlo.trans (psi_mono (S := S) Low.InR_Om_one le_self_add).1)
        (hdm.trans_lt hmE) (by rw [hcδ, hy]; exact hxX) hcond
      have hc1 : ssP (Bc.bcB S n μ) c0' = S.psi B' (Om 1) := by rw [hc0', ← hBKu, hB0']
      obtain ⟨hBxF, hcond'⟩ := himg c0' hc1
      rw [hcδ, hy] at hBxF
      have hδL : δ < Nc.ncL S ω := ((Ordinal.sub_le_self Ds 1).trans_lt hDsx).trans hxL
      have hBη : Bc.bcB S n η = 1 + Bc.bcB S n δ := by
        rw [hηD, ← hδ, Bc.bcB_add h1L hδL, Mw.mwB_one]
      rw [hBxF, svK_enum0 hC hMG ht'SC ht'1 ht'.2 hEμ' hμ'M hμ'T hc0τ' hc0d' hmin'' _ hBηT hBη1
        (by rw [hBη]; exact sv_valid_one hcond'), hBη, add_assoc]
  · -- `p > m0` a fixed point of `Φ_μ`: `x = Φ_μ(p + 1 + δ) = ϑᵗ(Δ_μ + (p + δ))`
    have htp : t < p := (le_max_left _ _).trans_lt hm0p
    have hdp : ssDatL μ < p := (le_max_right _ _).trans_lt hm0p
    have hpSC : SC p := hpp ▸ ssP_SC μ p
    have hpL : p < Nc.ncL S ω := hpx.trans hxL
    have hpX : p < Bc.bcC S (n + 1) := hpx.trans hxX
    have hpW : p < S.psi (bcAlphaW S) (Om 1) := by rw [← Bc.ncL_omega_eq S]; exact hpL
    obtain ⟨Bp, hownp, hBp⟩ := rb_own_of_SC hpSC hpW
    have hdvd2p : Le.leOe (μ + 1) ∣ Bp := sv_conv hμG hownp (by rw [hBp]; exact hpp)
    have hdvd1p : Le.leOe μ ∣ Bp := (rhU_dvd le_self_add).trans hdvd2p
    have hpy : p < y := (ssP_lt_iff μ).1 (by rw [hpp, hy]; exact hpx)
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
    have hcond : ∀ σ, σ ≤ δ → p + 1 + σ < ssP μ (p + 1 + σ) := by
      intro σ hσ
      refine hnofix _ (lt_of_lt_of_le (lt_add_one p) le_self_add) (lt_of_le_of_lt ?_ hyx)
      rw [← hpδy]; exact (add_le_add_iff_left _).2 hσ
    have hlo : Bc.bcC S n ≤ S.psi Bp (Om 1) := by rw [hBp]; exact hc.trans htp.le
    obtain ⟨B', -, -, hB0', himg⟩ := sv_B_run hμC hownp hdvd1p (hpp.trans hBp.symm) hlo
      (by rw [hBp]; exact hdp) (by rw [hpδy, hy]; exact hxX) hcond
    have hpp' : ssP (Bc.bcB S n μ) (Bc.bcB S n p) = Bc.bcB S n p := by
      have := sv_B_fix hμC hownp hlo (by rw [hBp]; exact hpX) (by rw [hBp]; exact hpp)
      rwa [hBp] at this
    have hc1 : ssP (Bc.bcB S n μ) (Bc.bcB S n p) = S.psi B' (Om 1) := by rw [hpp', ← hBp, hB0']
    obtain ⟨hBxF, hcond'⟩ := himg _ hc1
    rw [hpδy, hy] at hBxF
    have hpδT : p + δ ∈ Tset t := hTm _ (hpδx.trans hx2)
    have hpδ1 : p + δ < Om1 := (hpδx.trans hx2).trans hu1
    have hvx : vt t (Om1 * (Om1 + μ) + (p + δ)) = x := by
      rw [svK_enum_fix2 hC hMG htSC ht1 ht.2 hEμ hμM hμT hpp htp δ hpδT hpδ1 hcond, hpδy, hy]
    have hηδ : η = p + δ := svK_inj hC hMG htSC ht1 hEμ hμM hμT hη hηΩ hpδT hpδ1 (by rw [hvx])
    have hδL : δ < Nc.ncL S ω := (le_add_self.trans_lt hpδx).trans hxL
    have hBpδ : Bc.bcB S n (p + δ) = Bc.bcB S n p + Bc.bcB S n δ := Bc.bcB_add hpL hδL
    have ht'p' : Bc.bcB S n t < Bc.bcB S n p := (Bc.bcB_lt_iff htL hpL).2 htp
    have hpδx' : Bc.bcB S n p + Bc.bcB S n δ < Bc.bcB S n x := by
      rw [← hBpδ]; exact (Bc.bcB_lt_iff (hpδx.trans hxL) hxL).2 hpδx
    have hpδT' : Bc.bcB S n p + Bc.bcB S n δ ∈ Tset (Bc.bcB S n t) := hTm' _ (hpδx'.trans hhi')
    have hpδ1' : Bc.bcB S n p + Bc.bcB S n δ < Om1 := (hpδx'.trans hhi').trans hu1'
    rw [hηδ, hBpδ, svK_enum_fix2 hC hMG ht'SC ht'1 ht'.2 hEμ' hμ'M hμ'T hpp' ht'p' _ hpδT' hpδ1' hcond',
      hBxF]

/-- **`B_n(ϑ^β(Δ_μ + η)) = ϑ^{B_n β}(Δ_{B_n μ} + B_n η)`** for every level-closed `β < c_{n+1}`, every level
`E₁ ≤ μ < M` with `ssDatL μ ∈ Tᵝ` and `B_n μ < M`, and `η ∈ Tᵝ ∩ Ω₁`. -/
theorem svVtE {M : Ordinal.{0}} (hC : SvCit M) (hMG : M ≤ ggGam) {n : ℕ} {β μ η : Ordinal.{0}} (hβ : SpLC β)
    (hβc : β < Bc.bcC S (n + 1)) (hEμ : ggE ≤ μ) (hμM : μ < M) (hμ'M : Bc.bcB S n μ < M)
    (hμT : ssDatL μ ∈ Tset β) (hη : η ∈ Tset β) (hηΩ : η < Om1) :
    Bc.bcB S n (vt β (Om1 * (Om1 + μ) + η)) =
      vt (Bc.bcB S n β) (Om1 * (Om1 + Bc.bcB S n μ) + Bc.bcB S n η) := by
  have hβE : InE β := gg_SC_eps hβ.1
  have hβ1 : β < Om1 := (Rt.rt_lt_Om1 hβc).1
  obtain ⟨-, -, hxT, -, hx1, -, hdx, hηx⟩ := svK_facts hC hMG hβ.1 hβ1 hEμ hμM hμT hη hηΩ
  rcases le_or_gt (Bc.bcC S n) β with hc | hc
  · obtain ⟨u, huc, hTw, hTw'⟩ := ssWin hβE hc hβc
    have hu1 : u < Om1 := (Rt.rt_lt_Om1 huc).1
    have hu1' : Bc.bcB S n u < Om1 := (Rt.rt_lt_Om1 huc).2
    exact svVt_core hC hMG hc hβc ((hTw _ hx1).1 hxT) huc (fun a ha => (hTw a (ha.trans hu1)).2 ha)
      (fun a ha => (hTw' a (ha.trans hu1')).2 ha) hβ (spLC_img hβ hc hβc) hEμ hμM hμ'M hμT hη hηΩ
  · -- below `c_n`: `B_n` fixes the value, the base, the level and `η`
    obtain ⟨m, -, -, hmin, hTm, -⟩ := T_next (Or.inr hβE) hβ1
    have hmc : m ≤ Bc.bcC S n := hmin _ hc (Rt.rt_c_inf n)
    have hxc : vt β (Om1 * (Om1 + μ) + η) < Bc.bcC S n := ((hTm _ hx1).1 hxT).trans_le hmc
    have hdc : ssDatL μ < Bc.bcC S n := hdx.trans hxc
    have hcS : SC (Bc.bcC S n) := Lw.lw_L_SC S _
    have hμC : GgCl (Bc.bcC S n) μ := ss_code_lvl hcS (hμM.trans_le hMG) hdc
    have hBμ : Bc.bcB S n μ = μ := Sm.smB_code_fix μ hμC
    rw [Bc.bcB_fix' S n _ hxc, Bc.bcB_fix' S n _ hc, Bc.bcB_fix' S n _ (hηx.trans hxc), hBμ]

end Googology.Trans.PoR.InaccPsi.R2.Sv
