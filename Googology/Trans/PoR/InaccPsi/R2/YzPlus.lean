import Googology.Trans.PoR.InaccPsi.R2.CitedYz
import Googology.Trans.PoR.InaccPsi.R2.YuEps
import Googology.Trans.PoR.InaccPsi.R2.VjVt
import Googology.Trans.PoR.InaccPsi.R2.VjTop
import Googology.Trans.PoR.InaccPsi.R2.SpVt
import Googology.Trans.PoR.InaccPsi.R2.UoB
import Googology.Trans.PoR.InaccPsi.R2.SfRst
import Googology.Trans.PoR.InaccPsi.R2.CitedUz

/-!
# The gap `ε`-numbers at the top level: `Yu.YuGapPlus` and `Yu.YuGapEpsTop` proved

Notation as in `R2.YuEps`: a window `(n, λ, λ')`, a far index `p`, `B_n = Bc.bcB S n`, a gap point `a`
(`B_n q ≤ a < B_n p` for `q < p`), `τ = υ_ξ` the bracket base of `a`, `a = ϑᵗ(ξ')` with `ξ' ≥ Ω₁·ε_{Ω₁+1}`,
`Δ_μ = Ω₁·(Ω₁ + μ)`, `d_μ = Ul.ulD S 0 μ`, `θ = ConjT.th S`.

* `yzLhPlus`: **`Yu.YuLhPlus`** from the cited `R2.yzLhT_lt_plus` ([W07b] Lemma 4.2).
* `yz_cmp_hi` (**`a⁺ ≤ X`**): for `a = ϑᵗ(Δ_{μ'} + η') < X = ϑᵗ(Δ_{μX} + ηX)` with `d_{μX} < a`, `ηX < a`:
  `ϑᵗ(Δ_{μ'} + η' + 1) ≤ X` (`Vj.vjc_lt_of`: `ξ' < ξX`; then `Vj.vjc_vt_lt`).
* `yz_cmp_lo`: `ϑᵗ(Ω₁·M + η) < a` for countable `M, η < a` (`Vj.vjc_vt_lt`, `Vj.vj_small`).
* `yz_gap_strict` (`B_n q < a` for every `q < p`), `yz_gap_base` (**the bracket base of `p` is sent to `τ`**: `p`
  is not a `υ`-point, `p ∈ (υ_{ξ₀}, υ_{ξ₀+1})`, `B_n υ_{ξ₀} = υ_ξ`; by `Sf.sfShiftAll`).
* `yzGapPlus`: **`Yu.YuGapPlus S`**, no hypothesis: `p = ϑ^{υ_{ξ₀}}(Ω₁·M_p + η_p)`; for `M_p < Ω₁`, `B_n p =
  ϑᵗ(Ω₁·B_n M_p + B_n η_p) < a` (`Sp.spVtU_all`, `Vj.vjVtTopAll`, `Vj.vjB_Om1mul`), impossible; for `M_p ≥ Ω₁`,
  `B_n p = ϑᵗ(Δ_{B_n μ_p} + B_n η_p)` (`Vj.vjVtE`), `d_{B_n μ_p} = B_n d_{μ_p}`-wise below `a` (`Uo.uoDat_B`) and
  `B_n η_p < a`, so `a⁺ ≤ B_n p` by `yz_cmp_hi`.
* `yzGapEpsTop`: **`Yu.YuGapEpsTop S`** under `L(ω+1) ≤ ν_C` (`Yu.yuTop_of_plus`), `yzGapEps` (**`Ye.YeGapEps S`**).

New axiom: none here (`R2.CitedYz.yzLhT_lt_plus` is the cited one).  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ul
  Googology.Trans.PoR.InaccPsi.R2.Vd Googology.Trans.PoR.InaccPsi.R2.Vj Googology.Trans.PoR.InaccPsi.R2.Mv

variable {S : InaccSeq.{0}}

/-! ## [W07b] Lemma 4.2 as `Yu.YuLhPlus` -/

/-- **`Yu.YuLhPlus`** (from the cited [W07b] Lemma 4.2). -/
theorem yzLhPlus : Yu.YuLhPlus := fun _ _ hτ hτ1 hξT hξ2 hΩ =>
  yzLhT_lt_plus hτ hτ1 hξT hξ2 ((vt_E_iff hτ hτ1 hξT hξ2).2 hΩ).1

/-! ## Comparisons of `ϑ`-values -/

/-- `Ω₁·a + b < Ω₁·c + d` with `d < Ω₁` gives `a ≤ c`. -/
theorem yz_om1_le {a b c d : Ordinal.{0}} (h : Om1 * a + b < Om1 * c + d) (hd : d < Om1) : a ≤ c := by
  by_contra hca
  push Not at hca
  have h1 : Om1 * c + d < Om1 * (c + 1) := by rw [mul_add_one]; exact (add_lt_add_iff_left _).2 hd
  have h2 : Om1 * (c + 1) ≤ Om1 * a := mul_le_mul_left' (Order.add_one_le_of_lt hca) _
  exact absurd (h.trans (h1.trans_le (h2.trans le_self_add))) (lt_irrefl _)

section Cmp

variable {τ : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1)
include hτ hτ1

/-- **`a⁺ ≤ X`**: for `a = ϑᵗ(Δ_{μ'} + η') < X = ϑᵗ(Δ_{μX} + ηX)` with `d_{μX} < a` and `ηX < a`. -/
theorem yz_cmp_hi {μ' η' μX ηX : Ordinal.{0}} (hμ'θ : μ' < ConjT.th S) (hμ'T : vdDat S (Om1 + μ') ∈ Tset τ)
    (hη'T : η' ∈ Tset τ) (hη'1 : η' < Om1) (hη1T : η' + 1 ∈ Tset τ)
    (hμXθ : μX < ConjT.th S) (hμXT : vdDat S (Om1 + μX) ∈ Tset τ) (hηXT : ηX ∈ Tset τ) (hηX1 : ηX < Om1)
    (hlt : vt τ (Om1 * (Om1 + μ') + η') < vt τ (Om1 * (Om1 + μX) + ηX))
    (hd : ulD S 0 μX < vt τ (Om1 * (Om1 + μ') + η')) (hη : ηX < vt τ (Om1 * (Om1 + μ') + η')) :
    vt τ (Om1 * (Om1 + μ') + η' + 1) ≤ vt τ (Om1 * (Om1 + μX) + ηX) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  obtain ⟨hξ'T, hξ'2, -, -, -, haE, hda, hηa⟩ := vjK_facts hτ hτ1 hμ'θ hμ'T hη'T hη'1
  have hSa := vjK_SC hτ hτ1 hμ'θ hμ'T hη'T hη'1
  have hξlt : Om1 * (Om1 + μ') + η' < Om1 * (Om1 + μX) + ηX :=
    vjc_lt_of hτE hτ1 hμXθ hξ'T hξ'2 hμXT hηXT hηX1 hSa hd hη hlt
  rcases (Order.add_one_le_of_lt hξlt).lt_or_eq with h | h
  · rw [add_assoc] at h ⊢
    have hη'11 : η' + 1 < Om1 := Rj.rj_Om1_inE.add_lt hη'1 ((one_lt_omega0).trans (omega0_lt_inE Rj.rj_Om1_inE))
    have hM' : Om1 + μ' ≤ Om1 + μX := yz_om1_le h hηX1
    obtain ⟨-, -, -, -, hX1, -, -, -⟩ := vjK_facts hτ hτ1 hμXθ hμXT hηXT hηX1
    have hSX := vjK_SC hτ hτ1 hμXθ hμXT hηXT hηX1
    have hd' : VdLtS S (Om1 + μ') (vt τ (Om1 * (Om1 + μX) + ηX)) := (vj_ltS hSX hX1.le).2 (hda.trans hlt)
    have hη'X : η' + 1 < vt τ (Om1 * (Om1 + μX) + ηX) :=
      (haE.add_lt hηa (Gg.gg_one_lt_of_SC hSa)).trans hlt
    exact (vjc_vt_lt hτE hτ1 hμXθ hM' hμ'T hη1T hη'11 hμXT hηXT hηX1 h hd' hη'X).le
  · rw [h]

/-- `ϑᵗ(Ω₁·M + η) < a = ϑᵗ(Δ_{μ'} + η')` for countable `M, η < a` in `Tᵗ`. -/
theorem yz_cmp_lo {μ' η' M η : Ordinal.{0}} (hμ'θ : μ' < ConjT.th S) (hμ'T : vdDat S (Om1 + μ') ∈ Tset τ)
    (hη'T : η' ∈ Tset τ) (hη'1 : η' < Om1) (hM1 : M < Om1) (hMT : M ∈ Tset τ) (hηT : η ∈ Tset τ)
    (hη1 : η < Om1) (hMa : M < vt τ (Om1 * (Om1 + μ') + η')) (hηa : η < vt τ (Om1 * (Om1 + μ') + η')) :
    vt τ (Om1 * M + η) < vt τ (Om1 * (Om1 + μ') + η') := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hM' : M ≤ Om1 + μ' := hM1.le.trans le_self_add
  have hMT' : vdDat S M ∈ Tset τ := by rw [(vj_small (S := S) (v := 0) hM1).1]; exact hMT
  have harg : Om1 * M + η < Om1 * (Om1 + μ') + η' := by
    have h1 : Om1 * M + η < Om1 * (M + 1) := by rw [mul_add_one]; exact (add_lt_add_iff_left _).2 hη1
    have h2 : Om1 * (M + 1) ≤ Om1 * (Om1 + μ') :=
      mul_le_mul_left' ((Order.add_one_le_of_lt hM1).trans le_self_add) _
    exact (h1.trans_le h2).trans_le le_self_add
  have hd' : VdLtS S M (vt τ (Om1 * (Om1 + μ') + η')) := (vj_small hM1).2.2 hMa
  exact vjc_vt_lt hτE hτ1 hμ'θ hM' hMT' hηT hη1 hμ'T hη'T hη'1 harg hd' hηa

end Cmp

/-! ## The gap and the bracket base of `p` -/

/-- `1 < c_n`. -/
theorem yz_one_lt_c (n : ℕ) : (1 : Ordinal.{0}) < Bc.bcC S n :=
  (one_lt_omega0).trans (omega0_lt_inE (upsPt_inE ⟨Xw.xw_c_pos n, Rt.rt_c_inf n⟩))

/-- **The strict gap**: `B_n q < a` for every `q < p`. -/
theorem yz_gap_strict {n : ℕ} {l l' p a : Ordinal.{0}} (hP : Ye.YeGapPt S n l l' p a) (hE : InE a) :
    ∀ q < p, Bc.bcB S n q < a := by
  have hpE := Yu.yu_gap_pE hP hE
  obtain ⟨hW, hfar, hp, -, -, -, -, hgap⟩ := hP
  obtain ⟨-, hpL, -, -, -⟩ := Xw.xwWin hW hfar hp
  intro q hq
  have hq1 : q + 1 < p := hpE.add_lt hq ((one_lt_omega0).trans (omega0_lt_inE hpE))
  have h := hgap _ hq1
  have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω := (yz_one_lt_c n).trans (Bc.bcC_lt S n)
  rw [Bc.bcB_add (hq.trans hpL) h1L, Bc.bcB_fix' S n 1 (yz_one_lt_c n)] at h
  exact Order.add_one_le_iff.1 h

/-- **The bracket base of `p`**: `p` is not a `υ`-point; `υ_{ξ₀} < p < υ_{ξ₀+1}` with `ξ₀ ≠ 0`, `c_n ≤ υ_{ξ₀}`,
`υ_{ξ₀+1} < c_{n+1}`, and `B_n υ_{ξ₀} = υ_ξ` (the bracket base of `a`), `B_n p < υ_{ξ+1}`. -/
theorem yz_gap_base {n : ℕ} {l l' p a ξ : Ordinal.{0}} (hP : Ye.YeGapPt S n l l' p a) (hE : InE a)
    (hnoU : ∀ u, UpsPt u → a < u → Bc.bcB S n p < u) (hτa : upsilon ξ < a) (h2a : a < upsilon (ξ + 1)) :
    ∃ ξ₀, ξ₀ ≠ 0 ∧ Bc.bcC S n ≤ upsilon ξ₀ ∧ upsilon ξ₀ < p ∧ p < upsilon (ξ₀ + 1) ∧
      upsilon (ξ₀ + 1) < Bc.bcC S (n + 1) ∧ Bc.bcB S n (upsilon ξ₀) = upsilon ξ := by
  have hgs := yz_gap_strict hP hE
  obtain ⟨hW, hfar, hp, -, -, -, ha, -⟩ := hP
  obtain ⟨hpC, hpL, -, hδp, -⟩ := Xw.xwWin hW hfar hp
  have hcp : Bc.bcC S n < p := hW.2.1.trans ((cdRho_lt_delta l).trans hδp)
  obtain ⟨ξ₀, h01, h02⟩ := Lh.lhBracket p
  obtain ⟨k, hk0, hk⟩ := upsPt_iff_upsilon.1 (show UpsPt (Bc.bcC S n) from ⟨Xw.xw_c_pos n, Rt.rt_c_inf n⟩)
  have hkξ : k ≤ ξ₀ := Order.lt_add_one_iff.1 (Tp.tpUps_lt_iff.1 (hk ▸ hcp.trans h02))
  have h0n : Bc.bcC S n ≤ upsilon ξ₀ := hk ▸ Tp.tpUps_le_iff.2 hkξ
  have hξ00 : ξ₀ ≠ 0 := fun h0 => (pos_iff_ne_zero.1 hk0) (nonpos_iff_eq_zero.1 (h0 ▸ hkξ))
  have hτ0c : upsilon ξ₀ < Bc.bcC S (n + 1) := h01.trans_lt hpC
  obtain ⟨μ, β, hμ, hβ, hζ, hμn⟩ := Tp.tpWin_idx h0n
  have hμx : upsilon μ < Bc.bcC S (n + 1) :=
    lt_of_le_of_lt (upsilon_normal.strictMono.monotone (le_self_add.trans_eq hζ.symm)) hτ0c
  obtain ⟨μ', -, hB⟩ := Sf.sfShiftAll n μ hμ hμn hμx
  have hz1 : upsilon (ξ₀ + 1) < Bc.bcC S (n + 1) := Tp.tpWin_succ hτ0c
  have e0 : Bc.bcB S n (upsilon ξ₀) = upsilon (μ' + β) := by rw [hζ]; exact hB β hβ (hζ ▸ hτ0c)
  have e1 : Bc.bcB S n (upsilon (ξ₀ + 1)) = upsilon (μ' + β + 1) := by
    have := hB (β + 1) (Tp.tpWW_lim.add_one_lt hβ) (by rw [← add_assoc, ← hζ]; exact hz1)
    rw [← add_assoc, ← add_assoc, ← hζ] at this; exact this
  have hBp : Bc.bcB S n p < upsilon (μ' + β + 1) := by
    rw [← e1]; exact Bc.bcB_mono' S n hpC hz1 h02
  -- `p` is not a `υ`-point
  have hτ0p : upsilon ξ₀ < p := by
    refine lt_of_le_of_ne h01 fun e => ?_
    have hBc : Bc.bcB S n (Bc.bcC S n) ≤ Bc.bcB S n p :=
      (Bc.bcB_mono' S n (hcp.trans hpC) hpC hcp).le
    have hpos : 0 < μ' + β := by
      rw [pos_iff_ne_zero]; intro h0
      rw [← e, e0, h0, upsilon_zero] at hBc
      have : (0 : Ordinal.{0}) < Bc.bcB S n (Bc.bcC S n) := by
        rw [show Bc.bcC S n = Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) from rfl, Bc.bcB_base]
        exact (Xw.xw_c_pos n).trans (Bc.bcC_lt S n)
      exact absurd hBc (not_le.2 this)
    have hU : UpsPt (Bc.bcB S n p) := by rw [← e, e0]; exact upsPt_upsilon hpos
    exact lt_irrefl _ (hnoU _ hU ha)
  have h1 : upsilon (μ' + β) < a := e0 ▸ hgs _ hτ0p
  have hle1 : μ' + β ≤ ξ := Order.lt_add_one_iff.1 (Tp.tpUps_lt_iff.1 (h1.trans h2a))
  have hle2 : ξ ≤ μ' + β := Order.lt_add_one_iff.1 (Tp.tpUps_lt_iff.1 ((hτa.trans ha).trans hBp))
  exact ⟨ξ₀, hξ00, h0n, hτ0p, h02, hz1, by rw [e0, le_antisymm hle1 hle2]⟩

/-! ## `Yu.YuGapPlus` -/

/-- **`Yu.YuGapPlus S`**: at a top-level gap `ε`-number `a = ϑ^{υ_ξ}(ξ')`, `a⁺ = ϑ^{υ_ξ}(ξ' + 1) ≤ B_n p`.
No hypothesis beyond `S`. -/
theorem yzGapPlus : Yu.YuGapPlus S := by
  intro n l l' p a ξ ξ' hP hE hU hnoU hξ0 hτa h2a hξ'T hξ'2 hv htop
  have hgs := yz_gap_strict hP hE
  have hpE := Yu.yu_gap_pE hP hE
  obtain ⟨ξ₀, hξ00, -, hτ0p, hp0, hz1, hBτ⟩ := yz_gap_base hP hE hnoU hτa h2a
  obtain ⟨hW, hfar, hp, -, -, -, ha, -⟩ := hP
  obtain ⟨hpC, hpL, hBp1, -, -⟩ := Xw.xwWin hW hfar hp
  -- the base `τ = υ_ξ` of `a`
  have ha1 : a < Om1 := ha.trans hBp1
  have hτU : UpsPt (upsilon ξ) := upsPt_upsilon (pos_iff_ne_zero.2 hξ0)
  have hτE : InE (upsilon ξ) := upsPt_inE hτU
  have hτ1 : upsilon ξ < Om1 := hτa.trans ha1
  have hXL : Bc.bcB S n p < Nc.ncL S (ω + 1) := Bc.bcB_bound' S n p hpC
  have hτP : upsilon ξ < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S]; exact hτa.trans (ha.trans hXL)
  have hτSC : SC (upsilon ξ) := Mv.mvUps_SC hξ0 hτP
  have hc : upsilon (succ ξ) < Om1 := next_lt_Om1 (upsilon_isNext ξ) (Or.inr hτU) hτ1
  have hTτ : ∀ x, x < upsilon (ξ + 1) → x ∈ Tset (upsilon ξ) := by
    intro x hx
    have hx1 : x < Om1 := hx.trans hc
    have h := upsilon_succ_T ξ hc x hx1
    rw [if_neg hξ0] at h
    exact h.2 hx
  have hTa : ∀ x, x < a → x ∈ Tset (upsilon ξ) := fun x hx => hTτ x (hx.trans h2a)
  -- `ξ' = Δ_{μ'} + η'`
  have hΩ1E : Om1 ≤ Gg.ggE := Rj.rj_Om1_lt_E.le
  have hΩξ' : Om1 ≤ ξ' := (Ordinal.le_mul_left Om1 (InE.pos (show InE Gg.ggE from Gg.ggE_spec.1))).trans htop
  obtain ⟨-, hη'T, hη'1, hdec'⟩ := Lu.lu_split hτE hτ1 hξ'T hξ'2 hΩξ'
  set M' := ξ' / Om1 with hM'
  set η' := ξ' % Om1 with hη'
  have hΩ0 : Om1 ≠ 0 := (InE.pos Rj.rj_Om1_inE).ne'
  have hEM' : Gg.ggE ≤ M' := (Ordinal.mul_le_iff_le_div hΩ0).1 htop
  have hξ'θ : ξ' < ConjT.th S := uzTBound (S := S) _ hτE hτ1 ξ' hξ'T hξ'2
  have hM'ξ : M' ≤ ξ' := (Ordinal.le_mul_right M' (InE.pos Rj.rj_Om1_inE)).trans (Ordinal.mul_div_le ξ' Om1)
  set μ' := M' - Om1 with hμ'
  have hμ'M : Om1 + μ' = M' := Ordinal.add_sub_cancel_of_le (hΩ1E.trans hEM')
  have hμ'θ : μ' < ConjT.th S := ((Ordinal.sub_le_self _ _).trans hM'ξ).trans_lt hξ'θ
  have hξ'e : ξ' = Om1 * (Om1 + μ') + η' := by rw [hμ'M]; exact hdec'.symm
  have hμ'T : vdDat S (Om1 + μ') ∈ Tset (upsilon ξ) := vjc_dat hτE hτ1 hμ'θ hη'1 (hξ'e ▸ hξ'T)
  have hva : vt (upsilon ξ) (Om1 * (Om1 + μ') + η') = a := by rw [← hξ'e]; exact hv
  have hSa : SC a := hva ▸ vjK_SC hτSC hτ1 hμ'θ hμ'T hη'T hη'1
  obtain ⟨-, -, -, -, -, -, -, hη'a⟩ := vjK_facts hτSC hτ1 hμ'θ hμ'T hη'T hη'1
  rw [hva] at hη'a
  have hη1T : η' + 1 ∈ Tset (upsilon ξ) := hTa _ (hE.add_lt hη'a (Gg.gg_one_lt_of_SC hSa))
  -- the base `τ₀ = υ_{ξ₀}` of `p`
  have hτ0c : upsilon ξ₀ < Bc.bcC S (n + 1) := hτ0p.trans hpC
  have hLC : Sp.SpLC (upsilon ξ₀) := Sp.spLC_ups hξ00 hτ0c
  have hτ0E : InE (upsilon ξ₀) := Gg.gg_SC_eps hLC.1
  have hτ01 : upsilon ξ₀ < Om1 := (Rt.rt_lt_Om1 hτ0c).1
  have hp1 : p < Om1 := (Rt.rt_lt_Om1 hpC).1
  have hc0 : upsilon (succ ξ₀) < Om1 := (Rt.rt_lt_Om1 hz1).1
  have hpT : p ∈ Tset (upsilon ξ₀) := by
    have h := upsilon_succ_T ξ₀ hc0 p hp1
    rw [if_neg hξ00] at h
    exact h.2 hp0
  obtain ⟨ξp, hξpT, hξp2, hvp⟩ := vt_rep hτ0E hτ01 hpT hτ0p.le hp1 (inE_indec hpE)
  have hΩξp : Om1 ≤ ξp := (vt_E_iff hτ0E hτ01 hξpT hξp2).1 ⟨hvp ▸ hτ0p, hvp ▸ hpE⟩
  obtain ⟨hMp1, hηpT, hηp1, hdecp⟩ := Lu.lu_split hτ0E hτ01 hξpT hξp2 hΩξp
  set Mp := ξp / Om1 with hMp
  set ηp := ξp % Om1 with hηp
  have hξpθ : ξp < ConjT.th S := uzTBound (S := S) _ hτ0E hτ01 ξp hξpT hξp2
  -- the goal in the `Δ`-form
  rw [hξ'e]
  rcases lt_or_ge Mp Om1 with hMpΩ | hΩMp
  · -- low levels: impossible
    exfalso
    have hT' : Om1 * (Om1 * 0 + Mp) + ηp ∈ Tset (upsilon ξ₀) := by rw [mul_zero, zero_add, hdecp]; exact hξpT
    have hMpT : Mp ∈ Tset (upsilon ξ₀) :=
      (Rk.rkArg_T hτ0E hτ01 (lt_of_le_of_lt zero_le hMpΩ) hMpΩ hηp1 hT').2
    have hlow : Mp < p ∧ ηp < p := by
      rcases lt_or_ge Mp (upsilon ξ₀) with hMτ | hτM
      · obtain ⟨-, -, -, -, -, -, -, hηv⟩ := Lu.lu_th_facts hτ0E hτ01 hMp1 hMτ hηpT hηp1
        rw [hdecp, hvp] at hηv
        exact ⟨hMτ.trans hτ0p, hηv⟩
      · obtain ⟨-, -, -, -, -, -, -, hMv, hηv⟩ := Lv.gen_facts hτ0E hτ01 hMpT hτM hMpΩ hηpT hηp1
        rw [hdecp, hvp] at hMv hηv
        exact ⟨hMv, hηv⟩
    have hDM : MvD S Mp := mvD_of_lt (hlow.1.trans hpL)
    have hDη : MvD S ηp := mvD_of_lt (hlow.2.trans hpL)
    obtain ⟨hDOM, hBOM⟩ := vjB_Om1mul (n := n) hDM
    obtain ⟨-, hBadd⟩ := mvB_add (k := n) hDOM hDη
    have hSi := Sp.spVtU_all hLC hτ0c (vjVtTopAll n (upsilon ξ₀) hLC hτ0c)
    have hBp : Bc.bcB S n p = vt (upsilon ξ) (Om1 * Bc.bcB S n Mp + Bc.bcB S n ηp) := by
      rw [← hvp, hSi ξp hξpT hΩξp hξp2, hBτ, ← hdecp, Rj.rj_Om1, hBadd, hBOM]
    have hMa := hgs _ hlow.1
    have hηa := hgs _ hlow.2
    have hlt := yz_cmp_lo hτSC hτ1 hμ'θ hμ'T hη'T hη'1 (hMa.trans ha1) (hTa _ hMa) (hTa _ hηa)
      (hηa.trans ha1) (hva ▸ hMa) (hva ▸ hηa)
    rw [hva, ← hBp] at hlt
    exact absurd ha (not_lt.2 hlt.le)
  · -- levels `≥ Ω₁`
    set μp := Mp - Om1 with hμp
    have hμpM : Om1 + μp = Mp := Ordinal.add_sub_cancel_of_le hΩMp
    have hMpξ : Mp ≤ ξp := (Ordinal.le_mul_right Mp (InE.pos Rj.rj_Om1_inE)).trans (Ordinal.mul_div_le ξp Om1)
    have hμpθ : μp < ConjT.th S := ((Ordinal.sub_le_self _ _).trans hMpξ).trans_lt hξpθ
    have hξpe : ξp = Om1 * (Om1 + μp) + ηp := by rw [hμpM]; exact hdecp.symm
    have hμpT : vdDat S (Om1 + μp) ∈ Tset (upsilon ξ₀) := vjc_dat hτ0E hτ01 hμpθ hηp1 (hξpe ▸ hξpT)
    have hvp' : vt (upsilon ξ₀) (Om1 * (Om1 + μp) + ηp) = p := by rw [← hξpe]; exact hvp
    have hpSC : SC p := hvp' ▸ vjK_SC hLC.1 hτ01 hμpθ hμpT hηpT hηp1
    obtain ⟨-, -, -, -, -, -, hdp, hηpv⟩ := vjK_facts hLC.1 hτ01 hμpθ hμpT hηpT hηp1
    rw [hvp'] at hdp hηpv
    have hBp : Bc.bcB S n p = vt (upsilon ξ) (Om1 * (Om1 + Bc.bcB S n μp) + Bc.bcB S n ηp) := by
      rw [← hvp', vjVtE hLC hτ0c hμpθ hμpT hηpT hηp1, hBτ]
    obtain ⟨hDμ, hBμθ, -⟩ := vj_B_lvl (n := n) hμpθ (hdp.trans hpC)
    -- the datum of `B_n μ_p` is below `a`
    have hpL' : p ≤ Nc.ncL S ω := hpL.le
    obtain ⟨-, hup, -⟩ := vjD_lev hpSC hpL' hdp
    obtain ⟨-, hBu⟩ := Uo.uoDat_B (n := n) hDμ
    have ha1' : a ≤ Om 1 := by rw [← Rj.rj_Om1]; exact ha1.le
    have hdX : ulD S 0 (Bc.bcB S n μp) < a :=
      (vj_dat_iff (vj_B_not μp) hSa ha1').2 (by rw [hBu]; exact hgs _ hup)
    have hδX : vdDat S (Om1 + Bc.bcB S n μp) ∈ Tset (upsilon ξ) := hTa _ ((vj_datv hSa ha1.le).2 hdX)
    have hηX := hgs _ hηpv
    have hlt : vt (upsilon ξ) (Om1 * (Om1 + μ') + η') <
        vt (upsilon ξ) (Om1 * (Om1 + Bc.bcB S n μp) + Bc.bcB S n ηp) := by rw [hva, ← hBp]; exact ha
    rw [hBp]
    exact yz_cmp_hi hτSC hτ1 hμ'θ hμ'T hη'T hη'1 hη1T hBμθ hδX (hTa _ hηX) (hηX.trans ha1) hlt
      (hva ▸ hdX) (hva ▸ hηX)

/-! ## The leaves -/

/-- **`Yu.YuGapEpsTop S`** (under `L(ω+1) ≤ ν_C`): `lh(a) = lhᵗ(a) < a⁺ ≤ B_n p`. -/
theorem yzGapEpsTop (hν : Nc.ncL S (ω + 1) ≤ nuC) : Yu.YuGapEpsTop S := Yu.yuTop_of_plus hν yzLhPlus yzGapPlus

/-- **`Ye.YeGapEps S`** (under `L(ω+1) ≤ ν_C`). -/
theorem yzGapEps (hν : Nc.ncL S (ω + 1) ≤ nuC) : Ye.YeGapEps S := Yu.yuGapEps_of_top hν (yzGapEpsTop hν)

end Googology.Trans.PoR.InaccPsi.R2.Yz
