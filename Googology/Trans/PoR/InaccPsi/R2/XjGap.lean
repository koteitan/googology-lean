import Googology.Trans.PoR.InaccPsi.R2.WwGap
import Googology.Trans.PoR.InaccPsi.R2.XjRoad

/-!
# The gap for forms with constant `ϑ`-levels: `X′ = ϑ^{u₁}(Ω₁·(B₂ + λ) + λ)`; the supply road `Xb.XbVisGen` is void

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`λ = L(k) = υ_λ`, `u₁ = υ_{λ+1}`, `u₂ = υ_{λ+2}`, `M₀ = B₂ + λ`, `X′ = ϑ^{u₁}(Ω₁·M₀ + λ)`.  The forms `Xb.XbForm`
allow a `ϑ`-node `ϑ^{υ_{λ+h}}(Ω₁·M + e)` only at a level `M` whose data lie below some `c < υ_λ` (`Xb.XbCL`).  The
level `M₀` has the leaf `λ`: its `K⁽⁰⁾`-datum is never below a strongly critical `q ≤ λ` (`xj_M0_noLt`, by
`Ul.ulK_mod`, `Ul.ulK_lt_W`).  So `X′` has no form with constant `ϑ`-levels (`xjForm_X`, `xjLast`: the last-term
lemma `Wu.wuLast` with `ϑ`-nodes), and at the window `ν = λ + X′ + ω²` the supply hypothesis `Xb.XbVisGen` of
`Xb.xbRoad` fails (as `Ww.wwVis_ref` for `Wf.WfVisGen`).

* `xj_u1_SC`, `xj_M0_dat`, `xj_M0_noLt` (**no reading of the data of `M₀` lies below `λ`**), `xj_arg`, `xjX_spec`
  (**`X′ ∈ T^{u₁}` is an `ε`-number in `(u₁, u₂)` with the parameter `λ`**), `xj_par_X`;
* `xjVt_ne_low` (no `ϑ^{u₁}(ξ)`, `ξ < B₂`, is `X′`), `xjVt_ne_lev` (**no `ϑ^{u₁}(Ω₁·M + η)` with `VdLtIn M c`, `c ≤
  λ`, is `X′`**: [W07a] Lemma 3.30 through `R2.vdVt_lt`);
* `xjLast` (**the last-term lemma for `Ww.WwE` with `Xb.XbCL`**), `xjForm_X`;
* `xjVis_ref` (**`L(k+1) ≤ ν_C ⇒ ¬ Xb.XbVisGen` at `L(k)`**), `xjRoad_vac`, `xjRoad_false` /
  `xbRoad_false` (**THE HYPOTHESES OF `Xj.xjRoad` AND OF `Xb.xbRoad` ARE JOINTLY FALSE**; `xjRoadZ`, `Xf.xfRoad`, `Xf.xfRoadZ`, `Xb.xbRoadZ` have the same `h0`), `xjFormHighX_fail`
  (**the forms clause `skFormHighX` fails at a high window**).

No new axiom.  New definition: `xjX` (an ordinal).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **The witness** `X′ = ϑ^{u₁}(Ω₁·(B₂ + λ) + λ)`. -/
noncomputable def xjX (S : InaccSeq.{0}) (k : ℕ) : Ordinal.{0} :=
  vt (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1))
    (Om1 * (Uc.ucB + Nc.ncL S (k : Ordinal.{0})) + Nc.ncL S (k : Ordinal.{0}))

/-- `u₁` is strongly critical (a named `υ`-point below `L(k+1)`). -/
theorem xj_u1_SC (k : ℕ) : SC (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) := by
  obtain ⟨-, -, -, hu12, hu2L1, -, -, -, -⟩ := Vr.vr_facts (S := S) k
  refine Mv.mvUps_SC (S := S) (ηx := Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))
    (lt_of_le_of_lt zero_le (lt_add_one _)).ne' ?_
  rw [← Lw.lw_L_eq]; exact hu12.trans hu2L1

/-- `B₂ + λ < θ`. -/
theorem xj_M0_th (k : ℕ) : Uc.ucB + Nc.ncL S (k : Ordinal.{0}) < ConjT.th S := by
  obtain ⟨-, hu1O, hlu1, -, -, -⟩ := Ww.ww_seg (S := S) k
  exact (Xe.xe_th S).1.add_lt Vd.vd_B_lt_th ((hlu1.trans hu1O).trans (Xe.xe_th S).2.1)

/-- **The `K⁽⁰⁾`-datum of `M₀ = B₂ + λ` lies below `u₁`.** -/
theorem xj_M0_dat (k : ℕ) :
    Vd.vdD S 0 (Uc.ucB + Nc.ncL S (k : Ordinal.{0})) < upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) := by
  obtain ⟨-, -, hlu1, -, -, -⟩ := Ww.ww_seg (S := S) k
  rw [Vd.vdD_eq]
  exact (Ul.ul_vis (xj_u1_SC k)).2 (Ul.UlK.add (Ww.ww_B_K _) (Ul.UlK.small hlu1))

/-- `(B₂ + x) % Ω₁ = x` for `x < Ω₁`. -/
theorem xj_mod {x : Ordinal.{0}} (hx : x < Om1) : (Uc.ucB + x) % ω ^ (Om1 : Ordinal.{0}) = x := by
  rw [Rj.rj_Om1_opow]
  conv_lhs => rw [← Uf.uf_Om1_mul_B]
  rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hx]

/-- **No reading of the data of `M₀ = B₂ + λ` lies below `λ`**: `¬ VdLtIn (B₂ + λ) c` for `c ≤ λ`. -/
theorem xj_M0_noLt (k : ℕ) {c : Ordinal.{0}} (hc : c ≤ Nc.ncL S (k : Ordinal.{0})) :
    ¬ Vd.VdLtIn (Uc.ucB + Nc.ncL S (k : Ordinal.{0})) c := by
  obtain ⟨-, hu1O, hlu1, -, -, -⟩ := Ww.ww_seg (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  have hlO : l < Om1 := hlu1.trans hu1O
  rintro (⟨hB, -⟩ | ⟨S', -, -, q, hq, hqc, hd⟩)
  · exact absurd hB (not_lt.2 le_self_add)
  · rw [Vd.vdD_eq] at hd
    have hK := (Ul.ul_vis hq).1 hd
    have hK2 := Ul.ulK_mod hq _ hK Om1
    rw [xj_mod hlO] at hK2
    have h1 : (0 : Ordinal.{0}) < ω := omega0_pos
    have h2 : Om (0 : Ordinal.{0}) < q := by rw [Om_zero]; exact hq.1
    have h3 : l < Om ((0 : Ordinal.{0}) + 1) := by rw [zero_add, ← Rj.rj_Om1]; exact hlO
    have hlq := Ul.ulK_lt_W h1 hq h2 hK2 h3
    exact absurd (hlq.trans_le (hqc.trans hc)) (lt_irrefl _)

/-- The argument `Ω₁·M₀ + λ` lies in `T^{u₁} ∩ Ω₂` above `Ω₁`, and `λ` is one of its additive components. -/
theorem xj_arg (k : ℕ) :
    Om1 * (Uc.ucB + Nc.ncL S (k : Ordinal.{0})) + Nc.ncL S (k : Ordinal.{0}) ∈
      Tset (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) ∧
    Om1 * (Uc.ucB + Nc.ncL S (k : Ordinal.{0})) + Nc.ncL S (k : Ordinal.{0}) < OmTwo ∧
    Om1 ≤ Om1 * (Uc.ucB + Nc.ncL S (k : Ordinal.{0})) + Nc.ncL S (k : Ordinal.{0}) ∧
    Nc.ncL S (k : Ordinal.{0}) ∈ comps (Om1 * (Uc.ucB + Nc.ncL S (k : Ordinal.{0})) + Nc.ncL S (k : Ordinal.{0})) ∧
    Vd.VdDatIn (· ∈ Tset (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1))) (Uc.ucB + Nc.ncL S (k : Ordinal.{0})) := by
  obtain ⟨hP, hu1O, hlu1, hlfix, -, -⟩ := Ww.ww_seg (S := S) k
  obtain ⟨hl0, -, -, hu12, -, -, -, -, -⟩ := Vr.vr_facts (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  set u1 := upsilon (l + 1) with hu1def
  have hu1E : InE u1 := upsPt_inE hP
  have hlO : l < Om1 := hlu1.trans hu1O
  have hlT : l ∈ Tset u1 := Ww.ww_mem k (hlu1.trans hu12)
  have hθ := xj_M0_th (S := S) k
  have hMT : Vd.VdDatIn (· ∈ Tset u1) (Uc.ucB + l) :=
    Vd.vdDatIn_th (S := S) le_self_add hθ (Ww.ww_mem k ((xj_M0_dat k).trans hu12))
  have hM1 : Om1 ≤ Uc.ucB + l := Uc.ucB_gt.le.trans le_self_add
  have hmem := vdArg_mem hu1E hu1O hM1 hMT hlT hlO
  have hΓ2 : Om1 * (Uc.ucB + l) < OmTwo := (Xe.xe_mul_lt_th hθ).trans (Xe.xe_th S).2.2
  refine ⟨hmem, Ww.ww_Om2_E.add_lt hΓ2 (hlO.trans tqc_Om1_lt_OmTwo),
    (hM1.trans (Xe.xe_le_mul _)).trans le_self_add, ?_, hMT⟩
  have hlE : InE l := hlfix ▸ upsPt_inE (upsPt_upsilon hl0)
  have hd : ω ^ Om1 ∣ Om1 * (Uc.ucB + l) := by
    rw [Rj.rj_Om1_inE]; exact dvd_mul_right _ _
  have hlt : l < ω ^ Om1 := by rw [Rj.rj_Om1_inE]; exact hlO
  refine Rj.rj_comps_add _ hd l hlt l ?_
  have : comps l = [l] := by
    have h := comps_opow l; rwa [hlE] at h
  rw [this]; exact List.mem_singleton_self l

/-- **The witness is an `ε`-number of `T^{u₁}` in `(u₁, u₂)` with the parameter `λ`.** -/
theorem xjX_spec (k : ℕ) :
    xjX S k ∈ Tset (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) ∧ InE (xjX S k) ∧
    upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) < xjX S k ∧ xjX S k < upsilon (Nc.ncL S (k : Ordinal.{0}) + 2) ∧
    Nc.ncL S (k : Ordinal.{0}) ∈ Par (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) (xjX S k) := by
  obtain ⟨hP, hu1O, hlu1, -, -, hT⟩ := Ww.ww_seg (S := S) k
  obtain ⟨hξT, hξ2, hΩξ, hlc, -⟩ := xj_arg (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  set u1 := upsilon (l + 1) with hu1def
  have hu1E : InE u1 := upsPt_inE hP
  obtain ⟨hXT, -, hX1, -, hPar⟩ := vt_memTwo hu1E hu1O hξT hξ2
  obtain ⟨hu1X', hXE⟩ := (vt_E_iff hu1E hu1O hξT hξ2).2 hΩξ
  have hXu2 := (hT _ hX1).1 hXT
  refine ⟨hXT, hXE, hu1X', hXu2, ?_⟩
  unfold xjX
  rw [hPar]
  obtain ⟨-, hiff⟩ := Par_comps_eq hu1E hu1O hξT (hu1O.trans_le hΩξ).le
  refine (hiff l).2 ⟨l, hlc, ?_⟩
  rw [Par_lt hu1E hu1O hlu1]; exact Finset.mem_singleton_self l

/-- **Every point `y` of an inner segment `[υ_{λ+h}, υ_{λ+h+1}) ⊂ Ω₁` with `e(y) = X′` has a parameter `≥ υ_λ`**
(`Ww.ww_par_X` with the witness `X′`). -/
theorem xj_par_X (k : ℕ) {h y : Ordinal.{0}} (h0 : 0 < h)
    (hτ1 : upsilon (Nc.ncL S (k : Ordinal.{0}) + h) < Om1)
    (h1 : upsilon (Nc.ncL S (k : Ordinal.{0}) + h) ≤ y)
    (h2 : y < upsilon (succ (Nc.ncL S (k : Ordinal.{0}) + h))) (hy0 : y ≠ 0) (he : cdExp y = xjX S k) :
    ∃ p ∈ Par (upsilon (Nc.ncL S (k : Ordinal.{0}) + h)) y, upsilon (Nc.ncL S (k : Ordinal.{0})) ≤ p := by
  obtain ⟨hl0, -, -, -, -, -, -, -, -⟩ := Vr.vr_facts (S := S) k
  obtain ⟨-, -, hlu1, hlfix, -, -⟩ := Ww.ww_seg (S := S) k
  obtain ⟨-, hXE, hu1X, hXu2, hlP⟩ := xjX_spec (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  set X := xjX S k with hXdef
  set τ := upsilon (l + h) with hτdef
  have hm := upsilon_normal.strictMono
  have hτP : UpsPt τ := upsPt_upsilon (hl0.trans_le le_self_add)
  have hτE : InE τ := upsPt_inE hτP
  obtain ⟨m, hn, hT⟩ := exists_next hτP hτ1
  have hmτ : m = upsilon (succ (l + h)) := hn.unique (upsilon_isNext (l + h))
  have hnO : m < Om1 := next_lt_Om1 hn (Or.inr hτP) hτ1
  have hyT : y ∈ Tset τ := (hT y ((hmτ ▸ h2).trans hnO)).2 (hmτ ▸ h2)
  obtain ⟨-, hiff⟩ := Par_comps_eq hτE hτ1 hyT h1
  have hc : X ∈ comps y := by
    have := Ww.ww_comps_exp hy0; rwa [he, hXE] at this
  rcases lt_or_ge X τ with hXτ | hτX
  · refine ⟨X, (hiff X).2 ⟨X, hc, ?_⟩, ?_⟩
    · rw [Par_lt hτE hτ1 hXτ]; exact Finset.mem_singleton_self X
    · rw [hlfix]; exact (hlu1.trans hu1X).le
  · have hh2 : l + h < l + 2 := hm.lt_iff_lt.1 (hτX.trans_lt hXu2)
    have hh : h = 1 := by
      have h' := (add_lt_add_iff_left l).1 hh2
      have : h ≤ 1 := by
        rw [← one_add_one_eq_two] at h'; exact Order.lt_add_one_iff.1 h'
      exact le_antisymm this (one_le_iff_pos.2 h0)
    refine ⟨l, (hiff l).2 ⟨X, hc, ?_⟩, by rw [hlfix]⟩
    have : τ = upsilon (l + 1) := by rw [hτdef, hh]
    rw [this]; exact hlP

/-- **No `ξ ∈ T^{u₁}`, `ξ < B₂`, has `ϑ^{u₁}(ξ) = X′`** (`Ww.wwVt_ne` with the level `M₀`). -/
theorem xjVt_ne_low (k : ℕ) : ∀ ξ, ξ ∈ Tset (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) → ξ < Uc.ucB →
    vt (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) ξ ≠ xjX S k := by
  intro ξ hξT hξB heq
  obtain ⟨hP, hu1O, hlu1, -, -, -⟩ := Ww.ww_seg (S := S) k
  obtain ⟨-, hXE, hu1X, -, -⟩ := xjX_spec (S := S) k
  obtain ⟨-, -, hΩξ0, -, hMT⟩ := xj_arg (S := S) k
  obtain ⟨-, -, -, hu12, -, -, -, -, -⟩ := Vr.vr_facts (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  set u1 := upsilon (l + 1) with hu1def
  have hu1E : InE u1 := upsPt_inE hP
  have hξ2 : ξ < OmTwo := hξB.trans Uc.ucB_lt_Om2
  by_cases hΩ : Om1 ≤ ξ
  · obtain ⟨hdec, hM'B, hη'O, hdT, hη'T, hd_lt, hη_lt⟩ := Ww.ww_lev (S := S) k hξT hΩ hξB
    rw [heq] at hd_lt hη_lt
    have hlO : l < Om1 := hlu1.trans hu1O
    have hlT : l ∈ Tset u1 := Ww.ww_mem k (hlu1.trans hu12)
    have hM1 : Om1 ≤ Uc.ucB + l := Uc.ucB_gt.le.trans le_self_add
    have harg : Om1 * (ξ / Om1) + ξ % Om1 < Om1 * (Uc.ucB + l) + l := by
      rw [hdec]
      exact hξB.trans_le ((le_self_add.trans (Xe.xe_le_mul _)).trans le_self_add)
    have hlt := vdVt_lt hu1E hu1O hM1 (hM'B.le.trans le_self_add) (Vd.vdDatIn_uc hM'B hdT) hη'T hη'O hMT hlT hlO
      harg
    have hX : vt u1 (Om1 * (Uc.ucB + l) + l) = xjX S k := rfl
    rw [hX, hdec, heq] at hlt
    exact lt_irrefl _ (hlt (Vd.vdLtIn_uc hM'B hd_lt) hη_lt)
  · have h := (vt_E_iff hu1E hu1O hξT hξ2).1 (by rw [heq]; exact ⟨hu1X, hXE⟩)
    exact hΩ h

/-- A reading of the data below `c ≤ λ` gives the data in `T^{u₁}`. -/
theorem xj_datIn (k : ℕ) {M c : Ordinal.{0}} (hc : c ≤ Nc.ncL S (k : Ordinal.{0})) (h : Vd.VdLtIn M c) :
    Vd.VdDatIn (· ∈ Tset (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1))) M := by
  obtain ⟨-, -, hlu1, -, -, -⟩ := Ww.ww_seg (S := S) k
  obtain ⟨-, -, -, hu12, -, -, -, -, -⟩ := Vr.vr_facts (S := S) k
  have hcu2 : c < upsilon (Nc.ncL S (k : Ordinal.{0}) + 2) := hc.trans_lt (hlu1.trans hu12)
  rcases h with ⟨hMB, hd⟩ | ⟨S', hB, hθ, q, -, hqc, hd⟩
  · exact Vd.vdDatIn_uc hMB (Ww.ww_mem k (hd.trans hcu2))
  · exact Vd.vdDatIn_th (S := S') hB hθ (Ww.ww_mem k ((hd.trans_le hqc).trans hcu2))

/-- `Ω₁·M + η < Ω₁·M' + η'` with `η' < Ω₁` gives `M ≤ M'`. -/
theorem xj_div_le {M η M' η' : Ordinal.{0}} (hη' : η' < Om1) (h : Om1 * M + η < Om1 * M' + η') : M ≤ M' := by
  by_contra hlt
  push Not at hlt
  have h1 : Om1 * (M' + 1) ≤ Om1 * M := mul_le_mul_left' (Order.add_one_le_of_lt hlt) _
  rw [mul_add, mul_one] at h1
  have h2 : Om1 * M' + η' < Om1 * M' + Om1 := (add_lt_add_iff_left _).2 hη'
  exact absurd (h.trans (h2.trans_le (h1.trans le_self_add))) (lt_irrefl _)

/-- **No `ϑ^{u₁}(Ω₁·M + η)` with a level `M` whose data lie below `c ≤ λ` is `X′`** ([W07a] Lemma 3.30 through
`R2.vdVt_lt` in both directions; at equal arguments `M = M₀`, excluded by `xj_M0_noLt`). -/
theorem xjVt_ne_lev (k : ℕ) {M η c : Ordinal.{0}} (hc : c ≤ Nc.ncL S (k : Ordinal.{0})) (h1M : 1 ≤ M)
    (hML : Vd.VdLtIn M c) (hη1 : η < Om1) (hξT : Om1 * M + η ∈ Tset (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1))) :
    vt (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) (Om1 * M + η) ≠ xjX S k := by
  intro heq
  obtain ⟨hP, hu1O, hlu1, hlfix, -, -⟩ := Ww.ww_seg (S := S) k
  obtain ⟨hl0, -, -, hu12, -, -, -, -, -⟩ := Vr.vr_facts (S := S) k
  obtain ⟨-, hXE, hu1X, -, -⟩ := xjX_spec (S := S) k
  obtain ⟨-, -, -, -, hM0T⟩ := xj_arg (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  set u1 := upsilon (l + 1) with hu1def
  have hu1E : InE u1 := upsPt_inE hP
  have hlO : l < Om1 := hlu1.trans hu1O
  have hlT : l ∈ Tset u1 := Ww.ww_mem k (hlu1.trans hu12)
  have hlE : InE l := hlfix ▸ upsPt_inE (upsPt_upsilon hl0)
  have hX : vt u1 (Om1 * (Uc.ucB + l) + l) = xjX S k := rfl
  have hMT : Vd.VdDatIn (· ∈ Tset u1) M := xj_datIn k hc hML
  have hηT : η ∈ Tset u1 := by
    have hd : ω ^ Om1 ∣ Om1 * M := by rw [Rj.rj_Om1_inE]; exact dvd_mul_right _ _
    have hlt : η < ω ^ Om1 := by rw [Rj.rj_Om1_inE]; exact hη1
    have hu1ξ : u1 ≤ Om1 * M + η :=
      (hu1O.le.trans (Ordinal.le_mul_left Om1 (Order.one_le_iff_pos.1 h1M))).trans le_self_add
    refine Si.siT_of_comps hu1E hu1O η fun p hp => ?_
    exact (Par_comps_eq hu1E hu1O hξT hu1ξ).1 p (Rj.rj_comps_add (Om1 * M) hd η hlt p hp)
  have hBl : Bases l u1 := ⟨hlE, hu1E, hlu1, hu1O⟩
  have hXL : Xe.XeLev l M := Xe.xeLev_of_ltIn hlE h1M (Xb.xb_ltIn_mono hML hc)
  have hηv : η < vt u1 (Om1 * M + η) := Xe.xeLt_vt_self hBl hXL hηT hη1
  have hM1 : Om1 ≤ Uc.ucB + l := Uc.ucB_gt.le.trans le_self_add
  rcases lt_trichotomy (Om1 * M + η) (Om1 * (Uc.ucB + l) + l) with hlt | heq' | hgt
  · have hle := xj_div_le hlO hlt
    have hd' : Vd.VdLtIn M (vt u1 (Om1 * (Uc.ucB + l) + l)) :=
      Xb.xb_ltIn_mono hML (hc.trans ((hlu1.trans hu1X).le.trans (le_of_eq (hX.symm))))
    have hηv' : η < vt u1 (Om1 * (Uc.ucB + l) + l) := by rw [hX, ← heq]; exact hηv
    have := vdVt_lt hu1E hu1O hM1 hle hMT hηT hη1 hM0T hlT hlO hlt hd' hηv'
    rw [heq, hX] at this
    exact lt_irrefl _ this
  · have hMe : M = Uc.ucB + l := by
      have e1 := congrArg (· / Om1) heq'
      simp only at e1
      rwa [Ordinal.mul_add_div _ Rj.rj_Om1_pos.ne', Ordinal.mul_add_div _ Rj.rj_Om1_pos.ne',
        Ordinal.div_eq_zero_of_lt hη1, Ordinal.div_eq_zero_of_lt hlO, add_zero, add_zero] at e1
    rw [hMe] at hML
    exact xj_M0_noLt k hc hML
  · have hle := xj_div_le hη1 hgt
    have hM1' : Om1 ≤ M := hM1.trans hle
    have hd' : Vd.VdLtIn (Uc.ucB + l) (vt u1 (Om1 * M + η)) :=
      Or.inr ⟨S, le_self_add, xj_M0_th k, u1, xj_u1_SC k, by rw [heq]; exact hu1X.le, xj_M0_dat k⟩
    have hlv : l < vt u1 (Om1 * M + η) := by rw [heq]; exact hlu1.trans hu1X
    have := vdVt_lt hu1E hu1O hM1' hle hM0T hlT hlO hMT hηT hη1 hgt hd' hlv
    rw [heq, hX] at this
    exact lt_irrefl _ this

section Last

variable {l β X c : Ordinal.{0}} (hl0 : 0 < l) (hb1 : upsilon (l + β) ≤ Om1) (hX : InE X)
  (hX1 : upsilon (l + 1) < X) (hX2 : X < upsilon (l + 2))
include hl0 hb1 hX hX1 hX2

/-- **THE LAST-TERM LEMMA for forms with constant `ϑ`-levels** (`Wu.wuLast` with `ϑ`-nodes): if a well-formed
`Ww.WwE` over `υ_λ` with `Xb.XbCL c` has value with last term `X` (an `ε`-number in `(u₁, u₂)`), then an `sg`-node
`y` with all parameters below `υ_λ` has last term `X`, or `X = ϑ^{u₁}(ξ)` with `ξ < B₂`, or `X = ϑ^{u₁}(Ω₁·M + η)`
with `1 ≤ M` and a reading of the data of `M` below `c`. -/
theorem xjLast : ∀ E : Ww.WwE, Ww.WwWF l β E → Xb.XbCL c E → Ww.wwVal l E ≠ 0 → cdExp (Ww.wwVal l E) = X →
    (∃ h y, 0 < h ∧ h < β ∧ upsilon (l + h) ≤ y ∧ y < upsilon (succ (l + h)) ∧
        (∀ p ∈ Par (upsilon (l + h)) y, p < upsilon l) ∧ y ≠ 0 ∧ cdExp y = X) ∨
      (∃ ξ, ξ ∈ Tset (upsilon (l + 1)) ∧ ξ < Uc.ucB ∧ vt (upsilon (l + 1)) ξ = X) ∨
      ∃ M η, 1 ≤ M ∧ Vd.VdLtIn M c ∧ η < Om1 ∧ Om1 * M + η ∈ Tset (upsilon (l + 1)) ∧
        vt (upsilon (l + 1)) (Om1 * M + η) = X := by
  intro E
  induction E with
  | old E =>
    intro hw _ h0 he
    rcases Wu.wuLast hl0 hb1 hX hX1 hX2 E hw h0 he with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  | th h M e _ =>
    intro hw hc h0 he
    obtain ⟨hh0, hh, -, he1, hmem, hlt2, -, -⟩ := hw
    obtain ⟨e1, e2⟩ := Wu.wuVt hl0 hb1 hX hX2 hh0 hh hmem hlt2 he
    exact Or.inr (Or.inr ⟨M, Ww.wwVal l e, hc.1, hc.2.1, he1, e1 ▸ hmem, e2⟩)
  | add s t ihs iht =>
    intro hw hc h0 he
    by_cases ht : Ww.wwVal l t = 0
    · have e : Ww.wwVal l (.add s t) = Ww.wwVal l s := by
        show Ww.wwVal l s + Ww.wwVal l t = _; rw [ht, add_zero]
      exact ihs hw.1 hc.1 (by rw [← e]; exact h0) (by rw [← e]; exact he)
    · have e : cdExp (Ww.wwVal l (.add s t)) = cdExp (Ww.wwVal l t) := Cp.cpExp_add _ ht
      exact iht hw.2 hc.2 ht (by rw [← e]; exact he)

end Last

/-- **A form with constant `ϑ`-levels at an `ε`-offset `X ∈ (u₁, u₂)`** ends in an `sg`-node with parameters below
`υ_λ`, in `ϑ^{u₁}(ξ)` with `ξ < B₂`, or in `ϑ^{u₁}(Ω₁·M + η)` with the data of `M` below some `c < υ_λ`. -/
theorem xjForm_X (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {X β : Ordinal.{0}} (hXE : InE X)
    (hX1 : upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) < X) (hX2 : X < upsilon (Nc.ncL S (k : Ordinal.{0}) + 2))
    (hb1 : upsilon (Nc.ncL S (k : Ordinal.{0}) + β) ≤ Om1) (hF : Xb.XbForm S (Nc.ncL S (k : Ordinal.{0})) β X) :
    (∃ h y, 0 < h ∧ h < β ∧ upsilon (Nc.ncL S (k : Ordinal.{0}) + h) ≤ y ∧
        y < upsilon (succ (Nc.ncL S (k : Ordinal.{0}) + h)) ∧
        (∀ p ∈ Par (upsilon (Nc.ncL S (k : Ordinal.{0}) + h)) y, p < upsilon (Nc.ncL S (k : Ordinal.{0}))) ∧
        y ≠ 0 ∧ cdExp y = X) ∨
      (∃ ξ, ξ ∈ Tset (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) ∧ ξ < Uc.ucB ∧
        vt (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) ξ = X) ∨
      ∃ c M η, c < upsilon (Nc.ncL S (k : Ordinal.{0})) ∧ 1 ≤ M ∧ Vd.VdLtIn M c ∧ η < Om1 ∧
        Om1 * M + η ∈ Tset (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) ∧
        vt (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) (Om1 * M + η) = X := by
  obtain ⟨hl0, -, -, -, -, -, -, -, -⟩ := Vr.vr_facts (S := S) k
  obtain ⟨E, c, hc, hW, hCL, hv⟩ := hF
  have hX0 : X ≠ 0 := (InE.pos hXE).ne'
  rw [Wu.wuR_X k hν hXE hX2] at hv
  have hv0 : Ww.wwVal (Nc.ncL S (k : Ordinal.{0})) E ≠ 0 := by
    rw [hv]; exact (lt_of_lt_of_le (InE.pos hXE) le_add_self).ne'
  have he : cdExp (Ww.wwVal (Nc.ncL S (k : Ordinal.{0})) E) = X := by
    rw [hv, Cp.cpExp_add _ hX0, Te.te_cdExp_E hXE]
  rcases xjLast hl0 hb1 hXE hX1 hX2 E hW hCL hv0 he with h | h | ⟨M, η, h1, h2, h3, h4, h5⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨c, M, η, hc, h1, h2, h3, h4, h5⟩)

/-- **REFUTATION of the supply hypothesis of `Xb.xbRoad` at `L(k)`**: `L(k+1) ≤ ν_C ⇒ ¬ Xb.XbVisGen` at `L(k)` (at
the window `ν = λ + X′ + ω²` the forms clause at the offset `X′` fails: no big reach, `Wq.wqBigTop`; no form,
`xjForm_X`, `xj_par_X`, `xjVt_ne_low`, `xjVt_ne_lev`). -/
theorem xjVis_ref (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) :
    ¬ Xb.XbVisGen S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0})))) := by
  intro hV
  have hm := upsilon_normal.strictMono
  obtain ⟨-, hXE, hX1, hX2, -⟩ := xjX_spec (S := S) k
  obtain ⟨-, -, -, hlfix, -, -⟩ := Ww.ww_seg (S := S) k
  set X := xjX S k with hXdef
  obtain ⟨-, e, hR, hc, hb, hlν, hcov, hiso⟩ := Wu.wuWin k hν hXE hX1 hX2
  obtain ⟨-, -, -, -, -, -, hL1O, -, -⟩ := Vr.vr_facts (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  obtain ⟨β, e1, e2, hGen⟩ := hV (l + X + ω ^ 2) hR hc hb hlν hcov hiso
  have hνβ : l + X + ω ^ 2 < l + β := hm.lt_iff_lt.1 e1
  have hXβ' : X + ω ^ 2 < β := by rw [add_assoc] at hνβ; exact (add_lt_add_iff_left l).1 hνβ
  have hXβ : X < β := (le_self_add).trans_lt hXβ'
  have hωX : ω ≤ X := Vo.vo_omega_le hXE (InE.pos hXE)
  have h2c : (2 : Ordinal.{0}) ≤ X := ((natCast_lt_omega0 2).trans_le hωX).le
  have hω2g : ω ^ 2 ∣ X := by
    have h := Vo.vo_e2 ▸ opow_dvd_opow ω h2c
    rwa [hXE] at h
  have hb1 : upsilon (l + β) ≤ Om1 := e2.trans hL1O.le
  rcases hGen.2.1 X (InE.pos hXE) hXβ hω2g with hbig | hF
  · have hlt := Wq.wqBigTop (S := S) k hν (InE.pos hXE) hω2g hX2
    have hle : upsilon (l + (X + ω ^ 2)) ≤ upsilon (l + β) := hm.monotone ((add_le_add_iff_left l).2 hXβ'.le)
    exact absurd (hbig.trans_lt (hlt.trans_le hle)) (lt_irrefl _)
  · rcases xjForm_X k hν hXE hX1 hX2 hb1 hF with ⟨h, y, h0, hhβ, h1, h2, h3, h4, h5⟩ | ⟨ξ, hξ, hξB, hξe⟩ |
        ⟨c, M, η, hcl, h1M, hML, hη1, hξT, hξe⟩
    · have hτ1 : upsilon (l + h) < Om1 := (hm ((add_lt_add_iff_left l).2 hhβ)).trans_le hb1
      obtain ⟨p, hp, hpl⟩ := xj_par_X k h0 hτ1 h1 h2 h4 h5
      exact absurd (h3 p hp) (not_lt.2 hpl)
    · exact xjVt_ne_low k ξ hξ hξB hξe
    · rw [hlfix] at hcl
      exact xjVt_ne_lev k hcl.le h1M hML hη1 hξT hξe

/-- **`h0` of `Xb.xbRoad` and `L(1) ≤ ν_C` exclude each other** (no hypothesis). -/
theorem xjRoad_vac :
    ¬ ((∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
        Xb.XbVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0)))) ∧
      Nc.ncL S 1 ≤ nuC) := by
  rintro ⟨h0, hν⟩
  have hν' : Nc.ncL S ((0 + 1 : ℕ) : Ordinal.{0}) ≤ nuC := by simpa using hν
  apply xjVis_ref 0 hν'
  have e : Nc.ncL S ((0 : ℕ) : Ordinal.{0}) = upsilon (Nc.ncL S ((0 : ℕ) : Ordinal.{0})) := (Te.teUps_L 0).symm
  have h := h0 (Nc.ncL S ((0 : ℕ) : Ordinal.{0})) (Te.teRst_L 0) (by simpa using e)
  simpa using h

/-- **THE HYPOTHESES OF `xjRoad` ARE JOINTLY FALSE**: the road proves `L(ω) ≤ ν_C`, hence `L(1) ≤ ν_C`, which refutes
its own supply hypothesis `h0` (`xjRoad_vac`).  So `xjRoad` is VACUOUS. -/
theorem xjRoad_false
    (hUH : ∀ l, CdRange S l → Xf.XfPast S l → CdUpper S l)
    (hLH : ∀ l, CdRange S l → Xf.XfPast S l → CdLower S l)
    (hVH : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Xf.XfPast S l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → Xf.XfPast S l → CdCapV S l)
    (hT : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      Xb.XbVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      Xb.XbVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    False := by
  have hR := xjRoad hUH hLH hVH hVt hT hF h0 hn
  have hLw : Nc.ncL S ω ≤ nuC := hR.2.2.2.2.2.1
  have h1 : Nc.ncL S 1 ≤ nuC := by
    have := Rp.rpL_lt (S := S) 1
    exact (by simpa using this : Nc.ncL S 1 < Nc.ncL S ω).le.trans hLw
  exact xjRoad_vac ⟨h0, h1⟩

/-- **The hypotheses of `Xb.xbRoad` are jointly false** (with its own `hS`; this proof does not use `R2.xeVt_trL`). -/
theorem xbRoad_false
    (hUH : ∀ l, CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdUpper S l)
    (hLH : ∀ l, CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdLower S l)
    (hVH : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdCapV S l)
    (hT : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S)
    (hS : Xb.XbShift S)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      Xb.XbVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      Xb.XbVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    False := by
  have hR := Xb.xbRoad hUH hLH hVH hVt hT hF hS h0 hn
  have hLw : Nc.ncL S ω ≤ nuC := hR.2.2.2.2.2.1
  have h1 : Nc.ncL S 1 ≤ nuC := by
    have := Rp.rpL_lt (S := S) 1
    exact (by simpa using this : Nc.ncL S 1 < Nc.ncL S ω).le.trans hLw
  exact xjRoad_vac ⟨h0, h1⟩

/-- **Every high-window forms clause with constant `ϑ`-levels fails** (only `L(k+1) ≤ ν_C`): the `ε`-number `X′ ∈
(u₁, u₂)`, `X′ ≥ ε_{u₁+1}`, `X′ ≠ ω^{ω^{u₁+1}}`, whose window has no big reach and no form `Xb.XbForm` at the offset
`X′` (the negation of the skeleton leaf `skFormHighX` at the window `λ + X′ + ω²`). -/
theorem xjFormHighX_fail (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) :
    ∃ X, InE X ∧ upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) < X ∧ X < upsilon (Nc.ncL S (k : Ordinal.{0}) + 2) ∧
      eN (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) ≤ X ∧
      X ≠ ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) ∧
      ¬ (upsilon (Nc.ncL S (k : Ordinal.{0}) + (Nc.ncL S (k : Ordinal.{0}) + X + ω ^ 2 - Nc.ncL S (k : Ordinal.{0}) +
          ω ^ 2)) ≤ cdR S (Nc.ncL S (k : Ordinal.{0}) + X) ∨
        Xb.XbForm S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S (k : Ordinal.{0}) + X + ω ^ 2 -
          Nc.ncL S (k : Ordinal.{0}) + ω ^ 2) X) := by
  have hm := upsilon_normal.strictMono
  obtain ⟨-, hXE, hX1, hX2, -⟩ := xjX_spec (S := S) k
  obtain ⟨-, -, -, hlfix, -, -⟩ := Ww.ww_seg (S := S) k
  obtain ⟨hl0, -, -, -, hu2L1, hL1E, hL1O, hbelow, -⟩ := Vr.vr_facts (S := S) k
  set X := xjX S k with hXdef
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  set u1 := upsilon (l + 1) with hu1def
  have e : l + X + ω ^ 2 - l + ω ^ 2 = X + ω ^ 2 + ω ^ 2 := by rw [add_assoc l, Ordinal.add_sub_cancel]
  have hωX : ω ≤ X := Vo.vo_omega_le hXE (InE.pos hXE)
  have h2c : (2 : Ordinal.{0}) ≤ X := ((natCast_lt_omega0 2).trans_le hωX).le
  have hω2g : ω ^ 2 ∣ X := by
    have h := Vo.vo_e2 ▸ opow_dvd_opow ω h2c
    rwa [hXE] at h
  have hω2X : ω ^ 2 < X := by rw [Vo.vo_e2]; exact hXE.opow_lt ((natCast_lt_omega0 2).trans_le hωX)
  have hβ1 : X + ω ^ 2 + ω ^ 2 < upsilon (l + 2) := by
    have hu2E : InE (upsilon (l + 2)) := upsPt_inE (upsPt_upsilon (hl0.trans_le le_self_add))
    exact hu2E.add_lt (hu2E.add_lt hX2 (hω2X.trans hX2)) (hω2X.trans hX2)
  have hlβ : l + (X + ω ^ 2 + ω ^ 2) < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) :=
    hL1E.add_lt (Te.teL_lt_succ k) (hβ1.trans hu2L1)
  have hb1 : upsilon (l + (X + ω ^ 2 + ω ^ 2)) ≤ Om1 := ((hbelow _ hlβ).trans hL1O).le
  have hXβ' : X + ω ^ 2 ≤ X + ω ^ 2 + ω ^ 2 := le_self_add
  refine ⟨X, hXE, hX1, hX2, eN_le hX1 hXE, ?_, ?_⟩
  · intro h
    have hinj : ∀ a b : Ordinal.{0}, ω ^ a = ω ^ b → a = b := fun a b hab =>
      le_antisymm ((opow_le_opow_iff_right one_lt_omega0).1 hab.le)
        ((opow_le_opow_iff_right one_lt_omega0).1 hab.ge)
    have h1 : ω ^ ω ^ ω ^ (u1 + 1) = ω ^ ω ^ (u1 + 1) := by
      have h' := hXE; rw [h] at h'; exact h'
    have h3 : ω ^ (u1 + 1) = u1 + 1 := hinj _ _ (hinj _ _ h1)
    have hL : IsSuccLimit (ω ^ (u1 + 1)) :=
      isSuccLimit_opow_left isSuccLimit_omega0 (lt_of_le_of_lt zero_le (lt_add_one u1)).ne'
    rw [h3] at hL
    have := hL.succ_lt (lt_add_one u1)
    rw [Order.succ_eq_add_one] at this
    exact lt_irrefl _ this
  · rw [e]
    rintro (hbig | hF)
    · have hlt := Wq.wqBigTop (S := S) k hν (InE.pos hXE) hω2g hX2
      have hle : upsilon (l + (X + ω ^ 2)) ≤ upsilon (l + (X + ω ^ 2 + ω ^ 2)) :=
        hm.monotone ((add_le_add_iff_left l).2 hXβ')
      exact absurd (hbig.trans_lt (hlt.trans_le hle)) (lt_irrefl _)
    · rcases xjForm_X k hν hXE hX1 hX2 hb1 hF with ⟨h, y, h0, hhβ, h1, h2, h3, h4, h5⟩ | ⟨ξ, hξ, hξB, hξe⟩ |
          ⟨c, M, η, hcl, h1M, hML, hη1, hξT, hξe⟩
      · have hτ1 : upsilon (l + h) < Om1 := (hm ((add_lt_add_iff_left l).2 hhβ)).trans_le hb1
        obtain ⟨p, hp, hpl⟩ := xj_par_X k h0 hτ1 h1 h2 h4 h5
        exact absurd (h3 p hp) (not_lt.2 hpl)
      · exact xjVt_ne_low k ξ hξ hξB hξe
      · rw [hlfix] at hcl
        exact xjVt_ne_lev k hcl.le h1M hML hη1 hξT hξe

end Googology.Trans.PoR.InaccPsi.R2.Xj
