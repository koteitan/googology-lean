import Googology.Trans.PoR.InaccPsi.R2.WuWin
import Googology.Trans.PoR.InaccPsi.R2.CitedVd
import Googology.Trans.PoR.InaccPsi.R2.CitedLv
import Googology.Trans.PoR.InaccPsi.R2.CitedLu
import Googology.Trans.PoR.InaccPsi.R2.RkArgT
import Googology.Trans.PoR.InaccPsi.R2.RjArg
import Googology.Trans.PoR.InaccPsi.R2.SiUnc
import Googology.Trans.PoR.InaccPsi.R2.GqLoc
import Googology.Trans.PoR.InaccPsi.R2.LqGam
import Googology.Trans.PoR.InaccPsi.R2.UoUc
import Googology.Trans.PoR.InaccPsi.R2.VdDat
import Googology.Trans.PoR.InaccPsi.R2.VdEq
import Googology.Trans.PoR.InaccPsi.R2.UfTop
import Googology.Trans.PoR.InaccPsi.R2.VdCit
import Googology.Trans.PoR.InaccPsi.R2.UcBH
import Googology.Trans.PoR.InaccPsi.R2.UiAgree
import Googology.Trans.PoR.InaccPsi.R2.WsZeta
import Googology.Trans.PoR.InaccPsi.R2.RpPair
import Googology.Trans.PoR.InaccPsi.R2.WfRoad

/-!
# The gap at every `L(k)`: the `ε`-number `X = ϑ^{u₁}(B₂ + υ_λ)` has no repaired form

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`λ = L(k) = υ_λ`, `u₁ = υ_{λ+1}`, `u₂ = υ_{λ+2}`, `B₂ = Uc.ucB = Ω₁·B₂`, `X = ϑ^{u₁}(B₂ + λ)`.

* `ww_B_dat` (the `K⁽⁰⁾`-datum of `B₂` lies below every strongly critical `q`), `ww_seg` (`T^{u₁} ∩ Ω₁ = u₂`);
* `wwX_spec` (**`X ∈ T^{u₁}` is an `ε`-number, `u₁ < X < u₂`, `λ ∈ Par^{u₁}(X)`**: `CitedVd.vdArg_mem` at the level
  `B₂`, `vt_E_iff`, `vt_memTwo`, `Par_comps_eq`);
* `wwVt_ne` (**no `ξ ∈ T^{u₁}`, `ξ < B₂`, has `ϑ^{u₁}(ξ) = X`**: `CitedVd.vdVt_lt` / `vdLevel_lt`, `CitedLu`,
  `CitedLv` at the levels below `Ω₁`, `vt_E_iff` below `Ω₁`);
* `ww_comps_exp` (`ω^{e(y)}` is an additive component of `y ≠ 0`), `ww_par_X` (**every segment point `y` with
  `e(y) = X` has the parameter `X` or `λ`, both `≥ υ_λ`**);
* `WwGap` (`Wu.WuGap` with the segment clause asked only where `υ_{λ+h} < Ω₁`, the only place `Par` is cited;
  `wuGap_ww`), `wwGap` (**`WwGap S k` for every `k`, UNCONDITIONAL**);
* `wwVis_ref` (**`L(k+1) ≤ ν_C ⇒ ¬ Wf.WfVisGen` at `L(k)`**), `wwRoad_vac` (`h0'` and `L(1) ≤ ν_C` exclude each
  other), `wwRoad_false` (**the hypotheses of `Wf.wfRoad` are jointly FALSE**), `wwRoadZ_false` (the same for the
  current road `Ws.wsRoadZ`).

No new axiom.  New definitions: `wwX` (an ordinal), `WwGap` (a statement).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ww

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-! ## The datum of `B₂` -/

/-- `B₂ = ψ_{Ω₂}(φ(1, Ω₂ + 1))` lies in every `K⁽⁰⁾_q`. -/
theorem ww_B_K (q : Ordinal.{0}) : Ul.UlK S 0 q Uc.ucB := by
  rw [← Uc.uc_psiE_eq_B (S := S), Uc.uc_E_eq_veblen]
  refine Uo.uoPsi2 (Ul.UlK.phi Ul.UlK.one (Ul.UlK.add ?_ Ul.UlK.one))
  rw [Uc.uc_Om2_eq]; exact Uo.uoW2

/-- **The `K⁽⁰⁾`-datum of `B₂` lies below every strongly critical `q`.** -/
theorem ww_B_dat {q : Ordinal.{0}} (hq : SC q) : Vd.vdD S 0 Uc.ucB < q := by
  rw [Vd.vdD_eq]; exact (Ul.ul_vis hq).2 (ww_B_K q)

/-! ## The segment of `u₁` -/

/-- **The segment of `u₁ = υ_{λ+1}`**: `u₁` is a countable `υ`-point above `λ = υ_λ`, and `T^{u₁} ∩ Ω₁ = u₂`. -/
theorem ww_seg (k : ℕ) :
    UpsPt (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) ∧ upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) < Om1 ∧
    Nc.ncL S (k : Ordinal.{0}) < upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) ∧
    upsilon (Nc.ncL S (k : Ordinal.{0})) = Nc.ncL S (k : Ordinal.{0}) ∧
    upsilon (Nc.ncL S (k : Ordinal.{0}) + 2) < Om1 ∧
    ∀ a, a < Om1 → (a ∈ Tset (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) ↔
      a < upsilon (Nc.ncL S (k : Ordinal.{0}) + 2)) := by
  obtain ⟨hl0, -, -, hu12, hu2L1, -, hL1O, -, -⟩ := Vr.vr_facts (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  have hm := upsilon_normal.strictMono
  have hlfix : upsilon l = l := Te.teUps_L k
  have hP : UpsPt (upsilon (l + 1)) := upsPt_upsilon (hl0.trans_le le_self_add)
  have hu1O : upsilon (l + 1) < Om1 := hu12.trans (hu2L1.trans hL1O)
  obtain ⟨m, hn, hT⟩ := exists_next hP hu1O
  have hn' : IsNext (upsilon (l + 1)) (upsilon (l + 2)) := by
    have h := upsilon_isNext (l + 1)
    rwa [succ_eq_add_one, add_assoc, one_add_one_eq_two] at h
  have hm2 : m = upsilon (l + 2) := hn.unique hn'
  refine ⟨hP, hu1O, ?_, hlfix, hu2L1.trans hL1O, fun a ha => hm2 ▸ hT a ha⟩
  have := hm (lt_add_one l); rwa [hlfix] at this

/-- Every ordinal below `u₂` lies in `T^{u₁}`. -/
theorem ww_mem (k : ℕ) {a : Ordinal.{0}} (ha : a < upsilon (Nc.ncL S (k : Ordinal.{0}) + 2)) :
    a ∈ Tset (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) := by
  obtain ⟨-, -, -, -, hu2O, hT⟩ := ww_seg (S := S) k
  exact (hT a (ha.trans hu2O)).2 ha

/-! ## The witness `X = ϑ^{u₁}(B₂ + λ)` -/

/-- **The witness**: `X = ϑ^{u₁}(B₂ + λ)`. -/
noncomputable def wwX (S : InaccSeq.{0}) (k : ℕ) : Ordinal.{0} :=
  vt (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) (Uc.ucB + Nc.ncL S (k : Ordinal.{0}))

theorem ww_Om2_E : InE (OmTwo : Ordinal.{0}) := Uc.uc_Om2_opow_self

/-- The argument `B₂ + λ` lies in `T^{u₁} ∩ Ω₂` above `Ω₁`, and `λ` is one of its additive components. -/
theorem ww_arg (k : ℕ) :
    Uc.ucB + Nc.ncL S (k : Ordinal.{0}) ∈ Tset (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) ∧
    Uc.ucB + Nc.ncL S (k : Ordinal.{0}) < OmTwo ∧ Om1 ≤ Uc.ucB + Nc.ncL S (k : Ordinal.{0}) ∧
    Nc.ncL S (k : Ordinal.{0}) ∈ comps (Uc.ucB + Nc.ncL S (k : Ordinal.{0})) := by
  obtain ⟨hP, hu1O, hlu1, hlfix, -, -⟩ := ww_seg (S := S) k
  obtain ⟨hl0, -, -, hu12, -, -, -, -, -⟩ := Vr.vr_facts (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  set u1 := upsilon (l + 1) with hu1def
  have hu1E : InE u1 := upsPt_inE hP
  have hlO : l < Om1 := hlu1.trans hu1O
  have hlT : l ∈ Tset u1 := ww_mem k (hlu1.trans hu12)
  have hγ : gamma 0 ≤ u1 := Gq.gq_gam_le_ups S hP
  have hdT : Vd.vdD S 0 Uc.ucB ∈ Tset u1 :=
    ww_mem k ((ww_B_dat (S := S) (Lq.lq_gamma_SC 0)).trans_le (hγ.trans hu12.le))
  have hMT : Vd.VdDatIn (· ∈ Tset u1) Uc.ucB := Vd.vdDatIn_th (S := S) le_rfl Vd.vd_B_lt_th hdT
  have hmem := vdArg_mem hu1E hu1O Uc.ucB_gt.le hMT hlT hlO
  rw [Uf.uf_Om1_mul_B] at hmem
  refine ⟨hmem, ww_Om2_E.add_lt Uc.ucB_lt_Om2 (hlO.trans tqc_Om1_lt_OmTwo), Uc.ucB_gt.le.trans le_self_add, ?_⟩
  have hlE : InE l := hlfix ▸ upsPt_inE (upsPt_upsilon hl0)
  have hd : ω ^ Om1 ∣ Uc.ucB := by
    rw [Rj.rj_Om1_inE]; exact ⟨Uc.ucB, Uf.uf_Om1_mul_B.symm⟩
  have hlt : l < ω ^ Om1 := by rw [Rj.rj_Om1_inE]; exact hlO
  refine Rj.rj_comps_add Uc.ucB hd l hlt l ?_
  have : comps l = [l] := by
    have h := comps_opow l; rwa [hlE] at h
  rw [this]; exact List.mem_singleton_self l

/-- **The witness is an `ε`-number of `T^{u₁}` in `(u₁, u₂)` with the parameter `λ`.** -/
theorem wwX_spec (k : ℕ) :
    wwX S k ∈ Tset (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) ∧ InE (wwX S k) ∧
    upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) < wwX S k ∧ wwX S k < upsilon (Nc.ncL S (k : Ordinal.{0}) + 2) ∧
    Nc.ncL S (k : Ordinal.{0}) ∈ Par (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) (wwX S k) := by
  obtain ⟨hP, hu1O, hlu1, -, hu2O, hT⟩ := ww_seg (S := S) k
  obtain ⟨hξT, hξ2, hΩξ, hlc⟩ := ww_arg (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  set u1 := upsilon (l + 1) with hu1def
  have hu1E : InE u1 := upsPt_inE hP
  obtain ⟨hXT, hu1X, hX1, -, hPar⟩ := vt_memTwo hu1E hu1O hξT hξ2
  obtain ⟨hu1X', hXE⟩ := (vt_E_iff hu1E hu1O hξT hξ2).2 hΩξ
  have hXu2 := (hT _ hX1).1 hXT
  refine ⟨hXT, hXE, hu1X', hXu2, ?_⟩
  unfold wwX
  rw [hPar]
  obtain ⟨-, hiff⟩ := Par_comps_eq hu1E hu1O hξT (hu1O.trans_le hΩξ).le
  refine (hiff l).2 ⟨l, hlc, ?_⟩
  rw [Par_lt hu1E hu1O hlu1]; exact Finset.mem_singleton_self l

/-! ## No `ϑ^{u₁}(ξ)` with `ξ < B₂` is the witness -/

/-- **The data of a level below `B₂` lie below its `ϑ`-value**: for `ξ = Ω₁·M' + η' ∈ T^{u₁}`, `Ω₁ ≤ ξ < B₂`,
`ucDat M'` and `η'` lie in `T^{u₁}` and below `ϑ^{u₁}(ξ)`. -/
theorem ww_lev (k : ℕ) {ξ : Ordinal.{0}} (hξT : ξ ∈ Tset (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)))
    (hΩ : Om1 ≤ ξ) (hξB : ξ < Uc.ucB) :
    Om1 * (ξ / Om1) + ξ % Om1 = ξ ∧ ξ / Om1 < Uc.ucB ∧ ξ % Om1 < Om1 ∧
    Uc.ucDat (ξ / Om1) ∈ Tset (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) ∧
    ξ % Om1 ∈ Tset (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) ∧
    Uc.ucDat (ξ / Om1) < vt (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) ξ ∧
    ξ % Om1 < vt (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) ξ := by
  obtain ⟨hP, hu1O, -, -, -, -⟩ := ww_seg (S := S) k
  set u1 := upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) with hu1def
  have hu1E : InE u1 := upsPt_inE hP
  have hO0 : (Om1 : Ordinal.{0}) ≠ 0 := Rj.rj_Om1_inE.pos.ne'
  set M' := ξ / Om1 with hM'
  set η' := ξ % Om1 with hη'
  have hdec : Om1 * M' + η' = ξ := div_add_mod ξ Om1
  have hη'O : η' < Om1 := mod_lt ξ hO0
  have hM'ξ : M' ≤ ξ :=
    calc M' ≤ Om1 * M' := Ordinal.le_mul_right M' Rj.rj_Om1_inE.pos
      _ ≤ Om1 * M' + η' := le_self_add
      _ = ξ := hdec
  have hM'B : M' < Uc.ucB := hM'ξ.trans_lt hξB
  have hM'1 : 1 ≤ M' := by
    rw [Order.one_le_iff_ne_zero]
    intro h0
    rw [h0, mul_zero, zero_add] at hdec
    exact absurd (hdec ▸ hη'O) (not_lt.2 hΩ)
  have hu1ξ : u1 ≤ ξ := (hu1O.trans_le hΩ).le
  have hξ2 : ξ < OmTwo := hξB.trans Uc.ucB_lt_Om2
  -- `η' ∈ T^{u₁}`
  have hη'T : η' ∈ Tset u1 := by
    have hd : ω ^ Om1 ∣ Om1 * M' := by rw [Rj.rj_Om1_inE]; exact dvd_mul_right _ _
    have hlt : η' < ω ^ Om1 := by rw [Rj.rj_Om1_inE]; exact hη'O
    refine Si.siT_of_comps hu1E hu1O η' fun p hp => ?_
    have hp' := Rj.rj_comps_add (Om1 * M') hd η' hlt p hp
    rw [hdec] at hp'
    exact (Par_comps_eq hu1E hu1O hξT hu1ξ).1 p hp'
  have hvt := vt_memTwo hu1E hu1O hξT hξ2
  refine ⟨hdec, hM'B, hη'O, ?_, hη'T, ?_⟩
  · by_cases hM'Ω : Om1 ≤ M'
    · exact (vdArg_dat hu1E hu1O hM'Ω hη'O (by rw [hdec]; exact hξT)).1 hM'B
    · push Not at hM'Ω
      rw [Uc.ucDat_small hM'Ω]
      have h : Om1 * (Om1 * 0 + M') + η' ∈ Tset u1 := by rw [mul_zero, zero_add, hdec]; exact hξT
      exact (Rk.rkArg_T hu1E hu1O Rj.rj_Om1_inE.pos hM'Ω hη'O h).2
  · by_cases hM'Ω : Om1 ≤ M'
    · have hMT : Vd.VdDatIn (· ∈ Tset u1) M' :=
        Vd.vdDatIn_uc hM'B ((vdArg_dat hu1E hu1O hM'Ω hη'O (by rw [hdec]; exact hξT)).1 hM'B)
      have h := vdLevel_lt hu1E hu1O hM'Ω hMT hη'T hη'O
      rw [hdec] at h
      exact ⟨h.1.1 hM'B, h.2⟩
    · push Not at hM'Ω
      rw [Uc.ucDat_small hM'Ω]
      have h : Om1 * (Om1 * 0 + M') + η' ∈ Tset u1 := by rw [mul_zero, zero_add, hdec]; exact hξT
      have hM'T : M' ∈ Tset u1 := (Rk.rkArg_T hu1E hu1O Rj.rj_Om1_inE.pos hM'Ω hη'O h).2
      rcases lt_or_ge M' u1 with hlo | hhi
      · have h2 := luLt_vt_self hu1E hu1O hM'1 hlo hη'T hη'O
        rw [hdec] at h2
        exact ⟨hlo.trans_le hvt.2.1, h2⟩
      · have h2 := lvLevel_lt_vt hu1E hu1O hM'T hhi hM'Ω hη'T hη'O
        rw [hdec] at h2
        exact h2

/-- **No `ξ ∈ T^{u₁}`, `ξ < B₂`, has `ϑ^{u₁}(ξ) = X`.** -/
theorem wwVt_ne (k : ℕ) : ∀ ξ, ξ ∈ Tset (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) → ξ < Uc.ucB →
    vt (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) ξ ≠ wwX S k := by
  intro ξ hξT hξB heq
  obtain ⟨hP, hu1O, hlu1, -, -, -⟩ := ww_seg (S := S) k
  obtain ⟨-, hXE, hu1X, hXu2, -⟩ := wwX_spec (S := S) k
  obtain ⟨-, -, -, -, hu2L1, -, -, -, -⟩ := Vr.vr_facts (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  set u1 := upsilon (l + 1) with hu1def
  have hu1E : InE u1 := upsPt_inE hP
  have hξ2 : ξ < OmTwo := hξB.trans Uc.ucB_lt_Om2
  by_cases hΩ : Om1 ≤ ξ
  · obtain ⟨hdec, hM'B, hη'O, hdT, hη'T, hd_lt, hη_lt⟩ := ww_lev (S := S) k hξT hΩ hξB
    rw [heq] at hd_lt hη_lt
    -- the data of the witness level
    obtain ⟨hargT, -, -, -⟩ := ww_arg (S := S) k
    have hlO : l < Om1 := hlu1.trans hu1O
    obtain ⟨-, -, -, hu12, -, -, -, -, -⟩ := Vr.vr_facts (S := S) k
    have hlT : l ∈ Tset u1 := ww_mem k (hlu1.trans hu12)
    have hγ : gamma 0 ≤ u1 := Gq.gq_gam_le_ups S hP
    have hdBT : Vd.vdD S 0 Uc.ucB ∈ Tset u1 :=
      ww_mem k ((ww_B_dat (S := S) (Lq.lq_gamma_SC 0)).trans_le (hγ.trans hu12.le))
    have hMT : Vd.VdDatIn (· ∈ Tset u1) Uc.ucB := Vd.vdDatIn_th (S := S) le_rfl Vd.vd_B_lt_th hdBT
    have harg : Om1 * (ξ / Om1) + ξ % Om1 < Om1 * Uc.ucB + l := by
      rw [hdec, Uf.uf_Om1_mul_B]; exact hξB.trans_le le_self_add
    have hlt := vdVt_lt hu1E hu1O Uc.ucB_gt.le hM'B.le (Vd.vdDatIn_uc hM'B hdT) hη'T hη'O hMT hlT hlO harg
    -- the witness value is `ϑ^{u₁}(Ω₁·B₂ + λ)`
    have hX : vt u1 (Om1 * Uc.ucB + l) = wwX S k := by rw [Uf.uf_Om1_mul_B]; rfl
    rw [hX, hdec, heq] at hlt
    exact lt_irrefl _ (hlt (Vd.vdLtIn_uc hM'B hd_lt) hη_lt)
  · have h := (vt_E_iff hu1E hu1O hξT hξ2).1 (by rw [heq]; exact ⟨hu1X, hXE⟩)
    exact hΩ h

/-! ## The parameters of a segment point ending in the witness -/

/-- **`ω^{e(y)}` is an additive component of `y ≠ 0`.** -/
theorem ww_comps_exp {y : Ordinal.{0}} (hy : y ≠ 0) : ω ^ cdExp y ∈ comps y := by
  obtain ⟨η0, hη, hd⟩ := cdExp_decomp hy
  set E := cdExp y with hE
  obtain ⟨c, rfl⟩ := hd
  have hsplit : ω ^ E * c + ω ^ E = ω ^ (E + 1) * (c / ω) + ω ^ E * (c % ω + 1) := by
    conv_lhs => rw [← div_add_mod c ω]
    rw [mul_add, mul_add, mul_one, ← mul_assoc, ← opow_succ, succ_eq_add_one, add_assoc]
  have hmω : c % ω + 1 < ω := by
    have := mod_lt c omega0_ne_zero
    obtain ⟨n, hn⟩ := lt_omega0.1 this
    rw [hn]; exact_mod_cast natCast_lt_omega0 (n + 1)
  have hz : ω ^ E * (c % ω + 1) < ω ^ (E + 1) := by
    rw [opow_add, opow_one]; exact mul_lt_mul_of_pos_left hmω (opow_pos E omega0_pos)
  have hdv : ω ^ (E + 1) ∣ ω ^ (E + 1) * (c / ω) := dvd_mul_right _ _
  rw [hη, hsplit]
  refine Rj.rj_comps_add _ hdv _ hz _ ?_
  have hz0 : ω ^ E * (c % ω + 1) ≠ 0 :=
    mul_ne_zero (opow_pos E omega0_pos).ne' (add_pos_of_right zero_lt_one _).ne'
  rw [Si.si_comps_cons hz0]
  have hlog : log ω (ω ^ E * (c % ω + 1)) = E := by
    have hne : c % ω + 1 ≠ 0 := (add_pos_of_right zero_lt_one _).ne'
    have h := log_opow_mul_add one_lt_omega0 hne (opow_pos E omega0_pos)
    rw [add_zero] at h
    rw [h, Ordinal.log_eq_zero hmω, add_zero]
  rw [hlog]; exact List.mem_cons_self

/-- **Every point `y` of an inner segment `[υ_{λ+h}, υ_{λ+h+1}) ⊂ Ω₁` with `e(y) = X` has a parameter `≥ υ_λ`**: the
component `ω^X = X` is a parameter (`X < υ_{λ+h}`, `h ≥ 2`) or has the parameter `λ` (`h = 1`). -/
theorem ww_par_X (k : ℕ) {h y : Ordinal.{0}} (h0 : 0 < h)
    (hτ1 : upsilon (Nc.ncL S (k : Ordinal.{0}) + h) < Om1)
    (h1 : upsilon (Nc.ncL S (k : Ordinal.{0}) + h) ≤ y)
    (h2 : y < upsilon (succ (Nc.ncL S (k : Ordinal.{0}) + h))) (hy0 : y ≠ 0) (he : cdExp y = wwX S k) :
    ∃ p ∈ Par (upsilon (Nc.ncL S (k : Ordinal.{0}) + h)) y, upsilon (Nc.ncL S (k : Ordinal.{0})) ≤ p := by
  obtain ⟨hl0, -, -, -, -, -, -, -, -⟩ := Vr.vr_facts (S := S) k
  obtain ⟨-, -, hlu1, hlfix, -, -⟩ := ww_seg (S := S) k
  obtain ⟨-, hXE, hu1X, hXu2, hlP⟩ := wwX_spec (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  set X := wwX S k with hXdef
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
    have := ww_comps_exp hy0; rwa [he, hXE] at this
  rcases lt_or_ge X τ with hXτ | hτX
  · refine ⟨X, (hiff X).2 ⟨X, hc, ?_⟩, ?_⟩
    · rw [Par_lt hτE hτ1 hXτ]; exact Finset.mem_singleton_self X
    · rw [hlfix]; exact (hlu1.trans hu1X).le
  · -- `h = 1`
    have hh2 : l + h < l + 2 := hm.lt_iff_lt.1 (hτX.trans_lt hXu2)
    have hh : h = 1 := by
      have h' := (add_lt_add_iff_left l).1 hh2
      have : h ≤ 1 := by
        rw [← one_add_one_eq_two] at h'; exact Order.lt_add_one_iff.1 h'
      exact le_antisymm this (one_le_iff_pos.2 h0)
    refine ⟨l, (hiff l).2 ⟨X, hc, ?_⟩, by rw [hlfix]⟩
    have : τ = upsilon (l + 1) := by rw [hτdef, hh]
    rw [this]; exact hlP

/-! ## The gap -/

/-- **The gap statement, restricted to the countable segments** (`Wu.WuGap` with the segment clause asked only where
`υ_{λ+h} < Ω₁`; `Par` is cited only over countable bases). -/
def WwGap (S : InaccSeq.{0}) (k : ℕ) : Prop :=
  ∃ X, InE X ∧ upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) < X ∧ X < upsilon (Nc.ncL S (k : Ordinal.{0}) + 2) ∧
    (∀ ξ, ξ ∈ Tset (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) → ξ < Uc.ucB →
      vt (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) ξ ≠ X) ∧
    ∀ h y, 0 < h → upsilon (Nc.ncL S (k : Ordinal.{0}) + h) < Om1 → upsilon (Nc.ncL S (k : Ordinal.{0}) + h) ≤ y →
      y < upsilon (succ (Nc.ncL S (k : Ordinal.{0}) + h)) → y ≠ 0 → cdExp y = X →
      ∃ p ∈ Par (upsilon (Nc.ncL S (k : Ordinal.{0}) + h)) y, upsilon (Nc.ncL S (k : Ordinal.{0})) ≤ p

/-- `Wu.WuGap ⇒ WwGap`. -/
theorem wuGap_ww {k : ℕ} (hG : Wu.WuGap S k) : WwGap S k := by
  obtain ⟨X, h1, h2, h3, h4, h5⟩ := hG
  exact ⟨X, h1, h2, h3, h4, fun h y h0 _ hy1 hy2 hy0 he => h5 h y h0 hy1 hy2 hy0 he⟩

/-- **THE GAP HOLDS at every `L(k)`** (no hypothesis): `X = ϑ^{u₁}(B₂ + λ)`. -/
theorem wwGap (k : ℕ) : WwGap S k := by
  obtain ⟨-, hXE, hu1X, hXu2, -⟩ := wwX_spec (S := S) k
  exact ⟨wwX S k, hXE, hu1X, hXu2, wwVt_ne k, fun h y h0 hτ1 hy1 hy2 hy0 he => ww_par_X k h0 hτ1 hy1 hy2 hy0 he⟩

/-! ## The supply hypothesis of `Wf.wfRoad` fails -/

/-- **REFUTATION of the supply hypothesis at `L(k)`**: `L(k+1) ≤ ν_C ⇒ ¬ Wf.WfVisGen` at `L(k)` (as `Wu.wuVis_ref`,
with the gap now a theorem). -/
theorem wwVis_ref (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) :
    ¬ Wf.WfVisGen S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0})))) := by
  intro hV
  have hm := upsilon_normal.strictMono
  obtain ⟨X, hXE, hX1, hX2, hvt, hsg⟩ := wwGap (S := S) k
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
  · rcases Wu.wuForm_X k hν hXE hX1 hX2 hb1 hF with ⟨h, y, h0, hhβ, h1, h2, h3, h4, h5⟩ | ⟨ξ, hξ, hξB, hξe⟩
    · have hτ1 : upsilon (l + h) < Om1 := (hm ((add_lt_add_iff_left l).2 hhβ)).trans_le hb1
      obtain ⟨p, hp, hpl⟩ := hsg h y h0 hτ1 h1 h2 h4 h5
      exact absurd (h3 p hp) (not_lt.2 hpl)
    · exact hvt ξ hξ hξB hξe

/-- **`h0'` of `Wf.wfRoad` and `L(1) ≤ ν_C` exclude each other** (no hypothesis). -/
theorem wwRoad_vac :
    ¬ ((∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
        Wf.WfVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0)))) ∧
      Nc.ncL S 1 ≤ nuC) := by
  rintro ⟨h0, hν⟩
  have hν' : Nc.ncL S ((0 + 1 : ℕ) : Ordinal.{0}) ≤ nuC := by simpa using hν
  apply wwVis_ref 0 hν'
  have e : Nc.ncL S ((0 : ℕ) : Ordinal.{0}) = upsilon (Nc.ncL S ((0 : ℕ) : Ordinal.{0})) := (Te.teUps_L 0).symm
  have h := h0 (Nc.ncL S ((0 : ℕ) : Ordinal.{0})) (Te.teRst_L 0) (by simpa using e)
  simpa using h

/-- **THE HYPOTHESES OF `Wf.wfRoad` ARE JOINTLY FALSE**: the road proves `L(ω) ≤ ν_C`, hence `L(1) ≤ ν_C`, which
refutes its own supply hypothesis `h0` (`wwRoad_vac`).  So `Wf.wfRoad` (and every road built on it) is VACUOUS. -/
theorem wwRoad_false
    (hUH : ∀ l, CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdUpper S l)
    (hLH : ∀ l, CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdLower S l)
    (hVH : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdCapV S l)
    (hT : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      Wf.WfVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      Wf.WfVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    False := by
  have hR := Wf.wfRoad hUH hLH hVH hVt hT hF h0 hn
  have hLw : Nc.ncL S ω ≤ nuC := hR.2.2.2.2.2.1
  have h1 : Nc.ncL S 1 ≤ nuC := by
    have := Rp.rpL_lt (S := S) 1
    exact (by simpa using this : Nc.ncL S 1 < Nc.ncL S ω).le.trans hLw
  exact wwRoad_vac ⟨h0, h1⟩

/-- **The current road `Ws.wsRoadZ` is VACUOUS too**: its hypotheses are jointly false. -/
theorem wwRoadZ_false
    (hUH : ∀ l, CdRange S l → Bt.iota S (Gc.gcG Ws.wsVz.B * ω) ≤ l → CdUpper S l)
    (hLH : ∀ l, CdRange S l → Bt.iota S (Gc.gcG Ws.wsVz.B * ω) ≤ l → CdLower S l)
    (hVH : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S (Gc.gcG Ws.wsVz.B * ω) ≤ l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → Bt.iota S (Gc.gcG Ws.wsVz.B * ω) ≤ l → CdCapV S l)
    (hT : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      Wf.WfVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      Wf.WfVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    False := by
  have hR := Ws.wsRoadZ S hUH hLH hVH hVt hT hF h0 hn
  have hLw : Nc.ncL S ω ≤ nuC := hR.2.2.2.2.2.1
  have h1 : Nc.ncL S 1 ≤ nuC := by
    have := Rp.rpL_lt (S := S) 1
    exact (by simpa using this : Nc.ncL S 1 < Nc.ncL S ω).le.trans hLw
  exact wwRoad_vac ⟨h0, h1⟩

/-- **Every high-window forms clause fails** (no hypothesis but `L(k+1) ≤ ν_C`; `Wu.wuFormHigh_fail` with the gap
now a theorem): there is an `ε`-number `X ∈ (u₁, u₂)`, `X ≥ ε_{u₁+1}`, `X ≠ ω^{ω^{u₁+1}}`, whose window `ν_X` has no
big reach and no repaired form `Vr.VrForm` at the offset `X`. -/
theorem wwFormHigh_fail (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC)  :
    ∃ X, InE X ∧ upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) < X ∧ X < upsilon (Nc.ncL S (k : Ordinal.{0}) + 2) ∧
      eN (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) ≤ X ∧
      X ≠ ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) ∧
      ¬ (upsilon (Nc.ncL S (k : Ordinal.{0}) + (Nc.ncL S (k : Ordinal.{0}) + X + ω ^ 2 - Nc.ncL S (k : Ordinal.{0}) +
          ω ^ 2)) ≤ cdR S (Nc.ncL S (k : Ordinal.{0}) + X) ∨
        Vr.VrForm S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S (k : Ordinal.{0}) + X + ω ^ 2 -
          Nc.ncL S (k : Ordinal.{0}) + ω ^ 2) X) := by
  have hm := upsilon_normal.strictMono
  obtain ⟨X, hXE, hX1, hX2, hvt, hsg⟩ := wwGap (S := S) k
  obtain ⟨hl0, -, -, -, hu2L1, hL1E, hL1O, hbelow, hωL1⟩ := Vr.vr_facts (S := S) k
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
    · rcases Wu.wuForm_X k hν hXE hX1 hX2 hb1 hF with ⟨h, y, h0, hhβ, h1, h2, h3, h4, h5⟩ | ⟨ξ, hξ, hξB, hξe⟩
      · have hτ1 : upsilon (l + h) < Om1 := (hm ((add_lt_add_iff_left l).2 hhβ)).trans_le hb1
        obtain ⟨p, hp, hpl⟩ := hsg h y h0 hτ1 h1 h2 h4 h5
        exact absurd (h3 p hp) (not_lt.2 hpl)
      · exact hvt ξ hξ hξB hξe

end Googology.Trans.PoR.InaccPsi.R2.Ww
