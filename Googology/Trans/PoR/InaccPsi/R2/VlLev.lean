import Googology.Trans.PoR.InaccPsi.R2.ViTr
import Googology.Trans.PoR.InaccPsi.R2.ViLev
import Googology.Trans.PoR.InaccPsi.R2.ChainL

/-!
# The level clause of FRAG with moving level leaves

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
[W07b] G. Wilken, "Σ1-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.

For the node `thz G r` (`Vi.vmap`, the levels `G = Ω₁·q < B₂` with countable leaves), FRAG must carry, for each
segment map `Ψ`, a **level clause** `VlLC A Ψ`: at every level `Ω₁·q` whose leaves satisfy `A`, the moved level is a
level (`Ω₁ · vq Ψ q = vcSub Ψ (Ω₁·q)`, `1 ≤ vq Ψ q`, `< B₂`), leaf substitutions compose after it
(`vcSub f (vcSub Ψ z) = vcSub (f ∘ Ψ) z`) and its leaves are the `Ψ`-images (`VcLv P (vcSub Ψ z) ↔ VcLv (P ∘ Ψ) z`).

* `vl_T_mul_nat`, `vl_om1_mul_low`, `vl_lv_mem` (**a level whose leaves lie in `T^g` lies in `T^g`**: `Ω₁·q`,
  `1 ≤ q`, `Ω₁·q < B₂`; [W07b] Cor 5.10 through `R2.T_inter_Om1`, `Uy.uy_dat_of_mul`, `R2.ucArg_mem`,
  `R2.lvArg_mem`, `R2.luOm1_opow_T`, `R2.vzT_add`);
* `VlLC`, `vl_lc_congr`, `vl_lc_mono`, `vl_lc_id`, `vl_lc_pi`, `vl_lc_up`, `vl_lc_mv` (**the base: the segment
  move**), `vl_lc_comp` (**the step: `π⁻¹_{γ,t'} ∘ Ψ' ∘ π_{β,t}`**);
* on terms: `ZL_and`, `Lv_vmap`, `Lv_vtr`, `ZL_vtr`, `LoL_back_vmap`, `HdDA_vmap`, `vmap_vmap_lc`, `ZL_vmap_lc`,
  `vtr_vmap` (**the translation commutes with `vmap Ψ`**, the analogue of `Ur.trr_map`).

New definition: `VlLC`.  No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vl

open Ordinal Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uh Googology.Trans.PoR.InaccPsi.R2.Un
  Googology.Trans.PoR.InaccPsi.R2.Un.UnT Googology.Trans.PoR.InaccPsi.R2.Ur Googology.Trans.PoR.InaccPsi.R2.Vc
  Googology.Trans.PoR.InaccPsi.R2.Vi Googology.Trans.PoR.InaccPsi.R2.Uc

/-! ## Membership of a level from its leaves -/

theorem vl_T_mul_nat {g x : Ordinal.{0}} (hg : InE g) (hg1 : g < Om1) (hx : x ∈ Tset g) :
    ∀ n : ℕ, 1 ≤ n → x * (n : Ordinal.{0}) ∈ Tset g
  | 0, h => absurd h (by omega)
  | 1, _ => by simpa using hx
  | n + 2, _ => by
    have h := vl_T_mul_nat hg hg1 hx (n + 1) (by omega)
    rw [show n + 2 = (n + 1) + 1 from rfl, Nat.cast_add_one, mul_add, mul_one]
    exact vzT_add hg hg1 h hx

/-- `Ω₁·M ∈ T^g` for every `M < g`. -/
theorem vl_om1_mul_low {g : Ordinal.{0}} (hg : InE g) (hg1 : g < Om1) :
    ∀ M, M < g → Om1 * M ∈ Tset g := by
  intro M
  induction M using WellFoundedLT.induction with
  | ind M IH =>
  intro hMg
  rcases eq_or_ne M 0 with h0 | h0
  · rw [h0, mul_zero]; exact uh_T_le hg hg1 (zero_le (a := g))
  obtain ⟨hdec, hv0, hvω, -⟩ := Si.si_dec h0
  have hrM : M % ω ^ log ω M < M := Rj.rj_mod_lt h0
  have hl : log ω M ≤ g := (Ordinal.log_le_self ω M).trans hMg.le
  have hw : Om1 * ω ^ log ω M ∈ Tset g := luOm1_opow_T hg hg1 hl
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.1 hvω
  have hn1 : 1 ≤ n := by
    rcases n with _ | n
    · exact absurd (by simpa using hn) hv0
    · omega
  have h1 : Om1 * ω ^ log ω M * (n : Ordinal.{0}) ∈ Tset g := vl_T_mul_nat hg hg1 hw n hn1
  have h2 := IH _ hrM (hrM.trans hMg)
  have e : Om1 * M = Om1 * ω ^ log ω M * (n : Ordinal.{0}) + Om1 * (M % ω ^ log ω M) := by
    calc Om1 * M = Om1 * (ω ^ log ω M * (M / ω ^ log ω M) + M % ω ^ log ω M) := by rw [hdec]
      _ = _ := by rw [mul_add, ← mul_assoc, hn]
  rw [e]
  exact vzT_add hg hg1 h1 h2

/-- **A level whose leaves lie in `T^g` lies in `T^g`** (`g` an `ε`-number below `Ω₁`, `1 ≤ q`, `Ω₁·q < B₂`):
`T^g ∩ Ω₁ = m` is an `ε`-number ([W07b] Cor 5.10, `R2.T_inter_Om1`), so `ucDat(Ω₁·q) < m`, `ucDat q < m`
(`Uy.uy_dat_of_mul`), and `Ω₁·q ∈ T^g` by `R2.ucArg_mem` (`q ≥ Ω₁`), `R2.lvArg_mem` (`g ≤ q < Ω₁`) or
`vl_om1_mul_low` (`q < g`). -/
theorem vl_lv_mem {g q : Ordinal.{0}} (hg : InE g) (hg1 : g < Om1) (hq1 : 1 ≤ q) (hqB : Om1 * q < ucB)
    (hL : VcLv (· ∈ Tset g) (Om1 * q)) : Om1 * q ∈ Tset g := by
  obtain ⟨m, hgm, hm, -, hT, hm1⟩ := T_next (Or.inr hg) hg1
  have hmE : InE m := upsPt_inE ⟨(zero_le (a := g)).trans_lt hgm, hm⟩
  have hLm : VcLv (· < m) (Om1 * q) := VcLv_mono (fun x hx hxT => (hT x hx).1 hxT) _ hL
  have hd : ucDat (Om1 * q) < m := (vc_dat_lt hmE _ hqB).1 hLm
  have hdq : ucDat q < m := Uy.uy_dat_of_mul hmE q (Order.one_le_iff_ne_zero.1 hq1) hqB hd
  have hqB' : q < ucB := (le_mul_right q Rj.rj_Om1_pos).trans_lt hqB
  have h0T : (0 : Ordinal.{0}) ∈ Tset g := uh_T_le hg hg1 (zero_le (a := g))
  rcases lt_or_ge q Om1 with hq | hq
  · have hqm : q < m := by rwa [ucDat_small hq] at hdq
    have hqT : q ∈ Tset g := (hT q hq).2 hqm
    rcases lt_or_ge q g with hqg | hqg
    · exact vl_om1_mul_low hg hg1 q hqg
    · have := lvArg_mem hg hg1 hqT hqg hq h0T Rj.rj_Om1_pos
      rwa [add_zero] at this
  · have := ucArg_mem hg hg1 hq hqB' ((hT _ (hdq.trans hm1)).2 hdq) h0T Rj.rj_Om1_pos
    rwa [add_zero] at this

/-! ## The level clause -/

/-- **The level clause of a segment map `Ψ` on the leaves `A`**: at every level `Ω₁·q` (`1 ≤ q`, `Ω₁·q < B₂`)
whose leaves satisfy `A`, `vcSub Ψ (Ω₁·q)` is the level `Ω₁ · vq Ψ q` (`1 ≤ vq Ψ q`, `< B₂`), leaf substitutions
compose after `Ψ`, and the leaves of the moved level are the `Ψ`-images. -/
def VlLC (A : Ordinal.{0} → Prop) (Ψ : Ordinal.{0} → Ordinal.{0}) : Prop :=
  ∀ q, 1 ≤ q → Om1 * q < ucB → VcLv A (Om1 * q) →
    Om1 * vq Ψ q = vcSub Ψ (Om1 * q) ∧ 1 ≤ vq Ψ q ∧ Om1 * vq Ψ q < ucB ∧
    (∀ f : Ordinal.{0} → Ordinal.{0}, vcSub f (vcSub Ψ (Om1 * q)) = vcSub (fun x => f (Ψ x)) (Om1 * q)) ∧
    (∀ P : Ordinal.{0} → Prop, VcLv P (vcSub Ψ (Om1 * q)) ↔ VcLv (fun x => P (Ψ x)) (Om1 * q))

theorem vl_lc_mono {A A' : Ordinal.{0} → Prop} {Ψ : Ordinal.{0} → Ordinal.{0}} (hA : ∀ x, A x → A' x)
    (h : VlLC A' Ψ) : VlLC A Ψ := fun q hq1 hqB hL =>
  h q hq1 hqB (VcLv_mono (fun x _ hx => hA x hx) _ hL)

/-- The level clause depends only on the values of `Ψ` on `A`. -/
theorem vl_lc_congr {A : Ordinal.{0} → Prop} {Ψ Ψ₀ : Ordinal.{0} → Ordinal.{0}} (he : ∀ x, A x → Ψ x = Ψ₀ x)
    (h : VlLC A Ψ₀) : VlLC A Ψ := by
  intro q hq1 hqB hL
  obtain ⟨e, h1, hB, hc, hP⟩ := h q hq1 hqB hL
  have hE : VcLv (fun x => Ψ x = Ψ₀ x) (Om1 * q) := VcLv_mono (fun x _ hx => he x hx) _ hL
  have hs : vcSub Ψ (Om1 * q) = vcSub Ψ₀ (Om1 * q) := vcSub_congr _ hE
  have hv : vq Ψ q = vq Ψ₀ q := by
    show vcSub Ψ (Om1 * q) / Om1 = vcSub Ψ₀ (Om1 * q) / Om1
    rw [hs]
  refine ⟨by rw [hv, hs]; exact e, hv ▸ h1, hv ▸ hB, fun f => ?_, fun P => ?_⟩
  · rw [hs, hc f]
    exact vcSub_congr _ (VcLv_mono (fun x _ hx => by simp only [hx]) _ hE)
  · rw [hs, hP P]
    exact vi_lv_congr (VcLv_mono (fun x _ hx => by simp only [hx]) _ hE)

theorem vl_lc_id (A : Ordinal.{0} → Prop) : VlLC A id := by
  intro q hq1 hqB hL
  have hs : vcSub id (Om1 * q) = Om1 * q := vcSub_fix _ (VcLv_mono (fun _ _ _ => rfl) _ hL)
  have hv : vq id q = q := vq_id q hL
  refine ⟨by rw [hv, hs], by rw [hv]; exact hq1, by rw [hv]; exact hqB, fun f => ?_, fun P => ?_⟩
  · rw [hs]; rfl
  · rw [hs]; rfl

/-- **The base change** `π_{σ,τ}` on levels with leaves in `Tᵗ[σ]` (`Vc.vc_level_img`, `Vc.vc_comp`,
`Vi.vi_lv_pi`). -/
theorem vl_lc_pi {σ τ : Ordinal.{0}} (h : Bases σ τ) : VlLC (· ∈ TB τ σ) (pi σ τ) := by
  intro q hq1 hqB hL
  obtain ⟨hGT, -⟩ := vc_pi h _ hqB hL
  obtain ⟨M', hM', h1, hB, hsub⟩ := vc_level_img h hq1 hqB hGT
  have hv : vq (pi σ τ) q = M' := by
    show vcSub (pi σ τ) (Om1 * q) / Om1 = M'
    rw [← hsub, hM']; exact Ordinal.mul_div_cancel M' Rj.rj_Om1_pos.ne'
  refine ⟨by rw [hv, ← hsub, hM'], hv ▸ h1, hv ▸ hB, fun f => ?_, fun P => ?_⟩
  · rw [← hsub]; exact vc_comp h f _ hqB hGT
  · rw [← hsub]; exact vi_lv_pi h P _ hqB hGT

/-- **The inverse base change** `π⁻¹_{σ,τ}` on levels with leaves in `T^σ` (`vl_lv_mem`, `Vi.vi_up_level`,
`Vi.vi_sub_up`, `Vi.vi_lv_up`). -/
theorem vl_lc_up {σ τ : Ordinal.{0}} (h : Bases σ τ) : VlLC (· ∈ Tset σ) (up σ τ) := by
  intro q hq1 hqB hL
  have hGT : Om1 * q ∈ Tset σ := vl_lv_mem h.1 (h.2.2.1.trans h.2.2.2) hq1 hqB hL
  obtain ⟨u0, u1, u2, -⟩ := vi_up_level (τ := τ) h hq1 hqB hGT
  have hsub : up σ τ (Om1 * q) = vcSub (up σ τ) (Om1 * q) := (vc_up h hqB hGT).1
  refine ⟨by rw [u0, hsub], u1, u2, fun f => ?_, fun P => ?_⟩
  · rw [← hsub]; exact vi_sub_up h f hqB hGT
  · rw [← hsub]; exact vi_lv_up h P hqB hGT

/-- **THE BASE OF THE LEVEL CLAUSE: the segment move** `mv b c` on levels with leaves in `T^b[κ]`. -/
theorem vl_lc_mv {κ b c : Ordinal.{0}} (hb : InE b) (hb1 : b < Om1) (hc : InE c) (hc1 : c < Om1) (hκc : κ ≤ c) :
    VlLC (· ∈ TB b κ) (mv b c) := by
  rcases lt_trichotomy c b with hcb | rfl | hbc
  · have hmv : mv b c = pi c b := by unfold mv; rw [if_pos hcb]
    rw [hmv]
    exact vl_lc_mono (fun x hx => Ub.ub_TB_mono hκc hx) (vl_lc_pi ⟨hc, hb, hcb, hb1⟩)
  · have hmv : mv c c = id := by unfold mv; simp
    rw [hmv]; exact vl_lc_id _
  · have hmv : mv b c = up b c := by unfold mv; rw [if_neg (not_lt.2 hbc.le), if_pos hbc]
    rw [hmv]
    exact vl_lc_mono (fun x hx => hx.1) (vl_lc_up ⟨hb, hc, hbc, hc1⟩)

/-- **THE STEP OF THE LEVEL CLAUSE**: if `Ψ'` has the level clause on `A'`, `π_{β,t}` maps `A` into `A'` (with
`A ⊆ Tᵗ[β]`) and `Ψ'` maps `A'` into `T^γ`, then `x ↦ π⁻¹_{γ,t'}(Ψ'(π_{β,t} x))` has the level clause on `A`
(the moved level `π⁻¹ W`, `W = vcSub Ψ' (π z)`, lies in `T^γ` by `vl_lv_mem`). -/
theorem vl_lc_comp {β t γ t' : Ordinal.{0}} (hβ : Bases β t) (hγ : Bases γ t') {A A' : Ordinal.{0} → Prop}
    {Ψ' : Ordinal.{0} → Ordinal.{0}} (hFT : ∀ x, A x → x ∈ TB t β) (hF' : ∀ x, A x → A' (pi β t x))
    (hΨT : ∀ x, A' x → Ψ' x ∈ Tset γ) (hC : VlLC A' Ψ') :
    VlLC A (fun x => up γ t' (Ψ' (pi β t x))) := by
  intro q hq1 hqB hL
  have hL1 : VcLv (· ∈ TB t β) (Om1 * q) := VcLv_mono (fun x _ hx => hFT x hx) _ hL
  have hzT : Om1 * q ∈ TB t β := (vc_pi hβ _ hqB hL1).1
  obtain ⟨M', hM', hM1, hMB, -⟩ := vc_level_img hβ hq1 hqB hzT
  have hL' : VcLv A' (Om1 * M') := by
    rw [← hM']; exact (vi_lv_pi hβ A' _ hqB hzT).2 (VcLv_mono (fun x _ hx => hF' x hx) _ hL)
  obtain ⟨e', h1', hB', hc', hP'⟩ := hC M' hM1 hMB hL'
  have hγ1 : γ < Om1 := hγ.2.2.1.trans hγ.2.2.2
  have hWT : Om1 * vq Ψ' M' ∈ Tset γ := by
    refine vl_lv_mem hγ.1 hγ1 h1' hB' ?_
    rw [e']; exact (hP' _).2 (VcLv_mono (fun x _ hx => hΨT x hx) _ hL')
  obtain ⟨u0, u1, u2, -⟩ := vi_up_level (τ := t') hγ h1' hB' hWT
  have hsW : up γ t' (Om1 * vq Ψ' M') = vcSub (up γ t') (Om1 * vq Ψ' M') := (vc_up hγ hB' hWT).1
  have key : vcSub (fun x => up γ t' (Ψ' (pi β t x))) (Om1 * q) = up γ t' (Om1 * vq Ψ' M') := by
    calc vcSub (fun x => up γ t' (Ψ' (pi β t x))) (Om1 * q)
        = vcSub ((fun y => up γ t' (Ψ' y)) ∘ pi β t) (Om1 * q) := rfl
      _ = vcSub (fun y => up γ t' (Ψ' y)) (pi β t (Om1 * q)) :=
          (vc_comp hβ (fun y => up γ t' (Ψ' y)) _ hqB hzT).symm
      _ = vcSub (up γ t') (vcSub Ψ' (Om1 * M')) := by rw [hM', hc' (up γ t')]
      _ = up γ t' (Om1 * vq Ψ' M') := by rw [← e', hsW]
  have hv : vq (fun x => up γ t' (Ψ' (pi β t x))) q = vq (up γ t') (vq Ψ' M') := by
    show vcSub (fun x => up γ t' (Ψ' (pi β t x))) (Om1 * q) / Om1 = _
    rw [key, ← u0]; exact Ordinal.mul_div_cancel _ Rj.rj_Om1_pos.ne'
  refine ⟨by rw [hv, u0, key], hv ▸ u1, hv ▸ u2, fun f => ?_, fun P => ?_⟩
  · rw [key, vi_sub_up hγ f hB' hWT, e', hc' (f ∘ up γ t'), ← hM']
    exact vc_comp hβ (fun y => (f ∘ up γ t') (Ψ' y)) _ hqB hzT
  · rw [key, vi_lv_up hγ P hB' hWT, e', hP' (fun y => P (up γ t' y)), ← hM']
    exact vi_lv_pi hβ (fun y => P (up γ t' (Ψ' y))) _ hqB hzT

/-! ## On terms -/

theorem ZL_and {P Q : Ordinal.{0} → Prop} :
    ∀ {k : Bool} (t : UnT k), ZL P t → ZL Q t → ZL (fun p => P p ∧ Q p) t
  | _, .par _, _, _ => trivial
  | _, .add s t, h1, h2 => ⟨ZL_and s h1.1 h2.1, ZL_and t h1.2 h2.2⟩
  | _, .base, _, _ => trivial
  | _, .th1 s, h1, h2 => ZL_and s h1 h2
  | _, .thc _ r, h1, h2 => ⟨VcLv_and _ h1.1 h2.1, ZL_and r h1.2 h2.2⟩
  | _, .thg _ G r, h1, h2 => ⟨ZL_and G h1.1 h2.1, ZL_and r h1.2 h2.2⟩
  | _, .lf c, h1, h2 => ZL_and c h1 h2
  | _, .om b, h1, h2 => ZL_and b h1 h2
  | _, .ad x y, h1, h2 => ⟨ZL_and x h1.1 h2.1, ZL_and y h1.2 h2.2⟩

theorem Lv_vmap {P : Ordinal.{0} → Prop} {f : Ordinal.{0} → Ordinal.{0}} :
    ∀ {k : Bool} (t : UnT k), Lv P (vmap f t) ↔ Lv (fun p => P (f p)) t
  | _, .par _ => Iff.rfl
  | _, .add s t => and_congr (Lv_vmap s) (Lv_vmap t)
  | _, .base => Iff.rfl
  | _, .th1 s => Lv_vmap s
  | _, .thc _ r => Lv_vmap r
  | _, .thg _ G r => and_congr (Lv_vmap G) (Lv_vmap r)
  | _, .lf c => Lv_vmap c
  | _, .om b => Lv_vmap b
  | _, .ad x y => and_congr (Lv_vmap x) (Lv_vmap y)

theorem Lv_vtr {P : Ordinal.{0} → Prop} {a : Ordinal.{0}} (ha : P a) :
    ∀ {k : Bool} (t : UnT k), Lv P t → Lv P (vtr a t)
  | _, .par _, h => h
  | _, .add s t, h => ⟨Lv_vtr ha s h.1, Lv_vtr ha t h.2⟩
  | _, .base, _ => ha
  | _, .th1 s, h => ⟨ha, Lv_vtr ha s h⟩
  | _, .thc q r, h => by
    by_cases hG : VcLv (· < a) (Om1 * q)
    · rw [vtr_thc_lo hG]; exact ⟨ha, Lv_vtr ha r h⟩
    · rw [vtr_thc_hi hG]; exact Lv_vtr ha r h
  | _, .thg _ G r, h => by
    by_cases hG : LoL a G
    · rw [vtr_thg_lo hG]; exact ⟨Lv_vtr ha G h.1, ha, Lv_vtr ha r h.2⟩
    · rw [vtr_thg_hi hG]; exact ⟨Lv_vtr ha G h.1, Lv_vtr ha r h.2⟩
  | _, .lf c, h => Lv_vtr ha c h
  | _, .om b, h => Lv_vtr ha b h
  | _, .ad x y, h => ⟨Lv_vtr ha x h.1, Lv_vtr ha y h.2⟩

/-- The translation keeps the levels. -/
theorem ZL_vtr {P : Ordinal.{0} → Prop} (a : Ordinal.{0}) :
    ∀ {k : Bool} (t : UnT k), ZL P t → ZL P (vtr a t)
  | _, .par _, h => h
  | _, .add s t, h => ⟨ZL_vtr a s h.1, ZL_vtr a t h.2⟩
  | _, .base, _ => trivial
  | _, .th1 s, h => ⟨trivial, ZL_vtr a s h⟩
  | _, .thc q r, h => by
    by_cases hG : VcLv (· < a) (Om1 * q)
    · rw [vtr_thc_lo hG]; exact ⟨h.1, trivial, ZL_vtr a r h.2⟩
    · rw [vtr_thc_hi hG]; exact ⟨h.1, ZL_vtr a r h.2⟩
  | _, .thg _ G r, h => by
    by_cases hG : LoL a G
    · rw [vtr_thg_lo hG]; exact ⟨ZL_vtr a G h.1, trivial, ZL_vtr a r h.2⟩
    · rw [vtr_thg_hi hG]; exact ⟨ZL_vtr a G h.1, ZL_vtr a r h.2⟩
  | _, .lf c, h => ZL_vtr a c h
  | _, .om b, h => ZL_vtr a b h
  | _, .ad x y, h => ⟨ZL_vtr a x h.1, ZL_vtr a y h.2⟩

theorem LoL_back_vmap (a : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) :
    ∀ {k : Bool} (G : UnT k), Lv (fun p => p < a ↔ f p < f a) G → LoL (f a) (vmap f G) → LoL a G
  | _, .lf (.par _), hl, h' => hl.2 h'
  | _, .om b, hl, h' => LoL_back_vmap a f b hl h'
  | _, .ad x y, hl, h' => ⟨LoL_back_vmap a f x hl.1 h'.1, LoL_back_vmap a f y hl.2 h'.2⟩
  | _, .lf (.add _ _), _, h' => h'.elim
  | _, .lf .base, _, h' => h'.elim
  | _, .lf (.th1 _), _, h' => h'.elim
  | _, .lf (.thc _ _), _, h' => h'.elim
  | _, .lf (.thg _ _ _), _, h' => h'.elim
  | _, .par _, _, h' => h'.elim
  | _, .add _ _, _, h' => h'.elim
  | _, .base, _, h' => h'.elim
  | _, .th1 _, _, h' => h'.elim
  | _, .thc _ _, _, h' => h'.elim
  | _, .thg _ _ _, _, h' => h'.elim

theorem HdDA_vmap {τ σ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} :
    ∀ {k : Bool} (t : UnT k), Lv (fun p => (τ ≤ p → σ ≤ f p) ∧ (p < τ → f p < σ)) t → HdDA τ t →
      HdDA σ (vmap f t)
  | _, .par _, _, _ => trivial
  | _, .add s t, hl, h => ⟨HdDA_vmap s hl.1 h.1, HdDA_vmap t hl.2 h.2⟩
  | _, .base, _, _ => trivial
  | _, .th1 s, hl, h => HdDA_vmap s hl h
  | _, .thc _ r, hl, h => HdDA_vmap r hl h
  | _, .thg m G r, hl, h => ⟨HdD_vmap m G hl.1 h.1, HdDA_vmap G hl.1 h.2.1, HdDA_vmap r hl.2 h.2.2⟩
  | _, .lf c, hl, h => HdDA_vmap c hl h
  | _, .om b, hl, h => HdDA_vmap b hl h
  | _, .ad x y, hl, h => ⟨HdDA_vmap x hl.1 h.1, HdDA_vmap y hl.2 h.2⟩

/-- **`vmap f ∘ vmap Ψ = vmap (f ∘ Ψ)`** under the level clause of `Ψ` on the level leaves. -/
theorem vmap_vmap_lc {A : Ordinal.{0} → Prop} {Ψ : Ordinal.{0} → Ordinal.{0}} (hC : VlLC A Ψ)
    (f : Ordinal.{0} → Ordinal.{0}) {τ : Ordinal.{0}} :
    ∀ {k : Bool} (t : UnT k), ZW τ t → ZL A t → vmap f (vmap Ψ t) = vmap (fun x => f (Ψ x)) t
  | _, .par _, _, _ => rfl
  | _, .add s t, hz, hl => by
    simp only [vmap, vmap_vmap_lc hC f s hz.1 hl.1, vmap_vmap_lc hC f t hz.2 hl.2]
  | _, .base, _, _ => rfl
  | _, .th1 s, hz, hl => by simp only [vmap, vmap_vmap_lc hC f s hz hl]
  | _, .thc q r, hz, hl => by
    obtain ⟨e, -, -, hc, -⟩ := hC q hz.1.q1 hz.1.qB hl.1
    have hq : vq f (vq Ψ q) = vq (fun x => f (Ψ x)) q := by
      show vcSub f (Om1 * vq Ψ q) / Om1 = vcSub (fun x => f (Ψ x)) (Om1 * q) / Om1
      rw [e, hc]
    simp only [vmap, vmap_vmap_lc hC f r hz.2 hl.2, hq]
  | _, .thg _ G r, hz, hl => by
    simp only [vmap, vmap_vmap_lc hC f G hz.1 hl.1, vmap_vmap_lc hC f r hz.2 hl.2]
  | _, .lf c, hz, hl => by simp only [vmap, vmap_vmap_lc hC f c hz hl]
  | _, .om b, hz, hl => by simp only [vmap, vmap_vmap_lc hC f b hz hl]
  | _, .ad x y, hz, hl => by
    simp only [vmap, vmap_vmap_lc hC f x hz.1 hl.1, vmap_vmap_lc hC f y hz.2 hl.2]

/-- **The level leaves after `vmap Ψ`** under the level clause: `ZL P (vmap Ψ t) ↔ ZL (P ∘ Ψ) t`. -/
theorem ZL_vmap_lc {A : Ordinal.{0} → Prop} {Ψ : Ordinal.{0} → Ordinal.{0}} (hC : VlLC A Ψ)
    (P : Ordinal.{0} → Prop) {τ : Ordinal.{0}} :
    ∀ {k : Bool} (t : UnT k), ZW τ t → ZL A t → (ZL P (vmap Ψ t) ↔ ZL (fun x => P (Ψ x)) t)
  | _, .par _, _, _ => Iff.rfl
  | _, .add s t, hz, hl => and_congr (ZL_vmap_lc hC P s hz.1 hl.1) (ZL_vmap_lc hC P t hz.2 hl.2)
  | _, .base, _, _ => Iff.rfl
  | _, .th1 s, hz, hl => ZL_vmap_lc hC P s hz hl
  | _, .thc q r, hz, hl => by
    obtain ⟨e, -, -, -, hP⟩ := hC q hz.1.q1 hz.1.qB hl.1
    show VcLv P (Om1 * vq Ψ q) ∧ _ ↔ _
    rw [e, hP P]
    exact and_congr Iff.rfl (ZL_vmap_lc hC P r hz.2 hl.2)
  | _, .thg _ G r, hz, hl => and_congr (ZL_vmap_lc hC P G hz.1 hl.1) (ZL_vmap_lc hC P r hz.2 hl.2)
  | _, .lf c, hz, hl => ZL_vmap_lc hC P c hz hl
  | _, .om b, hz, hl => ZL_vmap_lc hC P b hz hl
  | _, .ad x y, hz, hl => and_congr (ZL_vmap_lc hC P x hz.1 hl.1) (ZL_vmap_lc hC P y hz.2 hl.2)

/-- **THE TRANSLATION COMMUTES WITH `vmap Ψ`** (the analogue of `Ur.trr_map`): if `Ψ` keeps the order to `a` on the
parameters and on the level leaves and has the level clause there, the decision at a `thz`-node (every leaf of the
level below `a`) is the same at `a` and at `Ψ a`, so `vmap Ψ (vtr a t) = vtr (Ψ a) (vmap Ψ t)`. -/
theorem vtr_vmap {A : Ordinal.{0} → Prop} {Ψ : Ordinal.{0} → Ordinal.{0}} (hC : VlLC A Ψ) (a : Ordinal.{0})
    {τ : Ordinal.{0}} :
    ∀ {k : Bool} (t : UnT k), ZW τ t → ZL A t → ZL (fun p => p < a ↔ Ψ p < Ψ a) t →
      Lv (fun p => p < a ↔ Ψ p < Ψ a) t → vmap Ψ (vtr a t) = vtr (Ψ a) (vmap Ψ t)
  | _, .par _, _, _, _, _ => rfl
  | _, .add s t, hz, hA, ho, hl => by
    simp only [vtr, vmap, vtr_vmap hC a s hz.1 hA.1 ho.1 hl.1, vtr_vmap hC a t hz.2 hA.2 ho.2 hl.2]
  | _, .base, _, _, _, _ => rfl
  | _, .th1 s, hz, hA, ho, hl => by simp only [vtr, vmap, vtr_vmap hC a s hz hA ho hl]
  | _, .thc q r, hz, hA, ho, hl => by
    obtain ⟨e, -, -, -, hP⟩ := hC q hz.1.q1 hz.1.qB hA.1
    have hiff : VcLv (· < a) (Om1 * q) ↔ VcLv (· < Ψ a) (Om1 * vq Ψ q) := by
      rw [e, hP (· < Ψ a)]; exact vi_lv_congr ho.1
    have IH := vtr_vmap hC a r hz.2 hA.2 ho.2 hl
    by_cases hG : VcLv (· < a) (Om1 * q)
    · rw [vtr_thc_lo hG, show vmap Ψ (UnT.thc q r) = UnT.thc (vq Ψ q) (vmap Ψ r) from rfl,
        vtr_thc_lo (hiff.1 hG)]
      simp only [vmap, IH]
    · rw [vtr_thc_hi hG, show vmap Ψ (UnT.thc q r) = UnT.thc (vq Ψ q) (vmap Ψ r) from rfl,
        vtr_thc_hi (fun h' => hG (hiff.2 h'))]
      simp only [vmap, IH]
  | _, .thg m G r, hz, hA, ho, hl => by
    have hiff : LoL a G ↔ LoL (Ψ a) (vmap Ψ G) :=
      ⟨LoL_vmap G (Lv_mono (fun _ hp => hp.1) G hl.1), fun h' => LoL_back_vmap a Ψ G hl.1 h'⟩
    have IG := vtr_vmap hC a G hz.1 hA.1 ho.1 hl.1
    have IR := vtr_vmap hC a r hz.2 hA.2 ho.2 hl.2
    by_cases hG : LoL a G
    · rw [vtr_thg_lo hG, show vmap Ψ (UnT.thg m G r) = UnT.thg m (vmap Ψ G) (vmap Ψ r) from rfl,
        vtr_thg_lo (hiff.1 hG)]
      simp only [vmap, IG, IR]
    · rw [vtr_thg_hi hG, show vmap Ψ (UnT.thg m G r) = UnT.thg m (vmap Ψ G) (vmap Ψ r) from rfl,
        vtr_thg_hi (fun h' => hG (hiff.2 h'))]
      simp only [vmap, IG, IR]
  | _, .lf c, hz, hA, ho, hl => by simp only [vtr, vmap, vtr_vmap hC a c hz hA ho hl]
  | _, .om b, hz, hA, ho, hl => by simp only [vtr, vmap, vtr_vmap hC a b hz hA ho hl]
  | _, .ad x y, hz, hA, ho, hl => by
    simp only [vtr, vmap, vtr_vmap hC a x hz.1 hA.1 ho.1 hl.1, vtr_vmap hC a y hz.2 hA.2 ho.2 hl.2]

/-- `ZL` is monotone in the countable leaves. -/
theorem vl_ZL_mono {P Q : Ordinal.{0} → Prop} (hx : ∀ x, x < Om1 → P x → Q x) :
    ∀ {k : Bool} (t : UnT k), ZL P t → ZL Q t
  | _, .par _, _ => trivial
  | _, .add s t, h => ⟨vl_ZL_mono hx s h.1, vl_ZL_mono hx t h.2⟩
  | _, .base, _ => trivial
  | _, .th1 s, h => vl_ZL_mono hx s h
  | _, .thc _ r, h => ⟨VcLv_mono (fun x h1 h2 => hx x h1 h2) _ h.1, vl_ZL_mono hx r h.2⟩
  | _, .thg _ G r, h => ⟨vl_ZL_mono hx G h.1, vl_ZL_mono hx r h.2⟩
  | _, .lf c, h => vl_ZL_mono hx c h
  | _, .om b, h => vl_ZL_mono hx b h
  | _, .ad x y, h => ⟨vl_ZL_mono hx x h.1, vl_ZL_mono hx y h.2⟩

/-- **The level leaves of a term over `τ` lie below every `υ`-point above `τ`** when they lie in `Tᵗ`
(`Tᵗ ∩ Ω₁` is the next `υ`-point, [W07b] Cor 5.10). -/
theorem vl_ZL_lt {τ u : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hτu : τ < u) (hu : UpsPt u) {k : Bool}
    (t : UnT k) (h : ZL (· ∈ Tset τ) t) : ZL (· < u) t := by
  obtain ⟨m, -, -, hmin, hT, -⟩ := T_next (Or.inr hτ) hτ1
  have hmu : m ≤ u := hmin u hτu hu.2
  exact vl_ZL_mono (fun x hx hxT => ((hT x hx).1 hxT).trans_le hmu) t h

end Googology.Trans.PoR.InaccPsi.R2.Vl
