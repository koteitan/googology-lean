import Googology.Trans.PoR.InaccPsi.R2.XuC
import Googology.Trans.PoR.InaccPsi.R2.XcBr

/-!
# XuBase: EVERY `ε`-NUMBER CODE `e ∈ [t₀, Γ(1))` HAS A SEQUENCE OF LEVELS — ONE PROOF FOR EVERY VEBLEN LEVEL

`e = glPsi α ι = φ(α, Λ_α(ι))` (`ι = xuI e`, or `1 + xuI e` at the level `G`; the gate of `e` is
`max 1 (max (xuQ α) (xuQ ι))`, `xu_gg_glPsi`).  The argument of `R2.WxBase` (one case split on the argument
`y = Λ_α(ι)`, generic in `α`), with the interface `Xu.xuC` (gate `xuGg`):

* **`y` a limit** (`xu_base_I`): `glPsi α ι_k` / `glPsi α (s μ)` from the sequence of the smaller code `ι`;
* **`y` a successor or `0`** (`xu_pkg`, the predecessor `f`), by the level: `α = 1` (`e = ε_{f+1}`: `t₀` itself
  from the towers `G^{⋯^G}` of `Wt.wtTw`, `xu_base_t0`, or the towers `f^{f^{⋯}}` over `f ≥ t₀`, `xu_base_succE`);
  `α = α'+1`, `α' ≥ 1`: the iterates of `φ(α', ·)` over `f + 1`; `α` a limit: `φ(α_k, f+1)` / `φ(s μ, f+1)`.

The gate-cofinality recursion `xu_rec` treats the codes below `t₀` through ONE member of the sequence above `t₀`
(`hT0`; below `t₀` the brackets are not `xuPsi` codes).

No new axiom.  New definitions: `XuPkg`.
-/

set_option autoImplicit false

open Googology.Trans.PoR.InaccPsi.R2.Wm Googology.Trans.PoR.InaccPsi.R2.Wh Googology.Trans.PoR.InaccPsi.R2.Ho
open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gf
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb
  Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gk
open Googology.Trans.PoR.InaccPsi.R2.Wo Googology.Trans.PoR.InaccPsi.R2.Wn Googology.Trans.PoR.InaccPsi.R2.Ws
  Googology.Trans.PoR.InaccPsi.R2.Wt Googology.Trans.PoR.InaccPsi.R2.Xc Googology.Trans.PoR.InaccPsi.R2.Wx

namespace Googology.Trans.PoR.InaccPsi.R2.Xu

/-! ## Gates -/

theorem xuQ_le_gg (a : Ordinal.{0}) : xuQ a ≤ xuGg a := (xuQ_le a).trans (le_max_right _ _)

theorem xu_one_le_gg (a : Ordinal.{0}) : (1 : Ordinal.{0}) ≤ xuGg a := le_max_left _ _

theorem xuQ_inf {a : Ordinal.{0}} (ha : ω ≤ a) : xuQ a = xuG a := if_neg (not_lt.2 ha)

theorem xu_gg_lim {d : Ordinal.{0}} (hd : IsSuccLimit d) : xuGg d = max 1 (xuQ d) := by
  unfold xuGg; rw [xuQ_inf (omega0_le_of_isSuccLimit hd)]

/-- A part whose gate as a part is bounded by the gate of `b` has its gate below every `ε`-number above `b`'s. -/
theorem xu_gg_part {q b σ : Ordinal.{0}} (hσ : InE σ) (hq : xuQ q ≤ xuG b) (hb : xuGg b < σ) : xuGg q < σ := by
  by_cases hω : q < ω
  · obtain ⟨n, rfl⟩ := lt_omega0.1 hω
    exact (xuGg_lt_iff hσ).2 ((xuG_nat_lt n).trans (omega0_lt_inE hσ))
  · refine (xuGg_lt_iff hσ).2 ?_
    rw [← xuQ_inf (not_lt.1 hω)]; exact hq.trans_lt ((xuGg_lt_iff hσ).1 hb)

theorem xuQ_succ (a : Ordinal.{0}) (ha : a + 1 < gcG 1) : xuQ a ≤ xuQ (a + 1) := by
  unfold xuQ
  by_cases h : a < ω
  · rw [if_pos h]; exact zero_le
  · have h1 : ¬ a + 1 < ω := fun h' => h ((lt_add_one a).trans h')
    rw [if_neg h, if_neg h1]; exact xuG_le_succ a ha

theorem xuQ_G : xuQ (gcG 0) = 0 := by
  rw [xuQ_inf (omega0_lt_inE gl_G0_E).le, xuG_G]

theorem xuQ_Om1 : xuQ Om1 = 1 := by rw [xuQ_lowG gl_Om1_lt_G0, wx_glQ_Om1]

theorem xuQ_Om1s : xuQ (Om1 + 1) = 1 := by rw [xuQ_lowG wx_Om1s_lt_G, wx_glQ_Om1s]

theorem xu_glPsi_Om1 {α ι : Ordinal.{0}} (hα1 : 1 ≤ α) (hαG : α < gcG 1) : Om1 < glPsi α ι := by
  rcases lt_or_ge α (gcG 0) with h | h
  · exact (glPsi_gt hα1 h ι).1
  · exact gl_Om1_lt_G0.trans_le (h.trans (left_le_veblen _ _))

theorem xu_glPsi_lt_G1 {α ι : Ordinal.{0}} (hα : α < gcG 1) (hι : ι < gcG 1) : glPsi α ι < gcG 1 := by
  unfold glPsi; exact xu_veb_lt_G1 hα (xuLam_lt_G1 hι)

/-- `glPsi α ι` as an `xuPsi` code when it lies above `G`. -/
theorem xu_glPsi_hi {α ι : Ordinal.{0}} (hα1 : 1 ≤ α) (hαG : α < gcG 1) (hι : ι < gcG 1)
    (hG : gcG 0 < glPsi α ι) : ∃ η, η < gcG 1 ∧ glPsi α ι = xuPsi α η ∧ xuQ η = xuQ ι := by
  by_cases hα : α = gcG 0
  · have hι0 : ι ≠ 0 := by
      rintro rfl
      have : glPsi (gcG 0) 0 = gcG 0 := by
        unfold glPsi
        rw [glLam_of_not (glFw_zero _), glY0_gt gl_Om1_lt_G0, add_zero, Xf.xf_sc_veb0 (gcG_SC 0)]
      rw [hα, this] at hG; exact lt_irrefl _ hG
    have e1 : 1 + (ι - 1) = ι := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hι0)
    refine ⟨ι - 1, (le_add_self.trans_eq e1).trans_lt hι, by rw [hα, xuPsi_G, e1], ?_⟩
    conv_rhs => rw [← e1]
    exact (xuQ_one_add _).symm
  · exact ⟨ι, hι, (xuPsi_ne hα ι).symm, rfl⟩

/-- **THE GATE OF `glPsi α ι` ABOVE `t₀`**: `max 1 (max (xuQ α) (xuQ ι))`. -/
theorem xu_gg_glPsi {α ι : Ordinal.{0}} (hα1 : 1 ≤ α) (hαG : α < gcG 1) (hι : ι < gcG 1)
    (ht : Wj.wjT 0 ≤ glPsi α ι) : xuGg (glPsi α ι) = max 1 (max (xuQ α) (xuQ ι)) := by
  obtain ⟨η, hη, he, hq⟩ := xu_glPsi_hi hα1 hαG hι (xu_G_lt_of ht)
  unfold xuGg
  rw [he, xuG_psi hα1 hαG hη (he ▸ ht), hq]

/-- **The gate of `glPsi α ι` is at most `max 1 (max (xuQ α) (xuQ ι))`** (every value). -/
theorem xu_gg_glPsi_le {α ι : Ordinal.{0}} (hα1 : 1 ≤ α) (hαG : α < gcG 1) (hι : ι < gcG 1) :
    xuGg (glPsi α ι) ≤ max 1 (max (xuQ α) (xuQ ι)) := by
  rcases lt_trichotomy (glPsi α ι) (gcG 0) with hlt | heq | hgt
  · have hαG0 : α < gcG 0 := by
      by_contra h; push Not at h
      exact absurd (h.trans (left_le_veblen α (glLam α ι))) (not_le.2 hlt)
    have hιG0 : ι < gcG 0 := (lt_glPsi α ι).trans hlt
    unfold xuGg
    rw [xuG_lowG hlt, glG_psi hα1 hαG0 hιG0, ← xuQ_lowG hαG0, ← xuQ_lowG hιG0]
  · rw [heq]; unfold xuGg; rw [xuG_G]; exact max_le_max le_rfl zero_le
  · exact (xu_gg_glPsi hα1 hαG hι (xu_t0_le_of (glPsi_E hα1 ι) hgt)).le

theorem xu_ML_glPsi {α ι : Ordinal.{0}} (hα1 : 1 ≤ α) (hαG : α < gcG 1) : ML (glPsi α ι) :=
  ws_ML_E (glPsi_E hα1 ι) (xu_glPsi_Om1 hα1 hαG)

theorem xu_glPsi_lt_lev {α' α : Ordinal.{0}} (hlt : α' < α) (hα1 : 1 ≤ α) (hαG : α < gcG 1)
    {η' η : Ordinal.{0}} : glPsi α' η' < glPsi α η ↔ η' < glPsi α η :=
  ⟨fun h => (lt_glPsi α' η').trans h, fun h =>
    glPsi_lt_of (luP_mono le_add_self (add_one_le_of_lt hlt) (glPsi_P α η)) (xu_glPsi_Om1 hα1 hαG) h⟩

theorem xu_glPsi_lt_lev' {α' α : Ordinal.{0}} (hlt : α < α') (hα'1 : 1 ≤ α') (hα'G : α' < gcG 1)
    {η' η : Ordinal.{0}} : glPsi α' η' < glPsi α η ↔ glPsi α' η' ≤ η := by
  refine ⟨fun h => ?_, fun h => h.trans_lt (lt_glPsi α η)⟩
  by_contra hc
  push Not at hc
  exact absurd ((xu_glPsi_lt_lev hlt hα'1 hα'G).2 hc) (not_lt.2 h.le)

/-- **The data of an `ε`-number code `e ∈ [t₀, Γ(1))` as `glPsi α ι`.** -/
theorem xu_glData {e : Ordinal.{0}} (he : InE e) (ht : Wj.wjT 0 ≤ e) (heB : e < gcG 1) :
    ∃ α ι, 1 ≤ α ∧ α < e ∧ ι < e ∧ glPsi α ι = e ∧ xuQ ι = xuQ (xuI e) ∧ α = xuK e := by
  obtain ⟨h1, h2, h3, h4⟩ := xuData_spec he (xu_G_lt_of ht) heB
  by_cases hα : xuK e = gcG 0
  · refine ⟨xuK e, 1 + xuI e, h1, h2, ?_, ?_, xuQ_one_add _, rfl⟩
    · rcases lt_or_ge (xuI e) ω with hω | hω
      · obtain ⟨n, hn⟩ := lt_omega0.1 hω
        rw [hn]
        exact (show (1 : Ordinal.{0}) + n < ω by exact_mod_cast natCast_lt_omega0 (1 + n)).trans
          (omega0_lt_inE he)
      · rw [one_add_of_omega0_le hω]; exact h3
    · have h4' := h4
      rw [hα, xuPsi_G] at h4'
      rw [hα]; exact h4'
  · exact ⟨xuK e, xuI e, h1, h2, h3, by rw [← xuPsi_ne hα, h4], rfl, rfl⟩

/-- **The gate of an `ε`-number code `e ≥ t₀` through any `glPsi` form.** -/
theorem xu_gg_of_glPsi {e α ι : Ordinal.{0}} (he : InE e) (ht : Wj.wjT 0 ≤ e) (heB : e < gcG 1)
    (hα1 : 1 ≤ α) (hαe : α < e) (hιe : ι < e) (hpe : glPsi α ι = e) : xuGg e = max 1 (max (xuQ α) (xuQ ι)) := by
  rw [← hpe]; exact xu_gg_glPsi hα1 (hαe.trans heB) (hιe.trans heB) (hpe ▸ ht)

/-! ## The bracket data of a code `b ≥ t₀` -/

theorem xu_bdat {b σ : Ordinal.{0}} (hσ : InE σ) (h1 : Wj.wjT 0 ≤ b) (h2 : b < gcG 1) (hg : xuGg b < σ) :
    ∃ α ι, 1 ≤ α ∧ α < gcG 1 ∧ ι < gcG 1 ∧ glPsi α ι = guE b ∧ xuGg α < σ ∧ xuGg ι < σ ∧
      xuGg (guE b) < σ ∧ guE b ≤ b ∧ ι < b := by
  have hEt := xu_E_ge h1
  have hEb := gl_E_le (xu_gfE_le h1)
  have hEB := xu_E_lt h1 h2
  obtain ⟨α, ι, hα1, hαe, hιe, hpe, hq, hK⟩ := xu_glData (guE_E b) hEt hEB
  have hdec := xuG_dec h1 h2
  have hQE : xuQE (guE b) ≤ xuG b := by rw [hdec]; exact le_max_of_le_left (le_max_left _ _)
  refine ⟨α, ι, hα1, hαe.trans hEB, hιe.trans hEB, hpe, ?_, ?_, ?_, hEb, hιe.trans_le hEb⟩
  · rw [hK]; exact xu_gg_part hσ ((le_max_left _ _).trans hQE) hg
  · exact xu_gg_part hσ (by rw [hq]; exact (le_max_right _ _).trans hQE) hg
  · refine xu_gg_part hσ ?_ hg
    rw [xuQ_inf (omega0_lt_inE (guE_E b)).le, xuG_base (guE_E b) hEt hEB]; exact hQE

/-! ## The recursion for gate-cofinality -/

/-- **GATE-COFINALITY BY RECURSION**: if one member `T μ₀` is at least `t₀`, and every code `b ∈ [t₀, e)` with gate
below `σ` has its bracket below some `T μ` (given the same for the smaller codes), then so has every code `b < e`. -/
theorem xu_rec {e σ : Ordinal.{0}} (hσ : InE σ) (T : Ordinal.{0} → Ordinal.{0})
    (hT : ∀ μ, μ < σ → InE (T μ) ∧ Om1 < T μ) (hT0 : ∃ μ, μ < σ ∧ Wj.wjT 0 ≤ T μ)
    (step : ∀ b, Wj.wjT 0 ≤ b → b < e → xuGg b < σ →
      (∀ b', b' < b → xuGg b' < σ → ∃ μ, μ < σ ∧ b' < T μ) → ∃ μ, μ < σ ∧ guE b < T μ) :
    ∀ b, b < e → xuGg b < σ → ∃ μ, μ < σ ∧ b < T μ := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b ih =>
  intro hb hg
  rcases lt_or_ge b (Wj.wjT 0) with h | h
  · obtain ⟨μ, hμ, hT0'⟩ := hT0
    exact ⟨μ, hμ, h.trans_le hT0'⟩
  · obtain ⟨μ, hμ, hlt⟩ := step b h hb hg (fun b' hb' hg' => ih b' hb' (hb'.trans hb) hg')
    exact ⟨μ, hμ, (gl_lt_eN (xu_gfE_le h)).trans_le (eN_le hlt (hT μ hμ).1)⟩

/-! ## Sequences below `t₀` and the base `t₀` -/

section Cls

variable {B : Ordinal.{0}} (hBE : InE B) (hBt : Wj.wjT 0 ≤ B) (hB1 : B < gcG 1)

/-- **An `xcA3` classification below `t₀` is an `xuC` classification** (the gates agree below `t₀`). -/
theorem xu_cls_of_xc {M : Ordinal.{0} → Prop} {c : Ordinal.{0}} (hc : c < Wj.wjT 0) (h : XCls xcA3 M c) :
    XCls (xuC B hBE hBt hB1) M c := by
  rcases h with ⟨cs, h1, h2, h3, h4, h5⟩ | ⟨s, ⟨s1, s2, s3, s4⟩, hM⟩
  · refine Or.inl ⟨cs, h1, h2, h3, h4, fun k => ?_⟩
    show xuGg (cs k) ≤ xuGg c
    rw [xuGg_low ((h3 k).trans hc), xuGg_low hc]; exact h5 k
  · refine Or.inr ⟨s, ⟨s1, s2, fun x hx hx1 hg μ hμ => ?_, fun σ hσ hσ1 b hb hg => ?_⟩, hM⟩
    · show xuGg (s μ) < x
      rw [xuGg_low ((s1 μ (hμ.trans hx1)).2.trans hc)]
      exact s3 x hx hx1 (by show xg c < x; rw [← xuGg_low hc]; exact hg) μ hμ
    · exact s4 σ hσ hσ1 b hb (by show xg b < σ; rw [← xuGg_low (hb.trans hc)]; exact hg)

/-- **THE BASE `t₀`**: the towers `G^{⋯^G}` (`Wt.wtTw`), gate `1 = xuGg t₀`. -/
theorem xu_base_t0 : XCls (xuC B hBE hBt hB1) ML (Wj.wjT 0) := by
  refine Or.inl ⟨wtTw, fun k => ⟨(gl_Om1_lt_G0.trans (wtTw_G k)).le, wtTw_dvd k⟩, wtTw_strict, wtTw_lt,
    fun t ht => wtTw_cof ht, fun k => ?_⟩
  show xuGg (wtTw k) ≤ xuGg (Wj.wjT 0)
  rw [xuGg_low (wtTw_lt k), xg_tw]
  unfold xuGg; rw [xuG_t0]; exact le_max_left _ _

end Cls

/-! ## The tower over an `ε`-number code `f ≥ t₀` -/

section Tw

variable {f : Ordinal.{0}} (hf : InE f) (hft : Wj.wjT 0 ≤ f) (hNG : eN f < gcG 1)
include hf hft hNG

theorem xu_tw_gate : ∀ k : ℕ, xuG (woU f (k + 1)) ≤ xuQE f
  | 0 => by rw [ws_tw_one hf, xuG_base hf hft ((lt_eN f).trans hNG)]
  | k + 1 => by
    have ht0 : woU f (k + 1) ≠ 0 := (hf.pos.trans_le (ws_tw_ge hf k)).ne'
    have hN : f ^ woU f (k + 1) * 1 + 0 < eN f := by rw [mul_one, add_zero]; exact woU_lt_eN hf (k + 2)
    have h := xuG_cnf hf hft ht0 one_ne_zero (Lu.lu_one_lt_E hf) (opow_pos _ hf.pos) hN (hN.trans hNG)
    rw [mul_one, add_zero] at h
    show xuG (f ^ woU f (k + 1)) ≤ _
    rw [h, xuQ_one, xuG_zero, max_self, max_eq_left zero_le]
    exact max_le le_rfl ((xuQ_le _).trans (xu_tw_gate k))

/-- **THE BASE `ε_{f+1}` FROM THE TOWER OVER `f ≥ t₀`**, when `max 1 (xuQE f) ≤ xuGg ε_{f+1}`. -/
theorem xu_base_succE {B : Ordinal.{0}} (hBE : InE B) (hBt : Wj.wjT 0 ≤ B) (hB1 : B < gcG 1)
    (hg : max 1 (xuQE f) ≤ xuGg (eN f)) : XCls (xuC B hBE hBt hB1) ML (eN f) := by
  have hOf : Om1 < f := xu_Om1_lt_t0.trans_le hft
  refine Or.inl ⟨fun k => woU f (k + 2), fun k => ?_, fun k => ws_tw_lt hf (k + 1),
    fun k => woU_lt_eN hf (k + 2), fun t ht => ?_, fun k => ?_⟩
  · have := ws_ML_mul (q := 1) hf hOf (hf.pos.trans_le (ws_tw_ge hf k)).ne' zero_lt_one
    rwa [mul_one] at this
  · obtain ⟨k, hk⟩ := woU_cof hf ht
    exact ⟨k, hk.trans_le ((ws_tw_le hf k).trans (ws_tw_le hf (k + 1)))⟩
  · exact (max_le_max le_rfl (xu_tw_gate hf hft hNG (k + 1))).trans hg

end Tw

end Googology.Trans.PoR.InaccPsi.R2.Xu
