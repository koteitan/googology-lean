import Googology.Trans.PoR.InaccPsi.R2.XuBase2

/-!
# XuBase3: THE `ε`-NUMBER BASES OF REGION (A3), case (II) and the base theorem

`xu_base_one` (`α = 1`: `e = ε_{f+1}`, `f = G` gives `t₀`, `f ≥ t₀` the towers over `f`), `xu_base_succ`
(`α = α'+1`, `α' ≥ 1`: the iterates of `φ(α', ·)` over `f + 1`), `xu_base_lim` (`α` a limit: `φ(α_k, f+1)` /
`φ(s μ, f+1)`), `xu_base` (**EVERY `ε`-NUMBER CODE `e ∈ [t₀, Γ(1))` HAS A SEQUENCE OF LEVELS**, given the sequences of
the smaller limit codes).

No new axiom, no new definition.
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
  Googology.Trans.PoR.InaccPsi.R2.Gv

namespace Googology.Trans.PoR.InaccPsi.R2.Xu

section Base

variable {B : Ordinal.{0}} (hBE : InE B) (hBt : Wj.wjT 0 ≤ B) (hB1 : B < gcG 1)

section CaseII

variable {α ι f : Ordinal.{0}} (hα1 : 1 ≤ α) (hαG : α < gcG 1) (hιG : ι < gcG 1)
  (ht : Wj.wjT 0 ≤ glPsi α ι) (hpk : XuPkg α ι f)
include hα1 hαG hιG ht hpk

/-- **THE SUCCESSOR LEVEL `α'+1`, `α' ≥ 1`: THE ITERATES OF `φ(α', ·)` OVER `f + 1`.** -/
theorem xu_base_succ {α' : Ordinal.{0}} (hα : α = α' + 1) (hα'1 : 1 ≤ α') :
    XCls (xuC B hBE hBt hB1) ML (glPsi α ι) := by
  subst hα
  obtain ⟨hpre, hOf, hfc, hgf, hfG⟩ := hpk
  set e := glPsi (α' + 1) ι with he_def
  have hα'G : α' < gcG 1 := (lt_add_one α').trans hαG
  have heG : e < gcG 1 := xu_glPsi_lt_G1 hαG hιG
  set cs : ℕ → Ordinal.{0} := fun k => (veblen α')^[k + 1] (f + 1) with hcs
  have hcs_s : ∀ k : ℕ, cs (k + 1) = veblen α' (cs k) := fun k => Function.iterate_succ_apply' _ _ _
  have hcs0 : cs 0 = veblen α' (f + 1) := rfl
  have hlt : ∀ k, cs k < e := fun k => wx_pre_succ_lt hpre (k + 1)
  have hE : ∀ k, InE (cs k) := fun k => by
    show InE ((veblen α')^[k + 1] (f + 1))
    rw [Function.iterate_succ_apply']; exact luP_E hα'1 (luP_veblen _ _)
  have hge : ∀ k : ℕ, f + 1 ≤ (veblen α')^[k] (f + 1) := by
    intro k; induction k with
    | zero => exact le_rfl
    | succ k ih => rw [Function.iterate_succ_apply']; exact ih.trans (right_le_veblen _ _)
  have hO : ∀ k, Om1 < cs k := fun k => (Order.lt_add_one_iff.2 hOf).trans_le (hge (k + 1))
  have hnofix : ∀ k : ℕ, veblen α' ((veblen α')^[k] (f + 1)) ≠ (veblen α')^[k] (f + 1) := by
    intro k; induction k with
    | zero => exact wx_veb_succ_ne α' f
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact fun h => ih ((veblen_injective α') h)
  have hnP : ∀ k, ¬ LuP (α' + 1) (cs k) := fun k h => hnofix (k + 1) (luP_succ.1 h)
  have hstr : ∀ k, cs k < cs (k + 1) := fun k => by
    rw [hcs_s]; exact lt_of_le_of_ne (right_le_veblen _ _) (fun h => hnP k (luP_succ.2 h.symm))
  have hQα : xuQ α' ≤ xuGg e := by
    rw [he_def, xu_gg_glPsi hα1 hαG hιG ht]
    exact le_max_of_le_right (le_max_of_le_left (xuQ_succ α' hαG))
  have hgate : ∀ k, xuGg (cs k) ≤ xuGg e := by
    intro k; induction k with
    | zero =>
      rw [hcs0]
      refine (xu_gh_veb hα'1 hα'G hfG (xu_f_cases ⟨hpre, hOf, hfc, hgf, hfG⟩ le_rfl)).trans ?_
      exact max_le (xu_one_le_gg _) (max_le hQα ((le_max_right _ _).trans hgf))
    | succ k ih =>
      rw [hcs_s, wx_veb_psi (hE k) (hO k) (hnP k)]
      refine (xu_gg_glPsi_le hα'1 hα'G ((hlt k).trans heG)).trans ?_
      exact max_le (xu_one_le_gg _) (max_le hQα ((xuQ_le_gg _).trans ih))
  refine Or.inl ⟨cs, fun k => ws_ML_E (hE k) (hO k), hstr, hlt, fun t ht' => ?_, hgate⟩
  exact wx_pre_succ_cof hpre ht'

/-- **THE LEVEL `1`**: `e = ε_{f+1}`: `t₀` itself (`f = G`), or the towers over `f ≥ t₀`. -/
theorem xu_base_one (hα : α = 1) : XCls (xuC B hBE hBt hB1) ML (glPsi α ι) := by
  subst hα
  obtain ⟨hpre, hOf, hfc, hgf, hfG⟩ := hpk
  rcases hpre with ⟨y, he, rfl⟩ | ⟨-, -, h⟩
  · have hev : glPsi 1 ι = eN (veblen 1 y) := by rw [he, go_eN_veb]
    rcases hfc with h | ⟨hOf', hP⟩
    · exfalso
      rw [hev, h] at ht
      exact absurd (ht.trans (eN_le gl_Om1_lt_G0 gl_G0_E)) (not_le.2 xu_G_lt_t0)
    · have hfE : InE (veblen 1 y) := luP_E le_rfl hP
      have hGf : gcG 0 ≤ veblen 1 y := by
        by_contra hc; push Not at hc
        have h1 : eN (veblen 1 y) ≤ gcG 0 := eN_le hc gl_G0_E
        rw [← hev] at h1
        exact absurd (xu_G_lt_of ht) (not_lt.2 h1)
      rcases hGf.lt_or_eq with hGf | hGf
      · have hft := xu_t0_le_of hfE hGf
        rw [hev]
        refine xu_base_succE hfE hft (by rw [← hev]; exact xu_glPsi_lt_G1 hαG hιG) hBE hBt hB1 ?_
        rw [← hev]
        have : xuQ (veblen 1 y) = xuQE (veblen 1 y) := by
          rw [xuQ_inf (omega0_lt_inE hfE).le, xuG_base hfE hft (hfG)]
        rw [← this]; exact hgf
      · rw [hev, ← hGf, ← xu_t0_eN]; exact xu_base_t0 hBE hBt hB1
  · exact absurd (h.trans_le le_rfl) (not_lt.2 (one_lt_omega0.trans omega_lt_Om1).le)

/-- **THE LIMIT LEVEL `α`**: `φ(α_k, f+1)` / `φ(s μ, f+1)` from the sequence of `α`. -/
theorem xu_base_lim (hl : IsSuccLimit α) (hαs : XCls (xuC B hBE hBt hB1) (fun _ => True) α) :
    XCls (xuC B hBE hBt hB1) ML (glPsi α ι) := by
  obtain ⟨hpre, hOf, hfc, hgf, hfG⟩ := hpk
  set e := glPsi α ι with he_def
  have hα0 : α ≠ 0 := hl.ne_bot
  have hge : xuGg e = max 1 (max (xuQ α) (xuQ ι)) := xu_gg_glPsi hα1 hαG hιG ht
  have hghα : xuGg α ≤ xuGg e := by
    rw [xu_gg_lim hl, hge]; exact max_le_max le_rfl (le_max_left _ _)
  have hcase : ∀ β, β < α → f = Om1 ∨ glF β f := fun β hβ =>
    xu_f_cases ⟨hpre, hOf, hfc, hgf, hfG⟩ (Order.add_one_le_of_lt hβ)
  have hgβ : ∀ β, 1 ≤ β → β < α → xuGg β ≤ xuGg e → xuGg (veblen β (f + 1)) ≤ xuGg e := by
    intro β hβ1 hβα hgb
    refine (xu_gh_veb hβ1 (hβα.trans hαG) hfG (hcase β hβα)).trans ?_
    exact max_le (xu_one_le_gg _) (max_le ((xuQ_le_gg _).trans hgb) ((le_max_right _ _).trans hgf))
  have hMLv : ∀ β, 1 ≤ β → ML (veblen β (f + 1)) := fun β hβ1 =>
    ws_ML_E (luP_E hβ1 (luP_veblen _ _)) ((Order.lt_add_one_iff.2 hOf).trans_le (right_le_veblen _ _))
  rcases hαs with ⟨as, -, h2, h3, h4, h5⟩ | ⟨s, ⟨s1, s2, s3, s4⟩, -⟩
  · have hpos : ∀ k, 1 ≤ as (k + 1) := fun k => Order.one_le_iff_pos.2 (zero_le.trans_lt (h2 k))
    refine Or.inl ⟨fun k => veblen (as (k + 1)) (f + 1), fun k => hMLv _ (hpos k),
      fun k => wx_veb_lt_left (h2 (k + 1)) f, fun k => wx_pre_lim_lt hα0 hpre (h3 (k + 1)),
      fun t ht' => ?_, fun k => hgβ _ (hpos k) (h3 (k + 1)) ((h5 (k + 1)).trans hghα)⟩
    obtain ⟨β, hβ, htβ⟩ := wx_pre_lim_cof hl hpre ht'
    obtain ⟨k, hk⟩ := h4 β hβ
    exact ⟨k, htβ.trans_le (veblen_left_monotone (f + 1) (hk.trans (h2 k)).le)⟩
  · have hmono : ∀ μ' μ, μ' ≤ μ → μ < Om1 → s μ' ≤ s μ := fun μ' μ h hμ => by
      rcases h.lt_or_eq with h | rfl
      · exact (s2 μ' μ h hμ).le
      · exact le_rfl
    refine Or.inr ⟨fun μ => veblen (s μ) (f + 1), ⟨fun μ hμ => ⟨Order.one_le_iff_pos.2 veblen_pos,
      wx_pre_lim_lt hα0 hpre (s1 μ hμ).2⟩, fun μ' μ h hμ => wx_veb_lt_left (s2 μ' μ h hμ) f,
      fun x hx hx1 hgx μ hμ => ?_, fun σ hσ hσ1 b hb hgb => ?_⟩, fun μ hμ => hMLv _ (s1 μ hμ).1⟩
    · change xuGg e < x at hgx
      show xuGg (veblen (s μ) (f + 1)) < x
      have hsμ := s1 μ (hμ.trans hx1)
      refine (xu_gh_veb hsμ.1 (hsμ.2.trans hαG) hfG (hcase _ hsμ.2)).trans_lt ?_
      exact max_lt (wo_one_lt_inE hx) (max_lt ((xuQ_le_gg _).trans_lt (s3 x hx hx1 (hghα.trans_lt hgx) μ hμ))
        ((le_max_right _ _).trans_lt (hgf.trans_lt hgx)))
    · change xuGg b < σ at hgb
      have h1σ : (1 : Ordinal.{0}) < σ := wo_one_lt_inE hσ
      have hT0 : ∃ μ, μ < σ ∧ Wj.wjT 0 ≤ veblen (s μ) (f + 1) := by
        rcases lt_or_ge f (gcG 0) with hfG0 | hfG0
        · -- `f < G` forces `G < α`
          have hGα : gcG 0 < α := by
            rcases lt_trichotomy α (gcG 0) with h | h | h
            · exfalso
              rcases hpre with ⟨y, he, rfl⟩ | ⟨he, -, -⟩
              · have hy : y + 1 < gcG 0 :=
                  gl_G0_lim.add_one_lt ((right_le_veblen α y).trans_lt hfG0)
                have := gl_veb_lt_G0 h hy
                rw [← he] at this
                exact absurd (xu_G_lt_of ht) (not_lt.2 this.le)
              · have := gl_veb_lt_G0 h gl_G0_E.pos
                rw [← he] at this
                exact absurd (xu_G_lt_of ht) (not_lt.2 this.le)
            · exfalso
              rcases hpre with ⟨y, he, rfl⟩ | ⟨he, -, -⟩
              · rw [h] at hfG0
                exact absurd ((left_le_veblen _ _).trans_lt hfG0) (lt_irrefl _)
              · rw [he, h, Xf.xf_sc_veb0 (gcG_SC 0)] at ht
                exact absurd ht (not_le.2 xu_G_lt_t0)
            · exact h
          obtain ⟨μ, hμ, hlt⟩ := s4 σ hσ hσ1 _ hGα (by show xuGg _ < σ; rw [xu_gg_G]; exact h1σ)
          exact ⟨μ, hμ, xu_t0_le_of (luP_E (s1 μ (hμ.trans hσ1)).1 (luP_veblen _ _))
            (hlt.trans_le (left_le_veblen _ _))⟩
        · refine ⟨0, hσ.pos, xu_t0_le_of (luP_E (s1 0 gv_Om1_pos).1 (luP_veblen _ _)) ?_⟩
          exact (Order.lt_add_one_iff.2 hfG0).trans_le (right_le_veblen _ _)
      refine xu_rec hσ (fun μ => veblen (s μ) (f + 1)) (fun μ hμ => ⟨luP_E (s1 μ (hμ.trans hσ1)).1
        (luP_veblen _ _), (Order.lt_add_one_iff.2 hOf).trans_le (right_le_veblen _ _)⟩) hT0
        (fun b hEb hbe hgb' IH => ?_) b hb hgb
      obtain ⟨αb, ιb, d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ :=
        xu_bdat hσ hEb (hbe.trans (xu_glPsi_lt_G1 hαG hιG)) hgb'
      rcases lt_or_ge αb α with hlt | hge'
      · obtain ⟨μ1, hμ1, hlt1⟩ := s4 σ hσ hσ1 _ hlt d5
        obtain ⟨μ2, hμ2, hlt2⟩ := IH _ d9 d6
        refine ⟨max μ1 μ2, max_lt hμ1 hμ2, ?_⟩
        have hm : max μ1 μ2 < Om1 := (max_lt hμ1 hμ2).trans hσ1
        have hk : αb < s (max μ1 μ2) := hlt1.trans_le (hmono _ _ (le_max_left _ _) hm)
        have hT : ιb < veblen (s (max μ1 μ2)) (f + 1) :=
          hlt2.trans_le (veblen_left_monotone (f + 1) (hmono _ _ (le_max_right _ _) hm))
        rw [← d4]
        exact glPsi_lt_of (luP_mono le_add_self (Order.add_one_le_of_lt hk) (luP_veblen _ _))
          ((Order.lt_add_one_iff.2 hOf).trans_le (right_le_veblen _ _)) hT
      · have hP : LuP α (guE b) := by rw [← d4]; exact luP_mono hα1 hge' (glPsi_P _ _)
        have hle : guE b ≤ f := wx_pre_below hpre hP (d8.trans_lt hbe)
        exact ⟨0, hσ.pos, (Order.lt_add_one_iff.2 hle).trans_le (right_le_veblen _ _)⟩

end CaseII

/-- **EVERY `ε`-NUMBER CODE `e ∈ [t₀, Γ(1))` HAS A SEQUENCE OF LEVELS**, given the sequences of the smaller limit
codes.  ONE proof for every Veblen level. -/
theorem xu_base {e : Ordinal.{0}} (he : InE e) (ht : Wj.wjT 0 ≤ e) (heB : e < gcG 1)
    (IH : ∀ c, c < e → IsSuccLimit c → XCls (xuC B hBE hBt hB1) (fun _ => True) c) :
    XCls (xuC B hBE hBt hB1) ML e := by
  obtain ⟨α, ι, hα1, hαe, hιe, hpe, -, -⟩ := xu_glData he ht heB
  have hαG : α < gcG 1 := hαe.trans heB
  have hιG : ι < gcG 1 := hιe.trans heB
  have ht' : Wj.wjT 0 ≤ glPsi α ι := hpe ▸ ht
  rw [← hpe]
  by_cases hI : IsSuccLimit ι ∧ ¬ glFw α ι
  · exact xu_base_I hBE hBt hB1 hα1 hαG hιG hI.1 hI.2 ht' (IH ι hιe hI.1)
  obtain ⟨f, hpk⟩ := xu_pkg hα1 hαG hιG ht' hI
  rcases zero_or_succ_or_isSuccLimit α with h0 | ⟨α', hα'⟩ | hl
  · exact absurd (h0 ▸ hα1) (not_le.2 zero_lt_one)
  · rw [Order.succ_eq_add_one] at hα'
    rcases eq_or_ne α' 0 with h0 | h0
    · exact xu_base_one hBE hBt hB1 hα1 hαG hιG ht' hpk (by rw [← hα', h0, zero_add])
    · exact xu_base_succ hBE hBt hB1 hα1 hαG hιG ht' hpk hα'.symm (Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 h0))
  · exact xu_base_lim hBE hBt hB1 hα1 hαG hιG ht' hpk hl (IH α hαe hl)

end Base

end Googology.Trans.PoR.InaccPsi.R2.Xu
