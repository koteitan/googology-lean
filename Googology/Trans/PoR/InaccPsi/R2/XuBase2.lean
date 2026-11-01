import Googology.Trans.PoR.InaccPsi.R2.XuBase

/-!
# XuBase2: THE `ε`-NUMBER BASES OF REGION (A3) ABOVE `t₀`, the two cases

`xu_base_I` (a limit argument), `XuPkg` / `xu_pkg` (the predecessor `f`), `xu_base_one` (`α = 1`),
`xu_base_succ` (`α = α'+1`, `α' ≥ 1`), `xu_base_lim` (`α` a limit), and `xu_base` (**EVERY `ε`-NUMBER CODE
`e ∈ [t₀, Γ(1))` HAS A SEQUENCE OF LEVELS**, given the sequences of the smaller limit codes; one proof for every
Veblen level).  The argument of `R2.WxBase` with the gate `xuGg` of `Xu.xuC`.

No new axiom.  New definition: `XuPkg`.
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

theorem xu_G_fw {α : Ordinal.{0}} (hα : α < gcG 0) : glFw α (gcG 0) :=
  ⟨gcG 0, ⟨luP_succ.2 (gn_veb_fix (gcG_SC 0) hα), gl_Om1_lt_G0⟩, 0, by rw [Nat.cast_zero, add_zero]⟩

theorem xu_gg_G : xuGg (gcG 0) = 1 := by unfold xuGg; rw [xuG_G, max_eq_left zero_le]

/-- **The gate of `φ(β, f+1)`** for `f = Ω₁` or `f ∈ F_β`. -/
theorem xu_gh_veb {β f : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβG : β < gcG 1) (hfG : f < gcG 1)
    (hf : f = Om1 ∨ glF β f) : xuGg (veblen β (f + 1)) ≤ max 1 (max (xuQ β) (xuQ f)) := by
  rcases hf with rfl | hf
  · rcases lt_or_ge β Om1 with h | h
    · rw [wx_veb_Om_lt h]
      refine (xu_gg_glPsi_le hβ1 hβG xu_G1_E.pos).trans ?_
      rw [xuQ_zero, xuQ_Om1]; exact max_le_max le_rfl (max_le_max le_rfl zero_le)
    · rw [wx_veb_Om_ge h]
      refine (xu_gg_glPsi_le hβ1 hβG (xu_G1_lim.add_one_lt xu_Om1_lt_G1)).trans ?_
      rw [xuQ_Om1s, xuQ_Om1]
  · rw [wx_veb_F hf]; exact xu_gg_glPsi_le hβ1 hβG hfG

section Base

variable {B : Ordinal.{0}} (hBE : InE B) (hBt : Wj.wjT 0 ≤ B) (hB1 : B < gcG 1)

/-! ## Case (I): a limit argument -/

section CaseI

variable {α ι : Ordinal.{0}} (hα1 : 1 ≤ α) (hαG : α < gcG 1) (hιG : ι < gcG 1) (hl : IsSuccLimit ι)
  (hnf : ¬ glFw α ι) (ht : Wj.wjT 0 ≤ glPsi α ι)
include hα1 hαG hιG hl hnf ht

/-- **CASE (I)**: `ι` a limit, `¬ glFw α ι`: the sequence of `glPsi α ι` from that of `ι`. -/
theorem xu_base_I (hι : XCls (xuC B hBE hBt hB1) (fun _ => True) ι) :
    XCls (xuC B hBE hBt hB1) ML (glPsi α ι) := by
  have hge : xuGg (glPsi α ι) = max 1 (max (xuQ α) (xuQ ι)) := xu_gg_glPsi hα1 hαG hιG ht
  have hghι : xuGg ι ≤ xuGg (glPsi α ι) := by
    rw [xu_gg_lim hl, hge]; exact max_le_max le_rfl (le_max_right _ _)
  have hQα : xuQ α ≤ xuGg (glPsi α ι) := by rw [hge]; exact le_max_of_le_right (le_max_left _ _)
  rcases hι with ⟨cs, -, h2, h3, h4, h5⟩ | ⟨s, ⟨s1, s2, s3, s4⟩, -⟩
  · refine Or.inl ⟨fun k => glPsi α (cs k), fun k => xu_ML_glPsi hα1 hαG,
      fun k => glPsi_strictMono α (h2 k), fun k => glPsi_strictMono α (h3 k), fun t ht' => ?_, fun k => ?_⟩
    · obtain ⟨η', hη', ht''⟩ := wx_psi_cont hl hnf ht'
      obtain ⟨k, hk⟩ := h4 η' hη'
      exact ⟨k, ht''.trans (glPsi_strictMono α hk)⟩
    · show xuGg _ ≤ xuGg _
      exact (xu_gg_glPsi_le hα1 hαG ((h3 k).trans hιG)).trans
        (max_le (xu_one_le_gg _) (max_le hQα ((xuQ_le_gg _).trans ((h5 k).trans hghι))))
  · refine Or.inr ⟨fun μ => glPsi α (s μ), ⟨fun μ hμ => ⟨(xu_one_lt_inE (glPsi_E hα1 _)).le,
      glPsi_strictMono α (s1 μ hμ).2⟩, fun μ' μ h hμ => glPsi_strictMono α (s2 μ' μ h hμ),
      fun x hx hx1 hgx μ hμ => ?_, fun σ hσ hσ1 b hb hgb => ?_⟩, fun μ _ => xu_ML_glPsi hα1 hαG⟩
    · change xuGg (glPsi α ι) < x at hgx
      show xuGg (glPsi α (s μ)) < x
      have hsμ := s1 μ (hμ.trans hx1)
      refine (xu_gg_glPsi_le hα1 hαG (hsμ.2.trans hιG)).trans_lt ?_
      exact max_lt (wo_one_lt_inE hx) (max_lt (hQα.trans_lt hgx)
        ((xuQ_le_gg _).trans_lt (s3 x hx hx1 (hghι.trans_lt hgx) μ hμ)))
    · change xuGg b < σ at hgb
      have h1σ : (1 : Ordinal.{0}) < σ := wo_one_lt_inE hσ
      have hT0 : ∃ μ, μ < σ ∧ Wj.wjT 0 ≤ glPsi α (s μ) := by
        rcases lt_or_ge α (gcG 0) with hαG0 | hαG0
        · have hGι : gcG 0 < ι := by
            rcases lt_trichotomy ι (gcG 0) with h | h | h
            · exact absurd (xu_G_lt_of ht) (not_lt.2 (glPsi_lt_G hαG0 h).le)
            · exact absurd (h ▸ xu_G_fw hαG0) hnf
            · exact h
          obtain ⟨μ, hμ, hlt⟩ := s4 σ hσ hσ1 _ hGι (by show xuGg _ < σ; rw [xu_gg_G]; exact h1σ)
          exact ⟨μ, hμ, xu_t0_le_of (glPsi_E hα1 _) (hlt.trans (lt_glPsi α _))⟩
        · refine ⟨0, hσ.pos, xu_t0_le_of (glPsi_E hα1 _) ?_⟩
          rcases hαG0.lt_or_eq with h | h
          · unfold glPsi
            exact h.trans_le ((xu_veb_zero_gt h hαG).le.trans ((veblen_le_veblen_iff_right).2 zero_le))
          · rw [← h]; unfold glPsi
            have hs0 : 0 < glLam (gcG 0) (s 0) :=
              lt_of_lt_of_le zero_lt_one ((s1 0 gv_Om1_pos).1.trans (glLam_ge _ _))
            exact (left_le_veblen _ _).trans_lt ((veblen_lt_veblen_iff_right).2 hs0)
      refine xu_rec hσ (fun μ => glPsi α (s μ)) (fun μ _ => ⟨glPsi_E hα1 _, xu_glPsi_Om1 hα1 hαG⟩) hT0
        (fun b hEb hbe hgb' IH => ?_) b hb hgb
      obtain ⟨αb, ιb, d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ :=
        xu_bdat hσ hEb (hbe.trans (xu_glPsi_lt_G1 hαG hιG)) hgb'
      have heb : guE b < glPsi α ι := d8.trans_lt hbe
      rcases lt_trichotomy αb α with hlt | heq | hgt
      · obtain ⟨μ, hμ, hlt'⟩ := IH _ d9 d6
        refine ⟨μ, hμ, ?_⟩
        rw [← d4]; exact (xu_glPsi_lt_lev hlt hα1 hαG).2 hlt'
      · rw [← d4, heq] at heb
        have hηb : ιb < ι := glPsi_lt_iff.1 heb
        obtain ⟨μ, hμ, hlt'⟩ := s4 σ hσ hσ1 _ hηb d6
        refine ⟨μ, hμ, ?_⟩
        rw [← d4, heq]; exact glPsi_lt_iff.2 hlt'
      · rw [← d4] at heb
        have hle : glPsi αb ιb ≤ ι := (xu_glPsi_lt_lev' hgt d1 d2).1 heb
        rw [d4] at hle
        have hne : guE b ≠ ι := by
          intro he
          refine hnf ⟨ι, ⟨?_, ?_⟩, 0, by rw [Nat.cast_zero, add_zero]⟩
          · rw [← he, ← d4]
            exact luP_mono (le_add_self) (add_one_le_of_lt hgt) (glPsi_P _ _)
          · rw [← he]; exact gl_Om1_lt_E (xu_gfE_le hEb)
        obtain ⟨μ, hμ, hlt'⟩ := s4 σ hσ hσ1 _ (lt_of_le_of_ne hle hne) d7
        exact ⟨μ, hμ, hlt'.trans (lt_glPsi α _)⟩

end CaseI

end Base

/-! ## The predecessor `f` -/

/-- **The predecessor package** of `glPsi α ι` (`≥ t₀`). -/
def XuPkg (α ι f : Ordinal.{0}) : Prop :=
  WxPre α (glPsi α ι) f ∧ Om1 ≤ f ∧ (f = Om1 ∨ (Om1 < f ∧ LuP α f)) ∧ max 1 (xuQ f) ≤ xuGg (glPsi α ι) ∧
    f < gcG 1

/-- **Every node whose argument is not a limit has a predecessor package.** -/
theorem xu_pkg {α ι : Ordinal.{0}} (hα1 : 1 ≤ α) (hαG : α < gcG 1) (hιG : ι < gcG 1)
    (ht : Wj.wjT 0 ≤ glPsi α ι) (hI : ¬ (IsSuccLimit ι ∧ ¬ glFw α ι)) : ∃ f, XuPkg α ι f := by
  have hge : xuGg (glPsi α ι) = max 1 (max (xuQ α) (xuQ ι)) := xu_gg_glPsi hα1 hαG hιG ht
  have hOm : max 1 (xuQ Om1) ≤ xuGg (glPsi α ι) := by rw [xuQ_Om1, max_self]; exact xu_one_le_gg _
  rcases zero_or_succ_or_isSuccLimit ι with h0 | ⟨ι'', hs⟩ | hl
  · subst h0
    refine ⟨Om1, ?_, le_rfl, Or.inl rfl, hOm, xu_Om1_lt_G1⟩
    unfold glPsi
    rw [glLam_of_not (glFw_zero α), add_zero]
    rcases lt_trichotomy α Om1 with h | h | h
    · exact Or.inl ⟨Om1, by rw [glY0_lt h], (gl_veb_Om1 h).symm⟩
    · subst h; exact Or.inl ⟨0, by rw [glY0_eq, zero_add], gl_veb_Om1_zero.symm⟩
    · exact Or.inr ⟨by rw [glY0_gt h], rfl, h⟩
  · rw [Order.succ_eq_add_one] at hs
    subst hs
    have hι''G : ι'' < gcG 1 := (lt_add_one ι'').trans hιG
    refine ⟨glPsi α ι'', Or.inl ⟨glLam α ι'', by unfold glPsi; rw [wx_lam_succ], rfl⟩,
      (xu_glPsi_Om1 hα1 hαG).le, Or.inr ⟨xu_glPsi_Om1 hα1 hαG, glPsi_P α ι''⟩, ?_,
      xu_glPsi_lt_G1 hαG hι''G⟩
    rw [xuQ_inf (omega0_lt_inE (glPsi_E hα1 ι'')).le, hge]
    show xuGg (glPsi α ι'') ≤ _
    exact (xu_gg_glPsi_le hα1 hαG hι''G).trans (max_le_max le_rfl (max_le_max le_rfl (xuQ_succ ι'' hιG)))
  · have hfw : glFw α ι := by by_contra h; exact hI ⟨hl, h⟩
    have hF : glF α ι := wx_fw_lim hl hfw
    refine ⟨ι, Or.inl ⟨ι, by unfold glPsi; rw [glLam_of hfw], (luP_succ.1 hF.1).symm⟩, hF.2.le,
      Or.inr ⟨hF.2, luP_mono hα1 le_self_add hF.1⟩, ?_, hιG⟩
    rw [hge]; exact max_le_max le_rfl (le_max_right _ _)

theorem xu_f_cases {α ι f β : Ordinal.{0}} (hpk : XuPkg α ι f) (hβ : β + 1 ≤ α) : f = Om1 ∨ glF β f := by
  rcases hpk.2.2.1 with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨luP_mono (le_add_self) hβ h2, h1⟩

end Googology.Trans.PoR.InaccPsi.R2.Xu
