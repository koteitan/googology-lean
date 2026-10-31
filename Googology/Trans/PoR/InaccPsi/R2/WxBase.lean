import Googology.Trans.PoR.InaccPsi.R2.WxVeb

/-!
# WxBase: EVERY `ε`-NUMBER CODE OF REGION (A2) HAS A SEQUENCE OF LEVELS — ONE PROOF FOR EVERY VEBLEN LEVEL

`e = glPsi α η = φ(α, Λ_α(η))`, `1 ≤ α < e`, `η < e` (`Gl.glPsi_surj`), `ε_{Ω₁+1} < e < G`.  One case split on the
argument `y = Λ_α(η)`, generic in `α`:

* **`y` a limit** (`η` a limit, `¬ glFw α η`, `wx_base_I`): `glPsi α η_k` / `glPsi α (s μ)` from the sequence of the
  SMALLER code `η` (continuity `Wx.wx_psi_cont`; gate-cofinality by the recursion `wx_rec` through the bracket
  `guE b = glPsi α_b η_b`: `α_b < α` recurses on `η_b`, `α_b = α` uses `η_b < η`, `α_b > α` gives `guE b < η`);
* **`y` a successor or `0`** (`wx_pkg`: the predecessor `f`, `e = φ(α, y'+1)` with `f = φ(α, y')`, or
  `e = φ(α, 0)` with `f = Ω₁`, `WxPre`), by the level:
  - `α = 1`: `e = ε_{f+1}`, the towers `f^{f^{⋯}}` (`Ws.ws_base_succ`; `wx_base_one`);
  - `α = α'+1`, `α' ≥ 1`: **the iterates of `φ(α', ·)`** over `f + 1` (`wx_base_succ`);
  - `α` a limit: `φ(α_k, f+1)` / `φ(s μ, f+1)` from the sequence of the SMALLER code `α` (`wx_base_lim`;
    gate-cofinality: `α_b < α` recurses on `η_b`, `α_b ≥ α` gives `guE b ≤ f`).

`wx_base_hi` (**THE VEBLEN NODES ABOVE `ε_{Ω₁+1}`**), `wx_baseI` (**`WsBaseI G`, UNCONDITIONAL**), `wx_base_all`
(**`WsBase G`**: every `ε`-number code in `[ε_{Ω₁+1}, G)` has a sequence of levels), `wx_refute` (the REFUTE-FIRST
instances `φ(1, ζ_{Ω₁+1}+1)` and `φ(2, Ω₁+2)`).

No new axiom.  New definitions: `WxPre`, `WxPkg`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wx

open Googology.Trans.PoR.InaccPsi.R2.Wm Googology.Trans.PoR.InaccPsi.R2.Wh Googology.Trans.PoR.InaccPsi.R2.Ho
open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gf
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt
open Googology.Trans.PoR.InaccPsi.R2.Wo Googology.Trans.PoR.InaccPsi.R2.Wn Googology.Trans.PoR.InaccPsi.R2.Wp
open Googology.Trans.PoR.InaccPsi.R2.Gk
open Googology.Trans.PoR.InaccPsi.R2.Ws Googology.Trans.PoR.InaccPsi.R2.Ws.WsC

/-! ## The recursion for gate-cofinality -/

/-- **GATE-COFINALITY BY RECURSION**: if every code `b ∈ [ε_{Ω₁+1}, e)` with `gh b < σ` has its bracket `guE b`
below some `T μ`, `μ < σ` (given the same for the smaller codes), then so has every code `b < e` itself. -/
theorem wx_rec {e σ : Ordinal.{0}} (hσ : InE σ) (T : Ordinal.{0} → Ordinal.{0})
    (hT : ∀ μ, μ < σ → InE (T μ) ∧ Om1 < T μ)
    (step : ∀ b, gfE ≤ b → b < e → gh b < σ →
      (∀ b', b' < b → gh b' < σ → ∃ μ, μ < σ ∧ b' < T μ) → ∃ μ, μ < σ ∧ guE b < T μ) :
    ∀ b, b < e → gh b < σ → ∃ μ, μ < σ ∧ b < T μ := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b ih =>
  intro hb hg
  rcases lt_or_ge b gfE with h | h
  · exact ⟨0, hσ.pos, h.trans_le (eN_le (hT 0 hσ.pos).2 (hT 0 hσ.pos).1)⟩
  · obtain ⟨μ, hμ, hlt⟩ := step b h hb hg (fun b' hb' hg' => ih b' hb' (hb'.trans hb) hg')
    exact ⟨μ, hμ, (gl_lt_eN h).trans_le (eN_le hlt (hT μ hμ).1)⟩

/-- **The data of the bracket** of a code `b ∈ [ε_{Ω₁+1}, G)` with `gh b < σ`: `guE b = glPsi α_b η_b`, the gates
of `α_b`, `η_b`, `guE b` below `σ`. -/
theorem wx_bdat {b σ : Ordinal.{0}} (hσ : InE σ) (h1 : gfE ≤ b) (h2 : b < gcG 0) (hg : gh b < σ) :
    1 ≤ glK (guE b) ∧ glK (guE b) < gcG 0 ∧ glI (guE b) < gcG 0 ∧ glPsi (glK (guE b)) (glI (guE b)) = guE b ∧
      gh (glK (guE b)) < σ ∧ gh (glI (guE b)) < σ ∧ gh (guE b) < σ ∧ guE b ≤ b ∧ glI (guE b) < b := by
  obtain ⟨d1, d2, d3, d4⟩ := gl_E_data h1 h2
  have hEb := gl_E_le h1
  have hdec := glG_dec h1 h2
  have hQE : glQE (guE b) ≤ glG b := by rw [hdec]; exact le_max_of_le_left (le_max_left _ _)
  have hEG : guE b < gcG 0 := hEb.trans_lt h2
  refine ⟨d1, d2.trans hEG, d3.trans hEG, d4, ws_gh_part hσ ((le_max_left _ _).trans hQE) hg,
    ws_gh_part hσ ((le_max_right _ _).trans hQE) hg, ws_gh_part hσ ?_ hg, hEb, d3.trans_le hEb⟩
  rw [wx_glQ_inf (omega0_lt_inE (guE_E b)).le, glG_base (guE_E b) (gl_Om1_lt_E h1) hEG]
  exact hQE

/-! ## Case (I): a limit argument -/

theorem wx_ML_psi {α : Ordinal.{0}} (hα1 : 1 ≤ α) (hαG : α < gcG 0) (η' : Ordinal.{0}) : ML (glPsi α η') :=
  ws_ML_E (glPsi_E hα1 η') (glPsi_gt hα1 hαG η').1

section CaseI

variable {α η : Ordinal.{0}} (hα1 : 1 ≤ α) (hαG : α < gcG 0) (hηG : η < gcG 0) (hl : IsSuccLimit η)
  (hnf : ¬ glFw α η)
include hα1 hαG hηG hl hnf

/-- **CASE (I)**: `η` a limit, `¬ glFw α η`: the sequence of `glPsi α η` from that of `η`. -/
theorem wx_base_I (hη : BCls (fun _ => True) η) : BCls ML (glPsi α η) := by
  have hge : gh (glPsi α η) = max 1 (max (glQ α) (glQ η)) := wx_gh_psi hα1 hαG hηG
  have hghη : gh η ≤ gh (glPsi α η) := by
    rw [ws_gh_lim hl, hge]; exact max_le_max le_rfl (le_max_right _ _)
  have hQα : glQ α ≤ gh (glPsi α η) := by rw [hge]; exact le_max_of_le_right (le_max_left _ _)
  rcases hη with ⟨cs, -, h2, h3, h4, h5⟩ | ⟨s, ⟨s1, s2, s3, s4⟩, -⟩
  · refine Or.inl ⟨fun k => glPsi α (cs k), fun k => wx_ML_psi hα1 hαG _,
      fun k => glPsi_strictMono α (h2 k), fun k => glPsi_strictMono α (h3 k), fun t ht => ?_, fun k => ?_⟩
    · obtain ⟨η', hη', ht'⟩ := wx_psi_cont hl hnf ht
      obtain ⟨k, hk⟩ := h4 η' hη'
      exact ⟨k, ht'.trans (glPsi_strictMono α hk)⟩
    · rw [wx_gh_psi hα1 hαG ((h3 k).trans hηG)]
      exact max_le (one_le_gh _) (max_le hQα ((ws_glQ_le_gh _).trans ((h5 k).trans hghη)))
  · have hsG : ∀ μ, μ < Om1 → s μ < gcG 0 := fun μ hμ => (s1 μ hμ).2.trans hηG
    refine Or.inr ⟨fun μ => glPsi α (s μ), ⟨fun μ hμ => ⟨(one_lt_inE (glPsi_E hα1 _)).le,
      glPsi_strictMono α (s1 μ hμ).2⟩, fun μ' μ h hμ => glPsi_strictMono α (s2 μ' μ h hμ),
      fun x hx hx1 hgx μ hμ => ?_, fun σ hσ hσ1 b hb hgb => ?_⟩, fun μ _ => wx_ML_psi hα1 hαG _⟩
    · change gh (glPsi α η) < x at hgx
      show gh (glPsi α (s μ)) < x
      rw [wx_gh_psi hα1 hαG (hsG μ (hμ.trans hx1))]
      exact max_lt (one_lt_inE hx) (max_lt (hQα.trans_lt hgx)
        ((ws_glQ_le_gh _).trans_lt (s3 x hx hx1 (hghη.trans_lt hgx) μ hμ)))
    · change gh b < σ at hgb
      refine wx_rec hσ (fun μ => glPsi α (s μ)) (fun μ _ => ⟨glPsi_E hα1 _, (glPsi_gt hα1 hαG _).1⟩)
        (fun b hEb hbe hgb' IH => ?_) b hb hgb
      have hbG : b < gcG 0 := hbe.trans (glPsi_lt_G hαG hηG)
      obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ := wx_bdat hσ hEb hbG hgb'
      have heb : guE b < glPsi α η := d8.trans_lt hbe
      rcases lt_trichotomy (glK (guE b)) α with hlt | heq | hgt
      · obtain ⟨μ, hμ, hlt'⟩ := IH _ d9 d6
        refine ⟨μ, hμ, ?_⟩
        rw [← d4]; exact (glPsi_lt_lev hlt hα1 hαG).2 hlt'
      · rw [← d4, heq] at heb
        have hηb : glI (guE b) < η := glPsi_lt_iff.1 heb
        obtain ⟨μ, hμ, hlt'⟩ := s4 σ hσ hσ1 _ hηb d6
        refine ⟨μ, hμ, ?_⟩
        rw [← d4, heq]; exact glPsi_lt_iff.2 hlt'
      · rw [← d4] at heb
        have hle : glPsi (glK (guE b)) (glI (guE b)) ≤ η := (glPsi_lt_lev' hgt d1 d2).1 heb
        rw [d4] at hle
        have hne : guE b ≠ η := by
          intro he
          refine hnf ⟨η, ⟨?_, ?_⟩, 0, by rw [Nat.cast_zero, add_zero]⟩
          · rw [← he, ← d4]
            exact luP_mono (le_add_self) (add_one_le_of_lt hgt) (glPsi_P _ _)
          · rw [← he]; exact gl_Om1_lt_E hEb
        obtain ⟨μ, hμ, hlt'⟩ := s4 σ hσ hσ1 _ (lt_of_le_of_ne hle hne) d7
        exact ⟨μ, hμ, hlt'.trans (lt_glPsi α _)⟩

end CaseI

/-! ## The predecessor `f` -/

/-- **The shape of a node with a successor or zero argument**: `e = φ(α, y+1)`, `f = φ(α, y)`, or `e = φ(α, 0)`,
`f = Ω₁ < α`. -/
def WxPre (α e f : Ordinal.{0}) : Prop :=
  (∃ y, e = veblen α (y + 1) ∧ f = veblen α y) ∨ (e = veblen α 0 ∧ f = Om1 ∧ Om1 < α)

/-- **The predecessor package** of `glPsi α η`: the shape, `Ω₁ ≤ f < G`, `f = Ω₁` or a value of `φ_α` above `Ω₁`,
and the gate of `f` below the gate of the node. -/
def WxPkg (α η f : Ordinal.{0}) : Prop :=
  WxPre α (glPsi α η) f ∧ Om1 ≤ f ∧ (f = Om1 ∨ (Om1 < f ∧ LuP α f)) ∧ max 1 (glQ f) ≤ gh (glPsi α η) ∧
    f < gcG 0

/-- **Every node whose argument is not a limit has a predecessor package.** -/
theorem wx_pkg {α η : Ordinal.{0}} (hα1 : 1 ≤ α) (hαG : α < gcG 0) (hηG : η < gcG 0)
    (hI : ¬ (IsSuccLimit η ∧ ¬ glFw α η)) : ∃ f, WxPkg α η f := by
  have hge : gh (glPsi α η) = max 1 (max (glQ α) (glQ η)) := wx_gh_psi hα1 hαG hηG
  have hOm : max 1 (glQ Om1) ≤ gh (glPsi α η) := by rw [wx_glQ_Om1, max_self]; exact one_le_gh _
  rcases zero_or_succ_or_isSuccLimit η with h0 | ⟨η'', hs⟩ | hl
  · subst h0
    refine ⟨Om1, ?_, le_rfl, Or.inl rfl, hOm, gl_Om1_lt_G0⟩
    unfold glPsi
    rw [glLam_of_not (glFw_zero α), add_zero]
    rcases lt_trichotomy α Om1 with h | h | h
    · exact Or.inl ⟨Om1, by rw [glY0_lt h], (gl_veb_Om1 h).symm⟩
    · subst h; exact Or.inl ⟨0, by rw [glY0_eq, zero_add], gl_veb_Om1_zero.symm⟩
    · exact Or.inr ⟨by rw [glY0_gt h], rfl, h⟩
  · rw [Order.succ_eq_add_one] at hs
    subst hs
    have hη''G : η'' < gcG 0 := (lt_add_one η'').trans hηG
    refine ⟨glPsi α η'', Or.inl ⟨glLam α η'', by unfold glPsi; rw [wx_lam_succ], rfl⟩,
      (glPsi_gt hα1 hαG η'').1.le, Or.inr ⟨(glPsi_gt hα1 hαG η'').1, glPsi_P α η''⟩, ?_,
      glPsi_lt_G hαG hη''G⟩
    rw [wx_glQ_inf (omega0_lt_inE (glPsi_E hα1 η'')).le, glG_psi hα1 hαG hη''G, hge]
    exact max_le_max le_rfl (max_le_max le_rfl (ws_glQ_succ η''))
  · have hfw : glFw α η := by by_contra h; exact hI ⟨hl, h⟩
    have hF : glF α η := wx_fw_lim hl hfw
    refine ⟨η, Or.inl ⟨η, by unfold glPsi; rw [glLam_of hfw], (luP_succ.1 hF.1).symm⟩, hF.2.le,
      Or.inr ⟨hF.2, luP_mono hα1 le_self_add hF.1⟩, ?_, hηG⟩
    rw [hge]; exact max_le_max le_rfl (le_max_right _ _)

section Pre

variable {α e f : Ordinal.{0}}

theorem wx_pre_range (h : WxPre α e f) : ∃ z, e = veblen α z := by
  rcases h with ⟨y, he, -⟩ | ⟨he, -, -⟩
  · exact ⟨_, he⟩
  · exact ⟨_, he⟩

/-- **Every value of `φ_α` below `e` is `≤ f`.** -/
theorem wx_pre_below (h : WxPre α e f) {u : Ordinal.{0}} (hu : LuP α u) (hue : u < e) : u ≤ f := by
  obtain ⟨z, rfl⟩ := hu
  rcases h with ⟨y, rfl, rfl⟩ | ⟨rfl, -, -⟩
  · exact (veblen_le_veblen_iff_right).2 (Order.lt_add_one_iff.1 ((veblen_lt_veblen_iff_right).1 hue))
  · exact absurd ((veblen_le_veblen_iff_right).2 zero_le) (not_le.2 hue)

theorem wx_pre_lt (h : WxPre α e f) : f < e := by
  rcases h with ⟨y, rfl, rfl⟩ | ⟨rfl, rfl, hα⟩
  · exact (veblen_lt_veblen_iff_right).2 (lt_add_one y)
  · exact hα.trans_le (left_le_veblen α 0)

theorem wx_pre_f1 (hα0 : α ≠ 0) (h : WxPre α e f) : f + 1 < e := by
  obtain ⟨z, hz⟩ := wx_pre_range h
  have hl : IsSuccLimit e := by rw [hz]; exact Ta.taVeb_lim hα0
  exact hl.add_one_lt (wx_pre_lt h)

/-- **The successor level `α'+1`**: every `x < e` lies below an iterate `φ(α', ·)^{k+1}(f+1)`. -/
theorem wx_pre_succ_cof {α' : Ordinal.{0}} (h : WxPre (α' + 1) e f) {x : Ordinal.{0}} (hx : x < e) :
    ∃ k : ℕ, x < (veblen α')^[k + 1] (f + 1) := by
  have hus : ∀ j : ℕ, (veblen α')^[j + 1] (f + 1) = veblen α' ((veblen α')^[j] (f + 1)) :=
    fun j => Function.iterate_succ_apply' _ _ _
  have key : ∀ b, b ≤ f + 1 → x < nfp (veblen α') b → ∃ k : ℕ, x < (veblen α')^[k + 1] (f + 1) := by
    intro b hb hxb
    obtain ⟨j, hj⟩ := Ta.taTw_cof (veblen_right_strictMono α').monotone (fun _ => le_rfl) hxb
      (fun j => (veblen α')^[j] (f + 1)) hb hus
    exact ⟨j, hj.trans_le (by rw [hus]; exact right_le_veblen _ _)⟩
  rcases h with ⟨y, rfl, rfl⟩ | ⟨rfl, rfl, -⟩
  · rw [Ta.taVeb_succ] at hx
    exact key _ le_rfl hx
  · rw [veblen_add_one, deriv_zero_right] at hx
    exact key 0 zero_le hx

/-- The iterates stay below `e` at a successor level. -/
theorem wx_pre_succ_lt {α' : Ordinal.{0}} (h : WxPre (α' + 1) e f) : ∀ k : ℕ, (veblen α')^[k] (f + 1) < e
  | 0 => wx_pre_f1 (add_pos_of_right zero_lt_one α').ne' h
  | k + 1 => by
    obtain ⟨z, hz⟩ := wx_pre_range h
    rw [Function.iterate_succ_apply']
    calc veblen α' ((veblen α')^[k] (f + 1)) < veblen α' e :=
          (veblen_lt_veblen_iff_right).2 (wx_pre_succ_lt h k)
      _ = e := by rw [hz]; exact veblen_veblen_of_lt (lt_add_one α') z

/-- **The limit level `α`**: every `x < e` lies below `φ(β, f+1)` for some `β < α`. -/
theorem wx_pre_lim_cof (hl : IsSuccLimit α) (h : WxPre α e f) {x : Ordinal.{0}} (hx : x < e) :
    ∃ β, β < α ∧ x < veblen β (f + 1) := by
  rcases h with ⟨y, rfl, rfl⟩ | ⟨rfl, rfl, -⟩
  · exact Ta.taVeb_lim_cof hl hx
  · obtain ⟨β, hβ, hxβ⟩ := wx_veb_lim_cof0 hl hx
    exact ⟨β, hβ, hxβ.trans_le ((veblen_le_veblen_iff_right).2 zero_le)⟩

theorem wx_pre_lim_lt (hα0 : α ≠ 0) (h : WxPre α e f) {β : Ordinal.{0}} (hβ : β < α) :
    veblen β (f + 1) < e := by
  have hf1 := wx_pre_f1 hα0 h
  obtain ⟨z, hz⟩ := wx_pre_range h
  calc veblen β (f + 1) < veblen β e := (veblen_lt_veblen_iff_right).2 hf1
    _ = e := by rw [hz]; exact veblen_veblen_of_lt hβ z

end Pre

/-! ## Case (II): the levels -/

theorem wx_f_cases {α η f β : Ordinal.{0}} (hpk : WxPkg α η f) (hβ : β + 1 ≤ α) : f = Om1 ∨ glF β f := by
  rcases hpk.2.2.1 with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨luP_mono (le_add_self) hβ h2, h1⟩

section CaseII

variable {α η f : Ordinal.{0}} (hα1 : 1 ≤ α) (hαG : α < gcG 0) (hηG : η < gcG 0) (hpk : WxPkg α η f)
include hα1 hαG hηG hpk

/-- **THE SUCCESSOR LEVEL `α'+1`, `α' ≥ 1`: THE ITERATES OF `φ(α', ·)` OVER `f + 1`.** -/
theorem wx_base_succ {α' : Ordinal.{0}} (hα : α = α' + 1) (hα'1 : 1 ≤ α') : BCls ML (glPsi α η) := by
  subst hα
  obtain ⟨hpre, hOf, hfc, hgf, hfG⟩ := hpk
  set e := glPsi (α' + 1) η with he_def
  have hα'G : α' < gcG 0 := (lt_add_one α').trans hαG
  have heG : e < gcG 0 := glPsi_lt_G hαG hηG
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
  have hQα : glQ α' ≤ gh e := by
    rw [he_def, wx_gh_psi hα1 hαG hηG]
    exact le_max_of_le_right (le_max_of_le_left (ws_glQ_succ α'))
  have hgate : ∀ k, gh (cs k) ≤ gh e := by
    intro k; induction k with
    | zero =>
      rw [hcs0]
      refine (wx_gh_veb hα'1 hα'G hfG (wx_f_cases ⟨hpre, hOf, hfc, hgf, hfG⟩ le_rfl)).trans ?_
      exact max_le (one_le_gh _) (max_le hQα ((le_max_right _ _).trans hgf))
    | succ k ih =>
      rw [hcs_s, wx_veb_psi (hE k) (hO k) (hnP k), wx_gh_psi hα'1 hα'G ((hlt k).trans heG)]
      exact max_le (one_le_gh _) (max_le hQα ((ws_glQ_le_gh _).trans ih))
  refine Or.inl ⟨cs, fun k => ws_ML_E (hE k) (hO k), hstr, hlt, fun t ht => ?_, hgate⟩
  exact wx_pre_succ_cof hpre ht

/-- **THE LEVEL `1`**: `e = ε_{f+1}`, the towers over `f` (`Ws.ws_base_succ`). -/
theorem wx_base_one (hα : α = 1) (hEe : gfE < glPsi α η) : BCls ML (glPsi α η) := by
  subst hα
  obtain ⟨hpre, hOf, hfc, hgf, hfG⟩ := hpk
  rcases hpre with ⟨y, he, rfl⟩ | ⟨-, -, h⟩
  · have hev : glPsi 1 η = eN (veblen 1 y) := by rw [he, go_eN_veb]
    rcases hfc with h | ⟨hOf', hP⟩
    · exfalso
      rw [hev, h] at hEe
      exact absurd hEe (lt_irrefl _)
    · have hfE : InE (veblen 1 y) := luP_E le_rfl hP
      rw [hev]
      refine ws_base_succ hfE hOf' (by rw [← hev]; exact glPsi_lt_G hαG hηG) ?_
      rw [← hev, ← glG_base hfE hOf' hfG, ← wx_glQ_inf (omega0_lt_inE hfE).le]
      exact hgf
  · exact absurd (h.trans_le hα1) (not_lt.2 (one_lt_omega0.trans omega_lt_Om1).le)

/-- **THE LIMIT LEVEL `α`**: `φ(α_k, f+1)` / `φ(s μ, f+1)` from the sequence of `α`. -/
theorem wx_base_lim (hl : IsSuccLimit α) (hαs : BCls (fun _ => True) α) : BCls ML (glPsi α η) := by
  obtain ⟨hpre, hOf, hfc, hgf, hfG⟩ := hpk
  set e := glPsi α η with he_def
  have hα0 : α ≠ 0 := hl.ne_bot
  have hge : gh e = max 1 (max (glQ α) (glQ η)) := wx_gh_psi hα1 hαG hηG
  have hghα : gh α ≤ gh e := by
    rw [ws_gh_lim hl, hge]; exact max_le_max le_rfl (le_max_left _ _)
  have hcase : ∀ β, β < α → f = Om1 ∨ glF β f := fun β hβ =>
    wx_f_cases ⟨hpre, hOf, hfc, hgf, hfG⟩ (Order.add_one_le_of_lt hβ)
  have hgβ : ∀ β, 1 ≤ β → β < α → gh β ≤ gh e → gh (veblen β (f + 1)) ≤ gh e := by
    intro β hβ1 hβα hgb
    refine (wx_gh_veb hβ1 (hβα.trans hαG) hfG (hcase β hβα)).trans ?_
    exact max_le (one_le_gh _) (max_le ((ws_glQ_le_gh _).trans hgb) ((le_max_right _ _).trans hgf))
  have hMLv : ∀ β, 1 ≤ β → ML (veblen β (f + 1)) := fun β hβ1 =>
    ws_ML_E (luP_E hβ1 (luP_veblen _ _)) ((Order.lt_add_one_iff.2 hOf).trans_le (right_le_veblen _ _))
  rcases hαs with ⟨as, -, h2, h3, h4, h5⟩ | ⟨s, ⟨s1, s2, s3, s4⟩, -⟩
  · have hpos : ∀ k, 1 ≤ as (k + 1) := fun k => Order.one_le_iff_pos.2 (zero_le.trans_lt (h2 k))
    refine Or.inl ⟨fun k => veblen (as (k + 1)) (f + 1), fun k => hMLv _ (hpos k),
      fun k => wx_veb_lt_left (h2 (k + 1)) f, fun k => wx_pre_lim_lt hα0 hpre (h3 (k + 1)),
      fun t ht => ?_, fun k => hgβ _ (hpos k) (h3 (k + 1)) ((h5 (k + 1)).trans hghα)⟩
    obtain ⟨β, hβ, htβ⟩ := wx_pre_lim_cof hl hpre ht
    obtain ⟨k, hk⟩ := h4 β hβ
    exact ⟨k, htβ.trans_le (veblen_left_monotone (f + 1) (hk.trans (h2 k)).le)⟩
  · have hmono : ∀ μ' μ, μ' ≤ μ → μ < Om1 → s μ' ≤ s μ := fun μ' μ h hμ => by
      rcases h.lt_or_eq with h | rfl
      · exact (s2 μ' μ h hμ).le
      · exact le_rfl
    refine Or.inr ⟨fun μ => veblen (s μ) (f + 1), ⟨fun μ hμ => ⟨Order.one_le_iff_pos.2 veblen_pos,
      wx_pre_lim_lt hα0 hpre (s1 μ hμ).2⟩, fun μ' μ h hμ => wx_veb_lt_left (s2 μ' μ h hμ) f,
      fun x hx hx1 hgx μ hμ => ?_, fun σ hσ hσ1 b hb hgb => ?_⟩, fun μ hμ => hMLv _ (s1 μ hμ).1⟩
    · change gh e < x at hgx
      show gh (veblen (s μ) (f + 1)) < x
      have hsμ := s1 μ (hμ.trans hx1)
      refine (wx_gh_veb hsμ.1 (hsμ.2.trans hαG) hfG (hcase _ hsμ.2)).trans_lt ?_
      exact max_lt (one_lt_inE hx) (max_lt ((ws_glQ_le_gh _).trans_lt (s3 x hx hx1 (hghα.trans_lt hgx) μ hμ))
        ((le_max_right _ _).trans_lt (hgf.trans_lt hgx)))
    · change gh b < σ at hgb
      refine wx_rec hσ (fun μ => veblen (s μ) (f + 1)) (fun μ hμ => ⟨luP_E (s1 μ (hμ.trans hσ1)).1 (luP_veblen _ _),
        (Order.lt_add_one_iff.2 hOf).trans_le (right_le_veblen _ _)⟩) (fun b hEb hbe hgb' IH => ?_) b hb hgb
      have hbG : b < gcG 0 := hbe.trans (glPsi_lt_G hαG hηG)
      obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ := wx_bdat hσ hEb hbG hgb'
      rcases lt_or_ge (glK (guE b)) α with hlt | hge'
      · obtain ⟨μ1, hμ1, hlt1⟩ := s4 σ hσ hσ1 _ hlt d5
        obtain ⟨μ2, hμ2, hlt2⟩ := IH _ d9 d6
        refine ⟨max μ1 μ2, max_lt hμ1 hμ2, ?_⟩
        have hm : max μ1 μ2 < Om1 := (max_lt hμ1 hμ2).trans hσ1
        have hk : glK (guE b) < s (max μ1 μ2) := hlt1.trans_le (hmono _ _ (le_max_left _ _) hm)
        have hT : glI (guE b) < veblen (s (max μ1 μ2)) (f + 1) :=
          hlt2.trans_le (veblen_left_monotone (f + 1) (hmono _ _ (le_max_right _ _) hm))
        rw [← d4]
        exact glPsi_lt_of (luP_mono le_add_self (Order.add_one_le_of_lt hk) (luP_veblen _ _))
          ((Order.lt_add_one_iff.2 hOf).trans_le (right_le_veblen _ _)) hT
      · have hP : LuP α (guE b) := by rw [← d4]; exact luP_mono hα1 hge' (glPsi_P _ _)
        have hle : guE b ≤ f := wx_pre_below hpre hP (d8.trans_lt hbe)
        exact ⟨0, hσ.pos, (Order.lt_add_one_iff.2 hle).trans_le (right_le_veblen _ _)⟩

end CaseII

/-! ## The bases -/

/-- **THE VEBLEN NODES ABOVE `ε_{Ω₁+1}`**: every `ε`-number code `e ∈ (ε_{Ω₁+1}, G)` has a sequence of levels, given
the sequences of the smaller limit codes.  ONE proof for every Veblen level. -/
theorem wx_base_hi {e : Ordinal.{0}} (he : InE e) (hEe : gfE < e) (heG : e < gcG 0)
    (IH : ∀ c, c < e → IsSuccLimit c → BCls (fun _ => True) c) : BCls ML e := by
  obtain ⟨α, hα1, hαe, η, hηe, rfl⟩ := glPsi_surj he (Om1_lt_eW.trans hEe) heG
  have hαG : α < gcG 0 := hαe.trans heG
  have hηG : η < gcG 0 := hηe.trans heG
  by_cases hI : IsSuccLimit η ∧ ¬ glFw α η
  · exact wx_base_I hα1 hαG hηG hI.1 hI.2 (IH η hηe hI.1)
  obtain ⟨f, hpk⟩ := wx_pkg hα1 hαG hηG hI
  rcases zero_or_succ_or_isSuccLimit α with h0 | ⟨α', hα'⟩ | hl
  · exact absurd (h0 ▸ hα1) (not_le.2 zero_lt_one)
  · rw [Order.succ_eq_add_one] at hα'
    rcases eq_or_ne α' 0 with h0 | h0
    · exact wx_base_one hα1 hαG hηG hpk (by rw [← hα', h0, zero_add]) hEe
    · exact wx_base_succ hα1 hαG hηG hpk hα'.symm (Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 h0))
  · exact wx_base_lim hα1 hαG hηG hpk hl (IH α hαe hl)

/-- **`WsBaseI G`, UNCONDITIONAL**: every `ε`-number code in `[ε_{Ω₁+1}, G)` has a sequence of levels given the
smaller codes. -/
theorem wx_baseI : WsBaseI (gcG 0) := by
  intro e he hEe heG IH
  rcases hEe.lt_or_eq with h | rfl
  · exact wx_base_hi he h heG IH
  · exact ws_base_E

/-- **`WsBase G`**: every `ε`-number code in `[ε_{Ω₁+1}, G)` has a sequence of levels (no induction hypothesis). -/
theorem wx_base_all : WsBase (gcG 0) := by
  intro e he hEe heG
  refine wx_baseI e he hEe heG (fun c hc hcl => (ws_br le_rfl wx_baseI c (hc.trans heG) hcl).1)

/-- **THE STATEMENT OF THE SKELETON LEAF `skBaseA2Hi`**: the `ε`-number codes in `(ζ_{Ω₁+1}, G)`. -/
theorem wx_baseA2Hi : ∀ e, InE e → wsZ < e → e < gcG 0 →
    (∀ c, c < e → IsSuccLimit c → BCls (fun _ => True) c) → BCls ML e := by
  intro e he hZ hG IH
  exact wx_base_hi he ((wsZs_zero ▸ wsZs_lt_Z 0).trans hZ) hG IH

/-- **REFUTE FIRST, the first codes past level 1**: `ε_{ζ_{Ω₁+1}+1} = φ(1, ζ_{Ω₁+1}+1)` and `φ(2, Ω₁+2)` (the
first code of level `2` past `ζ_{Ω₁+1}`) have sequences of levels. -/
theorem wx_refute : BCls ML (veblen 1 (wsZ + 1)) ∧ BCls ML (veblen 2 (Om1 + 1 + 1)) := by
  have hZ1 : wsZ + 1 < gcG 0 := gl_G0_lim.add_one_lt wsZ_lt_G
  have h2 : (2 : Ordinal.{0}) < gcG 0 := ws_two_lt_G
  refine ⟨wx_base_all _ (luP_E le_rfl (luP_veblen _ _)) ?_ ?_, wx_base_all _ (luP_E one_le_two (luP_veblen _ _)) ?_ ?_⟩
  · exact eN_le ((wsZ_Om1.trans (lt_add_one _)).trans_le (right_le_veblen _ _)) (luP_E le_rfl (luP_veblen _ _))
  · exact gl_veb_lt_G0 gl_one_lt_G0 hZ1
  · exact eN_le ((lt_add_one Om1).trans ((lt_add_one _).trans_le (right_le_veblen _ _)))
      (luP_E one_le_two (luP_veblen _ _))
  · exact gl_veb_lt_G0 h2 (gl_G0_lim.add_one_lt wx_Om1s_lt_G)

end Googology.Trans.PoR.InaccPsi.R2.Wx
