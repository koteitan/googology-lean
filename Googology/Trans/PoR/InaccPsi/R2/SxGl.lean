import Googology.Trans.PoR.InaccPsi.R2.SxAt

/-!
# The offsets below `Γ_{a+1}`: the codes of `R2.Gl` as an offset code system

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

The codes `c < Γ_{Ω₁+1}` of `R2.Gl` (generic in the Veblen level) read `Gl.glR c x` at the base `x`.  `R2.GlR1`–
`GlR7` give `R(b+1) = R(b) + 1`, monotonicity, readings below `Γ_{x+1} = lgG x`, Lemma EXACT (`Gl.gl_pi`, no
`υ`-point hypothesis), the last term with Lemma EXACT for its logend (`Gl.gl_ld`), and hull membership (`Gl.gl_mem`);
`Sx.sxGl_ex` gives surjectivity onto `[0, Γ_{x+1})`.  So:

* `sxGl_ld`, `sxGl : SuCS` (**the offset code system with `V = Γ_{·+1}`**; the reading is `Gl.glRr`, equal to
  `glR` below `Ω₁`), `sxGl_V`;
* `sxGlReal_M`, `sxGlReal_L` (**`LrReal S a υ_{a+Γ_{a+1}}` at `m*` and every `L(n+1)`**), `sxGlShort_L`,
  `sxGlShort_M` (**`a ≤₁ υ_{a+Γ_{a+1}}`**), `sxGlRoad` (**the road with the gaps asked only above
  `υ_{a+Γ_{a+1}}`**), `sxGlCL_iff_noUncov`, `sxGlM_iff_noUncov` (**(CL) at `n` / `m* ≤₁ L(1)` iff no uncovered
  reach in `[υ_{a+Γ_{a+1}}, L(n+2))` / `[υ_{m*+Γ_{m*+1}}, L(1))`**);
* `sxZ_lt_G` (`ζ_{a+1} < Γ_{a+1}`), `sxGl_gt_Z` (`υ_{a+ζ_{a+1}} < υ_{a+Γ_{a+1}}`), `sxGap_of_gapZ` (the gaps above
  `υ_{a+ζ_{a+1}}` give those above `υ_{a+Γ_{a+1}}`), `sxGl_V_le_SC` (`Γ_{a+1}` is at most every strongly critical
  ordinal above `a`).

No new axiom.  New definition: `sxGl` (an instance of the structure `SuCS`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Sx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Su Googology.Trans.PoR.InaccPsi.R2.Gf

variable {S : InaccSeq.{0}}

/-- The last exponent of a limit code moves with `π_{σ,ρ}`. -/
theorem sxGl_ld {σ ρ c : Ordinal.{0}} (hB : Bases σ ρ) (hl : IsSuccLimit c) (hc : c < gcG 0)
    (hg : glG c < σ) : cdExp (glR c ρ) ∈ TB ρ σ ∧ pi σ ρ (cdExp (glR c ρ)) = cdExp (glR c σ) := by
  have hld := gl_ld c hl hc
  unfold GlLD at hld
  obtain ⟨_cp, _lp, T, -, -, hdec, hpi⟩ := hld
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hT : ∀ y, InE y → y < Om1 → glG c < y → cdExp (glR c y) = T y := by
    intro y hy hy1 hgy
    obtain ⟨e1, e2, -, -⟩ := hdec y hy hy1 hgy
    rw [e1]
    exact Ge.lg_add_opow e2
  rw [hT ρ hB.2.1 hρ1 (hg.trans hB.2.2.1), hT σ hB.1 hσ1 hg]
  exact hpi σ ρ hB hg

/-- **The offset code system of `R2.Gl`**: codes below `Γ_{Ω₁+1}`, readings below `V x = Γ_{x+1}`. -/
noncomputable def sxGl : SuCS where
  R := glRr
  G := glG
  B := gcG 0
  V := lgG
  B_lim := gl_G0_lim
  B_le := fun S k => gl_G0_le (Ls.lsTh_SC (k + 1)) (by rw [Br.Om1_eq]; exact Rp.rpOm1_lt_th (S := S) k)
  zero_R := fun x => by
    rcases lt_or_ge x Om1 with hx1 | hx1
    · rw [glRr_eq hx1, glR_zero]
    · rw [glRr_hi hx1, if_pos eW_E.pos]
  zero_G := glG_zero
  succ_R := fun b x _ => glRr_succ b x
  succ_G := fun b _ hb hZ hg => glG_succ hZ b (gl_G0_lim.add_one_lt hb) hg
  R_mono := fun _ _ _ hx hc hbc hgb hgc => glRr_mono hx hc hbc hgb hgc
  R_lt := fun _ _ hx hx1 hc hg => by rw [glRr_eq hx1]; exact glR_lt_G hx hx1 hc hg
  R_ex := fun _ ν hx hx1 hν => by
    obtain ⟨c, h1, h2, h3⟩ := sxGl_ex hx hx1 ν hν
    exact ⟨c, h1, h2, by rw [glRr_eq hx1]; exact h3⟩
  R_pi := fun _ _ c hB hc hg => by
    rw [glRr_eq hB.2.2.2, glRr_eq (hB.2.2.1.trans hB.2.2.2)]; exact gl_pi hB c hc hg
  R_ld := fun _ _ _ hB hl hc hg => by
    rw [glRr_eq hB.2.2.2, glRr_eq (hB.2.2.1.trans hB.2.2.2)]; exact sxGl_ld hB hl hc hg
  R_mem := fun _ _ _ c hc hg e he => (gl_mem c hc hg).2 e he
  V_E := fun x hx hx1 => lgG_inE x hx hx1
  V_gt := fun _ hx hx1 => (lgG_facts hx hx1).2.1
  V_le := fun _ _ hx hx1 hxu hu => lgG_le fun n => (LvGT.lvg_top_lt_next hx hx1 n hxu hu.2).le

theorem sxGl_V : sxGl.V = lgG := rfl

/-! ## `ζ_{a+1} < Γ_{a+1}` -/

/-- `ζ_{x+1} < Γ_{x+1}`. -/
theorem sxZ_lt_G {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : evZ x < lgG x := by
  have h2 : ((2 : ℕ) : Ordinal.{0}) < lgG x :=
    (natCast_lt_omega0 2).trans ((omega0_lt_inE hx).trans (lgG_facts hx hx1).2.1)
  have h := glA_lt_G hx hx1 h2 (lgG_pos hx hx1)
  unfold glA at h
  rwa [gl_vt_two hx hx1] at h

/-- `Γ_{a+1}` is at most every strongly critical ordinal above `a`. -/
theorem sxGl_V_le_SC {x b : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hb : SC b) (hxb : x < b) :
    sxGl.V x ≤ b := sxG_le_SC hx hx1 hb hxb

/-- **The new bound is strictly larger**: `υ_{a+ζ_{a+1}} < υ_{a+Γ_{a+1}}`. -/
theorem sxGl_gt_Z {a : Ordinal.{0}} (haE : InE a) (ha1 : a < Om1) :
    upsilon (a + evZ a) < upsilon (a + lgG a) :=
  upsilon_normal.strictMono ((add_lt_add_iff_left a).2 (sxZ_lt_G haE ha1))

/-- **The gaps above `υ_{a+ζ_{a+1}}` give the gaps above `υ_{a+Γ_{a+1}}`.** -/
theorem sxGap_of_gapZ {a b : Ordinal.{0}} (haE : InE a) (ha1 : a < Om1)
    (h : LrGap S a b (upsilon (a + evZ a))) : LrGap S a b (upsilon (a + lgG a)) :=
  Ls.lsGap_mono (upsilon_normal.strictMono.monotone (add_le_add le_rfl (sxZ_lt_G haE ha1).le)) h

/-! ## The realizers and the road up to `υ_{a+Γ_{a+1}}` -/

/-- **The realizers at `m*` up to `υ_{m*+Γ_{m*+1}} < L(1)`**, given `L(ω) ≤ ν_C`. -/
theorem sxGlReal_M (hlow : Nc.ncL S ω ≤ nuC)
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (hstd : Cx.CxStdPairTop S) :
    LrReal S (Nc.ncL S 0) (upsilon (Nc.ncL S 0 + lgG (Nc.ncL S 0))) ∧
      upsilon (Nc.ncL S 0 + lgG (Nc.ncL S 0)) < Nc.ncL S 1 :=
  suReal_M sxGl hlow hU hL hstd

/-- **The realizers at `L(n+1)` up to `υ_{a+Γ_{a+1}} < L(n+2)`**, given `L(ω) ≤ ν_C`. -/
theorem sxGlReal_L (hlow : Nc.ncL S ω ≤ nuC)
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (hstd : Cx.CxStdPairTop S) (n : ℕ) :
    LrReal S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + lgG (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))) ∧
      upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + lgG (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))) <
        Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) :=
  suReal_L sxGl hlow hU hL hstd n

/-- **`L(n+1) ≤₁ υ_{a+Γ_{a+1}}`** from UPPER, CapV, LOWER. -/
theorem sxGlShort_L (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (n : ℕ) :
    le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + lgG (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))) :=
  suShort_L sxGl hU hV hVt hL n

/-- **`m* ≤₁ υ_{m*+Γ_{m*+1}}`** from UPPER, CapV, LOWER. -/
theorem sxGlShort_M (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) :
    le1 (Nc.ncL S 0) (upsilon (Nc.ncL S 0 + lgG (Nc.ncL S 0))) :=
  suShort_M sxGl hU hV hVt hL

/-- **The road with the gaps asked only above `υ_{a+Γ_{a+1}}`** (at `m*` and every `L(n+1)`). -/
theorem sxGlRoad (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S) (hmove : Cx.CxStdMoveTop S)
    (h0 : LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + lgG (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + lgG (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  suRoad sxGl hU hO hL hV hVt hEQ htop hmove h0 hn

/-- **(CL) at `n` iff no uncovered reach of `L(n+1)` in `[υ_{a+Γ_{a+1}}, L(n+2))`** (UPPER, CapV, LOWER). -/
theorem sxGlCL_iff_noUncov (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (n : ℕ) :
    le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})) ↔
      ¬ ∃ r, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) r ∧
        upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + lgG (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))) ≤ r ∧
        r < Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) ∧
        ∀ l, CdRange S l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ≤ upsilon l → upsilon l ≤ r →
          cdR S l ≤ r :=
  suCL_iff_noUncov sxGl hU hV hVt hL n

/-- **`m* ≤₁ L(1)` iff no uncovered reach of `m*` in `[υ_{m*+Γ_{m*+1}}, L(1))`** (UPPER, CapV, LOWER). -/
theorem sxGlM_iff_noUncov (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) :
    le1 (Nc.ncL S 0) (Nc.ncL S 1) ↔
      ¬ ∃ r, IsReach R2C (Nc.ncL S 0) r ∧ upsilon (Nc.ncL S 0 + lgG (Nc.ncL S 0)) ≤ r ∧
        r < Nc.ncL S 1 ∧
        ∀ l, CdRange S l → Nc.ncL S 0 ≤ upsilon l → upsilon l ≤ r → cdR S l ≤ r :=
  suM_iff_noUncov sxGl hU hV hVt hL

end Googology.Trans.PoR.InaccPsi.R2.Sx
