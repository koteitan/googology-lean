import Googology.Trans.PoR.InaccPsi.R2.GsWall

/-!
# THE LEAST NAMED `υ`-FIXED POINT `F₀ = P(Ω₁)`, AND WHY THE GATE STILL STOPS AT `K`

`P(η) = ψ_{Ω₁}(Ω_ω + θ·η)`, `K = P(0) = ψ_{Ω₁}(Ω_ω)`.  A named fixed point is a restart index `F = υ_F` with
`υ_F < P(ηx)` for some `ηx`.  Its name `η_F` is good, `ι(η_F) = F` and `P(η_F) = F`.  If `η_F < Ω₁`, then
`η_F < P(η_F)` (a good name lies in the hull without countable collapses, `Nn.nnGood_HCl`, `Bt.HCl_lt`), and
`ι(η_F) ≤ ι(0) + η_F = 1 + η_F` (`Fx.fx_iota_add_le`), so `F ≤ 1 + η_F ≤ max(ω, η_F) < F` (as `ω² < F`): impossible.
So `η_F ≥ Ω₁` and `F = P(η_F) ≥ P(Ω₁)`.  The index `ι(Ω₁)` is itself a named fixed point with value `P(Ω₁)`
(`Gg.ggFix`: `Ω₁` is a limit and `ζ + Ω₁ = Ω₁` for `ζ < Ω₁`).  So **`F₀ = P(Ω₁)` is the least named `υ`-fixed
point**, and `K < F₀`.

The gated frontier lemma (`Gs.gsB1_eq`) uses a lower bound of the named fixed points; `F₀` would serve.  The patched
layer (`Gq.gqLayP`), however, asks the gate below EVERY `υ`-point, and `K = υ₁` is one (`gv_K_ups`): a gate `g` lies
below every `υ`-point iff `g < K` (`gv_gU_iff`).  So the codes with gate in `[K, F₀)` are not located by the patched
layer; the bound `ε_{G+Ω₁}` read with `Ω₁ ↦ x` (gate `0`, `R2.GvU`) avoids the constant gates altogether.

* `gvF0` (`F₀ = P(Ω₁)`), `gv_eta_ge` (**`Ω₁ ≤ η_F`**), `gv_fix_ge` (**`F₀ ≤ F` for every named fixed point**),
  `gvF0_fix` (**`ι(Ω₁)` is a named fixed point with value `F₀`**), `gvK_eq`, `gvK_lt_F0`, `gvF0_lt_Om1`;
* `gv_K_ups` (**`K = υ₁` is a `υ`-point**), `gv_gU_iff` (**`g` below every `υ`-point `⇔ g < K`**).

No new axiom.  New definition: `gvF0`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Gg

variable {S : InaccSeq.{0}}

/-- **The least named `υ`-fixed point**: `F₀ = P(Ω₁) = ψ_{Ω₁}(Ω_ω + θ·Ω₁)`. -/
noncomputable def gvF0 (S : InaccSeq.{0}) : Ordinal.{0} := Pv S (Om 1)

theorem gvF0_lt_Om1 : gvF0 S < Om 1 := Pv_lt_Om1 S _

/-- `K = P(0)`. -/
theorem gvK_eq (S : InaccSeq.{0}) : Td.tdK S = Pv S 0 := by
  show S.psi (Om ω) (Om 1) = S.psi (ConjT.Aη S 0) (Om 1)
  rw [A_zero]

/-- **The name of a named fixed point is at least `Ω₁`.** -/
theorem gv_eta_ge {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) : Om 1 ≤ cdEta S F := by
  obtain ⟨hg, hι, -, hP⟩ := cdEta_pv_spec (S := S) hF.1 hX
  by_contra hlt
  push Not at hlt
  have hη : cdEta S F < Pv S (cdEta S F) :=
    HCl_lt (Pv_SC S _) (Nn.nnGood_HCl hg) hlt
  rw [hP, hfix] at hη
  have hle : F ≤ 1 + cdEta S F := by
    have h := Fx.fx_iota_add_le (S := S) 0 (cdEta S F)
    rw [zero_add, iota_zero, hι] at h
    exact h
  have hww := gg_ww_lt hF hfix
  rcases lt_or_ge (cdEta S F) ω with hω | hω
  · have h1 : 1 + cdEta S F < ω := isPrincipal_add_omega0 one_lt_omega0 hω
    have h2 : ω ≤ ω * ω := le_mul_left _ omega0_pos
    exact absurd ((hle.trans_lt h1).trans_le h2) (not_lt.2 hww.le)
  · rw [one_add_of_omega0_le hω] at hle
    exact absurd hη (not_lt.2 hle)

/-- **`F₀ ≤ F` for every named `υ`-fixed point `F`.** -/
theorem gv_fix_ge {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) : gvF0 S ≤ F := by
  have h := Pv_mono (S := S) (gv_eta_ge hF hfix hX)
  rw [cdEta_pv hF.1 hX, hfix] at h
  exact h

theorem gv_Om1_gap : ∀ ζ < Om (1 : Ordinal.{0}), ζ + Om 1 ≤ Om 1 := fun ζ hζ =>
  (Fx.fx_Om1_prin.add_eq_right hζ).le

/-- **`ι(Ω₁)` is a named `υ`-fixed point with value `F₀`**, so `F₀` is the least named fixed point. -/
theorem gvF0_fix (S : InaccSeq.{0}) :
    IsRestartIdx (iota S (Om 1)) ∧ upsilon (iota S (Om 1)) = iota S (Om 1) ∧ iota S (Om 1) = gvF0 S ∧
      upsilon (iota S (Om 1)) < Pv S (Om 1 + 1) := by
  have hfix : upsilon (iota S (Om 1)) = iota S (Om 1) := ggFix Fx.fx_Om1_lim gv_Om1_gap
  have hF0 : iota S (Om 1) ≠ 0 := (lt_of_lt_of_le zero_lt_one (one_le_iota _)).ne'
  have he : iota S (Om 1) = gvF0 S := by
    rw [← hfix]; exact ups_iota S _
  refine ⟨Fx.fx_ri_of_fix hF0 hfix, hfix, he, ?_⟩
  rw [hfix, he]
  have hg : Bt.Good S (Om 1) := CSet.Om_mem (CSet.one_mem _ _)
  exact Pv_lt_succ hg

/-- **`K < F₀`.** -/
theorem gvK_lt_F0 (S : InaccSeq.{0}) : Td.tdK S < gvF0 S := by
  rw [gvK_eq]
  calc Pv S 0 < Pv S 1 := by
        have h := Pv_lt_succ (S := S) (show Bt.Good S 0 from CSet.zero_mem _ _)
        rwa [zero_add] at h
    _ ≤ gvF0 S := Pv_mono (Order.one_le_iff_pos.2 (Om_pos one_ne_zero))

/-- **`K = υ₁` is a `υ`-point.** -/
theorem gv_K_ups (S : InaccSeq.{0}) : UpsPt (Td.tdK S) := by
  rw [gvK_eq, Pv_zero]; exact upsPt_upsilon zero_lt_one

/-- **A gate lies below every `υ`-point iff it lies below `K`** (the patched layer `Gq.gqLayP` asks the left side). -/
theorem gv_gU_iff (S : InaccSeq.{0}) (g : Ordinal.{0}) : (∀ u, UpsPt u → g < u) ↔ g < Td.tdK S :=
  ⟨fun h => h _ (gv_K_ups S), fun h u hu => h.trans_le (Gr.gr_tdK_le_ups S hu)⟩

end Googology.Trans.PoR.InaccPsi.R2.Gv
