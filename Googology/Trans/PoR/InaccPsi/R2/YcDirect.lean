import Googology.Trans.PoR.InaccPsi.R2.YcBase

/-!
# YcDirect: A THIRD ROUTE — ONE DIRECT READING SYSTEM OVER THE BASE ATOMS LOCATES THE WHOLE LAYER

The frontier lemma over `Γ(c)` (`Xx.xxLoc`, `Xx.xxEnum`, `Xx.xxCapV`) needs only a READING SYSTEM `Xx.XxRS c`
(codes, gates, readings below `Γ_{x+2+c}`, Lemma EXACT, limit data with Lemma IMG), not the systems `Yc.YcVD c`
with their next-base fields (`b`, `ba`, `dig`, `Z`), which serve only to BUILD readings level by level.  If the
codes of the layer `c` are read DIRECTLY (as `Xu.xuR` reads every code below `Γ(1)`), the layer is located with
no system recursion, and the old levels (`skLayLo`) and the new levels (`skLayHi`) at once:

* `YcDirect S c B₀` (**codes cofinal below `B₀` in reading systems over `Γ(c)`**, with gates below `K`);
* `ycUV_of_direct` (**UPPER ∧ LOWER ∧ CapV at every range restart below `ι(Γ(B)·ω)`, `B < B₀`**);
* `ycLay_of_direct` (**`YcDirect S c Γ(c+1)` ⇒ the conclusions of `skLayLo` AND `skLayHi` at `c`**:
  `φ(ℓ, Γ(c)+1) < Γ(c+1)` for every `ℓ < Γ(c+1)`), `yc_veb_lt_next`;
* `ycDirect_A2` (**non-vacuity: `YcDirect S 0 φ(G, 1)` is a theorem**, from the closed region (A2),
  `Wx.wxSysA2`, through `Xx.xxVRS`): at `c = 0` the route gives region (A2) again.

No new axiom.  New definition: `YcDirect`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gf
  Googology.Trans.PoR.InaccPsi.R2.Xx Googology.Trans.PoR.InaccPsi.R2.Xk

/-- **DIRECT READINGS OF THE LAYER `c` BELOW `B₀`**: every `B < B₀` lies below a code `B' ≥ max(B, ε_{Ω₁+1})` of a
reading system over `Γ(c)` with gate below `K`. -/
def YcDirect (S : InaccSeq.{0}) (c B₀ : Ordinal.{0}) : Prop :=
  ∀ B, B < B₀ → ∃ RS : XxRS c, ∃ B', B ≤ B' ∧ gfE ≤ B' ∧ B' < RS.K.B ∧ RS.K.gt B' < Td.tdK S

/-- **UPPER ∧ LOWER ∧ CapV below `ι(Γ(B)·ω)` for every `B < B₀`** from direct readings below `B₀`. -/
theorem ycUV_of_direct {S : InaccSeq.{0}} {c B₀ : Ordinal.{0}} (h : YcDirect S c B₀) :
    ∀ l, Cd.CdRange S l → ∀ B, B < B₀ → l < Bt.iota S (gcG B * ω) →
      Cd.CdUpper S l ∧ Cd.CdLower S l ∧ Cd.CdCapV S l := by
  intro l hr B hB hl
  obtain ⟨RS, B', hBB, hE, hB', hg⟩ := h B hB
  have hl' : l < Bt.iota S (gcG B' * ω) :=
    hl.trans_le (Bt.iota_mono (S := S) _ _ (mul_le_mul_left (gcG_le hBB) ω))
  exact ⟨(xxEnum RS B' hE hB' S hg hr hl').1, (xxEnum RS B' hE hB' S hg hr hl').2, xxCapV RS B' hE hB' S hg hr hl'⟩

/-- **`φ(ℓ, Γ(c)+1) < Γ(c+1)`** for every `ℓ < Γ(c+1)`. -/
theorem yc_veb_lt_next {c ℓ : Ordinal.{0}} (hℓ : ℓ < gcG (c + 1)) : veblen ℓ (gcG c + 1) < gcG (c + 1) := by
  have hSC := gcG_SC (c + 1)
  have hE : InE (gcG (c + 1)) := Low.opow_eq_self_of_SC hSC
  have hfix : veblen ℓ (gcG (c + 1)) = gcG (c + 1) := Gn.gn_veb_fix hSC hℓ
  have h1 : gcG c + 1 < gcG (c + 1) := (ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt (lt_add_one c))
  have h2 := (isNormal_veblen ℓ).strictMono h1
  rwa [hfix] at h2

/-- **THE WHOLE LAYER `c` FROM DIRECT READINGS BELOW `Γ(c+1)`**: the conclusions of `skLayLo` (levels `ℓ < Γ(c)`) and
of `skLayHi` (levels `Γ(c) ≤ ℓ < Γ(c+1)`) at `c`. -/
theorem ycLay_of_direct {S : InaccSeq.{0}} {c : Ordinal.{0}} (h : YcDirect S c (gcG (c + 1))) :
    ∀ l, Cd.CdRange S l → (∃ ℓ, ℓ < gcG (c + 1) ∧ l < Bt.iota S (gcG (veblen ℓ (gcG c + 1)) * ω)) →
      Cd.CdUpper S l ∧ Cd.CdLower S l ∧ Cd.CdCapV S l := by
  rintro l hr ⟨ℓ, hℓ, hl⟩
  exact ycUV_of_direct h l hr _ (yc_veb_lt_next hℓ) hl

/-- **NON-VACUITY: `YcDirect S 0 φ(G, 1)` IS A THEOREM** (region (A2), `Wx.wxSysA2`, through `Xx.xxVRS`). -/
theorem ycDirect_A2 (S : InaccSeq.{0}) : YcDirect S 0 (veblen (gcG 0) 1) := by
  intro B hB
  obtain ⟨V, hVB, hγ⟩ := Wx.wxSysA2 S B hB
  have hk : (0 : Ordinal.{0}) + 1 < ε₀ := yc_zero_one_eps
  refine ⟨xxVRS (XkVD.ofHg V) hk, V.B, hVB, (xx_E_lt_B (XkVD.ofHg V)).le, xx_B_lt_Bw (XkVD.ofHg V), ?_⟩
  exact (xxVRS_gt_B (XkVD.ofHg V) hk).le.trans_lt hγ

end Googology.Trans.PoR.InaccPsi.R2.Yc
