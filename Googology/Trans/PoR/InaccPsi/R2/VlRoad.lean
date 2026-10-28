import Googology.Trans.PoR.InaccPsi.R2.UyRoad
import Googology.Trans.PoR.InaccPsi.R2.VlReal

/-!
# The road with inner reaches given by terms with the node `thz G r` (levels with moving leaves)

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Uy.uyRoadGen` and `Uy.uyTyRoad` with `Vl.vlReal_gen` (fifth form `Uy.UyForm ∨ VlForm`, carry `VlCarry`).

* `VlGen`, `vlReal_of_gen`, `vlGen_of_uy` (**`Uy.UyGen ⇒ VlGen`**), `VlVisGen`, `vlVisI_of_gen`;
* `VlTyGen`, `vlTyGen_of_uy`, `vlTyGen_ur`, `VlTyVis`, `vlTyVis_of_uy` (**`Uy.UyTyVis ⇒ VlTyVis`: the new road
  hypothesis is weaker**), `vlTyVis_gen`;
* `vlRoadGen`, `vlTyRoad` (**the road from `VlVisGen` / `VlTyVis` at `m*` and every `L(n+1)`**).

New definitions: `VlGen`, `VlVisGen`, `VlTyGen`, `VlTyVis` (statements).  No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vl

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Tk Googology.Trans.PoR.InaccPsi.R2.Tv
  Googology.Trans.PoR.InaccPsi.R2.Ty Googology.Trans.PoR.InaccPsi.R2.Ub Googology.Trans.PoR.InaccPsi.R2.Un
open Googology.Trans.PoR.InaccPsi.R2.Ur Googology.Trans.PoR.InaccPsi.R2.Uy

variable {S : InaccSeq.{0}}

/-- **The hypotheses of `vlReal_gen` at `(λ, β)`**: UPPER at the inner restarts, the forms of their reaches, the
supply with `Tv.TvCarry`, `Ub.UbCarry`, `Ue.UeCarry`, `Uh.UhCarry`, `Uk.UkCarry`, `Un.UnCarry`, `Uy.UyCarry`,
`VlCarry`. -/
def VlGen (S : InaccSeq.{0}) (l β : Ordinal.{0}) : Prop :=
  (∀ g, 0 < g → g < β → ω ^ 2 ∣ g → CdUpper S (l + g)) ∧
  (∀ g, 0 < g → g < β → ω ^ 2 ∣ g → UbF3 S l β g ∨ UbForm S l β g ∨ UyForm S l β g ∨ VlForm S l β g) ∧
  (∀ γ < upsilon l, ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < β) →
      ∃ μ f B, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧ μ + B ≤ l ∧ ω ^ 2 ∣ B ∧
        upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧ TvCarry S l β μ f B Os ∧ UbCarry S l β μ f Os ∧
          Ue.UeCarry S l β μ f Os ∧ Uh.UhCarry S l β μ f Os ∧ Uk.UkCarry S l β μ f Os ∧
          UnCarry S l β μ f Os ∧ Ur.UrCarry S l β μ f Os ∧ UyCarry S l β μ f Os ∧
          VlCarry S l β μ f Os)

/-- **`VlGen` gives the realizer.** -/
theorem vlReal_of_gen {l β : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : upsilon l < Om1)
    (hν : upsilon l < nuC) (hνβ : upsilon (l + β) ≤ nuC) (hstd : Cx.CxStdPairTop S)
    (hlL : upsilon l ≤ Nc.ncL S (ω + 1)) (h : VlGen S l β) : Lr.LrReal S (upsilon l) (upsilon (l + β)) :=
  vlReal_gen hl hl1 hν hνβ h.1 h.2.1 h.2.2 hstd hlL

/-- **At every isolated uncovered Range restart `ν` of `[c, b)` some `β` with `ρ_ν < υ_{λ+β} ≤ b` and
`VlGen S λ β`.** -/
def VlVisGen (S : InaccSeq.{0}) (l b c : Ordinal.{0}) : Prop :=
  ∀ ν, CdRange S ν → c ≤ upsilon ν → upsilon ν < b → upsilon l < upsilon ν → ¬ TkCov S (upsilon l) ν →
    TkIso S (upsilon l) ν → ∃ β, upsilon ν < upsilon (l + β) ∧ upsilon (l + β) ≤ b ∧ VlGen S l β

/-- **`VlVisGen` gives the visible statements `Tk.TkVisI`.** -/
theorem vlVisI_of_gen (hL : CdLOWER S) {l b c : Ordinal.{0}} (hl : IsRestartIdx l) (hb : b ≤ nuC)
    (hbL : b ≤ Nc.ncL S (ω + 1)) (hstd : Cx.CxStdPairTop S) (h : VlVisGen S l b c) :
    TkVisI S (upsilon l) b c := by
  refine tkVisI_of_real hL hl rfl hb fun ν h1 h2 h3 h4 h5 h6 => ?_
  obtain ⟨β, hνβ, hβb, hG⟩ := h ν h1 h2 h3 h4 h5 h6
  have hν : upsilon l < nuC := (h4.trans h3).trans_le hb
  exact ⟨_, hνβ, hβb, vlReal_of_gen hl (hν.trans_le nuC_le_Om1) hν (hβb.trans hb) hstd
    ((h4.trans h3).le.trans hbL) hG⟩

/-- **`Ty.TyGen` with the fourth form and the fifth form `Uy.UyForm ∨ VlForm`**: the forms of the inner reaches and, for
every `γ ∈ [w, υ_λ)` and finite offset set, a restart `μ` above `γ` with supply `υ_{μ+B} ≤ r(μ)`, an offset map,
`Ty.TyCarry`, `Ub.UbCarry`, `Ue.UeCarry`, `Uh.UhCarry`, `Uk.UkCarry`, `Un.UnCarry`, `Uy.UyCarry` and `VlCarry`. -/
def VlTyGen (S : InaccSeq.{0}) (l β w : Ordinal.{0}) : Prop :=
  (∀ g, 0 < g → g < β → ω ^ 2 ∣ g → UbF3 S l β g ∨ UbForm S l β g ∨ UyForm S l β g ∨ VlForm S l β g) ∧
  (∀ γ, w ≤ γ → γ < upsilon l → ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < β) →
      ∃ μ f B, IsRestartIdx μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧ μ + B ≤ l ∧ ω ^ 2 ∣ B ∧
        upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧ TyCarry S l β μ f B Os ∧ UbCarry S l β μ f Os ∧
          Ue.UeCarry S l β μ f Os ∧ Uh.UhCarry S l β μ f Os ∧ Uk.UkCarry S l β μ f Os ∧
          UnCarry S l β μ f Os ∧ Ur.UrCarry S l β μ f Os ∧ UyCarry S l β μ f Os ∧
          VlCarry S l β μ f Os)

/-- **`VlTyGen` gives `VlGen` at `L(k)`** under UPPER and LOWER at the Range restarts with `RzRest` (as
`Ty.tyGen_tv`). -/
theorem vlTyGen_ur (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) {k : ℕ} {w l β : Ordinal.{0}} (hw : TyWin S k w)
    (hla : upsilon l = Nc.ncL S (k : Ordinal.{0}))
    (hβ : upsilon (l + β) ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (h : VlTyGen S l β w) : VlGen S l β := by
  have hm := upsilon_normal.strictMono
  have hlk : l = Nc.ncL S (k : Ordinal.{0}) := hm.injective (hla.trans (Te.teUps_L (S := S) k).symm)
  have hl : IsRestartIdx l := hlk ▸ Te.teRst_L (S := S) k
  have hwin : ∀ ν, IsRestartIdx ν → w < upsilon ν → upsilon ν < upsilon l → CdRange S ν ∧ Rz.RzRest ν :=
    fun ν hν h1 h2 => tyWin_rng hw hν h1 (hla ▸ h2)
  refine ⟨fun g hg0 hgβ hgd => ?_, h.1, fun γ hγ Os hOs => ?_⟩
  · have hν : IsRestartIdx (l + g) :=
      ⟨(lt_of_lt_of_le (pos_iff_ne_zero.2 hl.1) le_self_add).ne', dvd_add hl.2 hgd⟩
    have h1 : Nc.ncL S (k : Ordinal.{0}) < upsilon (l + g) := hla ▸ hm (lt_add_of_pos_right l hg0)
    have h2 : upsilon (l + g) < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) :=
      (hm (add_lt_add_right hgβ l)).trans_le hβ
    obtain ⟨hr, hz⟩ := tyInner_rng hν h1 h2
    exact hU _ hr hz
  · have hwl : w < upsilon l := hla ▸ hw.2.1
    obtain ⟨μ, f, B, hμ, hγμ, hμl, hμB, hBd, hsupB, hoff, ⟨hc1, hc2⟩, hub, hue, huh, huk, hun, hur, huy, hvl⟩ :=
      h.2 (max γ w) (le_max_right _ _) (max_lt hγ hwl) Os hOs
    have hwμ : w < upsilon μ := (le_max_right γ w).trans_lt hγμ
    refine ⟨μ, f, B, (hwin μ hμ hwμ hμl).1, (le_max_left γ w).trans_lt hγμ, hμl, hμB, hBd, hsupB, hoff,
      ⟨fun g hg hg0 hgd => ⟨?_, (hc1 g hg hg0 hgd).1, (hc1 g hg hg0 hgd).2⟩, hc2⟩, hub, hue, huh, huk, hun, hur, huy,
      hvl⟩
    obtain ⟨q, hq⟩ := hgd
    have hν : IsRestartIdx (μ + f g) :=
      ⟨(lt_of_lt_of_le (pos_iff_ne_zero.2 hμ.1) le_self_add).ne', dvd_add hμ.2 (hq ▸ hoff.dvd q)⟩
    have h1 : w < upsilon (μ + f g) := hwμ.trans_le (hm.monotone le_self_add)
    have h2 : upsilon (μ + f g) < upsilon l :=
      hm ((add_lt_add_right (hoff.bd g hg) μ).trans_le hμB)
    obtain ⟨hr, hz⟩ := hwin _ hν h1 h2
    exact hL _ hr hz

/-- **At every isolated uncovered Range restart `ν` of `[c, b)` some `β` with `ρ_ν < υ_{λ+β} ≤ b` and
`VlTyGen S λ β w`.** -/
def VlTyVis (S : InaccSeq.{0}) (l b c w : Ordinal.{0}) : Prop :=
  ∀ ν, CdRange S ν → c ≤ upsilon ν → upsilon ν < b → upsilon l < upsilon ν → ¬ TkCov S (upsilon l) ν →
    TkIso S (upsilon l) ν → ∃ β, upsilon ν < upsilon (l + β) ∧ upsilon (l + β) ≤ b ∧ VlTyGen S l β w

/-- **`UrTyVis ⇒ VlVisGen` at `L(k)`** (`b ≤ L(k+1)`, `w` a window) under UPPER and LOWER at the Range restarts
with `RzRest`. -/
theorem vlTyVis_gen (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) {k : ℕ} {w l b c : Ordinal.{0}} (hw : TyWin S k w)
    (hla : upsilon l = Nc.ncL S (k : Ordinal.{0})) (hb : b ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
    (h : VlTyVis S l b c w) : VlVisGen S l b c := by
  intro ν h1 h2 h3 h4 h5 h6
  obtain ⟨β, hνβ, hβb, hG⟩ := h ν h1 h2 h3 h4 h5 h6
  exact ⟨β, hνβ, hβb, vlTyGen_ur hU hL hw hla (hβb.trans hb) hG⟩

/-- **`Uy.UyGen ⇒ VlGen`** (`VlCarry` is vacuous: every form is `Ub.UbF3 ∨ Ub.UbForm ∨ Uy.UyForm`). -/
theorem vlGen_of_uy {l β : Ordinal.{0}} (h : Uy.UyGen S l β) : VlGen S l β := by
  refine ⟨h.1, fun g h0 h1 h2 => (h.2.1 g h0 h1 h2).imp_right (Or.imp_right Or.inl), fun γ hγ Os hOs => ?_⟩
  obtain ⟨μ, f, B, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := h.2.2 γ hγ Os hOs
  exact ⟨μ, f, B, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15,
    fun g _ h0 hgβ hgd hn3 hn4 hn5 => absurd (((h.2.1 g h0 hgβ hgd).resolve_left hn3).resolve_left hn4) hn5⟩

/-- **`Uy.UyTyGen ⇒ VlTyGen`** (`VlCarry` vacuous). -/
theorem vlTyGen_of_uy {l β w : Ordinal.{0}} (h : Uy.UyTyGen S l β w) : VlTyGen S l β w := by
  refine ⟨fun g h0 h1 h2 => (h.1 g h0 h1 h2).imp_right (Or.imp_right Or.inl), fun γ hγ hγl Os hOs => ?_⟩
  obtain ⟨μ, f, B, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := h.2 γ hγ hγl Os hOs
  exact ⟨μ, f, B, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15,
    fun g _ h0 hgβ hgd hn3 hn4 hn5 => absurd (((h.1 g h0 hgβ hgd).resolve_left hn3).resolve_left hn4) hn5⟩

/-- **`Uy.UyTyVis ⇒ VlTyVis`**: the new road hypothesis is implied by the one of `Uy.uyTyRoad` (hence by those of
`Ur.urTyRoad`, `Un.unTyRoad`, …). -/
theorem vlTyVis_of_uy {l b c w : Ordinal.{0}} (h : Uy.UyTyVis S l b c w) : VlTyVis S l b c w := by
  intro ν h1 h2 h3 h4 h5 h6
  obtain ⟨β, hνβ, hβb, hG⟩ := h ν h1 h2 h3 h4 h5 h6
  exact ⟨β, hνβ, hβb, vlTyGen_of_uy hG⟩

/-- **`Uy.UyVisGen ⇒ VlVisGen`.** -/
theorem vlVisGen_of_uy {l b c : Ordinal.{0}} (h : Uy.UyVisGen S l b c) : VlVisGen S l b c := by
  intro ν h1 h2 h3 h4 h5 h6
  obtain ⟨β, hνβ, hβb, hG⟩ := h ν h1 h2 h3 h4 h5 h6
  exact ⟨β, hνβ, hβb, vlGen_of_uy hG⟩

section Road

variable (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
  (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
  (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
  (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
  (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
  (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S) (hmove : Cx.CxStdMoveTop S)
include hU hO hL hV hVt hEQ htop hmove

/-- **The road from `VlVisGen` at `m*` and every `L(n+1)`** (the realizers of `Tk.tkRoadReal` built by
`vlReal_gen`; no `LrGap`, no `CxStdPairTop`). -/
theorem vlRoadGen
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      VlVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      VlVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hν := Sh.shNu hU hV hVt hL
  have hstd : Cx.CxStdPairTop S := Tp.tpStdPairTop hν
  have hLW : CdLOWER S := Rz.rzLOWER_of_rest hL
  have hlt : ∀ k : ℕ, Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ Nc.ncL S (ω + 1) := fun k =>
    ((Pp.ppL_lt_omega k).trans (Qq.qqL_lt_succ S)).le
  refine tkRoadVis hU hO hL hV hVt hEQ htop hmove ?_ ?_
  · obtain ⟨l, hl, e⟩ := Cv.cvM_restart (S := S)
    have h1 : Nc.ncL S 1 ≤ Nc.ncL S (ω + 1) := by simpa using hlt 0
    have := vlVisI_of_gen hLW hl (h1.trans hν) h1 hstd (h0 l hl e)
    rwa [← e] at this
  · intro n
    obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
    have := vlVisI_of_gen hLW hl ((hlt (n + 1)).trans hν) (hlt (n + 1)) hstd (hn n l hl e)
    rwa [← e] at this

/-- **The road from `VlTyVis` at `m*` (window `υ(Λ_B⁺)`) and at every `L(n+1)` (window `L(n)`)**: the conclusion
of `Ty.tyRoad`, with the forms `Ub.UbForm` and `UyForm` of inner reaches allowed per block. -/
theorem vlTyRoad
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      VlTyVis S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))) (upsilon Rz.rzLam))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      VlTyVis S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
        (Nc.ncL S (n : Ordinal.{0}))) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  refine vlRoadGen hU hO hL hV hVt hEQ htop hmove (fun l hl e => ?_) (fun n l hl e => ?_)
  · have hla : upsilon l = Nc.ncL S ((0 : ℕ) : Ordinal.{0}) := by rw [Nat.cast_zero]; exact e.symm
    have hb : Nc.ncL S 1 ≤ Nc.ncL S ((0 + 1 : ℕ) : Ordinal.{0}) := by simp
    exact vlTyVis_gen hU hL tyWin_M hla hb (h0 l hl e)
  · have hb : Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) ≤ Nc.ncL S ((n + 1 + 1 : ℕ) : Ordinal.{0}) := le_rfl
    exact vlTyVis_gen hU hL (tyWin_L n) e.symm hb (hn n l hl e)

end Road

end Googology.Trans.PoR.InaccPsi.R2.Vl
