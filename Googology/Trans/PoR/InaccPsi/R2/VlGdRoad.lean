import Googology.Trans.PoR.InaccPsi.R2.UyGdRoad
import Googology.Trans.PoR.InaccPsi.R2.VlRoad
import Googology.Trans.PoR.InaccPsi.R2.VlExist

/-!
# The road with inner reaches given by ordinal decompositions with levels with moving leaves

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Uy.uyGdTyRoad` with `Vl.vlTyRoad` and `Vl.vlExist`: the reach of an inner restart is asked as a decomposition
`VlGd` (constant levels, gap levels, and the new levels with moving leaves `thz`).

* `VlGdForm`, `vlForm_of_gd` (**a decomposition gives the term form `VlForm`**, the bound `δ` an `υ`-point between the
  level data and `υ_λ`), `vlGdForm_of_uy` (**`Uy.UyGdForm ⇒ VlGdForm`**);
* `VlGdTyGen`, `vlTyGen_of_gd`, `vlGdTyGen_of_uy`, `VlGdTyVis`, `vlTyVis_of_gd`, `vlGdTyVis_of_uy`
  (**`Uy.UyGdTyVis ⇒ VlGdTyVis`: the new road hypothesis is weaker**);
* `vlGdTyRoad` (**the road from `VlGdTyVis` at `m*` and every `L(n+1)`**).

New definitions: `VlGdForm`, `VlGdTyGen`, `VlGdTyVis` (statements).  No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vl

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Tk Googology.Trans.PoR.InaccPsi.R2.Tv
  Googology.Trans.PoR.InaccPsi.R2.Ty Googology.Trans.PoR.InaccPsi.R2.Ub Googology.Trans.PoR.InaccPsi.R2.Un
open Googology.Trans.PoR.InaccPsi.R2.Ur Googology.Trans.PoR.InaccPsi.R2.Uy

variable {S : InaccSeq.{0}}

/-- **The reach of the inner restart `λ+g` has a decomposition `VlGd` over `υ_{λ+h}`**: `r(λ+g) ∈ seg(υ_{λ+h})`,
`υ_{λ+h} < Ω₁`, `VlGd υ_λ υ_{λ+h} P r(λ+g)` with parameters and moving level leaves `p < υ_λ` or `p = υ_{λ+h'}`,
`h' ≤ h`. -/
def VlGdForm (S : InaccSeq.{0}) (l β g : Ordinal.{0}) : Prop :=
  ∃ h, 0 < h ∧ h < β ∧ upsilon (l + h) < Om1 ∧ upsilon (l + h) ≤ cdR S (l + g) ∧
    cdR S (l + g) < upsilon (succ (l + h)) ∧
    VlGd (upsilon l) (upsilon (l + h)) (fun p => p < upsilon l ∨ ∃ h', h' ≤ h ∧ p = upsilon (l + h'))
      (cdR S (l + g))

/-- **`VlGdForm ⇒ VlForm`** (`vlExist`; the bound `δ = υ_{ι+1}` with the level data below it, `υ_λ` a limit of
`υ`-points). -/
theorem vlForm_of_gd {l β g : Ordinal.{0}} (hl : IsRestartIdx l) (h : VlGdForm S l β g) : VlForm S l β g := by
  obtain ⟨h, h0, h1, hO, hlo, hhi, hgd⟩ := h
  have hm := upsilon_normal.strictMono
  have ha : UpsPt (upsilon l) := upsPt_upsilon (pos_iff_ne_zero.2 hl.1)
  have hB : Bases (upsilon l) (upsilon (l + h)) :=
    ⟨upsPt_inE ha, upsPt_inE (upsPt_upsilon (lt_of_lt_of_le (pos_iff_ne_zero.2 hl.1) le_self_add)),
      hm (lt_add_of_pos_right l h0), hO⟩
  obtain ⟨t, Lf, Dq, e, w, z, lP, -, hLf, hDq, hZ, -⟩ := vlExist hB hgd
  have hMa : Dq.sup id < upsilon l := (Finset.sup_lt_iff ha.1).2 fun d hd => hDq d hd
  obtain ⟨_, ⟨ι, hιl, rfl⟩, hMι, -⟩ := (upsilon_limit (ri_lim hl)).exists_between hMa
  have hκU : UpsPt (upsilon (succ ι)) := upsPt_upsilon (lt_of_le_of_lt zero_le (lt_succ ι))
  have hMκ : Dq.sup id < upsilon (succ ι) := hMι.trans (hm (lt_succ ι))
  have hκa : upsilon (succ ι) < upsilon l := hm ((ri_lim hl).succ_lt hιl)
  exact ⟨h, t, Lf, upsilon (succ ι), h0, h1, hκa, z, w, lP,
    hZ _ (upsPt_inE hκU) (fun d hd => (Finset.le_sup (f := id) hd).trans_lt hMκ),
    fun p hp => (hLf p hp).2, hlo, hhi, e⟩

/-- **`Uy.UyGdForm ⇒ VlGdForm`** (`vlGd_of_uy`). -/
theorem vlGdForm_of_uy {l β g : Ordinal.{0}} (h : UyGdForm S l β g) : VlGdForm S l β g := by
  obtain ⟨h, h0, h1, hO, hlo, hhi, hgd⟩ := h
  exact ⟨h, h0, h1, hO, hlo, hhi, vlGd_of_uy hgd⟩

/-- **`Vl.VlTyGen` with decompositions in place of terms.** -/
def VlGdTyGen (S : InaccSeq.{0}) (l β w : Ordinal.{0}) : Prop :=
  (∀ g, 0 < g → g < β → ω ^ 2 ∣ g → UbF3 S l β g ∨ UbForm S l β g ∨ VlGdForm S l β g) ∧
  (∀ γ, w ≤ γ → γ < upsilon l → ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < β) →
      ∃ μ f B, IsRestartIdx μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧ μ + B ≤ l ∧ ω ^ 2 ∣ B ∧
        upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧ TyCarry S l β μ f B Os ∧ UbCarry S l β μ f Os ∧
          Ue.UeCarry S l β μ f Os ∧ Uh.UhCarry S l β μ f Os ∧ Uk.UkCarry S l β μ f Os ∧
          UnCarry S l β μ f Os ∧ Ur.UrCarry S l β μ f Os ∧ UyCarry S l β μ f Os ∧ VlCarry S l β μ f Os)

/-- **`VlGdTyGen ⇒ VlTyGen`** at a restart index. -/
theorem vlTyGen_of_gd {l β w : Ordinal.{0}} (hl : IsRestartIdx l) (h : VlGdTyGen S l β w) :
    VlTyGen S l β w :=
  ⟨fun g h0 h1 h2 => (h.1 g h0 h1 h2).imp_right (Or.imp_right fun hf => Or.inr (vlForm_of_gd hl hf)), h.2⟩

/-- **`Uy.UyGdTyGen ⇒ VlGdTyGen`** (`VlCarry` vacuous: a `Uy.UyGdForm` gives `Uy.UyForm`). -/
theorem vlGdTyGen_of_uy {l β w : Ordinal.{0}} (hl : IsRestartIdx l) (h : UyGdTyGen S l β w) :
    VlGdTyGen S l β w := by
  refine ⟨fun g h0 h1 h2 => (h.1 g h0 h1 h2).imp_right (Or.imp_right vlGdForm_of_uy), fun γ hγ hγl Os hOs => ?_⟩
  obtain ⟨μ, f, B, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := h.2 γ hγ hγl Os hOs
  exact ⟨μ, f, B, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15,
    fun g _ h0 hgβ hgd hn3 hn4 hn5 =>
      absurd (uyForm_of_gd hl (((h.1 g h0 hgβ hgd).resolve_left hn3).resolve_left hn4)) hn5⟩

/-- **`Vl.VlTyVis` with decompositions in place of terms.** -/
def VlGdTyVis (S : InaccSeq.{0}) (l b c w : Ordinal.{0}) : Prop :=
  ∀ ν, CdRange S ν → c ≤ upsilon ν → upsilon ν < b → upsilon l < upsilon ν → ¬ TkCov S (upsilon l) ν →
    TkIso S (upsilon l) ν → ∃ β, upsilon ν < upsilon (l + β) ∧ upsilon (l + β) ≤ b ∧ VlGdTyGen S l β w

theorem vlTyVis_of_gd {l b c w : Ordinal.{0}} (hl : IsRestartIdx l) (h : VlGdTyVis S l b c w) :
    VlTyVis S l b c w := by
  intro ν h1 h2 h3 h4 h5 h6
  obtain ⟨β, hνβ, hβb, hG⟩ := h ν h1 h2 h3 h4 h5 h6
  exact ⟨β, hνβ, hβb, vlTyGen_of_gd hl hG⟩

/-- **`Uy.UyGdTyVis ⇒ VlGdTyVis`**: the road hypothesis of `vlGdTyRoad` is implied by that of `Uy.uyGdTyRoad`. -/
theorem vlGdTyVis_of_uy {l b c w : Ordinal.{0}} (hl : IsRestartIdx l) (h : UyGdTyVis S l b c w) :
    VlGdTyVis S l b c w := by
  intro ν h1 h2 h3 h4 h5 h6
  obtain ⟨β, hνβ, hβb, hG⟩ := h ν h1 h2 h3 h4 h5 h6
  exact ⟨β, hνβ, hβb, vlGdTyGen_of_uy hl hG⟩

section Road

variable (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
  (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
  (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
  (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
  (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
  (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S) (hmove : Cx.CxStdMoveTop S)
include hU hO hL hV hVt hEQ htop hmove

/-- **The road from `VlGdTyVis` at `m*` (window `υ(Λ_B⁺)`) and at every `L(n+1)` (window `L(n)`)**: the conclusion
of `Uy.uyGdTyRoad`; the reaches of the inner restarts are asked as decompositions `VlGd` (levels with moving leaves
allowed). -/
theorem vlGdTyRoad
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      VlGdTyVis S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))) (upsilon Rz.rzLam))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      VlGdTyVis S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
        (Nc.ncL S (n : Ordinal.{0}))) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  vlTyRoad hU hO hL hV hVt hEQ htop hmove (fun l hl e => vlTyVis_of_gd hl (h0 l hl e))
    (fun n l hl e => vlTyVis_of_gd hl (hn n l hl e))

end Road

end Googology.Trans.PoR.InaccPsi.R2.Vl
