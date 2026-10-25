import Googology.Trans.PoR.InaccPsi.R2.UrRoad
import Googology.Trans.PoR.InaccPsi.R2.UrExist
import Googology.Trans.PoR.InaccPsi.R2.UnGdRoad

/-!
# The road with inner reaches given by ordinal decompositions with gap levels

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Un.unGdTyRoad` with `Ur.urExist` in place of `Un.unExist`: the form `Ur.UrForm` of the reach `r(λ+g) ∈
seg(υ_{λ+h})` follows from ORDINAL data (`UrGdForm`, a decomposition `Ur.UrGd`): parameters below `υ_λ` or inner
`υ`-points `υ_{λ+h'}`, `h' ≤ h`, constant levels over `υ_λ`, levels `Ω₁·M < ε_{Ω₁+1}` with `Γ^* ≥ υ_{λ+h}` and
decomposed leaves, and **gap levels**: `Ω₁·M` whose leaves are parameters below `υ_{λ+h}` (e.g. `Ω₁·υ_{λ+h'}`,
`h' < h`).  No term is asked of the user of the road.

* `UrGdForm`, `urForm_of_gd` (**`UrGdForm ⇒ Ur.UrForm`**), `urGdForm_of_un` (**`Un.UnGdForm ⇒ UrGdForm`**);
* `UrGdTyGen`, `urTyGen_of_gd` (**`UrGdTyGen ⇒ Ur.UrTyGen`**), `urGdTyGen_of_un`, `UrGdTyVis`, `urTyVis_of_gd`,
  `urGdTyVis_of_un` (**`Un.UnGdTyVis ⇒ UrGdTyVis`**: the new road hypothesis is weaker);
* `urGdTyRoad` (**the road of `Ur.urTyRoad` from `UrGdTyVis` at `m*` and every `L(n+1)`**).

No new axiom.  New definitions: `UrGdForm`, `UrGdTyGen`, `UrGdTyVis` (statements).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ur

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Tk Googology.Trans.PoR.InaccPsi.R2.Tv
  Googology.Trans.PoR.InaccPsi.R2.Ty Googology.Trans.PoR.InaccPsi.R2.Ub Googology.Trans.PoR.InaccPsi.R2.Un

variable {S : InaccSeq.{0}}

/-- **The reach of the inner restart `λ+g` has an ordinal decomposition over `υ_{λ+h}`**: `r(λ+g) ∈
seg(υ_{λ+h})`, `υ_{λ+h} < Ω₁`, and `Ur.UrGd υ_λ υ_{λ+h} P r(λ+g)` (gap levels allowed) with parameters
`p < υ_λ` or `p = υ_{λ+h'}`,
`h' ≤ h`. -/
def UrGdForm (S : InaccSeq.{0}) (l β g : Ordinal.{0}) : Prop :=
  ∃ h, 0 < h ∧ h < β ∧ upsilon (l + h) < Om1 ∧ upsilon (l + h) ≤ cdR S (l + g) ∧
    cdR S (l + g) < upsilon (succ (l + h)) ∧
    UrGd (upsilon l) (upsilon (l + h)) (fun p => p < upsilon l ∨ ∃ h', h' ≤ h ∧ p = upsilon (l + h'))
      (cdR S (l + g))

/-- **`UrGdForm ⇒ UrForm`** (`Ur.urExist`). -/
theorem urForm_of_gd {l β g : Ordinal.{0}} (hl : IsRestartIdx l) (h : UrGdForm S l β g) : UrForm S l β g := by
  obtain ⟨h, h0, h1, hO, hlo, hhi, hgd⟩ := h
  have hm := upsilon_normal.strictMono
  have hB : Bases (upsilon l) (upsilon (l + h)) :=
    ⟨upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 hl.1)),
      upsPt_inE (upsPt_upsilon (lt_of_lt_of_le (pos_iff_ne_zero.2 hl.1) le_self_add)),
      hm (lt_add_of_pos_right l h0), hO⟩
  obtain ⟨t, e, w, q, lP, -, -⟩ := urExist hB hgd
  exact ⟨h, t, h0, h1, q, w, lP, hlo, hhi, e⟩

/-- **`Ur.UrTyGen` with decompositions in place of terms.** -/
def UrGdTyGen (S : InaccSeq.{0}) (l β w : Ordinal.{0}) : Prop :=
  (∀ g, 0 < g → g < β → ω ^ 2 ∣ g → UbF3 S l β g ∨ UbForm S l β g ∨ UrGdForm S l β g) ∧
  (∀ γ, w ≤ γ → γ < upsilon l → ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < β) →
      ∃ μ f B, IsRestartIdx μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧ μ + B ≤ l ∧ ω ^ 2 ∣ B ∧
        upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧ TyCarry S l β μ f B Os ∧ UbCarry S l β μ f Os ∧
          Ue.UeCarry S l β μ f Os ∧ Uh.UhCarry S l β μ f Os ∧ Uk.UkCarry S l β μ f Os ∧
          UnCarry S l β μ f Os ∧ UrCarry S l β μ f Os)

/-- **`UrGdTyGen ⇒ UrTyGen`** at a restart index. -/
theorem urTyGen_of_gd {l β w : Ordinal.{0}} (hl : IsRestartIdx l) (h : UrGdTyGen S l β w) :
    UrTyGen S l β w :=
  ⟨fun g h0 h1 h2 => (h.1 g h0 h1 h2).imp_right (Or.imp_right (urForm_of_gd hl)), h.2⟩

/-- **`Ur.UrTyVis` with decompositions in place of terms.** -/
def UrGdTyVis (S : InaccSeq.{0}) (l b c w : Ordinal.{0}) : Prop :=
  ∀ ν, CdRange S ν → c ≤ upsilon ν → upsilon ν < b → upsilon l < upsilon ν → ¬ TkCov S (upsilon l) ν →
    TkIso S (upsilon l) ν → ∃ β, upsilon ν < upsilon (l + β) ∧ upsilon (l + β) ≤ b ∧ UrGdTyGen S l β w

theorem urTyVis_of_gd {l b c w : Ordinal.{0}} (hl : IsRestartIdx l) (h : UrGdTyVis S l b c w) :
    UrTyVis S l b c w := by
  intro ν h1 h2 h3 h4 h5 h6
  obtain ⟨β, hνβ, hβb, hG⟩ := h ν h1 h2 h3 h4 h5 h6
  exact ⟨β, hνβ, hβb, urTyGen_of_gd hl hG⟩

/-- **`Un.UnGdForm ⇒ UrGdForm`.** -/
theorem urGdForm_of_un {l β g : Ordinal.{0}} (h : UnGdForm S l β g) : UrGdForm S l β g := by
  obtain ⟨h, h0, h1, hO, hlo, hhi, hgd⟩ := h
  exact ⟨h, h0, h1, hO, hlo, hhi, urGd_of_un hgd⟩

/-- **`Un.UnGdTyGen ⇒ UrGdTyGen`** (`UrCarry` vacuous at the forms of `Un`). -/
theorem urGdTyGen_of_un {l β w : Ordinal.{0}} (hl : IsRestartIdx l) (h : UnGdTyGen S l β w) :
    UrGdTyGen S l β w := by
  refine ⟨fun g h0 h1 h2 => (h.1 g h0 h1 h2).imp_right (Or.imp_right urGdForm_of_un), fun γ hγ hγl Os hOs => ?_⟩
  obtain ⟨μ, f, B, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := h.2 γ hγ hγl Os hOs
  exact ⟨μ, f, B, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
    fun g _ h0 hgβ hgd hn3 hn4 _ hn6 =>
      absurd (unForm_of_gd hl (((h.1 g h0 hgβ hgd).resolve_left hn3).resolve_left hn4)) hn6⟩

/-- **`Un.UnGdTyVis ⇒ UrGdTyVis`**: the road hypothesis of `urGdTyRoad` is implied by that of `Un.unGdTyRoad`. -/
theorem urGdTyVis_of_un {l b c w : Ordinal.{0}} (hl : IsRestartIdx l) (h : UnGdTyVis S l b c w) :
    UrGdTyVis S l b c w := by
  intro ν h1 h2 h3 h4 h5 h6
  obtain ⟨β, hνβ, hβb, hG⟩ := h ν h1 h2 h3 h4 h5 h6
  exact ⟨β, hνβ, hβb, urGdTyGen_of_un hl hG⟩

section Road

variable (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
  (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
  (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
  (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
  (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
  (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S) (hmove : Cx.CxStdMoveTop S)
include hU hO hL hV hVt hEQ htop hmove

/-- **The road from `UrGdTyVis` at `m*` (window `υ(Λ_B⁺)`) and at every `L(n+1)` (window `L(n)`)**: the conclusion
of `Un.unTyRoad`; the reaches of the inner restarts are asked as ordinal decompositions with gap levels
(`UrGdForm`). -/
theorem urGdTyRoad
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      UrGdTyVis S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))) (upsilon Rz.rzLam))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      UrGdTyVis S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
        (Nc.ncL S (n : Ordinal.{0}))) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  urTyRoad hU hO hL hV hVt hEQ htop hmove (fun l hl e => urTyVis_of_gd hl (h0 l hl e))
    (fun n l hl e => urTyVis_of_gd hl (hn n l hl e))

end Road

end Googology.Trans.PoR.InaccPsi.R2.Ur
