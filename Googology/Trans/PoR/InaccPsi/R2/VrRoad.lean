import Googology.Trans.PoR.InaccPsi.R2.VrReal
import Googology.Trans.PoR.InaccPsi.R2.VrWit

/-!
# The road with the repaired forms, and why it is not refuted by the no-go witness

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.

* `VrGen` (UPPER at the inner restarts, the forms `υ_{λ+β} ≤ r(λ+g) ∨ VrForm`, the supply with `VrCarry`),
  `vrReal_of_gen`, `VrVisGen`, `vrVisI_of_gen` (**`VrVisGen ⇒ Tk.TkVisI`**);
* `vrRoad` (**the conclusion of `Tk.tkRoadVis` from `VrVisGen` at `m*` and every `L(n+1)`**), `vrLong`
  (**(CL), `m* ≤₁ L(1)`, `L(k) ≤₁ ν_C` and `Tk.TkSucc` at every `L(k)`**, via `Vo.voLong_of_vis`);
* `vrSup`, `vrGen_wit_iff` (**non-vacuity at the no-go witness**: at `a = L(k)`, `β₀ = g + ω²·2`, under UPPER at the
  Range restarts, `VrGen S a β₀` is equivalent to its supply clause alone: the form clause is a theorem there);
  `vrVis_wit` (**the witness `ν = a + g + ω²` of `Vo.voNoGo` is answered by `β₀` as soon as the supply holds**).

New definitions: `VrGen`, `VrVisGen`, `VrSup` (statements).  No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vr

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Tk

variable {S : InaccSeq.{0}}

/-- **The supply clause with the repaired carry** at `(λ, β)`. -/
def VrSup (S : InaccSeq.{0}) (l β : Ordinal.{0}) : Prop :=
  ∀ γ < upsilon l, ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < β) →
    ∃ μ f B, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧ μ + B ≤ l ∧ ω ^ 2 ∣ B ∧
      upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧ VrCarry S l β μ f B Os

/-- **The hypotheses of `vrReal_gen` at `(λ, β)`.** -/
def VrGen (S : InaccSeq.{0}) (l β : Ordinal.{0}) : Prop :=
  (∀ g, 0 < g → g < β → ω ^ 2 ∣ g → CdUpper S (l + g)) ∧
  (∀ g, 0 < g → g < β → ω ^ 2 ∣ g → upsilon (l + β) ≤ cdR S (l + g) ∨ VrForm S l β g) ∧ VrSup S l β

/-- **`VrGen` gives the realizer.** -/
theorem vrReal_of_gen {l β : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : upsilon l < Om1)
    (hν : upsilon l < nuC) (hνβ : upsilon (l + β) ≤ nuC) (hstd : Cx.CxStdPairTop S)
    (hlL : upsilon l ≤ Nc.ncL S (ω + 1)) (h : VrGen S l β) : Lr.LrReal S (upsilon l) (upsilon (l + β)) :=
  vrReal_gen hl hl1 hν hνβ h.1 h.2.1 h.2.2 hstd hlL

/-- **At every isolated uncovered Range restart `ν` of `[c, b)` some `β` with `ρ_ν < υ_{λ+β} ≤ b` and
`VrGen S λ β`.** -/
def VrVisGen (S : InaccSeq.{0}) (l b c : Ordinal.{0}) : Prop :=
  ∀ ν, CdRange S ν → c ≤ upsilon ν → upsilon ν < b → upsilon l < upsilon ν → ¬ TkCov S (upsilon l) ν →
    TkIso S (upsilon l) ν → ∃ β, upsilon ν < upsilon (l + β) ∧ upsilon (l + β) ≤ b ∧ VrGen S l β

/-- **`VrVisGen` gives the visible statements `Tk.TkVisI`.** -/
theorem vrVisI_of_gen (hL : CdLOWER S) {l b c : Ordinal.{0}} (hl : IsRestartIdx l) (hb : b ≤ nuC)
    (hbL : b ≤ Nc.ncL S (ω + 1)) (hstd : Cx.CxStdPairTop S) (h : VrVisGen S l b c) :
    TkVisI S (upsilon l) b c := by
  refine tkVisI_of_real hL hl rfl hb fun ν h1 h2 h3 h4 h5 h6 => ?_
  obtain ⟨β, hνβ, hβb, hG⟩ := h ν h1 h2 h3 h4 h5 h6
  have hν : upsilon l < nuC := (h4.trans h3).trans_le hb
  exact ⟨_, hνβ, hβb, vrReal_of_gen hl (hν.trans_le nuC_le_Om1) hν (hβb.trans hb) hstd
    ((h4.trans h3).le.trans hbL) hG⟩

/-- The visible statements at `m*` and every `L(n+1)` from `VrVisGen`. -/
theorem vrVis_all (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      VrVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      VrVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    TkVisI S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))) ∧
      ∀ n : ℕ, TkVisI S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))) := by
  have hν := Sh.shNu hU hV hVt hL
  have hstd : Cx.CxStdPairTop S := Tp.tpStdPairTop hν
  have hLW : CdLOWER S := Rz.rzLOWER_of_rest hL
  have hlt : ∀ k : ℕ, Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ Nc.ncL S (ω + 1) := fun k =>
    ((Pp.ppL_lt_omega k).trans (Qq.qqL_lt_succ S)).le
  refine ⟨?_, fun n => ?_⟩
  · obtain ⟨l, hl, e⟩ := Cv.cvM_restart (S := S)
    have h1 : Nc.ncL S 1 ≤ Nc.ncL S (ω + 1) := by simpa using hlt 0
    have := vrVisI_of_gen hLW hl (h1.trans hν) h1 hstd (h0 l hl e)
    rwa [← e] at this
  · obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
    have := vrVisI_of_gen hLW hl ((hlt (n + 1)).trans hν) (hlt (n + 1)) hstd (hn n l hl e)
    rwa [← e] at this

section Road

variable (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
  (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
  (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
  (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
  (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
  (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S) (hmove : Cx.CxStdMoveTop S)
include hU hO hL hV hVt hEQ htop hmove

/-- **The road with the repaired forms** (the conclusion of `Tk.tkRoadVis`). -/
theorem vrRoad
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      VrVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      VrVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  obtain ⟨v0, vn⟩ := vrVis_all hU hL hV hVt h0 hn
  exact tkRoadVis hU hO hL hV hVt hEQ htop hmove v0 vn

/-- **(F) with the repaired forms**: (CL), `m* ≤₁ L(1)`, `L(k) ≤₁ ν_C` and `Tk.TkSucc` at every `L(k)`
(`Vo.voLong_of_vis`). -/
theorem vrLong
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      VrVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      VrVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    (CdCL S ∧ le1 (Nc.ncL S 0) (Nc.ncL S 1)) ∧ (∀ k : ℕ, le1 (Nc.ncL S (k : Ordinal.{0})) nuC) ∧
      ∀ k : ℕ, TkSucc S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0})))) := by
  obtain ⟨v0, vn⟩ := vrVis_all hU hL hV hVt h0 hn
  exact Vo.voLong_of_vis hU hO hL hV hVt hEQ htop hmove v0 vn

end Road

/-! ## Non-vacuity at the no-go witness -/

/-- **At the no-go witness the form clause is a theorem**: at `a = L(k)`, `β₀ = g + ω²·2`
(`g = ω^{ω^{υ_{a+1}+1}}`), under `L(k+1) ≤ ν_C` and UPPER at the Range restarts with `RzRest`, `VrGen S a β₀` is
equivalent to its supply clause `VrSup S a β₀`. -/
theorem vrGen_wit_iff (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l) (k : ℕ)
    (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) :
    VrGen S (Nc.ncL S (k : Ordinal.{0})) (ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) + ω ^ 2 * 2) ↔
      VrSup S (Nc.ncL S (k : Ordinal.{0})) (ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) + ω ^ 2 * 2) := by
  obtain ⟨-, hβL, hF⟩ := vrForms_win (S := S) k hν
  refine ⟨fun h => h.2.2, fun h => ⟨fun g hg0 hgβ hgd => ?_, fun g hg0 hgβ hgd => Or.inr (hF g hg0 hgβ hgd), h⟩⟩
  have hm := upsilon_normal.strictMono
  set l := Nc.ncL S (k : Ordinal.{0})
  have hl := Te.teRst_L (S := S) k
  have hla : upsilon l = l := Te.teUps_L k
  have hν' : IsRestartIdx (l + g) :=
    ⟨(lt_of_lt_of_le (pos_iff_ne_zero.2 hl.1) le_self_add).ne', dvd_add hl.2 hgd⟩
  have h1 : l < upsilon (l + g) := by have := hm (lt_add_of_pos_right l hg0); rwa [hla] at this
  have h2 : upsilon (l + g) < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) :=
    (hm (add_lt_add_right hgβ l)).trans hβL
  obtain ⟨hr, hz⟩ := Ty.tyInner_rng hν' h1 h2
  exact hU _ hr hz

/-- **The witness of `Vo.voNoGo` is answered**: at `ν = a + g + ω²` (the Range restart of `Vo.voWit`), `β₀`
satisfies `ρ_ν < υ_{a+β₀} ≤ L(k+1)`, and `VrGen S a β₀` holds as soon as the supply clause `VrSup S a β₀` holds. -/
theorem vrVis_wit (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l) (k : ℕ)
    (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC)
    (hsup : VrSup S (Nc.ncL S (k : Ordinal.{0})) (ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) + ω ^ 2 * 2)) :
    ∃ β, upsilon (Nc.ncL S (k : Ordinal.{0}) + ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) + ω ^ 2) <
      upsilon (Nc.ncL S (k : Ordinal.{0}) + β) ∧
      upsilon (Nc.ncL S (k : Ordinal.{0}) + β) ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ∧
      VrGen S (Nc.ncL S (k : Ordinal.{0})) β := by
  obtain ⟨h1, h2, -⟩ := vrForms_win (S := S) k hν
  exact ⟨_, h1, h2.le, (vrGen_wit_iff hU k hν).2 hsup⟩

end Googology.Trans.PoR.InaccPsi.R2.Vr
