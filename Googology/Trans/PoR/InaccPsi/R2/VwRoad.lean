import Googology.Trans.PoR.InaccPsi.R2.VsTop
import Googology.Trans.PoR.InaccPsi.R2.HlU
import Googology.Trans.PoR.InaccPsi.R2.VrRoad

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

variable {S : InaccSeq.{0}}

/-- Join the road hypotheses, deriving every restart fact below the proved Hl frontier. -/
theorem vwRoad
    (hUH : ∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdUpper S l)
    (hLH : ∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdLower S l)
    (hVH : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l)
    (hVt : ∀ l, Cd.CdRange S l → Nc.ncL S ω < upsilon l →
      Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l)
    (hEQtop : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S) (hmove : Cx.CxStdMoveTop S)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      Vr.VrVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      Vr.VrVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cd.CdCL S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S (k + 1)) (Nc.ncL S (ω + 1)) := by
  let F : Ordinal.{0} := Bt.iota S (Gc.gcG Hl.hlU.B * ω)
  have hUall : ∀ l, Cd.CdRange S l → Cd.CdUpper S l := by
    intro l hr
    by_cases h : F ≤ l
    · exact hUH l hr h
    · exact (Hl.hlU_enum S hr (lt_of_not_ge h)).1
  have hLall : ∀ l, Cd.CdRange S l → Cd.CdLower S l := by
    intro l hr
    by_cases h : F ≤ l
    · exact hLH l hr h
    · exact (Hl.hlU_enum S hr (lt_of_not_ge h)).2
  have hVlow : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω →
      Rz.RzRest l → Cd.CdCapV S l := by
    intro l hr hu _
    by_cases h : F ≤ l
    · exact hVH l hr hu h
    · exact Hl.hlU_capV S hr (lt_of_not_ge h)
  have hVhigh : ∀ l, Cd.CdRange S l → Nc.ncL S ω < upsilon l → Cd.CdCapV S l := by
    intro l hr hu
    by_cases h : F ≤ l
    · exact hVt l hr hu h
    · exact Hl.hlU_capV S hr (lt_of_not_ge h)
  have hUR : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l :=
    fun l hr _ => hUall l hr
  have hLR : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l :=
    fun l hr _ => hLall l hr
  have hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l := by
    intro l hr hlR hfix
    exact (Rz.rzUpper_nonfix hr.1 hlR hfix (Rz.rz_range_pv hr)).1.1 (hUall l hr)
  have hv := Vr.vrRoad hUR hO hLR hVlow hVhigh hEQtop htop hmove h0 hn
  rcases hv with ⟨hEQ, hTC, hB2, hT, hCL, _, _, _, _, _, _, _, _, _⟩
  have hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1)) := by
    intro n
    exact (Cx.cxTCAt_L_iff hT n).1 (hTC n _ (Cx.cxC_lt n))
  have hrest : Cd.CdTCrest S := fun n x hx => Or.inr (Or.inr (hTC n x hx))
  have hh := Hl.hlU_road S hUH hLH hVH hCL hEQ hrest hB2
  have hν : Nc.ncL S (ω + 1) ≤ nuC := hh.1.symm.le
  have hUV : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdUpper S l :=
    fun l hr _ => hUall l hr
  have hLV : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdLower S l :=
    fun l hr _ => hLall l hr
  have hVV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω →
      Bt.iota S Ge.geV ≤ l → Cd.CdCapV S l := by
    intro l hr hu _
    by_cases h : F ≤ l
    · exact hVH l hr hu h
    · exact Hl.hlU_capV S hr (lt_of_not_ge h)
  exact Vp.vpRoadA hUV hLV hVV hEQ hν Vs.vsPiLev hT hcl

#print axioms vwRoad

end Googology.Trans.PoR.InaccPsi.R2.Vw
