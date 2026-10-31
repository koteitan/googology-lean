import Googology.Trans.PoR.InaccPsi.R2.WdRoad
import Googology.Trans.PoR.InaccPsi.R2.VwRoad
import Googology.Trans.PoR.InaccPsi.R2.WfReal

/-!
# The road with the restricted supply

`L(ξ) = Nc.ncL S ξ`, `F = ι(Γ(φ(Ω₁·Ω₁, G+1))·ω)` (the frontier of `Hl.hlU`), `hν := L(ω+1) ≤ ν_C`.

* `wfRoad` (**the conclusion of `Wd.wdRoadL` with `h0` / `hn` in the restricted form `WfVisGen`**): the same
  hypotheses `hUH`, `hLH`, `hVH`, `hVt`, `hT`, `hF`, and `h0'` / `hn'` (`WfVisGen` at `m*` and every `L(n+1)`);
* `wfRoad_of_vr` (**`Wd.wdRoadL` is a corollary**: the old `h0` / `hn` give `h0'` / `hn'` by `wfVisGen_of_vr`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

variable {S : InaccSeq.{0}}

/-- **The road with the restricted supply** (`Wd.wdRoadL` with `Vr.VrVisGen` replaced by `WfVisGen`). -/
theorem wfRoad
    (hUH : ∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdUpper S l)
    (hLH : ∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdLower S l)
    (hVH : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l)
    (hVt : ∀ l, Cd.CdRange S l → Nc.ncL S ω < upsilon l →
      Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l)
    (hT : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      WfVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      WfVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cd.CdCL S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S (k + 1)) (Nc.ncL S (ω + 1)) := by
  have hν0 := Wd.wdNu hUH hLH hVH hVt
  have hEQtop : Cx.CxEQtop S := (Wd.wdEQtop_iff hν0).2 ⟨hT hν0, hF hν0⟩
  have htop : Cx.CxTCtopOff S := Wa.waTCtopOff hν0
  have hmove : Cx.CxStdMoveTop S := Wa.waStdMoveTop
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
  obtain ⟨v0, vn⟩ := wfVis_all hUR hLR hVlow hVhigh h0 hn
  have hv := Tk.tkRoadVis hUR hO hLR hVlow hVhigh hEQtop htop hmove v0 vn
  rcases hv with ⟨hEQ, hTC, hB2, hTT, hCL, _, _, _, _, _, _, _, _, _⟩
  have hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1)) := by
    intro n
    exact (Cx.cxTCAt_L_iff hTT n).1 (hTC n _ (Cx.cxC_lt n))
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
  exact Vp.vpRoadA hUV hLV hVV hEQ hν Vs.vsPiLev hTT hcl

/-- **`Wd.wdRoadL` from `wfRoad`**: the old supply hypotheses give the restricted ones (`wfVisGen_of_vr`), so the
restricted road is no stronger in its hypotheses. -/
theorem wfRoad_of_vr
    (hUH : ∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdUpper S l)
    (hLH : ∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdLower S l)
    (hVH : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l)
    (hVt : ∀ l, Cd.CdRange S l → Nc.ncL S ω < upsilon l →
      Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l)
    (hT : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      Vr.VrVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      Vr.VrVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    nuC = Nc.ncL S (ω + 1) :=
  (wfRoad hUH hLH hVH hVt hT hF (fun l hl e => wfVisGen_of_vr (h0 l hl e))
    (fun n l hl e => wfVisGen_of_vr (hn n l hl e))).2.2.2.2.1

end Googology.Trans.PoR.InaccPsi.R2.Wf
