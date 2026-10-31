import Googology.Trans.PoR.InaccPsi.R2.WaTop

/-!
# The joined road without `CxStdMoveTop` and `CxTCtopOff`

`L(ξ) = Nc.ncL S ξ`, `F = ι(Γ(φ(Ω₁·Ω₁, G+1))·ω)` (the frontier of `Hl.hlU`).

* `waRoad`: the conclusion of `Vw.vwRoad` from its hypotheses less `Cx.CxStdMoveTop` (`Wa.waStdMoveTop`) and
  `Cx.CxTCtopOff` (from `L(ω+1) ≤ ν_C`, which `Sh.shNu` gives from UPPER, LOWER, CapV: `Wa.waTCtopOff`);
* `waRoadUx`: the same with `Cx.CxEQtop` replaced by `UxAtMove26`, `RnThMoveM`, `RnEQhi2` (each asked only under
  `L(ω+1) ≤ ν_C`; `Wa.waEQtop_ux`);
* `waRoad_hyps` (**non-vacuity**): the hypotheses of `waRoad` are those of `Vw.vwRoad` less two, and `hEQtop`
  follows from the road's own conclusion `CdEQ` (`Wa.waEQtop_of_EQ`); `waRoadUx_hyps`: the three new hypotheses
  follow from `LjEQhi` and `LjAtMove` (`Rn.rnRoadD_hyps`, with `Ux.uxAtMove26_of25`, `Ud.udAtMove25_of24`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wa

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

variable {S : InaccSeq.{0}}

/-- **The road of `Vw.vwRoad` with `CxStdMoveTop` and `CxTCtopOff` proved.** -/
theorem waRoad
    (hUH : ∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdUpper S l)
    (hLH : ∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdLower S l)
    (hVH : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l)
    (hVt : ∀ l, Cd.CdRange S l → Nc.ncL S ω < upsilon l →
      Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l)
    (hEQtop : Cx.CxEQtop S)
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
  have hUR : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l := by
    intro l hr _
    by_cases h : F ≤ l
    · exact hUH l hr h
    · exact (Hl.hlU_enum S hr (lt_of_not_ge h)).1
  have hLR : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l := by
    intro l hr _
    by_cases h : F ≤ l
    · exact hLH l hr h
    · exact (Hl.hlU_enum S hr (lt_of_not_ge h)).2
  have hVlow : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l := by
    intro l hr hu _
    by_cases h : F ≤ l
    · exact hVH l hr hu h
    · exact Hl.hlU_capV S hr (lt_of_not_ge h)
  have hVhigh : ∀ l, Cd.CdRange S l → Nc.ncL S ω < upsilon l → Cd.CdCapV S l := by
    intro l hr hu
    by_cases h : F ≤ l
    · exact hVt l hr hu h
    · exact Hl.hlU_capV S hr (lt_of_not_ge h)
  have hν : Nc.ncL S (ω + 1) ≤ nuC := Sh.shNu hUR hVlow hVhigh hLR
  exact Vw.vwRoad hUH hLH hVH hVt hEQtop (waTCtopOff hν) waStdMoveTop h0 hn

/-- **The road with `CxEQtop` replaced by `UxAtMove26`, `RnThMoveM`, `RnEQhi2`.** -/
theorem waRoadUx
    (hUH : ∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdUpper S l)
    (hLH : ∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdLower S l)
    (hVH : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l)
    (hVt : ∀ l, Cd.CdRange S l → Nc.ncL S ω < upsilon l →
      Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l)
    (hat : Nc.ncL S (ω + 1) ≤ nuC → Ux.UxAtMove26 S)
    (hM : Nc.ncL S (ω + 1) ≤ nuC → Rn.RnThMoveM S)
    (hE : Nc.ncL S (ω + 1) ≤ nuC → Rn.RnEQhi2 S)
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
  have hUR : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l := by
    intro l hr _
    by_cases h : F ≤ l
    · exact hUH l hr h
    · exact (Hl.hlU_enum S hr (lt_of_not_ge h)).1
  have hLR : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l := by
    intro l hr _
    by_cases h : F ≤ l
    · exact hLH l hr h
    · exact (Hl.hlU_enum S hr (lt_of_not_ge h)).2
  have hVlow : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l := by
    intro l hr hu _
    by_cases h : F ≤ l
    · exact hVH l hr hu h
    · exact Hl.hlU_capV S hr (lt_of_not_ge h)
  have hVhigh : ∀ l, Cd.CdRange S l → Nc.ncL S ω < upsilon l → Cd.CdCapV S l := by
    intro l hr hu
    by_cases h : F ≤ l
    · exact hVt l hr hu h
    · exact Hl.hlU_capV S hr (lt_of_not_ge h)
  have hν : Nc.ncL S (ω + 1) ≤ nuC := Sh.shNu hUR hVlow hVhigh hLR
  exact waRoad hUH hLH hVH hVt (waEQtop_ux hν (hat hν) (hM hν) (hE hν)) h0 hn

/-- **Non-vacuity of `hEQtop`**: it follows from the road's own conclusion `CdEQ`, and `vwRoad`'s two other
top-window hypotheses are theorems (given the road hypotheses), so `waRoad` asks strictly no more than
`Vw.vwRoad`. -/
theorem waRoad_hyps (hEQ : Cd.CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) :
    Cx.CxEQtop S ∧ Cx.CxTCtopOff S ∧ Cx.CxStdMoveTop S :=
  ⟨waEQtop_of_EQ hEQ, waTCtopOff hν, waStdMoveTop⟩

/-- **Non-vacuity of `waRoadUx`**: its three new hypotheses follow from those of `Lj.ljRoadA` (`LjAtMove`,
`LjEQhi`), through `Ud.UdAtMove25`. -/
theorem waRoadUx_hyps (hat : Nc.ncL S (ω + 1) ≤ nuC → Ud.UdAtMove25 S)
    (hhi : Nc.ncL S (ω + 1) ≤ nuC → Lj.LjEQhi S) :
    (Nc.ncL S (ω + 1) ≤ nuC → Ux.UxAtMove26 S) ∧ (Nc.ncL S (ω + 1) ≤ nuC → Rn.RnThMoveM S) ∧
      (Nc.ncL S (ω + 1) ≤ nuC → Rn.RnEQhi2 S) :=
  ⟨Ux.uxRoad_hyps hat, fun hν => Rn.rnThMoveM_of hν (hhi hν), fun hν => Rn.rnEQhi2_of (hhi hν)⟩

end Googology.Trans.PoR.InaccPsi.R2.Wa
