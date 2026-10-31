import Googology.Trans.PoR.InaccPsi.R2.WqWit

/-!
# The carry at the low windows: the big-reach clause is vacuous, LOWER is a road hypothesis

`a = υ_λ = L(k)`, `ν` an uncovered Range restart of the window of `L(k)` with `ν − λ < υ_{λ+2}` (a "low window";
the witness window of `Vo.voNoGo` is one: `Wq.wqWit_low`, `Wq.wqLow_u2`), `β = (ν − λ) + ω²`.

* `wqBigLow` (**the big-reach clause of `Wf.WfCarry` holds at every low window for EVERY offset map**: the only
  offset that could reach `υ_{λ+β}` is `ν − λ` (`Wk.wkBigF`), and `r(ν) < υ_{ν+ω²}` there (`Wq.wqBigTop`));
* `wqCarry_low` (**`Wf.WfCarry` at a low window from the image clause alone**: LOWER by `Wk.wkLowerF` from the road
  hypothesis `hL`, the big reach by `wqBigLow`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **The big-reach clause at a low window, for every offset map** (given `L(k+1) ≤ ν_C`). -/
theorem wqBigLow {k : ℕ} (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {l ν μ B : Ordinal.{0}}
    {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (hl : IsRestartIdx l) (hνR : IsRestartIdx ν) (hlν : upsilon l < upsilon ν)
    (hlk : Nc.ncL S (k : Ordinal.{0}) = upsilon l) (hνk : upsilon ν < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
    (hcov : ¬ Tk.TkCov S (upsilon l) ν) (hlow : ν - l < upsilon (l + 2)) :
    ∀ z ∈ Os, 0 < z → ω ^ 2 ∣ z → z < ν - l + ω ^ 2 →
      (upsilon (l + (ν - l + ω ^ 2)) ≤ cdR S (l + z) → upsilon (μ + B) ≤ cdR S (μ + f z)) := by
  have hm := upsilon_normal.strictMono
  have hll : l = Nc.ncL S (k : Ordinal.{0}) := hm.injective (hlk.symm.trans (Te.teUps_L (S := S) k).symm)
  have hlν' : l < ν := hm.lt_iff_lt.1 hlν
  have e : l + (ν - l) = ν := Ordinal.add_sub_cancel_of_le hlν'.le
  have hd : ω ^ 2 ∣ ν - l := (Ordinal.dvd_add_iff hl.2).1 (by rw [e]; exact hνR.2)
  have hd0 : 0 < ν - l := by
    rcases eq_or_lt_of_le (zero_le : (0 : Ordinal.{0}) ≤ ν - l) with h | h
    · rw [← h, add_zero] at e; exact absurd e hlν'.ne
    · exact h
  refine Wk.wkBigF hl hνR hlν hlk hνk hcov fun _ hbig => ?_
  exfalso
  have hlt := wqBigTop (S := S) k hν hd0 hd (by rw [← hll]; exact hlow)
  rw [← hll, e] at hlt
  exact absurd hbig (not_le.2 hlt)

/-- **`Wf.WfCarry` at a low window from the image clause**: given the road hypothesis `hL` (LOWER at every Range
restart with `RzRest`), `L(k+1) ≤ ν_C`, a window `w < υ_μ` of `L(k)`, and map data `μ + B ≤ λ`, `Sl.SlOff f Os B`,
the image clause is the only part of the carry left. -/
theorem wqCarry_low (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    {k : ℕ} (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {l ν μ w B : Ordinal.{0}}
    {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (hl : IsRestartIdx l) (hνR : IsRestartIdx ν) (hlν : upsilon l < upsilon ν)
    (hlk : Nc.ncL S (k : Ordinal.{0}) = upsilon l) (hνk : upsilon ν < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
    (hcov : ¬ Tk.TkCov S (upsilon l) ν) (hlow : ν - l < upsilon (l + 2))
    (hw : Ty.TyWin S k w) (hwμ : w < upsilon μ) (hμ : IsRestartIdx μ) (hB : μ + B ≤ l)
    (hO : Sl.SlOff f Os B) (hOs : ∀ d ∈ Os, d < ν - l + ω ^ 2)
    (hI : ∀ g ∈ Os, 0 < g → ω ^ 2 ∣ g →
      ∀ E : Vr.VrE, Vr.VrWF l (ν - l + ω ^ 2) E → Vr.vrVal l E = cdR S (l + g) → Vr.VrOs l Os E →
        Wf.WfR l μ E → Vr.vrImg l μ f E ≤ cdR S (μ + f g)) :
    Wf.WfCarry S l (ν - l + ω ^ 2) μ f B Os := by
  intro g hg hg0 hgd
  exact ⟨Wk.wkLowerF hL hlk hw hwμ hμ hB hO g hg hg0 hgd,
    wqBigLow hν hl hνR hlν hlk hνk hcov hlow g hg hg0 hgd (hOs g hg), hI g hg hg0 hgd⟩

end Googology.Trans.PoR.InaccPsi.R2.Wq
