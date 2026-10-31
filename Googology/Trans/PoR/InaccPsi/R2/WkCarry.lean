import Googology.Trans.PoR.InaccPsi.R2.WfCarry
import Googology.Trans.PoR.InaccPsi.R2.TyRng

/-!
# Two clauses of the restricted carry `Wf.WfCarry` at the witness window: LOWER and the big-reach clause

`a = υ_λ = L(k)`, `ν` the chosen Range restart of the window (`L(k) < υ_ν < L(k+1)`, not covered: `¬ Tk.TkCov`),
`β = (ν − λ) + ω²`, `μ` a supply restart with `μ + B ≤ λ`, `f` an offset map (`Sl.SlOff f Os B`), `r = cdR`.
A *window* `w` for `L(k)` (`Ty.TyWin S k w`: `υ(Λ_B⁺) ≤ w < L(k)`, no `L(j)` in `(w, L(k))`).

* `wkWin_ex` (**a window exists for every `k`**: `υ(Λ_B⁺)` for `k = 0`, `L(n)` for `k = n+1`);
* `wkInner_rng` (**`μ + f z` is a Range restart with `RzRest`** when `w < υ_μ`: `υ_μ < υ_{μ+f z} < υ_λ = L(k)`),
  `wkLowerF` (**LOWER at `μ + f z`** from the road hypothesis `hL`: LOWER at the Range restarts with `RzRest`);
* `wkBig_vac` (**the big-reach clause is vacuous below `ν`**: for `λ + z < ν`, `r(λ+z) ≤ υ_ν < υ_{λ+β}`, since
  `ν` is not covered), `wkTop_eq` (the only offset `z < β` with `ω² | z` and `λ + z ≥ ν` is `z = ν − λ`),
  `wkBigF` (**the big-reach clause from its single instance at `z = ν − λ`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **A window exists for every `k`.** -/
theorem wkWin_ex (k : ℕ) : ∃ w, Ty.TyWin S k w := by
  rcases k with _ | n
  · exact ⟨_, Ty.tyWin_M⟩
  · exact ⟨_, Ty.tyWin_L n⟩

/-- The value of an offset map at a positive multiple of `ω²` is a positive multiple of `ω²` below `B`. -/
theorem wkOff_val {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}} {B : Ordinal.{0}}
    (hO : Sl.SlOff f Os B) {z : Ordinal.{0}} (hz : z ∈ Os) (hz0 : 0 < z) (hzd : ω ^ 2 ∣ z) :
    0 < f z ∧ ω ^ 2 ∣ f z ∧ f z < B := by
  refine ⟨?_, ?_, hO.bd z hz⟩
  · have h0m : (0 : Ordinal.{0}) ∈ (↑(insert 0 Os) : Set Ordinal.{0}) :=
      Finset.mem_coe.2 (Finset.mem_insert_self 0 Os)
    have hzm : z ∈ (↑(insert 0 Os) : Set Ordinal.{0}) := Finset.mem_coe.2 (Finset.mem_insert_of_mem hz)
    have h := hO.mono h0m hzm hz0
    rwa [hO.zero] at h
  · obtain ⟨q, rfl⟩ := hzd; exact hO.dvd q

/-- **`μ + f z` is a Range restart with `RzRest`** when the supply restart lies above a window `w` of `L(k)`. -/
theorem wkInner_rng {k : ℕ} {l μ w B : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (hlk : Nc.ncL S (k : Ordinal.{0}) = upsilon l) (hw : Ty.TyWin S k w) (hwμ : w < upsilon μ)
    (hμ : IsRestartIdx μ) (hB : μ + B ≤ l) (hO : Sl.SlOff f Os B) {z : Ordinal.{0}} (hz : z ∈ Os)
    (hz0 : 0 < z) (hzd : ω ^ 2 ∣ z) : CdRange S (μ + f z) ∧ Rz.RzRest (μ + f z) := by
  have hm := upsilon_normal.strictMono
  obtain ⟨hp, hd, hb⟩ := wkOff_val hO hz hz0 hzd
  have hr : IsRestartIdx (μ + f z) :=
    ⟨((pos_iff_ne_zero.2 hμ.1).trans_le le_self_add).ne', dvd_add hμ.2 hd⟩
  have h1 : upsilon μ < upsilon (μ + f z) := hm (lt_add_of_pos_right μ hp)
  have h2 : upsilon (μ + f z) < upsilon l := hm (((add_lt_add_iff_left μ).2 hb).trans_le hB)
  exact Ty.tyWin_rng hw hr (hwμ.trans h1) (h2.trans_eq hlk.symm)

/-- **LOWER at `μ + f z`** from the road hypothesis `hL` (LOWER at the Range restarts with `RzRest`). -/
theorem wkLowerF (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) {k : ℕ} {l μ w B : Ordinal.{0}}
    {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (hlk : Nc.ncL S (k : Ordinal.{0}) = upsilon l) (hw : Ty.TyWin S k w) (hwμ : w < upsilon μ)
    (hμ : IsRestartIdx μ) (hB : μ + B ≤ l) (hO : Sl.SlOff f Os B) :
    ∀ z ∈ Os, 0 < z → ω ^ 2 ∣ z → CdLower S (μ + f z) := by
  intro z hz hz0 hzd
  obtain ⟨hR, hZ⟩ := wkInner_rng hlk hw hwμ hμ hB hO hz hz0 hzd
  exact hL _ hR hZ

/-- **The big-reach clause is vacuous below `ν`**: an inner restart `λ + z < ν` of the long region does not cover
`ν`, so `r(λ+z) ≤ υ_ν < υ_{λ+β}`. -/
theorem wkBig_vac {k : ℕ} {l ν β z : Ordinal.{0}} (hl : IsRestartIdx l)
    (hlk : Nc.ncL S (k : Ordinal.{0}) = upsilon l) (hν : upsilon ν < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
    (hcov : ¬ Tk.TkCov S (upsilon l) ν) (hβ : upsilon ν < upsilon (l + β)) (hz0 : 0 < z) (hzd : ω ^ 2 ∣ z)
    (hzν : l + z < ν) : cdR S (l + z) < upsilon (l + β) := by
  have hm := upsilon_normal.strictMono
  have hr : IsRestartIdx (l + z) :=
    ⟨((pos_iff_ne_zero.2 hl.1).trans_le le_self_add).ne', dvd_add hl.2 hzd⟩
  have h1 : upsilon l < upsilon (l + z) := hm (lt_add_of_pos_right l hz0)
  have h2 : upsilon (l + z) < upsilon ν := hm hzν
  obtain ⟨hR, -⟩ := Ty.tyInner_rng (S := S) (k := k) hr (hlk.trans_lt h1) (h2.trans hν)
  have hle : cdR S (l + z) ≤ upsilon ν := by
    by_contra hc
    exact hcov ⟨l + z, hR, h1, h2, lt_of_not_ge hc⟩
  exact hle.trans_lt hβ

/-- **The only offset `z < (ν − λ) + ω²` with `ω² | z` and `λ + z ≥ ν` is `z = ν − λ`.** -/
theorem wkTop_eq {l ν z : Ordinal.{0}} (hl : IsRestartIdx l) (hν : IsRestartIdx ν) (hlν : l < ν)
    (hzd : ω ^ 2 ∣ z) (hzβ : z < ν - l + ω ^ 2) (hzν : ν ≤ l + z) : z = ν - l := by
  have e : l + (ν - l) = ν := Ordinal.add_sub_cancel_of_le hlν.le
  have hd : ω ^ 2 ∣ ν - l := (Ordinal.dvd_add_iff hl.2).1 (by rw [e]; exact hν.2)
  have hge : ν - l ≤ z := by
    rw [← e] at hzν; exact (add_le_add_iff_left l).1 hzν
  set d := z - (ν - l) with hddef
  have ez : z = (ν - l) + d := (Ordinal.add_sub_cancel_of_le hge).symm
  have hdlt : d < ω ^ 2 := by rw [ez] at hzβ; exact (add_lt_add_iff_left _).1 hzβ
  have hdd : ω ^ 2 ∣ d := (Ordinal.dvd_add_iff hd).1 (by rw [← ez]; exact hzd)
  have hd0 : d = 0 := by
    obtain ⟨q, hq⟩ := hdd
    rcases eq_or_ne q 0 with h0 | h0
    · rw [hq, h0, mul_zero]
    · exfalso
      have : ω ^ 2 * 1 ≤ ω ^ 2 * q := mul_le_mul_right (Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 h0)) _
      rw [mul_one, ← hq] at this
      exact absurd hdlt (not_lt.2 this)
  rw [ez, hd0, add_zero]

/-- **The big-reach clause of `Wf.WfCarry` from its single instance at `z = ν − λ`** (all other offsets of the
window are vacuous, `wkBig_vac`). -/
theorem wkBigF {k : ℕ} {l ν μ B : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (hl : IsRestartIdx l) (hν : IsRestartIdx ν) (hlν : upsilon l < upsilon ν)
    (hlk : Nc.ncL S (k : Ordinal.{0}) = upsilon l) (hνk : upsilon ν < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
    (hcov : ¬ Tk.TkCov S (upsilon l) ν)
    (htop : ν - l ∈ Os → upsilon (l + (ν - l + ω ^ 2)) ≤ cdR S ν → upsilon (μ + B) ≤ cdR S (μ + f (ν - l))) :
    ∀ z ∈ Os, 0 < z → ω ^ 2 ∣ z → z < ν - l + ω ^ 2 →
      (upsilon (l + (ν - l + ω ^ 2)) ≤ cdR S (l + z) → upsilon (μ + B) ≤ cdR S (μ + f z)) := by
  have hm := upsilon_normal.strictMono
  have hlν' : l < ν := hm.lt_iff_lt.1 hlν
  have e : l + (ν - l) = ν := Ordinal.add_sub_cancel_of_le hlν'.le
  have hβ : upsilon ν < upsilon (l + (ν - l + ω ^ 2)) := by
    rw [← add_assoc, e]; exact hm (lt_add_of_pos_right ν (pow_pos omega0_pos 2))
  intro z hz hz0 hzd hzβ hbig
  rcases lt_or_ge (l + z) ν with hlt | hge
  · exact absurd hbig (not_le.2 (wkBig_vac hl hlk hνk hcov hβ hz0 hzd hlt))
  · have hz' := wkTop_eq hl hν hlν' hzd hzβ hge
    subst hz'
    rw [e] at hbig
    exact htop hz hbig

end Googology.Trans.PoR.InaccPsi.R2.Wk

#print axioms Googology.Trans.PoR.InaccPsi.R2.Wk.wkWin_ex
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wk.wkInner_rng
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wk.wkLowerF
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wk.wkBig_vac
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wk.wkTop_eq
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wk.wkBigF
