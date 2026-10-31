import Googology.Trans.PoR.InaccPsi.R2.WkCarry
import Googology.Trans.PoR.InaccPsi.R2.WkRead
import Googology.Trans.PoR.InaccPsi.R2.WfWin
import Googology.Trans.PoR.InaccPsi.R2.WfRefute
import Googology.Trans.PoR.InaccPsi.R2.VoNoGo
import Googology.Trans.PoR.InaccPsi.R2.LsName

/-!
# The witness window exists, the big reach at `ν` is vacuous, and the forms at the low windows

`a = L(k)`, `u₁ = υ_{a+1}`, `c = ω^{u₁+1}`, `g = ω^c`, `ν₀ = a + g + ω²` (the window of the `Vo.voNoGo` witness).
Every inner restart `a + z` with `0 < z < υ_{a+2}` has `r(a+z) = υ_{a+(z+ω+1)} + m_{a+z}`, `m_{a+z} ≤ z`
(`Vr.vrR_inner`), so it never reaches `υ_{a+(z+ω²)}`.

* `wqWitCtx` (**the witness context exists, with `ν₀` explicit**: `ν₀` is a Range restart in the window
  `[υ(a + W(a)), L(k+1))`, uncovered from `a`, isolated from below; given `L(k+1) ≤ ν_C`);
* `wqMu_ex` (**supply restarts below every `L(k)`**: Range, code `G₂+1`, below `L(ω)`, with `Wc.WcRead0`);
* `wqBigTop` (**`r(a+z) < υ_{a+(z+ω²)}` for `0 < z < υ_{a+2}`, `ω² | z`**), so the big-reach clause at `ν` itself is
  vacuous at every window `ν` with `ν − a < υ_{a+2}`;
* `wqWit_low` (`g + ω² < ω^{c+1}`: the witness window is a low window), `wqLow_u2` (`ω^{c+1} < υ_{a+2}`);
* `wqForms_low` (**the forms clause at every window `β ≤ ω^{c+1}`, `ω² | β`**), `wqForms_eps` (**the forms clause
  at every window `β ≤ ε_{u₁+1}`, `ω² | β`**: codes `m ≤ z < ε_{u₁+1}`, `Vr.vrForm_code`), `wqEps_beta`, `wqEps_u2`
  (`ε_{u₁+1} ≤ υ_{a+2}`), `wqWit_eps` (`g + ω² < ε_{u₁+1}`: the witness window lies below `ε_{u₁+1}`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- `ω^{c+1}` is additive principal and above `g + ω²` (`c = ω^{u+1}`, `g = ω^c`). -/
theorem wqWit_low (u : Ordinal.{0}) :
    ω ^ ω ^ (u + 1) + ω ^ 2 < ω ^ (ω ^ (u + 1) + 1) := by
  set c := ω ^ (u + 1) with hc
  have hωc : ω ≤ c := left_le_opow ω (lt_of_le_of_lt zero_le (lt_add_one u))
  have hP : IsPrincipal (· + ·) (ω ^ (c + 1)) := isPrincipal_add_omega0_opow _
  have hgc1 : ω ^ c < ω ^ (c + 1) := (opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_one c)
  have h2 : ω ^ 2 < ω ^ (c + 1) := by
    rw [Vo.vo_e2]
    refine (opow_lt_opow_iff_right one_lt_omega0).2 ?_
    exact ((natCast_lt_omega0 2).trans_le hωc).trans (lt_add_one c)
  exact hP hgc1 h2

/-- `ω^{c+1} < υ_{a+2}` at `a = L(k)`. -/
theorem wqLow_u2 (k : ℕ) :
    ω ^ (ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) + 1) < upsilon (Nc.ncL S (k : Ordinal.{0}) + 2) := by
  obtain ⟨-, -, hu2E, hu12, -, -, -, -, -⟩ := Vr.vr_facts (S := S) k
  have hωu2 : ω ≤ upsilon (Nc.ncL S (k : Ordinal.{0}) + 2) := Vo.vo_omega_le hu2E (InE.pos hu2E)
  have h1 : (1 : Ordinal.{0}) < upsilon (Nc.ncL S (k : Ordinal.{0}) + 2) := one_lt_omega0.trans_le hωu2
  exact hu2E.opow_lt (hu2E.add_lt (hu2E.opow_lt (hu2E.add_lt hu12 h1)) h1)

/-- **The big reach is never reached in the low region**: `r(a+z) < υ_{a+(z+ω²)}` for `0 < z < υ_{a+2}`,
`ω² | z`, `a = L(k)`, given `L(k+1) ≤ ν_C`. -/
theorem wqBigTop (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {z : Ordinal.{0}} (hz0 : 0 < z)
    (hzd : ω ^ 2 ∣ z) (hzu : z < upsilon (Nc.ncL S (k : Ordinal.{0}) + 2)) :
    cdR S (Nc.ncL S (k : Ordinal.{0}) + z) < upsilon (Nc.ncL S (k : Ordinal.{0}) + (z + ω ^ 2)) := by
  have hm := upsilon_normal.strictMono
  obtain ⟨hl0, -, -, -, -, -, -, -, -⟩ := Vr.vr_facts (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  rw [Vr.vrR_inner k hν hz0 hzd hzu]
  have hωz : ω ≤ z := Vr.vr_omega_le hz0.ne' hzd
  have hcz : cdCode S (l + z) ≤ z := by
    rw [Vo.voCode_add k hωz hzu]; exact (cdOff_le _).trans (Cp.cpExp_le hz0.ne')
  set F := upsilon (l + (z + ω + 1) + 1) with hF
  have hFE : InE F := upsPt_inE (upsPt_upsilon (lt_of_lt_of_le hl0 (le_self_add.trans le_self_add)))
  have hEF : upsilon (l + (z + ω + 1)) < F := hm (lt_add_one _)
  have hmF : cdCode S (l + z) < F := by
    refine (hcz.trans_lt hzu).trans_le (hm.monotone ?_)
    rw [add_assoc]
    refine (add_le_add_iff_left l).2 ?_
    calc (2 : Ordinal.{0}) ≤ ω := (natCast_lt_omega0 2).le
      _ ≤ z := hωz
      _ ≤ z + ω + 1 + 1 := le_self_add.trans (le_self_add.trans le_self_add)
  refine (hFE.add_lt hEF hmF).trans_le (hm.monotone ?_)
  rw [add_assoc]
  refine (add_le_add_iff_left l).2 ?_
  rw [add_assoc, add_assoc]
  refine (add_le_add_iff_left z).2 ?_
  have h2 : (1 : Ordinal.{0}) + 1 = 2 := one_add_one_eq_two
  rw [h2]
  exact Vo.vo_om2.le

/-- **The forms clause at every low window**: for `ω² | β ≤ ω^{c+1}` every inner restart `a + z`
(`0 < z < β`, `ω² | z`) has a repaired form (`Vr.vrForm_inner`), given `L(k+1) ≤ ν_C`. -/
theorem wqForms_low (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {β : Ordinal.{0}}
    (hβd : ω ^ 2 ∣ β) (hβ : β ≤ ω ^ (ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) + 1)) :
    ∀ z, 0 < z → z < β → ω ^ 2 ∣ z → Vr.VrForm S (Nc.ncL S (k : Ordinal.{0})) β z := by
  intro z hz0 hzβ hzd
  have hstep := Vr.vr_dvd_step hzd hβd hzβ
  have hω1 : ω + 1 < ω ^ 2 := (add_lt_add_right one_lt_two ω).trans Vo.vo_om2
  have hzβ' : z + ω + 1 < β := by
    rw [add_assoc]; exact ((add_lt_add_iff_left z).2 hω1).trans_le hstep
  exact Vr.vrForm_inner k hν hz0 hzd (hzβ.trans_le hβ) hzβ'

/-- **The forms clause at every window below the next `ε`-number above `u₁`**: for `ω² | β ≤ ε_{u₁+1}` (`eN u₁`)
every inner restart `a + z` (`0 < z < β`, `ω² | z`) has a repaired form: its code `m ≤ z < ε_{u₁+1}` has no
`ε`-number in `(u₁, m]` (`Vr.vrForm_code`); given `L(k+1) ≤ ν_C`. -/
theorem wqForms_eps (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {β : Ordinal.{0}}
    (hβd : ω ^ 2 ∣ β) (hβ : β ≤ eN (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1))) :
    ∀ z, 0 < z → z < β → ω ^ 2 ∣ z → Vr.VrForm S (Nc.ncL S (k : Ordinal.{0})) β z := by
  obtain ⟨-, -, hu2E, hu12, -, -, -, -, -⟩ := Vr.vr_facts (S := S) k
  intro z hz0 hzβ hzd
  have hstep := Vr.vr_dvd_step hzd hβd hzβ
  have hω1 : ω + 1 < ω ^ 2 := (add_lt_add_right one_lt_two ω).trans Vo.vo_om2
  have hzβ' : z + ω + 1 < β := by
    rw [add_assoc]; exact ((add_lt_add_iff_left z).2 hω1).trans_le hstep
  have hzE : z < eN (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) := hzβ.trans_le hβ
  have hzu : z < upsilon (Nc.ncL S (k : Ordinal.{0}) + 2) := hzE.trans_le (eN_le hu12 hu2E)
  have hωz : ω ≤ z := Vr.vr_omega_le hz0.ne' hzd
  have hcz : cdCode S (Nc.ncL S (k : Ordinal.{0}) + z) ≤ z := by
    rw [Vo.voCode_add k hωz hzu]; exact (cdOff_le _).trans (Cp.cpExp_le hz0.ne')
  refine Vr.vrForm_code k hν hz0 hzd hzu hzβ' fun e he1 he2 hE => ?_
  exact absurd ((he2.trans hcz).trans_lt hzE) (not_lt.2 (eN_le he1 hE))

/-- **A window below `ε_{u+1}`**: `ν − a < ε_{u+1}` with `ω² | ν − a` gives `β = (ν − a) + ω² ≤ ε_{u+1}`. -/
theorem wqEps_beta {u d : Ordinal.{0}} (hd : ω ^ 2 ∣ d) (hdl : d < eN u) :
    ω ^ 2 ∣ d + ω ^ 2 ∧ d + ω ^ 2 ≤ eN u := by
  have hE := eN_E u
  have h2 : (2 : Ordinal.{0}) ≤ eN u :=
    (natCast_lt_omega0 2).le.trans (Vo.vo_omega_le hE (InE.pos hE))
  have hdv : ω ^ 2 ∣ eN u := by
    have h := Vo.vo_e2 ▸ opow_dvd_opow ω h2
    unfold InE at hE; rwa [hE] at h
  exact ⟨dvd_add hd dvd_rfl, Vr.vr_dvd_step hd hdv hdl⟩

/-- `ε_{u₁+1} ≤ υ_{a+2}` at `a = L(k)`. -/
theorem wqEps_u2 (k : ℕ) :
    eN (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) ≤ upsilon (Nc.ncL S (k : Ordinal.{0}) + 2) := by
  obtain ⟨-, -, hu2E, hu12, -, -, -, -, -⟩ := Vr.vr_facts (S := S) k
  exact eN_le hu12 hu2E

/-- **The witness window lies below `ε_{u+1}`**: `ω^{ω^{u+1}} + ω² < ε_{u+1}`. -/
theorem wqWit_eps (u : Ordinal.{0}) : ω ^ ω ^ (u + 1) + ω ^ 2 < eN u := by
  have hE := eN_E u
  have hu : u < eN u := lt_eN u
  have h1 : (1 : Ordinal.{0}) < eN u := one_lt_omega0.trans_le (Vo.vo_omega_le hE (InE.pos hE))
  have h2 : (2 : Ordinal.{0}) < eN u := (natCast_lt_omega0 2).trans_le (Vo.vo_omega_le hE (InE.pos hE))
  have hc : ω ^ (u + 1) < eN u := hE.opow_lt (hE.add_lt hu h1)
  exact hE.add_lt (hE.opow_lt hc) (Vo.vo_e2 ▸ hE.opow_lt h2)

/-- **A low window**: `ν − a < ω^{c+1}` with `ω² | ν − a` gives `β = (ν − a) + ω² ≤ ω^{c+1}`. -/
theorem wqLow_beta {u d : Ordinal.{0}} (hd : ω ^ 2 ∣ d) (hdl : d < ω ^ (ω ^ (u + 1) + 1)) :
    ω ^ 2 ∣ d + ω ^ 2 ∧ d + ω ^ 2 ≤ ω ^ (ω ^ (u + 1) + 1) := by
  have hωc : ω ≤ ω ^ (u + 1) := left_le_opow ω (lt_of_le_of_lt zero_le (lt_add_one u))
  have h2 : (2 : Ordinal.{0}) ≤ ω ^ (u + 1) + 1 :=
    ((natCast_lt_omega0 2).le.trans hωc).trans le_self_add
  have hdv : ω ^ 2 ∣ ω ^ (ω ^ (u + 1) + 1) := Vo.vo_e2 ▸ opow_dvd_opow ω h2
  exact ⟨dvd_add hd dvd_rfl, Vr.vr_dvd_step hd hdv hdl⟩

/-- **Supply restarts below `L(k)`**: for every `γ < L(k)` a Range restart `μ` with code `G₂+1`,
`γ < υ_μ < L(k)`, `υ_μ < L(ω)` and `Wc.WcRead0 S μ` (`Ls.lsNames_M`, `Ls.lsNames_L`, `Wk.wkRead0`). -/
theorem wqMu_ex (k : ℕ) : ∀ γ < Nc.ncL S (k : Ordinal.{0}), ∃ μ, CdRange S μ ∧ γ < upsilon μ ∧
    upsilon μ < Nc.ncL S (k : Ordinal.{0}) ∧ cdCode S μ = Ls.lsG S (0 + 1 + 1) + 1 ∧
    upsilon μ < Nc.ncL S ω ∧ Wc.WcRead0 S μ := by
  intro γ hγ
  have key : ∃ μ, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < Nc.ncL S (k : Ordinal.{0}) ∧
      cdCode S μ = Ls.lsG S (0 + 1 + 1) + 1 := by
    rcases k with _ | n
    · have hγ' : γ < Nc.ncL S 0 := by simpa using hγ
      obtain ⟨μ, hR, h1, h2, hc⟩ := Ls.lsNames_M (S := S) 1 γ hγ'
      exact ⟨μ, hR, h1, by simpa using h2, hc⟩
    · exact Ls.lsNames_L (S := S) n 1 γ hγ
  obtain ⟨μ, hR, h1, h2, hc⟩ := key
  have hω : upsilon μ < Nc.ncL S ω := h2.trans (Qq.qqL_lt_omega S k)
  exact ⟨μ, hR, h1, h2, hc, hω, Wk.wkRead0 hR hc hω⟩

/-- **The witness context exists** (given `L(k+1) ≤ ν_C`): at `a = L(k)` and `ν₀ = a + g + ω²`, `ν₀` is a Range
restart, `υ(a + W(a)) ≤ υ_{ν₀} < L(k+1)`, `υ_a < υ_{ν₀}`, `ν₀` is not covered from `υ_a` and is isolated from
below.  (The same facts as inside `Vo.voWit`, with `ν₀` explicit.) -/
theorem wqWitCtx (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) :
    IsRestartIdx (Nc.ncL S (k : Ordinal.{0})) ∧
    Nc.ncL S (k : Ordinal.{0}) = upsilon (Nc.ncL S (k : Ordinal.{0})) ∧
    CdRange S (Nc.ncL S (k : Ordinal.{0}) + ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) + ω ^ 2) ∧
    upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0}))) ≤
      upsilon (Nc.ncL S (k : Ordinal.{0}) + ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) + ω ^ 2) ∧
    upsilon (Nc.ncL S (k : Ordinal.{0}) + ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) + ω ^ 2) <
      Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ∧
    upsilon (Nc.ncL S (k : Ordinal.{0})) <
      upsilon (Nc.ncL S (k : Ordinal.{0}) + ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) + ω ^ 2) ∧
    ¬ Tk.TkCov S (upsilon (Nc.ncL S (k : Ordinal.{0})))
      (Nc.ncL S (k : Ordinal.{0}) + ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) + ω ^ 2) ∧
    Tk.TkIso S (upsilon (Nc.ncL S (k : Ordinal.{0})))
      (Nc.ncL S (k : Ordinal.{0}) + ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) + ω ^ 2) := by
  have hm := upsilon_normal.strictMono
  obtain ⟨hl0, -, hu2E, hu12, hu2L1, hL1E, hL1O, hbelow, hωL1⟩ := Vr.vr_facts (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  set L1 := Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) with hL1def
  have hlfix : upsilon l = l := Te.teUps_L k
  have hlR : IsRestartIdx l := Te.teRst_L k
  have hlL1 : l < L1 := Te.teL_lt_succ k
  have hlE : InE l := hlfix ▸ upsPt_inE (upsPt_upsilon hl0)
  have hnatL1 : ∀ n : ℕ, (n : Ordinal.{0}) < L1 := fun n => (natCast_lt_omega0 n).trans hωL1
  have hC : ∀ x, x < L1 → upsilon (x + ω + 1) < nuC := fun x hx =>
    (hbelow _ (hL1E.add_lt (hL1E.add_lt hx hωL1) (by exact_mod_cast hnatL1 1))).trans_le hν
  set u1 := upsilon (l + 1) with hu1
  have hlu1 : l < u1 := hlfix ▸ hm (lt_add_one l)
  set c := ω ^ (u1 + 1) with hc
  set g := ω ^ c with hg
  have hu1P : 0 < u1 := lt_of_le_of_lt zero_le hlu1
  have hcu2 : c < upsilon (l + 2) :=
    hu2E.opow_lt (hu2E.add_lt hu12 ((Order.one_le_iff_pos.2 hu1P).trans_lt hu12))
  have hgu2 : g < upsilon (l + 2) := hu2E.opow_lt hcu2
  have hωc : ω ≤ c := left_le_opow ω (lt_of_le_of_lt zero_le (lt_add_one u1))
  have h2c : (2 : Ordinal.{0}) ≤ c := ((natCast_lt_omega0 2).trans_le hωc).le
  have hω2g : ω ^ 2 ∣ g := Vo.vo_e2 ▸ opow_dvd_opow ω h2c
  have hω2le : ω ^ 2 ≤ g := Vo.vo_e2 ▸ opow_le_opow_right omega0_pos h2c
  have hcg : c ≤ g := right_le_opow c one_lt_omega0
  have hu1c : u1 ≤ c := (lt_add_one u1).le.trans (right_le_opow _ one_lt_omega0)
  have hu1g : u1 ≤ g := hu1c.trans hcg
  have hgL1 : g < L1 := hgu2.trans hu2L1
  set lam := l + g with hlam
  set ν := l + g + ω ^ 2 with hνdef
  have hνa : ν = l + (g + ω ^ 2) := add_assoc _ _ _
  have hlamL1 : lam < L1 := hL1E.add_lt hlL1 hgL1
  have hω2L1 : ω ^ 2 < L1 := hω2le.trans_lt hgL1
  have hνL1 : ν < L1 := hL1E.add_lt hlamL1 hω2L1
  have hlamν : lam < ν := lt_add_of_pos_right lam ((Vo.vo_e2 ▸ opow_pos (2 : Ordinal.{0}) omega0_pos))
  have hllam : l < lam := lt_add_of_pos_right l (opow_pos c omega0_pos)
  have hlamR : IsRestartIdx lam := ⟨(hl0.trans hllam).ne', dvd_add hlR.2 hω2g⟩
  have hνR : IsRestartIdx ν := ⟨(hl0.trans (hllam.trans hlamν)).ne', dvd_add hlamR.2 dvd_rfl⟩
  have hCR : CdRange S ν := by
    have h1 := hm (hllam.trans hlamν); rw [hlfix] at h1
    exact Tk.tkL_rng k ν hνR h1 (hbelow ν hνL1)
  have hcw : upsilon (l + Te.teW l) ≤ upsilon ν := by
    refine hm.monotone ?_
    have hW : Te.teW l ≤ u1 :=
      Te.teW_le hlE (hlL1.trans hL1O) hlu1 (upsPt_upsilon (hl0.trans_le le_self_add))
    calc l + Te.teW l ≤ l + g := (add_le_add_iff_left l).2 (hW.trans hu1g)
      _ ≤ ν := le_self_add
  have hlν : upsilon l < upsilon ν := hm (hllam.trans hlamν)
  have hcov : ¬ Tk.TkCov S (upsilon l) ν := by
    rintro ⟨R, hR, h1, h2, h3⟩
    have hlR' : l < R := hm.lt_iff_lt.1 h1
    have hRν : R < ν := hm.lt_iff_lt.1 h2
    obtain ⟨z, rfl⟩ := exists_add_of_le hlR'.le
    have hz0 : z ≠ 0 := by rintro rfl; rw [add_zero] at hlR'; exact lt_irrefl _ hlR'
    have hdz : ω ^ 2 ∣ z := (Ordinal.dvd_add_iff hlR.2).1 hR.1.2
    have hzg : z ≤ g := by
      by_contra hgz
      push Not at hgz
      obtain ⟨d, rfl⟩ := exists_add_of_le hgz.le
      have hd0 : d ≠ 0 := by rintro rfl; rw [add_zero] at hgz; exact lt_irrefl _ hgz
      have hdd : ω ^ 2 ∣ d := (Ordinal.dvd_add_iff hω2g).1 hdz
      have := le_of_dvd hd0 hdd
      rw [hνa] at hRν
      exact absurd ((add_lt_add_iff_left l).1 hRν) (not_lt.2 ((add_le_add_iff_left g).2 this))
    have hzu : z < upsilon (l + 2) := hzg.trans_lt hgu2
    have hlt := wqBigTop (S := S) k hν (pos_iff_ne_zero.2 hz0) hdz hzu
    have hle : upsilon (l + (z + ω ^ 2)) ≤ upsilon ν := by
      refine hm.monotone ?_
      rw [hνa]
      exact (add_le_add_iff_left l).2 (add_le_add_left hzg _)
    exact absurd (h3.trans (hlt.trans_le hle)) (lt_irrefl _)
  have hiso : Tk.TkIso S (upsilon l) ν := by
    refine ⟨upsilon lam, hm.monotone hllam.le, hm hlamν, fun ν' hν' h1 h2 => ?_⟩
    exfalso
    have hl1 : lam < ν' := hm.lt_iff_lt.1 h1
    have hl2 : ν' < ν := hm.lt_iff_lt.1 h2
    obtain ⟨d, rfl⟩ := exists_add_of_le hl1.le
    have hd0 : d ≠ 0 := by rintro rfl; rw [add_zero] at hl1; exact lt_irrefl _ hl1
    have hdd : ω ^ 2 ∣ d := (Ordinal.dvd_add_iff hlamR.2).1 hν'.1.2
    exact absurd ((add_lt_add_iff_left lam).1 hl2) (not_lt.2 (le_of_dvd hd0 hdd))
  exact ⟨hlR, hlfix.symm, hCR, hcw, hbelow ν hνL1, hlν, hcov, hiso⟩

end Googology.Trans.PoR.InaccPsi.R2.Wq
