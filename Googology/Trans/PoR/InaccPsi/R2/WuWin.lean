import Googology.Trans.PoR.InaccPsi.R2.WqWit
import Googology.Trans.PoR.InaccPsi.R2.WfCarry
import Googology.Trans.PoR.InaccPsi.R2.EpsE
import Googology.Trans.PoR.InaccPsi.R2.WuAtom

/-!
# The high windows exist, and the forms clause there ends in a `ϑ^{u₁}`-atom below `B₂` or an `sg`-node

`a = L(k) = υ_a` (index `a`), `u₁ = υ_{a+1}`, `u₂ = υ_{a+2}`, `X` an `ε`-number with `u₁ < X < u₂`, `ν_X = a + X + ω²`.

The code of the inner restart `a + X` is `m = cdOff(cdExp X) = X` (`Vo.voCode_add`), so `r(a+X) = υ_{a+(X+ω+1)} + X`
(`Vr.vrR_inner`): the reach ENDS in `X`.  `ν_X` is an uncovered, isolated Range restart of the window of `L(k)`
(as `Wq.wqWitCtx`; every inner reach of the low region stays below `υ_{a+(z+ω²)}`, `Wq.wqBigTop`).  So
`Wf.WfVisGen` at `L(k)` asks the forms clause at the offset `X`, where the big reach is impossible, so a repaired
form `Vr.VrForm` of a value ending in `X` is needed, and `Wu.wuLast` says what it must end with.

* `wuWin` (**the window `ν_X` exists, for every `ε`-number `X ∈ (u₁, u₂)`**), `wuWin_high` (`X = ε_{u₁+1}` gives a
  window with `ν − a ≥ ε_{u₁+1}`, not the witness window: the hypotheses of `skFormHigh` / `skCarryHigh` are
  satisfiable);
* `wuR_X` (**`r(a+X) = υ_{a+(X+ω+1)} + X`**);
* `wuForm_X` (**a repaired form at the offset `X` ends in an `sg`-node with parameters below `υ_a`, or in
  `X = ϑ^{u₁}(ξ)` with `ξ ∈ T^{u₁}`, `ξ < B₂`**);
* `WuGap S k` (statement: some `ε`-number `X ∈ (u₁, u₂)` is no `ϑ^{u₁}(ξ)` with `ξ ∈ T^{u₁}`, `ξ < B₂`, and every
  segment point ending in `X` has a Wilken parameter `≥ υ_a`), `wuVis_ref` (**`WuGap S k ∧ L(k+1) ≤ ν_C ⇒ ¬
  Wf.WfVisGen` at `L(k)`**: the supply hypotheses `h0'` / `hn'` of `Wf.wfRoad` fail), `wuRoad_vac`.

No new axiom.  New definition: `WuGap` (a statement).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wu

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **The window at an `ε`-offset**: for every `ε`-number `X ∈ (u₁, u₂)`, `ν = a + X + ω²` is a Range restart in the
window `[υ_{a+W(a)}, L(k+1))`, uncovered from `a`, isolated from below (given `L(k+1) ≤ ν_C`). -/
theorem wuWin (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {X : Ordinal.{0}} (hXE : InE X)
    (hX1 : upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) < X) (hX2 : X < upsilon (Nc.ncL S (k : Ordinal.{0}) + 2)) :
    IsRestartIdx (Nc.ncL S (k : Ordinal.{0})) ∧
    Nc.ncL S (k : Ordinal.{0}) = upsilon (Nc.ncL S (k : Ordinal.{0})) ∧
    CdRange S (Nc.ncL S (k : Ordinal.{0}) + X + ω ^ 2) ∧
    upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0}))) ≤
      upsilon (Nc.ncL S (k : Ordinal.{0}) + X + ω ^ 2) ∧
    upsilon (Nc.ncL S (k : Ordinal.{0}) + X + ω ^ 2) < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ∧
    upsilon (Nc.ncL S (k : Ordinal.{0})) < upsilon (Nc.ncL S (k : Ordinal.{0}) + X + ω ^ 2) ∧
    ¬ Tk.TkCov S (upsilon (Nc.ncL S (k : Ordinal.{0}))) (Nc.ncL S (k : Ordinal.{0}) + X + ω ^ 2) ∧
    Tk.TkIso S (upsilon (Nc.ncL S (k : Ordinal.{0}))) (Nc.ncL S (k : Ordinal.{0}) + X + ω ^ 2) := by
  have hm := upsilon_normal.strictMono
  obtain ⟨hl0, -, hu2E, -, hu2L1, hL1E, hL1O, hbelow, -⟩ := Vr.vr_facts (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  set L1 := Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) with hL1def
  have hlfix : upsilon l = l := Te.teUps_L k
  have hlR : IsRestartIdx l := Te.teRst_L k
  have hlL1 : l < L1 := Te.teL_lt_succ k
  have hlE : InE l := hlfix ▸ upsPt_inE (upsPt_upsilon hl0)
  set u1 := upsilon (l + 1) with hu1
  have hlu1 : l < u1 := hlfix ▸ hm (lt_add_one l)
  set g := X with hg
  have hgu2 : g < upsilon (l + 2) := hX2
  have hωX : ω ≤ X := Vo.vo_omega_le hXE (InE.pos hXE)
  have h2c : (2 : Ordinal.{0}) ≤ X := ((natCast_lt_omega0 2).trans_le hωX).le
  have hω2g : ω ^ 2 ∣ g := by
    have h := Vo.vo_e2 ▸ opow_dvd_opow ω h2c
    rwa [hXE] at h
  have hω2le : ω ^ 2 ≤ g := le_of_dvd (InE.pos hXE).ne' hω2g
  have hu1g : u1 ≤ g := hX1.le
  have hgL1 : g < L1 := hgu2.trans hu2L1
  set lam := l + g with hlam
  set ν := l + g + ω ^ 2 with hνdef
  have hνa : ν = l + (g + ω ^ 2) := add_assoc _ _ _
  have hlamL1 : lam < L1 := hL1E.add_lt hlL1 hgL1
  have hω2L1 : ω ^ 2 < L1 := hω2le.trans_lt hgL1
  have hνL1 : ν < L1 := hL1E.add_lt hlamL1 hω2L1
  have hlamν : lam < ν := lt_add_of_pos_right lam ((Vo.vo_e2 ▸ opow_pos (2 : Ordinal.{0}) omega0_pos))
  have hllam : l < lam := lt_add_of_pos_right l (InE.pos hXE)
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
    have hlt := Wq.wqBigTop (S := S) k hν (pos_iff_ne_zero.2 hz0) hdz hzu
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

/-- **The reach at an `ε`-offset ends in the offset**: `r(a+X) = υ_{a+(X+ω+1)} + X`. -/
theorem wuR_X (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {X : Ordinal.{0}} (hXE : InE X)
    (hX2 : X < upsilon (Nc.ncL S (k : Ordinal.{0}) + 2)) :
    cdR S (Nc.ncL S (k : Ordinal.{0}) + X) = upsilon (Nc.ncL S (k : Ordinal.{0}) + (X + ω + 1)) + X := by
  have hωX : ω ≤ X := Vo.vo_omega_le hXE (InE.pos hXE)
  have h2c : (2 : Ordinal.{0}) ≤ X := ((natCast_lt_omega0 2).trans_le hωX).le
  have hω2g : ω ^ 2 ∣ X := by
    have h := Vo.vo_e2 ▸ opow_dvd_opow ω h2c
    rwa [hXE] at h
  rw [Vr.vrR_inner k hν (InE.pos hXE) hω2g hX2, Vo.voCode_add k hωX hX2, Te.te_cdExp_E hXE]
  unfold cdOff; rw [if_neg (not_lt.2 hωX)]

/-- **A repaired form at an `ε`-offset `X ∈ (u₁, u₂)`** ends in an `sg`-node (all parameters below `υ_a`) or in
`X = ϑ^{u₁}(ξ)`, `ξ ∈ T^{u₁}`, `ξ < B₂`. -/
theorem wuForm_X (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {X β : Ordinal.{0}} (hXE : InE X)
    (hX1 : upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) < X) (hX2 : X < upsilon (Nc.ncL S (k : Ordinal.{0}) + 2))
    (hb1 : upsilon (Nc.ncL S (k : Ordinal.{0}) + β) ≤ Om1) (hF : Vr.VrForm S (Nc.ncL S (k : Ordinal.{0})) β X) :
    (∃ h y, 0 < h ∧ h < β ∧ upsilon (Nc.ncL S (k : Ordinal.{0}) + h) ≤ y ∧
        y < upsilon (succ (Nc.ncL S (k : Ordinal.{0}) + h)) ∧
        (∀ p ∈ Par (upsilon (Nc.ncL S (k : Ordinal.{0}) + h)) y, p < upsilon (Nc.ncL S (k : Ordinal.{0}))) ∧
        y ≠ 0 ∧ cdExp y = X) ∨
      ∃ ξ, ξ ∈ Tset (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) ∧ ξ < Uc.ucB ∧
        vt (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) ξ = X := by
  obtain ⟨hl0, -, -, -, -, -, -, -, -⟩ := Vr.vr_facts (S := S) k
  obtain ⟨E, hW, hv⟩ := hF
  have hX0 : X ≠ 0 := (InE.pos hXE).ne'
  rw [wuR_X k hν hXE hX2] at hv
  have hv0 : Vr.vrVal (Nc.ncL S (k : Ordinal.{0})) E ≠ 0 := by
    rw [hv]; exact (lt_of_lt_of_le (InE.pos hXE) le_add_self).ne'
  have he : cdExp (Vr.vrVal (Nc.ncL S (k : Ordinal.{0})) E) = X := by rw [hv, Cp.cpExp_add _ hX0, Te.te_cdExp_E hXE]
  exact wuLast hl0 hb1 hXE hX1 hX2 E hW hv0 he

/-- **The gap statement at `L(k)`**: an `ε`-number `X ∈ (u₁, u₂)` that is no `ϑ^{u₁}(ξ)` with `ξ ∈ T^{u₁}`, `ξ < B₂`,
and such that every point of an inner segment ending in `X` has a Wilken parameter `≥ υ_a`. -/
def WuGap (S : InaccSeq.{0}) (k : ℕ) : Prop :=
  ∃ X, InE X ∧ upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) < X ∧ X < upsilon (Nc.ncL S (k : Ordinal.{0}) + 2) ∧
    (∀ ξ, ξ ∈ Tset (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) → ξ < Uc.ucB →
      vt (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) ξ ≠ X) ∧
    ∀ h y, 0 < h → upsilon (Nc.ncL S (k : Ordinal.{0}) + h) ≤ y →
      y < upsilon (succ (Nc.ncL S (k : Ordinal.{0}) + h)) → y ≠ 0 → cdExp y = X →
      ∃ p ∈ Par (upsilon (Nc.ncL S (k : Ordinal.{0}) + h)) y, upsilon (Nc.ncL S (k : Ordinal.{0})) ≤ p

/-- **CONDITIONAL REFUTATION of the supply hypothesis at `L(k)`**: if `WuGap S k` and `L(k+1) ≤ ν_C`, then
`Wf.WfVisGen` fails at `L(k)` (at the window `ν_X`, every admissible `β` asks the forms clause at the offset `X`;
the big reach is impossible, `Wq.wqBigTop`, and a repaired form is excluded by `wuForm_X`). -/
theorem wuVis_ref (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) (hG : WuGap S k) :
    ¬ Wf.WfVisGen S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0})))) := by
  intro hV
  have hm := upsilon_normal.strictMono
  obtain ⟨X, hXE, hX1, hX2, hvt, hsg⟩ := hG
  obtain ⟨-, e, hR, hc, hb, hlν, hcov, hiso⟩ := wuWin k hν hXE hX1 hX2
  obtain ⟨-, -, -, -, -, -, hL1O, -, -⟩ := Vr.vr_facts (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  have hlu : upsilon l = l := e.symm
  obtain ⟨β, e1, e2, hGen⟩ := hV (l + X + ω ^ 2) hR hc hb hlν hcov hiso
  have hνβ : l + X + ω ^ 2 < l + β := hm.lt_iff_lt.1 e1
  have hXβ' : X + ω ^ 2 < β := by rw [add_assoc] at hνβ; exact (add_lt_add_iff_left l).1 hνβ
  have hXβ : X < β := (le_self_add).trans_lt hXβ'
  have hωX : ω ≤ X := Vo.vo_omega_le hXE (InE.pos hXE)
  have h2c : (2 : Ordinal.{0}) ≤ X := ((natCast_lt_omega0 2).trans_le hωX).le
  have hω2g : ω ^ 2 ∣ X := by
    have h := Vo.vo_e2 ▸ opow_dvd_opow ω h2c
    rwa [hXE] at h
  have hb1 : upsilon (l + β) ≤ Om1 := e2.trans hL1O.le
  rcases hGen.2.1 X (InE.pos hXE) hXβ hω2g with hbig | hF
  · have hlt := Wq.wqBigTop (S := S) k hν (InE.pos hXE) hω2g hX2
    have hle : upsilon (l + (X + ω ^ 2)) ≤ upsilon (l + β) := hm.monotone ((add_le_add_iff_left l).2 hXβ'.le)
    exact absurd (hbig.trans_lt (hlt.trans_le hle)) (lt_irrefl _)
  · rcases wuForm_X k hν hXE hX1 hX2 hb1 hF with ⟨h, y, h0, -, h1, h2, h3, h4, h5⟩ | ⟨ξ, hξ, hξB, hξe⟩
    · obtain ⟨p, hp, hpl⟩ := hsg h y h0 h1 h2 h4 h5
      exact absurd (h3 p hp) (not_lt.2 hpl)
    · exact hvt ξ hξ hξB hξe

/-- **The road `Wf.wfRoad` is vacuous under `WuGap S 0`**: its supply hypothesis `h0'` and its own conclusion
`L(1) ≤ ν_C` cannot both hold. -/
theorem wuRoad_vac (hG : WuGap S 0) :
    ¬ ((∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
        Wf.WfVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0)))) ∧
      Nc.ncL S 1 ≤ nuC) := by
  rintro ⟨h0, hν⟩
  have hν' : Nc.ncL S ((0 + 1 : ℕ) : Ordinal.{0}) ≤ nuC := by simpa using hν
  apply wuVis_ref 0 hν' hG
  have e : Nc.ncL S ((0 : ℕ) : Ordinal.{0}) = upsilon (Nc.ncL S ((0 : ℕ) : Ordinal.{0})) := (Te.teUps_L 0).symm
  have h := h0 (Nc.ncL S ((0 : ℕ) : Ordinal.{0})) (Te.teRst_L 0) (by simpa using e)
  simpa using h

/-- **High windows exist** (non-vacuity of `skFormHigh` / `skCarryHigh`, with `wuWin` at `X = ε_{u₁+1}`): `X = ε_{u₁+1}`
lies in `(u₁, u₂)` and gives a window `ν_X` with
`ν − a = X + ω² ≥ ε_{u₁+1}`, and `ν_X` is not the witness window `a + g + ω²` (`g = ω^{ω^{u₁+1}} < ε_{u₁+1}`). -/
theorem wuWin_high (k : ℕ) :
    eN (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) < upsilon (Nc.ncL S (k : Ordinal.{0}) + 2) ∧
    ¬ (Nc.ncL S (k : Ordinal.{0}) + eN (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) + ω ^ 2 -
        Nc.ncL S (k : Ordinal.{0}) < eN (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1))) ∧
    Nc.ncL S (k : Ordinal.{0}) + eN (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) + ω ^ 2 ≠
      Nc.ncL S (k : Ordinal.{0}) + ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) + ω ^ 2 := by
  obtain ⟨hl0, -, -, hu12, hu2L1, -, hL1O, -, -⟩ := Vr.vr_facts (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  set u1 := upsilon (l + 1) with hu1def
  have hu1P : UpsPt u1 := upsPt_upsilon (hl0.trans_le le_self_add)
  have hu2P : UpsPt (upsilon (l + 2)) := upsPt_upsilon (hl0.trans_le le_self_add)
  have hu1O : u1 < Om1 := hu12.trans (hu2L1.trans hL1O)
  have h1 := (eN_lt_upsPt hu1P hu1O).2.2 _ hu12 hu2P
  refine ⟨h1, ?_, ?_⟩
  · rw [add_assoc, Ordinal.add_sub_cancel]; exact not_lt.2 le_self_add
  · intro h
    rw [add_assoc, add_assoc] at h
    have h' := (add_left_cancel_iff).1 h
    have hE := eN_E u1
    have hu : u1 < eN u1 := lt_of_lt_of_le (lt_add_one u1) (le_nfp _ _)
    have hlt : ω ^ ω ^ (u1 + 1) < eN u1 := hE.opow_lt (hE.opow_lt (hE.add_lt hu (So.soOne_lt_E hE)))
    have hω2 : ω ^ 2 < eN u1 := by
      rw [Vo.vo_e2]; exact hE.opow_lt ((natCast_lt_omega0 2).trans_le (Vo.vo_omega_le hE (InE.pos hE)))
    have h3 : ω ^ ω ^ (u1 + 1) + ω ^ 2 < eN u1 + ω ^ 2 := (hE.add_lt hlt hω2).trans_le le_self_add
    exact absurd h' h3.ne'

/-- **Under `WuGap S k` the forms clause fails at a high window**: there is an `ε`-number `X ∈ (u₁, u₂)`,
`X ≥ ε_{u₁+1}`, `X ≠ g = ω^{ω^{u₁+1}}`, whose window `ν_X = a + X + ω²` exists (`wuWin`) and at which the forms clause
of `β(ν_X) = (ν_X − a) + ω²` fails at the offset `X` (no big reach, no repaired form). -/
theorem wuFormHigh_fail (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) (hG : WuGap S k) :
    ∃ X, InE X ∧ upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) < X ∧ X < upsilon (Nc.ncL S (k : Ordinal.{0}) + 2) ∧
      eN (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) ≤ X ∧
      X ≠ ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) ∧
      ¬ (upsilon (Nc.ncL S (k : Ordinal.{0}) + (Nc.ncL S (k : Ordinal.{0}) + X + ω ^ 2 - Nc.ncL S (k : Ordinal.{0}) +
          ω ^ 2)) ≤ cdR S (Nc.ncL S (k : Ordinal.{0}) + X) ∨
        Vr.VrForm S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S (k : Ordinal.{0}) + X + ω ^ 2 -
          Nc.ncL S (k : Ordinal.{0}) + ω ^ 2) X) := by
  have hm := upsilon_normal.strictMono
  obtain ⟨X, hXE, hX1, hX2, hvt, hsg⟩ := hG
  obtain ⟨hl0, -, -, -, hu2L1, hL1E, hL1O, hbelow, hωL1⟩ := Vr.vr_facts (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  set u1 := upsilon (l + 1) with hu1def
  have e : l + X + ω ^ 2 - l + ω ^ 2 = X + ω ^ 2 + ω ^ 2 := by rw [add_assoc l, Ordinal.add_sub_cancel]
  have hωX : ω ≤ X := Vo.vo_omega_le hXE (InE.pos hXE)
  have h2c : (2 : Ordinal.{0}) ≤ X := ((natCast_lt_omega0 2).trans_le hωX).le
  have hω2g : ω ^ 2 ∣ X := by
    have h := Vo.vo_e2 ▸ opow_dvd_opow ω h2c
    rwa [hXE] at h
  have hω2X : ω ^ 2 < X := by rw [Vo.vo_e2]; exact hXE.opow_lt ((natCast_lt_omega0 2).trans_le hωX)
  have hβ1 : X + ω ^ 2 + ω ^ 2 < upsilon (l + 2) := by
    have hu2E : InE (upsilon (l + 2)) := upsPt_inE (upsPt_upsilon (hl0.trans_le le_self_add))
    exact hu2E.add_lt (hu2E.add_lt hX2 (hω2X.trans hX2)) (hω2X.trans hX2)
  have hlβ : l + (X + ω ^ 2 + ω ^ 2) < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) :=
    hL1E.add_lt (Te.teL_lt_succ k) (hβ1.trans hu2L1)
  have hb1 : upsilon (l + (X + ω ^ 2 + ω ^ 2)) ≤ Om1 := ((hbelow _ hlβ).trans hL1O).le
  have hXβ' : X + ω ^ 2 ≤ X + ω ^ 2 + ω ^ 2 := le_self_add
  refine ⟨X, hXE, hX1, hX2, eN_le hX1 hXE, ?_, ?_⟩
  · intro h
    have hinj : ∀ a b : Ordinal.{0}, ω ^ a = ω ^ b → a = b := fun a b hab =>
      le_antisymm ((opow_le_opow_iff_right one_lt_omega0).1 hab.le)
        ((opow_le_opow_iff_right one_lt_omega0).1 hab.ge)
    have h1 : ω ^ ω ^ ω ^ (u1 + 1) = ω ^ ω ^ (u1 + 1) := by
      have h' := hXE; rw [h] at h'; exact h'
    have h3 : ω ^ (u1 + 1) = u1 + 1 := hinj _ _ (hinj _ _ h1)
    have hL : IsSuccLimit (ω ^ (u1 + 1)) :=
      isSuccLimit_opow_left isSuccLimit_omega0 (lt_of_le_of_lt zero_le (lt_add_one u1)).ne'
    rw [h3] at hL
    have := hL.succ_lt (lt_add_one u1)
    rw [Order.succ_eq_add_one] at this
    exact lt_irrefl _ this
  · rw [e]
    rintro (hbig | hF)
    · have hlt := Wq.wqBigTop (S := S) k hν (InE.pos hXE) hω2g hX2
      have hle : upsilon (l + (X + ω ^ 2)) ≤ upsilon (l + (X + ω ^ 2 + ω ^ 2)) :=
        hm.monotone ((add_le_add_iff_left l).2 hXβ')
      exact absurd (hbig.trans_lt (hlt.trans_le hle)) (lt_irrefl _)
    · rcases wuForm_X k hν hXE hX1 hX2 hb1 hF with ⟨h, y, h0, -, h1, h2, h3, h4, h5⟩ | ⟨ξ, hξ, hξB, hξe⟩
      · obtain ⟨p, hp, hpl⟩ := hsg h y h0 h1 h2 h4 h5
        exact absurd (h3 p hp) (not_lt.2 hpl)
      · exact hvt ξ hξ hξB hξe

end Googology.Trans.PoR.InaccPsi.R2.Wu
