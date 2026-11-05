import Googology.Trans.PoR.InaccPsi.R2.ZlAsm
import Googology.Trans.PoR.InaccPsi.R2.PhFr

/-!
# The supply clause at the windows of `L(k)`: `skSupKXo` from the reduced clause `ZlCfg`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

The context of the skeleton leaf `skSupKXo` (`υ_λ = L(k)`, `ν` a Range restart of the window with `υ_λ < υ_ν <
L(k+1)`, `β = ν − λ + ω²`) gives every side condition of `Zl.zlSup_of` and `Zl.zlCfg_of_sup` once `L(ω+1) ≤ ν_C`:
`υ_λ = λ`, `υ_λ < Ω₁`, `ω² ∣ β`, `υ_{λ+β} = υ_{ν+ω²} < L(k+1) ≤ L(ω+1) ≤ ν_C`, `υ_{rzLam} < L(k)`, `ω² < β`.

* `zlCtx_facts` (the side conditions);
* `zlSup_ctx` (**`ZlCfg ⇒ Xo.XoSup` at every window context**, given `L(ω+1) ≤ ν_C` and LOWER at the Range `RzRest`
  restarts — both shared nodes of the skeleton: `skNu`, `skLowRR`);
* `zlCfg_ctx` (**`Xo.XoSup ⇒ ZlCfg`** there), `zlCtx_iff`.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zl

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **The side conditions at a window context.** -/
theorem zlCtx_facts (k : ℕ) {l ν : Ordinal.{0}} (hl : IsRestartIdx l)
    (he : Nc.ncL S (k : Ordinal.{0}) = upsilon l) (hνR : CdRange S ν)
    (hνL : upsilon ν < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (hlν : upsilon l < upsilon ν)
    (hNu : Nc.ncL S (ω + 1) ≤ nuC) :
    upsilon l = l ∧ upsilon l < Om 1 ∧ ω ^ 2 ∣ ν - l + ω ^ 2 ∧ upsilon (l + (ν - l + ω ^ 2)) ≤ nuC ∧
      upsilon (l + (ν - l + ω ^ 2)) ≤ Nc.ncL S (ω + 1) ∧ upsilon Rz.rzLam < upsilon l ∧ ω ^ 2 < ν - l + ω ^ 2 := by
  have hm := upsilon_normal.strictMono
  obtain ⟨-, -, -, -, -, hL1E, -, hbelow, hωL1⟩ := Vr.vr_facts (S := S) k
  have hfixL : upsilon (Nc.ncL S (k : Ordinal.{0})) = Nc.ncL S (k : Ordinal.{0}) := Te.teUps_L k
  have hlk : l = Nc.ncL S (k : Ordinal.{0}) := hm.injective (by rw [hfixL, he])
  have hfl : upsilon l = l := by rw [hlk, hfixL]
  have hl1 : upsilon l < Om 1 := by rw [← he, Lw.lw_L_eq]; exact Nm.Pv_lt_Om1 S _
  have hlν' : l < ν := hm.lt_iff_lt.1 hlν
  have hsub : l + (ν - l) = ν := Ordinal.add_sub_cancel_of_le hlν'.le
  have hd : ω ^ 2 ∣ ν - l := (Ordinal.dvd_add_iff hl.2).1 (by rw [hsub]; exact hνR.1.2)
  have he2 : l + (ν - l + ω ^ 2) = ν + ω ^ 2 := by rw [← add_assoc, hsub]
  have hfix1 := Te.teUps_L (S := S) (k + 1)
  have hνL1 : ν < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) := by
    have := hνL; rw [← hfix1] at this; exact hm.lt_iff_lt.1 this
  have hw2 : ω ^ 2 < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) := by
    rw [Vo.vo_e2]; exact hL1E.opow_lt ((natCast_lt_omega0 2).trans hωL1)
  have hlt : upsilon (ν + ω ^ 2) < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) := hbelow _ (hL1E.add_lt hνL1 hw2)
  have hLL : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ Nc.ncL S (ω + 1) := by
    rw [Lw.lw_L_eq, Lw.lw_L_eq]
    refine Nm.Pv_mono (add_le_add_right (mul_le_mul_left' ?_ _) _)
    have : ((k + 1 : ℕ) : Ordinal.{0}) ≤ ω := (natCast_lt_omega0 _).le
    exact this.trans le_self_add
  have hRz : upsilon Rz.rzLam < upsilon l := by
    rw [← he]
    rcases k with _ | n
    · exact (Ph.phFr_order (S := S) 0).1.1
    · exact (Ph.phFr_order (S := S) n).2.1.1
  have h2 : (0 : Ordinal.{0}) < ω ^ 2 := by rw [Vo.vo_e2]; exact opow_pos _ omega0_pos
  have hνl0 : 0 < ν - l := by
    rcases eq_or_lt_of_le (zero_le : (0 : Ordinal.{0}) ≤ ν - l) with h | h
    · rw [← h, add_zero] at hsub; exact absurd hsub hlν'.ne
    · exact h
  have hw2le : ω ^ 2 ≤ ν - l := le_of_dvd hνl0.ne' hd
  have hβ2 : ω ^ 2 < ν - l + ω ^ 2 :=
    (lt_add_of_pos_right (ω ^ 2) h2).trans_le (add_le_add_left hw2le _)
  refine ⟨hfl, hl1, dvd_add hd dvd_rfl, ?_, ?_, hRz, hβ2⟩
  · rw [he2]; exact (hlt.trans_le hLL).le.trans hNu
  · rw [he2]; exact (hlt.trans_le hLL).le

/-- **`ZlCfg ⇒ Xo.XoSup` at every window context** (given `L(ω+1) ≤ ν_C` and LOWER at the Range `RzRest`
restarts). -/
theorem zlSup_ctx (k : ℕ) {l ν : Ordinal.{0}} (hl : IsRestartIdx l)
    (he : Nc.ncL S (k : Ordinal.{0}) = upsilon l) (hνR : CdRange S ν)
    (hνL : upsilon ν < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (hlν : upsilon l < upsilon ν)
    (hNu : Nc.ncL S (ω + 1) ≤ nuC) (hLow : ∀ lam, CdRange S lam → Rz.RzRest lam → CdLower S lam)
    (hcfg : ZlCfg S l (ν - l + ω ^ 2)) : Xo.XoSup S l (ν - l + ω ^ 2) := by
  obtain ⟨hfl, hl1, hβd, hβν, hβL, hRz, -⟩ := zlCtx_facts k hl he hνR hνL hlν hNu
  exact zlSup_of hl hfl hl1 hβd hβν hβL hLow hRz hcfg

/-- **`Xo.XoSup ⇒ ZlCfg` at every window context.** -/
theorem zlCfg_ctx (k : ℕ) {l ν : Ordinal.{0}} (hl : IsRestartIdx l)
    (he : Nc.ncL S (k : Ordinal.{0}) = upsilon l) (hνR : CdRange S ν)
    (hνL : upsilon ν < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (hlν : upsilon l < upsilon ν)
    (hNu : Nc.ncL S (ω + 1) ≤ nuC) (hsup : Xo.XoSup S l (ν - l + ω ^ 2)) : ZlCfg S l (ν - l + ω ^ 2) := by
  obtain ⟨hfl, hl1, hβd, hβν, hβL, -, hβ2⟩ := zlCtx_facts k hl he hνR hνL hlν hNu
  exact zlCfg_of_sup hl hfl hβν hβL hβ2 hsup

theorem zlCtx_iff (k : ℕ) {l ν : Ordinal.{0}} (hl : IsRestartIdx l)
    (he : Nc.ncL S (k : Ordinal.{0}) = upsilon l) (hνR : CdRange S ν)
    (hνL : upsilon ν < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (hlν : upsilon l < upsilon ν)
    (hNu : Nc.ncL S (ω + 1) ≤ nuC) (hLow : ∀ lam, CdRange S lam → Rz.RzRest lam → CdLower S lam) :
    ZlCfg S l (ν - l + ω ^ 2) ↔ Xo.XoSup S l (ν - l + ω ^ 2) :=
  ⟨zlSup_ctx k hl he hνR hνL hlν hNu hLow, zlCfg_ctx k hl he hνR hνL hlν hNu⟩

end Googology.Trans.PoR.InaccPsi.R2.Zl
