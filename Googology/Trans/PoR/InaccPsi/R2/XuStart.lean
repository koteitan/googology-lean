import Googology.Trans.PoR.InaccPsi.R2.XuRec
import Googology.Trans.PoR.InaccPsi.R2.XpT0

/-!
# XuStart: THE PSEUDO-BASE `φ(t_n, G)` AND ITS START FOR EVERY `n`; `Wn.WnEnt3 S n` FOR EVERY `n`

With the bound `T = t_{n+1}` (`Xu.xuT_t`), the level `t_n` is an ordinary band level (`xu_tn_lv`), so the band
recursion `Xu.xuqSys` gives a system at its bottom `φ(t_n, 0)` (`xuSV_at`).  The bottom recursion `Xl.xlU` of the level
`t_n` (step `Xp.xpSt` of the package of `t_n`, bottom base `Xu.xuqBK` with the low field `N_{t_{n+1}(x)}(0)`) reaches the
offset `G`: the stage `φ(t_n, G)` starts the pseudo-base `φ(t_n, G)` (gate `1`), as `Xp.xpQG_start` at `n = 0`.

* `xu_tn_lv`, `xuSB`, `xuSV`, `xuSV_at`, `xuS_start0`, `xuVT` (**the stage at the offset `l` of the level `t_n`**),
  `xuVT_B`, `xuVT_gG`, `xuQB` (**THE PSEUDO-BASE `φ(t_n, G)`**), `xuQB_F`, `xuQB_γ`, `xuQB_start`;
* `xuQStart` (**the leaf `skA3QStart`**: for every `n`, the pseudo-base `φ(t_n, G)` over the datum of `Xu.xuPk3 n`,
  gate `1 < K`, and a system starting it);
* `xuEnt3` (**`Wn.WnEnt3 S n` FOR EVERY `n`, UNCONDITIONAL**), `xuEnt3_step` (**`skSysA3StepW`**).

No new axiom.  New definitions: `xuSB`, `xuSV`, `xuVT`, `xuQB`.
-/

set_option autoImplicit false

open Googology.Trans.PoR.InaccPsi.R2.Wm Googology.Trans.PoR.InaccPsi.R2.Wh Googology.Trans.PoR.InaccPsi.R2.Ho
open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
open Googology.Trans.PoR.InaccPsi.R2.Wo Googology.Trans.PoR.InaccPsi.R2.Wn Googology.Trans.PoR.InaccPsi.R2.Wp
open Googology.Trans.PoR.InaccPsi.R2.Xc
open Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt
open Googology.Trans.PoR.InaccPsi.R2.Xf
open Googology.Trans.PoR.InaccPsi.R2.Ho
open Googology.Trans.PoR.InaccPsi.R2.Xl
open Googology.Trans.PoR.InaccPsi.R2.Xp
open Googology.Trans.PoR.InaccPsi.R2.Xp
open Googology.Trans.PoR.InaccPsi.R2.Xl Googology.Trans.PoR.InaccPsi.R2.Wy
open Googology.Trans.PoR.InaccPsi.R2.Gv

namespace Googology.Trans.PoR.InaccPsi.R2.Xu

section N

variable (n : ℕ)

/-- **`t_n` is a band level below `t_{n+1}`.** -/
theorem xu_tn_lv : XuqLv (Wj.wjT (n + 1)) (Wj.wjT n) :=
  ⟨(Wj.wjT_spec n).1, wp_Om1_dvd_E (Wj.wjT_spec n).2.2.1 (xu_Om1_lt_t0.trans_le (Wj.wjT_mono (Nat.zero_le n))),
    xu_t_lt n⟩

/-- **The band datum of `t_n`** (the package of the family below `t_{n+1}`). -/
noncomputable def xuSB : XpBd0 := (xuqBdOf (xuT_t (n + 1)) (Wj.wjT n) (xu_tn_lv n)).toXpBd0

/-- **The system at the bottom `φ(t_n, 0)`** (the band recursion below `t_{n+1}`). -/
noncomputable def xuSV : HgVD := xuqSys (xuT_t (n + 1)) (Wj.wjT n)

theorem xuSV_at : XuqAt (Wj.wjT (n + 1)) (xuSB n).K.Λ 0 (xuSV n) := xuqSys_at (xuT_t (n + 1)) (xu_tn_lv n)

theorem xuS_start0 : XlStart (xuqBK (xuT_t (n + 1)) (xuSB n) 0 gv_Om1_pos) (xuSV n) :=
  xuq_start_of_at (xuT_t (n + 1)) (xuSB n) gv_Om1_pos (xuSV_at n)

/-- **THE STAGE AT THE OFFSET `l` OF THE LEVEL `t_n`** (the bottom recursion `Xl.xlU` over `xuSV n`). -/
noncomputable def xuVT (l : Ordinal.{0}) : HgVD :=
  xlU (xpSt (xuSB n) 0) (xuqBK (xuT_t (n + 1)) (xuSB n) 0 gv_Om1_pos) (xuSV n) l

theorem xuSB_L : (xuSB n).K.Λ.L = Wj.wjT n := rfl

theorem xuSB_g : (xuSB n).K.Λ.g = 1 := xuGg_t n

theorem xu_G_lt_N : gcG 0 < hcN ((xuSB n).K.Λ.L + 0) 0 := by
  rw [add_zero, xl_N_eq]
  exact (Wj.wjT_spec n).1.trans_le ((le_add_right le_rfl).trans (left_le_veblen _ 0))

/-- **THE STAGE AT THE OFFSET `l < N_{t_n}(0)` IS A SYSTEM AT `φ(t_n, l)`.** -/
theorem xuVT_B {l : Ordinal.{0}} (hl : l < hcN ((xuSB n).K.Λ.L + 0) 0) : (xuVT n l).B = veblen (Wj.wjT n) l := by
  have h := xlU_B (xpSt_spec (xuSB n) gv_Om1_pos) (xuS_start0 n) hl
  rw [xuqBK_e, zero_add, add_zero] at h; exact h

theorem xuVT_gG : (xuVT n (gcG 0)).g (gcG 0) = 0 :=
  (xuVT n (gcG 0)).g_G0 (by rw [xuVT_B n (xu_G_lt_N n)]; exact (xf_G_veb0.symm.trans_lt
    ((veblen_zero_lt_veblen_zero.2 (Wj.wjT_spec n).1).trans_le ((isNormal_veblen _).monotone zero_le))))

/-- **THE PSEUDO-BASE `φ(t_n, G)` OF THE RECURSION** (gate `1`). -/
noncomputable def xuQB : HnVQ (xuSB n).K.Λ 0 :=
  xlOff (xuqBK (xuT_t (n + 1)) (xuSB n) 0 gv_Om1_pos) (xuVT n (gcG 0)) (gcG 0)
    (xlU_self (xpSt_spec (xuSB n) gv_Om1_pos) (xuS_start0 n) (xu_G_lt_N n)) (xu_G_lt_N n)
    (xlU_Zb (xpSt_spec (xuSB n) gv_Om1_pos) (xuS_start0 n) (xu_G_lt_N n))

theorem xuQB_F : (xuQB n).F = veblen (Wj.wjT n) (gcG 0) := by
  show veblen (Wj.wjT n + 0) ((((xuqBK (xuT_t (n + 1)) (xuSB n) 0 gv_Om1_pos).e : ℕ) : Ordinal.{0}) + gcG 0) = _
  rw [xuqBK_e, zero_add, add_zero]

theorem xuQB_γ : (xuQB n).γ = 1 := by
  show max (max 0 (xuSB n).K.Λ.g) ((xuVT n (gcG 0)).g (gcG 0)) = 1
  rw [xuVT_gG, xuSB_g, max_eq_right zero_le, max_eq_left zero_le]

/-- **THE STAGE `φ(t_n, G)` STARTS THE PSEUDO-BASE `φ(t_n, G)`.** -/
theorem xuQB_start : HgSStart (hnVPB (xuQB n)) (xuVT n (gcG 0)) :=
  xlU_start (xpSt_spec (xuSB n) gv_Om1_pos) (xuS_start0 n) (xu_G_lt_N n)

end N

/-- **THE LEAF `skA3QStart`**: for every `n`, the pseudo-base `φ(t_n, G)` over the datum of `Xu.xuPk3 n` (gate `1`)
and a system starting it. -/
theorem xuQStart (S : InaccSeq.{0}) (n : ℕ) : ∃ (Q : WnQ3 (xuPk3 n).Λ 0) (U : HgVD)
    (_ : HgSStart (hgdPB Q.toP) U), Q.F = veblen (Wj.wjT n) (gcG 0) ∧ Q.γ < Td.tdK S :=
  ⟨wyQ3 (xuQB n), xuVT n (gcG 0), xuQB_start n, xuQB_F n,
    by rw [wyQ3_γ, xuQB_γ]; exact xc_one_lt_SC Td.tdK_SC⟩

/-- **`Wn.WnEnt3 S n` FOR EVERY `n`, UNCONDITIONAL**: the package `Xu.xuPk3 n` at `t_n` and the pseudo-base
`φ(t_n, G)` started by `xuVT n G`. -/
theorem xuEnt3 (S : InaccSeq.{0}) (n : ℕ) : WnEnt3 S n := by
  obtain ⟨Q, U, hU, hF, hγ⟩ := xuQStart S n
  exact ⟨xuPk3 n, rfl, by rw [xuPk3_g]; exact xc_one_lt_SC Td.tdK_SC, Q, U, hU, hF, hγ⟩

/-- **THE LADDER STEP `skSysA3StepW`** (proved without its hypothesis). -/
theorem xuEnt3_step (S : InaccSeq.{0}) : ∀ n, WnEnt3 S n → WnEnt3 S (n + 1) := fun n _ => xuEnt3 S (n + 1)

end Googology.Trans.PoR.InaccPsi.R2.Xu
