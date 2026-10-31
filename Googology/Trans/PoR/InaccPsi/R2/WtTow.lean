import Googology.Trans.PoR.InaccPsi.R2.WtLv3

/-!
# WtTow: THE `ω`-SEQUENCE OF (A3) LEVELS BELOW `t₀ = ε_{G+1}` (the data of the limit step at `t₀`)

`t₀ = ε_{G+1}` has cofinality `ω`: the towers `G^G`, `G^{G^G}`, … (`Go.GoD.hTw` of `Go.goGl`) are (A3) levels with
gate `0` (`Wn.wnLv3T0` has gate `0` too).  This module proves, with no hypothesis, the level and reading data that
the limit step at `t₀` asks of an `ω`-sequence (the fields of `Wm.WmSeq` that do not mention packages):

* `wtTw n = G^{⋯^G}` (`n + 2` letters `G`), `wtTw_G`, `wtTw_dvd`, `wtTw_lt`, `wtTw_g` (gate `0`),
  `wtTw_step` (`wtTw n + Ω₁ ≤ wtTw (n+1)`), `wtTw_cof` (**cofinal in `t₀`**);
* `wtTw_R` (**reading `Γ_{x+1}^{(G^{⋯})(x)}`**), `wtTw_rstep` (**`ℓ_n(x) + x < ℓ_{n+1}(x)`**), `wtTw_rlt` (**below the
  reading `ε_{Γ_{x+1}+1}` of `t₀`**), `wtTw_rcof` (**cofinal in it**);
* `wtTwLv n` (the (A3) level datum of `wtTw n`, `Wt.wtLv3`), `wtTowSeq` (**THE `ω`-SEQUENCE OF (A3) LEVEL DATA BELOW
  `Wn.wnLv3T0`**: gates `0 ≤` the gate of `t₀`, levels `+Ω₁`-increasing and cofinal, readings `+x`-increasing,
  below and cofinal in the reading of `t₀` at every `ε`-number `x < Ω₁`).

No new axiom.  New definitions: `wtTw`, `wtTwLv`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wt

open Googology.Trans.PoR.InaccPsi.R2.Ho
open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gf
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd
open Googology.Trans.PoR.InaccPsi.R2.Wh Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Wn

/-- The towers `G^{⋯^G}` (`n + 2` letters). -/
noncomputable def wtTw (n : ℕ) : Ordinal.{0} := goGl.hTw (n + 1)

theorem wtTw_succ (n : ℕ) : wtTw (n + 1) = gcG 0 ^ wtTw n := rfl

theorem wt_hTw_ge (n : ℕ) : gcG 0 ≤ goGl.hTw n := goGl.hTw_ge n

theorem wtTw_G (n : ℕ) : gcG 0 < wtTw n := (wt_hTw_ge n).trans_lt (goGl.hTw_strict n)

theorem wtTw_lt (n : ℕ) : wtTw n < Wj.wjT 0 := by rw [← wtD_B]; exact goGl.hTw_lt (n + 1)

theorem wtTw_g (n : ℕ) : wtD.g (wtTw n) = 0 := goGl.hTw_g (n + 1)

/-- `Ω₁ ∣ ω^e` for `Ω₁ ≤ e`. -/
theorem wt_dvd_opow {e : Ordinal.{0}} (he : Om1 ≤ e) : Om1 ∣ ω ^ e := by
  refine ⟨ω ^ (e - Om1), ?_⟩
  conv_lhs => rw [← Ordinal.add_sub_cancel_of_le he]
  rw [opow_add, rj_Om1_opow]

theorem wtTw_dvd (n : ℕ) : Om1 ∣ wtTw n := by
  show Om1 ∣ gcG 0 ^ goGl.hTw n
  have hG : ω ^ gcG 0 = gcG 0 := gl_G0_E
  rw [← hG, ← opow_mul]
  refine wt_dvd_opow (gl_Om1_lt_G0.le.trans ?_)
  exact Ordinal.le_mul_left _ ((gcG_SC 0).1.trans_le (wt_hTw_ge n))

/-- Two multiples `a < b` of `Ω₁` have `a + Ω₁ ≤ b`. -/
theorem wt_dvd_step {a b : Ordinal.{0}} (ha : Om1 ∣ a) (hb : Om1 ∣ b) (h : a < b) : a + Om1 ≤ b := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  have hij : i < j := lt_of_mul_lt_mul_left' h
  rw [← mul_add_one]
  exact mul_le_mul_left' (Order.add_one_le_of_lt hij) _

theorem wtTw_strict (n : ℕ) : wtTw n < wtTw (n + 1) := goGl.hTw_strict (n + 1)

theorem wtTw_step (n : ℕ) : wtTw n + Om1 ≤ wtTw (n + 1) :=
  wt_dvd_step (wtTw_dvd n) (wtTw_dvd (n + 1)) (wtTw_strict n)

theorem wtTw_mono {m n : ℕ} (h : m ≤ n) : wtTw m ≤ wtTw n := by
  induction n with
  | zero => rw [Nat.le_zero.1 h]
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with hm | hm
    · exact (ih (Nat.lt_succ_iff.1 hm)).trans (wtTw_strict n).le
    · rw [le_antisymm h hm]

/-- **The towers are cofinal in `t₀`.** -/
theorem wtTw_cof {y : Ordinal.{0}} (hy : y < Wj.wjT 0) : ∃ n : ℕ, y < wtTw n := by
  rw [← wtD_B] at hy
  obtain ⟨n, hn⟩ := goGl.hTw_cof hy
  exact ⟨n, hn.trans (goGl.hTw_strict n)⟩

/-- **The reading of a tower**: `Γ_{x+1}^{(G^{⋯})(x)}`. -/
theorem wtTw_R (n : ℕ) (x : Ordinal.{0}) : wtD.R (wtTw n) x = lgG x ^ wtD.R (goGl.hTw n) x := by
  have h0 : goGl.hTw n ≠ 0 := ((gcG_SC 0).1.trans_le (wt_hTw_ge n)).ne'
  exact goGl.hR_pow h0 (goGl.hTw_lt n) x

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem wtTw_Rpos (n : ℕ) : 0 < wtD.R (goGl.hTw n) x := by
  have h0 : goGl.hTw n ≠ 0 := ((gcG_SC 0).1.trans_le (wt_hTw_ge n)).ne'
  exact wtD.R_pos x hx hx1 _ h0 (goGl.hTw_lt n) (by rw [show wtD.g (goGl.hTw n) = 0 from goGl.hTw_g n]; exact hx.pos)

/-- **`ℓ_n(x) + x < ℓ_{n+1}(x)`** (the next reading is additively principal). -/
theorem wtTw_rstep (n : ℕ) : wtD.R (wtTw n) x + x < wtD.R (wtTw (n + 1)) x := by
  have hg : ∀ m, wtD.g (wtTw m) < x := fun m => by rw [wtTw_g]; exact hx.pos
  have hlt : wtD.R (wtTw n) x < wtD.R (wtTw (n + 1)) x :=
    wtD.mono x hx hx1 _ (wt_LB (wtTw_lt (n + 1))) _ (wtTw_strict n) (hg _) (hg _)
  have hxl : x < wtD.R (wtTw (n + 1)) x :=
    (lgG_facts hx hx1).2.1.trans (wt_R_gtG (wtTw_G _) (wtTw_lt _) hx hx1 (hg _))
  have hP : Principal (· + ·) (wtD.R (wtTw (n + 1)) x) := by
    rw [wtTw_R, show lgG x = ω ^ lgG x from (lgG_facts hx hx1).2.2.2.1.symm, ← opow_mul]
    exact principal_add_omega0_opow _
  exact hP hlt hxl

/-- **The readings lie below the reading `ε_{Γ_{x+1}+1}` of `t₀`.** -/
theorem wtTw_rlt (n : ℕ) : wtD.R (wtTw n) x < wnLv3T0.l x := by
  rw [wnLv3T0_l hx hx1]
  exact goGl.hR_lt_eNb hx hx1 (wt_LB (wtTw_lt n)) (by rw [show goGl.hG (wtTw n) = 0 from wtTw_g n]; exact hx.pos)

/-- **The readings are cofinal in the reading `ε_{Γ_{x+1}+1}` of `t₀`.** -/
theorem wtTw_rcof {ν : Ordinal.{0}} (hν : ν < wnLv3T0.l x) : ∃ n : ℕ, ν < wtD.R (wtTw n) x := by
  rw [wnLv3T0_l hx hx1] at hν
  obtain ⟨c, hc, hgc, hνc⟩ := goGl.NB_cof hx hx1 hν
  obtain ⟨n, hn⟩ := goGl.hTw_cof hc
  refine ⟨n, hνc.trans ?_⟩
  exact wtD.mono x hx hx1 _ (wt_LB (wtTw_lt n)) c (hn.trans (goGl.hTw_strict n)) (by rw [wtTw_g]; exact hx.pos) hgc

end Base

/-- The (A3) level datum of the tower `wtTw n` (gate `0`). -/
noncomputable def wtTwLv (n : ℕ) : WnLv3 := wtLv3 (wtTw n) (wtTw_G n) (wtTw_dvd n) (wtTw_lt n)

theorem wtTwLv_g (n : ℕ) : (wtTwLv n).g = 0 := wtTw_g n

theorem wtTwLv_l (n : ℕ) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : (wtTwLv n).l x = wtD.R (wtTw n) x :=
  wtLv3_l _ _ _ hx hx1 (by rw [wtTw_g]; exact hx.pos)

/-- **THE `ω`-SEQUENCE OF (A3) LEVEL DATA BELOW `t₀`** (`Wn.wnLv3T0`): gates `0`, levels `+Ω₁`-increasing, below
`t₀` and cofinal in it; readings `+x`-increasing, below the reading of `t₀` and cofinal in it, at every
`ε`-number `x < Ω₁`. -/
theorem wtTowSeq :
    (∀ n, (wtTwLv n).g ≤ wnLv3T0.g) ∧
    (∀ n, (wtTwLv n).L + Om1 ≤ (wtTwLv (n + 1)).L ∧ (wtTwLv n).L + Om1 ≤ wnLv3T0.L) ∧
    (∀ y, y < wnLv3T0.L → ∃ n, y < (wtTwLv n).L) ∧
    (∀ x, InE x → x < Om1 → ∀ n,
      (wtTwLv n).l x + x ≤ (wtTwLv (n + 1)).l x ∧ (wtTwLv n).l x + x ≤ wnLv3T0.l x) ∧
    (∀ x, InE x → x < Om1 → ∀ ν, ν < wnLv3T0.l x → ∃ n, ν < (wtTwLv n).l x) := by
  refine ⟨fun n => by rw [wtTwLv_g, wnLv3T0_g], fun n => ⟨wtTw_step n, (wtTw_step n).trans (wtTw_lt _).le⟩,
    fun y hy => wtTw_cof hy, fun x hx hx1 n => ?_, fun x hx hx1 ν hν => ?_⟩
  · rw [wtTwLv_l n hx hx1, wtTwLv_l (n + 1) hx hx1]
    exact ⟨(wtTw_rstep hx hx1 n).le, ((wtTw_rstep hx hx1 n).trans (wtTw_rlt hx hx1 (n + 1))).le⟩
  · obtain ⟨n, hn⟩ := wtTw_rcof hx hx1 hν
    exact ⟨n, by rw [wtTwLv_l n hx hx1]; exact hn⟩

end Googology.Trans.PoR.InaccPsi.R2.Wt
