import Googology.Trans.PoR.InaccPsi.R2.XuBr

/-!
# XuEnd: WHERE REGION (A3) ENDS, AND THE (A3) PACKAGE AT EVERY `t_n`

* `xu_A3_end` (**(A3) ENDS EXACTLY AT `Γ(1)`**: `G < t_n < Γ(1)` for every `n`, every `y < Γ(1)` lies below some `t_n`,
  and `Γ(1)` is the least strongly critical ordinal above `G`);
* `xu_t_lev` (**every `t_m`, `m < n`, is a level of `xuCn n`**), `xuGg_t` (**the gate of every `t_n` is `1`**);
* `xuLv3` (**THE (A3) LEVEL DATUM `Wn.WnLv3` OF EVERY LEVEL `G < ℓ < B` OF `xuC B`**; `Wy.wyLv (xuLv3 ℓ) = (xuC B).lv ℓ`);
* `xuPk` (the package of the family `Ws.wsF (xuCls)` at a level, an `Hn.HnPk`), `xuPk3` (**THE (A3) PACKAGE
  `Wn.WnPk3` AT EVERY `t_n`, LEVEL `t_n`, GATE `1`**, from the interface `xuCn (n+1)` and its classification).

No new axiom.  New definitions: `xuLv3`, `xuPk`, `xuPk3`.
-/

set_option autoImplicit false

open Googology.Trans.PoR.InaccPsi.R2.Wm Googology.Trans.PoR.InaccPsi.R2.Wh Googology.Trans.PoR.InaccPsi.R2.Ho
open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gf
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb
  Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gk
open Googology.Trans.PoR.InaccPsi.R2.Wo Googology.Trans.PoR.InaccPsi.R2.Wn Googology.Trans.PoR.InaccPsi.R2.Ws
  Googology.Trans.PoR.InaccPsi.R2.Wt Googology.Trans.PoR.InaccPsi.R2.Xc Googology.Trans.PoR.InaccPsi.R2.Wx
  Googology.Trans.PoR.InaccPsi.R2.Gv Googology.Trans.PoR.InaccPsi.R2.Wy Googology.Trans.PoR.InaccPsi.R2.Wp

namespace Googology.Trans.PoR.InaccPsi.R2.Xu

theorem xu_t_lt (n : ℕ) : Wj.wjT n < Wj.wjT (n + 1) := by
  show Wj.wjT n < veblen (Wj.wjT n) 0
  exact xu_veb_zero_gt (Wj.wjT_spec n).1 (Wj.wjT_spec n).2.1

theorem xu_t_strict {m n : ℕ} (h : m < n) : Wj.wjT m < Wj.wjT n := by
  induction n with
  | zero => exact absurd h (Nat.not_lt_zero m)
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | rfl
    · exact (ih h').trans (xu_t_lt n)
    · exact xu_t_lt m

/-- **(A3) ENDS EXACTLY AT `Γ(1)`**: `G < t_n < Γ(1)`, the `t_n` are cofinal in `Γ(1)`, and `Γ(1)` is the least
strongly critical ordinal above `G`. -/
theorem xu_A3_end : (∀ n, gcG 0 < Wj.wjT n ∧ Wj.wjT n < gcG 1) ∧ (∀ y, y < gcG 1 → ∃ n, y < Wj.wjT n) ∧
    ∀ b, SC b → gcG 0 < b → gcG 1 ≤ b := by
  refine ⟨fun n => ⟨(Wj.wjT_spec n).1, (Wj.wjT_spec n).2.1⟩, fun y hy => ?_, fun b hb hGb => xu_G1_le hb hGb⟩
  obtain ⟨n, hn⟩ := Wj.wjA3Cof hy
  refine ⟨n + 2, hn.trans ?_⟩
  have hG1 : gcG 0 + 1 < Wj.wjT (n + 2) :=
    (ev_isSuccLimit_of_inE (Wj.wjT_spec (n + 2)).2.2.1).add_one_lt (Wj.wjT_spec (n + 2)).1
  calc veblen (Wj.wjT n) (gcG 0 + 1) < veblen (Wj.wjT n) (Wj.wjT (n + 2)) := (veblen_lt_veblen_iff_right).2 hG1
    _ = Wj.wjT (n + 2) := by
      show veblen (Wj.wjT n) (veblen (Wj.wjT (n + 1)) 0) = veblen (Wj.wjT (n + 1)) 0
      exact veblen_veblen_of_lt (xu_t_lt n) 0

/-- **Every `t_m`, `m < n`, is a level of `xuCn n`.** -/
theorem xu_t_lev {m n : ℕ} (h : m < n) : (xuCn n).Lev (Wj.wjT m) :=
  ⟨(xu_Om1_lt_t0.trans_le (Wj.wjT_mono (Nat.zero_le m))).le,
    wp_Om1_dvd_E (Wj.wjT_spec m).2.2.1 (xu_Om1_lt_t0.trans_le (Wj.wjT_mono (Nat.zero_le m))), xu_t_strict h⟩

/-- `t_{n+1} = glPsi t_n 0`. -/
theorem xu_t_psi (n : ℕ) : Wj.wjT (n + 1) = glPsi (Wj.wjT n) 0 := by
  unfold glPsi
  rw [glLam_of_not (glFw_zero _), glY0_gt (xu_Om1_lt_t0.trans_le (Wj.wjT_mono (Nat.zero_le n))), add_zero]
  rfl

/-- **The gate of every `t_n` is `1`.** -/
theorem xuGg_t : ∀ n : ℕ, xuGg (Wj.wjT n) = 1
  | 0 => by unfold xuGg; rw [xuG_t0, max_eq_left zero_le]
  | n + 1 => by
    have hn1 : (1 : Ordinal.{0}) ≤ Wj.wjT n :=
      (xu_one_lt_inE (Wj.wjT_spec n).2.2.1).le
    have h := xu_gg_glPsi hn1 (Wj.wjT_spec n).2.1 xu_G1_E.pos
      (by rw [← xu_t_psi]; exact Wj.wjT_mono (Nat.zero_le _))
    rw [← xu_t_psi, xuQ_zero, xuQ_inf (omega0_lt_inE (Wj.wjT_spec n).2.2.1).le] at h
    rw [h]
    have := xuGg_t n
    unfold xuGg at this
    rw [max_eq_left zero_le, this]

section Lv

variable {B : Ordinal.{0}} (hBE : InE B) (hBt : Wj.wjT 0 ≤ B) (hB1 : B < gcG 1)

/-- **THE (A3) LEVEL DATUM OF EVERY LEVEL `G < ℓ < B`** of `xuC B`. -/
noncomputable def xuLv3 (ℓ : Ordinal.{0}) (hℓ : (xuC B hBE hBt hB1).Lev ℓ) (hG : gcG 0 < ℓ) : WnLv3 where
  L := ℓ
  l := ((xuC B hBE hBt hB1).lv ℓ hℓ).l
  u := ((xuC B hBE hBt hB1).lv ℓ hℓ).u
  q := ((xuC B hBE hBt hB1).lv ℓ hℓ).q
  g := ((xuC B hBE hBt hB1).lv ℓ hℓ).g
  g_lt := ((xuC B hBE hBt hB1).lv ℓ hℓ).g_lt
  q_lt := ((xuC B hBE hBt hB1).lv ℓ hℓ).q_lt
  G_lt := hG
  L_G1 := ((xuC B hBE hBt hB1).lv ℓ hℓ).L_G
  L_eq := ((xuC B hBE hBt hB1).lv ℓ hℓ).L_eq
  g_cl := ((xuC B hBE hBt hB1).lv ℓ hℓ).g_cl
  L_mem := ((xuC B hBE hBt hB1).lv ℓ hℓ).L_mem
  l_ge := ((xuC B hBE hBt hB1).lv ℓ hℓ).l_ge
  l_gtG := fun x hx hx1 hg => by
    show lgG x < (xuC B hBE hBt hB1).rd ℓ x
    rw [(xuC B hBE hBt hB1).rd_eq hx hx1 hℓ.1 hℓ.2.2 hg, ← xuR_G x]
    exact xuR_mono hx hx1 (hℓ.2.2.trans hB1) hG ((xuGg_lt_iff hx).1 hg) (by rw [xuG_G]; exact hx.pos)
  l_lt := ((xuC B hBE hBt hB1).lv ℓ hℓ).l_lt
  l_pi := ((xuC B hBE hBt hB1).lv ℓ hℓ).l_pi

theorem xuLv3_wy (ℓ : Ordinal.{0}) (hℓ : (xuC B hBE hBt hB1).Lev ℓ) (hG : gcG 0 < ℓ) :
    wyLv (xuLv3 hBE hBt hB1 ℓ hℓ hG) = (xuC B hBE hBt hB1).lv ℓ hℓ := rfl

/-- **The package of the family at a level `ℓ < B`.** -/
noncomputable def xuPk (ℓ : Ordinal.{0}) (hℓ : (xuC B hBE hBt hB1).Lev ℓ) : HnPk :=
  wsPkOf ℓ hℓ (wsF (xuCls hBE hBt hB1) ℓ) (wsFam (xuCls hBE hBt hB1) ℓ hℓ hℓ.2.2).1

theorem xuPk_Λ (ℓ : Ordinal.{0}) (hℓ : (xuC B hBE hBt hB1).Lev ℓ) :
    (xuPk hBE hBt hB1 ℓ hℓ).Λ = (xuC B hBE hBt hB1).lv ℓ hℓ := rfl

end Lv

/-- **THE (A3) PACKAGE AT `t_n`**: level `t_n`, gate `1`, from `xuCn (n+1)`. -/
noncomputable def xuPk3 (n : ℕ) : WnPk3 :=
  wyPk3 (xuLv3 _ _ _ (Wj.wjT n) (xu_t_lev (Nat.lt_succ_self n)) (Wj.wjT_spec n).1)
    (xuPk _ _ _ (Wj.wjT n) (xu_t_lev (Nat.lt_succ_self n))).St0
    (xuPk _ _ _ (Wj.wjT n) (xu_t_lev (Nat.lt_succ_self n))).h0

theorem xuPk3_L (n : ℕ) : (xuPk3 n).Λ.L = Wj.wjT n := rfl

theorem xuPk3_g (n : ℕ) : (xuPk3 n).Λ.g = 1 := xuGg_t n

/-- **THE (A3) PACKAGE AT EVERY `t_n` WITH GATE BELOW `K`** (the first half of `Wn.WnEnt3 S n`). -/
theorem xuPk3_ent (S : InaccSeq.{0}) (n : ℕ) :
    ∃ K : WnPk3, K.Λ.L = Wj.wjT n ∧ K.Λ.g < Td.tdK S :=
  ⟨xuPk3 n, rfl, by rw [xuPk3_g]; exact xc_one_lt_SC Td.tdK_SC⟩

end Googology.Trans.PoR.InaccPsi.R2.Xu
