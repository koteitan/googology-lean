import Googology.Trans.PoR.InaccPsi.R2.WtCl

/-!
# WtLv3: THE (A3) LEVEL DATUM OF EVERY (A3) LEVEL BELOW `t₀ = ε_{G+1}`

`G = Γ_{Ω₁+1}`, `t₀ = Wj.wjT 0 = φ(1, G+1) = ε_{G+1}`.  The (A3) levels below `t₀` are the ordinals `L` with
`G < L < t₀`, `Ω₁ ∣ L` (`G + Ω₁`, `G·2`, `G^G`, …).  They are codes of the hereditary step `wtD = Go.goGl.step`
(codes `G^k·d + r < ε_{G+1}` over the digit system `Go.goGl` of the `Gl` codes below `G`, read with `Ω₁ ↦ x`,
`G ↦ Γ_{x+1}`; Lemma EXACT `Go.GoD.ex`, hull membership `Go.GoD.mem`, code gate `Go.GoD.code_gate`).

* `wtD`, `wtD_B` (**its bound is `t₀`**), `wtD_RG` (**`G` is read as `Γ_{x+1}`, gate `0`**);
* `wtLv3` (**THE (A3) LEVEL DATUM OF EVERY (A3) LEVEL `G < L < t₀`**: a `Wn.WnLv3` with `L = L`, gate `wtD.g L`,
  reading `wtD.R L x` above the gate; the code-gate field from `Wt.wt_cl_head` and `Go.GoD.code_gate`),
  `wtLv3DatumAll`, `wtLv3_GO` (**NON-VACUITY**: the level `G + Ω₁`);
* `wt_l_mono` (**the readings increase with the level** above both gates), `wt_l_lt_t0` (**every reading lies
  below the reading `ε_{Γ_{x+1}+1}` of `t₀`**, `Wn.wnLv3T0`);
* `wt_Q3_low` (**an (A3) pseudo-base of level `L` is a value of `φ(μ, ·)` for every `μ < L`, and the bound
  `hdNx μ F` of the level-`μ` step lies below the bound `hdNx L F` of the level-`L` step**: a step at an (A3)
  level contains the steps of all lower levels, (A1) and (A2) included).

No new axiom.  New definitions: `wtD`, `wtRd`, `wtLv3`.
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

/-- **The hereditary code system below `t₀`**: `Go.goGl.step` (codes `G^k·d + r < ε_{G+1}`). -/
noncomputable def wtD : GoD := goGl.step

theorem wt_G_fix1 : veblen 1 (gcG 0) = gcG 0 :=
  gn_veb_fix (gcG_SC 0) (one_lt_omega0.trans (omega0_lt_inE (Low.opow_eq_self_of_SC (gcG_SC 0))))

/-- **The bound of `wtD` is `t₀ = ε_{G+1}`.** -/
theorem wtD_B : wtD.B = Wj.wjT 0 := by
  show eN (gcG 0) = veblen 1 (gcG 0 + 1)
  conv_lhs => rw [← wt_G_fix1]
  exact go_eN_veb (gcG 0)

theorem wtD_G_lt : gcG 0 < wtD.B := by rw [wtD_B]; exact (Wj.wjT_spec 0).1

/-- **`G` is a code of `wtD` with gate `0`, read as `Γ_{x+1}`.** -/
theorem wtD_gG : wtD.g (gcG 0) = 0 := wtD.g_G0 wtD_G_lt

theorem wtD_RG (x : Ordinal.{0}) : wtD.R (gcG 0) x = lgG x := goGl.hR_G x

/-! ## The level datum -/

section Lev

variable {L : Ordinal.{0}} (hG : gcG 0 < L) (hO : Om1 ∣ L) (hL : L < Wj.wjT 0)

theorem wt_LB (hL : L < Wj.wjT 0) : L < wtD.B := by rw [wtD_B]; exact hL

include hG hL in
/-- Above the gate the reading of an (A3) level lies above `Γ_{x+1}`. -/
theorem wt_R_gtG {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : wtD.g L < x) : lgG x < wtD.R L x := by
  rw [← wtD_RG x]
  exact wtD.mono x hx hx1 L (wt_LB hL) (gcG 0) hG hg (by rw [wtD_gG]; exact hx.pos)

include hG hL in
theorem wt_le_R {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : wtD.g L < x) : x ≤ wtD.R L x :=
  ((lgG_facts hx hx1).2.1.trans (wt_R_gtG hG hL hx hx1 hg)).le

/-- The reading of the level datum: `wtD.R L x` (at least `x`) above the gate, `x` at or below it. -/
noncomputable def wtRd (L x : Ordinal.{0}) : Ordinal.{0} := if wtD.g L < x then max x (wtD.R L x) else x

include hG hL in
theorem wtRd_eq {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : wtD.g L < x) : wtRd L x = wtD.R L x := by
  unfold wtRd; rw [if_pos hg, max_eq_right (wt_le_R hG hL hx hx1 hg)]

end Lev

/-- **THE (A3) LEVEL DATUM OF EVERY (A3) LEVEL BELOW `t₀`**: `G < L < t₀`, `Ω₁ ∣ L`; `L = Ω₁·u + Ω₁·q` with
`u = Ω₁·(L / Ω₁²)`, `q = (L mod Ω₁²) / Ω₁`; gate `wtD.g L`; reading `wtD.R L x` above the gate. -/
noncomputable def wtLv3 (L : Ordinal.{0}) (hG : gcG 0 < L) (hO : Om1 ∣ L) (hL : L < Wj.wjT 0) : WnLv3 where
  L := L
  l := wtRd L
  u := Om1 * (L / (Om1 * Om1))
  q := (L % (Om1 * Om1)) / Om1
  g := wtD.g L
  g_lt := wtD.g_lt L (wt_LB hL)
  q_lt := (wh_L_dec hO).2
  G_lt := hG
  L_G1 := hL.trans (Wj.wjT_spec 0).2.1
  L_eq := by rw [← Br.Om1_eq]; exact (wh_L_dec hO).1
  g_cl := fun Z y hZ hZ1 hy hLy hy2 => by
    rw [← Br.Om1_eq] at hy2
    have hLe := (wh_L_dec hO).1
    have hLC : GxCl Z {gcG 0} L := by
      rw [hLe, ← mul_add]
      rw [hLe, ← mul_add] at hLy
      exact wt_cl_head hZ hy hLy hy2
    have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1
    exact wtD.code_gate Z hZ1' hZ.1 (fun u v hu hv => hZ.isPrincipal hu hv) (fun u v hu hv => hZ.2 u hu v hv)
      {gcG 0} (fun s hs => Or.inl hs) L hLC (wt_LB hL)
  L_mem := fun S a b ha hb => (wtD.mem S a b ha L (wt_LB hL) hb).1
  l_ge := fun x => by unfold wtRd; split_ifs; exacts [le_max_left _ _, le_rfl]
  l_gtG := fun x hx hx1 hg => by rw [wtRd_eq hG hL hx hx1 hg]; exact wt_R_gtG hG hL hx hx1 hg
  l_lt := fun x hx hx1 => by
    have hxq : x < gq 1 x := (lgG_facts hx hx1).2.1.trans (mg_lgG_lt_G1 hx hx1)
    unfold wtRd; split_ifs with hg
    · exact max_lt hxq (goGl.hR_lt1 hx hx1 (wt_LB hL) hg)
    · exact hxq
  l_pi := fun σ ρ hB hg => by
    rw [wtRd_eq hG hL hB.2.1 hB.2.2.2 (hg.trans hB.2.2.1), wtRd_eq hG hL hB.1 (hB.2.2.1.trans hB.2.2.2) hg]
    exact wtD.ex σ ρ hB L (wt_LB hL) hg

section Facts

variable {L : Ordinal.{0}} (hG : gcG 0 < L) (hO : Om1 ∣ L) (hL : L < Wj.wjT 0)

theorem wtLv3_L : (wtLv3 L hG hO hL).L = L := rfl

theorem wtLv3_g : (wtLv3 L hG hO hL).g = wtD.g L := rfl

theorem wtLv3_l {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : wtD.g L < x) :
    (wtLv3 L hG hO hL).l x = wtD.R L x := wtRd_eq hG hL hx hx1 hg

end Facts

/-- **EVERY (A3) LEVEL BELOW `t₀` HAS AN (A3) LEVEL DATUM** (`L = L`, gate `wtD.g L`, reading `wtD.R L x` above
it). -/
theorem wtLv3DatumAll : ∀ L, gcG 0 < L → Om1 ∣ L → L < Wj.wjT 0 → ∃ Λ : WnLv3, Λ.L = L ∧ Λ.g = wtD.g L ∧
    ∀ x, InE x → x < Om1 → Λ.g < x → Λ.l x = wtD.R L x := fun L hG hO hL =>
  ⟨wtLv3 L hG hO hL, rfl, rfl, fun _ hx hx1 hg => wtRd_eq hG hL hx hx1 hg⟩

/-! ## Non-vacuity, monotonicity, the bound `t₀` -/

theorem wt_Om1_dvd_G : Om1 ∣ gcG 0 := by
  refine ⟨gcG 0, ?_⟩
  have h := wn_Om1_mul_pow gl_G0_E gl_Om1_lt_G0 one_ne_zero
  rw [opow_one] at h
  exact h.symm

theorem wt_GO_lt : gcG 0 + Om1 < Wj.wjT 0 :=
  (inE_indec (Wj.wjT_spec 0).2.2.1).add_lt (Wj.wjT_spec 0).1 (gl_Om1_lt_G0.trans (Wj.wjT_spec 0).1)

/-- **NON-VACUITY**: the (A3) level datum of `G + Ω₁`. -/
noncomputable def wtLv3_GO : WnLv3 :=
  wtLv3 (gcG 0 + Om1) (lt_add_of_pos_right _ wh_Om1_pos) (dvd_add wt_Om1_dvd_G (dvd_refl _)) wt_GO_lt

/-- **The readings increase with the level** above both gates. -/
theorem wt_l_mono {L L' : Ordinal.{0}} (hG : gcG 0 < L) (hO : Om1 ∣ L) (hL' : L' < Wj.wjT 0) (hG' : gcG 0 < L')
    (hO' : Om1 ∣ L') (hLL : L < L') {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : wtD.g L < x)
    (hg' : wtD.g L' < x) :
    (wtLv3 L hG hO (hLL.trans hL')).l x < (wtLv3 L' hG' hO' hL').l x := by
  rw [wtLv3_l hG hO (hLL.trans hL') hx hx1 hg, wtLv3_l hG' hO' hL' hx hx1 hg']
  exact wtD.mono x hx hx1 L' (wt_LB hL') L hLL hg' hg

/-- **Every reading lies below the reading `ε_{Γ_{x+1}+1}` of `t₀`** (`Wn.wnLv3T0`). -/
theorem wt_l_lt_t0 {L : Ordinal.{0}} (hG : gcG 0 < L) (hO : Om1 ∣ L) (hL : L < Wj.wjT 0) {x : Ordinal.{0}}
    (hx : InE x) (hx1 : x < Om1) (hg : wtD.g L < x) : (wtLv3 L hG hO hL).l x < wnLv3T0.l x := by
  rw [wtLv3_l hG hO hL hx hx1 hg, wnLv3T0_l hx hx1]
  exact goGl.hR_lt_eNb hx hx1 (wt_LB hL) hg

/-! ## An (A3) step contains the steps of every lower level -/

/-- **An (A3) pseudo-base `F` of level `L` is a value of `φ(μ, ·)` for every `μ < L`, and `hdNx μ F < hdNx L F`**:
the system of a step at an (A3) level has, below its bound, the bounds of the steps of every lower level at `F`
((A1) levels `< ε_{Ω₁+1}`, (A2) levels `< G`, (A3) levels `< L`). -/
theorem wt_Q3_low {Λ : WnLv3} (Q : WnQ3 Λ 0) {μ : Ordinal.{0}} (hμ : μ < Λ.L) :
    veblen μ Q.F = Q.F ∧ hdNx μ Q.F < hdNx Λ.L Q.F := by
  obtain ⟨a, ha⟩ := Q.F_P
  rw [add_zero] at ha
  refine ⟨by rw [← ha]; exact veblen_veblen_of_lt hμ a, ?_⟩
  have hμ1 : μ + 1 < Λ.L := by
    obtain ⟨k, hk⟩ : Om1 ∣ Λ.L := ⟨Λ.u + Λ.q, by rw [Λ.L_eq, ← mul_add, ← Br.Om1_eq]⟩
    rw [hk] at hμ ⊢
    have hq : μ / Om1 < k := (Ordinal.div_lt wh_Om1_pos.ne').2 hμ
    have hl : IsSuccLimit (Om1 * (μ / Om1) + Om1) := Ordinal.isSuccLimit_add _ gl_Om1_lim
    calc μ + 1 < Om1 * (μ / Om1) + Om1 := hl.add_one_lt (lt_mul_div_add μ wh_Om1_pos.ne')
    _ = Om1 * (μ / Om1 + 1) := by rw [mul_add_one]
    _ ≤ Om1 * k := mul_le_mul_left' (Order.add_one_le_of_lt hq) _
  exact (hdNx_lt_N (hcN_gt _ _)).trans (hdN_lt_Nx hμ1)

end Googology.Trans.PoR.InaccPsi.R2.Wt
