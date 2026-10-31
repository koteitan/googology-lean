import Googology.Trans.PoR.InaccPsi.R2.XcTow

/-!
# XcQ: THE PSEUDO-BASE `φ(t₀, G)` OF LEVEL `t₀`, AND WHAT ITS START MUST BE

`a(x) = ε_{Γ_{x+1}+1}` is the reading of `t₀` (`Wn.wnLv3T0`).  The pseudo-base of level `t₀ + 0` at the point
`F = φ(t₀, G)` (gate `0`):

* `xcQ3` (**THE PSEUDO-BASE**: reading `Fr(x) = ϑˣ(Ω₁·a(x) + Γ_{x+1})`, low field `Zo(x) = hcN a(x) (Fr x)`; Lemma
  EXACT from `Gl.glA_pi`, the next value `ϑˣ(Ω₁·a + Γ_{x+1} + 1) = hdNx a (Fr x)` from `Hc.hc_glA_succV`),
  `xcQT0` (the same as a pseudo-base of the `Hn` stack);
* `xc_start_iff` (**THE START, EXPLICITLY**: a system `U` starts `xcQT0` iff `U.ix = φ(t₀, G)`, `U.γ` is below every
  `ε`-number, `U.b x = Fr x` and `U.Z x = ζ_{Fr x + 1}` at every `ε`-number `x < Ω₁`);
* `xcQT0_of_start` (**the skeleton leaf `skA3QT0` from a start of `xcQT0`**), `xcEnt3_of_start`.

No new axiom.  New definitions: `xcFr`, `xcZo`, `xcQ3`, `xcQT0`.
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
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gf
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd
open Googology.Trans.PoR.InaccPsi.R2.Wo Googology.Trans.PoR.InaccPsi.R2.Wn Googology.Trans.PoR.InaccPsi.R2.Wp
  Googology.Trans.PoR.InaccPsi.R2.Ws Googology.Trans.PoR.InaccPsi.R2.Wt Googology.Trans.PoR.InaccPsi.R2.Wy
  Googology.Trans.PoR.InaccPsi.R2.Wx
  Googology.Trans.PoR.InaccPsi.R2.Xc

namespace Googology.Trans.PoR.InaccPsi.R2.Xc

/-- The reading of `F = φ(t₀, G)`: `ϑˣ(Ω₁·ε_{Γ_{x+1}+1} + Γ_{x+1})`. -/
noncomputable def xcFr (x : Ordinal.{0}) : Ordinal.{0} := glA (wnLv3T0.l x) (lgG x) x

/-- The outer low field: the next fixed point of `φ(a(x), ·)` above `Fr x`. -/
noncomputable def xcZo (x : Ordinal.{0}) : Ordinal.{0} := hcN (wnLv3T0.l x) (xcFr x)

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem xc_a_facts : 1 ≤ wnLv3T0.l x ∧ wnLv3T0.l x ∈ Tset x ∧ wnLv3T0.l x < Om1 ∧ wnLv3T0.l x < gq 1 x :=
  ⟨(wo_one_lt_inE hx).le.trans (wnLv3T0.l_ge x), (gm1_T hx hx1 (wnLv3T0.l_lt x hx hx1)).1,
    (gm1_T hx hx1 (wnLv3T0.l_lt x hx hx1)).2, wnLv3T0.l_lt x hx hx1⟩

theorem xcFr_facts : xcFr x ∈ Tset x ∧ x < xcFr x ∧ xcFr x < Om1 ∧ InE (xcFr x) ∧ wnLv3T0.l x < xcFr x ∧
    lgG x < xcFr x := by
  obtain ⟨h1, h2, h3, -⟩ := xc_a_facts hx hx1
  obtain ⟨g1, -, g3, -⟩ := lgG_facts hx hx1
  exact glA_facts hx hx1 h1 h2 h3 g1 g3

theorem xcFr_P : LuP (wnLv3T0.l x) (xcFr x) := by
  obtain ⟨h1, h2, h3, -⟩ := xc_a_facts hx hx1
  obtain ⟨g1, -, g3, -⟩ := lgG_facts hx hx1
  exact glA_P hx hx1 h1 h2 h3 g1 g3

theorem xcFr_lt1 : xcFr x < gq 1 x :=
  hi_glA_lt1 hx hx1 (xc_a_facts hx hx1).2.2.2 (mg_lgG_lt_G1 hx hx1)

theorem xc_lgG1_lt : lgG x + 1 < gq 1 x :=
  (ev_isSuccLimit_of_inE (gm1_facts hx hx1).2.2.2).add_one_lt (mg_lgG_lt_G1 hx hx1)

/-- **The next value**: `ϑˣ(Ω₁·a + Γ_{x+1} + 1) = hdNx a (Fr x)`. -/
theorem xcFr_succ : glA (wnLv3T0.l x) (lgG x + 1) x = hdNx (wnLv3T0.l x) (xcFr x) := by
  obtain ⟨i, hi⟩ := xcFr_P hx hx1
  rw [hc_glA_succV hx hx1 (xc_a_facts hx hx1).1 (xc_a_facts hx hx1).2.2.2 (xc_lgG1_lt hx hx1) hi.symm,
    ← hdNx_veb, hi]

end Base

theorem xc_two_lt_a (x : Ordinal.{0}) : (2 : Ordinal.{0}) < wnLv3T0.l x := by
  have h2 : (2 : Ordinal.{0}) < ω := by exact_mod_cast natCast_lt_omega0 2
  exact (h2.trans (omega0_lt_inE (eN_E (lgG x)))).trans_le (le_max_right _ _)

theorem xcF_code {Z : Ordinal.{0}} (hZ : SC Z) : GxCl Z {gcG 0} (veblen (Wj.wjT 0) (gcG 0)) := by
  have h1 : (1 : Ordinal.{0}) < Z := xc_one_lt_SC hZ
  have hG : GxCl Z {gcG 0} (gcG 0) := GxCl.atom rfl
  have ht : GxCl Z {gcG 0} (Wj.wjT 0) := by
    show GxCl Z {gcG 0} (veblen 1 (gcG 0 + 1))
    exact GxCl.phi (GxCl.small h1) (GxCl.add hG (GxCl.small h1))
  exact GxCl.phi ht hG

theorem xcS0 : hdNx (wnLv3T0.L + 0) (veblen (Wj.wjT 0) (gcG 0)) = veblen (Wj.wjT 0) (gcG 0 + 1) := by
  show hdNx (Wj.wjT 0 + 0) (veblen (Wj.wjT 0) (gcG 0)) = _
  rw [add_zero, hdNx_veb]

/-- **THE PSEUDO-BASE `φ(t₀, G)` OF LEVEL `t₀`** (gate `0`). -/
noncomputable def xcQ3 : WnQ3 wnLv3T0 0 where
  F := veblen (Wj.wjT 0) (gcG 0)
  Fr := xcFr
  γ := 0
  Zo := xcZo
  lv := gv_Om1_pos
  γ_ge := le_rfl
  lg := le_rfl
  γ_lt := gv_Om1_pos
  F_P := (wnQ3_bounds 0).2.2
  G_lt := (wnQ3_bounds 0).1
  S_lt1 := (wnQ3_bounds 0).2.1
  F_mem := fun S a b ha hb => CSet.phi_mem (wnLv3T0.L_mem S a b ha hb) (gmS_G0_mem S ha)
  S_mem := fun S a b ha hb => by
    rw [xcS0]; exact CSet.phi_mem (wnLv3T0.L_mem S a b ha hb) (CSet.succ_mem (gmS_G0_mem S ha))
  F_code := fun Z hZ _ _ _ _ _ => xcF_code hZ
  F_cl := fun _ hZ _ _ _ _ _ => hZ.1
  S_cl := fun _ hZ _ _ => hZ.1
  Fr_gt := fun hx hx1 _ => by rw [add_zero]; exact (xcFr_facts hx hx1).2.2.2.2.1
  Fr_P := fun hx hx1 _ => by rw [add_zero]; exact xcFr_P hx hx1
  S_Zo := fun _ _ _ => by rw [add_zero]; exact hdNx_lt_N (hcN_gt _ _)
  Zo_fix := fun x => by
    show veblen 2 (hcN (wnLv3T0.l x) (xcFr x)) = hcN (wnLv3T0.l x) (xcFr x)
    calc veblen 2 (hcN (wnLv3T0.l x) (xcFr x))
        = veblen 2 (veblen (wnLv3T0.l x) (hcN (wnLv3T0.l x) (xcFr x))) := by rw [hcN_fix]
      _ = veblen (wnLv3T0.l x) (hcN (wnLv3T0.l x) (xcFr x)) := veblen_veblen_of_lt (xc_two_lt_a x) _
      _ = hcN (wnLv3T0.l x) (xcFr x) := hcN_fix _ _
  Zo_G1 := fun x hx hx1 => he_N_lt1 hx hx1
    ((ev_isSuccLimit_of_inE (gm1_facts hx hx1).2.2.2).add_one_lt (xc_a_facts hx hx1).2.2.2) (xcFr_lt1 hx hx1)
  Fr_pi := fun {σ ρ} hB _ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    obtain ⟨l1, l2⟩ := wnLv3T0.l_pi σ ρ hB hB.1.pos
    obtain ⟨b1, b2⟩ := goGl.b_pi σ ρ hB
    have h := glA_pi hB l1 (xc_a_facts hB.2.1 hρ1).2.2.1 b1 (lgG_facts hB.2.1 hρ1).2.2.1
    rw [l2, b2] at h
    exact h
  S_pi := fun {σ ρ} hB _ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    rw [add_zero, add_zero, ← xcFr_succ hB.2.1 hρ1, ← xcFr_succ hB.1 hσ1]
    obtain ⟨l1, l2⟩ := wnLv3T0.l_pi σ ρ hB hB.1.pos
    obtain ⟨b1, b2⟩ := goGl.b_pi σ ρ hB
    obtain ⟨o1, o2⟩ := one_TB hB
    obtain ⟨s1, s2⟩ := pi_add hB b1 o1
    have hs1 : lgG ρ + 1 < Om1 := gl_Om1_lim.add_one_lt (lgG_facts hB.2.1 hρ1).2.2.1
    have h := glA_pi hB l1 (xc_a_facts hB.2.1 hρ1).2.2.1 s1 hs1
    rw [l2, s2, b2, o2] at h
    exact h

theorem xcQ3_F : xcQ3.F = veblen (Wj.wjT 0) (gcG 0) := rfl

theorem xcQ3_γ : xcQ3.γ = 0 := rfl

/-- **The pseudo-base `φ(t₀, G)` as a pseudo-base of the `Hn` stack.** -/
noncomputable def xcQT0 : HnVQ (wyLv wnLv3T0) 0 := wyQ xcQ3

/-- **THE START, EXPLICITLY.** -/
theorem xc_start_iff (U : HgVD) : HgSStart (hnVPB xcQT0) U ↔
    U.ix = veblen (Wj.wjT 0) (gcG 0) ∧ (∀ x, InE x → x < Om1 → U.γ < x) ∧
      (∀ x, InE x → x < Om1 → U.b x = xcFr x) ∧ ∀ x, InE x → x < Om1 → U.Z x = evZ (xcFr x) := by
  constructor
  · intro h
    refine ⟨h.ix, fun x hx hx1 => (h.γ x hx hx1).2 hx.pos, fun x hx hx1 => h.b x hx hx1 hx.pos,
      fun x hx hx1 => ?_⟩
    rw [h.Z x hx hx1]
    show (if (0 : Ordinal.{0}) < x then evZ (xcFr x) else xcZo x) = _
    rw [if_pos hx.pos]
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, fun x hx hx1 => ⟨fun _ => hx.pos, fun _ => h2 x hx hx1⟩, fun x hx hx1 _ => h3 x hx hx1,
      fun x hx hx1 => ?_⟩
    rw [h4 x hx hx1]
    show _ = (if (0 : Ordinal.{0}) < x then evZ (xcFr x) else xcZo x)
    rw [if_pos hx.pos]

/-- **THE SKELETON LEAF `skA3QT0` FROM A START OF `xcQT0`.** -/
theorem xcQT0_of_start (S : InaccSeq.{0}) (U : HgVD) (hU : HgSStart (hnVPB xcQT0) U) :
    ∃ (Q : HnVQ (wyLv wnLv3T0) 0) (U : HgVD) (_ : HgSStart (hnVPB Q) U),
      Q.F = veblen (Wj.wjT 0) (gcG 0) ∧ Q.γ < Td.tdK S :=
  ⟨xcQT0, U, hU, rfl, (zero_lt_one.trans (xc_one_lt_SC Td.tdK_SC))⟩

/-- **`Wn.WnEnt3 S 0` FROM A START OF `xcQT0`.** -/
theorem xcEnt3_of_start (S : InaccSeq.{0}) (U : HgVD) (hU : HgSStart (hnVPB xcQT0) U) : WnEnt3 S 0 :=
  xcEnt3_of S xcQT0 U hU rfl (zero_lt_one.trans (xc_one_lt_SC Td.tdK_SC))

/-- **A start of `xcQT0` has the bound `φ(t₀, G)`.** -/
theorem xc_start_B (U : HgVD) (h : HgSStart (hnVPB xcQT0) U) : U.B = veblen (Wj.wjT 0) (gcG 0) := by
  rw [U.B_ix, h.ix]
  show veblen 1 (veblen (Wj.wjT 0) (gcG 0)) = _
  exact veblen_veblen_of_lt xc_one_lt_t0 _

/-- **A start of `xcQT0` lies above the bound `φ(ℓ, G+1)` of every level `ℓ < t₀`** (so it contains the systems of
all (A3) levels below `t₀` over their pseudo-bases `φ(ℓ, G)`). -/
theorem xc_start_cover (U : HgVD) (h : HgSStart (hnVPB xcQT0) U) {ℓ : Ordinal.{0}} (hℓ : ℓ < Wj.wjT 0) :
    veblen ℓ (gcG 0 + 1) < U.B := by
  rw [xc_start_B U h]
  have hF : InE (veblen (Wj.wjT 0) (gcG 0)) :=
    luP_E (xc_one_lt_t0.le) (luP_veblen _ _)
  have hG1 : gcG 0 + 1 < veblen (Wj.wjT 0) (gcG 0) :=
    (ev_isSuccLimit_of_inE hF).add_one_lt (wnQ3_bounds 0).1
  calc veblen ℓ (gcG 0 + 1) < veblen ℓ (veblen (Wj.wjT 0) (gcG 0)) := (veblen_lt_veblen_iff_right).2 hG1
    _ = veblen (Wj.wjT 0) (gcG 0) := veblen_veblen_of_lt hℓ _

/-- **The tower data of the family are not the gate-`0` data `Wy.wyLv (Wt.wtTwLv n)`** (gate `1` vs `0`): the
skeleton leaf `skA3TowPk` (gate `0`) is replaced by `Xc.xcTowPk` (gate `1`). -/
theorem xc_lv_ne (n : ℕ) : xcA3.lv (wtTw n) (xc_lev_tw n) ≠ wyLv (wtTwLv n) := by
  intro h
  have hg := congrArg HnLv.g h
  have h1 : (xcA3.lv (wtTw n) (xc_lev_tw n)).g = 1 := xg_tw n
  rw [h1, wyLv_g, wtTwLv_g] at hg
  exact one_ne_zero hg

end Googology.Trans.PoR.InaccPsi.R2.Xc
