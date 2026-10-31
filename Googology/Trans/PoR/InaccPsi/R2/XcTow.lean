import Googology.Trans.PoR.InaccPsi.R2.XcBr

/-!
# XcTow: THE (A3) PACKAGES AT THE TOWER LEVELS, THE `ω`-LIMIT AT `t₀`, AND `skSysA3Lev0W` FROM THE PSEUDO-BASE

* `xcFam` (**THE (A3) FAMILY** over raw data at every level below `t₀`, from `Ws.wsFam` and `Xc.xcCls`);
* `xc_wmExt` (**`Ws.WsExt` OF TWO ENTRIES GIVES `Wm.WmExt` OF THEIR PACKAGES**, for every code interface: lowering
  keeps the point, reading, gate and low field, so the two steps start at the same system);
* `xcPk n` (the package at the tower level `wtTw n = G^{⋯^G}` over the datum `xcA3.lv (wtTw n)`, gate `1`),
  `xcTowPk` (**THE TOWER PACKAGES EXTENDING EACH OTHER**, unconditional);
* `xcLvT0` (the datum of `t₀` with gate `1`, reading `ε_{Γ_{x+1}+1}`), `xcSeqT0` (**THE `ω`-SEQUENCE BELOW IT**),
  `xcPkT0` (**THE (A3) PACKAGE AT `t₀`**, unconditional);
* `xcRaise` (a pseudo-base over `Wn.wnLv3T0` raised to the gate `max 1 γ` over `xcLvT0`), `xc_start_raise` (the
  same systems start it);
* `xcEnt3_of` (**`Wn.WnEnt3 S 0` FROM THE PSEUDO-BASE `φ(t₀, G)` WITH A START ALONE**: the hypothesis is exactly
  the statement of the skeleton leaf `skA3QT0`).

No new axiom.  New definitions: `xcF`, `xcPk`, `xcLvT0`, `xcSeqT0`, `xcPkT0`, `xcRaise`.
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

/-! ## `WsExt` gives `WmExt` -/

/-- **`Ws.WsExt` OF TWO ENTRIES GIVES `Wm.WmExt` OF THEIR PACKAGES** (every code interface). -/
theorem xc_wmExt {C : WsC} {ℓ' ℓ : Ordinal.{0}} (hℓ' : C.Lev ℓ') (hℓ : C.Lev ℓ) {E' E : WoE}
    (hs' : WsSpec C ℓ' E') (hs : WsSpec C ℓ E) (hext : WsExt C ℓ E' E) :
    WmExt (wsPkOf ℓ' hℓ' E' hs') (wsPkOf ℓ hℓ E hs) := by
  intro Q hg hL hl U hU c x hc
  exact hext (woQR Q) (wsSt1 hℓ Q U hU) (wsGood_Q hℓ Q) (wsSt1_sh hℓ Q U hU) c x hc

/-! ## The family and the tower packages -/

/-- **THE (A3) FAMILY** at every level below `t₀`. -/
theorem xcFam : ∀ ℓ, xcA3.Lev ℓ → ℓ < Wj.wjT 0 → WsSpec xcA3 ℓ (wsF xcCls ℓ) ∧
    ∀ ℓ', ℓ' < ℓ → xcA3.Lev ℓ' → WsExt xcA3 ℓ (wsF xcCls ℓ') (wsF xcCls ℓ) := fun ℓ hℓ hL =>
  wsFam xcCls ℓ hℓ hL

/-- **THE PACKAGE AT THE TOWER LEVEL `wtTw n`** (datum `xcA3.lv (wtTw n)`, gate `1`). -/
noncomputable def xcPk (n : ℕ) : HnPk :=
  wsPkOf (wtTw n) (xc_lev_tw n) (wsF xcCls (wtTw n)) (xcFam _ (xc_lev_tw n) (wtTw_lt n)).1

theorem xcPk_Λ (n : ℕ) : (xcPk n).Λ = xcA3.lv (wtTw n) (xc_lev_tw n) := rfl

theorem xcPk_ext (n : ℕ) : WmExt (xcPk n) (xcPk (n + 1)) :=
  xc_wmExt _ _ _ _ ((xcFam _ (xc_lev_tw (n + 1)) (wtTw_lt (n + 1))).2 _ (wtTw_strict n) (xc_lev_tw n))

/-- **THE TOWER PACKAGES EXTENDING EACH OTHER** (unconditional). -/
theorem xcTowPk : ∃ K : ℕ → HnPk, (∀ n, (K n).Λ = xcA3.lv (wtTw n) (xc_lev_tw n)) ∧
    ∀ n, WmExt (K n) (K (n + 1)) := ⟨xcPk, xcPk_Λ, xcPk_ext⟩

/-! ## The datum of `t₀` with gate `1` and the `ω`-limit -/

theorem xc_one_lt_SC {Z : Ordinal.{0}} (hZ : SC Z) : (1 : Ordinal.{0}) < Z :=
  one_lt_omega0.trans (wn_omega_lt_SC hZ)

/-- **The datum of `t₀` with gate `1`** (the fields of `Wn.wnLv3T0`, gate `1`). -/
noncomputable def xcLvT0 : WnLv3 :=
  { wnLv3T0 with
    g := 1
    g_lt := wh_one_lt_Om1
    g_cl := fun _ _ hZ _ _ _ _ => xc_one_lt_SC hZ
    L_mem := fun S a b ha hb => wnLv3T0.L_mem S a b ha (show (0 : Ordinal.{0}) < b from zero_lt_one.trans hb)
    l_gtG := fun x hx hx1 _ => wnLv3T0.l_gtG x hx hx1 hx.pos
    l_pi := fun σ ρ hB _ => wnLv3T0.l_pi σ ρ hB hB.1.pos }

theorem xcLvT0_L : xcLvT0.L = Wj.wjT 0 := rfl

theorem xcLvT0_g : xcLvT0.g = 1 := rfl

theorem xcLvT0_l (x : Ordinal.{0}) : xcLvT0.l x = wnLv3T0.l x := rfl

theorem xc_twl {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (n : ℕ) :
    (xcPk n).Λ.l x = wtD.R (wtTw n) x := xc_tw_l n hx hx1

/-- **THE `ω`-SEQUENCE OF THE TOWER PACKAGES BELOW THE DATUM OF `t₀` WITH GATE `1`.** -/
noncomputable def xcSeqT0 : WmSeq (wyLv xcLvT0) where
  K := xcPk
  hL := fun k => (wtTowSeq.2.1 k).2
  hl := fun k x hx hx1 _ => by
    show (xcPk k).Λ.l x + x ≤ wnLv3T0.l x
    rw [xc_twl hx hx1 k, ← wtTwLv_l k hx hx1]; exact (wtTowSeq.2.2.2.1 x hx hx1 k).2
  hLs := fun k => (wtTowSeq.2.1 k).1
  hls := fun k x hx hx1 _ => by
    rw [xc_twl hx hx1 k, xc_twl hx hx1 (k + 1), ← wtTwLv_l k hx hx1, ← wtTwLv_l (k + 1) hx hx1]
    exact (wtTowSeq.2.2.2.1 x hx hx1 k).1
  cof := fun t ht => by
    have ht1 : t + 1 < wnLv3T0.L := (ev_isSuccLimit_of_inE wnT0_E).add_one_lt ht
    obtain ⟨n, hn⟩ := wtTowSeq.2.2.1 (t + 1) ht1
    exact ⟨n, hn⟩
  lcof := fun x hx hx1 _ t ht => by
    have ht' : t < wnLv3T0.l x := ht
    rw [wnLv3T0_l hx hx1] at ht'
    have ht1 : t + 1 < wnLv3T0.l x := by
      rw [wnLv3T0_l hx hx1]; exact (ev_isSuccLimit_of_inE (eN_E _)).add_one_lt ht'
    obtain ⟨n, hn⟩ := wtTowSeq.2.2.2.2 x hx hx1 (t + 1) ht1
    exact ⟨n, by rw [xc_twl hx hx1 n, ← wtTwLv_l n hx hx1]; exact hn⟩
  Kg := fun k => by show xg (wtTw k) ≤ 1; rw [xg_tw]
  ext := xcPk_ext

/-- **THE (A3) PACKAGE AT `t₀`** (datum `xcLvT0`: level `t₀`, gate `1`), unconditional. -/
noncomputable def xcPkT0 : WnPk3 := wyPk3 xcLvT0 (wmPkL xcSeqT0).St0 (wmPkL xcSeqT0).h0

theorem xcPkT0_Λ : xcPkT0.Λ = xcLvT0 := rfl

/-! ## Raising the gate of a pseudo-base of `t₀` -/

/-- **A pseudo-base over `Wn.wnLv3T0` raised to the gate `max 1 γ` over `xcLvT0`** (same point, reading, low
field). -/
noncomputable def xcRaise {ν : Ordinal.{0}} (Q : WnQ3 wnLv3T0 ν) : WnQ3 xcLvT0 ν where
  F := Q.F
  Fr := Q.Fr
  γ := max 1 Q.γ
  Zo := Q.Zo
  lv := Q.lv
  γ_ge := Q.γ_ge.trans (le_max_right _ _)
  lg := le_max_left _ _
  γ_lt := max_lt wh_one_lt_Om1 Q.γ_lt
  F_P := Q.F_P
  G_lt := Q.G_lt
  S_lt1 := Q.S_lt1
  F_mem := fun S _ _ ha hb => Q.F_mem S ha ((le_max_right _ _).trans_lt hb)
  S_mem := fun S _ _ ha hb => Q.S_mem S ha ((le_max_right _ _).trans_lt hb)
  F_code := Q.F_code
  F_cl := fun Z hZ hZ1 y hy hQy hyZ => max_lt (xc_one_lt_SC hZ) (Q.F_cl Z hZ hZ1 y hy hQy hyZ)
  S_cl := fun Z hZ hZ1 h => max_lt (xc_one_lt_SC hZ) (Q.S_cl Z hZ hZ1 h)
  Fr_gt := fun hx hx1 hγ => Q.Fr_gt hx hx1 ((le_max_right _ _).trans_lt hγ)
  Fr_P := fun hx hx1 hγ => Q.Fr_P hx hx1 ((le_max_right _ _).trans_lt hγ)
  S_Zo := fun hx hx1 hγ => Q.S_Zo hx hx1 ((le_max_right _ _).trans_lt hγ)
  Zo_fix := Q.Zo_fix
  Zo_G1 := Q.Zo_G1
  Fr_pi := fun hB hγ => Q.Fr_pi hB ((le_max_right _ _).trans_lt hγ)
  S_pi := fun hB hγ => Q.S_pi hB ((le_max_right _ _).trans_lt hγ)

theorem xcRaise_F {ν : Ordinal.{0}} (Q : WnQ3 wnLv3T0 ν) : (xcRaise Q).F = Q.F := rfl

theorem xcRaise_γ {ν : Ordinal.{0}} (Q : WnQ3 wnLv3T0 ν) : (xcRaise Q).γ = max 1 Q.γ := rfl

/-- **The systems that start a pseudo-base start its raise** (the start asks the gate only through its cut at
`ε`-numbers, where `γ` and `max 1 γ` agree). -/
theorem xc_start_raise {ν : Ordinal.{0}} (Q : WnQ3 wnLv3T0 ν) (U : HgVD) (h : HgSStart (hgdPB Q.toP) U) :
    HgSStart (hgdPB (xcRaise Q).toP) U := by
  have hcut : ∀ x, InE x → (max 1 Q.γ < x ↔ Q.γ < x) := fun x hx =>
    ⟨fun h => (le_max_right _ _).trans_lt h, fun h => max_lt (wo_one_lt_inE hx) h⟩
  refine ⟨h.ix, fun x hx hx1 => (h.γ x hx hx1).trans (hcut x hx).symm,
    fun x hx hx1 hγ => h.b x hx hx1 ((hcut x hx).1 hγ), fun x hx hx1 => ?_⟩
  rw [h.Z x hx hx1]
  show (if Q.γ < x then evZ (Q.Fr x) else Q.Zo x) = (if max 1 Q.γ < x then evZ (Q.Fr x) else Q.Zo x)
  by_cases hk : Q.γ < x
  · rw [if_pos hk, if_pos ((hcut x hx).2 hk)]
  · rw [if_neg hk, if_neg (fun h' => hk ((hcut x hx).1 h'))]

/-- **`Wn.WnEnt3 S 0` FROM THE PSEUDO-BASE `φ(t₀, G)` OVER `Wn.wnLv3T0` WITH A START** (the statement of the
skeleton leaf `skA3QT0`): the package is `xcPkT0`, the pseudo-base the raise. -/
theorem xcEnt3_of (S : InaccSeq.{0}) (Q : HnVQ (wyLv wnLv3T0) 0) (U : HgVD) (hU : HgSStart (hnVPB Q) U)
    (hF : Q.F = veblen (Wj.wjT 0) (gcG 0)) (hγ : Q.γ < Td.tdK S) : WnEnt3 S 0 :=
  ⟨xcPkT0, rfl, by show (1 : Ordinal.{0}) < _; exact xc_one_lt_SC Td.tdK_SC, xcRaise (wyQ3 Q), U,
    xc_start_raise (wyQ3 Q) U hU, hF, max_lt (xc_one_lt_SC Td.tdK_SC) hγ⟩

end Googology.Trans.PoR.InaccPsi.R2.Xc
