import Googology.Trans.PoR.InaccPsi.R2.WtTow
import Googology.Trans.PoR.InaccPsi.R2.WnLv3
import Googology.Trans.PoR.InaccPsi.R2.WmPkL

/-!
# WyLv: EVERY (A3) LEVEL DATUM IS A BAND LEVEL DATUM; (A3) PSEUDO-BASES, SPECIFICATIONS AND PACKAGES ARE THOSE OF THE
# `Hn` STACK; THE `ω`-LIMIT AT `t₀`

Since round 120 the band level datum `Hn.HnLv` asks `L < Γ(1)` and `ℓ(x) < Γ_{x+2}` (the old bounds `L < G`,
`ℓ(x) < Γ_{x+1}` are the predicate `Hn.HnLvG`).  Then:

* `wyLv` (**every `Wn.WnLv3` is an `Hn.HnLv`**, same level, reading, gate), `wyLv_notG` (it never has the old
  bounds), `wyNoBand_false` (**the old statement "every band level datum lies below `t₀`" is now FALSE**);
* `wyQ` / `wyQ3` (**an (A3) pseudo-base `Wn.WnQ3 Λ ν` is exactly an `Hn.HnVQ (wyLv Λ) ν`**, both ways),
  `wySpec_iff` (`Hn.HnVSpec` ⇔ `Wn.WnSpec3`), `wyPk3` / `wyPkOf` (**(A3) packages `Wn.WnPk3` ⇔ `Hn.HnPk` at
  `wyLv Λ`**);
* `wySeqT0` (**the `ω`-sequence of packages at the tower levels `G^{⋯^G}` is a `Wm.WmSeq` below `t₀`**, from
  `Wt.wtTowSeq`), `wyPkT0` (**THE PACKAGE AT `t₀`** = `Wm.wmPkL` of it), `wyEnt3_of` (**`Wn.WnEnt3 S 0` from the
  tower packages and the pseudo-base `φ(t₀, G)` with a start**), `wyEnt3_iff` (the target is equivalent to a package
  at `t₀` and that pseudo-base, both in `Hn` form).

No new axiom.  New definitions: `wyLv`, `wyQ`, `wyQ3`, `wyPk3`, `wyPkOf`, `wySeqT0`, `wyPkT0`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wy

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
open Googology.Trans.PoR.InaccPsi.R2.Wh Googology.Trans.PoR.InaccPsi.R2.Wm Googology.Trans.PoR.InaccPsi.R2.Wn
  Googology.Trans.PoR.InaccPsi.R2.Wt

/-! ## Every (A3) level datum is a band level datum -/

/-- **EVERY (A3) LEVEL DATUM IS A BAND LEVEL DATUM** (same level, reading, gate). -/
noncomputable def wyLv (Λ : WnLv3) : HnLv where
  L := Λ.L
  l := Λ.l
  u := Λ.u
  q := Λ.q
  g := Λ.g
  g_lt := Λ.g_lt
  q_lt := Λ.q_lt
  OL := (gl_Om1_lt_G0.trans Λ.G_lt).le
  L_G := Λ.L_G1
  L_eq := Λ.L_eq
  g_cl := Λ.g_cl
  L_mem := Λ.L_mem
  l_ge := Λ.l_ge
  l_lt := Λ.l_lt
  l_pi := Λ.l_pi

theorem wyLv_L (Λ : WnLv3) : (wyLv Λ).L = Λ.L := rfl

theorem wyLv_l (Λ : WnLv3) (x : Ordinal.{0}) : (wyLv Λ).l x = Λ.l x := rfl

theorem wyLv_g (Λ : WnLv3) : (wyLv Λ).g = Λ.g := rfl

/-- **An (A3) datum never has the (A1)/(A2) bounds.** -/
theorem wyLv_notG (Λ : WnLv3) : ¬ HnLvG (wyLv Λ) := fun h => absurd h.L_G (not_lt.2 Λ.G_lt.le)

/-- **THE OLD STATEMENT "EVERY BAND LEVEL DATUM LIES BELOW `t₀`" IS FALSE** for the widened band level datum
(witness: the datum of `t₀` itself). -/
theorem wyNoBand_false : ¬ (∀ Λ : HnLv, Λ.L < Wj.wjT 0) := fun h => lt_irrefl _ (h (wyLv wnLv3T0))

/-- **NON-VACUITY**: the datum of `t₀` and the tower data are band level data with level `t₀`, `G^{⋯^G}`. -/
theorem wyLv_T0 : (wyLv wnLv3T0).L = Wj.wjT 0 ∧ (wyLv wnLv3T0).g = 0 ∧ ∀ n, (wyLv (wtTwLv n)).L = wtTw n ∧
    (wyLv (wtTwLv n)).g = 0 := ⟨rfl, rfl, fun n => ⟨rfl, wtTwLv_g n⟩⟩

/-! ## Pseudo-bases, specifications, packages -/

section Q

variable {Λ : WnLv3} {ν : Ordinal.{0}}

/-- **An (A3) pseudo-base is a pseudo-base of the `Hn` stack.** -/
noncomputable def wyQ (Q : WnQ3 Λ ν) : HnVQ (wyLv Λ) ν where
  F := Q.F
  Fr := Q.Fr
  γ := Q.γ
  Zo := Q.Zo
  lv := Q.lv
  γ_ge := Q.γ_ge
  lg := Q.lg
  γ_lt := Q.γ_lt
  F_P := Q.F_P
  G_lt := Q.G_lt
  S_lt1 := Q.S_lt1
  F_mem := Q.F_mem
  S_mem := Q.S_mem
  F_code := Q.F_code
  F_cl := Q.F_cl
  S_cl := Q.S_cl
  Fr_gt := Q.Fr_gt
  Fr_P := Q.Fr_P
  S_Zo := Q.S_Zo
  Zo_fix := Q.Zo_fix
  Zo_G1 := Q.Zo_G1
  Fr_pi := Q.Fr_pi
  S_pi := Q.S_pi

/-- **A pseudo-base of the `Hn` stack at `wyLv Λ` is an (A3) pseudo-base.** -/
noncomputable def wyQ3 (Q : HnVQ (wyLv Λ) ν) : WnQ3 Λ ν where
  F := Q.F
  Fr := Q.Fr
  γ := Q.γ
  Zo := Q.Zo
  lv := Q.lv
  γ_ge := Q.γ_ge
  lg := Q.lg
  γ_lt := Q.γ_lt
  F_P := Q.F_P
  G_lt := Q.G_lt
  S_lt1 := Q.S_lt1
  F_mem := Q.F_mem
  S_mem := Q.S_mem
  F_code := Q.F_code
  F_cl := Q.F_cl
  S_cl := Q.S_cl
  Fr_gt := Q.Fr_gt
  Fr_P := Q.Fr_P
  S_Zo := Q.S_Zo
  Zo_fix := Q.Zo_fix
  Zo_G1 := Q.Zo_G1
  Fr_pi := Q.Fr_pi
  S_pi := Q.S_pi

theorem wyQ_F (Q : WnQ3 Λ ν) : (wyQ Q).F = Q.F := rfl

theorem wyQ_γ (Q : WnQ3 Λ ν) : (wyQ Q).γ = Q.γ := rfl

theorem wyQ3_F (Q : HnVQ (wyLv Λ) ν) : (wyQ3 Q).F = Q.F := rfl

theorem wyQ3_γ (Q : HnVQ (wyLv Λ) ν) : (wyQ3 Q).γ = Q.γ := rfl

/-- **The two level-`ω` pseudo-bases agree**, so the starts agree. -/
theorem wyQ_PB (Q : WnQ3 Λ ν) : hnVPB (wyQ Q) = hgdPB Q.toP := rfl

theorem wyQ3_PB (Q : HnVQ (wyLv Λ) ν) : hgdPB (wyQ3 Q).toP = hnVPB Q := rfl

/-- **THE SPECIFICATIONS AGREE.** -/
theorem wySpec_iff (Q : WnQ3 Λ ν) (U T : HgVD) : HnVSpec (wyQ Q) U T ↔ WnSpec3 Q U T :=
  ⟨fun h => ⟨h.B, h.γ, h.b, h.Z, h.extR, h.extg, h.high, h.RF, h.gF⟩,
    fun h => ⟨h.B, h.γ, h.b, h.Z, h.extR, h.extg, h.high, h.RF, h.gF⟩⟩

theorem wySpec3_iff (Q : HnVQ (wyLv Λ) ν) (U T : HgVD) : WnSpec3 (wyQ3 Q) U T ↔ HnVSpec Q U T :=
  ⟨fun h => ⟨h.B, h.γ, h.b, h.Z, h.extR, h.extg, h.high, h.RF, h.gF⟩,
    fun h => ⟨h.B, h.γ, h.b, h.Z, h.extR, h.extg, h.high, h.RF, h.gF⟩⟩

end Q

/-- **AN `Hn` PACKAGE AT `wyLv Λ` IS AN (A3) PACKAGE AT `Λ`.** -/
noncomputable def wyPk3 (Λ : WnLv3) (St0 : HnVStTy (wyLv Λ) 0) (h0 : ∀ Q U h, HnVSpec Q U (St0 Q U h)) : WnPk3 where
  Λ := Λ
  St0 := fun Q U hU => St0 (wyQ Q) U hU
  h0 := fun Q U hU => (wySpec_iff Q U _).1 (h0 (wyQ Q) U hU)

/-- **AN (A3) PACKAGE IS AN `Hn` PACKAGE** (at `wyLv K.Λ`). -/
noncomputable def wyPkOf (K : WnPk3) : HnPk where
  Λ := wyLv K.Λ
  St0 := fun Q U hU => K.St0 (wyQ3 Q) U hU
  h0 := fun Q U hU => (wySpec3_iff Q U _).1 (K.h0 (wyQ3 Q) U hU)

theorem wyPk3_Λ (Λ : WnLv3) (St0 : HnVStTy (wyLv Λ) 0) (h0 : ∀ Q U h, HnVSpec Q U (St0 Q U h)) :
    (wyPk3 Λ St0 h0).Λ = Λ := rfl

theorem wyPkOf_Λ (K : WnPk3) : (wyPkOf K).Λ = wyLv K.Λ := rfl

/-! ## The `ω`-limit at `t₀` along the tower -/

/-- **THE TOWER SEQUENCE OF PACKAGES BELOW `t₀`**: packages at the tower levels `wtTw n` (as band data) extending
each other give a `Wm.WmSeq` below the datum of `t₀` (levels, readings, cofinality, gates from `Wt.wtTowSeq`). -/
noncomputable def wySeqT0 (K : ℕ → HnPk) (hK : ∀ n, (K n).Λ = wyLv (wtTwLv n))
    (hext : ∀ n, WmExt (K n) (K (n + 1))) : WmSeq (wyLv wnLv3T0) where
  K := K
  hL := fun k => by rw [hK k]; exact (wtTowSeq.2.1 k).2
  hl := fun k x hx hx1 _ => by rw [hK k]; exact (wtTowSeq.2.2.2.1 x hx hx1 k).2
  hLs := fun k => by rw [hK k, hK (k + 1)]; exact (wtTowSeq.2.1 k).1
  hls := fun k x hx hx1 _ => by rw [hK k, hK (k + 1)]; exact (wtTowSeq.2.2.2.1 x hx hx1 k).1
  cof := fun t ht => by
    have ht1 : t + 1 < wnLv3T0.L := (ev_isSuccLimit_of_inE wnT0_E).add_one_lt ht
    obtain ⟨n, hn⟩ := wtTowSeq.2.2.1 (t + 1) ht1
    exact ⟨n, by rw [hK n]; exact hn⟩
  lcof := fun x hx hx1 _ t ht => by
    have ht' : t < wnLv3T0.l x := ht
    rw [wnLv3T0_l hx hx1] at ht'
    have ht1 : t + 1 < wnLv3T0.l x := by
      rw [wnLv3T0_l hx hx1]; exact (ev_isSuccLimit_of_inE (eN_E _)).add_one_lt ht'
    obtain ⟨n, hn⟩ := wtTowSeq.2.2.2.2 x hx hx1 (t + 1) ht1
    exact ⟨n, by rw [hK n]; exact hn⟩
  Kg := fun k => by rw [hK k]; exact wtTowSeq.1 k
  ext := hext

/-- **THE (A3) PACKAGE AT `t₀`**: the `ω`-limit (`Wm.wmPkL`) of a tower sequence, as a `Wn.WnPk3`. -/
noncomputable def wyPkT0 (H : WmSeq (wyLv wnLv3T0)) : WnPk3 := wyPk3 wnLv3T0 (wmPkL H).St0 (wmPkL H).h0

theorem wyPkT0_Λ (H : WmSeq (wyLv wnLv3T0)) : (wyPkT0 H).Λ = wnLv3T0 := rfl

/-- **`Wn.WnEnt3 S 0` FROM THE TOWER PACKAGES AND THE PSEUDO-BASE `φ(t₀, G)`**: packages at the tower levels
extending each other, and a pseudo-base of level `t₀` (over the datum of `t₀`) at `φ(t₀, G)` with gate `< K` that
some system starts. -/
theorem wyEnt3_of (S : InaccSeq.{0}) (K : ℕ → HnPk) (hK : ∀ n, (K n).Λ = wyLv (wtTwLv n))
    (hext : ∀ n, WmExt (K n) (K (n + 1))) (Q : HnVQ (wyLv wnLv3T0) 0) (U : HgVD) (hU : HgSStart (hnVPB Q) U)
    (hF : Q.F = veblen (Wj.wjT 0) (gcG 0)) (hγ : Q.γ < Td.tdK S) : WnEnt3 S 0 :=
  ⟨wyPkT0 (wySeqT0 K hK hext), rfl, InE.pos (Low.opow_eq_self_of_SC (Td.tdK_SC (S := S))), wyQ3 Q, U, hU, hF, hγ⟩

/-- **THE (A3) TARGET AT `t₀` IN `Hn` FORM**: `Wn.WnEnt3 S 0` holds iff some (A3) datum `Λ` of level `t₀` with
gate `< K` carries an `Hn` package (a step at every pseudo-base of `wyLv Λ`) and a pseudo-base of `wyLv Λ` at
`φ(t₀, G)` with gate `< K` that some system starts. -/
theorem wyEnt3_iff (S : InaccSeq.{0}) : WnEnt3 S 0 ↔
    ∃ Λ : WnLv3, Λ.L = Wj.wjT 0 ∧ Λ.g < Td.tdK S ∧
      (∃ K : HnPk, K.Λ = wyLv Λ) ∧ ∃ (Q : HnVQ (wyLv Λ) 0) (U : HgVD) (_ : HgSStart (hnVPB Q) U),
        Q.F = veblen (Wj.wjT 0) (gcG 0) ∧ Q.γ < Td.tdK S := by
  constructor
  · rintro ⟨K, hL, hg, Q, U, hU, hF, hγ⟩
    exact ⟨K.Λ, hL, hg, ⟨wyPkOf K, rfl⟩, wyQ Q, U, hU, hF, hγ⟩
  · rintro ⟨Λ, hL, hg, ⟨K, hK⟩, Q, U, hU, hF, hγ⟩
    obtain ⟨KΛ, St0, h0⟩ := K
    subst hK
    exact ⟨wyPk3 Λ St0 h0, hL, hg, wyQ3 Q, U, hU, hF, hγ⟩

end Googology.Trans.PoR.InaccPsi.R2.Wy
