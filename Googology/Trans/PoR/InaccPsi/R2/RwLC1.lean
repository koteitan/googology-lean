import Googology.Trans.PoR.InaccPsi.R2.RwEX

/-!
# Code levels: the level-`E` family for a code `E` (not only `E < ρ_λ`)

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `EE_j = Rv.rvEE S X₀ β E j`,
`EX_j = Rw.rwEX S X₀ β j`.  For a code exponent `E` the level `W^E` has the image `Ω^{Θ E}`; `E` must be own over
the offset: `E < EX_j(X₀, β)` for some `j` (so `E < ψ_{Ω₂}(β + W^{X₀ + W^E})`, `Rw.rwEX_gt`).

`RwLevC S λ E`: for every base bound `b` and offset `(X₀, X̂₀)` over `b` with `W^E ∣ X₀`, the bounds, and
`E < EX_j(X₀, b)`: `RvTop b (X₀ + W^E) (X̂₀ + Ω^{Θ E}) 0`.

* `rwEEc_lt_succ`, `rwEEc_mono`, `rwEEc_sup`, `rwEEc_ge`, `rwEEc_gtT` (as `Rv.rvEE_*` with `E < Ω₁` replaced by
  the ownness `E < ψ_{Ω₂}(β + W^{X₀ + W^E})`);
* `rwSh_mc` (the members `X₀ + W^E·ζ` are shifts own relative to `β`);
* `rwFamC` (**the level-`E` family**: under `RwLevC E`, every code `ζ < EE_j` with `Θ ζ < Ω₁` gives an offset);
* `rwEEc_code` (`EE_j` is a code with `Θ(EE_j) < Ω₁`).

No new axiom.  New definition: `RwLevC`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv

variable {S : InaccSeq.{0}}

/-- **The code-level statement**: the top law at `X₀ + W^E`, image `X̂₀ + Ω^{Θ E}`, over every offset. -/
def RwLevC (S : InaccSeq.{0}) (l E : Ordinal.{0}) : Prop :=
  ∀ b X0 Xh0, RvOff S l b X0 Xh0 → leWe E ∣ X0 → X0 + leWe E + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)) →
    Xh0 + leOe (gxTh (upsilon l) (ldAtR S l) E) + Om 1 < S.psi 0 (Om (1 + 1)) →
    (∃ j, E < rwEX S X0 b j) →
    RvTop S l b (X0 + leWe E) (Xh0 + leOe (gxTh (upsilon l) (ldAtR S l) E)) 0

theorem rvEE_one_le {X0 β e : Ordinal.{0}} (j : ℕ) : (1 : Ordinal.{0}) ≤ rvEE S X0 β e j :=
  Order.one_le_iff_pos.2 (rvEE_SC j).1

section Seq

variable {X0 β e : Ordinal.{0}}

variable (hβown : ∀ d, d ≤ leWe (X0 + leWe (e + 1)) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
  (hX0m : X0 ∈ S.CSet 0 (S.psi (β + leWe X0) (Om (1 + 1))))
  (heo : e < S.psi (β + leWe (X0 + leWe e)) (Om (1 + 1)))

include hβown hX0m heo

omit hβown hX0m in
theorem rwEEc_e_lt {x : Ordinal.{0}} (hx : 1 ≤ x) : e < S.psi (β + leWe (X0 + leWe e * x)) (Om (1 + 1)) :=
  heo.trans_le (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono
    ((add_le_add_iff_left X0).2 (by
      calc leWe e = leWe e * 1 := (mul_one _).symm
        _ ≤ leWe e * x := leMulWe_mono hx))))).1

theorem rwEEc_lt_succ : ∀ j, rvEE S X0 β e j < rvEE S X0 β e (j + 1)
  | 0 => (psiS_bounds (S := S) _ 1).1
  | j + 1 => by
    have IH := rwEEc_lt_succ j
    have hle : rvEE S X0 β e (j + 1) ≤ rvEE S X0 β e (j + 2) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
        (leWe_mono ((add_le_add_iff_left X0).2 (leMulWe_mono IH.le))))).1
    refine psi_lt_psi_of_mem (InR_Om_succ 1)
      ((add_lt_add_iff_left β).2 (leWe_lt ((add_lt_add_iff_left X0).2 (leMulWe_lt IH)))) ?_
    have hX0 : X0 ∈ S.CSet (β + leWe (X0 + leWe e * rvEE S X0 β e (j + 1)))
        (S.psi (β + leWe (X0 + leWe e * rvEE S X0 β e (j + 1))) (Om (1 + 1))) :=
      CSet_mono zero_le (psi_mono (S := S) (InR_Om_succ 1)
        ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1 hX0m
    refine CSet.add_mem (hβown _ (leWe_mono ((add_le_add_iff_left X0).2 (rvWe_lt_succ (rvEE_lt_Om2 _)).le)))
      (leWe_mem (CSet.add_mem hX0 (leMulWe_mem (CSet.of_lt (rwEEc_e_lt heo (rvEE_one_le _)))
        (CSet.of_lt (IH.trans_le hle)))))

theorem rwEEc_mono {j j' : ℕ} (h : j ≤ j') : rvEE S X0 β e j ≤ rvEE S X0 β e j' :=
  (strictMono_nat_of_lt_succ (fun i => rwEEc_lt_succ hβown hX0m heo i)).monotone h

/-- **`T_{X₀ + W^{e+1}}(β) = sup_j EE_j`** for an own code exponent `e`. -/
theorem rwEEc_sup (hβd : leWe (X0 + leWe (e + 1)) ∣ β)
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
    (hX0G3 : X0 + leWe (e + 1) < S.psi 0 (Om (1 + 1 + 1)))
    {x : Ordinal.{0}} (hx : x < leTe S (X0 + leWe (e + 1)) β) : ∃ j, x < rvEE S X0 β e j := by
  have hbdd : BddAbove (Set.range (rvEE S X0 β e)) := Ordinal.bddAbove_of_small
  have hlt : ∀ y, y < ⨆ j, rvEE S X0 β e j ↔ ∃ j, y < rvEE S X0 β e j := fun y => lt_ciSup_iff hbdd
  have hKQ : ∀ j, rvEE S X0 β e j < ⨆ j, rvEE S X0 β e j :=
    fun j => (hlt _).2 ⟨j + 1, rwEEc_lt_succ hβown hX0m heo j⟩
  have hΩQ : Om (1 : Ordinal.{0}) < ⨆ j, rvEE S X0 β e j := hKQ 0
  have hQSC : SC (⨆ j, rvEE S X0 β e j) := by
    refine ⟨(Om_pos one_ne_zero).trans hΩQ, fun x hx y hy => ?_⟩
    obtain ⟨i, hi⟩ := (hlt _).1 hx
    obtain ⟨j, hj⟩ := (hlt _).1 hy
    have hi' := hi.trans_le (rwEEc_mono hβown hX0m heo (le_max_left i j))
    have hj' := hj.trans_le (rwEEc_mono hβown hX0m heo (le_max_right i j))
    exact ((rvEE_SC (max i j)).2 _ hi' _ hj').trans (hKQ _)
  set Q := ⨆ j, rvEE S X0 β e j with hQ
  have hG3 : SC (S.psi 0 (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) 0
  have hWG3 : Om (1 + 1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (psiS_bounds (S := S) 0 (1 + 1)).1
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hX1 : S.psi (β + leWe X0) (Om (1 + 1)) < rvEE S X0 β e 1 := by
    refine psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left β).2
      (leWe_lt (lt_add_of_pos_right X0 (mul_pos (leWe_pos e) (Om_pos one_ne_zero))))) ?_
    exact CSet.add_mem (hβown _ (leWe_mono ((add_le_add_iff_left X0).2 (rvWe_lt_succ gg_Om1_lt_Om2).le)))
      (leWe_mem (CSet_mono zero_le (psi_mono (S := S) (InR_Om_succ 1)
        ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1 hX0m))
  have hβ1 : S.psi β (Om (1 + 1)) < rvEE S X0 β e 1 :=
    lt_of_le_of_lt (psi_mono (S := S) (InR_Om_succ 1) le_self_add).1 hX1
  have heQ : e < Q := (rwEEc_e_lt heo (Order.one_le_iff_pos.2 (Om_pos one_ne_zero))).trans (hKQ 1)
  have hFQ : leTe S (X0 + leWe (e + 1)) β ≤ Q := by
    refine lePsi2_le hQSC hΩQ fun x hx hc => ?_
    rcases le_or_gt x β with hxβ | hxβ
    · exact ((psi_mono (S := S) (InR_Om_succ 1) hxβ).1.trans_lt hβ1).trans (hKQ 1)
    obtain ⟨x', rfl⟩ := exists_add_of_le hxβ.le
    have hx'W : x' < leWe (X0 + leWe (e + 1)) := (add_lt_add_iff_left β).1 hx
    rcases eq_or_ne x' 0 with rfl | hx0
    · rw [add_zero]; exact (hβ1.trans (hKQ 1))
    have hc2 := LeCl.mod hQSC.1 ldOm2_SC.isPrincipal (Om (1 + 1) * (X0 + leWe (e + 1))) hc
    change LeCl (Om (1 + 1)) Q ((β + x') % S.psi 0 (Om (1 + 1 + 1)) % leWe (X0 + leWe (e + 1))) at hc2
    rw [Ordinal.mod_mod_of_dvd _ (leWe_lt_SC hG3 hWG3 hX0G3).2] at hc2
    have hm : (β + x') % leWe (X0 + leWe (e + 1)) = x' := by
      obtain ⟨q, hq⟩ := hβd
      rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hx'W]
    rw [hm] at hc2
    obtain ⟨-, hlog⟩ := leClDec hQSC ldOm2_SC x' hc2
    have hla : log ω x' < Om (1 + 1) * X0 + leWe (1 + e + 1) := by
      rw [show (1 : Ordinal.{0}) + e + 1 = 1 + (e + 1) from add_assoc _ _ _, ← rvWe_mul (e + 1), ← mul_add]
      exact (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hx0).trans_lt hx'W)
    have hx'lt := lt_opow_succ_log_self one_lt_omega0 x'
    rw [Order.succ_eq_add_one] at hx'lt
    rcases lt_or_ge (log ω x') (Om (1 + 1) * X0) with h1 | h1
    · have hxX : x' < leWe X0 := hx'lt.trans_le (opow_le_opow_right omega0_pos (Order.add_one_le_of_lt h1))
      exact ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hxX.le)).1.trans_lt hX1).trans
        (hKQ 1)
    have hXC : LeCl (Om (1 + 1)) Q (Om (1 + 1) * X0) :=
      LeCl.mulK hQSC ldOm2_SC X0 (hX0cl Q hQSC (hX1.trans (hKQ 1)).le)
    have hu := (leClDec hQSC ldOm2_SC (log ω x') hlog).1 _ hXC h1
    have hdec : Om (1 + 1) * X0 + (log ω x' - Om (1 + 1) * X0) = log ω x' := Ordinal.add_sub_cancel_of_le h1
    have hu2 : log ω x' - Om (1 + 1) * X0 < ω ^ (Om (1 + 1) * (1 + e) + Om (1 + 1)) := by
      rw [← mul_add_one]; change _ < leWe (1 + e + 1)
      have : Om (1 + 1) * X0 + (log ω x' - Om (1 + 1) * X0) < Om (1 + 1) * X0 + leWe (1 + e + 1) := by
        rw [hdec]; exact hla
      exact (add_lt_add_iff_left _).1 this
    have h1e : LeCl (Om (1 + 1)) Q (1 + e) :=
      LeCl.small (hQSC.isPrincipal ((one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1)).trans hΩQ) heQ)
    have hb := leCl_boundY hQSC ldOm2_SC h1e _ hu hu2
    change _ < leWe (1 + e) * Q at hb
    have hK0 : leWe (1 + e) ≠ 0 := (leWe_pos _).ne'
    have hq : (log ω x' - Om (1 + 1) * X0) / leWe (1 + e) < Q := (Ordinal.lt_mul_iff_div_lt hK0).1 hb
    obtain ⟨j, hj⟩ := (hlt _).1 hq
    have h2 : log ω x' + 1 ≤ Om (1 + 1) * (X0 + leWe e * rvEE S X0 β e j) := by
      rw [mul_add, ← mul_assoc, rvWe_mul e, ← hdec, add_assoc]
      refine (add_le_add_iff_left _).2 (Order.add_one_le_of_lt ?_)
      calc log ω x' - Om (1 + 1) * X0
          < leWe (1 + e) * ((log ω x' - Om (1 + 1) * X0) / leWe (1 + e)) + leWe (1 + e) :=
            Ordinal.lt_mul_div_add _ hK0
        _ = leWe (1 + e) * ((log ω x' - Om (1 + 1) * X0) / leWe (1 + e) + 1) := (mul_add_one _ _).symm
        _ ≤ leWe (1 + e) * rvEE S X0 β e j := mul_le_mul_right (Order.add_one_le_of_lt hj) _
    have hxW : x' < leWe (X0 + leWe e * rvEE S X0 β e j) := hx'lt.trans_le (opow_le_opow_right omega0_pos h2)
    exact ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hxW.le)).1).trans_lt (hKQ (j + 1))
  exact (hlt x).1 (hx.trans_le hFQ)

theorem rwEEc_ge (hβd : leWe (X0 + leWe (e + 1)) ∣ β)
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
    (hX0G3 : X0 + leWe (e + 1) < S.psi 0 (Om (1 + 1 + 1)))
    {x : Ordinal.{0}} (hx : leTe S (X0 + leWe (e + 1)) β ≤ x) :
    leTe S (X0 + leWe (e + 1)) β ≤ S.psi (β + leWe (X0 + leWe e * x)) (Om (1 + 1)) := by
  by_contra h
  push Not at h
  obtain ⟨j, hj⟩ := rwEEc_sup hβown hX0m heo hβd hX0cl hX0G3 h
  have h1 : rvEE S X0 β e (j + 1) ≤ S.psi (β + leWe (X0 + leWe e * x)) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
      (leWe_mono ((add_le_add_iff_left X0).2 (leMulWe_mono ((rvEE_le_top j).trans hx)))))).1
  exact absurd (hj.trans_le ((rwEEc_lt_succ hβown hX0m heo j).le.trans h1)) (lt_irrefl _)

theorem rwEEc_gtT (hβd : leWe (X0 + leWe (e + 1)) ∣ β)
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
    (hX0G3 : X0 + leWe (e + 1) < S.psi 0 (Om (1 + 1 + 1)))
    {x : Ordinal.{0}} (hx : x < leTe S (X0 + leWe (e + 1)) β) :
    x < S.psi (β + leWe (X0 + leWe e * x)) (Om (1 + 1)) := by
  obtain ⟨j, hj⟩ := rwEEc_sup hβown hX0m heo hβd hX0cl hX0G3 hx
  exact rvEE_gt j x hj

end Seq

section Mem

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The members `(X₀ + W^E·ζ, X̂₀ + Ω^{Θ E}·Θ ζ)` of the level-`E` family are shifts own relative to `β`.** -/
theorem rwSh_mc {E : Ordinal.{0}} (he1 : 1 ≤ E) (hE : GxCl (upsilon l) (ldAtR S l) E) (hEW : E < Om (1 + 1))
    {β X0 Xh0 ζ : Ordinal.{0}}
    (hoff : RvOff S l β X0 Xh0) (hEo : E < S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)))
    (hζ : GxCl (upsilon l) (ldAtR S l) ζ) (hζW : ζ < Om (1 + 1)) (hζ0 : ζ ≠ 0)
    (hown : ζ < S.psi (β + leWe (X0 + leWe E * ζ)) (Om (1 + 1)))
    (hΘ1 : gxTh (upsilon l) (ldAtR S l) ζ < Om 1)
    (hG3 : X0 + leWe (E + 1) + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)))
    (hG : Xh0 + leOe (gxTh (upsilon l) (ldAtR S l) E + 1) + Om 1 < S.psi 0 (Om (1 + 1))) :
    RvSh S l β (X0 + leWe E * ζ) (Xh0 + leOe (gxTh (upsilon l) (ldAtR S l) E) * gxTh (upsilon l) (ldAtR S l) ζ) := by
  obtain ⟨hd, hH, hm, hmh, hcl, hclh⟩ := rvOff_data hoff
  have hle : S.psi (β + leWe X0) (Om (1 + 1)) ≤ S.psi (β + leWe (X0 + leWe E * ζ)) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1
  have hEle : S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ S.psi (β + leWe (X0 + leWe E * ζ)) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono ((add_le_add_iff_left X0).2 (by
      calc leWe E = leWe E * 1 := (mul_one _).symm
        _ ≤ leWe E * ζ := leMulWe_mono (Order.one_le_iff_ne_zero.2 hζ0)))))).1
  have hEo' := hEo.trans_le hEle
  have hΘown := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hζ hown
  have hΘEo := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hE hEo'
  have hWk : Om (1 + 1) ∣ leWe E := by
    have h := leWe_dvd he1; rwa [leWe_one] at h
  have hlt1 : leWe E * ζ < leWe (E + 1) := rvWe_lt_succ hζW
  have hlt2 : leOe (gxTh (upsilon l) (ldAtR S l) E) * gxTh (upsilon l) (ldAtR S l) ζ <
      leOe (gxTh (upsilon l) (ldAtR S l) E + 1) := rvOe_lt_succ hΘ1
  refine ⟨fun h => (mul_ne_zero (leWe_pos E).ne' hζ0) (le_antisymm (h ▸ le_add_self) zero_le),
    dvd_add hd (hWk.trans (dvd_mul_right _ _)),
    CSet.add_mem hH (leMulWe_mem ((ldHull_iff hl hX hEW).2 hE) ((ldHull_iff hl hX hζW).2 hζ)),
    CSet.add_mem (CSet_mono le_rfl hle hm) (leMulWe_mem (CSet.of_lt hEo') (CSet.of_lt hown)),
    CSet.add_mem (CSet_mono le_rfl (gxTh_mono hle) hmh)
      (leMulOe_mem (CSet.of_lt hΘEo) (CSet.of_lt hΘown)), ?_, ?_,
    fun Q hQ hb => LeCl.add (hcl Q hQ (hle.trans hb)) (rvCl_mulOp hQ (LeCl.mulK hQ ldOm2_SC E
      (LeCl.small (hEo'.trans_le hb))) ldOm2_SC _ (LeCl.small (hown.trans_le hb))),
    fun Q hQ hb => LeCl.add (hclh Q hQ ((gxTh_mono hle).trans hb)) (rvCl_mulOp hQ (LeCl.mulK hQ Ph.ph_SC_Om1 _
      (LeCl.small (hΘEo.trans_le hb))) Ph.ph_SC_Om1 _ (LeCl.small (hΘown.trans_le hb)))⟩
  · refine lt_of_le_of_lt ?_ hG3
    exact add_le_add_left ((add_le_add_iff_left X0).2 hlt1.le) _
  · refine lt_of_le_of_lt ?_ hG
    exact add_le_add_left ((add_le_add_iff_left Xh0).2 hlt2.le) _

end Mem

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {E : Ordinal.{0}} (he1 : 1 ≤ E) (hE : GxCl (upsilon l) (ldAtR S l) E) (hEW : E < Om (1 + 1))
  (IH : RwLevC S l E)

include hl hX he1 hE hEW IH

/-- **The level-`E` family over `β`** (bound `ζ < EE_j(X₀, β, E)`), `E` own over `X₀` at `β`. -/
theorem rwFamC {X0 Xh0 β : Ordinal.{0}} (hoff : RvOff S l β X0 Xh0) (hd : leWe (E + 1) ∣ X0)
    (hG3 : X0 + leWe (E + 1) + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)))
    (hG : Xh0 + leOe (gxTh (upsilon l) (ldAtR S l) E + 1) + Om 1 < S.psi 0 (Om (1 + 1)))
    (hEX : ∃ j, E < rwEX S X0 β j) :
    ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → (∃ j, ζ < rvEE S X0 β E j) →
      gxTh (upsilon l) (ldAtR S l) ζ < Om 1 →
      RvOff S l β (X0 + leWe E * ζ) (Xh0 + leOe (gxTh (upsilon l) (ldAtR S l) E) * gxTh (upsilon l) (ldAtR S l) ζ) := by
  set ΘE := gxTh (upsilon l) (ldAtR S l) E with hΘE_def
  have hk0 : leWe E ≠ 0 := (leWe_pos E).ne'
  have hOk0 : leOe ΘE ≠ 0 := (leOe_pos _).ne'
  have hdk : leWe E ∣ X0 := (leWe_dvd le_self_add).trans hd
  have hEo : E < S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) := by
    obtain ⟨j, hj⟩ := hEX; exact rwEX_gt j E hj
  have hmem : ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → (∃ j, ζ < rvEE S X0 β E j) →
      gxTh (upsilon l) (ldAtR S l) ζ < Om 1 → ζ ≠ 0 →
      RvSh S l β (X0 + leWe E * ζ) (Xh0 + leOe ΘE * gxTh (upsilon l) (ldAtR S l) ζ) := fun ζ hζ hζT hΘ hζ0 => by
    obtain ⟨j, hj⟩ := hζT
    exact rwSh_mc hl hX he1 hE hEW hoff hEo hζ (hj.trans (rvEE_lt_Om2 j)) hζ0 (rvEE_gt j ζ hj) hΘ hG3 hG
  intro ζ
  induction ζ using WellFoundedLT.induction with
  | ind ζ IHz =>
  intro hζ hζT hΘ1
  have hζW : ζ < Om (1 + 1) := by obtain ⟨j, hj⟩ := hζT; exact hj.trans (rvEE_lt_Om2 j)
  rcases zero_or_succ_or_isSuccLimit ζ with h0 | ⟨ζ0, hζ0⟩ | hlim
  · subst h0; simpa only [mul_zero, add_zero, gxTh_zero] using hoff
  · rw [succ_eq_add_one] at hζ0
    subst hζ0
    have hζ0c := rqCode_pred hl hX hζ hζW
    have hΘ0 : gxTh (upsilon l) (ldAtR S l) ζ0 < Om 1 := (gxTh_mono (lt_add_one ζ0).le).trans_lt hΘ1
    have hT0 : ∃ j, ζ0 < rvEE S X0 β E j := by
      obtain ⟨j, hj⟩ := hζT; exact ⟨j, (lt_add_one ζ0).trans hj⟩
    have hoff0 := IHz ζ0 (lt_add_one ζ0) hζ0c hT0 hΘ0
    have hΘs := rqTh_succ hl hX hζ0c
    have hle1 : leWe E * ζ0 + leWe E ≤ leWe (E + 1) := by
      rw [← mul_add_one]; exact (rvWe_lt_succ hζW).le
    have hle2 : leOe ΘE * gxTh (upsilon l) (ldAtR S l) ζ0 + leOe ΘE ≤ leOe (ΘE + 1) := by
      rw [← mul_add_one, ← hΘs]; exact (rvOe_lt_succ hΘ1).le
    have hEX0 : ∃ j, E < rwEX S (X0 + leWe E * ζ0) β j := by
      obtain ⟨j, hj⟩ := hEX; exact ⟨j, hj.trans_le (rwEX_mono_off le_self_add j)⟩
    have ht := IH β _ _ hoff0 (dvd_add hdk (dvd_mul_right _ _))
      (lt_of_le_of_lt (add_le_add_left (by rw [add_assoc]; exact (add_le_add_iff_left X0).2 hle1) _) hG3)
      (lt_of_le_of_lt (add_le_add_left (by rw [add_assoc]; exact (add_le_add_iff_left Xh0).2 hle2) _) hG)
      hEX0
    rw [add_assoc, add_assoc, ← mul_add_one, ← mul_add_one, ← hΘs] at ht
    exact Or.inr ⟨hmem _ hζ hζT hΘ1 (by simp), ht⟩
  · have hζ0 : ζ ≠ 0 := hlim.ne_bot
    have hs := hmem ζ hζ hζT hΘ1 hζ0
    have hΘpos : 0 < gxTh (upsilon l) (ldAtR S l) ζ := by
      have := gxTh_lt (Z := upsilon l) (At := ldAtR S l) (GxCl.zero (leRho hl hX).1.1) (pos_iff_ne_zero.2 hζ0)
      rwa [gxTh_zero] at this
    have hsub : ∀ c, GxCl (upsilon l) (ldAtR S l) c → c < ζ →
        RvSh S l β (X0 + leWe E * (c + 1)) (Xh0 + leOe ΘE * gxTh (upsilon l) (ldAtR S l) (c + 1)) ∧
        RvTop S l β (X0 + leWe E * (c + 1)) (Xh0 + leOe ΘE * gxTh (upsilon l) (ldAtR S l) (c + 1)) 0 ∧
        gxTh (upsilon l) (ldAtR S l) (c + 1) < gxTh (upsilon l) (ldAtR S l) ζ := by
      intro c hc hcζ
      have hc1 := hlim.succ_lt hcζ
      have hc1c := rqCode_succ hl hX hc (hc1.trans hζW)
      have hΘc : gxTh (upsilon l) (ldAtR S l) (c + 1) < Om 1 := (gxTh_mono hc1.le).trans_lt hΘ1
      have hT1 : ∃ j, c + 1 < rvEE S X0 β E j := by
        obtain ⟨j, hj⟩ := hζT; exact ⟨j, hc1.trans hj⟩
      have h := rvOff_ne (IHz _ hc1 hc1c hT1 hΘc)
        (fun h => (mul_ne_zero hk0 (by simp)) (le_antisymm (h ▸ le_add_self) zero_le))
      exact ⟨h.1, h.2, gxTh_lt hc1c hc1⟩
    refine Or.inr ⟨hs, rvTopLimSh hl hX hs (fun x hxH hx => ?_) (fun z hz => ?_)⟩
    · rcases lt_or_ge x X0 with hxX | hxX
      · have hX00 : X0 ≠ 0 := (zero_le.trans_lt hxX).ne'
        obtain ⟨hs0, ht0⟩ := rvOff_ne hoff hX00
        refine ⟨X0, Xh0, le_self_add, hxX, lt_add_of_pos_right _ (mul_pos (leOe_pos _) hΘpos), hs0, ht0⟩
      · obtain ⟨r, rfl⟩ := exists_add_of_le hxX
        have hr : r < leWe E * ζ := (add_lt_add_iff_left X0).1 hx
        have hrW : r < leWe (E + 1) := hr.trans (rvWe_lt_succ hζW)
        have hrH : r ∈ cdHull S l := by
          have h1 := leModP_mem (S := S) (Om (1 + 1) * (E + 1)) hxH
          have hm : (X0 + r) % ω ^ (Om (1 + 1) * (E + 1)) = r := by
            obtain ⟨q, hq⟩ := hd
            change (X0 + r) % leWe (E + 1) = r
            rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hrW]
          rwa [hm] at h1
        have hq : r / leWe E < ζ := (Ordinal.lt_mul_iff_div_lt hk0).1 hr
        have hqc := (ldHull_iff hl hX (hq.trans hζW)).1
          (leDivOp_mem (dvd_mul_right _ _) hrH (by rw [← mul_add_one]; exact hrW))
        obtain ⟨hs1, ht1, hΘlt⟩ := hsub _ hqc hq
        refine ⟨_, _, ?_, ?_, (add_lt_add_iff_left Xh0).2 ((mul_lt_mul_iff_right₀ (leOe_pos _)).2 hΘlt), hs1, ht1⟩
        · exact (add_le_add_iff_left X0).2 (mul_le_mul_right (Order.add_one_le_of_lt hq) _)
        · refine (add_lt_add_iff_left X0).2 ?_
          rw [mul_add_one]; exact Ordinal.lt_mul_div_add r hk0
    · rcases lt_or_ge z Xh0 with hzX | hzX
      · have hXh00 : Xh0 ≠ 0 := (zero_le.trans_lt hzX).ne'
        obtain ⟨hs0, ht0⟩ := rvOff_neh hoff hXh00
        exact ⟨X0, Xh0, lt_add_of_pos_right _ (mul_pos (leWe_pos E) (pos_iff_ne_zero.2 hζ0)), hzX, hs0, ht0⟩
      · obtain ⟨u, rfl⟩ := exists_add_of_le hzX
        have hu : u < leOe ΘE * gxTh (upsilon l) (ldAtR S l) ζ := (add_lt_add_iff_left Xh0).1 hz
        have hq : u / leOe ΘE < gxTh (upsilon l) (ldAtR S l) ζ := (Ordinal.lt_mul_iff_div_lt hOk0).1 hu
        obtain ⟨c, hc, hcζ, hcz⟩ := gxTh_onto hq
        obtain ⟨hs1, ht1, -⟩ := hsub c hc hcζ
        refine ⟨_, _, (add_lt_add_iff_left X0).2 ((mul_lt_mul_iff_right₀ (leWe_pos E)).2 (hlim.succ_lt hcζ)), ?_,
          hs1, ht1⟩
        refine (add_lt_add_iff_left Xh0).2 ?_
        rw [rqTh_succ hl hX hc, hcz, mul_add_one]; exact Ordinal.lt_mul_div_add u hOk0

/-- **`EE_j` is a code with `Θ(EE_j) < Ω₁`** at a base `β` of `X₀ + W^{E+1}` with a reading. -/
theorem rwEEc_code {X0 Xh0 β Â : Ordinal.{0}} (hoff : RvOff S l β X0 Xh0) (hd : leWe (E + 1) ∣ X0)
    (hG3 : X0 + leWe (E + 1) + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)))
    (hG : Xh0 + leOe (gxTh (upsilon l) (ldAtR S l) E + 1) + Om 1 < S.psi 0 (Om (1 + 1)))
    (hEX : ∃ j, E < rwEX S X0 β j)
    (hb : RoBaseE S l (X0 + leWe (E + 1)) 0 β) (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hbase : gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1)) :
    ∀ j, GxCl (upsilon l) (ldAtR S l) (rvEE S X0 β E j) ∧
      gxTh (upsilon l) (ldAtR S l) (rvEE S X0 β E j) < Om 1 := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have heH : E ∈ cdHull S l := (ldHull_iff hl hX hEW).2 hE
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  obtain ⟨-, hX0H, hX0m, -, -, -⟩ := rvOff_data hoff
  have hb' := hb
  obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
  rw [add_zero] at hβd hβA hβown
  have hEo : E < S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) := by
    obtain ⟨j, hj⟩ := hEX; exact rwEX_gt j E hj
  have hk0 : leWe E ≠ 0 := (leWe_pos E).ne'
  intro j
  induction j with
  | zero =>
    refine ⟨GxCl.om, ?_⟩
    change gxTh (upsilon l) (ldAtR S l) (Om 1) < Om 1
    rw [gxTh_Om1 hρSC hρ1 hAt]; exact hρ1
  | succ j IHj =>
    obtain ⟨hc, hΘ⟩ := IHj
    have hjW : rvEE S X0 β E j < Om (1 + 1) := rvEE_lt_Om2 j
    have hjH : rvEE S X0 β E j ∈ cdHull S l := (ldHull_iff hl hX hjW).2 hc
    have hlt : β + leWe (X0 + leWe E * rvEE S X0 β E j) < β + leWe (X0 + leWe (E + 1)) :=
      (add_lt_add_iff_left β).2 (leWe_lt ((add_lt_add_iff_left X0).2 (rvWe_lt_succ hjW)))
    have hat : rvEE S X0 β E (j + 1) ∈ ldAtR S l :=
      ⟨β + leWe (X0 + leWe E * rvEE S X0 β E j),
        CSet.add_mem hβH (leWe_mem (CSet.add_mem hX0H (leMulWe_mem heH hjH))), hlt.trans hβA, rfl⟩
    refine ⟨GxCl.atom hat, ?_⟩
    have hj0 : rvEE S X0 β E j ≠ 0 := (rvEE_SC j).1.ne'
    have hoffj := rwFamC hl hX he1 hE hEW IH hoff hd hG3 hG hEX _ hc
      ⟨j + 1, rwEEc_lt_succ hβown hX0m hEo j⟩ hΘ
    obtain ⟨-, htj⟩ := rvOff_ne hoffj
      (fun h => (mul_ne_zero hk0 hj0) (le_antisymm (h ▸ le_add_self) zero_le))
    have hsb : RoBaseE S l (X0 + leWe E * rvEE S X0 β E j) 0 β :=
      roBaseE_shift hb' (by rw [add_zero]; exact (add_le_add_iff_left X0).2 (rvWe_lt_succ hjW).le) zero_le
    have e1 := htj β Â hsb le_rfl hÂ hbase
    have e2 : leTe S (X0 + leWe E * rvEE S X0 β E j + 0) β = rvEE S X0 β E (j + 1) := by
      rw [add_zero]; rfl
    rw [e2] at e1
    rw [e1]; exact psi_lt Low.InR_Om_one _

end Main

end Googology.Trans.PoR.InaccPsi.R2.Rw
