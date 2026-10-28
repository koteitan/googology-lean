import Googology.Trans.PoR.InaccPsi.R2.VkGam

/-!
# The level statement with no bound: offsets, own exponents of any level, the sequence `EE_j`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`,
`EE_j = Rv.rvEE S X₀ β E j` (`EE_0 = Ω₁`, `EE_{j+1} = T_{X₀ + W^E·EE_j}(β)`).

`Uj.UjOff`, `Uj.UjOwn`, `Uj.UjOwP`, `Uj.UjLev` without the bounds `Y₃`, `Y₂` and with the codes `Vk.VkA` above the
levels 2 (exponents) and 1 (images) in place of `Ug.UgC`.

* `VkOff` (**an offset**: `0`, or a shift `Vk.VkSh` with its top), `vkOff_of_rv`, `vkOff_mono`, `vkOff_data`,
  `vkOff_ne`, `vkOff_neh`;
* `VkOwnE` (**an own exponent of any level**), `vkOwnE_of_sc`, `vkOwnE_mono`, `VkOwP`, `VkLev` (**the level
  statement with no bound**: at every offset `X₀` with `W^E ∣ X₀` and `Ow b X₀`, `RvTop (X₀ + W^E) (X̂₀ + Ω^Ê) 0`);
* `vkE_le_base`, `vkEE_e_mem`, `vkEE_lt_succ`, `vkEE_mono`, `vkEE_sup` (`T_{X₀ + W^{e+1}}(β) = sup_j EE_j` for an
  own exponent `e` that is a code above the level 2, no bound), `vkEE_ge`, `vkEE_gtT`.

No new axiom.  New definitions: `VkOff`, `VkOwnE`, `VkOwP`, `VkLev`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj

variable {S : InaccSeq.{0}}

/-- **An offset (no bound)**: `0`, or a shift `VkSh` with its top. -/
def VkOff (S : InaccSeq.{0}) (l b X0 Xh0 : Ordinal.{0}) : Prop :=
  (X0 = 0 ∧ Xh0 = 0) ∨ (VkSh S l b X0 Xh0 ∧ RvTop S l b X0 Xh0 0)

/-- Every offset `Rv.RvOff` is an offset `VkOff`. -/
theorem vkOff_of_rv {l b X0 Xh0 : Ordinal.{0}} (h : RvOff S l b X0 Xh0) : VkOff S l b X0 Xh0 := by
  rcases h with h | ⟨hs, ht⟩
  · exact Or.inl h
  · exact Or.inr ⟨vkSh_of_rv hs, ht⟩

theorem vkOff_mono {l b b' X0 Xh0 : Ordinal.{0}} (hbb : b ≤ b') (h : VkOff S l b X0 Xh0) :
    VkOff S l b' X0 Xh0 := by
  rcases h with h | ⟨hs, ht⟩
  · exact Or.inl h
  · exact Or.inr ⟨vkSh_mono hs hbb, rvTop_mono hbb ht⟩

/-- The membership and the codes of an offset. -/
theorem vkOff_data {l b X0 Xh0 : Ordinal.{0}} (h : VkOff S l b X0 Xh0) :
    Om (1 + 1) ∣ X0 ∧ X0 ∈ cdHull S l ∧ X0 ∈ S.CSet X0 (S.psi (b + leWe X0) (Om (1 + 1))) ∧
      Xh0 ∈ S.CSet Xh0 (gxTh (upsilon l) (ldAtR S l) (S.psi (b + leWe X0) (Om (1 + 1)))) ∧
      (∀ Q, SC Q → S.psi (b + leWe X0) (Om (1 + 1)) ≤ Q → VkA (1 + 1) Q X0) ∧
      (∀ Q, SC Q → gxTh (upsilon l) (ldAtR S l) (S.psi (b + leWe X0) (Om (1 + 1))) ≤ Q → VkA 1 Q Xh0) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨hs, -⟩
  · exact ⟨dvd_zero _, CSet.zero_mem _ _, CSet.zero_mem _ _, CSet.zero_mem _ _,
      fun Q hQ _ => VkA.zero hQ.1, fun Q hQ _ => VkA.zero hQ.1⟩
  · exact ⟨hs.dvd, hs.hull, hs.mem, hs.memh, hs.cl, hs.clh⟩

theorem vkOff_ne {l b X0 Xh0 : Ordinal.{0}} (h : VkOff S l b X0 Xh0) (hne : X0 ≠ 0) :
    VkSh S l b X0 Xh0 ∧ RvTop S l b X0 Xh0 0 := by
  rcases h with ⟨rfl, -⟩ | h
  · exact absurd rfl hne
  · exact h

theorem vkOff_neh {l b X0 Xh0 : Ordinal.{0}} (h : VkOff S l b X0 Xh0) (hne : Xh0 ≠ 0) :
    VkSh S l b X0 Xh0 ∧ RvTop S l b X0 Xh0 0 := by
  rcases h with ⟨-, rfl⟩ | h
  · exact absurd rfl hne
  · exact h

/-- **An own exponent `E` (any level, no bound) of `W^E` over the offset `X₀` at the base `b`, with the
image `Ê`**: `Sc.ScOwn` with relative memberships and the codes above the levels 2 and 1. -/
structure VkOwnE (S : InaccSeq.{0}) (l b X0 E Eh : Ordinal.{0}) : Prop where
  one : 1 ≤ E
  hull : E ∈ cdHull S l
  mem : E ∈ S.CSet E (S.psi (b + leWe (X0 + leWe E)) (Om (1 + 1)))
  memh : Eh ∈ S.CSet Eh (gxTh (upsilon l) (ldAtR S l) (S.psi (b + leWe (X0 + leWe E)) (Om (1 + 1))))
  cl : ∀ Q, SC Q → S.psi (b + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ Q → VkA (1 + 1) Q E
  clh : ∀ Q, SC Q → gxTh (upsilon l) (ldAtR S l) (S.psi (b + leWe (X0 + leWe E)) (Om (1 + 1))) ≤ Q →
    VkA 1 Q Eh

/-- Every `Sc.ScOwn` is a `VkOwnE`. -/
theorem vkOwnE_of_sc {l b X0 E Eh : Ordinal.{0}} (h : ScOwn S l b X0 E Eh) : VkOwnE S l b X0 E Eh :=
  ⟨h.one, h.hull, CSet_mono zero_le le_rfl h.mem, CSet_mono zero_le le_rfl h.memh,
    fun Q hQ hY => vkA_of_le hQ.1 (h.cl Q hQ hY),
    fun Q hQ hY => vkA_of_le hQ.1 (h.clh Q hQ hY)⟩

/-- An own exponent stays own at a larger base and a larger offset. -/
theorem vkOwnE_mono {l b β X0 X0' E Eh : Ordinal.{0}} (h : VkOwnE S l b X0 E Eh) (hb : b ≤ β) (hX : X0 ≤ X0') :
    VkOwnE S l β X0' E Eh := by
  have hle := scTop_mono (S := S) hb hX (le_refl E)
  exact ⟨h.one, h.hull, CSet_mono le_rfl hle h.mem, CSet_mono le_rfl (gxTh_mono hle) h.memh,
    fun Q hQ hY => h.cl Q hQ (hle.trans hY), fun Q hQ hY => h.clh Q hQ ((gxTh_mono hle).trans hY)⟩

/-- **An own predicate with its data**. -/
structure VkOwP (S : InaccSeq.{0}) (l : Ordinal.{0}) (Ow : Ordinal.{0} → Ordinal.{0} → Prop) (E Eh : Ordinal.{0}) :
    Prop where
  dat : ∀ b X0, Ow b X0 → VkOwnE S l b X0 E Eh
  mono : ∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0'

/-- **The level statement with no bound** at the exponent `E` with the image `Ê` and the own predicate `Ow`. -/
def VkLev (S : InaccSeq.{0}) (l : Ordinal.{0}) (Ow : Ordinal.{0} → Ordinal.{0} → Prop) (E Eh : Ordinal.{0}) :
    Prop :=
  ∀ b X0 Xh0, VkOff S l b X0 Xh0 → leWe E ∣ X0 → Ow b X0 →
    RvTop S l b (X0 + leWe E) (Xh0 + leOe Eh) 0

/-- `e ≤ β + W^{X₀ + W^e·x}` for `x ≥ 1`. -/
theorem vkE_le_base (X0 e β x : Ordinal.{0}) (hx : 1 ≤ x) : e ≤ β + leWe (X0 + leWe e * x) :=
  (ujLe_We e).trans ((Ordinal.le_mul_left _ (Order.one_le_iff_pos.1 hx)).trans
    (le_add_self.trans ((ujLe_We _).trans le_add_self)))

section Seq

variable {X0 β e : Ordinal.{0}}

variable (hβown : ∀ d, d ≤ leWe (X0 + leWe (e + 1)) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
  (hX0m : X0 ∈ S.CSet X0 (S.psi (β + leWe X0) (Om (1 + 1))))
  (hem : e ∈ S.CSet e (S.psi (β + leWe (X0 + leWe e)) (Om (1 + 1))))

include hem in
theorem vkEE_e_mem {x a : Ordinal.{0}} (ha : e ≤ a) (hx : 1 ≤ x) :
    e ∈ S.CSet a (S.psi (β + leWe (X0 + leWe e * x)) (Om (1 + 1))) := by
  refine CSet_mono ha ?_ hem
  refine (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono
    ((add_le_add_iff_left X0).2 ?_)))).1
  calc leWe e = leWe e * 1 := (mul_one _).symm
    _ ≤ leWe e * x := leMulWe_mono hx

include hβown hX0m hem

theorem vkEE_lt_succ : ∀ j, rvEE S X0 β e j < rvEE S X0 β e (j + 1)
  | 0 => (psiS_bounds (S := S) _ 1).1
  | j + 1 => by
    have IH := vkEE_lt_succ j
    have hle : rvEE S X0 β e (j + 1) ≤ rvEE S X0 β e (j + 2) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
        (leWe_mono ((add_le_add_iff_left X0).2 (leMulWe_mono IH.le))))).1
    refine psi_lt_psi_of_mem (InR_Om_succ 1)
      ((add_lt_add_iff_left β).2 (leWe_lt ((add_lt_add_iff_left X0).2 (leMulWe_lt IH)))) ?_
    have hX0 : X0 ∈ S.CSet (β + leWe (X0 + leWe e * rvEE S X0 β e (j + 1)))
        (S.psi (β + leWe (X0 + leWe e * rvEE S X0 β e (j + 1))) (Om (1 + 1))) :=
      CSet_mono (ujX_le_base X0 _ β) (psi_mono (S := S) (InR_Om_succ 1)
        ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1 hX0m
    refine CSet.add_mem (hβown _ (leWe_mono ((add_le_add_iff_left X0).2 (rvWe_lt_succ (rvEE_lt_Om2 _)).le)))
      (leWe_mem (CSet.add_mem hX0 (leMulWe_mem (vkEE_e_mem hem (vkE_le_base X0 e β _ (rvEE_one_le _)) (rvEE_one_le _))
        (CSet.of_lt (IH.trans_le hle)))))

theorem vkEE_mono {j j' : ℕ} (h : j ≤ j') : rvEE S X0 β e j ≤ rvEE S X0 β e j' :=
  (strictMono_nat_of_lt_succ (fun i => vkEE_lt_succ hβown hX0m hem i)).monotone h

/-- **`T_{X₀ + W^{e+1}}(β) = sup_j EE_j`** for an own exponent `e` of any level. -/
theorem vkEE_sup (hecl : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe e)) (Om (1 + 1)) ≤ Q → VkA (1 + 1) Q e)
    (hβd : leWe (X0 + leWe (e + 1)) ∣ β)
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → VkA (1 + 1) Q X0)
    {x : Ordinal.{0}} (hx : x < leTe S (X0 + leWe (e + 1)) β) : ∃ j, x < rvEE S X0 β e j := by
  have hbdd : BddAbove (Set.range (rvEE S X0 β e)) := Ordinal.bddAbove_of_small
  have hlt : ∀ y, y < ⨆ j, rvEE S X0 β e j ↔ ∃ j, y < rvEE S X0 β e j := fun y => lt_ciSup_iff hbdd
  have hKQ : ∀ j, rvEE S X0 β e j < ⨆ j, rvEE S X0 β e j :=
    fun j => (hlt _).2 ⟨j + 1, vkEE_lt_succ hβown hX0m hem j⟩
  have hΩQ : Om (1 : Ordinal.{0}) < ⨆ j, rvEE S X0 β e j := hKQ 0
  have hQSC : SC (⨆ j, rvEE S X0 β e j) := by
    refine ⟨(Om_pos one_ne_zero).trans hΩQ, fun x hx y hy => ?_⟩
    obtain ⟨i, hi⟩ := (hlt _).1 hx
    obtain ⟨j, hj⟩ := (hlt _).1 hy
    have hi' := hi.trans_le (vkEE_mono hβown hX0m hem (le_max_left i j))
    have hj' := hj.trans_le (vkEE_mono hβown hX0m hem (le_max_right i j))
    exact ((rvEE_SC (max i j)).2 _ hi' _ hj').trans (hKQ _)
  set Q := ⨆ j, rvEE S X0 β e j with hQ
  have h2 : (1 + 1 : Ordinal.{0}) ≠ 0 := by rw [one_add_one_eq_two]; exact two_ne_zero
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hX1 : S.psi (β + leWe X0) (Om (1 + 1)) < rvEE S X0 β e 1 := by
    refine psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left β).2
      (leWe_lt (lt_add_of_pos_right X0 (mul_pos (leWe_pos e) (Om_pos one_ne_zero))))) ?_
    exact CSet.add_mem (hβown _ (leWe_mono ((add_le_add_iff_left X0).2 (rvWe_lt_succ gg_Om1_lt_Om2).le)))
      (leWe_mem (CSet_mono (ujX_le_base X0 _ β) (psi_mono (S := S) (InR_Om_succ 1)
        ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1 hX0m))
  have hβ1 : S.psi β (Om (1 + 1)) < rvEE S X0 β e 1 :=
    lt_of_le_of_lt (psi_mono (S := S) (InR_Om_succ 1) le_self_add).1 hX1
  have hYe : S.psi (β + leWe (X0 + leWe e)) (Om (1 + 1)) ≤ Q := by
    refine le_of_lt (lt_of_le_of_lt ?_ (hKQ 1))
    refine (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono
      ((add_le_add_iff_left X0).2 ?_)))).1
    calc leWe e = leWe e * 1 := (mul_one _).symm
      _ ≤ leWe e * Om 1 := leMulWe_mono (Order.one_le_iff_pos.2 (Om_pos one_ne_zero))
  have hFQ : leTe S (X0 + leWe (e + 1)) β ≤ Q := by
    refine vkPsi2_le hQSC hΩQ fun x hx hc => ?_
    rcases le_or_gt x β with hxβ | hxβ
    · exact ((psi_mono (S := S) (InR_Om_succ 1) hxβ).1.trans_lt hβ1).trans (hKQ 1)
    obtain ⟨x', rfl⟩ := exists_add_of_le hxβ.le
    have hx'W : x' < leWe (X0 + leWe (e + 1)) := (add_lt_add_iff_left β).1 hx
    rcases eq_or_ne x' 0 with rfl | hx0
    · rw [add_zero]; exact (hβ1.trans (hKQ 1))
    have hc2 := vkA_mod hQSC (Om (1 + 1) * (X0 + leWe (e + 1))) hc
    change VkA (1 + 1) Q ((β + x') % leWe (X0 + leWe (e + 1))) at hc2
    have hm : (β + x') % leWe (X0 + leWe (e + 1)) = x' := by
      obtain ⟨q, hq⟩ := hβd
      rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hx'W]
    rw [hm] at hc2
    obtain ⟨-, hlog⟩ := vkDec hQSC x' hc2
    have hla : log ω x' < Om (1 + 1) * X0 + leWe (1 + e + 1) := by
      rw [show (1 : Ordinal.{0}) + e + 1 = 1 + (e + 1) from add_assoc _ _ _, ← rvWe_mul (e + 1), ← mul_add]
      exact (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hx0).trans_lt hx'W)
    have hx'lt := lt_opow_succ_log_self one_lt_omega0 x'
    rw [Order.succ_eq_add_one] at hx'lt
    rcases lt_or_ge (log ω x') (Om (1 + 1) * X0) with h1 | h1
    · have hxX : x' < leWe X0 := hx'lt.trans_le (opow_le_opow_right omega0_pos (Order.add_one_le_of_lt h1))
      exact ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hxX.le)).1.trans_lt hX1).trans
        (hKQ 1)
    have hXC : VkA (1 + 1) Q (Om (1 + 1) * X0) :=
      vkA_mulK hQSC h2 X0 (hX0cl Q hQSC (hX1.trans (hKQ 1)).le)
    have hu := (vkDec hQSC (log ω x') hlog).1 _ hXC h1
    have hdec : Om (1 + 1) * X0 + (log ω x' - Om (1 + 1) * X0) = log ω x' := Ordinal.add_sub_cancel_of_le h1
    have hu2 : log ω x' - Om (1 + 1) * X0 < ω ^ (Om (1 + 1) * (1 + e) + Om (1 + 1)) := by
      rw [← mul_add_one]; change _ < leWe (1 + e + 1)
      have : Om (1 + 1) * X0 + (log ω x' - Om (1 + 1) * X0) < Om (1 + 1) * X0 + leWe (1 + e + 1) := by
        rw [hdec]; exact hla
      exact (add_lt_add_iff_left _).1 this
    have h1e : VkA (1 + 1) Q (1 + e) :=
      VkA.add (VkA.small ((one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1)).trans hΩQ))
        (hecl Q hQSC hYe)
    have hb := vkA_boundY hQSC h2 h1e _ hu hu2
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

theorem vkEE_ge (hecl : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe e)) (Om (1 + 1)) ≤ Q → VkA (1 + 1) Q e)
    (hβd : leWe (X0 + leWe (e + 1)) ∣ β)
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → VkA (1 + 1) Q X0)
    {x : Ordinal.{0}} (hx : leTe S (X0 + leWe (e + 1)) β ≤ x) :
    leTe S (X0 + leWe (e + 1)) β ≤ S.psi (β + leWe (X0 + leWe e * x)) (Om (1 + 1)) := by
  by_contra h
  push Not at h
  obtain ⟨j, hj⟩ := vkEE_sup hβown hX0m hem hecl hβd hX0cl h
  have h1 : rvEE S X0 β e (j + 1) ≤ S.psi (β + leWe (X0 + leWe e * x)) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
      (leWe_mono ((add_le_add_iff_left X0).2 (leMulWe_mono ((rvEE_le_top j).trans hx)))))).1
  exact absurd (hj.trans_le ((vkEE_lt_succ hβown hX0m hem j).le.trans h1)) (lt_irrefl _)

theorem vkEE_gtT (hecl : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe e)) (Om (1 + 1)) ≤ Q → VkA (1 + 1) Q e)
    (hβd : leWe (X0 + leWe (e + 1)) ∣ β)
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → VkA (1 + 1) Q X0)
    {x : Ordinal.{0}} (hx : x < leTe S (X0 + leWe (e + 1)) β) :
    x < S.psi (β + leWe (X0 + leWe e * x)) (Om (1 + 1)) := by
  obtain ⟨j, hj⟩ := vkEE_sup hβown hX0m hem hecl hβd hX0cl hx
  exact rvEE_gt j x hj

end Seq

end Googology.Trans.PoR.InaccPsi.R2.Vk
