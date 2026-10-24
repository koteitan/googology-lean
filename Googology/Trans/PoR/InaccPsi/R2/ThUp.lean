import Googology.Trans.PoR.InaccPsi.R2.TeAtom

/-!
# An upper bound for the reading: `Θ_λ(m) ≤ ψ_{Ω₁}(A_{η_λ} + m)`, so `Θ_{L(ξ)}(P') ≤ L(ξ+1)`

`Θ_λ(m) = otp(Cl(A, ρ_λ) ∩ m)` (`Cd.cdTheta`), `A = A_{η_λ}`, `ρ_λ = ψ_{Ω₁}(A)`, `P' = ψ_{Ω₂}(Ω_ω·2)`,
`L(ξ) = ψ_{Ω₁}(Ω_ω·2 + P'·ξ)`.

* `thOtp_le_of_map` (**an order type is at most every strictly increasing bound**: if `f c < f d` for every
  `c ∈ C` and `c < d`, then `otp(C ∩ m) ≤ f(m)`);
* `thOtp_le_psi` (**`otp(Cl(A, ψ_{Ω₁}(A)) ∩ m) ≤ ψ_{Ω₁}(A + m)`** when `A ∈ Cl(A, ψ_{Ω₁}(A))`: the map
  `c ↦ ψ_{Ω₁}(A + c)` is strictly increasing on the hull, since `A + c` lies in `Cl(A + d, ψ_{Ω₁}(A + d))`);
* `thTheta_le` (**`Θ_λ(m) ≤ ψ_{Ω₁}(A_{η_λ} + m)`** at every named restart whose `A_{η_λ}` is in its own hull);
* `thA_L` (`A_{Ω_ω + P'·ξ} = Ω_ω·2 + P'·ξ`), `thA_L_mem` (`Ω_ω·2 + P'·ξ` lies in its own hull for `ξ < ω` and
  `ξ = ω`);
* `thTheta_Lk`, `thTheta_Lw` (**`Θ_{L(k)}(P') ≤ L(k+1)`, `Θ_{L(ω)}(P') ≤ L(ω+1)`**, no hypothesis),
  `thTheta_Lw_succ` (**`Θ_{L(ω)}(P'+1) = Θ_{L(ω)}(P') + 1`**: `P'` is a code of `L(ω)`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Th

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

open Classical in
/-- **An order type is at most every strictly increasing bound.** -/
theorem thOtp_le_of_map {C : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}}
    (hf : ∀ c ∈ C, ∀ d, c < d → f c < f d) : ∀ m, cdOtp C m ≤ f m := by
  intro m
  induction m using WellFoundedLT.induction with
  | ind m IH =>
  rw [cdOtp_eq]
  refine ciSup_le' fun c => ?_
  split_ifs with hc
  · exact Order.add_one_le_of_lt ((IH c.1 c.2).trans_lt (hf c.1 hc m c.2))
  · exact zero_le

/-- **`otp(Cl(A, ψ_{Ω₁}(A)) ∩ m) ≤ ψ_{Ω₁}(A + m)`** when `A ∈ Cl(A, ψ_{Ω₁}(A))`. -/
theorem thOtp_le_psi {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (m : Ordinal.{0}) :
    cdOtp (S.CSet A (S.psi A (Om 1))) m ≤ S.psi (A + m) (Om 1) := by
  refine thOtp_le_of_map (f := fun m => S.psi (A + m) (Om 1)) (fun c hc d hcd => ?_) m
  show S.psi (A + c) (Om 1) < S.psi (A + d) (Om 1)
  have hmono := (psi_mono (S := S) Low.InR_Om_one (le_self_add : A ≤ A + d)).2
  exact psi_lt_psi_of_mem Low.InR_Om_one ((add_lt_add_iff_left A).2 hcd)
    (CSet.add_mem (hmono hA) (hmono hc))

/-- **`Θ_λ(m) ≤ ψ_{Ω₁}(A_{η_λ} + m)`** at a named restart whose `A_{η_λ}` lies in its own hull. -/
theorem thTheta_le {l : Ordinal.{0}} (hpv : Nm.Pv S (cdEta S l) = upsilon l)
    (hA : ConjT.Aη S (cdEta S l) ∈ S.CSet (ConjT.Aη S (cdEta S l)) (upsilon l)) (m : Ordinal.{0}) :
    cdTheta S l m ≤ S.psi (ConjT.Aη S (cdEta S l) + m) (Om 1) := by
  have e : upsilon l = S.psi (ConjT.Aη S (cdEta S l)) (Om 1) := hpv.symm
  unfold cdTheta cdHull
  rw [e] at hA ⊢
  exact thOtp_le_psi hA m

/-- `A_{Ω_ω + P'·ξ} = Ω_ω·2 + P'·ξ`. -/
theorem thA_L (ξ : Ordinal.{0}) :
    ConjT.Aη S (Om ω + Nc.ncPp S * ξ) = Om ω + Om ω + Nc.ncPp S * ξ := by
  unfold ConjT.Aη
  rw [mul_add, Bt.th_mul_Om_omega, ← mul_assoc, Nc.ncTh_mul_Pp, add_assoc]

/-- `Ω_ω·2 + P'·ξ` lies in every hull `Cl(a, b)` with `Ω_ω·2 < a` once `P'·ξ` is built from `P'`. -/
theorem thA_mem_of {ξ a b : Ordinal.{0}} (hξ : Nc.ncPp S * ξ ∈ S.CSet a b) :
    Om ω + Om ω + Nc.ncPp S * ξ ∈ S.CSet a b :=
  CSet.add_mem (CSet.add_mem (ConjT.OmW_mem S a b) (ConjT.OmW_mem S a b)) hξ

/-- **`Ω_ω·2 + P'·k` lies in its own hull.** -/
theorem thA_L_mem (k : ℕ) :
    Om ω + Om ω + Nc.ncPp S * (k : Ordinal.{0}) ∈
      S.CSet (Om ω + Om ω + Nc.ncPp S * (k : Ordinal.{0}))
        (S.psi (Om ω + Om ω + Nc.ncPp S * (k : Ordinal.{0})) (Om 1)) := by
  refine thA_mem_of ?_
  rcases Nat.eq_zero_or_pos k with h0 | hk
  · subst h0; rw [Nat.cast_zero, mul_zero]; exact CSet.zero_mem _ _
  · have hlt : Om ω + Om ω < Om ω + Om ω + Nc.ncPp S * (k : Ordinal.{0}) :=
      lt_add_of_pos_right _ (mul_pos (Nc.ncPp_SC S).1 (by exact_mod_cast hk))
    exact ConjT.mul_nat_mem S (Lw.lw_Pp_mem hlt) k

/-- **`Ω_ω·2 + P'·ω` lies in its own hull.** -/
theorem thA_Lw_mem :
    Om ω + Om ω + Nc.ncPp S * ω ∈
      S.CSet (Om ω + Om ω + Nc.ncPp S * ω) (S.psi (Om ω + Om ω + Nc.ncPp S * ω) (Om 1)) := by
  refine thA_mem_of ?_
  have hlt : Om ω + Om ω < Om ω + Om ω + Nc.ncPp S * ω :=
    lt_add_of_pos_right _ (mul_pos (Nc.ncPp_SC S).1 omega0_pos)
  have hP := Lw.lw_Pp_mem (S := S) (b := S.psi (Om ω + Om ω + Nc.ncPp S * ω) (Om 1)) hlt
  have e : Nc.ncPp S * ω = ω ^ (Nc.ncPp S + 1) := by
    rw [opow_add, opow_one, Lw.lw_Pp_opow S]
  have := CSet.phi_mem (S := S) (CSet.zero_mem _ _) (CSet.succ_mem hP)
  rw [veblen_zero_apply, ← e] at this
  exact this

/-- The general form at a point `L(ξ)` with the name `Ω_ω + P'·ξ`. -/
theorem thTheta_L_gen {l ξ : Ordinal.{0}} (hl : upsilon l = Nc.ncL S ξ)
    (hη : cdEta S l = Om ω + Nc.ncPp S * ξ)
    (hA : Om ω + Om ω + Nc.ncPp S * ξ ∈
      S.CSet (Om ω + Om ω + Nc.ncPp S * ξ) (S.psi (Om ω + Om ω + Nc.ncPp S * ξ) (Om 1))) :
    cdTheta S l (Nc.ncPp S) ≤ Nc.ncL S (ξ + 1) := by
  have hpv : Nm.Pv S (cdEta S l) = upsilon l := by
    rw [hl, hη, Lw.lw_L_eq S]
  have hA' : ConjT.Aη S (cdEta S l) ∈ S.CSet (ConjT.Aη S (cdEta S l)) (upsilon l) := by
    rw [← hpv]; unfold Nm.Pv; rw [hη, thA_L]; exact hA
  have h := thTheta_le hpv hA' (Nc.ncPp S)
  rw [hη, thA_L] at h
  unfold Nc.ncL
  rw [mul_add_one, ← add_assoc]
  exact h

/-- **`Θ_{L(k)}(P') ≤ L(k+1)`** for every `k < ω`. -/
theorem thTheta_Lk (k : ℕ) :
    cdTheta S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncPp S) ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) := by
  have hl : upsilon (Nc.ncL S (k : Ordinal.{0})) = Nc.ncL S (k : Ordinal.{0}) := Te.teUps_L k
  have hη : cdEta S (Nc.ncL S (k : Ordinal.{0})) = Om ω + Nc.ncPp S * (k : Ordinal.{0}) := by
    cases k with
    | zero =>
      have h0 : upsilon (Nc.ncL S (0 : Ordinal.{0})) = Nc.ncL S 0 := by simpa using hl
      have := (cdCode_L0 h0).1
      simpa using this
    | succ n => exact cdEta_L n hl
  rw [Nat.cast_succ]
  exact thTheta_L_gen hl hη (thA_L_mem k)

/-- **`Θ_{L(ω)}(P') ≤ L(ω+1)`.** -/
theorem thTheta_Lw : cdTheta S (Nc.ncL S ω) (Nc.ncPp S) ≤ Nc.ncL S (ω + 1) :=
  thTheta_L_gen Rc.rcUps_Lw (cdEta_Lω Rc.rcUps_Lw) thA_Lw_mem

/-- **`P'` is a code of `L(ω)`**, so `Θ_{L(ω)}(P'+1) = Θ_{L(ω)}(P') + 1`. -/
theorem thPp_mem_Lw : Nc.ncPp S ∈ cdHull S (Nc.ncL S ω) := by
  unfold cdHull
  rw [cdEta_Lω Rc.rcUps_Lw, thA_L]
  exact Lw.lw_Pp_mem (lt_add_of_pos_right _ (mul_pos (Nc.ncPp_SC S).1 omega0_pos))

open Classical in
theorem thOtp_succ {C : Set Ordinal.{0}} {m : Ordinal.{0}} (hm : m ∈ C) :
    cdOtp C (m + 1) = cdOtp C m + 1 := by
  refine le_antisymm ?_ ?_
  · rw [cdOtp_eq C (m + 1)]
    refine ciSup_le' fun c => ?_
    split_ifs with hc
    · rcases (Order.lt_add_one_iff.1 (show c.1 < m + 1 from c.2)).lt_or_eq with h | h
      · exact (Order.add_one_le_of_lt (cdOtp_lt_of_mem hc h)).trans le_self_add
      · rw [h]
    · exact zero_le
  · exact Order.add_one_le_of_lt (cdOtp_lt_of_mem hm (lt_add_one m))

/-- **`Θ_{L(ω)}(P'+1) = Θ_{L(ω)}(P') + 1 ≤ L(ω+1) + 1`.** -/
theorem thTheta_Lw_succ :
    cdTheta S (Nc.ncL S ω) (Nc.ncPp S + 1) = cdTheta S (Nc.ncL S ω) (Nc.ncPp S) + 1 ∧
      cdTheta S (Nc.ncL S ω) (Nc.ncPp S + 1) ≤ Nc.ncL S (ω + 1) + 1 := by
  have e : cdTheta S (Nc.ncL S ω) (Nc.ncPp S + 1) = cdTheta S (Nc.ncL S ω) (Nc.ncPp S) + 1 :=
    thOtp_succ thPp_mem_Lw
  refine ⟨e, ?_⟩
  rw [e]
  exact add_le_add thTheta_Lw le_rfl

end Googology.Trans.PoR.InaccPsi.R2.Th
