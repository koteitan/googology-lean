import Googology.Trans.PoR.InaccPsi.R2.ZiChain

/-!
# THE TOP ATOM AT THE EXPONENT `X + Ω₃` IS THE SUPREMUM OF THE TOP ATOMS AT THE ψ₃-ITERATES

`W^x = leWe x = ω^{Ω₂·x}`, `ψ₂ = ψ_{Ω₂}`, `ψ₃ = ψ_{Ω₃}`.  The ψ₃-iterates over `β` and `X`:
`u_0 = 0`, `u_{m+1} = ψ₃(β + W^{X+u_m})` (`ziU S X β m`).

* `ziU_mono` (the iterates increase), `ziU_lt_Om3`,
* `ziR3U` (a member of the stage `Cl(β + W^{X+u_k}, ψ₂(β + W^{X+u_k}))` below `β + W^{X+Ω₃}` is below
  `β + W^{X+u_{k+1}}`: its `Ω₃`-part is a member of `Cl(·, ψ₃(·)) ∩ Ω₃`),
* `ziKeyU` (every member of `Cl(β + W^{X+Ω₃}, sup_m ψ₂(β + W^{X+u_m}))` lies in a stage),
* `ziPlat3` (**THE LEVEL-3 PLATEAU**: `ψ₂(β + W^{X+Ω₃}) = sup_m ψ₂(β + W^{X+u_m})`, for EVERY `β`, `X`),
* `ziU_one_Om3` (at `β = 0`, `X = Ω₃`: `u_1 = Y₃`), `ziU_ge_Y3` (`u_m ≥ Y₃` for `m ≥ 1` there),
  `ziY3_gt_chain` (`Y₃ > Ω₂·ξ + e` for every `ξ, e < Ω₂`): so the top atom `ψ₂(W^{Ω₃·2})` at the exponent `E = Ω₃` of
  the shift `Ω₃` is the supremum of the top atoms at the exponents `E = u_m ∈ [Y₃, Ω₃)`, all beyond the chain
  `E = Ω₂·ξ + e` of `Zi.ziChain`.

No new axiom.  New definition: `ziU` (the ψ₃-iterates).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zi

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ug

variable {S : InaccSeq.{0}}

/-- The ψ₃-iterates `u_0 = 0`, `u_{m+1} = ψ₃(β + W^{X+u_m})`. -/
noncomputable def ziU (S : InaccSeq.{0}) (X β : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => 0
  | m + 1 => S.psi (β + leWe (X + ziU S X β m)) (Om (1 + 1 + 1))

theorem ziU_zero (X β : Ordinal.{0}) : ziU S X β 0 = 0 := rfl

theorem ziU_succ (X β : Ordinal.{0}) (m : ℕ) :
    ziU S X β (m + 1) = S.psi (β + leWe (X + ziU S X β m)) (Om (1 + 1 + 1)) := rfl

theorem ziInR3 : S.InR (Om (1 + 1 + 1 : Ordinal.{0})) := InR_Om_succ (1 + 1)

theorem ziSC3 : SC (Om (1 + 1 + 1 : Ordinal.{0})) := SC_Om (add_pos_of_right zero_lt_one _).ne'

theorem ziU_lt_Om3 (X β : Ordinal.{0}) : ∀ m, ziU S X β m < Om (1 + 1 + 1)
  | 0 => ziSC3.1
  | m + 1 => psi_lt ziInR3 _

theorem ziU_le_succ (X β : Ordinal.{0}) : ∀ m, ziU S X β m ≤ ziU S X β (m + 1)
  | 0 => zero_le
  | m + 1 => by
    rw [ziU_succ X β (m + 1), ziU_succ X β m]
    exact (psi_mono ziInR3 (add_le_add_right (leWe_mono ((add_le_add_iff_left X).2 (ziU_le_succ X β m))) β)).1

theorem ziU_mono (X β : Ordinal.{0}) : Monotone (ziU S X β) := monotone_nat_of_le_succ (ziU_le_succ X β)

/-- `Ω₂·Ω₃ = Ω₃`. -/
theorem ziOm2_mul_Om3 : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1 + 1) = Om (1 + 1 + 1) := by
  have h23 : Om (1 + 1 : Ordinal.{0}) < Om (1 + 1 + 1) := Om_lt_Om.2 (lt_add_one _)
  conv_lhs => rw [← gg_SC_eps ldOm2_SC, ← gg_SC_eps ziSC3]
  rw [← opow_add, isPrincipal_add_iff_add_left_eq_self.1 ziSC3.isPrincipal _ h23, gg_SC_eps ziSC3]

/-- `Ω₂ < ψ₃(x)` for every `x`. -/
theorem ziOm2_lt_psi3 (x : Ordinal.{0}) : Om (1 + 1 : Ordinal.{0}) < S.psi x (Om (1 + 1 + 1)) :=
  lt_psi_of_mem ziInR3 (mxOm2_mem _ _) (Om_lt_Om.2 (lt_add_one _))

/-- **A member of a stage below `β + W^{X+Ω₃}` is below the next stage's argument**: for
`y ∈ Cl(β + W^{X+u_k}, ψ₂(β + W^{X+u_k}))`, `y < β + W^{X+Ω₃}` gives `y < β + W^{X+u_{k+1}}`. -/
theorem ziR3U (X β : Ordinal.{0}) (k : ℕ) {y : Ordinal.{0}}
    (hy : y ∈ S.CSet (β + leWe (X + ziU S X β k)) (S.psi (β + leWe (X + ziU S X β k)) (Om (1 + 1))))
    (hlt : y < β + leWe (X + Om (1 + 1 + 1))) : y < β + leWe (X + ziU S X β (k + 1)) := by
  set a := β + leWe (X + ziU S X β k) with ha
  rcases lt_or_ge y β with h1 | h1
  · exact h1.trans_le le_self_add
  have hz : y - β ∈ S.CSet a (S.psi a (Om (1 + 1))) := Ta.taSub_mem y hy β
  have hzl : y - β < leWe (X + Om (1 + 1 + 1)) := Ry.rySub_lt h1 hlt
  have e1 : y = β + (y - β) := (Ordinal.add_sub_cancel_of_le h1).symm
  rw [e1]
  refine (add_lt_add_iff_left β).2 ?_
  set z := y - β with hzdef
  rcases eq_or_ne z 0 with hz0 | hz0
  · rw [hz0]; exact leWe_pos _
  set L := log ω z with hLdef
  have hLmem : L ∈ S.CSet a (S.psi a (Om (1 + 1))) := leLog_mem hz
  have hzl' : z < ω ^ (Om (1 + 1) * X + Om (1 + 1 + 1)) := by
    have h := hzl; unfold leWe at h; rwa [mul_add, ziOm2_mul_Om3] at h
  have hLlt : L < Om (1 + 1) * X + Om (1 + 1 + 1) := (lt_opow_iff_log_lt one_lt_omega0 hz0).1 hzl'
  unfold leWe
  refine (lt_opow_iff_log_lt one_lt_omega0 hz0).2 ?_
  rw [mul_add]
  rcases lt_or_ge L (Om (1 + 1) * X) with h2 | h2
  · exact h2.trans_le le_self_add
  have hq : L - Om (1 + 1) * X < Om (1 + 1 + 1) := Ry.rySub_lt h2 hLlt
  have hqm : L - Om (1 + 1) * X ∈ S.CSet a (S.psi a (Om (1 + 1 + 1))) :=
    CSet_mono le_rfl ((psi_lt (InR_Om_succ 1) a).le.trans (ziOm2_lt_psi3 a).le) (Ta.taSub_mem L hLmem _)
  have hqu : L - Om (1 + 1) * X < ziU S X β (k + 1) := by
    rw [ziU_succ]; exact lt_psi_of_mem ziInR3 hqm hq
  have hu : ziU S X β (k + 1) ≤ Om (1 + 1) * ziU S X β (k + 1) := Ordinal.le_mul_right _ ldOm2_SC.1
  have e2 : L = Om (1 + 1) * X + (L - Om (1 + 1) * X) := (Ordinal.add_sub_cancel_of_le h2).symm
  show L < _
  rw [e2]
  exact (add_lt_add_iff_left _).2 (hqu.trans_le hu)

theorem ziStgU_mono (X β : Ordinal.{0}) {i j : ℕ} (h : i ≤ j) :
    S.CSet (β + leWe (X + ziU S X β i)) (S.psi (β + leWe (X + ziU S X β i)) (Om (1 + 1))) ⊆
      S.CSet (β + leWe (X + ziU S X β j)) (S.psi (β + leWe (X + ziU S X β j)) (Om (1 + 1))) :=
  (psi_mono (InR_Om_succ 1) (add_le_add_right (leWe_mono ((add_le_add_iff_left X).2 (ziU_mono X β h))) β)).2

theorem ziU_bdd (X β : Ordinal.{0}) :
    BddAbove (range fun m : ℕ => S.psi (β + leWe (X + ziU S X β m)) (Om (1 + 1))) :=
  ⟨Om (1 + 1), by rintro _ ⟨m, rfl⟩; exact (psi_lt (InR_Om_succ 1) _).le⟩

/-- **Every member of `Cl(β + W^{X+Ω₃}, sup_m ψ₂(β + W^{X+u_m}))` lies in a stage.** -/
theorem ziKeyU (X β : Ordinal.{0}) :
    ∀ y ∈ S.CSet (β + leWe (X + Om (1 + 1 + 1))) (⨆ m : ℕ, S.psi (β + leWe (X + ziU S X β m)) (Om (1 + 1))),
      ∃ k, y ∈ S.CSet (β + leWe (X + ziU S X β k)) (S.psi (β + leWe (X + ziU S X β k)) (Om (1 + 1))) := by
  intro y hy
  induction hy with
  | small h =>
    obtain ⟨n, hn⟩ := (lt_ciSup_iff (ziU_bdd X β)).1 h
    exact ⟨n, CSet.of_lt hn⟩
  | zero => exact ⟨0, CSet.zero_mem _ _⟩
  | inacc n => exact ⟨0, Clos.inacc n⟩
  | inaccW => exact ⟨0, Clos.inaccW⟩
  | add _ _ ihp ihq =>
    obtain ⟨i, hi⟩ := ihp
    obtain ⟨j, hj⟩ := ihq
    exact ⟨max i j, CSet.add_mem (ziStgU_mono X β (le_max_left i j) hi) (ziStgU_mono X β (le_max_right i j) hj)⟩
  | phi _ _ ihp ihq =>
    obtain ⟨i, hi⟩ := ihp
    obtain ⟨j, hj⟩ := ihq
    exact ⟨max i j, Clos.phi (ziStgU_mono X β (le_max_left i j) hi) (ziStgU_mono X β (le_max_right i j) hj)⟩
  | om _ ih =>
    obtain ⟨i, hi⟩ := ih
    exact ⟨i, CSet.Om_mem hi⟩
  | @coll π e hπ _ _ ihπ ihe =>
    obtain ⟨i, hi⟩ := ihπ
    obtain ⟨k, hk⟩ := ihe
    have hlt : e.1 < β + leWe (X + ziU S X β (k + 1)) := ziR3U X β k hk e.2
    set N := max (k + 1) i with hN
    have hltN : e.1 < β + leWe (X + ziU S X β N) :=
      hlt.trans_le (add_le_add_right (leWe_mono ((add_le_add_iff_left X).2
        (ziU_mono X β (le_max_left (k + 1) i)))) β)
    have heN := ziStgU_mono X β ((Nat.le_succ k).trans (le_max_left (k + 1) i)) hk
    have hπN := ziStgU_mono X β (le_max_right (k + 1) i) hi
    exact ⟨N, Clos.coll (e := ⟨e.1, hltN⟩) hπ hπN heN⟩

/-- **THE LEVEL-3 PLATEAU**: `ψ₂(β + W^{X+Ω₃}) = sup_m ψ₂(β + W^{X+u_m})`, `u_{m+1} = ψ₃(β + W^{X+u_m})`
(every `β`, every `X`). -/
theorem ziPlat3 (X β : Ordinal.{0}) :
    S.psi (β + leWe (X + Om (1 + 1 + 1))) (Om (1 + 1)) =
      ⨆ m : ℕ, S.psi (β + leWe (X + ziU S X β m)) (Om (1 + 1)) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  refine le_antisymm (psi_le_of_good (mxOm2_mem _ _) fun y hy hy2 => ?_) (ciSup_le fun m => ?_)
  · obtain ⟨n, hn⟩ := ziKeyU X β y hy
    exact (lt_psi_of_mem hκ2 hn hy2).trans_le (le_ciSup (ziU_bdd X β) n)
  · exact (psi_mono hκ2 (add_le_add_right (leWe_mono ((add_le_add_iff_left X).2 (ziU_lt_Om3 X β m).le)) β)).1

/-- At `β = 0`, `X = Ω₃`: `u_1 = ψ₃(W^{Ω₃}) = ψ₃(Ω₃) = Y₃`. -/
theorem ziU_one_Om3 : ziU S (Om (1 + 1 + 1)) 0 1 = ugY S := by
  rw [ziU_succ, ziU_zero, add_zero, zero_add, Vn.vnWe_Om3]; rfl

/-- At `β = 0`, `X = Ω₃`: `Y₃ ≤ u_m` for every `m ≥ 1`. -/
theorem ziU_ge_Y3 (m : ℕ) : ugY S ≤ ziU S (Om (1 + 1 + 1)) 0 (m + 1) := by
  rw [← ziU_one_Om3]; exact ziU_mono _ _ (Nat.succ_le_succ zero_le)

/-- `Ω₂·ξ + e < Y₃` for every `ξ, e < Ω₂` (the chain `Ω_{k+3} + Ω₂·ξ + e` of `Zi.ziChain` stays below `Ω_{k+3} + Y₃`). -/
theorem ziY3_gt_chain {ξ e : Ordinal.{0}} (hξ : ξ < Om (1 + 1)) (he : e < Om (1 + 1)) :
    Om (1 + 1) * ξ + e < ugY S := by
  have hY := Uq.uqY_SC (S := S)
  have h2Y : Om (1 + 1 : Ordinal.{0}) < ugY S := Uq.uqW_lt_Y
  have hm : Om (1 + 1) * ξ < ugY S := by
    refine (mul_lt_mul_of_pos_left hξ ldOm2_SC.1).trans ?_
    have h22 : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) = veblen 0 (Om (1 + 1) + Om (1 + 1)) := by
      rw [veblen_zero_apply, opow_add, gg_SC_eps ldOm2_SC]
    rw [h22]; exact hY.2 0 hY.1 _ (hY.isPrincipal h2Y h2Y)
  exact hY.isPrincipal hm (he.trans h2Y)

/-- **REFUTE-FIRST record of (b) at `E = Ω₃`** (`k = 0`, `β = 0`): the top atom `ψ₂(W^{Ω₃+Ω₃})` is the supremum of
the top atoms `ψ₂(W^{Ω₃+u_m})`, whose exponents `u_m` (`m ≥ 1`) lie in `[Y₃, Ω₃)`, above every exponent
`Ω₂·ξ + e` (`ξ, e < Ω₂`) of the chain. -/
theorem ziTestOm3 :
    S.psi (leWe (Om (1 + 1 + 1) + Om (1 + 1 + 1))) (Om (1 + 1)) =
        ⨆ m : ℕ, S.psi (leWe (Om (1 + 1 + 1) + ziU S (Om (1 + 1 + 1)) 0 m)) (Om (1 + 1)) ∧
      (∀ m : ℕ, ugY S ≤ ziU S (Om (1 + 1 + 1)) 0 (m + 1) ∧ ziU S (Om (1 + 1 + 1)) 0 (m + 1) < Om (1 + 1 + 1)) ∧
      ∀ ξ e : Ordinal.{0}, ξ < Om (1 + 1) → e < Om (1 + 1) → Om (1 + 1) * ξ + e < ugY S := by
  refine ⟨?_, fun m => ⟨ziU_ge_Y3 m, ziU_lt_Om3 _ _ _⟩, fun ξ e hξ he => ziY3_gt_chain hξ he⟩
  have h := ziPlat3 (S := S) (Om (1 + 1 + 1)) 0
  simp only [zero_add] at h
  exact h

end Googology.Trans.PoR.InaccPsi.R2.Zi
