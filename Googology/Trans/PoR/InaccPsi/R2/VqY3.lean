import Googology.Trans.PoR.InaccPsi.R2.VqLimSh

/-!
# The first top at a shift in `[Y₃, Ω₃)`: `RvTop λ b Y₃ Y₂ 0` at every base `b ≥ Ω₃`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `Y₃ = ψ_{Ω₃}(Ω₃)`, `Y₂ = ψ_{Ω₂}(Ω₂)`, `y_n`, `z_n` the
iterates of `ψ_{Ω₃}`, `ψ_{Ω₂}` from `0`.

* `vqSh_it` (**`(y_{n+1}, z_{n+1})` is a base-relative shift at every base**), `vqTop_it` (**its top
  `RvTop λ 0 y_{n+1} z_{n+1} 0`**, from the level statement `Uu.uuLSY` at `y_{n+1}`);
* `vqTopY3` (**`RvTop λ b Y₃ Y₂ 0` for every `b ≥ Ω₃`**: the limit rule `Vq.vqTopLimSh` over the members
  `y_{n+1}`; `(Y₃, Y₂)` is no `Vk.VkSh`, `Vq.vqNoVk_Y3`), `vqTopY3E` (every code exponent), `vqTopY3W` (the
  pull-back `RvTop λ b (Y₃ + Ω₂) (Y₂ + Ω₁) 0`);
* `vqBase_Om3` (`Ω₃` is a base of the shift `Y₃`: the top is not vacuous), `vqRead_Om3Y3` (**`Θ(ψ₂(Ω₃ + Y₃)) =
  ψ₁(A + 1 + Y₂ + Y₂)`**).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj Googology.Trans.PoR.InaccPsi.R2.Uq
  Googology.Trans.PoR.InaccPsi.R2.Uu Googology.Trans.PoR.InaccPsi.R2.Vk Googology.Trans.PoR.InaccPsi.R2.Vn
  Googology.Trans.PoR.InaccPsi.R2.Ua

variable {S : InaccSeq.{0}}

theorem vqY_SC (n : ℕ) : SC ((fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0) := by
  rw [Function.iterate_succ_apply']; exact SC_psi (InR_Om_succ (1 + 1)) _

theorem vqY_gt (n : ℕ) : Om (1 + 1) < (fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0 := by
  rw [Function.iterate_succ_apply']; exact ugOm2_lt_psi3 _

theorem vqZ_SC (n : ℕ) : SC ((fun x => S.psi x (Om (1 + 1)))^[n + 1] 0) := by
  rw [Function.iterate_succ_apply']; exact SC_psi (InR_Om_succ 1) _

theorem vqZ_gt (n : ℕ) : Om 1 < (fun x => S.psi x (Om (1 + 1)))^[n + 1] 0 := by
  rw [Function.iterate_succ_apply']; exact (psiS_bounds (S := S) _ 1).1

/-- **`(y_{n+1}, z_{n+1})` is a base-relative shift at every base.** -/
theorem vqSh_it (l A b : Ordinal.{0}) (n : ℕ) :
    VqSh S l A b ((fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0) ((fun x => S.psi x (Om (1 + 1)))^[n + 1] 0) where
  ne := (vqY_SC n).1.ne'
  dvd := by
    have h := leWe_dvd (Order.one_le_iff_pos.2 (vqY_SC (S := S) n).1)
    rwa [leWe_one, (uaWfix (gg_SC_eps (vqY_SC n)) (vqY_gt n)).2] at h
  hull := vnIt_mem (s := 1 + 1) vnOm3C (n + 1) _ _ (uuLtA (vnIt_lt (s := 1 + 1) vnOm3C (n + 1))).le
  mem := vnIt_mem (s := 1 + 1) vnOm3C (n + 1) _ _ ((ujLe_We _).trans le_add_self)
  memh := vnIt_mem (s := 1) (fun a c => mxOm2_mem a c) (n + 1) _ _ ((ujLe_Oe _).trans le_add_self)
  cl := fun _ _ _ => VkA.big (vqY_gt n).le (vqY_SC n)
  clh := fun _ _ _ => VkA.big (vqZ_gt n).le (vqZ_SC n)

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The top of the shift `(y_{n+1}, z_{n+1})` at the base `0`** (`Uu.uuLSY` at the level `y_{n+1}`). -/
theorem vqTop_it (n : ℕ) :
    RvTop S l 0 ((fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0) ((fun x => S.psi x (Om (1 + 1)))^[n + 1] 0) 0 := by
  have hay : (fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0 < ugY S := vnIt_lt (s := 1 + 1) vnOm3C (n + 1)
  have haA := uuLtA (l := l) hay
  have haH : (fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0 ∈ cdHull S l :=
    vnIt_mem (s := 1 + 1) vnOm3C (n + 1) _ _ haA.le
  have hΩa := vqY_gt (S := S) n
  have h1 : 1 ≤ (fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0 :=
    (gg_one_lt_of_SC ldOm2_SC).le.trans hΩa.le
  have hT := vnT_it (S := S) l (n + 1)
  have hTY : ugTh S l ((fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0) < ujY S 0 := by
    rw [ujY_zero]; exact uuTh_lt_Y2 hl hX haH hay
  have hlev := (uuLSY hl hX).lev _ haH h1 hay
  have h3 : 0 + leWe ((fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0) + Om (1 + 1) < ugY S := by
    rw [zero_add]; exact uqY_SC.isPrincipal (leWe_lt_SC uqY_SC uqW_lt_Y hay).1 uqW_lt_Y
  have h2 : 0 + leOe (ugTh S l ((fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0)) + Om 1 < ujY S 0 := by
    rw [zero_add]; exact uuY2_SC.isPrincipal (leOe_lt_SC uuY2_SC uuOm1_lt_Y2 hTY).1 uuOm1_lt_Y2
  have hle : (fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0 ≤
      0 + leWe (0 + leWe ((fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0)) := by
    rw [zero_add, zero_add]; exact (ujLe_We _).trans (ujLe_We _)
  have hown : uuOw S ((fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0) 0 0 :=
    Or.inr ⟨hΩa.le, fun Q hQ hQ' => uqC_mem hQ hQ' (vnIt_mem (s := 1 + 1) vnOm3C (n + 1) _ _ hle) hay⟩
  have hT3 := hlev 0 0 0 (Or.inl ⟨rfl, rfl⟩) (dvd_zero _) h3 h2 hown
  rw [zero_add, zero_add, hT, (uaWfix (gg_SC_eps (vqY_SC n)) hΩa).2,
    uaOe_fix (gg_SC_eps (vqZ_SC n)) (vqZ_gt n)] at hT3
  exact hT3

section Rst

variable {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hA hρ

/-- **THE TOP AT `Y₃`: `RvTop λ b Y₃ Y₂ 0` for every base `b ≥ Ω₃`.** -/
theorem vqTopY3 {b : Ordinal.{0}} (hb : Om (1 + 1 + 1) ≤ b) :
    RvTop S l b (ugY S) (S.psi (Om (1 + 1)) (Om (1 + 1))) 0 := by
  refine vqTopLimSh hl hX hA hρ (vqSh_Y3_rst hl hX hA hρ hb) (fun x _ hx => ?_) (fun z hz => ?_)
  · obtain ⟨m, hm⟩ := (lt_ciSup_iff (uuIt_bdd (S := S) (1 + 1))).1 (hx.trans_le (uuY_le_sup (S := S) uuThree_lt))
    exact ⟨_, _, (vnIt_lt (s := 1 + 1) vnOm3C (m + 1)).le, hm.trans (uuIt_lt (S := S) (1 + 1) m),
      vnIt_lt (s := 1) (fun a c => mxOm2_mem a c) (m + 1), vqSh_it l A b m,
      rvTop_mono zero_le (vqTop_it hl hX m)⟩
  · obtain ⟨m, hm⟩ := (lt_ciSup_iff (uuIt_bdd (S := S) 1)).1 (hz.trans_le (uuY_le_sup (S := S) uuTwo_lt))
    exact ⟨_, _, vnIt_lt (s := 1 + 1) vnOm3C (m + 1), hm.trans (uuIt_lt (S := S) 1 m), vqSh_it l A b m,
      rvTop_mono zero_le (vqTop_it hl hX m)⟩

/-- The top at `Y₃ + e` for every code `e < Ω₂`, at every base `b ≥ Ω₃`. -/
theorem vqTopY3E {b : Ordinal.{0}} (hb : Om (1 + 1 + 1) ≤ b) :
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) →
      RvTop S l b (ugY S) (S.psi (Om (1 + 1)) (Om (1 + 1))) e :=
  vqTopE (vqSh_Y3_rst hl hX hA hρ hb) hl hX hA hρ (vqTopY3 hl hX hA hρ hb)

/-- The pull-back: `RvTop λ b (Y₃ + Ω₂) (Y₂ + Ω₁) 0` at every base `b ≥ Ω₃`. -/
theorem vqTopY3W {b : Ordinal.{0}} (hb : Om (1 + 1 + 1) ≤ b) :
    RvTop S l b (ugY S + Om (1 + 1)) (S.psi (Om (1 + 1)) (Om (1 + 1)) + Om 1) 0 :=
  vqTopW (vqSh_Y3_rst hl hX hA hρ hb) hl hX hA hρ (vqTopY3E hl hX hA hρ hb)

end Rst

end Main

theorem vqWeY3 : leWe (ugY S) = ugY S := (uaWfix (gg_SC_eps uqY_SC) uqW_lt_Y).2

/-- **`Ω₃` is a base of the shift `Y₃`** (exponent `0`). -/
theorem vqBase_Om3 (l : Ordinal.{0}) : RoBaseE S l (ugY S) 0 (Om (1 + 1 + 1)) := by
  unfold RoBaseE
  rw [add_zero, vqWeY3]
  refine ⟨?_, Ry.ryOm3_mem _ _, ?_, fun _ _ => Ry.ryOm3_mem _ _, fun e' _ he' => ?_⟩
  · have h := leWe_dvd (ugY_lt_Om3 (S := S)).le
    rwa [vqWeY3, vnWe_Om3] at h
  · exact (vkOmW.1.isPrincipal Ry.ryOm3_lt (ugY_lt_Om3.trans Ry.ryOm3_lt)).trans_le (ConjT.OmW_le_A S _)
  · rw [nonpos_iff_eq_zero.1 he']
    exact (Om_pos one_ne_zero).trans (psiS_bounds (S := S) _ 1).1

/-- **`Θ(ψ₂(Ω₃ + Y₃)) = ψ₁(A + 1 + Y₂ + Y₂)`.** -/
theorem vqRead_Om3Y3 {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1) + ugY S) (Om (1 + 1))) =
      S.psi (A + 1 + S.psi (Om (1 + 1)) (Om (1 + 1)) + S.psi (Om (1 + 1)) (Om (1 + 1))) (Om 1) := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hAω := vnA_ge hl hX hA hρ
  have hle : A ≤ A + 1 + S.psi (Om (1 + 1)) (Om (1 + 1)) := le_self_add.trans le_self_add
  have hΩ2 : Om (1 + 1) < A + 1 + S.psi (Om (1 + 1)) (Om (1 + 1)) := (vkOmW.2.trans_le hAω).trans_le hle
  have hÂ : A + 1 + S.psi (Om (1 + 1)) (Om (1 + 1)) ∈ S.CSet (A + 1 + S.psi (Om (1 + 1)) (Om (1 + 1)))
      (S.psi (A + 1 + S.psi (Om (1 + 1)) (Om (1 + 1))) (Om 1)) :=
    CSet.add_mem (CSet.add_mem ((psi_mono (S := S) hκ1 hle).2 hA) (CSet.one_mem _ _)) (vqY2_mem hΩ2)
  have hbase := vnRead_W hl hX hA hρ (X := Om (1 + 1 + 1)) (by rw [vnWe_Om3]; exact ugY_lt_Om3.le)
    vnWe_Om3.le
  rw [vnWe_Om3] at hbase
  have h := vqTopY3 hl hX hA hρ le_rfl _ _ (vqBase_Om3 l) le_rfl hÂ hbase
  rw [add_zero, gxTh_zero, add_zero, uaOe_fix (gg_SC_eps vqY2_SC) (psiS_bounds (S := S) _ 1).1] at h
  unfold leTe at h
  rwa [vqWeY3] at h

end Googology.Trans.PoR.InaccPsi.R2.Vq
