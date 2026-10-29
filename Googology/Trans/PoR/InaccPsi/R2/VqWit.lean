import Googology.Trans.PoR.InaccPsi.R2.VqPull

/-!
# Witnesses for the base-relative shift; the tests against `Vn.vnNoSh` and `Vn.vnTop_Om3`

`Y₃ = ψ_{Ω₃}(Ω₃) = Ug.ugY S`, `Y₂ = ψ_{Ω₂}(Ω₂)`, `W^E = Ω₂^E`.

* `vqA_spec` (**the restart hypotheses `A ∈ Cl(A, ψ₁(A))`, `ψ₁(A) = ρ_λ` hold for `A = A_{η_λ}`** whenever
  `ρ_λ < c_{n+1}` for some `n`: the hypotheses `hAo`, `hρo` of `Vq.VqSucc`, `Vq.VqLim`, `Vq.VqPull` are satisfiable);
* `vqWit_W1` (**a shift with its top: `VqSh λ A b W^{Ω₁} Ω^{ρ_λ}` and `RvTop λ b W^{Ω₁} Ω^{ρ_λ} 0` at every base**,
  so the hypotheses of `vqTopE`, `vqTopW` are jointly satisfiable);
* `vqSh_Y3` (**`(Y₃, Y₂)` IS a base-relative shift at every base `b ≥ Ω₃`** when `Ω₂ < A`), `vqSh_Y3_rst` (the same
  at a restart), `vqNoVk_Y3` (**and it is no `Vk.VkSh` at any base**, as `Vn.vnNoSh` says);
* `vqNoSh` (**no base-relative shift in `[Y₃, Ω₃)` at a base `b` with `b + W^X ≤ Ω₃`**), `vqNoSh0` (at the base `0`):
  the levels `[Y₃, Ω₃)` are shifts only above `Ω₃`, so the top at `Y₃` over the base `0` must come from the visible
  levels below `Y₃` (as in `Vn.vnRead_Y3`), not from a shift;
* `vqOm3_sh` (`(Ω₃, Ω₂)` is a `VqSh` at the base `0`) and `vqOm3_top_false` (**its top `RvTop λ 0 Ω₃ Ω₂ 0` is false**,
  `Vn.vnTop_Om3`): the hypothesis `h0` of `vqTopE` is refutable at that instance, satisfiable at `vqWit_W1`.

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj Googology.Trans.PoR.InaccPsi.R2.Uq
  Googology.Trans.PoR.InaccPsi.R2.Vk Googology.Trans.PoR.InaccPsi.R2.Vn

variable {S : InaccSeq.{0}}

/-- **The restart hypotheses hold at `A = A_{η_λ}`** when `ρ_λ < c_{n+1}`. -/
theorem vqA_spec {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {n : ℕ}
    (hn : upsilon l < Bc.bcC S (n + 1)) :
    ConjT.Aη S (cdEta S l) ∈ S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)) ∧
      S.psi (ConjT.Aη S (cdEta S l)) (Om 1) = upsilon l := by
  obtain ⟨hg, -, -, hpv⟩ := cdEta_pv_spec (S := S) hl.1 hX
  have hAL := (Sf.sfA_lt (S := S) (n := n) (hpv ▸ hn)).2
  exact ⟨Sf.sfOwn hg hAL, hpv⟩

/-- **A base-relative shift with its top at every base**: `(W^{Ω₁}, Ω^{ρ_λ})`. -/
theorem vqWit_W1 {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) (A b : Ordinal.{0}) :
    VqSh S l A b (leWe (Om 1)) (leOe (upsilon l)) ∧ RvTop S l b (leWe (Om 1)) (leOe (upsilon l)) 0 :=
  ⟨vqSh_of_vk (vkSh_of_rv (Rw.rwShW1 hl hX b)), Rw.rwTopW1 hl hX b⟩

theorem vqY2_SC : SC (S.psi (Om (1 + 1)) (Om (1 + 1))) := SC_psi (InR_Om_succ 1) _

theorem vqY3_mem {a c : Ordinal.{0}} (h : Om (1 + 1 + 1) < a) : ugY S ∈ S.CSet a c :=
  CSet.psi_mem h (InR_Om_succ (1 + 1)) (Ry.ryOm3_mem _ _) (Ry.ryOm3_mem _ _)

theorem vqY2_mem {a c : Ordinal.{0}} (h : Om (1 + 1) < a) : S.psi (Om (1 + 1)) (Om (1 + 1)) ∈ S.CSet a c :=
  CSet.psi_mem h (InR_Om_succ 1) (mxOm2_mem _ _) (mxOm2_mem _ _)

/-- **`(Y₃, Y₂)` is a base-relative shift at every base `b ≥ Ω₃`** (image own relative to `A > Ω₂`). -/
theorem vqSh_Y3 {l A b : Ordinal.{0}} (hA2 : Om (1 + 1) < A) (hb : Om (1 + 1 + 1) ≤ b) :
    VqSh S l A b (ugY S) (S.psi (Om (1 + 1)) (Om (1 + 1))) where
  ne := uqY_SC.1.ne'
  dvd := by
    have h := (leWe_lt_SC (uqY_SC (S := S)) uqW_lt_Y (gg_one_lt_of_SC (uqY_SC (S := S)))).2
    rwa [leWe_one] at h
  hull := vqY3_mem (Ry.ryOm3_lt.trans_le (ConjT.OmW_le_A S _))
  mem := vqY3_mem (hb.trans_lt (lt_add_of_pos_right b (leWe_pos _)))
  memh := vqY2_mem (hA2.trans_le le_self_add)
  cl := fun _ _ _ => VkA.big uqW_lt_Y.le uqY_SC
  clh := fun _ _ _ => VkA.big (psiS_bounds (S := S) _ 1).1.le vqY2_SC

/-- The same at a restart, with `A` of the restart. -/
theorem vqSh_Y3_rst {l ηx A b : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) (hb : Om (1 + 1 + 1) ≤ b) :
    VqSh S l A b (ugY S) (S.psi (Om (1 + 1)) (Om (1 + 1))) :=
  vqSh_Y3 (vkOmW.2.trans_le (vnA_ge hl hX hA hρ)) hb

/-- **`(Y₃, ·)` is no `Vk.VkSh`** at any base. -/
theorem vqNoVk_Y3 (l b Xh : Ordinal.{0}) : ¬ VkSh S l b (ugY S) Xh := fun hs =>
  vnNoSelf (s := 1 + 1) le_rfl ugY_lt_Om3
    ((psi_lt (InR_Om_succ 1) _).le.trans (ugOm2_lt_psi3 _).le) hs.mem

/-- **No base-relative shift in `[Y₃, Ω₃)` at a base `b` with `b + W^X ≤ Ω₃`.** -/
theorem vqNoSh {l A b X Xh : Ordinal.{0}} (hYX : ugY S ≤ X) (hX3 : X < Om (1 + 1 + 1))
    (hb : b + leWe X ≤ Om (1 + 1 + 1)) : ¬ VqSh S l A b X Xh := fun hs => by
  have hQ : S.psi (b + leWe X) (Om (1 + 1)) ≤ ugY S := (psi_lt (InR_Om_succ 1) _).le.trans uqW_lt_Y.le
  have h1 := vnCSet_sub (s := 1 + 1) hb hQ hs.mem
  exact vnNoSelf (s := 1 + 1) hYX hX3 ((psi_lt (InR_Om_succ 1) _).le.trans (ugOm2_lt_psi3 _).le)
    (CSet_mono hYX le_rfl h1)

/-- **No base-relative shift in `[Y₃, Ω₃)` at the base `0`.** -/
theorem vqNoSh0 {l A X Xh : Ordinal.{0}} (hYX : ugY S ≤ X) (hX3 : X < Om (1 + 1 + 1)) :
    ¬ VqSh S l A 0 X Xh := by
  have h3 : (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := (add_pos_of_right zero_lt_one _).ne'
  refine vqNoSh hYX hX3 ?_
  rw [zero_add]
  exact (leWe_lt_SC (SC_Om h3) (Om_lt_Om.2 (lt_add_one _)) hX3).1.le

/-- `(Ω₃, Ω₂)` is a base-relative shift at every base. -/
theorem vqOm3_sh (l A b : Ordinal.{0}) : VqSh S l A b (Om (1 + 1 + 1)) (Om (1 + 1)) := by
  have h := vkSh_Om (S := S) l b 1
  simp only [Nat.cast_one] at h
  exact vqSh_of_vk h

/-- **The top of the shift `(Ω₃, Ω₂)` at the base `0` is false** (`Vn.vnTop_Om3`). -/
theorem vqOm3_top_false {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    VqSh S l A 0 (Om (1 + 1 + 1)) (Om (1 + 1)) ∧ ¬ RvTop S l 0 (Om (1 + 1 + 1)) (Om (1 + 1)) 0 :=
  ⟨vqOm3_sh l A 0, vnTop_Om3 hl hX hA hρ⟩

end Googology.Trans.PoR.InaccPsi.R2.Vq
