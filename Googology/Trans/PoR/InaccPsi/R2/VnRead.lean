import Googology.Trans.PoR.InaccPsi.R2.VnWall

/-!
# The reading of `ψ_{Ω₂}(Y₃)`; the tops at `Ω_{k+3}` asked by `Vk.vkTheta_th` are false

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T = Ug.ugTh S λ`, `Y₃ = ψ_{Ω₃}(Ω₃)`, `Y₂ = ψ_{Ω₂}(Ω₂)`,
`y_n`, `z_n` the iterates of `ψ_{Ω₃}`, `ψ_{Ω₂}` from `0`, `θ = ψ_{Ω₂}(Ω_ω)`; a restart `λ` (`IsRestartIdx λ`,
`ρ_λ < P(η_x)`) with `ψ_{Ω₁}(A) = ρ_λ`, `A ∈ Cl(A, ψ_{Ω₁}(A))`.

* `vnT_it` (`T(y_n) = z_n`), `vnA_ge` (`Ω_ω ≤ A`), `vnTop_it` (**`Θ(ψ₂(W^{W^{y_{n+1}}})) = ψ₁(A+1+Ω^{Ω^{z_{n+1}}})`**,
  from the level statement past `Γ₂` at `y_{n+1}`, `Uu.uuLSY`);
* `vnRead_Y3` (**`Θ_λ(ψ_{Ω₂}(Y₃)) = ψ_{Ω₁}(A + 1 + Y₂)`**), `vnRead_W` (the same reading at every `ψ₂(W^X)` with
  `Y₃ ≤ W^X ≤ Ω₃`: `ψ₂` does not see past `Y₃`, `Vn.vnPsi2_eq`);
* `vnTop_false` (**`¬ RvTop λ 0 X X̂ 0` whenever `Y₃ ≤ W^X ≤ Ω₃` and `Y₂ < Ω^{X̂}`**), `vnTop_Om3` (**the top at
  `Ω₃` with the image `Ω₂ = T Ω₃` is false**), `vnTheta_vac` (**the hypothesis of `Vk.vkTheta_th` is false, so
  `vkTheta_th` is vacuous**);
* `vnOwnE_Om3` (UNCONDITIONAL: `Ω₃` is an own exponent `Vk.VkOwnE` with the image `Ω₂` at every base and offset),
  `vnLev_Om3` (**no level statement `Vk.VkLev Ow Ω₃ Ω₂` with `Ow 0 0`**: the level statement with the image `T E` fails
  at the own level `E = Ω₃`);
* `vnTheta_th` (**`Θ_λ(θ) = ψ_{Ω₁}(A + 1 + Ω_ω)` from the readings `Θ(ψ₂(Y_{k+3})) = ψ₁(A + 1 + Y_{k+2})`**, the
  corrected tops), `vnTheta_hyp0` (its case `k = 0` holds).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj Googology.Trans.PoR.InaccPsi.R2.Uq
  Googology.Trans.PoR.InaccPsi.R2.Uu Googology.Trans.PoR.InaccPsi.R2.Vk

variable {S : InaccSeq.{0}}

theorem vnOm3C (a b : Ordinal.{0}) : Om (1 + 1 + 1 : Ordinal.{0}) ∈ S.CSet a b := Ry.ryOm3_mem a b

/-- **`T(y_n) = z_n`.** -/
theorem vnT_it (l : Ordinal.{0}) : ∀ n : ℕ,
    ugTh S l ((fun x => S.psi x (Om (1 + 1 + 1)))^[n] 0) = (fun x => S.psi x (Om (1 + 1)))^[n] 0 := by
  intro n
  induction n with
  | zero => exact ugTh_zero l
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    exact ugTh_atom (uuLt3 (vnIt_lt (s := 1 + 1) vnOm3C n))

/-- `W^{Ω₃} = Ω₃`. -/
theorem vnWe_Om3 : leWe (Om (1 + 1 + 1 : Ordinal.{0})) = Om (1 + 1 + 1) := by
  have h3 : (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := (add_pos_of_right zero_lt_one _).ne'
  exact (ugSC_W (SC_Om h3) (Om_lt_Om.2 (lt_add_one _))).2

/-- **UNCONDITIONAL: `Ω₃` is an own exponent with the image `Ω₂`** at every base and every offset. -/
theorem vnOwnE_Om3 (l b X0 : Ordinal.{0}) : VkOwnE S l b X0 (Om (1 + 1 + 1)) (Om (1 + 1)) := by
  have h3 : (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := (add_pos_of_right zero_lt_one _).ne'
  have h23 : (1 + 1 : Ordinal.{0}) ≤ 1 + 1 + 1 := le_self_add
  have h12 : (1 : Ordinal.{0}) ≤ 1 + 1 := le_self_add
  exact ⟨(gg_one_lt_of_SC (SC_Om h3)).le, vnOm3C _ _, vnOm3C _ _, mxOm2_mem _ _,
    fun Q hQ _ => VkA.om hQ.1 h23, fun Q hQ _ => VkA.om hQ.1 h12⟩

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`Ω_ω ≤ A`** for `ψ_{Ω₁}(A) = ρ_λ` in normal form (`K = ψ_{Ω₁}(Ω_ω) ≤ ρ_λ`). -/
theorem vnA_ge {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    Om ω ≤ A := by
  by_contra h
  push Not at h
  have h1 : S.psi A (Om 1) < S.psi (Om ω) (Om 1) :=
    psi_lt_psi_of_mem Low.InR_Om_one h ((psi_mono (S := S) Low.InR_Om_one h.le).2 hA)
  have h2 := Td.tdK_le_rho (S := S) hl hX
  unfold Td.tdK at h2
  rw [hρ] at h1
  exact absurd (h1.trans_le h2) (lt_irrefl _)

/-- **`Θ(ψ₂(W^{W^{y_{n+1}}})) = ψ₁(A + 1 + Ω^{Ω^{z_{n+1}}})`** (the level statement past `Γ₂` at `y_{n+1}`). -/
theorem vnTop_it {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    (n : ℕ) :
    gxTh (upsilon l) (ldAtR S l)
        (S.psi (leWe (leWe ((fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0))) (Om (1 + 1))) =
      S.psi (A + 1 + leOe (leOe ((fun x => S.psi x (Om (1 + 1)))^[n + 1] 0))) (Om 1) := by
  have hay : (fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0 < ugY S := vnIt_lt (s := 1 + 1) vnOm3C (n + 1)
  have haA := uuLtA (l := l) hay
  have haH : (fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0 ∈ cdHull S l :=
    vnIt_mem (s := 1 + 1) vnOm3C (n + 1) _ _ haA.le
  have hΩa : Om (1 + 1) < (fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0 := by
    rw [Function.iterate_succ_apply']; exact ugOm2_lt_psi3 _
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
  rw [zero_add, zero_add] at hT3
  have hWω : leWe ((fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0) < Om ω :=
    ((leWe_lt_SC uqY_SC uqW_lt_Y hay).1.trans ugY_lt_Om3).trans Ry.ryOm3_lt
  have h := vkRead0 hT3 hWω hA hρ
  rw [hT] at h
  exact h

/-- **`Θ_λ(ψ_{Ω₂}(Y₃)) = ψ_{Ω₁}(A + 1 + Y₂)`.** -/
theorem vnRead_Y3 {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (ugY S) (Om (1 + 1))) =
      S.psi (A + 1 + S.psi (Om (1 + 1)) (Om (1 + 1))) (Om 1) := by
  have hκC2 : ∀ a b, Om (1 + 1 : Ordinal.{0}) ∈ S.CSet a b := fun a b => mxOm2_mem a b
  have hY2SC : SC (S.psi (Om (1 + 1)) (Om (1 + 1))) := SC_psi (InR_Om_succ 1) _
  have hΩ1Y2 : Om 1 < S.psi (Om (1 + 1)) (Om (1 + 1)) := (psiS_bounds (S := S) _ 1).1
  have hEX : ∀ n : ℕ, leWe (leWe ((fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0)) ≤ ugY S := fun n =>
    (leWe_lt_SC uqY_SC uqW_lt_Y (leWe_lt_SC uqY_SC uqW_lt_Y (vnIt_lt (s := 1 + 1) vnOm3C (n + 1))).1).1.le
  have hEcof : ∀ e, e < ugY S → ∃ n : ℕ, e < leWe (leWe ((fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0)) := by
    intro e he
    obtain ⟨m, hm⟩ := (lt_ciSup_iff (uuIt_bdd (S := S) (1 + 1))).1 (he.trans_le (uuY_le_sup (S := S) uuThree_lt))
    exact ⟨m, hm.trans ((uuIt_lt (S := S) (1 + 1) m).trans_le ((ujLe_We _).trans (ujLe_We _)))⟩
  have hyY : ∀ n : ℕ, leOe (leOe ((fun x => S.psi x (Om (1 + 1)))^[n + 1] 0)) ≤ S.psi (Om (1 + 1)) (Om (1 + 1)) :=
    fun n => (leOe_lt_SC hY2SC hΩ1Y2 (leOe_lt_SC hY2SC hΩ1Y2 (vnIt_lt (s := 1) hκC2 (n + 1))).1).1.le
  have hycof : ∀ z, z < S.psi (Om (1 + 1)) (Om (1 + 1)) →
      ∃ n : ℕ, z ≤ leOe (leOe ((fun x => S.psi x (Om (1 + 1)))^[n + 1] 0)) := by
    intro z hz
    obtain ⟨m, hm⟩ := (lt_ciSup_iff (uuIt_bdd (S := S) 1)).1 (hz.trans_le (uuY_le_sup (S := S) uuTwo_lt))
    exact ⟨m, (hm.trans (uuIt_lt (S := S) 1 m)).le.trans ((ujLe_Oe _).trans (ujLe_Oe _))⟩
  have hTop : ∀ n : ℕ, gxTh (upsilon l) (ldAtR S l)
      (S.psi (0 + leWe (leWe ((fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0))) (Om (1 + 1))) =
      S.psi (A + 1 + leOe (leOe ((fun x => S.psi x (Om (1 + 1)))^[n + 1] 0))) (Om 1) := fun n => by
    rw [zero_add]; exact vnTop_it hl hX hA hρ n
  have h := ugReadLim (S := S) (l := l) (β := 0) (Â := A + 1)
    (fun n => leWe (leWe ((fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0)))
    (fun n => leOe (leOe ((fun x => S.psi x (Om (1 + 1)))^[n + 1] 0)))
    uqY_SC.isSuccLimit hY2SC.isSuccLimit hEX hEcof hyY hycof hTop
  rw [zero_add] at h
  exact h

/-- **The same reading at every `ψ₂(W^X)` with `Y₃ ≤ W^X ≤ Ω₃`.** -/
theorem vnRead_W {A X : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    (hYW : ugY S ≤ leWe X) (hW3 : leWe X ≤ Om (1 + 1 + 1)) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (leWe X) (Om (1 + 1))) =
      S.psi (A + 1 + S.psi (Om (1 + 1)) (Om (1 + 1))) (Om 1) := by
  rw [vnPsi2_eq (s := 1 + 1) (ugOm2_lt_psi3 _) hYW hW3]
  exact vnRead_Y3 hl hX hA hρ

/-- **`¬ RvTop λ 0 X X̂ 0` whenever `Y₃ ≤ W^X ≤ Ω₃` and `Y₂ < Ω^{X̂}`.** -/
theorem vnTop_false {A X Xh : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1)))
    (hρ : S.psi A (Om 1) = upsilon l) (hYW : ugY S ≤ leWe X) (hW3 : leWe X ≤ Om (1 + 1 + 1))
    (hXh : S.psi (Om (1 + 1)) (Om (1 + 1)) < leOe Xh) : ¬ RvTop S l 0 X Xh 0 := by
  intro hT
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hXω : X < Om ω := ((ujLe_We X).trans hW3).trans_lt Ry.ryOm3_lt
  have h1 := vkRead0 hT hXω hA hρ
  rw [vnRead_W hl hX hA hρ hYW hW3] at h1
  have hAω := vnA_ge hl hX hA hρ
  have hle : A ≤ A + 1 + leOe Xh := le_self_add.trans le_self_add
  have hlt : A + 1 + S.psi (Om (1 + 1)) (Om (1 + 1)) < A + 1 + leOe Xh := (add_lt_add_iff_left _).2 hXh
  have hΩ2 : Om (1 + 1) < A + 1 + leOe Xh := (vkOmW.2.trans_le hAω).trans_le hle
  have hmem : A + 1 + S.psi (Om (1 + 1)) (Om (1 + 1)) ∈ S.CSet (A + 1 + leOe Xh) (S.psi (A + 1 + leOe Xh) (Om 1)) :=
    CSet.add_mem (CSet.add_mem ((psi_mono (S := S) hκ1 hle).2 hA) (CSet.one_mem _ _))
      (CSet.psi_mem hΩ2 (InR_Om_succ 1) (mxOm2_mem _ _) (mxOm2_mem _ _))
  have h2 := psi_lt_psi_of_mem hκ1 hlt hmem
  rw [h1] at h2
  exact lt_irrefl _ h2

/-- **The top at `Ω₃` with the image `Ω₂ = T Ω₃` is false.** -/
theorem vnTop_Om3 {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    ¬ RvTop S l 0 (Om (1 + 1 + 1)) (Om (1 + 1)) 0 :=
  vnTop_false hl hX hA hρ (by rw [vnWe_Om3]; exact ugY_lt_Om3.le) vnWe_Om3.le
    ((psi_lt (InR_Om_succ 1) _).trans_le (ujLe_Oe _))

/-- **The hypothesis of `Vk.vkTheta_th` is false**: `vkTheta_th` is vacuous. -/
theorem vnTheta_vac {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    ¬ ∀ k : ℕ, RvTop S l 0 (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Om ((k : Ordinal.{0}) + 1 + 1)) 0 := by
  intro h
  have h0 := h 0
  rw [Nat.cast_zero, zero_add] at h0
  exact vnTop_Om3 hl hX hA hρ h0

/-- **No level statement `VkLev Ow Ω₃ Ω₂` with `Ow 0 0`** (although `Ω₃` is own with the image `Ω₂`,
`vnOwnE_Om3`). -/
theorem vnLev_Om3 {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    {Ow : Ordinal.{0} → Ordinal.{0} → Prop} (hO : Ow 0 0) : ¬ VkLev S l Ow (Om (1 + 1 + 1)) (Om (1 + 1)) := by
  intro hL
  have h := hL 0 0 0 (Or.inl ⟨rfl, rfl⟩) (dvd_zero _) hO
  rw [zero_add, zero_add] at h
  refine vnTop_false hl hX hA hρ (by rw [vnWe_Om3, vnWe_Om3]; exact ugY_lt_Om3.le)
    (by rw [vnWe_Om3, vnWe_Om3]) ((psi_lt (InR_Om_succ 1) _).trans_le ((ujLe_Oe _).trans (ujLe_Oe _))) h

/-- **The case `k = 0` of the corrected tops holds**: `Θ(ψ₂(Y₃)) = ψ₁(A + 1 + Y₂)`. -/
theorem vnTheta_hyp0 {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (ujY S (((0 : ℕ) : Ordinal.{0}) + 1)) (Om (1 + 1))) =
      S.psi (A + 1 + ujY S ((0 : ℕ) : Ordinal.{0})) (Om 1) := by
  rw [Nat.cast_zero, zero_add, ujY_one, ujY_zero]
  exact vnRead_Y3 hl hX hA hρ

end Main

/-- **`Θ_λ(θ) = ψ_{Ω₁}(A + 1 + Ω_ω)` from the corrected tops** `Θ(ψ₂(Y_{k+3})) = ψ₁(A + 1 + Y_{k+2})`. -/
theorem vnTheta_th {l A : Ordinal.{0}}
    (hY : ∀ k : ℕ, gxTh (upsilon l) (ldAtR S l) (S.psi (ujY S ((k : Ordinal.{0}) + 1)) (Om (1 + 1))) =
      S.psi (A + 1 + ujY S (k : Ordinal.{0})) (Om 1)) :
    gxTh (upsilon l) (ldAtR S l) (ConjT.th S) = S.psi (A + 1 + Om ω) (Om 1) := by
  have hW := vkOmW
  have hlim : IsSuccLimit (Om (ω : Ordinal.{0})) := hW.1.isSuccLimit
  have h := ugReadLim (S := S) (l := l) (β := 0) (Â := A + 1) (X := Om ω) (Y := Om ω)
    (fun k => ujY S ((k : Ordinal.{0}) + 1)) (fun k => ujY S (k : Ordinal.{0})) hlim hlim
    (fun k => ((ujY_lt _).trans (Om_lt_Om.2 (vkNat_lt_omega k))).le)
    (fun e he => by
      obtain ⟨n, hn⟩ := Rx.rxOmW_nat he
      exact ⟨n, hn.trans_le ((Om_le_Om.2 (le_self_add.trans le_self_add)).trans (ujY_gt _).le)⟩)
    (fun k => ((ujY_lt _).trans (Om_lt_Om.2 (Vb.vbNat_lt_omega k))).le)
    (fun z hz => by
      obtain ⟨n, hn⟩ := Rx.rxOmW_nat hz
      exact ⟨n, (hn.trans_le ((Om_le_Om.2 le_self_add).trans (ujY_gt _).le)).le⟩)
    (fun k => by rw [zero_add]; exact hY k)
  rw [zero_add] at h
  exact h

end Googology.Trans.PoR.InaccPsi.R2.Vn
