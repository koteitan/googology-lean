import Googology.Trans.PoR.InaccPsi.R2.XiLaw

/-!
# REFUTE FIRST on the family law `skTopFam` (`Wg.WgTopFamAll`): it FAILS at `k = 0`, `β = 0`, `e = ω`

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Vb.vbT S λ`, `A = A_{η_λ}` (own, `ψ₁(A) = ρ_λ`), `W^x = ω^{Ω₂·x}` (`Le.leWe`),
`Ω^x = ω^{Ω₁·x}` (`Le.leOe`), `a_c = W^{Ω₃+c}`, `P* = ψ₂(Ω^{Ω₂+ω})`.

* `xiReadOm` (**THE READING AT `e = ω`**): `Θ(ψ₂(W^{Ω₃+ω})) = ψ₁(A + P*)`.  Upper half: `Xd.xdUp_at` at `a_ω`
  (`T a_ω = Ω^{Ω₂+ω}`, `Vh.vhT_cnfW`); lower half: the law at `k = 0` (`Xd.xdLow0`) at the bases `a_n = W^{Ω₃+n}`
  (`T a_n = Ω^{Ω₂+n}`), `ψ₂(a_n + Ω₃) < ψ₂(a_ω)`, and `P* = sup_n ψ₂(Ω^{Ω₂+n} + Ω₂)` (`xiPstar_cof`).
* `xiShape` (`Ω^{Z+ω} ≠ P` for every strongly critical `P > Ω₁`: the family shape never has a strongly critical
  offset at a limit exponent).
* `xiFamOm_false` (**no image `X̂` gives `Vt.VtTopDyn λ 0 Ω₃ X̂ ω`**: if `ψ₁(A + P*) = ψ₁(A + 1 + Ω^{X̂(0)+ω})` then
  `Ω^{X̂(0)+ω} < P*` is impossible (the own arguments `A + ψ₂(Ω^{Ω₂+n} + Ω₂)` are cofinal below `A + P*` and their
  `ψ₁`-values increase strictly) and `Ω^{X̂(0)+ω} > P*` is impossible (`A + P*` is own, so
  `ψ₁(A + P*) < ψ₁(A + P* + 1)`)).
* `xiTopFam_false` (**`Wg.WgTopFamAll S` (the skeleton node `skTopFam`) IS FALSE**, at the restart of `m* = L(0)`).
* `xiTopUp0` (the replacement law `XiTopUp` at `e = 0`: every `k`, every `β ∈ D`), `xiTopUpOm` (at `k = 0`,
  `e = ω`, `β = 0`): the non-vacuity of the replacement node.

No new axiom.  New definition: `XiTopUp` (the statement of the replacement node; no repo statement depends on it).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xi

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Vk Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le

variable {S : InaccSeq.{0}}

/-- The replacement law (statement of the new skeleton node `skTopUp`): the `Wz.WzUpU` bound is attained at every
top atom `T_{Ω_{k+3}+e}(β) = ψ₂(β + W^{Ω_{k+3}+e})`, `e < Ω₂` a code, `β ∈ D` a base. -/
def XiTopUp (S : InaccSeq.{0}) : Prop :=
  ∀ (k : ℕ) (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
    A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
    ∀ e β, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → VbD S l β →
      Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β →
      gxTh (upsilon l) (ldAtR S l) (leTe S (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) β) =
        S.psi (A + 1 + S.psi (vbT S l (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e))) (Om (1 + 1))) (Om 1)

/-- Every `x < Ω^{Ω₂+ω}` is below some `Ω^{Ω₂+n}`. -/
theorem xiOe_cof {x : Ordinal.{0}} (hx : x < leOe (Om (1 + 1) + ω)) :
    ∃ n : ℕ, x < leOe (Om (1 + 1) + (n : Ordinal.{0})) := by
  by_contra hc
  push Not at hc
  have h0 := hc 0
  have hx0 : x ≠ 0 := by
    intro h; rw [h] at h0; exact absurd h0 (not_le.2 (opow_pos _ omega0_pos))
  have hg : log ω x < Om 1 * (Om (1 + 1) + ω) := (lt_opow_iff_log_lt one_lt_omega0 hx0).1 hx
  have hn : ∀ n : ℕ, Om 1 * Om (1 + 1) + Om 1 * (n : Ordinal.{0}) ≤ log ω x := fun n => by
    rw [← mul_add]; exact le_log_of_opow_le one_lt_omega0 (hc n)
  rw [mul_add] at hg
  have h1 := hn 0
  rw [Nat.cast_zero, mul_zero, add_zero] at h1
  have hd : log ω x - Om 1 * Om (1 + 1) < Om 1 * ω := Ry.rySub_lt h1 hg
  have hO1 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  have hq : (log ω x - Om 1 * Om (1 + 1)) / Om 1 < ω := (Ordinal.div_lt hO1).2 hd
  obtain ⟨m, hm⟩ := lt_omega0.1 hq
  have h2 := hn (m + 1)
  have ee : log ω x = Om 1 * Om (1 + 1) + (log ω x - Om 1 * Om (1 + 1)) :=
    (Ordinal.add_sub_cancel_of_le h1).symm
  rw [ee] at h2
  have h3 := (add_le_add_iff_left _).1 h2
  have h4 : ((m + 1 : ℕ) : Ordinal.{0}) ≤ (log ω x - Om 1 * Om (1 + 1)) / Om 1 := (Ordinal.le_div hO1).2 h3
  rw [hm] at h4
  exact absurd (Nat.cast_le.1 h4) (by omega)

/-- **`P* = ψ₂(Ω^{Ω₂+ω})` is the supremum of `ψ₂(Ω^{Ω₂+n} + Ω₂)`.** -/
theorem xiPstar_cof {Q : Ordinal.{0}} (hQ : Q < S.psi (leOe (Om (1 + 1) + ω)) (Om (1 + 1))) :
    ∃ n : ℕ, Q < S.psi (leOe (Om (1 + 1) + (n : Ordinal.{0})) + Om (1 + 1)) (Om (1 + 1)) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hpos : (0 : Ordinal.{0}) < Om 1 * (Om (1 + 1) + ω) :=
    mul_pos (Om_pos one_ne_zero) (lt_of_lt_of_le omega0_pos le_add_self)
  have hlim : IsSuccLimit (leOe (Om (1 + 1) + ω)) := by
    unfold leOe; exact isSuccLimit_opow_left isSuccLimit_omega0 hpos.ne'
  rw [Lw.lw_psi_limit S hκ2 hlim] at hQ
  have hbdd : BddAbove (range fun e : Iio (leOe (Om (1 + 1) + ω)) => S.psi e.1 (Om (1 + 1))) :=
    ⟨Om (1 + 1), by rintro _ ⟨e, rfl⟩; exact (psi_lt hκ2 _).le⟩
  haveI : Nonempty (Iio (leOe (Om (1 + 1) + ω))) := ⟨⟨0, opow_pos _ omega0_pos⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff hbdd).1 hQ
  obtain ⟨n, hn⟩ := xiOe_cof (x := e.1) e.2
  exact ⟨n, he.trans_le (psi_mono hκ2 (hn.le.trans le_self_add)).1⟩

/-- **The family shape has no strongly critical offset at a limit exponent**: `Ω^{Z+ω} ≠ P` for `P` strongly critical,
`P > Ω₁`. -/
theorem xiShape {P : Ordinal.{0}} (hP : SC P) (h1 : Om 1 < P) (Z : Ordinal.{0}) : leOe (Z + ω) ≠ P := by
  intro h
  have hPε : ω ^ P = P := gg_SC_eps hP
  have e1 : Om 1 * (Z + ω) = P := by
    unfold leOe at h
    rw [← hPε] at h
    exact le_antisymm ((opow_le_opow_iff_right one_lt_omega0).1 h.le)
      ((opow_le_opow_iff_right one_lt_omega0).1 h.ge)
  rw [mul_add] at e1
  have hω : Om 1 * ω < P := Nc.ncSC_mul hP h1 (Lw.lw_omega_lt_SC hP)
  have hω0 : (0 : Ordinal.{0}) < Om 1 * ω := mul_pos (Om_pos one_ne_zero) omega0_pos
  rcases lt_or_ge (Om 1 * Z) P with hz | hz
  · exact absurd e1 (hP.isPrincipal hz hω).ne
  · exact absurd e1 (lt_of_le_of_lt hz (lt_add_of_pos_right _ hω0)).ne'

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

theorem xiRho_gt : ω < upsilon l := Lw.lw_omega_lt_SC (Le.leRho hl hX).1

/-- A small constant `c ≤ ρ_λ` with `c` in every closure: `c ∈ D`, `T c = c`. -/
theorem xiSmall {c : Ordinal.{0}} (hcρ : c ≤ upsilon l) (hc : ∀ a b : Ordinal.{0}, c ∈ S.CSet a b) :
    VbD S l c ∧ vbT S l c = c := by
  have hρ1 := (Le.leRho hl hX).2
  have hc1 : c < Om 1 := hcρ.trans_lt hρ1
  have hc2 : c < Om (1 + 1) := hc1.trans (Om_lt_Om.2 (lt_add_one 1))
  refine ⟨⟨hc _ _, hc _ _, hc2.trans ldOm2_lt_OmW⟩, ?_⟩
  rw [vbT_code hl hX hc2 (hc _ _), gxTh_small hcρ]

/-- `a_c = W^{Ω₃+c} ∈ D` and `T a_c = Ω^{Ω₂+c}`. -/
theorem xiTW {c : Ordinal.{0}} (hcρ : c ≤ upsilon l) (hc : ∀ a b : Ordinal.{0}, c ∈ S.CSet a b) :
    VbD S l (leWe (Om (1 + 1 + 1) + c)) ∧
      vbT S l (leWe (Om (1 + 1 + 1) + c)) = leOe (Om (1 + 1) + c) := by
  obtain ⟨hcD, hcT⟩ := xiSmall hl hX hcρ hc
  have h3D : VbD S l (Om (1 + 1 + 1)) := Wz.wzD_Om3
  have hgD : VbD S l (Om (1 + 1 + 1) + c) :=
    ⟨CSet.add_mem h3D.1 hcD.1, CSet.add_mem h3D.2.1 hcD.2.1, vkOmW.1.isPrincipal h3D.2.2 hcD.2.2⟩
  have hgW : Om (1 + 1 + 1) + c < Om ω := hgD.2.2
  have hWD : VbD S l (leWe (Om (1 + 1 + 1) + c)) :=
    ⟨leWe_mem hgD.1, leWe_mem hgD.2.1, (leWe_lt_SC vkOmW.1 vkOmW.2 hgW).1⟩
  refine ⟨hWD, ?_⟩
  have h0D : VbD S l 0 := xiD_zero l
  have h1ρ : (1 : Ordinal.{0}) ≤ upsilon l := (one_lt_omega0.trans (xiRho_gt hl hX)).le
  have h := Vh.vhT_cnfW hl hX (g := Om (1 + 1 + 1) + c) (d := 1) (r := 0) hgD h0D (CSet.one_mem _ _)
    (gg_one_lt_of_SC ldOm2_SC)
  simp only [mul_one, add_zero] at h
  rw [gxTh_small h1ρ, Vh.vhT_zero hl hX, mul_one, add_zero, Vh.vhT_add hl hX h3D hcD, Wz.wzT_Om3 hl hX,
    hcT] at h
  exact h

/-- `a_c = W^{Ω₃+c}` is a base of `Ω₃` (exponent `0`). -/
theorem xiRB {c : Ordinal.{0}} (hcρ : c ≤ upsilon l) (hc : ∀ a b : Ordinal.{0}, c ∈ S.CSet a b) :
    Ro.RoBaseE S l (Om (1 + 1 + 1)) 0 (leWe (Om (1 + 1 + 1) + c)) := by
  have hWD := (xiTW hl hX hcρ hc).1
  have hW3 : leWe (Om (1 + 1 + 1) + 0) = Om (1 + 1 + 1) := by rw [add_zero, Vn.vnWe_Om3]
  have hg : ∀ a b : Ordinal.{0}, Om (1 + 1 + 1) + c ∈ S.CSet a b := fun a b =>
    CSet.add_mem (Ry.ryOm3_mem _ _) (hc a b)
  refine ⟨leWe_dvd (add_le_add le_rfl zero_le), hWD.1, ?_, fun _ _ => leWe_mem (hg _ _), ?_⟩
  · rw [hW3]
    exact (vkOmW.1.isPrincipal hWD.2.2 Ry.ryOm3_lt).trans_le (ConjT.OmW_le_A S _)
  · intro e' _ he'
    rw [nonpos_iff_eq_zero.1 he']
    exact (Om_pos one_ne_zero).trans (psiS_bounds (S := S) _ 1).1

end Rst

/-- `RoBaseE λ Ω₃ ω 0` at every restart. -/
theorem xiRBω (l : Ordinal.{0}) : Ro.RoBaseE S l (Om (1 + 1 + 1)) ω 0 := by
  have hω3 : (ω : Ordinal.{0}) < Om (1 + 1 + 1) :=
    (Lw.lw_omega_lt_SC Ph.ph_SC_Om1).trans (Om_lt_Om.2 (by
      exact lt_of_lt_of_le (lt_add_one 1) le_self_add))
  refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
  · rw [zero_add]
    exact (leWe_lt_SC vkOmW.1 vkOmW.2 (Vq.vqOm3_add_lt hω3)).1.trans_le (ConjT.OmW_le_A S _)
  · exact h'.trans_lt ((Lw.lw_omega_lt_SC Ph.ph_SC_Om1).trans (leOm1_lt_Te (S := S) _ _))

section Rst2

variable {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hl hX hA hρ

/-- **THE READING AT `e = ω`**: `Θ(ψ₂(W^{Ω₃+ω})) = ψ₁(A + ψ₂(Ω^{Ω₂+ω}))`. -/
theorem xiReadOm :
    gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (Om (1 + 1 + 1) + ω)) (Om (1 + 1))) =
      S.psi (A + S.psi (leOe (Om (1 + 1) + ω)) (Om (1 + 1))) (Om 1) := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hωρ : (ω : Ordinal.{0}) ≤ upsilon l := (xiRho_gt hl hX).le
  have hnρ : ∀ n : ℕ, (n : Ordinal.{0}) ≤ upsilon l := fun n => (natCast_lt_omega0 n).le.trans hωρ
  set P := S.psi (leOe (Om (1 + 1) + ω)) (Om (1 + 1)) with hPdef
  have hPSC : SC P := SC_psi hκ2 _
  have hPω : ω ≤ P := (Lw.lw_omega_lt_SC hPSC).le
  obtain ⟨hDω, hTω⟩ := xiTW hl hX hωρ (fun a b => Lw.lw_omega_mem a b)
  -- the upper half
  have hup := Xd.xdUp_at hl hX hA hρ _ hDω
  rw [hTω, add_assoc A 1, one_add_of_omega0_le hPω] at hup
  -- the lower half
  have hPW : IsPrincipal (· + ·) (leWe (Om (1 + 1 + 1) + ω)) := isPrincipal_add_omega0_opow _
  have h3W : Om (1 + 1 + 1) < leWe (Om (1 + 1 + 1) + ω) := by
    conv_lhs => rw [← Vn.vnWe_Om3]
    exact leWe_lt (lt_add_of_pos_right _ omega0_pos)
  have hn : ∀ n : ℕ, S.psi (A + S.psi (leOe (Om (1 + 1) + (n : Ordinal.{0})) + Om (1 + 1)) (Om (1 + 1))) (Om 1) ≤
      gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (Om (1 + 1 + 1) + ω)) (Om (1 + 1))) := by
    intro n
    obtain ⟨hDn, hTn⟩ := xiTW hl hX (hnρ n) (fun a b => Sc.scNat_mem a b n)
    have h1 := Xd.xdLow0 hl hX hA hρ hDn (xiRB hl hX (hnρ n) (fun a b => Sc.scNat_mem a b n))
    rw [hTn] at h1
    have hlt : leWe (Om (1 + 1 + 1) + (n : Ordinal.{0})) < leWe (Om (1 + 1 + 1) + ω) :=
      leWe_lt ((add_lt_add_iff_left _).2 (natCast_lt_omega0 n))
    exact h1.trans (gxTh_mono (psi_mono hκ2 (hPW hlt h3W).le).1)
  have hlow : S.psi (A + P) (Om 1) ≤
      gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (Om (1 + 1 + 1) + ω)) (Om (1 + 1))) := by
    have hlim : IsSuccLimit (A + P) := isSuccLimit_add _ hPSC.isSuccLimit
    rw [Lw.lw_psi_limit S hκ1 hlim]
    refine ciSup_le' fun e => ?_
    rcases lt_or_ge e.1 A with h1 | h1
    · exact (psi_mono (S := S) hκ1 (h1.le.trans le_self_add)).1.trans (hn 0)
    · have e1 : e.1 = A + (e.1 - A) := (Ordinal.add_sub_cancel_of_le h1).symm
      have hlt' : e.1 - A < P := by
        have h2 := e.2
        change e.1 < A + P at h2
        rw [e1] at h2
        exact (add_lt_add_iff_left _).1 h2
      obtain ⟨n, hn'⟩ := xiPstar_cof hlt'
      rw [e1]
      exact (psi_mono (S := S) hκ1 (add_le_add le_rfl hn'.le)).1.trans (hn n)
  exact le_antisymm hup hlow

/-- **No image gives the family law at `k = 0`, `e = ω`** (at the base `β = 0`). -/
theorem xiFamOm_false {Xh : Ordinal.{0} → Ordinal.{0}} (h : Vt.VtTopDyn S l 0 (Om (1 + 1 + 1)) Xh ω) : False := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hωρ : (ω : Ordinal.{0}) ≤ upsilon l := (xiRho_gt hl hX).le
  have hR := h 0 (A + 1) (xiRBω l) le_rfl (Vx.vxHatA1 (S := S) hA) (ldBlk_zero hA hρ)
  rw [gxTh_small hωρ] at hR
  unfold leTe at hR
  rw [zero_add, xiReadOm hl hX hA hρ] at hR
  set P := S.psi (leOe (Om (1 + 1) + ω)) (Om (1 + 1)) with hPdef
  set Q := leOe (Xh 0 + ω) with hQdef
  have hPSC : SC P := SC_psi hκ2 _
  have hP1 : Om 1 < P := (psiS_bounds (S := S) _ 1).1
  have hAω : Om ω ≤ A := by obtain ⟨-, rfl⟩ := Wg.wgOwnEta hl hX hA hρ; exact ConjT.OmW_le_A S _
  have hQω : ω ≤ Q := by
    have hpos : (1 : Ordinal.{0}) ≤ Om 1 * (Xh 0 + ω) := Order.one_le_iff_pos.2
      (mul_pos (Om_pos one_ne_zero) (lt_of_lt_of_le omega0_pos le_add_self))
    have := opow_le_opow_right (a := ω) omega0_pos hpos
    rwa [opow_one] at this
  rw [add_assoc A 1 Q, one_add_of_omega0_le hQω] at hR
  have hLW : leOe (Om (1 + 1) + ω) < Om ω :=
    (leOe_lt_SC vkOmW.1 (Om_lt_Om.2 one_lt_omega0) (vkOmW.1.isPrincipal vkOmW.2
        ((Lw.lw_omega_lt_SC Ph.ph_SC_Om1).trans (Om_lt_Om.2 one_lt_omega0)))).1
  have hLmem : ∀ a b : Ordinal.{0}, leOe (Om (1 + 1) + ω) ∈ S.CSet a b := fun a b =>
    leOe_mem (CSet.add_mem (mxOm2_mem _ _) (Lw.lw_omega_mem a b))
  rcases lt_trichotomy Q P with hlt | heq | hgt
  · -- `Q < P*`: the own arguments `A + p_n` are cofinal below `A + P*`
    obtain ⟨n, hn⟩ := xiPstar_cof hlt
    set p : ℕ → Ordinal.{0} := fun m => S.psi (leOe (Om (1 + 1) + (m : Ordinal.{0})) + Om (1 + 1)) (Om (1 + 1))
      with hpdef
    have hargW : ∀ m : ℕ, leOe (Om (1 + 1) + (m : Ordinal.{0})) + Om (1 + 1) < Om ω := fun m =>
      vkOmW.1.isPrincipal (((leOe_mono (add_le_add le_rfl (natCast_lt_omega0 m).le))).trans_lt hLW)
        vkOmW.2
    have hargM : ∀ (m : ℕ) (a b : Ordinal.{0}), leOe (Om (1 + 1) + (m : Ordinal.{0})) + Om (1 + 1) ∈ S.CSet a b :=
      fun m a b => CSet.add_mem (leOe_mem (CSet.add_mem (mxOm2_mem _ _) (Sc.scNat_mem a b m))) (mxOm2_mem _ _)
    have hpM : ∀ (m : ℕ) (a b : Ordinal.{0}), leOe (Om (1 + 1) + (m : Ordinal.{0})) + Om (1 + 1) < a →
        p m ∈ S.CSet a b := fun m a b ha => CSet.psi_mem ha hκ2 (mxOm2_mem _ _) (hargM m a b)
    -- `p n < p (n+1)` and `p (n+1) ≤ P*`
    have hO2 : Om (1 + 1) ≤ leOe (Om (1 + 1) + (n : Ordinal.{0})) := by
      have e2 : leOe (Om (1 + 1)) = Om (1 + 1) := Ua.uaOe_fix ruOm2_eps (Om_lt_Om.2 (lt_add_one 1))
      exact (le_of_eq e2.symm).trans (leOe_mono le_self_add)
    have hPn1 : IsPrincipal (· + ·) (leOe (Om (1 + 1) + ((n + 1 : ℕ) : Ordinal.{0}))) :=
      isPrincipal_add_omega0_opow _
    have hnn : leOe (Om (1 + 1) + (n : Ordinal.{0})) < leOe (Om (1 + 1) + ((n + 1 : ℕ) : Ordinal.{0})) :=
      leOe_lt ((add_lt_add_iff_left _).2 (Nat.cast_lt.2 (Nat.lt_succ_self n)))
    have hargs : leOe (Om (1 + 1) + (n : Ordinal.{0})) + Om (1 + 1) <
        leOe (Om (1 + 1) + ((n + 1 : ℕ) : Ordinal.{0})) + Om (1 + 1) :=
      (hPn1 hnn (hO2.trans_lt hnn)).trans_le le_self_add
    have hpp : p n < p (n + 1) := psi_lt_psi_of_mem hκ2 hargs (hargM n _ _)
    have hpP : p (n + 1) ≤ P := by
      have hPL : IsPrincipal (· + ·) (leOe (Om (1 + 1) + ω)) := isPrincipal_add_omega0_opow _
      have h1 : leOe (Om (1 + 1) + ((n + 1 : ℕ) : Ordinal.{0})) < leOe (Om (1 + 1) + ω) :=
        leOe_lt ((add_lt_add_iff_left _).2 (natCast_lt_omega0 _))
      exact (psi_mono hκ2 (hPL h1 ((hO2.trans_lt hnn).trans h1)).le).1
    have hAn : A + p n ∈ S.CSet (A + p (n + 1)) (S.psi (A + p (n + 1)) (Om 1)) :=
      CSet.add_mem ((psi_mono (S := S) hκ1 le_self_add).2 hA)
        (hpM n _ _ ((hargW n).trans_le (hAω.trans le_self_add)))
    have hs : S.psi (A + p n) (Om 1) < S.psi (A + p (n + 1)) (Om 1) :=
      psi_lt_psi_of_mem hκ1 ((add_lt_add_iff_left A).2 hpp) hAn
    have h1 : S.psi (A + Q) (Om 1) ≤ S.psi (A + p n) (Om 1) := (psi_mono hκ1 (add_le_add le_rfl hn.le)).1
    have h2 : S.psi (A + p (n + 1)) (Om 1) ≤ S.psi (A + P) (Om 1) := (psi_mono hκ1 (add_le_add le_rfl hpP)).1
    rw [← hR] at h1
    exact absurd (h1.trans_lt (hs.trans_le h2)) (lt_irrefl _)
  · exact xiShape hPSC hP1 (Xh 0) heq
  · -- `Q > P*`: `A + P*` is own
    have hAP : A + P ∈ S.CSet (A + P + 1) (S.psi (A + P + 1) (Om 1)) :=
      CSet.add_mem ((psi_mono (S := S) hκ1 (le_self_add.trans le_self_add)).2 hA)
        (CSet.psi_mem (hLW.trans_le (hAω.trans (le_self_add.trans le_self_add))) hκ2 (mxOm2_mem _ _)
          (hLmem _ _))
    have hs : S.psi (A + P) (Om 1) < S.psi (A + P + 1) (Om 1) := psi_lt_psi_of_mem hκ1 (lt_add_one _) hAP
    have hle : A + P + 1 ≤ A + Q := by rw [add_assoc]; exact add_le_add le_rfl (Order.add_one_le_of_lt hgt)
    rw [hR] at hs
    exact absurd (hs.trans_le (psi_mono hκ1 hle).1) (lt_irrefl _)

/-- The replacement law `XiTopUp` at `k = 0`, `e = ω`, `β = 0` (an instance of `xiReadOm`). -/
theorem xiTopUpOm :
    gxTh (upsilon l) (ldAtR S l) (leTe S (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + ω) 0) =
      S.psi (A + 1 + S.psi (vbT S l (0 + leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + ω))) (Om (1 + 1)))
        (Om 1) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hωρ : (ω : Ordinal.{0}) ≤ upsilon l := (xiRho_gt hl hX).le
  obtain ⟨-, hTω⟩ := xiTW hl hX hωρ (fun a b => Lw.lw_omega_mem a b)
  simp only [Nat.cast_zero, zero_add]
  unfold leTe
  rw [zero_add, hTω, xiReadOm hl hX hA hρ, add_assoc A 1,
    one_add_of_omega0_le (Lw.lw_omega_lt_SC (SC_psi hκ2 _)).le]

end Rst2

/-- **`Wg.WgTopFamAll S` (the skeleton node `skTopFam`) IS FALSE**: at the restart of `m* = L(0)` with its own `A`,
`k = 0`, the code `e = ω` has no image. -/
theorem xiTopFam_false (S : InaccSeq.{0}) : ¬ Wg.WgTopFamAll S := by
  intro h
  obtain ⟨l, hl, -, hX, hA, hρ⟩ := Xd.xdWit S
  have hωρ : (ω : Ordinal.{0}) < upsilon l := xiRho_gt hl hX
  have hω2 : (ω : Ordinal.{0}) < Om (1 + 1) :=
    (Lw.lw_omega_lt_SC Ph.ph_SC_Om1).trans (Om_lt_Om.2 (lt_add_one 1))
  obtain ⟨Xh, hT⟩ := h 0 l _ _ hl hX hA hρ ω (GxCl.small hωρ) hω2
  have e3 : ((((0 : ℕ) + 3 : ℕ)) : Ordinal.{0}) = 1 + 1 + 1 := by norm_num
  rw [e3] at hT
  exact xiFamOm_false hl hX hA hρ hT

/-- The replacement law `XiTopUp` at `e = 0`: every level `k`, every base `β ∈ D` (from `xiLawDK`). -/
theorem xiTopUp0 {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) (k : ℕ) {β : Ordinal.{0}}
    (hβD : VbD S l β) (hB : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) 0 β) :
    gxTh (upsilon l) (ldAtR S l) (leTe S (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + 0) β) =
      S.psi (A + 1 + S.psi (vbT S l (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + 0))) (Om (1 + 1))) (Om 1) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hlow := xiLow hl hX hA hρ k β hβD hB
  have hD3 : VbD S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) := xiD_Om k l
  have hβ3D : VbD S l (β + Om ((k : Ordinal.{0}) + 1 + 1 + 1)) :=
    ⟨CSet.add_mem hβD.1 hD3.1, CSet.add_mem hβD.2.1 hD3.2.1, vkOmW.1.isPrincipal hβD.2.2 hD3.2.2⟩
  have hup := Xd.xdUp_at hl hX hA hρ _ hβ3D
  unfold leTe
  rw [add_zero, Vn.vnWe_OmK]
  refine le_antisymm hup ?_
  have hT3K : vbT S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) = Om ((k : Ordinal.{0}) + 1 + 1) := by
    have h := vbT_Om (S := S) hl hX (k := k + 1 + 1) (by omega); rwa [xiC2] at h
  rw [Vh.vhT_add hl hX hβD hD3, hT3K, add_assoc A 1,
    one_add_of_omega0_le (Lw.lw_omega_lt_SC (SC_psi hκ2 _)).le]
  exact hlow

end Googology.Trans.PoR.InaccPsi.R2.Xi

#print axioms Googology.Trans.PoR.InaccPsi.R2.Xi.xiOe_cof
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xi.xiPstar_cof
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xi.xiShape
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xi.xiTW
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xi.xiRB
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xi.xiReadOm
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xi.xiFamOm_false
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xi.xiTopUpOm
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xi.xiTopFam_false
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xi.xiTopUp0
