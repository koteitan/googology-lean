import Googology.Trans.PoR.InaccPsi.R2.WlLow
import Googology.Trans.PoR.InaccPsi.R2.VxDyn
import Googology.Trans.PoR.InaccPsi.R2.VhAgree

/-!
# The images `X̂_e(β)` of the top law at `Ω_{k+3}`: every image is below `θ`; the naive image `T(Y_{k+3})`
is refuted at every `k ≥ 1`; the intrinsic candidate `X̂⁰_k(β) = ψ_{Ω₂}(T β + Ω_{k+2})`

`Θ = gxTh ρ_λ (ldAtR λ)`, `θ = ψ_{Ω₂}(Ω_ω)`, `T = Vb.vbT S λ` (the image one level down), `Ω^x = leOe x`,
`T_X(β) = ψ_{Ω₂}(β + W^X)` (`leTe`), `Y_{s+2} = ψ_{Ω_{s+2}}(Ω_{s+2})` (`Uj.ujY S s`); a restart `λ`
(`IsRestartIdx λ`, `ρ_λ < P(η_x)`) with `ψ_{Ω₁}(A) = ρ_λ`, `A ∈ Cl(A, ψ_{Ω₁}(A))`.

* `wvRead_lt_th` (**every atom `t < θ` read as `Θ(t) = ψ_{Ω₁}(A + x)` has `x < θ`**: `Θ(t) < Θ(θ) = ψ_{Ω₁}(A + θ)`,
  `Wl.wlThVal`);
* `wvImg_lt_thE` (**every image of the top law at the base `0` below `θ` has `Ω^{X̂ + Θ e} < θ`**),
  `wvImg_lt_th` (`e = 0`, every level `k`: `Ω^{X̂} < θ`);
* `wvNoBig` (**no image `Z ≥ Ω₂` at any level `k`**), `wvT_Y` (`T(Y_{k+3}) = Y_{k+2}` at every `k`), `wvNoT`
  (**NO-GO: the naive image `X̂ = T(Y(0)) = T(ψ_{Ω_{k+3}}(Ω_{k+3})) = Y_{k+2}` fails at EVERY `k ≥ 1`**; sharpens
  `Wb.wbNoY_ge1`, which gives only some `k ≥ 1`);
* `wvX0` (**the intrinsic candidate `X̂⁰_k(β) = ψ_{Ω₂}(T β + Ω_{k+2})`**; at `k = 0` it is `T(ψ_{Ω₃}(β + Ω₃))` where
  `T` passes through `ψ_{Ω₃}`), `wvX0_base0`, `wvX0_law00` (the law holds with it at `k = 0`, `β = 0`),
  `wvX0_lt_th` (`Ω^{X̂⁰_k(0)} < θ` at every `k`: consistent with `wvImg_lt_th`), `wvX0_sep` (**REFUTE-FIRST tests
  passed**: `Ω^{X̂⁰_0(0)} ≤ Y₂ < Ω^{X̂⁰_0(Ω₃)}`, the constraints of `Vx.vxDyn_le0`, `Vx.vxDyn_gtOm3`, `Wg.wgSep01`).

No new axiom.  New definition: `wvX0` (a candidate image; no statement of the repo depends on it).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Uj Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vn Googology.Trans.PoR.InaccPsi.R2.Ug

variable {S : InaccSeq.{0}}

/-- **The intrinsic candidate image at `e = 0`**: `X̂⁰_k(β) = ψ_{Ω₂}(T β + Ω_{k+2})`. -/
noncomputable def wvX0 (S : InaccSeq.{0}) (l : Ordinal.{0}) (k : ℕ) (β : Ordinal.{0}) : Ordinal.{0} :=
  S.psi (Vb.vbT S l β + Om ((k : Ordinal.{0}) + 1 + 1)) (Om (1 + 1))

theorem wvOmK_lt_W (k : ℕ) : Om ((k : Ordinal.{0}) + 1 + 1 + 1) < Om ω := Om_lt_Om.2 (vkNat_lt_omega k)

/-- `ψ_{Ω₂}(Ω_{k+3})` is an atom of `λ` below `θ`. -/
theorem wvAt0 (l : Ordinal.{0}) (k : ℕ) :
    S.psi (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Om (1 + 1)) ∈ ldAtR S l ∧
      S.psi (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Om (1 + 1)) < ConjT.th S :=
  ⟨⟨_, vnOmK3_mem k _ _, (wvOmK_lt_W k).trans_le (ConjT.OmW_le_A S _), rfl⟩,
    psi_lt_psi_of_mem (InR_Om_succ 1) (wvOmK_lt_W k) (vnOmK3_mem k _ _)⟩

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- `T(Y_{k+3}) = Y_{k+2}` at every `k`. -/
theorem wvT_Y (k : ℕ) : Vb.vbT S l (ujY S ((k : Ordinal.{0}) + 1)) = ujY S (k : Ordinal.{0}) := by
  have hk : 1 ≤ k + 1 := Nat.le_add_left 1 k
  have hc : ((k + 1 : ℕ) : Ordinal.{0}) = (k : Ordinal.{0}) + 1 := by push_cast; rfl
  have hD : Vb.VbD S l (Om (((k + 1 : ℕ) : Ordinal.{0}) + 1 + 1)) := by
    have h := Vb.vbD_Om (S := S) (l := l) (k + 1 + 1)
    rw [hc]; push_cast at h; exact h
  have hdn : Om (((k + 1 : ℕ) : Ordinal.{0}) + 1 + 1) ∈ S.CSet (Om (((k + 1 : ℕ) : Ordinal.{0}) + 1 + 1))
      (S.psi (Om (((k + 1 : ℕ) : Ordinal.{0}) + 1 + 1)) (Om (((k + 1 : ℕ) : Ordinal.{0}) + 1 + 1))) := by
    rw [hc]; exact vnOmK3_mem k _ _
  have h := (Vb.vbT_atom hl hX hk hD hdn).1
  have hO := Vb.vbT_Om (S := S) hl hX (k := k + 1 + 1) (by omega)
  push_cast at hO
  rw [hc, hO] at h
  unfold ujY
  exact h

/-- `X̂⁰_k(0) = ψ_{Ω₂}(Ω_{k+2})`. -/
theorem wvX0_base0 (k : ℕ) : wvX0 S l k 0 = S.psi (Om ((k : Ordinal.{0}) + 1 + 1)) (Om (1 + 1)) := by
  unfold wvX0; rw [Vh.vhT_zero hl hX, zero_add]

/-- `X̂⁰_0(0) = Y₂`. -/
theorem wvX0_zero : wvX0 S l 0 0 = S.psi (Om (1 + 1)) (Om (1 + 1)) := by
  rw [wvX0_base0 hl hX 0, Nat.cast_zero, zero_add]

/-- **`Ω^{X̂⁰_k(0)} < θ` at every level `k`.** -/
theorem wvX0_lt_th (k : ℕ) : leOe (wvX0 S l k 0) < ConjT.th S := by
  rw [wvX0_base0 hl hX k]
  have hSC : SC (S.psi (Om ((k : Ordinal.{0}) + 1 + 1)) (Om (1 + 1))) := SC_psi (InR_Om_succ 1) _
  rw [Ua.uaOe_fix (gg_SC_eps hSC) (psiS_bounds (S := S) _ 1).1]
  exact psi_lt_psi_of_mem (InR_Om_succ 1) (Om_lt_Om.2 (Vb.vbNat_lt_omega k)) (vnOmK_mem k _ _)

/-- **REFUTE-FIRST tests of the candidate at `k = 0`**: `Ω^{X̂⁰_0(0)} ≤ Y₂ < Ω^{X̂⁰_0(Ω₃)}` (the constraints of
`Vx.vxDyn_le0`, `Vx.vxDyn_gtOm3`; with `Wg.wgSep01`: `X̂⁰_0(0) ≤ Y₂ < X̂⁰_0(Ω₃)`), so the candidate is not constant
(`Vx.vxDyn_nonconst`, `Vq.vqNoTop_Om3`, `Vn.vnTop_Om3`). -/
theorem wvX0_sep :
    leOe (wvX0 S l 0 0) ≤ S.psi (Om (1 + 1)) (Om (1 + 1)) ∧ wvX0 S l 0 0 ≤ S.psi (Om (1 + 1)) (Om (1 + 1)) ∧
      S.psi (Om (1 + 1)) (Om (1 + 1)) < wvX0 S l 0 (Om (1 + 1 + 1)) ∧
      S.psi (Om (1 + 1)) (Om (1 + 1)) < leOe (wvX0 S l 0 (Om (1 + 1 + 1))) := by
  have hY2SC : SC (S.psi (Om (1 + 1)) (Om (1 + 1))) := SC_psi (InR_Om_succ 1) _
  have hfix := Ua.uaOe_fix (gg_SC_eps hY2SC) (psiS_bounds (S := S) (Om (1 + 1)) 1).1
  have hgt : S.psi (Om (1 + 1)) (Om (1 + 1)) < wvX0 S l 0 (Om (1 + 1 + 1)) := by
    unfold wvX0
    have hO := Vb.vbT_Om (S := S) hl hX (k := 2) (by norm_num)
    have h2 : ((2 : ℕ) : Ordinal.{0}) = 1 + 1 := by norm_num [one_add_one_eq_two]
    rw [h2] at hO
    rw [hO, Nat.cast_zero, zero_add]
    have h0 : (1 + 1 : Ordinal.{0}) ≠ 0 := (add_pos zero_lt_one zero_lt_one).ne'
    exact psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right _ (Om_pos h0))
      (mxOm2_mem _ _)
  rw [wvX0_zero hl hX, hfix]
  exact ⟨le_rfl, le_rfl, hgt, hgt.trans_le (ujLe_Oe _)⟩

/-- **The candidate at `k = 1` passes the test of `wvImg1_gt`**: `Y₂ + Y₂ < Ω^{X̂⁰_1(0)} < θ`. -/
theorem wvX0_one_in :
    S.psi (Om (1 + 1)) (Om (1 + 1)) + S.psi (Om (1 + 1)) (Om (1 + 1)) < leOe (wvX0 S l 1 0) ∧
      leOe (wvX0 S l 1 0) < ConjT.th S := by
  refine ⟨?_, wvX0_lt_th hl hX 1⟩
  rw [wvX0_base0 hl hX 1, Nat.cast_one]
  have hSC : SC (S.psi (Om (1 + 1 + 1)) (Om (1 + 1))) := SC_psi (InR_Om_succ 1) _
  rw [Ua.uaOe_fix (gg_SC_eps hSC) (psiS_bounds (S := S) _ 1).1]
  have hY : S.psi (Om (1 + 1)) (Om (1 + 1)) < S.psi (Om (1 + 1 + 1)) (Om (1 + 1)) :=
    psi_lt_psi_of_mem (InR_Om_succ 1) (Om_lt_Om.2 (lt_add_one _)) (mxOm2_mem _ _)
  exact hSC.isPrincipal hY hY

section Own

variable {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hA hρ

/-- **Every atom `t < θ` read as `Θ(t) = ψ_{Ω₁}(A + x)` has `x < θ`.** -/
theorem wvRead_lt_th {t x : Ordinal.{0}} (ht : t ∈ ldAtR S l) (htθ : t < ConjT.th S)
    (hx : gxTh (upsilon l) (ldAtR S l) t = S.psi (A + x) (Om 1)) : x < ConjT.th S := by
  have h1 := gxTh_lt (Z := upsilon l) (GxCl.atom ht) htθ
  rw [Wl.wlThVal hl hX hA hρ, hx] at h1
  by_contra hc
  push Not at hc
  exact absurd h1 (not_lt.2 (psi_mono (S := S) Low.InR_Om_one (add_le_add le_rfl hc : A + ConjT.th S ≤ A + x)).1)

/-- **Every image of the top law at the base `0` whose atom is below `θ` has `Ω^{X̂ + Θ e} < θ`.** -/
theorem wvImg_lt_thE {X Z e : Ordinal.{0}} (hat : leTe S (X + e) 0 ∈ ldAtR S l)
    (hθ : leTe S (X + e) 0 < ConjT.th S) (hT : Wg.WgTopAt S l X Z e 0) :
    leOe (Z + gxTh (upsilon l) (ldAtR S l) e) < ConjT.th S := by
  have h := hT (A + 1) (Vx.vxHatA1 hA) (ldBlk_zero hA hρ)
  rw [add_assoc] at h
  exact le_add_self.trans_lt (wvRead_lt_th hl hX hA hρ hat hθ h)

/-- **`e = 0`, every level `k`: every image `Z` of the top law at `Ω_{k+3}` at the base `0` has `Ω^Z < θ`.** -/
theorem wvImg_lt_th (k : ℕ) {Z : Ordinal.{0}} (hT : Wg.WgTopAt S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) Z 0 0) :
    leOe Z < ConjT.th S := by
  have hE : leTe S (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + 0) 0 =
      S.psi (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Om (1 + 1)) := by
    unfold leTe; rw [add_zero, zero_add, vnWe_OmK k]
  have h := wvImg_lt_thE hl hX hA hρ (hE ▸ (wvAt0 l k).1) (hE ▸ (wvAt0 l k).2) hT
  rwa [gxTh_zero, add_zero] at h

/-- **No image `Z ≥ Ω₂` at any level `k`.** -/
theorem wvNoBig (k : ℕ) {Z : Ordinal.{0}} (hZ : Om (1 + 1) ≤ Z) :
    ¬ Wg.WgTopAt S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) Z 0 0 := fun hT => by
  have h := wvImg_lt_th hl hX hA hρ k hT
  have hθ2 : ConjT.th S < Om (1 + 1) := psi_lt (InR_Om_succ 1) _
  exact absurd ((hθ2.trans_le hZ).trans_le (ujLe_Oe Z)) (not_lt.2 h.le)

/-- **NO-GO for the naive image `T(Y(0))` at every `k ≥ 1`**: the top law at `Ω_{k+3}`, base `0`, with the image
`T(ψ_{Ω_{k+3}}(Ω_{k+3})) = Y_{k+2}` is false. -/
theorem wvNoT (k : ℕ) (hk : 1 ≤ k) :
    ¬ Wg.WgTopAt S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Vb.vbT S l (ujY S ((k : Ordinal.{0}) + 1))) 0 0 := by
  rw [wvT_Y hl hX k]
  refine wvNoBig hl hX hA hρ k ?_
  have hk' : (1 : Ordinal.{0}) ≤ (k : Ordinal.{0}) := by exact_mod_cast hk
  exact (Om_le_Om.2 (add_le_add hk' le_rfl)).trans (ujY_gt (S := S) (k : Ordinal.{0})).le

/-- **The candidate satisfies the law at `k = 0`, `β = 0`** (`Wg.wgTop0_base0`). -/
theorem wvX0_law00 : Wg.WgTopAt S l (Om (1 + 1 + 1)) (wvX0 S l 0 0) 0 0 := by
  rw [wvX0_zero hl hX]; exact Wg.wgTop0_base0 hl hX hA hρ

/-- **Lower test at `k = 1`**: every image `Z` of the top law at `Ω₄`, base `0`, has `Y₂ + Y₂ < Ω^Z`
(`Θ(ψ₂(Ω₃ + Y₃)) = ψ₁(A + 1 + Y₂ + Y₂)`, `Vq.vqRead_Om3Y3`, and `ψ₂(Ω₃ + Y₃) < ψ₂(Ω₄)`); with `wvImg_lt_th`:
`Y₂ + Y₂ < Ω^Z < θ`.  The candidate `X̂⁰_1(0) = ψ₂(Ω₃)` lies in this interval (`wvX0_one_in`). -/
theorem wvImg1_gt {Z : Ordinal.{0}} (hT : Wg.WgTopAt S l (Om (1 + 1 + 1 + 1)) Z 0 0) :
    S.psi (Om (1 + 1)) (Om (1 + 1)) + S.psi (Om (1 + 1)) (Om (1 + 1)) < leOe Z := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hW4 : leWe (Om (1 + 1 + 1 + 1 : Ordinal.{0})) = Om (1 + 1 + 1 + 1) := by
    have h := vnWe_OmK 1; rw [Nat.cast_one] at h; exact h
  have h := hT (A + 1) (Vx.vxHatA1 hA) (ldBlk_zero hA hρ)
  rw [add_zero, gxTh_zero, add_zero] at h
  unfold leTe at h
  rw [zero_add, hW4] at h
  have hr := Vq.vqRead_Om3Y3 hl hX hA hρ
  have h4 : (1 + 1 + 1 + 1 : Ordinal.{0}) ≠ 0 := (add_pos_of_right zero_lt_one _).ne'
  have h34 : Om (1 + 1 + 1 : Ordinal.{0}) < Om (1 + 1 + 1 + 1) := Om_lt_Om.2 (lt_add_one _)
  have hY3 : ugY S < Om (1 + 1 + 1) := ugY_lt_Om3
  have hYmem : ∀ a b, Om (1 + 1 + 1) < a → ugY S ∈ S.CSet a b := fun a b ha =>
    CSet.psi_mem ha (InR_Om_succ (1 + 1)) (Ry.ryOm3_mem _ _) (Ry.ryOm3_mem _ _)
  have hlt4 : Om (1 + 1 + 1) + ugY S < Om (1 + 1 + 1 + 1) :=
    (SC_Om h4).isPrincipal h34 (hY3.trans h34)
  have hat : S.psi (Om (1 + 1 + 1) + ugY S) (Om (1 + 1)) ∈ ldAtR S l :=
    ⟨_, CSet.add_mem (Ry.ryOm3_mem _ _) (hYmem _ _ (Ry.ryOm3_lt.trans_le (ConjT.OmW_le_A S _))),
      (vkOmW.1.isPrincipal Ry.ryOm3_lt (hY3.trans Ry.ryOm3_lt)).trans_le (ConjT.OmW_le_A S _), rfl⟩
  have hψ : S.psi (Om (1 + 1 + 1) + ugY S) (Om (1 + 1)) < S.psi (Om (1 + 1 + 1 + 1)) (Om (1 + 1)) :=
    psi_lt_psi_of_mem (InR_Om_succ 1) hlt4 (CSet.add_mem (Ry.ryOm3_mem _ _) (hYmem _ _ h34))
  have hlt := gxTh_lt (Z := upsilon l) (GxCl.atom hat) hψ
  rw [hr, h] at hlt
  have hargs : A + 1 + S.psi (Om (1 + 1)) (Om (1 + 1)) + S.psi (Om (1 + 1)) (Om (1 + 1)) < A + 1 + leOe Z := by
    by_contra hc
    push Not at hc
    exact absurd hlt (not_lt.2 (psi_mono (S := S) hκ1 hc).1)
  rw [add_assoc (A + 1)] at hargs
  exact (add_lt_add_iff_left _).1 hargs

end Own

end Rst

/-- **Non-vacuity at the witness restart** (`m* = L(0)`): a restart with an own `A` where the candidate satisfies
the law at `k = 0`, `β = 0`, and where the naive image fails at every `k ≥ 1`. -/
theorem wvWit (S : InaccSeq.{0}) :
    ∃ l A : Ordinal.{0}, IsRestartIdx l ∧ upsilon l = Nc.ncL S 0 ∧ A ∈ S.CSet A (S.psi A (Om 1)) ∧
      S.psi A (Om 1) = upsilon l ∧ Wg.WgTopAt S l (Om (1 + 1 + 1)) (wvX0 S l 0 0) 0 0 ∧
      ∀ k : ℕ, 1 ≤ k →
        ¬ Wg.WgTopAt S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Vb.vbT S l (ujY S ((k : Ordinal.{0}) + 1))) 0 0 := by
  obtain ⟨l, hl, e⟩ := Cv.cvM_restart (S := S)
  have hX : upsilon l < Pv S (Om ω + Nc.ncPp S * 1) := by
    rw [← e, ← Lw.lw_L_eq]; exact Rl.rlM_lt_L1
  have hL1 : Nc.ncL S 1 = Bc.bcC S 0 := by simp [Bc.bcC]
  have hn : upsilon l < Bc.bcC S (0 + 1) := by
    rw [← e]
    exact (Rl.rlM_lt_L1 (S := S)).trans_le (hL1 ▸ Bc.bcC_mono (S := S) (Nat.zero_le _))
  obtain ⟨hA, hρ⟩ := Vq.vqA_spec hl hX (n := 0) hn
  exact ⟨l, _, hl, e.symm, hA, hρ, wvX0_law00 hl hX hA hρ, fun k hk => wvNoT hl hX hA hρ k hk⟩

end Googology.Trans.PoR.InaccPsi.R2.Wv

#print axioms Googology.Trans.PoR.InaccPsi.R2.Wv.wvAt0
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wv.wvT_Y
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wv.wvX0_base0
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wv.wvX0_lt_th
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wv.wvX0_sep
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wv.wvX0_one_in
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wv.wvRead_lt_th
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wv.wvImg_lt_thE
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wv.wvImg_lt_th
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wv.wvNoBig
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wv.wvNoT
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wv.wvX0_law00
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wv.wvImg1_gt
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wv.wvWit
