import Googology.Trans.PoR.InaccPsi.R2.XdLaw

/-!
# THE LAW AT `k = 1`, `β = 0`: `Θ(ψ_{Ω₂}(Ω₄)) = ψ_{Ω₁}(A + 1 + ψ_{Ω₂}(Ω₃))`

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Vb.vbT S λ`, `A = A_{η_λ}` (own, `ψ₁(A) = ρ_λ`), `u_n = ψ_{Ω₄}^n(0)`,
`y_n = ψ_{Ω₃}^n(0)` (`T u_n = y_n`), `Y₃ = ψ_{Ω₃}(Ω₃)`.

* upper half: `Xd.xdUp_at` at `a = Ω₄` (`T Ω₄ = Ω₃`);
* lower half: the law at `k = 0` over the bases `u_n` (`Xd.xdLow0`: `ψ₁(A + ψ₂(y_n + Ω₂)) ≤ Θ(ψ₂(u_n + Ω₃))`, and
  `ψ₂(u_n + Ω₃) ≤ ψ₂(Ω₄)`), with `ψ₂(Ω₃) = ψ₂(Y₃) = sup_n ψ₂(y_n)` (`Vn.vnPsi2_eq`, `Uu.uuY_le_sup`).

* `xdModG` (`ω^P = P`, `P ≤ x`, `x` strongly critical ⇒ `x % P = 0`), `xdU_D`, `xdU_T` (`T u_n = y_n`),
  `xdU_base` (`RoBaseE λ Ω₃ 0 u_n`), `xdPsi3_cof` (`ζ < ψ₂(Ω₃) ⇒ ζ < ψ₂(y_n)` for some `n`),
  `xdLaw1` (**THE LAW AT `k = 1`, `β = 0`**, the node `skX0Law` at `(1, 0)`), `xdLaw1_val`.

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Vk Googology.Trans.PoR.InaccPsi.R2.Vb

variable {S : InaccSeq.{0}}

/-- A strongly critical `x ≥ P` with `ω^P = P` is a multiple of `P`. -/
theorem xdModG {P x : Ordinal.{0}} (hP : ω ^ P = P) (hS : SC x) (h : P ≤ x) : x % P = 0 := by
  have e := gg_SC_eps hS
  have hc : P ≤ x := h
  rw [← hP] at h
  rw [← e, ← Ordinal.add_sub_cancel_of_le hc, opow_add, hP]
  exact Ordinal.mul_mod _ _

theorem xdE4 : ((1 : ℕ) : Ordinal.{0}) + 1 + 1 + 1 = 1 + 1 + 1 + 1 := by rw [Nat.cast_one]

theorem xdOm4C (a b : Ordinal.{0}) : Om (1 + 1 + 1 + 1 : Ordinal.{0}) ∈ S.CSet a b := by
  have h := Vn.vnOmK3_mem (S := S) 1 a b; rwa [xdE4] at h

theorem xdOm4_lt_W : Om (1 + 1 + 1 + 1 : Ordinal.{0}) < Om ω := by
  have h := Wv.wvOmK_lt_W 1; rwa [xdE4] at h

theorem xdOm34 : Om (1 + 1 + 1 : Ordinal.{0}) < Om (1 + 1 + 1 + 1) := Om_lt_Om.2 (lt_add_one _)

/-- The iterates `u_n = ψ_{Ω₄}^n(0)`. -/
theorem xdU_lt (n : ℕ) : (fun x => S.psi x (Om (1 + 1 + 1 + 1)))^[n] 0 < Om (1 + 1 + 1 + 1) :=
  (Vn.vnIt_lt (s := 1 + 1 + 1) xdOm4C n).trans (psi_lt (InR_Om_succ _) _)

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

theorem xdU_D (n : ℕ) : VbD S l ((fun x => S.psi x (Om (1 + 1 + 1 + 1)))^[n] 0) := by
  have hlt := xdU_lt (S := S) n
  have hW := hlt.trans xdOm4_lt_W
  exact ⟨Vn.vnIt_mem xdOm4C n _ _ (hW.le.trans (ConjT.OmW_le_A S _)),
    Vn.vnIt_mem xdOm4C n _ _ hW.le, hW⟩

/-- **`T u_n = y_n`.** -/
theorem xdU_T : ∀ n : ℕ, vbT S l ((fun x => S.psi x (Om (1 + 1 + 1 + 1)))^[n] 0) =
    (fun x => S.psi x (Om (1 + 1 + 1)))^[n] 0 := by
  have e2 : ((2 : ℕ) : Ordinal.{0}) + 1 + 1 = 1 + 1 + 1 + 1 := by norm_num
  have e2' : ((2 : ℕ) : Ordinal.{0}) + 1 = 1 + 1 + 1 := by norm_num
  intro n
  induction n with
  | zero => exact Vh.vhT_zero hl hX
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    have hn : (fun x => S.psi x (Om (1 + 1 + 1 + 1)))^[n] 0 ∈
        S.CSet ((fun x => S.psi x (Om (1 + 1 + 1 + 1)))^[n] 0)
          (S.psi ((fun x => S.psi x (Om (1 + 1 + 1 + 1)))^[n] 0) (Om (((2 : ℕ) : Ordinal.{0}) + 1 + 1))) := by
      rw [e2]; exact Vn.vnIt_mem xdOm4C n _ _ le_rfl
    have h := (vbT_atom hl hX (k := 2) (by norm_num) (xdU_D hl hX n) hn).1
    rwa [e2, e2'] at h

/-- `RoBaseE λ Ω₃ 0 u_n`. -/
theorem xdU_base (n : ℕ) : Ro.RoBaseE S l (Om (1 + 1 + 1)) 0 ((fun x => S.psi x (Om (1 + 1 + 1 + 1)))^[n] 0) := by
  have hW3 : Le.leWe (Om (1 + 1 + 1) + 0) = Om (1 + 1 + 1) := by rw [add_zero, Vn.vnWe_Om3]
  have h3 : (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := (add_pos_of_right zero_lt_one _).ne'
  have h3ε : ω ^ Om (1 + 1 + 1) = (Om (1 + 1 + 1) : Ordinal.{0}) := gg_SC_eps (SC_Om h3)
  have h4 : (1 + 1 + 1 + 1 : Ordinal.{0}) ≠ 0 := (add_pos_of_right zero_lt_one _).ne'
  have hlt := xdU_lt (S := S) n
  have hsum : (fun x => S.psi x (Om (1 + 1 + 1 + 1)))^[n] 0 + Om (1 + 1 + 1) < Om (1 + 1 + 1 + 1) :=
    (SC_Om h4).isPrincipal hlt xdOm34
  refine ⟨?_, (xdU_D hl hX n).1, ?_, fun d hd => Vn.vnIt_mem xdOm4C n _ _ le_self_add, ?_⟩
  · rw [hW3, Ordinal.dvd_iff_mod_eq_zero]
    cases n with
    | zero => exact Ordinal.zero_mod _
    | succ n =>
      rw [Function.iterate_succ_apply']
      have hb := psiS_bounds (S := S) ((fun x => S.psi x (Om (1 + 1 + 1 + 1)))^[n] 0) (1 + 1 + 1)
      exact xdModG h3ε (SC_psi (InR_Om_succ _) _) hb.1.le
  · rw [hW3]
    exact (hsum.trans xdOm4_lt_W).trans_le (ConjT.OmW_le_A S _)
  · intro e' _ he'
    rw [nonpos_iff_eq_zero.1 he']
    exact (Om_pos one_ne_zero).trans (psiS_bounds (S := S) _ 1).1

end Rst

/-- **`ζ < ψ₂(Ω₃) ⇒ ζ < ψ₂(y_n)` for some `n`** (`ψ₂(Ω₃) = ψ₂(Y₃) = sup_n ψ₂(y_n)`). -/
theorem xdPsi3_cof {ζ : Ordinal.{0}} (hζ : ζ < S.psi (Om (1 + 1 + 1)) (Om (1 + 1))) :
    ∃ n : ℕ, ζ < S.psi ((fun x => S.psi x (Om (1 + 1 + 1)))^[n] 0) (Om (1 + 1)) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hκ3 : S.InR (Om (1 + 1 + 1 : Ordinal.{0})) := InR_Om_succ _
  have h2 : Om (1 + 1) < S.psi (Om (1 + 1 + 1)) (Om (1 + 1 + 1)) := (psiS_bounds (S := S) _ (1 + 1)).1
  have e := Vn.vnPsi2_eq (S := S) (s := 1 + 1) h2 (psi_lt hκ3 _).le le_rfl
  rw [e] at hζ
  have hlim : IsSuccLimit (S.psi (Om (1 + 1 + 1)) (Om (1 + 1 + 1))) := (SC_psi hκ3 _).isSuccLimit
  rw [Lw.lw_psi_limit S hκ2 hlim] at hζ
  have hbdd : BddAbove (range fun e : Iio (S.psi (Om (1 + 1 + 1)) (Om (1 + 1 + 1))) =>
      S.psi e.1 (Om (1 + 1))) := ⟨Om (1 + 1), by rintro _ ⟨e, rfl⟩; exact (psi_lt hκ2 _).le⟩
  haveI : Nonempty (Iio (S.psi (Om (1 + 1 + 1)) (Om (1 + 1 + 1)))) := ⟨⟨0, (SC_psi hκ3 _).1⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff hbdd).1 hζ
  obtain ⟨n, hn⟩ := (lt_ciSup_iff (Uu.uuIt_bdd (S := S) (1 + 1))).1
    (e.2.trans_le (Uu.uuY_le_sup (S := S) (s := 1 + 1) Uu.uuThree_lt))
  exact ⟨n, he.trans_le (psi_mono hκ2 hn.le).1⟩

/-- **THE LAW AT `k = 1`, `β = 0`, as a value**: `Θ(ψ₂(Ω₄)) = ψ₁(A + ψ₂(Ω₃))`. -/
theorem xdLaw1_val {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1 + 1)) (Om (1 + 1))) =
      S.psi (A + S.psi (Om (1 + 1 + 1)) (Om (1 + 1))) (Om 1) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have h4 : (1 + 1 + 1 + 1 : Ordinal.{0}) ≠ 0 := (add_pos_of_right zero_lt_one _).ne'
  set Xh := S.psi (Om (1 + 1 + 1)) (Om (1 + 1)) with hXhdef
  have hXSC : SC Xh := SC_psi hκ2 _
  have hXω : ω ≤ Xh := (Lw.lw_omega_lt_SC hXSC).le
  -- the upper half
  have hD4 : VbD S l (Om (1 + 1 + 1 + 1)) := by
    have h := vbD_Om (S := S) (l := l) 3; rwa [show ((3 : ℕ) : Ordinal.{0}) + 1 = 1 + 1 + 1 + 1 by norm_num] at h
  have hT4 : vbT S l (Om (1 + 1 + 1 + 1)) = Om (1 + 1 + 1) := by
    have h := vbT_Om (S := S) hl hX (k := 3) (by norm_num)
    rwa [show ((3 : ℕ) : Ordinal.{0}) + 1 = 1 + 1 + 1 + 1 by norm_num,
      show ((3 : ℕ) : Ordinal.{0}) = 1 + 1 + 1 by norm_num] at h
  have hup := xdUp_at hl hX hA hρ _ hD4
  rw [hT4, add_assoc A 1, one_add_of_omega0_le hXω] at hup
  -- the lower half
  have hbig : ∀ ζ, ζ < Xh → S.psi (A + ζ) (Om 1) ≤
      gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1 + 1)) (Om (1 + 1))) := by
    intro ζ hζ
    obtain ⟨n, hn⟩ := xdPsi3_cof hζ
    have h1 := xdLow0 hl hX hA hρ (xdU_D hl hX n) (xdU_base hl hX n)
    rw [xdU_T hl hX n] at h1
    have hsum : (fun x => S.psi x (Om (1 + 1 + 1 + 1)))^[n] 0 + Om (1 + 1 + 1) ≤ Om (1 + 1 + 1 + 1) :=
      ((SC_Om h4).isPrincipal (xdU_lt n) xdOm34).le
    have h2 := gxTh_mono (Z := upsilon l) (At := ldAtR S l) (psi_mono hκ2 hsum).1
    have h0 : ζ ≤ S.psi ((fun x => S.psi x (Om (1 + 1 + 1)))^[n] 0 + Om (1 + 1)) (Om (1 + 1)) :=
      hn.le.trans (psi_mono hκ2 le_self_add).1
    exact ((psi_mono (S := S) Low.InR_Om_one (add_le_add le_rfl h0)).1.trans h1).trans h2
  have hlow : S.psi (A + Xh) (Om 1) ≤
      gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1 + 1)) (Om (1 + 1))) := by
    have hlim : IsSuccLimit (A + Xh) := isSuccLimit_add _ hXSC.isSuccLimit
    rw [Lw.lw_psi_limit S Low.InR_Om_one hlim]
    refine ciSup_le' fun e => ?_
    rcases lt_or_ge e.1 A with h1 | h1
    · have h0 := hbig 0 hXSC.1
      rw [add_zero] at h0
      exact (psi_mono (S := S) Low.InR_Om_one h1.le).1.trans h0
    · have e1 : e.1 = A + (e.1 - A) := (Ordinal.add_sub_cancel_of_le h1).symm
      have hlt' : e.1 - A < Xh := by
        have h2 := e.2
        change e.1 < A + Xh at h2
        rw [e1] at h2
        exact (add_lt_add_iff_left _).1 h2
      rw [e1]
      exact hbig _ hlt'
  exact le_antisymm hup hlow

/-- **THE LAW AT `k = 1`, `β = 0`** (the node `skX0Law` at `(1, 0)`, image `X̂⁰_1(0) = ψ₂(Ω₃)`). -/
theorem xdLaw1 {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    Wg.WgTopAt S l (Om (((1 : ℕ) : Ordinal.{0}) + 1 + 1 + 1)) (Wv.wvX0 S l 1 0) 0 0 := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hXSC : SC (S.psi (Om (1 + 1 + 1)) (Om (1 + 1))) := SC_psi hκ2 _
  have hval := xdLaw1_val hl hX hA hρ
  intro Â hÂ hb
  have hX0 : Wv.wvX0 S l 1 0 = S.psi (Om (1 + 1 + 1)) (Om (1 + 1)) := by
    unfold Wv.wvX0; rw [Vh.vhT_zero hl hX, zero_add, Nat.cast_one]
  have hÂe : Â = A + 1 := by
    have e0 := ldBlk_zero hA hρ
    have hown := Vx.vxHatA1 hA
    exact le_antisymm (Sf.sfArg_le hÂ hown (by rw [← hb, e0]))
      (Sf.sfArg_le hown hÂ (by rw [← hb, e0]))
  rw [hX0, gxTh_zero, xdE4]
  simp only [add_zero]
  rw [Ua.uaOe_fix (gg_SC_eps hXSC) (psiS_bounds (S := S) _ 1).1]
  unfold Le.leTe
  have hW4 : Le.leWe (Om (1 + 1 + 1 + 1 : Ordinal.{0})) = Om (1 + 1 + 1 + 1) := by
    have h := Vn.vnWe_OmK 1; rwa [xdE4] at h
  rw [hW4, zero_add, hval, hÂe, add_assoc A 1 (S.psi (Om (1 + 1 + 1)) (Om (1 + 1))),
    one_add_of_omega0_le (Lw.lw_omega_lt_SC hXSC).le]

end Googology.Trans.PoR.InaccPsi.R2.Xd

#print axioms Googology.Trans.PoR.InaccPsi.R2.Xd.xdModG
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xd.xdU_T
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xd.xdU_base
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xd.xdPsi3_cof
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xd.xdLaw1_val
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xd.xdLaw1
