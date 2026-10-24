import Googology.Trans.PoR.InaccPsi.R2.SnAt

/-!
# The towers below `ε_{κ+1}`: the cofinal sequence of the limit `ε_{Ω₂+1}`

For a strongly critical `κ`: `t_0 = 1`, `t_{k+1} = ω^{κ·t_k}` (`sqTw κ k`; at `κ = Ω₂` this is `W^{t_k}`, at
`κ = Ω₁` it is `Ω^{t_k}`).  `ε = ε_{Ω₂+1} = veblen 1 (Ω₂+1)`, `ε̂ = ε_{Ω₁+1} = veblen 1 (Ω₁+1)`.

* `sqTw_lt` (**`t_k < ε_{κ+1}`**), `sqTw_lt_succ`, `sqTw_mono`, `sqTw_cof` (**every `x < ε_{κ+1}` is below some
  `t_k`**: `ε_{κ+1}` is the least fixed point of `ω^·` above `κ`, by `Mathlib`'s `deriv_succ`, `lt_nfp_iff`);
* `sqTw_cl` (`t_k` is a code over every `Q > 1`), `sqTw_mem` (in every `CSet`), `sqEps_cl`, `sqEps_mem`,
  `sqEpsH_cl`, `sqEpsH_mem` (the same for `ε`, `ε̂`), `sqEps_We` (**`W^ε = ε`**), `sqEpsH_Oe` (`Ω^{ε̂} = ε̂`);
* `sqThH_tw` (**`Θ̂(t_k) = t̂_k`**: the image of the `Ω₂`-tower is the `Ω₁`-tower, by `Sg.sgThH_cnf`).

No new axiom.  New definition: `sqTw`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Sg

variable {S : InaccSeq.{0}}

/-- **The tower** `t_0 = 1`, `t_{k+1} = ω^{κ·t_k}`. -/
noncomputable def sqTw (κ : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => 1
  | k + 1 => ω ^ (κ * sqTw κ k)

theorem sqTw_zero (κ : Ordinal.{0}) : sqTw κ 0 = 1 := rfl
theorem sqTw_succ (κ : Ordinal.{0}) (k : ℕ) : sqTw κ (k + 1) = ω ^ (κ * sqTw κ k) := rfl

theorem sqTw_We (k : ℕ) : sqTw (Om (1 + 1)) (k + 1) = leWe (sqTw (Om (1 + 1)) k) := rfl
theorem sqTw_Oe (k : ℕ) : sqTw (Om 1) (k + 1) = leOe (sqTw (Om 1) k) := rfl

section Gen

variable {κ : Ordinal.{0}} (hκ : SC κ)

include hκ

theorem sqOne_lt : (1 : Ordinal.{0}) < κ := gg_one_lt_of_SC hκ

omit hκ in
theorem sqK_lt_eps : κ < veblen 1 (κ + 1) := (lt_add_one κ).trans_le (right_le_veblen 1 _)

/-- `x < ε_{κ+1}` gives `ω^{κ·x} < ε_{κ+1}`. -/
theorem sqOpow_lt {x : Ordinal.{0}} (hx : x < veblen 1 (κ + 1)) : ω ^ (κ * x) < veblen 1 (κ + 1) := by
  have hE : ω ^ veblen 1 (κ + 1) = veblen 1 (κ + 1) := gg_veblen_eps one_ne_zero
  have hp := Ph.ph_veblen_prin (1 : Ordinal.{0}) (κ + 1)
  have hk : κ * x < veblen 1 (κ + 1) := by
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [mul_zero]; exact veblen_pos
    have hlt : κ * x ≤ ω ^ (κ + x) := by
      rw [opow_add, gg_SC_eps hκ]
      exact mul_le_mul_right (right_le_opow x one_lt_omega0) _
    exact hlt.trans_lt (by
      conv_rhs => rw [← hE]
      exact (opow_lt_opow_iff_right one_lt_omega0).2 (hp sqK_lt_eps hx))
  conv_rhs => rw [← hE]
  exact (opow_lt_opow_iff_right one_lt_omega0).2 hk

/-- **`t_k < ε_{κ+1}`.** -/
theorem sqTw_lt : ∀ k, sqTw κ k < veblen 1 (κ + 1)
  | 0 => (sqOne_lt hκ).trans sqK_lt_eps
  | k + 1 => sqOpow_lt hκ (sqTw_lt k)

omit hκ in
theorem sqTw_pos : ∀ k, 0 < sqTw κ k
  | 0 => zero_lt_one
  | _ + 1 => opow_pos _ omega0_pos

theorem sqTw_lt_succ : ∀ k, sqTw κ k < sqTw κ (k + 1)
  | 0 => by
    show (1 : Ordinal.{0}) < ω ^ (κ * 1)
    rw [mul_one, gg_SC_eps hκ]; exact sqOne_lt hκ
  | k + 1 => (opow_lt_opow_iff_right one_lt_omega0).2
      ((mul_lt_mul_iff_right₀ hκ.1).2 (sqTw_lt_succ k))

theorem sqTw_strictMono : StrictMono (sqTw κ) := strictMono_nat_of_lt_succ (sqTw_lt_succ hκ)

theorem sqTw_mono {j k : ℕ} (h : j ≤ k) : sqTw κ j ≤ sqTw κ k := (sqTw_strictMono hκ).monotone h

theorem sqOne_le_tw (k : ℕ) : 1 ≤ sqTw κ k := Order.one_le_iff_pos.2 (sqTw_pos k)

/-- `κ + 1 ≤ t_2`. -/
theorem sqK1_le_tw2 : κ + 1 ≤ sqTw κ 2 := by
  have h1 : sqTw κ 1 = κ := by show ω ^ (κ * 1) = κ; rw [mul_one, gg_SC_eps hκ]
  show κ + 1 ≤ ω ^ (κ * sqTw κ 1)
  rw [h1]
  refine (Order.add_one_le_of_lt ?_).trans (right_le_opow _ one_lt_omega0)
  calc κ = κ * 1 := (mul_one _).symm
    _ < κ * κ := (mul_lt_mul_iff_right₀ hκ.1).2 (sqOne_lt hκ)

/-- `(ω^·)^[n](κ + 1) ≤ t_{n+2}`. -/
theorem sqIter_le : ∀ n : ℕ, (fun a : Ordinal.{0} => ω ^ a)^[n] (κ + 1) ≤ sqTw κ (n + 2)
  | 0 => sqK1_le_tw2 hκ
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    refine (opow_le_opow_right omega0_pos (sqIter_le n)).trans ?_
    show ω ^ sqTw κ (n + 2) ≤ ω ^ (κ * sqTw κ (n + 2))
    exact opow_le_opow_right omega0_pos (Ordinal.le_mul_right _ hκ.1)

/-- **Every `x < ε_{κ+1}` is below some `t_k`.** -/
theorem sqTw_cof {x : Ordinal.{0}} (hx : x < veblen 1 (κ + 1)) : ∃ k, x < sqTw κ k := by
  have hd : deriv (fun a : Ordinal.{0} => ω ^ a) κ = κ := by
    have h := hκ.veblen_right (sqOne_lt hκ)
    rwa [← zero_add (1 : Ordinal.{0}), veblen_add_one, veblen_zero] at h
  have he : veblen 1 (κ + 1) = nfp (fun a : Ordinal.{0} => ω ^ a) (κ + 1) := by
    rw [← zero_add (1 : Ordinal.{0}), veblen_add_one, veblen_zero, zero_add, ← Order.succ_eq_add_one,
      deriv_succ, hd]
  rw [he] at hx
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hx
  exact ⟨n + 2, hn.trans_le (sqIter_le hκ n)⟩

/-- `t_k` is a code over every `Q > 1` (`κ` as the letter). -/
theorem sqTw_cl {Q : Ordinal.{0}} (hQ : SC Q) : ∀ k, LeCl κ Q (sqTw κ k)
  | 0 => LeCl.small (gg_one_lt_of_SC hQ)
  | k + 1 => LeCl.opow hQ.1 (LeCl.mulK hQ hκ _ (sqTw_cl hQ k))

end Gen

/-- `t_k ∈ CSet a b` for the `Ω₂`-tower. -/
theorem sqTwW_mem {a b : Ordinal.{0}} : ∀ k, sqTw (Om (1 + 1)) k ∈ S.CSet a b
  | 0 => CSet.one_mem _ _
  | k + 1 => leWe_mem (sqTwW_mem k)

/-- `t̂_k ∈ CSet a b` for the `Ω₁`-tower. -/
theorem sqTwO_mem {a b : Ordinal.{0}} : ∀ k, sqTw (Om 1) k ∈ S.CSet a b
  | 0 => CSet.one_mem _ _
  | k + 1 => leOe_mem (sqTwO_mem k)

/-- **`κ·ε_{κ+1} = ε_{κ+1}`.** -/
theorem sqK_mul_eps {κ : Ordinal.{0}} (hκ : SC κ) : κ * veblen 1 (κ + 1) = veblen 1 (κ + 1) := by
  have hE : ω ^ veblen 1 (κ + 1) = veblen 1 (κ + 1) := gg_veblen_eps one_ne_zero
  have h1 : κ < ω ^ veblen 1 (κ + 1) := by rw [hE]; exact sqK_lt_eps
  calc κ * veblen 1 (κ + 1) = ω ^ κ * ω ^ veblen 1 (κ + 1) := by rw [gg_SC_eps hκ, hE]
    _ = ω ^ (κ + veblen 1 (κ + 1)) := (opow_add _ _ _).symm
    _ = ω ^ veblen 1 (κ + 1) := by rw [Ordinal.add_of_omega0_opow_le h1 hE.le]
    _ = veblen 1 (κ + 1) := hE

/-- **`W^ε = ε`** for `ε = ε_{Ω₂+1}`. -/
theorem sqEps_We : leWe (veblen 1 (Om (1 + 1) + 1)) = veblen 1 (Om (1 + 1) + 1) := by
  unfold leWe; rw [sqK_mul_eps ldOm2_SC, gg_veblen_eps one_ne_zero]

/-- **`Ω^{ε̂} = ε̂`** for `ε̂ = ε_{Ω₁+1}`. -/
theorem sqEpsH_Oe : leOe (veblen 1 (Om 1 + 1)) = veblen 1 (Om 1 + 1) := by
  unfold leOe; rw [sqK_mul_eps Ph.ph_SC_Om1, gg_veblen_eps one_ne_zero]

theorem sqEps_dvd : Om (1 + 1 : Ordinal.{0}) ∣ veblen 1 (Om (1 + 1) + 1) :=
  ⟨_, (sqK_mul_eps ldOm2_SC).symm⟩

theorem sqEps_cl {Q : Ordinal.{0}} (hQ : SC Q) : LeCl (Om (1 + 1)) Q (veblen 1 (Om (1 + 1) + 1)) :=
  LeCl.phi (LeCl.small (gg_one_lt_of_SC hQ)) (LeCl.add LeCl.om (LeCl.small (gg_one_lt_of_SC hQ)))

theorem sqEpsH_cl {Q : Ordinal.{0}} (hQ : SC Q) : LeCl (Om 1) Q (veblen 1 (Om 1 + 1)) :=
  LeCl.phi (LeCl.small (gg_one_lt_of_SC hQ)) (LeCl.add LeCl.om (LeCl.small (gg_one_lt_of_SC hQ)))

theorem sqEps_mem {a b : Ordinal.{0}} : veblen 1 (Om (1 + 1) + 1) ∈ S.CSet a b :=
  CSet.phi_mem (CSet.one_mem _ _) (CSet.succ_mem (mxOm2_mem _ _))

theorem sqEpsH_mem {a b : Ordinal.{0}} : veblen 1 (Om 1 + 1) ∈ S.CSet a b :=
  CSet.phi_mem (CSet.one_mem _ _) (CSet.succ_mem (CSet.Om_mem (CSet.one_mem _ _)))

/-- `ε_{Ω₂+1} < ψ_{Ω₃}(0)`, `ε_{Ω₁+1} < ψ_{Ω₂}(0)`. -/
theorem sqEpsH_lt_G : veblen 1 (Om 1 + 1) < S.psi 0 (Om (1 + 1)) := by
  have hG1 := Rw.rwG_SC (S := S)
  have hΩ := Rw.rwO_lt_G (S := S)
  exact hG1.2 1 (gg_one_lt_of_SC hG1) _ (hG1.isSuccLimit.succ_lt hΩ)

/-- **`Θ̂(t_k) = t̂_k`**: the image of the `Ω₂`-tower is the `Ω₁`-tower. -/
theorem sqThH_tw (l : Ordinal.{0}) (h1 : (1 : Ordinal.{0}) ≤ upsilon l) :
    ∀ k, sgThH S l (sqTw (Om (1 + 1)) k) = sqTw (Om 1) k
  | 0 => by
    rw [sqTw_zero, sqTw_zero, sgThH_code l le_rfl (gg_one_lt_of_SC ldOm2_SC), gxTh_small h1]
  | k + 1 => by
    have hE1 : 1 ≤ sqTw (Om (1 + 1)) (k + 1) := sqOne_le_tw ldOm2_SC _
    have hE : sqTw (Om (1 + 1)) (k + 1) < veblen 1 (Om (1 + 1) + 1) := sqTw_lt ldOm2_SC _
    rw [sgThH_cnf l hE1 hE]
    have hlw : sgLW (sqTw (Om (1 + 1)) (k + 1)) = sqTw (Om (1 + 1)) k := by
      unfold sgLW
      rw [sqTw_succ, Ordinal.log_opow one_lt_omega0, Ordinal.mul_div_cancel _ ldOm2_SC.1.ne']
    rw [hlw, ← sqTw_We, Ordinal.div_self (sqTw_pos _).ne', Ordinal.mod_self, sgThH_zero, add_zero,
      gxTh_small h1, mul_one, sqThH_tw l h1 k]
    rfl

end Googology.Trans.PoR.InaccPsi.R2.Sq
