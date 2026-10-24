import Googology.Trans.PoR.InaccPsi.R2.SqTw

/-!
# The level `ε_{Ω₂+1}`: the top law `Θ(ψ_{Ω₂}(β + W^{X₀ + ε})) = ψ_{Ω₁}(Â + Ω^{X̂₀ + ε̂})`

`Θ = gxTh ρ_λ (ldAtR λ)`, `Θ̂ = Sg.sgThH S λ`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `ε = ε_{Ω₂+1}` (`W^ε = ε`),
`ε̂ = ε_{Ω₁+1}` (`Ω^{ε̂} = ε̂`), `t_k = Sq.sqTw Ω₂ k` (`t_{k+1} = W^{t_k}`), `t̂_k = Sq.sqTw Ω₁ k`.

The limit `ε` is the supremum of the fixed sequence `t_k` (no base-dependent sequence is needed: every `t_k` is
built from `Ω₂` alone, so it is a code over every strongly critical `Q`, and the closure condition `Sn.SnCL` of
`t_k` holds at every base and offset).  The level members `X₀ + W^{t_k}` are shifts own relative to `b` with the
top law (`Sc.scFam`, `Sn.snOwP`, `Sn.snLev`), cofinal in `X₀ + ε` with images `X̂₀ + t̂_{k+1}` cofinal in
`X̂₀ + ε̂`, and `Rv.rvTopLimSh` gives the top law at `X₀ + ε`.

* `sqOwn_eps`, `sqOwP_eps` (**`ε` is an own exponent at every base and offset, image `ε̂`, own predicate `⊤`**);
* `sqMemb` (the members `X₀ + W^{t_k}`), `sqSh_eps` (**`X₀ + ε` is a shift own relative to `b`**);
* `sqLev_eps` (**`Sc.ScLev ⊤ ε ε̂`: the top law at `X₀ + W^ε` over every own offset `X₀` at every base**),
  `sqTop_eps` (**`Θ(ψ_{Ω₂}(β + ε)) = ψ_{Ω₁}(Â + ε̂)`** at every base `β` with a reading),
  `sqFam_eps` (**the level-`ε` family `X₀ + ε·ζ`** by `Sc.scFam`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg
  Googology.Trans.PoR.InaccPsi.R2.Sn

variable {S : InaccSeq.{0}}

theorem sqOne_le_eps : (1 : Ordinal.{0}) ≤ veblen 1 (Om (1 + 1) + 1) :=
  (gg_one_lt_of_SC ldOm2_SC).le.trans sqK_lt_eps.le

theorem sqOne_lt_Om1 : (1 : Ordinal.{0}) < Om 1 := gg_one_lt_of_SC Ph.ph_SC_Om1

/-- **`ε` is an own exponent at every base and offset, with the image `ε̂`.** -/
theorem sqOwn_eps {l : Ordinal.{0}} (b X0 : Ordinal.{0}) :
    ScOwn S l b X0 (veblen 1 (Om (1 + 1) + 1)) (veblen 1 (Om 1 + 1)) :=
  ⟨sqOne_le_eps, sqEps_mem, sqEps_mem, sqEpsH_mem, fun _ hQ _ => sqEps_cl hQ, fun _ hQ _ => sqEpsH_cl hQ⟩

theorem sqOwP_eps {l : Ordinal.{0}} :
    ScOwP S l (fun _ _ => True) (veblen 1 (Om (1 + 1) + 1)) (veblen 1 (Om 1 + 1)) :=
  ⟨fun b X0 _ => sqOwn_eps b X0, fun _ _ _ _ _ _ _ => trivial⟩

/-- `X₀ + W^ε + Ω₂ < ψ_{Ω₃}(0)` gives `X₀ + W^{ε+1} + Ω₂ < ψ_{Ω₃}(0)`. -/
theorem sqG3_succ {X0 : Ordinal.{0}}
    (hG3 : X0 + leWe (veblen 1 (Om (1 + 1) + 1)) + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1))) :
    X0 + leWe (veblen 1 (Om (1 + 1) + 1) + 1) + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)) := by
  have hG3S := rwG3_SC (S := S)
  have hX0 : X0 < S.psi 0 (Om (1 + 1 + 1)) := (le_self_add.trans le_self_add).trans_lt hG3
  have hW : leWe (veblen 1 (Om (1 + 1) + 1) + 1) < S.psi 0 (Om (1 + 1 + 1)) :=
    (leWe_lt_SC hG3S rwW_lt_G3 (hG3S.isSuccLimit.succ_lt snEps_lt_G3)).1
  exact hG3S.isPrincipal (hG3S.isPrincipal hX0 hW) rwW_lt_G3

/-- `X̂₀ + Ω^{ε̂} + Ω₁ < ψ_{Ω₂}(0)` gives `X̂₀ + Ω^{ε̂+1} + Ω₁ < ψ_{Ω₂}(0)`. -/
theorem sqG_succ {Xh0 : Ordinal.{0}}
    (hG : Xh0 + leOe (veblen 1 (Om 1 + 1)) + Om 1 < S.psi 0 (Om (1 + 1))) :
    Xh0 + leOe (veblen 1 (Om 1 + 1) + 1) + Om 1 < S.psi 0 (Om (1 + 1)) := by
  have hG1 := rwG_SC (S := S)
  have hX0 : Xh0 < S.psi 0 (Om (1 + 1)) := (le_self_add.trans le_self_add).trans_lt hG
  have hO : leOe (veblen 1 (Om 1 + 1) + 1) < S.psi 0 (Om (1 + 1)) :=
    (leOe_lt_SC hG1 rwO_lt_G (hG1.isSuccLimit.succ_lt sqEpsH_lt_G)).1
  exact hG1.isPrincipal (hG1.isPrincipal hX0 hO) rwO_lt_G

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

theorem sqTh_one : gxTh (upsilon l) (ldAtR S l) 1 = 1 :=
  gxTh_small (gg_one_lt_of_SC (leRho hl hX).1).le

/-- **The members `X₀ + W^{t_k}` of the level `ε`** (image `X̂₀ + Ω^{Θ̂ t_k}`): shifts own relative to `b` with the
top law. -/
theorem sqMemb {b X0 Xh0 : Ordinal.{0}} (hoff : RvOff S l b X0 Xh0)
    (hd : leWe (veblen 1 (Om (1 + 1) + 1)) ∣ X0)
    (hG3 : X0 + leWe (veblen 1 (Om (1 + 1) + 1)) + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)))
    (hG : Xh0 + leOe (veblen 1 (Om 1 + 1)) + Om 1 < S.psi 0 (Om (1 + 1))) (k : ℕ) :
    RvSh S l b (X0 + leWe (sqTw (Om (1 + 1)) k) * 1)
        (Xh0 + leOe (sgThH S l (sqTw (Om (1 + 1)) k)) * gxTh (upsilon l) (ldAtR S l) 1) ∧
      RvTop S l b (X0 + leWe (sqTw (Om (1 + 1)) k) * 1)
        (Xh0 + leOe (sgThH S l (sqTw (Om (1 + 1)) k)) * gxTh (upsilon l) (ldAtR S l) 1) 0 := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have h1ρ : (1 : Ordinal.{0}) ≤ upsilon l := (gg_one_lt_of_SC hρSC).le
  have hE1 : 1 ≤ sqTw (Om (1 + 1)) k := sqOne_le_tw ldOm2_SC k
  have hEε : sqTw (Om (1 + 1)) k < veblen 1 (Om (1 + 1) + 1) := sqTw_lt ldOm2_SC k
  have hEH : sqTw (Om (1 + 1)) k ∈ cdHull S l := sqTwW_mem k
  have hE1ε : sqTw (Om (1 + 1)) k + 1 ≤ veblen 1 (Om (1 + 1) + 1) := Order.add_one_le_of_lt hEε
  have hdE : leWe (sqTw (Om (1 + 1)) k + 1) ∣ X0 := (leWe_dvd hE1ε).trans hd
  have hG3' : X0 + leWe (sqTw (Om (1 + 1)) k + 1) + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)) :=
    lt_of_le_of_lt (add_le_add_left ((add_le_add_iff_left X0).2 (leWe_mono hE1ε)) _) hG3
  have hÊ : sgThH S l (sqTw (Om (1 + 1)) k) = sqTw (Om 1) k := sqThH_tw l h1ρ k
  have hG' : Xh0 + leOe (sgThH S l (sqTw (Om (1 + 1)) k) + 1) + Om 1 < S.psi 0 (Om (1 + 1)) := by
    rw [hÊ]
    exact lt_of_le_of_lt (add_le_add_left ((add_le_add_iff_left Xh0).2
      (leOe_mono (Order.add_one_le_of_lt (sqTw_lt Ph.ph_SC_Om1 k)))) _) hG
  have hcl : SnCL S (sqTw (Om (1 + 1)) k) b X0 := fun Q hQ _ => sqTw_cl ldOm2_SC hQ k
  have h := scFam hl hX (snOwP hl hX hEH hE1 hEε) (snLev hl hX hEH hE1 hEε) hoff hdE hG3' hG' hcl 1
    (GxCl.small (gg_one_lt_of_SC hρSC)) ⟨0, show (1 : Ordinal.{0}) < Om 1 from sqOne_lt_Om1⟩
    (by rw [sqTh_one hl hX]; exact sqOne_lt_Om1)
  refine rvOff_ne h fun h' => (leWe_pos (sqTw (Om (1 + 1)) k)).ne' ?_
  have := le_antisymm (h' ▸ le_add_self : leWe (sqTw (Om (1 + 1)) k) * 1 ≤ 0) zero_le
  rwa [mul_one] at this

/-- **`X₀ + ε` is a shift own relative to `b`** (image `X̂₀ + ε̂`). -/
theorem sqSh_eps {b X0 Xh0 : Ordinal.{0}} (hoff : RvOff S l b X0 Xh0)
    (hG3 : X0 + leWe (veblen 1 (Om (1 + 1) + 1)) + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)))
    (hG : Xh0 + leOe (veblen 1 (Om 1 + 1)) + Om 1 < S.psi 0 (Om (1 + 1))) :
    RvSh S l b (X0 + leWe (veblen 1 (Om (1 + 1) + 1))) (Xh0 + leOe (veblen 1 (Om 1 + 1))) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have h := scSh_m hl hX hoff (sqOwn_eps (l := l) b X0) (ζ := 1) (GxCl.small (gg_one_lt_of_SC hρSC))
    (gg_one_lt_of_SC ldOm2_SC) one_ne_zero
    (sqOne_lt_Om1.trans (psiS_bounds (S := S) _ 1).1)
    (by rw [sqTh_one hl hX]; exact sqOne_lt_Om1) (sqG3_succ hG3) (sqG_succ hG)
  rwa [mul_one, sqTh_one hl hX, mul_one] at h

/-- **THE LEVEL `ε`: the top law at `X₀ + W^ε` over every own offset `X₀` at every base** (`Sc.ScLev ⊤ ε ε̂`). -/
theorem sqLev_eps : ScLev S l (fun _ _ => True) (veblen 1 (Om (1 + 1) + 1)) (veblen 1 (Om 1 + 1)) := by
  intro b X0 Xh0 hoff hd hG3 hG _
  have hm := sqMemb hl hX hoff hd hG3 hG
  have hΘ1 := sqTh_one hl hX
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have h1ρ : (1 : Ordinal.{0}) ≤ upsilon l := (gg_one_lt_of_SC hρSC).le
  refine rvTopLimSh hl hX (sqSh_eps hl hX hoff hG3 hG) ?_ ?_
  · intro x _ hx
    rw [sqEps_We] at hx
    obtain ⟨k, hk⟩ : ∃ k, x < X0 + sqTw (Om (1 + 1)) k := by
      rcases lt_or_ge x X0 with h | h
      · exact ⟨0, h.trans_le le_self_add⟩
      · obtain ⟨y, rfl⟩ := exists_add_of_le h
        obtain ⟨k, hk⟩ := sqTw_cof ldOm2_SC ((add_lt_add_iff_left X0).1 hx)
        exact ⟨k, (add_lt_add_iff_left X0).2 hk⟩
    obtain ⟨hsk, htk⟩ := hm k
    refine ⟨_, _, ?_, ?_, ?_, hsk, htk⟩
    · rw [mul_one]
      exact (add_le_add_iff_left X0).2 (leWe_mono (sqTw_lt ldOm2_SC k).le)
    · rw [mul_one, ← sqTw_We]
      exact hk.trans ((add_lt_add_iff_left X0).2 (sqTw_lt_succ ldOm2_SC k))
    · rw [sqThH_tw l h1ρ k, hΘ1, mul_one, ← sqTw_Oe, sqEpsH_Oe]
      exact (add_lt_add_iff_left Xh0).2 (sqTw_lt Ph.ph_SC_Om1 (k + 1))
  · intro z hz
    rw [sqEpsH_Oe] at hz
    obtain ⟨k, hk⟩ : ∃ k, z < Xh0 + sqTw (Om 1) k := by
      rcases lt_or_ge z Xh0 with h | h
      · exact ⟨0, h.trans_le le_self_add⟩
      · obtain ⟨y, rfl⟩ := exists_add_of_le h
        obtain ⟨k, hk⟩ := sqTw_cof Ph.ph_SC_Om1 ((add_lt_add_iff_left Xh0).1 hz)
        exact ⟨k, (add_lt_add_iff_left Xh0).2 hk⟩
    obtain ⟨hsk, htk⟩ := hm k
    refine ⟨_, _, ?_, ?_, hsk, htk⟩
    · rw [mul_one, sqEps_We, ← sqTw_We]
      exact (add_lt_add_iff_left X0).2 (sqTw_lt ldOm2_SC (k + 1))
    · rw [sqThH_tw l h1ρ k, hΘ1, mul_one, ← sqTw_Oe]
      exact hk.trans ((add_lt_add_iff_left Xh0).2 (sqTw_lt_succ Ph.ph_SC_Om1 k))

/-- **`Θ(ψ_{Ω₂}(β + W^{X₀+ε})) = ψ_{Ω₁}(Â + Ω^{X̂₀ + ε̂})`** at every base `β ≥ b` with a reading, for every own
offset `X₀` (with `W^ε ∣ X₀` and the bounds). -/
theorem sqTop_eps {b X0 Xh0 β Â : Ordinal.{0}} (hoff : RvOff S l b X0 Xh0)
    (hd : leWe (veblen 1 (Om (1 + 1) + 1)) ∣ X0)
    (hG3 : X0 + leWe (veblen 1 (Om (1 + 1) + 1)) + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)))
    (hG : Xh0 + leOe (veblen 1 (Om 1 + 1)) + Om 1 < S.psi 0 (Om (1 + 1)))
    (hb : RoBaseE S l (X0 + veblen 1 (Om (1 + 1) + 1)) 0 β) (hbβ : b ≤ β)
    (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hbase : gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1)) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (X0 + veblen 1 (Om (1 + 1) + 1))) (Om (1 + 1))) =
      S.psi (Â + leOe (Xh0 + veblen 1 (Om 1 + 1))) (Om 1) := by
  have h := sqLev_eps hl hX b X0 Xh0 hoff hd hG3 hG trivial β Â (by rwa [sqEps_We]) hbβ hÂ hbase
  rw [sqEps_We, sqEpsH_Oe, add_zero, gxTh_zero, add_zero] at h
  exact h

/-- **The level-`ε` family** `X₀ + ε·ζ` (image `X̂₀ + ε̂·Θ ζ`), `ζ < EE_j(X₀, β, ε)` a code, over every own offset. -/
theorem sqFam_eps {X0 Xh0 β : Ordinal.{0}} (hoff : RvOff S l β X0 Xh0)
    (hd : leWe (veblen 1 (Om (1 + 1) + 1) + 1) ∣ X0)
    (hG3 : X0 + leWe (veblen 1 (Om (1 + 1) + 1) + 1) + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)))
    (hG : Xh0 + leOe (veblen 1 (Om 1 + 1) + 1) + Om 1 < S.psi 0 (Om (1 + 1))) :
    ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → (∃ j, ζ < rvEE S X0 β (veblen 1 (Om (1 + 1) + 1)) j) →
      gxTh (upsilon l) (ldAtR S l) ζ < Om 1 →
      RvOff S l β (X0 + veblen 1 (Om (1 + 1) + 1) * ζ)
        (Xh0 + veblen 1 (Om 1 + 1) * gxTh (upsilon l) (ldAtR S l) ζ) := by
  intro ζ hζ hj hΘ
  have h := scFam hl hX sqOwP_eps (sqLev_eps hl hX) hoff hd hG3 hG trivial ζ hζ hj hΘ
  rwa [sqEps_We, sqEpsH_Oe] at h

end Main

end Googology.Trans.PoR.InaccPsi.R2.Sq
