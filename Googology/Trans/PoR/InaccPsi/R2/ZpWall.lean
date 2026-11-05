import Googology.Trans.PoR.InaccPsi.R2.ZpBase

/-!
# THE WALL ASSEMBLY: the wall below `θ` from the ψ₃-offsets and the top law

`θ = ψ_{Ω₂}(Ω_ω)`, "window", "IH(s)" as in `Zp.zpYjBase`; `b = Ω₃·(d/Ω₃)` the `Ω₃`-divisible part of `d`.

* `ZpPsi3OffAll S` (**THE ψ₃-OFFSETS OVER EVERY `Ω₃`-BASE**, a statement: at a window, over every base `a` with a
  law at both ends (`Yj.YjBase`), `Ω₃ ∣ a`, `Ω₃ ∣ B_n a`, `Ω₃ ≤ a`, every atom `ψ₂(a) ≤ s < ψ₂(a + Ω₃)` moves under
  IH(s); this is the statement of the skeleton node `skPsi3OffD`);
* `ZpWallTh S` (the wall at the bound `θ`: every atom `ψ₂(Y₃) ≤ s < θ` moves under IH(s));
* `zpDecomp` (**EVERY ATOM BELOW THE WALL IS `ψ₂(b + δ)`**: for every atom `ψ₂(Y₃) ≤ s < θ` of `λ` there is a
  normal `d ∈ D_λ` with `s = ψ₂ d`, its `Ω₃`-part `b` is normal, in `D_λ`, `Ω₃ ∣ b`, `Ω₃ ≤ b`, `d < b + Ω₃`,
  `ψ₂ b ≤ s < ψ₂(b + Ω₃)`; UNCONDITIONAL beyond the restart hypotheses);
* `zpWall` (**THE ASSEMBLY**: `ZpTopLawAll S → ZpPsi3OffAll S → ZpWallTh S`);
* `zpOff_of_wall` (**NON-VACUITY of `ZpPsi3OffAll`**: it follows from the target `ZpWallTh S`);
* `zpLaw_top` (**NON-VACUITY of `ZpTopLawAll` on the top atoms**: every top atom `β + W^{Ω_{k+3}+e}`, `e` a code,
  satisfies the premises of `ZpTopLawAll`, and its conclusion there is the theorem `Xm.xmTopUp`);
* `zpTest1`, `zpTest2` (the REFUTE-FIRST points `ψ₂(Ω₃·2 + Ω₃)` (`b = Ω₃·3`, `δ = 0`) and
  `ψ₂(W^{Ω₃+1} + Y₃·2)` (`b = Ω₃·Ω₂ = W^{Ω₃+1}`, `δ = Y₃·2`)).

No new axiom.  New definitions: `ZpPsi3OffAll`, `ZpWallTh` (statement names).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Rx

variable {S : InaccSeq.{0}}

/-- **THE ψ₃-OFFSETS OVER EVERY `Ω₃`-BASE** (the statement of `skPsi3OffD`). -/
def ZpPsi3OffAll (S : InaccSeq.{0}) : Prop :=
  ∀ (n : ℕ) (l l' A' a D s : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l →
    cdR S l < Bc.bcC S (n + 1) → IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
    A' ∈ S.CSet A' (S.psi A' (Om 1)) → S.psi A' (Om 1) = upsilon l' → Yj.YjBase S n l l' A' a D →
    Om (1 + 1 + 1) ∣ a → Om (1 + 1 + 1) ∣ Bc.bcB S n a → Om (1 + 1 + 1) ≤ a → s ∈ ldAtR S l →
    S.psi a (Om (1 + 1)) ≤ s → s < S.psi (a + Om (1 + 1 + 1)) (Om (1 + 1)) →
    (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- The wall at the bound `θ`. -/
def ZpWallTh (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
    ∀ s ∈ ldAtR S l, S.psi (Ug.ugY S) (Om (1 + 1)) ≤ s → s < ConjT.th S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

theorem zpOm3_ne : Om (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := (Om_pos (add_pos_of_right zero_lt_one _).ne').ne'

/-- `ψ₂(Ω₃) = ψ₂(Y₃)`. -/
theorem zpPsi_Om3 : S.psi (Om (1 + 1 + 1)) (Om (1 + 1)) = S.psi (Ug.ugY S) (Om (1 + 1)) := by
  have h2 : Om (1 + 1) < S.psi (Om (1 + 1 + 1)) (Om (1 + 1 + 1)) := (psiS_bounds (S := S) _ (1 + 1)).1
  have hY : S.psi (Om (1 + 1 + 1)) (Om (1 + 1 + 1)) ≤ Om (1 + 1 + 1) := (psi_lt (InR_Om_succ (1 + 1)) _).le
  exact Vn.vnPsi2_eq (s := 1 + 1) h2 hY le_rfl

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **EVERY ATOM BELOW THE WALL IS `ψ₂(b + δ)`** with `b` a normal `Ω₃`-divisible member of `D`, `b ≥ Ω₃`. -/
theorem zpDecomp {s : Ordinal.{0}} (hs : s ∈ ldAtR S l) (hsY : S.psi (Ug.ugY S) (Om (1 + 1)) ≤ s)
    (hsθ : s < ConjT.th S) :
    ∃ d, VbD S l d ∧ S.psi d (Om (1 + 1)) = s ∧ d ∈ S.CSet d (S.psi d (Om (1 + 1))) ∧
      VbD S l (Om (1 + 1 + 1) * (d / Om (1 + 1 + 1))) ∧
      Om (1 + 1 + 1) * (d / Om (1 + 1 + 1)) ∈ S.CSet (Om (1 + 1 + 1) * (d / Om (1 + 1 + 1)))
        (S.psi (Om (1 + 1 + 1) * (d / Om (1 + 1 + 1))) (Om (1 + 1))) ∧
      Om (1 + 1 + 1) ≤ Om (1 + 1 + 1) * (d / Om (1 + 1 + 1)) ∧
      d < Om (1 + 1 + 1) * (d / Om (1 + 1 + 1)) + Om (1 + 1 + 1) ∧
      S.psi (Om (1 + 1 + 1) * (d / Om (1 + 1 + 1))) (Om (1 + 1)) ≤ s ∧
      s < S.psi (Om (1 + 1 + 1) * (d / Om (1 + 1 + 1)) + Om (1 + 1 + 1)) (Om (1 + 1)) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨d, hdD, hds, hdn⟩ := vbReach hl hX hs hsθ
  set Q := Om (1 + 1 + 1 : Ordinal.{0}) with hQ
  have hQSC := zpOm3_SC S
  have hbn := zpPre3_norm hdn
  have hbD : VbD S l (Q * (d / Q)) :=
    ⟨zpPre_mem hQSC (zpOm3_mem _ _) hdD.1, zpPre_mem hQSC (zpOm3_mem _ _) hdD.2.1,
      (zpPre_le _ _).trans_lt hdD.2.2⟩
  have hlt : d < Q * (d / Q) + Q := zpPre_lt zpOm3_ne d
  have h3 : Q ≤ Q * (d / Q) := by
    rcases eq_or_ne (d / Q) 0 with h0 | h0
    · exfalso
      rw [h0, mul_zero, zero_add] at hlt
      have h := psi_lt_psi hκ2 hlt hdn
      rw [zpPsi_Om3, hds] at h
      exact absurd (hsY.trans_lt h) (lt_irrefl _)
    · calc Q = Q * 1 := (mul_one Q).symm
        _ ≤ Q * (d / Q) := mul_le_mul_left' (one_le_iff_ne_zero.2 h0) Q
  refine ⟨d, hdD, hds, hdn, hbD, hbn, h3, hlt, ?_, ?_⟩
  · rw [← hds]; exact (psi_mono hκ2 (zpPre_le _ _)).1
  · rw [← hds]; exact psi_lt_psi hκ2 hlt hdn

end Rst

/-- **THE ASSEMBLY**: the top law at every exponent and the ψ₃-offsets over every `Ω₃`-base give the wall below `θ`. -/
theorem zpWall (hLaw : ZpTopLawAll S) (hOff : ZpPsi3OffAll S) : ZpWallTh S := by
  intro n l l' hR h1 hr hl' hB s hs hsY hsθ IH
  obtain ⟨hX, -, -, -, A', hA', hρ'⟩ := Xv.xvWin hR h1 hr hl' hB
  obtain ⟨d, -, -, -, hbD, hbn, h3, -, hbs, hsb⟩ := zpDecomp hR.1 hX hs hsY hsθ
  have IHb := fun x hx (hxb : x < S.psi (Om (1 + 1 + 1) * (d / Om (1 + 1 + 1))) (Om (1 + 1))) =>
    IH x hx (hxb.trans_le hbs)
  obtain ⟨hYj, hdv'⟩ := zpYjBase hR h1 hr hl' hB hA' hρ' hLaw hbD hbn (zpPre_div _ _) h3 IHb
  exact hOff n l l' A' _ _ s hR h1 hr hl' hB hA' hρ' hYj (zpPre_div _ _) hdv' h3 hs hbs hsb IH

/-- **NON-VACUITY of `ZpPsi3OffAll`**: it follows from the target. -/
theorem zpOff_of_wall (hW : ZpWallTh S) : ZpPsi3OffAll S := by
  intro n l l' A' a D s hR h1 hr hl' hB _ _ hb _ _ h3 hs hsa hsT IH
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have haW : a < Om ω := hb.D_a.2.2
  have h3W : Om (1 + 1 + 1 : Ordinal.{0}) < Om ω :=
    Om_lt_Om.2 (by rw [show (1 + 1 + 1 : Ordinal.{0}) = ((3 : ℕ) : Ordinal.{0}) by norm_num]
                   exact Ordinal.nat_lt_omega0 3)
  have hsum : a + Om (1 + 1 + 1) < Om ω := vkOmW.1.isPrincipal haW h3W
  have hY3 : S.psi (Ug.ugY S) (Om (1 + 1)) ≤ s := by
    rw [← zpPsi_Om3]; exact (psi_mono hκ2 h3).1.trans hsa
  have hsθ : s < ConjT.th S := hsT.trans_le (psi_mono hκ2 hsum.le).1
  exact hW n l l' hR h1 hr hl' hB s hs hY3 hsθ IH

/-- **NON-VACUITY of `ZpTopLawAll` on the top atoms**: every top atom `t = β + W^{Ω_{k+3}+e}` (`e` a code,
`Ro.RoBaseE`) satisfies the premises of `ZpTopLawAll`, and the conclusion holds there (`Xm.xmTopUp`). -/
theorem zpLaw_top (k : ℕ) {l ηx A e β : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    (hec : GxCl (upsilon l) (ldAtR S l) e) (he2 : e < Om (1 + 1)) (hβD : VbD S l β)
    (hb : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β) :
    VbD S l (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) ∧
      β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) ∈ S.CSet (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e))
        (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1))) ∧
      Om (1 + 1 + 1) ∣ β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) ∧
      Om (1 + 1 + 1) ≤ β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) ∧
      gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1))) =
        S.psi (A + 1 + S.psi (vbT S l (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e))) (Om (1 + 1))) (Om 1) := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  obtain ⟨htD, -, htown⟩ := Xq.xqTopD hl hX k hec he2 hβD hb
  have htn : β + leWe (X + e) ∈ S.CSet (β + leWe (X + e)) (S.psi (β + leWe (X + e)) (Om (1 + 1))) := by
    have h := htown 0 zero_le; rwa [add_zero] at h
  -- `Ω₃ ∣ X ∣ W^{X+e}`, `W^{X+e} ∣ β`
  have hXk : ((k : Ordinal.{0}) + 1 + 1 + 1) ≠ 0 := (add_pos_of_right zero_lt_one _).ne'
  have hXSC : SC X := SC_Om hXk
  have h3X : Om (1 + 1 + 1 : Ordinal.{0}) ≤ X := Om_le_Om.2 (by
    have : (1 + 1 + 1 : Ordinal.{0}) ≤ (k : Ordinal.{0}) + 1 + 1 + 1 := by
      simpa [add_assoc] using (le_add_left (1 + 1 + 1 : Ordinal.{0}) (k : Ordinal.{0}))
    exact this)
  have h3dX : Om (1 + 1 + 1 : Ordinal.{0}) ∣ X := by
    rw [← zpOm3_opow S, ← Low.opow_eq_self_of_SC hXSC]
    exact opow_dvd_opow ω h3X
  have hWsplit : leWe (X + e) = X * leWe e := by
    have h := Vn.vnWe_OmK k
    unfold leWe at h ⊢
    rw [mul_add, opow_add, h]
  have hXdW : X ∣ leWe (X + e) := by rw [hWsplit]; exact dvd_mul_right X _
  have hW0 : leWe (X + e) ≠ 0 := by unfold leWe; exact opow_ne_zero _ omega0_ne_zero
  have hdvt : Om (1 + 1 + 1) ∣ β + leWe (X + e) :=
    dvd_add ((h3dX.trans hXdW).trans hb.1) (h3dX.trans hXdW)
  have h3t : Om (1 + 1 + 1) ≤ β + leWe (X + e) :=
    (h3X.trans (Ordinal.le_of_dvd hW0 hXdW)).trans le_add_self
  have hlaw := Xm.xmTopUp S k l ηx A hl hX hA hρ e β hec he2 hβD hb
  unfold leTe at hlaw
  exact ⟨htD, htn, hdvt, h3t, hlaw⟩

/-- **REFUTE-FIRST point 1**: `ψ₂(Ω₃·2 + Ω₃)`: the `Ω₃`-part of `Ω₃·2 + Ω₃` is `Ω₃·3`, the offset `0`. -/
theorem zpTest1 :
    Om (1 + 1 + 1) * ((Om (1 + 1 + 1) * 2 + Om (1 + 1 + 1)) / Om (1 + 1 + 1)) = Om (1 + 1 + 1 : Ordinal.{0}) * 3 ∧
      Om (1 + 1 + 1) * 2 + Om (1 + 1 + 1) = Om (1 + 1 + 1 : Ordinal.{0}) * 3 := by
  have e : Om (1 + 1 + 1) * 2 + Om (1 + 1 + 1) = Om (1 + 1 + 1 : Ordinal.{0}) * 3 := by
    rw [show (3 : Ordinal.{0}) = 2 + 1 by norm_num, mul_add, mul_one]
  refine ⟨?_, e⟩
  rw [e, Ordinal.mul_div_cancel _ zpOm3_ne]

/-- **REFUTE-FIRST point 2**: `ψ₂(W^{Ω₃+1} + Y₃·2)`: `W^{Ω₃+1} = Ω₃·Ω₂` is the `Ω₃`-part, `Y₃·2 < Ω₃` the offset. -/
theorem zpTest2 :
    leWe (Om (1 + 1 + 1) + 1) = Om (1 + 1 + 1 : Ordinal.{0}) * Om (1 + 1) ∧
      Ug.ugY S * 2 < Om (1 + 1 + 1) ∧
      Om (1 + 1 + 1) * ((leWe (Om (1 + 1 + 1) + 1) + Ug.ugY S * 2) / Om (1 + 1 + 1)) =
        leWe (Om (1 + 1 + 1 : Ordinal.{0}) + 1) := by
  have hW3 : leWe (Om (1 + 1 + 1 : Ordinal.{0})) = Om (1 + 1 + 1) := by
    have h := Vn.vnWe_OmK 0
    simpa using h
  have h2 : ω ^ Om (1 + 1 : Ordinal.{0}) = Om (1 + 1) :=
    Low.opow_eq_self_of_SC ((InR_Om_succ (S := S) 1).SC S)
  have hW : leWe (Om (1 + 1 + 1) + 1) = Om (1 + 1 + 1 : Ordinal.{0}) * Om (1 + 1) := by
    have : leWe (Om (1 + 1 + 1) + 1) = leWe (Om (1 + 1 + 1 : Ordinal.{0})) * ω ^ Om (1 + 1) := by
      unfold leWe; rw [mul_add, mul_one, opow_add]
    rw [this, hW3, h2]
  have hY : Ug.ugY S < Om (1 + 1 + 1) := psi_lt (InR_Om_succ (1 + 1)) _
  have hY2 : Ug.ugY S * 2 < Om (1 + 1 + 1) := by
    rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one]
    exact (zpOm3_SC S).isPrincipal hY hY
  refine ⟨hW, hY2, ?_⟩
  rw [hW, Ordinal.mul_add_div _ zpOm3_ne, Ordinal.div_eq_zero_of_lt hY2, add_zero]

/-- **NON-VACUITY of the premises of `ZpTopLawAll`**: at every restart `b = Ω₃` satisfies them and the law. -/
theorem zpLaw_wit {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    ∃ b, VbD S l b ∧ b ∈ S.CSet b (S.psi b (Om (1 + 1))) ∧ Om (1 + 1 + 1) ∣ b ∧ Om (1 + 1 + 1) ≤ b ∧
      gxTh (upsilon l) (ldAtR S l) (S.psi b (Om (1 + 1))) =
        S.psi (A + 1 + S.psi (vbT S l b) (Om (1 + 1))) (Om 1) := by
  obtain ⟨hD, hB⟩ := Yj.yjNonvac (S := S) 0 l 0
  have h0 : GxCl (upsilon l) (ldAtR S l) 0 := GxCl.zero (vbZ hl hX).1.1
  have h02 : (0 : Ordinal.{0}) < Om (1 + 1) := Om_pos (add_pos zero_lt_one zero_lt_one).ne'
  obtain ⟨h1, h2, h3, h4, h5⟩ := zpLaw_top 0 hl hX hA hρ h0 h02 hD hB
  exact ⟨_, h1, h2, h3, h4, h5⟩

end Googology.Trans.PoR.InaccPsi.R2.Zp
