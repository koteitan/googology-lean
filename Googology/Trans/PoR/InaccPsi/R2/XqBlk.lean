import Googology.Trans.PoR.InaccPsi.R2.XmLim

/-!
# The block law above every top atom, and the refutation of the `ψ₂(T a)` form off the tops

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Vb.vbT S λ`, `D = Vb.VbD S λ`, `A = A_{η_λ}` (own, `ψ₁(A) = ρ_λ`),
`σ(a) = ψ₁(A + 1 + ψ₂(T a))`, `F^a = ψ₂(a + Ω₂)` (`Ld.ldTop`).

* `xqOwn` (**`A + 1 + ψ₂(T a)` is own for every normal `a ∈ D`**: `T a ∈ Cl(Â, ψ₁ Â)` by the transfer `Xd.xdT_cl`,
  the codes of `a` being read below `Θ(ψ₂ a) ≤ σ(a)`, `Xd.xdUp_at`);
* `xqBlk` (**THE BLOCK LAW WITH THE `T` VALUE**: if `Θ(ψ₂ a) = σ(a)` at a normal `a ∈ D` with `Ω₂ ∣ a`, own for the
  offsets `d ≤ Ω₂`, then `Θ(ψ₂(a + c)) = ψ₁(A + 1 + ψ₂(T a) + Θ c)` for every code `c < F^a`, and
  `Θ(F^a) = ψ₁(A + 1 + ψ₂(T a) + Ω₁)`);
* `xqTopBlk` (**the block above every top atom `t = β + W^{Ω_{k+3}+e}`**, from `Xm.xmTopUp`, unconditional
  beyond the base hypotheses of `Xi.XiTopUp`);
* `xqRef` (**REFUTATION** at `a = Ω₃ + 1`: `Θ(ψ₂(Ω₃ + 1)) = ψ₁(A + 1 + ψ₂(Ω₂) + 1) < ψ₁(A + 1 + ψ₂(T(Ω₃ + 1)))`
  at every restart with own `A`, so the law `Θ(ψ₂ a) = σ(a)` fails off the top atoms), `xqRef_wit` (at the restart of
  `m* = L(0)`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt

variable {S : InaccSeq.{0}}

section Rst

variable {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hl hX hA hρ

/-- **`A + 1 + ψ₂(T a)` is own** for every normal `a ∈ D`. -/
theorem xqOwn {a : Ordinal.{0}} (ha : VbD S l a) (han : a ∈ S.CSet a (S.psi a (Om (1 + 1)))) :
    A + 1 + S.psi (vbT S l a) (Om (1 + 1)) ∈ S.CSet (A + 1 + S.psi (vbT S l a) (Om (1 + 1)))
      (S.psi (A + 1 + S.psi (vbT S l a) (Om (1 + 1))) (Om 1)) := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hAÂ : A ≤ A + 1 + S.psi (vbT S l a) (Om (1 + 1)) := le_self_add.trans le_self_add
  have hAω : Om ω ≤ A := Vn.vnA_ge hl hX hA hρ
  have hTlt : ∀ e, VbD S l e → vbT S l e < A + 1 + S.psi (vbT S l a) (Om (1 + 1)) := fun e he =>
    (vbT_mem hl hX he).2.trans_le (hAω.trans hAÂ)
  have hTa : vbT S l a ∈ S.CSet (A + 1 + S.psi (vbT S l a) (Om (1 + 1)))
      (S.psi (A + 1 + S.psi (vbT S l a) (Om (1 + 1))) (Om 1)) := by
    refine Xd.xdT_cl hl hX (psi_lt hκ2 a).le (fun e he _ => hTlt e he) (fun c hc hc2 hcC => ?_) a ha han
    rw [vbT_code hl hX hc2 hc.1]
    refine CSet.of_lt ?_
    have hcode : GxCl (upsilon l) (ldAtR S l) c := (ldHull_iff hl hX hc2).1 hc.1
    exact (gxTh_lt hcode (lt_psi_of_mem hκ2 hcC hc2)).trans_le (Xd.xdUp_at hl hX hA hρ a ha)
  exact CSet.add_mem (CSet.add_mem ((psi_mono (S := S) hκ1 hAÂ).2 hA) (CSet.one_mem _ _))
    (CSet.psi_mem (hTlt a ha) hκ2 (Xd.xdOm2_mem _ _) hTa)

/-- **THE BLOCK LAW WITH THE `T` VALUE**: at a normal base `a ∈ D` (`Ω₂ ∣ a`, own for `d ≤ Ω₂`) where the law
`Θ(ψ₂ a) = ψ₁(A + 1 + ψ₂(T a))` holds, `Θ(ψ₂(a + c)) = ψ₁(A + 1 + ψ₂(T a) + Θ c)` for every code `c < F^a`, and
`Θ(F^a) = ψ₁(A + 1 + ψ₂(T a) + Ω₁)`. -/
theorem xqBlk {a : Ordinal.{0}} (ha : VbD S l a) (hd : Om (1 + 1) ∣ a)
    (hown : ∀ d, d ≤ Om (1 + 1) → a ∈ S.CSet (a + d) (S.psi (a + d) (Om (1 + 1))))
    (hlaw : gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) =
      S.psi (A + 1 + S.psi (vbT S l a) (Om (1 + 1))) (Om 1)) :
    (∀ c, GxCl (upsilon l) (ldAtR S l) c → c < ldTop S a →
      gxTh (upsilon l) (ldAtR S l) (S.psi (a + c) (Om (1 + 1))) =
        S.psi (A + 1 + S.psi (vbT S l a) (Om (1 + 1)) + gxTh (upsilon l) (ldAtR S l) c) (Om 1)) ∧
    gxTh (upsilon l) (ldAtR S l) (ldTop S a) =
      S.psi (A + 1 + S.psi (vbT S l a) (Om (1 + 1)) + Om 1) (Om 1) := by
  have han : a ∈ S.CSet a (S.psi a (Om (1 + 1))) := by
    have h := hown 0 zero_le; rwa [add_zero] at h
  have hÂ := xqOwn hl hX hA hρ ha han
  have hA2 : a + Om (1 + 1) < ConjT.Aη S (cdEta S l) :=
    Vq.vqOm3_lt_A l (vkOmW.1.isPrincipal ha.2.2 ldOm2_lt_OmW)
  exact ⟨ldBlk_step hl hX hown hd ha.1 hA2 hÂ hlaw, ldBlk_next hl hX hown hd ha.1 hA2 hÂ hlaw⟩

/-- **THE BLOCK ABOVE EVERY TOP ATOM** `t = β + W^{Ω_{k+3}+e}` (a code `e < Ω₂`, `β ∈ D` a base of exponent `e`):
`Θ(ψ₂(t + c)) = ψ₁(A + 1 + ψ₂(T t) + Θ c)` for every code `c < F^t`, and `Θ(F^t) = ψ₁(A + 1 + ψ₂(T t) + Ω₁)`. -/
theorem xqTopBlk (k : ℕ) {e β : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (he2 : e < Om (1 + 1))
    (hβD : VbD S l β) (hB : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β) :
    (∀ c, GxCl (upsilon l) (ldAtR S l) c → c < ldTop S (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) →
      gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) + c) (Om (1 + 1))) =
        S.psi (A + 1 + S.psi (vbT S l (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e))) (Om (1 + 1)) +
          gxTh (upsilon l) (ldAtR S l) c) (Om 1)) ∧
    gxTh (upsilon l) (ldAtR S l) (ldTop S (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e))) =
      S.psi (A + 1 + S.psi (vbT S l (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e))) (Om (1 + 1)) + Om 1)
        (Om 1) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hlaw := Xm.xmTopUp S k l ηx A hl hX hA hρ e β hec he2 hβD hB
  unfold leTe at hlaw
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  have hXmem : ∀ a c : Ordinal.{0}, X ∈ S.CSet a c := Vn.vnOmK3_mem k
  have hXW : X < Om ω := Wv.wvOmK_lt_W k
  obtain ⟨hβd, hβH, -, hβown, hexpA⟩ := hB
  have hexp : e < S.psi (β + leWe (X + e)) (Om (1 + 1)) := hexpA e hec le_rfl
  have hβW : β < Om ω := hβD.2.2
  have hgW : X + e < Om ω := vkOmW.1.isPrincipal hXW (he2.trans ldOm2_lt_OmW)
  have hwW : leWe (X + e) < Om ω := (leWe_lt_SC vkOmW.1 vkOmW.2 hgW).1
  have heθ : e < ConjT.th S := hexp.trans_le (psi_mono hκ2 (vkOmW.1.isPrincipal hβW hwW).le).1
  have hD : VbD S l (β + leWe (X + e)) :=
    ⟨CSet.add_mem hβH (leWe_mem (CSet.add_mem (hXmem _ _) ((ldHull_iff hl hX he2).2 hec))),
      CSet.add_mem hβD.2.1 (leWe_mem (CSet.add_mem (hXmem _ _) (CSet.of_lt heθ))),
      vkOmW.1.isPrincipal hβW hwW⟩
  have h1g : (1 : Ordinal.{0}) ≤ X + e :=
    (Order.one_le_iff_pos.2 (Om_pos (add_pos_of_right zero_lt_one _).ne')).trans le_self_add
  have hW2 : Om (1 + 1) ∣ leWe (X + e) := by
    have h := leWe_dvd h1g; rwa [leWe_one] at h
  have hd : Om (1 + 1) ∣ β + leWe (X + e) := dvd_add (hW2.trans hβd) hW2
  have hown : ∀ d, d ≤ Om (1 + 1) → β + leWe (X + e) ∈
      S.CSet (β + leWe (X + e) + d) (S.psi (β + leWe (X + e) + d) (Om (1 + 1))) := by
    intro d _
    have hle : β + leWe (X + e) ≤ β + leWe (X + e) + d := le_self_add
    have hβm := (psi_mono (S := S) hκ2 hle).2 (hβown _ le_rfl)
    have hem : e ∈ S.CSet (β + leWe (X + e) + d) (S.psi (β + leWe (X + e) + d) (Om (1 + 1))) :=
      CSet.of_lt (hexp.trans_le (psi_mono hκ2 hle).1)
    exact CSet.add_mem hβm (leWe_mem (CSet.add_mem (hXmem _ _) hem))
  exact xqBlk hl hX hA hρ hD hd hown hlaw

/-- **THE REFUTATION OFF THE TOPS** at `a = Ω₃ + 1` (`k = 0`, `β = Ω₃` the top of exponent `0` over `0`):
`Θ(ψ₂(Ω₃ + 1)) = ψ₁(A + 1 + ψ₂(Ω₂) + 1) < ψ₁(A + 1 + ψ₂(T(Ω₃ + 1)))`, while `Ω₃ + 1 ∈ D` is normal. -/
theorem xqRef :
    VbD S l (Om (1 + 1 + 1) + 1) ∧
    Om (1 + 1 + 1) + 1 ∈ S.CSet (Om (1 + 1 + 1) + 1) (S.psi (Om (1 + 1 + 1) + 1) (Om (1 + 1))) ∧
    gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1) + 1) (Om (1 + 1))) =
      S.psi (A + 1 + S.psi (Om (1 + 1)) (Om (1 + 1)) + 1) (Om 1) ∧
    S.psi (A + 1 + S.psi (Om (1 + 1)) (Om (1 + 1)) + 1) (Om 1) <
      S.psi (A + 1 + S.psi (vbT S l (Om (1 + 1 + 1) + 1)) (Om (1 + 1))) (Om 1) := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have h1ρ : (1 : Ordinal.{0}) < upsilon l := gg_one_lt_of_SC hρSC
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small h1ρ.le
  have h1c : GxCl (upsilon l) (ldAtR S l) 1 := GxCl.small h1ρ
  have h12 : (1 : Ordinal.{0}) < Om (1 + 1) := gg_one_lt_of_SC ldOm2_SC
  have h1H : (1 : Ordinal.{0}) ∈ cdHull S l := (ldHull_iff hl hX h12).2 h1c
  have h1D : VbD S l 1 := ⟨h1H, CSet.one_mem _ _, h12.trans ldOm2_lt_OmW⟩
  have h3D : VbD S l (Om (1 + 1 + 1)) := Wz.wzD_Om3
  have hT3 : vbT S l (Om (1 + 1 + 1)) = Om (1 + 1) := by
    have h := vbT_Om (S := S) hl hX (k := 2) (by norm_num); rwa [Wz.wzTwo] at h
  have hT1 : vbT S l 1 = 1 := by rw [vbT_code hl hX h12 h1H, hΘ1]
  have hT31 : vbT S l (Om (1 + 1 + 1) + 1) = Om (1 + 1) + 1 := by
    rw [Vh.vhT_add hl hX h3D h1D, hT3, hT1]
  have hD31 : VbD S l (Om (1 + 1 + 1) + 1) :=
    ⟨CSet.add_mem h3D.1 h1H, CSet.add_mem h3D.2.1 (CSet.one_mem _ _),
      vkOmW.1.isPrincipal Ry.ryOm3_lt (h12.trans ldOm2_lt_OmW)⟩
  have hd : Om (1 + 1) ∣ Om (1 + 1 + 1) := by
    have h := leWe_dvd (Order.one_le_iff_pos.2 (Om_pos (add_pos_of_right zero_lt_one _).ne') :
      (1 : Ordinal.{0}) ≤ Om (1 + 1 + 1))
    rwa [leWe_one, Vn.vnWe_Om3] at h
  have hlaw : gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1)) (Om (1 + 1))) =
      S.psi (A + 1 + S.psi (vbT S l (Om (1 + 1 + 1))) (Om (1 + 1))) (Om 1) := by
    rw [hT3]; exact Wz.wzBase hl hX hA hρ
  have hblk := (xqBlk hl hX hA hρ h3D hd (fun _ _ => Ry.ryOm3_mem _ _) hlaw).1 1 h1c
    (gg_one_lt_of_SC (ldTop_SC _))
  rw [hΘ1, hT3] at hblk
  refine ⟨hD31, CSet.add_mem (Ry.ryOm3_mem _ _) (CSet.one_mem _ _), hblk, ?_⟩
  rw [hT31]
  have hY : S.psi (Om (1 + 1)) (Om (1 + 1)) < S.psi (Om (1 + 1) + 1) (Om (1 + 1)) :=
    psi_lt_psi_of_mem hκ2 (lt_add_one _) (mxOm2_mem _ _)
  have hY1 : S.psi (Om (1 + 1)) (Om (1 + 1)) + 1 < S.psi (Om (1 + 1) + 1) (Om (1 + 1)) := by
    have := (SC_psi hκ2 (Om (1 + 1) + 1)).isSuccLimit.succ_lt hY; rwa [Order.succ_eq_add_one] at this
  have hle : A ≤ A + 1 + S.psi (Om (1 + 1) + 1) (Om (1 + 1)) := le_self_add.trans le_self_add
  have hΩ2 : Om (1 + 1) < A + 1 + S.psi (Om (1 + 1) + 1) (Om (1 + 1)) :=
    (vkOmW.2.trans_le (Vn.vnA_ge hl hX hA hρ)).trans_le hle
  refine psi_lt_psi_of_mem hκ1 ?_ ?_
  · rw [add_assoc (A + 1)]; exact (add_lt_add_iff_left _).2 hY1
  · exact CSet.add_mem (CSet.add_mem (CSet.add_mem ((psi_mono (S := S) hκ1 hle).2 hA) (CSet.one_mem _ _))
      (Vq.vqY2_mem hΩ2)) (CSet.one_mem _ _)

/-- The law `Θ(ψ₂ a) = ψ₁(A + 1 + ψ₂(T a))` FAILS at the normal member `a = Ω₃ + 1 ∈ D`. -/
theorem xqRef_ne :
    gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1) + 1) (Om (1 + 1))) ≠
      S.psi (A + 1 + S.psi (vbT S l (Om (1 + 1 + 1) + 1)) (Om (1 + 1))) (Om 1) := by
  obtain ⟨-, -, h1, h2⟩ := xqRef hl hX hA hρ
  rw [h1]; exact h2.ne

end Rst

/-- **UNCONDITIONAL**: at the restart of `m* = L(0)` (own `A`) the `ψ₂(T a)` law fails at the normal `a = Ω₃ + 1 ∈ D`. -/
theorem xqRef_wit (S : InaccSeq.{0}) :
    ∃ l ηx A : Ordinal.{0}, IsRestartIdx l ∧ upsilon l < Pv S ηx ∧ A ∈ S.CSet A (S.psi A (Om 1)) ∧
      S.psi A (Om 1) = upsilon l ∧ VbD S l (Om (1 + 1 + 1) + 1) ∧
      Om (1 + 1 + 1) + 1 ∈ S.CSet (Om (1 + 1 + 1) + 1) (S.psi (Om (1 + 1 + 1) + 1) (Om (1 + 1))) ∧
      gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1) + 1) (Om (1 + 1))) ≠
        S.psi (A + 1 + S.psi (vbT S l (Om (1 + 1 + 1) + 1)) (Om (1 + 1))) (Om 1) := by
  obtain ⟨l, hl, -, hX, hA, hρ⟩ := Xd.xdWit S
  obtain ⟨hD, hn, -, -⟩ := xqRef hl hX hA hρ
  exact ⟨l, _, _, hl, hX, hA, hρ, hD, hn, xqRef_ne hl hX hA hρ⟩

end Googology.Trans.PoR.InaccPsi.R2.Xq

#print axioms Googology.Trans.PoR.InaccPsi.R2.Xq.xqOwn
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xq.xqBlk
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xq.xqTopBlk
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xq.xqRef
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xq.xqRef_wit
