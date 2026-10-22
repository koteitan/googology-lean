import Googology.Trans.PoR.InaccPsi.R2.RoAt

/-!
# The block law at the base `Ω_ω`, truncated by `A_{η_λ}`, and bounds for `Θ_λ(θ)`

`Θ = gxTh ρ_λ (ldAtR λ)`, `A = A_{η_λ} = Ω_ω + θ·η_λ`, `θ = ψ_{Ω₂}(Ω_ω)`, `M_W = ψ_{Ω₂}(Ω_ω + Ω₂)` (`Rn.rnMW`),
`F_K = ψ_{Ω₂}(Ω₂^{Ω₂·K})`.  `Ld.ldBlk_step` asks `β + Ω₂ < A`, false at `β = Ω_ω` (`θ·η < Ω₂`); the atoms
`ψ_{Ω₂}(Ω_ω + c)` of `H_λ` are exactly those with `c ∈ H_λ`, `Ω_ω + c < A`, i.e. `c < θ·η_λ`.

* `roBlkT_step` (**THE TRUNCATED BLOCK LAW**: for a base `β` (`Ω₂ ∣ β`, `β` own for `d ≤ Ω₂`, `β ∈ H_λ`) with
  `Θ(ψ_{Ω₂}(β)) = ψ_{Ω₁}(Â)`, `Â` own: `Θ(ψ_{Ω₂}(β + c)) = ψ_{Ω₁}(Â + Θ c)` for every code `c < ψ_{Ω₂}(β + Ω₂)` with
  `β + c < A` only; the proof of `Ld.ldBlk_step` with the bound `β + c < A` in place of `β + Ω₂ < A`);
* `roThW` (**at the base `Ω_ω`: if `Θ_λ(θ) = ψ_{Ω₁}(Â)`, `Â` own, then `Θ_λ(ψ_{Ω₂}(Ω_ω + c)) = ψ_{Ω₁}(Â + Θ_λ c)` for
  every code `c < M_W` with `Ω_ω + c < A`**), `roThW_A` (the same with the expected value `Â = A + θ`);
* `roTheta_th_gt` (**`ψ_{Ω₁}(A + 1 + Ω₁^{Ω₁·K}) < Θ_λ(θ)` for every `K ≥ 1`**: `F_K < θ` is an atom).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ro

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn

variable {S : InaccSeq.{0}}

section Blk

variable {l ηx β Â : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hβown : ∀ d, d ≤ Om (1 + 1) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
  (hβd : Om (1 + 1) ∣ β) (hβH : β ∈ cdHull S l)
  (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
  (hbase : gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1))

include hl hX hβown hβd hβH hÂ hbase

/-- **THE TRUNCATED BLOCK LAW**: `Θ(ψ_{Ω₂}(β + c)) = ψ_{Ω₁}(Â + Θ(c))` for every code `c < ψ_{Ω₂}(β + Ω₂)` with
`β + c < A_{η_λ}`. -/
theorem roBlkT_step : ∀ c, GxCl (upsilon l) (ldAtR S l) c → c < ldTop S β →
    β + c < ConjT.Aη S (cdEta S l) →
    gxTh (upsilon l) (ldAtR S l) (S.psi (β + c) (Om (1 + 1))) =
      S.psi (Â + gxTh (upsilon l) (ldAtR S l) c) (Om 1) := by
  have hpv := cdEta_pv (S := S) hl.1 hX
  have hρSC : SC (upsilon l) := hpv ▸ SC_psi Low.InR_Om_one _
  have hρ1 : upsilon l < Om 1 := hpv ▸ psi_lt Low.InR_Om_one _
  have hρ0 : 0 < upsilon l := hρSC.1
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hatc : ∀ c, GxCl (upsilon l) (ldAtR S l) c → c < ldTop S β → β + c < ConjT.Aη S (cdEta S l) →
      S.psi (β + c) (Om (1 + 1)) ∈ ldAtR S l := fun c hc hcF hcA =>
    ⟨β + c, CSet.add_mem hβH ((ldHull_iff hl hX (hcF.trans (ldTop_lt_Om2 β))).2 hc), hcA, rfl⟩
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hcF hcA
  have hbat : S.psi β (Om (1 + 1)) ∈ ldAtR S l := ⟨β, hβH, le_self_add.trans_lt hcA, rfl⟩
  have hρÂ : upsilon l < S.psi Â (Om 1) := by
    rw [← hbase]; exact (ldAtom_ge hρSC hρ1 hAt hbat).2.1
  have hc2 : c < Om (1 + 1) := hcF.trans (ldTop_lt_Om2 β)
  have hsat := hatc c hc hcF hcA
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [add_zero, gxTh_zero, add_zero]; exact hbase
  have hΘc0 : 0 < gxTh (upsilon l) (ldAtR S l) c := by
    have := gxTh_lt (Z := upsilon l) (At := ldAtR S l) (GxCl.zero hρ0) (pos_iff_ne_zero.2 hc0)
    rwa [gxTh_zero] at this
  obtain ⟨hTSC, -, hTs⟩ := ldAtom_ge hρSC hρ1 hAt hsat
  have hβs := ldBase_lt hβown hc0 hcF
  have hÂb : Â ∈ S.CSet (Â + gxTh (upsilon l) (ldAtR S l) c)
      (S.psi (Â + gxTh (upsilon l) (ldAtR S l) c) (Om 1)) :=
    (psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ
  have hbaseb : S.psi Â (Om 1) < S.psi (Â + gxTh (upsilon l) (ldAtR S l) c) (Om 1) :=
    psi_lt_psi_of_mem Low.InR_Om_one (lt_add_of_pos_right Â hΘc0) hÂb
  apply le_antisymm
  · refine ldAtom_le hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) (hρÂ.trans hbaseb) ?_
    intro t ht hts
    rcases ldBlk_cls hl hX hβown hβd ht (hts.trans (ldTop_lt hβown hcF)) with hle | ⟨c', hc'g, hc'F, rfl⟩
    · exact (gxTh_mono hle).trans_lt (by rw [hbase]; exact hbaseb)
    · have hc'c : c' < c := by
        by_contra h
        push Not at h
        exact absurd hts (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 h)).1)
      have hc'A : β + c' < ConjT.Aη S (cdEta S l) := ((add_lt_add_iff_left β).2 hc'c).trans hcA
      have hIH := IH c' hc'c hc'g hc'F hc'A
      rw [hIH]
      have hΘ' : gxTh (upsilon l) (ldAtR S l) c' < gxTh (upsilon l) (ldAtR S l) c := gxTh_lt hc'g hc'c
      have hΘ'b : gxTh (upsilon l) (ldAtR S l) c' < S.psi (Â + gxTh (upsilon l) (ldAtR S l) c) (Om 1) := by
        have h1 := gxTh_lt hc'g (ldTop_gt hβown hβd hc'F)
        rw [hIH] at h1
        exact h1.trans_le (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left Â).2 hΘ'.le)).1
      exact psi_lt_psi_of_mem Low.InR_Om_one ((add_lt_add_iff_left Â).2 hΘ')
        (CSet.add_mem hÂb (CSet.of_lt hΘ'b))
  · refine ldPsi1_le hTSC fun e he _ => ?_
    rcases le_or_gt e Â with heÂ | heÂ
    · refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one heÂ).1 ?_
      rw [← hbase]; exact hTs _ hbat hβs
    · obtain ⟨d, rfl⟩ := exists_add_of_le heÂ.le
      have hd : d < gxTh (upsilon l) (ldAtR S l) c := (add_lt_add_iff_left Â).1 he
      obtain ⟨c', hc'g, hc'c, rfl⟩ := gxTh_onto hd
      have hc'F := hc'c.trans hcF
      have hc'A : β + c' < ConjT.Aη S (cdEta S l) := ((add_lt_add_iff_left β).2 hc'c).trans hcA
      have ht's : S.psi (β + c') (Om (1 + 1)) < S.psi (β + c) (Om (1 + 1)) :=
        psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left β).2 hc'c)
          (CSet.add_mem (hβown c hc2.le) (CSet.of_lt (hc'c.trans (ldTop_gt hβown hβd hcF))))
      rw [← IH c' hc'c hc'g hc'F hc'A]
      exact hTs _ (hatc c' hc'g hc'F hc'A) ht's

end Blk

theorem roOmW_mem (a b : Ordinal.{0}) : Om ω ∈ S.CSet a b := by
  have hω : (ω : Ordinal.{0}) ∈ S.CSet a b := by
    have := CSet.phi_mem (S := S) (CSet.zero_mem a b) (CSet.one_mem a b)
    rwa [veblen_zero_apply, opow_one] at this
  exact CSet.Om_mem hω

theorem roW_dvd_OmW : Om (1 + 1 : Ordinal.{0}) ∣ Om ω := by
  conv_rhs => rw [← gg_SC_eps (SC_Om omega0_ne_zero)]
  conv_lhs => rw [← gg_SC_eps ldOm2_SC]
  exact opow_dvd_opow ω ldOm2_lt_OmW.le

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The block law at the base `Ω_ω`**, given `Θ_λ(θ) = ψ_{Ω₁}(Â)`, `Â` own. -/
theorem roThW {Â : Ordinal.{0}} (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hθ : gxTh (upsilon l) (ldAtR S l) (ConjT.th S) = S.psi Â (Om 1)) :
    ∀ c, GxCl (upsilon l) (ldAtR S l) c → c < rnMW S → Om ω + c < ConjT.Aη S (cdEta S l) →
      gxTh (upsilon l) (ldAtR S l) (S.psi (Om ω + c) (Om (1 + 1))) =
        S.psi (Â + gxTh (upsilon l) (ldAtR S l) c) (Om 1) := by
  have hownW : ∀ d, d ≤ Om (1 + 1) → Om ω ∈ S.CSet (Om ω + d) (S.psi (Om ω + d) (Om (1 + 1))) :=
    fun d _ => roOmW_mem _ _
  have hH : Om ω ∈ cdHull S l := roOmW_mem _ _
  exact roBlkT_step hl hX hownW roW_dvd_OmW hH hÂ hθ

/-- **The block law at the base `Ω_ω` with the expected reading `Θ_λ(θ) = ψ_{Ω₁}(A + θ)`.** -/
theorem roThW_A {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hAη : A = ConjT.Aη S (cdEta S l))
    (hθ : gxTh (upsilon l) (ldAtR S l) (ConjT.th S) = S.psi (A + ConjT.th S) (Om 1)) :
    ∀ c, GxCl (upsilon l) (ldAtR S l) c → c < rnMW S → Om ω + c < A →
      gxTh (upsilon l) (ldAtR S l) (S.psi (Om ω + c) (Om (1 + 1))) =
        S.psi (A + ConjT.th S + gxTh (upsilon l) (ldAtR S l) c) (Om 1) := by
  have hθ0 : 0 < ConjT.th S := (Om_pos one_ne_zero).trans (psiS_bounds (S := S) _ 1).1
  have hWA : Om ω < A + ConjT.th S := by
    rw [hAη]; unfold ConjT.Aη
    exact lt_of_le_of_lt le_self_add (lt_add_of_pos_right _ hθ0)
  have hÂ : A + ConjT.th S ∈ S.CSet (A + ConjT.th S) (S.psi (A + ConjT.th S) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA)
      (CSet.psi_mem hWA (InR_Om_succ 1) (mxOm2_mem _ _) (roOmW_mem _ _))
  intro c hc hcM hcA
  exact roThW hl hX hÂ hθ c hc hcM (hAη ▸ hcA)

/-- **`ψ_{Ω₁}(A + 1 + Ω₁^{Ω₁·K}) < Θ_λ(θ)` for every `K ≥ 1`.** -/
theorem roTheta_th_gt {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    {K : ℕ} (hK : 1 ≤ K) :
    S.psi (A + 1 + leOe (Om 1 * (K : Ordinal.{0}))) (Om 1) < gxTh (upsilon l) (ldAtR S l) (ConjT.th S) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hc0 : GxCl (upsilon l) (ldAtR S l) (0 : Ordinal.{0}) := GxCl.zero hρSC.1
  have h := roTh_k0 hl hX hA hρ hK hc0 (fun e' _ h' => by
    obtain rfl : e' = 0 := le_antisymm h' zero_le
    exact (SC_psi (InR_Om_succ 1) _).1)
  rw [add_zero, gxTh_zero, add_zero] at h
  have hKW : Om (1 + 1) * (K : Ordinal.{0}) < Om ω :=
    ldMulNat_lt (Om_isPrincipal omega0_ne_zero) ldOm2_lt_OmW K
  have hat : S.psi (leWe (Om (1 + 1) * (K : Ordinal.{0}))) (Om (1 + 1)) ∈ ldAtR S l :=
    ⟨_, leWe_mem (mul_nat_mem (mxOm2_mem _ _) K),
      (roWe_lt_OmW hKW).trans_le (by unfold ConjT.Aη; exact le_self_add), rfl⟩
  rw [← h]
  exact gxTh_lt (GxCl.atom hat) roFK_lt_th

end Main

end Googology.Trans.PoR.InaccPsi.R2.Ro
