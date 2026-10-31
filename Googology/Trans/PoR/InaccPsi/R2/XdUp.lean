import Googology.Trans.PoR.InaccPsi.R2.XdTr

/-!
# `WzUpU` is a theorem: `Θ(ψ_{Ω₂}(a)) ≤ ψ_{Ω₁}(A + 1 + ψ_{Ω₂}(T a))` for every `a` in the domain of `T`

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Vb.vbT S λ`, `D = Vb.VbD S λ`, `A = A_{η_λ}` (own, `ψ₁(A) = ρ_λ`),
`σ(a) = ψ₁(A + 1 + ψ₂(T a))`.

Proof (one well-founded induction on `a`, inside it one on the atoms `t < ψ₂(a)`): the reading of `ψ₂(a)` is at most
every strongly critical `X > ρ_λ` above the readings of the atoms below `ψ₂(a)` (`Ld.ldAtom_le`); take `X = σ(a)`.
An atom `t < ψ₂(a)` is `ψ₂(d)` with a normal `d ∈ D`, `d < a`; by the outer induction `Θ(t) ≤ σ(d)`, and
`σ(d) < σ(a)`: `ψ₂(T d) < ψ₂(T a)` by the transfer (`Xd.xdT_psi_lt`), and `T d ∈ Cl(A + 1 + ψ₂(T a), σ(a))`
by the generic transfer `Xd.xdT_cl` with the codes `c < ψ₂(d)` of `d` read below `σ(a)` (inner induction and
`Mx.mxGx_bound`).

* `xdUp_at` (**the bound at every `a ∈ D`**, normal or not), `xdUpU` (**`Wz.WzUpU S` holds**);
* `xdLaw0` (**the law at `k = 0`, `β = Ω₃`**: `Wg.WgTopAt S λ Ω₃ (X̂⁰_0(Ω₃)) 0 Ω₃`, from `Wz.wzLaw_of_U`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rx
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}}

theorem xdOm2_mem (a b : Ordinal.{0}) : Om (1 + 1 : Ordinal.{0}) ∈ S.CSet a b :=
  CSet.Om_mem (CSet.add_mem (CSet.one_mem a b) (CSet.one_mem a b))

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE UPPER BOUND AT EVERY MEMBER OF THE DOMAIN**: `Θ(ψ₂(a)) ≤ ψ₁(A + 1 + ψ₂(T a))`. -/
theorem xdUp_at {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    ∀ a, VbD S l a → gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) ≤
      S.psi (A + 1 + S.psi (vbT S l a) (Om (1 + 1))) (Om 1) := by
  obtain ⟨-, rfl⟩ := Wg.wgOwnEta hl hX hA hρ
  obtain ⟨hρSC, hρ1⟩ := vbZ hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hAω : Om ω ≤ ConjT.Aη S (cdEta S l) := by unfold ConjT.Aη; exact le_self_add
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IHo =>
  intro ha
  have hσSC : SC (S.psi (ConjT.Aη S (cdEta S l) + 1 + S.psi (vbT S l a) (Om (1 + 1))) (Om 1)) :=
    SC_psi Low.InR_Om_one _
  have hρσ : upsilon l < S.psi (ConjT.Aη S (cdEta S l) + 1 + S.psi (vbT S l a) (Om (1 + 1))) (Om 1) := by
    rw [← hρ]
    exact (mxPsi_succ_gt hA).trans_le (psi_mono (S := S) Low.InR_Om_one le_self_add).1
  have hTa_lt : ∀ e, VbD S l e →
      vbT S l e < ConjT.Aη S (cdEta S l) + 1 + S.psi (vbT S l a) (Om (1 + 1)) := fun e he =>
    (vbT_mem hl hX he).2.trans_le (hAω.trans (le_self_add.trans le_self_add))
  have hin : ∀ t, t ∈ ldAtR S l → t < S.psi a (Om (1 + 1)) → gxTh (upsilon l) (ldAtR S l) t <
      S.psi (ConjT.Aη S (cdEta S l) + 1 + S.psi (vbT S l a) (Om (1 + 1))) (Om 1) := by
    intro t
    induction t using WellFoundedLT.induction with
    | ind t IHi =>
    intro ht hta
    obtain ⟨a0, ha0C, ha0A, ht0⟩ := ht
    have hth : S.psi a (Om (1 + 1)) < ConjT.th S :=
      psi_lt_psi_of_mem (InR_Om_succ 1) ha.2.2 ha.2.1
    have hb1 := psiS_bounds (S := S) a0 1
    rw [← ht0] at hb1
    have hVt : VbD S l t := by
      refine ⟨?_, CSet.of_lt (hta.trans hth), hb1.2.trans (Om_lt_Om.2 (by simpa using Vb.vbNat_lt_omega 0))⟩
      rw [ht0]; exact CSet.psi_mem ha0A (InR_Om_succ 1) (xdOm2_mem _ _) ha0C
    have hne : ¬ ∃ j : ℕ, t = Om (j : Ordinal.{0}) := fun ⟨j, hj⟩ => not_Om_of_between hb1.1 hb1.2 _ hj
    obtain ⟨k, hk, d, hdE, hdn, hxd, -⟩ :=
      rxE_atom hρ1.le (vbD_E hl hX hVt) (ht0 ▸ SC_psi (InR_Om_succ 1) a0) hb1.1 hne
    have hbk := psiS_bounds (S := S) d (k : Ordinal.{0})
    rw [← hxd] at hbk
    have hk1 : (k : Ordinal.{0}) = 1 := between_unique hbk.1 hbk.2 hb1.1 hb1.2
    have hdD : VbD S l d := vbD_atom hl hX (hxd ▸ hVt) hdE hdn hk
    rw [hk1] at hxd hdn
    have hlt : S.psi d (Om (1 + 1)) < S.psi a (Om (1 + 1)) := hxd ▸ hta
    have hda : d < a := by
      by_contra hc
      exact absurd hlt (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) (not_lt.1 hc)).1)
    have hO := IHo d hda hdD
    -- the codes of `d` are read below `σ(a)`
    have hatoms : ∀ s ∈ ldAtR S l, s < S.psi d (Om (1 + 1)) → gxTh (upsilon l) (ldAtR S l) s <
        S.psi (ConjT.Aη S (cdEta S l) + 1 + S.psi (vbT S l a) (Om (1 + 1))) (Om 1) :=
      fun s hs hsd => IHi s (hxd ▸ hsd) hs (hsd.trans hlt)
    have hTdC : vbT S l d ∈ S.CSet (ConjT.Aη S (cdEta S l) + 1 + S.psi (vbT S l a) (Om (1 + 1)))
        (S.psi (ConjT.Aη S (cdEta S l) + 1 + S.psi (vbT S l a) (Om (1 + 1))) (Om 1)) := by
      refine xdT_cl hl hX (psi_lt (InR_Om_succ 1) d).le (fun e he _ => hTa_lt e he)
        (fun c hc hc2 hcC => ?_) d hdD hdn
      rw [vbT_code hl hX hc2 hc.1]
      exact CSet.of_lt (mxGx_bound hρSC hρ1 hAt hσSC hρσ hatoms c ((ldHull_iff hl hX hc2).1 hc.1)
        (lt_psi_of_mem (InR_Om_succ 1) hcC hc2))
    have hB : ConjT.Aη S (cdEta S l) + 1 + S.psi (vbT S l d) (Om (1 + 1)) <
        ConjT.Aη S (cdEta S l) + 1 + S.psi (vbT S l a) (Om (1 + 1)) :=
      (add_lt_add_iff_left _).2 (xdT_psi_lt hl hX ha hdD hdn hlt)
    have hBm : ConjT.Aη S (cdEta S l) + 1 + S.psi (vbT S l d) (Om (1 + 1)) ∈
        S.CSet (ConjT.Aη S (cdEta S l) + 1 + S.psi (vbT S l a) (Om (1 + 1)))
          (S.psi (ConjT.Aη S (cdEta S l) + 1 + S.psi (vbT S l a) (Om (1 + 1))) (Om 1)) := by
      refine CSet.add_mem (CSet.add_mem ?_ (CSet.one_mem _ _))
        (CSet.psi_mem (hTa_lt d hdD) (InR_Om_succ 1) (xdOm2_mem _ _) hTdC)
      exact (psi_mono (S := S) Low.InR_Om_one (le_self_add.trans le_self_add)).2 hA
    rw [hxd]
    exact hO.trans_lt (psi_lt_psi_of_mem Low.InR_Om_one hB hBm)
  exact ldAtom_le hρSC hρ1 hAt hσSC hρσ hin

end Rst

/-- **`Wz.WzUpU S` IS A THEOREM.** -/
theorem xdUpU : Wz.WzUpU S := fun _ _ _ a hl hX hA hρ ha _ => xdUp_at hl hX hA hρ a ha

/-- **THE LAW AT `k = 0`, `β = Ω₃`** (`skX0Law` there): `Θ(ψ₂(Ω₃·2)) = ψ₁(Â + Ω^{X̂⁰_0(Ω₃)})`. -/
theorem xdLaw0 {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    Wg.WgTopAt S l (Om (1 + 1 + 1)) (Wv.wvX0 S l 0 (Om (1 + 1 + 1))) 0 (Om (1 + 1 + 1)) :=
  Wz.wzLaw_of_U hl hX xdUpU hA hρ

end Googology.Trans.PoR.InaccPsi.R2.Xd

#print axioms Googology.Trans.PoR.InaccPsi.R2.Xd.xdUp_at
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xd.xdUpU
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xd.xdLaw0
