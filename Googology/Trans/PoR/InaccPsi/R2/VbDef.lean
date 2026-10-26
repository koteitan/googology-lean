import Googology.Trans.PoR.InaccPsi.R2.ThLow

/-!
# The image one level down, generic in the level: the inverse of the level shift `κ_λ`

`ρ_λ = υ_λ`, `H_λ = cdHull S λ`, `Θ = gxTh ρ_λ (ldAtR λ)` (the reading of the codes `< Ω₂`), `W_λ = min(Θ(Ω₂), Ω₁)`
(`vbW`), `κ_λ = Rx.rxL S ρ_λ (ldAtR λ) W_λ` (`vbK`: `Θ⁻¹` below `Ω₁`, `Ω_k ↦ Ω_{k+1}`,
`ψ_{Ω_{k+1}}(d) ↦ ψ_{Ω_{k+2}}(κ d)`
at every finite level `k ≥ 1`, Cantor and Veblen normal forms kept), `RxE S W` the domain of `κ_λ`, `θ = ψ_{Ω₂}(Ω_ω)`.

* `VbD S λ x` (**the domain of the image**): `x ∈ H_λ`, `x ∈ Cl(Ω_ω, θ)`, `x < Ω_ω`;
* `vbT S λ x` (**THE IMAGE ONE LEVEL DOWN**, `T x`): the member `y` of the domain of `κ_λ` with `κ_λ(y) = x`, `0` if
  there is none.  One definition for every level: `Ω_{k+1} ↦ Ω_k`, `ψ_{Ω_{k+1}}(d) ↦ ψ_{Ω_k}(T d)` and `Θ` on the codes
  `< Ω₂` all come out of the equations of `κ_λ` (module `VbLaw`), once every member of the domain is a value of `κ_λ`
  (module `VbOnto`);
* `vbT_spec`, `vbK_inj`, `vbT_K` (`T(κ y) = y`), `vbT_lt` (`T` is strictly increasing on the values of `κ_λ`);
* `vbZ2_le` (**the readings of the codes are countable**: `Θ(Ω₂) ≤ Ω₁`, since `H_λ` is countable), `vbW_eq`;
* `vbCode_K` (**a code `x < Ω₂` of `H_λ` is `κ_λ(Θ x)`**), `vbHullN` (**`H_λ` lies in the normal hull over `ρ_λ`**),
  `vbD_E`, `vbC_rem`, `vbD_log`, `vbD_rem`, `vbD_veb`, `vbD_atom` (the parts of a member of the domain are members).

No new axiom.  New definitions: `vbW`, `vbK` (abbreviations), `VbD`, `vbT`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vb

open Ordinal Order Set Cardinal Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

/-- The bound `W_λ = min(Θ_λ(Ω₂), Ω₁)` of the countable members of the domain of `κ_λ`. -/
noncomputable abbrev vbW (S : InaccSeq.{0}) (l : Ordinal.{0}) : Ordinal.{0} := rxW (upsilon l) (ldAtR S l)

/-- **The level shift at `λ`**. -/
noncomputable abbrev vbK (S : InaccSeq.{0}) (l y : Ordinal.{0}) : Ordinal.{0} :=
  rxL S (upsilon l) (ldAtR S l) (vbW S l) y

/-- **The domain of the image**: members of `H_λ` in `Cl(Ω_ω, θ)` below `Ω_ω`. -/
def VbD (S : InaccSeq.{0}) (l x : Ordinal.{0}) : Prop :=
  x ∈ cdHull S l ∧ x ∈ S.CSet (Om ω) (ConjT.th S) ∧ x < Om ω

open Classical in
/-- **THE IMAGE ONE LEVEL DOWN**: the member `y` of the domain of `κ_λ` with `κ_λ(y) = x` (`0` if there is none). -/
noncomputable def vbT (S : InaccSeq.{0}) (l x : Ordinal.{0}) : Ordinal.{0} :=
  if h : ∃ y, RxE S (vbW S l) y ∧ vbK S l y = x then Classical.choose h else 0

theorem vbT_spec {l x : Ordinal.{0}} (h : ∃ y, RxE S (vbW S l) y ∧ vbK S l y = x) :
    RxE S (vbW S l) (vbT S l x) ∧ vbK S l (vbT S l x) = x := by
  have e : vbT S l x = Classical.choose h := by unfold vbT; rw [dif_pos h]
  rw [e]; exact Classical.choose_spec h

/-- The remainder of the Cantor normal form of a member of `Cl(a, b)` is a member. -/
theorem vbC_rem {a b x : Ordinal.{0}} (hx : x ∈ S.CSet a b) : x % ω ^ log ω x ∈ S.CSet a b := by
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
  have hdm : x = ω ^ log ω x * n + x % ω ^ log ω x := by
    rw [← hn]; exact (Ordinal.div_add_mod x _).symm
  have e : x - ω ^ log ω x * n = x % ω ^ log ω x := by
    have e0 := Ordinal.add_sub_cancel (ω ^ log ω x * n) (x % ω ^ log ω x)
    rwa [← hdm] at e0
  have hle : ω ^ log ω x * n ≤ x := le_self_add.trans_eq hdm.symm
  have hop : ω ^ log ω x ∈ S.CSet a b := by
    have := CSet.phi_mem (S := S) (CSet.zero_mem _ _) (rxCDec x hx).2; rwa [veblen_zero_apply] at this
  have h := (rxCDec x hx).1 _ (ConjT.mul_nat_mem S hop n) hle
  rwa [e] at h

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

theorem vbZ : SC (upsilon l) ∧ upsilon l < Om 1 := Le.leRho hl hX

theorem vbW_SC : SC (vbW S l) := rxW_SC (vbZ hl hX).1 (vbZ hl hX).2 (ldAt_GxAt _ _)

theorem vbK_mono {y' y : Ordinal.{0}} (hy' : RxE S (vbW S l) y') (hy : RxE S (vbW S l) y) (h : y' < y) :
    vbK S l y' < vbK S l y :=
  rxL_mono (vbZ hl hX).1 (vbZ hl hX).2 (ldAt_GxAt _ _) hy' hy h

theorem vbK_inj {y' y : Ordinal.{0}} (hy' : RxE S (vbW S l) y') (hy : RxE S (vbW S l) y)
    (e : vbK S l y' = vbK S l y) : y' = y := by
  rcases lt_trichotomy y' y with h | h | h
  · exact absurd e (vbK_mono hl hX hy' hy h).ne
  · exact h
  · exact absurd e.symm (vbK_mono hl hX hy hy' h).ne

theorem vbK_le_iff {y' y : Ordinal.{0}} (hy' : RxE S (vbW S l) y') (hy : RxE S (vbW S l) y) :
    y' ≤ y ↔ vbK S l y' ≤ vbK S l y := by
  constructor
  · intro h
    rcases h.lt_or_eq with h | h
    · exact (vbK_mono hl hX hy' hy h).le
    · rw [h]
  · intro h
    by_contra hc
    exact absurd h (not_le.2 (vbK_mono hl hX hy hy' (not_le.1 hc)))

theorem vbK_lt_iff {y' y : Ordinal.{0}} (hy' : RxE S (vbW S l) y') (hy : RxE S (vbW S l) y) :
    y' < y ↔ vbK S l y' < vbK S l y := by
  rw [← not_le, ← not_le, vbK_le_iff hl hX hy hy']

/-- **`T(κ_λ y) = y`.** -/
theorem vbT_K {y : Ordinal.{0}} (hy : RxE S (vbW S l) y) : vbT S l (vbK S l y) = y := by
  obtain ⟨h1, h2⟩ := vbT_spec (S := S) (l := l) ⟨y, hy, rfl⟩
  exact vbK_inj hl hX h1 hy h2

/-- **`T` is strictly increasing on the values of `κ_λ`.** -/
theorem vbT_lt {x' x : Ordinal.{0}} (hx' : ∃ y, RxE S (vbW S l) y ∧ vbK S l y = x')
    (hx : ∃ y, RxE S (vbW S l) y ∧ vbK S l y = x) (h : x' < x) : vbT S l x' < vbT S l x := by
  obtain ⟨h1, e1⟩ := vbT_spec hx'
  obtain ⟨h2, e2⟩ := vbT_spec hx
  rw [vbK_lt_iff hl hX h1 h2, e1, e2]; exact h

/-- **The readings of the codes are countable**: `Θ(Ω₂) ≤ Ω₁` (`H_λ` is countable). -/
theorem vbZ2_le : gxTh (upsilon l) (ldAtR S l) (Om (1 + 1)) ≤ Om 1 := by
  by_contra hc
  push Not at hc
  have hmem : ∀ g : Iio (Om 1 : Ordinal.{0}), ruInv (upsilon l) (ldAtR S l) g.1 ∈ cdHull S l := fun g => by
    obtain ⟨hcode, hlt2, -⟩ := ruInv_spec (g.2.trans hc)
    exact (ldHull_iff hl hX hlt2).2 hcode
  have hinj : Function.Injective (fun g : Iio (Om 1 : Ordinal.{0}) =>
      (⟨ruInv (upsilon l) (ldAtR S l) g.1, hmem g⟩ : cdHull S l)) := by
    intro g g' e
    have e' : ruInv (upsilon l) (ldAtR S l) g.1 = ruInv (upsilon l) (ldAtR S l) g'.1 := congrArg Subtype.val e
    have h1 := (ruInv_spec (g.2.trans hc)).2.2
    have h2 := (ruInv_spec (g'.2.trans hc)).2.2
    exact Subtype.ext (by rw [← h1, ← h2, e'])
  have hle := Cardinal.mk_le_of_injective hinj
  rw [Cardinal.mk_Iio_ordinal, card_Om one_ne_zero] at hle
  have hcρ : (upsilon l).card ≤ ℵ₀ := by
    have h := (vbZ hl hX).2
    rw [Om_eq_ord one_ne_zero, Cardinal.lt_ord] at h
    exact Cardinal.lt_aleph_one_iff.1 h
  have hH : #(cdHull S l) ≤ ℵ₀ := by
    refine (mk_CSet_le (S := S) _ _).trans (max_le ?_ le_rfl)
    calc Cardinal.lift.{1} (upsilon l).card ≤ Cardinal.lift.{1} (ℵ₀ : Cardinal.{0}) := Cardinal.lift_le.2 hcρ
      _ = ℵ₀ := Cardinal.lift_aleph0
  exact absurd (Cardinal.lift_le_aleph0.1 (hle.trans hH)) (not_le.2 aleph0_lt_aleph_one)

theorem vbW_eq : vbW S l = gxTh (upsilon l) (ldAtR S l) (Om (1 + 1)) := min_eq_left (vbZ2_le hl hX)

/-- **A code `x < Ω₂` of `H_λ` is `κ_λ(Θ x)`.** -/
theorem vbCode_K {x : Ordinal.{0}} (hx2 : x < Om (1 + 1)) (hxH : x ∈ cdHull S l) :
    RxE S (vbW S l) (gxTh (upsilon l) (ldAtR S l) x) ∧ vbK S l (gxTh (upsilon l) (ldAtR S l) x) = x := by
  have hc : GxCl (upsilon l) (ldAtR S l) x := (ldHull_iff hl hX hx2).1 hxH
  have hlt : gxTh (upsilon l) (ldAtR S l) x < gxTh (upsilon l) (ldAtR S l) (Om (1 + 1)) := gxTh_lt hc hx2
  have hW : gxTh (upsilon l) (ldAtR S l) x < vbW S l := by rw [vbW_eq hl hX]; exact hlt
  have hx1 : gxTh (upsilon l) (ldAtR S l) x < Om 1 := hW.trans_le (min_le_right _ _)
  have h1θ : Om 1 < ConjT.th S := (psiS_bounds (S := S) (Om ω) 1).1
  have h1W : Om 1 < Om ω := Om_lt_Om.2 one_lt_omega0
  refine ⟨⟨RxN.small hW, CSet.of_lt (hx1.trans h1θ), hx1.trans h1W⟩, ?_⟩
  show rxL S (upsilon l) (ldAtR S l) (vbW S l) _ = x
  rw [rxL_lt_Om1 hx1]
  obtain ⟨h1, -, h3⟩ := ruInv_spec hlt
  exact ruCode_inj h1 hc h3

/-- **`H_λ` lies in the normal hull over `ρ_λ`.** -/
theorem vbHullN {x : Ordinal.{0}} (hx : x ∈ cdHull S l) : RxN S (upsilon l) x := by
  have hρ1 := (vbZ hl hX).2
  have hpv : S.psi (ConjT.Aη S (cdEta S l)) (Om 1) = upsilon l := cdEta_pv hl.1 hX
  change x ∈ S.CSet (ConjT.Aη S (cdEta S l)) (upsilon l) at hx
  induction hx with
  | small h => exact RxN.small h
  | zero => exact RxN.zero
  | inacc n => exact RxN.inacc n
  | inaccW => exact RxN.inaccW
  | add _ _ ihx ihy => exact RxN.add ihx ihy
  | phi _ _ ihx ihy => exact RxN.phi ihx ihy
  | om _ ih => exact RxN.om ih
  | @coll π e hπ hπC heC ihπ ihe =>
    show RxN S (upsilon l) (S.psi e.1 π)
    by_cases h1 : π = Om 1
    · subst h1
      apply RxN.small
      have hmem : S.psi e.1 (Om 1) ∈ S.CSet (ConjT.Aη S (cdEta S l)) (upsilon l) :=
        CSet.psi_mem e.2 hπ hπC heC
      rw [← hpv] at hmem ⊢
      exact lt_psi_of_mem Low.InR_Om_one hmem (psi_lt hπ _)
    · exact rxN_psi hρ1.le e.1 ihe π hπ h1 ihπ

theorem vbD_E {x : Ordinal.{0}} (hx : VbD S l x) : RxE S (upsilon l) x :=
  ⟨vbHullN hl hX hx.1, hx.2.1, hx.2.2⟩

omit hl hX in
theorem vbD_log {x : Ordinal.{0}} (hx : VbD S l x) (hxE : RxE S (upsilon l) x) :
    VbD S l (log ω x) ∧ RxE S (upsilon l) (log ω x) ∧ rxH S (upsilon l) (log ω x) ≤ rxH S (upsilon l) x := by
  obtain ⟨hE, hh⟩ := rxE_log hxE
  exact ⟨⟨(rxCDec x hx.1).2, hE.2.1, hE.2.2⟩, hE, hh⟩

omit hl hX in
theorem vbD_rem {x : Ordinal.{0}} (hx : VbD S l x) (hxE : RxE S (upsilon l) x) :
    VbD S l (x % ω ^ log ω x) ∧ RxE S (upsilon l) (x % ω ^ log ω x) ∧
      rxH S (upsilon l) (x % ω ^ log ω x) ≤ rxH S (upsilon l) x := by
  obtain ⟨hE, hh⟩ := rxE_rem hxE
  exact ⟨⟨vbC_rem hx.1, hE.2.1, hE.2.2⟩, hE, hh⟩

omit hl hX in
theorem vbD_veb {x a b : Ordinal.{0}} (hx : VbD S l x) (hxE : RxE S (upsilon l) x) (e : veblen a b = x)
    (hb : b < x) :
    VbD S l a ∧ VbD S l b ∧ RxE S (upsilon l) a ∧ RxE S (upsilon l) b ∧
      rxH S (upsilon l) a ≤ rxH S (upsilon l) x ∧ rxH S (upsilon l) b ≤ rxH S (upsilon l) x := by
  obtain ⟨haE, hbE, hha, hhb⟩ := rxE_veb hxE e hb
  obtain ⟨haC, hbC⟩ := rxCDecV hx.1 a b e hb
  exact ⟨⟨haC, haE.2.1, haE.2.2⟩, ⟨hbC, hbE.2.1, hbE.2.2⟩, haE, hbE, hha, hhb⟩

/-- The normal argument of an atom of the domain is in the domain. -/
theorem vbD_atom {d : Ordinal.{0}} {k : ℕ} (hx : VbD S l (S.psi d (Om ((k : Ordinal.{0}) + 1))))
    (hdE : RxE S (upsilon l) d) (hdn : d ∈ S.CSet d (S.psi d (Om ((k : Ordinal.{0}) + 1))))
    (hk : 1 ≤ k) : VbD S l d := by
  have hρ1 := (vbZ hl hX).2
  have hρx : upsilon l ≤ S.psi d (Om ((k : Ordinal.{0}) + 1)) :=
    (hρ1.trans_le ((rxOm1_le_nat hk).trans (psiS_bounds (S := S) d (k : Ordinal.{0})).1.le)).le
  have hρL : upsilon l ≤ S.Lam :=
    (hρ1.trans (lt_Lam_of_mem zero_le (CSet.Om_mem (CSet.one_mem (S := S) 0 0)))).le
  exact ⟨(arg_mem_of_psi_mem (InR_Om_succ _) hx.1 hρx hρL hdn).1, hdE.2.1, hdE.2.2⟩

end Rst

end Googology.Trans.PoR.InaccPsi.R2.Vb
