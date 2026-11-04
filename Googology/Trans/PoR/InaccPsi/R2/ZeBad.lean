import Googology.Trans.PoR.InaccPsi.R2.CdLow
import Googology.Trans.PoR.InaccPsi.R2.NmD

/-!
# A bad interval `[β, β + ω^E)` makes `β + ω^E` bad

`A_η = Ω_ω + θ·η`, `P(η) = ψ_{Ω₁}(A_η)`, `η` *good*: `η ∈ Cl(A_η + 1, P(η))` (`Bt.Good`), `HCl S a Z` the hull
`Cl(a, Z)` without the collapses `ψ_{Ω₁}(e)` (`Bt.HCl`).

* `zeHCl_lead_tail`: `HCl` is closed under the leading summand and the rest (the `HCl` twin of
  `InaccSeq.lead_tail_mem`);
* `zeHCl_peel`: `β + ω^E ∈ HCl`, `ω^E ∣ β` give `β ∈ HCl` (the prefix of the Cantor normal form);
* `zeBad_top` (**the main lemma**): if `β ≠ 0`, `ω^E ∣ β` and every `ζ ∈ [β, β + ω^E)` is bad, then `β + ω^E` is bad.
  Proof: `ι` and `P` are constant on `[β, β + ω^E]` (`Z = P(β)`); no `ζ ∈ [β, β + ω^E]` lies in `HCl(A_β, Z)`
  (for `ζ < β + ω^E` it would be good; for `ζ = β + ω^E` its prefix `β` would be, `zeHCl_peel`); hence every
  member of `HCl(A_{β+ω^E} + θ, Z)` lies in `HCl(A_β, Z)` (the `θ`-quotient of a collapse argument would be such
  a `ζ`, `Bt.quotA`; the twin of `Bt.HCl_shrink`), every collapse argument there gives a value below `Z`, so
  `P(β + ω^E + 1) ≤ Z = P(β + ω^E)` (`Bt.psi_le_of_key`) and `β + ω^E` is bad (`Nm.bad_of_eq`);
* `zeIota_prefix_lt` (**the good name of a restart is never at the end of a bad interval**): for every good
  `η = β + ω^E` with `ω^E ∣ β`, `ι(β) < ι(η)` (for `β = 0` from `ι(0) = 1`; otherwise a bad interval
  `[β, η)` would make `η` bad).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ze

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

/-- `HCl` is closed under the leading summand and the rest. -/
theorem zeHCl_lead_tail {a Z x : Ordinal.{0}} (hx : HCl S a Z x) (h0 : x ≠ 0) :
    HCl S a Z (lead x) ∧ HCl S a Z (tail x) := by
  have prin : ∀ {y}, HCl S a Z y → IsPrincipal (· + ·) y → y ≠ 0 →
      HCl S a Z (lead y) ∧ HCl S a Z (tail y) := fun hy hP h0 => by
    obtain ⟨h1, h2⟩ := lead_tail_of_principal hP h0
    rw [h1, h2]; exact ⟨hy, HCl.zero⟩
  revert h0
  induction hx with
  | @small y h =>
    intro h0
    exact ⟨HCl.small (lt_of_le_of_lt (lead_le h0) h), HCl.small (lt_of_le_of_lt (tail_le y) h)⟩
  | zero => intro h0; exact absurd rfl h0
  | inacc n => intro h0; exact prin (HCl.inacc n) (SC_I n).isPrincipal h0
  | inaccW => intro h0; exact prin HCl.inaccW SC_Iw.isPrincipal h0
  | @add p q hp hq ihp ihq =>
    intro h0
    by_cases hq0 : q = 0
    · subst hq0; simp only [add_zero] at h0 ⊢; exact ihp h0
    by_cases hp0 : p = 0
    · subst hp0; simp only [zero_add] at h0 ⊢; exact ihq h0
    rcases lead_tail_add hp0 hq0 with habs | ⟨hl, ht⟩
    · rw [habs]; exact ihq hq0
    · rw [hl, ht]; exact ⟨(ihp hp0).1, HCl.add (ihp hp0).2 hq⟩
  | @phi p q hp hq _ _ =>
    intro h0; exact prin (HCl.phi hp hq) (veblen_isPrincipal p q) h0
  | @om p hp _ =>
    intro h0
    have hp0 : p ≠ 0 := by rintro rfl; exact h0 Om_zero
    exact prin (HCl.om hp) (SC_Om hp0).isPrincipal h0
  | @coll π e hπ hπ1 hπC heC he _ _ =>
    intro h0; exact prin (HCl.coll hπ hπ1 hπC heC he) (SC_psi hπ e).isPrincipal h0

/-- **The prefix of the Cantor normal form**: `β + ω^E ∈ HCl`, `ω^E ∣ β` give `β ∈ HCl`. -/
theorem zeHCl_peel {a Z : Ordinal.{0}} (x : Ordinal.{0}) : HCl S a Z x → ∀ y E : Ordinal.{0},
    ω ^ E ∣ y → x = y + ω ^ E → HCl S a Z y := by
  induction x using WellFoundedLT.induction with
  | _ x ih =>
  intro hx y E hy e
  rcases eq_or_ne y 0 with rfl | hy0
  · exact HCl.zero
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hy0 (le_antisymm (e ▸ le_self_add) zero_le)
  obtain ⟨hl, ht⟩ := zeHCl_lead_tail hx hx0
  have hEy : E ≤ Ordinal.log ω y :=
    (opow_le_iff_le_log one_lt_omega0 hy0).1 (Ordinal.le_of_dvd hy0 hy)
  have hlog : Ordinal.log ω x = Ordinal.log ω y := by
    rw [e]
    refine log_add_of_le hy0 ?_
    rw [Ordinal.log_opow one_lt_omega0]
    exact hEy
  have hlead : lead x = lead y := by unfold lead; rw [hlog]
  have htail : tail x = tail y + ω ^ E := by
    have h1 := lead_add_tail hx0
    have h2 := lead_add_tail hy0
    rw [hlead] at h1
    have : lead y + tail x = lead y + (tail y + ω ^ E) := by
      rw [h1, ← add_assoc, h2, e]
    exact add_left_cancel this
  have hdl : ω ^ E ∣ lead y := opow_dvd_opow ω hEy
  have hdt : ω ^ E ∣ tail y := by
    have h2 := lead_add_tail hy0
    rw [← h2] at hy
    exact (dvd_add_iff hdl).1 hy
  have hty : HCl S a Z (tail y) := ih (tail x) (tail_lt hx0) ht (tail y) E hdt htail
  rw [← lead_add_tail hy0]
  exact HCl.add (hlead ▸ hl) hty

/-- **A bad interval `[β, β + ω^E)` makes `β + ω^E` bad.** -/
theorem zeBad_top {β E : Ordinal.{0}} (hβ0 : β ≠ 0) (hd : ω ^ E ∣ β)
    (hbad : ∀ ζ, β ≤ ζ → ζ < β + ω ^ E → ¬ Bt.Good S ζ) : ¬ Bt.Good S (β + ω ^ E) := by
  set η := β + ω ^ E with hη
  -- `ι` is constant on `[β, η]`
  have hι : ∀ ζ, β ≤ ζ → ζ ≤ η → iota S ζ = iota S β := by
    intro ζ
    induction ζ using WellFoundedLT.induction with
    | _ ζ IH =>
    intro hβζ hζη
    rcases eq_or_lt_of_le hβζ with h | hlt
    · rw [h]
    rcases zero_or_succ_or_isSuccLimit ζ with h0 | ⟨ζ', hζ'⟩ | hlim
    · exact absurd (h0 ▸ hlt) (not_lt.2 zero_le)
    · rw [succ_eq_add_one] at hζ'
      subst hζ'
      have h1 : β ≤ ζ' := Order.lt_add_one_iff.1 hlt
      have h2 : ζ' < η := lt_of_lt_of_le (lt_add_one ζ') hζη
      rw [iota_bad (hbad ζ' h1 h2)]
      exact IH ζ' (lt_add_one ζ') h1 h2.le
    · rw [iota_limit hlim]
      refine le_antisymm (ciSup_le' fun e => ?_) ?_
      · rcases lt_or_ge e.1 β with h | h
        · exact iota_mono β e.1 h.le
        · exact (IH e.1 e.2 h (e.2.le.trans hζη)).le
      · rw [← iota_limit hlim]; exact iota_mono ζ β hβζ
  have hP : ∀ ζ, β ≤ ζ → ζ ≤ η → Pv S ζ = Pv S β := by
    intro ζ h1 h2
    calc Pv S ζ = upsilon (iota S ζ) := (ups_iota S ζ).symm
      _ = upsilon (iota S β) := by rw [hι ζ h1 h2]
      _ = Pv S β := ups_iota S β
  set Z := Pv S β with hZdef
  have hZ : SC Z := SC_psi Low.InR_Om_one _
  have hZ1 : Z < Om 1 := psi_lt Low.InR_Om_one _
  have hβη : β ≤ η := le_self_add
  -- no point of `[β, η]` lies in `HCl(A_β, Z)`
  have hno : ∀ ζ, β ≤ ζ → ζ ≤ η → HCl S (ConjT.Aη S β) Z ζ → False := by
    intro ζ h1 h2 hH
    have hgood : ∀ ξ, β ≤ ξ → ξ ≤ η → HCl S (ConjT.Aη S β) Z ξ → Bt.Good S ξ := by
      intro ξ k1 k2 hξ
      have hle : ConjT.Aη S β ≤ ConjT.Aη S ξ + 1 := (ConjT.A_mono S k1).trans le_self_add
      have hm : ξ ∈ S.CSet (ConjT.Aη S ξ + 1) Z := (hξ.mono hle).mem_CSet
      show ξ ∈ S.CSet (ConjT.Aη S ξ + 1) (Pv S ξ)
      rw [hP ξ k1 k2]; exact hm
    rcases eq_or_lt_of_le h2 with he | hlt
    · have hβH : HCl S (ConjT.Aη S β) Z β := zeHCl_peel ζ hH β E hd (he.trans hη)
      exact hbad β le_rfl (lt_add_of_pos_right _ (opow_pos E omega0_pos)) (hgood β le_rfl hβη hβH)
    · exact hbad ζ h1 hlt (hgood ζ h1 h2 hH)
  -- the shrink
  have hθβ : ConjT.th S ∈ S.CSet (ConjT.Aη S β) Z := by
    refine ConjT.th_mem S ?_
    unfold ConjT.Aη
    exact lt_add_of_pos_right _ (mul_pos (ConjT.SC_th S).1 (pos_iff_ne_zero.2 hβ0))
  have hshr : ∀ {x}, HCl S (ConjT.Aη S η + ConjT.th S) Z x → HCl S (ConjT.Aη S β) Z x := by
    intro x h
    induction h with
    | small h => exact HCl.small h
    | zero => exact HCl.zero
    | inacc n => exact HCl.inacc n
    | inaccW => exact HCl.inaccW
    | add _ _ ihx ihy => exact HCl.add ihx ihy
    | phi _ _ ihx ihy => exact HCl.phi ihx ihy
    | om _ ih => exact HCl.om ih
    | @coll π e hπ hπ1 _ _ he ihπ ihe =>
      refine HCl.coll hπ hπ1 ihπ ihe ?_
      by_contra hge
      rw [not_lt] at hge
      have h1 : Om (ω : Ordinal.{0}) ≤ e := (ConjT.OmW_le_A S β).trans hge
      obtain ⟨ζ, hζ, k1, k2⟩ := quotA hZ1 ihe h1
      rw [ConjT.A_succ] at k2
      have hβζ : β ≤ ζ := Order.lt_add_one_iff.1 (A_lt_A_iff.1 (lt_of_le_of_lt hge k2))
      rw [ConjT.A_succ] at he
      have hζη : ζ ≤ η := Order.lt_add_one_iff.1 (A_lt_A_iff.1 (lt_of_le_of_lt k1 he))
      exact hno ζ hβζ hζη hζ
  -- the key
  have hA0 : ConjT.Aη S 0 < ConjT.Aη S β := A_lt_A_iff.2 (pos_iff_ne_zero.2 hβ0)
  have hkey : ∀ e, HCl S (ConjT.Aη S η + ConjT.th S) Z e → e < ConjT.Aη S η + ConjT.th S →
      S.psi e (Om 1) < Z := by
    intro e he hea
    have he' := hshr he
    rcases lt_or_ge e (Om (ω : Ordinal.{0})) with h1 | h1
    · have hmem : ConjT.Aη S 0 ∈ S.CSet (ConjT.Aη S β) Z := by
        rw [A_zero]; exact ConjT.OmW_mem S _ _
      have := psi_lt_psi_of_mem Low.InR_Om_one hA0 hmem
      rw [A_zero] at this
      exact lt_of_le_of_lt (psi_mono Low.InR_Om_one h1.le).1 this
    · obtain ⟨ζ, hζ, k1, k2⟩ := quotA hZ1 he' h1
      rw [ConjT.A_succ] at hea k2
      have hζη : ζ ≤ η := Order.lt_add_one_iff.1 (A_lt_A_iff.1 (lt_of_le_of_lt k1 hea))
      rcases le_or_gt β ζ with hβζ | hζβ
      · exact (hno ζ hβζ hζη hζ).elim
      rcases eq_or_lt_of_le (Order.add_one_le_of_lt hζβ) with he1 | hlt1
      · exact (hno β le_rfl hβη (he1 ▸ hζ.succ)).elim
      · have hmem : ConjT.Aη S (ζ + 1) ∈ S.CSet (ConjT.Aη S β) Z :=
          CSet.add_mem (ConjT.OmW_mem S _ _) (C_mul_th hθβ _ hζ.succ.mem_CSet)
        have := psi_lt_psi_of_mem Low.InR_Om_one (A_lt_A_iff.2 hlt1) hmem
        exact lt_of_le_of_lt (psi_mono Low.InR_Om_one k2.le).1 this
  have hle : S.psi (ConjT.Aη S η + ConjT.th S) (Om 1) ≤ Z := psi_le_of_key hZ hkey
  rw [ConjT.A_succ] at hle
  refine bad_of_eq (le_antisymm (Pv_mono le_self_add) ?_)
  calc Pv S (η + 1) ≤ Z := hle
    _ = Pv S η := (hP η hβη le_rfl).symm

/-- **The good name is never at the end of a bad interval**: a good `η = β + ω^E` with `ω^E ∣ β` has
`ι(β) < ι(η)`. -/
theorem zeIota_prefix_lt {β E : Ordinal.{0}} (hd : ω ^ E ∣ β) (hg : Bt.Good S (β + ω ^ E)) :
    iota S β < iota S (β + ω ^ E) := by
  rcases eq_or_ne β 0 with rfl | hβ0
  · rw [zero_add, iota_zero]
    have h1 : iota S 1 = 2 := by
      rw [show (1 : Ordinal.{0}) = 0 + 1 from (zero_add 1).symm, iota_good (Nm.good_zero S), iota_zero,
        one_add_one_eq_two]
    calc (1 : Ordinal.{0}) < 2 := one_lt_two
      _ = iota S 1 := h1.symm
      _ ≤ iota S (ω ^ E) := iota_mono _ 1 (Order.one_le_iff_ne_zero.2 (opow_pos E omega0_pos).ne')
  · by_contra hge
    push Not at hge
    have heq : iota S (β + ω ^ E) = iota S β := le_antisymm hge (iota_mono _ β le_self_add)
    refine zeBad_top hβ0 hd (fun ζ h1 h2 hζ => ?_) hg
    have k1 : iota S β ≤ iota S ζ := iota_mono ζ β h1
    have k2 : iota S (ζ + 1) ≤ iota S (β + ω ^ E) := iota_mono _ _ (Order.add_one_le_of_lt h2)
    rw [iota_good hζ, heq] at k2
    exact absurd (k1.trans_lt (lt_add_one _)) (not_lt.2 k2)

end Googology.Trans.PoR.InaccPsi.R2.Ze
