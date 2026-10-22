import Googology.Trans.PoR.InaccPsi.R2.RpAt

/-!
# The lift lemma: lower readings of the atoms `ψ_{Ω₂}(β + κ(ζ))` from a lift `κ`

`HCl S a Z` is `Cl(a, Z)` without the countable collapses (`Bt.HCl`), `Θ = gxTh Z At` the reading of the codes
over `Z` with the atoms `At`, `ggGam` the least strongly critical ordinal above `Ω₁`.

* `ruHCl_modK` (**`HCl S a Z` is closed under `x ↦ x % κ`** for a strongly critical `κ`);
* `ruHCl_gg` (**a member of `HCl S a Z` below `ggGam` is a code over `Z`**: the collapses `ψ_π(e)`, `π ≠ Ω₁`, the
  `I_n`, `I_ω` and the `Ω_x`, `x ≥ 2`, are strongly critical above `Ω₁`);
* `ruTail` (**the tail of a member of the hull**: if `ggGam ∣ Â`, `Â ≤ e < Â + y`, `y ≤ ggGam` and `e` is a member
  of `HCl S a Z`, then `e − Â` is a code over `Z`);
* `ruLift` (**THE LIFT LEMMA**): let `ψ_{Ω₂}(β)` be an atom with `ψ_{Ω₁}(Â) ≤ Θ(ψ_{Ω₂}(β))`, `D` a set of offsets and
  `κ : D → codes` strictly increasing, such that every `ψ_{Ω₂}(β + κ ζ)` (`ζ ∈ D`) is an atom above `ψ_{Ω₂}(β)` (for
  `ζ ≠ 0`), and for every `ζ ∈ D` and every `e ∈ HCl S (Â + ζ) T_ζ` (`T_ζ = Θ(ψ_{Ω₂}(β + κ ζ))`) with
  `Â ≤ e < Â + ζ` the offset `e − Â` lies in `D` with `β + κ(e − Â) ∈ Cl(β + κ ζ, ψ_{Ω₂}(β + κ ζ))`.  Then
  `ψ_{Ω₁}(Â + ζ) ≤ Θ(ψ_{Ω₂}(β + κ ζ))` for every `ζ ∈ D`.  (`Bt.psi_le_of_key` with `Z = T_ζ`; a collapse below
  `Â` is below the base, one above is `Â + ζ'` with `ζ' ∈ D`, `ζ' < ζ`, read below `T_ζ` by induction.)

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ru

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ld

variable {S : InaccSeq.{0}}

/-- **`HCl S a Z` is closed under `x ↦ x % κ`** for a strongly critical `κ`. -/
theorem ruHCl_modK {κ a Z x : Ordinal.{0}} (hκ : SC κ) (hx : HCl S a Z x) : HCl S a Z (x % κ) := by
  have prin : ∀ {p : Ordinal.{0}}, IsPrincipal (· + ·) p → HCl S a Z p → HCl S a Z (p % κ) := by
    intro p hp hpC
    rcases ldModK_prin hκ hp with ⟨-, e⟩ | e
    · rw [e]; exact hpC
    · rw [e]; exact HCl.zero
  induction hx with
  | small h => exact HCl.small ((Ordinal.mod_le _ _).trans_lt h)
  | zero => rw [Ordinal.zero_mod]; exact HCl.zero
  | inacc n => exact prin (SC_I (S := S) n).isPrincipal (HCl.inacc n)
  | inaccW => exact prin (SC_Iw (S := S)).isPrincipal HCl.inaccW
  | @add x y _ hy ihx ihy =>
    rcases lt_or_ge y κ with h | h
    · rw [ldModK_add_lt hκ x h]; exact HCl.add ihx hy
    · rw [ldModK_add_ge hκ x h]; exact ihy
  | @phi x y hx hy _ _ => exact prin (Ph.ph_veblen_prin x y) (HCl.phi hx hy)
  | @om x hx _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero, Ordinal.zero_mod]; exact HCl.zero
    · exact prin (Om_isPrincipal hx0) (HCl.om hx)
  | @coll π e hπ hπ1 hπC heC hea _ _ =>
    exact prin (SC_psi hπ e).isPrincipal (HCl.coll hπ hπ1 hπC heC hea)

/-- **A member of `HCl S a Z` below `ggGam` is a code over `Z`.** -/
theorem ruHCl_gg {a Z x : Ordinal.{0}} (hZ : 0 < Z) (hx : HCl S a Z x) : x < ggGam → GgCl Z x := by
  induction hx with
  | small h => exact fun _ => GgCl.small h
  | zero => exact fun _ => GgCl.zero hZ
  | inacc n =>
    exact fun h => absurd (ggGam_le (SC_I (S := S) n) (gg_Om1_lt_I S n)) (not_le.2 h)
  | inaccW =>
    exact fun h => absurd (ggGam_le (SC_Iw (S := S)) (gg_Om1_lt_Iw S)) (not_le.2 h)
  | @add x y _ _ ihx ihy =>
    intro h
    exact GgCl.add (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y _ _ ihx ihy =>
    intro h
    exact GgCl.phi (ihx (lt_of_le_of_lt (left_le_veblen x y) h))
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h))
  | @om x _ _ =>
    intro h
    have h2 : x < 1 + 1 := Om_lt_Om.1 (h.trans_le ggGam_le_Om2)
    rcases (Order.lt_add_one_iff.1 h2).lt_or_eq with h0 | h1
    · rw [Order.lt_one_iff] at h0; rw [h0, Om_zero]; exact GgCl.zero hZ
    · rw [h1]; exact GgCl.om
  | @coll π e hπ hπ1 hπC heC hea _ _ =>
    intro h
    have hge : Om 1 ≤ S.psi e π := not_lt.1 fun h' => hπ1 (Low.eq_Om_one_of_psi_lt hπ h')
    have hne : Om 1 ≠ S.psi e π := fun h' =>
      psi_notMem hπ e (h' ▸ CSet.Om_mem (CSet.one_mem _ _))
    exact absurd (ggGam_le (SC_psi hπ _) (lt_of_le_of_ne hge hne)) (not_le.2 h)

/-- **The tail of a member of the hull**: for `ggGam ∣ Â` and `Â ≤ e < Â + y ≤ Â + ggGam`, `e − Â` is a code over
`Z`. -/
theorem ruTail {a Z Â y e : Ordinal.{0}} (hZ : 0 < Z) (hdvd : ggGam ∣ Â) (hy : y ≤ ggGam)
    (he : HCl S a Z e) (h1 : Â ≤ e) (h2 : e < Â + y) : GgCl Z (e - Â) ∧ e - Â < y := by
  have hG := ggGam_spec.1
  have e1 : e = Â + (e - Â) := (Ordinal.add_sub_cancel_of_le h1).symm
  have hlt : e - Â < y := by
    rw [e1] at h2; exact (add_lt_add_iff_left _).1 h2
  have hm : e % ggGam = e - Â := by
    conv_lhs => rw [e1]
    rw [ldModK_add_lt hG Â (hlt.trans_le hy), Ordinal.mod_eq_zero_of_dvd hdvd, zero_add]
  refine ⟨?_, hlt⟩
  rw [← hm]
  exact ruHCl_gg hZ (ruHCl_modK hG he) (Ordinal.mod_lt e hG.1.ne')

section Lift

variable {Z β Â : Ordinal.{0}} {At : Set Ordinal.{0}} {D : Set Ordinal.{0}} {κ : Ordinal.{0} → Ordinal.{0}}

/-- **THE LIFT LEMMA**: `ψ_{Ω₁}(Â + ζ) ≤ Θ(ψ_{Ω₂}(β + κ ζ))` for every `ζ ∈ D`. -/
theorem ruLift (hZ : SC Z) (hZ1 : Z < Om 1) (hAt : GxAt At)
    (hβ : S.psi β (Om (1 + 1)) ∈ At)
    (hbase : S.psi Â (Om 1) ≤ gxTh Z At (S.psi β (Om (1 + 1))))
    (hmono : ∀ ζ ∈ D, ∀ ζ' ∈ D, ζ' < ζ → κ ζ' < κ ζ)
    (hat : ∀ ζ ∈ D, S.psi (β + κ ζ) (Om (1 + 1)) ∈ At)
    (hpos : ∀ ζ ∈ D, ζ ≠ 0 → S.psi β (Om (1 + 1)) < S.psi (β + κ ζ) (Om (1 + 1)))
    (hcl : ∀ ζ ∈ D, ∀ e, HCl S (Â + ζ) (gxTh Z At (S.psi (β + κ ζ) (Om (1 + 1)))) e → Â ≤ e →
      e < Â + ζ → e - Â ∈ D ∧
        β + κ (e - Â) ∈ S.CSet (β + κ ζ) (S.psi (β + κ ζ) (Om (1 + 1)))) :
    ∀ ζ ∈ D, S.psi (Â + ζ) (Om 1) ≤ gxTh Z At (S.psi (β + κ ζ) (Om (1 + 1))) := by
  intro ζ
  induction ζ using WellFoundedLT.induction with
  | ind ζ IH =>
  intro hζ
  have hT : SC (gxTh Z At (S.psi (β + κ ζ) (Om (1 + 1)))) :=
    gxTh_SC hZ hAt (SC_psi (InR_Om_succ 1) _) (hZ1.trans (psiS_bounds (S := S) _ 1).1)
  rcases eq_or_ne ζ 0 with rfl | hζ0
  · rw [add_zero]
    exact hbase.trans (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) le_self_add).1)
  refine psi_le_of_key hT fun e he heA => ?_
  have hβlt : gxTh Z At (S.psi β (Om (1 + 1))) < gxTh Z At (S.psi (β + κ ζ) (Om (1 + 1))) :=
    gxTh_lt (GxCl.atom hβ) (hpos ζ hζ hζ0)
  rcases lt_or_ge e Â with h1 | h1
  · exact ((psi_mono (S := S) Low.InR_Om_one h1.le).1.trans hbase).trans_lt hβlt
  · obtain ⟨hD, hmem⟩ := hcl ζ hζ e he h1 heA
    have e1 : e = Â + (e - Â) := (Ordinal.add_sub_cancel_of_le h1).symm
    have hlt : e - Â < ζ := by
      have h2 := heA; rw [e1] at h2; exact (add_lt_add_iff_left _).1 h2
    have hκ := hmono ζ hζ _ hD hlt
    have hs : S.psi (β + κ (e - Â)) (Om (1 + 1)) < S.psi (β + κ ζ) (Om (1 + 1)) :=
      psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left β).2 hκ) hmem
    rw [e1]
    exact (IH _ hlt hD).trans_lt (gxTh_lt (GxCl.atom (hat _ hD)) hs)

end Lift

end Googology.Trans.PoR.InaccPsi.R2.Ru
