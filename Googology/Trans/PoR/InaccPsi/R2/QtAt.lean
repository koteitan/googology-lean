import Googology.Trans.PoR.InaccPsi.R2.ZbAt
import Googology.Trans.PoR.InaccPsi.R2.VdCit

/-!
# QtAt: THE ATOM SYSTEM OF ALL CODES BELOW `θ = ψ_{Ω₂}(Ω_ω)` (ATOMS: THE STRONGLY CRITICAL MEMBERS OF `K⁽⁰⁾_Z`)

`θ = ConjT.th S`, `K⁽⁰⁾_Z = Ul.UlK S 0 Z` (the closure of `Z ∪ {0, I_n, I_ω}` under `+`, `φ`, `Ω_·` and every
`ψ_π`, `π ≠ Ω₁`, any argument), `Cl(a, Z) = S.CSet a Z`.  The atoms over `Z` are the strongly critical `Ω₁ < s < θ`
in `K⁽⁰⁾_Z`; they depend on `S`, and with the bound `θ` they form an atom system `qtU S : Zb.ZbAS` with its hull
facts at `S` (`Zb.ZbAS.Ok`):

* the hull lemma (`qt_hull`): for `Z ≤ Ω₁` with `Cl(a, Z) ∩ Ω₁ ⊆ Z`, every member of `Cl(a, Z)`
  below `θ` is a code over the atoms: `Cl(a, Z) ⊆ K⁽⁰⁾_Z` (`Ul.ulK_hull`), and a member is split by
  `lead_tail_mem` and `prin_mem_cases` (a collapse `ψ_{Ω₂}(e) < θ` is an atom, a countable one is below `Z`);
* hull membership (`qt_mem`): an atom over `Z` with every ordinal below `Z` of the notation is of the notation
  (`qt_K_Vals`), its datum is below every strongly critical `b ≥ Z` (`Vd.vd_dat_ui`, `Ul.ul_vis`), and its collapse
  arguments are below `Ω_ω` (`Ui.ui_args_th`), so it lies in `Cl(a, b)` for `a ≥ Ω_ω` (`Ui.ui_code_mem`).

* `qtAt`, `qt_N_iff`, `qt_K_Vals`, `qt_hull`, `qt_mem`, `qtU` (**THE ATOM SYSTEM BELOW `θ`**), `qtU_ok`, `qtU_V`,
  `qtU_At`.

No new axiom.  New definitions: `qtAt`, `qtU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Zb

variable (S : InaccSeq.{0})

/-- **The atoms over `Z`**: the strongly critical `Ω₁ < s < θ` in `K⁽⁰⁾_Z`. -/
def qtAt (Z : Ordinal.{0}) : Set Ordinal.{0} :=
  {s | SC s ∧ Om 1 < s ∧ s < ConjT.th S ∧ Ul.UlK S 0 Z s}

theorem qt_N_iff {x : Ordinal.{0}} : x ∈ Term.Vals S ↔ x ∈ ⋃ e, S.CSet e 0 := by
  rw [← Term.vals_eq S]; exact Iff.rfl

/-- **A member of `K⁽⁰⁾_Z` is of the notation when every ordinal below `Z` is.** -/
theorem qt_K_Vals {Z x : Ordinal.{0}} (hZN : ∀ z < Z, z ∈ Term.Vals S) (hx : Ul.UlK S 0 Z x) :
    x ∈ Term.Vals S := by
  induction hx with
  | small h => exact hZN _ h
  | zero => exact Term.zero_mem_Vals
  | inacc n => exact Term.I_mem_Vals n
  | inaccW => exact Term.Iw_mem_Vals
  | add _ _ ihx ihy => exact Term.add_mem_Vals ihx ihy
  | phi _ _ ihx ihy => exact Term.phi_mem_Vals ihx ihy
  | om _ ih => exact Term.Om_mem_Vals ih
  | coll hπ _ _ _ ihπ ihe =>
    rcases hπ with ⟨n, rfl⟩ | ⟨σ, rfl⟩
    · exact (Term.psi_mem_Vals S _ ihe).1 n
    · exact (Term.psi_mem_Vals S _ ihe).2 σ (Term.mem_Vals_of_Om_succ ihπ)

variable {S}

/-- **THE HULL LEMMA BELOW `θ`**: for `Z ≤ Ω₁` with `Cl(a, Z) ∩ Ω₁ ⊆ Z`, every member of `Cl(a, Z)` below `θ` is a
code over the atoms `qtAt Z`. -/
theorem qt_hull {a Z : Ordinal.{0}} (hZ1 : Z ≤ Om 1)
    (hkey : ∀ y ∈ S.CSet a Z, y < Om 1 → y < Z) :
    ∀ x, x ∈ S.CSet a Z → x < ConjT.th S → GxCl Z (qtAt S Z) x := by
  have hK : ∀ x, x ∈ S.CSet a Z → Ul.UlK S 0 Z x := Ul.ulK_hull (s := 0) fun e hea heC _ => by
    rw [zero_add]
    exact hkey _ (CSet.psi_mem hea Low.InR_Om_one (CSet.Om_mem (CSet.one_mem _ _)) heC) (psi_lt Low.InR_Om_one _)
  have hθ2 : ConjT.th S < Om (1 + 1) := Ui.ui_th_lt_Om2
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx hxθ
  rcases lt_or_ge x (Om 1) with h1 | h1
  · exact GxCl.small (hkey x hx h1)
  have h0 : x ≠ 0 := (lt_of_lt_of_le (zero_lt_one.trans Nm.one_lt_Om1) h1).ne'
  by_cases hP : IsPrincipal (· + ·) x
  · rcases prin_mem_cases hx (hZ1.trans h1) hP h0 with
      ⟨n, rfl⟩ | rfl | ⟨p, q, hp, hq, hpx, hqx, rfl⟩ | ⟨p, hp, hpx, rfl⟩ | ⟨π, e, hπ, -, -, -, rfl⟩
    · exact absurd (hxθ.trans hθ2) (not_lt.2 (mxOm2_lt_I n).le)
    · exact absurd (hxθ.trans hθ2) (not_lt.2 mxOm2_lt_Iw.le)
    · exact GxCl.phi (IH p hpx hp (hpx.trans hxθ)) (IH q hqx hq (hqx.trans hxθ))
    · have hp1 : p ≤ 1 := le_of_Om_lt_Om_succ (hxθ.trans hθ2)
      have hp1' : 1 ≤ p := not_lt.1 fun h => absurd h1 (not_le.2 (Om_lt_Om.2 h))
      rw [le_antisymm hp1 hp1']
      exact GxCl.om
    · rcases eq_or_lt_of_le h1 with h | h
      · rw [← h]; exact GxCl.om
      · exact GxCl.atom ⟨SC_psi hπ e, h, hxθ, hK _ hx⟩
  · obtain ⟨hl, ht⟩ := lead_tail_mem hx h0
    have hlx : lead x < x := lt_of_le_of_ne (lead_le h0) fun e =>
      hP (by rw [← e]; exact isPrincipal_add_omega0_opow _)
    have htx : tail x < x := tail_lt h0
    rw [← lead_add_tail h0]
    exact GxCl.add (IH _ hlx hl (hlx.trans hxθ)) (IH _ htx ht (htx.trans hxθ))

/-- **Hull membership of the atoms**: an atom over `Z`, with every ordinal below `Z` of the notation, lies in every
`Cl(a, b)` with `Ω_ω ≤ a` and a strongly critical `b ∈ [Z, Ω₁]`. -/
theorem qt_mem {a b Z s : Ordinal.{0}} (ha : Om ω ≤ a) (hb : SC b) (hb1 : b ≤ Om 1) (hZb : Z ≤ b)
    (hZN : ∀ z < Z, z ∈ ⋃ e, S.CSet e 0) (hs : s ∈ qtAt S Z) : s ∈ S.CSet a b := by
  have hsN : s ∈ ⋃ e, S.CSet e 0 :=
    (qt_N_iff S).1 (qt_K_Vals S (fun z hz => (qt_N_iff S).2 (hZN z hz)) hs.2.2.2)
  have hd : Ui.uiDat S s < b := by
    have h1 : Ul.ulD S 0 s < b := (Ul.ul_vis hb).2 (hs.2.2.2.mono hZb)
    rw [← Vd.vdD_eq] at h1
    exact (Vd.vd_dat_ui hsN hb hb1).1 h1
  have hargs : Ui.uiArgs S a s := Ui.uiArgsT_mono ha _ (Ui.ui_args_th s hsN hs.2.2.1)
  obtain ⟨-, hv⟩ := Bc.bcNf_spec S hsN
  have h := Ui.ui_code_mem (S := S) (A := a) (q := b) _ hd hargs
  rwa [hv] at h

variable (S)

/-- **THE ATOM SYSTEM BELOW `θ`**: atoms the strongly critical members `Ω₁ < s < θ` of `K⁽⁰⁾_Z`, bound `θ`. -/
noncomputable def qtU : ZbAS where
  At := qtAt S
  V := ConjT.th S
  V_SC := ConjT.SC_th S
  V_lt := Ui.ui_th_lt_Om2
  Om1_lt_V := (psiS_bounds (S := S) _ 1).1
  gxAt := fun _ s hs => ⟨hs.1, hs.2.1⟩
  mono := fun _ _ h _ hs => ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.mono h⟩
  lt_V := fun _ _ hs => hs.2.2.1
  supp := fun _ _ hZ hs => by
    obtain ⟨m, hm, hk⟩ := Ul.ulK_supp hZ hs.2.2.2
    exact ⟨m + 1, hZ.isSuccLimit.add_one_lt hm, hs.1, hs.2.1, hs.2.2.1, hk⟩

theorem qtU_ok : (qtU S).Ok S where
  mem := fun _ _ _ _ ha hb hb1 hZb hZN hs => qt_mem ha hb hb1 hZb hZN hs
  hull := fun _ _ _ hZ1 hkey x hx hxV => qt_hull hZ1 hkey x hx hxV

instance : Fact ((qtU S).Ok S) := ⟨qtU_ok S⟩

theorem qtU_V : (qtU S).V = ConjT.th S := rfl

theorem qtU_At (Z : Ordinal.{0}) : (qtU S).At Z = qtAt S Z := rfl

end Googology.Trans.PoR.InaccPsi.R2.Qt
