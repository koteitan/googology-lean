import Googology.Trans.PoR.InaccPsi.R2.ZbTl
import Googology.Trans.PoR.InaccPsi.R2.UcCl
import Googology.Trans.PoR.InaccPsi.R2.UfDL
import Googology.Trans.PoR.InaccPsi.R2.UfHull
import Googology.Trans.PoR.InaccPsi.R2.UfB

/-!
# QcAt: THE ATOM SYSTEM OF ALL CODES BELOW `B₂` (ATOMS: THE VALUES `H_γ(y)` OF EVERY LEVEL `γ < E₂`)

`B₂ = Uc.ucB = ψ_{Ω₂}(ε_{Ω₂+1})`, `UcCl Z` the codes over `Z` below `B₂` (`R2.UcCl`: the ordinals below `Z`, `Ω₁`, `+`,
`φ`, the codes of `TlCl Z` and the atoms `H_γ(y) ≥ X`).  As `Zb.zbTl` for the codes below `X`, the strongly critical
codes `Ω₁ < s < B₂` of `UcCl Z` form an abstract atom system `qcU : Zb.ZbAS` with the bound `B₂`: the hull lemma is
`Uf.uf_diglev`, hull membership `Uf.uf_mem_CSet` with `Uf.uf_args_E` (the own arguments of the atoms below `B₂` are
below `E₂ < Ω_ω`).  So the frontier lemma `Zb.zbUV` holds with every atom below `B₂`; the bound `V = B₂` is past every
`Γ(c+1)`, `c < B₂`.

* `qcAt`, `qc_comps_supp`, `qc_supp` (**support of codes below every strongly critical `Z`**), `qc_gx` / `qc_of_gx`
  (**`GxCl Z (qcAt Z) x ⇔ UcCl Z x` below `B₂`**), `qcU` (**THE ATOM SYSTEM BELOW `B₂`**), `qcU_V`, `qcU_At`,
  `qcU_cl_iff`, `qc_tl_sub` (the atoms of `Zb.zbTl` are atoms of `qcU`).

No new axiom.  New definitions: `qcAt`, `qcU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Zb

/-- **The atoms over `Z`**: the strongly critical codes `Ω₁ < s < B₂` of `UcCl Z`. -/
def qcAt (Z : Ordinal.{0}) : Set Ordinal.{0} := {s | SC s ∧ Om 1 < s ∧ s < ucB ∧ UcCl Z s}

/-- **The components of a level are codes over one `Z' < Z`** when each is a code over some `Z' < Z`. -/
theorem qc_comps_supp {Z : Ordinal.{0}} (hZ : SC Z) :
    ∀ γ, (∀ x ∈ ucComps γ, ∃ Z' < Z, UcCl Z' x) → ∃ Z' < Z, ∀ x ∈ ucComps γ, UcCl Z' x := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro h
  by_cases h1 : γ < OmTwo
  · rw [ucComps_small h1] at h ⊢
    obtain ⟨Z', hZ', h'⟩ := h γ rfl
    exact ⟨Z', hZ', fun x hx => by rw [mem_singleton_iff.1 hx]; exact h'⟩
  by_cases h2 : γ < ucE
  · rw [ucComps_big (not_lt.1 h1) h2] at h ⊢
    obtain ⟨Z1, h1', g1⟩ := IH _ (uc_log_lt (not_lt.1 h1) h2) fun x hx => h x (Or.inl hx)
    obtain ⟨Z2, h2', g2⟩ := h (γ / OmTwo ^ log OmTwo γ) (Or.inr (Or.inl rfl))
    obtain ⟨Z3, h3', g3⟩ := IH _ (uc_mod_lt (not_lt.1 h1)) fun x hx => h x (Or.inr (Or.inr hx))
    refine ⟨max Z1 (max Z2 Z3), max_lt h1' (max_lt h2' h3'), fun x hx => ?_⟩
    rcases hx with hx | rfl | hx
    · exact (g1 x hx).mono (le_max_left _ _)
    · exact g2.mono ((le_max_left _ _).trans (le_max_right _ _))
    · exact (g3 x hx).mono ((le_max_right _ _).trans (le_max_right _ _))
  · rw [ucComps_out (not_lt.1 h2)]
    exact ⟨0, hZ.1, fun _ hx => absurd hx (Set.notMem_empty _)⟩

/-- **A code over a strongly critical `Z` is a code over some `Z' < Z`.** -/
theorem qc_supp {Z : Ordinal.{0}} (hZ : SC Z) {x : Ordinal.{0}} (hx : UcCl Z x) : ∃ Z' < Z, UcCl Z' x := by
  have h1 := gg_one_lt_of_SC hZ
  induction hx with
  | @small x h => exact ⟨x + 1, hZ.isPrincipal h h1, UcCl.small (lt_add_one x)⟩
  | om => exact ⟨0, hZ.1, UcCl.om⟩
  | add _ _ ihx ihy =>
    obtain ⟨Z1, h1', g1⟩ := ihx
    obtain ⟨Z2, h2', g2⟩ := ihy
    exact ⟨max Z1 Z2, max_lt h1' h2', UcCl.add (g1.mono (le_max_left _ _)) (g2.mono (le_max_right _ _))⟩
  | phi _ _ ihx ihy =>
    obtain ⟨Z1, h1', g1⟩ := ihx
    obtain ⟨Z2, h2', g2⟩ := ihy
    exact ⟨max Z1 Z2, max_lt h1' h2', UcCl.phi (g1.mono (le_max_left _ _)) (g2.mono (le_max_right _ _))⟩
  | tl h =>
    obtain ⟨Z', hZ', h'⟩ := zbTl_supp hZ h
    exact ⟨Z', hZ', UcCl.tl h'⟩
  | @hatom γ y hγ _ _ hX ihc ihy =>
    obtain ⟨Z1, h1', g1⟩ := qc_comps_supp hZ γ ihc
    obtain ⟨Z2, h2', g2⟩ := ihy
    exact ⟨max Z1 Z2, max_lt h1' h2',
      UcCl.hatom hγ (fun x hx => (g1 x hx).mono (le_max_left _ _)) (g2.mono (le_max_right _ _)) hX⟩

/-- **The atoms of `Zb.zbTl` are atoms of `qcU`.** -/
theorem qc_tl_sub (Z : Ordinal.{0}) : zbTlAt Z ⊆ qcAt Z :=
  fun _ hs => ⟨hs.1, hs.2.1, hs.2.2.1.trans uc_X_lt_B, UcCl.tl hs.2.2.2⟩

/-- **A code of `UcCl Z` below `B₂` is a code over the atoms `qcAt Z`** (`Z ≤ Ω₁`). -/
theorem qc_gx {Z : Ordinal.{0}} (hZ : Z ≤ Om1) {x : Ordinal.{0}} (hx : UcCl Z x) : x < ucB → GxCl Z (qcAt Z) x := by
  induction hx with
  | small h => exact fun _ => GxCl.small h
  | om => intro _; rw [Br.Om1_eq]; exact GxCl.om
  | @add x y _ _ ihx ihy =>
    exact fun h => GxCl.add (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y _ _ ihx ihy =>
    exact fun h => GxCl.phi (ihx (lt_of_le_of_lt (left_le_veblen x y) h))
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h))
  | @tl x h =>
    intro _
    exact (zbTl_gx h (uc_tl_lt_X hZ h)).mono le_rfl (qc_tl_sub Z)
  | @hatom γ y hγ hc hy hX _ _ =>
    intro h
    exact GxCl.atom ⟨ucH_SC γ y, by rw [← Br.Om1_eq]; exact ucH_gt γ y, h, UcCl.hatom hγ hc hy hX⟩

/-- **A code over the atoms `qcAt Z` is a code of `UcCl Z`.** -/
theorem qc_of_gx {Z : Ordinal.{0}} {x : Ordinal.{0}} (hx : GxCl Z (qcAt Z) x) : UcCl Z x := by
  induction hx with
  | small h => exact UcCl.small h
  | om => rw [← Br.Om1_eq]; exact UcCl.om
  | atom hs => exact hs.2.2.2
  | add _ _ ihx ihy => exact UcCl.add ihx ihy
  | phi _ _ ihx ihy => exact UcCl.phi ihx ihy

/-- **THE ATOM SYSTEM BELOW `B₂`**: atoms the strongly critical codes `Ω₁ < s < B₂`, bound `B₂`. -/
noncomputable def qcU : ZbAS where
  At := qcAt
  V := ucB
  V_SC := ucB_SC
  V_lt := by rw [← Uf.uf_Om2]; exact ucB_lt_Om2
  Om1_lt_V := by rw [← Br.Om1_eq]; exact ucB_gt
  gxAt := fun _ s hs => ⟨hs.1, hs.2.1⟩
  mono := fun _ _ h _ hs => ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.mono h⟩
  lt_V := fun _ _ hs => hs.2.2.1
  supp := fun _ s hZ hs => by
    obtain ⟨Z', hZ', h'⟩ := qc_supp hZ hs.2.2.2
    exact ⟨Z', hZ', hs.1, hs.2.1, hs.2.2.1, h'⟩

theorem qcU_ok (S : InaccSeq.{0}) : qcU.Ok S where
  mem := fun a b Z s ha hb hb1 hZb _ hs => by
    have hb1' : b ≤ Om1 := by rw [Br.Om1_eq]; exact hb1
    have hE : ucE ≤ a := Uf.uf_E_lt_Omw.le.trans (le_self_add.trans ha)
    exact (Uf.uf_mem_CSet (S := S) hb hb1' le_rfl s (hs.2.2.2.mono hZb) (Uf.uf_args_E hE hs.2.2.1)).1
  hull := fun a Z hZ hZ1 hkey x hx hxV => by
    have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1
    have hcoll : ∀ e, e < a → e ∈ S.CSet a Z → Ri.RiDg Z e → Uf.UfLev Z e → S.psi e (Om 1) < Z :=
      fun e hea heC _ _ => hkey _ (CSet.psi_mem hea Low.InR_Om_one (CSet.Om_mem (CSet.one_mem _ _)) heC)
        (psi_lt Low.InR_Om_one _)
    exact qc_gx hZ1' ((Uf.uf_diglev (S := S) hZ hZ1 hcoll x hx).2.2.1 hxV) hxV

instance (S : InaccSeq.{0}) : Fact (qcU.Ok S) := ⟨qcU_ok S⟩

theorem qcU_V : qcU.V = ucB := rfl

theorem qcU_At (Z : Ordinal.{0}) : qcU.At Z = qcAt Z := rfl

/-- **`GxCl Z (qcU.At Z) x ⇔ UcCl Z x` below `B₂`** (`Z ≤ Ω₁`). -/
theorem qcU_cl_iff {Z x : Ordinal.{0}} (hZ : Z ≤ Om1) (hx : x < ucB) : GxCl Z (qcU.At Z) x ↔ UcCl Z x :=
  ⟨qc_of_gx, fun h => qc_gx hZ h hx⟩

end Googology.Trans.PoR.InaccPsi.R2.Qc
