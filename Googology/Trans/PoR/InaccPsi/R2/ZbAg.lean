import Googology.Trans.PoR.InaccPsi.R2.ZbTl

/-!
# ZbAg: THE ATOM SYSTEM `zbU` (ALL CODES BELOW `X`, WITH THE ATOMS OF `Yr`) AND ITS AGREEMENT WITH `Yr.yrKN`

`zbU` has the atoms of `Zb.zbTl` (the strongly critical codes of `Tl.TlCl Z` below `X`) together with the atoms
`Γ_{Ω₁+1+c}` (`c < B_Γ`, gate `Yr.yrG c < Z`) of the reading systems `Yr.yrRSN` below `B_Γ`.  Below `B_Γ` both atom
sets give the same codes over every strongly critical `Z ≤ Ω₁` (`zb_tl_K`: a code of `TlCl Z` below `B_Γ` has its
atoms `F_β(y)` of kind `β = 0`, `Γ_{Ω₁+1+i}` with `i` again a code, so `Yr.yr_code_gate` bounds the gate of `i`).
So every reading statement of `Yr` (`Yr.YrRS.GqLC`) is a reading statement with the atoms of `zbU`.

* `zbKAt`, `zbUAt`, `zbU` (**THE ATOM SYSTEM BELOW `X` WITH THE `Yr` ATOMS**), `zbU_V`;
* `zb_tl_K` (**`TlCl Z x`, `x < B_Γ` ⇒ `x` is a code over the `Yr` atoms**), `zb_U_K`, `zb_K_yr`, `zb_yr_U`,
  `zb_cl_yr_iff`, `zb_th_yr` (**`Θ_y` with the atoms of `Yr.yrKN B` = `Θ_y` with the atoms of `zbU` up to
  `Γ_{Ω₁+1+B}`**).

No new axiom.  New definitions: `zbKAt`, `zbUAt`, `zbU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Tf
  Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Gs

/-- **The atoms of the reading systems `Yr.yrRSN`**: `Γ_{Ω₁+1+c}`, `c < B_Γ`, gate below `Z`. -/
def zbKAt (Z : Ordinal.{0}) : Set Ordinal.{0} := {s | ∃ c, c < tfBG ∧ yrG c < Z ∧ s = gcG c}

/-- **The atoms of `zbU`.** -/
def zbUAt (Z : Ordinal.{0}) : Set Ordinal.{0} := zbTlAt Z ∪ zbKAt Z

theorem zbKAt_hA {Z : Ordinal.{0}} : ∀ s ∈ zbKAt Z, ∃ i, s = gcG i ∧ i < gcG i ∧ yrG i < Z := by
  rintro s ⟨c, hc, hg, rfl⟩
  exact ⟨c, rfl, yr_idx_BG hc, hg⟩

/-- **A code of `TlCl Z` below `B_Γ` is a code over the `Yr` atoms** (`Z` strongly critical, `Z ≤ Ω₁`). -/
theorem zb_tl_K {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om1) :
    ∀ x, x < tfBG → TlCl Z x → GxCl Z (zbKAt Z) x := by
  have hωZ : ω < Z := by
    have hZw : ∀ u, u < Z → ω ^ u < Z := fun u hu => by
      have := hZ.2 0 hZ.1 u hu; rwa [veblen_zero_apply] at this
    have h1 := hZw 0 hZ.1; rw [opow_zero] at h1
    have := hZw 1 h1; rwa [opow_one] at this
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hxB hx
  suffices H : ∀ w, TlCl Z w → w ≤ x → GxCl Z (zbKAt Z) w from H x hx le_rfl
  intro w hw
  induction hw with
  | small h => exact fun _ => GxCl.small h
  | om => intro _; rw [Br.Om1_eq]; exact GxCl.om
  | @add a b _ _ iha ihb =>
    exact fun h => GxCl.add (iha (le_self_add.trans h)) (ihb (le_add_self.trans h))
  | @phi a b _ _ iha ihb =>
    exact fun h => GxCl.phi (iha ((left_le_veblen a b).trans h)) (ihb ((right_le_veblen a b).trans h))
  | @atom β y _ hy hlt _ _ =>
    intro h
    have hsB : rhF β y < tfBG := h.trans_lt hxB
    have hβ0 : β = 0 := by
      by_contra hne
      have hfix : gamma (rhF β y) = rhF β y := by
        rw [← rhF_zero]; exact rhF_fix_lower (pos_iff_ne_zero.2 hne) y
      exact absurd (tfBG_le hfix hlt) (not_le.2 hsB)
    subst hβ0
    rw [rhF_zero] at hlt hsB h
    rw [rhF_zero]
    have hy1 : Om1 < y := tf_Om1_lt_gamma.1 hlt
    obtain ⟨i, hi⟩ := exists_add_of_le (Order.add_one_le_of_lt hy1)
    have hgi : gamma y = gcG i := by rw [tf_gcG, hi]
    have hiy : i ≤ y := by rw [hi]; exact le_add_self
    have hiB : i < tfBG := (hiy.trans (isNormal_gamma.strictMono.le_apply)).trans_lt hsB
    have hii : i < gcG i := yr_idx_BG hiB
    have hiTl : TlCl Z i := by
      have hy' : TlCl Z (Om1 + (1 + i)) := by rw [← add_assoc, ← hi]; exact hy
      have h1i := (tl_cl_Om1_add hZ).1 hy'
      rcases lt_or_ge i ω with hiw | hiw
      · exact TlCl.small (hiw.trans hωZ)
      · rwa [one_add_of_omega0_le hiw] at h1i
    have hix : i < x := hii.trans_le (hgi ▸ h)
    have hiK := IH i hix hiB hiTl
    have hg := yr_code_gate hZ hZ1 zbKAt_hA i hiK
    rw [hgi]
    exact GxCl.atom ⟨i, hiB, hg, rfl⟩

/-- **THE ATOM SYSTEM BELOW `X` WITH THE `Yr` ATOMS.** -/
noncomputable def zbU : ZbAS where
  At := zbUAt
  V := tlX
  V_SC := tlX_SC
  V_lt := tlX_lt_Om2
  Om1_lt_V := by rw [← Br.Om1_eq]; exact tlX_gt
  gxAt := fun _ s hs => by
    rcases hs with hs | ⟨c, -, -, rfl⟩
    · exact ⟨hs.1, hs.2.1⟩
    · exact ⟨gcG_SC c, gcG_Om1_lt c⟩
  mono := fun Z Z' h s hs => by
    rcases hs with hs | ⟨c, hc, hg, rfl⟩
    · exact Or.inl (zbTl.mono Z Z' h hs)
    · exact Or.inr ⟨c, hc, hg.trans_le h, rfl⟩
  lt_V := fun _ s hs => by
    rcases hs with hs | ⟨c, hc, -, rfl⟩
    · exact hs.2.2.1
    · exact (yr_gcG_lt_BG hc).trans tl_BG_lt_X
  supp := fun Z s hZ hs => by
    rcases hs with hs | ⟨c, hc, hg, rfl⟩
    · obtain ⟨Z', h1, h2⟩ := zbTl.supp Z s hZ hs
      exact ⟨Z', h1, Or.inl h2⟩
    · exact ⟨yrG c + 1, hZ.isPrincipal hg (gg_one_lt_of_SC hZ), Or.inr ⟨c, hc, lt_add_one _, rfl⟩⟩

theorem zbU_ok (S : InaccSeq.{0}) : zbU.Ok S where
  mem := fun a b Z s ha hb hb1 hZb hZN hs => by
    rcases hs with hs | ⟨c, hc, hg, rfl⟩
    · exact (zbTl_ok S).mem a b Z s ha hb hb1 hZb hZN hs
    · have hca : c < a := (hc.trans tfBG_lt_Om2).trans (Ph.ph_Om2_lt_Omw.trans_le ha)
      have hcC := (yr_mem (S := S) c hc hca (hg.trans_le hZb)).1
      have hpsi : gcG c = S.psi c (Om (1 + 1)) := by rw [tf_psi S c hc.le, tf_gcG]
      rw [hpsi]
      exact CSet.psi_mem hca (InR_Om_succ 1) (Ga.ga_Om2_mem _ _) hcC
  hull := fun a Z hZ hZ1 hkey x hx hxV =>
    ((zbTl_ok S).hull a Z hZ hZ1 hkey x hx hxV).mono le_rfl fun _ hs => Or.inl hs

instance (S : InaccSeq.{0}) : Fact (zbU.Ok S) := ⟨zbU_ok S⟩

theorem zbU_V : zbU.V = tlX := rfl

theorem zbU_At (Z : Ordinal.{0}) : zbU.At Z = zbUAt Z := rfl

/-- **Below `B_Γ` a code over the atoms of `zbU` is a code over the `Yr` atoms.** -/
theorem zb_U_K {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om1) {x : Ordinal.{0}} (hx : GxCl Z (zbU.At Z) x) :
    x < tfBG → GxCl Z (zbKAt Z) x := by
  induction hx with
  | small h => exact fun _ => GxCl.small h
  | om => exact fun _ => GxCl.om
  | @atom s hs =>
    intro h
    rcases hs with hs | hs
    · exact zb_tl_K hZ hZ1 s h hs.2.2.2
    · exact GxCl.atom hs
  | @add a b _ _ iha ihb =>
    exact fun h => GxCl.add (iha (lt_of_le_of_lt le_self_add h)) (ihb (lt_of_le_of_lt le_add_self h))
  | @phi a b _ _ iha ihb =>
    exact fun h => GxCl.phi (iha (lt_of_le_of_lt (left_le_veblen a b) h))
      (ihb (lt_of_le_of_lt (right_le_veblen a b) h))

/-- **Below `Γ_{Ω₁+1+B}` a code over the `Yr` atoms is a code over the atoms of `Yr.yrKN B`.** -/
theorem zb_K_yr {B : Ordinal.{0}} (hBB : B < tfBG) {Z x : Ordinal.{0}} (hx : GxCl Z (zbKAt Z) x) :
    x < gcG B → GxCl Z ((yrKN B hBB).At Z) x := by
  induction hx with
  | small h => exact fun _ => GxCl.small h
  | om => exact fun _ => GxCl.om
  | @atom s hs =>
    intro h
    obtain ⟨c, -, hg, rfl⟩ := hs
    exact GxCl.atom ⟨c, gcG_lt_iff.1 h, hg, rfl⟩
  | @add a b _ _ iha ihb =>
    exact fun h => GxCl.add (iha (lt_of_le_of_lt le_self_add h)) (ihb (lt_of_le_of_lt le_add_self h))
  | @phi a b _ _ iha ihb =>
    exact fun h => GxCl.phi (iha (lt_of_le_of_lt (left_le_veblen a b) h))
      (ihb (lt_of_le_of_lt (right_le_veblen a b) h))

/-- **A code over the atoms of `Yr.yrKN B` is a code over the atoms of `zbU`.** -/
theorem zb_yr_U {B : Ordinal.{0}} (hBB : B < tfBG) {Z x : Ordinal.{0}} (hx : GxCl Z ((yrKN B hBB).At Z) x) :
    GxCl Z (zbU.At Z) x :=
  hx.mono le_rfl fun _ hs => by
    obtain ⟨c, hc, hg, rfl⟩ := hs
    exact Or.inr ⟨c, hc.trans hBB, hg, rfl⟩

/-- **`GxCl Z (zbU.At Z) x ⇔ GxCl Z ((yrKN B).At Z) x` below `Γ_{Ω₁+1+B}`** (`Z` strongly critical, `Z ≤ Ω₁`). -/
theorem zb_cl_yr_iff {B : Ordinal.{0}} (hBB : B < tfBG) {Z x : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om1)
    (hx : x < gcG B) : GxCl Z ((yrKN B hBB).At Z) x ↔ GxCl Z (zbU.At Z) x :=
  ⟨zb_yr_U hBB, fun h => zb_K_yr hBB (zb_U_K hZ hZ1 h (hx.trans (yr_gcG_lt_BG hBB))) hx⟩

/-- **`Θ_y` with the atoms of `Yr.yrKN B` is `Θ_y` with the atoms of `zbU` up to `Γ_{Ω₁+1+B}`.** -/
theorem zb_th_yr {B : Ordinal.{0}} (hBB : B < tfBG) {y d : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1)
    (hd : d ≤ gcG B) : gxTh y ((yrKN B hBB).At y) d = gxTh y (zbU.At y) d :=
  ggOtp_congr d fun _ hx => zb_cl_yr_iff hBB hy (by rw [Br.Om1_eq]; exact hy1.le) (hx.trans_le hd)

end Googology.Trans.PoR.InaccPsi.R2.Zb
