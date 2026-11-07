import Googology.Trans.PoR.InaccPsi.R2.QtAt
import Googology.Trans.PoR.InaccPsi.R2.QcAt

/-!
# QtK: THE CODES OF `qtU` ARE THE MEMBERS OF `K⁽⁰⁾_Z` BELOW `θ`; BELOW `B₂` THEY ARE THE CODES OF `qcU`

`K⁽ˢ⁾_q = Ul.UlK S s q`, `θ = ConjT.th S`, `B₂ = Uc.ucB`.  The splitting facts of `Cl(a, b)` (`lead_tail_mem`,
`mem_of_veblen_mem`, `prin_mem_cases`) hold for `K⁽ˢ⁾_q` with the same proofs; so a member of `K⁽⁰⁾_Z` below `θ`
is a code over the atoms `Qt.qtAt S Z` (strongly critical `Z ≤ Ω₁`), and conversely.  Below `B₂` the codes of
`qtU` are those of `Qc.qcU` (`Uo.uo_cl_iffK`), and so are the readings.

* `ulK_veb_parts` (**`φ(a, b) ∈ K_q` with `a, b < φ(a, b)` gives `a, b ∈ K_q`**), `ulK_lead_tail`,
  `ulK_prin_cases` (**the principal members of `K_q` at or above `q`**);
* `qt_K_of_codes`, `qt_codes` (**`GxCl Z (qtAt S Z) x ↔ x ∈ K⁽⁰⁾_Z`** for `x < θ`), `qt_qc_codes` (**below `B₂` the codes of
  `qtU` and `qcU` agree**), `qt_qc_th` (**and so do the readings `gxTh y (·) c`, `c ≤ B₂`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Ul

variable {S : InaccSeq.{0}} {s q : Ordinal.{0}}

/-- **`φ(a, b) ∈ K_q` with `a, b < φ(a, b)` gives `a, b ∈ K_q`.** -/
theorem ulK_veb_parts {a b : Ordinal.{0}} (h : UlK S s q (veblen a b)) (ha : a < veblen a b)
    (hb : b < veblen a b) : UlK S s q a ∧ UlK S s q b := by
  suffices H : ∀ z, UlK S s q z → ∀ x y, z = veblen x y → x < z → y < z → UlK S s q x ∧ UlK S s q y from
    H _ h a b rfl ha hb
  intro z hz
  induction hz with
  | small h => intro x y _ hx hy; exact ⟨UlK.small (hx.trans h), UlK.small (hy.trans h)⟩
  | zero => intro x y e _ _; exact absurd e veblen_pos.ne
  | inacc n => intro x y e hx hy; exact absurd e.symm ((SC_I n).not_veblen_lt hx hy)
  | inaccW => intro x y e hx hy; exact absurd e.symm (SC_Iw.not_veblen_lt hx hy)
  | @add p r _ _ ihp ihr =>
    intro x y e hx hy
    have hP : IsPrincipal (· + ·) (p + r) := by rw [e]; exact veblen_isPrincipal x y
    by_cases hr0 : r = 0
    · subst hr0
      simp only [add_zero] at e hx hy
      exact ihp x y e hx hy
    · have hpz : p < p + r := lt_add_of_pos_right p (pos_iff_ne_zero.2 hr0)
      have hrz : r = p + r :=
        le_antisymm le_add_self (not_lt.1 fun h => lt_irrefl _ (hP hpz h))
      rw [← hrz] at e hx hy
      exact ihr x y e hx hy
  | @phi p r hp hr ihp ihr =>
    intro x y e hx hy
    by_cases hpz : p = veblen p r
    · rw [← hpz] at e hx hy; exact ihp x y e hx hy
    by_cases hrz : r = veblen p r
    · rw [← hrz] at e hx hy; exact ihr x y e hx hy
    have hrl : r < veblen p r := lt_of_le_of_ne (right_le_veblen p r) hrz
    rcases veblen_eq_veblen_iff.1 e with ⟨rfl, rfl⟩ | ⟨_, h⟩ | ⟨_, h⟩
    · exact ⟨hp, hr⟩
    · rw [e, ← h] at hrl; exact absurd hrl (lt_irrefl _)
    · rw [h] at hy; exact absurd hy (lt_irrefl _)
  | @om p _ _ =>
    intro x y e hx hy
    by_cases hp0 : p = 0
    · rw [hp0, Om_zero] at e; exact absurd e veblen_pos.ne
    · exact absurd e.symm ((SC_Om hp0).not_veblen_lt hx hy)
  | @coll π e hπ _ _ _ _ _ =>
    intro x y ex hx hy
    exact absurd ex.symm ((SC_psi hπ e).not_veblen_lt hx hy)

/-- **The leading summand and the rest of a member of `K_q` are members** (`q` strongly critical). -/
theorem ulK_lead_tail (hq : SC q) {x : Ordinal.{0}} (hx : UlK S s q x) (h0 : x ≠ 0) :
    UlK S s q (lead x) ∧ UlK S s q (tail x) := by
  have hl : UlK S s q (lead x) := (ulK_dec hq x hx).2.opow
  exact ⟨hl, (ulK_dec hq x hx).1 _ hl (lead_le h0)⟩

/-- **The principal members of `K_q` at or above `q`.** -/
theorem ulK_prin_cases {z : Ordinal.{0}} (hz : UlK S s q z) (hqz : q ≤ z) (hP : IsPrincipal (· + ·) z)
    (hz0 : z ≠ 0) :
    (∃ n, z = S.I n) ∨ z = S.Iw ∨
    (∃ p r, UlK S s q p ∧ UlK S s q r ∧ p < z ∧ r < z ∧ z = veblen p r) ∨
    (∃ p, UlK S s q p ∧ p < z ∧ z = Om p) ∨
    (∃ π e, S.InR π ∧ π ≠ Om (s + 1) ∧ z = S.psi e π) := by
  revert hqz hP hz0
  induction hz with
  | small h => intro hqz _ _; exact absurd (lt_of_lt_of_le h hqz) (lt_irrefl _)
  | zero => intro _ _ hz0; exact absurd rfl hz0
  | inacc n => intro _ _ _; exact Or.inl ⟨n, rfl⟩
  | inaccW => intro _ _ _; exact Or.inr (Or.inl rfl)
  | @add p r _ _ ihp ihr =>
    intro hqz hP hz0
    by_cases hr0 : r = 0
    · subst hr0
      simp only [add_zero] at hqz hP hz0 ⊢
      exact ihp hqz hP hz0
    · have hpz : p < p + r := lt_add_of_pos_right p (pos_iff_ne_zero.2 hr0)
      have hrz : r = p + r :=
        le_antisymm le_add_self (not_lt.1 fun h => lt_irrefl _ (hP hpz h))
      rw [← hrz] at hqz hP hz0 ⊢
      exact ihr hqz hP hz0
  | @phi p r hp hr ihp ihr =>
    intro hqz hP hz0
    by_cases hpz : p = veblen p r
    · rw [← hpz] at hqz hP hz0 ⊢; exact ihp hqz hP hz0
    by_cases hrz : r = veblen p r
    · rw [← hrz] at hqz hP hz0 ⊢; exact ihr hqz hP hz0
    exact Or.inr (Or.inr (Or.inl ⟨p, r, hp, hr, lt_of_le_of_ne (left_le_veblen p r) hpz,
      lt_of_le_of_ne (right_le_veblen p r) hrz, rfl⟩))
  | @om p hp ihp =>
    intro hqz hP hz0
    rcases (le_Om p).lt_or_eq with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, h, rfl⟩)))
    · rw [← h] at hqz hP hz0 ⊢; exact ihp hqz hP hz0
  | @coll π e hπ hπW _ _ _ _ =>
    intro _ _ _
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨π, e, hπ, hπW, rfl⟩)))

/-- A code over the atoms `qtAt S Z` is in `K⁽⁰⁾_Z`. -/
theorem qt_K_of_codes {Z x : Ordinal.{0}} (h : GxCl Z (qtAt S Z) x) : UlK S 0 Z x := by
  induction h with
  | small h => exact UlK.small h
  | om => exact UlK.om UlK.one
  | atom hs => exact hs.2.2.2
  | add _ _ ihx ihy => exact UlK.add ihx ihy
  | phi _ _ ihx ihy => exact UlK.phi ihx ihy

/-- **The codes of `qtU` below `θ` are the members of `K⁽⁰⁾_Z`** (`Z ≤ Ω₁` strongly critical). -/
theorem qt_codes {Z x : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (hxθ : x < ConjT.th S) :
    GxCl Z (qtAt S Z) x ↔ UlK S 0 Z x := by
  refine ⟨qt_K_of_codes, ?_⟩
  have hθ2 : ConjT.th S < Om (1 + 1) := Ui.ui_th_lt_Om2
  have hL : Om (0 : Ordinal.{0}) < Z := by rw [Om_zero]; exact hZ.1
  revert hxθ
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hxθ hx
  rcases lt_or_ge x (Om 1) with h1 | h1
  · exact GxCl.small (ulK_lt_W omega0_pos hZ hL hx (by rw [zero_add]; exact h1))
  have h0 : x ≠ 0 := (lt_of_lt_of_le (zero_lt_one.trans Nm.one_lt_Om1) h1).ne'
  have hZx : Z ≤ x := hZ1.trans h1
  by_cases hP : IsPrincipal (· + ·) x
  · rcases ulK_prin_cases hx hZx hP h0 with
      ⟨n, rfl⟩ | rfl | ⟨p, r, hp, hr, hpx, hrx, rfl⟩ | ⟨p, hp, hpx, rfl⟩ | ⟨π, e, hπ, -, rfl⟩
    · exact absurd (hxθ.trans hθ2) (not_lt.2 (mxOm2_lt_I n).le)
    · exact absurd (hxθ.trans hθ2) (not_lt.2 mxOm2_lt_Iw.le)
    · exact GxCl.phi (IH p hpx (hpx.trans hxθ) hp) (IH r hrx (hrx.trans hxθ) hr)
    · have hp1 : p ≤ 1 := le_of_Om_lt_Om_succ (hxθ.trans hθ2)
      have hp1' : 1 ≤ p := not_lt.1 fun h => absurd h1 (not_le.2 (Om_lt_Om.2 h))
      rw [le_antisymm hp1 hp1']
      exact GxCl.om
    · rcases eq_or_lt_of_le h1 with h | h
      · rw [← h]; exact GxCl.om
      · exact GxCl.atom ⟨SC_psi hπ e, h, hxθ, hx⟩
  · obtain ⟨hl, ht⟩ := ulK_lead_tail hZ hx h0
    have hlx : lead x < x := lt_of_le_of_ne (lead_le h0) fun e =>
      hP (by rw [← e]; exact isPrincipal_add_omega0_opow _)
    have htx : tail x < x := tail_lt h0
    rw [← lead_add_tail h0]
    exact GxCl.add (IH _ hlx (hlx.trans hxθ) hl) (IH _ htx (htx.trans hxθ) ht)

/-- **Below `B₂` the codes of `qtU` and of `qcU` agree** (`Z ≤ Ω₁` strongly critical). -/
theorem qt_qc_codes {Z x : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (hxB : x < Uc.ucB) :
    GxCl Z (qtAt S Z) x ↔ GxCl Z (Qc.qcAt Z) x := by
  have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1
  rw [qt_codes hZ hZ1 (hxB.trans Vd.vd_B_lt_th), ← Uo.uo_cl_iffK hZ hZ1' hxB]
  exact ⟨fun h => Qc.qc_gx hZ1' h hxB, Qc.qc_of_gx⟩

/-- **Below `B₂` the readings of `qtU` and of `qcU` agree.** -/
theorem qt_qc_th {y c : Ordinal.{0}} (hy : SC y) (hy1 : y ≤ Om 1) (hc : c ≤ Uc.ucB) :
    gxTh y (qtAt S y) c = gxTh y (Qc.qcAt y) c :=
  Gg.ggOtp_congr c fun _ hx => qt_qc_codes hy hy1 (hx.trans_le hc)

end Googology.Trans.PoR.InaccPsi.R2.Qt
