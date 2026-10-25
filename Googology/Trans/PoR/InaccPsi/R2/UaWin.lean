import Googology.Trans.PoR.InaccPsi.R2.UaCode

/-!
# Codes in the windows `(φ(Ω₂, u), φ(Ω₂, u + 1))` and the bound `X₃ = φ(Ω₂ + 1, 0)`

`φ = veblen`, codes = `Le.LeCl κ Q` (`κ`, `Q` strongly critical), `F_u = φ(Ω₂, u)` (the fixed points of every
`φ(c, ·)`, `c < Ω₂`), `X₃ = Ua.uaX3 = φ(Ω₂ + 1, 0)` (the least fixed point of `φ(Ω₂, ·)`).

* `uaX3`, `uaX3_lim`, `uaX3_lt_Gam`, `uaX3_lt_G3`, `uaX2_lt_X3`, `uaX3_lev` (**every `φ(p, q) < X₃` has `p ≤ Ω₂`**),
  `uaWin_lev` (**every `φ(p, q)` strictly inside a window has a level `p < Ω₂`**), `uaG_le_F`;
* `uaCl_decK` (**`Ta.taCl_dec` at the level `κ` itself**: a code `w < φ(κ, X)`, `X` a limit, is below `φ(κ, u)` for
  a code `u < X`);
* `uaCl_FW` (**a code inside `[F_u, F_{u+1})` gives the code `F_u`**, by `Ua.uaCl_idx` at the level `Ω₂`),
  `uaCl_levW`, `uaCl_NWin`, `uaCl_argW` (`Ua.uaCl_levX`, `Ua.uaCl_NX`, `Ua.uaCl_argX` in every window: no fixed
  point of a level `≥ Ω₂` lies strictly inside a window);
* `uaCl_levG` (**THE LEVEL OF A CODE AT EVERY LEVEL `c`**: a code `h ≥ φ(c, y) > Ω₂` with no fixed point of
  `φ(c, ·)` in `[φ(c, y), h]` gives the code `c`), `uaNoFix` (no fixed point of `φ(a, ·)` in
  `(φ(a, y'), φ(a, y' + 1)]`): the tools for the levels `≥ Ω₂`.

No new axiom.  New definition: `uaX3`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ua

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td
  Googology.Trans.PoR.InaccPsi.R2.Tg Googology.Trans.PoR.InaccPsi.R2.Tu Googology.Trans.PoR.InaccPsi.R2.Tx

variable {S : InaccSeq.{0}}

/-- **The bound `X₃ = φ(Ω₂ + 1, 0)`.** -/
noncomputable def uaX3 : Ordinal.{0} := veblen (Om (1 + 1) + 1) 0

theorem uaX3_lim : IsSuccLimit (uaX3 : Ordinal.{0}) := taVeb_lim (zero_lt_one.trans_le le_add_self).ne'

theorem uaX3_lt_Gam : uaX3 < uaGam :=
  uaGam_spec.1.2 _ (uaGam_spec.1.isSuccLimit.add_one_lt uaGam_spec.2) _ uaGam_spec.1.1

theorem uaX3_lt_G3 : uaX3 < S.psi 0 (Om (1 + 1 + 1)) := uaX3_lt_Gam.trans_le uaGam_le_G3

theorem uaX2_lt_X3 : uaX2 < uaX3 := by
  unfold uaX2 uaX3
  refine veblen_lt_veblen_iff.2 (Or.inr (Or.inl ⟨lt_add_one _, ?_⟩))
  exact ((ldOm2_SC.isSuccLimit.add_one_lt (gg_one_lt_of_SC ldOm2_SC)).trans (lt_add_one _)).trans_le
    (left_le_veblen _ _)

/-- **Every `φ(p, q) < X₃` has `p ≤ Ω₂`.** -/
theorem uaX3_lev {p q : Ordinal.{0}} (h : veblen p q < uaX3) : p ≤ Om (1 + 1) := by
  rcases veblen_lt_veblen_iff.1 h with ⟨_, hq⟩ | ⟨hlt, _⟩ | ⟨_, h2⟩
  · exact absurd hq (not_lt.2 zero_le)
  · exact Order.lt_add_one_iff.1 hlt
  · exact absurd h2 (not_lt.2 zero_le)

/-- `G ≤ F_u` for `u ≥ 1`. -/
theorem uaG_le_F {u : Ordinal.{0}} (hu : 1 ≤ u) : veblen (Om (1 + 1)) 1 ≤ veblen (Om (1 + 1)) u :=
  (veblen_le_veblen_iff_right).2 hu

/-- **Every `φ(p, q)` strictly inside a window `(F_u, F_{u+1})` has `p < Ω₂`.** -/
theorem uaWin_lev {u p q : Ordinal.{0}} (h1 : veblen (Om (1 + 1)) u < veblen p q)
    (h2 : veblen p q < veblen (Om (1 + 1)) (u + 1)) : p < Om (1 + 1) := by
  rcases veblen_lt_veblen_iff.1 h2 with ⟨hpe, hq⟩ | ⟨hlt, _⟩ | ⟨_, h3⟩
  · exfalso
    rw [hpe] at h1
    exact absurd ((veblen_le_veblen_iff_right).2 (Order.lt_add_one_iff.1 hq)) (not_le.2 h1)
  · exact hlt
  · exfalso
    have : u < veblen p q := (right_le_veblen _ u).trans_lt h1
    exact absurd h3 (not_lt.2 (Order.add_one_le_of_lt this))

section Code

variable {κ Q : Ordinal.{0}} (hQ : SC Q) (hκ : SC κ)

include hQ hκ

/-- **`Ta.taCl_dec` at the level `κ`**: a code `w < φ(κ, X)` (`X` a limit) is below `φ(κ, u)` for a code `u < X`. -/
theorem uaCl_decK {X : Ordinal.{0}} (hX : IsSuccLimit X) :
    ∀ w, LeCl κ Q w → w < veblen κ X → ∃ u, LeCl κ Q u ∧ u < X ∧ w < veblen κ u := by
  intro w hw hwX
  have h1X : 1 < X := Rv.rvLim_one_lt hX
  rcases lt_or_ge w κ with hwκ | hκw
  · refine ⟨1, LeCl.small (gg_one_lt_of_SC hQ), h1X, hwκ.trans_le ?_⟩
    calc κ = veblen κ 0 := hκ.veblen_zero.symm
      _ ≤ veblen κ 1 := (veblen_le_veblen_iff_right).2 zero_le
  · obtain ⟨u, hu, hu1, hu2⟩ := uaCl_idx hκ hQ.1 w hw (by rw [hκ.veblen_zero]; exact hκw)
    have huX : u < X := (veblen_lt_veblen_iff_right).1 (hu1.trans_lt hwX)
    exact ⟨u + 1, LeCl.add hu (LeCl.small (gg_one_lt_of_SC hQ)), hX.add_one_lt huX, hu2⟩

end Code

section Code2

variable {Q : Ordinal.{0}} (hQ : SC Q)

include hQ

/-- **A code inside `[F_u, F_{u+1})` gives the code `F_u`.** -/
theorem uaCl_FW {u h : Ordinal.{0}} (hh : LeCl (Om (1 + 1)) Q h) (h1 : veblen (Om (1 + 1)) u ≤ h)
    (h2 : h < veblen (Om (1 + 1)) (u + 1)) : LeCl (Om (1 + 1)) Q (veblen (Om (1 + 1)) u) := by
  have h0 : veblen (Om (1 + 1)) 0 ≤ h := ((veblen_le_veblen_iff_right).2 zero_le).trans h1
  obtain ⟨u', hu', hu1, hu2⟩ := uaCl_idx ldOm2_SC hQ.1 h hh h0
  have e : u' = u := taIdx_uniq hu1 hu2 h1 h2
  rw [← e]; exact LeCl.phi LeCl.om hu'

/-- **The level of a code above a node inside a window**: a code `h` with `φ(c, y) ≤ h < F_{u+1}`,
`F_u < φ(c, y)`, `c < Ω₂` gives the code `c`. -/
theorem uaCl_levW {u c y : Ordinal.{0}} (hcW : c < Om (1 + 1))
    (hF : veblen (Om (1 + 1)) u < veblen c y) :
    ∀ h, LeCl (Om (1 + 1)) Q h → veblen c y ≤ h → h < veblen (Om (1 + 1)) (u + 1) →
      LeCl (Om (1 + 1)) Q c := by
  intro h hh
  induction hh with
  | @small w hwQ =>
    intro hle _
    exact LeCl.small (((left_le_veblen c y).trans hle).trans_lt hwQ)
  | om =>
    intro hle _
    have h2 : Om (1 + 1) < veblen c y :=
      (ldOm2_SC.veblen_zero.symm.le.trans ((veblen_le_veblen_iff_right).2 zero_le)).trans_lt hF
    exact absurd (h2.trans_le hle) (lt_irrefl _)
  | @add x z _ _ ihx ihz =>
    intro hle hX
    by_cases hx : veblen c y ≤ x
    · exact ihx hx (le_self_add.trans_lt hX)
    by_cases hz : veblen c y ≤ z
    · exact ihz hz (le_add_self.trans_lt hX)
    push Not at hx hz
    exact absurd (Ph.ph_veblen_prin c y hx hz) (not_lt.2 hle)
  | @phi p q hp _ _ ihq =>
    intro hle hX
    rcases lt_trichotomy p c with hpc | rfl | hcp
    · have hq : veblen c y ≤ q := by
        by_contra hc'
        push Not at hc'
        have : veblen p q < veblen c y := by
          calc veblen p q < veblen p (veblen c y) := (veblen_lt_veblen_iff_right).2 hc'
            _ = veblen c y := veblen_veblen_of_lt hpc y
        exact absurd hle (not_le.2 this)
      exact ihq hq ((right_le_veblen p q).trans_lt hX)
    · exact hp
    · have hpW : p < Om (1 + 1) := uaWin_lev (hF.trans_le hle) hX
      exact LeCl.small (hcp.trans (tdCl_lt hQ p hp hpW))

/-- **The own transfer at a successor argument in a window**: a code `h` with `N = φ(a, y') < h ≤ φ(a, y' + 1)`,
`h < F_{u+1}`, `F_u ≤ N`, `a < Ω₂`, gives the code `N`. -/
theorem uaCl_NWin {u a y' h : Ordinal.{0}} (haW : a < Om (1 + 1))
    (hFN : veblen (Om (1 + 1)) u ≤ veblen a y') (hh : LeCl (Om (1 + 1)) Q h) (h1 : veblen a y' < h)
    (h2 : h ≤ veblen a (y' + 1)) (hX : h < veblen (Om (1 + 1)) (u + 1)) : LeCl (Om (1 + 1)) Q (veblen a y') := by
  rcases hFN.lt_or_eq with hlt | heq
  · have hac := uaCl_levW hQ haW hlt h hh h1.le hX
    have h0 : veblen a 0 ≤ h := ((veblen_le_veblen_iff_right).2 zero_le).trans h1.le
    obtain ⟨u', hu, hu1, hu2⟩ := taCl_idx ldOm2_SC haW h hh h0
    have hlo : y' ≤ u' := Order.lt_add_one_iff.1 ((veblen_lt_veblen_iff_right).1 (h1.trans hu2))
    have hhi : u' ≤ y' + 1 := (veblen_le_veblen_iff_right).1 (hu1.trans h2)
    exact LeCl.phi hac (tuCl_of_succ hQ hlo hhi hu)
  · rw [← heq]; exact uaCl_FW hQ hh (heq ▸ h1.le) hX

/-- **The own transfer in the argument in a window**: a code `h` with `φ(a, m) ≤ h ≤ φ(a, z)`, `h < F_{u+1}`,
`F_u < φ(a, m)`, `a < Ω₂`, gives the code `a` and a code `v` with `m ≤ v ≤ z`. -/
theorem uaCl_argW {u a m z h : Ordinal.{0}} (haW : a < Om (1 + 1))
    (hFm : veblen (Om (1 + 1)) u < veblen a m) (hh : LeCl (Om (1 + 1)) Q h) (h1 : veblen a m ≤ h)
    (h2 : h ≤ veblen a z) (hX : h < veblen (Om (1 + 1)) (u + 1)) :
    LeCl (Om (1 + 1)) Q a ∧ ∃ v, LeCl (Om (1 + 1)) Q v ∧ m ≤ v ∧ v ≤ z := by
  have hac := uaCl_levW hQ haW hFm h hh h1 hX
  have h0 : veblen a 0 ≤ h := ((veblen_le_veblen_iff_right).2 zero_le).trans h1
  obtain ⟨u', hu, hu1, hu2⟩ := taCl_idx ldOm2_SC haW h hh h0
  have hlo : m ≤ u' := Order.lt_add_one_iff.1 ((veblen_lt_veblen_iff_right).1 (h1.trans_lt hu2))
  have hhi : u' ≤ z := (veblen_le_veblen_iff_right).1 (hu1.trans h2)
  exact ⟨hac, u', hu, hlo, hhi⟩

/-- **THE LEVEL OF A CODE AT EVERY LEVEL**: a code `h ≥ φ(c, y) > Ω₂` with no fixed point of `φ(c, ·)` in
`[φ(c, y), h]` gives the code `c` (no window, no bound on `c`). -/
theorem uaCl_levG {c y : Ordinal.{0}} (hΩ : Om (1 + 1) < veblen c y) :
    ∀ h, LeCl (Om (1 + 1)) Q h → veblen c y ≤ h → (∀ v, veblen c y ≤ v → v ≤ h → veblen c v ≠ v) →
      LeCl (Om (1 + 1)) Q c := by
  intro h hh
  induction hh with
  | @small w hwQ =>
    intro hle _
    exact LeCl.small (((left_le_veblen c y).trans hle).trans_lt hwQ)
  | om =>
    intro hle _
    exact absurd (hΩ.trans_le hle) (lt_irrefl _)
  | @add x z _ _ ihx ihz =>
    intro hle hnf
    by_cases hx : veblen c y ≤ x
    · exact ihx hx fun v h1 h2 => hnf v h1 (h2.trans le_self_add)
    by_cases hz : veblen c y ≤ z
    · exact ihz hz fun v h1 h2 => hnf v h1 (h2.trans le_add_self)
    push Not at hx hz
    exact absurd (Ph.ph_veblen_prin c y hx hz) (not_lt.2 hle)
  | @phi p q hp _ _ ihq =>
    intro hle hnf
    rcases lt_trichotomy p c with hpc | rfl | hcp
    · have hq : veblen c y ≤ q := by
        by_contra hc'
        push Not at hc'
        have : veblen p q < veblen c y := by
          calc veblen p q < veblen p (veblen c y) := (veblen_lt_veblen_iff_right).2 hc'
            _ = veblen c y := veblen_veblen_of_lt hpc y
        exact absurd hle (not_le.2 this)
      exact ihq hq fun v h1 h2 => hnf v h1 (h2.trans (right_le_veblen p q))
    · exact hp
    · exact absurd (veblen_veblen_of_lt hcp q) (hnf _ hle le_rfl)

omit hQ in
/-- **No fixed point of `φ(a, ·)` lies in `(φ(a, y'), φ(a, y' + 1)]`.** -/
theorem uaNoFix {a y' v : Ordinal.{0}} (h1 : veblen a y' < v) (h2 : v ≤ veblen a (y' + 1)) : veblen a v ≠ v := by
  intro hv
  have hle : v ≤ y' + 1 := by
    have h := h2
    rw [← hv] at h
    exact (veblen_le_veblen_iff_right).1 h
  have hveq : v = y' + 1 := le_antisymm hle (Order.add_one_le_of_lt ((right_le_veblen a y').trans_lt h1))
  have hP : IsPrincipal (· + ·) (y' + 1) := by
    have h := Ph.ph_veblen_prin a (y' + 1)
    rw [← hveq, hv] at h
    rwa [← hveq]
  rcases eq_or_ne y' 0 with rfl | hy0
  · rw [zero_add] at hveq
    rw [hveq] at h1
    exact absurd h1 (not_lt.2 (Order.one_le_iff_pos.2 veblen_pos))
  · exact lt_irrefl _ (hP (lt_add_one y')
      ((lt_add_one (1 : Ordinal.{0})).trans_le (add_le_add (Order.one_le_iff_ne_zero.2 hy0) le_rfl)))

end Code2

end Googology.Trans.PoR.InaccPsi.R2.Ua
