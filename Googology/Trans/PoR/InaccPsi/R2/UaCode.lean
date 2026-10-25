import Googology.Trans.PoR.InaccPsi.R2.UaMS

/-!
# Codes at every level: the index lemma at the level `Ω₂`, and the own transfer above `G`

`φ = veblen`, codes = `Le.LeCl κ Q` (`κ`, `Q` strongly critical), `G = φ(Ω₂, 1)`, `X₂ = Ua.uaX2 = φ(Ω₂, 2)` (the
least fixed point of every `φ(c, ·)`, `c < Ω₂`, above `G`).

* `uaCl_idx` (**THE INDEX OF A CODE IS A CODE AT EVERY LEVEL**: a code `w ≥ φ(a, 0)` lies in
  `[φ(a, u), φ(a, u + 1))` for a code `u`; `Ta.taCl_idx` asked `a < κ`), `uaCl_NW` (**the own transfer at the level
  `κ`**: a code `h` with `φ(κ, b) < h ≤ φ(κ, b + 1)` gives the code `φ(κ, b)`);
* `uaX2`, `uaG_lt_X2`, `uaE_lt_X2`, `uaX2_lt_Gam`, `uaX2_lev` (**every Veblen fixed point in `(G, X₂)` has a level
  below `Ω₂`**);
* `uaCl_levX` (**the level of a code above a node in `(G, X₂)`**), `uaCl_NX` (the own transfer at a successor
  argument), `uaCl_argX` (the own transfer in the argument): `Tx.txCl_lev`, `Tx.txCl_N`, `Tx.txCl_arg` for the
  nodes `G < φ(a, y) < X₂`.

No new axiom.  New definition: `uaX2`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ua

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td
  Googology.Trans.PoR.InaccPsi.R2.Tg Googology.Trans.PoR.InaccPsi.R2.Tu Googology.Trans.PoR.InaccPsi.R2.Tx

variable {S : InaccSeq.{0}}

section Code

variable {κ Q : Ordinal.{0}} (hQ : SC Q) (hκ : SC κ)

include hκ in
/-- **THE INDEX OF A CODE IS A CODE AT EVERY LEVEL `a`.** -/
theorem uaCl_idx {a : Ordinal.{0}} (hQ0 : 0 < Q) :
    ∀ w, LeCl κ Q w → veblen a 0 ≤ w → ∃ u, LeCl κ Q u ∧ veblen a u ≤ w ∧ w < veblen a (u + 1) := by
  rcases lt_or_ge a κ with haκ | hκa
  · exact taCl_idx hκ haκ
  intro w hw
  induction hw with
  | @small w hwQ =>
    intro h0
    obtain ⟨u, h1, h2⟩ := taIdx_ex h0
    exact ⟨u, LeCl.small (((right_le_veblen a u).trans h1).trans_lt hwQ), h1, h2⟩
  | om =>
    intro h0
    have haκ' : a = κ := le_antisymm ((left_le_veblen a 0).trans h0) hκa
    subst haκ'
    refine ⟨0, LeCl.zero hQ0, hκ.veblen_zero.le, ?_⟩
    calc a = veblen a 0 := hκ.veblen_zero.symm
      _ < veblen a (0 + 1) := (veblen_lt_veblen_iff_right).2 (by rw [zero_add]; exact zero_lt_one)
  | @add x y hx hy ihx ihy =>
    intro h0
    have hP := Ph.ph_veblen_prin a 0
    by_cases hxa : veblen a 0 ≤ x
    · obtain ⟨u1, hc1, hu1, hx1⟩ := ihx hxa
      by_cases hya : veblen a 0 ≤ y
      · obtain ⟨u2, hc2, hu2, hy2⟩ := ihy hya
        refine ⟨max u1 u2, ?_, ?_, Ph.ph_veblen_prin a _ (hx1.trans_le ?_) (hy2.trans_le ?_)⟩
        · rcases le_total u1 u2 with h | h
          · rw [max_eq_right h]; exact hc2
          · rw [max_eq_left h]; exact hc1
        · rcases le_total u1 u2 with h | h
          · rw [max_eq_right h]; exact hu2.trans le_add_self
          · rw [max_eq_left h]; exact hu1.trans le_self_add
        · exact (veblen_le_veblen_iff_right).2 (add_le_add (le_max_left _ _) le_rfl)
        · exact (veblen_le_veblen_iff_right).2 (add_le_add (le_max_right _ _) le_rfl)
      · push Not at hya
        refine ⟨u1, hc1, hu1.trans le_self_add, Ph.ph_veblen_prin a _ hx1 (hya.trans_le ?_)⟩
        exact (veblen_le_veblen_iff_right).2 zero_le
    · push Not at hxa
      by_cases hya : veblen a 0 ≤ y
      · obtain ⟨u2, hc2, hu2, hy2⟩ := ihy hya
        refine ⟨u2, hc2, hu2.trans le_add_self, Ph.ph_veblen_prin a _ (hxa.trans_le ?_) hy2⟩
        exact (veblen_le_veblen_iff_right).2 zero_le
      · push Not at hya
        exact absurd h0 (not_le.2 (hP hxa hya))
  | @phi p q hp hq _ ihq =>
    intro h0
    rcases lt_trichotomy p a with hpa | rfl | hpa
    · have hq0 : veblen a 0 ≤ q := by
        by_contra hq'
        push Not at hq'
        have : veblen p q < veblen a 0 := by
          calc veblen p q < veblen p (veblen a 0) := (veblen_lt_veblen_iff_right).2 hq'
            _ = veblen a 0 := veblen_veblen_of_lt hpa 0
        exact absurd h0 (not_le.2 this)
      obtain ⟨u, hu, h1, h2⟩ := ihq hq0
      refine ⟨u, hu, h1.trans (right_le_veblen p q), ?_⟩
      calc veblen p q < veblen p (veblen a (u + 1)) := (veblen_lt_veblen_iff_right).2 h2
        _ = veblen a (u + 1) := veblen_veblen_of_lt hpa _
    · exact ⟨q, hq, le_rfl, (veblen_lt_veblen_iff_right).2 (lt_add_one q)⟩
    · have hfix : veblen a (veblen p q) = veblen p q := veblen_veblen_of_lt hpa q
      refine ⟨veblen p q, LeCl.phi hp hq, hfix.le, ?_⟩
      calc veblen p q = veblen a (veblen p q) := hfix.symm
        _ < veblen a (veblen p q + 1) := (veblen_lt_veblen_iff_right).2 (lt_add_one _)

include hQ hκ in
/-- **The own transfer at the level `κ`**: a code `h` with `φ(κ, b) < h ≤ φ(κ, b + 1)` gives the code `φ(κ, b)`. -/
theorem uaCl_NW {b h : Ordinal.{0}} (hh : LeCl κ Q h) (h1 : veblen κ b < h) (h2 : h ≤ veblen κ (b + 1)) :
    LeCl κ Q (veblen κ b) := by
  have h0 : veblen κ 0 ≤ h := ((veblen_le_veblen_iff_right).2 zero_le).trans h1.le
  obtain ⟨u, hu, hu1, hu2⟩ := uaCl_idx hκ hQ.1 h hh h0
  have hbu : b ≤ u := Order.lt_add_one_iff.1 ((veblen_lt_veblen_iff_right).1 (h1.trans hu2))
  have hhi : u ≤ b + 1 := (veblen_le_veblen_iff_right).1 (hu1.trans h2)
  refine LeCl.phi LeCl.om ?_
  rcases hbu.lt_or_eq with hlt | heq
  · have hu' : u = b + 1 := le_antisymm hhi (Order.add_one_le_of_lt hlt)
    rw [hu'] at hu
    exact tuCl_pred hQ hκ hu
  · rw [heq]; exact hu

end Code

/-- **The bound `X₂ = φ(Ω₂, 2)`.** -/
noncomputable def uaX2 : Ordinal.{0} := veblen (Om (1 + 1)) (1 + 1)

theorem uaG_lt_X2 : veblen (Om (1 + 1 : Ordinal.{0})) 1 < uaX2 :=
  (veblen_lt_veblen_iff_right).2 (lt_add_one 1)

theorem uaX2_lim : IsSuccLimit (uaX2 : Ordinal.{0}) := taVeb_lim ldOm2_SC.1.ne'

theorem uaX2_lt_Gam : uaX2 < uaGam :=
  uaGam_spec.1.2 _ uaGam_spec.2 _ (uaGam_spec.1.isSuccLimit.add_one_lt (gg_one_lt_of_SC uaGam_spec.1))

theorem uaX2_lt_G3 : uaX2 < S.psi 0 (Om (1 + 1 + 1)) := uaX2_lt_Gam.trans_le uaGam_le_G3

/-- `X₂` is a fixed point of every `φ(c, ·)`, `c < Ω₂`. -/
theorem uaX2_fix {c : Ordinal.{0}} (hc : c < Om (1 + 1)) : veblen c uaX2 = uaX2 := veblen_veblen_of_lt hc _

theorem uaE_lt_X2 : uaE < uaX2 := by
  unfold uaE
  rw [← uaX2_fix (gg_one_lt_of_SC ldOm2_SC)]
  exact (veblen_lt_veblen_iff_right).2 (uaX2_lim.add_one_lt uaG_lt_X2)

/-- **Every `φ(p, q)` in `(G, X₂)` has `p < Ω₂`.** -/
theorem uaX2_lev {p q : Ordinal.{0}} (hG : veblen (Om (1 + 1)) 1 < veblen p q) (hX : veblen p q < uaX2) :
    p < Om (1 + 1) := by
  rcases veblen_lt_veblen_iff.1 hX with ⟨hpe, hq⟩ | ⟨hlt, _⟩ | ⟨_, h2⟩
  · exfalso
    rw [hpe] at hG
    have hq1 : q ≤ 1 := Order.lt_add_one_iff.1 hq
    exact absurd ((veblen_le_veblen_iff_right).2 hq1) (not_le.2 hG)
  · exact hlt
  · exfalso
    have h3 : (1 + 1 : Ordinal.{0}) < veblen p q :=
      ((ldOm2_SC.isSuccLimit.add_one_lt (gg_one_lt_of_SC ldOm2_SC)).trans tgOm_lt_G).trans hG
    exact absurd h2 (not_lt.2 h3.le)

section Code2

variable {Q : Ordinal.{0}} (hQ : SC Q)

include hQ

/-- **The level of a code above a node in `(G, X₂)`**: a code `h` with `φ(c, y) ≤ h < X₂`, `G < φ(c, y)`,
`c < Ω₂` gives the code `c`. -/
theorem uaCl_levX {c y : Ordinal.{0}} (hcW : c < Om (1 + 1)) (hG : veblen (Om (1 + 1)) 1 < veblen c y) :
    ∀ h, LeCl (Om (1 + 1)) Q h → veblen c y ≤ h → h < uaX2 → LeCl (Om (1 + 1)) Q c := by
  intro h hh
  induction hh with
  | @small w hwQ =>
    intro hle _
    exact LeCl.small (((left_le_veblen c y).trans hle).trans_lt hwQ)
  | om =>
    intro hle _
    exact absurd ((tgOm_lt_G.trans hG).trans_le hle) (lt_irrefl _)
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
    · have hpW : p < Om (1 + 1) := uaX2_lev (hG.trans_le hle) hX
      exact LeCl.small (hcp.trans (tdCl_lt hQ p hp hpW))

/-- **The own transfer at a successor argument**: a code `h` with `N = φ(a, y') < h ≤ φ(a, y' + 1) < X₂`,
`G < N`, `a < Ω₂`, gives the code `N`. -/
theorem uaCl_NX {a y' h : Ordinal.{0}} (haW : a < Om (1 + 1)) (hGN : veblen (Om (1 + 1)) 1 < veblen a y')
    (hh : LeCl (Om (1 + 1)) Q h) (h1 : veblen a y' < h) (h2 : h ≤ veblen a (y' + 1)) (hX : h < uaX2) :
    LeCl (Om (1 + 1)) Q (veblen a y') := by
  have hac := uaCl_levX hQ haW hGN h hh h1.le hX
  have h0 : veblen a 0 ≤ h := ((veblen_le_veblen_iff_right).2 zero_le).trans h1.le
  obtain ⟨u, hu, hu1, hu2⟩ := taCl_idx ldOm2_SC haW h hh h0
  have hlo : y' ≤ u := Order.lt_add_one_iff.1 ((veblen_lt_veblen_iff_right).1 (h1.trans hu2))
  have hhi : u ≤ y' + 1 := (veblen_le_veblen_iff_right).1 (hu1.trans h2)
  exact LeCl.phi hac (tuCl_of_succ hQ hlo hhi hu)

/-- **The own transfer in the argument**: a code `h` with `φ(a, m) ≤ h ≤ φ(a, z)`, `G < φ(a, m)`, `h < X₂`,
`a < Ω₂`, gives the code `a` and a code `v` with `m ≤ v ≤ z`. -/
theorem uaCl_argX {a m z h : Ordinal.{0}} (haW : a < Om (1 + 1)) (hGm : veblen (Om (1 + 1)) 1 < veblen a m)
    (hh : LeCl (Om (1 + 1)) Q h) (h1 : veblen a m ≤ h) (h2 : h ≤ veblen a z) (hX : h < uaX2) :
    LeCl (Om (1 + 1)) Q a ∧ ∃ v, LeCl (Om (1 + 1)) Q v ∧ m ≤ v ∧ v ≤ z := by
  have hac := uaCl_levX hQ haW hGm h hh h1 hX
  have h0 : veblen a 0 ≤ h := ((veblen_le_veblen_iff_right).2 zero_le).trans h1
  obtain ⟨u, hu, hu1, hu2⟩ := taCl_idx ldOm2_SC haW h hh h0
  have hlo : m ≤ u := Order.lt_add_one_iff.1 ((veblen_lt_veblen_iff_right).1 (h1.trans_lt hu2))
  have hhi : u ≤ z := (veblen_le_veblen_iff_right).1 (hu1.trans h2)
  exact ⟨hac, u, hu, hlo, hhi⟩

end Code2

end Googology.Trans.PoR.InaccPsi.R2.Ua
