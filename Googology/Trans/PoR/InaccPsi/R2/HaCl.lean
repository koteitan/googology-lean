import Googology.Trans.PoR.InaccPsi.R2.GzLFr

/-!
# HaCl: THE `ζ`-INDEX OF A CODE IN `[Q, ζ⁺(Q))` IS A CODE

A code `y` over a strongly critical `Z ≤ Ω₁` (atoms `{G}`, `G = Γ_{Ω₁+1}`) with `Q ≤ y < evZ(Q)`, where `Q = φ(2, j)`
is a `ζ`-point above `G` that is not a fixed point of `φ(2, ·)`, has the `ζ`-index `j` as a code
(`ha_cl_zj`): in the closure under `+` and `φ`, a value in `[Q, evZ(Q))` comes from a summand or an argument in the
same interval, or from `φ(a, b) = Q` with `a ≥ 2` (then `a = 2`, `b = j`).  With `j = G + 1 + λ` the index `λ` is a
code (`ha_cl_idx`), so its gate lies below `Z` (`ha_cl_gate`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ha

open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **No `ε`-fixed point in `(Q, evZ(Q))`.** -/
theorem ha_fix_eq {Q y : Ordinal.{0}} (hQy : Q ≤ y) (hy : y < evZ Q) (hfix : veblen 1 y = y) : y = Q := by
  rcases hQy.lt_or_eq with h | h
  · exact absurd hy (not_lt.2 (evZ_le h hfix))
  · exact h.symm

/-- **`y + 1` a code ⇒ `y` a code.** -/
theorem ha_cl_succ {Z : Ordinal.{0}} (hZ0 : 0 < Z) {At : Set Ordinal.{0}} (hAt : ∀ s ∈ At, IsSuccLimit s)
    {c : Ordinal.{0}} (hc : GxCl Z At c) : ∀ y, c = y + 1 → GxCl Z At y := by
  induction hc with
  | small h => intro y e; exact GxCl.small ((lt_add_one y).trans (e ▸ h))
  | om =>
    intro y e
    have hl : IsSuccLimit (Om 1) := Br.Om1_eq ▸ gv_Om1_lim
    rw [e, ← Order.succ_eq_add_one] at hl
    exact absurd hl (Order.not_isSuccLimit_succ y)
  | atom h =>
    intro y e
    exact absurd (e ▸ hAt _ h) (by rw [← Order.succ_eq_add_one]; exact Order.not_isSuccLimit_succ y)
  | @add u v hu hv ihu ihv =>
    intro y e
    rcases eq_or_ne v 0 with rfl | hv0
    · rw [add_zero] at e; exact ihu y e
    · rcases zero_or_succ_or_isSuccLimit v with h0 | ⟨v', hv'⟩ | hlim
      · exact absurd h0 hv0
      · rw [← hv', Order.succ_eq_add_one, ← add_assoc] at e
        have e' : u + v' = y := Order.succ_injective (by rw [Order.succ_eq_add_one, Order.succ_eq_add_one]; exact e)
        rw [← e']
        exact GxCl.add hu (ihv v' (by rw [← hv', Order.succ_eq_add_one]))
      · exfalso
        have hl : IsSuccLimit (u + v) := isSuccLimit_add _ hlim
        rw [e, ← Order.succ_eq_add_one] at hl
        exact Order.not_isSuccLimit_succ y hl
  | @phi a b ha hb iha ihb =>
    intro y e
    rcases eq_or_ne (veblen a b) 1 with h1 | h1
    · rw [h1] at e
      have : y = 0 := by
        have e' : (0 : Ordinal.{0}) + 1 = y + 1 := by rw [zero_add]; exact e
        exact (Order.succ_injective (by rw [Order.succ_eq_add_one, Order.succ_eq_add_one]; exact e')).symm
      rw [this]
      exact GxCl.small hZ0
    · exfalso
      obtain ⟨d, hd⟩ := veblen_mem_range_opow a b
      have hd0 : d ≠ 0 := by
        rintro rfl
        exact h1 (by rw [← hd]; exact opow_zero ω)
      have hl : IsSuccLimit (veblen a b) := by rw [← hd]; exact isSuccLimit_opow_left isSuccLimit_omega0 hd0
      rw [e, ← Order.succ_eq_add_one] at hl
      exact Order.not_isSuccLimit_succ y hl

/-- **THE `ζ`-INDEX OF A CODE IN `[Q, evZ(Q))` IS A CODE**, `Q = φ(2, j)`, `j < Q`, `G < Q`. -/
theorem ha_cl_zj {Z j : Ordinal.{0}} (hZ1 : Z ≤ Om 1) (hj : j < veblen 2 j) (hGQ : gcG 0 < veblen 2 j)
    {y : Ordinal.{0}} (hy : GxCl Z {gcG 0} y) (hQy : veblen 2 j ≤ y) (hyZ : y < evZ (veblen 2 j)) :
    GxCl Z {gcG 0} j := by
  set Q := veblen 2 j with hQdef
  have hQE : InE Q := gg_veblen_eps two_ne_zero
  have hQfix : veblen 1 Q = Q := veblen_veblen_of_lt one_lt_two j
  have hOQ : Om 1 < Q := (gcG_Om1_lt 0).trans hGQ
  induction hy with
  | small h => exact absurd (hQy.trans_lt (h.trans_le hZ1)) (not_lt.2 hOQ.le)
  | om => exact absurd hQy (not_le.2 hOQ)
  | atom h =>
    rw [Set.mem_singleton_iff] at h
    rw [h] at hQy; exact absurd hQy (not_le.2 hGQ)
  | @add u v hu hv ihu ihv =>
    rcases le_or_gt Q u with hQu | huQ
    · exact ihu hQu (lt_of_le_of_lt le_self_add hyZ)
    · rcases le_or_gt Q v with hQv | hvQ
      · exact ihv hQv (lt_of_le_of_lt le_add_self hyZ)
      · exact absurd hQy (not_le.2 ((inE_indec hQE).add_lt huQ hvQ))
  | @phi a b ha hb iha ihb =>
    have hbyZ : b < evZ Q := lt_of_le_of_lt (right_le_veblen a b) hyZ
    rcases lt_or_ge a 2 with ha2 | ha2
    · -- `a ∈ {0, 1}`: the argument `b` lies in `[Q, evZ(Q))`
      refine ihb ?_ hbyZ
      refine not_lt.1 fun hbQ => ?_
      have hlt : veblen a b < Q := by
        have h1 : veblen a b < veblen a Q := (isNormal_veblen a).strictMono hbQ
        have h2 : veblen a Q = Q := by
          rcases lt_or_ge a 1 with ha1 | ha1
          · rw [Order.lt_one_iff.1 ha1, veblen_zero_apply]; exact hQE
          · have : a = 1 := le_antisymm (Order.lt_add_one_iff.1 (by rw [one_add_one_eq_two]; exact ha2)) ha1
            rw [this]; exact hQfix
        rwa [h2] at h1
      exact absurd hQy (not_le.2 hlt)
    · -- `a ≥ 2`: `φ(a, b)` is an `ε`-fixed point in `[Q, evZ(Q))`, so it is `Q`
      have hfix : veblen 1 (veblen a b) = veblen a b := veblen_veblen_of_lt (one_lt_two.trans_le ha2) b
      have e := ha_fix_eq hQy hyZ hfix
      rcases ha2.lt_or_eq with ha2' | ha2'
      · exfalso
        have e2 : veblen 2 (veblen a b) = veblen a b := veblen_veblen_of_lt ha2' b
        have : j = veblen a b := by
          have h3 : veblen 2 j = veblen 2 (veblen a b) := by rw [e2, e]
          exact (veblen_inj).1 h3
        rw [this, e] at hj
        exact lt_irrefl _ hj
      · subst ha2'
        have : b = j := (veblen_inj).1 e
        rw [← this]; exact hb

/-- **The `ζ`-index `λ` of a code in `[φ(2, G+1+λ), evZ(φ(2, G+1+λ)))` is a code.** -/
theorem ha_cl_idx {Z l : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1)
    (hj : gcG 0 + 1 + l < veblen 2 (gcG 0 + 1 + l)) {y : Ordinal.{0}} (hy : GxCl Z {gcG 0} y)
    (hQy : veblen 2 (gcG 0 + 1 + l) ≤ y) (hyZ : y < evZ (veblen 2 (gcG 0 + 1 + l))) : GxCl Z {gcG 0} l := by
  have hGQ : gcG 0 < veblen 2 (gcG 0 + 1 + l) := by
    have h := (isNormal_veblen 2).strictMono ((lt_add_one (gcG 0)).trans_le
      (le_self_add : gcG 0 + 1 ≤ gcG 0 + 1 + l))
    rwa [gn_veb_fix (gcG_SC 0) gw_two_lt_G] at h
  have hjc := ha_cl_zj hZ1 hj hGQ hy hQy hyZ
  rw [add_assoc] at hjc
  have h1l := gwY_cl_of_add hZ hZ1 (Low.opow_eq_self_of_SC (gcG_SC 0)) le_rfl (GxCl.atom (Set.mem_singleton _)) hjc
  rcases lt_or_ge l ω with hlω | hlω
  · exact GxCl.small (hlω.trans (omega0_lt_inE (Low.opow_eq_self_of_SC hZ)))
  · rwa [one_add_of_omega0_le hlω] at h1l

/-- **THE CODE-GATE CONDITION OF A `ζ`-INDEX**: a code in `[φ(2, G+1+λ), evZ(φ(2, G+1+λ)))` over a strongly critical
`Z ≤ Ω₁` forces the gate of `λ` (in any system `E` containing `λ`) below `Z`. -/
theorem ha_cl_gate (E : GzVD) {Z l : Ordinal.{0}} (hlB : l < E.B) (hZ : SC Z) (hZ1 : Z ≤ Om 1)
    (hj : gcG 0 + 1 + l < veblen 2 (gcG 0 + 1 + l)) {y : Ordinal.{0}} (hy : GxCl Z {gcG 0} y)
    (hQy : veblen 2 (gcG 0 + 1 + l) ≤ y) (hyZ : y < evZ (veblen 2 (gcG 0 + 1 + l))) : E.g l < Z := by
  have h := ha_cl_idx hZ hZ1 hj hy hQy hyZ
  have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1
  exact E.code_gate Z hZ1' hZ.1 (fun _ _ hu hv => hZ.isPrincipal hu hv) (fun _ _ hu hv => hZ.2 _ hu _ hv)
    {gcG 0} (fun s hs => Or.inl (Set.mem_singleton_iff.1 hs)) l h hlB

end Googology.Trans.PoR.InaccPsi.R2.Ha
