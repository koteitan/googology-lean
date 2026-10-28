import Googology.Trans.PoR.InaccPsi.R2.VhAdd

/-!
# `T = Ug.ugTh` on all of `D ∩ Y₃`

`T = Vb.vbT S λ` (the image one level down, the inverse of the level shift), `Ug.ugTh S λ` (the image past `Γ₂`),
`D = Vb.VbD S λ`, `Y₃ = ψ_{Ω₃}(Ω₃)` (`Ug.ugY`), `Γ₂ = ψ_{Ω₃}(0)` (`Ua.uaGam`), `G = φ(Ω₂, 1)`,
`Θ = gxTh ρ_λ (ldAtR λ)`, `W^g = Ω₂^g`, `Ω^g = Ω₁^g`.

* `vhOm2_veb0` (`φ(Ω₂, 0) = Ω₂`), `vhWfix` (**a `W`-fixed `x > 0` is an `ε`-number above `Ω₂`**),
  `vhNodeLow` (**a node `x = φ(a, b)` with `Ω₂ < x < G` has `1 ≤ a < Ω₂` and `Ω₂ ≤ b`**);
* `vhT_ug` (**`T x = ugTh x` for every `x ∈ D` with `x < Y₃`**): one induction on the recursion of `ugTh` —
  `W`-normal form `T(W^g·d + r) = Ω^{T g}·Θ d + T r` (`Vh.vhT_cnfW`), `ψ₃`-atoms `T ψ₃(d) = ψ₂(T d)`
  (`Vb.vbT_atom`), nodes `T φ(a, b) = φ(T a, T b)` (`Vb.vbT_veb`) against the clauses of `ugTh`, `uaTh`
  (`Ua.uaVeb`) and `tdThL` (`Tx.txVeb`, `T(Ω₂ + z) = Ω₁ + T z`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rx
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Ua

variable {S : InaccSeq.{0}}

/-- `φ(Ω₂, 0) = Ω₂`. -/
theorem vhOm2_veb0 : veblen (Om (1 + 1 : Ordinal.{0})) 0 = Om (1 + 1) := by
  have hε : ω ^ Om (1 + 1 : Ordinal.{0}) = Om (1 + 1) := gg_SC_eps ldOm2_SC
  have hv : veblen (invVeblen₁ (Om (1 + 1 : Ordinal.{0}))) (invVeblen₂ (Om (1 + 1))) = Om (1 + 1) := by
    rw [veblen_invVeblen₁_invVeblen₂, hε]
  have hb : invVeblen₂ (Om (1 + 1 : Ordinal.{0})) < Om (1 + 1) := by
    have := invVeblen₂_lt (Om (1 + 1 : Ordinal.{0})); rwa [hε] at this
  obtain ⟨e1, e2⟩ := rxSC_veb ldOm2_SC hv hb
  rw [e1, e2] at hv; exact hv

/-- **A `W`-fixed `x > 0` is an `ε`-number above `Ω₂`.** -/
theorem vhWfix {x : Ordinal.{0}} (h0 : 0 < x) (hsx : sgLW x = x) : ω ^ x = x ∧ Om (1 + 1) < x := by
  have hlog : log ω x = x := by
    refine le_antisymm (log_le_self ω x) ?_
    calc x = sgLW x := hsx.symm
      _ ≤ log ω x := Ordinal.div_le_of_le_mul (Ordinal.le_mul_right _ ldOm2_SC.1)
  have hε : ω ^ x = x := by
    refine le_antisymm ?_ (right_le_opow x one_lt_omega0)
    calc ω ^ x = ω ^ log ω x := by rw [hlog]
      _ ≤ x := opow_log_le_self ω h0.ne'
  refine ⟨hε, ?_⟩
  have hs : x / Om (1 + 1) = x := by
    have : sgLW x = log ω x / Om (1 + 1) := rfl
    rw [hlog] at this; rw [← this]; exact hsx
  by_contra hc
  push Not at hc
  rcases hc.lt_or_eq with h | h
  · rw [Ordinal.div_eq_zero_of_lt h] at hs; exact h0.ne' hs.symm
  · rw [h, Ordinal.div_self ldOm2_SC.1.ne'] at hs
    exact absurd hs (ne_of_lt (gg_one_lt_of_SC ldOm2_SC))

/-- **A node below `G = φ(Ω₂, 1)`**: `x = φ(a, b)` with `Ω₂ < x < G`, `b < x` has `1 ≤ a < Ω₂` and `Ω₂ ≤ b`. -/
theorem vhNodeLow {x a b : Ordinal.{0}} (hv : veblen a b = x) (ha0 : 0 < a) (h2 : Om (1 + 1) < x)
    (hG : x < veblen (Om (1 + 1)) 1) : 1 ≤ a ∧ a < Om (1 + 1) ∧ Om (1 + 1) ≤ b := by
  have haW : a < Om (1 + 1) := by
    by_contra hc
    push Not at hc
    rcases hc.lt_or_eq with h | h
    · have h1 : (1 : Ordinal.{0}) < veblen a 0 :=
        (gg_one_lt_of_SC ldOm2_SC).trans (h.trans_le (left_le_veblen a 0))
      have h3 : veblen (Om (1 + 1)) 1 < veblen a 0 := by
        calc veblen (Om (1 + 1)) 1 < veblen (Om (1 + 1)) (veblen a 0) := veblen_lt_veblen_iff_right.2 h1
          _ = veblen a 0 := veblen_veblen_of_lt h 0
      exact absurd (h3.trans_le ((veblen_le_veblen_iff_right.2 zero_le).trans hv.le)) (not_lt.2 hG.le)
    · subst h
      rcases eq_or_ne b 0 with rfl | hb0
      · rw [vhOm2_veb0] at hv; exact absurd hv (ne_of_lt h2)
      · have : veblen (Om (1 + 1)) 1 ≤ x :=
          hv ▸ veblen_le_veblen_iff_right.2 (Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 hb0))
        exact absurd this (not_le.2 hG)
  refine ⟨Order.one_le_iff_pos.2 ha0, haW, ?_⟩
  by_contra hc
  push Not at hc
  exact absurd (hv ▸ ldOm2_SC.2 a haW b hc) (not_lt.2 h2.le)

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

theorem vhT_zero : vbT S l 0 = 0 := by
  have h := vbT_K hl hX (rxE_zero (S := S) (T := vbW S l))
  rwa [vhK_zero hl hX] at h

/-- **`T = ugTh` on `D ∩ Y₃`**: `T x = ugTh x` for every `x ∈ D` with `x < Y₃`. -/
theorem vhT_ug : ∀ x, VbD S l x → x < ugY S → vbT S l x = ugTh S l x := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx hxY
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [ugTh_zero, vhT_zero hl hX]
  have h0 : 0 < x := pos_iff_ne_zero.2 hx0
  obtain ⟨-, -, hdC, -, hdW, -, hrlt, hxeq, hT, hor⟩ := ugParts hl hX hx.1 h0 hxY
  rcases hor with hs | ⟨hsx, -, -⟩
  · -- the `W`-normal form
    obtain ⟨hgD, hrD⟩ := vhD_parts hl hX hx h0
    have hrx : x % leWe (sgLW x) < x := hrlt.trans_le (sgLW_le h0)
    have hdH : x / leWe (sgLW x) ∈ cdHull S l := (ldHull_iff hl hX hdW).2 hdC
    rw [hT, ← IH _ hs hgD (hs.trans hxY), ← IH _ hrx hrD (hrx.trans hxY)]
    calc vbT S l x = vbT S l (leWe (sgLW x) * (x / leWe (sgLW x)) + x % leWe (sgLW x)) :=
          congrArg (vbT S l) hxeq
      _ = _ := vhT_cnfW hl hX hgD hrD hdH hdW
  -- a `W`-fixed point
  obtain ⟨hε, h2⟩ := vhWfix h0 hsx
  have hns : ¬ sgLW x < x := by rw [hsx]; exact lt_irrefl _
  have hE3 : x < Om (1 + 1 + 1) := hxY.trans ugY_lt_Om3
  by_cases hS : SC x
  · -- a `ψ₃`-atom
    obtain ⟨d, -, hd, hdn, hxd⟩ := ugAtomH hl hX hx.1 hS h2 hxY
    have h1 : Om 1 < x := (Om_lt_Om.2 (lt_add_one 1)).trans h2
    have hne : ¬ ∃ k : ℕ, x = Om (k : Ordinal.{0}) := fun ⟨k, hk⟩ => not_Om_of_between h2 hE3 _ hk
    obtain ⟨k, hk, d', hd'E, hd'n, hxd', -⟩ := rxE_atom (vbZ hl hX).2.le (vbD_E hl hX hx) hS h1 hne
    have hd'D : VbD S l d' := vbD_atom hl hX (hxd' ▸ hx) hd'E hd'n hk
    have hk2 : (k : Ordinal.{0}) = 1 + 1 := by
      have hb := psiS_bounds (S := S) d' (k : Ordinal.{0})
      rw [← hxd'] at hb
      exact between_unique hb.1 hb.2 h2 hE3
    rw [hk2] at hxd' hd'n
    have hdd : d' = d := by
      have e1 := rxDn_eq ugInR3 hd'n
      have e2 := rxDn_eq ugInR3 hdn
      rw [← hxd', ← hxd] at e1
      exact e1.symm.trans e2
    rw [hdd] at hd'D
    have hdx : d < x := hxd ▸ hd
    have hA := (vbT_atom hl hX (k := 1) le_rfl hd'D (by rw [Nat.cast_one]; exact hdn)).1
    rw [Nat.cast_one] at hA
    rw [← hxd, hA, ugTh_atom hd, IH d hdx hd'D (hdx.trans hxY)]
  -- a node `x = φ(a, b)`
  have hv : veblen (invVeblen₁ x) (invVeblen₂ x) = x := by rw [veblen_invVeblen₁_invVeblen₂, hε]
  have hb : invVeblen₂ x < x := by have := invVeblen₂_lt x; rwa [hε] at this
  have ha0 : 0 < invVeblen₁ x := by
    refine pos_iff_ne_zero.2 fun h => ?_
    rw [h, veblen_zero_apply] at hv
    have : invVeblen₂ x = x := (opow_right_inj one_lt_omega0).1 (hv.trans hε.symm)
    exact absurd this hb.ne
  have ha : invVeblen₁ x < x := by
    refine lt_of_le_of_ne (invVeblen₁_le x) fun e => ?_
    rw [e] at hv
    have hle : veblen x 0 ≤ x := (veblen_le_veblen_iff_right.2 zero_le).trans hv.le
    exact hS (Ru.ruSC_of_veblen h0 (le_antisymm hle (left_le_veblen x 0)))
  obtain ⟨haD, hbD, -⟩ := vbD_veb hx (vbD_E hl hX hx) hv hb
  have hTx : vbT S l x = veblen (vbT S l (invVeblen₁ x)) (vbT S l (invVeblen₂ x)) :=
    vbT_veb hl hX hx hv ha0.ne' hb h2.le
  rcases le_or_gt uaGam x with hG2 | hG2
  · rw [hTx, ugTh_node hG2 hns hS ⟨ha, hb⟩, IH _ ha haD (ha.trans hxY), IH _ hb hbD (hb.trans hxY)]
  rcases le_or_gt (veblen (Om (1 + 1)) 1) x with hG | hG
  · have hU := uaVeb hl hX haD.1 hbD.1 ha0.ne' (hv.symm ▸ hG) (hv.symm ▸ hG2)
    rw [hv] at hU
    rw [hTx, ugTh_lt hG2, hU, IH _ ha haD (ha.trans hxY), IH _ hb hbD (hb.trans hxY),
      ugTh_lt (ha.trans hG2), ugTh_lt (hb.trans hG2)]
  -- below `G`: `x = φ(a, Ω₂ + z)` with a code `a`
  obtain ⟨h1a, haW, hΩb⟩ := vhNodeLow hv ha0 h2 hG
  have hΩD := vhD_Om2 (S := S) (l := l)
  set z := invVeblen₂ x - Om (1 + 1) with hz
  have hbz : invVeblen₂ x = Om (1 + 1) + z := (Ordinal.add_sub_cancel_of_le hΩb).symm
  have hzD : VbD S l z :=
    ⟨(rxCDec _ hbD.1).1 _ hΩD.1 hΩb, (rxCDec _ hbD.2.1).1 _ hΩD.2.1 hΩb,
      (Ordinal.sub_le_self _ _).trans_lt hbD.2.2⟩
  have hzx : z < x := ((Ordinal.sub_le_self _ _).trans_lt hb)
  have hxz : veblen (invVeblen₁ x) (Om (1 + 1) + z) = x := by rw [← hbz]; exact hv
  have hTd := Tx.txVeb hl hX haD.1 h1a haW hzD.1 (hxz.symm ▸ hG)
  rw [hxz] at hTd
  have hTb : vbT S l (invVeblen₂ x) = Om 1 + vbT S l z := by
    rw [hbz, vhT_add hl hX hΩD hzD]
    have h := vbT_Om hl hX (k := 1) le_rfl
    rw [Nat.cast_one] at h
    rw [h]
  rw [hTx, ugTh_lt hG2, uaTh_lt hG, hTd, hTb, vbT_code hl hX haW haD.1, IH z hzx hzD (hzx.trans hxY),
    ugTh_lt (hzx.trans hG2), uaTh_lt (hzx.trans hG)]

end Rst

end Googology.Trans.PoR.InaccPsi.R2.Vh
