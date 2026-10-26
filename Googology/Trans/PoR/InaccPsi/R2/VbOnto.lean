import Googology.Trans.PoR.InaccPsi.R2.VbBack

/-!
# Every member of the domain is a value of the level shift

`ρ_λ = υ_λ`, `H_λ = cdHull S λ`, `κ_λ = vbK S λ`, `W_λ = vbW S λ`, `VbD S λ` the domain of the image (`VbDef`),
`T = vbT S λ`.

* `vbMulNat_lt` (an additively principal `P > 0` is closed under `x ↦ x·n`);
* `vbLow` (**a value `≥ Ω₂` of `κ_λ` comes from a member `≥ Ω₁`**);
* `vbOnto` (**THE ONTO THEOREM, generic in the level**): at a restart index `λ` with `ρ_λ < P(η_x)`, every
  `x ∈ VbD S λ` is `κ_λ(y)` for a member `y` of the domain of `κ_λ`.  One induction on the measure of `x` in the
  normal hull over `ρ_λ`: codes `x < Ω₂` are `κ_λ(Θ x)`; `Ω_{j+1} = κ_λ(Ω_j)`; Cantor and Veblen normal forms from the
  parts; an atom `x = ψ_{Ω_{k+2}}(d)`, `k ≥ 1`, with a normal argument `d = κ_λ(y_d)` is `κ_λ(ψ_{Ω_{k+1}}(y_d))`, since
  `y_d` is a normal argument for `ψ_{Ω_{k+1}}` by the backward transfer `vbBack`;
* `vbT_eq` (**`κ_λ(T x) = x` and `T x` is a member** for every `x ∈ VbD S λ`).

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

theorem vbMulNat_lt {P x : Ordinal.{0}} (hP : IsPrincipal (· + ·) P) (hP0 : 0 < P) (hx : x < P) :
    ∀ n : ℕ, x * n < P
  | 0 => by rw [Nat.cast_zero, mul_zero]; exact hP0
  | n + 1 => by rw [Nat.cast_succ, mul_add_one]; exact hP (vbMulNat_lt hP hP0 hx n) hx

theorem vbOmW_SC : SC (Om ω : Ordinal.{0}) := SC_Om omega0_ne_zero

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **A value `≥ Ω₂` of `κ_λ` comes from a member `≥ Ω₁`.** -/
theorem vbLow {u v : Ordinal.{0}} (hu : RxE S (vbW S l) u) (huv : vbK S l u = v) (hv2 : Om (1 + 1) ≤ v) :
    Om 1 ≤ u := by
  by_contra hc
  push Not at hc
  obtain ⟨e, h2, -⟩ := rxL_small (vbZ hl hX).1 (vbZ hl hX).2 (ldAt_GxAt _ _) hu hc
  have h3 : ruInv (upsilon l) (ldAtR S l) u = v := e.symm.trans huv
  rw [← h3] at hv2
  exact absurd h2 (not_lt.2 hv2)

/-- **THE ONTO THEOREM**: every member of `VbD S λ` is a value of `κ_λ`. -/
theorem vbOnto : ∀ x, VbD S l x → ∃ y, RxE S (vbW S l) y ∧ vbK S l y = x := by
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  refine rxMs_ind (S := S) (T := upsilon l) fun x IH hx => ?_
  have hxE : RxE S (upsilon l) x := vbD_E hl hX hx
  rcases lt_or_ge x (Om (1 + 1)) with h2 | h2
  · exact ⟨_, vbCode_K hl hX h2 hx.1⟩
  by_cases hΩ : ∃ j : ℕ, x = Om (j : Ordinal.{0})
  · obtain ⟨j, rfl⟩ := hΩ
    have hj : 2 ≤ j := by
      have h := Om_le_Om.1 h2
      rw [one_add_one_eq_two] at h
      have h' : ((2 : ℕ) : Ordinal.{0}) ≤ j := by rw [Nat.cast_ofNat]; exact h
      exact_mod_cast h'
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    refine ⟨Om (i : Ordinal.{0}), ⟨RxN.om (rxN_nat i), rxC_Om_nat _ _ i, Om_lt_Om.2 (natCast_lt_omega0 i)⟩, ?_⟩
    show rxL S (upsilon l) (ldAtR S l) (vbW S l) (Om (i : Ordinal.{0})) = Om ((i + 1 : ℕ) : Ordinal.{0})
    rw [rxL_Om (by omega : 1 ≤ i), Nat.cast_succ]
  have hx2 : Om (1 + 1) < x := lt_of_le_of_ne h2 (fun e => hΩ ⟨2, by rw [← e]; norm_num⟩)
  have hx1 : Om 1 < x := (Om_lt_Om.2 (lt_add_one 1)).trans hx2
  have h0 : x ≠ 0 := ((Om_pos one_ne_zero).trans hx1).ne'
  by_cases hS : SC x
  · obtain ⟨k, hk, d, hdE, hdn, rfl, hst⟩ := rxE_atom hZ1.le hxE hS hx1 hΩ
    have hk2 : 2 ≤ k := by
      by_contra hc
      have hk1 : k = 1 := by omega
      subst hk1
      have := (psiS_bounds (S := S) d ((1 : ℕ) : Ordinal.{0})).2
      rw [Nat.cast_one] at this hx2
      exact absurd (hx2.trans this) (lt_irrefl _)
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hk' : 1 ≤ k' := by omega
    have hdD : VbD S l d := vbD_atom hl hX hx hdE hdn hk
    obtain ⟨yd, hydE, hyd⟩ := IH d (rxMs_lt_stage (rxE_lt_Lam hdE) hst) hdD
    have hdn' : d ∈ S.CSet d (S.psi d (Om ((k' : Ordinal.{0}) + 1 + 1))) := by
      have e : ((k' + 1 : ℕ) : Ordinal.{0}) = (k' : Ordinal.{0}) + 1 := Nat.cast_succ k'
      rw [e] at hdn; exact hdn
    have hnyd := vbBack hZ hZ1 hAt hk' hydE hyd hdn'
    refine ⟨S.psi yd (Om ((k' : Ordinal.{0}) + 1)), rxE_psi hk' hydE hnyd, ?_⟩
    show rxL S (upsilon l) (ldAtR S l) (vbW S l) _ = _
    rw [(rxL_psiE hk' hydE hnyd).1]
    show S.psi (vbK S l yd) _ = _
    rw [hyd, Nat.cast_succ]
  by_cases hε : ω ^ x = x
  · obtain ⟨hv, ha0, ha, hb⟩ := rxVeb hx1 hε hS
    obtain ⟨haD, hbD, -, -, hha, hhb⟩ := vbD_veb hx hxE hv hb
    obtain ⟨ya, hyaE, hya⟩ := IH _ (rxMs_lt_val hha ha) haD
    obtain ⟨yb, hybE, hyb⟩ := IH _ (rxMs_lt_val hhb hb) hbD
    have hya0 : ya ≠ 0 := fun h => by
      rw [h] at hya
      have e0 : vbK S l 0 = 0 := rxL_zero hZ
      rw [e0] at hya
      exact ha0.ne hya
    have hab2 : Om (1 + 1) ≤ invVeblen₁ x ∨ Om (1 + 1) ≤ invVeblen₂ x := by
      by_contra hc
      push Not at hc
      have h' : veblen (invVeblen₁ x) (invVeblen₂ x) < Om (1 + 1) := ldOm2_SC.2 _ hc.1 _ hc.2
      rw [hv] at h'
      exact absurd (hx2.trans h') (lt_irrefl _)
    set y := veblen ya yb with hydef
    have hy1 : Om 1 ≤ y := by
      rcases hab2 with h | h
      · exact (vbLow hl hX hyaE hya h).trans (left_le_veblen ya yb)
      · exact (vbLow hl hX hybE hyb h).trans (right_le_veblen ya yb)
    have hyε : ω ^ y = y := gg_veblen_eps hya0
    have hyE : RxE S (vbW S l) y :=
      ⟨RxN.phi hyaE.1 hybE.1, CSet.phi_mem hyaE.2.1 hybE.2.1, vbOmW_SC.2 _ hyaE.2.2 _ hybE.2.2⟩
    obtain ⟨a', b', hv', hb', -, ha'E, -, hκy, -, -, -⟩ := rxLDecV hZ hyE hy1 hyε
    rw [hydef] at hv'
    rcases veblen_eq_veblen_iff.1 hv' with ⟨e1, e2⟩ | ⟨-, e2⟩ | ⟨h3, e3⟩
    · refine ⟨y, hyE, ?_⟩
      show rxL S (upsilon l) (ldAtR S l) (vbW S l) y = x
      rw [hκy, e1, e2]
      show veblen (vbK S l ya) (vbK S l yb) = x
      rw [hya, hyb, hv]
    · exact absurd hb' (by rw [e2, ← hydef]; exact lt_irrefl _)
    · exfalso
      have hyb' : yb = y := e3.symm.trans (hv'.trans hydef.symm)
      have hbκ : invVeblen₂ x = veblen (vbK S l a') (vbK S l b') := by
        rw [← hyb, hyb']; exact hκy
      have hlt : invVeblen₁ x < vbK S l a' := by rw [← hya]; exact vbK_mono hl hX hyaE ha'E h3
      have h4 := veblen_veblen_of_lt hlt (vbK S l b')
      rw [← hbκ, hv] at h4
      exact lt_irrefl x (h4.trans_lt hb)
  -- the Cantor normal form
  have hlx : log ω x < x := ruLog_lt hx1 hε
  obtain ⟨hlD, -, hlh⟩ := vbD_log hx hxE
  obtain ⟨hrD, -, hrh⟩ := vbD_rem hx hxE
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
  have hpos : (0 : Ordinal.{0}) < ω ^ log ω x := opow_pos _ omega0_pos
  have hdm : x = ω ^ log ω x * n + x % ω ^ log ω x := by
    rw [← hn]; exact (Ordinal.div_add_mod x _).symm
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      have hlt : x < ω ^ log ω x * 1 :=
        (Ordinal.lt_mul_iff_div_lt hpos.ne').2 (by rw [hn, h]; exact zero_lt_one)
      rw [mul_one] at hlt
      exact absurd (opow_log_le_self ω h0) (not_le.2 hlt)
    · exact h
  have hn0 : (n : Ordinal.{0}) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  obtain ⟨yl, hylE, hyl⟩ := IH _ (rxMs_lt_val hlh hlx) hlD
  obtain ⟨yr, hyrE, hyr⟩ := IH _ (rxMs_lt_val hrh (mod_opow_log_lt_self ω h0)) hrD
  have hl2 : Om (1 + 1) ≤ log ω x := le_log_of_opow_le one_lt_omega0 (by rw [ruOm2_eps]; exact h2)
  have hyl1 : Om 1 ≤ yl := vbLow hl hX hylE hyl hl2
  have hoW : ω ^ yl < Om ω := by
    have := vbOmW_SC.2 0 (Om_pos omega0_ne_zero) yl hylE.2.2; rwa [veblen_zero_apply] at this
  have hoC : ω ^ yl ∈ S.CSet (Om ω) (ConjT.th S) := by
    have := CSet.phi_mem (S := S) (CSet.zero_mem _ _) hylE.2.1; rwa [veblen_zero_apply] at this
  have hoE : RxE S (vbW S l) (ω ^ yl) := ⟨RxN.opow hylE.1, hoC, hoW⟩
  have hκo : vbK S l (ω ^ yl) = ω ^ log ω x := by
    show rxL S (upsilon l) (ldAtR S l) (vbW S l) (ω ^ yl) = _
    rw [rxL_opow hZ hZ1 hAt hylE hoE hyl1]
    show ω ^ vbK S l yl = _
    rw [hyl]
  have hyrlt : yr < ω ^ yl := by
    rw [vbK_lt_iff hl hX hyrE hoE, hyr, hκo]; exact Ordinal.mod_lt x hpos.ne'
  set y := ω ^ yl * n + yr with hydef
  have hyE : RxE S (vbW S l) y :=
    ⟨RxN.add (RxN.mul_nat hoE.1 n) hyrE.1, CSet.add_mem (ConjT.mul_nat_mem S hoC n) hyrE.2.1,
      vbOmW_SC.isPrincipal (vbMulNat_lt vbOmW_SC.isPrincipal vbOmW_SC.1 hoW n) hyrE.2.2⟩
  have hn1' : (1 : Ordinal.{0}) ≤ n := by exact_mod_cast hn1
  have hy1 : Om 1 ≤ y :=
    ((hyl1.trans (right_le_opow _ one_lt_omega0)).trans (Ordinal.le_mul_left _ (zero_lt_one.trans_le hn1'))).trans
      le_self_add
  obtain ⟨n', -, hdm', hκy, -⟩ := rxLDecK hZ hZ1 hAt hyE hy1
  have hlogy : log ω y = yl := by
    rw [hydef, log_opow_mul_add one_lt_omega0 hn0 hyrlt, log_eq_zero (natCast_lt_omega0 n), add_zero]
  have hmody : y % ω ^ yl = yr := by
    rw [hydef, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hyrlt]
  have hyl0 : ω ^ yl ≠ 0 := (opow_pos _ omega0_pos).ne'
  have hnn : (n' : Ordinal.{0}) = n := by
    rw [hlogy, hmody] at hdm'
    have e1 : y / ω ^ yl = n := by
      rw [hydef, Ordinal.mul_add_div _ hyl0, Ordinal.div_eq_zero_of_lt hyrlt, add_zero]
    have e2 : y / ω ^ yl = n' := by
      rw [hdm', Ordinal.mul_add_div _ hyl0, Ordinal.div_eq_zero_of_lt hyrlt, add_zero]
    rw [← e1, ← e2]
  refine ⟨y, hyE, ?_⟩
  show rxL S (upsilon l) (ldAtR S l) (vbW S l) y = x
  rw [hκy, hlogy, hmody, hnn]
  show ω ^ vbK S l yl * n + vbK S l yr = x
  rw [hyl, hyr, ← hdm]

/-- **`κ_λ(T x) = x` and `T x` is a member** for every `x ∈ VbD S λ`. -/
theorem vbT_eq {x : Ordinal.{0}} (hx : VbD S l x) :
    RxE S (vbW S l) (vbT S l x) ∧ vbK S l (vbT S l x) = x :=
  vbT_spec (vbOnto hl hX x hx)

end Rst

end Googology.Trans.PoR.InaccPsi.R2.Vb
