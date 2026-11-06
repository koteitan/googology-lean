import Googology.Trans.PoR.InaccPsi.R2.KzBack

/-!
# Kz: EVERY MEMBER OF `D_K` IS A VALUE OF THE LEVEL SHIFT (`Vb.vbOnto` below a bound `K`)

* `vbCodeK`, `vbLowK`, `vbOntoK` (**THE ONTO THEOREM BELOW `K`**: one induction on the measure; the new member
  `Ω_ω = κ Ω_ω`), `vbTK_eq` (**`κ_λ(T_K x) = x` and `T_K x` is a member**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Vb

variable {S : InaccSeq.{0}}

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {K : Ordinal.{0}} (hK : KzB S K)

include hl hX hK

/-- **A code `x < Ω₂` of `H_λ` is `κ_λ(Θ x)`.** -/
theorem vbCodeK {x : Ordinal.{0}} (hx2 : x < Om (1 + 1)) (hxH : x ∈ cdHull S l) :
    RxEK S (vbW S l) K (gxTh (upsilon l) (ldAtR S l) x) ∧ vbK S l (gxTh (upsilon l) (ldAtR S l) x) = x := by
  have hc : GxCl (upsilon l) (ldAtR S l) x := (ldHull_iff hl hX hx2).1 hxH
  have hlt : gxTh (upsilon l) (ldAtR S l) x < gxTh (upsilon l) (ldAtR S l) (Om (1 + 1)) := gxTh_lt hc hx2
  have hW : gxTh (upsilon l) (ldAtR S l) x < vbW S l := by rw [vbW_eq hl hX]; exact hlt
  have hx1 : gxTh (upsilon l) (ldAtR S l) x < Om 1 := hW.trans_le (min_le_right _ _)
  have h1θ : Om 1 < S.psi K (Om (1 + 1)) := (psiS_bounds (S := S) K 1).1
  have h1W : Om 1 < K := (Om_lt_Om.2 one_lt_omega0).trans_le hK.ge
  refine ⟨⟨RxN.small hW, CSet.of_lt (hx1.trans h1θ), hx1.trans h1W⟩, ?_⟩
  show rxL S (upsilon l) (ldAtR S l) (vbW S l) _ = x
  rw [rxL_lt_Om1 hx1]
  obtain ⟨h1, -, h3⟩ := ruInv_spec hlt
  exact ruCode_inj h1 hc h3

/-- **A value `≥ Ω₂` of `κ_λ` comes from a member `≥ Ω₁`.** -/
theorem vbLowK {u v : Ordinal.{0}} (hu : RxEK S (vbW S l) K u) (huv : vbK S l u = v) (hv2 : Om (1 + 1) ≤ v) :
    Om 1 ≤ u := by
  by_contra hc
  push Not at hc
  obtain ⟨e, h2, -⟩ := kzL_small (vbZ hl hX).1 (vbZ hl hX).2 (ldAt_GxAt _ _) hu hc
  have h3 : ruInv (upsilon l) (ldAtR S l) u = v := e.symm.trans huv
  rw [← h3] at hv2
  exact absurd h2 (not_lt.2 hv2)

/-- **THE ONTO THEOREM**: every member of `VbD S λ` is a value of `κ_λ`. -/
theorem vbOntoK : ∀ x, VbDK S l K x → ∃ y, RxEK S (vbW S l) K y ∧ vbK S l y = x := by
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  refine rxMs_ind (S := S) (T := upsilon l) fun x IH hx => ?_
  have hxE : RxEK S (upsilon l) K x := vbDK_E hl hX hx
  rcases lt_or_ge x (Om (1 + 1)) with h2 | h2
  · exact ⟨_, vbCodeK hl hX hK h2 hx.1⟩
  by_cases hΩ : ∃ j : ℕ, x = Om (j : Ordinal.{0})
  · obtain ⟨j, rfl⟩ := hΩ
    have hj : 2 ≤ j := by
      have h := Om_le_Om.1 h2
      rw [one_add_one_eq_two] at h
      have h' : ((2 : ℕ) : Ordinal.{0}) ≤ j := by rw [Nat.cast_ofNat]; exact h
      exact_mod_cast h'
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    refine ⟨Om (i : Ordinal.{0}), ⟨RxN.om (rxN_nat i), rxC_Om_nat _ _ i,
      (Om_lt_Om.2 (natCast_lt_omega0 i)).trans_le hK.ge⟩, ?_⟩
    show rxL S (upsilon l) (ldAtR S l) (vbW S l) (Om (i : Ordinal.{0})) = Om ((i + 1 : ℕ) : Ordinal.{0})
    rw [rxL_Om (by omega : 1 ≤ i), Nat.cast_succ]
  by_cases hxW : x = Om ω
  · subst hxW
    have hωN : RxN S (vbW S l) ω := by
      have := RxN.phi (RxN.zero (S := S) (T := vbW S l)) (RxN.succ (RxN.zero (S := S) (T := vbW S l)))
      rwa [veblen_zero_apply, zero_add, opow_one] at this
    exact ⟨Om ω, ⟨RxN.om hωN, ConjT.OmW_mem S _ _, hx.2.2⟩, kzL_OmW⟩
  have hx2 : Om (1 + 1) < x := lt_of_le_of_ne h2 (fun e => hΩ ⟨2, by rw [← e]; norm_num⟩)
  have hx1 : Om 1 < x := (Om_lt_Om.2 (lt_add_one 1)).trans hx2
  have h0 : x ≠ 0 := ((Om_pos one_ne_zero).trans hx1).ne'
  by_cases hS : SC x
  · obtain ⟨k, hk, d, hdE, hdn, rfl, hst⟩ := kzE_atom hK hZ1.le hxE hS hx1 (kzNe hK hxE hΩ hxW)
    have hk2 : 2 ≤ k := by
      by_contra hc
      have hk1 : k = 1 := by omega
      subst hk1
      have := (psiS_bounds (S := S) d ((1 : ℕ) : Ordinal.{0})).2
      rw [Nat.cast_one] at this hx2
      exact absurd (hx2.trans this) (lt_irrefl _)
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hk' : 1 ≤ k' := by omega
    have hdD : VbDK S l K d := vbDK_atom hl hX hx hdE hdn hk
    obtain ⟨yd, hydE, hyd⟩ := IH d (rxMs_lt_stage (kzE_lt_Lam hK hdE) hst) hdD
    have hdn' : d ∈ S.CSet d (S.psi d (Om ((k' : Ordinal.{0}) + 1 + 1))) := by
      have e : ((k' + 1 : ℕ) : Ordinal.{0}) = (k' : Ordinal.{0}) + 1 := Nat.cast_succ k'
      rw [e] at hdn; exact hdn
    have hnyd := kzBack hZ hZ1 hAt hK hk' hydE hyd hdn'
    refine ⟨S.psi yd (Om ((k' : Ordinal.{0}) + 1)), kzE_psi hK hk' hydE hnyd, ?_⟩
    show rxL S (upsilon l) (ldAtR S l) (vbW S l) _ = _
    rw [(kzL_psiE hK hk' hydE hnyd).1]
    show S.psi (vbK S l yd) _ = _
    rw [hyd, Nat.cast_succ]
  by_cases hε : ω ^ x = x
  · obtain ⟨hv, ha0, ha, hb⟩ := rxVeb hx1 hε hS
    obtain ⟨haD, hbD, -, -, hha, hhb⟩ := vbDK_veb hx hxE hv hb
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
      · exact (vbLowK hl hX hK hyaE hya h).trans (left_le_veblen ya yb)
      · exact (vbLowK hl hX hK hybE hyb h).trans (right_le_veblen ya yb)
    have hyε : ω ^ y = y := gg_veblen_eps hya0
    have hyE : RxEK S (vbW S l) K y :=
      ⟨RxN.phi hyaE.1 hybE.1, CSet.phi_mem hyaE.2.1 hybE.2.1, hK.sc.2 _ hyaE.2.2 _ hybE.2.2⟩
    obtain ⟨a', b', hv', hb', -, ha'E, -, hκy, -, -, -⟩ := kzLDecV hZ hK hyE hy1 hyε
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
      have hlt : invVeblen₁ x < vbK S l a' := by rw [← hya]; exact vbKK_mono hl hX hK hyaE ha'E h3
      have h4 := veblen_veblen_of_lt hlt (vbK S l b')
      rw [← hbκ, hv] at h4
      exact lt_irrefl x (h4.trans_lt hb)
  -- the Cantor normal form
  have hlx : log ω x < x := ruLog_lt hx1 hε
  obtain ⟨hlD, -, hlh⟩ := vbDK_log hx hxE
  obtain ⟨hrD, -, hrh⟩ := vbDK_rem hx hxE
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
  have hyl1 : Om 1 ≤ yl := vbLowK hl hX hK hylE hyl hl2
  have hoW : ω ^ yl < K := by
    have := hK.sc.2 0 hK.sc.1 yl hylE.2.2; rwa [veblen_zero_apply] at this
  have hoC : ω ^ yl ∈ S.CSet K (S.psi K (Om (1 + 1))) := by
    have := CSet.phi_mem (S := S) (CSet.zero_mem _ _) hylE.2.1; rwa [veblen_zero_apply] at this
  have hoE : RxEK S (vbW S l) K (ω ^ yl) := ⟨RxN.opow hylE.1, hoC, hoW⟩
  have hκo : vbK S l (ω ^ yl) = ω ^ log ω x := by
    show rxL S (upsilon l) (ldAtR S l) (vbW S l) (ω ^ yl) = _
    rw [kzL_opow hZ hZ1 hAt hK hylE hoE hyl1]
    show ω ^ vbK S l yl = _
    rw [hyl]
  have hyrlt : yr < ω ^ yl := by
    rw [vbKK_lt_iff hl hX hK hyrE hoE, hyr, hκo]; exact Ordinal.mod_lt x hpos.ne'
  set y := ω ^ yl * n + yr with hydef
  have hyE : RxEK S (vbW S l) K y :=
    ⟨RxN.add (RxN.mul_nat hoE.1 n) hyrE.1, CSet.add_mem (ConjT.mul_nat_mem S hoC n) hyrE.2.1,
      hK.sc.isPrincipal (vbMulNat_lt hK.sc.isPrincipal hK.sc.1 hoW n) hyrE.2.2⟩
  have hn1' : (1 : Ordinal.{0}) ≤ n := by exact_mod_cast hn1
  have hy1 : Om 1 ≤ y :=
    ((hyl1.trans (right_le_opow _ one_lt_omega0)).trans (Ordinal.le_mul_left _ (zero_lt_one.trans_le hn1'))).trans
      le_self_add
  obtain ⟨n', -, hdm', hκy, -⟩ := kzLDecK hZ hZ1 hAt hK hyE hy1
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
theorem vbTK_eq {x : Ordinal.{0}} (hx : VbDK S l K x) :
    RxEK S (vbW S l) K (vbTK S l K x) ∧ vbK S l (vbTK S l K x) = x :=
  vbTK_spec (vbOntoK hl hX hK x hx)

end Rst

end Googology.Trans.PoR.InaccPsi.R2.Kz
