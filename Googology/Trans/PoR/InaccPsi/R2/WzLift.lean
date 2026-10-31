import Googology.Trans.PoR.InaccPsi.R2.WzIt
import Googology.Trans.PoR.InaccPsi.R2.WkLift

/-!
# The level shift with a level bound `L`: `κ x ∈ Cl(a, b)` for `x ∈ Cl(c, ψ_{Ω₂}(c))`, `c ≤ L`, `a ≥ κ L`

`κ = rxL S Z At W` the level shift of `Rx` (`Ω_k ↦ Ω_{k+1}`, `ψ_{Ω_{k+1}}(d) ↦ ψ_{Ω_{k+2}}(κ d)`, `Θ⁻¹` below `Ω₁`),
`W = rxW Z At`.  `Wk.wkL_memN` is the case `L = Ω_n` (`κ Ω_n = Ω_{n+1}`); here `L` is any member of the domain,
e.g. `L = Ω₂ + ζ` with `κ L = Ω₃ + κ ζ` (`Vh.vhK_add`): the lift at the base `Ω₃` with offsets up to `ψ_{Ω₂}(Ω₂·2)`.

* `wzL_memL` (**every normal collapse `ψ_{Ω_{j+1}}(d)` met in `x` has `d < L`, and `κ d < κ L ≤ a`**; the proof of
  `Wk.wkL_memN` with `rxL_mono` in place of `rxL_Om`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Rx

variable {S : InaccSeq.{0}}

section K

variable {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1) (hAt : GxAt At)
include hZ hZ1 hAt

/-- **THE LEVEL SHIFT WITH A LEVEL BOUND `L`**: if `x` is a member over `T ≤ W` with `x ∈ Cl(c, ψ_{Ω₂}(c))` for
some `c ≤ L` (`L` in the domain of `κ`), then `κ x ∈ Cl(a, b)` for every `a ≥ κ L`, when every `Θ⁻¹(g)`, `g < T`,
is in it. -/
theorem wzL_memL {T a b L : Ordinal.{0}} (hT : SC T) (hTW : T ≤ rxW Z At)
    (hLE : RxE S (rxW Z At) L) (ha : rxL S Z At (rxW Z At) L ≤ a)
    (hinv : ∀ g, g < T → ruInv Z At g ∈ S.CSet a b) :
    ∀ x, RxE S T x → (∃ c, c ≤ L ∧ x ∈ S.CSet c (S.psi c (Om (1 + 1)))) →
      rxL S Z At (rxW Z At) x ∈ S.CSet a b := by
  have hW1 := rxW_le_Om1 (Z := Z) (At := At)
  have hT1 : T ≤ Om 1 := hTW.trans hW1
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  refine rxMs_ind (S := S) (T := rxW Z At) fun x IH hx hcx => ?_
  obtain ⟨c, hcn, hxc⟩ := hcx
  have hxW : RxE S (rxW Z At) x := hx.mono hTW
  rcases lt_or_ge x (Om 1) with h1 | h1
  · rw [(rxL_small hZ hZ1 hAt hxW h1).1]; exact hinv x (rxE_lt_T hT hx h1)
  by_cases hΩ : ∃ j : ℕ, x = Om (j : Ordinal.{0})
  · obtain ⟨j, rfl⟩ := hΩ
    have hj : 1 ≤ j := by
      by_contra h0
      have : j = 0 := by omega
      subst this
      rw [Nat.cast_zero, Om_zero] at h1; exact absurd h1 (not_le.2 (Om_pos one_ne_zero))
    rw [rxL_Om hj]; exact rxC_Om_succ _ _ j
  have h1' : Om 1 < x := lt_of_le_of_ne h1 fun e => hΩ ⟨1, by rw [Nat.cast_one]; exact e.symm⟩
  by_cases hS : SC x
  · obtain ⟨j, hj, d, hdE, hdn, rfl, -⟩ := rxE_atom hT1 hx hS h1' hΩ
    obtain ⟨hK, hdh⟩ := rxL_psiE hj (hdE.mono hTW) hdn
    -- the argument `d` is below `c ≤ Ω_n`, and the invariant passes to `d`
    have hdc : d < L ∧
        ∃ c', c' ≤ L ∧ d ∈ S.CSet c' (S.psi c' (Om (1 + 1))) := by
      rcases le_or_gt (S.psi c (Om (1 + 1))) (S.psi d (Om ((j : Ordinal.{0}) + 1))) with hle | hlt
      · have hL : S.psi c (Om (1 + 1)) ≤ S.Lam := (psi_lt hκ2 c).le.trans Wk.wkOm2_le_Lam
        obtain ⟨hdm, hdlt⟩ := arg_mem_of_psi_mem (InR_Om_succ _) hxc hle hL hdn
        exact ⟨hdlt.trans_le hcn, c, hcn, hdm⟩
      · have hj1 : j = 1 := by
          by_contra hne
          have hj2 : 2 ≤ j := by omega
          have h2 : Om (1 + 1 : Ordinal.{0}) ≤ Om (j : Ordinal.{0}) := by
            refine Om_le_Om.2 ?_
            rw [one_add_one_eq_two]; exact_mod_cast hj2
          have h3 := (psiS_bounds (S := S) d (j : Ordinal.{0})).1
          exact absurd ((h2.trans h3.le).trans_lt (hlt.trans (psi_lt hκ2 c))) (lt_irrefl _)
        subst hj1
        rw [Nat.cast_one] at hlt hdn
        have hdlt : d < c := by
          by_contra hcon
          exact absurd (psi_mono (S := S) hκ2 (not_lt.1 hcon)).1 (not_le.2 hlt)
        exact ⟨hdlt.trans_le hcn, d, (hdlt.trans_le hcn).le, hdn⟩
    obtain ⟨hdlt, hdI⟩ := hdc
    have hκd : rxL S Z At (rxW Z At) d < rxL S Z At (rxW Z At) L :=
      rxL_mono hZ hZ1 hAt (hdE.mono hTW) hLE hdlt
    rw [hK]
    exact CSet.psi_mem (hκd.trans_le ha) (InR_Om_succ _)
      (rxC_Om_succ2 _ _ j) (IH d (rxMs_lt_stage (rxE_lt_Lam hdE) hdh) hdE hdI)
  by_cases hε : ω ^ x = x
  · obtain ⟨hv, -, ha', hb⟩ := rxVeb h1' hε hS
    obtain ⟨haE, hbE, -, -⟩ := rxE_veb hx hv hb
    obtain ⟨-, -, hha, hhb⟩ := rxE_veb hxW hv hb
    obtain ⟨hac, hbc⟩ := rxCDecV hxc _ _ hv hb
    rw [rxL_veb hxW h1' hε hS]
    exact CSet.phi_mem (IH _ (rxMs_lt_val hha ha') haE ⟨c, hcn, hac⟩)
      (IH _ (rxMs_lt_val hhb hb) hbE ⟨c, hcn, hbc⟩)
  · have hlt := ruLog_lt h1' hε
    have hrlt : x % ω ^ log ω x < x := mod_opow_log_lt_self ω ((Om_pos one_ne_zero).trans h1').ne'
    obtain ⟨hlE, -⟩ := rxE_log hx
    obtain ⟨hrE, -⟩ := rxE_rem hx
    obtain ⟨-, hlh⟩ := rxE_log hxW
    obtain ⟨-, hrh⟩ := rxE_rem hxW
    have hlc : log ω x ∈ S.CSet c (S.psi c (Om (1 + 1))) := (rxCDec x hxc).2
    have hrc : x % ω ^ log ω x ∈ S.CSet c (S.psi c (Om (1 + 1))) := Wk.wkRem_mem hxc
    obtain ⟨m, hm⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
    rw [rxL_gt hxW h1' hlt, hm]
    have h1m := IH _ (rxMs_lt_val hlh hlt) hlE ⟨c, hcn, hlc⟩
    have h2m := IH _ (rxMs_lt_val hrh hrlt) hrE ⟨c, hcn, hrc⟩
    have hop : ω ^ rxL S Z At (rxW Z At) (log ω x) ∈ S.CSet a b := by
      have := CSet.phi_mem (S := S) (CSet.zero_mem a b) h1m; rwa [veblen_zero_apply] at this
    exact CSet.add_mem (ConjT.mul_nat_mem S hop m) h2m

end K

end Googology.Trans.PoR.InaccPsi.R2.Wz

#print axioms Googology.Trans.PoR.InaccPsi.R2.Wz.wzL_memL
