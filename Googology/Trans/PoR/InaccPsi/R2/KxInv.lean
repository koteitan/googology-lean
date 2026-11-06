import Googology.Trans.PoR.InaccPsi.R2.KwLimC

/-!
# Kx: THE INVERSE TRANSFER (the level shift `κ` keeps the closures with a bound on the arguments)

`κ = Rx.rxL S Z At W` (`W = rxW Z At`; `Θ⁻¹` below `Ω₁`, `Ω_k ↦ Ω_{k+1}`, `ψ_{k+1}(d) ↦ ψ_{k+2}(κ d)`), `RxE S T` its
domain over `T ≤ W`, `ψ₂ = ψ_{Ω₂}`.

* `kxK` (**THE BOUNDED INVERSE TRANSFER**): every member `x` over `T` with `x ∈ Cl(α, ψ₂(α))` has
  `κ x ∈ Cl(a, b)`, when every `Θ⁻¹(g)`, `g < T`, is in `Cl(a, b)` and `κ d < a` for every member `d < α`
  (`Rx.rxL_memH` is the case `Ω_ω ≤ a` without the bound on the arguments).  The atoms `ψ_{k+1}(d)` of
  `Cl(α, ψ₂ α)`: at or above `ψ₂(α)` the normal argument is in `Cl(α, ψ₂ α)` below `α`
  (`arg_mem_of_psi_mem`); below `ψ₂(α)` the atom is `ψ₂(d)` with `d < α` normal.
* `kxNorm` (**the normal hull in `D`**): for `z ∈ D`, `Ω₃ ∣ z`, `M(z)` (the least member of `Cl(z, ψ₂ z)` at or above
  `z`) is in `D`, normal, `Ω₃`-divisible, with `ψ₂(M z) = ψ₂(z)`.

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Vb
  Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

section K

variable {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1) (hAt : GxAt At)
include hZ hZ1 hAt

/-- **THE BOUNDED INVERSE TRANSFER.** -/
theorem kxK {T α a b : Ordinal.{0}} (hT : SC T) (hTW : T ≤ rxW Z At)
    (hinv : ∀ g, g < T → ruInv Z At g ∈ S.CSet a b)
    (harg : ∀ d, RxE S (rxW Z At) d → d < α → rxL S Z At (rxW Z At) d < a) :
    ∀ x, RxE S T x → x ∈ S.CSet α (S.psi α (Om (1 + 1))) → rxL S Z At (rxW Z At) x ∈ S.CSet a b := by
  have hW1 := rxW_le_Om1 (Z := Z) (At := At)
  have hT1 : T ≤ Om 1 := hTW.trans hW1
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hgL : S.psi α (Om (1 + 1)) ≤ S.Lam := (psi_lt hκ2 α).le.trans Xd.xdOm2_le_Lam
  refine rxMs_ind (S := S) (T := rxW Z At) fun x IH hx hxC => ?_
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
    -- the normal argument `d` lies in `Cl(α, ψ₂ α)` below `α`
    have hdCα : d ∈ S.CSet α (S.psi α (Om (1 + 1))) ∧ d < α := by
      rcases le_or_gt (S.psi α (Om (1 + 1))) (S.psi d (Om ((j : Ordinal.{0}) + 1))) with hle | hlt
      · exact arg_mem_of_psi_mem (InR_Om_succ _) hxC hle hgL hdn
      · have hb := psiS_bounds (S := S) d (j : Ordinal.{0})
        have hj1 : j = 1 := by
          have h3 : (j : Ordinal.{0}) < 1 + 1 :=
            Om_lt_Om.1 (hb.1.trans (hlt.trans (psi_lt hκ2 α)))
          have : j < 2 := by
            have h4 : (j : Ordinal.{0}) < 2 := by rwa [one_add_one_eq_two] at h3
            exact_mod_cast h4
          omega
        subst hj1
        rw [Nat.cast_one] at hlt hdn
        have hdα : d < α := by
          by_contra hc
          push Not at hc
          exact absurd hlt (not_lt.2 (psi_mono hκ2 hc).1)
        exact ⟨CSet_mono hdα.le (psi_mono hκ2 hdα.le).1 hdn, hdα⟩
    rw [hK]
    exact CSet.psi_mem (harg d (hdE.mono hTW) hdCα.2) (InR_Om_succ _) (rxC_Om_succ2 _ _ j)
      (IH d (rxMs_lt_stage (rxE_lt_Lam hdE) hdh) hdE hdCα.1)
  by_cases hε : ω ^ x = x
  · obtain ⟨hv, -, ha', hb⟩ := rxVeb h1' hε hS
    obtain ⟨haE, hbE, -, -⟩ := rxE_veb hx hv hb
    obtain ⟨-, -, hha, hhb⟩ := rxE_veb hxW hv hb
    obtain ⟨haC, hbC⟩ := rxCDecV hxC _ _ hv hb
    rw [rxL_veb hxW h1' hε hS]
    exact CSet.phi_mem (IH _ (rxMs_lt_val hha ha') haE haC) (IH _ (rxMs_lt_val hhb hb) hbE hbC)
  · have hlt := ruLog_lt h1' hε
    have hrlt : x % ω ^ log ω x < x := mod_opow_log_lt_self ω ((Om_pos one_ne_zero).trans h1').ne'
    obtain ⟨hlE, -⟩ := rxE_log hx
    obtain ⟨hrE, -⟩ := rxE_rem hx
    obtain ⟨-, hlh⟩ := rxE_log hxW
    obtain ⟨-, hrh⟩ := rxE_rem hxW
    obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
    rw [rxL_gt hxW h1' hlt, hn]
    have h1m := IH _ (rxMs_lt_val hlh hlt) hlE (rxCDec x hxC).2
    have h2m := IH _ (rxMs_lt_val hrh hrlt) hrE (vbC_rem hxC)
    have hop : ω ^ rxL S Z At (rxW Z At) (log ω x) ∈ S.CSet a b := by
      have := CSet.phi_mem (S := S) (CSet.zero_mem a b) h1m; rwa [veblen_zero_apply] at this
    exact CSet.add_mem (ConjT.mul_nat_mem S hop n) h2m

end K

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The normal hull in `D`**: `M(z)` for `z ∈ D`, `Ω₃ ∣ z`. -/
theorem kxNorm {z : Ordinal.{0}} (hzD : VbD S l z) (hz3 : Om (1 + 1 + 1) ∣ z) :
    VbD S l (S.M z (S.psi z (Om (1 + 1))) z) ∧
      S.M z (S.psi z (Om (1 + 1))) z ∈ S.CSet (S.M z (S.psi z (Om (1 + 1))) z)
        (S.psi (S.M z (S.psi z (Om (1 + 1))) z) (Om (1 + 1))) ∧
      Om (1 + 1 + 1) ∣ S.M z (S.psi z (Om (1 + 1))) z ∧ z ≤ S.M z (S.psi z (Om (1 + 1))) z ∧
      S.psi (S.M z (S.psi z (Om (1 + 1))) z) (Om (1 + 1)) = S.psi z (Om (1 + 1)) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  set g := S.psi z (Om (1 + 1)) with hgdef
  set a := S.M z g z with hadef
  have hzW : z < Om ω := hzD.2.2
  have hzL : z < S.Lam := hzW.trans rxOmW_lt_Lam
  obtain ⟨haC, hza⟩ := M_spec (e := z) (g := g) hzL
  have hψ : S.psi a (Om (1 + 1)) = g := psi_M_eq hκ2 hzL
  have hn : a ∈ S.CSet a (S.psi a (Om (1 + 1))) := M_mem_self hκ2 hzL
  have hgθ : g ≤ ConjT.th S := (psi_mono hκ2 hzW.le).1
  have haΩ : a ∈ S.CSet (Om ω) (ConjT.th S) := CSet_mono hzW.le hgθ haC
  have hAω : Om ω ≤ ConjT.Aη S (cdEta S l) := ConjT.OmW_le_A S _
  have hρL : upsilon l ≤ S.Lam := (hZ1.trans (Om_lt_Om.2 (lt_add_one 1))).le.trans Xd.xdOm2_le_Lam
  have hρg : upsilon l ≤ g := (hZ1.trans (psiS_bounds (S := S) z 1).1).le
  have haH : a ∈ cdHull S l := by
    have hzA : z ≤ ConjT.Aη S (cdEta S l) := hzW.le.trans hAω
    exact M_mem_of_Good (closed_CSet hzA hρL) z hzL (MQ_of_mem_CSet hzA hρg hρL hzD.1).1.1
  -- `a < Ω_ω`: some finite `Ω_n ≥ z` is a member of `Cl(z, g)`
  have haW : a < Om ω := by
    obtain ⟨n, hn⟩ := rxOmW_nat hzW
    exact (M_le (CSet.Om_mem (rxC_nat (S := S) z g n)) hn.le).trans_lt (Om_lt_Om.2 (natCast_lt_omega0 n))
  -- `Ω₃ ∣ a`: `Ω₃·(a/Ω₃)` is a member of `Cl(z, g)` at or above `z`
  have h3SC : SC (Om (1 + 1 + 1 : Ordinal.{0})) := SC_Om (add_pos_of_nonneg_of_pos zero_le zero_lt_one).ne'
  have h3e : ω ^ Om (1 + 1 + 1 : Ordinal.{0}) = Om (1 + 1 + 1) := gg_SC_eps h3SC
  have h30 : Om (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := h3SC.1.ne'
  have hf := (Vh.vhC_div _ haC (Om (1 + 1 + 1))).1
  rw [h3e] at hf
  have hzf : z ≤ Om (1 + 1 + 1) * (a / Om (1 + 1 + 1)) := by
    obtain ⟨q, hq⟩ := hz3
    have hqa : q ≤ a / Om (1 + 1 + 1) :=
      not_lt.1 fun h => absurd (hq ▸ hza) (not_le.2 ((Ordinal.lt_mul_iff_div_lt h30).2 h))
    rw [hq]; exact mul_le_mul_right hqa _
  have haf : a = Om (1 + 1 + 1) * (a / Om (1 + 1 + 1)) :=
    le_antisymm (M_le hf hzf) (Ordinal.mul_div_le a _)
  exact ⟨⟨haH, haΩ, haW⟩, hn, ⟨_, haf⟩, hza, hψ⟩

end Main

end Googology.Trans.PoR.InaccPsi.R2.Kx

#print axioms Googology.Trans.PoR.InaccPsi.R2.Kx.kxK
#print axioms Googology.Trans.PoR.InaccPsi.R2.Kx.kxNorm
