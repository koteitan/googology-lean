import Googology.Trans.PoR.InaccPsi.R2.KzLow

/-!
# Kz: THE INVERSE TRANSFER AND THE NORMAL HULL BELOW A BOUND `K` (`Kx.kxK`, `Kx.kxNorm` on `D_K`)

`κ = Rx.rxL S Z At W` (`W = rxW Z At`), `RxEK S T K` its domain over `T ≤ W` below `K` (`Kz.KzB`), `ψ₂ = ψ_{Ω₂}`.

* `kzKx` (**THE BOUNDED INVERSE TRANSFER BELOW `K`**: the proof of `Kx.kxK`, with the new case `x = Ω_ω`,
  `κ Ω_ω = Ω_ω`);
* `kzNorm` (**the normal hull in `D_K`**: for `z ∈ D_K`, `z ≤ A`, `Ω₃ ∣ z`, `M(z)` is in `D_K`, normal,
  `Ω₃`-divisible, `≥ z`, with `ψ₂(M z) = ψ₂(z)`; `M z < K` from `KzB.fin`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Vb
  Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

section K

variable {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1) (hAt : GxAt At)
  {K : Ordinal.{0}} (hKB : KzB S K)
include hZ hZ1 hAt hKB

/-- **THE BOUNDED INVERSE TRANSFER BELOW `K`.** -/
theorem kzKx {T α a b : Ordinal.{0}} (hT : SC T) (hTW : T ≤ rxW Z At)
    (hinv : ∀ g, g < T → ruInv Z At g ∈ S.CSet a b)
    (harg : ∀ d, RxEK S (rxW Z At) K d → d < α → rxL S Z At (rxW Z At) d < a) :
    ∀ x, RxEK S T K x → x ∈ S.CSet α (S.psi α (Om (1 + 1))) → rxL S Z At (rxW Z At) x ∈ S.CSet a b := by
  have hW1 := rxW_le_Om1 (Z := Z) (At := At)
  have hT1 : T ≤ Om 1 := hTW.trans hW1
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hgL : S.psi α (Om (1 + 1)) ≤ S.Lam := (psi_lt hκ2 α).le.trans Xd.xdOm2_le_Lam
  refine rxMs_ind (S := S) (T := rxW Z At) fun x IH hx hxC => ?_
  have hxW : RxEK S (rxW Z At) K x := ⟨hx.1.mono hTW, hx.2⟩
  rcases lt_or_ge x (Om 1) with h1 | h1
  · rw [(kzL_small hZ hZ1 hAt hxW h1).1]; exact hinv x (rxNs_lt_T hT (rxH_spec hx.1) h1)
  by_cases hΩ : ∃ j : ℕ, x = Om (j : Ordinal.{0})
  · obtain ⟨j, rfl⟩ := hΩ
    have hj : 1 ≤ j := by
      by_contra h0
      have : j = 0 := by omega
      subst this
      rw [Nat.cast_zero, Om_zero] at h1; exact absurd h1 (not_le.2 (Om_pos one_ne_zero))
    rw [rxL_Om hj]; exact rxC_Om_succ _ _ j
  by_cases hW : x = Om ω
  · rw [hW, kzL_OmW]; exact CSet.Om_mem (kzOmega_mem a b)
  have h1' : Om 1 < x := lt_of_le_of_ne h1 fun e => hΩ ⟨1, by rw [Nat.cast_one]; exact e.symm⟩
  by_cases hS : SC x
  · have hne : ∀ σ, x ≠ Om σ := fun σ e => by
      rcases kzCard hKB (e ▸ hx.2.2) with ⟨k, rfl⟩ | rfl
      · exact hΩ ⟨k, e⟩
      · exact hW e
    obtain ⟨j, hj, d, hdE, hdn, rfl, -⟩ := kzE_atom hKB hT1 hx hS h1' hne
    have hdEW : RxEK S (rxW Z At) K d := ⟨hdE.1.mono hTW, hdE.2⟩
    obtain ⟨hK, hdh⟩ := kzL_psiE hKB hj hdEW hdn
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
    exact CSet.psi_mem (harg d hdEW hdCα.2) (InR_Om_succ _) (rxC_Om_succ2 _ _ j)
      (IH d (rxMs_lt_stage (kzE_lt_Lam hKB hdE) hdh) hdE hdCα.1)
  by_cases hε : ω ^ x = x
  · obtain ⟨hv, -, ha', hb⟩ := rxVeb h1' hε hS
    obtain ⟨haE, hbE, -, -⟩ := kzE_veb hx hv hb
    obtain ⟨-, -, hha, hhb⟩ := kzE_veb hxW hv hb
    obtain ⟨haC, hbC⟩ := rxCDecV hxC _ _ hv hb
    rw [kzL_veb hxW h1' hε hS]
    exact CSet.phi_mem (IH _ (rxMs_lt_val hha ha') haE haC) (IH _ (rxMs_lt_val hhb hb) hbE hbC)
  · have hlt := ruLog_lt h1' hε
    have hrlt : x % ω ^ log ω x < x := mod_opow_log_lt_self ω ((Om_pos one_ne_zero).trans h1').ne'
    obtain ⟨hlE, -⟩ := kzE_log hx
    obtain ⟨hrE, -⟩ := kzE_rem hx
    obtain ⟨-, hlh⟩ := kzE_log hxW
    obtain ⟨-, hrh⟩ := kzE_rem hxW
    obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
    rw [kzL_gt hxW h1' hlt, hn]
    have h1m := IH _ (rxMs_lt_val hlh hlt) hlE (rxCDec x hxC).2
    have h2m := IH _ (rxMs_lt_val hrh hrlt) hrE (vbC_rem hxC)
    have hop : ω ^ rxL S Z At (rxW Z At) (log ω x) ∈ S.CSet a b := by
      have := CSet.phi_mem (S := S) (CSet.zero_mem a b) h1m; rwa [veblen_zero_apply] at this
    exact CSet.add_mem (ConjT.mul_nat_mem S hop n) h2m

end K

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {K : Ordinal.{0}} (hKB : KzB S K)

include hl hX hKB

/-- **The normal hull in `D_K`**: `M(z)` for `z ∈ D_K`, `z ≤ A`, `Ω₃ ∣ z`. -/
theorem kzNorm {z : Ordinal.{0}} (hzD : VbDK S l K z) (hzA : z ≤ ConjT.Aη S (cdEta S l))
    (hz3 : Om (1 + 1 + 1) ∣ z) :
    VbDK S l K (S.M z (S.psi z (Om (1 + 1))) z) ∧
      S.M z (S.psi z (Om (1 + 1))) z ∈ S.CSet (S.M z (S.psi z (Om (1 + 1))) z)
        (S.psi (S.M z (S.psi z (Om (1 + 1))) z) (Om (1 + 1))) ∧
      Om (1 + 1 + 1) ∣ S.M z (S.psi z (Om (1 + 1))) z ∧ z ≤ S.M z (S.psi z (Om (1 + 1))) z ∧
      S.psi (S.M z (S.psi z (Om (1 + 1))) z) (Om (1 + 1)) = S.psi z (Om (1 + 1)) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  set g := S.psi z (Om (1 + 1)) with hgdef
  set a := S.M z g z with hadef
  have hzK : z < K := hzD.2.2
  have hzL : z < S.Lam := hzK.trans (kzK_lt_Lam hKB)
  obtain ⟨haC, hza⟩ := M_spec (e := z) (g := g) hzL
  have hψ : S.psi a (Om (1 + 1)) = g := psi_M_eq hκ2 hzL
  have hn : a ∈ S.CSet a (S.psi a (Om (1 + 1))) := M_mem_self hκ2 hzL
  have hgK : g ≤ S.psi K (Om (1 + 1)) := (psi_mono hκ2 hzK.le).1
  have haK' : a ∈ S.CSet K (S.psi K (Om (1 + 1))) := CSet_mono hzK.le hgK haC
  have hρL : upsilon l ≤ S.Lam := (hZ1.trans (Om_lt_Om.2 (lt_add_one 1))).le.trans Xd.xdOm2_le_Lam
  have hρg : upsilon l ≤ g := (hZ1.trans (psiS_bounds (S := S) z 1).1).le
  have haH : a ∈ cdHull S l :=
    M_mem_of_Good (closed_CSet hzA hρL) z hzL (MQ_of_mem_CSet hzA hρg hρL hzD.1).1.1
  -- `a < K`: a closed `w < K` lies at or above `z`
  have haK : a < K := by
    obtain ⟨w, hzw, hwK, hwC⟩ := hKB.fin z hzK
    exact (M_le (hwC z g) hzw).trans_lt hwK
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
  exact ⟨⟨haH, haK', haK⟩, hn, ⟨_, haf⟩, hza, hψ⟩

end Main

end Googology.Trans.PoR.InaccPsi.R2.Kz

#print axioms Googology.Trans.PoR.InaccPsi.R2.Kz.kzKx
#print axioms Googology.Trans.PoR.InaccPsi.R2.Kz.kzNorm
