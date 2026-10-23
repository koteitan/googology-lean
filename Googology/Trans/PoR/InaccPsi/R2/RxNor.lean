import Googology.Trans.PoR.InaccPsi.R2.RxArg

/-!
# The members of `HCl` with normal collapse arguments

`HCl S a T` is `Cl(a, T)` without the countable collapses (`Bt.HCl`), `M = InaccSeq.M`, `RxClosed` the closed target
sets without countable collapses (`Rx.RxClosed`).

* `RxN S T` (**the normal hull over `T`**): the least set with every `x < T`, `0`, `I_n`, `I_ω`, closed under `+`,
  `φ`, `Ω`, and containing `ψ_π(d)` for every `π ∈ R`, `π ≠ Ω₁`, in the set and every member `d` of the set that
  lies in its own closure `Cl(d, ψ_π(d))` (a *normal* argument);
* `rxN_lt_Lam`, `RxN.mono`, `RxN.succ`;
* `rxMQ_of_mem_N` (**every member of `RxN S T` satisfies `MQ`** for a closed target `RxN S T`, `T ≤ g`);
* `rxN_psi` (**`RxN S T` is closed under every collapse `ψ_π`, `π ≠ Ω₁`**, normal argument or not, for
  `T ≤ Ω₁`): by induction on the argument `ξ`, the argument is moved up to `M(ξ)`, which stays in the set
  (`rxMQ_of_mem_N`, needing the collapses below `ξ` only) and lies in its own closure (the proof of the notation's
  `psi_mem_Vals`);
* `rxN_of_HCl` (**`HCl S a T ⊆ RxN S T`** for `T ≤ Ω₁`).

So every member of a hull without countable collapses is generated with normal arguments only.

No new axiom.  New definition: `RxN`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt

/-- **The normal hull over `T`.** -/
inductive RxN (S : InaccSeq.{0}) (T : Ordinal.{0}) : Ordinal.{0} → Prop
  | small {x : Ordinal.{0}} : x < T → RxN S T x
  | zero : RxN S T 0
  | inacc (n : ℕ) : RxN S T (S.I n)
  | inaccW : RxN S T S.Iw
  | add {x y : Ordinal.{0}} : RxN S T x → RxN S T y → RxN S T (x + y)
  | phi {x y : Ordinal.{0}} : RxN S T x → RxN S T y → RxN S T (veblen x y)
  | om {x : Ordinal.{0}} : RxN S T x → RxN S T (Om x)
  | psi {π d : Ordinal.{0}} : S.InR π → π ≠ Om 1 → RxN S T π → RxN S T d →
      d ∈ S.CSet d (S.psi d π) → RxN S T (S.psi d π)

variable {S : InaccSeq.{0}} {T : Ordinal.{0}}

theorem RxN.mono {T' : Ordinal.{0}} (h : T ≤ T') {x : Ordinal.{0}} (hx : RxN S T x) : RxN S T' x := by
  induction hx with
  | small h' => exact RxN.small (lt_of_lt_of_le h' h)
  | zero => exact RxN.zero
  | inacc n => exact RxN.inacc n
  | inaccW => exact RxN.inaccW
  | add _ _ ihx ihy => exact RxN.add ihx ihy
  | phi _ _ ihx ihy => exact RxN.phi ihx ihy
  | om _ ih => exact RxN.om ih
  | psi hπ hπ1 _ _ hd ihπ ihd => exact RxN.psi hπ hπ1 ihπ ihd hd

theorem RxN.one : RxN S T 1 := by
  have := RxN.phi (RxN.zero (S := S) (T := T)) RxN.zero
  rwa [veblen_zero_apply, opow_zero] at this

theorem RxN.succ {x : Ordinal.{0}} (h : RxN S T x) : RxN S T (x + 1) := RxN.add h RxN.one

theorem rxN_lt_Lam (hT : T ≤ S.Lam) {x : Ordinal.{0}} (hx : RxN S T x) : x < S.Lam := by
  induction hx with
  | small h => exact lt_of_lt_of_le h hT
  | zero => exact lt_of_le_of_lt zero_le Iw_lt_Lam
  | inacc n => exact I_lt_Lam n
  | inaccW => exact Iw_lt_Lam
  | add _ _ ihx ihy => exact add_lt_Lam ihx ihy
  | phi _ _ ihx ihy => exact veblen_lt_Lam ihx ihy
  | om _ ih => exact Om_lt_Lam ih
  | @psi π d hπ _ _ _ _ ihπ _ => exact lt_trans (psi_lt hπ d) ihπ

/-- **Every member of `RxN S T` satisfies `MQ`** for a closed target `RxN S T` and `T ≤ g`. -/
theorem rxMQ_of_mem_N {e g x : Ordinal.{0}} (hT : RxClosed S e {x | RxN S T x}) (hTg : T ≤ g)
    (hx : RxN S T x) :
    MQ S e g {x | RxN S T x} x ∧ ∀ σ, x = Om σ → MGood S e g {x | RxN S T x} σ := by
  have Om0 : ∀ σ : Ordinal.{0}, 0 = Om σ → σ = 0 := fun σ hσ => by
    by_contra h; exact (Om_pos h).ne' hσ.symm
  induction hx with
  | @small y h =>
    have hall : ∀ z ≤ y, z ∈ {x | RxN S T x} := fun z hz => RxN.small (lt_of_le_of_lt hz h)
    refine ⟨rxMQ_small hT (lt_of_lt_of_le h hTg) hall, fun σ hσ => ?_⟩
    have hσy : σ ≤ y := hσ ▸ le_Om σ
    exact MGood_small (lt_of_le_of_lt hσy (lt_of_lt_of_le h hTg))
      fun z hz => hall z (hz.trans hσy)
  | zero =>
    exact ⟨MQ_zero, fun σ hσ => by rw [Om0 σ hσ]; exact MGood_zero⟩
  | inacc n =>
    have Q := rxMQ_mem hT (SC_I n) (CSet.I_mem e g n) (RxN.inacc n)
    refine ⟨Q, fun σ hσ => ?_⟩
    rw [← Om_inj.1 ((Om_I n).trans hσ)]; exact Q.1
  | inaccW =>
    have Q := rxMQ_mem hT SC_Iw (CSet.Iw_mem e g) (RxN.inaccW (S := S) (T := T))
    refine ⟨Q, fun σ hσ => ?_⟩
    rw [← Om_inj.1 (S.Om_Iw.trans hσ)]; exact Q.1
  | @add p q _ _ ihp ihq =>
    refine ⟨MQ_add ihp.1 ihq.1, fun σ hσ => ?_⟩
    by_cases hσ0 : σ = 0
    · rw [hσ0]; exact MGood_zero
    by_cases hq0 : q = 0
    · rw [hq0, add_zero] at hσ; exact ihp.2 σ hσ
    have hpz : p < p + q := lt_add_of_pos_right p (pos_iff_ne_zero.2 hq0)
    have hP := (SC_Om hσ0).isPrincipal
    rw [hσ] at hpz
    have hqz : q = Om σ := le_antisymm (hσ ▸ le_add_self)
      (not_lt.1 fun h => absurd hσ (hP hpz h).ne)
    exact ihq.2 σ hqz
  | @phi p q _ _ ihp ihq =>
    refine ⟨rxMQ_phi hT ihp.1 ihq.1, fun σ hσ => ?_⟩
    by_cases hσ0 : σ = 0
    · rw [hσ0, Om_zero] at hσ; exact absurd hσ veblen_pos.ne'
    rcases (SC_Om hσ0).eq_of_veblen_eq hσ with h | h
    · exact ihp.2 σ h
    · exact ihq.2 σ h
  | @om p _ ihp =>
    refine ⟨rxMQ_Om hT ihp.1, fun σ hσ => ?_⟩
    rw [← Om_inj.1 hσ]; exact ihp.1.1
  | @psi π d hπ hπ1 hπN hdN hdn ihπ ihd =>
    rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
    · have Q := rxMQ_psiI hT ihd.1.1 (RxN.psi (InR_I n) hπ1 hπN hdN hdn)
      refine ⟨Q, fun σ hσ => ?_⟩
      have : σ = S.psi d (S.I n) := Om_inj.1 (hσ.symm.trans (Om_psiI d n).symm)
      rw [this]; exact Q.1
    · have hs1 := ihπ.2 (s + 1) rfl
      have hs : MGood S e g {x | RxN S T x} s := fun h hc => hs1 h hc.add_one
      have hs0 : s ≠ 0 := fun h0 => hπ1 (by rw [h0, zero_add])
      have Q := rxMQ_psiS hT hs0 hs ihd.1.1 (RxN.psi (InR_Om_succ s) hπ1 hπN hdN hdn)
      exact ⟨Q, fun σ hσ =>
        absurd hσ (not_Om_of_between (psiS_bounds _ _).1 (psiS_bounds _ _).2 σ)⟩

/-- `ψ_π(e) ≥ Ω₁` for `π ≠ Ω₁`. -/
theorem rxOm1_le_psi {π e : Ordinal.{0}} (hπ : S.InR π) (hπ1 : π ≠ Om 1) : Om 1 ≤ S.psi e π :=
  not_lt.1 fun h => hπ1 (Low.eq_Om_one_of_psi_lt hπ h)

/-- **`RxN S T` is closed under every collapse `ψ_π`, `π ≠ Ω₁`.** -/
theorem rxN_psi (hT1 : T ≤ Om 1) : ∀ ξ, RxN S T ξ → ∀ π, S.InR π → π ≠ Om 1 → RxN S T π →
    RxN S T (S.psi ξ π) := by
  have hTL : T ≤ S.Lam := hT1.trans (lt_Lam_of_mem zero_le (CSet.Om_mem (CSet.one_mem (S := S) 0 0))).le
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | _ ξ IH =>
  intro hξ π hπ hπ1 hπN
  have hT : RxClosed S ξ {x | RxN S T x} :=
    { zero := RxN.zero
      I := fun n => RxN.inacc n
      add := fun _ _ hx hy => RxN.add hx hy
      phi := fun _ _ hx hy => RxN.phi hx hy
      om := fun _ hx => RxN.om hx
      psiS := fun s w hs0 hs hw hwξ => IH w hwξ hw (Om (s + 1)) (InR_Om_succ s)
        (fun h => hs0 (by have h' : s < 1 := (Om_inj.1 h) ▸ lt_add_one s; exact Order.lt_one_iff.1 h'))
        (RxN.om (RxN.succ hs))
      psiI := fun n w hw hwξ => IH w hwξ hw (S.I n) (InR_I n) (rxI_ne_Om1 n) (RxN.inacc n)
      lt := fun _ hx => rxN_lt_Lam hTL hx }
  have hL : ξ < S.Lam := rxN_lt_Lam hTL hξ
  have hTg : T ≤ S.psi ξ π := hT1.trans (rxOm1_le_psi hπ hπ1)
  have hQ := (rxMQ_of_mem_N (e := ξ) (g := S.psi ξ π) hT hTg hξ).1
  have hM : RxN S T (S.M ξ (S.psi ξ π) ξ) := rxM_mem_of_Good hT ξ hL hQ.1
  have hself := M_mem_self hπ hL
  have heq := psi_M_eq hπ hL
  rw [← heq]
  exact RxN.psi hπ hπ1 hπN hM hself

/-- **`HCl S a T ⊆ RxN S T`** for `T ≤ Ω₁`. -/
theorem rxN_of_HCl {a x : Ordinal.{0}} (hT1 : T ≤ Om 1) (hx : HCl S a T x) : RxN S T x := by
  induction hx with
  | small h => exact RxN.small h
  | zero => exact RxN.zero
  | inacc n => exact RxN.inacc n
  | inaccW => exact RxN.inaccW
  | add _ _ ihx ihy => exact RxN.add ihx ihy
  | phi _ _ ihx ihy => exact RxN.phi ihx ihy
  | om _ ih => exact RxN.om ih
  | @coll π e hπ hπ1 _ _ _ ihπ ihe => exact rxN_psi hT1 e ihe π hπ hπ1 ihπ

end Googology.Trans.PoR.InaccPsi.R2.Rx
