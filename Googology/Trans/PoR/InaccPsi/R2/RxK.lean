import Googology.Trans.PoR.InaccPsi.R2.RyHi

/-!
# The level shift `κ` on the codes with normal `ψ_{Ω₂}`-atoms

`Θ = gxTh Z At` (the reading of the codes over a strongly critical `Z < Ω₁` with the atoms `At`),
`W = min(Θ(Ω₂), Ω₁)`, `ψ₂ = ψ_{Ω₂}`, `ψ₃ = ψ_{Ω₃}`, `ruInv` the inverse reading of `Ru.ruInv`.

* `RxC S T` (**the codes over `T` with normal `ψ₂`-atoms**): the least set with every `x < T`, `Ω₁`, closed
  under `+` and `φ`, and containing `ψ₂(d)` for every member `d` with `d < ψ₂(d)`; `rxAt S T` its atoms;
* `rxD S s` (**the normal argument**: the `d < s` with `ψ₂(d) = s`; `rxD_eq`: it is unique);
* `rxK S Z At` (**the level shift**): `ruInv` below `Ω₁`, `Ω₁ ↦ Ω₂`, `ψ₂(d) ↦ ψ₃(κ d)` at a strongly critical
  `s = ψ₂(d)`, `d = rxD s < s`, and `κ` commutes with the Cantor normal form and with `φ` at the other
  `ε`-numbers (the clauses of `Ru.ruK`, which `κ` extends by the atoms `ψ₂(d)`);
* `rxK_mono` (**`κ` is strictly increasing on `RxC S W`**), `rxK_mem` (**`κ ζ ∈ Cl(a, b)`** for a code `ζ` over
  `T ≤ W` when `Ω₃ ≤ a` and every `ruInv g`, `g < T`, is in `Cl(a, b)`), `rxK_lt_Om3` (`κ ζ < Ω₃`),
  `rxK_lt_psi3` (`κ ζ < ψ₃(Y)` for `Y ≥ Ω₃`), `rxK_ge`, `rxK_pos`, `rxK_atom`.

No new axiom.  New definitions: `RxC`, `rxAt`, `rxD`, `rxK`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Ru

/-- **The codes over `T` with normal `ψ_{Ω₂}`-atoms.** -/
inductive RxC (S : InaccSeq.{0}) (T : Ordinal.{0}) : Ordinal.{0} → Prop
  | small {x : Ordinal.{0}} : x < T → RxC S T x
  | om : RxC S T (Om 1)
  | psi {d : Ordinal.{0}} : RxC S T d → d < S.psi d (Om (1 + 1)) → RxC S T (S.psi d (Om (1 + 1)))
  | add {x y : Ordinal.{0}} : RxC S T x → RxC S T y → RxC S T (x + y)
  | phi {x y : Ordinal.{0}} : RxC S T x → RxC S T y → RxC S T (veblen x y)

/-- The atoms of `RxC S T`. -/
def rxAt (S : InaccSeq.{0}) (T : Ordinal.{0}) : Set Ordinal.{0} :=
  {s | ∃ d, RxC S T d ∧ d < S.psi d (Om (1 + 1)) ∧ s = S.psi d (Om (1 + 1))}

/-- **The normal argument** of `s`: the `d < s` with `ψ_{Ω₂}(d) = s`. -/
noncomputable def rxD (S : InaccSeq.{0}) (s : Ordinal.{0}) : Ordinal.{0} :=
  sInf {d | d < s ∧ S.psi d (Om (1 + 1)) = s}

open Classical in
/-- **The level shift.** -/
noncomputable def rxK (S : InaccSeq.{0}) (Z : Ordinal.{0}) (At : Set Ordinal.{0}) (ζ : Ordinal.{0}) :
    Ordinal.{0} :=
  if _h1 : ζ < Om 1 then ruInv Z At ζ
  else if ζ = Om 1 then Om (1 + 1)
  else if _h2 : SC ζ ∧ rxD S ζ < ζ then S.psi (rxK S Z At (rxD S ζ)) (Om (1 + 1 + 1))
  else if _h3 : log ω ζ < ζ then
    ω ^ rxK S Z At (log ω ζ) * (ζ / ω ^ log ω ζ) + rxK S Z At (ζ % ω ^ log ω ζ)
  else if _h4 : invVeblen₁ ζ < ζ ∧ invVeblen₂ ζ < ζ then
    veblen (rxK S Z At (invVeblen₁ ζ)) (rxK S Z At (invVeblen₂ ζ))
  else 0
termination_by ζ
decreasing_by
  · exact _h2.2
  · exact _h3
  · exact mod_opow_log_lt_self ω (((Om_pos one_ne_zero).trans_le (not_lt.1 _h1)).ne')
  · exact _h4.1
  · exact _h4.2

variable {S : InaccSeq.{0}}

section Codes

variable {T : Ordinal.{0}}

theorem RxC.mono {T' : Ordinal.{0}} (h : T ≤ T') {x : Ordinal.{0}} (hx : RxC S T x) : RxC S T' x := by
  induction hx with
  | small h' => exact RxC.small (lt_of_lt_of_le h' h)
  | om => exact RxC.om
  | psi _ hd ih => exact RxC.psi ih hd
  | add _ _ ihx ihy => exact RxC.add ihx ihy
  | phi _ _ ihx ihy => exact RxC.phi ihx ihy

theorem RxC.zero (hT : 0 < T) : RxC S T 0 := RxC.small hT

theorem RxC.opow (hT : 0 < T) {c : Ordinal.{0}} (h : RxC S T c) : RxC S T (ω ^ c) := by
  have := RxC.phi (RxC.zero (S := S) hT) h; rwa [veblen_zero_apply] at this

theorem RxC.mul_nat (hT : 0 < T) {x : Ordinal.{0}} (h : RxC S T x) : ∀ n : ℕ, RxC S T (x * n)
  | 0 => by simpa using RxC.zero (S := S) hT
  | n + 1 => by
    rw [Nat.cast_succ, mul_add_one]
    exact RxC.add (RxC.mul_nat hT h n) h

theorem rxC_gx {x : Ordinal.{0}} (hx : RxC S T x) : GxCl T (rxAt S T) x := by
  induction hx with
  | small h => exact GxCl.small h
  | om => exact GxCl.om
  | @psi d hd hlt _ => exact GxCl.atom ⟨d, hd, hlt, rfl⟩
  | add _ _ ihx ihy => exact GxCl.add ihx ihy
  | phi _ _ ihx ihy => exact GxCl.phi ihx ihy

theorem rxC_of_gx {x : Ordinal.{0}} (hx : GxCl T (rxAt S T) x) : RxC S T x := by
  induction hx with
  | small h => exact RxC.small h
  | om => exact RxC.om
  | atom hs =>
    obtain ⟨d, hd, hlt, rfl⟩ := hs
    exact RxC.psi hd hlt
  | add _ _ ihx ihy => exact RxC.add ihx ihy
  | phi _ _ ihx ihy => exact RxC.phi ihx ihy

theorem rxAt_GxAt (T : Ordinal.{0}) : GxAt (rxAt S T) := by
  rintro s ⟨d, -, -, rfl⟩
  exact ⟨SC_psi (InR_Om_succ 1) d, (psiS_bounds (S := S) d 1).1⟩

/-- **Decomposition** (`Mx.gxDec`). -/
theorem rxDec (hT : SC T) : ∀ w, RxC S T w →
    (∀ x, RxC S T x → x ≤ w → RxC S T (w - x)) ∧ RxC S T (log ω w) := fun w hw => by
  have h := gxDec hT (rxAt_GxAt T) w (rxC_gx hw)
  exact ⟨fun x hx hxw => rxC_of_gx (h.1 x (rxC_gx hx) hxw), rxC_of_gx h.2⟩

/-- **The Veblen decomposition** (`Mx.gxDecV`). -/
theorem rxDecV (hT : 0 < T) {x : Ordinal.{0}} (hx : RxC S T x) :
    ∀ a b, veblen a b = x → b < x → RxC S T a ∧ RxC S T b := fun a b e hb => by
  have h := gxDecV hT (rxAt_GxAt T) (rxC_gx hx) a b e hb
  exact ⟨rxC_of_gx h.1, rxC_of_gx h.2⟩

/-- A countable code over a strongly critical `T` is below `T`. -/
theorem rxC_lt_of_lt_Om1 (hT : SC T) {x : Ordinal.{0}} (hx : RxC S T x) (h : x < Om 1) : x < T :=
  GxCl.lt_of_lt_Om1 hT (rxAt_GxAt T) (rxC_gx hx) h

/-- **A strongly critical code above `Ω₁` is an atom** (for `T ≤ Ω₁`). -/
theorem rxSC_atom (hT1 : T ≤ Om 1) {x : Ordinal.{0}} (hx : RxC S T x) (hs : SC x) (h1 : Om 1 < x) :
    ∃ d, RxC S T d ∧ d < S.psi d (Om (1 + 1)) ∧ x = S.psi d (Om (1 + 1)) := by
  induction hx with
  | small h => exact absurd ((h.trans_le hT1).trans h1) (lt_irrefl _)
  | om => exact absurd h1 (lt_irrefl _)
  | @psi d hd hlt _ => exact ⟨d, hd, hlt, rfl⟩
  | @add u v _ _ ihu ihv =>
    rcases eq_or_ne v 0 with rfl | hv0
    · rw [add_zero] at hs h1 ⊢; exact ihu hs h1
    · have hu' : u < u + v := lt_add_of_pos_right u (pos_iff_ne_zero.2 hv0)
      have hvv : v = u + v := by
        rcases (le_add_self : v ≤ u + v).lt_or_eq with h | h
        · exact absurd (hs.isPrincipal hu' h) (lt_irrefl _)
        · exact h
      rw [← hvv] at hs h1 ⊢
      exact ihv hs h1
  | @phi a b _ _ iha ihb =>
    by_cases ha : a < veblen a b
    · by_cases hb : b < veblen a b
      · exact absurd (hs.2 a ha b hb) (lt_irrefl _)
      · have e : b = veblen a b := le_antisymm (right_le_veblen _ _) (not_lt.1 hb)
        rw [← e] at hs h1 ⊢
        exact ihb hs h1
    · have e : a = veblen a b := le_antisymm (left_le_veblen _ _) (not_lt.1 ha)
      rw [← e] at hs h1 ⊢
      exact iha hs h1

end Codes

/-- **The normal argument is unique**: `d < ψ₂(d)` gives `rxD (ψ₂ d) = d`. -/
theorem rxD_eq {d : Ordinal.{0}} (hd : d < S.psi d (Om (1 + 1))) : rxD S (S.psi d (Om (1 + 1))) = d := by
  refine le_antisymm (csInf_le' ⟨hd, rfl⟩) (le_csInf ⟨d, hd, rfl⟩ fun d' hd' => ?_)
  obtain ⟨h1, h2⟩ := hd'
  by_contra hlt
  have hlt' : d' < d := not_le.1 hlt
  have := psi_lt_psi_of_mem (S := S) (InR_Om_succ 1) hlt' (CSet.of_lt h1)
  rw [h2] at this
  exact lt_irrefl _ this

section Eqn

variable {Z : Ordinal.{0}} {At : Set Ordinal.{0}}

theorem rxK_lt_Om1 {ζ : Ordinal.{0}} (h : ζ < Om 1) : rxK S Z At ζ = ruInv Z At ζ := by
  rw [rxK, dif_pos h]

theorem rxK_Om1 : rxK S Z At (Om 1) = Om (1 + 1) := by
  rw [rxK, dif_neg (lt_irrefl _), if_pos rfl]

theorem rxK_zero (hZ0 : 0 < Z) : rxK S Z At 0 = 0 := by
  rw [rxK_lt_Om1 (Om_pos one_ne_zero), ruInv_zero hZ0]

/-- **`κ(ψ₂(d)) = ψ₃(κ d)`** at a normal argument `d < ψ₂(d)`. -/
theorem rxK_atom {d : Ordinal.{0}} (hd : d < S.psi d (Om (1 + 1))) :
    rxK S Z At (S.psi d (Om (1 + 1))) = S.psi (rxK S Z At d) (Om (1 + 1 + 1)) := by
  have h1 : Om 1 < S.psi d (Om (1 + 1)) := (psiS_bounds (S := S) d 1).1
  have hD := rxD_eq hd
  have h2 : SC (S.psi d (Om (1 + 1))) ∧ rxD S (S.psi d (Om (1 + 1))) < S.psi d (Om (1 + 1)) :=
    ⟨SC_psi (InR_Om_succ 1) d, by rw [hD]; exact hd⟩
  rw [rxK, dif_neg (not_lt.2 h1.le), if_neg h1.ne', dif_pos h2, hD]

theorem rxK_gt {ζ : Ordinal.{0}} (h1 : Om 1 < ζ) (h3 : log ω ζ < ζ) :
    rxK S Z At ζ = ω ^ rxK S Z At (log ω ζ) * (ζ / ω ^ log ω ζ) + rxK S Z At (ζ % ω ^ log ω ζ) := by
  have h2 : ¬ (SC ζ ∧ rxD S ζ < ζ) := fun h => by
    rw [ruLog_eps (gg_SC_eps h.1)] at h3; exact lt_irrefl _ h3
  rw [rxK, dif_neg (not_lt.2 h1.le), if_neg h1.ne', dif_neg h2, dif_pos h3]

theorem rxK_veb {ζ : Ordinal.{0}} (h1 : Om 1 < ζ) (hε : ω ^ ζ = ζ) (hS : ¬ SC ζ)
    (h4 : invVeblen₁ ζ < ζ ∧ invVeblen₂ ζ < ζ) :
    rxK S Z At ζ = veblen (rxK S Z At (invVeblen₁ ζ)) (rxK S Z At (invVeblen₂ ζ)) := by
  rw [rxK, dif_neg (not_lt.2 h1.le), if_neg h1.ne', dif_neg (fun h => hS h.1),
    dif_neg (by rw [ruLog_eps hε]; exact lt_irrefl _), dif_pos h4]

end Eqn

/-- **The Veblen normal form of an `ε`-number above `Ω₁` that is not strongly critical.** -/
theorem rxVeb {ζ : Ordinal.{0}} (h1 : Om 1 < ζ) (hε : ω ^ ζ = ζ) (hS : ¬ SC ζ) :
    veblen (invVeblen₁ ζ) (invVeblen₂ ζ) = ζ ∧ 0 < invVeblen₁ ζ ∧ invVeblen₁ ζ < ζ ∧
      invVeblen₂ ζ < ζ := by
  have hv : veblen (invVeblen₁ ζ) (invVeblen₂ ζ) = ζ := by rw [veblen_invVeblen₁_invVeblen₂, hε]
  have hb : invVeblen₂ ζ < ζ := by have := invVeblen₂_lt ζ; rwa [hε] at this
  have hpos : 0 < ζ := (Om_pos one_ne_zero).trans h1
  refine ⟨hv, ?_, ?_, hb⟩
  · refine pos_iff_ne_zero.2 fun h0 => ?_
    rw [h0, veblen_zero_apply] at hv
    have : invVeblen₂ ζ = ζ := by
      have h2 : ω ^ invVeblen₂ ζ = ω ^ ζ := hv.trans hε.symm
      exact (opow_right_inj one_lt_omega0).1 h2
    exact absurd this hb.ne
  · refine lt_of_le_of_ne (invVeblen₁_le ζ) fun e => ?_
    rw [e] at hv
    have hle : veblen ζ 0 ≤ ζ := (veblen_le_veblen_iff_right.2 zero_le).trans hv.le
    exact hS (ruSC_of_veblen hpos (le_antisymm hle (left_le_veblen ζ 0)))

section K

variable {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1) (hAt : GxAt At)

/-- The bound of the domain: `W = min(Θ(Ω₂), Ω₁)`. -/
noncomputable abbrev rxW (Z : Ordinal.{0}) (At : Set Ordinal.{0}) : Ordinal.{0} :=
  min (gxTh Z At (Om (1 + 1))) (Om 1)

/-- **An atom of the domain.** -/
theorem rxAtomD {ζ : Ordinal.{0}} (hζ : RxC S (rxW Z At) ζ) (hS : SC ζ) (h1 : Om 1 < ζ) :
    ∃ d, RxC S (rxW Z At) d ∧ d < S.psi d (Om (1 + 1)) ∧ ζ = S.psi d (Om (1 + 1)) :=
  rxSC_atom (min_le_right _ _) hζ hS h1

theorem rxOm2_lt_Om3 : Om (1 + 1 : Ordinal.{0}) < Om (1 + 1 + 1) := Om_lt_Om.2 (lt_add_one _)

include hZ hZ1 hAt

theorem rxW_SC : SC (rxW Z At) := by
  rcases le_total (gxTh Z At (Om (1 + 1))) (Om 1) with h | h
  · rw [rxW, min_eq_left h]; exact ruZ2_SC hZ hZ1 hAt
  · rw [rxW, min_eq_right h]; exact Ph.ph_SC_Om1

/-- **The Cantor normal form of a member of the domain `≥ Ω₁` and its parts.** -/
theorem rxCNF {ζ : Ordinal.{0}} (hζ : RxC S (rxW Z At) ζ) (h1 : Om 1 ≤ ζ) :
    ∃ n : ℕ, 1 ≤ n ∧ ζ / ω ^ log ω ζ = n ∧ ζ = ω ^ log ω ζ * n + ζ % ω ^ log ω ζ ∧
      RxC S (rxW Z At) (log ω ζ) ∧ RxC S (rxW Z At) (ζ % ω ^ log ω ζ) ∧
      RxC S (rxW Z At) (ω ^ log ω ζ) ∧
      ζ % ω ^ log ω ζ < ω ^ log ω ζ ∧ ω ^ log ω ζ ≤ ζ ∧ Om 1 ≤ log ω ζ := by
  have hW := rxW_SC hZ hZ1 hAt
  have h0 : ζ ≠ 0 := ((Om_pos one_ne_zero).trans_le h1).ne'
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt ζ one_lt_omega0)
  have hpos : (0 : Ordinal.{0}) < ω ^ log ω ζ := opow_pos _ omega0_pos
  have hopζ : ω ^ log ω ζ ≤ ζ := opow_log_le_self ω h0
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      have hlt : ζ < ω ^ log ω ζ * 1 :=
        (Ordinal.lt_mul_iff_div_lt hpos.ne').2 (by rw [hn, h]; exact zero_lt_one)
      rw [mul_one] at hlt
      exact absurd hopζ (not_le.2 hlt)
    · exact h
  have hdm : ζ = ω ^ log ω ζ * n + ζ % ω ^ log ω ζ := by
    rw [← hn]; exact (Ordinal.div_add_mod ζ _).symm
  have hℓ1 : Om 1 ≤ log ω ζ := le_log_of_opow_le one_lt_omega0 (by rw [Om1_opow]; exact h1)
  have hlog : RxC S (rxW Z At) (log ω ζ) := (rxDec hW ζ hζ).2
  have hopow : RxC S (rxW Z At) (ω ^ log ω ζ) := RxC.opow hW.1 hlog
  have hmul : RxC S (rxW Z At) (ω ^ log ω ζ * n) := RxC.mul_nat hW.1 hopow n
  have hrem : RxC S (rxW Z At) (ζ % ω ^ log ω ζ) := by
    have := (rxDec hW ζ hζ).1 _ hmul (le_self_add.trans_eq hdm.symm)
    have e : ζ - ω ^ log ω ζ * n = ζ % ω ^ log ω ζ := by
      have e0 := Ordinal.add_sub_cancel (ω ^ log ω ζ * n) (ζ % ω ^ log ω ζ)
      rwa [← hdm] at e0
    rwa [e] at this
  exact ⟨n, hn1, hn, hdm, hlog, hrem, hopow, Ordinal.mod_lt ζ hpos.ne', hopζ, hℓ1⟩

/-- **The Veblen normal form of a non-strongly-critical `ε`-number of the domain above `Ω₁`.** -/
theorem rxEpsD {ζ : Ordinal.{0}} (hζ : RxC S (rxW Z At) ζ) (h1 : Om 1 < ζ) (hε : ω ^ ζ = ζ)
    (hS : ¬ SC ζ) :
    veblen (invVeblen₁ ζ) (invVeblen₂ ζ) = ζ ∧ 0 < invVeblen₁ ζ ∧ invVeblen₁ ζ < ζ ∧
      invVeblen₂ ζ < ζ ∧ RxC S (rxW Z At) (invVeblen₁ ζ) ∧ RxC S (rxW Z At) (invVeblen₂ ζ) ∧
      rxK S Z At ζ = veblen (rxK S Z At (invVeblen₁ ζ)) (rxK S Z At (invVeblen₂ ζ)) := by
  obtain ⟨hv, ha0, ha, hb⟩ := rxVeb h1 hε hS
  obtain ⟨hga, hgb⟩ := rxDecV (rxW_SC hZ hZ1 hAt).1 hζ _ _ hv hb
  exact ⟨hv, ha0, ha, hb, hga, hgb, rxK_veb h1 hε hS ⟨ha, hb⟩⟩

/-- **`Ω₂ ≤ κ ζ` for `ζ ≥ Ω₁` in the domain.** -/
theorem rxK_ge : ∀ ζ, RxC S (rxW Z At) ζ → Om 1 ≤ ζ → Om (1 + 1) ≤ rxK S Z At ζ := by
  intro ζ
  induction ζ using WellFoundedLT.induction with
  | ind ζ IH =>
  intro hζ h1
  rcases h1.lt_or_eq with h1 | e
  swap
  · rw [← e, rxK_Om1]
  by_cases hS : SC ζ
  · obtain ⟨d, -, hd, rfl⟩ := rxAtomD hζ hS h1
    rw [rxK_atom hd]
    exact (psiS_bounds (S := S) _ (1 + 1)).1.le
  by_cases hε : ω ^ ζ = ζ
  · obtain ⟨hv, -, ha, hb, haD, hbD, hK⟩ := rxEpsD hZ hZ1 hAt hζ h1 hε hS
    rw [hK]
    by_cases hab : Om 1 ≤ invVeblen₁ ζ
    · exact (IH _ ha haD hab).trans (left_le_veblen _ _)
    · by_cases hbb : Om 1 ≤ invVeblen₂ ζ
      · exact (IH _ hb hbD hbb).trans (right_le_veblen _ _)
      · push Not at hab hbb
        have := Ph.ph_SC_Om1.2 _ hab _ hbb
        rw [hv] at this
        exact absurd h1 (not_lt.2 this.le)
  · obtain ⟨n, hn1, hn, -, hℓ, -, -, -, -, hℓ1⟩ := rxCNF hZ hZ1 hAt hζ h1.le
    have hlt := ruLog_lt h1 hε
    rw [rxK_gt h1 hlt, hn]
    calc Om (1 + 1) = ω ^ Om (1 + 1) := ruOm2_eps.symm
      _ ≤ ω ^ rxK S Z At (log ω ζ) := opow_le_opow_right omega0_pos (IH _ hlt hℓ hℓ1)
      _ ≤ ω ^ rxK S Z At (log ω ζ) * n := le_mul_left _ (by exact_mod_cast hn1)
      _ ≤ _ := le_self_add

theorem rxK_ne_zero {ζ : Ordinal.{0}} (hζ : RxC S (rxW Z At) ζ) (h0 : ζ ≠ 0) : rxK S Z At ζ ≠ 0 := by
  rcases lt_or_ge ζ (Om 1) with h1 | h1
  · rw [rxK_lt_Om1 h1]
    intro e
    have hlt : ζ < gxTh Z At (Om (1 + 1)) :=
      (rxC_lt_of_lt_Om1 (rxW_SC hZ hZ1 hAt) hζ h1).trans_le (min_le_left _ _)
    obtain ⟨-, -, he⟩ := ruInv_spec hlt
    rw [e, gxTh_zero] at he
    exact h0 he.symm
  · exact ((Om_pos (by norm_num)).trans_le (rxK_ge hZ hZ1 hAt ζ hζ h1)).ne'

theorem rxK_pos {ζ : Ordinal.{0}} (hζ : RxC S (rxW Z At) ζ) (h0 : ζ ≠ 0) : 0 < rxK S Z At ζ :=
  pos_iff_ne_zero.2 (rxK_ne_zero hZ hZ1 hAt hζ h0)

omit hZ hZ1 hAt in
/-- **`κ` keeps the strongly critical ordinals `≥ Ω₁` of the domain.** -/
theorem rxK_SC {ζ : Ordinal.{0}} (hζ : RxC S (rxW Z At) ζ) (h1 : Om 1 ≤ ζ) (hS : SC ζ) :
    SC (rxK S Z At ζ) := by
  rcases h1.lt_or_eq with h1 | e
  · obtain ⟨d, -, hd, rfl⟩ := rxAtomD hζ hS h1
    rw [rxK_atom hd]; exact SC_psi (InR_Om_succ (1 + 1)) _
  · rw [← e, rxK_Om1]; exact ldOm2_SC

/-- **`κ` keeps `ε`-numbers** at and above `Ω₁`. -/
theorem rxK_eps {ζ : Ordinal.{0}} (hζ : RxC S (rxW Z At) ζ) (h1 : Om 1 ≤ ζ) (hε : ω ^ ζ = ζ) :
    ω ^ rxK S Z At ζ = rxK S Z At ζ := by
  by_cases hS : SC ζ
  · exact gg_SC_eps (rxK_SC hζ h1 hS)
  rcases h1.lt_or_eq with h1 | e
  · obtain ⟨-, ha0, -, -, haD, -, hK⟩ := rxEpsD hZ hZ1 hAt hζ h1 hε hS
    rw [hK]
    exact gg_veblen_eps (rxK_ne_zero hZ hZ1 hAt haD ha0.ne')
  · exact absurd (e ▸ Ph.ph_SC_Om1) hS

/-- **The lift on the Cantor normal form** of a member of the domain `≥ Ω₁`. -/
theorem rxDecK {ζ : Ordinal.{0}} (hζ : RxC S (rxW Z At) ζ) (h1 : Om 1 ≤ ζ) :
    ∃ n : ℕ, 1 ≤ n ∧ ζ = ω ^ log ω ζ * n + ζ % ω ^ log ω ζ ∧
      rxK S Z At ζ = ω ^ rxK S Z At (log ω ζ) * n + rxK S Z At (ζ % ω ^ log ω ζ) ∧
      RxC S (rxW Z At) (log ω ζ) ∧ RxC S (rxW Z At) (ζ % ω ^ log ω ζ) ∧
      RxC S (rxW Z At) (ω ^ log ω ζ) ∧
      ζ % ω ^ log ω ζ < ω ^ log ω ζ ∧ ω ^ log ω ζ ≤ ζ ∧ Om 1 ≤ log ω ζ ∧
      (ω ^ ζ = ζ ∨ log ω ζ < ζ) := by
  obtain ⟨n, hn1, hn, hdm, hℓ, hr, hop, hrlt, hopζ, hℓ1⟩ := rxCNF hZ hZ1 hAt hζ h1
  by_cases hε : ω ^ ζ = ζ
  · have hl := ruLog_eps hε
    have en : (n : Ordinal.{0}) = 1 := by
      rw [← hn, hl, hε, Ordinal.div_self ((Om_pos one_ne_zero).trans_le h1).ne']
    refine ⟨n, hn1, hdm, ?_, hℓ, hr, hop, hrlt, hopζ, hℓ1, Or.inl hε⟩
    rw [en, hl, hε, Ordinal.mod_self, rxK_zero hZ.1, add_zero, mul_one, rxK_eps hZ hZ1 hAt hζ h1 hε]
  · have hgt : Om 1 < ζ := lt_of_le_of_ne h1 fun e => hε (by rw [← e]; exact Om1_opow)
    refine ⟨n, hn1, hdm, ?_, hℓ, hr, hop, hrlt, hopζ, hℓ1, Or.inr (ruLog_lt hgt hε)⟩
    rw [← hn]; exact rxK_gt hgt (ruLog_lt hgt hε)

/-- **The lift on the Veblen normal form** of an `ε`-number of the domain `≥ Ω₁`. -/
theorem rxDecV' {ζ : Ordinal.{0}} (hζ : RxC S (rxW Z At) ζ) (h1 : Om 1 ≤ ζ) (hε : ω ^ ζ = ζ) :
    ∃ a b, veblen a b = ζ ∧ b < ζ ∧ a ≤ ζ ∧ RxC S (rxW Z At) a ∧ RxC S (rxW Z At) b ∧
      rxK S Z At ζ = veblen (rxK S Z At a) (rxK S Z At b) ∧ (¬ SC ζ → a < ζ) := by
  have hW := rxW_SC hZ hZ1 hAt
  by_cases hS : SC ζ
  · have hK := rxK_SC hζ h1 hS
    refine ⟨ζ, 0, hS.veblen_zero, hS.1, le_rfl, hζ, RxC.zero hW.1, ?_, fun h => absurd hS h⟩
    rw [rxK_zero hZ.1, hK.veblen_zero]
  · have h1' : Om 1 < ζ := lt_of_le_of_ne h1 fun e => hS (e ▸ Ph.ph_SC_Om1)
    obtain ⟨hv, -, ha, hb, haD, hbD, hK⟩ := rxEpsD hZ hZ1 hAt hζ h1' hε hS
    exact ⟨_, _, hv, hb, ha.le, haD, hbD, hK, fun _ => ha⟩

/-- **`κ(ω^ℓ) = ω^{κ ℓ}`** for `ℓ ≥ Ω₁` in the domain. -/
theorem rxK_opow {ℓ : Ordinal.{0}} (hℓ : RxC S (rxW Z At) ℓ) (h1 : Om 1 ≤ ℓ) :
    rxK S Z At (ω ^ ℓ) = ω ^ rxK S Z At ℓ := by
  by_cases hε : ω ^ ω ^ ℓ = ω ^ ℓ
  · have e : ω ^ ℓ = ℓ := (opow_right_inj one_lt_omega0).1 hε
    rw [e]; exact (rxK_eps hZ hZ1 hAt hℓ h1 e).symm
  · have hgt : Om 1 < ω ^ ℓ := lt_of_le_of_ne (h1.trans (right_le_opow ℓ one_lt_omega0))
      fun e => hε (by rw [← e]; exact Om1_opow)
    have hlog : log ω (ω ^ ℓ) = ℓ := log_opow one_lt_omega0 ℓ
    rw [rxK_gt hgt (ruLog_lt hgt hε), hlog, Ordinal.div_self (opow_pos ℓ omega0_pos).ne',
      Ordinal.mod_self, rxK_zero hZ.1, add_zero, mul_one]

/-- **A bound from the parts**: for a non-strongly-critical `ζ > Ω₁` of the domain and a strongly critical `X`,
`κ ζ < X` once `κ y < X` for the members `y < ζ` of the domain. -/
theorem rxK_step_lt {X ζ : Ordinal.{0}} (hX : SC X) (hζ : RxC S (rxW Z At) ζ) (h1 : Om 1 < ζ)
    (hS : ¬ SC ζ) (IH : ∀ y < ζ, RxC S (rxW Z At) y → rxK S Z At y < X) : rxK S Z At ζ < X := by
  by_cases hε : ω ^ ζ = ζ
  · obtain ⟨-, -, ha, hb, haD, hbD, hK⟩ := rxEpsD hZ hZ1 hAt hζ h1 hε hS
    rw [hK]; exact hX.2 _ (IH _ ha haD) _ (IH _ hb hbD)
  obtain ⟨n, -, hn, -, hℓ, hr, -, -, -, -⟩ := rxCNF hZ hZ1 hAt hζ h1.le
  have hlt := ruLog_lt h1 hε
  have hrlt : ζ % ω ^ log ω ζ < ζ := mod_opow_log_lt_self ω ((Om_pos one_ne_zero).trans h1).ne'
  rw [rxK_gt h1 hlt, hn]
  have h1m := IH _ hlt hℓ
  have hop : ω ^ rxK S Z At (log ω ζ) < X := by
    rw [← gg_SC_eps hX]; exact (opow_lt_opow_iff_right one_lt_omega0).2 h1m
  exact hX.isPrincipal (ldMul_lt_SC hX hop ((natCast_lt_omega0 n).trans (Lw.lw_omega_lt_SC hX)))
    (IH _ hrlt hr)

/-- **`κ ζ < Ω₃`** on the domain. -/
theorem rxK_lt_Om3 : ∀ ζ, RxC S (rxW Z At) ζ → rxK S Z At ζ < Om (1 + 1 + 1) := by
  have hW := rxW_SC hZ hZ1 hAt
  have h3 : SC (Om (1 + 1 + 1 : Ordinal.{0})) := SC_Om (by
    intro h; exact absurd h (ne_of_gt (lt_of_lt_of_le zero_lt_one le_add_self)))
  intro ζ
  induction ζ using WellFoundedLT.induction with
  | ind ζ IH =>
  intro hζ
  rcases lt_or_ge ζ (Om 1) with h1 | h1
  · rw [rxK_lt_Om1 h1]
    have hlt : ζ < gxTh Z At (Om (1 + 1)) := (rxC_lt_of_lt_Om1 hW hζ h1).trans_le (min_le_left _ _)
    exact (ruInv_spec hlt).2.1.trans rxOm2_lt_Om3
  rcases h1.lt_or_eq with h1 | e
  swap
  · rw [← e, rxK_Om1]; exact rxOm2_lt_Om3
  by_cases hS : SC ζ
  · obtain ⟨d, -, hd, rfl⟩ := rxAtomD hζ hS h1
    rw [rxK_atom hd]; exact psi_lt (InR_Om_succ (1 + 1)) _
  · exact rxK_step_lt hZ hZ1 hAt h3 hζ h1 hS IH

/-- **`κ ζ ∈ Cl(a, b)`** for a code `ζ` over `T ≤ W`, when `Ω₃ ≤ a` and every `ruInv g`, `g < T`, is in
`Cl(a, b)`. -/
theorem rxK_mem {T a b : Ordinal.{0}} (hT : SC T) (hTW : T ≤ rxW Z At) (ha : Om (1 + 1 + 1) ≤ a)
    (hinv : ∀ g, g < T → ruInv Z At g ∈ S.CSet a b) :
    ∀ ζ, RxC S T ζ → rxK S Z At ζ ∈ S.CSet a b := by
  intro ζ
  induction ζ using WellFoundedLT.induction with
  | ind ζ IH =>
  intro hζ
  have hD : RxC S (rxW Z At) ζ := hζ.mono hTW
  rcases lt_or_ge ζ (Om 1) with h1 | h1
  · rw [rxK_lt_Om1 h1]; exact hinv ζ (rxC_lt_of_lt_Om1 hT hζ h1)
  rcases h1.lt_or_eq with h1 | e
  swap
  · rw [← e, rxK_Om1]; exact mxOm2_mem a b
  by_cases hS : SC ζ
  · obtain ⟨d, hdT, hd, rfl⟩ := rxSC_atom (hTW.trans (min_le_right _ _)) hζ hS h1
    rw [rxK_atom hd]
    exact CSet.psi_mem ((rxK_lt_Om3 hZ hZ1 hAt d (hdT.mono hTW)).trans_le ha) (InR_Om_succ (1 + 1))
      (Ry.ryOm3_mem a b) (IH d hd hdT)
  by_cases hε : ω ^ ζ = ζ
  · obtain ⟨hv, -, ha', hb, -, -, hK⟩ := rxEpsD hZ hZ1 hAt hD h1 hε hS
    obtain ⟨hga, hgb⟩ := rxDecV hT.1 hζ _ _ hv hb
    rw [hK]
    exact CSet.phi_mem (IH _ ha' hga) (IH _ hb hgb)
  obtain ⟨n, -, hn, hdm, -, -, -, -, -, -⟩ := rxCNF hZ hZ1 hAt hD h1.le
  have hlt := ruLog_lt h1 hε
  have hlog : RxC S T (log ω ζ) := (rxDec hT ζ hζ).2
  have hmul : RxC S T (ω ^ log ω ζ * n) := RxC.mul_nat hT.1 (RxC.opow hT.1 hlog) n
  have hrem : RxC S T (ζ % ω ^ log ω ζ) := by
    have := (rxDec hT ζ hζ).1 _ hmul (le_self_add.trans_eq hdm.symm)
    have e : ζ - ω ^ log ω ζ * n = ζ % ω ^ log ω ζ := by
      have e0 := Ordinal.add_sub_cancel (ω ^ log ω ζ * n) (ζ % ω ^ log ω ζ)
      rwa [← hdm] at e0
    rwa [e] at this
  have hrlt : ζ % ω ^ log ω ζ < ζ := mod_opow_log_lt_self ω ((Om_pos one_ne_zero).trans h1).ne'
  rw [rxK_gt h1 hlt, hn]
  have h1m := IH _ hlt hlog
  have h2m := IH _ hrlt hrem
  have hop : ω ^ rxK S Z At (log ω ζ) ∈ S.CSet a b := by
    have := CSet.phi_mem (S := S) (CSet.zero_mem a b) h1m; rwa [veblen_zero_apply] at this
  exact CSet.add_mem (ConjT.mul_nat_mem S hop n) h2m

/-- **`κ ζ < ψ₃(Y)`** on the domain, for `Y ≥ Ω₃`. -/
theorem rxK_lt_psi3 {Y : Ordinal.{0}} (hY : Om (1 + 1 + 1) ≤ Y) :
    ∀ ζ, RxC S (rxW Z At) ζ → rxK S Z At ζ < S.psi Y (Om (1 + 1 + 1)) := by
  have hW := rxW_SC hZ hZ1 hAt
  have hX : SC (S.psi Y (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) _
  have h2X : Om (1 + 1 : Ordinal.{0}) < S.psi Y (Om (1 + 1 + 1)) := (psiS_bounds (S := S) Y (1 + 1)).1
  intro ζ
  induction ζ using WellFoundedLT.induction with
  | ind ζ IH =>
  intro hζ
  rcases lt_or_ge ζ (Om 1) with h1 | h1
  · rw [rxK_lt_Om1 h1]
    have hlt : ζ < gxTh Z At (Om (1 + 1)) := (rxC_lt_of_lt_Om1 hW hζ h1).trans_le (min_le_left _ _)
    exact (ruInv_spec hlt).2.1.trans h2X
  rcases h1.lt_or_eq with h1 | e
  swap
  · rw [← e, rxK_Om1]; exact h2X
  by_cases hS : SC ζ
  · obtain ⟨d, hdD, hd, rfl⟩ := rxAtomD hζ hS h1
    rw [rxK_atom hd]
    have hd3 := rxK_lt_Om3 hZ hZ1 hAt d hdD
    refine psi_lt_psi_of_mem (InR_Om_succ (1 + 1)) (hd3.trans_le hY) ?_
    refine rxK_mem hZ hZ1 hAt hW le_rfl hY (fun g hg => CSet.of_lt ?_) d hdD
    have hg' : g < gxTh Z At (Om (1 + 1)) := hg.trans_le (min_le_left _ _)
    exact (ruInv_spec hg').2.1.trans h2X
  · exact rxK_step_lt hZ hZ1 hAt hX hζ h1 hS IH

/-- **`κ` is strictly increasing on the domain.** -/
theorem rxK_mono : ∀ ζ, RxC S (rxW Z At) ζ → ∀ ζ', RxC S (rxW Z At) ζ' → ζ' < ζ →
    rxK S Z At ζ' < rxK S Z At ζ := by
  have hW := rxW_SC hZ hZ1 hAt
  have hcnt : ∀ y, RxC S (rxW Z At) y → y < Om 1 → y < gxTh Z At (Om (1 + 1)) := fun y hy h =>
    (rxC_lt_of_lt_Om1 hW hy h).trans_le (min_le_left _ _)
  have hinvlt : ∀ y, RxC S (rxW Z At) y → y < Om 1 → rxK S Z At y < Om (1 + 1) := fun y hy h => by
    rw [rxK_lt_Om1 h]; exact (ruInv_spec (hcnt y hy h)).2.1
  intro ζ
  induction ζ using WellFoundedLT.induction with
  | ind ζ IH =>
  intro hζ ζ'
  induction ζ' using WellFoundedLT.induction with
  | ind ζ' IH' =>
  intro hζ' hlt
  rcases lt_or_ge ζ (Om 1) with h1 | h1
  · rw [rxK_lt_Om1 h1, rxK_lt_Om1 (hlt.trans h1)]
    exact ruInv_lt (hcnt ζ hζ h1) hlt
  rcases lt_or_ge ζ' (Om 1) with h1' | h1'
  · exact (hinvlt ζ' hζ' h1').trans_le (rxK_ge hZ hZ1 hAt ζ hζ h1)
  have hζ1 : Om 1 < ζ := h1'.trans_lt hlt
  by_cases hS : SC ζ
  · -- `ζ = ψ₂(d)` an atom
    obtain ⟨d, hdD, hd, hζd⟩ := rxAtomD hζ hS hζ1
    have hKζ : rxK S Z At ζ = S.psi (rxK S Z At d) (Om (1 + 1 + 1)) := by rw [hζd, rxK_atom hd]
    have hX : SC (rxK S Z At ζ) := by rw [hKζ]; exact SC_psi (InR_Om_succ (1 + 1)) _
    by_cases hS' : SC ζ'
    · rcases h1'.lt_or_eq with h1'' | e
      · obtain ⟨d', hd'D, hd', hζd'⟩ := rxAtomD hζ' hS' h1''
        have hdd : d' < d := by
          by_contra hc
          have hc' : d ≤ d' := not_lt.1 hc
          have := (psi_mono (S := S) (InR_Om_succ 1) hc').1
          rw [← hζd, ← hζd'] at this
          exact absurd hlt (not_lt.2 this)
        have hdζ : d < ζ := by rw [hζd]; exact hd
        have hK : rxK S Z At d' < rxK S Z At d := IH d hdζ hdD d' hd'D hdd
        have hK' : rxK S Z At d' < S.psi (rxK S Z At d') (Om (1 + 1 + 1)) := by
          have hd'ζ' : d' < ζ' := by rw [hζd']; exact hd'
          have := IH ζ' hlt hζ' d' hd'D hd'ζ'
          rwa [hζd', rxK_atom hd'] at this
        rw [hKζ, hζd', rxK_atom hd']
        exact psi_lt_psi_of_mem (InR_Om_succ (1 + 1)) hK
          (CSet.of_lt (hK'.trans_le (psi_mono (S := S) (InR_Om_succ (1 + 1)) hK.le).1))
      · rw [← e, rxK_Om1, hKζ]; exact (psiS_bounds (S := S) _ (1 + 1)).1
    · have h1'' : Om 1 < ζ' := lt_of_le_of_ne h1' fun e => hS' (e ▸ Ph.ph_SC_Om1)
      exact rxK_step_lt hZ hZ1 hAt hX hζ' h1'' hS' fun y hy hyD => IH' y hy hyD (hy.trans hlt)
  by_cases hboth : ω ^ ζ = ζ ∧ ω ^ ζ' = ζ'
  · -- two `ε`-numbers: the Veblen comparison
    obtain ⟨a, b, hab, hb, -, haD, hbD, hK, hane⟩ := rxDecV' hZ hZ1 hAt hζ h1 hboth.1
    obtain ⟨a', b', hab', hb', ha'le, ha'D, hb'D, hK', -⟩ := rxDecV' hZ hZ1 hAt hζ' h1' hboth.2
    have ha : a < ζ := hane hS
    rw [hK, hK']
    have hlt' := hlt
    rw [← hab, ← hab'] at hlt'
    rcases veblen_lt_veblen_iff.1 hlt' with ⟨e, h⟩ | ⟨h, h2⟩ | ⟨h, h2⟩
    · rw [e]
      exact veblen_lt_veblen_iff_right.2 (IH b hb hbD b' hb'D h)
    · refine veblen_lt_veblen_iff.2 (Or.inr (Or.inl ⟨IH a ha haD a' ha'D h, ?_⟩))
      rw [← hK]
      exact IH' b' hb' hb'D (hb'.trans hlt)
    · refine veblen_lt_veblen_iff.2 (Or.inr (Or.inr ⟨IH a' (ha'le.trans_lt hlt) ha'D a haD h, ?_⟩))
      rw [← hK']
      rw [hab'] at h2
      exact IH b hb hbD ζ' hζ' h2
  · -- the Cantor normal form
    obtain ⟨n, hn1, hdm, hK, hℓ, hr, hop, hrlt, hopζ, hℓ1, hcase⟩ := rxDecK hZ hZ1 hAt hζ h1
    obtain ⟨n', hn1', hdm', hK', hℓ', hr', hop', hrlt', hopζ', hℓ1', hcase'⟩ := rxDecK hZ hZ1 hAt hζ' h1'
    have hℓle : log ω ζ' ≤ log ω ζ := log_mono_right ω hlt.le
    have hrb : rxK S Z At (ζ' % ω ^ log ω ζ') < ω ^ rxK S Z At (log ω ζ') := by
      rw [← rxK_opow hZ hZ1 hAt hℓ' hℓ1']
      exact IH _ (hopζ'.trans_lt hlt) hop' _ hr' hrlt'
    have hK'lt : rxK S Z At ζ' < ω ^ rxK S Z At (log ω ζ') * ((n' : Ordinal.{0}) + 1) := by
      rw [hK', mul_add_one]; exact (add_lt_add_iff_left _).2 hrb
    have hKζ : ω ^ rxK S Z At (log ω ζ) ≤ rxK S Z At ζ := by
      rw [hK]; exact (le_mul_left _ (by exact_mod_cast hn1)).trans le_self_add
    rcases hℓle.lt_or_eq with hℓlt | hℓeq
    · have hKℓ : rxK S Z At (log ω ζ') < rxK S Z At (log ω ζ) := by
        rcases hcase with hε | hℓζ
        · have hne' : ω ^ ζ' ≠ ζ' := fun h => hboth ⟨hε, h⟩
          have hℓ'ζ' : log ω ζ' < ζ' := by
            rcases hcase' with h | h
            · exact absurd h hne'
            · exact h
          rw [ruLog_eps hε]
          exact IH' _ hℓ'ζ' hℓ' (hℓ'ζ'.trans hlt)
        · exact IH _ hℓζ hℓ _ hℓ' hℓlt
      calc rxK S Z At ζ' < ω ^ rxK S Z At (log ω ζ') * ((n' : Ordinal.{0}) + 1) := hK'lt
        _ ≤ ω ^ rxK S Z At (log ω ζ') * ω := by
            gcongr; exact (Order.add_one_le_of_lt (natCast_lt_omega0 n')).trans_eq (by rfl)
        _ = ω ^ (rxK S Z At (log ω ζ') + 1) := (opow_add_one _ _).symm
        _ ≤ ω ^ rxK S Z At (log ω ζ) := opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hKℓ)
        _ ≤ rxK S Z At ζ := hKζ
    · rw [hℓeq] at hK'lt hdm' hrlt' hK'
      have hnle : n' ≤ n := by
        by_contra hc
        push Not at hc
        have h2 : ω ^ log ω ζ * ((n + 1 : ℕ) : Ordinal.{0}) ≤ ζ' := by
          rw [hdm']; exact (mul_le_mul_right (by exact_mod_cast hc) _).trans le_self_add
        have h3 : ζ < ω ^ log ω ζ * ((n + 1 : ℕ) : Ordinal.{0}) := by
          rw [Nat.cast_succ, mul_add_one]
          conv_lhs => rw [hdm]
          exact (add_lt_add_iff_left _).2 hrlt
        exact absurd (h3.trans_le h2) (not_lt.2 hlt.le)
      rcases hnle.lt_or_eq with hnlt | hneq
      · calc rxK S Z At ζ' < ω ^ rxK S Z At (log ω ζ) * ((n' : Ordinal.{0}) + 1) := hK'lt
          _ ≤ ω ^ rxK S Z At (log ω ζ) * n := by
              gcongr; exact_mod_cast Nat.succ_le_of_lt hnlt
          _ ≤ rxK S Z At ζ := by rw [hK]; exact le_self_add
      · subst hneq
        have hrr : ζ' % ω ^ log ω ζ < ζ % ω ^ log ω ζ := by
          have h4 := hlt
          rw [hdm, hdm'] at h4
          exact (add_lt_add_iff_left _).1 h4
        rw [hK, hK']
        refine (add_lt_add_iff_left _).2 (IH _ (hrlt.trans_le hopζ) hr _ ?_ hrr)
        rw [← hℓeq]; exact hr'

end K

end Googology.Trans.PoR.InaccPsi.R2.Rx
