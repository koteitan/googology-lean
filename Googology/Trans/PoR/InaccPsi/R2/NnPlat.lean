import Googology.Trans.PoR.InaccPsi.R2.FxPlat

/-!
# The window plateau of `P`, the prefix closure of the hull, and the hull of a good name

`θ = ψ_{Ω₂}(Ω_ω)`, `A_η = Ω_ω + θ·η`, `P(η) = ψ_{Ω₁}(A_η)` (`Nm.Pv`), `HCl S a Z` = `Cl(a, Z)` without the countable
collapses (`Bt.HCl`), `η` good when `η ∈ Cl(A_η + 1, P(η))` (`Bt.Good`).

* `nnHCl_pre` (**the `ω^u`-prefix of a hull member is in the hull**, every `u`): `x ∈ HCl(a, Z)` gives
  `ω^u·(x / ω^u) ∈ HCl(a, Z)` (`Fx.fxHCl_pre` is `u = Ω₁`);
* `nnShrink`, `nn_key`, `nnWPlat` (**THE WINDOW PLATEAU**): if no `β₀ + y''`, `y'' ≤ y`, lies in
  `HCl(A_{β₀}, P(β₀))`, then `HCl(A_{β₀+y} + 1, P(β₀)) ⊆ HCl(A_{β₀}, P(β₀))`, `P(β₀ + y) = P(β₀)` and `β₀ + y` is
  bad (`Fx.fxPlat` is the case `β₀` bad, `y < Ω₁`);
* `nnGood_HCl` (**a good name lies in the hull without countable collapses**): `η` good gives
  `η ∈ HCl(A_η, P(η))` (the window plateau with `y = 0`); so the level invariants `Nm.linv0_HCl`, `Nm.linvG_HCl`,
  `Nm.tinv_HCl` hold at `η` with `Z = P(η)`;
* `nnPrefix_good` (**the prefix of a good name is good**): `η₀ + t` good, `ω^u ∣ η₀`, `t < ω^u` give `η₀` good.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Nn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Br Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Fx

variable {S : InaccSeq.{0}}

/-! ## The prefix closure -/

theorem nn_opow_ne (u : Ordinal.{0}) : ω ^ u ≠ 0 := (opow_pos _ omega0_pos).ne'

/-- `(U·q + s) / U = q` for `s < U`. -/
theorem nn_div_eq {U q s : Ordinal.{0}} (hU : U ≠ 0) (hs : s < U) : (U * q + s) / U = q := by
  rw [mul_add_div _ hU, div_eq_zero_of_lt hs, add_zero]

/-- The `U`-prefix of an additive principal ordinal is `0` or itself. -/
theorem nn_quot_prin {U p : Ordinal.{0}} (hU : U ≠ 0) (hp : IsPrincipal (· + ·) p) :
    U * (p / U) = 0 ∨ U * (p / U) = p := by
  rcases lt_or_ge p U with h | h
  · left; rw [div_eq_zero_of_lt h, mul_zero]
  · right
    refine le_antisymm (mul_div_le p _) (not_lt.1 fun hlt => ?_)
    have hm : p % U < p := (mod_lt p hU).trans_le h
    have : U * (p / U) + p % U < p := hp hlt hm
    rw [div_add_mod] at this
    exact lt_irrefl _ this

/-- The `ω^u`-prefix of a sum. -/
theorem nn_quot_add (u x y : Ordinal.{0}) :
    (y < ω ^ u ∧ ω ^ u * ((x + y) / ω ^ u) = ω ^ u * (x / ω ^ u)) ∨
      (ω ^ u * ((x + y) / ω ^ u) = ω ^ u * (x / ω ^ u) + ω ^ u * (y / ω ^ u)) := by
  have hU := nn_opow_ne u
  rcases lt_or_ge y (ω ^ u) with hy | hy
  · left
    refine ⟨hy, ?_⟩
    have hs : x % ω ^ u + y < ω ^ u := isPrincipal_add_omega0_opow u (mod_lt x hU) hy
    have e : x + y = ω ^ u * (x / ω ^ u) + (x % ω ^ u + y) := by
      conv_lhs => rw [← div_add_mod x (ω ^ u)]
      rw [add_assoc]
    rw [e, nn_div_eq hU hs]
  · right
    have hq : 1 ≤ y / ω ^ u := Order.one_le_iff_pos.2 ((Ordinal.div_pos hU).2 hy)
    have hab : x % ω ^ u + ω ^ u * (y / ω ^ u) = ω ^ u * (y / ω ^ u) :=
      add_of_omega0_opow_le (mod_lt x hU) (le_mul_of_one_le_right' hq)
    have e : x + y = ω ^ u * (x / ω ^ u + y / ω ^ u) + y % ω ^ u := by
      conv_lhs => rw [← div_add_mod x (ω ^ u), ← div_add_mod y (ω ^ u)]
      rw [mul_add, add_assoc (ω ^ u * (x / ω ^ u)), ← add_assoc (x % ω ^ u), hab, ← add_assoc]
    rw [e, nn_div_eq hU (mod_lt y hU), mul_add]

variable {a Z : Ordinal.{0}}

/-- **The `ω^u`-prefix of a hull member is in the hull.** -/
theorem nnHCl_pre (u : Ordinal.{0}) {x : Ordinal.{0}} (h : HCl S a Z x) :
    HCl S a Z (ω ^ u * (x / ω ^ u)) := by
  have hU := nn_opow_ne u
  have prin : ∀ {p : Ordinal.{0}}, IsPrincipal (· + ·) p → HCl S a Z p →
      HCl S a Z (ω ^ u * (p / ω ^ u)) := fun hp hx => by
    rcases nn_quot_prin hU hp with e | e <;> rw [e]
    · exact HCl.zero
    · exact hx
  induction h with
  | @small x hx => exact HCl.small ((mul_div_le x _).trans_lt hx)
  | zero => rw [Ordinal.zero_div, mul_zero]; exact HCl.zero
  | inacc n => exact prin (SC_I n).isPrincipal (HCl.inacc n)
  | inaccW => exact prin SC_Iw.isPrincipal HCl.inaccW
  | @add x y hx hy ihx ihy =>
    rcases nn_quot_add u x y with ⟨-, e⟩ | e <;> rw [e]
    · exact ihx
    · exact HCl.add ihx ihy
  | @phi x y hx hy _ _ => exact prin (veblen_isPrincipal x y) (HCl.phi hx hy)
  | @om x hx _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero, Ordinal.zero_div, mul_zero]; exact HCl.zero
    · exact prin (Om_isPrincipal hx0) (HCl.om hx)
  | @coll π e hπ hπ1 hπC heC hea _ _ =>
    exact prin (SC_psi hπ e).isPrincipal (HCl.coll hπ hπ1 hπC heC hea)

/-- For `ω^u ∣ η₀` and `t < ω^u`: `η₀ + t` in the hull gives `η₀` in the hull. -/
theorem nnHCl_of_add {u η0 t : Ordinal.{0}} (hd : ω ^ u ∣ η0) (ht : t < ω ^ u) (h : HCl S a Z (η0 + t)) :
    HCl S a Z η0 := by
  have hpre := nnHCl_pre u h
  obtain ⟨q, rfl⟩ := hd
  rwa [nn_div_eq (nn_opow_ne u) ht] at hpre

/-! ## The window plateau -/

/-- **The hull does not grow across a window without hull members.** -/
theorem nnShrink {β0 y : Ordinal.{0}}
    (hwin : ∀ y'' ≤ y, ¬ HCl S (ConjT.Aη S β0) (Pv S β0) (β0 + y'')) {b : Ordinal.{0}}
    (hb : b ≤ ConjT.Aη S (β0 + y) + 1) {x : Ordinal.{0}} (h : HCl S b (Pv S β0) x) :
    HCl S (ConjT.Aη S β0) (Pv S β0) x := by
  have hZ1 := Pv_lt_Om1 S β0
  induction h with
  | small h => exact HCl.small h
  | zero => exact HCl.zero
  | inacc n => exact HCl.inacc n
  | inaccW => exact HCl.inaccW
  | add _ _ ihx ihy => exact HCl.add ihx ihy
  | phi _ _ ihx ihy => exact HCl.phi ihx ihy
  | om _ ih => exact HCl.om ih
  | @coll π e hπ hπ1 _ _ he ihπ ihe =>
    refine HCl.coll hπ hπ1 ihπ ihe ?_
    by_contra hge
    rw [not_lt] at hge
    obtain ⟨y'', hy'', hmem⟩ := fx_quot_window hZ1 ihe hge (he.trans_le hb)
    exact hwin y'' hy'' hmem

/-- The key condition across the window: every hull argument `e < b ≤ A_{β₀+y} + 1` has `ψ_{Ω₁}(e) < P(β₀)`. -/
theorem nn_key {β0 y : Ordinal.{0}}
    (hwin : ∀ y'' ≤ y, ¬ HCl S (ConjT.Aη S β0) (Pv S β0) (β0 + y'')) {b : Ordinal.{0}}
    (hb : b ≤ ConjT.Aη S (β0 + y) + 1) :
    ∀ e, HCl S b (Pv S β0) e → e < b → S.psi e (Om 1) < Pv S β0 := by
  intro e he heb
  have hZ1 := Pv_lt_Om1 S β0
  have he' : HCl S (ConjT.Aη S β0) (Pv S β0) e := nnShrink hwin hb he
  rcases lt_or_ge e (ConjT.Aη S β0) with hlt | hge
  · exact psi_lt_psi_of_mem Low.InR_Om_one hlt he'.mem_CSet
  · exfalso
    obtain ⟨y'', hy'', hmem⟩ := fx_quot_window hZ1 he' hge (heb.trans_le hb)
    exact hwin y'' hy'' hmem

/-- **THE WINDOW PLATEAU**: if no `β₀ + y''`, `y'' ≤ y`, lies in `HCl(A_{β₀}, P(β₀))`, then `P(β₀ + y) = P(β₀)`
and `β₀ + y` is bad. -/
theorem nnWPlat {β0 y : Ordinal.{0}}
    (hwin : ∀ y'' ≤ y, ¬ HCl S (ConjT.Aη S β0) (Pv S β0) (β0 + y'')) :
    Pv S (β0 + y) = Pv S β0 ∧ ¬ Bt.Good S (β0 + y) := by
  have hZ := Pv_SC S β0
  have hP : Pv S (β0 + y) = Pv S β0 :=
    le_antisymm (psi_le_of_key hZ (nn_key hwin le_self_add)) (Pv_mono le_self_add)
  refine ⟨hP, fun hg => ?_⟩
  have hg' : β0 + y ∈ S.CSet (ConjT.Aη S (β0 + y) + 1) (Pv S β0) := by
    have h2 : β0 + y ∈ S.CSet (ConjT.Aη S (β0 + y) + 1) (Pv S (β0 + y)) := hg
    rwa [hP] at h2
  have hH := CSet_sub_HCl (nn_key hwin le_rfl) _ hg'
  exact hwin y le_rfl (nnShrink hwin le_rfl hH)

/-- **A good name lies in the hull without countable collapses**: `η ∈ HCl(A_η, P(η))`. -/
theorem nnGood_HCl {η : Ordinal.{0}} (hg : Bt.Good S η) : HCl S (ConjT.Aη S η) (Pv S η) η := by
  by_contra h
  have hw : ∀ y'' ≤ (0 : Ordinal.{0}), ¬ HCl S (ConjT.Aη S η) (Pv S η) (η + y'') := by
    intro y'' hy''
    rw [nonpos_iff_eq_zero.1 hy'', add_zero]; exact h
  have := (nnWPlat hw).2
  rw [add_zero] at this
  exact this hg

/-- **The prefix of a good name is good**: `η₀ + t` good, `ω^u ∣ η₀`, `t < ω^u` give `η₀` good. -/
theorem nnPrefix_good {u η0 t : Ordinal.{0}} (hd : ω ^ u ∣ η0) (ht : t < ω ^ u) (hg : Bt.Good S (η0 + t)) :
    Bt.Good S η0 := by
  by_contra hbad
  have hw : ∀ y'' ≤ t, ¬ HCl S (ConjT.Aη S η0) (Pv S η0) (η0 + y'') := by
    intro y'' hy'' hmem
    exact hbad ((nnHCl_of_add hd (hy''.trans_lt ht) hmem).mono le_self_add).mem_CSet
  exact (nnWPlat hw).2 hg

end Googology.Trans.PoR.InaccPsi.R2.Nn
