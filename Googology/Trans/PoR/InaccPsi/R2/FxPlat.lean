import Googology.Trans.PoR.InaccPsi.R2.NmD

/-!
# The plateaus of `P`: a bad `η` stays bad for a countable distance

`θ = ψ_{Ω₂}(Ω_ω)`, `A_η = Ω_ω + θ·η`, `P(η) = ψ_{Ω₁}(A_η)` (`Nm.Pv`); `η` is good when
`η ∈ Cl(A_η + 1, P(η))` (`Bt.Good`); `HCl S a Z` is `Cl(a, Z)` without the countable collapses (`Bt.HCl`).

* `fxHCl_pre` (**the `Ω₁`-prefix of a hull member is in the hull**): `x ∈ HCl(a, Z)`, `Z < Ω₁` give
  `Ω₁·(x / Ω₁) ∈ HCl(a, Z)` (induction on the hull; sums split at `Ω₁`, the other constructors give
  additive principal values);
* `fxHCl_of_add`: for `y < Ω₁`, `η + y ∈ HCl(a, Z)` gives `η ∈ HCl(a, Z)` (with `Nm.linv0_HCl`: the countable
  remainder of a member is `< Z`);
* `fxShrink` (**the hull does not grow along a countable stretch after a bad `η`**): for `η ∉ HCl(A_η + 1, Z)`
  and `y < Ω₁`, `HCl(A_{η+y} + 1, Z) ⊆ HCl(A_η, Z)` (the `θ`-quotient `η'` of an argument `e ≥ A_η` of a
  collapse lies in `[η, η + y]`, so `η` would be in the hull);
* `fxPlat` (**the plateau**): for `η` bad and `y < Ω₁`: `P(η + y) = P(η)` and `η + y` is bad;
  `fxPlat_Om1`: `P(η + Ω₁) = P(η)` at a bad `η` (Lemma CONT).

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Fx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Br Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

theorem fx_Om1_ne : Om (1 : Ordinal.{0}) ≠ 0 := (zero_lt_one.trans one_lt_Om1).ne'

theorem fx_Om1_prin : IsPrincipal (· + ·) (Om (1 : Ordinal.{0})) := Om_isPrincipal one_ne_zero

/-- `(Ω₁·q + s) / Ω₁ = q` for `s < Ω₁`. -/
theorem fx_div_eq {q s : Ordinal.{0}} (hs : s < Om 1) : (Om 1 * q + s) / Om 1 = q := by
  rw [mul_add_div _ fx_Om1_ne, div_eq_zero_of_lt hs, add_zero]

/-- The `Ω₁`-prefix of an additive principal ordinal is `0` or itself. -/
theorem fx_quot_prin {p : Ordinal.{0}} (hp : IsPrincipal (· + ·) p) :
    Om 1 * (p / Om 1) = 0 ∨ Om 1 * (p / Om 1) = p := by
  rcases lt_or_ge p (Om (1 : Ordinal.{0})) with h | h
  · left; rw [div_eq_zero_of_lt h, mul_zero]
  · right
    refine le_antisymm (mul_div_le p _) (not_lt.1 fun hlt => ?_)
    have hm : p % Om 1 < p := (mod_lt p fx_Om1_ne).trans_le h
    have : Om 1 * (p / Om 1) + p % Om 1 < p := hp hlt hm
    rw [div_add_mod] at this
    exact lt_irrefl _ this

/-- The `Ω₁`-prefix of a sum. -/
theorem fx_quot_add (x y : Ordinal.{0}) :
    (y < Om 1 ∧ Om 1 * ((x + y) / Om 1) = Om 1 * (x / Om 1)) ∨
      (Om 1 * ((x + y) / Om 1) = Om 1 * (x / Om 1) + Om 1 * (y / Om 1)) := by
  rcases lt_or_ge y (Om (1 : Ordinal.{0})) with hy | hy
  · left
    refine ⟨hy, ?_⟩
    have hs : x % Om 1 + y < Om 1 := fx_Om1_prin (mod_lt x fx_Om1_ne) hy
    have e : x + y = Om 1 * (x / Om 1) + (x % Om 1 + y) := by
      conv_lhs => rw [← div_add_mod x (Om 1)]
      rw [add_assoc]
    rw [e, fx_div_eq hs]
  · right
    have hq : 1 ≤ y / Om 1 := Order.one_le_iff_pos.2 ((Ordinal.div_pos fx_Om1_ne).2 hy)
    have hab : x % Om 1 + Om 1 * (y / Om 1) = Om 1 * (y / Om 1) := by
      refine add_of_omega0_opow_le (b := Om 1) ?_ ?_
      · rw [Om1_opow]; exact mod_lt x fx_Om1_ne
      · rw [Om1_opow]; exact le_mul_of_one_le_right' hq
    have e : x + y = Om 1 * (x / Om 1 + y / Om 1) + y % Om 1 := by
      conv_lhs => rw [← div_add_mod x (Om 1), ← div_add_mod y (Om 1)]
      rw [mul_add, add_assoc (Om 1 * (x / Om 1)), ← add_assoc (x % Om 1), hab, ← add_assoc]
    rw [e, fx_div_eq (mod_lt y fx_Om1_ne), mul_add]

variable {a Z : Ordinal.{0}}

/-- **The `Ω₁`-prefix of a hull member is in the hull.** -/
theorem fxHCl_pre (hZ1 : Z < Om 1) {x : Ordinal.{0}} (h : HCl S a Z x) :
    HCl S a Z (Om 1 * (x / Om 1)) := by
  have prin : ∀ {p : Ordinal.{0}}, IsPrincipal (· + ·) p → HCl S a Z p →
      HCl S a Z (Om 1 * (p / Om 1)) := fun hp hx => by
    rcases fx_quot_prin hp with e | e <;> rw [e]
    · exact HCl.zero
    · exact hx
  induction h with
  | @small x hx =>
    rw [div_eq_zero_of_lt (hx.trans hZ1), mul_zero]; exact HCl.zero
  | zero => rw [Ordinal.zero_div, mul_zero]; exact HCl.zero
  | inacc n => exact prin (SC_I n).isPrincipal (HCl.inacc n)
  | inaccW => exact prin SC_Iw.isPrincipal HCl.inaccW
  | @add x y hx hy ihx ihy =>
    rcases fx_quot_add x y with ⟨-, e⟩ | e <;> rw [e]
    · exact ihx
    · exact HCl.add ihx ihy
  | @phi x y hx hy _ _ => exact prin (veblen_isPrincipal x y) (HCl.phi hx hy)
  | @om x hx _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero, Ordinal.zero_div, mul_zero]; exact HCl.zero
    · exact prin (Om_isPrincipal hx0) (HCl.om hx)
  | @coll π e hπ hπ1 hπC heC hea _ _ =>
    exact prin (SC_psi hπ e).isPrincipal (HCl.coll hπ hπ1 hπC heC hea)

/-- For `y < Ω₁`: `η + y` in the hull gives `η` in the hull. -/
theorem fxHCl_of_add (hZ : SC Z) (hZ1 : Z < Om 1) {η y : Ordinal.{0}} (hy : y < Om 1)
    (h : HCl S a Z (η + y)) : HCl S a Z η := by
  have hd : η % Om 1 + y < Om 1 := fx_Om1_prin (mod_lt η fx_Om1_ne) hy
  have e : η + y = Om 1 * (η / Om 1) + (η % Om 1 + y) := by
    conv_lhs => rw [← div_add_mod η (Om 1)]
    rw [add_assoc]
  have hpre := fxHCl_pre hZ1 h
  rw [e, fx_div_eq hd] at hpre
  obtain ⟨q, z, hz, hq⟩ := linv0_HCl hZ hZ1 h
  rw [e] at hq
  have hzΩ : z < Om 1 := hz.trans hZ1
  obtain ⟨-, hzz⟩ := div_unique fx_Om1_ne hd hzΩ hq
  have hdZ : η % Om 1 < Z := lt_of_le_of_lt le_self_add (hzz ▸ hz)
  have := HCl.add hpre (HCl.small (S := S) (a := a) hdZ)
  rwa [div_add_mod] at this

/-- The `θ`-quotient of a hull member `e` with `A_η ≤ e ≤ A_{η+y}` is `η + y''` with `y'' ≤ y`. -/
theorem fx_quot_window (hZ1 : Z < Om 1) {η y e : Ordinal.{0}} (he : HCl S a Z e)
    (h1 : ConjT.Aη S η ≤ e) (h2 : e < ConjT.Aη S (η + y) + 1) :
    ∃ y'', y'' ≤ y ∧ HCl S a Z (η + y'') := by
  obtain ⟨η', hη', k1, k2⟩ := quotA hZ1 he ((ConjT.OmW_le_A S η).trans h1)
  rw [ConjT.A_succ] at k2
  have hle1 : η ≤ η' := Order.lt_add_one_iff.1 (A_lt_A_iff.1 (lt_of_le_of_lt h1 k2))
  have hle2 : η' ≤ η + y := by
    by_contra hlt
    rw [not_le] at hlt
    have := A_lt_A_iff (S := S) |>.2 hlt
    have h3 : ConjT.Aη S (η + y) + 1 ≤ ConjT.Aη S η' := Order.add_one_le_of_lt this
    exact absurd (h2.trans_le (h3.trans k1)) (lt_irrefl _)
  obtain ⟨y'', rfl⟩ := exists_add_of_le hle1
  exact ⟨y'', (add_le_add_iff_left η).1 hle2, hη'⟩

/-- **The hull does not grow along a countable stretch after a bad `η`.** -/
theorem fxShrink (hZ : SC Z) (hZ1 : Z < Om 1) {η y : Ordinal.{0}} (hy : y < Om 1)
    (hbad : ¬ HCl S (ConjT.Aη S η + 1) Z η) {x : Ordinal.{0}}
    (h : HCl S (ConjT.Aη S (η + y) + 1) Z x) : HCl S (ConjT.Aη S η) Z x := by
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
    obtain ⟨y'', hy'', hmem⟩ := fx_quot_window hZ1 ihe hge he
    exact hbad ((fxHCl_of_add hZ hZ1 (hy''.trans_lt hy) hmem).mono le_self_add)

/-- The key condition along the stretch: every hull argument `e < A_{η+y} + 1` has `ψ_{Ω₁}(e) < P(η)`. -/
theorem fx_key {η y : Ordinal.{0}} (hy : y < Om 1)
    (hbad : ¬ HCl S (ConjT.Aη S η + 1) (Pv S η) η) {b : Ordinal.{0}}
    (hb : b ≤ ConjT.Aη S (η + y) + 1) :
    ∀ e, HCl S b (Pv S η) e → e < b → S.psi e (Om 1) < Pv S η := by
  intro e he heb
  have hZ := Pv_SC S η
  have hZ1 := Pv_lt_Om1 S η
  have he' : HCl S (ConjT.Aη S η) (Pv S η) e := fxShrink hZ hZ1 hy hbad (he.mono hb)
  rcases lt_or_ge e (ConjT.Aη S η) with hlt | hge
  · exact psi_lt_psi_of_mem Low.InR_Om_one hlt he'.mem_CSet
  · exfalso
    obtain ⟨y'', hy'', hmem⟩ := fx_quot_window hZ1 he' hge (heb.trans_le hb)
    exact hbad ((fxHCl_of_add hZ hZ1 (hy''.trans_lt hy) hmem).mono le_self_add)

/-- **The plateau**: a bad `η` gives `P(η + y) = P(η)` and `η + y` bad for every `y < Ω₁`. -/
theorem fxPlat {η y : Ordinal.{0}} (hbad : ¬ Bt.Good S η) (hy : y < Om 1) :
    Pv S (η + y) = Pv S η ∧ ¬ Bt.Good S (η + y) := by
  have hZ := Pv_SC S η
  have hZ1 := Pv_lt_Om1 S η
  have hbadH : ¬ HCl S (ConjT.Aη S η + 1) (Pv S η) η := fun h => hbad h.mem_CSet
  have hP : Pv S (η + y) = Pv S η :=
    le_antisymm (psi_le_of_key hZ (fx_key hy hbadH le_self_add)) (Pv_mono le_self_add)
  refine ⟨hP, fun hg => ?_⟩
  have hg' : η + y ∈ S.CSet (ConjT.Aη S (η + y) + 1) (Pv S η) := by
    have h2 : η + y ∈ S.CSet (ConjT.Aη S (η + y) + 1) (Pv S (η + y)) := hg
    rwa [hP] at h2
  have hH := CSet_sub_HCl (fx_key hy hbadH le_rfl) _ hg'
  exact hbadH ((fxHCl_of_add hZ hZ1 hy (fxShrink hZ hZ1 hy hbadH hH)).mono le_self_add)

theorem fx_Om1_lim : IsSuccLimit (Om (1 : Ordinal.{0})) := eps_isSuccLimit Om1_opow one_lt_Om1

/-- **`P(η + Ω₁) = P(η)`** at a bad `η`. -/
theorem fxPlat_Om1 {η : Ordinal.{0}} (hbad : ¬ Bt.Good S η) :
    Pv S (η + Om 1) = Pv S η :=
  le_antisymm (cont_le fx_Om1_lim fun _ hc => (fxPlat hbad hc).1.le) (Pv_mono le_self_add)

end Googology.Trans.PoR.InaccPsi.R2.Fx
