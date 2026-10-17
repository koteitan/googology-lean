import Googology.Trans.PoR.InaccPsi.R2.BtX

/-!
# The hull without countable collapses, and the step at a bad argument

`θ = ψ_{Ω₂}(Ω_ω)`, `A_η = Ω_ω + θ·η`.  `HCl S a Z` is `Cl(a, Z)` without the collapses `ψ_{Ω₁}(e)`
(`HCl.mem_CSet`: it is a part of `Cl(a, Z)`).

* `HCl_lt`: a countable member of `HCl S a Z` is below `Z` (`Z` strongly critical);
* `CSet_sub_HCl`, `psi_le_of_key`: if `ψ_{Ω₁}(e) < Z` for every `e < a` in the hull, then `Cl(a, Z)` is the
  hull and `ψ_{Ω₁}(a) ≤ Z`;
* `QInv`, `QInv_HCl`, `quotA` (**the `θ`-quotient**): a member `x ≥ θ` of the hull lies in `[θ·η, θ·η + θ)`,
  a member `x ≥ Ω_ω` in `[A_η, A_η + θ)`, for some `η` of the hull; `x - θ` and `x - Ω_ω` are in the hull;
* `C_mul_th`: `Cl(a, b)` is closed under `x ↦ θ·x` (when `θ ∈ Cl(a, b)`); `HA_of_good`: (HA) at `A_η` when
  `η ∈ Cl(A_η + 1, ψ_{Ω₁}(A_η))` (`η` **good**);
* `psi_succ_of_bad` (**the step at a bad argument**): for `η > 0` with
  `η ∉ Cl(A_η + 1, ψ_{Ω₁}(A_η))`: `ψ_{Ω₁}(A_{η+1}) = ψ_{Ω₁}(A_η)`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Bt

open Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq

/-- `Cl(a, Z)` without the countable collapses `ψ_{Ω₁}(e)`. -/
inductive HCl (S : InaccSeq.{0}) (a Z : Ordinal.{0}) : Ordinal.{0} → Prop
  | small {x : Ordinal.{0}} : x < Z → HCl S a Z x
  | zero : HCl S a Z 0
  | inacc (n : ℕ) : HCl S a Z (S.I n)
  | inaccW : HCl S a Z S.Iw
  | add {x y : Ordinal.{0}} : HCl S a Z x → HCl S a Z y → HCl S a Z (x + y)
  | phi {x y : Ordinal.{0}} : HCl S a Z x → HCl S a Z y → HCl S a Z (veblen x y)
  | om {x : Ordinal.{0}} : HCl S a Z x → HCl S a Z (Om x)
  | coll {π e : Ordinal.{0}} : S.InR π → π ≠ Om 1 → HCl S a Z π → HCl S a Z e → e < a →
      HCl S a Z (S.psi e π)

variable {S : InaccSeq.{0}} {a Z : Ordinal.{0}}

theorem HCl.opow {c : Ordinal.{0}} (h : HCl S a Z c) : HCl S a Z (ω ^ c) := by
  have := HCl.phi HCl.zero h; rwa [veblen_zero_apply] at this

theorem HCl.one : HCl S a Z 1 := by
  have := (HCl.zero (S := S) (a := a) (Z := Z)).opow; rwa [opow_zero] at this

theorem HCl.succ {x : Ordinal.{0}} (h : HCl S a Z x) : HCl S a Z (x + 1) := HCl.add h HCl.one

theorem HCl.mem_CSet {x : Ordinal.{0}} (h : HCl S a Z x) : x ∈ S.CSet a Z := by
  induction h with
  | small h => exact CSet.of_lt h
  | zero => exact CSet.zero_mem _ _
  | inacc n => exact CSet.I_mem _ _ n
  | inaccW => exact CSet.Iw_mem _ _
  | add _ _ ihx ihy => exact CSet.add_mem ihx ihy
  | phi _ _ ihx ihy => exact CSet.phi_mem ihx ihy
  | om _ ih => exact CSet.Om_mem ih
  | coll hπ _ _ _ he ihπ ihe => exact CSet.psi_mem he hπ ihπ ihe

theorem HCl.mono {a' : Ordinal.{0}} (haa : a ≤ a') {x : Ordinal.{0}} (h : HCl S a Z x) :
    HCl S a' Z x := by
  induction h with
  | small h => exact HCl.small h
  | zero => exact HCl.zero
  | inacc n => exact HCl.inacc n
  | inaccW => exact HCl.inaccW
  | add _ _ ihx ihy => exact HCl.add ihx ihy
  | phi _ _ ihx ihy => exact HCl.phi ihx ihy
  | om _ ih => exact HCl.om ih
  | coll hπ hπ1 _ _ he ihπ ihe => exact HCl.coll hπ hπ1 ihπ ihe (lt_of_lt_of_le he haa)

/-- A countable member of the hull is below `Z`. -/
theorem HCl_lt (hZ : SC Z) {x : Ordinal.{0}} (h : HCl S a Z x) : x < Om 1 → x < Z := by
  induction h with
  | small h => exact fun _ => h
  | zero => exact fun _ => hZ.1
  | inacc n => exact fun h1 => absurd h1 (not_lt.2 (Low.Om_one_le_I n))
  | inaccW => exact fun h1 => absurd h1 (not_lt.2 ((Low.Om_one_le_I 0).trans (S.I_le_Iw 0)))
  | add _ _ ihx ihy =>
    exact fun h1 => hZ.isPrincipal (ihx (lt_of_le_of_lt le_self_add h1))
      (ihy (lt_of_le_of_lt le_add_self h1))
  | @phi x y _ _ ihx ihy =>
    exact fun h1 => hZ.2 _ (ihx (lt_of_le_of_lt (left_le_veblen x y) h1)) _
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h1))
  | @om x _ _ =>
    intro h1
    rw [Low.eq_zero_of_Om_lt_Om_one h1, Om_zero]; exact hZ.1
  | coll hπ hπ1 _ _ _ _ _ => exact fun h1 => absurd (Low.eq_Om_one_of_psi_lt hπ h1) hπ1

/-- If every countable collapse of the hull below `a` is below `Z`, `Cl(a, Z)` is the hull. -/
theorem CSet_sub_HCl (hKey : ∀ e, HCl S a Z e → e < a → S.psi e (Om 1) < Z) :
    ∀ x ∈ S.CSet a Z, HCl S a Z x := by
  intro x hx
  induction hx with
  | small h => exact HCl.small h
  | zero => exact HCl.zero
  | inacc n => exact HCl.inacc n
  | inaccW => exact HCl.inaccW
  | add _ _ ihx ihy => exact HCl.add ihx ihy
  | phi _ _ ihx ihy => exact HCl.phi ihx ihy
  | om _ ih => exact HCl.om ih
  | @coll π e hπ _ _ ihπ ihe =>
    by_cases h1 : π = Om 1
    · subst h1; exact HCl.small (hKey e.1 ihe e.2)
    · exact HCl.coll hπ h1 ihπ ihe e.2

/-- `ψ_{Ω₁}(a) ≤ Z` from the key condition. -/
theorem psi_le_of_key (hZ : SC Z) (hKey : ∀ e, HCl S a Z e → e < a → S.psi e (Om 1) < Z) :
    S.psi a (Om 1) ≤ Z :=
  psi_le_of_good (CSet.Om_mem (CSet.one_mem _ _)) fun x hx hx1 =>
    HCl_lt hZ (CSet_sub_HCl hKey x hx) hx1

/-! ## Ordinal arithmetic -/

/-- A principal `x < P + Q` with `Q ≤ P` is `≤ P`. -/
theorem prin_le_of_lt_add {x P Q : Ordinal.{0}} (hp : IsPrincipal (· + ·) x) (hx : x < P + Q)
    (hQ : Q ≤ P) : x ≤ P := by
  by_contra hgt
  rw [not_le] at hgt
  have e1 : P + x = x := hp.add_eq_right hgt
  obtain ⟨c, rfl⟩ := exists_add_of_le hgt.le
  have hc : c < Q := (add_lt_add_iff_left _).1 hx
  have e2 : P + c = c := add_left_cancel_iff.1 e1
  have h3 := add_eq_right_iff_mul_omega0_le.1 e2
  have hP : P ≤ c := (le_mul_left _ omega0_pos).trans h3
  exact absurd ((hP.trans_lt hc).trans_le hQ) (lt_irrefl _)

theorem absorb_th {r η : Ordinal.{0}} (hr : r < ConjT.th S) (hη : η ≠ 0) :
    r + ConjT.th S * η = ConjT.th S * η := by
  obtain ⟨η', rfl⟩ : ∃ η', η = 1 + η' :=
    ⟨η - 1, (Ordinal.add_sub_cancel_of_le (Order.one_le_iff_ne_zero.2 hη)).symm⟩
  rw [mul_add, mul_one, ← add_assoc, (ConjT.SC_th S).isPrincipal.add_eq_right hr]

theorem A_lt_A_iff {η η' : Ordinal.{0}} : ConjT.Aη S η < ConjT.Aη S η' ↔ η < η' := by
  unfold ConjT.Aη
  rw [add_lt_add_iff_left, mul_lt_mul_iff_right₀ th_pos]

/-! ## The `θ`-quotient -/

/-- The invariant of the `θ`-quotient: above `θ` the member lies in `[θ·η, θ·η + θ)` for an `η` of the hull,
and `x - θ`, `x - Ω_ω` are in the hull. -/
def QInv (S : InaccSeq.{0}) (a Z x : Ordinal.{0}) : Prop :=
  (ConjT.th S ≤ x → ∃ η, HCl S a Z η ∧ ConjT.th S * η ≤ x ∧ x < ConjT.th S * η + ConjT.th S) ∧
  (ConjT.th S ≤ x → HCl S a Z (x - ConjT.th S)) ∧
  (Om ω ≤ x → HCl S a Z (x - Om ω))

/-- `x - P` for a principal member `x ≥ P`. -/
theorem HCl_sub_prin {x P : Ordinal.{0}} (hp : IsPrincipal (· + ·) x) (hx : HCl S a Z x) (hP : P ≤ x) :
    HCl S a Z (x - P) := by
  rcases eq_or_lt_of_le hP with e | hlt
  · rw [← e, Ordinal.sub_self]; exact HCl.zero
  · rw [Ordinal.sub_eq_of_add_eq (hp.add_eq_right hlt)]; exact hx

/-- `QInv` for an `ε`-number of the hull. -/
theorem QInv_eps {x : Ordinal.{0}} (he : ω ^ x = x) (hx : HCl S a Z x) : QInv S a Z x := by
  have hp : IsPrincipal (· + ·) x := by rw [← he]; exact isPrincipal_add_omega0_opow _
  refine ⟨fun h1 => ?_, HCl_sub_prin hp hx, HCl_sub_prin hp hx⟩
  rcases eq_or_lt_of_le h1 with e | hlt
  · refine ⟨1, HCl.one, by rw [mul_one, e], ?_⟩
    rw [mul_one, ← e]; exact lt_add_of_pos_right _ th_pos
  · have e2 : ConjT.th S * x = x := by
      conv_lhs => rw [← he]
      rw [th_mul_opow, hp.add_eq_right hlt, he]
    refine ⟨x, hx, e2.le, ?_⟩
    rw [e2]; exact lt_add_of_pos_right _ th_pos

/-- `QInv` for `ω^c`. -/
theorem QInv_opow {c : Ordinal.{0}} (hc : HCl S a Z c) (hq : QInv S a Z c) :
    QInv S a Z (ω ^ c) := by
  have hp : IsPrincipal (· + ·) (ω ^ c) := isPrincipal_add_omega0_opow _
  refine ⟨fun h1 => ?_, HCl_sub_prin hp hc.opow, HCl_sub_prin hp hc.opow⟩
  have hθc : ConjT.th S ≤ c := by
    rw [← Low.opow_eq_self_of_SC (ConjT.SC_th S)] at h1
    exact (opow_le_opow_iff_right one_lt_omega0).1 h1
  have hsub := hq.2.1 hθc
  have e : ConjT.th S * ω ^ (c - ConjT.th S) = ω ^ c := by
    rw [th_mul_opow, Ordinal.add_sub_cancel_of_le hθc]
  refine ⟨ω ^ (c - ConjT.th S), hsub.opow, e.le, ?_⟩
  rw [e]; exact lt_add_of_pos_right _ th_pos

/-- `(y + z) - P` for a principal `P`. -/
theorem HCl_sub_add {P y z : Ordinal.{0}} (hP : IsPrincipal (· + ·) P)
    (hz : HCl S a Z z) (qy : P ≤ y → HCl S a Z (y - P)) (qz : P ≤ z → HCl S a Z (z - P))
    (h1 : P ≤ y + z) : HCl S a Z (y + z - P) := by
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [add_zero] at h1 ⊢; exact qy h1
  rcases lt_or_ge y P with hyP | hyP
  · rcases lt_or_ge z P with hzP | hzP
    · exact absurd (hP hyP hzP) (not_lt.2 h1)
    · obtain ⟨z', rfl⟩ := exists_add_of_le hzP
      have e : y + (P + z') = P + z' := by rw [← add_assoc, hP.add_eq_right hyP]
      rw [e]; exact qz hzP
  · have e : y + z - P = (y - P) + z := by
      refine Ordinal.sub_eq_of_add_eq ?_
      rw [← add_assoc, Ordinal.add_sub_cancel_of_le hyP]
    rw [e]; exact HCl.add (qy hyP) hz

/-- `QInv` for a sum. -/
theorem QInv_add {y z : Ordinal.{0}} (hy : HCl S a Z y) (hz : HCl S a Z z) (qy : QInv S a Z y)
    (qz : QInv S a Z z) : QInv S a Z (y + z) := by
  have hθ := (ConjT.SC_th S).isPrincipal
  refine ⟨fun h1 => ?_, HCl_sub_add hθ hz qy.2.1 qz.2.1, HCl_sub_add Om_omega_principal hz qy.2.2
    qz.2.2⟩
  rcases lt_or_ge z (ConjT.th S) with hzθ | hzθ
  · rcases lt_or_ge y (ConjT.th S) with hyθ | hyθ
    · exact absurd (hθ hyθ hzθ) (not_lt.2 h1)
    · obtain ⟨η, hη, k1, k2⟩ := qy.1 hyθ
      obtain ⟨r, rfl⟩ := exists_add_of_le k1
      have hr : r < ConjT.th S := (add_lt_add_iff_left _).1 k2
      refine ⟨η, hη, le_self_add.trans le_self_add, ?_⟩
      rw [add_assoc]; exact (add_lt_add_iff_left _).2 (hθ hr hzθ)
  · obtain ⟨ηz, hηz, k1, k2⟩ := qz.1 hzθ
    obtain ⟨rz, hrz⟩ := exists_add_of_le k1
    have hrz' : rz < ConjT.th S := by rw [hrz] at k2; exact (add_lt_add_iff_left _).1 k2
    have hηz0 : ηz ≠ 0 := by
      rintro rfl; rw [mul_zero, zero_add] at k2; exact absurd k2 (not_lt.2 hzθ)
    rcases lt_or_ge y (ConjT.th S) with hyθ | hyθ
    · have e : y + z = z := by rw [hrz, ← add_assoc, absorb_th hyθ hηz0]
      rw [e]; exact ⟨ηz, hηz, k1, k2⟩
    · obtain ⟨ηy, hηy, l1, l2⟩ := qy.1 hyθ
      obtain ⟨ry, rfl⟩ := exists_add_of_le l1
      have hry : ry < ConjT.th S := (add_lt_add_iff_left _).1 l2
      have e : ConjT.th S * ηy + ry + z = ConjT.th S * (ηy + ηz) + rz := by
        rw [hrz, add_assoc, ← add_assoc ry, absorb_th hry hηz0, ← add_assoc, ← mul_add]
      rw [e]
      exact ⟨ηy + ηz, HCl.add hηy hηz, le_self_add, (add_lt_add_iff_left _).2 hrz'⟩

theorem QInv_small {x : Ordinal.{0}} (hxθ : x < ConjT.th S) : QInv S a Z x :=
  ⟨fun h1 => absurd h1 (not_le.2 hxθ), fun h1 => absurd h1 (not_le.2 hxθ),
    fun h1 => absurd h1 (not_le.2 (hxθ.trans (th_lt_Om_omega S)))⟩

/-- **The `θ`-quotient**: every member of the hull has `QInv` (for `Z < Ω₁`). -/
theorem QInv_HCl (hZ1 : Z < Om 1) {x : Ordinal.{0}} (h : HCl S a Z x) : QInv S a Z x := by
  induction h with
  | @small x hx => exact QInv_small ((hx.trans hZ1).trans Om1_lt_th)
  | zero => exact QInv_small th_pos
  | inacc n => exact QInv_eps (Low.opow_eq_self_of_SC (SC_I n)) (HCl.inacc n)
  | inaccW => exact QInv_eps (Low.opow_eq_self_of_SC SC_Iw) HCl.inaccW
  | add hy hz qy qz => exact QInv_add hy hz qy qz
  | @phi x y hx hy _ qy =>
    rcases eq_or_ne x 0 with rfl | hx0
    · have := QInv_opow hy qy; rwa [← veblen_zero_apply] at this
    · have he : ω ^ veblen x y = veblen x y := by
        rw [← veblen_zero_apply]; exact veblen_veblen_of_lt (pos_iff_ne_zero.2 hx0) y
      exact QInv_eps he (HCl.phi hx hy)
  | @om x hx _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero]; exact QInv_small th_pos
    · exact QInv_eps (Low.opow_eq_self_of_SC (SC_Om hx0)) (HCl.om hx)
  | coll hπ hπ1 hπ' he' he _ _ =>
    exact QInv_eps (Low.opow_eq_self_of_SC (SC_psi hπ _)) (HCl.coll hπ hπ1 hπ' he' he)

theorem th_mul_Om_omega (S : InaccSeq.{0}) : ConjT.th S * Om ω = Om ω := by
  have hSCw : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero
  have e := Low.opow_eq_self_of_SC hSCw
  conv_lhs => rw [← e]
  rw [th_mul_opow, hSCw.isPrincipal.add_eq_right (th_lt_Om_omega S), e]

theorem th_mul_lt_Om_omega {x : Ordinal.{0}} (hx : x < Om ω) : ConjT.th S * x < Om ω := by
  have hSCw : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero
  calc ConjT.th S * x ≤ ConjT.th S * ω ^ x := by
        gcongr; exact Ordinal.right_le_opow x one_lt_omega0
    _ = ω ^ (ConjT.th S + x) := th_mul_opow S x
    _ < Om ω := by
        have := hSCw.2 0 hSCw.1 _ (hSCw.isPrincipal (th_lt_Om_omega S) hx)
        rwa [veblen_zero_apply] at this

/-- **The quotient above `Ω_ω`**: a member `x ≥ Ω_ω` of the hull lies in `[A_η, A_η + θ)` for an `η` of
the hull. -/
theorem quotA (hZ1 : Z < Om 1) {x : Ordinal.{0}} (h : HCl S a Z x) (hx : Om ω ≤ x) :
    ∃ η, HCl S a Z η ∧ ConjT.Aη S η ≤ x ∧ x < ConjT.Aη S η + ConjT.th S := by
  obtain ⟨η, hη, k1, k2⟩ := (QInv_HCl hZ1 h).1 ((th_lt_Om_omega S).le.trans hx)
  have hηω : Om ω ≤ η := by
    by_contra hlt
    rw [not_le] at hlt
    have : ConjT.th S * η + ConjT.th S < Om ω := by
      rw [← mul_add_one]; exact th_mul_lt_Om_omega ((SC_Om omega0_ne_zero).add_one_lt hlt)
    exact absurd (k2.trans this) (not_lt.2 hx)
  have e : ConjT.Aη S (η - Om ω) = ConjT.th S * η := by
    unfold ConjT.Aη
    nth_rewrite 1 [← th_mul_Om_omega S]
    rw [← mul_add, Ordinal.add_sub_cancel_of_le hηω]
  refine ⟨η - Om ω, (QInv_HCl hZ1 hη).2.2 hηω, by rw [e]; exact k1, by rw [e]; exact k2⟩

/-! ## `θ·x` and (HA) -/

theorem th_mul_eps_mem {a b x : Ordinal.{0}} (hθ : ConjT.th S ∈ S.CSet a b) (hx : x ∈ S.CSet a b)
    (he : ω ^ x = x) : ConjT.th S * x ∈ S.CSet a b := by
  rw [← he, th_mul_opow, ← veblen_zero_apply]
  exact CSet.phi_mem (CSet.zero_mem _ _) (CSet.add_mem hθ hx)

theorem th_mul_opow_mem {a b c : Ordinal.{0}} (hθ : ConjT.th S ∈ S.CSet a b) (hc : c ∈ S.CSet a b) :
    ConjT.th S * ω ^ c ∈ S.CSet a b := by
  rw [th_mul_opow, ← veblen_zero_apply]
  exact CSet.phi_mem (CSet.zero_mem _ _) (CSet.add_mem hθ hc)

/-- `Cl(a, b)` is closed under `x ↦ θ·x` when `θ ∈ Cl(a, b)`. -/
theorem C_mul_th {a b : Ordinal.{0}} (hθ : ConjT.th S ∈ S.CSet a b) :
    ∀ x ∈ S.CSet a b, ConjT.th S * x ∈ S.CSet a b := by
  intro x hx
  induction hx with
  | @small x h =>
    obtain ⟨L, hL1, -, hL3⟩ := exists_prin_list x
    rw [← hL3, ← foldr_map_mul]
    refine foldr_mem _ fun l hl => ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hl
    obtain ⟨hp, h0, hle⟩ := hL1 y hy
    obtain ⟨c, rfl⟩ := prin_eq_opow hp h0
    exact th_mul_opow_mem hθ (CSet.of_lt
      (lt_of_le_of_lt ((Ordinal.right_le_opow c one_lt_omega0).trans hle) h))
  | zero => rw [mul_zero]; exact CSet.zero_mem _ _
  | inacc n => exact th_mul_eps_mem hθ (CSet.I_mem _ _ n) (Low.opow_eq_self_of_SC (SC_I n))
  | inaccW => exact th_mul_eps_mem hθ (CSet.Iw_mem _ _) (Low.opow_eq_self_of_SC SC_Iw)
  | add _ _ ihx ihy => rw [mul_add]; exact CSet.add_mem ihx ihy
  | @phi x y hx hy _ _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [veblen_zero_apply]; exact th_mul_opow_mem hθ hy
    · refine th_mul_eps_mem hθ (CSet.phi_mem hx hy) ?_
      rw [← veblen_zero_apply]; exact veblen_veblen_of_lt (pos_iff_ne_zero.2 hx0) y
  | @om x hx _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero, mul_zero]; exact CSet.zero_mem _ _
    · exact th_mul_eps_mem hθ (CSet.Om_mem hx) (Low.opow_eq_self_of_SC (SC_Om hx0))
  | @coll π e hπ hπC heC _ _ =>
    exact th_mul_eps_mem hθ (CSet.psi_mem e.2 hπ hπC heC) (Low.opow_eq_self_of_SC (SC_psi hπ _))

/-- **(HA) at a good argument**: `η ∈ Cl(A_η + 1, ψ_{Ω₁}(A_η))` gives (HA) at `A_η`. -/
theorem HA_of_good (S : InaccSeq.{0}) {η : Ordinal.{0}}
    (h : η ∈ S.CSet (ConjT.Aη S η + 1) (S.psi (ConjT.Aη S η) (Om 1))) :
    ConjT.HA S (ConjT.Aη S η) := by
  have hlt : Om (ω : Ordinal.{0}) < ConjT.Aη S η + 1 :=
    lt_of_le_of_lt (ConjT.OmW_le_A S η) (lt_add_one _)
  exact CSet.add_mem (ConjT.OmW_mem S _ _) (C_mul_th (ConjT.th_mem S hlt) η h)

/-! ## The step at a bad argument -/

/-- The `θ`-quotient is unique. -/
theorem quot_unique {η η' e : Ordinal.{0}} (h1 : ConjT.Aη S η ≤ e) (h2 : e < ConjT.Aη S η + ConjT.th S)
    (h1' : ConjT.Aη S η' ≤ e) (h2' : e < ConjT.Aη S η' + ConjT.th S) : η = η' := by
  rw [ConjT.A_succ] at h2 h2'
  have a1 : η < η' + 1 := A_lt_A_iff.1 (lt_of_le_of_lt h1 h2')
  have a2 : η' < η + 1 := A_lt_A_iff.1 (lt_of_le_of_lt h1' h2)
  exact le_antisymm (Order.lt_add_one_iff.1 a1) (Order.lt_add_one_iff.1 a2)

/-- At a bad argument the hull of `A_η + θ` is the hull of `A_η`. -/
theorem HCl_shrink {η Z : Ordinal.{0}} (hZ1 : Z < Om 1)
    (hbad : ¬ HCl S (ConjT.Aη S η + 1) Z η) {x : Ordinal.{0}}
    (h : HCl S (ConjT.Aη S η + ConjT.th S) Z x) : HCl S (ConjT.Aη S η) Z x := by
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
    have h1 : Om (ω : Ordinal.{0}) ≤ e := (ConjT.OmW_le_A S η).trans hge
    obtain ⟨η', hη', k1, k2⟩ := quotA hZ1 ihe h1
    have := quot_unique hge he k1 k2
    subst this
    exact hbad (hη'.mono (le_self_add))

/-- **The step at a bad argument**: for `η > 0` with `η ∉ Cl(A_η + 1, ψ_{Ω₁}(A_η))`:
`ψ_{Ω₁}(A_{η+1}) = ψ_{Ω₁}(A_η)`. -/
theorem psi_succ_of_bad (S : InaccSeq.{0}) {η : Ordinal.{0}} (hη0 : η ≠ 0)
    (hbad : η ∉ S.CSet (ConjT.Aη S η + 1) (S.psi (ConjT.Aη S η) (Om 1))) :
    S.psi (ConjT.Aη S (η + 1)) (Om 1) = S.psi (ConjT.Aη S η) (Om 1) := by
  set Z := S.psi (ConjT.Aη S η) (Om 1) with hZdef
  have hZ : SC Z := SC_psi Low.InR_Om_one _
  have hZ1 : Z < Om 1 := psi_lt Low.InR_Om_one _
  have hbadH : ¬ HCl S (ConjT.Aη S η + 1) Z η := fun h => hbad h.mem_CSet
  have hbadH' : ¬ HCl S (ConjT.Aη S η) Z η := fun h => hbadH (h.mono le_self_add)
  have hθ : ConjT.th S ∈ S.CSet (ConjT.Aη S η) Z := by
    refine ConjT.th_mem S ?_
    unfold ConjT.Aη
    exact lt_add_of_pos_right _ (mul_pos th_pos (pos_iff_ne_zero.2 hη0))
  refine le_antisymm ?_ (psi_A_mono S le_self_add)
  rw [← ConjT.A_succ]
  refine psi_le_of_key hZ fun e he hea => ?_
  have he' := HCl_shrink hZ1 hbadH he
  rcases lt_or_ge e (Om (ω : Ordinal.{0})) with h1 | h1
  · have hlt : ConjT.Aη S 0 < ConjT.Aη S η := A_lt_A_iff.2 (pos_iff_ne_zero.2 hη0)
    have hmem : ConjT.Aη S 0 ∈ S.CSet (ConjT.Aη S η) Z := by rw [A_zero]; exact ConjT.OmW_mem S _ _
    have := psi_lt_psi_of_mem Low.InR_Om_one hlt hmem
    rw [A_zero] at this
    exact lt_of_le_of_lt (psi_mono Low.InR_Om_one h1.le).1 this
  · obtain ⟨η', hη', k1, k2⟩ := quotA hZ1 he' h1
    rw [ConjT.A_succ] at hea k2
    have hη'le : η' ≤ η := Order.lt_add_one_iff.1 (A_lt_A_iff.1 (lt_of_le_of_lt k1 hea))
    have hne : η' ≠ η := fun e => hbadH' (e ▸ hη')
    have hne1 : η' + 1 ≠ η := fun e => hbadH' (e ▸ hη'.succ)
    have hlt1 : η' + 1 < η :=
      lt_of_le_of_ne (Order.add_one_le_iff.2 (lt_of_le_of_ne hη'le hne)) hne1
    have hmem : ConjT.Aη S (η' + 1) ∈ S.CSet (ConjT.Aη S η) Z :=
      CSet.add_mem (ConjT.OmW_mem S _ _) (C_mul_th hθ _ hη'.succ.mem_CSet)
    have := psi_lt_psi_of_mem Low.InR_Om_one (A_lt_A_iff.2 hlt1) hmem
    exact lt_of_le_of_lt (psi_mono Low.InR_Om_one k2.le).1 this

end Googology.Trans.PoR.InaccPsi.R2.Bt
