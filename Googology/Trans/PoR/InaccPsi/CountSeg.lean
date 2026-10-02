import Googology.Notation.InaccPsi.Onto

/-!
# The countable part of `Cl(α, 0)` is the ordinal `ψ_{Ω_1}(α)`

Lemma L of README.md, §3:

* `Cl(α, 0) ∩ Ω_1 = ψ_{Ω_1}(α)` for every `α` (`CSet_inter_Om1`);
* the countable values of the NF terms form the ordinal `ψ_{Ω_1}(Λ)`
  (`vals_inter_Om1`), `Λ` = least fixed point of `Ω` above `I_ω` (`Lam`).
-/

namespace Googology.Notation.InaccPsi

open Ordinal Set

universe u

namespace InaccSeq

variable {S : InaccSeq.{u}}

/-- A set with `0` that is closed under `+` and `φ` and contains `ξ, η` and everything
below them contains everything below `φ(ξ, η)`. -/
theorem veblen_downward {T : Set Ordinal.{u}}
    (hadd : ∀ x y, x ∈ T → y ∈ T → x + y ∈ T)
    (hphi : ∀ x y, x ∈ T → y ∈ T → veblen x y ∈ T) {ξ η : Ordinal.{u}}
    (hξ : ξ ∈ T) (hη : η ∈ T) (hξ' : ∀ y < ξ, y ∈ T) (hη' : ∀ y < η, y ∈ T) :
    ∀ y < veblen ξ η, y ∈ T := by
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
    intro hy
    by_cases h1 : y ≤ ξ
    · rcases h1.lt_or_eq with h | h
      · exact hξ' y h
      · rw [h]; exact hξ
    by_cases h2 : y ≤ η
    · rcases h2.lt_or_eq with h | h
      · exact hη' y h
      · rw [h]; exact hη
    have hξy : ξ < y := lt_of_not_ge h1
    have hηy : η < y := lt_of_not_ge h2
    have hy0 : y ≠ 0 := (lt_of_le_of_lt zero_le hξy).ne'
    by_cases ht : tail y = 0
    · -- `y = ω^x` is additively principal
      have hyl : lead y = y := by
        have := lead_add_tail hy0; rwa [ht, add_zero] at this
      set x := Ordinal.log ω y with hx
      have hyx : ω ^ x = y := hyl
      have hv := veblen_invVeblen₁_invVeblen₂ x
      rw [hyx] at hv
      have hb : invVeblen₂ x < y := by
        have := invVeblen₂_lt x; rwa [hyx] at this
      have ha : invVeblen₁ x ≤ y :=
        (invVeblen₁_le x).trans (by rw [← hyx]; exact right_le_opow x one_lt_omega0)
      rcases ha.lt_or_eq with ha | ha
      · rw [← hv]
        exact hphi _ _ (IH _ ha (ha.trans hy)) (IH _ hb (hb.trans hy))
      · -- `y = φ(y, b)`: then `φ(ξ, η) < y`, impossible
        exfalso
        have : veblen ξ η < veblen (invVeblen₁ x) (invVeblen₂ x) := by
          rw [veblen_lt_veblen_iff]
          refine Or.inr (Or.inl ⟨by rw [ha]; exact hξy, ?_⟩)
          rw [hv]; exact hηy
        rw [hv] at this
        exact lt_asymm this hy
    · -- `y = lead y + tail y` with both parts below `y`
      have hsum := lead_add_tail hy0
      have htl : tail y < y := tail_lt hy0
      have hll : lead y < y := by
        conv_rhs => rw [← hsum]
        exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 ht)
      rw [← hsum]
      exact hadd _ _ (IH _ hll (hll.trans hy)) (IH _ htl (htl.trans hy))

theorem one_lt_I (n : ℕ) : (1 : Ordinal.{u}) < S.I n := by
  have h := Om_one_lt_psiI (S := S) 0 n
  have h2 := psi_lt (InR_I (S := S) n) 0
  exact lt_of_le_of_lt (le_Om 1) (h.trans h2)

/-- If `δ ⊆ Cl(a, 0)` then `Cl(a, δ) ⊆ Cl(a, 0)`. -/
theorem CSet_sub_zero {a δ : Ordinal.{u}} (hδ : ∀ y < δ, y ∈ S.CSet a 0) :
    S.CSet a δ ⊆ S.CSet a 0 := by
  intro x hx
  induction hx with
  | small h => exact hδ _ h
  | zero => exact CSet.zero_mem a 0
  | inacc n => exact CSet.I_mem a 0 n
  | inaccW => exact CSet.Iw_mem a 0
  | add _ _ ihx ihy => exact CSet.add_mem ihx ihy
  | phi _ _ ihx ihy => exact CSet.phi_mem ihx ihy
  | om _ ih => exact CSet.Om_mem ih
  | @coll π e hπ _ _ ihπ ihe => exact CSet.psi_mem e.2 hπ ihπ ihe

/-- **Lemma L, inner part.** If `Cl(e, 0) ∩ Ω_1` is downward closed, every ordinal
below `ψ_{Ω_1}(e)` is in `Cl(e, 0)`. -/
theorem lt_psi_mem_of_down {e : Ordinal.{u}}
    (hdown : ∀ x ∈ S.CSet e 0, x < Om 1 → ∀ y < x, y ∈ S.CSet e 0) :
    ∀ y < S.psi e (Om 1), y ∈ S.CSet e 0 := by
  have hne : {y | y ∉ S.CSet e 0}.Nonempty :=
    ⟨S.Lam, fun h => lt_irrefl _ (lt_Lam_of_mem zero_le h)⟩
  set δ := sInf {y | y ∉ S.CSet e 0} with hδdef
  have hδ : ∀ y < δ, y ∈ S.CSet e 0 := fun y hy => by
    by_contra h; exact absurd (csInf_le' h) (not_le.2 hy)
  have hδnot : δ ∉ S.CSet e 0 := csInf_mem hne
  have hκ : S.InR (Om 1) := by
    have := InR_Om_succ (S := S) 0; rwa [zero_add] at this
  have hle : S.psi e (Om 1) ≤ δ := by
    refine psi_le_of_good (CSet.Om_mem (CSet.one_mem e δ)) fun x hx hx1 => ?_
    have hx0 := CSet_sub_zero hδ hx
    by_contra hxδ
    rcases (not_lt.1 hxδ).lt_or_eq with h | h
    · exact hδnot (hdown x hx0 hx1 δ h)
    · exact hδnot (h ▸ hx0)
  exact fun y hy => hδ y (lt_of_lt_of_le hy hle)

/-- **Lemma L.** `Cl(a, 0) ∩ Ω_1` is downward closed. -/
theorem CSet_down (a : Ordinal.{u}) :
    ∀ x ∈ S.CSet a 0, x < Om 1 → ∀ y < x, y ∈ S.CSet a 0 := by
  induction a using WellFoundedLT.induction with
  | ind a IHa =>
    intro x hx
    induction hx with
    | small h => exact absurd h (not_lt.2 zero_le)
    | zero => intro _ y hy; exact absurd hy (not_lt.2 zero_le)
    | inacc n =>
      intro h1; exfalso
      have : Om 1 < S.I n := by rw [← Om_I n, Om_lt_Om]; exact one_lt_I n
      exact lt_asymm h1 this
    | inaccW =>
      intro h1; exfalso
      have : Om 1 < S.I 0 := by rw [← Om_I 0, Om_lt_Om]; exact one_lt_I 0
      exact lt_asymm h1 (this.trans (S.I_lt_Iw 0))
    | @add x y hx hy ihx ihy =>
      intro h1 z hz
      have hxl : x < Om 1 := lt_of_le_of_lt (le_self_add) h1
      have hyl : y < Om 1 := lt_of_le_of_lt (le_add_self) h1
      by_cases hzx : z < x
      · exact ihx hxl z hzx
      · have hxz : x ≤ z := not_lt.1 hzx
        have hz' : x + (z - x) = z := Ordinal.add_sub_cancel_of_le hxz
        have hlt : z - x < y := by
          rw [← hz'] at hz; exact (add_lt_add_iff_left x).1 hz
        rw [← hz']
        exact CSet.add_mem hx (ihy hyl _ hlt)
    | @phi x y hx hy ihx ihy =>
      intro h1
      have hxl : x < Om 1 := lt_of_le_of_lt (left_le_veblen x y) h1
      have hyl : y < Om 1 := lt_of_le_of_lt (right_le_veblen x y) h1
      exact veblen_downward (T := S.CSet a 0) (fun _ _ => CSet.add_mem)
        (fun _ _ => CSet.phi_mem) hx hy (ihx hxl) (ihy hyl)
    | @om x hx ih =>
      intro h1 z hz
      have hx1 : x < 1 := Om_lt_Om.1 h1
      have hx0 : x = 0 := Order.lt_one_iff.1 hx1
      rw [hx0, Om_zero] at hz
      exact absurd hz (not_lt.2 zero_le)
    | @coll π e hπ hπC heC ihπ ihe =>
      intro h1 z hz
      -- the subscript is `Ω_1`
      have hπ1 : π = Om 1 := by
        rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
        · exact absurd h1 (not_lt.2 (Om_one_lt_psiI e.1 n).le)
        · have hb := (psiS_bounds (S := S) e.1 s).1
          by_cases hs : s = 0
          · rw [hs, zero_add]
          · exfalso
            have : Om 1 ≤ Om s :=
              Om_le_Om.2 (Order.one_le_iff_ne_zero.2 hs)
            exact lt_asymm h1 (lt_of_le_of_lt this hb)
      subst hπ1
      have hdown_e : ∀ x ∈ S.CSet e.1 0, x < Om 1 → ∀ y < x, y ∈ S.CSet e.1 0 :=
        IHa e.1 e.2
      exact CSet_mono e.2.le le_rfl (lt_psi_mem_of_down hdown_e z hz)

theorem InR_Om1 : S.InR (Om 1) := by
  have := InR_Om_succ (S := S) 0; rwa [zero_add] at this

/-- **Lemma L.** `Cl(a, 0) ∩ Ω_1 = ψ_{Ω_1}(a)`. -/
theorem CSet_inter_Om1 (a : Ordinal.{u}) :
    S.CSet a 0 ∩ Iio (Om 1) = Iio (S.psi a (Om 1)) := by
  ext x
  constructor
  · rintro ⟨hx, hx1⟩
    exact lt_psi_of_mem InR_Om1 (CSet_mono le_rfl zero_le hx) hx1
  · intro hx
    exact ⟨lt_psi_mem_of_down (CSet_down a) x hx,
      lt_trans hx (psi_lt InR_Om1 a)⟩

/-- Every `Cl(a, 0)` is contained in `Cl(Λ, 0)`. -/
theorem CSet_sub_Lam (a : Ordinal.{u}) : S.CSet a 0 ⊆ S.CSet S.Lam 0 := by
  intro x hx
  induction hx with
  | small h => exact absurd h (not_lt.2 zero_le)
  | zero => exact CSet.zero_mem _ 0
  | inacc n => exact CSet.I_mem _ 0 n
  | inaccW => exact CSet.Iw_mem _ 0
  | add _ _ ihx ihy => exact CSet.add_mem ihx ihy
  | phi _ _ ihx ihy => exact CSet.phi_mem ihx ihy
  | om _ ih => exact CSet.Om_mem ih
  | @coll π e hπ _ heC ihπ ihe =>
    exact CSet.psi_mem (lt_Lam_of_mem zero_le ihe) hπ ihπ ihe

end InaccSeq

namespace Term

variable (S : InaccSeq.{u})

/-- **The countable values of the whole system are the ordinal `ψ_{Ω_1}(Λ)`.** -/
theorem vals_inter_Om1 :
    {x | ∃ t : Term, t.NF ∧ val S t = x} ∩ Iio (Om 1) =
      Iio (S.psi S.Lam (Om 1)) := by
  rw [vals_eq, ← InaccSeq.CSet_inter_Om1]
  congr 1
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hx
    exact InaccSeq.CSet_sub_Lam a ha
  · intro x hx
    exact Set.mem_iUnion.2 ⟨S.Lam, hx⟩

/-- **The bounded systems.** For a normal form `X`, the countable values of the normal
forms `t` with `K_0(t) < X` (all collapse arguments below `X`) are `ψ_{Ω_1}(|X|)`. -/
theorem bounded_inter_Om1 {X : Term} (hX : NF X) :
    {x | ∃ t : Term, t.NF ∧ KLt zero t X ∧ val S t = x} ∩ Iio (Om 1) =
      Iio (S.psi (val S X) (Om 1)) := by
  rw [← InaccSeq.CSet_inter_Om1]
  congr 1
  ext x
  constructor
  · rintro ⟨t, ht, hK, rfl⟩
    exact KLt_sound_NF S (show NF zero from trivial) hX ht hK
  · intro hx
    obtain ⟨t, ht, rfl⟩ := exists_NF S (Set.mem_iUnion.2 ⟨_, hx⟩)
    refine ⟨t, ht, ?_, rfl⟩
    exact KLt_complete (S := S) (μ := zero) (α := X)
      (fun _ _ h => absurd h (not_lt.2 zero_le))
      (fun y hy h => (cmp_lt_iff S hy hX).2 h) zero_le ht hx

end Term

namespace InaccSeq
variable {S : InaccSeq.{u}}

/-- The three candidate bounds give three different countable segments:
`ψ_{Ω_1}(I_ω) < ψ_{Ω_1}(ε_{I_ω+1}) < ψ_{Ω_1}(Λ)` (here `ε_{I_ω+1} = φ(1, I_ω+1)`). -/
theorem three_bounds :
    S.psi S.Iw (Om 1) < S.psi (veblen 1 (S.Iw + 1)) (Om 1) ∧
      S.psi (veblen 1 (S.Iw + 1)) (Om 1) < S.psi S.Lam (Om 1) := by
  have hE : veblen 1 (S.Iw + 1) ∈ S.CSet (veblen 1 (S.Iw + 1)) (S.psi (veblen 1 (S.Iw + 1)) (Om 1)) :=
    CSet.phi_mem (CSet.one_mem _ _) (CSet.succ_mem (CSet.Iw_mem _ _))
  have h1 : S.Iw < veblen 1 (S.Iw + 1) :=
    lt_of_lt_of_le (lt_add_one _) (right_le_veblen _ _)
  have h2 : veblen 1 (S.Iw + 1) < S.Lam := veblen_lt_Lam one_lt_Lam (add_one_lt_Lam Iw_lt_Lam)
  exact ⟨psi_lt_psi InR_Om1 h1 (CSet.Iw_mem _ _), psi_lt_psi InR_Om1 h2 hE⟩

end InaccSeq

end Googology.Notation.InaccPsi

#print axioms Googology.Notation.InaccPsi.Term.vals_inter_Om1
#print axioms Googology.Notation.InaccPsi.Term.bounded_inter_Om1
#print axioms Googology.Notation.InaccPsi.InaccSeq.CSet_inter_Om1
#print axioms Googology.Notation.InaccPsi.InaccSeq.three_bounds
