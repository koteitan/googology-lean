import Googology.Notation.InaccPsi

/-!
# The countable values of InaccPsi normal forms form an initial segment

README.md, §3, Lemma IS.  For every `InaccSeq S` and every ordinal `a`:

* every ordinal below `ψ_{Ω_1}(a)` is the value of a normal form (`lt_psi_one_mem_Vals`);
* below `Ω_1`, the set of values of normal forms is downward closed
  (`mem_Vals_of_lt_of_countable`).

So the countable values of normal forms are exactly the ordinals below
`sup_a ψ_{Ω_1}(a)`.

Proof: let `ρ` be the least ordinal that is not a value.  `ρ` is closed under `+` and
`φ` (`rho_add`, `rho_veblen`; the second uses Mathlib's `invVeblen₁`, `invVeblen₂`), and
`ψ_{Ω_1}(a) ≤ ρ` by induction on `a`: `ρ` satisfies the defining condition of
`ψ_{Ω_1}(a)`, because every countable member of `Cl(a, ρ)` is below `ρ`
(induction on the closure; a countable collapse `ψ_π(e)` has `π = Ω_1`, and
`ψ_{Ω_1}(e) ≤ ρ` by the induction on `a`, with `ψ_{Ω_1}(e)` a value, so `≠ ρ`).
-/

namespace Googology.Notation.InaccPsi.Low

open Ordinal Set Googology.Notation.InaccPsi Term InaccSeq

universe u

variable {S : InaccSeq.{u}}

/-- `Cl(a, ρ)` consists of values when every ordinal below `ρ` is a value. -/
theorem CSet_subset_Vals {a ρ : Ordinal.{u}} (h : ∀ z < ρ, z ∈ Vals S) :
    S.CSet a ρ ⊆ Vals S := by
  intro x hx
  induction hx with
  | small h' => exact h _ h'
  | zero => exact zero_mem_Vals
  | inacc n => exact I_mem_Vals n
  | inaccW => exact Iw_mem_Vals
  | add _ _ ihx ihy => exact add_mem_Vals ihx ihy
  | phi _ _ ihx ihy => exact phi_mem_Vals ihx ihy
  | om _ ih => exact Om_mem_Vals ih
  | @coll π e hπ _ _ ihπ ihe =>
    rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
    · exact (psi_mem_Vals S e.1 ihe).1 n
    · exact (psi_mem_Vals S e.1 ihe).2 s (mem_Vals_of_Om_succ ihπ)

theorem InR_Om_one : S.InR (Om 1) := by
  simpa using InR_Om_succ (S := S) (0 : Ordinal.{u})

theorem Om_one_le_I (n : ℕ) : Om 1 ≤ S.I n := by
  rw [← S.fix n]
  exact Om_le_Om.2 (Order.one_le_iff_ne_zero.2 (S.I_ne_zero n))

theorem eq_zero_of_Om_lt_Om_one {x : Ordinal.{u}} (h : Om x < Om 1) : x = 0 := by
  by_contra hx
  exact absurd h (not_lt.2 (Om_le_Om.2 (Order.one_le_iff_ne_zero.2 hx)))

/-- A countable collapse is a collapse at `Ω_1`. -/
theorem eq_Om_one_of_psi_lt {π e : Ordinal.{u}} (hπ : S.InR π) (h : S.psi e π < Om 1) :
    π = Om 1 := by
  rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
  · exact absurd h (not_lt.2 (Om_one_lt_psiI (S := S) e n).le)
  · by_cases hs : s = 0
    · simp [hs]
    · exfalso
      have h1 : Om 1 ≤ Om s := Om_le_Om.2 (Order.one_le_iff_ne_zero.2 hs)
      exact absurd h (not_lt.2 (h1.trans (psiS_bounds (S := S) e s).1.le))

section rho

variable {ρ : Ordinal.{u}} (h1 : ∀ z < ρ, z ∈ Vals S) (h2 : ρ ∉ Vals S)
include h1 h2

theorem rho_pos : 0 < ρ := by
  rcases eq_or_ne ρ 0 with h | h
  · exact absurd (h ▸ zero_mem_Vals) h2
  · exact pos_iff_ne_zero.2 h

theorem rho_add {x y : Ordinal.{u}} (hx : x < ρ) (hy : y < ρ) : x + y < ρ := by
  by_contra hc
  have hc' : ρ ≤ x + y := not_lt.1 hc
  have hsub : ρ - x ≤ y := Ordinal.sub_le.2 hc'
  have hρ : x + (ρ - x) = ρ := Ordinal.add_sub_cancel_of_le hx.le
  have hmem := add_mem_Vals (h1 x hx) (h1 _ (lt_of_le_of_lt hsub hy))
  rw [hρ] at hmem
  exact h2 hmem

theorem rho_isPrincipal : IsPrincipal (· + ·) ρ := fun _ _ hx hy => rho_add h1 h2 hx hy

theorem rho_veblen {x y : Ordinal.{u}} (hx : x < ρ) (hy : y < ρ) : veblen x y < ρ := by
  obtain ⟨e, he⟩ : ρ ∈ range (ω ^ · : Ordinal.{u} → Ordinal.{u}) :=
    (isPrincipal_add_iff_zero_or_omega0_opow.1 (rho_isPrincipal h1 h2)).resolve_left
      (rho_pos h1 h2).ne'
  simp only at he
  have hab : veblen (invVeblen₁ e) (invVeblen₂ e) = ρ := by
    rw [veblen_invVeblen₁_invVeblen₂, he]
  have hbρ : invVeblen₂ e < ρ := by
    refine lt_of_le_of_ne (hab ▸ right_le_veblen _ _) ?_
    intro hb
    have h3 : veblen (invVeblen₁ e) (ω ^ e) = ω ^ e := by
      rw [he]; nth_rewrite 1 [← hb]; exact hab
    have h4 : veblen (invVeblen₁ e) e = e := veblen_opow_eq_opow_iff.1 h3
    exact absurd h4 (lt_veblen_invVeblen₁ e).ne'
  have haρ : invVeblen₁ e ≤ ρ :=
    (invVeblen₁_le e).trans (he ▸ right_le_opow e one_lt_omega0)
  rcases lt_or_eq_of_le haρ with ha | ha
  · exfalso
    have hmem := phi_mem_Vals (h1 _ ha) (h1 _ hbρ)
    rw [hab] at hmem
    exact h2 hmem
  · have hfix : veblen x ρ = ρ := by
      have hxa : x < invVeblen₁ e := ha ▸ hx
      rw [← hab]
      exact veblen_veblen_of_lt hxa _
    calc veblen x y < veblen x ρ := veblen_lt_veblen_iff_right.2 hy
      _ = ρ := hfix

/-- **Key step.** `ψ_{Ω_1}(a) ≤ ρ` for every `a`. -/
theorem psi_one_le_rho : ∀ a : Ordinal.{u}, S.psi a (Om 1) ≤ ρ := by
  intro a
  induction a using WellFoundedLT.induction with
  | _ a IH =>
  refine psi_le_of_good (CSet.Om_mem (CSet.one_mem a ρ)) ?_
  intro x hx
  induction hx with
  | small h => exact fun _ => h
  | zero => exact fun _ => rho_pos h1 h2
  | inacc n => exact fun h => absurd h (not_lt.2 (Om_one_le_I n))
  | inaccW => exact fun h => absurd h (not_lt.2 ((Om_one_le_I 0).trans (S.I_le_Iw 0)))
  | add _ _ ihx ihy =>
    intro h
    exact rho_add h1 h2 (ihx (lt_of_le_of_lt le_self_add h))
      (ihy (lt_of_le_of_lt le_add_self h))
  | phi _ _ ihx ihy =>
    intro h
    exact rho_veblen h1 h2 (ihx (lt_of_le_of_lt (left_le_veblen _ _) h))
      (ihy (lt_of_le_of_lt (right_le_veblen _ _) h))
  | @om x _ _ =>
    intro h
    rw [eq_zero_of_Om_lt_Om_one h, Om_zero]
    exact rho_pos h1 h2
  | @coll π e hπ _ heC _ _ =>
    intro h
    have h' : S.psi e.1 π < Om 1 := h
    have hπ1 := eq_Om_one_of_psi_lt hπ h'
    subst hπ1
    have hle : S.psi e.1 (Om 1) ≤ ρ := IH e.1 e.2
    have he : e.1 ∈ Vals S := CSet_subset_Vals h1 (a := a) heC
    have hmem : S.psi e.1 (Om 1) ∈ Vals S := by
      simpa using (psi_mem_Vals S e.1 he).2 0 zero_mem_Vals
    show S.psi e.1 (Om 1) < ρ
    exact lt_of_le_of_ne hle (fun hc => h2 (hc ▸ hmem))

end rho

/-- **Theorem IS (a).** Every ordinal below `ψ_{Ω_1}(a)` is the value of a normal form. -/
theorem lt_psi_one_mem_Vals (a z : Ordinal.{u}) (hz : z < S.psi a (Om 1)) : z ∈ Vals S := by
  by_contra hzV
  have hne : {w : Ordinal.{u} | w ∉ Vals S}.Nonempty := ⟨z, hzV⟩
  have h2 : sInf {w : Ordinal.{u} | w ∉ Vals S} ∉ Vals S := csInf_mem hne
  have h1 : ∀ w < sInf {w : Ordinal.{u} | w ∉ Vals S}, w ∈ Vals S := fun w hw => by
    by_contra hw'
    exact absurd hw (not_lt.2 (csInf_le' hw'))
  have hle : sInf {w : Ordinal.{u} | w ∉ Vals S} ≤ z := csInf_le' hzV
  exact absurd hz (not_lt.2 ((psi_one_le_rho h1 h2 a).trans hle))

/-- **Theorem IS (a), as normal forms.** -/
theorem exists_NF_of_lt_psi_one (a z : Ordinal.{u}) (hz : z < S.psi a (Om 1)) :
    ∃ t : Term, t.NF ∧ val S t = z :=
  lt_psi_one_mem_Vals a z hz

/-- **Theorem IS (b).** A countable value of a normal form bounds only values:
the countable values of normal forms form an initial segment of `Ω_1`. -/
theorem mem_Vals_of_lt_of_countable {x z : Ordinal.{u}} (hx : x ∈ Vals S) (hxΩ : x < Om 1)
    (hz : z < x) : z ∈ Vals S := by
  obtain ⟨t, -, rfl⟩ := hx
  obtain ⟨a, ha⟩ := exists_mem_CSet S t
  have hx' : val S t ∈ S.CSet a (S.psi a (Om 1)) := CSet_mono le_rfl zero_le ha
  have hlt : val S t < S.psi a (Om 1) := lt_psi_of_mem InR_Om_one hx' hxΩ
  exact lt_psi_one_mem_Vals a z (hz.trans hlt)

/-- **Lemma CONT.** `ψ_{Ω_1}` is continuous along increasing ω-sequences. -/
theorem psi_one_iSup {f : ℕ → Ordinal.{u}} (hf : Monotone f) :
    S.psi (⨆ n, f n) (Om 1) = ⨆ n, S.psi (f n) (Om 1) := by
  have hbdd : BddAbove (range f) := Ordinal.bddAbove_of_small
  have hbdd' : BddAbove (range fun n => S.psi (f n) (Om 1)) := Ordinal.bddAbove_of_small
  set σ := ⨆ n, S.psi (f n) (Om 1) with hσ
  have hg : Monotone fun n => S.psi (f n) (Om 1) := fun m n hmn =>
    (psi_mono InR_Om_one (hf hmn)).1
  -- every member of `Cl(sup f, σ)` lies in some `Cl(f N, ψ_{Ω_1}(f N))`
  have key : ∀ x ∈ S.CSet (⨆ n, f n) σ, ∃ N, x ∈ S.CSet (f N) (S.psi (f N) (Om 1)) := by
    intro x hx
    have up : ∀ {y : Ordinal.{u}} {N M : ℕ}, N ≤ M →
        y ∈ S.CSet (f N) (S.psi (f N) (Om 1)) → y ∈ S.CSet (f M) (S.psi (f M) (Om 1)) :=
      fun hNM hy => CSet_mono (hf hNM) (hg hNM) hy
    induction hx with
    | small h =>
      obtain ⟨m, hm⟩ := (lt_ciSup_iff hbdd').1 h
      exact ⟨m, CSet.of_lt hm⟩
    | zero => exact ⟨0, CSet.zero_mem _ _⟩
    | inacc n => exact ⟨0, CSet.I_mem _ _ n⟩
    | inaccW => exact ⟨0, CSet.Iw_mem _ _⟩
    | add _ _ ihx ihy =>
      obtain ⟨N1, h1⟩ := ihx
      obtain ⟨N2, h2⟩ := ihy
      exact ⟨max N1 N2, CSet.add_mem (up (le_max_left _ _) h1) (up (le_max_right _ _) h2)⟩
    | phi _ _ ihx ihy =>
      obtain ⟨N1, h1⟩ := ihx
      obtain ⟨N2, h2⟩ := ihy
      exact ⟨max N1 N2, CSet.phi_mem (up (le_max_left _ _) h1) (up (le_max_right _ _) h2)⟩
    | om _ ih =>
      obtain ⟨N1, h1⟩ := ih
      exact ⟨N1, CSet.Om_mem h1⟩
    | @coll π e hπ _ _ ihπ ihe =>
      obtain ⟨N1, h1⟩ := ihπ
      obtain ⟨N2, h2⟩ := ihe
      obtain ⟨m, hm⟩ := (lt_ciSup_iff hbdd).1 e.2
      refine ⟨max m (max N1 N2), ?_⟩
      have he : e.1 < f (max m (max N1 N2)) := lt_of_lt_of_le hm (hf (le_max_left _ _))
      exact CSet.psi_mem he hπ
        (up (le_trans (le_max_left _ _) (le_max_right _ _)) h1)
        (up (le_trans (le_max_right _ _) (le_max_right _ _)) h2)
  apply le_antisymm
  · refine psi_le_of_good (CSet.Om_mem (CSet.one_mem _ _)) ?_
    intro x hx hxΩ
    obtain ⟨N, hN⟩ := key x hx
    exact lt_of_lt_of_le (lt_psi_of_mem InR_Om_one hN hxΩ) (le_ciSup hbdd' N)
  · exact ciSup_le fun n => (psi_mono InR_Om_one (le_ciSup hbdd n)).1

end Googology.Notation.InaccPsi.Low
