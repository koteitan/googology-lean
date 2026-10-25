import Googology.Trans.PoR.InaccPsi.R2.UlCode
import Googology.Trans.PoR.InaccPsi.R2.UiArgs

/-!
# Below `ψ_{Ω_{s+2}}(B)` every collapse argument (of a subterm `≥ Ω_{s+1}`) is below `B`: visibility of the lifted
# levels

`W = Ω_{s+1}`, `V = Ω_{s+2}`, `ψ_V = S.psi · V`, `Cl(A, q) = S.CSet A q`, `ulDat`, `ulArgs` (`R2.UlCode`, threshold
`κ = W`).  A *lifted level* is an ordinal `γ ∈ [W, V)` whose components are `≥ W` (atoms `ψ_V(e)`); the least own
`B` with `γ < ψ_V(B)` is the `V`-part `A(γ)` that sees every argument of `γ`.  Here, for every own `B` (`B ∈ Cl(B,
ψ_V(B))`) and every `γ < ψ_V(B)` of the notation, the arguments of `γ` are below `B`, so that membership of `γ` in a
hull `Cl(A, q)`, `A ≥ B`, `q ≤ W`, depends on the leaves of `γ` below `W` only:

* `ulArgsT_mono`, `ul_args_hull` (**the hull lemma for the arguments above a point `q`**);
* `ul_args_psi` (**every `z < ψ_{Ω_{s+2}}(B)` of the notation, `B` own, has every collapse argument of a subterm
  `≥ Ω_{s+1}` below `B`**: the atoms `ψ_V(e)` of `z` have `e` own and `ψ_V(e) < ψ_V(B)`, so `e < B`, and the arguments
  inside `e` are below `e` by the hull lemma at `q = ψ_V(e)`);
* `ul_code_psi` (**the visibility test of a lifted level**: for `γ < ψ_V(B)` of the notation, `B` own, `B ≤ A`,
  `0 < q ≤ W`, `Cl(A, q) ∩ W ⊆ q`: `γ ∈ Cl(A, q) ↔ ulDat W γ < q`);
* `ul_zero_th` (**at `s = 0`, `B = Ω_ω` this is `Ui.ui_code_th`**, the code test below `θ = ψ_{Ω₂}(Ω_ω)`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ul

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2

variable {S : InaccSeq.{0}} {κ : Ordinal.{0}}

theorem ulArgsT_mono {A A' : Ordinal.{0}} (hA : A ≤ A') : ∀ t : Term, ulArgsT S κ A t → ulArgsT S κ A' t := by
  intro t
  induction t with
  | zero => intro _; trivial
  | inacc n => intro _; trivial
  | inaccW => intro _; trivial
  | add a b iha ihb =>
    intro h; rcases h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨iha h.1, ihb h.2⟩
  | phi a b iha ihb =>
    intro h; rcases h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨iha h.1, ihb h.2⟩
  | om a iha =>
    intro h; rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (iha h)
  | psiS s a ihs iha =>
    intro h; rcases h with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1.trans_le hA, ihs h2, iha h3⟩
  | psiI n a iha =>
    intro h; rcases h with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1.trans_le hA, iha h2⟩

/-- **The hull lemma for the arguments above `q`**: a normal form `t` with `val t ∈ Cl(A, q)`, `A ≤ B`, has every
collapse argument of a subterm `≥ κ` below `B`, once the normal forms with values in `[κ, q)` have. -/
theorem ul_args_hull {A B q : Ordinal.{0}} (hκ0 : 0 < κ) (hqL : q ≤ S.Lam) (hAB : A ≤ B)
    (hlow : ∀ u : Term, NF u → κ ≤ val S u → val S u < q → ulArgsT S κ B u) :
    ∀ t : Term, NF t → val S t ∈ S.CSet A q → ulArgsT S κ B t := by
  intro t
  induction t with
  | zero => intro _ _; trivial
  | inacc n => intro _ _; trivial
  | inaccW => intro _ _; trivial
  | add a b iha ihb =>
    intro hN hm
    by_cases h : val S (add a b) < κ
    · exact Or.inl h
    by_cases hq : val S (add a b) < q
    · exact hlow _ hN (not_lt.1 h) hq
    have h0 : val S (add a b) ≠ 0 := fun e => h (by rw [e]; exact hκ0)
    obtain ⟨hl, ht⟩ := lead_tail_mem hm h0
    obtain ⟨hla, htb⟩ := Ui.ui_add_parts (S := S) hN
    rw [hla] at hl; rw [htb] at ht
    exact Or.inr ⟨iha hN.1 hl, ihb hN.2.1 ht⟩
  | phi a b iha ihb =>
    intro hN hm
    by_cases h : val S (phi a b) < κ
    · exact Or.inl h
    by_cases hq : val S (phi a b) < q
    · exact hlow _ hN (not_lt.1 h) hq
    have hN' := hN
    obtain ⟨hNa, hNb, hca, hcb⟩ := hN
    have hav : val S a < val S (phi a b) := by
      have e := Term.cmp_eq_compare S hNa hN'
      rw [e] at hca; exact compare_lt_iff_lt.1 hca
    have hbv : val S b < val S (phi a b) := by
      have e := Term.cmp_eq_compare S hNb hN'
      rw [e] at hcb; exact compare_lt_iff_lt.1 hcb
    obtain ⟨hma, hmb⟩ := mem_of_veblen_mem hm hav hbv
    exact Or.inr ⟨iha hNa hma, ihb hNb hmb⟩
  | om a iha =>
    intro hN hm
    by_cases h : val S (om a) < κ
    · exact Or.inl h
    by_cases hq : val S (om a) < q
    · exact hlow _ hN (not_lt.1 h) hq
    exact Or.inr (iha hN.1 (mem_of_Om_mem hm))
  | psiS s a ihs iha =>
    intro hN hm
    by_cases h : val S (psiS s a) < κ
    · exact Or.inl h
    by_cases hq : val S (psiS s a) < q
    · exact hlow _ hN (not_lt.1 h) hq
    have hβz : q ≤ S.psi (val S a) (Om (val S s + 1)) := not_lt.1 hq
    have hsem := Term.sem_of_NF (S := S) hN
    obtain ⟨hma, hlt⟩ := arg_mem_of_psi_mem (InR_Om_succ _) hm hβz hqL hsem.2.2
    have hms := Ui.ui_sub_mem_of_psi_mem (S := S) hm hβz
    exact Or.inr ⟨hlt.trans_le hAB, ihs hN.1 hms, iha hN.2.1 hma⟩
  | psiI n a iha =>
    intro hN hm
    by_cases h : val S (psiI n a) < κ
    · exact Or.inl h
    by_cases hq : val S (psiI n a) < q
    · exact hlow _ hN (not_lt.1 h) hq
    have hβz : q ≤ S.psi (val S a) (S.I n) := not_lt.1 hq
    have hsem := Term.sem_of_NF (S := S) hN
    obtain ⟨hma, hlt⟩ := arg_mem_of_psi_mem (InR_I n) hm hβz hqL hsem.2
    exact Or.inr ⟨hlt.trans_le hAB, iha hN.1 hma⟩

/-- Finite ordinals: `s + 1 + 1 < ω` for `s < ω`. -/
theorem ul_fin2 {s : Ordinal.{0}} (hs : s < ω) : s + 1 + 1 < ω := by
  obtain ⟨n, rfl⟩ := lt_omega0.1 hs
  exact_mod_cast natCast_lt_omega0 (n + 1 + 1)

/-- `ω ≤ Ω_{s+1}`. -/
theorem ul_omega_le_W (s : Ordinal.{0}) : ω ≤ Om (s + 1) := by
  have h0 : s + 1 ≠ 0 := (Order.lt_add_one_iff.2 zero_le).ne'
  rw [Om_of_ne_zero h0]; exact omega0_le_omega (s + 1)

/-- **Every `z < ψ_{Ω_{s+2}}(B)` of the notation, `B` own, has every collapse argument of a subterm `≥ Ω_{s+1}`
below `B`.** -/
theorem ul_args_psi {s : Ordinal.{0}} (hs : s < ω) {B : Ordinal.{0}}
    (hownB : B ∈ S.CSet B (S.psi B (Om (s + 1 + 1)))) :
    ∀ z, z ∈ ⋃ a, S.CSet a 0 → z < S.psi B (Om (s + 1 + 1)) → ulArgs S (Om (s + 1)) B z := by
  have hκV : S.InR (Om (s + 1 + 1)) := InR_Om_succ (s + 1)
  have hω2 := ul_fin2 hs
  have hωW := ul_omega_le_W s
  have hW0 : (0 : Ordinal.{0}) < Om (s + 1) := omega0_pos.trans_le hωW
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hz hzθ
  obtain ⟨hN, hv⟩ := Bc.bcNf_spec S hz
  have hsub : ∀ u : Term, NF u → val S u < z → ulArgsT S (Om (s + 1)) B u := fun u hu hlt => by
    have h := IH (val S u) hlt (Set.mem_iUnion.2 (exists_mem_CSet S u)) (hlt.trans hzθ)
    unfold ulArgs at h; rwa [Bc.bcNf_val S hu] at h
  have hz2 : z < Om (s + 1 + 1) := hzθ.trans (psi_lt hκV B)
  unfold ulArgs
  generalize Bc.bcNf S z = t at hN hv
  subst hv
  cases t with
  | zero => trivial
  | inacc n => trivial
  | inaccW => trivial
  | add a b =>
    by_cases h : val S (add a b) < Om (s + 1)
    · exact Or.inl h
    have h0 : val S (add a b) ≠ 0 := fun e => h (by rw [e]; exact hW0)
    obtain ⟨hla, htb⟩ := Ui.ui_add_parts (S := S) hN
    have htl : tail (val S (add a b)) < val S (add a b) := tail_lt h0
    have hb0 : val S b ≠ 0 := Term.val_ne_zero (S := S) hN.2.1 hN.2.2.2.1
    have hal : lead (val S (add a b)) < val S (add a b) := by
      conv_rhs => rw [← lead_add_tail h0]
      rw [htb]; exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hb0)
    rw [hla] at hal; rw [htb] at htl
    exact Or.inr ⟨hsub a hN.1 hal, hsub b hN.2.1 htl⟩
  | phi a b =>
    by_cases h : val S (phi a b) < Om (s + 1)
    · exact Or.inl h
    have hN' := hN
    obtain ⟨hNa, hNb, hca, hcb⟩ := hN
    have hav : val S a < val S (phi a b) := by
      have e := Term.cmp_eq_compare S hNa hN'
      rw [e] at hca; exact compare_lt_iff_lt.1 hca
    have hbv : val S b < val S (phi a b) := by
      have e := Term.cmp_eq_compare S hNb hN'
      rw [e] at hcb; exact compare_lt_iff_lt.1 hcb
    exact Or.inr ⟨hsub a hNa hav, hsub b hNb hbv⟩
  | om a =>
    by_cases h : val S (om a) < Om (s + 1)
    · exact Or.inl h
    refine Or.inr (hsub a hN.1 ?_)
    have h2 : val S a < s + 1 + 1 := Om_lt_Om.1 hz2
    exact (h2.trans hω2).trans_le (hωW.trans (not_lt.1 h))
  | psiS s' a =>
    by_cases h : val S (psiS s' a) < Om (s + 1)
    · exact Or.inl h
    have hsem := Term.sem_of_NF (S := S) hN
    set σ := val S s' with hσ
    have hb := psiS_bounds (S := S) (val S a) σ
    have hσ1 : σ = s + 1 := by
      have h1 : Om σ < Om (s + 1 + 1) := hb.1.trans hz2
      have h3 : Om (s + 1) < Om (σ + 1) := (not_lt.1 h).trans_lt hb.2
      have ha : σ < s + 1 + 1 := Om_lt_Om.1 h1
      have hb' : s + 1 < σ + 1 := Om_lt_Om.1 h3
      exact le_antisymm (Order.lt_add_one_iff.1 ha) (Order.lt_add_one_iff.1 hb')
    have hval : val S (psiS s' a) = S.psi (val S a) (Om (s + 1 + 1)) := by
      simp only [val]; rw [← hσ, hσ1]
    have hown : val S a ∈ S.CSet (val S a) (S.psi (val S a) (Om (s + 1 + 1))) := by
      have := hsem.2.2; rw [← hσ, hσ1] at this; exact this
    have haB : val S a < B := by
      have h1 := compare_psi hκV hown hownB
      have h2 : S.psi (val S a) (Om (s + 1 + 1)) < S.psi B (Om (s + 1 + 1)) := by
        rw [← hval]; exact hzθ
      rw [compare_lt_iff_lt.2 h2] at h1
      exact compare_lt_iff_lt.1 h1.symm
    have hs1 : σ < val S (psiS s' a) := by
      rw [hσ1]
      exact ((Order.lt_add_one_iff.2 le_rfl).trans hω2).trans_le (hωW.trans (not_lt.1 h))
    have hsa := hsub s' hN.1 hs1
    have hqL : val S (psiS s' a) ≤ S.Lam := (val_lt_Lam S _).le
    refine Or.inr ⟨haB, hsa, ul_args_hull (A := val S a) (B := B) (q := val S (psiS s' a)) hW0 hqL
      haB.le (fun u hu _ hlt => hsub u hu hlt) a hN.2.1 ?_⟩
    rw [hval]; exact hown
  | psiI n a =>
    by_cases h : val S (psiI n a) < Om (s + 1)
    · exact Or.inl h
    exfalso
    have hfix : Om (val S (psiI n a)) = val S (psiI n a) := Om_psiI _ n
    have h2 : val S (psiI n a) < s + 1 + 1 := by
      have := hz2; rw [← hfix] at this; exact Om_lt_Om.1 this
    exact absurd ((h2.trans hω2).trans_le (hωW.trans (not_lt.1 h))) (lt_irrefl _)

/-- **The visibility test of a lifted level**: for `γ < ψ_{Ω_{s+2}}(B)` of the notation, `B` own, `B ≤ A`,
`0 < q ≤ Ω_{s+1}`, `q ≤ Λ` and `Cl(A, q) ∩ Ω_{s+1} ⊆ q`: `γ ∈ Cl(A, q) ↔ ulDat Ω_{s+1} γ < q`. -/
theorem ul_code_psi {s : Ordinal.{0}} (hs : s < ω) {A B q γ : Ordinal.{0}}
    (hownB : B ∈ S.CSet B (S.psi B (Om (s + 1 + 1)))) (hγ : γ ∈ ⋃ a, S.CSet a 0)
    (hγB : γ < S.psi B (Om (s + 1 + 1))) (hBA : B ≤ A) (hq1 : q ≤ Om (s + 1)) (hqL : q ≤ S.Lam)
    (hcl : ∀ y ∈ S.CSet A q, y < Om (s + 1) → y < q) (hq0 : 0 < q) :
    γ ∈ S.CSet A q ↔ ulDat S (Om (s + 1)) γ < q := by
  rw [ul_code_iff hγ hq1 hqL hcl hq0]
  exact ⟨fun h => h.1, fun h => ⟨h, ulArgsT_mono hBA _ (ul_args_psi hs hownB γ hγ hγB)⟩⟩

/-- **At `s = 0` and `B = Ω_ω` the test is `Ui.ui_code_th`** (the code test below `θ = ψ_{Ω₂}(Ω_ω)`). -/
theorem ul_zero_th {A q z : Ordinal.{0}} (hz : z ∈ ⋃ a, S.CSet a 0) (hzθ : z < ConjT.th S) (hA : Om ω ≤ A)
    (hq1 : q ≤ Om 1) (hcl : ∀ y ∈ S.CSet A q, y < Om 1 → y < q) (hq0 : 0 < q) :
    z ∈ S.CSet A q ↔ Ui.uiDat S z < q := by
  have e1 : (0 : Ordinal.{0}) + 1 = 1 := zero_add 1
  have hown : Om ω ∈ S.CSet (Om ω) (S.psi (Om ω) (Om (0 + 1 + 1))) := by rw [e1]; exact Ui.ui_OmW_own
  have hzθ' : z < S.psi (Om ω) (Om (0 + 1 + 1)) := by rw [e1]; exact hzθ
  have hqL : q ≤ S.Lam := hq1.trans (S.Om_lt_Lam S.one_lt_Lam).le
  have h := ul_code_psi (S := S) (s := 0) omega0_pos hown hz hzθ' hA (by rw [e1]; exact hq1) hqL
    (by rw [e1]; exact hcl) hq0
  rw [h, e1, ul_one_ulDat]

end Googology.Trans.PoR.InaccPsi.R2.Ul
