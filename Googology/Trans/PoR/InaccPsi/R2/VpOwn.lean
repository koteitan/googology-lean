import Googology.Trans.PoR.InaccPsi.R2.VpHt

/-!
# `Vp.VpHt` is a theorem: the atom move at `Ω₂` on `[B₂, θ)` with no hypothesis; the road with (a) only

`W = Ω₂`, `V = Ω₃`, `ψ_π = S.psi · π`, `ulDatT S κ t` / `ulArgsT S κ A t` the leaves of `t` below `κ` and the
collapse arguments of its subterms `≥ κ` (`R2.UlCode`), `m(γ) = ulDat S Ω₂ γ`.  An own-for-`ψ_V` ordinal `K` has its
collapse arguments below `K` also at the threshold `W` (`vp_args_WV`: a subterm `ψ_V(a)` in `[W, V)` is a leaf at `V`
below `ψ_V(K)`, so `a < K`, and `a` is own for `ψ_V`); its leaves below `W` are below `ψ_W(K)` as soon as `γ` is
visible at `ψ_W(K)` (`Vp.vp_gap_K` and `Uo.uoArg`), and then `K` is own for `ψ_W` (`Ul.ul_code_mem`):

* `vp_args_small`, `vp_args_mono`, `vp_code_V` (**the code test at `V` of an own-for-`ψ_V` normal form**),
  `vp_args_WV` (**`ulDatT V t < ψ_V(A)` and `ulArgsT V A t` give `ulArgsT W A t`** for a normal form `t`);
* `vpHt` (**`Vp.VpHt S`, no hypothesis**);
* `vmAtomMove` (**`Vm.VmAtomMove S`, no hypothesis: `B_n γ < Ω₃` and `B_n(Hˡ_γ(y)) = Hˡ_{B_n γ}(B_n y)` for every
  atom `B₂ ≤ Hˡ_γ(y) < θ` in `K_{c_{n+1}}`**), `vpRoadA` (**the road of `Vm.vmRoad` with (a) `Vm.VmPiLev S` as the
  only hypothesis on `[B₂, θ)`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul

variable {S : InaccSeq.{0}}

theorem vp_args_small {κ A : Ordinal.{0}} (t : Term) (h : val S t < κ) : ulArgsT S κ A t := by
  cases t with
  | zero => trivial
  | inacc _ => trivial
  | inaccW => trivial
  | add a b => exact Or.inl h
  | phi a b => exact Or.inl h
  | om a => exact Or.inl h
  | psiS σ a => exact Or.inl h
  | psiI m a => exact Or.inl h

theorem vp_args_mono {κ A A' : Ordinal.{0}} (hA : A ≤ A') : ∀ t : Term, ulArgsT S κ A t → ulArgsT S κ A' t := by
  intro t
  induction t with
  | zero => intro _; trivial
  | inacc _ => intro _; trivial
  | inaccW => intro _; trivial
  | add a b iha ihb =>
    intro h
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨iha h1, ihb h2⟩
  | phi a b iha ihb =>
    intro h
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨iha h1, ihb h2⟩
  | om a iha =>
    intro h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (iha h)
  | psiS σ a ihs iha =>
    intro h
    rcases h with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1.trans_le hA, ihs h2, iha h3⟩
  | psiI m a iha =>
    intro h
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1.trans_le hA, iha h2⟩

/-- **The code test at `V` of an own-for-`ψ_V` normal form**: `ulDatT V t < ψ_V(|t|)` and `ulArgsT V |t| t`. -/
theorem vp_code_V {t : Term} (hN : NF t)
    (hown : val S t ∈ S.CSet (val S t) (S.psi (val S t) (Om (1 + 1 + 1)))) :
    ulDatT S (Om (1 + 1 + 1)) t < S.psi (val S t) (Om (1 + 1 + 1)) ∧
      ulArgsT S (Om (1 + 1 + 1)) (val S t) t := by
  have hκV : S.InR (Om (1 + 1 + 1)) := InR_Om_succ (1 + 1)
  have hq1 : S.psi (val S t) (Om (1 + 1 + 1)) ≤ Om (1 + 1 + 1) := (Ui.ui_psi_lt (s := 1 + 1) _).le
  exact ul_code_dat hq1 (Us.us_qΛ (i := 1 + 1) (Ui.ui_s1_lt_omega vp_hs1) hq1)
    (fun y hy hyV => lt_psi_of_mem hκV hy hyV) (Ui.ui_psi_SC (s := 1 + 1) _).1 t hN hown

theorem vp_two_lt_W : (1 + 1 : Ordinal.{0}) < Om (1 + 1) :=
  (Ui.ui_s1_lt_omega vp_hs1).trans_le (vp_omega_le_Om1.trans vp_Om1_le_W)

/-- **The collapse arguments at `W` from those at `V`**: for a normal form `t` with `ulDatT V t < ψ_V(A)` and
`ulArgsT V A t`, `ulArgsT W A t`. -/
theorem vp_args_WV : ∀ t : Term, NF t → ∀ A : Ordinal.{0},
    ulDatT S (Om (1 + 1 + 1)) t < S.psi A (Om (1 + 1 + 1)) → ulArgsT S (Om (1 + 1 + 1)) A t →
      ulArgsT S (Om (1 + 1)) A t := by
  have hκV : S.InR (Om (1 + 1 + 1)) := InR_Om_succ (1 + 1)
  intro t
  induction t with
  | zero => intro _ _ _ _; trivial
  | inacc n => intro _ _ _ _; trivial
  | inaccW => intro _ _ _ _; trivial
  | add a b iha ihb =>
    intro hN A hd ha
    simp only [ulArgsT]
    by_cases hW : val S (add a b) < Om (1 + 1)
    · exact Or.inl hW
    refine Or.inr ?_
    have hle_a : val S a ≤ val S (add a b) := by show val S a ≤ val S a + val S b; exact le_self_add
    have hle_b : val S b ≤ val S (add a b) := by show val S b ≤ val S a + val S b; exact le_add_self
    by_cases hV : val S (add a b) < Om (1 + 1 + 1)
    · rw [ulDatT_small hV] at hd
      have hsa : val S a < Om (1 + 1 + 1) := hle_a.trans_lt hV
      have hsb : val S b < Om (1 + 1 + 1) := hle_b.trans_lt hV
      exact ⟨iha hN.1 A (by rw [ulDatT_small hsa]; exact hle_a.trans_lt hd) (vp_args_small _ hsa),
        ihb hN.2.1 A (by rw [ulDatT_small hsb]; exact hle_b.trans_lt hd) (vp_args_small _ hsb)⟩
    · simp only [ulDatT, if_neg hV] at hd
      simp only [ulArgsT] at ha
      have ha' := ha.resolve_left hV
      exact ⟨iha hN.1 A ((le_max_left _ _).trans_lt hd) ha'.1, ihb hN.2.1 A ((le_max_right _ _).trans_lt hd) ha'.2⟩
  | phi a b iha ihb =>
    intro hN A hd ha
    simp only [ulArgsT]
    by_cases hW : val S (phi a b) < Om (1 + 1)
    · exact Or.inl hW
    refine Or.inr ?_
    have hN' := hN
    obtain ⟨hNa, hNb, hca, hcb⟩ := hN
    have hle_a : val S a ≤ val S (phi a b) := by
      have e := Term.cmp_eq_compare S hNa hN'
      rw [e] at hca; exact (compare_lt_iff_lt.1 hca).le
    have hle_b : val S b ≤ val S (phi a b) := by
      have e := Term.cmp_eq_compare S hNb hN'
      rw [e] at hcb; exact (compare_lt_iff_lt.1 hcb).le
    by_cases hV : val S (phi a b) < Om (1 + 1 + 1)
    · rw [ulDatT_small hV] at hd
      have hsa : val S a < Om (1 + 1 + 1) := hle_a.trans_lt hV
      have hsb : val S b < Om (1 + 1 + 1) := hle_b.trans_lt hV
      exact ⟨iha hNa A (by rw [ulDatT_small hsa]; exact hle_a.trans_lt hd) (vp_args_small _ hsa),
        ihb hNb A (by rw [ulDatT_small hsb]; exact hle_b.trans_lt hd) (vp_args_small _ hsb)⟩
    · simp only [ulDatT, if_neg hV] at hd
      simp only [ulArgsT] at ha
      have ha' := ha.resolve_left hV
      exact ⟨iha hNa A ((le_max_left _ _).trans_lt hd) ha'.1, ihb hNb A ((le_max_right _ _).trans_lt hd) ha'.2⟩
  | om a iha =>
    intro hN A hd ha
    simp only [ulArgsT]
    by_cases hW : val S (om a) < Om (1 + 1)
    · exact Or.inl hW
    refine Or.inr ?_
    by_cases hV : val S (om a) < Om (1 + 1 + 1)
    · have h3 : val S a < 1 + 1 + 1 := Om_lt_Om.1 hV
      exact vp_args_small _ ((Order.lt_add_one_iff.1 h3).trans_lt vp_two_lt_W)
    · simp only [ulDatT, if_neg hV] at hd
      simp only [ulArgsT] at ha
      exact iha hN.1 A hd (ha.resolve_left hV)
  | psiS σ a ihs iha =>
    intro hN A hd ha
    simp only [ulArgsT]
    by_cases hW : val S (psiS σ a) < Om (1 + 1)
    · exact Or.inl hW
    refine Or.inr ?_
    have hsem := Term.sem_of_NF (S := S) hN
    by_cases hV : val S (psiS σ a) < Om (1 + 1 + 1)
    · have hb := psiS_bounds (S := S) (val S a) (val S σ)
      have hval : val S (psiS σ a) = S.psi (val S a) (Om (val S σ + 1)) := rfl
      have hσ : val S σ = 1 + 1 := by
        have h1 : Om (1 + 1) < Om (val S σ + 1) := (not_lt.1 hW).trans_lt (hval ▸ hb.2)
        have h2 : Om (val S σ) < Om (1 + 1 + 1) := hb.1.trans (hval ▸ hV)
        exact le_antisymm (Order.lt_add_one_iff.1 (Om_lt_Om.1 h2)) (Order.lt_add_one_iff.1 (Om_lt_Om.1 h1))
      rw [ulDatT_small hV, hval, hσ] at hd
      have hlt : val S a < A := by
        by_contra hc
        push Not at hc
        exact absurd (psi_mono hκV hc).1 (not_le.2 hd)
      have hσW : val S σ < Om (1 + 1) := by rw [hσ]; exact vp_two_lt_W
      refine ⟨hlt, vp_args_small _ hσW, ?_⟩
      have hown : val S a ∈ S.CSet (val S a) (S.psi (val S a) (Om (1 + 1 + 1))) := by
        have h := hsem.2.2
        rwa [hσ] at h
      obtain ⟨hda, haa⟩ := vp_code_V hN.2.1 hown
      exact vp_args_mono hlt.le _ (iha hN.2.1 (val S a) hda haa)
    · simp only [ulDatT, if_neg hV] at hd
      simp only [ulArgsT] at ha
      obtain ⟨hlt, has, haa⟩ := ha.resolve_left hV
      exact ⟨hlt, ihs hN.1 A ((le_max_left _ _).trans_lt hd) has,
        iha hN.2.1 A ((le_max_right _ _).trans_lt hd) haa⟩
  | psiI m a iha =>
    intro hN A hd ha
    simp only [ulArgsT]
    by_cases hW : val S (psiI m a) < Om (1 + 1)
    · exact Or.inl hW
    refine Or.inr ?_
    have hfix : Om (val S (psiI m a)) = val S (psiI m a) := InaccSeq.Om_psiI _ _
    have hne : val S (psiI m a) ≠ 0 :=
      (lt_of_le_of_lt zero_le (InaccSeq.Om_one_lt_psiI (S := S) (val S a) m)).ne'
    have hV : ¬ val S (psiI m a) < Om (1 + 1 + 1) := not_lt.2 (vp_fix_ge hfix hne)
    simp only [ulDatT, if_neg hV] at hd
    simp only [ulArgsT] at ha
    obtain ⟨hlt, haa⟩ := ha.resolve_left hV
    exact ⟨hlt, iha hN.1 A hd haa⟩

/-- **`Vp.VpHt S`, no hypothesis**: an own-for-`ψ_{Ω₃}` `K` of the notation with `ψ_{Ω₃}(K) ≤ γ < ψ_{Ω₃}(K + 1)` is
own for `ψ_{Ω₂}`, or `ψ_{Ω₂}(K) ≤ m(γ)`. -/
theorem vpHt : VpHt S := by
  intro γ K hγN hKN hown hle hlt
  have hκV : S.InR (Om (1 + 1 + 1)) := InR_Om_succ (1 + 1)
  by_cases h : S.psi K (Om (1 + 1)) ≤ ulDat S (Om (1 + 1)) γ
  · exact Or.inr h
  push Not at h
  left
  have hqS : SC (S.psi K (Om (1 + 1))) := Ui.ui_psi_SC (s := 1) K
  have hq1 : Om 1 < S.psi K (Om (1 + 1)) := Ui.ui_L_lt_psi (s := 1) K
  have hqW : S.psi K (Om (1 + 1)) ≤ Om (1 + 1) := (Ui.ui_psi_lt (s := 1) K).le
  have hγq : UlK S 1 (S.psi K (Om (1 + 1))) γ := (Uo.uo_K_iff_dat vp_hs1 hqS hq1 hqW hγN).2 h
  have htq := vp_gap_K hqW hown γ hγq hle hlt
  have hqL : S.psi K (Om (1 + 1)) ≤ S.Lam := Us.us_qΛ (i := 1) vp_hs1 hqW
  have hKq : UlK S 1 (S.psi K (Om (1 + 1))) K := Uo.uoArg hqL hκV hown htq (ul_psiW_le_psiV K K)
  obtain ⟨hN, hv⟩ := Bc.bcNf_spec S hKN
  have hdat : ulDatT S (Om (1 + 1)) (Bc.bcNf S K) < S.psi K (Om (1 + 1)) :=
    Uo.uo_K_code_dat vp_hs1 hqS hq1 hqW _ hN (by rw [hv]; exact hKq)
  have hownt : val S (Bc.bcNf S K) ∈ S.CSet (val S (Bc.bcNf S K))
      (S.psi (val S (Bc.bcNf S K)) (Om (1 + 1 + 1))) := by rw [hv]; exact hown
  obtain ⟨hdV, haV⟩ := vp_code_V hN hownt
  rw [hv] at hdV haV
  have haW := vp_args_WV _ hN K hdV haV
  have hmem := ul_code_mem (S := S) (κ := Om (1 + 1)) (A := K) (q := S.psi K (Om (1 + 1))) _ hdat haW
  rwa [hv] at hmem

/-- **`Vm.VmAtomMove S`, no hypothesis**: `B_n γ < Ω₃` and `B_n(Hˡ_γ(y)) = Hˡ_{B_n γ}(B_n y)` for every atom
`B₂ ≤ Hˡ_γ(y) < θ` (`γ < Ω₃`, `y < Hˡ_γ(y)`) in `K_{c_{n+1}}`. -/
theorem vmAtomMove : Vm.VmAtomMove S := vmAtom_of_ht vpHt

/-- **The road of `Vm.vmRoad` with (a) `Vm.VmPiLev S` as the only hypothesis on `[B₂, θ)`** ((b) is
`vmAtomMove`). -/
theorem vpRoadA
    (hU : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdUpper S l)
    (hL : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S Ge.geV ≤ l → Cd.CdCapV S l)
    (hEQ : Cd.CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (hA : Vm.VmPiLev S)
    (hT : Cx.CxT S) (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) :
    Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cd.CdCL S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Vm.vmRoad hU hL hV hEQ hν hA vmAtomMove hT hcl

end Googology.Trans.PoR.InaccPsi.R2.Vp
