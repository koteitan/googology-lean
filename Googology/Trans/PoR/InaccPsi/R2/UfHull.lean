import Googology.Trans.PoR.InaccPsi.R2.UfKey

/-!
# Codes below `B₂` in the hulls `Cl(a, b)` (the hull converse) and the top atom

`ψ = ψ_{Ω₂}`, `H_λ = Uc.ucH λ`, `X = Tl.tlX`, `B₂ = Uc.ucB`, `UcCl Z` the codes over `Z`, `Tw.TwArgs S a x` (every
strongly critical `s ∈ (Ω₁, x]` has its own argument below `a`).  The ports of `Tw.tw_mem_CSet` and `Tw.tw_top` from
`X` to `B₂`; the own argument of an atom `H_λ(y) ≥ X` is the run `B + Ω₂^λ·D` of `Uf.ufRun`, built from the components
of `λ`, `D`, and the own argument of a smaller atom (`Uf.uf_first_base` for the base of the first value):

* `uf_mem_comps` (**`x < E₂` lies in `Cl(a, b)` when its components do**);
* `uf_args_of` (`TwArgs` from the atoms that are codes);
* `uf_mem_CSet` (**the hull converse**: a code `x` over a countable strongly critical `Z ≤ b` with `TwArgs S a x`
  lies in `Cl(a, b)`, and so does the own argument of `x` when `x` is an atom);
* `uf_top` (**the top atom**: for a code `μ` with `TwArgs S B μ` there is `A < B` with `TwArgs S a μ` for every
  `a > A`, and `A ∈ Cl(a, b)` for every `a > A` and every countable strongly critical `b` over which `μ` is a code).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Tl
  Googology.Trans.PoR.InaccPsi.R2.Tw

variable {S : InaccSeq.{0}}

/-- **`x < E₂` lies in `Cl(a, b)` when all its components do.** -/
theorem uf_mem_comps {a b : Ordinal.{0}} :
    ∀ x, x < ucE → (∀ c ∈ ucComps x, c ∈ S.CSet a b) → x ∈ S.CSet a b := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hxE hx
  by_cases hx2 : x < OmTwo
  · exact hx x (by rw [ucComps_small hx2]; rfl)
  have hx2' := not_lt.1 hx2
  have hc := ucComps_big hx2' hxE
  have hel := uc_log_lt hx2' hxE
  have hrl := uc_mod_lt hx2'
  have he := IH _ hel (hel.trans hxE) fun c h => hx c (by rw [hc]; exact Or.inl h)
  have hr := IH _ hrl (hrl.trans hxE) fun c h => hx c (by rw [hc]; exact Or.inr (Or.inr h))
  have hd := hx (x / OmTwo ^ log OmTwo x) (by rw [hc]; exact Or.inr (Or.inl rfl))
  have hW := Le.leMulWe_mem he hd
  rw [uc_leWe] at hW
  rw [← uc_cnf_eq x]
  exact CSet.add_mem hW hr

/-- `TwArgs` from the atoms that are codes. -/
theorem uf_args_of {Z a x : Ordinal.{0}} (hZ : Z ≤ Om1) (hx : UcCl Z x)
    (h : ∀ t e, UcCl Z t → SC t → Om1 < t → t ≤ x → e ∈ S.CSet e (S.psi e (Om (1 + 1))) →
      S.psi e (Om (1 + 1)) = t → e < a) : TwArgs S a x := by
  intro s e hS hs hsx hown hψ
  obtain ⟨t, htc, htS, hst, htx⟩ := uf_SC_code hZ x hx s hS hs hsx
  have hts : Om1 < t := hs.trans_le hst
  have htB : t < ucB := htx.trans_lt (uf_cl_lt_B hZ hx)
  obtain ⟨et, hownt, -, hψt⟩ := uc_own_of_SC (S := S) htS (by rw [← uf_Om1]; exact hts) htB
  have het := h t et htc htS hts htx hownt hψt
  refine lt_of_le_of_lt (not_lt.1 fun hlt => ?_) het
  have := (Ts.ts_own_lt_iff hownt hown).2 hlt
  rw [hψt, hψ] at this
  exact absurd hst (not_le.2 this)

/-- **The hull converse below `B₂`**: a code `x` over a countable strongly critical `Z ≤ b` whose atoms have their
own arguments below `a` lies in `Cl(a, b)`; when `x` is an atom, so does its own argument. -/
theorem uf_mem_CSet {Z a b : Ordinal.{0}} (hZS : SC Z) (hZ : Z ≤ Om1) (hZb : Z ≤ b) :
    ∀ x, UcCl Z x → TwArgs S a x → x ∈ S.CSet a b ∧
      (SC x → Om1 < x → ∀ e, e ∈ S.CSet e (S.psi e (Om (1 + 1))) → S.psi e (Om (1 + 1)) = x →
        e ∈ S.CSet a b) := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx hargs
  have hxB := uf_cl_lt_B hZ hx
  rcases lt_or_ge x tlX with hxX | hXx
  · exact tw_mem_CSet hZS hZ hZb x (uc_cl_lt_X hx hxX) hargs
  have h : Om1 < x := uc_Om1_lt_of_X hXx
  by_cases hE : ω ^ x = x
  · by_cases hI : invVeblen₁ x < x
    · obtain ⟨h1, h2⟩ := uc_cl_inv hZ x hx h hE hI
      have h2l := Tf.tf_inv2_lt hE
      have e : veblen (invVeblen₁ x) (invVeblen₂ x) = x := by rw [veblen_invVeblen₁_invVeblen₂, hE]
      refine ⟨?_, fun hSC _ => absurd hI (tl_SC_facts hSC).2⟩
      rw [← e]
      exact CSet.phi_mem (IH _ hI h1 (hargs.mono le_rfl hI.le)).1 (IH _ h2l h2 (hargs.mono le_rfl h2l.le)).1
    · -- an atom `H_λ(y)`: its own argument is the run `B + Ω₂^λ·D`
      have hSC := tl_SC_of h hI
      have hne := uc_nf_of_lt hSC h hxB
      obtain ⟨hlE, hlv, -, -, -⟩ := ucLev_spec hSC h hne
      obtain ⟨hnf, hyz⟩ := uc_nf hSC h hne
      obtain ⟨hcl, hcy⟩ := uc_cl_atom hZ x hx hSC hXx hxB
      generalize hldef : ucLev x = l at hlE hlv hnf hyz hcl hcy
      generalize hydef : ucI l x = y at hnf hyz hcy
      obtain ⟨B, c, D, hown, hBE, hdvd, hc, hcD, hD2, hval, hcc, hDc, hcase⟩ :=
        ufRun (S := S) hZS hZ hlE hcy (by rw [hnf]; exact hyz) (by rw [hnf]; exact hxB)
      have hcz : c < x := (le_self_add.trans_eq hcD).trans_lt hyz
      have hDz : D < x := (le_add_self.trans_eq hcD).trans_lt hyz
      obtain ⟨hψe, -, howne, -⟩ := ufRun_eq hlE hown hBE hdvd hc hD2 hval
      rw [hcD, hnf] at hψe
      have hlC : l ∈ S.CSet a b := uf_mem_comps l hlE fun c' hc' =>
        (IH c' ((le_ucC hc').trans_lt hlv) (hcl c' hc') (hargs.mono le_rfl ((le_ucC hc').trans hlv.le))).1
      have hDC := (IH D hDz hDc (hargs.mono le_rfl hDz.le)).1
      have hBC : B ∈ S.CSet a b := by
        rcases hcase with hc0 | ⟨hc1, hcf, -, -⟩
        · subst hc0
          rcases eq_or_ne l 0 with hl0 | hl0
          · subst hl0
            have hψ : S.psi B (Om (1 + 1)) = S.psi 0 (Om (1 + 1)) := by rw [← hc, uf_H0]
            rw [Ts.ts_own_unique hown (CSet.zero_mem _ _) hψ]; exact CSet.zero_mem _ _
          have h0B : ucH l 0 < ucB := ((uf_H_le_iff l).2 zero_le).trans_lt (by rw [hnf]; exact hxB)
          obtain ⟨K, hownK, -, hBK, -, hK⟩ := uf_first_base (S := S) (Order.one_le_iff_ne_zero.2 hl0) hlE h0B hown hc
          have hWl : OmTwo ^ l ∈ S.CSet a b := by
            have := Le.leWe_mem hlC; rwa [uc_leWe] at this
          rw [hBK]
          refine CSet.add_mem ?_ hWl
          rcases hK with ⟨hK0, -⟩ | ⟨hKm, -, hmaxK⟩
          · rw [hK0]; exact CSet.zero_mem _ _
          · -- `ψ(K)` is the largest strongly critical point `≤ ucC l`, a code below `x`
            have hmc : ucC l ∈ ucComps l := uf_ucC_mem l hlE
            have hvS : SC (S.psi K (Om (1 + 1))) := Ts.ts_psi_SC K
            have hv1 : Om1 < S.psi K (Om (1 + 1)) := by rw [uf_Om1]; exact Ts.ts_Om1_lt_psi K
            obtain ⟨t, htc, htS, hvt, htm⟩ := uf_SC_code hZ _ (hcl _ hmc) _ hvS hv1 hKm
            have htv : t = S.psi K (Om (1 + 1)) := le_antisymm (hmaxK t htS (hv1.trans_le hvt) htm) hvt
            rw [htv] at htc
            exact (IH _ (hKm.trans_lt hlv) htc (hargs.mono le_rfl (hKm.trans hlv.le))).2 hvS hv1 K hownK rfl
        · have hcSC : SC c := by rw [← hcf]; exact ucH_SC l c
          exact (IH c hcz hcc (hargs.mono le_rfl hcz.le)).2 hcSC hc1 B hown (by rw [← hc, hcf])
      have hWD : OmTwo ^ l * D ∈ S.CSet a b := by
        have := Le.leMulWe_mem hlC hDC; rwa [uc_leWe] at this
      have heC : B + OmTwo ^ l * D ∈ S.CSet a b := CSet.add_mem hBC hWD
      have hea : B + OmTwo ^ l * D < a := hargs x _ hSC h le_rfl howne hψe
      have hxC : x ∈ S.CSet a b := by
        rw [← hψe]; exact CSet.psi_mem hea (InR_Om_succ 1) (Mx.mxOm2_mem a b) heC
      refine ⟨hxC, fun _ _ e hown' hψ' => ?_⟩
      have := Ts.ts_own_unique hown' howne (by rw [hψ', hψe])
      rw [this]; exact heC
  · have hz0 : x ≠ 0 := (Rj.rj_Om1_pos.trans h).ne'
    obtain ⟨hsub, hlog⟩ := ucDec hZS hZ x hx
    set g := log ω x with hg
    obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
    have hdec : ω ^ g * k + x % ω ^ g = x := by
      have := Ordinal.div_add_mod x (ω ^ g); rwa [hk] at this
    have hwk : UcCl Z (ω ^ g * k) := UcCl.mul_nat hZS.1 (UcCl.opow hZS.1 hlog) k
    have hle : ω ^ g * k ≤ x := by
      conv_rhs => rw [← hdec]
      exact le_self_add
    have hr : UcCl Z (x % ω ^ g) := by
      have e : x - ω ^ g * k = x % ω ^ g := by
        nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
      rw [← e]; exact hsub _ hwk hle
    have hgl := Tf.tf_log_lt h hE
    have hml := Rj.rj_mod_lt hz0
    have hgC := (IH _ hgl hlog (hargs.mono le_rfl hgl.le)).1
    have hmC := (IH _ hml hr (hargs.mono le_rfl hml.le)).1
    have hwC : ω ^ g ∈ S.CSet a b := by
      have := CSet.phi_mem (CSet.zero_mem a b) hgC; rwa [veblen_zero_apply] at this
    refine ⟨?_, fun hSC _ => absurd (tl_SC_facts hSC).1 hE⟩
    rw [← hdec]
    exact CSet.add_mem (mul_nat_mem hwC k) hmC

/-- **The top atom below `B₂`**: for a code `μ` over a countable strongly critical `Z` with `TwArgs S B μ`, `0 < B`,
there is `A < B` with `TwArgs S a μ` for every `a > A`, and `A ∈ Cl(a, b)` for every `a > A` and every countable
strongly critical `b` over which `μ` is a code. -/
theorem uf_top {Z B μ : Ordinal.{0}} (hZ : Z ≤ Om1) (hμ : UcCl Z μ) (h : TwArgs S B μ) (hB : 0 < B) :
    ∃ A, A < B ∧ (∀ a, A < a → TwArgs S a μ) ∧
      (∀ a b, A < a → SC b → b ≤ Om1 → UcCl b μ → A ∈ S.CSet a b) := by
  by_cases hex : ∃ s, SC s ∧ Om1 < s ∧ s ≤ μ
  · set T : Set Ordinal.{0} := {s | SC s ∧ Om1 < s ∧ s ≤ μ} with hT
    have hne : T.Nonempty := hex
    have hbd : BddAbove T := ⟨μ, fun s hs => hs.2.2⟩
    have htS : SC (sSup T) := Rk.rk_SC_sSup (fun v hv => hv.1) hne hbd
    obtain ⟨s0, hs0⟩ := hex
    have ht1 : Om1 < sSup T := hs0.2.1.trans_le (le_csSup hbd hs0)
    have htμ : sSup T ≤ μ := csSup_le hne fun s hs => hs.2.2
    have hmax : ∀ s, SC s → Om1 < s → s ≤ μ → s ≤ sSup T := fun s h1 h2 h3 => le_csSup hbd ⟨h1, h2, h3⟩
    have htB : sSup T < ucB := htμ.trans_lt (uf_cl_lt_B hZ hμ)
    obtain ⟨A, hownA, -, hψA⟩ := uc_own_of_SC (S := S) htS (by rw [← uf_Om1]; exact ht1) htB
    have hAB : A < B := h _ A htS ht1 htμ hownA hψA
    have hargs : ∀ a, A < a → TwArgs S a μ := by
      intro a ha s e hS hs hsμ hown hψ
      refine lt_of_le_of_lt (not_lt.1 fun hlt => ?_) ha
      have := (Ts.ts_own_lt_iff hownA hown).2 hlt
      rw [hψA, hψ] at this
      exact absurd (hmax s hS hs hsμ) (not_le.2 this)
    refine ⟨A, hAB, hargs, fun a b ha hb hb1 hμb => ?_⟩
    obtain ⟨t, htc, htS', htt, htμ'⟩ := uf_SC_code hb1 μ hμb (sSup T) htS ht1 htμ
    have hteq : t = sSup T := le_antisymm (hmax t htS' (ht1.trans_le htt) htμ') htt
    rw [← hteq] at hψA htS ht1
    exact (uf_mem_CSet hb hb1 le_rfl t htc ((hargs a ha).mono le_rfl htμ')).2 htS ht1 A hownA hψA
  · push Not at hex
    refine ⟨0, hB, fun a _ s e hS hs hsμ => absurd (hex s hS hs) (not_lt.2 hsμ), fun a b _ _ _ _ =>
      CSet.zero_mem _ _⟩

end Googology.Trans.PoR.InaccPsi.R2.Uf
