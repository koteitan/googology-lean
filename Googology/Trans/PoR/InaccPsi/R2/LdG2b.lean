import Googology.Trans.PoR.InaccPsi.R2.LdG2a

/-!
# The readings and the reading moves below `G₂ = ψ_{Ω₂}(Ω₂·Ω₂)`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `H_λ = Cl(A_{η_λ}, ρ_λ)`, `ldAtR λ` its atoms below `Ω₂`, `Θ = gxTh ρ_λ (ldAtR λ)`
(`= Θ_λ` below `Ω₂`), `F^β = ψ_{Ω₂}(β + Ω₂)`, `G₂ = ψ_{Ω₂}(Ω₂·Ω₂)`, `m_λ` the code of `λ`.

* `ldG2_base` (**`Θ_λ(ψ_{Ω₂}(Ω₂·γ)) = ψ_{Ω₁}(A + 1 + Ω₁·Θ_λ(γ))`** for every code `γ < G₂` and every own `A` with
  `ψ_{Ω₁}(A) = ρ_λ`: `γ = 0` by `Ld.ldBlk_zero`, successors by the next base `Ld.ldBlk_next`, limits by the finite
  support `Ld.ldG2_supp`), `ldG2_th` (**`Θ_λ(ψ_{Ω₂}(Ω₂·γ + c)) = ψ_{Ω₁}(A + 1 + Ω₁·Θ_λ(γ) + Θ_λ(c))`** for every code
  `c < F^{Ω₂·γ}`): with `Ld.ldG2_clsAll` this is `Θ_λ` on every code below `G₂`;
* `ldMul_lt_SC`, `ldAtMove_G2` (**every atom below `G₂` moves** once the codes below it move: `B_n(Ω₂·γ) = Ω₂·B_n γ`,
  `B_n(Ω₁·Θ γ) = Ω₁·B_n(Θ γ)`), `ldThMove_G2` (**`MxThMove` at every long code `m_λ < G₂`**, no hypothesis);
* `LdThMoveS S` (a hypothesis name): the reading moves at the codes `G₂ ≤ m_λ ≤ θ·ω`; `ldThMoveR_of_S`,
  `ldThMoveS_of_R` (equivalent to `Ld.LdThMoveR`), `ldRoadS` (**the road**).

No new axiom.  New definition: the hypothesis name `LdThMoveS`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ld

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Sf
  Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}}

/-! ## The readings of the bases `Ω₂·γ` -/

theorem ldHat_own {A x : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1)))
    (hx : x < S.psi (A + 1 + Om 1 * x) (Om 1)) :
    A + 1 + Om 1 * x ∈ S.CSet (A + 1 + Om 1 * x) (S.psi (A + 1 + Om 1 * x) (Om 1)) :=
  CSet.add_mem (CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add.trans le_self_add)).2 hA)
    (CSet.one_mem _ _)) (ldMulK_small Ph.ph_SC_Om1 (CSet.Om_mem (CSet.one_mem _ _)) x hx)

/-- **`Θ_λ(ψ_{Ω₂}(Ω₂·γ)) = ψ_{Ω₁}(A + 1 + Ω₁·Θ_λ(γ))`** for every code `γ < G₂`. -/
theorem ldG2_base {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ < ldG2 S →
      gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1) * γ) (Om (1 + 1))) =
        S.psi (A + 1 + Om 1 * gxTh (upsilon l) (ldAtR S l) γ) (Om 1) := by
  have hρSC : SC (upsilon l) := hρ ▸ SC_psi Low.InR_Om_one A
  have hρ1 : upsilon l < Om 1 := hρ ▸ psi_lt Low.InR_Om_one A
  have hρ0 : 0 < upsilon l := hρSC.1
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΩ1C : ∀ a b, Om (1 : Ordinal.{0}) ∈ S.CSet a b := fun a b => CSet.Om_mem (CSet.one_mem a b)
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγ hγG
  have hγ2 : γ < Om (1 + 1) := hγG.trans ldG2_lt_Om2
  have hγH : γ ∈ cdHull S l := (ldHull_iff hl hX hγ2).2 hγ
  -- the block law below `γ`
  have hown : ∀ γ', GxCl (upsilon l) (ldAtR S l) γ' → γ' < γ →
      A + 1 + Om 1 * gxTh (upsilon l) (ldAtR S l) γ' ∈ S.CSet (A + 1 + Om 1 * gxTh (upsilon l) (ldAtR S l) γ')
        (S.psi (A + 1 + Om 1 * gxTh (upsilon l) (ldAtR S l) γ') (Om 1)) := by
    intro γ' hγ' hγ'γ
    refine ldHat_own hA ?_
    rw [← IH γ' hγ'γ hγ' (hγ'γ.trans hγG)]
    exact gxTh_lt hγ' (ldG2_gt (hγ'γ.trans hγG))
  have hblk : ∀ γ', GxCl (upsilon l) (ldAtR S l) γ' → γ' < γ →
      ∀ c, GxCl (upsilon l) (ldAtR S l) c → c < ldTop S (Om (1 + 1) * γ') →
        gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1) * γ' + c) (Om (1 + 1))) =
          S.psi (A + 1 + Om 1 * gxTh (upsilon l) (ldAtR S l) γ' + gxTh (upsilon l) (ldAtR S l) c) (Om 1) := by
    intro γ' hγ' hγ'γ
    have hγ'G := hγ'γ.trans hγG
    have hγ'H : γ' ∈ cdHull S l := (ldHull_iff hl hX (hγ'G.trans ldG2_lt_Om2)).2 hγ'
    exact ldBlk_step hl hX (ldG2_own hγ'G) (dvd_mul_right _ _) (ldG2_H hγ'H)
      (ldG2_A l (hγ'G.trans ldG2_lt_Om2)) (hown γ' hγ' hγ'γ) (IH γ' hγ'γ hγ' hγ'G)
  rcases zero_or_succ_or_isSuccLimit γ with h0 | ⟨γ', hγ'⟩ | hlim
  · subst h0
    rw [mul_zero, gxTh_zero, mul_zero, add_zero]
    exact ldBlk_zero hA hρ
  · -- the successor `γ = γ' + 1`
    rw [succ_eq_add_one] at hγ'
    subst hγ'
    have hγ'γ : γ' < γ' + 1 := lt_add_one γ'
    have hγ'G := hγ'γ.trans hγG
    have hγ'2 := hγ'G.trans ldG2_lt_Om2
    have hγ'H : γ' ∈ cdHull S l := mem_of_add_one_mem hγH
    have hγ'c : GxCl (upsilon l) (ldAtR S l) γ' := (ldHull_iff hl hX hγ'2).1 hγ'H
    have h := ldBlk_next hl hX (ldG2_own hγ'G) (dvd_mul_right _ _) (ldG2_H hγ'H) (ldG2_A l hγ'2)
      (hown γ' hγ'c hγ'γ) (IH γ' hγ'γ hγ'c hγ'G)
    rw [ldTop_mul] at h
    rw [h, gxTh_add hρSC hAt hγ'c, gxTh_small (gg_one_lt_of_SC hρSC).le, mul_add_one, add_assoc]
  · -- a limit `γ`
    have hγ0 : γ ≠ 0 := hlim.ne_bot
    have hΘ0 : 0 < gxTh (upsilon l) (ldAtR S l) γ := by
      have := gxTh_lt (Z := upsilon l) (At := ldAtR S l) (GxCl.zero hρ0) (pos_iff_ne_zero.2 hγ0)
      rwa [gxTh_zero] at this
    have hsat : S.psi (Om (1 + 1) * γ) (Om (1 + 1)) ∈ ldAtR S l :=
      ldBlk_base_atom (ldG2_H hγH) (ldG2_A l hγ2)
    set Θγ := gxTh (upsilon l) (ldAtR S l) γ with hΘγ
    have hAX : A ∈ S.CSet (A + 1 + Om 1 * Θγ) (S.psi (A + 1 + Om 1 * Θγ) (Om 1)) :=
      (psi_mono (S := S) Low.InR_Om_one (le_self_add.trans le_self_add)).2 hA
    have hρX : upsilon l < S.psi (A + 1 + Om 1 * Θγ) (Om 1) := by
      rw [← hρ]
      exact psi_lt_psi_of_mem Low.InR_Om_one ((lt_add_one A).trans_le le_self_add) hAX
    -- every atom below `ψ_{Ω₂}(Ω₂·γ)` is in a block `γ1 < γ`
    have hcls : ∀ t ∈ ldAtR S l, t < S.psi (Om (1 + 1) * γ) (Om (1 + 1)) →
        ∃ γ1, GxCl (upsilon l) (ldAtR S l) γ1 ∧ γ1 < γ ∧ ∃ c, GxCl (upsilon l) (ldAtR S l) c ∧
          c < ldTop S (Om (1 + 1) * γ1) ∧ t = S.psi (Om (1 + 1) * γ1 + c) (Om (1 + 1)) := by
      intro t ht htγ
      obtain ⟨γ'', hγ''c, hγ''γ, hcase⟩ := ldG2_cls hl hX hγG.le ht htγ
      rcases hcase with ⟨c, hc, hcF, rfl⟩ | rfl
      · exact ⟨γ'', hγ''c, hγ''γ, c, hc, hcF, rfl⟩
      · have hγ1 : γ'' + 1 < γ := hlim.succ_lt hγ''γ
        have hγ12 : γ'' + 1 < Om (1 + 1) := (hγ1.trans hγG).trans ldG2_lt_Om2
        have hγ1c : GxCl (upsilon l) (ldAtR S l) (γ'' + 1) :=
          (ldHull_iff hl hX hγ12).1 (CSet.succ_mem ((ldHull_iff hl hX ((lt_add_one _).trans hγ12)).2 hγ''c))
        refine ⟨γ'' + 1, hγ1c, hγ1, 0, GxCl.zero hρ0, (Om_pos one_ne_zero).trans (ldOm1_lt_Top _), ?_⟩
        rw [add_zero, ldTop_mul]
    apply le_antisymm
    · refine ldAtom_le hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) hρX ?_
      intro t ht htγ
      obtain ⟨γ1, hγ1c, hγ1γ, c, hc, hcF, rfl⟩ := hcls t ht htγ
      have hγ1G := hγ1γ.trans hγG
      rw [hblk γ1 hγ1c hγ1γ c hc hcF]
      have hcs : gxTh (upsilon l) (ldAtR S l) c <
          S.psi (A + 1 + Om 1 * gxTh (upsilon l) (ldAtR S l) γ1 + gxTh (upsilon l) (ldAtR S l) c) (Om 1) := by
        rw [← hblk γ1 hγ1c hγ1γ c hc hcF]
        exact gxTh_lt hc (ldTop_gt (ldG2_own hγ1G) (dvd_mul_right _ _) hcF)
      have hc1 := hcs.trans (psi_lt Low.InR_Om_one _)
      have hΘ1 : gxTh (upsilon l) (ldAtR S l) γ1 < Θγ := gxTh_lt hγ1c hγ1γ
      have harg : A + 1 + Om 1 * gxTh (upsilon l) (ldAtR S l) γ1 + gxTh (upsilon l) (ldAtR S l) c <
          A + 1 + Om 1 * Θγ := by
        rw [add_assoc (A + 1)]
        refine (add_lt_add_iff_left (A + 1)).2 ?_
        calc Om 1 * gxTh (upsilon l) (ldAtR S l) γ1 + gxTh (upsilon l) (ldAtR S l) c
            < Om 1 * gxTh (upsilon l) (ldAtR S l) γ1 + Om 1 := (add_lt_add_iff_left _).2 hc1
          _ = Om 1 * (gxTh (upsilon l) (ldAtR S l) γ1 + 1) := (mul_add_one _ _).symm
          _ ≤ Om 1 * Θγ := mul_le_mul_right (Order.add_one_le_of_lt hΘ1) _
      have hγ1X : gxTh (upsilon l) (ldAtR S l) γ1 < S.psi (A + 1 + Om 1 * Θγ) (Om 1) := by
        have h1 := gxTh_lt hγ1c (ldG2_gt hγ1G)
        rw [IH γ1 hγ1γ hγ1c hγ1G] at h1
        refine h1.trans_le (psi_mono (S := S) Low.InR_Om_one ?_).1
        exact add_le_add_right (mul_le_mul_right hΘ1.le _) _
      refine psi_lt_psi_of_mem Low.InR_Om_one harg (CSet.add_mem (CSet.add_mem (CSet.add_mem hAX
        (CSet.one_mem _ _)) (ldMulK_small Ph.ph_SC_Om1 (hΩ1C _ _) _ hγ1X)) (CSet.of_lt ?_))
      exact hcs.trans_le (psi_mono (S := S) Low.InR_Om_one harg.le).1
    · obtain ⟨hTSC, hρT, hTs⟩ := ldAtom_ge hρSC hρ1 hAt hsat
      refine ldPsi1_le hTSC fun e he hmod => ?_
      rcases le_or_gt e A with heA | heA
      · exact lt_of_le_of_lt (hρ ▸ (psi_mono (S := S) Low.InR_Om_one heA).1) hρT
      obtain ⟨r, rfl⟩ := exists_add_of_le heA.le
      have hr0 : r ≠ 0 := by rintro rfl; rw [add_zero] at heA; exact lt_irrefl _ heA
      obtain ⟨r', rfl⟩ := exists_add_of_le (Order.one_le_iff_ne_zero.2 hr0)
      rw [← add_assoc] at he hmod ⊢
      have hr'lt : r' < Om 1 * Θγ := (add_lt_add_iff_left (A + 1)).1 he
      have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
      have hx : r' / Om 1 < Θγ := (Ordinal.lt_mul_iff_div_lt hΩ0).1 hr'lt
      have hdec : r' = Om 1 * (r' / Om 1) + r' % Om 1 := (Ordinal.div_add_mod r' _).symm
      have hy : r' % Om 1 < gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1) * γ) (Om (1 + 1))) := by
        rcases lt_or_ge r' (Om 1) with h1 | h1
        · rw [ldMod_add_lt (A + 1) h1] at hmod
          rw [Ordinal.mod_eq_of_lt h1]; exact le_add_self.trans_lt hmod
        · rw [ldMod_add_ge (A + 1) h1] at hmod; exact hmod
      obtain ⟨γ', hγ'c, hγ'γ, hγ'x⟩ := gxTh_onto hx
      obtain ⟨c, hc, hcγ, hcy⟩ := gxTh_onto hy
      obtain ⟨γs, hγs, hγ'γs, hγsγ, hcF⟩ := ldG2_supp hl hX hγG.le hlim c hc hcγ γ' hγ'c hγ'γ
      have hγsG := hγsγ.trans hγG
      have hγsH : γs ∈ cdHull S l := (ldHull_iff hl hX (hγsG.trans ldG2_lt_Om2)).2 hγs
      have htat := ldBlk_atom hl hX (ldG2_H hγsH) (ldG2_A l (hγsG.trans ldG2_lt_Om2)) hc hcF
      have htγ : S.psi (Om (1 + 1) * γs + c) (Om (1 + 1)) < S.psi (Om (1 + 1) * γ) (Om (1 + 1)) := by
        refine (ldTop_lt (ldG2_own hγsG) hcF).trans_le ?_
        rw [ldTop_mul]
        exact (psi_mono (S := S) (InR_Om_succ 1) (ldOm2_mul_mono (Order.add_one_le_of_lt hγsγ))).1
      have h1 := hTs _ htat htγ
      rw [hblk γs hγs hγsγ c hc hcF, hcy] at h1
      refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one ?_).1 h1
      rw [add_assoc (A + 1)]
      refine add_le_add_right ?_ _
      conv_lhs => rw [hdec]
      refine add_le_add (mul_le_mul_right ?_ _) le_rfl
      rw [← hγ'x]
      exact gxTh_mono hγ'γs

/-- **`Θ_λ(ψ_{Ω₂}(Ω₂·γ + c)) = ψ_{Ω₁}(A + 1 + Ω₁·Θ_λ(γ) + Θ_λ(c))`** for codes `γ < G₂`, `c < F^{Ω₂·γ}`. -/
theorem ldG2_th {l ηx A γ c : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    (hγ : GxCl (upsilon l) (ldAtR S l) γ) (hγG : γ < ldG2 S)
    (hc : GxCl (upsilon l) (ldAtR S l) c) (hcF : c < ldTop S (Om (1 + 1) * γ)) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1) * γ + c) (Om (1 + 1))) =
      S.psi (A + 1 + Om 1 * gxTh (upsilon l) (ldAtR S l) γ + gxTh (upsilon l) (ldAtR S l) c) (Om 1) := by
  have hbase := ldG2_base hl hX hA hρ γ hγ hγG
  have hγH : γ ∈ cdHull S l := (ldHull_iff hl hX (hγG.trans ldG2_lt_Om2)).2 hγ
  have hown := ldHat_own hA (x := gxTh (upsilon l) (ldAtR S l) γ) (by
    rw [← hbase]; exact gxTh_lt hγ (ldG2_gt hγG))
  exact ldBlk_step hl hX (ldG2_own hγG) (dvd_mul_right _ _) (ldG2_H hγH) (ldG2_A l (hγG.trans ldG2_lt_Om2))
    hown hbase c hc hcF

/-! ## The moves below `G₂` -/

/-- A strongly critical `T` is closed under multiplication. -/
theorem ldMul_lt_SC {T a b : Ordinal.{0}} (hT : SC T) (ha : a < T) (hb : b < T) : a * b < T := by
  have h1 : a * b ≤ ω ^ a * ω ^ b := mul_le_mul' (right_le_opow a one_lt_omega0) (right_le_opow b one_lt_omega0)
  rw [← opow_add] at h1
  exact h1.trans_lt (ldOpow_lt_SC hT (hT.isPrincipal ha hb))

theorem ldB_G2 {n : ℕ} : MvD S (ldG2 S) ∧ Bc.bcB S n (ldG2 S) = ldG2 S := by
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hD2 hD2
  have hne : ω ^ (Om (1 + 1 : Ordinal.{0}) + Om (1 + 1)) ≠ Om (1 + 1) + Om (1 + 1) := by
    intro h
    have h1 : Om (1 + 1 : Ordinal.{0}) + Om (1 + 1) < Om (1 + 1) * ω := by
      have e2 : Om (1 + 1 : Ordinal.{0}) + Om (1 + 1) = Om (1 + 1) * 2 := by
        rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one]
      rw [e2]; exact (mul_lt_mul_iff_right₀ ldOm2_SC.1).2 (by exact_mod_cast natCast_lt_omega0 2)
    have h2 : Om (1 + 1 : Ordinal.{0}) * ω ≤ ω ^ (Om (1 + 1) + Om (1 + 1)) := by
      rw [ldW2_eq]; exact opow_le_opow_right omega0_pos (add_le_add_right (Order.one_le_iff_ne_zero.2
        ldOm2_SC.1.ne') _)
    rw [h] at h2
    exact absurd h1 (not_lt.2 h2)
  obtain ⟨hDo, hBo⟩ := mvB_opow (k := n) hDs hne
  rw [hBs, hB2, ← ldOm2sq_eq] at hBo
  rw [← ldOm2sq_eq] at hDo
  obtain ⟨hDG, hBG⟩ := mxB_atom (n := n) hDo (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) (mxOm2_mem (S := S) _ _))
  exact ⟨hDG, by unfold ldG2; rw [hBG, hBo]⟩

/-- **Every atom below `G₂` moves** once the codes below it move. -/
theorem ldAtMove_G2 {n : ℕ} {l l' A A' ηx ηx' : Ordinal.{0}} (hl : IsRestartIdx l) (hl' : IsRestartIdx l')
    (hX : upsilon l < Pv S ηx) (hX' : upsilon l' < Pv S ηx')
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1)))
    (hρ : S.psi A (Om 1) = upsilon l) (hρ' : S.psi A' (Om 1) = upsilon l')
    (hbX : ∀ d, d ≤ ConjT.th S → S.psi (A + d) (Om 1) < Bc.bcC S (n + 1))
    (hBψ : ∀ d, MvD S d → A + d ∈ S.CSet (A + d) (S.psi (A + d) (Om 1)) → d ≤ ConjT.th S →
      Bc.bcB S n (S.psi (A + d) (Om 1)) = S.psi (A' + Bc.bcB S n d) (Om 1)) :
    ∀ s ∈ ldAtR S l, s < ldG2 S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ldG2 S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ldG2 S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hθ1 : Om (1 : Ordinal.{0}) < ConjT.th S := (psiS_bounds (S := S) _ 1).1
  have hθSC : SC (ConjT.th S) := SC_psi (InR_Om_succ 1) _
  have hρSC : SC (upsilon l) := hρ ▸ SC_psi Low.InR_Om_one A
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  intro s hs hsG IHx
  obtain ⟨γ, hγc, hγG, c, hc, hcF, rfl⟩ := ldG2_clsAll hl hX hs hsG
  have hγ2 : γ < Om (1 + 1) := hγG.trans ldG2_lt_Om2
  have hcs : c < S.psi (Om (1 + 1) * γ + c) (Om (1 + 1)) := ldTop_gt (ldG2_own hγG) (dvd_mul_right _ _) hcF
  have hγs : γ < S.psi (Om (1 + 1) * γ + c) (Om (1 + 1)) :=
    (ldG2_gt hγG).trans_le (psi_mono (S := S) (InR_Om_succ 1) le_self_add).1
  obtain ⟨hDγ, hBγc, hBγG, hΘγX, hΘγ⟩ := IHx γ hγc hγs
  obtain ⟨hDc, hBc, -, hΘcX, hΘc⟩ := IHx c hc hcs
  -- `B_n(Ω₂·γ) = Ω₂·B_n γ`
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDβ, hBβ⟩ := ldB_mulK (n := n) ldOm2_SC hD2 hB2
    (fun x => GxCl (upsilon l) (ldAtR S l) x ∧ x < S.psi (Om (1 + 1) * γ + c) (Om (1 + 1)) ∧ x < Om (1 + 1))
    (fun x hx => (IHx x hx.1 hx.2.1).1)
    (fun x hx hx0 => by
      obtain ⟨hsub, hlog⟩ := gxDec hρSC hAt x hx.1
      have hlx : log ω x ≤ x := log_le_self ω x
      have hle : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
      exact ⟨⟨hlog, hlx.trans_lt hx.2.1, hlx.trans_lt hx.2.2⟩,
        ⟨hsub _ (GxCl.opow hρSC.1 hlog) hle, (Ordinal.sub_le_self _ _).trans_lt hx.2.1,
          (Ordinal.sub_le_self _ _).trans_lt hx.2.2⟩⟩)
    (fun x hx => hx.2.2) γ ⟨hγc, hγs, hγ2⟩
  obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hDβ hDc
  obtain ⟨hDs, hBs⟩ := mxB_atom (n := n) hDa (ldOwn (ldG2_own hγG) (dvd_mul_right _ _) hcF)
  -- `B_n(F^{Ω₂·γ}) = F^{Ω₂·B_n γ}`
  obtain ⟨hDβ2, hBβ2⟩ := mvB_add (k := n) hDβ hD2
  obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hDβ2
    (CSet.add_mem (ldG2_own hγG _ le_rfl) (mxOm2_mem _ _))
  have hBγ2 : Bc.bcB S n γ < Om (1 + 1) := hBγG.trans ldG2_lt_Om2
  have hBγH : Bc.bcB S n γ ∈ cdHull S l' := (ldHull_iff hl' hX' hBγ2).2 hBγc
  have hBcF : Bc.bcB S n c < ldTop S (Om (1 + 1) * Bc.bcB S n γ) := by
    have h := (mvB_lt_iff (k := n) hDc hDT).2 hcF
    unfold ldTop at h ⊢
    rwa [hBT, hBβ2, hBβ, hB2] at h
  -- the reading of `s`
  have hth := ldG2_th hl hX hA hρ hγc hγG hc hcF
  set γ' := gxTh (upsilon l) (ldAtR S l) γ with hγ'
  set δ := gxTh (upsilon l) (ldAtR S l) c with hδ
  set d := 1 + Om 1 * γ' + δ with hd
  have hAd : A + 1 + Om 1 * γ' + δ = A + d := by rw [hd, add_assoc, add_assoc, add_assoc]
  rw [hAd] at hth
  have hδs : δ < S.psi (A + d) (Om 1) := by rw [← hth]; exact gxTh_lt hc hcs
  have hγ's : γ' < S.psi (A + d) (Om 1) := by rw [← hth]; exact gxTh_lt hγc hγs
  have hδ1 : δ < Om 1 := hδs.trans (psi_lt Low.InR_Om_one _)
  have hγ'1 : γ' < Om 1 := hγ's.trans (psi_lt Low.InR_Om_one _)
  have hdθ : d ≤ ConjT.th S :=
    (hθSC.isPrincipal (hθSC.isPrincipal (one_lt_Om1.trans hθ1) (ldMul_lt_SC hθSC hθ1 (hγ'1.trans hθ1)))
      (hδ1.trans hθ1)).le
  have hownd : A + d ∈ S.CSet (A + d) (S.psi (A + d) (Om 1)) := by
    rw [← hAd]
    refine CSet.add_mem (CSet.add_mem (CSet.add_mem ?_ (CSet.one_mem _ _))
      (ldMulK_small Ph.ph_SC_Om1 (CSet.Om_mem (CSet.one_mem _ _)) _ (hAd ▸ hγ's))) (CSet.of_lt (hAd ▸ hδs))
    exact (psi_mono (S := S) Low.InR_Om_one (le_self_add.trans (le_self_add.trans le_self_add))).2 hA
  -- `B_n d`
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hDΩ, hBΩ⟩ := mvB_Om1 (S := S) (k := n)
  obtain ⟨hDΩγ, hBΩγ⟩ := ldB_mulK (n := n) Ph.ph_SC_Om1 hDΩ hBΩ
    (fun x => x < Om 1 ∧ x < Bc.bcC S (n + 1)) (fun x hx => mvD_of_lt (hx.2.trans hLw))
    (fun x hx _ => ⟨⟨(log_le_self ω x).trans_lt hx.1, (log_le_self ω x).trans_lt hx.2⟩,
      ⟨(Ordinal.sub_le_self _ _).trans_lt hx.1, (Ordinal.sub_le_self _ _).trans_lt hx.2⟩⟩)
    (fun x hx => hx.1) γ' ⟨hγ'1, hΘγX⟩
  obtain ⟨hD1Ω, hB1Ω⟩ := mvB_add (k := n) hD1 hDΩγ
  have hDδ : MvD S δ := mvD_of_lt (hΘcX.trans hLw)
  obtain ⟨hDd, hBd⟩ := mvB_add (k := n) hD1Ω hDδ
  have hBβ' : Bc.bcB S n (Om (1 + 1) * γ) = Om (1 + 1) * Bc.bcB S n γ := hBβ
  refine ⟨hDs, ?_, ?_, ?_, ?_⟩
  · rw [hBs, hBa, hBβ']
    exact ldBlk_atom hl' hX' (ldG2_H hBγH) (ldG2_A l' hBγ2) hBc hBcF
  · rw [hBs, hBa, hBβ']
    refine (ldTop_lt (ldG2_own hBγG) hBcF).trans ?_
    rw [ldTop_mul]
    have h1 : Bc.bcB S n γ + 1 < ldG2 S := ldG2_SC.isSuccLimit.succ_lt hBγG
    exact psi_lt_psi_of_mem (InR_Om_succ 1) (ldOm2_mul_lt (h1.trans ldG2_lt_Om2))
      (ldMulK_small ldOm2_SC (mxOm2_mem _ _) _ h1)
  · rw [hth]; exact hbX d hdθ
  · rw [hBs, hBa, hBβ', ldG2_th hl' hX' hA' hρ' hBγc hBγG hBc hBcF, hΘγ, hΘc, hth, hBψ d hDd hownd hdθ, hd,
      hBd, hB1Ω, mwB_one, hBΩγ]
    simp only [add_assoc]

/-- **`MxThMove` at every long code `m_λ < G₂`.** -/
theorem ldThMove_G2 {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    (he : ggGam < cdExp (cdEta S l)) (hK : cdCode S l < ldG2 S) :
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l') := by
  have hl := hR.1
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hX : upsilon l < Nm.Pv S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0})) := by
    rw [← Lw.lw_L_eq S]; exact h2
  have hX' : upsilon l' < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S, ← hB]; exact Bc.bcB_bound' S n _ h2
  obtain ⟨hg, -, -, hpv⟩ := cdEta_pv_spec (S := S) hl.1 hX
  set η := cdEta S l with hη_def
  set A := ConjT.Aη S η with hA_def
  have hρA : S.psi A (Om 1) = upsilon l := hpv
  have hAL : A < S.Lam := (sfA_lt (S := S) (n := n) (hpv ▸ h2)).2
  have hown : A ∈ S.CSet A (S.psi A (Om 1)) := sfOwn hg hAL
  set e := cdExp η with he_def
  have hωe : (ω : Ordinal.{0}) ≤ e := (Lw.lw_omega_lt_SC ggGam_spec.1).le.trans he.le
  have hWA : Om ω ≤ A := le_self_add
  have he2 : e < Om (1 + 1) := by
    by_contra h
    have hc : cdCode S l = cdPi S η := by
      show cdCodeOf S η = _; unfold cdCodeOf; rw [if_neg h]
    have hle : ldG2 S ≤ cdPi S η := (psi_mono (S := S) (InR_Om_succ 1) (ldOm2sq_lt_OmW.le.trans hWA)).1
    exact absurd (hc ▸ hK) (not_lt.2 hle)
  have hcode : cdCode S l = e := by
    show cdCodeOf S η = e
    rw [cdCodeOf_of_lt he2]; unfold cdOff; rw [if_neg (not_lt.2 hωe)]
  have heF : e < ldG2 S := hcode ▸ hK
  have hH := ggExp_HCl (Nn.nnGood_HCl hg)
  have hmemH : e ∈ cdHull S l := by unfold cdHull; rw [← hpv]; exact hH.mem_CSet
  have hge : GxCl (upsilon l) (ldAtR S l) e := (ldHull_iff hl hX he2).1 hmemH
  have hmem0 : e ∈ ⋃ a, S.CSet a 0 := by
    refine Set.mem_iUnion.2 ⟨A, mxHull_sub0 ?_⟩
    have : e ∈ S.CSet A (upsilon l) := hmemH
    rwa [← hρA] at this
  obtain ⟨η', -, hBη', hη', hexp'⟩ := mvExp_move hl.1 h1 h2 (heF.trans ldG2_lt_th) hmem0
  have hl'eq : l' = Bt.iota S η' := Tp.tpUps_inj (hB.symm.trans hBη')
  have hu1 : upsilon (l + 1) < cdDelta l :=
    upsilon_normal.strictMono (by
      calc l + 1 < l + ω := (add_lt_add_iff_left l).2 one_lt_omega0
        _ < l + ω + 1 := lt_add_one _)
  have hsucc := mxUps_succ hl hX
  have hbX : ∀ d, d ≤ ConjT.th S → S.psi (A + d) (Om 1) < Bc.bcC S (n + 1) := by
    intro d hd
    have h3 : S.psi (A + d) (Om 1) ≤ upsilon (l + 1) := by
      rw [hsucc]; exact (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left A).2 hd)).1
    exact (h3.trans_lt hu1).trans hδr
  have hρ0 : (0 : Ordinal.{0}) < Pv S η := hpv ▸ mvUps_pos hl
  obtain ⟨A', hA', hBP, -⟩ := mxB_psi_add (n := n) hg (hpv ▸ h1.le) (by rw [add_zero]; exact hρ0)
    (by rw [add_zero]; show Pv S η < Bc.bcC S (n + 1); rw [hpv]; exact h2)
  have hρA' : S.psi A' (Om 1) = upsilon l' := by rw [← hBP, hpv, hB]
  have hBψ : ∀ d, MvD S d → A + d ∈ S.CSet (A + d) (S.psi (A + d) (Om 1)) → d ≤ ConjT.th S →
      Bc.bcB S n (S.psi (A + d) (Om 1)) = S.psi (A' + Bc.bcB S n d) (Om 1) := by
    intro d hDd hownd hdθ
    obtain ⟨A'', hA'', hBP'', hBd⟩ := ldB_psi_add (n := n) hg (hpv ▸ h1.le) hDd hownd (hbX d hdθ)
    have : A'' = A' := mxPsi_inj hA'' hA' (by rw [← hBP'', hBP])
    rw [hBd, this]
  have hρSC : SC (upsilon l) := hρA ▸ SC_psi Low.InR_Om_one A
  have hρ1 : upsilon l < Om 1 := hρA ▸ psi_lt Low.InR_Om_one A
  have hρ'SC : SC (upsilon l') := hρA' ▸ SC_psi Low.InR_Om_one A'
  have hρ'1 : upsilon l' < Om 1 := hρA' ▸ psi_lt Low.InR_Om_one A'
  obtain ⟨hDe, -, hBeF, -, hEq⟩ := ldGxStepRec (n := n) hρSC hρ1 hρ'SC hρ'1 (ldAt_GxAt _ _)
    (ldAt_GxAt _ _) hB (Lw.lw_L_SC S _) h2 hLw ldG2_SC ldOm1_lt_G2.le
    (ldAtMove_G2 hl hl' hX hX' hown hA' hρA hρA' hbX hBψ) e hge heF
  have hΩe : Om (1 : Ordinal.{0}) < Bc.bcB S n e := by
    obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
    have h3 := (mvB_lt_iff (k := n) hDO hDe).2 (ggGam_spec.2.trans he)
    rwa [hBO] at h3
  have hωBe : (ω : Ordinal.{0}) ≤ Bc.bcB S n e := (Lw.lw_omega_lt_SC Ph.ph_SC_Om1).le.trans hΩe.le
  have hcode' : cdCode S l' = Bc.bcB S n e := by
    rw [hl'eq]
    show cdCodeOf S (cdEta S (Bt.iota S η')) = _
    rw [hη', cdCodeOf_of_lt (hexp' ▸ hBeF.trans ldG2_lt_Om2), hexp']
    unfold cdOff; rw [if_neg (not_lt.2 hωBe)]
  rw [hcode, hcode', ldTheta hl hX he2.le, ldTheta hl' hX' (hBeF.trans ldG2_lt_Om2).le]
  exact hEq.symm

/-! ## The remaining reading moves and the road -/

/-- **The reading moves at the codes `G₂ ≤ m_λ ≤ θ·ω`.** -/
def LdThMoveS (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    ldG2 S ≤ cdCode S l → cdCode S l ≤ ConjT.th S * ω →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l')

theorem ldFw_le_G2 : ldFw S ≤ ldG2 S :=
  (psi_mono (S := S) (InR_Om_succ 1) (ldOm2_mul_mono (omega0_lt_Om (by
    rw [one_add_one_eq_two]; exact two_ne_zero)).le)).1

/-- **`LdThMoveS` gives `LdThMoveR`.** -/
theorem ldThMoveR_of_S (h : LdThMoveS S) : LdThMoveR S := by
  intro n l l' hR h1 hr hl' hB hm hF hw
  by_cases hK : cdCode S l < ldG2 S
  · exact ldThMove_G2 hR h1 hr hl' hB (ldGam_lt_Fw.trans_le (hF.trans (cdCodeOf_le_exp S _))) hK
  · exact h n l l' hR h1 hr hl' hB hm (not_lt.1 hK) hw

/-- `LdThMoveR` gives `LdThMoveS` (so `LdThMoveS` is not the stronger hypothesis). -/
theorem ldThMoveS_of_R (h : LdThMoveR S) : LdThMoveS S :=
  fun n l l' hR h1 hr hl' hB hm hG hw => h n l l' hR h1 hr hl' hB hm (ldFw_le_G2.trans hG) hw

/-- **The road with `MxLhTopG`, `L(ω+1) ≤ ν_C → LdThMoveS` and `L(ω+1) ≤ ν_C → LdEQhi`.** -/
theorem ldRoadS (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hth : Nc.ncL S (ω + 1) ≤ nuC → LdThMoveS S)
    (hhi : Nc.ncL S (ω + 1) ≤ nuC → LdEQhi S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  ldRoadR hU hO hL hV hN hlh (fun hν => ldThMoveR_of_S (hth hν)) hhi

end Googology.Trans.PoR.InaccPsi.R2.Ld
