import Googology.Trans.PoR.InaccPsi.R2.LeLay

/-!
# The block law at every level `k`: `Θ_λ(ψ_{Ω₂}(β + c)) = ψ_{Ω₁}(Â + h_k(c))`, and the readings below `ψ_{Ω₂}(Ω₂^ω)`

`H_λ = Cl(A_{η_λ}, ρ_λ)`, `ldAtR λ` its atoms below `Ω₂`, `Θ = gxTh ρ_λ (ldAtR λ)` (`= Θ_λ` below `Ω₂`, `Ld.ldTheta`),
`W^k = Ω₂^k`, `Ω^k = Ω₁^k`, `T_k(β) = ψ_{Ω₂}(β + W^{k+1})`, `F_{ω²} = ψ_{Ω₂}(Ω₂^ω)` (`leFw`).

The own arguments of a block of level `k` (`LeOwn S λ k β c`): for `k = 0` the codes `c < ldTop β` (`Ld.ldBlk_step`);
for `k + 1` the ordinals `c = W^{k+1}·γ + c'` with a code `γ < T_{k+1}(β)` and `c'` own in the block of level `k`
of `β + W^{k+1}·γ`.  Their level-1 image (`leH S λ k c`): `h_0(c) = Θ(c)`,
`h_{k+1}(W^{k+1}·γ + c') = Ω^{k+1}·Θ(γ) + h_k(c')` (the base-`Ω₂` digits read at base `Ω₁`).

* `leBlk` (**THE BLOCK LAW AT LEVEL `k`**: for a base `β` of level `k` with `Θ(ψ_{Ω₂}(β)) = ψ_{Ω₁}(Â)`, `Â` own,
  `Θ(ψ_{Ω₂}(β + c)) = ψ_{Ω₁}(Â + h_k(c))` for every own `c`, and `Θ(T_k(β)) = ψ_{Ω₁}(Â + Ω^{k+1})`), by induction on `k`
  from `Ld.ldBlk_step` / `Ld.ldBlk_next`: the sub-bases `β + W^{k+1}·γ` by induction on the code `γ` (limits by the
  sub-bases alone, no support lemma), the top by the digit bound `Le.lePsi1_le` / `Le.leCl_bound`;
* `leCls` (**every atom of a block of level `k` is `≤ ψ_{Ω₂}(β)` or `ψ_{Ω₂}(β + c)` with `c` own**);
* `leTh_Fw` (**every atom `t < F_{ω²}` is `ψ_{Ω₂}(c)` with `c` own at a level `k`, and
  `Θ_λ(t) = ψ_{Ω₁}(A + 1 + h_k(c))`**, `A` own with `ψ_{Ω₁}(A) = ρ_λ`).

No new axiom.  New definitions: `LeOwn`, `leH`, `leFw`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Le

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

/-- **The own arguments of a block of level `k`.** -/
def LeOwn (S : InaccSeq.{0}) (l : Ordinal.{0}) : ℕ → Ordinal.{0} → Ordinal.{0} → Prop
  | 0, β, c => GxCl (upsilon l) (ldAtR S l) c ∧ c < ldTop S β
  | k + 1, β, c => ∃ γ c', c = leW (k + 1) * γ + c' ∧ GxCl (upsilon l) (ldAtR S l) γ ∧
      γ < leT S (k + 1) β ∧ LeOwn S l k (β + leW (k + 1) * γ) c'

/-- **The level-1 image** `h_k(c)` of an argument `c < W^{k+1}`. -/
noncomputable def leH (S : InaccSeq.{0}) (l : Ordinal.{0}) : ℕ → Ordinal.{0} → Ordinal.{0}
  | 0, c => gxTh (upsilon l) (ldAtR S l) c
  | k + 1, c => leO (k + 1) * gxTh (upsilon l) (ldAtR S l) (c / leW (k + 1)) + leH S l k (c % leW (k + 1))

/-- `F_{ω²} = ψ_{Ω₂}(Ω₂^ω)`. -/
noncomputable def leFw (S : InaccSeq.{0}) : Ordinal.{0} := S.psi (ω ^ (Om (1 + 1) * ω)) (Om (1 + 1))

theorem leH_zero (l c : Ordinal.{0}) : leH S l 0 c = gxTh (upsilon l) (ldAtR S l) c := rfl

theorem leH_succ_eq (l : Ordinal.{0}) (k : ℕ) {γ c' : Ordinal.{0}} (hc' : c' < leW (k + 1)) :
    leH S l (k + 1) (leW (k + 1) * γ + c') =
      leO (k + 1) * gxTh (upsilon l) (ldAtR S l) γ + leH S l k c' := by
  have hμ0 : leW (k + 1) ≠ 0 := (leW_pos _).ne'
  show leO (k + 1) * gxTh (upsilon l) (ldAtR S l) ((leW (k + 1) * γ + c') / leW (k + 1)) +
    leH S l k ((leW (k + 1) * γ + c') % leW (k + 1)) = _
  rw [Ordinal.mul_add_div _ hμ0, Ordinal.div_eq_zero_of_lt hc', add_zero, Ordinal.mul_add_mod_self,
    Ordinal.mod_eq_of_lt hc']

theorem leOwn_lt {l : Ordinal.{0}} : ∀ (k : ℕ) {β c : Ordinal.{0}}, LeOwn S l k β c → c < leW (k + 1)
  | 0, β, c, h => by
    have e1 : leW (0 + 1) = Om (1 + 1) := leW_one
    rw [e1]; exact h.2.trans (ldTop_lt_Om2 β)
  | k + 1, β, c, h => by
    obtain ⟨γ, c', rfl, -, hγT, hc'⟩ := h
    have hγW : γ + 1 ≤ Om (1 + 1) :=
      Order.add_one_le_of_lt (hγT.trans (leT_lt_Om2 _ _))
    calc leW (k + 1) * γ + c' < leW (k + 1) * γ + leW (k + 1) := (add_lt_add_iff_left _).2 (leOwn_lt k hc')
      _ = leW (k + 1) * (γ + 1) := (mul_add_one _ _).symm
      _ ≤ leW (k + 1) * Om (1 + 1) := leMulW_mono hγW
      _ = leW (k + 1 + 1) := (leW_succ _).symm

theorem leOwn_zero {l : Ordinal.{0}} (hρ0 : 0 < upsilon l) : ∀ (k : ℕ) (β : Ordinal.{0}), LeOwn S l k β 0
  | 0, β => ⟨GxCl.zero hρ0, (Om_pos one_ne_zero).trans (ldOm1_lt_Top β)⟩
  | k + 1, β => ⟨0, 0, by rw [mul_zero, add_zero], GxCl.zero hρ0,
      (Om_pos one_ne_zero).trans (leOm1_lt_T _ _), by rw [mul_zero, add_zero]; exact leOwn_zero hρ0 k β⟩

/-- An own argument `Â + Ω^k·x`. -/
theorem leHat_own (k : ℕ) {Â x : Ordinal.{0}} (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hx : x < S.psi (Â + leO k * x) (Om 1)) :
    Â + leO k * x ∈ S.CSet (Â + leO k * x) (S.psi (Â + leO k * x) (Om 1)) :=
  CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ) (leMulO_mem k (CSet.of_lt hx))

theorem leRho {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) :
    SC (upsilon l) ∧ upsilon l < Om 1 := by
  have hpv := cdEta_pv (S := S) hl.1 hX
  exact ⟨hpv ▸ SC_psi Low.InR_Om_one _, hpv ▸ psi_lt Low.InR_Om_one _⟩

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE BLOCK LAW AT LEVEL `k`.** -/
theorem leBlk : ∀ k : ℕ, ∀ β Â : Ordinal.{0}, LeBase S l k β → Â ∈ S.CSet Â (S.psi Â (Om 1)) →
    gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1) →
    (∀ c, LeOwn S l k β c →
      gxTh (upsilon l) (ldAtR S l) (S.psi (β + c) (Om (1 + 1))) = S.psi (Â + leH S l k c) (Om 1) ∧
      Â + leH S l k c ∈ S.CSet (Â + leH S l k c) (S.psi (Â + leH S l k c) (Om 1)) ∧
      leH S l k c < leO (k + 1)) ∧
    gxTh (upsilon l) (ldAtR S l) (leT S k β) = S.psi (Â + leO (k + 1)) (Om 1) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hρ0 : 0 < upsilon l := hρSC.1
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  intro k
  induction k with
  | zero =>
    intro β Â hb hÂ hbase
    have e1 : leW (0 + 1) = Om (1 + 1) := leW_one
    have e2 : leO (0 + 1) = Om 1 := leO_one
    obtain ⟨hβd, hβH, hβA, hβown⟩ := hb
    rw [e1] at hβd hβA hβown
    refine ⟨fun c hc => ?_, ?_⟩
    · obtain ⟨hcg, hcF⟩ := hc
      have hstep := ldBlk_step hl hX hβown hβd hβH hβA hÂ hbase c hcg hcF
      rw [leH_zero]
      have hlt : gxTh (upsilon l) (ldAtR S l) c <
          S.psi (Â + gxTh (upsilon l) (ldAtR S l) c) (Om 1) := by
        rw [← hstep]; exact gxTh_lt hcg (ldTop_gt hβown hβd hcF)
      refine ⟨hstep, CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ) (CSet.of_lt hlt), ?_⟩
      rw [e2]; exact hlt.trans (psi_lt Low.InR_Om_one _)
    · rw [leT_zero, e2]
      exact ldBlk_next hl hX hβown hβd hβH hβA hÂ hbase
  | succ k IHk =>
    intro β Â hb hÂ hbase
    have hb' := hb
    obtain ⟨hβd, hβH, hβA, hβown⟩ := hb
    have hμ0 : leW (k + 1) ≠ 0 := (leW_pos _).ne'
    have hO0 : leO (k + 1) ≠ 0 := (leO_pos _).ne'
    have hβd' : leW (k + 1) * Om (1 + 1) ∣ β := by rw [← leW_succ]; exact hβd
    have hβA' : β + leW (k + 1) * Om (1 + 1) < ConjT.Aη S (cdEta S l) := by rw [← leW_succ]; exact hβA
    have hsub : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ < leT S (k + 1) β →
        LeBase S l k (β + leW (k + 1) * γ) := fun γ hγ hγT =>
      leBase_sub hb' ((ldHull_iff hl hX (hγT.trans (leT_lt_Om2 _ _))).2 hγ) hγT
    have hγs : ∀ γ, γ < leT S (k + 1) β → γ < S.psi (β + leW (k + 1) * γ) (Om (1 + 1)) :=
      fun γ h => leT_gt hβown hβd h
    have hβat : S.psi β (Om (1 + 1)) ∈ ldAtR S l := ⟨β, hβH, le_self_add.trans_lt hβA, rfl⟩
    have hρÂ : upsilon l < S.psi Â (Om 1) := by
      rw [← hbase]; exact (ldAtom_ge hρSC hρ1 hAt hβat).2.1
    have hsat : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ < Om (1 + 1) →
        S.psi (β + leW (k + 1) * γ) (Om (1 + 1)) ∈ ldAtR S l := by
      intro γ hγ hγW
      refine ⟨β + leW (k + 1) * γ, CSet.add_mem hβH (leMulW_mem _ ((ldHull_iff hl hX hγW).2 hγ)), ?_, rfl⟩
      exact ((add_lt_add_iff_left β).2 (leMulW_lt hγW)).trans hβA'
    have hslt : ∀ γ γ', γ < γ' → γ' ≤ Om (1 + 1) → γ < S.psi (β + leW (k + 1) * γ') (Om (1 + 1)) →
        S.psi (β + leW (k + 1) * γ) (Om (1 + 1)) < S.psi (β + leW (k + 1) * γ') (Om (1 + 1)) := by
      intro γ γ' h hγ'W hown
      refine psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left β).2 (leMulW_lt h)) ?_
      refine CSet.add_mem (hβown _ ?_) (leMulW_mem _ (CSet.of_lt hown))
      rw [leW_succ (k + 1)]; exact leMulW_mono hγ'W
    have hΘsucc : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ →
        gxTh (upsilon l) (ldAtR S l) (γ + 1) = gxTh (upsilon l) (ldAtR S l) γ + 1 := fun γ hγ => by
      rw [gxTh_add hρSC hAt hγ 1, hΘ1]
    have hcode1 : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ + 1 < Om (1 + 1) →
        GxCl (upsilon l) (ldAtR S l) (γ + 1) := fun γ hγ h =>
      (ldHull_iff hl hX h).1 (CSet.succ_mem ((ldHull_iff hl hX ((lt_add_one γ).trans h)).2 hγ))
    have hrle : ∀ r γ', GxCl (upsilon l) (ldAtR S l) γ' →
        r / leO (k + 1) = gxTh (upsilon l) (ldAtR S l) γ' →
        r ≤ leO (k + 1) * gxTh (upsilon l) (ldAtR S l) (γ' + 1) := by
      intro r γ' hγ' hx
      rw [hΘsucc γ' hγ', ← hx, mul_add_one]
      exact (Ordinal.lt_mul_div_add r hO0).le
    -- Step A: the sub-bases
    have hA : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ < leT S (k + 1) β →
        gxTh (upsilon l) (ldAtR S l) (S.psi (β + leW (k + 1) * γ) (Om (1 + 1))) =
          S.psi (Â + leO (k + 1) * gxTh (upsilon l) (ldAtR S l) γ) (Om 1) ∧
        Â + leO (k + 1) * gxTh (upsilon l) (ldAtR S l) γ ∈
          S.CSet (Â + leO (k + 1) * gxTh (upsilon l) (ldAtR S l) γ)
            (S.psi (Â + leO (k + 1) * gxTh (upsilon l) (ldAtR S l) γ) (Om 1)) := by
      intro γ
      induction γ using WellFoundedLT.induction with
      | ind γ IH =>
      intro hγ hγT
      have hγW : γ < Om (1 + 1) := hγT.trans (leT_lt_Om2 _ _)
      suffices e : gxTh (upsilon l) (ldAtR S l) (S.psi (β + leW (k + 1) * γ) (Om (1 + 1))) =
          S.psi (Â + leO (k + 1) * gxTh (upsilon l) (ldAtR S l) γ) (Om 1) by
        refine ⟨e, leHat_own (k + 1) hÂ ?_⟩
        rw [← e]; exact gxTh_lt hγ (hγs γ hγT)
      rcases zero_or_succ_or_isSuccLimit γ with h0 | ⟨γ', hγ'⟩ | hlim
      · subst h0
        rw [mul_zero, add_zero, gxTh_zero, mul_zero, add_zero]; exact hbase
      · rw [succ_eq_add_one] at hγ'
        subst hγ'
        have hγ'c : GxCl (upsilon l) (ldAtR S l) γ' :=
          (ldHull_iff hl hX ((lt_add_one γ').trans hγW)).1 (mem_of_add_one_mem ((ldHull_iff hl hX hγW).2 hγ))
        have hγ'T : γ' < leT S (k + 1) β := (lt_add_one γ').trans hγT
        obtain ⟨e', own'⟩ := IH γ' (lt_add_one γ') hγ'c hγ'T
        have h := (IHk (β + leW (k + 1) * γ') _ (hsub γ' hγ'c hγ'T) own' e').2
        have eT : leT S k (β + leW (k + 1) * γ') = S.psi (β + leW (k + 1) * (γ' + 1)) (Om (1 + 1)) := by
          unfold leT; rw [add_assoc, ← mul_add_one]
        rw [eT, add_assoc, ← mul_add_one] at h
        rw [h, hΘsucc γ' hγ'c]
      · have hγ0 : γ ≠ 0 := hlim.ne_bot
        have hΘ0 : 0 < gxTh (upsilon l) (ldAtR S l) γ := by
          have := gxTh_lt (Z := upsilon l) (At := ldAtR S l) (GxCl.zero hρ0) (pos_iff_ne_zero.2 hγ0)
          rwa [gxTh_zero] at this
        have hsγ := hsat γ hγ hγW
        set X := S.psi (Â + leO (k + 1) * gxTh (upsilon l) (ldAtR S l) γ) (Om 1) with hX_def
        have hÂX : Â ∈ S.CSet (Â + leO (k + 1) * gxTh (upsilon l) (ldAtR S l) γ) X :=
          (psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ
        have hÂlt : S.psi Â (Om 1) < X :=
          psi_lt_psi_of_mem Low.InR_Om_one (lt_add_of_pos_right Â (mul_pos (leO_pos _) hΘ0)) hÂX
        have hlt1 : ∀ γ1, GxCl (upsilon l) (ldAtR S l) γ1 → γ1 < γ →
            gxTh (upsilon l) (ldAtR S l) (S.psi (β + leW (k + 1) * γ1) (Om (1 + 1))) =
              S.psi (Â + leO (k + 1) * gxTh (upsilon l) (ldAtR S l) γ1) (Om 1) ∧
            S.psi (Â + leO (k + 1) * gxTh (upsilon l) (ldAtR S l) γ1) (Om 1) < X := by
          intro γ1 hγ1 h1
          obtain ⟨e1, own1⟩ := IH γ1 h1 hγ1 (h1.trans hγT)
          have hlt : Â + leO (k + 1) * gxTh (upsilon l) (ldAtR S l) γ1 <
              Â + leO (k + 1) * gxTh (upsilon l) (ldAtR S l) γ :=
            (add_lt_add_iff_left Â).2 ((mul_lt_mul_iff_right₀ (leO_pos _)).2 (gxTh_lt hγ1 h1))
          exact ⟨e1, psi_lt_psi_of_mem Low.InR_Om_one hlt ((psi_mono (S := S) Low.InR_Om_one hlt.le).2 own1)⟩
        apply le_antisymm
        · refine ldAtom_le hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) (hρÂ.trans hÂlt) ?_
          intro t ht hts
          obtain ⟨a, haH, -, rfl⟩ := ht
          rcases lt_or_ge a β with haβ | haβ
          · exact (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) haβ.le).1).trans_lt (by rw [hbase]; exact hÂlt)
          have haγ : a < β + leW (k + 1) * γ := by
            by_contra h
            push Not at h
            exact absurd hts (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) h).1)
          obtain ⟨hgW, hlo, hhi, -⟩ := leSplit hμ0 hβd' haβ
            (haγ.trans ((add_lt_add_iff_left β).2 (leMulW_lt hγW)))
          have hgγ : a / leW (k + 1) % Om (1 + 1) < γ := by
            by_contra h
            push Not at h
            exact absurd (((add_le_add_iff_left β).2 (leMulW_mono h)).trans hlo) (not_le.2 haγ)
          have hgH : a / leW (k + 1) % Om (1 + 1) ∈ cdHull S l := ldModK_mem ldOm2_SC (leDivW_mem _ haH)
          have hgc := (ldHull_iff hl hX hgW).1 hgH
          have hg1γ := hlim.succ_lt hgγ
          have hg1c := hcode1 _ hgc (hg1γ.trans hγW)
          obtain ⟨e1, hlt⟩ := hlt1 _ hg1c hg1γ
          refine lt_of_le_of_lt (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) hhi.le).1) ?_
          rw [e1]; exact hlt
        · obtain ⟨hTSC, -, hTs⟩ := ldAtom_ge hρSC hρ1 hAt hsγ
          refine ldPsi1_le hTSC fun e he _ => ?_
          have hβs : S.psi β (Om (1 + 1)) < S.psi (β + leW (k + 1) * γ) (Om (1 + 1)) := by
            have := hslt 0 γ (pos_iff_ne_zero.2 hγ0) hγW.le ((pos_iff_ne_zero.2 hγ0).trans (hγs γ hγT))
            rwa [mul_zero, add_zero] at this
          rcases le_or_gt e Â with heÂ | heÂ
          · refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one heÂ).1 ?_
            rw [← hbase]; exact hTs _ hβat hβs
          obtain ⟨r, rfl⟩ := exists_add_of_le heÂ.le
          have hr : r < leO (k + 1) * gxTh (upsilon l) (ldAtR S l) γ := (add_lt_add_iff_left Â).1 he
          have hx : r / leO (k + 1) < gxTh (upsilon l) (ldAtR S l) γ := (Ordinal.lt_mul_iff_div_lt hO0).1 hr
          obtain ⟨γ', hγ'c, hγ'γ, hγ'x⟩ := gxTh_onto hx
          have hγ'1 := hlim.succ_lt hγ'γ
          have hγ'1c := hcode1 _ hγ'c (hγ'1.trans hγW)
          obtain ⟨e1, -⟩ := hlt1 _ hγ'1c hγ'1
          refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one
            ((add_le_add_iff_left Â).2 (hrle r γ' hγ'c hγ'x.symm))).1 ?_
          rw [← e1]
          exact hTs _ (hsat _ hγ'1c (hγ'1.trans hγW)) (hslt _ γ hγ'1 hγW.le (hγ'1.trans (hγs γ hγT)))
    refine ⟨fun c hc => ?_, ?_⟩
    · -- Step B: the own arguments
      obtain ⟨γ, c', rfl, hγc, hγT, hc'⟩ := hc
      obtain ⟨eγ, ownγ⟩ := hA γ hγc hγT
      obtain ⟨e2, own2, hbd2⟩ := (IHk (β + leW (k + 1) * γ) _ (hsub γ hγc hγT) ownγ eγ).1 c' hc'
      rw [leH_succ_eq l k (leOwn_lt k hc'), ← add_assoc β, ← add_assoc Â]
      refine ⟨e2, own2, ?_⟩
      have hΘ1' : gxTh (upsilon l) (ldAtR S l) γ < Om 1 := by
        refine (gxTh_lt hγc (hγs γ hγT)).trans ?_
        rw [eγ]; exact psi_lt Low.InR_Om_one _
      calc leO (k + 1) * gxTh (upsilon l) (ldAtR S l) γ + leH S l k c'
          < leO (k + 1) * gxTh (upsilon l) (ldAtR S l) γ + leO (k + 1) := (add_lt_add_iff_left _).2 hbd2
        _ = leO (k + 1) * (gxTh (upsilon l) (ldAtR S l) γ + 1) := (mul_add_one _ _).symm
        _ ≤ leO (k + 1) * Om 1 := mul_le_mul_right (Order.add_one_le_of_lt hΘ1') _
        _ = leO (k + 1 + 1) := (leO_succ _).symm
    · -- Step C: the top
      have htat : leT S (k + 1) β ∈ ldAtR S l :=
        ⟨β + leW (k + 1 + 1), CSet.add_mem hβH (leW_mem _ _ _), hβA, rfl⟩
      set X := S.psi (Â + leO (k + 1 + 1)) (Om 1) with hX_def
      have hÂX : Â ∈ S.CSet (Â + leO (k + 1 + 1)) X := (psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ
      have hÂlt : S.psi Â (Om 1) < X :=
        psi_lt_psi_of_mem Low.InR_Om_one (lt_add_of_pos_right Â (leO_pos _)) hÂX
      have hTW : leT S (k + 1) β = S.psi (β + leW (k + 1) * Om (1 + 1)) (Om (1 + 1)) := leT_succ_eq k β
      -- the readings of the sub-bases are below `X`
      have hsubX : ∀ g, GxCl (upsilon l) (ldAtR S l) g → g < leT S (k + 1) β →
          S.psi (Â + leO (k + 1) * gxTh (upsilon l) (ldAtR S l) g) (Om 1) < X := by
        intro g hg hgT
        obtain ⟨e1, own1⟩ := hA g hg hgT
        have hΘ1' : gxTh (upsilon l) (ldAtR S l) g < Om 1 := by
          refine (gxTh_lt hg (hγs g hgT)).trans ?_
          rw [e1]; exact psi_lt Low.InR_Om_one _
        have hlt : Â + leO (k + 1) * gxTh (upsilon l) (ldAtR S l) g < Â + leO (k + 1 + 1) := by
          refine (add_lt_add_iff_left Â).2 ?_
          rw [leO_succ (k + 1)]; exact (mul_lt_mul_iff_right₀ (leO_pos _)).2 hΘ1'
        exact psi_lt_psi_of_mem Low.InR_Om_one hlt ((psi_mono (S := S) Low.InR_Om_one hlt.le).2 own1)
      -- a sub-base atom below the top
      have hsubT : ∀ g, g < leT S (k + 1) β →
          S.psi (β + leW (k + 1) * g) (Om (1 + 1)) < leT S (k + 1) β := by
        intro g hgT
        rw [hTW]
        exact hslt g (Om (1 + 1)) (hgT.trans (leT_lt_Om2 _ _)) le_rfl (by rw [← hTW]; exact hgT)
      apply le_antisymm
      · refine ldAtom_le hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) (hρÂ.trans hÂlt) ?_
        intro t ht hts
        obtain ⟨a, haH, -, rfl⟩ := ht
        rcases lt_or_ge a β with haβ | haβ
        · exact (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) haβ.le).1).trans_lt (by rw [hbase]; exact hÂlt)
        have ha2 : a < β + leW (k + 1) * Om (1 + 1) := by
          by_contra h
          push Not at h
          rw [hTW] at hts
          exact absurd hts (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) h).1)
        obtain ⟨hgW, hlo, hhi, -⟩ := leSplit hμ0 hβd' haβ ha2
        have hgH : a / leW (k + 1) % Om (1 + 1) ∈ cdHull S l := ldModK_mem ldOm2_SC (leDivW_mem _ haH)
        have hgc := (ldHull_iff hl hX hgW).1 hgH
        have hgT : a / leW (k + 1) % Om (1 + 1) < leT S (k + 1) β := by
          by_contra h
          push Not at h
          have h1 := leT_ge hβown hβd h
          exact absurd (h1.trans (psi_mono (S := S) (InR_Om_succ 1) hlo).1) (not_le.2 hts)
        have hg1T := (leT_SC (S := S) (k + 1) β).isSuccLimit.succ_lt hgT
        have hg1c := hcode1 _ hgc (hg1T.trans (leT_lt_Om2 _ _))
        refine lt_of_le_of_lt (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) hhi.le).1) ?_
        rw [(hA _ hg1c hg1T).1]; exact hsubX _ hg1c hg1T
      · obtain ⟨hTSC, -, hTs⟩ := ldAtom_ge hρSC hρ1 hAt htat
        refine lePsi1_le hTSC fun e he hc => ?_
        have hβs : S.psi β (Om (1 + 1)) < leT S (k + 1) β := by
          have := hsubT 0 ((Om_pos one_ne_zero).trans (leOm1_lt_T _ _))
          rwa [mul_zero, add_zero] at this
        rcases le_or_gt e Â with heÂ | heÂ
        · refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one heÂ).1 ?_
          rw [← hbase]; exact hTs _ hβat hβs
        obtain ⟨r, rfl⟩ := exists_add_of_le heÂ.le
        have hr : r < leO (k + 1 + 1) := (add_lt_add_iff_left Â).1 he
        have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
        have hΩG1 : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
        have hc2 := LeCl.mod hTSC.1 Ph.ph_SC_Om1.isPrincipal (Om 1 * ((k + 1 + 1 : ℕ) : Ordinal.{0})) hc
        change LeCl (Om 1) _ ((Â + r) % S.psi 0 (Om (1 + 1)) % leO (k + 1 + 1)) at hc2
        rw [Ordinal.mod_mod_of_dvd _ (leO_lt_SC hG1 hΩG1 _).2] at hc2
        have hmod : (Â + r) % leO (k + 1 + 1) = Â % leO (k + 1 + 1) + r := leMod_add_lt _ Â hr
        rw [hmod] at hc2
        have hlt' : Â % leO (k + 1 + 1) + r < leO (k + 1 + 1) :=
          isPrincipal_add_omega0_opow _ (Ordinal.mod_lt Â (leO_pos _).ne') hr
        have hbnd := leCl_bound hTSC Ph.ph_SC_Om1 (k + 1) _ hc2 hlt'
        change Â % leO (k + 1 + 1) + r < leO (k + 1) * _ at hbnd
        have hrT : r < leO (k + 1) * gxTh (upsilon l) (ldAtR S l) (leT S (k + 1) β) :=
          le_add_self.trans_lt hbnd
        have hx := (Ordinal.lt_mul_iff_div_lt hO0).1 hrT
        obtain ⟨γ', hγ'c, hγ'T, hγ'x⟩ := gxTh_onto hx
        have hγ'1T := (leT_SC (S := S) (k + 1) β).isSuccLimit.succ_lt hγ'T
        have hγ'1c := hcode1 _ hγ'c (hγ'1T.trans (leT_lt_Om2 _ _))
        refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one
          ((add_le_add_iff_left Â).2 (hrle r γ' hγ'c hγ'x.symm))).1 ?_
        rw [← (hA _ hγ'1c hγ'1T).1]
        exact hTs _ (hsat _ hγ'1c (hγ'1T.trans (leT_lt_Om2 _ _))) (hsubT _ hγ'1T)

/-- **Every atom of a block of level `k` is `≤ ψ_{Ω₂}(β)` or `ψ_{Ω₂}(β + c)` with `c` own.** -/
theorem leCls : ∀ (k : ℕ) (β : Ordinal.{0}), LeBase S l k β → ∀ t ∈ ldAtR S l, t < leT S k β →
    t ≤ S.psi β (Om (1 + 1)) ∨ ∃ c, LeOwn S l k β c ∧ t = S.psi (β + c) (Om (1 + 1)) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  intro k
  induction k with
  | zero =>
    intro β hb t ht htT
    have e1 : leW (0 + 1) = Om (1 + 1) := leW_one
    obtain ⟨hβd, -, -, hβown⟩ := hb
    rw [e1] at hβd hβown
    rw [leT_zero] at htT
    rcases ldBlk_cls hl hX hβown hβd ht htT with h | ⟨c, hc, hcF, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨c, ⟨hc, hcF⟩, rfl⟩
  | succ k IHk =>
    intro β hb t ht htT
    have hb' := hb
    obtain ⟨hβd, hβH, -, hβown⟩ := hb
    have hμ0 : leW (k + 1) ≠ 0 := (leW_pos _).ne'
    have hβd' : leW (k + 1) * Om (1 + 1) ∣ β := by rw [← leW_succ]; exact hβd
    have hTW : leT S (k + 1) β = S.psi (β + leW (k + 1) * Om (1 + 1)) (Om (1 + 1)) := leT_succ_eq k β
    obtain ⟨a, haH, haA, rfl⟩ := ht
    rcases lt_or_ge a β with haβ | haβ
    · exact Or.inl (psi_mono (S := S) (InR_Om_succ 1) haβ.le).1
    have ha2 : a < β + leW (k + 1) * Om (1 + 1) := by
      by_contra h
      push Not at h
      rw [hTW] at htT
      exact absurd htT (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) h).1)
    obtain ⟨hgW, hlo, hhi, -⟩ := leSplit hμ0 hβd' haβ ha2
    set g := a / leW (k + 1) % Om (1 + 1) with hg_def
    have hgH : g ∈ cdHull S l := ldModK_mem ldOm2_SC (leDivW_mem _ haH)
    have hgc := (ldHull_iff hl hX hgW).1 hgH
    have hgT : g < leT S (k + 1) β := by
      by_contra h
      push Not at h
      have h1 := leT_ge hβown hβd h
      exact absurd (h1.trans (psi_mono (S := S) (InR_Om_succ 1) hlo).1) (not_le.2 htT)
    have hb2 := leBase_sub hb' hgH hgT
    have hρ0 : 0 < upsilon l := hρSC.1
    rcases lt_or_ge (S.psi a (Om (1 + 1))) (leT S k (β + leW (k + 1) * g)) with hlt | hge
    · rcases IHk _ hb2 _ ⟨a, haH, haA, rfl⟩ hlt with hle | ⟨c', hc', e⟩
      · refine Or.inr ⟨leW (k + 1) * g + 0, ⟨g, 0, rfl, hgc, hgT, leOwn_zero hρ0 k _⟩, ?_⟩
        rw [add_zero]
        exact le_antisymm hle (psi_mono (S := S) (InR_Om_succ 1) hlo).1
      · exact Or.inr ⟨leW (k + 1) * g + c', ⟨g, c', rfl, hgc, hgT, hc'⟩, by rw [← add_assoc]; exact e⟩
    · have hg1T := (leT_SC (S := S) (k + 1) β).isSuccLimit.succ_lt hgT
      have hg1W : g + 1 < Om (1 + 1) := hg1T.trans (leT_lt_Om2 _ _)
      have hg1c : GxCl (upsilon l) (ldAtR S l) (g + 1) :=
        (ldHull_iff hl hX hg1W).1 (CSet.succ_mem hgH)
      refine Or.inr ⟨leW (k + 1) * (g + 1) + 0, ⟨g + 1, 0, rfl, hg1c, hg1T, leOwn_zero hρ0 k _⟩, ?_⟩
      have eT : leT S k (β + leW (k + 1) * g) = S.psi (β + leW (k + 1) * (g + 1)) (Om (1 + 1)) := by
        unfold leT; rw [add_assoc, ← mul_add_one]
      rw [eT] at hge
      rw [add_zero]
      exact le_antisymm (psi_mono (S := S) (InR_Om_succ 1) hhi.le).1 hge

/-- **Every atom `t < F_{ω²}` is `ψ_{Ω₂}(c)` with `c` own at a level `k`, and `Θ_λ(t) = ψ_{Ω₁}(A + 1 + h_k(c))`.** -/
theorem leTh_Fw {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    ∀ t ∈ ldAtR S l, t < leFw S → ∃ (k : ℕ) (c : Ordinal.{0}), LeOwn S l k 0 c ∧ t = S.psi c (Om (1 + 1)) ∧
      gxTh (upsilon l) (ldAtR S l) t = S.psi (A + 1 + leH S l k c) (Om 1) ∧
      A + 1 + leH S l k c ∈ S.CSet (A + 1 + leH S l k c) (S.psi (A + 1 + leH S l k c) (Om 1)) ∧
      leH S l k c < leO (k + 1) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hρ0 : 0 < upsilon l := hρSC.1
  have hA1 : A + 1 ∈ S.CSet (A + 1) (S.psi (A + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) (CSet.one_mem _ _)
  have hbase0 := ldBlk_zero hA hρ
  intro t ht htF
  obtain ⟨a, haH, haA, rfl⟩ := ht
  have haW : a < ω ^ (Om (1 + 1) * ω) := by
    by_contra h
    push Not at h
    exact absurd htF (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) h).1)
  obtain ⟨c', hc', hac'⟩ := (lt_opow_of_isSuccLimit omega0_ne_zero
    (isSuccLimit_mul_right ldOm2_SC.1 isSuccLimit_omega0)).1 haW
  obtain ⟨n, hn, hc'n⟩ := (lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 hc'
  obtain ⟨m, rfl⟩ := Ordinal.lt_omega0.1 hn
  have ham : a < leW (m + 1) :=
    hac'.trans ((opow_lt_opow_iff_right one_lt_omega0).2 (hc'n.trans_le (mul_le_mul_right (by
      exact_mod_cast Nat.le_succ m) _)))
  have hle : S.psi a (Om (1 + 1)) ≤ leT S m 0 := by
    unfold leT; rw [zero_add]; exact (psi_mono (S := S) (InR_Om_succ 1) ham.le).1
  have hrep : ∃ (k : ℕ) (c : Ordinal.{0}), LeOwn S l k 0 c ∧ S.psi a (Om (1 + 1)) = S.psi c (Om (1 + 1)) := by
    rcases hle.lt_or_eq with hlt | heq
    · rcases leCls hl hX m 0 (leBase_zero l m) _ ⟨a, haH, haA, rfl⟩ hlt with h0 | ⟨c, hc, e⟩
      · exact ⟨m, 0, leOwn_zero hρ0 m 0, le_antisymm h0 (psi_mono (S := S) (InR_Om_succ 1) zero_le).1⟩
      · rw [zero_add] at e; exact ⟨m, c, hc, e⟩
    · have h1ρ : (1 : Ordinal.{0}) < upsilon l := gg_one_lt_of_SC hρSC
      have h1T : (1 : Ordinal.{0}) < leT S (m + 1) 0 :=
        (one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1)).trans (leOm1_lt_T _ _)
      refine ⟨m + 1, leW (m + 1) * 1 + 0, ⟨1, 0, rfl, GxCl.small h1ρ, h1T, leOwn_zero hρ0 m _⟩, ?_⟩
      rw [heq, mul_one, add_zero]; unfold leT; rw [zero_add]
  obtain ⟨k, c, hc, e⟩ := hrep
  obtain ⟨e1, own, hb⟩ := (leBlk hl hX k 0 (A + 1) (leBase_zero l k) hA1 hbase0).1 c hc
  rw [zero_add] at e1
  exact ⟨k, c, hc, e, by rw [e]; exact e1, own, hb⟩

end Main

end Googology.Trans.PoR.InaccPsi.R2.Le
