import Googology.Trans.PoR.InaccPsi.R2.RwOwn

/-!
# Every atom of a shifted block is `ψ_{Ω₂}(β + c)` with `c` own, for base-indexed families of shifts

`W^E = Ω₂^E`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `Sh b X X̂` a family of shifts indexed by the base (`Rw.RwOwn`).

`RwClsAt S λ Sh X e β` (a hypothesis name, **the atoms below `T_{X+e}(β)` are own**): every atom `t < T_{X+e}(β)`
is `≤ ψ_{Ω₂}(β)` or `ψ_{Ω₂}(β + c)` with `(X', e', c, v)` own over `β` (`Rw.RwOwn`), `β` a base of shift `X'` and
exponent `e'`, and either `X' = X`, `e' ≤ e`, or `X' + Ω₂ ≤ X`, `e' < T_{X'+Ω₂}(β)`.

* `rwTop_own` (the top of a sub-block is own), `rwCls_one` (**`RwClsAt Ω₂ 0` at every base**);
* `rwClsE` (**`RwClsAt X 0` at every base `≥ b` gives `RwClsAt X e` at every base `≥ b` for every code `e`**),
  `rwClsW` (**the pull-back to `X + Ω₂`**), `rwClsLimSh` (**a limit shift**, base by base), as `Rq.rqClsE`,
  `Rq.rqClsW`, `Rq.rqClsLimSh`; the family is asked to be hereditary (`Sh b ⊆ Sh b'` for `b ≤ b'`).

No new axiom.  New definitions: the hypothesis name `RwClsAt`, `RwRd` (a base with a reading; the closure is
asked only at the bases with a reading, and the sub-bases inherit one by `Rv.rvStepA`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv

variable {S : InaccSeq.{0}}

/-- **The atoms below `T_{X+e}(β)` are own** (base-indexed family). -/
def RwClsAt (S : InaccSeq.{0}) (l : Ordinal.{0}) (Sh : Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Prop)
    (X e β : Ordinal.{0}) : Prop :=
  ∀ t ∈ ldAtR S l, t < leTe S (X + e) β → t ≤ S.psi β (Om (1 + 1)) ∨
    ∃ X' e' c v, ((X' = X ∧ e' ≤ e) ∨ (X' + Om (1 + 1) ≤ X ∧ e' < leTe S (X' + Om (1 + 1)) β)) ∧
      RwOwn S l Sh X' e' β c v ∧ RoBaseE S l X' e' β ∧ t = S.psi (β + c) (Om (1 + 1))

/-- **`β` has a reading**: `Θ(ψ_{Ω₂}(β)) = ψ_{Ω₁}(Â)` with `Â` own. -/
def RwRd (S : InaccSeq.{0}) (l β : Ordinal.{0}) : Prop :=
  ∃ Â, Â ∈ S.CSet Â (S.psi Â (Om 1)) ∧ gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1)

/-- The top `ψ_{Ω₂}(β + W^{X+g}·γ)` of a sub-block, `γ ≠ 0` a code `< T_{X+g+1}(β)`, is own. -/
theorem rwTop_own {l : Ordinal.{0}} {Sh : Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Prop} {X Xh g β γ : Ordinal.{0}}
    (hsh : Sh β X Xh) (hXW : Om (1 + 1) ≤ X)
    (hgc : GxCl (upsilon l) (ldAtR S l) g) (hγc : GxCl (upsilon l) (ldAtR S l) γ) (hγ0 : γ ≠ 0)
    (hγT : γ < leTe S (X + g + 1) β) :
    RwOwn S l Sh X (g + 1) β (leWe (X + g) * γ + 0)
      (leOe (Xh + gxTh (upsilon l) (ldAtR S l) g) * gxTh (upsilon l) (ldAtR S l) γ + 0) := by
  have hT0 : (0 : Ordinal.{0}) < leTe S (0 + Om (1 + 1)) (β + leWe (X + g) * γ) :=
    (Om_pos one_ne_zero).trans (leOm1_lt_Te _ _)
  exact RwOwn.succ hsh hgc hγc hγ0 hγT (Or.inr ⟨by rw [zero_add]; exact hXW, hT0⟩) (RwOwn.low LeOwnH.zero)

/-- **`RwClsAt Ω₂ 0` at every base**, from `Le.leClsE`. -/
theorem rwCls_one {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    {Sh : Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Prop} {β : Ordinal.{0}}
    (hb : RoBaseE S l (Om (1 + 1) * ((1 : ℕ) : Ordinal.{0})) 0 β) :
    RwClsAt S l Sh (Om (1 + 1) * ((1 : ℕ) : Ordinal.{0})) 0 β := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
  simp only [Nat.cast_one, mul_one, add_zero] at hβd hβA hβown ⊢
  have hrb : RnBase S l β := ⟨hβd, hβH, hβA, hβown⟩
  intro t ht htT
  rw [add_zero] at htT
  obtain ⟨a, haH, haA, rfl⟩ := ht
  rcases lt_or_ge a β with haβ | haβ
  · exact Or.inl (psi_mono (S := S) (InR_Om_succ 1) haβ.le).1
  obtain ⟨d, rfl⟩ := exists_add_of_le haβ
  rcases eq_or_ne d 0 with rfl | hd0
  · rw [add_zero]; exact Or.inl le_rfl
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hdW : d < leWe (Om (1 + 1)) := by
    by_contra h
    push Not at h
    exact absurd htT (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 h)).1)
  have hdH : d ∈ cdHull S l := by
    have h1 := leModP_mem (S := S) (Om (1 + 1) * Om (1 + 1)) haH
    have hm : (β + d) % ω ^ (Om (1 + 1) * Om (1 + 1)) = d := by
      obtain ⟨q, hq⟩ := hβd
      change (β + d) % leWe (Om (1 + 1)) = d
      rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hdW]
    rwa [hm] at h1
  have hlogd : log ω d < Om (1 + 1) * Om (1 + 1) :=
    (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hd0).trans_lt hdW)
  have hgW : log ω d / Om (1 + 1) < Om (1 + 1) := (Ordinal.lt_mul_iff_div_lt hW0).1 hlogd
  have hgH : log ω d / Om (1 + 1) ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hdH)
  have hgT : log ω d / Om (1 + 1) < rnTW S β := by
    by_contra h
    push Not at h
    have h1 := rnTW_ge hβown hβd h
    have h2 : leWe (log ω d / Om (1 + 1)) ≤ d := by
      unfold leWe
      exact (opow_le_opow_right omega0_pos (Ordinal.mul_div_le _ _)).trans (opow_log_le_self ω hd0)
    exact absurd (h1.trans (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 h2)).1)
      (not_le.2 htT)
  set E := log ω d / Om (1 + 1) + 1 with hE_def
  have hET : E < rnTW S β := (rnTW_SC β).isSuccLimit.succ_lt hgT
  have hEW : E < Om (1 + 1) := hET.trans (rnTW_lt_Om2 β)
  have hEc : GxCl (upsilon l) (ldAtR S l) E := (ldHull_iff hl hX hEW).1 (CSet.succ_mem hgH)
  have hdE : d < leWe E := roLt_We_log d
  have hle : S.psi (β + d) (Om (1 + 1)) ≤ leTe S E β := by
    unfold leTe; exact (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hdE.le)).1
  have hb0 : ∀ e, e < rnTW S β → RoBaseE S l 0 e β := fun e he => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := rnBaseE hrb he
    refine ⟨by rwa [zero_add], h2, by rwa [zero_add], by rwa [zero_add], fun e' he' h' => ?_⟩
    rw [zero_add]; exact h5 e' he' h'
  have hcnd : ∀ e, e < rnTW S β → (0 = Om (1 + 1) ∧ e ≤ 0) ∨
      (0 + Om (1 + 1) ≤ Om (1 + 1) ∧ e < leTe S (0 + Om (1 + 1)) β) := fun e he =>
    Or.inr ⟨by rw [zero_add], by rw [zero_add]; exact he⟩
  rcases hle.lt_or_eq with hlt | heq
  · rcases leClsE hl hX E hEc le_add_self β (rnBaseE hrb hET) _ ⟨β + d, haH, haA, rfl⟩ hlt with
      h0 | ⟨e', c, v, he', hown, e⟩
    · exact Or.inl h0
    · have he'T := he'.trans_lt hET
      exact Or.inr ⟨0, e', c, v, hcnd e' he'T, RwOwn.low hown, hb0 e' he'T, e⟩
  · have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
    have h1T : (1 : Ordinal.{0}) < leTe S (E + 1) β := roOne_lt_Te _ _
    have hE1T := (rnTW_SC β).isSuccLimit.succ_lt hET
    refine Or.inr ⟨0, E + 1, leWe E * 1 + 0, _, hcnd _ hE1T,
      RwOwn.low (LeOwnH.succ hEc le_add_self hc1 one_ne_zero h1T zero_le LeOwnH.zero), hb0 _ hE1T, ?_⟩
    rw [heq, mul_one, add_zero]; rfl

/-- A relative shift is at least `Ω₂`. -/
theorem rwSh_W {l b X Xh : Ordinal.{0}} (hs : RvSh S l b X Xh) : Om (1 + 1) ≤ X := by
  obtain ⟨q, hq⟩ := hs.dvd
  rw [hq]
  have hq0 : q ≠ 0 := by rintro rfl; exact hs.ne (by rw [hq, mul_zero])
  exact le_mul_left _ (pos_iff_ne_zero.2 hq0)

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {Sh : Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Prop}

include hl hX

variable (hSh : ∀ b X Xh, Sh b X Xh → RvSh S l b X Xh ∧
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → RvTop S l b X Xh e)
  (hShM : ∀ b b' X Xh, b ≤ b' → Sh b X Xh → Sh b' X Xh)

include hSh hShM

/-- **`RwClsAt X 0` at every base `≥ b` gives `RwClsAt X e` at every base `≥ b` for every code `e`.** -/
theorem rwClsE {b X Xh : Ordinal.{0}} (hsh : Sh b X Xh)
    (hlow : ∀ β, b ≤ β → RoBaseE S l X 0 β → RwRd S l β → RwClsAt S l Sh X 0 β) :
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β, b ≤ β → RoBaseE S l X e β → RwRd S l β →
      RwClsAt S l Sh X e β := by
  obtain ⟨hs, hTop⟩ := hSh b X Xh hsh
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hρ0 : 0 < upsilon l := hρSC.1
  have hXW : Om (1 + 1) ≤ X := rwSh_W hs
  have hcode1 : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ + 1 < Om (1 + 1) →
      GxCl (upsilon l) (ldAtR S l) (γ + 1) := fun γ hγ h =>
    (ldHull_iff hl hX h).1 (CSet.succ_mem ((ldHull_iff hl hX ((lt_add_one γ).trans h)).2 hγ))
  have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
  have hc0 : GxCl (upsilon l) (ldAtR S l) (0 : Ordinal.{0}) := GxCl.zero hρ0
  intro e
  induction e using WellFoundedLT.induction with
  | ind e IH =>
  intro hec heW β hbβ hb hrd t ht htT
  have hshβ : Sh β X Xh := hShM b β X Xh hbβ hsh
  have hb' := hb
  obtain ⟨hβd, hβH, -, hβown, hexpA⟩ := hb
  obtain ⟨a, haH, haA, rfl⟩ := ht
  rcases lt_or_ge a β with haβ | haβ
  · exact Or.inl (psi_mono (S := S) (InR_Om_succ 1) haβ.le).1
  rcases zero_or_succ_or_isSuccLimit e with h0 | ⟨e0, he0⟩ | hlim
  · subst h0; exact hlow β hbβ hb' hrd _ ⟨a, haH, haA, rfl⟩ htT
  · rw [succ_eq_add_one] at he0
    subst he0
    have he0W : e0 < Om (1 + 1) := (lt_add_one e0).trans heW
    have he0c : GxCl (upsilon l) (ldAtR S l) e0 :=
      (ldHull_iff hl hX he0W).1 (mem_of_add_one_mem ((ldHull_iff hl hX heW).2 hec))
    have hexp0 : e0 < S.psi (β + leWe (X + e0)) (Om (1 + 1)) := hexpA e0 he0c (lt_add_one e0).le
    obtain ⟨hEC, hEG, hEL⟩ := rvE_data hs hbβ hexp0
    obtain ⟨hβd1, -, hβown1⟩ := roBase_succ hb'
    have hμ0 : leWe (X + e0) ≠ 0 := (leWe_pos _).ne'
    have hβd' : leWe (X + e0) * Om (1 + 1) ∣ β := by rw [← leWe_succ]; exact hβd1
    have hTW : leTe S (X + e0 + 1) β = S.psi (β + leWe (X + e0) * Om (1 + 1)) (Om (1 + 1)) :=
      leTe_succ (X + e0) β
    rw [← add_assoc] at htT
    have ha2 : a < β + leWe (X + e0) * Om (1 + 1) := by
      by_contra h
      push Not at h
      rw [hTW] at htT
      exact absurd htT (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) h).1)
    obtain ⟨hgW, hlo, hhi⟩ := leSplitE hμ0 hβd' haβ ha2
    set g := a % (leWe (X + e0) * Om (1 + 1)) / leWe (X + e0) with hg_def
    have hgH : g ∈ cdHull S l := by
      have h1 : a % (leWe (X + e0) * Om (1 + 1)) ∈ cdHull S l := by
        rw [← leWe_succ]; exact leModP_mem _ haH
      have h2 : a % (leWe (X + e0) * Om (1 + 1)) < ω ^ (Om (1 + 1) * (X + e0) + Om (1 + 1)) := by
        have : leWe (X + e0) * Om (1 + 1) = ω ^ (Om (1 + 1) * (X + e0) + Om (1 + 1)) := by
          rw [← leWe_succ]; unfold leWe; rw [mul_add_one]
        rw [← this]; exact Ordinal.mod_lt _ (mul_ne_zero hμ0 ldOm2_SC.1.ne')
      exact leDivOp_mem (dvd_mul_right _ _) h1 h2
    have hgc := (ldHull_iff hl hX hgW).1 hgH
    have hgT : g < leTe S (X + e0 + 1) β := by
      by_contra h
      push Not at h
      have h1 := roTe_ge hβown1 hEC hβd1 hEG hEL h
      exact absurd (h1.trans (psi_mono (S := S) (InR_Om_succ 1) hlo).1) (not_le.2 htT)
    have hb2 := rvBaseE_sub hs hbβ hl hX hb' he0c hgH hgT
    have hbβ2 : b ≤ β + leWe (X + e0) * g := hbβ.trans le_self_add
    have hrd2 : RwRd S l (β + leWe (X + e0) * g) := by
      obtain ⟨Â, hÂ, hbase⟩ := hrd
      obtain ⟨e1, own1⟩ := rvStepA hs hl hX he0c (hTop e0 he0c he0W) hb' hbβ hÂ hbase g hgc hgT
      exact ⟨_, own1, e1⟩
    rcases lt_or_ge (S.psi a (Om (1 + 1))) (leTe S (X + e0) (β + leWe (X + e0) * g)) with hlt | hge
    · rcases IH e0 (lt_add_one e0) he0c he0W _ hbβ2 hb2 hrd2 _ ⟨a, haH, haA, rfl⟩ hlt with
        hle | ⟨X', e', c', v, hcond, hown, hbo, e⟩
      · have heq : S.psi a (Om (1 + 1)) = S.psi (β + leWe (X + e0) * g) (Om (1 + 1)) :=
          le_antisymm hle (psi_mono (S := S) (InR_Om_succ 1) hlo).1
        rcases eq_or_ne g 0 with hg0 | hg0
        · rw [hg0, mul_zero, add_zero] at heq; exact Or.inl heq.le
        · refine Or.inr ⟨X, e0 + 1, _, _, Or.inl ⟨rfl, le_rfl⟩, rwTop_own hshβ hXW he0c hgc hg0 hgT,
            hb', ?_⟩
          rw [add_zero]; exact heq
      · rcases eq_or_ne g 0 with hg0 | hg0
        · rw [hg0, mul_zero, add_zero] at hown e hbo hcond
          refine Or.inr ⟨X', e', c', v, ?_, hown, hbo, e⟩
          rcases hcond with ⟨h1, h2⟩ | h2
          · exact Or.inl ⟨h1, h2.trans (lt_add_one e0).le⟩
          · exact Or.inr h2
        · exact Or.inr ⟨X, e0 + 1, leWe (X + e0) * g + c', _, Or.inl ⟨rfl, le_rfl⟩,
            RwOwn.succ hshβ he0c hgc hg0 hgT hcond hown, hb', by rw [← add_assoc]; exact e⟩
    · have hg1T := (leTe_SC (S := S) (X + e0 + 1) β).isSuccLimit.succ_lt hgT
      have hg1c := hcode1 _ hgc (hg1T.trans (leTe_lt_Om2 _ _))
      have eT : leTe S (X + e0) (β + leWe (X + e0) * g) = S.psi (β + leWe (X + e0) * (g + 1)) (Om (1 + 1)) := by
        unfold leTe; rw [add_assoc, ← mul_add_one]
      rw [eT] at hge
      refine Or.inr ⟨X, e0 + 1, leWe (X + e0) * (g + 1) + 0, _, Or.inl ⟨rfl, le_rfl⟩,
        rwTop_own hshβ hXW he0c hg1c (add_pos_of_right zero_lt_one g).ne' hg1T, hb', ?_⟩
      rw [add_zero]
      exact le_antisymm (psi_mono (S := S) (InR_Om_succ 1) hhi.le).1 hge
  · obtain ⟨d, rfl⟩ := exists_add_of_le haβ
    have hd : d < leWe (X + e) := by
      by_contra h
      push Not at h
      exact absurd htT (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 h)).1)
    rcases eq_or_ne d 0 with rfl | hd0
    · rw [add_zero]; exact Or.inl le_rfl
    have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
    have hdH : d ∈ cdHull S l := by
      have h1 := leModP_mem (S := S) (Om (1 + 1) * (X + e)) haH
      have hm : (β + d) % ω ^ (Om (1 + 1) * (X + e)) = d := by
        obtain ⟨q, hq⟩ := hβd
        change (β + d) % leWe (X + e) = d
        rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hd]
      rwa [hm] at h1
    set x := log ω d / Om (1 + 1) with hx_def
    have hlogd : log ω d < Om (1 + 1) * (X + e) :=
      (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hd0).trans_lt hd)
    have hxe : x < X + e := (Ordinal.lt_mul_iff_div_lt hW0).1 hlogd
    have hxH : x ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hdH)
    have hdx := roLt_We_log d
    rw [← hx_def] at hdx
    have h0e : (0 : Ordinal.{0}) < e := pos_iff_ne_zero.2 hlim.ne_bot
    obtain ⟨g', hg'c, hg'e, hdg'⟩ : ∃ g', GxCl (upsilon l) (ldAtR S l) g' ∧ g' < e ∧ d < leWe (X + g') := by
      rcases lt_or_ge x X with hxX | hxX
      · refine ⟨0, hc0, h0e, hdx.trans_le (leWe_mono ?_)⟩
        rw [add_zero]; exact Order.add_one_le_of_lt hxX
      · have hxW : x < X + Om (1 + 1) := hxe.trans ((add_lt_add_iff_left X).2 heW)
        have hgm := roModX hs.dvd hxX hxW
        have hgH : x - X ∈ cdHull S l := by rw [← hgm]; exact ldModK_mem ldOm2_SC hxH
        have hge : x - X < e := by
          have : X + (x - X) < X + e := by rwa [Ordinal.add_sub_cancel_of_le hxX]
          exact (add_lt_add_iff_left X).1 this
        have hgc := (ldHull_iff hl hX (hge.trans heW)).1 hgH
        refine ⟨x - X + 1, hcode1 _ hgc ((hlim.succ_lt hge).trans heW), hlim.succ_lt hge, ?_⟩
        rw [← add_assoc, Ordinal.add_sub_cancel_of_le hxX]; exact hdx
    have hle : S.psi (β + d) (Om (1 + 1)) ≤ leTe S (X + g') β :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hdg'.le)).1
    rcases hle.lt_or_eq with hlt | heq
    · rcases IH g' hg'e hg'c (hg'e.trans heW) β hbβ (roBaseE_mono hg'e.le hb') hrd _ ⟨β + d, haH, haA, rfl⟩
        hlt with
        h | ⟨X', e', c, v, hcond, hown, hbo, e1⟩
      · exact Or.inl h
      · refine Or.inr ⟨X', e', c, v, ?_, hown, hbo, e1⟩
        rcases hcond with ⟨h1, h2⟩ | h2
        · exact Or.inl ⟨h1, h2.trans hg'e.le⟩
        · exact Or.inr h2
    · have hg1 := hlim.succ_lt hg'e
      have h1T : (1 : Ordinal.{0}) < leTe S (X + g' + 1) β := roOne_lt_Te _ _
      refine Or.inr ⟨X, g' + 1, leWe (X + g') * 1 + 0, _, Or.inl ⟨rfl, hg1.le⟩,
        rwTop_own hshβ hXW hg'c hc1 one_ne_zero h1T, roBaseE_mono hg1.le hb', ?_⟩
      rw [heq, mul_one, add_zero]; rfl

/-- **The pull-back: `RwClsAt X e` (every code `e`, every base `≥ b`) gives `RwClsAt (X + Ω₂) 0` at every base
`≥ b`.** -/
theorem rwClsW {b X Xh : Ordinal.{0}} (hsh : Sh b X Xh)
    (hcls : ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β, b ≤ β → RoBaseE S l X e β →
      RwRd S l β → RwClsAt S l Sh X e β) :
    ∀ β, b ≤ β → RoBaseE S l (X + Om (1 + 1)) 0 β → RwRd S l β → RwClsAt S l Sh (X + Om (1 + 1)) 0 β := by
  obtain ⟨hs, -⟩ := hSh b X Xh hsh
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hρ0 : 0 < upsilon l := hρSC.1
  have hXW : Om (1 + 1) ≤ X := rwSh_W hs
  have hcode1 : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ + 1 < Om (1 + 1) →
      GxCl (upsilon l) (ldAtR S l) (γ + 1) := fun γ hγ h =>
    (ldHull_iff hl hX h).1 (CSet.succ_mem ((ldHull_iff hl hX ((lt_add_one γ).trans h)).2 hγ))
  have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
  have hc0 : GxCl (upsilon l) (ldAtR S l) (0 : Ordinal.{0}) := GxCl.zero hρ0
  intro β hbβ hb hrd t ht htT
  have hshβ : Sh β X Xh := hShM b β X Xh hbβ hsh
  have hb' := hb
  obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
  rw [add_zero] at hβd hβA hβown htT
  set T := leTe S (X + Om (1 + 1)) β with hT_def
  have hTSC : SC T := leTe_SC _ _
  obtain ⟨a, haH, haA, rfl⟩ := ht
  rcases lt_or_ge a β with haβ | haβ
  · exact Or.inl (psi_mono (S := S) (InR_Om_succ 1) haβ.le).1
  obtain ⟨d, rfl⟩ := exists_add_of_le haβ
  have hd : d < leWe (X + Om (1 + 1)) := by
    by_contra h
    push Not at h
    exact absurd htT (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 h)).1)
  rcases eq_or_ne d 0 with rfl | hd0
  · rw [add_zero]; exact Or.inl le_rfl
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hdH : d ∈ cdHull S l := by
    have h1 := leModP_mem (S := S) (Om (1 + 1) * (X + Om (1 + 1))) haH
    have hm : (β + d) % ω ^ (Om (1 + 1) * (X + Om (1 + 1))) = d := by
      obtain ⟨q, hq⟩ := hβd
      change (β + d) % leWe (X + Om (1 + 1)) = d
      rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hd]
    rwa [hm] at h1
  set x := log ω d / Om (1 + 1) with hx_def
  have hlogd : log ω d < Om (1 + 1) * (X + Om (1 + 1)) :=
    (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hd0).trans_lt hd)
  have hxW : x < X + Om (1 + 1) := (Ordinal.lt_mul_iff_div_lt hW0).1 hlogd
  have hxH : x ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hdH)
  have hdx := roLt_We_log d
  rw [← hx_def] at hdx
  have hWx : leWe x ≤ d := by
    unfold leWe
    exact (opow_le_opow_right omega0_pos (Ordinal.mul_div_le _ _)).trans (opow_log_le_self ω hd0)
  have h0T : (0 : Ordinal.{0}) < T := (Om_pos one_ne_zero).trans (leOm1_lt_Te _ _)
  obtain ⟨g', hg'c, hg'T, hdg'⟩ : ∃ g', GxCl (upsilon l) (ldAtR S l) g' ∧ g' < T ∧ d < leWe (X + g') := by
    rcases lt_or_ge x X with hxX | hxX
    · refine ⟨0, hc0, h0T, hdx.trans_le (leWe_mono ?_)⟩
      rw [add_zero]; exact Order.add_one_le_of_lt hxX
    · have hgm := roModX hs.dvd hxX hxW
      have hgH : x - X ∈ cdHull S l := by rw [← hgm]; exact ldModK_mem ldOm2_SC hxH
      have hgW' : x - X < Om (1 + 1) := by
        have : X + (x - X) < X + Om (1 + 1) := by rwa [Ordinal.add_sub_cancel_of_le hxX]
        exact (add_lt_add_iff_left X).1 this
      have hgc := (ldHull_iff hl hX hgW').1 hgH
      have hgT : x - X < T := by
        by_contra h
        push Not at h
        have h1 := rvTW_ge hs hβown hbβ hβd h
        rw [Ordinal.add_sub_cancel_of_le hxX] at h1
        exact absurd (h1.trans (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hWx)).1)
          (not_le.2 htT)
      refine ⟨x - X + 1, hcode1 _ hgc (ldOm2_SC.isSuccLimit.succ_lt hgW'), hTSC.isSuccLimit.succ_lt hgT, ?_⟩
      rw [← add_assoc, Ordinal.add_sub_cancel_of_le hxX]; exact hdx
  have hg'W : g' < Om (1 + 1) := hg'T.trans (leTe_lt_Om2 _ _)
  have hle : S.psi (β + d) (Om (1 + 1)) ≤ leTe S (X + g') β :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hdg'.le)).1
  rcases hle.lt_or_eq with hlt | heq
  · rcases hcls g' hg'c hg'W β hbβ (rvBaseE_of_W hs hbβ hb' hg'T) hrd _ ⟨β + d, haH, haA, rfl⟩ hlt with
      h | ⟨X', e', c, v, hcond, hown, hbo, e1⟩
    · exact Or.inl h
    · refine Or.inr ⟨X', e', c, v, Or.inr ?_, hown, hbo, e1⟩
      rcases hcond with ⟨rfl, h2⟩ | ⟨h1, h2⟩
      · exact ⟨le_rfl, h2.trans_lt hg'T⟩
      · exact ⟨h1.trans le_self_add, h2⟩
  · have hg1T := hTSC.isSuccLimit.succ_lt hg'T
    have h1T : (1 : Ordinal.{0}) < leTe S (X + g' + 1) β := roOne_lt_Te _ _
    refine Or.inr ⟨X, g' + 1, leWe (X + g') * 1 + 0, _, Or.inr ⟨le_rfl, hg1T⟩,
      rwTop_own hshβ hXW hg'c hc1 one_ne_zero h1T, rvBaseE_of_W hs hbβ hb' hg1T, ?_⟩
    rw [heq, mul_one, add_zero]; rfl

omit hShM in
/-- **The atoms below `T_X(β)` are own at a limit shift**, base by base: every exponent `x < X` of the hull is
below a shift `X'` of the family at `β` with `X' + Ω₂ ≤ X` and its own atoms at `β`. -/
theorem rwClsLimSh {X β : Ordinal.{0}}
    (hup : ∀ x, x ∈ cdHull S l → x < X → ∃ X' Xh', Sh β X' Xh' ∧ X' + Om (1 + 1) ≤ X ∧ x < X' ∧
      (RoBaseE S l X' 0 β → RwRd S l β → RwClsAt S l Sh X' 0 β)) :
    RoBaseE S l X 0 β → RwRd S l β → RwClsAt S l Sh X 0 β := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
  have hc0 : GxCl (upsilon l) (ldAtR S l) (0 : Ordinal.{0}) := GxCl.zero hρSC.1
  intro hb hrd t ht htT
  have hb' := hb
  obtain ⟨hβd, -, -, -, -⟩ := hb
  rw [add_zero] at hβd htT
  obtain ⟨a, haH, haA, rfl⟩ := ht
  rcases lt_or_ge a β with haβ | haβ
  · exact Or.inl (psi_mono (S := S) (InR_Om_succ 1) haβ.le).1
  obtain ⟨d, rfl⟩ := exists_add_of_le haβ
  have hd : d < leWe X := by
    by_contra h
    push Not at h
    exact absurd htT (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 h)).1)
  rcases eq_or_ne d 0 with rfl | hd0
  · rw [add_zero]; exact Or.inl le_rfl
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hdH : d ∈ cdHull S l := by
    have h1 := leModP_mem (S := S) (Om (1 + 1) * X) haH
    have hm : (β + d) % ω ^ (Om (1 + 1) * X) = d := by
      obtain ⟨q, hq⟩ := hβd
      change (β + d) % leWe X = d
      rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hd]
    rwa [hm] at h1
  have hlogd : log ω d < Om (1 + 1) * X :=
    (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hd0).trans_lt hd)
  have hxX : log ω d / Om (1 + 1) < X := (Ordinal.lt_mul_iff_div_lt hW0).1 hlogd
  have hxH : log ω d / Om (1 + 1) ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hdH)
  obtain ⟨X', Xh', hsh', hX'W, hxX', hcls'⟩ := hup _ hxH hxX
  obtain ⟨hs', -⟩ := hSh β X' Xh' hsh'
  have hXW' : Om (1 + 1) ≤ X' := rwSh_W hs'
  have hX'1 : X' + 1 ≤ X :=
    ((add_le_add_iff_left X').2 (one_lt_omega0.trans (Lw.lw_omega_lt_SC ldOm2_SC)).le).trans hX'W
  have hdX' : d < leWe (X' + 0) := by
    rw [add_zero]; exact (roLt_We_log d).trans_le (leWe_mono (Order.add_one_le_of_lt hxX'))
  have hle : S.psi (β + d) (Om (1 + 1)) ≤ leTe S (X' + 0) β :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hdX'.le)).1
  have h0T : (0 : Ordinal.{0}) < leTe S (X' + Om (1 + 1)) β := (Om_pos one_ne_zero).trans (leOm1_lt_Te _ _)
  rcases hle.lt_or_eq with hlt | heq
  · rcases hcls' (roBaseE_shift hb' (by rw [add_zero]; exact le_self_add.trans hX'W) zero_le) hrd _
      ⟨β + d, haH, haA, rfl⟩ hlt with h | ⟨X'', e'', c, v, hcond, hown, hbo, e1⟩
    · exact Or.inl h
    · refine Or.inr ⟨X'', e'', c, v, Or.inr ?_, hown, hbo, e1⟩
      rcases hcond with ⟨rfl, h2⟩ | ⟨h1, h2⟩
      · exact ⟨hX'W, (h2.trans zero_le.ge).trans_lt h0T⟩
      · exact ⟨h1.trans (le_self_add.trans hX'W), h2⟩
  · have h1T : (1 : Ordinal.{0}) < leTe S (X' + 0 + 1) β := roOne_lt_Te _ _
    have h1T' : (0 : Ordinal.{0}) + 1 < leTe S (X' + Om (1 + 1)) β := by
      rw [zero_add]; exact roOne_lt_Te _ _
    refine Or.inr ⟨X', 0 + 1, leWe (X' + 0) * 1 + 0, _, Or.inr ⟨hX'W, h1T'⟩,
      rwTop_own hsh' hXW' hc0 hc1 one_ne_zero h1T,
      roBaseE_shift hb' (by rw [zero_add]; exact hX'1) (by rw [zero_add]), ?_⟩
    rw [heq, mul_one, add_zero, add_zero]; rfl

end Main

end Googology.Trans.PoR.InaccPsi.R2.Rw
