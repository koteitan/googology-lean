import Googology.Trans.PoR.InaccPsi.R2.RnSup

/-!
# The block of a base `β` up to `T_W(β)`, and the top `Θ(T_W(β)) = ψ_{Ω₁}(Â + Ω₁^{Ω₁})` (the pull-back)

`Θ = gxTh ρ_λ (ldAtR λ)` (`= Θ_λ` below `Ω₂`), `W^e = Ω₂^e`, `Ω^x = Ω₁^x` (`Le.leOe`), `T_W(β) = ψ_{Ω₂}(β + W^W)`
(`Rn.rnTW`), `β` a base (`Rn.RnBase`) with `Θ(ψ_{Ω₂}(β)) = ψ_{Ω₁}(Â)`, `Â` own.

* `rnTh_base` (**every atom `t < T_W(β)` is `≤ ψ_{Ω₂}(β)` or `ψ_{Ω₂}(β + c)` with `(e, c, v)` own over `β`
  (`Le.LeOwnH`), `e < T_W(β)`, and `Θ(t) = ψ_{Ω₁}(Â + v)`**: the block law `Le.leOwnRead` at every own exponent,
  which `Rn.rnBaseE` supplies);
* `rnTheta_exp` (`Θ(e) < Ω₁` for the exponents `e < T_W(β)`);
* `rnTopW` (**`Θ(T_W(β)) = ψ_{Ω₁}(Â + Ω₁^{Ω₁})`**: the exponent `W` is not own at `β`, its level-1 image is `Ω₁`;
  "`≤`" from the readings of the atoms below, "`≥`" from `Le.lePsi1_le`: the position of the leading digit of a code
  below `Ω₁^{Ω₁}` is the reading of a code `g < T_W(β)`, and the top `T_{g+1}(β)` is read above it).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The atoms below `T_W(β)` above `ψ_{Ω₂}(β)`, and their readings.** -/
theorem rnTh_base {β Â : Ordinal.{0}} (hb : RnBase S l β) (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hbase : gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1)) :
    ∀ t ∈ ldAtR S l, t < rnTW S β → t ≤ S.psi β (Om (1 + 1)) ∨
      ∃ e c v, e < rnTW S β ∧ LeOwnH S l e β c v ∧ t = S.psi (β + c) (Om (1 + 1)) ∧
        gxTh (upsilon l) (ldAtR S l) t = S.psi (Â + v) (Om 1) ∧
        Â + v ∈ S.CSet (Â + v) (S.psi (Â + v) (Om 1)) ∧
        v < leOe (gxTh (upsilon l) (ldAtR S l) e) ∧ c < leWe e := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hb' := hb
  obtain ⟨hβd, -, -, hβown⟩ := hb
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  intro t ht htT
  obtain ⟨a, haH, haA, rfl⟩ := ht
  rcases lt_or_ge a β with haβ | haβ
  · exact Or.inl (psi_mono (S := S) (InR_Om_succ 1) haβ.le).1
  obtain ⟨d, rfl⟩ := exists_add_of_le haβ
  rcases eq_or_ne d 0 with rfl | hd0
  · rw [add_zero]; exact Or.inl le_rfl
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
  have hdE : d < leWe E := by
    unfold leWe
    calc d < ω ^ (log ω d + 1) := by
          rw [← Order.succ_eq_add_one]; exact lt_opow_succ_log_self one_lt_omega0 d
      _ ≤ ω ^ (Om (1 + 1) * E) := by
          refine opow_le_opow_right omega0_pos (Order.add_one_le_of_lt ?_)
          rw [hE_def, mul_add_one]; exact Ordinal.lt_mul_div_add _ hW0
  have hle : S.psi (β + d) (Om (1 + 1)) ≤ leTe S E β := by
    unfold leTe; exact (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hdE.le)).1
  have hrep : S.psi (β + d) (Om (1 + 1)) ≤ S.psi β (Om (1 + 1)) ∨ ∃ e c v, e < rnTW S β ∧
      LeOwnH S l e β c v ∧ S.psi (β + d) (Om (1 + 1)) = S.psi (β + c) (Om (1 + 1)) := by
    rcases hle.lt_or_eq with hlt | heq
    · rcases leClsE hl hX E hEc le_add_self β (rnBaseE hb' hET) _ ⟨β + d, haH, haA, rfl⟩ hlt with
        h0 | ⟨e', c, v, he', hown, e⟩
      · exact Or.inl h0
      · exact Or.inr ⟨e', c, v, he'.trans_lt hET, hown, e⟩
    · have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
      have h1T : (1 : Ordinal.{0}) < leTe S (E + 1) β :=
        (one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1)).trans (leOm1_lt_Te _ _)
      refine Or.inr ⟨E + 1, leWe E * 1 + 0, _, (rnTW_SC β).isSuccLimit.succ_lt hET,
        LeOwnH.succ hEc le_add_self hc1 one_ne_zero h1T zero_le LeOwnH.zero, ?_⟩
      rw [heq, mul_one, add_zero]; rfl
  rcases hrep with h | ⟨e, c, v, heT, hown, he⟩
  · exact Or.inl h
  obtain ⟨e1, own, hv, hc⟩ := leOwnRead hl hX hown Â (rnBaseE hb' heT) hÂ hbase
  exact Or.inr ⟨e, c, v, heT, hown, he, by rw [he]; exact e1, own, hv, hc⟩

/-- `Θ(e) < Ω₁` for the exponents `e < T_W(β)` of the own arguments. -/
theorem rnTheta_exp {β Â e c v : Ordinal.{0}} (hb : RnBase S l β) (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hbase : gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1))
    (heT : e < rnTW S β) (hown : LeOwnH S l e β c v) : gxTh (upsilon l) (ldAtR S l) e < Om 1 := by
  rcases eq_or_ne e 0 with rfl | he0
  · rw [gxTh_zero]; exact Om_pos one_ne_zero
  have hec := leOwnH_code hl hX hown (heT.trans (rnTW_lt_Om2 β))
  have hT := leTopE hl hX e hec (Order.one_le_iff_ne_zero.2 he0) β Â (rnBaseE hb heT) hÂ hbase
  have heT' : e < leTe S e β := by unfold leTe; exact rnTW_gt hb.2.2.2 hb.1 heT
  refine (gxTh_lt hec heT').trans ?_
  rw [hT]; exact psi_lt Low.InR_Om_one _

/-- **The top of exponent `W`: `Θ(T_W(β)) = ψ_{Ω₁}(Â + Ω₁^{Ω₁})`.** -/
theorem rnTopW {β Â : Ordinal.{0}} (hb : RnBase S l β) (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hbase : gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1)) :
    gxTh (upsilon l) (ldAtR S l) (rnTW S β) = S.psi (Â + leOe (Om 1)) (Om 1) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  have hb' := hb
  obtain ⟨hβd, hβH, hβA, hβown⟩ := hb
  have hΘsucc : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ →
      gxTh (upsilon l) (ldAtR S l) (γ + 1) = gxTh (upsilon l) (ldAtR S l) γ + 1 := fun γ hγ => by
    rw [gxTh_add hρSC hAt hγ 1, hΘ1]
  have hcode1 : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ + 1 < Om (1 + 1) →
      GxCl (upsilon l) (ldAtR S l) (γ + 1) := fun γ hγ h =>
    (ldHull_iff hl hX h).1 (CSet.succ_mem ((ldHull_iff hl hX ((lt_add_one γ).trans h)).2 hγ))
  have hβat := rnBase_atom hb'
  have hρÂ : upsilon l < S.psi Â (Om 1) := by
    rw [← hbase]; exact (ldAtom_ge hρSC hρ1 hAt hβat).2.1
  set X := S.psi (Â + leOe (Om 1)) (Om 1) with hX_def
  have hÂX : Â ∈ S.CSet (Â + leOe (Om 1)) X := (psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ
  have hÂlt : S.psi Â (Om 1) < X :=
    psi_lt_psi_of_mem Low.InR_Om_one (lt_add_of_pos_right Â (leOe_pos _)) hÂX
  have htop := rnTW_atom hb'
  have hup : gxTh (upsilon l) (ldAtR S l) (rnTW S β) ≤ X := by
    refine ldAtom_le hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) (hρÂ.trans hÂlt) ?_
    intro t ht hts
    rcases rnTh_base hl hX hb' hÂ hbase t ht hts with h | ⟨e, c, v, heT, hown, -, hth, hownv, hv, -⟩
    · exact (gxTh_mono h).trans_lt (by rw [hbase]; exact hÂlt)
    have hΘe := rnTheta_exp hl hX hb' hÂ hbase heT hown
    have hvO : v < leOe (Om 1) := hv.trans (leOe_lt hΘe)
    have hlt : Â + v < Â + leOe (Om 1) := (add_lt_add_iff_left Â).2 hvO
    rw [hth]
    refine psi_lt_psi_of_mem Low.InR_Om_one hlt ?_
    exact CSet_mono hlt.le (psi_mono (S := S) Low.InR_Om_one hlt.le).1 hownv
  apply le_antisymm hup
  obtain ⟨hTSC, -, hTs⟩ := ldAtom_ge hρSC hρ1 hAt htop
  have hβs := rnBase_lt hb'
  refine lePsi1_le hTSC fun x hx hc => ?_
  rcases le_or_gt x Â with hxÂ | hxÂ
  · refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one hxÂ).1 ?_
    rw [← hbase]; exact hTs _ hβat hβs
  obtain ⟨r, rfl⟩ := exists_add_of_le hxÂ.le
  have hr : r < leOe (Om 1) := (add_lt_add_iff_left Â).1 hx
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hΩG1 : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
  have hc2 := LeCl.mod hTSC.1 Ph.ph_SC_Om1.isPrincipal (Om 1 * Om 1) hc
  change LeCl (Om 1) _ ((Â + r) % S.psi 0 (Om (1 + 1)) % leOe (Om 1)) at hc2
  rw [Ordinal.mod_mod_of_dvd _ (leOe_lt_SC hG1 hΩG1 hΩG1).2] at hc2
  have hmod : (Â + r) % leOe (Om 1) = Â % leOe (Om 1) + r := leMod_add_lt _ Â hr
  rw [hmod] at hc2
  set y := Â % leOe (Om 1) + r with hy_def
  have hyP : y < leOe (Om 1) := isPrincipal_add_omega0_opow _ (Ordinal.mod_lt Â (leOe_pos _).ne') hr
  have hry : r ≤ y := le_add_self
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [add_zero, ← hbase]; exact hTs _ hβat hβs
  have hy0 : y ≠ 0 := fun h => hr0 (le_antisymm (h ▸ hry) zero_le)
  have hlogy : log ω y < Om 1 * Om 1 :=
    (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hy0).trans_lt hyP)
  have hlogC := (leClDec hTSC Ph.ph_SC_Om1 y hc2).2
  have hbd := leCl_boundK hTSC Ph.ph_SC_Om1 _ hlogC hlogy
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  have hδT := (Ordinal.lt_mul_iff_div_lt hΩ0).1 hbd
  obtain ⟨g, hgc, hgT, hgx⟩ := gxTh_onto hδT
  have hg1T : g + 1 < rnTW S β := (rnTW_SC β).isSuccLimit.succ_lt hgT
  have hg1W : g + 1 < Om (1 + 1) := hg1T.trans (rnTW_lt_Om2 β)
  have hg1c := hcode1 g hgc hg1W
  have hg1H : g + 1 ∈ cdHull S l := (ldHull_iff hl hX hg1W).2 hg1c
  have hyg : y < leOe (gxTh (upsilon l) (ldAtR S l) (g + 1)) := by
    rw [hΘsucc g hgc, hgx]
    unfold leOe
    calc y < ω ^ (log ω y + 1) := by
          rw [← Order.succ_eq_add_one]; exact lt_opow_succ_log_self one_lt_omega0 y
      _ ≤ ω ^ (Om 1 * (log ω y / Om 1 + 1)) := by
          refine opow_le_opow_right omega0_pos (Order.add_one_le_of_lt ?_)
          rw [mul_add_one]; exact Ordinal.lt_mul_div_add _ hΩ0
  have e1 := leTopE hl hX (g + 1) hg1c le_add_self β Â (rnBaseE hb' hg1T) hÂ hbase
  have hlt : β + leWe (g + 1) < β + leWe (Om (1 + 1)) := (add_lt_add_iff_left β).2 (leWe_lt hg1W)
  have hat1 : leTe S (g + 1) β ∈ ldAtR S l :=
    ⟨β + leWe (g + 1), CSet.add_mem hβH (leWe_mem hg1H), hlt.trans hβA, rfl⟩
  have hlt1 : leTe S (g + 1) β < rnTW S β := by
    refine psi_lt_psi_of_mem (InR_Om_succ 1) hlt (CSet.add_mem (hβown _ le_rfl) (leWe_mem (CSet.of_lt ?_)))
    exact hg1T
  refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one
    ((add_le_add_iff_left Â).2 (hry.trans hyg.le))).1 ?_
  rw [← e1]
  exact hTs _ hat1 hlt1

end Main

end Googology.Trans.PoR.InaccPsi.R2.Rn
