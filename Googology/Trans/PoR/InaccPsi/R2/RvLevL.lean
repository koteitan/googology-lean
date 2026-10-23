import Googology.Trans.PoR.InaccPsi.R2.RvSE

/-!
# The top law at `X₀ + Ω₂^e` for every level `1 ≤ e < ρ_λ`, and at `Ω₂^e` over `0`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E` (`Le.leWe`), `Ω^x = Ω₁^x` (`Le.leOe`), `T_E(β) = ψ_{Ω₂}(β + W^E)`.

* `rvShLev` (`(X₀ + W^e, X̂₀ + Ω^e)` is a shift own relative to `b` for an offset over `b`);
* `rvLevE_one` (`e = 1`), `rvLevE_lim` (**limit levels**: `RvLevSE e'` for all `1 ≤ e' < e` gives `RvLevSE e`),
  `rvLevE_all` (**`RvLevSE e` for every `1 ≤ e < ρ_λ`**, one induction on `e` with `Rv.rvLevE_succ`);
* `rvTopLev` (**`RoTop (Ω₂^e) (Ω₁^e) 0` for every `1 ≤ e < ρ_λ`**), `rvTh_e0`
  (**`Θ_λ(ψ_{Ω₂}(Ω₂^{Ω₂^e})) = ψ_{Ω₁}(A + 1 + Ω₁^{Ω₁^e})`**).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq

variable {S : InaccSeq.{0}}

theorem rvLim_one_lt {e : Ordinal.{0}} (hlim : IsSuccLimit e) : (1 : Ordinal.{0}) < e := by
  have := hlim.succ_lt (pos_iff_ne_zero.2 hlim.ne_bot); rwa [succ_eq_add_one, zero_add] at this

/-- Every `r < Ω₂^e` (`e` a limit) is below some `Ω₂^{e'}`, `1 ≤ e' < e`. -/
theorem rvLt_We_lim {e r : Ordinal.{0}} (hlim : IsSuccLimit e) (hr : r < leWe e) :
    ∃ e', 1 ≤ e' ∧ e' < e ∧ r < leWe e' := by
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  rcases eq_or_ne r 0 with rfl | hr0
  · exact ⟨1, le_rfl, (rvLim_one_lt hlim), leWe_pos 1⟩
  have hlog : log ω r < Om (1 + 1) * e :=
    (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hr0).trans_lt hr)
  have hm : log ω r / Om (1 + 1) < e := (Ordinal.lt_mul_iff_div_lt hW0).1 hlog
  exact ⟨_, le_add_self, hlim.succ_lt hm, roLt_We_log r⟩

/-- Every `u < Ω^e` (`e` a limit) is below some `Ω^{e'}`, `1 ≤ e' < e`. -/
theorem rvLt_Oe_lim {e u : Ordinal.{0}} (hlim : IsSuccLimit e) (hu : u < leOe e) :
    ∃ e', 1 ≤ e' ∧ e' < e ∧ u < leOe e' := by
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  rcases eq_or_ne u 0 with rfl | hu0
  · exact ⟨1, le_rfl, (rvLim_one_lt hlim), leOe_pos 1⟩
  have hlog : log ω u < Om 1 * e :=
    (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hu0).trans_lt hu)
  have hm : log ω u / Om 1 < e := (Ordinal.lt_mul_iff_div_lt hΩ0).1 hlog
  exact ⟨_, le_add_self, hlim.succ_lt hm, roLt_Oe_log u⟩

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`(X₀ + W^e, X̂₀ + Ω^e)` is a shift own relative to `b`** for an offset over `b`, `1 ≤ e < ρ_λ`. -/
theorem rvShLev {b X0 Xh0 e : Ordinal.{0}} (hoff : RvOff S l b X0 Xh0) (he1 : 1 ≤ e) (heρ : e < upsilon l)
    (hG3 : X0 + leWe e + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)))
    (hG : Xh0 + leOe e + Om 1 < S.psi 0 (Om (1 + 1))) :
    RvSh S l b (X0 + leWe e) (Xh0 + leOe e) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  obtain ⟨hd, hH, hm, hmh, hcl, hclh⟩ := rvOff_data hoff
  have heΩ : e < Om 1 := heρ.trans hρ1
  have heH : e ∈ cdHull S l := (ldHull_iff hl hX (heΩ.trans gg_Om1_lt_Om2)).2 (GxCl.small heρ)
  have hle : S.psi (b + leWe X0) (Om (1 + 1)) ≤ S.psi (b + leWe (X0 + leWe e)) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left b).2 (leWe_mono le_self_add))).1
  have hρT : upsilon l < gxTh (upsilon l) (ldAtR S l) (S.psi (b + leWe (X0 + leWe e)) (Om (1 + 1))) := by
    have h := gxTh_lt (Z := upsilon l) (At := ldAtR S l) GxCl.om (psiS_bounds (S := S) (b + leWe (X0 + leWe e)) 1).1
    rwa [gxTh_Om1 hρSC hρ1 hAt] at h
  have hWe : Om (1 + 1) ∣ leWe e := by have h := leWe_dvd he1; rwa [leWe_one] at h
  refine ⟨fun h => (leWe_pos e).ne' (le_antisymm (h ▸ le_add_self) zero_le), dvd_add hd hWe,
    CSet.add_mem hH (leWe_mem heH), CSet.add_mem (CSet_mono le_rfl hle hm) (leWe_mem (rvE_mem heΩ)),
    CSet.add_mem (CSet_mono le_rfl (gxTh_mono hle) hmh) (leOe_mem (CSet.of_lt (heρ.trans hρT))), hG3, hG,
    fun Q hQ hb => LeCl.add (hcl Q hQ (hle.trans hb)) (LeCl.opow hQ.1 (LeCl.mulK hQ ldOm2_SC e
      (LeCl.small ((heΩ.trans (psiS_bounds (S := S) _ 1).1).trans_le hb)))),
    fun Q hQ hb => LeCl.add (hclh Q hQ ((gxTh_mono hle).trans hb)) (LeCl.opow hQ.1 (LeCl.mulK hQ Ph.ph_SC_Om1 e
      (LeCl.small ((heρ.trans hρT).trans_le hb))))⟩

/-- **Level `1`.** -/
theorem rvLevE_one : RvLevSE S l 1 := by
  intro b X0 Xh0 hoff _ _ _
  rw [leWe_one, leOe_one]
  rcases hoff with ⟨rfl, rfl⟩ | ⟨hs, ht⟩
  · have h := roTop_one (S := S) hl hX
    rw [Nat.cast_one, mul_one, mul_one] at h
    rw [zero_add, zero_add]; exact rvTop_of_ro h
  · exact rvTopW hs hl hX (rvTopE hs hl hX ht)

/-- **Limit levels.** -/
theorem rvLevE_lim {e : Ordinal.{0}} (hlim : IsSuccLimit e) (heρ : e < upsilon l)
    (IH : ∀ e', 1 ≤ e' → e' < e → RvLevSE S l e') : RvLevSE S l e := by
  intro b X0 Xh0 hoff hd hG3 hG
  have he1 : 1 ≤ e := (rvLim_one_lt hlim).le
  have hs := rvShLev hl hX hoff he1 heρ hG3 hG
  have hsub : ∀ e', 1 ≤ e' → e' < e →
      RvSh S l b (X0 + leWe e') (Xh0 + leOe e') ∧ RvTop S l b (X0 + leWe e') (Xh0 + leOe e') 0 := by
    intro e' h1 he'
    have hle1 : X0 + leWe e' + Om (1 + 1) ≤ X0 + leWe e + Om (1 + 1) :=
      add_le_add_left ((add_le_add_iff_left X0).2 (leWe_mono he'.le)) _
    have hle2 : Xh0 + leOe e' + Om 1 ≤ Xh0 + leOe e + Om 1 :=
      add_le_add_left ((add_le_add_iff_left Xh0).2 (leOe_mono he'.le)) _
    exact ⟨rvShLev hl hX hoff h1 (he'.trans heρ) (hle1.trans_lt hG3) (hle2.trans_lt hG),
      IH e' h1 he' b X0 Xh0 hoff ((leWe_dvd he'.le).trans hd) (hle1.trans_lt hG3) (hle2.trans_lt hG)⟩
  refine rvTopLimSh hl hX hs (fun x _ hx => ?_) (fun z hz => ?_)
  · rcases lt_or_ge x X0 with hxX | hxX
    · obtain ⟨hs0, ht0⟩ := rvOff_ne hoff (zero_le.trans_lt hxX).ne'
      exact ⟨X0, Xh0, le_self_add, hxX, lt_add_of_pos_right _ (leOe_pos e), hs0, ht0⟩
    · obtain ⟨r, rfl⟩ := exists_add_of_le hxX
      have hr : r < leWe e := (add_lt_add_iff_left X0).1 hx
      obtain ⟨e', h1, he', hre'⟩ := rvLt_We_lim hlim hr
      obtain ⟨hs1, ht1⟩ := hsub e' h1 he'
      exact ⟨_, _, (add_le_add_iff_left X0).2 (leWe_mono he'.le), (add_lt_add_iff_left X0).2 hre',
        (add_lt_add_iff_left Xh0).2 (leOe_lt he'), hs1, ht1⟩
  · rcases lt_or_ge z Xh0 with hzX | hzX
    · obtain ⟨hs0, ht0⟩ := rvOff_neh hoff (zero_le.trans_lt hzX).ne'
      exact ⟨X0, Xh0, lt_add_of_pos_right _ (leWe_pos e), hzX, hs0, ht0⟩
    · obtain ⟨u, rfl⟩ := exists_add_of_le hzX
      have hu : u < leOe e := (add_lt_add_iff_left Xh0).1 hz
      obtain ⟨e', h1, he', hue'⟩ := rvLt_Oe_lim hlim hu
      obtain ⟨hs1, ht1⟩ := hsub e' h1 he'
      exact ⟨_, _, (add_lt_add_iff_left X0).2 (leWe_lt he'), (add_lt_add_iff_left Xh0).2 hue', hs1, ht1⟩

/-- **`RvLevSE e` for every level `1 ≤ e < ρ_λ`.** -/
theorem rvLevE_all : ∀ e, 1 ≤ e → e < upsilon l → RvLevSE S l e := by
  intro e
  induction e using WellFoundedLT.induction with
  | ind e IH =>
  intro he1 heρ
  rcases zero_or_succ_or_isSuccLimit e with h0 | ⟨e0, he0⟩ | hlim
  · subst h0; exact absurd he1 (by simp)
  · rw [succ_eq_add_one] at he0
    subst he0
    rcases eq_or_ne e0 0 with rfl | h00
    · rw [zero_add]; exact rvLevE_one hl hX
    · have h10 : 1 ≤ e0 := Order.one_le_iff_ne_zero.2 h00
      have he0ρ : e0 < upsilon l := (lt_add_one e0).trans heρ
      exact rvLevE_succ hl hX h10 he0ρ (IH e0 (lt_add_one e0) h10 he0ρ)
  · exact rvLevE_lim hl hX hlim heρ (fun e' h1 he' => IH e' he' h1 (he'.trans heρ))

/-- **`RoTop (Ω₂^e) (Ω₁^e) 0` for every `1 ≤ e < ρ_λ`.** -/
theorem rvTopLev {e : Ordinal.{0}} (he1 : 1 ≤ e) (heρ : e < upsilon l) : RoTop S l (leWe e) (leOe e) 0 := by
  obtain ⟨-, hρ1⟩ := leRho hl hX
  have heΩ : e < Om 1 := heρ.trans hρ1
  have hG3 : SC (S.psi 0 (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) 0
  have hWG3 : Om (1 + 1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (psiS_bounds (S := S) 0 (1 + 1)).1
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hΩG1 : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
  have h := rvLevE_all hl hX e he1 heρ 0 0 0 (Or.inl ⟨rfl, rfl⟩) (dvd_zero _)
    (by rw [zero_add]; exact hG3.isPrincipal (leWe_lt_SC hG3 hWG3 ((heΩ.trans gg_Om1_lt_Om2).trans hWG3)).1 hWG3)
    (by rw [zero_add]; exact hG1.isPrincipal (leOe_lt_SC hG1 hΩG1 (heΩ.trans hΩG1)).1 hΩG1)
  rw [zero_add, zero_add] at h
  exact rvTop_zero h

/-- **`Θ_λ(ψ_{Ω₂}(Ω₂^{Ω₂^e})) = ψ_{Ω₁}(A + 1 + Ω₁^{Ω₁^e})`** for every `1 ≤ e < ρ_λ`. -/
theorem rvTh_e0 {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    {e : Ordinal.{0}} (he1 : 1 ≤ e) (heρ : e < upsilon l) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (leWe e)) (Om (1 + 1))) =
      S.psi (A + 1 + leOe (leOe e)) (Om 1) := by
  obtain ⟨-, hρ1⟩ := leRho hl hX
  have hA1 : A + 1 ∈ S.CSet (A + 1) (S.psi (A + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) (CSet.one_mem _ _)
  have heW : e < Om ω := (heρ.trans hρ1).trans (gg_Om1_lt_Om2.trans ldOm2_lt_OmW)
  have hb : RoBaseE S l (leWe e) 0 0 := by
    refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
    · rw [zero_add, add_zero]; exact (roWe_lt_OmW (roWe_lt_OmW heW)).trans_le le_self_add
    · obtain rfl : e' = 0 := le_antisymm h' zero_le
      exact (SC_psi (InR_Om_succ 1) _).1
  have h := rvTopLev hl hX he1 heρ 0 (A + 1) hb hA1 (ldBlk_zero hA hρ)
  unfold leTe at h
  rwa [zero_add, add_zero, gxTh_zero, add_zero] at h

end Main

end Googology.Trans.PoR.InaccPsi.R2.Rv
