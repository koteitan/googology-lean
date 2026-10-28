import Googology.Trans.PoR.InaccPsi.R2.VkCst

/-!
# Every code level `1 ≤ E < Ω₂` over every offset, with no bound

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`,
`EX_j = Rw.rwEX S X₀ b j` (`EX_0 = Ω₁`, `EX_{j+1} = T_{X₀ + W^{EX_j}}(b)`), `Ow_E` the own predicate
`∃ j, E < EX_j(X₀, b)` of a code `E`.

* `vkSh_own` (**`X₀ + W^E` is a shift `VkSh` for every own exponent `E`** of any level);
* `vkOwP_code` (the own predicate of a code has the data, image `Θ E`), `vkLev_codeLim` (**the limit code level**),
  `vkLev_code` (**`VkLev Ow_E E (Θ E)` for every code `1 ≤ E < Ω₂`**: `Θ(T_{X₀ + W^E}(β)) = ψ_{Ω₁}(Â + Ω^{X̂₀ +
  Ω^{Θ E}})` at every offset `X₀` with `E < EX_j(X₀, b)`, `W^E ∣ X₀`; no bound on `X₀`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Sc
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Ua Googology.Trans.PoR.InaccPsi.R2.Uj

variable {S : InaccSeq.{0}}

/-- **`X₀ + W^E` is a shift `VkSh` for every own exponent `E`** (any level). -/
theorem vkSh_own {l b X0 Xh0 E Eh : Ordinal.{0}} (hoff : VkOff S l b X0 Xh0) (hEo : VkOwnE S l b X0 E Eh) :
    VkSh S l b (X0 + leWe E) (Xh0 + leOe Eh) := by
  obtain ⟨hd, hH, hm, hmh, hcl, hclh⟩ := vkOff_data hoff
  have h2 : (1 + 1 : Ordinal.{0}) ≠ 0 := by rw [one_add_one_eq_two]; exact two_ne_zero
  have hle : S.psi (b + leWe X0) (Om (1 + 1)) ≤ S.psi (b + leWe (X0 + leWe E)) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left b).2 (leWe_mono le_self_add))).1
  have hEa : E ≤ X0 + leWe E := (ujLe_We E).trans le_add_self
  have hEha : Eh ≤ Xh0 + leOe Eh := (ujLe_Oe Eh).trans le_add_self
  have hWd : Om (1 + 1) ∣ leWe E := by have h := leWe_dvd hEo.one; rwa [leWe_one] at h
  refine ⟨fun h => (leWe_pos E).ne' (le_antisymm (h ▸ le_add_self) zero_le), dvd_add hd hWd,
    CSet.add_mem hH (leWe_mem hEo.hull),
    CSet.add_mem (CSet_mono le_self_add hle hm) (leWe_mem (CSet_mono hEa le_rfl hEo.mem)),
    CSet.add_mem (CSet_mono le_self_add (gxTh_mono hle) hmh) (leOe_mem (CSet_mono hEha le_rfl hEo.memh)),
    fun Q hQ hb => ?_, fun Q hQ hb => ?_⟩
  · exact VkA.add (hcl Q hQ (hle.trans hb)) (VkA.opow hQ.1 (vkA_mulK hQ h2 E (hEo.cl Q hQ hb)))
  · exact VkA.add (hclh Q hQ ((gxTh_mono hle).trans hb))
      (VkA.opow hQ.1 (vkA_mulK hQ one_ne_zero Eh (hEo.clh Q hQ hb)))

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The own predicate of a code has the data** (image `Θ E`). -/
theorem vkOwP_code {E : Ordinal.{0}} (he1 : 1 ≤ E) (hE : GxCl (upsilon l) (ldAtR S l) E) (hEW : E < Om (1 + 1)) :
    VkOwP S l (fun b X0 => ∃ j, E < rwEX S X0 b j) E (gxTh (upsilon l) (ldAtR S l) E) := by
  refine ⟨fun b X0 hEX => ?_, fun _ _ _ _ ⟨j, hj⟩ hb hX0 =>
    ⟨j, (hj.trans_le (rwEX_mono_base hb j)).trans_le (rwEX_mono_off hX0 j)⟩⟩
  obtain ⟨j, hj⟩ := hEX
  have hEo := rwEX_gt j E hj
  have hΘo := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hE hEo
  exact ⟨he1, (ldHull_iff hl hX hEW).2 hE, CSet.of_lt hEo, CSet.of_lt hΘo,
    fun Q _ hY => VkA.small (hEo.trans_le hY), fun Q _ hY => VkA.small (hΘo.trans_le hY)⟩

/-- **THE LIMIT CODE LEVEL**: a limit code `L < Ω₂` whose smaller code levels have the level statement has it. -/
theorem vkLev_codeLim {L : Ordinal.{0}} (hlim : IsSuccLimit L) (hL : GxCl (upsilon l) (ldAtR S l) L)
    (hLW : L < Om (1 + 1))
    (IH : ∀ E, GxCl (upsilon l) (ldAtR S l) E → 1 ≤ E → E < L →
      VkLev S l (fun b X0 => ∃ j, E < rwEX S X0 b j) E (gxTh (upsilon l) (ldAtR S l) E)) :
    VkLev S l (fun b X0 => ∃ j, L < rwEX S X0 b j) L (gxTh (upsilon l) (ldAtR S l) L) := by
  intro b X0 Xh0 hoff hd hLX
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  have h1L : (1 : Ordinal.{0}) < L := rvLim_one_lt hlim
  have hρ0 : 0 < upsilon l := (leRho hl hX).1.1
  have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := by
    have h := rqCode_succ hl hX (GxCl.zero hρ0) (by rw [zero_add]; exact gg_one_lt_of_SC ldOm2_SC)
    rwa [zero_add] at h
  set ΘL := gxTh (upsilon l) (ldAtR S l) L with hΘL_def
  -- every smaller code level gives a shift with its top
  have hsub : ∀ E, GxCl (upsilon l) (ldAtR S l) E → 1 ≤ E → E < L →
      VkSh S l b (X0 + leWe E) (Xh0 + leOe (gxTh (upsilon l) (ldAtR S l) E)) ∧
      RvTop S l b (X0 + leWe E) (Xh0 + leOe (gxTh (upsilon l) (ldAtR S l) E)) 0 ∧
      gxTh (upsilon l) (ldAtR S l) E < ΘL := by
    intro E hE h1 hEL
    have hΘlt : gxTh (upsilon l) (ldAtR S l) E < ΘL := gxTh_lt hE hEL
    have hEX : ∃ j, E < rwEX S X0 b j := by obtain ⟨j, hj⟩ := hLX; exact ⟨j, hEL.trans hj⟩
    have hP := vkOwP_code hl hX h1 hE (hEL.trans hLW)
    exact ⟨vkSh_own hoff (hP.dat b X0 hEX),
      IH E hE h1 hEL b X0 Xh0 hoff ((leWe_dvd hEL.le).trans hd) hEX, hΘlt⟩
  have hPL := vkOwP_code hl hX h1L.le hL hLW
  refine vkTopLimSh hl hX (vkSh_own hoff (hPL.dat b X0 hLX)) (fun x hxH hx => ?_) (fun z hz => ?_)
  · obtain ⟨E, hEc, h1E, hEL, hxE⟩ : ∃ E, GxCl (upsilon l) (ldAtR S l) E ∧ 1 ≤ E ∧ E < L ∧
        x < X0 + leWe E := by
      rcases lt_or_ge x X0 with hxX | hxX
      · exact ⟨1, hc1, le_rfl, h1L, hxX.trans_le le_self_add⟩
      obtain ⟨y, rfl⟩ := exists_add_of_le hxX
      have hy : y < leWe L := (add_lt_add_iff_left X0).1 hx
      rcases eq_or_ne y 0 with rfl | hy0
      · exact ⟨1, hc1, le_rfl, h1L, by rw [add_zero]; exact lt_add_of_pos_right _ (leWe_pos 1)⟩
      have hyH : y ∈ cdHull S l := by
        have h1 := leModP_mem (S := S) (Om (1 + 1) * L) hxH
        have hm : (X0 + y) % ω ^ (Om (1 + 1) * L) = y := by
          obtain ⟨q, hq⟩ := hd
          change (X0 + y) % leWe L = y
          rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hy]
        rwa [hm] at h1
      have hlogd : log ω y < Om (1 + 1) * L :=
        (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hy0).trans_lt hy)
      have hq : log ω y / Om (1 + 1) < L := (Ordinal.lt_mul_iff_div_lt hW0).1 hlogd
      have hqH : log ω y / Om (1 + 1) ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hyH)
      have hqc := (ldHull_iff hl hX (hq.trans hLW)).1 hqH
      exact ⟨log ω y / Om (1 + 1) + 1, rqCode_succ hl hX hqc ((hlim.succ_lt hq).trans hLW), le_add_self,
        hlim.succ_lt hq, (add_lt_add_iff_left X0).2 (roLt_We_log y)⟩
    obtain ⟨hs1, ht1, hΘ1⟩ := hsub E hEc h1E hEL
    exact ⟨_, _, (add_le_add_iff_left X0).2 (leWe_mono hEL.le), hxE,
      (add_lt_add_iff_left Xh0).2 (leOe_lt hΘ1), hs1, ht1⟩
  · obtain ⟨E, hEc, h1E, hEL, hzE⟩ : ∃ E, GxCl (upsilon l) (ldAtR S l) E ∧ 1 ≤ E ∧ E < L ∧
        z < Xh0 + leOe (gxTh (upsilon l) (ldAtR S l) E) := by
      have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC (leRho hl hX).1).le
      rcases lt_or_ge z Xh0 with hzX | hzX
      · exact ⟨1, hc1, le_rfl, h1L, hzX.trans_le le_self_add⟩
      obtain ⟨r, rfl⟩ := exists_add_of_le hzX
      have hr : r < leOe ΘL := (add_lt_add_iff_left Xh0).1 hz
      rcases eq_or_ne r 0 with rfl | hr0
      · exact ⟨1, hc1, le_rfl, h1L, by rw [add_zero, hΘ1]; exact lt_add_of_pos_right _ (leOe_pos 1)⟩
      have hlogr : log ω r < Om 1 * ΘL :=
        (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hr0).trans_lt hr)
      have hq : log ω r / Om 1 < ΘL := (Ordinal.lt_mul_iff_div_lt hΩ0).1 hlogr
      obtain ⟨c, hc, hcL, hcz⟩ := gxTh_onto hq
      refine ⟨c + 1, rqCode_succ hl hX hc ((hlim.succ_lt hcL).trans hLW), le_add_self, hlim.succ_lt hcL, ?_⟩
      rw [rqTh_succ hl hX hc, hcz]
      exact (add_lt_add_iff_left Xh0).2 (roLt_Oe_log r)
    obtain ⟨hs1, ht1, -⟩ := hsub E hEc h1E hEL
    exact ⟨_, _, (add_lt_add_iff_left X0).2 (leWe_lt hEL), hzE, hs1, ht1⟩

/-- **`VkLev Ow_E E (Θ E)` for every code `1 ≤ E < Ω₂`**: every code level over every offset (no bound). -/
theorem vkLev_code : ∀ E, GxCl (upsilon l) (ldAtR S l) E → 1 ≤ E → E < Om (1 + 1) →
    VkLev S l (fun b X0 => ∃ j, E < rwEX S X0 b j) E (gxTh (upsilon l) (ldAtR S l) E) := by
  intro E
  induction E using WellFoundedLT.induction with
  | ind E IH =>
  intro hE h1 hEW
  rcases zero_or_succ_or_isSuccLimit E with h0 | ⟨E0, hE0⟩ | hlim
  · subst h0; exact absurd h1 (by simp)
  · rw [succ_eq_add_one] at hE0
    subst hE0
    have hE0c := rqCode_pred hl hX hE hEW
    rw [rqTh_succ hl hX hE0c]
    rcases eq_or_ne E0 0 with rfl | h00
    · have hΘ0 : gxTh (upsilon l) (ldAtR S l) (0 : Ordinal.{0}) = 0 := gxTh_zero
      rw [zero_add, hΘ0, zero_add]
      intro b X0 Xh0 hoff hd _
      exact vkLev_one hl hX b X0 Xh0 hoff hd trivial
    have h10 : 1 ≤ E0 := Order.one_le_iff_ne_zero.2 h00
    have hE0W : E0 < Om (1 + 1) := (lt_add_one E0).trans hEW
    exact vkLev_succ hl hX (vkOwP_code hl hX h10 hE0c hE0W) (IH E0 (lt_add_one E0) hE0c h10 hE0W)
      (fun _ _ ⟨j, hj⟩ => ⟨j, (lt_add_one E0).trans hj⟩)
  · exact vkLev_codeLim hl hX hlim hE hEW (fun E' hE' h1' hE'E => IH E' hE'E hE' h1' (hE'E.trans hEW))

end Main

end Googology.Trans.PoR.InaccPsi.R2.Vk
