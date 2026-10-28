import Googology.Trans.PoR.InaccPsi.R2.VkNat

/-!
# Every level `1 ≤ E < ρ_λ` over every offset, with no bound

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `⊤` the own predicate that holds
everywhere.  A level `E < ρ_λ` is a small element of every closure that matters (`Uj.ujRho_le_Th`).

* `vkOwP_lev` (every level `1 ≤ E < ρ_λ` is own at every offset, image `E`), `vkSh_lev` (**`X₀ + W^E` is a shift
  `VkSh`** for every offset `X₀` and `1 ≤ E < ρ_λ`);
* `vkLev_limC` (**the limit level**), `vkLev_all` (**`VkLev ⊤ E E` for every `1 ≤ E < ρ_λ`**).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Ug
  Googology.Trans.PoR.InaccPsi.R2.Ua Googology.Trans.PoR.InaccPsi.R2.Uj

variable {S : InaccSeq.{0}}

/-- **Every level `1 ≤ E < ρ_λ` is own at every offset** (image `E`; `E` is a small element of every closure that
matters). -/
theorem vkOwP_lev {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {E : Ordinal.{0}}
    (h1 : 1 ≤ E) (hE : E < upsilon l) : VkOwP S l (fun _ _ => True) E E := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hW : ∀ x, E < S.psi x (Om (1 + 1)) := fun x => (hE.trans hρ1).trans (psiS_bounds (S := S) x 1).1
  have hT : ∀ x, E < gxTh (upsilon l) (ldAtR S l) (S.psi x (Om (1 + 1))) :=
    fun x => hE.trans_le (ujRho_le_Th hl hX x)
  exact ⟨fun _ _ _ => ⟨h1, CSet.of_lt hE, CSet.of_lt (hW _), CSet.of_lt (hT _),
    fun _ _ hb => VkA.small ((hW _).trans_le hb), fun _ _ hb => VkA.small ((hT _).trans_le hb)⟩,
    fun _ _ _ _ _ _ _ => trivial⟩

/-- **`X₀ + W^E` is a shift `VkSh`** for every offset `X₀` and every `1 ≤ E < ρ_λ`. -/
theorem vkSh_lev {l ηx b X0 Xh0 E : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hoff : VkOff S l b X0 Xh0) (h1 : 1 ≤ E) (hE : E < upsilon l) :
    VkSh S l b (X0 + leWe E) (Xh0 + leOe E) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  obtain ⟨hd, hH, hm, hmh, hcl, hclh⟩ := vkOff_data hoff
  have h2 : (1 + 1 : Ordinal.{0}) ≠ 0 := by rw [one_add_one_eq_two]; exact two_ne_zero
  have hle : S.psi (b + leWe X0) (Om (1 + 1)) ≤ S.psi (b + leWe (X0 + leWe E)) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left b).2 (leWe_mono le_self_add))).1
  have hW : ∀ x, E < S.psi x (Om (1 + 1)) := fun x => (hE.trans hρ1).trans (psiS_bounds (S := S) x 1).1
  have hT : ∀ x, E < gxTh (upsilon l) (ldAtR S l) (S.psi x (Om (1 + 1))) :=
    fun x => hE.trans_le (ujRho_le_Th hl hX x)
  have hWd : Om (1 + 1) ∣ leWe E := by have h := leWe_dvd h1; rwa [leWe_one] at h
  refine ⟨fun h => (leWe_pos E).ne' (le_antisymm (h ▸ le_add_self) zero_le), dvd_add hd hWd,
    CSet.add_mem hH (leWe_mem (CSet.of_lt hE)),
    CSet.add_mem (CSet_mono le_self_add hle hm) (leWe_mem (CSet.of_lt (hW _))),
    CSet.add_mem (CSet_mono le_self_add (gxTh_mono hle) hmh) (leOe_mem (CSet.of_lt (hT _))),
    fun Q hQ hb => ?_, fun Q hQ hb => ?_⟩
  · exact VkA.add (hcl Q hQ (hle.trans hb))
      (VkA.opow hQ.1 (vkA_mulK hQ h2 E (VkA.small ((hW _).trans_le hb))))
  · exact VkA.add (hclh Q hQ ((gxTh_mono hle).trans hb))
      (VkA.opow hQ.1 (vkA_mulK hQ one_ne_zero E (VkA.small ((hT _).trans_le hb))))

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE LIMIT LEVEL**: a limit `L < ρ_λ` whose smaller levels `1 ≤ E < L` have the level statement has it. -/
theorem vkLev_limC {L : Ordinal.{0}} (hlim : IsSuccLimit L) (hL : L < upsilon l)
    (IH : ∀ E, 1 ≤ E → E < L → VkLev S l (fun _ _ => True) E E) : VkLev S l (fun _ _ => True) L L := by
  intro b X0 Xh0 hoff hd _
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  have h1L : (1 : Ordinal.{0}) < L := rvLim_one_lt hlim
  -- every smaller level gives a shift with its top
  have hsub : ∀ E, 1 ≤ E → E < L → VkSh S l b (X0 + leWe E) (Xh0 + leOe E) ∧
      RvTop S l b (X0 + leWe E) (Xh0 + leOe E) 0 := by
    intro E h1 hEL
    exact ⟨vkSh_lev hl hX hoff h1 (hEL.trans hL),
      IH E h1 hEL b X0 Xh0 hoff ((leWe_dvd hEL.le).trans hd) trivial⟩
  refine vkTopLimSh hl hX (vkSh_lev hl hX hoff h1L.le hL) (fun x _ hx => ?_) (fun z hz => ?_)
  · -- a level `E < L` with `x < X₀ + W^E`
    obtain ⟨E, h1E, hEL, hxE⟩ : ∃ E, 1 ≤ E ∧ E < L ∧ x < X0 + leWe E := by
      rcases lt_or_ge x X0 with hxX | hxX
      · exact ⟨1, le_rfl, h1L, hxX.trans_le le_self_add⟩
      obtain ⟨y, rfl⟩ := exists_add_of_le hxX
      have hy : y < leWe L := (add_lt_add_iff_left X0).1 hx
      rcases eq_or_ne y 0 with rfl | hy0
      · exact ⟨1, le_rfl, h1L, by rw [add_zero]; exact lt_add_of_pos_right _ (leWe_pos 1)⟩
      have hlogd : log ω y < Om (1 + 1) * L :=
        (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hy0).trans_lt hy)
      have hq : log ω y / Om (1 + 1) < L := (Ordinal.lt_mul_iff_div_lt hW0).1 hlogd
      exact ⟨log ω y / Om (1 + 1) + 1, le_add_self, hlim.succ_lt hq,
        (add_lt_add_iff_left X0).2 (roLt_We_log y)⟩
    obtain ⟨hs1, ht1⟩ := hsub E h1E hEL
    exact ⟨_, _, (add_le_add_iff_left X0).2 (leWe_mono hEL.le), hxE,
      (add_lt_add_iff_left Xh0).2 (leOe_lt hEL), hs1, ht1⟩
  · obtain ⟨E, h1E, hEL, hzE⟩ : ∃ E, 1 ≤ E ∧ E < L ∧ z < Xh0 + leOe E := by
      rcases lt_or_ge z Xh0 with hzX | hzX
      · exact ⟨1, le_rfl, h1L, hzX.trans_le le_self_add⟩
      obtain ⟨r, rfl⟩ := exists_add_of_le hzX
      have hr : r < leOe L := (add_lt_add_iff_left Xh0).1 hz
      rcases eq_or_ne r 0 with rfl | hr0
      · exact ⟨1, le_rfl, h1L, by rw [add_zero]; exact lt_add_of_pos_right _ (leOe_pos 1)⟩
      have hlogr : log ω r < Om 1 * L :=
        (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hr0).trans_lt hr)
      have hq : log ω r / Om 1 < L := (Ordinal.lt_mul_iff_div_lt hΩ0).1 hlogr
      exact ⟨log ω r / Om 1 + 1, le_add_self, hlim.succ_lt hq, (add_lt_add_iff_left Xh0).2 (roLt_Oe_log r)⟩
    obtain ⟨hs1, ht1⟩ := hsub E h1E hEL
    exact ⟨_, _, (add_lt_add_iff_left X0).2 (leWe_lt hEL), hzE, hs1, ht1⟩

/-- **`VkLev ⊤ E E` for every `1 ≤ E < ρ_λ`**: every level below `ρ_λ` over every offset (no bound). -/
theorem vkLev_all : ∀ E, 1 ≤ E → E < upsilon l → VkLev S l (fun _ _ => True) E E := by
  intro E
  induction E using WellFoundedLT.induction with
  | ind E IH =>
  intro h1 hE
  rcases zero_or_succ_or_isSuccLimit E with h0 | ⟨E0, hE0⟩ | hlim
  · subst h0; exact absurd h1 (by simp)
  · rw [succ_eq_add_one] at hE0
    subst hE0
    rcases eq_or_ne E0 0 with rfl | h00
    · rw [zero_add]; exact vkLev_one hl hX
    have h10 : 1 ≤ E0 := Order.one_le_iff_ne_zero.2 h00
    have hE0G : E0 < upsilon l := (lt_add_one E0).trans hE
    exact vkLev_succ hl hX (vkOwP_lev hl hX h10 hE0G) (IH E0 (lt_add_one E0) h10 hE0G) (fun _ _ h => h)
  · exact vkLev_limC hl hX hlim hE (fun E' h1' hE' => IH E' hE' h1' (hE'.trans hE))

end Main

end Googology.Trans.PoR.InaccPsi.R2.Vk
