import Googology.Trans.PoR.InaccPsi.R2.UjNat

/-!
# Every level `1 ≤ E < ρ_λ` over every offset past `Γ₂`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `Y₃ = ψ_{Ω₃}(Ω₃)`,
`Y₂ = ψ_{Ω₂}(Ω₂)`, `Γ₂ = ψ_{Ω₃}(0)`, `G₁ = ψ_{Ω₂}(0)`, `⊤` the own predicate that holds everywhere.  A level
`E < ρ_λ` is a small element of the hull and of every closure `Cl(·, ψ_{Ω₂}(x))`, `Cl(·, Θ_λ(ψ_{Ω₂}(x)))`
(`Θ_λ(ψ_{Ω₂}(x)) ≥ ρ_λ`).  `Rv.rvLevE_all` (offsets below `Γ₂`) for the offsets past `Γ₂`.

* `ujRho_le_Th`, `ujOwP_lev` (**every `1 ≤ E < ρ_λ` is own at every offset**, image `E`), `ujSh_lev`
  (**`X₀ + W^E` is a shift past `Γ₂`** for every offset `X₀` and `1 ≤ E < ρ_λ`);
* `ujLev_limC` (**THE LIMIT LEVEL**: a limit `L < ρ_λ` whose smaller levels have the level statement has it, through
  `Uj.ujTopLimSh`), `ujLev_all` (**`UjLev ⊤ E E` for every `1 ≤ E < ρ_λ`**: the top law
  `Θ(T_{X₀ + W^E}(β)) = ψ_{Ω₁}(Â + Ω^{X̂₀ + Ω^E})` at every offset `X₀` past `Γ₂` with `W^E ∣ X₀`, `X₀ + W^E + Ω₂ < Y₃`,
  `X̂₀ + Ω^E + Ω₁ < Y₂`);
* `ujGam_boundsC`, `ujGamLevC` (**`RvTop (Γ₂ + W^E) (G₁ + Ω^E) 0`** at every base, `1 ≤ E < ρ_λ`), `ujGamReadC`
  (**`Θ_λ(ψ_{Ω₂}(W^{Γ₂ + W^E})) = ψ_{Ω₁}(A + 1 + Ω^{G₁ + Ω^E})`** at every restart).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Uj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Ug
  Googology.Trans.PoR.InaccPsi.R2.Ua

variable {S : InaccSeq.{0}}

/-- **The images of the atoms lie above `ρ_λ`**: `ρ_λ ≤ Θ_λ(ψ_{Ω₂}(x))`. -/
theorem ujRho_le_Th {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) (x : Ordinal.{0}) :
    upsilon l ≤ gxTh (upsilon l) (ldAtR S l) (S.psi x (Om (1 + 1))) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  calc upsilon l = gxTh (upsilon l) (ldAtR S l) (Om 1) := (gxTh_Om1 hρSC hρ1 (ldAt_GxAt _ _)).symm
    _ ≤ gxTh (upsilon l) (ldAtR S l) (S.psi x (Om (1 + 1))) := gxTh_mono (psiS_bounds (S := S) x 1).1.le

/-- **Every level `1 ≤ E < ρ_λ` is own at every offset** (image `E`; `E` is a small element of every closure that
matters). -/
theorem ujOwP_lev {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {E : Ordinal.{0}}
    (h1 : 1 ≤ E) (hE : E < upsilon l) : UjOwP S l (fun _ _ => True) E E := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hW : ∀ x, E < S.psi x (Om (1 + 1)) := fun x => (hE.trans hρ1).trans (psiS_bounds (S := S) x 1).1
  have hT : ∀ x, E < gxTh (upsilon l) (ldAtR S l) (S.psi x (Om (1 + 1))) :=
    fun x => hE.trans_le (ujRho_le_Th hl hX x)
  exact ⟨fun _ _ _ => ⟨h1, CSet.of_lt hE, CSet.of_lt (hW _), CSet.of_lt (hT _),
    fun _ _ hb => UgC.small ((hW _).trans_le hb), fun _ _ hb => UgC.small ((hT _).trans_le hb)⟩,
    fun _ _ _ _ _ _ _ => trivial⟩

/-- **`X₀ + W^E` is a shift past `Γ₂`** for every offset `X₀` and every `1 ≤ E < ρ_λ`. -/
theorem ujSh_lev {l ηx b X0 Xh0 E : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hoff : UjOff S l b X0 Xh0) (h1 : 1 ≤ E) (hE : E < upsilon l)
    (hG3 : X0 + leWe E + Om (1 + 1) < ugY S) (hG : Xh0 + leOe E + Om 1 < ujY S 0) :
    UjSh S l b (X0 + leWe E) (Xh0 + leOe E) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  obtain ⟨hd, hH, hm, hmh, hcl, hclh⟩ := ujOff_data hoff
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
    lt_of_le_of_lt le_rfl hG3, lt_of_le_of_lt le_rfl hG, fun Q hQ hb => ?_, fun Q hQ hb => ?_⟩
  · exact UgC.add (hcl Q hQ (hle.trans hb))
      (UgC.opow hQ.1 (ugC_mulK hQ h2 E (UgC.small ((hW _).trans_le hb))))
  · exact UgC.add (hclh Q hQ ((gxTh_mono hle).trans hb))
      (UgC.opow hQ.1 (ugC_mulK hQ one_ne_zero E (UgC.small ((hT _).trans_le hb))))

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE LIMIT LEVEL**: a limit `L < ρ_λ` whose smaller levels `1 ≤ E < L` have the level statement has it. -/
theorem ujLev_limC {L : Ordinal.{0}} (hlim : IsSuccLimit L) (hL : L < upsilon l)
    (IH : ∀ E, 1 ≤ E → E < L → UjLev S l (fun _ _ => True) E E) : UjLev S l (fun _ _ => True) L L := by
  intro b X0 Xh0 hoff hd hG3 hG _
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  have h1L : (1 : Ordinal.{0}) < L := rvLim_one_lt hlim
  -- every smaller level gives a shift with its top
  have hsub : ∀ E, 1 ≤ E → E < L → UjSh S l b (X0 + leWe E) (Xh0 + leOe E) ∧
      RvTop S l b (X0 + leWe E) (Xh0 + leOe E) 0 := by
    intro E h1 hEL
    have hWle : leWe E ≤ leWe L := leWe_mono hEL.le
    have hOle : leOe E ≤ leOe L := leOe_mono hEL.le
    have hG3E : X0 + leWe E + Om (1 + 1) < ugY S :=
      lt_of_le_of_lt (add_le_add_left ((add_le_add_iff_left X0).2 hWle) _) hG3
    have hGE : Xh0 + leOe E + Om 1 < ujY S 0 :=
      lt_of_le_of_lt (add_le_add_left ((add_le_add_iff_left Xh0).2 hOle) _) hG
    exact ⟨ujSh_lev hl hX hoff h1 (hEL.trans hL) hG3E hGE,
      IH E h1 hEL b X0 Xh0 hoff ((leWe_dvd hEL.le).trans hd) hG3E hGE trivial⟩
  refine ujTopLimSh hl hX (ujSh_lev hl hX hoff h1L.le hL hG3 hG) (fun x _ hx => ?_) (fun z hz => ?_)
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

/-- **`UjLev ⊤ E E` for every `1 ≤ E < ρ_λ`**: every level below `ρ_λ` over every offset past `Γ₂`. -/
theorem ujLev_all : ∀ E, 1 ≤ E → E < upsilon l → UjLev S l (fun _ _ => True) E E := by
  intro E
  induction E using WellFoundedLT.induction with
  | ind E IH =>
  intro h1 hE
  rcases zero_or_succ_or_isSuccLimit E with h0 | ⟨E0, hE0⟩ | hlim
  · subst h0; exact absurd h1 (by simp)
  · rw [succ_eq_add_one] at hE0
    subst hE0
    rcases eq_or_ne E0 0 with rfl | h00
    · rw [zero_add]; exact ujLev_one hl hX
    have h10 : 1 ≤ E0 := Order.one_le_iff_ne_zero.2 h00
    have hE0G : E0 < upsilon l := (lt_add_one E0).trans hE
    exact ujLev_succ hl hX (ujOwP_lev hl hX h10 hE0G) (IH E0 (lt_add_one E0) h10 hE0G) (fun _ _ h => h)
  · exact ujLev_limC hl hX hlim hE (fun E' h1' hE' => IH E' hE' h1' (hE'.trans hE))

/-- The bounds at `Γ₂ + W^E`, `E < ρ_λ`. -/
theorem ujGam_boundsC {E : Ordinal.{0}} (hE : E < upsilon l) :
    leWe E ∣ uaGam ∧ uaGam + leWe E + Om (1 + 1) < ugY S ∧
      S.psi 0 (Om (1 + 1)) + leOe E + Om 1 < ujY S 0 := by
  have hY : SC (ugY S) := ujY_SC (S := S) 1
  have hWY : Om (1 + 1 : Ordinal.{0}) < ugY S := ujY_gt (S := S) 1
  have hY2 : SC (ujY S 0) := ujY_SC 0
  have hΩY2 : Om (1 : Ordinal.{0}) < ujY S 0 := by have := ujY_gt (S := S) 0; rwa [zero_add] at this
  have hE1 : E < Om 1 := hE.trans (leRho hl hX).2
  have hEG : E < uaGam := hE1.trans (gg_Om1_lt_Om2.trans uaGam_spec.2)
  refine ⟨(leWe_lt_SC uaGam_spec.1 uaGam_spec.2 hEG).2,
    hY.isPrincipal (hY.isPrincipal ujGam_lt_Y (leWe_lt_SC hY hWY (hEG.trans ujGam_lt_Y)).1) hWY,
    hY2.isPrincipal (hY2.isPrincipal ujY2_gt_G1 (leOe_lt_SC hY2 hΩY2 (hE1.trans hΩY2)).1) hΩY2⟩

/-- **`RvTop (Γ₂ + W^E) (G₁ + Ω^E) 0`** at every base, for every `1 ≤ E < ρ_λ`. -/
theorem ujGamLevC (b : Ordinal.{0}) {E : Ordinal.{0}} (h1 : 1 ≤ E) (hE : E < upsilon l) :
    RvTop S l b (uaGam + leWe E) (S.psi 0 (Om (1 + 1)) + leOe E) 0 := by
  obtain ⟨hd, hG3, hG⟩ := ujGam_boundsC hl hX hE
  exact ujLev_all hl hX E h1 hE b _ _ (ujGamOff hl hX b) hd hG3 hG trivial

/-- **`Θ_λ(ψ_{Ω₂}(W^{Γ₂ + W^E})) = ψ_{Ω₁}(A + 1 + Ω^{G₁ + Ω^E})`** for every `1 ≤ E < ρ_λ`, at every restart `λ`
with `A` own, `ψ_{Ω₁}(A) = ρ_λ`. -/
theorem ujGamReadC {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    {E : Ordinal.{0}} (h1 : 1 ≤ E) (hE : E < upsilon l) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (uaGam + leWe E)) (Om (1 + 1))) =
      S.psi (A + 1 + leOe (S.psi 0 (Om (1 + 1)) + leOe E)) (Om 1) := by
  obtain ⟨-, hG3, -⟩ := ujGam_boundsC hl hX hE
  exact ujRead0 (ujGamLevC hl hX 0 h1 hE) (lt_of_le_of_lt le_self_add hG3) hA hρ

end Main

end Googology.Trans.PoR.InaccPsi.R2.Uj
