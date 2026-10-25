import Googology.Trans.PoR.InaccPsi.R2.UmLad

/-!
# The level `Γ₂` over every offset past `Γ₂`

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Ua.uaTh`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `Γ₂ = Ua.uaGam = ψ_{Ω₃}(0)`,
`G₁ = ψ_{Ω₂}(0)`, `X_k = Ud.udX k` (`Γ₂ = sup_k X_k`, `G₁ = sup_k T X_k`: `Ud.udX_cof`, `Ug.ugThX_cof`),
`Y₃ = ψ_{Ω₃}(Ω₃)`, `Y₂ = ψ_{Ω₂}(Ω₂)`.

`UjLev ⊤ Γ₂ G₁` by the hull-limit rule past `Γ₂` (`Um.umLevLimH`) with the members `X_k` (`Um.umLevX`, own
predicate `CL X_k` true at every base and offset): every hull `y < W^{Γ₂}` is below some `W^{X_k}`, every
`z < Ω^{G₁}` below some `Ω^{T X_k}`.  The own data of `Γ₂` (image `G₁`) at every base and offset come from the shift
`Uj.ujShG` and the atom code `Ug.ugC_gam`.

* `umOwP_gam` (**the own data of `Γ₂` with the image `ψ_{Ω₂}(0)`, own predicate `⊤`**);
* `umLevGam` (**THE LEVEL `Γ₂` OVER EVERY OFFSET PAST `Γ₂`: `UjLev ⊤ Γ₂ G₁`**, i.e.
  `Θ(ψ_{Ω₂}(β + W^{X₀ + W^{Γ₂}})) = ψ_{Ω₁}(Â + Ω^{X̂₀ + Ω^{G₁}})` at every offset `X₀` past `Γ₂` with `W^{Γ₂} ∣ X₀`);
* `umGamGamLev`, `umGamGamRead` (**`Θ_λ(ψ_{Ω₂}(W^{Γ₂ + W^{Γ₂}})) = ψ_{Ω₁}(A + 1 + Ω^{G₁ + Ω^{G₁}})`**: the offset
  `Γ₂`, the level `Γ₂`);
* `umOwP_succ` (the own data past `Γ₂` pass from `E` to `E + 1`), `umLevGamN` (**the levels `Γ₂ + n`, image
  `G₁ + n`, over every offset past `Γ₂`**).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Um

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Ua Googology.Trans.PoR.InaccPsi.R2.Ud
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj

variable {S : InaccSeq.{0}}

/-- **The own data of `Γ₂` with the image `ψ_{Ω₂}(0)`** at every base and offset. -/
theorem umOwP_gam (l : Ordinal.{0}) : UjOwP S l (fun _ _ => True) uaGam (S.psi 0 (Om (1 + 1))) := by
  refine ⟨fun b X0 _ => ?_, fun _ _ _ _ _ _ _ => trivial⟩
  have hs := ujShG (S := S) l b
  have hle : S.psi (b + leWe uaGam) (Om (1 + 1)) ≤ S.psi (b + leWe (X0 + leWe uaGam)) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left b).2
      (leWe_mono ((ujLe_We _).trans le_add_self)))).1
  exact ⟨(gg_one_lt_of_SC uaGam_spec.1).le, hs.hull, CSet_mono le_rfl hle hs.mem,
    CSet_mono le_rfl (gxTh_mono hle) hs.memh, fun Q hQ _ => ugC_gam hQ.1,
    fun Q hQ hQ' => hs.clh Q hQ ((gxTh_mono hle).trans hQ')⟩

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE LEVEL `Γ₂` OVER EVERY OFFSET PAST `Γ₂`**: `UjLev ⊤ Γ₂ ψ_{Ω₂}(0)`. -/
theorem umLevGam : UjLev S l (fun _ _ => True) uaGam (S.psi 0 (Om (1 + 1))) := by
  have hTX : ∀ k, uaTh S l (udX k) < S.psi 0 (Om (1 + 1)) := fun k =>
    uaLtG1 hl hX _ (ugX_mem _ _ k) (udX_lt k)
  have hmemX : ∀ (b X0 : Ordinal.{0}) k, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop,
      UjOwP S l Owe (udX k) (uaTh S l (udX k)) ∧ UjLev S l Owe (udX k) (uaTh S l (udX k)) ∧ Owe b X0 :=
    fun b X0 k => ⟨SnCL S (udX k), (umLevX hl hX k).1, (umLevX hl hX k).2, fun Q hQ _ => ugX_cl hQ k⟩
  refine umLevLimH hl hX (umOwP_gam l) ?_ ?_
  · intro b X0 _ y _ hy
    obtain ⟨k, hk⟩ : ∃ k, y < leWe (udX k) := by
      rcases eq_or_ne y 0 with rfl | hy0
      · exact ⟨0, leWe_pos _⟩
      have hw := (sjLogW (by rw [leWe_zero]; exact Order.one_le_iff_ne_zero.2 hy0) hy).2
      obtain ⟨k, hk⟩ := udX_cof hw
      exact ⟨k, (roLt_We_log y).trans_le (leWe_mono (Order.add_one_le_of_lt hk))⟩
    obtain ⟨Owe, h1, h2, h3⟩ := hmemX b X0 k
    exact ⟨_, _, Owe, h1, h2, h3, udX_lt k, hTX k, hk⟩
  · intro b X0 _ z hz
    obtain ⟨k, hk⟩ : ∃ k, z < leOe (uaTh S l (udX k)) := by
      rcases eq_or_ne z 0 with rfl | hz0
      · exact ⟨0, leOe_pos _⟩
      have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
      have hq : log ω z / Om 1 < S.psi 0 (Om (1 + 1)) :=
        (Ordinal.lt_mul_iff_div_lt hΩ0).1 ((lt_opow_iff_log_lt one_lt_omega0 hz0).1 hz)
      obtain ⟨k, hk⟩ := ugThX_cof hl hX hq
      exact ⟨k, (roLt_Oe_log z).trans_le (leOe_mono (Order.add_one_le_of_lt hk))⟩
    obtain ⟨Owe, h1, h2, h3⟩ := hmemX b X0 k
    exact ⟨_, _, Owe, h1, h2, h3, udX_lt k, hTX k, hk⟩

/-- **`RvTop (Γ₂ + W^{Γ₂}) (G₁ + Ω^{G₁}) 0`** at every base (the offset `Γ₂`, the level `Γ₂`). -/
theorem umGamGamLev (b : Ordinal.{0}) :
    RvTop S l b (uaGam + leWe uaGam) (S.psi 0 (Om (1 + 1)) + leOe (S.psi 0 (Om (1 + 1)))) 0 := by
  have hW : leWe uaGam = uaGam := (uaWfix (gg_SC_eps uaGam_spec.1) uaGam_spec.2).2
  have hY : SC (ugY S) := ujY_SC (S := S) 1
  have hWY : Om (1 + 1 : Ordinal.{0}) < ugY S := ujY_gt (S := S) 1
  have hY2 : SC (ujY S 0) := ujY_SC 0
  have hΩY2 : Om (1 : Ordinal.{0}) < ujY S 0 := by have := ujY_gt (S := S) 0; rwa [zero_add] at this
  have hd : leWe uaGam ∣ uaGam := by rw [hW]
  have hG3 : uaGam + leWe uaGam + Om (1 + 1) < ugY S := by
    rw [hW]; exact hY.isPrincipal (hY.isPrincipal ujGam_lt_Y ujGam_lt_Y) hWY
  have hG : S.psi 0 (Om (1 + 1)) + leOe (S.psi 0 (Om (1 + 1))) + Om 1 < ujY S 0 :=
    hY2.isPrincipal (hY2.isPrincipal ujY2_gt_G1 (leOe_lt_SC hY2 hΩY2 ujY2_gt_G1).1) hΩY2
  exact umLevGam hl hX b _ _ (ujGamOff hl hX b) hd hG3 hG trivial

/-- **`Θ_λ(ψ_{Ω₂}(W^{Γ₂ + W^{Γ₂}})) = ψ_{Ω₁}(A + 1 + Ω^{G₁ + Ω^{G₁}})`** at every restart `λ` with `A` own,
`ψ_{Ω₁}(A) = ρ_λ`. -/
theorem umGamGamRead {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (uaGam + leWe uaGam)) (Om (1 + 1))) =
      S.psi (A + 1 + leOe (S.psi 0 (Om (1 + 1)) + leOe (S.psi 0 (Om (1 + 1))))) (Om 1) := by
  have hW : leWe uaGam = uaGam := (uaWfix (gg_SC_eps uaGam_spec.1) uaGam_spec.2).2
  have hY : SC (ugY S) := ujY_SC (S := S) 1
  have hXY : uaGam + leWe uaGam < ugY S := by rw [hW]; exact hY.isPrincipal ujGam_lt_Y ujGam_lt_Y
  exact ujRead0 (umGamGamLev hl hX 0) hXY hA hρ

omit hl hX in
/-- **The own data pass from `E` to `E + 1`** (past `Γ₂`). -/
theorem umOwP_succ {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {E Eh : Ordinal.{0}} (h : UjOwP S l Ow E Eh) :
    UjOwP S l Ow (E + 1) (Eh + 1) := by
  refine ⟨fun b X0 hOw => ?_, h.mono⟩
  have hd := h.dat b X0 hOw
  have hle := scTop_mono (S := S) (le_refl b) (le_refl X0) (le_self_add : E ≤ E + 1)
  exact ⟨le_add_self, CSet.succ_mem hd.hull, CSet.succ_mem (CSet_mono le_self_add hle hd.mem),
    CSet.succ_mem (CSet_mono le_self_add (gxTh_mono hle) hd.memh),
    fun Q hQ hY => UgC.add (hd.cl Q hQ (hle.trans hY)) (UgC.small (gg_one_lt_of_SC hQ)),
    fun Q hQ hY => UgC.add (hd.clh Q hQ ((gxTh_mono hle).trans hY)) (UgC.small (gg_one_lt_of_SC hQ))⟩

/-- **The levels `Γ₂ + n` over every offset past `Γ₂`**: `UjLev ⊤ (Γ₂ + n) (G₁ + n)` with the own data. -/
theorem umLevGamN : ∀ n : ℕ, UjOwP S l (fun _ _ => True) (uaGam + n) (S.psi 0 (Om (1 + 1)) + n) ∧
    UjLev S l (fun _ _ => True) (uaGam + n) (S.psi 0 (Om (1 + 1)) + n)
  | 0 => by simpa using ⟨umOwP_gam (S := S) l, umLevGam hl hX⟩
  | n + 1 => by
    obtain ⟨hP, hL⟩ := umLevGamN n
    have e1 : uaGam + ((n + 1 : ℕ) : Ordinal.{0}) = uaGam + n + 1 := by rw [Nat.cast_succ, add_assoc]
    have e2 : S.psi 0 (Om (1 + 1)) + ((n + 1 : ℕ) : Ordinal.{0}) = S.psi 0 (Om (1 + 1)) + n + 1 := by
      rw [Nat.cast_succ, add_assoc]
    rw [e1, e2]
    exact ⟨umOwP_succ hP, ujLev_succ hl hX hP hL (fun _ _ h => h)⟩

end Main

end Googology.Trans.PoR.InaccPsi.R2.Um
