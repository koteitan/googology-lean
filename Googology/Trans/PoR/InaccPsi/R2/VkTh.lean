import Googology.Trans.PoR.InaccPsi.R2.VkCodeL

/-!
# The shifts `Ω_{k+2}` past the wall `Y₃`, and `Θ_λ(θ)` from the tops at the levels `Ω_{k+3}`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `θ = ConjT.th S = ψ_{Ω₂}(Ω_ω)`, `T = Vb.vbT S λ`.

* `vkSh_Om` (**`(Ω_{k+2}, Ω_{k+1})` is a shift `Vk.VkSh` at every base, for every `k`**), `vkNoUj` (**no
  `Uj.UjSh` has the shift `Ω₃`**: the fixed bound `Y₃` excludes it), `vkSh_OmT` (the image is `T Ω_{k+2}`);
* `vkTheta_th` (**`Θ_λ(θ) = ψ_{Ω₁}(A + 1 + Ω_ω)`** at a restart with `ψ_{Ω₁}(A) = ρ_λ`, given the tops
  `RvTop (Ω_{k+3}) (Ω_{k+2}) 0` at the base `0` for every `k`; through `Ug.ugReadLim` and `Vk.vkRead0`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj

variable {S : InaccSeq.{0}}

theorem vkNat_lt_omega (k : ℕ) : (k : Ordinal.{0}) + 1 + 1 + 1 < ω := by
  have h : (k : Ordinal.{0}) + 1 + 1 + 1 = ((k + 1 + 1 + 1 : ℕ) : Ordinal.{0}) := by
    simp only [Nat.cast_add, Nat.cast_one]
  rw [h]; exact natCast_lt_omega0 _

theorem vkOm_mem (a c : Ordinal.{0}) (k : ℕ) : Om ((k : Ordinal.{0}) + 1) ∈ S.CSet a c :=
  CSet.Om_mem (CSet.succ_mem (Sc.scNat_mem a c k))

/-- **`(Ω_{k+2}, Ω_{k+1})` is a shift at every base, for every `k`.** -/
theorem vkSh_Om (l b : Ordinal.{0}) (k : ℕ) :
    VkSh S l b (Om ((k : Ordinal.{0}) + 1 + 1)) (Om ((k : Ordinal.{0}) + 1)) := by
  have hk2 : (1 + 1 : Ordinal.{0}) ≤ (k : Ordinal.{0}) + 1 + 1 := by gcongr; exact le_add_self
  have hk1 : (1 : Ordinal.{0}) ≤ (k : Ordinal.{0}) + 1 := le_add_self
  have hm : ∀ a c, Om ((k : Ordinal.{0}) + 1 + 1) ∈ S.CSet a c := fun a c => by
    have h := vkOm_mem (S := S) a c (k + 1); rwa [Nat.cast_succ] at h
  have hdvd : Om (1 + 1) ∣ Om ((k : Ordinal.{0}) + 1 + 1) := by
    rcases hk2.lt_or_eq with h | h
    · have hSC : SC (Om ((k : Ordinal.{0}) + 1 + 1)) := SC_Om (zero_lt_one.trans_le (hk1.trans le_self_add)).ne'
      have h1 := (leWe_lt_SC hSC (Om_lt_Om.2 h) (one_lt_omega0.trans (Lw.lw_omega_lt_SC hSC))).2
      rwa [leWe_one] at h1
    · rw [h]
  refine ⟨(Om_pos (zero_lt_one.trans_le (hk1.trans le_self_add)).ne').ne', hdvd, hm _ _, hm _ _,
    vkOm_mem _ _ k, fun Q hQ _ => VkA.om hQ.1 hk2, fun Q hQ _ => VkA.om hQ.1 hk1⟩

/-- **No `Uj.UjSh` has the shift `Ω₃`**: the bound `X + Ω₂ < Y₃` of `Uj.UjSh` fails there. -/
theorem vkNoUj (l b Xh : Ordinal.{0}) : ¬ UjSh S l b (Om (1 + 1 + 1)) Xh := fun hs =>
  absurd (ugY_lt_Om3.trans_le le_self_add) (not_lt.2 hs.ltY.le)

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- The image of the shift `Ω_{k+3}` is `T Ω_{k+3} = Ω_{k+2}`. -/
theorem vkSh_OmT (b : Ordinal.{0}) (k : ℕ) :
    VkSh S l b (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Vb.vbT S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1))) := by
  have h := Vb.vbT_Om (S := S) hl hX (k := k + 1 + 1) (by omega)
  have h2 := vkSh_Om (S := S) l b (k + 1)
  simp only [Nat.cast_add, Nat.cast_one] at h h2
  rw [h]; exact h2

end Rst

/-- **`Θ_λ(θ) = ψ_{Ω₁}(A + 1 + Ω_ω)`** from the tops `RvTop (Ω_{k+3}) (Ω_{k+2}) 0` at the base `0`. -/
theorem vkTheta_th {l A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    (hT : ∀ k : ℕ, RvTop S l 0 (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Om ((k : Ordinal.{0}) + 1 + 1)) 0) :
    gxTh (upsilon l) (ldAtR S l) (ConjT.th S) = S.psi (A + 1 + Om ω) (Om 1) := by
  have hW := vkOmW
  have hlim : IsSuccLimit (Om (ω : Ordinal.{0})) := hW.1.isSuccLimit
  have hlt3 : ∀ k : ℕ, Om ((k : Ordinal.{0}) + 1 + 1 + 1) < Om ω := fun k => Om_lt_Om.2 (vkNat_lt_omega k)
  have hlt2 : ∀ k : ℕ, Om ((k : Ordinal.{0}) + 1 + 1) < Om ω :=
    fun k => (Om_lt_Om.2 (lt_add_one _)).trans (hlt3 k)
  have hn3 : ∀ n : ℕ, Om (n : Ordinal.{0}) ≤ Om ((n : Ordinal.{0}) + 1 + 1 + 1) :=
    fun n => Om_le_Om.2 ((le_self_add.trans le_self_add).trans le_self_add)
  have h := ugReadLim (S := S) (l := l) (β := 0) (Â := A + 1) (X := Om ω) (Y := Om ω)
    (fun k => leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1))) (fun k => leOe (Om ((k : Ordinal.{0}) + 1 + 1)))
    hlim hlim (fun k => (leWe_lt_SC hW.1 hW.2 (hlt3 k)).1.le)
    (fun e he => by
      obtain ⟨n, hn⟩ := Rx.rxOmW_nat he
      exact ⟨n, hn.trans_le ((hn3 n).trans (ujLe_We _))⟩)
    (fun k => (leOe_lt_SC hW.1 ((Om_lt_Om.2 (lt_add_one 1)).trans hW.2) (hlt2 k)).1.le)
    (fun z hz => by
      obtain ⟨n, hn⟩ := Rx.rxOmW_nat hz
      exact ⟨n, hn.le.trans ((Om_le_Om.2 (le_self_add.trans le_self_add)).trans (ujLe_Oe _))⟩)
    (fun k => by rw [zero_add]; exact vkRead0 (hT k) (hlt3 k) hA hρ)
  rw [zero_add] at h
  exact h

end Googology.Trans.PoR.InaccPsi.R2.Vk
