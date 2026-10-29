import Googology.Trans.PoR.InaccPsi.R2.VnRead

/-!
# At every level `k`: the corrected top at `Y_{k+3}` refutes the top at `Ω_{k+3}` with the image `Ω_{k+2}`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `Y_{k+2} = ψ_{Ω_{k+2}}(Ω_{k+2}) = Uj.ujY S k`; a restart `λ`
with `ψ_{Ω₁}(A) = ρ_λ`, `A ∈ Cl(A, ψ_{Ω₁}(A))`.

* `vnRead_WK` (**given `Θ(ψ₂(Y_{k+3})) = ψ₁(A + 1 + Y_{k+2})`, the same reading at every `ψ₂(W^X)` with
  `Y_{k+3} ≤ W^X ≤ Ω_{k+3}`**);
* `vnTop_falseK` (**then `¬ RvTop λ 0 X X̂ 0` whenever `Y_{k+3} ≤ W^X ≤ Ω_{k+3}` and `Y_{k+2} < Ω^{X̂}`**),
  `vnTop_OmK` (**the top at `Ω_{k+3}` with the image `Ω_{k+2} = T Ω_{k+3}` is false**), `vnLev_OmK` (**no level
  statement `VkLev Ow Ω_{k+3} Ω_{k+2}` with `Ow 0 0`**), `vnOwnE_OmK` (UNCONDITIONAL: `Ω_{k+3}` is own with the image
  `Ω_{k+2}` at every base and offset).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj Googology.Trans.PoR.InaccPsi.R2.Vk

variable {S : InaccSeq.{0}}

theorem vnOmK_mem (k : ℕ) (a c : Ordinal.{0}) : Om ((k : Ordinal.{0}) + 1 + 1) ∈ S.CSet a c :=
  CSet.Om_mem (CSet.succ_mem (CSet.succ_mem (Sc.scNat_mem a c k)))

theorem vnOmK3_mem (k : ℕ) (a c : Ordinal.{0}) : Om ((k : Ordinal.{0}) + 1 + 1 + 1) ∈ S.CSet a c :=
  CSet.Om_mem (CSet.succ_mem (CSet.succ_mem (CSet.succ_mem (Sc.scNat_mem a c k))))

theorem vnOm2_lt_K (k : ℕ) : Om (1 + 1 : Ordinal.{0}) < Om ((k : Ordinal.{0}) + 1 + 1 + 1) := by
  have hk2 : (1 + 1 : Ordinal.{0}) ≤ (k : Ordinal.{0}) + 1 + 1 := by gcongr; exact le_add_self
  exact Om_lt_Om.2 (hk2.trans_lt (lt_add_one _))

/-- `W^{Ω_{k+3}} = Ω_{k+3}`. -/
theorem vnWe_OmK (k : ℕ) : leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) = Om ((k : Ordinal.{0}) + 1 + 1 + 1) := by
  have h3 : ((k : Ordinal.{0}) + 1 + 1 + 1) ≠ 0 := (add_pos_of_right zero_lt_one _).ne'
  exact (ugSC_W (SC_Om h3) (vnOm2_lt_K k)).2

/-- **UNCONDITIONAL: `Ω_{k+3}` is an own exponent with the image `Ω_{k+2}`** at every base and every offset. -/
theorem vnOwnE_OmK (k : ℕ) (l b X0 : Ordinal.{0}) :
    VkOwnE S l b X0 (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Om ((k : Ordinal.{0}) + 1 + 1)) := by
  have h3 : ((k : Ordinal.{0}) + 1 + 1 + 1) ≠ 0 := (add_pos_of_right zero_lt_one _).ne'
  have h23 : (1 + 1 : Ordinal.{0}) ≤ (k : Ordinal.{0}) + 1 + 1 + 1 := by
    have : (1 + 1 : Ordinal.{0}) ≤ (k : Ordinal.{0}) + 1 + 1 := by gcongr; exact le_add_self
    exact this.trans le_self_add
  have h12 : (1 : Ordinal.{0}) ≤ (k : Ordinal.{0}) + 1 + 1 := le_add_self
  exact ⟨(gg_one_lt_of_SC (SC_Om h3)).le, vnOmK3_mem k _ _, vnOmK3_mem k _ _, vnOmK_mem k _ _,
    fun Q hQ _ => VkA.om hQ.1 h23, fun Q hQ _ => VkA.om hQ.1 h12⟩

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

omit hl hX in
/-- **The reading at every `ψ₂(W^X)` with `Y_{k+3} ≤ W^X ≤ Ω_{k+3}`**, given the reading at `Y_{k+3}`. -/
theorem vnRead_WK (k : ℕ) {A X : Ordinal.{0}}
    (hYk : gxTh (upsilon l) (ldAtR S l) (S.psi (ujY S ((k : Ordinal.{0}) + 1)) (Om (1 + 1))) =
      S.psi (A + 1 + ujY S (k : Ordinal.{0})) (Om 1))
    (hYW : ujY S ((k : Ordinal.{0}) + 1) ≤ leWe X) (hW3 : leWe X ≤ Om ((k : Ordinal.{0}) + 1 + 1 + 1)) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (leWe X) (Om (1 + 1))) =
      S.psi (A + 1 + ujY S (k : Ordinal.{0})) (Om 1) := by
  have hk2 : (1 + 1 : Ordinal.{0}) ≤ (k : Ordinal.{0}) + 1 + 1 := by gcongr; exact le_add_self
  have h2 : Om (1 + 1 : Ordinal.{0}) < ujY S ((k : Ordinal.{0}) + 1) :=
    (Om_le_Om.2 hk2).trans_lt (ujY_gt _)
  rw [vnPsi2_eq (s := (k : Ordinal.{0}) + 1 + 1) h2 hYW hW3]
  exact hYk

/-- **Given `Θ(ψ₂(Y_{k+3})) = ψ₁(A + 1 + Y_{k+2})`: `¬ RvTop λ 0 X X̂ 0` whenever `Y_{k+3} ≤ W^X ≤ Ω_{k+3}` and
`Y_{k+2} < Ω^{X̂}`.** -/
theorem vnTop_falseK (k : ℕ) {A X Xh : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1)))
    (hρ : S.psi A (Om 1) = upsilon l)
    (hYk : gxTh (upsilon l) (ldAtR S l) (S.psi (ujY S ((k : Ordinal.{0}) + 1)) (Om (1 + 1))) =
      S.psi (A + 1 + ujY S (k : Ordinal.{0})) (Om 1))
    (hYW : ujY S ((k : Ordinal.{0}) + 1) ≤ leWe X) (hW3 : leWe X ≤ Om ((k : Ordinal.{0}) + 1 + 1 + 1))
    (hXh : ujY S (k : Ordinal.{0}) < leOe Xh) : ¬ RvTop S l 0 X Xh 0 := by
  intro hT
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hXω : X < Om ω := ((ujLe_We X).trans hW3).trans_lt (Om_lt_Om.2 (vkNat_lt_omega k))
  have h1 := vkRead0 hT hXω hA hρ
  rw [vnRead_WK k hYk hYW hW3] at h1
  have hAω := vnA_ge hl hX hA hρ
  have hle : A ≤ A + 1 + leOe Xh := le_self_add.trans le_self_add
  have hlt : A + 1 + ujY S (k : Ordinal.{0}) < A + 1 + leOe Xh := (add_lt_add_iff_left _).2 hXh
  have hΩk : Om ((k : Ordinal.{0}) + 1 + 1) < A + 1 + leOe Xh :=
    ((Om_lt_Om.2 (Vb.vbNat_lt_omega k)).trans_le hAω).trans_le hle
  have hmem : A + 1 + ujY S (k : Ordinal.{0}) ∈ S.CSet (A + 1 + leOe Xh) (S.psi (A + 1 + leOe Xh) (Om 1)) :=
    CSet.add_mem (CSet.add_mem ((psi_mono (S := S) hκ1 hle).2 hA) (CSet.one_mem _ _))
      (CSet.psi_mem hΩk (InR_Om_succ ((k : Ordinal.{0}) + 1)) (vnOmK_mem k _ _) (vnOmK_mem k _ _))
  have h2 := psi_lt_psi_of_mem hκ1 hlt hmem
  rw [h1] at h2
  exact lt_irrefl _ h2

/-- **The top at `Ω_{k+3}` with the image `Ω_{k+2} = T Ω_{k+3}` is false** (given the reading at `Y_{k+3}`). -/
theorem vnTop_OmK (k : ℕ) {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1)))
    (hρ : S.psi A (Om 1) = upsilon l)
    (hYk : gxTh (upsilon l) (ldAtR S l) (S.psi (ujY S ((k : Ordinal.{0}) + 1)) (Om (1 + 1))) =
      S.psi (A + 1 + ujY S (k : Ordinal.{0})) (Om 1)) :
    ¬ RvTop S l 0 (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Om ((k : Ordinal.{0}) + 1 + 1)) 0 :=
  vnTop_falseK hl hX k hA hρ hYk (by rw [vnWe_OmK]; exact (ujY_lt _).le) (vnWe_OmK k).le
    ((ujY_lt _).trans_le (ujLe_Oe _))

/-- **No level statement `VkLev Ow Ω_{k+3} Ω_{k+2}` with `Ow 0 0`** (given the reading at `Y_{k+3}`). -/
theorem vnLev_OmK (k : ℕ) {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1)))
    (hρ : S.psi A (Om 1) = upsilon l)
    (hYk : gxTh (upsilon l) (ldAtR S l) (S.psi (ujY S ((k : Ordinal.{0}) + 1)) (Om (1 + 1))) =
      S.psi (A + 1 + ujY S (k : Ordinal.{0})) (Om 1))
    {Ow : Ordinal.{0} → Ordinal.{0} → Prop} (hO : Ow 0 0) :
    ¬ VkLev S l Ow (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Om ((k : Ordinal.{0}) + 1 + 1)) := by
  intro hL
  have h := hL 0 0 0 (Or.inl ⟨rfl, rfl⟩) (dvd_zero _) hO
  rw [zero_add, zero_add] at h
  refine vnTop_falseK hl hX k hA hρ hYk (by rw [vnWe_OmK, vnWe_OmK]; exact (ujY_lt _).le)
    (by rw [vnWe_OmK, vnWe_OmK]) ((ujY_lt _).trans_le ((ujLe_Oe _).trans (ujLe_Oe _))) h

end Main

end Googology.Trans.PoR.InaccPsi.R2.Vn
