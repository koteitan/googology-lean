import Googology.Trans.PoR.InaccPsi.R2.VkPsi

/-!
# `T` maps codes above the level `k + 2` to codes above the level `k + 1`, on all of `D`

`T = Vb.vbT S λ`, `D = Vb.VbD S λ`, `Θ = gxTh ρ_λ (ldAtR λ)`, `VkA k Q` the codes over `Q` above the level `k`
(module `Vk.VkCode`).  `Vh.vhOwn` maps the level-`(k+2)` codes `Ug.UgC` (which lie below `Y_{k+3}`); here the codes
above the level `k + 2` (every strongly critical ordinal `≥ Ω_{k+2}` is a code) cover every member of `D` with a
code condition, up to `Ω_ω`.

* `vkOwn` (**THE OWN PROPERTY OF `T` ABOVE EVERY LEVEL**): for `k : ℕ`, `x ∈ D`, a strongly critical `T₀ < Ω₂` with
  `x` a code above the level `k + 2` over every strongly critical `Q ≥ T₀`, the image `T x` is a code above the
  level `k + 1` over every strongly critical `Q ≥ Θ(T₀)`;
* `vkOwn2` (`k = 0`), `VkCL` (**the closure condition above the level 2**: `E` a code above the level 2 over every
  strongly critical `Q ≥ ψ_{Ω₂}(b + W^{X₀ + W^E})`), `vkCL_of_ug` (`Ug.UgCL ⇒ VkCL`), `vkCL_mono`, `vkOwnCL`.

No new axiom.  New definition: `VkCL`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rx
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Vh Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}}

/-- **The closure condition above the level 2**: `E` is a code above the level 2 over every strongly critical
`Q ≥ ψ_{Ω₂}(b + W^{X₀ + W^E})`. -/
def VkCL (S : InaccSeq.{0}) (E b X0 : Ordinal.{0}) : Prop :=
  ∀ Q, SC Q → S.psi (b + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ Q → VkA (1 + 1) Q E

theorem vkCL_of_ug {E b X0 : Ordinal.{0}} (h : UgCL S E b X0) : VkCL S E b X0 :=
  fun Q hQ hQ' => vkA_of_ugC hQ.1 (h Q hQ hQ')

theorem vkCL_mono {E b β X0 X0' : Ordinal.{0}} (h : VkCL S E b X0) (hb : b ≤ β) (hX : X0 ≤ X0') :
    VkCL S E β X0' :=
  fun Q hQ hQ' => h Q hQ ((Sc.scTop_mono (S := S) hb hX (le_refl E)).trans hQ')

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE OWN PROPERTY OF `T` ABOVE EVERY LEVEL**: codes above the level `k + 2` over every `Q ≥ T₀` go to codes
above the level `k + 1` over every `Q ≥ Θ(T₀)`. -/
theorem vkOwn (k : ℕ) : ∀ x, VbD S l x → ∀ T0, SC T0 → T0 < Om (1 + 1) →
    (∀ Q, SC Q → T0 ≤ Q → VkA ((k : Ordinal.{0}) + 1 + 1) Q x) →
    ∀ Q, SC Q → gxTh (upsilon l) (ldAtR S l) T0 ≤ Q → VkA ((k : Ordinal.{0}) + 1) Q (vbT S l x) := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx T0 hT0 hT2 hcl Q hQ hTQ
  rcases lt_or_ge x (Om (1 + 1)) with hx2 | hx2
  · -- a code `x < Ω₂`: `x < T₀`
    have hxK : x < Om ((k : Ordinal.{0}) + 1 + 1) :=
      hx2.trans_le (Om_le_Om.2 (by gcongr; exact le_add_self))
    have hxT : x < T0 := vkA_lt_om hT0 (hcl T0 hT0 le_rfl) hxK
    rw [vbT_code hl hX hx2 hx.1]
    exact VkA.small ((gxTh_lt ((ldHull_iff hl hX hx2).1 hx.1) hxT).trans_le hTQ)
  have hx0 : x ≠ 0 := (ldOm2_SC.1.trans_le hx2).ne'
  have hxE := vbD_E hl hX hx
  by_cases hε : ω ^ x = x
  swap
  · -- the Cantor normal form
    have hlog : log ω x < x := by
      refine lt_of_le_of_ne (log_le_self ω x) fun e => hε ?_
      refine le_antisymm ?_ (right_le_opow x one_lt_omega0)
      calc ω ^ x = ω ^ log ω x := by rw [e]
        _ ≤ x := opow_log_le_self ω hx0
    obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
    have hpos : (0 : Ordinal.{0}) < n := hn ▸ div_opow_log_pos ω hx0
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (by rintro rfl; exact lt_irrefl _ hpos)
    have hdm : x = ω ^ log ω x * n + x % ω ^ log ω x := by
      rw [← hn]; exact (Ordinal.div_add_mod x _).symm
    have hs : x % ω ^ log ω x < ω ^ log ω x := Ordinal.mod_lt x (opow_pos _ omega0_pos).ne'
    have hsx : x % ω ^ log ω x < x := hs.trans_le (opow_log_le_self ω hx0)
    obtain ⟨heD, -, -⟩ := vbD_log hx hxE
    obtain ⟨hsD, -, -⟩ := vbD_rem hx hxE
    have hecl : ∀ Q, SC Q → T0 ≤ Q → VkA ((k : Ordinal.{0}) + 1 + 1) Q (log ω x) :=
      fun Q hQ hTQ => (vkDec hQ x (hcl Q hQ hTQ)).2
    have hscl : ∀ Q, SC Q → T0 ≤ Q → VkA ((k : Ordinal.{0}) + 1 + 1) Q (x % ω ^ log ω x) :=
      fun Q hQ hTQ => vkA_mod hQ _ (hcl Q hQ hTQ)
    rw [(congrArg (vbT S l) hdm).trans (vhT_cnf hl hX n hn1 heD hsD hs)]
    exact VkA.add (vkA_mulNat hQ.1 (VkA.opow hQ.1 (IH _ hlog heD T0 hT0 hT2 hecl Q hQ hTQ)) n)
      (IH _ hsx hsD T0 hT0 hT2 hscl Q hQ hTQ)
  by_cases hS : SC x
  · -- a strongly critical code `≥ Ω_{k+2}`: its image is strongly critical and `≥ Ω_{k+1}`
    have hge := vkA_SC_ge x (hcl T0 hT0 le_rfl) hS (hT2.le.trans hx2)
    exact VkA.big (vbT_ge_lev hl hX hx k hge) (vbT_SC hl hX hx hx2 hS)
  -- a node `x = φ(a, b)`
  have hv : veblen (invVeblen₁ x) (invVeblen₂ x) = x := by rw [veblen_invVeblen₁_invVeblen₂, hε]
  have hb : invVeblen₂ x < x := by have := invVeblen₂_lt x; rwa [hε] at this
  have h0 : 0 < x := pos_iff_ne_zero.2 hx0
  have ha0 : 0 < invVeblen₁ x := by
    refine pos_iff_ne_zero.2 fun h => ?_
    rw [h, veblen_zero_apply] at hv
    have : invVeblen₂ x = x := (opow_right_inj one_lt_omega0).1 (hv.trans hε.symm)
    exact absurd this hb.ne
  have ha : invVeblen₁ x < x := by
    refine lt_of_le_of_ne (invVeblen₁_le x) fun e => ?_
    rw [e] at hv
    have hle : veblen x 0 ≤ x := (veblen_le_veblen_iff_right.2 zero_le).trans hv.le
    exact hS (Ru.ruSC_of_veblen h0 (le_antisymm hle (left_le_veblen x 0)))
  obtain ⟨haD, hbD, -⟩ := vbD_veb hx hxE hv hb
  have hacl : ∀ Q, SC Q → T0 ≤ Q → VkA ((k : Ordinal.{0}) + 1 + 1) Q (invVeblen₁ x) :=
    fun Q hQ hTQ => vkA_lev _ (hcl Q hQ hTQ) _ _ hv.symm hb
  have hbcl : ∀ Q, SC Q → T0 ≤ Q → VkA ((k : Ordinal.{0}) + 1 + 1) Q (invVeblen₂ x) :=
    fun Q hQ hTQ => vkA_arg hQ _ (hcl Q hQ hTQ) _ _ hv.symm hb
  rw [vbT_veb hl hX hx hv ha0.ne' hb hx2]
  exact VkA.phi (IH _ ha haD T0 hT0 hT2 hacl Q hQ hTQ) (IH _ hb hbD T0 hT0 hT2 hbcl Q hQ hTQ)

/-- **The own property above the level 2 on all of `D`.** -/
theorem vkOwn2 {x : Ordinal.{0}} (hx : VbD S l x) {T0 : Ordinal.{0}} (hT0 : SC T0) (hT2 : T0 < Om (1 + 1))
    (hcl : ∀ Q, SC Q → T0 ≤ Q → VkA (1 + 1) Q x) :
    ∀ Q, SC Q → gxTh (upsilon l) (ldAtR S l) T0 ≤ Q → VkA 1 Q (vbT S l x) := by
  have h := vkOwn hl hX 0 x hx T0 hT0 hT2 (by simpa using hcl)
  simpa using h

/-- **The own property from the closure condition above the level 2, on all of `D`.** -/
theorem vkOwnCL {E b X0 : Ordinal.{0}} (hE : VbD S l E) (h : VkCL S E b X0) :
    ∀ Q, SC Q → gxTh (upsilon l) (ldAtR S l) (S.psi (b + leWe (X0 + leWe E)) (Om (1 + 1))) ≤ Q →
      VkA 1 Q (vbT S l E) :=
  vkOwn2 hl hX hE (SC_psi (InR_Om_succ 1) _) (psi_lt (InR_Om_succ 1) _) h

end Rst

end Googology.Trans.PoR.InaccPsi.R2.Vk
