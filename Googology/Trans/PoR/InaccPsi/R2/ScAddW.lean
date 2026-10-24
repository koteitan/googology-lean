import Googology.Trans.PoR.InaccPsi.R2.ScDer

/-!
# The step `E₀ ↦ E₀ + Ω₂` on derived exponents, and `W·2`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `SQ_j = Sc.scSq` of the lifted shape.

* `scOwSq_mono` (the own predicate `Ow ∧ ζ < SQ_j` of a member is monotone);
* `scDer_addW` (**a derived exponent `E₀` with `Ω₂ ∣ E₀` gives `E₀ + Ω₂`**, image `Ê₀ + Ω₁`, the same own
  predicate: the members `E₀ + ζ` of the shape `pre E₀ (lin 0)` are derived by `succ` and `lim`, then `om`);
* `scDer_W2` (**`W·2 = Ω₂ + Ω₂` is derived**, image `Ω₁ + Ω₁`, own predicate `⊤`), `scLev_W2` (the top at
  `W^{Ω₂·2}` over every offset and base bound, by soundness);
* `scDer_Wsq` (**`W^2 = Ω₂^2` is derived**, image `Ω₁^2`: members `Ω₂·ζ` by `scDer_addW` and `lim`), `scLev_Wsq`.

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw

variable {S : InaccSeq.{0}}

/-- The own predicate `Ow ∧ ζ < SQ_j` of a member is monotone. -/
theorem scOwSq_mono {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {G : Ordinal.{0} → Ordinal.{0}} (hG : Monotone G)
    (hmono : ∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') (ζ : Ordinal.{0}) :
    ∀ b β X0 X0', (Ow b X0 ∧ ∃ j, ζ < scSq S G X0 b j) → b ≤ β → X0 ≤ X0' →
      (Ow β X0' ∧ ∃ j, ζ < scSq S G X0' β j) :=
  fun _ _ _ _ ⟨hO, j, hj⟩ hb hXX =>
    ⟨hmono _ _ _ _ hO hb hXX, j, hj.trans_le ((scSq_mono_base hG hb j).trans (scSq_mono_off hG hXX j))⟩

section Add

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **A derived exponent `E₀` with `Ω₂ ∣ E₀` gives `E₀ + Ω₂`** (image `Ê₀ + Ω₁`). -/
theorem scDer_addW {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {E0 Eh0 : Ordinal.{0}} (hD : ScDer S l Ow E0 Eh0)
    (hdv : Om (1 + 1) ∣ E0) : ScDer S l Ow (E0 + Om (1 + 1)) (Eh0 + Om 1) := by
  obtain ⟨-, hP⟩ := scDer_sound hl hX hD
  obtain ⟨hρSC, -⟩ := leRho hl hX
  set g : Ordinal.{0} → Ordinal.{0} := fun z => E0 + leWe 0 * z with hg
  set gh : Ordinal.{0} → Ordinal.{0} := fun v => Eh0 + leOe 0 * v with hgh
  have hg1 : g 1 = E0 + 1 := by simp only [hg, leWe_zero, one_mul]
  have hshp : ∀ b X0, Ow b X0 → ScShp S l g gh (E0 + leWe (0 + 1)) (Eh0 + leOe (0 + 1))
      (leTe S (X0 + leWe (g 1)) b) (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe (g 1)) b)) := by
    intro b X0 hO
    have hd := hP.dat b X0 hO
    have hY : S.psi (b + leWe (X0 + leWe E0)) (Om (1 + 1)) ≤ leTe S (X0 + leWe (g 1)) b := by
      rw [hg1]; exact scTop_mono le_rfl le_rfl le_self_add
    have hlin := scShp_lin hl hX (F := 0) (Fh := 0) (bot := leTe S (X0 + leWe (g 1)) b)
      (both := gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe (g 1)) b)) (CSet.zero_mem _ _)
      (CSet.zero_mem _ _) (CSet.zero_mem _ _) (fun Q hQ _ => LeCl.zero hQ.1) (fun Q hQ _ => LeCl.zero hQ.1)
    exact scShp_pre hl hX hlin hd.hull (CSet_mono le_rfl hY hd.mem) (CSet_mono le_rfl (gxTh_mono hY) hd.memh)
      (fun Q hQ hc => hd.cl Q hQ (hY.trans hc)) (fun Q hQ hc => hd.clh Q hQ ((gxTh_mono hY).trans hc))
      (k := Om (1 + 1) * (0 + 1)) rfl (by rw [zero_add, leWe_one]; exact hdv)
  have hGmo : Monotone (fun z => leWe (g z)) :=
    fun a c h => leWe_mono ((add_le_add_iff_left E0).2 (mul_le_mul_right h _))
  have hmono := hP.mono
  have hmem : ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → 1 ≤ ζ → ζ < Om (1 + 1) →
      ScDer S l (fun b X0 => Ow b X0 ∧ ∃ j, ζ < scSq S (fun z => leWe (g z)) X0 b j) (g ζ)
        (gh (gxTh (upsilon l) (ldAtR S l) ζ)) := by
    intro ζ
    induction ζ using WellFoundedLT.induction with
    | ind ζ IH =>
    intro hζ h1 hζW
    rcases zero_or_succ_or_isSuccLimit ζ with h0 | ⟨ζ0, hζ0⟩ | hlim
    · subst h0; exact absurd h1 (not_le.2 zero_lt_one)
    · rw [succ_eq_add_one] at hζ0
      subst hζ0
      have hζ0c := rqCode_pred hl hX hζ hζW
      have e1 : g (ζ0 + 1) = g ζ0 + 1 := by simp only [hg, leWe_zero, one_mul, add_assoc]
      have e2 : gh (gxTh (upsilon l) (ldAtR S l) (ζ0 + 1)) = gh (gxTh (upsilon l) (ldAtR S l) ζ0) + 1 := by
        simp only [hgh, leOe_zero, one_mul, rqTh_succ hl hX hζ0c, add_assoc]
      rw [e1, e2]
      rcases eq_or_ne ζ0 0 with rfl | h00
      · have e3 : g 0 = E0 := by simp only [hg, mul_zero, add_zero]
        have e4 : gh (gxTh (upsilon l) (ldAtR S l) 0) = Eh0 := by simp only [hgh, gxTh_zero, mul_zero, add_zero]
        rw [e3, e4]
        exact ScDer.weaken (ScDer.succ hD) (fun _ _ h => h.1) (scOwSq_mono hGmo hmono _)
      · have h10 : 1 ≤ ζ0 := Order.one_le_iff_ne_zero.2 h00
        exact ScDer.weaken (ScDer.succ (IH ζ0 (lt_add_one ζ0) hζ0c h10 ((lt_add_one ζ0).trans hζW)))
          (fun _ _ ⟨hO, j, hj⟩ => ⟨hO, j, (lt_add_one ζ0).trans hj⟩) (scOwSq_mono hGmo hmono _)
    · exact ScDer.lim hshp hmono hζ hζW hlim fun c hc hcζ =>
        IH (c + 1) (hlim.succ_lt hcζ) (rqCode_succ hl hX hc ((hlim.succ_lt hcζ).trans hζW)) le_add_self
          ((hlim.succ_lt hcζ).trans hζW)
  have h := ScDer.om hshp hmono hmem
  rwa [zero_add, leWe_one, leOe_one] at h

/-- **`W·2 = Ω₂ + Ω₂` is derived** (image `Ω₁ + Ω₁`). -/
theorem scDer_W2 : ScDer S l (fun _ _ => True) (Om (1 + 1) + Om (1 + 1)) (Om 1 + Om 1) :=
  scDer_addW hl hX (scDer_W hl hX) (dvd_refl _)

/-- **The top at `W^{Ω₂·2}` over every offset and base bound** (image `Ω^{Ω₁·2}`). -/
theorem scLev_W2 : ScLev S l (fun _ _ => True) (Om (1 + 1) + Om (1 + 1)) (Om 1 + Om 1) :=
  (scDer_sound hl hX (scDer_W2 hl hX)).1

/-- **`W^2 = Ω₂^2` is derived** (image `Ω₁^2`, own predicate `⊤`): the shape `ζ ↦ Ω₂·ζ` (`lin 1`), its members
`Ω₂·ζ` derived from `W` by `scDer_addW` at successors and `lim` at limit codes. -/
theorem scDer_Wsq : ScDer S l (fun _ _ => True) (leWe (1 + 1)) (leOe (1 + 1)) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  set g : Ordinal.{0} → Ordinal.{0} := fun z => leWe 1 * z with hg
  set gh : Ordinal.{0} → Ordinal.{0} := fun v => leOe 1 * v with hgh
  have h1H : (1 : Ordinal.{0}) ∈ cdHull S l := CSet.one_mem _ _
  have hshp : ∀ b X0 : Ordinal.{0}, (fun _ _ : Ordinal.{0} => True) b X0 → ScShp S l g gh (leWe (1 + 1)) (leOe (1 + 1))
      (leTe S (X0 + leWe (g 1)) b) (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe (g 1)) b)) :=
    fun b X0 _ => scShp_lin hl hX h1H (CSet.one_mem _ _) (CSet.one_mem _ _)
      (fun Q hQ _ => LeCl.small (gg_one_lt_of_SC hQ)) (fun Q hQ _ => LeCl.small (gg_one_lt_of_SC hQ))
  have hmono : ∀ b β X0 X0' : Ordinal.{0}, (fun _ _ : Ordinal.{0} => True) b X0 → b ≤ β → X0 ≤ X0' →
      (fun _ _ : Ordinal.{0} => True) β X0' :=
    fun _ _ _ _ _ _ _ => trivial
  have hGmo : Monotone (fun z => leWe (g z)) := fun a c h => leWe_mono (mul_le_mul_right h _)
  have hmem : ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → 1 ≤ ζ → ζ < Om (1 + 1) →
      ScDer S l (fun b X0 => (fun _ _ => True) b X0 ∧ ∃ j, ζ < scSq S (fun z => leWe (g z)) X0 b j) (g ζ)
        (gh (gxTh (upsilon l) (ldAtR S l) ζ)) := by
    intro ζ
    induction ζ using WellFoundedLT.induction with
    | ind ζ IH =>
    intro hζ h1 hζW
    rcases zero_or_succ_or_isSuccLimit ζ with h0 | ⟨ζ0, hζ0⟩ | hlim
    · subst h0; exact absurd h1 (not_le.2 zero_lt_one)
    · rw [succ_eq_add_one] at hζ0
      subst hζ0
      have hζ0c := rqCode_pred hl hX hζ hζW
      rcases eq_or_ne ζ0 0 with rfl | h00
      · have e1 : g (0 + 1) = Om (1 + 1) := by simp only [hg, zero_add, mul_one, leWe_one]
        have e2 : gh (gxTh (upsilon l) (ldAtR S l) (0 + 1)) = Om 1 := by
          simp only [hgh, zero_add, gxTh_small (gg_one_lt_of_SC hρSC).le, mul_one, leOe_one]
        rw [e1, e2]
        exact ScDer.weaken (scDer_W hl hX) (fun _ _ _ => trivial) (scOwSq_mono hGmo hmono _)
      · have h10 : 1 ≤ ζ0 := Order.one_le_iff_ne_zero.2 h00
        have e1 : g (ζ0 + 1) = g ζ0 + Om (1 + 1) := by simp only [hg, mul_add_one, leWe_one]
        have e2 : gh (gxTh (upsilon l) (ldAtR S l) (ζ0 + 1)) = gh (gxTh (upsilon l) (ldAtR S l) ζ0) + Om 1 := by
          simp only [hgh, rqTh_succ hl hX hζ0c, mul_add_one, leOe_one]
        rw [e1, e2]
        have hdv : Om (1 + 1) ∣ g ζ0 := by rw [hg]; simp only [leWe_one]; exact dvd_mul_right _ _
        exact ScDer.weaken (scDer_addW hl hX (IH ζ0 (lt_add_one ζ0) hζ0c h10 ((lt_add_one ζ0).trans hζW)) hdv)
          (fun _ _ ⟨hO, j, hj⟩ => ⟨hO, j, (lt_add_one ζ0).trans hj⟩) (scOwSq_mono hGmo hmono _)
    · exact ScDer.lim hshp hmono hζ hζW hlim fun c hc hcζ =>
        IH (c + 1) (hlim.succ_lt hcζ) (rqCode_succ hl hX hc ((hlim.succ_lt hcζ).trans hζW)) le_add_self
          ((hlim.succ_lt hcζ).trans hζW)
  exact ScDer.om hshp hmono hmem

/-- **The top at `W^{Ω₂^2}` over every offset and base bound** (image `Ω^{Ω₁^2}`). -/
theorem scLev_Wsq : ScLev S l (fun _ _ => True) (leWe (1 + 1)) (leOe (1 + 1)) :=
  (scDer_sound hl hX (scDer_Wsq hl hX)).1

end Add

end Googology.Trans.PoR.InaccPsi.R2.Sc
