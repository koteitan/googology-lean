import Googology.Trans.PoR.InaccPsi.R2.KxLim

/-!
# Kx: THE TOP LAW AT EVERY EXPONENT (`Zp.ZpTopLawAll`)

`Θ`, `T`, `D`, `A`, `Ku.KuN`, `Ku.KuLaw` as before.  One induction on `b ∈ KuN`:

* the quotient `b/Ω₃` is a limit: `Kx.kxLim`;
* `b = β' + Ω₃`, `Ω₃ ∣ β'`: the law at `β' + Ω₃` (`Xi.xiTopUp0`, `k = 0`); `β'` is in `D` (`b/Ω₃ = β'/Ω₃ + 1`) and
  normal: the first use by the collapse depth (`kwFUG`, the extraction `e ↦ Ω₃·(e/Ω₃) = β'` on `[β', b)`).

* `kwStarG`, `kwFUG` (**the first use for any extraction** at one collapse depth: `Kw.kwStar`, `Kw.kwFU` are the
  extraction of the exponent), `kxPred` (`β' ∈ Cl` from `β' + Ω₃ ∈ Cl`), `kxBase` (**the law at `β' + Ω₃`**),
  `kxTop` (**THE TOP LAW AT EVERY `b ∈ KuN`**), `kxTopLawAll` (**`Zp.ZpTopLawAll S`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Ku Googology.Trans.PoR.InaccPsi.R2.Kw

variable {S : InaccSeq.{0}}

/-- Every member of `Cl(b, s)` of depth `d` lies in `Cl(a₁, s)`, or `K` has a smaller depth, when every collapse
argument in `[a₁, b)` of depth `d` gives `K` at depth `d`. -/
theorem kwStarG {a₁ b s K : Ordinal.{0}}
    (hext : ∀ {d : ℕ} {e : Ordinal.{0}}, KwC S b s d e → a₁ ≤ e → e < b → KwC S b s d K) :
    ∀ {d : ℕ} {y : Ordinal.{0}}, KwC S b s d y → y ∈ S.CSet a₁ s ∨ ∃ d' < d, KwC S b s d' K := by
  intro d y hy
  induction hy with
  | small h => exact Or.inl (CSet.of_lt h)
  | zero => exact Or.inl (CSet.zero_mem _ _)
  | inacc n => exact Or.inl (CSet.I_mem _ _ n)
  | inaccW => exact Or.inl (CSet.Iw_mem _ _)
  | add _ _ ihx ihy =>
    rcases ihx with hx | hx
    · rcases ihy with hy | hy
      · exact Or.inl (CSet.add_mem hx hy)
      · exact Or.inr hy
    · exact Or.inr hx
  | phi _ _ ihx ihy =>
    rcases ihx with hx | hx
    · rcases ihy with hy | hy
      · exact Or.inl (CSet.phi_mem hx hy)
      · exact Or.inr hy
    · exact Or.inr hx
  | om _ ih =>
    rcases ih with hx | hx
    · exact Or.inl (CSet.Om_mem hx)
    · exact Or.inr hx
  | @coll d π e hπ _ heC he ihπ ihe =>
    rcases lt_or_ge e a₁ with hea | hea
    · rcases ihπ with hπ' | ⟨d', hd', h'⟩
      · rcases ihe with he' | ⟨d', hd', h'⟩
        · exact Or.inl (CSet.psi_mem hea hπ hπ' he')
        · exact Or.inr ⟨d', hd'.trans (lt_add_one d), h'⟩
      · exact Or.inr ⟨d', hd'.trans (lt_add_one d), h'⟩
    · exact Or.inr ⟨d, lt_add_one d, hext heC hea he⟩
  | @up d _ _ ih =>
    rcases ih with hx | ⟨d', hd', h'⟩
    · exact Or.inl hx
    · exact Or.inr ⟨d', hd'.trans (lt_add_one d), h'⟩

/-- **THE FIRST USE FOR ANY EXTRACTION**: `K ∈ Cl(b, ψ₂ b)` gives `K ∈ Cl(a₁, ψ₂ a₁)`. -/
theorem kwFUG {a₁ b K : Ordinal.{0}}
    (hext : ∀ {d : ℕ} {e : Ordinal.{0}}, KwC S b (S.psi a₁ (Om (1 + 1))) d e → a₁ ≤ e → e < b →
      KwC S b (S.psi a₁ (Om (1 + 1))) d K)
    (hK : K ∈ S.CSet b (S.psi b (Om (1 + 1)))) : K ∈ S.CSet a₁ (S.psi a₁ (Om (1 + 1))) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  set s := S.psi a₁ (Om (1 + 1)) with hsdef
  have hKb : K ∈ S.CSet b s := by
    by_contra hne
    have hsub : S.CSet b s ⊆ S.CSet a₁ s := by
      intro y hy
      obtain ⟨d, hd⟩ := CSet_kwC hy
      rcases kwStarG hext hd with h | ⟨d', _, h'⟩
      · exact h
      · exact absurd (kwC_CSet h') hne
    have hψ : S.psi b (Om (1 + 1)) ≤ s :=
      psi_le_of_good (mxOm2_mem _ _) fun x hx hx2 => lt_psi_of_mem hκ2 (hsub hx) hx2
    exact hne (CSet_mono le_rfl hψ hK)
  obtain ⟨d, hd⟩ := CSet_kwC hKb
  classical
  have hex : ∃ d, KwC S b s d K := ⟨d, hd⟩
  rcases kwStarG hext (Nat.find_spec hex) with h | ⟨d', hd', h'⟩
  · exact h
  · exact absurd h' (Nat.find_min hex hd')

theorem kx3SC : SC (Om (1 + 1 + 1 : Ordinal.{0})) := SC_Om (add_pos_of_nonneg_of_pos zero_le zero_lt_one).ne'

theorem kx3e : ω ^ Om (1 + 1 + 1 : Ordinal.{0}) = Om (1 + 1 + 1) := gg_SC_eps kx3SC

theorem kxO3 (x y : Ordinal.{0}) : Om (1 + 1 + 1 : Ordinal.{0}) ∈ S.CSet x y :=
  CSet.Om_mem (CSet.succ_mem (CSet.succ_mem (CSet.one_mem x y)))

/-- `(Ω₃·q + r)/Ω₃ = q` for `r < Ω₃`. -/
theorem kxDiv {q e : Ordinal.{0}} (h1 : Om (1 + 1 + 1) * q ≤ e) (h2 : e < Om (1 + 1 + 1) * q + Om (1 + 1 + 1)) :
    e / Om (1 + 1 + 1) = q := by
  have h30 : Om (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := kx3SC.1.ne'
  refine le_antisymm ?_ ?_
  · have : e < Om (1 + 1 + 1) * (q + 1) := by rwa [mul_add_one]
    exact Order.lt_add_one_iff.1 ((Ordinal.lt_mul_iff_div_lt h30).1 this)
  · exact not_lt.1 fun h => absurd h1 (not_le.2 ((Ordinal.lt_mul_iff_div_lt h30).2 h))

/-- `β' ∈ Cl` from `β' + Ω₃ ∈ Cl`, `Ω₃ ∣ β'`. -/
theorem kxPred {β' a c : Ordinal.{0}} (h3 : Om (1 + 1 + 1) ∣ β') (hb : β' + Om (1 + 1 + 1) ∈ S.CSet a c) :
    β' ∈ S.CSet a c := by
  have h30 : Om (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := kx3SC.1.ne'
  obtain ⟨q, rfl⟩ := h3
  rw [← mul_add_one] at hb
  have hq := (Vh.vhC_div _ hb (Om (1 + 1 + 1))).2.2 (kxO3 a c)
  rw [kx3e, Ordinal.mul_div_cancel _ h30] at hq
  have h := leMulWe_mem (kxO3 a c) (mem_of_add_one_mem hq)
  rwa [Vn.vnWe_Om3] at h

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hl hX hA hρ

/-- **The law at `β' + Ω₃`**, `Ω₃ ∣ β'`. -/
theorem kxBase {β' : Ordinal.{0}} (h3 : Om (1 + 1 + 1) ∣ β') (hb : KuN S l (β' + Om (1 + 1 + 1))) :
    KuLaw S l A (β' + Om (1 + 1 + 1)) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hbD, hbn, -, -⟩ := hb
  have hβD : VbD S l β' := ⟨kxPred h3 hbD.1, kxPred h3 hbD.2.1, le_self_add.trans_lt hbD.2.2⟩
  have hβm : β' ∈ S.CSet (β' + Om (1 + 1 + 1)) (S.psi (β' + Om (1 + 1 + 1)) (Om (1 + 1))) := kxPred h3 hbn
  have hβn : β' ∈ S.CSet β' (S.psi β' (Om (1 + 1))) := by
    refine kwFUG (a₁ := β') (b := β' + Om (1 + 1 + 1)) (K := β') (fun {d e} he h1 h2 => ?_) hβm
    obtain ⟨q, hq⟩ := h3
    have h := (kwC_div e he (Om (1 + 1 + 1))).1
    rw [kx3e, kxDiv (hq ▸ h1) (hq ▸ h2), ← hq] at h
    exact h
  have hB : Ro.RoBaseE S l (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1)) 0 β' := by
    have e0 : Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) = Om (1 + 1 + 1) := by rw [Nat.cast_zero, zero_add]
    unfold Ro.RoBaseE
    rw [e0, add_zero, Vn.vnWe_Om3]
    refine ⟨h3, hβD.1, hbD.2.2.trans_le (ConjT.OmW_le_A S _), fun d _ => ?_, fun e' _ he' => ?_⟩
    · exact CSet_mono le_self_add (psi_mono hκ2 le_self_add).1 hβn
    · rw [nonpos_iff_eq_zero.1 he']
      exact (SC_psi hκ2 _).1
  have h := Xi.xiTopUp0 hl hX hA hρ 0 hβD hB
  unfold leTe at h
  rw [Nat.cast_zero, zero_add, add_zero, Vn.vnWe_Om3] at h
  unfold KuLaw
  exact h

/-- **THE TOP LAW AT EVERY `b ∈ KuN`.** -/
theorem kxTop : ∀ b, KuN S l b → KuLaw S l A b := by
  have h30 : Om (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := kx3SC.1.ne'
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb
  by_cases hq : ∀ y, y < b → Om (1 + 1 + 1) * (y / Om (1 + 1 + 1)) + Om (1 + 1 + 1) < b
  · exact kxLim hl hX hA hρ hb hq fun a ha hab => IH a hab ha
  · push Not at hq
    obtain ⟨y, hyb, hle⟩ := hq
    obtain ⟨q, hbq⟩ := hb.2.2.1
    have hlt : y / Om (1 + 1 + 1) < q := (Ordinal.lt_mul_iff_div_lt h30).1 (hbq ▸ hyb)
    have hle' : Om (1 + 1 + 1) * (y / Om (1 + 1 + 1)) + Om (1 + 1 + 1) ≤ b := by
      rw [hbq, ← mul_add_one]; exact mul_le_mul_right (Order.add_one_le_of_lt hlt) _
    have heq := le_antisymm hle' hle
    rw [← heq] at hb ⊢
    exact kxBase hl hX hA hρ (dvd_mul_right _ _) hb

end Main

/-- **THE TOP LAW AT EVERY EXPONENT** (`Zp.ZpTopLawAll`, the leaf `skTopLawAll`). -/
theorem kxTopLawAll (S : InaccSeq.{0}) : Zp.ZpTopLawAll S :=
  fun _ _ _ hl hX hA hρ b hbD hbn hb3 hb3le => kxTop hl hX hA hρ b ⟨hbD, hbn, hb3, hb3le⟩

end Googology.Trans.PoR.InaccPsi.R2.Kx

#print axioms Googology.Trans.PoR.InaccPsi.R2.Kx.kxBase
#print axioms Googology.Trans.PoR.InaccPsi.R2.Kx.kxTopLawAll
