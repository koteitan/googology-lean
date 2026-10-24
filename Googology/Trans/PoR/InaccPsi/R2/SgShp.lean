import Googology.Trans.PoR.InaccPsi.R2.SgTm

/-!
# Path shapes: the linear shape carried through a context

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(b) = ψ_{Ω₂}(b + W^E)`.

* `sgCat` (**concatenation** `A ⊕ B` of terms, value `A + B`), `sgV_cat`, `sgI_cat`, `sgWF_cat`, `sgOwn_cat`;
* `SgDatC` (the data of the prefixes of a context above the bottoms), `sgOwnC_dat` (**own prefixes have the
  data above `T_{X₀ + W^{K(y)}}(b)` for every `y`**);
* `sgShp_ctx` (**a shape carried through a context is a shape**: `pfx` by `Sg.sgShp_preG`, `lft` by
  `Sc.scShp_lift`), `sgShp_path` (**the path shape `ζ ↦ K(W^F·ζ)`** (top `K(W^{F+1})`) at the bottom
  `T_{X₀ + W^{K(W^F)}}(b)`, for an own context `K` and an own exponent term `F`).

No new axiom.  New definitions: `sgCat`, `SgDatC`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc

/-- **Concatenation** of terms: the value of `A ⊕ B` is `A + B`. -/
def sgCat : SgT → SgT → SgT
  | A, .zero => A
  | A, .term P R c => .term (sgCat A P) R c

/-- **The data of the prefixes of a context** above the bottoms. -/
def SgDatC (S : InaccSeq.{0}) (l bot both : Ordinal.{0}) : SgC → Prop
  | .hole => True
  | .pfx K Q => SgDatC S l bot both K ∧ sgV Q ∈ cdHull S l ∧ sgV Q ∈ S.CSet 0 bot ∧ sgI S l Q ∈ S.CSet 0 both ∧
      (∀ Q', SC Q' → bot ≤ Q' → LeCl (Om (1 + 1)) Q' (sgV Q)) ∧ (∀ Q', SC Q' → both ≤ Q' → LeCl (Om 1) Q' (sgI S l Q))
  | .lft K => SgDatC S l bot both K

variable {S : InaccSeq.{0}}

theorem sgV_cat (A : SgT) : ∀ B : SgT, sgV (sgCat A B) = sgV A + sgV B
  | .zero => (add_zero _).symm
  | .term P R c => by
    show sgV (sgCat A P) + leWe (sgV R) * c = sgV A + (sgV P + leWe (sgV R) * c)
    rw [sgV_cat A P, add_assoc]

theorem sgI_cat (l : Ordinal.{0}) (A : SgT) : ∀ B : SgT, sgI S l (sgCat A B) = sgI S l A + sgI S l B
  | .zero => (add_zero _).symm
  | .term P R c => by
    show sgI S l (sgCat A P) + leOe (sgI S l R) * gxTh (upsilon l) (ldAtR S l) c =
      sgI S l A + (sgI S l P + leOe (sgI S l R) * gxTh (upsilon l) (ldAtR S l) c)
    rw [sgI_cat l A P, add_assoc]

theorem sgWF_cat {l : Ordinal.{0}} {A : SgT} (hA : SgWF S l A) : ∀ B : SgT, SgWF S l B → SgWF S l (sgCat A B)
  | .zero, _ => hA
  | .term P R c, ⟨hP, hR, hc⟩ => ⟨sgWF_cat hA P hP, hR, hc⟩

/-- The own predicate of a concatenation. -/
theorem sgOwn_cat {b X0 : Ordinal.{0}} {A : SgT} : ∀ (B : SgT) (e : Ordinal.{0} → Ordinal.{0}), Monotone e →
    SgOwn S b X0 e A → SgOwn S b X0 (fun y => e (sgV A + y)) B → SgOwn S b X0 e (sgCat A B)
  | .zero, _, _, hA, _ => hA
  | .term P R c, e, he, hA, ⟨hP, hR, hc⟩ => by
    have eV := sgV_cat A P
    refine ⟨sgOwn_cat P e he hA hP, ?_, ?_⟩
    · refine sgOwn_mono le_rfl le_rfl R _ _
        (fun _ _ h => he ((add_le_add_iff_left _).2 ((add_le_add_iff_left _).2 (leWe_mono h))))
        (fun _ _ h => he ((add_le_add_iff_left _).2 (leWe_mono h))) (fun y => ?_) hR
      show e (sgV A + (sgV P + leWe y)) ≤ e (sgV (sgCat A P) + leWe y)
      rw [eV, add_assoc]
    · refine sgLimC_mono (fun _ _ h => he ((add_le_add_iff_left _).2 ((add_le_add_iff_left _).2 (leMulWe_mono h))))
        (fun _ _ h => he ((add_le_add_iff_left _).2 (leMulWe_mono h))) (fun z => ?_) le_rfl le_rfl hc
      show e (sgV A + (sgV P + leWe (sgV R) * z)) ≤ e (sgV (sgCat A P) + leWe (sgV R) * z)
      rw [eV, add_assoc]

section Ctx

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **Own prefixes have the data above `T_{X₀ + W^{K(y)}}(b)` for every `y`.** -/
theorem sgOwnC_dat {b X0 : Ordinal.{0}} : ∀ K : SgC, SgWFC S l K → SgOwnC S b X0 K → ∀ y bot,
    S.psi (b + leWe (X0 + leWe (sgE K y))) (Om (1 + 1)) ≤ bot →
    SgDatC S l bot (gxTh (upsilon l) (ldAtR S l) bot) K
  | .hole, _, _, _, _, _ => trivial
  | .pfx K Q, ⟨hKw, hQw⟩, ⟨hKo, hQo⟩, y, bot, hbot => by
    have hle : S.psi (b + leWe (X0 + leWe (sgE K (sgV Q)))) (Om (1 + 1)) ≤ bot :=
      ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left b).2 (leWe_mono
        ((add_le_add_iff_left X0).2 (leWe_mono (sgE_mono K (le_self_add : sgV Q ≤ sgV Q + y)))))))).1.trans hbot
    obtain ⟨h1, h2, h3, h4⟩ := sgDat Q (sgE K) (sgE_mono K) hQw hQo
    exact ⟨sgOwnC_dat K hKw hKo (sgV Q + y) bot hbot, sgV_hull hl hX Q hQw, h1 bot hle,
      h2 _ (gxTh_mono hle), fun Q' hQ' h => h3 Q' hQ' (hle.trans h),
      fun Q' hQ' h => h4 Q' hQ' ((gxTh_mono hle).trans h)⟩
  | .lft K, hKw, hKo, y, bot, hbot => sgOwnC_dat K hKw hKo (leWe y) bot hbot

/-- **A shape carried through a context is a shape.** -/
theorem sgShp_ctx {bot both : Ordinal.{0}} : ∀ K : SgC, SgDatC S l bot both K →
    ∀ (g gh : Ordinal.{0} → Ordinal.{0}) (gs ghs : Ordinal.{0}), ScShp S l g gh gs ghs bot both →
    ScShp S l (fun z => sgE K (g z)) (fun v => sgEh S l K (gh v)) (sgE K gs) (sgEh S l K ghs) bot both
  | .hole, _, _, _, _, _, h => h
  | .pfx K Q, ⟨hK, hH, hm, hmh, hcl, hclh⟩, g, gh, gs, ghs, h =>
    sgShp_ctx K hK _ _ _ _ (sgShp_preG hl hX h hH hm hmh hcl hclh)
  | .lft K, hK, g, gh, gs, ghs, h => sgShp_ctx K hK _ _ _ _ (scShp_lift hl hX h)

/-- **The path shape `ζ ↦ K(W^F·ζ)`** at the bottom `T_{X₀ + W^{K(W^F·1)}}(b)`. -/
theorem sgShp_path {b X0 : Ordinal.{0}} {K : SgC} {F : SgT} (hKw : SgWFC S l K) (hFw : SgWF S l F)
    (hKo : SgOwnC S b X0 K) (hFo : SgOwn S b X0 (fun r => sgE K (leWe r)) F) :
    ScShp S l (fun z => sgE K (leWe (sgV F) * z)) (fun v => sgEh S l K (leOe (sgI S l F) * v))
      (sgE K (leWe (sgV F + 1))) (sgEh S l K (leOe (sgI S l F + 1)))
      (leTe S (X0 + leWe ((fun z => sgE K (leWe (sgV F) * z)) 1)) b)
      (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe ((fun z => sgE K (leWe (sgV F) * z)) 1)) b)) := by
  set bot := leTe S (X0 + leWe ((fun z => sgE K (leWe (sgV F) * z)) 1)) b with hbot
  have hbot' : S.psi (b + leWe (X0 + leWe (sgE K (leWe (sgV F) * 1)))) (Om (1 + 1)) ≤ bot := le_rfl
  have hD := sgOwnC_dat hl hX K hKw hKo _ bot hbot'
  have heF : Monotone (fun r => sgE K (leWe r)) := fun _ _ h => sgE_mono K (leWe_mono h)
  obtain ⟨h1, h2, h3, h4⟩ := sgDat (l := l) F _ heF hFw hFo
  have hle : S.psi (b + leWe (X0 + leWe ((fun r => sgE K (leWe r)) (sgV F)))) (Om (1 + 1)) ≤ bot := by
    rw [hbot]; unfold leTe; simp only [mul_one]; exact le_rfl
  have hlin := scShp_lin hl hX (F := sgV F) (Fh := sgI S l F) (bot := bot)
    (both := gxTh (upsilon l) (ldAtR S l) bot) (sgV_hull hl hX F hFw) (h1 bot hle) (h2 _ (gxTh_mono hle))
    (fun Q hQ h => h3 Q hQ (hle.trans h)) (fun Q hQ h => h4 Q hQ ((gxTh_mono hle).trans h))
  exact sgShp_ctx hl hX K hD _ _ _ _ hlin

end Ctx

end Googology.Trans.PoR.InaccPsi.R2.Sg
