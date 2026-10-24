import Googology.Trans.PoR.InaccPsi.R2.SwTm

/-!
# Shapes through contexts with leaves

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(b) = ψ_{Ω₂}(b + W^E)`, terms and contexts of `Sw.SwT`,
`Sw.SwC`.

* `SwDatC` (the data of the prefixes of a context above the bottoms), `swOwnC_dat` (**own prefixes have the data
  above `T_{X₀ + W^{K(y)}}(b)`**), `swShp_ctx` (**a shape carried through a context is a shape**, `Sg.sgShp_preG`
  and `Sc.scShp_lift`), `swShp_path` (**the path shape `ζ ↦ K(W^F·ζ)`** for every own term `F`, leaves included);
* `swDatE` (**the data of `K(y)` from the data of `K` and of `y`**), `swOwP_ctx` (**the own data `Sc.ScOwP` of
  `K(y)`** for a closed `y` such as a leaf).

No new axiom.  New definition: `SwDatC`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg

variable {S : InaccSeq.{0}}

/-- **The data of the prefixes of a context** above the bottoms. -/
def SwDatC (S : InaccSeq.{0}) (l bot both : Ordinal.{0}) : SwC → Prop
  | .hole => True
  | .pfx K Q => SwDatC S l bot both K ∧ swV Q ∈ cdHull S l ∧ swV Q ∈ S.CSet 0 bot ∧ swI S l Q ∈ S.CSet 0 both ∧
      (∀ Q', SC Q' → bot ≤ Q' → LeCl (Om (1 + 1)) Q' (swV Q)) ∧ (∀ Q', SC Q' → both ≤ Q' → LeCl (Om 1) Q' (swI S l Q))
  | .lft K => SwDatC S l bot both K

section Ctx

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **Own prefixes have the data above `T_{X₀ + W^{K(y)}}(b)` for every `y`.** -/
theorem swOwnC_dat {b X0 : Ordinal.{0}} : ∀ K : SwC, SwWFC S l K → SwOwnC S b X0 K → ∀ y bot,
    S.psi (b + leWe (X0 + leWe (swE K y))) (Om (1 + 1)) ≤ bot →
    SwDatC S l bot (gxTh (upsilon l) (ldAtR S l) bot) K
  | .hole, _, _, _, _, _ => trivial
  | .pfx K Q, ⟨hKw, hQw⟩, ⟨hKo, hQo⟩, y, bot, hbot => by
    have hle : S.psi (b + leWe (X0 + leWe (swE K (swV Q)))) (Om (1 + 1)) ≤ bot :=
      ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left b).2 (leWe_mono
        ((add_le_add_iff_left X0).2 (leWe_mono (swE_mono K (le_self_add : swV Q ≤ swV Q + y)))))))).1.trans hbot
    obtain ⟨h1, h2, h3, h4⟩ := swDat Q (swE K) (swE_mono K) hQw hQo
    exact ⟨swOwnC_dat K hKw hKo (swV Q + y) bot hbot, swV_hull hl hX Q hQw, h1 bot hle,
      h2 _ (gxTh_mono hle), fun Q' hQ' h => h3 Q' hQ' (hle.trans h),
      fun Q' hQ' h => h4 Q' hQ' ((gxTh_mono hle).trans h)⟩
  | .lft K, hKw, hKo, y, bot, hbot => swOwnC_dat K hKw hKo (leWe y) bot hbot

/-- **A shape carried through a context is a shape.** -/
theorem swShp_ctx {bot both : Ordinal.{0}} : ∀ K : SwC, SwDatC S l bot both K →
    ∀ (g gh : Ordinal.{0} → Ordinal.{0}) (gs ghs : Ordinal.{0}), ScShp S l g gh gs ghs bot both →
    ScShp S l (fun z => swE K (g z)) (fun v => swEh S l K (gh v)) (swE K gs) (swEh S l K ghs) bot both
  | .hole, _, _, _, _, _, h => h
  | .pfx K Q, ⟨hK, hH, hm, hmh, hcl, hclh⟩, g, gh, gs, ghs, h =>
    swShp_ctx K hK _ _ _ _ (sgShp_preG hl hX h hH hm hmh hcl hclh)
  | .lft K, hK, g, gh, gs, ghs, h => swShp_ctx K hK _ _ _ _ (scShp_lift hl hX h)

/-- **The path shape `ζ ↦ K(W^F·ζ)`** at the bottom `T_{X₀ + W^{K(W^F·1)}}(b)`. -/
theorem swShp_path {b X0 : Ordinal.{0}} {K : SwC} {F : SwT} (hKw : SwWFC S l K) (hFw : SwWF S l F)
    (hKo : SwOwnC S b X0 K) (hFo : SwOwn S b X0 (fun r => swE K (leWe r)) F) :
    ScShp S l (fun z => swE K (leWe (swV F) * z)) (fun v => swEh S l K (leOe (swI S l F) * v))
      (swE K (leWe (swV F + 1))) (swEh S l K (leOe (swI S l F + 1)))
      (leTe S (X0 + leWe ((fun z => swE K (leWe (swV F) * z)) 1)) b)
      (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe ((fun z => swE K (leWe (swV F) * z)) 1)) b)) := by
  set bot := leTe S (X0 + leWe ((fun z => swE K (leWe (swV F) * z)) 1)) b with hbot
  have hbot' : S.psi (b + leWe (X0 + leWe (swE K (leWe (swV F) * 1)))) (Om (1 + 1)) ≤ bot := le_rfl
  have hD := swOwnC_dat hl hX K hKw hKo _ bot hbot'
  have heF : Monotone (fun r => swE K (leWe r)) := fun _ _ h => swE_mono K (leWe_mono h)
  obtain ⟨h1, h2, h3, h4⟩ := swDat (l := l) F _ heF hFw hFo
  have hle : S.psi (b + leWe (X0 + leWe ((fun r => swE K (leWe r)) (swV F)))) (Om (1 + 1)) ≤ bot := by
    rw [hbot]; unfold leTe; simp only [mul_one]; exact le_rfl
  have hlin := scShp_lin hl hX (F := swV F) (Fh := swI S l F) (bot := bot)
    (both := gxTh (upsilon l) (ldAtR S l) bot) (swV_hull hl hX F hFw) (h1 bot hle) (h2 _ (gxTh_mono hle))
    (fun Q hQ h => h3 Q hQ (hle.trans h)) (fun Q hQ h => h4 Q hQ ((gxTh_mono hle).trans h))
  exact swShp_ctx hl hX K hD _ _ _ _ hlin

omit hl hX in
/-- **The data of `K(y)`** from the data of the prefixes of `K` and of `y`. -/
theorem swDatE {bot both : Ordinal.{0}} : ∀ K : SwC, SwDatC S l bot both K → ∀ y yh,
    y ∈ cdHull S l → y ∈ S.CSet 0 bot → yh ∈ S.CSet 0 both →
    (∀ Q, SC Q → bot ≤ Q → LeCl (Om (1 + 1)) Q y) → (∀ Q, SC Q → both ≤ Q → LeCl (Om 1) Q yh) →
    swE K y ∈ cdHull S l ∧ swE K y ∈ S.CSet 0 bot ∧ swEh S l K yh ∈ S.CSet 0 both ∧
      (∀ Q, SC Q → bot ≤ Q → LeCl (Om (1 + 1)) Q (swE K y)) ∧ (∀ Q, SC Q → both ≤ Q → LeCl (Om 1) Q (swEh S l K yh))
  | .hole, _, _, _, h1, h2, h3, h4, h5 => ⟨h1, h2, h3, h4, h5⟩
  | .pfx K Q, ⟨hK, hH, hm, hmh, hcl, hclh⟩, y, yh, h1, h2, h3, h4, h5 =>
    swDatE K hK _ _ (CSet.add_mem hH h1) (CSet.add_mem hm h2) (CSet.add_mem hmh h3)
      (fun Q' hQ' hb => LeCl.add (hcl Q' hQ' hb) (h4 Q' hQ' hb))
      (fun Q' hQ' hb => LeCl.add (hclh Q' hQ' hb) (h5 Q' hQ' hb))
  | .lft K, hK, y, yh, h1, h2, h3, h4, h5 =>
    swDatE K hK _ _ (leWe_mem h1) (leWe_mem h2) (leOe_mem h3)
      (fun Q' hQ' hb => LeCl.opow hQ'.1 (LeCl.mulK hQ' ldOm2_SC _ (h4 Q' hQ' hb)))
      (fun Q' hQ' hb => LeCl.opow hQ'.1 (LeCl.mulK hQ' Ph.ph_SC_Om1 _ (h5 Q' hQ' hb)))

/-- **The own data of `K(y)`** under an own predicate that gives the prefixes of `K`, for `y` a code over every
`Q` (such as a leaf) with `1 ≤ K(y)`. -/
theorem swOwP_ctx {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {K : SwC} {y yh : Ordinal.{0}} (hKw : SwWFC S l K)
    (hmono : ∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') (hown : ∀ b X0, Ow b X0 → SwOwnC S b X0 K)
    (hyH : y ∈ cdHull S l) (hym : ∀ c, y ∈ S.CSet 0 c) (hyhm : ∀ c, yh ∈ S.CSet 0 c)
    (hycl : ∀ Q, SC Q → LeCl (Om (1 + 1)) Q y) (hyhcl : ∀ Q, SC Q → LeCl (Om 1) Q yh) (h1 : 1 ≤ swE K y) :
    ScOwP S l Ow (swE K y) (swEh S l K yh) := by
  refine ⟨fun b X0 hOw => ?_, hmono⟩
  set T := S.psi (b + leWe (X0 + leWe (swE K y))) (Om (1 + 1))
  have hD := swOwnC_dat hl hX K hKw (hown b X0 hOw) y T le_rfl
  obtain ⟨a1, a2, a3, a4, a5⟩ := swDatE K hD y yh hyH (hym _) (hyhm _) (fun Q hQ _ => hycl Q hQ)
    (fun Q hQ _ => hyhcl Q hQ)
  exact ⟨h1, a1, a2, a3, a4, a5⟩

end Ctx

end Googology.Trans.PoR.InaccPsi.R2.Sw
