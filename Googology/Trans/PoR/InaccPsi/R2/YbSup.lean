import Googology.Trans.PoR.InaccPsi.R2.YbLev

/-!
# The repaired carry is never silent at a small reach

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Xo.XoCarry` bounds only the images of decompositions restricted at the chosen `μ` (`Xo.XoR`).  With the covering
lemma (`Yb.ybCover`), the supply clause `Xo.XoSup` can always be called with a configuration (a bound `γ` above the
tails, a finite offset set `Os` containing the offsets of chosen decompositions) such that **every** inner reach
`r(λ+g) < υ_{λ+β}` with `g` in a given finite set gets an image bound from the carry: `ybSup_bound`.  So a realizer
built from `Xo.XoSup` (the open bridge `Xo.XoRealB`) has carry information at every small reach it meets.

* `ybReach_choice` (one covered decomposition, tail and offset set per offset `g`);
* `ybSup_bound` (**the non-silent supply**, under `Yb.YbLevK`);
* `ybSup_bound_IF` (the same under the notation statement `Yb.YbIF` alone).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **One covered decomposition per offset**, with its tail and its offset set. -/
theorem ybReach_choice {l β : Ordinal.{0}} (hl0 : 0 < l) (hb1 : upsilon (l + β) ≤ Om1) (hK : YbLevK S l β)
    (g : Ordinal.{0}) :
    ∃ O : Finset Ordinal.{0}, ∃ γ, γ < upsilon l ∧ (∀ d ∈ O, d < β) ∧
      (cdR S (l + g) < upsilon (l + β) → ∃ E : Xo.XoE, Xo.XoWF S l β E ∧ Xo.xoVal S l E = cdR S (l + g) ∧
        (∀ μ, γ < upsilon μ → Bases (upsilon μ) (upsilon l) → Xo.XoR S l μ E) ∧
        ∀ Os : Finset Ordinal.{0}, O ⊆ Os → Xo.XoOs l Os E) := by
  by_cases hs : cdR S (l + g) < upsilon (l + β)
  · obtain ⟨E, hW, hv, -, ⟨γ, hγ, hR⟩, ⟨O, hO, hO'⟩⟩ := ybCover hl0 hK _ hs (hs.trans_le hb1)
    exact ⟨O, γ, hγ, hO, fun _ => ⟨E, hW, hv, hR, hO'⟩⟩
  · exact ⟨∅, 0, yb_ups_pos hl0, by simp, fun h => absurd h hs⟩

/-- **The non-silent supply**: from `Xo.XoSup S λ β` and `YbLevK`, for every `γ < υ_λ` and every finite set `G` of
offsets below `β` there is a supply configuration `(μ, f, B, Os ⊇ G)` above `γ` whose carry bounds the image of a
restricted decomposition of EVERY inner reach `r(λ+g) < υ_{λ+β}`, `g ∈ G`, `0 < g`, `ω² ∣ g`. -/
theorem ybSup_bound {l β : Ordinal.{0}} (hl0 : 0 < l) (hb1 : upsilon (l + β) ≤ Om1) (hl1 : upsilon l < Om1)
    (hK : YbLevK S l β) (hS : Xo.XoSup S l β) :
    ∀ γ < upsilon l, ∀ G : Finset Ordinal.{0}, (∀ d ∈ G, d < β) →
      ∃ μ f B, ∃ Os : Finset Ordinal.{0}, G ⊆ Os ∧ CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧
        μ + B ≤ l ∧ ω ^ 2 ∣ B ∧ upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧ Xo.XoCarry S l β μ f B Os ∧
        ∀ g ∈ G, 0 < g → ω ^ 2 ∣ g → cdR S (l + g) < upsilon (l + β) →
          ∃ E : Xo.XoE, Xo.XoWF S l β E ∧ Xo.xoVal S l E = cdR S (l + g) ∧ Xo.XoR S l μ E ∧
            Xo.xoImg S l μ f E ≤ cdR S (μ + f g) := by
  intro γ hγ G hG
  choose O γf hγf hO hE using ybReach_choice (S := S) hl0 hb1 hK
  set Os := G ∪ G.biUnion O with hOsdef
  have hOs : ∀ d ∈ Os, d < β := by
    intro d hd
    rcases Finset.mem_union.1 hd with h | h
    · exact hG d h
    · obtain ⟨g, -, hg⟩ := Finset.mem_biUnion.1 h
      exact hO g d hg
  have hsup : G.sup γf < upsilon l := (Finset.sup_lt_iff (yb_ups_pos hl0)).2 fun g _ => hγf g
  have h0l : upsilon 0 < upsilon l := upsilon_normal.strictMono hl0
  set γ' := max (max γ (upsilon 0)) (G.sup γf) with hγ'def
  have hγ' : γ' < upsilon l := max_lt (max_lt hγ h0l) hsup
  obtain ⟨μ, f, B, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hS γ' hγ' Os hOs
  have hμ0 : 0 < μ := yb_mu_pos (((le_max_right γ _).trans (le_max_left _ _)).trans_lt h2)
  have hBs : Bases (upsilon μ) (upsilon l) :=
    ⟨upsPt_inE (upsPt_upsilon hμ0), upsPt_inE (upsPt_upsilon hl0), h3, hl1⟩
  refine ⟨μ, f, B, Os, Finset.subset_union_left, h1, ((le_max_left γ _).trans (le_max_left _ _)).trans_lt h2,
    h3, h4, h5, h6, h7, h8, fun g hg hg0 hgd hs => ?_⟩
  obtain ⟨E, hW, hv, hR, hEO⟩ := hE g hs
  have hRμ : Xo.XoR S l μ E :=
    hR μ (((Finset.le_sup (f := γf) hg).trans (le_max_right _ _)).trans_lt h2) hBs
  have hOE : Xo.XoOs l Os E :=
    hEO Os ((Finset.subset_biUnion_of_mem O hg).trans Finset.subset_union_right)
  exact ⟨E, hW, hv, hRμ, (h8 g (Finset.subset_union_left hg) hg0 hgd).2.2 E hW hv hOE hRμ⟩

/-- **The non-silent supply under the notation statement `YbIF` alone.** -/
theorem ybSup_bound_IF {l β : Ordinal.{0}} (hl0 : 0 < l) (hb1 : upsilon (l + β) ≤ Om1) (hl1 : upsilon l < Om1)
    (hIF : YbIF S) (hS : Xo.XoSup S l β) :
    ∀ γ < upsilon l, ∀ G : Finset Ordinal.{0}, (∀ d ∈ G, d < β) →
      ∃ μ f B, ∃ Os : Finset Ordinal.{0}, G ⊆ Os ∧ CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧
        μ + B ≤ l ∧ ω ^ 2 ∣ B ∧ upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧ Xo.XoCarry S l β μ f B Os ∧
        ∀ g ∈ G, 0 < g → ω ^ 2 ∣ g → cdR S (l + g) < upsilon (l + β) →
          ∃ E : Xo.XoE, Xo.XoWF S l β E ∧ Xo.xoVal S l E = cdR S (l + g) ∧ Xo.XoR S l μ E ∧
            Xo.xoImg S l μ f E ≤ cdR S (μ + f g) :=
  ybSup_bound hl0 hb1 hl1 (ybLevK_of_IF hl0 hb1 hIF) hS

end Googology.Trans.PoR.InaccPsi.R2.Yb
