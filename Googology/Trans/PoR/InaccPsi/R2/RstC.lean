import Googology.Trans.PoR.InaccPsi.R2.BlockB

/-!
# The restarts below `υ_{ω³}` in `R₂^C`: Theorem B″, Lemma TOP, the blocks of every restart

Notation: `ρ = υ_{ω²·(h+1)}` (the restart), `τ = υ_{ω²·(h+1)+ω}`, `δ = υ_{ω²·(h+1)+ω+1}` (the top of the
first block of `ρ`).  All in `R₂^C` ([C09] Def 5.3–5.4).

* `chains_of`, `not_le2_gap_of`: Lemma L against clause 2 of [C09] Def 5.3, as standalone lemmas.
* `RstCtx ρ τ δ`: a restart context (no point below `ρ` is `≤₁` a point `≥ ρ`; landing blocks below `ρ`
  where `≤₁` is that of `R₁⁺`; the block tops below `ρ` are closed).
* In a restart context: `noSucc` (`ρ` has no `<₂`-successor), `le1ρ` (**Lemma C″ (a)**: `ρ ≤₁ γ` up to
  the least `<₂`-right end above `ρ`), `noPairGap` (no `<₂`-right end in `(ρ, δ)`), `pair` (`τ <₂ δ`),
  `le1ρδ` (**B″4**: `ρ ≤₁ γ` for `γ ∈ [ρ, δ]`), `lowδ` (SK1 in the restart block), `top` (**Lemma TOP**:
  `ρ` is not `≤₁` any `γ > δ + 1`), `T3succ` (no point `≤ δ + 1` is `≤₁` a point `> δ + 1`).
* `ctxA a T₀`: the block contexts after a lower end `T₀` with base index `a`
  (`τ_j = υ_{a+ω·j+ω}`, top `υ_{a+ω·j+ω+1}`).
* `rstCtx h`: the restart context of `ρ_{h+1}`, for every `h` (induction on `h`).
* `thmB2_C` (**Theorem B″ with TOP below `υ_{ω³}`**).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-! ## Lemma L against clause 2, standalone -/

/-- `≤₁`-chains of `υ`-points of `R₂^C` cofinal below `τ`, from `υ`-points cofinal below `τ` and
`≤₁ = ≤₁` of `R₁⁺` on `(T, τ]`. -/
theorem chains_of {T τ : Ordinal.{0}} (hTτ : T < τ)
    (hcof : ∀ c' < τ, ∃ u, UpsPt u ∧ c' < u ∧ u < τ)
    (hlow : ∀ a b, T < a → b ≤ τ → (le1 a b ↔ le1R a b)) :
    ∀ c' < τ, ∃ g : ℕ → Ordinal.{0}, StrictMono g ∧ (∀ i, Indec (g i)) ∧
      (∀ i, c' < g i ∧ g i < τ) ∧ ∀ i k, i ≤ k → le1 (g i) (g k) := by
  classical
  intro c' hc'
  let F : Ordinal.{0} → Ordinal.{0} := fun x => if hx : x < τ then Classical.choose (hcof x hx) else 0
  have hF : ∀ x < τ, UpsPt (F x) ∧ x < F x ∧ F x < τ := fun x hx => by
    simp only [F, dif_pos hx]; exact Classical.choose_spec (hcof x hx)
  let g : ℕ → Ordinal.{0} := fun i => Nat.rec (motive := fun _ => Ordinal.{0}) (F (max c' T))
    (fun _ y => F y) i
  have hm : max c' T < τ := max_lt hc' hTτ
  have hg : ∀ i, UpsPt (g i) ∧ max c' T < g i ∧ g i < τ := by
    intro i
    induction i with
    | zero => exact hF _ hm
    | succ i ih =>
      have := hF (g i) ih.2.2
      exact ⟨this.1, ih.2.1.trans this.2.1, this.2.2⟩
  have hgs : ∀ i, g i < g (i + 1) := fun i => (hF (g i) (hg i).2.2).2.1
  have hmono : StrictMono g := strictMono_nat_of_lt_succ hgs
  refine ⟨g, hmono, fun i => indec_of_upsPt (hg i).1,
    fun i => ⟨lt_of_le_of_lt (le_max_left _ _) (hg i).2.1, (hg i).2.2⟩, fun i k hik => ?_⟩
  refine (hlow (g i) (g k) (lt_of_le_of_lt (le_max_right _ _) (hg i).2.1) (hg k).2.2.le).2 ?_
  exact (hg i).1.2 _ (hmono.monotone hik)

/-- `τ <₂ d` fails for `d ∈ (τ, τ^∞)` when `R₂^C` has `≤₁`-chains of indecomposables cofinal below `τ`
(Lemma L against clause 2 of [C09] Def 5.3). -/
theorem not_le2_gap_of {τ β : Ordinal.{0}} (hτU : UpsPt τ) (hn : IsNext τ β) (hβ1 : β < Om1)
    (hch : ∀ c' < τ, ∃ g : ℕ → Ordinal.{0}, StrictMono g ∧ (∀ i, Indec (g i)) ∧
      (∀ i, c' < g i ∧ g i < τ) ∧ ∀ i k, i ≤ k → le1 (g i) (g k)) :
    ∀ d, τ < d → d < β → ¬ le2 τ d := by
  classical
  intro d hτd hdβ h2
  have hτ1 : τ < Om1 := hn.1.trans hβ1
  have hT : ∀ a, a < Om1 → (a ∈ Tset τ ↔ a < β) := by
    obtain ⟨m, hm, hT⟩ := exists_next hτU hτ1
    rw [← hm.unique hn]; exact hT
  have hd1 : d < Om1 := hdβ.trans hβ1
  set K := ht τ d + 2 with hK
  obtain ⟨f, hfM, hfI, -, -⟩ := hch 0 hτU.1
  have hZc : Closed (↑((Finset.range (K + 1)).image f) : Set Ordinal.{0}) :=
    closed_of_indec (by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
      exact hfI i)
  have hcof : CofCov R2C ∅ ((Finset.range (K + 1)).image f) chainP τ := by
    intro c' hc'
    obtain ⟨g, hgM, hgI, hgb, hg1⟩ := hch c' hc'
    obtain ⟨hh, hcov, -⟩ := cov_chain R2C K hfM hgM hfI hgI (fun i j hij _ => hg1 i j hij)
      le2_refl
    refine ⟨(Finset.range (K + 1)).image g, ?_, ?_, hh, ?_⟩
    · intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
      exact hgb i
    · rw [Finset.empty_union]
      exact closed_of_indec (by
        intro x hx
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
        exact hgI i)
    · rw [Finset.empty_union]; exact hcov
  obtain ⟨-, -, H2⟩ := le2_iff.1 h2
  have hcofd := H2 ∅ (by simp) _ chainP hZc hcof
  obtain ⟨Y, hY, -, hh, hcov⟩ := hcofd τ hτd
  have hmemZ : ∀ i ≤ K, f i ∈ (↑((Finset.range (K + 1)).image f) : Set Ordinal.{0}) :=
    fun i hi => Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩)
  have hzY : ∀ i ≤ K, τ < hh (f i) ∧ hh (f i) < d := by
    intro i hi
    have hm := hcov.1.1.mapsTo (hmemZ i hi)
    rw [Finset.coe_union, Finset.coe_empty, Set.empty_union] at hm
    exact hY _ (Finset.mem_coe.1 hm)
  have hch' : ∀ i < K, hh (f i) < hh (f (i + 1)) ∧ le1R (hh (f i)) (hh (f (i + 1))) := by
    intro i hi
    refine ⟨hcov.1.2.1 (hmemZ i hi.le) (hmemZ (i + 1) hi) (hfM (Nat.lt_succ_self i)), ?_⟩
    have h1 : le1 (hh (f i)) (hh (f (i + 1))) :=
      hcov.2.1 _ (hmemZ i hi.le) _ (hmemZ (i + 1) hi) (hfM.monotone (Nat.le_succ i))
    exact inc1 ((hzY (i + 1) hi).2.trans hd1) h1
  have hbound := chain_bound_gap (upsPt_inE hτU) hτ1 hT hdβ hd1 K
    (fun i => hh (f i)) (hzY 0 (Nat.zero_le K)).1 (hzY K le_rfl).2.le hch'
  omega

/-! ## Restart contexts -/

/-- A restart context `RstCtx ρ τ δ` (`ρ` the restart, `τ <₂ δ` the pair of its first block). -/
structure RstCtx (ρ τ δ : Ordinal.{0}) : Prop where
  ρU : UpsPt ρ
  ρτ : ρ < τ
  τU : UpsPt τ
  next : IsNext τ δ
  δ1 : δ < Om1
  below : ∀ c < ρ, ∀ g, ρ ≤ g → ¬ le1 c g
  land : ∀ c' < ρ, ∃ σ σ', UpsPt σ ∧ c' < σ ∧ IsNext σ σ' ∧ σ' < ρ ∧
    (∀ a b, σ < a → b < σ' → (le1 a b ↔ le1R a b)) ∧ (∀ b, σ ≤ b → b < σ' → le1 σ b) ∧
    (∀ c d, c < d → σ < d → d < σ' → ¬ le2 c d)
  capP : ∃ x0 < ρ, ∀ c d, x0 < c → c < d → d < ρ → le2 c d → ∀ x ≤ d, ∀ g, d < g → ¬ le1 x g
  left : ∀ l, IsSuccLimit l → ρ < upsilon l → upsilon l ≤ τ → upsilon l = τ
  cof : ∀ c' < τ, ∃ u, UpsPt u ∧ c' < u ∧ u < τ

namespace RstCtx

variable {ρ τ δ : Ordinal.{0}} (h : RstCtx ρ τ δ)
include h

theorem τ1 : τ < Om1 := h.next.1.trans h.δ1

theorem ρ1 : ρ < Om1 := h.ρτ.trans h.τ1

theorem τδ : τ < δ := h.next.1

/-- `ρ` has no `<₂`-successor. -/
theorem noSucc : ∀ b, ρ < b → ¬ le2 ρ b := by
  intro b hρb h2
  obtain ⟨y, -, hyρ, hy⟩ := le2_preds_cofinal h2 hρb 0 h.ρU.1
  exact h.below y hyρ ρ le_rfl hy

/-- No `<₂`-pair has its right end in `(ρ, τ]`. -/
theorem noPairUpto : ∀ c d, c < d → ρ < d → d ≤ τ → ¬ le2 c d := by
  intro c d hcd hρd hdτ h2
  rcases lt_trichotomy c ρ with hcρ | rfl | hρc
  · exact h.below c hcρ d hρd.le (le2_le1 h2)
  · exact h.noSucc d hcd h2
  · obtain ⟨l, hl, rfl⟩ := left_limit h2 hcd (lt_of_le_of_lt (hcd.le.trans hdτ) h.τ1)
    have := h.left l hl hρc (hcd.le.trans hdτ)
    rw [this] at hcd
    exact absurd (lt_of_lt_of_le hcd hdτ) (lt_irrefl _)

/-- **Lemma C″ (a)** in `R₂^C`: `ρ ≤₁ γ` as long as no `<₂`-pair has its right end in `(ρ, γ)`. -/
theorem le1ρ : ∀ γ, ρ ≤ γ → γ < Om1 → (∀ c d, c < d → ρ < d → d < γ → ¬ le2 c d) →
    le1 ρ γ := by
  classical
  intro γ hργ hγ1 hno
  rcases eq_or_lt_of_le hργ with e | hργ'
  · rw [← e]; exact le1_refl _
  have hρ1 := h.ρ1
  have hρE := upsPt_inE h.ρU
  obtain ⟨s1, hs1n, hTρ⟩ := exists_next h.ρU hρ1
  refine le1_iff.2 ⟨hργ, fun X Y hX hY hXY => ?_⟩
  set Y2 := Y.filter (· < s1) with hY2
  set Y3 := Y.filter (fun y => ¬ y < s1) with hY3
  obtain ⟨X', hsub, hX'C, hX'b⟩ := exists_closed (insert 0 (insert ρ (X ∪ Y2)))
  have hX'lt : ∀ x ∈ X', x < s1 := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := hX'b x hx
    refine lt_of_le_of_lt hxs ?_
    simp only [Finset.mem_insert, Finset.mem_union] at hs
    rcases hs with rfl | rfl | hs | hs
    · exact hs1n.2.1.1
    · exact hs1n.1
    · exact (hX s hs).trans hs1n.1
    · exact (Finset.mem_filter.1 hs).2
  have hXX' : ∀ x ∈ X, x ∈ X' := fun x hx => hsub (by simp [hx])
  have hY2X' : ∀ y ∈ Y2, y ∈ X' := fun y hy => hsub (by simp [hy])
  have h0X' : (0 : Ordinal.{0}) ∈ X' := hsub (by simp)
  have hρX' : ρ ∈ X' := hsub (by simp)
  have hY3 : ∀ y ∈ Y3, s1 ≤ y ∧ y < max γ s1 := by
    intro y hy
    obtain ⟨hy0, hys⟩ := Finset.mem_filter.1 hy
    exact ⟨not_lt.1 hys, lt_of_lt_of_le (hY y hy0).2 (le_max_left _ _)⟩
  have hD : (↑(X ∪ Y) : Set Ordinal.{0}) ⊆ ↑(X' ∪ Y3) := by
    intro w hw
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hw ⊢
    rcases hw with hw | hw
    · exact Or.inl (hXX' w hw)
    · by_cases hws : w < s1
      · exact Or.inl (hY2X' w (Finset.mem_filter.2 ⟨hw, hws⟩))
      · exact Or.inr (Finset.mem_filter.2 ⟨hw, hws⟩)
  have hX'Y3 : Closed ↑(X' ∪ Y3) := by
    have he : (↑(X' ∪ Y3) : Set Ordinal.{0}) = ↑X' ∪ ↑(X ∪ Y) := by
      ext w
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
      constructor
      · rintro (hw | hw)
        · exact Or.inl hw
        · exact Or.inr (Or.inr (Finset.mem_filter.1 hw).1)
      · rintro (hw | hw | hw)
        · exact Or.inl hw
        · exact Or.inl (hXX' w hw)
        · by_cases hws : w < s1
          · exact Or.inl (hY2X' w (Finset.mem_filter.2 ⟨hw, hws⟩))
          · exact Or.inr (Finset.mem_filter.2 ⟨hw, hws⟩)
    rw [he]; exact hX'C.union hXY
  obtain ⟨ψ, hψ, hψc, hψfix, hYψ, hψR⟩ :=
    ccf (hs1n.2.1.2 _ (le_max_right _ _)) X' Y3 hX'lt hY3 h0X' hX'Y3
  have hψD : ∀ w ∈ (↑(X ∪ Y) : Set Ordinal.{0}), ψ w < s1 := by
    intro w hw
    rcases Finset.mem_union.1 (Finset.mem_coe.1 (hD hw)) with h' | h'
    · rw [hψfix w h']; exact hX'lt w h'
    · exact (hYψ w h').2
  have hs11 : s1 < Om1 := next_lt_Om1 hs1n (Or.inr h.ρU) hρ1
  have hψX : ∀ x ∈ X, ψ x = x := fun x hx => hψfix x (hXX' x hx)
  have hρD' : ρ ∈ (↑(X' ∪ Y3) : Set Ordinal.{0}) := by simp [hρX']
  have hψρ : ψ ρ = ρ := hψfix ρ hρX'
  have hψY : ∀ y ∈ Y, ρ ≤ ψ y := by
    intro y hy
    rcases eq_or_lt_of_le (hY y hy).1 with e | hlt
    · rw [← e, hψρ]
    · have := hψ.2.1 hρD' (hD (by simp [hy])) hlt
      rw [hψρ] at this; exact this.le
  have hψYT : ∀ y ∈ Y, ψ y ∈ Tset ρ := fun y hy =>
    (hTρ _ ((hψD y (by simp [hy])).trans hs11)).2 (hψD y (by simp [hy]))
  set S := X ∪ Y.biUnion (fun y => Par ρ (ψ y)) with hSdef
  have hS : ∀ s ∈ S, s < ρ := by
    intro s hs
    rcases Finset.mem_union.1 hs with hs | hs
    · exact hX s hs
    · obtain ⟨y, hy, hsy⟩ := Finset.mem_biUnion.1 hs
      exact Par_sub hρE hρ1 (hψYT y hy) (Finset.mem_coe.2 hsy)
  have hsup : (insert 0 S).sup id < ρ := by
    rw [Finset.sup_lt_iff h.ρU.1]
    intro b hb
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact h.ρU.1
    · exact hS b hb
  obtain ⟨σ, σ', hσU, hc'σ, hσn, hσ'ρ, hlow, hσle1, hnop⟩ := h.land _ hsup
  have hSσ : ∀ s ∈ S, s < σ := fun s hs =>
    lt_of_le_of_lt (Finset.le_sup (f := id) (Finset.mem_insert_of_mem hs)) hc'σ
  have hσρ : σ < ρ := hσn.1.trans hσ'ρ
  have hB : Bases σ ρ := ⟨upsPt_inE hσU, hρE, hσρ, hρ1⟩
  obtain ⟨mσ, hmσ, hTσ⟩ := exists_next hσU (hσρ.trans hρ1)
  have hmσ' : mσ = σ' := hmσ.unique hσn
  rw [hmσ'] at hTσ
  have hXσ : ∀ x ∈ X, x < σ := fun x hx => hSσ x (Finset.mem_union_left _ hx)
  set W := ψ '' ↑(X ∪ Y) with hWdef
  have hWTB : W ⊆ TB ρ σ := by
    rintro _ ⟨w, hw, rfl⟩
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hw) with hw | hw
    · rw [hψX w hw]; exact (TB_inter_lt hB (hX w hw)).2 (hXσ w hw)
    · exact ⟨hψYT w hw, fun p hp =>
        hSσ p (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨w, hw, Finset.mem_coe.1 hp⟩))⟩
  have hW1 : ∀ w ∈ W, w < Om1 := by
    rintro _ ⟨w, hw, rfl⟩; exact (hψD w hw).trans hs11
  have hψisoD : ArithIso ↑(X ∪ Y) W ψ :=
    ⟨(hψ.2.1.mono hD).injOn.bijOn_image, hψ.2.1.mono hD,
      fun x hx y hy z hz => hψ.2.2 x (hD hx) y (hD hy) z (hD hz)⟩
  have hWc : Closed W := closed_image hψ hψc hD hXY
  have hpiso : ArithIso W (pi σ ρ '' W) (pi σ ρ) :=
    ⟨(down_mono hB hWTB).injOn.bijOn_image, down_mono hB hWTB, down_add hB hWTB⟩
  set f := pi σ ρ ∘ ψ with hfdef
  have hfimg : f '' ↑(X ∪ Y) = pi σ ρ '' W := by rw [hfdef, Set.image_comp]
  have hfiso : ArithIso ↑(X ∪ Y) (f '' ↑(X ∪ Y)) f := by
    rw [hfimg]; exact hψisoD.comp hpiso
  have hfcl : Closed (f '' ↑(X ∪ Y)) := by
    rw [hfimg]
    exact closed_image_of_indec hpiso hWc (fun s hs hI => down_indec hB (hWTB hs) (hW1 s hs) hI)
  have hfX : ∀ x ∈ X, f x = x := by
    intro x hx
    show pi σ ρ (ψ x) = x
    rw [hψX x hx, pi_lt hB (hXσ x hx)]
  have hψYW : ∀ y ∈ Y, ψ y ∈ W := fun y hy => ⟨y, by simp [hy], rfl⟩
  have hfY : ∀ y ∈ Y, σ ≤ f y ∧ f y < σ' := by
    intro y hy
    have hT := hWTB (hψYW y hy)
    refine ⟨down_ge hB hT (hψY y hy), (hTσ _ (down_lt_Om1 hB hT (hW1 _ (hψYW y hy)))).1
      ((pi_bijOn hB).1.mapsTo hT)⟩
  have hfρ : ρ ∈ Y → f ρ = σ := by
    intro _
    show pi σ ρ (ψ ρ) = σ
    rw [hψρ, (pi_base hB).2]
  have hXlt : ∀ c ∈ (↑(X ∪ Y) : Set Ordinal.{0}), ∀ d ∈ X, c ≤ d → c ∈ X := by
    intro c hc d hd hcd
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hc) with hc | hc
    · exact hc
    · exact absurd (lt_of_le_of_lt hcd (hX d hd)) (not_lt.2 (hY c hc).1)
  have hcov : Cov R2C R2C ↑(X ∪ Y) (f '' ↑(X ∪ Y)) f := by
    refine ⟨hfiso, ?_, ?_⟩
    · intro c hc d hd hcd
      change le1 c d at hcd
      change le1 (f c) (f d)
      rcases Finset.mem_union.1 (Finset.mem_coe.1 hd) with hdX | hdY
      · rw [hfX c (hXlt c hc d hdX (le1_le hcd)), hfX d hdX]; exact hcd
      rcases lt_trichotomy c ρ with hcρ | e | hρc
      · exact absurd hcd (h.below c hcρ d (hY d hdY).1)
      · have hcY : c ∈ Y := by
          rcases Finset.mem_union.1 (Finset.mem_coe.1 hc) with hcX | hcY
          · exact absurd (e ▸ hX c hcX) (lt_irrefl _)
          · exact hcY
        rw [e] at hcY ⊢
        rw [hfρ hcY]
        exact hσle1 _ (hfY d hdY).1 (hfY d hdY).2
      · have hR := inc1 ((hY d hdY).2.trans hγ1) hcd
        have hcD := hD hc
        have hdD := hD hd
        have hR' := hψR c (Finset.mem_coe.1 hcD) d (Finset.mem_coe.1 hdD) hR
        have hψc : ρ < ψ c := by
          have := hψ.2.1 hρD' hcD hρc
          rwa [hψρ] at this
        have hcW : ψ c ∈ W := ⟨c, hc, rfl⟩
        have hdW : ψ d ∈ W := ⟨d, hd, rfl⟩
        have hR'' := (down_le1R hσU h.ρU hB (hWTB hcW) (hWTB hdW) (hW1 _ hcW)).1 hR'
        exact (hlow _ _ (down_gt hB (hWTB hcW) hψc) (hfY d hdY).2).2 hR''
    · intro c hc d hd hcd
      change le2 c d at hcd
      change le2 (f c) (f d)
      rcases eq_or_lt_of_le (le2_le hcd) with e | hlt
      · rw [e]; exact le2_refl _
      rcases Finset.mem_union.1 (Finset.mem_coe.1 hd) with hdX | hdY
      · rw [hfX c (hXlt c hc d hdX hlt.le), hfX d hdX]; exact hcd
      rcases eq_or_lt_of_le (hY d hdY).1 with e | hρd
      · rw [← e] at hlt hcd
        exact absurd (le2_le1 hcd) (h.below c hlt ρ le_rfl)
      · exact absurd hcd (hno c d hlt hρd (hY d hdY).2)
  have himg : (↑(X ∪ Y.image f) : Set Ordinal.{0}) = f '' ↑(X ∪ Y) := by
    ext w
    simp only [Set.mem_image, Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro (hw | ⟨t, ht, rfl⟩)
      · exact ⟨w, Or.inl hw, hfX w hw⟩
      · exact ⟨t, Or.inr ht, rfl⟩
    · rintro ⟨t, ht | ht, rfl⟩
      · left; rw [hfX t ht]; exact ht
      · right; exact ⟨t, ht, rfl⟩
  refine ⟨Y.image f, ?_, ?_, ?_, f, ?_⟩
  · intro y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    exact (hfY t ht).2.trans hσ'ρ
  · intro x hx y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    exact lt_of_lt_of_le (hXσ x hx) (hfY t ht).1
  · rw [himg]; exact hfcl
  · rw [himg]; exact hcov

/-- `≤₁` of `R₂^C` is `≤₁` of `R₁⁺` on `(ρ, B]` when no `<₂`-pair has its right end in `(ρ, B)`. -/
theorem lowB {B : Ordinal.{0}} (hB : B < Om1) (hno : ∀ c d, c < d → ρ < d → d < B → ¬ le2 c d) :
    ∀ a b, ρ < a → b ≤ B → (le1 a b ↔ le1R a b) := by
  intro a b ha hb
  refine le1_iff_le1R_blk' hB (fun c hc g hg hgB hcg => ?_) hno b hb a ha
  rcases eq_or_lt_of_le hc with e | hcρ
  · refine ⟨e, fun g' hg' hg'B => h.le1ρ g' hg'.le (lt_of_le_of_lt hg'B hB) ?_⟩
    exact fun c d hcd hρd hdg => hno c d hcd hρd (lt_of_lt_of_le hdg hg'B)
  · exact absurd hcg (h.below c hcρ g hg.le)

theorem lowτ : ∀ a b, ρ < a → b ≤ τ → (le1 a b ↔ le1R a b) :=
  h.lowB h.τ1 (fun c d hcd hρd hdτ => h.noPairUpto c d hcd hρd hdτ.le)

/-- No `<₂`-pair has its right end in `(ρ, δ)`. -/
theorem noPairGap : ∀ c d, c < d → ρ < d → d < δ → ¬ le2 c d := by
  intro c d hcd hρd hdδ h2
  rcases lt_trichotomy c ρ with hcρ | rfl | hρc
  · exact h.below c hcρ d hρd.le (le2_le1 h2)
  · exact h.noSucc d hcd h2
  have hc1 : c < Om1 := (hcd.trans hdδ).trans h.δ1
  have hcU := Googology.Trans.PoR.InaccPsi.R2.left h2 hcd hc1
  have hcτ : c ≤ τ := by
    by_contra hlt
    exact absurd (lt_trans hcd hdδ) (not_lt.2 (h.next.2.2 c (not_le.1 hlt) hcU))
  obtain ⟨l, hl, rfl⟩ := left_limit h2 hcd hc1
  have := h.left l hl hρc hcτ
  rw [this] at h2 hcd
  exact not_le2_gap_of h.τU h.next h.δ1 (chains_of h.ρτ h.cof h.lowτ) d hcd hdδ h2

/-- **B″4**: `ρ ≤₁ γ` for every `γ ∈ [ρ, δ]`. -/
theorem le1ρδ : ∀ g, ρ ≤ g → g ≤ δ → le1 ρ g := fun g hg hgδ =>
  h.le1ρ g hg (lt_of_le_of_lt hgδ h.δ1)
    (fun c d hcd hρd hdg => h.noPairGap c d hcd hρd (lt_of_lt_of_le hdg hgδ))

/-- SK1 in the restart block: `≤₁` of `R₂^C` is `≤₁` of `R₁⁺` on `(ρ, δ]`. -/
theorem lowδ : ∀ a b, ρ < a → b ≤ δ → (le1 a b ↔ le1R a b) := h.lowB h.δ1 h.noPairGap

/-- The restart block as a pair context. -/
theorem toPair : PairCtx ρ τ δ := by
  refine ⟨h.τU, h.next, h.δ1, h.ρτ, h.cof, h.noPairGap, h.lowδ, ?_⟩
  intro c hc d hd hdδ hcd
  rcases eq_or_lt_of_le hc with e | hcρ
  · exact ⟨e, fun g hg hgδ => h.le1ρδ g hg.le hgδ⟩
  · exact absurd hcd (h.below c hcρ d hd.le)

/-- **The pair of the restart block**: `τ <₂ δ`. -/
theorem pair : le2 τ δ := h.toPair.pair

/-- `τ` is the only `<₂`-predecessor of `δ`. -/
theorem pairs_at_top {c : Ordinal.{0}} (hc : c < δ) (h2 : le2 c δ) : c = τ := by
  rcases lt_trichotomy c ρ with hcρ | rfl | hρc
  · exact absurd (le2_le1 h2) (h.below c hcρ δ (h.ρτ.trans h.τδ).le)
  · exact absurd h2 (h.noSucc δ hc)
  have hcU := Googology.Trans.PoR.InaccPsi.R2.left h2 hc (hc.trans h.δ1)
  have hcτ : c ≤ τ := by
    by_contra hlt
    exact absurd hc (not_lt.2 (h.next.2.2 c (not_le.1 hlt) hcU))
  obtain ⟨l, hl, rfl⟩ := left_limit h2 hc (hc.trans h.δ1)
  exact h.left l hl hρc hcτ

omit h in
/-- `x + 1` is decomposable for `x > 1`. -/
theorem not_indec_succ (x : Ordinal.{0}) (hx : 1 < x) : ¬ Indec (x + 1) := by
  intro hI
  exact hI (Or.inr ⟨x, 1, lt_add_one x, lt_of_lt_of_le hx le_self_add, rfl⟩)

/-- **Lemma TOP** in `R₂^C`: `ρ` is not `≤₁` any `γ > δ + 1`. -/
theorem top : ∀ g, δ + 1 < g → ¬ le1 ρ g := by
  classical
  intro g hg hρg
  obtain ⟨x0, hx0ρ, hcap⟩ := h.capP
  have hρδ : ρ < δ := h.ρτ.trans h.τδ
  have hρI := indec_of_upsPt h.ρU
  have hτI := indec_of_upsPt h.τU
  have hδI := indec_of_upsPt h.next.2.1
  have h1ρ : (1 : Ordinal.{0}) < ρ := by
    have := hρI.pos
    have hE := upsPt_inE h.ρU
    unfold InE at hE
    calc (1 : Ordinal.{0}) < ω := one_lt_omega0
      _ = ω ^ (1 : Ordinal.{0}) := (opow_one ω).symm
      _ ≤ ω ^ ρ := opow_le_opow_right omega0_pos (one_le_iff_pos.2 this)
      _ = ρ := hE
  have h1I : Indec (1 : Ordinal.{0}) := by
    have := indec_opow (0 : Ordinal.{0}); rwa [opow_zero] at this
  set Y : Finset Ordinal.{0} := {ρ, τ, δ, δ + 1} with hYdef
  have hmemA : ∀ x ∈ (↑({1} ∪ Y : Finset Ordinal.{0}) : Set Ordinal.{0}),
      x = 1 ∨ x = ρ ∨ x = τ ∨ x = δ ∨ x = δ + 1 := by
    intro x hx; simp [hYdef] at hx; tauto
  have hcl : Closed (↑({1} ∪ Y : Finset Ordinal.{0}) : Set Ordinal.{0}) := by
    intro x hx hdx
    rcases hmemA x hx with rfl | rfl | rfl | rfl | rfl
    · exact absurd hdx h1I
    · exact absurd hdx hρI
    · exact absurd hdx hτI
    · exact absurd hdx hδI
    · exact Or.inr ⟨δ, by simp [hYdef], 1, by simp, lt_add_one δ,
        lt_of_lt_of_le (h1ρ.trans hρδ) le_self_add, rfl⟩
  have hYb : ∀ y ∈ Y, ρ ≤ y ∧ y < g := by
    intro y hy
    simp only [hYdef, Finset.mem_insert, Finset.mem_singleton] at hy
    have hδg : δ < g := (lt_add_one δ).trans hg
    rcases hy with rfl | rfl | rfl | rfl
    · exact ⟨le_rfl, lt_of_le_of_lt hρδ.le hδg⟩
    · exact ⟨h.ρτ.le, h.τδ.trans hδg⟩
    · exact ⟨hρδ.le, hδg⟩
    · exact ⟨hρδ.le.trans le_self_add, hg⟩
  obtain ⟨Yt, hYt, -, -, f, hf, hfix, hmap⟩ := le1_cof hρg hx0ρ {1} Y (by simpa using h1ρ)
    hYb hcl
  have mA : ∀ y ∈ Y, y ∈ (↑({1} ∪ Y : Finset Ordinal.{0}) : Set Ordinal.{0}) := by
    intro y hy; simp [hy]
  have m1 : (1 : Ordinal.{0}) ∈ (↑({1} ∪ Y : Finset Ordinal.{0}) : Set Ordinal.{0}) := by simp
  have mρ : ρ ∈ Y := by simp [hYdef]
  have mτ : τ ∈ Y := by simp [hYdef]
  have mδ : δ ∈ Y := by simp [hYdef]
  have mδ1 : δ + 1 ∈ Y := by simp [hYdef]
  have hf1 : f 1 = 1 := hfix 1 (by simp)
  have hadd : f δ + f 1 = f (δ + 1) := (hf.1.2.2 δ (mA δ mδ) 1 m1 (δ + 1) (mA _ mδ1)).1 rfl
  rw [hf1] at hadd
  have h2 : le2 (f τ) (f δ) := hf.2.2 _ (mA τ mτ) _ (mA δ mδ) h.pair
  have hlt : f τ < f δ := hf.1.2.1 (mA τ mτ) (mA δ mδ) h.τδ
  have hρδ1 : le1 ρ (δ + 1) := le1_of_le_of_le1 (hρδ.le.trans le_self_add) hg.le hρg
  have h1' : le1 (f ρ) (f (δ + 1)) := hf.2.1 _ (mA ρ mρ) _ (mA _ mδ1) hρδ1
  rw [← hadd] at h1'
  have hfρδ : f ρ ≤ f δ := (hf.1.2.1 (mA ρ mρ) (mA δ mδ) hρδ).le
  have hτY := hYt _ (hmap τ mτ)
  have hδY := hYt _ (hmap δ mδ)
  exact hcap (f τ) (f δ) hτY.1 hlt hδY.2 h2 (f ρ) hfρδ (f δ + 1) (lt_add_one _) h1'

/-- No point `≤ δ + 1` is `≤₁` a point `> δ + 1` (the closedness after the restart block). -/
theorem T3succ : ∀ c ≤ δ + 1, ∀ g, δ + 1 < g → ¬ le1 c g := by
  classical
  intro c hc g hg hcg
  have hδg : δ < g := (lt_add_one δ).trans hg
  rcases lt_trichotomy c ρ with hcρ | rfl | hρc
  · exact h.below c hcρ g ((h.ρτ.trans h.τδ).le.trans hδg.le) hcg
  · exact h.top g hg hcg
  rcases eq_or_lt_of_le hc with e | hcδ1
  · rw [e] at hcg
    have hδ1 : (1 : Ordinal.{0}) < δ := by
      have hδE := upsPt_inE h.next.2.1
      unfold InE at hδE
      calc (1 : Ordinal.{0}) < ω := one_lt_omega0
        _ = ω ^ (1 : Ordinal.{0}) := (opow_one ω).symm
        _ ≤ ω ^ δ := opow_le_opow_right omega0_pos (one_le_iff_pos.2 h.next.2.1.1)
        _ = δ := hδE
    exact RstCtx.not_indec_succ δ hδ1 (indec_of_lt1 hcg hg)
  have hcδ : c ≤ δ := Order.lt_succ_iff.1 (by rwa [succ_eq_add_one])
  have hτI := indec_of_upsPt h.τU
  have hδI := indec_of_upsPt h.next.2.1
  rcases le_or_gt c τ with hcτ | hτc
  · have hmem : ∀ x ∈ (↑((∅ : Finset Ordinal.{0}) ∪ {τ, δ} : Finset Ordinal.{0}) :
        Set Ordinal.{0}), x = τ ∨ x = δ := by
      intro x hx; simpa using hx
    obtain ⟨Yt, hYt, -, -, f, hf, -, hmap⟩ := le1_cof hcg hρc ∅ {τ, δ} (by simp)
      (by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact ⟨hcτ, h.τδ.trans hδg⟩
        · exact ⟨hcδ, hδg⟩)
      (closed_of_indec (by
        intro x hx
        rcases hmem x hx with rfl | rfl
        · exact hτI
        · exact hδI))
    have hτm : τ ∈ (↑((∅ : Finset Ordinal.{0}) ∪ {τ, δ} : Finset Ordinal.{0}) :
        Set Ordinal.{0}) := by simp
    have hδm : δ ∈ (↑((∅ : Finset Ordinal.{0}) ∪ {τ, δ} : Finset Ordinal.{0}) :
        Set Ordinal.{0}) := by simp
    have h2 : le2 (f τ) (f δ) := hf.2.2 _ hτm _ hδm h.pair
    have hlt : f τ < f δ := hf.1.2.1 hτm hδm h.τδ
    have hfδ := hYt _ (hmap δ (by simp))
    exact h.noPairGap _ _ hlt hfδ.1 (lt_of_lt_of_le hfδ.2 (hcτ.trans h.τδ.le)) h2
  · obtain ⟨Yt, hYt, -, -, f, hf, hfix, hmap⟩ := le1_cof hcg hτc {τ} {δ} (by simpa using hτc)
      (by simpa using ⟨hcδ, hδg⟩)
      (closed_of_indec (by
        intro x hx
        simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union,
          Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact hτI
        · exact hδI))
    have hτm : τ ∈ (↑({τ} ∪ {δ} : Finset Ordinal.{0}) : Set Ordinal.{0}) := by simp
    have hδm : δ ∈ (↑({τ} ∪ {δ} : Finset Ordinal.{0}) : Set Ordinal.{0}) := by simp
    have h2 : le2 (f τ) (f δ) := hf.2.2 _ hτm _ hδm h.pair
    have hfδ := hYt _ (hmap δ (by simp))
    rw [hfix τ (by simp)] at h2
    exact h.noPairGap _ _ hfδ.1 (h.ρτ.trans hfδ.1) (lt_of_lt_of_le hfδ.2 hcδ) h2

end RstCtx

end Googology.Trans.PoR.InaccPsi.R2
