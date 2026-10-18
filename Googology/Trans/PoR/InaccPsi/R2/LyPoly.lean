import Googology.Trans.PoR.InaccPsi.R2.LyStep

/-!
# The layer of all constant exponents: terms `T(x)·(x^{a₁}·γ₁ + ⋯ + x^{aₙ}·γₙ) + s(x)`, top `T(x)·x^x`

For a layer `L` (`R2.XtLay`, top `T(x) = ω^{E(x)}`) the terms of `lyPoly L` are a list of pairs `(aᵢ, γᵢ)` of
constants (exponents strictly decreasing, coefficients positive) and a term `s` of `L`; the value at a base `x` is
`T(x)·Σ x^{aᵢ}·γᵢ + s(x)` (the base-`x` Cantor normal form, `lyPv`).  Every constant exponent `a < x` occurs, so the
tops `T(x)·x^a` of all layers with a constant exponent (`B(x)·x^{ω·k+n}`, `B(x)·x^{ω²}`, …) are values of terms.

* the order: every value is below `T(x)·x^x` (`lyPv_lt`), every ordinal below `T(ρ)·ρ^ρ` is a value (division by
  `T(ρ)` and the Cantor normal form base `ρ`, `Ordinal.CNF`);
* **EXACT** (`lyExact`): `π_{σ,ρ}(T(ρ)·ρ^a·γ) = T(σ)·σ^a·γ` for `a, γ < σ` (`ρ^a = ω^{ρ·a}`, `xtPiOpowMul`,
  `pi_add`);
* **IMG** (`lyImg`): `f(T(ρ)·ρ^a·γ) ≥ T(f(ρ))·f(ρ)^a·γ` (`lyPow`, `xtLMul`), sums by the closure of the witness
  sets;
* **RS** (`lyRs`, `rs_rstF`);
* the witness pair of the top `T(ρ)·ρ^ρ` (`lyPowTop`), so `lyPoly L` is again a layer, with top `T(x)·x^x`
  and exponent `E(x) + x·x`.

No new axiom beyond `R2.CitedXt`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ly

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt

/-- The base-`x` polynomial `Σ x^{aᵢ}·γᵢ` of a list of pairs (exponent, coefficient). -/
noncomputable def lyPv (x : Ordinal.{0}) (ps : List (Ordinal.{0} × Ordinal.{0})) : Ordinal.{0} :=
  ps.foldr (fun p r => x ^ p.1 * p.2 + r) 0

/-- Normal form: exponents strictly decreasing, coefficients positive. -/
def LyNF (ps : List (Ordinal.{0} × Ordinal.{0})) : Prop :=
  ps.Pairwise (fun p q => q.1 < p.1) ∧ ∀ p ∈ ps, 0 < p.2

/-- The exponents and coefficients lie below `x`. -/
def LyBd (ps : List (Ordinal.{0} × Ordinal.{0})) (x : Ordinal.{0}) : Prop := ∀ p ∈ ps, p.1 < x ∧ p.2 < x

@[simp] theorem lyPv_nil (x : Ordinal.{0}) : lyPv x [] = 0 := rfl

theorem lyPv_cons (x : Ordinal.{0}) (p : Ordinal.{0} × Ordinal.{0}) (ps : List (Ordinal.{0} × Ordinal.{0})) :
    lyPv x (p :: ps) = x ^ p.1 * p.2 + lyPv x ps := rfl

theorem lyNF_tail {p : Ordinal.{0} × Ordinal.{0}} {ps : List (Ordinal.{0} × Ordinal.{0})} (h : LyNF (p :: ps)) :
    LyNF ps := ⟨(List.pairwise_cons.1 h.1).2, fun q hq => h.2 q (List.mem_cons_of_mem _ hq)⟩

theorem lyNF_head {p : Ordinal.{0} × Ordinal.{0}} {ps : List (Ordinal.{0} × Ordinal.{0})} (h : LyNF (p :: ps)) :
    ∀ q ∈ ps, q.1 < p.1 := (List.pairwise_cons.1 h.1).1

/-- **The polynomial lies below `x^b`** when every exponent is below `b`. -/
theorem lyPv_lt {x : Ordinal.{0}} (hx : 1 < x) : ∀ (ps : List (Ordinal.{0} × Ordinal.{0})) (b : Ordinal.{0}),
    LyNF ps → LyBd ps x → (∀ p ∈ ps, p.1 < b) → lyPv x ps < x ^ b
  | [], b, _, _, _ => by simpa using opow_pos b (zero_lt_one.trans hx)
  | p :: ps, b, hN, hB, hb => by
    have ih := lyPv_lt hx ps p.1 (lyNF_tail hN) (fun q hq => hB q (List.mem_cons_of_mem _ hq)) (lyNF_head hN)
    have hp := hB p List.mem_cons_self
    rw [lyPv_cons]
    calc x ^ p.1 * p.2 + lyPv x ps < x ^ p.1 * p.2 + x ^ p.1 := (add_lt_add_iff_left _).2 ih
      _ = x ^ p.1 * (p.2 + 1) := (mul_add_one _ _).symm
      _ ≤ x ^ p.1 * x := mul_le_mul_right (Order.add_one_le_of_lt hp.2) _
      _ = x ^ (p.1 + 1) := (opow_add_one _ _).symm
      _ ≤ x ^ b := opow_le_opow_right (zero_lt_one.trans hx) (Order.add_one_le_of_lt (hb p List.mem_cons_self))

theorem lyPv_pos {x : Ordinal.{0}} (hx : 0 < x) {ps : List (Ordinal.{0} × Ordinal.{0})} (hN : LyNF ps)
    (hne : ps ≠ []) : 1 ≤ lyPv x ps := by
  obtain ⟨p, ps', rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [lyPv_cons]
  have h1 : 1 ≤ x ^ p.1 * p.2 :=
    one_le_iff_pos.2 (mul_pos (opow_pos _ hx) (hN.2 p List.mem_cons_self))
  exact h1.trans le_self_add

theorem lyPv_eq_zero {x : Ordinal.{0}} (hx : 0 < x) {ps : List (Ordinal.{0} × Ordinal.{0})} (hN : LyNF ps)
    (h0 : lyPv x ps = 0) : ps = [] := by
  by_contra hne
  have := lyPv_pos hx hN hne
  rw [h0] at this
  exact absurd this (not_le.2 zero_lt_one)

variable (L : XtLay)

/-- The value `T(x)·Σ x^{aᵢ}·γᵢ + s(x)`. -/
noncomputable def lyVal (t : List (Ordinal.{0} × Ordinal.{0}) × L.sys.Tm) (x : Ordinal.{0}) : Ordinal.{0} :=
  L.sys.top x * lyPv x t.1 + L.sys.val t.2 x

/-- The constants below `x`, and the normal form. -/
def lyCB (t : List (Ordinal.{0} × Ordinal.{0}) × L.sys.Tm) (x : Ordinal.{0}) : Prop :=
  LyNF t.1 ∧ LyBd t.1 x ∧ L.sys.CB t.2 x

/-- The constants. -/
def lyCs (t : List (Ordinal.{0} × Ordinal.{0}) × L.sys.Tm) : List Ordinal.{0} :=
  t.1.map Prod.fst ++ t.1.map Prod.snd ++ L.sys.cs t.2

variable {L}

theorem lyVal_nil (s : L.sys.Tm) : lyVal L ([], s) = L.sys.val s := by
  funext x; simp [lyVal]

theorem lyVal_cons (p : Ordinal.{0} × Ordinal.{0}) (ps : List (Ordinal.{0} × Ordinal.{0})) (s : L.sys.Tm)
    (x : Ordinal.{0}) :
    lyVal L (p :: ps, s) x = L.sys.top x * x ^ p.1 * p.2 + lyVal L (ps, s) x := by
  simp only [lyVal, lyPv_cons, mul_add, mul_assoc, add_assoc]

theorem lyCB_tail {p : Ordinal.{0} × Ordinal.{0}} {ps : List (Ordinal.{0} × Ordinal.{0})} {s : L.sys.Tm}
    {x : Ordinal.{0}} (h : lyCB L (p :: ps, s) x) : lyCB L (ps, s) x :=
  ⟨lyNF_tail h.1, fun q hq => h.2.1 q (List.mem_cons_of_mem _ hq), h.2.2⟩

theorem lyCB_cst (t : List (Ordinal.{0} × Ordinal.{0}) × L.sys.Tm) (x : Ordinal.{0}) (h : lyCB L t x) :
    ∀ c ∈ lyCs L t, c < x := by
  intro c hc
  simp only [lyCs, List.mem_append, List.mem_map] at hc
  rcases hc with (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) | hc
  · exact (h.2.1 p hp).1
  · exact (h.2.1 p hp).2
  · exact L.sys.cb_cst t.2 x h.2.2 c hc

theorem lyCB_iff (t : List (Ordinal.{0} × Ordinal.{0}) × L.sys.Tm) (x x' : Ordinal.{0}) (h : lyCB L t x)
    (h' : ∀ c ∈ lyCs L t, c < x') : lyCB L t x' := by
  refine ⟨h.1, fun p hp => ⟨h' _ ?_, h' _ ?_⟩, L.sys.cb_iff t.2 x x' h.2.2 fun c hc => h' c ?_⟩
  · simp only [lyCs, List.mem_append, List.mem_map]; exact Or.inl (Or.inl ⟨p, hp, rfl⟩)
  · simp only [lyCs, List.mem_append, List.mem_map]; exact Or.inl (Or.inr ⟨p, hp, rfl⟩)
  · simp only [lyCs, List.mem_append]; exact Or.inr hc

theorem lyT_pos {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : 0 < L.sys.top x :=
  hx.pos.trans (L.top_gt x hx hx1)

/-- **Every value is below `T(x)·x^x`.** -/
theorem lyLt_top {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (t : List (Ordinal.{0} × Ordinal.{0}) × L.sys.Tm)
    (h : lyCB L t x) : lyVal L t x < L.sys.top x * x ^ x := by
  have h1x : 1 < x := one_lt_omega0.trans (omega0_lt_inE hx)
  have hpv := lyPv_lt h1x t.1 x h.1 h.2.1 (fun p hp => (h.2.1 p hp).1)
  have hs := L.lt_top_E x hx hx1 t.2 h.2.2
  calc lyVal L t x < L.sys.top x * lyPv x t.1 + L.sys.top x := (add_lt_add_iff_left _).2 hs
    _ = L.sys.top x * (lyPv x t.1 + 1) := (mul_add_one _ _).symm
    _ ≤ L.sys.top x * x ^ x := mul_le_mul_right (Order.add_one_le_of_lt hpv) _

theorem lyTop_lt_ups {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hxu : x < u) (hu : UpsPt u) :
    L.sys.top x * x ^ x < u :=
  (upsPt_inE hu).mul_lt (L.top_lt_ups x u hx hx1 hxu hu) (ly_pow_lt (upsPt_inE hu) hxu hxu)

/-- The tail below the leading term: `T(x)·Σ_{i ≥ 2} x^{aᵢ}·γᵢ + s(x) < T(x)·x^{a₁}`. -/
theorem lyTail_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {p : Ordinal.{0} × Ordinal.{0}}
    {ps : List (Ordinal.{0} × Ordinal.{0})} {s : L.sys.Tm} (h : lyCB L (p :: ps, s) x) :
    lyVal L (ps, s) x < L.sys.top x * x ^ p.1 := by
  have h1x : 1 < x := one_lt_omega0.trans (omega0_lt_inE hx)
  have ht := lyCB_tail h
  have hpv := lyPv_lt h1x ps p.1 ht.1 ht.2.1 (lyNF_head h.1)
  have hs := L.lt_top_E x hx hx1 s h.2.2
  calc lyVal L (ps, s) x < L.sys.top x * lyPv x ps + L.sys.top x := (add_lt_add_iff_left _).2 hs
    _ = L.sys.top x * (lyPv x ps + 1) := (mul_add_one _ _).symm
    _ ≤ L.sys.top x * x ^ p.1 := mul_le_mul_right (Order.add_one_le_of_lt hpv) _

/-- A value `0` at a base `x > 0` is the value `0` everywhere. -/
theorem lyVal_zero {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {t : List (Ordinal.{0} × Ordinal.{0}) × L.sys.Tm}
    (h : lyCB L t x) (h0 : lyVal L t x = 0) : ∀ y, lyVal L t y = 0 := by
  obtain ⟨ps, s⟩ := t
  have hs0 : L.sys.val s x = 0 := (add_eq_zero_iff.1 h0).2 |> fun h => h
  have hT0 : L.sys.top x * lyPv x ps = 0 := (add_eq_zero_iff.1 h0).1
  have hp0 : lyPv x ps = 0 := by
    rcases mul_eq_zero.1 hT0 with h' | h'
    · exact absurd h' (lyT_pos hx hx1).ne'
    · exact h'
  have hps := lyPv_eq_zero hx.pos h.1 hp0
  subst hps
  have hconst : ∀ y, L.sys.val s y = 0 := by
    rcases L.sys.small s with hc | hc
    · intro y; rw [hc y x, hs0]
    · have := hc x hx hx1 h.2.2
      rw [hs0] at this
      exact absurd this (not_le.2 hx.pos)
  intro y; simp [lyVal, hconst y]

/-! ## Lemma EXACT -/

/-- **Lemma EXACT for `T(ρ)·ρ^a·γ`** (`a, γ < σ`). -/
theorem lyPiT {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {a γ : Ordinal.{0}}
    (ha : a < σ) (hγ : γ < σ) :
    L.sys.top ρ * ρ ^ a * γ ∈ TB ρ σ ∧ pi σ ρ (L.sys.top ρ * ρ ^ a * γ) = L.sys.top σ * σ ^ a * γ := by
  have hρ1 := hB.2.2.2
  have hσ1 := hB.2.2.1.trans hρ1
  have hρE := hB.2.1
  have hσE := hB.1
  obtain ⟨h1, h2⟩ := L.exp_pi σ ρ hσ hρ hB
  obtain ⟨h3, h4⟩ := pi_base hB
  obtain ⟨h5, h6⟩ := xtPiOpowMul hσ hρ hB h3 h4 hρ1 a ha
  rw [show ω ^ ρ = ρ from hρE] at h5 h6
  rw [show ω ^ σ = σ from hσE] at h6
  obtain ⟨h7, h8⟩ := pi_add hB h1 h5
  rw [h6, h2] at h8
  have hE1 : L.E ρ + ρ * a < Om1 := Om1_add_lt (L.exp_lt ρ hρE hρ1) (Om1_mul_lt hρ1 (ha.trans hσ1))
  obtain ⟨h9, h10⟩ := xtPiOpowMul hσ hρ hB h7 h8 hE1 γ hγ
  rw [ly_top_pow L hρE hρ1, ly_top_pow L hσE hσ1]
  exact ⟨h9, h10⟩

/-- **Lemma EXACT for the terms of `lyPoly L`.** -/
theorem lyExact {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) (s : L.sys.Tm) :
    ∀ ps : List (Ordinal.{0} × Ordinal.{0}), lyCB L (ps, s) σ →
      lyVal L (ps, s) ρ ∈ TB ρ σ ∧ pi σ ρ (lyVal L (ps, s) ρ) = lyVal L (ps, s) σ
  | [], h => by
    rw [lyVal_nil]; exact L.exact σ ρ hσ hρ hB s h.2.2
  | p :: ps, h => by
    have hp := h.2.1 p List.mem_cons_self
    obtain ⟨h1, h2⟩ := lyPiT (L := L) hσ hρ hB hp.1 hp.2
    obtain ⟨h3, h4⟩ := lyExact hσ hρ hB s ps (lyCB_tail h)
    obtain ⟨h5, h6⟩ := pi_add hB h1 h3
    rw [lyVal_cons, lyVal_cons]
    exact ⟨h5, by rw [h6, h2, h4]⟩

/-! ## Lemma IMG -/

variable {ρ τ δ : Ordinal.{0}}

/-- **The witness pair of `T(ρ)·ρ^a·γ`**: `f(T(ρ)·ρ^a·γ) ≥ T(f(ρ))·f(ρ)^a·γ` (`a, γ < ρ`, `γ ≠ 0`). -/
theorem lyWitH (h : RstK ρ τ δ) {a γ : Ordinal.{0}} (ha : a < ρ) (hγ : γ < ρ) (hγ0 : γ ≠ 0) :
    ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ L.sys.top ρ * ρ ^ a * γ ∈ W ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
        L.sys.top (f ρ) * f ρ ^ a * γ ≤ f (L.sys.top ρ * ρ ^ a * γ) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hδE := h.δE
  obtain ⟨W1, Z1, hw1, hbW, hI1⟩ := lyPow L h a ha
  have hbe : L.sys.top ρ * ρ ^ a = ω ^ (L.E ρ + ρ * a) := ly_top_pow L hρE hρ1 a
  rw [hbe] at hbW hI1 ⊢
  have he0 : L.E ρ + ρ * a ≠ 0 :=
    (lt_of_lt_of_le (pos_iff_ne_zero.2 (ly_E_ne L hρE hρ1)) le_self_add).ne'
  have hρT : ρ < L.sys.top ρ := L.top_gt ρ hρE hρ1
  have hρb : ρ ≤ ω ^ (L.E ρ + ρ * a) := by
    rw [← hbe]; exact hρT.le.trans (le_mul_left _ (opow_pos _ hρE.pos))
  have hbδ : ω ^ (L.E ρ + ρ * a) < δ := by
    rw [← hbe]
    exact hδE.mul_lt (L.top_lt_ups ρ δ hρE hρ1 h.ρδ h.next.2.1) (ly_pow_lt hδE h.ρδ (ha.trans h.ρδ))
  have hed : ω ^ ρ ∣ L.E ρ + ρ * a :=
    dvd_add (L.exp_dvd ρ hρE hρ1) ⟨a, by rw [show ω ^ ρ = ρ from hρE]⟩
  obtain ⟨W, Z, hw, hγW, hWW, hZZ, hI⟩ := xtLMul h he0 hρb hbδ hed hw1 hbW
    (fun A f hW hZ C => by obtain ⟨e', h1, h2, -⟩ := hI1 A f hW hZ C; exact ⟨e', h1, h2⟩) γ hγ
  refine ⟨W, insert γ Z, hw.insZ hγ, hγW hγ0, fun A f hW hZ C => ?_⟩
  have hZA : ↑Z ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  have hγA : γ ∈ A := hZ (by simp)
  have h1 := hI A f hW hZA C (C.above γ hγA hγ)
  obtain ⟨e', he', -, hle⟩ := hI1 A f (fun x hx => hW (hWW hx)) (fun x hx => hZA (hZZ hx)) C
  have hfE := upsPt_inE C.ups
  have hf1 := (C.low ρ C.rho).trans hρ1
  rw [ly_top_pow L hfE hf1]
  refine (mul_le_mul_left ?_ γ).trans h1
  rw [he']
  exact opow_le_opow_right omega0_pos hle

/-- **Lemma IMG for the terms of `lyPoly L`**, as witness sets for the value. -/
theorem lyImgList (h : RstK ρ τ δ) (s : L.sys.Tm)
    (hs : ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ (L.sys.val s ρ ≠ 0 → L.sys.val s ρ ∈ W ∪ Z) ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
        L.sys.val s (f ρ) ≤ f (L.sys.val s ρ)) :
    ∀ ps : List (Ordinal.{0} × Ordinal.{0}), lyCB L (ps, s) ρ →
      ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ (lyVal L (ps, s) ρ ≠ 0 → lyVal L (ps, s) ρ ∈ W ∪ Z) ∧
        ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
          lyVal L (ps, s) (f ρ) ≤ f (lyVal L (ps, s) ρ)
  | [], _ => by rw [lyVal_nil]; exact hs
  | p :: ps, hCB => by
    classical
    have hρE := h.ρE
    have hρ1 := h.ρ1
    have hδE := h.δE
    have hδI := inE_indec hδE
    have hp := hCB.2.1 p List.mem_cons_self
    have hγ0 : p.2 ≠ 0 := (hCB.1.2 p List.mem_cons_self).ne'
    obtain ⟨W1, Z1, hw1, hHW, hI1⟩ := lyWitH (L := L) h hp.1 hp.2 hγ0
    obtain ⟨W2, Z2, hw2, hRW, hI2⟩ := lyImgList h s hs ps (lyCB_tail hCB)
    set H := L.sys.top ρ * ρ ^ p.1 * p.2 with hH
    set R := lyVal L (ps, s) ρ with hR
    have hRlt : R < L.sys.top ρ * ρ ^ p.1 := lyTail_lt hρE hρ1 hCB
    have hTH : L.sys.top ρ * ρ ^ p.1 ≤ H := le_mul_left _ (pos_iff_ne_zero.2 hγ0)
    have hRH : R < H := hRlt.trans_le hTH
    have hρH : ρ ≤ H := (L.top_gt ρ hρE hρ1).le.trans
      ((le_mul_left _ (opow_pos _ hρE.pos)).trans hTH)
    have hHδ : H < δ := (hw1.1 H hHW).2
    have hv : lyVal L (p :: ps, s) ρ = H + R := lyVal_cons p ps s ρ
    rcases eq_or_ne R 0 with hR0 | hR0
    · have hz := lyVal_zero hρE hρ1 (lyCB_tail hCB) hR0
      refine ⟨W1, Z1, hw1, fun _ => by rw [hv, hR0, add_zero]; exact Finset.mem_union_left _ hHW,
        fun A f hW hZ C => ?_⟩
      rw [lyVal_cons, hv, hR0, add_zero, hz (f ρ), add_zero]
      exact hI1 A f hW hZ C
    · have hRm := hRW hR0
      have hsum : WZ ρ δ (insert (H + R) (W1 ∪ W2)) (Z1 ∪ Z2) := by
        refine (hw1.union hw2).insW (hρH.trans le_self_add) (hδI.add_lt hHδ (hRH.trans hHδ)) (Or.inr ?_)
        refine ⟨H, by simp [hHW], R, ?_, lt_add_of_pos_right _ (pos_iff_ne_zero.2 hR0),
          hRH.trans_le le_self_add, rfl⟩
        rcases Finset.mem_union.1 hRm with h' | h' <;> simp [h']
      refine ⟨_, _, hsum, fun _ => by rw [hv]; simp, fun A f hW hZ C => ?_⟩
      have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
      have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
      have hW2 : ↑W2 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
      have hZ2 : ↑Z2 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
      have hHA : H ∈ A := hW1 hHW
      have hRA : R ∈ A := mem_A hRm hW2 hZ2
      have hvA : H + R ∈ A := hW (by simp)
      rw [lyVal_cons, hv, ← C.add H hHA R hRA (H + R) hvA rfl]
      exact add_le_add (hI1 A f hW1 hZ1 C) (hI2 A f hW2 hZ2 C)

/-- **Lemma IMG for the terms of `lyPoly L`** (the package). -/
theorem lyPkg {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1)
    (t : List (Ordinal.{0} × Ordinal.{0}) × L.sys.Tm) (hCB : lyCB L t (upsilon l))
    (h1 : 1 ≤ lyVal L t (upsilon l)) (R : RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1))) :
    ImgPkg (upsilon l) (upsilon (l + ω + 1)) (lyVal L t) := by
  obtain ⟨ps, s⟩ := t
  have hρE := R.ρE
  have hρ1 := R.ρ1
  have hs : ∃ W Z : Finset Ordinal.{0}, WZ (upsilon l) (upsilon (l + ω + 1)) W Z ∧
      (L.sys.val s (upsilon l) ≠ 0 → L.sys.val s (upsilon l) ∈ W ∪ Z) ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx (upsilon l) A f →
        L.sys.val s (f (upsilon l)) ≤ f (L.sys.val s (upsilon l)) := by
    rcases eq_or_ne (L.sys.val s (upsilon l)) 0 with h0 | h0
    · have hz := lyVal_zero (L := L) (t := ([], s)) hρE hρ1 ⟨⟨List.Pairwise.nil, by simp⟩, by simp [LyBd],
        hCB.2.2⟩ (by rw [lyVal_nil]; exact h0)
      refine ⟨∅, ∅, WZ.empty, fun h' => absurd h0 h', fun A f _ _ _ => ?_⟩
      have := hz (f (upsilon l)); rw [lyVal_nil] at this; rw [this]; exact zero_le
    · obtain ⟨-, -, W, Z, hw, hm, hI⟩ := L.sys.pkg l hl hl1 s hCB.2.2 (one_le_iff_ne_zero.2 h0) R
      exact ⟨W, Z, hw, fun _ => hm, hI⟩
  obtain ⟨W, Z, hw, hm, hI⟩ := lyImgList (L := L) R s hs ps hCB
  have hv0 : lyVal L (ps, s) (upsilon l) ≠ 0 := (lt_of_lt_of_le zero_lt_one h1).ne'
  exact ⟨h1, (lyLt_top hρE hρ1 _ hCB).trans (lyTop_lt_ups hρE hρ1 R.ρδ R.next.2.1), W, Z, hw, hm hv0, hI⟩

/-! ## Lemma RS -/

/-- **Lemma RS for the terms of `lyPoly L`.** -/
theorem lyRs {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1)
    (t : List (Ordinal.{0} × Ordinal.{0}) × L.sys.Tm) (hCB : lyCB L t (upsilon l)) : RsStep l (lyVal L t) := by
  classical
  obtain ⟨ps, s⟩ := t
  rcases eq_or_ne ps [] with rfl | hne
  · rw [lyVal_nil]; exact L.sys.rs l hl hl1 s hCB.2.2
  intro R htg
  have hρE := R.ρE
  have hρ1 := R.ρ1
  have hnx := upsilon_isNext l
  have hCs : ∀ σ, (∀ c ∈ (lyCs L (ps, s)).toFinset, c < σ) → lyCB L (ps, s) σ := fun σ hσ =>
    lyCB_iff _ _ σ hCB (fun c hc => hσ c (List.mem_toFinset.2 hc))
  refine rs_rstF (T := lyVal L (ps, s)) (C := (lyCs L (ps, s)).toFinset) R
    (fun c hc => lyCB_cst _ _ hCB c (List.mem_toFinset.1 hc)) ?_ ?_ ?_ ?_ htg
  · have h1 := lyPv_pos hρE.pos hCB.1 hne
    exact (L.top_gt _ hρE hρ1).le.trans ((le_mul_left _ (lt_of_lt_of_le zero_lt_one h1)).trans le_self_add)
  · exact (lyLt_top hρE hρ1 _ hCB).trans (lyTop_lt_ups hρE hρ1 hnx.1 hnx.2.1)
  · intro σ hσ hB hCσ _
    exact (lyExact hσ R.ρU hB s ps (hCs σ hCσ)).2
  · intro σ hσE hσρ _ hCσ
    have hσ1 := hσρ.trans hρ1
    exact (lyLt_top hσE hσ1 _ (hCs σ hCσ)).trans (lyTop_lt_ups hσE hσ1 hσρ R.ρU)

/-! ## The term system and the layer -/

/-- **The term system of `lyPoly L`.** -/
noncomputable def lySys (L : XtLay) : XtSys where
  Tm := List (Ordinal.{0} × Ordinal.{0}) × L.sys.Tm
  val := lyVal L
  CB := lyCB L
  cs := lyCs L
  cst := fun c => ([], L.sys.cst c)
  top := fun x => L.sys.top x * x ^ x
  cb_cst := lyCB_cst
  cb_iff := lyCB_iff
  val_cst := fun c x => by rw [lyVal_nil]; exact L.sys.val_cst c x
  cb_cstI := fun c x h => ⟨⟨List.Pairwise.nil, by simp⟩, by simp [LyBd], L.sys.cb_cstI c x h⟩
  lt_top := fun l hl hl1 t hCB => lyLt_top (ups_inE hl) (ups_lt_Om1 l hl1) t hCB
  one_le_top := fun l hl hl1 => by
    have hρE := ups_inE hl
    exact (one_le_iff_pos.2 hρE.pos).trans ((L.top_gt _ hρE (ups_lt_Om1 l hl1)).le.trans
      (le_mul_left _ (opow_pos _ hρE.pos)))
  rep := fun l hl hl1 v hv => by
    have hρE := ups_inE hl
    have hρ1 := ups_lt_Om1 l hl1
    have h1ρ : 1 < upsilon l := one_lt_omega0.trans (omega0_lt_inE hρE)
    set ρ := upsilon l with hρdef
    have hT0 : L.sys.top ρ ≠ 0 := (lyT_pos hρE hρ1).ne'
    have hq : v / L.sys.top ρ < ρ ^ ρ := (Ordinal.lt_mul_iff_div_lt hT0).1 hv
    obtain ⟨s, hs, es⟩ := L.sys.rep l hl hl1 _ (mod_lt v hT0)
    refine ⟨(CNF ρ (v / L.sys.top ρ), s), ⟨⟨?_, fun p hp => CNF.snd_pos hp⟩, fun p hp => ⟨?_, CNF.snd_lt h1ρ hp⟩,
      hs⟩, ?_⟩
    · have := CNF.sortedGT ρ (v / L.sys.top ρ)
      rw [List.sortedGT_iff_pairwise, List.pairwise_map] at this
      exact this
    · have hq0 : v / L.sys.top ρ ≠ 0 := by
        intro h0; rw [h0, CNF.zero_right] at hp; simp at hp
      exact (CNF.fst_le_log hp).trans_lt ((lt_opow_iff_log_lt h1ρ hq0).1 hq)
    · show L.sys.top ρ * lyPv ρ (CNF ρ (v / L.sys.top ρ)) + L.sys.val s ρ = v
      rw [es, show lyPv ρ (CNF ρ (v / L.sys.top ρ)) = v / L.sys.top ρ from CNF.foldr ρ _]
      exact div_add_mod v _
  top_lt := fun l hl hl1 => by
    have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
    have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
    exact (lyTop_lt_ups (ups_inE hl) (ups_lt_Om1 l hl1) (upsilon_normal.strictMono h1)
      (upsPt_upsilon (hl0.trans h1))).trans (upsilon_normal.strictMono (lt_add_one _))
  pkg := fun l hl hl1 t hCB h1 R => lyPkg hl hl1 t hCB h1 R
  rs := fun l hl hl1 t hCB => lyRs hl hl1 t hCB
  uni_le := fun σ ρ hσ hρ hB t u ht hu =>
    xt_uni_of_exact hB (lyExact hσ hρ hB t.2 t.1 ht) (lyExact hσ hρ hB u.2 u.1 hu)
  small := fun t => by
    obtain ⟨ps, s⟩ := t
    rcases eq_or_ne ps [] with rfl | hne
    · rcases L.sys.small s with hc | hc
      · exact Or.inl fun x y => by rw [lyVal_nil]; exact hc x y
      · exact Or.inr fun x hx hx1 hCB => by rw [lyVal_nil]; exact hc x hx hx1 hCB.2.2
    · refine Or.inr fun x hx hx1 hCB => ?_
      have h1 := lyPv_pos hx.pos hCB.1 hne
      exact (L.top_gt x hx hx1).le.trans ((le_mul_left _ (lt_of_lt_of_le zero_lt_one h1)).trans le_self_add)

/-- **The layer of all constant exponents**: the terms `T(x)·Σ x^{aᵢ}·γᵢ + s(x)`, top `T(x)·x^x`,
exponent `E(x) + x·x`. -/
noncomputable def lyPoly (L : XtLay) : XtLay where
  sys := lySys L
  E := fun x => L.E x + x * x
  top_eq := fun x hx hx1 => ly_top_pow L hx hx1 x
  exp_dvd := fun x hx hx1 => dvd_add (L.exp_dvd x hx hx1) ⟨x, by rw [show ω ^ x = x from hx]⟩
  exp_lt := fun x hx hx1 => Om1_add_lt (L.exp_lt x hx hx1) (Om1_mul_lt hx1 hx1)
  top_gt := fun x hx hx1 => (L.top_gt x hx hx1).trans_le (le_mul_left _ (opow_pos _ hx.pos))
  top_lt_ups := fun _ _ hx hx1 hxu hu => lyTop_lt_ups hx hx1 hxu hu
  lt_top_E := fun _ hx hx1 t ht => lyLt_top hx hx1 t ht
  exact := fun _ _ hσ hρ hB t ht => lyExact hσ hρ hB t.2 t.1 ht
  exp_pi := fun σ ρ hσ hρ hB => by
    show L.E ρ + ρ * ρ ∈ TB ρ σ ∧ pi σ ρ (L.E ρ + ρ * ρ) = L.E σ + σ * σ
    obtain ⟨h1, h2⟩ := L.exp_pi σ ρ hσ hρ hB
    obtain ⟨h3, h4⟩ := pi_base hB
    obtain ⟨h5, h6⟩ := pi_add hB h3 h3
    rw [h4] at h6
    have hρρ : ρ + ρ < Om1 := Om1_add_lt hB.2.2.2 hB.2.2.2
    obtain ⟨h7, h8⟩ := pi_opowZ hσ hρ hB h5 hρρ
    rw [h6] at h8
    have eρ : ρ * ρ = ω ^ (ρ + ρ) := by rw [← ly_mul_opow hB.2.1, show ω ^ ρ = ρ from hB.2.1]
    have eσ : σ * σ = ω ^ (σ + σ) := by rw [← ly_mul_opow hB.1, show ω ^ σ = σ from hB.1]
    rw [eρ, eσ]
    obtain ⟨h9, h10⟩ := pi_add hB h1 h7
    exact ⟨h9, by rw [h10, h2, h8]⟩
  top_wit := fun ρ τ δ h => by
    obtain ⟨W, Z, hw, hTW, hI⟩ := lyPowTop L h
    refine ⟨W, Z, hw, hTW, fun A f hW hZ C => ?_⟩
    obtain ⟨e', he', hdv, hle⟩ := hI A f hW hZ C
    have hfE := upsPt_inE C.ups
    have hf1 := (C.low ρ C.rho).trans h.ρ1
    refine ⟨⟨e', he', hdv⟩, ?_⟩
    show L.sys.top (f ρ) * f ρ ^ f ρ ≤ f (L.sys.top ρ * ρ ^ ρ)
    rw [ly_top_pow L hfE hf1, he']
    exact opow_le_opow_right omega0_pos hle

theorem lyPoly_top (L : XtLay) (x : Ordinal.{0}) : (lyPoly L).sys.top x = L.sys.top x * x ^ x := rfl

/-- The term `T(x)·x^a` of `lyPoly L` (a constant `a`). -/
def lyPowTm (L : XtLay) (a : Ordinal.{0}) : (lyPoly L).sys.Tm := ([(a, 1)], L.sys.cst 0)

theorem lyPowTm_val (L : XtLay) (a x : Ordinal.{0}) :
    (lyPoly L).sys.val (lyPowTm L a) x = L.sys.top x * x ^ a := by
  show lyVal L ([(a, 1)], L.sys.cst 0) x = _
  rw [lyVal_cons, lyVal_nil, L.sys.val_cst, mul_one, add_zero]

theorem lyPowTm_cb (L : XtLay) {a x : Ordinal.{0}} (hx : UpsPt x) (ha : a < x) :
    (lyPoly L).sys.CB (lyPowTm L a) x :=
  (⟨⟨List.pairwise_singleton _ _, by simp⟩, by simp [LyBd, ha, one_lt_of_upsPt hx],
    L.sys.cb_cstI 0 x hx.1⟩ : lyCB L ([(a, 1)], L.sys.cst 0) x)

end Googology.Trans.PoR.InaccPsi.R2.Ly
