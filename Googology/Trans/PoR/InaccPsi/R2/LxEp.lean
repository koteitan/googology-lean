import Googology.Trans.PoR.InaccPsi.R2.LxTm
import Googology.Trans.PoR.InaccPsi.R2.LyCmp

/-!
# THE GENERIC ε-STEP: from a layer `K` with an `ε`-number top to the layer with top `ε_{E_K(x)+1}`

`R2.LyEp` builds, over a base layer `L` with `B(x) ≤ E_L(x) < ε_{B(x)+1}`, the terms `Σ ω^{E_L(x) + dᵢ(x)}·kᵢ + s(x)`
with exponents `dᵢ` below `ε_{B(x)+1}`.  It cannot pass `Γ(x)`: for `E_L = Γ` the bound `E_L(x) < ε_{B(x)+1}` fails.
Here the exponents are the terms `LxTm K` of `R2.LxTm` over **any** layer `K` with an `ε`-number top (`LxEK K`), and
the bounds are `E_K(x) ≤ E_L(x) < ε_{E_K(x)+1}`:

* `lxSum`, `lxVal` (the value `Σ ω^{E_L(x) + dᵢ(x)}·kᵢ + s(x)`), `lxCB`, `lxCs`; `lxLt_top` (**every value is below
  `ε_{E_K(x)+1}`**);
* **EXACT** (`lxExact`: `lxt_pi`, `pi_opowZ`, `pi_mul_nat`, `pi_add`);
* **IMG for the exponents** (`lxPow`): `f(ω^{E_L(ρ) + v}) ≥ ω^{E_L(f(ρ)) + d(f(ρ))}` for every `v < ε_{E_K(ρ)+1}` and
  every term `d` of `v` (an `ε`-number `lg v` below `ε_{E_K(ρ)+1}` is at most `E_K(ρ) ≤ E_L(ρ)`);
* `lxImgList`, `lxPkg` (**IMG**), `lxRs` (**RS**), `lxEp` (**the term system**, top `ε_{E_K(x)+1}`), `lxTopWit` (**the
  witness pair of the top**: the atom `ε ≤₁ ε·2` of `R₁⁺`, [W07b] §2 after Theorem 2.2, `le1R_two_iff`, makes every
  copy `f(ε)` an `ε`-number above `f(E_K(ρ)) ≥ E_K(f(ρ))`), `lxEp_topPkg`;
* `lxEpLay` (**the layer**: given Lemma EXACT for the top, `LxEpPi K`, the term system is a layer with
  `E(x) = ε_{E_K(x)+1}`), `lxNext K = lxEpLay K K` (**the generic step**: `E_{next}(x) = ε_{E_K(x)+1}`, again an
  `ε`-number, so the step can be repeated), `lxNext_EK`, `lxEp_topIn` (`L`'s top is a term of `lxEp L K`).

No new axiom.

[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Lx

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Ly LxTm

variable {K : XtLay}

/-- Two exponent terms in decreasing order at every `υ`-point base `< Ω₁` above their constants. -/
def LxGt (p q : LxTm K × Ordinal.{0}) : Prop :=
  ∀ y, UpsPt y → y < Om1 → (∀ c ∈ p.1.cs, c < y) → (∀ c ∈ q.1.cs, c < y) → q.1.val y < p.1.val y

/-- The exponent terms have their constants below `x`, the coefficients are positive integers. -/
def LxCo (ps : List (LxTm K × Ordinal.{0})) (x : Ordinal.{0}) : Prop :=
  ∀ p ∈ ps, p.1.CBt x ∧ 0 < p.2 ∧ p.2 < ω

theorem lxCo_tail {p : LxTm K × Ordinal.{0}} {ps : List (LxTm K × Ordinal.{0})} {x : Ordinal.{0}}
    (h : LxCo (p :: ps) x) : LxCo ps x := fun q hq => h q (List.mem_cons_of_mem _ hq)

variable (L : XtLay)

/-- `Σ ω^{E_L(x) + dᵢ(x)}·kᵢ`. -/
noncomputable def lxSum (x : Ordinal.{0}) : List (LxTm K × Ordinal.{0}) → Ordinal.{0}
  | [] => 0
  | p :: ps => ω ^ (L.E x + p.1.val x) * p.2 + lxSum x ps

/-- The value `Σ ω^{E_L(x) + dᵢ(x)}·kᵢ + s(x)`. -/
noncomputable def lxVal (t : List (LxTm K × Ordinal.{0}) × L.sys.Tm) (x : Ordinal.{0}) : Ordinal.{0} :=
  lxSum L x t.1 + L.sys.val t.2 x

/-- The constants below `x`, the order and the coefficients. -/
def lxCB (t : List (LxTm K × Ordinal.{0}) × L.sys.Tm) (x : Ordinal.{0}) : Prop :=
  t.1.Pairwise LxGt ∧ LxCo t.1 x ∧ L.sys.CB t.2 x

/-- The constants. -/
def lxCs (t : List (LxTm K × Ordinal.{0}) × L.sys.Tm) : List Ordinal.{0} :=
  t.1.flatMap (fun p => p.1.cs) ++ L.sys.cs t.2

variable {L}

@[simp] theorem lxSum_nil (x : Ordinal.{0}) : lxSum (K := K) L x [] = 0 := rfl

theorem lxSum_cons (x : Ordinal.{0}) (p : LxTm K × Ordinal.{0}) (ps : List (LxTm K × Ordinal.{0})) :
    lxSum L x (p :: ps) = ω ^ (L.E x + p.1.val x) * p.2 + lxSum L x ps := rfl

theorem lxVal_nil (s : L.sys.Tm) : lxVal (K := K) L ([], s) = L.sys.val s := by
  funext x; simp [lxVal]

theorem lxVal_cons (p : LxTm K × Ordinal.{0}) (ps : List (LxTm K × Ordinal.{0})) (s : L.sys.Tm)
    (x : Ordinal.{0}) : lxVal L (p :: ps, s) x = ω ^ (L.E x + p.1.val x) * p.2 + lxVal L (ps, s) x := by
  simp only [lxVal, lxSum_cons, add_assoc]

theorem lxCB_tail {p : LxTm K × Ordinal.{0}} {ps : List (LxTm K × Ordinal.{0})} {s : L.sys.Tm}
    {x : Ordinal.{0}} (h : lxCB L (p :: ps, s) x) : lxCB L (ps, s) x :=
  ⟨(List.pairwise_cons.1 h.1).2, lxCo_tail h.2.1, h.2.2⟩

theorem lxCB_cst (t : List (LxTm K × Ordinal.{0}) × L.sys.Tm) (x : Ordinal.{0}) (h : lxCB L t x) :
    ∀ c ∈ lxCs L t, c < x := by
  intro c hc
  simp only [lxCs, List.mem_append, List.mem_flatMap] at hc
  rcases hc with ⟨p, hp, hc⟩ | hc
  · exact LxTm.cbt_cst p.1 x (h.2.1 p hp).1 c hc
  · exact L.sys.cb_cst t.2 x h.2.2 c hc

theorem lxCB_iff (t : List (LxTm K × Ordinal.{0}) × L.sys.Tm) (x x' : Ordinal.{0}) (h : lxCB L t x)
    (h' : ∀ c ∈ lxCs L t, c < x') : lxCB L t x' := by
  refine ⟨h.1, fun p hp => ⟨LxTm.cbt_iff p.1 x x' (h.2.1 p hp).1 fun c hc => h' c ?_, (h.2.1 p hp).2⟩,
    L.sys.cb_iff t.2 x x' h.2.2 fun c hc => h' c ?_⟩
  · simp only [lxCs, List.mem_append, List.mem_flatMap]; exact Or.inl ⟨p, hp, hc⟩
  · simp only [lxCs, List.mem_append]; exact Or.inr hc

/-- At a `υ`-point base `x` above the constants the exponents decrease. -/
theorem lxDec_at {ps : List (LxTm K × Ordinal.{0})} {x : Ordinal.{0}} (hx : UpsPt x) (hx1 : x < Om1)
    (hP : ps.Pairwise LxGt) (hC : LxCo ps x) : ps.Pairwise (fun p q => q.1.val x < p.1.val x) :=
  hP.imp_of_mem fun {p q} hp hq h => h x hx hx1
    (LxTm.cbt_cst p.1 x (hC p hp).1) (LxTm.cbt_cst q.1 x (hC q hq).1)

/-- A sum of the powers with exponents below `E_L(x) + D`. -/
theorem lxSum_lt {x : Ordinal.{0}} (D : Ordinal.{0}) :
    ∀ ps : List (LxTm K × Ordinal.{0}), (∀ p ∈ ps, p.1.val x < D ∧ p.2 < ω) →
      lxSum L x ps < ω ^ (L.E x + D)
  | [], _ => by simpa using opow_pos (L.E x + D) omega0_pos
  | p :: ps, h => by
    rw [lxSum_cons]
    have hp := h p List.mem_cons_self
    have h1 : ω ^ (L.E x + p.1.val x) * p.2 < ω ^ (L.E x + D) := by
      calc ω ^ (L.E x + p.1.val x) * p.2 < ω ^ (L.E x + p.1.val x) * ω :=
            (mul_lt_mul_iff_right₀ (opow_pos _ omega0_pos)).2 hp.2
        _ = ω ^ (L.E x + p.1.val x + 1) := by rw [opow_add_one]
        _ ≤ ω ^ (L.E x + D) := opow_le_opow_right omega0_pos
            (by rw [add_assoc]; exact add_le_add le_rfl (Order.add_one_le_of_lt hp.1))
    exact (indec_opow _).add_lt h1 (lxSum_lt D ps fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem lxVal_lt_pow {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (D : Ordinal.{0})
    {t : List (LxTm K × Ordinal.{0}) × L.sys.Tm} (hs : L.sys.CB t.2 x)
    (h : ∀ p ∈ t.1, p.1.val x < D ∧ p.2 < ω) : lxVal L t x < ω ^ (L.E x + D) := by
  have h2 : L.sys.val t.2 x < ω ^ (L.E x + D) := by
    refine (L.lt_top_E x hx hx1 t.2 hs).trans_le ?_
    rw [L.top_eq x hx hx1]; exact opow_le_opow_right omega0_pos le_self_add
  exact (indec_opow _).add_lt (lxSum_lt D t.1 h) h2

/-- `ω^{E_L(x) + ε_{E_K(x)+1}} = ε_{E_K(x)+1}` for `E_L(x) < ε_{E_K(x)+1}`. -/
theorem lx_top_eq {x : Ordinal.{0}} (hEe : L.E x < eN (K.E x)) :
    ω ^ (L.E x + eN (K.E x)) = eN (K.E x) := by
  have he : ω ^ eN (K.E x) = eN (K.E x) := eN_E _
  have h1 : L.E x < ω ^ eN (K.E x) := by rw [he]; exact hEe
  rw [Ordinal.add_of_omega0_opow_le h1 he.le, he]

/-- **Every value is below `ε_{E_K(x)+1}`.** -/
theorem lxLt_top (hK : LxEK K) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hEe : L.E x < eN (K.E x))
    (t : List (LxTm K × Ordinal.{0}) × L.sys.Tm) (h : lxCB L t x) : lxVal L t x < eN (K.E x) := by
  have := lxVal_lt_pow hx hx1 _ h.2.2 fun p hp => ⟨lxt_lt_eN hK hx hx1 _ (h.2.1 p hp).1, (h.2.1 p hp).2.2⟩
  rwa [lx_top_eq hEe] at this

/-- The tail below the leading power. -/
theorem lxTail_lt {x : Ordinal.{0}} (hx : UpsPt x) (hx1 : x < Om1) {p : LxTm K × Ordinal.{0}}
    {ps : List (LxTm K × Ordinal.{0})} {s : L.sys.Tm} (h : lxCB L (p :: ps, s) x) :
    lxVal L (ps, s) x < ω ^ (L.E x + p.1.val x) := by
  have hd := List.pairwise_cons.1 (lxDec_at hx hx1 h.1 h.2.1)
  exact lxVal_lt_pow (upsPt_inE hx) hx1 _ h.2.2 fun q hq =>
    ⟨hd.1 q hq, (h.2.1 q (List.mem_cons_of_mem _ hq)).2.2⟩

theorem lxVal_zero {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
    {t : List (LxTm K × Ordinal.{0}) × L.sys.Tm} (h : lxCB L t x) (h0 : lxVal L t x = 0) :
    ∀ y, lxVal L t y = 0 := by
  obtain ⟨ps, s⟩ := t
  have hs0 : L.sys.val s x = 0 := (add_eq_zero_iff.1 h0).2
  have hps : ps = [] := by
    rcases ps with _ | ⟨p, ps⟩
    · rfl
    · exfalso
      have h1 := (add_eq_zero_iff.1 h0).1
      rw [lxSum_cons] at h1
      have h2 := (add_eq_zero_iff.1 h1).1
      rcases mul_eq_zero.1 h2 with h' | h'
      · exact (opow_pos _ omega0_pos).ne' h'
      · exact (h.2.1 p List.mem_cons_self).2.1.ne' h'
  subst hps
  have hconst : ∀ y, L.sys.val s y = 0 := by
    rcases L.sys.small s with hc | hc
    · intro y; rw [hc y x, hs0]
    · have := hc x hx hx1 h.2.2
      rw [hs0] at this
      exact absurd this (not_le.2 hx.pos)
  intro y; simp [lxVal, hconst y]

/-! ## Lemma EXACT -/

theorem lxPiH (hK : LxEK K) {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {d : LxTm K}
    (hd : d.CBt σ) {k : Ordinal.{0}} (hk : k < ω) :
    ω ^ (L.E ρ + d.val ρ) * k ∈ TB ρ σ ∧ pi σ ρ (ω ^ (L.E ρ + d.val ρ) * k) = ω ^ (L.E σ + d.val σ) * k := by
  have hρ1 := hB.2.2.2
  obtain ⟨h1, h2⟩ := L.exp_pi σ ρ hσ hρ hB
  obtain ⟨h3, h4⟩ := lxt_pi hK hσ hρ hB d hd
  obtain ⟨h5, h6⟩ := pi_add hB h1 h3
  rw [h2, h4] at h6
  have hd1 : d.val ρ < Om1 := lxt_lt_Om1 hK hB.2.1 hρ1 d (LxTm.cbt_mono hd hB.2.2.1.le)
  obtain ⟨h7, h8⟩ := pi_opowZ hσ hρ hB h5 (Om1_add_lt (L.exp_lt ρ hB.2.1 hρ1) hd1)
  rw [h6] at h8
  obtain ⟨n, rfl⟩ := lt_omega0.1 hk
  exact pi_mul_nat hB h7 h8 n

/-- **Lemma EXACT for the terms of `lxEp L K`.** -/
theorem lxExact (hK : LxEK K) {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ)
    (s : L.sys.Tm) : ∀ ps : List (LxTm K × Ordinal.{0}), lxCB L (ps, s) σ →
      lxVal L (ps, s) ρ ∈ TB ρ σ ∧ pi σ ρ (lxVal L (ps, s) ρ) = lxVal L (ps, s) σ
  | [], h => by rw [lxVal_nil]; exact L.exact σ ρ hσ hρ hB s h.2.2
  | p :: ps, h => by
    have hp := h.2.1 p List.mem_cons_self
    obtain ⟨h1, h2⟩ := lxPiH (L := L) hK hσ hρ hB hp.1 hp.2.2
    obtain ⟨h3, h4⟩ := lxExact hK hσ hρ hB s ps (lxCB_tail h)
    obtain ⟨h5, h6⟩ := pi_add hB h1 h3
    rw [lxVal_cons, lxVal_cons]
    exact ⟨h5, by rw [h6, h2, h4]⟩

/-! ## Lemma IMG -/

variable {ρ τ δ : Ordinal.{0}}

/-- **Lemma IMG for `ω^{E_L(ρ) + v}`, `v < ε_{E_K(ρ)+1}`**: every covering copy maps it to a power `ω^{e'}` with
`E_L(f(ρ)) + d(f(ρ)) ≤ e'` for every term `d` of `v` with constants in `A`. -/
theorem lxPow (hK : LxEK K) (h : RstK ρ τ δ) (hb : LxBase K ρ δ) (hEB : K.E ρ ≤ L.E ρ) :
    ∀ v, v < eN (K.E ρ) →
    ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ ω ^ (L.E ρ + v) ∈ W ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
        ∃ e', f (ω ^ (L.E ρ + v)) = ω ^ e' ∧ ∀ d : LxTm K, d.CBt ρ → d.val ρ = v → (∀ c ∈ d.cs, c ∈ A) →
          L.E (f ρ) + d.val (f ρ) ≤ e' := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hδE := h.δE
  have hδI := inE_indec hδE
  have hTe : L.sys.top ρ = ω ^ L.E ρ := L.top_eq ρ hρE hρ1
  have hρT : ρ < ω ^ L.E ρ := hTe ▸ L.top_gt ρ hρE hρ1
  have hTδ : ω ^ L.E ρ < δ := hTe ▸ L.top_lt_ups ρ δ hρE hρ1 h.ρδ h.next.2.1
  have hEδ : L.E ρ < δ := (right_le_opow _ one_lt_omega0).trans_lt hTδ
  have hBδ : eN (K.E ρ) < δ := (lx_eN_lt hK hρE hρ1).2 δ h.ρδ h.next.2.1
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hvB
  rcases eq_or_ne v 0 with rfl | hv0
  · obtain ⟨W, Z, hw, hTW, hI⟩ := L.top_wit ρ τ δ h
    refine ⟨W, Z, hw, by rw [add_zero, ← hTe]; exact hTW, fun A f hW hZ C => ?_⟩
    obtain ⟨⟨e', he', -⟩, hle⟩ := hI A f hW hZ C
    have hfE := upsPt_inE C.ups
    have hf1 := (C.low ρ C.rho).trans hρ1
    refine ⟨e', by rw [add_zero, ← hTe]; exact he', fun d hd hdv hdA => ?_⟩
    rw [lxt_zero hK hρE hρ1 d hd hdv (f ρ), add_zero]
    rw [L.top_eq _ hfE hf1, he'] at hle
    exact (opow_le_opow_iff_right one_lt_omega0).1 hle
  obtain ⟨v', hvs, -, hv'v⟩ := lg_split hv0
  set z := lg v with hz
  have hzv : z ≤ v := lg_le hv0
  have hzB : z < eN (K.E ρ) := hzv.trans_lt hvB
  have hv'B : v' < eN (K.E ρ) := hv'v.trans hvB
  obtain ⟨W1, Z1, hw1, hPW1, hI1⟩ := IH v' hv'v hv'B
  obtain ⟨Wz, Zz, sz, hwz, hcz, hcsz, hvz, hmz, hIz⟩ := lxt_img hK h hb z hzB
  obtain ⟨Wv, Zv, sv, hwv, hcv, hcsv, hvv, -, -⟩ := lxt_img hK h hb v' hv'B
  set P := ω ^ (L.E ρ + v') with hP
  have hNe : ω ^ (L.E ρ + v) = ω ^ (L.E ρ + v' + ω ^ z) := by rw [hvs, add_assoc]
  have hρP : ρ ≤ P := hρT.le.trans (opow_le_opow_right omega0_pos le_self_add)
  have hNδ : ω ^ (L.E ρ + v' + ω ^ z) < δ := by
    rw [← hNe]; exact h.opow_lt_δ (hδI.add_lt hEδ (hvB.trans hBδ))
  have hw0 : WZ ρ δ ((W1 ∪ Wz) ∪ Wv) ((Z1 ∪ Zz) ∪ Zv) := (hw1.union hwz).union hwv
  have hPW0 : P ∈ (W1 ∪ Wz) ∪ Wv := Finset.mem_union_left _ (Finset.mem_union_left _ hPW1)
  have hzW0 : z ∈ ((W1 ∪ Wz) ∪ Wv) ∪ ((Z1 ∪ Zz) ∪ Zv) := by
    rcases Finset.mem_union.1 hmz with h' | h' <;> simp [h']
  have hsplit : ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑((W1 ∪ Wz) ∪ Wv) ⊆ A →
      ↑((Z1 ∪ Zz) ∪ Zv) ⊆ A → ImgCtx ρ A f → ∃ e1, f P = ω ^ e1 ∧ L.E (f ρ) + sv.val (f ρ) ≤ e1 ∧
        sz.val (f ρ) ≤ f z ∧ ∀ d : LxTm K, d.CBt ρ → d.val ρ = v → (∀ c ∈ d.cs, c ∈ A) →
          d.val (f ρ) = sv.val (f ρ) + ω ^ sz.val (f ρ) := by
    intro A f hW hZ C
    have hZv : ∀ c ∈ sv.cs, c ∈ A := fun c hc => hZ (by simp [hcsv c hc])
    have hZz : ∀ c ∈ sz.cs, c ∈ A := fun c hc => hZ (by simp [hcsz c hc])
    obtain ⟨e1, he1, hle1⟩ := hI1 A f (fun x hx => hW (by simp [Finset.mem_coe.1 hx]))
      (fun x hx => hZ (by simp [Finset.mem_coe.1 hx])) C
    refine ⟨e1, he1, hle1 sv hcv hvv hZv, hIz A f (fun x hx => hW (by simp [Finset.mem_coe.1 hx]))
      (fun x hx => hZ (by simp [Finset.mem_coe.1 hx])) C, fun d hd hdv hdA => ?_⟩
    have hsm : (LxTm.sm sv (LxTm.pw sz)).CBt ρ := ⟨hcv, hcz⟩
    have := lxt_val_fρ hK h C hd hsm hdA (fun c hc => by
      simp only [LxTm.cs, List.mem_append] at hc
      rcases hc with hc | hc
      · exact hZv c hc
      · exact hZz c hc) (by rw [hdv, LxTm.val_sm, LxTm.val_pw, hvv, hvz, ← hvs])
    rw [this, LxTm.val_sm, LxTm.val_pw]
  rcases eq_or_ne z 0 with hz0 | hz0
  · have hPN : P < ω ^ (L.E ρ + v) :=
      (opow_lt_opow_iff_right one_lt_omega0).2 ((add_lt_add_iff_left _).2 hv'v)
    have hw : WZ ρ δ (insert (ω ^ (L.E ρ + v)) ((W1 ∪ Wz) ∪ Wv)) ((Z1 ∪ Zz) ∪ Zv) :=
      hw0.insW (hρP.trans hPN.le) (hNe ▸ hNδ) (Or.inl (indec_opow _))
    refine ⟨_, _, hw, by simp, fun A f hW hZ C => ?_⟩
    have hW0 : ↑((W1 ∪ Wz) ∪ Wv) ⊆ A := fun x hx =>
      hW (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx)))
    obtain ⟨e1, he1, hle1, hzf, hsp⟩ := hsplit A f hW0 hZ C
    have hNA : ω ^ (L.E ρ + v) ∈ A := hW (by simp)
    have hPA : P ∈ A := hW0 (Finset.mem_coe.2 hPW0)
    obtain ⟨c, hc⟩ := indec_eq_opow (C.indec _ hNA (indec_opow _))
    have h2 : f P < f (ω ^ (L.E ρ + v)) := C.mono hPA hNA hPN
    rw [hc, he1] at h2
    have h3 : e1 < c := (opow_lt_opow_iff_right one_lt_omega0).1 h2
    refine ⟨c, hc, fun d hd hdv hdA => ?_⟩
    have hsz0 : sz.val (f ρ) = 0 := lxt_zero hK hρE hρ1 sz hcz (by rw [hvz, hz0]) (f ρ)
    rw [hsp d hd hdv hdA, hsz0, opow_zero, ← add_assoc]
    exact (add_le_add hle1 le_rfl).trans (Order.add_one_le_of_lt h3)
  · have hqN : z < ω ^ (L.E ρ + v' + ω ^ z) := by
      have hzz : z ≤ ω ^ z := right_le_opow _ one_lt_omega0
      rcases hzz.lt_or_eq with hlt | heq
      · exact hlt.trans_le (le_add_self.trans (right_le_opow _ one_lt_omega0))
      · have hzle : z ≤ K.E ρ := not_lt.1 fun hBz => lx_no_eps hBz hzB heq.symm
        calc z ≤ L.E ρ := hzle.trans hEB
          _ < L.E ρ + v' + ω ^ z := by
            rw [add_assoc]; exact lt_add_of_pos_right _ (lt_of_lt_of_le (opow_pos z omega0_pos) le_add_self)
          _ ≤ ω ^ (L.E ρ + v' + ω ^ z) := right_le_opow _ one_lt_omega0
    obtain ⟨W, Z, hw, hNW, hWW, hZZ, hI⟩ :=
      lyStep h hρP (pos_iff_ne_zero.2 hz0) hqN hNδ hw0 hPW0 hzW0
    refine ⟨W, Z, hw, by rw [hNe]; exact hNW, fun A f hW hZ C => ?_⟩
    obtain ⟨e1, he1, hle1, hzf, hsp⟩ :=
      hsplit A f (fun x hx => hW (hWW (Finset.mem_coe.1 hx))) (fun x hx => hZ (hZZ (Finset.mem_coe.1 hx))) C
    obtain ⟨a, ha, -, hnext⟩ := hI A f hW hZ C
    refine ⟨a, by rw [hNe]; exact ha, fun d hd hdv hdA => ?_⟩
    rw [hsp d hd hdv hdA, ← add_assoc]
    exact (add_le_add hle1 (opow_le_opow_right omega0_pos hzf)).trans (hnext e1 he1)

/-- **The witness pair of `ω^{E_L(ρ) + d(ρ)}·k`** (`0 < k < ω`). -/
theorem lxWitH (hK : LxEK K) (h : RstK ρ τ δ) (hb : LxBase K ρ δ) (hEB : K.E ρ ≤ L.E ρ) {d : LxTm K}
    (hd : d.CBt ρ) {k : Ordinal.{0}} (hk0 : 0 < k) (hk : k < ω) :
    ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ ω ^ (L.E ρ + d.val ρ) * k ∈ W ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
        ω ^ (L.E (f ρ) + d.val (f ρ)) * k ≤ f (ω ^ (L.E ρ + d.val ρ) * k) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hδI := inE_indec h.δE
  obtain ⟨n, rfl⟩ := lt_omega0.1 hk
  have hn0 : 0 < n := by exact_mod_cast hk0
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨W1, Z1, hw1, hNW, hI⟩ := lxPow (L := L) hK h hb hEB (d.val ρ) (lxt_lt_eN hK hρE hρ1 d hd)
  set N := ω ^ (L.E ρ + d.val ρ) with hN
  have hρN : ρ ≤ N := (L.top_gt ρ hρE hρ1).le.trans
    (by rw [L.top_eq ρ hρE hρ1]; exact opow_le_opow_right omega0_pos le_self_add)
  have hNδ : N < δ := (hw1.1 N hNW).2
  have hwc : WZ ρ δ ∅ d.cs.toFinset :=
    ⟨by simp, fun z hz => LxTm.cbt_cst d ρ hd z (List.mem_toFinset.1 hz), by simp⟩
  have hw2 := (vzWZ_mul hw1 hρN (indec_opow _) hδI hNδ m).union hwc
  rw [Finset.union_empty] at hw2
  refine ⟨_, _, hw2, Finset.mem_union_right _ (vz_mulF_mem N m m le_rfl), fun A f hW hZ C => ?_⟩
  have hW1 : ↑W1 ⊆ A := fun x hx => hW (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 hx)))
  have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 hx)))
  have hdA : ∀ c ∈ d.cs, c ∈ A := fun c hc =>
    hZ (Finset.mem_coe.2 (Finset.mem_union_right _ (List.mem_toFinset.2 hc)))
  obtain ⟨e', he', hle⟩ := hI A f hW1 hZ1 C
  have hmul := vz_copy_mul C (v := N) (q := m)
    (fun j hj => hW (Finset.mem_coe.2 (Finset.mem_union_right _ (vz_mulF_mem N m j hj)))) m le_rfl
  rw [hmul, he']
  exact mul_le_mul_left (opow_le_opow_right omega0_pos (hle d hd rfl hdA)) _

/-- **Lemma IMG for the terms of `lxEp L K`**, as witness sets for the value. -/
theorem lxImgList (hK : LxEK K) (h : RstK ρ τ δ) (hb : LxBase K ρ δ) (hEB : K.E ρ ≤ L.E ρ) (s : L.sys.Tm)
    (hs : ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ (L.sys.val s ρ ≠ 0 → L.sys.val s ρ ∈ W ∪ Z) ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
        L.sys.val s (f ρ) ≤ f (L.sys.val s ρ)) :
    ∀ ps : List (LxTm K × Ordinal.{0}), lxCB L (ps, s) ρ →
      ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ (lxVal L (ps, s) ρ ≠ 0 → lxVal L (ps, s) ρ ∈ W ∪ Z) ∧
        ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
          lxVal L (ps, s) (f ρ) ≤ f (lxVal L (ps, s) ρ)
  | [], _ => by rw [lxVal_nil]; exact hs
  | p :: ps, hCB => by
    classical
    have hρE := h.ρE
    have hρ1 := h.ρ1
    have hδI := inE_indec h.δE
    have hp := hCB.2.1 p List.mem_cons_self
    obtain ⟨W1, Z1, hw1, hHW, hI1⟩ := lxWitH (L := L) hK h hb hEB hp.1 hp.2.1 hp.2.2
    obtain ⟨W2, Z2, hw2, hRW, hI2⟩ := lxImgList hK h hb hEB s hs ps (lxCB_tail hCB)
    set H := ω ^ (L.E ρ + p.1.val ρ) * p.2 with hH
    set R := lxVal L (ps, s) ρ with hR
    have hRlt : R < ω ^ (L.E ρ + p.1.val ρ) := lxTail_lt h.ρU hρ1 hCB
    have hNH : ω ^ (L.E ρ + p.1.val ρ) ≤ H := le_mul_left _ hp.2.1
    have hRH : R < H := hRlt.trans_le hNH
    have hρH : ρ ≤ H := (hw1.1 H hHW).1
    have hHδ : H < δ := (hw1.1 H hHW).2
    have hv : lxVal L (p :: ps, s) ρ = H + R := lxVal_cons p ps s ρ
    rcases eq_or_ne R 0 with hR0 | hR0
    · have hz := lxVal_zero hρE hρ1 (lxCB_tail hCB) hR0
      refine ⟨W1, Z1, hw1, fun _ => by rw [hv, hR0, add_zero]; exact Finset.mem_union_left _ hHW,
        fun A f hW hZ C => ?_⟩
      rw [lxVal_cons, hv, hR0, add_zero, hz (f ρ), add_zero]
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
      rw [lxVal_cons, hv, ← C.add H hHA R hRA (H + R) hvA rfl]
      exact add_le_add (hI1 A f hW1 hZ1 C) (hI2 A f hW2 hZ2 C)

/-- **Lemma IMG for the terms of `lxEp L K`** (the package). -/
theorem lxPkg (hK : LxEK K) (hTE : ∀ x, InE x → x < Om1 → K.E x ≤ L.E x)
    (hEe : ∀ x, InE x → x < Om1 → L.E x < eN (K.E x)) {l : Ordinal.{0}} (hl : IsRestartIdx l)
    (hl1 : l < Om1) (t : List (LxTm K × Ordinal.{0}) × L.sys.Tm) (hCB : lxCB L t (upsilon l))
    (h1 : 1 ≤ lxVal L t (upsilon l)) (R : RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1))) :
    ImgPkg (upsilon l) (upsilon (l + ω + 1)) (lxVal L t) := by
  obtain ⟨ps, s⟩ := t
  have hρE := R.ρE
  have hρ1 := R.ρ1
  have hs : ∃ W Z : Finset Ordinal.{0}, WZ (upsilon l) (upsilon (l + ω + 1)) W Z ∧
      (L.sys.val s (upsilon l) ≠ 0 → L.sys.val s (upsilon l) ∈ W ∪ Z) ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx (upsilon l) A f →
        L.sys.val s (f (upsilon l)) ≤ f (L.sys.val s (upsilon l)) := by
    rcases eq_or_ne (L.sys.val s (upsilon l)) 0 with h0 | h0
    · have hz := lxVal_zero (L := L) (K := K) (t := ([], s)) hρE hρ1 ⟨List.Pairwise.nil, by simp [LxCo], hCB.2.2⟩
        (by rw [lxVal_nil]; exact h0)
      refine ⟨∅, ∅, WZ.empty, fun h' => absurd h0 h', fun A f _ _ _ => ?_⟩
      have := hz (f (upsilon l)); rw [lxVal_nil] at this; rw [this]; exact zero_le
    · obtain ⟨-, -, W, Z, hw, hm, hI⟩ := L.sys.pkg l hl hl1 s hCB.2.2 (one_le_iff_ne_zero.2 h0) R
      exact ⟨W, Z, hw, fun _ => hm, hI⟩
  obtain ⟨W, Z, hw, hm, hI⟩ := lxImgList (L := L) hK R (lxBase_ri hK hl hl1 R) (hTE _ hρE hρ1) s hs ps hCB
  have hv0 : lxVal L (ps, s) (upsilon l) ≠ 0 := (lt_of_lt_of_le zero_lt_one h1).ne'
  exact ⟨h1, (lxLt_top hK hρE hρ1 (hEe _ hρE hρ1) _ hCB).trans
    ((lx_eN_lt hK hρE hρ1).2 _ R.ρδ R.next.2.1), W, Z, hw, hm hv0, hI⟩

/-! ## Lemma RS -/

theorem lx_ge_T {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {ps : List (LxTm K × Ordinal.{0})}
    {s : L.sys.Tm} (hC : LxCo ps x) (hne : ps ≠ []) : L.sys.top x ≤ lxVal L (ps, s) x := by
  obtain ⟨p, ps', rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [lxVal_cons, L.top_eq x hx hx1]
  exact ((opow_le_opow_right omega0_pos le_self_add).trans
    (le_mul_left _ (hC p List.mem_cons_self).2.1)).trans le_self_add

/-- **Lemma RS for the terms of `lxEp L K`.** -/
theorem lxRs (hK : LxEK K) (hEe : ∀ x, InE x → x < Om1 → L.E x < eN (K.E x)) {l : Ordinal.{0}}
    (hl : IsRestartIdx l) (hl1 : l < Om1) (t : List (LxTm K × Ordinal.{0}) × L.sys.Tm)
    (hCB : lxCB L t (upsilon l)) : RsStep l (lxVal L t) := by
  classical
  obtain ⟨ps, s⟩ := t
  rcases eq_or_ne ps [] with rfl | hne
  · rw [lxVal_nil]; exact L.sys.rs l hl hl1 s hCB.2.2
  intro R htg
  have hρE := R.ρE
  have hρ1 := R.ρ1
  have hnx := upsilon_isNext l
  have hCs : ∀ σ, (∀ c ∈ (lxCs L (ps, s)).toFinset, c < σ) → lxCB L (ps, s) σ := fun σ hσ =>
    lxCB_iff _ _ σ hCB (fun c hc => hσ c (List.mem_toFinset.2 hc))
  refine rs_rstF (T := lxVal L (ps, s)) (C := (lxCs L (ps, s)).toFinset) R
    (fun c hc => lxCB_cst _ _ hCB c (List.mem_toFinset.1 hc)) ?_ ?_ ?_ ?_ htg
  · exact (L.top_gt _ hρE hρ1).le.trans (lx_ge_T hρE hρ1 hCB.2.1 hne)
  · exact (lxLt_top hK hρE hρ1 (hEe _ hρE hρ1) _ hCB).trans ((lx_eN_lt hK hρE hρ1).2 _ hnx.1 hnx.2.1)
  · intro σ hσ hB hCσ _
    exact (lxExact hK hσ R.ρU hB s ps (hCs σ hCσ)).2
  · intro σ hσE hσρ _ hCσ
    have hσ1 := hσρ.trans hρ1
    exact (lxLt_top hK hσE hσ1 (hEe σ hσE hσ1) _ (hCs σ hCσ)).trans ((lx_eN_lt hK hσE hσ1).2 _ hσρ R.ρU)

/-! ## The representation -/

/-- Terms for a list of exponents below `ε_{E_K(ρ)+1}`. -/
theorem lx_terms (hK : LxEK K) {ρ : Ordinal.{0}} (hρE : InE ρ) (hρ1 : ρ < Om1) (hr : LxRep K ρ) :
    ∀ l : List (Ordinal.{0} × Ordinal.{0}), (∀ p ∈ l, p.1 < eN (K.E ρ)) →
      ∃ ps : List (LxTm K × Ordinal.{0}), ps.map (fun p => (p.1.val ρ, p.2)) = l ∧ ∀ p ∈ ps, p.1.CBt ρ
  | [], _ => ⟨[], rfl, by simp⟩
  | q :: l, h => by
    obtain ⟨ps, hps, hc⟩ := lx_terms hK hρE hρ1 hr l fun p hp => h p (List.mem_cons_of_mem _ hp)
    obtain ⟨d, hd, hdv⟩ := lxt_rep hK hρE hρ1 hr q.1 (h q List.mem_cons_self)
    refine ⟨(d, q.2) :: ps, by simp [hps, hdv], fun p hp => ?_⟩
    rcases List.mem_cons.1 hp with rfl | hp
    · exact hd
    · exact hc p hp

theorem lxSum_eq {x : Ordinal.{0}} : ∀ ps : List (LxTm K × Ordinal.{0}),
    lxSum L x ps = ω ^ L.E x * (ps.map (fun p => (p.1.val x, p.2))).foldr (fun p r => ω ^ p.1 * p.2 + r) 0
  | [] => by simp
  | p :: ps => by
    rw [lxSum_cons, lxSum_eq ps, List.map_cons, List.foldr_cons, mul_add, opow_add, mul_assoc]

/-! ## The term system -/

/-- **The ε-step term system**: the terms `Σ ω^{E_L(x) + dᵢ(x)}·kᵢ + s(x)` (`dᵢ` terms of `LxTm K`, `s` a term of
`L`), top `ε_{E_K(x)+1}`. -/
noncomputable def lxEp (L K : XtLay) (hK : LxEK K) (hTE : ∀ x, InE x → x < Om1 → K.E x ≤ L.E x)
    (hEe : ∀ x, InE x → x < Om1 → L.E x < eN (K.E x)) : XtSys where
  Tm := List (LxTm K × Ordinal.{0}) × L.sys.Tm
  val := lxVal L
  CB := lxCB L
  cs := lxCs L
  cst := fun c => ([], L.sys.cst c)
  top := fun x => eN (K.E x)
  cb_cst := lxCB_cst
  cb_iff := lxCB_iff
  val_cst := fun c x => by rw [lxVal_nil]; exact L.sys.val_cst c x
  cb_cstI := fun c x h => ⟨List.Pairwise.nil, by simp [LxCo], L.sys.cb_cstI c x h⟩
  lt_top := fun l hl hl1 t hCB =>
    lxLt_top hK (ups_inE hl) (ups_lt_Om1 l hl1) (hEe _ (ups_inE hl) (ups_lt_Om1 l hl1)) t hCB
  one_le_top := fun _ _ _ => one_le_iff_pos.2 (eN_E _).pos
  rep := fun l hl hl1 v hv => by
    have hρE := ups_inE hl
    have hρ1 := ups_lt_Om1 l hl1
    have hρU := ups_ri hl
    have hr := lxRep_ri hK hl hl1
    set ρ := upsilon l with hρdef
    have hT0 : ω ^ L.E ρ ≠ 0 := (opow_pos _ omega0_pos).ne'
    have he := lx_top_eq (L := L) (K := K) (hEe ρ hρE hρ1)
    have hv' : v < ω ^ L.E ρ * ω ^ eN (K.E ρ) := by rw [← opow_add, he]; exact hv
    have hq : v / ω ^ L.E ρ < ω ^ eN (K.E ρ) := (Ordinal.lt_mul_iff_div_lt hT0).1 hv'
    have hsT : v % ω ^ L.E ρ < L.sys.top ρ := by rw [L.top_eq ρ hρE hρ1]; exact mod_lt v hT0
    obtain ⟨s, hs, es⟩ := L.sys.rep l hl hl1 _ hsT
    set q := v / ω ^ L.E ρ with hqdef
    have hlog : ∀ p ∈ CNF ω q, p.1 < eN (K.E ρ) := fun p hp => by
      have hq0 : q ≠ 0 := by intro h0; rw [h0, CNF.zero_right] at hp; simp at hp
      exact (CNF.fst_le_log hp).trans_lt ((lt_opow_iff_log_lt one_lt_omega0 hq0).1 hq)
    obtain ⟨ps, hps, hpc⟩ := lx_terms hK hρE hρ1 hr (CNF ω q) hlog
    have hmem : ∀ p ∈ ps, (p.1.val ρ, p.2) ∈ CNF ω q := fun p hp => by
      rw [← hps]; exact List.mem_map.2 ⟨p, hp, rfl⟩
    have hdecρ : ps.Pairwise (fun p p' => p'.1.val ρ < p.1.val ρ) := by
      have := CNF.sortedGT ω q
      rw [List.sortedGT_iff_pairwise, ← hps, List.map_map, List.pairwise_map] at this
      exact this
    refine ⟨(ps, s), ⟨?_, fun p hp => ⟨hpc p hp, CNF.snd_pos (hmem p hp),
      CNF.snd_lt one_lt_omega0 (hmem p hp)⟩, hs⟩, ?_⟩
    · refine hdecρ.imp_of_mem fun {p p'} hp hp' hlt y hy hy1 hcy hcy' => ?_
      have hyE := upsPt_inE hy
      rcases lt_trichotomy y ρ with hyρ | rfl | hρy
      · have hB : Bases y ρ := ⟨hyE, hρE, hyρ, hρ1⟩
        exact (lxt_uni_lt hK hy hρU hB (LxTm.cbt_iff _ ρ y (hpc p' hp') hcy')
          (LxTm.cbt_iff _ ρ y (hpc p hp) hcy)).1 hlt
      · exact hlt
      · have hB : Bases ρ y := ⟨hρE, hyE, hρy, hy1⟩
        exact (lxt_uni_lt hK hρU hy hB (hpc p' hp') (hpc p hp)).2 hlt
    · show lxSum L ρ ps + L.sys.val s ρ = v
      rw [es, lxSum_eq, hps, CNF.foldr]
      exact div_add_mod v _
  top_lt := fun l hl hl1 => by
    have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
    have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
    exact ((lx_eN_lt hK (ups_inE hl) (ups_lt_Om1 l hl1)).2 _ (upsilon_normal.strictMono h1)
      (upsPt_upsilon (hl0.trans h1))).trans (upsilon_normal.strictMono (lt_add_one _))
  pkg := fun l hl hl1 t hCB h1 R => lxPkg hK hTE hEe hl hl1 t hCB h1 R
  rs := fun l hl hl1 t hCB => lxRs hK hEe hl hl1 t hCB
  uni_le := fun σ ρ hσ hρ hB t u ht hu =>
    xt_uni_of_exact hB (lxExact hK hσ hρ hB t.2 t.1 ht) (lxExact hK hσ hρ hB u.2 u.1 hu)
  small := fun t => by
    obtain ⟨ps, s⟩ := t
    rcases eq_or_ne ps [] with rfl | hne
    · rcases L.sys.small s with hc | hc
      · exact Or.inl fun x y => by rw [lxVal_nil]; exact hc x y
      · exact Or.inr fun x hx hx1 hCB => by rw [lxVal_nil]; exact hc x hx hx1 hCB.2.2
    · exact Or.inr fun x hx hx1 hCB => (L.top_gt x hx hx1).le.trans (lx_ge_T hx hx1 hCB.2.1 hne)

theorem lxEp_top (L K : XtLay) (hK : LxEK K) (hTE : ∀ x, InE x → x < Om1 → K.E x ≤ L.E x)
    (hEe : ∀ x, InE x → x < Om1 → L.E x < eN (K.E x)) (x : Ordinal.{0}) :
    (lxEp L K hK hTE hEe).top x = eN (K.E x) := rfl

/-- **The witness pair of the top `ε_{E_K(ρ)+1}`**: the atom `ε ≤₁ ε·2` of `R₁⁺` makes every copy an `ε`-number above
`f(E_K(ρ)) ≥ E_K(f(ρ))`. -/
theorem lxTopWit (hK : LxEK K) (h : RstK ρ τ δ) :
    ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ eN (K.E ρ) ∈ W ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
        (∃ e', f (eN (K.E ρ)) = ω ^ e' ∧ ω ^ f ρ ∣ e') ∧ eN (K.E (f ρ)) ≤ f (eN (K.E ρ)) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  set e := eN (K.E ρ) with hedef
  have heE : InE e := eN_E _
  have hBe : K.E ρ < e := lt_eN _
  have hρB : ρ < K.E ρ := lx_E_gt hK hρE hρ1
  have heδ : e < δ := (lx_eN_lt hK hρE hρ1).2 δ h.ρδ h.next.2.1
  have hδI := inE_indec h.δE
  have hee : e + e < δ := hδI.add_lt heδ heδ
  obtain ⟨W0, Z0, hw0, hTW, hI⟩ := K.top_wit ρ τ δ h
  rw [lx_top hK hρE hρ1] at hTW
  have hw : WZ ρ δ (insert (e + e) (insert e W0)) Z0 := by
    have w1 := hw0.insW (hρB.trans hBe).le heδ (Or.inl (inE_indec heE))
    exact w1.insW ((hρB.trans hBe).le.trans le_self_add) hee
      (Or.inr ⟨e, by simp, e, by simp, lt_add_of_pos_right _ heE.pos, lt_add_of_pos_right _ heE.pos, rfl⟩)
  refine ⟨_, _, hw, Finset.mem_insert_of_mem (Finset.mem_insert_self e _), fun A f hW hZ C => ?_⟩
  have heA : e ∈ A := hW (by simp)
  have heeA : e + e ∈ A := hW (by simp)
  have hW0 : ↑W0 ⊆ A := fun x hx =>
    hW (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx))))
  have hBA : K.E ρ ∈ A := hW0 hTW
  have hfB : K.E (f ρ) ≤ f (K.E ρ) := by
    have h2 := (hI A f hW0 hZ C).2
    have hfE := upsPt_inE C.ups
    have hf1 := (C.low ρ C.rho).trans hρ1
    rwa [lx_top hK hfE hf1, lx_top hK hρE hρ1] at h2
  have hsrc : le1 e (e + e) := by
    refine (h.lowδ e (e + e) (hρB.trans hBe) hee.le).2 ?_
    rw [← mul_two_eq]; exact (le1R_two_iff heE.pos).2 heE
  have himg : le1 (f e) (f e + f e) := by
    have := C.cov1 e heA (e + e) heeA hsrc
    rwa [← C.add e heA e heA (e + e) heeA rfl] at this
  have hfBe : f (K.E ρ) < f e := C.mono hBA heA hBe
  have hfE : InE (f e) := by
    by_cases hU : UpsPt (f e)
    · exact upsPt_inE hU
    · have hR := (C.sk (f e) (C.low e heA) hU (f e + f e)).1 himg
      have hpos : 0 < f e := lt_of_le_of_lt zero_le hfBe
      rw [← mul_two_eq] at hR
      exact (le1R_two_iff hpos).1 hR
  have hρe : f ρ ≤ f e := (C.mono C.rho heA (hρB.trans hBe)).le
  exact ⟨⟨f e, hfE.symm, opow_dvd_of_inE hfE hρe⟩, eN_le (hfB.trans_lt hfBe) hfE⟩

/-- **The top `ε_{E_K(ρ)+1}` has an IMG package.** -/
theorem lxEp_topPkg (L K : XtLay) (hK : LxEK K) (hTE : ∀ x, InE x → x < Om1 → K.E x ≤ L.E x)
    (hEe : ∀ x, InE x → x < Om1 → L.E x < eN (K.E x)) : XtTopPkg (lxEp L K hK hTE hEe) := fun _ _ _ R => by
  obtain ⟨W, Z, hw, hTW, hI⟩ := lxTopWit hK R
  have hρE := R.ρE
  have hρ1 := R.ρ1
  exact ⟨one_le_iff_pos.2 (eN_E _).pos, (lx_eN_lt hK hρE hρ1).2 _ R.ρδ R.next.2.1, W, Z, hw,
    Finset.mem_union_left _ hTW, fun A f hW hZ C => (hI A f hW hZ C).2⟩

/-! ## The layer -/

/-- **Lemma EXACT for the top `ε_{E_K(x)+1}`** (asked of `K`). -/
def LxEpPi (K : XtLay) : Prop :=
  ∀ σ ρ, UpsPt σ → UpsPt ρ → Bases σ ρ → eN (K.E ρ) ∈ TB ρ σ ∧ pi σ ρ (eN (K.E ρ)) = eN (K.E σ)

/-- **The ε-step layer**: `lxEp L K` with `E(x) = ε_{E_K(x)+1}`, given Lemma EXACT for the top. -/
noncomputable def lxEpLay (L K : XtLay) (hK : LxEK K) (hTE : ∀ x, InE x → x < Om1 → K.E x ≤ L.E x)
    (hEe : ∀ x, InE x → x < Om1 → L.E x < eN (K.E x)) (hpi : LxEpPi K) : XtLay where
  sys := lxEp L K hK hTE hEe
  E := fun x => eN (K.E x)
  top_eq := fun _ _ _ => (eN_E _).symm
  exp_dvd := fun x hx hx1 => opow_dvd_of_inE (eN_E _) ((lx_E_gt hK hx hx1).trans (lt_eN _)).le
  exp_lt := fun _ hx hx1 => (lx_eN_lt hK hx hx1).1
  top_gt := fun _ hx hx1 => (lx_E_gt hK hx hx1).trans (lt_eN _)
  top_lt_ups := fun _ u hx hx1 hxu hu => (lx_eN_lt hK hx hx1).2 u hxu hu
  lt_top_E := fun _ hx hx1 t ht => lxLt_top hK hx hx1 (hEe _ hx hx1) t ht
  exact := fun _ _ hσ hρ hB t ht => lxExact hK hσ hρ hB t.2 t.1 ht
  exp_pi := hpi
  top_wit := fun _ _ _ h => lxTopWit hK h

theorem lxEpLay_E (L K : XtLay) (hK : LxEK K) (hTE : ∀ x, InE x → x < Om1 → K.E x ≤ L.E x)
    (hEe : ∀ x, InE x → x < Om1 → L.E x < eN (K.E x)) (hpi : LxEpPi K) (x : Ordinal.{0}) :
    (lxEpLay L K hK hTE hEe hpi).E x = eN (K.E x) := rfl

/-- **THE GENERIC STEP**: from a layer `K` with an `ε`-number top `E_K(x)` (and Lemma EXACT for `ε_{E_K(x)+1}`) to
the layer of the terms `Σ ω^{E_K(x) + dᵢ(x)}·kᵢ + s(x)` with top `ε_{E_K(x)+1}`. -/
noncomputable def lxNext (K : XtLay) (hK : LxEK K) (hpi : LxEpPi K) : XtLay :=
  lxEpLay K K hK (fun _ _ _ => le_rfl) (fun _ _ _ => lt_eN _) hpi

theorem lxNext_E (K : XtLay) (hK : LxEK K) (hpi : LxEpPi K) (x : Ordinal.{0}) :
    (lxNext K hK hpi).E x = eN (K.E x) := rfl

/-- **The step keeps an `ε`-number top**, so it can be repeated. -/
theorem lxNext_EK (K : XtLay) (hK : LxEK K) (hpi : LxEpPi K) : LxEK (lxNext K hK hpi) :=
  fun _ _ _ => eN_E _

/-- **`lxEp L K` contains the top of `L`** (the term `ω^{E_L(x) + 0}`), with a gap of more than `1`. -/
theorem lxEp_topIn (L K : XtLay) (hK : LxEK K) (hTE : ∀ x, InE x → x < Om1 → K.E x ≤ L.E x)
    (hEe : ∀ x, InE x → x < Om1 → L.E x < eN (K.E x)) : LyTopIn (lxEp L K hK hTE hEe) L.sys := by
  refine ⟨([(LxTm.bs (K.sys.cst 0), 1)], L.sys.cst 0), fun x hx hx1 => ⟨?_, ?_⟩, fun l hl hl1 => ?_⟩
  · exact (⟨List.pairwise_singleton _ _, by simp [LxCo, LxTm.CBt, K.sys.cb_cstI 0 x hx.1],
      L.sys.cb_cstI 0 x hx.1⟩ : lxCB L ([(LxTm.bs (K.sys.cst 0), 1)], L.sys.cst 0) x)
  · show lxVal L ([(LxTm.bs (K.sys.cst 0), 1)], L.sys.cst 0) x = _
    rw [lxVal_cons, lxVal_nil, L.sys.val_cst, LxTm.val_bs, K.sys.val_cst, add_zero, mul_one, add_zero,
      L.top_eq x (upsPt_inE hx) hx1]
  · have hρE := ups_inE hl
    have hρ1 := ups_lt_Om1 l hl1
    show L.sys.top (upsilon l) + 1 < eN (K.E (upsilon l))
    have heE := eN_E (K.E (upsilon l))
    have h1 : L.sys.top (upsilon l) < eN (K.E (upsilon l)) := by
      rw [L.top_eq _ hρE hρ1]
      calc ω ^ L.E (upsilon l) < ω ^ eN (K.E (upsilon l)) :=
            (opow_lt_opow_iff_right one_lt_omega0).2 (hEe _ hρE hρ1)
        _ = eN (K.E (upsilon l)) := heE
    exact (inE_indec heE).add_lt h1 (one_lt_omega0.trans (omega0_lt_inE heE))

end Googology.Trans.PoR.InaccPsi.R2.Lx
