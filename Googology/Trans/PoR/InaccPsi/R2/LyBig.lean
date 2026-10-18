import Googology.Trans.PoR.InaccPsi.R2.LyStep

/-!
# Exponents in `x`: the layer of the terms `Σ ω^{E(x) + dᵢ(x)}·kᵢ + s(x)`, top `T(x)·B(x) = ω^{E(x) + B(x)}`

For a layer `L` (`R2.XtLay`, top `T(x) = ω^{E(x)}`) with `B(x) ≤ E(x)` (`B(x)` the least `φ(ω, ·)`-value above `x`),
the terms of `lyBig L hEB` are a list of pairs `(dᵢ, kᵢ)` (`dᵢ` a term `φ(n, ·)` in `x`, `R2.VzT`, decreasing at every
`υ`-point base above the constants; `0 < kᵢ < ω`) and a term `s` of `L`; the value is `Σ ω^{E(x) + dᵢ(x)}·kᵢ + s(x)`.
Every ordinal below `T(ρ)·B(ρ)` is a value (the Cantor normal form of the quotient by `T(ρ)`, its exponents below
`B(ρ)` values of `φ(n, ·)`-terms, `vzv_rep`).  So the exponents of the powers of `x` are no longer constants:
`T(x)·x^{e(x)} = ω^{E(x) + x·e(x)}` for every `e(x)` with `x·e(x) < B(x)`, and for `T = B` the top is `B(x)²`.

* **EXACT** (`lbExact`): `π_{σ,ρ}(ω^{E(ρ) + d(ρ)}·k) = ω^{E(σ) + d(σ)}·k` (`pi_add`, `vzv_pi`, `pi_opowZ`,
  `pi_mul_nat`);
* **IMG for the exponents `≥ ρ`** (`lbPow`): `f(ω^{E(ρ) + v}) ≥ ω^{E(f(ρ)) + d(f(ρ))}` for every `v < B(ρ)` and every
  term `d` of `v`, by induction on `v = v' + ω^z` (`lg_split`): the term of `z` from Lemma IMG below `B(ρ)` (`imgVz`:
  `z(f(ρ)) ≤ f(z)`); for `z > 0` one atom step `ω^{E+v} ≤₁ ω^{E+v} + z` of `R₁⁺` (`lyStep`, [W07b] Theorem 2.2), for
  `z = 0` the copy of a power is a power; `d(f(ρ)) = d'(f(ρ)) + ω^{z(f(ρ))}` by the comparison at two bases
  (`uniVz_eq`);
* `lbImgList`, `lbPkg` (**IMG**), `lbRs` (**RS**), `lbSys`, and the witness pair of the top (one atom step with
  `q = B(ρ)`, `xtWitB`), so `lyBig L hEB` is a layer with top `ω^{E(x) + B(x)}` (`B(x) ≤ E(x) + B(x)` again).

No new axiom beyond `R2.CitedXt`.

[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ly

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt

/-- Two exponent terms in decreasing order at every `υ`-point base `< Ω₁` above their constants. -/
def LyGt (p q : VzTm × Ordinal.{0}) : Prop :=
  ∀ y, UpsPt y → y < Om1 → (∀ c ∈ p.1.cst', c < y) → (∀ c ∈ q.1.cst', c < y) → q.1.val y < p.1.val y

/-- The exponent terms have their constants below `x`, the coefficients are positive integers. -/
def LyCo (ps : List (VzTm × Ordinal.{0})) (x : Ordinal.{0}) : Prop :=
  ∀ p ∈ ps, p.1.CBt x ∧ 0 < p.2 ∧ p.2 < ω

theorem lyCo_tail {p : VzTm × Ordinal.{0}} {ps : List (VzTm × Ordinal.{0})} {x : Ordinal.{0}}
    (h : LyCo (p :: ps) x) : LyCo ps x := fun q hq => h q (List.mem_cons_of_mem _ hq)

variable (L : XtLay)

/-- `Σ ω^{E(x) + dᵢ(x)}·kᵢ`. -/
noncomputable def lbSum (x : Ordinal.{0}) : List (VzTm × Ordinal.{0}) → Ordinal.{0}
  | [] => 0
  | p :: ps => ω ^ (L.E x + p.1.val x) * p.2 + lbSum x ps

/-- The value `Σ ω^{E(x) + dᵢ(x)}·kᵢ + s(x)`. -/
noncomputable def lbVal (t : List (VzTm × Ordinal.{0}) × L.sys.Tm) (x : Ordinal.{0}) : Ordinal.{0} :=
  lbSum L x t.1 + L.sys.val t.2 x

/-- The constants below `x`, the order and the coefficients. -/
def lbCB (t : List (VzTm × Ordinal.{0}) × L.sys.Tm) (x : Ordinal.{0}) : Prop :=
  t.1.Pairwise LyGt ∧ LyCo t.1 x ∧ L.sys.CB t.2 x

/-- The constants. -/
def lbCs (t : List (VzTm × Ordinal.{0}) × L.sys.Tm) : List Ordinal.{0} :=
  t.1.flatMap (fun p => p.1.cst') ++ L.sys.cs t.2

variable {L}

@[simp] theorem lbSum_nil (x : Ordinal.{0}) : lbSum L x [] = 0 := rfl

theorem lbSum_cons (x : Ordinal.{0}) (p : VzTm × Ordinal.{0}) (ps : List (VzTm × Ordinal.{0})) :
    lbSum L x (p :: ps) = ω ^ (L.E x + p.1.val x) * p.2 + lbSum L x ps := rfl

theorem lbVal_nil (s : L.sys.Tm) : lbVal L ([], s) = L.sys.val s := by
  funext x; simp [lbVal]

theorem lbVal_cons (p : VzTm × Ordinal.{0}) (ps : List (VzTm × Ordinal.{0})) (s : L.sys.Tm) (x : Ordinal.{0}) :
    lbVal L (p :: ps, s) x = ω ^ (L.E x + p.1.val x) * p.2 + lbVal L (ps, s) x := by
  simp only [lbVal, lbSum_cons, add_assoc]

theorem lbCB_tail {p : VzTm × Ordinal.{0}} {ps : List (VzTm × Ordinal.{0})} {s : L.sys.Tm} {x : Ordinal.{0}}
    (h : lbCB L (p :: ps, s) x) : lbCB L (ps, s) x :=
  ⟨(List.pairwise_cons.1 h.1).2, lyCo_tail h.2.1, h.2.2⟩

theorem lbCB_cst (t : List (VzTm × Ordinal.{0}) × L.sys.Tm) (x : Ordinal.{0}) (h : lbCB L t x) :
    ∀ c ∈ lbCs L t, c < x := by
  intro c hc
  simp only [lbCs, List.mem_append, List.mem_flatMap] at hc
  rcases hc with ⟨p, hp, hc⟩ | hc
  · exact VzTm.cbt_cst p.1 x (h.2.1 p hp).1 c hc
  · exact L.sys.cb_cst t.2 x h.2.2 c hc

theorem lbCB_iff (t : List (VzTm × Ordinal.{0}) × L.sys.Tm) (x x' : Ordinal.{0}) (h : lbCB L t x)
    (h' : ∀ c ∈ lbCs L t, c < x') : lbCB L t x' := by
  refine ⟨h.1, fun p hp => ⟨VzTm.cbt_iff p.1 x x' (h.2.1 p hp).1 fun c hc => h' c ?_, (h.2.1 p hp).2⟩,
    L.sys.cb_iff t.2 x x' h.2.2 fun c hc => h' c ?_⟩
  · simp only [lbCs, List.mem_append, List.mem_flatMap]; exact Or.inl ⟨p, hp, hc⟩
  · simp only [lbCs, List.mem_append]; exact Or.inr hc

/-- At a `υ`-point base `x` above the constants the exponents decrease. -/
theorem lbDec_at {ps : List (VzTm × Ordinal.{0})} {x : Ordinal.{0}} (hx : UpsPt x) (hx1 : x < Om1)
    (hP : ps.Pairwise LyGt) (hC : LyCo ps x) : ps.Pairwise (fun p q => q.1.val x < p.1.val x) :=
  hP.imp_of_mem fun {p q} hp hq h => h x hx hx1
    (VzTm.cbt_cst p.1 x (hC p hp).1) (VzTm.cbt_cst q.1 x (hC q hq).1)

theorem lbE_le_T {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : L.E x ≤ L.sys.top x := by
  rw [L.top_eq x hx hx1]; exact right_le_opow _ one_lt_omega0

/-- A sum of the powers with exponents below `E(x) + D`. -/
theorem lbSum_lt {x : Ordinal.{0}} (D : Ordinal.{0}) :
    ∀ ps : List (VzTm × Ordinal.{0}), (∀ p ∈ ps, p.1.val x < D ∧ p.2 < ω) → lbSum L x ps < ω ^ (L.E x + D)
  | [], _ => by simpa using opow_pos (L.E x + D) omega0_pos
  | p :: ps, h => by
    rw [lbSum_cons]
    have hp := h p List.mem_cons_self
    have h1 : ω ^ (L.E x + p.1.val x) * p.2 < ω ^ (L.E x + D) := by
      calc ω ^ (L.E x + p.1.val x) * p.2 < ω ^ (L.E x + p.1.val x) * ω :=
            (mul_lt_mul_iff_right₀ (opow_pos _ omega0_pos)).2 hp.2
        _ = ω ^ (L.E x + p.1.val x + 1) := by rw [opow_add_one]
        _ ≤ ω ^ (L.E x + D) := opow_le_opow_right omega0_pos
            (by rw [add_assoc]; exact add_le_add le_rfl (Order.add_one_le_of_lt hp.1))
    exact (indec_opow _).add_lt h1 (lbSum_lt D ps fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem lbVal_lt_pow {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (D : Ordinal.{0})
    {t : List (VzTm × Ordinal.{0}) × L.sys.Tm} (hs : L.sys.CB t.2 x)
    (h : ∀ p ∈ t.1, p.1.val x < D ∧ p.2 < ω) : lbVal L t x < ω ^ (L.E x + D) := by
  have h2 : L.sys.val t.2 x < ω ^ (L.E x + D) := by
    refine (L.lt_top_E x hx hx1 t.2 hs).trans_le ?_
    rw [L.top_eq x hx hx1]; exact opow_le_opow_right omega0_pos le_self_add
  exact (indec_opow _).add_lt (lbSum_lt D t.1 h) h2

/-- **Every value is below `ω^{E(x) + B(x)}`.** -/
theorem lbLt_top {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (t : List (VzTm × Ordinal.{0}) × L.sys.Tm)
    (h : lbCB L t x) : lbVal L t x < ω ^ (L.E x + VzB x) :=
  lbVal_lt_pow hx hx1 _ h.2.2 fun p hp => ⟨vzv_lt_B hx hx1 (h.2.1 p hp).1, (h.2.1 p hp).2.2⟩

theorem lbTop_lt_ups {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hxu : x < u) (hu : UpsPt u) :
    ω ^ (L.E x + VzB x) < u := by
  have huE := upsPt_inE hu
  have h1 : L.E x < u := (lbE_le_T hx hx1).trans_lt (L.top_lt_ups x u hx hx1 hxu hu)
  exact huE.opow_lt (huE.add_lt h1 (xt_B_lt_ups hx hx1 hxu hu))

/-- The tail below the leading power. -/
theorem lbTail_lt {x : Ordinal.{0}} (hx : UpsPt x) (hx1 : x < Om1) {p : VzTm × Ordinal.{0}}
    {ps : List (VzTm × Ordinal.{0})} {s : L.sys.Tm} (h : lbCB L (p :: ps, s) x) :
    lbVal L (ps, s) x < ω ^ (L.E x + p.1.val x) := by
  have hd := List.pairwise_cons.1 (lbDec_at hx hx1 h.1 h.2.1)
  exact lbVal_lt_pow (upsPt_inE hx) hx1 _ h.2.2 fun q hq =>
    ⟨hd.1 q hq, (h.2.1 q (List.mem_cons_of_mem _ hq)).2.2⟩

theorem lbVal_zero {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {t : List (VzTm × Ordinal.{0}) × L.sys.Tm}
    (h : lbCB L t x) (h0 : lbVal L t x = 0) : ∀ y, lbVal L t y = 0 := by
  obtain ⟨ps, s⟩ := t
  have hs0 : L.sys.val s x = 0 := (add_eq_zero_iff.1 h0).2
  have hps : ps = [] := by
    rcases ps with _ | ⟨p, ps⟩
    · rfl
    · exfalso
      have h1 := (add_eq_zero_iff.1 h0).1
      rw [lbSum_cons] at h1
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
  intro y; simp [lbVal, hconst y]

/-! ## Lemma EXACT -/

theorem lbPiH {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {d : VzTm} (hd : d.CBt σ)
    {k : Ordinal.{0}} (hk : k < ω) :
    ω ^ (L.E ρ + d.val ρ) * k ∈ TB ρ σ ∧ pi σ ρ (ω ^ (L.E ρ + d.val ρ) * k) = ω ^ (L.E σ + d.val σ) * k := by
  have hρ1 := hB.2.2.2
  obtain ⟨h1, h2⟩ := L.exp_pi σ ρ hσ hρ hB
  obtain ⟨h3, h4⟩ := vzv_pi hσ hρ hB d hd
  obtain ⟨h5, h6⟩ := pi_add hB h1 h3
  rw [h2, h4] at h6
  have hd1 : d.val ρ < Om1 :=
    (vzv_lt_B hB.2.1 hρ1 (VzTm.CBt_mono hd hB.2.2.1.le)).trans (xt_B_lt_Om1 hB.2.1 hρ1)
  obtain ⟨h7, h8⟩ := pi_opowZ hσ hρ hB h5 (Om1_add_lt (L.exp_lt ρ hB.2.1 hρ1) hd1)
  rw [h6] at h8
  obtain ⟨n, rfl⟩ := lt_omega0.1 hk
  exact pi_mul_nat hB h7 h8 n

/-- **Lemma EXACT for the terms of `lyBig L`.** -/
theorem lbExact {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) (s : L.sys.Tm) :
    ∀ ps : List (VzTm × Ordinal.{0}), lbCB L (ps, s) σ →
      lbVal L (ps, s) ρ ∈ TB ρ σ ∧ pi σ ρ (lbVal L (ps, s) ρ) = lbVal L (ps, s) σ
  | [], h => by rw [lbVal_nil]; exact L.exact σ ρ hσ hρ hB s h.2.2
  | p :: ps, h => by
    have hp := h.2.1 p List.mem_cons_self
    obtain ⟨h1, h2⟩ := lbPiH (L := L) hσ hρ hB hp.1 hp.2.2
    obtain ⟨h3, h4⟩ := lbExact hσ hρ hB s ps (lbCB_tail h)
    obtain ⟨h5, h6⟩ := pi_add hB h1 h3
    rw [lbVal_cons, lbVal_cons]
    exact ⟨h5, by rw [h6, h2, h4]⟩

/-! ## Lemma IMG -/

variable {ρ τ δ : Ordinal.{0}}

/-- A term with value `0` at a base `x` is the constant `0`. -/
theorem lb_zero_const {d : VzTm} {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hd : d.CBt x)
    (h0 : d.val x = 0) : ∀ y, d.val y = 0 := by
  by_cases hb : d.noB
  · intro y; rw [vzv_noB d hb y x, h0]
  · exact absurd (le_vzv_of_not_noB hx hx1 d hd hb) (by rw [h0]; exact not_le.2 hx.pos)

theorem lb_val_fρ {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (h : RstK ρ τ δ) (C : ImgCtx ρ A f)
    {d e : VzTm} (hd : d.CBt ρ) (he : e.CBt ρ) (hdA : ∀ c ∈ d.cst', c ∈ A) (heA : ∀ c ∈ e.cst', c ∈ A)
    (hde : d.val ρ = e.val ρ) : d.val (f ρ) = e.val (f ρ) :=
  (uniVz_eq C.ups h.ρU (h.img_bases C) (cbt_img C hd hdA) (cbt_img C he heA)).1 hde

/-- **Lemma IMG for `ω^{E(ρ) + v}`, `v < B(ρ)`**: every covering copy maps it to a power `ω^{e'}` with
`E(f(ρ)) + d(f(ρ)) ≤ e'` for every term `d` of `v` with constants in `A`. -/
theorem lbPow (h : RstK ρ τ δ) (hEB : VzB ρ ≤ L.E ρ) : ∀ v, v < VzB ρ →
    ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ ω ^ (L.E ρ + v) ∈ W ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
        ∃ e', f (ω ^ (L.E ρ + v)) = ω ^ e' ∧ ∀ d : VzTm, d.CBt ρ → d.val ρ = v → (∀ c ∈ d.cst', c ∈ A) →
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
  have hBδ : VzB ρ < δ := h.vz_B_lt_δ
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
    rw [lb_zero_const hρE hρ1 hd hdv (f ρ), add_zero]
    rw [L.top_eq _ hfE hf1, he'] at hle
    exact (opow_le_opow_iff_right one_lt_omega0).1 hle
  obtain ⟨v', hvs, -, hv'v⟩ := lg_split hv0
  set z := lg v with hz
  have hzv : z ≤ v := lg_le hv0
  have hzB : z < VzB ρ := hzv.trans_lt hvB
  have hv'B : v' < VzB ρ := hv'v.trans hvB
  obtain ⟨W1, Z1, hw1, hPW1, hI1⟩ := IH v' hv'v hv'B
  obtain ⟨⟨Wz, Zz, sz, hwz, hcz, hcsz, hvz, hmz, hIz⟩, -⟩ := h.imgVz z hzB
  obtain ⟨⟨Wv, Zv, sv, hwv, hcv, hcsv, hvv, -, -⟩, -⟩ := h.imgVz v' hv'B
  set P := ω ^ (L.E ρ + v') with hP
  have hNe : ω ^ (L.E ρ + v) = ω ^ (L.E ρ + v' + ω ^ z) := by rw [hvs, add_assoc]
  have hρP : ρ ≤ P := hρT.le.trans (opow_le_opow_right omega0_pos le_self_add)
  have hNδ : ω ^ (L.E ρ + v' + ω ^ z) < δ := by
    rw [← hNe]; exact h.opow_lt_δ (hδI.add_lt hEδ (hvB.trans hBδ))
  have hw0 : WZ ρ δ ((W1 ∪ Wz) ∪ Wv) ((Z1 ∪ Zz) ∪ Zv) := (hw1.union hwz).union hwv
  have hPW0 : P ∈ (W1 ∪ Wz) ∪ Wv := Finset.mem_union_left _ (Finset.mem_union_left _ hPW1)
  have hzW0 : z ∈ ((W1 ∪ Wz) ∪ Wv) ∪ ((Z1 ∪ Zz) ∪ Zv) := by
    rcases Finset.mem_union.1 hmz with h' | h' <;> simp [h']
  -- the common part of the image: for every term `d` of `v`, `d(f ρ) = sv(f ρ) + ω^{sz(f ρ)}`
  have hsplit : ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑((W1 ∪ Wz) ∪ Wv) ⊆ A →
      ↑((Z1 ∪ Zz) ∪ Zv) ⊆ A → ImgCtx ρ A f → ∃ e1, f P = ω ^ e1 ∧ L.E (f ρ) + sv.val (f ρ) ≤ e1 ∧
        sz.val (f ρ) ≤ f z ∧ ∀ d : VzTm, d.CBt ρ → d.val ρ = v → (∀ c ∈ d.cst', c ∈ A) →
          d.val (f ρ) = sv.val (f ρ) + ω ^ sz.val (f ρ) := by
    intro A f hW hZ C
    have hZv : ∀ c ∈ sv.cst', c ∈ A := fun c hc => hZ (by simp [hcsv c hc])
    have hZz : ∀ c ∈ sz.cst', c ∈ A := fun c hc => hZ (by simp [hcsz c hc])
    obtain ⟨e1, he1, hle1⟩ := hI1 A f (fun x hx => hW (by simp [Finset.mem_coe.1 hx]))
      (fun x hx => hZ (by simp [Finset.mem_coe.1 hx])) C
    refine ⟨e1, he1, hle1 sv hcv hvv hZv, hIz A f (fun x hx => hW (by simp [Finset.mem_coe.1 hx]))
      (fun x hx => hZ (by simp [Finset.mem_coe.1 hx])) C, fun d hd hdv hdA => ?_⟩
    have hsm : (VzTm.sm sv (VzTm.pw sz)).CBt ρ := ⟨hcv, hcz⟩
    have := lb_val_fρ h C hd hsm hdA (fun c hc => by
      simp only [VzTm.cst', List.mem_append] at hc
      rcases hc with hc | hc
      · exact hZv c hc
      · exact hZz c hc) (by rw [hdv, VzTm.val_sm, VzTm.val_pw, hvv, hvz, ← hvs])
    rw [this, VzTm.val_sm, VzTm.val_pw]
  rcases eq_or_ne z 0 with hz0 | hz0
  · -- `v = v' + 1`: the copy of a power is a power
    have hPN : P < ω ^ (L.E ρ + v) :=
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
    have hsz0 : sz.val (f ρ) = 0 := lb_zero_const hρE hρ1 hcz (by rw [hvz, hz0]) (f ρ)
    rw [hsp d hd hdv hdA, hsz0, opow_zero, ← add_assoc]
    exact (add_le_add hle1 le_rfl).trans (Order.add_one_le_of_lt h3)
  · -- `z > 0`: one atom step
    have hqN : z < ω ^ (L.E ρ + v' + ω ^ z) := by
      calc z < VzB ρ := hzB
        _ ≤ L.E ρ := hEB
        _ ≤ ω ^ L.E ρ := right_le_opow _ one_lt_omega0
        _ ≤ ω ^ (L.E ρ + v' + ω ^ z) := opow_le_opow_right omega0_pos (le_self_add.trans le_self_add)
    obtain ⟨W, Z, hw, hNW, hWW, hZZ, hI⟩ :=
      lyStep h hρP (pos_iff_ne_zero.2 hz0) hqN hNδ hw0 hPW0 hzW0
    refine ⟨W, Z, hw, by rw [hNe]; exact hNW, fun A f hW hZ C => ?_⟩
    obtain ⟨e1, he1, hle1, hzf, hsp⟩ :=
      hsplit A f (fun x hx => hW (hWW (Finset.mem_coe.1 hx))) (fun x hx => hZ (hZZ (Finset.mem_coe.1 hx))) C
    obtain ⟨a, ha, -, hnext⟩ := hI A f hW hZ C
    refine ⟨a, by rw [hNe]; exact ha, fun d hd hdv hdA => ?_⟩
    rw [hsp d hd hdv hdA, ← add_assoc]
    exact (add_le_add hle1 (opow_le_opow_right omega0_pos hzf)).trans (hnext e1 he1)

/-- **The witness pair of `ω^{E(ρ) + d(ρ)}·k`** (`0 < k < ω`). -/
theorem lbWitH (h : RstK ρ τ δ) (hEB : VzB ρ ≤ L.E ρ) {d : VzTm} (hd : d.CBt ρ) {k : Ordinal.{0}}
    (hk0 : 0 < k) (hk : k < ω) :
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
  obtain ⟨W1, Z1, hw1, hNW, hI⟩ := lbPow (L := L) h hEB (d.val ρ) (vzv_lt_B hρE hρ1 hd)
  set N := ω ^ (L.E ρ + d.val ρ) with hN
  have hρN : ρ ≤ N := (L.top_gt ρ hρE hρ1).le.trans
    (by rw [L.top_eq ρ hρE hρ1]; exact opow_le_opow_right omega0_pos le_self_add)
  have hNδ : N < δ := (hw1.1 N hNW).2
  have hwc : WZ ρ δ ∅ d.cst'.toFinset :=
    ⟨by simp, fun z hz => VzTm.cbt_cst d ρ hd z (List.mem_toFinset.1 hz), by simp⟩
  have hw2 := (vzWZ_mul hw1 hρN (indec_opow _) hδI hNδ m).union hwc
  rw [Finset.union_empty] at hw2
  refine ⟨_, _, hw2, Finset.mem_union_right _ (vz_mulF_mem N m m le_rfl), fun A f hW hZ C => ?_⟩
  have hW1 : ↑W1 ⊆ A := fun x hx => hW (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 hx)))
  have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 hx)))
  have hdA : ∀ c ∈ d.cst', c ∈ A := fun c hc =>
    hZ (Finset.mem_coe.2 (Finset.mem_union_right _ (List.mem_toFinset.2 hc)))
  obtain ⟨e', he', hle⟩ := hI A f hW1 hZ1 C
  have hmul := vz_copy_mul C (v := N) (q := m) (fun j hj => hW (Finset.mem_coe.2 (Finset.mem_union_right _ (vz_mulF_mem N m j hj)))) m le_rfl
  rw [hmul, he']
  exact mul_le_mul_left (opow_le_opow_right omega0_pos (hle d hd rfl hdA)) _

/-- **Lemma IMG for the terms of `lyBig L`**, as witness sets for the value. -/
theorem lbImgList (h : RstK ρ τ δ) (hEB : VzB ρ ≤ L.E ρ) (s : L.sys.Tm)
    (hs : ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ (L.sys.val s ρ ≠ 0 → L.sys.val s ρ ∈ W ∪ Z) ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
        L.sys.val s (f ρ) ≤ f (L.sys.val s ρ)) :
    ∀ ps : List (VzTm × Ordinal.{0}), lbCB L (ps, s) ρ →
      ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ (lbVal L (ps, s) ρ ≠ 0 → lbVal L (ps, s) ρ ∈ W ∪ Z) ∧
        ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
          lbVal L (ps, s) (f ρ) ≤ f (lbVal L (ps, s) ρ)
  | [], _ => by rw [lbVal_nil]; exact hs
  | p :: ps, hCB => by
    classical
    have hρE := h.ρE
    have hρ1 := h.ρ1
    have hδI := inE_indec h.δE
    have hp := hCB.2.1 p List.mem_cons_self
    obtain ⟨W1, Z1, hw1, hHW, hI1⟩ := lbWitH (L := L) h hEB hp.1 hp.2.1 hp.2.2
    obtain ⟨W2, Z2, hw2, hRW, hI2⟩ := lbImgList h hEB s hs ps (lbCB_tail hCB)
    set H := ω ^ (L.E ρ + p.1.val ρ) * p.2 with hH
    set R := lbVal L (ps, s) ρ with hR
    have hRlt : R < ω ^ (L.E ρ + p.1.val ρ) := lbTail_lt h.ρU hρ1 hCB
    have hNH : ω ^ (L.E ρ + p.1.val ρ) ≤ H := le_mul_left _ hp.2.1
    have hRH : R < H := hRlt.trans_le hNH
    have hρH : ρ ≤ H := (hw1.1 H hHW).1
    have hHδ : H < δ := (hw1.1 H hHW).2
    have hv : lbVal L (p :: ps, s) ρ = H + R := lbVal_cons p ps s ρ
    rcases eq_or_ne R 0 with hR0 | hR0
    · have hz := lbVal_zero hρE hρ1 (lbCB_tail hCB) hR0
      refine ⟨W1, Z1, hw1, fun _ => by rw [hv, hR0, add_zero]; exact Finset.mem_union_left _ hHW,
        fun A f hW hZ C => ?_⟩
      rw [lbVal_cons, hv, hR0, add_zero, hz (f ρ), add_zero]
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
      rw [lbVal_cons, hv, ← C.add H hHA R hRA (H + R) hvA rfl]
      exact add_le_add (hI1 A f hW1 hZ1 C) (hI2 A f hW2 hZ2 C)

/-- **Lemma IMG for the terms of `lyBig L`** (the package). -/
theorem lbPkg (hEB : ∀ x, InE x → x < Om1 → VzB x ≤ L.E x) {l : Ordinal.{0}} (hl : IsRestartIdx l)
    (hl1 : l < Om1) (t : List (VzTm × Ordinal.{0}) × L.sys.Tm) (hCB : lbCB L t (upsilon l))
    (h1 : 1 ≤ lbVal L t (upsilon l)) (R : RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1))) :
    ImgPkg (upsilon l) (upsilon (l + ω + 1)) (lbVal L t) := by
  obtain ⟨ps, s⟩ := t
  have hρE := R.ρE
  have hρ1 := R.ρ1
  have hs : ∃ W Z : Finset Ordinal.{0}, WZ (upsilon l) (upsilon (l + ω + 1)) W Z ∧
      (L.sys.val s (upsilon l) ≠ 0 → L.sys.val s (upsilon l) ∈ W ∪ Z) ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx (upsilon l) A f →
        L.sys.val s (f (upsilon l)) ≤ f (L.sys.val s (upsilon l)) := by
    rcases eq_or_ne (L.sys.val s (upsilon l)) 0 with h0 | h0
    · have hz := lbVal_zero (L := L) (t := ([], s)) hρE hρ1 ⟨List.Pairwise.nil, by simp [LyCo], hCB.2.2⟩
        (by rw [lbVal_nil]; exact h0)
      refine ⟨∅, ∅, WZ.empty, fun h' => absurd h0 h', fun A f _ _ _ => ?_⟩
      have := hz (f (upsilon l)); rw [lbVal_nil] at this; rw [this]; exact zero_le
    · obtain ⟨-, -, W, Z, hw, hm, hI⟩ := L.sys.pkg l hl hl1 s hCB.2.2 (one_le_iff_ne_zero.2 h0) R
      exact ⟨W, Z, hw, fun _ => hm, hI⟩
  obtain ⟨W, Z, hw, hm, hI⟩ := lbImgList (L := L) R (hEB _ hρE hρ1) s hs ps hCB
  have hv0 : lbVal L (ps, s) (upsilon l) ≠ 0 := (lt_of_lt_of_le zero_lt_one h1).ne'
  exact ⟨h1, (lbLt_top hρE hρ1 _ hCB).trans (lbTop_lt_ups hρE hρ1 R.ρδ R.next.2.1), W, Z, hw, hm hv0, hI⟩

/-! ## Lemma RS -/

theorem lb_ge_T {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {ps : List (VzTm × Ordinal.{0})}
    {s : L.sys.Tm} (hC : LyCo ps x) (hne : ps ≠ []) : L.sys.top x ≤ lbVal L (ps, s) x := by
  obtain ⟨p, ps', rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [lbVal_cons, L.top_eq x hx hx1]
  exact ((opow_le_opow_right omega0_pos le_self_add).trans
    (le_mul_left _ (hC p List.mem_cons_self).2.1)).trans le_self_add

/-- **Lemma RS for the terms of `lyBig L`.** -/
theorem lbRs {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1)
    (t : List (VzTm × Ordinal.{0}) × L.sys.Tm) (hCB : lbCB L t (upsilon l)) : RsStep l (lbVal L t) := by
  classical
  obtain ⟨ps, s⟩ := t
  rcases eq_or_ne ps [] with rfl | hne
  · rw [lbVal_nil]; exact L.sys.rs l hl hl1 s hCB.2.2
  intro R htg
  have hρE := R.ρE
  have hρ1 := R.ρ1
  have hnx := upsilon_isNext l
  have hCs : ∀ σ, (∀ c ∈ (lbCs L (ps, s)).toFinset, c < σ) → lbCB L (ps, s) σ := fun σ hσ =>
    lbCB_iff _ _ σ hCB (fun c hc => hσ c (List.mem_toFinset.2 hc))
  refine rs_rstF (T := lbVal L (ps, s)) (C := (lbCs L (ps, s)).toFinset) R
    (fun c hc => lbCB_cst _ _ hCB c (List.mem_toFinset.1 hc)) ?_ ?_ ?_ ?_ htg
  · exact (L.top_gt _ hρE hρ1).le.trans (lb_ge_T hρE hρ1 hCB.2.1 hne)
  · exact (lbLt_top hρE hρ1 _ hCB).trans (lbTop_lt_ups hρE hρ1 hnx.1 hnx.2.1)
  · intro σ hσ hB hCσ _
    exact (lbExact hσ R.ρU hB s ps (hCs σ hCσ)).2
  · intro σ hσE hσρ _ hCσ
    have hσ1 := hσρ.trans hρ1
    exact (lbLt_top hσE hσ1 _ (hCs σ hCσ)).trans (lbTop_lt_ups hσE hσ1 hσρ R.ρU)

/-! ## The representation -/

/-- Terms for a list of exponents below `B(ρ)`. -/
theorem lb_terms {ρ : Ordinal.{0}} (hρE : InE ρ) (hρ1 : ρ < Om1) :
    ∀ l : List (Ordinal.{0} × Ordinal.{0}), (∀ p ∈ l, p.1 < VzB ρ) →
      ∃ ps : List (VzTm × Ordinal.{0}), ps.map (fun p => (p.1.val ρ, p.2)) = l ∧ ∀ p ∈ ps, p.1.CBt ρ
  | [], _ => ⟨[], rfl, by simp⟩
  | q :: l, h => by
    obtain ⟨ps, hps, hc⟩ := lb_terms hρE hρ1 l fun p hp => h p (List.mem_cons_of_mem _ hp)
    obtain ⟨N, hN⟩ := vzB_lt_iff.1 (h q List.mem_cons_self)
    have hN' : q.1 < vt ρ (Om1 * ((max N 1 : ℕ) : Ordinal.{0}) + 0) :=
      hN.trans_le (vzN_le hρE hρ1 (le_max_left N 1))
    obtain ⟨d, hd, hdv⟩ := vzv_rep hρE hρ1 (le_max_right N 1) q.1 hN'
    refine ⟨(d, q.2) :: ps, by simp [hps, hdv], fun p hp => ?_⟩
    rcases List.mem_cons.1 hp with rfl | hp
    · exact hd
    · exact hc p hp

theorem lbSum_eq {x : Ordinal.{0}} : ∀ ps : List (VzTm × Ordinal.{0}),
    lbSum L x ps = ω ^ L.E x * (ps.map (fun p => (p.1.val x, p.2))).foldr (fun p r => ω ^ p.1 * p.2 + r) 0
  | [] => by simp
  | p :: ps => by
    rw [lbSum_cons, lbSum_eq ps, List.map_cons, List.foldr_cons, mul_add, opow_add, mul_assoc]

/-! ## The term system and the layer -/

/-- **The term system of `lyBig L`.** -/
noncomputable def lbSys (L : XtLay) (hEB : ∀ x, InE x → x < Om1 → VzB x ≤ L.E x) : XtSys where
  Tm := List (VzTm × Ordinal.{0}) × L.sys.Tm
  val := lbVal L
  CB := lbCB L
  cs := lbCs L
  cst := fun c => ([], L.sys.cst c)
  top := fun x => ω ^ (L.E x + VzB x)
  cb_cst := lbCB_cst
  cb_iff := lbCB_iff
  val_cst := fun c x => by rw [lbVal_nil]; exact L.sys.val_cst c x
  cb_cstI := fun c x h => ⟨List.Pairwise.nil, by simp [LyCo], L.sys.cb_cstI c x h⟩
  lt_top := fun l hl hl1 t hCB => lbLt_top (ups_inE hl) (ups_lt_Om1 l hl1) t hCB
  one_le_top := fun l hl hl1 => one_le_iff_pos.2 (opow_pos _ omega0_pos)
  rep := fun l hl hl1 v hv => by
    have hρE := ups_inE hl
    have hρ1 := ups_lt_Om1 l hl1
    have hρU := ups_ri hl
    set ρ := upsilon l with hρdef
    have hT0 : ω ^ L.E ρ ≠ 0 := (opow_pos _ omega0_pos).ne'
    have hBE := xt_B_E hρE hρ1
    have hv' : v < ω ^ L.E ρ * ω ^ VzB ρ := by rw [← opow_add]; exact hv
    have hq : v / ω ^ L.E ρ < ω ^ VzB ρ := (Ordinal.lt_mul_iff_div_lt hT0).1 hv'
    have hsT : v % ω ^ L.E ρ < L.sys.top ρ := by rw [L.top_eq ρ hρE hρ1]; exact mod_lt v hT0
    obtain ⟨s, hs, es⟩ := L.sys.rep l hl hl1 _ hsT
    set q := v / ω ^ L.E ρ with hqdef
    have hlog : ∀ p ∈ CNF ω q, p.1 < VzB ρ := fun p hp => by
      have hq0 : q ≠ 0 := by intro h0; rw [h0, CNF.zero_right] at hp; simp at hp
      exact (CNF.fst_le_log hp).trans_lt ((lt_opow_iff_log_lt one_lt_omega0 hq0).1 hq)
    obtain ⟨ps, hps, hpc⟩ := lb_terms hρE hρ1 (CNF ω q) hlog
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
        exact (uniVz_lt hy hρU hB (VzTm.cbt_iff _ ρ y (hpc p' hp') hcy')
          (VzTm.cbt_iff _ ρ y (hpc p hp) hcy)).1 hlt
      · exact hlt
      · have hB : Bases ρ y := ⟨hρE, hyE, hρy, hy1⟩
        exact (uniVz_lt hρU hy hB (hpc p' hp') (hpc p hp)).2 hlt
    · show lbSum L ρ ps + L.sys.val s ρ = v
      rw [es, lbSum_eq, hps, CNF.foldr]
      exact div_add_mod v _
  top_lt := fun l hl hl1 => by
    have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
    have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
    exact (lbTop_lt_ups (ups_inE hl) (ups_lt_Om1 l hl1) (upsilon_normal.strictMono h1)
      (upsPt_upsilon (hl0.trans h1))).trans (upsilon_normal.strictMono (lt_add_one _))
  pkg := fun l hl hl1 t hCB h1 R => lbPkg hEB hl hl1 t hCB h1 R
  rs := fun l hl hl1 t hCB => lbRs hl hl1 t hCB
  uni_le := fun σ ρ hσ hρ hB t u ht hu =>
    xt_uni_of_exact hB (lbExact hσ hρ hB t.2 t.1 ht) (lbExact hσ hρ hB u.2 u.1 hu)
  small := fun t => by
    obtain ⟨ps, s⟩ := t
    rcases eq_or_ne ps [] with rfl | hne
    · rcases L.sys.small s with hc | hc
      · exact Or.inl fun x y => by rw [lbVal_nil]; exact hc x y
      · exact Or.inr fun x hx hx1 hCB => by rw [lbVal_nil]; exact hc x hx hx1 hCB.2.2
    · exact Or.inr fun x hx hx1 hCB => (L.top_gt x hx hx1).le.trans (lb_ge_T hx hx1 hCB.2.1 hne)

/-- **The witness pair of the top `ω^{E(ρ) + B(ρ)}`.** -/
theorem lbTop_wit (hEB : ∀ x, InE x → x < Om1 → VzB x ≤ L.E x) (h : RstK ρ τ δ) :
    ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ ω ^ (L.E ρ + VzB ρ) ∈ W ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
        (∃ e', f (ω ^ (L.E ρ + VzB ρ)) = ω ^ e' ∧ ω ^ f ρ ∣ e') ∧
          ω ^ (L.E (f ρ) + VzB (f ρ)) ≤ f (ω ^ (L.E ρ + VzB ρ)) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hδE := h.δE
  have hδI := inE_indec hδE
  have hTe : L.sys.top ρ = ω ^ L.E ρ := L.top_eq ρ hρE hρ1
  have hρT : ρ < ω ^ L.E ρ := hTe ▸ L.top_gt ρ hρE hρ1
  have hTδ : ω ^ L.E ρ < δ := hTe ▸ L.top_lt_ups ρ δ hρE hρ1 h.ρδ h.next.2.1
  have hEδ : L.E ρ < δ := (right_le_opow _ one_lt_omega0).trans_lt hTδ
  have hBE := xt_B_E hρE hρ1
  have hBr : ω ^ VzB ρ = VzB ρ := hBE
  obtain ⟨Wt, Zt, hwt, hTW, hIt⟩ := L.top_wit ρ τ δ h
  obtain ⟨hwB, hBW, hIB⟩ := xtWitB h
  have hNe : ω ^ (L.E ρ + VzB ρ) = ω ^ (L.E ρ + ω ^ VzB ρ) := by rw [hBr]
  have hNδ : ω ^ (L.E ρ + ω ^ VzB ρ) < δ := by
    rw [← hNe]; exact h.opow_lt_δ (hδI.add_lt hEδ h.vz_B_lt_δ)
  have hqN : VzB ρ < ω ^ (L.E ρ + ω ^ VzB ρ) := by
    rw [← hNe]
    calc VzB ρ = ω ^ VzB ρ := hBr.symm
      _ < ω ^ (VzB ρ + 1) := (opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_one _)
      _ ≤ ω ^ (L.E ρ + VzB ρ) := opow_le_opow_right omega0_pos
          ((add_le_add le_rfl (one_le_iff_pos.2 hBE.pos)).trans (add_le_add (hEB ρ hρE hρ1) le_rfl))
  have hw0 : WZ ρ δ (Wt ∪ {VzB ρ * ω, VzB ρ, ρ}) (Zt ∪ ∅) := hwt.union hwB
  have hPW0 : ω ^ L.E ρ ∈ Wt ∪ {VzB ρ * ω, VzB ρ, ρ} := by rw [← hTe]; simp [hTW]
  have hqW0 : VzB ρ ∈ (Wt ∪ {VzB ρ * ω, VzB ρ, ρ}) ∪ (Zt ∪ ∅) := by simp
  obtain ⟨W, Z, hw, hNW, hWW, hZZ, hI⟩ := lyStep h hρT.le hBE.pos hqN hNδ hw0 hPW0 hqW0
  refine ⟨W, Z, hw, by rw [hNe]; exact hNW, fun A f hW hZ C => ?_⟩
  have hWt : ↑Wt ⊆ A := fun x hx => hW (hWW (by simp [Finset.mem_coe.1 hx]))
  have hZt : ↑Zt ⊆ A := fun x hx => hZ (hZZ (by simp [Finset.mem_coe.1 hx]))
  have hWB : ↑({VzB ρ * ω, VzB ρ, ρ} : Finset Ordinal.{0}) ⊆ A :=
    fun x hx => hW (hWW (Finset.mem_union_right _ (Finset.mem_coe.1 hx)))
  have hBA : VzB ρ ∈ A := hWB (by simp)
  obtain ⟨⟨e1, he1, -⟩, hle1⟩ := hIt A f hWt hZt C
  obtain ⟨-, hfB⟩ := hIB A f hWB (by simp) C
  obtain ⟨a, ha, hdv, hnext⟩ := hI A f hW hZ C
  have hfE := upsPt_inE C.ups
  have hf1 := (C.low ρ C.rho).trans hρ1
  refine ⟨⟨a, by rw [hNe]; exact ha, ?_⟩, ?_⟩
  · exact (opow_dvd_opow ω (C.mono.monotoneOn C.rho hBA (vzB_omega hρE hρ1).2.1.le)).trans hdv
  · rw [hNe, ha]
    have h2 := hnext e1 (by rw [← hTe]; exact he1)
    rw [L.top_eq _ hfE hf1, he1] at hle1
    have hle : L.E (f ρ) ≤ e1 := (opow_le_opow_iff_right one_lt_omega0).1 hle1
    refine opow_le_opow_right omega0_pos ?_
    calc L.E (f ρ) + VzB (f ρ) = L.E (f ρ) + ω ^ VzB (f ρ) := by
          rw [show ω ^ VzB (f ρ) = VzB (f ρ) from xt_B_E hfE hf1]
      _ ≤ e1 + ω ^ f (VzB ρ) := add_le_add hle (opow_le_opow_right omega0_pos hfB)
      _ ≤ a := h2

/-- **The layer of the exponents below `B(x)`**: the terms `Σ ω^{E(x) + dᵢ(x)}·kᵢ + s(x)`, top `ω^{E(x) + B(x)}`. -/
noncomputable def lyBig (L : XtLay) (hEB : ∀ x, InE x → x < Om1 → VzB x ≤ L.E x) : XtLay where
  sys := lbSys L hEB
  E := fun x => L.E x + VzB x
  top_eq := fun _ _ _ => rfl
  exp_dvd := fun x hx hx1 =>
    dvd_add (L.exp_dvd x hx hx1) (opow_dvd_of_inE (xt_B_E hx hx1) (vzB_omega hx hx1).2.1.le)
  exp_lt := fun x hx hx1 => Om1_add_lt (L.exp_lt x hx hx1) (xt_B_lt_Om1 hx hx1)
  top_gt := fun x hx hx1 => by
    have := L.top_gt x hx hx1
    rw [L.top_eq x hx hx1] at this
    exact this.trans_le (opow_le_opow_right omega0_pos le_self_add)
  top_lt_ups := fun _ _ hx hx1 hxu hu => lbTop_lt_ups hx hx1 hxu hu
  lt_top_E := fun _ hx hx1 t ht => lbLt_top hx hx1 t ht
  exact := fun _ _ hσ hρ hB t ht => lbExact hσ hρ hB t.2 t.1 ht
  exp_pi := fun σ ρ hσ hρ hB => by
    obtain ⟨h1, h2⟩ := L.exp_pi σ ρ hσ hρ hB
    obtain ⟨h3, h4⟩ := xtPiB hB
    obtain ⟨h5, h6⟩ := pi_add hB h1 h3
    exact ⟨h5, by rw [h6, h2, h4]⟩
  top_wit := fun ρ τ δ h => lbTop_wit hEB h

theorem lyBig_top (L : XtLay) (hEB : ∀ x, InE x → x < Om1 → VzB x ≤ L.E x) (x : Ordinal.{0}) :
    (lyBig L hEB).sys.top x = ω ^ (L.E x + VzB x) := rfl

theorem lyBig_EB (L : XtLay) (hEB : ∀ x, InE x → x < Om1 → VzB x ≤ L.E x) :
    ∀ x, InE x → x < Om1 → VzB x ≤ (lyBig L hEB).E x :=
  fun x hx hx1 => (hEB x hx hx1).trans le_self_add

/-- The term `ω^{E(x) + d(x)}` of `lyBig L`. -/
def lbPowTm (L : XtLay) (hEB : ∀ x, InE x → x < Om1 → VzB x ≤ L.E x) (d : VzTm) : (lyBig L hEB).sys.Tm :=
  ([(d, 1)], L.sys.cst 0)

theorem lbPowTm_val (L : XtLay) (hEB : ∀ x, InE x → x < Om1 → VzB x ≤ L.E x) (d : VzTm) (x : Ordinal.{0}) :
    (lyBig L hEB).sys.val (lbPowTm L hEB d) x = ω ^ (L.E x + d.val x) := by
  show lbVal L ([(d, 1)], L.sys.cst 0) x = _
  rw [lbVal_cons, lbVal_nil, L.sys.val_cst, mul_one, add_zero]

theorem lbPowTm_cb (L : XtLay) (hEB : ∀ x, InE x → x < Om1 → VzB x ≤ L.E x) {d : VzTm} {x : Ordinal.{0}}
    (hx : UpsPt x) (hd : d.CBt x) : (lyBig L hEB).sys.CB (lbPowTm L hEB d) x :=
  (⟨List.pairwise_singleton _ _, by simp [LyCo, hd], L.sys.cb_cstI 0 x hx.1⟩ :
    lbCB L ([(d, 1)], L.sys.cst 0) x)

end Googology.Trans.PoR.InaccPsi.R2.Ly
