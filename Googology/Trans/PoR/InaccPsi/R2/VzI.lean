import Googology.Trans.PoR.InaccPsi.R2.VzT
import Googology.Trans.PoR.InaccPsi.R2.EvIZ

/-!
# Lemma IMG for every value of a term `φ(n, ·)` in `x`

The project's Lemma IMG for every ordinal `v < VzB ρ = sup_N ϑᵖ(Ω₁·N)`, with a term of `VzTm`, by induction on `v`:

* an `ε`-number `v = ϑᵖ(Ω₁·q + r)` (`1 ≤ q`, `r < v`): inside the block `v ≤₁ v·(q+1) + ζ` (`R₁⁺`, `vz_lh_th_fix`,
  `vz_lh_th_lim`), the copy keeps it, and a copy `f(v)` that is not a `υ`-point lies in `P_q` (`vz_le1R_level`);
  then `ϑ^{fρ}(Ω₁·q + s(fρ)) ≤ f(v)` by the minimality of `R2.VzL` at the base `f(ρ)`:
  - if `ϑᵖ(Ω₁·q + σ) ≤ r` for every `σ < r`, the same holds at `f(ρ)` (base change, `vz_fix_transfer`);
  - if `r = r' + 1`, every `ϑ^{fρ}(Ω₁·q + σ)`, `σ ≤ s'(fρ)`, is at most the copy of `ϑᵖ(Ω₁·q + r')`;
  - if `r = r' + ω^z`, `z > 0`, `f(v) ≥ φ_q(i + ω^{f(z)})` for `φ_q(i) = f(ϑᵖ(Ω₁·q + r'))` (`vz_le1R_ge`), and
    `ϑ^{fρ}(Ω₁·q + s'(fρ) + d) ≤ φ_q(i + d + 1)` (`vz_th_ub`);
* an atom `ω^{e+β}` with the `ε`-base `e`: the argument of `RstK.imgZ` (`R2.EvIZ`), with the IMG of `e`;
* a sum is copied by a sum.

* `ImgVz`, `cbt_img`, `vzMulF`, `vzWZ_mul`, `vz_copy_mul`, `vz_pi_th`, `vz_fix_transfer`, `vz_th_le1R`;
* `RstK.vzImg_th`, `RstK.vzImg_E`, `RstK.vzImg_atom`, `RstK.imgVz` (**Lemma IMG below `VzB ρ`**), `RstK.pkgVz`
  (the IMG package of a term of `VzTm` with value `≥ 1`).

No new axiom beyond `R2.CitedVz`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order VzTm

/-- **The IMG statement for one value** `v` with a term `s` of `VzTm` (`s(ρ) = v`, constants in `Z`). -/
def ImgVz (ρ δ v : Ordinal.{0}) (W Z : Finset Ordinal.{0}) (s : VzTm) : Prop :=
  WZ ρ δ W Z ∧ CBt s ρ ∧ (∀ c ∈ cst' s, c ∈ Z) ∧ val s ρ = v ∧ v ∈ W ∪ Z ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      val s (f ρ) ≤ f v

theorem cbt_img {ρ : Ordinal.{0}} {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}}
    (C : ImgCtx ρ A f) {s : VzTm} (hs : CBt s ρ) (hA : ∀ c ∈ cst' s, c ∈ A) : CBt s (f ρ) :=
  cbt_iff s ρ (f ρ) hs (fun c hc => C.above c (hA c hc) (cbt_cst s ρ hs c hc))

/-! ## Multiples -/

/-- `{v, v·2, …, v·(q+1)}`. -/
noncomputable def vzMulF (v : Ordinal.{0}) : ℕ → Finset Ordinal.{0}
  | 0 => {v}
  | q + 1 => insert (v * ((q + 1 + 1 : ℕ) : Ordinal.{0})) (vzMulF v q)

theorem vz_mulF_mem (v : Ordinal.{0}) : ∀ q j : ℕ, j ≤ q → v * ((j + 1 : ℕ) : Ordinal.{0}) ∈ vzMulF v q
  | 0, j, hj => by
    have : j = 0 := by omega
    subst this; simp [vzMulF]
  | q + 1, j, hj => by
    rcases Nat.lt_or_ge j (q + 1) with h | h
    · exact Finset.mem_insert_of_mem (vz_mulF_mem v q j (by omega))
    · have : j = q + 1 := by omega
      subst this; exact Finset.mem_insert_self _ _

theorem vz_mulF_sub (v : Ordinal.{0}) : ∀ q : ℕ, ∀ w ∈ vzMulF v q, ∃ j : ℕ, j ≤ q ∧ w = v * ((j + 1 : ℕ) : Ordinal.{0})
  | 0, w, hw => ⟨0, le_rfl, by simp [vzMulF] at hw; rw [hw]; simp⟩
  | q + 1, w, hw => by
    rcases Finset.mem_insert.1 hw with rfl | hw
    · exact ⟨q + 1, le_rfl, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := vz_mulF_sub v q w hw
      exact ⟨j, by omega, rfl⟩

theorem vz_mul_lt {δ v : Ordinal.{0}} (hδI : Indec δ) (hv : v < δ) : ∀ k : ℕ, v * (k : Ordinal.{0}) < δ
  | 0 => by rw [Nat.cast_zero, mul_zero]; exact lt_of_le_of_lt zero_le hv
  | k + 1 => by rw [vz_mul_succ]; exact hδI.add_lt (vz_mul_lt hδI hv k) hv

/-- The multiples of an indecomposable `v ∈ [ρ, δ)` may be added to witness sets. -/
theorem vzWZ_mul {ρ δ v : Ordinal.{0}} {W Z : Finset Ordinal.{0}} (hw : WZ ρ δ W Z) (hρv : ρ ≤ v)
    (hvI : Indec v) (hδI : Indec δ) (hvδ : v < δ) : ∀ q : ℕ, WZ ρ δ (W ∪ vzMulF v q) Z
  | 0 => by
    have e : W ∪ vzMulF v 0 = insert v W := by rw [vzMulF, Finset.union_comm, ← Finset.insert_eq]
    rw [e]; exact hw.insW hρv hvδ (Or.inl hvI)
  | q + 1 => by
    have ih := vzWZ_mul hw hρv hvI hδI hvδ q
    have hv0 : 0 < v := hvI.pos
    have e : W ∪ vzMulF v (q + 1) = insert (v * ((q + 1 + 1 : ℕ) : Ordinal.{0})) (W ∪ vzMulF v q) := by
      simp only [vzMulF, Finset.union_insert]
    rw [e]
    refine ih.insW (hρv.trans (vz_le_mul (by omega))) (vz_mul_lt hδI hvδ _)
      (Or.inr ⟨v * ((q + 1 : ℕ) : Ordinal.{0}), ?_, v, ?_, ?_, ?_, (vz_mul_succ v (q + 1)).symm⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (vz_mulF_mem v q q le_rfl))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by
        have := vz_mulF_mem v q 0 (by omega); rwa [zero_add, Nat.cast_one, mul_one] at this))
    · rw [vz_mul_succ v (q + 1)]; exact lt_add_of_pos_right _ hv0
    · rw [vz_mul_succ v (q + 1)]
      exact lt_of_lt_of_le (lt_add_of_pos_right v hv0) (add_le_add_left (vz_le_mul (by omega)) v)

/-- A covering copy multiplies: `f(v·(j+1)) = f(v)·(j+1)` for the multiples in `A`. -/
theorem vz_copy_mul {ρ v : Ordinal.{0}} {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f)
    {q : ℕ} (hA : ∀ j : ℕ, j ≤ q → v * ((j + 1 : ℕ) : Ordinal.{0}) ∈ A) :
    ∀ j : ℕ, j ≤ q → f (v * ((j + 1 : ℕ) : Ordinal.{0})) = f v * ((j + 1 : ℕ) : Ordinal.{0}) := by
  have hv : v ∈ A := by have := hA 0 (by omega); rwa [zero_add, Nat.cast_one, mul_one] at this
  intro j
  induction j with
  | zero => intro _; simp only [zero_add, Nat.cast_one, mul_one]
  | succ j ih =>
    intro hj
    have e1 := C.add _ (hA j (by omega)) v hv _ (hA (j + 1) hj) (vz_mul_succ v (j + 1)).symm
    rw [← e1, ih (by omega), ← vz_mul_succ]

/-! ## Base change of `ϑ`-terms and of the fixed-point property -/

/-- `ϑᵖ(Ω₁·q + γ) ∈ Tᵖ[σ]` and `π_{σ,ρ}(ϑᵖ(Ω₁·q + γ)) = ϑ^σ(Ω₁·q + π_{σ,ρ}(γ))`. -/
theorem vz_pi_th {σ ρ γ : Ordinal.{0}} (hB : Bases σ ρ) (hγ : γ ∈ TB ρ σ) (hγ1 : γ < Om1) (q : ℕ) :
    vt ρ (Om1 * (q : Ordinal.{0}) + γ) ∈ TB ρ σ ∧
      pi σ ρ (vt ρ (Om1 * (q : Ordinal.{0}) + γ)) = vt σ (Om1 * (q : Ordinal.{0}) + pi σ ρ γ) := by
  obtain ⟨hγTB, hpγ⟩ := vz_pi_Om1_mul hB hγ q
  have hγ2 := vzOm1_mul_lt hγ1 q
  obtain ⟨hvT, -, -, -, hvP⟩ := vt_memTwo hB.2.1 hB.2.2.2 hγTB.1 hγ2
  exact ⟨⟨hvT, by rw [hvP]; exact hγTB.2⟩, by rw [pi_vt_two hB hγTB hγ2, hpγ]⟩

theorem vz_pi_lt_Om1 {σ ρ γ : Ordinal.{0}} (hB : Bases σ ρ) (hγ : γ ∈ TB ρ σ) (hγ1 : γ < Om1) :
    pi σ ρ γ < Om1 := by
  have := (pi_bijOn hB).2 hγ (pi_Om1 hB).1 hγ1; rwa [(pi_Om1 hB).2] at this

/-- **The fixed-point property moves with the base change**: if `ϑᵖ(Ω₁·q + σ') ≤ γ` for every `σ' < γ`, then
`ϑ^σ(Ω₁·q + σ') ≤ π(γ)` for every `σ' < π(γ)`. -/
theorem vz_fix_transfer {σ ρ γ : Ordinal.{0}} {q : ℕ} (hB : Bases σ ρ) (hγ : γ ∈ TB ρ σ) (hγ1 : γ < Om1)
    (hfix : ∀ s, s < γ → vt ρ (Om1 * (q : Ordinal.{0}) + s) ≤ γ) :
    ∀ s, s < pi σ ρ γ → vt σ (Om1 * (q : Ordinal.{0}) + s) ≤ pi σ ρ γ := by
  intro s hs
  have hσE := hB.1
  have hσ1 : σ < Om1 := hB.2.2.1.trans hB.2.2.2
  have hpγT : pi σ ρ γ ∈ Tset σ := (pi_bijOn hB).1.mapsTo hγ
  have hpγ1 := vz_pi_lt_Om1 hB hγ hγ1
  have hsT : s ∈ Tset σ := vz_T_down hσE hσ1 hpγT hpγ1 hs.le
  obtain ⟨s', hs'TB, hs'e⟩ := (pi_bijOn hB).1.surjOn hsT
  have hs'γ : s' < γ := by
    by_contra hge; push Not at hge
    have := ((pi_bijOn hB).2.le_iff_le hγ hs'TB).2 hge
    rw [hs'e] at this
    exact absurd hs (not_lt.2 this)
  have hs'1 : s' < Om1 := hs'γ.trans hγ1
  obtain ⟨hvTB, hpv⟩ := vz_pi_th hB hs'TB hs'1 q
  have h1 := ((pi_bijOn hB).2.le_iff_le hvTB hγ).2 (hfix s' hs'γ)
  rwa [hpv, hs'e] at h1

/-- `ϑᵗ(Ω₁·q + η) ≤₁ ϑᵗ(Ω₁·q + η)·(q + 1)` in `R₁⁺`. -/
theorem vz_th_le1R {τ η : Ordinal.{0}} {q : ℕ} (hτ : InE τ) (hτ1 : τ < Om1) (hq : 1 ≤ q) (hη : η ∈ Tset τ)
    (hη1 : η < Om1) :
    le1R (vt τ (Om1 * (q : Ordinal.{0}) + η)) (vt τ (Om1 * (q : Ordinal.{0}) + η) * ((q + 1 : ℕ) : Ordinal.{0})) := by
  by_cases hl : ∃ s, s < η ∧ η < vt τ (Om1 * (q : Ordinal.{0}) + s)
  · have hη0 : η ≠ 0 := by
      obtain ⟨s, hs, -⟩ := hl; exact (lt_of_le_of_lt zero_le hs).ne'
    exact le1R_of_le (vz_le_mul (by omega)) le_self_add (vz_lh_th_lim hτ hτ1 hq hη hη1 hη0 hl).1
  · push Not at hl
    exact (vz_lh_th_fix hτ hτ1 hq hη hη1 hl).1

/-- The `ε`-base is unique: two `ε`-numbers `a, b ≤ X` with `X < eN a`, `X < eN b` are equal. -/
theorem vz_ebase_unique {a b X : Ordinal.{0}} (ha : InE a) (hb : InE b) (hax : a ≤ X) (hxa : X < eN a)
    (hbx : b ≤ X) (hxb : X < eN b) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · exact absurd (lt_of_le_of_lt ((eN_le h hb).trans hbx) hxa) (lt_irrefl _)
  · exact h
  · exact absurd (lt_of_le_of_lt ((eN_le h ha).trans hax) hxb) (lt_irrefl _)

/-- The base change maps `ε`-numbers to `ε`-numbers. -/
theorem vz_pi_E {σ ρ x : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) (hx : x ∈ TB ρ σ)
    (hx1 : x < Om1) (hxE : InE x) : InE (pi σ ρ x) := by
  have hσE := hB.1
  rcases lt_or_ge x σ with hxσ | hσx
  · rw [pi_lt hB hxσ]; exact hxE
  obtain ⟨hxxT, hpxx⟩ := pi_add hB hx hx
  have hle : le1R x (x + x) := by rw [← mul_two_eq]; exact (le1R_two_iff hxE.pos).2 hxE
  have h2 := (down_le1R hσ hρ hB hx hxxT hx1).1 hle
  rw [hpxx] at h2
  have h0 : 0 < pi σ ρ x := by
    have := (pi_bijOn hB).2.lt_iff_lt (mem_TB_of_lt hB hσE.pos) hx |>.2 (hσE.pos.trans_le hσx)
    rwa [pi_lt hB hσE.pos] at this
  exact (le1R_two_iff h0).1 (by rw [mul_two_eq]; exact h2)

namespace RstK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

theorem vz_B_lt_δ : VzB ρ < δ := (vzB_le_next h.ρE h.ρ1 h.ρτ h.τU.2).trans_lt h.τδ

theorem vz_img_base {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f) :
    InE (f ρ) ∧ f ρ < Om1 ∧ Bases (f ρ) ρ :=
  ⟨upsPt_inE C.ups, (C.low ρ C.rho).trans h.ρ1, h.img_bases C⟩

/-- **Lemma IMG at an `ε`-number `v = ϑᵖ(Ω₁·q + r)`** (`1 ≤ q`), from the IMG of the values below `v`. -/
theorem vzImg_th {q : ℕ} (hq : 1 ≤ q) {r v : Ordinal.{0}} (hrT : r ∈ Tset ρ) (hr1 : r < Om1)
    (hve : vt ρ (Om1 * (q : Ordinal.{0}) + r) = v) (hvB : v < VzB ρ)
    (I1 : ∀ u, u < v → ∃ W Z s, ImgVz ρ δ u W Z s) : ∃ W Z s, ImgVz ρ δ v W Z s := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hδI := inE_indec h.δE
  obtain ⟨-, -, hvT, hρv, hv1, hvE, hvI, hrv⟩ := vz_th_facts hρE hρ1 hq hrT hr1
  rw [hve] at hvT hρv hv1 hvE hvI hrv
  have hvδ : v < δ := hvB.trans h.vz_B_lt_δ
  obtain ⟨W1, Z1, s1, w1, cb1, cs1, e1, m1, b1⟩ := I1 r hrv
  have hvq : v * ((q + 1 : ℕ) : Ordinal.{0}) < δ := vz_mul_lt hδI hvδ _
  have hvm : ∀ j : ℕ, j ≤ q → v * ((j + 1 : ℕ) : Ordinal.{0}) ∈ vzMulF v q := vz_mulF_mem v q
  have hvm0 : v ∈ vzMulF v q := by have := hvm 0 (by omega); rwa [zero_add, Nat.cast_one, mul_one] at this
  by_cases hl : ∃ σ, σ < r ∧ r < vt ρ (Om1 * (q : Ordinal.{0}) + σ)
  · have hr0 : r ≠ 0 := by obtain ⟨σ, hσ, -⟩ := hl; exact (lt_of_le_of_lt zero_le hσ).ne'
    obtain ⟨r', hrs, hdvd, hr'r⟩ := lg_split hr0
    set z := lg r with hz
    have hzr : z ≤ r := lg_le hr0
    have hzv : z < v := lt_of_le_of_lt hzr hrv
    have hr'T : r' ∈ Tset ρ := vz_T_down hρE hρ1 hrT hr1 hr'r.le
    have hr'1 : r' < Om1 := hr'r.trans hr1
    set v' := vt ρ (Om1 * (q : Ordinal.{0}) + r') with hv'
    have hv'v : v' < v := by rw [← hve]; exact vz_th_lt hρE hρ1 hq hr'T hrT hr1 hr'r
    obtain ⟨-, -, -, hρv', -, -, hv'I, -⟩ := vz_th_facts hρE hρ1 hq hr'T hr'1
    obtain ⟨W2, Z2, s2, w2, cb2, cs2, e2, m2, b2⟩ := I1 v' hv'v
    obtain ⟨W3, Z3, s3, w3, cb3, cs3, e3, m3, b3⟩ := I1 r' (hr'r.trans hrv)
    have hv'δ : v' < δ := hv'v.trans hvδ
    have hv'q : v' * ((q + 1 : ℕ) : Ordinal.{0}) < δ := vz_mul_lt hδI hv'δ _
    have hsrc' : le1 v' (v' * ((q + 1 : ℕ) : Ordinal.{0})) :=
      (h.lowδ _ _ hρv' hv'q.le).2 (vz_th_le1R hρE hρ1 hq hr'T hr'1)
    have hv'm : ∀ j : ℕ, j ≤ q → v' * ((j + 1 : ℕ) : Ordinal.{0}) ∈ vzMulF v' q := vz_mulF_mem v' q
    rcases eq_or_ne z 0 with hz0 | hz0
    · -- `r = r' + 1`
      rw [hz0, opow_zero] at hrs
      have hsrc : le1 v (v * ((q + 1 : ℕ) : Ordinal.{0})) :=
        (h.lowδ _ _ hρv hvq.le).2 (by rw [← hve]; exact vz_th_le1R hρE hρ1 hq hrT hr1)
      set W0 := W1 ∪ W2 ∪ W3 with hW0
      set Z0 := Z1 ∪ Z2 ∪ Z3 with hZ0
      have wz : WZ ρ δ (W0 ∪ vzMulF v q) Z0 :=
        vzWZ_mul ((w1.union w2).union w3) hρv.le hvI hδI hvδ q
      refine ⟨W0 ∪ vzMulF v q, Z0, th q s1, ⟨wz, ⟨hq, cb1⟩, fun c hc => ?_, by rw [val_th, e1, hve],
        Finset.mem_union_left _ (Finset.mem_union_right _ hvm0), ?_⟩⟩
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (cs1 c hc))
      intro A f hW hZ C
      obtain ⟨hyE, hy1, hB⟩ := h.vz_img_base C
      have hsW : ∀ {S : Finset Ordinal.{0}}, S ⊆ W0 ∪ vzMulF v q → ↑S ⊆ A := fun hS x hx =>
        hW (Finset.mem_coe.2 (hS (Finset.mem_coe.1 hx)))
      have hsZ : ∀ {S : Finset Ordinal.{0}}, S ⊆ Z0 → ↑S ⊆ A := fun hS x hx =>
        hZ (Finset.mem_coe.2 (hS (Finset.mem_coe.1 hx)))
      have hW1 : ↑W1 ⊆ A := hsW (by intro x hx; simp [hW0, hx])
      have hW2 : ↑W2 ⊆ A := hsW (by intro x hx; simp [hW0, hx])
      have hW3 : ↑W3 ⊆ A := hsW (by intro x hx; simp [hW0, hx])
      have hZ1 : ↑Z1 ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
      have hZ2 : ↑Z2 ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
      have hZ3 : ↑Z3 ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
      have hmulA : ∀ j : ℕ, j ≤ q → v * ((j + 1 : ℕ) : Ordinal.{0}) ∈ A := fun j hj =>
        hW (Finset.mem_coe.2 (Finset.mem_union_right _ (hvm j hj)))
      have hvA : v ∈ A := hW (Finset.mem_coe.2 (Finset.mem_union_right _ hvm0))
      have hrA : r ∈ A := mem_A m1 hW1 hZ1
      have hv'A : v' ∈ A := mem_A m2 hW2 hZ2
      have hcb1y := cbt_img C cb1 (fun c hc => hZ1 (Finset.mem_coe.2 (cs1 c hc)))
      have hcb2y := cbt_img C cb2 (fun c hc => hZ2 (Finset.mem_coe.2 (cs2 c hc)))
      have hcb3y := cbt_img C cb3 (fun c hc => hZ3 (Finset.mem_coe.2 (cs3 c hc)))
      have hb1 := b1 A f hW1 hZ1 C
      have hb2 := b2 A f hW2 hZ2 C
      have hfrv : f r < f v := C.mono hrA hvA hrv
      have hfv'v : f v' < f v := C.mono hv'A hvA hv'v
      have hyv : f ρ < f v := C.mono C.rho hvA hρv
      rw [val_th]
      by_cases hU : UpsPt (f v)
      · exact (vzv_lt_ups hyE hy1 (t := th q s1) ⟨hq, hcb1y⟩ hyv hU).le
      have himg : le1 (f v) (f v * ((q + 1 : ℕ) : Ordinal.{0})) := by
        have := C.cov1 v hvA _ (hmulA q le_rfl) hsrc
        rwa [vz_copy_mul C hmulA q le_rfl] at this
      have hR := (C.sk _ (C.low _ hvA) hU _).1 himg
      have hP := vz_le1R_level q hq (f v) (lt_of_le_of_lt zero_le hyv) hR
      have hs1y : val s1 (f ρ) = val s3 (f ρ) + 1 := by
        have hc : CBt (sm s3 (cst 1)) (f ρ) := ⟨hcb3y, one_lt_of_upsPt C.ups⟩
        have := (uniVz_eq C.ups h.ρU hB hcb1y hc).1 (by rw [val_sm, val_cst, e1, e3, hrs])
        rwa [val_sm, val_cst] at this
      have hprev2 : vt (f ρ) (Om1 * (q : Ordinal.{0}) + val s3 (f ρ)) ≤ f v' := by
        have := (uniVz_eq C.ups h.ρU hB (t := th q s3) (u := s2) ⟨hq, hcb3y⟩ hcb2y).1
          (by rw [val_th, e3, e2])
        rw [val_th] at this; rw [this]; exact hb2
      obtain ⟨hs1T, hs1_1⟩ := vzv_T hyE hy1 s1 hcb1y
      obtain ⟨hs3T, hs3_1⟩ := vzv_T hyE hy1 s3 hcb3y
      refine vz_th_min hyE hy1 hq hs1T hs1_1 hP hyv (hb1.trans_lt hfrv) (fun σ hσ => ?_)
      rw [hs1y] at hσ
      have hσ' : σ ≤ val s3 (f ρ) := Order.lt_add_one_iff.1 hσ
      have hσT := vz_T_down hyE hy1 hs3T hs3_1 hσ'
      exact ((vz_th_le hyE hy1 hq hσT hs3T hs3_1 hσ').trans hprev2).trans_lt hfv'v
    · -- `r = r' + ω^z`, `z > 0`
      have hsrcR : le1R v (v * ((q + 1 : ℕ) : Ordinal.{0}) + z) := by
        have := (vz_lh_th_lim hρE hρ1 hq hrT hr1 hr0 hl).1; rwa [hve] at this
      have hvqz : v * ((q + 1 : ℕ) : Ordinal.{0}) + z < δ := hδI.add_lt hvq (hzv.trans hvδ)
      have hsrc : le1 v (v * ((q + 1 : ℕ) : Ordinal.{0}) + z) := (h.lowδ _ _ hρv hvqz.le).2 hsrcR
      obtain ⟨W4, Z4, sz, w4, cb4, cs4, e4, m4, b4⟩ := I1 z hzv
      set W0 := W1 ∪ W2 ∪ W3 ∪ W4 with hW0
      set Z0 := insert 0 (Z1 ∪ Z2 ∪ Z3 ∪ Z4) with hZ0
      have wz0 : WZ ρ δ W0 Z0 := ((((w1.union w2).union w3).union w4).insZ hρE.pos)
      have wz1 := vzWZ_mul wz0 hρv.le hvI hδI hvδ q
      have wz2 := vzWZ_mul wz1 hρv'.le hv'I hδI hv'δ q
      set W5 := W0 ∪ vzMulF v q ∪ vzMulF v' q with hW5
      have hvqm : v * ((q + 1 : ℕ) : Ordinal.{0}) ∈ W5 ∪ Z0 :=
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hvm q le_rfl)))
      have hzm : z ∈ W5 ∪ Z0 := by
        rcases Finset.mem_union.1 m4 with hx | hx
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (by simp [hW0, hx])))
        · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (by simp [hx]))
      have hvlt : v * ((q + 1 : ℕ) : Ordinal.{0}) < v * ((q + 1 : ℕ) : Ordinal.{0}) + z :=
        lt_add_of_pos_right _ (pos_iff_ne_zero.2 hz0)
      have hzlt : z < v * ((q + 1 : ℕ) : Ordinal.{0}) + z :=
        lt_of_lt_of_le hzv ((vz_le_mul (by omega)).trans le_self_add)
      have wz3 : WZ ρ δ (insert (v * ((q + 1 : ℕ) : Ordinal.{0}) + z) W5) Z0 :=
        wz2.insW (hρv.le.trans ((vz_le_mul (by omega)).trans le_self_add)) hvqz
          (Or.inr ⟨_, hvqm, z, hzm, hvlt, hzlt, rfl⟩)
      refine ⟨insert (v * ((q + 1 : ℕ) : Ordinal.{0}) + z) W5, Z0, th q s1, ⟨wz3, ⟨hq, cb1⟩,
        fun c hc => Finset.mem_insert_of_mem (by simp [cs1 c hc]), by rw [val_th, e1, hve],
        Finset.mem_union_left _ (Finset.mem_insert_of_mem
          (Finset.mem_union_left _ (Finset.mem_union_right _ hvm0))), ?_⟩⟩
      intro A f hW hZ C
      obtain ⟨hyE, hy1, hB⟩ := h.vz_img_base C
      have hsW : ∀ {S : Finset Ordinal.{0}}, S ⊆ W0 → ↑S ⊆ A := fun hS x hx =>
        hW (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _
          (hS (Finset.mem_coe.1 hx))))))
      have hsZ : ∀ {S : Finset Ordinal.{0}}, S ⊆ Z0 → ↑S ⊆ A := fun hS x hx =>
        hZ (Finset.mem_coe.2 (hS (Finset.mem_coe.1 hx)))
      have hW1 : ↑W1 ⊆ A := hsW (by intro x hx; simp [hW0, hx])
      have hW2 : ↑W2 ⊆ A := hsW (by intro x hx; simp [hW0, hx])
      have hW3 : ↑W3 ⊆ A := hsW (by intro x hx; simp [hW0, hx])
      have hW4 : ↑W4 ⊆ A := hsW (by intro x hx; simp [hW0, hx])
      have hZ1 : ↑Z1 ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
      have hZ2 : ↑Z2 ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
      have hZ3 : ↑Z3 ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
      have hZ4 : ↑Z4 ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
      have h0A : (0 : Ordinal.{0}) ∈ A := hsZ (S := {0}) (by simp [hZ0]) (by simp)
      have hmulA : ∀ j : ℕ, j ≤ q → v * ((j + 1 : ℕ) : Ordinal.{0}) ∈ A := fun j hj =>
        hW (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_union_left _
          (Finset.mem_union_right _ (hvm j hj)))))
      have hmul'A : ∀ j : ℕ, j ≤ q → v' * ((j + 1 : ℕ) : Ordinal.{0}) ∈ A := fun j hj =>
        hW (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_union_right _ (hv'm j hj))))
      have hvqzA : v * ((q + 1 : ℕ) : Ordinal.{0}) + z ∈ A := hW (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
      have hvA : v ∈ A := by have := hmulA 0 (by omega); rwa [zero_add, Nat.cast_one, mul_one] at this
      have hv'A : v' ∈ A := by have := hmul'A 0 (by omega); rwa [zero_add, Nat.cast_one, mul_one] at this
      have hrA : r ∈ A := mem_A m1 hW1 hZ1
      have hzA : z ∈ A := mem_A m4 hW4 hZ4
      have hcb1y := cbt_img C cb1 (fun c hc => hZ1 (Finset.mem_coe.2 (cs1 c hc)))
      have hcb2y := cbt_img C cb2 (fun c hc => hZ2 (Finset.mem_coe.2 (cs2 c hc)))
      have hcb3y := cbt_img C cb3 (fun c hc => hZ3 (Finset.mem_coe.2 (cs3 c hc)))
      have hcb4y := cbt_img C cb4 (fun c hc => hZ4 (Finset.mem_coe.2 (cs4 c hc)))
      have hb1 := b1 A f hW1 hZ1 C
      have hb2 := b2 A f hW2 hZ2 C
      have hb4 := b4 A f hW4 hZ4 C
      have hfrv : f r < f v := C.mono hrA hvA hrv
      have hfv'v : f v' < f v := C.mono hv'A hvA hv'v
      have hyv : f ρ < f v := C.mono C.rho hvA hρv
      have hyv' : f ρ < f v' := C.mono C.rho hv'A hρv'
      rw [val_th]
      by_cases hU : UpsPt (f v)
      · exact (vzv_lt_ups hyE hy1 (t := th q s1) ⟨hq, hcb1y⟩ hyv hU).le
      by_cases hU' : UpsPt (f v')
      · exact ((vzv_lt_ups hyE hy1 (t := th q s1) ⟨hq, hcb1y⟩ hyv' hU').trans hfv'v).le
      have himg : le1 (f v) (f v * ((q + 1 : ℕ) : Ordinal.{0}) + f z) := by
        have := C.cov1 v hvA _ hvqzA hsrc
        rwa [← C.add _ (hmulA q le_rfl) z hzA _ hvqzA rfl, vz_copy_mul C hmulA q le_rfl] at this
      have hR := (C.sk _ (C.low _ hvA) hU _).1 himg
      have himg' : le1 (f v') (f v' * ((q + 1 : ℕ) : Ordinal.{0})) := by
        have := C.cov1 v' hv'A _ (hmul'A q le_rfl) hsrc'
        rwa [vz_copy_mul C hmul'A q le_rfl] at this
      have hR' := (C.sk _ (C.low _ hv'A) hU' _).1 himg'
      obtain ⟨i, hi⟩ := vz_le1R_level q hq (f v') (lt_of_le_of_lt zero_le hyv') hR'
      have hfz : f z < f v := C.mono hzA hvA hzv
      have hge := vz_le1R_ge hq (f z) (f v) i hfz (by rw [hi]; exact hfv'v) hR
      have hP := vz_le1R_level q hq (f v) (lt_of_le_of_lt zero_le hyv) (vz_le1R_base hR)
      have hs1y : val s1 (f ρ) = val s3 (f ρ) + ω ^ val sz (f ρ) := by
        have hc : CBt (sm s3 (pw sz)) (f ρ) := ⟨hcb3y, hcb4y⟩
        have := (uniVz_eq C.ups h.ρU hB hcb1y hc).1 (by rw [val_sm, val_pw, e1, e3, e4, hrs])
        rwa [val_sm, val_pw] at this
      have hprev2 : vt (f ρ) (Om1 * (q : Ordinal.{0}) + val s3 (f ρ)) ≤ f v' := by
        have := (uniVz_eq C.ups h.ρU hB (t := th q s3) (u := s2) ⟨hq, hcb3y⟩ hcb2y).1
          (by rw [val_th, e3, e2])
        rw [val_th] at this; rw [this]; exact hb2
      have hfz0 : f z ≠ 0 := by
        have h1 : f 0 < f z := C.mono h0A hzA (pos_iff_ne_zero.2 hz0)
        rw [C.fix 0 h0A hρE.pos] at h1
        exact h1.ne'
      obtain ⟨hs1T, hs1_1⟩ := vzv_T hyE hy1 s1 hcb1y
      obtain ⟨hs3T, hs3_1⟩ := vzv_T hyE hy1 s3 hcb3y
      refine vz_th_min hyE hy1 hq hs1T hs1_1 hP hyv (hb1.trans_lt hfrv) (fun σ hσ => ?_)
      have hσT := vz_T_down hyE hy1 hs1T hs1_1 hσ.le
      have hσ1 : σ < Om1 := hσ.trans hs1_1
      rw [hs1y] at hσ
      rcases lt_or_ge σ (val s3 (f ρ)) with hσs | hsσ
      · exact ((vz_th_lt hyE hy1 hq hσT hs3T hs3_1 hσs).le.trans hprev2).trans_lt hfv'v
      set d := σ - val s3 (f ρ) with hd
      have hσe : val s3 (f ρ) + d = σ := Ordinal.add_sub_cancel_of_le hsσ
      have hdz : d < ω ^ val sz (f ρ) := (add_lt_add_iff_left _).1 (by rw [hσe]; exact hσ)
      have hsb : val s3 (f ρ) < veblen (q : Ordinal.{0}) i :=
        (vzLt_vt_self hyE hy1 hq hs3T hs3_1).trans_le (by rw [hi]; exact hprev2)
      have hub := vz_th_ub hyE hy1 hq hs3T hs3_1 (by rw [hi]; exact hprev2) hsb d
        (by rw [hσe]; exact hσT) (by rw [hσe]; exact hσ1)
      rw [hσe] at hub
      refine lt_of_le_of_lt hub (lt_of_lt_of_le ((veblen_lt_veblen_iff_right).2 ?_) hge)
      rw [add_assoc]
      refine (add_lt_add_iff_left i).2 ?_
      have hd' : d < ω ^ f z := hdz.trans_le ((opow_le_opow_iff_right one_lt_omega0).2 hb4)
      have h1 : (1 : Ordinal.{0}) < ω ^ f z :=
        one_lt_omega0.trans_le (by
          have := (opow_le_opow_iff_right one_lt_omega0).2 (one_le_iff_ne_zero.2 hfz0)
          rwa [opow_one] at this)
      exact isPrincipal_add_omega0_opow _ hd' h1
  · -- `ϑᵖ(Ω₁·q + σ) ≤ r` for every `σ < r`
    push Not at hl
    have hsrc : le1 v (v * ((q + 1 : ℕ) : Ordinal.{0})) :=
      (h.lowδ _ _ hρv hvq.le).2 (by rw [← hve]; exact vz_th_le1R hρE hρ1 hq hrT hr1)
    have wz : WZ ρ δ (W1 ∪ vzMulF v q) Z1 := vzWZ_mul w1 hρv.le hvI hδI hvδ q
    refine ⟨W1 ∪ vzMulF v q, Z1, th q s1, ⟨wz, ⟨hq, cb1⟩, cs1, by rw [val_th, e1, hve],
      Finset.mem_union_left _ (Finset.mem_union_right _ hvm0), ?_⟩⟩
    intro A f hW hZ C
    obtain ⟨hyE, hy1, hB⟩ := h.vz_img_base C
    have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hmulA : ∀ j : ℕ, j ≤ q → v * ((j + 1 : ℕ) : Ordinal.{0}) ∈ A := fun j hj =>
      hW (Finset.mem_coe.2 (Finset.mem_union_right _ (hvm j hj)))
    have hvA : v ∈ A := hW (Finset.mem_coe.2 (Finset.mem_union_right _ hvm0))
    have hrA : r ∈ A := mem_A m1 hW1 hZ
    have hcb1y := cbt_img C cb1 (fun c hc => hZ (Finset.mem_coe.2 (cs1 c hc)))
    have hb1 := b1 A f hW1 hZ C
    have hfrv : f r < f v := C.mono hrA hvA hrv
    have hyv : f ρ < f v := C.mono C.rho hvA hρv
    rw [val_th]
    by_cases hU : UpsPt (f v)
    · exact (vzv_lt_ups hyE hy1 (t := th q s1) ⟨hq, hcb1y⟩ hyv hU).le
    have himg : le1 (f v) (f v * ((q + 1 : ℕ) : Ordinal.{0})) := by
      have := C.cov1 v hvA _ (hmulA q le_rfl) hsrc
      rwa [vz_copy_mul C hmulA q le_rfl] at this
    have hR := (C.sk _ (C.low _ hvA) hU _).1 himg
    have hP := vz_le1R_level q hq (f v) (lt_of_le_of_lt zero_le hyv) hR
    obtain ⟨hs1T, hs1_1⟩ := vzv_T hyE hy1 s1 hcb1y
    have hpi := vzv_pi C.ups h.ρU hB s1 hcb1y
    refine vz_th_min hyE hy1 hq hs1T hs1_1 hP hyv (hb1.trans_lt hfrv) (fun σ hσ => ?_)
    have htr := vz_fix_transfer (q := q) hB hpi.1 (by rw [e1]; exact hr1) (by rw [e1]; exact hl) σ
      (by rw [hpi.2]; exact hσ)
    rw [hpi.2] at htr
    exact htr.trans_lt (hb1.trans_lt hfrv)

/-- **The atom form of an `ε`-number** `v ≥ ρ`: `v = ω^{v+0}`, with its IMG term as the `ε`-base. -/
theorem vzImg_E {v : Ordinal.{0}} (hρv : ρ ≤ v) (hvE : InE v) (hvδ : v < δ) {W Z : Finset Ordinal.{0}}
    {s : VzTm} (hI : ImgVz ρ δ v W Z s) :
    ∃ W' Z' se s', ImgVz ρ δ v W' Z' (pw (sm se s')) ∧ InE (val se ρ) ∧ val se ρ + val s' ρ < eN (val se ρ) := by
  classical
  obtain ⟨w, cb, cs, e, m, b⟩ := hI
  have hρE := h.ρE
  have hv0 : 0 < v := hvE.pos
  have hvv : v + v < δ := (inE_indec h.δE).add_lt hvδ hvδ
  have hm' : v ∈ W ∪ insert 0 Z := by
    rcases Finset.mem_union.1 m with hx | hx
    · exact Finset.mem_union_left _ hx
    · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hx)
  have wz : WZ ρ δ (insert (v + v) W) (insert 0 Z) :=
    (w.insZ hρE.pos).insW (hρv.trans le_self_add) hvv
      (Or.inr ⟨v, hm', v, hm', lt_add_of_pos_right _ hv0, lt_add_of_pos_right _ hv0, rfl⟩)
  refine ⟨insert (v + v) W, insert 0 Z, s, cst 0, ⟨wz, ⟨cb, hρE.pos⟩, fun c hc => ?_, ?_, ?_, ?_⟩,
    by rw [e]; exact hvE, by rw [e, val_cst, add_zero]; exact lt_eN v⟩
  · simp only [cst', List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact Finset.mem_insert_of_mem (cs c hc)
    · exact Finset.mem_insert_self _ _
  · rw [val_pw, val_sm, val_cst, add_zero, e]; exact hvE
  · rcases Finset.mem_union.1 m with hx | hx
    · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hx)
    · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hx)
  intro A f hW hZ C
  have hW0 : ↑W ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hZ0 : ↑Z ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  have hvA : v ∈ A := mem_A m hW0 hZ0
  have hbv := b A f hW0 hZ0 C
  have hfE : InE (f v) := by
    rcases eq_or_lt_of_le hρv with rfl | hρv'
    · exact upsPt_inE C.ups
    have hvvA : v + v ∈ A := hW (by simp)
    have hsrc : le1 v (v + v) :=
      (h.lowδ _ _ hρv' hvv.le).2 (by rw [← mul_two_eq]; exact (le1R_two_iff hv0).2 hvE)
    have himg : le1 (f v) (f v + f v) := by
      have := C.cov1 v hvA _ hvvA hsrc
      rwa [← C.add v hvA v hvA _ hvvA rfl] at this
    by_cases hU : UpsPt (f v)
    · exact upsPt_inE hU
    · have hR := (C.sk _ (C.low _ hvA) hU _).1 himg
      have h0 : 0 < f v := lt_of_le_of_lt zero_le (C.mono C.rho hvA hρv')
      exact (le1R_two_iff h0).1 (by rw [mul_two_eq]; exact hR)
  rw [val_pw, val_sm, val_cst, add_zero]
  have := (opow_le_opow_iff_right one_lt_omega0).2 hbv
  rwa [show ω ^ f v = f v from hfE] at this

end RstK

namespace RstK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **Lemma IMG at an atom** `v = ω^L ≥ ρ` that is not an `ε`-number, from the IMG of the values below `v` (the
atom form for the indecomposable ones). -/
theorem vzImg_atom {L : Ordinal.{0}} (hρv : ρ ≤ ω ^ L) (hE : ¬ InE (ω ^ L)) (hvB : ω ^ L < VzB ρ)
    (I1 : ∀ u, u < ω ^ L → ∃ W Z s, ImgVz ρ δ u W Z s)
    (I2 : ∀ u, u < ω ^ L → ρ ≤ u → Indec u → ∃ W Z se s', ImgVz ρ δ u W Z (pw (sm se s')) ∧
      InE (val se ρ) ∧ val se ρ + val s' ρ < eN (val se ρ)) :
    ∃ W Z se s', ImgVz ρ δ (ω ^ L) W Z (pw (sm se s')) ∧ InE (val se ρ) ∧ val se ρ + val s' ρ < eN (val se ρ) := by
  classical
  have hρE := h.ρE
  have hδE := h.δE
  have hδI := inE_indec hδE
  have hρE' : ω ^ ρ = ρ := hρE
  have hvδ : ω ^ L < δ := hvB.trans h.vz_B_lt_δ
  have hρL : ρ ≤ L := (opow_le_opow_iff_right one_lt_omega0).1 (by rw [hρE']; exact hρv)
  have hLv : L < ω ^ L := lt_of_le_of_ne (right_le_opow _ one_lt_omega0)
    (fun h' => hE (by unfold InE; rw [← h']; exact h'.symm))
  obtain ⟨n, -, hn1, hn2⟩ := evA_bracket hρE hρL
    (show L < evA ρ (L + 1) from lt_of_lt_of_le (lt_add_one L) (le_evA_idx ρ _))
  set e := evA ρ n with hedef
  have heE : InE e := evA_E _ _
  have heE' : ω ^ e = e := heE
  have hρe : ρ ≤ e := le_evA hρE n
  have hnext : eN e = evA ρ (n + 1) := by rw [hedef, evA_add_one]
  have hev : e < ω ^ L := lt_of_le_of_lt hn1 hLv
  obtain ⟨We, Ze, se, we, cbe, cse, ee', me, ie⟩ := I1 e hev
  set β := L - e with hβdef
  have heβ : e + β = L := Ordinal.add_sub_cancel_of_le hn1
  have hβn : e + β < eN e := by rw [heβ, hnext]; exact hn2
  rw [← heβ] at hρv hE hvB hvδ I1 I2 hev ⊢
  have hβ0 : β ≠ 0 := by
    intro h0; rw [h0, add_zero] at hE; exact hE (by unfold InE; rw [heE', heE'])
  set v := ω ^ (e + β) with hvdef
  have hβv : e + β < v := exp_lt_atomE hβ0 hβn
  have hρv' : ρ < v := lt_of_le_of_lt (hρe.trans le_self_add) hβv
  have hv1 : v < Om1 := hvδ.trans h.δ1
  obtain ⟨β'', hgs, hdvd, hβ''β⟩ := lg_split hβ0
  have hzβ : lg β ≤ β := lg_le hβ0
  set v'' := ω ^ (e + β'') with hv''def
  have hv''v : v'' < v :=
    (opow_lt_opow_iff_right one_lt_omega0).2 ((add_lt_add_iff_left _).2 hβ''β)
  have hρv'' : ρ ≤ v'' := (hρe.trans le_self_add).trans (right_le_opow _ one_lt_omega0)
  have heβ''n : e + β'' < eN e := lt_of_le_of_lt (add_le_add (le_refl e) hβ''β.le) hβn
  obtain ⟨W1, Z1, t1, s'', ⟨w1, c1, cs1, e1, m1, b1⟩, hE1, hlt1⟩ := I2 v'' hv''v hρv'' (indec_opow _)
  have e1' : val t1 ρ + val s'' ρ = e + β'' := by
    have := e1; rw [val_pw, val_sm] at this; exact opow_inj this
  have hnn : val t1 ρ = e := vz_ebase_unique hE1 heE (by rw [← e1']; exact le_self_add)
    (by rw [← e1']; exact hlt1) le_self_add heβ''n
  rw [hnn] at e1'
  have hs'' : val s'' ρ = β'' := (add_left_cancel_iff).1 e1'
  obtain ⟨ct1, c1⟩ := c1
  have cst1 : ∀ c ∈ cst' t1, c ∈ Z1 := fun c hc => cs1 c (by simp [cst', hc])
  have cs1' : ∀ c ∈ cst' s'', c ∈ Z1 := fun c hc => cs1 c (by simp [cst', hc])
  have he1 : e < Om1 := hev.trans hv1
  -- the bases of `t1` and `se` agree at every copied base, and are `ε`-numbers there
  have hagree : ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑Z1 ⊆ A → ↑Ze ⊆ A → ImgCtx ρ A f →
      val t1 (f ρ) = val se (f ρ) ∧ InE (val t1 (f ρ)) := by
    intro A f hZ1 hZe C
    have hct1 := cbt_img C ct1 (fun c hc => hZ1 (Finset.mem_coe.2 (cst1 c hc)))
    have hcse := cbt_img C cbe (fun c hc => hZe (Finset.mem_coe.2 (cse c hc)))
    have hB := h.img_bases C
    refine ⟨(uniVz_eq C.ups h.ρU hB hct1 hcse).1 (by rw [hnn, ee']), ?_⟩
    have hpi := vzv_pi C.ups h.ρU hB t1 hct1
    rw [← hpi.2]
    exact vz_pi_E C.ups h.ρU hB hpi.1 (by rw [hnn]; exact he1) (by rw [hnn]; exact heE)
  rcases eq_or_ne (lg β) 0 with hz0 | hz0
  · -- `β = β'' + 1`
    have hβs : β = β'' + 1 := by rw [hgs, hz0, opow_zero]
    have h1ρ : (1 : Ordinal.{0}) < ρ := one_lt_of_upsPt h.ρU
    refine ⟨insert v W1, insert 1 Z1, t1, sm s'' (cst 1),
      ⟨(w1.insZ h1ρ).insW hρv'.le hvδ (Or.inl (indec_opow _)), ⟨ct1, c1, h1ρ⟩, ?_, ?_,
      Finset.mem_union_left _ (Finset.mem_insert_self _ _), ?_⟩, by rw [hnn]; exact heE,
      by rw [hnn, val_sm, val_cst, hs'', ← hβs]; exact hβn⟩
    · intro c hc
      simp only [cst', List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | hc | rfl
      · exact Finset.mem_insert_of_mem (cst1 c hc)
      · exact Finset.mem_insert_of_mem (cs1' c hc)
      · exact Finset.mem_insert_self _ _
    · rw [val_pw, val_sm, val_sm, val_cst, hs'', hnn, ← hβs]
    intro A f hW hZ C
    have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have hvA : v ∈ A := hW (by simp)
    have h1A : v'' ∈ A := mem_A m1 hW1 hZ1
    have hb := b1 A f hW1 hZ1 C
    rw [val_pw, val_sm] at hb
    have hlt : f v'' < f v := C.mono h1A hvA hv''v
    obtain ⟨c, hc⟩ := indec_eq_opow (C.indec _ hvA (indec_opow _))
    rw [hc] at hlt
    rw [val_pw, val_sm, val_sm, val_cst, hc, ← add_assoc]
    have h3 : val t1 (f ρ) + val s'' (f ρ) < c :=
      (opow_lt_opow_iff_right one_lt_omega0).1 (lt_of_le_of_lt hb hlt)
    exact (opow_le_opow_iff_right one_lt_omega0).2 (add_one_le_of_lt h3)
  -- `β = β'' + ω^z`, `z > 0`
  set z := lg β with hzdef
  have hz0' : 0 < z := pos_iff_ne_zero.2 hz0
  have hzv : z < v := lt_of_le_of_lt (hzβ.trans le_add_self) hβv
  have hzδ : z < δ := hzv.trans hvδ
  have hdβ : ω ^ z ∣ β := by rw [hgs]; exact dvd_add hdvd (dvd_refl _)
  obtain ⟨W3, Z3, sz, w3, c3, cs3, e3, m3, b3⟩ := I1 z hzv
  have hsrc : le1 v (v + z) :=
    h.src_gen hz0 (lt_of_lt_of_le heE.pos le_self_add).ne' (dvdE heE hβ0 hdβ) hzv.le hρv'
      (hδI.add_lt hvδ hzδ).le
  have hvzδ : v + z < δ := hδI.add_lt hvδ hzδ
  have hzvz : z < v + z := lt_of_lt_of_le hzv le_self_add
  have hvvz : v < v + z := lt_add_of_pos_right v hz0'
  have hev' : e < v := lt_of_lt_of_le (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hβ0)) hβv.le
  have heδ : e < δ := hev'.trans hvδ
  -- a copy that is a `υ`-point is above every term value at the copied base
  have hups : ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ImgCtx ρ A f → v ∈ A →
      UpsPt (f v) → ∀ s' : VzTm, CBt s' (f ρ) → val s' (f ρ) ≤ f v := by
    intro A f C hvA hU s' hs'
    obtain ⟨hyE, hy1, -⟩ := h.vz_img_base C
    exact (vzv_lt_ups hyE hy1 hs' (C.mono C.rho hvA hρv') hU).le
  rcases eq_or_ne β'' 0 with hb0 | hb0
  · -- `β = ω^z`
    have hβz : β = ω ^ z := by rw [hgs, hb0, zero_add]
    set W0 := W1 ∪ W3 ∪ We with hW0
    set Z0 := insert 0 (Z1 ∪ Z3 ∪ Ze) with hZ0
    have wz0 : WZ ρ δ W0 Z0 := ((w1.union w3).union we).insZ hρE.pos
    have hzm0 : z ∈ W0 ∪ Z0 := by
      rcases Finset.mem_union.1 m3 with hx | hx
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hx))
      · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem
          (Finset.mem_union_left _ (Finset.mem_union_right _ hx)))
    have hem0 : e ∈ W0 ∪ Z0 := by
      rcases Finset.mem_union.1 me with hx | hx
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
      · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ hx))
    set Wx := if z ≤ e then insert (e + z) W0 else W0 with hWx
    have hW0x : W0 ⊆ Wx := by
      rw [hWx]; split_ifs
      · exact Finset.subset_insert _ _
      · exact subset_refl _
    have wzx : WZ ρ δ Wx Z0 := by
      rw [hWx]; split_ifs with hze
      · exact wz0.insW (hρe.trans le_self_add) (hδI.add_lt heδ hzδ)
          (Or.inr ⟨e, hem0, z, hzm0, lt_add_of_pos_right _ hz0',
            lt_of_le_of_lt hze (lt_add_of_pos_right _ hz0'), rfl⟩)
      · exact wz0
    have hmx : ∀ x ∈ W0 ∪ Z0, x ∈ insert v Wx ∪ Z0 := by
      intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (hW0x hx))
      · exact Finset.mem_union_right _ hx
    have wzf : WZ ρ δ (insert (v + z) (insert v Wx)) Z0 :=
      (wzx.insW hρv'.le hvδ (Or.inl (indec_opow _))).insW (hρv'.le.trans le_self_add) hvzδ
        (Or.inr ⟨v, Finset.mem_union_left _ (Finset.mem_insert_self _ _), z, hmx z hzm0, hvvz,
          hzvz, rfl⟩)
    refine ⟨insert (v + z) (insert v Wx), Z0, t1, pw sz, ⟨wzf, ⟨ct1, c3⟩, ?_, ?_,
      Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)), ?_⟩,
      by rw [hnn]; exact heE, by rw [hnn, val_pw, e3, ← hβz]; exact hβn⟩
    · intro c hc
      simp only [cst', List.mem_append] at hc
      rcases hc with hc | hc
      · exact Finset.mem_insert_of_mem (by simp [cst1 c hc])
      · exact Finset.mem_insert_of_mem (by simp [cs3 c hc])
    · rw [val_pw, val_sm, val_pw, e3, hnn, ← hβz]
    intro A f hW hZ C
    have hW0A : ↑W0 ⊆ A := fun x hx => hW (Finset.mem_coe.2 (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (hW0x (Finset.mem_coe.1 hx)))))
    have hsW : ∀ {S : Finset Ordinal.{0}}, S ⊆ W0 → ↑S ⊆ A := fun hS x hx =>
      hW0A (Finset.mem_coe.2 (hS (Finset.mem_coe.1 hx)))
    have hsZ : ∀ {S : Finset Ordinal.{0}}, S ⊆ Z0 → ↑S ⊆ A := fun hS x hx =>
      hZ (Finset.mem_coe.2 (hS (Finset.mem_coe.1 hx)))
    have hZ1 : ↑Z1 ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
    have hW3 : ↑W3 ⊆ A := hsW (by intro x hx; simp [hW0, hx])
    have hZ3 : ↑Z3 ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
    have hWe : ↑We ⊆ A := hsW (by intro x hx; simp [hW0, hx])
    have hZe : ↑Ze ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
    have h0A : (0 : Ordinal.{0}) ∈ A := hsZ (S := {0}) (by simp [hZ0]) (by simp)
    have hvA : v ∈ A := hW (by simp)
    have hvzA : v + z ∈ A := hW (by simp)
    have hzA : z ∈ A := mem_A hzm0 hW0A hZ
    have heA : e ∈ A := mem_A hem0 hW0A hZ
    have hbz : val sz (f ρ) ≤ f z := b3 A f hW3 hZ3 C
    have hct1 : CBt t1 (f ρ) := cbt_img C ct1 (fun c hc => hZ1 (Finset.mem_coe.2 (cst1 c hc)))
    obtain ⟨hag, hE1y⟩ := hagree A f hZ1 hZe C
    have hfe : val t1 (f ρ) ≤ f e := by rw [hag]; exact ie A f hWe hZe C
    have hfev : f e < f v := C.mono heA hvA hev'
    have hCB : CBt sz (f ρ) := cbt_img C c3 (fun c hc => hZ3 (Finset.mem_coe.2 (cs3 c hc)))
    by_cases hU : UpsPt (f v)
    · exact hups A f C hvA hU (pw (sm t1 (pw sz))) ⟨hct1, hCB⟩
    obtain ⟨a, ha, hda⟩ := h.copy_atom C hvA hzA hvzA hz0 hzv.le h0A hsrc
    rw [val_pw, val_sm, val_pw, ha]
    refine (opow_le_opow_iff_right one_lt_omega0).2 ?_
    have htw : ω ^ val sz (f ρ) ≤ ω ^ f z := (opow_le_opow_iff_right one_lt_omega0).2 hbz
    have hE1y' : ω ^ val t1 (f ρ) = val t1 (f ρ) := hE1y
    by_cases hze : z ≤ e
    · have hezA : e + z ∈ A := by
        have : e + z ∈ Wx := by rw [hWx, if_pos hze]; exact Finset.mem_insert_self _ _
        exact hW (by simp [this])
      obtain ⟨c, hc, hdc⟩ : ∃ c, f e = ω ^ c ∧ ω ^ f z ∣ c := by
        rcases eq_or_lt_of_le hρe with he0 | hρe'
        · have hfE : ω ^ f ρ = f ρ := upsPt_inE C.ups
          refine ⟨f ρ, by rw [← he0, hfE], ?_⟩
          have hzρ : z ≤ ρ := he0 ▸ hze
          exact opow_dvd_of_inE (upsPt_inE C.ups) ((C.mono.le_iff_le hzA C.rho).2 hzρ)
        · have hsrce : le1 e (e + z) := by
            have := h.src_gen (a' := e) hz0 heE.pos.ne' (opow_dvd_of_inE heE hze)
              (by rw [heE']; exact hze) (by rw [heE']; exact hρe')
              (by rw [heE']; exact (hδI.add_lt heδ hzδ).le)
            rwa [heE'] at this
          exact h.copy_atom C heA hzA hezA hz0 hze h0A hsrce
      have hcl : val t1 (f ρ) ≤ c := by
        rw [hc, ← hE1y'] at hfe; exact (opow_le_opow_iff_right one_lt_omega0).1 hfe
      have hca : c < a := by
        have := hfev; rw [hc, ha] at this; exact (opow_lt_opow_iff_right one_lt_omega0).1 this
      exact (add_le_add hcl htw).trans (dvd_next hda hdc hca)
    · push Not at hze
      have hfz : f e < f z := C.mono heA hzA hze
      have h1 : val t1 (f ρ) < ω ^ f z :=
        lt_of_le_of_lt hfe (hfz.trans_le (right_le_opow _ one_lt_omega0))
      have ha0 : a ≠ 0 := by
        intro h0
        rw [h0, opow_zero] at ha
        have : (1 : Ordinal.{0}) < f v :=
          lt_of_le_of_lt (one_le_iff_pos.2 hE1y.pos) (lt_of_le_of_lt hfe hfev)
        rw [ha] at this; exact lt_irrefl _ this
      have h2 : val t1 (f ρ) + ω ^ val sz (f ρ) ≤ ω ^ f z := by
        rcases htw.lt_or_eq with hlt | heq
        · exact (isPrincipal_add_omega0_opow _ h1 hlt).le
        · rw [heq, add_omega0_opow h1]
      exact h2.trans (le_of_dvd ha0 hda)
  · -- `β'' ≠ 0`: the source atom of `v''` too
    have hzb : z ≤ β'' := (right_le_opow z one_lt_omega0).trans (le_of_dvd hb0 hdvd)
    have hzvb : z < v'' := lt_of_le_of_lt (hzb.trans le_add_self) (exp_lt_atomE hb0 heβ''n)
    have hv''zδ : v'' + z < δ := hδI.add_lt (hv''v.trans hvδ) hzδ
    have hρv3 : ρ < v'' := lt_of_le_of_lt (hρe.trans le_self_add) (exp_lt_atomE hb0 heβ''n)
    have hsrc'' : le1 v'' (v'' + z) :=
      h.src_gen hz0 (lt_of_lt_of_le heE.pos le_self_add).ne' (dvdE heE hb0 hdvd) hzvb.le hρv3 hv''zδ.le
    set W0 := W1 ∪ W3 ∪ We with hW0
    set Z0 := insert 0 (Z1 ∪ Z3 ∪ Ze) with hZ0
    have wz0 : WZ ρ δ W0 Z0 := ((w1.union w3).union we).insZ hρE.pos
    have hv''m : v'' ∈ W0 ∪ Z0 := by
      rcases Finset.mem_union.1 m1 with hx | hx
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hx))
      · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem
          (Finset.mem_union_left _ (Finset.mem_union_left _ hx)))
    have hzm0 : z ∈ W0 ∪ Z0 := by
      rcases Finset.mem_union.1 m3 with hx | hx
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hx))
      · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem
          (Finset.mem_union_left _ (Finset.mem_union_right _ hx)))
    have wz1 : WZ ρ δ (insert (v'' + z) W0) Z0 :=
      wz0.insW (hρv''.trans le_self_add) hv''zδ
        (Or.inr ⟨v'', hv''m, z, hzm0, lt_add_of_pos_right _ hz0', lt_of_lt_of_le hzvb le_self_add, rfl⟩)
    have hmx : ∀ x ∈ W0 ∪ Z0, x ∈ insert v (insert (v'' + z) W0) ∪ Z0 := by
      intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
      · exact Finset.mem_union_right _ hx
    have wzf : WZ ρ δ (insert (v + z) (insert v (insert (v'' + z) W0))) Z0 :=
      (wz1.insW hρv'.le hvδ (Or.inl (indec_opow _))).insW (hρv'.le.trans le_self_add) hvzδ
        (Or.inr ⟨v, Finset.mem_union_left _ (Finset.mem_insert_self _ _), z, hmx z hzm0, hvvz, hzvz, rfl⟩)
    refine ⟨insert (v + z) (insert v (insert (v'' + z) W0)), Z0, t1, sm s'' (pw sz),
      ⟨wzf, ⟨ct1, c1, c3⟩, ?_, ?_, Finset.mem_union_left _ (Finset.mem_insert_of_mem
        (Finset.mem_insert_self _ _)), ?_⟩, by rw [hnn]; exact heE,
      by rw [hnn, val_sm, val_pw, hs'', e3, ← hgs]; exact hβn⟩
    · intro c hc
      simp only [cst', List.mem_append] at hc
      rcases hc with hc | hc | hc
      · exact Finset.mem_insert_of_mem (by simp [cst1 c hc])
      · exact Finset.mem_insert_of_mem (by simp [cs1' c hc])
      · exact Finset.mem_insert_of_mem (by simp [cs3 c hc])
    · rw [val_pw, val_sm, val_sm, val_pw, hs'', e3, hnn, ← hgs]
    intro A f hW hZ C
    have hW0A : ↑W0 ⊆ A := fun x hx => hW (Finset.mem_coe.2 (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx)))))
    have hsW : ∀ {S : Finset Ordinal.{0}}, S ⊆ W0 → ↑S ⊆ A := fun hS x hx =>
      hW0A (Finset.mem_coe.2 (hS (Finset.mem_coe.1 hx)))
    have hsZ : ∀ {S : Finset Ordinal.{0}}, S ⊆ Z0 → ↑S ⊆ A := fun hS x hx =>
      hZ (Finset.mem_coe.2 (hS (Finset.mem_coe.1 hx)))
    have hW1 : ↑W1 ⊆ A := hsW (by intro x hx; simp [hW0, hx])
    have hW3 : ↑W3 ⊆ A := hsW (by intro x hx; simp [hW0, hx])
    have hZ1 : ↑Z1 ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
    have hZ3 : ↑Z3 ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
    have h0A : (0 : Ordinal.{0}) ∈ A := hsZ (S := {0}) (by simp [hZ0]) (by simp)
    have hvA : v ∈ A := hW (by simp)
    have hvzA : v + z ∈ A := hW (by simp)
    have hv''zA : v'' + z ∈ A := hW (by simp)
    have hzA : z ∈ A := mem_A hzm0 hW0A hZ
    have hv''A : v'' ∈ A := mem_A hv''m hW0A hZ
    have hb'' := b1 A f hW1 hZ1 C
    rw [val_pw, val_sm] at hb''
    have hbz : val sz (f ρ) ≤ f z := b3 A f hW3 hZ3 C
    have htw : ω ^ val sz (f ρ) ≤ ω ^ f z := (opow_le_opow_iff_right one_lt_omega0).2 hbz
    have hct1 : CBt t1 (f ρ) := cbt_img C ct1 (fun c hc => hZ1 (Finset.mem_coe.2 (cst1 c hc)))
    have hcs1 : CBt s'' (f ρ) := cbt_img C c1 (fun c hc => hZ1 (Finset.mem_coe.2 (cs1' c hc)))
    have hcs3 : CBt sz (f ρ) := cbt_img C c3 (fun c hc => hZ3 (Finset.mem_coe.2 (cs3 c hc)))
    by_cases hU : UpsPt (f v)
    · exact hups A f C hvA hU (pw (sm t1 (sm s'' (pw sz)))) ⟨hct1, hcs1, hcs3⟩
    obtain ⟨c, hc, hdc⟩ := h.copy_atom C hv''A hzA hv''zA hz0 hzvb.le h0A hsrc''
    have hbc : val t1 (f ρ) + val s'' (f ρ) ≤ c := by
      rw [hc] at hb''; exact (opow_le_opow_iff_right one_lt_omega0).1 hb''
    have hfv''v : f v'' < f v := C.mono hv''A hvA hv''v
    obtain ⟨a, ha, hda⟩ := h.copy_atom C hvA hzA hvzA hz0 hzv.le h0A hsrc
    have hca : c < a := by
      have := hfv''v; rw [hc, ha] at this; exact (opow_lt_opow_iff_right one_lt_omega0).1 this
    rw [val_pw, ha]
    refine (opow_le_opow_iff_right one_lt_omega0).2 ?_
    rw [val_sm, val_sm, val_pw, ← add_assoc]
    exact (add_le_add hbc htw).trans (dvd_next hda hdc hca)

/-- **Lemma IMG below `VzB ρ`**: every `v < VzB ρ` has a term of `VzTm` and witness sets such that every covering
copy `f` of a set containing them has `s(f(ρ)) ≤ f(v)`; for an indecomposable `v ≥ ρ` also in the atom form
`ω^{se + s'}` with the `ε`-base `se(ρ)` (`se(ρ) ≤ se(ρ) + s'(ρ) < eN(se(ρ))`). -/
theorem imgVz : ∀ v, v < VzB ρ →
    (∃ W Z s, ImgVz ρ δ v W Z s) ∧
    (ρ ≤ v → Indec v → ∃ W Z se s', ImgVz ρ δ v W Z (pw (sm se s')) ∧ InE (val se ρ) ∧
      val se ρ + val s' ρ < eN (val se ρ)) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have h0T := mem_T_of_le hρE hρ1 (zero_le : (0 : Ordinal.{0}) ≤ ρ)
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  have hvδ : v < δ := hv.trans h.vz_B_lt_δ
  have I1 : ∀ u, u < v → ∃ W Z s, ImgVz ρ δ u W Z s := fun u hu => (IH u hu (hu.trans hv)).1
  have I2 : ∀ u, u < v → ρ ≤ u → Indec u → ∃ W Z se s', ImgVz ρ δ u W Z (pw (sm se s')) ∧
      InE (val se ρ) ∧ val se ρ + val s' ρ < eN (val se ρ) := fun u hu => (IH u hu (hu.trans hv)).2
  -- the `ε`-numbers `≥ ρ`
  have PE : ρ ≤ v → InE v → ∃ W Z s, ImgVz ρ δ v W Z s := by
    intro hρv hE
    rcases eq_or_lt_of_le hρv with heq | hρv'
    · refine ⟨{ρ}, ∅, bs, ⟨?_, trivial, by simp [cst'], heq, by simp [heq], fun A f _ _ C => ?_⟩⟩
      · have := (WZ.empty (ρ := ρ) (δ := δ)).insW le_rfl (heq ▸ hvδ) (Or.inl (inE_indec hρE))
        simpa using this
      · rw [val_bs, ← heq]
    obtain ⟨N, hN⟩ := vzB_lt_iff.1 hv
    rcases Nat.eq_zero_or_pos N with rfl | hN1
    · exfalso
      have h00 : Om1 * ((0 : ℕ) : Ordinal.{0}) + 0 = 0 := by rw [Nat.cast_zero, mul_zero, add_zero]
      rw [h00] at hN
      obtain ⟨h0vT, -, h0v1, -, -⟩ := vt_memTwo hρE hρ1 h0T (lt_of_le_of_lt zero_le Om1_lt_OmTwo)
      have hv1 : v < Om1 := hN.trans h0v1
      have hvT : v ∈ Tset ρ := vz_T_down hρE hρ1 h0vT h0v1 hN.le
      obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hρE hρ1 hvT hρv hv1 (inE_indec hE)
      have := vzLt_of_vt_lt (n := 0) hρE hρ1 hξT hξ2 h0T (Ordinal.omega_pos 1) (by rw [hξv]; exact hE.pos)
        (by rw [h00, hξv]; exact hN)
      rw [h00] at this
      exact absurd this (not_lt.2 zero_le)
    obtain ⟨-, -, hNT, -, hN1', -, -, -⟩ := vz_th_facts hρE hρ1 hN1 h0T (Ordinal.omega_pos 1)
    have hv1 : v < Om1 := hN.trans hN1'
    have hvT : v ∈ Tset ρ := vz_T_down hρE hρ1 hNT hN1' hN.le
    obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hρE hρ1 hvT hρv hv1 (inE_indec hE)
    have hΩξ : Om1 ≤ ξ := (vt_E_iff hρE hρ1 hξT hξ2).1 ⟨by rw [hξv]; exact hρv', by rw [hξv]; exact hE⟩
    have hξN : ξ < Om1 * (N : Ordinal.{0}) + 0 :=
      vzLt_of_vt_lt hρE hρ1 hξT hξ2 h0T (Ordinal.omega_pos 1) (by rw [hξv]; exact hE.pos)
        (by rw [hξv]; exact hN)
    obtain ⟨hdec, hr1⟩ := vz_div_Om1 ξ
    set q := ξ / Om1 with hq
    set r := ξ % Om1 with hr
    have hqN : q < (N : Ordinal.{0}) := by
      have h1 : Om1 * q < Om1 * (N : Ordinal.{0}) := by
        calc Om1 * q ≤ ξ := hdec ▸ le_self_add
          _ < Om1 * (N : Ordinal.{0}) := by rw [add_zero] at hξN; exact hξN
      exact (mul_lt_mul_iff_right₀ (Ordinal.omega_pos 1)).1 h1
    obtain ⟨q', hq'⟩ := lt_omega0.1 (hqN.trans (natCast_lt_omega0 _))
    have hq'1 : 1 ≤ q' := by
      rcases Nat.eq_zero_or_pos q' with h0 | h0
      · exfalso
        rw [h0, Nat.cast_zero] at hq'
        rw [hq', mul_zero, zero_add] at hdec
        exact absurd (hdec ▸ hr1) (not_lt.2 hΩξ)
      · exact h0
    have hrT : r ∈ Tset ρ := vzRem_T hρE hρ1 hξT hξ2 hdec.symm (dvd_mul_right _ _) hr1
    have e : Om1 * (q' : Ordinal.{0}) + r = ξ := by rw [← hq']; exact hdec
    exact h.vzImg_th hq'1 hrT hr1 (by rw [e, hξv]) hv I1
  refine ⟨?_, fun hρv hI => ?_⟩
  · rcases lt_or_ge v ρ with hvρ | hρv
    · -- a constant
      refine ⟨∅, {v}, cst v, ⟨WZ.empty.insZ hvρ, hvρ, by simp [cst'], rfl, by simp, ?_⟩⟩
      intro A f _ hZ C
      have hvA : v ∈ A := hZ (by simp)
      rw [val_cst, C.fix v hvA hvρ]
    by_cases hI : Indec v
    · by_cases hE : InE v
      · exact PE hρv hE
      · obtain ⟨L, rfl⟩ := indec_eq_opow hI
        obtain ⟨W, Z, se, s', hY, -, -⟩ := h.vzImg_atom hρv hE hv I1 I2
        exact ⟨W, Z, _, hY⟩
    · -- a decomposable value: a sum
      have hD : DecompR0 v := not_not.1 hI
      rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
      · exact absurd h0 (lt_of_lt_of_le hρE.pos hρv).ne'
      obtain ⟨W1, Z1, s1, w1, c1, cs1, e1, m1, b1⟩ := I1 u1 hu1
      obtain ⟨W2, Z2, s2, w2, c2, cs2, e2, m2, b2⟩ := I1 u2 hu2
      subst hsum
      have hm : ∀ x, x ∈ W1 ∪ Z1 ∨ x ∈ W2 ∪ Z2 → x ∈ W1 ∪ W2 ∪ (Z1 ∪ Z2) := by
        intro x hx
        rcases hx with hx | hx <;> rcases Finset.mem_union.1 hx with hx | hx <;> simp [hx]
      refine ⟨insert (u1 + u2) (W1 ∪ W2), Z1 ∪ Z2, sm s1 s2,
        ⟨(w1.union w2).insW hρv hvδ (Or.inr ⟨u1, hm u1 (Or.inl m1), u2, hm u2 (Or.inr m2), hu1, hu2,
          rfl⟩), ⟨c1, c2⟩, ?_, by simp [e1, e2], by simp, ?_⟩⟩
      · intro c hc
        simp only [cst', List.mem_append] at hc
        rcases hc with hc | hc
        · exact Finset.mem_union_left _ (cs1 c hc)
        · exact Finset.mem_union_right _ (cs2 c hc)
      · intro A f hW hZ C
        have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
        have hW2 : ↑W2 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
        have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
        have hZ2 : ↑Z2 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
        have hvA : u1 + u2 ∈ A := hW (by simp)
        have := C.add u1 (mem_A m1 hW1 hZ1) u2 (mem_A m2 hW2 hZ2) _ hvA rfl
        rw [val_sm, ← this]
        exact add_le_add (b1 A f hW1 hZ1 C) (b2 A f hW2 hZ2 C)
  · by_cases hE : InE v
    · obtain ⟨W, Z, s, hY⟩ := PE hρv hE
      exact h.vzImg_E hρv hE hvδ hY
    · obtain ⟨L, rfl⟩ := indec_eq_opow hI
      exact h.vzImg_atom hρv hE hv I1 I2

/-- **The IMG package of a term of `VzTm`** (constants below `ρ`, value `≥ 1`). -/
theorem pkgVz {s : VzTm} (hs : CBt s ρ) (h1 : 1 ≤ val s ρ) : ImgPkg ρ δ (val s) := by
  classical
  have hvB := vzv_lt_B h.ρE h.ρ1 hs
  obtain ⟨⟨W, Z, s0, w, c0, cs0, e0, m0, b0⟩, -⟩ := h.imgVz (val s ρ) hvB
  have wzc : WZ ρ δ ∅ (cst' s).toFinset :=
    ⟨by simp, fun z hz => cbt_cst s ρ hs z (List.mem_toFinset.1 hz), by simp⟩
  have hw' := w.union wzc
  rw [Finset.union_empty] at hw'
  refine ⟨h1, hvB.trans h.vz_B_lt_δ, W, Z ∪ (cst' s).toFinset, hw', ?_, ?_⟩
  · rcases Finset.mem_union.1 m0 with hm | hm
    · exact Finset.mem_union_left _ hm
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hm)
  · intro A f hW hZ C
    have hZ0 : ↑Z ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have hcs : ∀ c ∈ cst' s, c ∈ A := fun c hc => hZ (by simp [hc])
    have hcs0 : ∀ c ∈ cst' s0, c ∈ A := fun c hc => hZ0 (Finset.mem_coe.2 (cs0 c hc))
    have hB := h.img_bases C
    have heq := (uniVz_eq C.ups h.ρU hB (cbt_img C hs hcs) (cbt_img C c0 hcs0)).1 e0.symm
    rw [heq]
    exact b0 A f hW hZ0 C

end RstK

end Googology.Trans.PoR.InaccPsi.R2
