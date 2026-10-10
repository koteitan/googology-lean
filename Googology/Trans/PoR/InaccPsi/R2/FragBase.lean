import Googology.Trans.PoR.InaccPsi.R2.Frag

/-!
# Tools for Lemma FRAG with several bases

* `Cl`: monotone, idempotent, bounded by `ε`-numbers and by `Ω₁`; finite generators (`ClS.gen`).
* `comps`: components are `≤` the ordinal; a component is its own only component.
* `InSeg b x` (`x ∈ seg(b) ∩ Ω₁`) and its link with `Tᵇ` ([W07b] Cor 5.10).
* `DD κ b k`: the domain `D_k` of the paper proof, with `Cl`: `D₀ = κ`,
  `D_{k+1} = D_k ∪ {x ∈ seg(b_k) ∩ Ω₁ ∩ T^{b_k} | Par^{b_k}(x) ⊆ Cl(D_k)}`
  (the paper proof has `Par ⊆ D_k`; the `Cl` form is larger, so the theorem is stronger).
* `down_*`, `up_*`: one base change `π_{σ,τ}` and its inverse on a set: order, `+`, `≤₁`
  (Lemma ST) and `ε`-numbers (from Lemma ST and [W07b] remark after Thm 2.2).
* `assemble`: the `≤₁`-cases D1–D5 of the paper proof for any map that keeps the segments.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-! ## `Cl` -/

theorem ClS.sub (X : Set Ordinal.{0}) : X ⊆ ClS X := fun _ hx => Cl.base hx

theorem ClS.sub_of {X Y : Set Ordinal.{0}} (h : X ⊆ ClS Y) : ClS X ⊆ ClS Y := by
  intro x hx
  induction hx with
  | base hx => exact h hx
  | add _ _ ih1 ih2 => exact Cl.add ih1 ih2
  | opow _ ih => exact Cl.opow ih

theorem ClS.mono {X Y : Set Ordinal.{0}} (h : X ⊆ Y) : ClS X ⊆ ClS Y :=
  ClS.sub_of (h.trans (ClS.sub Y))

/-- `Cl(X) ⊆ e` when `X ⊆ e` and `e` is closed under `+` and `ξ ↦ ω^ξ`. -/
theorem ClS.lt_of {e : Ordinal.{0}} (hadd : ∀ x y, x < e → y < e → x + y < e)
    (hexp : ∀ x, x < e → ω ^ x < e) {X : Set Ordinal.{0}} (h : X ⊆ Set.Iio e) :
    ClS X ⊆ Set.Iio e := by
  intro x hx
  induction hx with
  | base hx => exact h hx
  | add _ _ ih1 ih2 => exact hadd _ _ ih1 ih2
  | opow _ ih => exact hexp _ ih

theorem InE.add_lt {e : Ordinal.{0}} (he : InE e) {x y : Ordinal.{0}} (hx : x < e) (hy : y < e) :
    x + y < e := by
  have hp := isPrincipal_add_omega0_opow e
  rw [he] at hp
  exact hp hx hy

theorem InE.opow_lt {e : Ordinal.{0}} (he : InE e) {x : Ordinal.{0}} (hx : x < e) : ω ^ x < e := by
  calc ω ^ x < ω ^ e := (opow_lt_opow_iff_right one_lt_omega0).2 hx
    _ = e := he

theorem ClS.lt_of_E {e : Ordinal.{0}} (he : InE e) {X : Set Ordinal.{0}} (h : X ⊆ Set.Iio e) :
    ClS X ⊆ Set.Iio e :=
  ClS.lt_of (fun _ _ hx hy => he.add_lt hx hy) (fun _ hx => he.opow_lt hx) h

theorem Om1_add_lt {x y : Ordinal.{0}} (hx : x < Om1) (hy : y < Om1) : x + y < Om1 :=
  isPrincipal_add_omega 1 hx hy

theorem Om1_opow_lt {x : Ordinal.{0}} (hx : x < Om1) : ω ^ x < Om1 :=
  isPrincipal_opow_omega 1 omega0_lt_omega_one hx

theorem ClS.lt_Om1 {X : Set Ordinal.{0}} (h : X ⊆ Set.Iio Om1) : ClS X ⊆ Set.Iio Om1 :=
  ClS.lt_of (fun _ _ hx hy => Om1_add_lt hx hy) (fun _ hx => Om1_opow_lt hx) h

/-- Every element of `Cl(Y)` lies in `Cl(G)` for a finite `G ⊆ Y` of ordinals below it. -/
theorem ClS.gen {Y : Set Ordinal.{0}} {x : Ordinal.{0}} (hx : x ∈ ClS Y) :
    ∃ G : Finset Ordinal.{0}, ↑G ⊆ Y ∧ (∀ g ∈ G, g ≤ x) ∧ x ∈ ClS ↑G := by
  classical
  induction hx with
  | @base x hx => exact ⟨{x}, by simpa using hx, by simp, Cl.base (by simp)⟩
  | @add x y _ _ ih1 ih2 =>
    obtain ⟨G1, h1, b1, c1⟩ := ih1
    obtain ⟨G2, h2, b2, c2⟩ := ih2
    refine ⟨G1 ∪ G2, by rw [Finset.coe_union]; exact Set.union_subset h1 h2, ?_,
      Cl.add (ClS.mono (by simp) c1) (ClS.mono (by simp) c2)⟩
    intro g hg
    rcases Finset.mem_union.1 hg with hg | hg
    · exact (b1 g hg).trans le_self_add
    · exact (b2 g hg).trans le_add_self
  | @opow x _ ih =>
    obtain ⟨G, h, b, c⟩ := ih
    exact ⟨G, h, fun g hg => (b g hg).trans (right_le_opow _ one_lt_omega0), Cl.opow c⟩

/-! ## Components -/

theorem le_of_mem_comps {x p : Ordinal.{0}} (hp : p ∈ comps x) : p ≤ x := by
  unfold comps at hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  have hx : x ≠ 0 := by rintro rfl; simp at hq
  calc ω ^ q.1 ≤ ω ^ log ω x := opow_le_opow_right omega0_pos (CNF.fst_le_log hq)
    _ ≤ x := opow_log_le_self ω hx

theorem comps_opow (e : Ordinal.{0}) : comps (ω ^ e) = [ω ^ e] := by
  unfold comps
  have h := CNF.opow_mul_add (b := ω) (e := e) (x := 1) (y := 0) one_lt_omega0 one_ne_zero
    one_lt_omega0 (opow_pos e omega0_pos)
  simp only [mul_one, add_zero, CNF.zero_right] at h
  rw [h]; simp

theorem comps_of_mem_comps {x p : Ordinal.{0}} (hp : p ∈ comps x) : comps p = [p] := by
  unfold comps at hp
  obtain ⟨q, _, rfl⟩ := List.mem_map.1 hp
  exact comps_opow _

theorem DC_Iio (κ : Ordinal.{0}) : DC (Set.Iio κ) :=
  fun x hx p hp => lt_of_le_of_lt (le_of_mem_comps hp) hx

/-- `Y` together with the components of its elements is closed under additive decomposition. -/
theorem DC_withComps (Y : Set Ordinal.{0}) : DC (Y ∪ {p | ∃ y ∈ Y, p ∈ comps y}) := by
  intro x hx p hp
  rcases hx with hx | ⟨y, hy, hxy⟩
  · exact Or.inr ⟨x, hx, hp⟩
  · rw [comps_of_mem_comps hxy, List.mem_singleton] at hp
    subst hp
    exact Or.inr ⟨y, hy, hxy⟩

/-! ## Segments -/

/-- `x ∈ seg(b) ∩ Ω₁`: `b ≤ x < Ω₁` and `x` lies below every `υ`-point above `b`. -/
def InSeg (b x : Ordinal.{0}) : Prop := b ≤ x ∧ x < Om1 ∧ ∀ u, b < u → UpsPt u → x < u

theorem InSeg.self {b : Ordinal.{0}} (hb1 : b < Om1) : InSeg b b :=
  ⟨le_rfl, hb1, fun _ hu _ => hu⟩

/-- A point strictly inside a segment is not a `υ`-point. -/
theorem InSeg.not_ups {b x : Ordinal.{0}} (h : InSeg b x) (hbx : b < x) : ¬ UpsPt x :=
  fun hx => lt_irrefl x (h.2.2 x hbx hx)

/-- [W07b] Cor 5.10: for a countable `υ`-point `τ`, `seg(τ) ∩ Ω₁ = [τ, Ω₁) ∩ Tᵗ`. -/
theorem inSeg_iff {b x : Ordinal.{0}} (hb : UpsPt b) (hb1 : b < Om1) :
    InSeg b x ↔ b ≤ x ∧ x < Om1 ∧ x ∈ Tset b := by
  obtain ⟨m, hm, hT⟩ := exists_next hb hb1
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, (hT x h2).2 (h3 m hm.1 hm.2.1)⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun u hu hu' => lt_of_lt_of_le ((hT x h2).1 h3) (hm.2.2 u hu hu')⟩

/-- For an `ε`-number `γ` strictly inside `seg(c)` (`c` a `υ`-point): `T^γ ∩ Ω₁ = c^∞`
([W07b] Cor 5.10 at `γ`). -/
theorem T_of_inSeg_E {c γ x : Ordinal.{0}} (hγ : InE γ) (hcγ : InSeg c γ) (hx1 : x < Om1)
    (hx : ∀ u, c < u → UpsPt u → x < u) : x ∈ Tset γ := by
  obtain ⟨m, hγm, hm, hmin, hT⟩ := T_inter_Om1 hγ hcγ.2.1
  refine (hT x hx1).2 (hx m (lt_of_le_of_lt hcγ.1 hγm) ⟨lt_of_le_of_lt (by simp) hγm, hm⟩)

/-! ## The domains `D_k` -/

/-- `D_k` of the paper proof (with `Cl`). -/
def DD (κ : Ordinal.{0}) (b : ℕ → Ordinal.{0}) : ℕ → Set Ordinal.{0}
  | 0 => Set.Iio κ
  | k + 1 => DD κ b k ∪
      {x | InSeg (b k) x ∧ x ∈ Tset (b k) ∧ ↑(Par (b k) x) ⊆ ClS (DD κ b k)}

/-- The hypotheses on a list of bases `b_0 < ⋯ < b_{m-1}` above `κ`. -/
structure Chain (κ : Ordinal.{0}) (b : ℕ → Ordinal.{0}) (m : ℕ) : Prop where
  kap : UpsPt κ
  kap1 : κ < Om1
  ups : ∀ k, k < m → UpsPt (b k) ∧ b k < Om1
  mono : ∀ j k, j < k → k < m → b j < b k
  bot : ∀ k, k < m → κ < b k

theorem Chain.of_succ {κ : Ordinal.{0}} {b : ℕ → Ordinal.{0}} {m : ℕ} (h : Chain κ b (m + 1)) :
    Chain κ b m :=
  ⟨h.kap, h.kap1, fun k hk => h.ups k (by omega), fun j k hjk hk => h.mono j k hjk (by omega),
    fun k hk => h.bot k (by omega)⟩

theorem DD_mono {κ : Ordinal.{0}} {b : ℕ → Ordinal.{0}} {j k : ℕ} (hjk : j ≤ k) :
    DD κ b j ⊆ DD κ b k := by
  induction hjk with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans Set.subset_union_left

/-- Every element of `D_m` is below `κ` or in exactly one segment `seg(b_k)`, `k < m`. -/
theorem mem_DD {κ : Ordinal.{0}} {b : ℕ → Ordinal.{0}} {m : ℕ} {x : Ordinal.{0}}
    (hx : x ∈ DD κ b m) : x < κ ∨ ∃ k, k < m ∧ InSeg (b k) x ∧ x ∈ Tset (b k) ∧
      ↑(Par (b k) x) ⊆ ClS (DD κ b k) := by
  induction m with
  | zero => exact Or.inl hx
  | succ m ih =>
    rcases hx with hx | hx
    · rcases ih hx with h | ⟨k, hk, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨k, by omega, h⟩
    · exact Or.inr ⟨m, by omega, hx⟩

/-- The segments of a chain are disjoint. -/
theorem InSeg.unique {κ : Ordinal.{0}} {b : ℕ → Ordinal.{0}} {m : ℕ} (hb : Chain κ b m)
    {j k : ℕ} (hj : j < m) (hk : k < m) {x : Ordinal.{0}} (h1 : InSeg (b j) x)
    (h2 : InSeg (b k) x) : j = k := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact absurd (h1.2.2 (b k) (hb.mono j k h hk) (hb.ups k hk).1) (not_lt.2 h2.1)
  · exact absurd (h2.2.2 (b j) (hb.mono k j h hj) (hb.ups j hj).1) (not_lt.2 h1.1)

/-- `D_{k+1}` lies below every `υ`-point above `b_k`. -/
theorem DD_lt_ups {κ : Ordinal.{0}} {b : ℕ → Ordinal.{0}} {m : ℕ} (hb : Chain κ b (m + 1))
    {x : Ordinal.{0}} (hx : x ∈ DD κ b (m + 1)) :
    ∀ u, b m < u → UpsPt u → x < u := by
  intro u hu hu'
  rcases mem_DD hx with h | ⟨k, hk, hs, -, -⟩
  · exact (h.trans (hb.bot m (by omega))).trans hu
  · rcases Nat.lt_or_ge k m with hkm | hkm
    · exact (hs.2.2 (b m) (hb.mono k m hkm (by omega)) (hb.ups m (by omega)).1).trans hu
    · have : k = m := by omega
      subst this; exact hs.2.2 u hu hu'

theorem DD_lt_Om1 {κ : Ordinal.{0}} {b : ℕ → Ordinal.{0}} {m : ℕ} (hb : Chain κ b m)
    {x : Ordinal.{0}} (hx : x ∈ DD κ b m) : x < Om1 := by
  rcases mem_DD hx with h | ⟨k, hk, hs, -, -⟩
  · exact h.trans hb.kap1
  · exact hs.2.1

/-! ## One base change on a set -/

theorem mul_two_eq (a : Ordinal.{0}) : a * 2 = a + a := by
  rw [show (2 : Ordinal.{0}) = 1 + 1 from one_add_one_eq_two.symm, mul_add, mul_one]

theorem InE.pos {e : Ordinal.{0}} (he : InE e) : 0 < e := by
  rcases eq_or_ne e 0 with h | h
  · exfalso; rw [h] at he; unfold InE at he; simp at he
  · exact pos_iff_ne_zero.2 h

theorem down_mono {σ τ : Ordinal.{0}} (h : Bases σ τ) {S : Set Ordinal.{0}} (hS : S ⊆ TB τ σ) :
    StrictMonoOn (pi σ τ) S := (pi_bijOn h).2.mono hS

theorem down_add {σ τ : Ordinal.{0}} (h : Bases σ τ) {S : Set Ordinal.{0}} (hS : S ⊆ TB τ σ) :
    ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, (x + y = z ↔ pi σ τ x + pi σ τ y = pi σ τ z) := by
  intro x hx y hy z hz
  obtain ⟨hxyT, hpxy⟩ := pi_add h (hS hx) (hS hy)
  constructor
  · intro e; rw [← hpxy, e]
  · intro e
    rw [← hpxy] at e
    exact (pi_bijOn h).1.injOn hxyT (hS hz) e

theorem down_gt {σ τ : Ordinal.{0}} (h : Bases σ τ) {x : Ordinal.{0}} (hx : x ∈ TB τ σ)
    (h1 : τ < x) : σ < pi σ τ x := by
  have hb := pi_base h
  have := (pi_bijOn h).2 hb.1 hx h1
  rwa [hb.2] at this

theorem down_ge {σ τ : Ordinal.{0}} (h : Bases σ τ) {x : Ordinal.{0}} (hx : x ∈ TB τ σ)
    (h1 : τ ≤ x) : σ ≤ pi σ τ x := by
  rcases eq_or_lt_of_le h1 with rfl | h1
  · exact (pi_base h).2.ge
  · exact (down_gt h hx h1).le

theorem down_lt_Om1 {σ τ : Ordinal.{0}} (h : Bases σ τ) {x : Ordinal.{0}} (hx : x ∈ TB τ σ)
    (h1 : x < Om1) : pi σ τ x < Om1 := by
  have hO := pi_Om1 h
  have := (pi_bijOn h).2 hx hO.1 h1
  rwa [hO.2] at this

theorem down_E {σ τ : Ordinal.{0}} (h : Bases σ τ) {x : Ordinal.{0}} (hx : x ∈ TB τ σ)
    (h1 : τ < x) (h2 : x < Om1) : InE x ↔ InE (pi σ τ x) := by
  obtain ⟨hxx, hpxx⟩ := pi_add h hx hx
  have hx0 : 0 < x := lt_of_le_of_lt (by simp) h1
  have hp0 : 0 < pi σ τ x := lt_of_le_of_lt (by simp) (down_gt h hx h1)
  rw [← le1R_two_iff hx0, ← le1R_two_iff hp0, mul_two_eq, mul_two_eq, st_le1 h hx h1 h2 hxx,
    hpxx]

/-- The inverse base change `π_{σ,τ}⁻¹ : Tᵟ → Tᵗ[σ]`. -/
noncomputable def up (σ τ : Ordinal.{0}) : Ordinal.{0} → Ordinal.{0} :=
  Function.invFunOn (pi σ τ) (TB τ σ)

theorem up_spec {σ τ : Ordinal.{0}} (h : Bases σ τ) {x : Ordinal.{0}} (hx : x ∈ Tset σ) :
    up σ τ x ∈ TB τ σ ∧ pi σ τ (up σ τ x) = x := by
  have hex : ∃ a ∈ TB τ σ, pi σ τ a = x := (pi_bijOn h).1.surjOn hx
  exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩

theorem up_pi {σ τ : Ordinal.{0}} (h : Bases σ τ) {y : Ordinal.{0}} (hy : y ∈ TB τ σ) :
    up σ τ (pi σ τ y) = y := by
  have hs := up_spec h ((pi_bijOn h).1.mapsTo hy)
  exact (pi_bijOn h).1.injOn hs.1 hy hs.2

theorem up_lt {σ τ : Ordinal.{0}} (h : Bases σ τ) {x : Ordinal.{0}} (hx : x < σ) :
    up σ τ x = x := by
  have hxT : x ∈ TB τ σ := (TB_inter_lt h (hx.trans h.2.2.1)).2 hx
  have := up_pi h hxT
  rwa [pi_lt h hx] at this

theorem up_base {σ τ : Ordinal.{0}} (h : Bases σ τ) : up σ τ σ = τ := by
  have := up_pi h (pi_base h).1
  rwa [(pi_base h).2] at this

theorem up_mono {σ τ : Ordinal.{0}} (h : Bases σ τ) {S : Set Ordinal.{0}} (hS : S ⊆ Tset σ) :
    StrictMonoOn (up σ τ) S := by
  intro x hx y hy hxy
  have hsx := up_spec h (hS hx)
  have hsy := up_spec h (hS hy)
  by_contra hle
  have := ((pi_bijOn h).2.le_iff_le hsy.1 hsx.1).2 (not_lt.1 hle)
  rw [hsx.2, hsy.2] at this
  exact absurd hxy (not_lt.2 this)

theorem up_add {σ τ : Ordinal.{0}} (h : Bases σ τ) {S : Set Ordinal.{0}} (hS : S ⊆ Tset σ) :
    ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, (x + y = z ↔ up σ τ x + up σ τ y = up σ τ z) := by
  intro x hx y hy z hz
  have hsx := up_spec h (hS hx)
  have hsy := up_spec h (hS hy)
  have hsz := up_spec h (hS hz)
  obtain ⟨hxyT, hpxy⟩ := pi_add h hsx.1 hsy.1
  constructor
  · intro e
    refine (pi_bijOn h).1.injOn hxyT hsz.1 ?_
    rw [hpxy, hsx.2, hsy.2, hsz.2, e]
  · intro e
    have := congrArg (pi σ τ) e
    rwa [hpxy, hsx.2, hsy.2, hsz.2] at this

theorem up_gt {σ τ : Ordinal.{0}} (h : Bases σ τ) {x : Ordinal.{0}} (hx : x ∈ Tset σ)
    (h1 : σ < x) : τ < up σ τ x := by
  have hs := up_spec h hx
  have hb := pi_base h
  by_contra hle
  have := ((pi_bijOn h).2.le_iff_le hs.1 hb.1).2 (not_lt.1 hle)
  rw [hs.2, hb.2] at this
  exact absurd h1 (not_lt.2 this)

theorem up_ge {σ τ : Ordinal.{0}} (h : Bases σ τ) {x : Ordinal.{0}} (hx : x ∈ Tset σ)
    (h1 : σ ≤ x) : τ ≤ up σ τ x := by
  rcases eq_or_lt_of_le h1 with rfl | h1
  · exact (up_base h).ge
  · exact (up_gt h hx h1).le

theorem up_lt_Om1 {σ τ : Ordinal.{0}} (h : Bases σ τ) {x : Ordinal.{0}} (hx : x ∈ Tset σ)
    (h1 : x < Om1) : up σ τ x < Om1 := by
  have hs := up_spec h hx
  have hO := pi_Om1 h
  by_contra hle
  have := ((pi_bijOn h).2.le_iff_le hO.1 hs.1).2 (not_lt.1 hle)
  rw [hs.2, hO.2] at this
  exact absurd h1 (not_lt.2 this)

theorem up_le1 {σ τ : Ordinal.{0}} (h : Bases σ τ) {x y : Ordinal.{0}} (hx : x ∈ Tset σ)
    (h1 : σ < x) (h2 : x < Om1) (hy : y ∈ Tset σ) : le1R x y ↔ le1R (up σ τ x) (up σ τ y) := by
  have hsx := up_spec h hx
  have hsy := up_spec h hy
  have := st_le1 h hsx.1 (up_gt h hx h1) (up_lt_Om1 h hx h2) hsy.1
  rw [hsx.2, hsy.2] at this
  exact this.symm

theorem up_E {σ τ : Ordinal.{0}} (h : Bases σ τ) {x : Ordinal.{0}} (hx : x ∈ Tset σ)
    (h1 : σ < x) (h2 : x < Om1) : InE x ↔ InE (up σ τ x) := by
  have hsx := up_spec h hx
  have := down_E h hsx.1 (up_gt h hx h1) (up_lt_Om1 h hx h2)
  rw [hsx.2] at this
  exact this.symm

/-! ## The `≤₁`-cases of the paper proof (F-d) and the conclusion -/

/-- The conclusion of Theorem FRAG for a map `Ψ` on a finite `F`. -/
def FragConcl (κ : Ordinal.{0}) (b c : ℕ → Ordinal.{0}) (m : ℕ) (F : Finset Ordinal.{0})
    (Ψ : Ordinal.{0} → Ordinal.{0}) : Prop :=
  (∀ x ∈ F, x < κ → Ψ x = x) ∧
  (∀ k, k < m → ∀ x ∈ F, InSeg (b k) x → InSeg (c k) (Ψ x)) ∧
  (∀ k, k < m → b k ∈ F → Ψ (b k) = c k) ∧
  ArithIso ↑F (Ψ '' ↑F) Ψ ∧
  (∀ x ∈ F, ∀ y ∈ F, le1R x y ↔ le1R (Ψ x) (Ψ y)) ∧
  (∀ x ∈ F, UpsPt (Ψ x) ↔ UpsPt x) ∧
  (∀ x ∈ F, InE x → InE (Ψ x))

/-- A point strictly inside `seg(b_j)` is `≤₁` no `y ≥ u`, `u > b_j` a `υ`-point. -/
theorem not_le1R_of_inSeg {bj x u y : Ordinal.{0}} (hs : InSeg bj x) (hbx : bj < x)
    (hu : UpsPt u) (hbu : bj < u) (huy : u ≤ y) : ¬ le1R x y := by
  intro h
  have hxu : x < u := hs.2.2 u hbu hu
  have := (le1R_lt_ups hu hxu huy).1 h
  exact hs.not_ups hbx ⟨lt_of_le_of_lt (by simp) hbx, this⟩

theorem concl_of {κ : Ordinal.{0}} {b c : ℕ → Ordinal.{0}} {m : ℕ} (hb : Chain κ b m)
    (hc : Chain κ c m) {F : Finset Ordinal.{0}} (hF : ↑F ⊆ DD κ b m)
    (hbF : ∀ k, k < m → b k ∈ F) {Ψ : Ordinal.{0} → Ordinal.{0}}
    (h1 : ∀ x ∈ F, x < κ → Ψ x = x)
    (h2 : ∀ k, k < m → ∀ x ∈ F, InSeg (b k) x → InSeg (c k) (Ψ x))
    (h3 : ∀ k, k < m → Ψ (b k) = c k)
    (h4 : StrictMonoOn Ψ ↑F)
    (hadd : ∀ x ∈ F, ∀ y ∈ F, ∀ z ∈ F, (x + y = z ↔ Ψ x + Ψ y = Ψ z))
    (h5 : ∀ k, k < m → ∀ x ∈ F, ∀ y ∈ F, InSeg (b k) x → InSeg (b k) y → b k < x →
      (le1R x y ↔ le1R (Ψ x) (Ψ y)))
    (h6 : ∀ k, k < m → ∀ x ∈ F, InSeg (b k) x → b k < x → InE x → InE (Ψ x)) :
    FragConcl κ b c m F Ψ := by
  -- where a point of `F` lies
  have hloc : ∀ x ∈ F, x < κ ∨ ∃ k, k < m ∧ InSeg (b k) x := by
    intro x hx
    rcases mem_DD (hF hx) with h | ⟨k, hk, hs, -, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨k, hk, hs⟩
  -- `Ψ` above `b_k` inside the segment
  have hgt : ∀ k, k < m → ∀ x ∈ F, b k < x → c k < Ψ x := by
    intro k hk x hx hbx
    rw [← h3 k hk]; exact h4 (hbF k hk) hx hbx
  refine ⟨h1, h2, fun k hk _ => h3 k hk, ⟨h4.injOn.bijOn_image, h4, hadd⟩, ?_, ?_, ?_⟩
  · intro x hx y hy
    rcases hloc x hx with hxk | ⟨j, hj, hxs⟩ <;> rcases hloc y hy with hyk | ⟨k, hk, hys⟩
    · rw [h1 x hx hxk, h1 y hy hyk]
    · rw [h1 x hx hxk, le1R_lt_ups hb.kap hxk ((hb.bot k hk).le.trans hys.1),
        le1R_lt_ups hb.kap hxk ((hc.bot k hk).le.trans (h2 k hk y hy hys).1)]
    · have hyx : y < x := lt_of_lt_of_le (hyk.trans (hb.bot j hj)) hxs.1
      have hyx' : Ψ y < Ψ x := h4 hy hx hyx
      exact ⟨fun h => absurd (le1R_le h) (not_le.2 hyx),
        fun h => absurd (le1R_le h) (not_le.2 hyx')⟩
    · rcases lt_trichotomy j k with hjk | rfl | hjk
      · -- D2
        rcases eq_or_lt_of_le hxs.1 with rfl | hbx
        · rw [h3 j hj]
          exact ⟨fun _ => (hc.ups j hj).1.2 _ (((hc.mono j k hjk hk).le).trans
              (h2 k hk y hy hys).1),
            fun _ => (hb.ups j hj).1.2 _ (((hb.mono j k hjk hk).le).trans hys.1)⟩
        · have n1 := not_le1R_of_inSeg hxs hbx (hb.ups k hk).1 (hb.mono j k hjk hk) hys.1
          have n2 := not_le1R_of_inSeg (h2 j hj x hx hxs) (hgt j hj x hx hbx) (hc.ups k hk).1
            (hc.mono j k hjk hk) (h2 k hk y hy hys).1
          exact ⟨fun h => absurd h n1, fun h => absurd h n2⟩
      · rcases eq_or_lt_of_le hxs.1 with rfl | hbx
        · -- D3
          rw [h3 j hj]
          exact ⟨fun _ => (hc.ups j hj).1.2 _ (h2 j hj y hy hys).1,
            fun _ => (hb.ups j hj).1.2 _ hys.1⟩
        · exact h5 j hj x hx y hy hxs hys hbx
      · have hyx : y < x :=
          lt_of_lt_of_le (hys.2.2 (b j) (hb.mono k j hjk hj) (hb.ups j hj).1) hxs.1
        have hyx' : Ψ y < Ψ x := h4 hy hx hyx
        exact ⟨fun h => absurd (le1R_le h) (not_le.2 hyx),
          fun h => absurd (le1R_le h) (not_le.2 hyx')⟩
  · intro x hx
    rcases hloc x hx with hxk | ⟨j, hj, hxs⟩
    · rw [h1 x hx hxk]
    · rcases eq_or_lt_of_le hxs.1 with rfl | hbx
      · rw [h3 j hj]; exact ⟨fun _ => (hb.ups j hj).1, fun _ => (hc.ups j hj).1⟩
      · exact ⟨fun h => absurd h ((h2 j hj x hx hxs).not_ups (hgt j hj x hx hbx)),
          fun h => absurd h (hxs.not_ups hbx)⟩
  · intro x hx hE
    rcases hloc x hx with hxk | ⟨j, hj, hxs⟩
    · rw [h1 x hx hxk]; exact hE
    · rcases eq_or_lt_of_le hxs.1 with rfl | hbx
      · rw [h3 j hj]; exact upsPt_inE (hc.ups j hj).1
      · exact h6 j hj x hx hxs hbx hE

end Googology.Trans.PoR.InaccPsi.R2
