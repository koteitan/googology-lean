import Googology.Notation.InaccPsi

/-!
# The simultaneously defined collapsing functions `ϑ̄ᵢ` over a base `τ`

[W25] G. Wilken, "Fundamental sequences based on localization", arXiv 2410.15953v4 (2025), §2.2:
Definition 2.7 (= Def 2.1 of Weiermann–Wilken 2011) and Definition 2.9.

The setting ([W25] §2.1, §2.2): `Ω₀ = τ` and `Ωᵢ = ℵᵢ` for `0 < i < ω` ("The canonical choice is to assume
that `τ` is countable (recursive) and that `Ωᵢ = ℵᵢ` for `0 < i < ω`"), `Ω_ω = sup_{n<ω} Ωₙ`.  Here
`OmT τ i` is `Ωᵢ` (`Om i = ω_i` of the InaccPsi notation for `i > 0`).

[W25] Definition 2.7: "Simultaneously for all `i < ω` we define sets of ordinals `C̄ᵢ(α, β)` where
`β ≤ Ω_{i+1}` and, whenever `α ∈ C̄ᵢ(α, Ω_{i+1}) ∩ Ω_ω`, ordinals `ϑ̄ᵢ(α)` by recursion on `α ≤ Ω_ω`.  For
each `β ≤ Ω_{i+1}` the set `C̄ᵢ(α, β)` is defined inductively by
1. `Ωᵢ ∪ β ⊆ C̄ᵢ(α, β)`
2. `ξ, η ∈ C̄ᵢ(α, β) ⇒ ξ + η ∈ C̄ᵢ(α, β)`
3. `j ∈ [i, ω) & ξ ∈ C̄ⱼ(ξ, Ω_{j+1}) ∩ C̄ᵢ(α, β) ∩ α ⇒ ϑ̄ⱼ(ξ) ∈ C̄ᵢ(α, β)`.
For `α ∈ C̄ᵢ(α, Ω_{i+1})` we define
`ϑ̄ᵢ(α) := min({ξ < Ω_{i+1} | α ∈ C̄ᵢ(α, ξ) & C̄ᵢ(α, ξ) ∩ Ω_{i+1} ⊆ ξ} ∪ {Ω_{i+1}})`.
We then define `dom(ϑ̄ᵢ) := {α < Ω_ω | α ∈ C̄ᵢ(α, Ω_{i+1})}`."
[W25] Definition 2.9: "`T̄_m := C̄_m(Ω_ω, 0)`.  We set `T̄^τ := T̄₀`".

Lean: `Mem τ g a i b x` is `x ∈ C̄ᵢ(a, b)` computed with `g ξ j` for `ϑ̄ⱼ(ξ)`; `thb τ` is defined by
well-founded recursion on `a` (`thb τ a i = ϑ̄ᵢ(a)`); `thb_eq` is the defining equation with `g = thb τ`.
The definition is total (any `a`, `b`); the paper's values are the ones with `a ≤ Ω_ω`, `b ≤ Ω_{i+1}`,
`a ∈ dom` (clause 3 only applies `ϑ̄ⱼ` to `ξ < a ≤ Ω_ω` with `ξ ∈ C̄ⱼ(ξ, Ω_{j+1})`, i.e. `ξ ∈ dom(ϑ̄ⱼ)`).

Proved here, with no axiom (for `τ = 1` or `τ` an epsilon number, `τ < Ω₁`): for `α ∈ dom(ϑ̄ᵢ)`,
`ϑ̄ᵢ(α) < Ω_{i+1}` (the regularity argument, `thb_lt`), `ϑ̄ᵢ(α)` satisfies its defining condition
(`thb_good`), `Ωᵢ ≤ ϑ̄ᵢ(α)`, `ϑ̄ᵢ(α)` is additively principal, `ϑ̄ᵢ` is injective on `dom(ϑ̄ᵢ)`, and
`T̄^τ ⊆ Ω_ω` is closed under `+` and the `ϑ̄ⱼ` on their domains.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Cardinal Set Googology.Notation.InaccPsi

/-- `Ωᵢ` of the setting: `Ω₀ = τ`, `Ωᵢ = ω_i` for `i > 0`. -/
noncomputable def OmT (τ : Ordinal.{0}) (i : ℕ) : Ordinal.{0} :=
  if i = 0 then τ else Om (i : Ordinal.{0})

/-- `Mem τ g a i b x`: `x ∈ C̄ᵢ(a, b)` ([W25] Def 2.7), with `g ξ j` in the place of `ϑ̄ⱼ(ξ)`. -/
inductive Mem (τ : Ordinal.{0}) (g : Ordinal.{0} → ℕ → Ordinal.{0}) :
    Ordinal.{0} → ℕ → Ordinal.{0} → Ordinal.{0} → Prop
  | base {a : Ordinal.{0}} {i : ℕ} {b x : Ordinal.{0}} : x < OmT τ i → Mem τ g a i b x
  | small {a : Ordinal.{0}} {i : ℕ} {b x : Ordinal.{0}} : x < b → Mem τ g a i b x
  | add {a : Ordinal.{0}} {i : ℕ} {b x y : Ordinal.{0}} :
      Mem τ g a i b x → Mem τ g a i b y → Mem τ g a i b (x + y)
  | th {a : Ordinal.{0}} {i : ℕ} {b : Ordinal.{0}} {j : ℕ} {ξ : Ordinal.{0}} :
      i ≤ j → ξ < a → Mem τ g ξ j (OmT τ (j + 1)) ξ → Mem τ g a i b ξ → Mem τ g a i b (g ξ j)

/-- The defining condition of `ϑ̄ᵢ(a)`: `ξ < Ω_{i+1}`, `a ∈ C̄ᵢ(a, ξ)`, `C̄ᵢ(a, ξ) ∩ Ω_{i+1} ⊆ ξ`. -/
def Good (τ : Ordinal.{0}) (g : Ordinal.{0} → ℕ → Ordinal.{0}) (a : Ordinal.{0}) (i : ℕ)
    (ξ : Ordinal.{0}) : Prop :=
  ξ < OmT τ (i + 1) ∧ Mem τ g a i ξ a ∧ ∀ x, Mem τ g a i ξ x → x < OmT τ (i + 1) → x < ξ

/-- One step of the recursion: `ϑ̄ᵢ(a)` from the values `ϑ̄ⱼ(y)`, `y < a`. -/
noncomputable def thbF (τ : Ordinal.{0}) (a : Ordinal.{0})
    (IH : ∀ y : Ordinal.{0}, y < a → ℕ → Ordinal.{0}) (i : ℕ) : Ordinal.{0} :=
  sInf ({ξ | Good τ (fun y j => if h : y < a then IH y h j else 0) a i ξ} ∪ {OmT τ (i + 1)})

/-- `thb τ a i = ϑ̄ᵢ(a)` over the base `τ` ([W25] Def 2.7). -/
noncomputable def thb (τ : Ordinal.{0}) : Ordinal.{0} → ℕ → Ordinal.{0} :=
  (wellFounded_lt (α := Ordinal.{0})).fix (thbF τ)

/-- `dom(ϑ̄ᵢ) = {α < Ω_ω | α ∈ C̄ᵢ(α, Ω_{i+1})}` ([W25] Def 2.7). -/
def Dom (τ : Ordinal.{0}) (i : ℕ) (a : Ordinal.{0}) : Prop :=
  a < Om (ω : Ordinal.{0}) ∧ Mem τ (thb τ) a i (OmT τ (i + 1)) a

/-- `T̄^τ = C̄₀(Ω_ω, 0)` ([W25] Def 2.9). -/
def Tbar (τ : Ordinal.{0}) : Set Ordinal.{0} := {x | Mem τ (thb τ) (Om (ω : Ordinal.{0})) 0 0 x}

/-- The base: `τ = 1` or `τ` an epsilon number, and `τ < Ω₁`. -/
def Base (τ : Ordinal.{0}) : Prop := (τ = 1 ∨ ω ^ τ = τ) ∧ τ < Om (1 : Ordinal.{0})

variable {τ : Ordinal.{0}}

/-! ## The recursion -/

theorem thb_fix (τ a : Ordinal.{0}) : thb τ a = thbF τ a (fun y _ => thb τ y) :=
  WellFounded.fix_eq _ _ _

/-- `Mem` only reads `g` below `a`. -/
theorem Mem.congr {g g' : Ordinal.{0} → ℕ → Ordinal.{0}} {a : Ordinal.{0}} {i : ℕ}
    {b x : Ordinal.{0}} (h : Mem τ g a i b x) :
    (∀ y < a, ∀ j, g y j = g' y j) → Mem τ g' a i b x := by
  induction h with
  | base h => exact fun _ => Mem.base h
  | small h => exact fun _ => Mem.small h
  | add _ _ ihx ihy => exact fun hg => Mem.add (ihx hg) (ihy hg)
  | @th a i b j ξ hij hξ _ _ ihd ihm =>
    intro hg
    rw [hg ξ hξ j]
    exact Mem.th hij hξ (ihd fun y hy k => hg y (hy.trans hξ) k) (ihm hg)

theorem Mem.congr_iff {g g' : Ordinal.{0} → ℕ → Ordinal.{0}} {a : Ordinal.{0}} {i : ℕ}
    {b x : Ordinal.{0}} (hg : ∀ y < a, ∀ j, g y j = g' y j) :
    Mem τ g a i b x ↔ Mem τ g' a i b x :=
  ⟨fun h => h.congr hg, fun h => h.congr fun y hy j => (hg y hy j).symm⟩

/-- **The defining equation of `ϑ̄ᵢ`** ([W25] Def 2.7). -/
theorem thb_eq (τ a : Ordinal.{0}) (i : ℕ) :
    thb τ a i = sInf ({ξ | Good τ (thb τ) a i ξ} ∪ {OmT τ (i + 1)}) := by
  rw [thb_fix]
  unfold thbF
  have hg : ∀ y < a, ∀ j, (fun y j => if h : y < a then thb τ y j else 0) y j = thb τ y j := by
    intro y hy j; simp [hy]
  congr 2
  ext ξ
  simp only [Set.mem_setOf_eq, Good]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, (Mem.congr_iff hg).1 h2, fun x hx => h3 x ((Mem.congr_iff hg).2 hx)⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, (Mem.congr_iff hg).2 h2, fun x hx => h3 x ((Mem.congr_iff hg).1 hx)⟩

/-! ## Monotonicity -/

theorem Mem.mono_b {g : Ordinal.{0} → ℕ → Ordinal.{0}} {a : Ordinal.{0}} {i : ℕ}
    {b b' x : Ordinal.{0}} (h : Mem τ g a i b x) (hb : b ≤ b') : Mem τ g a i b' x := by
  induction h with
  | base h => exact Mem.base h
  | small h => exact Mem.small (lt_of_lt_of_le h hb)
  | add _ _ ihx ihy => exact Mem.add (ihx hb) (ihy hb)
  | th hij hξ hd _ _ ihm => exact Mem.th hij hξ hd (ihm hb)

theorem Mem.mono_a {g : Ordinal.{0} → ℕ → Ordinal.{0}} {a a' : Ordinal.{0}} {i : ℕ}
    {b x : Ordinal.{0}} (h : Mem τ g a i b x) (ha : a ≤ a') : Mem τ g a' i b x := by
  induction h with
  | base h => exact Mem.base h
  | small h => exact Mem.small h
  | add _ _ ihx ihy => exact Mem.add (ihx ha) (ihy ha)
  | th hij hξ hd _ _ ihm => exact Mem.th hij (lt_of_lt_of_le hξ ha) hd (ihm ha)

/-! ## The cardinals `Ωᵢ` -/

theorem OmT_zero (τ : Ordinal.{0}) : OmT τ 0 = τ := if_pos rfl

theorem OmT_succ (τ : Ordinal.{0}) (i : ℕ) : OmT τ (i + 1) = Om ((i : Ordinal.{0}) + 1) := by
  rw [OmT, if_neg (Nat.succ_ne_zero i)]; push_cast; rfl

theorem OmT_pos_of_ne {i : ℕ} (hi : i ≠ 0) (τ : Ordinal.{0}) :
    OmT τ i = Om (i : Ordinal.{0}) := if_neg hi

theorem natCast_succ_ne_zero (i : ℕ) : ((i : Ordinal.{0}) + 1) ≠ 0 := by
  rw [← Order.succ_eq_add_one]; exact Order.succ_ne_bot _

theorem OmT_succ_regular (τ : Ordinal.{0}) (i : ℕ) :
    (OmT τ (i + 1)).card.IsRegular ∧ ℵ₀ < (OmT τ (i + 1)).card ∧
      OmT τ (i + 1) = (OmT τ (i + 1)).card.ord := by
  rw [OmT_succ]
  have hs := natCast_succ_ne_zero i
  refine ⟨?_, aleph0_lt_card_Om hs, ?_⟩
  · rw [card_Om hs]; exact isRegular_aleph_add_one _
  · rw [card_Om hs, Om_eq_ord hs]

theorem OmT_succ_isSuccLimit (τ : Ordinal.{0}) (i : ℕ) : Order.IsSuccLimit (OmT τ (i + 1)) := by
  rw [OmT_succ]; exact InaccSeq.Om_isSuccLimit (natCast_succ_ne_zero i)

theorem OmT_succ_pos (τ : Ordinal.{0}) (i : ℕ) : 0 < OmT τ (i + 1) := by
  rw [OmT_succ]; exact Om_pos (natCast_succ_ne_zero i)

theorem Om_lt_Om_omega (n : ℕ) : Om (n : Ordinal.{0}) < Om (ω : Ordinal.{0}) :=
  Om_lt_Om.2 (natCast_lt_omega0 n)

theorem OmT_succ_lt_Om_omega (τ : Ordinal.{0}) (i : ℕ) : OmT τ (i + 1) < Om (ω : Ordinal.{0}) := by
  rw [OmT_succ]
  have : ((i : Ordinal.{0}) + 1) = ((i + 1 : ℕ) : Ordinal.{0}) := by push_cast; rfl
  rw [this]; exact Om_lt_Om_omega _

theorem Base.pos (hτ : Base τ) : 0 < τ := by
  rcases hτ.1 with h | h
  · rw [h]; exact zero_lt_one
  · by_contra h0
    rw [not_lt, nonpos_iff_eq_zero] at h0
    rw [h0, opow_zero] at h
    exact one_ne_zero h

theorem Base.lt_Om1 (hτ : Base τ) : τ < Om (1 : Ordinal.{0}) := hτ.2

theorem Base.principal (hτ : Base τ) : IsPrincipal (· + ·) τ := by
  rcases hτ.1 with h | h
  · rw [h]; intro a b ha hb
    rw [Order.lt_one_iff] at ha hb; simp [ha, hb]
  · rw [← h]; exact isPrincipal_add_omega0_opow τ

theorem OmT_lt_succ (hτ : Base τ) (i : ℕ) : OmT τ i < OmT τ (i + 1) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [OmT_zero, show (0 : ℕ) + 1 = 1 from rfl, OmT_pos_of_ne one_ne_zero]
    exact_mod_cast hτ.lt_Om1
  · rw [OmT_pos_of_ne hi.ne', OmT_succ]
    exact Om_lt_Om.2 (by rw [← Order.succ_eq_add_one]; exact Order.lt_succ _)

theorem OmT_pos (hτ : Base τ) (i : ℕ) : 0 < OmT τ i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [OmT_zero]; exact hτ.pos
  · rw [OmT_pos_of_ne hi.ne']; exact Om_pos (by exact_mod_cast hi.ne')

theorem OmT_mono (hτ : Base τ) {i j : ℕ} (h : i ≤ j) : OmT τ i ≤ OmT τ j := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (OmT_lt_succ hτ _).le

theorem OmT_strictMono (hτ : Base τ) {i j : ℕ} (h : i < j) : OmT τ i < OmT τ j :=
  lt_of_lt_of_le (OmT_lt_succ hτ i) (OmT_mono hτ h)

theorem OmT_lt_Om_omega (hτ : Base τ) (i : ℕ) : OmT τ i < Om (ω : Ordinal.{0}) :=
  (OmT_lt_succ hτ i).trans (OmT_succ_lt_Om_omega τ i)

theorem OmT_succ_principal (τ : Ordinal.{0}) (i : ℕ) : IsPrincipal (· + ·) (OmT τ (i + 1)) := by
  rw [OmT_succ]; exact Om_isPrincipal (natCast_succ_ne_zero i)

theorem Om_omega_principal : IsPrincipal (· + ·) (Om (ω : Ordinal.{0})) :=
  Om_isPrincipal omega0_ne_zero

/-! ## The regularity argument: `ϑ̄ᵢ(α) < Ω_{i+1}` for `α ∈ dom(ϑ̄ᵢ)` -/

section Reg

variable {g : Ordinal.{0} → ℕ → Ordinal.{0}}

/-- A member of `C̄ᵢ(a, Ω_{i+1})` is a member of some `C̄ᵢ(a, b)`, `b < Ω_{i+1}`. -/
theorem Mem.exists_lt_of_succ {a : Ordinal.{0}} {i : ℕ} {b x : Ordinal.{0}}
    (h : Mem τ g a i b x) : b = OmT τ (i + 1) → ∃ b' < OmT τ (i + 1), Mem τ g a i b' x := by
  induction h with
  | base h => exact fun _ => ⟨0, OmT_succ_pos τ _, Mem.base h⟩
  | @small a i b x h =>
    intro hb; subst hb
    refine ⟨x + 1, ?_, Mem.small (lt_add_one x)⟩
    rw [← Order.succ_eq_add_one]; exact (OmT_succ_isSuccLimit τ i).succ_lt h
  | add _ _ ihx ihy =>
    intro hb
    obtain ⟨b1, h1, m1⟩ := ihx hb
    obtain ⟨b2, h2, m2⟩ := ihy hb
    exact ⟨max b1 b2, max_lt h1 h2,
      Mem.add (m1.mono_b (le_max_left _ _)) (m2.mono_b (le_max_right _ _))⟩
  | th hij hξ hd _ _ ihm =>
    intro hb
    obtain ⟨b1, h1, m1⟩ := ihm hb
    exact ⟨b1, h1, Mem.th hij hξ hd m1⟩

variable (τ g) in
/-- The finite stages of `C̄ᵢ(a, b)` (with all `g ξ j`, a superset suffices for the size bound). -/
def stage (a : Ordinal.{0}) (i : ℕ) (b : Ordinal.{0}) : ℕ → Set Ordinal.{0}
  | 0 => Iio (max b (OmT τ i))
  | n + 1 =>
      stage a i b n
      ∪ (fun p : Ordinal.{0} × Ordinal.{0} => p.1 + p.2) '' (stage a i b n ×ˢ stage a i b n)
      ∪ ⋃ j : ULift.{1} ℕ, (fun ξ => g ξ j.down) '' stage a i b n

theorem stage_mono (a : Ordinal.{0}) (i : ℕ) (b : Ordinal.{0}) {m n : ℕ} (h : m ≤ n) :
    stage τ g a i b m ⊆ stage τ g a i b n := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact ih.trans fun _ hx => Or.inl (Or.inl hx)

theorem Mem.exists_stage {a : Ordinal.{0}} {i : ℕ} {b x : Ordinal.{0}} (h : Mem τ g a i b x) :
    ∃ n, x ∈ stage τ g a i b n := by
  induction h with
  | base h => exact ⟨0, lt_of_lt_of_le h (le_max_right _ _)⟩
  | small h => exact ⟨0, lt_of_lt_of_le h (le_max_left _ _)⟩
  | @add a i b x y _ _ ihx ihy =>
    obtain ⟨m, hm⟩ := ihx
    obtain ⟨k, hk⟩ := ihy
    refine ⟨max m k + 1, Or.inl (Or.inr ⟨(x, y), ⟨?_, ?_⟩, rfl⟩)⟩
    · exact stage_mono a i b (le_max_left m k) hm
    · exact stage_mono a i b (le_max_right m k) hk
  | @th a i b j ξ _ _ _ _ _ ihm =>
    obtain ⟨m, hm⟩ := ihm
    exact ⟨m + 1, Or.inr (mem_iUnion.2 ⟨⟨j⟩, ξ, hm, rfl⟩)⟩

/-- The bound `max |max b Ωᵢ| ℵ₀`. -/
noncomputable abbrev bndT (τ b : Ordinal.{0}) (i : ℕ) : Cardinal.{1} :=
  max (Cardinal.lift.{1} (max b (OmT τ i)).card) ℵ₀

theorem mk_stage_le (a : Ordinal.{0}) (i : ℕ) (b : Ordinal.{0}) (n : ℕ) :
    #(stage τ g a i b n) ≤ bndT τ b i := by
  have hinf : (ℵ₀ : Cardinal.{1}) ≤ bndT τ b i := le_max_right _ _
  induction n with
  | zero =>
    show #(Iio (max b (OmT τ i))) ≤ _
    rw [Cardinal.mk_Iio_ordinal]; exact le_max_left _ _
  | succ n ih =>
    have hprod : #((stage τ g a i b n ×ˢ stage τ g a i b n : Set (Ordinal.{0} × Ordinal.{0})))
        ≤ bndT τ b i := by
      rw [mk_setProd]
      exact (mul_le_mul' ih ih).trans_eq (mul_eq_self hinf)
    have hA : #((fun p : Ordinal.{0} × Ordinal.{0} => p.1 + p.2) ''
        (stage τ g a i b n ×ˢ stage τ g a i b n)) ≤ bndT τ b i := mk_image_le.trans hprod
    have hB : #(⋃ j : ULift.{1} ℕ, (fun ξ => g ξ j.down) '' stage τ g a i b n) ≤ bndT τ b i := by
      refine (mk_iUnion_le _).trans ?_
      have hcard : #(ULift.{1} ℕ) = ℵ₀ := by simp
      rw [hcard]
      have hsup : (⨆ j : ULift.{1} ℕ, #((fun ξ => g ξ j.down) '' stage τ g a i b n)) ≤ bndT τ b i :=
        ciSup_le fun j => mk_image_le.trans ih
      exact (mul_le_mul' hinf hsup).trans_eq (mul_eq_self hinf)
    refine (mk_union_le _ _).trans ?_
    refine (add_le_add ((mk_union_le _ _).trans (add_le_add ih hA)) hB).trans ?_
    rw [add_eq_self hinf, add_eq_self hinf]

theorem mk_mem_le (a : Ordinal.{0}) (i : ℕ) (b : Ordinal.{0}) :
    #{x | Mem τ g a i b x} ≤ bndT τ b i := by
  have hsub : {x | Mem τ g a i b x} ⊆ ⋃ n : ULift.{1} ℕ, stage τ g a i b n.down := by
    intro x hx
    obtain ⟨n, hn⟩ := Mem.exists_stage hx
    exact mem_iUnion.2 ⟨⟨n⟩, hn⟩
  refine (mk_le_mk_of_subset hsub).trans ((mk_iUnion_le _).trans ?_)
  have hcard : #(ULift.{1} ℕ) = ℵ₀ := by simp
  rw [hcard]
  have hsup : (⨆ n : ULift.{1} ℕ, #(stage τ g a i b n.down)) ≤ bndT τ b i :=
    ciSup_le fun n => mk_stage_le a i b n.down
  exact (mul_le_mul' (le_max_right _ _) hsup).trans_eq (mul_eq_self (le_max_right _ _))

/-- A member of `C̄ᵢ(a, sup_n B_n)` is in some `C̄ᵢ(a, B_n)`, for monotone `B`. -/
theorem Mem.exists_of_iSup {a : Ordinal.{0}} {i : ℕ} {x : Ordinal.{0}}
    {B : ULift.{1} ℕ → Ordinal.{0}} (hB : ∀ m n : ULift.{1} ℕ, m.down ≤ n.down → B m ≤ B n)
    (hx : Mem τ g a i (⨆ n, B n) x) : ∃ n, Mem τ g a i (B n) x := by
  have hbdd : BddAbove (range B) := Ordinal.bddAbove_of_small
  generalize hb : (⨆ n, B n) = b at hx
  induction hx with
  | base h => exact ⟨⟨0⟩, Mem.base h⟩
  | small h =>
    rw [← hb] at h
    obtain ⟨n, hn⟩ := (lt_ciSup_iff hbdd).1 h
    exact ⟨n, Mem.small hn⟩
  | add _ _ ihx ihy =>
    obtain ⟨p, hp⟩ := ihx hb
    obtain ⟨q, hq⟩ := ihy hb
    exact ⟨⟨max p.down q.down⟩, Mem.add (hp.mono_b (hB _ _ (le_max_left _ _)))
      (hq.mono_b (hB _ _ (le_max_right _ _)))⟩
  | th hij hξ hd _ _ ihm =>
    obtain ⟨p, hp⟩ := ihm hb
    exact ⟨p, Mem.th hij hξ hd hp⟩

variable (g) in
/-- **The regularity argument** ([W25] §2.2, after Def 2.7: "by the usual regularity argument, for all
`α ∈ dom(ϑ̄ᵢ)` we have `ϑ̄ᵢ(α) < Ω_{i+1}`"): the condition of `ϑ̄ᵢ(a)` has a solution below `Ω_{i+1}`. -/
theorem exists_good (hτ : Base τ) {a : Ordinal.{0}} {i : ℕ}
    (hdom : Mem τ g a i (OmT τ (i + 1)) a) : ∃ ξ < OmT τ (i + 1), Good τ g a i ξ := by
  set κ := OmT τ (i + 1) with hκdef
  obtain ⟨hreg, hunc, hκord⟩ := OmT_succ_regular τ i
  obtain ⟨b₀, hb₀, hm₀⟩ := hdom.exists_lt_of_succ rfl
  have hlim : Order.IsSuccLimit κ := OmT_succ_isSuccLimit τ i
  have hOi : OmT τ i < κ := OmT_lt_succ hτ i
  let step : Ordinal.{0} → Ordinal.{0} := fun b =>
    max b (⨆ x : ↥({x | Mem τ g a i b x} ∩ Iio κ), Order.succ x.1)
  have hstep_lt : ∀ b < κ, step b < κ := by
    intro b hb
    refine max_lt hb ?_
    have hbc : max b (OmT τ i) < κ.card.ord := lt_of_lt_of_eq (max_lt hb hOi) hκord
    have h : (⨆ x : ↥({x | Mem τ g a i b x} ∩ Iio κ), Order.succ x.1) < κ.card.ord := by
      refine iSup_lt_ord_big hreg ?_ fun x => ?_
      · refine lt_of_le_of_lt ((mk_le_mk_of_subset inter_subset_left).trans (mk_mem_le a i b)) ?_
        refine max_lt ?_ ?_
        · rw [Cardinal.lift_lt]
          exact lt_ord.1 hbc
        · rw [← lift_aleph0.{1, 0}]; exact Cardinal.lift_lt.2 hunc
      · exact lt_of_lt_of_eq (hlim.succ_lt x.2.2) hκord
    exact lt_of_lt_of_eq h hκord.symm
  let B : ℕ → Ordinal.{0} := fun n => Nat.rec b₀ (fun _ b => step b) n
  have hB_lt : ∀ n, B n < κ := by
    intro n
    induction n with
    | zero => exact hb₀
    | succ n ih => exact hstep_lt _ ih
  have hB_succ : ∀ n, B n ≤ B (n + 1) := fun n => le_max_left _ _
  have hB_mono : ∀ m n, m ≤ n → B m ≤ B n := fun m n h => by
    induction h with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans (hB_succ _)
  let B' : ULift.{1} ℕ → Ordinal.{0} := fun n => B n.down
  let β := ⨆ n, B' n
  have hbdd : BddAbove (range B') := Ordinal.bddAbove_of_small
  have hβ : β < κ := by
    have h : β < κ.card.ord := by
      refine iSup_lt_ord_big hreg ?_ fun n => lt_of_lt_of_eq (hB_lt n.down) hκord
      have : #(ULift.{1} ℕ) = ℵ₀ := by simp
      rw [this, ← lift_aleph0.{1, 0}]
      exact Cardinal.lift_lt.2 hunc
    exact lt_of_lt_of_eq h hκord.symm
  refine ⟨β, hβ, hβ, hm₀.mono_b (le_ciSup hbdd ⟨0⟩), fun x hx hxκ => ?_⟩
  obtain ⟨n, hn⟩ := Mem.exists_of_iSup (fun m n h => hB_mono _ _ h) hx
  have h1 : Order.succ x ≤ step (B n.down) :=
    le_trans (le_ciSup (f := fun y : ↥({x | Mem τ g a i (B n.down) x} ∩ Iio κ) => Order.succ y.1)
      Ordinal.bddAbove_of_small ⟨x, hn, hxκ⟩) (le_max_right _ _)
  have h2 : step (B n.down) ≤ β := le_ciSup hbdd ⟨n.down + 1⟩
  exact lt_of_lt_of_le (Order.lt_succ x) (h1.trans h2)

end Reg

/-! ## The basic facts on `ϑ̄ᵢ` -/

/-- For `α ∈ dom(ϑ̄ᵢ)`: `ϑ̄ᵢ(α) < Ω_{i+1}` and `ϑ̄ᵢ(α)` satisfies its defining condition. -/
theorem thb_good (hτ : Base τ) {a : Ordinal.{0}} {i : ℕ} (hd : Dom τ i a) :
    Good τ (thb τ) a i (thb τ a i) := by
  obtain ⟨ξ, hξ, hg⟩ := exists_good (thb τ) hτ hd.2
  set s := {ξ | Good τ (thb τ) a i ξ} ∪ {OmT τ (i + 1)} with hs
  have hne : s.Nonempty := ⟨_, Or.inr rfl⟩
  have hmem := csInf_mem hne
  have hle : sInf s ≤ ξ := csInf_le' (Or.inl hg)
  rw [thb_eq]
  rcases hmem with h | h
  · exact h
  · exact absurd (h ▸ lt_of_le_of_lt hle hξ) (lt_irrefl _)

theorem thb_lt (hτ : Base τ) {a : Ordinal.{0}} {i : ℕ} (hd : Dom τ i a) :
    thb τ a i < OmT τ (i + 1) := (thb_good hτ hd).1

/-- `ϑ̄ᵢ(α) ≥ Ωᵢ`. -/
theorem OmT_le_thb (hτ : Base τ) {a : Ordinal.{0}} {i : ℕ} (hd : Dom τ i a) :
    OmT τ i ≤ thb τ a i := by
  have hg := thb_good hτ hd
  refine le_of_forall_lt fun x hx => ?_
  exact hg.2.2 x (Mem.base hx) (hx.trans (OmT_lt_succ hτ i))

theorem thb_pos (hτ : Base τ) {a : Ordinal.{0}} {i : ℕ} (hd : Dom τ i a) : 0 < thb τ a i :=
  lt_of_lt_of_le (OmT_pos hτ i) (OmT_le_thb hτ hd)

/-- `ϑ̄ᵢ(α)` is additively principal. -/
theorem thb_principal (hτ : Base τ) {a : Ordinal.{0}} {i : ℕ} (hd : Dom τ i a) :
    IsPrincipal (· + ·) (thb τ a i) := by
  have hg := thb_good hτ hd
  intro x y hx hy
  exact hg.2.2 _ (Mem.add (Mem.small hx) (Mem.small hy))
    (OmT_succ_principal τ i (hx.trans hg.1) (hy.trans hg.1))

/-- `ϑ̄ᵢ` is injective on `dom(ϑ̄ᵢ)`. -/
theorem thb_inj (hτ : Base τ) {a a' : Ordinal.{0}} {i : ℕ} (hd : Dom τ i a) (hd' : Dom τ i a')
    (he : thb τ a i = thb τ a' i) : a = a' := by
  by_contra hne
  wlog hlt : a < a' generalizing a a'
  · exact this hd' hd he.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne))
  have hg := thb_good hτ hd
  have hg' := thb_good hτ hd'
  have h1 : Mem τ (thb τ) a' i (thb τ a' i) a := by
    rw [← he]; exact hg.2.1.mono_a hlt.le
  have h2 : Mem τ (thb τ) a' i (thb τ a' i) (thb τ a i) := Mem.th le_rfl hlt hd.2 h1
  have := hg'.2.2 _ h2 (he ▸ hg.1)
  rw [he] at this
  exact lt_irrefl _ this

/-! ## `T̄^τ` -/

theorem Tbar.zero (hτ : Base τ) : (0 : Ordinal.{0}) ∈ Tbar τ := Mem.base (by rw [OmT_zero]; exact hτ.pos)

theorem Tbar.add {x y : Ordinal.{0}} (hx : x ∈ Tbar τ) (hy : y ∈ Tbar τ) : x + y ∈ Tbar τ :=
  Mem.add hx hy

theorem Tbar.lt_tau {x : Ordinal.{0}} (hx : x < τ) : x ∈ Tbar τ := Mem.base (by rw [OmT_zero]; exact hx)

theorem Tbar.thb {ξ : Ordinal.{0}} {j : ℕ} (hξ : ξ ∈ Tbar τ) (hd : Dom τ j ξ) :
    thb τ ξ j ∈ Tbar τ := Mem.th (Nat.zero_le j) hd.1 hd.2 hξ

/-- `T̄^τ ⊆ Ω_ω`. -/
theorem Tbar.lt_Om_omega (hτ : Base τ) {x : Ordinal.{0}} (hx : x ∈ Tbar τ) :
    x < Om (ω : Ordinal.{0}) := by
  unfold Tbar at hx
  generalize ha : Om (ω : Ordinal.{0}) = A at hx
  generalize hi : (0 : ℕ) = i at hx
  generalize hb : (0 : Ordinal.{0}) = b at hx
  induction hx with
  | base h => rw [← ha]; exact lt_of_lt_of_le h (OmT_lt_Om_omega hτ _).le
  | small h => rw [← hb] at h; exact absurd h (not_lt.2 zero_le)
  | add _ _ ihx ihy => rw [← ha]; exact Om_omega_principal (ha ▸ ihx ha hi hb) (ha ▸ ihy ha hi hb)
  | @th a i b j ξ _ hξ hd _ _ _ =>
    rw [← ha]
    have hξω : ξ < Om (ω : Ordinal.{0}) := ha ▸ hξ
    exact (thb_lt hτ ⟨hξω, hd⟩).trans (OmT_succ_lt_Om_omega τ j)

end Googology.Trans.PoR.InaccPsi.R2.Br
