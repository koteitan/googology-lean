import Googology.Trans.PoR.InaccPsi.R2.BaseC
import Googology.Trans.PoR.InaccPsi.R2.BlockC

/-!
# The first pair of `R₂^C`: `υ_ω <₂ υ_{ω+1}` (Theorem A in `R₂^C`)

The project's Theorem A, now for `R₂^C` ([C09] Def 5.3–5.4) instead of `R₂⁺`:

* `no_pair_below` (step (d)): no `<₂`-pair of `R₂^C` has its right end below `υ_{ω+1}`.  A least
  right end `d` would have left end `υ_ω` (LEFT) and lie in the gap `(υ_ω, υ_{ω+1})`; clause 2 of
  [C09] Def 5.3 moves a `≤₁`-chain of length `htᵗ(d) + 2` (cofinal below `υ_ω`: the `υ_n`) into
  `(υ_ω, d)`, against Lemma L (`chain_bound_gap`).
* `first_pair_c1` (clause 1): copies by one base change `π_{υ_n, υ_ω}`.
* `comp_c` (**Lemma COMP-C**, the segment compression as a covering of `R₂^C`): for finite
  `X < υ_ω` and `c' ∈ [υ_ω, υ_{ω+1})` there is `c'' < υ_ω` such that every finite `Y₀ ⊆ (c'', υ_ω)`
  with `X ∪ Y₀` closed is moved, by a covering of `R₂^C` that fixes `X`, onto a closed `X ∪ Y` with
  `Y ⊆ (c', υ_{ω+1})`.  The map compresses the segments `seg(υ_k)`, `k > n + 1`, met by `Y₀` into
  `seg(υ_{n+1})` (Theorem CC-F at `υ_{n+2} ≤₁ υ_ω`, `ccf`) and then moves `seg(υ_{n+1})` up into
  `seg(υ_ω)` by `π_{υ_{n+1}, υ_ω}⁻¹`.
* `first_pair_c2` (clause 2), `first_pair` (**`υ_ω <₂ υ_{ω+1}` in `R₂^C`**).
* `thmA_C`: (A1) the pair, it is the least pair, and `υ_ω` is the only left end at `υ_{ω+1}`;
  (A2) `≤₁` of `R₂^C` is `≤₁` of `R₁⁺` for right ends `≤ υ_{ω+1}`; (A3) no `α ≤ υ_{ω+1}` is
  `≤₁` an ordinal `> υ_{ω+1}`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-! ## `υ_n`, `υ_ω`, `υ_{ω+1}` -/

theorem upsOm_U : UpsPt (upsilon ω) := upsPt_upsilon omega0_pos

theorem upsOm_next : IsNext (upsilon ω) (upsilon (succ ω)) := upsilon_isNext ω

theorem upsOm1_lt : upsilon (succ ω) < Om1 :=
  next_lt_Om1 upsOm_next (Or.inr upsOm_U) upsilon_omega_lt_Om1

theorem upsOm_T : ∀ a, a < Om1 → (a ∈ Tset (upsilon ω) ↔ a < upsilon (succ ω)) := by
  obtain ⟨m, hm, hT⟩ := exists_next upsOm_U upsilon_omega_lt_Om1
  rw [← hm.unique upsOm_next]; exact hT

theorem upsNat_strictMono : StrictMono (fun n : ℕ => upsilon (n : Ordinal.{0})) :=
  fun a b h => upsilon_normal.strictMono (by exact_mod_cast h)

theorem upsNat_lt_om (n : ℕ) : upsilon (n : Ordinal.{0}) < upsilon ω :=
  upsilon_normal.strictMono (natCast_lt_omega0 n)

theorem upsNat_U {n : ℕ} (hn : 0 < n) : UpsPt (upsilon (n : Ordinal.{0})) :=
  upsPt_upsilon (by exact_mod_cast hn)

theorem exists_upsNat {c : Ordinal.{0}} (hc : c < upsilon ω) : ∃ n : ℕ, c < upsilon n := by
  obtain ⟨x, ⟨ι, hι, rfl⟩, hcx⟩ := (lt_isLUB_iff (upsilon_limit isSuccLimit_omega0)).1 hc
  obtain ⟨n, rfl⟩ := lt_omega0.1 hι
  exact ⟨n, hcx⟩

theorem exists_upsNat_fin (S : Finset Ordinal.{0}) (hS : ∀ s ∈ S, s < upsilon ω) :
    ∃ n : ℕ, ∀ s ∈ S, s < upsilon n := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a S _ ih =>
    obtain ⟨n, hn⟩ := ih (fun s hs => hS s (Finset.mem_insert_of_mem hs))
    obtain ⟨k, hk⟩ := exists_upsNat (hS a (Finset.mem_insert_self a S))
    refine ⟨max n k, fun s hs => ?_⟩
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact lt_of_lt_of_le hk (upsNat_strictMono.monotone (le_max_right n k))
    · exact lt_of_lt_of_le (hn s hs) (upsNat_strictMono.monotone (le_max_left n k))

/-! ## Chains as patterns -/

/-- The pattern of a chain: `≤₁` is `≤`, `≤₂` is equality. -/
def chainP : Str := ⟨fun x y => x ≤ y, fun x y => x = y⟩

/-- Two increasing sequences of indecomposables: `f i ↦ g i` (`i ≤ K`) is a covering of the chain
pattern on `{f 0, …, f K}` onto `{g 0, …, g K}`, as soon as the `g i` form a `≤₁`-chain of `R`. -/
theorem cov_chain (R : Str) (K : ℕ) {f g : ℕ → Ordinal.{0}} (hf : StrictMono f)
    (hg : StrictMono g) (hfI : ∀ i, Indec (f i)) (hgI : ∀ i, Indec (g i))
    (hR1 : ∀ i j, i ≤ j → j ≤ K → R.le1 (g i) (g j)) (hR2 : ∀ x, R.le2 x x) :
    ∃ h, Cov chainP R ↑((Finset.range (K + 1)).image f) ↑((Finset.range (K + 1)).image g) h ∧
      ∀ i, h (f i) = g i := by
  classical
  let h : Ordinal.{0} → Ordinal.{0} := fun x => g (Function.invFun f x)
  have hfi : ∀ i, h (f i) = g i := fun i => by
    show g (Function.invFun f (f i)) = g i
    rw [Function.leftInverse_invFun hf.injective i]
  have mem : ∀ x ∈ (↑((Finset.range (K + 1)).image f) : Set Ordinal.{0}),
      ∃ i, i ≤ K ∧ f i = x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    exact ⟨i, Nat.lt_succ_iff.1 (Finset.mem_range.1 hi), rfl⟩
  have hmono : StrictMonoOn h ↑((Finset.range (K + 1)).image f) := by
    intro x hx y hy hxy
    obtain ⟨i, -, rfl⟩ := mem x hx
    obtain ⟨j, -, rfl⟩ := mem y hy
    rw [hfi, hfi]; exact hg (hf.lt_iff_lt.1 hxy)
  refine ⟨h, ⟨⟨⟨?_, hmono.injOn, ?_⟩, hmono, ?_⟩, ?_, ?_⟩, hfi⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := mem x hx
    rw [hfi]
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩)
  · intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    exact ⟨f i, Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, hi, rfl⟩), hfi i⟩
  · intro x hx y hy z hz
    obtain ⟨i, -, rfl⟩ := mem x hx
    obtain ⟨j, -, rfl⟩ := mem y hy
    obtain ⟨k, -, rfl⟩ := mem z hz
    rw [hfi, hfi, hfi, add_iff_indec (hfI i) (hfI j) (hfI k),
      add_iff_indec (hgI i) (hgI j) (hgI k), hf.lt_iff_lt, hg.lt_iff_lt, hf.injective.eq_iff,
      hg.injective.eq_iff]
  · intro x hx y hy hxy
    obtain ⟨i, -, rfl⟩ := mem x hx
    obtain ⟨j, hj, rfl⟩ := mem y hy
    rw [hfi, hfi]; exact hR1 i j (hf.le_iff_le.1 hxy) hj
  · intro x _ y _ hxy
    change x = y at hxy
    subst hxy; exact hR2 _

/-! ## Step (d): no `<₂`-right end below `υ_{ω+1}` -/

/-- **Step (d)** of Theorem A in `R₂^C`: no `c <₂ d` with `d < υ_{ω+1}`. -/
theorem no_pair_below : ∀ c d, c < d → d < upsilon (succ ω) → ¬ le2 c d := by
  classical
  have key : ∀ d, d < upsilon (succ ω) → ∀ c, c < d → ¬ le2 c d := by
    intro d
    induction d using WellFoundedLT.induction with
    | ind d IH =>
    intro hdβ c hcd h2
    have hd1 : d < Om1 := hdβ.trans upsOm1_lt
    have hc1 : c < Om1 := hcd.trans hd1
    have hcU : UpsPt c := left h2 hcd hc1
    have hτc : upsilon ω ≤ c := upsilon_omega_le_left h2 hcd hc1
    have hcτ : c = upsilon ω := by
      rcases eq_or_lt_of_le hτc with e | hlt
      · exact e.symm
      · exact absurd (lt_trans hcd hdβ) (not_lt.2 (upsOm_next.2.2 c hlt hcU))
    subst hcτ
    set K := ht (upsilon ω) d + 2 with hK
    let us : ℕ → Ordinal.{0} := fun i => upsilon ((i + 1 : ℕ) : Ordinal.{0})
    have hus_mono : StrictMono us := fun a b hab => upsNat_strictMono (by omega)
    have husI : ∀ i, Indec (us i) := fun i => indec_of_upsPt (upsNat_U (Nat.succ_pos i))
    have husU : ∀ i, UpsPt (us i) := fun i => upsNat_U (Nat.succ_pos i)
    have husτ : ∀ i, us i < upsilon ω := fun i => upsNat_lt_om _
    have hZc : Closed (↑((Finset.range (K + 1)).image us) : Set Ordinal.{0}) :=
      closed_of_indec (by
        intro x hx
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
        exact husI i)
    have hcof : CofCov R2C ∅ ((Finset.range (K + 1)).image us) chainP (upsilon ω) := by
      intro c' hc'
      obtain ⟨n, hn⟩ := exists_upsNat hc'
      have hgm : StrictMono (fun i => us (n + i)) := fun a b hab => hus_mono (by omega)
      obtain ⟨h, hcov, -⟩ := cov_chain R2C K hus_mono hgm husI (fun i => husI (n + i))
        (fun i j hij _ => by
          show le1 (us (n + i)) (us (n + j))
          refine (le1_iff_le1R_upsilon_omega _ (husτ _).le _).2 ?_
          exact (husU (n + i)).2 _ (hus_mono.monotone (by omega)))
        le2_refl
      refine ⟨(Finset.range (K + 1)).image (fun i => us (n + i)), ?_, ?_, h, ?_⟩
      · intro y hy
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
        refine ⟨lt_of_lt_of_le hn ?_, husτ _⟩
        exact upsNat_strictMono.monotone (by omega)
      · rw [Finset.empty_union]
        exact closed_of_indec (by
          intro x hx
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
          exact husI (n + i))
      · rw [Finset.empty_union]; exact hcov
    obtain ⟨-, -, H2⟩ := le2_iff.1 h2
    have hcofd := H2 ∅ (by simp) _ chainP hZc hcof
    obtain ⟨Y, hY, -, h, hcov⟩ := hcofd (upsilon ω) hcd
    have hmemZ : ∀ i ≤ K, us i ∈ (↑((Finset.range (K + 1)).image us) : Set Ordinal.{0}) :=
      fun i hi => Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩)
    have hzY : ∀ i ≤ K, upsilon ω < h (us i) ∧ h (us i) < d := by
      intro i hi
      have hm := hcov.1.1.mapsTo (hmemZ i hi)
      rw [Finset.coe_union, Finset.coe_empty, Set.empty_union] at hm
      exact hY _ (Finset.mem_coe.1 hm)
    have hch : ∀ i < K, h (us i) < h (us (i + 1)) ∧ le1R (h (us i)) (h (us (i + 1))) := by
      intro i hi
      refine ⟨hcov.1.2.1 (hmemZ i hi.le) (hmemZ (i + 1) hi) (hus_mono (Nat.lt_succ_self i)), ?_⟩
      have h1 : le1 (h (us i)) (h (us (i + 1))) :=
        hcov.2.1 _ (hmemZ i hi.le) _ (hmemZ (i + 1) hi) (hus_mono.monotone (Nat.le_succ i))
      exact inc1 ((hzY (i + 1) hi).2.trans hd1) h1
    have hbound := chain_bound_gap (upsPt_inE upsOm_U) upsilon_omega_lt_Om1 upsOm_T hdβ hd1 K
      (fun i => h (us i)) (hzY 0 (Nat.zero_le K)).1 (hzY K le_rfl).2.le hch
    omega
  exact fun c d hcd hdβ => key d hdβ c hcd

/-- `≤₁` of `R₂^C` is `≤₁` of `R₁⁺` for right ends `≤ υ_{ω+1}` (A2). -/
theorem le1_iff_le1R_upsOm1 : ∀ b ≤ upsilon (succ ω), ∀ a, le1 a b ↔ le1R a b :=
  le1_iff_le1R_below upsOm1_lt no_pair_below

/-- `≤₂` of `R₂^C` is equality on pairs with right end `< υ_{ω+1}`. -/
theorem le2_eq_below {c d : Ordinal.{0}} (h : le2 c d) (hd : d < upsilon (succ ω)) : c = d := by
  rcases eq_or_lt_of_le (le2_le h) with e | hlt
  · exact e
  · exact absurd h (no_pair_below c d hlt hd)

/-! ## Clause 1 -/

/-- A base `σ = υ_{n+1}` below `υ_ω` and its facts. -/
theorem base_facts (n : ℕ) :
    UpsPt (upsilon ((n + 1 : ℕ) : Ordinal.{0})) ∧
      Bases (upsilon ((n + 1 : ℕ) : Ordinal.{0})) (upsilon ω) ∧
      IsNext (upsilon ((n + 1 : ℕ) : Ordinal.{0})) (upsilon ((n + 2 : ℕ) : Ordinal.{0})) ∧
      upsilon ((n + 2 : ℕ) : Ordinal.{0}) < upsilon ω ∧ upsilon (n : Ordinal.{0}) <
        upsilon ((n + 1 : ℕ) : Ordinal.{0}) := by
  have hσU := upsNat_U (Nat.succ_pos n)
  have hnx : IsNext (upsilon ((n + 1 : ℕ) : Ordinal.{0})) (upsilon ((n + 2 : ℕ) : Ordinal.{0})) := by
    have := upsilon_isNext ((n + 1 : ℕ) : Ordinal.{0})
    rwa [succ_eq_add_one, show ((n + 1 : ℕ) : Ordinal.{0}) + 1 = ((n + 2 : ℕ) : Ordinal.{0}) by
      push_cast; rw [add_assoc]; norm_num] at this
  exact ⟨hσU, ⟨upsPt_inE hσU, upsPt_inE upsOm_U, upsNat_lt_om _, upsilon_omega_lt_Om1⟩, hnx,
    upsNat_lt_om _, upsNat_strictMono (Nat.lt_succ_self n)⟩

/-- `T^σ ∩ Ω₁ = υ_{n+2}` for `σ = υ_{n+1}`. -/
theorem base_T (n : ℕ) : ∀ a, a < Om1 →
    (a ∈ Tset (upsilon ((n + 1 : ℕ) : Ordinal.{0})) ↔ a < upsilon ((n + 2 : ℕ) : Ordinal.{0})) := by
  obtain ⟨hσU, hB, hnx, -, -⟩ := base_facts n
  obtain ⟨m, hm, hT⟩ := exists_next hσU (hB.2.2.1.trans hB.2.2.2)
  rw [← hm.unique hnx]; exact hT

/-- **Clause 1** of `υ_ω ≤₂^∞ υ_{ω+1}` ([C09] Def 5.3) in `R₂^C`, by `π_{υ_{n+1}, υ_ω}`. -/
theorem first_pair_c1 (X Y : Finset Ordinal.{0}) (hX : ∀ x ∈ X, x < upsilon ω)
    (hY : ∀ y ∈ Y, upsilon ω ≤ y ∧ y < upsilon (succ ω)) (hXY : Closed ↑(X ∪ Y)) :
    ∃ Yt : Finset Ordinal.{0}, (∀ y ∈ Yt, y < upsilon ω) ∧ (∀ x ∈ X, ∀ y ∈ Yt, x < y) ∧
      Closed ↑(X ∪ Yt) ∧ ∃ h, Cov R2C R2C ↑(X ∪ Y) ↑(X ∪ Yt) h ∧
        ∀ y ∈ Y, le1 y (upsilon (succ ω)) → le1 (h y) (upsilon ω) := by
  classical
  have hτE := upsPt_inE upsOm_U
  have hτ1 := upsilon_omega_lt_Om1
  have hYT : ∀ y ∈ Y, y ∈ Tset (upsilon ω) := fun y hy =>
    (upsOm_T y ((hY y hy).2.trans upsOm1_lt)).2 (hY y hy).2
  obtain ⟨n, hn⟩ := exists_upsNat_fin (X ∪ Y.biUnion (fun y => Par (upsilon ω) y)) (by
    intro s hs
    rcases Finset.mem_union.1 hs with hs | hs
    · exact hX s hs
    · obtain ⟨y, hy, hsy⟩ := Finset.mem_biUnion.1 hs
      exact Par_sub hτE hτ1 (hYT y hy) (Finset.mem_coe.2 hsy))
  obtain ⟨hσU, hB, -, hσ'τ, hnσ⟩ := base_facts n
  set σ := upsilon ((n + 1 : ℕ) : Ordinal.{0}) with hσdef
  have hT := base_T n
  have hXσ : ∀ x ∈ X, x < σ := fun x hx => (hn x (Finset.mem_union_left _ hx)).trans hnσ
  have hA : (↑(X ∪ Y) : Set Ordinal.{0}) ⊆ TB (upsilon ω) σ := by
    intro w hw
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hw) with hw | hw
    · exact (TB_inter_lt hB (hX w hw)).2 (hXσ w hw)
    · refine ⟨hYT w hw, fun p hp => ?_⟩
      have := hn p (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨w, hw, Finset.mem_coe.1 hp⟩))
      exact this.trans hnσ
  have hA1 : ∀ w ∈ X ∪ Y, w < upsilon (succ ω) := by
    intro w hw
    rcases Finset.mem_union.1 hw with hw | hw
    · exact (hX w hw).trans upsOm_next.1
    · exact (hY w hw).2
  let h := pi σ (upsilon ω)
  have hfix : ∀ x ∈ X, h x = x := fun x hx => pi_lt hB (hXσ x hx)
  have hiso : ArithIso ↑(X ∪ Y) (h '' ↑(X ∪ Y)) h :=
    ⟨(down_mono hB hA).injOn.bijOn_image, down_mono hB hA, down_add hB hA⟩
  have hYh : ∀ y ∈ Y, σ ≤ h y ∧ h y < upsilon ((n + 2 : ℕ) : Ordinal.{0}) := by
    intro y hy
    have hyA : y ∈ TB (upsilon ω) σ := hA (Finset.mem_coe.2 (Finset.mem_union_right _ hy))
    have hy1 : y < Om1 := (hY y hy).2.trans upsOm1_lt
    exact ⟨down_ge hB hyA (hY y hy).1,
      (hT _ (down_lt_Om1 hB hyA hy1)).1 ((pi_bijOn hB).1.mapsTo hyA)⟩
  have himg : (↑(X ∪ Y.image h) : Set Ordinal.{0}) = h '' ↑(X ∪ Y) := by
    ext w
    simp only [Set.mem_image, Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro (hw | ⟨t, ht, rfl⟩)
      · exact ⟨w, Or.inl hw, hfix w hw⟩
      · exact ⟨t, Or.inr ht, rfl⟩
    · rintro ⟨t, ht | ht, rfl⟩
      · left; rw [hfix t ht]; exact ht
      · right; exact ⟨t, ht, rfl⟩
  have hcl : Closed (h '' ↑(X ∪ Y)) :=
    closed_image_of_indec hiso hXY (fun s hs hI =>
      down_indec hB (hA hs) ((hA1 s (Finset.mem_coe.1 hs)).trans upsOm1_lt) hI)
  have himgβ : ∀ w ∈ X ∪ Y, h w < upsilon (succ ω) := by
    intro w hw
    rcases Finset.mem_union.1 hw with hw | hw
    · rw [hfix w hw]; exact (hX w hw).trans upsOm_next.1
    · exact ((hYh w hw).2.trans hσ'τ).trans upsOm_next.1
  have hcov : Cov R2C R2C ↑(X ∪ Y) (h '' ↑(X ∪ Y)) h := by
    refine ⟨hiso, ?_, ?_⟩
    · intro c hc d hd hcd
      change le1 c d at hcd
      change le1 (h c) (h d)
      have hR := (le1_iff_le1R_upsOm1 d (hA1 d hd).le c).1 hcd
      have hR' := (down_le1R hσU upsOm_U hB (hA hc) (hA hd)
        ((hA1 c hc).trans upsOm1_lt)).1 hR
      exact (le1_iff_le1R_upsOm1 _ (himgβ d hd).le _).2 hR'
    · intro c _ d hd hcd
      change le2 c d at hcd
      change le2 (h c) (h d)
      rw [le2_eq_below hcd (hA1 d hd)]; exact le2_refl _
  refine ⟨Y.image h, ?_, ?_, ?_, h, ?_, ?_⟩
  · intro y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    exact (hYh t ht).2.trans hσ'τ
  · intro x hx y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    exact lt_of_lt_of_le (hXσ x hx) (hYh t ht).1
  · rw [himg]; exact hcl
  · rw [himg]; exact hcov
  · intro y hy hyβ
    have hR := inc1 upsOm1_lt hyβ
    rcases eq_or_lt_of_le (hY y hy).1 with e | hlt
    · rw [← e]
      show le1 (pi σ (upsilon ω) (upsilon ω)) (upsilon ω)
      rw [(pi_base hB).2]
      exact (le1_iff_le1R_upsilon_omega _ le_rfl _).2 (hσU.2 _ hB.2.2.1.le)
    · exact absurd hR (not_le1R_gap upsOm_next hlt (hY y hy).2 le_rfl)

/-! ## Lemma COMP-C and clause 2 -/

/-- **Lemma COMP-C** (segment compression, a covering of `R₂^C`). -/
theorem comp_c (X : Finset Ordinal.{0}) (hX : ∀ x ∈ X, x < upsilon ω) {c' : Ordinal.{0}}
    (hc1 : upsilon ω ≤ c') (hc2 : c' < upsilon (succ ω)) :
    ∃ c'' < upsilon ω, ∀ Y0 : Finset Ordinal.{0}, (∀ y ∈ Y0, c'' < y ∧ y < upsilon ω) →
      Closed ↑(X ∪ Y0) → ∃ Y : Finset Ordinal.{0}, (∀ y ∈ Y, c' < y ∧ y < upsilon (succ ω)) ∧
        Closed ↑(X ∪ Y) ∧ ∃ g, Cov R2C R2C ↑(X ∪ Y0) ↑(X ∪ Y) g ∧ ∀ x ∈ X, g x = x := by
  classical
  have hτE := upsPt_inE upsOm_U
  have hτ1 := upsilon_omega_lt_Om1
  have hcT : c' ∈ Tset (upsilon ω) := (upsOm_T c' (hc2.trans upsOm1_lt)).2 hc2
  obtain ⟨n, hn⟩ := exists_upsNat_fin (X ∪ Par (upsilon ω) c') (by
    intro s hs
    rcases Finset.mem_union.1 hs with hs | hs
    · exact hX s hs
    · exact Par_sub hτE hτ1 hcT (Finset.mem_coe.2 hs))
  obtain ⟨hσU, hB, hnx, hσ'τ, hnσ⟩ := base_facts n
  set σ := upsilon ((n + 1 : ℕ) : Ordinal.{0}) with hσdef
  set σ' := upsilon ((n + 2 : ℕ) : Ordinal.{0}) with hσ'def
  have hT := base_T n
  have hσ'1 : σ' < Om1 := hσ'τ.trans hτ1
  have hσ'U : UpsPt σ' := hnx.2.1
  have hXσ : ∀ x ∈ X, x < σ := fun x hx => (hn x (Finset.mem_union_left _ hx)).trans hnσ
  have hcTB : c' ∈ TB (upsilon ω) σ := ⟨hcT, fun p hp =>
    (hn p (Finset.mem_union_right _ (Finset.mem_coe.1 hp))).trans hnσ⟩
  set ct := pi σ (upsilon ω) c' with hctdef
  have hctσ : σ ≤ ct := down_ge hB hcTB hc1
  have hct1 : ct < Om1 := down_lt_Om1 hB hcTB (hc2.trans upsOm1_lt)
  have hctT : ct ∈ Tset σ := (pi_bijOn hB).1.mapsTo hcTB
  have hctσ' : ct < σ' := (hT ct hct1).1 hctT
  refine ⟨ct, hctσ'.trans hσ'τ, fun Y0 hY0 hXY0 => ?_⟩
  -- the split of `Y₀` at `σ'`
  set Y2 := Y0.filter (· < σ') with hY2
  set Y3 := Y0.filter (fun y => ¬ y < σ') with hY3
  obtain ⟨X', hsub, hX'C, hX'b⟩ := exists_closed (insert 0 (insert ct (X ∪ Y2)))
  have hX'lt : ∀ x ∈ X', x < σ' := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := hX'b x hx
    refine lt_of_le_of_lt hxs ?_
    simp only [Finset.mem_insert, Finset.mem_union] at hs
    rcases hs with rfl | rfl | hs | hs
    · exact hσ'U.1
    · exact hctσ'
    · exact (hXσ s hs).trans (hnx.1)
    · exact (Finset.mem_filter.1 hs).2
  have hXX' : ∀ x ∈ X, x ∈ X' := fun x hx => hsub (by simp [hx])
  have hY2X' : ∀ y ∈ Y2, y ∈ X' := fun y hy => hsub (by simp [hy])
  have h0X' : (0 : Ordinal.{0}) ∈ X' := hsub (by simp)
  have hctX' : ct ∈ X' := hsub (by simp)
  have hY3 : ∀ y ∈ Y3, σ' ≤ y ∧ y < upsilon ω := by
    intro y hy
    obtain ⟨hy0, hyσ⟩ := Finset.mem_filter.1 hy
    exact ⟨not_lt.1 hyσ, (hY0 y hy0).2⟩
  have hD : (↑(X ∪ Y0) : Set Ordinal.{0}) ⊆ ↑(X' ∪ Y3) := by
    intro w hw
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hw ⊢
    rcases hw with hw | hw
    · exact Or.inl (hXX' w hw)
    · by_cases hwσ : w < σ'
      · exact Or.inl (hY2X' w (Finset.mem_filter.2 ⟨hw, hwσ⟩))
      · exact Or.inr (Finset.mem_filter.2 ⟨hw, hwσ⟩)
  have hX'Y3 : Closed ↑(X' ∪ Y3) := by
    have he : (↑(X' ∪ Y3) : Set Ordinal.{0}) = ↑X' ∪ ↑(X ∪ Y0) := by
      ext w
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
      constructor
      · rintro (hw | hw)
        · exact Or.inl hw
        · exact Or.inr (Or.inr (Finset.mem_filter.1 hw).1)
      · rintro (hw | hw | hw)
        · exact Or.inl hw
        · exact Or.inl (hXX' w hw)
        · by_cases hwσ : w < σ'
          · exact Or.inl (hY2X' w (Finset.mem_filter.2 ⟨hw, hwσ⟩))
          · exact Or.inr (Finset.mem_filter.2 ⟨hw, hwσ⟩)
    rw [he]; exact hX'C.union hXY0
  -- Theorem CC-F at `σ' ≤₁ υ_ω`
  obtain ⟨ψ, hψ, hψc, hψfix, hYψ, hψR⟩ :=
    ccf (hσ'U.2 _ hσ'τ.le) X' Y3 hX'lt hY3 h0X' hX'Y3
  have hψD : ∀ w ∈ (↑(X ∪ Y0) : Set Ordinal.{0}), ψ w < σ' := by
    intro w hw
    rcases Finset.mem_union.1 (Finset.mem_coe.1 (hD hw)) with h' | h'
    · rw [hψfix w h']; exact hX'lt w h'
    · exact (hYψ w h').2
  have hψT : ∀ w ∈ (↑(X ∪ Y0) : Set Ordinal.{0}), ψ w ∈ Tset σ ∧ ψ w < Om1 := fun w hw =>
    ⟨(hT _ ((hψD w hw).trans hσ'1)).2 (hψD w hw), (hψD w hw).trans hσ'1⟩
  have hψY0 : ∀ y ∈ Y0, ct < ψ y := by
    intro y hy
    by_cases hyσ : y < σ'
    · rw [hψfix y (hY2X' y (Finset.mem_filter.2 ⟨hy, hyσ⟩))]; exact (hY0 y hy).1
    · exact (hYψ y (Finset.mem_filter.2 ⟨hy, hyσ⟩)).1 ct hctX'
  -- the map `g = π⁻¹ ∘ ψ`
  set W := ψ '' ↑(X ∪ Y0) with hWdef
  have hWT : W ⊆ Tset σ := by rintro _ ⟨w, hw, rfl⟩; exact (hψT w hw).1
  have hψisoD : ArithIso ↑(X ∪ Y0) W ψ :=
    ⟨(hψ.2.1.mono hD).injOn.bijOn_image, hψ.2.1.mono hD,
      fun x hx y hy z hz => hψ.2.2 x (hD hx) y (hD hy) z (hD hz)⟩
  have hWc : Closed W := closed_image hψ hψc hD hXY0
  have hupiso : ArithIso W (up σ (upsilon ω) '' W) (up σ (upsilon ω)) :=
    ⟨(up_mono hB hWT).injOn.bijOn_image, up_mono hB hWT, up_add hB hWT⟩
  set g := up σ (upsilon ω) ∘ ψ with hgdef
  have hgimg : g '' ↑(X ∪ Y0) = up σ (upsilon ω) '' W := by rw [hgdef, Set.image_comp]
  have hgiso : ArithIso ↑(X ∪ Y0) (g '' ↑(X ∪ Y0)) g := by
    rw [hgimg]; exact hψisoD.comp hupiso
  have hgcl : Closed (g '' ↑(X ∪ Y0)) := by
    rw [hgimg]
    refine closed_image_of_indec hupiso hWc ?_
    rintro _ ⟨w, hw, rfl⟩ hI
    exact up_indec hB (hψT w hw).1 (hψT w hw).2 hI
  have hgfix : ∀ x ∈ X, g x = x := by
    intro x hx
    show up σ (upsilon ω) (ψ x) = x
    rw [hψfix x (hXX' x hx), up_lt hB (hXσ x hx)]
  have hgβ : ∀ w ∈ (↑(X ∪ Y0) : Set Ordinal.{0}), g w < upsilon (succ ω) := by
    intro w hw
    obtain ⟨hwT, hw1⟩ := hψT w hw
    have hu := (up_spec hB hwT).1
    exact (upsOm_T _ (up_lt_Om1 hB hwT hw1)).1 hu.1
  have hgY0 : ∀ y ∈ Y0, c' < g y := by
    intro y hy
    have hyD : y ∈ (↑(X ∪ Y0) : Set Ordinal.{0}) := by simp [hy]
    have := up_mono hB (S := {ct, ψ y}) (by
      intro w hw
      rcases hw with rfl | hw
      · exact hctT
      · rw [Set.mem_singleton_iff.1 hw]; exact (hψT y hyD).1) (by simp) (by simp) (hψY0 y hy)
    rwa [hctdef, up_pi hB hcTB] at this
  have hτβ : upsilon ω < upsilon (succ ω) := upsOm_next.1
  have hD1 : ∀ w ∈ (↑(X ∪ Y0) : Set Ordinal.{0}), w < upsilon ω := by
    intro w hw
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hw) with hw | hw
    · exact hX w hw
    · exact (hY0 w hw).2
  have hgcov : Cov R2C R2C ↑(X ∪ Y0) (g '' ↑(X ∪ Y0)) g := by
    refine ⟨hgiso, ?_, ?_⟩
    · intro c hc d hd hcd
      change le1 c d at hcd
      change le1 (g c) (g d)
      have hR := (le1_iff_le1R_upsilon_omega d (hD1 d hd).le c).1 hcd
      have hR' := hψR c (Finset.mem_coe.1 (hD hc)) d (Finset.mem_coe.1 (hD hd)) hR
      have hR'' := (up_le1R hσU upsOm_U hB (hψT c hc).1 (hψT d hd).1 (hψT c hc).2).1 hR'
      exact (le1_iff_le1R_upsOm1 _ (hgβ d hd).le _).2 hR''
    · intro c _ d hd hcd
      change le2 c d at hcd
      change le2 (g c) (g d)
      rw [le2_eq_below hcd ((hD1 d hd).trans hτβ)]; exact le2_refl _
  have himg : (↑(X ∪ Y0.image g) : Set Ordinal.{0}) = g '' ↑(X ∪ Y0) := by
    ext w
    simp only [Set.mem_image, Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro (hw | ⟨t, ht, rfl⟩)
      · exact ⟨w, Or.inl hw, hgfix w hw⟩
      · exact ⟨t, Or.inr ht, rfl⟩
    · rintro ⟨t, ht | ht, rfl⟩
      · left; rw [hgfix t ht]; exact ht
      · right; exact ⟨t, ht, rfl⟩
  refine ⟨Y0.image g, ?_, ?_, g, ?_, hgfix⟩
  · intro y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨hgY0 t ht, hgβ t (by simp [ht])⟩
  · rw [himg]; exact hgcl
  · rw [himg]; exact hgcov

/-- **Clause 2** of `υ_ω ≤₂^∞ υ_{ω+1}` ([C09] Def 5.3) in `R₂^C`. -/
theorem first_pair_c2 (X : Finset Ordinal.{0}) (hX : ∀ x ∈ X, x < upsilon ω)
    (Z : Finset Ordinal.{0}) (P : Str) (_hZ : Closed ↑Z)
    (hC : CofCov R2C X Z P (upsilon ω)) : CofCov R2C X Z P (upsilon (succ ω)) := by
  intro c' hc'
  rcases lt_or_ge c' (upsilon ω) with hlt | hge
  · obtain ⟨Y, hY, hcl, h, hcov⟩ := hC c' hlt
    exact ⟨Y, fun y hy => ⟨(hY y hy).1, (hY y hy).2.trans upsOm_next.1⟩, hcl, h, hcov⟩
  · obtain ⟨c'', hc''τ, H⟩ := comp_c X hX hge hc'
    obtain ⟨Y0, hY0, hcl0, h0, hcov0⟩ := hC c'' hc''τ
    obtain ⟨Y, hY, hcl, g, hg, -⟩ := H Y0 hY0 hcl0
    exact ⟨Y, hY, hcl, g ∘ h0, hcov0.comp hg⟩

/-- **The first pair** of `R₂^C`: `υ_ω <₂ υ_{ω+1}`. -/
theorem first_pair : le2 (upsilon ω) (upsilon (succ ω)) :=
  le2_iff.2 ⟨upsOm_next.1.le, fun X Y hX hY hXY => first_pair_c1 X Y hX hY hXY,
    fun X hX Z P hZ hC => first_pair_c2 X hX Z P hZ hC⟩

/-- (A3) No `α ≤ υ_{ω+1}` is `≤₁` an ordinal `> υ_{ω+1}` in `R₂^C`. -/
theorem not_le1_above {a g : Ordinal.{0}} (ha : a ≤ upsilon (succ ω))
    (hg : upsilon (succ ω) < g) : ¬ le1 a g := by
  classical
  intro h
  obtain ⟨-, H⟩ := le1_iff.1 h
  have hτβ : upsilon ω < upsilon (succ ω) := upsOm_next.1
  have hτI := indec_of_upsPt upsOm_U
  have hβI := indec_of_upsPt upsOm_next.2.1
  rcases le_or_gt a (upsilon ω) with haτ | hτa
  · obtain ⟨Yt, hYt, -, -, f, hf⟩ := H ∅ {upsilon ω, upsilon (succ ω)} (by simp)
      (by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact ⟨haτ, hτβ.trans hg⟩
        · exact ⟨ha, hg⟩)
      (closed_of_indec (by
        intro x hx
        simp only [Finset.coe_union, Finset.coe_empty, Set.empty_union, Finset.coe_insert,
          Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact hτI
        · exact hβI))
    have hτm : upsilon ω ∈ (↑((∅ : Finset Ordinal.{0}) ∪ {upsilon ω, upsilon (succ ω)} :
        Finset Ordinal.{0}) : Set Ordinal.{0}) := by simp
    have hβm : upsilon (succ ω) ∈ (↑((∅ : Finset Ordinal.{0}) ∪ {upsilon ω, upsilon (succ ω)} :
        Finset Ordinal.{0}) : Set Ordinal.{0}) := by simp
    have h2 : le2 (f (upsilon ω)) (f (upsilon (succ ω))) := hf.2.2 _ hτm _ hβm first_pair
    have hlt : f (upsilon ω) < f (upsilon (succ ω)) := hf.1.2.1 hτm hβm hτβ
    have hfβ := hf.1.1.mapsTo hβm
    rw [Finset.coe_union, Finset.coe_empty, Set.empty_union] at hfβ
    have hfβa := hYt _ (Finset.mem_coe.1 hfβ)
    exact no_pair_below _ _ hlt (lt_of_lt_of_le hfβa (haτ.trans hτβ.le)) h2
  · have hXc : Closed (↑({upsilon ω} ∪ {upsilon (succ ω)} : Finset Ordinal.{0}) :
        Set Ordinal.{0}) := closed_of_indec (by
      intro x hx
      simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union,
        Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hτI
      · exact hβI)
    obtain ⟨Yt, hYt, hXYt, -, f, hf⟩ := H {upsilon ω} {upsilon (succ ω)} (by simpa using hτa)
      (by simpa using ⟨ha, hg⟩) hXc
    have hτm : upsilon ω ∈ (↑({upsilon ω} ∪ {upsilon (succ ω)} : Finset Ordinal.{0}) :
        Set Ordinal.{0}) := by simp
    have hβm : upsilon (succ ω) ∈ (↑({upsilon ω} ∪ {upsilon (succ ω)} : Finset Ordinal.{0}) :
        Set Ordinal.{0}) := by simp
    have hfτ : f (upsilon ω) = upsilon ω := by
      refine fix_initial hf.1.1 hf.1.2.1 (S := {upsilon ω}) (by simp) (by simp) ?_ ?_ _ rfl
      · intro x hx hxn s hs
        rw [Set.mem_singleton_iff.1 hs]
        simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union,
          Set.mem_singleton_iff] at hx hxn
        rcases hx with rfl | rfl
        · exact absurd rfl hxn
        · exact hτβ
      · intro x hx hxn s hs
        rw [Set.mem_singleton_iff.1 hs]
        simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union, Finset.mem_coe,
          Set.mem_singleton_iff] at hx hxn
        rcases hx with rfl | hx
        · exact absurd rfl hxn
        · exact hXYt _ (Finset.mem_singleton_self _) _ hx
    have h2 : le2 (f (upsilon ω)) (f (upsilon (succ ω))) := hf.2.2 _ hτm _ hβm first_pair
    have hlt : f (upsilon ω) < f (upsilon (succ ω)) := hf.1.2.1 hτm hβm hτβ
    have hfβ := hf.1.1.mapsTo hβm
    simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union, Finset.mem_coe,
      Set.mem_singleton_iff] at hfβ
    rw [hfτ] at h2 hlt
    rcases hfβ with e | hfβ
    · rw [e] at hlt; exact absurd hlt (lt_irrefl _)
    · exact no_pair_below _ _ hlt (lt_of_lt_of_le (hYt _ hfβ) ha) h2

/-- **Theorem A in `R₂^C`.** (A1) `υ_ω <₂ υ_{ω+1}`; no `<₂`-pair has its right end below `υ_{ω+1}`;
`υ_ω` is the only `<₂`-predecessor of `υ_{ω+1}`.  (A2) For right ends `≤ υ_{ω+1}`, `≤₁` of `R₂^C`
is `≤₁` of `R₁⁺`.  (A3) No `α ≤ υ_{ω+1}` is `≤₁` an ordinal `> υ_{ω+1}`. -/
theorem thmA_C :
    (le2 (upsilon ω) (upsilon (succ ω)) ∧
      (∀ c d, c < d → d < upsilon (succ ω) → ¬ le2 c d) ∧
      (∀ c, c < upsilon (succ ω) → le2 c (upsilon (succ ω)) → c = upsilon ω)) ∧
    (∀ b ≤ upsilon (succ ω), ∀ a, le1 a b ↔ le1R a b) ∧
    (∀ a g, a ≤ upsilon (succ ω) → upsilon (succ ω) < g → ¬ le1 a g) := by
  refine ⟨⟨first_pair, no_pair_below, fun c hc h2 => ?_⟩, le1_iff_le1R_upsOm1,
    fun a g ha hg => not_le1_above ha hg⟩
  have hc1 : c < Om1 := hc.trans upsOm1_lt
  have hcU := left h2 hc hc1
  rcases eq_or_lt_of_le (upsilon_omega_le_left h2 hc hc1) with e | hlt
  · exact e.symm
  · exact absurd hc (not_lt.2 (upsOm_next.2.2 c hlt hcU))

end Googology.Trans.PoR.InaccPsi.R2
