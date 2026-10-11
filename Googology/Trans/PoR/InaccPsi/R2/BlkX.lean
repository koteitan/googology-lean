import Googology.Trans.PoR.InaccPsi.R2.Off

/-!
# Theorems BLK^Ξ / BLK^O in `R₂^C`, part 1: the block structure and Lemma TOP_λ (FRAG-free)

The project's block theorem by transfinite induction on the restart index, for any offset function
`O` that satisfies an offset specification `OffSpec O B` (`Off`: `c*` up to `Ξ_ω`, `specXi`;
`OffPhi`: the offsets below `Φ_1`).  `Good O l` collects what is known about `[0, υ_l)` (`l = 0` or a
multiple of `ω²`):

* `below`: no point below `υ_l` is `≤₁` a point `≥ υ_l`;
* `land`: landing blocks (a `υ`-point `σ` and its successor `σ'` with `≤₁` of `R₁⁺` and no pair in
  between) cofinal below `υ_l`;
* `caps` (BLOCKTOP with the reaches): if `c <₂ d`, `d < υ_l`, `x ≤ c` and `x ≤₁ g`, then `g ≤ d`, or
  `x = ρ_μ` is a restart with `δ_μ ≤ d` and `g ≤ δ_μ + O(μ)`;
* `pairs` (BLK (i)): the `<₂`-pairs below `υ_l` are exactly `(υ_{μ+ω(j+1)}, υ_{μ+ω(j+1)+1})`,
  `μ = 0` or a restart index, `μ < l`;
* `sk` (BLK (iii), skeletal): a point below `υ_l` that is not a `υ`-point has its `R₁⁺` reach;
* `rst` (BLK (ii), upper end): every restart `μ < l` has a restart context (`RstK`), Lemma TOP
  (`ρ_μ` is not `≤₁` any `γ > δ_μ + O(μ)`), and the chain of block contexts after `δ_μ + O(μ)`.

Steps: `good_zero`; `good_first` (the blocks of Theorem B, base `0`); `good_step` (a restart `λ`:
`RstK` from `Good O λ`, Lemma TOP from `RstK.top_gen` with the input `TopIn O λ` and the caps, (T3) at
`δ_λ + O(λ)`, the chain of blocks after it); `good_limit` (union).  `OffSpec`, `good_all`, `good_B`:
`Good O (ω²·η)` for every `ω²·η ≤ B`.  `specXi`: `c*` is an offset specification up to `Ξ_ω + ω²`.
Nothing here uses FRAG.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-! ## Index arithmetic -/

theorem w_add_ww : (ω : Ordinal.{0}) + ω * ω = ω * ω := add_eq_right_iff_mul_omega0_le.2 le_rfl

theorem w_mul_succ' (k : ℕ) : ω * ((k + 1 : ℕ) : Ordinal.{0}) = ω + ω * (k : Ordinal.{0}) := by
  rw [show ((k + 1 : ℕ) : Ordinal.{0}) = ((1 + k : ℕ) : Ordinal.{0}) by rw [Nat.add_comm]]
  push_cast; rw [mul_add, mul_one]

/-- The left end of the chain pair `k` after the restart `l` is `υ_{l+ω(k+2)}`. -/
theorem idx_chain (l : Ordinal.{0}) (k : ℕ) :
    l + ω * ((k + 1 + 1 : ℕ) : Ordinal.{0}) = l + ω + ω * (k : Ordinal.{0}) + ω := by
  rw [omega_mul_succ (k + 1), w_mul_succ' k]; simp only [add_assoc]

theorem idx_zero (k : ℕ) : (0 : Ordinal.{0}) + ω * ((k + 1 : ℕ) : Ordinal.{0}) =
    0 + ω * (k : Ordinal.{0}) + ω := by
  rw [omega_mul_succ k, add_assoc]

theorem idx_one (l : Ordinal.{0}) : l + ω * ((0 + 1 : ℕ) : Ordinal.{0}) = l + ω := by simp

theorem idx_lt (l : Ordinal.{0}) (j n : ℕ) : l + ω + ω * (j : Ordinal.{0}) + n < l + ω * ω := by
  rw [add_assoc, add_assoc]
  refine (add_lt_add_iff_left l).2 ?_
  rw [← add_assoc, ← w_mul_succ']
  have h1 : ω * ((j + 1 : ℕ) : Ordinal.{0}) + n < ω * ((j + 1 : ℕ) : Ordinal.{0}) + ω :=
    (add_lt_add_iff_left _).2 (natCast_lt_omega0 n)
  rw [← omega_mul_succ] at h1
  exact h1.trans ((mul_lt_mul_iff_right₀ omega0_pos).2 (natCast_lt_omega0 _))

theorem pidx_lt (μ : Ordinal.{0}) (j : ℕ) : μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 < μ + ω * ω := by
  rw [add_assoc]
  refine (add_lt_add_iff_left μ).2 ?_
  have h1 : ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 < ω * ((j + 1 : ℕ) : Ordinal.{0}) + ω :=
    (add_lt_add_iff_left _).2 one_lt_omega0
  rw [← omega_mul_succ] at h1
  exact h1.trans ((mul_lt_mul_iff_right₀ omega0_pos).2 (natCast_lt_omega0 _))

/-- Between two multiples of `ω²` there is a gap of `ω²`. -/
theorem next_mult {l μ : Ordinal.{0}} (hl : ω * ω ∣ l) (hμ : ω * ω ∣ μ) (h : l < μ) :
    l + ω * ω ≤ μ := by
  obtain ⟨p, rfl⟩ := hl
  obtain ⟨q, rfl⟩ := hμ
  have hpq : p < q := (mul_lt_mul_iff_right₀ (mul_pos omega0_pos omega0_pos)).1 h
  rw [← mul_add_one]
  exact mul_le_mul_right (add_one_le_of_lt hpq) _

theorem mult_of {μ : Ordinal.{0}} (hμ : μ = 0 ∨ IsRestartIdx μ) : ω * ω ∣ μ := by
  rcases hμ with rfl | h
  · exact dvd_zero _
  · exact (ri_iff.1 h).2

theorem ri_ge {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) : ω * ω ≤ μ :=
  le_of_dvd hμ.1 (ri_iff.1 hμ).2

/-- A point of `(δ, δ + o]` (`o < δ`) is decomposable. -/
theorem decomp_mid {δ o α : Ordinal.{0}} (hoδ : o < δ) (h1 : δ < α) (h2 : α ≤ δ + o) :
    ¬ Indec α := by
  have he : δ + (α - δ) = α := Ordinal.add_sub_cancel_of_le h1.le
  have hξ0 : 0 < α - δ := by
    rcases eq_or_ne (α - δ) 0 with e | e
    · rw [e, add_zero] at he; exact absurd he (ne_of_lt h1)
    · exact pos_iff_ne_zero.2 e
  have hξo : α - δ ≤ o := by
    rw [← he] at h2; exact (add_le_add_iff_left δ).1 h2
  intro hI
  apply hI
  refine Or.inr ⟨δ, α - δ, ?_, ?_, he⟩
  · rw [← he]; exact lt_add_of_pos_right δ hξ0
  · exact lt_of_le_of_lt hξo (lt_of_lt_of_le hoδ h1.le)

/-- A decomposable point has only itself as `≤₁`-successor, in `R₂^C` and in `R₁⁺`. -/
theorem sk_decomp {α : Ordinal.{0}} (hα : ¬ Indec α) : ∀ γ, le1 α γ ↔ le1R α γ := by
  intro γ
  rcases lt_trichotomy γ α with hγ | rfl | hγ
  · exact ⟨fun h => absurd (le1_le h) (not_le.2 hγ), fun h => absurd (le1R_le h) (not_le.2 hγ)⟩
  · exact ⟨fun _ => le1R_refl _, fun _ => le1_refl _⟩
  · exact ⟨fun h => absurd (indec_of_lt1 h hγ) hα, fun h => absurd (indec_of_lt1R h hγ) hα⟩

/-! ## The chain region -/

section ChainRegion

variable {a T0 : Ordinal.{0}} (C : ∀ j : ℕ, BlkCtx (topA a T0 j) (lpA a j) (topA a T0 (j + 1)))
include C

/-- A pair above `T₀` in a chain is a chain pair, and its right end is closed. -/
theorem chain_pair (hTa : upsilon a ≤ T0) {c d : Ordinal.{0}} (hT0d : T0 < d)
    (hd : d < upsilon (a + ω * ω)) (hcd : c < d) (h2 : le2 c d) :
    ∃ k : ℕ, c = lpA a k ∧ d = topA a T0 (k + 1) ∧ ∀ x ≤ d, ∀ g, le1 x g → g ≤ d := by
  rcases chainA_sup hTa hd with hdT | ⟨j, hdj⟩
  · exact absurd hT0d (not_lt.2 hdT)
  obtain ⟨k, -, rfl, rfl⟩ := chainA_pairs C (j + 1) c d hcd hT0d hdj h2
  exact ⟨k, rfl, rfl, fun x hx g hg => not_lt.1 (fun hlt => (C (k + 1)).T3 x hx g hlt hg)⟩

/-- Skeletal in the chain region. -/
theorem chain_sk (hTa : upsilon a ≤ T0) {α : Ordinal.{0}} (hTα : T0 < α)
    (hα : α < upsilon (a + ω * ω)) (hnu : ¬ UpsPt α) : ∀ γ, le1 α γ ↔ le1R α γ := by
  classical
  have hex : ∃ j, α ≤ topA a T0 j := by
    rcases chainA_sup hTa hα with hαT | ⟨j, hαj⟩
    · exact absurd hTα (not_lt.2 hαT)
    · exact ⟨j + 1, hαj⟩
  set j := Nat.find hex with hj
  have hαj : α ≤ topA a T0 j := Nat.find_spec hex
  rcases j with _ | j
  · exact absurd hTα (not_lt.2 hαj)
  have hTj : topA a T0 j < α := not_le.1 (Nat.find_min hex (show j < Nat.find hex by omega))
  have H := C j
  exact skel_block H.next.2.1 H.β1 hTj hαj hnu H.le1_lowβ

end ChainRegion

/-! ## What is known below `υ_l` -/

/-- The block structure of `[0, υ_l)` (see the module docstring). -/
structure Good (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Prop where
  below : ∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g
  land : 0 < l → ∀ c' < upsilon l, ∃ σ σ', UpsPt σ ∧ c' < σ ∧ IsNext σ σ' ∧ σ' < upsilon l ∧
    (∀ a b, σ < a → b < σ' → (le1 a b ↔ le1R a b)) ∧ (∀ b, σ ≤ b → b < σ' → le1 σ b) ∧
    (∀ c d, c < d → σ < d → d < σ' → ¬ le2 c d)
  caps : ∀ c d, c < d → d < upsilon l → le2 c d → ∀ x ≤ c, ∀ g, le1 x g →
    g ≤ d ∨ ∃ μ, IsRestartIdx μ ∧ μ < l ∧ x = upsilon μ ∧ upsilon (μ + ω + 1) ≤ d ∧
      g ≤ upsilon (μ + ω + 1) + O μ
  pairs : ∀ c d, c < d → d < upsilon l → (le2 c d ↔ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧
      μ < l ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))
  sk : ∀ α < upsilon l, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ
  rst : ∀ μ, IsRestartIdx μ → μ < l →
    RstK (upsilon μ) (upsilon (μ + ω)) (upsilon (μ + ω + 1)) ∧
    (∀ g, upsilon (μ + ω + 1) + O μ < g → ¬ le1 (upsilon μ) g) ∧
    (∀ j : ℕ, BlkCtx (topA (μ + ω) (upsilon (μ + ω + 1) + O μ) j) (lpA (μ + ω) j)
      (topA (μ + ω) (upsilon (μ + ω + 1) + O μ) (j + 1)))

theorem good_zero (O : Ordinal.{0} → Ordinal.{0}) : Good O 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc; rw [upsilon_zero] at hc; exact absurd hc (not_lt.2 zero_le)
  · intro h; exact absurd h (lt_irrefl 0)
  · intro c d _ hd; rw [upsilon_zero] at hd; exact absurd hd (not_lt.2 zero_le)
  · intro c d _ hd; rw [upsilon_zero] at hd; exact absurd hd (not_lt.2 zero_le)
  · intro α hα; rw [upsilon_zero] at hα; exact absurd hα (not_lt.2 zero_le)
  · intro μ _ hμ; exact absurd hμ (not_lt.2 zero_le)

theorem T3_zero : ∀ c ≤ (0 : Ordinal.{0}), ∀ g, (0 : Ordinal.{0}) < g → ¬ le1 c g :=
  fun c hc g hg => by rw [le_antisymm hc zero_le]; exact not_le1_zero hg

/-- The first step: the blocks of Theorem B (base index `0`, lower end `0`). -/
theorem good_first (O : Ordinal.{0} → Ordinal.{0}) : Good O (0 + ω * ω) := by
  have C := ctx0
  have hTa : upsilon 0 ≤ (0 : Ordinal.{0}) := by rw [upsilon_zero]
  refine ⟨chainA_below C T3_zero hTa, fun _ => chainA_land C hTa, ?_, ?_, ?_, ?_⟩
  · intro c d hcd hd h2 x hx g hg
    obtain ⟨k, -, -, hcap⟩ := chain_pair C hTa (lt_of_le_of_lt zero_le hcd) hd hcd h2
    exact Or.inl (hcap x (hx.trans hcd.le) g hg)
  · intro c d hcd hd
    constructor
    · intro h2
      obtain ⟨k, rfl, rfl, -⟩ := chain_pair C hTa (lt_of_le_of_lt zero_le hcd) hd hcd h2
      refine ⟨0, k, Or.inl rfl, by simp [mul_pos omega0_pos omega0_pos], ?_, ?_⟩
      · show upsilon (0 + ω * (k : Ordinal.{0}) + ω) = _
        rw [idx_zero]
      · show upsilon (0 + ω * (k : Ordinal.{0}) + ω + 1) = _
        rw [idx_zero]
    · rintro ⟨μ, j, hμ, hμl, rfl, rfl⟩
      rcases hμ with rfl | hμ
      · have := (C j).pair
        simp only [lpA, topA] at this
        rw [idx_zero]; exact this
      · exact absurd (ri_ge hμ) (not_le.2 (by simpa using hμl))
  · intro α hα hnu γ
    rcases eq_or_ne α 0 with rfl | hα0
    · constructor
      · intro h
        rcases eq_or_lt_of_le (le1_le h) with e | hlt
        · rw [← e]; exact le1R_refl 0
        · exact absurd h (not_le1_zero hlt)
      · intro h
        rcases eq_or_lt_of_le (le1R_le h) with e | hlt
        · rw [← e]; exact le1_refl 0
        · exact absurd (le1R_lim_P h hlt).1 (lt_irrefl 0)
    · exact chain_sk C hTa (pos_iff_ne_zero.2 hα0) hα hnu γ
  · intro μ hμ hμl
    exact absurd (ri_ge hμ) (not_le.2 (by simpa using hμl))

/-! ## The step at a restart -/

/-- The restart context of `ρ_λ` from what is known below it. -/
theorem rstK_of_good {O : Ordinal.{0} → Ordinal.{0}} {l : Ordinal.{0}} (hl : IsRestartIdx l) (G : Good O l)
    (hc : upsilon (l + ω + 1) < Om1) :
    RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hlim : IsSuccLimit (l + ω) := isSuccLimit_add _ isSuccLimit_omega0
  refine ⟨upsPt_upsilon hl0, upsilon_normal.strictMono (lt_add_of_pos_right l omega0_pos),
    upsPt_upsilon (lt_of_lt_of_le hl0 le_self_add), ?_, hc, G.below, G.land hl0, ?_, ?_⟩
  · have := upsilon_isNext (l + ω); rwa [succ_eq_add_one] at this
  · intro l' hl' hρl hlτ
    have h1 : l < l' := upsilon_normal.strictMono.lt_iff_lt.1 hρl
    have h2 : l' ≤ l + ω := upsilon_normal.strictMono.le_iff_le.1 hlτ
    rw [limit_eq_add_omega hl' h1 h2]
  · intro c' hc'
    obtain ⟨_, ⟨ι, hι, rfl⟩, hcx⟩ := (lt_isLUB_iff (upsilon_limit hlim)).1 hc'
    refine ⟨upsilon (succ ι), upsPt_upsilon (lt_of_le_of_lt zero_le (lt_succ ι)),
      hcx.trans (upsilon_normal.strictMono (lt_succ ι)), ?_⟩
    exact upsilon_normal.strictMono (hlim.succ_lt hι)

/-- **Lemma TOP_λ** (the upper end of BLK (ii)) at a restart index `λ` with the input `TopIn O λ`,
from what is known below `ρ_λ`: `ρ_λ` is not `≤₁` any `γ > δ_λ + O(λ)`. -/
theorem top_of_good {O : Ordinal.{0} → Ordinal.{0}} {l : Ordinal.{0}} (hT : TopIn O l)
    (G : Good O l) (R : RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1))) :
    ∀ g, upsilon (l + ω + 1) + O l < g → ¬ le1 (upsilon l) g := by
  obtain ⟨b, k, x0, hoff, hk, hk1, hx0, hreal⟩ := hT
  rw [hoff]
  refine R.top_gen hk hk1 hx0 ?_
  intro c d _ hcd hd h2 x hx0x hxc e he1 hte hxe
  rcases G.caps c d hcd hd h2 x hxc (d + e) hxe with hle | ⟨μ, hμ, hμl, rfl, hδd, hg⟩
  · exact absurd hle (not_le.2 (lt_add_of_pos_right d (lt_of_lt_of_le zero_lt_one he1)))
  · have hμ0 : 0 < μ := pos_iff_ne_zero.2 hμ.1
    have h1 := hreal μ hμ hμl hx0x
    have h2' := hte (upsPt_upsilon hμ0)
    have : upsilon (μ + ω + 1) + O μ < d + e :=
      lt_of_lt_of_le ((add_lt_add_iff_left _).2 (lt_of_lt_of_le h1 h2')) (add_le_add hδd le_rfl)
    exact absurd hg (not_le.2 this)

/-- `c*(λ) < δ_λ`. -/
theorem off_lt_δ {l : Ordinal.{0}} (hl : IsRestartIdx l) : off l < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hU : UpsPt (upsilon (l + ω + 1)) := upsPt_upsilon (lt_of_lt_of_le hl0 (le_self_add.trans
    le_self_add))
  have hlt : upsilon l < upsilon (l + ω + 1) := upsilon_normal.strictMono
    (lt_of_lt_of_le (lt_add_of_pos_right l omega0_pos) le_self_add)
  exact lt_of_le_of_lt (off_le hl) ((indec_of_upsPt hU).add_lt hlt (one_lt_of_upsPt hU))

/-- The chain of block contexts after `δ_λ + c*(λ)`, from TOP. -/
theorem chain_after {O : Ordinal.{0} → Ordinal.{0}} {l : Ordinal.{0}} (hO : O l < upsilon (l + ω + 1))
    (R : RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)))
    (htop : ∀ g, upsilon (l + ω + 1) + O l < g → ¬ le1 (upsilon l) g)
    (hcnt : l + ω * ω < Om1) :
    ∀ j : ℕ, BlkCtx (topA (l + ω) (upsilon (l + ω + 1) + O l) j) (lpA (l + ω) j)
      (topA (l + ω) (upsilon (l + ω + 1) + O l) (j + 1)) := by
  have hoffδ := hO
  have hT3 := R.T3off hoffδ htop
  have hT0 : upsilon (l + ω + 1) + O l < lpA (l + ω) 0 := by
    have hU : UpsPt (lpA (l + ω) 0) := upsPt_upsilon (lpA_index_pos _ 0)
    have hδl : upsilon (l + ω + 1) < lpA (l + ω) 0 := by
      refine upsilon_normal.strictMono ?_
      simp only [Nat.cast_zero, mul_zero, add_zero]
      exact (add_lt_add_iff_left _).2 one_lt_omega0
    exact (indec_of_upsPt hU).add_lt hδl (hoffδ.trans hδl)
  have hidx : ∀ l', IsSuccLimit l' → upsilon (l + ω + 1) + O l < upsilon l' → l + ω < l' := by
    intro l' _ h
    have : upsilon (l + ω + 1) < upsilon l' := lt_of_le_of_lt le_self_add h
    exact lt_of_le_of_lt le_self_add (upsilon_normal.strictMono.lt_iff_lt.1 this)
  exact ctxA (l + ω) _ hT3 hT0 hidx (fun j n => ups_lt_Om1 _ ((idx_lt l j n).trans hcnt))

/-- **The step at a restart `λ`** (given the input of Lemma TOP at `λ`): from `[0, ρ_λ)` to
`[0, ρ_{λ+ω²})`. -/
theorem good_step {O : Ordinal.{0} → Ordinal.{0}} {l : Ordinal.{0}} (hl : IsRestartIdx l)
    (hT : TopIn O l) (hO : O l < upsilon (l + ω + 1)) (G : Good O l)
    (hcnt : l + ω * ω < Om1) : Good O (l + ω * ω) := by
  have hww : 0 < ω * ω := mul_pos omega0_pos omega0_pos
  have hll : l < l + ω * ω := lt_add_of_pos_right l hww
  have hδ1 : upsilon (l + ω + 1) < Om1 :=
    ups_lt_Om1 _ (lt_of_lt_of_le (by simpa using idx_lt l 0 1) hcnt.le)
  have R := rstK_of_good hl G hδ1
  have htop := top_of_good hT G R
  have hoffδ := hO
  have hT3 := R.T3off hoffδ htop
  have C := chain_after hO R htop hcnt
  have hTa : upsilon (l + ω) ≤ upsilon (l + ω + 1) + O l := R.next.1.le.trans le_self_add
  have he : l + ω + ω * ω = l + ω * ω := by rw [add_assoc, w_add_ww]
  have hbelowC := chainA_below C hT3 hTa
  have hlandC := chainA_land C hTa
  rw [he] at hbelowC hlandC
  have hρc : ∀ c d, c < d → upsilon l ≤ d → le2 c d → upsilon l < c := by
    intro c d hcd hρd h2
    rcases lt_trichotomy c (upsilon l) with hcρ | e | h'
    · exact absurd (le2_le1 h2) (G.below c hcρ d hρd)
    · rw [e] at h2 hcd; exact absurd h2 (R.noSucc d hcd)
    · exact h'
  refine ⟨hbelowC, fun _ => hlandC, ?_, ?_, ?_, ?_⟩
  · -- caps
    intro c d hcd hd h2 x hxc g hg
    rcases lt_or_ge d (upsilon l) with hdρ | hρd
    · rcases G.caps c d hcd hdρ h2 x hxc g hg with h | ⟨μ, hμ, hμl, hx, hδd, hg'⟩
      · exact Or.inl h
      · exact Or.inr ⟨μ, hμ, hμl.trans hll, hx, hδd, hg'⟩
    have hρc' := hρc c d hcd hρd h2
    have hρd' : upsilon l < d := hρc'.trans hcd
    rcases lt_trichotomy d (upsilon (l + ω + 1)) with hdδ | e | hδd
    · exact absurd h2 (R.noPairGap c d hcd hρd' hdδ)
    · rw [e] at hcd ⊢
      rcases lt_trichotomy x (upsilon l) with hxρ | ex | hρx
      · exact Or.inl (le_of_lt (lt_of_lt_of_le (not_le.1 (fun h' => G.below x hxρ g h' hg))
          R.ρδ.le))
      · exact Or.inr ⟨l, hl, hll, ex, le_rfl, not_lt.1 (fun h' => htop g h' (ex ▸ hg))⟩
      · exact Or.inl (not_lt.1 (fun h' => R.capδ x hρx (hxc.trans hcd.le) g h' hg))
    · rcases le_or_gt d (upsilon (l + ω + 1) + O l) with hdT | hTd
      · exact absurd (indec_of_lt2_right h2 hcd).1 (decomp_mid hoffδ hδd hdT)
      · obtain ⟨k, -, -, hcap⟩ := chain_pair C hTa hTd (by rw [he]; exact hd) hcd h2
        exact Or.inl (hcap x (hxc.trans hcd.le) g hg)
  · -- pairs
    intro c d hcd hd
    constructor
    · intro h2
      rcases lt_or_ge d (upsilon l) with hdρ | hρd
      · obtain ⟨μ, j, hμ, hμl, hc, hd'⟩ := (G.pairs c d hcd hdρ).1 h2
        exact ⟨μ, j, hμ, hμl.trans hll, hc, hd'⟩
      have hρc' := hρc c d hcd hρd h2
      rcases lt_trichotomy d (upsilon (l + ω + 1)) with hdδ | e | hδd
      · exact absurd h2 (R.noPairGap c d hcd (hρc'.trans hcd) hdδ)
      · rw [e] at hcd h2 ⊢
        refine ⟨l, 0, Or.inr hl, hll, ?_, ?_⟩
        · rw [idx_one]; exact R.pairs_at_top hcd h2
        · rw [idx_one]
      · rcases le_or_gt d (upsilon (l + ω + 1) + O l) with hdT | hTd
        · exact absurd (indec_of_lt2_right h2 hcd).1 (decomp_mid hoffδ hδd hdT)
        · obtain ⟨k, rfl, rfl, -⟩ := chain_pair C hTa hTd (by rw [he]; exact hd) hcd h2
          refine ⟨l, k + 1, Or.inr hl, hll, ?_, ?_⟩
          · show upsilon (l + ω + ω * (k : Ordinal.{0}) + ω) = _
            rw [idx_chain]
          · show upsilon (l + ω + ω * (k : Ordinal.{0}) + ω + 1) = _
            rw [idx_chain]
    · rintro ⟨μ, j, hμ, hμl, rfl, rfl⟩
      rcases lt_trichotomy μ l with hμl' | e | hlμ
      · have hlt : upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < upsilon l :=
          upsilon_normal.strictMono (lt_of_lt_of_le (pidx_lt μ j)
            (next_mult (mult_of hμ) (ri_iff.1 hl).2 hμl'))
        exact (G.pairs _ _ hcd hlt).2 ⟨μ, j, hμ, hμl', rfl, rfl⟩
      · rw [e]
        rcases j with _ | k
        · rw [idx_one]; exact R.pair
        · have := (C k).pair
          simp only [lpA, topA] at this
          rw [idx_chain]; exact this
      · exact absurd hμl (not_lt.2 (next_mult (ri_iff.1 hl).2 (mult_of hμ) hlμ))
  · -- skeletal
    intro α hα hnu γ
    rcases lt_or_ge α (upsilon l) with hαρ | hρα
    · exact G.sk α hαρ hnu γ
    rcases eq_or_lt_of_le hρα with e | hρα'
    · exact absurd (e ▸ R.ρU) hnu
    rcases le_or_gt α (upsilon (l + ω + 1)) with hαδ | hδα
    · exact skel_block R.next.2.1 R.δ1 hρα' hαδ hnu R.lowδ γ
    rcases le_or_gt α (upsilon (l + ω + 1) + O l) with hαT | hTα
    · exact sk_decomp (decomp_mid hoffδ hδα hαT) γ
    · exact chain_sk C hTa hTα (by rw [he]; exact hα) hnu γ
  · -- restarts
    intro μ hμ hμl
    rcases lt_trichotomy μ l with hμl' | e | hlμ
    · exact G.rst μ hμ hμl'
    · rw [e]; exact ⟨R, htop, C⟩
    · exact absurd hμl (not_lt.2 (next_mult (ri_iff.1 hl).2 (ri_iff.1 hμ).2 hlμ))

/-! ## The limit step and the induction -/

theorem good_limit {O : Ordinal.{0} → Ordinal.{0}} {η : Ordinal.{0}} (hη : IsSuccLimit η)
    (IH : ∀ η' < η, Good O (ω * ω * η')) : Good O (ω * ω * η) := by
  have hww : 0 < ω * ω := mul_pos omega0_pos omega0_pos
  have hlim : IsSuccLimit (ω * ω * η) := isSuccLimit_mul_right hww hη
  have hlt : ∀ η' < η, ω * ω * η' < ω * ω * η := fun η' h => (mul_lt_mul_iff_right₀ hww).2 h
  have hup : ∀ η' < η, upsilon (ω * ω * η') < upsilon (ω * ω * η) :=
    fun η' h => upsilon_normal.strictMono (hlt η' h)
  have key : ∀ c < upsilon (ω * ω * η), ∃ η' < η, 0 < η' ∧ c < upsilon (ω * ω * η') := by
    intro c hc
    obtain ⟨_, ⟨ι, hι, rfl⟩, hcx⟩ := (lt_isLUB_iff (upsilon_limit hlim)).1 hc
    obtain ⟨η', hη', hιη'⟩ := (lt_mul_iff_of_isSuccLimit hη).1 hι
    refine ⟨η' + 1, hη.add_one_lt hη', lt_of_le_of_lt zero_le (lt_add_one _), hcx.trans
      (upsilon_normal.strictMono (hιη'.trans ((mul_lt_mul_iff_right₀ hww).2 (lt_add_one _))))⟩
  have keyμ : ∀ μ < ω * ω * η, ∃ η' < η, μ < ω * ω * η' :=
    fun μ hμ => (lt_mul_iff_of_isSuccLimit hη).1 hμ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc g hg
    obtain ⟨η', hη', -, hcη⟩ := key c hc
    exact (IH η' hη').below c hcη g ((hup η' hη').le.trans hg)
  · intro _ c' hc'
    obtain ⟨η', hη', h0, hcη⟩ := key c' hc'
    obtain ⟨σ, σ', h1, h2, h3, h4, h5⟩ := (IH η' hη').land (mul_pos hww h0) c' hcη
    exact ⟨σ, σ', h1, h2, h3, h4.trans (hup η' hη'), h5⟩
  · intro c d hcd hd h2 x hx g hg
    obtain ⟨η', hη', -, hdη⟩ := key d hd
    rcases (IH η' hη').caps c d hcd hdη h2 x hx g hg with h | ⟨μ, hμ, hμl, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨μ, hμ, hμl.trans (hlt η' hη'), h3⟩
  · intro c d hcd hd
    constructor
    · intro h2
      obtain ⟨η', hη', -, hdη⟩ := key d hd
      obtain ⟨μ, j, hμ, hμl, h3⟩ := ((IH η' hη').pairs c d hcd hdη).1 h2
      exact ⟨μ, j, hμ, hμl.trans (hlt η' hη'), h3⟩
    · rintro ⟨μ, j, hμ, hμl, rfl, rfl⟩
      obtain ⟨η', hη', hμη⟩ := keyμ μ hμl
      have hlt' : upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < upsilon (ω * ω * η') :=
        upsilon_normal.strictMono (lt_of_lt_of_le (pidx_lt μ j)
          (next_mult (mult_of hμ) (dvd_mul_right _ _) hμη))
      exact ((IH η' hη').pairs _ _ hcd hlt').2 ⟨μ, j, hμ, hμη, rfl, rfl⟩
  · intro α hα hnu γ
    obtain ⟨η', hη', -, hαη⟩ := key α hα
    exact (IH η' hη').sk α hαη hnu γ
  · intro μ hμ hμl
    obtain ⟨η', hη', hμη⟩ := keyμ μ hμl
    exact (IH η' hη').rst μ hμ hμη

theorem ww_lt_Om1 : (ω * ω : Ordinal.{0}) < Om1 := by
  rw [← pow_two, ← opow_natCast]
  exact Om1_opow_lt (lt_trans (natCast_lt_omega0 2) omega0_lt_omega_one)

theorem XiW_ri : IsRestartIdx XiW := ri_of_fp XiW_pos XiW_fp

/-- **An offset specification up to `B`** (a countable multiple of `ω²`): for every restart index
`λ < B`, `O(λ) < δ_λ`, `O(λ) ≥ 1`, the input of Lemma TOP (`TopIn O λ`), `O(λ) = 1` at a successor
restart index (`c(λ) < 2`), and the input of Lemma RS (`RsIn O λ`) at a limit restart index. -/
structure OffSpec (O : Ordinal.{0} → Ordinal.{0}) (B : Ordinal.{0}) : Prop where
  mult : ω * ω ∣ B
  cnt : B < Om1
  le : ∀ l, IsRestartIdx l → l < B → O l < upsilon (l + ω + 1)
  one : ∀ l, IsRestartIdx l → l < B → 1 ≤ O l
  top : ∀ l, IsRestartIdx l → l < B → TopIn O l
  succ : ∀ l, IsRestartIdx l → l < B → cL l < 2 → O l = 1
  rs : ∀ l, IsRestartIdx l → l < B → 2 ≤ cL l → RsIn O l

/-- **The block structure below `υ_B`** (FRAG-free): `Good O (ω²·η)` for every `ω²·η ≤ B`. -/
theorem good_all {O : Ordinal.{0} → Ordinal.{0}} {B : Ordinal.{0}} (S : OffSpec O B) :
    ∀ η, ω * ω * η ≤ B → Good O (ω * ω * η) := by
  have hww : 0 < ω * ω := mul_pos omega0_pos omega0_pos
  intro η
  induction η using WellFoundedLT.induction with
  | ind η IH =>
  intro hη
  rcases zero_or_succ_or_isSuccLimit η with rfl | ⟨η', rfl⟩ | hlim
  · rw [mul_zero]; exact good_zero O
  · have IH' := IH η' (lt_succ η')
    rw [succ_eq_add_one, mul_add_one] at hη ⊢
    have Gη' := IH' (le_self_add.trans hη)
    rcases eq_or_ne η' 0 with rfl | hη0
    · rw [mul_zero]; exact good_first O
    · have hl : IsRestartIdx (ω * ω * η') :=
        ri_iff.2 ⟨(mul_pos hww (pos_iff_ne_zero.2 hη0)).ne', dvd_mul_right _ _⟩
      have hlB : ω * ω * η' < B := lt_of_lt_of_le (lt_add_of_pos_right _ hww) hη
      exact good_step hl (S.top _ hl hlB) (S.le _ hl hlB) Gη' (lt_of_le_of_lt hη S.cnt)
  · exact good_limit hlim (fun η' hη' =>
      IH η' hη' (le_trans (mul_le_mul_right hη'.le _) hη))

/-- `Good O B`. -/
theorem good_B {O : Ordinal.{0} → Ordinal.{0}} {B : Ordinal.{0}} (S : OffSpec O B) : Good O B := by
  obtain ⟨ξ, hξ⟩ := S.mult
  rw [hξ]; exact good_all S ξ (hξ ▸ le_rfl)

/-- The offsets `c*` up to `Ξ_ω` form an offset specification up to `Ξ_ω + ω²` (by `topIn`, `rsIn`). -/
theorem specXi : OffSpec off (XiW + ω * ω) := by
  have hX : ∀ l, IsRestartIdx l → l < XiW + ω * ω → l ≤ XiW := fun l hl hlt => by
    by_contra hgt
    exact absurd hlt (not_lt.2 (next_mult (ri_iff.1 XiW_ri).2 (ri_iff.1 hl).2 (not_le.1 hgt)))
  refine ⟨?_, Om1_add_lt XiW_lt_Om1 ww_lt_Om1, fun _ hl _ => off_lt_δ hl,
    fun _ hl _ => one_le_off hl, fun l hl hlt => (topIn hl (hX l hl hlt)).toTopIn,
    fun _ hl _ h2 => off_succ hl h2, fun l hl hlt h2 => (rsIn hl (hX l hl hlt) h2).toRsIn⟩
  obtain ⟨q, hq⟩ := (ri_iff.1 XiW_ri).2
  exact ⟨q + 1, by rw [mul_add_one, hq]⟩

end Googology.Trans.PoR.InaccPsi.R2
