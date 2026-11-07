import Googology.Trans.PoR.InaccPsi.R2.YsGood

/-!
# Ys: the relative block induction from a restart `l₀` with short and long restarts

`Yf.YfSpec` starts the block induction at `l₀` but asks the base data (no crossing at all) and short offsets
everywhere; in the windows both are false (`Yf.yfNoBase_win`, `Yi.yiWinShort_ref`).  Here the induction
starts at `a = ρ_{l₀}` with NO base data except the landing blocks below `ρ_{l₀}`, allows crossings from the
points `≤ a`, and at every restart `l ∈ [l₀, B)` one of two kinds of input:

* `YsShortIn a O l` (an ordinary restart): an offset term `x·m + k` for `O(l) < δ_l`, a crossing bound
  `a ≤ x₀ < ρ_l` above which no restart realizes the term, and the chain data for the points `≤ x₀`;
* `YsGivenIn O l` (Lemma TOP given: a supply restart with a long reach, chain start `δ_l`, `YsLongIn`; or the
  base restart `l₀`, chain start `δ_{l₀} + O(l₀)`): Lemma TOP at `δ_l + O(l)` (that is UPPER when
  `δ_l + O(l) = r(l)`) and the chain data for the points `≤ ρ_l`;

and the pair field `nostr` at `ρ_l`.  Then `ysGood_all`: `YsGood (ρ_{l₀}) O (ω²·η)` for every
`l₀ ≤ ω²·η ≤ B`;  `ysTop_all`: Lemma TOP at every restart in `[l₀, B)`; `ysUpper_all`: UPPER at every restart
`μ` in `[l₀, B)` with `δ_μ + O(μ) = r(μ)`.

Supporting lemmas: `ysNoCross_short` (in the short kind no restart above `x₀` crosses `ρ_l`), `ysReach_of_le1`
(the chain datum `reach` from `x₀ ≤₁ υ_{l+ω²}`: in particular at a supply restart from LOWER and
`υ_{l+ω²} ≤ r(l)`, `ysReach_long`), `ysUpper_of_top`, `ysDelta_le_R` (UPPER forces `δ_μ ≤ r(μ)`), `ysT3_given`, `ysTopA_ge`, `ysTop_lt`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ys

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi

/-- The chain datum `reach` after `T₀ = δ_l + o`: a point `c ≤ x₀` crossing into a chain block reaches its top. -/
def YsReachIn (l o x0 : Ordinal.{0}) : Prop :=
  ∀ j : ℕ, ∀ c, c ≤ x0 → c ≤ topA (l + ω) (upsilon (l + ω + 1) + o) j →
      ∀ d, topA (l + ω) (upsilon (l + ω + 1) + o) j < d →
      d < topA (l + ω) (upsilon (l + ω + 1) + o) (j + 1) → le1 c d →
      le1 c (topA (l + ω) (upsilon (l + ω + 1) + o) (j + 1))

/-- The chain datum `nostr` after `T₀ = δ_l + o`: no pair from a point `c ≤ x₀` ends in a chain block. -/
def YsNostrIn (l o x0 : Ordinal.{0}) : Prop :=
  ∀ j : ℕ, ∀ c, c ≤ x0 → c ≤ topA (l + ω) (upsilon (l + ω + 1) + o) j →
      ∀ d, topA (l + ω) (upsilon (l + ω + 1) + o) j < d →
      d ≤ topA (l + ω) (upsilon (l + ω + 1) + o) (j + 1) → ¬ le2 c d

/-- The chain data after `T₀ = δ_l + o` for the crossing points `≤ x₀`. -/
def YsChainIn (l o x0 : Ordinal.{0}) : Prop := YsNostrIn l o x0

/-- **The input at an ordinary restart** (short offset term, crossing bound `x₀`). -/
def YsShortIn (a : Ordinal.{0}) (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Prop :=
  ∃ (m : ℕ) (k x0 : Ordinal.{0}), O l = tm m k (upsilon l) ∧ k < upsilon l ∧ (m = 0 → 1 ≤ k) ∧
    a ≤ x0 ∧ x0 < upsilon l ∧
    (∀ μ, IsRestartIdx μ → μ < l → x0 < upsilon μ → O μ < tm m k (upsilon μ)) ∧
    O l < upsilon (l + ω + 1) ∧ YsChainIn l (O l) x0

/-- **The input with Lemma TOP given** (a supply restart with a long reach, `o = 0`; or the base restart
`l₀`, `o = O(l₀)`): Lemma TOP at `δ_l + O(l)`, a chain start `δ_l + o` (`o < δ_l`, `o ≤ O(l)`) and the chain
data for the points `≤ ρ_l`. -/
def YsGivenIn (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Prop :=
  ∃ o, o < upsilon (l + ω + 1) ∧ o ≤ O l ∧
    (∀ g, upsilon (l + ω + 1) + O l < g → ¬ le1 (upsilon l) g) ∧ YsChainIn l o (upsilon l)

/-- **The input at a supply restart** (long reach): Lemma TOP at `δ_l + O(l)` and the chain data for the
points `≤ ρ_l` (the chain after `δ_l`). -/
def YsLongIn (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Prop :=
  (∀ g, upsilon (l + ω + 1) + O l < g → ¬ le1 (upsilon l) g) ∧ YsChainIn l 0 (upsilon l)

/-- A long input is a given input with `o = 0`. -/
theorem YsLongIn.toGiven {O : Ordinal.{0} → Ordinal.{0}} {l : Ordinal.{0}} (hl : IsRestartIdx l)
    (h : YsLongIn O l) : YsGivenIn O l :=
  ⟨0, lt_of_le_of_lt zero_le (upsilon_normal.strictMono (lt_of_lt_of_le (pos_iff_ne_zero.2 hl.1)
    (le_self_add.trans le_self_add))), zero_le, h.1, by simpa using h.2⟩

/-- **The hypotheses of the relative block induction** from `l₀` up to `B`. -/
structure YsSpec (O : Ordinal.{0} → Ordinal.{0}) (l0 B : Ordinal.{0}) : Prop where
  ri : IsRestartIdx l0
  mult : ω * ω ∣ B
  cnt : B < Om1
  lt : l0 < B
  land0 : ∀ c' < upsilon l0, ∃ σ σ', UpsPt σ ∧ c' < σ ∧ IsNext σ σ' ∧ σ' < upsilon l0 ∧
    (∀ a' b, σ < a' → b < σ' → (le1 a' b ↔ le1R a' b)) ∧ (∀ b, σ ≤ b → b < σ' → le1 σ b) ∧
    (∀ c d, c < d → σ < d → d < σ' → ¬ le2 c d)
  nostr : ∀ l, IsRestartIdx l → l0 ≤ l → l < B →
    ∀ c d, c < d → c ≤ upsilon l → upsilon l ≤ d → d ≤ upsilon (l + ω + 1) → ¬ le2 c d
  kind : ∀ l, IsRestartIdx l → l0 ≤ l → l < B → YsShortIn (upsilon l0) O l ∨ YsGivenIn O l

/-- **In the short kind no restart above `x₀` crosses `ρ_l`.** -/
theorem ysNoCross_short {O : Ordinal.{0} → Ordinal.{0}} {l x0 k : Ordinal.{0}} {m : ℕ}
    (hl : IsRestartIdx l) (hk : k < upsilon l)
    (hreal : ∀ μ, IsRestartIdx μ → μ < l → x0 < upsilon μ → O μ < tm m k (upsilon μ)) :
    ∀ μ, IsRestartIdx μ → μ < l → x0 < upsilon μ → upsilon (μ + ω + 1) + O μ < upsilon l := by
  intro μ hμ hμl hx
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hI := indec_of_upsPt (upsPt_upsilon hl0)
  have hδμ : upsilon (μ + ω + 1) < upsilon l :=
    upsilon_normal.strictMono (lt_of_lt_of_le (by simpa using idx_lt μ 0 1)
      (next_mult (ri_iff.1 hμ).2 (ri_iff.1 hl).2 hμl))
  have hρμ : upsilon μ < upsilon l := upsilon_normal.strictMono hμl
  have ht : tm m k (upsilon μ) < upsilon l :=
    hI.add_lt (YsRstK.mul_nat_lt hI hρμ m) hk
  exact hI.add_lt hδμ ((hreal μ hμ hμl hx).trans ht)

/-- `δ_l ≤` every chain top. -/
theorem ysTopA_ge (l o : Ordinal.{0}) (j : ℕ) :
    upsilon (l + ω + 1) ≤ topA (l + ω) (upsilon (l + ω + 1) + o) j := by
  cases j with
  | zero => exact le_self_add
  | succ j =>
    show upsilon (l + ω + 1) ≤ upsilon (l + ω + ω * (j : Ordinal.{0}) + ω + 1)
    refine upsilon_normal.strictMono.monotone (add_le_add ?_ le_rfl)
    exact le_self_add.trans le_self_add

/-- **The chain datum `reach` from one `≤₁`**: if `x₀ ≤ δ_l`, `x₀ ≤₁ E` and every chain top is `≤ E`, every
point `c ≤ x₀` crossing into a chain block reaches its top. -/
theorem ysReach_of_le1 {l o x0 E : Ordinal.{0}} (hx : x0 ≤ upsilon (l + ω + 1)) (hE : le1 x0 E)
    (htop : ∀ j : ℕ, topA (l + ω) (upsilon (l + ω + 1) + o) (j + 1) ≤ E) :
    ∀ j : ℕ, ∀ c, c ≤ x0 → c ≤ topA (l + ω) (upsilon (l + ω + 1) + o) j →
      ∀ d, topA (l + ω) (upsilon (l + ω + 1) + o) j < d →
      d < topA (l + ω) (upsilon (l + ω + 1) + o) (j + 1) → le1 c d →
      le1 c (topA (l + ω) (upsilon (l + ω + 1) + o) (j + 1)) := by
  intro j c hcx _ d hjd hdj hcd
  have hxd : x0 ≤ d := (hx.trans (ysTopA_ge l o j)).trans hjd.le
  have hcx0 : le1 c x0 := le1_of_le_of_le1 hcx hxd hcd
  exact le1_of_le_of_le1 ((hcx.trans hxd).trans hdj.le) (htop j) (le1_trans hcx0 hE)

/-- The chain tops are below `υ_{l+ω²}`. -/
theorem ysTop_lt (l o : Ordinal.{0}) (j : ℕ) :
    topA (l + ω) (upsilon (l + ω + 1) + o) (j + 1) ≤ upsilon (l + ω * ω) := by
  have := chainA_lp_lt (a := l + ω) (j + 1)
  have he : l + ω + ω * ω = l + ω * ω := by rw [add_assoc, w_add_ww]
  rw [he] at this
  refine le_of_lt (lt_of_lt_of_le ?_ this.le)
  show upsilon (l + ω + ω * (j : Ordinal.{0}) + ω + 1) < lpA (l + ω) (j + 1)
  unfold lpA
  refine upsilon_normal.strictMono ?_
  rw [omega_mul_succ, ← add_assoc]
  exact (add_lt_add_iff_left _).2 one_lt_omega0

/-- **The chain datum `reach` at a supply restart** from `ρ_l ≤₁ υ_{l+ω²}` (LOWER and a long reach). -/
theorem ysReach_long {l : Ordinal.{0}} (hE : le1 (upsilon l) (upsilon (l + ω * ω))) :
    ∀ j : ℕ, ∀ c, c ≤ upsilon l → c ≤ topA (l + ω) (upsilon (l + ω + 1) + 0) j →
      ∀ d, topA (l + ω) (upsilon (l + ω + 1) + 0) j < d →
      d < topA (l + ω) (upsilon (l + ω + 1) + 0) (j + 1) → le1 c d →
      le1 c (topA (l + ω) (upsilon (l + ω + 1) + 0) (j + 1)) :=
  ysReach_of_le1 (upsilon_normal.strictMono.monotone (le_self_add.trans le_self_add)) hE
    (fun j => ysTop_lt l 0 j)

/-- **Lemma TOP gives UPPER** when `δ_μ + O(μ) = r(μ)`. -/
theorem ysUpper_of_top {S : InaccSeq.{0}} {O : Ordinal.{0} → Ordinal.{0}} {μ : Ordinal.{0}}
    (htop : ∀ g, upsilon (μ + ω + 1) + O μ < g → ¬ le1 (upsilon μ) g)
    (hR : upsilon (μ + ω + 1) + O μ = Cd.cdR S μ) : Cd.CdUpper S μ := by
  intro h
  exact htop _ (by rw [hR]; exact lt_add_one _) h

/-- **UPPER forces `δ_μ ≤ r(μ)`** at a restart context with crossings (`ρ_μ ≤₁` all of `[ρ_μ, δ_μ]`). -/
theorem ysDelta_le_R {S : InaccSeq.{0}} {μ : Ordinal.{0}}
    (R : YsRstK (upsilon μ) (upsilon (μ + ω)) (upsilon (μ + ω + 1))) (hU : Cd.CdUpper S μ) :
    upsilon (μ + ω + 1) ≤ Cd.cdR S μ := by
  by_contra h
  push_neg at h
  have h1 : Cd.cdR S μ + 1 ≤ upsilon (μ + ω + 1) := add_one_le_of_lt h
  exact hU (R.le1ρδ _ ((Cd.cdRho_lt_R S μ).le.trans le_self_add) h1)

/-- **The closedness above `ρ_l` up to any chain start `δ_l + o`** (`o < δ_l`): no point of `(ρ_l, δ_l + o]` is
`≤₁` a point `> δ_l + o` (`capδ`, and the points of `(δ_l, δ_l + o]` are decomposable). -/
theorem ysT3_given {l o : Ordinal.{0}}
    (R : YsRstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1))) (ho : o < upsilon (l + ω + 1)) :
    ∀ c, upsilon l < c → c ≤ upsilon (l + ω + 1) + o → ∀ g, upsilon (l + ω + 1) + o < g → ¬ le1 c g := by
  intro c hρc hc g hg hcg
  have hδg : upsilon (l + ω + 1) < g := lt_of_le_of_lt le_self_add hg
  rcases le_or_gt c (upsilon (l + ω + 1)) with hcδ | hδc
  · exact R.capδ c hρc hcδ g hδg hcg
  · exact decomp_mid ho hδc hc (indec_of_lt1 hcg (lt_of_le_of_lt hc hg))

section Spec

variable {O : Ordinal.{0} → Ordinal.{0}} {l0 B : Ordinal.{0}} (Sp : YsSpec O l0 B)
include Sp

/-- **The relative block structure at every boundary `l₀ ≤ ω²·η ≤ B`.** -/
theorem ysGood_all : ∀ η, l0 ≤ ω * ω * η → ω * ω * η ≤ B → YsGood (upsilon l0) O (ω * ω * η) := by
  have hww : 0 < ω * ω := mul_pos omega0_pos omega0_pos
  have hl00 : 0 < l0 := pos_iff_ne_zero.2 Sp.ri.1
  intro η
  induction η using WellFoundedLT.induction with
  | ind η IH =>
  intro hl0η hη
  rcases eq_or_lt_of_le hl0η with e | hlt
  · rw [← e]; exact ysGood_base O l0
  rcases zero_or_succ_or_isSuccLimit η with rfl | ⟨η', rfl⟩ | hlim
  · rw [mul_zero] at hlt; exact absurd hlt (not_lt.2 zero_le)
  · rw [succ_eq_add_one, mul_add_one] at hη hlt ⊢
    have hl0η' : l0 ≤ ω * ω * η' := by
      by_contra h
      push_neg at h
      exact absurd hlt (not_lt.2 (next_mult (dvd_mul_right (ω * ω) η') (ri_iff.1 Sp.ri).2 h))
    set l := ω * ω * η' with hldef
    have hl : IsRestartIdx l := ri_iff.2 ⟨(lt_of_lt_of_le hl00 hl0η').ne', dvd_mul_right _ _⟩
    have hlB : l < B := lt_of_lt_of_le (lt_add_of_pos_right _ hww) hη
    have G := IH η' (lt_succ η') hl0η' (le_self_add.trans hη)
    have hcnt : l + ω * ω < Om1 := lt_of_le_of_lt hη Sp.cnt
    have hδ1 : upsilon (l + ω + 1) < Om1 :=
      ups_lt_Om1 _ (lt_of_lt_of_le (by simpa using idx_lt l 0 1) hcnt.le)
    have hal : upsilon l0 ≤ upsilon l := upsilon_normal.strictMono.monotone hl0η'
    have hland : ∀ c' < upsilon l, ∃ σ σ', UpsPt σ ∧ c' < σ ∧ IsNext σ σ' ∧ σ' < upsilon l ∧
        (∀ a' b, σ < a' → b < σ' → (le1 a' b ↔ le1R a' b)) ∧ (∀ b, σ ≤ b → b < σ' → le1 σ b) ∧
        (∀ c d, c < d → σ < d → d < σ' → ¬ le2 c d) := by
      rcases eq_or_lt_of_le hl0η' with e | h
      · rw [← e]; exact Sp.land0
      · exact G.land_all (upsilon_normal.strictMono h)
    have R := ysRst_of hl hland (Sp.nostr l hl hl0η' hlB) hδ1
    rcases Sp.kind l hl hl0η' hlB with ⟨m, k, x0, hoff, hk, hk1, hax, hx0, hreal, hO, hch2⟩ |
      ⟨o, ho, hoO, htop, hch2⟩
    · have htop := ysTop_short G R hoff hk hk1 hax hx0 hreal
      have hbel := ysBel_of G hax (ysNoCross_short hl hk hreal)
      exact ysGood_step hl G hal R htop hO le_rfl hax hx0.le (ysT3_short R hO htop hbel) hch2 hcnt
    · exact ysGood_step hl G hal R htop ho hoO hal le_rfl (ysT3_given R ho) hch2 hcnt
  · exact ysGood_limit hlim hlt (fun η' hη' h0 =>
      IH η' hη' h0 (le_trans (mul_le_mul_right hη'.le _) hη))

theorem ysGood_B : YsGood (upsilon l0) O B := by
  obtain ⟨ξ, hξ⟩ := Sp.mult
  rw [hξ]
  exact ysGood_all Sp ξ (hξ ▸ Sp.lt.le) (hξ ▸ le_rfl)

/-- **Lemma TOP at every restart `l₀ ≤ μ < B`**, with the restart context with crossings. -/
theorem ysTop_all {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h0 : l0 ≤ μ) (hμB : μ < B) :
    YsRstK (upsilon μ) (upsilon (μ + ω)) (upsilon (μ + ω + 1)) ∧
    (∀ g, upsilon (μ + ω + 1) + O μ < g → ¬ le1 (upsilon μ) g) :=
  ⟨((ysGood_B Sp).rst μ hμ hμB (upsilon_normal.strictMono.monotone h0)).1,
    ((ysGood_B Sp).rst μ hμ hμB (upsilon_normal.strictMono.monotone h0)).2.1⟩

/-- **UPPER at every restart `l₀ ≤ μ < B` whose bound is its predicted reach.** -/
theorem ysUpper_all {S : InaccSeq.{0}} {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h0 : l0 ≤ μ)
    (hμB : μ < B) (hR : upsilon (μ + ω + 1) + O μ = Cd.cdR S μ) : Cd.CdUpper S μ :=
  ysUpper_of_top (ysTop_all Sp hμ h0 hμB).2 hR

/-- No crossing structure is violated at the top: every point of `(ρ_{l₀}, υ_B)` that is `≤₁` a point
`≥ υ_B` is a restart `ρ_μ` with `g ≤ δ_μ + O(μ)`. -/
theorem ysCross_B : ∀ c, upsilon l0 < c → c < upsilon B → ∀ g, upsilon B ≤ g → le1 c g →
    ∃ μ, IsRestartIdx μ ∧ μ < B ∧ c = upsilon μ ∧ g ≤ upsilon (μ + ω + 1) + O μ :=
  (ysGood_B Sp).cross

end Spec

end Googology.Trans.PoR.InaccPsi.R2.Ys
