import Googology.Trans.PoR.InaccPsi.R2.XwJump

/-!
# Composing base changes: `B_m ∘ C_{n,m} = B_n`

Notation: `c_n = L(n+1)` (`Bc.bcC S n`), `B_n = Bc.bcB S n` (the base change `L(n+1) ↦ L(ω)` on `[0, L(ω))`),
`σ_m = bcSig (bcPre (m+1)) bcPreW`, `τ_m = bcSig bcPreW (bcPre (m+1))` (`R2.BcOnto`).

* `yeTau S m y = |τ_m(nf y)|` (**the `B_m`-preimage of `y`**), `YeDom S m y` (the domain of `τ_m` at the normal form
  of `y`, `Bc.bciD`);
* `yeTau_spec`: on the domain, `B_m(τ_m y) = y` and `τ_m y < L(m+2)` (for `y < L(ω+1)`);
* `yeDom_ev`, `yeDom_mono`: every `y < L(ω+1)` is in the domain for every large `m`, and the domain grows with `m`;
* `yeTau_lt_iff`, `yeTau_eq_of`: `τ_m` is strictly increasing on the domain, and it is the unique `B_m`-preimage
  below `L(m+2)`;
* `yeC S n m x = τ_m(B_n x)` (**the base change `C_{n,m}` from window `n` to window `m`**), `yeComp`
  (**`B_m(C_{n,m} x) = B_n x` for every large `m`**, `x < L(n+2)`), `yeComp_fin` (uniformly on a finite set);
* `yeGap_pre` (**the jump gap of `B_n` is the `B_m`-image of the gap of `C_{n,m}`**): for `p < L(n+2)` and a gap
  point `a ∈ [L(ω), B_n p)`, for every large `m` there is `a' ∈ (c_m, C_{n,m} p)` with `B_m a' = a`, and for every
  `q` in the domain, `B_n q ≤ a ⇔ C_{n,m} q ≤ a'`;
* `yeReach_pre` (under `L(ω+1) ≤ ν_C`): at a preimage `a'` that is not a range restart and has a reach `R < c_{m+1}`,
  `lh(B_m a') = B_m R`; so `yeGapLh_pre`: `lh(a) < B_n p ⇔ lh(a') < C_{n,m} p`;
* REFUTE-FIRST record at `n = 0`, `m = 1` (`ye01`): `C_{0,1}(c_1) = L(3) = c_2`, `B_1(C_{0,1} c_1) = L(ω+1) =
  B_0(c_1)`, and at the first jump `p = c_0·2`: `B_1(c_1·2) = L(ω)·2 = B_0(c_0·2)`, the gap point
  `L(ω) + c_0` of `B_0` is `B_1(c_1 + c_0)`, and `c_1 + c_0` lies in `[c_1 + c_0, c_1·2)` (the gap of `C_{0,1}`).
  No counterexample.

New definitions: `yeTau`, `YeDom`, `yeC` (maps and a domain predicate built from the repo's `bcSig`, `bcNf`, `bciD`;
no statement of the repo depends on them).  No axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ye

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Bc

/-- **The `B_m`-preimage** `τ_m(y) = |τ_m(nf y)|`. -/
noncomputable def yeTau (S : InaccSeq.{0}) (m : ℕ) (y : Ordinal.{0}) : Ordinal.{0} :=
  val S (bcSig bcPreW (bcPre (m + 1)) (bcNf S y))

/-- The domain of `τ_m` at `y`: the normal form of `y` is in the domain `bciD` of `τ_m`. -/
def YeDom (S : InaccSeq.{0}) (m : ℕ) (y : Ordinal.{0}) : Prop := bciD S m (bcNf S y)

/-- **The base change `C_{n,m}` from window `n` to window `m`**: `C_{n,m} = τ_m ∘ B_n`. -/
noncomputable def yeC (S : InaccSeq.{0}) (n m : ℕ) (x : Ordinal.{0}) : Ordinal.{0} :=
  yeTau S m (bcB S n x)

variable {S : InaccSeq.{0}}

theorem ye_lt_psiW {y : Ordinal.{0}} (hy : y < Nc.ncL S (ω + 1)) :
    y < S.psi (bcAlphaW S + Nc.ncPp S) (Om 1) := by
  rw [Nc.ncL_succ_omega] at hy; exact hy

theorem ye_nf {y : Ordinal.{0}} (hy : y < Nc.ncL S (ω + 1)) :
    NF (bcNf S y) ∧ val S (bcNf S y) = y :=
  bcNf_spec S (mem_of_lt_psi S (ye_lt_psiW hy))

/-- `c_m < L(m+2)`. -/
theorem ye_c_lt (m : ℕ) : bcC S m < Nc.ncL S ((m + 2 : ℕ) : Ordinal.{0}) := by
  show Nc.ncL S (((m + 1 : ℕ)) : Ordinal.{0}) < Nc.ncL S ((m + 2 : ℕ) : Ordinal.{0})
  unfold Nc.ncL
  exact psi_lt_psi Low.InR_Om_one ((add_lt_add_iff_left _).2 ((mul_lt_mul_iff_right₀ (Qq.qqPp_pos S)).2
    (by exact_mod_cast (show m + 1 < m + 2 by omega)))) (Qq.qqArg_nat_mem S (m + 1) _)

/-- **`B_m(τ_m y) = y` and `τ_m y < L(m+2)` on the domain.** -/
theorem yeTau_spec {m : ℕ} {y : Ordinal.{0}} (hy : y < Nc.ncL S (ω + 1)) (hD : YeDom S m y) :
    bcB S m (yeTau S m y) = y ∧ yeTau S m y < Nc.ncL S ((m + 2 : ℕ) : Ordinal.{0}) := by
  obtain ⟨hN, hv⟩ := ye_nf hy
  set t' := bcSig bcPreW (bcPre (m + 1)) (bcNf S y) with ht'
  have ht'N : NF t' := bci_NF hD
  refine ⟨?_, ?_⟩
  · unfold bcB yeTau
    rw [← ht', bcNf_val S ht'N, ht', bc_sig_tau S m _ _ le_rfl hD, hv]
  · have hc := bci_cmp' hD (bciD_bcLtW1 S m)
    rw [tau_bcLtW1, cmp_lt_of_val S hN (NF_bcLtW1 S) (by rw [hv, val_bcLtW1]; exact hy)] at hc
    have := (cmp_lt_iff S ht'N (NF_bcLt S (m + 1))).1 hc
    rw [val_bcLt] at this
    exact this

/-- The domain grows with `m`. -/
theorem yeDom_mono {m m' : ℕ} (hm : m ≤ m') {y : Ordinal.{0}} (hD : YeDom S m y) : YeDom S m' y :=
  ⟨hD.1, bciArgs_mono S hm hD.2⟩

/-- **Every `y < L(ω+1)` is in the domain of `τ_m` for every large `m`.** -/
theorem yeDom_ev {y : Ordinal.{0}} (hy : y < Nc.ncL S (ω + 1)) : ∃ M : ℕ, ∀ m, M ≤ m → YeDom S m y := by
  have hy' := ye_lt_psiW hy
  obtain ⟨hN, hv⟩ := ye_nf hy
  have hA : bcArgsLt S (bcAlphaWW S) (bcNf S y) := by
    refine bcArgsLt_mono S ?_ (bcArgsLt_of_lt S hN (by rw [hv]; exact hy'))
    unfold bcAlphaWW
    refine (add_le_add_iff_left _).2 ?_
    have := (cmp_lt_iff S NF_tPp NF_tWp).1 cmp_tPp_tWp
    rw [val_tPp, val_tWp] at this
    exact this.le
  have hy1 : y < Om 1 := hy.trans (InaccSeq.psi_lt (S := S) InaccSeq.InR_Om1 _)
  have hNA := bc_nargs S hN hA (by rw [hv]; exact hy1.trans (Om1_lt_Wp S))
  obtain ⟨M, hM⟩ := bci_eventually S hN hA hNA
  exact ⟨M, fun m hm => ⟨hN, hM m hm⟩⟩

/-- **`τ_m` is strictly increasing on its domain.** -/
theorem yeTau_lt_iff {m : ℕ} {y y' : Ordinal.{0}} (hy : y < Nc.ncL S (ω + 1)) (hy' : y' < Nc.ncL S (ω + 1))
    (hD : YeDom S m y) (hD' : YeDom S m y') : yeTau S m y < yeTau S m y' ↔ y < y' := by
  obtain ⟨e1, l1⟩ := yeTau_spec hy hD
  obtain ⟨e2, l2⟩ := yeTau_spec hy' hD'
  have h := (bcB_mono (S := S) m).lt_iff_lt (Set.mem_Iio.2 l1) (Set.mem_Iio.2 l2)
  rw [e1, e2] at h
  exact h.symm

/-- **`τ_m y` is the unique `B_m`-preimage of `y` below `L(m+2)`.** -/
theorem yeTau_eq_of {m : ℕ} {y y' : Ordinal.{0}} (hy : y < Nc.ncL S (ω + 1)) (hD : YeDom S m y)
    (hy' : y' < Nc.ncL S ((m + 2 : ℕ) : Ordinal.{0})) (he : bcB S m y' = y) : yeTau S m y = y' := by
  obtain ⟨e1, l1⟩ := yeTau_spec hy hD
  exact (bcB_mono (S := S) m).injOn (Set.mem_Iio.2 l1) (Set.mem_Iio.2 hy') (e1.trans he.symm)

/-! ## The composition -/

/-- **`B_m(C_{n,m} x) = B_n x` for every large `m`** (`x < L(n+2)`). -/
theorem yeComp {n : ℕ} {x : Ordinal.{0}} (hx : x < Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})) :
    ∃ M : ℕ, ∀ m, M ≤ m → YeDom S m (bcB S n x) ∧ bcB S m (yeC S n m x) = bcB S n x ∧
      yeC S n m x < Nc.ncL S ((m + 2 : ℕ) : Ordinal.{0}) := by
  have hb := bcB_bound (S := S) n x hx
  obtain ⟨M, hM⟩ := yeDom_ev hb
  exact ⟨M, fun m hm => ⟨hM m hm, (yeTau_spec hb (hM m hm)).1, (yeTau_spec hb (hM m hm)).2⟩⟩

/-- **The composition uniformly on a finite set.** -/
theorem yeComp_fin {n : ℕ} (Y : Finset Ordinal.{0}) (hY : ∀ x ∈ Y, x < Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})) :
    ∃ M : ℕ, ∀ m, M ≤ m → ∀ x ∈ Y, YeDom S m (bcB S n x) ∧ bcB S m (yeC S n m x) = bcB S n x ∧
      yeC S n m x < Nc.ncL S ((m + 2 : ℕ) : Ordinal.{0}) := by
  classical
  induction Y using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert y Y _ ih =>
    obtain ⟨M1, h1⟩ := ih (fun z hz => hY z (Finset.mem_insert_of_mem hz))
    obtain ⟨M2, h2⟩ := yeComp (hY y (Finset.mem_insert_self y Y))
    refine ⟨max M1 M2, fun m hm z hz => ?_⟩
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact h2 m (le_of_max_le_right hm)
    · exact h1 m (le_of_max_le_left hm) z hz

/-- `C_{n,m}` is strictly increasing where the composition holds. -/
theorem yeC_lt_iff {n m : ℕ} {x x' : Ordinal.{0}} (hx : x < Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
    (hx' : x' < Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})) (hD : YeDom S m (bcB S n x))
    (hD' : YeDom S m (bcB S n x')) : yeC S n m x < yeC S n m x' ↔ x < x' := by
  unfold yeC
  rw [yeTau_lt_iff (bcB_bound n x hx) (bcB_bound n x' hx') hD hD']
  exact (bcB_mono (S := S) n).lt_iff_lt (Set.mem_Iio.2 hx) (Set.mem_Iio.2 hx')

/-! ## The jump gap of `B_n` through `B_m` -/

/-- **The gap of `B_n` at `p` is the `B_m`-image of the gap of `C_{n,m}` at `p`** (pointwise, every large `m`). -/
theorem yeGap_pre {n : ℕ} {p a : Ordinal.{0}} (hp : p < Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
    (hLa : Nc.ncL S ω ≤ a) (ha : a < bcB S n p) :
    ∃ M : ℕ, ∀ m, M ≤ m → ∃ a', bcC S m ≤ a' ∧ a' < yeC S n m p ∧ bcB S m a' = a ∧
      bcB S m (yeC S n m p) = bcB S n p ∧
      ∀ q < Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}), YeDom S m (bcB S n q) →
        (bcB S n q ≤ a ↔ yeC S n m q ≤ a') := by
  have hpb := bcB_bound (S := S) n p hp
  have haW : a < Nc.ncL S (ω + 1) := ha.trans hpb
  obtain ⟨M1, h1⟩ := bc_onto_one S haW
  obtain ⟨M2, h2⟩ := yeComp hp
  refine ⟨max M1 M2, fun m hm => ?_⟩
  obtain ⟨a', ha'L, ha'⟩ := h1 m (le_of_max_le_left hm)
  obtain ⟨-, hCp, hCpL⟩ := h2 m (le_of_max_le_right hm)
  refine ⟨a', ?_, ?_, ha', hCp, fun q hq hDq => ?_⟩
  · by_contra hlt
    push Not at hlt
    have hcL : bcC S m < Nc.ncL S ((m + 2 : ℕ) : Ordinal.{0}) := ye_c_lt m
    have := ((bcB_mono (S := S) m).lt_iff_lt (Set.mem_Iio.2 ha'L) (Set.mem_Iio.2 hcL)).2 hlt
    rw [ha', show bcB S m (bcC S m) = Nc.ncL S ω from bcB_base m] at this
    exact absurd hLa (not_le.2 this)
  · have := ((bcB_mono (S := S) m).lt_iff_lt (Set.mem_Iio.2 ha'L) (Set.mem_Iio.2 hCpL)).1
      (by rw [ha', hCp]; exact ha)
    exact this
  · have hqb := bcB_bound (S := S) n q hq
    obtain ⟨eq1, lq⟩ := yeTau_spec hqb hDq
    have hle := (bcB_mono (S := S) m).le_iff_le (Set.mem_Iio.2 lq) (Set.mem_Iio.2 ha'L)
    unfold yeC
    rw [← hle, eq1, ha']

/-- **The reach move at a preimage** (under `L(ω+1) ≤ ν_C`): if `a' ∈ (c_m, c_{m+1})` is not a range restart and
`lh(a') = R < c_{m+1}`, then `lh(B_m a') = B_m R`. -/
theorem yeReach_pre (hν : Nc.ncL S (ω + 1) ≤ nuC) {m : ℕ} {a' R : Ordinal.{0}} (h1 : bcC S m < a')
    (hRc : R < bcC S (m + 1)) (hR : IsReach R2C a' R) (hnr : ∀ l, CdRange S l → a' ≠ upsilon l) :
    IsReach R2C (bcB S m a') (bcB S m R) :=
  Xr.xrRM_off hν h1 hRc hR hnr

/-- **The gap-reach question moves to the window `m`**: at a preimage `a'` of a gap point `a` as in `yeGap_pre`,
with `a'` not a range restart and `lh(a') = R < c_{m+1}`: `lh(a) < B_n p ⇔ lh(a') < C_{n,m} p`. -/
theorem yeGapLh_pre (hν : Nc.ncL S (ω + 1) ≤ nuC) {n m : ℕ} {p a a' R : Ordinal.{0}}
    (h1 : bcC S m < a') (hRc : R < bcC S (m + 1)) (hR : IsReach R2C a' R)
    (hnr : ∀ l, CdRange S l → a' ≠ upsilon l) (ha' : bcB S m a' = a)
    (hCp : bcB S m (yeC S n m p) = bcB S n p)
    (hCpL : yeC S n m p < Nc.ncL S ((m + 2 : ℕ) : Ordinal.{0})) :
    IsReach R2C a (bcB S m R) ∧ (bcB S m R < bcB S n p ↔ R < yeC S n m p) := by
  refine ⟨ha' ▸ yeReach_pre hν h1 hRc hR hnr, ?_⟩
  rw [← hCp]
  exact (bcB_mono (S := S) m).lt_iff_lt (Set.mem_Iio.2 hRc) (Set.mem_Iio.2 hCpL)

/-! ## REFUTE FIRST at `n = 0`, `m = 1` -/

/-- **The composition at `n = 0`, `m = 1`, tested at `c_1 = L(2)` and at the first jump of `B_0`.**
`C_{0,1}(c_1) = L(3) = c_2`, `B_1(C_{0,1} c_1) = L(ω+1) = B_0(c_1)`; `B_1(c_1·2) = L(ω)·2 = B_0(c_0·2)`;
the gap point `L(ω) + c_0` of `B_0` at `c_0·2` is `B_1(c_1 + c_0)`, and `c_1 + c_0 ∈ [c_1 + c_0, c_1·2)` lies in the
gap of `C_{0,1}` at `c_0·2`. -/
theorem ye01 :
    yeC S 0 1 (bcC S 1) = bcC S 2 ∧ bcB S 1 (yeC S 0 1 (bcC S 1)) = bcB S 0 (bcC S 1) ∧
      bcB S 1 (bcC S 1 * 2) = bcB S 0 (bcC S 0 * 2) ∧
      bcB S 1 (bcC S 1 + bcC S 0) = Nc.ncL S ω + bcC S 0 ∧
      (∀ q < bcC S 0 * 2, bcB S 0 q < Nc.ncL S ω + bcC S 0) ∧
      Nc.ncL S ω + bcC S 0 < bcB S 0 (bcC S 0 * 2) ∧ bcC S 1 + bcC S 0 < bcC S 1 * 2 := by
  have hB0 : bcB S 0 (bcC S 1) = Nc.ncL S (ω + 1) := bcB_base1 0
  have hτ : yeTau S 1 (Nc.ncL S (ω + 1)) = bcC S 2 := by
    unfold yeTau
    rw [← val_bcLtW1 (S := S), bcNf_val S (NF_bcLtW1 S), tau_bcLtW1, val_bcLt]
    rfl
  have hC : yeC S 0 1 (bcC S 1) = bcC S 2 := by unfold yeC; rw [hB0, hτ]
  refine ⟨hC, ?_, ?_, ?_, Xw.xwFirst_below 0, ?_, ?_⟩
  · rw [hC, hB0]; exact bcB_base1 1
  · rw [Xw.xwFirst_val 1, Xw.xwFirst_val 0]
  · rw [bcB_add (bcC_lt S 1) (bcC_lt S 0), show bcB S 1 (bcC S 1) = Nc.ncL S ω from bcB_base 1,
      bcB_fixN 1 (bcC S 0) (ye_c_lt 0)]
  · rw [Xw.xwFirst_val 0]; exact Xw.xwFirst_gap_ne 0
  · rw [Xw.xw_mul2]; exact (add_lt_add_iff_left _).2 (ye_c_lt 0)

end Googology.Trans.PoR.InaccPsi.R2.Ye
