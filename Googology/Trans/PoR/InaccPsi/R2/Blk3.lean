import Googology.Trans.PoR.InaccPsi.R2.RstC

/-!
# All blocks below `υ_{ω³}` in `R₂^C` (Theorem B″ for every restart, Lemma TOP^h, Lemma SK3)

* `ups_next_lt`, `ups_lim_lt`, `ups_lt_Om1_off`, `ups_lt_Om1_3`: the `υ`-points with index
  `< ω³` are countable.
* `topA a T₀ j`, `lpA a j`, `ctxA`: the chain of block contexts after a lower end `T₀` with base
  index `a` (`lpA a j = υ_{a+ω·j+ω}`, `topA a T₀ (j+1) = υ_{a+ω·j+ω+1}`, `topA a T₀ 0 = T₀`).
* `chainA_*`: what a chain gives below `υ_{a+ω·ω}`: the pairs, the closedness of points below,
  landing blocks, the caps of the pairs.
* `rst_of_chain`, `rstCtx`: the restart context of `ρ_{h+1} = υ_{ω²·(h+1)}` for every `h`.
* `thmB2_C` (**Theorem B″ in `R₂^C` for every restart below `υ_{ω³}`, with TOP^h**), `pairs_lt_w3`
  (the `<₂`-pairs below `υ_{ω³}`), `sk3_C` (**Lemma SK3 in `R₂^C`**: skeletal below `υ_{ω³}`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-! ## Countability -/

theorem ups_next_lt {x : Ordinal.{0}} (hx : upsilon x < Om1) : upsilon (x + 1) < Om1 := by
  have hn := upsilon_isNext x
  rw [succ_eq_add_one] at hn
  refine next_lt_Om1 hn ?_ hx
  rcases eq_or_ne (upsilon x) 0 with h0 | h0
  · left; exact h0
  · right; exact ⟨pos_iff_ne_zero.2 h0, ((upsilon_mem _).resolve_left h0).2⟩

theorem ups_lim_lt {b : Ordinal.{0}} (hb : ∀ n : ℕ, upsilon (b + n) < Om1) :
    upsilon (b + ω) < Om1 := by
  have hlub := upsilon_limit (isSuccLimit_add b isSuccLimit_omega0)
  have hs : (⨆ n : ℕ, upsilon (b + n)) < Om1 := Ordinal.iSup_lt_omega_one hb
  refine lt_of_le_of_lt (hlub.2 ?_) hs
  rintro _ ⟨i, hi, rfl⟩
  obtain ⟨d, hd, hid⟩ := (lt_add_iff_of_isSuccLimit isSuccLimit_omega0).1 hi
  obtain ⟨n, rfl⟩ := lt_omega0.1 hd
  exact (upsilon_normal.strictMono hid).le.trans
    (le_ciSup (f := fun n : ℕ => upsilon (b + n)) ⟨Om1, by rintro _ ⟨k, rfl⟩; exact (hb k).le⟩ n)

theorem ups_lt_Om1_off {a : Ordinal.{0}} (ha : upsilon a < Om1) :
    ∀ j n : ℕ, upsilon (a + ω * (j : Ordinal.{0}) + n) < Om1 := by
  have hn0 : ∀ b : Ordinal.{0}, upsilon b < Om1 → ∀ n : ℕ, upsilon (b + n) < Om1 := by
    intro b hb n
    induction n with
    | zero => simpa using hb
    | succ n ih => rw [Nat.cast_succ, ← add_assoc]; exact ups_next_lt ih
  intro j
  induction j with
  | zero => intro n; simpa using hn0 a ha n
  | succ j ih =>
    have h0 : upsilon (a + ω * ((j + 1 : ℕ) : Ordinal.{0})) < Om1 := by
      rw [omega_mul_succ, ← add_assoc]; exact ups_lim_lt ih
    exact hn0 _ h0

theorem ups_lt_Om1_3 : ∀ h j n : ℕ, upsilon (ω * ω * (h : Ordinal.{0}) + ω * j + n) < Om1 := by
  intro h
  induction h with
  | zero =>
    have := ups_lt_Om1_off (a := 0) (by rw [upsilon_zero]; exact omega_pos 1)
    simpa using this
  | succ h ih =>
    refine ups_lt_Om1_off ?_
    have he : ω * ω * ((h + 1 : ℕ) : Ordinal.{0}) = ω * ω * (h : Ordinal.{0}) + ω * ω := by
      push_cast; rw [mul_add, mul_one]
    rw [he]
    have hlim : IsSuccLimit (ω * ω : Ordinal.{0}) := isSuccLimit_mul_right omega0_pos isSuccLimit_omega0
    have hlub := upsilon_limit (isSuccLimit_add (ω * ω * (h : Ordinal.{0})) hlim)
    have hs : (⨆ m : ℕ, upsilon (ω * ω * (h : Ordinal.{0}) + ω * m)) < Om1 :=
      Ordinal.iSup_lt_omega_one (fun m => by simpa using ih m 0)
    refine lt_of_le_of_lt (hlub.2 ?_) hs
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨d, hd, hid⟩ := (lt_add_iff_of_isSuccLimit hlim).1 hi
    obtain ⟨c', hc', hdc⟩ := (lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 hd
    obtain ⟨m, rfl⟩ := lt_omega0.1 hc'
    have : i < ω * ω * (h : Ordinal.{0}) + ω * m := hid.trans_le ((add_le_add_iff_left _).2 hdc.le)
    exact (upsilon_normal.strictMono this).le.trans
      (le_ciSup (f := fun m : ℕ => upsilon (ω * ω * (h : Ordinal.{0}) + ω * m))
        ⟨Om1, by rintro _ ⟨k, rfl⟩; simpa using (ih k 0).le⟩ m)

theorem one_lt_of_upsPt {u : Ordinal.{0}} (hu : UpsPt u) : 1 < u := by
  have hE := upsPt_inE hu
  unfold InE at hE
  calc (1 : Ordinal.{0}) < ω := one_lt_omega0
    _ = ω ^ (1 : Ordinal.{0}) := (opow_one ω).symm
    _ ≤ ω ^ u := opow_le_opow_right omega0_pos (one_le_iff_pos.2 hu.1)
    _ = u := hE

/-! ## Chains of block contexts -/

/-- The top of block `j` after `T₀` with base index `a`. -/
noncomputable def topA (a T0 : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => T0
  | j + 1 => upsilon (a + ω * (j : Ordinal.{0}) + ω + 1)

/-- The left end of the pair of block `j`: `υ_{a+ω·j+ω}`. -/
noncomputable def lpA (a : Ordinal.{0}) (j : ℕ) : Ordinal.{0} := upsilon (a + ω * (j : Ordinal.{0}) + ω)

theorem lpA_index_pos (a : Ordinal.{0}) (j : ℕ) : 0 < a + ω * (j : Ordinal.{0}) + ω :=
  lt_of_lt_of_le omega0_pos le_add_self

/-- The chain of block contexts after `T₀`. -/
theorem ctxA (a T0 : Ordinal.{0}) (hT3 : ∀ c ≤ T0, ∀ g, T0 < g → ¬ le1 c g)
    (hT0 : T0 < lpA a 0) (hidx : ∀ l, IsSuccLimit l → T0 < upsilon l → a < l)
    (hc : ∀ j n : ℕ, upsilon (a + ω * (j : Ordinal.{0}) + n) < Om1) :
    ∀ j : ℕ, BlkCtx (topA a T0 j) (lpA a j) (topA a T0 (j + 1)) := by
  have base : ∀ j : ℕ, (∀ c ≤ topA a T0 j, ∀ g, topA a T0 j < g → ¬ le1 c g) →
      (topA a T0 j < lpA a j) →
      (∀ l, IsSuccLimit l → topA a T0 j < upsilon l → a + ω * (j : Ordinal.{0}) < l) →
      BlkCtx (topA a T0 j) (lpA a j) (topA a T0 (j + 1)) := by
    intro j hT3' hTτ hidx'
    have hlim : IsSuccLimit (a + ω * (j : Ordinal.{0}) + ω) := isSuccLimit_add _ isSuccLimit_omega0
    have hnext : IsNext (lpA a j) (topA a T0 (j + 1)) := by
      have := upsilon_isNext (a + ω * (j : Ordinal.{0}) + ω)
      rwa [succ_eq_add_one] at this
    refine ⟨upsPt_upsilon (lpA_index_pos a j), hnext, ?_, hTτ, hT3', ?_, ?_⟩
    · show upsilon (a + ω * (j : Ordinal.{0}) + ω + 1) < Om1
      have := hc (j + 1) 1
      rwa [omega_mul_succ, ← add_assoc, Nat.cast_one] at this
    · intro l hl hTl hlτ
      have h1 := hidx' l hl hTl
      have h2 : l ≤ a + ω * (j : Ordinal.{0}) + ω := upsilon_normal.strictMono.le_iff_le.1 hlτ
      show upsilon l = upsilon (a + ω * (j : Ordinal.{0}) + ω)
      rw [limit_eq_add_omega hl h1 h2]
    · intro c' hc'
      obtain ⟨_, ⟨ι, hι, rfl⟩, hcx⟩ := (lt_isLUB_iff (upsilon_limit hlim)).1 hc'
      refine ⟨upsilon (succ ι), upsPt_upsilon (lt_of_le_of_lt zero_le (lt_succ ι)),
        hcx.trans (upsilon_normal.strictMono (lt_succ ι)), ?_⟩
      exact upsilon_normal.strictMono (hlim.succ_lt hι)
  intro j
  induction j with
  | zero =>
    refine base 0 hT3 hT0 ?_
    intro l hl hTl
    simpa using hidx l hl hTl
  | succ j ih =>
    refine base (j + 1) ih.T3_next ?_ ?_
    · show upsilon (a + ω * (j : Ordinal.{0}) + ω + 1) <
        upsilon (a + ω * ((j + 1 : ℕ) : Ordinal.{0}) + ω)
      rw [omega_mul_succ, ← add_assoc]
      exact upsilon_normal.strictMono ((add_lt_add_iff_left _).2 one_lt_omega0)
    · intro l _ hTl
      have : a + ω * (j : Ordinal.{0}) + ω + 1 < l := upsilon_normal.strictMono.lt_iff_lt.1 hTl
      rw [omega_mul_succ, ← add_assoc]
      exact lt_of_le_of_lt le_self_add this

section Chain

variable {a T0 : Ordinal.{0}} (hctx : ∀ j : ℕ, BlkCtx (topA a T0 j) (lpA a j) (topA a T0 (j + 1)))
include hctx

theorem chainA_topMono : StrictMono (topA a T0) :=
  strictMono_nat_of_lt_succ fun j => lt_trans (hctx j).Tτ (hctx j).τβ

/-- The pairs with right end in `(T₀, topA j]`. -/
theorem chainA_pairs : ∀ j : ℕ, ∀ c d, c < d → T0 < d → d ≤ topA a T0 j → le2 c d →
    ∃ k < j, c = lpA a k ∧ d = topA a T0 (k + 1) := by
  intro j
  induction j with
  | zero =>
    intro c d _ hTd hd _
    exact absurd (lt_of_lt_of_le hTd hd) (lt_irrefl _)
  | succ j ih =>
    intro c d hcd hTd hd h2
    rcases le_or_gt d (topA a T0 j) with hdj | hdj
    · obtain ⟨k, hk, hck, hdk⟩ := ih c d hcd hTd hdj h2
      exact ⟨k, Nat.lt_succ_of_lt hk, hck, hdk⟩
    rcases eq_or_lt_of_le hd with e | hlt
    · subst e
      exact ⟨j, Nat.lt_succ_self j, (hctx j).pairs_at_top hcd h2, rfl⟩
    · exact absurd h2 ((hctx j).no_pair_gap c d hcd hdj hlt)

omit hctx in
theorem chainA_lp_lt (j : ℕ) : lpA a j < upsilon (a + ω * ω) := by
  refine upsilon_normal.strictMono ?_
  rw [add_assoc]
  refine (add_lt_add_iff_left a).2 ?_
  rw [← omega_mul_succ]
  exact (mul_lt_mul_iff_right₀ omega0_pos).2 (natCast_lt_omega0 _)

theorem chainA_top_lt (j : ℕ) : topA a T0 (j + 1) < upsilon (a + ω * ω) :=
  ((hctx (j + 1)).Tτ).trans (chainA_lp_lt (a := a) (j + 1))

omit hctx in
/-- Every point below `υ_{a+ω·ω}` lies below `T₀` or below some block top. -/
theorem chainA_sup (hTa : upsilon a ≤ T0) {c : Ordinal.{0}} (hc : c < upsilon (a + ω * ω)) :
    c ≤ T0 ∨ ∃ j, c ≤ topA a T0 (j + 1) := by
  have hlim : IsSuccLimit (ω * ω : Ordinal.{0}) := isSuccLimit_mul_right omega0_pos isSuccLimit_omega0
  obtain ⟨_, ⟨ι, hι, rfl⟩, hcx⟩ :=
    (lt_isLUB_iff (upsilon_limit (isSuccLimit_add a hlim))).1 hc
  obtain ⟨d, hd, hid⟩ := (lt_add_iff_of_isSuccLimit hlim).1 hι
  obtain ⟨c', hc', hdc⟩ := (lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 hd
  obtain ⟨m, rfl⟩ := lt_omega0.1 hc'
  rcases m with _ | m
  · left
    have : ι < a := by simpa using hid.trans_le ((add_le_add_iff_left _).2 hdc.le)
    exact (hcx.trans (upsilon_normal.strictMono this)).le.trans hTa
  · right
    refine ⟨m, (hcx.trans (upsilon_normal.strictMono ?_)).le⟩
    have : ι < a + ω * ((m + 1 : ℕ) : Ordinal.{0}) := hid.trans_le ((add_le_add_iff_left _).2 hdc.le)
    rw [omega_mul_succ, ← add_assoc] at this
    exact this.trans (lt_add_one _)

/-- No point below `υ_{a+ω·ω}` is `≤₁` a point `≥ υ_{a+ω·ω}`. -/
theorem chainA_below (hT3 : ∀ c ≤ T0, ∀ g, T0 < g → ¬ le1 c g) (hTa : upsilon a ≤ T0) :
    ∀ c < upsilon (a + ω * ω), ∀ g, upsilon (a + ω * ω) ≤ g → ¬ le1 c g := by
  intro c hc g hg
  have hT0 : T0 < upsilon (a + ω * ω) := ((hctx 0).Tτ).trans (chainA_lp_lt (a := a) 0)
  rcases chainA_sup hTa hc with hcT | ⟨j, hcj⟩
  · exact hT3 c hcT g (lt_of_lt_of_le hT0 hg)
  · exact (hctx (j + 1)).T3 c hcj g (lt_of_lt_of_le (chainA_top_lt hctx j) hg)

/-- Landing blocks below `υ_{a+ω·ω}`. -/
theorem chainA_land (hTa : upsilon a ≤ T0) : ∀ c' < upsilon (a + ω * ω), ∃ σ σ', UpsPt σ ∧
    c' < σ ∧ IsNext σ σ' ∧ σ' < upsilon (a + ω * ω) ∧
    (∀ a' b, σ < a' → b < σ' → (le1 a' b ↔ le1R a' b)) ∧ (∀ b, σ ≤ b → b < σ' → le1 σ b) ∧
    (∀ c d, c < d → σ < d → d < σ' → ¬ le2 c d) := by
  intro c' hc'
  have hj : ∃ j, c' < lpA a j := by
    rcases chainA_sup hTa hc' with hcT | ⟨j, hcj⟩
    · exact ⟨0, lt_of_le_of_lt hcT (hctx 0).Tτ⟩
    · exact ⟨j + 1, lt_of_le_of_lt hcj (hctx (j + 1)).Tτ⟩
  obtain ⟨j, hcj⟩ := hj
  have H := hctx j
  obtain ⟨σ, hσU, hσ, hστ⟩ := H.cof (max c' (topA a T0 j)) (max_lt hcj H.Tτ)
  obtain ⟨σ', hσn, -⟩ := exists_next hσU (hστ.trans H.τ1)
  have hσ'τ : σ' ≤ lpA a j := hσn.2.2 _ hστ H.τU
  have hTσ : topA a T0 j < σ := lt_of_le_of_lt (le_max_right _ _) hσ
  refine ⟨σ, σ', hσU, lt_of_le_of_lt (le_max_left _ _) hσ, hσn,
    lt_of_le_of_lt hσ'τ (chainA_lp_lt (a := a) j), ?_, ?_, ?_⟩
  · intro a' b ha' hb
    exact H.le1_lowτ a' b (hTσ.trans ha') (hb.le.trans hσ'τ)
  · intro b hb hbσ
    exact (H.le1_lowτ σ b hTσ (hbσ.le.trans hσ'τ)).2 (hσU.2 b hb)
  · intro c d hcd hσd hdσ
    exact H.no_pair_upto c d hcd (hTσ.trans hσd) (hdσ.le.trans hσ'τ)

/-- The pairs above `T₀` below `υ_{a+ω·ω}` end at block tops, which are closed. -/
theorem chainA_cap (hTa : upsilon a ≤ T0) : ∀ c d, T0 < c → c < d → d < upsilon (a + ω * ω) →
    le2 c d → ∀ x ≤ d, ∀ g, d < g → ¬ le1 x g := by
  intro c d hTc hcd hd h2 x hx g hg
  rcases chainA_sup hTa hd with hdT | ⟨j, hdj⟩
  · exact absurd (lt_of_lt_of_le (hTc.trans hcd) hdT) (lt_irrefl _)
  · obtain ⟨k, -, -, rfl⟩ := chainA_pairs hctx (j + 1) c d hcd (hTc.trans hcd) hdj h2
    exact (hctx (k + 1)).T3 x hx g hg

end Chain

/-! ## The restart contexts -/

/-- A restart context from a chain below it. -/
theorem rst_of_chain {a T0 r : Ordinal.{0}}
    (hctx : ∀ j : ℕ, BlkCtx (topA a T0 j) (lpA a j) (topA a T0 (j + 1)))
    (hT3 : ∀ c ≤ T0, ∀ g, T0 < g → ¬ le1 c g) (hTa : upsilon a ≤ T0) (hr : a + ω * ω = r)
    (hδ1 : upsilon (r + ω + 1) < Om1) :
    RstCtx (upsilon r) (upsilon (r + ω)) (upsilon (r + ω + 1)) := by
  have hr0 : 0 < r := by
    rw [← hr]; exact lt_of_lt_of_le (mul_pos omega0_pos omega0_pos) le_add_self
  have hlim : IsSuccLimit (r + ω) := isSuccLimit_add _ isSuccLimit_omega0
  have hT0r : T0 < upsilon r := by
    rw [← hr]; exact ((hctx 0).Tτ).trans (chainA_lp_lt (a := a) 0)
  refine ⟨upsPt_upsilon hr0, upsilon_normal.strictMono (lt_add_of_pos_right r omega0_pos),
    upsPt_upsilon (lt_of_lt_of_le hr0 le_self_add), ?_, hδ1, ?_, ?_, ?_, ?_, ?_⟩
  · have := upsilon_isNext (r + ω)
    rwa [succ_eq_add_one] at this
  · rw [← hr]; exact chainA_below hctx hT3 hTa
  · rw [← hr]; exact chainA_land hctx hTa
  · refine ⟨T0, hT0r, ?_⟩
    rw [← hr]; exact chainA_cap hctx hTa
  · intro l hl hρl hlτ
    have h1 : r < l := upsilon_normal.strictMono.lt_iff_lt.1 hρl
    have h2 : l ≤ r + ω := upsilon_normal.strictMono.le_iff_le.1 hlτ
    rw [limit_eq_add_omega hl h1 h2]
  · intro c' hc'
    obtain ⟨_, ⟨ι, hι, rfl⟩, hcx⟩ := (lt_isLUB_iff (upsilon_limit hlim)).1 hc'
    refine ⟨upsilon (succ ι), upsPt_upsilon (lt_of_le_of_lt zero_le (lt_succ ι)),
      hcx.trans (upsilon_normal.strictMono (lt_succ ι)), ?_⟩
    exact upsilon_normal.strictMono (hlim.succ_lt hι)

/-- The restart index `ω²·(h+1)`. -/
noncomputable def rI (h : ℕ) : Ordinal.{0} := ω * ω * ((h + 1 : ℕ) : Ordinal.{0})

/-- The base index of the blocks after the restart block of `ρ_{h+1}`. -/
noncomputable def aI (h : ℕ) : Ordinal.{0} := rI h + ω

theorem rI_succ (h : ℕ) : aI h + ω * ω = rI (h + 1) := by
  unfold aI rI
  have hw : (ω : Ordinal.{0}) + ω * ω = ω * ω := add_eq_right_iff_mul_omega0_le.2 le_rfl
  rw [add_assoc, hw]
  simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one]

theorem rI_zero : (0 : Ordinal.{0}) + ω * ω = rI 0 := by
  unfold rI; simp

theorem rI_count (h : ℕ) : upsilon (rI h + ω + 1) < Om1 := by
  have := ups_lt_Om1_3 (h + 1) 1 1
  simpa [rI] using this

theorem aI_add (h j : ℕ) : aI h + ω * (j : Ordinal.{0}) = ω * ω * ((h + 1 : ℕ) : Ordinal.{0}) +
    ω * ((j + 1 : ℕ) : Ordinal.{0}) := by
  unfold aI rI
  rw [add_assoc]
  congr 1
  rw [show ((j + 1 : ℕ) : Ordinal.{0}) = 1 + (j : Ordinal.{0}) by
    rw [Nat.add_comm, Nat.cast_add, Nat.cast_one]]
  rw [mul_add, mul_one]

theorem aI_count (h : ℕ) : ∀ j n : ℕ, upsilon (aI h + ω * (j : Ordinal.{0}) + n) < Om1 := by
  intro j n
  rw [aI_add]; exact ups_lt_Om1_3 (h + 1) (j + 1) n

/-- The block chain of Theorem B (base index `0`, lower end `0`). -/
theorem ctx0 : ∀ j : ℕ, BlkCtx (topA 0 0 j) (lpA 0 j) (topA 0 0 (j + 1)) :=
  ctxA 0 0 (fun c hc g hg => by rw [le_antisymm hc zero_le]; exact not_le1_zero hg)
    (by
      show (0 : Ordinal.{0}) < upsilon (0 + ω * ((0 : ℕ) : Ordinal.{0}) + ω)
      exact upsPt_upsilon (lpA_index_pos 0 0) |>.1)
    (fun l hl _ => pos_iff_ne_zero.2 hl.ne_bot)
    (ups_lt_Om1_off (by rw [upsilon_zero]; exact omega_pos 1))

/-- **The restart contexts**: `ρ_{h+1} = υ_{ω²·(h+1)}`, `τ = υ_{ω²·(h+1)+ω}`, `δ = υ_{ω²·(h+1)+ω+1}`,
together with the chain of the blocks after `δ + 1`. -/
theorem rstCtx : ∀ h : ℕ, RstCtx (upsilon (rI h)) (upsilon (rI h + ω)) (upsilon (rI h + ω + 1)) ∧
    ∀ j : ℕ, BlkCtx (topA (aI h) (upsilon (rI h + ω + 1) + 1) j) (lpA (aI h) j)
      (topA (aI h) (upsilon (rI h + ω + 1) + 1) (j + 1)) := by
  have chainOf : ∀ h : ℕ, RstCtx (upsilon (rI h)) (upsilon (rI h + ω)) (upsilon (rI h + ω + 1)) →
      ∀ j : ℕ, BlkCtx (topA (aI h) (upsilon (rI h + ω + 1) + 1) j) (lpA (aI h) j)
        (topA (aI h) (upsilon (rI h + ω + 1) + 1) (j + 1)) := by
    intro h R
    refine ctxA (aI h) _ R.T3succ ?_ ?_ (aI_count h)
    · show upsilon (rI h + ω + 1) + 1 < upsilon (aI h + ω * ((0 : ℕ) : Ordinal.{0}) + ω)
      have hI := indec_of_upsPt (upsPt_upsilon (lpA_index_pos (aI h) 0))
      refine hI.add_lt ?_ ?_
      · refine upsilon_normal.strictMono ?_
        unfold aI; simp only [Nat.cast_zero, mul_zero, add_zero]
        exact (add_lt_add_iff_left _).2 one_lt_omega0
      · exact one_lt_of_upsPt (upsPt_upsilon (lpA_index_pos (aI h) 0))
    · intro l _ hl
      have : upsilon (rI h + ω + 1) < upsilon l := lt_of_lt_of_le (lt_add_one _) hl.le
      have := upsilon_normal.strictMono.lt_iff_lt.1 this
      exact lt_of_le_of_lt le_self_add this
  intro h
  induction h with
  | zero =>
    have R := rst_of_chain ctx0 (fun c hc g hg => by
        rw [le_antisymm hc zero_le]; exact not_le1_zero hg)
      (by rw [upsilon_zero]) rI_zero (rI_count 0)
    exact ⟨R, chainOf 0 R⟩
  | succ h ih =>
    obtain ⟨R, C⟩ := ih
    have R' := rst_of_chain C R.T3succ
      (by
        show upsilon (rI h + ω) ≤ upsilon (rI h + ω + 1) + 1
        exact (R.next.1.le).trans le_self_add)
      (rI_succ h) (rI_count (h + 1))
    exact ⟨R', chainOf (h + 1) R'⟩


/-! ## Theorem B″ for every restart, the pairs, Lemma SK3 -/

/-- **Theorem B″ with Lemma TOP^h in `R₂^C`**, for the restart `ρ = υ_{ω²·(h+1)}` with
`τ = υ_{ω²·(h+1)+ω}`, `δ = υ_{ω²·(h+1)+ω+1}`: (1) no point below `ρ` is `≤₁` a point `≥ ρ` (so `ρ` has
no `<₁`-predecessor); (2) `ρ` has no `<₂`-successor; (3) `ρ ≤₁ γ` for `γ ∈ [ρ, δ]`; (4) (TOP) `ρ` is not
`≤₁` any `γ > δ + 1`; (5) `τ <₂ δ`, and `≤₁` is that of `R₁⁺` on `(ρ, δ]`; (6) no point `≤ δ + 1` is `≤₁`
a point `> δ + 1`; (7) the blocks after `δ + 1`: `υ_{a+ω·j+ω} <₂ υ_{a+ω·j+ω+1}` (`a = ω²·(h+1)+ω`) and
`≤₁` is that of `R₁⁺` inside each of them. -/
theorem thmB2_C (h : ℕ) :
    (∀ c < upsilon (rI h), ∀ g, upsilon (rI h) ≤ g → ¬ le1 c g) ∧
    (∀ b, upsilon (rI h) < b → ¬ le2 (upsilon (rI h)) b) ∧
    (∀ g, upsilon (rI h) ≤ g → g ≤ upsilon (rI h + ω + 1) → le1 (upsilon (rI h)) g) ∧
    (∀ g, upsilon (rI h + ω + 1) + 1 < g → ¬ le1 (upsilon (rI h)) g) ∧
    (le2 (upsilon (rI h + ω)) (upsilon (rI h + ω + 1)) ∧
      ∀ a b, upsilon (rI h) < a → b ≤ upsilon (rI h + ω + 1) → (le1 a b ↔ le1R a b)) ∧
    (∀ c ≤ upsilon (rI h + ω + 1) + 1, ∀ g, upsilon (rI h + ω + 1) + 1 < g → ¬ le1 c g) ∧
    (∀ j : ℕ, le2 (lpA (aI h) j) (topA (aI h) (upsilon (rI h + ω + 1) + 1) (j + 1)) ∧
      ∀ a b, topA (aI h) (upsilon (rI h + ω + 1) + 1) j < a →
        b ≤ topA (aI h) (upsilon (rI h + ω + 1) + 1) (j + 1) → (le1 a b ↔ le1R a b)) := by
  obtain ⟨R, C⟩ := rstCtx h
  exact ⟨R.below, R.noSucc, R.le1ρδ, R.top, ⟨R.pair, R.lowδ⟩, R.T3succ,
    fun j => ⟨(C j).pair, (C j).le1_lowβ⟩⟩

theorem not_lt1_succ {x g : Ordinal.{0}} (hx : 1 < x) (hg : x + 1 < g) : ¬ le1 (x + 1) g :=
  fun h => RstCtx.not_indec_succ x hx (indec_of_lt1 h hg)

theorem not_lt1R_succ {x g : Ordinal.{0}} (hx : 1 < x) (hg : x + 1 < g) : ¬ le1R (x + 1) g :=
  fun h => RstCtx.not_indec_succ x hx (indec_of_lt1R h hg)

theorem not_lt2_succ {x c : Ordinal.{0}} (hx : 1 < x) (hc : c < x + 1) : ¬ le2 c (x + 1) :=
  fun h => RstCtx.not_indec_succ x hx (indec_of_lt2_right h hc).1

/-- `υ_{ω³}` is the supremum of the restarts. -/
theorem exists_rst_above {d : Ordinal.{0}} (hd : d < upsilon (ω * ω * ω)) :
    ∃ k : ℕ, d < upsilon (ω * ω * (k : Ordinal.{0})) := by
  have hlim : IsSuccLimit (ω * ω * ω : Ordinal.{0}) :=
    isSuccLimit_mul_right (mul_pos omega0_pos omega0_pos) isSuccLimit_omega0
  obtain ⟨_, ⟨ι, hι, rfl⟩, hdx⟩ := (lt_isLUB_iff (upsilon_limit hlim)).1 hd
  obtain ⟨c', hc', hιc⟩ := (lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 hι
  obtain ⟨k, rfl⟩ := lt_omega0.1 hc'
  exact ⟨k, hdx.trans (upsilon_normal.strictMono hιc)⟩

/-- Where a point below `υ_{ω³}` lies: below `ρ₁ = υ_{ω²}`, or in `[ρ_{h+1}, ρ_{h+2})`. -/
theorem region {d : Ordinal.{0}} (hd : d < upsilon (ω * ω * ω)) :
    d < upsilon (ω * ω) ∨ ∃ h : ℕ, upsilon (rI h) ≤ d ∧ d < upsilon (rI (h + 1)) := by
  classical
  have hex := exists_rst_above hd
  set k := Nat.find hex with hk
  have hkd : d < upsilon (ω * ω * (k : Ordinal.{0})) := Nat.find_spec hex
  rcases k with _ | _ | h
  · simp only [Nat.cast_zero, mul_zero, upsilon_zero] at hkd
    exact absurd hkd (not_lt.2 zero_le)
  · left; simpa using hkd
  · right
    refine ⟨h, ?_, ?_⟩
    · have := Nat.find_min hex (show h + 1 < Nat.find hex by omega)
      exact not_lt.1 this
    · show d < upsilon (ω * ω * ((h + 1 + 1 : ℕ) : Ordinal.{0}))
      exact hkd

theorem lp_eq (j : ℕ) : lp j = upsilon (ω * ω * ((0 : ℕ) : Ordinal.{0}) + ω * j + ω) := by
  simp [lp]

/-- **The `<₂`-pairs below `υ_{ω³}`** in `R₂^C`: exactly `υ_ξ <₂ υ_{ξ+1}` for
`ξ = ω²·h + ω·j + ω`. -/
theorem pairs_lt_w3 {c d : Ordinal.{0}} (hcd : c < d) (hd : d < upsilon (ω * ω * ω)) :
    le2 c d ↔ ∃ h j : ℕ, c = upsilon (ω * ω * (h : Ordinal.{0}) + ω * j + ω) ∧
      d = upsilon (ω * ω * (h : Ordinal.{0}) + ω * j + ω + 1) := by
  constructor
  · intro h2
    rcases region hd with hd1 | ⟨h, hρd, hdρ⟩
    · obtain ⟨j, rfl, rfl⟩ := (thmB_C.2.1 c d hcd hd1).1 h2
      exact ⟨0, j, by simp [lp], by simp [top]⟩
    obtain ⟨R, C⟩ := rstCtx h
    have hδ1 : (1 : Ordinal.{0}) < upsilon (rI h + ω + 1) := one_lt_of_upsPt R.next.2.1
    rcases eq_or_lt_of_le hρd with e | hρd'
    · rw [← e] at hcd h2
      exact absurd (le2_le1 h2) (R.below c hcd _ le_rfl)
    rcases lt_or_ge d (upsilon (rI h + ω + 1)) with hdδ | hδd
    · exact absurd h2 (R.noPairGap c d hcd hρd' hdδ)
    rcases eq_or_lt_of_le hδd with e | hδd'
    · subst e
      refine ⟨h + 1, 0, ?_, ?_⟩
      · rw [R.pairs_at_top hcd h2]; simp [rI]
      · simp [rI]
    rcases eq_or_lt_of_le (Order.add_one_le_of_lt hδd') with e | hδ1d
    · rw [← e] at hcd h2
      exact absurd h2 (not_lt2_succ hδ1 hcd)
    have hTa : upsilon (aI h) ≤ upsilon (rI h + ω + 1) + 1 :=
      (R.next.1.le).trans le_self_add
    rw [← rI_succ h] at hdρ
    rcases chainA_sup hTa hdρ with hdT | ⟨j, hdj⟩
    · exact absurd hδ1d (not_lt.2 hdT)
    obtain ⟨k, -, rfl, rfl⟩ := chainA_pairs C (j + 1) c d hcd hδ1d hdj h2
    refine ⟨h + 1, k + 1, ?_, ?_⟩
    · show upsilon (aI h + ω * (k : Ordinal.{0}) + ω) = _
      rw [aI_add]
    · show upsilon (aI h + ω * (k : Ordinal.{0}) + ω + 1) = _
      rw [aI_add]
  · rintro ⟨h, j, rfl, rfl⟩
    rcases h with _ | h
    · have := (ctx0 j).pair
      simpa [lpA, topA] using this
    rcases j with _ | j
    · have := (rstCtx h).1.pair
      simpa [rI] using this
    · have := ((rstCtx h).2 j).pair
      have e1 := aI_add h j
      simp only [lpA, topA] at this
      rw [e1] at this
      exact this

/-- A non-`υ`-point inside a block `(T, β]` (`β` a countable `υ`-point, `≤₁` of `R₂^C` = `≤₁` of
`R₁⁺` on `(T, β]`) has its `R₁⁺` reach in `R₂^C`. -/
theorem skel_block {T β α : Ordinal.{0}} (hβU : UpsPt β) (hβ1 : β < Om1) (hTα : T < α)
    (hαβ : α ≤ β) (hnu : ¬ UpsPt α)
    (hlow : ∀ a b, T < a → b ≤ β → (le1 a b ↔ le1R a b)) : ∀ γ, le1 α γ ↔ le1R α γ := by
  intro γ
  rcases le_or_gt γ β with hγ | hγ
  · exact hlow α γ hTα hγ
  have hαβ' : α < β := lt_of_le_of_ne hαβ (fun e => hnu (e ▸ hβU))
  have hα0 : 0 < α := lt_of_le_of_lt zero_le hTα
  have key : ¬ le1R α (β + 1) := fun h =>
    hnu ⟨hα0, (le1R_lt_ups hβU hαβ' le_self_add).1 h⟩
  constructor
  · intro h
    exact absurd (inc1 (Om1_add_lt hβ1 (lt_trans one_lt_omega0 omega0_lt_omega_one))
      (le1_of_le_of_le1 (hαβ.trans le_self_add) (Order.add_one_le_of_lt hγ) h)) key
  · intro h
    exact absurd (le1R_of_le (hαβ.trans le_self_add) (Order.add_one_le_of_lt hγ) h) key

/-- **Lemma SK3 in `R₂^C`**: below `υ_{ω³}`, every `<₂`-pair is `(υ_ξ, υ_{ξ+1})`, and every point
that is not a `υ`-point has its `R₁⁺` reach (`α ≤₁ γ` in `R₂^C` iff in `R₁⁺`, for every `γ`). -/
theorem sk3_C :
    (∀ c d, c < d → d < upsilon (ω * ω * ω) → le2 c d → ∃ ξ, c = upsilon ξ ∧
      d = upsilon (ξ + 1)) ∧
    (∀ α, α < upsilon (ω * ω * ω) → ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) := by
  classical
  refine ⟨fun c d hcd hd h2 => ?_, fun α hα hnu γ => ?_⟩
  · obtain ⟨h, j, rfl, rfl⟩ := (pairs_lt_w3 hcd hd).1 h2
    exact ⟨_, rfl, rfl⟩
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
  have hα0' : 0 < α := pos_iff_ne_zero.2 hα0
  rcases region hα with hα1 | ⟨h, hρα, hαρ⟩
  · -- below `υ_{ω²}`: the blocks of Theorem B
    obtain ⟨j0, hj0⟩ := exists_top_above hα1
    have hex : ∃ j, α ≤ top j := ⟨j0, hj0⟩
    set j := Nat.find hex with hj
    have hαj : α ≤ top j := Nat.find_spec hex
    rcases j with _ | j
    · exact absurd hαj (not_le.2 hα0')
    have hTj : top j < α := not_le.1 (Nat.find_min hex (show j < Nat.find hex by omega))
    have H := ctxB j
    exact skel_block H.next.2.1 H.β1 hTj hαj hnu H.le1_lowβ γ
  obtain ⟨R, C⟩ := rstCtx h
  have hδ1 : (1 : Ordinal.{0}) < upsilon (rI h + ω + 1) := one_lt_of_upsPt R.next.2.1
  rcases eq_or_lt_of_le hρα with e | hρα'
  · exact absurd (e ▸ R.ρU) hnu
  rcases le_or_gt α (upsilon (rI h + ω + 1)) with hαδ | hδα
  · exact skel_block R.next.2.1 R.δ1 hρα' hαδ hnu R.lowδ γ
  rcases eq_or_lt_of_le (Order.add_one_le_of_lt hδα) with e | hδ1α
  · rw [← e]
    rcases lt_trichotomy γ (upsilon (rI h + ω + 1) + 1) with hγ | e' | hγ
    · exact ⟨fun h => absurd (le1_le h) (not_le.2 hγ), fun h => absurd (le1R_le h) (not_le.2 hγ)⟩
    · rw [e']; exact ⟨fun _ => le1R_refl _, fun _ => le1_refl _⟩
    · exact ⟨fun h => absurd h (not_lt1_succ hδ1 hγ), fun h => absurd h (not_lt1R_succ hδ1 hγ)⟩
  have hTa : upsilon (aI h) ≤ upsilon (rI h + ω + 1) + 1 := (R.next.1.le).trans le_self_add
  rw [← rI_succ h] at hαρ
  have hex : ∃ j, α ≤ topA (aI h) (upsilon (rI h + ω + 1) + 1) j := by
    rcases chainA_sup hTa hαρ with hαT | ⟨j, hαj⟩
    · exact absurd hδ1α (not_lt.2 hαT)
    · exact ⟨j + 1, hαj⟩
  set j := Nat.find hex with hj
  have hαj : α ≤ topA (aI h) (upsilon (rI h + ω + 1) + 1) j := Nat.find_spec hex
  rcases j with _ | j
  · exact absurd hδ1α (not_lt.2 hαj)
  have hTj : topA (aI h) (upsilon (rI h + ω + 1) + 1) j < α :=
    not_le.1 (Nat.find_min hex (show j < Nat.find hex by omega))
  have H := C j
  exact skel_block H.next.2.1 H.β1 hTj hαj hnu H.le1_lowβ γ

end Googology.Trans.PoR.InaccPsi.R2
