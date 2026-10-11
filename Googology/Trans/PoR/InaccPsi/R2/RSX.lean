import Googology.Trans.PoR.InaccPsi.R2.BlkX

/-!
# Theorem BLK^Ξ in `R₂^C`, part 2: the exact reaches `lh(ρ_λ) = δ_λ + c*(λ)` (Lemma RS_λ, with FRAG)

* `rs_rst` (**Lemma RS with a restart target**, the project's proof of Lemmas RS^O / RS_λ, for
  the terms `x·m + k`): for the restart `ρ = υ_r` with first pair `τ <₂ δ`, a term `t = tm m k`
  (`k < ρ`), and targets `μ` with `ρ_μ` above any given `κ' < ρ` and `ρ_μ ≤₁ γ` for every
  `γ ∈ [ρ_μ, δ_μ + t(ρ_μ)]`: `ρ ≤₁ δ + t(ρ) + 1`.  A finite `Y ⊆ [ρ, δ + t(ρ)]` is copied by a FRAG
  map (Theorem FRAG, `frag`) that moves the bases `υ_r, …, υ_{r+N}, τ, δ` to
  `υ_μ, …, υ_{μ+N}, τ_μ, δ_μ` and fixes the parameters below `κ`; it keeps `+`, so
  `δ + t(ρ) ↦ δ_μ + t(ρ_μ)` (the project's Lemma EXACT for these terms); then the leading-term
  map of Theorem CC-F makes the image closed.  The covering conditions: `ρ ≤₁ y ↦ ρ_μ ≤₁ ψ y` (the
  target's reach); `≤₁` on `(ρ, δ]` is that of `R₁⁺` on both sides; the points of `(δ, δ + t(ρ)]` are
  decomposable; the only pair is `τ <₂ δ ↦ τ_μ <₂ δ_μ`.
* `rs_allO`: for an offset specification `OffSpec O B`, `ρ_λ ≤₁ δ_λ + O(λ)` for every restart index
  `λ < B` (induction on `λ`; a successor index by stage 3's `rs_gen` with a block target, a limit
  index by `rs_rst` with the input `RsIn O λ`); `reach_allO` (with Lemma TOP: `lh(ρ_λ) = δ_λ + O(λ)`);
  `blk_gen` (the block theorem below `υ_B`).
* `rs_all`, `reach_all`, `blkXi` (**Theorem BLK^Ξ**): the case `O = c*`, `B = Ξ_ω + ω²`;
  `reach_opow` (`lh(ρ_{ω^e}) = δ + (e − 1)`), `reach_w3`, `reach_ww`, `reach_Xi`, `reach_XiW`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-- **Lemma RS with a restart target** (see the module docstring). -/
theorem rs_rst {r : Ordinal.{0}} (h : RstK (upsilon r) (upsilon (r + ω)) (upsilon (r + ω + 1)))
    {m : ℕ} {k : Ordinal.{0}} (hk : k < upsilon r)
    (htarget : ∀ κ' < upsilon r, ∃ μ, κ' < upsilon μ ∧ upsilon (μ + ω + 1) < upsilon r ∧
      RstK (upsilon μ) (upsilon (μ + ω)) (upsilon (μ + ω + 1)) ∧
      ∀ g, upsilon μ ≤ g → g ≤ upsilon (μ + ω + 1) + tm m k (upsilon μ) → le1 (upsilon μ) g) :
    le1 (upsilon r) (upsilon (r + ω + 1) + tm m k (upsilon r) + 1) := by
  classical
  have hρτ := h.ρτ
  have hτδ := h.τδ
  have hρδ : upsilon r < upsilon (r + ω + 1) := hρτ.trans hτδ
  have hδ1 := h.δ1
  have hρ0 : 0 < upsilon r := h.ρU.1
  have hρI := indec_of_upsPt h.ρU
  have hδI := indec_of_upsPt h.next.2.1
  set ρ := upsilon r with hρdef
  set δ := upsilon (r + ω + 1) with hδdef
  set cρ := tm m k ρ with hcρdef
  have hmul : ∀ j : ℕ, ρ * (j : Ordinal.{0}) < δ := RstK.mul_nat_lt hδI hρδ
  have hmulk : ∀ j : ℕ, ρ * (j : Ordinal.{0}) + k < δ := fun j =>
    hδI.add_lt (hmul j) (hk.trans hρδ)
  have hcδ : cρ < δ := hmulk m
  set g' := δ + cρ with hg'def
  have hg'1 : g' < Om1 := Om1_add_lt hδ1 (hcδ.trans hδ1)
  -- the next `υ`-point after `δ`
  have hnx := upsilon_isNext (r + ω + 1)
  have hg'nx : g' < upsilon (succ (r + ω + 1)) :=
    (indec_of_upsPt hnx.2.1).add_lt hnx.1 (hcδ.trans hnx.1)
  refine le1_iff.2 ⟨hρδ.le.trans (le_self_add.trans le_self_add), fun X Y hX hY hXY => ?_⟩
  have hYg : ∀ y ∈ Y, ρ ≤ y ∧ y ≤ g' := fun y hy =>
    ⟨(hY y hy).1, Order.lt_add_one_iff.1 (hY y hy).2⟩
  -- the hereditary parameters
  set Pm : Finset Ordinal.{0} := (Finset.range m).image (fun i => ρ * ((i + 1 : ℕ) : Ordinal.{0}))
    with hPm
  set Pk : Finset Ordinal.{0} :=
    (Finset.range m).image (fun i => ρ * ((i + 1 : ℕ) : Ordinal.{0}) + k) with hPk
  set W : Finset Ordinal.{0} := ({k, ρ, δ, g'} ∪ Pm) ∪ Pk with hWdef
  set F0 := (X ∪ Y ∪ W).biUnion (hpar ρ) with hF0
  have hAF : ∀ z ∈ X ∪ Y ∪ W, z ∈ F0 := fun z hz =>
    Finset.mem_biUnion.2 ⟨z, hz, mem_hpar_self _ _⟩
  have hXYF : ∀ z ∈ X ∪ Y, z ∈ F0 := fun z hz => hAF z (Finset.mem_union_left _ hz)
  have hWF : ∀ z ∈ W, z ∈ F0 := fun z hz => hAF z (Finset.mem_union_right _ hz)
  have hkF : k ∈ F0 := hWF k (by simp [hWdef])
  have hρF : ρ ∈ F0 := hWF ρ (by simp [hWdef])
  have hPmF : ∀ i < m, ρ * ((i + 1 : ℕ) : Ordinal.{0}) ∈ F0 := fun i hi => hWF _ (by
    simp only [hWdef, Finset.mem_union]
    exact Or.inl (Or.inr (Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩)))
  have hPkF : ∀ i < m, ρ * ((i + 1 : ℕ) : Ordinal.{0}) + k ∈ F0 := fun i hi => hWF _ (by
    simp only [hWdef, Finset.mem_union]
    exact Or.inr (Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩))
  have hδF : δ ∈ F0 := hWF δ (by simp [hWdef])
  have hg'F : g' ∈ F0 := hWF g' (by simp [hWdef])
  have hcF : cρ ∈ F0 := by
    rcases m with _ | m
    · rw [hcρdef, tm_zero]; exact hkF
    · exact hPkF m (Nat.lt_succ_self m)
  have hF0g : ∀ z ∈ F0, z ≤ g' := by
    intro z hz
    obtain ⟨w, hw, hzw⟩ := Finset.mem_biUnion.1 hz
    refine (hpar_le _ w z hzw).trans ?_
    rcases Finset.mem_union.1 hw with hw | hw
    · rcases Finset.mem_union.1 hw with hwX | hwY
      · exact ((hX w hwX).trans hρδ).le.trans le_self_add
      · exact (hYg w hwY).2
    · simp only [hWdef, hPm, hPk, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_image, Finset.mem_range] at hw
      rcases hw with ((rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩
      · exact (hk.trans hρδ).le.trans le_self_add
      · exact hρδ.le.trans le_self_add
      · exact le_self_add
      · exact le_rfl
      · exact (hmul _).le.trans le_self_add
      · exact (hmulk _).le.trans le_self_add
  have hF0cl : ∀ z ∈ F0, ρ ≤ z → ∀ p ∈ Par (sb z) z, p < z → p ∈ F0 := by
    intro z hz hρz p hp hpz
    obtain ⟨w, hw, hzw⟩ := Finset.mem_biUnion.1 hz
    exact Finset.mem_biUnion.2 ⟨w, hw, hpar_closed _ w z hzw hρz p hp hpz⟩
  -- the base `κ`
  have hsup : (insert 0 (F0.filter (· < ρ))).sup id < ρ := by
    rw [Finset.sup_lt_iff hρ0]
    intro b hb
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact hρ0
    · exact (Finset.mem_filter.1 hb).2
  obtain ⟨κ, κ', hκU, hκ, hκn, hκ'ρ, -, -, -⟩ := h.land _ hsup
  have hκρ : κ < ρ := hκn.1.trans hκ'ρ
  have hκ1 : κ < Om1 := hκρ.trans h.ρ1
  have hLoκ : ∀ z ∈ F0, z < ρ → z < κ := fun z hz hzρ =>
    lt_of_le_of_lt (Finset.le_sup (f := id)
      (Finset.mem_insert_of_mem (show z ∈ F0.filter (· < ρ) from
        Finset.mem_filter.2 ⟨hz, hzρ⟩))) hκ
  -- the number `N` of segments below `τ`
  have hlimτ : IsSuccLimit (r + ω) := isSuccLimit_add r isSuccLimit_omega0
  have hN : ∃ N : ℕ, ∀ z ∈ F0, z < upsilon (r + ω) → z < upsilon (r + (N : Ordinal.{0})) := by
    have hs : (insert 0 (F0.filter (· < upsilon (r + ω)))).sup id < upsilon (r + ω) := by
      rw [Finset.sup_lt_iff (hρ0.trans hρτ)]
      intro b hb
      rcases Finset.mem_insert.1 hb with rfl | hb
      · exact hρ0.trans hρτ
      · exact (Finset.mem_filter.1 hb).2
    obtain ⟨_, ⟨ι, hι, rfl⟩, hsx⟩ := (lt_isLUB_iff (upsilon_limit hlimτ)).1 hs
    obtain ⟨d, hd, hιd⟩ := (lt_add_iff_of_isSuccLimit isSuccLimit_omega0).1 hι
    obtain ⟨n, rfl⟩ := lt_omega0.1 hd
    refine ⟨n, fun z hz hzτ => ?_⟩
    have hz' : z ≤ (insert 0 (F0.filter (· < upsilon (r + ω)))).sup id :=
      Finset.le_sup (f := id) (Finset.mem_insert_of_mem
        (show z ∈ F0.filter (· < upsilon (r + ω)) from Finset.mem_filter.2 ⟨hz, hzτ⟩))
    exact lt_of_le_of_lt hz' (hsx.trans (upsilon_normal.strictMono hιd))
  obtain ⟨N, hNz⟩ := hN
  -- the bases `b`
  set bb : ℕ → Ordinal.{0} := fun j => upsilon (ix r 0 N j) with hbdef
  have hb0 : bb 0 = ρ := by simp [hbdef, hρdef, ix_low (Nat.zero_le N)]
  have hbN1 : bb (N + 1) = upsilon (r + ω) := by simp [hbdef, ix_N1]
  have hbN2 : bb (N + 2) = δ := by simp [hbdef, hδdef, ix_N2]
  have hblow : ∀ j ≤ N, bb j = upsilon (r + (j : Ordinal.{0})) := by
    intro j hj; simp [hbdef, ix_low hj]
  have hbmono : ∀ i j, i < j → j < N + 3 → bb i < bb j := fun i j hij hj =>
    upsilon_normal.strictMono (ix_lt hij (by omega))
  have hbge : ∀ j < N + 3, ρ ≤ bb j := fun j hj => by
    rw [← hb0]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact le_rfl
    · exact (hbmono 0 j hj0 hj).le
  have hble : ∀ j < N + 3, bb j ≤ δ := fun j hj => by
    rw [← hbN2]
    rcases eq_or_lt_of_le (show j ≤ N + 2 by omega) with rfl | hlt
    · exact le_rfl
    · exact (hbmono j (N + 2) hlt (by omega)).le
  have hbU : ∀ j < N + 3, UpsPt (bb j) ∧ bb j < Om1 := by
    intro j hj
    refine ⟨?_, lt_of_le_of_lt (hble j hj) hδ1⟩
    rcases upsilon_mem (ix r 0 N j) with h0 | hU
    · exact absurd h0 (ne_of_gt (lt_of_lt_of_le hρ0 (hbge j hj)))
    · exact hU
  have hbC : Chain κ bb (N + 3) :=
    ⟨hκU, hκ1, hbU, hbmono, fun j hj => lt_of_lt_of_le hκρ (hbge j hj)⟩
  -- the segments of the points of `F0` above `ρ`
  have hseg : ∀ z ∈ F0, ρ ≤ z → ∃ j < N + 3, InSeg (bb j) z := by
    intro z hz hρz
    have hzg := hF0g z hz
    have hz1 : z < Om1 := lt_of_le_of_lt hzg hg'1
    rcases lt_or_ge z (upsilon (r + ω)) with hzτ | hτz
    · have hex : ∃ n : ℕ, z < upsilon (r + ((n + 1 : ℕ) : Ordinal.{0})) :=
        ⟨N, (hNz z hz hzτ).trans (upsilon_normal.strictMono
          ((add_lt_add_iff_left r).2 (by exact_mod_cast Nat.lt_succ_self N)))⟩
      set n0 := Nat.find hex with hn0
      have hzn : z < upsilon (r + ((n0 + 1 : ℕ) : Ordinal.{0})) := Nat.find_spec hex
      have hn0N : n0 ≤ N := by
        by_contra hgt
        have := Nat.find_min hex (show N < n0 by omega)
        exact this (lt_of_lt_of_le (hNz z hz hzτ) (upsilon_normal.strictMono.monotone
          ((add_le_add_iff_left r).2 (by exact_mod_cast Nat.le_succ N))))
      have hbz : bb n0 ≤ z := by
        rw [hblow n0 hn0N]
        rcases Nat.eq_zero_or_pos n0 with h0 | hpos
        · rw [h0]; simpa using hρz
        · obtain ⟨n, hn⟩ : ∃ n, n0 = n + 1 := ⟨n0 - 1, by omega⟩
          have := Nat.find_min hex (show n < n0 by omega)
          rw [hn]; exact not_lt.1 this
      refine ⟨n0, by omega, hbz, hz1, fun u hu huU => ?_⟩
      have hnx' := upsilon_isNext (r + (n0 : Ordinal.{0}))
      rw [succ_eq_add_one] at hnx'
      rw [hblow n0 hn0N] at hu
      have := hnx'.2.2 u hu huU
      refine lt_of_lt_of_le hzn (le_of_eq_of_le ?_ this)
      push_cast; rw [add_assoc]
    · rcases lt_or_ge z δ with hzδ | hδz
      · refine ⟨N + 1, by omega, ?_⟩
        rw [hbN1]
        exact ⟨hτz, hz1, fun u hu huU => lt_of_lt_of_le hzδ (h.next.2.2 u hu huU)⟩
      · refine ⟨N + 2, by omega, ?_⟩
        rw [hbN2]
        exact ⟨hδz, hz1, fun u hu huU => lt_of_le_of_lt hzg (lt_of_lt_of_le hg'nx (hnx.2.2 u hu huU))⟩
  -- `F0` lies in the domain of FRAG
  have hF0DD : (↑F0 : Set Ordinal.{0}) ⊆ DD κ bb (N + 3) := by
    suffices H : ∀ z, z ∈ F0 → z ∈ DD κ bb (N + 3) from fun z hz => H z hz
    intro z
    induction z using WellFoundedLT.induction with
    | ind z IH =>
    intro hz
    rcases lt_or_ge z ρ with hzρ | hρz
    · exact Iio_sub_DD _ (hLoκ z hz hzρ)
    obtain ⟨j, hj, hs⟩ := hseg z hz hρz
    have hU := hbU j hj
    have hzT : z ∈ Tset (bb j) := ((inSeg_iff hU.1 hU.2).1 hs).2.2
    have hsb : sb z = bb j := sb_eq hU.1 hs
    have hPar : ↑(Par (bb j) z) ⊆ ClS (DD κ bb j) := by
      intro p hp
      have hpb : p < bb j := Par_sub (upsPt_inE hU.1) hU.2 hzT hp
      have hpz : p < z := lt_of_lt_of_le hpb hs.1
      have hpF : p ∈ F0 := hF0cl z hz hρz p (by rw [hsb]; exact Finset.mem_coe.1 hp) hpz
      exact ClS.sub _ (DD_down hbC (IH p hpz hpF) hj hpb)
    exact DD_mono (show j + 1 ≤ N + 3 by omega) (Or.inr ⟨hs, hzT, hPar⟩)
  -- the target restart
  obtain ⟨μ, hκμ, hδμρ, Rμ, hle1μ⟩ := htarget κ hκρ
  set cc : ℕ → Ordinal.{0} := fun j => upsilon (ix μ 0 N j) with hcdef
  have hc0 : cc 0 = upsilon μ := by simp [hcdef, ix_low (Nat.zero_le N)]
  have hcN1 : cc (N + 1) = upsilon (μ + ω) := by simp [hcdef, ix_N1]
  have hcN2 : cc (N + 2) = upsilon (μ + ω + 1) := by simp [hcdef, ix_N2]
  have hcmono : ∀ i j, i < j → j < N + 3 → cc i < cc j := fun i j hij hj =>
    upsilon_normal.strictMono (ix_lt hij (by omega))
  have hcge : ∀ j < N + 3, upsilon μ ≤ cc j := by
    intro j hj
    rw [← hc0]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact le_rfl
    · exact (hcmono 0 j hj0 hj).le
  have hcle : ∀ j < N + 3, cc j ≤ upsilon (μ + ω + 1) := fun j hj =>
    upsilon_normal.strictMono.monotone (ix_top (show j ≤ N + 2 by omega))
  have hμ0 : 0 < upsilon μ := lt_of_le_of_lt zero_le hκμ
  have hcU : ∀ j < N + 3, UpsPt (cc j) ∧ cc j < Om1 := by
    intro j hj
    refine ⟨?_, lt_of_le_of_lt (hcle j hj) Rμ.δ1⟩
    rcases upsilon_mem (ix μ 0 N j) with h0 | hU
    · exact absurd h0 (ne_of_gt (lt_of_lt_of_le hμ0 (hcge j hj)))
    · exact hU
  have hcC : Chain κ cc (N + 3) :=
    ⟨hκU, hκ1, hcU, hcmono, fun j hj => lt_of_lt_of_le hκμ (hcge j hj)⟩
  -- FRAG
  obtain ⟨Ψ, Q1, -, Q3, Q4, Q5, -, -⟩ := frag hbC hcC F0 hF0DD
  have hΨmono : StrictMonoOn Ψ ↑F0 := Q4.2.1
  have hΨadd : ∀ x ∈ F0, ∀ y ∈ F0, ∀ z ∈ F0, x + y = z → Ψ x + Ψ y = Ψ z := fun x hx y hy z hz e =>
    (Q4.2.2 x hx y hy z hz).1 e
  have hΨρ : Ψ ρ = upsilon μ := by
    have := Q3 0 (by omega) (by rw [hb0]; exact hρF); rwa [hb0, hc0] at this
  have hΨτ : upsilon (r + ω) ∈ F0 → Ψ (upsilon (r + ω)) = upsilon (μ + ω) := fun hτF => by
    have := Q3 (N + 1) (by omega) (by rw [hbN1]; exact hτF); rwa [hbN1, hcN1] at this
  have hΨδ : Ψ δ = upsilon (μ + ω + 1) := by
    have := Q3 (N + 2) (by omega) (by rw [hbN2]; exact hδF); rwa [hbN2, hcN2] at this
  have hΨk : Ψ k = k := Q1 k hkF (hLoκ k hkF hk)
  have hΨPm : ∀ i < m, Ψ (ρ * ((i + 1 : ℕ) : Ordinal.{0})) =
      upsilon μ * ((i + 1 : ℕ) : Ordinal.{0}) := by
    intro i
    induction i with
    | zero => intro _; simpa using hΨρ
    | succ i ih =>
      intro hi
      have he : ρ * ((i + 1 + 1 : ℕ) : Ordinal.{0}) = ρ * ((i + 1 : ℕ) : Ordinal.{0}) + ρ := by
        rw [Nat.cast_succ (i + 1), mul_add_one]
      have := hΨadd _ (hPmF i (by omega)) ρ hρF _ (hPmF (i + 1) hi) he.symm
      rw [← this, ih (by omega), hΨρ, Nat.cast_succ (i + 1), mul_add_one]
  have hΨc : Ψ cρ = tm m k (upsilon μ) := by
    rcases m with _ | m
    · rw [hcρdef, tm_zero, tm_zero]; exact hΨk
    · have := hΨadd _ (hPmF m (Nat.lt_succ_self m)) k hkF _ (hPkF m (Nat.lt_succ_self m)) rfl
      rw [hΨPm m (Nat.lt_succ_self m), hΨk] at this
      exact this.symm
  have hΨg' : Ψ g' = upsilon (μ + ω + 1) + tm m k (upsilon μ) := by
    rw [← hΨδ, ← hΨc]; exact (hΨadd δ hδF cρ hcF g' hg'F rfl).symm
  have hΨup : ∀ z ∈ F0, ρ ≤ z → upsilon μ ≤ Ψ z ∧ Ψ z ≤ upsilon (μ + ω + 1) + tm m k (upsilon μ) := by
    intro z hz hρz
    refine ⟨?_, ?_⟩
    · rw [← hΨρ]; exact hΨmono.monotoneOn hρF hz hρz
    · rw [← hΨg']; exact hΨmono.monotoneOn hz hg'F (hF0g z hz)
  have hΨlowδ : ∀ z ∈ F0, z ≤ δ → Ψ z ≤ upsilon (μ + ω + 1) := fun z hz hzδ => by
    rw [← hΨδ]; exact hΨmono.monotoneOn hz hδF hzδ
  -- the leading-term map on `X ∪ Y`
  have hAF0 : (↑(X ∪ Y) : Set Ordinal.{0}) ⊆ ↑F0 := fun z hz => hXYF z (Finset.mem_coe.1 hz)
  have hΨA : ArithIso ↑(X ∪ Y) (Ψ '' ↑(X ∪ Y)) Ψ :=
    ⟨(Q4.2.1.mono hAF0).injOn.bijOn_image, Q4.2.1.mono hAF0,
      fun x hx y hy z hz => Q4.2.2 x (hAF0 hx) y (hAF0 hy) z (hAF0 hz)⟩
  obtain ⟨hψ, hψc, hψle, hψeq, hψfix⟩ := close_map hXY hΨA
  set ψ := ext (fun a => mc (Ψ a)) with hψdef
  have hψX : ∀ x ∈ X, ψ x = x := by
    intro x hx
    refine hψfix x (by simp [hx]) (fun a ha => Q1 a ?_ ?_)
    · exact hXYF a (hXY.pc_mem x (by simp [hx]) a ha)
    · exact lt_of_le_of_lt (le_of_mem_pc ha) (hLoκ x (hXYF x (by simp [hx])) (hX x hx))
  have hψYb : ∀ y ∈ Y, ψ y ≤ upsilon (μ + ω + 1) + tm m k (upsilon μ) := fun y hy =>
    (hψle y (by simp [hy])).trans (hΨup y (hXYF y (by simp [hy])) (hYg y hy).1).2
  have hXlt : ∀ c' ∈ (↑(X ∪ Y) : Set Ordinal.{0}), ∀ d ∈ X, c' ≤ d → c' ∈ X := by
    intro c' hc' d hd hcd
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hc') with hc' | hc'
    · exact hc'
    · exact absurd (lt_of_le_of_lt hcd (hX d hd)) (not_lt.2 (hYg c' hc').1)
  have hψbk : ∀ j < N + 3, bb j ∈ (↑(X ∪ Y) : Set Ordinal.{0}) → ψ (bb j) = cc j := by
    intro j hj hbA
    have hΨbk := Q3 j hj (hAF0 hbA)
    rw [hψeq (bb j) hbA (indec_of_upsPt (hbU j hj).1)
      (by rw [hΨbk]; exact indec_of_upsPt (hcU j hj).1), hΨbk]
  have hψmono : StrictMonoOn ψ ↑(X ∪ Y) := hψ.2.1
  have hcov : Cov R2C R2C ↑(X ∪ Y) (ψ '' ↑(X ∪ Y)) ψ := by
    refine ⟨hψ, ?_, ?_⟩
    · intro c' hc' d hd hcd
      change le1 c' d at hcd
      change le1 (ψ c') (ψ d)
      rcases eq_or_lt_of_le (le1_le hcd) with e | hlt
      · rw [e]; exact le1_refl _
      rcases Finset.mem_union.1 (Finset.mem_coe.1 hd) with hdX | hdY
      · rw [hψX c' (hXlt c' hc' d hdX hlt.le), hψX d hdX]; exact hcd
      rcases lt_trichotomy c' ρ with hcρ | e | hρc
      · exact absurd hcd (h.below c' hcρ d (hYg d hdY).1)
      · have hρA : bb 0 ∈ (↑(X ∪ Y) : Set Ordinal.{0}) := by rw [hb0, ← e]; exact hc'
        have hψρ := hψbk 0 (by omega) hρA
        rw [hb0, hc0] at hψρ
        have hle : upsilon μ ≤ ψ d := by
          rw [← hψρ]
          exact (hψmono (by rw [← e]; exact hc') hd (by rw [← e]; exact hlt)).le
        rw [e, hψρ]
        exact hle1μ _ hle (hψYb d hdY)
      · have hcF := hAF0 hc'
        have hdF := hAF0 hd
        rcases le_or_gt d δ with hdδ | hδd
        · have hR := inc1 (lt_of_le_of_lt hdδ hδ1) hcd
          have hR' := (Q5 c' hcF d hdF).1 hR
          have hΨlt : Ψ c' < Ψ d := Q4.2.1 hcF hdF hlt
          have hψc' : ψ c' = Ψ c' := hψeq c' hc' (indec_of_lt1R hR hlt) (indec_of_lt1R hR' hΨlt)
          have hψlt : ψ c' < ψ d := hψmono hc' hd hlt
          have hR'' : le1R (ψ c') (ψ d) :=
            le1R_of_le hψlt.le (hψle d hd) (by rw [hψc']; exact hR')
          have hμψ : upsilon μ < ψ c' := by
            rw [hψc', ← hΨρ]; exact hΨmono hρF hcF hρc
          have hψdδ : ψ d ≤ upsilon (μ + ω + 1) := (hψle d hd).trans (hΨlowδ d hdF hdδ)
          exact (Rμ.lowδ _ _ hμψ hψdδ).2 hR''
        · rcases le_or_gt c' δ with hcδ | hδc
          · exact absurd hcd (h.capδ c' hρc hcδ d hδd)
          · exact absurd (indec_of_lt1 hcd hlt)
              (decomp_mid hcδ hδc (hF0g c' hcF))
    · intro c' hc' d hd hcd
      change le2 c' d at hcd
      change le2 (ψ c') (ψ d)
      rcases eq_or_lt_of_le (le2_le hcd) with e | hlt
      · rw [e]; exact le2_refl _
      rcases Finset.mem_union.1 (Finset.mem_coe.1 hd) with hdX | hdY
      · rw [hψX c' (hXlt c' hc' d hdX hlt.le), hψX d hdX]; exact hcd
      rcases lt_trichotomy c' ρ with hcρ | e | hρc
      · exact absurd (le2_le1 hcd) (h.below c' hcρ d (hYg d hdY).1)
      · rw [e] at hcd hlt; exact absurd hcd (h.noSucc d hlt)
      have hρd : ρ < d := hρc.trans hlt
      rcases lt_trichotomy d δ with hdδ | hdδ | hδd
      · exact absurd hcd (h.noPairGap c' d hlt hρd hdδ)
      · have hcτ : c' = upsilon (r + ω) :=
          h.pairs_at_top (by rw [← hdδ]; exact hlt) (by rw [← hdδ]; exact hcd)
        have hτA : bb (N + 1) ∈ (↑(X ∪ Y) : Set Ordinal.{0}) := by rw [hbN1, ← hcτ]; exact hc'
        have hδA : bb (N + 2) ∈ (↑(X ∪ Y) : Set Ordinal.{0}) := by rw [hbN2, ← hdδ]; exact hd
        have e1 := hψbk (N + 1) (by omega) hτA
        have e2 := hψbk (N + 2) (by omega) hδA
        rw [hbN1, hcN1] at e1
        rw [hbN2, hcN2] at e2
        rw [hcτ, hdδ, e1, e2]; exact Rμ.pair
      · exact absurd (indec_of_lt2_right hcd hlt).1
          (decomp_mid hcδ hδd (hF0g d (hAF0 hd)))
  have himg : (↑(X ∪ Y.image ψ) : Set Ordinal.{0}) = ψ '' ↑(X ∪ Y) := by
    ext w
    simp only [Set.mem_image, Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro (hw | ⟨t, ht, rfl⟩)
      · exact ⟨w, Or.inl hw, hψX w hw⟩
      · exact ⟨t, Or.inr ht, rfl⟩
    · rintro ⟨t, ht | ht, rfl⟩
      · left; rw [hψX t ht]; exact ht
      · right; exact ⟨t, ht, rfl⟩
  have htgt : upsilon (μ + ω + 1) + tm m k (upsilon μ) < ρ := by
    have hμρ : upsilon μ < ρ :=
      lt_of_le_of_lt (upsilon_normal.strictMono.monotone (le_self_add.trans le_self_add)) hδμρ
    have htv : tm m k (upsilon μ) < ρ := hρI.add_lt (RstK.mul_nat_lt hρI hμρ m) hk
    exact hρI.add_lt hδμρ htv
  refine ⟨Y.image ψ, ?_, ?_, ?_, ψ, ?_⟩
  · intro y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    exact lt_of_le_of_lt (hψYb t ht) htgt
  · intro x hx y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    have := hψmono (show x ∈ (↑(X ∪ Y) : Set Ordinal.{0}) by simp [hx])
      (show t ∈ (↑(X ∪ Y) : Set Ordinal.{0}) by simp [ht])
      (lt_of_lt_of_le (hX x hx) (hYg t ht).1)
    rwa [hψX x hx] at this
  · rw [himg]; exact hψc
  · rw [himg]; exact hcov

/-! ## The reaches of all restarts below `B`, for an offset specification -/

section Spec

variable {O : Ordinal.{0} → Ordinal.{0}} {B : Ordinal.{0}} (S : OffSpec O B)
include S

theorem lt_B_add {μ : Ordinal.{0}} (hm : μ = 0 ∨ IsRestartIdx μ) (hμ : μ < B)
    {j : ℕ} : μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 < B :=
  lt_of_lt_of_le (pidx_lt μ j) (next_mult (mult_of hm) S.mult hμ)

/-- The restart context, Lemma TOP_λ and the chain after it, for every restart index `λ < B`. -/
theorem rstO {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < B) :
    RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)) ∧
    (∀ g, upsilon (l + ω + 1) + O l < g → ¬ le1 (upsilon l) g) ∧
    (∀ j : ℕ, BlkCtx (topA (l + ω) (upsilon (l + ω + 1) + O l) j) (lpA (l + ω) j)
      (topA (l + ω) (upsilon (l + ω + 1) + O l) (j + 1))) :=
  (good_B S).rst l hl hlB

/-- **Lemma RS_λ** in `R₂^C`: `ρ_λ ≤₁ δ_λ + O(λ)` for every restart index `λ < B`. -/
theorem rs_allO : ∀ l, IsRestartIdx l → l < B →
    le1 (upsilon l) (upsilon (l + ω + 1) + O l) := by
  intro l
  induction l using WellFoundedLT.induction with
  | ind l IH =>
  intro hl hlB
  obtain ⟨R, htop, -⟩ := rstO S hl hlB
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  rcases lt_or_ge (cL l) 2 with h2 | h2
  · -- a successor restart index: stage 3's Lemma RS with a block target
    rw [S.succ l hl hlB h2]
    obtain ⟨l0, hl0', rfl⟩ := succ_ri hl h2
    rcases hl0' with rfl | hl0r
    · have RC := rst_of_chain ctx0 T3_zero (by rw [upsilon_zero]) rfl R.δ1
      refine rs_gen RC ?_
      have := target_of_chain ctx0 (by rw [upsilon_zero] : upsilon 0 ≤ (0 : Ordinal.{0}))
      exact this
    · have hl0B : l0 < B := lt_of_le_of_lt le_self_add hlB
      obtain ⟨R0, htop0, C0⟩ := rstO S hl0r hl0B
      have hT3 := R0.T3off (S.le l0 hl0r hl0B) htop0
      have hTa : upsilon (l0 + ω) ≤ upsilon (l0 + ω + 1) + O l0 :=
        R0.next.1.le.trans le_self_add
      have hr : l0 + ω + ω * ω = l0 + ω * ω := by rw [add_assoc, w_add_ww]
      have RC := rst_of_chain C0 hT3 hTa hr R.δ1
      refine rs_gen RC ?_
      have := target_of_chain C0 hTa
      rwa [hr] at this
  · -- a limit restart index: restart targets
    have hRs := S.rs l hl hlB h2
    have hlim : IsSuccLimit l := by
      obtain ⟨q, hq⟩ := (ri_iff.1 hl).2
      have hq0 : q ≠ 0 := by intro h0; rw [h0, mul_zero] at hq; exact hl.1 hq
      rw [hq]
      exact isSuccLimit_mul_left (isSuccLimit_mul_right omega0_pos isSuccLimit_omega0)
        (pos_iff_ne_zero.2 hq0)
    have hstep : ∀ z < O l, le1 (upsilon l) (upsilon (l + ω + 1) + z + 1) := by
      intro z hz
      obtain ⟨b, k, rfl, hk, hcof⟩ := hRs z hz
      refine rs_rst R hk (fun κ' hκ' => ?_)
      obtain ⟨_, ⟨ι, hι, rfl⟩, hκι⟩ := (lt_isLUB_iff (upsilon_limit hlim)).1 hκ'
      obtain ⟨μ, hμ, hιμ, hμl, htv⟩ := hcof ι hι
      have hμB : μ < B := hμl.trans hlB
      obtain ⟨Rμ, -, -⟩ := rstO S hμ hμB
      have hrsμ := IH μ hμl hμ hμB
      refine ⟨μ, hκι.trans (upsilon_normal.strictMono hιμ), ?_, Rμ, fun g hg1 hg2 =>
        le1_of_le_of_le1 hg1 (hg2.trans (add_le_add le_rfl htv)) hrsμ⟩
      exact upsilon_normal.strictMono (lt_of_lt_of_le (by simpa using idx_lt μ 0 1)
        (next_mult (ri_iff.1 hμ).2 (ri_iff.1 hl).2 hμl))
    have hρδ := R.ρδ
    have hall : ∀ b', upsilon l ≤ b' → b' < upsilon (l + ω + 1) + O l → le1 (upsilon l) b' := by
      intro b' hb1 hb2
      rcases le_or_gt b' (upsilon (l + ω + 1)) with hbδ | hδb
      · exact R.le1ρδ b' hb1 hbδ
      · have he : upsilon (l + ω + 1) + (b' - upsilon (l + ω + 1)) = b' :=
          Ordinal.add_sub_cancel_of_le hδb.le
        have hz : b' - upsilon (l + ω + 1) < O l := by
          rw [← he] at hb2; exact (add_lt_add_iff_left _).1 hb2
        have hb'le : b' ≤ upsilon (l + ω + 1) + (b' - upsilon (l + ω + 1)) + 1 :=
          calc b' = upsilon (l + ω + 1) + (b' - upsilon (l + ω + 1)) := he.symm
            _ ≤ _ := le_self_add
        exact le1_of_le_of_le1 hb1 hb'le (hstep _ hz)
    rcases zero_or_succ_or_isSuccLimit (O l) with h0 | ⟨z0, hz0⟩ | hlimo
    · exact absurd h0 (ne_of_gt (lt_of_lt_of_le zero_lt_one (S.one l hl hlB)))
    · rw [← hz0, succ_eq_add_one, ← add_assoc]
      exact hstep z0 (by rw [← hz0]; exact lt_succ z0)
    · exact le1_limit (isSuccLimit_add _ hlimo)
        (lt_of_lt_of_le hρδ le_self_add) (fun b' hb1 hb2 => hall b' hb1 hb2)

/-- **The exact reach of every restart below `B`** in `R₂^C`: `lh(ρ_λ) = δ_λ + O(λ)`. -/
theorem reach_allO {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < B) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + O l) :=
  ⟨rs_allO S l hl hlB, fun g hg => not_lt.1 (fun h => (rstO S hl hlB).2.1 g h hg)⟩

/-- **The block theorem below `υ_B`** for an offset specification `O` up to `B`: (i) the `<₂`-pairs
with right end below `υ_B` are exactly `(υ_{μ+ω·j}, υ_{μ+ω·j+1})`, `j ≥ 1`, `μ < B` zero or a
restart index; (ii) a restart `ρ_λ` (`λ < B`) has no `<₁`-predecessor and no `<₂`-successor, and
`{γ : ρ_λ ≤₁ γ} = [ρ_λ, δ_λ + O(λ)]`; (iii) every point below `υ_B` that is not a `υ`-point has
its `R₁⁺` reach. -/
theorem blk_gen :
    (∀ c d, c < d → d < upsilon B → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < B ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < B →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + O l)) ∧
    (∀ α < upsilon B, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) := by
  refine ⟨fun c d hcd hd => (good_B S).pairs c d hcd hd, fun l hl hlB => ?_, (good_B S).sk⟩
  obtain ⟨R, -, -⟩ := rstO S hl hlB
  exact ⟨R.below, R.noSucc, reach_allO S hl hlB⟩

end Spec

/-! ## Theorem BLK^Ξ -/

theorem lt_XiW_add {μ : Ordinal.{0}} (hμ : μ ≤ XiW) : μ < XiW + ω * ω :=
  lt_of_le_of_lt hμ (lt_add_of_pos_right _ (mul_pos omega0_pos omega0_pos))

theorem le_XiW_of_lt {μ : Ordinal.{0}} (hm : μ = 0 ∨ IsRestartIdx μ) (hμ : μ < XiW + ω * ω) :
    μ ≤ XiW := by
  by_contra hgt
  exact absurd hμ (not_lt.2 (next_mult (ri_iff.1 XiW_ri).2 (mult_of hm) (not_le.1 hgt)))

/-- **Lemma RS_λ** for every restart index `λ ≤ Ξ_ω`: `ρ_λ ≤₁ δ_λ + c*(λ)`. -/
theorem rs_all {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlX : l ≤ XiW) :
    le1 (upsilon l) (upsilon (l + ω + 1) + off l) :=
  rs_allO specXi l hl (lt_XiW_add hlX)

/-- **The exact reach of every restart up to `Ξ_ω`** in `R₂^C`: `lh(ρ_λ) = δ_λ + c*(λ)`. -/
theorem reach_all {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlX : l ≤ XiW) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + off l) :=
  reach_allO specXi hl (lt_XiW_add hlX)

/-- **Theorem BLK^Ξ in `R₂^C`.**  (i) The `<₂`-pairs with right end below `υ_{Ξ_ω+ω²}` are exactly
`(τ^μ_j, δ^μ_j) = (υ_{μ+ω·j}, υ_{μ+ω·j+1})`, `j ≥ 1`, `μ = 0` or a restart index `≤ Ξ_ω`.
(ii) A restart `ρ_λ` (`λ ≤ Ξ_ω`) has no `<₁`-predecessor and no `<₂`-successor, and
`{γ : ρ_λ ≤₁ γ} = [ρ_λ, δ_λ + c*(λ)]`.  (iii) Every point below `υ_{Ξ_ω+ω²}` that is not a
`υ`-point has its `R₁⁺` reach (`≤₁` of `R₂^C` = `≤₁` of `R₁⁺` from it). -/
theorem blkXi :
    (∀ c d, c < d → d < upsilon (XiW + ω * ω) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ ≤ XiW ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l ≤ XiW →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + off l)) ∧
    (∀ α < upsilon (XiW + ω * ω), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) := by
  obtain ⟨H1, H2, H3⟩ := blk_gen specXi
  refine ⟨fun c d hcd hd => ?_, fun l hl hlX => H2 l hl (lt_XiW_add hlX), H3⟩
  rw [H1 c d hcd hd]
  constructor
  · rintro ⟨μ, j, hμ, hμl, h1, h2⟩
    exact ⟨μ, j, hμ, le_XiW_of_lt hμ hμl, h1, h2⟩
  · rintro ⟨μ, j, hμ, hμl, h1, h2⟩
    exact ⟨μ, j, hμ, lt_XiW_add hμl, h1, h2⟩

/-! ## The values -/

theorem ri_opow {e : Ordinal.{0}} (he : 2 ≤ e) : IsRestartIdx (ω ^ e) := by
  refine ⟨(opow_pos _ omega0_pos).ne', ?_⟩
  rw [← opow_natCast]; exact opow_dvd_opow ω (by exact_mod_cast he)

theorem opow_lt_XiW {e : Ordinal.{0}} (he : e < XiW) : ω ^ e < XiW := by
  have hE := inE_of_fp XiW_pos XiW_fp
  unfold InE at hE
  rw [← hE]; exact (opow_lt_opow_iff_right one_lt_omega0).2 he

/-- `lh(ρ_{ω^e}) = δ_{ω^e} + (e − 1)` for `2 ≤ e < Ξ_ω` (so `δ + 2` at `ω³`, `δ + 3` at `ω⁴`, `δ + ω`
at `ω^ω`). -/
theorem reach_opow {e : Ordinal.{0}} (he : 2 ≤ e) (heX : e < XiW) :
    IsReach R2C (upsilon (ω ^ e)) (upsilon (ω ^ e + ω + 1) + (e - 1)) := by
  have h := reach_all (ri_opow he) (opow_lt_XiW heX).le
  rwa [off_lt_XiW (opow_lt_XiW heX), cL_opow he] at h

theorem two_lt_XiW : (2 : Ordinal.{0}) < XiW := by
  have h1 : (2 : Ordinal.{0}) < ω := by
    have := natCast_lt_omega0 2; rwa [Nat.cast_ofNat] at this
  refine h1.trans_le ?_
  have hE := inE_of_fp XiW_pos XiW_fp
  unfold InE at hE
  calc ω = ω ^ (1 : Ordinal.{0}) := (opow_one ω).symm
    _ ≤ ω ^ XiW := opow_le_opow_right omega0_pos (one_lt_of_ups_fp XiW_pos XiW_fp).le
    _ = XiW := hE

theorem omega_lt_XiW : (ω : Ordinal.{0}) < XiW := by
  have hE := inE_of_fp XiW_pos XiW_fp
  unfold InE at hE
  calc (ω : Ordinal.{0}) < ω ^ (2 : Ordinal.{0}) := by
        rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, opow_add, opow_one]
        exact lt_mul_of_one_lt_right omega0_pos one_lt_omega0
    _ < ω ^ XiW := (opow_lt_opow_iff_right one_lt_omega0).2 two_lt_XiW
    _ = XiW := hE

/-- `lh(υ_{ω³}) = δ + 2`. -/
theorem reach_w3 : IsReach R2C (upsilon (ω ^ (3 : Ordinal.{0})))
    (upsilon (ω ^ (3 : Ordinal.{0}) + ω + 1) + 2) := by
  have h3 : (3 : Ordinal.{0}) < XiW := by
    have : (3 : Ordinal.{0}) < ω := by
      have := natCast_lt_omega0 3; rwa [Nat.cast_ofNat] at this
    exact this.trans omega_lt_XiW
  have := reach_opow (show (2 : Ordinal.{0}) ≤ 3 by norm_num) h3
  have e : (3 : Ordinal.{0}) - 1 = 2 := by
    rw [show (3 : Ordinal.{0}) = 1 + 2 by norm_num, Ordinal.add_sub_cancel]
  rwa [e] at this

/-- `lh(υ_{ω^ω}) = δ + ω`. -/
theorem reach_ww : IsReach R2C (upsilon (ω ^ ω)) (upsilon (ω ^ ω + ω + 1) + ω) := by
  have := reach_opow (show (2 : Ordinal.{0}) ≤ ω from (by
    have := natCast_lt_omega0 2; rw [Nat.cast_ofNat] at this; exact this.le)) omega_lt_XiW
  have e : (ω : Ordinal.{0}) - 1 = ω := by
    conv_lhs => rw [← one_add_omega0]
    rw [Ordinal.add_sub_cancel]
  rwa [e] at this

/-- `lh(Ξ_n) = δ + Ξ_n` (`ρ = Ξ_n`, `n ≥ 1`). -/
theorem reach_Xi (n : ℕ) (hn : 1 ≤ n) :
    IsReach R2C (Xi n) (upsilon (Xi n + ω + 1) + Xi n) := by
  have h0 : 0 < Xi n := by
    have := Xi_strictMono (show ((0 : ℕ) : Ordinal.{0}) < n by exact_mod_cast hn)
    rwa [Nat.cast_zero, Xi_zero] at this
  have hlt : Xi n < XiW := Xi_strictMono (natCast_lt_omega0 n)
  have h := reach_all (ri_of_fp h0 (Xi_fp n)) hlt.le
  rwa [off_lt_XiW hlt, cL_fp h0 (Xi_fp n), Xi_fp] at h

/-- `lh(Ξ_ω) = δ + Ξ_ω + 1`. -/
theorem reach_XiW : IsReach R2C XiW (upsilon (XiW + ω + 1) + (XiW + 1)) := by
  have h := reach_all XiW_ri le_rfl
  rwa [off_XiW, XiW_fp] at h

end Googology.Trans.PoR.InaccPsi.R2
