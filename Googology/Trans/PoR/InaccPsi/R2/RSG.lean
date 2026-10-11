import Googology.Trans.PoR.InaccPsi.R2.Exact
import Googology.Trans.PoR.InaccPsi.R2.CoreX

/-!
# Lemma RS with a restart target for the offset terms `x·γ + e` (Lemma EXACT inside FRAG)

* `tg γ e x = x·γ + e`, `tq b γ e x` (`x·γ + e` for `b = false`, `x·x + e` for `b = true`); `InE.mul_lt`,
  `tg_lt`, `tq_lt`, `tq_const`, `pi_tq` (Lemma EXACT for these terms).
* `rs_rstG` (**Lemma RS with a restart target**, the project's Lemma RS^O, for the terms `x·γ + e`
  and `x·x + e`, `γ` any ordinal constant): as `rs_rst` (stage 4, terms `x·m + k`, `m` finite), with the FRAG map of
  `fragX`; on `seg(ρ)` it is the base change `π_{ρ_μ, ρ}` (`ρ_μ < ρ`), and Lemma EXACT (`pi_tq`) gives
  `Ψ(t(ρ)) = t(ρ_μ)`, so `δ + t(ρ) ↦ δ_μ + t(ρ_μ)`.  For `m` finite `x·m + k` is `tg m k`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-- The value at `x` of the offset term `x·γ + e`. -/
def tg (γ e x : Ordinal.{0}) : Ordinal.{0} := x * γ + e

theorem tm_eq_tg (m : ℕ) (k r : Ordinal.{0}) : tm m k r = tg (m : Ordinal.{0}) k r := rfl

/-- An `ε`-number is closed under multiplication. -/
theorem InE.mul_lt {u a b : Ordinal.{0}} (hu : InE u) (ha : a < u) (hb : b < u) : a * b < u := by
  have hP : IsPrincipal (· * ·) u := by
    have h1 : u = ω ^ ω ^ u := by unfold InE at hu; rw [hu, hu]
    rw [h1]; exact isPrincipal_mul_omega0_opow_opow u
  exact hP ha hb

/-- `x·γ + e < u` for an `ε`-number `u` above `x, γ, e`. -/
theorem tg_lt {u γ e x : Ordinal.{0}} (hu : InE u) (hγ : γ < u) (he : e < u) (hx : x < u) :
    tg γ e x < u :=
  (inE_indec hu).add_lt (hu.mul_lt hx hγ) he

/-- The offset terms of this stage: `x·γ + e` (`b = false`) and `x·x + e` (`b = true`). -/
def tq (b : Bool) (γ e x : Ordinal.{0}) : Ordinal.{0} := if b then x * x + e else x * γ + e

theorem tq_false (γ e x : Ordinal.{0}) : tq false γ e x = tg γ e x := by simp [tq, tg]

theorem tq_true (γ e x : Ordinal.{0}) : tq true γ e x = x * x + e := by simp [tq]

theorem tq_lt {u : Ordinal.{0}} {b : Bool} {γ e x : Ordinal.{0}} (hu : InE u) (hγ : γ < u)
    (he : e < u) (hx : x < u) : tq b γ e x < u := by
  cases b
  · rw [tq_false]; exact tg_lt hu hγ he hx
  · rw [tq_true]; exact (inE_indec hu).add_lt (hu.mul_lt hx hx) he

/-- A term whose value at `ρ ≥ 1` is below `ρ` is the constant `e`. -/
theorem tq_const {b : Bool} {γ e ρ : Ordinal.{0}} (hρ : 1 ≤ ρ) (h : tq b γ e ρ < ρ) :
    ∀ x, tq b γ e x = e := by
  cases b
  · rcases eq_or_ne γ 0 with hγ | hγ
    · intro x; rw [tq_false, tg, hγ, mul_zero, zero_add]
    · exfalso
      rw [tq_false, tg] at h
      exact absurd h (not_lt.2 ((le_mul_left ρ (pos_iff_ne_zero.2 hγ)).trans le_self_add))
  · exfalso
    rw [tq_true] at h
    exact absurd h (not_lt.2 ((le_mul_left ρ (lt_of_lt_of_le zero_lt_one hρ)).trans le_self_add))

/-- **Lemma EXACT for the terms `tq`**: `π_{s,r}(t(r)) = t(s)` for constants `γ, e < s`. -/
theorem pi_tq {s r : Ordinal.{0}} {b : Bool} {γ e : Ordinal.{0}} (hB : Bases s r) (hγ : γ < s)
    (he : e < s) : tq b γ e r ∈ TB r s ∧ pi s r (tq b γ e r) = tq b γ e s := by
  cases b
  · rw [tq_false, tq_false, tg, tg]; exact pi_term hB hγ he
  · rw [tq_true, tq_true]
    obtain ⟨h1, h2⟩ := pi_sq hB
    obtain ⟨h3, h4⟩ := pi_add hB h1 (mem_TB_of_lt hB he)
    exact ⟨h3, by rw [h4, h2, pi_lt hB he]⟩

theorem rs_rstG {r : Ordinal.{0}} (h : RstK (upsilon r) (upsilon (r + ω)) (upsilon (r + ω + 1)))
    {b : Bool} {γ e : Ordinal.{0}} (hγ : γ < upsilon r) (he : e < upsilon r)
    (htarget : ∀ κ' < upsilon r, ∃ μ, κ' < upsilon μ ∧ upsilon (μ + ω + 1) < upsilon r ∧
      RstK (upsilon μ) (upsilon (μ + ω)) (upsilon (μ + ω + 1)) ∧
      ∀ g, upsilon μ ≤ g → g ≤ upsilon (μ + ω + 1) + tq b γ e (upsilon μ) → le1 (upsilon μ) g) :
    le1 (upsilon r) (upsilon (r + ω + 1) + tq b γ e (upsilon r) + 1) := by
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
  set cρ := tq b γ e ρ with hcρdef
  have hδE : InE δ := upsPt_inE h.next.2.1
  have hcδ : cρ < δ := tq_lt hδE (hγ.trans hρδ) (he.trans hρδ) hρδ
  have hρE : InE ρ := upsPt_inE h.ρU
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
  set W : Finset Ordinal.{0} := {γ, e, ρ, δ, cρ, g'} with hWdef
  set F0 := (X ∪ Y ∪ W).biUnion (hpar ρ) with hF0
  have hAF : ∀ z ∈ X ∪ Y ∪ W, z ∈ F0 := fun z hz =>
    Finset.mem_biUnion.2 ⟨z, hz, mem_hpar_self _ _⟩
  have hXYF : ∀ z ∈ X ∪ Y, z ∈ F0 := fun z hz => hAF z (Finset.mem_union_left _ hz)
  have hWF : ∀ z ∈ W, z ∈ F0 := fun z hz => hAF z (Finset.mem_union_right _ hz)
  have hγF : γ ∈ F0 := hWF γ (by simp [hWdef])
  have heF : e ∈ F0 := hWF e (by simp [hWdef])
  have hρF : ρ ∈ F0 := hWF ρ (by simp [hWdef])
  have hδF : δ ∈ F0 := hWF δ (by simp [hWdef])
  have hg'F : g' ∈ F0 := hWF g' (by simp [hWdef])
  have hcF : cρ ∈ F0 := hWF cρ (by simp [hWdef])
  have hF0g : ∀ z ∈ F0, z ≤ g' := by
    intro z hz
    obtain ⟨w, hw, hzw⟩ := Finset.mem_biUnion.1 hz
    refine (hpar_le _ w z hzw).trans ?_
    rcases Finset.mem_union.1 hw with hw | hw
    · rcases Finset.mem_union.1 hw with hwX | hwY
      · exact ((hX w hwX).trans hρδ).le.trans le_self_add
      · exact (hYg w hwY).2
    · simp only [hWdef, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hγ.trans hρδ).le.trans le_self_add
      · exact (he.trans hρδ).le.trans le_self_add
      · exact hρδ.le.trans le_self_add
      · exact le_self_add
      · exact hcδ.le.trans le_self_add
      · exact le_rfl
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
  obtain ⟨Ψ, ⟨Q1, -, Q3, Q4, Q5, -, -⟩, Q8⟩ := fragX hbC hcC F0 hF0DD
  have hΨmono : StrictMonoOn Ψ ↑F0 := Q4.2.1
  have hΨadd : ∀ x ∈ F0, ∀ y ∈ F0, ∀ z ∈ F0, x + y = z → Ψ x + Ψ y = Ψ z := fun x hx y hy z hz e =>
    (Q4.2.2 x hx y hy z hz).1 e
  have hΨρ : Ψ ρ = upsilon μ := by
    have := Q3 0 (by omega) (by rw [hb0]; exact hρF); rwa [hb0, hc0] at this
  have hΨτ : upsilon (r + ω) ∈ F0 → Ψ (upsilon (r + ω)) = upsilon (μ + ω) := fun hτF => by
    have := Q3 (N + 1) (by omega) (by rw [hbN1]; exact hτF); rwa [hbN1, hcN1] at this
  have hΨδ : Ψ δ = upsilon (μ + ω + 1) := by
    have := Q3 (N + 2) (by omega) (by rw [hbN2]; exact hδF); rwa [hbN2, hcN2] at this
  have hγκ : γ < κ := hLoκ γ hγF hγ
  have heκ : e < κ := hLoκ e heF he
  have hμρ : upsilon μ < ρ :=
    lt_of_le_of_lt (upsilon_normal.strictMono.monotone (le_self_add.trans le_self_add)) hδμρ
  have hΨc : Ψ cρ = tq b γ e (upsilon μ) := by
    by_cases hρc : ρ ≤ cρ
    · -- `cρ ∈ seg(ρ) ∩ D_1`: `Ψ = π_{ρ_μ, ρ}` there (FRAG on `D_1`), and Lemma EXACT
      have hnx0 := upsilon_isNext r
      have hc1 : cρ < upsilon (succ r) :=
        tq_lt (upsPt_inE hnx0.2.1) (hγ.trans hnx0.1) (he.trans hnx0.1) hnx0.1
      have hcs : InSeg ρ cρ :=
        ⟨hρc, hcδ.trans hδ1, fun u hu hu' => lt_of_lt_of_le hc1 (hnx0.2.2 u hu hu')⟩
      have hcT : cρ ∈ Tset ρ := ((inSeg_iff h.ρU h.ρ1).1 hcs).2.2
      have hcD : cρ ∈ DD κ bb 1 := by
        refine Or.inr ⟨by rw [hb0]; exact hcs, by rw [hb0]; exact hcT, ?_⟩
        intro p hp
        rw [hb0] at hp
        have hpρ : p < ρ := Par_sub hρE h.ρ1 hcT hp
        have hpF : p ∈ F0 := hF0cl cρ hcF hρc p (by rw [sb_eq h.ρU hcs]; exact Finset.mem_coe.1 hp)
          (lt_of_lt_of_le hpρ hρc)
        exact ClS.sub _ (hLoκ p hpF hpρ)
      rw [Q8 (by omega) cρ hcF hcD, hb0, hc0, mv_down hμρ]
      have hBμ : Bases (upsilon μ) ρ := ⟨upsPt_inE Rμ.ρU, hρE, hμρ, h.ρ1⟩
      exact (pi_tq hBμ (hγκ.trans hκμ) (heκ.trans hκμ)).2
    · -- a constant term: `cρ = e`
      have hconst := tq_const (one_le_iff_pos.2 hρ0) (not_le.1 hρc)
      have hc : cρ = e := hconst ρ
      rw [hc, Q1 e heF heκ, hconst]
  have hΨg' : Ψ g' = upsilon (μ + ω + 1) + tq b γ e (upsilon μ) := by
    rw [← hΨδ, ← hΨc]; exact (hΨadd δ hδF cρ hcF g' hg'F rfl).symm
  have hΨup : ∀ z ∈ F0, ρ ≤ z → upsilon μ ≤ Ψ z ∧ Ψ z ≤ upsilon (μ + ω + 1) + tq b γ e (upsilon μ) := by
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
  have hψYb : ∀ y ∈ Y, ψ y ≤ upsilon (μ + ω + 1) + tq b γ e (upsilon μ) := fun y hy =>
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
  have htgt : upsilon (μ + ω + 1) + tq b γ e (upsilon μ) < ρ := by
    have htv : tq b γ e (upsilon μ) < ρ := tq_lt hρE hγ he hμρ
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

end Googology.Trans.PoR.InaccPsi.R2
