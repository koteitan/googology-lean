import Googology.Trans.PoR.InaccPsi.R2.Blk3

/-!
# Lemmas RS and RS^h in `R₂^C`: `ρ_h ≤₁ δ_h + 1`, so `lh(ρ_h) = δ_h + 1` below `υ_{ω³}`

The project's Lemma RS (the paper proof uses Theorem FRAG): for the restart `ρ = υ_r` with the pair
`τ = υ_{r+ω} <₂ δ = υ_{r+ω+1}` of its first block, a finite `Y ⊆ [ρ, δ]` is copied below `ρ` by a FRAG
map `Ψ` (Theorem FRAG, `frag`) that moves the bases `υ_r, υ_{r+1}, …, υ_{r+N}, τ, δ` to
`υ_{A+2}, …, υ_{A+2+N}, υ_{A+ω}, υ_{A+ω+1}` inside a lower block `(υ_{A+1}, υ_{A+ω+1}]` with the pair
`υ_{A+ω} <₂ υ_{A+ω+1}`, followed by the leading-term map of Theorem CC-F (closedness, [C09] Lemma 4.5).

* `close_map`: the leading-term map `ext (mc ∘ Ψ)` of an arithmetic isomorphism of a closed set.
* `sb`, `sb_eq`: the `υ`-point of the segment of a point.
* `hpar`: the hereditary parameters of a point above `ρ` (a finite set), with `hpar_le`,
  `hpar_closed`.
* `DD_down`, `ix`, `ix_lt`: domains of FRAG and the index lists of the bases.
* `rs_gen` (**Lemma RS**, general form), `rs_h` (**Lemma RS^h** for every restart below `υ_{ω³}`),
  `reach_rst` (`lh(ρ_{h+1}) = δ_{h+1} + 1` in `R₂^C`, with Lemma TOP^h).
  Index shift: in `rs_h h` and `reach_rst h` the Lean argument `h` is the paper's `h − 1` (they are
  about the paper's restart `ρ_{h+1} = υ_{ω²·(h+1)}`; `h = 0` is `ρ_1 = υ_{ω²}`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-! ## The leading-term map -/

/-- The leading-term map of Theorem CC-F for an arithmetic isomorphism `Ψ` of a closed set `A`:
`ext (mc ∘ Ψ)` is an arithmetic isomorphism onto a closed set, it is `≤ Ψ`, it agrees with `Ψ` on
indecomposables with indecomposable image, and it fixes every point whose components `Ψ` fixes. -/
theorem close_map {A : Set Ordinal.{0}} (hA : Closed A) {Ψ : Ordinal.{0} → Ordinal.{0}}
    (hΨ : ArithIso A (Ψ '' A) Ψ) :
    ArithIso A (ext (fun a => mc (Ψ a)) '' A) (ext (fun a => mc (Ψ a))) ∧
    Closed (ext (fun a => mc (Ψ a)) '' A) ∧
    (∀ z ∈ A, ext (fun a => mc (Ψ a)) z ≤ Ψ z) ∧
    (∀ z ∈ A, Indec z → Indec (Ψ z) → ext (fun a => mc (Ψ a)) z = Ψ z) ∧
    (∀ x ∈ A, (∀ a ∈ pc x, Ψ a = a) → ext (fun a => mc (Ψ a)) x = x) := by
  have hne : ∀ a ∈ A, a ≠ 0 → Ψ a ≠ 0 := by
    intro a ha ha0 e
    apply ha0
    have : Ψ a + Ψ a = Ψ a := by rw [e, add_zero]
    exact add_self_eq_self ((hΨ.2.2 a ha a ha a ha).2 this)
  have hf : StrictMonoOn (fun a => mc (Ψ a)) (IndecIn A) := by
    intro a ha b hb hab
    have hsum : a + b = b := hb.2.add_eq hab
    have := (hΨ.2.2 a ha.1 b hb.1 b hb.1).1 hsum
    exact mc_lt_of_add_eq (hne a ha.1 ha.2.ne_zero) this
  have hfI : ∀ a ∈ IndecIn A, Indec ((fun a => mc (Ψ a)) a) := fun a ha =>
    mc_indec (hne a ha.1 ha.2.ne_zero)
  have hiso := ext_arithIso hA hf hfI
  refine ⟨hiso, ext_closed hA hf hfI,
    le_of_le_on_indec hA hiso hΨ (fun a _ hI => by rw [ext_indec hI]; exact mc_le _), ?_, ?_⟩
  · intro z _ hzI hΨI
    rw [ext_indec hzI]; exact mc_of_indec hΨI
  · intro x _ hx
    apply ext_fix
    intro a ha
    show mc (Ψ a) = a
    rw [hx a ha, mc_of_indec (indec_of_mem_pc ha)]

/-! ## Segments and hereditary parameters -/

/-- The `υ`-point of the segment of `x`: the largest `υ`-point `≤ x`. -/
noncomputable def sb (x : Ordinal.{0}) : Ordinal.{0} := sSup {u | u ≤ x ∧ UpsPt u}

theorem sb_eq {b x : Ordinal.{0}} (hb : UpsPt b) (hs : InSeg b x) : sb x = b := by
  refine IsGreatest.csSup_eq ⟨⟨hs.1, hb⟩, fun u hu => ?_⟩
  by_contra hlt
  exact absurd hu.1 (not_le.2 (hs.2.2 u (not_le.1 hlt) hu.2))

/-- The hereditary parameters of `x` above `ρ`: `x`, and, if `ρ ≤ x`, the hereditary parameters
of the parameters `Par^{sb x}(x)`. -/
noncomputable def hpar (ρ : Ordinal.{0}) : Ordinal.{0} → Finset Ordinal.{0} :=
  (wellFounded_lt (α := Ordinal.{0})).fix fun x IH =>
    insert x (if ρ ≤ x then (Par (sb x) x).biUnion
      (fun p => if hp : p < x then IH p hp else ∅) else ∅)

theorem hpar_eq (ρ x : Ordinal.{0}) : hpar ρ x = insert x (if ρ ≤ x then (Par (sb x) x).biUnion
    (fun p => if p < x then hpar ρ p else ∅) else ∅) := by
  rw [hpar, WellFounded.fix_eq]
  congr 2

theorem mem_hpar_self (ρ x : Ordinal.{0}) : x ∈ hpar ρ x := by
  rw [hpar_eq]; exact Finset.mem_insert_self _ _

theorem hpar_low {ρ x : Ordinal.{0}} (hx : x < ρ) : hpar ρ x = {x} := by
  rw [hpar_eq, if_neg (not_le.2 hx)]; rfl

theorem hpar_sub {ρ x p : Ordinal.{0}} (hρx : ρ ≤ x) (hp : p ∈ Par (sb x) x) (hpx : p < x) :
    hpar ρ p ⊆ hpar ρ x := by
  intro y hy
  rw [hpar_eq ρ x, if_pos hρx]
  refine Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨p, hp, ?_⟩)
  rw [if_pos hpx]; exact hy

theorem hpar_le (ρ : Ordinal.{0}) : ∀ x, ∀ y ∈ hpar ρ x, y ≤ x := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro y hy
  rw [hpar_eq] at hy
  rcases Finset.mem_insert.1 hy with rfl | hy
  · exact le_rfl
  split_ifs at hy with hρx
  · obtain ⟨p, -, hyp⟩ := Finset.mem_biUnion.1 hy
    split_ifs at hyp with hpx
    · exact (IH p hpx y hyp).trans hpx.le
    · simp at hyp
  · simp at hy

theorem hpar_closed (ρ : Ordinal.{0}) : ∀ x, ∀ y ∈ hpar ρ x, ρ ≤ y →
    ∀ p ∈ Par (sb y) y, p < y → p ∈ hpar ρ x := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro y hy hρy p hp hpy
  rw [hpar_eq] at hy
  rcases Finset.mem_insert.1 hy with rfl | hy
  · exact hpar_sub hρy hp hpy (mem_hpar_self ρ p)
  split_ifs at hy with hρx
  · obtain ⟨q, hq, hyq⟩ := Finset.mem_biUnion.1 hy
    split_ifs at hyq with hqx
    · exact hpar_sub hρx hq hqx (IH q hqx y hyq hρy p hp hpy)
    · simp at hyq
  · simp at hy

/-! ## Domains of FRAG and index lists -/

theorem DD_down {κ : Ordinal.{0}} {b : ℕ → Ordinal.{0}} {m : ℕ} (hb : Chain κ b m)
    {x : Ordinal.{0}} (hx : x ∈ DD κ b m) {k : ℕ} (_hk : k < m) (hxk : x < b k) :
    x ∈ DD κ b k := by
  rcases mem_DD hx with h | ⟨j, hj, hs, hT, hP⟩
  · exact Iio_sub_DD k h
  · have hjk : j < k := by
      by_contra hkj
      rcases eq_or_lt_of_le (not_lt.1 hkj) with e | hlt
      · subst e; exact absurd hs.1 (not_le.2 hxk)
      · exact absurd (lt_of_lt_of_le (hb.mono k j hlt hj) hs.1) (not_lt.2 hxk.le)
    exact DD_mono (show j + 1 ≤ k by omega) (Or.inr ⟨hs, hT, hP⟩)

/-- The index list `B + o, B + o + 1, …, B + o + N, B + ω, B + ω + 1`. -/
noncomputable def ix (B : Ordinal.{0}) (o N k : ℕ) : Ordinal.{0} :=
  if k ≤ N then B + ((o + k : ℕ) : Ordinal.{0}) else if k = N + 1 then B + ω else B + ω + 1

theorem ix_lt {B : Ordinal.{0}} {o N j k : ℕ} (hjk : j < k) (hk : k ≤ N + 2) :
    ix B o N j < ix B o N k := by
  unfold ix
  by_cases hj : j ≤ N
  · rw [if_pos hj]
    by_cases hkN : k ≤ N
    · rw [if_pos hkN]
      exact (add_lt_add_iff_left B).2 (by exact_mod_cast (show o + j < o + k by omega))
    · rw [if_neg hkN]
      have h1 : B + ((o + j : ℕ) : Ordinal.{0}) < B + ω :=
        (add_lt_add_iff_left B).2 (natCast_lt_omega0 _)
      split_ifs
      · exact h1
      · exact h1.trans (lt_add_one _)
  · have hjN : j = N + 1 := by omega
    have hkN : k = N + 2 := by omega
    rw [if_neg hj, if_pos hjN, if_neg (by omega), if_neg (by omega)]
    exact lt_add_one _

theorem ix_le {B : Ordinal.{0}} {o N j k : ℕ} (hjk : j ≤ k) (hk : k ≤ N + 2) :
    ix B o N j ≤ ix B o N k := by
  rcases eq_or_lt_of_le hjk with rfl | h
  · exact le_rfl
  · exact (ix_lt h hk).le

theorem ix_low {B : Ordinal.{0}} {o N k : ℕ} (hk : k ≤ N) : ix B o N k = B + ((o + k : ℕ) : Ordinal.{0}) := by
  unfold ix; rw [if_pos hk]

theorem ix_N1 {B : Ordinal.{0}} {o N : ℕ} : ix B o N (N + 1) = B + ω := by
  unfold ix; rw [if_neg (by omega), if_pos rfl]

theorem ix_N2 {B : Ordinal.{0}} {o N : ℕ} : ix B o N (N + 2) = B + ω + 1 := by
  unfold ix; rw [if_neg (by omega), if_neg (by omega)]

theorem ix_ge {B : Ordinal.{0}} {o N k : ℕ} (hk : k ≤ N + 2) : B + (o : Ordinal.{0}) ≤ ix B o N k := by
  have h0 : ix B o N 0 = B + (o : Ordinal.{0}) := by rw [ix_low (Nat.zero_le N)]; simp
  rw [← h0]; exact ix_le (Nat.zero_le k) hk

theorem ix_top {B : Ordinal.{0}} {o N k : ℕ} (hk : k ≤ N + 2) : ix B o N k ≤ B + ω + 1 := by
  rw [← ix_N2 (o := o) (N := N)]; exact ix_le hk le_rfl

/-! ## Lemma RS -/

/-- **Lemma RS** (general form): for a restart context of `ρ = υ_r` with lower blocks
`(υ_{A+1}, υ_{A+ω+1}]` (pair `υ_{A+ω} <₂ υ_{A+ω+1}`) cofinal below `ρ`: `ρ ≤₁ δ + 1`,
`δ = υ_{r+ω+1}`. -/
theorem rs_gen {r : Ordinal.{0}}
    (h : RstCtx (upsilon r) (upsilon (r + ω)) (upsilon (r + ω + 1)))
    (htarget : ∀ κ' < upsilon r, ∃ A', κ' < upsilon (A' + 1) ∧ upsilon (A' + ω + 1) < upsilon r ∧
      BlkCtx (upsilon (A' + 1)) (upsilon (A' + ω)) (upsilon (A' + ω + 1))) :
    le1 (upsilon r) (upsilon (r + ω + 1) + 1) := by
  have hρτ := h.ρτ
  have hτδ := h.τδ
  have hρδ : upsilon r < upsilon (r + ω + 1) := hρτ.trans hτδ
  have hδ1 := h.δ1
  have hρ0 : 0 < upsilon r := h.ρU.1
  refine le1_iff.2 ⟨hρδ.le.trans le_self_add, fun X Y hX hY hXY => ?_⟩
  have hYδ : ∀ y ∈ Y, upsilon r ≤ y ∧ y ≤ upsilon (r + ω + 1) := fun y hy =>
    ⟨(hY y hy).1, Order.lt_add_one_iff.1 (hY y hy).2⟩
  -- the hereditary parameters
  set F0 := (X ∪ Y).biUnion (hpar (upsilon r)) with hF0
  have hAF : ∀ z ∈ X ∪ Y, z ∈ F0 := fun z hz =>
    Finset.mem_biUnion.2 ⟨z, hz, mem_hpar_self _ _⟩
  have hF0δ : ∀ z ∈ F0, z ≤ upsilon (r + ω + 1) := by
    intro z hz
    obtain ⟨w, hw, hzw⟩ := Finset.mem_biUnion.1 hz
    refine (hpar_le _ w z hzw).trans ?_
    rcases Finset.mem_union.1 hw with hwX | hwY
    · exact ((hX w hwX).trans hρδ).le
    · exact (hYδ w hwY).2
  have hF0cl : ∀ z ∈ F0, upsilon r ≤ z → ∀ p ∈ Par (sb z) z, p < z → p ∈ F0 := by
    intro z hz hρz p hp hpz
    obtain ⟨w, hw, hzw⟩ := Finset.mem_biUnion.1 hz
    exact Finset.mem_biUnion.2 ⟨w, hw, hpar_closed _ w z hzw hρz p hp hpz⟩
  -- the base `κ`
  have hsup : (insert 0 (F0.filter (· < upsilon r))).sup id < upsilon r := by
    rw [Finset.sup_lt_iff hρ0]
    intro b hb
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact hρ0
    · exact (Finset.mem_filter.1 hb).2
  obtain ⟨κ, κ', hκU, hκ, hκn, hκ'ρ, -, -, -⟩ := h.land _ hsup
  have hκρ : κ < upsilon r := hκn.1.trans hκ'ρ
  have hκ1 : κ < Om1 := hκρ.trans h.ρ1
  have hLoκ : ∀ z ∈ F0, z < upsilon r → z < κ := fun z hz hzρ =>
    lt_of_le_of_lt (Finset.le_sup (f := id)
      (Finset.mem_insert_of_mem (show z ∈ F0.filter (· < upsilon r) from
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
  set b : ℕ → Ordinal.{0} := fun k => upsilon (ix r 0 N k) with hbdef
  have hb0 : b 0 = upsilon r := by simp [hbdef, ix_low (Nat.zero_le N)]
  have hbN1 : b (N + 1) = upsilon (r + ω) := by simp [hbdef, ix_N1]
  have hbN2 : b (N + 2) = upsilon (r + ω + 1) := by simp [hbdef, ix_N2]
  have hblow : ∀ k ≤ N, b k = upsilon (r + (k : Ordinal.{0})) := by
    intro k hk; simp [hbdef, ix_low hk]
  have hbmono : ∀ j k, j < k → k < N + 3 → b j < b k := fun j k hjk hk =>
    upsilon_normal.strictMono (ix_lt hjk (by omega))
  have hbge : ∀ k < N + 3, upsilon r ≤ b k := fun k hk => by
    rw [← hb0]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact le_rfl
    · exact (hbmono 0 k hk0 hk).le
  have hble : ∀ k < N + 3, b k ≤ upsilon (r + ω + 1) := fun k hk => by
    rw [← hbN2]
    rcases eq_or_lt_of_le (show k ≤ N + 2 by omega) with rfl | hlt
    · exact le_rfl
    · exact (hbmono k (N + 2) hlt (by omega)).le
  have hbU : ∀ k < N + 3, UpsPt (b k) ∧ b k < Om1 := by
    intro k hk
    refine ⟨?_, lt_of_le_of_lt (hble k hk) hδ1⟩
    rcases upsilon_mem (ix r 0 N k) with h0 | hU
    · exact absurd h0 (ne_of_gt (lt_of_lt_of_le hρ0 (hbge k hk)))
    · exact hU
  have hbC : Chain κ b (N + 3) :=
    ⟨hκU, hκ1, hbU, hbmono, fun k hk => lt_of_lt_of_le hκρ (hbge k hk)⟩
  -- the segments of the points of `F0` above `ρ`
  have hseg : ∀ z ∈ F0, upsilon r ≤ z → ∃ k < N + 3, InSeg (b k) z := by
    intro z hz hρz
    have hz1 : z < Om1 := lt_of_le_of_lt (hF0δ z hz) hδ1
    rcases lt_or_ge z (upsilon (r + ω)) with hzτ | hτz
    · have hex : ∃ n : ℕ, z < upsilon (r + ((n + 1 : ℕ) : Ordinal.{0})) :=
        ⟨N, (hNz z hz hzτ).trans (upsilon_normal.strictMono
          ((add_lt_add_iff_left r).2 (by exact_mod_cast Nat.lt_succ_self N)))⟩
      set n0 := Nat.find hex with hn0
      have hzn : z < upsilon (r + ((n0 + 1 : ℕ) : Ordinal.{0})) := Nat.find_spec hex
      have hn0N : n0 ≤ N := by
        by_contra hgt
        have hNn : N + 1 ≤ n0 := by omega
        have := Nat.find_min hex (show N < n0 by omega)
        exact this (lt_of_lt_of_le (hNz z hz hzτ) (upsilon_normal.strictMono.monotone
          ((add_le_add_iff_left r).2 (by exact_mod_cast Nat.le_succ N))))
      have hbz : b n0 ≤ z := by
        rw [hblow n0 hn0N]
        rcases Nat.eq_zero_or_pos n0 with h0 | hpos
        · rw [h0]; simpa using hρz
        · obtain ⟨n, hn⟩ : ∃ n, n0 = n + 1 := ⟨n0 - 1, by omega⟩
          have := Nat.find_min hex (show n < n0 by omega)
          rw [hn]; exact not_lt.1 this
      refine ⟨n0, by omega, hbz, hz1, fun u hu huU => ?_⟩
      have hnx := upsilon_isNext (r + (n0 : Ordinal.{0}))
      rw [succ_eq_add_one] at hnx
      rw [hblow n0 hn0N] at hu
      have := hnx.2.2 u hu huU
      refine lt_of_lt_of_le hzn (le_of_eq_of_le ?_ this)
      push_cast; rw [add_assoc]
    · rcases lt_or_ge z (upsilon (r + ω + 1)) with hzδ | hδz
      · refine ⟨N + 1, by omega, ?_⟩
        rw [hbN1]
        exact ⟨hτz, hz1, fun u hu huU => lt_of_lt_of_le hzδ (h.next.2.2 u hu huU)⟩
      · refine ⟨N + 2, by omega, ?_⟩
        rw [hbN2, le_antisymm (hF0δ z hz) hδz]
        exact InSeg.self hδ1
  -- `F0` lies in the domain of FRAG
  have hF0DD : (↑F0 : Set Ordinal.{0}) ⊆ DD κ b (N + 3) := by
    suffices H : ∀ z, z ∈ F0 → z ∈ DD κ b (N + 3) from fun z hz => H z hz
    intro z
    induction z using WellFoundedLT.induction with
    | ind z IH =>
    intro hz
    rcases lt_or_ge z (upsilon r) with hzρ | hρz
    · exact Iio_sub_DD _ (hLoκ z hz hzρ)
    obtain ⟨k, hk, hs⟩ := hseg z hz hρz
    have hU := hbU k hk
    have hzT : z ∈ Tset (b k) := ((inSeg_iff hU.1 hU.2).1 hs).2.2
    have hsb : sb z = b k := sb_eq hU.1 hs
    have hPar : ↑(Par (b k) z) ⊆ ClS (DD κ b k) := by
      intro p hp
      have hpb : p < b k := Par_sub (upsPt_inE hU.1) hU.2 hzT hp
      have hpz : p < z := lt_of_lt_of_le hpb hs.1
      have hpF : p ∈ F0 := hF0cl z hz hρz p (by rw [hsb]; exact Finset.mem_coe.1 hp) hpz
      exact ClS.sub _ (DD_down hbC (IH p hpz hpF) hk hpb)
    exact DD_mono (show k + 1 ≤ N + 3 by omega) (Or.inr ⟨hs, hzT, hPar⟩)
  -- the targets
  obtain ⟨A', hκA, hA'ρ, H⟩ := htarget κ hκρ
  set c : ℕ → Ordinal.{0} := fun k => upsilon (ix A' 2 N k) with hcdef
  have hc0 : c 0 = upsilon (A' + 2) := by simp [hcdef, ix_low (Nat.zero_le N)]
  have hcN1 : c (N + 1) = upsilon (A' + ω) := by simp [hcdef, ix_N1]
  have hcN2 : c (N + 2) = upsilon (A' + ω + 1) := by simp [hcdef, ix_N2]
  have hcmono : ∀ j k, j < k → k < N + 3 → c j < c k := fun j k hjk hk =>
    upsilon_normal.strictMono (ix_lt hjk (by omega))
  have hTc : ∀ k < N + 3, upsilon (A' + 1) < c k := by
    intro k hk
    refine upsilon_normal.strictMono (lt_of_lt_of_le ?_ (ix_ge (show k ≤ N + 2 by omega)))
    exact (add_lt_add_iff_left A').2 (by exact_mod_cast (show 1 < 2 by omega))
  have hcle : ∀ k < N + 3, c k ≤ upsilon (A' + ω + 1) := fun k hk =>
    upsilon_normal.strictMono.monotone (ix_top (show k ≤ N + 2 by omega))
  have hcU : ∀ k < N + 3, UpsPt (c k) ∧ c k < Om1 := by
    intro k hk
    refine ⟨?_, lt_of_le_of_lt (hcle k hk) H.β1⟩
    rcases upsilon_mem (ix A' 2 N k) with h0 | hU
    · exact absurd h0 (ne_of_gt (lt_of_le_of_lt zero_le (hTc k hk)))
    · exact hU
  have hcC : Chain κ c (N + 3) :=
    ⟨hκU, hκ1, hcU, hcmono, fun k hk => hκA.trans (hTc k hk)⟩
  -- FRAG
  obtain ⟨Ψ, Q1, Q2, Q3, Q4, Q5, -, -⟩ := frag hbC hcC F0 hF0DD
  have hΨb : ∀ z ∈ F0, upsilon r ≤ z → c 0 ≤ Ψ z ∧ Ψ z ≤ upsilon (A' + ω + 1) := by
    intro z hz hρz
    obtain ⟨k, hk, hs⟩ := hseg z hz hρz
    have hs' := Q2 k hk z hz hs
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hk0
      · exact hs'.1
      · exact (hcmono 0 k hk0 hk).le.trans hs'.1
    · rcases eq_or_lt_of_le (show k ≤ N + 2 by omega) with rfl | hlt
      · have hzδ : z = upsilon (r + ω + 1) := le_antisymm (hF0δ z hz) (hbN2 ▸ hs.1)
        have hδF : b (N + 2) ∈ F0 := by rw [hbN2, ← hzδ]; exact hz
        rw [hzδ, ← hbN2, Q3 (N + 2) (by omega) hδF, hcN2]
      · rw [← hcN2]
        exact (hs'.2.2 (c (N + 2)) (hcmono k (N + 2) hlt (by omega)) (hcU (N + 2) (by omega)).1).le
  -- the leading-term map on `X ∪ Y`
  have hAF0 : (↑(X ∪ Y) : Set Ordinal.{0}) ⊆ ↑F0 := fun z hz => hAF z (Finset.mem_coe.1 hz)
  have hΨA : ArithIso ↑(X ∪ Y) (Ψ '' ↑(X ∪ Y)) Ψ :=
    ⟨(Q4.2.1.mono hAF0).injOn.bijOn_image, Q4.2.1.mono hAF0,
      fun x hx y hy z hz => Q4.2.2 x (hAF0 hx) y (hAF0 hy) z (hAF0 hz)⟩
  obtain ⟨hψ, hψc, hψle, hψeq, hψfix⟩ := close_map hXY hΨA
  set ψ := ext (fun a => mc (Ψ a)) with hψdef
  have hXρ : ∀ x ∈ X, x < upsilon r := hX
  have hψX : ∀ x ∈ X, ψ x = x := by
    intro x hx
    refine hψfix x (by simp [hx]) (fun a ha => Q1 a ?_ ?_)
    · exact hAF a (hXY.pc_mem x (by simp [hx]) a ha)
    · exact lt_of_le_of_lt (le_of_mem_pc ha) (hLoκ x (hAF x (by simp [hx])) (hX x hx))
  have hmem : ∀ z, z ∈ X ∪ Y → z ∈ (↑(X ∪ Y) : Set Ordinal.{0}) := fun z hz => hz
  have hψYβ : ∀ y ∈ Y, ψ y ≤ upsilon (A' + ω + 1) := fun y hy =>
    (hψle y (by simp [hy])).trans (hΨb y (hAF y (by simp [hy])) (hYδ y hy).1).2
  have hXlt : ∀ c' ∈ (↑(X ∪ Y) : Set Ordinal.{0}), ∀ d ∈ X, c' ≤ d → c' ∈ X := by
    intro c' hc' d hd hcd
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hc') with hc' | hc'
    · exact hc'
    · exact absurd (lt_of_le_of_lt hcd (hX d hd)) (not_lt.2 (hYδ c' hc').1)
  have hψbk : ∀ k < N + 3, b k ∈ (↑(X ∪ Y) : Set Ordinal.{0}) → ψ (b k) = c k := by
    intro k hk hbA
    have hΨbk := Q3 k hk (hAF0 hbA)
    rw [hψeq (b k) hbA (indec_of_upsPt (hbU k hk).1)
      (by rw [hΨbk]; exact indec_of_upsPt (hcU k hk).1), hΨbk]
  have hψmono : StrictMonoOn ψ ↑(X ∪ Y) := hψ.2.1
  have hT2 : upsilon (A' + 1) < upsilon (A' + 2) := hc0 ▸ hTc 0 (by omega)
  have hU2 : UpsPt (upsilon (A' + 2)) := hc0 ▸ (hcU 0 (by omega)).1
  have hcov : Cov R2C R2C ↑(X ∪ Y) (ψ '' ↑(X ∪ Y)) ψ := by
    refine ⟨hψ, ?_, ?_⟩
    · intro c' hc' d hd hcd
      change le1 c' d at hcd
      change le1 (ψ c') (ψ d)
      rcases eq_or_lt_of_le (le1_le hcd) with e | hlt
      · rw [e]; exact le1_refl _
      rcases Finset.mem_union.1 (Finset.mem_coe.1 hd) with hdX | hdY
      · rw [hψX c' (hXlt c' hc' d hdX hlt.le), hψX d hdX]; exact hcd
      have hdβ := hψYβ d hdY
      rcases lt_trichotomy c' (upsilon r) with hcρ | e | hρc
      · exact absurd hcd (h.below c' hcρ d (hYδ d hdY).1)
      · have hρA : b 0 ∈ (↑(X ∪ Y) : Set Ordinal.{0}) := by rw [hb0, ← e]; exact hc'
        have hψρ := hψbk 0 (by omega) hρA
        rw [hb0, hc0] at hψρ
        have hle : upsilon (A' + 2) ≤ ψ d := by
          rw [← hψρ]
          exact (hψmono (by rw [← e]; exact hc') hd (by rw [← e]; exact hlt)).le
        rw [e, hψρ]
        exact (H.le1_lowβ _ _ hT2 hdβ).2 (hU2.2 _ hle)
      · have hcF := hAF0 hc'
        have hdF := hAF0 hd
        have hR := inc1 (lt_of_le_of_lt (hYδ d hdY).2 hδ1) hcd
        have hR' := (Q5 c' hcF d hdF).1 hR
        have hΨlt : Ψ c' < Ψ d := Q4.2.1 hcF hdF hlt
        have hψc : ψ c' = Ψ c' := hψeq c' hc' (indec_of_lt1R hR hlt) (indec_of_lt1R hR' hΨlt)
        have hψlt : ψ c' < ψ d := hψmono hc' hd hlt
        have hR'' : le1R (ψ c') (ψ d) :=
          le1R_of_le hψlt.le (hψle d hd) (by rw [hψc]; exact hR')
        have hTψ : upsilon (A' + 1) < ψ c' := by
          rw [hψc]; exact lt_of_lt_of_le (hTc 0 (by omega)) (hΨb c' hcF hρc.le).1
        exact (H.le1_lowβ _ _ hTψ hdβ).2 hR''
    · intro c' hc' d hd hcd
      change le2 c' d at hcd
      change le2 (ψ c') (ψ d)
      rcases eq_or_lt_of_le (le2_le hcd) with e | hlt
      · rw [e]; exact le2_refl _
      rcases Finset.mem_union.1 (Finset.mem_coe.1 hd) with hdX | hdY
      · rw [hψX c' (hXlt c' hc' d hdX hlt.le), hψX d hdX]; exact hcd
      rcases lt_trichotomy c' (upsilon r) with hcρ | e | hρc
      · exact absurd (le2_le1 hcd) (h.below c' hcρ d (hYδ d hdY).1)
      · rw [e] at hcd hlt; exact absurd hcd (h.noSucc d hlt)
      have hρd : upsilon r < d := hρc.trans hlt
      rcases lt_or_ge d (upsilon (r + ω + 1)) with hdδ | hδd
      · exact absurd hcd (h.noPairGap c' d hlt hρd hdδ)
      have hdδ : d = upsilon (r + ω + 1) := le_antisymm (hYδ d hdY).2 hδd
      have hcτ : c' = upsilon (r + ω) :=
        h.pairs_at_top (by rw [← hdδ]; exact hlt) (by rw [← hdδ]; exact hcd)
      have hτA : b (N + 1) ∈ (↑(X ∪ Y) : Set Ordinal.{0}) := by rw [hbN1, ← hcτ]; exact hc'
      have hδA : b (N + 2) ∈ (↑(X ∪ Y) : Set Ordinal.{0}) := by rw [hbN2, ← hdδ]; exact hd
      have e1 := hψbk (N + 1) (by omega) hτA
      have e2 := hψbk (N + 2) (by omega) hδA
      rw [hbN1, hcN1] at e1
      rw [hbN2, hcN2] at e2
      rw [hcτ, hdδ, e1, e2]; exact H.pair
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
  refine ⟨Y.image ψ, ?_, ?_, ?_, ψ, ?_⟩
  · intro y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    exact lt_of_le_of_lt (hψYβ t ht) hA'ρ
  · intro x hx y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    have := hψmono (show x ∈ (↑(X ∪ Y) : Set Ordinal.{0}) by simp [hx])
      (show t ∈ (↑(X ∪ Y) : Set Ordinal.{0}) by simp [ht])
      (lt_of_lt_of_le (hX x hx) (hYδ t ht).1)
    rwa [hψX x hx] at this
  · rw [himg]; exact hψc
  · rw [himg]; exact hcov

/-- Lower blocks from a chain of block contexts. -/
theorem target_of_chain {a T0 : Ordinal.{0}}
    (hctx : ∀ j : ℕ, BlkCtx (topA a T0 j) (lpA a j) (topA a T0 (j + 1)))
    (hTa : upsilon a ≤ T0) : ∀ κ' < upsilon (a + ω * ω), ∃ A', κ' < upsilon (A' + 1) ∧
      upsilon (A' + ω + 1) < upsilon (a + ω * ω) ∧
      BlkCtx (upsilon (A' + 1)) (upsilon (A' + ω)) (upsilon (A' + ω + 1)) := by
  intro κ' hκ'
  have hj : ∃ j0, κ' ≤ topA a T0 j0 := by
    rcases chainA_sup hTa hκ' with h0 | ⟨j, hj⟩
    · exact ⟨0, h0⟩
    · exact ⟨j + 1, hj⟩
  obtain ⟨j0, hj0⟩ := hj
  have hA : a + ω * ((j0 + 1 : ℕ) : Ordinal.{0}) = a + ω * (j0 : Ordinal.{0}) + ω := by
    rw [omega_mul_succ, add_assoc]
  refine ⟨a + ω * (j0 : Ordinal.{0}) + ω, ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt hj0 (chainA_topMono hctx (Nat.lt_succ_self j0))
  · have := chainA_top_lt hctx (j0 + 1)
    simp only [topA] at this
    rwa [hA] at this
  · have := hctx (j0 + 1)
    simp only [topA, lpA] at this
    rwa [hA] at this

/-- **Lemma RS^h** in `R₂^C`: `ρ_{h+1} ≤₁ δ_{h+1} + 1` for every restart below `υ_{ω³}` (Lean `h` =
paper `h − 1`). -/
theorem rs_h (h : ℕ) : le1 (upsilon (rI h)) (upsilon (rI h + ω + 1) + 1) := by
  rcases h with _ | h
  · refine rs_gen (rstCtx 0).1 ?_
    rw [← rI_zero]
    exact target_of_chain ctx0 (by rw [upsilon_zero])
  · refine rs_gen (rstCtx (h + 1)).1 ?_
    rw [← rI_succ h]
    exact target_of_chain (rstCtx h).2 ((rstCtx h).1.next.1.le.trans le_self_add)

/-- **The reach of every restart below `υ_{ω³}`** in `R₂^C` (Lean `h` = paper `h − 1`):
`lh(ρ_{h+1}) = δ_{h+1} + 1` (Lemmas RS^h
and TOP^h). -/
theorem reach_rst (h : ℕ) : IsReach R2C (upsilon (rI h)) (upsilon (rI h + ω + 1) + 1) := by
  refine ⟨rs_h h, fun g hg => ?_⟩
  by_contra hlt
  exact (rstCtx h).1.top g (not_le.1 hlt) hg

end Googology.Trans.PoR.InaccPsi.R2
