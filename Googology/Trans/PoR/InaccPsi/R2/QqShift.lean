import Googology.Trans.PoR.InaccPsi.R2.QqEmb

/-!
# The shift criterion SHIFT in `R₂^C`

The data of SHIFT (the shape of Wilken 2020, Thm 21.13, one level up; the docs' PAIR uses it with
`a = L(ω)`, `b = L(ω+1)`, `c_n = L(n)`):

* `c` is monotone, `c n < a`, and `{c n}` is cofinal in `a`;
* (C1) `c (n+1) ≤₁ a` for every `n`;
* (EMB) `B n` embeds `[0, c (n+1))` into `[0, b)`: strictly increasing, keeps and reflects `+`, `≤₁`,
  `≤₂`, with closed range ([C09] Def 5.2: a covering is a closed embedding); and `B n` fixes `[0, c n)`;
* (ONTO-FIN) every finite `Y ⊆ [a, b)` lies in the range of `B n` on `[0, c (n+1))` for arbitrarily
  large `n`.

* `qqShift` (**SHIFT**): the data give `a ≤₂ b` in `R₂^C`.  Clause 1 of [C09] Def 5.3 for `≤₂`: pull
  `Y` back by `B n` (`qqInv_cov`, `qqInv_closed`); clause (d): a pulled-back `y'` with `y ≤₁ b` is `≤₁`
  every point of `[y', c (n+1))`, hence `y' ≤₁ c (n+1) ≤₁ a`.  Clause 2: a pattern realized cofinally
  below `a` is copied below `c (n+1)` above `B n⁻¹(c')` by (C1) ([C09] Lemma 5.5 (1), `le1_cof`) and
  pushed forward by `B n` above `c'` (`qqFwd_cov`, `qqFwd_closed`).  The hypothesis `a ≤₁ b` of the
  docs' form is not needed: it follows (`qqShift_le1`);
* `qqShift_P`: (P) at `(a, b)`: cofinally many `α < a` have `α ≤₁ b`.

No axiom.

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Qq

open Ordinal Googology.Trans.PoR.InaccPsi.R2

section Shift

variable {a b : Ordinal.{0}} {c : ℕ → Ordinal.{0}} {B : ℕ → Ordinal.{0} → Ordinal.{0}}
  (hmono : Monotone c) (hca : ∀ n, c n < a) (hcof : ∀ γ < a, ∃ n, γ < c n)
  (hc1 : ∀ n, le1 (c (n + 1)) a) (hab : a ≤ b)
  (hBm : ∀ n, StrictMonoOn (B n) (Set.Iio (c (n + 1))))
  (hBb : ∀ n, ∀ x < c (n + 1), B n x < b)
  (hBadd : ∀ n, ∀ x < c (n + 1), ∀ y < c (n + 1), ∀ z < c (n + 1),
    (x + y = z ↔ B n x + B n y = B n z))
  (hB1 : ∀ n, ∀ x < c (n + 1), ∀ y < c (n + 1), (le1 x y ↔ le1 (B n x) (B n y)))
  (hB2 : ∀ n, ∀ x < c (n + 1), ∀ y < c (n + 1), (le2 x y ↔ le2 (B n x) (B n y)))
  (hBcl : ∀ n, Closed (B n '' Set.Iio (c (n + 1))))
  (hfix : ∀ n, ∀ x < c n, B n x = x)
  (honto : ∀ Y : Finset Ordinal.{0}, (∀ y ∈ Y, a ≤ y ∧ y < b) → ∀ N, ∃ n, N ≤ n ∧
    ∀ y ∈ Y, ∃ y' < c (n + 1), B n y' = y)

include hmono hca hcof hc1 hab hBm hBb hBadd hB1 hB2 hBcl hfix honto

/-- **SHIFT in `R₂^C`**: the data of SHIFT give `a ≤₂ b`. -/
theorem qqShift : le2 a b := by
  classical
  refine le2_iff.2 ⟨hab, fun X Y hX hY hXY => ?_, fun X hX Z P hZ hC => ?_⟩
  · -- clause 1: pull `Y` back by `B n`
    obtain ⟨N, hN⟩ := qqFin_below hmono hcof X hX
    obtain ⟨n, hNn, hYn⟩ := honto Y hY N
    set d := c (n + 1) with hd
    have hcn : c n ≤ d := hmono (Nat.le_succ n)
    have hda : d < a := hca (n + 1)
    let g : Ordinal.{0} → Ordinal.{0} := fun y =>
      if hy : ∃ y' < d, B n y' = y then Classical.choose hy else 0
    have hg : ∀ y ∈ Y, g y < d ∧ B n (g y) = y := by
      intro y hy
      have hex : ∃ y' < d, B n y' = y := hYn y hy
      have hsp := Classical.choose_spec hex
      simp only [g, dif_pos hex]
      exact hsp
    let h : Ordinal.{0} → Ordinal.{0} := fun z => if z < a then z else g z
    have hXa : ∀ x ∈ X, x < c n := fun x hx => (hN x hx).trans_le (hmono hNn)
    have hhX : ∀ x ∈ X, h x = x := fun x hx => by simp only [h, if_pos (hX x hx)]
    have hhY : ∀ y ∈ Y, h y = g y := fun y hy => by
      simp only [h, if_neg (not_lt.2 (hY y hy).1)]
    have hA : ∀ u ∈ (↑(X ∪ Y) : Set Ordinal.{0}), h u < d ∧ B n (h u) = u := by
      intro u hu
      rcases Finset.mem_union.1 (Finset.mem_coe.1 hu) with hu | hu
      · rw [hhX u hu]; exact ⟨(hXa u hu).trans_le hcn, hfix n u (hXa u hu)⟩
      · rw [hhY u hu]; exact hg u hu
    have hgc : ∀ y ∈ Y, c n ≤ g y := by
      intro y hy
      by_contra hlt
      rw [not_le] at hlt
      have e := hfix n (g y) hlt
      rw [(hg y hy).2] at e
      exact absurd (e ▸ hlt.trans (hca n)) (not_lt.2 (hY y hy).1)
    have himg := qqImage_fix (Y := Y) hhX
    refine ⟨Y.image h, ?_, ?_, ?_, h, ?_, ?_⟩
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
      rw [hhY y hy]; exact (hg y hy).1.trans hda
    · intro x hx z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
      rw [hhY y hy]; exact (hXa x hx).trans_le (hgc y hy)
    · rw [himg]; exact qqInv_closed (hBm n) (hBadd n) hA hXY
    · rw [himg]; exact qqInv_cov (hBm n) (hBadd n) (hB1 n) (hB2 n) hA
    · -- clause (d)
      intro y hy hyb
      show le1 (h y) a
      rw [hhY y hy]
      obtain ⟨hyd, hBy⟩ := hg y hy
      have hy0 : g y ≠ 0 := by
        intro e
        have hB0 : B n 0 = 0 := by
          have hd0 : (0 : Ordinal.{0}) < d := lt_of_le_of_lt zero_le hyd
          have := (hBadd n 0 hd0 0 hd0 0 hd0).1 (add_zero 0)
          exact add_self_eq_self this
        rw [e, hB0] at hBy
        exact absurd (hBy ▸ (hY y hy).1) (not_le.2 (lt_of_le_of_lt zero_le (hca 0)))
      have hd1 : 1 < d := lt_of_le_of_lt (Order.one_le_iff_ne_zero.2 hy0) hyd
      have hdI : Indec d := indec_of_lt1 (hc1 n) hda
      have hall : ∀ z, g y ≤ z → z < d → le1 (g y) z := by
        intro z hyz hzd
        have hBz : B n (g y) ≤ B n z := (hBm n).monotoneOn hyd hzd hyz
        rw [hBy] at hBz
        exact (hB1 n (g y) hyd z hzd).2 (by
          rw [hBy]; exact le1_of_le_of_le1 hBz (hBb n z hzd).le hyb)
      have hyd1 : le1 (g y) d := le1_of_cofinal hyd.le fun z hyz hzd =>
        ⟨z + 1, Order.lt_add_one_iff.2 le_rfl,
          hall (z + 1) (hyz.trans le_self_add) (hdI.add_lt hzd hd1)⟩
      exact le1_trans hyd1 (hc1 n)
  · -- clause 2: patterns cofinal below `a` are cofinal below `b`
    intro c' hc'
    by_cases hc'a : c' < a
    · obtain ⟨Y, hY, hcl, g, hg⟩ := hC c' hc'a
      exact ⟨Y, fun y hy => ⟨(hY y hy).1, (hY y hy).2.trans_le hab⟩, hcl, g, hg⟩
    obtain ⟨N, hN⟩ := qqFin_below hmono hcof X hX
    obtain ⟨n, hNn, hon⟩ := honto {c'} (by simpa using ⟨not_lt.1 hc'a, hc'⟩) N
    obtain ⟨d0, hd0, hBd0⟩ := hon c' (Finset.mem_singleton_self c')
    have hXn : ∀ x ∈ X, x < c n := fun x hx => (hN x hx).trans_le (hmono hNn)
    have hXd : ∀ x ∈ X, x < c (n + 1) := fun x hx => (hXn x hx).trans_le (hmono (Nat.le_succ n))
    obtain ⟨Y0, hY0, hcl0, g, hg⟩ := hC (c (n + 1)) (hca (n + 1))
    obtain ⟨Yt, hYt, -, hclt, f, hf, -, -⟩ := le1_cof (hc1 n) hd0 X Y0 hXd
      (fun y hy => ⟨(hY0 y hy).1.le, (hY0 y hy).2⟩) hcl0
    have hsub : (↑(X ∪ Yt) : Set Ordinal.{0}) ⊆ Set.Iio (c (n + 1)) := by
      intro z hz
      rcases Finset.mem_union.1 (Finset.mem_coe.1 hz) with hz | hz
      · exact hXd z hz
      · exact (hYt z hz).2
    have himg := qqImage_fix (Y := Yt) (fun x hx => hfix n x (hXn x hx))
    refine ⟨Yt.image (B n), ?_, ?_, B n ∘ (f ∘ g), ?_⟩
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
      refine ⟨?_, hBb n y (hYt y hy).2⟩
      rw [← hBd0]; exact hBm n hd0 (hYt y hy).2 (hYt y hy).1
    · rw [himg]; exact qqFwd_closed (hBm n) (hBadd n) (hBcl n) hsub hclt
    · rw [himg]
      exact (hg.comp hf).comp (qqFwd_cov (hBm n) (hBadd n) (hB1 n) (hB2 n) hsub)

/-- The data of SHIFT give `a ≤₁ b`. -/
theorem qqShift_le1 : le1 a b :=
  le2_le1 (qqShift hmono hca hcof hc1 hab hBm hBb hBadd hB1 hB2 hBcl hfix honto)

/-- (P) at `(a, b)`: cofinally many `α < a` have `α ≤₁ b`. -/
theorem qqShift_P : ∀ γ < a, ∃ α, γ < α ∧ α < a ∧ le1 α b := by
  intro γ hγ
  obtain ⟨n, hn⟩ := hcof γ hγ
  exact ⟨c (n + 1), hn.trans_le (hmono (Nat.le_succ n)), hca (n + 1),
    le1_trans (hc1 n) (qqShift_le1 hmono hca hcof hc1 hab hBm hBb hBadd hB1 hB2 hBcl hfix honto)⟩

end Shift

end Googology.Trans.PoR.InaccPsi.R2.Qq
