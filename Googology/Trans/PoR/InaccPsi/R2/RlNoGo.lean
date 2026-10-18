import Googology.Trans.PoR.InaccPsi.R2.CvNamed

/-!
# The global realizer maps of `Cv.CvReal` do not exist past `a + a`

`L(ξ) = Nc.ncL S ξ`, `m* = L(0)`, `P' = Nc.ncPp S`, `P = Nm.Pv S`.

The copying principle `Cv.cvLe1_of_maps` and the realizer maps `Cv.CvReal S a t` ask for one map
`D_k` on the whole interval `[a, t)` that is strictly increasing there, keeps the graph of `+` on
`[0, c_k) ∪ [a, t)`, and sends `[a, t)` below `a`.  This file proves that no such map exists once
`a + a < t`:

* `rlId_le`: a strictly increasing map on `[0, a)` is at least the identity there;
* `rlNoGo` (**the obstruction**): if `D` is strictly increasing on `[a, t)`, `D(a + a) = D(a) + D(a)`,
  `D(a) < a` and `a + a < t`, then `z ↦ -D(a) + D(a + z)` is a strictly increasing map of `[0, a)`
  into `[0, D(a))`, which is impossible at `z = D(a)`;
* `rlMaps_le`: the hypotheses of `Cv.cvLe1_of_maps` force `b ≤ a + a`;
  `rlReal_le`: `CvReal S a t → t ≤ a + a`; `rlRealCof_le`: `CvRealCof S a b → b ≤ a + a`;
* the named restarts are additively principal and increasing, so **every realizer hypothesis of the
  round-64 road through `Cv.CvReal` is false** (those theorems are removed from `R2.CvNamed`):
  `rlNoReal_m` (at `m*`, target `L(1)`), `rlNoReal_n` (at `L(n+1)`, target `L(n+2)`),
  `rlNoReal_w` (at `L(ω)`, target `L(ω+1)`), `rlNoReal_cross` (the CROSS targets
  `P(Ω_ω + P'·(n+1) + c')`, `c' ≥ 1`).

No axiom is added.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rl

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cv

/-- A strictly increasing map on `[0, a)` is at least the identity there. -/
theorem rlId_le {a : Ordinal.{0}} {g : Ordinal.{0} → Ordinal.{0}} (hg : StrictMonoOn g (Iio a)) :
    ∀ z < a, z ≤ g z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hz
  by_contra h
  have h' : g z < z := not_le.1 h
  have h1 : g (g z) < g z := hg (show g z < a from h'.trans hz) (show z < a from hz) h'
  exact absurd (IH (g z) h' (h'.trans hz)) (not_le.2 h1)

/-- **The obstruction**: no map strictly increasing on `[a, t)` with `D(a + a) = D(a) + D(a)` and
`D(a) < a`, when `a + a < t`. -/
theorem rlNoGo {a t : Ordinal.{0}} {D : Ordinal.{0} → Ordinal.{0}} (hDm : StrictMonoOn D (Ico a t))
    (hadd : D (a + a) = D a + D a) (hwin : D a < a) (ht : a + a < t) : False := by
  have hmem : ∀ z < a, a + z ∈ Ico a t := fun z hz =>
    ⟨le_self_add, ((add_lt_add_iff_left a).2 hz).trans ht⟩
  have haa : a + a ∈ Ico a t := ⟨le_self_add, ht⟩
  have ha : a ∈ Ico a t := ⟨le_rfl, le_self_add.trans_lt ht⟩
  have hge : ∀ z < a, D a ≤ D (a + z) := fun z hz =>
    hDm.monotoneOn ha (hmem z hz) le_self_add
  have hlt : ∀ z < a, D (a + z) < D a + D a := fun z hz => by
    rw [← hadd]; exact hDm (hmem z hz) haa ((add_lt_add_iff_left a).2 hz)
  have hg : ∀ z < a, D a + (D (a + z) - D a) = D (a + z) := fun z hz =>
    Ordinal.add_sub_cancel_of_le (hge z hz)
  have hgm : StrictMonoOn (fun z => D (a + z) - D a) (Iio a) := by
    intro z hz z' hz' hzz'
    have h := hDm (hmem z hz) (hmem z' hz') ((add_lt_add_iff_left a).2 hzz')
    rw [← hg z hz, ← hg z' hz'] at h
    exact (add_lt_add_iff_left (D a)).1 h
  have h1 := rlId_le hgm (D a) hwin
  have h2 : D (a + D a) - D a < D a := by
    have h := hlt (D a) hwin
    rw [← hg (D a) hwin] at h
    exact (add_lt_add_iff_left (D a)).1 h
  exact absurd h1 (not_le.2 h2)

/-- **The hypotheses of `Cv.cvLe1_of_maps` force `b ≤ a + a`.** -/
theorem rlMaps_le {a b : Ordinal.{0}} {c : ℕ → Ordinal.{0}} {D : ℕ → Ordinal.{0} → Ordinal.{0}}
    (hDm : ∀ k, StrictMonoOn (D k) (Ico a b))
    (hDadd : ∀ k, ∀ x ∈ CvDom (c k) a b, ∀ y ∈ CvDom (c k) a b, ∀ z ∈ CvDom (c k) a b,
      (x + y = z ↔ D k x + D k y = D k z))
    (hDwin : ∀ k, ∀ y, a ≤ y → y < b → c k ≤ D k y ∧ D k y < a) : b ≤ a + a := by
  by_contra hlt
  have ht : a + a < b := not_le.1 hlt
  have hat : a < b := le_self_add.trans_lt ht
  have ha : a ∈ CvDom (c 0) a b := Or.inr ⟨le_rfl, hat⟩
  have haa : a + a ∈ CvDom (c 0) a b := Or.inr ⟨le_self_add, ht⟩
  exact rlNoGo (hDm 0) ((hDadd 0 a ha a ha (a + a) haa).1 rfl).symm (hDwin 0 a le_rfl hat).2 ht

variable {S : InaccSeq.{0}}

/-- **`CvReal S a t` forces `t ≤ a + a`.** -/
theorem rlReal_le {a t : Ordinal.{0}} (h : CvReal S a t) : t ≤ a + a := by
  obtain ⟨c, D, μ, -, -, hDm, hDadd, -, -, hDwin, -, -⟩ := h
  exact rlMaps_le hDm hDadd hDwin

/-- **`CvRealCof S a b` forces `b ≤ a + a`.** -/
theorem rlRealCof_le {a b : Ordinal.{0}} (h : CvRealCof S a b) : b ≤ a + a := by
  by_contra hlt
  have hb : a + a < b := not_le.1 hlt
  obtain ⟨t, hyt, -, hR⟩ := h (a + a) le_self_add hb
  exact absurd (rlReal_le hR) (not_le.2 hyt)

/-- `Ω_ω` is good. -/
theorem rlGood_W : Bt.Good S (Om ω) := by
  unfold Bt.Good
  have hw2 := Pp.ppSC_ww (SC_psi Low.InR_Om_one (S := S) (ConjT.Aη S (Om ω)))
  exact CSet.Om_mem (CSet.of_lt (lt_of_le_of_lt (le_mul_left _ omega0_pos) hw2))

/-- `1 < P'`. -/
theorem rlOne_lt_Pp : (1 : Ordinal.{0}) < Nc.ncPp S :=
  lt_of_lt_of_le (by
      have := mul_lt_mul_of_pos_left (one_lt_omega0) omega0_pos
      rw [mul_one] at this
      exact one_lt_omega0.trans this)
    (Pp.ppSC_ww (Nc.ncPp_SC S)).le

/-- `m* < L(1)`. -/
theorem rlM_lt_L1 : Nc.ncL S 0 < Nc.ncL S 1 := by
  rw [Lw.lw_L_eq S 0, Lw.lw_L_eq S 1, mul_zero, add_zero, mul_one]
  exact (Pv_lt_succ rlGood_W).trans_le (Pv_mono (add_le_add_right rlOne_lt_Pp.le _))

/-- **No realizer maps at `m*`** (`CvRealCof S m* L(1)` is false). -/
theorem rlNoReal_m : ¬ CvRealCof S (Nc.ncL S 0) (Nc.ncL S 1) := fun h =>
  absurd (rlRealCof_le h) (not_le.2 (Bc.ncL_add_lt rlM_lt_L1 rlM_lt_L1))

/-- **No realizer maps at `L(n+1)`** (`CvRealCof S L(n+1) L(n+2)` is false). -/
theorem rlNoReal_n (n : ℕ) :
    ¬ CvRealCof S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})) :=
  fun h => absurd (rlRealCof_le h)
    (not_le.2 (Bc.ncL_add_lt (Pp.ppL_lt_succ n) (Pp.ppL_lt_succ n)))

/-- **No realizer maps at `L(ω)`** (`CvRealCof S L(ω) L(ω+1)` is false). -/
theorem rlNoReal_w : ¬ CvRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1)) := fun h =>
  absurd (rlRealCof_le h) (not_le.2 (Bc.ncL_add_lt (Qq.qqL_lt_succ S) (Qq.qqL_lt_succ S)))

/-- **No realizer maps at the CROSS targets** (the round-64 CROSS hypothesis through `CvReal` is false):
for `c' ≥ 1`, `L(n+1) + L(n+1) < P(Ω_ω + P'·(n+1) + c')`. -/
theorem rlNoReal_cross (n : ℕ) {c' : Ordinal.{0}} (hc : 1 ≤ c') :
    ¬ CvReal S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Pv S (Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) + c')) := by
  intro h
  have hg := Pp.ppGood_eta (S := S) n (y := 0) (mul_pos omega0_pos omega0_pos)
  rw [add_zero] at hg
  have ha : Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) <
      Pv S (Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) + c') := by
    rw [Lw.lw_L_eq S]
    exact (Pv_lt_succ hg).trans_le (Pv_mono (add_le_add_right hc _))
  exact absurd (rlReal_le h) (not_le.2 ((Pv_SC S _).isPrincipal ha ha))

/-- **The round-64 CROSS hypothesis through `CvReal` is false.** -/
theorem rlNoReal_crossAll :
    ¬ (∀ n : ℕ, ∀ c < Nc.ncPp S, ∃ c', c ≤ c' ∧ c' < Nc.ncPp S ∧
      CvReal S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
        (Pv S (Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) + c'))) := by
  intro h
  obtain ⟨c', hc', -, hR⟩ := h 0 1 rlOne_lt_Pp
  exact rlNoReal_cross 0 hc' hR

end Googology.Trans.PoR.InaccPsi.R2.Rl
