import Googology.Trans.PoR.InaccPsi.R2.SwRoad

/-!
# The Veblen levels below `Γ₀`: fixed points, towers, the index of a code and of a hull element

`φ = veblen`, `W^E = Ω₂^E` (`Le.leWe`), `Ω^x = Ω₁^x` (`Le.leOe`), codes = `Le.LeCl κ Q` (generator `κ`, bound `Q`,
both strongly critical), `Γ₀ = gamma 0`.  A **small Veblen level** (`TaSm a`) is `1 ≤ a < Γ₀`: it lies below every
strongly critical ordinal, so it is a code over every `Q`, a member of every closure above `Γ₀`, and it is fixed by
every reading and every base change.

* `taGam_le_SC` (`Γ₀ ≤ Q` for strongly critical `Q`), `taSm_lt_SC`;
* `taK_mul_veb`, `taWe_veb` (**`W^{φ(a, Ω₂ + y)} = φ(a, Ω₂ + y)` for `y ≥ 1`**), `taOe_veb`;
* `taIdx_ex` (**the index of an ordinal for `φ(a, ·)`**: `φ(a, u) ≤ c < φ(a, u+1)`);
* `taVeb_succ` (`φ(a'+1, z+1) = nfp φ(a', ·) (φ(a'+1, z) + 1)`), `taTw_cof` (**a dominating tower is cofinal**),
  `taVeb_lim_cof` (**at a limit level `a`: every `x < φ(a, z+1)` is below `φ(a', φ(a, z) + 1)` for some
  `a' < a`**), `taVeb_lim_lt`;
* `taCl_dec` (**THE FINE DECOMPOSITION: a code `w < φ(a, X)`, `X` a limit, is below `φ(a, u)` for a code
  `u < X`**), `taCl_idx` (**the index of a code is a code**), `taCl_inv` (**`φ(a, y)` a code gives `y` a
  code**);
* `taHull_idx` (**the index of a member of a closure is a member**), `taSub_mem` (**`x - y` is a member for every
  member `x`**).

No new axiom.  New definition: `TaSm`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ta

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Ld

variable {S : InaccSeq.{0}}

/-- **A small Veblen level**: `1 ≤ a < Γ₀`. -/
def TaSm (a : Ordinal.{0}) : Prop := 1 ≤ a ∧ a < gamma 0

/-- `Γ₀` is the least strongly critical ordinal. -/
theorem taGam_le_SC {Q : Ordinal.{0}} (hQ : SC Q) : gamma 0 ≤ Q := by
  obtain ⟨y, hy⟩ := Ls.lsSC_gamma hQ
  rw [← hy]; exact gamma_le_gamma.2 zero_le

theorem taSm_lt_SC {a Q : Ordinal.{0}} (ha : TaSm a) (hQ : SC Q) : a < Q := ha.2.trans_le (taGam_le_SC hQ)

theorem taSm_ne0 {a : Ordinal.{0}} (ha : TaSm a) : a ≠ 0 := (zero_lt_one.trans_le ha.1).ne'

theorem taSm_lt_Om1 {a : Ordinal.{0}} (ha : TaSm a) : a < Om 1 := taSm_lt_SC ha Ph.ph_SC_Om1

theorem taSm_lt_Om2 {a : Ordinal.{0}} (ha : TaSm a) : a < Om (1 + 1) := taSm_lt_SC ha ldOm2_SC

/-! ## Fixed points -/

/-- `κ·φ(a, y) = φ(a, y)` when `κ < φ(a, y)`, `a ≠ 0`. -/
theorem taK_mul_veb {κ a y : Ordinal.{0}} (hκ : SC κ) (ha : a ≠ 0) (hlt : κ < veblen a y) :
    κ * veblen a y = veblen a y := by
  have hE : ω ^ veblen a y = veblen a y := gg_veblen_eps ha
  have h1 : κ < ω ^ veblen a y := by rw [hE]; exact hlt
  calc κ * veblen a y = ω ^ κ * ω ^ veblen a y := by rw [gg_SC_eps hκ, hE]
    _ = ω ^ (κ + veblen a y) := (opow_add _ _ _).symm
    _ = ω ^ veblen a y := by rw [Ordinal.add_of_omega0_opow_le h1 hE.le]
    _ = veblen a y := hE

theorem taKy_lt {κ a y : Ordinal.{0}} (hy : 1 ≤ y) : κ < veblen a (κ + y) :=
  (lt_add_of_pos_right κ (zero_lt_one.trans_le hy)).trans_le (right_le_veblen a _)

/-- **`W^{φ(a, Ω₂ + y)} = φ(a, Ω₂ + y)`** for `a ≠ 0`, `y ≥ 1`. -/
theorem taWe_veb {a y : Ordinal.{0}} (ha : a ≠ 0) (hy : 1 ≤ y) :
    leWe (veblen a (Om (1 + 1) + y)) = veblen a (Om (1 + 1) + y) := by
  unfold leWe; rw [taK_mul_veb ldOm2_SC ha (taKy_lt hy), gg_veblen_eps ha]

/-- **`Ω^{φ(a, Ω₁ + v)} = φ(a, Ω₁ + v)`** for `a ≠ 0`, `v ≥ 1`. -/
theorem taOe_veb {a v : Ordinal.{0}} (ha : a ≠ 0) (hv : 1 ≤ v) :
    leOe (veblen a (Om 1 + v)) = veblen a (Om 1 + v) := by
  unfold leOe; rw [taK_mul_veb Ph.ph_SC_Om1 ha (taKy_lt hv), gg_veblen_eps ha]

theorem taVeb_lim {a y : Ordinal.{0}} (ha : a ≠ 0) : IsSuccLimit (veblen a y) := by
  rw [← gg_veblen_eps (y := y) ha]
  exact isSuccLimit_opow_left isSuccLimit_omega0 (veblen_pos).ne'

/-! ## The index of an ordinal -/

/-- **The index of `c` for `φ(a, ·)`**: `φ(a, u) ≤ c < φ(a, u+1)` whenever `φ(a, 0) ≤ c`. -/
theorem taIdx_ex {a c : Ordinal.{0}} (h0 : veblen a 0 ≤ c) :
    ∃ u, veblen a u ≤ c ∧ c < veblen a (u + 1) := by
  set s : Set Ordinal.{0} := {u | c < veblen a u} with hs
  have hne : s.Nonempty := ⟨c + 1, (lt_add_one c).trans_le (right_le_veblen a _)⟩
  set w := sInf s with hw
  have hwm : c < veblen a w := csInf_mem hne
  have hmin : ∀ u < w, veblen a u ≤ c := fun u hu => by
    have h := notMem_of_lt_csInf' (s := s) hu
    exact not_lt.1 h
  rcases zero_or_succ_or_isSuccLimit w with h | ⟨u, hu⟩ | hl
  · rw [h] at hwm; exact absurd h0 (not_le.2 hwm)
  · refine ⟨u, hmin u ?_, ?_⟩
    · rw [← hu]; exact Order.lt_succ u
    · rw [← Order.succ_eq_add_one, hu]; exact hwm
  · obtain ⟨u, hu, hcu⟩ := ((isNormal_veblen a).lt_iff_exists_lt hl).1 hwm
    exact absurd (hmin u hu) (not_le.2 hcu)

/-- The index is unique. -/
theorem taIdx_uniq {a c u v : Ordinal.{0}} (hu1 : veblen a u ≤ c) (hu2 : c < veblen a (u + 1))
    (hv1 : veblen a v ≤ c) (hv2 : c < veblen a (v + 1)) : u = v := by
  have h1 : u < v + 1 := (veblen_lt_veblen_iff_right).1 (hu1.trans_lt hv2)
  have h2 : v < u + 1 := (veblen_lt_veblen_iff_right).1 (hv1.trans_lt hu2)
  exact le_antisymm (Order.lt_add_one_iff.1 h1) (Order.lt_add_one_iff.1 h2)

/-! ## Towers -/

/-- `φ(a'+1, z+1) = nfp φ(a', ·) (φ(a'+1, z) + 1)`. -/
theorem taVeb_succ (a' z : Ordinal.{0}) :
    veblen (a' + 1) (z + 1) = nfp (veblen a') (veblen (a' + 1) z + 1) := by
  rw [veblen_add_one, deriv_add_one]

/-- **A dominating tower is cofinal in a normal fixed point.** -/
theorem taTw_cof {f g : Ordinal.{0} → Ordinal.{0}} (hfm : Monotone f) (hfg : ∀ x, f x ≤ g x)
    {b x : Ordinal.{0}} (h : x < nfp f b) (u : ℕ → Ordinal.{0}) (hu0 : b ≤ u 0)
    (hus : ∀ j, u (j + 1) = g (u j)) : ∃ j, x < u j := by
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 h
  have key : ∀ n : ℕ, f^[n] b ≤ u n := by
    intro n
    induction n with
    | zero => exact hu0
    | succ n ih => rw [Function.iterate_succ_apply', hus]; exact (hfm ih).trans (hfg _)
  exact ⟨n, hn.trans_le (key n)⟩

/-- At a limit level: every `x < φ(a, z+1)` lies below `φ(a', φ(a, z) + 1)` for some `a' < a`. -/
theorem taVeb_lim_cof {a z x : Ordinal.{0}} (ha : IsSuccLimit a) (hx : x < veblen a (z + 1)) :
    ∃ a', a' < a ∧ x < veblen a' (veblen a z + 1) := by
  have ha0 : a ≠ 0 := ha.ne_bot
  have e : veblen a (z + 1) = nfpFamily (fun b : Iio a => veblen b.1) (veblen a z + 1) := by
    have h := veblen_of_ne_zero ha0
    rw [h, derivFamily_add_one]
  rw [e] at hx
  obtain ⟨l, hl⟩ := lt_nfpFamily_iff.1 hx
  generalize veblen a z + 1 = t0 at hl ⊢
  have key : ∀ l : List (Iio a), ∃ b, b < a ∧ List.foldr (fun b : Iio a => veblen b.1) t0 l ≤ veblen b t0 := by
    intro l
    induction l with
    | nil => exact ⟨0, pos_iff_ne_zero.2 ha0, right_le_veblen 0 t0⟩
    | cons c l ih =>
      obtain ⟨b, hb, hle⟩ := ih
      set m := max c.1 b with hm
      have hma : m < a := max_lt c.2 hb
      refine ⟨m + 1, ha.add_one_lt hma, ?_⟩
      show veblen c.1 (List.foldr (fun b : Iio a => veblen b.1) t0 l) ≤ veblen (m + 1) t0
      calc veblen c.1 (List.foldr (fun b : Iio a => veblen b.1) t0 l) ≤ veblen c.1 (veblen (m + 1) t0) :=
            (veblen_le_veblen_iff_right).2 (hle.trans (veblen_left_monotone t0
              ((le_max_right c.1 b).trans le_self_add)))
        _ = veblen (m + 1) t0 :=
            veblen_veblen_of_lt (Order.lt_add_one_iff.2 (le_max_left _ _)) t0
  obtain ⟨b, hb, hle⟩ := key l
  exact ⟨b, hb, hl.trans_le hle⟩

/-- The members `φ(a', κ + (φ(a, z) + 1))` stay below `φ(a, z+1)` (for `a' < a`, `κ < φ(a, z+1)`). -/
theorem taVeb_lim_lt {κ a a' z : Ordinal.{0}} (ha0 : a ≠ 0) (ha' : a' < a) (hκ : κ < veblen a (z + 1)) :
    veblen a' (κ + (veblen a z + 1)) < veblen a (z + 1) := by
  have hL : IsSuccLimit (veblen a (z + 1)) := taVeb_lim ha0
  have ht : veblen a z + 1 < veblen a (z + 1) :=
    hL.add_one_lt ((veblen_lt_veblen_iff_right).2 (lt_add_one z))
  have hs : κ + (veblen a z + 1) < veblen a (z + 1) := Ph.ph_veblen_prin a (z + 1) hκ ht
  calc veblen a' (κ + (veblen a z + 1)) < veblen a' (veblen a (z + 1)) := (veblen_lt_veblen_iff_right).2 hs
    _ = veblen a (z + 1) := veblen_veblen_of_lt ha' _

/-! ## The fine decomposition and the index of a code -/

section Code

variable {κ Q : Ordinal.{0}} (hQ : SC Q) (hκ : SC κ)

include hQ hκ

/-- **THE FINE DECOMPOSITION**: a code `w < φ(a, X)` (`X` a limit, `a < κ`) is below `φ(a, u)` for a code `u < X`. -/
theorem taCl_dec {a X : Ordinal.{0}} (haκ : a < κ) (hX : IsSuccLimit X) :
    ∀ w, LeCl κ Q w → w < veblen a X → ∃ u, LeCl κ Q u ∧ u < X ∧ w < veblen a u := by
  intro w hw
  induction hw with
  | @small w hwQ =>
    intro hlt
    by_cases hwX : w < X
    · exact ⟨w + 1, LeCl.small (hQ.add_one_lt hwQ), hX.add_one_lt hwX,
        (lt_add_one w).trans_le (right_le_veblen a _)⟩
    · push Not at hwX
      obtain ⟨u, hu, hwu⟩ := ((isNormal_veblen a).lt_iff_exists_lt hX).1 hlt
      exact ⟨u, LeCl.small ((hu.trans_le hwX).trans hwQ), hu, hwu⟩
  | om =>
    intro hlt
    by_cases hX1 : κ + 1 < X
    · exact ⟨κ + 1, LeCl.add LeCl.om (LeCl.small (gg_one_lt_of_SC hQ)), hX1,
        (lt_add_one κ).trans_le (right_le_veblen a _)⟩
    · exfalso
      push Not at hX1
      have hXκ : X ≤ κ := by
        by_contra h
        push Not at h
        exact absurd (hX.add_one_lt h) (not_lt.2 hX1)
      have := (veblen_le_veblen_iff_right (o := a)).2 hXκ
      rw [hκ.veblen_right haκ] at this
      exact absurd hlt (not_lt.2 this)
  | @add x y _ _ ihx ihy =>
    intro hlt
    obtain ⟨u1, h1, hu1, hx1⟩ := ihx (le_self_add.trans_lt hlt)
    obtain ⟨u2, h2, hu2, hy2⟩ := ihy (le_add_self.trans_lt hlt)
    refine ⟨max u1 u2, ?_, max_lt hu1 hu2, Ph.ph_veblen_prin a _ (hx1.trans_le ?_) (hy2.trans_le ?_)⟩
    · rcases le_total u1 u2 with h | h
      · rw [max_eq_right h]; exact h2
      · rw [max_eq_left h]; exact h1
    · exact (veblen_le_veblen_iff_right).2 (le_max_left _ _)
    · exact (veblen_le_veblen_iff_right).2 (le_max_right _ _)
  | @phi p q hp hq _ ihq =>
    intro hlt
    rcases lt_trichotomy p a with hpa | rfl | hpa
    · obtain ⟨u, hu, huX, hqu⟩ := ihq ((right_le_veblen p q).trans_lt hlt)
      refine ⟨u, hu, huX, ?_⟩
      calc veblen p q < veblen p (veblen a u) := (veblen_lt_veblen_iff_right).2 hqu
        _ = veblen a u := veblen_veblen_of_lt hpa u
    · have hqX : q < X := (veblen_lt_veblen_iff_right).1 hlt
      exact ⟨q + 1, LeCl.add hq (LeCl.small (gg_one_lt_of_SC hQ)), hX.add_one_lt hqX,
        (veblen_lt_veblen_iff_right).2 (lt_add_one q)⟩
    · have hfix : veblen a (veblen p q) = veblen p q := veblen_veblen_of_lt hpa q
      have hwX : veblen p q < X := by
        rw [← hfix] at hlt; exact (veblen_lt_veblen_iff_right).1 hlt
      refine ⟨veblen p q + 1, LeCl.add (LeCl.phi hp hq) (LeCl.small (gg_one_lt_of_SC hQ)), hX.add_one_lt hwX, ?_⟩
      calc veblen p q = veblen a (veblen p q) := hfix.symm
        _ < veblen a (veblen p q + 1) := (veblen_lt_veblen_iff_right).2 (lt_add_one _)

omit hQ in
/-- **The index of a code is a code** (`a < κ`). -/
theorem taCl_idx {a : Ordinal.{0}} (haκ : a < κ) :
    ∀ w, LeCl κ Q w → veblen a 0 ≤ w → ∃ u, LeCl κ Q u ∧ veblen a u ≤ w ∧ w < veblen a (u + 1) := by
  intro w hw
  induction hw with
  | @small w hwQ =>
    intro h0
    obtain ⟨u, h1, h2⟩ := taIdx_ex h0
    exact ⟨u, LeCl.small (((right_le_veblen a u).trans h1).trans_lt hwQ), h1, h2⟩
  | om =>
    intro _
    refine ⟨κ, LeCl.om, (hκ.veblen_right haκ).le, ?_⟩
    calc κ = veblen a κ := (hκ.veblen_right haκ).symm
      _ < veblen a (κ + 1) := (veblen_lt_veblen_iff_right).2 (lt_add_one κ)
  | @add x y hx hy ihx ihy =>
    intro h0
    have hP := Ph.ph_veblen_prin a 0
    by_cases hxa : veblen a 0 ≤ x
    · obtain ⟨u1, hc1, hu1, hx1⟩ := ihx hxa
      by_cases hya : veblen a 0 ≤ y
      · obtain ⟨u2, hc2, hu2, hy2⟩ := ihy hya
        refine ⟨max u1 u2, ?_, ?_, Ph.ph_veblen_prin a _ (hx1.trans_le ?_) (hy2.trans_le ?_)⟩
        · rcases le_total u1 u2 with h | h
          · rw [max_eq_right h]; exact hc2
          · rw [max_eq_left h]; exact hc1
        · rcases le_total u1 u2 with h | h
          · rw [max_eq_right h]; exact hu2.trans le_add_self
          · rw [max_eq_left h]; exact hu1.trans le_self_add
        · exact (veblen_le_veblen_iff_right).2 (add_le_add (le_max_left _ _) le_rfl)
        · exact (veblen_le_veblen_iff_right).2 (add_le_add (le_max_right _ _) le_rfl)
      · push Not at hya
        refine ⟨u1, hc1, hu1.trans le_self_add, Ph.ph_veblen_prin a _ hx1 (hya.trans_le ?_)⟩
        exact (veblen_le_veblen_iff_right).2 zero_le
    · push Not at hxa
      by_cases hya : veblen a 0 ≤ y
      · obtain ⟨u2, hc2, hu2, hy2⟩ := ihy hya
        refine ⟨u2, hc2, hu2.trans le_add_self, Ph.ph_veblen_prin a _ (hxa.trans_le ?_) hy2⟩
        exact (veblen_le_veblen_iff_right).2 zero_le
      · push Not at hya
        exact absurd h0 (not_le.2 (hP hxa hya))
  | @phi p q hp hq _ ihq =>
    intro h0
    rcases lt_trichotomy p a with hpa | rfl | hpa
    · have hq0 : veblen a 0 ≤ q := by
        by_contra hq
        push Not at hq
        have : veblen p q < veblen a 0 := by
          calc veblen p q < veblen p (veblen a 0) := (veblen_lt_veblen_iff_right).2 hq
            _ = veblen a 0 := veblen_veblen_of_lt hpa 0
        exact absurd h0 (not_le.2 this)
      obtain ⟨u, hu, h1, h2⟩ := ihq hq0
      refine ⟨u, hu, h1.trans (right_le_veblen p q), ?_⟩
      calc veblen p q < veblen p (veblen a (u + 1)) := (veblen_lt_veblen_iff_right).2 h2
        _ = veblen a (u + 1) := veblen_veblen_of_lt hpa _
    · exact ⟨q, hq, le_rfl, (veblen_lt_veblen_iff_right).2 (lt_add_one q)⟩
    · have hfix : veblen a (veblen p q) = veblen p q := veblen_veblen_of_lt hpa q
      refine ⟨veblen p q, LeCl.phi hp hq, hfix.le, ?_⟩
      calc veblen p q = veblen a (veblen p q) := hfix.symm
        _ < veblen a (veblen p q + 1) := (veblen_lt_veblen_iff_right).2 (lt_add_one _)

/-- **`φ(a, y)` a code gives `y` a code** (`a < κ`; no condition `y < φ(a, y)`). -/
theorem taCl_inv {a y : Ordinal.{0}} (haκ : a < κ) (h : LeCl κ Q (veblen a y)) : LeCl κ Q y := by
  obtain ⟨u, hu, h1, h2⟩ := taCl_idx hκ haκ _ h ((veblen_le_veblen_iff_right).2 zero_le)
  have : u = y := taIdx_uniq h1 h2 le_rfl ((veblen_lt_veblen_iff_right).2 (lt_add_one y))
  rwa [this] at hu

end Code

/-! ## The index of a member of a closure -/

/-- The index of a strongly critical `z` above `a` is `z` itself. -/
theorem taIdx_SC {a z : Ordinal.{0}} (hz : SC z) (ha : a < z) :
    veblen a z ≤ z ∧ z < veblen a (z + 1) := by
  refine ⟨(hz.veblen_right ha).le, ?_⟩
  calc z = veblen a z := (hz.veblen_right ha).symm
    _ < veblen a (z + 1) := (veblen_lt_veblen_iff_right).2 (lt_add_one z)

/-- **The index of a member of a closure is a member** (`a < Γ₀`). -/
theorem taHull_idx {A B a c : Ordinal.{0}} (ha : a < gamma 0) (hc : c ∈ S.CSet A B) (h0 : veblen a 0 ≤ c) :
    ∃ u ∈ S.CSet A B, veblen a u ≤ c ∧ c < veblen a (u + 1) := by
  have hSC : ∀ z, SC z → z ∈ S.CSet A B → ∃ u ∈ S.CSet A B, veblen a u ≤ z ∧ z < veblen a (u + 1) :=
    fun z hz hzm => ⟨z, hzm, taIdx_SC hz (ha.trans_le (taGam_le_SC hz))⟩
  revert h0
  induction hc with
  | @small x hx =>
    intro h0
    obtain ⟨u, h1, h2⟩ := taIdx_ex h0
    exact ⟨u, CSet.of_lt (((right_le_veblen a u).trans h1).trans_lt hx), h1, h2⟩
  | zero => intro h0; exact absurd h0 (not_le.2 veblen_pos)
  | inacc n => intro _; exact hSC _ (SC_I n) (Clos.inacc n)
  | inaccW => intro _; exact hSC _ SC_Iw Clos.inaccW
  | @add x y hx hy ihx ihy =>
    intro h0
    have hP := Ph.ph_veblen_prin a 0
    by_cases hxa : veblen a 0 ≤ x
    · obtain ⟨u1, hc1, hu1, hx1⟩ := ihx hxa
      by_cases hya : veblen a 0 ≤ y
      · obtain ⟨u2, hc2, hu2, hy2⟩ := ihy hya
        refine ⟨max u1 u2, ?_, ?_, Ph.ph_veblen_prin a _ (hx1.trans_le ?_) (hy2.trans_le ?_)⟩
        · rcases le_total u1 u2 with h | h
          · rw [max_eq_right h]; exact hc2
          · rw [max_eq_left h]; exact hc1
        · rcases le_total u1 u2 with h | h
          · rw [max_eq_right h]; exact hu2.trans le_add_self
          · rw [max_eq_left h]; exact hu1.trans le_self_add
        · exact (veblen_le_veblen_iff_right).2 (add_le_add (le_max_left _ _) le_rfl)
        · exact (veblen_le_veblen_iff_right).2 (add_le_add (le_max_right _ _) le_rfl)
      · push Not at hya
        refine ⟨u1, hc1, hu1.trans le_self_add, Ph.ph_veblen_prin a _ hx1 (hya.trans_le ?_)⟩
        exact (veblen_le_veblen_iff_right).2 zero_le
    · push Not at hxa
      by_cases hya : veblen a 0 ≤ y
      · obtain ⟨u2, hc2, hu2, hy2⟩ := ihy hya
        refine ⟨u2, hc2, hu2.trans le_add_self, Ph.ph_veblen_prin a _ (hxa.trans_le ?_) hy2⟩
        exact (veblen_le_veblen_iff_right).2 zero_le
      · push Not at hya
        exact absurd h0 (not_le.2 (hP hxa hya))
  | @phi p q hp hq _ ihq =>
    intro h0
    rcases lt_trichotomy p a with hpa | rfl | hpa
    · have hq0 : veblen a 0 ≤ q := by
        by_contra hq
        push Not at hq
        have : veblen p q < veblen a 0 := by
          calc veblen p q < veblen p (veblen a 0) := (veblen_lt_veblen_iff_right).2 hq
            _ = veblen a 0 := veblen_veblen_of_lt hpa 0
        exact absurd h0 (not_le.2 this)
      obtain ⟨u, hu, h1, h2⟩ := ihq hq0
      refine ⟨u, hu, h1.trans (right_le_veblen p q), ?_⟩
      calc veblen p q < veblen p (veblen a (u + 1)) := (veblen_lt_veblen_iff_right).2 h2
        _ = veblen a (u + 1) := veblen_veblen_of_lt hpa _
    · exact ⟨q, hq, le_rfl, (veblen_lt_veblen_iff_right).2 (lt_add_one q)⟩
    · have hfix : veblen a (veblen p q) = veblen p q := veblen_veblen_of_lt hpa q
      refine ⟨veblen p q, Clos.phi hp hq, hfix.le, ?_⟩
      calc veblen p q = veblen a (veblen p q) := hfix.symm
        _ < veblen a (veblen p q + 1) := (veblen_lt_veblen_iff_right).2 (lt_add_one _)
  | @om x hx _ =>
    intro h0
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero] at h0; exact absurd h0 (not_le.2 veblen_pos)
    · exact hSC _ (SC_Om hx0) (Clos.om hx)
  | @coll π e hπ hπC heC _ _ =>
    intro _
    exact hSC _ (SC_psi hπ e.1) (Clos.coll hπ hπC heC)

/-- **`x - y` is a member of a closure for every member `x`.** -/
theorem taSub_mem {A B : Ordinal.{0}} : ∀ x, x ∈ S.CSet A B → ∀ y, x - y ∈ S.CSet A B := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx y
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Ordinal.sub_eq_zero_iff_le.2 zero_le]; exact CSet.zero_mem _ _
  obtain ⟨hlead, htail⟩ := lead_tail_mem hx hx0
  have hdec : lead x + tail x = x := lead_add_tail hx0
  rcases lt_or_ge y (lead x) with hy | hy
  · have e : y + x = x := Ordinal.add_of_omega0_opow_le hy (lead_le hx0)
    rw [Ordinal.sub_eq_of_add_eq e]; exact hx
  · obtain ⟨y', rfl⟩ := exists_add_of_le hy
    have e : x - (lead x + y') = tail x - y' := by
      have h := Ordinal.add_sub_add_cancel (lead x) (tail x) y'
      rwa [hdec] at h
    rw [e]
    exact IH _ (tail_lt hx0) htail y'

end Googology.Trans.PoR.InaccPsi.R2.Ta
