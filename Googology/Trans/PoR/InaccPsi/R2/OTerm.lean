import Googology.Trans.PoR.InaccPsi.R2.RSG

/-!
# Offset terms in one variable: Lemma EXACT, the uniform comparison, and the representation

The project's offset terms (its paper's 2.1), in the form used here: constants, `ω^{x+t}` and sums
(`OT`).  For an `ε`-number `x` above the constants, `ω^{x+t}` is `x·ω^t`, so every Cantor normal form
relative to `x` is such a term; `rep` proves that every ordinal below the next `ε`-number after `r`
is the value at `r` of a term with constants below `r`.

* `OT`, `OT.ev` (the value), `OT.CB` (all constants below a bound), `OT.cs` (the list of constants),
  `OT.nmul` (`n`-fold sum);
* `eN x`: the least `ε`-number above `x` (`eN_E`, `lt_eN`, `eN_le`);
* `ev_lt` (a term with constants below an `ε`-number `u` has value below `u` at every `x < u`),
  `ev_lt_Om1`, `ev_lt_eN`;
* `vt_opow'` (`ϑʳ(β) = ω^{r+β}` for `1 ≤ β` as long as no `ε`-number lies in `(r, r+β]`; [W07a]
  Lemma 4.2 with `wbar_eq`);
* `pi_ev` (**Lemma EXACT for every term**: `π_{s,r}(t(r)) = t(s)` and `t(r) ∈ Tʳ[s]` for constants
  below `s`; [W07a] Lemma 4.2, Def 3.22/3.28, Def 5.1, Lemma 5.3);
* `uni_le`, `uni_lt`, `uni_eq` (**the uniform comparison**: two terms compare at `r` as at `s`;
  from Lemma EXACT and [W07a] Lemma 5.3 (b), (d), `π` strictly increasing);
* `rep` (**the representation**).

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-- Offset terms in one variable `x`: a constant, `ω^{x+t}`, or a sum. -/
inductive OT : Type 1
  | k : Ordinal.{0} → OT
  | xw : OT → OT
  | add : OT → OT → OT

namespace OT

/-- The value of a term at `x`. -/
noncomputable def ev : OT → Ordinal.{0} → Ordinal.{0}
  | k a, _ => a
  | xw t, x => ω ^ (x + ev t x)
  | add t u, x => ev t x + ev u x

/-- All constants of `t` are below `s`. -/
def CB : OT → Ordinal.{0} → Prop
  | k a, s => a < s
  | xw t, s => CB t s
  | add t u, s => CB t s ∧ CB u s

/-- The constants of `t`. -/
def cs : OT → List Ordinal.{0}
  | k a => [a]
  | xw t => cs t
  | add t u => cs t ++ cs u

/-- The `n`-fold sum `t + ⋯ + t` (`0` for `n = 0`). -/
def nmul (t : OT) : ℕ → OT
  | 0 => k 0
  | n + 1 => add (nmul t n) t

@[simp] theorem ev_k (a x : Ordinal.{0}) : ev (k a) x = a := rfl
@[simp] theorem ev_xw (t : OT) (x : Ordinal.{0}) : ev (xw t) x = ω ^ (x + ev t x) := rfl
@[simp] theorem ev_add (t u : OT) (x : Ordinal.{0}) : ev (add t u) x = ev t x + ev u x := rfl

theorem cb_iff : ∀ (t : OT) (s : Ordinal.{0}), CB t s ↔ ∀ c ∈ cs t, c < s
  | k a, s => by simp [CB, cs]
  | xw t, s => cb_iff t s
  | add t u, s => by
      simp only [CB, cs, List.mem_append]
      rw [cb_iff t s, cb_iff u s]
      constructor
      · rintro ⟨h1, h2⟩ c (hc | hc)
        · exact h1 c hc
        · exact h2 c hc
      · intro h; exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩

theorem CB_mono {t : OT} {s s' : Ordinal.{0}} (h : CB t s) (hs : s ≤ s') : CB t s' :=
  (cb_iff t s').2 (fun c hc => lt_of_lt_of_le ((cb_iff t s).1 h c hc) hs)

theorem ev_nmul (t : OT) (x : Ordinal.{0}) : ∀ n : ℕ, ev (nmul t n) x = ev t x * (n : Ordinal.{0})
  | 0 => by simp [nmul]
  | n + 1 => by
      simp only [nmul, ev_add]
      rw [ev_nmul t x n, Nat.cast_succ, mul_add_one]

theorem CB_nmul {t : OT} {s : Ordinal.{0}} (hs : 0 < s) (h : CB t s) : ∀ n : ℕ, CB (nmul t n) s
  | 0 => hs
  | n + 1 => ⟨CB_nmul hs h n, h⟩

end OT

open OT

/-! ## The next `ε`-number -/

/-- The least `ε`-number above `x`. -/
noncomputable def eN (x : Ordinal.{0}) : Ordinal.{0} := nfp (fun a => ω ^ a) (x + 1)

theorem eN_E (x : Ordinal.{0}) : InE (eN x) := nfp_fp (isNormal_opow one_lt_omega0) _

theorem lt_eN (x : Ordinal.{0}) : x < eN x :=
  lt_of_lt_of_le (lt_add_one x) (le_nfp _ _)

theorem eN_le {x u : Ordinal.{0}} (hxu : x < u) (hu : InE u) : eN x ≤ u :=
  nfp_le_fp (isNormal_opow one_lt_omega0).monotone (add_one_le_of_lt hxu) (le_of_eq hu)

/-! ## Values of terms -/

/-- A term with constants below an `ε`-number `u` has value below `u` at every `x < u`. -/
theorem ev_lt {u x : Ordinal.{0}} (hu : InE u) (hx : x < u) : ∀ t : OT, CB t u → ev t x < u := by
  intro t
  induction t with
  | k a => intro h; exact h
  | xw t ih =>
    intro h
    have h1 : x + ev t x < u := (inE_indec hu).add_lt hx (ih h)
    have h2 := (opow_lt_opow_iff_right one_lt_omega0).2 h1
    have hu' : ω ^ u = u := hu
    rw [hu'] at h2; exact h2
  | add t s iht ihs => intro h; exact (inE_indec hu).add_lt (iht h.1) (ihs h.2)

theorem ev_lt_Om1 {x : Ordinal.{0}} (hx : x < Om1) : ∀ t : OT, CB t Om1 → ev t x < Om1 := by
  intro t
  induction t with
  | k a => intro h; exact h
  | xw t ih => intro h; exact Om1_opow_lt (Om1_add_lt hx (ih h))
  | add t s iht ihs => intro h; exact Om1_add_lt (iht h.1) (ihs h.2)

theorem ev_lt_eN {x : Ordinal.{0}} {t : OT} (h : CB t x) : ev t x < eN x :=
  ev_lt (eN_E x) (lt_eN x) t (CB_mono h (lt_eN x).le)

/-! ## Lemma EXACT -/

/-- `ϑʳ(β) = ω^{r+β}` for `1 ≤ β < Ω₁` when no `ε`-number lies in `(r, r+β]` ([W07a] Lemma 4.2,
`wbar_eq`). -/
theorem vt_opow' {r β : Ordinal.{0}} (hr : InE r) (hr1 : r < Om1) (hβ1 : 1 ≤ β) (hβ : β < Om1)
    (hno : ∀ u, r < u → u ≤ r + β → ¬ InE u) : vt r β = ω ^ (r + β) := by
  have he : 1 + (β - 1) = β := Ordinal.add_sub_cancel_of_le hβ1
  have hα1 : β - 1 < Om1 := lt_of_le_of_lt (sub_le_self β 1) hβ
  rw [← he, vt_wbar hr hr1 hα1, wbar_eq hr, add_assoc]
  intro u h1 h2
  rw [add_assoc, he] at h2
  exact hno u h1 h2

/-- **Lemma EXACT** for every offset term: for `ε`-numbers `s < r < Ω₁` and a term `t` with constants
below `s`, `t(r) ∈ Tʳ[s]` and `π_{s,r}(t(r)) = t(s)`. -/
theorem pi_ev {s r : Ordinal.{0}} (hB : Bases s r) :
    ∀ t : OT, CB t s → ev t r ∈ TB r s ∧ pi s r (ev t r) = ev t s := by
  have hsE := hB.1
  have hrE := hB.2.1
  have hsr := hB.2.2.1
  have hr1 := hB.2.2.2
  have hs1 : s < Om1 := hsr.trans hr1
  have hr' : ω ^ r = r := hrE
  have hs' : ω ^ s = s := hsE
  have h0T : (0 : Ordinal.{0}) ∈ TB r s := mem_TB_of_lt hB hsE.pos
  have h0pi : pi s r 0 = 0 := pi_lt hB hsE.pos
  intro t
  induction t with
  | k a => intro h; exact ⟨mem_TB_of_lt hB h, pi_lt hB h⟩
  | add t u iht ihu =>
    intro h
    obtain ⟨h1, h2⟩ := iht h.1
    obtain ⟨h3, h4⟩ := ihu h.2
    obtain ⟨h5, h6⟩ := pi_add hB h1 h3
    refine ⟨h5, ?_⟩
    simp only [ev_add]; rw [h6, h2, h4]
  | xw t ih =>
    intro h
    obtain ⟨hβT, hβpi⟩ := ih h
    simp only [ev_xw]
    rcases eq_or_ne (ev t r) 0 with hβ0 | hβ0
    · have h0 : ev t s = 0 := by rw [← hβpi, hβ0, h0pi]
      rw [hβ0, h0, add_zero, add_zero, hr', hs']
      exact pi_base hB
    · have hβ1 : 1 ≤ ev t r := one_le_iff_ne_zero.2 hβ0
      have hβOm : ev t r < Om1 := ev_lt_Om1 hr1 t (CB_mono h hs1.le)
      have hno : ∀ u, r < u → u ≤ r + ev t r → ¬ InE u := by
        intro u hru hu hE
        have : ev t r < u := ev_lt hE hru t (CB_mono h (hsr.trans hru).le)
        exact absurd hu (not_le.2 ((inE_indec hE).add_lt hru this))
      have hv := vt_opow' hrE hr1 hβ1 hβOm hno
      obtain ⟨hvT, hvP⟩ := vt_mem hrE hr1 hβT.1 hβOm
      refine ⟨by rw [← hv]; exact ⟨hvT, by rw [hvP]; exact hβT.2⟩, ?_⟩
      rw [← hv, pi_vt hB hβT hβOm, hβpi]
      have hβ'0 : ev t s ≠ 0 := by
        intro h0
        have : pi s r 0 < pi s r (ev t r) :=
          (pi_bijOn hB).2 h0T hβT (pos_iff_ne_zero.2 hβ0)
        rw [h0pi, hβpi, h0] at this
        exact lt_irrefl _ this
      refine vt_opow' hsE hs1 (one_le_iff_ne_zero.2 hβ'0) (ev_lt_Om1 hs1 t (CB_mono h hs1.le)) ?_
      intro u hsu hu hE
      have : ev t s < u := ev_lt hE hsu t (CB_mono h hsu.le)
      exact absurd hu (not_le.2 ((inE_indec hE).add_lt hsu this))

/-! ## The uniform comparison -/

/-- **Uniform comparison** (`≤`): for terms with constants below `s` (`s < r` `ε`-numbers),
`t(r) ≤ u(r) ↔ t(s) ≤ u(s)`. -/
theorem uni_le {s r : Ordinal.{0}} (hB : Bases s r) {t u : OT} (ht : CB t s) (hu : CB u s) :
    ev t r ≤ ev u r ↔ ev t s ≤ ev u s := by
  obtain ⟨h1, h2⟩ := pi_ev hB t ht
  obtain ⟨h3, h4⟩ := pi_ev hB u hu
  rw [← h2, ← h4]
  exact ((pi_bijOn hB).2.le_iff_le h1 h3).symm

theorem uni_lt {s r : Ordinal.{0}} (hB : Bases s r) {t u : OT} (ht : CB t s) (hu : CB u s) :
    ev t r < ev u r ↔ ev t s < ev u s := by
  rw [← not_le, ← not_le, uni_le hB hu ht]

theorem uni_eq {s r : Ordinal.{0}} (hB : Bases s r) {t u : OT} (ht : CB t s) (hu : CB u s) :
    ev t r = ev u r ↔ ev t s = ev u s := by
  rw [le_antisymm_iff, le_antisymm_iff, uni_le hB ht hu, uni_le hB hu ht]

/-! ## The representation -/

/-- **Representation**: every ordinal below the next `ε`-number after an `ε`-number `r` is the value
at `r` of a term with constants below `r` (Cantor normal form, `ω^{r+β} = r·ω^β`). -/
theorem rep {r : Ordinal.{0}} (hr : InE r) : ∀ z, z < eN r → ∃ t : OT, CB t r ∧ ev t r = z := by
  have hr' : ω ^ r = r := hr
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hz
  rcases lt_or_ge z r with hzr | hrz
  · exact ⟨k z, hzr, rfl⟩
  have hz0 : z ≠ 0 := (lt_of_lt_of_le hr.pos hrz).ne'
  set L := log ω z with hL
  have hrL : r ≤ L := le_log_of_opow_le one_lt_omega0 (by rw [hr']; exact hrz)
  have hωL : ω ^ L ≤ z := opow_log_le_self ω hz0
  have hβz : L - r < z := by
    rcases eq_or_ne L r with hLr | hLr
    · rw [hLr, Ordinal.sub_self]; exact lt_of_lt_of_le hr.pos hrz
    · have hrL' : r < L := lt_of_le_of_ne hrL (Ne.symm hLr)
      have hnE : ¬ InE L := fun hE => by
        have h1 : eN r ≤ L := eN_le hrL' hE
        exact absurd (lt_of_lt_of_le hz h1)
          (not_lt.2 ((right_le_opow L one_lt_omega0).trans hωL))
      have hLω : L < ω ^ L := lt_of_le_of_ne (right_le_opow L one_lt_omega0) (fun h => hnE h.symm)
      exact lt_of_le_of_lt (sub_le_self L r) (lt_of_lt_of_le hLω hωL)
  have hω0 : ω ^ L ≠ 0 := (opow_pos L omega0_pos).ne'
  have hm : z % ω ^ L < z := lt_of_lt_of_le (mod_lt z hω0) hωL
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt z one_lt_omega0)
  obtain ⟨tβ, hβC, hβv⟩ := IH (L - r) hβz (hβz.trans hz)
  obtain ⟨tm, hmC, hmv⟩ := IH (z % ω ^ L) hm (hm.trans hz)
  refine ⟨add (nmul (xw tβ) n) tm, ⟨CB_nmul (t := xw tβ) hr.pos hβC n, hmC⟩, ?_⟩
  simp only [ev_add, ev_nmul, ev_xw]
  rw [hβv, hmv, Ordinal.add_sub_cancel_of_le hrL, ← hn]
  exact div_add_mod z (ω ^ L)

end Googology.Trans.PoR.InaccPsi.R2
