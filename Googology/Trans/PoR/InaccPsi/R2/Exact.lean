import Googology.Trans.PoR.InaccPsi.R2.CitedW
import Googology.Trans.PoR.InaccPsi.R2.FragX

/-!
# Lemma EXACT for the offset terms `x·γ + e`

The project's Lemma EXACT ("a base change moves an offset term exactly, `π(t(r)) = t(s)`"), for the
terms `t(x) = x·γ + e` with constants `γ, e < s`, from [W07a] Lemma 4.2 (`vt_wbar`), Def 3.22/3.28
(`vt_mem`), Def 5.1 (`pi_vt`) and Lemma 5.3 (`pi_add`):

* `inE_opow_iff`, `nonEAP_unbounded`, `wbar_le`, `wbar_eq` (`ω̄_{r+α} = ω^{r+1+α}` for an `ε`-number `r`
  as long as no `ε`-number lies in `(r, r+1+α]`);
* `vt_opow` (`ϑʳ(g) = ω^{r+g}` for `1 ≤ g ≤ r`), `pi_opow` (`π_{s,r}(ω^{r+g}) = ω^{s+g}`);
* `pi_mul` (`π_{s,r}(r·γ) = s·γ`), `pi_term` (`π_{s,r}(r·γ + e) = s·γ + e`), each with membership in
  `Tʳ[s]`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

theorem inE_opow_iff (b : Ordinal.{0}) : InE (ω ^ b) ↔ InE b := by
  unfold InE
  constructor
  · intro h
    exact le_antisymm ((opow_le_opow_iff_right one_lt_omega0).1 h.le)
      (right_le_opow b one_lt_omega0)
  · intro h; rw [h, h]

theorem inE_indec {b : Ordinal.{0}} (h : InE b) : Indec b := by
  have := indec_opow b; unfold InE at h; rwa [h] at this

theorem not_inE_opow_succ (a : Ordinal.{0}) : ¬ InE (ω ^ (a + 1)) := by
  rw [inE_opow_iff]
  intro h
  have hl : IsSuccLimit (ω ^ (a + 1)) := by
    rw [opow_add, opow_one]
    exact isSuccLimit_mul_right (opow_pos a omega0_pos) isSuccLimit_omega0
  unfold InE at h
  rw [h] at hl
  exact not_isSuccLimit_add_one a hl

theorem opow_succ_mem (a : Ordinal.{0}) : ω ^ (a + 1) ∈ NonEAP :=
  ⟨indec_opow _, not_inE_opow_succ a⟩

theorem nonEAP_unbounded : ¬ BddAbove NonEAP := by
  rintro ⟨b, hb⟩
  have h := hb (opow_succ_mem b)
  exact absurd h (not_le.2 (lt_of_lt_of_le (lt_add_one b) (right_le_opow _ one_lt_omega0)))

/-- An indecomposable is a power of `ω`. -/
theorem indec_eq_opow {w : Ordinal.{0}} (hw : Indec w) : ∃ c : Ordinal.{0}, w = ω ^ c := by
  rcases isPrincipal_add_iff_zero_or_omega0_opow.1 (indec_iff.1 hw).2 with h0 | ⟨c, hc⟩
  · exact absurd h0 hw.ne_zero
  · exact ⟨c, hc.symm⟩

theorem wbar_le : ∀ γ, wbar γ ≤ ω ^ (γ + 1) := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  refine enumOrd_le_of_forall_lt (opow_succ_mem γ) (fun b hb => ?_)
  exact lt_of_le_of_lt (IH b hb) ((opow_lt_opow_iff_right one_lt_omega0).2
    (lt_of_le_of_lt (add_one_le_of_lt hb) (lt_add_one γ)))

/-- **`ω̄` above an `ε`-number**: `ω̄_{r+α} = ω^{r+1+α}` when no `ε`-number lies in `(r, r+1+α]`. -/
theorem wbar_eq {r : Ordinal.{0}} (hr : InE r) :
    ∀ α, (∀ β, r < β → β ≤ r + 1 + α → ¬ InE β) → wbar (r + α) = ω ^ (r + 1 + α) := by
  intro α
  induction α using WellFoundedLT.induction with
  | ind α IH =>
  intro hno
  have hmono := enumOrd_strictMono nonEAP_unbounded
  have hmem : ω ^ (r + 1 + α) ∈ NonEAP := by
    refine ⟨indec_opow _, fun h => ?_⟩
    rw [inE_opow_iff] at h
    exact hno _ (lt_of_lt_of_le (lt_add_one r) le_self_add) le_rfl h
  have hr' : ω ^ r = r := hr
  -- the upper bound
  have hup : wbar (r + α) ≤ ω ^ (r + 1 + α) := by
    refine enumOrd_le_of_forall_lt hmem (fun b hb => ?_)
    show wbar b < _
    by_cases hbr : b < r
    · calc wbar b ≤ ω ^ (b + 1) := wbar_le b
        _ ≤ ω ^ r := (opow_le_opow_iff_right one_lt_omega0).2 (add_one_le_of_lt hbr)
        _ < ω ^ (r + 1 + α) := (opow_lt_opow_iff_right one_lt_omega0).2
            (lt_of_lt_of_le (lt_add_one r) le_self_add)
    · have hrb : r ≤ b := not_lt.1 hbr
      have he : r + (b - r) = b := Ordinal.add_sub_cancel_of_le hrb
      have hlt : b - r < α := by rw [← he] at hb; exact (add_lt_add_iff_left r).1 hb
      have := IH (b - r) hlt (fun β h1 h2 => hno β h1 (h2.trans (add_le_add le_rfl hlt.le)))
      rw [he] at this
      rw [this]
      exact (opow_lt_opow_iff_right one_lt_omega0).2 ((add_lt_add_iff_left _).2 hlt)
  -- the lower bound
  have hw : wbar (r + α) ∈ NonEAP := enumOrd_mem nonEAP_unbounded (r + α)
  obtain ⟨c, hc⟩ := indec_eq_opow hw.1
  have hcE : ¬ InE c := by rw [← inE_opow_iff, ← hc]; exact hw.2
  have hrc : r < c := by
    have h1 : r ≤ wbar (r + α) :=
      le_self_add.trans (le_enumOrd_self (s := NonEAP) nonEAP_unbounded)
    rw [hc, ← hr'] at h1
    have h2 := (opow_le_opow_iff_right one_lt_omega0).1 h1
    rcases eq_or_lt_of_le h2 with e | h
    · exact absurd (e ▸ hr) hcE
    · exact h
  have hlow : r + 1 + α ≤ c := by
    by_contra hlt
    have hlt := not_le.1 hlt
    have h1 : r + 1 ≤ c := add_one_le_of_lt hrc
    have he : r + 1 + (c - (r + 1)) = c := Ordinal.add_sub_cancel_of_le h1
    have hα : c - (r + 1) < α := by rw [← he] at hlt; exact (add_lt_add_iff_left _).1 hlt
    have := IH _ hα (fun β h1 h2 => hno β h1 (h2.trans (add_le_add le_rfl hα.le)))
    rw [he, ← hc] at this
    exact absurd (hmono.injective this) (ne_of_lt ((add_lt_add_iff_left r).2 hα))
  refine le_antisymm hup ?_
  rw [hc]; exact (opow_le_opow_iff_right one_lt_omega0).2 hlow

/-- `ϑʳ(g) = ω^{r+g}` for an `ε`-number `r < Ω₁` and `1 ≤ g ≤ r`. -/
theorem vt_opow {r g : Ordinal.{0}} (hr : InE r) (hr1 : r < Om1) (hg1 : 1 ≤ g) (hgr : g ≤ r) :
    vt r g = ω ^ (r + g) := by
  have he : 1 + (g - 1) = g := Ordinal.add_sub_cancel_of_le hg1
  have hα1 : g - 1 < Om1 := lt_of_le_of_lt (sub_le_self g 1) (lt_of_le_of_lt hgr hr1)
  rw [← he, vt_wbar hr hr1 hα1, wbar_eq hr, add_assoc]
  intro β hrβ hβ hE
  have hI := inE_indec hE
  have : r + r < β := hI.add_lt hrβ hrβ
  rw [add_assoc, he] at hβ
  exact absurd (hβ.trans (add_le_add le_rfl hgr)) (not_le.2 this)

theorem mem_TB_of_lt {s r x : Ordinal.{0}} (hB : Bases s r) (hx : x < s) : x ∈ TB r s :=
  (TB_inter_lt hB (hx.trans hB.2.2.1)).2 hx

/-- **`π_{s,r}(ω^{r+g}) = ω^{s+g}`** for `1 ≤ g < s` ([W07a] Lemma 4.2, Def 3.22, 3.28, 5.1). -/
theorem pi_opow {s r g : Ordinal.{0}} (hB : Bases s r) (hg1 : 1 ≤ g) (hgs : g < s) :
    ω ^ (r + g) ∈ TB r s ∧ pi s r (ω ^ (r + g)) = ω ^ (s + g) := by
  obtain ⟨hsE, hrE, hsr, hr1⟩ := hB
  have hB' : Bases s r := ⟨hsE, hrE, hsr, hr1⟩
  have hgT := mem_TB_of_lt hB' hgs
  have hg1' : g < Om1 := (hgs.trans hsr).trans hr1
  have hv := vt_opow hrE hr1 hg1 (hgs.trans hsr).le
  obtain ⟨hvT, hvP⟩ := vt_mem hrE hr1 hgT.1 hg1'
  refine ⟨?_, ?_⟩
  · rw [← hv]; exact ⟨hvT, by rw [hvP]; exact hgT.2⟩
  · rw [← hv, pi_vt hB' hgT hg1', pi_lt hB' hgs, vt_opow hsE (hsr.trans hr1) hg1 hgs.le]

theorem pi_opow' {s r g : Ordinal.{0}} (hB : Bases s r) (hgs : g < s) :
    ω ^ (r + g) ∈ TB r s ∧ pi s r (ω ^ (r + g)) = ω ^ (s + g) := by
  rcases eq_or_ne g 0 with rfl | hg0
  · have hr : ω ^ r = r := hB.2.1
    have hs : ω ^ s = s := hB.1
    rw [add_zero, add_zero, hr, hs]; exact pi_base hB
  · exact pi_opow hB (one_le_iff_ne_zero.2 hg0) hgs

theorem pi_mul_nat {s r p p' : Ordinal.{0}} (hB : Bases s r) (hp : p ∈ TB r s)
    (hpp : pi s r p = p') : ∀ n : ℕ, p * (n : Ordinal.{0}) ∈ TB r s ∧
      pi s r (p * (n : Ordinal.{0})) = p' * (n : Ordinal.{0}) := by
  intro n
  induction n with
  | zero =>
    simp only [Nat.cast_zero, mul_zero]
    exact ⟨mem_TB_of_lt hB (InE.pos hB.1), pi_lt hB (InE.pos hB.1)⟩
  | succ n ih =>
    rw [Nat.cast_succ, mul_add_one, mul_add_one]
    obtain ⟨h1, h2⟩ := pi_add hB ih.1 hp
    exact ⟨h1, by rw [h2, ih.2, hpp]⟩

/-- **`π_{s,r}(r·γ) = s·γ`** for `γ < s`. -/
theorem pi_mul {s r : Ordinal.{0}} (hB : Bases s r) :
    ∀ γ, γ < s → r * γ ∈ TB r s ∧ pi s r (r * γ) = s * γ := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγ
  rcases eq_or_ne γ 0 with rfl | hγ0
  · simp only [mul_zero]
    exact ⟨mem_TB_of_lt hB (InE.pos hB.1), pi_lt hB (InE.pos hB.1)⟩
  set g := log ω γ with hg
  set q := γ / ω ^ g with hq
  set m := γ % ω ^ g with hm
  have hω0 : ω ^ g ≠ 0 := (opow_pos g omega0_pos).ne'
  have hdm : ω ^ g * q + m = γ := div_add_mod γ (ω ^ g)
  have hmlt : m < ω ^ g := mod_lt γ hω0
  have hgle : ω ^ g ≤ γ := opow_log_le_self ω hγ0
  have hqω : q < ω := div_opow_log_lt γ one_lt_omega0
  obtain ⟨n, hn⟩ := lt_omega0.1 hqω
  have hgs : g < s := lt_of_le_of_lt (log_le_self ω γ) hγ
  have hrE : ω ^ r = r := hB.2.1
  have hsE : ω ^ s = s := hB.1
  obtain ⟨hPT, hPpi⟩ := pi_opow' hB hgs
  obtain ⟨hPnT, hPnpi⟩ := pi_mul_nat hB hPT hPpi n
  obtain ⟨hmT, hmpi⟩ := IH m (lt_of_lt_of_le hmlt hgle) (lt_of_lt_of_le hmlt (hgle.trans hγ.le))
  have hdecomp : ∀ t : Ordinal.{0}, ω ^ t = t → t * γ = ω ^ (t + g) * (n : Ordinal.{0}) + t * m := by
    intro t ht
    conv_lhs => rw [← hdm, hn, mul_add, ← mul_assoc]
    nth_rewrite 1 [← ht]
    rw [← opow_add]
  rw [hdecomp r hrE, hdecomp s hsE]
  obtain ⟨h1, h2⟩ := pi_add hB hPnT hmT
  exact ⟨h1, by rw [h2, hPnpi, hmpi]⟩

/-- **Lemma EXACT for `x·γ + e`**: `π_{s,r}(r·γ + e) = s·γ + e` for `γ, e < s`. -/
theorem pi_term {s r γ e : Ordinal.{0}} (hB : Bases s r) (hγ : γ < s) (he : e < s) :
    r * γ + e ∈ TB r s ∧ pi s r (r * γ + e) = s * γ + e := by
  obtain ⟨h1, h2⟩ := pi_mul hB γ hγ
  obtain ⟨h3, h4⟩ := pi_add hB h1 (mem_TB_of_lt hB he)
  exact ⟨h3, by rw [h4, h2, pi_lt hB he]⟩

/-- **Lemma EXACT for `x·x`**: `π_{s,r}(r·r) = s·s` (`r·r = ω^{r+r} = ϑʳ(r)`, [W07a] Lemma 4.2, Def 5.1). -/
theorem pi_sq {s r : Ordinal.{0}} (hB : Bases s r) : r * r ∈ TB r s ∧ pi s r (r * r) = s * s := by
  obtain ⟨hsE, hrE, hsr, hr1⟩ := hB
  have hB' : Bases s r := ⟨hsE, hrE, hsr, hr1⟩
  have hsq : ∀ t : Ordinal.{0}, ω ^ t = t → t * t = ω ^ (t + t) := by
    intro t ht; nth_rewrite 1 [← ht]; nth_rewrite 2 [← ht]; rw [← opow_add]
  have h1r : (1 : Ordinal.{0}) ≤ r := one_le_iff_pos.2 hrE.pos
  have h1s : (1 : Ordinal.{0}) ≤ s := one_le_iff_pos.2 hsE.pos
  have hv := vt_opow hrE hr1 h1r le_rfl
  have hrT := (pi_base hB').1
  obtain ⟨hvT, hvP⟩ := vt_mem hrE hr1 hrT.1 hr1
  rw [hsq r hrE, hsq s hsE, ← hv]
  refine ⟨⟨hvT, by rw [hvP]; exact hrT.2⟩, ?_⟩
  rw [pi_vt hB' hrT hr1, (pi_base hB').2, vt_opow hsE (hsr.trans hr1) h1s le_rfl]

theorem mv_down {b c : Ordinal.{0}} (h : c < b) : mv b c = pi c b := by simp [mv, h]

end Googology.Trans.PoR.InaccPsi.R2
