import Googology.Trans.PoR.InaccPsi.R2.SfRefl

/-!
# The last summand of a normal chain, and the last exponent under σ

A normal-form sum is a chain `p₁ + (p₂ + ⋯ + p_m)` of principal terms `p₁ ≥ ⋯ ≥ p_m`.
`sfLast t = p_m` (the last summand) and `sfInit t = p₁ + ⋯ + p_{m-1}` (`zero` for `m ≤ 1`).
`σ = bcSig (bcPre (n+1)) bcPreW`, `θ = ψ_{Ω₂}(Ω_ω)`; `cdExp x` is the last exponent of `x`
(`Cd.cdExp`: the largest `e` with `ω^e ∣ x`).

* `sfInit_val`: `|t| = |sfInit t| + |sfLast t|`; `sfInit_dvd`: `ω^g ∣ |sfInit t|` when `|sfLast t| = ω^g`
  (the summands are decreasing); `sfInit_NF`, `sfInit_args`, `sfLast_sub`: the parts are normal and
  inside `t`; `sfLast_sig`, `sfInit_sig`: `σ` commutes with both;
* `sfCdExp`, `sfCdExp_any`: `cdExp(I + ω^h) = h` when `ω^h ∣ I`, and `cdExp(Y + ω^g) = g` for every `Y`;
  `sfLast_val`: **if `|t| = Y + ω^g` then `|sfLast t| = ω^g`**;
* `sfSig_dvdG` (**σ keeps `ω^g`-divisibility** for a threshold `ω^g` that is the value of a normal term
  `σ` fixes); `sfSig_val_inj`: `|σ(s)| = |σ(t)|` gives `|s| = |t|` on the domain of `σ`;
* `sfThK k`: a normal term of `θ·k` that `σ` fixes; `sfArgs_addNF`, `sfFree_addNF`: `addNF` keeps the
  argument bounds and freeness.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

/-! ## Ordinal facts -/

theorem sfMul_inj {a b c : Ordinal.{0}} (ha : 0 < a) (h : a * b = a * c) : b = c := by
  rcases lt_trichotomy b c with h1 | h1 | h1
  · exact absurd h ((mul_lt_mul_iff_right₀ ha).2 h1).ne
  · exact h1
  · exact absurd h ((mul_lt_mul_iff_right₀ ha).2 h1).ne'

/-- A nonzero principal `x ≥ ω^g` is a multiple of `ω^g`. -/
theorem sfDvd_prin {x g : Ordinal.{0}} (hP : IsPrincipal (· + ·) x) (hx0 : x ≠ 0)
    (h : ω ^ g ≤ x) : ω ^ g ∣ x := by
  obtain ⟨e, rfl⟩ := exists_opow_of_principal hP hx0
  exact opow_dvd_opow ω ((opow_le_opow_iff_right one_lt_omega0).1 h)

/-- `cdExp(I + ω^h) = h` when `ω^h ∣ I`. -/
theorem sfCdExp {I h : Ordinal.{0}} (hI : ω ^ h ∣ I) : Cd.cdExp (I + ω ^ h) = h := by
  have hne : I + ω ^ h ≠ 0 := (lt_of_lt_of_le (opow_pos h omega0_pos) le_add_self).ne'
  refine le_antisymm ?_ (Cd.cdExp_max hne (dvd_add hI (dvd_refl _)))
  by_contra hlt
  push Not at hlt
  have hd : ω ^ (h + 1) ∣ I + ω ^ h :=
    (opow_dvd_opow ω (Order.add_one_le_of_lt hlt)).trans (Cd.cdExp_dvd hne)
  obtain ⟨m, rfl⟩ := hI
  obtain ⟨q, hq⟩ := hd
  rw [← mul_add_one, opow_add, opow_one, mul_assoc] at hq
  have e := sfMul_inj (opow_pos h omega0_pos) hq
  have hl : IsSuccPrelimit (m + 1) := isSuccPrelimit_iff_omega0_dvd.2 ⟨q, e⟩
  rw [← Order.succ_eq_add_one] at hl
  exact Order.not_isSuccPrelimit_succ m hl

/-- `cdExp(Y + ω^g) = g` for every `Y`. -/
theorem sfCdExp_any (Y g : Ordinal.{0}) : Cd.cdExp (Y + ω ^ g) = g := by
  have hω : ω ^ g ≠ 0 := (opow_pos g omega0_pos).ne'
  have e : Y + ω ^ g = ω ^ g * (Y / ω ^ g) + ω ^ g := by
    conv_lhs => rw [← div_add_mod Y (ω ^ g)]
    rw [add_assoc, add_omega0_opow (mod_lt Y hω)]
  rw [e]
  exact sfCdExp (dvd_mul_right _ _)

/-! ## The last summand -/

/-- The last summand of a chain. -/
def sfLast : Term → Term
  | Term.add _ b => sfLast b
  | t => t

/-- The chain without its last summand. -/
def sfInit : Term → Term
  | Term.add a b => if b.isPrin then a else Term.add a (sfInit b)
  | _ => Term.zero

theorem sfLast_of_prin {t : Term} (h : t.isPrin = true) : sfLast t = t := by
  cases t <;> simp [isPrin, isSC] at h <;> rfl

theorem sfInit_of_prin {t : Term} (h : t.isPrin = true) : sfInit t = Term.zero := by
  cases t <;> simp [isPrin, isSC] at h <;> rfl

theorem sfLast_prin : ∀ {t : Term}, NF t → t ≠ Term.zero → (sfLast t).isPrin = true
  | Term.add _ b, h, _ => by simp only [sfLast]; exact sfLast_prin h.2.1 h.2.2.2.1
  | Term.zero, _, h0 => absurd rfl h0
  | Term.inacc _, _, _ => rfl
  | Term.inaccW, _, _ => rfl
  | Term.phi _ _, _, _ => rfl
  | Term.om _, _, _ => rfl
  | Term.psiS _ _, _, _ => rfl
  | Term.psiI _ _, _, _ => rfl

theorem sfLast_sub : ∀ t : Term, bcSub (sfLast t) t
  | Term.add a b => by simp only [sfLast]; exact bcSub_trans (sfLast_sub b) (sub_add_r a b)
  | Term.zero => bcSub_refl _
  | Term.inacc _ => bcSub_refl _
  | Term.inaccW => bcSub_refl _
  | Term.phi _ _ => bcSub_refl _
  | Term.om _ => bcSub_refl _
  | Term.psiS _ _ => bcSub_refl _
  | Term.psiI _ _ => bcSub_refl _

theorem sfInit_args {A : Ordinal.{0}} : ∀ {t : Term}, bcArgsLt S A t → bcArgsLt S A (sfInit t)
  | Term.add a b, h => by
    simp only [sfInit]; split_ifs
    · exact h.1
    · exact ⟨h.1, sfInit_args h.2⟩
  | Term.zero, _ => trivial
  | Term.inacc _, _ => trivial
  | Term.inaccW, _ => trivial
  | Term.phi _ _, _ => trivial
  | Term.om _, _ => trivial
  | Term.psiS _ _, _ => trivial
  | Term.psiI _ _, _ => trivial

/-- `sfInit` of a chain with two or more summands keeps its head. -/
theorem sfInit_NF : ∀ {t : Term}, NF t →
    NF (sfInit t) ∧ (t.isPrin = false → t ≠ Term.zero → sfInit t ≠ Term.zero ∧ head (sfInit t) = head t)
  | Term.add a b, h => by
    simp only [sfInit]
    split_ifs with hb
    · exact ⟨h.1, fun _ _ => ⟨NF.ne_zero_of_isPrin h.2.2.1, head_of_isPrin h.2.2.1⟩⟩
    · have hbp : b.isPrin = false := by simpa using hb
      obtain ⟨ih1, ih2⟩ := sfInit_NF h.2.1
      obtain ⟨hne, hhd⟩ := ih2 hbp h.2.2.2.1
      refine ⟨⟨h.1, ih1, h.2.2.1, hne, by rw [hhd]; exact h.2.2.2.2⟩, fun _ _ => ⟨by simp, rfl⟩⟩
  | Term.zero, _ => ⟨trivial, fun _ h0 => absurd rfl h0⟩
  | Term.inacc _, _ => ⟨trivial, fun h => by simp [isPrin, isSC] at h⟩
  | Term.inaccW, _ => ⟨trivial, fun h => by simp [isPrin, isSC] at h⟩
  | Term.phi _ _, _ => ⟨trivial, fun h => by simp [isPrin] at h⟩
  | Term.om _, _ => ⟨trivial, fun h => by simp [isPrin, isSC] at h⟩
  | Term.psiS _ _, _ => ⟨trivial, fun h => by simp [isPrin, isSC] at h⟩
  | Term.psiI _ _, _ => ⟨trivial, fun h => by simp [isPrin, isSC] at h⟩

theorem sfInit_val : ∀ {t : Term}, NF t → val S t = val S (sfInit t) + val S (sfLast t)
  | Term.add a b, h => by
    simp only [sfInit, sfLast]
    split_ifs with hb
    · rw [sfLast_of_prin hb]; rfl
    · show val S a + val S b = val S a + val S (sfInit b) + val S (sfLast b)
      rw [add_assoc, ← sfInit_val h.2.1]
  | Term.zero, _ => by simp [sfInit, sfLast, val]
  | Term.inacc _, _ => by simp [sfInit, sfLast, val]
  | Term.inaccW, _ => by simp [sfInit, sfLast, val]
  | Term.phi _ _, _ => by simp [sfInit, sfLast, val]
  | Term.om _, _ => by simp [sfInit, sfLast, val]
  | Term.psiS _ _, _ => by simp [sfInit, sfLast, val]
  | Term.psiI _ _, _ => by simp [sfInit, sfLast, val]

/-- The last summand is at most the head. -/
theorem sfLast_le_head : ∀ {t : Term}, NF t → val S (sfLast t) ≤ val S (head t)
  | Term.add a b, h => by
    simp only [sfLast, head]
    refine (sfLast_le_head h.2.1).trans ?_
    have e := cmp_eq_compare S h.2.1.head h.1
    rcases hc : compare (val S (head b)) (val S a) with _ | _ | _
    · exact (compare_lt_iff_lt.1 hc).le
    · exact (compare_eq_iff_eq.1 hc).le
    · rw [hc] at e; exact absurd e h.2.2.2.2
  | Term.zero, _ => le_rfl
  | Term.inacc _, _ => le_rfl
  | Term.inaccW, _ => le_rfl
  | Term.phi _ _, _ => le_rfl
  | Term.om _, _ => le_rfl
  | Term.psiS _ _, _ => le_rfl
  | Term.psiI _ _, _ => le_rfl

/-- The initial part is a multiple of the last summand `ω^g`. -/
theorem sfInit_dvd {g : Ordinal.{0}} : ∀ {t : Term}, NF t → val S (sfLast t) = ω ^ g →
    ω ^ g ∣ val S (sfInit t)
  | Term.add a b, h, hg => by
    simp only [sfInit, sfLast] at hg ⊢
    have hb0 : val S (sfLast b) ≤ val S a := by
      refine (sfLast_le_head h.2.1).trans ?_
      have e := cmp_eq_compare S h.2.1.head h.1
      rcases hc : compare (val S (head b)) (val S a) with _ | _ | _
      · exact (compare_lt_iff_lt.1 hc).le
      · exact (compare_eq_iff_eq.1 hc).le
      · rw [hc] at e; exact absurd e h.2.2.2.2
    have ha : ω ^ g ∣ val S a := by
      refine sfDvd_prin (isPrincipal_val S h.1 h.2.2.1)
        (val_ne_zero S h.1 (NF.ne_zero_of_isPrin h.2.2.1)) ?_
      rw [← hg]; exact hb0
    split_ifs with hb
    · exact ha
    · exact dvd_add ha (sfInit_dvd h.2.1 hg)
  | Term.zero, _, _ => by simp [sfInit, val]
  | Term.inacc _, _, _ => by simp [sfInit, val]
  | Term.inaccW, _, _ => by simp [sfInit, val]
  | Term.phi _ _, _, _ => by simp [sfInit, val]
  | Term.om _, _, _ => by simp [sfInit, val]
  | Term.psiS _ _, _, _ => by simp [sfInit, val]
  | Term.psiI _ _, _, _ => by simp [sfInit, val]

/-- **The last summand of a chain with value `Y + ω^g` is `ω^g`.** -/
theorem sfLast_val {t : Term} (hN : NF t) (h0 : t ≠ Term.zero) {Y g : Ordinal.{0}}
    (hv : val S t = Y + ω ^ g) : val S (sfLast t) = ω ^ g := by
  have hP := sfLast_prin hN h0
  have hlN : NF (sfLast t) := NF_of_sub (sfLast_sub t) hN
  have hl0 : val S (sfLast t) ≠ 0 := val_ne_zero S hlN (NF.ne_zero_of_isPrin hP)
  obtain ⟨h, hh⟩ := exists_opow_of_principal (isPrincipal_val S hlN hP) hl0
  have hd := sfInit_dvd (S := S) hN hh
  have e1 := sfInit_val (S := S) hN
  rw [hh] at e1
  have c1 := sfCdExp hd
  rw [← e1, hv, sfCdExp_any] at c1
  rw [hh, c1]

/-! ## `σ` and the last summand -/

section Sig

variable {Ps Pt : List Term}

theorem sfSig_nonadd : ∀ {t : Term}, t.isPrin = true → (bcSig Ps Pt t).isPrin = true := by
  intro t h; rw [isPrin_bcSig]; exact h

theorem sfLast_sig : ∀ t : Term, sfLast (bcSig Ps Pt t) = bcSig Ps Pt (sfLast t)
  | Term.add a b => by rw [bcSig_add]; simp only [sfLast]; exact sfLast_sig b
  | Term.zero => by simp [sfLast]
  | Term.inacc _ => by simp [sfLast]
  | Term.inaccW => by simp [sfLast]
  | Term.phi a b => by
    rw [sfLast_of_prin (t := phi a b) rfl, sfLast_of_prin (sfSig_nonadd (t := phi a b) rfl)]
  | Term.om a => by
    rw [sfLast_of_prin (t := om a) rfl, sfLast_of_prin (sfSig_nonadd (t := om a) rfl)]
  | Term.psiS s a => by
    rw [sfLast_of_prin (t := psiS s a) rfl, sfLast_of_prin (sfSig_nonadd (t := psiS s a) rfl)]
  | Term.psiI m a => by
    rw [sfLast_of_prin (t := psiI m a) rfl, sfLast_of_prin (sfSig_nonadd (t := psiI m a) rfl)]

theorem sfInit_sig : ∀ t : Term, sfInit (bcSig Ps Pt t) = bcSig Ps Pt (sfInit t)
  | Term.add a b => by
    rw [bcSig_add]; simp only [sfInit, isPrin_bcSig]
    split_ifs
    · rfl
    · rw [bcSig_add, sfInit_sig b]
  | Term.zero => by simp [sfInit]
  | Term.inacc _ => by simp [sfInit]
  | Term.inaccW => by simp [sfInit]
  | Term.phi _ _ => by rw [bcSig_phi]; simp [sfInit]
  | Term.om _ => by rw [bcSig_om]; simp [sfInit]
  | Term.psiS s a => by
    rw [sfInit_of_prin (t := psiS s a) rfl, sfInit_of_prin (sfSig_nonadd (t := psiS s a) rfl),
      bcSig_zero]
  | Term.psiI _ _ => by rw [bcSig_psiI]; simp [sfInit]

end Sig

/-! ## σ keeps `ω^g`-divisibility -/

section Dvd

variable {n : ℕ} {e : Term} {g : Ordinal.{0}}

/-- `|σ(s)| = |σ(t)|` gives `|s| = |t|` on the domain of `σ`. -/
theorem sfSig_val_inj {s t : Term} (hs : bcD S s) (ht : bcD S t)
    (h : val S (bcSig (bcPre (n + 1)) bcPreW s) = val S (bcSig (bcPre (n + 1)) bcPreW t)) :
    val S s = val S t := by
  rcases lt_trichotomy (val S s) (val S t) with h1 | h1 | h1
  · exact absurd h ((bc_lt_iff (k := n) hs ht).2 h1).ne
  · exact h1
  · exact absurd h ((bc_lt_iff (k := n) ht hs).2 h1).ne'

theorem sfSig_dvdG_prin (he : NF e) (hef : bcFree e) (hev : val S e = ω ^ g) {p : Term}
    (hD : bcD S p) (hP : p.isPrin = true) (h : ω ^ g ∣ val S p) :
    ω ^ g ∣ val S (bcSig (bcPre (n + 1)) bcPreW p) := by
  have hp0 : p ≠ Term.zero := NF.ne_zero_of_isPrin hP
  have hv0 : val S p ≠ 0 := val_ne_zero S hD.1 hp0
  have hθ : ω ^ g ≤ val S p := Ordinal.le_of_dvd hv0 h
  have hN := bc_NF (k := n) hD
  have hσ : ω ^ g ≤ val S (bcSig (bcPre (n + 1)) bcPreW p) := by
    have := (bc_lt_iff (k := n) hD (bcD_free he hef)).not.2 (not_lt.2 (by rw [hev]; exact hθ))
    rw [not_lt, bcSig_free hef, hev] at this
    exact this
  refine sfDvd_prin (isPrincipal_val S hN (by rw [isPrin_bcSig]; exact hP)) ?_ hσ
  exact (lt_of_lt_of_le (opow_pos g omega0_pos) hσ).ne'

/-- **σ keeps `ω^g`-divisibility** (`ω^g` the value of a normal term that `σ` fixes). -/
theorem sfSig_dvdG (he : NF e) (hef : bcFree e) (hev : val S e = ω ^ g) :
    ∀ {r : Term}, bcD S r → ω ^ g ∣ val S r → ω ^ g ∣ val S (bcSig (bcPre (n + 1)) bcPreW r)
  | Term.zero, _, _ => by rw [bcSig_zero]; exact dvd_zero _
  | Term.add p r, hD, h => by
    have hN := hD.1
    have hDp : bcD S p := bcD_sub hD (sub_add_l p r)
    have hDr : bcD S r := bcD_sub hD (sub_add_r p r)
    have hp : ω ^ g ∣ val S p := by
      have hP : p.isPrin = true := hN.2.2.1
      have hp0 : val S p ≠ 0 := val_ne_zero S hN.1 (NF.ne_zero_of_isPrin hP)
      refine sfDvd_prin (isPrincipal_val S hN.1 hP) hp0 ?_
      by_contra hlt
      push Not at hlt
      obtain ⟨h', hg'⟩ := exists_opow_of_principal (isPrincipal_val S hN.1 hP) hp0
      have hgθ : h' < g := by
        rw [hg'] at hlt
        exact (opow_lt_opow_iff_right one_lt_omega0).1 hlt
      have hb : val S (Term.add p r) < val S p * ω := by
        have := val_lt_head_mul (S := S) hN (by simp)
        simpa [head] using this
      have hle : val S p * ω ≤ ω ^ g := by
        rw [hg', ← opow_succ]
        exact opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hgθ)
      have hne : val S (Term.add p r) ≠ 0 := val_ne_zero S hN (by simp)
      have := Ordinal.le_of_dvd hne h
      exact absurd (hb.trans_le hle) (not_lt.2 this)
    have hr : ω ^ g ∣ val S r := (dvd_add_iff hp).1 h
    rw [bcSig_add]
    exact dvd_add (sfSig_dvdG_prin he hef hev hDp hN.2.2.1 hp) (sfSig_dvdG he hef hev hDr hr)
  | Term.inacc m, hD, h => sfSig_dvdG_prin he hef hev hD rfl h
  | Term.inaccW, hD, h => sfSig_dvdG_prin he hef hev hD rfl h
  | Term.phi a b, hD, h => sfSig_dvdG_prin he hef hev hD rfl h
  | Term.om a, hD, h => sfSig_dvdG_prin he hef hev hD rfl h
  | Term.psiS s a, hD, h => sfSig_dvdG_prin he hef hev hD rfl h
  | Term.psiI m a, hD, h => sfSig_dvdG_prin he hef hev hD rfl h

end Dvd

/-! ## `addNF` and the term of `θ·k` -/

theorem sfArgs_addNF {A : Ordinal.{0}} : ∀ {x y : Term}, bcArgsLt S A x → bcArgsLt S A y →
    bcArgsLt S A (addNF x y)
  | Term.zero, _, _, hy => hy
  | Term.add a b, y, hx, hy => by
    rw [addNF_add]; split_ifs
    · exact hx
    · exact hy
    · exact ⟨hx.1, sfArgs_addNF hx.2 hy⟩
  | Term.inacc m, y, hx, hy => by
    rw [addNF_prin (x := Term.inacc m) rfl]; split_ifs
    · exact hx
    · exact hy
    · exact ⟨hx, hy⟩
  | Term.inaccW, y, hx, hy => by
    rw [addNF_prin (x := Term.inaccW) rfl]; split_ifs
    · exact hx
    · exact hy
    · exact ⟨hx, hy⟩
  | Term.phi a b, y, hx, hy => by
    rw [addNF_prin (x := Term.phi a b) rfl]; split_ifs
    · exact hx
    · exact hy
    · exact ⟨hx, hy⟩
  | Term.om a, y, hx, hy => by
    rw [addNF_prin (x := Term.om a) rfl]; split_ifs
    · exact hx
    · exact hy
    · exact ⟨hx, hy⟩
  | Term.psiS s a, y, hx, hy => by
    rw [addNF_prin (x := Term.psiS s a) rfl]; split_ifs
    · exact hx
    · exact hy
    · exact ⟨hx, hy⟩
  | Term.psiI m a, y, hx, hy => by
    rw [addNF_prin (x := Term.psiI m a) rfl]; split_ifs
    · exact hx
    · exact hy
    · exact ⟨hx, hy⟩

theorem sfFree_addNF : ∀ {x y : Term}, bcFree x → bcFree y → bcFree (addNF x y)
  | Term.zero, _, _, hy => hy
  | Term.add a b, y, hx, hy => by
    rw [addNF_add]; split_ifs
    · exact hx
    · exact hy
    · exact ⟨hx.1, sfFree_addNF hx.2 hy⟩
  | Term.inacc m, y, hx, hy => by
    rw [addNF_prin (x := Term.inacc m) rfl]; split_ifs
    · exact hx
    · exact hy
    · exact ⟨hx, hy⟩
  | Term.inaccW, y, hx, hy => by
    rw [addNF_prin (x := Term.inaccW) rfl]; split_ifs
    · exact hx
    · exact hy
    · exact ⟨hx, hy⟩
  | Term.phi a b, y, hx, hy => by
    rw [addNF_prin (x := Term.phi a b) rfl]; split_ifs
    · exact hx
    · exact hy
    · exact ⟨hx, hy⟩
  | Term.om a, y, hx, hy => by
    rw [addNF_prin (x := Term.om a) rfl]; split_ifs
    · exact hx
    · exact hy
    · exact ⟨hx, hy⟩
  | Term.psiS s a, y, hx, hy => by
    rw [addNF_prin (x := Term.psiS s a) rfl]; split_ifs
    · exact hx
    · exact hy
    · exact ⟨hx, hy⟩
  | Term.psiI m a, y, hx, hy => by
    rw [addNF_prin (x := Term.psiI m a) rfl]; split_ifs
    · exact hx
    · exact hy
    · exact ⟨hx, hy⟩

/-- A normal term of `θ·k`. -/
def sfThK : ℕ → Term
  | 0 => Term.zero
  | k + 1 => addNF (sfThK k) sfThT

theorem sfThK_spec (S : InaccSeq.{0}) : ∀ k : ℕ,
    NF (sfThK k) ∧ bcFree (sfThK k) ∧ val S (sfThK k) = ConjT.th S * k
  | 0 => ⟨trivial, trivial, by simp [sfThK, val]⟩
  | k + 1 => by
    obtain ⟨h1, h2, h3⟩ := sfThK_spec S k
    obtain ⟨hN, hv, -⟩ := addNF_spec (S := S) h1 sfThT_NF
    refine ⟨hN, sfFree_addNF h2 sfThT_free, ?_⟩
    show val S (addNF (sfThK k) sfThT) = _
    rw [hv, h3, sfThT_val, Nat.cast_succ, mul_add_one]

end Googology.Trans.PoR.InaccPsi.R2.Sf
