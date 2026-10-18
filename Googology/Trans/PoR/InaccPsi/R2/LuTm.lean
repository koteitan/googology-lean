import Googology.Trans.PoR.InaccPsi.R2.LuTh

/-!
# The terms `ϑˣ(Ω₁·β + t)` of every constant level `1 ≤ β < x`: values, Lemma EXACT, the representation, Lemma RS

`LuT`: a constant (`cst a`), the base `x` (`bs`), `ϑˣ(Ω₁·β + t)` for a constant level `β` (`th β t`; `1 ≤ β < x`, the
level is one of the constants of the term), a sum (`sm`), and `ω^t` (`pw t`).  This is `VzTm` of `R2.VzT` with the
finite levels `n` replaced by every ordinal level below the base; it contains the terms of every layer `Ω₁·n + η`,
`Ω₁·ω + η`, `Ω₁·(ω+1) + η`, … of the earlier rounds.  The top is `ϑˣ(Ω₁·x)` (`luTop`), the code `Ω₁·Ω₁`.

* `LuT`, `LuT.val`, `LuT.CBt`, `LuT.cs`, `LuT.noB`; `lu_T` (**`t(x) ∈ Tˣ` and `t(x) < ϑˣ(Ω₁·x)`**: [W07a] Lemma 3.30 at
  `Ω₁·x`, `luVt_lt_top`), `lu_lt_next`, `lu_lt_ups`, `lu_top_le_next`;
* `luOm1_mul_TB`, `lu_pi_th`, `lu_pi` (**Lemma EXACT**: `t(ρ) ∈ Tᵖ[σ]` and `π_{σ,ρ}(t(ρ)) = t(σ)`), `luUni_le`,
  `luUni_lt`, `luUni_eq`;
* `lu_rep` (**representation**: every ordinal below `ϑᵖ(Ω₁·ρ)` is a value at `ρ`; an `ε`-number `v ∈ (ρ, ϑᵖ(Ω₁·ρ))` is
  `ϑᵖ(Ω₁·q + r)` with `1 ≤ q < ρ`, `r < v`, by [W07a] Lemma 3.30 at `Ω₁·ρ`, `luLt_of_vt_lt_top`);
* `lu_noB`, `le_lu_of_not_noB`, `rs_rstLu`, `rsStep_Lu` (**Lemma RS for every term**).

No new axiom beyond `R2.CitedLu`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lu

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2

/-- The terms of every constant level: a constant, the base, `ϑˣ(Ω₁·β + t)`, a sum, or `ω^t`. -/
inductive LuT : Type 1
  | cst : Ordinal.{0} → LuT
  | bs : LuT
  | th : Ordinal.{0} → LuT → LuT
  | sm : LuT → LuT → LuT
  | pw : LuT → LuT

namespace LuT

/-- The value of a term at the base `x`. -/
noncomputable def val : LuT → Ordinal.{0} → Ordinal.{0}
  | cst a, _ => a
  | bs, x => x
  | th b t, x => vt x (Om1 * b + val t x)
  | sm a b, x => val a x + val b x
  | pw t, x => ω ^ val t x

/-- All constants (the levels included) below `s`, all levels `≥ 1`. -/
def CBt : LuT → Ordinal.{0} → Prop
  | cst a, s => a < s
  | bs, _ => True
  | th b t, s => 1 ≤ b ∧ b < s ∧ CBt t s
  | sm a b, s => CBt a s ∧ CBt b s
  | pw t, s => CBt t s

/-- The constants, the levels included. -/
def cs : LuT → List Ordinal.{0}
  | cst a => [a]
  | bs => []
  | th b t => b :: cs t
  | sm a b => cs a ++ cs b
  | pw t => cs t

/-- No `bs` and no `th` occurs (a constant term). -/
def noB : LuT → Prop
  | cst _ => True
  | bs => False
  | th _ _ => False
  | sm a b => noB a ∧ noB b
  | pw t => noB t

@[simp] theorem val_cst (a x : Ordinal.{0}) : val (cst a) x = a := rfl
@[simp] theorem val_bs (x : Ordinal.{0}) : val bs x = x := rfl
@[simp] theorem val_th (b : Ordinal.{0}) (t : LuT) (x : Ordinal.{0}) :
    val (th b t) x = vt x (Om1 * b + val t x) := rfl
@[simp] theorem val_sm (a b : LuT) (x : Ordinal.{0}) : val (sm a b) x = val a x + val b x := rfl
@[simp] theorem val_pw (t : LuT) (x : Ordinal.{0}) : val (pw t) x = ω ^ val t x := rfl

theorem cbt_iff : ∀ (t : LuT) (s s' : Ordinal.{0}), CBt t s → (∀ c ∈ cs t, c < s') → CBt t s'
  | cst a, s, s', _, h => h a (by simp [cs])
  | bs, _, _, _, _ => trivial
  | th b t, s, s', h, h' => ⟨h.1, h' b (by simp [cs]), cbt_iff t s s' h.2.2 (fun c hc => h' c (by simp [cs, hc]))⟩
  | sm a b, s, s', h, h' => ⟨cbt_iff a s s' h.1 (fun c hc => h' c (by simp [cs, hc])),
      cbt_iff b s s' h.2 (fun c hc => h' c (by simp [cs, hc]))⟩
  | pw t, s, s', h, h' => cbt_iff t s s' h h'

theorem cbt_cst : ∀ (t : LuT) (s : Ordinal.{0}), CBt t s → ∀ c ∈ cs t, c < s
  | cst a, s, h, c, hc => by simp [cs] at hc; rw [hc]; exact h
  | bs, _, _, c, hc => by simp [cs] at hc
  | th b t, s, h, c, hc => by
    simp only [cs, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact h.2.1
    · exact cbt_cst t s h.2.2 c hc
  | sm a b, s, h, c, hc => by
    simp only [cs, List.mem_append] at hc
    rcases hc with hc | hc
    · exact cbt_cst a s h.1 c hc
    · exact cbt_cst b s h.2 c hc
  | pw t, s, h, c, hc => cbt_cst t s h c hc

theorem cbt_mono {t : LuT} {s s' : Ordinal.{0}} (h : CBt t s) (hs : s ≤ s') : CBt t s' :=
  cbt_iff t s s' h (fun c hc => lt_of_lt_of_le (cbt_cst t s h c hc) hs)

end LuT

open LuT

/-- **The top of all levels**: `ϑˣ(Ω₁·x)` (the code `Ω₁·Ω₁`). -/
noncomputable def luTop (x : Ordinal.{0}) : Ordinal.{0} := vt x (Om1 * x)

/-! ## Values -/

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem luTop_facts : luTop x ∈ Tset x ∧ x < luTop x ∧ luTop x < Om1 ∧ InE (luTop x) ∧ Indec (luTop x) := by
  obtain ⟨-, -, h1, h2, h3, h4, h5⟩ := lu_top_facts hx hx1
  exact ⟨h1, h2, h3, h4, h5⟩

/-- **`t(x) ∈ Tˣ` and `t(x) < ϑˣ(Ω₁·x)`** for a term with constants below `x`. -/
theorem lu_T : ∀ t : LuT, CBt t x → val t x ∈ Tset x ∧ val t x < luTop x
  | cst a, h => ⟨mem_T_of_le hx hx1 h.le, h.trans (luTop_facts hx hx1).2.1⟩
  | bs, _ => ⟨mem_T_of_le hx hx1 le_rfl, (luTop_facts hx hx1).2.1⟩
  | th b t, h => by
    obtain ⟨h1, h2⟩ := lu_T t h.2.2
    have ht1 : val t x < Om1 := h2.trans (luTop_facts hx hx1).2.2.1
    obtain ⟨-, -, hvT, -, -, -, -, -⟩ := lu_th_facts hx hx1 h.1 h.2.1 h1 ht1
    exact ⟨hvT, lu_th_lt_top hx hx1 h.2.1 h1 ht1 h2⟩
  | sm a b, h => by
    obtain ⟨h1, h2⟩ := lu_T a h.1
    obtain ⟨h3, h4⟩ := lu_T b h.2
    exact ⟨vzT_add hx hx1 h1 h3, (luTop_facts hx hx1).2.2.2.2.add_lt h2 h4⟩
  | pw t, h => by
    obtain ⟨h1, h2⟩ := lu_T t h
    obtain ⟨hTT, -, hT1, hTE, -⟩ := luTop_facts hx hx1
    have hw : ω ^ val t x < luTop x := hTE.opow_lt h2
    exact ⟨vz_T_down hx hx1 hTT hT1 hw.le, hw⟩

theorem lu_lt_Om1 {t : LuT} (ht : CBt t x) : val t x < Om1 :=
  (lu_T hx hx1 t ht).2.trans (luTop_facts hx hx1).2.2.1

/-- The top lies below every `<₁ ∞`-point above the base. -/
theorem lu_top_lt_next {u : Ordinal.{0}} (hxu : x < u) (hu : LtInf1 u) : luTop x < u := by
  obtain ⟨m, -, -, hmin, hTm, -⟩ := T_next (Or.inr hx) hx1
  obtain ⟨h1, -, h2, -, -⟩ := luTop_facts hx hx1
  exact lt_of_lt_of_le ((hTm _ h2).1 h1) (hmin u hxu hu)

/-- Term values lie below every `<₁ ∞`-point above the base. -/
theorem lu_lt_next {t : LuT} (ht : CBt t x) {u : Ordinal.{0}} (hxu : x < u) (hu : LtInf1 u) : val t x < u :=
  (lu_T hx hx1 t ht).2.trans (lu_top_lt_next hx hx1 hxu hu)

theorem lu_lt_ups {t : LuT} (ht : CBt t x) {u : Ordinal.{0}} (hxu : x < u) (hu : UpsPt u) : val t x < u :=
  lu_lt_next hx hx1 ht hxu hu.2

end Base

/-! ## Lemma EXACT -/

/-- `Ω₁·ω^b·n ∈ Tᵖ[σ]` with `π_{σ,ρ}(Ω₁·ω^b·n) = Ω₁·ω^b·n` for `b < σ`. -/
theorem luOm1_opow_nat_TB {σ ρ b : Ordinal.{0}} (hB : Bases σ ρ) (hb : b < σ) :
    ∀ n : ℕ, Om1 * ω ^ b * (n : Ordinal.{0}) ∈ TB ρ σ ∧
      pi σ ρ (Om1 * ω ^ b * (n : Ordinal.{0})) = Om1 * ω ^ b * (n : Ordinal.{0})
  | 0 => by
    rw [Nat.cast_zero, mul_zero]
    exact ⟨mem_TB_of_lt hB hB.1.pos, pi_lt hB hB.1.pos⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := luOm1_opow_nat_TB hB hb n
    obtain ⟨h3, h4⟩ := luOm1_opow_TB hB hb
    obtain ⟨h5, h6⟩ := pi_add hB h1 h3
    rw [Nat.cast_succ, mul_add_one]
    exact ⟨h5, by rw [h6, h2, h4]⟩

/-- **`Ω₁·β ∈ Tᵖ[σ]` and `π_{σ,ρ}(Ω₁·β) = Ω₁·β`** for a level `β < σ`. -/
theorem luOm1_mul_TB {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) :
    ∀ β, β < σ → Om1 * β ∈ TB ρ σ ∧ pi σ ρ (Om1 * β) = Om1 * β := by
  intro β
  induction β using WellFoundedLT.induction with
  | ind β IH =>
  intro hβ
  rcases eq_or_ne β 0 with rfl | hβ0
  · rw [mul_zero]; exact ⟨mem_TB_of_lt hB hB.1.pos, pi_lt hB hB.1.pos⟩
  set b := log ω β with hb
  have hω0 : ω ^ b ≠ 0 := (opow_pos b omega0_pos).ne'
  have hdm : ω ^ b * (β / ω ^ b) + β % ω ^ b = β := div_add_mod β (ω ^ b)
  have hmlt : β % ω ^ b < ω ^ b := mod_lt β hω0
  have hgle : ω ^ b ≤ β := opow_log_le_self ω hβ0
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt β one_lt_omega0)
  have hbβ : b ≤ β := log_le_self ω β
  obtain ⟨hm1, hm2⟩ := IH _ (hmlt.trans_le hgle) ((hmlt.trans_le hgle).trans hβ)
  obtain ⟨hp1, hp2⟩ := luOm1_opow_nat_TB hB (lt_of_le_of_lt hbβ hβ) n
  have e : Om1 * β = Om1 * ω ^ b * (n : Ordinal.{0}) + Om1 * (β % ω ^ b) := by
    conv_lhs => rw [← hdm]
    rw [mul_add, hn, mul_assoc]
  obtain ⟨hs1, hs2⟩ := pi_add hB hp1 hm1
  rw [e]
  exact ⟨hs1, by rw [hs2, hp2, hm2]⟩

/-- `Ω₁·β + γ ∈ Tᵖ[σ]` and `π_{σ,ρ}(Ω₁·β + γ) = Ω₁·β + π_{σ,ρ}(γ)`. -/
theorem lu_pi_Om1_mul_add {σ ρ β γ : Ordinal.{0}} (hB : Bases σ ρ) (hβ : β < σ) (hγ : γ ∈ TB ρ σ) :
    Om1 * β + γ ∈ TB ρ σ ∧ pi σ ρ (Om1 * β + γ) = Om1 * β + pi σ ρ γ := by
  obtain ⟨h1, h2⟩ := luOm1_mul_TB hB β hβ
  obtain ⟨h3, h4⟩ := pi_add hB h1 hγ
  exact ⟨h3, by rw [h4, h2]⟩

/-- `ϑᵖ(Ω₁·β + γ) ∈ Tᵖ[σ]` and `π_{σ,ρ}(ϑᵖ(Ω₁·β + γ)) = ϑ^σ(Ω₁·β + π_{σ,ρ}(γ))` for a level `β < σ`. -/
theorem lu_pi_th {σ ρ β γ : Ordinal.{0}} (hB : Bases σ ρ) (hβ : β < σ) (hγ : γ ∈ TB ρ σ) (hγ1 : γ < Om1) :
    vt ρ (Om1 * β + γ) ∈ TB ρ σ ∧ pi σ ρ (vt ρ (Om1 * β + γ)) = vt σ (Om1 * β + pi σ ρ γ) := by
  obtain ⟨hγTB, hpγ⟩ := lu_pi_Om1_mul_add hB hβ hγ
  have hγ2 := luOm1_mul_lt ((hβ.trans hB.2.2.1).trans hB.2.2.2) hγ1
  obtain ⟨hvT, -, -, -, hvP⟩ := vt_memTwo hB.2.1 hB.2.2.2 hγTB.1 hγ2
  exact ⟨⟨hvT, by rw [hvP]; exact hγTB.2⟩, by rw [pi_vt_two hB hγTB hγ2, hpγ]⟩

/-- **Lemma EXACT for `LuT`**: for `υ`-points `σ < ρ` (`Bases σ ρ`) and a term with constants below `σ`,
`t(ρ) ∈ Tᵖ[σ]` and `π_{σ,ρ}(t(ρ)) = t(σ)`. -/
theorem lu_pi {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) :
    ∀ t : LuT, CBt t σ → val t ρ ∈ TB ρ σ ∧ pi σ ρ (val t ρ) = val t σ
  | cst a, h => ⟨mem_TB_of_lt hB h, pi_lt hB h⟩
  | bs, _ => pi_base hB
  | th b t, h => by
    obtain ⟨h1, h2⟩ := lu_pi hσ hρ hB t h.2.2
    have ht1 : val t ρ < Om1 := lu_lt_Om1 hB.2.1 hB.2.2.2 (cbt_mono h.2.2 hB.2.2.1.le)
    obtain ⟨h3, h4⟩ := lu_pi_th hB h.2.1 h1 ht1
    simp only [val_th]
    exact ⟨h3, by rw [h4, h2]⟩
  | sm a b, h => by
    obtain ⟨h1, h2⟩ := lu_pi hσ hρ hB a h.1
    obtain ⟨h3, h4⟩ := lu_pi hσ hρ hB b h.2
    obtain ⟨h5, h6⟩ := pi_add hB h1 h3
    simp only [val_sm]
    exact ⟨h5, by rw [h6, h2, h4]⟩
  | pw t, h => by
    obtain ⟨h1, h2⟩ := lu_pi hσ hρ hB t h
    have hb := lu_lt_Om1 hB.2.1 hB.2.2.2 (t := t) (cbt_mono h hB.2.2.1.le)
    obtain ⟨h3, h4⟩ := pi_opowZ hσ hρ hB h1 hb
    simp only [val_pw]
    exact ⟨h3, by rw [h4, h2]⟩

theorem luUni_le {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : LuT}
    (ht : CBt t σ) (hu : CBt u σ) : val t ρ ≤ val u ρ ↔ val t σ ≤ val u σ := by
  obtain ⟨h1, h2⟩ := lu_pi hσ hρ hB t ht
  obtain ⟨h3, h4⟩ := lu_pi hσ hρ hB u hu
  rw [← h2, ← h4]
  exact ((pi_bijOn hB).2.le_iff_le h1 h3).symm

theorem luUni_lt {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : LuT}
    (ht : CBt t σ) (hu : CBt u σ) : val t ρ < val u ρ ↔ val t σ < val u σ := by
  rw [← not_le, ← not_le, luUni_le hσ hρ hB hu ht]

theorem luUni_eq {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : LuT}
    (ht : CBt t σ) (hu : CBt u σ) : val t ρ = val u ρ ↔ val t σ = val u σ := by
  rw [le_antisymm_iff, le_antisymm_iff, luUni_le hσ hρ hB ht hu, luUni_le hσ hρ hB hu ht]

/-! ## The representation -/

/-- **Representation**: every ordinal below `ϑᵖ(Ω₁·ρ)` is the value at `ρ` of a term with constants below `ρ`. -/
theorem lu_rep {ρ : Ordinal.{0}} (hρ : InE ρ) (hρ1 : ρ < Om1) :
    ∀ v, v < luTop ρ → ∃ t : LuT, CBt t ρ ∧ val t ρ = v := by
  obtain ⟨hTT, -, hT1, -, -⟩ := luTop_facts hρ hρ1
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  have hv1 : v < Om1 := hv.trans hT1
  have hvT : v ∈ Tset ρ := vz_T_down hρ hρ1 hTT hT1 hv.le
  rcases lt_or_ge v ρ with hvρ | hρv
  · exact ⟨cst v, hvρ, rfl⟩
  by_cases hI : Indec v
  · by_cases hE : InE v
    · rcases eq_or_lt_of_le hρv with rfl | hρv'
      · exact ⟨bs, trivial, rfl⟩
      obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hρ hρ1 hvT hρv hv1 hI
      have hΩξ : Om1 ≤ ξ := (vt_E_iff hρ hρ1 hξT hξ2).1 ⟨by rw [hξv]; exact hρv', by rw [hξv]; exact hE⟩
      obtain ⟨hq1, hrT, hr1, hdec⟩ := lu_split hρ hρ1 hξT hξ2 hΩξ
      have hqρ : ξ / Om1 < ρ :=
        lu_rep_top hρ hρ1 hξT hξ2 (by rw [hξv]; exact hρv') (by rw [hξv]; exact hv)
      have hrv : ξ % Om1 < v := by
        have := (lu_th_facts hρ hρ1 hq1 hqρ hrT hr1).2.2.2.2.2.2.2
        rwa [hdec, hξv] at this
      obtain ⟨t, ht, et⟩ := IH _ hrv (hrv.trans hv)
      exact ⟨th (ξ / Om1) t, ⟨hq1, hqρ, ht⟩, by rw [val_th, et, hdec, hξv]⟩
    · obtain ⟨L, rfl⟩ := indec_eq_opow hI
      have hL : L < ω ^ L := lt_of_le_of_ne (right_le_opow _ one_lt_omega0)
        (fun h => hE (by unfold InE; rw [← h]; exact h.symm))
      obtain ⟨t, ht, e⟩ := IH L hL (hL.trans hv)
      exact ⟨pw t, ht, by rw [val_pw, e]⟩
  · have hD : DecompR0 v := not_not.1 hI
    rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
    · exact absurd h0 (lt_of_lt_of_le hρ.pos hρv).ne'
    obtain ⟨s1, h1, e1⟩ := IH u1 hu1 (hu1.trans hv)
    obtain ⟨s2, h2, e2⟩ := IH u2 hu2 (hu2.trans hv)
    exact ⟨sm s1 s2, ⟨h1, h2⟩, by rw [val_sm, e1, e2, hsum]⟩

/-! ## Lemma RS -/

/-- A term without `bs` and `th` has a constant value. -/
theorem lu_noB : ∀ t : LuT, noB t → ∀ x y, val t x = val t y
  | cst _, _, _, _ => rfl
  | bs, h, _, _ => absurd h id
  | th _ _, h, _, _ => absurd h id
  | sm a b, h, x, y => by simp only [val_sm, lu_noB a h.1 x y, lu_noB b h.2 x y]
  | pw t, h, x, y => by simp only [val_pw, lu_noB t h x y]

/-- A term with `bs` or `th` has value `≥ x`. -/
theorem le_lu_of_not_noB {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    ∀ t : LuT, CBt t x → ¬ noB t → x ≤ val t x
  | cst _, _, h => absurd trivial h
  | bs, _, _ => le_rfl
  | th b t, hc, _ => by
    obtain ⟨h1, h2⟩ := lu_T hx hx1 t hc.2.2
    have ht1 : val t x < Om1 := h2.trans (luTop_facts hx hx1).2.2.1
    exact (lu_th_facts hx hx1 hc.1 hc.2.1 h1 ht1).2.2.2.1.le
  | sm a b, hc, h => by
    simp only [noB, not_and_or] at h
    rcases h with h | h
    · exact (le_lu_of_not_noB hx hx1 a hc.1 h).trans le_self_add
    · exact (le_lu_of_not_noB hx hx1 b hc.2 h).trans le_add_self
  | pw t, hc, h => (le_lu_of_not_noB hx hx1 t hc h).trans (right_le_opow _ one_lt_omega0)

/-- **Lemma RS with the target `t(ρ)`** (`t(ρ) ≥ ρ`, constants below `ρ`). -/
theorem rs_rstLu {r : Ordinal.{0}} (h : RstK (upsilon r) (upsilon (r + ω)) (upsilon (r + ω + 1)))
    {s : LuT} (hs : CBt s (upsilon r)) (hρs : upsilon r ≤ val s (upsilon r))
    (htarget : ∀ κ' < upsilon r, ∃ μ, κ' < upsilon μ ∧ upsilon (μ + ω + 1) < upsilon r ∧
      RstK (upsilon μ) (upsilon (μ + ω)) (upsilon (μ + ω + 1)) ∧
      ∀ g, upsilon μ ≤ g → g ≤ upsilon (μ + ω + 1) + val s (upsilon μ) → le1 (upsilon μ) g) :
    le1 (upsilon r) (upsilon (r + ω + 1) + val s (upsilon r) + 1) := by
  classical
  have hnx := upsilon_isNext r
  have hCs : ∀ σ, (∀ c ∈ (cs s).toFinset, c < σ) → CBt s σ := fun σ hσ =>
    cbt_iff s _ σ hs (fun c hc => hσ c (List.mem_toFinset.2 hc))
  refine rs_rstF (T := val s) (C := (cs s).toFinset) h
    (fun c hc => cbt_cst s _ hs c (List.mem_toFinset.1 hc)) hρs
    (lu_lt_ups h.ρE h.ρ1 hs hnx.1 hnx.2.1) ?_ ?_ htarget
  · intro σ hσ hB hCσ _
    exact (lu_pi hσ h.ρU hB s (hCs σ hCσ)).2
  · intro σ hσE hσρ _ hCσ
    exact lu_lt_next hσE (hσρ.trans h.ρ1) (hCs σ hCσ) hσρ h.ρU.2

/-- **Lemma RS for every term of `LuT`** with constants below `ρ_λ`. -/
theorem rsStep_Lu {l : Ordinal.{0}} {s : LuT} (hs : CBt s (upsilon l)) : RsStep l (val s) := by
  intro R htg
  by_cases hρs : upsilon l ≤ val s (upsilon l)
  · exact rs_rstLu R hs hρs htg
  · have hn : noB s := by
      by_contra hn
      exact hρs (le_lu_of_not_noB R.ρE R.ρ1 s hs hn)
    set c := val s (upsilon l) with hc
    have e : val s = OT.ev (OT.k c) := funext (fun y => by rw [OT.ev_k, hc, lu_noB s hn y])
    have hcb : OT.CB (OT.k c) (upsilon l) := not_le.1 hρs
    rw [e] at htg
    have := rs_rstT R hcb htg
    rwa [OT.ev_k] at this

end Googology.Trans.PoR.InaccPsi.R2.Lu
