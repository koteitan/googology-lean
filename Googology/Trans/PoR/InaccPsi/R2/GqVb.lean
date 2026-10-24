import Googology.Trans.PoR.InaccPsi.R2.GqFr

/-!
# THE ϑ-INDEX ↔ VEBLEN-INDEX LINK, and the reach test of every finite Veblen level

At an `ε`-number base `x < Ω₁`, every `ε`-number `E ∈ Tˣ ∩ (x, Γ_{x+1})` is `E = ϑˣ(Ω₁·q + r)` with `1 ≤ q`,
`q, r ∈ Tˣ ∩ Ω₁` (`gq_th_rep`).  Then:

* `gq_veb_level` (**THE LINK**: for `1 ≤ β`, `E ∈ range φ(β, ·)` iff `β ≤ q`: the Veblen index of `E` IS its ϑ-index,
  from `lv_th_P` (`E ∈ P_q`) and `lv_th_notP` (`E ∉ P_{q+1}`));
* `gq_lh_th` (**the `R₁⁺`-reach `lh(E) = luL(E, q) + ζ`** at every ϑ-index `q`, `Lu.lu_lh_th` for `q < x`,
  `Lv.lv_lh_gen` for `q ≥ x`);
* `gq_veb_le1R` (**`E ∈ range φ(n, ·)`, `1 ≤ n < ω` ⇒ `E ≤₁ E·(n+1)` in `R₁⁺`**), `gq_veb_le1R_inf`
  (**`E ∈ range φ(β, ·)`, `β ≥ ω` ⇒ `E ≤₁ E·ω`**);
* `gq_le1R_veb` (**the converse**: `E ≤₁ E·(n+1)` ⇒ `E ∈ range φ(n, ·)`), `gq_veb_iff_le1R` (**the level test
  `E ∈ range φ(n, ·) ⇔ E ≤₁ E·(n+1)`** at every finite level `n ≥ 1`; `le1R_two_iff` was the case `n = 1`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gq

open Ordinal Order Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lu

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **Every `ε`-number `E ∈ (x, Γ_{x+1})` is `ϑˣ(Ω₁·q + r)`** with `1 ≤ q`, `q, r ∈ Tˣ ∩ Ω₁`. -/
theorem gq_th_rep {E : Ordinal.{0}} (hE : InE E) (hxE : x < E) (hEG : E < lgG x) :
    ∃ q r, 1 ≤ q ∧ q ∈ Tset x ∧ q < Om1 ∧ r ∈ Tset x ∧ r < Om1 ∧ vt x (Om1 * q + r) = E := by
  obtain ⟨n, hn⟩ := lt_lgG_iff.1 hEG
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 1 := by
    rcases n with _ | M
    · exact absurd (eN_le hxE hE) (not_le.2 hn)
    · exact ⟨M, rfl⟩
  obtain ⟨hTT, -, hT1, -⟩ := gT_facts hx hx1 (M + 1)
  have hE1 : E < Om1 := hn.trans hT1
  have hET : E ∈ Tset x := vz_T_down hx hx1 hTT hT1 hn.le
  obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 hET hxE.le hE1 (inE_indec hE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxE, by rw [hξv]; exact hE⟩
  obtain ⟨hq1, hrT, hr1, hdec⟩ := lu_split hx hx1 hξT hξ2 hΩξ
  have hqM : ξ / Om1 < gT M x :=
    lvg_quot hx hx1 M ξ hξT hξ2 (by rw [hξv]; exact hxE) (by rw [hξv]; exact hE) (by rw [hξv]; exact hn)
  obtain ⟨hMT, -, hM1, -⟩ := gT_facts hx hx1 M
  exact ⟨ξ / Om1, ξ % Om1, hq1, vz_T_down hx hx1 hMT hM1 hqM.le, hqM.trans hM1, hrT, hr1, by rw [hdec, hξv]⟩

section Th

variable {q r : Ordinal.{0}} (hq1 : 1 ≤ q) (hqT : q ∈ Tset x) (hqΩ : q < Om1) (hrT : r ∈ Tset x) (hr1 : r < Om1)
include hq1 hqT hqΩ hrT hr1

/-- **THE ϑ-INDEX ↔ VEBLEN-INDEX LINK**: `ϑˣ(Ω₁·q + r) ∈ range φ(β, ·)` iff `β ≤ q` (`1 ≤ β`). -/
theorem gq_veb_level {β : Ordinal.{0}} (hβ1 : 1 ≤ β) : LuP β (vt x (Om1 * q + r)) ↔ β ≤ q := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have h' : LuP (q + 1) (vt x (Om1 * q + r)) := luP_mono le_add_self (Order.add_one_le_of_lt hlt) h
    exact lv_th_notP hx hx1 hq1 hqT hqΩ hrT hr1 h'
  · intro h
    exact luP_mono hβ1 h (lv_th_P hx hx1 q hq1 hqT hqΩ r hrT hr1)

/-- **The `R₁⁺`-reach of `ϑˣ(Ω₁·q + r)` at every ϑ-index `q`**, and `ζ < ϑˣ(Ω₁·q + r)`. -/
theorem gq_lh_th : IsLh1 (vt x (Om1 * q + r)) (luL (vt x (Om1 * q + r)) q + luZeta x q r) ∧
    luZeta x q r < vt x (Om1 * q + r) ∧ q < vt x (Om1 * q + r) ∧ InE (vt x (Om1 * q + r)) := by
  rcases lt_or_ge q x with hqx | hxq
  · obtain ⟨-, -, -, -, -, hvE, -, hrv⟩ := lu_th_facts hx hx1 hq1 hqx hrT hr1
    refine ⟨lu_lh_th hx hx1 hq1 hqx hrT hr1, lu_zeta_le.trans_lt hrv, ?_, hvE⟩
    exact hqx.trans (lu_th_facts hx hx1 hq1 hqx hrT hr1).2.2.2.1
  · obtain ⟨-, -, -, -, -, hvE, -, hqv, hrv⟩ := Lv.gen_facts hx hx1 hqT hxq hqΩ hrT hr1
    exact ⟨Lv.lv_lh_gen hx hx1 hqT hxq hqΩ hrT hr1, lu_zeta_le.trans_lt hrv, hqv, hvE⟩

end Th

/-- **`E ∈ range φ(n, ·)`, `1 ≤ n < ω`, ⇒ `E ≤₁ E·(n+1)` in `R₁⁺`** (`E` an `ε`-number in `(x, Γ_{x+1})`). -/
theorem gq_veb_le1R {E : Ordinal.{0}} (hE : InE E) (hxE : x < E) (hEG : E < lgG x) {n : ℕ} (hn : 1 ≤ n)
    (hP : LuP n E) : le1R E (E * ((n : Ordinal.{0}) + 1)) := by
  obtain ⟨q, r, hq1, hqT, hqΩ, hrT, hr1, rfl⟩ := gq_th_rep hx hx1 hE hxE hEG
  have hnq : (n : Ordinal.{0}) ≤ q :=
    (gq_veb_level hx hx1 hq1 hqT hqΩ hrT hr1 (by exact_mod_cast hn)).1 hP
  obtain ⟨hL, -, -, -⟩ := gq_lh_th hx hx1 hq1 hqT hqΩ hrT hr1
  set E := vt x (Om1 * q + r)
  have hle : E * ((n : Ordinal.{0}) + 1) ≤ luL E q + luZeta x q r := by
    refine le_trans ?_ le_self_add
    unfold luL
    split_ifs with hqω
    · have e : (1 : Ordinal.{0}) + q = q + 1 := by
        obtain ⟨m, rfl⟩ := lt_omega0.1 hqω
        rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, add_comm]
      rw [e]
      exact mul_le_mul_left' (by gcongr) E
    · push Not at hqω
      have hlog : 1 ≤ log ω q := by
        have := le_log_of_opow_le one_lt_omega0 (show ω ^ (1 : Ordinal.{0}) ≤ q by rw [opow_one]; exact hqω)
        exact this
      have h1 : E * ((n : Ordinal.{0}) + 1) ≤ E * ω ^ log ω q := by
        refine mul_le_mul_left' ?_ E
        calc (n : Ordinal.{0}) + 1 ≤ ω := (Order.add_one_le_of_lt (natCast_lt_omega0 n)).trans le_rfl
          _ = ω ^ (1 : Ordinal.{0}) := (opow_one ω).symm
          _ ≤ ω ^ log ω q := opow_le_opow_right omega0_pos hlog
      exact h1.trans (le_self_add.trans le_self_add)
  have hEle : E ≤ E * ((n : Ordinal.{0}) + 1) := le_mul_of_one_le_right' le_add_self
  exact le1R_of_le hEle hle hL.1

/-- **`E ∈ range φ(β, ·)`, `β ≥ ω`, ⇒ `E ≤₁ E·ω` in `R₁⁺`.** -/
theorem gq_veb_le1R_inf {E β : Ordinal.{0}} (hE : InE E) (hxE : x < E) (hEG : E < lgG x) (hβ : ω ≤ β)
    (hP : LuP β E) : le1R E (E * ω) := by
  obtain ⟨q, r, hq1, hqT, hqΩ, hrT, hr1, rfl⟩ := gq_th_rep hx hx1 hE hxE hEG
  have hβq : β ≤ q := (gq_veb_level hx hx1 hq1 hqT hqΩ hrT hr1 (one_lt_omega0.le.trans hβ)).1 hP
  obtain ⟨hL, -, -, -⟩ := gq_lh_th hx hx1 hq1 hqT hqΩ hrT hr1
  set E := vt x (Om1 * q + r)
  have hqω : ω ≤ q := hβ.trans hβq
  have hle : E * ω ≤ luL E q + luZeta x q r := by
    refine le_trans ?_ le_self_add
    unfold luL
    rw [if_neg (not_lt.2 hqω)]
    have hlog : 1 ≤ log ω q :=
      le_log_of_opow_le one_lt_omega0 (show ω ^ (1 : Ordinal.{0}) ≤ q by rw [opow_one]; exact hqω)
    have h1 : E * ω ≤ E * ω ^ log ω q := by
      refine mul_le_mul_left' ?_ E
      calc ω = ω ^ (1 : Ordinal.{0}) := (opow_one ω).symm
        _ ≤ ω ^ log ω q := opow_le_opow_right omega0_pos hlog
    exact h1.trans (le_self_add.trans le_self_add)
  have hEle : E ≤ E * ω := le_mul_of_one_le_right' one_lt_omega0.le
  exact le1R_of_le hEle hle hL.1

/-- **The converse**: `E ≤₁ E·(n+1)` in `R₁⁺` (`1 ≤ n < ω`) ⇒ `E ∈ range φ(n, ·)`. -/
theorem gq_le1R_veb {E : Ordinal.{0}} (hE : InE E) (hxE : x < E) (hEG : E < lgG x) {n : ℕ} (hn : 1 ≤ n)
    (hR : le1R E (E * ((n : Ordinal.{0}) + 1))) : LuP n E := by
  obtain ⟨q, r, hq1, hqT, hqΩ, hrT, hr1, rfl⟩ := gq_th_rep hx hx1 hE hxE hEG
  refine (gq_veb_level hx hx1 hq1 hqT hqΩ hrT hr1 (by exact_mod_cast hn)).2 ?_
  by_contra hlt
  push Not at hlt
  obtain ⟨hL, hζ, -, -⟩ := gq_lh_th hx hx1 hq1 hqT hqΩ hrT hr1
  set E := vt x (Om1 * q + r)
  have hqω : q < ω := hlt.trans (natCast_lt_omega0 n)
  have h1 := lu_luL_fin_lt hqω hζ
  have h2 : E * q + E + E ≤ E * ((n : Ordinal.{0}) + 1) := by
    obtain ⟨m, rfl⟩ := lt_omega0.1 hqω
    have hmn : m + 1 ≤ n := by exact_mod_cast Order.add_one_le_of_lt hlt
    rw [← mul_add_one, ← mul_add_one]
    refine mul_le_mul_left' ?_ E
    exact_mod_cast (Nat.add_le_add_right hmn 1 : m + 1 + 1 ≤ n + 1)
  exact absurd (hL.2 _ hR) (not_le.2 (h1.trans_le h2))

/-- **THE LEVEL TEST at every finite Veblen level `n ≥ 1`**: for an `ε`-number `E ∈ (x, Γ_{x+1})`,
`E ∈ range φ(n, ·) ⇔ E ≤₁ E·(n+1)` in `R₁⁺`. -/
theorem gq_veb_iff_le1R {E : Ordinal.{0}} (hE : InE E) (hxE : x < E) (hEG : E < lgG x) {n : ℕ} (hn : 1 ≤ n) :
    LuP n E ↔ le1R E (E * ((n : Ordinal.{0}) + 1)) :=
  ⟨gq_veb_le1R hx hx1 hE hxE hEG hn, gq_le1R_veb hx hx1 hE hxE hEG hn⟩

end Base

/-! ## Lemma IMG at every finite Veblen level: the source atom and the copy -/

/-- **The source at level `n`**: inside a restart block, an `ε`-number `E ∈ (ρ, Γ_{ρ+1}) ∩ range φ(n, ·)` with
`E·(n+1) ≤ δ` has `E ≤₁ E·(n+1)` in `R₂^C`. -/
theorem gq_src_level {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ) {E : Ordinal.{0}} (hE : InE E) (hρE : ρ < E)
    (hEG : E < lgG ρ) {n : ℕ} (hn : 1 ≤ n) (hP : LuP n E) (hδ : E * ((n : Ordinal.{0}) + 1) ≤ δ) :
    le1 E (E * ((n : Ordinal.{0}) + 1)) :=
  (h.lowδ _ _ hρE hδ).2 (gq_veb_le1R h.ρE h.ρ1 hE hρE hEG hn hP)

/-- The copy of `E·(k+1)`: `f(E·(k+1)) = f(E)·(k+1)` when the partial products lie in the domain. -/
theorem gq_img_mul {ρ : Ordinal.{0}} {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f)
    {E : Ordinal.{0}} (hA : ∀ k : ℕ, E * ((k : Ordinal.{0}) + 1) ∈ A) :
    ∀ k : ℕ, f (E * ((k : Ordinal.{0}) + 1)) = f E * ((k : Ordinal.{0}) + 1)
  | 0 => by simp
  | k + 1 => by
    have e : E * (((k + 1 : ℕ) : Ordinal.{0}) + 1) = E * ((k : Ordinal.{0}) + 1) + E := by
      push_cast; rw [mul_add_one (a := E) (b := (k : Ordinal.{0}) + 1)]
    have hEA : E ∈ A := by have := hA 0; simpa using this
    have h1 := C.add _ (hA k) _ hEA _ (hA (k + 1)) e.symm
    rw [← h1, gq_img_mul C hA k]
    push_cast
    rw [mul_add_one (a := f E) (b := (k : Ordinal.{0}) + 1)]

/-- **THE COPY AT LEVEL `n`** (Lemma IMG, target side, generalizing `Gk.gk_img_inE` from level `1`): if
`E ≤₁ E·(n+1)` in `R₂^C` and the products `E·(k+1)` lie in the domain of the copy `f`, then `f(E) ∈ range φ(n, ·)`. -/
theorem gq_img_level {ρ : Ordinal.{0}} {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f)
    {E : Ordinal.{0}} (hA : ∀ k : ℕ, E * ((k : Ordinal.{0}) + 1) ∈ A) {n : ℕ} (hn : 1 ≤ n)
    (hsrc : le1 E (E * ((n : Ordinal.{0}) + 1))) (hpos : 0 < f E) : LuP n (f E) := by
  have hEA : E ∈ A := by have := hA 0; simpa using this
  have himg : le1 (f E) (f E * ((n : Ordinal.{0}) + 1)) := by
    have := C.cov1 _ hEA _ (hA n) hsrc
    rwa [gq_img_mul C hA n] at this
  have hR : le1R (f E) (f E * ((n + 1 : ℕ) : Ordinal.{0})) := by
    push_cast
    by_cases hU : UpsPt (f E)
    · exact hU.2 _ (le_mul_of_one_le_right' le_add_self)
    · exact (C.sk _ (C.low _ hEA) hU _).1 himg
  exact vz_le1R_level n hn _ hpos hR

/-- **LEMMA IMG AT LEVEL `n`, in one statement**: inside a restart block, the copy of an `ε`-number
`E ∈ (ρ, Γ_{ρ+1}) ∩ range φ(n, ·)` (with `E·(n+1) ≤ δ`, the products in the domain) lies in `range φ(n, ·)`. -/
theorem gq_img_veb {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ) {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}}
    (C : ImgCtx ρ A f) {E : Ordinal.{0}} (hE : InE E) (hρE : ρ < E) (hEG : E < lgG ρ) {n : ℕ} (hn : 1 ≤ n)
    (hP : LuP n E) (hδ : E * ((n : Ordinal.{0}) + 1) ≤ δ) (hA : ∀ k : ℕ, E * ((k : Ordinal.{0}) + 1) ∈ A)
    (hpos : 0 < f E) : LuP n (f E) :=
  gq_img_level C hA hn (gq_src_level h hE hρE hEG hn hP hδ) hpos

end Googology.Trans.PoR.InaccPsi.R2.Gq
