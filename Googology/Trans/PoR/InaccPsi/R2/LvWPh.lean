import Googology.Trans.PoR.InaccPsi.R2.LvWLev

/-!
# `lvwSys` has terms for every code below `φ(Ω₁·ω, 0)`, and its frontier lies below `L(0)`

For a strongly critical base `y < Ω₁` (the level lemma `lvPhLev` of `R2.LvPh` holds at every level `β ∈ Tʸ ∩ Ω₁`
below the members of `P_β` above `y`):

* `lvwC k a := Ω₁·(k+1) + a` (the code of the level `y·(k+1) + a`), `lvwTh_C` (`Θ_y(Ω₁·(k+1) + a) = y·(k+1) + a`),
  `lvwTh_veblen_lvl`, `lvwIndCode` (**the index of a code is a code**, for a level `Ω₁·(k+1) + a`, `a < Z`);
* `lvwTc := φ(Ω₁·ω, 0)` (the code of the top), `lvwTh_T` (**`Θ_y(φ(Ω₁·ω, 0)) = φ(y·ω, 0) = ϑʸ(Ω₁·(y·ω))`**),
  `lvwPoly` (**`GgPoly lvwSys lvwTc`**: a code `c < φ(Ω₁·ω, 0)` is a constant, `Ω₁`, a sum, a power, `φ_a(b)` with a
  constant level `1 ≤ a < Z` (the term `th0 a t`), or `φ_{Ω₁·(k+1)+a}(b)` with `a < Z` (the term `th k a t`));
* `lvw_fr` (**`Λ⁺(lvwSys) ≤ ι(ω^{φ(Ω₁·ω,0)}·ω) < L(0)`, `υ_{Λ⁺(lvwSys)} < L(0)`**), `lvw_fr_order`.

No new axiom beyond `R2.CitedLu` and `R2.CitedLv`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ph Lu

/-- The code `Ω₁·(k+1) + a` of the level `y·(k+1) + a`. -/
noncomputable def lvwC (k : ℕ) (a : Ordinal.{0}) : Ordinal.{0} := Om 1 * ((k : Ordinal.{0}) + 1) + a

theorem lvwL_zero (y : Ordinal.{0}) : lvwL y 0 0 = y := by
  unfold lvwL; rw [Nat.cast_zero, zero_add, mul_one, add_zero]

theorem lvwL_ge {y : Ordinal.{0}} (k : ℕ) (a : Ordinal.{0}) : y ≤ lvwL y k a := by
  unfold lvwL
  calc y = y * 1 := (mul_one y).symm
    _ ≤ y * ((k : Ordinal.{0}) + 1) := mul_le_mul_right le_add_self y
    _ ≤ _ := le_self_add

theorem lvwC_ge (k : ℕ) (a : Ordinal.{0}) : Om 1 ≤ lvwC k a := lvwL_ge (y := Om 1) k a

theorem lvwL_gt {y : Ordinal.{0}} (hy : 0 < y) {k : ℕ} {a : Ordinal.{0}} (hka : ¬ (k = 0 ∧ a = 0)) :
    y < lvwL y k a := by
  unfold lvwL
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have ha : a ≠ 0 := fun h => hka ⟨rfl, h⟩
    rw [Nat.cast_zero, zero_add, mul_one]
    exact lt_add_of_pos_right y (pos_iff_ne_zero.2 ha)
  · have h2 : y < y * ((k : Ordinal.{0}) + 1) := by
      calc y = y * 1 := (mul_one y).symm
        _ < y * ((k : Ordinal.{0}) + 1) := (mul_lt_mul_iff_right₀ hy).2
          (by exact_mod_cast Nat.lt_add_of_pos_left hk)
    exact h2.trans_le le_self_add

/-- Between `y` and `y·ω` no ordinal is additive principal (`y` an `ε`-number). -/
theorem lvw_not_indec {y β : Ordinal.{0}} (hy : InE y) (hyβ : y < β) (hβ : β < y * ω) : ¬ Indec β := by
  intro hI
  obtain ⟨e, rfl⟩ := indec_eq_opow hI
  have hy' : ω ^ y = y := hy
  have h1 : y < e := by
    rw [← hy'] at hyβ; exact (opow_lt_opow_iff_right one_lt_omega0).1 hyβ
  have h2 : e < y + 1 := by
    have e2 : y * ω = ω ^ (y + 1) := by rw [opow_add, opow_one, hy']
    rw [e2] at hβ; exact (opow_lt_opow_iff_right one_lt_omega0).1 hβ
  exact absurd (Order.lt_add_one_iff.1 h2) (not_le.2 h1)

section Codes

variable {Z : Ordinal.{0}}

theorem lvwC_cl {k : ℕ} {a : Ordinal.{0}} (hZ : SC Z) (ha : a < Z) : GgCl Z (lvwC k a) := by
  have := GgCl.mul_nat hZ.1 GgCl.om (k + 1)
  rw [Nat.cast_succ] at this
  exact GgCl.add this (GgCl.small ha)

theorem lvwTh_mulnat {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) :
    ∀ n : ℕ, ggTh y (Om 1 * (n : Ordinal.{0})) = y * (n : Ordinal.{0})
  | 0 => by rw [Nat.cast_zero, mul_zero, mul_zero, phTh_zero]
  | n + 1 => by
      rw [Nat.cast_succ, mul_add_one, mul_add_one,
        ggTh_add hy (GgCl.mul_nat hy.1 GgCl.om n), ggTh_Om1 hy hy1, lvwTh_mulnat hy hy1 n]

/-- `Θ_y(Ω₁·(k+1) + a) = y·(k+1) + a` for `a < y`. -/
theorem lvwTh_C {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) (k : ℕ) {a : Ordinal.{0}} (ha : a < y) :
    ggTh y (lvwC k a) = lvwL y k a := by
  have hc := GgCl.mul_nat hy.1 GgCl.om (k + 1)
  rw [Nat.cast_succ] at hc
  unfold lvwC lvwL
  rw [ggTh_add hy hc, ggTh_small ha.le, ← Nat.cast_succ, lvwTh_mulnat hy hy1, Nat.cast_succ]

/-- `φ_{Ω₁·(k+1)+a}` read over `y`: `Θ_y(φ_{Ω₁·(k+1)+a}(b)) = φ_{y·(k+1)+a}(Θ_y(b))` for `a < y`. -/
theorem lvwTh_veblen_lvl {y a b : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) (k : ℕ) (ha : a < y)
    (hb : GgCl y b) : ggTh y (veblen (lvwC k a) b) = veblen (lvwL y k a) (ggTh y b) := by
  rw [phTh_phi hy _ (lvwC_cl hy ha) b hb, lvwTh_C hy hy1 k ha]

/-- **The index of a code is a code** (a level `Ω₁·(k+1) + a`, `a < Z`). -/
theorem lvwIndCode (hZ : SC Z) (k : ℕ) {a b : Ordinal.{0}} (haZ : a < Z) (hb : GgCl Z b)
    (hb0 : k = 0 → a = 0 → 0 < b) (hbv : b < veblen (lvwC k a) b) :
    ∃ d, GgCl Z d ∧ d ≤ b ∧ ∀ y, SC y → y < Om 1 → Z ≤ y → ggTh y d = lvInd (lvwL y k a) y (ggTh y b) := by
  have ha : GgCl Z (lvwC k a) := lvwC_cl hZ haZ
  have ha1 : GgCl Z (lvwC k a + 1) := GgCl.add ha (GgCl.small (gg_one_lt_of_SC hZ))
  have hq : GgCl Z (veblen (lvwC k a + 1) 0) := GgCl.phi ha1 (GgCl.zero hZ.1)
  have hqP : LuP (lvwC k a + 1) (veblen (lvwC k a + 1) 0) := luP_veblen _ _
  have hThq : ∀ y, SC y → y < Om 1 → Z ≤ y → ggTh y (veblen (lvwC k a + 1) 0) = veblen (lvwL y k a + 1) 0 :=
    fun y hy hy1 hZy => by
      rw [phTh_phi hy _ (ha1.mono hZy) _ (GgCl.zero hy.1), ggTh_add hy (ha.mono hZy),
        lvwTh_C hy hy1 k (haZ.trans_le hZy), ggTh_small (gg_one_lt_of_SC hy).le, phTh_zero]
  have hPy : ∀ y v, LuP (lvwL y k a + 1) v → veblen (lvwL y k a + 1) 0 ≤ v := by
    intro y v hv
    obtain ⟨γ, rfl⟩ := hv
    exact veblen_le_veblen_iff_right.2 zero_le
  rcases lt_or_ge b (veblen (lvwC k a + 1) 0) with hbq | hbq
  · -- below the first member of `P_{Ω₁+a+1}`: no member of `P_{y+a+1}` below `Θ_y(b)`
    have hnoP : ∀ y, SC y → y < Om 1 → Z ≤ y → ∀ z, z < ggTh y b → ¬ LuP (lvwL y k a + 1) z := by
      intro y hy hy1 hZy z hz hP
      have h1 := ggTh_lt (hb.mono hZy) hbq (y := y)
      rw [hThq y hy hy1 hZy] at h1
      exact absurd (hPy y z hP) (not_le.2 (hz.trans h1))
    by_cases hka : k = 0 ∧ a = 0
    · have hb0' := hb0 hka.1 hka.2
      have hb1 : 1 ≤ b := one_le_iff_pos.2 hb0'
      refine ⟨b - 1, (ggDec hZ b hb).1 1 (GgCl.small (gg_one_lt_of_SC hZ)) hb1, Ordinal.sub_le_self _ _,
        fun y hy hy1 hZy => ?_⟩
      have hbe : ggTh y b = 1 + ggTh y (b - 1) := by
        conv_lhs => rw [← Ordinal.add_sub_cancel_of_le hb1]
        rw [ggTh_add hy (GgCl.small (gg_one_lt_of_SC hy)), ggTh_small (gg_one_lt_of_SC hy).le]
      have hn := hnoP y hy hy1 hZy
      obtain ⟨rfl, rfl⟩ := hka
      rw [lvwL_zero] at hn ⊢
      rw [hbe]
      refine (lvInd_low_eq hy.veblen_zero fun z hz => hn (1 + z) ?_).symm
      rw [hbe]
      exact (add_lt_add_iff_left 1).2 hz
    · refine ⟨b, hb, le_rfl, fun y hy hy1 hZy => ?_⟩
      have hy0 : y < veblen (lvwL y k a) 0 := by
        calc y = veblen y 0 := hy.veblen_zero.symm
          _ < veblen (lvwL y k a) 0 := veblen_zero_lt_veblen_zero.2 (lvwL_gt hy.1 hka)
      exact (lvInd_low_gt hy0 (hnoP y hy hy1 hZy)).symm
  · have hqb : veblen (lvwC k a + 1) 0 < b := lt_of_le_of_ne hbq fun e => by
      have h1 : veblen (lvwC k a) (veblen (lvwC k a + 1) 0) = veblen (lvwC k a + 1) 0 :=
        veblen_veblen_of_lt (lt_add_one _) _
      rw [← e] at hbv; rw [h1] at hbv; exact lt_irrefl _ hbv
    obtain ⟨c, n, hc, hdc, hbc, hθc⟩ := phSplit hZ b hb
    have hqc : veblen (lvwC k a + 1) 0 ≤ c := by
      by_contra hlt
      push Not at hlt
      have key : c + n < veblen (lvwC k a + 1) 0 + (0 : ℕ) := by
        obtain ⟨u, rfl⟩ := hdc
        obtain ⟨u', hu'⟩ := lu_P_dvd hqP
        rw [hu'] at hlt ⊢
        have hu : u < u' := (mul_lt_mul_iff_right₀ omega0_pos).1 hlt
        calc ω * u + n < ω * u + ω := (add_lt_add_iff_left _).2 (natCast_lt_omega0 n)
          _ = ω * (u + 1) := by rw [mul_add_one]
          _ ≤ ω * u' := by gcongr; exact Order.add_one_le_of_lt hu
          _ ≤ ω * u' + ((0 : ℕ) : Ordinal.{0}) := le_self_add
      rw [Nat.cast_zero, add_zero, ← hbc] at key
      exact absurd hqb (not_lt.2 key.le)
    have hc1 : Om 1 < c := by
      refine lt_of_lt_of_le ?_ hqc
      calc Om 1 = veblen (Om 1) 0 := ph_SC_Om1.veblen_zero.symm
        _ < veblen (lvwC k a + 1) 0 :=
          veblen_zero_lt_veblen_zero.2 ((lvwC_ge k a).trans_lt (lt_add_one _))
    have hThp : ∀ y, SC y → y < Om 1 → Z ≤ y → y < ggTh y c := fun y hy hy1 hZy => by
      have := ggTh_lt (GgCl.om (Z := y)) hc1 (y := y); rwa [ggTh_Om1 hy hy1] at this
    by_cases hfa : veblen (lvwC k a) c = c
    · -- `b = c + n`, `c ∈ P_{Ω₁+a+1}`: `d = c + (n - 1)`
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [Nat.cast_zero, add_zero] at hbc
        rw [hbc, hfa] at hbv; exact lt_irrefl _ hbv
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      refine ⟨c + m, GgCl.add hc (ph_cl_nat hZ m), ?_, fun y hy hy1 hZy => ?_⟩
      · rw [hbc]; exact (add_le_add_iff_left _).2 (by exact_mod_cast Nat.le_succ m)
      · have hcy := hc.mono hZy
        have hP : LuP (lvwL y k a + 1) (ggTh y c) := by
          refine luP_succ.2 ?_
          rw [← lvwTh_veblen_lvl hy hy1 k (haZ.trans_le hZy) hcy, hfa]
        have e : ggTh y b = ggTh y c + 1 + m := by
          rw [hbc, phTh_add_nat hy hcy, add_assoc]; congr 1; exact_mod_cast Nat.add_comm m 1
        rw [phTh_add_nat hy hcy, e, lvInd_above hP (hThp y hy hy1 hZy) fun z hz => ?_]
        obtain ⟨j, rfl⟩ := lt_omega0.1 (hz.trans (natCast_lt_omega0 m))
        exact lu_P_nat_not _ j
    · -- otherwise `d = b`
      refine ⟨b, hb, le_rfl, fun y hy hy1 hZy => ?_⟩
      have hcy := hc.mono hZy
      have hby := hb.mono hZy
      have hay : a < y := haZ.trans_le hZy
      set β := ggTh y b with hβ
      have hβP : ¬ LuP (lvwL y k a + 1) β := by
        intro hP
        have h1 := ggTh_lt hby hbv
        rw [lvwTh_veblen_lvl hy hy1 k hay hby, ← hβ, luP_succ.1 hP] at h1
        exact lt_irrefl _ h1
      set s := {v | LuP (lvwL y k a + 1) v ∧ v < β} with hs
      have hqs : ggTh y (veblen (lvwC k a + 1) 0) ∈ s :=
        ⟨by rw [hThq y hy hy1 hZy]; exact luP_veblen _ _, ggTh_lt (hq.mono hZy) hqb⟩
      have hne : s.Nonempty := ⟨_, hqs⟩
      have hbdd : BddAbove s := ⟨β, fun v hv => hv.2.le⟩
      have hpP : LuP (lvwL y k a + 1) (sSup s) := by
        refine luP_succ.2 ?_
        rw [(isNormal_veblen (lvwL y k a)).map_sSup hne hbdd]
        congr 1
        ext v
        constructor
        · rintro ⟨w, hw, rfl⟩; rw [luP_succ.1 hw.1]; exact hw
        · intro hv; exact ⟨v, hv, luP_succ.1 hv.1⟩
      have hpβ : sSup s < β :=
        lt_of_le_of_ne (csSup_le hne fun v hv => hv.2.le) fun e => hβP (e ▸ hpP)
      have hyp : y < sSup s := by
        refine lt_of_lt_of_le ?_ (le_csSup hbdd hqs)
        rw [hThq y hy hy1 hZy]
        calc y = veblen y 0 := hy.veblen_zero.symm
          _ < veblen (lvwL y k a + 1) 0 :=
            veblen_zero_lt_veblen_zero.2 ((lvwL_ge k a).trans_lt (lt_add_one _))
      set p := sSup s with hp
      have hδ : p + 1 + (β - (p + 1)) = β := Ordinal.add_sub_cancel_of_le (Order.add_one_le_of_lt hpβ)
      have hgap : ∀ z < β - (p + 1), ¬ LuP (lvwL y k a + 1) (p + 1 + z) := by
        intro z hz hP
        have h1 : p + 1 + z < β := by
          calc p + 1 + z < p + 1 + (β - (p + 1)) := (add_lt_add_iff_left _).2 hz
            _ = β := hδ
        have h2 := le_csSup hbdd (show p + 1 + z ∈ s from ⟨hP, h1⟩)
        exact absurd h2 (not_le.2 ((lt_add_one p).trans_le le_self_add))
      have hω : ω ≤ β - (p + 1) := by
        by_contra hlt
        push Not at hlt
        obtain ⟨j, hj⟩ := lt_omega0.1 hlt
        have e1 : ggTh y c + (n : Ordinal.{0}) = p + ((1 + j : ℕ) : Ordinal.{0}) := by
          rw [← phTh_add_nat hy hcy, ← hbc, ← hβ, ← hδ, hj, add_assoc]; push_cast; rfl
        obtain ⟨e2, -⟩ := phSplit_uniq (hθc y hy hy1 hZy) (lu_P_dvd hpP) e1
        apply hfa
        refine phTh_inj (GgCl.phi (lvwC_cl hy hay) hcy) hcy ?_
        rw [lvwTh_veblen_lvl hy hy1 k hay hcy, e2]
        exact luP_succ.1 hpP
      conv_rhs => rw [← hδ]
      rw [lvInd_above hpP hyp hgap]
      conv_lhs => rw [← hδ]
      rw [add_assoc p 1, one_add_of_omega0_le hω]

/-- **The code of the top**: `φ(Ω₁·ω, 0)`. -/
noncomputable def lvwTc : Ordinal.{0} := veblen (Om 1 * ω) 0

theorem lvw_Om1w_eq : Om (1 : Ordinal.{0}) * ω = ω ^ (Om (1 : Ordinal.{0}) + 1) := by
  rw [opow_add, opow_one, gg_SC_eps ph_SC_Om1]

theorem lvw_cl_T (hZ : SC Z) : GgCl Z lvwTc := by
  unfold lvwTc
  rw [lvw_Om1w_eq]
  exact GgCl.phi (GgCl.opow hZ.1 (ph_cl_Om1_one hZ)) (GgCl.zero hZ.1)

theorem lvw_Om1_le_T : Om 1 ≤ lvwTc := (Ordinal.le_mul_left _ omega0_pos).trans (left_le_veblen _ _)

theorem lvw_T_lt_Gam : lvwTc < ggGam := by
  have h1 : Om 1 + 1 < ggGam := ggGam_spec.1.add_one_lt ggGam_spec.2
  have h2 : Om 1 * ω < ggGam := by
    rw [lvw_Om1w_eq, ← veblen_zero_apply]
    exact ggGam_spec.1.2 0 ggGam_spec.1.1 _ h1
  exact ggGam_spec.1.2 _ h2 _ ggGam_spec.1.1

/-- **`Θ_y(φ(Ω₁·ω, 0)) = φ(y·ω, 0) = ϑʸ(Ω₁·(y·ω))`** for a strongly critical `y < Ω₁`. -/
theorem lvwTh_T {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) : ggTh y lvwTc = lvwTop y := by
  have hyE : InE y := gg_SC_eps hy
  have hy1' : y < Om1 := by rw [ph_Om1_eq]; exact hy1
  have hw : ggTh y (Om 1 * ω) = y * ω := by
    rw [lvw_Om1w_eq, ggTh_opow hy (ph_cl_Om1_one hy), phTh_Om1_one hy hy1, opow_add, opow_one,
      show ω ^ y = y from hyE]
  have hwcl : GgCl y (Om 1 * ω) := by rw [lvw_Om1w_eq]; exact GgCl.opow hy.1 (ph_cl_Om1_one hy)
  unfold lvwTc
  rw [phTh_phi hy _ hwcl _ (GgCl.zero hy.1), hw, phTh_zero]
  apply le_antisymm
  · obtain ⟨j, hj⟩ := lvw_top_P hyE hy1'
    rw [← hj]
    exact (veblen_le_veblen_iff_right).2 zero_le
  · refine lvw_top_least hyE hy1' (luP_veblen (y * ω) 0) ?_
    calc y = veblen y 0 := hy.veblen_zero.symm
      _ < veblen (y * ω) 0 := veblen_zero_lt_veblen_zero.2 (by
          calc y = y * 1 := (mul_one y).symm
            _ < y * ω := (mul_lt_mul_iff_right₀ hy.1).2 one_lt_omega0)

/-- **`lvwSys` has terms for every code below `φ(Ω₁·ω, 0)`.** -/
theorem lvwPoly : GgPoly lvwSys lvwTc := by
  refine phPoly_of_SC fun Z hZ _ => ?_
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hcB
  rcases lt_trichotomy c (Om 1) with hc1 | hc1 | hc1
  · have hcZ : c < Z := hc.lt_of_lt_Om1 hZ hc1
    exact ⟨LvWT.cst c, fun y _ _ hZy =>
      ⟨lt_of_lt_of_le hcZ hZy, by show c = ggTh y c; rw [ggTh_small (hcZ.le.trans hZy)]⟩⟩
  · subst hc1
    exact ⟨LvWT.bs, fun y hy hy1 _ => ⟨trivial, by show y = ggTh y (Om 1); rw [ggTh_Om1 hy hy1]⟩⟩
  have hc0 : c ≠ 0 := (lt_of_le_of_lt zero_le hc1).ne'
  obtain ⟨hsub, hlog⟩ := ggDec hZ c hc
  have hw : GgCl Z (ω ^ log ω c) := GgCl.opow hZ.1 hlog
  have hwc : ω ^ log ω c ≤ c := opow_log_le_self ω hc0
  rcases hwc.lt_or_eq with hwc' | hwc'
  · have hr := hsub _ hw hwc
    have hcr : ω ^ log ω c + (c - ω ^ log ω c) = c := Ordinal.add_sub_cancel_of_le hwc
    have hrc : c - ω ^ log ω c < c := by
      rcases (Ordinal.sub_le_self c (ω ^ log ω c)).lt_or_eq with h | h
      · exact h
      · exfalso
        have h1 : ω ^ log ω c + c = c := by conv_rhs => rw [← hcr]
                                            rw [h]
        have h2 := add_eq_right_iff_mul_omega0_le.1 h1
        rw [← opow_succ] at h2
        exact absurd (lt_opow_succ_log_self one_lt_omega0 c) (not_lt.2 h2)
    obtain ⟨s1, hs1⟩ := IH _ hwc' hw (hwc'.trans hcB)
    obtain ⟨s2, hs2⟩ := IH _ hrc hr (hrc.trans hcB)
    refine ⟨LvWT.sm s1 s2, fun y hy hy1 hZy => ?_⟩
    obtain ⟨c1, v1⟩ := hs1 y hy hy1 hZy
    obtain ⟨c2, v2⟩ := hs2 y hy hy1 hZy
    refine ⟨⟨c1, c2⟩, ?_⟩
    show lvwSys.val s1 y + lvwSys.val s2 y = _
    rw [v1, v2, ← ggTh_add hy (hw.mono hZy), hcr]
  rcases (log_le_self ω c).lt_or_eq with hL | hL
  · obtain ⟨s, hs⟩ := IH _ hL hlog (hL.trans hcB)
    refine ⟨LvWT.pw s, fun y hy hy1 hZy => ?_⟩
    obtain ⟨c1, v1⟩ := hs y hy hy1 hZy
    refine ⟨c1, ?_⟩
    show ω ^ lvwSys.val s y = _
    rw [v1, ← ggTh_opow hy (hlog.mono hZy), hwc']
  have hcE : ω ^ c = c := by conv_lhs => rw [← hL]
                             exact hwc'
  have hdec : veblen (invVeblen₁ c) (invVeblen₂ c) = c := by rw [veblen_invVeblen₁_invVeblen₂, hcE]
  have hb1 : invVeblen₂ c < c := by have := invVeblen₂_lt c; rwa [hcE] at this
  obtain ⟨ha, hb⟩ := phDec hZ.1 hc _ _ hdec hb1
  set a := invVeblen₁ c with hadef
  set b := invVeblen₂ c with hbdef
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, veblen_zero_apply] at hdec
    have e := hcE
    rw [← hdec] at e
    have e2 := (opow_right_inj one_lt_omega0).1 e
    rw [← hdec, e2] at hb1
    exact lt_irrefl _ hb1
  have hSC1 := ph_SC_Om1
  have haOO : a < Om 1 * ω := by
    have hlt : veblen a b < veblen (Om 1 * ω) 0 := by rw [hdec]; exact hcB
    rcases veblen_lt_veblen_iff.1 hlt with ⟨_, hb'⟩ | ⟨h', _⟩ | ⟨_, h'⟩
    · exact absurd hb' (not_lt.2 zero_le)
    · exact h'
    · exact absurd h' (not_lt.2 zero_le)
  have hbv : b < veblen a b := by rw [hdec]; exact hb1
  rcases lt_or_ge a (Om 1) with haO | haO
  · have haZ : a < Z := ha.lt_of_lt_Om1 hZ haO
    have ha1 : 1 ≤ a := one_le_iff_ne_zero.2 ha0
    have hbO : Om 1 < b := by
      by_contra hle
      push Not at hle
      have h3 := (veblen_le_veblen_iff_right (o := a)).2 hle
      rw [hdec, hSC1.veblen_right haO] at h3
      exact absurd hc1 (not_lt.2 h3)
    obtain ⟨d, hd, hdb, hdθ⟩ := luIndCode hZ haZ hb hbO hbv
    obtain ⟨t, ht⟩ := IH d (hdb.trans_lt hb1) hd ((hdb.trans_lt hb1).trans hcB)
    refine ⟨LvWT.th0 a t, fun y hy hy1 hZy => ?_⟩
    obtain ⟨ct, vt'⟩ := ht y hy hy1 hZy
    have hy1' : y < Om1 := by rw [ph_Om1_eq]; exact hy1
    have hay : a < y := haZ.trans_le hZy
    refine ⟨⟨ha1, hay, ct⟩, ?_⟩
    show vt y (Om1 * a + lvwSys.val t y) = ggTh y c
    have hby := hb.mono hZy
    have hThc : ggTh y c = veblen a (ggTh y b) := by
      rw [← hdec, luTh_veblen_lvl hy hay hby]
    have hyb : y < ggTh y b := by
      have := ggTh_lt (GgCl.om (Z := y)) hbO (y := y); rwa [ggTh_Om1 hy hy1] at this
    have hbP : ¬ LuP (a + 1) (ggTh y b) := by
      intro hP
      have h1 := ggTh_lt hby hbv
      rw [luTh_veblen_lvl hy hay hby, luP_succ.1 hP] at h1
      exact lt_irrefl _ h1
    obtain ⟨htT, htlt⟩ := LvWT.lvw_T (gg_SC_eps hy) hy1' t ct
    have hTv : lvwSys.val t y ∈ Tset y ∧ lvwSys.val t y < Om1 :=
      ⟨htT, htlt.trans (lvwTop_facts (gg_SC_eps hy) hy1').2.2.2.2.1⟩
    have e1 : lvwSys.val t y = luInd a y (ggTh y b) := by rw [vt', hdθ y hy hy1 hZy]
    rw [e1] at hTv ⊢
    rw [hThc, luPhLev hy hy1' ha1 hay _ hyb hbP hTv.1 hTv.2]
  · -- a level `Ω₁·(k+1) + a'`, `a' < Z`: the term `th k a' t`
    have hO0 : Om 1 ≠ 0 := (zero_lt_one.trans (gg_one_lt_of_SC hSC1)).ne'
    have hdm : Om 1 * (a / Om 1) + a % Om 1 = a := div_add_mod a (Om 1)
    have ha'O : a % Om 1 < Om 1 := mod_lt a hO0
    have hqω : a / Om 1 < ω := by
      have h0 : Om 1 * (a / Om 1) ≤ a := by
        calc Om 1 * (a / Om 1) ≤ Om 1 * (a / Om 1) + a % Om 1 := le_self_add
          _ = a := hdm
      exact (mul_lt_mul_iff_right₀ (pos_iff_ne_zero.2 hO0)).1 (h0.trans_lt haOO)
    have hq1 : 1 ≤ a / Om 1 := by
      rcases eq_or_ne (a / Om 1) 0 with h0 | h0
      · rw [h0, mul_zero, zero_add] at hdm
        exact absurd (hdm ▸ ha'O) (not_lt.2 haO)
      · exact one_le_iff_ne_zero.2 h0
    obtain ⟨n, hn⟩ := lt_omega0.1 hqω
    have hn1 : 1 ≤ n := by
      have h : (1 : Ordinal.{0}) ≤ (n : Ordinal.{0}) := hn ▸ hq1
      exact_mod_cast h
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    set a' := a % Om 1 with ha'def
    have hae : lvwC k a' = a := by unfold lvwC; rw [← Nat.cast_succ, ← hn, hdm]
    have hmc : GgCl Z (Om 1 * (a / Om 1)) := by rw [hn]; exact GgCl.mul_nat hZ.1 GgCl.om (k + 1)
    have ha'c : GgCl Z a' := by
      have hle : Om 1 * (a / Om 1) ≤ a := by
        calc Om 1 * (a / Om 1) ≤ Om 1 * (a / Om 1) + a % Om 1 := le_self_add
          _ = a := hdm
      have := (ggDec hZ a ha).1 _ hmc hle
      have e : a - Om 1 * (a / Om 1) = a' := by
        nth_rewrite 1 [← hdm]
        exact Ordinal.add_sub_cancel _ _
      rwa [e] at this
    have ha'Z : a' < Z := ha'c.lt_of_lt_Om1 hZ ha'O
    have hbv' : b < veblen (lvwC k a') b := by rw [hae]; exact hbv
    have hb0 : k = 0 → a' = 0 → 0 < b := by
      intro hk0 ha'0
      rcases eq_or_ne b 0 with hb0 | hb0
      · exfalso
        have e : a = Om 1 := by rw [← hae, hk0, ha'0]; unfold lvwC; rw [Nat.cast_zero, zero_add, mul_one, add_zero]
        rw [e, hb0, hSC1.veblen_zero] at hdec
        rw [← hdec] at hc1
        exact lt_irrefl _ hc1
      · exact pos_iff_ne_zero.2 hb0
    obtain ⟨d, hd, hdb, hdθ⟩ := lvwIndCode hZ k ha'Z hb hb0 hbv'
    obtain ⟨t, ht⟩ := IH d (hdb.trans_lt hb1) hd ((hdb.trans_lt hb1).trans hcB)
    refine ⟨LvWT.th k a' t, fun y hy hy1 hZy => ?_⟩
    obtain ⟨ct, vt'⟩ := ht y hy hy1 hZy
    have hyE : InE y := gg_SC_eps hy
    have hy1' : y < Om1 := by rw [ph_Om1_eq]; exact hy1
    have hay : a' < y := ha'Z.trans_le hZy
    refine ⟨⟨hay, ct⟩, ?_⟩
    show vt y (Om1 * lvwL y k a' + lvwSys.val t y) = ggTh y c
    have hby := hb.mono hZy
    have hThc : ggTh y c = veblen (lvwL y k a') (ggTh y b) := by
      rw [← hdec, ← hae, lvwTh_veblen_lvl hy hy1 k hay hby]
    have hyb : y < veblen (lvwL y k a') (ggTh y b) := by
      by_cases hka : k = 0 ∧ a' = 0
      · rw [hka.1, hka.2, lvwL_zero]
        have hpos : 0 < ggTh y b := by
          have := ggTh_lt (GgCl.zero hy.1) (hb0 hka.1 hka.2) (y := y); rwa [phTh_zero] at this
        calc y = veblen y 0 := hy.veblen_zero.symm
          _ < veblen y (ggTh y b) := (veblen_lt_veblen_iff_right).2 hpos
      · calc y = veblen y 0 := hy.veblen_zero.symm
          _ < veblen (lvwL y k a') 0 := veblen_zero_lt_veblen_zero.2 (lvwL_gt hy.1 hka)
          _ ≤ veblen (lvwL y k a') (ggTh y b) := (veblen_le_veblen_iff_right).2 zero_le
    have hbP : ¬ LuP (lvwL y k a' + 1) (ggTh y b) := by
      intro hP
      have h1 := ggTh_lt hby hbv'
      rw [lvwTh_veblen_lvl hy hy1 k hay hby, luP_succ.1 hP] at h1
      exact lt_irrefl _ h1
    obtain ⟨htT, htlt⟩ := LvWT.lvw_T hyE hy1' t ct
    have hTv : lvwSys.val t y ∈ Tset y ∧ lvwSys.val t y < Om1 :=
      ⟨htT, htlt.trans (lvwTop_facts hyE hy1').2.2.2.2.1⟩
    have e1 : lvwSys.val t y = lvInd (lvwL y k a') y (ggTh y b) := by rw [vt', hdθ y hy hy1 hZy]
    rw [e1] at hTv ⊢
    obtain ⟨hLT, hyL, hLw, hL1⟩ := lvwL_facts hyE hy1' (k := k) hay
    have hβ1 : 1 ≤ lvwL y k a' := (lu_one_lt_E hyE).le.trans hyL
    have hβu : ∀ u, LuP (lvwL y k a') u → y < u → lvwL y k a' < u := by
      intro u hPu hyu
      refine lv_level_lt_P' hβ1 ?_ hPu hyu
      rcases hyL.lt_or_eq with h | h
      · exact Or.inr (lvw_not_indec hyE h hLw)
      · exact Or.inl h.ge
    rw [hThc, lvPhLev hy hy1' hβ1 hLT hL1 hβu _ hyb hbP hTv.1 hTv.2]

end Codes

/-! ## The frontier lies below `L(0)` -/

variable {S : InaccSeq.{0}}

/-- **The frontier of `lvwSys`**: `Λ(lvwSys) ≤ ι(ω^{φ(Ω₁·ω,0)})`, `Λ⁺(lvwSys) ≤ ι(ω^{φ(Ω₁·ω,0)}·ω) < L(0)` and
`υ_{Λ⁺(lvwSys)} < L(0)`. -/
theorem lvw_fr :
    (∀ n : ℕ, XtFr lvwSys (iota S (ω ^ lvwTc * ((n : Ordinal.{0}) + 1))) ∧
      upsilon (iota S (ω ^ lvwTc * ((n : Ordinal.{0}) + 1))) = iota S (ω ^ lvwTc * ((n : Ordinal.{0}) + 1))) ∧
    xtLam lvwSys ≤ iota S (ω ^ lvwTc) ∧ xtB1 lvwSys ≤ iota S (ω ^ lvwTc * ω) ∧
    iota S (ω ^ lvwTc * ω) < Nc.ncL S 0 ∧ upsilon (xtB1 lvwSys) < Nc.ncL S 0 :=
  phFrGen lvw_T_lt_Gam (phPolyR_of lvwPoly) (fun _ hy hy1 => (lvwTh_T hy hy1).symm) (fun _ hZ => lvw_cl_T hZ)
    lvw_Om1_le_T

/-- **Where the frontier lies**: `ρ` of `Λ⁺(lvSys)` < `ρ` of `Λ(lvwSys)` < `ρ` of `Λ⁺(lvwSys)` < `L(0) = m* ≤ L(n+1) <
`L(ω) < L(ω+1)`, and `Λ⁺(lvwSys) < L(ω+1)`, unconditionally. -/
theorem lvw_fr_order (n : ℕ) :
    upsilon (xtB1 lvSys) < upsilon (xtLam lvwSys) ∧ upsilon (xtLam lvwSys) < upsilon (xtB1 lvwSys) ∧
    upsilon (xtB1 lvwSys) < Nc.ncL S 0 ∧ Nc.ncL S 0 ≤ Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ∧
    Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) < Nc.ncL S ω ∧ Nc.ncL S ω < Nc.ncL S (ω + 1) ∧
    xtB1 lvwSys < Nc.ncL S (ω + 1) := by
  obtain ⟨h0, h1, h2⟩ := phL_chain (S := S) n
  have hU := (lvw_fr (S := S)).2.2.2.2
  refine ⟨upsilon_normal.strictMono lvwLam_gt, upsilon_normal.strictMono lvw_lamLtB1, hU, h0, h1, h2, ?_⟩
  exact upsilon_normal.strictMono.le_apply.trans_lt (((hU.trans_le h0).trans h1).trans h2)

end Googology.Trans.PoR.InaccPsi.R2
