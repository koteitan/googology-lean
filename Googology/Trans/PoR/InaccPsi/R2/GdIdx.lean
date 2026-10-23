import Googology.Trans.PoR.InaccPsi.R2.GdFr

/-!
# The index of a code is a code, for the codes with the atoms over the base

The proofs of `R2.GaIdx` (`gxIndCodeU`, `gxIndCodeV`) and of `R2.GaCl.gxSplit` for the codes `GxCl Z (gdAt Z)` of
`R2.GdAt`, whose atoms grow with the base: a code over `Z` is read at every strongly critical `y ≥ Z` with the atoms
over `y` (`gdCl_mono`).

* `gdSplit` (**a code is `a + n`** with `ω ∣ a` and `ω ∣ Θ_y(a)` at every `y ≥ Z`);
* `gdIndCodeU` (**the index of a code is a code**, a constant level `1 ≤ a < Z`), `gdIndCodeV` (**the same for a level
  code `a ≥ Ω₁`**).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph Lu
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Lp
  Googology.Trans.PoR.InaccPsi.R2.Ga

variable {Z : Ordinal.{0}}

/-- **A code is `a + n`** with `a` a code, `ω ∣ a`, `n < ω`, and `ω ∣ Θ_y(a)` at every strongly critical `y ≥ Z`. -/
theorem gdSplit (hZ : SC Z)  : ∀ b, GxCl Z (gdAt Z) b → ∃ a : Ordinal.{0}, ∃ n : ℕ, GxCl Z (gdAt Z) a ∧
    ω ∣ a ∧ b = a + n ∧ ∀ y, SC y → y < Om 1 → Z ≤ y → ω ∣ gxTh y (gdAt y) a := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb
  rcases lt_or_ge b ω with hbω | hbω
  · obtain ⟨n, rfl⟩ := lt_omega0.1 hbω
    exact ⟨0, n, GxCl.zero hZ.1, dvd_zero _, by rw [zero_add], fun y _ _ _ => by
      rw [gxTh_zero]; exact dvd_zero _⟩
  have hb0 : b ≠ 0 := (omega0_pos.trans_le hbω).ne'
  have hL : log ω b ≠ 0 := by
    intro h
    have := lt_opow_succ_log_self one_lt_omega0 b
    rw [h, Order.succ_eq_add_one, zero_add, opow_one] at this
    exact absurd hbω (not_le.2 this)
  obtain ⟨hsub, hlog⟩ := gxDec hZ (gdAt_GxAt Z) b hb
  have hw : GxCl Z (gdAt Z) (ω ^ log ω b) := GxCl.opow hZ.1 hlog
  have hwb : ω ^ log ω b ≤ b := opow_log_le_self ω hb0
  have hr := hsub _ hw hwb
  have hbr : ω ^ log ω b + (b - ω ^ log ω b) = b := Ordinal.add_sub_cancel_of_le hwb
  rcases eq_or_ne (b - ω ^ log ω b) 0 with h0 | h0
  · rw [h0, add_zero] at hbr
    refine ⟨b, 0, hb, hbr ▸ ph_omega_dvd_opow hL, by rw [Nat.cast_zero, add_zero], fun y hy hy1 hZy => ?_⟩
    rw [← hbr, gxTh_opow hy (gdAt_GxAt y) (gdCl_mono hZy hlog)]
    exact ph_omega_dvd_opow (gx_ne_zero hy hL)
  · have hrb : b - ω ^ log ω b < b := by
      rcases (Ordinal.sub_le_self b (ω ^ log ω b)).lt_or_eq with h | h
      · exact h
      · exfalso
        have h1 : ω ^ log ω b + b = b := by conv_rhs => rw [← hbr]
                                            rw [h]
        have h2 := add_eq_right_iff_mul_omega0_le.1 h1
        rw [← opow_succ] at h2
        exact absurd (lt_opow_succ_log_self one_lt_omega0 b) (not_lt.2 h2)
    obtain ⟨a', n, ha', hd', he', hθ'⟩ := IH _ hrb hr
    refine ⟨ω ^ log ω b + a', n, GxCl.add hw ha', dvd_add (ph_omega_dvd_opow hL) hd', ?_,
      fun y hy hy1 hZy => ?_⟩
    · rw [add_assoc, ← he', hbr]
    · rw [gxTh_add hy (gdAt_GxAt y) (gdCl_mono hZy hw), gxTh_opow hy (gdAt_GxAt y) (gdCl_mono hZy hlog)]
      exact dvd_add (ph_omega_dvd_opow (gx_ne_zero hy hL)) (hθ' y hy hy1 hZy)

/-- **The index of a code is a code** (a constant level `1 ≤ a < Z`). -/
theorem gdIndCodeU (hZ : SC Z) {a b : Ordinal.{0}} (haZ : a < Z) (hb : GxCl Z (gdAt Z) b) (hb1 : Om 1 < b)
    (hbv : b < veblen a b) :
    ∃ d, GxCl Z (gdAt Z) d ∧ d ≤ b ∧ ∀ y, SC y → y < Om 1 → Z ≤ y →
      gxTh y (gdAt y) d = luInd a y (gxTh y (gdAt y) b) := by
  have ha1Z : a + 1 < Z := hZ.add_one_lt haZ
  set q := veblen (a + 1) (Om 1 + 1) with hqdef
  have hq : GxCl Z (gdAt Z) q := GxCl.phi (GxCl.small ha1Z) (gx_Om1_one hZ)
  have hqP : LuP (a + 1) q := luP_veblen _ _
  -- facts at every base
  have hThq : ∀ y, SC y → y < Om 1 → Z ≤ y → gxTh y (gdAt y) q = veblen (a + 1) (y + 1) := fun y hy hy1 hZy => by
    rw [gxTh_veblen_lvl hy (gdAt_GxAt y) (ha1Z.trans_le hZy) (gx_Om1_one hy), gxTh_Om1_one hy hy1 (gdAt_GxAt y)]
  have hPy : ∀ y, SC y → Z ≤ y → ∀ v, LuP (a + 1) v → y < v → veblen (a + 1) (y + 1) ≤ v := by
    intro y hy hZy v hv hyv
    obtain ⟨γ, rfl⟩ := hv
    have hky : veblen (a + 1) y = y := hy.veblen_right (ha1Z.trans_le hZy)
    refine veblen_le_veblen_iff_right.2 (Order.add_one_le_of_lt ?_)
    by_contra hle
    push Not at hle
    have := (veblen_le_veblen_iff_right (o := a + 1)).2 hle
    rw [hky] at this
    exact absurd hyv (not_lt.2 this)
  rcases lt_or_ge b q with hbq | hbq
  · -- `b < φ_{a+1}(Ω₁ + 1)`: `d = b - (Ω₁ + 1)`
    have hle : Om 1 + 1 ≤ b := Order.add_one_le_of_lt hb1
    refine ⟨b - (Om 1 + 1), (gxDec hZ (gdAt_GxAt Z) b hb).1 _ (gx_Om1_one hZ) hle, Ordinal.sub_le_self _ _,
      fun y hy hy1 hZy => ?_⟩
    have hbe : gxTh y (gdAt y) b = y + 1 + gxTh y (gdAt y) (b - (Om 1 + 1)) := by
      conv_lhs => rw [← Ordinal.add_sub_cancel_of_le hle]
      rw [gxTh_add hy (gdAt_GxAt y) (gx_Om1_one hy), gxTh_Om1_one hy hy1 (gdAt_GxAt y)]
    rw [hbe, luInd_low]
    intro z hz hP
    have h1 : y + 1 + z < gxTh y (gdAt y) b := by rw [hbe]; exact (add_lt_add_iff_left _).2 hz
    have h2 := hPy y hy hZy _ hP ((lt_add_one y).trans_le le_self_add)
    rw [← hThq y hy hy1 hZy] at h2
    exact absurd (h2.trans_lt h1) (not_lt.2 (gxTh_lt (gdCl_mono hZy hb) hbq).le)
  · have hqb : q < b := lt_of_le_of_ne hbq fun e => by
      have h1 : veblen a q = q := by
        rw [hqdef]; exact veblen_veblen_of_lt (lt_add_one _) _
      rw [← e] at hbv; rw [h1] at hbv; exact lt_irrefl _ hbv
    obtain ⟨c, n, hc, hdc, hbc, hθc⟩ := gdSplit hZ b hb
    have hqc : q ≤ c := by
      by_contra hlt
      push Not at hlt
      have key : c + n < q + (0 : ℕ) := by
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
      exact (lt_add_one _).trans_le (right_le_veblen _ _)
    have hThp : ∀ y, SC y → y < Om 1 → Z ≤ y → y < gxTh y (gdAt y) c := fun y hy hy1 hZy => by
      have := gxTh_lt (GxCl.om (Z := y) (At := gdAt y)) hc1; rwa [gxTh_Om1 hy hy1 (gdAt_GxAt y)] at this
    by_cases hfa : veblen a c = c
    · -- `b = c + n`, `c ∈ P_{a+1}`: `d = c + (n - 1)`
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [Nat.cast_zero, add_zero] at hbc
        rw [hbc, hfa] at hbv; exact lt_irrefl _ hbv
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      refine ⟨c + m, GxCl.add hc (GxCl.small (ph_nat_lt hZ m)), ?_, fun y hy hy1 hZy => ?_⟩
      · rw [hbc]; exact (add_le_add_iff_left _).2 (by exact_mod_cast Nat.le_succ m)
      · have hcy := gdCl_mono hZy hc
        have hP : LuP (a + 1) (gxTh y (gdAt y) c) := by
          refine luP_succ.2 ?_
          rw [← gxTh_veblen_lvl hy (gdAt_GxAt y) (haZ.trans_le hZy) hcy, hfa]
        have e : gxTh y (gdAt y) b = gxTh y (gdAt y) c + 1 + m := by
          rw [hbc, gx_add_nat hy (gdAt_GxAt y) hcy, add_assoc]; congr 1; exact_mod_cast Nat.add_comm m 1
        rw [gx_add_nat hy (gdAt_GxAt y) hcy, e, luInd_above hP (hThp y hy hy1 hZy) fun z hz => ?_]
        obtain ⟨j, rfl⟩ := lt_omega0.1 (hz.trans (natCast_lt_omega0 m))
        exact lu_P_nat_not _ j
    · -- otherwise `d = b`
      refine ⟨b, hb, le_rfl, fun y hy hy1 hZy => ?_⟩
      have hcy := gdCl_mono hZy hc
      have hby := gdCl_mono hZy hb
      have hay : a < y := haZ.trans_le hZy
      set β := gxTh y (gdAt y) b with hβ
      have hβP : ¬ LuP (a + 1) β := by
        intro hP
        have h1 := gxTh_lt hby hbv
        rw [gxTh_veblen_lvl hy (gdAt_GxAt y) hay hby, ← hβ, luP_succ.1 hP] at h1
        exact lt_irrefl _ h1
      set s := {v | LuP (a + 1) v ∧ v < β} with hs
      have hqs : gxTh y (gdAt y) q ∈ s :=
        ⟨by rw [hThq y hy hy1 hZy]; exact luP_veblen _ _, gxTh_lt (gdCl_mono hZy hq) hqb⟩
      have hne : s.Nonempty := ⟨_, hqs⟩
      have hbdd : BddAbove s := ⟨β, fun v hv => hv.2.le⟩
      have hpP : LuP (a + 1) (sSup s) := by
        refine luP_succ.2 ?_
        rw [(isNormal_veblen a).map_sSup hne hbdd]
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
        exact (lt_add_one y).trans_le (right_le_veblen _ _)
      set p := sSup s with hp
      have hδ : p + 1 + (β - (p + 1)) = β := Ordinal.add_sub_cancel_of_le (Order.add_one_le_of_lt hpβ)
      have hgap : ∀ z < β - (p + 1), ¬ LuP (a + 1) (p + 1 + z) := by
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
        have e1 : gxTh y (gdAt y) c + (n : Ordinal.{0}) = p + ((1 + j : ℕ) : Ordinal.{0}) := by
          rw [← gx_add_nat hy (gdAt_GxAt y) hcy, ← hbc, ← hβ, ← hδ, hj, add_assoc]; push_cast; rfl
        obtain ⟨e2, -⟩ := phSplit_uniq (hθc y hy hy1 hZy) (lu_P_dvd hpP) e1
        apply hfa
        refine gx_inj (GxCl.phi (GxCl.small hay) hcy) hcy ?_
        rw [gxTh_veblen_lvl hy (gdAt_GxAt y) hay hcy, e2]
        exact luP_succ.1 hpP
      conv_rhs => rw [← hδ]
      rw [luInd_above hpP hyp hgap]
      conv_lhs => rw [← hδ]
      rw [add_assoc p 1, one_add_of_omega0_le hω]



/-- **The index of a code is a code** (every level code `a ≥ Ω₁`). -/
theorem gdIndCodeV (hZ : SC Z) {a b : Ordinal.{0}} (ha : GxCl Z (gdAt Z) a) (haO : Om 1 ≤ a) (hb : GxCl Z (gdAt Z) b)
    (hb0 : veblen a 0 = a → 0 < b) (hbv : b < veblen a b) :
    ∃ d, GxCl Z (gdAt Z) d ∧ d ≤ b ∧ ∀ y, SC y → y < Om 1 → Z ≤ y →
      gxTh y (gdAt y) d = lpInd (gxTh y (gdAt y) a) y (gxTh y (gdAt y) b) := by
  have hyΘ : ∀ y, SC y → y < Om 1 → Z ≤ y → y ≤ gxTh y (gdAt y) a := fun y hy hy1 hZy => by
    rcases haO.lt_or_eq with h | h
    · have := gxTh_lt (GxCl.om (Z := y) (At := gdAt y)) h; rw [gxTh_Om1 hy hy1 (gdAt_GxAt y)] at this; exact this.le
    · rw [← h, gxTh_Om1 hy hy1 (gdAt_GxAt y)]
  have ha1 : GxCl Z (gdAt Z) (a + 1) := GxCl.add ha (GxCl.small (gg_one_lt_of_SC hZ))
  have hq : GxCl Z (gdAt Z) (veblen (a + 1) 0) := GxCl.phi ha1 (GxCl.zero hZ.1)
  have hqP : LuP (a + 1) (veblen (a + 1) 0) := luP_veblen _ _
  have hThq : ∀ y, SC y → y < Om 1 → Z ≤ y → gxTh y (gdAt y) (veblen (a + 1) 0) = veblen (gxTh y (gdAt y) a + 1) 0 :=
    fun y hy hy1 hZy => by
      rw [gxTh_phi hy (gdAt_GxAt y) _ (gdCl_mono hZy ha1) _ (GxCl.zero hy.1),
        gxTh_add hy (gdAt_GxAt y) (gdCl_mono hZy ha),
        gxTh_small (gg_one_lt_of_SC hy).le, gxTh_zero]
  have hPy : ∀ y v, LuP (gxTh y (gdAt y) a + 1) v → veblen (gxTh y (gdAt y) a + 1) 0 ≤ v := by
    intro y v hv
    obtain ⟨γ, rfl⟩ := hv
    exact veblen_le_veblen_iff_right.2 zero_le
  rcases lt_or_ge b (veblen (a + 1) 0) with hbq | hbq
  · -- below the first member of `P_{Ω₁+a+1}`: no member of `P_{y+a+1}` below `Θ_y(b)`
    have hnoP : ∀ y, SC y → y < Om 1 → Z ≤ y → ∀ z, z < gxTh y (gdAt y) b → ¬ LuP (gxTh y (gdAt y) a + 1) z := by
      intro y hy hy1 hZy z hz hP
      have h1 := gxTh_lt (gdCl_mono hZy hb) hbq
      rw [hThq y hy hy1 hZy] at h1
      exact absurd (hPy y z hP) (not_le.2 (hz.trans h1))
    have hThv : ∀ y, SC y → Z ≤ y → gxTh y (gdAt y) (veblen a 0) = veblen (gxTh y (gdAt y) a) 0 := fun y hy hZy => by
      rw [gxTh_phi hy (gdAt_GxAt y) _ (gdCl_mono hZy ha) _ (GxCl.zero hy.1), gxTh_zero]
    by_cases hka : veblen a 0 = a
    · have hb0' := hb0 hka
      have hb1 : 1 ≤ b := one_le_iff_pos.2 hb0'
      refine ⟨b - 1, (gxDec hZ (gdAt_GxAt Z) b hb).1 1 (GxCl.small (gg_one_lt_of_SC hZ)) hb1, Ordinal.sub_le_self _ _,
        fun y hy hy1 hZy => ?_⟩
      have hbe : gxTh y (gdAt y) b = 1 + gxTh y (gdAt y) (b - 1) := by
        conv_lhs => rw [← Ordinal.add_sub_cancel_of_le hb1]
        rw [gxTh_add hy (gdAt_GxAt y) (GxCl.small (gg_one_lt_of_SC hy)), gxTh_small (gg_one_lt_of_SC hy).le]
      have hn := hnoP y hy hy1 hZy
      have hfix : veblen (gxTh y (gdAt y) a) 0 = gxTh y (gdAt y) a := by rw [← hThv y hy hZy, hka]
      rw [hbe]
      refine (lpInd_low_eq (Or.inr ⟨hfix, hyΘ y hy hy1 hZy⟩) fun z hz => hn (1 + z) ?_).symm
      rw [hbe]
      exact (add_lt_add_iff_left 1).2 hz
    · refine ⟨b, hb, le_rfl, fun y hy hy1 hZy => ?_⟩
      have hav : a < veblen a 0 := lt_of_le_of_ne (left_le_veblen a 0) (Ne.symm hka)
      have hβ0 : gxTh y (gdAt y) a < veblen (gxTh y (gdAt y) a) 0 := by
        rw [← hThv y hy hZy]; exact gxTh_lt (gdCl_mono hZy ha) hav
      exact (lpInd_low_gt ((hyΘ y hy hy1 hZy).trans_lt hβ0) hβ0 (hnoP y hy hy1 hZy)).symm
  · have hqb : veblen (a + 1) 0 < b := lt_of_le_of_ne hbq fun e => by
      have h1 : veblen (a) (veblen (a + 1) 0) = veblen (a + 1) 0 :=
        veblen_veblen_of_lt (lt_add_one _) _
      rw [← e] at hbv; rw [h1] at hbv; exact lt_irrefl _ hbv
    obtain ⟨c, n, hc, hdc, hbc, hθc⟩ := gdSplit hZ b hb
    have hqc : veblen (a + 1) 0 ≤ c := by
      by_contra hlt
      push Not at hlt
      have key : c + n < veblen (a + 1) 0 + (0 : ℕ) := by
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
        _ < veblen (a + 1) 0 :=
          veblen_zero_lt_veblen_zero.2 (haO.trans_lt (lt_add_one _))
    have hThp : ∀ y, SC y → y < Om 1 → Z ≤ y → y < gxTh y (gdAt y) c := fun y hy hy1 hZy => by
      have := gxTh_lt (GxCl.om (Z := y) (At := gdAt y)) hc1; rwa [gxTh_Om1 hy hy1 (gdAt_GxAt y)] at this
    by_cases hfa : veblen (a) c = c
    · -- `b = c + n`, `c ∈ P_{Ω₁+a+1}`: `d = c + (n - 1)`
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [Nat.cast_zero, add_zero] at hbc
        rw [hbc, hfa] at hbv; exact lt_irrefl _ hbv
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      refine ⟨c + m, GxCl.add hc (GxCl.small (ph_nat_lt hZ m)), ?_, fun y hy hy1 hZy => ?_⟩
      · rw [hbc]; exact (add_le_add_iff_left _).2 (by exact_mod_cast Nat.le_succ m)
      · have hcy := gdCl_mono hZy hc
        have hP : LuP (gxTh y (gdAt y) a + 1) (gxTh y (gdAt y) c) := by
          refine luP_succ.2 ?_
          rw [← gxTh_phi hy (gdAt_GxAt y) _ (gdCl_mono hZy ha) _ hcy, hfa]
        have e : gxTh y (gdAt y) b = gxTh y (gdAt y) c + 1 + m := by
          rw [hbc, gx_add_nat hy (gdAt_GxAt y) hcy, add_assoc]; congr 1; exact_mod_cast Nat.add_comm m 1
        rw [gx_add_nat hy (gdAt_GxAt y) hcy, e, lpInd_above hP (hThp y hy hy1 hZy) fun z hz => ?_]
        obtain ⟨j, rfl⟩ := lt_omega0.1 (hz.trans (natCast_lt_omega0 m))
        exact lu_P_nat_not _ j
    · -- otherwise `d = b`
      refine ⟨b, hb, le_rfl, fun y hy hy1 hZy => ?_⟩
      have hcy := gdCl_mono hZy hc
      have hby := gdCl_mono hZy hb
      set β := gxTh y (gdAt y) b with hβ
      have hβP : ¬ LuP (gxTh y (gdAt y) a + 1) β := by
        intro hP
        have h1 := gxTh_lt hby hbv
        rw [gxTh_phi hy (gdAt_GxAt y) _ (gdCl_mono hZy ha) _ hby, ← hβ, luP_succ.1 hP] at h1
        exact lt_irrefl _ h1
      set s := {v | LuP (gxTh y (gdAt y) a + 1) v ∧ v < β} with hs
      have hqs : gxTh y (gdAt y) (veblen (a + 1) 0) ∈ s :=
        ⟨by rw [hThq y hy hy1 hZy]; exact luP_veblen _ _, gxTh_lt (gdCl_mono hZy hq) hqb⟩
      have hne : s.Nonempty := ⟨_, hqs⟩
      have hbdd : BddAbove s := ⟨β, fun v hv => hv.2.le⟩
      have hpP : LuP (gxTh y (gdAt y) a + 1) (sSup s) := by
        refine luP_succ.2 ?_
        rw [(isNormal_veblen (gxTh y (gdAt y) a)).map_sSup hne hbdd]
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
          _ < veblen (gxTh y (gdAt y) a + 1) 0 :=
            veblen_zero_lt_veblen_zero.2 ((hyΘ y hy hy1 hZy).trans_lt (lt_add_one _))
      set p := sSup s with hp
      have hδ : p + 1 + (β - (p + 1)) = β := Ordinal.add_sub_cancel_of_le (Order.add_one_le_of_lt hpβ)
      have hgap : ∀ z < β - (p + 1), ¬ LuP (gxTh y (gdAt y) a + 1) (p + 1 + z) := by
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
        have e1 : gxTh y (gdAt y) c + (n : Ordinal.{0}) = p + ((1 + j : ℕ) : Ordinal.{0}) := by
          rw [← gx_add_nat hy (gdAt_GxAt y) hcy, ← hbc, ← hβ, ← hδ, hj, add_assoc]; push_cast; rfl
        obtain ⟨e2, -⟩ := phSplit_uniq (hθc y hy hy1 hZy) (lu_P_dvd hpP) e1
        apply hfa
        refine gx_inj (GxCl.phi (gdCl_mono hZy ha) hcy) hcy ?_
        rw [gxTh_phi hy (gdAt_GxAt y) _ (gdCl_mono hZy ha) _ hcy, e2]
        exact luP_succ.1 hpP
      conv_rhs => rw [← hδ]
      rw [lpInd_above hpP hyp hgap]
      conv_lhs => rw [← hδ]
      rw [add_assoc p 1, one_add_of_omega0_le hω]

end Googology.Trans.PoR.InaccPsi.R2.Gd
