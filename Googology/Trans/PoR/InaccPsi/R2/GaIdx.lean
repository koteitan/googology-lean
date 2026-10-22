import Googology.Trans.PoR.InaccPsi.R2.GaCl

/-!
# The index of a code is a code, for codes with any strongly critical atoms

The proofs of `R2.LpIdx` (`lpIndCodeU`, `lpIndCodeV`) with the codes `GxCl Z At` of `R2.MxGx` (any atoms `At` with
`GxAt At`) and the reading `gxTh y At` in place of `LgCl` and `lgTh`:

* `gxIndCodeU` (**the index of a code is a code**, a constant level `1 ≤ a < Z`: some code `d ≤ b` reads
  `luInd a y (Θ_y(b))` at every strongly critical `y ≥ Z`);
* `gxIndCodeV` (**the same for a level code `a ≥ Ω₁`**, strongly critical levels `φ(a, 0) = a` included: `Θ_y(d) =
  lpInd (Θ_y a) y (Θ_y b)`).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ga

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph Lu
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Lp

variable {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hAt : GxAt At)
include hAt

/-- **The index of a code is a code** (a constant level `1 ≤ a < Z`). -/
theorem gxIndCodeU (hZ : SC Z) {a b : Ordinal.{0}} (haZ : a < Z) (hb : GxCl Z At b) (hb1 : Om 1 < b)
    (hbv : b < veblen a b) :
    ∃ d, GxCl Z At d ∧ d ≤ b ∧ ∀ y, SC y → y < Om 1 → Z ≤ y → gxTh y At d = luInd a y (gxTh y At b) := by
  have ha1Z : a + 1 < Z := hZ.add_one_lt haZ
  set q := veblen (a + 1) (Om 1 + 1) with hqdef
  have hq : GxCl Z At q := GxCl.phi (GxCl.small ha1Z) (gx_Om1_one hZ)
  have hqP : LuP (a + 1) q := luP_veblen _ _
  -- facts at every base
  have hThq : ∀ y, SC y → y < Om 1 → Z ≤ y → gxTh y At q = veblen (a + 1) (y + 1) := fun y hy hy1 hZy => by
    rw [gxTh_veblen_lvl hy hAt (ha1Z.trans_le hZy) (gx_Om1_one hy), gxTh_Om1_one hy hy1 hAt]
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
    refine ⟨b - (Om 1 + 1), (gxDec hZ hAt b hb).1 _ (gx_Om1_one hZ) hle, Ordinal.sub_le_self _ _,
      fun y hy hy1 hZy => ?_⟩
    have hbe : gxTh y At b = y + 1 + gxTh y At (b - (Om 1 + 1)) := by
      conv_lhs => rw [← Ordinal.add_sub_cancel_of_le hle]
      rw [gxTh_add hy hAt (gx_Om1_one hy), gxTh_Om1_one hy hy1 hAt]
    rw [hbe, luInd_low]
    intro z hz hP
    have h1 : y + 1 + z < gxTh y At b := by rw [hbe]; exact (add_lt_add_iff_left _).2 hz
    have h2 := hPy y hy hZy _ hP ((lt_add_one y).trans_le le_self_add)
    rw [← hThq y hy hy1 hZy] at h2
    exact absurd (h2.trans_lt h1) (not_lt.2 (gxTh_lt (hb.mono hZy Subset.rfl) hbq).le)
  · have hqb : q < b := lt_of_le_of_ne hbq fun e => by
      have h1 : veblen a q = q := by
        rw [hqdef]; exact veblen_veblen_of_lt (lt_add_one _) _
      rw [← e] at hbv; rw [h1] at hbv; exact lt_irrefl _ hbv
    obtain ⟨c, n, hc, hdc, hbc, hθc⟩ := gxSplit hZ hAt b hb
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
    have hThp : ∀ y, SC y → y < Om 1 → Z ≤ y → y < gxTh y At c := fun y hy hy1 hZy => by
      have := gxTh_lt (GxCl.om (Z := y) (At := At)) hc1; rwa [gxTh_Om1 hy hy1 hAt] at this
    by_cases hfa : veblen a c = c
    · -- `b = c + n`, `c ∈ P_{a+1}`: `d = c + (n - 1)`
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [Nat.cast_zero, add_zero] at hbc
        rw [hbc, hfa] at hbv; exact lt_irrefl _ hbv
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      refine ⟨c + m, GxCl.add hc (GxCl.small (ph_nat_lt hZ m)), ?_, fun y hy hy1 hZy => ?_⟩
      · rw [hbc]; exact (add_le_add_iff_left _).2 (by exact_mod_cast Nat.le_succ m)
      · have hcy := hc.mono hZy Subset.rfl
        have hP : LuP (a + 1) (gxTh y At c) := by
          refine luP_succ.2 ?_
          rw [← gxTh_veblen_lvl hy hAt (haZ.trans_le hZy) hcy, hfa]
        have e : gxTh y At b = gxTh y At c + 1 + m := by
          rw [hbc, gx_add_nat hy hAt hcy, add_assoc]; congr 1; exact_mod_cast Nat.add_comm m 1
        rw [gx_add_nat hy hAt hcy, e, luInd_above hP (hThp y hy hy1 hZy) fun z hz => ?_]
        obtain ⟨j, rfl⟩ := lt_omega0.1 (hz.trans (natCast_lt_omega0 m))
        exact lu_P_nat_not _ j
    · -- otherwise `d = b`
      refine ⟨b, hb, le_rfl, fun y hy hy1 hZy => ?_⟩
      have hcy := hc.mono hZy Subset.rfl
      have hby := hb.mono hZy Subset.rfl
      have hay : a < y := haZ.trans_le hZy
      set β := gxTh y At b with hβ
      have hβP : ¬ LuP (a + 1) β := by
        intro hP
        have h1 := gxTh_lt hby hbv
        rw [gxTh_veblen_lvl hy hAt hay hby, ← hβ, luP_succ.1 hP] at h1
        exact lt_irrefl _ h1
      set s := {v | LuP (a + 1) v ∧ v < β} with hs
      have hqs : gxTh y At q ∈ s :=
        ⟨by rw [hThq y hy hy1 hZy]; exact luP_veblen _ _, gxTh_lt (hq.mono hZy Subset.rfl) hqb⟩
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
        have e1 : gxTh y At c + (n : Ordinal.{0}) = p + ((1 + j : ℕ) : Ordinal.{0}) := by
          rw [← gx_add_nat hy hAt hcy, ← hbc, ← hβ, ← hδ, hj, add_assoc]; push_cast; rfl
        obtain ⟨e2, -⟩ := phSplit_uniq (hθc y hy hy1 hZy) (lu_P_dvd hpP) e1
        apply hfa
        refine gx_inj (GxCl.phi (GxCl.small hay) hcy) hcy ?_
        rw [gxTh_veblen_lvl hy hAt hay hcy, e2]
        exact luP_succ.1 hpP
      conv_rhs => rw [← hδ]
      rw [luInd_above hpP hyp hgap]
      conv_lhs => rw [← hδ]
      rw [add_assoc p 1, one_add_of_omega0_le hω]



/-- **The index of a code is a code** (every level code `a ≥ Ω₁`). -/
theorem gxIndCodeV (hZ : SC Z) {a b : Ordinal.{0}} (ha : GxCl Z At a) (haO : Om 1 ≤ a) (hb : GxCl Z At b)
    (hb0 : veblen a 0 = a → 0 < b) (hbv : b < veblen a b) :
    ∃ d, GxCl Z At d ∧ d ≤ b ∧ ∀ y, SC y → y < Om 1 → Z ≤ y → gxTh y At d = lpInd (gxTh y At a) y (gxTh y At b) := by
  have hyΘ : ∀ y, SC y → y < Om 1 → Z ≤ y → y ≤ gxTh y At a := fun y hy hy1 hZy => by
    rcases haO.lt_or_eq with h | h
    · have := gxTh_lt (GxCl.om (Z := y) (At := At)) h; rw [gxTh_Om1 hy hy1 hAt] at this; exact this.le
    · rw [← h, gxTh_Om1 hy hy1 hAt]
  have ha1 : GxCl Z At (a + 1) := GxCl.add ha (GxCl.small (gg_one_lt_of_SC hZ))
  have hq : GxCl Z At (veblen (a + 1) 0) := GxCl.phi ha1 (GxCl.zero hZ.1)
  have hqP : LuP (a + 1) (veblen (a + 1) 0) := luP_veblen _ _
  have hThq : ∀ y, SC y → y < Om 1 → Z ≤ y → gxTh y At (veblen (a + 1) 0) = veblen (gxTh y At a + 1) 0 :=
    fun y hy hy1 hZy => by
      rw [gxTh_phi hy hAt _ (ha1.mono hZy Subset.rfl) _ (GxCl.zero hy.1), gxTh_add hy hAt (ha.mono hZy Subset.rfl),
        gxTh_small (gg_one_lt_of_SC hy).le, gxTh_zero]
  have hPy : ∀ y v, LuP (gxTh y At a + 1) v → veblen (gxTh y At a + 1) 0 ≤ v := by
    intro y v hv
    obtain ⟨γ, rfl⟩ := hv
    exact veblen_le_veblen_iff_right.2 zero_le
  rcases lt_or_ge b (veblen (a + 1) 0) with hbq | hbq
  · -- below the first member of `P_{Ω₁+a+1}`: no member of `P_{y+a+1}` below `Θ_y(b)`
    have hnoP : ∀ y, SC y → y < Om 1 → Z ≤ y → ∀ z, z < gxTh y At b → ¬ LuP (gxTh y At a + 1) z := by
      intro y hy hy1 hZy z hz hP
      have h1 := gxTh_lt (hb.mono hZy Subset.rfl) hbq
      rw [hThq y hy hy1 hZy] at h1
      exact absurd (hPy y z hP) (not_le.2 (hz.trans h1))
    have hThv : ∀ y, SC y → Z ≤ y → gxTh y At (veblen a 0) = veblen (gxTh y At a) 0 := fun y hy hZy => by
      rw [gxTh_phi hy hAt _ (ha.mono hZy Subset.rfl) _ (GxCl.zero hy.1), gxTh_zero]
    by_cases hka : veblen a 0 = a
    · have hb0' := hb0 hka
      have hb1 : 1 ≤ b := one_le_iff_pos.2 hb0'
      refine ⟨b - 1, (gxDec hZ hAt b hb).1 1 (GxCl.small (gg_one_lt_of_SC hZ)) hb1, Ordinal.sub_le_self _ _,
        fun y hy hy1 hZy => ?_⟩
      have hbe : gxTh y At b = 1 + gxTh y At (b - 1) := by
        conv_lhs => rw [← Ordinal.add_sub_cancel_of_le hb1]
        rw [gxTh_add hy hAt (GxCl.small (gg_one_lt_of_SC hy)), gxTh_small (gg_one_lt_of_SC hy).le]
      have hn := hnoP y hy hy1 hZy
      have hfix : veblen (gxTh y At a) 0 = gxTh y At a := by rw [← hThv y hy hZy, hka]
      rw [hbe]
      refine (lpInd_low_eq (Or.inr ⟨hfix, hyΘ y hy hy1 hZy⟩) fun z hz => hn (1 + z) ?_).symm
      rw [hbe]
      exact (add_lt_add_iff_left 1).2 hz
    · refine ⟨b, hb, le_rfl, fun y hy hy1 hZy => ?_⟩
      have hav : a < veblen a 0 := lt_of_le_of_ne (left_le_veblen a 0) (Ne.symm hka)
      have hβ0 : gxTh y At a < veblen (gxTh y At a) 0 := by
        rw [← hThv y hy hZy]; exact gxTh_lt (ha.mono hZy Subset.rfl) hav
      exact (lpInd_low_gt ((hyΘ y hy hy1 hZy).trans_lt hβ0) hβ0 (hnoP y hy hy1 hZy)).symm
  · have hqb : veblen (a + 1) 0 < b := lt_of_le_of_ne hbq fun e => by
      have h1 : veblen (a) (veblen (a + 1) 0) = veblen (a + 1) 0 :=
        veblen_veblen_of_lt (lt_add_one _) _
      rw [← e] at hbv; rw [h1] at hbv; exact lt_irrefl _ hbv
    obtain ⟨c, n, hc, hdc, hbc, hθc⟩ := gxSplit hZ hAt b hb
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
    have hThp : ∀ y, SC y → y < Om 1 → Z ≤ y → y < gxTh y At c := fun y hy hy1 hZy => by
      have := gxTh_lt (GxCl.om (Z := y) (At := At)) hc1; rwa [gxTh_Om1 hy hy1 hAt] at this
    by_cases hfa : veblen (a) c = c
    · -- `b = c + n`, `c ∈ P_{Ω₁+a+1}`: `d = c + (n - 1)`
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [Nat.cast_zero, add_zero] at hbc
        rw [hbc, hfa] at hbv; exact lt_irrefl _ hbv
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      refine ⟨c + m, GxCl.add hc (GxCl.small (ph_nat_lt hZ m)), ?_, fun y hy hy1 hZy => ?_⟩
      · rw [hbc]; exact (add_le_add_iff_left _).2 (by exact_mod_cast Nat.le_succ m)
      · have hcy := hc.mono hZy Subset.rfl
        have hP : LuP (gxTh y At a + 1) (gxTh y At c) := by
          refine luP_succ.2 ?_
          rw [← gxTh_phi hy hAt _ (ha.mono hZy Subset.rfl) _ hcy, hfa]
        have e : gxTh y At b = gxTh y At c + 1 + m := by
          rw [hbc, gx_add_nat hy hAt hcy, add_assoc]; congr 1; exact_mod_cast Nat.add_comm m 1
        rw [gx_add_nat hy hAt hcy, e, lpInd_above hP (hThp y hy hy1 hZy) fun z hz => ?_]
        obtain ⟨j, rfl⟩ := lt_omega0.1 (hz.trans (natCast_lt_omega0 m))
        exact lu_P_nat_not _ j
    · -- otherwise `d = b`
      refine ⟨b, hb, le_rfl, fun y hy hy1 hZy => ?_⟩
      have hcy := hc.mono hZy Subset.rfl
      have hby := hb.mono hZy Subset.rfl
      set β := gxTh y At b with hβ
      have hβP : ¬ LuP (gxTh y At a + 1) β := by
        intro hP
        have h1 := gxTh_lt hby hbv
        rw [gxTh_phi hy hAt _ (ha.mono hZy Subset.rfl) _ hby, ← hβ, luP_succ.1 hP] at h1
        exact lt_irrefl _ h1
      set s := {v | LuP (gxTh y At a + 1) v ∧ v < β} with hs
      have hqs : gxTh y At (veblen (a + 1) 0) ∈ s :=
        ⟨by rw [hThq y hy hy1 hZy]; exact luP_veblen _ _, gxTh_lt (hq.mono hZy Subset.rfl) hqb⟩
      have hne : s.Nonempty := ⟨_, hqs⟩
      have hbdd : BddAbove s := ⟨β, fun v hv => hv.2.le⟩
      have hpP : LuP (gxTh y At a + 1) (sSup s) := by
        refine luP_succ.2 ?_
        rw [(isNormal_veblen (gxTh y At a)).map_sSup hne hbdd]
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
          _ < veblen (gxTh y At a + 1) 0 :=
            veblen_zero_lt_veblen_zero.2 ((hyΘ y hy hy1 hZy).trans_lt (lt_add_one _))
      set p := sSup s with hp
      have hδ : p + 1 + (β - (p + 1)) = β := Ordinal.add_sub_cancel_of_le (Order.add_one_le_of_lt hpβ)
      have hgap : ∀ z < β - (p + 1), ¬ LuP (gxTh y At a + 1) (p + 1 + z) := by
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
        have e1 : gxTh y At c + (n : Ordinal.{0}) = p + ((1 + j : ℕ) : Ordinal.{0}) := by
          rw [← gx_add_nat hy hAt hcy, ← hbc, ← hβ, ← hδ, hj, add_assoc]; push_cast; rfl
        obtain ⟨e2, -⟩ := phSplit_uniq (hθc y hy hy1 hZy) (lu_P_dvd hpP) e1
        apply hfa
        refine gx_inj (GxCl.phi (ha.mono hZy Subset.rfl) hcy) hcy ?_
        rw [gxTh_phi hy hAt _ (ha.mono hZy Subset.rfl) _ hcy, e2]
        exact luP_succ.1 hpP
      conv_rhs => rw [← hδ]
      rw [lpInd_above hpP hyp hgap]
      conv_lhs => rw [← hδ]
      rw [add_assoc p 1, one_add_of_omega0_le hω]

end Googology.Trans.PoR.InaccPsi.R2.Ga
