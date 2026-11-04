import Googology.Trans.PoR.InaccPsi.R2.ZbBG

/-!
# ZbLd: THE LADDER OVER A LAYER WITH AN ABSTRACT TOP CODE (ATOMS OF ANY `Zb.ZbAS`)

The proofs of `Gs.GsmIdx`, `Gs.GsmLd` (and `Gs.gsmTh_lt_Om1`) with the atoms of a code system `K : GsCS` replaced by
those of an atom system `A : Zb.ZbAS`; the one fact on `K` beyond its atom sets, that the reading of an atom over a
countable strongly critical `y` is countable, is the hypothesis `ZbTh A` (`Zb.zbU_th` for `Zb.zbU`).

* `ZbTh`, `zbTh_lt_Om1` (**every reading of a code over `y` is below `Ω₁`**), `zbPoly_of_SCT`;
* `zbSplit`, `zbIndCodeU`, `zbIndCodeV` (**the index of a code is a code**);
* `zbcQ_cl`, `zbNotNoB`, `ZbLdP`, `zbTop_th` (**`gdP B n y = Θ_y(cQ c n)`**), `zbPoly` (**every code below `cQ c n`
  is read by a term of stage `≤ n`**).

No new axiom.  New definitions: `ZbTh`, `ZbLdP`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zb

open Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq Googology.Trans.PoR.InaccPsi.R2.Gr
  Googology.Trans.PoR.InaccPsi.R2.Gs
open Googology.Trans.PoR.InaccPsi.R2.Gi
open Googology.Trans.PoR.InaccPsi.R2.Gf
open Googology.Trans.PoR.InaccPsi.R2.Ge
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph Lu
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Lp
  Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **The readings of the atoms over a countable strongly critical base are countable.** -/
def ZbTh (A : ZbAS) : Prop := ∀ y, SC y → y < Om 1 → ∀ s ∈ A.At y, gxTh y (A.At y) s < Om 1

/-- Every reading of a code over `y` is below `Ω₁`. -/
theorem zbTh_lt_Om1 {A : ZbAS} (hth : ZbTh A) {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) {c : Ordinal.{0}}
    (hc : GxCl y (A.At y) c) : gxTh y (A.At y) c < Om 1 := by
  have hAt := A.gxAt y
  induction hc with
  | small h => rw [gxTh_small h.le]; exact h.trans hy1
  | om => rw [gxTh_Om1 hy hy1 hAt]; exact hy1
  | atom hs => exact hth y hy hy1 _ hs
  | @add u v hu _ ihu ihv => rw [gxTh_add hy hAt hu]; exact ph_SC_Om1.isPrincipal ihu ihv
  | @phi a b ha hb iha ihb => rw [gxTh_phi hy hAt a ha b hb]; exact ph_SC_Om1.2 _ iha _ ihb

/-- **Reduction to strongly critical bases below `Ω₁`** (any term type). -/
theorem zbPoly_of_SCT {A : ZbAS} {T : Type 1} (CB : T → Ordinal.{0} → Prop) (val : T → Ordinal.{0} → Ordinal.{0})
    (t0 : T) {g E : Ordinal.{0}}
    (h : ∀ Z, SC Z → Z < Om 1 → g < Z → ∀ c, GxCl Z (A.At Z) c → c < E → ∃ s : T, ∀ y, SC y → y < Om 1 →
      Z ≤ y → CB s y ∧ val s y = gxTh y (A.At y) c) :
    ∀ Z c, g < Z → GxCl Z (A.At Z) c → c < E → ∃ s : T, ∀ y, SC y → y < Om 1 → Z ≤ y →
      CB s y ∧ val s y = gxTh y (A.At y) c := by
  intro Z c hg hc hcE
  by_cases hex : ∃ y, SC y ∧ y < Om 1 ∧ Z ≤ y
  · have hmem : sInf {y | SC y ∧ y < Om 1 ∧ Z ≤ y} ∈ {y | SC y ∧ y < Om 1 ∧ Z ≤ y} := csInf_mem hex
    obtain ⟨h1, h2, h3⟩ := hmem
    obtain ⟨s, hs⟩ := h _ h1 h2 (hg.trans_le h3) c (A.cl_mono h3 hc) hcE
    exact ⟨s, fun y hy hy1 hZy => hs y hy hy1 (csInf_le' ⟨hy, hy1, hZy⟩)⟩
  · push Not at hex
    exact ⟨t0, fun y hy hy1 hZy => absurd hZy (not_le.2 (hex y hy hy1))⟩

section Idx

variable {Z : Ordinal.{0}} {A : ZbAS}

/-- **A code is `a + n`** with `a` a code, `ω ∣ a`, `n < ω`, and `ω ∣ Θ_y(a)` at every strongly critical `y ≥ Z`. -/
theorem zbSplit (hZ : SC Z)  : ∀ b, GxCl Z (A.At Z) b → ∃ a : Ordinal.{0}, ∃ n : ℕ, GxCl Z (A.At Z) a ∧
    ω ∣ a ∧ b = a + n ∧ ∀ y, SC y → y < Om 1 → Z ≤ y → ω ∣ gxTh y (A.At y) a := by
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
  obtain ⟨hsub, hlog⟩ := gxDec hZ (A.gxAt Z) b hb
  have hw : GxCl Z (A.At Z) (ω ^ log ω b) := GxCl.opow hZ.1 hlog
  have hwb : ω ^ log ω b ≤ b := opow_log_le_self ω hb0
  have hr := hsub _ hw hwb
  have hbr : ω ^ log ω b + (b - ω ^ log ω b) = b := Ordinal.add_sub_cancel_of_le hwb
  rcases eq_or_ne (b - ω ^ log ω b) 0 with h0 | h0
  · rw [h0, add_zero] at hbr
    refine ⟨b, 0, hb, hbr ▸ ph_omega_dvd_opow hL, by rw [Nat.cast_zero, add_zero], fun y hy hy1 hZy => ?_⟩
    rw [← hbr, gxTh_opow hy (A.gxAt y) (A.cl_mono hZy hlog)]
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
    · rw [gxTh_add hy (A.gxAt y) (A.cl_mono hZy hw), gxTh_opow hy (A.gxAt y) (A.cl_mono hZy hlog)]
      exact dvd_add (ph_omega_dvd_opow (gx_ne_zero hy hL)) (hθ' y hy hy1 hZy)

/-- **The index of a code is a code** (a constant level `1 ≤ a < Z`). -/
theorem zbIndCodeU (hZ : SC Z) {a b : Ordinal.{0}} (haZ : a < Z) (hb : GxCl Z (A.At Z) b) (hb1 : Om 1 < b)
    (hbv : b < veblen a b) :
    ∃ d, GxCl Z (A.At Z) d ∧ d ≤ b ∧ ∀ y, SC y → y < Om 1 → Z ≤ y →
      gxTh y (A.At y) d = luInd a y (gxTh y (A.At y) b) := by
  have ha1Z : a + 1 < Z := hZ.add_one_lt haZ
  set q := veblen (a + 1) (Om 1 + 1) with hqdef
  have hq : GxCl Z (A.At Z) q := GxCl.phi (GxCl.small ha1Z) (gx_Om1_one hZ)
  have hqP : LuP (a + 1) q := luP_veblen _ _
  -- facts at every base
  have hThq : ∀ y, SC y → y < Om 1 → Z ≤ y → gxTh y (A.At y) q = veblen (a + 1) (y + 1) := fun y hy hy1 hZy => by
    rw [gxTh_veblen_lvl hy (A.gxAt y) (ha1Z.trans_le hZy) (gx_Om1_one hy), gxTh_Om1_one hy hy1 (A.gxAt y)]
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
    refine ⟨b - (Om 1 + 1), (gxDec hZ (A.gxAt Z) b hb).1 _ (gx_Om1_one hZ) hle, Ordinal.sub_le_self _ _,
      fun y hy hy1 hZy => ?_⟩
    have hbe : gxTh y (A.At y) b = y + 1 + gxTh y (A.At y) (b - (Om 1 + 1)) := by
      conv_lhs => rw [← Ordinal.add_sub_cancel_of_le hle]
      rw [gxTh_add hy (A.gxAt y) (gx_Om1_one hy), gxTh_Om1_one hy hy1 (A.gxAt y)]
    rw [hbe, luInd_low]
    intro z hz hP
    have h1 : y + 1 + z < gxTh y (A.At y) b := by rw [hbe]; exact (add_lt_add_iff_left _).2 hz
    have h2 := hPy y hy hZy _ hP ((lt_add_one y).trans_le le_self_add)
    rw [← hThq y hy hy1 hZy] at h2
    exact absurd (h2.trans_lt h1) (not_lt.2 (gxTh_lt (A.cl_mono hZy hb) hbq).le)
  · have hqb : q < b := lt_of_le_of_ne hbq fun e => by
      have h1 : veblen a q = q := by
        rw [hqdef]; exact veblen_veblen_of_lt (lt_add_one _) _
      rw [← e] at hbv; rw [h1] at hbv; exact lt_irrefl _ hbv
    obtain ⟨c, n, hc, hdc, hbc, hθc⟩ := zbSplit hZ b hb
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
    have hThp : ∀ y, SC y → y < Om 1 → Z ≤ y → y < gxTh y (A.At y) c := fun y hy hy1 hZy => by
      have := gxTh_lt (GxCl.om (Z := y) (At := A.At y)) hc1; rwa [gxTh_Om1 hy hy1 (A.gxAt y)] at this
    by_cases hfa : veblen a c = c
    · -- `b = c + n`, `c ∈ P_{a+1}`: `d = c + (n - 1)`
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [Nat.cast_zero, add_zero] at hbc
        rw [hbc, hfa] at hbv; exact lt_irrefl _ hbv
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      refine ⟨c + m, GxCl.add hc (GxCl.small (ph_nat_lt hZ m)), ?_, fun y hy hy1 hZy => ?_⟩
      · rw [hbc]; exact (add_le_add_iff_left _).2 (by exact_mod_cast Nat.le_succ m)
      · have hcy := A.cl_mono hZy hc
        have hP : LuP (a + 1) (gxTh y (A.At y) c) := by
          refine luP_succ.2 ?_
          rw [← gxTh_veblen_lvl hy (A.gxAt y) (haZ.trans_le hZy) hcy, hfa]
        have e : gxTh y (A.At y) b = gxTh y (A.At y) c + 1 + m := by
          rw [hbc, gx_add_nat hy (A.gxAt y) hcy, add_assoc]; congr 1; exact_mod_cast Nat.add_comm m 1
        rw [gx_add_nat hy (A.gxAt y) hcy, e, luInd_above hP (hThp y hy hy1 hZy) fun z hz => ?_]
        obtain ⟨j, rfl⟩ := lt_omega0.1 (hz.trans (natCast_lt_omega0 m))
        exact lu_P_nat_not _ j
    · -- otherwise `d = b`
      refine ⟨b, hb, le_rfl, fun y hy hy1 hZy => ?_⟩
      have hcy := A.cl_mono hZy hc
      have hby := A.cl_mono hZy hb
      have hay : a < y := haZ.trans_le hZy
      set β := gxTh y (A.At y) b with hβ
      have hβP : ¬ LuP (a + 1) β := by
        intro hP
        have h1 := gxTh_lt hby hbv
        rw [gxTh_veblen_lvl hy (A.gxAt y) hay hby, ← hβ, luP_succ.1 hP] at h1
        exact lt_irrefl _ h1
      set s := {v | LuP (a + 1) v ∧ v < β} with hs
      have hqs : gxTh y (A.At y) q ∈ s :=
        ⟨by rw [hThq y hy hy1 hZy]; exact luP_veblen _ _, gxTh_lt (A.cl_mono hZy hq) hqb⟩
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
        have e1 : gxTh y (A.At y) c + (n : Ordinal.{0}) = p + ((1 + j : ℕ) : Ordinal.{0}) := by
          rw [← gx_add_nat hy (A.gxAt y) hcy, ← hbc, ← hβ, ← hδ, hj, add_assoc]; push_cast; rfl
        obtain ⟨e2, -⟩ := phSplit_uniq (hθc y hy hy1 hZy) (lu_P_dvd hpP) e1
        apply hfa
        refine gx_inj (GxCl.phi (GxCl.small hay) hcy) hcy ?_
        rw [gxTh_veblen_lvl hy (A.gxAt y) hay hcy, e2]
        exact luP_succ.1 hpP
      conv_rhs => rw [← hδ]
      rw [luInd_above hpP hyp hgap]
      conv_lhs => rw [← hδ]
      rw [add_assoc p 1, one_add_of_omega0_le hω]



/-- **The index of a code is a code** (every level code `a ≥ Ω₁`). -/
theorem zbIndCodeV (hZ : SC Z) {a b : Ordinal.{0}} (ha : GxCl Z (A.At Z) a) (haO : Om 1 ≤ a) (hb : GxCl Z (A.At Z) b)
    (hb0 : veblen a 0 = a → 0 < b) (hbv : b < veblen a b) :
    ∃ d, GxCl Z (A.At Z) d ∧ d ≤ b ∧ ∀ y, SC y → y < Om 1 → Z ≤ y →
      gxTh y (A.At y) d = lpInd (gxTh y (A.At y) a) y (gxTh y (A.At y) b) := by
  have hyΘ : ∀ y, SC y → y < Om 1 → Z ≤ y → y ≤ gxTh y (A.At y) a := fun y hy hy1 hZy => by
    rcases haO.lt_or_eq with h | h
    · have := gxTh_lt (GxCl.om (Z := y) (At := A.At y)) h; rw [gxTh_Om1 hy hy1 (A.gxAt y)] at this; exact this.le
    · rw [← h, gxTh_Om1 hy hy1 (A.gxAt y)]
  have ha1 : GxCl Z (A.At Z) (a + 1) := GxCl.add ha (GxCl.small (gg_one_lt_of_SC hZ))
  have hq : GxCl Z (A.At Z) (veblen (a + 1) 0) := GxCl.phi ha1 (GxCl.zero hZ.1)
  have hqP : LuP (a + 1) (veblen (a + 1) 0) := luP_veblen _ _
  have hThq : ∀ y, SC y → y < Om 1 → Z ≤ y → gxTh y (A.At y) (veblen (a + 1) 0) = veblen (gxTh y (A.At y) a + 1) 0 :=
    fun y hy hy1 hZy => by
      rw [gxTh_phi hy (A.gxAt y) _ (A.cl_mono hZy ha1) _ (GxCl.zero hy.1),
        gxTh_add hy (A.gxAt y) (A.cl_mono hZy ha),
        gxTh_small (gg_one_lt_of_SC hy).le, gxTh_zero]
  have hPy : ∀ y v, LuP (gxTh y (A.At y) a + 1) v → veblen (gxTh y (A.At y) a + 1) 0 ≤ v := by
    intro y v hv
    obtain ⟨γ, rfl⟩ := hv
    exact veblen_le_veblen_iff_right.2 zero_le
  rcases lt_or_ge b (veblen (a + 1) 0) with hbq | hbq
  · -- below the first member of `P_{Ω₁+a+1}`: no member of `P_{y+a+1}` below `Θ_y(b)`
    have hnoP : ∀ y, SC y → y < Om 1 → Z ≤ y → ∀ z, z < gxTh y (A.At y) b → ¬ LuP (gxTh y (A.At y) a + 1) z := by
      intro y hy hy1 hZy z hz hP
      have h1 := gxTh_lt (A.cl_mono hZy hb) hbq
      rw [hThq y hy hy1 hZy] at h1
      exact absurd (hPy y z hP) (not_le.2 (hz.trans h1))
    have hThv : ∀ y, SC y → Z ≤ y → gxTh y (A.At y) (veblen a 0) = veblen (gxTh y (A.At y) a) 0 := fun y hy hZy => by
      rw [gxTh_phi hy (A.gxAt y) _ (A.cl_mono hZy ha) _ (GxCl.zero hy.1), gxTh_zero]
    by_cases hka : veblen a 0 = a
    · have hb0' := hb0 hka
      have hb1 : 1 ≤ b := one_le_iff_pos.2 hb0'
      refine ⟨b - 1, (gxDec hZ (A.gxAt Z) b hb).1 1 (GxCl.small (gg_one_lt_of_SC hZ)) hb1, Ordinal.sub_le_self _ _,
        fun y hy hy1 hZy => ?_⟩
      have hbe : gxTh y (A.At y) b = 1 + gxTh y (A.At y) (b - 1) := by
        conv_lhs => rw [← Ordinal.add_sub_cancel_of_le hb1]
        rw [gxTh_add hy (A.gxAt y) (GxCl.small (gg_one_lt_of_SC hy)), gxTh_small (gg_one_lt_of_SC hy).le]
      have hn := hnoP y hy hy1 hZy
      have hfix : veblen (gxTh y (A.At y) a) 0 = gxTh y (A.At y) a := by rw [← hThv y hy hZy, hka]
      rw [hbe]
      refine (lpInd_low_eq (Or.inr ⟨hfix, hyΘ y hy hy1 hZy⟩) fun z hz => hn (1 + z) ?_).symm
      rw [hbe]
      exact (add_lt_add_iff_left 1).2 hz
    · refine ⟨b, hb, le_rfl, fun y hy hy1 hZy => ?_⟩
      have hav : a < veblen a 0 := lt_of_le_of_ne (left_le_veblen a 0) (Ne.symm hka)
      have hβ0 : gxTh y (A.At y) a < veblen (gxTh y (A.At y) a) 0 := by
        rw [← hThv y hy hZy]; exact gxTh_lt (A.cl_mono hZy ha) hav
      exact (lpInd_low_gt ((hyΘ y hy hy1 hZy).trans_lt hβ0) hβ0 (hnoP y hy hy1 hZy)).symm
  · have hqb : veblen (a + 1) 0 < b := lt_of_le_of_ne hbq fun e => by
      have h1 : veblen (a) (veblen (a + 1) 0) = veblen (a + 1) 0 :=
        veblen_veblen_of_lt (lt_add_one _) _
      rw [← e] at hbv; rw [h1] at hbv; exact lt_irrefl _ hbv
    obtain ⟨c, n, hc, hdc, hbc, hθc⟩ := zbSplit hZ b hb
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
    have hThp : ∀ y, SC y → y < Om 1 → Z ≤ y → y < gxTh y (A.At y) c := fun y hy hy1 hZy => by
      have := gxTh_lt (GxCl.om (Z := y) (At := A.At y)) hc1; rwa [gxTh_Om1 hy hy1 (A.gxAt y)] at this
    by_cases hfa : veblen (a) c = c
    · -- `b = c + n`, `c ∈ P_{Ω₁+a+1}`: `d = c + (n - 1)`
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [Nat.cast_zero, add_zero] at hbc
        rw [hbc, hfa] at hbv; exact lt_irrefl _ hbv
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      refine ⟨c + m, GxCl.add hc (GxCl.small (ph_nat_lt hZ m)), ?_, fun y hy hy1 hZy => ?_⟩
      · rw [hbc]; exact (add_le_add_iff_left _).2 (by exact_mod_cast Nat.le_succ m)
      · have hcy := A.cl_mono hZy hc
        have hP : LuP (gxTh y (A.At y) a + 1) (gxTh y (A.At y) c) := by
          refine luP_succ.2 ?_
          rw [← gxTh_phi hy (A.gxAt y) _ (A.cl_mono hZy ha) _ hcy, hfa]
        have e : gxTh y (A.At y) b = gxTh y (A.At y) c + 1 + m := by
          rw [hbc, gx_add_nat hy (A.gxAt y) hcy, add_assoc]; congr 1; exact_mod_cast Nat.add_comm m 1
        rw [gx_add_nat hy (A.gxAt y) hcy, e, lpInd_above hP (hThp y hy hy1 hZy) fun z hz => ?_]
        obtain ⟨j, rfl⟩ := lt_omega0.1 (hz.trans (natCast_lt_omega0 m))
        exact lu_P_nat_not _ j
    · -- otherwise `d = b`
      refine ⟨b, hb, le_rfl, fun y hy hy1 hZy => ?_⟩
      have hcy := A.cl_mono hZy hc
      have hby := A.cl_mono hZy hb
      set β := gxTh y (A.At y) b with hβ
      have hβP : ¬ LuP (gxTh y (A.At y) a + 1) β := by
        intro hP
        have h1 := gxTh_lt hby hbv
        rw [gxTh_phi hy (A.gxAt y) _ (A.cl_mono hZy ha) _ hby, ← hβ, luP_succ.1 hP] at h1
        exact lt_irrefl _ h1
      set s := {v | LuP (gxTh y (A.At y) a + 1) v ∧ v < β} with hs
      have hqs : gxTh y (A.At y) (veblen (a + 1) 0) ∈ s :=
        ⟨by rw [hThq y hy hy1 hZy]; exact luP_veblen _ _, gxTh_lt (A.cl_mono hZy hq) hqb⟩
      have hne : s.Nonempty := ⟨_, hqs⟩
      have hbdd : BddAbove s := ⟨β, fun v hv => hv.2.le⟩
      have hpP : LuP (gxTh y (A.At y) a + 1) (sSup s) := by
        refine luP_succ.2 ?_
        rw [(isNormal_veblen (gxTh y (A.At y) a)).map_sSup hne hbdd]
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
          _ < veblen (gxTh y (A.At y) a + 1) 0 :=
            veblen_zero_lt_veblen_zero.2 ((hyΘ y hy hy1 hZy).trans_lt (lt_add_one _))
      set p := sSup s with hp
      have hδ : p + 1 + (β - (p + 1)) = β := Ordinal.add_sub_cancel_of_le (Order.add_one_le_of_lt hpβ)
      have hgap : ∀ z < β - (p + 1), ¬ LuP (gxTh y (A.At y) a + 1) (p + 1 + z) := by
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
        have e1 : gxTh y (A.At y) c + (n : Ordinal.{0}) = p + ((1 + j : ℕ) : Ordinal.{0}) := by
          rw [← gx_add_nat hy (A.gxAt y) hcy, ← hbc, ← hβ, ← hδ, hj, add_assoc]; push_cast; rfl
        obtain ⟨e2, -⟩ := phSplit_uniq (hθc y hy hy1 hZy) (lu_P_dvd hpP) e1
        apply hfa
        refine gx_inj (GxCl.phi (A.cl_mono hZy ha) hcy) hcy ?_
        rw [gxTh_phi hy (A.gxAt y) _ (A.cl_mono hZy ha) _ hcy, e2]
        exact luP_succ.1 hpP
      conv_rhs => rw [← hδ]
      rw [lpInd_above hpP hyp hgap]
      conv_lhs => rw [← hδ]
      rw [add_assoc p 1, one_add_of_omega0_le hω]


end Idx

section Ld

variable {A : ZbAS}

theorem zbcQ_cl {g c : Ordinal.{0}} (hc : ∀ Z, SC Z → g < Z → GxCl Z (A.At Z) c) {Z : Ordinal.{0}} (hZ : SC Z)
    (hgZ : g < Z) : ∀ n : ℕ, GxCl Z (A.At Z) (cQ c n)
  | 0 => hc Z hZ hgZ
  | n + 1 => GxCl.phi (zbcQ_cl hc hZ hgZ n) (GxCl.small (bQ_lt hZ _))

/-! ## A level code is not read by a base-free term -/

/-- **A term that reads a level code `a ≥ Ω₁` at every strongly critical `y ≥ Z` is not base-free.** -/
theorem zbNotNoB (hth : ZbTh A) {B : GdB} {Z a : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1)
    (ha : GxCl Z (A.At Z) a) (haO : Om 1 ≤ a) {l : GdT B}
    (hl : ∀ y, SC y → y < Om 1 → Z ≤ y → GdT.val l y = gxTh y (A.At y) a) : ¬ GdT.noB l := by
  intro hn
  obtain ⟨Y, hYS, hvY, hY1⟩ := gd_SC_above (zbTh_lt_Om1 hth hZ hZ1 ha)
  have hZv : Z ≤ gxTh Z (A.At Z) a := by
    have := gxTh_mono (Z := Z) (At := A.At Z) haO
    rwa [gxTh_Om1 hZ hZ1 (A.gxAt Z)] at this
  have hge : Y ≤ gxTh Y (A.At Y) a := by
    have := gxTh_mono (Z := Y) (At := A.At Y) haO
    rwa [gxTh_Om1 hYS hY1 (A.gxAt _)] at this
  have e := GdT.noB_val l hn Z Y
  rw [hl Z hZ hZ1 le_rfl, hl _ hYS hY1 (hZv.trans hvY.le)] at e
  exact absurd (e ▸ hvY) (not_lt.2 hge)

/-- **The ladder statement**: every code `d < E` over a base `Z` above the gate is read by a term of stage `≤ n`. -/
def ZbLdP (A : ZbAS) (B : GdB) (n : ℕ) (E : Ordinal.{0}) : Prop :=
  ∀ Z d, B.g < Z → GxCl Z (A.At Z) d → d < E → ∃ s : GdT B, ∀ y, SC y → y < Om 1 → Z ≤ y →
    (GdT.CBt s y ∧ GdT.stage s ≤ n) ∧ GdT.val s y = gxTh y (A.At y) d

/-! ## The readings of the stage tops and the terms for the codes -/

section Poly

variable {B : GdB} {c : Ordinal.{0}} (hc : ∀ Z, SC Z → B.g < Z → GxCl Z (A.At Z) c) (hcO : Om 1 ≤ c)
  (hKE : ∀ y, SC y → y < Om 1 → B.g < y → B.K.E y = gxTh y (A.At y) c)
include hc hcO hKE

omit hcO in
/-- **`gP n y = Θ_y(cQ c n)`** at every strongly critical `y < Ω₁`. -/
theorem zbTop_th : ∀ n : ℕ, ∀ y, SC y → y < Om 1 → B.g < y → gdP B n y = gxTh y (A.At y) (cQ c n)
  | 0, y, hy, hy1, hg => hKE y hy hy1 hg
  | n + 1, y, hy, hy1, hg => by
      have hAt := A.gxAt y
      have hyE := gg_SC_eps hy
      have hy1' := lp_y1 hy1
      have ih := zbTop_th n y hy hy1 hg
      have hcn := zbcQ_cl hc hy hg n
      have hbn : GxCl y (A.At y) (bQ (cQ c n)) := GxCl.small (bQ_lt hy _)
      show vt y (Om1 * gdP B n y) = gxTh y (A.At y) (veblen (cQ c n) (bQ (cQ c n)))
      rw [gxTh_phi hy hAt _ hcn _ hbn, gxTh_small (bQ_lt hy _).le, ← ih]
      obtain ⟨hβT, hyβ, hβ1, -⟩ := gdP_facts B hyE hy1' hg n
      have hβ1' : 1 ≤ gdP B n y := (Lu.lu_one_lt_E hyE).le.trans hyβ.le
      by_cases hS : veblen (cQ c n) 0 = cQ c n
      · rw [bQ_of hS]
        have hβS : veblen (gdP B n y) 0 = gdP B n y := by
          have := congrArg (gxTh y (A.At y)) hS
          rw [gxTh_phi hy hAt _ hcn _ (GxCl.zero hy.1), gxTh_zero, ← ih] at this
          exact this
        have h0 : lpInd (gdP B n y) y 1 = 0 := by
          have := lpInd_low_eq (β := gdP B n y) (y := y) (δ := 0) (Or.inr ⟨hβS, hyβ.le⟩)
            (fun z hz => absurd hz (not_lt.2 zero_le))
          rwa [add_zero] at this
        have hnP : ¬ LuP (gdP B n y + 1) 1 := by
          have h := lu_P_nat_not (β := gdP B n y) 0 0
          have e : (0 : Ordinal.{0}) + 1 + ((0 : ℕ) : Ordinal.{0}) = 1 := by simp
          rwa [e] at h
        have hy1v : y < veblen (gdP B n y) 1 :=
          hyβ.trans (lt_of_eq_of_lt hβS.symm (veblen_lt_veblen_iff_right.2 zero_lt_one))
        have e := lpPhLev hy hy1' hβ1' hβT hβ1 1 hy1v (lp_lvl_lt zero_lt_one) hnP
          (by rw [h0]; exact mem_T_of_le hyE hy1' zero_le) (by rw [h0]; exact Ordinal.omega_pos 1)
        rw [e, h0, add_zero]
      · rw [bQ_of_not hS]
        have hβv : gdP B n y < veblen (gdP B n y) 0 := by
          have := gxTh_lt hcn (lt_of_le_of_ne (left_le_veblen (cQ c n) 0) (Ne.symm hS)) (At := A.At y)
          rwa [gxTh_phi hy hAt _ hcn _ (GxCl.zero hy.1), gxTh_zero, ← ih] at this
        have h0 : lpInd (gdP B n y) y 0 = 0 := ggOtp_zero _
        have hnP : ¬ LuP (gdP B n y + 1) 0 := by
          rintro ⟨j, hj⟩
          exact absurd hj (gg_veblen_eps (x := gdP B n y + 1) (y := j)
            (by simp) ▸ (Ordinal.opow_pos _ omega0_pos)).ne'
        have e := lpPhLev hy hy1' hβ1' hβT hβ1 0 (hyβ.trans hβv) hβv hnP
          (by rw [h0]; exact mem_T_of_le hyE hy1' zero_le) (by rw [h0]; exact Ordinal.omega_pos 1)
        rw [e, h0, add_zero]

/-- **Every code below `cQ c n` over a base above the gate is read by a term of stage `≤ n`** (given the terms of `K`
for the codes below `c`). -/
theorem zbPoly (hth : ZbTh A) (hKP : ZbPolyG A B.K.sys c) : ∀ n : ℕ, ZbLdP A B n (cQ c n) := by
  have hKterm : ∀ (n : ℕ) (Z d : Ordinal.{0}), B.g < Z → GxCl Z (A.At Z) d → d < c → ∃ s : GdT B, ∀ y, SC y →
      y < Om 1 → Z ≤ y → (GdT.CBt s y ∧ GdT.stage s ≤ n) ∧ GdT.val s y = gxTh y (A.At y) d := by
    intro n Z d hgZ hd hdc
    obtain ⟨k, hk⟩ := hKP Z d hgZ hd hdc
    exact ⟨GdT.ak k, fun y hy hy1 hZy => ⟨⟨(hk y hy hy1 hZy).1, Nat.zero_le n⟩, (hk y hy hy1 hZy).2⟩⟩
  intro n
  induction n with
  | zero => exact fun Z d hgZ hd hdc => hKterm 0 Z d hgZ hd hdc
  | succ n ihn =>
    refine zbPoly_of_SCT (fun s y => GdT.CBt s y ∧ GdT.stage s ≤ n + 1) GdT.val (GdT.cst 0) fun Z hZ hZ1 hgZ => ?_
    intro d
    induction d using WellFoundedLT.induction with
    | ind d IH =>
    intro hd hdB
    rcases lt_trichotomy d c with hdc | rfl | hcd
    · exact hKterm (n + 1) Z d hgZ hd hdc
    · exact ⟨GdT.tp, fun y hy hy1 hZy => ⟨⟨trivial, by simp [GdT.stage]⟩, hKE y hy hy1 (hgZ.trans_le hZy)⟩⟩
    have hd1 : Om 1 < d := hcO.trans_lt hcd
    have hd0 : d ≠ 0 := (lt_of_le_of_lt zero_le hd1).ne'
    obtain ⟨hsub, hlog⟩ := gxDec hZ (A.gxAt Z) d hd
    have hw : GxCl Z (A.At Z) (ω ^ log ω d) := GxCl.opow hZ.1 hlog
    have hwd : ω ^ log ω d ≤ d := opow_log_le_self ω hd0
    rcases hwd.lt_or_eq with hwd' | hwd'
    · have hr := hsub _ hw hwd
      have hdr : ω ^ log ω d + (d - ω ^ log ω d) = d := Ordinal.add_sub_cancel_of_le hwd
      have hrd : d - ω ^ log ω d < d := by
        rcases (Ordinal.sub_le_self d (ω ^ log ω d)).lt_or_eq with h | h
        · exact h
        · exfalso
          have h1 : ω ^ log ω d + d = d := by conv_rhs => rw [← hdr]
                                              rw [h]
          have h2 := add_eq_right_iff_mul_omega0_le.1 h1
          rw [← opow_succ] at h2
          exact absurd (lt_opow_succ_log_self one_lt_omega0 d) (not_lt.2 h2)
      obtain ⟨s1, hs1⟩ := IH _ hwd' hw (hwd'.trans hdB)
      obtain ⟨s2, hs2⟩ := IH _ hrd hr (hrd.trans hdB)
      refine ⟨GdT.sm s1 s2, fun y hy hy1 hZy => ?_⟩
      obtain ⟨c1, v1⟩ := hs1 y hy hy1 hZy
      obtain ⟨c2, v2⟩ := hs2 y hy hy1 hZy
      refine ⟨⟨⟨c1.1, c2.1⟩, max_le c1.2 c2.2⟩, ?_⟩
      show GdT.val s1 y + GdT.val s2 y = _
      rw [v1, v2, ← gxTh_add hy (A.gxAt y) (A.cl_mono hZy hw), hdr]
    rcases (log_le_self ω d).lt_or_eq with hL | hL
    · obtain ⟨s, hs⟩ := IH _ hL hlog (hL.trans hdB)
      refine ⟨GdT.pw s, fun y hy hy1 hZy => ?_⟩
      obtain ⟨c1, v1⟩ := hs y hy hy1 hZy
      refine ⟨c1, ?_⟩
      show ω ^ GdT.val s y = _
      rw [v1, ← gxTh_opow hy (A.gxAt y) (A.cl_mono hZy hlog), hwd']
    have hdE : ω ^ d = d := by conv_lhs => rw [← hL]
                               exact hwd'
    have hdec : veblen (invVeblen₁ d) (invVeblen₂ d) = d := by rw [veblen_invVeblen₁_invVeblen₂, hdE]
    have hb1 : invVeblen₂ d < d := by have := invVeblen₂_lt d; rwa [hdE] at this
    obtain ⟨ha, hb⟩ := gxDecV hZ.1 (A.gxAt Z) hd _ _ hdec hb1
    set a := invVeblen₁ d with hadef
    set b := invVeblen₂ d with hbdef
    have ha0 : a ≠ 0 := by
      intro h0
      rw [h0, veblen_zero_apply] at hdec
      have e := hdE
      rw [← hdec] at e
      have e2 := (opow_right_inj one_lt_omega0).1 e
      rw [← hdec, e2] at hb1
      exact lt_irrefl _ hb1
    have hSC1 := ph_SC_Om1
    have haOO : a < cQ c n := by
      have hlt : veblen a b < veblen (cQ c n) (bQ (cQ c n)) := by rw [hdec]; exact hdB
      rcases veblen_lt_veblen_iff.1 hlt with ⟨h1, hb'⟩ | ⟨h', _⟩ | ⟨_, h'⟩
      · exfalso
        have hb0 : b = 0 := Order.lt_one_iff.1 (hb'.trans_le (bQ_le_one _))
        have hsc : veblen (cQ c n) 0 = cQ c n := bQ_ne_zero_iff.1 (pos_iff_ne_zero.1 (lt_of_le_of_lt zero_le hb'))
        have hdc' : d = cQ c n := by rw [← hdec, h1, hb0, hsc]
        cases n with
        | zero => exact hcd.ne' hdc'
        | succ m => exact cQ_succ_notSC hcO m hsc
      · exact h'
      · exact absurd (Order.lt_one_iff.1 (h'.trans_le (bQ_le_one _))) veblen_pos.ne'
    have hbv : b < veblen a b := by rw [hdec]; exact hb1
    -- a strongly critical code `d = φ(d, 0)` below `cQ c n`: a term of the stage `n`
    by_cases hdS : veblen a 0 = a ∧ b = 0
    · have hda : d = a := by rw [← hdec, hdS.2, hdS.1]
      obtain ⟨l, hlv⟩ := ihn Z d hgZ hd (hda ▸ haOO)
      refine ⟨l, fun y hy hy1 hZy => ?_⟩
      obtain ⟨c1, v1⟩ := hlv y hy hy1 hZy
      exact ⟨⟨c1.1, c1.2.trans (Nat.le_succ n)⟩, v1⟩
    have had : a < d := by
      refine lt_of_le_of_ne (hdec ▸ left_le_veblen a b) fun e => hdS ?_
      have h1 : veblen a 0 ≤ veblen a b := (veblen_le_veblen_iff_right).2 zero_le
      rw [hdec, ← e] at h1
      have h2 : veblen a 0 = a := le_antisymm h1 (left_le_veblen a 0)
      refine ⟨h2, ?_⟩
      by_contra hb0
      have h3 : veblen a 0 < veblen a b := (veblen_lt_veblen_iff_right).2 (pos_iff_ne_zero.2 hb0)
      rw [h2, hdec, ← e] at h3
      exact lt_irrefl _ h3
    rcases lt_or_ge a (Om 1) with haO | haO
    · have haZ : a < Z := GxCl.lt_of_lt_Om1 hZ (A.gxAt Z) ha haO
      have ha1 : 1 ≤ a := one_le_iff_ne_zero.2 ha0
      have hbO : Om 1 < b := by
        by_contra hle
        push Not at hle
        have h3 := (veblen_le_veblen_iff_right (o := a)).2 hle
        rw [hdec, hSC1.veblen_right haO] at h3
        exact absurd hd1 (not_lt.2 h3)
      obtain ⟨d', hd', hd'b, hdθ⟩ := zbIndCodeU hZ haZ hb hbO hbv
      obtain ⟨t, ht⟩ := IH d' (hd'b.trans_lt hb1) hd' ((hd'b.trans_lt hb1).trans hdB)
      refine ⟨GdT.th0 a t, fun y hy hy1 hZy => ?_⟩
      obtain ⟨ct, vt'⟩ := ht y hy hy1 hZy
      have hy1' := lp_y1 hy1
      have hay : a < y := haZ.trans_le hZy
      refine ⟨⟨⟨ha1, hay, ct.1⟩, max_le (Nat.succ_le_succ (Nat.zero_le n)) ct.2⟩, ?_⟩
      have hgy : B.g < y := hgZ.trans_le hZy
      show vt y (Om1 * a + GdT.val t y) = gxTh y (A.At y) d
      have hby := A.cl_mono hZy hb
      have hThd : gxTh y (A.At y) d = veblen a (gxTh y (A.At y) b) := by
        rw [← hdec, gxTh_veblen_lvl hy (A.gxAt y) hay hby]
      have hyb : y < gxTh y (A.At y) b := by
        have := gxTh_lt (GxCl.om (Z := y) (At := A.At y)) hbO; rwa [gxTh_Om1 hy hy1 (A.gxAt y)] at this
      have hbP : ¬ LuP (a + 1) (gxTh y (A.At y) b) := by
        intro hP
        have h1 := gxTh_lt hby hbv
        rw [gxTh_veblen_lvl hy (A.gxAt y) hay hby, luP_succ.1 hP] at h1
        exact lt_irrefl _ h1
      obtain ⟨htT, htlt⟩ := GdT.gd_T (gg_SC_eps hy) hy1' hgy t ct.1
      have hTv : GdT.val t y ∈ Tset y ∧ GdT.val t y < Om1 :=
        ⟨htT, htlt.trans (gdP_facts B (gg_SC_eps hy) hy1' hgy _).2.2.1⟩
      have e1 : GdT.val t y = luInd a y (gxTh y (A.At y) b) := by rw [vt', hdθ y hy hy1 hZy]
      rw [e1] at hTv ⊢
      rw [hThd, luPhLev hy hy1' ha1 hay _ hyb hbP hTv.1 hTv.2]
    · -- a level code `Ω₁ ≤ a < cQ c n`: the term `tl l t`
      obtain ⟨l, hlv⟩ := ihn Z a hgZ ha haOO
      have hl : ¬ GdT.noB l :=
        zbNotNoB hth hZ hZ1 ha haO (fun y hy hy1 hZy => (hlv y hy hy1 hZy).2)
      have hb0 : veblen a 0 = a → 0 < b := by
        intro hfa
        rcases eq_or_ne b 0 with hb0 | hb0
        · exact absurd ⟨hfa, hb0⟩ hdS
        · exact pos_iff_ne_zero.2 hb0
      obtain ⟨d', hd', hd'b, hdθ⟩ := zbIndCodeV hZ ha haO hb hb0 hbv
      obtain ⟨t, ht⟩ := IH d' (hd'b.trans_lt hb1) hd' ((hd'b.trans_lt hb1).trans hdB)
      refine ⟨GdT.tl l t, fun y hy hy1 hZy => ?_⟩
      obtain ⟨ct, vt'⟩ := ht y hy hy1 hZy
      obtain ⟨clc, clv⟩ := hlv y hy hy1 hZy
      have hyE : InE y := gg_SC_eps hy
      have hy1' := lp_y1 hy1
      have hgy : B.g < y := hgZ.trans_le hZy
      refine ⟨⟨⟨hl, clc.1, ct.1⟩, max_le (Nat.succ_le_succ clc.2) ct.2⟩, ?_⟩
      show vt y (Om1 * GdT.val l y + GdT.val t y) = gxTh y (A.At y) d
      have hby := A.cl_mono hZy hb
      have hay := A.cl_mono hZy ha
      have hThd : gxTh y (A.At y) d = veblen (gxTh y (A.At y) a) (gxTh y (A.At y) b) := by
        rw [← hdec, gxTh_phi hy (A.gxAt y) _ hay _ hby]
      have hyΘ : y ≤ gxTh y (A.At y) a := by
        rcases haO.lt_or_eq with h | h
        · have := gxTh_lt (GxCl.om (Z := y) (At := A.At y)) h
          rw [gxTh_Om1 hy hy1 (A.gxAt y)] at this; exact this.le
        · rw [← h, gxTh_Om1 hy hy1 (A.gxAt y)]
      have hβd : gxTh y (A.At y) a < veblen (gxTh y (A.At y) a) (gxTh y (A.At y) b) := by
        rw [← hThd]; exact gxTh_lt hay had
      have hbP : ¬ LuP (gxTh y (A.At y) a + 1) (gxTh y (A.At y) b) := by
        intro hP
        have h1 := gxTh_lt hby hbv
        rw [gxTh_phi hy (A.gxAt y) _ hay _ hby, luP_succ.1 hP] at h1
        exact lt_irrefl _ h1
      obtain ⟨htT, htlt⟩ := GdT.gd_T hyE hy1' hgy t ct.1
      have hTv : GdT.val t y ∈ Tset y ∧ GdT.val t y < Om1 :=
        ⟨htT, htlt.trans (gdP_facts B hyE hy1' hgy _).2.2.1⟩
      have e1 : GdT.val t y = lpInd (gxTh y (A.At y) a) y (gxTh y (A.At y) b) := by rw [vt', hdθ y hy hy1 hZy]
      rw [e1] at hTv ⊢
      have hLT := (GdT.gd_T hyE hy1' hgy l clc.1).1
      have hL1 := GdT.gd_lt_Om1 hyE hy1' hgy l clc.1
      have clv' : GdT.val l y = gxTh y (A.At y) a := clv
      rw [clv'] at hLT hL1
      have hβ1 : 1 ≤ gxTh y (A.At y) a := (lu_one_lt_E hyE).le.trans hyΘ
      rw [clv', hThd, lpPhLev hy hy1' hβ1 hLT hL1 _ (hyΘ.trans_lt hβd) hβd hbP hTv.1 hTv.2]

end Poly


end Ld

end Googology.Trans.PoR.InaccPsi.R2.Zb
