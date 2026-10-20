import Googology.Trans.PoR.InaccPsi.R2.LvLev
import Googology.Trans.PoR.InaccPsi.R2.LuPh

/-!
# `lvSys` has terms for every code below `φ(Ω₁ + Ω₁, 0)`, and its frontier lies below `L(0)`

For a strongly critical base `y < Ω₁` and a level `1 ≤ β < y + y` (`R2.LuPh` did this for the constant levels
`β < y`):

* `lvC`, `lvInd` (the index of `b` among the ordinals `x` off `P_{β+1}` with `y < φ_β(x)`), `lvInd_P`, `lvInd_above`,
  `lvInd_low_gt`, `lvInd_low_eq`;
* `lvPhLev` (**THE LEVEL LEMMA at every level `β ∈ Tʸ ∩ Ω₁`, `1 ≤ β`, below every member of `P_β` above `y`**):
  `φ_β(b) = ϑʸ(Ω₁·β + ind(b))` for `b` off `P_{β+1}` with `y < φ_β(b)` and `ind(b) ∈ Tʸ ∩ Ω₁` (from `R2.LvLev`);
* `lvIndCode` (**the index of a code is a code**, for a level `Ω₁ + a`, `a < Z`), `lvTc := φ(Ω₁ + Ω₁, 0)` (the code of
  the top), `lvTh_T` (**`Θ_y(φ(Ω₁ + Ω₁, 0)) = φ(y + y, 0) = ϑʸ(Ω₁·(y + y))`**), `lvPoly` (**`GgPoly lvSys lvTc`**: a
  code `c < φ(Ω₁ + Ω₁, 0)` over `Z` is a constant, `Ω₁`, a sum, a power, `φ_a(b)` with a constant level `1 ≤ a < Z`
  (the term `th0 a t`, by `Lu.luIndCode`, `Lu.luPhLev`), or `φ_{Ω₁+a}(b)` with `a < Z` (the term `th a t`));
* `lv_fr` (**`Λ(lvSys) ≤ ι(ω^{φ(Ω₁+Ω₁,0)})`, `Λ⁺(lvSys) ≤ ι(ω^{φ(Ω₁+Ω₁,0)}·ω) < L(0)`, `υ_{Λ⁺(lvSys)} < L(0)`**, by
  THEOREM UNI, `Ph.phFrGen`), `lv_fr_order` (**`ρ` of `Λ⁺(luSys)` < `ρ` of `Λ(lvSys)` < `ρ` of `Λ⁺(lvSys)` < `L(0) = m*
  ≤ L(n+1) < L(ω) < L(ω+1)`**).

No new axiom beyond `R2.CitedLu` and `R2.CitedLv`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ph Lu

/-! ## The index of `b` among the ordinals `x` off `P_{β+1}` with `y < φ_β(x)` -/

/-- The ordinals `x` off `P_{β+1}` with `y < φ_β(x)`. -/
def lvC (β y : Ordinal.{0}) : Set Ordinal.{0} := {x | y < veblen β x ∧ ¬ LuP (β + 1) x}

/-- The index of `b` in `lvC β y`. -/
noncomputable def lvInd (β y b : Ordinal.{0}) : Ordinal.{0} := cdOtp (lvC β y) b

section Index

variable {β y : Ordinal.{0}}

theorem mem_lvC_of {x : Ordinal.{0}} (hyx : y < x) (hP : ¬ LuP (β + 1) x) : x ∈ lvC β y :=
  ⟨hyx.trans_le (right_le_veblen _ _), hP⟩

/-- **`ind(p) = p`** for `p ∈ P_{β+1}` above `y`. -/
theorem lvInd_P : ∀ p, LuP (β + 1) p → y < p → lvInd β y p = p := by
  intro p
  induction p using WellFoundedLT.induction with
  | ind p IH =>
  intro hP hyp
  refine le_antisymm (cdOtp_le_self _ p) (le_of_forall_lt fun α hα => ?_)
  by_cases hex : ∃ p', LuP (β + 1) p' ∧ max α y < p' ∧ p' < p
  · obtain ⟨p', hP', hm, hp'⟩ := hex
    calc α < p' := (le_max_left α y).trans_lt hm
      _ = lvInd β y p' := (IH p' hp' hP' ((le_max_right α y).trans_lt hm)).symm
      _ ≤ lvInd β y p := cdOtp_mono _ hp'.le
  · push Not at hex
    have hmp : max α y < p := max_lt hα hyp
    have hm1 : max α y + 1 < p := by rw [← succ_eq_add_one]; exact (lu_P_lim hP).succ_lt hmp
    have hprin : IsPrincipal (· + ·) p := by
      have hE' : ω ^ p = p := lu_P_E hP
      rw [← hE']; exact isPrincipal_add_omega0_opow p
    have e : max α y + 1 + p = p := hprin.add_eq_right hm1
    have hsh := phOtp_shift (lvC β y) (max α y + 1) p fun z hz => by
      refine mem_lvC_of (lt_of_le_of_lt (le_max_right α y) ((lt_add_one _).trans_le le_self_add)) fun hz' => ?_
      have h1 := hex _ hz' ((lt_add_one _).trans_le le_self_add)
      have h2 : max α y + 1 + z < max α y + 1 + p := (add_lt_add_iff_left _).2 hz
      rw [e] at h2
      exact absurd h1 (not_le.2 h2)
    rw [e] at hsh
    show α < cdOtp (lvC β y) p
    rw [hsh]
    exact hα.trans_le le_add_self

/-- **`ind(p + 1 + δ) = p + δ`** for `p ∈ P_{β+1}` above `y` and no member of `P_{β+1}` in `(p, p + 1 + δ)`. -/
theorem lvInd_above {p δ : Ordinal.{0}} (hP : LuP (β + 1) p) (hyp : y < p)
    (h : ∀ z < δ, ¬ LuP (β + 1) (p + 1 + z)) : lvInd β y (p + 1 + δ) = p + δ := by
  have e1 : cdOtp (lvC β y) p = cdOtp (lvC β y) (p + 1) :=
    cdOtp_eq_of_gap _ le_self_add fun c hc hpc hcp => by
      have hcp' : c = p := le_antisymm (Order.lt_add_one_iff.1 hcp) hpc
      exact hc.2 (hcp' ▸ hP)
  have e2 : cdOtp (lvC β y) p = p := lvInd_P p hP hyp
  show cdOtp (lvC β y) (p + 1 + δ) = p + δ
  rw [phOtp_shift _ _ δ fun z hz => mem_lvC_of (hyp.trans ((lt_add_one p).trans_le le_self_add)) (h z hz),
    ← e1, e2]

/-- **`ind(δ) = δ`** when `y < φ_β(0)` and no member of `P_{β+1}` lies below `δ`. -/
theorem lvInd_low_gt {δ : Ordinal.{0}} (hy0 : y < veblen β 0) (h : ∀ z < δ, ¬ LuP (β + 1) z) :
    lvInd β y δ = δ := by
  unfold lvInd
  have := phOtp_shift (lvC β y) 0 δ fun z hz => by
    rw [zero_add]
    exact ⟨hy0.trans_le ((veblen_le_veblen_iff_right).2 zero_le), h z hz⟩
  rwa [zero_add, ggOtp_zero, zero_add] at this

/-- **`ind(1 + δ) = δ`** when `φ_β(0) = y` and no member of `P_{β+1}` lies in `[1, 1 + δ)`. -/
theorem lvInd_low_eq {δ : Ordinal.{0}} (hy0 : veblen β 0 = y) (h : ∀ z < δ, ¬ LuP (β + 1) (1 + z)) :
    lvInd β y (1 + δ) = δ := by
  unfold lvInd
  have hlow : cdOtp (lvC β y) 1 = 0 := phOtp_low _ fun c hc => by
    rcases eq_or_ne c 0 with rfl | hc0
    · exact absurd (hy0 ▸ hc.1) (lt_irrefl _)
    · exact one_le_iff_ne_zero.2 hc0
  rw [phOtp_shift (lvC β y) 1 δ fun z hz => ⟨by
      rw [← hy0]; exact (veblen_lt_veblen_iff_right).2 (lt_of_lt_of_le zero_lt_one le_self_add), h z hz⟩,
    hlow, zero_add]

end Index

/-- A member of `P_β` above `y` is above a level `β ≥ 1` that is `≤ y` or not additive principal. -/
theorem lv_level_lt_P' {β y u : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβ : β ≤ y ∨ ¬ Indec β) (hPu : LuP β u)
    (hyu : y < u) : β < u := by
  have huE : InE u := luP_E hβ1 hPu
  obtain ⟨j, rfl⟩ := hPu
  refine lt_of_le_of_ne (left_le_veblen _ _) fun e => ?_
  rcases hβ with h | h
  · exact absurd (e ▸ hyu) (not_lt.2 h)
  · exact h (e ▸ inE_indec huE)

/-- A member of `P_β` above `y` is above the level `β < y + y`. -/
theorem lv_level_lt_P {β y u : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβ : β < y + y) (hPu : LuP β u) (hyu : y < u) :
    β < u := by
  refine lv_level_lt_P' hβ1 ?_ hPu hyu
  rcases le_or_gt β y with h | h
  · exact Or.inl h
  · exact Or.inr fun hI => absurd (hI.add_lt h h) (not_lt.2 hβ.le)

/-- **THE LEVEL LEMMA at every level `β ∈ Tʸ ∩ Ω₁`, `1 ≤ β`, below the members of `P_β` above `y`**: for a strongly
critical `y < Ω₁` and `b` off `P_{β+1}` with `y < φ_β(b)` and `ind(b) ∈ Tʸ ∩ Ω₁`, `φ_β(b) = ϑʸ(Ω₁·β + ind(b))`. -/
theorem lvPhLev {β y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om1) (hβ1 : 1 ≤ β) (hβT : β ∈ Tset y)
    (hβΩ : β < Om1) (hβu : ∀ u, LuP β u → y < u → β < u) :
    ∀ b, y < veblen β b → ¬ LuP (β + 1) b → lvInd β y b ∈ Tset y → lvInd β y b < Om1 →
      veblen β b = vt y (Om1 * β + lvInd β y b) := by
  have hyE : InE y := gg_SC_eps hy
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hyb hbP hT h1
  have hbv : b < veblen β b :=
    lt_of_le_of_ne (right_le_veblen _ _) (fun e => hbP (luP_succ.2 e.symm))
  apply le_antisymm
  · have hfacts := ul_facts hyE hy1 hβ1 hβT hβΩ hT h1
    have hnP := lv_th_notP hyE hy1 hβ1 hβT hβΩ hT h1
    obtain ⟨b', hb'⟩ := lv_th_P hyE hy1 β hβ1 hβT hβΩ _ hT h1
    have hyb' : y < veblen β b' := by rw [hb']; exact hfacts.2.2.2.1
    have hb'P : ¬ LuP (β + 1) b' := by
      intro hP
      have hfx : veblen β b' = b' := luP_succ.1 hP
      apply hnP
      rw [← hb', hfx]; exact hP
    rcases lt_or_ge b' b with hlt | hge
    · exfalso
      have hmem : b' ∈ lvC β y := ⟨hyb', hb'P⟩
      have hlt' : lvInd β y b' < lvInd β y b := cdOtp_lt_of_mem hmem hlt
      have hT' := vz_T_down hyE hy1 hT h1 hlt'.le
      have e := IH b' hlt hyb' hb'P hT' (hlt'.trans h1)
      have h3 := ul_eta_lt hyE hy1 hβ1 hβT hβΩ hT' hT h1 hlt'
      rw [← e, hb'] at h3
      exact lt_irrefl _ h3
    · rw [← hb']; exact veblen_le_veblen_iff_right.2 hge
  · refine lv_th_min hyE hy1 hβ1 hβT hβΩ hT h1 (luP_veblen β b) hyb
      ((cdOtp_le_self _ b).trans_lt hbv) (hβu _ (luP_veblen β b) hyb) fun σ hσ => ?_
    obtain ⟨b', hb'C, hb'b, hσe⟩ := ggOtp_onto (lvC β y) b σ hσ
    obtain ⟨hyb', hb'P⟩ := hb'C
    have hσe' : lvInd β y b' = σ := hσe
    have hT' : lvInd β y b' ∈ Tset y := by rw [hσe']; exact vz_T_down hyE hy1 hT h1 hσ.le
    rw [← hσe', ← IH b' hb'b hyb' hb'P hT' (by rw [hσe']; exact hσ.trans h1)]
    exact veblen_lt_veblen_iff_right.2 hb'b

/-! ## Codes -/

section Codes

variable {Z : Ordinal.{0}}

/-- `φ_{Ω₁+a}` read over `y`: `Θ_y(φ_{Ω₁+a}(b)) = φ_{y+a}(Θ_y(b))` for `a < y`. -/
theorem lvTh_veblen_lvl {y a b : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) (ha : a < y) (hb : GgCl y b) :
    ggTh y (veblen (Om 1 + a) b) = veblen (y + a) (ggTh y b) := by
  rw [phTh_phi hy _ (GgCl.add GgCl.om (GgCl.small ha)) b hb, ggTh_add hy GgCl.om, ggTh_Om1 hy hy1,
    ggTh_small ha.le]

/-- **The index of a code is a code** (a level `Ω₁ + a`, `a < Z`). -/
theorem lvIndCode (hZ : SC Z) {a b : Ordinal.{0}} (haZ : a < Z) (hb : GgCl Z b) (hb0 : a = 0 → 0 < b)
    (hbv : b < veblen (Om 1 + a) b) :
    ∃ d, GgCl Z d ∧ d ≤ b ∧ ∀ y, SC y → y < Om 1 → Z ≤ y → ggTh y d = lvInd (y + a) y (ggTh y b) := by
  have ha : GgCl Z (Om 1 + a) := GgCl.add GgCl.om (GgCl.small haZ)
  have ha1 : GgCl Z (Om 1 + a + 1) := GgCl.add ha (GgCl.small (gg_one_lt_of_SC hZ))
  have hq : GgCl Z (veblen (Om 1 + a + 1) 0) := GgCl.phi ha1 (GgCl.zero hZ.1)
  have hqP : LuP (Om 1 + a + 1) (veblen (Om 1 + a + 1) 0) := luP_veblen _ _
  have hThq : ∀ y, SC y → y < Om 1 → Z ≤ y → ggTh y (veblen (Om 1 + a + 1) 0) = veblen (y + a + 1) 0 :=
    fun y hy hy1 hZy => by
      rw [phTh_phi hy _ (ha1.mono hZy) _ (GgCl.zero hy.1), ggTh_add hy (ha.mono hZy), ggTh_add hy GgCl.om,
        ggTh_Om1 hy hy1, ggTh_small (haZ.le.trans hZy), ggTh_small (gg_one_lt_of_SC hy).le, phTh_zero]
  have hPy : ∀ y v, LuP (y + a + 1) v → veblen (y + a + 1) 0 ≤ v := by
    intro y v hv
    obtain ⟨γ, rfl⟩ := hv
    exact veblen_le_veblen_iff_right.2 zero_le
  rcases lt_or_ge b (veblen (Om 1 + a + 1) 0) with hbq | hbq
  · -- below the first member of `P_{Ω₁+a+1}`: no member of `P_{y+a+1}` below `Θ_y(b)`
    have hnoP : ∀ y, SC y → y < Om 1 → Z ≤ y → ∀ z, z < ggTh y b → ¬ LuP (y + a + 1) z := by
      intro y hy hy1 hZy z hz hP
      have h1 := ggTh_lt (hb.mono hZy) hbq (y := y)
      rw [hThq y hy hy1 hZy] at h1
      exact absurd (hPy y z hP) (not_le.2 (hz.trans h1))
    rcases eq_or_ne a 0 with ha0 | ha0
    · have hb0' := hb0 ha0
      have hb1 : 1 ≤ b := one_le_iff_pos.2 hb0'
      refine ⟨b - 1, (ggDec hZ b hb).1 1 (GgCl.small (gg_one_lt_of_SC hZ)) hb1, Ordinal.sub_le_self _ _,
        fun y hy hy1 hZy => ?_⟩
      have hbe : ggTh y b = 1 + ggTh y (b - 1) := by
        conv_lhs => rw [← Ordinal.add_sub_cancel_of_le hb1]
        rw [ggTh_add hy (GgCl.small (gg_one_lt_of_SC hy)), ggTh_small (gg_one_lt_of_SC hy).le]
      have hn := hnoP y hy hy1 hZy
      subst ha0
      rw [add_zero] at hn ⊢
      rw [hbe]
      refine (lvInd_low_eq hy.veblen_zero fun z hz => hn (1 + z) ?_).symm
      rw [hbe]
      exact (add_lt_add_iff_left 1).2 hz
    · refine ⟨b, hb, le_rfl, fun y hy hy1 hZy => ?_⟩
      have hy0 : y < veblen (y + a) 0 := by
        calc y = veblen y 0 := hy.veblen_zero.symm
          _ < veblen (y + a) 0 := veblen_zero_lt_veblen_zero.2 (lt_add_of_pos_right y (pos_iff_ne_zero.2 ha0))
      exact (lvInd_low_gt hy0 (hnoP y hy hy1 hZy)).symm
  · have hqb : veblen (Om 1 + a + 1) 0 < b := lt_of_le_of_ne hbq fun e => by
      have h1 : veblen (Om 1 + a) (veblen (Om 1 + a + 1) 0) = veblen (Om 1 + a + 1) 0 :=
        veblen_veblen_of_lt (lt_add_one _) _
      rw [← e] at hbv; rw [h1] at hbv; exact lt_irrefl _ hbv
    obtain ⟨c, n, hc, hdc, hbc, hθc⟩ := phSplit hZ b hb
    have hqc : veblen (Om 1 + a + 1) 0 ≤ c := by
      by_contra hlt
      push Not at hlt
      have key : c + n < veblen (Om 1 + a + 1) 0 + (0 : ℕ) := by
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
        _ < veblen (Om 1 + a + 1) 0 :=
          veblen_zero_lt_veblen_zero.2 ((le_self_add).trans_lt (lt_add_one _))
    have hThp : ∀ y, SC y → y < Om 1 → Z ≤ y → y < ggTh y c := fun y hy hy1 hZy => by
      have := ggTh_lt (GgCl.om (Z := y)) hc1 (y := y); rwa [ggTh_Om1 hy hy1] at this
    by_cases hfa : veblen (Om 1 + a) c = c
    · -- `b = c + n`, `c ∈ P_{Ω₁+a+1}`: `d = c + (n - 1)`
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [Nat.cast_zero, add_zero] at hbc
        rw [hbc, hfa] at hbv; exact lt_irrefl _ hbv
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      refine ⟨c + m, GgCl.add hc (ph_cl_nat hZ m), ?_, fun y hy hy1 hZy => ?_⟩
      · rw [hbc]; exact (add_le_add_iff_left _).2 (by exact_mod_cast Nat.le_succ m)
      · have hcy := hc.mono hZy
        have hP : LuP (y + a + 1) (ggTh y c) := by
          refine luP_succ.2 ?_
          rw [← lvTh_veblen_lvl hy hy1 (haZ.trans_le hZy) hcy, hfa]
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
      have hβP : ¬ LuP (y + a + 1) β := by
        intro hP
        have h1 := ggTh_lt hby hbv
        rw [lvTh_veblen_lvl hy hy1 hay hby, ← hβ, luP_succ.1 hP] at h1
        exact lt_irrefl _ h1
      set s := {v | LuP (y + a + 1) v ∧ v < β} with hs
      have hqs : ggTh y (veblen (Om 1 + a + 1) 0) ∈ s :=
        ⟨by rw [hThq y hy hy1 hZy]; exact luP_veblen _ _, ggTh_lt (hq.mono hZy) hqb⟩
      have hne : s.Nonempty := ⟨_, hqs⟩
      have hbdd : BddAbove s := ⟨β, fun v hv => hv.2.le⟩
      have hpP : LuP (y + a + 1) (sSup s) := by
        refine luP_succ.2 ?_
        rw [(isNormal_veblen (y + a)).map_sSup hne hbdd]
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
          _ < veblen (y + a + 1) 0 :=
            veblen_zero_lt_veblen_zero.2 ((le_self_add).trans_lt (lt_add_one _))
      set p := sSup s with hp
      have hδ : p + 1 + (β - (p + 1)) = β := Ordinal.add_sub_cancel_of_le (Order.add_one_le_of_lt hpβ)
      have hgap : ∀ z < β - (p + 1), ¬ LuP (y + a + 1) (p + 1 + z) := by
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
        refine phTh_inj (GgCl.phi (GgCl.add GgCl.om (GgCl.small hay)) hcy) hcy ?_
        rw [lvTh_veblen_lvl hy hy1 hay hcy, e2]
        exact luP_succ.1 hpP
      conv_rhs => rw [← hδ]
      rw [lvInd_above hpP hyp hgap]
      conv_lhs => rw [← hδ]
      rw [add_assoc p 1, one_add_of_omega0_le hω]

/-- **The code of the top**: `φ(Ω₁ + Ω₁, 0)`. -/
noncomputable def lvTc : Ordinal.{0} := veblen (Om 1 + Om 1) 0

theorem lv_cl_T (hZ : SC Z) : GgCl Z lvTc := GgCl.phi (GgCl.add GgCl.om GgCl.om) (GgCl.zero hZ.1)

theorem lv_Om1_le_T : Om 1 ≤ lvTc := le_self_add.trans (left_le_veblen _ _)

theorem lv_T_lt_Gam : lvTc < ggGam := by
  have hp := isPrincipal_add_omega0_opow ggGam
  rw [gg_SC_eps ggGam_spec.1] at hp
  exact ggGam_spec.1.2 _ (hp ggGam_spec.2 ggGam_spec.2) _ ggGam_spec.1.1

/-- **`Θ_y(φ(Ω₁ + Ω₁, 0)) = φ(y + y, 0) = ϑʸ(Ω₁·(y + y))`** for a strongly critical `y < Ω₁`. -/
theorem lvTh_T {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) : ggTh y lvTc = lvTop y := by
  have hyE : InE y := gg_SC_eps hy
  have hy1' : y < Om1 := by rw [ph_Om1_eq]; exact hy1
  unfold lvTc
  rw [phTh_phi hy _ (GgCl.add GgCl.om GgCl.om) _ (GgCl.zero hy.1), ggTh_add hy GgCl.om, ggTh_Om1 hy hy1,
    phTh_zero]
  apply le_antisymm
  · obtain ⟨j, hj⟩ := lv_top_P hyE hy1'
    rw [← hj]
    exact (veblen_le_veblen_iff_right).2 zero_le
  · refine lv_top_least hyE hy1' (luP_veblen (y + y) 0) ?_
    calc y = veblen y 0 := hy.veblen_zero.symm
      _ < veblen (y + y) 0 := veblen_zero_lt_veblen_zero.2 (lt_add_of_pos_right y hy.1)

/-- **`lvSys` has terms for every code below `φ(Ω₁ + Ω₁, 0)`.** -/
theorem lvPoly : GgPoly lvSys lvTc := by
  refine phPoly_of_SC fun Z hZ _ => ?_
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hcB
  rcases lt_trichotomy c (Om 1) with hc1 | hc1 | hc1
  · have hcZ : c < Z := hc.lt_of_lt_Om1 hZ hc1
    exact ⟨LvT.cst c, fun y _ _ hZy =>
      ⟨lt_of_lt_of_le hcZ hZy, by show c = ggTh y c; rw [ggTh_small (hcZ.le.trans hZy)]⟩⟩
  · subst hc1
    exact ⟨LvT.bs, fun y hy hy1 _ => ⟨trivial, by show y = ggTh y (Om 1); rw [ggTh_Om1 hy hy1]⟩⟩
  have hc0 : c ≠ 0 := (lt_of_le_of_lt zero_le hc1).ne'
  obtain ⟨hsub, hlog⟩ := ggDec hZ c hc
  have hw : GgCl Z (ω ^ log ω c) := GgCl.opow hZ.1 hlog
  have hwc : ω ^ log ω c ≤ c := opow_log_le_self ω hc0
  rcases hwc.lt_or_eq with hwc' | hwc'
  · -- a sum `ω^L + r`
    have hr := hsub _ hw hwc
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
    refine ⟨LvT.sm s1 s2, fun y hy hy1 hZy => ?_⟩
    obtain ⟨c1, v1⟩ := hs1 y hy hy1 hZy
    obtain ⟨c2, v2⟩ := hs2 y hy hy1 hZy
    refine ⟨⟨c1, c2⟩, ?_⟩
    show lvSys.val s1 y + lvSys.val s2 y = _
    rw [v1, v2, ← ggTh_add hy (hw.mono hZy), hcr]
  rcases (log_le_self ω c).lt_or_eq with hL | hL
  · -- a power `ω^L`, `L < c`
    obtain ⟨s, hs⟩ := IH _ hL hlog (hL.trans hcB)
    refine ⟨LvT.pw s, fun y hy hy1 hZy => ?_⟩
    obtain ⟨c1, v1⟩ := hs y hy hy1 hZy
    refine ⟨c1, ?_⟩
    show ω ^ lvSys.val s y = _
    rw [v1, ← ggTh_opow hy (hlog.mono hZy), hwc']
  -- an `ε`-number: `c = φ_a(b)`
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
  have haOO : a < Om 1 + Om 1 := by
    have hlt : veblen a b < veblen (Om 1 + Om 1) 0 := by rw [hdec]; exact hcB
    rcases veblen_lt_veblen_iff.1 hlt with ⟨_, hb'⟩ | ⟨h', _⟩ | ⟨_, h'⟩
    · exact absurd hb' (not_lt.2 zero_le)
    · exact h'
    · exact absurd h' (not_lt.2 zero_le)
  have hbv : b < veblen a b := by rw [hdec]; exact hb1
  rcases lt_or_ge a (Om 1) with haO | haO
  · -- a constant level `1 ≤ a < Z`: the term `th0 a t`
    have haZ : a < Z := ha.lt_of_lt_Om1 hZ haO
    have ha1 : 1 ≤ a := one_le_iff_ne_zero.2 ha0
    have hbO : Om 1 < b := by
      by_contra hle
      push Not at hle
      have h3 := (veblen_le_veblen_iff_right (o := a)).2 hle
      rw [hdec, hSC1.veblen_right haO] at h3
      exact absurd hc1 (not_lt.2 h3)
    obtain ⟨d, hd, hdb, hdθ⟩ := luIndCode hZ haZ hb hbO hbv
    obtain ⟨t, ht⟩ := IH d (hdb.trans_lt hb1) hd ((hdb.trans_lt hb1).trans hcB)
    refine ⟨LvT.th0 a t, fun y hy hy1 hZy => ?_⟩
    obtain ⟨ct, vt'⟩ := ht y hy hy1 hZy
    have hy1' : y < Om1 := by rw [ph_Om1_eq]; exact hy1
    have hay : a < y := haZ.trans_le hZy
    refine ⟨⟨ha1, hay, ct⟩, ?_⟩
    show vt y (Om1 * a + lvSys.val t y) = ggTh y c
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
    obtain ⟨htT, htlt⟩ := LvT.lv_T (gg_SC_eps hy) hy1' t ct
    have hTv : lvSys.val t y ∈ Tset y ∧ lvSys.val t y < Om1 :=
      ⟨htT, htlt.trans (LvT.lvTop_facts (gg_SC_eps hy) hy1').2.2.2.2.1⟩
    have e1 : lvSys.val t y = luInd a y (ggTh y b) := by rw [vt', hdθ y hy hy1 hZy]
    rw [e1] at hTv ⊢
    rw [hThc, luPhLev hy hy1' ha1 hay _ hyb hbP hTv.1 hTv.2]
  · -- a level `Ω₁ + a'`, `a' < Z`: the term `th a' t`
    have ha'e : Om 1 + (a - Om 1) = a := Ordinal.add_sub_cancel_of_le haO
    have ha'O : a - Om 1 < Om 1 := (add_lt_add_iff_left (Om 1)).1 (by rw [ha'e]; exact haOO)
    have ha'c : GgCl Z (a - Om 1) := (ggDec hZ a ha).1 _ GgCl.om haO
    have ha'Z : a - Om 1 < Z := ha'c.lt_of_lt_Om1 hZ ha'O
    have hbv' : b < veblen (Om 1 + (a - Om 1)) b := by rw [ha'e]; exact hbv
    have hb0 : a - Om 1 = 0 → 0 < b := by
      intro h0
      rw [h0, add_zero] at ha'e
      rcases eq_or_ne b 0 with hb0 | hb0
      · exfalso
        rw [← ha'e, hb0, hSC1.veblen_zero] at hdec
        rw [← hdec] at hc1
        exact lt_irrefl _ hc1
      · exact pos_iff_ne_zero.2 hb0
    obtain ⟨d, hd, hdb, hdθ⟩ := lvIndCode hZ ha'Z hb hb0 hbv'
    obtain ⟨t, ht⟩ := IH d (hdb.trans_lt hb1) hd ((hdb.trans_lt hb1).trans hcB)
    refine ⟨LvT.th (a - Om 1) t, fun y hy hy1 hZy => ?_⟩
    obtain ⟨ct, vt'⟩ := ht y hy hy1 hZy
    have hyE : InE y := gg_SC_eps hy
    have hy1' : y < Om1 := by rw [ph_Om1_eq]; exact hy1
    have hay : a - Om 1 < y := ha'Z.trans_le hZy
    refine ⟨⟨hay, ct⟩, ?_⟩
    show vt y (Om1 * (y + (a - Om 1)) + lvSys.val t y) = ggTh y c
    have hby := hb.mono hZy
    have hThc : ggTh y c = veblen (y + (a - Om 1)) (ggTh y b) := by
      rw [← hdec, ← ha'e, lvTh_veblen_lvl hy hy1 hay hby, ha'e]
    have hyb : y < veblen (y + (a - Om 1)) (ggTh y b) := by
      rcases eq_or_ne (a - Om 1) 0 with h0 | h0
      · rw [h0, add_zero]
        have hpos : 0 < ggTh y b := by
          have := ggTh_lt (GgCl.zero hy.1) (hb0 h0) (y := y); rwa [phTh_zero] at this
        calc y = veblen y 0 := hy.veblen_zero.symm
          _ < veblen y (ggTh y b) := (veblen_lt_veblen_iff_right).2 hpos
      · calc y = veblen y 0 := hy.veblen_zero.symm
          _ < veblen (y + (a - Om 1)) 0 :=
            veblen_zero_lt_veblen_zero.2 (lt_add_of_pos_right y (pos_iff_ne_zero.2 h0))
          _ ≤ veblen (y + (a - Om 1)) (ggTh y b) := (veblen_le_veblen_iff_right).2 zero_le
    have hbP : ¬ LuP (y + (a - Om 1) + 1) (ggTh y b) := by
      intro hP
      have h1 := ggTh_lt hby hbv'
      rw [lvTh_veblen_lvl hy hy1 hay hby, luP_succ.1 hP] at h1
      exact lt_irrefl _ h1
    obtain ⟨htT, htlt⟩ := LvT.lv_T hyE hy1' t ct
    have hTv : lvSys.val t y ∈ Tset y ∧ lvSys.val t y < Om1 :=
      ⟨htT, htlt.trans (LvT.lvTop_facts hyE hy1').2.2.2.2.1⟩
    have e1 : lvSys.val t y = lvInd (y + (a - Om 1)) y (ggTh y b) := by rw [vt', hdθ y hy hy1 hZy]
    rw [e1] at hTv ⊢
    have hβ1 : 1 ≤ y + (a - Om 1) := (lu_one_lt_E hyE).le.trans le_self_add
    have hβ : y + (a - Om 1) < y + y := (add_lt_add_iff_left y).2 hay
    obtain ⟨hTT, hT1⟩ := lv_tt hyE hy1'
    rw [hThc, lvPhLev hy hy1' hβ1 (vz_T_down hyE hy1' hTT hT1 hβ.le) (hβ.trans hT1)
      (fun u hPu hyu => lv_level_lt_P hβ1 hβ hPu hyu) _ hyb hbP hTv.1 hTv.2]

end Codes

/-! ## The frontier lies below `L(0)` -/

variable {S : InaccSeq.{0}}

/-- **The frontier of `lvSys`**: every `ι(ω^{φ(Ω₁+Ω₁,0)}·(n+1))` is a frontier, `Λ(lvSys) ≤ ι(ω^{φ(Ω₁+Ω₁,0)})`,
`Λ⁺(lvSys) ≤ ι(ω^{φ(Ω₁+Ω₁,0)}·ω) < L(0)` and `υ_{Λ⁺(lvSys)} < L(0)`. -/
theorem lv_fr :
    (∀ n : ℕ, XtFr lvSys (iota S (ω ^ lvTc * ((n : Ordinal.{0}) + 1))) ∧
      upsilon (iota S (ω ^ lvTc * ((n : Ordinal.{0}) + 1))) = iota S (ω ^ lvTc * ((n : Ordinal.{0}) + 1))) ∧
    xtLam lvSys ≤ iota S (ω ^ lvTc) ∧ xtB1 lvSys ≤ iota S (ω ^ lvTc * ω) ∧
    iota S (ω ^ lvTc * ω) < Nc.ncL S 0 ∧ upsilon (xtB1 lvSys) < Nc.ncL S 0 :=
  phFrGen lv_T_lt_Gam (phPolyR_of lvPoly) (fun _ hy hy1 => (lvTh_T hy hy1).symm) (fun _ hZ => lv_cl_T hZ)
    lv_Om1_le_T

/-- **Where the frontier lies**: `ρ` of `Λ⁺(luSys)` < `ρ` of `Λ(lvSys)` < `ρ` of `Λ⁺(lvSys)` < `L(0) = m* ≤ L(n+1) <
`L(ω) < L(ω+1)`, and `Λ⁺(lvSys) < L(ω+1)`, unconditionally. -/
theorem lv_fr_order (n : ℕ) :
    upsilon (xtB1 luSys) < upsilon (xtLam lvSys) ∧ upsilon (xtLam lvSys) < upsilon (xtB1 lvSys) ∧
    upsilon (xtB1 lvSys) < Nc.ncL S 0 ∧ Nc.ncL S 0 ≤ Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ∧
    Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) < Nc.ncL S ω ∧ Nc.ncL S ω < Nc.ncL S (ω + 1) ∧
    xtB1 lvSys < Nc.ncL S (ω + 1) := by
  obtain ⟨h0, h1, h2⟩ := phL_chain (S := S) n
  have hU := (lv_fr (S := S)).2.2.2.2
  refine ⟨upsilon_normal.strictMono lvLam_gt, upsilon_normal.strictMono lv_lamLtB1, hU, h0, h1, h2, ?_⟩
  exact upsilon_normal.strictMono.le_apply.trans_lt (((hU.trans_le h0).trans h1).trans h2)

end Googology.Trans.PoR.InaccPsi.R2
