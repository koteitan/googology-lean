import Googology.Trans.PoR.InaccPsi.R2.LpPh

/-!
# The level lemma at every level, strongly critical levels included, and the index of a code is a code

* `lpC β y = {x | y < φ_β(x), β < φ_β(x), x ∉ P_{β+1}}`, `lpInd β y b` (the index of `b` in it), `lpInd_P`,
  `lpInd_above`, `lpInd_low_gt`, `lpInd_low_eq`;
* `lpPhLev` (**THE LEVEL LEMMA at every level `1 ≤ β ∈ Tʸ ∩ Ω₁`**, without the hypothesis of `R2.LvPh.lvPhLev` that
  no member of `P_β` above `y` is `≤ β`: `φ_β(b) = ϑʸ(Ω₁·β + ind(b))` for `b` off `P_{β+1}` with `y < φ_β(b)`,
  `β < φ_β(b)`, `ind(b) ∈ Tʸ ∩ Ω₁`; at a strongly critical level `β = Γ_{y+1}` it gives `φ_β(1 + δ) =
  ϑʸ(Ω₁·β + δ)`);
* `lpTh_veblen_lvl`, `lpIndCodeU` (**the index of a code is a code**, a constant level `a < Z`, codes `LgCl`),
  `lpIndCodeV` (**the same for a level code `a ≥ Ω₁`**, strongly critical levels `φ(a, 0) = a` included).

No new axiom beyond the cited facts already in the repo.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Lp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph Lu
  Googology.Trans.PoR.InaccPsi.R2.Cd

/-! ## The index of `b` among the ordinals `x` off `P_{β+1}` with `y, β < φ_β(x)` -/

/-- The ordinals `x` off `P_{β+1}` with `y < φ_β(x)` and `β < φ_β(x)`. -/
def lpC (β y : Ordinal.{0}) : Set Ordinal.{0} := {x | y < veblen β x ∧ β < veblen β x ∧ ¬ LuP (β + 1) x}

/-- The index of `b` in `lpC β y`. -/
noncomputable def lpInd (β y b : Ordinal.{0}) : Ordinal.{0} := cdOtp (lpC β y) b

section Index

variable {β y : Ordinal.{0}}

/-- `β < φ_β(x)` for `x > 0`. -/
theorem lp_lvl_lt {x : Ordinal.{0}} (hx : 0 < x) : β < veblen β x :=
  (left_le_veblen β 0).trans_lt (veblen_lt_veblen_iff_right.2 hx)

theorem mem_lpC_of {x : Ordinal.{0}} (hyx : y < x) (hP : ¬ LuP (β + 1) x) : x ∈ lpC β y :=
  ⟨hyx.trans_le (right_le_veblen _ _), lp_lvl_lt (lt_of_le_of_lt zero_le hyx), hP⟩

/-- **`ind(p) = p`** for `p ∈ P_{β+1}` above `y`. -/
theorem lpInd_P : ∀ p, LuP (β + 1) p → y < p → lpInd β y p = p := by
  intro p
  induction p using WellFoundedLT.induction with
  | ind p IH =>
  intro hP hyp
  refine le_antisymm (cdOtp_le_self _ p) (le_of_forall_lt fun α hα => ?_)
  by_cases hex : ∃ p', LuP (β + 1) p' ∧ max α y < p' ∧ p' < p
  · obtain ⟨p', hP', hm, hp'⟩ := hex
    calc α < p' := (le_max_left α y).trans_lt hm
      _ = lpInd β y p' := (IH p' hp' hP' ((le_max_right α y).trans_lt hm)).symm
      _ ≤ lpInd β y p := cdOtp_mono _ hp'.le
  · push Not at hex
    have hmp : max α y < p := max_lt hα hyp
    have hm1 : max α y + 1 < p := by rw [← succ_eq_add_one]; exact (lu_P_lim hP).succ_lt hmp
    have hprin : IsPrincipal (· + ·) p := by
      have hE' : ω ^ p = p := lu_P_E hP
      rw [← hE']; exact isPrincipal_add_omega0_opow p
    have e : max α y + 1 + p = p := hprin.add_eq_right hm1
    have hsh := phOtp_shift (lpC β y) (max α y + 1) p fun z hz => by
      refine mem_lpC_of (lt_of_le_of_lt (le_max_right α y) ((lt_add_one _).trans_le le_self_add)) fun hz' => ?_
      have h1 := hex _ hz' ((lt_add_one _).trans_le le_self_add)
      have h2 : max α y + 1 + z < max α y + 1 + p := (add_lt_add_iff_left _).2 hz
      rw [e] at h2
      exact absurd h1 (not_le.2 h2)
    rw [e] at hsh
    show α < cdOtp (lpC β y) p
    rw [hsh]
    exact hα.trans_le le_add_self

/-- **`ind(p + 1 + δ) = p + δ`** for `p ∈ P_{β+1}` above `y` and no member of `P_{β+1}` in `(p, p + 1 + δ)`. -/
theorem lpInd_above {p δ : Ordinal.{0}} (hP : LuP (β + 1) p) (hyp : y < p)
    (h : ∀ z < δ, ¬ LuP (β + 1) (p + 1 + z)) : lpInd β y (p + 1 + δ) = p + δ := by
  have e1 : cdOtp (lpC β y) p = cdOtp (lpC β y) (p + 1) :=
    cdOtp_eq_of_gap _ le_self_add fun c hc hpc hcp => by
      have hcp' : c = p := le_antisymm (Order.lt_add_one_iff.1 hcp) hpc
      exact hc.2.2 (hcp' ▸ hP)
  have e2 : cdOtp (lpC β y) p = p := lpInd_P p hP hyp
  show cdOtp (lpC β y) (p + 1 + δ) = p + δ
  rw [phOtp_shift _ _ δ fun z hz => mem_lpC_of (hyp.trans ((lt_add_one p).trans_le le_self_add)) (h z hz),
    ← e1, e2]

/-- **`ind(δ) = δ`** when `y < φ_β(0)`, `β < φ_β(0)` and no member of `P_{β+1}` lies below `δ`. -/
theorem lpInd_low_gt {δ : Ordinal.{0}} (hy0 : y < veblen β 0) (hβ0 : β < veblen β 0)
    (h : ∀ z < δ, ¬ LuP (β + 1) z) : lpInd β y δ = δ := by
  unfold lpInd
  have := phOtp_shift (lpC β y) 0 δ fun z hz => by
    rw [zero_add]
    exact ⟨hy0.trans_le ((veblen_le_veblen_iff_right).2 zero_le),
      hβ0.trans_le ((veblen_le_veblen_iff_right).2 zero_le), h z hz⟩
  rwa [zero_add, ggOtp_zero, zero_add] at this

/-- **`ind(1 + δ) = δ`** when `φ_β(0) = y` or `φ_β(0) = β ≥ y` (a strongly critical level) and no member of
`P_{β+1}` lies in `[1, 1 + δ)`. -/
theorem lpInd_low_eq {δ : Ordinal.{0}} (hy0 : veblen β 0 = y ∨ (veblen β 0 = β ∧ y ≤ β))
    (h : ∀ z < δ, ¬ LuP (β + 1) (1 + z)) : lpInd β y (1 + δ) = δ := by
  unfold lpInd
  have hlow : cdOtp (lpC β y) 1 = 0 := phOtp_low _ fun c hc => by
    rcases eq_or_ne c 0 with rfl | hc0
    · rcases hy0 with e | ⟨e, -⟩
      · exact absurd (e ▸ hc.1) (lt_irrefl _)
      · exact absurd (e ▸ hc.2.1) (lt_irrefl _)
    · exact one_le_iff_ne_zero.2 hc0
  have hpos : ∀ z : Ordinal.{0}, 0 < 1 + z := fun z => lt_of_lt_of_le zero_lt_one le_self_add
  have hy0' : y ≤ veblen β 0 := by
    rcases hy0 with e | ⟨e, he⟩
    · exact e.ge
    · rw [e]; exact he
  rw [phOtp_shift (lpC β y) 1 δ fun z hz => ⟨hy0'.trans_lt ((veblen_lt_veblen_iff_right).2 (hpos z)),
      lp_lvl_lt (hpos z), h z hz⟩,
    hlow, zero_add]

end Index

/-- **THE LEVEL LEMMA at every level `β ∈ Tʸ ∩ Ω₁`, `1 ≤ β`**: for a strongly critical `y < Ω₁` and `b` off
`P_{β+1}` with `y < φ_β(b)`, `β < φ_β(b)` and `ind(b) ∈ Tʸ ∩ Ω₁`, `φ_β(b) = ϑʸ(Ω₁·β + ind(b))`. -/
theorem lpPhLev {β y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om1) (hβ1 : 1 ≤ β) (hβT : β ∈ Tset y)
    (hβΩ : β < Om1) :
    ∀ b, y < veblen β b → β < veblen β b → ¬ LuP (β + 1) b → lpInd β y b ∈ Tset y → lpInd β y b < Om1 →
      veblen β b = vt y (Om1 * β + lpInd β y b) := by
  have hyE : InE y := gg_SC_eps hy
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hyb hβb hbP hT h1
  have hbv : b < veblen β b :=
    lt_of_le_of_ne (right_le_veblen _ _) (fun e => hbP (luP_succ.2 e.symm))
  apply le_antisymm
  · have hfacts := ul_facts hyE hy1 hβ1 hβT hβΩ hT h1
    have hnP := lv_th_notP hyE hy1 hβ1 hβT hβΩ hT h1
    obtain ⟨b', hb'⟩ := lv_th_P hyE hy1 β hβ1 hβT hβΩ _ hT h1
    have hyb' : y < veblen β b' := by rw [hb']; exact hfacts.2.2.2.1
    have hβb' : β < veblen β b' := by rw [hb']; exact hfacts.2.2.2.2.2.2.1
    have hb'P : ¬ LuP (β + 1) b' := by
      intro hP
      have hfx : veblen β b' = b' := luP_succ.1 hP
      apply hnP
      rw [← hb', hfx]; exact hP
    rcases lt_or_ge b' b with hlt | hge
    · exfalso
      have hmem : b' ∈ lpC β y := ⟨hyb', hβb', hb'P⟩
      have hlt' : lpInd β y b' < lpInd β y b := cdOtp_lt_of_mem hmem hlt
      have hT' := vz_T_down hyE hy1 hT h1 hlt'.le
      have e := IH b' hlt hyb' hβb' hb'P hT' (hlt'.trans h1)
      have h3 := ul_eta_lt hyE hy1 hβ1 hβT hβΩ hT' hT h1 hlt'
      rw [← e, hb'] at h3
      exact lt_irrefl _ h3
    · rw [← hb']; exact veblen_le_veblen_iff_right.2 hge
  · refine lv_th_min hyE hy1 hβ1 hβT hβΩ hT h1 (luP_veblen β b) hyb
      ((cdOtp_le_self _ b).trans_lt hbv) hβb fun σ hσ => ?_
    obtain ⟨b', hb'C, hb'b, hσe⟩ := ggOtp_onto (lpC β y) b σ hσ
    obtain ⟨hyb', hβb', hb'P⟩ := hb'C
    have hσe' : lpInd β y b' = σ := hσe
    have hT' : lpInd β y b' ∈ Tset y := by rw [hσe']; exact vz_T_down hyE hy1 hT h1 hσ.le
    rw [← hσe', ← IH b' hb'b hyb' hβb' hb'P hT' (by rw [hσe']; exact hσ.trans h1)]
    exact veblen_lt_veblen_iff_right.2 hb'b

/-! ## Codes -/

section Codes

variable {Z : Ordinal.{0}}


/-- `φ_a` with a constant level `a < y` read over `y`: `Θ_y(φ_a(b)) = φ_a(Θ_y(b))`. -/
theorem lpTh_veblen_lvl {y a b : Ordinal.{0}} (hy : SC y) (ha : a < y) (hb : LgCl y b) :
    lgTh y (veblen a b) = veblen a (lgTh y b) := by
  rw [lpTh_phi hy a (LgCl.small ha) b hb, lgTh_small ha.le]

/-- **The index of a code is a code** (a constant level `1 ≤ a < Z`). -/
theorem lpIndCodeU (hZ : SC Z) {a b : Ordinal.{0}} (haZ : a < Z) (hb : LgCl Z b) (hb1 : Om 1 < b)
    (hbv : b < veblen a b) :
    ∃ d, LgCl Z d ∧ d ≤ b ∧ ∀ y, SC y → y < Om 1 → Z ≤ y → lgTh y d = luInd a y (lgTh y b) := by
  have ha1Z : a + 1 < Z := hZ.add_one_lt haZ
  set q := veblen (a + 1) (Om 1 + 1) with hqdef
  have hq : LgCl Z q := LgCl.phi (LgCl.small ha1Z) (lg_cl_Om1_one hZ)
  have hqP : LuP (a + 1) q := luP_veblen _ _
  -- facts at every base
  have hThq : ∀ y, SC y → y < Om 1 → Z ≤ y → lgTh y q = veblen (a + 1) (y + 1) := fun y hy hy1 hZy => by
    rw [lpTh_veblen_lvl hy (ha1Z.trans_le hZy) (lg_cl_Om1_one hy), lgTh_Om1_one hy hy1]
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
    refine ⟨b - (Om 1 + 1), (lgDec hZ b hb).1 _ (lg_cl_Om1_one hZ) hle, Ordinal.sub_le_self _ _,
      fun y hy hy1 hZy => ?_⟩
    have hbe : lgTh y b = y + 1 + lgTh y (b - (Om 1 + 1)) := by
      conv_lhs => rw [← Ordinal.add_sub_cancel_of_le hle]
      rw [lgTh_add hy (lg_cl_Om1_one hy), lgTh_Om1_one hy hy1]
    rw [hbe, luInd_low]
    intro z hz hP
    have h1 : y + 1 + z < lgTh y b := by rw [hbe]; exact (add_lt_add_iff_left _).2 hz
    have h2 := hPy y hy hZy _ hP ((lt_add_one y).trans_le le_self_add)
    rw [← hThq y hy hy1 hZy] at h2
    exact absurd (h2.trans_lt h1) (not_lt.2 (lgTh_lt (hb.mono hZy) hbq).le)
  · have hqb : q < b := lt_of_le_of_ne hbq fun e => by
      have h1 : veblen a q = q := by
        rw [hqdef]; exact veblen_veblen_of_lt (lt_add_one _) _
      rw [← e] at hbv; rw [h1] at hbv; exact lt_irrefl _ hbv
    obtain ⟨c, n, hc, hdc, hbc, hθc⟩ := lpSplit hZ b hb
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
    have hThp : ∀ y, SC y → y < Om 1 → Z ≤ y → y < lgTh y c := fun y hy hy1 hZy => by
      have := lgTh_lt (LgCl.om (Z := y)) hc1 (y := y); rwa [lgTh_Om1 hy hy1] at this
    by_cases hfa : veblen a c = c
    · -- `b = c + n`, `c ∈ P_{a+1}`: `d = c + (n - 1)`
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [Nat.cast_zero, add_zero] at hbc
        rw [hbc, hfa] at hbv; exact lt_irrefl _ hbv
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      refine ⟨c + m, LgCl.add hc (LgCl.small (ph_nat_lt hZ m)), ?_, fun y hy hy1 hZy => ?_⟩
      · rw [hbc]; exact (add_le_add_iff_left _).2 (by exact_mod_cast Nat.le_succ m)
      · have hcy := hc.mono hZy
        have hP : LuP (a + 1) (lgTh y c) := by
          refine luP_succ.2 ?_
          rw [← lpTh_veblen_lvl hy (haZ.trans_le hZy) hcy, hfa]
        have e : lgTh y b = lgTh y c + 1 + m := by
          rw [hbc, lpTh_add_nat hy hcy, add_assoc]; congr 1; exact_mod_cast Nat.add_comm m 1
        rw [lpTh_add_nat hy hcy, e, luInd_above hP (hThp y hy hy1 hZy) fun z hz => ?_]
        obtain ⟨j, rfl⟩ := lt_omega0.1 (hz.trans (natCast_lt_omega0 m))
        exact lu_P_nat_not _ j
    · -- otherwise `d = b`
      refine ⟨b, hb, le_rfl, fun y hy hy1 hZy => ?_⟩
      have hcy := hc.mono hZy
      have hby := hb.mono hZy
      have hay : a < y := haZ.trans_le hZy
      set β := lgTh y b with hβ
      have hβP : ¬ LuP (a + 1) β := by
        intro hP
        have h1 := lgTh_lt hby hbv
        rw [lpTh_veblen_lvl hy hay hby, ← hβ, luP_succ.1 hP] at h1
        exact lt_irrefl _ h1
      set s := {v | LuP (a + 1) v ∧ v < β} with hs
      have hqs : lgTh y q ∈ s := ⟨by rw [hThq y hy hy1 hZy]; exact luP_veblen _ _, lgTh_lt (hq.mono hZy) hqb⟩
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
        have e1 : lgTh y c + (n : Ordinal.{0}) = p + ((1 + j : ℕ) : Ordinal.{0}) := by
          rw [← lpTh_add_nat hy hcy, ← hbc, ← hβ, ← hδ, hj, add_assoc]; push_cast; rfl
        obtain ⟨e2, -⟩ := phSplit_uniq (hθc y hy hy1 hZy) (lu_P_dvd hpP) e1
        apply hfa
        refine lpTh_inj (LgCl.phi (LgCl.small hay) hcy) hcy ?_
        rw [lpTh_veblen_lvl hy hay hcy, e2]
        exact luP_succ.1 hpP
      conv_rhs => rw [← hδ]
      rw [luInd_above hpP hyp hgap]
      conv_lhs => rw [← hδ]
      rw [add_assoc p 1, one_add_of_omega0_le hω]



/-- **The index of a code is a code** (every level code `a ≥ Ω₁`). -/
theorem lpIndCodeV (hZ : SC Z) {a b : Ordinal.{0}} (ha : LgCl Z a) (haO : Om 1 ≤ a) (hb : LgCl Z b)
    (hb0 : veblen a 0 = a → 0 < b) (hbv : b < veblen a b) :
    ∃ d, LgCl Z d ∧ d ≤ b ∧ ∀ y, SC y → y < Om 1 → Z ≤ y → lgTh y d = lpInd (lgTh y a) y (lgTh y b) := by
  have hyΘ : ∀ y, SC y → y < Om 1 → Z ≤ y → y ≤ lgTh y a := fun y hy hy1 hZy => by
    rcases haO.lt_or_eq with h | h
    · have := lgTh_lt (LgCl.om (Z := y)) h (y := y); rw [lgTh_Om1 hy hy1] at this; exact this.le
    · rw [← h, lgTh_Om1 hy hy1]
  have ha1 : LgCl Z (a + 1) := LgCl.add ha (LgCl.small (gg_one_lt_of_SC hZ))
  have hq : LgCl Z (veblen (a + 1) 0) := LgCl.phi ha1 (LgCl.zero hZ.1)
  have hqP : LuP (a + 1) (veblen (a + 1) 0) := luP_veblen _ _
  have hThq : ∀ y, SC y → y < Om 1 → Z ≤ y → lgTh y (veblen (a + 1) 0) = veblen (lgTh y a + 1) 0 :=
    fun y hy hy1 hZy => by
      rw [lpTh_phi hy _ (ha1.mono hZy) _ (LgCl.zero hy.1), lgTh_add hy (ha.mono hZy),
        lgTh_small (gg_one_lt_of_SC hy).le, lpTh_zero]
  have hPy : ∀ y v, LuP (lgTh y a + 1) v → veblen (lgTh y a + 1) 0 ≤ v := by
    intro y v hv
    obtain ⟨γ, rfl⟩ := hv
    exact veblen_le_veblen_iff_right.2 zero_le
  rcases lt_or_ge b (veblen (a + 1) 0) with hbq | hbq
  · -- below the first member of `P_{Ω₁+a+1}`: no member of `P_{y+a+1}` below `Θ_y(b)`
    have hnoP : ∀ y, SC y → y < Om 1 → Z ≤ y → ∀ z, z < lgTh y b → ¬ LuP (lgTh y a + 1) z := by
      intro y hy hy1 hZy z hz hP
      have h1 := lgTh_lt (hb.mono hZy) hbq (y := y)
      rw [hThq y hy hy1 hZy] at h1
      exact absurd (hPy y z hP) (not_le.2 (hz.trans h1))
    have hThv : ∀ y, SC y → Z ≤ y → lgTh y (veblen a 0) = veblen (lgTh y a) 0 := fun y hy hZy => by
      rw [lpTh_phi hy _ (ha.mono hZy) _ (LgCl.zero hy.1), lpTh_zero]
    by_cases hka : veblen a 0 = a
    · have hb0' := hb0 hka
      have hb1 : 1 ≤ b := one_le_iff_pos.2 hb0'
      refine ⟨b - 1, (lgDec hZ b hb).1 1 (LgCl.small (gg_one_lt_of_SC hZ)) hb1, Ordinal.sub_le_self _ _,
        fun y hy hy1 hZy => ?_⟩
      have hbe : lgTh y b = 1 + lgTh y (b - 1) := by
        conv_lhs => rw [← Ordinal.add_sub_cancel_of_le hb1]
        rw [lgTh_add hy (LgCl.small (gg_one_lt_of_SC hy)), lgTh_small (gg_one_lt_of_SC hy).le]
      have hn := hnoP y hy hy1 hZy
      have hfix : veblen (lgTh y a) 0 = lgTh y a := by rw [← hThv y hy hZy, hka]
      rw [hbe]
      refine (lpInd_low_eq (Or.inr ⟨hfix, hyΘ y hy hy1 hZy⟩) fun z hz => hn (1 + z) ?_).symm
      rw [hbe]
      exact (add_lt_add_iff_left 1).2 hz
    · refine ⟨b, hb, le_rfl, fun y hy hy1 hZy => ?_⟩
      have hav : a < veblen a 0 := lt_of_le_of_ne (left_le_veblen a 0) (Ne.symm hka)
      have hβ0 : lgTh y a < veblen (lgTh y a) 0 := by
        rw [← hThv y hy hZy]; exact lgTh_lt (ha.mono hZy) hav
      exact (lpInd_low_gt ((hyΘ y hy hy1 hZy).trans_lt hβ0) hβ0 (hnoP y hy hy1 hZy)).symm
  · have hqb : veblen (a + 1) 0 < b := lt_of_le_of_ne hbq fun e => by
      have h1 : veblen (a) (veblen (a + 1) 0) = veblen (a + 1) 0 :=
        veblen_veblen_of_lt (lt_add_one _) _
      rw [← e] at hbv; rw [h1] at hbv; exact lt_irrefl _ hbv
    obtain ⟨c, n, hc, hdc, hbc, hθc⟩ := lpSplit hZ b hb
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
    have hThp : ∀ y, SC y → y < Om 1 → Z ≤ y → y < lgTh y c := fun y hy hy1 hZy => by
      have := lgTh_lt (LgCl.om (Z := y)) hc1 (y := y); rwa [lgTh_Om1 hy hy1] at this
    by_cases hfa : veblen (a) c = c
    · -- `b = c + n`, `c ∈ P_{Ω₁+a+1}`: `d = c + (n - 1)`
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [Nat.cast_zero, add_zero] at hbc
        rw [hbc, hfa] at hbv; exact lt_irrefl _ hbv
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      refine ⟨c + m, LgCl.add hc (LgCl.small (ph_nat_lt hZ m)), ?_, fun y hy hy1 hZy => ?_⟩
      · rw [hbc]; exact (add_le_add_iff_left _).2 (by exact_mod_cast Nat.le_succ m)
      · have hcy := hc.mono hZy
        have hP : LuP (lgTh y a + 1) (lgTh y c) := by
          refine luP_succ.2 ?_
          rw [← lpTh_phi hy _ (ha.mono hZy) _ hcy, hfa]
        have e : lgTh y b = lgTh y c + 1 + m := by
          rw [hbc, lpTh_add_nat hy hcy, add_assoc]; congr 1; exact_mod_cast Nat.add_comm m 1
        rw [lpTh_add_nat hy hcy, e, lpInd_above hP (hThp y hy hy1 hZy) fun z hz => ?_]
        obtain ⟨j, rfl⟩ := lt_omega0.1 (hz.trans (natCast_lt_omega0 m))
        exact lu_P_nat_not _ j
    · -- otherwise `d = b`
      refine ⟨b, hb, le_rfl, fun y hy hy1 hZy => ?_⟩
      have hcy := hc.mono hZy
      have hby := hb.mono hZy
      set β := lgTh y b with hβ
      have hβP : ¬ LuP (lgTh y a + 1) β := by
        intro hP
        have h1 := lgTh_lt hby hbv
        rw [lpTh_phi hy _ (ha.mono hZy) _ hby, ← hβ, luP_succ.1 hP] at h1
        exact lt_irrefl _ h1
      set s := {v | LuP (lgTh y a + 1) v ∧ v < β} with hs
      have hqs : lgTh y (veblen (a + 1) 0) ∈ s :=
        ⟨by rw [hThq y hy hy1 hZy]; exact luP_veblen _ _, lgTh_lt (hq.mono hZy) hqb⟩
      have hne : s.Nonempty := ⟨_, hqs⟩
      have hbdd : BddAbove s := ⟨β, fun v hv => hv.2.le⟩
      have hpP : LuP (lgTh y a + 1) (sSup s) := by
        refine luP_succ.2 ?_
        rw [(isNormal_veblen (lgTh y a)).map_sSup hne hbdd]
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
          _ < veblen (lgTh y a + 1) 0 :=
            veblen_zero_lt_veblen_zero.2 ((hyΘ y hy hy1 hZy).trans_lt (lt_add_one _))
      set p := sSup s with hp
      have hδ : p + 1 + (β - (p + 1)) = β := Ordinal.add_sub_cancel_of_le (Order.add_one_le_of_lt hpβ)
      have hgap : ∀ z < β - (p + 1), ¬ LuP (lgTh y a + 1) (p + 1 + z) := by
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
        have e1 : lgTh y c + (n : Ordinal.{0}) = p + ((1 + j : ℕ) : Ordinal.{0}) := by
          rw [← lpTh_add_nat hy hcy, ← hbc, ← hβ, ← hδ, hj, add_assoc]; push_cast; rfl
        obtain ⟨e2, -⟩ := phSplit_uniq (hθc y hy hy1 hZy) (lu_P_dvd hpP) e1
        apply hfa
        refine lpTh_inj (LgCl.phi (ha.mono hZy) hcy) hcy ?_
        rw [lpTh_phi hy _ (ha.mono hZy) _ hcy, e2]
        exact luP_succ.1 hpP
      conv_rhs => rw [← hδ]
      rw [lpInd_above hpP hyp hgap]
      conv_lhs => rw [← hδ]
      rw [add_assoc p 1, one_add_of_omega0_le hω]

end Codes

end Googology.Trans.PoR.InaccPsi.R2.Lp
