import Googology.Trans.PoR.InaccPsi.R2.LuLev
import Googology.Trans.PoR.InaccPsi.R2.PhFr

/-!
# `luSys` has terms for every code below `φ(Ω₁, 1)`, and its frontier lies below `L(0)`

For a strongly critical base `y < Ω₁` and a constant level `1 ≤ β < y` (`R2.PhLev`, `R2.PhVz` did this for `β < ω`):

* `luC`, `luInd` (the index of `b` among the ordinals above `y` off `P_{β+1}`), `luInd_low`, `luInd_P`, `luInd_above`;
* `luPhLev` (**THE LEVEL LEMMA at every constant level**): `φ_β(b) = ϑʸ(Ω₁·β + ind(b))` for `b > y` off `P_{β+1}` with
  `ind(b) ∈ Tʸ ∩ Ω₁` (from `R2.LuLev`: minimality, `ϑʸ(Ω₁·β + η) ∈ P_β ∖ P_{β+1}`);
* `luIndCode` (**the index of a code is a code**, for a level `a < Z`), `luT := φ(Ω₁, 1)` (the code of the top),
  `luTh_T` (**`Θ_y(φ(Ω₁, 1)) = φ(y, 1) = ϑʸ(Ω₁·y)`**), `luPoly` (**`GgPoly luSys luT`**: a code `c < φ(Ω₁, 1)` over `Z`
  is a constant, `Ω₁`, a sum, a power, or `φ_a(b)` with a constant level `1 ≤ a < Z`, `Ω₁ < b < φ_a(b)`, read as the
  term `th a t`);
* `lu_fr` (**`Λ(luSys) ≤ ι(ω^{φ(Ω₁,1)})`, `Λ⁺(luSys) ≤ ι(ω^{φ(Ω₁,1)}·ω) < L(0)`, `υ_{Λ⁺(luSys)} < L(0)`**, by THEOREM UNI,
  `Ph.phFrGen`), `lu_fr_order` (**`ρ` of `Λ⁺(lnSw)` < `ρ` of `Λ⁺(luSys)` < `L(0) = m* ≤ L(n+1) < L(ω) < L(ω+1)`**,
  unconditionally).

No new axiom beyond `R2.CitedLu`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lu

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ph

/-! ## The index of `b` among the ordinals above `y` off `P_{β+1}` -/

/-- The ordinals above `y` that are not in `P_{β+1}`. -/
def luC (β y : Ordinal.{0}) : Set Ordinal.{0} := {x | y < x ∧ ¬ LuP (β + 1) x}

/-- The index of `b` in `luC β y`. -/
noncomputable def luInd (β y b : Ordinal.{0}) : Ordinal.{0} := cdOtp (luC β y) b

section Index

variable {β y : Ordinal.{0}}

theorem mem_luC {x : Ordinal.{0}} : x ∈ luC β y ↔ y < x ∧ ¬ LuP (β + 1) x := Iff.rfl

theorem lu_P_E {v : Ordinal.{0}} (h : LuP (β + 1) v) : InE v := luP_E le_add_self h

theorem lu_P_lim {v : Ordinal.{0}} (h : LuP (β + 1) v) : IsSuccLimit v := by
  have hE := lu_P_E h
  have hv0 : v ≠ 0 := hE.pos.ne'
  have hE' : ω ^ v = v := hE
  rw [← hE']; exact ph_opow_lim hv0

theorem lu_P_succ_not (v : Ordinal.{0}) : ¬ LuP (β + 1) (v + 1) := fun h =>
  not_isSuccLimit_succ v (by rw [succ_eq_add_one]; exact lu_P_lim h)

theorem lu_P_nat_not (v : Ordinal.{0}) (n : ℕ) : ¬ LuP (β + 1) (v + 1 + n) := by
  have e : v + 1 + (n : Ordinal.{0}) = v + n + 1 := by
    rw [add_assoc, add_assoc]; congr 1; exact_mod_cast Nat.add_comm 1 n
  rw [e]; exact lu_P_succ_not _

theorem lu_P_dvd {v : Ordinal.{0}} (h : LuP (β + 1) v) : ω ∣ v :=
  isSuccPrelimit_iff_omega0_dvd.1 (lu_P_lim h).isSuccPrelimit

/-- **`ind(y + 1 + δ) = δ`** when no member of `P_{β+1}` lies in `(y, y + 1 + δ)`. -/
theorem luInd_low {δ : Ordinal.{0}} (h : ∀ z < δ, ¬ LuP (β + 1) (y + 1 + z)) :
    luInd β y (y + 1 + δ) = δ := by
  unfold luInd
  rw [phOtp_shift _ _ δ fun z hz => mem_luC.2 ⟨lt_of_lt_of_le (lt_add_one y) le_self_add, h z hz⟩,
    phOtp_low _ fun c hc => Order.add_one_le_of_lt (mem_luC.1 hc).1, zero_add]

/-- **`ind(p) = p`** for `p ∈ P_{β+1}` above `y`. -/
theorem luInd_P : ∀ p, LuP (β + 1) p → y < p → luInd β y p = p := by
  intro p
  induction p using WellFoundedLT.induction with
  | ind p IH =>
  intro hP hyp
  refine le_antisymm (cdOtp_le_self _ p) (le_of_forall_lt fun α hα => ?_)
  by_cases hex : ∃ p', LuP (β + 1) p' ∧ max α y < p' ∧ p' < p
  · obtain ⟨p', hP', hm, hp'⟩ := hex
    calc α < p' := (le_max_left α y).trans_lt hm
      _ = luInd β y p' := (IH p' hp' hP' ((le_max_right α y).trans_lt hm)).symm
      _ ≤ luInd β y p := cdOtp_mono _ hp'.le
  · push Not at hex
    have hmp : max α y < p := max_lt hα hyp
    have hm1 : max α y + 1 < p := by rw [← succ_eq_add_one]; exact (lu_P_lim hP).succ_lt hmp
    have hprin : IsPrincipal (· + ·) p := by
      have hE' : ω ^ p = p := lu_P_E hP
      rw [← hE']; exact isPrincipal_add_omega0_opow p
    have e : max α y + 1 + p = p := hprin.add_eq_right hm1
    have hsh := phOtp_shift (luC β y) (max α y + 1) p fun z hz => by
      refine mem_luC.2 ⟨lt_of_le_of_lt (le_max_right α y) ((lt_add_one _).trans_le le_self_add), fun hz' => ?_⟩
      have h1 := hex _ hz' ((lt_add_one _).trans_le le_self_add)
      have h2 : max α y + 1 + z < max α y + 1 + p := (add_lt_add_iff_left _).2 hz
      rw [e] at h2
      exact absurd h1 (not_le.2 h2)
    rw [e] at hsh
    show α < cdOtp (luC β y) p
    rw [hsh]
    exact hα.trans_le le_add_self

/-- **`ind(p + 1 + δ) = p + δ`** for `p ∈ P_{β+1}` above `y` and no member of `P_{β+1}` in `(p, p + 1 + δ)`. -/
theorem luInd_above {p δ : Ordinal.{0}} (hP : LuP (β + 1) p) (hyp : y < p)
    (h : ∀ z < δ, ¬ LuP (β + 1) (p + 1 + z)) : luInd β y (p + 1 + δ) = p + δ := by
  have e1 : cdOtp (luC β y) p = cdOtp (luC β y) (p + 1) :=
    cdOtp_eq_of_gap _ le_self_add fun c hc hpc hcp => by
      have hcp' : c = p := le_antisymm (Order.lt_add_one_iff.1 hcp) hpc
      exact (mem_luC.1 hc).2 (hcp' ▸ hP)
  have e2 : cdOtp (luC β y) p = p := luInd_P p hP hyp
  show cdOtp (luC β y) (p + 1 + δ) = p + δ
  rw [phOtp_shift _ _ δ fun z hz => mem_luC.2 ⟨hyp.trans ((lt_add_one p).trans_le le_self_add), h z hz⟩,
    ← e1, e2]

/-- **THE LEVEL LEMMA at every constant level**: for a strongly critical `y < Ω₁`, `1 ≤ β < y` and `b > y` off
`P_{β+1}` with `ind(b) ∈ Tʸ ∩ Ω₁`, `φ_β(b) = ϑʸ(Ω₁·β + ind(b))`. -/
theorem luPhLev (hy : SC y) (hy1 : y < Om1) (hβ1 : 1 ≤ β) (hβy : β < y) :
    ∀ b, y < b → ¬ LuP (β + 1) b → luInd β y b ∈ Tset y → luInd β y b < Om1 →
      veblen β b = vt y (Om1 * β + luInd β y b) := by
  have hyE : InE y := gg_SC_eps hy
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hyb hbP hT h1
  have hbv : b < veblen β b :=
    lt_of_le_of_ne (right_le_veblen _ _) (fun e => hbP (luP_succ.2 e.symm))
  apply le_antisymm
  · have hfacts := lu_th_facts hyE hy1 hβ1 hβy hT h1
    have hnP := lu_th_notP hyE hy1 hβ1 hβy hT h1
    obtain ⟨b', hb'⟩ := lu_th_P hyE hy1 β hβ1 hβy _ hT h1
    have hky : veblen β y = y := hy.veblen_right hβy
    have hyb' : y < b' := by
      by_contra hle
      push Not at hle
      have h2 := (veblen_le_veblen_iff_right (o := β)).2 hle
      rw [hky, hb'] at h2
      exact absurd hfacts.2.2.2.1 (not_lt.2 h2)
    have hb'P : ¬ LuP (β + 1) b' := by
      intro hP
      have hfx : veblen β b' = b' := luP_succ.1 hP
      apply hnP
      rw [← hb', hfx]; exact hP
    rcases lt_or_ge b' b with hlt | hge
    · exfalso
      have hmem : b' ∈ luC β y := mem_luC.2 ⟨hyb', hb'P⟩
      have hlt' : luInd β y b' < luInd β y b := cdOtp_lt_of_mem hmem hlt
      have hT' := vz_T_down hyE hy1 hT h1 hlt'.le
      have e := IH b' hlt hyb' hb'P hT' (hlt'.trans h1)
      have h3 := lu_th_lt hyE hy1 hβ1 hβy hT' hT h1 hlt'
      rw [← e, hb'] at h3
      exact lt_irrefl _ h3
    · rw [← hb']; exact veblen_le_veblen_iff_right.2 hge
  · refine lu_th_min hyE hy1 hβ1 hβy hT h1 (luP_veblen β b) (hyb.trans_le (right_le_veblen _ _))
      ((cdOtp_le_self _ b).trans_lt hbv) fun σ hσ => ?_
    obtain ⟨b', hb'C, hb'b, hσe⟩ := ggOtp_onto (luC β y) b σ hσ
    obtain ⟨hyb', hb'P⟩ := mem_luC.1 hb'C
    have hσe' : luInd β y b' = σ := hσe
    have hT' : luInd β y b' ∈ Tset y := by rw [hσe']; exact vz_T_down hyE hy1 hT h1 hσ.le
    rw [← hσe', ← IH b' hb'b hyb' hb'P hT' (by rw [hσe']; exact hσ.trans h1)]
    exact veblen_lt_veblen_iff_right.2 hb'b

end Index

/-! ## Codes -/

section Codes

variable {Z : Ordinal.{0}}

/-- `φ_a` with a constant level `a < y` read over `y`: `Θ_y(φ_a(b)) = φ_a(Θ_y(b))`. -/
theorem luTh_veblen_lvl {y a b : Ordinal.{0}} (hy : SC y) (ha : a < y) (hb : GgCl y b) :
    ggTh y (veblen a b) = veblen a (ggTh y b) := by
  rw [phTh_phi hy a (GgCl.small ha) b hb, ggTh_small ha.le]

/-- **The index of a code is a code** (a constant level `1 ≤ a < Z`). -/
theorem luIndCode (hZ : SC Z) {a b : Ordinal.{0}} (haZ : a < Z) (hb : GgCl Z b) (hb1 : Om 1 < b)
    (hbv : b < veblen a b) :
    ∃ d, GgCl Z d ∧ d ≤ b ∧ ∀ y, SC y → y < Om 1 → Z ≤ y → ggTh y d = luInd a y (ggTh y b) := by
  have ha1Z : a + 1 < Z := hZ.add_one_lt haZ
  set q := veblen (a + 1) (Om 1 + 1) with hqdef
  have hq : GgCl Z q := GgCl.phi (GgCl.small ha1Z) (ph_cl_Om1_one hZ)
  have hqP : LuP (a + 1) q := luP_veblen _ _
  -- facts at every base
  have hThq : ∀ y, SC y → y < Om 1 → Z ≤ y → ggTh y q = veblen (a + 1) (y + 1) := fun y hy hy1 hZy => by
    rw [luTh_veblen_lvl hy (ha1Z.trans_le hZy) (ph_cl_Om1_one hy), phTh_Om1_one hy hy1]
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
    refine ⟨b - (Om 1 + 1), (ggDec hZ b hb).1 _ (ph_cl_Om1_one hZ) hle, Ordinal.sub_le_self _ _,
      fun y hy hy1 hZy => ?_⟩
    have hbe : ggTh y b = y + 1 + ggTh y (b - (Om 1 + 1)) := by
      conv_lhs => rw [← Ordinal.add_sub_cancel_of_le hle]
      rw [ggTh_add hy (ph_cl_Om1_one hy), phTh_Om1_one hy hy1]
    rw [hbe, luInd_low]
    intro z hz hP
    have h1 : y + 1 + z < ggTh y b := by rw [hbe]; exact (add_lt_add_iff_left _).2 hz
    have h2 := hPy y hy hZy _ hP ((lt_add_one y).trans_le le_self_add)
    rw [← hThq y hy hy1 hZy] at h2
    exact absurd (h2.trans_lt h1) (not_lt.2 (ggTh_lt (hb.mono hZy) hbq).le)
  · have hqb : q < b := lt_of_le_of_ne hbq fun e => by
      have h1 : veblen a q = q := by
        rw [hqdef]; exact veblen_veblen_of_lt (lt_add_one _) _
      rw [← e] at hbv; rw [h1] at hbv; exact lt_irrefl _ hbv
    obtain ⟨c, n, hc, hdc, hbc, hθc⟩ := phSplit hZ b hb
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
    have hThp : ∀ y, SC y → y < Om 1 → Z ≤ y → y < ggTh y c := fun y hy hy1 hZy => by
      have := ggTh_lt (GgCl.om (Z := y)) hc1 (y := y); rwa [ggTh_Om1 hy hy1] at this
    by_cases hfa : veblen a c = c
    · -- `b = c + n`, `c ∈ P_{a+1}`: `d = c + (n - 1)`
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [Nat.cast_zero, add_zero] at hbc
        rw [hbc, hfa] at hbv; exact lt_irrefl _ hbv
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      refine ⟨c + m, GgCl.add hc (ph_cl_nat hZ m), ?_, fun y hy hy1 hZy => ?_⟩
      · rw [hbc]; exact (add_le_add_iff_left _).2 (by exact_mod_cast Nat.le_succ m)
      · have hcy := hc.mono hZy
        have hP : LuP (a + 1) (ggTh y c) := by
          refine luP_succ.2 ?_
          rw [← luTh_veblen_lvl hy (haZ.trans_le hZy) hcy, hfa]
        have e : ggTh y b = ggTh y c + 1 + m := by
          rw [hbc, phTh_add_nat hy hcy, add_assoc]; congr 1; exact_mod_cast Nat.add_comm m 1
        rw [phTh_add_nat hy hcy, e, luInd_above hP (hThp y hy hy1 hZy) fun z hz => ?_]
        obtain ⟨j, rfl⟩ := lt_omega0.1 (hz.trans (natCast_lt_omega0 m))
        exact lu_P_nat_not _ j
    · -- otherwise `d = b`
      refine ⟨b, hb, le_rfl, fun y hy hy1 hZy => ?_⟩
      have hcy := hc.mono hZy
      have hby := hb.mono hZy
      have hay : a < y := haZ.trans_le hZy
      set β := ggTh y b with hβ
      have hβP : ¬ LuP (a + 1) β := by
        intro hP
        have h1 := ggTh_lt hby hbv
        rw [luTh_veblen_lvl hy hay hby, ← hβ, luP_succ.1 hP] at h1
        exact lt_irrefl _ h1
      set s := {v | LuP (a + 1) v ∧ v < β} with hs
      have hqs : ggTh y q ∈ s := ⟨by rw [hThq y hy hy1 hZy]; exact luP_veblen _ _, ggTh_lt (hq.mono hZy) hqb⟩
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
        have e1 : ggTh y c + (n : Ordinal.{0}) = p + ((1 + j : ℕ) : Ordinal.{0}) := by
          rw [← phTh_add_nat hy hcy, ← hbc, ← hβ, ← hδ, hj, add_assoc]; push_cast; rfl
        obtain ⟨e2, -⟩ := phSplit_uniq (hθc y hy hy1 hZy) (lu_P_dvd hpP) e1
        apply hfa
        refine phTh_inj (GgCl.phi (GgCl.small hay) hcy) hcy ?_
        rw [luTh_veblen_lvl hy hay hcy, e2]
        exact luP_succ.1 hpP
      conv_rhs => rw [← hδ]
      rw [luInd_above hpP hyp hgap]
      conv_lhs => rw [← hδ]
      rw [add_assoc p 1, one_add_of_omega0_le hω]

/-- **The code of the top**: `φ(Ω₁, 1)`. -/
noncomputable def luTc : Ordinal.{0} := veblen (Om 1) 1

theorem lu_cl_T (hZ : SC Z) : GgCl Z luTc := GgCl.phi GgCl.om (GgCl.small (gg_one_lt_of_SC hZ))

theorem lu_Om1_le_T : Om 1 ≤ luTc := by
  unfold luTc
  calc Om 1 = veblen (Om 1) 0 := ph_SC_Om1.veblen_zero.symm
    _ ≤ veblen (Om 1) 1 := (veblen_le_veblen_iff_right).2 zero_le_one

theorem lu_T_lt_Gam : luTc < ggGam :=
  ggGam_spec.1.2 _ ggGam_spec.2 _ ((lt_of_lt_of_le one_lt_omega0 (ph_omega_lt ph_SC_Om1).le).trans ggGam_spec.2)

/-- **`Θ_y(φ(Ω₁, 1)) = φ(y, 1) = ϑʸ(Ω₁·y)`** for a strongly critical `y < Ω₁`. -/
theorem luTh_T {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) : ggTh y luTc = luTop y := by
  have hyE : InE y := gg_SC_eps hy
  have hy1' : y < Om1 := by rw [ph_Om1_eq]; exact hy1
  unfold luTc luTop
  rw [phTh_phi hy _ GgCl.om _ (GgCl.small (gg_one_lt_of_SC hy)), ggTh_Om1 hy hy1,
    ggTh_small (gg_one_lt_of_SC hy).le]
  have hy0 : veblen y 0 = y := hy.veblen_zero
  apply le_antisymm
  · obtain ⟨j, hj⟩ := lu_top_P hyE hy1'
    have hyj : y < veblen y j := by rw [hj]; exact (lu_top_facts hyE hy1').2.2.2.1
    have hj0 : 0 < j := by
      by_contra h0
      push Not at h0
      rw [nonpos_iff_eq_zero.1 h0, hy0] at hyj
      exact lt_irrefl _ hyj
    rw [← hj]
    exact (veblen_le_veblen_iff_right).2 (one_le_iff_pos.2 hj0)
  · refine lu_top_least hyE hy1' (luP_veblen y 1) ?_
    calc y = veblen y 0 := hy0.symm
      _ < veblen y 1 := (veblen_lt_veblen_iff_right).2 zero_lt_one

/-- **`luSys` has terms for every code below `φ(Ω₁, 1)`.** -/
theorem luPoly : GgPoly luSys luTc := by
  refine phPoly_of_SC fun Z hZ _ => ?_
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hcB
  rcases lt_trichotomy c (Om 1) with hc1 | hc1 | hc1
  · have hcZ : c < Z := hc.lt_of_lt_Om1 hZ hc1
    exact ⟨LuT.cst c, fun y _ _ hZy =>
      ⟨lt_of_lt_of_le hcZ hZy, by show c = ggTh y c; rw [ggTh_small (hcZ.le.trans hZy)]⟩⟩
  · subst hc1
    exact ⟨LuT.bs, fun y hy hy1 _ => ⟨trivial, by show y = ggTh y (Om 1); rw [ggTh_Om1 hy hy1]⟩⟩
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
    refine ⟨LuT.sm s1 s2, fun y hy hy1 hZy => ?_⟩
    obtain ⟨c1, v1⟩ := hs1 y hy hy1 hZy
    obtain ⟨c2, v2⟩ := hs2 y hy hy1 hZy
    refine ⟨⟨c1, c2⟩, ?_⟩
    show luSys.val s1 y + luSys.val s2 y = _
    rw [v1, v2, ← ggTh_add hy (hw.mono hZy), hcr]
  rcases (log_le_self ω c).lt_or_eq with hL | hL
  · -- a power `ω^L`, `L < c`
    obtain ⟨s, hs⟩ := IH _ hL hlog (hL.trans hcB)
    refine ⟨LuT.pw s, fun y hy hy1 hZy => ?_⟩
    obtain ⟨c1, v1⟩ := hs y hy hy1 hZy
    refine ⟨c1, ?_⟩
    show ω ^ luSys.val s y = _
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
  have haO : a < Om 1 := by
    have hlt : veblen a b < veblen (Om 1) 1 := by rw [hdec]; exact hcB
    rcases veblen_lt_veblen_iff.1 hlt with ⟨e, hb'⟩ | ⟨h', _⟩ | ⟨_, h'⟩
    · exfalso
      have hb0 : b = 0 := le_antisymm (Order.lt_add_one_iff.1 (by rw [zero_add]; exact hb')) zero_le
      rw [e, hb0, hSC1.veblen_zero] at hdec
      rw [← hdec] at hc1
      exact lt_irrefl _ hc1
    · exact h'
    · exfalso
      rw [hdec] at h'
      exact hc0 (le_antisymm (Order.lt_add_one_iff.1 (by rw [zero_add]; exact h')) zero_le)
  have haZ : a < Z := ha.lt_of_lt_Om1 hZ haO
  have ha1 : 1 ≤ a := one_le_iff_ne_zero.2 ha0
  have hbO : Om 1 < b := by
    by_contra hle
    push Not at hle
    have h3 := (veblen_le_veblen_iff_right (o := a)).2 hle
    rw [hdec, hSC1.veblen_right haO] at h3
    exact absurd hc1 (not_lt.2 h3)
  have hbv : b < veblen a b := by rw [hdec]; exact hb1
  obtain ⟨d, hd, hdb, hdθ⟩ := luIndCode hZ haZ hb hbO hbv
  obtain ⟨t, ht⟩ := IH d (hdb.trans_lt hb1) hd ((hdb.trans_lt hb1).trans hcB)
  refine ⟨LuT.th a t, fun y hy hy1 hZy => ?_⟩
  obtain ⟨ct, vt'⟩ := ht y hy hy1 hZy
  have hy1' : y < Om1 := by rw [ph_Om1_eq]; exact hy1
  have hay : a < y := haZ.trans_le hZy
  refine ⟨⟨ha1, hay, ct⟩, ?_⟩
  show vt y (Om1 * a + luSys.val t y) = ggTh y c
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
  have hTv : luSys.val t y ∈ Tset y ∧ luSys.val t y < Om1 :=
    ⟨(lu_T (gg_SC_eps hy) hy1' t ct).1, lu_lt_Om1 (gg_SC_eps hy) hy1' ct⟩
  have e1 : luSys.val t y = luInd a y (ggTh y b) := by rw [vt', hdθ y hy hy1 hZy]
  rw [e1] at hTv ⊢
  rw [hThc, luPhLev hy hy1' ha1 hay _ hyb hbP hTv.1 hTv.2]

end Codes

/-! ## The frontier lies below `L(0)` -/

variable {S : InaccSeq.{0}}

/-- **The frontier of `luSys`**: every `ι(ω^{φ(Ω₁,1)}·(n+1))` is a frontier, `Λ(luSys) ≤ ι(ω^{φ(Ω₁,1)})`,
`Λ⁺(luSys) ≤ ι(ω^{φ(Ω₁,1)}·ω) < L(0)` and `υ_{Λ⁺(luSys)} < L(0)`. -/
theorem lu_fr :
    (∀ n : ℕ, XtFr luSys (iota S (ω ^ luTc * ((n : Ordinal.{0}) + 1))) ∧
      upsilon (iota S (ω ^ luTc * ((n : Ordinal.{0}) + 1))) = iota S (ω ^ luTc * ((n : Ordinal.{0}) + 1))) ∧
    xtLam luSys ≤ iota S (ω ^ luTc) ∧ xtB1 luSys ≤ iota S (ω ^ luTc * ω) ∧
    iota S (ω ^ luTc * ω) < Nc.ncL S 0 ∧ upsilon (xtB1 luSys) < Nc.ncL S 0 :=
  phFrGen lu_T_lt_Gam (phPolyR_of luPoly) (fun _ hy hy1 => (luTh_T hy hy1).symm) (fun _ hZ => lu_cl_T hZ)
    lu_Om1_le_T

/-- **Where the frontier lies**: `ρ` of `Λ⁺(lnSw)` < `ρ` of `Λ(luSys)` < `ρ` of `Λ⁺(luSys)` < `L(0) = m* ≤ L(n+1) <
`L(ω) < L(ω+1)`, and `Λ⁺(luSys) < L(ω+1)`, unconditionally. -/
theorem lu_fr_order (n : ℕ) :
    upsilon (xtB1 Lt.lnSw) < upsilon (xtLam luSys) ∧ upsilon (xtLam luSys) < upsilon (xtB1 luSys) ∧
    upsilon (xtB1 luSys) < Nc.ncL S 0 ∧ Nc.ncL S 0 ≤ Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ∧
    Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) < Nc.ncL S ω ∧ Nc.ncL S ω < Nc.ncL S (ω + 1) ∧
    xtB1 luSys < Nc.ncL S (ω + 1) := by
  obtain ⟨h0, h1, h2⟩ := phL_chain (S := S) n
  have hU := (lu_fr (S := S)).2.2.2.2
  refine ⟨upsilon_normal.strictMono luLam_gt, upsilon_normal.strictMono lu_lamLtB1, hU, h0, h1, h2, ?_⟩
  exact upsilon_normal.strictMono.le_apply.trans_lt (((hU.trans_le h0).trans h1).trans h2)

end Googology.Trans.PoR.InaccPsi.R2.Lu
