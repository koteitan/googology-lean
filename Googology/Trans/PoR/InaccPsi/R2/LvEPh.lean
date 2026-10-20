import Googology.Trans.PoR.InaccPsi.R2.LvELev

/-!
# `lveSys` has terms for every code below `φ(ε_{Ω₁+1}, 0)`, and its frontier lies below `L(0)`

For a strongly critical base `y < Ω₁` (the level lemma `lvPhLev` of `R2.LvPh` at every level `β ∈ [y, ε_{y+1})`):

* `lve_level_lt_P` (a member of `P_β` above `y` is above `β`), `lveSC_eN` (`φ(1, y+1) = ε_{y+1}`);
* `levPoly` (**every code `a < ε_{Ω₁+1}` is read by a level term**: `Θ_y(a) = l(y)`, with the base for `a ≥ Ω₁`),
  `lveIndCode` (**the index of a code is a code**, for every level code `a ≥ Ω₁`);
* `lveTc := φ(ε_{Ω₁+1}, 0)` (the code of the top), `lveTh_T` (**`Θ_y(φ(ε_{Ω₁+1}, 0)) = φ(ε_{y+1}, 0) =
  ϑʸ(Ω₁·ε_{y+1})`**), `lvePoly` (**`GgPoly lveSys lveTc`**: a code `c < φ(ε_{Ω₁+1}, 0)` is a constant, `Ω₁`, a sum, a
  power, `φ_a(b)` with a constant level `1 ≤ a < Z` (the term `th0 a t`), or `φ_a(b)` with `Ω₁ ≤ a < ε_{Ω₁+1}` (the
  term `tl l t` for the level term `l` of `a`));
* `lve_fr` (**`Λ⁺(lveSys) ≤ ι(ω^{φ(ε_{Ω₁+1},0)}·ω) < L(0)`, `υ_{Λ⁺(lveSys)} < L(0)`**), `lve_fr_order`.

No new axiom beyond `R2.CitedLu` and `R2.CitedLv`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ph Lu

/-- A member of `P_β` above `y` is above a level `β ≥ 1` that is `≤ y` or not an `ε`-number. -/
theorem lve_level_lt_P {β y u : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβ : β ≤ y ∨ ¬ InE β) (hPu : LuP β u)
    (hyu : y < u) : β < u := by
  have huE : InE u := luP_E hβ1 hPu
  obtain ⟨j, rfl⟩ := hPu
  refine lt_of_le_of_ne (left_le_veblen _ _) fun e => ?_
  rcases hβ with h | h
  · exact absurd (e ▸ hyu) (not_lt.2 h)
  · exact h (e ▸ huE)

/-- `φ(1, y + 1) = ε_{y+1}` for a strongly critical `y`. -/
theorem lveSC_eN {y : Ordinal.{0}} (hy : SC y) : veblen 1 (y + 1) = eN y := by
  have h1 : veblen 1 = deriv (fun a => ω ^ a) := by rw [← zero_add 1, veblen_add_one, veblen_zero]
  have hy1 : veblen 1 y = y := hy.veblen_right (gg_one_lt_of_SC hy)
  rw [h1, deriv_add_one, ← h1, hy1]
  rfl

section Codes

variable {Z : Ordinal.{0}}

/-- **Every code below `ε_{Ω₁+1}` is read by a level term**, with the base for the codes `≥ Ω₁`. -/
theorem levPoly (hZ : SC Z) : ∀ a, GgCl Z a → a < veblen 1 (Om 1 + 1) →
    ∃ l : LvET, LvET.isLev l ∧ (Om 1 ≤ a → LvET.hasB l) ∧
      ∀ y, SC y → y < Om 1 → Z ≤ y → LvET.CBt l y ∧ LvET.val l y = ggTh y a := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH =>
  intro ha haB
  rcases lt_trichotomy a (Om 1) with ha1 | ha1 | ha1
  · have haZ : a < Z := ha.lt_of_lt_Om1 hZ ha1
    exact ⟨.cst a, trivial, fun h => absurd h (not_le.2 ha1), fun y _ _ hZy =>
      ⟨lt_of_lt_of_le haZ hZy, by rw [LvET.val_cst, ggTh_small (haZ.le.trans hZy)]⟩⟩
  · subst ha1
    exact ⟨.bs, trivial, fun _ => trivial, fun y hy hy1 _ => ⟨trivial, by rw [LvET.val_bs, ggTh_Om1 hy hy1]⟩⟩
  have ha0 : a ≠ 0 := (lt_of_le_of_lt zero_le ha1).ne'
  obtain ⟨hsub, hlog⟩ := ggDec hZ a ha
  have hw : GgCl Z (ω ^ log ω a) := GgCl.opow hZ.1 hlog
  have hwa : ω ^ log ω a ≤ a := opow_log_le_self ω ha0
  have hO : ω ^ Om (1 : Ordinal.{0}) = Om 1 := gg_SC_eps ph_SC_Om1
  have hlogO : Om 1 ≤ log ω a := by
    by_contra hlt
    push Not at hlt
    have h1 : log ω a + 1 < Om 1 := ph_SC_Om1.add_one_lt hlt
    have h2 : a < ω ^ (log ω a + 1) := lt_opow_succ_log_self one_lt_omega0 a
    have h3 : ω ^ (log ω a + 1) < Om 1 := by
      rw [← hO]; exact (opow_lt_opow_iff_right one_lt_omega0).2 h1
    exact absurd (h2.trans h3) (not_lt.2 ha1.le)
  have hwO : Om 1 ≤ ω ^ log ω a := by
    rw [← hO]; exact (opow_le_opow_iff_right one_lt_omega0).2 hlogO
  rcases hwa.lt_or_eq with hwa' | hwa'
  · have hr := hsub _ hw hwa
    have hcr : ω ^ log ω a + (a - ω ^ log ω a) = a := Ordinal.add_sub_cancel_of_le hwa
    have hrc : a - ω ^ log ω a < a := by
      rcases (Ordinal.sub_le_self a (ω ^ log ω a)).lt_or_eq with h | h
      · exact h
      · exfalso
        have h1 : ω ^ log ω a + a = a := by conv_rhs => rw [← hcr]
                                            rw [h]
        have h2 := add_eq_right_iff_mul_omega0_le.1 h1
        rw [← opow_succ] at h2
        exact absurd (lt_opow_succ_log_self one_lt_omega0 a) (not_lt.2 h2)
    obtain ⟨l1, hl1, hb1, hv1⟩ := IH _ hwa' hw (hwa'.trans haB)
    obtain ⟨l2, hl2, -, hv2⟩ := IH _ hrc hr (hrc.trans haB)
    refine ⟨.sm l1 l2, ⟨hl1, hl2⟩, fun _ => Or.inl (hb1 hwO), fun y hy hy1 hZy => ?_⟩
    obtain ⟨c1, e1⟩ := hv1 y hy hy1 hZy
    obtain ⟨c2, e2⟩ := hv2 y hy hy1 hZy
    refine ⟨⟨c1, c2⟩, ?_⟩
    rw [LvET.val_sm, e1, e2, ← ggTh_add hy (hw.mono hZy), hcr]
  rcases (log_le_self ω a).lt_or_eq with hL | hL
  · obtain ⟨l, hl, hb, hv⟩ := IH _ hL hlog (hL.trans haB)
    refine ⟨.pw l, hl, fun _ => hb hlogO, fun y hy hy1 hZy => ?_⟩
    obtain ⟨c1, e1⟩ := hv y hy hy1 hZy
    refine ⟨c1, ?_⟩
    rw [LvET.val_pw, e1, ← ggTh_opow hy (hlog.mono hZy), hwa']
  · -- an `ε`-number in `(Ω₁, ε_{Ω₁+1})`: impossible
    exfalso
    have haE : ω ^ a = a := by conv_lhs => rw [← hL]
                               exact hwa'
    have h1 := eN_le ha1 haE
    rw [← lveSC_eN ph_SC_Om1] at h1
    exact absurd haB (not_lt.2 h1)

/-- **The index of a code is a code** (every level code `a ≥ Ω₁`). -/
theorem lveIndCode (hZ : SC Z) {a b : Ordinal.{0}} (ha : GgCl Z a) (haO : Om 1 ≤ a) (hb : GgCl Z b)
    (hb0 : a = Om 1 → 0 < b) (hbv : b < veblen a b) :
    ∃ d, GgCl Z d ∧ d ≤ b ∧ ∀ y, SC y → y < Om 1 → Z ≤ y → ggTh y d = lvInd (ggTh y a) y (ggTh y b) := by
  have hyΘ : ∀ y, SC y → y < Om 1 → Z ≤ y → y ≤ ggTh y a := fun y hy hy1 hZy => by
    rcases haO.lt_or_eq with h | h
    · have := ggTh_lt (GgCl.om (Z := y)) h (y := y); rw [ggTh_Om1 hy hy1] at this; exact this.le
    · rw [← h, ggTh_Om1 hy hy1]
  have ha1 : GgCl Z (a + 1) := GgCl.add ha (GgCl.small (gg_one_lt_of_SC hZ))
  have hq : GgCl Z (veblen (a + 1) 0) := GgCl.phi ha1 (GgCl.zero hZ.1)
  have hqP : LuP (a + 1) (veblen (a + 1) 0) := luP_veblen _ _
  have hThq : ∀ y, SC y → y < Om 1 → Z ≤ y → ggTh y (veblen (a + 1) 0) = veblen (ggTh y a + 1) 0 :=
    fun y hy hy1 hZy => by
      rw [phTh_phi hy _ (ha1.mono hZy) _ (GgCl.zero hy.1), ggTh_add hy (ha.mono hZy),
        ggTh_small (gg_one_lt_of_SC hy).le, phTh_zero]
  have hPy : ∀ y v, LuP (ggTh y a + 1) v → veblen (ggTh y a + 1) 0 ≤ v := by
    intro y v hv
    obtain ⟨γ, rfl⟩ := hv
    exact veblen_le_veblen_iff_right.2 zero_le
  rcases lt_or_ge b (veblen (a + 1) 0) with hbq | hbq
  · -- below the first member of `P_{Ω₁+a+1}`: no member of `P_{y+a+1}` below `Θ_y(b)`
    have hnoP : ∀ y, SC y → y < Om 1 → Z ≤ y → ∀ z, z < ggTh y b → ¬ LuP (ggTh y a + 1) z := by
      intro y hy hy1 hZy z hz hP
      have h1 := ggTh_lt (hb.mono hZy) hbq (y := y)
      rw [hThq y hy hy1 hZy] at h1
      exact absurd (hPy y z hP) (not_le.2 (hz.trans h1))
    by_cases hka : a = Om 1
    · have hb0' := hb0 hka
      have hb1 : 1 ≤ b := one_le_iff_pos.2 hb0'
      refine ⟨b - 1, (ggDec hZ b hb).1 1 (GgCl.small (gg_one_lt_of_SC hZ)) hb1, Ordinal.sub_le_self _ _,
        fun y hy hy1 hZy => ?_⟩
      have hbe : ggTh y b = 1 + ggTh y (b - 1) := by
        conv_lhs => rw [← Ordinal.add_sub_cancel_of_le hb1]
        rw [ggTh_add hy (GgCl.small (gg_one_lt_of_SC hy)), ggTh_small (gg_one_lt_of_SC hy).le]
      have hn := hnoP y hy hy1 hZy
      rw [hka, ggTh_Om1 hy hy1] at hn ⊢
      rw [hbe]
      refine (lvInd_low_eq hy.veblen_zero fun z hz => hn (1 + z) ?_).symm
      rw [hbe]
      exact (add_lt_add_iff_left 1).2 hz
    · refine ⟨b, hb, le_rfl, fun y hy hy1 hZy => ?_⟩
      have hy0 : y < veblen (ggTh y a) 0 := by
        calc y = veblen y 0 := hy.veblen_zero.symm
          _ < veblen (ggTh y a) 0 := veblen_zero_lt_veblen_zero.2 (by
              have := ggTh_lt (GgCl.om (Z := y)) (lt_of_le_of_ne haO (Ne.symm hka)) (y := y)
              rwa [ggTh_Om1 hy hy1] at this)
      exact (lvInd_low_gt hy0 (hnoP y hy hy1 hZy)).symm
  · have hqb : veblen (a + 1) 0 < b := lt_of_le_of_ne hbq fun e => by
      have h1 : veblen (a) (veblen (a + 1) 0) = veblen (a + 1) 0 :=
        veblen_veblen_of_lt (lt_add_one _) _
      rw [← e] at hbv; rw [h1] at hbv; exact lt_irrefl _ hbv
    obtain ⟨c, n, hc, hdc, hbc, hθc⟩ := phSplit hZ b hb
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
    have hThp : ∀ y, SC y → y < Om 1 → Z ≤ y → y < ggTh y c := fun y hy hy1 hZy => by
      have := ggTh_lt (GgCl.om (Z := y)) hc1 (y := y); rwa [ggTh_Om1 hy hy1] at this
    by_cases hfa : veblen (a) c = c
    · -- `b = c + n`, `c ∈ P_{Ω₁+a+1}`: `d = c + (n - 1)`
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [Nat.cast_zero, add_zero] at hbc
        rw [hbc, hfa] at hbv; exact lt_irrefl _ hbv
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      refine ⟨c + m, GgCl.add hc (ph_cl_nat hZ m), ?_, fun y hy hy1 hZy => ?_⟩
      · rw [hbc]; exact (add_le_add_iff_left _).2 (by exact_mod_cast Nat.le_succ m)
      · have hcy := hc.mono hZy
        have hP : LuP (ggTh y a + 1) (ggTh y c) := by
          refine luP_succ.2 ?_
          rw [← phTh_phi hy _ (ha.mono hZy) _ hcy, hfa]
        have e : ggTh y b = ggTh y c + 1 + m := by
          rw [hbc, phTh_add_nat hy hcy, add_assoc]; congr 1; exact_mod_cast Nat.add_comm m 1
        rw [phTh_add_nat hy hcy, e, lvInd_above hP (hThp y hy hy1 hZy) fun z hz => ?_]
        obtain ⟨j, rfl⟩ := lt_omega0.1 (hz.trans (natCast_lt_omega0 m))
        exact lu_P_nat_not _ j
    · -- otherwise `d = b`
      refine ⟨b, hb, le_rfl, fun y hy hy1 hZy => ?_⟩
      have hcy := hc.mono hZy
      have hby := hb.mono hZy
      set β := ggTh y b with hβ
      have hβP : ¬ LuP (ggTh y a + 1) β := by
        intro hP
        have h1 := ggTh_lt hby hbv
        rw [phTh_phi hy _ (ha.mono hZy) _ hby, ← hβ, luP_succ.1 hP] at h1
        exact lt_irrefl _ h1
      set s := {v | LuP (ggTh y a + 1) v ∧ v < β} with hs
      have hqs : ggTh y (veblen (a + 1) 0) ∈ s :=
        ⟨by rw [hThq y hy hy1 hZy]; exact luP_veblen _ _, ggTh_lt (hq.mono hZy) hqb⟩
      have hne : s.Nonempty := ⟨_, hqs⟩
      have hbdd : BddAbove s := ⟨β, fun v hv => hv.2.le⟩
      have hpP : LuP (ggTh y a + 1) (sSup s) := by
        refine luP_succ.2 ?_
        rw [(isNormal_veblen (ggTh y a)).map_sSup hne hbdd]
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
          _ < veblen (ggTh y a + 1) 0 :=
            veblen_zero_lt_veblen_zero.2 ((hyΘ y hy hy1 hZy).trans_lt (lt_add_one _))
      set p := sSup s with hp
      have hδ : p + 1 + (β - (p + 1)) = β := Ordinal.add_sub_cancel_of_le (Order.add_one_le_of_lt hpβ)
      have hgap : ∀ z < β - (p + 1), ¬ LuP (ggTh y a + 1) (p + 1 + z) := by
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
        refine phTh_inj (GgCl.phi (ha.mono hZy) hcy) hcy ?_
        rw [phTh_phi hy _ (ha.mono hZy) _ hcy, e2]
        exact luP_succ.1 hpP
      conv_rhs => rw [← hδ]
      rw [lvInd_above hpP hyp hgap]
      conv_lhs => rw [← hδ]
      rw [add_assoc p 1, one_add_of_omega0_le hω]

/-- **The code of the top**: `φ(ε_{Ω₁+1}, 0)`. -/
noncomputable def lveTc : Ordinal.{0} := veblen (veblen 1 (Om 1 + 1)) 0

theorem lve_cl_T (hZ : SC Z) : GgCl Z lveTc :=
  GgCl.phi (GgCl.phi (GgCl.small (gg_one_lt_of_SC hZ)) (ph_cl_Om1_one hZ)) (GgCl.zero hZ.1)

theorem lve_Om1_le_T : Om 1 ≤ lveTc :=
  (le_self_add.trans (right_le_veblen _ _)).trans (left_le_veblen _ _)

theorem lve_T_lt_Gam : lveTc < ggGam := by
  have h1 : Om 1 + 1 < ggGam := ggGam_spec.1.add_one_lt ggGam_spec.2
  have h2 : veblen 1 (Om 1 + 1) < ggGam :=
    ggGam_spec.1.2 1 (gg_one_lt_of_SC ggGam_spec.1) _ h1
  exact ggGam_spec.1.2 _ h2 _ ggGam_spec.1.1

/-- **`Θ_y(φ(ε_{Ω₁+1}, 0)) = φ(ε_{y+1}, 0) = ϑʸ(Ω₁·ε_{y+1})`** for a strongly critical `y < Ω₁`. -/
theorem lveTh_T {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) : ggTh y lveTc = lveTop y := by
  have hyE : InE y := gg_SC_eps hy
  have hy1' : y < Om1 := by rw [ph_Om1_eq]; exact hy1
  have hc1 : GgCl y (veblen 1 (Om 1 + 1)) := GgCl.phi (GgCl.small (gg_one_lt_of_SC hy)) (ph_cl_Om1_one hy)
  have hw : ggTh y (veblen 1 (Om 1 + 1)) = eN y := by
    rw [phTh_phi hy _ (GgCl.small (gg_one_lt_of_SC hy)) _ (ph_cl_Om1_one hy), ggTh_small (gg_one_lt_of_SC hy).le,
      phTh_Om1_one hy hy1, lveSC_eN hy]
  unfold lveTc
  rw [phTh_phi hy _ hc1 _ (GgCl.zero hy.1), hw, phTh_zero]
  apply le_antisymm
  · obtain ⟨j, hj⟩ := lve_top_P hyE hy1'
    rw [← hj]
    exact (veblen_le_veblen_iff_right).2 zero_le
  · refine lve_top_least hyE hy1' (luP_veblen (eN y) 0) ?_
    calc y = veblen y 0 := hy.veblen_zero.symm
      _ < veblen (eN y) 0 := veblen_zero_lt_veblen_zero.2 (lt_eN y)

/-- **`lveSys` has terms for every code below `φ(ε_{Ω₁+1}, 0)`.** -/
theorem lvePoly : GgPoly lveSys lveTc := by
  refine phPoly_of_SC fun Z hZ _ => ?_
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hcB
  rcases lt_trichotomy c (Om 1) with hc1 | hc1 | hc1
  · have hcZ : c < Z := hc.lt_of_lt_Om1 hZ hc1
    exact ⟨LvET.cst c, fun y _ _ hZy =>
      ⟨lt_of_lt_of_le hcZ hZy, by show c = ggTh y c; rw [ggTh_small (hcZ.le.trans hZy)]⟩⟩
  · subst hc1
    exact ⟨LvET.bs, fun y hy hy1 _ => ⟨trivial, by show y = ggTh y (Om 1); rw [ggTh_Om1 hy hy1]⟩⟩
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
    refine ⟨LvET.sm s1 s2, fun y hy hy1 hZy => ?_⟩
    obtain ⟨c1, v1⟩ := hs1 y hy hy1 hZy
    obtain ⟨c2, v2⟩ := hs2 y hy hy1 hZy
    refine ⟨⟨c1, c2⟩, ?_⟩
    show lveSys.val s1 y + lveSys.val s2 y = _
    rw [v1, v2, ← ggTh_add hy (hw.mono hZy), hcr]
  rcases (log_le_self ω c).lt_or_eq with hL | hL
  · obtain ⟨s, hs⟩ := IH _ hL hlog (hL.trans hcB)
    refine ⟨LvET.pw s, fun y hy hy1 hZy => ?_⟩
    obtain ⟨c1, v1⟩ := hs y hy hy1 hZy
    refine ⟨c1, ?_⟩
    show ω ^ lveSys.val s y = _
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
  have haOO : a < veblen 1 (Om 1 + 1) := by
    have hlt : veblen a b < veblen (veblen 1 (Om 1 + 1)) 0 := by rw [hdec]; exact hcB
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
    refine ⟨LvET.th0 a t, fun y hy hy1 hZy => ?_⟩
    obtain ⟨ct, vt'⟩ := ht y hy hy1 hZy
    have hy1' : y < Om1 := by rw [ph_Om1_eq]; exact hy1
    have hay : a < y := haZ.trans_le hZy
    refine ⟨⟨ha1, hay, ct⟩, ?_⟩
    show vt y (Om1 * a + lveSys.val t y) = ggTh y c
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
    obtain ⟨htT, htlt⟩ := LvET.lve_T (gg_SC_eps hy) hy1' t ct
    have hTv : lveSys.val t y ∈ Tset y ∧ lveSys.val t y < Om1 :=
      ⟨htT, htlt.trans (lveTop_facts (gg_SC_eps hy) hy1').2.2.2.2.1⟩
    have e1 : lveSys.val t y = luInd a y (ggTh y b) := by rw [vt', hdθ y hy hy1 hZy]
    rw [e1] at hTv ⊢
    rw [hThc, luPhLev hy hy1' ha1 hay _ hyb hbP hTv.1 hTv.2]
  · -- a level code `Ω₁ ≤ a < ε_{Ω₁+1}`: the term `tl l t`
    obtain ⟨l, hl, hlB, hlv⟩ := levPoly hZ a ha haOO
    have hb0 : a = Om 1 → 0 < b := by
      intro hO
      rcases eq_or_ne b 0 with hb0 | hb0
      · exfalso
        rw [hO, hb0, hSC1.veblen_zero] at hdec
        rw [← hdec] at hc1
        exact lt_irrefl _ hc1
      · exact pos_iff_ne_zero.2 hb0
    obtain ⟨d, hd, hdb, hdθ⟩ := lveIndCode hZ ha haO hb hb0 hbv
    obtain ⟨t, ht⟩ := IH d (hdb.trans_lt hb1) hd ((hdb.trans_lt hb1).trans hcB)
    refine ⟨LvET.tl l t, fun y hy hy1 hZy => ?_⟩
    obtain ⟨ct, vt'⟩ := ht y hy hy1 hZy
    obtain ⟨clc, clv⟩ := hlv y hy hy1 hZy
    have hyE : InE y := gg_SC_eps hy
    have hy1' : y < Om1 := by rw [ph_Om1_eq]; exact hy1
    refine ⟨⟨hl, hlB haO, clc, ct⟩, ?_⟩
    show vt y (Om1 * LvET.val l y + lveSys.val t y) = ggTh y c
    have hby := hb.mono hZy
    have hThc : ggTh y c = veblen (ggTh y a) (ggTh y b) := by
      rw [← hdec, phTh_phi hy _ (ha.mono hZy) _ hby]
    have hyΘ : y ≤ ggTh y a := by
      rcases haO.lt_or_eq with h | h
      · have := ggTh_lt (GgCl.om (Z := y)) h (y := y); rw [ggTh_Om1 hy hy1] at this; exact this.le
      · rw [← h, ggTh_Om1 hy hy1]
    have hyb : y < veblen (ggTh y a) (ggTh y b) := by
      rcases haO.lt_or_eq with h | h
      · have h2 : y < ggTh y a := by
          have := ggTh_lt (GgCl.om (Z := y)) h (y := y); rwa [ggTh_Om1 hy hy1] at this
        calc y = veblen y 0 := hy.veblen_zero.symm
          _ < veblen (ggTh y a) 0 := veblen_zero_lt_veblen_zero.2 h2
          _ ≤ veblen (ggTh y a) (ggTh y b) := (veblen_le_veblen_iff_right).2 zero_le
      · rw [← h, ggTh_Om1 hy hy1]
        have hpos : 0 < ggTh y b := by
          have := ggTh_lt (GgCl.zero hy.1) (hb0 h.symm) (y := y); rwa [phTh_zero] at this
        calc y = veblen y 0 := hy.veblen_zero.symm
          _ < veblen y (ggTh y b) := (veblen_lt_veblen_iff_right).2 hpos
    have hbP : ¬ LuP (ggTh y a + 1) (ggTh y b) := by
      intro hP
      have h1 := ggTh_lt hby hbv
      rw [phTh_phi hy _ (ha.mono hZy) _ hby, luP_succ.1 hP] at h1
      exact lt_irrefl _ h1
    obtain ⟨htT, htlt⟩ := LvET.lve_T hyE hy1' t ct
    have hTv : lveSys.val t y ∈ Tset y ∧ lveSys.val t y < Om1 :=
      ⟨htT, htlt.trans (lveTop_facts hyE hy1').2.2.2.2.1⟩
    have e1 : lveSys.val t y = lvInd (ggTh y a) y (ggTh y b) := by rw [vt', hdθ y hy hy1 hZy]
    rw [e1] at hTv ⊢
    obtain ⟨hLT, hyL, hLe, hL1⟩ := lve_lev_facts hyE hy1' hl (hlB haO) clc
    rw [clv] at hLT hyL hLe hL1
    have hβ1 : 1 ≤ ggTh y a := (lu_one_lt_E hyE).le.trans hyL
    have hβu : ∀ u, LuP (ggTh y a) u → y < u → ggTh y a < u := by
      intro u hPu hyu
      refine lve_level_lt_P hβ1 ?_ hPu hyu
      rcases hyL.lt_or_eq with h | h
      · exact Or.inr (fun hE => absurd hLe (not_lt.2 (eN_le h hE)))
      · exact Or.inl h.ge
    rw [clv, hThc, lvPhLev hy hy1' hβ1 hLT hL1 hβu _ hyb hbP hTv.1 hTv.2]

end Codes

/-! ## The frontier lies below `L(0)` -/

variable {S : InaccSeq.{0}}

/-- **The frontier of `lveSys`**: `Λ(lveSys) ≤ ι(ω^{φ(ε_{Ω₁+1},0)})`, `Λ⁺(lveSys) ≤ ι(ω^{φ(ε_{Ω₁+1},0)}·ω) < L(0)`
and `υ_{Λ⁺(lveSys)} < L(0)`. -/
theorem lve_fr :
    (∀ n : ℕ, XtFr lveSys (iota S (ω ^ lveTc * ((n : Ordinal.{0}) + 1))) ∧
      upsilon (iota S (ω ^ lveTc * ((n : Ordinal.{0}) + 1))) = iota S (ω ^ lveTc * ((n : Ordinal.{0}) + 1))) ∧
    xtLam lveSys ≤ iota S (ω ^ lveTc) ∧ xtB1 lveSys ≤ iota S (ω ^ lveTc * ω) ∧
    iota S (ω ^ lveTc * ω) < Nc.ncL S 0 ∧ upsilon (xtB1 lveSys) < Nc.ncL S 0 :=
  phFrGen lve_T_lt_Gam (phPolyR_of lvePoly) (fun _ hy hy1 => (lveTh_T hy hy1).symm) (fun _ hZ => lve_cl_T hZ)
    lve_Om1_le_T

/-- **Where the frontier lies**: `ρ` of `Λ⁺(lvwSys)` < `ρ` of `Λ(lveSys)` < `ρ` of `Λ⁺(lveSys)` < `L(0) = m* ≤
L(n+1) < L(ω) < L(ω+1)`, and `Λ⁺(lveSys) < L(ω+1)`, unconditionally. -/
theorem lve_fr_order (n : ℕ) :
    upsilon (xtB1 lvwSys) < upsilon (xtLam lveSys) ∧ upsilon (xtLam lveSys) < upsilon (xtB1 lveSys) ∧
    upsilon (xtB1 lveSys) < Nc.ncL S 0 ∧ Nc.ncL S 0 ≤ Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ∧
    Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) < Nc.ncL S ω ∧ Nc.ncL S ω < Nc.ncL S (ω + 1) ∧
    xtB1 lveSys < Nc.ncL S (ω + 1) := by
  obtain ⟨h0, h1, h2⟩ := phL_chain (S := S) n
  have hU := (lve_fr (S := S)).2.2.2.2
  refine ⟨upsilon_normal.strictMono lveLam_gt, upsilon_normal.strictMono lve_lamLtB1, hU, h0, h1, h2, ?_⟩
  exact upsilon_normal.strictMono.le_apply.trans_lt (((hU.trans_le h0).trans h1).trans h2)

end Googology.Trans.PoR.InaccPsi.R2
