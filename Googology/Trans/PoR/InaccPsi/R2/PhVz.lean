import Googology.Trans.PoR.InaccPsi.R2.PhLev
import Googology.Trans.PoR.InaccPsi.R2.GgUni
import Googology.Trans.PoR.InaccPsi.R2.XtVz

/-!
# `vzSys` has terms for every code below the code `φ(ω, Ω₁ + 1)` of `B`

`phB = φ(ω, Ω₁ + 1)`.  `Θ_y(phB) = φ(ω, y + 1) = B(y)` (`phTh_B`; `B = VzB` is the least value of `φ(ω, ·)` above
`y`, `R2.vzB_omega`).

* `phPoly_of_SC` (**reduction to strongly critical `Z`**: `GgPoly X E` follows from its instances at the strongly
  critical `Z < Ω₁`, since the least strongly critical `Z' ≥ Z` has the same `y`'s);
* `phIndCode` (**the index of a code is a code**): for `k < ω` and a code `b > Ω₁` over a strongly critical `Z`
  with `b < φ_k(b)`, there is a code `d ≤ b` over `Z` with `Θ_y(d) = ind_k^y(Θ_y(b))` at every strongly critical
  `y ≥ Z` below `Ω₁`: `d = b - (Ω₁ + 1)` if `b < φ_{k+1}(Ω₁ + 1)`; `d = a + (n - 1)` if `b = a + n`, `ω ∣ a`,
  `a ∈ P_{k+1}`; `d = b` otherwise (`R2.Ph.phInd_low`, `phInd_above`, the φ-law);
* `phPoly_vz` (**`GgPoly vzSys phB`**): a code `c < phB` over `Z` is a constant (`c < Ω₁`), the base (`c = Ω₁`), a
  sum, a power `ω^t`, or `φ_k(b)` with `1 ≤ k < ω`, `b < φ_k(b)`, `b > Ω₁` (Veblen decomposition `R2.Ph.phDec`,
  `phB` bounds the first argument); then `Θ_y(φ_k(b)) = φ_k(Θ_y(b)) = ϑʸ(Ω₁·k + Θ_y(d))` (`R2.Ph.phLev`), the
  value of the term `th k t` for the term `t` of `d`;
* `phTh_B`: `Θ_y(phB) = VzB y`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ph

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xt

/-- The code `φ(ω, Ω₁ + 1)` of `B`. -/
noncomputable def phB : Ordinal.{0} := veblen ω (Om 1 + 1)

theorem ph_omega_lt {y : Ordinal.{0}} (hy : SC y) : ω < y := by
  have := hy.2 0 hy.1 1 (gg_one_lt_of_SC hy)
  rwa [veblen_zero_apply, opow_one] at this

theorem ph_Om1_eq : Om1 = Om (1 : Ordinal.{0}) := Br.Om1_eq

/-- **Reduction to strongly critical `Z`.** -/
theorem phPoly_of_SC {X : XtSys} {E : Ordinal.{0}}
    (h : ∀ Z, SC Z → Z < Om 1 → ∀ c, GgCl Z c → c < E → ∃ s : X.Tm, ∀ y, SC y → y < Om 1 → Z ≤ y →
      X.CB s y ∧ X.val s y = ggTh y c) : GgPoly X E := by
  intro Z c hc hcE
  by_cases hex : ∃ y, SC y ∧ y < Om 1 ∧ Z ≤ y
  · have hmem : sInf {y | SC y ∧ y < Om 1 ∧ Z ≤ y} ∈ {y | SC y ∧ y < Om 1 ∧ Z ≤ y} := csInf_mem hex
    obtain ⟨h1, h2, h3⟩ := hmem
    obtain ⟨s, hs⟩ := h _ h1 h2 c (hc.mono h3) hcE
    exact ⟨s, fun y hy hy1 hZy => hs y hy hy1 (csInf_le' ⟨hy, hy1, hZy⟩)⟩
  · push Not at hex
    exact ⟨X.cst 0, fun y hy hy1 hZy => absurd hZy (not_le.2 (hex y hy hy1))⟩

variable {Z : Ordinal.{0}}

theorem ph_cl_nat (hZ : SC Z) (n : ℕ) : GgCl Z (n : Ordinal.{0}) := GgCl.small (ph_nat_lt hZ n)

theorem ph_cl_Om1_one (hZ : SC Z) : GgCl Z (Om 1 + 1) := GgCl.add GgCl.om (GgCl.small (gg_one_lt_of_SC hZ))

theorem phTh_Om1_one {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) : ggTh y (Om 1 + 1) = y + 1 := by
  rw [ggTh_add hy GgCl.om, ggTh_Om1 hy hy1, ggTh_small (gg_one_lt_of_SC hy).le]

theorem ph_P_dvd {k : ℕ} {v : Ordinal.{0}} (h : VzP (k + 1) v) : ω ∣ v :=
  isSuccPrelimit_iff_omega0_dvd.1 (ph_P_lim h).isSuccPrelimit

/-- `φ_k` read over `y`: `Θ_y(φ_k(b)) = φ_k(Θ_y(b))`. -/
theorem phTh_veblen_nat {y : Ordinal.{0}} (hy : SC y) (k : ℕ) {b : Ordinal.{0}} (hb : GgCl y b) :
    ggTh y (veblen (k : Ordinal.{0}) b) = veblen (k : Ordinal.{0}) (ggTh y b) := by
  rw [phTh_phi hy _ (ph_cl_nat hy k) b hb, phTh_nat hy]

/-- **The index of a code is a code.** -/
theorem phIndCode (hZ : SC Z) {k : ℕ} {b : Ordinal.{0}} (hb : GgCl Z b) (hb1 : Om 1 < b)
    (hbv : b < veblen (k : Ordinal.{0}) b) :
    ∃ d, GgCl Z d ∧ d ≤ b ∧ ∀ y, SC y → y < Om 1 → Z ≤ y → ggTh y d = phInd k y (ggTh y b) := by
  set q := veblen ((k + 1 : ℕ) : Ordinal.{0}) (Om 1 + 1) with hqdef
  have hq : GgCl Z q := GgCl.phi (ph_cl_nat hZ _) (ph_cl_Om1_one hZ)
  have hqP : VzP (k + 1) q := vzP_veblen _ _
  -- facts at every base
  have hThq : ∀ y, SC y → y < Om 1 → Z ≤ y →
      ggTh y q = veblen ((k + 1 : ℕ) : Ordinal.{0}) (y + 1) := fun y hy hy1 _ => by
    rw [phTh_veblen_nat hy _ (ph_cl_Om1_one hy), phTh_Om1_one hy hy1]
  have hThb : ∀ y, SC y → y < Om 1 → Z ≤ y → y < ggTh y b := fun y hy hy1 hZy => by
    have := ggTh_lt (GgCl.om (Z := y)) hb1 (y := y); rwa [ggTh_Om1 hy hy1] at this
  have hPy : ∀ y, SC y → ∀ v, VzP (k + 1) v → y < v → veblen ((k + 1 : ℕ) : Ordinal.{0}) (y + 1) ≤ v := by
    intro y hy v hv hyv
    obtain ⟨γ, rfl⟩ := hv
    have hky : veblen ((k + 1 : ℕ) : Ordinal.{0}) y = y := hy.veblen_right (ph_nat_lt hy _)
    refine veblen_le_veblen_iff_right.2 (Order.add_one_le_of_lt ?_)
    by_contra hle
    push Not at hle
    have := (veblen_le_veblen_iff_right (o := ((k + 1 : ℕ) : Ordinal.{0}))).2 hle
    rw [hky] at this
    exact absurd hyv (not_lt.2 this)
  rcases lt_or_ge b q with hbq | hbq
  · -- `b < φ_{k+1}(Ω₁ + 1)`: `d = b - (Ω₁ + 1)`
    have hle : Om 1 + 1 ≤ b := Order.add_one_le_of_lt hb1
    refine ⟨b - (Om 1 + 1), (ggDec hZ b hb).1 _ (ph_cl_Om1_one hZ) hle, Ordinal.sub_le_self _ _,
      fun y hy hy1 hZy => ?_⟩
    have hdy : GgCl y (b - (Om 1 + 1)) := ((ggDec hZ b hb).1 _ (ph_cl_Om1_one hZ) hle).mono hZy
    have hbe : ggTh y b = y + 1 + ggTh y (b - (Om 1 + 1)) := by
      conv_lhs => rw [← Ordinal.add_sub_cancel_of_le hle]
      rw [ggTh_add hy (ph_cl_Om1_one hy), phTh_Om1_one hy hy1]
    rw [hbe, phInd_low]
    intro z hz hP
    have h1 : y + 1 + z < ggTh y b := by rw [hbe]; exact (add_lt_add_iff_left _).2 hz
    have h2 := hPy y hy _ hP ((lt_add_one y).trans_le le_self_add)
    rw [← hThq y hy hy1 hZy] at h2
    exact absurd (h2.trans_lt h1) (not_lt.2 (ggTh_lt (hb.mono hZy) hbq).le)
  · have hqb : q < b := lt_of_le_of_ne hbq fun e => by
      have h1 : veblen (k : Ordinal.{0}) q = q := by
        rw [hqdef, Nat.cast_succ]; exact veblen_veblen_of_lt (lt_add_one _) _
      rw [← e] at hbv; rw [h1] at hbv; exact lt_irrefl _ hbv
    obtain ⟨a, n, ha, hda, hba, hθa⟩ := phSplit hZ b hb
    have hqa : q ≤ a := by
      by_contra hlt
      push Not at hlt
      have key : a + n < q + (0 : ℕ) := by
        obtain ⟨u, rfl⟩ := hda
        obtain ⟨u', hu'⟩ := ph_P_dvd hqP
        rw [hu'] at hlt ⊢
        have hu : u < u' := (mul_lt_mul_iff_right₀ omega0_pos).1 hlt
        calc ω * u + n < ω * u + ω := (add_lt_add_iff_left _).2 (natCast_lt_omega0 n)
          _ = ω * (u + 1) := by rw [mul_add_one]
          _ ≤ ω * u' := by gcongr; exact Order.add_one_le_of_lt hu
          _ ≤ ω * u' + ((0 : ℕ) : Ordinal.{0}) := le_self_add
      rw [Nat.cast_zero, add_zero, ← hba] at key
      exact absurd hqb (not_lt.2 key.le)
    have ha1 : Om 1 < a := by
      refine lt_of_lt_of_le ?_ hqa
      exact (lt_add_one _).trans_le (right_le_veblen _ _)
    have hThp : ∀ y, SC y → y < Om 1 → Z ≤ y → y < ggTh y a := fun y hy hy1 hZy => by
      have := ggTh_lt (GgCl.om (Z := y)) ha1 (y := y); rwa [ggTh_Om1 hy hy1] at this
    by_cases hfa : veblen (k : Ordinal.{0}) a = a
    · -- `b = a + n`, `a ∈ P_{k+1}`: `d = a + (n - 1)`
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [Nat.cast_zero, add_zero] at hba
        rw [hba, hfa] at hbv; exact lt_irrefl _ hbv
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      refine ⟨a + m, GgCl.add ha (ph_cl_nat hZ m), ?_, fun y hy hy1 hZy => ?_⟩
      · rw [hba]; exact (add_le_add_iff_left _).2 (by exact_mod_cast Nat.le_succ m)
      · have hay := ha.mono hZy
        have hP : VzP (k + 1) (ggTh y a) := by
          refine vzP_succ.2 ?_
          rw [← phTh_veblen_nat hy k hay, hfa]
        have e : ggTh y b = ggTh y a + 1 + m := by
          rw [hba, phTh_add_nat hy hay, add_assoc]; congr 1; exact_mod_cast Nat.add_comm m 1
        rw [phTh_add_nat hy hay, e, phInd_above hP (hThp y hy hy1 hZy) fun z hz => ?_]
        obtain ⟨j, rfl⟩ := lt_omega0.1 (hz.trans (natCast_lt_omega0 m))
        exact ph_P_nat_not _ j
    · -- otherwise `d = b`
      refine ⟨b, hb, le_rfl, fun y hy hy1 hZy => ?_⟩
      have hay := ha.mono hZy
      have hby := hb.mono hZy
      set β := ggTh y b with hβ
      have hβP : ¬ VzP (k + 1) β := by
        intro hP
        have h1 := ggTh_lt hby hbv
        rw [phTh_veblen_nat hy k hby, ← hβ, vzP_succ.1 hP] at h1
        exact lt_irrefl _ h1
      set s := {v | VzP (k + 1) v ∧ v < β} with hs
      have hqs : ggTh y q ∈ s := ⟨by rw [hThq y hy hy1 hZy]; exact vzP_veblen _ _, ggTh_lt (hq.mono hZy) hqb⟩
      have hne : s.Nonempty := ⟨_, hqs⟩
      have hbdd : BddAbove s := ⟨β, fun v hv => hv.2.le⟩
      have hpP : VzP (k + 1) (sSup s) := by
        refine vzP_succ.2 ?_
        rw [(isNormal_veblen (k : Ordinal.{0})).map_sSup hne hbdd]
        congr 1
        ext v
        constructor
        · rintro ⟨w, hw, rfl⟩; rw [vzP_succ.1 hw.1]; exact hw
        · intro hv; exact ⟨v, hv, vzP_succ.1 hv.1⟩
      have hpβ : sSup s < β :=
        lt_of_le_of_ne (csSup_le hne fun v hv => hv.2.le) fun e => hβP (e ▸ hpP)
      have hyp : y < sSup s := by
        refine lt_of_lt_of_le ?_ (le_csSup hbdd hqs)
        rw [hThq y hy hy1 hZy]
        exact (lt_add_one y).trans_le (right_le_veblen _ _)
      set p := sSup s with hp
      have hδ : p + 1 + (β - (p + 1)) = β := Ordinal.add_sub_cancel_of_le (Order.add_one_le_of_lt hpβ)
      have hgap : ∀ z < β - (p + 1), ¬ VzP (k + 1) (p + 1 + z) := by
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
        have e1 : ggTh y a + (n : Ordinal.{0}) = p + ((1 + j : ℕ) : Ordinal.{0}) := by
          rw [← phTh_add_nat hy hay, ← hba, ← hβ, ← hδ, hj, add_assoc]; push_cast; rfl
        obtain ⟨e2, -⟩ := phSplit_uniq (hθa y hy hy1 hZy) (ph_P_dvd hpP) e1
        apply hfa
        refine phTh_inj (GgCl.phi (ph_cl_nat hy k) hay) hay ?_
        rw [phTh_veblen_nat hy k hay, e2]
        exact vzP_succ.1 hpP
      conv_rhs => rw [← hδ]
      rw [phInd_above hpP hyp hgap]
      conv_lhs => rw [← hδ]
      rw [add_assoc p 1, one_add_of_omega0_le hω]

/-- `Θ_y(φ(ω, b)) = φ(ω, Θ_y(b))`. -/
theorem phTh_veblen_omega {y : Ordinal.{0}} (hy : SC y) {b : Ordinal.{0}} (hb : GgCl y b) :
    ggTh y (veblen ω b) = veblen ω (ggTh y b) := by
  rw [phTh_phi hy _ (GgCl.small (ph_omega_lt hy)) b hb, ggTh_small (ph_omega_lt hy).le]

theorem ph_cl_B (hZ : SC Z) : GgCl Z phB := GgCl.phi (GgCl.small (ph_omega_lt hZ)) (ph_cl_Om1_one hZ)

/-- **`Θ_y(phB) = B(y)`**. -/
theorem phTh_B {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) : ggTh y phB = VzB y := by
  have hyE : InE y := gg_SC_eps hy
  have hy1' : y < Om1 := by rw [ph_Om1_eq]; exact hy1
  unfold phB
  rw [phTh_veblen_omega hy (ph_cl_Om1_one hy), phTh_Om1_one hy hy1]
  obtain ⟨⟨γ, hγ⟩, hyB, hmin⟩ := vzB_omega hyE hy1'
  apply le_antisymm
  · rw [← hγ]
    refine veblen_le_veblen_iff_right.2 (Order.add_one_le_of_lt ?_)
    by_contra hle
    push Not at hle
    have h2 := (veblen_le_veblen_iff_right (o := ω)).2 hle
    rw [hy.veblen_right (ph_omega_lt hy), hγ] at h2
    exact absurd hyB (not_lt.2 h2)
  · exact hmin _ ⟨_, rfl⟩ ((lt_add_one y).trans_le (right_le_veblen _ _))

/-- **`vzSys` has terms for every code below `phB`.** -/
theorem phPoly_vz : GgPoly vzSys phB := by
  refine phPoly_of_SC fun Z hZ _ => ?_
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hcB
  rcases lt_trichotomy c (Om 1) with hc1 | hc1 | hc1
  · have hcZ : c < Z := hc.lt_of_lt_Om1 hZ hc1
    exact ⟨VzTm.cst c, fun y _ _ hZy =>
      ⟨lt_of_lt_of_le hcZ hZy, by show c = ggTh y c; rw [ggTh_small (hcZ.le.trans hZy)]⟩⟩
  · subst hc1
    exact ⟨VzTm.bs, fun y hy hy1 _ => ⟨trivial, by show y = ggTh y (Om 1); rw [ggTh_Om1 hy hy1]⟩⟩
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
    refine ⟨VzTm.sm s1 s2, fun y hy hy1 hZy => ?_⟩
    obtain ⟨c1, v1⟩ := hs1 y hy hy1 hZy
    obtain ⟨c2, v2⟩ := hs2 y hy hy1 hZy
    refine ⟨⟨c1, c2⟩, ?_⟩
    show vzSys.val s1 y + vzSys.val s2 y = _
    rw [v1, v2, ← ggTh_add hy (hw.mono hZy), hcr]
  rcases (log_le_self ω c).lt_or_eq with hL | hL
  · -- a power `ω^L`, `L < c`
    obtain ⟨s, hs⟩ := IH _ hL hlog (hL.trans hcB)
    refine ⟨VzTm.pw s, fun y hy hy1 hZy => ?_⟩
    obtain ⟨c1, v1⟩ := hs y hy hy1 hZy
    refine ⟨c1, ?_⟩
    show ω ^ vzSys.val s y = _
    rw [v1, ← ggTh_opow hy (hlog.mono hZy), hwc']
  -- an `ε`-number: `c = φ_k(b)`
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
  have haω : a < ω := by
    by_contra hge
    push Not at hge
    have hlt : veblen a b < veblen ω (Om 1 + 1) := by rw [hdec]; exact hcB
    rcases veblen_lt_veblen_iff.1 hlt with ⟨e, hb'⟩ | ⟨h', _⟩ | ⟨_, h'⟩
    · have hbO : b ≤ Om 1 := Order.lt_add_one_iff.1 hb'
      have h3 := (veblen_le_veblen_iff_right (o := a)).2 hbO
      rw [hdec, e, hSC1.veblen_right (ph_omega_lt hSC1)] at h3
      exact absurd hc1 (not_lt.2 h3)
    · exact absurd h' (not_lt.2 hge)
    · rw [hdec] at h'
      exact absurd hc1 (not_lt.2 (Order.lt_add_one_iff.1 h'))
  obtain ⟨k, hk⟩ := lt_omega0.1 haω
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact absurd (by rw [hk, h, Nat.cast_zero]) ha0
    · exact h
  rw [hk] at hdec ha
  have hbO : Om 1 < b := by
    by_contra hle
    push Not at hle
    have h3 := (veblen_le_veblen_iff_right (o := (k : Ordinal.{0}))).2 hle
    rw [hdec, hSC1.veblen_right ((natCast_lt_omega0 k).trans (ph_omega_lt hSC1))] at h3
    exact absurd hc1 (not_lt.2 h3)
  have hbv : b < veblen (k : Ordinal.{0}) b := by rw [hdec]; exact hb1
  obtain ⟨d, hd, hdb, hdθ⟩ := phIndCode hZ hb hbO hbv
  obtain ⟨t, ht⟩ := IH d (hdb.trans_lt hb1) hd ((hdb.trans_lt hb1).trans hcB)
  refine ⟨VzTm.th k t, fun y hy hy1 hZy => ?_⟩
  obtain ⟨ct, vt'⟩ := ht y hy hy1 hZy
  have hy1' : y < Om1 := by rw [ph_Om1_eq]; exact hy1
  refine ⟨⟨hk1, ct⟩, ?_⟩
  show vt y (Om1 * (k : Ordinal.{0}) + vzSys.val t y) = ggTh y c
  have hby := hb.mono hZy
  have hThc : ggTh y c = veblen (k : Ordinal.{0}) (ggTh y b) := by
    rw [← hdec, phTh_veblen_nat hy k hby]
  have hyb : y < ggTh y b := by
    have := ggTh_lt (GgCl.om (Z := y)) hbO (y := y); rwa [ggTh_Om1 hy hy1] at this
  have hbP : ¬ VzP (k + 1) (ggTh y b) := by
    intro hP
    have h1 := ggTh_lt hby hbv
    rw [phTh_veblen_nat hy k hby, vzP_succ.1 hP] at h1
    exact lt_irrefl _ h1
  have hTv : vzSys.val t y ∈ Tset y ∧ vzSys.val t y < Om1 := vzv_T (gg_SC_eps hy) hy1' t ct
  have e1 : vzSys.val t y = phInd k y (ggTh y b) := by rw [vt', hdθ y hy hy1 hZy]
  rw [e1] at hTv ⊢
  rw [hThc, phLev hy hy1' hk1 _ hyb hbP hTv.1 hTv.2]

end Googology.Trans.PoR.InaccPsi.R2.Ph
