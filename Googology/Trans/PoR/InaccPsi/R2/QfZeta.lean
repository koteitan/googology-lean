import Googology.Trans.PoR.InaccPsi.R2.GqVb
import Googology.Trans.PoR.InaccPsi.R2.LvPh

/-!
# QfZeta: THE REACH OF A VEBLEN POINT IN `φ`-FORM, `lh(φ(A, B)) = luL(φ(A, B), A) + logend(B)`

`Gq.gq_lh_th` gives the `R₁⁺`-reach of a point `ϑʸ(Ω₁·q + r)` over a base `y` through its ϑ-index `r`:
`luL(·, q) + ζ`, `ζ = luZeta y q r`.  Here the index is traded for the `φ`-argument: for a strongly critical base
`y < Ω₁` and a point `X = φ(A, B) ∈ (y, Γ_{y+1})` with `B < X`, `1 ≤ A`:

* `qf_noSC` (no strongly critical ordinal in `(y, Γ_{y+1})`), `qf_dec` (**every `ε`-number of `(y, Γ_{y+1})` is
  `φ(q, b)` with `1 ≤ q`, `b < φ(q, b)`, `q` its ϑ-level**), `qf_level` (the ϑ-level of `φ(A, B)` is `A`);
* `qf_ind_lg` (**`logend(ind(B)) = logend(B)`** for a limit `B`, `ind = lvInd A y`: the blocks between the fixed
  points of `φ_A`), `qf_zeta` (**`ζ = luZeta y A (ind B) = logend(B)`**: at a limit `B` the condition of
  [W07a] Def 4.11 holds, at a successor `B = p + 1` with `p` a fixed point it fails);
* `qf_lh` (**`lh(φ(A, B)) = luL(φ(A, B), A) + logend(B)`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gq Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Ph Googology.Trans.PoR.InaccPsi.R2.Gg

theorem qf_lg_succ (x : Ordinal.{0}) : lg (x + 1) = 0 := by
  rw [lu_lg_add_right one_ne_zero]
  have := lg_nat (n := 1) one_ne_zero
  simpa using this

section Base

variable {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om1)
include hy hy1

omit hy1 in
theorem qf_yE : InE y := Low.opow_eq_self_of_SC hy

/-- **No strongly critical ordinal lies in `(y, Γ_{y+1})`.** -/
theorem qf_noSC {a : Ordinal.{0}} (hya : y < a) (haG : a < lgG y) (ha : veblen a 0 = a) : False := by
  have hyE := qf_yE hy
  have hE : InE a := by
    have h1 : (1 : Ordinal.{0}) ≤ a := one_le_iff_ne_zero.2 (lt_of_le_of_lt zero_le hya).ne'
    rw [← ha]; exact luP_E h1 (luP_veblen a 0)
  obtain ⟨q, r, hq1, hqT, hqΩ, hrT, hr1, hv⟩ := gq_th_rep hyE hy1 hE hya haG
  have hlev := gq_veb_level hyE hy1 hq1 hqT hqΩ hrT hr1
    (β := a) (one_le_iff_ne_zero.2 (lt_of_le_of_lt zero_le hya).ne')
  rw [hv] at hlev
  have haq : a ≤ q := hlev.1 ⟨0, ha⟩
  obtain ⟨-, -, hqv, -⟩ := gq_lh_th hyE hy1 hq1 hqT hqΩ hrT hr1
  rw [hv] at hqv
  exact absurd haq (not_le.2 hqv)

/-- **The ϑ-level of `φ(A, B)` (`B < φ(A, B)`) is `A`.** -/
theorem qf_level {A B q r : Ordinal.{0}} (hA1 : 1 ≤ A) (hBX : B < veblen A B) (hq1 : 1 ≤ q) (hqT : q ∈ Tset y)
    (hqΩ : q < Om1) (hrT : r ∈ Tset y) (hr1 : r < Om1) (hv : vt y (Om1 * q + r) = veblen A B) : q = A := by
  have hyE := qf_yE hy
  have h1 := (gq_veb_level hyE hy1 hq1 hqT hqΩ hrT hr1 (β := A) hA1).1 (by rw [hv]; exact luP_veblen A B)
  have h2 : ¬ A + 1 ≤ q := fun hle => by
    have hP := (gq_veb_level hyE hy1 hq1 hqT hqΩ hrT hr1 (β := A + 1) (hA1.trans le_self_add)).2 hle
    rw [hv] at hP
    have hfix := luP_succ.1 hP
    have : veblen A B = B := (isNormal_veblen A).strictMono.injective hfix
    exact absurd this hBX.ne'
  push Not at h2
  exact le_antisymm (Order.lt_add_one_iff.1 h2) h1

/-- **Every `ε`-number of `(y, Γ_{y+1})` is `φ(q, b)`** with `1 ≤ q < φ(q, b)`, `b < φ(q, b)`, `q` its ϑ-level. -/
theorem qf_dec {w : Ordinal.{0}} (hw : InE w) (hyw : y < w) (hwG : w < lgG y) :
    ∃ q b, 1 ≤ q ∧ q < w ∧ b < w ∧ veblen q b = w := by
  have hyE := qf_yE hy
  obtain ⟨q, r, hq1, hqT, hqΩ, hrT, hr1, hv⟩ := gq_th_rep hyE hy1 hw hyw hwG
  have hP : LuP q w := by
    rw [← hv]; exact (gq_veb_level hyE hy1 hq1 hqT hqΩ hrT hr1 hq1).2 le_rfl
  have hnP : ¬ LuP (q + 1) w := by
    rw [← hv]; intro h
    exact absurd ((gq_veb_level hyE hy1 hq1 hqT hqΩ hrT hr1 (hq1.trans le_self_add)).1 h)
      (not_le.2 (lt_add_one q))
  obtain ⟨-, -, hqv, -⟩ := gq_lh_th hyE hy1 hq1 hqT hqΩ hrT hr1
  rw [hv] at hqv
  obtain ⟨b, hb⟩ := hP
  refine ⟨q, b, hq1, hqv, lt_of_le_of_ne (hb ▸ right_le_veblen q b) fun e => hnP (luP_succ.2 (e ▸ hb)), hb⟩

section Point

variable {A B : Ordinal.{0}} (hA1 : 1 ≤ A) (hyX : y < veblen A B) (hXG : veblen A B < lgG y)
  (hBX : B < veblen A B)
include hA1 hyX hXG hBX

theorem qf_A_lt : A < lgG y := (left_le_veblen A B).trans_lt hXG

theorem qf_B_notP : ¬ LuP (A + 1) B := fun h => absurd (luP_succ.1 h) hBX.ne'

/-- The members of `P_A` above `y` lie above `A`. -/
theorem qf_hu : ∀ u, LuP A u → y < u → A < u := by
  intro u hu hyu
  rcases le_or_gt A y with hAy | hyA
  · exact hAy.trans_lt hyu
  · refine lt_of_le_of_ne ?_ fun e => ?_
    · obtain ⟨j, rfl⟩ := hu; exact left_le_veblen A j
    · obtain ⟨j, rfl⟩ := hu
      have h0 : veblen A 0 = A :=
        le_antisymm (((veblen_le_veblen_iff_right).2 zero_le).trans e.symm.le) (left_le_veblen A 0)
      exact qf_noSC hy hy1 hyA (qf_A_lt hy hy1 hA1 hyX hXG hBX) h0

theorem qf_AT : A ∈ Tset y ∧ A < Om1 := Gl.gl_T_of_lt_G (qf_yE hy) hy1 (qf_A_lt hy hy1 hA1 hyX hXG hBX)

/-- `ind(b) ∈ Tʸ ∩ Ω₁` for `b ≤ B`. -/
theorem qf_indT {b : Ordinal.{0}} (hbB : b ≤ B) : lvInd A y b ∈ Tset y ∧ lvInd A y b < Om1 :=
  Gl.gl_T_of_lt_G (qf_yE hy) hy1 (((cdOtp_le_self _ b).trans hbB).trans_lt (hBX.trans hXG))

/-- **The dictionary** at `b ≤ B` in `lvC A y`: `φ_A(b) = ϑʸ(Ω₁·A + ind(b))`. -/
theorem qf_dict {b : Ordinal.{0}} (hbB : b ≤ B) (hyb : y < veblen A b) (hbP : ¬ LuP (A + 1) b) :
    veblen A b = vt y (Om1 * A + lvInd A y b) := by
  obtain ⟨hAT, hAΩ⟩ := qf_AT hy hy1 hA1 hyX hXG hBX
  obtain ⟨hT, h1⟩ := qf_indT hy hy1 hA1 hyX hXG hBX hbB
  exact lvPhLev hy hy1 hA1 hAT hAΩ (qf_hu hy hy1 hA1 hyX hXG hBX) b hyb hbP hT h1

/-- **`logend(ind(B)) = logend(B)`** at a limit `B`. -/
theorem qf_ind_lg (hlim : IsSuccLimit B) : lg (lvInd A y B) = lg B := by
  classical
  have hB0 : B ≠ 0 := hlim.bot_lt.ne'
  set F := {p | LuP (A + 1) p ∧ y < p ∧ p ≤ B} with hF
  by_cases hne : F.Nonempty
  · have hbdd : BddAbove F := ⟨B, fun p hp => hp.2.2⟩
    set p₀ := sSup F with hp₀
    have hP : LuP (A + 1) p₀ := by
      refine luP_succ.2 ?_
      rw [(isNormal_veblen A).map_sSup hne hbdd]
      congr 1
      ext v
      constructor
      · rintro ⟨w, hw, rfl⟩; rw [luP_succ.1 hw.1]; exact hw
      · intro hv; exact ⟨v, hv, luP_succ.1 hv.1⟩
    obtain ⟨p, hpF⟩ := hne
    have hyp : y < p₀ := hpF.2.1.trans_le (le_csSup hbdd hpF)
    have hpB : p₀ ≤ B := csSup_le ⟨p, hpF⟩ fun q hq => hq.2.2
    have hpB' : p₀ < B := lt_of_le_of_ne hpB fun e => qf_B_notP hy hy1 hA1 hyX hXG hBX (e ▸ hP)
    have hle : p₀ + 1 ≤ B := Order.add_one_le_of_lt hpB'
    set d := B - (p₀ + 1) with hd
    have hBd : p₀ + 1 + d = B := Ordinal.add_sub_cancel_of_le hle
    have hgap : ∀ z < d, ¬ LuP (A + 1) (p₀ + 1 + z) := by
      intro z hz hPz
      have hzB : p₀ + 1 + z ≤ B := by rw [← hBd]; exact ((add_lt_add_iff_left _).2 hz).le
      have h1 : p₀ + 1 + z ≤ p₀ := le_csSup hbdd ⟨hPz, hyp.trans ((lt_add_one p₀).trans_le le_self_add), hzB⟩
      exact absurd h1 (not_le.2 ((lt_add_one p₀).trans_le le_self_add))
    have hd0 : d ≠ 0 := by
      intro h0
      rw [h0, add_zero] at hBd
      exact (not_isSuccLimit_succ p₀) (by rw [succ_eq_add_one, hBd]; exact hlim)
    have hind := lvInd_above (β := A) (y := y) hP hyp hgap
    rw [hBd] at hind
    rw [hind, lu_lg_add_right hd0, ← hBd, lu_lg_add_right hd0]
  · have hnF : ∀ p, LuP (A + 1) p → y < p → p ≤ B → False := fun p h1 h2 h3 => hne ⟨p, h1, h2, h3⟩
    rcases lt_trichotomy (veblen A 0) y with h0 | h0 | h0
    · -- `φ_A(0) < y`: `A < y`, `φ_A(y) = y`, `B = y + 1 + d`
      have hAy : A < y := by
        by_contra hc; push Not at hc
        exact absurd ((hc.trans (left_le_veblen A 0))) (not_le.2 h0)
      have hfy : veblen A y = y := hy.veblen_right hAy
      have hyB : y < B := by
        by_contra hc; push Not at hc
        have := (veblen_le_veblen_iff_right (o := A)).2 hc
        rw [hfy] at this
        exact absurd hyX (not_lt.2 this)
      have hle : y + 1 ≤ B := Order.add_one_le_of_lt hyB
      set d := B - (y + 1) with hd
      have hBd : y + 1 + d = B := Ordinal.add_sub_cancel_of_le hle
      have hd0 : d ≠ 0 := by
        intro hz; rw [hz, add_zero] at hBd
        exact (not_isSuccLimit_succ y) (by rw [succ_eq_add_one, hBd]; exact hlim)
      have hlow : cdOtp (lvC A y) (y + 1) = 0 := phOtp_low _ fun c hc => by
        refine Order.add_one_le_of_lt ?_
        by_contra hcy; push Not at hcy
        have := (veblen_le_veblen_iff_right (o := A)).2 hcy
        rw [hfy] at this
        exact absurd hc.1 (not_lt.2 this)
      have hsh := phOtp_shift (lvC A y) (y + 1) d fun z hz => by
        refine ⟨?_, fun hPz => hnF _ hPz ((lt_add_one y).trans_le le_self_add) ?_⟩
        · exact hfy.symm.trans_lt ((veblen_lt_veblen_iff_right).2 ((lt_add_one y).trans_le le_self_add))
        · rw [← hBd]; exact ((add_lt_add_iff_left _).2 hz).le
      have hind : lvInd A y B = d := by
        show cdOtp (lvC A y) B = d
        rw [← hBd, hsh, hlow, zero_add]
      rw [hind, ← hBd, lu_lg_add_right hd0]
    · -- `φ_A(0) = y`
      have hωB : ω ≤ B := omega0_le_of_isSuccLimit hlim
      have h1B : 1 + B = B := one_add_of_omega0_le hωB
      have hind := lvInd_low_eq (β := A) (y := y) (δ := B) h0 fun z hz hPz => by
        have hfix : veblen A (1 + z) = 1 + z := luP_succ.1 hPz
        refine hnF _ hPz ?_ ?_
        · refine lt_of_le_of_ne ?_ fun e => ?_
          · rw [← h0, ← hfix]; exact (veblen_le_veblen_iff_right).2 zero_le
          · have hy0 : 0 < y := hy.1.trans_le' zero_le |>.trans_le' le_rfl
            have h2 := (veblen_lt_veblen_iff_right (o := A)).2 (hy0.trans_le e.le)
            rw [h0, hfix, ← e] at h2
            exact lt_irrefl _ h2
        · rw [← h1B]; exact ((add_lt_add_iff_left _).2 hz).le
      rw [h1B] at hind
      rw [hind]
    · -- `y < φ_A(0)`
      have hind := lvInd_low_gt (β := A) (y := y) (δ := B) h0 fun z hz hPz => by
        have hfix : veblen A z = z := luP_succ.1 hPz
        refine hnF z hPz ?_ hz.le
        rw [← hfix]; exact h0.trans_le ((veblen_le_veblen_iff_right).2 zero_le)
      rw [hind]

/-- **`ζ = luZeta y A (ind B) = logend(B)`.** -/
theorem qf_zeta : luZeta y A (lvInd A y B) = lg B := by
  classical
  have hyE := qf_yE hy
  obtain ⟨hAT, hAΩ⟩ := qf_AT hy hy1 hA1 hyX hXG hBX
  have hBnP := qf_B_notP hy hy1 hA1 hyX hXG hBX
  obtain ⟨hrT, hr1⟩ := qf_indT hy hy1 hA1 hyX hXG hBX (le_refl B)
  have hdictB := qf_dict hy hy1 hA1 hyX hXG hBX le_rfl hyX hBnP
  set r := lvInd A y B with hr
  have hrB : r ≤ B := cdOtp_le_self _ B
  rcases zero_or_succ_or_isSuccLimit B with hB0 | ⟨b', hb'⟩ | hlim
  · -- `B = 0`
    have : r = 0 := by rw [hr, hB0]; exact ggOtp_zero _
    rw [this, hB0, lu_zeta_zero]
    unfold lg; simp
  · -- `B = b' + 1`: `ζ = 0`
    subst hb'
    rw [succ_eq_add_one, qf_lg_succ]
    refine le_antisymm ?_ zero_le
    rcases zero_or_succ_or_isSuccLimit r with hr0 | ⟨s, hs⟩ | hrl
    · rw [hr0]; exact lu_zeta_le_lg.trans (by unfold lg; simp)
    · refine lu_zeta_le_lg.trans ?_; rw [← hs, succ_eq_add_one, qf_lg_succ]
    · -- `r` a limit: `b'` is a fixed point `p` above `y` and `r = p`
      have hb'C : b' ∉ lvC A y := by
        intro hc
        have := phOtp_shift (lvC A y) b' 1 fun z hz => by
          rw [Ordinal.lt_one_iff_zero.1 hz, add_zero]; exact hc
        rw [← succ_eq_add_one] at this
        have hr' : r = cdOtp (lvC A y) b' + 1 := by rw [hr]; exact this
        exact (not_isSuccLimit_succ (cdOtp (lvC A y) b')) (by rw [succ_eq_add_one, ← hr']; exact hrl)
      have hyb' : y < veblen A b' := by
        by_contra hc; push Not at hc
        have : r = 0 := by
          rw [hr]; refine phOtp_low _ fun c hc' => ?_
          refine Order.succ_le_of_lt ?_
          by_contra hcb; push Not at hcb
          exact absurd hc'.1 (not_lt.2 (((veblen_le_veblen_iff_right).2 hcb).trans hc))
        exact hrl.ne_bot this
      have hP : LuP (A + 1) b' := by
        by_contra hnP; exact hb'C ⟨hyb', hnP⟩
      have hfix : veblen A b' = b' := luP_succ.1 hP
      have hyp : y < b' := hfix ▸ hyb'
      have hrp : r = b' := by
        rw [hr]
        show cdOtp (lvC A y) (succ b') = b'
        rw [← cdOtp_eq_of_gap _ (le_succ b') fun c hc hpc hcp => by
          have : c = b' := le_antisymm (Order.lt_succ_iff.1 hcp) hpc
          exact hc.2 (this ▸ hP)]
        exact lvInd_P b' hP hyp
      refine (lu_zeta_fix fun σ hσ => ?_).le
      have hσB : σ ≤ succ b' := hσ.le.trans hrB
      obtain ⟨hσT, hσ1⟩ := Gl.gl_T_of_lt_G hyE hy1 (hσB.trans_lt (hBX.trans hXG))
      have hlt : vt y (Om1 * A + σ) < vt y (Om1 * A + r) :=
        Gl.glA_lt_of hyE hy1 hA1 hAT hAΩ hσT hrT hr1 hσ
      rw [← hdictB] at hlt
      obtain ⟨j, hj⟩ := lv_th_P hyE hy1 A hA1 hAT hAΩ σ hσT hσ1
      rw [← hj] at hlt ⊢
      have hjb : j ≤ b' := Order.lt_succ_iff.1 ((veblen_lt_veblen_iff_right).1 hlt)
      rw [hrp, ← hfix]
      exact (veblen_le_veblen_iff_right).2 hjb
  · -- `B` a limit: the condition of Def 4.11 holds
    rw [← qf_ind_lg hy hy1 hA1 hyX hXG hBX hlim]
    refine lu_zeta_lim ?_
    have hrX : r < veblen A B := hrB.trans_lt hBX
    obtain ⟨b, hbB, hrb⟩ := ((isNormal_veblen A).lt_iff_exists_lt hlim).1 hrX
    obtain ⟨b₀, hb₀B, hyb₀⟩ := ((isNormal_veblen A).lt_iff_exists_lt hlim).1 hyX
    set b₁ := max b b₀ + 1 with hb₁
    have hb₁B : b₁ < B := hlim.add_one_lt (max_lt hbB hb₀B)
    have hyb₁ : y < veblen A b₁ :=
      hyb₀.trans_le ((veblen_le_veblen_iff_right).2 ((le_max_right _ _).trans le_self_add))
    have hb₁P : ¬ LuP (A + 1) b₁ := lu_P_succ_not _
    have hb₁C : b₁ ∈ lvC A y := ⟨hyb₁, hb₁P⟩
    refine ⟨lvInd A y b₁, cdOtp_lt_of_mem hb₁C hb₁B, ?_⟩
    rw [← qf_dict hy hy1 hA1 hyX hXG hBX hb₁B.le hyb₁ hb₁P]
    exact hrb.trans ((veblen_lt_veblen_iff_right).2 ((le_max_left _ _).trans_lt (lt_add_one _)))

end Point

/-- **THE REACH OF A VEBLEN POINT**: for a strongly critical base `y < Ω₁` and `X = φ(A, B) ∈ (y, Γ_{y+1})`,
`1 ≤ A`, `B < X`: `lh(X) = luL(X, A) + logend(B)`. -/
theorem qf_lh {A B : Ordinal.{0}} (hA1 : 1 ≤ A) (hyX : y < veblen A B) (hXG : veblen A B < lgG y)
    (hBX : B < veblen A B) : IsLh1 (veblen A B) (luL (veblen A B) A + lg B) := by
  have hyE := qf_yE hy
  have hXE : InE (veblen A B) := luP_E hA1 (luP_veblen A B)
  obtain ⟨q, r, hq1, hqT, hqΩ, hrT, hr1, hv⟩ := gq_th_rep hyE hy1 hXE hyX hXG
  have hqA := qf_level hy hy1 hA1 hBX hq1 hqT hqΩ hrT hr1 hv
  subst hqA
  obtain ⟨hL, -⟩ := gq_lh_th hyE hy1 hq1 hqT hqΩ hrT hr1
  have hdict := qf_dict hy hy1 hq1 hyX hXG hBX le_rfl hyX (qf_B_notP hy hy1 hq1 hyX hXG hBX)
  obtain ⟨hiT, hi1⟩ := qf_indT hy hy1 hq1 hyX hXG hBX (le_refl B)
  have hri : r = lvInd q y B := by
    rcases lt_trichotomy r (lvInd q y B) with h | h | h
    · have := Gl.glA_lt_of hyE hy1 hq1 hqT hqΩ hrT hiT hi1 h
      exact absurd (hv.trans hdict) (ne_of_lt this)
    · exact h
    · have := Gl.glA_lt_of hyE hy1 hq1 hqT hqΩ hiT hrT hr1 h
      exact absurd (hv.trans hdict).symm (ne_of_lt this)
  rw [hv, hri, qf_zeta hy hy1 hq1 hyX hXG hBX] at hL
  exact hL

end Base

end Googology.Trans.PoR.InaccPsi.R2.Qf
