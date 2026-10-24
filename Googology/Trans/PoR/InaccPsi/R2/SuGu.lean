import Googology.Trans.PoR.InaccPsi.R2.SuRoad
import Googology.Trans.PoR.InaccPsi.R2.GkU9

/-!
# The offsets below `ζ_{a+1}`: the codes of `R2.Gk` (every pseudo-base `ε_{Ω₁+ν}`) as an offset code system

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

The codes `c < ζ_{Ω₁+1}` of `R2.GkU0` read `Gk.guR c x = ε_{x+ν(x)}^{k(x)}·d(x) + r(x)` (`rdc` below `ε_{Ω₁+1}`).
`R2.GkU2`–`GkU8` give monotonicity, `R(b+1) = R(b) + 1`, readings below `ζ_{x+1} = evZ x`, Lemma EXACT (`Gk.gu_pi`),
the last term with Lemma EXACT for its logend (`Gk.gu_ld`), and hull membership (`Gk.gu_mem`).  The missing field
is that the readings are ALL the ordinals below `ζ_{x+1}`:

* `suGu_ex` (**every `v < ζ_{x+1}` is the reading of a code with gate below `x`**: one induction on `v`; `v` lies in
  a bracket `[ε_{x+N}, ε_{x+N+1})`, `v = A^K·D + W` with `A = ε_{x+N}`, and `N, K, D, W < v` are readings of codes
  `n, k, d, w`; then `ε_{Ω₁+n}^k·d + w` is a normal-form code reading `v`);
* `suGu_ld` (the last exponent of a limit code moves with `π`), `suGu : SuCS` (**the offset code system with
  `V = evZ`**), `suGu_V`;
* `suGuReal_M`, `suGuReal_L` (**`LrReal S a υ_{a+ζ_{a+1}}` at `m*` and every `L(n+1)`**), `suGuShort_L`,
  `suGuShort_M` (**`a ≤₁ υ_{a+ζ_{a+1}}`**), `suGuRoad` (**the road with the gaps asked only above
  `υ_{a+ζ_{a+1}}`**), `suGuCL_iff_noUncov`, `suGuM_iff_noUncov` (**(CL) at `n` / `m* ≤₁ L(1)` iff no uncovered reach
  in `[υ_{a+ζ_{a+1}}, L(n+2))` / `[υ_{m*+ζ_{m*+1}}, L(1))`**), `suGu_gt_E` (`υ_{a+ε_{a+1}} < υ_{a+ζ_{a+1}}`),
  `suGuGap_of_gapE`.

No new axiom.  New definition: `suGu` (an instance of the structure `SuCS`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Su

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr Googology.Trans.PoR.InaccPsi.R2.Gk

variable {S : InaccSeq.{0}}

/-- **Every `v < ζ_{x+1}` is the reading of a code `c < ζ_{Ω₁+1}` with gate below `x`.** -/
theorem suGu_ex {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    ∀ v, v < evZ x → ∃ c, c < guB ∧ guG c < x ∧ guR c x = v := by
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  rcases lt_or_ge v (eN x) with hvE | hvE
  · obtain ⟨A, hA, hg, hr⟩ := Sr.srCode_ex hx hx1.le hvE
    exact ⟨A, hA.trans gfE_lt_guB, by rw [guG_low hA]; exact hg, by rw [guR_low hA]; exact hr⟩
  -- the bracket `[ε_{x+N}, ε_{x+N+1})` of `v`
  have hxv : x ≤ v := (lt_eN x).le.trans hvE
  obtain ⟨N, hNv, hN1, hN2⟩ := evA_bracket hx hxv (lt_evA_self hx hv)
  have hN0 : N ≠ 0 := by
    rintro rfl
    have e1 : evA x 1 = eN x := by rw [← zero_add (1 : Ordinal.{0}), evA_add_one, evA_zero hx]
    rw [zero_add, e1] at hN2
    exact absurd hvE (not_le.2 hN2)
  have hN1' : 1 ≤ N := Order.one_le_iff_ne_zero.2 hN0
  obtain ⟨n, hn, hgn, hrn⟩ := IH N hNv (hNv.trans hv)
  have hn0 : n ≠ 0 := by rintro rfl; rw [guR_zero] at hrn; exact hN0 hrn.symm
  have hn1 : 1 ≤ n := Order.one_le_iff_ne_zero.2 hn0
  set A := evA x N with hAdef
  have hAE : InE A := evA_E _ _
  have hAs : evA x (N + 1) = eN A := evA_add_one x N
  rw [hAs] at hN2
  have hA1 : (1 : Ordinal.{0}) < A := Lu.lu_one_lt_E hAE
  have hv0 : v ≠ 0 := (lt_of_lt_of_le hAE.pos hN1).ne'
  -- `v = A^K·D + W`
  set K := log A v with hKdef
  set D := v / A ^ K with hDdef
  set W := v % A ^ K with hWdef
  have hKv : K < v := gu_log_lt hAE hN1 hN2
  have hK0 : K ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (le_log_of_opow_le hA1 (by rw [opow_one]; exact hN1))).ne'
  have hAK : A ^ K ≤ v := opow_log_le_self A hv0
  have hAK0 : A ^ K ≠ 0 := (opow_pos K hAE.pos).ne'
  have hDA : D < A := div_opow_log_lt v hA1
  have hD0 : D ≠ 0 := (div_opow_log_pos A hv0).ne'
  have hWK : W < A ^ K := Ordinal.mod_lt v hAK0
  have hdec : A ^ K * D + W = v := Ordinal.div_add_mod v (A ^ K)
  obtain ⟨k, hk, hgk, hrk⟩ := IH K hKv (hKv.trans hv)
  obtain ⟨d, hd, hgd, hrd⟩ := IH D (hDA.trans_le hN1) ((hDA.trans_le hN1).trans hv)
  obtain ⟨w, hw, hgw, hrw⟩ := IH W (hWK.trans_le hAK) ((hWK.trans_le hAK).trans hv)
  have hk0 : k ≠ 0 := by rintro rfl; rw [guR_zero] at hrk; exact hK0 hrk.symm
  have hd0 : d ≠ 0 := by rintro rfl; rw [guR_zero] at hrd; exact hD0 hrd.symm
  -- the pseudo-base `E = ε_{Ω₁+n}` and the next one
  set E := evA Om1 n with hEdef
  have hEE : InE E := evA_E _ _
  have hEB : E < guB := gu_evA_lt hn
  have hgE : guG E < x := by rw [guG_base hn1 hn]; exact (guQ_le n).trans_lt hgn
  have hrE : guR E x = A := by rw [guR_base hn1 hn, hrn, guA_eq hx hN1']
  have hn1B : n + 1 < guB := guB_lim.add_one_lt hn
  have hE'B : evA Om1 (n + 1) < guB := gu_evA_lt hn1B
  have hgE' : guG (evA Om1 (n + 1)) < x := by
    rw [guG_base (hn1.trans le_self_add) hn1B]
    exact (guQ_le _).trans_lt (guG_succ (So.soE_lim hx) n hn1B hgn)
  have hrE' : guR (evA Om1 (n + 1)) x = eN A := by
    rw [guR_base (hn1.trans le_self_add) hn1B, guR_succ_all, hrn, guA_succ x hN1', guA_eq hx hN1']
  have hE' : evA Om1 (n + 1) = eN E := evA_add_one Om1 n
  -- `d < E`, `k < ε_{E+1}`, `w < E^k`
  have hlt_of : ∀ {p q : Ordinal.{0}}, p < guB → guG p < x → q < guB → guG q < x →
      guR p x < guR q x → p < q := by
    intro p q hp hgp hq hgq h
    rcases lt_trichotomy p q with h' | h' | h'
    · exact h'
    · rw [h'] at h; exact absurd h (lt_irrefl _)
    · exact absurd h (not_lt.2 (guR_mono hx hp h' hgp hgq).le)
  have hdE : d < E := hlt_of hd hgd hEB hgE (by rw [hrd, hrE]; exact hDA)
  have hkE : k < eN E := by
    rw [← hE']; exact hlt_of hk hgk hE'B hgE' (by rw [hrk, hrE']; exact hKv.trans hN2)
  have hEk : E ^ k < evA Om1 (n + 1) := by rw [hE']; exact gu_pow_lt_eN hEE hkE
  have hEkB : E ^ k < guB := hEk.trans hE'B
  obtain ⟨hrEk, hgEk⟩ := guR_pow hn1 hk0 hEk hEkB
  have hgEk' : guG (E ^ k) < x := by
    rw [hgEk]; exact max_lt ((guQ_le n).trans_lt hgn) ((guQ_le k).trans_lt hgk)
  have hrEk' : guR (E ^ k) x = A ^ K := by rw [hrEk x, hrn, guA_eq hx hN1', hrk]
  have hwE : w < E ^ k := hlt_of hw hgw hEkB hgEk' (by rw [hrw, hrEk']; exact hWK)
  have hv' : E ^ k * d + w < evA Om1 (n + 1) := by
    have hk1 : k + 1 < eN E := (So.soE_lim (eN_E E)).add_one_lt hkE
    calc E ^ k * d + w < E ^ k * d + E ^ k := (add_lt_add_iff_left _).2 hwE
      _ = E ^ k * (d + 1) := by rw [mul_add_one]
      _ ≤ E ^ k * E := mul_le_mul_right (Order.add_one_le_of_lt hdE) _
      _ = E ^ (k + 1) := by rw [opow_add, opow_one]
      _ < eN E := gu_pow_lt_eN hEE hk1
      _ = evA Om1 (n + 1) := hE'.symm
  have hB' : E ^ k * d + w < guB := hv'.trans hE'B
  refine ⟨E ^ k * d + w, hB', ?_, ?_⟩
  · rw [guG_cnf hn1 hk0 hd0 hdE hwE hv' hB']
    exact max_lt (max_lt ((guQ_le n).trans_lt hgn) ((guQ_le k).trans_lt hgk))
      (max_lt ((guQ_le d).trans_lt hgd) hgw)
  · rw [guR_cnf hn1 hk0 hd0 hdE hwE hv' hB', hrn, hrk, hrd, hrw, guA_eq hx hN1']
    exact hdec

/-- The last exponent of a limit code moves with `π_{σ,ρ}`. -/
theorem suGu_ld {σ ρ c : Ordinal.{0}} (hB : Bases σ ρ) (hl : IsSuccLimit c) (hc : c < guB) (hg : guG c < σ) :
    cdExp (guR c ρ) ∈ TB ρ σ ∧ pi σ ρ (cdExp (guR c ρ)) = cdExp (guR c σ) := by
  have hld := gu_ld c hl hc
  unfold GuLD at hld
  obtain ⟨_cp, _lp, T, -, -, hdec, hpi⟩ := hld
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hT : ∀ y, InE y → y < Om1 → guG c < y → cdExp (guR c y) = T y := by
    intro y hy hy1 hgy
    obtain ⟨e1, e2, -, -⟩ := hdec y hy hy1 hgy
    rw [e1]
    exact Ge.lg_add_opow e2
  rw [hT ρ hB.2.1 hρ1 (hg.trans hB.2.2.1), hT σ hB.1 hσ1 hg]
  exact hpi σ ρ hB hg

/-- **The offset code system of `R2.Gk`**: codes below `ζ_{Ω₁+1}`, readings below `V x = ζ_{x+1}`. -/
noncomputable def suGu : SuCS where
  R := guR
  G := guG
  B := guB
  V := evZ
  B_lim := guB_lim
  B_le := fun S k => evZ_le (by rw [Br.Om1_eq]; exact Rp.rpOm1_lt_th (S := S) k)
    (Mv.mvEps_fix_of_SC (Ls.lsTh_SC (k + 1)))
  zero_R := guR_zero
  zero_G := guG_zero
  succ_R := fun b x _ => guR_succ_all b x
  succ_G := fun b _ hb hZ hg => guG_succ hZ b (guB_lim.add_one_lt hb) hg
  R_mono := fun _ _ _ hx hc hbc hgb hgc => guR_mono hx hc hbc hgc hgb
  R_lt := fun _ c hx _ hc hg => guR_lt_evZ hx c hc hg
  R_ex := fun _ ν hx hx1 hν => suGu_ex hx hx1 ν hν
  R_pi := fun _ _ c hB hc hg => gu_pi hB c hc hg
  R_ld := fun _ _ _ hB hl hc hg => suGu_ld hB hl hc hg
  R_mem := fun _ _ _ c hc hg e he => (gu_mem c hc hg).2 e he
  V_E := fun x _ _ => evZ_E x
  V_gt := fun x _ _ => lt_evZ x
  V_le := fun _ _ hx hx1 hxu hu => evZ_le_ups hx hx1 hxu hu

theorem suGu_V : suGu.V = evZ := rfl

/-! ## The realizers and the road up to `υ_{a+ζ_{a+1}}` -/

/-- **The realizers at `m*` up to `υ_{m*+ζ_{m*+1}} < L(1)`**, given `L(ω) ≤ ν_C`. -/
theorem suGuReal_M (hlow : Nc.ncL S ω ≤ nuC)
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (hstd : Cx.CxStdPairTop S) :
    LrReal S (Nc.ncL S 0) (upsilon (Nc.ncL S 0 + evZ (Nc.ncL S 0))) ∧
      upsilon (Nc.ncL S 0 + evZ (Nc.ncL S 0)) < Nc.ncL S 1 :=
  suReal_M suGu hlow hU hL hstd

/-- **The realizers at `L(n+1)` up to `υ_{a+ζ_{a+1}} < L(n+2)`**, given `L(ω) ≤ ν_C`. -/
theorem suGuReal_L (hlow : Nc.ncL S ω ≤ nuC)
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (hstd : Cx.CxStdPairTop S) (n : ℕ) :
    LrReal S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + evZ (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))) ∧
      upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + evZ (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))) <
        Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) :=
  suReal_L suGu hlow hU hL hstd n

/-- **`L(n+1) ≤₁ υ_{a+ζ_{a+1}}`** from UPPER, CapV, LOWER. -/
theorem suGuShort_L (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (n : ℕ) :
    le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + evZ (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))) :=
  suShort_L suGu hU hV hVt hL n

/-- **`m* ≤₁ υ_{m*+ζ_{m*+1}}`** from UPPER, CapV, LOWER. -/
theorem suGuShort_M (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) :
    le1 (Nc.ncL S 0) (upsilon (Nc.ncL S 0 + evZ (Nc.ncL S 0))) :=
  suShort_M suGu hU hV hVt hL

/-- **The road with the gaps asked only above `υ_{a+ζ_{a+1}}`** (at `m*` and every `L(n+1)`). -/
theorem suGuRoad (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S) (hmove : Cx.CxStdMoveTop S)
    (h0 : LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + evZ (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + evZ (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  suRoad suGu hU hO hL hV hVt hEQ htop hmove h0 hn

/-- **(CL) at `n` iff no uncovered reach of `L(n+1)` in `[υ_{a+ζ_{a+1}}, L(n+2))`** (UPPER, CapV, LOWER). -/
theorem suGuCL_iff_noUncov (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (n : ℕ) :
    le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})) ↔
      ¬ ∃ r, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) r ∧
        upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + evZ (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))) ≤ r ∧
        r < Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) ∧
        ∀ l, CdRange S l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ≤ upsilon l → upsilon l ≤ r →
          cdR S l ≤ r :=
  suCL_iff_noUncov suGu hU hV hVt hL n

/-- **`m* ≤₁ L(1)` iff no uncovered reach of `m*` in `[υ_{m*+ζ_{m*+1}}, L(1))`** (UPPER, CapV, LOWER). -/
theorem suGuM_iff_noUncov (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) :
    le1 (Nc.ncL S 0) (Nc.ncL S 1) ↔
      ¬ ∃ r, IsReach R2C (Nc.ncL S 0) r ∧ upsilon (Nc.ncL S 0 + evZ (Nc.ncL S 0)) ≤ r ∧
        r < Nc.ncL S 1 ∧
        ∀ l, CdRange S l → Nc.ncL S 0 ≤ upsilon l → upsilon l ≤ r → cdR S l ≤ r :=
  suM_iff_noUncov suGu hU hV hVt hL

/-- **The new bound is strictly larger**: `υ_{a+ε_{a+1}} < υ_{a+ζ_{a+1}}` for every `ε`-number `a`. -/
theorem suGu_gt_E {a : Ordinal.{0}} (haE : InE a) : upsilon (a + eN a) < upsilon (a + evZ a) := by
  have h1 : evA a 1 = eN a := by rw [← zero_add (1 : Ordinal.{0}), evA_add_one, evA_zero haE]
  have h2 : (2 : Ordinal.{0}) < evZ a :=
    (natCast_lt_omega0 2).trans ((omega0_lt_inE haE).trans (lt_evZ a))
  have h3 : eN a < evZ a := by
    rw [← h1]
    exact (evA_lt_iff.2 (by norm_num : (1 : Ordinal.{0}) < 2)).trans (evA_lt_evZ haE h2)
  exact upsilon_normal.strictMono ((add_lt_add_iff_left a).2 h3)

/-- **The gaps above `υ_{a+ε_{a+1}}` give the gaps above `υ_{a+ζ_{a+1}}`**: `suGuRoad` asks no more than
`Sr.srRoad_E`. -/
theorem suGuGap_of_gapE {a b : Ordinal.{0}} (haE : InE a) (ha1 : a < Om1)
    (h : LrGap S a b (upsilon (a + eN a))) : LrGap S a b (upsilon (a + evZ a)) :=
  suGap_of_gapE suGu haE ha1 h

end Googology.Trans.PoR.InaccPsi.R2.Su
