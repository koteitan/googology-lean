import Googology.Trans.PoR.InaccPsi.R2.XfRec

/-!
# XlBot: THE OFFSETS OF A LEVEL FROM THE BOTTOM: THE BASE `XlB` AND THE OFFSET PSEUDO-BASE

At a level `α = L + κ` (`Hn.HnLv` datum `Λ`, offset `κ < Ω₁`) below the first fixed point `N_α(0) = φ(α+1, 0)` of
`φ(α, ·)` the offsets start at `0`: the offset `λ` gives `φ(α, e + λ)`, `e = 1` when `α` is strongly critical
(`φ(α, 0) = α`: the level `G`), `e = 0` otherwise (the levels `G + κ`, `κ ≥ 1`), in place of `φ(α, F + 1 + λ)` over a
fixed point `F` (`Hn.HnVB`).

* `XlB Λ κ` (**A BOTTOM BASE**: the shift `e`, the reading gate `γN`, the reading `ϑˣ(Ω₁·(ℓ(x)+κ) + t) =
  φ(ℓ(x)+κ, e + t)` below `N_{ℓ(x)+κ}(0)` (field `read`), Lemma EXACT for `N_{ℓ(x)+κ}(0)` (field `N_pi`));
* `xl_N_eq`, `XlB.j_lt` (`e + λ < φ(α, e + λ)`), `XlB.Q_lt_N`, `XlB.cover`, `XlB.gate_of_jN` (**THE GATE OF AN
  OFFSET**: a code over a strongly critical `Z` in `[φ(α, e+λ), φ(α, e+λ+1))` forces `max(γN, g(λ)) < Z`);
* `xl_glA` (**`ϑˣ(Ω₁·Γ_{x+1} + t) = φ(Γ_{x+1}, 1 + t)` for every `t < N_{Γ_{x+1}}(0)`**, widening
  `Xf.xf_glA_veb`), `xl_glA_N`, `xl_glA_Ng` (`ϑˣ(Ω₁·(α+1)) = N_α(0)`);
* `xlOff` (**THE OFFSET PSEUDO-BASE**: for a system `E` reading the offset `λ < N`, the pseudo-base `φ(α, e + λ)`,
  reading `ϑˣ(Ω₁·(ℓ(x)+κ) + λ_E(x))`, gate `max(γN, g_E(λ))`, low field `XlB.Zl`).

No new axiom.  New definitions: `XlB`, `XlB.Zl`, `xlOff`, `xlMPB`.
-/

set_option autoImplicit false


open Googology.Trans.PoR.InaccPsi.R2.Wm Googology.Trans.PoR.InaccPsi.R2.Wh Googology.Trans.PoR.InaccPsi.R2.Ho
open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gf
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd
open Googology.Trans.PoR.InaccPsi.R2.Wo Googology.Trans.PoR.InaccPsi.R2.Wn Googology.Trans.PoR.InaccPsi.R2.Wp
  Googology.Trans.PoR.InaccPsi.R2.Ws Googology.Trans.PoR.InaccPsi.R2.Wt Googology.Trans.PoR.InaccPsi.R2.Wy
  Googology.Trans.PoR.InaccPsi.R2.Wx

open Googology.Trans.PoR.InaccPsi.R2.Xc
open Googology.Trans.PoR.InaccPsi.R2.Xf

open Googology.Trans.PoR.InaccPsi.R2.Xf

namespace Googology.Trans.PoR.InaccPsi.R2.Xl

/-! ## Ordinal facts -/

/-- **`N_α(0) = φ(α+1, 0)`.** -/
theorem xl_N_eq (α : Ordinal.{0}) : hcN α 0 = veblen (α + 1) 0 := by
  refine le_antisymm (hcN_le (veblen_veblen_of_lt (lt_add_one α) 0) veblen_pos) ?_
  obtain ⟨a, ha⟩ := hc_LuP_of_fix (hcN_fix α 0)
  rw [← ha]; exact (isNormal_veblen _).monotone zero_le

theorem xl_one_lt_Ng (α : Ordinal.{0}) : (1 : Ordinal.{0}) < hcN α 0 := by
  have h := (hcN_lim α 0).add_one_lt (hcN_gt α 0); rwa [zero_add] at h

theorem xl_addg_lt {α t : Ordinal.{0}} (ht : t < hcN α 0) : 1 + t < hcN α 0 :=
  (inE_indec (hcN_E α 0)).add_lt (xl_one_lt_Ng α) ht

/-- **`1 + t < φ(α, 1 + t)` below the first fixed point.** -/
theorem xl_jg_lt {α t : Ordinal.{0}} (ht : t < hcN α 0) : 1 + t < veblen α (1 + t) := by
  rcases (right_le_veblen α (1 + t)).lt_or_eq with h | h
  · exact h
  · exfalso
    exact absurd (hcN_le h.symm (zero_lt_one.trans_le le_self_add)) (not_le.2 (xl_addg_lt ht))

theorem xl_Qg_lt_N {α t : Ordinal.{0}} (ht : t < hcN α 0) : veblen α (1 + t) < hcN α 0 := by
  have h := (isNormal_veblen α).strictMono (xl_addg_lt ht)
  rwa [hcN_fix] at h

/-- `e + t < φ(α, e + t)` below the first fixed point (`e` finite). -/
theorem xl_jeg_lt {α t : Ordinal.{0}} (e : ℕ) (ht : t < hcN α 0) : (e : Ordinal.{0}) + t < veblen α (e + t) := by
  have hy : (e : Ordinal.{0}) + t < hcN α 0 :=
    (inE_indec (hcN_E α 0)).add_lt ((natCast_lt_omega0 e).trans (omega0_lt_inE (hcN_E α 0))) ht
  rcases (right_le_veblen α ((e : Ordinal.{0}) + t)).lt_or_eq with h | h
  · exact h
  · exfalso
    have h0 : 0 < (e : Ordinal.{0}) + t := by
      rcases eq_or_ne ((e : Ordinal.{0}) + t) 0 with h0 | h0
      · rw [h0] at h; exact absurd h veblen_pos.ne
      · exact pos_iff_ne_zero.2 h0
    exact absurd (hcN_le h.symm h0) (not_le.2 hy)

theorem xl_addeg_lt {α t : Ordinal.{0}} (e : ℕ) (ht : t < hcN α 0) : (e : Ordinal.{0}) + t < hcN α 0 :=
  (inE_indec (hcN_E α 0)).add_lt ((natCast_lt_omega0 e).trans (omega0_lt_inE (hcN_E α 0))) ht

theorem xl_Qeg_lt_N {α t : Ordinal.{0}} (e : ℕ) (ht : t < hcN α 0) : veblen α (e + t) < hcN α 0 := by
  have h := (isNormal_veblen α).strictMono (xl_addeg_lt e ht)
  rwa [hcN_fix] at h

theorem xl_lt_N_of {α : Ordinal.{0}} : α < hcN α 0 := by
  have h := (isNormal_veblen α).strictMono (hcN_gt α 0)
  rw [hcN_fix] at h
  exact (left_le_veblen α 0).trans_lt h

/-! ## Readings at the level `G` -/


section Read

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem xl_lx : xfLv.l x + 0 = lgG x := by rw [add_zero, xf_l hx hx1]

theorem xl_Gq : lgG x + 1 < gq 1 x :=
  (ev_isSuccLimit_of_inE (gm1_facts hx hx1).2.2.2).add_one_lt (mg_lgG_lt_G1 hx hx1)

/-- `N_{Γ_{x+1}}(0) < Γ_{x+2}`. -/
theorem xl_Nx_lt1 : hcN (xfLv.l x + 0) 0 < gq 1 x := by
  rw [xl_lx hx hx1]; exact he_N_lt1 hx hx1 (xl_Gq hx hx1) (gm1_facts hx hx1).2.2.2.pos

theorem xl_GN : lgG x < hcN (lgG x) 0 := by
  have h := (isNormal_veblen (lgG x)).strictMono (hcN_gt (lgG x) 0)
  rwa [hcN_fix, he_G_sc hx hx1] at h

/-- **`ϑˣ(Ω₁·Γ_{x+1} + t) = φ(Γ_{x+1}, 1 + t)` for every `t < N_{Γ_{x+1}}(0)`.** -/
theorem xl_glA : ∀ t, t < hcN (lgG x) 0 → glA (lgG x) t x = veblen (lgG x) (1 + t) := by
  obtain ⟨hGT, hxG, hG1, -, -⟩ := lgG_facts hx hx1
  have hG1' : (1 : Ordinal.{0}) ≤ lgG x := (xf_one_lt_Gx hx hx1).le
  have hsc := he_G_sc hx hx1
  have hNq : hcN (lgG x) 0 < gq 1 x := by rw [← xl_lx hx hx1]; exact xl_Nx_lt1 hx hx1
  have hpos : ∀ s, lgG x < veblen (lgG x) (1 + s) := fun s => by
    conv_lhs => rw [← hsc]
    exact (isNormal_veblen _).strictMono (zero_lt_one.trans_le le_self_add)
  intro t
  induction t using WellFoundedLT.induction with
  | ind t IH =>
  intro ht
  obtain ⟨htT, ht1⟩ := gm1_T hx hx1 (ht.trans hNq)
  have hF := glA_facts hx hx1 hG1' hGT hG1 htT ht1
  obtain ⟨i, hi⟩ := glA_P hx hx1 hG1' hGT hG1 htT ht1
  have htj : t < veblen (lgG x) (1 + t) := le_add_self.trans_lt (xl_jg_lt ht)
  apply le_antisymm
  · refine glA_min hx hx1 hG1' hGT hG1 htT ht1 ⟨1 + t, rfl⟩ (hxG.trans (hpos t)) htj (hpos t)
      (fun σ hσ => ?_)
    rw [IH σ hσ (hσ.trans ht)]
    exact (isNormal_veblen _).strictMono ((add_lt_add_iff_left 1).2 hσ)
  · rw [← hi]
    apply (isNormal_veblen _).monotone
    refine le_of_forall_lt (fun s hs => ?_)
    have hi0 : 0 < i := by
      rcases eq_or_ne i 0 with h0 | h0
      · exfalso
        have h5 := hF.2.2.2.2.1
        rw [← hi, h0, hsc] at h5
        exact lt_irrefl _ h5
      · exact pos_iff_ne_zero.2 h0
    rcases eq_or_ne s 0 with rfl | hs0
    · exact hi0
    · have h1s : (1 : Ordinal.{0}) ≤ s := one_le_iff_ne_zero.2 hs0
      have hss : 1 + (s - 1) = s := Ordinal.add_sub_cancel_of_le h1s
      have hs' : s - 1 < t := by
        rw [← hss] at hs; exact (add_lt_add_iff_left 1).1 hs
      obtain ⟨hsT, hs1⟩ := gm1_T hx hx1 ((hs'.trans ht).trans hNq)
      have h := glA_lt_of hx hx1 hG1' hGT hG1 hsT htT ht1 hs'
      rw [IH (s - 1) hs' (hs'.trans ht), ← hi] at h
      have h' := (isNormal_veblen (lgG x)).strictMono.lt_iff_lt.1 h
      rwa [hss] at h'

/-- **`ϑˣ(Ω₁·(Γ_{x+1}+1)) = N_{Γ_{x+1}}(0)`.** -/
theorem xl_glA_N : glA (lgG x + 1) 0 x = hcN (lgG x) 0 := by
  obtain ⟨-, hxG, -, -, -⟩ := lgG_facts hx hx1
  obtain ⟨hβT, hβ1⟩ := gm1_T hx hx1 (xl_Gq hx hx1)
  obtain ⟨h0T, h01⟩ := gm1_T hx hx1 (gm1_facts hx hx1).2.2.2.pos
  have hβ : (1 : Ordinal.{0}) ≤ lgG x + 1 := le_add_self
  have hGN := xl_GN hx hx1
  apply le_antisymm
  · exact glA_min hx hx1 hβ hβT hβ1 h0T h01 (hc_LuP_of_fix (hcN_fix _ _)) (hxG.trans hGN) (hcN_gt _ _)
      ((hcN_lim _ _).add_one_lt hGN) (fun σ hσ => absurd hσ (not_lt.2 zero_le))
  · obtain ⟨i, hi⟩ := glA_P hx hx1 hβ hβT hβ1 h0T h01
    rw [← hi, xl_N_eq]; exact (isNormal_veblen _).monotone zero_le

/-- **`ϑˣ(Ω₁·Γ_{x+1} + r) < N_{Γ_{x+1}}(0)`** for `r < N_{Γ_{x+1}}(0)`. -/
theorem xl_glA_lt_N {r : Ordinal.{0}} (hr : r < hcN (xfLv.l x + 0) 0) :
    glA (xfLv.l x + 0) r x < hcN (xfLv.l x + 0) 0 := by
  rw [xl_lx hx hx1] at hr ⊢; rw [xl_glA hx hx1 r hr]; exact xl_Qg_lt_N hr

theorem xl_glA_eq {r : Ordinal.{0}} (hr : r < hcN (xfLv.l x + 0) 0) :
    glA (xfLv.l x + 0) r x = veblen (xfLv.l x + 0) (1 + r) := by
  rw [xl_lx hx hx1] at hr ⊢; exact xl_glA hx hx1 r hr

end Read

/-- **Lemma EXACT for `N_{Γ_{ρ+1}}(0) = φ(Γ_{ρ+1}+1, 0)`.** -/
theorem xl_N_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) :
    hcN (xfLv.l ρ + 0) 0 ∈ TB ρ σ ∧ pi σ ρ (hcN (xfLv.l ρ + 0) 0) = hcN (xfLv.l σ + 0) 0 := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have h1σ : (1 : Ordinal.{0}) < σ := wo_one_lt_inE hB.1
  have h := hnv_glA_pi xfLv (ν := 1) hB (by rw [xfLv_g]; exact h1σ) h1σ (mem_TB_of_lt hB (zero_lt_one.trans h1σ))
    (gm1_facts hB.2.1 hρ1).2.2.2.pos
  rw [pi_lt hB (zero_lt_one.trans h1σ), xf_l hB.2.1 hρ1, xf_l hB.1 hσ1, xl_glA_N hB.2.1 hρ1,
    xl_glA_N hB.1 hσ1] at h
  rw [xl_lx hB.2.1 hρ1, xl_lx hB.1 hσ1]; exact h


/-! ## The bottom base -/

/-- **A BOTTOM BASE OF THE LEVEL `L + κ`**: the offsets start at `0`, the offset `λ` gives `φ(L + κ, e + λ)`. -/
structure XlB (Λ : HnLv) (κ : Ordinal.{0}) where
  e : ℕ
  γN : Ordinal.{0}
  Zo : Ordinal.{0} → Ordinal.{0}
  lv : κ < Om1
  lvN : κ ≤ γN
  lg : Λ.g ≤ γN
  γN_lt : γN < Om1
  G_lt : gcG 0 < veblen (Λ.L + κ) e
  N_lt1 : hcN (Λ.L + κ) 0 < gcG 1
  N_mem : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → γN < b → hcN (Λ.L + κ) 0 ∈ S.CSet a b
  N_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z {gcG 0} (hcN (Λ.L + κ) 0) → γN < Z
  γN_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → κ < Z → Λ.g < Z → γN < Z
  Zo_fix : ∀ x, veblen 2 (Zo x) = Zo x
  Zo_G1 : ∀ x, InE x → x < Om1 → Zo x < gq 1 x
  read : ∀ {x}, InE x → x < Om1 → γN < x → ∀ t, t < hcN (Λ.l x + κ) 0 →
    glA (Λ.l x + κ) t x = veblen (Λ.l x + κ) (e + t)
  N_pi : ∀ {σ ρ}, Bases σ ρ → γN < σ →
    hcN (Λ.l ρ + κ) 0 ∈ TB ρ σ ∧ pi σ ρ (hcN (Λ.l ρ + κ) 0) = hcN (Λ.l σ + κ) 0

namespace XlB

variable {Λ : HnLv} {κ : Ordinal.{0}} (A : XlB Λ κ)

open Classical in
/-- **The low field**: `N_{ℓ(x)+κ}(0)` above `γN`, `Z_o(x)` at or below it. -/
noncomputable def Zl (x : Ordinal.{0}) : Ordinal.{0} :=
  if A.γN < x then hcN (Λ.l (max ω x) + κ) 0 else A.Zo x

theorem Zl_eq {x : Ordinal.{0}} (hx : InE x) (h : A.γN < x) : A.Zl x = hcN (Λ.l x + κ) 0 := by
  unfold XlB.Zl; rw [if_pos h, max_eq_right (omega0_lt_inE hx).le]

theorem Zl_low {x : Ordinal.{0}} (h : ¬ A.γN < x) : A.Zl x = A.Zo x := by unfold XlB.Zl; rw [if_neg h]

theorem Zl_fix (x : Ordinal.{0}) : veblen 2 (A.Zl x) = A.Zl x := by
  unfold XlB.Zl; split_ifs
  · exact hc_fix_down ((show (2 : Ordinal.{0}) ≤ ω from (by exact_mod_cast (natCast_lt_omega0 2).le)).trans
      (((le_max_left ω x).trans (Λ.l_ge _)).trans le_self_add)) (hcN_fix _ _)
  · exact A.Zo_fix x

theorem γ_lt : A.γN < Om1 := A.γN_lt

include A in
theorem N_E : InE (hcN (Λ.L + κ) 0) := hcN_E _ _

include A in
theorem N_lim : IsSuccLimit (hcN (Λ.L + κ) 0) := hcN_lim _ _

include A in
theorem zero_lt_N : (0 : Ordinal.{0}) < hcN (Λ.L + κ) 0 := (hcN_E _ _).pos

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : A.γN < x)
include hx hx1 hγ

theorem ν_lt : κ < x := A.lvN.trans_lt hγ

theorem N_lt1x : hcN (Λ.l x + κ) 0 < gq 1 x :=
  he_N_lt1 hx hx1 ((ev_isSuccLimit_of_inE (gm1_facts hx hx1).2.2.2).add_one_lt (hnv_q Λ hx hx1 (A.ν_lt hx hx1 hγ)))
    (gm1_facts hx hx1).2.2.2.pos

theorem Zl_G1x : A.Zl x < gq 1 x := by rw [A.Zl_eq hx hγ]; exact A.N_lt1x hx hx1 hγ

theorem t1_lt1 {r : Ordinal.{0}} (hr : r < hcN (Λ.l x + κ) 0) : r + 1 < gq 1 x :=
  ((hcN_lim _ _).add_one_lt hr).trans (A.N_lt1x hx hx1 hγ)

theorem t_lt1 {r : Ordinal.{0}} (hr : r < hcN (Λ.l x + κ) 0) : r < gq 1 x :=
  (lt_add_one _).trans (A.t1_lt1 hx hx1 hγ hr)

/-- **`ϑˣ(Ω₁·(ℓ(x)+κ) + r) < N_{ℓ(x)+κ}(0)`** for `r < N_{ℓ(x)+κ}(0)`. -/
theorem glA_lt_N {r : Ordinal.{0}} (hr : r < hcN (Λ.l x + κ) 0) : glA (Λ.l x + κ) r x < hcN (Λ.l x + κ) 0 := by
  rw [A.read hx hx1 hγ r hr]; exact xl_Qeg_lt_N A.e hr

theorem x_lt_N : x < hcN (Λ.l x + κ) 0 := (hnv_xl Λ hx hx1).trans_lt xl_lt_N_of

end Base

theorem Zl_G1 (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : A.Zl x < gq 1 x := by
  by_cases h : A.γN < x
  · exact A.Zl_G1x hx hx1 h
  · rw [A.Zl_low h]; exact A.Zo_G1 x hx hx1

section Lvl

variable {l : Ordinal.{0}} (hl : l < hcN (Λ.L + κ) 0)
include hl

theorem j_lt : (A.e : Ordinal.{0}) + l < veblen (Λ.L + κ) (A.e + l) := xl_jeg_lt A.e hl

theorem add_lt_N : (A.e : Ordinal.{0}) + l < hcN (Λ.L + κ) 0 := xl_addeg_lt A.e hl

theorem j1_lt : (A.e : Ordinal.{0}) + l + 1 < veblen (Λ.L + κ) (A.e + l + 1) := by
  have h := xl_jeg_lt (α := Λ.L + κ) A.e (A.N_lim.add_one_lt hl)
  rwa [← add_assoc] at h

theorem lt_Q : l < veblen (Λ.L + κ) (A.e + l) := le_add_self.trans_lt (A.j_lt hl)

theorem Q_lt_N : veblen (Λ.L + κ) (A.e + l) < hcN (Λ.L + κ) 0 := xl_Qeg_lt_N A.e hl

theorem Q1_lt_N : veblen (Λ.L + κ) (A.e + l + 1) < hcN (Λ.L + κ) 0 := by
  have h := xl_Qeg_lt_N (α := Λ.L + κ) A.e (A.N_lim.add_one_lt hl)
  rwa [← add_assoc] at h

end Lvl

theorem G_lt_Q (l : Ordinal.{0}) : gcG 0 < veblen (Λ.L + κ) (A.e + l) :=
  A.G_lt.trans_le ((isNormal_veblen _).monotone le_self_add)

theorem Q_lt_Q {μ l : Ordinal.{0}} (h : μ < l) :
    veblen (Λ.L + κ) (A.e + μ) < veblen (Λ.L + κ) (A.e + l) :=
  (isNormal_veblen _).strictMono ((add_lt_add_iff_left _).2 h)

theorem cover {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlN : l < hcN (Λ.L + κ) 0) :
    ∃ μ, μ < l ∧ l < veblen (Λ.L + κ) (A.e + μ) := by
  have h := A.lt_Q hlN
  obtain ⟨t, ht, hlt⟩ := ((isNormal_veblen _).lt_iff_exists_lt (isSuccLimit_add _ hl)).1 h
  obtain ⟨d, hf, htd⟩ := (lt_add_iff hl.bot_lt.ne').1 ht
  exact ⟨d, hf, hlt.trans_le ((isNormal_veblen _).monotone htd)⟩

include A in
theorem G_lt_N : gcG 0 < hcN (Λ.L + κ) 0 := (A.G_lt_Q 0).trans (A.Q_lt_N A.zero_lt_N)

/-- **THE GATE OF AN OFFSET**: `e + λ` a code over `Z` (with `κ, Λ.g < Z`) ⇒ `max(γN, g_E(λ)) < Z`. -/
theorem gate_of_jN (E : HgVD) {Z l : Ordinal.{0}} (hlB : l < E.B) (hZ : SC Z) (hZ1 : Z ≤ Om 1)
    (h : GxCl Z {gcG 0} ((A.e : Ordinal.{0}) + l)) (hνZ : κ < Z) (hgZ : Λ.g < Z) : max A.γN (E.g l) < Z := by
  have hl : GxCl Z {gcG 0} l := by
    rcases lt_or_ge l ω with hlω | hlω
    · exact GxCl.small (hlω.trans (omega0_lt_inE (Low.opow_eq_self_of_SC hZ)))
    · rwa [natCast_add_of_omega0_le hlω] at h
  have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1
  refine max_lt (A.γN_cl Z hZ hZ1 hνZ hgZ) ?_
  exact E.code_gate Z hZ1' hZ.1 (fun _ _ hu hv => hZ.isPrincipal hu hv) (fun _ _ hu hv => hZ.2 _ hu _ hv)
    {gcG 0} (fun s hs => Or.inl (Set.mem_singleton_iff.1 hs)) l hl hlB

theorem lvR_lt_N (E : HgVD) (hZ : ∀ x, InE x → x < Om1 → E.Z x ≤ A.Zl x) {c x : Ordinal.{0}} (hc : c < E.B)
    (hx : InE x) (hx1 : x < Om1) (hγ : A.γN < x) (hg : E.g c < x) : E.R c x < hcN (Λ.l x + κ) 0 := by
  have h := (E.R_lt_Z x hx hx1 c hc hg).trans_le (hZ x hx hx1)
  rwa [A.Zl_eq hx hγ] at h

theorem lvt_lt (E : HgVD) (hZ : ∀ x, InE x → x < Om1 → E.Z x ≤ A.Zl x) {c x : Ordinal.{0}} (hc : c < E.B)
    (hx : InE x) (hx1 : x < Om1) (hγ : A.γN < x) (hg : E.g c < x) : E.R c x < gq 1 x :=
  A.t_lt1 hx hx1 hγ (A.lvR_lt_N E hZ hc hx hx1 hγ hg)

end XlB

/-- **`ϑˣ(Ω₁·(α+1)) = N_α(0)`** at every level `α ∈ [1, Γ_{x+2})` that is not a successor of a fixed point. -/
theorem xl_glA_Ng {x α : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hα : α + 1 < gq 1 x) (hxα : x ≤ α) :
    glA (α + 1) 0 x = hcN α 0 := by
  obtain ⟨hβT, hβ1⟩ := gm1_T hx hx1 hα
  obtain ⟨h0T, h01⟩ := gm1_T hx hx1 (gm1_facts hx hx1).2.2.2.pos
  have hβ : (1 : Ordinal.{0}) ≤ α + 1 := le_add_self
  have hαN : α < hcN α 0 := xl_lt_N_of
  apply le_antisymm
  · exact glA_min hx hx1 hβ hβT hβ1 h0T h01 (hc_LuP_of_fix (hcN_fix _ _)) (hxα.trans_lt hαN) (hcN_gt _ _)
      ((hcN_lim _ _).add_one_lt hαN) (fun σ hσ => absurd hσ (not_lt.2 zero_le))
  · obtain ⟨i, hi⟩ := glA_P hx hx1 hβ hβT hβ1 h0T h01
    rw [← hi, xl_N_eq]; exact (isNormal_veblen _).monotone zero_le

/-- **Lemma EXACT for `N_{ℓ(ρ)+κ}(0) = φ(ℓ(ρ)+κ+1, 0)`** at every level datum (bases above `Λ.g` and `κ`). -/
theorem xl_N_pi_gen (Λ : HnLv) {κ σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hg : Λ.g < σ) (hκ : κ < σ) :
    hcN (Λ.l ρ + κ) 0 ∈ TB ρ σ ∧ pi σ ρ (hcN (Λ.l ρ + κ) 0) = hcN (Λ.l σ + κ) 0 := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hκ1 : κ + 1 < σ := (ev_isSuccLimit_of_inE hB.1).add_one_lt hκ
  have h0σ : (0 : Ordinal.{0}) < σ := hB.1.pos
  have h := hnv_glA_pi Λ (ν := κ + 1) hB hg hκ1 (mem_TB_of_lt hB h0σ) (gm1_facts hB.2.1 hρ1).2.2.2.pos
  have hq : ∀ {y}, InE y → y < Om1 → κ + 1 < y → Λ.l y + κ + 1 < gq 1 y := fun hy hy1 hk => by
    rw [add_assoc]; exact hnv_q Λ hy hy1 hk
  rw [pi_lt hB h0σ, ← add_assoc, ← add_assoc,
    xl_glA_Ng hB.2.1 hρ1 (hq hB.2.1 hρ1 (hκ1.trans hB.2.2.1)) ((Λ.l_ge ρ).trans le_self_add),
    xl_glA_Ng hB.1 hσ1 (hq hB.1 hσ1 hκ1) ((Λ.l_ge σ).trans le_self_add)] at h
  exact h

/-! ## The offset pseudo-base -/

section Off

variable {Λ : HnLv} {κ : Ordinal.{0}} (A : XlB Λ κ) (E : HgVD) (l : Ordinal.{0}) (hlB : l < E.B)
  (hlN : l < hcN (Λ.L + κ) 0) (hZ : ∀ x, InE x → x < Om1 → E.Z x ≤ A.Zl x)

include hlB hZ in
theorem xlOff_R_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : max A.γN (E.g l) < x) :
    E.R l x < hcN (Λ.l x + κ) 0 :=
  A.lvR_lt_N E hZ hlB hx hx1 (max_lt_iff.1 hγ).1 (max_lt_iff.1 hγ).2

include hlB hlN hZ in
/-- **THE OFFSET PSEUDO-BASE OF THE LEVEL `L + κ`**: the offset `λ < N` read by `E` gives the pseudo-base
`φ(L + κ, e + λ)`, reading `ϑˣ(Ω₁·(ℓ(x)+κ) + λ_E(x))` (`= φ(ℓ(x)+κ, e + λ_E(x))`), gate `max(γN, g_E(λ))`, low
field `Zl`. -/
noncomputable def xlOff : HnVQ Λ κ where
  F := veblen (Λ.L + κ) (A.e + l)
  Fr := fun x => glA (Λ.l x + κ) (E.R l x) x
  γ := max A.γN (E.g l)
  Zo := A.Zl
  lv := A.lv
  γ_ge := A.lvN.trans (le_max_left _ _)
  lg := A.lg.trans (le_max_left _ _)
  γ_lt := max_lt A.γN_lt (E.g_lt l hlB)
  F_P := ⟨_, rfl⟩
  G_lt := A.G_lt_Q l
  S_lt1 := by rw [hdNx_veb]; exact (A.Q1_lt_N hlN).trans A.N_lt1
  F_mem := fun S _ _ ha hb => CSet.phi_mem (hnv_L_mem Λ S ha ((A.lg.trans (le_max_left _ _)).trans_lt hb)
      ((A.lvN.trans (le_max_left _ _)).trans_lt hb))
    (CSet.add_mem (gr_cst_mem ha _ _ ((natCast_lt_omega0 A.e).trans (omega0_lt_gamma 1)))
      (E.mem S _ _ ha l hlB ((le_max_right _ _).trans_lt hb)).1)
  S_mem := fun S _ _ ha hb => by
    rw [hdNx_veb]
    exact CSet.phi_mem (hnv_L_mem Λ S ha ((A.lg.trans (le_max_left _ _)).trans_lt hb)
      ((A.lvN.trans (le_max_left _ _)).trans_lt hb)) (CSet.succ_mem
      (CSet.add_mem (gr_cst_mem ha _ _ ((natCast_lt_omega0 A.e).trans (omega0_lt_gamma 1)))
        (E.mem S _ _ ha l hlB ((le_max_right _ _).trans_lt hb)).1))
  F_code := fun Z _ hZ1 _ hy hQy hyZ => by
    rw [hdNx_veb] at hyZ
    exact GxCl.phi (hi_cl_lvl (hnv_L1 Λ κ) hZ1 (A.j_lt hlN) (A.G_lt_Q l) hy hQy hyZ)
      (hd_cl_lev (hnv_L1 Λ κ) hZ1 (A.j_lt hlN) (A.G_lt_Q l) hy hQy hyZ)
  F_cl := fun Z hZ hZ1 _ hy hQy hyZ => by
    rw [hdNx_veb] at hyZ
    exact A.gate_of_jN E hlB hZ hZ1 (hd_cl_lev (hnv_L1 Λ κ) hZ1 (A.j_lt hlN) (A.G_lt_Q l) hy hQy hyZ)
      (hnv_cl_gate Λ A.lv hZ hZ1 (A.j_lt hlN) (A.G_lt_Q l) hy hQy hyZ)
      (hnv_cl_g Λ A.lv hZ hZ1 (A.j_lt hlN) (A.G_lt_Q l) hy hQy hyZ)
  S_cl := fun Z hZ hZ1 h => by
    rw [hdNx_veb] at h
    have hG1 : gcG 0 < veblen (Λ.L + κ) (A.e + l + 1) := by
      have := A.G_lt_Q (l + 1); rwa [← add_assoc] at this
    have h1 := hd_cl_lev (hnv_L1 Λ κ) hZ1 (A.j1_lt hlN) hG1 h le_rfl
      ((isNormal_veblen (Λ.L + κ)).strictMono (lt_add_one _))
    have h2 := ha_cl_succ hZ.1 (fun s hs => by rw [Set.mem_singleton_iff.1 hs]; exact ev_isSuccLimit_of_inE gr_G_inE)
      h1 _ rfl
    exact A.gate_of_jN E hlB hZ hZ1 h2 (hnv_cl_gate Λ A.lv hZ hZ1 (A.j1_lt hlN) hG1 h
      le_rfl ((isNormal_veblen (Λ.L + κ)).strictMono (lt_add_one _)))
      (hnv_cl_g Λ A.lv hZ hZ1 (A.j1_lt hlN) hG1 h le_rfl ((isNormal_veblen (Λ.L + κ)).strictMono (lt_add_one _)))
  Fr_gt := fun hx hx1 hγ => (hnv_glA_facts Λ hx hx1 (A.ν_lt hx hx1 (max_lt_iff.1 hγ).1)
    (A.t_lt1 hx hx1 (max_lt_iff.1 hγ).1 (xlOff_R_lt A E l hlB hZ hx hx1 hγ))).1
  Fr_P := fun hx hx1 hγ => hnv_glA_P Λ hx hx1 (A.ν_lt hx hx1 (max_lt_iff.1 hγ).1)
    (A.t_lt1 hx hx1 (max_lt_iff.1 hγ).1 (xlOff_R_lt A E l hlB hZ hx hx1 hγ))
  S_Zo := fun {x} hx hx1 hγ => by
    have hA := (max_lt_iff.1 hγ).1
    have hR1 : E.R l x + 1 < hcN (Λ.l x + κ) 0 := (hcN_lim _ _).add_one_lt (xlOff_R_lt A E l hlB hZ hx hx1 hγ)
    show hdNx (Λ.l x + κ) (glA (Λ.l x + κ) (E.R l x) x) < A.Zl x
    rw [← hnv_glA_succ Λ hx hx1 (A.ν_lt hx hx1 hA) (A.t1_lt1 hx hx1 hA (xlOff_R_lt A E l hlB hZ hx hx1 hγ)),
      A.Zl_eq hx hA]
    exact A.glA_lt_N hx hx1 hA hR1
  Zo_fix := A.Zl_fix
  Zo_G1 := fun x hx hx1 => A.Zl_G1 x hx hx1
  Fr_pi := fun {σ ρ} hB hγ => by
    have hγρ : max A.γN (E.g l) < ρ := hγ.trans hB.2.2.1
    obtain ⟨e1, e2⟩ := E.ex σ ρ hB l hlB (max_lt_iff.1 hγ).2
    have h := hnv_glA_pi Λ hB (A.lg.trans_lt (max_lt_iff.1 hγ).1) (A.lvN.trans_lt (max_lt_iff.1 hγ).1) e1
      (A.t_lt1 hB.2.1 hB.2.2.2 (max_lt_iff.1 hγρ).1 (xlOff_R_lt A E l hlB hZ hB.2.1 hB.2.2.2 hγρ))
    rw [e2] at h; exact h
  S_pi := fun {σ ρ} hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hγρ : max A.γN (E.g l) < ρ := hγ.trans hB.2.2.1
    have h1σ : (1 : Ordinal.{0}) < σ := wo_one_lt_inE hB.1
    obtain ⟨e1, e2⟩ := E.ex σ ρ hB l hlB (max_lt_iff.1 hγ).2
    obtain ⟨u1, u2⟩ := pi_add hB e1 (mem_TB_of_lt hB h1σ)
    rw [e2, pi_lt hB h1σ] at u2
    have hAρ := (max_lt_iff.1 hγρ).1
    have hAσ := (max_lt_iff.1 hγ).1
    have h := hnv_glA_pi Λ hB (A.lg.trans_lt hAσ) (A.lvN.trans_lt hAσ) u1
      (A.t1_lt1 hB.2.1 hρ1 hAρ (xlOff_R_lt A E l hlB hZ hB.2.1 hρ1 hγρ))
    rw [u2, hnv_glA_succ Λ hB.2.1 hρ1 (A.ν_lt hB.2.1 hρ1 hAρ)
      (A.t1_lt1 hB.2.1 hρ1 hAρ (xlOff_R_lt A E l hlB hZ hB.2.1 hρ1 hγρ)),
      hnv_glA_succ Λ hB.1 hσ1 (A.ν_lt hB.1 hσ1 hAσ) (A.t1_lt1 hB.1 hσ1 hAσ (xlOff_R_lt A E l hlB hZ hB.1 hσ1 hγ))] at h
    exact h

theorem xlOff_F : (xlOff A E l hlB hlN hZ).F = veblen (Λ.L + κ) (A.e + l) := rfl

theorem xlOff_Fr (x : Ordinal.{0}) : (xlOff A E l hlB hlN hZ).Fr x = glA (Λ.l x + κ) (E.R l x) x := rfl

theorem xlOff_γ : (xlOff A E l hlB hlN hZ).γ = max A.γN (E.g l) := rfl

end Off

/-- The stage at the offset `λ`, `λ` read by `E`. -/
noncomputable abbrev xlMPB {Λ : HnLv} {κ : Ordinal.{0}} (A : XlB Λ κ) (E : HgVD) (l : Ordinal.{0}) (hlB : l < E.B)
    (hlN : l < hcN (Λ.L + κ) 0) (hZ : ∀ x, InE x → x < Om1 → E.Z x ≤ A.Zl x) : HgPB :=
  hnVPB (xlOff A E l hlB hlN hZ)

end Googology.Trans.PoR.InaccPsi.R2.Xl
