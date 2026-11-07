import Googology.Trans.PoR.InaccPsi.R2.QdB2

/-!
# QdFxC: EVERY CODE BELOW THE FIXED POINT `E = Hᵛ_λ(y)` IN `[B₂, B₃)` READS BELOW IT

As `Qc.qs_fx_lt` with the Veblen levels.  A code `c < B₂` reads below `ϑˣ(Ω₁·ε_{Ω₁+1})` (`Qd.qd_low_lt`), and that is
at most the reading of `E` (`qd_fx_B2`): from `λ ≥ E₂` the level reading is at least `E₂(x) = ε_{Ω₁+1}`; below `E₂`
either `B₂` is a fixed point of `Hᵛ_λ` below `y` (read below `K(x)`) or a leaf `d ≥ B₂` of `λ` reads at most the data
of `λ(x)` (`Qd.qdLv_dat_ge`), and `B₂` reads at most the reading of `d`.  From `B₂` on as `Qc.qs_fx_lt`: a smaller
fixed point `e = Hᵛ_μ(z) < E` of `Γ` reads `ϑˣ(Ω₁·(Ω₁+μ(x)) + K_e(x))` below `ϑˣ(Ω₁·(Ω₁+λ(x)) + K(x))` by the levels:
`μ < λ` (`Qd.qdLv_main`), `μ = λ` (`z < y`, `qd_fx_Kmono`), `μ > λ` (`e` a fixed point of `Hᵛ_λ` below `y`, or below
a leaf of `λ`, `Qd.qd_comp_lt`).

* `qd_fix_lev_u` (the level and index readings of a fixed point `e ∈ [B₂, B₃)` of `Γ`, with the data bound);
* `qd_fx_eps`, `qd_fx_Kmono`, `qd_fx_B2` (**`ϑˣ(Ω₁·ε_{Ω₁+1})` is at most the reading of `E`**), `qd_fx_lt` (**every
  code below `E` reads below `qdA E x`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yw
  Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Va Googology.Trans.PoR.InaccPsi.R2.Tl
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Yr
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Zm Googology.Trans.PoR.InaccPsi.R2.Tf
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Xk Googology.Trans.PoR.InaccPsi.R2.Gm
  Googology.Trans.PoR.InaccPsi.R2.Qc

variable (S : InaccSeq.{0})

include S in
/-- **The level and index readings of a fixed point `e ∈ [B₂, B₃)` of `Γ`** with the data bound
`tfDat(Ω₁ + μ(x)) ≤ max_{d leaf} d(x)`. -/
theorem qd_fix_lev_u {e x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hA : YhAt e) (hi : ¬ yhJ e < e)
    (hX : ucB ≤ e) (hB : e < qdB) (hgx : max ω (qdQEt e) < x)
    (hcode : ∀ c, c < e → qdGt c < x → vD c x ∈ Tset x ∧ vD c x < Om1)
    (hmono : ∀ b c, b < c → c < e → qdGt b < x → qdGt c < x → vD b x < vD c x) :
    (∀ d ∈ qdComps (qdLev e), d < e ∧ qdGt d < x) ∧ 1 ≤ qdLvx e (qdLev e) x ∧
      Om1 + qdLvx e (qdLev e) x < ggGam ∧ tfDat (Om1 + qdLvx e (qdLev e) x) ∈ Tset x ∧
      tfDat (Om1 + qdLvx e (qdLev e) x) ≤ qdFold (fun d => if d < e then vD d x else 0) (qdLev e) ∧
      qdRK (qdLev e) (qdI (qdLev e) e) x ∈ Tset x ∧ qdRK (qdLev e) (qdI (qdLev e) e) x < Om1 := by
  obtain ⟨hL1, hNG, hNT, hKT, hK1⟩ := qd_fix_lev S hx hx1 hA hi hX hB hgx hcode hmono
  obtain ⟨-, hlG, hlc, -, -, -⟩ := qd_fix_data S hA hi hX hB
  obtain ⟨hgcomp, -, -⟩ := qd_fix_gates S hA hi hX hB
  have he0 : (0 : Ordinal.{0}) < e := (show InE e from Low.opow_eq_self_of_SC hA.1).pos
  have hcomp : ∀ d ∈ qdComps (qdLev e), d < e ∧ qdGt d < x := fun d hd =>
    ⟨(qdFold_lt_iff he0 _).1 hlc d hd, (hgcomp d hd).trans_lt hgx⟩
  set f : Ordinal.{0} → Ordinal.{0} := fun d => if d < e then vD d x else 0 with hfdef
  have hf0 : f 0 = 0 := by simp only [hfdef, if_pos he0, vD_zero]
  have hD0 : (fun d => d < e ∧ qdGt d < x) 0 := ⟨he0, by rw [qdGt_zero]; exact hx.pos⟩
  have hfΩ : ∀ d, (fun d => d < e ∧ qdGt d < x) d → f d < Om1 := fun d hd => by
    simp only [hfdef, if_pos hd.1]; exact (hcode d hd.1 hd.2).2
  have hfm : ∀ d d', (fun d => d < e ∧ qdGt d < x) d → (fun d => d < e ∧ qdGt d < x) d' → d < d' →
      f d < f d' := fun d d' hd hd' hdd => by
    simp only [hfdef, if_pos hd.1, if_pos hd'.1]; exact hmono d d' hdd hd'.1 hd.2 hd'.2
  obtain ⟨hLG, hLdat, -, -, -, -⟩ := qdLv_main f (fun d => d < e ∧ qdGt d < x) hf0 hD0 hfΩ hfm _ hlG hcomp
  have hlx : qdLvx e (qdLev e) x = qdLv f (qdLev e) := rfl
  have hdatle : tfDat (Om1 + qdLvx e (qdLev e) x) ≤ qdFold f (qdLev e) := by
    rw [hlx, tfDat_eq_ss _ (tf_Om1_add_lt_gg hLG), qd_ssDat_Om1_add (hlx ▸ hL1) hLG]
    exact hLdat
  exact ⟨hcomp, hL1, hNG, hNT, hdatle, hKT, hK1⟩

section Fix

variable {E : Ordinal.{0}} (hE : InE E) (hBE : tfBG < E) (hEB : E < qdB) (hXE : ucB ≤ E)
  (hlim : ∀ e, InE e → e < E → eN e < E) (hIH : ∀ e, InE e → tfBG ≤ e → e < E → QdGood e)
  (hA : YhAt E) (hi : ¬ yhJ E < E)
  {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)

include hE hEB hIH hx hx1 in
/-- **The readings of the `ε`-number codes below `E` are `ε`-numbers.** -/
theorem qd_fx_eps {e' : Ordinal.{0}} (he' : InE e') (hBe' : tfBG ≤ e') (he'E : e' < E) (hg : qdGt e' < x) :
    InE (vD e' x) := by
  have hωx : ω < x := omega0_lt_inE hx
  have hGe : gcG 0 ≤ e' := va_G_le_BG.trans hBe'
  have he'B : e' < qdB := he'E.trans hEB
  obtain ⟨M, -, hEg, hV, -⟩ := hIH e' he' hBe' he'E
  have hgM : M.Eg < x := by rw [hEg]; exact max_lt hωx (by rw [← qdGt_base' he' hGe he'B]; exact hg)
  have h := (M.V_T x hx hx1 hgM).2.1
  rwa [hV x hx hx1 hgM, ← vD_base' he' hGe he'B] at h

include S hE hBE hEB hXE hlim hIH hA hi hx hx1

/-- **The index readings of `Hᵛ_λ` are ordered** below `E = Hᵛ_λ(y)`: `qdRK λ z x < qdRK λ y x` for `z < y`, `z` not a
fixed point of `Hᵛ_λ`, the parts of `z` with gates below `x`. -/
theorem qd_fx_Kmono (hgx : max ω (qdQEt E) < x) {z : Ordinal.{0}} (hzy : z < qdI (qdLev E) E)
    (hzr : qdH (qdLev E) z ≠ z)
    (hgf : QdFixH (qdLev E) z → qdGt (qdFpH (qdLev E) z) < x ∧ qdGt (z - (qdFpH (qdLev E) z + 1)) < x)
    (hg0 : ¬ QdFixH (qdLev E) z → qdGt z < x) :
    qdRK (qdLev E) z x < qdRK (qdLev E) (qdI (qdLev E) E) x := by
  obtain ⟨-, hl0, -, -, hyE, -, hne, -⟩ := qd_fx_dat S hEB hXE hA hi
  obtain ⟨-, hgF, hg0y⟩ := qd_fix_gates S hA hi hXE hEB
  have hmono : ∀ b c, b < c → c < E → qdGt b < x → qdGt c < x → vD b x < vD c x := fun b c hbc hc hgb hgc =>
    qd_mono S hE hBE hEB hlim hIH hx hx1 hbc hc hgb hgc
  unfold qdRK
  by_cases hFy : QdFixH (qdLev E) (qdI (qdLev E) E)
  · obtain ⟨hffy, hOfy, hfyy⟩ := qd_fpH_mem hne hFy
    obtain ⟨hgfy', hgoy'⟩ := hgF hFy
    have hgfy := hgfy'.trans_lt hgx
    have hgoy := hgoy'.trans_lt hgx
    rw [if_pos hFy]
    have hle_y : ∀ f', qdH (qdLev E) f' = f' → f' < qdI (qdLev E) E →
        f' ≤ qdFpH (qdLev E) (qdI (qdLev E) E) :=
      fun f' h1 h2 => le_csSup ⟨_, fun _ h => h.2.le⟩ ⟨h1, h2⟩
    have hzp : ¬ qdFpH (qdLev E) (qdI (qdLev E) E) < z → z < qdFpH (qdLev E) (qdI (qdLev E) E) := fun h => by
      rcases (not_lt.1 h).lt_or_eq with h' | h'
      · exact h'
      · exact absurd (h' ▸ hffy) hzr
    by_cases hFz : QdFixH (qdLev E) z
    · obtain ⟨hffz, -, hfzz⟩ := qd_fpH_mem hzr hFz
      obtain ⟨hgfz, hgoz⟩ := hgf hFz
      rw [if_pos hFz]
      have hfle := hle_y _ hffz (hfzz.trans hzy)
      rcases hfle.lt_or_eq with hflt | hfeq
      · have hzfy : z < qdFpH (qdLev E) (qdI (qdLev E) E) := hzp fun h => by
          have := (show qdFpH (qdLev E) (qdI (qdLev E) E) ≤ qdFpH (qdLev E) z from
            le_csSup ⟨_, fun _ h => h.2.le⟩ ⟨hffy, h⟩)
          exact absurd this (not_le.2 hflt)
        have hSC : SC (qdFpH (qdLev E) (qdI (qdLev E) E)) := by rw [← hffy]; exact qdH_SC _ _
        have hfyE : InE (vD (qdFpH (qdLev E) (qdI (qdLev E) E)) x) :=
          qd_fx_eps hE hEB hIH hx hx1 (Low.opow_eq_self_of_SC hSC)
            (tfBG_le (qd_P_gamma S hl0 hffy) hOfy) (hfyy.trans hyE) hgfy
        exact ((inE_indec hfyE).add_lt (hmono _ _ hflt (hfyy.trans hyE) hgfz hgfy)
          (hmono _ _ ((Ordinal.sub_le_self _ _).trans_lt hzfy) (hfyy.trans hyE) hgoz hgfy)).trans_le le_self_add
      · rw [hfeq] at hgoz ⊢
        have hfz' : qdFpH (qdLev E) (qdI (qdLev E) E) < z := by rw [← hfeq]; exact hfzz
        exact (add_lt_add_iff_left _).2 (hmono _ _ (vs_sub_lt (Order.add_one_le_of_lt hfz') hzy)
          ((Ordinal.sub_le_self _ _).trans_lt hyE) hgoz hgoy)
    · rw [if_neg hFz]
      have hzfy : z < qdFpH (qdLev E) (qdI (qdLev E) E) := hzp fun h => hFz ⟨_, hffy, h⟩
      exact (hmono _ _ hzfy (hfyy.trans hyE) (hg0 hFz) hgfy).trans_le le_self_add
  · have hFz : ¬ QdFixH (qdLev E) z := fun ⟨f, h1, h2⟩ => hFy ⟨f, h1, h2.trans hzy⟩
    rw [if_neg hFy, if_neg hFz]
    exact hmono _ _ hzy hyE (hg0 hFz) ((hg0y hFy).trans_lt hgx)

/-- **`ϑˣ(Ω₁·ε_{Ω₁+1})`, the reading of `B₂`, is at most the reading of `E`.** -/
theorem qd_fx_B2 (hI : QdImgH) (hgx : max ω (qdQEt E) < x) : vt x (Om1 * ggE) ≤ qdA E x := by
  have hωx : ω < x := omega0_lt_inE hx
  obtain ⟨-, hl0, hlG, hlc, hyE, hFy, hne, -⟩ := qd_fx_dat S hEB hXE hA hi
  obtain ⟨hVeq, -, -, -, hxV, -, -⟩ := qd_fx_V S hE hBE hEB hXE hlim hIH hA hi hx hx1 hI hgx
  obtain ⟨hcomp, hL1, hNG, hNT, hKT, hK1, -⟩ := qd_fx_parts S hE hBE hEB hXE hlim hIH hA hi hx hx1 hgx
  obtain ⟨-, hgF, -⟩ := qd_fix_gates S hA hi hXE hEB
  have hO1N : Om1 ≤ Om1 + qdLvx E (qdLev E) x := le_self_add
  obtain ⟨hdatV, hKV⟩ := tfLevel_lt hx hx1 hO1N (hNG.trans tf_gg_lt_BG) hNT hKT hK1
  rw [← hVeq] at hdatV hKV
  have hB2read : vD ucB x = vt x (Om1 * ggE) := by
    rw [vD_base' qd_B2_E qd_B2_G0 (qd_B2_lt_B3 S), qd_B2_read S]
  have hgB2 : qdGt ucB < x := by rw [qd_B2_gate S]; exact hx.pos
  have hlemono : ∀ b c, b ≤ c → c < E → qdGt b < x → qdGt c < x → vD b x ≤ vD c x := fun b c hbc hc hgb hgc =>
    qd_le_mono S hE hBE hEB hlim hIH hx hx1 hbc hc hgb hgc
  set fE : Ordinal.{0} → Ordinal.{0} := fun d => if d < E then vD d x else 0 with hfEdef
  have hE0 : (0 : Ordinal.{0}) < E := hE.pos
  have hcode : ∀ c, c < E → qdGt c < x → vD c x ∈ Tset x ∧ vD c x < Om1 := fun c hc hgc =>
    ⟨(qd_T S hE hBE hEB hlim hIH hx hx1 hc hgc).1, (qd_T S hE hBE hEB hlim hIH hx hx1 hc hgc).2.1⟩
  have hf0 : fE 0 = 0 := by simp only [hfEdef, if_pos hE0, vD_zero]
  have hD0 : (fun d => d < E ∧ qdGt d < x) 0 := ⟨hE0, by rw [qdGt_zero]; exact hx.pos⟩
  have hfΩ : ∀ d, (fun d => d < E ∧ qdGt d < x) d → fE d < Om1 := fun d hd => by
    simp only [hfEdef, if_pos hd.1]; exact (hcode d hd.1 hd.2).2
  have hfm : ∀ d d', (fun d => d < E ∧ qdGt d < x) d → (fun d => d < E ∧ qdGt d < x) d' → d < d' →
      fE d < fE d' := fun d d' hd hd' hdd => by
    simp only [hfEdef, if_pos hd.1, if_pos hd'.1]
    exact qd_mono S hE hBE hEB hlim hIH hx hx1 hdd hd'.1 hd.2 hd'.2
  have hlx : qdLvx E (qdLev E) x = qdLv fE (qdLev E) := rfl
  rcases lt_or_ge (qdLev E) ucE with hlt | hge
  · -- a level below `E₂`
    have hBE2 : ucB < E := lt_of_le_of_ne hXE fun h => by
      have := qd_B2_lev S; rw [h] at this; exact absurd this hlt.ne
    by_cases hvis : qdFold id (qdLev E) < ucB
    · -- `B₂` is a fixed point of `Hᵛ_λ` below `y`
      have hfixB := qd_low_fix S hlt hvis
      have hBy : ucB < qdI (qdLev E) E := by
        by_contra h
        push Not at h
        rcases h.lt_or_eq with h' | h'
        · have h2 := (qdH_lt_iff (qdLev E)).2 h'
          rw [hFy, hfixB] at h2
          exact absurd hBE2 (not_lt.2 h2.le)
        · have h2 := hFy; rw [h', hfixB] at h2; exact absurd h2 hBE2.ne
      have hFy' : QdFixH (qdLev E) (qdI (qdLev E) E) := ⟨_, hfixB, hBy⟩
      obtain ⟨-, -, hpy⟩ := qd_fpH_mem hne hFy'
      obtain ⟨hgp, -⟩ := hgF hFy'
      have hBp : ucB ≤ qdFpH (qdLev E) (qdI (qdLev E) E) := le_csSup ⟨_, fun _ h => h.2.le⟩ ⟨hfixB, hBy⟩
      have h1 := hlemono _ _ hBp (hpy.trans hyE) hgB2 (hgp.trans_lt hgx)
      have h2 : vD (qdFpH (qdLev E) (qdI (qdLev E) E)) x ≤ qdRK (qdLev E) (qdI (qdLev E) E) x := by
        unfold qdRK; rw [if_pos hFy']; exact le_self_add
      rw [← hB2read]
      exact (h1.trans h2).trans hKV.le
    · -- a leaf `d ≥ B₂` of `λ`
      have hex : ∃ d ∈ qdComps (qdLev E), ucB ≤ d := by
        by_contra hcon
        push Not at hcon
        exact hvis ((qdFold_lt_iff ucB_SC.1 _).2 hcon)
      obtain ⟨d, hd, hBd⟩ := hex
      obtain ⟨hdE, hgd⟩ := hcomp d hd
      have hdat := qdLv_dat_ge fE (fun d => d < E ∧ qdGt d < x) hf0 hD0 hfΩ hfm _ hlG hcomp d hd
      simp only [hfEdef, if_pos hdE] at hdat
      have hLG := (qdLv_main fE (fun d => d < E ∧ qdGt d < x) hf0 hD0 hfΩ hfm _ hlG hcomp).1
      have hdat' : vD d x ≤ tfDat (Om1 + qdLvx E (qdLev E) x) := by
        rw [hlx, tfDat_eq_ss _ (tf_Om1_add_lt_gg hLG), qd_ssDat_Om1_add (hlx ▸ hL1) hLG]; exact hdat
      rw [← hB2read]
      exact ((hlemono _ _ hBd hdE hgB2 hgd).trans hdat').trans hdatV.le
  · -- a level from `E₂` on: the level reading is at least `ε_{Ω₁+1}`
    have hcE : ∀ d ∈ qdComps ucE, d < E ∧ qdGt d < x := fun d hd => by
      rw [qdComps_E2 d hd]
      refine ⟨qd_one_lt_B2.trans_le hXE, ?_⟩
      rw [show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_num, qdGt_nat]
      exact (natCast_lt_omega0 1).trans hωx
    have hf1 : fE 1 = 1 := by simp only [hfEdef, if_pos (qd_one_lt_B2.trans_le hXE), vD_one]
    have hgeL : ggE ≤ qdLvx E (qdLev E) x := by
      rw [hlx, ← qdLv_E2 fE hf1]
      rcases hge.lt_or_eq with h | h
      · exact ((qdLv_main fE (fun d => d < E ∧ qdGt d < x) hf0 hD0 hfΩ hfm _ hlG hcomp).2.2.2.2.2 _ h hcE).le
      · rw [h]
    have hN : ggE ≤ Om1 + qdLvx E (qdLev E) x := hgeL.trans le_add_self
    have hOE : Om1 < ggE := by rw [rj_Om1]; exact ggE_spec.2
    have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
    have h0Ω : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
    have hdE : tfDat ggE ∈ Tset x := by rw [tfDat_E]; exact mem_T_of_le hx hx1 (lu_one_lt_E hx).le
    have hle : Om1 * ggE + 0 ≤ Om1 * (Om1 + qdLvx E (qdLev E) x) + qdRK (qdLev E) (qdI (qdLev E) E) x := by
      rw [add_zero]; exact (mul_le_mul_right hN _).trans le_self_add
    rw [hVeq]
    rcases hle.lt_or_eq with hlt' | heq'
    · have h := tfVt_lt hx hx1 hO1N (hNG.trans tf_gg_lt_BG) (tf_M_le hK1 hlt') hdE h0T h0Ω hNT hKT hK1 hlt'
        (by rw [tfDat_E]; exact (lu_one_lt_E hx).trans_le hxV.le |>.trans_eq hVeq)
        ((hx.pos.trans_le hxV.le).trans_eq hVeq)
      rw [add_zero] at h
      exact h.le
    · rw [← heq', add_zero]

/-- **Every code below the fixed point reads below its reading.** -/
theorem qd_fx_lt (hI : QdImgH) (hgx : max ω (qdQEt E) < x) : ∀ c, c < E → qdGt c < x → vD c x < qdA E x := by
  have hωx : ω < x := omega0_lt_inE hx
  obtain ⟨hfixE, hl0, hlG, hlc, hyE, hFy, hne, -⟩ := qd_fx_dat S hEB hXE hA hi
  obtain ⟨hVeq, hcl, hVT, hVE, hxV, -, hV1⟩ := qd_fx_V S hE hBE hEB hXE hlim hIH hA hi hx hx1 hI hgx
  obtain ⟨hcomp, hL1, hNG, hNT, hKT, hK1, -⟩ := qd_fx_parts S hE hBE hEB hXE hlim hIH hA hi hx hx1 hgx
  obtain ⟨-, hgF, hg0y⟩ := qd_fix_gates S hA hi hXE hEB
  have hB2 := qd_fx_B2 S hE hBE hEB hXE hlim hIH hA hi hx hx1 hI hgx
  have hmono : ∀ b c, b < c → c < E → qdGt b < x → qdGt c < x → vD b x < vD c x := fun b c hbc hc hgb hgc =>
    qd_mono S hE hBE hEB hlim hIH hx hx1 hbc hc hgb hgc
  have hlemono : ∀ b c, b ≤ c → c < E → qdGt b < x → qdGt c < x → vD b x ≤ vD c x := fun b c hbc hc hgb hgc =>
    qd_le_mono S hE hBE hEB hlim hIH hx hx1 hbc hc hgb hgc
  have hcodeE : ∀ c, c < E → qdGt c < x → vD c x ∈ Tset x ∧ vD c x < Om1 := fun c hc hgc =>
    ⟨(qd_T S hE hBE hEB hlim hIH hx hx1 hc hgc).1, (qd_T S hE hBE hEB hlim hIH hx hx1 hc hgc).2.1⟩
  -- the data of the level and the index are below the reading
  have hO1N : Om1 ≤ Om1 + qdLvx E (qdLev E) x := le_self_add
  obtain ⟨hdatV, hKV⟩ := tfLevel_lt hx hx1 hO1N (hNG.trans tf_gg_lt_BG) hNT hKT hK1
  rw [← hVeq] at hdatV hKV
  -- the leaf readings of the level are below the reading
  set fE : Ordinal.{0} → Ordinal.{0} := fun d => if d < E then vD d x else 0 with hfEdef
  have hE0 : (0 : Ordinal.{0}) < E := hE.pos
  have hf0 : fE 0 = 0 := by simp only [hfEdef, if_pos hE0, vD_zero]
  have hD0 : (fun d => d < E ∧ qdGt d < x) 0 := ⟨hE0, by rw [qdGt_zero]; exact hx.pos⟩
  have hfΩ : ∀ d, (fun d => d < E ∧ qdGt d < x) d → fE d < Om1 := fun d hd => by
    simp only [hfEdef, if_pos hd.1]; exact (hcodeE d hd.1 hd.2).2
  have hfm : ∀ d d', (fun d => d < E ∧ qdGt d < x) d → (fun d => d < E ∧ qdGt d < x) d' → d < d' →
      fE d < fE d' := fun d d' hd hd' hdd => by
    simp only [hfEdef, if_pos hd.1, if_pos hd'.1]; exact hmono d d' hdd hd'.1 hd.2 hd'.2
  have hlx : qdLvx E (qdLev E) x = qdLv fE (qdLev E) := rfl
  have hcompV : ∀ d ∈ qdComps (qdLev E), vD d x < qdA E x := fun d hd => by
    have h := qd_comp_lt fE (fun d => d < E ∧ qdGt d < x) hf0 hD0 hfΩ hfm hlG hcomp (hlx ▸ hL1) hdatV d hd
    simp only [hfEdef, if_pos (hcomp d hd).1] at h
    exact h
  have hglA : ∀ a t, a < qdA E x → t < qdA E x → glA a t x < qdA E x := by
    intro a t ha ht
    have hmT : max a t ∈ Tset x := vz_T_down hx hx1 hVT hV1 (max_lt ha ht).le
    have hm1 : max a t < Om1 := (max_lt ha ht).trans hV1
    have hq := gmq_gt hx hx1 hmT hm1
    exact (xkA_lt hx hx1 hmT hm1 ((le_max_left _ _).trans_lt hq) ((le_max_right _ _).trans_lt hq)).trans
      (hcl _ hmT (max_lt ha ht))
  have hDB : ywV 1 0 x ≤ qdA E x := (ywBG hx hx1).2.2 _ hxV hcl
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  have hcB : c < qdB := hc.trans hEB
  by_cases hcBG : c < tfBG
  · have hcX : c < tlX := hcBG.trans tl_BG_lt_X
    have hcB2 : c < ucB := hcX.trans uc_X_lt_B
    rw [vD_low hcB2, vQ_low hcX, vR_yr c hcBG x]
    rw [qdGt_low hcB2, qcG_low hcX] at hg
    exact (zmYr.lt c x hx hx1 hcBG hg).trans_le hDB
  have hcB' : tfBG ≤ c := not_lt.1 hcBG
  rcases lt_or_ge c ucB with hcB2 | hXc
  · -- below `B₂`
    rw [vD_low hcB2]
    rw [qdGt_low hcB2] at hg
    exact (qd_low_lt hx hx1 (qd_low_bd S hx hx1 hcB2 hg)).trans_le hB2
  have hGc : gcG 0 ≤ c := va_G_le_BG.trans hcB'
  obtain ⟨-, -, -, -, -, hlog, hmod, hdiv⟩ := gl_parts (yh_gfE_le hGc)
  obtain ⟨hgQE, q1, q2, hgr⟩ := qd_parts_Q hGc hcB hg
  have hgk := qdGt_of_Q hωx q1
  have hgd := qdGt_of_Q hωx q2
  have heB : tfBG ≤ guE c := gl_E_max (Low.opow_eq_self_of_SC tfBG_SC) tfBG_gt hcB'
  have hec : guE c ≤ c := gl_E_le (yh_gfE_le hGc)
  have heE := guE_E c
  have hGe : gcG 0 ≤ guE c := va_G_le_BG.trans heB
  have he'E : guE c < E := hec.trans_lt hc
  have he'B : guE c < qdB := he'E.trans hEB
  have hXe : ucB ≤ guE c := (qd_guE_B hXc hcB).1
  have hA' : qdA (guE c) x < qdA E x := by
    rcases vs_atom_cases heB with hB | ⟨hAc, hjB, hjE'⟩ | hnA
    · -- a fixed point `e = Hᵛ_μ(z) < E` of `Γ`: compare the levels
      have hF'fix : gamma (guE c) = guE c := by rw [hB]; exact vs_FB_fix heB
      have hOF' : Om1 < guE c := tfBG_gt.trans_le heB
      have hAF : YhAt (guE c) := ⟨by rw [← hF'fix]; exact Lq.lq_gamma_SC _, hOF'⟩
      have hiF : ¬ yhJ (guE c) < guE c := by
        have h := yhJ_gcG (guE c); rw [vs_gcG_fix hF'fix hOF'] at h; rw [h]; exact lt_irrefl _
      have hgxF : max ω (qdQEt (guE c)) < x := max_lt hωx hgQE
      have hcode' : ∀ c', c' < guE c → qdGt c' < x → vD c' x ∈ Tset x ∧ vD c' x < Om1 := fun c' hc' hg' =>
        hcodeE c' (hc'.trans he'E) hg'
      have hmono' : ∀ b c', b < c' → c' < guE c → qdGt b < x → qdGt c' < x → vD b x < vD c' x :=
        fun b c' hbc hc' hgb hgc => hmono b c' hbc (hc'.trans he'E) hgb hgc
      obtain ⟨hcompe, hμ1, hNeG, hNeT, hdatle, hKeT, hKe1⟩ :=
        qd_fix_lev_u S hx hx1 hAF hiF hXe he'B hgxF hcode' hmono'
      obtain ⟨-, hgFe, hg0e⟩ := qd_fix_gates S hAF hiF hXe he'B
      obtain ⟨-, -, -, hzc, hnfe, hzr⟩ := qd_fix_data S hAF hiF hXe he'B
      -- the parts of `e` read below the reading of `E`
      have hfoldV : qdFold (fun d => if d < guE c then vD d x else 0) (qdLev (guE c)) < qdA E x := by
        refine (qdFold_lt_iff' _ hVE.pos _).2 fun d hd => ?_
        obtain ⟨hde, hgd'⟩ := hcompe d hd
        simp only [if_pos hde]
        exact IH d (hde.trans_le hec) (hde.trans he'E) hgd'
      have hdatV' := hdatle.trans_lt hfoldV
      have hKeV : qdRK (qdLev (guE c)) (qdI (qdLev (guE c)) (guE c)) x < qdA E x := by
        unfold qdRK
        split_ifs with hF
        · obtain ⟨-, -, hpz⟩ := qd_fpH_mem hzr hF
          obtain ⟨hgp, hgo⟩ := hgFe hF
          have h1 := (hpz.trans hzc).trans_le hec
          have h2 : qdI (qdLev (guE c)) (guE c) - (qdFpH (qdLev (guE c)) (qdI (qdLev (guE c)) (guE c)) + 1) < c :=
            ((Ordinal.sub_le_self _ _).trans_lt hzc).trans_le hec
          exact (inE_indec hVE).add_lt (IH _ h1 (h1.trans hc) (hgp.trans_lt hgxF))
            (IH _ h2 (h2.trans hc) (hgo.trans_lt hgxF))
        · have h2 := hzc.trans_le hec
          exact IH _ h2 (h2.trans hc) ((hg0e hF).trans_lt hgxF)
      rw [← vD_base' heE hGe he'B, vD_fix hAF hiF hzc hXe he'B x]
      -- the level reading of `e` with the leaves read as for `E`
      have hlvx : qdLvx (guE c) (qdLev (guE c)) x = qdLv fE (qdLev (guE c)) := by
        unfold qdLvx
        refine qdLv_congr _ fun d hd => ?_
        have hde := (hcompe d hd).1
        simp only [hfEdef, if_pos hde, if_pos (hde.trans he'E)]
      rcases lt_trichotomy (qdLev (guE c)) (qdLev E) with hlt | heq | hgt
      · -- a lower level
        have hcompμ : ∀ d ∈ qdComps (qdLev (guE c)), d < E ∧ qdGt d < x := fun d hd =>
          ⟨(hcompe d hd).1.trans he'E, (hcompe d hd).2⟩
        have hord := (qdLv_main fE _ hf0 hD0 hfΩ hfm _ hlG hcomp).2.2.2.2.2 _ hlt hcompμ
        have hNlt : Om1 + qdLvx (guE c) (qdLev (guE c)) x < Om1 + qdLvx E (qdLev E) x := by
          rw [hlvx]; exact (add_lt_add_iff_left _).2 hord
        have harg : Om1 * (Om1 + qdLvx (guE c) (qdLev (guE c)) x) +
              qdRK (qdLev (guE c)) (qdI (qdLev (guE c)) (guE c)) x <
            Om1 * (Om1 + qdLvx E (qdLev E) x) + qdRK (qdLev E) (qdI (qdLev E) E) x := by
          calc _ < Om1 * (Om1 + qdLvx (guE c) (qdLev (guE c)) x) + Om1 := (add_lt_add_iff_left _).2 hKe1
            _ = Om1 * (Om1 + qdLvx (guE c) (qdLev (guE c)) x + 1) := (mul_add_one _ _).symm
            _ ≤ Om1 * (Om1 + qdLvx E (qdLev E) x) := mul_le_mul_right (Order.add_one_le_of_lt hNlt) _
            _ ≤ _ := le_self_add
        rw [hVeq]; rw [hVeq] at hdatV' hKeV
        exact tfVt_lt hx hx1 hO1N (hNG.trans tf_gg_lt_BG) (tf_M_le hK1 harg) hNeT hKeT hKe1 hNT hKT hK1 harg
          hdatV' hKeV
      · -- the same level: `z < y`, the index readings are ordered
        have hzy : qdI (qdLev E) (guE c) < qdI (qdLev E) E := by
          have h : qdH (qdLev E) (qdI (qdLev E) (guE c)) < qdH (qdLev E) (qdI (qdLev E) E) := by
            rw [hFy, ← heq, hnfe]; exact he'E
          exact (qdH_lt_iff _).1 h
        have hgf' : QdFixH (qdLev E) (qdI (qdLev E) (guE c)) →
            qdGt (qdFpH (qdLev E) (qdI (qdLev E) (guE c))) < x ∧
              qdGt (qdI (qdLev E) (guE c) - (qdFpH (qdLev E) (qdI (qdLev E) (guE c)) + 1)) < x := fun hF => by
          rw [← heq] at hF ⊢
          exact ⟨((hgFe hF).1).trans_lt hgxF, ((hgFe hF).2).trans_lt hgxF⟩
        have hg0' : ¬ QdFixH (qdLev E) (qdI (qdLev E) (guE c)) → qdGt (qdI (qdLev E) (guE c)) < x := fun hF => by
          rw [← heq] at hF ⊢; exact (hg0e hF).trans_lt hgxF
        have hzr' : qdH (qdLev E) (qdI (qdLev E) (guE c)) ≠ qdI (qdLev E) (guE c) := by rw [← heq]; exact hzr
        have hKlt := qd_fx_Kmono S hE hBE hEB hXE hlim hIH hA hi hx hx1 hgx hzy hzr' hgf' hg0'
        have hlv : qdLvx (guE c) (qdLev (guE c)) x = qdLvx E (qdLev E) x := by rw [hlvx, heq]; rfl
        rw [hlv, heq]
        rw [hlv] at hNeG hNeT hdatV'
        rw [heq] at hKeT hKe1 hKeV
        rw [hVeq]; rw [hVeq] at hdatV' hKeV
        have harg := (add_lt_add_iff_left (Om1 * (Om1 + qdLvx E (qdLev E) x))).2 hKlt
        exact tfVt_lt hx hx1 hO1N (hNG.trans tf_gg_lt_BG) (tf_M_le hK1 harg) hNeT hKeT hKe1 hNT hKT hK1 harg
          hdatV' hKeV
      · -- a higher level: `e` is a fixed point of `Hᵛ_λ` below `y`, or below a leaf of `λ`
        rw [← vD_fix hAF hiF hzc hXe he'B x]
        by_cases hCe : qdFold id (qdLev E) < guE c
        · have hfixl : qdH (qdLev E) (guE c) = guE c := ucG_fix_lower hgt ⟨_, hnfe⟩ hCe
          have hey : guE c < qdI (qdLev E) E := by
            by_contra h
            push Not at h
            rcases h.lt_or_eq with h' | h'
            · have h2 := (qdH_lt_iff (qdLev E)).2 h'
              rw [hFy, hfixl] at h2
              exact absurd he'E (not_lt.2 h2.le)
            · have h2 := hFy; rw [h', hfixl] at h2; exact absurd h2 he'E.ne
          have hFy' : QdFixH (qdLev E) (qdI (qdLev E) E) := ⟨_, hfixl, hey⟩
          obtain ⟨-, -, hpy⟩ := qd_fpH_mem hne hFy'
          obtain ⟨hgp, -⟩ := hgF hFy'
          have hep : guE c ≤ qdFpH (qdLev E) (qdI (qdLev E) E) := le_csSup ⟨_, fun _ h => h.2.le⟩ ⟨hfixl, hey⟩
          have h1 := hlemono _ _ hep (hpy.trans hyE) (by rw [qdGt_base' heE hGe he'B]; exact hgQE)
            (hgp.trans_lt hgx)
          have h2 : vD (qdFpH (qdLev E) (qdI (qdLev E) E)) x ≤ qdRK (qdLev E) (qdI (qdLev E) E) x := by
            unfold qdRK; rw [if_pos hFy']; exact le_self_add
          exact (h1.trans h2).trans_lt hKV
        · have h0 : (0 : Ordinal.{0}) < guE c := heE.pos
          have hex : ∃ d ∈ qdComps (qdLev E), guE c ≤ d := by
            by_contra hcon
            push Not at hcon
            exact hCe ((qdFold_lt_iff h0 _).2 hcon)
          obtain ⟨d, hd, hed⟩ := hex
          obtain ⟨hdE, hgd'⟩ := hcomp d hd
          exact (hlemono _ _ hed hdE (by rw [qdGt_base' heE hGe he'B]; exact hgQE) hgd').trans_lt (hcompV d hd)
    · -- an atom `Γ(j)` past its segment base: the index reading is below the reading
      rw [qdA_atom' he'B hAc hjE', qd_vI heB hjB hjE'.le]
      have hFe : vaFB (guE c) < c := hjB.trans (hjE'.trans_le hec)
      have hgeQ : qdGt (guE c) < x := by rw [qdGt_base' heE hGe he'B]; exact hgQE
      have hgF' : qdGt (vaFB (guE c)) < x := (qd_FB_gate' heB he'B).trans_lt (max_lt hωx hgeQ)
      have hgj : qdGt (yhJ (guE c)) < x := by
        rw [qdQEt_atom' he'B hAc hjE'] at hgQE; exact qdGt_of_Q hωx hgQE
      have hgo := (qd_off_gate' (vs_FB_E heB) (va_G_le_BG.trans (vs_FB_ge heB)) (hjE'.trans he'B) hjB).trans_lt
        (max_lt hωx hgj)
      have ho : yhJ (guE c) - (vaFB (guE c) + 1) < c := (Ordinal.sub_le_self _ _).trans_lt (hjE'.trans_le hec)
      have hI' : vD (vaFB (guE c)) x + vD (yhJ (guE c) - (vaFB (guE c) + 1)) x < qdA E x :=
        (inE_indec hVE).add_lt (IH _ hFe (hFe.trans hc) hgF') (IH _ ho (ho.trans hc) hgo)
      exact hcl _ (vz_T_down hx hx1 hVT hV1 hI'.le) hI'
    · have hGe' : gcG 0 < guE c := lt_of_le_of_ne hGe fun h => hnA (h ▸ yhAt_gcG 0)
      rw [qdA_psi'' heE hGe' he'B hnA]
      have hK := yh_lev_lt hGc hnA
      have hI' := yh_idx_lt hGc hnA
      rw [qdQEt_psi' heE hGe' he'B hnA] at hgQE
      exact hglA _ _ (IH _ hK (hK.trans hc) (qdGt_of_Q hωx ((le_max_left _ _).trans_lt hgQE)))
        (IH _ hI' (hI'.trans hc) (qdGt_of_Q hωx ((le_max_right _ _).trans_lt hgQE)))
  rw [vD_dec' hGc hcB x]
  exact (inE_indec hVE).add_lt (InE.mul_lt hVE (zm_opow_lt hVE hA' (IH _ hlog (hlog.trans hc) hgk))
    (IH _ hdiv (hdiv.trans hc) hgd)) (IH _ hmod (hmod.trans hc) hgr)

end Fix

end Googology.Trans.PoR.InaccPsi.R2.Qd
