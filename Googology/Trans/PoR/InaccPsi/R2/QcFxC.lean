import Googology.Trans.PoR.InaccPsi.R2.QcDat

/-!
# QcFxC: EVERY CODE BELOW THE FIXED POINT `E = H_λ(y)` READS BELOW IT

As `Va.vs_fx_lt` from `X` on.  A smaller fixed point `e = H_μ(z) < E` of `Γ` reads `ϑˣ(Ω₁·(Ω₁+μ(x)) + K_e(x))`
(`Qc.qs_fixRd`) below `ϑˣ(Ω₁·(Ω₁+λ(x)) + K(x))` by the levels: `μ < λ` (the level readings are ordered,
`Qc.qcLv_main`), `μ = λ` (`z < y`, the index readings are ordered, `qs_fx_Kmono`), `μ > λ` (`e` is a fixed point of
`H_λ` below `y`, read below `K(x)`, or below a component of `λ`, read below the reading of `E`, `Qc.qc_comp_lt`).

* `qs_fix_lev_u` (the level and index readings of a fixed point `e < B₂` of `Γ`, with the data bound);
* `qs_fx_eps`, `qs_fx_Kmono`, `qs_fx_lt` (**every code below `E` reads below `qcA E x`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yw
  Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Va Googology.Trans.PoR.InaccPsi.R2.Tl
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Yr
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Zm Googology.Trans.PoR.InaccPsi.R2.Tf
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Si Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Xk
  Googology.Trans.PoR.InaccPsi.R2.Gm

/-- **The level and index readings of a fixed point `e < B₂` of `Γ`** with the data bound
`rjDat(Ω₁ + μ(x)) ≤ max_{d ∈ comps μ} d(x)`. -/
theorem qs_fix_lev_u {e x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hA : YhAt e) (hi : ¬ yhJ e < e)
    (hB : e < ucB) (hgx : max ω (qcQE e) < x)
    (hcode : ∀ c, c < e → qcG c < x → vQ c x ∈ Tset x ∧ vQ c x < Om1)
    (hmono : ∀ b c, b < c → c < e → qcG b < x → qcG c < x → vQ b x < vQ c x) :
    (∀ d ∈ ucComps (ucLev e), d < e ∧ qcG d < x) ∧ 1 ≤ qcLvx e (ucLev e) x ∧
      Om1 + qcLvx e (ucLev e) x < ggE ∧ rjDat (Om1 + qcLvx e (ucLev e) x) ∈ Tset x ∧
      rjDat (Om1 + qcLvx e (ucLev e) x) ≤ ucFold (fun d => if d < e then vQ d x else 0) (ucLev e) ∧
      qcK (ucLev e) (ucI (ucLev e) e) x ∈ Tset x ∧ qcK (ucLev e) (ucI (ucLev e) e) x < Om1 := by
  have hO : Om1 < e := hA.2
  have hne' := uc_nf_of_lt hA.1 hO hB
  obtain ⟨hlE, hlc, -, -, -⟩ := ucLev_spec hA.1 hO hne'
  obtain ⟨hnf, hyc⟩ := uc_nf hA.1 hO hne'
  have hne : ucH (ucLev e) (ucI (ucLev e) e) ≠ ucI (ucLev e) e := by rw [hnf]; exact ne_of_gt hyc
  have hl0 : ucLev e ≠ 0 := by
    intro h0
    have hg : gcG (ucI (ucLev e) e) = e := by have h := hnf; rw [h0, qc_H0] at h; rw [h0]; exact h
    apply hi; rw [← hg, yhJ_gcG, hg]; have := hyc; rwa [h0] at this
  obtain ⟨hgcomp, hgF, hg0⟩ := qs_fix_gates hA hi hB
  have hcomp : ∀ d ∈ ucComps (ucLev e), d < e ∧ qcG d < x := fun d hd =>
    ⟨(le_ucC hd).trans_lt hlc, (hgcomp d hd).trans_lt hgx⟩
  set f : Ordinal.{0} → Ordinal.{0} := fun d => if d < e then vQ d x else 0 with hfdef
  have hE0 : (0 : Ordinal.{0}) < e := (show InE e from Low.opow_eq_self_of_SC hA.1).pos
  have hf0 : f 0 = 0 := by simp only [hfdef, if_pos hE0, vQ_zero]
  have hD0 : (fun d => d < e ∧ qcG d < x) 0 := ⟨hE0, by rw [qcG_zero]; exact hx.pos⟩
  have hfΩ : ∀ d, (fun d => d < e ∧ qcG d < x) d → f d < Om1 := fun d hd => by
    simp only [hfdef, if_pos hd.1]; exact (hcode d hd.1 hd.2).2
  have hfm : ∀ d d', (fun d => d < e ∧ qcG d < x) d → (fun d => d < e ∧ qcG d < x) d' → d < d' → f d < f d' :=
    fun d d' hd hd' hdd => by
      simp only [hfdef, if_pos hd.1, if_pos hd'.1]; exact hmono d d' hdd hd'.1 hd.2 hd'.2
  obtain ⟨hLE, hLdat, -, hLord⟩ := qcLv_main f (fun d => d < e ∧ qcG d < x) hf0 hD0 hfΩ hfm _ hlE hcomp
  have hlx : qcLvx e (ucLev e) x = qcLv f (ucLev e) := rfl
  have h0c : ∀ d ∈ ucComps 0, d < e ∧ qcG d < x := fun d hd => by
    rw [ucComps_small uc_SC_Om2.1, mem_singleton_iff] at hd; rw [hd]; exact hD0
  have hL1 : 1 ≤ qcLv f (ucLev e) := by
    have := hLord 0 (pos_iff_ne_zero.2 hl0) h0c
    rw [qcLv_small f uc_SC_Om2.1, hf0] at this; exact one_le_iff_ne_zero.2 this.ne'
  have hgE : InE ggE := ggE_spec.1
  have hOE : Om1 < ggE := by rw [rj_Om1]; exact ggE_spec.2
  obtain ⟨m, hmO, hT⟩ := qc_T_cut hx hx1
  have hle : rjDat (Om1 + qcLv f (ucLev e)) ≤ ucFold f (ucLev e) := by
    rcases lt_or_ge (qcLv f (ucLev e)) Om1 with hs | hs
    · rw [rjDat_Om1_add (one_le_iff_ne_zero.1 hL1) hs]; have h := hLdat; rwa [rjDat_small hs] at h
    · rw [si_rjDat_Om1_add hs hLE]; exact hLdat
  have hdatT : rjDat (Om1 + qcLv f (ucLev e)) ∈ Tset x := by
    have hfold : ucFold f (ucLev e) < m := by
      have hm0 : 0 < m := (hT 0 (hx.pos.trans hx1)).1 (mem_T_of_le hx hx1 zero_le)
      refine (ucFold_lt_iff f hm0 _).2 fun d hd => ?_
      obtain ⟨hde, hgd⟩ := hcomp d hd
      have := hcode d hde hgd
      simp only [hfdef, if_pos hde]
      exact (hT _ this.2).1 this.1
    have hlt := hle.trans_lt hfold
    exact (hT _ (hlt.trans_le hmO)).2 hlt
  have hKT : qcK (ucLev e) (ucI (ucLev e) e) x ∈ Tset x ∧ qcK (ucLev e) (ucI (ucLev e) e) x < Om1 := by
    unfold qcK
    split_ifs with hF
    · obtain ⟨-, -, hpy⟩ := qc_fpH_mem hne hF
      obtain ⟨hgp, hgo⟩ := hgF hF
      obtain ⟨hpT, hp1⟩ := hcode _ (hpy.trans hyc) (hgp.trans_lt hgx)
      obtain ⟨hoT, ho1⟩ := hcode _ ((Ordinal.sub_le_self _ _).trans_lt hyc) (hgo.trans_lt hgx)
      exact ⟨vzT_add hx hx1 hpT hoT, (inE_indec Gl.gl_Om1_E).add_lt hp1 ho1⟩
    · exact hcode _ hyc ((hg0 hF).trans_lt hgx)
  exact ⟨hcomp, hL1, hgE.add_lt hOE hLE, hdatT, hle, hKT.1, hKT.2⟩

section Fix

variable {E : Ordinal.{0}} (hE : InE E) (hBE : tfBG < E) (hEB : E < ucB) (hXE : tlX ≤ E)
  (hlim : ∀ e, InE e → e < E → eN e < E) (hIH : ∀ e, InE e → tfBG ≤ e → e < E → QsGood e)
  (hA : YhAt E) (hi : ¬ yhJ E < E)
  {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)

include hE hBE hEB hXE hlim hIH hA hi hx hx1

omit hBE hlim hXE hA hi in
/-- **The readings of the `ε`-number codes below `E` are `ε`-numbers.** -/
theorem qs_fx_eps {e' : Ordinal.{0}} (he' : InE e') (hBe' : tfBG ≤ e') (he'E : e' < E) (hg : qcG e' < x) :
    InE (vQ e' x) := by
  have hωx : ω < x := omega0_lt_inE hx
  have hGe : gcG 0 ≤ e' := va_G_le_BG.trans hBe'
  have he'B : e' < ucB := he'E.trans hEB
  obtain ⟨M, -, hEg, hV, -⟩ := hIH e' he' hBe' he'E
  have hgM : M.Eg < x := by rw [hEg]; exact max_lt hωx (by rw [← qcG_base' he' hGe he'B]; exact hg)
  have h := (M.V_T x hx hx1 hgM).2.1
  rwa [hV x hx hx1 hgM, ← vQ_base' he' hGe he'B] at h

/-- **The index readings of `H_λ` are ordered** below `E = H_λ(y)`: `qcK λ z x < qcK λ y x` for `z < y`, `z` not a
fixed point of `H_λ`, the parts of `z` with gates below `x`. -/
theorem qs_fx_Kmono (hgx : max ω (qcQE E) < x) {z : Ordinal.{0}} (hzy : z < ucI (ucLev E) E)
    (hzr : ucH (ucLev E) z ≠ z)
    (hgf : QcFixH (ucLev E) z → qcG (qcFpH (ucLev E) z) < x ∧ qcG (z - (qcFpH (ucLev E) z + 1)) < x)
    (hg0 : ¬ QcFixH (ucLev E) z → qcG z < x) :
    qcK (ucLev E) z x < qcK (ucLev E) (ucI (ucLev E) E) x := by
  obtain ⟨-, -, -, -, hyE, -, hne, -⟩ := qs_fx_dat hEB hXE hA hi
  obtain ⟨-, hgF, hg0y⟩ := qs_fix_gates hA hi hEB
  have hmono : ∀ b c, b < c → c < E → qcG b < x → qcG c < x → vQ b x < vQ c x := fun b c hbc hc hgb hgc =>
    qs_mono hE hBE hEB hlim hIH hx hx1 hbc hc hgb hgc
  unfold qcK
  by_cases hFy : QcFixH (ucLev E) (ucI (ucLev E) E)
  · obtain ⟨hffy, hOfy, hfyy⟩ := qc_fpH_mem hne hFy
    obtain ⟨hgfy', hgoy'⟩ := hgF hFy
    have hgfy := hgfy'.trans_lt hgx
    have hgoy := hgoy'.trans_lt hgx
    rw [if_pos hFy]
    have hle_y : ∀ f', ucH (ucLev E) f' = f' → f' < ucI (ucLev E) E → f' ≤ qcFpH (ucLev E) (ucI (ucLev E) E) :=
      fun f' h1 h2 => le_csSup ⟨_, fun _ h => h.2.le⟩ ⟨h1, h2⟩
    have hzp : ¬ qcFpH (ucLev E) (ucI (ucLev E) E) < z → z < qcFpH (ucLev E) (ucI (ucLev E) E) := fun h => by
      rcases (not_lt.1 h).lt_or_eq with h' | h'
      · exact h'
      · exact absurd (h' ▸ hffy) hzr
    by_cases hFz : QcFixH (ucLev E) z
    · obtain ⟨hffz, -, hfzz⟩ := qc_fpH_mem hzr hFz
      obtain ⟨hgfz, hgoz⟩ := hgf hFz
      rw [if_pos hFz]
      have hfle := hle_y _ hffz (hfzz.trans hzy)
      rcases hfle.lt_or_eq with hflt | hfeq
      · have hzfy : z < qcFpH (ucLev E) (ucI (ucLev E) E) := hzp fun h => by
          have := hle_y _ hffy |> fun _ => (show qcFpH (ucLev E) (ucI (ucLev E) E) ≤ qcFpH (ucLev E) z from
            le_csSup ⟨_, fun _ h => h.2.le⟩ ⟨hffy, h⟩)
          exact absurd this (not_le.2 hflt)
        have hSC : SC (qcFpH (ucLev E) (ucI (ucLev E) E)) := by rw [← hffy]; exact ucH_SC _ _
        have hfyE : InE (vQ (qcFpH (ucLev E) (ucI (ucLev E) E)) x) :=
          qs_fx_eps hE hEB hIH hx hx1 (Low.opow_eq_self_of_SC hSC)
            (tfBG_le (qc_P_gamma (qs_fx_dat hEB hXE hA hi).2.1 hffy) hOfy) (hfyy.trans hyE) hgfy
        exact ((inE_indec hfyE).add_lt (hmono _ _ hflt (hfyy.trans hyE) hgfz hgfy)
          (hmono _ _ ((Ordinal.sub_le_self _ _).trans_lt hzfy) (hfyy.trans hyE) hgoz hgfy)).trans_le le_self_add
      · rw [hfeq] at hgoz ⊢
        have hfz' : qcFpH (ucLev E) (ucI (ucLev E) E) < z := by rw [← hfeq]; exact hfzz
        exact (add_lt_add_iff_left _).2 (hmono _ _ (vs_sub_lt (Order.add_one_le_of_lt hfz') hzy)
          ((Ordinal.sub_le_self _ _).trans_lt hyE) hgoz hgoy)
    · rw [if_neg hFz]
      have hzfy : z < qcFpH (ucLev E) (ucI (ucLev E) E) := hzp fun h => hFz ⟨_, hffy, h⟩
      exact (hmono _ _ hzfy (hfyy.trans hyE) (hg0 hFz) hgfy).trans_le le_self_add
  · have hFz : ¬ QcFixH (ucLev E) z := fun ⟨f, h1, h2⟩ => hFy ⟨f, h1, h2.trans hzy⟩
    rw [if_neg hFy, if_neg hFz]
    exact hmono _ _ hzy hyE (hg0 hFz) ((hg0y hFy).trans_lt hgx)

/-- **Every code below the fixed point reads below its reading.** -/
theorem qs_fx_lt (hgx : max ω (qcQE E) < x) : ∀ c, c < E → qcG c < x → vQ c x < qcA E x := by
  have hωx : ω < x := omega0_lt_inE hx
  obtain ⟨hfixE, hl0, hlE, hlc, hyE, hFy, hne, -⟩ := qs_fx_dat hEB hXE hA hi
  obtain ⟨hVeq, hcl, hVT, hVE, hxV, -, hV1⟩ := qs_fx_V hE hBE hEB hXE hlim hIH hA hi hx hx1 hgx
  obtain ⟨hcomp, hL1, hNE, hNT, hKT, hK1, -⟩ := qs_fx_parts hE hBE hEB hXE hlim hIH hA hi hx hx1 hgx
  obtain ⟨-, hgF, hg0y⟩ := qs_fix_gates hA hi hEB
  have hmono : ∀ b c, b < c → c < E → qcG b < x → qcG c < x → vQ b x < vQ c x := fun b c hbc hc hgb hgc =>
    qs_mono hE hBE hEB hlim hIH hx hx1 hbc hc hgb hgc
  have hlemono : ∀ b c, b ≤ c → c < E → qcG b < x → qcG c < x → vQ b x ≤ vQ c x := fun b c hbc hc hgb hgc =>
    qs_le_mono hE hBE hEB hlim hIH hx hx1 hbc hc hgb hgc
  have hcodeE : ∀ c, c < E → qcG c < x → vQ c x ∈ Tset x ∧ vQ c x < Om1 := fun c hc hgc =>
    ⟨(qs_T hE hBE hEB hlim hIH hx hx1 hc hgc).1, (qs_T hE hBE hEB hlim hIH hx hx1 hc hgc).2.1⟩
  -- the data of the level and the index are below the reading
  have hO1N : Om1 ≤ Om1 + qcLvx E (ucLev E) x := le_self_add
  obtain ⟨hdatV, hKV⟩ := rjLevel_lt_vt hx hx1 hO1N hNE hNT hKT hK1
  rw [← hVeq] at hdatV hKV
  -- the component readings of the level are below the reading
  set fE : Ordinal.{0} → Ordinal.{0} := fun d => if d < E then vQ d x else 0 with hfEdef
  have hE0 : (0 : Ordinal.{0}) < E := hE.pos
  have hf0 : fE 0 = 0 := by simp only [hfEdef, if_pos hE0, vQ_zero]
  have hD0 : (fun d => d < E ∧ qcG d < x) 0 := ⟨hE0, by rw [qcG_zero]; exact hx.pos⟩
  have hfΩ : ∀ d, (fun d => d < E ∧ qcG d < x) d → fE d < Om1 := fun d hd => by
    simp only [hfEdef, if_pos hd.1]; exact (hcodeE d hd.1 hd.2).2
  have hfm : ∀ d d', (fun d => d < E ∧ qcG d < x) d → (fun d => d < E ∧ qcG d < x) d' → d < d' →
      fE d < fE d' := fun d d' hd hd' hdd => by
    simp only [hfEdef, if_pos hd.1, if_pos hd'.1]; exact hmono d d' hdd hd'.1 hd.2 hd'.2
  have hcompV : ∀ d ∈ ucComps (ucLev E), vQ d x < qcA E x := fun d hd => by
    have h := qc_comp_lt fE (fun d => d < E ∧ qcG d < x) hf0 hD0 hfΩ hfm hlE hcomp hVE hdatV d hd
    simp only [hfEdef, if_pos (hcomp d hd).1] at h
    exact h
  have hglA : ∀ a t, a < qcA E x → t < qcA E x → glA a t x < qcA E x := by
    intro a t ha ht
    have hmT : max a t ∈ Tset x := vz_T_down hx hx1 hVT hV1 (max_lt ha ht).le
    have hm1 : max a t < Om1 := (max_lt ha ht).trans hV1
    have hq := gmq_gt hx hx1 hmT hm1
    exact (xkA_lt hx hx1 hmT hm1 ((le_max_left _ _).trans_lt hq) ((le_max_right _ _).trans_lt hq)).trans
      (hcl _ hmT (max_lt ha ht))
  have hDB : ywV 1 0 x ≤ qcA E x := (ywBG hx hx1).2.2 _ hxV hcl
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  have hcB : c < ucB := hc.trans hEB
  by_cases hcBG : c < tfBG
  · have hcX : c < tlX := hcBG.trans tl_BG_lt_X
    rw [vQ_low hcX, vR_yr c hcBG x]
    rw [qcG_low hcX] at hg
    exact (zmYr.lt c x hx hx1 hcBG hg).trans_le hDB
  have hcB' : tfBG ≤ c := not_lt.1 hcBG
  have hGc : gcG 0 ≤ c := va_G_le_BG.trans hcB'
  obtain ⟨-, -, -, -, -, hlog, hmod, hdiv⟩ := gl_parts (yh_gfE_le hGc)
  obtain ⟨hgQE, q1, q2, hgr⟩ := qc_parts_Q hGc hcB hg
  have hgk := qcG_of_Q hωx q1
  have hgd := qcG_of_Q hωx q2
  have heB : tfBG ≤ guE c := gl_E_max (Low.opow_eq_self_of_SC tfBG_SC) tfBG_gt hcB'
  have hec : guE c ≤ c := gl_E_le (yh_gfE_le hGc)
  have heE := guE_E c
  have hGe : gcG 0 ≤ guE c := va_G_le_BG.trans heB
  have he'E : guE c < E := hec.trans_lt hc
  have he'B : guE c < ucB := he'E.trans hEB
  have hA' : qcA (guE c) x < qcA E x := by
    rcases vs_atom_cases heB with hB | ⟨hAc, hjB, hjE'⟩ | hnA
    · -- a fixed point `e = H_μ(z) < E` of `Γ`: compare the levels
      have hF'fix : gamma (guE c) = guE c := by rw [hB]; exact vs_FB_fix heB
      have hOF' : Om1 < guE c := tfBG_gt.trans_le heB
      have hAF : YhAt (guE c) := ⟨by rw [← hF'fix]; exact Lq.lq_gamma_SC _, hOF'⟩
      have hiF : ¬ yhJ (guE c) < guE c := by
        have h := yhJ_gcG (guE c); rw [vs_gcG_fix hF'fix hOF'] at h; rw [h]; exact lt_irrefl _
      have hgxF : max ω (qcQE (guE c)) < x := max_lt hωx hgQE
      have hcode' : ∀ c', c' < guE c → qcG c' < x → vQ c' x ∈ Tset x ∧ vQ c' x < Om1 := fun c' hc' hg' =>
        hcodeE c' (hc'.trans he'E) hg'
      have hmono' : ∀ b c', b < c' → c' < guE c → qcG b < x → qcG c' < x → vQ b x < vQ c' x :=
        fun b c' hbc hc' hgb hgc => hmono b c' hbc (hc'.trans he'E) hgb hgc
      obtain ⟨hcompe, hμ1, hNeE, hNeT, hdatle, hKeT, hKe1⟩ :=
        qs_fix_lev_u hx hx1 hAF hiF he'B hgxF hcode' hmono'
      obtain ⟨-, hgFe, hg0e⟩ := qs_fix_gates hAF hiF he'B
      have hne' := uc_nf_of_lt hAF.1 hOF' he'B
      obtain ⟨-, hμc, -, -, -⟩ := ucLev_spec hAF.1 hOF' hne'
      obtain ⟨hnfe, hzc⟩ := uc_nf hAF.1 hOF' hne'
      have hzr : ucH (ucLev (guE c)) (ucI (ucLev (guE c)) (guE c)) ≠ ucI (ucLev (guE c)) (guE c) := by
        rw [hnfe]; exact ne_of_gt hzc
      -- the parts of `e` read below the reading of `E`
      have hfoldV : ucFold (fun d => if d < guE c then vQ d x else 0) (ucLev (guE c)) < qcA E x := by
        refine (ucFold_lt_iff _ hVE.pos _).2 fun d hd => ?_
        obtain ⟨hde, hgd'⟩ := hcompe d hd
        simp only [if_pos hde]
        exact IH d (hde.trans_le hec) (hde.trans he'E) hgd'
      have hdatV' := hdatle.trans_lt hfoldV
      have hKeV : qcK (ucLev (guE c)) (ucI (ucLev (guE c)) (guE c)) x < qcA E x := by
        unfold qcK
        split_ifs with hF
        · obtain ⟨-, -, hpz⟩ := qc_fpH_mem hzr hF
          obtain ⟨hgp, hgo⟩ := hgFe hF
          have h1 := (hpz.trans hzc).trans_le hec
          have h2 : ucI (ucLev (guE c)) (guE c) - (qcFpH (ucLev (guE c)) (ucI (ucLev (guE c)) (guE c)) + 1) < c :=
            ((Ordinal.sub_le_self _ _).trans_lt hzc).trans_le hec
          exact (inE_indec hVE).add_lt (IH _ h1 (h1.trans hc) (hgp.trans_lt hgxF))
            (IH _ h2 (h2.trans hc) (hgo.trans_lt hgxF))
        · have h2 := hzc.trans_le hec
          exact IH _ h2 (h2.trans hc) ((hg0e hF).trans_lt hgxF)
      rw [← vQ_base' heE hGe he'B, qs_fixRd hAF hiF he'B x]
      -- the level reading of `e` with the components read as for `E`
      have hlvx : qcLvx (guE c) (ucLev (guE c)) x = qcLv fE (ucLev (guE c)) := by
        unfold qcLvx
        refine qcLv_congr _ fun d hd => ?_
        have hde := (hcompe d hd).1
        simp only [hfEdef, if_pos hde, if_pos (hde.trans he'E)]
      rcases lt_trichotomy (ucLev (guE c)) (ucLev E) with hlt | heq | hgt
      · -- a lower level
        have hcompμ : ∀ d ∈ ucComps (ucLev (guE c)), d < E ∧ qcG d < x := fun d hd =>
          ⟨(hcompe d hd).1.trans he'E, (hcompe d hd).2⟩
        have hord := (qcLv_main fE _ hf0 hD0 hfΩ hfm _ hlE hcomp).2.2.2 _ hlt hcompμ
        have hNlt : Om1 + qcLvx (guE c) (ucLev (guE c)) x < Om1 + qcLvx E (ucLev E) x := by
          rw [hlvx]; exact (add_lt_add_iff_left _).2 hord
        have harg : Om1 * (Om1 + qcLvx (guE c) (ucLev (guE c)) x) + qcK (ucLev (guE c)) (ucI (ucLev (guE c)) (guE c)) x <
            Om1 * (Om1 + qcLvx E (ucLev E) x) + qcK (ucLev E) (ucI (ucLev E) E) x := by
          calc _ < Om1 * (Om1 + qcLvx (guE c) (ucLev (guE c)) x) + Om1 := (add_lt_add_iff_left _).2 hKe1
            _ = Om1 * (Om1 + qcLvx (guE c) (ucLev (guE c)) x + 1) := (mul_add_one _ _).symm
            _ ≤ Om1 * (Om1 + qcLvx E (ucLev E) x) := mul_le_mul_right (Order.add_one_le_of_lt hNlt) _
            _ ≤ _ := le_self_add
        rw [hVeq]; rw [hVeq] at hdatV' hKeV
        exact rjVt_lt hx hx1 hNeE hNeT hKeT hKe1 hO1N hNE hNT hKT hK1 harg hdatV' hKeV
      · -- the same level: `z < y`, the index readings are ordered
        have hzy : ucI (ucLev E) (guE c) < ucI (ucLev E) E := by
          have h : ucH (ucLev E) (ucI (ucLev E) (guE c)) < ucH (ucLev E) (ucI (ucLev E) E) := by
            rw [hFy, ← heq, hnfe]; exact he'E
          exact (ucH_lt_iff _).1 h
        have hgf' : QcFixH (ucLev E) (ucI (ucLev E) (guE c)) →
            qcG (qcFpH (ucLev E) (ucI (ucLev E) (guE c))) < x ∧
              qcG (ucI (ucLev E) (guE c) - (qcFpH (ucLev E) (ucI (ucLev E) (guE c)) + 1)) < x := fun hF => by
          rw [← heq] at hF ⊢
          exact ⟨((hgFe hF).1).trans_lt hgxF, ((hgFe hF).2).trans_lt hgxF⟩
        have hg0' : ¬ QcFixH (ucLev E) (ucI (ucLev E) (guE c)) → qcG (ucI (ucLev E) (guE c)) < x := fun hF => by
          rw [← heq] at hF ⊢; exact (hg0e hF).trans_lt hgxF
        have hzr' : ucH (ucLev E) (ucI (ucLev E) (guE c)) ≠ ucI (ucLev E) (guE c) := by rw [← heq]; exact hzr
        have hKlt := qs_fx_Kmono hE hBE hEB hXE hlim hIH hA hi hx hx1 hgx hzy hzr' hgf' hg0'
        have hlv : qcLvx (guE c) (ucLev (guE c)) x = qcLvx E (ucLev E) x := by rw [hlvx, heq]; rfl
        rw [hlv, heq]
        rw [hlv] at hNeE hNeT hdatV'
        rw [heq] at hKeT hKe1 hKeV
        rw [hVeq]; rw [hVeq] at hdatV' hKeV
        exact rjVt_lt hx hx1 hNeE hNeT hKeT hKe1 hO1N hNE hNT hKT hK1 ((add_lt_add_iff_left _).2 hKlt) hdatV' hKeV
      · -- a higher level: `e` is a fixed point of `H_λ` below `y`, or below a component of `λ`
        rw [← qs_fixRd hAF hiF he'B x]
        by_cases hCe : ucC (ucLev E) < guE c
        · have hfixl : ucH (ucLev E) (guE c) = guE c := ucG_fix_lower hgt ⟨_, hnfe⟩ hCe
          have hey : guE c < ucI (ucLev E) E := by
            by_contra h
            push Not at h
            have h2 : ucH (ucLev E) (ucI (ucLev E) E) ≤ ucH (ucLev E) (guE c) := (ucG_le_iff _).2 h
            rw [hFy, hfixl] at h2
            exact absurd he'E (not_lt.2 h2)
          have hFy' : QcFixH (ucLev E) (ucI (ucLev E) E) := ⟨_, hfixl, hey⟩
          obtain ⟨-, -, hpy⟩ := qc_fpH_mem hne hFy'
          obtain ⟨hgp, -⟩ := hgF hFy'
          have hep : guE c ≤ qcFpH (ucLev E) (ucI (ucLev E) E) := le_csSup ⟨_, fun _ h => h.2.le⟩ ⟨hfixl, hey⟩
          have h1 := hlemono _ _ hep (hpy.trans hyE) (by rw [qcG_base' heE hGe he'B]; exact hgQE) (hgp.trans_lt hgx)
          have h2 : vQ (qcFpH (ucLev E) (ucI (ucLev E) E)) x ≤ qcK (ucLev E) (ucI (ucLev E) E) x := by
            unfold qcK; rw [if_pos hFy']; exact le_self_add
          exact (h1.trans h2).trans_lt hKV
        · have h0 : (0 : Ordinal.{0}) < guE c := heE.pos
          have hex : ∃ d ∈ ucComps (ucLev E), guE c ≤ d := by
            by_contra hcon
            push Not at hcon
            exact hCe ((ucC_lt_iff h0 _).2 hcon)
          obtain ⟨d, hd, hed⟩ := hex
          obtain ⟨hdE, hgd'⟩ := hcomp d hd
          exact (hlemono _ _ hed hdE (by rw [qcG_base' heE hGe he'B]; exact hgQE) hgd').trans_lt (hcompV d hd)
    · -- an atom `Γ(j)` past its segment base: the index reading is below the reading
      rw [qcA_atom' he'B hAc hjE', qc_vI heB hjB hjE'.le]
      have hFe : vaFB (guE c) < c := hjB.trans (hjE'.trans_le hec)
      have hgeQ : qcG (guE c) < x := by rw [qcG_base' heE hGe he'B]; exact hgQE
      have hgF' : qcG (vaFB (guE c)) < x := (qc_FB_gate' heB he'B).trans_lt (max_lt hωx hgeQ)
      have hgj : qcG (yhJ (guE c)) < x := by
        rw [qcQE_atom' he'B hAc hjE'] at hgQE; exact qcG_of_Q hωx hgQE
      have hgo := (qc_off_gate' (vs_FB_E heB) (va_G_le_BG.trans (vs_FB_ge heB)) (hjE'.trans he'B) hjB).trans_lt
        (max_lt hωx hgj)
      have ho : yhJ (guE c) - (vaFB (guE c) + 1) < c := (Ordinal.sub_le_self _ _).trans_lt (hjE'.trans_le hec)
      have hI : vQ (vaFB (guE c)) x + vQ (yhJ (guE c) - (vaFB (guE c) + 1)) x < qcA E x :=
        (inE_indec hVE).add_lt (IH _ hFe (hFe.trans hc) hgF') (IH _ ho (ho.trans hc) hgo)
      exact hcl _ (vz_T_down hx hx1 hVT hV1 hI.le) hI
    · have hGe' : gcG 0 < guE c := lt_of_le_of_ne hGe fun h => hnA (h ▸ yhAt_gcG 0)
      rw [qcA_psi'' heE hGe' he'B hnA]
      have hK := yh_lev_lt hGc hnA
      have hI := yh_idx_lt hGc hnA
      rw [qcQE_psi' heE hGe' he'B hnA] at hgQE
      exact hglA _ _ (IH _ hK (hK.trans hc) (qcG_of_Q hωx ((le_max_left _ _).trans_lt hgQE)))
        (IH _ hI (hI.trans hc) (qcG_of_Q hωx ((le_max_right _ _).trans_lt hgQE)))
  rw [vQ_dec' hGc hcB x]
  exact (inE_indec hVE).add_lt (InE.mul_lt hVE (zm_opow_lt hVE hA' (IH _ hlog (hlog.trans hc) hgk))
    (IH _ hdiv (hdiv.trans hc) hgd)) (IH _ hmod (hmod.trans hc) hgr)

end Fix

end Googology.Trans.PoR.InaccPsi.R2.Qc
