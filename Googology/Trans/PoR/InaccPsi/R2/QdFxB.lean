import Googology.Trans.PoR.InaccPsi.R2.QdFxA

/-!
# QdFxB: THE FIXED POINT `E = Hᵛ_λ(y)` OF `Γ` IN `[B₂, B₃)` — ITS DATA, PARTS AND READING

As `Qc.QcFxB` with the Veblen levels.  The parts of the reading `ϑˣ(Ω₁·(Ω₁+λ(x)) + K(x))` of every fixed point
`e ∈ [B₂, B₃)` of `Γ` keep its gate (`qd_fix_gates`, by `Qd.qdQEt_fix`).  The reading of `E` is a closed point below a
Veblen-level point; it is under the bound `Qc.YBd` with Lemma IMG at the Veblen levels (`Qd.QdImgH`).

* `qdBd_of_yBd`, `qd_fix_gates`;
* `qd_fx_dat` (**the data of `E`**), `qd_fx_parts` (the parts of the reading), `qd_fx_V` (**the reading of `E`: a
  closed point of `Tˣ ∩ (x, Ω₁)` under `YBd`**).

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
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Qc

theorem qdBd_of_yBd {x v : Ordinal.{0}} (h : YBd x v) : QdBd x v := by
  rcases h with h | ⟨-, h⟩
  · exact qdBd_of_qc h
  · exact h

variable (S : InaccSeq.{0})

include S in
/-- **The parts of the reading of a fixed point `e ∈ [B₂, B₃)` of `Γ` keep its gate.** -/
theorem qd_fix_gates {e : Ordinal.{0}} (hA : YhAt e) (hi : ¬ yhJ e < e) (hX : ucB ≤ e) (hB : e < qdB) :
    (∀ d ∈ qdComps (qdLev e), qdGt d ≤ max ω (qdQEt e)) ∧
      (QdFixH (qdLev e) (qdI (qdLev e) e) →
        qdGt (qdFpH (qdLev e) (qdI (qdLev e) e)) ≤ max ω (qdQEt e) ∧
          qdGt (qdI (qdLev e) e - (qdFpH (qdLev e) (qdI (qdLev e) e) + 1)) ≤ max ω (qdQEt e)) ∧
      (¬ QdFixH (qdLev e) (qdI (qdLev e) e) → qdGt (qdI (qdLev e) e) ≤ max ω (qdQEt e)) := by
  obtain ⟨-, -, hc, hN, -, -⟩ := qd_fix_data S hA hi hX hB
  have hQ := qdQEt_fix hX hB hA hi hN
  have he0 : (0 : Ordinal.{0}) < e := (show InE e from Low.opow_eq_self_of_SC hA.1).pos
  refine ⟨fun d hd => ?_, fun hF => ?_, fun hF => ?_⟩
  · have hde : d < e := (qdFold_lt_iff he0 _).1 hc d hd
    have h1 : qdQt d ≤ qdQEt e := by
      rw [hQ]
      refine (le_of_eq ?_).trans ((qd_fold_ge _ _ d hd).trans (le_max_left _ _))
      rw [if_pos hde]
    calc qdGt d ≤ max ω (qdGt d) := le_max_right _ _
      _ = max ω (qdQt d) := qd_maxQ le_rfl d
      _ ≤ max ω (qdQEt e) := max_le_max le_rfl h1
  · have hK : qdKQ (qdLev e) (qdI (qdLev e) e) ≤ qdQEt e := by rw [hQ]; exact le_max_right _ _
    unfold qdKQ at hK
    rw [if_pos hF] at hK
    refine ⟨?_, ?_⟩
    · calc qdGt _ ≤ max ω (qdGt _) := le_max_right _ _
        _ = max ω (qdQt _) := qd_maxQ le_rfl _
        _ ≤ max ω (qdQEt e) := max_le_max le_rfl ((le_max_left _ _).trans hK)
    · calc qdGt _ ≤ max ω (qdGt _) := le_max_right _ _
        _ = max ω (qdQt _) := qd_maxQ le_rfl _
        _ ≤ max ω (qdQEt e) := max_le_max le_rfl ((le_max_right _ _).trans hK)
  · have hK : qdKQ (qdLev e) (qdI (qdLev e) e) ≤ qdQEt e := by rw [hQ]; exact le_max_right _ _
    unfold qdKQ at hK
    rw [if_neg hF] at hK
    calc qdGt _ ≤ max ω (qdGt _) := le_max_right _ _
      _ = max ω (qdQt _) := qd_maxQ le_rfl _
      _ ≤ max ω (qdQEt e) := max_le_max le_rfl hK

/-! ## The fixed point `E` -/

section Fix

variable {E : Ordinal.{0}} (hE : InE E) (hBE : tfBG < E) (hEB : E < qdB) (hXE : ucB ≤ E)
  (hlim : ∀ e, InE e → e < E → eN e < E) (hIH : ∀ e, InE e → tfBG ≤ e → e < E → QdGood e)
  (hA : YhAt E) (hi : ¬ yhJ E < E)
  {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)

include S hA hi hXE hEB in
/-- **The data of the fixed point `E = Hᵛ_λ(y)`.** -/
theorem qd_fx_dat :
    gamma E = E ∧ qdLev E ≠ 0 ∧ qdLev E < qdG2 ∧ qdFold id (qdLev E) < E ∧ qdI (qdLev E) E < E ∧
      qdH (qdLev E) (qdI (qdLev E) E) = E ∧ qdH (qdLev E) (qdI (qdLev E) E) ≠ qdI (qdLev E) E ∧ vaFB E = E := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := qd_fix_data S hA hi hXE hEB
  have hfix := vs_fixatom hA hi
  exact ⟨hfix, h1, h2, h3, h4, h5, h6, vs_FB_self hfix hA.2⟩

include S hE hBE hEB hXE hlim hIH hA hi hx hx1

/-- **The parts of the reading of `E`.** -/
theorem qd_fx_parts (hgx : max ω (qdQEt E) < x) :
    (∀ d ∈ qdComps (qdLev E), d < E ∧ qdGt d < x) ∧ 1 ≤ qdLvx E (qdLev E) x ∧
      Om1 + qdLvx E (qdLev E) x < ggGam ∧ tfDat (Om1 + qdLvx E (qdLev E) x) ∈ Tset x ∧
      qdRK (qdLev E) (qdI (qdLev E) E) x ∈ Tset x ∧ qdRK (qdLev E) (qdI (qdLev E) E) x < Om1 ∧
      YBd x (max (tfDat (Om1 + qdLvx E (qdLev E) x)) (qdRK (qdLev E) (qdI (qdLev E) E) x)) := by
  obtain ⟨-, hl0, hlG, hlc, hyc, -, hne, -⟩ := qd_fx_dat S hEB hXE hA hi
  obtain ⟨hgcomp, hgF, hg0⟩ := qd_fix_gates S hA hi hXE hEB
  have hcode : ∀ c, c < E → qdGt c < x → vD c x ∈ Tset x ∧ vD c x < Om1 := fun c hc hgc =>
    ⟨(qd_T S hE hBE hEB hlim hIH hx hx1 hc hgc).1, (qd_T S hE hBE hEB hlim hIH hx hx1 hc hgc).2.1⟩
  have hmono : ∀ b c, b < c → c < E → qdGt b < x → qdGt c < x → vD b x < vD c x := fun b c hbc hc hgb hgc =>
    qd_mono S hE hBE hEB hlim hIH hx hx1 hbc hc hgb hgc
  obtain ⟨hL1, hNG, hNT, hKT, hK1⟩ := qd_fix_lev S hx hx1 hA hi hXE hEB hgx hcode hmono
  have hE0 : (0 : Ordinal.{0}) < E := hE.pos
  have hcomp : ∀ d ∈ qdComps (qdLev E), d < E ∧ qdGt d < x := fun d hd =>
    ⟨(qdFold_lt_iff hE0 _).1 hlc d hd, (hgcomp d hd).trans_lt hgx⟩
  -- the data of the level is at most the largest reading of a leaf
  set f : Ordinal.{0} → Ordinal.{0} := fun d => if d < E then vD d x else 0 with hfdef
  have hf0 : f 0 = 0 := by simp only [hfdef, if_pos hE0, vD_zero]
  have hD0 : (fun d => d < E ∧ qdGt d < x) 0 := ⟨hE0, by rw [qdGt_zero]; exact hx.pos⟩
  have hfΩ : ∀ d, (fun d => d < E ∧ qdGt d < x) d → f d < Om1 := fun d hd => by
    simp only [hfdef, if_pos hd.1]; exact (hcode d hd.1 hd.2).2
  have hfm : ∀ d d', (fun d => d < E ∧ qdGt d < x) d → (fun d => d < E ∧ qdGt d < x) d' → d < d' →
      f d < f d' := fun d d' hd hd' hdd => by
    simp only [hfdef, if_pos hd.1, if_pos hd'.1]; exact hmono d d' hdd hd'.1 hd.2 hd'.2
  obtain ⟨hLG, hLdat, -, -, -, -⟩ := qdLv_main f (fun d => d < E ∧ qdGt d < x) hf0 hD0 hfΩ hfm _ hlG hcomp
  have hlx : qdLvx E (qdLev E) x = qdLv f (qdLev E) := rfl
  have hdatle : tfDat (Om1 + qdLvx E (qdLev E) x) ≤ qdFold f (qdLev E) := by
    rw [hlx, tfDat_eq_ss _ (tf_Om1_add_lt_gg hLG), qd_ssDat_Om1_add (hlx ▸ hL1) hLG]
    exact hLdat
  have hfold : YBd x (qdFold f (qdLev E)) := yBd_fold hx hx1 f _ fun d hd => by
    obtain ⟨hdE, hgd⟩ := hcomp d hd
    simp only [hfdef, if_pos hdE]
    exact (qd_T S hE hBE hEB hlim hIH hx hx1 hdE hgd).2.2
  have hKbd : YBd x (qdRK (qdLev E) (qdI (qdLev E) E) x) := by
    unfold qdRK
    split_ifs with hF
    · obtain ⟨-, -, hpy⟩ := qd_fpH_mem hne hF
      obtain ⟨hgp, hgo⟩ := hgF hF
      exact yBd_add hx hx1 (qd_T S hE hBE hEB hlim hIH hx hx1 (hpy.trans hyc) (hgp.trans_lt hgx)).2.2
        (qd_T S hE hBE hEB hlim hIH hx hx1 ((Ordinal.sub_le_self _ _).trans_lt hyc) (hgo.trans_lt hgx)).2.2
    · exact (qd_T S hE hBE hEB hlim hIH hx hx1 hyc ((hg0 hF).trans_lt hgx)).2.2
  exact ⟨hcomp, hL1, hNG, hNT, hKT, hK1, yBd_max (yBd_mono hdatle hfold) hKbd⟩

/-- **The reading of the fixed point**: a closed point of `Tˣ ∩ (x, Ω₁)` under `YBd` (with Lemma IMG at the Veblen
levels). -/
theorem qd_fx_V (hI : QdImgH) (hgx : max ω (qdQEt E) < x) :
    qdA E x = vt x (Om1 * (Om1 + qdLvx E (qdLev E) x) + qdRK (qdLev E) (qdI (qdLev E) E) x) ∧
      YwClosed x (qdA E x) ∧ qdA E x ∈ Tset x ∧ InE (qdA E x) ∧ x < qdA E x ∧ YBd x (qdA E x) ∧
      qdA E x < Om1 := by
  obtain ⟨-, hL1, hNG, hNT, hKT, hK1, hbd⟩ := qd_fx_parts S hE hBE hEB hXE hlim hIH hA hi hx hx1 hgx
  have heq := qdA_fix S hA hi hXE hEB x
  have hcl := qd_fix_cl S hx hx1 hA hi hXE hEB hgx
    (fun c hc hgc => ⟨(qd_T S hE hBE hEB hlim hIH hx hx1 hc hgc).1, (qd_T S hE hBE hEB hlim hIH hx hx1 hc hgc).2.1⟩)
    (fun b c hbc hc hgb hgc => qd_mono S hE hBE hEB hlim hIH hx hx1 hbc hc hgb hgc)
  have hO1 : Om1 ≤ Om1 + qdLvx E (qdLev E) x := le_self_add
  have hargT := tfArg_mem hx hx1 hO1 (hNG.trans tf_gg_lt_BG) hNT hKT hK1
  have harg2 := qd_arg_lt hNG hK1
  obtain ⟨hvT, -, hv1, -, -⟩ := vt_memTwo hx hx1 hargT harg2
  obtain ⟨hxv, hvE⟩ := (vt_E_iff hx hx1 hargT harg2).2 (le_mul_of_one_le_right' (one_le_iff_ne_zero.2
    (by intro h; rw [h] at hO1; exact absurd (Rj.rj_Om1_pos) (not_lt.2 hO1))) |>.trans le_self_add)
  rw [heq] at hcl ⊢
  exact ⟨rfl, hcl, hvT, hvE, hxv,
    yBd_of_qd hI (qdBd_vt hx hx1 hNG hNT hKT hK1 (qdBd_of_yBd hbd)), hv1⟩

end Fix

end Googology.Trans.PoR.InaccPsi.R2.Qd
