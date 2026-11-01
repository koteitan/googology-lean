import Googology.Trans.PoR.InaccPsi.R2.XlFr

/-!
# XlK: THE LEVEL STEP `G + κ → G + κ + 1` (EVERY `1 ≤ κ < Ω₁`): THE BOTTOM BASE AND THE TRANSFER OF STARTS

The level `G + κ` (`κ ≥ 1`) is not strongly critical (`G + κ < φ(G + κ, 0)`, `xl_lt_veb0`), so its offsets start at
`φ(G + κ, 0)` itself (shift `e = 0`): the stage at the offset `λ` is `φ(G + κ, λ)`, read
`ϑˣ(Ω₁·(Γ_{x+1}+κ) + λ(x)) = φ(Γ_{x+1}+κ, λ(x))` (`xl_glAv`).

* `xlBK κ` (**THE BOTTOM BASE OF THE LEVEL `G + κ`**: shift `0`, reading gate `κ`, low field `xlZs`);
* `XlAt κ U` (**`U` IS A SYSTEM AT THE BOTTOM `φ(G + κ, 0)`**: bound, index, gate `κ`, base reading
  `φ(Γ_{x+1}+κ, 0)`, bound field), `xl_start_of_at` (**A SYSTEM AT `φ(G+κ, 0)` STARTS THE BOTTOM RECURSION OF THE
  LEVEL `G + κ`**), `xl_at_top` (**THE TOP OF THE LEVEL `G + κ` IS A SYSTEM AT `φ(G+κ+1, 0)`**), `xl_at_G`
  (`Xl.xlTop` is a system at `φ(G+1, 0)`).

No new axiom.  New definitions: `xlBK`, `XlAt`.
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
open Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt

open Googology.Trans.PoR.InaccPsi.R2.Xf

namespace Googology.Trans.PoR.InaccPsi.R2.Xl

/-! ## Readings at a level that is not strongly critical -/

/-- **`ϑˣ(Ω₁·α + t) = φ(α, t)`** below `N_α(0)` at a level `α < φ(α, 0)` (`α ≥ x`). -/
theorem xl_glAv {x α : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hα1 : 1 ≤ α) (hαq : α < gq 1 x) (hxα : x ≤ α)
    (hαv : α < veblen α 0) (hNq : hcN α 0 < gq 1 x) : ∀ t, t < hcN α 0 → glA α t x = veblen α t := by
  obtain ⟨hαT, hα1'⟩ := gm1_T hx hx1 hαq
  intro t
  induction t using WellFoundedLT.induction with
  | ind t IH =>
  intro ht
  obtain ⟨htT, ht1⟩ := gm1_T hx hx1 (ht.trans hNq)
  obtain ⟨i, hi⟩ := glA_P hx hx1 hα1 hαT hα1' htT ht1
  have hαu : α < veblen α t := hαv.trans_le ((isNormal_veblen α).monotone zero_le)
  have htu : t < veblen α t := by have := xl_jeg_lt 0 ht; rwa [Nat.cast_zero, zero_add] at this
  apply le_antisymm
  · refine glA_min hx hx1 hα1 hαT hα1' htT ht1 ⟨t, rfl⟩ (hxα.trans_lt hαu) htu hαu (fun σ hσ => ?_)
    rw [IH σ hσ (hσ.trans ht)]
    exact (isNormal_veblen _).strictMono hσ
  · rw [← hi]
    apply (isNormal_veblen _).monotone
    refine le_of_forall_lt (fun s hs => ?_)
    obtain ⟨hsT, -⟩ := gm1_T hx hx1 ((hs.trans ht).trans hNq)
    have h := glA_lt_of hx hx1 hα1 hαT hα1' hsT htT ht1 hs
    rw [IH s hs (hs.trans ht), ← hi] at h
    exact (isNormal_veblen α).strictMono.lt_iff_lt.1 h

/-- **`a + b < φ(a + b, 0)`** when `0 < b < a + b` (`a + b` is not additively principal). -/
theorem xl_lt_veb0 {a b : Ordinal.{0}} (hb : 0 < b) (hba : b < a + b) : a + b < veblen (a + b) 0 := by
  rcases (left_le_veblen (a + b) 0).lt_or_eq with h | h
  · exact h
  · exfalso
    have hE : InE (a + b) := by
      have := gg_veblen_eps (x := a + b) (y := 0) (hb.trans hba).ne'
      rwa [← h] at this
    have hab : a < a + b := by simpa using (add_lt_add_iff_left a).2 hb
    exact lt_irrefl _ ((inE_indec hE).add_lt hab hba)

/-- `N_α(0) < N_{α+1}(0)`. -/
theorem xl_N_lt_N (α : Ordinal.{0}) : hcN α 0 < hcN (α + 1) 0 := by
  rw [xl_N_eq α]
  have h := (isNormal_veblen (α + 1)).strictMono (hcN_E (α + 1) 0).pos
  rwa [hcN_fix] at h

theorem xl_lκ_lt_veb0 {x κ : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (h1 : 1 ≤ κ) (hκx : κ < x) :
    xfLv.l x + κ < veblen (xfLv.l x + κ) 0 := by
  refine xl_lt_veb0 (zero_lt_one.trans_le h1) ?_
  rw [xf_l hx hx1]
  exact hκx.trans ((lgG_facts hx hx1).2.1.trans_le le_self_add)

theorem xl_Nκ_lt1 {x κ : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hκx : κ < x) :
    hcN (xfLv.l x + κ) 0 < gq 1 x :=
  he_N_lt1 hx hx1 ((ev_isSuccLimit_of_inE (gm1_facts hx hx1).2.2.2).add_one_lt (hnv_q xfLv hx hx1 hκx))
    (gm1_facts hx hx1).2.2.2.pos

theorem xl_G1κ_lt {κ : Ordinal.{0}} (hκ : κ < Om1) : gcG 0 + κ + 1 < gcG 1 := by
  have hE := Low.opow_eq_self_of_SC (gcG_SC 1)
  exact (ev_isSuccLimit_of_inE hE).add_one_lt ((inE_indec hE).add_lt (gcG_lt zero_lt_one)
    (hκ.trans (gl_Om1_lt_G0.trans (gcG_lt zero_lt_one))))

/-! ## The low field of the levels `G + κ` -/

/-- **The common low field of the levels `G + κ`**: `φ(ℓ(x) + x + 1, 0)` (`x` read as `max(ω, x)`). -/
noncomputable def xlZs (x : Ordinal.{0}) : Ordinal.{0} := veblen (xfLv.l (max ω x) + max ω x + 1) 0

theorem xlZs_eq {x : Ordinal.{0}} (hx : InE x) : xlZs x = veblen (xfLv.l x + x + 1) 0 := by
  unfold xlZs; rw [max_eq_right (omega0_lt_inE hx).le]

theorem xl_two_lt_Zs (x : Ordinal.{0}) : (2 : Ordinal.{0}) < xfLv.l (max ω x) + max ω x + 1 :=
  ((show (2 : Ordinal.{0}) < ω from (by exact_mod_cast natCast_lt_omega0 2)).trans_le
    (((le_max_left ω x).trans (xfLv.l_ge _)).trans le_self_add)).trans (lt_add_one _)

theorem xlZs_fix (x : Ordinal.{0}) : veblen 2 (xlZs x) = xlZs x := veblen_veblen_of_lt (xl_two_lt_Zs x) 0

theorem xlZs_fix1 (x : Ordinal.{0}) : veblen 1 (xlZs x) = xlZs x :=
  veblen_veblen_of_lt (one_lt_two.trans (xl_two_lt_Zs x)) 0

theorem xlZs_G1 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : xlZs x < gq 1 x := by
  rw [xlZs_eq hx, ← xl_N_eq]
  have hq := (gm1_facts hx hx1).2.2.2
  exact he_N_lt1 hx hx1 ((ev_isSuccLimit_of_inE hq).add_one_lt ((inE_indec hq).add_lt (xfLv.l_lt x hx hx1)
    (gm1_facts hx hx1).2.1)) hq.pos

/-- Below a base `x`, every level `G + κ'` with `κ' < x` has its bottom below the low field. -/
theorem xl_veb_lt_Zs {x κ : Ordinal.{0}} (hx : InE x) (hκx : κ < x) : veblen (xfLv.l x + κ) 0 < xlZs x := by
  rw [xlZs_eq hx]
  exact veblen_zero_lt_veblen_zero.2 (((add_lt_add_iff_left _).2 hκx).trans (lt_add_one _))

/-! ## The bottom base of the level `G + κ` -/

/-- **THE BOTTOM BASE OF THE LEVEL `G + κ`** (`1 ≤ κ < Ω₁`): shift `0`, reading gate `κ`, low field `xlZs`. -/
noncomputable def xlBK (κ : Ordinal.{0}) (h1 : 1 ≤ κ) (hκ : κ < Om1) : XlB xfLv κ where
  e := 0
  γN := κ
  Zo := xlZs
  lv := hκ
  lvN := le_rfl
  lg := by rw [xfLv_g]; exact h1
  γN_lt := hκ
  G_lt := by
    show gcG 0 < veblen (gcG 0 + κ) ((0 : ℕ) : Ordinal.{0})
    rw [Nat.cast_zero]
    exact (by simpa using (add_lt_add_iff_left (gcG 0)).2 (zero_lt_one.trans_le h1) : gcG 0 < gcG 0 + κ).trans_le
      (left_le_veblen _ 0)
  N_lt1 := by
    show hcN (gcG 0 + κ) 0 < gcG 1
    rw [xl_N_eq]
    have h := (isNormal_veblen (gcG 0 + κ + 1)).strictMono (gcG_SC 1).1
    rwa [gn_veb_fix (gcG_SC 1) (xl_G1κ_lt hκ)] at h
  N_mem := fun S _ _ ha hb => by
    rw [xl_N_eq]
    exact CSet.phi_mem (CSet.succ_mem (hnv_L_mem xfLv S ha (by rw [xfLv_g]; exact h1.trans_lt hb) hb))
      (CSet.zero_mem _ _)
  N_cl := fun Z hZ hZ1 h => by
    rw [xl_N_eq, add_assoc] at h
    have hκ1 : κ + 1 < Om1 := gl_Om1_lim.add_one_lt hκ
    have hGQ : gcG 0 < veblen (xfLv.L + (κ + 1)) 0 :=
      (by simpa using (add_lt_add_iff_left (gcG 0)).2 (zero_lt_one.trans_le le_add_self) :
        gcG 0 < gcG 0 + (κ + 1)).trans_le (left_le_veblen _ 0)
    have h2 := hnv_cl_gate xfLv hκ1 hZ hZ1 veblen_pos hGQ h le_rfl
      ((isNormal_veblen _).strictMono (show (0 : Ordinal.{0}) < 0 + 1 by rw [zero_add]; exact zero_lt_one))
    exact (lt_add_one κ).trans h2
  γN_cl := fun _ _ _ h _ => h
  Zo_fix := xlZs_fix
  Zo_G1 := fun _ hx hx1 => xlZs_G1 hx hx1
  read := fun {x} hx hx1 hγ t ht => by
    rw [Nat.cast_zero, zero_add]
    exact xl_glAv hx hx1 (hnv_one xfLv hx hx1 hγ) (hnv_q xfLv hx hx1 hγ) (hnv_xl xfLv hx hx1)
      (xl_lκ_lt_veb0 hx hx1 h1 hγ) (xl_Nκ_lt1 hx hx1 hγ) t ht
  N_pi := fun hB hγ => xl_N_pi_gen xfLv hB (by rw [xfLv_g]; exact h1.trans_lt hγ) hγ

theorem xlBK_e (κ : Ordinal.{0}) (h1 : 1 ≤ κ) (hκ : κ < Om1) : (((xlBK κ h1 hκ).e : ℕ) : Ordinal.{0}) = 0 :=
  Nat.cast_zero

/-! ## Systems at the bottom `φ(G + κ, 0)` -/

/-- **`U` IS A SYSTEM AT THE BOTTOM `φ(G + κ, 0)` OF THE LEVEL `G + κ`.** -/
structure XlAt (κ : Ordinal.{0}) (U : HgVD) : Prop where
  B : U.B = veblen (xfLv.L + κ) 0
  ix : U.ix = veblen (xfLv.L + κ) 0
  γ : ∀ x, InE x → x < Om1 → (U.γ < x ↔ κ < x)
  b : ∀ x, InE x → x < Om1 → κ < x → U.b x = veblen (xfLv.l x + κ) 0
  γ_le : U.γ ≤ κ
  Z : ∀ x, InE x → x < Om1 → U.Z x = if κ < x then evZ (veblen (xfLv.l x + κ) 0) else xlZs x

/-- **A SYSTEM AT `φ(G + κ, 0)` STARTS THE BOTTOM RECURSION OF THE LEVEL `G + κ`.** -/
theorem xl_start_of_at {κ : Ordinal.{0}} (h1 : 1 ≤ κ) (hκ : κ < Om1) {U : HgVD} (hU : XlAt κ U) :
    XlStart (xlBK κ h1 hκ) U where
  B := by rw [hU.B, xlBK_e, add_zero]
  Zb := fun x hx hx1 => by
    rw [hU.Z x hx hx1]
    by_cases h : κ < x
    · rw [if_pos h, (xlBK κ h1 hκ).Zl_eq hx h, xl_N_eq]
      have h2 : (2 : Ordinal.{0}) < xfLv.l x + κ + 1 :=
        ((show (2 : Ordinal.{0}) ≤ ω from (by exact_mod_cast (natCast_lt_omega0 2).le)).trans
          (hnv_ωl xfLv hx hx1).le).trans_lt (lt_add_one _)
      exact (hb_evZ_lt_fix2 (veblen_veblen_of_lt h2 0) (veblen_zero_lt_veblen_zero.2 (lt_add_one _))).le
    · rw [if_neg h, (xlBK κ h1 hκ).Zl_low h]; rfl
  st := fun h2 hZ => by
    refine ⟨?_, fun x hx hx1 => ?_, fun x hx hx1 hg => ?_, fun x hx hx1 => ?_⟩
    · show U.ix = veblen (xfLv.L + κ) ((xlBK κ h1 hκ).e + 0)
      rw [hU.ix, xlBK_e, add_zero]
    · show U.γ < x ↔ max κ (U.g 0) < x
      rw [U.g_zero, max_eq_left zero_le]; exact hU.γ x hx hx1
    · have hκx : κ < x := (max_lt_iff.1 hg).1
      show U.b x = glA (xfLv.l x + κ) (U.R 0 x) x
      rw [U.R_zero, (xlBK κ h1 hκ).read hx hx1 hκx 0 (hcN_E _ _).pos, xlBK_e, add_zero, hU.b x hx hx1 hκx]
    · rw [hU.Z x hx hx1]
      show _ = HgPB.Zst _ x
      by_cases h : κ < x
      · have hg : max κ (U.g 0) < x := by rw [U.g_zero, max_eq_left zero_le]; exact h
        rw [if_pos h, HgPB.Zst_eq _ hg]
        show evZ (veblen (xfLv.l x + κ) 0) = evZ (glA (xfLv.l x + κ) (U.R 0 x) x)
        rw [U.R_zero, (xlBK κ h1 hκ).read hx hx1 h 0 (hcN_E _ _).pos, xlBK_e, add_zero]
      · have hg : ¬ max κ (U.g 0) < x := by rw [U.g_zero, max_eq_left zero_le]; exact h
        rw [if_neg h, HgPB.Zst_low _ hg]
        show xlZs x = (xlBK κ h1 hκ).Zl x
        rw [(xlBK κ h1 hκ).Zl_low h]; rfl

end Googology.Trans.PoR.InaccPsi.R2.Xl
