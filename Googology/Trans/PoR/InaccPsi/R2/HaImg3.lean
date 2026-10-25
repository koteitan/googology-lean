import Googology.Trans.PoR.InaccPsi.R2.HaImgP

/-!
# HaImg3: LEMMA IMG AT EVERY POINT OF VEBLEN LEVEL 3 AND BELOW `B₄(ρ) = φ(4, Γ_{ρ+1}+1)`

Level 3 as level 2 was done in `R2.GzImg`, now with the generic tools of `R2.HaImg` / `R2.HaImgP`:

* `ha_haN_veb3` (**`N(φ(3, a)) = φ(3, a + 1)`**), `ha_floor3`, `ha_glA3V` (**`ϑˣ(Ω₁·3 + Γ_{x+1} + ν) = φ(3, i₃ + ν)`**,
  `φ(3, i₃) = B₃(x)`, as long as no `φ(3,·)`-fixed point is passed), `haB4` (**`B₄(x)`**, the least fixed point of
  `φ(3, ·)` above `B₃(x)`), `haB4_lt1` (`B₄(x) < Γ_{x+2}`), `ha_nofix_B4`;
* `ha_down_Pall` (**the reach test on all of `(P, N(P))`**, `P` a fixed point of `φ(2, ·)`), `ha_img_N3` (**LEMMA IMG AT
  `ϑᵖ(Ω₁·3 + t + 1) = N(ϑᵖ(Ω₁·3 + t))`** for every `t`), `haI_limZ3` (**LEMMA IMG AT A LIMIT POINT `φ(3, i₃ + c)` OF
  LEVEL 3**: the reach test going down at level `3`; a level-3 point `φ(3, i₃ + d)`, `c' < d < c = c' + ω^z`, has
  reach `u·4 + ζ` with `ζ ≤ lg d < z`), `ha_img_B4` (**LEMMA IMG FOR EVERY VALUE BELOW `B₄(ρ)`**), `ha_pkg_B4`.

No new axiom.  New definition: `haB4`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ha

open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

theorem ha_two_lt_3 : (2 : Ordinal.{0}) < 3 := by
  rw [← ha_two_add_one]; exact lt_add_one 2

theorem ha_fix2_veb3 (a : Ordinal.{0}) : veblen 2 (veblen 3 a) = veblen 3 a := veblen_veblen_of_lt ha_two_lt_3 a

/-- **`N(φ(3, a)) = φ(3, a + 1)`**: the least fixed point of `φ(2, ·)` above `evZ(φ(3, a))`. -/
theorem ha_haN_veb3 (a : Ordinal.{0}) : haN (veblen 3 a) = veblen 3 (a + 1) := by
  have hfa := ha_fix2_veb3 a
  have hfa1 := ha_fix2_veb3 (a + 1)
  have hlt : veblen 3 a < veblen 3 (a + 1) := (isNormal_veblen 3).strictMono (lt_add_one a)
  refine le_antisymm ?_ ?_
  · have hZ : evZ (veblen 3 a) ≤ veblen 3 (a + 1) := evZ_le hlt (ha_fix1_of_fix2 hfa1)
    have hne : evZ (veblen 3 a) ≠ veblen 3 (a + 1) := fun e => ha_evZ_notfix hfa (by rw [e]; exact hfa1)
    exact ha_fix_ge_N hfa1 (lt_of_le_of_ne hZ hne)
  · obtain ⟨b, hb⟩ := ha_LuP3_of_fix2 (haN_fix (veblen 3 a))
    have hab : veblen 3 a < veblen 3 b := by rw [hb]; exact (lt_evZ _).trans (haN_gt _)
    rw [← hb]
    exact (isNormal_veblen 3).monotone (Order.add_one_le_of_lt ((isNormal_veblen 3).strictMono.lt_iff_lt.1 hab))

/-- Every ordinal above a point of level `3` lies in some `[φ(3, j), φ(3, j+1))`. -/
theorem ha_floor3 {u j0 : Ordinal.{0}} (h0 : veblen 3 j0 ≤ u) : ∃ j, veblen 3 j ≤ u ∧ u < veblen 3 (j + 1) := by
  have hne : ({j | u < veblen 3 j} : Set Ordinal.{0}).Nonempty :=
    ⟨u + 1, (lt_add_one u).trans_le (right_le_veblen 3 _)⟩
  have hmS : u < veblen 3 (sInf {j | u < veblen 3 j}) := csInf_mem hne
  have hmin : ∀ j, j < sInf {j | u < veblen 3 j} → veblen 3 j ≤ u := fun j hj =>
    not_lt.1 (fun h => absurd (csInf_le' (s := {j | u < veblen 3 j}) h) (not_le.2 hj))
  rcases zero_or_succ_or_isSuccLimit (sInf {j | u < veblen 3 j}) with h0' | ⟨j, hj⟩ | hlim
  · exfalso
    rw [h0'] at hmS
    exact absurd (((isNormal_veblen 3).monotone zero_le).trans h0) (not_le.2 hmS)
  · have hj' : sInf {j | u < veblen 3 j} = j + 1 := by rw [← hj, Order.succ_eq_add_one]
    exact ⟨j, hmin j (by rw [hj']; exact lt_add_one j), by rw [← hj']; exact hmS⟩
  · exfalso
    obtain ⟨a, ha, hua⟩ := ((isNormal_veblen 3).lt_iff_exists_lt hlim).1 hmS
    exact absurd (hmin a ha) (not_le.2 hua)

/-- **`B₄(x)`**, the least fixed point of `φ(3, ·)` above `B₃(x)` (`= φ(4, Γ_{x+1} + 1)`). -/
noncomputable def haB4 (x : Ordinal.{0}) : Ordinal.{0} := nfp (veblen 3) (gzB3 x + 1)

theorem haB4_fix (x : Ordinal.{0}) : veblen 3 (haB4 x) = haB4 x := nfp_fp (isNormal_veblen 3) _

theorem haB3_lt_B4 (x : Ordinal.{0}) : gzB3 x < haB4 x := (lt_add_one _).trans_le (le_nfp _ _)

theorem ha_fix_ge_B4 {x j : Ordinal.{0}} (hj : veblen 3 j = j) (hBj : gzB3 x < j) : haB4 x ≤ j :=
  nfp_le_fp (isNormal_veblen 3).strictMono.monotone (Order.add_one_le_of_lt hBj) hj.le

theorem haB4_fix2 (x : Ordinal.{0}) : veblen 2 (haB4 x) = haB4 x := by
  have h := ha_fix2_veb3 (haB4 x); rwa [haB4_fix] at h

theorem ha_three_add_one : (3 : Ordinal.{0}) + 1 = 4 := by
  have : ((3 : ℕ) : Ordinal.{0}) + 1 = ((4 : ℕ) : Ordinal.{0}) := by push_cast; rfl
  exact_mod_cast this

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **`B₃(x)` is not a fixed point of `φ(3, ·)`** (`B₃(x) = ϑˣ(Ω₁·3 + Γ_{x+1})` has Veblen level exactly `3`). -/
theorem ha_B3_notfix3 : veblen 3 (gzB3 x) ≠ gzB3 x := by
  intro e
  have hq := (gm1_facts hx hx1).2.2.2
  have h3q : (3 : Ordinal.{0}) < gq 1 x := (natCast_lt_omega0 3).trans (omega0_lt_inE hq)
  obtain ⟨h3T, h31⟩ := gm1_T hx hx1 h3q
  obtain ⟨hGT, -, hG1, -, -⟩ := lgG_facts hx hx1
  have h13 : (1 : Ordinal.{0}) ≤ 3 := by norm_num
  refine glA_notP hx hx1 h13 h3T h31 hGT hG1 ?_
  rw [ha_B3_eq hx hx1, ha_three_add_one]
  unfold LuP
  rw [mem_range_veblen four_ne_zero]
  intro b hb
  rcases lt_or_ge b 3 with hb3 | hb3
  · have h := veblen_veblen_of_lt hb3 (gzB3 x); rwa [e] at h
  · have : b = 3 := le_antisymm (Order.lt_add_one_iff.1 (by rw [ha_three_add_one]; exact hb)) hb3
    rw [this]; exact e

/-- **`B₄(x) < Γ_{x+2}`**: `ϑˣ(Ω₁·4 + Γ_{x+1})` is a fixed point of `φ(3, ·)` above `B₃(x)`, below `Γ_{x+2}`. -/
theorem haB4_lt1 : haB4 x < gq 1 x := by
  obtain ⟨hGT, -, hG1, -, -⟩ := lgG_facts hx hx1
  have hq := (gm1_facts hx hx1).2.2.2
  have h4q : (4 : Ordinal.{0}) < gq 1 x := (natCast_lt_omega0 4).trans (omega0_lt_inE hq)
  obtain ⟨h4T, h41⟩ := gm1_T hx hx1 h4q
  have h3q : (3 : Ordinal.{0}) < gq 1 x := (natCast_lt_omega0 3).trans (omega0_lt_inE hq)
  obtain ⟨h3T, h31⟩ := gm1_T hx hx1 h3q
  have h14 : (1 : Ordinal.{0}) ≤ 4 := by norm_num
  obtain ⟨k, hk⟩ := glA_P hx hx1 h14 h4T h41 hGT hG1
  have hfix3 : veblen 3 (glA 4 (lgG x) x) = glA 4 (lgG x) x := by
    rw [← hk]; exact veblen_veblen_of_lt (by norm_num) k
  have hlt : gzB3 x < glA 4 (lgG x) x := by
    rw [← ha_B3_eq hx hx1]
    exact (glA_lev hx hx1 (by norm_num) (by norm_num) h4T h41 hGT hG1 hGT hG1).2
      (glA_facts hx hx1 h14 h4T h41 hGT hG1).2.2.2.2.2
  exact (ha_fix_ge_B4 hfix3 hlt).trans_lt
    (lgVt_lt_low hx hx1 h4T h41 hGT hG1 (gm1_one_T hx hx1).1 (gm1_one_T hx hx1).2 h4q (mg_lgG_lt_G1 hx hx1))

/-- **`ϑˣ(Ω₁·3 + Γ_{x+1} + ν) = φ(3, i₃ + ν)`** (`φ(3, i₃) = B₃(x)`) for every `ν` with `Γ_{x+1} + ν < Γ_{x+2}` and
no `φ(3,·)`-fixed point `i₃ + ν'`, `ν' ≤ ν` a limit. -/
theorem ha_glA3V {i3 : Ordinal.{0}} (hi3 : veblen 3 i3 = gzB3 x) : ∀ ν, lgG x + ν < gq 1 x →
    (∀ ν', ν' ≤ ν → IsSuccLimit ν' → i3 + ν' < veblen 3 (i3 + ν')) →
    glA 3 (lgG x + ν) x = veblen 3 (i3 + ν) := by
  have hq0 := (gm1_facts hx hx1).2.2.2
  have h3q : (3 : Ordinal.{0}) < gq 1 x := (natCast_lt_omega0 3).trans (omega0_lt_inE hq0)
  obtain ⟨h3T, h31⟩ := gm1_T hx hx1 h3q
  have h13 : (1 : Ordinal.{0}) ≤ 3 := by norm_num
  obtain ⟨hGT, -, hG1, -, -⟩ := lgG_facts hx hx1
  have hPq : lgG x < gq 1 x := mg_lgG_lt_G1 hx hx1
  have hG0 : glA 3 (lgG x) x = veblen 3 i3 := by rw [hi3]; exact ha_B3_eq hx hx1
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hq hfix
  obtain ⟨htT, ht1⟩ := gm1_T hx hx1 hq
  rcases Ordinal.zero_or_succ_or_isSuccLimit ν with h0 | ⟨d, hd⟩ | hlim
  · subst h0; rw [add_zero, add_zero]; exact hG0
  · have hd' : ν = d + 1 := by rw [← succ_eq_add_one]; first | exact hd | exact hd.symm
    subst hd'
    have hdq : lgG x + d < gq 1 x := lt_of_le_of_lt (add_le_add le_rfl le_self_add) hq
    have IHd := IH d (lt_add_one d) hdq (fun ν' h hl => hfix ν' (h.trans le_self_add) hl)
    rw [← add_assoc] at hq ⊢
    rw [ha_glA3_succ hx hx1 hq, IHd, ha_haN_veb3, add_assoc]
  · have hval : ∀ ν'', ν'' < ν → glA 3 (lgG x + ν'') x = veblen 3 (i3 + ν'') := fun ν'' h =>
      IH ν'' h ((add_lt_add_iff_left _).2 h |>.trans hq) (fun ν' h' hl => hfix ν' (h'.trans h.le) hl)
    set u := veblen 3 (i3 + ν) with hu
    have huE : InE u := gg_veblen_eps three_ne_zero
    have hiu : veblen 3 i3 < u := (isNormal_veblen 3).strictMono (lt_add_of_pos_right _ hlim.bot_lt)
    obtain ⟨-, hxa, -, -, h3a, hGa⟩ := glA_facts hx hx1 h13 h3T h31 hGT hG1
    rw [hG0] at hxa h3a hGa
    have htu : lgG x + ν < u := (inE_indec huE).add_lt (hGa.trans hiu)
      ((le_add_self : ν ≤ i3 + ν).trans_lt (hfix ν le_rfl hlim))
    refine le_antisymm ?_ ?_
    · refine glA_min hx hx1 h13 h3T h31 htT ht1 ⟨_, rfl⟩ (hxa.trans hiu) htu (h3a.trans hiu) (fun σ hσ => ?_)
      rcases lt_or_ge σ (lgG x) with hσP | hσP
      · obtain ⟨hσT, hσ1⟩ := gm1_T hx hx1 (hσP.trans hPq)
        have := glA_lt_of hx hx1 h13 h3T h31 hσT hGT hG1 hσP
        rw [hG0] at this
        exact this.trans hiu
      · obtain ⟨ν'', rfl⟩ := exists_add_of_le hσP
        have hν'' : ν'' < ν := (add_lt_add_iff_left _).1 hσ
        rw [hval ν'' hν'']
        exact (isNormal_veblen 3).strictMono ((add_lt_add_iff_left _).2 hν'')
    · refine ((isNormal_veblen 3).le_iff_forall_le (isSuccLimit_add _ hlim)).2 fun c hc => ?_
      rcases lt_or_ge c i3 with hci | hci
      · refine ((isNormal_veblen 3).strictMono hci).le.trans ?_
        rw [← hG0]
        exact (glA_le_iff hx hx1 h13 h3T h31 hGT hG1 htT ht1).2 le_self_add
      · obtain ⟨c', rfl⟩ := exists_add_of_le hci
        have hc' : c' < ν := (add_lt_add_iff_left _).1 hc
        have hq' : lgG x + c' < gq 1 x := ((add_lt_add_iff_left _).2 hc').trans hq
        obtain ⟨hcT, -⟩ := gm1_T hx hx1 hq'
        rw [← hval c' hc']
        exact (glA_lt_of hx hx1 h13 h3T h31 hcT htT ht1 ((add_lt_add_iff_left _).2 hc')).le

/-- Below `B₄(x)` no index `j ≥ i₃` (`φ(3, i₃) = B₃(x)`) is a fixed point of `φ(3, ·)`. -/
theorem ha_nofix_B4 {i3 j : Ordinal.{0}} (hi3 : veblen 3 i3 = gzB3 x) (hij : i3 ≤ j) (hjB : veblen 3 j < haB4 x) :
    j < veblen 3 j := by
  rcases (right_le_veblen 3 j).lt_or_eq with h | h
  · exact h
  · exfalso
    have hBj : gzB3 x ≤ j := by rw [← hi3, h]; exact (isNormal_veblen 3).monotone hij
    have hne : gzB3 x ≠ j := fun e => ha_B3_notfix3 hx hx1 (by rw [e]; exact h.symm)
    have := ha_fix_ge_B4 h.symm (lt_of_le_of_ne hBj hne)
    exact absurd hjB (not_lt.2 (this.trans h.le))

end Base

/-! ## Lemma IMG at level 3 -/

section Img

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **The reach test on all of `(P, N(P))`**, `P ∈ (ρ, Γ_{ρ+2})` a fixed point of `φ(2, ·)`: Veblen level `1` (reach
`u·2 + lg d`) or `2` (reach `u·3 + ζ`, `evZ(P)` included). -/
theorem ha_down_Pall {P u : Ordinal.{0}} (hP : veblen 2 P = P) (hρP : ρ < P) (hNq : haN P < gq 1 ρ) (hu : InE u)
    (hPu : P < u) (huB : u < haN P) :
    ∃ m : ℕ, ∃ ζ, m ≤ 2 ∧ IsLh1 u (u * ((m : Ordinal.{0}) + 1) + ζ) ∧ ζ < u := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hPI : InE P := ha_inE_of_fix2 hP
  have hP1 : P < Om1 := (((lt_evZ P).trans (haN_gt P)).trans hNq).trans (gm1_facts hρE hρ1).2.2.1
  rcases lt_trichotomy u (evZ P) with hlt | heq | hgt
  · obtain ⟨d, hd⟩ := evA_surj hPI hu hPu.le
    have hd0 : d ≠ 0 := by rintro rfl; rw [evA_zero hPI] at hd; exact hPu.ne hd
    have hdZ : d < evZ P := by
      by_contra hge; push Not at hge
      exact absurd (hge.trans ((le_evA_idx P d).trans hd.le)) (not_le.2 hlt)
    have hlhu : IsLh1 u (u * 2 + lg d) := by rw [← hd]; exact gk_lh_evA hPI hP1 hd0 hdZ
    have hld : lg d < u := (lg_le hd0).trans_lt (by rw [← hd]; exact lt_evA_self hPI hdZ)
    refine ⟨1, lg d, by norm_num, ?_, hld⟩
    rw [Nat.cast_one, one_add_one_eq_two]; exact hlhu
  · subst heq
    refine ⟨2, 0, le_rfl, ?_, (evZ_E P).pos⟩
    rw [add_zero, show ((2 : ℕ) : Ordinal.{0}) + 1 = 2 + 1 by norm_num, mul_add_one]
    exact vz_lh_evZ hPI hP1
  · exact ha_down_P h hP hρP hNq hu hgt huB

/-- **LEMMA IMG AT `ϑᵖ(Ω₁·3 + t + 1) = N(ϑᵖ(Ω₁·3 + t))`**, the next point of Veblen level `3`, given Lemma IMG below
it (the reach test going down at level `3`). -/
theorem ha_img_N3 {t : Ordinal.{0}} (ht : t + 1 < gq 1 ρ) (hle : ∀ v, v < glA 3 (t + 1) ρ → GnI ρ δ v) :
    GnI ρ δ (glA 3 (t + 1) ρ) := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have ht' : t < gq 1 ρ := (lt_add_one t).trans ht
  obtain ⟨htT, ht1⟩ := gm1_T hρE hρ1 ht'
  obtain ⟨hsT, hs1⟩ := gm1_T hρE hρ1 ht
  have hq := (gm1_facts hρE hρ1).2.2.2
  have h3q : (3 : Ordinal.{0}) < gq 1 ρ := (natCast_lt_omega0 3).trans (omega0_lt_inE hq)
  obtain ⟨h3T, h31⟩ := gm1_T hρE hρ1 h3q
  have h13 : (1 : Ordinal.{0}) ≤ 3 := by norm_num
  obtain ⟨k, hk⟩ := glA_P hρE hρ1 h13 h3T h31 htT ht1
  have hPf : veblen 2 (glA 3 t ρ) = glA 3 t ρ := by rw [← hk]; exact veblen_veblen_of_lt (by norm_num) k
  obtain ⟨-, hρP, -, -, -, -⟩ := glA_facts hρE hρ1 h13 h3T h31 htT ht1
  have hN : glA 3 (t + 1) ρ = haN (glA 3 t ρ) := ha_glA3_succ hρE hρ1 ht
  have hNq : haN (glA 3 t ρ) < gq 1 ρ := by
    rw [← hN]
    exact lgVt_lt_low hρE hρ1 h3T h31 hsT hs1 (gm1_one_T hρE hρ1).1 (gm1_one_T hρE hρ1).2 h3q ht
  have e3 : glA ((3 : ℕ) : Ordinal.{0}) (t + 1) ρ = glA 3 (t + 1) ρ := by rw [Nat.cast_ofNat]
  have hZN : evZ (glA 3 t ρ) < glA ((3 : ℕ) : Ordinal.{0}) (t + 1) ρ := by rw [e3, hN]; exact haN_gt _
  have H := ha_img_down h (n := 3) (by norm_num) hsT hs1 (hρP.trans (lt_evZ _)) hZN
    (fun u hu hZu huB => by
      rw [e3, hN] at huB
      obtain ⟨m, ζ, hm, hl, hζ⟩ := ha_down_P h hPf hρP hNq hu hZu huB
      exact ⟨m, ζ, hm.trans (by norm_num), hl, hζ, fun e => absurd e (by omega)⟩)
    (fun u hu => hle u (by rw [e3] at hu; exact hu))
  rwa [e3] at H

/-- **LEMMA IMG AT A LIMIT POINT `E = φ(3, i₃ + c)` OF VEBLEN LEVEL 3** (`φ(3, i₃) = B₃(ρ)`, `c` a limit, no
`φ(3,·)`-fixed point `i₃ + ν'`, `ν' ≤ c`), given Lemma IMG below `E`: the reach test going down at level `3` with
`E' = φ(3, i₃ + c')`, `c = c' + ω^z`; a level-3 point `u = φ(3, i₃ + d)` in `(E', E)` has reach `u·4 + ζ` with
`ζ ≤ lg d < z`, every other `ε`-number there has level `1` or `2`. -/
theorem haI_limZ3 {i3 c : Ordinal.{0}} (hi3 : veblen 3 i3 = gzB3 ρ) (hlim : IsSuccLimit c)
    (hq : lgG ρ + c < gq 1 ρ) (hfix : ∀ ν', ν' ≤ c → IsSuccLimit ν' → i3 + ν' < veblen 3 (i3 + ν'))
    (IH : ∀ u, u < veblen 3 (i3 + c) → GnI ρ δ u) : GnI ρ δ (veblen 3 (i3 + c)) := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hc0 : c ≠ 0 := hlim.bot_lt.ne'
  have hEv : glA 3 (lgG ρ + c) ρ = veblen 3 (i3 + c) := ha_glA3V hρE hρ1 hi3 c hq hfix
  set E := veblen 3 (i3 + c) with hEdef
  have hq0 := (gm1_facts hρE hρ1).2.2.2
  have h3q : (3 : Ordinal.{0}) < gq 1 ρ := (natCast_lt_omega0 3).trans (omega0_lt_inE hq0)
  obtain ⟨h3T, h31⟩ := gm1_T hρE hρ1 h3q
  have h13 : (1 : Ordinal.{0}) ≤ 3 := by norm_num
  obtain ⟨htT, ht1⟩ := gm1_T hρE hρ1 hq
  obtain ⟨-, -, -, -, -, htE⟩ := glA_facts hρE hρ1 h13 h3T h31 htT ht1
  rw [hEv] at htE
  have hEq : E < gq 1 ρ := by
    rw [← hEv]
    exact lgVt_lt_low hρE hρ1 h3T h31 htT ht1 (gm1_one_T hρE hρ1).1 (gm1_one_T hρE hρ1).2 h3q hq
  obtain ⟨c', hcs, hdvd, hc'c⟩ := lg_split hc0
  set z := lg c with hzdef
  set E' := veblen 3 (i3 + c') with hE'def
  have hE'E : E' < E := (isNormal_veblen 3).strictMono ((add_lt_add_iff_left _).2 hc'c)
  obtain ⟨hGT, hρG, hG1, -, -⟩ := lgG_facts hρE hρ1
  have hBE' : gzB3 ρ ≤ E' := by rw [← hi3]; exact (isNormal_veblen 3).monotone le_self_add
  have hρE' : ρ < E' := ((hρG.trans (lt_evZ _)).trans (gzZ1_lt_B3 ρ)).trans_le hBE'
  -- `glZeta ρ 3 (Γ_{ρ+1} + c) = lg c`
  have hz' : glZeta ρ 3 (lgG ρ + c) = z := by
    rw [gz_glZeta_eq (lt_of_lt_of_le hlim.bot_lt (le_add_self : c ≤ lgG ρ + c)).ne' ?_, gz_lg_add _ hc0]
    obtain ⟨a, ha, hta⟩ := ((isNormal_veblen 3).lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 htE
    have hc'' : a - i3 < c := by
      rcases lt_or_ge a i3 with hai | hai
      · rw [Ordinal.sub_eq_zero_iff_le.2 hai.le]; exact hlim.bot_lt
      · have : i3 + (a - i3) < i3 + c := by rw [Ordinal.add_sub_cancel_of_le hai]; exact ha
        exact (add_lt_add_iff_left _).1 this
    refine ⟨lgG ρ + (a - i3), (add_lt_add_iff_left _).2 hc'', ?_⟩
    have hq'' : lgG ρ + (a - i3) < gq 1 ρ := ((add_lt_add_iff_left _).2 hc'').trans hq
    have hv : vt ρ (Om1 * ((3 : ℕ) : Ordinal.{0}) + (lgG ρ + (a - i3))) = glA 3 (lgG ρ + (a - i3)) ρ := by
      rw [Nat.cast_ofNat]; rfl
    rw [hv, ha_glA3V hρE hρ1 hi3 _ hq'' (fun ν' h' hl => hfix ν' (h'.trans hc''.le) hl)]
    exact hta.trans_le ((isNormal_veblen 3).monotone (Ordinal.le_add_sub a i3))
  have e3 : glA ((3 : ℕ) : Ordinal.{0}) (lgG ρ + c) ρ = E := by rw [Nat.cast_ofNat]; exact hEv
  have hE'E3 : E' < glA ((3 : ℕ) : Ordinal.{0}) (lgG ρ + c) ρ := by rw [e3]; exact hE'E
  have H := ha_img_down h (n := 3) (by norm_num) htT ht1 hρE' hE'E3 (fun u hu hE'u huE => ?_)
    (fun u hu => IH u (by rw [e3] at hu; exact hu))
  · rwa [e3] at H
  rw [e3] at huE
  obtain ⟨j, hj1, hj2⟩ := ha_floor3 (u := u) (j0 := i3 + c') hE'u.le
  have hcj : i3 + c' ≤ j := by
    have : veblen 3 (i3 + c') < veblen 3 (j + 1) := hE'u.trans hj2
    exact Order.lt_add_one_iff.1 ((isNormal_veblen 3).strictMono.lt_iff_lt.1 this)
  have hjE : j < i3 + c := (isNormal_veblen 3).strictMono.lt_iff_lt.1 (hj1.trans_lt huE)
  rcases hj1.lt_or_eq with hju | hju
  · -- `u` lies strictly between the level-3 points `φ(3, j)` and `φ(3, j+1)`
    have hNj : haN (veblen 3 j) = veblen 3 (j + 1) := ha_haN_veb3 j
    have hNq : haN (veblen 3 j) < gq 1 ρ := by
      rw [hNj]
      exact ((isNormal_veblen 3).monotone (Order.add_one_le_of_lt hjE)).trans_lt hEq
    have hρj : ρ < veblen 3 j := hρE'.trans_le ((isNormal_veblen 3).monotone hcj)
    obtain ⟨m, ζ, hm, hl, hζ⟩ := ha_down_Pall h (ha_fix2_veb3 j) hρj hNq hu hju (by rw [hNj]; exact hj2)
    exact ⟨m, ζ, hm.trans (by norm_num), hl, hζ, fun e => absurd e (by omega)⟩
  · -- `u = φ(3, i₃ + d)`, `c' < d < c`
    obtain ⟨d, rfl⟩ := exists_add_of_le (le_self_add.trans hcj : i3 ≤ j)
    have hc'd : c' < d := by
      rcases ((add_le_add_iff_left _).1 hcj).lt_or_eq with h' | h'
      · exact h'
      · exfalso; rw [← h'] at hju; exact absurd hju hE'u.ne
    have hdc : d < c := (add_lt_add_iff_left _).1 hjE
    have hd0 : d ≠ 0 := (lt_of_le_of_lt zero_le hc'd).ne'
    have hqd : lgG ρ + d < gq 1 ρ := ((add_lt_add_iff_left _).2 hdc).trans hq
    obtain ⟨hdT, hd1⟩ := gm1_T hρE hρ1 hqd
    have hval : glA 3 (lgG ρ + d) ρ = u := by
      rw [← hju]; exact ha_glA3V hρE hρ1 hi3 d hqd (fun ν' h' hl => hfix ν' (h'.trans hdc.le) hl)
    have hL := gl_lh_th (k := 3) hρE hρ1 (by norm_num) hdT hd1
    have hv : vt ρ (Om1 * ((3 : ℕ) : Ordinal.{0}) + (lgG ρ + d)) = u := by rw [Nat.cast_ofNat]; exact hval
    rw [hv] at hL
    have hζlg : glZeta ρ 3 (lgG ρ + d) ≤ lg d := (gz_glZeta_le ρ (lgG ρ + d) 3).trans (gz_lg_add _ hd0).le
    obtain ⟨-, -, -, -, -, htu⟩ := glA_facts hρE hρ1 h13 h3T h31 hdT hd1
    rw [hval] at htu
    have hdu : d < u := (le_add_self : d ≤ lgG ρ + d).trans_lt htu
    obtain ⟨δ', hδ'⟩ : ∃ δ', d = c' + δ' := ⟨d - c', (Ordinal.add_sub_cancel_of_le hc'd.le).symm⟩
    have hδ0 : δ' ≠ 0 := by rintro rfl; rw [add_zero] at hδ'; exact absurd hδ' hc'd.ne'
    have hδlt : δ' < ω ^ z := by
      have : c' + δ' < c' + ω ^ z := by rw [← hδ', ← hcs]; exact hdc
      exact (add_lt_add_iff_left _).1 this
    have hlgd : lg d < z := by
      rw [hδ', gz_lg_add _ hδ0]
      by_contra hge; push Not at hge
      obtain ⟨δ'', hδs, -, -⟩ := lg_split hδ0
      have h1 : ω ^ z ≤ ω ^ lg δ' := opow_le_opow_right omega0_pos hge
      have h2 : ω ^ lg δ' ≤ δ' := (le_add_self (a := ω ^ lg δ') (b := δ'')).trans_eq hδs.symm
      exact absurd (h1.trans h2) (not_le.2 hδlt)
    refine ⟨3, glZeta ρ 3 (lgG ρ + d), le_rfl, ?_, hζlg.trans_lt ((lg_le hd0).trans_lt hdu), ?_⟩
    · push_cast at hL ⊢; exact hL
    · intro _; rw [hz']; exact hζlg.trans_lt hlgd

/-- **LEMMA IMG FOR EVERY VALUE BELOW `B₄(ρ) = φ(4, Γ_{ρ+1}+1)`**: up to `B₃(ρ)` by `Ha.ha_img_le_B3`, between two
points of level `3` by `Ha.ha_img_next`, at successor points of level `3` by `ha_img_N3`, at limit points of level `3`
by `haI_limZ3`. -/
theorem ha_img_B4 : ∀ v, v < haB4 ρ → GnI ρ δ v := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hB4q := haB4_lt1 hρE hρ1
  obtain ⟨i3, hi3⟩ := ha_B3_LuP3 (x := ρ)
  have hB4f := haB4_fix ρ
  refine gnImg_of_eps h (fun v hv => gm1_T hρE hρ1 (hv.trans hB4q)) (fun e he _ heB IHe => ?_)
  rcases le_or_gt e (gzB3 ρ) with heB3 | hgt
  · exact ha_img_le_B3 h heB3
  obtain ⟨j, hj1, hj2⟩ := ha_floor3 (u := e) (j0 := i3) (by rw [hi3]; exact hgt.le)
  have hi3j : i3 ≤ j := by
    have : veblen 3 i3 < veblen 3 (j + 1) := by rw [hi3]; exact hgt.trans hj2
    exact Order.lt_add_one_iff.1 ((isNormal_veblen 3).strictMono.lt_iff_lt.1 this)
  have hjB4 : j < haB4 ρ := by
    have : veblen 3 j < veblen 3 (haB4 ρ) := by rw [hB4f]; exact hj1.trans_lt heB
    exact (isNormal_veblen 3).strictMono.lt_iff_lt.1 this
  have hj1B4 : veblen 3 (j + 1) < haB4 ρ := by
    have := (isNormal_veblen 3).strictMono ((ev_isSuccLimit_of_inE (ha_inE_of_fix2 (haB4_fix2 ρ))).add_one_lt hjB4)
    rwa [hB4f] at this
  have hρB3 : ρ < gzB3 ρ := ((lgG_facts hρE hρ1).2.1.trans (lt_evZ _)).trans (gzZ1_lt_B3 ρ)
  have hρj : ρ < veblen 3 j := hρB3.trans_le (by rw [← hi3]; exact (isNormal_veblen 3).monotone hi3j)
  rcases hj1.lt_or_eq with hjlt | hjeq
  · -- `e` strictly between `φ(3, j)` and `φ(3, j+1) = N(φ(3, j))`
    have hNj : haN (veblen 3 j) = veblen 3 (j + 1) := ha_haN_veb3 j
    exact ha_img_next h (ha_fix2_veb3 j) hρj (by rw [hNj]; exact hj1B4.trans hB4q)
      (fun v hv => IHe v (hv.trans_lt hjlt)) e (by rw [hNj]; exact hj2)
  · obtain ⟨d, rfl⟩ := exists_add_of_le hi3j
    have hnf : ∀ ν', ν' ≤ d → i3 + ν' < veblen 3 (i3 + ν') := fun ν' h' =>
      ha_nofix_B4 hρE hρ1 hi3 le_self_add
        (((isNormal_veblen 3).monotone ((add_le_add_iff_left _).2 h')).trans_lt (hjeq ▸ heB))
    have hdq : lgG ρ + d < gq 1 ρ :=
      (inE_indec (gm1_facts hρE hρ1).2.2.2).add_lt (mg_lgG_lt_G1 hρE hρ1)
        (((le_add_self : d ≤ i3 + d).trans_lt (hnf d le_rfl)).trans (hjeq ▸ heB.trans hB4q))
    rcases zero_or_succ_or_isSuccLimit d with h0 | ⟨d', hd'⟩ | hlim
    · subst h0
      rw [add_zero, hi3] at hjeq
      exact absurd hjeq hgt.ne
    · have hd'' : d = d' + 1 := by rw [← hd', succ_eq_add_one]
      subst hd''
      have hv : glA 3 (lgG ρ + d' + 1) ρ = e := by
        rw [← hjeq, add_assoc]; exact ha_glA3V hρE hρ1 hi3 (d' + 1) hdq (fun ν' h' _ => hnf ν' h')
      rw [← hv] at IHe ⊢
      exact ha_img_N3 h (by rw [add_assoc]; exact hdq) IHe
    · subst hjeq
      exact haI_limZ3 h hi3 hlim hdq (fun ν' h' _ => hnf ν' h') IHe

/-- **LEMMA IMG (gated) FOR A SPECIFIED FUNCTION BELOW `B₄(ρ)`.** -/
theorem ha_pkg_B4 {g : Ordinal.{0}} {C : Finset Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (hgρ : g < ρ)
    (hC : ∀ c ∈ C, c < ρ) (hT : T ρ < haB4 ρ) (hex : GjEx g C T) : GhPkg g ρ δ T :=
  gnPkg_of_GnI h hgρ hC (ha_img_B4 h _ hT) hex

end Img

end Googology.Trans.PoR.InaccPsi.R2.Ha
