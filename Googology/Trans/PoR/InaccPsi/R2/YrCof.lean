import Googology.Trans.PoR.InaccPsi.R2.YrMo
import Googology.Trans.PoR.InaccPsi.R2.YhCof

/-!
# YrCof: CODES BELOW `B_Γ`, READ ATOM INDICES: COFINALITY

Every `ν` below the reading of a code `c < B_Γ` is at most the reading of a smaller code with gate below `x`.  The
argument of `Yh.yhR_cof`; the atom `Γ(i)` is read `ϑˣ(Ω₁·Ω₁ + i(x))` and the codes below it have cofinal readings:
at `i = 0` by `Wt.wtD`; at `i = i' + 1` (`(i'+1)(x) = i'(x) + 1`) the supremum of the readings would be strongly
critical above `ϑˣ(Ω₁·Ω₁ + i'(x))` (`Xk.xk_sc_iff` at the admissible index `i'(x)`); at a limit `i` the reading
`i(x)` is a limit, `ν < ϑˣ(Ω₁·Ω₁ + j)` for some `j < i(x)` (`Yr.yr_lt_lim_iff`) and `j ≤ b(x)` for some `b < i`
(cofinality at the index), so `ν < Γ(b)(x)`.

* `yr_psi_read`, `YrCof`, `yr_lim_of_cof`, `yr_om_cl`, `yr_baseCof`, `yr_atomCof` (**THE BASE ATOMS WITH READ
  INDICES**), `yr_cofPow`, `yrR_cof` (**COFINALITY**, one induction).

No new axiom.  New definition: `YrCof`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yr

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Xu
  Googology.Trans.PoR.InaccPsi.R2.Xx Googology.Trans.PoR.InaccPsi.R2.Xk Googology.Trans.PoR.InaccPsi.R2.Wt
  Googology.Trans.PoR.InaccPsi.R2.Yh

/-- Cofinality at the code `j`: every `ν` below its reading is at most the reading of a smaller code. -/
def YrCof (x j : Ordinal.{0}) : Prop :=
  yrG j < x → ∀ ν, ν < yrR j x → ∃ b, b < j ∧ yrG b < x ∧ ν ≤ yrR b x

section Cof

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **`yhPsi α η` reads `ϑˣ(Ω₁·α(x) + η(x))` on both sides of `G`**, gate below `x`. -/
theorem yr_psi_read {α η : Ordinal.{0}} (hα1 : 1 ≤ α) (hαB : α < Tf.tfBG) (hηB : η < Tf.tfBG) (hgα : yrG α < x)
    (hgη : yrG η < x) :
    yrR (yhPsi α η) x = glA (yrR α x) (yrR η x) x ∧ yrG (yhPsi α η) < x ∧ yhPsi α η < Tf.tfBG := by
  have hpB : yhPsi α η < Tf.tfBG := yhPsi_lt_SC Tf.tfBG_SC Tf.tfBG_gt hαB hηB
  rcases lt_or_ge (yhPsi α η) (gcG 0) with hp | hp
  · have hαp := (yhPsi_gt hα1 η).2
    have hαG0 : α < gcG 0 := hαp.trans hp
    have hηG0 : η < gcG 0 := (lt_yhPsi α η).trans hp
    have hnA : ¬ YhAt α := fun h => absurd (yhAt_G_le h) (not_le.2 hαG0)
    have he : yhPsi α η = glPsi α η := yhPsi_ne hnA η
    rw [he] at hp ⊢
    refine ⟨?_, ?_, he ▸ hpB⟩
    · rw [yrR_low hp, glR_psi hα1 hαG0 hηG0, glBA_eq hx hx1, yrR_low hαG0, yrR_low hηG0]
    · rw [yrG_low hp, glG_psi hα1 hαG0 hηG0]
      rw [yrG_low hαG0] at hgα
      rw [yrG_low hηG0] at hgη
      exact max_lt ((glQ_le α).trans_lt hgα) ((glQ_le η).trans_lt hgη)
  · have hGp : gcG 0 < yhPsi α η := lt_of_le_of_ne hp (fun h => yhPsi_notAt hα1 (h ▸ yhAt_gcG 0))
    refine ⟨yrR_psi hα1 hGp x, ?_, hpB⟩
    rw [yrG_psi hα1 hGp]
    exact max_lt ((yrQ_le α).trans_lt hgα) ((yrQ_le η).trans_lt hgη)

/-- **A limit code has a limit reading.** -/
theorem yr_lim_of_cof {κ : Ordinal.{0}} (hl : IsSuccLimit κ) (hκB : κ < Tf.tfBG) (hg : yrG κ < x)
    (hc : YrCof x κ) : IsSuccLimit (yrR κ x) := by
  have hκ0 : κ ≠ 0 := hl.bot_lt.ne'
  rcases zero_or_succ_or_isSuccLimit (yrR κ x) with h0 | ⟨ν, hν⟩ | hlim
  · exact absurd h0 (yrR_pos hx hx1 hκ0 hκB hg).ne'
  · exfalso
    rw [succ_eq_add_one] at hν
    obtain ⟨b, hb, hgb, hνb⟩ := hc hg ν (by rw [← hν]; exact lt_add_one ν)
    have hbκ : yrR b x < yrR κ x := yrR_mono hx hx1 hκB hb hg hgb
    have hbe : yrR b x = ν := le_antisymm (Order.lt_add_one_iff.1 (hν ▸ hbκ)) hνb
    have hb1 : b + 1 < κ := hl.add_one_lt hb
    have hgb1 : yrG (b + 1) < x := yrG_succ (ev_isSuccLimit_of_inE hx) b hgb
    have := yrR_mono hx hx1 hκB hb1 hg hgb1
    rw [yrR_succ, hbe, hν] at this
    exact lt_irrefl _ this
  · exact hlim

/-- **Closure under `ω^·`** below a non-atom `ε`-number code `e ∈ (G, B_Γ)`. -/
theorem yr_om_cl {e t : Ordinal.{0}} (he : InE e) (hGe : gcG 0 < e) (heB : e < Tf.tfBG) (ht : t < e)
    (hgt : yrG t < x) : ∃ t', t' < e ∧ yrG t' < x ∧ ω ^ yrR t x ≤ yrR t' x := by
  rcases lt_or_ge t (gcG 0) with htG | htG
  · refine ⟨gcG 0, hGe, by rw [yrG_G0]; exact hx.pos, ?_⟩
    rw [yrR_G0, yrR_low htG, ← Gm.mg_gq0 hx hx1]
    rw [yrG_low htG] at hgt
    have := (lgG_facts hx hx1).2.2.2.1
    exact (this.opow_lt (glR_lt_G hx hx1 htG hgt)).le
  have htE := yh_gfE_le htG
  set et := guE t with hetdef
  have het : InE et := guE_E t
  have hett : et ≤ t := gl_E_le htE
  have hGet : gcG 0 ≤ et := yh_G_le_E htG
  have htB : t < eN et := gl_lt_eN htE
  have ht0 : t ≠ 0 := (lt_of_lt_of_le gl_G0_E.pos htG).ne'
  have hpB : et ^ t < eN et := gu_pow_lt_eN het htB
  have hpe : et ^ t < e := by
    rw [gu_pow_eq het]; exact he.opow_lt (he.mul_lt (hett.trans_lt ht) ht)
  have e1 : et ^ t = et ^ t * 1 + 0 := by rw [mul_one, add_zero]
  have hE1 : (1 : Ordinal.{0}) < et := Lu.lu_one_lt_E het
  have hr : (0 : Ordinal.{0}) < et ^ t := opow_pos _ het.pos
  have hv : et ^ t * 1 + 0 < eN et := by rw [← e1]; exact hpB
  have hge' := yr_E_g htG hgt
  have hetN : et < Tf.tfBG := (hett.trans_lt ht).trans heB
  refine ⟨et ^ t, hpe, ?_, ?_⟩
  · rw [e1, yrG_cnf het hGet ht0 one_ne_zero hE1 hr hv, yrQ_one, yrG_zero]
    rw [yrG_base het hGet] at hge'
    exact max_lt (max_lt hge' ((yrQ_le t).trans_lt hgt)) (max_lt hx.pos hx.pos)
  · rw [e1, yrR_cnf het hGet ht0 one_ne_zero hE1 hr hv, yrR_one, yrR_zero, mul_one, add_zero]
    have hA := (yrA_facts hx hx1 het hGet hetN hge').1
    exact opow_le_opow_left _ (omega0_lt_inE hA).le

/-- **THE CODES BELOW A NON-ATOM `ε`-NUMBER CODE `e = yhPsi α η ∈ (G, B_Γ)` HAVE READINGS COFINAL IN `e(x)`**, given
cofinality at the level and at the index. -/
theorem yr_baseCof {e : Ordinal.{0}} (he : InE e) (hGe : gcG 0 < e) (hnA : ¬ YhAt e) (heB : e < Tf.tfBG)
    (hge : yrG e < x) (hcα : YrCof x (yhK e)) (hcη : YrCof x (yhI e)) :
    ∀ ν, ν < yrR e x → ∃ t, t < e ∧ yrG t < x ∧ ν < yrR t x := by
  intro ν hν
  by_contra hcon
  push Not at hcon
  obtain ⟨r, hk1, hke, hηe, hgk, hgη, hkR, hkT, hk1x, hηT, hη1, hRE, -, -⟩ :=
    yr_eps_data hx hx1 he hGe hnA heB hge
  set α := yhK e with hαdef
  set η := yhI e with hηdef
  set β := yrR α x with hβdef
  have hce : yhPsi α η = e := (yhData_spec he hGe hnA).2.2.2
  have hαB : α < Tf.tfBG := hke.trans heB
  set T : Set Ordinal.{0} := {v | ∃ t, t < e ∧ yrG t < x ∧ v = yrR t x} with hTdef
  have hbdd : BddAbove T := ⟨ν, by rintro v ⟨t, ht, hgt, rfl⟩; exact hcon t ht hgt⟩
  have hmem : ∀ t, t < e → yrG t < x → yrR t x ∈ T := fun t ht hgt => ⟨t, ht, hgt, rfl⟩
  have hle : ∀ t, t < e → yrG t < x → yrR t x ≤ sSup T := fun t ht hgt => le_csSup hbdd (hmem t ht hgt)
  have hne : T.Nonempty := ⟨_, hmem 0 he.pos (by rw [yrG_zero]; exact hx.pos)⟩
  have huν : sSup T ≤ ν := csSup_le hne (by rintro v ⟨t, ht, hgt, rfl⟩; exact hcon t ht hgt)
  have hsucc : ∀ t, t < e → yrG t < x → t + 1 < e ∧ yrG (t + 1) < x ∧ yrR (t + 1) x = yrR t x + 1 :=
    fun t ht hgt => ⟨(ev_isSuccLimit_of_inE he).add_one_lt ht,
      yrG_succ (ev_isSuccLimit_of_inE hx) t hgt, yrR_succ t x⟩
  have hlt_of : ∀ t, t < e → yrG t < x → yrR t x < sSup T := by
    intro t ht hgt
    obtain ⟨h1, h2, h3⟩ := hsucc t ht hgt
    have := hle _ h1 h2
    rw [h3] at this
    exact (lt_add_one _).trans_le this
  have hlim : IsSuccLimit (sSup T) := by
    refine gl_sup_lim hne hbdd ?_
    rintro v ⟨t, ht, hgt, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hsucc t ht hgt
    exact ⟨_, hmem _ h1 h2, by rw [h3]; exact lt_add_one _⟩
  set u := sSup T with hudef
  have hEe : gfE < e := gfE_lt_G0.trans hGe
  have hEgate : yrG gfE < x := by rw [yrG_low gfE_lt_G0, glG_E]; exact hx.pos
  have hω : ∀ v, v < u → ω ^ v ≤ u := by
    intro v hv
    obtain ⟨w, ⟨t, ht, hgt, rfl⟩, hvw⟩ := exists_lt_of_lt_csSup hne hv
    obtain ⟨t', ht', hgt', hle'⟩ := yr_om_cl hx hx1 he hGe heB ht hgt
    exact (opow_le_opow_right omega0_pos hvw.le).trans (hle'.trans (hle _ ht' hgt'))
  have hPu : LuP β u := by
    have hβ0 : β ≠ 0 := (lt_of_lt_of_le zero_lt_one hkR).ne'
    refine (mem_range_veblen hβ0).2 fun γ hγ => ?_
    refine le_antisymm (((isNormal_veblen _).le_iff_forall_le hlim).2 fun v hv => ?_) (right_le_veblen _ _)
    rcases eq_or_ne γ 0 with rfl | hγ0
    · rw [veblen_zero_apply]; exact (hω v hv)
    obtain ⟨α'', hα''α, hgα'', hγα''⟩ := hcα hgk γ hγ
    have hα''0 : α'' ≠ 0 := by
      rintro rfl; rw [yrR_zero] at hγα''; exact hγ0 (le_antisymm hγα'' zero_le)
    have hα''1 : 1 ≤ α'' := one_le_iff_ne_zero.2 hα''0
    have hα''B : α'' < Tf.tfBG := hα''α.trans hαB
    obtain ⟨w, ⟨t, ht, hgt, rfl⟩, hvw⟩ := exists_lt_of_lt_csSup hne hv
    have htB : t < Tf.tfBG := ht.trans heB
    obtain ⟨htT, ht1⟩ := yrR_T hx hx1 htB hgt
    have hα''R1 : 1 ≤ yrR α'' x := one_le_iff_pos.2 (yrR_pos hx hx1 hα''0 hα''B hgα'')
    obtain ⟨hα''T, hα''1'⟩ := yrR_T hx hx1 hα''B hgα''
    have hpe : yhPsi α'' t < e := by
      rw [← hce]; exact (yhPsi_lt_lev hα''α hk1).2 (by rw [hce]; exact ht)
    obtain ⟨hRp, hgp, -⟩ := yr_psi_read hx hx1 hα''1 hα''B htB hgα'' hgt
    calc veblen γ v ≤ veblen (yrR α'' x) (yrR t x) :=
          (veblen_le_veblen_iff_right.2 hvw.le).trans (veblen_left_monotone _ hγα'')
      _ ≤ glA (yrR α'' x) (yrR t x) x := glA_veb_le hx hx1 hα''R1 hα''T hα''1' htT ht1
      _ = yrR (yhPsi α'' t) x := hRp.symm
      _ ≤ u := hle _ hpe hgp
  have hxu : x < u := by
    have := hle _ hEe hEgate
    rw [yrR_low gfE_lt_G0, glR_E] at this
    exact (lt_eN x).trans_le this
  have hηu : yrR η x < u := hlt_of η hηe hgη
  have hβu : β < u := hlt_of α hke hgk
  have hprev : ∀ σ, σ < yrR η x → glA β σ x < u := by
    intro σ hσ
    obtain ⟨σ', hσ'η, hgσ', hσσ'⟩ := hcη hgη σ hσ
    have hσ'B : σ' < Tf.tfBG := (hσ'η.trans hηe).trans heB
    obtain ⟨hσ'T, hσ'1⟩ := yrR_T hx hx1 hσ'B hgσ'
    have hσT : σ ∈ Tset x := vz_T_down hx hx1 hσ'T hσ'1 hσσ'
    have hpe : yhPsi α σ' < e := by rw [← hce]; exact yhPsi_lt_iff.2 hσ'η
    obtain ⟨h2, hgp, -⟩ := yr_psi_read hx hx1 hk1 hαB hσ'B hgk hgσ'
    have h1 : glA β σ x ≤ glA β (yrR σ' x) x :=
      (glA_le_iff hx hx1 hkR hkT hk1x hσT (lt_of_le_of_lt hσσ' hσ'1) hσ'T hσ'1).2 hσσ'
    rw [← h2] at h1
    exact h1.trans_lt (hlt_of _ hpe hgp)
  have hmin := glA_min hx hx1 hkR hkT hk1x hηT hη1 hPu hxu hηu hβu hprev
  rw [← r] at hmin
  exact absurd (hmin.trans huν) (not_le.2 hν)

/-- **THE CODES BELOW A BASE ATOM `Γ(i) < B_Γ` (gate below `x`) HAVE READINGS COFINAL IN `Γ_{x+1+i(x)}`**, given
cofinality at the index `i`. -/
theorem yr_atomCof {i : Ordinal.{0}} (hiB : gcG i < Tf.tfBG) (hgi : yrG i < x) (hci : YrCof x i) :
    ∀ ν, ν < gq (yrR i x) x → ∃ t, t < gcG i ∧ yrG t < x ∧ ν < yrR t x := by
  have hωx := omega0_lt_inE hx
  have hii : i < gcG i := yr_idx_BG ((gcG_strictMono.le_apply (x := i)).trans_lt hiB)
  have hiB' : i < Tf.tfBG := hii.trans hiB
  have hiN := yrR_N hx hx1 hiB' hgi
  intro ν hν
  rcases zero_or_succ_or_isSuccLimit i with rfl | ⟨i', hs⟩ | hl
  · -- `i = 0`: the hereditary step over `G`
    rw [yrR_zero, ← Gm.mg_gq0 hx hx1, ← wtD_RG x] at hν
    obtain ⟨d, hd, hgd, hνd⟩ := wtD.cof x hx hx1 (gcG 0) wtD_G_lt (by rw [wtD_gG]; exact hx.pos) ν hν
    have hdt : d < Wj.wjT 0 := hd.trans xu_G_lt_t0
    have hR : wtD.R d x = yrR d x := by rw [← xuR_low hdt, xuR_lowG hd, yrR_low hd]
    have hG : wtD.g d = yrG d := by rw [← xuG_low hdt, xuG_lowG hd, yrG_low hd]
    refine ⟨d + 1, (ev_isSuccLimit_of_inE gl_G0_E).add_one_lt hd, ?_, ?_⟩
    · exact yrG_succ (ev_isSuccLimit_of_inE hx) d (hG ▸ hgd)
    · rw [yrR_succ, ← hR]; exact Order.lt_add_one_iff.2 hνd
  · -- `i = i' + 1`: the supremum of the readings would be strongly critical above `Γ_{x+1+i'(x)}`
    rw [succ_eq_add_one] at hs
    subst hs
    have hi'i : i' < i' + 1 := lt_add_one i'
    have hi'B : gcG i' < Tf.tfBG := (gcG_lt hi'i).trans hiB
    have hii' : i' < gcG i' := yr_idx_BG ((gcG_strictMono.le_apply (x := i')).trans_lt hi'B)
    have hgi'0 : yrG i' < x := (yrG_le_succ i').trans_lt hgi
    have hi'N := yrR_N hx hx1 (hii'.trans hi'B) hgi'0
    rw [yrR_succ] at hν
    by_contra hcon
    push Not at hcon
    set T : Set Ordinal.{0} := {v | ∃ t, t < gcG (i' + 1) ∧ yrG t < x ∧ v = yrR t x} with hTdef
    have hbdd : BddAbove T := ⟨ν, by rintro v ⟨t, ht, hgt, rfl⟩; exact hcon t ht hgt⟩
    have hmem : ∀ t, t < gcG (i' + 1) → yrG t < x → yrR t x ∈ T := fun t ht hgt => ⟨t, ht, hgt, rfl⟩
    have hle : ∀ t, t < gcG (i' + 1) → yrG t < x → yrR t x ≤ sSup T :=
      fun t ht hgt => le_csSup hbdd (hmem t ht hgt)
    have hne : T.Nonempty := ⟨_, hmem 0 (gcG_SC _).1 (by rw [yrG_zero]; exact hx.pos)⟩
    have huν : sSup T ≤ ν := csSup_le hne (by rintro v ⟨t, ht, hgt, rfl⟩; exact hcon t ht hgt)
    have hGlim : IsSuccLimit (gcG (i' + 1)) := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (gcG_SC _))
    set u := sSup T with hudef
    have hi'lt : gcG i' < gcG (i' + 1) := gcG_lt hi'i
    have hgi' : yrG (gcG i') < x := by rw [yrG_atom hii']; exact (yrQ_le i').trans_lt hgi'0
    -- `Γ_{x+1+i'(x)} < u`
    have hqu : gq (yrR i' x) x < u := by
      have := hle _ (hGlim.add_one_lt hi'lt) (yrG_succ (ev_isSuccLimit_of_inE hx) _ hgi')
      rw [yrR_succ, yrR_atom hii'] at this
      exact (lt_add_one _).trans_le this
    obtain ⟨-, hxq, -, -, -⟩ := yr_facts hx hx1 hi'N
    -- `u` is strongly critical
    have hSC : SC u := by
      refine ⟨(hx.pos.trans hxq).trans hqu, fun a ha b hb => ?_⟩
      obtain ⟨w1, ⟨t1, ht1, hgt1, rfl⟩, hat1⟩ := exists_lt_of_lt_csSup hne ha
      obtain ⟨w2, ⟨t2, ht2, hgt2, rfl⟩, hbt2⟩ := exists_lt_of_lt_csSup hne hb
      have ht10 : t1 ≠ 0 := by rintro rfl; rw [yrR_zero] at hat1; exact absurd hat1 (not_lt.2 zero_le)
      have ht1B : t1 < Tf.tfBG := ht1.trans hiB
      have ht2B : t2 < Tf.tfBG := ht2.trans hiB
      have hR1 : 1 ≤ yrR t1 x := one_le_iff_pos.2 (yrR_pos hx hx1 ht10 ht1B hgt1)
      obtain ⟨hT1, h11⟩ := yrR_T hx hx1 ht1B hgt1
      obtain ⟨hT2, h12⟩ := yrR_T hx hx1 ht2B hgt2
      obtain ⟨hRp, hgp, -⟩ := yr_psi_read hx hx1 (one_le_iff_ne_zero.2 ht10) ht1B ht2B hgt1 hgt2
      have hpi : yhPsi t1 t2 < gcG (i' + 1) :=
        yhPsi_lt_SC (gcG_SC _) (by rw [Br.Om1_eq]; exact gcG_Om1_lt _) ht1 ht2
      calc veblen a b < veblen a (yrR t2 x) := veblen_lt_veblen_iff_right.2 hbt2
        _ ≤ veblen (yrR t1 x) (yrR t2 x) := veblen_left_monotone _ hat1.le
        _ ≤ glA (yrR t1 x) (yrR t2 x) x := glA_veb_le hx hx1 hR1 hT1 h11 hT2 h12
        _ = yrR (yhPsi t1 t2) x := hRp.symm
        _ < yrR (yhPsi t1 t2 + 1) x := by rw [yrR_succ]; exact lt_add_one _
        _ ≤ u := hle _ (hGlim.add_one_lt hpi) (yrG_succ (ev_isSuccLimit_of_inE hx) _ hgp)
    -- so `u = Γ_{x+1+c'}` for some `c' ≤ i'(x)`, a contradiction
    have hxu : x < u := hxq.trans hqu
    have hi'u : yrR i' x < u := (Gm.gmq_gt hx hx1 hi'N.1 hi'N.2.1).trans hqu
    have huq : u < gq (yrR i' x + 1) x := huν.trans_lt hν
    obtain ⟨c', hc', hc'u⟩ := (xk_sc_iff hx hx1 hi'N.1 hi'N.2.1 hxu hi'u huq).1 (Xf.xf_sc_veb0 hSC)
    have := yr_mono hx hx1 hi'N hc'
    rw [hc'u] at this
    exact absurd hqu (not_lt.2 this)
  · -- a limit `i`: its reading is a limit, the continuity of `ν ↦ Γ_{x+1+ν}` and cofinality at `i`
    have hlim := yr_lim_of_cof hx hx1 hl hiB' hgi hci
    obtain ⟨j, hj, hνj⟩ := yr_lt_lim_iff hx hx1 hlim hiN ν hν
    obtain ⟨b, hbi, hgb, hjb⟩ := hci hgi j hj
    have hbB : gcG b < Tf.tfBG := (gcG_lt hbi).trans hiB
    have hbb : b < gcG b := yr_idx_BG ((gcG_strictMono.le_apply (x := b)).trans_lt hbB)
    have hbN := yrR_N hx hx1 (hbb.trans hbB) hgb
    refine ⟨gcG b, gcG_lt hbi, by rw [yrG_atom hbb]; exact (yrQ_le b).trans_lt hgb, ?_⟩
    rw [yrR_atom hbb]
    exact hνj.trans_le (yr_mono hx hx1 hbN hjb)

/-- **The codes below `e^κ` have cofinal readings in `e(x)^{κ(x)}`** (`e ∈ [G, B_Γ)` an `ε`-number code whose
codes below are cofinal). -/
theorem yr_cofPow {M e : Ordinal.{0}} (hC : ∀ j, j < M → YrCof x j) (he : InE e) (hGe : gcG 0 ≤ e)
    (heB : e < Tf.tfBG) (hge : yrG e < x) (hbase : ∀ ν, ν < yrR e x → ∃ t, t < e ∧ yrG t < x ∧ ν < yrR t x) :
    ∀ κ, κ < M → κ ≠ 0 → κ < Tf.tfBG → yrG κ < x → κ < eN e →
    ∀ ν, ν < yrR e x ^ yrR κ x → ∃ t, t < e ^ κ ∧ yrG t < x ∧ ν < yrR t x := by
  set B := yrR e x with hBdef
  have hBE : InE B := by rw [hBdef, yrR_base he hGe]; exact (yrA_facts hx hx1 he hGe heB hge).1
  intro κ
  induction κ using WellFoundedLT.induction with
  | ind κ IH =>
  intro hκM hκ0 hκB hgκ hκE ν hν
  have hEκ : e ≤ e ^ κ := by
    calc e = e ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ e ^ κ := opow_le_opow_right he.pos (one_le_iff_ne_zero.2 hκ0)
  rcases zero_or_succ_or_isSuccLimit κ with h0 | ⟨κ', hs⟩ | hl
  · exact absurd h0 hκ0
  · rw [succ_eq_add_one] at hs
    have hκ'κ : κ' < κ := by rw [← hs]; exact lt_add_one κ'
    have r1 := yrR_succ κ' x
    have r2 := yrG_le_succ κ'
    rw [hs] at r1 r2
    have hgκ' : yrG κ' < x := r2.trans_lt hgκ
    rw [r1, opow_add, opow_one] at hν
    rcases eq_or_ne κ' 0 with h0 | hκ'0
    · rw [h0, yrR_zero, opow_zero, one_mul] at hν
      obtain ⟨t, ht, hgt, hvt⟩ := hbase ν hν
      exact ⟨t, ht.trans_le hEκ, hgt, hvt⟩
    · have hne : B ^ yrR κ' x ≠ 0 := opow_ne_zero _ hBE.pos.ne'
      have hq : ν / B ^ yrR κ' x < B := (Ordinal.div_lt hne).2 hν
      obtain ⟨t0, ht0, hgt0, hvt0⟩ := hbase _ hq
      have ht00 : t0 ≠ 0 := by
        rintro rfl; rw [yrR_zero] at hvt0; exact absurd hvt0 (not_lt.2 zero_le)
      have hpow : e ^ κ' * t0 < e ^ κ := by
        rw [← hs, opow_add, opow_one]; exact (mul_lt_mul_iff_right₀ (opow_pos _ he.pos)).2 ht0
      have hκpow : e ^ κ < eN e := gu_pow_lt_eN he hκE
      have hv : e ^ κ' * t0 + 0 < eN e := by rw [add_zero]; exact hpow.trans hκpow
      have hr0 : (0 : Ordinal.{0}) < e ^ κ' := opow_pos _ he.pos
      refine ⟨e ^ κ' * t0 + 0, by rw [add_zero]; exact hpow, ?_, ?_⟩
      · rw [yrG_cnf he hGe hκ'0 ht00 ht0 hr0 hv, yrG_zero]
        have hgE := yrG_base he hGe
        rw [hgE] at hge
        exact max_lt (max_lt hge ((yrQ_le _).trans_lt hgκ'))
          (max_lt ((yrQ_le _).trans_lt hgt0) (lt_of_le_of_lt zero_le hx.pos))
      · rw [yrR_cnf he hGe hκ'0 ht00 ht0 hr0 hv, yrR_zero, add_zero, ← yrR_base he hGe]
        calc ν < B ^ yrR κ' x * (ν / B ^ yrR κ' x + 1) := by
              rw [mul_add_one]
              conv_lhs => rw [← Ordinal.div_add_mod ν (B ^ yrR κ' x)]
              exact (add_lt_add_iff_left _).2 (Ordinal.mod_lt ν hne)
          _ ≤ B ^ yrR κ' x * yrR t0 x := mul_le_mul_right (add_one_le_of_lt hvt0) _
  · have hlim := yr_lim_of_cof hx hx1 hl hκB hgκ (hC κ hκM)
    obtain ⟨μ, hμ, hνμ⟩ := (lt_opow_of_isSuccLimit hBE.pos.ne' hlim).1 hν
    obtain ⟨κ', hκ'κ, hgκ', eκ'⟩ := hC κ hκM hgκ (μ + 1) (hlim.add_one_lt hμ)
    have hκ'0 : κ' ≠ 0 := by
      rintro rfl; rw [yrR_zero] at eκ'
      exact absurd eκ' (not_le.2 (lt_of_le_of_lt zero_le (lt_add_one μ)))
    have hν' : ν < B ^ yrR κ' x :=
      hνμ.trans_le (opow_le_opow_right hBE.pos ((lt_add_one μ).le.trans eκ'))
    obtain ⟨t, ht, hgt, hvt⟩ := IH κ' hκ'κ (hκ'κ.trans hκM) hκ'0 (hκ'κ.trans hκB) hgκ' (hκ'κ.trans hκE) ν hν'
    exact ⟨t, ht.trans_le (opow_le_opow_right he.pos hκ'κ.le), hgt, hvt⟩

/-- **COFINALITY**: every `ν` below the reading of a code `c < B_Γ` is at most the reading of a smaller code with
gate below `x`. -/
theorem yrR_cof : ∀ c, c < Tf.tfBG → YrCof x c := by
  have hωx := omega0_lt_inE hx
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg ν hν
  have hC : ∀ j, j < c → YrCof x j := fun j hj => IH j hj (hj.trans hc)
  rcases lt_or_ge c (gcG 0) with hcG | hcG
  · rw [yrG_low hcG] at hg
    rw [yrR_low hcG] at hν
    obtain ⟨b, hb, hgb, eb⟩ := glR_cof hx hx1 c hcG hg ν hν
    exact ⟨b, hb, by rw [yrG_low (hb.trans hcG)]; exact hgb, by rw [yrR_low (hb.trans hcG)]; exact eb⟩
  have hcE := yh_gfE_le hcG
  by_cases hcI : InE c
  · by_cases hA : YhAt c
    · obtain ⟨i, rfl⟩ := yhAt_iff.1 hA
      obtain ⟨hii, hie⟩ := yr_atom_idx rfl hc
      rw [yrR_atom hii] at hν
      have hgi : yrG i < x := yr_E_atom hωx hii hg
      obtain ⟨t, htc, hgt, hνt⟩ := yr_atomCof hx hx1 hc hgi (hC i hie) ν hν
      exact ⟨t, htc, hgt, hνt.le⟩
    · have hGc : gcG 0 < c := lt_of_le_of_ne hcG (fun h => hA (h ▸ yhAt_gcG 0))
      have hkc := (yhData_spec hcI hGc hA).2.1
      have hηc := (yhData_spec hcI hGc hA).2.2.1
      obtain ⟨t, htc, hgt, hνt⟩ := yr_baseCof hx hx1 hcI hGc hA hc hg (hC _ hkc) (hC _ hηc) ν hν
      exact ⟨t, htc, hgt, hνt.le⟩
  have hEc := gl_E_lt_self hcE hcI
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc, hdc⟩ := gl_parts hcE
  obtain ⟨g0, g1, g2⟩ := yr_parts_g hωx hcG hg
  obtain ⟨q0n, q0, -, -⟩ := yr_parts_Q hcG hg
  set e := guE c with hedef
  have he : InE e := guE_E c
  have hGe : gcG 0 ≤ e := yh_G_le_E hcG
  have heB : e < Tf.tfBG := hEc.trans hc
  have hge : yrG e < x := yr_E_g hcG hg
  set k := log e c with hkdef
  set d := c / e ^ k with hddef
  set r := c % e ^ k with hrdef
  set B := yrR e x with hBdef
  have hcN' : c < eN e := gl_lt_eN hcE
  have hBA : B = yrA e x := yrR_base he hGe x
  have hBE : InE B := by rw [hBA]; exact (yrA_facts hx hx1 he hGe heB hge).1
  -- the base cofinality of the bracket's `ε`-number
  have hbase : ∀ ν, ν < yrR e x → ∃ t, t < e ∧ yrG t < x ∧ ν < yrR t x := by
    by_cases hA : YhAt e
    · obtain ⟨i, hi⟩ := yhAt_iff.1 hA
      obtain ⟨hii, hie⟩ := yr_atom_idx hi heB
      have hgi : yrG i < x := yr_E_atom hωx hii (hi ▸ hge)
      rw [hi, yrR_atom hii]
      intro ν' hν'
      obtain ⟨t, ht, hgt, hvt⟩ := yr_atomCof hx hx1 (hi ▸ heB) hgi (hC i (hie.trans hEc)) ν' hν'
      exact ⟨t, hi ▸ ht, hgt, hvt⟩
    · have hGe' : gcG 0 < e := lt_of_le_of_ne hGe (fun h => hA (h ▸ yhAt_gcG 0))
      have hcη : YrCof x (yhI e) := hC _ ((yhData_spec he hGe' hA).2.2.1.trans hEc)
      have hcα : YrCof x (yhK e) := hC _ ((yhData_spec he hGe' hA).2.1.trans hEc)
      exact yr_baseCof hx hx1 he hGe' hA heB hge hcα hcη
  rw [yrR_dec hcG, ← hBA] at hν
  have hgate : ∀ d' t, d' ≠ 0 → d' < e → t < e ^ k → e ^ k * d' + t ≤ c → yrG d' < x → yrG t < x →
      yrG (e ^ k * d' + t) < x := by
    intro d' t hd' hd'E ht hle hgd' hgt
    rw [yrG_cnf he hGe hk hd' hd'E ht (hle.trans_lt hcN')]
    exact max_lt (max_lt q0n q0) (max_lt ((yrQ_le _).trans_lt hgd') hgt)
  rcases lt_or_ge ν (B ^ yrR k x * yrR d x) with hν1 | hν1
  · have hne : B ^ yrR k x ≠ 0 := opow_ne_zero _ hBE.pos.ne'
    have hμ : ν / B ^ yrR k x < yrR d x := (Ordinal.div_lt hne).2 hν1
    obtain ⟨d', hd'd, hgd', ed'⟩ := hC d hdc g1 _ hμ
    have hρ : ν % B ^ yrR k x < B ^ yrR k x := Ordinal.mod_lt ν hne
    obtain ⟨t, htk, hgt, hvt⟩ := yr_cofPow hx hx1 hC he hGe heB hge hbase k hkc hk (hkc.trans hc) g0
      (hkc.trans hcN') _ hρ
    have hd'E : d' < e := hd'd.trans hdE
    have hkd : e ^ k ≤ c := by
      rw [← hdec]; exact (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0)).trans le_self_add
    have hνe : ν = B ^ yrR k x * (ν / B ^ yrR k x) + ν % B ^ yrR k x := (Ordinal.div_add_mod ν _).symm
    rcases eq_or_ne d' 0 with hd'0 | hd'0
    · refine ⟨t, htk.trans_le hkd, hgt, ?_⟩
      rw [hd'0, yrR_zero] at ed'
      rw [hνe, nonpos_iff_eq_zero.1 ed', mul_zero, zero_add]; exact hvt.le
    · have hlt : e ^ k * d' + t < c := by
        calc e ^ k * d' + t < e ^ k * d' + e ^ k := (add_lt_add_iff_left _).2 htk
          _ = e ^ k * (d' + 1) := by rw [mul_add_one]
          _ ≤ e ^ k * d := mul_le_mul_right (add_one_le_of_lt hd'd) _
          _ ≤ c := by rw [← hdec]; exact le_self_add
      refine ⟨e ^ k * d' + t, hlt, hgate d' t hd'0 hd'E htk hlt.le hgd' hgt, ?_⟩
      rw [yrR_cnf he hGe hk hd'0 hd'E htk (hlt.le.trans_lt hcN'), ← yrR_base he hGe, hνe]
      exact add_le_add (mul_le_mul_right ed' _) hvt.le
  · have e1 : B ^ yrR k x * yrR d x + (ν - B ^ yrR k x * yrR d x) = ν := Ordinal.add_sub_cancel_of_le hν1
    have hν' : ν - B ^ yrR k x * yrR d x < yrR r x := by
      rw [← e1] at hν; exact (add_lt_add_iff_left _).1 hν
    obtain ⟨b', hb'r, hgb', hb'⟩ := hC r hrc g2 _ hν'
    have hb'k : b' < e ^ k := hb'r.trans hr
    have hlt : e ^ k * d + b' < c := by rw [← hdec]; exact (add_lt_add_iff_left _).2 hb'r
    refine ⟨e ^ k * d + b', hlt, hgate d b' hd0 hdE hb'k hlt.le g1 hgb', ?_⟩
    rw [yrR_cnf he hGe hk hd0 hdE hb'k (hlt.le.trans_lt hcN'), ← yrR_base he hGe, ← e1]
    exact add_le_add le_rfl hb'

end Cof

end Googology.Trans.PoR.InaccPsi.R2.Yr
