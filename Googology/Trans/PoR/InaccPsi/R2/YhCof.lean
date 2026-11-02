import Googology.Trans.PoR.InaccPsi.R2.YhMo

/-!
# YhCof: CODES BELOW `Γ(N)`: COFINALITY (every layer, every base atom)

Every `ν` below the reading of a code `c < Γ(N)` (`N < ε₀`) is at most the reading of a smaller code with gate below
`x`.  New against `Xu.xuR_cof`: the brackets of the base atoms.  The codes below `Γ(i)` have readings cofinal in
`Γ_{x+1+i}`: at `i = 0` by the hereditary step `Wt.wtD` (`lgG x = Γ_{x+1}`); at a limit `i` by the continuity of
`i ↦ Γ_{x+1+i}` (`Xx.xx_lt_lim_iff`); at `i = i' + 1` the supremum `u` of the readings would be strongly critical
(`φ(a, b) < ϑˣ(Ω₁·t₁(x) + t₂(x))` for `a < t₁(x)`, `b < t₂(x)`) and above `Γ_{x+1+i'}`, so `u ≥ Γ_{x+2+i'}` by
`Xk.xk_sc_iff`.

* `yh_psi_read` (**`yhPsi α η` reads `ϑˣ(Ω₁·α(x) + η(x))` on both sides of `G`**), `YhCof`, `yh_lim_of_cof`;
* `yh_om_cl`, `yh_baseCof` (**non-atom brackets**, the argument of `Xu.xu_baseCof`), `yh_atomCof` (**THE BASE ATOMS**);
* `yh_cofPow`, `yhR_cof` (**COFINALITY**, one induction).

No new axiom.  New definition: `YhCof`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yh

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Xu
  Googology.Trans.PoR.InaccPsi.R2.Xx Googology.Trans.PoR.InaccPsi.R2.Xk Googology.Trans.PoR.InaccPsi.R2.Wt

/-- Cofinality at the code `j`: every `ν` below its reading is at most the reading of a smaller code. -/
def YhCof (x j : Ordinal.{0}) : Prop :=
  yhG j < x → ∀ ν, ν < yhR j x → ∃ b, b < j ∧ yhG b < x ∧ ν ≤ yhR b x

section Cof

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {N : Ordinal.{0}} (hN : N < ε₀)
include hx hx1 hN

/-- **`yhPsi α η` reads `ϑˣ(Ω₁·α(x) + η(x))` on both sides of `G`**, gate below `x`. -/
theorem yh_psi_read {α η : Ordinal.{0}} (hα1 : 1 ≤ α) (hαN : α < gcG N) (hηN : η < gcG N) (hgα : yhG α < x)
    (hgη : yhG η < x) :
    yhR (yhPsi α η) x = glA (yhR α x) (yhR η x) x ∧ yhG (yhPsi α η) < x ∧ yhPsi α η < gcG N := by
  have hpN : yhPsi α η < gcG N := yhPsi_lt_SC (gcG_SC N) (by rw [Br.Om1_eq]; exact gcG_Om1_lt N) hαN hηN
  rcases lt_or_ge (yhPsi α η) (gcG 0) with hp | hp
  · have hαp := (yhPsi_gt hα1 η).2
    have hαG0 : α < gcG 0 := hαp.trans hp
    have hηG0 : η < gcG 0 := (lt_yhPsi α η).trans hp
    have hnA : ¬ YhAt α := fun h => absurd (yhAt_G_le h) (not_le.2 hαG0)
    have he : yhPsi α η = glPsi α η := yhPsi_ne hnA η
    rw [he] at hp ⊢
    refine ⟨?_, ?_, he ▸ hpN⟩
    · rw [yhR_low hp, glR_psi hα1 hαG0 hηG0, glBA_eq hx hx1, yhR_low hαG0, yhR_low hηG0]
    · rw [yhG_low hp, glG_psi hα1 hαG0 hηG0]
      rw [yhG_low hαG0] at hgα
      rw [yhG_low hηG0] at hgη
      exact max_lt ((glQ_le α).trans_lt hgα) ((glQ_le η).trans_lt hgη)
  · have hGp : gcG 0 < yhPsi α η := lt_of_le_of_ne hp (fun h => yhPsi_notAt hα1 (h ▸ yhAt_gcG 0))
    refine ⟨yhR_psi hα1 hGp x, ?_, hpN⟩
    rw [yhG_psi hα1 hGp]
    exact max_lt ((yhQ_le α).trans_lt hgα) ((yhQ_le η).trans_lt hgη)

/-- **A limit code has a limit reading.** -/
theorem yh_lim_of_cof {κ : Ordinal.{0}} (hl : IsSuccLimit κ) (hκN : κ < gcG N) (hg : yhG κ < x)
    (hc : YhCof x κ) : IsSuccLimit (yhR κ x) := by
  have hκ0 : κ ≠ 0 := hl.bot_lt.ne'
  rcases zero_or_succ_or_isSuccLimit (yhR κ x) with h0 | ⟨ν, hν⟩ | hlim
  · exact absurd h0 (yhR_pos hx hx1 hN hκ0 hκN hg).ne'
  · exfalso
    rw [succ_eq_add_one] at hν
    obtain ⟨b, hb, hgb, hνb⟩ := hc hg ν (by rw [← hν]; exact lt_add_one ν)
    have hbκ : yhR b x < yhR κ x := yhR_mono hx hx1 hN hκN hb hg hgb
    have hbe : yhR b x = ν := le_antisymm (Order.lt_add_one_iff.1 (hν ▸ hbκ)) hνb
    have hb1 : b + 1 < κ := hl.add_one_lt hb
    have hgb1 : yhG (b + 1) < x := yhG_succ (ev_isSuccLimit_of_inE hx) b hgb
    have := yhR_mono hx hx1 hN hκN hb1 hg hgb1
    rw [yhR_succ, hbe, hν] at this
    exact lt_irrefl _ this
  · exact hlim

/-- **Closure under `ω^·`** below a non-atom `ε`-number code `e ∈ (G, Γ(N))`. -/
theorem yh_om_cl {e t : Ordinal.{0}} (he : InE e) (hGe : gcG 0 < e) (heN : e < gcG N) (ht : t < e)
    (hgt : yhG t < x) : ∃ t', t' < e ∧ yhG t' < x ∧ ω ^ yhR t x ≤ yhR t' x := by
  rcases lt_or_ge t (gcG 0) with htG | htG
  · refine ⟨gcG 0, hGe, by rw [yhG_atom]; exact hx.pos, ?_⟩
    rw [yhR_atom, yhR_low htG, ← Gm.mg_gq0 hx hx1]
    rw [yhG_low htG] at hgt
    have := (lgG_facts hx hx1).2.2.2.1
    exact (this.opow_lt (glR_lt_G hx hx1 htG hgt)).le
  have htE := yh_gfE_le htG
  set et := guE t with hetdef
  have het : InE et := guE_E t
  have hett : et ≤ t := gl_E_le htE
  have hGet : gcG 0 ≤ et := yh_G_le_E htG
  have htN : t < eN et := gl_lt_eN htE
  have ht0 : t ≠ 0 := (lt_of_lt_of_le gl_G0_E.pos htG).ne'
  have hpN : et ^ t < eN et := gu_pow_lt_eN het htN
  have hpe : et ^ t < e := by
    rw [gu_pow_eq het]; exact he.opow_lt (he.mul_lt (hett.trans_lt ht) ht)
  have e1 : et ^ t = et ^ t * 1 + 0 := by rw [mul_one, add_zero]
  have hE1 : (1 : Ordinal.{0}) < et := Lu.lu_one_lt_E het
  have hr : (0 : Ordinal.{0}) < et ^ t := opow_pos _ het.pos
  have hv : et ^ t * 1 + 0 < eN et := by rw [← e1]; exact hpN
  have hge' := yh_E_g htG hgt
  have hetN : et < gcG N := (hett.trans_lt ht).trans heN
  refine ⟨et ^ t, hpe, ?_, ?_⟩
  · rw [e1, yhG_cnf het hGet ht0 one_ne_zero hE1 hr hv, yhQ_one, yhG_zero]
    rw [yhG_base het hGet] at hge'
    exact max_lt (max_lt hge' ((yhQ_le t).trans_lt hgt)) (max_lt hx.pos hx.pos)
  · rw [e1, yhR_cnf het hGet ht0 one_ne_zero hE1 hr hv, yhR_one, yhR_zero, mul_one, add_zero]
    have hA := (yhA_facts hx hx1 hN het hGet hetN hge').1
    exact opow_le_opow_left _ (omega0_lt_inE hA).le

/-- **THE CODES BELOW A NON-ATOM `ε`-NUMBER CODE `e = yhPsi α η ∈ (G, Γ(N))` HAVE READINGS COFINAL IN `e(x)`**, given
cofinality at the level and at the index. -/
theorem yh_baseCof {e : Ordinal.{0}} (he : InE e) (hGe : gcG 0 < e) (hnA : ¬ YhAt e) (heN : e < gcG N)
    (hge : yhG e < x) (hcα : YhCof x (yhK e)) (hcη : YhCof x (yhI e)) :
    ∀ ν, ν < yhR e x → ∃ t, t < e ∧ yhG t < x ∧ ν < yhR t x := by
  intro ν hν
  by_contra hcon
  push Not at hcon
  obtain ⟨r, hk1, hke, hηe, hgk, hgη, hkR, hkT, hk1x, hηT, hη1, hRE, -, -⟩ :=
    yh_eps_data hx hx1 hN he hGe hnA heN hge
  set α := yhK e with hαdef
  set η := yhI e with hηdef
  set β := yhR α x with hβdef
  have hce : yhPsi α η = e := (yhData_spec he hGe hnA).2.2.2
  have hαN : α < gcG N := hke.trans heN
  set T : Set Ordinal.{0} := {v | ∃ t, t < e ∧ yhG t < x ∧ v = yhR t x} with hTdef
  have hbdd : BddAbove T := ⟨ν, by rintro v ⟨t, ht, hgt, rfl⟩; exact hcon t ht hgt⟩
  have hmem : ∀ t, t < e → yhG t < x → yhR t x ∈ T := fun t ht hgt => ⟨t, ht, hgt, rfl⟩
  have hle : ∀ t, t < e → yhG t < x → yhR t x ≤ sSup T := fun t ht hgt => le_csSup hbdd (hmem t ht hgt)
  have hne : T.Nonempty := ⟨_, hmem 0 he.pos (by rw [yhG_zero]; exact hx.pos)⟩
  have huν : sSup T ≤ ν := csSup_le hne (by rintro v ⟨t, ht, hgt, rfl⟩; exact hcon t ht hgt)
  have hsucc : ∀ t, t < e → yhG t < x → t + 1 < e ∧ yhG (t + 1) < x ∧ yhR (t + 1) x = yhR t x + 1 :=
    fun t ht hgt => ⟨(ev_isSuccLimit_of_inE he).add_one_lt ht,
      yhG_succ (ev_isSuccLimit_of_inE hx) t hgt, yhR_succ t x⟩
  have hlt_of : ∀ t, t < e → yhG t < x → yhR t x < sSup T := by
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
  have hEgate : yhG gfE < x := by rw [yhG_low gfE_lt_G0, glG_E]; exact hx.pos
  have hω : ∀ v, v < u → ω ^ v ≤ u := by
    intro v hv
    obtain ⟨w, ⟨t, ht, hgt, rfl⟩, hvw⟩ := exists_lt_of_lt_csSup hne hv
    obtain ⟨t', ht', hgt', hle'⟩ := yh_om_cl hx hx1 hN he hGe heN ht hgt
    exact (opow_le_opow_right omega0_pos hvw.le).trans (hle'.trans (hle _ ht' hgt'))
  have hPu : LuP β u := by
    have hβ0 : β ≠ 0 := (lt_of_lt_of_le zero_lt_one hkR).ne'
    refine (mem_range_veblen hβ0).2 fun γ hγ => ?_
    refine le_antisymm (((isNormal_veblen _).le_iff_forall_le hlim).2 fun v hv => ?_) (right_le_veblen _ _)
    rcases eq_or_ne γ 0 with rfl | hγ0
    · rw [veblen_zero_apply]; exact (hω v hv)
    obtain ⟨α'', hα''α, hgα'', hγα''⟩ := hcα hgk γ hγ
    have hα''0 : α'' ≠ 0 := by
      rintro rfl; rw [yhR_zero] at hγα''; exact hγ0 (le_antisymm hγα'' zero_le)
    have hα''1 : 1 ≤ α'' := one_le_iff_ne_zero.2 hα''0
    have hα''N : α'' < gcG N := hα''α.trans hαN
    obtain ⟨w, ⟨t, ht, hgt, rfl⟩, hvw⟩ := exists_lt_of_lt_csSup hne hv
    have htN : t < gcG N := ht.trans heN
    obtain ⟨htT, ht1⟩ := yhR_T hx hx1 hN htN hgt
    have hα''R1 : 1 ≤ yhR α'' x := one_le_iff_pos.2 (yhR_pos hx hx1 hN hα''0 hα''N hgα'')
    obtain ⟨hα''T, hα''1'⟩ := yhR_T hx hx1 hN hα''N hgα''
    have hpe : yhPsi α'' t < e := by
      rw [← hce]; exact (yhPsi_lt_lev hα''α hk1).2 (by rw [hce]; exact ht)
    obtain ⟨hRp, hgp, -⟩ := yh_psi_read hx hx1 hN hα''1 hα''N htN hgα'' hgt
    calc veblen γ v ≤ veblen (yhR α'' x) (yhR t x) :=
          (veblen_le_veblen_iff_right.2 hvw.le).trans (veblen_left_monotone _ hγα'')
      _ ≤ glA (yhR α'' x) (yhR t x) x := glA_veb_le hx hx1 hα''R1 hα''T hα''1' htT ht1
      _ = yhR (yhPsi α'' t) x := hRp.symm
      _ ≤ u := hle _ hpe hgp
  have hxu : x < u := by
    have := hle _ hEe hEgate
    rw [yhR_low gfE_lt_G0, glR_E] at this
    exact (lt_eN x).trans_le this
  have hηu : yhR η x < u := hlt_of η hηe hgη
  have hβu : β < u := hlt_of α hke hgk
  have hprev : ∀ σ, σ < yhR η x → glA β σ x < u := by
    intro σ hσ
    obtain ⟨σ', hσ'η, hgσ', hσσ'⟩ := hcη hgη σ hσ
    have hσ'N : σ' < gcG N := (hσ'η.trans hηe).trans heN
    obtain ⟨hσ'T, hσ'1⟩ := yhR_T hx hx1 hN hσ'N hgσ'
    have hσT : σ ∈ Tset x := vz_T_down hx hx1 hσ'T hσ'1 hσσ'
    have hpe : yhPsi α σ' < e := by rw [← hce]; exact yhPsi_lt_iff.2 hσ'η
    obtain ⟨h2, hgp, -⟩ := yh_psi_read hx hx1 hN hk1 hαN hσ'N hgk hgσ'
    have h1 : glA β σ x ≤ glA β (yhR σ' x) x :=
      (glA_le_iff hx hx1 hkR hkT hk1x hσT (lt_of_le_of_lt hσσ' hσ'1) hσ'T hσ'1).2 hσσ'
    rw [← h2] at h1
    exact h1.trans_lt (hlt_of _ hpe hgp)
  have hmin := glA_min hx hx1 hkR hkT hk1x hηT hη1 hPu hxu hηu hβu hprev
  rw [← r] at hmin
  exact absurd (hmin.trans huν) (not_le.2 hν)

/-- **THE CODES BELOW A BASE ATOM `Γ(i)`, `i < N`, HAVE READINGS COFINAL IN `Γ_{x+1+i}`.** -/
theorem yh_atomCof {i : Ordinal.{0}} (hiN : i < N) :
    ∀ ν, ν < gq i x → ∃ t, t < gcG i ∧ yhG t < x ∧ ν < yhR t x := by
  have hiε : i < ε₀ := hiN.trans hN
  intro ν hν
  rcases zero_or_succ_or_isSuccLimit i with rfl | ⟨i', hs⟩ | hl
  · -- `i = 0`: the hereditary step over `G`
    rw [← Gm.mg_gq0 hx hx1, ← wtD_RG x] at hν
    obtain ⟨d, hd, hgd, hνd⟩ := wtD.cof x hx hx1 (gcG 0) wtD_G_lt (by rw [wtD_gG]; exact hx.pos) ν hν
    have hdt : d < Wj.wjT 0 := hd.trans xu_G_lt_t0
    have hR : wtD.R d x = yhR d x := by rw [← xuR_low hdt, xuR_lowG hd, yhR_low hd]
    have hG : wtD.g d = yhG d := by rw [← xuG_low hdt, xuG_lowG hd, yhG_low hd]
    refine ⟨d + 1, (ev_isSuccLimit_of_inE gl_G0_E).add_one_lt hd, ?_, ?_⟩
    · exact yhG_succ (ev_isSuccLimit_of_inE hx) d (hG ▸ hgd)
    · rw [yhR_succ, ← hR]; exact Order.lt_add_one_iff.2 hνd
  · -- `i = i' + 1`: the supremum of the readings would be strongly critical above `Γ_{x+1+i'}`
    rw [succ_eq_add_one] at hs
    subst hs
    have hi'N : i' < N := (lt_add_one i').trans hiN
    have hi'ε : i' < ε₀ := hi'N.trans hN
    by_contra hcon
    push Not at hcon
    set T : Set Ordinal.{0} := {v | ∃ t, t < gcG (i' + 1) ∧ yhG t < x ∧ v = yhR t x} with hTdef
    have hbdd : BddAbove T := ⟨ν, by rintro v ⟨t, ht, hgt, rfl⟩; exact hcon t ht hgt⟩
    have hmem : ∀ t, t < gcG (i' + 1) → yhG t < x → yhR t x ∈ T := fun t ht hgt => ⟨t, ht, hgt, rfl⟩
    have hle : ∀ t, t < gcG (i' + 1) → yhG t < x → yhR t x ≤ sSup T :=
      fun t ht hgt => le_csSup hbdd (hmem t ht hgt)
    have hne : T.Nonempty := ⟨_, hmem 0 (gcG_SC _).1 (by rw [yhG_zero]; exact hx.pos)⟩
    have huν : sSup T ≤ ν := csSup_le hne (by rintro v ⟨t, ht, hgt, rfl⟩; exact hcon t ht hgt)
    have hGlim : IsSuccLimit (gcG (i' + 1)) := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (gcG_SC _))
    set u := sSup T with hudef
    have hi'lt : gcG i' < gcG (i' + 1) := gcG_lt (lt_add_one i')
    have hgi' : yhG (gcG i') < x := by rw [yhG_atom]; exact hx.pos
    -- `Γ_{x+1+i'} < u`
    have hqu : gq i' x < u := by
      have := hle _ (hGlim.add_one_lt hi'lt) (yhG_succ (ev_isSuccLimit_of_inE hx) _ hgi')
      rw [yhR_succ, yhR_atom] at this
      exact (lt_add_one _).trans_le this
    -- `u` is strongly critical
    have hSC : SC u := by
      refine ⟨(hx.pos.trans (yh_gqN hx hx1 hi'ε).2.1).trans hqu, fun a ha b hb => ?_⟩
      obtain ⟨w1, ⟨t1, ht1, hgt1, rfl⟩, hat1⟩ := exists_lt_of_lt_csSup hne ha
      obtain ⟨w2, ⟨t2, ht2, hgt2, rfl⟩, hbt2⟩ := exists_lt_of_lt_csSup hne hb
      have ht10 : t1 ≠ 0 := by rintro rfl; rw [yhR_zero] at hat1; exact absurd hat1 (not_lt.2 zero_le)
      have ht1N : t1 < gcG N := ht1.trans_le (gcG_le hiN.le)
      have ht2N : t2 < gcG N := ht2.trans_le (gcG_le hiN.le)
      have hR1 : 1 ≤ yhR t1 x := one_le_iff_pos.2 (yhR_pos hx hx1 hN ht10 ht1N hgt1)
      obtain ⟨hT1, h11⟩ := yhR_T hx hx1 hN ht1N hgt1
      obtain ⟨hT2, h12⟩ := yhR_T hx hx1 hN ht2N hgt2
      obtain ⟨hRp, hgp, -⟩ := yh_psi_read hx hx1 hN (one_le_iff_ne_zero.2 ht10) ht1N ht2N hgt1 hgt2
      have hpi : yhPsi t1 t2 < gcG (i' + 1) :=
        yhPsi_lt_SC (gcG_SC _) (by rw [Br.Om1_eq]; exact gcG_Om1_lt _) ht1 ht2
      calc veblen a b < veblen a (yhR t2 x) := veblen_lt_veblen_iff_right.2 hbt2
        _ ≤ veblen (yhR t1 x) (yhR t2 x) := veblen_left_monotone _ hat1.le
        _ ≤ glA (yhR t1 x) (yhR t2 x) x := glA_veb_le hx hx1 hR1 hT1 h11 hT2 h12
        _ = yhR (yhPsi t1 t2) x := hRp.symm
        _ < yhR (yhPsi t1 t2 + 1) x := by rw [yhR_succ]; exact lt_add_one _
        _ ≤ u := hle _ (hGlim.add_one_lt hpi) (yhG_succ (ev_isSuccLimit_of_inE hx) _ hgp)
    -- so `u = Γ_{x+1+c'}` for some `c' ≤ i'`, a contradiction
    obtain ⟨-, hxq, -, -, hi'q, hi'T, hi'1⟩ := yh_gqN hx hx1 hi'ε
    have hxu : x < u := hxq.trans hqu
    have hi'u : i' < u := hi'q.trans hqu
    have huq : u < gq (i' + 1) x := huν.trans_lt hν
    obtain ⟨c', hc', hc'u⟩ := (xk_sc_iff hx hx1 hi'T hi'1 hxu hi'u huq).1 (Xf.xf_sc_veb0 hSC)
    have := xx_mono hx hx1 hi'ε hi'q hc'
    rw [hc'u] at this
    exact absurd hqu (not_lt.2 this)
  · -- a limit `i`: the continuity of `i ↦ Γ_{x+1+i}`
    obtain ⟨j, hj, hνj⟩ := xx_lt_lim_iff hx hx1 hN hl ((yh_gqN hx hx1 hN).2.2.2.2.1.trans_le' hiN.le) ν hν
    exact ⟨gcG j, gcG_lt hj, by rw [yhG_atom]; exact hx.pos, by rw [yhR_atom]; exact hνj⟩

/-- **The codes below `e^κ` have cofinal readings in `e(x)^{κ(x)}`** (`e ∈ [G, Γ(N))` an `ε`-number code whose
codes below are cofinal). -/
theorem yh_cofPow {M e : Ordinal.{0}} (hC : ∀ j, j < M → YhCof x j) (he : InE e) (hGe : gcG 0 ≤ e)
    (heN : e < gcG N) (hge : yhG e < x) (hbase : ∀ ν, ν < yhR e x → ∃ t, t < e ∧ yhG t < x ∧ ν < yhR t x) :
    ∀ κ, κ < M → κ ≠ 0 → κ < gcG N → yhG κ < x → κ < eN e →
    ∀ ν, ν < yhR e x ^ yhR κ x → ∃ t, t < e ^ κ ∧ yhG t < x ∧ ν < yhR t x := by
  set B := yhR e x with hBdef
  have hBE : InE B := by rw [hBdef, yhR_base he hGe]; exact (yhA_facts hx hx1 hN he hGe heN hge).1
  intro κ
  induction κ using WellFoundedLT.induction with
  | ind κ IH =>
  intro hκM hκ0 hκN hgκ hκE ν hν
  have hEκ : e ≤ e ^ κ := by
    calc e = e ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ e ^ κ := opow_le_opow_right he.pos (one_le_iff_ne_zero.2 hκ0)
  rcases zero_or_succ_or_isSuccLimit κ with h0 | ⟨κ', hs⟩ | hl
  · exact absurd h0 hκ0
  · rw [succ_eq_add_one] at hs
    have hκ'κ : κ' < κ := by rw [← hs]; exact lt_add_one κ'
    have r1 := yhR_succ κ' x
    have r2 := yhG_le_succ κ'
    rw [hs] at r1 r2
    have hgκ' : yhG κ' < x := r2.trans_lt hgκ
    rw [r1, opow_add, opow_one] at hν
    rcases eq_or_ne κ' 0 with h0 | hκ'0
    · rw [h0, yhR_zero, opow_zero, one_mul] at hν
      obtain ⟨t, ht, hgt, hvt⟩ := hbase ν hν
      exact ⟨t, ht.trans_le hEκ, hgt, hvt⟩
    · have hne : B ^ yhR κ' x ≠ 0 := opow_ne_zero _ hBE.pos.ne'
      have hq : ν / B ^ yhR κ' x < B := (Ordinal.div_lt hne).2 hν
      obtain ⟨t0, ht0, hgt0, hvt0⟩ := hbase _ hq
      have ht00 : t0 ≠ 0 := by
        rintro rfl; rw [yhR_zero] at hvt0; exact absurd hvt0 (not_lt.2 zero_le)
      have hpow : e ^ κ' * t0 < e ^ κ := by
        rw [← hs, opow_add, opow_one]; exact (mul_lt_mul_iff_right₀ (opow_pos _ he.pos)).2 ht0
      have hκpow : e ^ κ < eN e := gu_pow_lt_eN he hκE
      have hv : e ^ κ' * t0 + 0 < eN e := by rw [add_zero]; exact hpow.trans hκpow
      have hr0 : (0 : Ordinal.{0}) < e ^ κ' := opow_pos _ he.pos
      refine ⟨e ^ κ' * t0 + 0, by rw [add_zero]; exact hpow, ?_, ?_⟩
      · rw [yhG_cnf he hGe hκ'0 ht00 ht0 hr0 hv, yhG_zero]
        have hgE := yhG_base he hGe
        rw [hgE] at hge
        exact max_lt (max_lt hge ((yhQ_le _).trans_lt hgκ'))
          (max_lt ((yhQ_le _).trans_lt hgt0) (lt_of_le_of_lt zero_le hx.pos))
      · rw [yhR_cnf he hGe hκ'0 ht00 ht0 hr0 hv, yhR_zero, add_zero, ← yhR_base he hGe]
        calc ν < B ^ yhR κ' x * (ν / B ^ yhR κ' x + 1) := by
              rw [mul_add_one]
              conv_lhs => rw [← Ordinal.div_add_mod ν (B ^ yhR κ' x)]
              exact (add_lt_add_iff_left _).2 (Ordinal.mod_lt ν hne)
          _ ≤ B ^ yhR κ' x * yhR t0 x := mul_le_mul_right (add_one_le_of_lt hvt0) _
  · have hlim := yh_lim_of_cof hx hx1 hN hl hκN hgκ (hC κ hκM)
    obtain ⟨μ, hμ, hνμ⟩ := (lt_opow_of_isSuccLimit hBE.pos.ne' hlim).1 hν
    obtain ⟨κ', hκ'κ, hgκ', eκ'⟩ := hC κ hκM hgκ (μ + 1) (hlim.add_one_lt hμ)
    have hκ'0 : κ' ≠ 0 := by
      rintro rfl; rw [yhR_zero] at eκ'
      exact absurd eκ' (not_le.2 (lt_of_le_of_lt zero_le (lt_add_one μ)))
    have hν' : ν < B ^ yhR κ' x :=
      hνμ.trans_le (opow_le_opow_right hBE.pos ((lt_add_one μ).le.trans eκ'))
    obtain ⟨t, ht, hgt, hvt⟩ := IH κ' hκ'κ (hκ'κ.trans hκM) hκ'0 (hκ'κ.trans hκN) hgκ' (hκ'κ.trans hκE) ν hν'
    exact ⟨t, ht.trans_le (opow_le_opow_right he.pos hκ'κ.le), hgt, hvt⟩

/-- **COFINALITY**: every `ν` below the reading of a code `c < Γ(N)` is at most the reading of a smaller code with
gate below `x`. -/
theorem yhR_cof : ∀ c, c < gcG N → YhCof x c := by
  have hωx := omega0_lt_inE hx
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg ν hν
  have hC : ∀ j, j < c → YhCof x j := fun j hj => IH j hj (hj.trans hc)
  rcases lt_or_ge c (gcG 0) with hcG | hcG
  · rw [yhG_low hcG] at hg
    rw [yhR_low hcG] at hν
    obtain ⟨b, hb, hgb, eb⟩ := glR_cof hx hx1 c hcG hg ν hν
    exact ⟨b, hb, by rw [yhG_low (hb.trans hcG)]; exact hgb, by rw [yhR_low (hb.trans hcG)]; exact eb⟩
  have hcE := yh_gfE_le hcG
  by_cases hcI : InE c
  · by_cases hA : YhAt c
    · obtain ⟨i, rfl⟩ := yhAt_iff.1 hA
      rw [yhR_atom] at hν
      obtain ⟨t, htc, hgt, hνt⟩ := yh_atomCof hx hx1 hN (gcG_strictMono.lt_iff_lt.1 hc) ν hν
      exact ⟨t, htc, hgt, hνt.le⟩
    · have hGc : gcG 0 < c := lt_of_le_of_ne hcG (fun h => hA (h ▸ yhAt_gcG 0))
      have hkc := (yhData_spec hcI hGc hA).2.1
      have hηc := (yhData_spec hcI hGc hA).2.2.1
      obtain ⟨t, htc, hgt, hνt⟩ := yh_baseCof hx hx1 hN hcI hGc hA hc hg (hC _ hkc) (hC _ hηc) ν hν
      exact ⟨t, htc, hgt, hνt.le⟩
  have hEc := gl_E_lt_self hcE hcI
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc, hdc⟩ := gl_parts hcE
  obtain ⟨g0, g1, g2⟩ := yh_parts_g hωx hcG hg
  obtain ⟨q0n, q0, -, -⟩ := yh_parts_Q hcG hg
  set e := guE c with hedef
  have he : InE e := guE_E c
  have hGe : gcG 0 ≤ e := yh_G_le_E hcG
  have heN : e < gcG N := hEc.trans hc
  have hge : yhG e < x := yh_E_g hcG hg
  set k := log e c with hkdef
  set d := c / e ^ k with hddef
  set r := c % e ^ k with hrdef
  set B := yhR e x with hBdef
  have hcN' : c < eN e := gl_lt_eN hcE
  have hBA : B = yhA e x := yhR_base he hGe x
  have hBE : InE B := by rw [hBA]; exact (yhA_facts hx hx1 hN he hGe heN hge).1
  -- the base cofinality of the bracket's `ε`-number
  have hbase : ∀ ν, ν < yhR e x → ∃ t, t < e ∧ yhG t < x ∧ ν < yhR t x := by
    by_cases hA : YhAt e
    · obtain ⟨i, hi⟩ := yhAt_iff.1 hA
      rw [hi, yhR_atom]
      have hiN : i < N := gcG_strictMono.lt_iff_lt.1 (hi ▸ heN)
      intro ν' hν'
      obtain ⟨t, ht, hgt, hvt⟩ := yh_atomCof hx hx1 hN hiN ν' hν'
      exact ⟨t, hi ▸ ht, hgt, hvt⟩
    · have hGe' : gcG 0 < e := lt_of_le_of_ne hGe (fun h => hA (h ▸ yhAt_gcG 0))
      have hcη : YhCof x (yhI e) := hC _ ((yhData_spec he hGe' hA).2.2.1.trans hEc)
      have hcα : YhCof x (yhK e) := hC _ ((yhData_spec he hGe' hA).2.1.trans hEc)
      exact yh_baseCof hx hx1 hN he hGe' hA heN hge hcα hcη
  rw [yhR_dec hcG, ← hBA] at hν
  have hgate : ∀ d' t, d' ≠ 0 → d' < e → t < e ^ k → e ^ k * d' + t ≤ c → yhG d' < x → yhG t < x →
      yhG (e ^ k * d' + t) < x := by
    intro d' t hd' hd'E ht hle hgd' hgt
    rw [yhG_cnf he hGe hk hd' hd'E ht (hle.trans_lt hcN')]
    exact max_lt (max_lt q0n q0) (max_lt ((yhQ_le _).trans_lt hgd') hgt)
  rcases lt_or_ge ν (B ^ yhR k x * yhR d x) with hν1 | hν1
  · have hne : B ^ yhR k x ≠ 0 := opow_ne_zero _ hBE.pos.ne'
    have hμ : ν / B ^ yhR k x < yhR d x := (Ordinal.div_lt hne).2 hν1
    obtain ⟨d', hd'd, hgd', ed'⟩ := hC d hdc g1 _ hμ
    have hρ : ν % B ^ yhR k x < B ^ yhR k x := Ordinal.mod_lt ν hne
    obtain ⟨t, htk, hgt, hvt⟩ := yh_cofPow hx hx1 hN hC he hGe heN hge hbase k hkc hk (hkc.trans hc) g0
      (hkc.trans hcN') _ hρ
    have hd'E : d' < e := hd'd.trans hdE
    have hkd : e ^ k ≤ c := by
      rw [← hdec]; exact (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0)).trans le_self_add
    have hνe : ν = B ^ yhR k x * (ν / B ^ yhR k x) + ν % B ^ yhR k x := (Ordinal.div_add_mod ν _).symm
    rcases eq_or_ne d' 0 with hd'0 | hd'0
    · refine ⟨t, htk.trans_le hkd, hgt, ?_⟩
      rw [hd'0, yhR_zero] at ed'
      rw [hνe, nonpos_iff_eq_zero.1 ed', mul_zero, zero_add]; exact hvt.le
    · have hlt : e ^ k * d' + t < c := by
        calc e ^ k * d' + t < e ^ k * d' + e ^ k := (add_lt_add_iff_left _).2 htk
          _ = e ^ k * (d' + 1) := by rw [mul_add_one]
          _ ≤ e ^ k * d := mul_le_mul_right (add_one_le_of_lt hd'd) _
          _ ≤ c := by rw [← hdec]; exact le_self_add
      refine ⟨e ^ k * d' + t, hlt, hgate d' t hd'0 hd'E htk hlt.le hgd' hgt, ?_⟩
      rw [yhR_cnf he hGe hk hd'0 hd'E htk (hlt.le.trans_lt hcN'), ← yhR_base he hGe, hνe]
      exact add_le_add (mul_le_mul_right ed' _) hvt.le
  · have e1 : B ^ yhR k x * yhR d x + (ν - B ^ yhR k x * yhR d x) = ν := Ordinal.add_sub_cancel_of_le hν1
    have hν' : ν - B ^ yhR k x * yhR d x < yhR r x := by
      rw [← e1] at hν; exact (add_lt_add_iff_left _).1 hν
    obtain ⟨b', hb'r, hgb', hb'⟩ := hC r hrc g2 _ hν'
    have hb'k : b' < e ^ k := hb'r.trans hr
    have hlt : e ^ k * d + b' < c := by rw [← hdec]; exact (add_lt_add_iff_left _).2 hb'r
    refine ⟨e ^ k * d + b', hlt, hgate d b' hd0 hdE hb'k hlt.le g1 hgb', ?_⟩
    rw [yhR_cnf he hGe hk hd0 hdE hb'k (hlt.le.trans_lt hcN'), ← yhR_base he hGe, ← e1]
    exact add_le_add le_rfl hb'

end Cof

end Googology.Trans.PoR.InaccPsi.R2.Yh
