import Googology.Trans.PoR.InaccPsi.R2.SmVt

/-!
# `B_n` commutes with `ϑ^τ` at the uncountable arguments `[Ω₁, Ω₁·Ω₁)`, `τ = υ_ξ` the base of a point

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`B_n = Bc.bcB S n`, `c_n = L(n+1) = Bc.bcC S n`, `τ = υ_ξ`, `ϑᵗ = vt τ`, `φ_β = veblen β`, `P_β` the range of `φ_β`
(`LuP β`), `ind_{β,w}(b)` the index of `b` among the `x` off `P_{β+1}` with `w < φ_β(x)` (`lvInd β w b`).

* `sm_hbu` (`β < u` for every `u ∈ P_β` above `w`, when `β ≤ w` or `β` is not strongly critical);
* `smPhLev` (**THE LEVEL LEMMA with a lower bound `w ∈ {y} ∪ {β}`**: for a strongly critical `y < Ω₁`, a level
  `1 ≤ β ∈ Tʸ ∩ Ω₁` and `y ≤ w` with `w ≤ y` or `w = β`, and `β` below the members of `P_β` above `w`:
  `φ_β(b) = ϑʸ(Ω₁·β + ind_{β,w}(b))` for `b` off `P_{β+1}` with `w < φ_β(b)`; the proof of `R2.lvPhLev`, which is the
  case `w = y`; the case `w = β` covers the **strongly critical levels `β > y`**, where `φ_β(0) = β` is not a value
  of `η ↦ ϑʸ(Ω₁·β + η)` (those values exceed `β`, [W07a] Lemma 3.30));
* `smB_low` (`B_n(Ω₁·β + e) = Ω₁·B_n β + B_n e` for `β, e < c_{n+1}`);
* `smVtU_low` (**`B_n(ϑᵗ(η)) = ϑ^{B_n τ}(B_n η)` for every `η ∈ Tᵗ ∩ [Ω₁, Ω₁·Ω₁)`, at every `υ`-point
  `τ ∈ [c_n, c_{n+1})`**, unconditionally: `η = Ω₁·β + e` (`lgQuot_mem`, `vzRem_T`), `ϑᵗ(η) = φ_β(b)` with `b` off
  `P_{β+1}` (`lv_th_P`, `lv_th_notP`), `e = ind_{β,w}(b)` (`smPhLev`, `w = β` if `β > τ` is strongly critical, else
  `w = τ`), `B_n φ_β(b) = φ_{B_n β}(B_n b)` (`Mw.mwB_phi`), `ind_{B_n β, B_n w}(B_n b) = B_n(ind_{β,w}(b))`
  (`Mx.mxInd_move`), and `smPhLev` over `τ' = B_n τ`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Sm

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Rk

variable {S : InaccSeq.{0}}

/-- `β < u` for every `u ∈ P_β` above `w`, when `β ≤ w` or `β` is not strongly critical (`1 ≤ β`). -/
theorem sm_hbu {β w : Ordinal.{0}} (hβ1 : 1 ≤ β) (h : β ≤ w ∨ ¬ SC β) :
    ∀ u, LuP β u → w < u → β < u := by
  intro u hPu hwu
  obtain ⟨j, rfl⟩ := hPu
  refine lt_of_le_of_ne (left_le_veblen _ _) fun e => ?_
  rcases h with h | h
  · exact absurd (e ▸ hwu) (not_lt.2 h)
  · apply h
    have h0 : (0 : Ordinal.{0}) < β := lt_of_lt_of_le zero_lt_one hβ1
    refine mwSC_of_fix h0 (le_antisymm ?_ (left_le_veblen _ _))
    calc veblen β 0 ≤ veblen β j := veblen_le_veblen_iff_right.2 zero_le
      _ = β := e.symm

/-- **THE LEVEL LEMMA with a lower bound `w`**: for a strongly critical `y < Ω₁`, a level `1 ≤ β ∈ Tʸ ∩ Ω₁`, `y ≤ w`
with `w ≤ y` or `w = β`, and `β` below every member of `P_β` above `w`: `φ_β(b) = ϑʸ(Ω₁·β + ind_{β,w}(b))` for `b`
off `P_{β+1}` with `w < φ_β(b)` and `ind_{β,w}(b) ∈ Tʸ ∩ Ω₁` (the proof of `R2.lvPhLev`, its case `w = y`). -/
theorem smPhLev {β y w : Ordinal.{0}} (hy : SC y) (hy1 : y < Om1) (hβ1 : 1 ≤ β) (hβT : β ∈ Tset y)
    (hβΩ : β < Om1) (hyw : y ≤ w) (hwβ : w ≤ y ∨ w = β) (hβu : ∀ u, LuP β u → w < u → β < u) :
    ∀ b, w < veblen β b → ¬ LuP (β + 1) b → lvInd β w b ∈ Tset y → lvInd β w b < Om1 →
      veblen β b = vt y (Om1 * β + lvInd β w b) := by
  have hyE : InE y := gg_SC_eps hy
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hwb hbP hT h1
  have hbv : b < veblen β b :=
    lt_of_le_of_ne (right_le_veblen _ _) (fun e => hbP (luP_succ.2 e.symm))
  apply le_antisymm
  · have hfacts := ul_facts hyE hy1 hβ1 hβT hβΩ hT h1
    have hnP := lv_th_notP hyE hy1 hβ1 hβT hβΩ hT h1
    obtain ⟨b', hb'⟩ := lv_th_P hyE hy1 β hβ1 hβT hβΩ _ hT h1
    have hwb' : w < veblen β b' := by
      rw [hb']
      rcases hwβ with h | h
      · exact h.trans_lt hfacts.2.2.2.1
      · exact h.trans_lt hfacts.2.2.2.2.2.2.1
    have hb'P : ¬ LuP (β + 1) b' := by
      intro hP
      have hfx : veblen β b' = b' := luP_succ.1 hP
      apply hnP
      rw [← hb', hfx]; exact hP
    rcases lt_or_ge b' b with hlt | hge
    · exfalso
      have hmem : b' ∈ lvC β w := ⟨hwb', hb'P⟩
      have hlt' : lvInd β w b' < lvInd β w b := Cd.cdOtp_lt_of_mem hmem hlt
      have hT' := vz_T_down hyE hy1 hT h1 hlt'.le
      have e := IH b' hlt hwb' hb'P hT' (hlt'.trans h1)
      have h3 := ul_eta_lt hyE hy1 hβ1 hβT hβΩ hT' hT h1 hlt'
      rw [← e, hb'] at h3
      exact lt_irrefl _ h3
    · rw [← hb']; exact veblen_le_veblen_iff_right.2 hge
  · refine lv_th_min hyE hy1 hβ1 hβT hβΩ hT h1 (luP_veblen β b) (hyw.trans_lt hwb)
      ((Cd.cdOtp_le_self _ b).trans_lt hbv) (hβu _ (luP_veblen β b) hwb) fun σ hσ => ?_
    obtain ⟨b', hb'C, hb'b, hσe⟩ := ggOtp_onto (lvC β w) b σ hσ
    obtain ⟨hwb', hb'P⟩ := hb'C
    have hσe' : lvInd β w b' = σ := hσe
    have hT' : lvInd β w b' ∈ Tset y := by rw [hσe']; exact vz_T_down hyE hy1 hT h1 hσ.le
    rw [← hσe', ← IH b' hb'b hwb' hb'P hT' (by rw [hσe']; exact hσ.trans h1)]
    exact veblen_lt_veblen_iff_right.2 hb'b

/-- **`B_n(Ω₁·β + e) = Ω₁·B_n β + B_n e`** for `β, e < c_{n+1}`. -/
theorem smB_low {n : ℕ} {β e : Ordinal.{0}} (hβc : β < Bc.bcC S (n + 1)) (hec : e < Bc.bcC S (n + 1)) :
    Bc.bcB S n (Om1 * β + e) = Om1 * Bc.bcB S n β + Bc.bcB S n e := by
  have hcS : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  have hcL : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  obtain ⟨hDz, hBz⟩ := rkB_Om1mul (n := n) hcS hcL β (GgCl.small hβc)
  rw [Rj.rj_Om1, (mvB_add (k := n) hDz (mvD_of_lt (hec.trans hcL))).2, hBz]

/-- **`B_n` commutes with `ϑᵗ` on `Tᵗ ∩ [Ω₁, Ω₁·Ω₁)`** at every `υ`-point `τ = υ_ξ ∈ [c_n, c_{n+1})`. -/
theorem smVtU_low {n : ℕ} {ξ : Ordinal.{0}} (hc : Bc.bcC S n ≤ upsilon ξ) (hτc : upsilon ξ < Bc.bcC S (n + 1)) :
    ∀ η ∈ Tset (upsilon ξ), Om1 ≤ η → η < Om1 * Om1 →
      Bc.bcB S n (vt (upsilon ξ) η) = vt (Bc.bcB S n (upsilon ξ)) (Bc.bcB S n η) := by
  intro η hηT hη1 hη11
  obtain ⟨hξ0, hξ1lt, ξ', hBξ, hBξ1⟩ := smPrem hc hτc
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hcS : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  have hOm : Nc.ncL S ω < Om1 := by rw [Br.Om1_eq]; exact InaccSeq.psi_lt Low.InR_Om_one _
  have hτL0 : upsilon ξ < Nm.Pv S (Om ω + Nc.ncPp S * ω) := by
    rw [← Lw.lw_L_eq S]; exact hτc.trans hLw
  have hτSC : SC (upsilon ξ) := mvUps_SC hξ0 hτL0
  have hτE : InE (upsilon ξ) := gg_SC_eps hτSC
  have hτ1 : upsilon ξ < Om1 := (Rt.rt_lt_Om1 hτc).1
  have hτL : upsilon ξ < Nc.ncL S ω := hτc.trans hLw
  -- `τ' = B_n τ = υ_{ξ'}`
  have hξ'0 : ξ' ≠ 0 := by
    rintro rfl
    have hLω : Nc.ncL S ω ≤ Bc.bcB S n (upsilon ξ) := by
      rw [← Bc.bcB_base (S := S) n]
      rcases eq_or_lt_of_le hc with e | hlt
      · rw [← e]; exact le_rfl
      · exact ((Bc.bcB_lt_iff (Qq.qqL_lt_omega S (n + 1)) hτL).2 hlt).le
    rw [hBξ, upsilon_zero] at hLω
    exact absurd (lt_of_lt_of_le (Lw.lw_L_SC S ω).1 hLω) (lt_irrefl _)
  have hτ'L1 : upsilon ξ' < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S, ← hBξ]; exact Bc.bcB_bound' S n _ hτc
  have hτ'SC : SC (upsilon ξ') := mvUps_SC hξ'0 hτ'L1
  have hτ'E : InE (upsilon ξ') := gg_SC_eps hτ'SC
  have hτ'1 : upsilon ξ' < Om1 := by rw [Br.Om1_eq]; exact hτ'L1.trans (Nm.Pv_lt_Om1 S _)
  have hu1 : upsilon (ξ + 1) < Om1 := (hξ1lt.trans hLw).trans hOm
  have hu1' : upsilon (ξ' + 1) < Om1 := by
    rw [← hBξ1, Br.Om1_eq]
    exact (Bc.bcB_bound n _ hξ1lt).trans (InaccSeq.psi_lt Low.InR_Om_one _)
  have hTm' : ∀ a, a < upsilon (ξ' + 1) → a ∈ Tset (upsilon ξ') := by
    intro a ha
    have h := upsilon_succ_T ξ' (by rw [succ_eq_add_one]; exact hu1') a (ha.trans hu1')
    rw [if_neg hξ'0] at h
    exact h.2 (by rw [succ_eq_add_one]; exact ha)
  obtain ⟨m, -, -, hmin, hmT, -⟩ := T_next (Or.inr hτE) hτ1
  have hmle : m ≤ upsilon (ξ + 1) :=
    hmin _ (Tp.tpUps_lt_iff.2 (lt_add_one ξ)) (upsPt_upsilon (lt_of_le_of_lt zero_le (lt_add_one ξ))).2
  have hTlt : ∀ a ∈ Tset (upsilon ξ), a < Om1 → a < upsilon (ξ + 1) := fun a ha ha1 =>
    ((hmT a ha1).1 ha).trans_le hmle
  have hBlt : ∀ a, a < upsilon (ξ + 1) → Bc.bcB S n a < upsilon (ξ' + 1) := fun a ha => by
    rw [← hBξ1]; exact (Bc.bcB_lt_iff ((ha.trans hξ1lt).trans hLw) (hξ1lt.trans hLw)).2 ha
  -- `η = Ω₁·β + e`
  obtain ⟨hdec, he1⟩ := vz_div_Om1 η
  have hβΩ : η / Om1 < Om1 := (Ordinal.lt_mul_iff_div_lt Rj.rj_Om1_pos.ne').1 hη11
  have hη2 : η < OmTwo := by rw [← hdec]; exact lkcMul_lt hβΩ he1
  have hβT : η / Om1 ∈ Tset (upsilon ξ) := lgQuot_mem hτE hτ1 hηT hη11
  have heT : η % Om1 ∈ Tset (upsilon ξ) := vzRem_T hτE hτ1 hηT hη2 hdec.symm (dvd_mul_right _ _) he1
  set β := η / Om1 with hβdef
  set e := η % Om1 with hedef
  have hβ1 : 1 ≤ β := by
    refine one_le_iff_ne_zero.2 fun h0 => ?_
    rw [h0, mul_zero, zero_add] at hdec
    exact absurd (hdec ▸ he1) (not_lt.2 hη1)
  -- the value `x = ϑᵗ(Ω₁·β + e) = φ_β(b)`
  set x := vt (upsilon ξ) (Om1 * β + e) with hxdef
  obtain ⟨-, -, hxT, hτx, hx1, -, hβx, hex⟩ := ul_facts hτE hτ1 hβ1 hβT hβΩ heT he1
  have hxu : x < upsilon (ξ + 1) := hTlt x hxT hx1
  have hxc : x < Bc.bcC S (n + 1) := hxu.trans hξ1lt
  have hxL : x < Nc.ncL S ω := hxc.trans hLw
  have hβc : β < Bc.bcC S (n + 1) := hβx.trans hxc
  have hβL : β < Nc.ncL S ω := hβc.trans hLw
  have hec : e < Bc.bcC S (n + 1) := hex.trans hxc
  obtain ⟨b, hbx0⟩ := lv_th_P hτE hτ1 β hβ1 hβT hβΩ e heT he1
  have hbx : veblen β b = x := hbx0
  have hnP : ¬ LuP (β + 1) x := lv_th_notP hτE hτ1 hβ1 hβT hβΩ heT he1
  have hbP : ¬ LuP (β + 1) b := by
    intro hP
    apply hnP
    rw [← hbx, luP_succ.1 hP]; exact hP
  have hbφ : b < veblen β b :=
    lt_of_le_of_ne (right_le_veblen _ _) (fun h => hbP (luP_succ.2 h.symm))
  have hbx' : b < x := by rw [← hbx]; exact hbφ
  have hβφ : β < veblen β b := by rw [hbx]; exact hβx
  have hbL : b < Nc.ncL S ω := hbx'.trans hxL
  -- the lower bound `w`
  classical
  set w := if upsilon ξ < β ∧ SC β then β else upsilon ξ with hwdef
  have hww : (upsilon ξ < β ∧ SC β ∧ w = β) ∨ (¬ (upsilon ξ < β ∧ SC β) ∧ w = upsilon ξ) := by
    by_cases hc' : upsilon ξ < β ∧ SC β
    · exact Or.inl ⟨hc'.1, hc'.2, by rw [hwdef, if_pos hc']⟩
    · exact Or.inr ⟨hc', by rw [hwdef, if_neg hc']⟩
  have hτw : upsilon ξ ≤ w := by
    rcases hww with ⟨h, -, hw⟩ | ⟨-, hw⟩
    · rw [hw]; exact h.le
    · rw [hw]
  have hwβ : w ≤ upsilon ξ ∨ w = β := by
    rcases hww with ⟨-, -, hw⟩ | ⟨-, hw⟩
    · exact Or.inr hw
    · exact Or.inl hw.le
  have hwSC : SC w := by
    rcases hww with ⟨-, h, hw⟩ | ⟨-, hw⟩
    · rw [hw]; exact h
    · rw [hw]; exact hτSC
  have hwx : w < x := by
    rcases hwβ with h | h
    · exact h.trans_lt hτx
    · rw [h]; exact hβx
  have hwL : w < Nc.ncL S ω := hwx.trans hxL
  have hβu : ∀ u, LuP β u → w < u → β < u := by
    refine sm_hbu hβ1 ?_
    rcases hww with ⟨-, -, hw⟩ | ⟨h, hw⟩
    · exact Or.inl hw.ge
    · rcases le_or_gt β (upsilon ξ) with h' | h'
      · exact Or.inl (hw ▸ h')
      · exact Or.inr fun hs => h ⟨h', hs⟩
  have hwφ : w < veblen β b := by rw [hbx]; exact hwx
  have hindb : lvInd β w b ≤ b := Cd.cdOtp_le_self _ b
  have hindT : lvInd β w b ∈ Tset (upsilon ξ) := vz_T_down hτE hτ1 hxT hx1 (hindb.trans hbx'.le)
  have hind1 : lvInd β w b < Om1 := (hindb.trans_lt hbx').trans hx1
  have hlev := smPhLev hτSC hτ1 hβ1 hβT hβΩ hτw hwβ hβu b hwφ hbP hindT hind1
  have heind : e = lvInd β w b := by
    rcases lt_trichotomy e (lvInd β w b) with h | h | h
    · have := ul_eta_lt hτE hτ1 hβ1 hβT hβΩ heT hindT hind1 h
      rw [← hlev, hbx] at this; exact absurd this (lt_irrefl _)
    · exact h
    · have := ul_eta_lt hτE hτ1 hβ1 hβT hβΩ hindT heT he1 h
      rw [← hlev, hbx] at this; exact absurd this (lt_irrefl _)
  -- the image
  have hDβ : MvD S β := mvD_of_lt hβL
  have hDb : MvD S b := mvD_of_lt hbL
  obtain ⟨-, hBφ⟩ := mwB_phi (k := n) hDβ hDb hβφ hbφ
  have hBx : Bc.bcB S n x = veblen (Bc.bcB S n β) (Bc.bcB S n b) := by rw [← hbx]; exact hBφ
  have hBxu : Bc.bcB S n x < upsilon (ξ' + 1) := hBlt x hxu
  have hBx1 : Bc.bcB S n x < Om1 := hBxu.trans hu1'
  have hBβx : Bc.bcB S n β < Bc.bcB S n x := (Bc.bcB_lt_iff hβL hxL).2 hβx
  have hBbx : Bc.bcB S n b < Bc.bcB S n x := (Bc.bcB_lt_iff hbL hxL).2 hbx'
  have hBwx : Bc.bcB S n w < Bc.bcB S n x := (Bc.bcB_lt_iff hwL hxL).2 hwx
  have hBβT : Bc.bcB S n β ∈ Tset (upsilon ξ') := hTm' _ (hBβx.trans hBxu)
  have hBβΩ : Bc.bcB S n β < Om1 := (hBβx.trans hBxu).trans hu1'
  have hBβ1 : 1 ≤ Bc.bcB S n β := by
    have := Tp.tpB_le (n := n) hβL hβ1; rwa [mwB_one] at this
  have hτ'w : upsilon ξ' ≤ Bc.bcB S n w := by rw [← hBξ]; exact Tp.tpB_le hwL hτw
  have hwβ' : Bc.bcB S n w ≤ upsilon ξ' ∨ Bc.bcB S n w = Bc.bcB S n β := by
    rcases hwβ with h | h
    · left; rw [← hBξ]; exact Tp.tpB_le hτL h
    · right; rw [h]
  have hβu' : ∀ u, LuP (Bc.bcB S n β) u → Bc.bcB S n w < u → Bc.bcB S n β < u := by
    refine sm_hbu hBβ1 ?_
    rcases hww with ⟨-, -, hw⟩ | ⟨h, hw⟩
    · exact Or.inl (by rw [hw])
    · rcases le_or_gt β (upsilon ξ) with h' | h'
      · exact Or.inl (by rw [hw]; exact Tp.tpB_le hτL h')
      · exact Or.inr fun hs => h ⟨h', (mxB_SC_iff hβL).1 hs⟩
  have hBbP : ¬ LuP (Bc.bcB S n β + 1) (Bc.bcB S n b) := by
    intro hP
    have h := luP_succ.1 hP
    rw [← hBx] at h
    exact absurd h hBbx.ne'
  have hBwφ : Bc.bcB S n w < veblen (Bc.bcB S n β) (Bc.bcB S n b) := by rw [← hBx]; exact hBwx
  -- the index moves
  have hX : veblen β (Bc.bcC S (n + 1)) = Bc.bcC S (n + 1) := hcS.veblen_right hβc
  have hmove : lvInd (Bc.bcB S n β) (Bc.bcB S n w) (Bc.bcB S n b) = Bc.bcB S n (lvInd β w b) := by
    refine mxInd_move hwSC hwL hβL ?_ hwφ hbφ.ne' hX (hbx'.trans hxc) hLw
    intro hwβ'' hs
    rcases hww with ⟨-, -, hw⟩ | ⟨h, hw⟩
    · rw [hw] at hwβ''; exact lt_irrefl _ hwβ''
    · rw [hw] at hwβ''; exact h ⟨hwβ'', hs⟩
  have hBe : Bc.bcB S n e < Bc.bcB S n x := (Bc.bcB_lt_iff (hec.trans hLw) hxL).2 hex
  have hindT' : lvInd (Bc.bcB S n β) (Bc.bcB S n w) (Bc.bcB S n b) ∈ Tset (upsilon ξ') := by
    rw [hmove, ← heind]; exact hTm' _ (hBe.trans hBxu)
  have hind1' : lvInd (Bc.bcB S n β) (Bc.bcB S n w) (Bc.bcB S n b) < Om1 := by
    rw [hmove, ← heind]; exact (hBe.trans hBxu).trans hu1'
  have hlev' := smPhLev hτ'SC hτ'1 hBβ1 hBβT hBβΩ hτ'w hwβ' hβu' _ hBwφ hBbP hindT' hind1'
  rw [hmove, ← heind] at hlev'
  have hηeq : η = Om1 * β + e := hdec.symm
  rw [hBξ, hηeq, smB_low hβc hec, hBx, hlev']

end Googology.Trans.PoR.InaccPsi.R2.Sm
