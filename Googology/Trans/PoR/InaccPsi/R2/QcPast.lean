import Googology.Trans.PoR.InaccPsi.R2.QcLay

/-!
# QcPast: THE LAYERS `c < B₂` FROM THE ATOM SYSTEM `qcU` — `Zm.ZmPastAt S c`

As `Va.vsDirectX` up to `B₂`.  The levels `Ω₂, Ω₂^{Ω₂}, …` (`qcTw`, components `0` and `1`) are cofinal in
`E₂ = ε_{Ω₂+1}`, so the fixed points `H_{qcTw n}(0)` of `Γ` (gate below every `ε`-number, `Qc.qc_H_gate`) are cofinal in
`B₂` (`qcF_cof`: their supremum would be fixed by its own level).  A layer at each of them (`Qc.qs_layAt`) covers every
atom index below it.

* `qcTw`, `qcTw_facts` (the levels: components at most `1`, below `E₂`), `qcTw_mono`, `qcTw_cof` (**cofinal in
  `E₂`**);
* `qcF`, `qcF_facts` (**fixed points of `Γ` below `B₂` with small gates**), `qcF_mono`, `qcF_cof` (**cofinal in
  `B₂`**);
* `qc_layA_mono`, `qc_past` (**`Zm.ZmPastAt S c` for every `c < B₂`**).

No new axiom.  New definitions: `qcTw`, `qcF`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Zm Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Va
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Lu

/-- **The levels `Ω₂, Ω₂^{Ω₂}, …`.** -/
noncomputable def qcTw : ℕ → Ordinal.{0}
  | 0 => OmTwo
  | n + 1 => OmTwo ^ qcTw n

theorem qc_Om2_E : InE (OmTwo : Ordinal.{0}) := Low.opow_eq_self_of_SC uc_SC_Om2

/-- `Ω₂^γ = ω^{Ω₂·γ}`. -/
theorem qc_Om2_opow (γ : Ordinal.{0}) : OmTwo ^ γ = ω ^ (OmTwo * γ) := by
  conv_lhs => rw [← qc_Om2_E]
  rw [← opow_mul]

/-- `Ω₂^γ = Ω₂^γ·1 + 0` has the components of `γ`, `1` and `0`. -/
theorem qc_comps_pow {γ : Ordinal.{0}} (hγ1 : 1 ≤ γ) (hE : OmTwo ^ γ < ucE) :
    ucComps (OmTwo ^ γ) = ucComps γ ∪ ({1} ∪ {0}) := by
  have h := ucComps_cnf hγ1 one_ne_zero uc_one_lt_Om2 (opow_pos γ uc_SC_Om2.1) (by rw [mul_one, add_zero]; exact hE)
  rw [mul_one, add_zero, ucComps_small uc_SC_Om2.1] at h
  exact h

/-- **The levels**: `1 ≤ γ_n < E₂`, components at most `1`. -/
theorem qcTw_facts : ∀ n, 1 ≤ qcTw n ∧ qcTw n < ucE ∧ ∀ d ∈ ucComps (qcTw n), d ≤ 1
  | 0 => by
    have h1 : (1 : Ordinal.{0}) ≤ OmTwo := uc_one_lt_Om2.le
    have hE : OmTwo ^ (1 : Ordinal.{0}) < ucE := by rw [opow_one]; exact ucE_gt
    refine ⟨h1, ucE_gt, fun d hd => ?_⟩
    have hc := qc_comps_pow le_rfl hE
    rw [opow_one] at hc
    rw [show qcTw 0 = OmTwo from rfl, hc, ucComps_small uc_one_lt_Om2] at hd
    rcases hd with hd | hd | hd
    · rw [mem_singleton_iff.1 hd]
    · rw [mem_singleton_iff.1 hd]
    · rw [mem_singleton_iff.1 hd]; exact zero_le
  | n + 1 => by
    obtain ⟨h1, hE, hc⟩ := qcTw_facts n
    have hE' : OmTwo ^ qcTw n < ucE := by
      rw [qc_Om2_opow]
      have hm : OmTwo * qcTw n < ucE := uc_E_mulPrin ucE_gt hE
      calc ω ^ (OmTwo * qcTw n) < ω ^ ucE := (opow_lt_opow_iff_right one_lt_omega0).2 hm
        _ = ucE := ucE_fix
    refine ⟨show 1 ≤ OmTwo ^ qcTw n from one_le_iff_ne_zero.2 (opow_pos _ uc_SC_Om2.1).ne', hE', fun d hd => ?_⟩
    rw [show qcTw (n + 1) = OmTwo ^ qcTw n from rfl, qc_comps_pow h1 hE'] at hd
    rcases hd with hd | hd | hd
    · exact hc d hd
    · rw [mem_singleton_iff.1 hd]
    · rw [mem_singleton_iff.1 hd]; exact zero_le

theorem qcTw_le_succ (n : ℕ) : qcTw n ≤ qcTw (n + 1) :=
  (right_le_opow _ one_lt_omega0).trans (opow_le_opow_left _ (omega0_lt_inE qc_Om2_E).le)

theorem qcTw_mono : Monotone qcTw := monotone_nat_of_le_succ qcTw_le_succ

/-- The `ω`-tower over `Ω₂ + 1` is below the levels. -/
theorem qcTw_ge : ∀ n : ℕ, (fun x => ω ^ x)^[n] (OmTwo + 1) ≤ qcTw (n + 1)
  | 0 => by
    show OmTwo + 1 ≤ OmTwo ^ OmTwo
    rw [qc_Om2_opow]
    refine (right_le_opow _ one_lt_omega0).trans ((opow_le_opow_iff_right one_lt_omega0).2 ?_)
    calc OmTwo + 1 ≤ OmTwo + OmTwo := add_le_add le_rfl uc_one_lt_Om2.le
      _ = OmTwo * (1 + 1) := by rw [mul_add_one, mul_one]
      _ ≤ OmTwo * OmTwo := mul_le_mul_right (Order.add_one_le_of_lt uc_one_lt_Om2) _
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    show ω ^ ((fun x => ω ^ x)^[n] (OmTwo + 1)) ≤ OmTwo ^ qcTw (n + 1)
    rw [qc_Om2_opow]
    exact (opow_le_opow_iff_right one_lt_omega0).2 ((qcTw_ge n).trans (Ordinal.le_mul_right (qcTw (n + 1))
      uc_SC_Om2.1))

/-- **The levels are cofinal in `E₂`.** -/
theorem qcTw_cof {γ : Ordinal.{0}} (hγ : γ < ucE) : ∃ n, γ < qcTw n := by
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hγ
  exact ⟨n + 1, hn.trans_le (qcTw_ge n)⟩

/-- **The fixed points `H_{γ_n}(0)` of `Γ`.** -/
noncomputable def qcF (n : ℕ) : Ordinal.{0} := ucH (qcTw n) 0

/-- **Fixed points of `Γ` below `B₂` with gates below `K`.** -/
theorem qcF_facts (S : InaccSeq.{0}) (n : ℕ) :
    gamma (qcF n) = qcF n ∧ tfBG ≤ qcF n ∧ qcF n < ucB ∧ max ω (qcQE (qcF n)) < Td.tdK S := by
  obtain ⟨h1, hE, hc⟩ := qcTw_facts n
  have hn0 : qcTw n ≠ 0 := one_le_iff_ne_zero.1 h1
  have hSC : SC (ucH (qcTw n) 0) := ucH_SC _ _
  have hO : Om1 < ucH (qcTw n) 0 := ucH_gt _ _
  have hFE : InE (ucH (qcTw n) 0) := Low.opow_eq_self_of_SC hSC
  have hfix : gamma (ucH (qcTw n) 0) = ucH (qcTw n) 0 := by
    have h := (qc_H_fixG (y := 0) hn0).1
    rw [tf_gcG, gl_absorb hFE hO] at h
    exact h
  have hC : ucC (qcTw n) < ucB := by
    refine (ucC_lt_iff ucB_SC.1 _).2 fun d hd => (hc d hd).trans_lt ?_
    exact lu_one_lt_E (Low.opow_eq_self_of_SC ucB_SC)
  have hFB : qcF n < ucB := by
    unfold qcF
    calc ucH (qcTw n) 0 < ucH (qcTw n) ucB := (ucH_lt_iff _).2 ucB_SC.1
      _ = ucB := ucB_spec hE hC
  have hKE : InE (Td.tdK S) := Low.opow_eq_self_of_SC Td.tdK_SC
  have hgd : ∀ d ∈ ucComps (qcTw n), qcG d < Td.tdK S := fun d hd => by
    rcases (hc d hd).lt_or_eq with h | h
    · rw [Order.lt_one_iff.1 h, qcG_zero]; exact hKE.pos
    · rw [h, show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_num, qcG_nat]
      exact (natCast_lt_omega0 1).trans (omega0_lt_inE hKE)
  have hg := qc_H_gate hKE hn0 hE (ucH_gt (qcTw n) 0 |>.trans_le' zero_le |> fun h => lt_of_le_of_lt zero_le hO)
    hFB hgd (by rw [qcG_zero]; exact hKE.pos)
  refine ⟨hfix, tfBG_le hfix hO, hFB, max_lt (omega0_lt_inE hKE) ?_⟩
  show qcQE (ucH (qcTw n) 0) < Td.tdK S
  rw [← qcG_base' hFE (gl_G0_le hSC hO) hFB]
  exact hg

theorem qcF_le_succ (n : ℕ) : qcF n ≤ qcF (n + 1) := by
  rcases (qcTw_le_succ n).lt_or_eq with h | h
  · have hfix : ucH (qcTw n) (qcF (n + 1)) = qcF (n + 1) := by
      refine ucG_fix_lower h ⟨0, rfl⟩ ?_
      refine (ucC_lt_iff (ucH_SC _ _).1 _).2 fun d hd => ((qcTw_facts n).2.2 d hd).trans_lt ?_
      exact lu_one_lt_E (Low.opow_eq_self_of_SC (ucH_SC _ _))
    calc qcF n = ucH (qcTw n) 0 := rfl
      _ ≤ ucH (qcTw n) (qcF (n + 1)) := (ucH_normal _).strictMono.monotone zero_le
      _ = qcF (n + 1) := hfix
  · unfold qcF; rw [h]

theorem qcF_mono : Monotone qcF := monotone_nat_of_le_succ qcF_le_succ

/-- **The fixed points `H_{γ_n}(0)` are cofinal in `B₂`**: their supremum `v < B₂` would have a level
`λ < γ_n`, and `H_λ` would fix every `H_{γ_m}(0)`, `m ≥ n` large, so `v` itself. -/
theorem qcF_cof {B : Ordinal.{0}} (hB : B < ucB) : ∃ n, B < qcF n := by
  by_contra hcon
  push Not at hcon
  have hbdd : BddAbove (range qcF) := ⟨B, by rintro _ ⟨n, rfl⟩; exact hcon n⟩
  have hne : (range qcF).Nonempty := ⟨qcF 0, 0, rfl⟩
  set v := sSup (range qcF) with hv
  have hvB : v ≤ B := csSup_le hne (by rintro _ ⟨n, rfl⟩; exact hcon n)
  have hSC : SC v := gc_SC_iSup (fun n => ucH_SC (qcTw n) 0)
  have hFv : ∀ n, qcF n ≤ v := fun n => le_csSup hbdd ⟨n, rfl⟩
  have hO : Om1 < v := (ucH_gt (qcTw 0) 0).trans_le (hFv 0)
  obtain ⟨hlE, hlc, hlne, -, -⟩ := ucLev_spec hSC hO (uc_nf_of_lt hSC hO (hvB.trans_lt hB))
  obtain ⟨n, hn⟩ := qcTw_cof hlE
  obtain ⟨s, ⟨m, rfl⟩, hsm⟩ := exists_lt_of_lt_csSup hne hlc
  set N := max n m with hN
  have hfix : ∀ k, N ≤ k → ucH (ucLev v) (qcF k) = qcF k := fun k hk =>
    ucG_fix_lower (hn.trans_le (qcTw_mono ((le_max_left _ _).trans hk))) ⟨0, rfl⟩
      (hsm.trans_le (qcF_mono ((le_max_right _ _).trans hk)))
  apply hlne
  refine le_antisymm ?_ (ucH_le_self _ _)
  rw [hv, (ucH_normal (ucLev v)).map_sSup hne hbdd]
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
  rcases le_total N k with hk | hk
  · rw [hfix k hk]; exact hFv k
  · calc ucH (ucLev v) (qcF k) ≤ ucH (ucLev v) (qcF N) := (ucH_normal _).strictMono.monotone (qcF_mono hk)
      _ = qcF N := hfix N le_rfl
      _ ≤ sSup (range qcF) := hFv N

/-- A layer for `B'` is one for every `B ≤ B'`. -/
theorem qc_layA_mono {A : Zb.ZbAS} {S : InaccSeq.{0}} {B B' : Ordinal.{0}} (h : B ≤ B') (hL : ZmLayA A S B') :
    ZmLayA A S B := by
  obtain ⟨L, T, hBT, rest⟩ := hL
  exact ⟨L, T, (gcG_le h).trans hBT, rest⟩

/-- **`Zm.ZmPastAt S c` for every `c < B₂`**: one atom system `qcU` with a layer for every atom index below
`Γ(c+1)` (the layer at a fixed point `H_{γ_n}(0)` above it). -/
theorem qc_past (S : InaccSeq.{0}) : ∀ c, c < ucB → ZmPastAt S c := by
  intro c hc
  refine ⟨qcU, fun B hB => ?_⟩
  have hBB : B < ucB := hB.trans (qc_gcG_lt_B (ucB_SC.isSuccLimit.add_one_lt hc))
  obtain ⟨n, hn⟩ := qcF_cof hBB
  obtain ⟨hf, hb, hFB, hK⟩ := qcF_facts S n
  exact qc_layA_mono hn.le (qs_layAt S hf hb hFB hK)

end Googology.Trans.PoR.InaccPsi.R2.Qc
