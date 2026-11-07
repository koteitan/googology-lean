import Googology.Trans.PoR.InaccPsi.R2.QdLay

/-!
# QdPast: `Zm.ZmPastAt S c` FOR EVERY `c < B₃` (WITH LEMMA IMG AT THE VEBLEN LEVELS)

As `Qc.qc_past` up to `B₃`.  The Veblen levels `γ_n = E₂, φ(E₂, 0), φ(φ(E₂, 0), 0), …` (`qdTw`) have the leaves `0`
and `1` and are cofinal in `Γ_{Ω₂+1}`; the fixed points `Hᵛ_{γ_n}(0)` of `Γ` (`qdF`) are in `[B₂, B₃)`, have gate
`0` (`Qd.qd_H_gate`), and are cofinal in `B₃` (their supremum `v < B₃` would have a level `λ < γ_n` with leaves below
it, fixing every `Hᵛ_{γ_m}(0)`, `m ≥ n` large, so `v` itself).  So every `B < Γ(c+1) < B₃` is below a fixed point with
a layer (`Qd.qd_layAt`).

* `qdTw`, `qdTw_facts`, `qdTw_cof` (**the levels are cofinal in `Γ_{Ω₂+1}`**), `qdF`, `qdF_facts`, `qdF_le_succ`,
  `qdF_mono`, `qdF_cof` (**the fixed points `Hᵛ_{γ_n}(0)` are cofinal in `B₃`**);
* `qd_past` (**`ZmPastAt S c` for every `c < B₃`**, with the atom system `Qt.qtU S`).

No new axiom.  New definitions: `qdTw`, `qdF`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Zm Googology.Trans.PoR.InaccPsi.R2.Va
  Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Qc Googology.Trans.PoR.InaccPsi.R2.Qt Googology.Trans.PoR.InaccPsi.R2.Gl

/-- **The Veblen levels `E₂, φ(E₂, 0), …`.** -/
noncomputable def qdTw (n : ℕ) : Ordinal.{0} := (fun a => veblen a 0)^[n] ucE

/-- **The levels**: `E₂ ≤ γ_n < Γ_{Ω₂+1}`, leaves `0` and `1`. -/
theorem qdTw_facts : ∀ n, ucE ≤ qdTw n ∧ qdTw n < qdG2 ∧ ∀ d ∈ qdComps (qdTw n), d ≤ 1
  | 0 => ⟨le_rfl, qd_E_lt_G2, fun d hd => (qdComps_E2 d hd).le⟩
  | n + 1 => by
    obtain ⟨h1, h2, h3⟩ := qdTw_facts n
    have hS := qdG2_spec.1
    have hn : qdTw (n + 1) = veblen (qdTw n) 0 := Function.iterate_succ_apply' _ _ _
    have ha0 : qdTw n ≠ 0 := (lt_of_lt_of_le (uc_SC_Om2.1.trans ucE_gt) h1).ne'
    have hv0 : (0 : Ordinal.{0}) < veblen (qdTw n) 0 := veblen_pos
    have hvG : veblen (qdTw n) 0 < qdG2 := hS.2 _ h2 0 hS.1
    have hOv : OmTwo < veblen (qdTw n) 0 := (ucE_gt.trans_le h1).trans_le (left_le_veblen _ _)
    refine ⟨by rw [hn]; exact h1.trans (left_le_veblen _ _), by rw [hn]; exact hvG, fun d hd => ?_⟩
    rw [hn, qdComps_veb ha0 hv0 hOv hvG, qdComps_small qd_Om2_pos] at hd
    rcases hd with hd | hd
    · exact h3 d hd
    · rw [mem_singleton_iff.1 hd]; exact zero_le

/-- **The levels are cofinal in `Γ_{Ω₂+1}`.** -/
theorem qdTw_cof {γ : Ordinal.{0}} (hγ : γ < qdG2) : ∃ n, γ < qdTw n := by
  have hfix : veblen (nfp (fun a => veblen a 0) ucE) 0 = nfp (fun a => veblen a 0) ucE :=
    nfp_fp isNormal_veblen_zero _
  have hgt : OmTwo < nfp (fun a => veblen a 0) ucE := ucE_gt.trans_le (le_nfp _ _)
  have hle : qdG2 ≤ nfp (fun a => veblen a 0) ucE :=
    qdG2_le (Ru.ruSC_of_veblen (uc_SC_Om2.1.trans hgt) hfix) hgt
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 (hγ.trans_le hle)
  exact ⟨n, hn⟩

theorem qdTw_le_succ (n : ℕ) : qdTw n ≤ qdTw (n + 1) := by
  rw [show qdTw (n + 1) = veblen (qdTw n) 0 from Function.iterate_succ_apply' _ _ _]
  exact left_le_veblen _ _

theorem qdTw_mono : Monotone qdTw := monotone_nat_of_le_succ qdTw_le_succ

/-- **The fixed points `Hᵛ_{γ_n}(0)` of `Γ`.** -/
noncomputable def qdF (n : ℕ) : Ordinal.{0} := qdH (qdTw n) 0

theorem qd_one_lt_Om1' : (1 : Ordinal.{0}) < Om1 := by rw [Rj.rj_Om1]; exact Nm.one_lt_Om1

/-- The leaves of `γ_n` are below every strongly critical `v > Ω₁`. -/
theorem qdTw_vis (n : ℕ) {v : Ordinal.{0}} (hv : Om1 < v) : qdFold id (qdTw n) < v :=
  (qdFold_lt_iff (Rj.rj_Om1_pos.trans hv) _).2 fun d hd =>
    ((qdTw_facts n).2.2 d hd).trans_lt (qd_one_lt_Om1'.trans hv)

/-- **Fixed points of `Γ` in `[B₂, B₃)` with gate `0`.** -/
theorem qdF_facts (S : InaccSeq.{0}) (n : ℕ) :
    gamma (qdF n) = qdF n ∧ tfBG ≤ qdF n ∧ qdF n < qdB ∧ max ω (qdQEt (qdF n)) < Td.tdK S := by
  obtain ⟨h1, hG, hc⟩ := qdTw_facts n
  have hn0 : qdTw n ≠ 0 := (lt_of_lt_of_le (uc_SC_Om2.1.trans ucE_gt) h1).ne'
  have hO : Om1 < qdF n := qdH_gt _ _
  have hS : SC (qdF n) := qdH_SC _ _
  have hFE : InE (qdF n) := Low.opow_eq_self_of_SC hS
  -- a fixed point of `Γ`
  have h1T : (1 : Ordinal.{0}) < qdTw n :=
    (qd_one_lt_Om2.trans ucE_gt).trans_le h1
  have hfix1 : qdH 1 (qdF n) = qdF n := ucG_fix_lower h1T ⟨0, rfl⟩ (by
    rw [qdFold_small id qd_one_lt_Om2]; exact qd_one_lt_Om1'.trans hO)
  have hfix : gamma (qdF n) = qdF n := qd_P_gamma S one_ne_zero hfix1
  -- below `B₃`
  have hFB : qdF n < qdB := by
    unfold qdF
    calc qdH (qdTw n) 0 < qdH (qdTw n) qdB := (qdH_lt_iff _).2 qdB_SC.1
      _ = qdB := qdB_spec hG (qdTw_vis n qdB_gt)
  -- from `B₂` on, with gate `0`
  have hX : ucB ≤ qdF n := qd_H_ge_B2 S (Or.inr fun h => absurd h.1 (not_lt.2 h1))
  have hKE : InE (Td.tdK S) := Low.opow_eq_self_of_SC Td.tdK_SC
  have hgd : ∀ d ∈ qdComps (qdTw n), qdGt d < Td.tdK S := fun d hd => by
    rcases (hc d hd).lt_or_eq with h | h
    · rw [Order.lt_one_iff.1 h, qdGt_zero]; exact hKE.pos
    · rw [h, show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_num, qdGt_nat]
      exact (natCast_lt_omega0 1).trans (omega0_lt_inE hKE)
  have hg := qd_H_gate S hKE hn0 hG (lt_of_le_of_lt zero_le hO) hX hFB hgd (by rw [qdGt_zero]; exact hKE.pos)
  refine ⟨hfix, tfBG_le hfix hO, hFB, max_lt (omega0_lt_inE hKE) ?_⟩
  rw [← qdGt_base' hFE (gl_G0_le hS hO) hFB]
  exact hg

theorem qdF_le_succ (n : ℕ) : qdF n ≤ qdF (n + 1) := by
  rcases (qdTw_le_succ n).lt_or_eq with h | h
  · have hfix : qdH (qdTw n) (qdF (n + 1)) = qdF (n + 1) :=
      ucG_fix_lower h ⟨0, rfl⟩ (qdTw_vis n (qdH_gt _ _))
    calc qdF n = qdH (qdTw n) 0 := rfl
      _ ≤ qdH (qdTw n) (qdF (n + 1)) := (qdH_normal _).strictMono.monotone zero_le
      _ = qdF (n + 1) := hfix
  · unfold qdF; rw [h]

theorem qdF_mono : Monotone qdF := monotone_nat_of_le_succ qdF_le_succ

/-- **The fixed points `Hᵛ_{γ_n}(0)` are cofinal in `B₃`.** -/
theorem qdF_cof {B : Ordinal.{0}} (hB : B < qdB) : ∃ n, B < qdF n := by
  by_contra hcon
  push Not at hcon
  have hbdd : BddAbove (range qdF) := ⟨B, by rintro _ ⟨n, rfl⟩; exact hcon n⟩
  have hne : (range qdF).Nonempty := ⟨qdF 0, 0, rfl⟩
  set v := sSup (range qdF) with hv
  have hvB : v ≤ B := csSup_le hne (by rintro _ ⟨n, rfl⟩; exact hcon n)
  have hSC : SC v := gc_SC_iSup (fun n => qdH_SC (qdTw n) 0)
  have hFv : ∀ n, qdF n ≤ v := fun n => le_csSup hbdd ⟨n, rfl⟩
  have hO : Om1 < v := (qdH_gt (qdTw 0) 0).trans_le (hFv 0)
  obtain ⟨hlG, hlc, hlne, -, -⟩ := qdLev_spec hSC hO (qd_nf_of_lt hSC hO (hvB.trans_lt hB))
  obtain ⟨n, hn⟩ := qdTw_cof hlG
  obtain ⟨s, ⟨m, rfl⟩, hsm⟩ := exists_lt_of_lt_csSup hne hlc
  set N := max n m with hN
  have hfix : ∀ k, N ≤ k → qdH (qdLev v) (qdF k) = qdF k := fun k hk =>
    ucG_fix_lower (hn.trans_le (qdTw_mono ((le_max_left _ _).trans hk))) ⟨0, rfl⟩
      (hsm.trans_le (qdF_mono ((le_max_right _ _).trans hk)))
  apply hlne
  refine le_antisymm ?_ (qdH_le_self _ _)
  rw [hv, (qdH_normal (qdLev v)).map_sSup hne hbdd]
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
  rcases le_total N k with hk | hk
  · rw [hfix k hk]; exact hFv k
  · calc qdH (qdLev v) (qdF k) ≤ qdH (qdLev v) (qdF N) := (qdH_normal _).strictMono.monotone (qdF_mono hk)
      _ = qdF N := hfix N le_rfl
      _ ≤ sSup (range qdF) := hFv N

/-- **`Zm.ZmPastAt S c` for every `c < B₃`** (with Lemma IMG at the Veblen levels): one atom system `qtU S` with a
layer for every atom index below `Γ(c+1)` (the layer at a fixed point `Hᵛ_{γ_n}(0)` above it). -/
theorem qd_past (S : InaccSeq.{0}) (hI : QdImgH) : ∀ c, c < qdB → ZmPastAt S c := by
  intro c hc
  refine ⟨qtU S, qtU_ok S, fun B hB => ?_⟩
  have hBB : B < qdB := hB.trans (qd_gcG_lt_B3 S (qdB_SC.isSuccLimit.add_one_lt hc))
  obtain ⟨n, hn⟩ := qdF_cof hBB
  obtain ⟨hf, hb, hFB, hK⟩ := qdF_facts S n
  exact qt_layA_mono hn.le (qd_layAt S hI hf hb hFB hK)

end Googology.Trans.PoR.InaccPsi.R2.Qd
