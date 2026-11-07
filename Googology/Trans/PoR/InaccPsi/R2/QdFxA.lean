import Googology.Trans.PoR.InaccPsi.R2.QdMxG
import Googology.Trans.PoR.InaccPsi.R2.QcFxA

/-!
# QdFxA: TOOLS FOR THE TOP AT A FIXED POINT OF `Γ` BELOW `B₃`

As `Qc.QcFxA` with `vD`, `qdA`, `qdGt` and the Veblen levels.

* `vD_dec'` (**the Cantor clause of `vD` on `[G, B₃)`**), `qdRI_low`, `qdA_atom'`, `vD_atom'` (**a base atom `Γ(i)`,
  `i < Γ(i)`, below `B₃` reads `gq(qdRI i)`**), `qdRI_noFix`;
* `qd_off_gate'` (the offset `j − (F+1)` keeps the gate of `j` on `[G, B₃)`), `qdLv_congr`;
* `yBd_zero`, `yBd_max`, `yBd_fold` (**`YBd` of the largest value on the leaves**);
* `qd_tower` (**every level below `Γ_{Ω₁+1}` is below a tower `Ω₁+1, φ(Ω₁+1, 0), …` of data `1`**), `qdBd_vt`
  (**a point `ϑˣ(Ω₁·N + K)` with its data and `K` below a Veblen-level point is one**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yw
  Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Va Googology.Trans.PoR.InaccPsi.R2.Tl
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Yr
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Zm Googology.Trans.PoR.InaccPsi.R2.Tf
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Qc

/-- **The Cantor clause of `vD` on `[G, B₃)`.** -/
theorem vD_dec' {c : Ordinal.{0}} (h : gcG 0 ≤ c) (hB : c < qdB) (x : Ordinal.{0}) :
    vD c x = qdA (guE c) x ^ vD (log (guE c) c) x * vD (c / guE c ^ log (guE c) c) x +
      vD (c % guE c ^ log (guE c) c) x := by
  rcases lt_or_ge c ucB with hX | hX
  · obtain ⟨-, -, -, -, -, hkc, hrc, hdc⟩ := gl_parts (yh_gfE_le h)
    have hec := gl_E_le (yh_gfE_le h)
    rw [vD_low hX, vQ_dec' h hX x, qdA_low (hec.trans_lt hX), vD_low (hkc.trans hX), vD_low (hdc.trans hX),
      vD_low (hrc.trans hX)]
  · exact vD_dec hX hB x

/-- Below `B₂` the atom index reading is `Qc.qcI`. -/
theorem qdRI_low {j : Ordinal.{0}} (hj : j < ucB) (x : Ordinal.{0}) : qdRI j x = qcI j x := by
  unfold qdRI qcI
  split_ifs
  · rw [vD_low ((va_fpG_le j).trans_lt hj), vD_low ((Ordinal.sub_le_self _ _).trans_lt hj)]
  · rw [vD_low hj]

/-- **A base atom `Γ(j) < B₃`, `j < Γ(j)`, reads `gq(qdRI j)` as a base.** -/
theorem qdA_atom' {e : Ordinal.{0}} (hB : e < qdB) (hA : YhAt e) (hi : yhJ e < e) (x : Ordinal.{0}) :
    qdA e x = gq (qdRI (yhJ e) x) x := by
  rcases lt_or_ge e ucB with hX | hX
  · rw [qdA_low hX, qcA_atom' hX hA hi, qdRI_low (hi.trans hX)]
  · unfold qdA; rw [if_pos ⟨hX, hB⟩, if_pos hA, if_pos hi]

/-- **A base atom `Γ(i) < B₃`, `i < Γ(i)`, reads `gq(qdRI i)`.** -/
theorem vD_atom' {i : Ordinal.{0}} (hi : i < gcG i) (hB : gcG i < qdB) (x : Ordinal.{0}) :
    vD (gcG i) x = gq (qdRI i x) x := by
  have hE : InE (gcG i) := Low.opow_eq_self_of_SC (gcG_SC i)
  have hi' : yhJ (gcG i) < gcG i := by rw [yhJ_gcG]; exact hi
  rw [vD_base' hE (gcG_le zero_le) hB, qdA_atom' hB (yhAt_gcG i) hi', yhJ_gcG]

/-- Below the first fixed point of `Γ` above `Ω₁` an atom index reads itself. -/
theorem qdRI_noFix {j : Ordinal.{0}} (hj : ¬ tfBG < j) (x : Ordinal.{0}) : qdRI j x = vD j x := by
  unfold qdRI; rw [if_neg (va_noFixG hj)]

/-- **The offset `j − (F+1)` keeps the gate of `j` up to `ω`** on `[G, B₃)` (`F` an `ε`-number code). -/
theorem qd_off_gate' {F j : Ordinal.{0}} (hFE : InE F) (hFG : gcG 0 ≤ F) (hjB : j < qdB) (hj : F < j) :
    qdGt (j - (F + 1)) ≤ max ω (qdGt j) := by
  rcases lt_or_ge j ucB with hjX | hjX
  · rw [qdGt_low hjX, qdGt_low ((Ordinal.sub_le_self _ _).trans_lt hjX)]
    exact qc_off_gate' hFE hFG hjX hj
  rcases le_or_gt ucB F with hXF | hFX
  · exact qd_off_gate hFE hXF hjB hj
  · -- `F < B₂ ≤ j`: the prefix is absorbed
    have hF1 : (F + 1) * ω ≤ j := by
      have h1 : F + 1 < ucB := (ev_isSuccLimit_of_inE qd_B2_E).add_one_lt hFX
      exact (qd_B2_E.mul_lt h1 (omega0_lt_inE qd_B2_E)).le.trans hjX
    rw [Ordinal.sub_eq_of_add_eq (add_eq_right_iff_mul_omega0_le.2 hF1)]
    exact le_max_right _ _

/-- **`qdLv f z` depends on `f` only at the leaves of `z`.** -/
theorem qdLv_congr {f g : Ordinal.{0} → Ordinal.{0}} :
    ∀ z : Ordinal.{0}, (∀ d ∈ qdComps z, f d = g d) → qdLv f z = qdLv g z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro h
  by_cases hz : OmTwo < z ∧ z < qdG2
  · by_cases hE : ω ^ z = z
    · have hc := qdComps_phi hz.1 hz.2 hE
      rw [qdLv_phi f hz.1 hz.2 hE, qdLv_phi g hz.1 hz.2 hE,
        IH _ (qd_inv1_lt hz.1 hz.2) fun d hd => h d (by rw [hc]; exact Or.inl hd),
        IH _ (Ss.ss_inv2_lt hE) fun d hd => h d (by rw [hc]; exact Or.inr hd)]
    · have hc := qdComps_cnf hz.1 hz.2 hE
      rw [qdLv_cnf f hz.1 hz.2 hE, qdLv_cnf g hz.1 hz.2 hE,
        IH _ (Ss.ss_log_lt (qd_Om2_pos.trans hz.1).ne' hE) fun d hd => h d (by rw [hc]; exact Or.inl hd),
        IH _ (rj_mod_lt (qd_Om2_pos.trans hz.1).ne') fun d hd => h d (by rw [hc]; exact Or.inr hd)]
  · rcases lt_trichotomy z OmTwo with h1 | rfl | h1
    · rw [qdLv_small f h1, qdLv_small g h1]
      exact h z (by rw [qdComps_small h1]; exact mem_singleton _)
    · rw [qdLv_Om2, qdLv_Om2]
    · rw [qdLv, dif_neg hz, if_neg (not_lt.2 h1.le), if_neg h1.ne', qdLv, dif_neg hz, if_neg (not_lt.2 h1.le),
        if_neg h1.ne']

section Bd

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem yBd_zero : YBd x 0 := yBd_of_qc (qcBd_zero hx hx1)

omit hx hx1 in
theorem yBd_max {a b : Ordinal.{0}} (ha : YBd x a) (hb : YBd x b) : YBd x (max a b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; exact hb
  · rw [max_eq_left h]; exact ha

/-- **`YBd` of the largest value on the leaves.** -/
theorem yBd_fold (f : Ordinal.{0} → Ordinal.{0}) :
    ∀ z : Ordinal.{0}, (∀ d ∈ qdComps z, YBd x (f d)) → YBd x (qdFold f z) := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro h
  by_cases hz : OmTwo < z ∧ z < qdG2
  · by_cases hE : ω ^ z = z
    · have hc := qdComps_phi hz.1 hz.2 hE
      rw [qdFold_phi f hz.1 hz.2 hE]
      exact yBd_max (IH _ (qd_inv1_lt hz.1 hz.2) fun d hd => h d (by rw [hc]; exact Or.inl hd))
        (IH _ (Ss.ss_inv2_lt hE) fun d hd => h d (by rw [hc]; exact Or.inr hd))
    · have hc := qdComps_cnf hz.1 hz.2 hE
      rw [qdFold_cnf f hz.1 hz.2 hE]
      exact yBd_max (IH _ (Ss.ss_log_lt (qd_Om2_pos.trans hz.1).ne' hE) fun d hd => h d (by rw [hc]; exact Or.inl hd))
        (IH _ (rj_mod_lt (qd_Om2_pos.trans hz.1).ne') fun d hd => h d (by rw [hc]; exact Or.inr hd))
  · rcases lt_trichotomy z OmTwo with h1 | rfl | h1
    · rw [qdFold_small f h1]; exact h z (by rw [qdComps_small h1]; exact mem_singleton _)
    · rw [qdFold_Om2]; exact yBd_zero hx hx1
    · rw [qdFold, dif_neg hz, if_neg (not_lt.2 h1.le)]; exact yBd_zero hx hx1

end Bd

/-- **Every level below `Γ_{Ω₁+1}` is below a tower point of data `1`.** -/
theorem qd_tower {N : Ordinal.{0}} (hN : N < ggGam) :
    ∃ N', N < N' ∧ Om1 ≤ N' ∧ N' < ggGam ∧ tfDat N' ≤ 1 := by
  have hGS : SC (ggGam : Ordinal.{0}) := ggGam_spec.1
  have hOG : Om1 < (ggGam : Ordinal.{0}) := by rw [rj_Om1]; exact ggGam_spec.2
  set τ : ℕ → Ordinal.{0} := fun n => (fun a => veblen a 0)^[n] (Om1 + 1) with hτ
  have hτG : ∀ n, τ n < ggGam := by
    intro n
    induction n with
    | zero => exact hGS.isSuccLimit.add_one_lt hOG
    | succ n ih =>
      show (fun a => veblen a 0)^[n + 1] (Om1 + 1) < ggGam
      rw [Function.iterate_succ_apply']
      exact hGS.2 _ ih 0 hGS.1
  have hτO : ∀ n, Om1 + 1 ≤ τ n := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      show Om1 + 1 ≤ (fun a => veblen a 0)^[n + 1] (Om1 + 1)
      rw [Function.iterate_succ_apply']
      exact ih.trans (left_le_veblen _ _)
  have hτd : ∀ n, tfDat (τ n) ≤ 1 := by
    intro n
    induction n with
    | zero => exact tfDat_Om1_succ.le
    | succ n ih =>
      show tfDat ((fun a => veblen a 0)^[n + 1] (Om1 + 1)) ≤ 1
      rw [Function.iterate_succ_apply']
      have ha0 : τ n ≠ 0 := (lt_of_lt_of_le (lt_of_le_of_lt zero_le (lt_add_one _)) (hτO n)).ne'
      have hv0 : (0 : Ordinal.{0}) < veblen (τ n) 0 := veblen_pos
      have hOv : Om1 < veblen (τ n) 0 := ((lt_add_one _).trans_le (hτO n)).trans_le (left_le_veblen _ _)
      have hvG : veblen (τ n) 0 < ggGam := hGS.2 _ (hτG n) 0 hGS.1
      rw [tfDat_eq_ss _ hvG, Ss.ssDat_eq_phi hOv hvG (qd_eps_veb ha0), invVeblen₁_veblen hv0,
        invVeblen₂_veblen ha0 hv0, Ss.ssDat_small Rj.rj_Om1_pos, ← tfDat_eq_ss _ (hτG n)]
      exact max_le ih zero_le
  have hfix : veblen (nfp (fun a => veblen a 0) (Om1 + 1)) 0 = nfp (fun a => veblen a 0) (Om1 + 1) :=
    nfp_fp isNormal_veblen_zero _
  have hgt : Om1 < nfp (fun a => veblen a 0) (Om1 + 1) := (lt_add_one _).trans_le (le_nfp _ _)
  have hle : ggGam ≤ nfp (fun a => veblen a 0) (Om1 + 1) :=
    ggGam_le (Ru.ruSC_of_veblen (Rj.rj_Om1_pos.trans hgt) hfix) (by rw [← rj_Om1]; exact hgt)
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 (hN.trans_le hle)
  exact ⟨τ n, hn, le_self_add.trans (hτO n), hτG n, hτd n⟩

/-- **A point `ϑˣ(Ω₁·N + K)` with its data and `K` below a Veblen-level point is below one.** -/
theorem qdBd_vt {x N K : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hNG : N < ggGam)
    (hNT : tfDat N ∈ Tset x) (hK : K ∈ Tset x) (hK1 : K < Om1) (hb : QdBd x (max (tfDat N) K)) :
    QdBd x (vt x (Om1 * N + K)) := by
  obtain ⟨N₀, hN₀2, hN₀G, hN₀x, hb₀⟩ := qdBd_up hx hx1 hb
  obtain ⟨N₁, hNN₁, hN₁O, hN₁G, hN₁d⟩ := qd_tower hNG
  obtain ⟨o1, -, -⟩ := qc_O2_facts
  have hN₀1 : Om1 ≤ N₀ := o1.trans hN₀2
  have hN₁x : tfDat N₁ < x := hN₁d.trans_lt (lu_one_lt_E hx)
  set N' := max N₀ N₁ with hN'
  have hN'1 : Om1 ≤ N' := hN₀1.trans (le_max_left _ _)
  have hN'G : N' < ggGam := max_lt hN₀G hN₁G
  have hN'x : tfDat N' < x := by
    rcases le_total N₀ N₁ with h | h
    · rw [hN', max_eq_right h]; exact hN₁x
    · rw [hN', max_eq_left h]; exact hN₀x
  have hmono := qd_vt_mono hx hx1 hN₀1 hN₀x hN'G hN'x (le_max_left _ _)
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  refine ⟨N', hN'1, hN'G, hN'x, ?_⟩
  have harg : Om1 * N + K < Om1 * N' + 0 := by
    rw [add_zero]
    calc Om1 * N + K < Om1 * N + Om1 := (add_lt_add_iff_left _).2 hK1
      _ = Om1 * (N + 1) := (mul_add_one _ _).symm
      _ ≤ Om1 * N' := mul_le_mul_right (Order.add_one_le_of_lt (hNN₁.trans_le (le_max_right _ _))) _
  have h := tfVt_lt hx hx1 hN'1 (hN'G.trans tf_gg_lt_BG) (tf_M_le h0Ω harg) hNT hK hK1
    (mem_T_of_le hx hx1 hN'x.le) h0T h0Ω harg
    (by rw [add_zero]; exact ((le_max_left _ _).trans_lt hb₀).trans_le hmono)
    (by rw [add_zero]; exact ((le_max_right _ _).trans_lt hb₀).trans_le hmono)
  rwa [add_zero] at h

end Googology.Trans.PoR.InaccPsi.R2.Qd
