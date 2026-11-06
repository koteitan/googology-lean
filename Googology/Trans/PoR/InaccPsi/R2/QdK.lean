import Googology.Trans.PoR.InaccPsi.R2.QdPi
import Googology.Trans.PoR.InaccPsi.R2.UlUB
import Googology.Trans.PoR.InaccPsi.R2.UiAgree
import Googology.Trans.PoR.InaccPsi.R2.YgIF

/-!
# QdK: THE LEAVES OF A VEBLEN LEVEL ARE BELOW `v` IFF THE LEVEL IS VISIBLE AT `v` (Phase D1)

For a strongly critical `v > Ω₁` and a Veblen level `z < Γ_{Ω₂+1}`: every leaf of `z` is below `v` (`qdP v z`) iff
`z ∈ K_v` (`Ul.UlK S 1 v`, the visibility closure at `Ω₂`, for every `S`).  `⇒`: `z` is built from its leaves and
`Ω₂` by `+`, `ω^·`, finite multiples and `φ`.  `⇐`: by the closure — sums and `φ` keep the leaves below `v`, `Ω_x`
and every collapse `ψ_π`, `π ≠ Ω₂`, is below `Ω₁` or at least `Γ_{Ω₂+1}` (no leaves).  So the hierarchy on the
largest leaf, `qdH`, is the lifted hierarchy `Hˡ = Ul.ulH S 1` below `Γ_{Ω₂+1}`, for every `S` (`qdH_eq_ul`).

* `qdComps_big`, `qdComps_mem` (a leaf is below `Ω₂` and at most the level), `qdP`, `qdP_of_lt`, `qdP_big`,
  `qd_Om2_eq`, `qd_big_of`, `qd_log_mod` (the parts of a level `≥ Ω₂`), `qdP_add`, `qdP_phi`;
* `qd_two_lt_Om1`, `qd_Omfix_gt`, `qd_of_K` (`⇐`), `qd_K_of` (`⇒`), `qd_K_iff`, `qdFold_big`, `qdFold_lt_iff`;
* `qdH`, `qdH_eq_ul` (**`qdH γ = Hˡ_γ` for `γ < Γ_{Ω₂+1}`, every `S`**).

No new axiom.  New definitions: `qdP`, `qdH`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj
  Googology.Trans.PoR.InaccPsi.R2.Ul

/-! ## The leaves -/

theorem qdComps_big {z : Ordinal.{0}} (h : qdG2 ≤ z) : qdComps z = ∅ := by
  rw [qdComps, dif_neg (fun hz => absurd hz.2 (not_lt.2 h)),
    if_neg (fun h' => absurd (h'.trans qd_Om2_lt_G2) (not_lt.2 h))]

/-- **A leaf is below `Ω₂` and at most the level.** -/
theorem qdComps_mem : ∀ z : Ordinal.{0}, ∀ d ∈ qdComps z, d < OmTwo ∧ d ≤ z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro d hd
  rcases lt_trichotomy z OmTwo with h2 | h2 | h2
  · rw [qdComps_small h2, mem_singleton_iff] at hd; rw [hd]; exact ⟨h2, le_rfl⟩
  · rw [h2, qdComps_Om2] at hd; exact absurd hd (Set.notMem_empty _)
  rcases lt_or_ge z qdG2 with hG | hG
  · by_cases hE : ω ^ z = z
    · rw [qdComps_phi h2 hG hE] at hd
      rcases hd with hd | hd
      · have h := qd_inv1_lt h2 hG
        obtain ⟨a, b⟩ := IH _ h d hd; exact ⟨a, b.trans h.le⟩
      · have h := Ss.ss_inv2_lt hE
        obtain ⟨a, b⟩ := IH _ h d hd; exact ⟨a, b.trans h.le⟩
    · rw [qdComps_cnf h2 hG hE] at hd
      rcases hd with hd | hd
      · have h := Ss.ss_log_lt (qd_Om2_pos.trans h2).ne' hE
        obtain ⟨a, b⟩ := IH _ h d hd; exact ⟨a, b.trans h.le⟩
      · have h := rj_mod_lt (qd_Om2_pos.trans h2).ne'
        obtain ⟨a, b⟩ := IH _ h d hd; exact ⟨a, b.trans h.le⟩
  · rw [qdComps_big hG] at hd; exact absurd hd (Set.notMem_empty _)

/-- **Every leaf of `z` is below `v`.** -/
def qdP (v z : Ordinal.{0}) : Prop := ∀ d ∈ qdComps z, d < v

theorem qdP_of_lt {v z : Ordinal.{0}} (h : z < v) : qdP v z := fun d hd => ((qdComps_mem z d hd).2).trans_lt h

theorem qdP_big {v z : Ordinal.{0}} (h : qdG2 ≤ z) : qdP v z := by
  intro d hd; rw [qdComps_big h] at hd; exact absurd hd (Set.notMem_empty _)

theorem qd_Om2_eq : (OmTwo : Ordinal.{0}) = Om 2 := by rw [uc_Om2_eq]; norm_num

/-- A strongly critical ordinal above `Ω₂` is at least `Γ_{Ω₂+1}`. -/
theorem qd_big_of {x : Ordinal.{0}} (hSC : SC x) (h : OmTwo < x) : qdG2 ≤ x := qdG2_le hSC h

/-- The parts of a level `x ≥ Ω₂`. -/
theorem qd_log_mod {v x : Ordinal.{0}} (hv : 0 < v) (h2 : OmTwo ≤ x) (hG : x < qdG2) (hP : qdP v x) :
    qdP v (log ω x) ∧ qdP v (x % ω ^ log ω x) := by
  have hO2E : ω ^ (OmTwo : Ordinal.{0}) = OmTwo := Low.opow_eq_self_of_SC uc_SC_Om2
  by_cases hE : ω ^ x = x
  · have hl : log ω x = x := by
      conv_lhs => rw [← hE]
      exact log_opow one_lt_omega0 x
    have hm : x % ω ^ x = 0 := by rw [hE, mod_self]
    rw [hl, hm]
    exact ⟨hP, qdP_of_lt hv⟩
  · have h2' : OmTwo < x := lt_of_le_of_ne h2 fun h => hE (by rw [← h]; exact hO2E)
    have hc := qdComps_cnf h2' hG hE
    exact ⟨fun d hd => hP d (by rw [hc]; exact Or.inl hd), fun d hd => hP d (by rw [hc]; exact Or.inr hd)⟩

section V

variable {v : Ordinal.{0}} (hv : SC v)
include hv

/-- **Sums keep the leaves below `v`.** -/
theorem qdP_add : ∀ x y : Ordinal.{0}, qdP v x → qdP v y → qdP v (x + y) := by
  have hO2E : ω ^ (OmTwo : Ordinal.{0}) = OmTwo := Low.opow_eq_self_of_SC uc_SC_Om2
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro y hx hy
  rcases lt_or_ge (x + y) qdG2 with hG | hG
  swap
  · exact qdP_big hG
  rcases eq_or_ne y 0 with rfl | hy0
  · rwa [add_zero]
  rcases eq_or_ne x 0 with rfl | hx0
  · rwa [zero_add]
  rcases lt_trichotomy (x + y) OmTwo with h2 | h2 | h2
  · have hx2 : x < OmTwo := le_self_add.trans_lt h2
    have hy2 : y < OmTwo := le_add_self.trans_lt h2
    have hxv : x < v := hx x (by rw [qdComps_small hx2]; exact mem_singleton _)
    have hyv : y < v := hy y (by rw [qdComps_small hy2]; exact mem_singleton _)
    exact qdP_of_lt (hv.isPrincipal hxv hyv)
  · rw [h2]; intro d hd; rw [qdComps_Om2] at hd; exact absurd hd (Set.notMem_empty _)
  rcases lt_or_ge (log ω x) (log ω y) with hlt | hle
  · have hxy : x + y = y := Ordinal.add_of_omega0_opow_le ((lt_opow_succ_log_self one_lt_omega0 x).trans_le
      (opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hlt))) (opow_log_le_self ω hy0)
    rw [hxy]; exact hy
  -- `log y ≤ log x`, `x ≥ Ω₂`
  have hx2 : OmTwo ≤ x := by
    by_contra h; push Not at h
    have hlx : log ω x < OmTwo := (log_le_self ω x).trans_lt h
    have hy' : y < OmTwo := (lt_opow_succ_log_self one_lt_omega0 y).trans_le (by
      rw [← hO2E]; exact opow_le_opow_right omega0_pos (Order.add_one_le_of_lt (hle.trans_lt hlx)))
    exact absurd (uc_SC_Om2.isPrincipal h hy') (not_lt.2 h2.le)
  have hxG : x < qdG2 := le_self_add.trans_lt hG
  have hlx2 : OmTwo ≤ log ω x := le_log_of_opow_le one_lt_omega0 (by rw [hO2E]; exact hx2)
  obtain ⟨hPl, hPr⟩ := qd_log_mod hv.1 hx2 hxG hx
  have hxdec : ω ^ log ω x * (x / ω ^ log ω x) + x % ω ^ log ω x = x := div_add_mod x _
  have hxr : x % ω ^ log ω x < ω ^ log ω x := mod_lt x (opow_pos _ omega0_pos).ne'
  have hxn0 : x / ω ^ log ω x ≠ 0 := (div_opow_log_pos ω hx0).ne'
  have hxn : x / ω ^ log ω x < ω := div_opow_log_lt x one_lt_omega0
  have hrx : x % ω ^ log ω x < x := rj_mod_lt hx0
  -- the Cantor normal form of `x + y`
  have hcnf : ∃ n r, n ≠ 0 ∧ n < ω ∧ r < ω ^ log ω x ∧ ω ^ log ω x * n + r = x + y ∧ qdP v r := by
    rcases hle.lt_or_eq with hlt | heq
    · refine ⟨x / ω ^ log ω x, x % ω ^ log ω x + y, hxn0, hxn, ?_, ?_, IH _ hrx _ hPr hy⟩
      · exact isPrincipal_add_omega0_opow _ hxr ((lt_opow_succ_log_self one_lt_omega0 y).trans_le
          (opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hlt)))
      · rw [← add_assoc, hxdec]
    · have hy2 : OmTwo ≤ y := by
        calc OmTwo = ω ^ OmTwo := hO2E.symm
          _ ≤ ω ^ log ω x := opow_le_opow_right omega0_pos hlx2
          _ = ω ^ log ω y := by rw [heq]
          _ ≤ y := opow_log_le_self ω hy0
      have hyG : y < qdG2 := le_add_self.trans_lt hG
      obtain ⟨-, hPr'⟩ := qd_log_mod hv.1 hy2 hyG hy
      have hydec : ω ^ log ω y * (y / ω ^ log ω y) + y % ω ^ log ω y = y := div_add_mod y _
      have hyr : y % ω ^ log ω y < ω ^ log ω y := mod_lt y (opow_pos _ omega0_pos).ne'
      have hym0 : y / ω ^ log ω y ≠ 0 := (div_opow_log_pos ω hy0).ne'
      have hym : y / ω ^ log ω y < ω := div_opow_log_lt y one_lt_omega0
      obtain ⟨a, ha⟩ := lt_omega0.1 hxn
      obtain ⟨b, hb⟩ := lt_omega0.1 hym
      refine ⟨x / ω ^ log ω x + y / ω ^ log ω y, y % ω ^ log ω y, ?_, ?_, hyr.trans_eq (by rw [heq]), ?_, hPr'⟩
      · exact fun h => hxn0 (le_antisymm (h ▸ le_self_add) zero_le)
      · rw [ha, hb]; exact_mod_cast natCast_lt_omega0 (a + b)
      · have habs : x % ω ^ log ω x + y = y := Ordinal.add_of_omega0_opow_le hxr (by rw [← heq]; exact opow_log_le_self ω hy0)
        calc ω ^ log ω x * (x / ω ^ log ω x + y / ω ^ log ω y) + y % ω ^ log ω y
            = ω ^ log ω x * (x / ω ^ log ω x) + (ω ^ log ω x * (y / ω ^ log ω y) + y % ω ^ log ω y) := by
              rw [mul_add, add_assoc]
          _ = ω ^ log ω x * (x / ω ^ log ω x) + y := by rw [← heq, hydec]
          _ = ω ^ log ω x * (x / ω ^ log ω x) + (x % ω ^ log ω x + y) := by rw [habs]
          _ = x + y := by rw [← add_assoc, hxdec]
  obtain ⟨n, r, hn0, hn, hr, hxy, hPr2⟩ := hcnf
  obtain ⟨e1, e2, -⟩ := qd_cnf_log hn0 hn hr
  have hE : ω ^ (x + y) ≠ x + y := by
    rw [← hxy]
    refine qd_cnf_nE hn0 hn hr fun h => ?_
    rw [hxy] at h
    -- `x + y = log x ≤ x`
    have : x + y ≤ x := h ▸ log_le_self ω x
    exact absurd (lt_add_of_pos_right x (pos_iff_ne_zero.2 hy0)) (not_lt.2 this)
  unfold qdP
  rw [show qdComps (x + y) = qdComps (log ω (x + y)) ∪ qdComps ((x + y) % ω ^ log ω (x + y)) from
    qdComps_cnf h2 hG hE, ← hxy, e1, e2]
  rintro d (hd | hd)
  · exact hPl d hd
  · exact hPr2 d hd

/-- **`φ` keeps the leaves below `v`.** -/
theorem qdP_phi (x y : Ordinal.{0}) (hx : qdP v x) (hy : qdP v y) : qdP v (veblen x y) := by
  rcases lt_or_ge (veblen x y) qdG2 with hG | hG
  swap
  · exact qdP_big hG
  rcases lt_trichotomy (veblen x y) OmTwo with h2 | h2 | h2
  · have hx2 : x < OmTwo := (left_le_veblen x y).trans_lt h2
    have hy2 : y < OmTwo := (right_le_veblen x y).trans_lt h2
    have hxv : x < v := hx x (by rw [qdComps_small hx2]; exact mem_singleton _)
    have hyv : y < v := hy y (by rw [qdComps_small hy2]; exact mem_singleton _)
    exact qdP_of_lt (hv.2 x hxv y hyv)
  · rw [h2]; intro d hd; rw [qdComps_Om2] at hd; exact absurd hd (Set.notMem_empty _)
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [veblen_zero_apply] at h2 hG ⊢
    by_cases hE : ω ^ (ω ^ y) = ω ^ y
    · have hyy : ω ^ y = y := (isNormal_opow one_lt_omega0).strictMono.injective hE
      rw [hyy]; exact hy
    · unfold qdP
      rw [qdComps_cnf h2 hG hE, log_opow one_lt_omega0, mod_self]
      rintro d (hd | hd)
      · exact hy d hd
      · rw [qdComps_small qd_Om2_pos, mem_singleton_iff] at hd; rw [hd]; exact hv.1
  · by_cases hfix : veblen x y = y
    · rw [hfix]; exact hy
    · have hyv : y < veblen x y := lt_of_le_of_ne (right_le_veblen _ _) (Ne.symm hfix)
      unfold qdP
      rw [qdComps_veb hx0 hyv h2 hG]
      rintro d (hd | hd)
      · exact hx d hd
      · exact hy d hd

end V

/-! ## The visibility closure -/

section K

variable {S : InaccSeq.{0}} {v : Ordinal.{0}} (hv : SC v) (hvO : Om1 < v)
include hv hvO

theorem qd_two_lt_Om1 : (2 : Ordinal.{0}) < Om1 :=
  (show (2 : Ordinal.{0}) < ω from by exact_mod_cast natCast_lt_omega0 2).trans
    (omega0_lt_inE (show InE Om1 from rj_Om1_opow))

omit hv hvO in
/-- An `Ω`-fixed point above `2` is above `Ω₂`. -/
theorem qd_Omfix_gt {x : Ordinal.{0}} (hx : Om x = x) (h2 : 2 < x) : OmTwo < x := by
  rw [qd_Om2_eq, ← hx]; exact Om_lt_Om.2 h2

/-- **`⇐`: the leaves of a level visible at `v` are below `v`.** -/
theorem qd_of_K : ∀ z : Ordinal.{0}, UlK S 1 v z → qdP v z := by
  have h2O : (2 : Ordinal.{0}) < Om1 := qd_two_lt_Om1 hv hvO
  intro z hz
  induction hz with
  | small h => exact qdP_of_lt h
  | zero => exact qdP_of_lt hv.1
  | inacc n =>
    refine qdP_big (qd_big_of (InaccSeq.SC_I n) ?_)
    exact Yg.yg_Om2_lt_I0.trans_le (S.strictMono.monotone (Nat.zero_le n))
  | inaccW => exact qdP_big (qd_big_of InaccSeq.SC_Iw (Yg.yg_Om2_lt_I0.trans (S.I_lt_Iw 0)))
  | add _ _ ihx ihy => exact qdP_add hv _ _ ihx ihy
  | phi _ _ ihx ihy => exact qdP_phi hv _ _ ihx ihy
  | @om x _ _ =>
    rcases lt_trichotomy x 2 with hx | hx | hx
    · have hx1 : x ≤ 1 := Order.lt_add_one_iff.1 (by rw [one_add_one_eq_two]; exact hx)
      refine qdP_of_lt ((Om_le_Om.2 hx1).trans_lt ?_)
      rw [← Br.Om1_eq]; exact hvO
    · rw [hx, ← qd_Om2_eq]; intro d hd; rw [qdComps_Om2] at hd; exact absurd hd (Set.notMem_empty _)
    · have hx0 : x ≠ 0 := (lt_of_le_of_lt zero_le (show (0 : Ordinal.{0}) < 2 by norm_num) |>.trans hx).ne'
      exact qdP_big (qd_big_of (SC_Om hx0) (by rw [qd_Om2_eq]; exact Om_lt_Om.2 hx))
  | @coll π e hπ hne _ _ _ _ =>
    rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
    · have h1 := InaccSeq.Om_one_lt_psiI (S := S) e n
      refine qdP_big (qd_big_of (InaccSeq.SC_psi (InaccSeq.InR_I n) e) (qd_Omfix_gt (InaccSeq.Om_psiI e n) ?_))
      rw [← Br.Om1_eq] at h1; exact h2O.trans h1
    · obtain ⟨hlo, hhi⟩ := InaccSeq.psiS_bounds (S := S) e s
      rcases eq_or_ne s 0 with rfl | hs0
      · rw [zero_add, ← Br.Om1_eq] at hhi; rw [zero_add, ← Br.Om1_eq]; exact qdP_of_lt (hhi.trans hvO)
      have hs1 : s ≠ 1 := fun h => hne (by rw [h])
      have hs2 : 2 ≤ s := by
        by_contra h; push Not at h
        have : s ≤ 1 := Order.lt_add_one_iff.1 (by rw [one_add_one_eq_two]; exact h)
        rcases (Order.le_one_iff).1 this with h' | h'
        · exact hs0 h'
        · exact hs1 h'
      refine qdP_big (qd_big_of (InaccSeq.SC_psi (InaccSeq.InR_Om_succ s) e) ?_)
      rw [qd_Om2_eq]; exact (Om_le_Om.2 hs2).trans_lt hlo

omit hv hvO in
/-- **`⇒`: a level with its leaves below `v` is visible at `v`.** -/
theorem qd_K_of : ∀ z : Ordinal.{0}, z < qdG2 → qdP v z → UlK S 1 v z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hzG hP
  rcases lt_trichotomy z OmTwo with h2 | h2 | h2
  · exact UlK.small (hP z (by rw [qdComps_small h2]; exact mem_singleton _))
  · rw [h2, uc_Om2_eq]; exact ulK_W one_lt_omega0
  by_cases hE : ω ^ z = z
  · have hc := qdComps_phi h2 hzG hE
    have ha := IH _ (qd_inv1_lt h2 hzG) ((qd_inv1_lt h2 hzG).trans hzG) fun d hd => hP d (by rw [hc]; exact Or.inl hd)
    have hb := IH _ (Ss.ss_inv2_lt hE) ((Ss.ss_inv2_lt hE).trans hzG) fun d hd => hP d (by rw [hc]; exact Or.inr hd)
    rw [← qd_veb_inv hE]; exact UlK.phi ha hb
  · have hc := qdComps_cnf h2 hzG hE
    have hl0 := Ss.ss_log_lt (qd_Om2_pos.trans h2).ne' hE
    have hr0 := rj_mod_lt (qd_Om2_pos.trans h2).ne'
    have hl := IH _ hl0 (hl0.trans hzG) fun d hd => hP d (by rw [hc]; exact Or.inl hd)
    have hr := IH _ hr0 (hr0.trans hzG) fun d hd => hP d (by rw [hc]; exact Or.inr hd)
    obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt z one_lt_omega0)
    have hdec : ω ^ log ω z * (k : Ordinal.{0}) + z % ω ^ log ω z = z := by
      rw [← hk]; exact div_add_mod z _
    rw [← hdec]
    exact UlK.add (UlK.mul_nat (UlK.opow hl) k) hr

theorem qd_K_iff {z : Ordinal.{0}} (hzG : z < qdG2) : qdP v z ↔ UlK S 1 v z :=
  ⟨qd_K_of z hzG, qd_of_K hv hvO z⟩

end K

theorem qdFold_big {z : Ordinal.{0}} (h : qdG2 ≤ z) : qdFold id z = 0 := by
  rw [qdFold, dif_neg (fun hz => absurd hz.2 (not_lt.2 h)),
    if_neg (fun h' => absurd (h'.trans qd_Om2_lt_G2) (not_lt.2 h))]

/-- **The largest leaf is below `v` iff every leaf is.** -/
theorem qdFold_lt_iff {v : Ordinal.{0}} (hv : 0 < v) : ∀ z : Ordinal.{0}, qdFold id z < v ↔ qdP v z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  rcases lt_trichotomy z OmTwo with h2 | h2 | h2
  · rw [qdFold_small id h2]
    unfold qdP; rw [qdComps_small h2]
    exact ⟨fun h d hd => by rw [mem_singleton_iff.1 hd]; exact h, fun h => h z rfl⟩
  · rw [h2, qdFold_Om2]
    exact ⟨fun _ d hd => by rw [qdComps_Om2] at hd; exact absurd hd (Set.notMem_empty _), fun _ => hv⟩
  rcases lt_or_ge z qdG2 with hG | hG
  · by_cases hE : ω ^ z = z
    · rw [qdFold_phi id h2 hG hE, max_lt_iff, IH _ (qd_inv1_lt h2 hG), IH _ (Ss.ss_inv2_lt hE)]
      unfold qdP; rw [qdComps_phi h2 hG hE]
      exact ⟨fun ⟨ha, hb⟩ d hd => hd.elim (ha d) (hb d), fun h => ⟨fun d hd => h d (Or.inl hd),
        fun d hd => h d (Or.inr hd)⟩⟩
    · rw [qdFold_cnf id h2 hG hE, max_lt_iff, IH _ (Ss.ss_log_lt (qd_Om2_pos.trans h2).ne' hE),
        IH _ (rj_mod_lt (qd_Om2_pos.trans h2).ne')]
      unfold qdP; rw [qdComps_cnf h2 hG hE]
      exact ⟨fun ⟨ha, hb⟩ d hd => hd.elim (ha d) (hb d), fun h => ⟨fun d hd => h d (Or.inl hd),
        fun d hd => h d (Or.inr hd)⟩⟩
  · rw [qdFold_big hG]; exact ⟨fun _ => qdP_big hG, fun _ => hv⟩

/-! ## The hierarchy on the largest leaf -/

/-- **The hierarchy of the Veblen levels** on the largest leaf, floor `Ω₁` (no inaccessibles). -/
noncomputable def qdH (γ : Ordinal.{0}) : Ordinal.{0} → Ordinal.{0} := ucG (qdFold id) Om1 γ

/-- **`qdH γ = Hˡ_γ` below `Γ_{Ω₂+1}`, for every `S`.** -/
theorem qdH_eq_ul (S : InaccSeq.{0}) {γ : Ordinal.{0}} (hγ : γ < qdG2) : qdH γ = ulH S 1 γ := by
  unfold qdH ulH
  rw [← Br.Om1_eq]
  refine ul_ucG_congr γ fun j hj v hv hLv => ?_
  rw [ul_vis hv, qdFold_lt_iff hv.1]
  exact qd_K_iff hv hLv (hj.trans_lt hγ)

end Googology.Trans.PoR.InaccPsi.R2.Qd
