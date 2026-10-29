import Googology.Trans.PoR.InaccPsi.R2.VpMove
import Googology.Trans.PoR.InaccPsi.R2.VpGap

/-!
# Certificates of the first values from two thresholds; the residual `VpHt`

`W = Ω_{s+1}`, `ψ_W = S.psi · W` (`s` finite), `m(γ) = ulDat S Ω₂ γ`, `Hˡ_γ = Ul.ulH S 1 γ`.  For a level `γ` the hull
condition `γ ∈ Cl(e, ψ_{Ω₂} e)` at an own `e ≠ 0` is the conjunction of two thresholds (`Uz.uz_hull_iff`,
`Uo.uo_K_iff_dat`): `m(γ) < ψ_{Ω₂}(e)` and `γ < ψ_{Ω₃}(e)`.  Each threshold is `K < e` for an own `K` with
`K = 0` or `ψ(K) ≤ x < ψ(K + 1)` (`vp_thr`), and these `K` are what `B_n` moves.  The first value of `Hˡ_γ` is
`ψ(max(K₁, K₂) + Ω₂^γ)` (or `ψ(K₂)` when `γ = ψ_{Ω₃}(K₂)`), provided the height threshold `K₂` is own also for
`ψ_{Ω₂}` whenever it is the larger one:

* `vp_thr` (**a threshold**: for `x < ψ_W(A)` an own `K` with `K = 0` or `ψ_W(K) ≤ x`, and `x < ψ_W(e) ↔ K < e` for
  every `e ≠ 0`), `vp_succ_mem` (**the threshold of a member of `K^{(i)}_q` is in `K^{(i)}_q`**, via `Uw.uw_next`),
  `vp_dvd_self_add` (`u ∣ M + u` for indecomposable `u`);
* `VpHt S` (**the residual**: an own-for-`ψ_{Ω₃}` `K` with `ψ_{Ω₃}(K) ≤ γ < ψ_{Ω₃}(K + 1)` is own for `ψ_{Ω₂}`, or
  `ψ_{Ω₂}(K) ≤ m(γ)`; a statement about the notation only), `vpCert_of_ht` (**`VpHt S ⇒ Vp.VpCert S`**),
  `vmAtom_of_ht` (**`VpHt S ⇒ Vm.VmAtomMove S`**).

No new axiom.  New definition: `VpHt` (a Prop).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Uo
  Googology.Trans.PoR.InaccPsi.R2.Uc

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

/-- **A threshold**: for `x < ψ_W(A)` there is an own `K` with `K = 0` or `ψ_W(K) ≤ x`, and `x < ψ_W(e) ↔ K < e` for
every `e ≠ 0`. -/
theorem vp_thr (hs : s < ω) {x A : Ordinal.{0}} (hx : x < S.psi A (Om (s + 1))) :
    ∃ K, K ∈ S.CSet K (S.psi K (Om (s + 1))) ∧ (K = 0 ∨ S.psi K (Om (s + 1)) ≤ x) ∧
      ∀ e, e ≠ 0 → (x < S.psi e (Om (s + 1)) ↔ K < e) := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  by_cases h0 : x < S.psi 0 (Om (s + 1))
  · exact ⟨0, CSet.zero_mem _ _, Or.inl rfl, fun e he =>
      ⟨fun _ => pos_iff_ne_zero.2 he, fun _ => h0.trans_le (psi_mono hκ zero_le).1⟩⟩
  push Not at h0
  set P : Set Ordinal.{0} := {v | SC v ∧ Om s < v ∧ v ≤ x} with hPdef
  have hψ0 : S.psi 0 (Om (s + 1)) ∈ P := ⟨Ui.ui_psi_SC 0, Ui.ui_L_lt_psi 0, h0⟩
  have hPne : P.Nonempty := ⟨_, hψ0⟩
  have hPb : BddAbove P := ⟨x, fun v hv => hv.2.2⟩
  have hvS : SC (sSup P) := uc_SC_sSup (fun v hv => hv.1) hPne hPb
  have hv1 : Om s < sSup P := (Ui.ui_L_lt_psi 0).trans_le (le_csSup hPb hψ0)
  have hvx : sSup P ≤ x := csSup_le hPne fun v hv => hv.2.2
  obtain ⟨K, hown, hK⟩ := Ui.ui_own_of_SC hs hvS hv1 (hvx.trans_lt hx)
  have hKx : S.psi K (Om (s + 1)) ≤ x := by rw [hK]; exact hvx
  have hxK1 : x < S.psi (K + 1) (Om (s + 1)) := by
    by_contra hc
    push Not at hc
    have h1 := le_csSup hPb (⟨Ui.ui_psi_SC _, Ui.ui_L_lt_psi _, hc⟩ : S.psi (K + 1) (Om (s + 1)) ∈ P)
    have h2 := Ui.ui_psi_lt_of_own hown (lt_add_one K)
    rw [hK] at h2
    exact absurd h1 (not_le.2 h2)
  refine ⟨K, hown, Or.inr hKx, fun e _ => ⟨fun h => ?_, fun h => ?_⟩⟩
  · by_contra hc
    push Not at hc
    exact absurd ((psi_mono hκ hc).1.trans hKx) (not_le.2 h)
  · exact hxK1.trans_le (psi_mono hκ (Order.add_one_le_of_lt h)).1

/-- **The threshold of a member of `K^{(i)}_q` is in `K^{(i)}_q`**: for `z ∈ K^{(i)}_q`, `z < Ω_{r+1}` (`i < r`) and
an own `K ≠ 0` with `z < ψ(e) ↔ K < e` for every `e ≠ 0`. -/
theorem vp_succ_mem {r i q z K : Ordinal.{0}} (hr : r < ω) (hir : i < r) (hq : SC q) (hqL : q ≤ Om (i + 1))
    (hz : UlK S i q z) (hzr : z < Om (r + 1)) (hown : K ∈ S.CSet K (S.psi K (Om (r + 1)))) (hK0 : K ≠ 0)
    (hthr : ∀ e, e ≠ 0 → (z < S.psi e (Om (r + 1)) ↔ K < e)) : UlK S i q K := by
  have hκ : S.InR (Om (r + 1)) := InR_Om_succ r
  obtain ⟨ed, hedK, hedO, hed⟩ := Uw.uw_next hr hir hq hqL z hz hzr
  have hown1 : K + 1 ∈ S.CSet (K + 1) (S.psi (K + 1) (Om (r + 1))) :=
    CSet.add_mem ((psi_mono hκ le_self_add).2 hown) (CSet.one_mem _ _)
  have h10 : K + 1 ≠ 0 := (lt_of_le_of_lt zero_le (lt_add_one K)).ne'
  have hed0 : ed ≠ 0 := by
    rintro rfl
    have h := (hed 0 (CSet.zero_mem _ _)).2 le_rfl
    exact (lt_irrefl K) ((hthr K hK0).1 (h.trans_le (psi_mono hκ zero_le).1))
  have h1 : ed ≤ K + 1 := (hed (K + 1) hown1).1 ((hthr (K + 1) h10).2 (lt_add_one K))
  have h2 : K + 1 ≤ ed := Order.add_one_le_of_lt ((hthr ed hed0).1 ((hed ed hedO).2 le_rfl))
  rw [le_antisymm h1 h2] at hedK
  exact ulK_of_succ hq hedK

/-- `u ∣ M + u` for an indecomposable `u`. -/
theorem vp_dvd_self_add {u : Ordinal.{0}} (hu : Indec u) (M : Ordinal.{0}) : u ∣ M + u := by
  refine ⟨M / u + 1, ?_⟩
  conv_lhs => rw [← Ordinal.div_add_mod M u]
  rw [add_assoc, hu.add_eq (Ordinal.mod_lt M hu.ne_zero), mul_add_one]

/-- **The residual** (a hypothesis name, about the notation only): an own-for-`ψ_{Ω₃}` ordinal `K` of the notation with
`ψ_{Ω₃}(K) ≤ γ < ψ_{Ω₃}(K + 1)` (`γ` of the notation) is own for `ψ_{Ω₂}`, or `ψ_{Ω₂}(K) ≤ m(γ)`. -/
def VpHt (S : InaccSeq.{0}) : Prop :=
  ∀ γ K, γ ∈ ⋃ a, S.CSet a 0 → K ∈ ⋃ a, S.CSet a 0 → K ∈ S.CSet K (S.psi K (Om (1 + 1 + 1))) →
    S.psi K (Om (1 + 1 + 1)) ≤ γ →
    γ < S.psi (K + 1) (Om (1 + 1 + 1)) →
      K ∈ S.CSet K (S.psi K (Om (1 + 1))) ∨ S.psi K (Om (1 + 1)) ≤ ulDat S (Om (1 + 1)) γ

/-- **`VpHt S ⇒ Vp.VpCert S`**: the first value of `Hˡ_γ` is `ψ(max(K₁, K₂) + Ω₂^γ)` with the thresholds `K₁` (of
`m(γ)` at `Ω₂`) and `K₂` (of `γ` at `Ω₃`), or `ψ(K₂)` when `γ = ψ_{Ω₃}(K₂)` and `Ω₂^γ ∣ K₂`. -/
theorem vpCert_of_ht (hH : VpHt S) : VpCert S := by
  intro γ hγ0 hγV hγN hθ _
  have hs1 := vp_hs1
  have hκ : S.InR (Om (1 + 1)) := InR_Om_succ 1
  have hκV : S.InR (Om (1 + 1 + 1)) := InR_Om_succ (1 + 1)
  have hvis : ∀ e, (UlK S 1 (S.psi e (Om (1 + 1))) γ ↔ ulDat S (Om (1 + 1)) γ < S.psi e (Om (1 + 1))) :=
    fun e => uo_K_iff_dat hs1 (Ui.ui_psi_SC (s := 1) e) (Ui.ui_L_lt_psi (s := 1) e) (Ui.ui_psi_lt (s := 1) e).le hγN
  have hm0 : ulDat S (Om (1 + 1)) γ < ulH S 1 γ 0 :=
    (uo_vis_dat hs1 (ulH_SC γ 0) (ulH_gt γ 0) (hθ.trans Vd.vd_th_lt_W).le hγN).1 (ulH_D_lt γ 0)
  have hmθ : ulDat S (Om (1 + 1)) γ < S.psi (Om ω) (Om (1 + 1)) := hm0.trans hθ
  obtain ⟨K1, hK1o, hK1m, hK1⟩ := vp_thr (S := S) (s := 1) hs1 hmθ
  obtain ⟨a, ha⟩ := mem_iUnion.1 hγN
  have hγa : γ < S.psi a (Om (1 + 1 + 1)) := lt_psi_of_mem hκV (CSet_mono le_rfl zero_le ha) hγV
  obtain ⟨K2, hK2o, hK2g, hK2⟩ := vp_thr (S := S) (s := 1 + 1) (Ui.ui_s1_lt_omega hs1) hγa
  have hne : ∀ {x : Ordinal.{0}}, 0 < x → x ≠ 0 := fun h => h.ne'
  have hhull : ∀ e, e ∈ S.CSet e (S.psi e (Om (1 + 1))) → e ≠ 0 →
      (γ ∈ S.CSet e (S.psi e (Om (1 + 1))) ↔ K1 < e ∧ K2 < e) := fun e he he0 => by
    rw [Uz.uz_hull_iff hs1 hγV he, hvis e, hK1 e he0, hK2 e he0]
  -- `max(K₁, K₂)` is own
  have hMo : max K1 K2 ∈ S.CSet (max K1 K2) (S.psi (max K1 K2) (Om (1 + 1))) := by
    rcases le_total K2 K1 with h | h
    · rw [max_eq_left h]; exact hK1o
    · rw [max_eq_right h]
      rcases h.lt_or_eq with hlt | heq
      · have hK20 : K2 ≠ 0 := hne (lt_of_le_of_lt zero_le hlt)
        have hg : S.psi K2 (Om (1 + 1 + 1)) ≤ γ := hK2g.resolve_left hK20
        have hgu : γ < S.psi (K2 + 1) (Om (1 + 1 + 1)) :=
          (hK2 (K2 + 1) (hne (lt_of_le_of_lt zero_le (lt_add_one K2)))).2 (lt_add_one K2)
        have hK2C : S.psi K2 (Om (1 + 1 + 1)) ∈ S.CSet a 0 := vp_gap_C zero_le hK2o γ ha hg hgu
        have hK2N : K2 ∈ ⋃ a, S.CSet a 0 := mem_iUnion.2 ⟨a, (arg_mem_of_psi_mem hκV hK2C zero_le zero_le hK2o).1⟩
        rcases hH γ K2 hγN hK2N hK2o hg hgu with hw | hw
        · exact hw
        · exact absurd ((hK1 K2 hK20).2 hlt) (not_lt.2 hw)
      · rw [← heq]; exact hK1o
  set M := max K1 K2 with hMdef
  have hM1 : K1 ≤ M := le_max_left _ _
  have hM2 : K2 ≤ M := le_max_right _ _
  have hMo1 : M + 1 ∈ S.CSet (M + 1) (S.psi (M + 1) (Om (1 + 1))) :=
    CSet.add_mem ((psi_mono hκ le_self_add).2 hMo) (CSet.one_mem _ _)
  have hγC1 : γ ∈ S.CSet (M + 1) (S.psi (M + 1) (Om (1 + 1))) :=
    (hhull (M + 1) hMo1 (hne (lt_of_le_of_lt zero_le (lt_add_one M)))).2
      ⟨hM1.trans_lt (lt_add_one M), hM2.trans_lt (lt_add_one M)⟩
  have hME1 : M + 1 ≤ M + Om (1 + 1) ^ γ :=
    add_le_add_right (one_le_iff_ne_zero.2 (Ui.ui_W_pos 1 γ).ne') M
  have hγCE : γ ∈ S.CSet (M + Om (1 + 1) ^ γ) (S.psi (M + Om (1 + 1) ^ γ) (Om (1 + 1))) :=
    (psi_mono hκ hME1).2 hγC1
  have hEo : M + Om (1 + 1) ^ γ ∈ S.CSet (M + Om (1 + 1) ^ γ) (S.psi (M + Om (1 + 1) ^ γ) (Om (1 + 1))) := by
    have hW := ul_Wpow_mem (S := S) hs1 hγCE (CSet.one_mem _ _)
    rw [mul_one] at hW
    exact CSet.add_mem ((psi_mono hκ le_self_add).2 hMo) hW
  have hE0 : M + Om (1 + 1) ^ γ ≠ 0 := hne (lt_of_lt_of_le (Ui.ui_W_pos 1 γ) le_add_self)
  have hdvdE : Om (1 + 1) ^ γ ∣ M + Om (1 + 1) ^ γ := vp_dvd_self_add (vp_Wg_indec 1 γ) M
  have hγψE : γ ≤ S.psi (M + Om (1 + 1) ^ γ) (Om (1 + 1 + 1)) :=
    (ul_lt_psiV hγCE le_rfl (ul_psiW_le_psiV _ _) hγV).le
  have hvalE := vp_val_of hs1 hEo hE0 hγ0 hγV hdvdE hγψE (ul_K_of_mem hγCE)
  by_cases hsp : K1 < K2 ∧ γ = S.psi K2 (Om (1 + 1 + 1)) ∧ Om (1 + 1) ^ γ ∣ K2
  · obtain ⟨hlt, hg, hd⟩ := hsp
    have hK2W : K2 ∈ S.CSet K2 (S.psi K2 (Om (1 + 1))) := by
      have e : M = K2 := max_eq_right hlt.le
      rw [← e]; exact hMo
    have hK20 : K2 ≠ 0 := hne (lt_of_le_of_lt zero_le hlt)
    have hKv : UlK S 1 (S.psi K2 (Om (1 + 1))) γ := (hvis K2).2 ((hK1 K2 hK20).2 hlt)
    exact ⟨K2, hK2W, (Us.us_bv hs1 K2 hK2W hK20 γ hγ0 hγV hd hg.le hKv (Or.inl hg)).symm, Or.inl hg⟩
  -- the options of the certificate at `M`
  have hopt : M = 0 ∨ S.psi M (Om (1 + 1)) ≤ ulDat S (Om (1 + 1)) γ ∨ S.psi M (Om (1 + 1 + 1)) < γ ∨
      (S.psi M (Om (1 + 1 + 1)) ≤ γ ∧ ¬ Om (1 + 1) ^ γ ∣ M) := by
    rcases le_total K2 K1 with h | h
    · rw [hMdef, max_eq_left h]
      rcases hK1m with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (Or.inl h0)
    · rcases h.lt_or_eq with hlt | heq
      · rw [hMdef, max_eq_right h]
        have hK20 : K2 ≠ 0 := hne (lt_of_le_of_lt zero_le hlt)
        have hg : S.psi K2 (Om (1 + 1 + 1)) ≤ γ := hK2g.resolve_left hK20
        rcases hg.lt_or_eq with hg' | hg'
        · exact Or.inr (Or.inr (Or.inl hg'))
        · exact Or.inr (Or.inr (Or.inr ⟨hg, fun hd => hsp ⟨hlt, hg'.symm, hd⟩⟩))
      · rw [hMdef, max_eq_right h, ← heq]
        rcases hK1m with h0 | h0
        · exact Or.inl h0
        · exact Or.inr (Or.inl h0)
  -- the countable data of `M`
  have hsupp : ∀ q, SC q → q ≤ Om 1 → UlK S 0 q γ → UlK S 0 q M := by
    intro q hq hq1 hγK
    have hqL : q ≤ Om (0 + 1) := by rw [zero_add]; exact hq1
    have hK1q : UlK S 0 q K1 := by
      rcases eq_or_ne K1 0 with h0 | h0
      · rw [h0]; exact UlK.zero
      obtain ⟨z, hzK, hzW, hz⟩ := Uz.uz_dat (s := 1) hs1 zero_lt_one hqL hγK
      have hthr : ∀ e, e ≠ 0 → (z < S.psi e (Om (1 + 1)) ↔ K1 < e) := fun e he =>
        ((hz _ (Ui.ui_psi_SC (s := 1) e) (Ui.ui_L_lt_psi (s := 1) e) (Ui.ui_psi_lt (s := 1) e).le).symm.trans
          (hvis e)).trans (hK1 e he)
      exact vp_succ_mem hs1 zero_lt_one hq hqL hzK hzW hK1o h0 hthr
    have hK2q : UlK S 0 q K2 := by
      rcases eq_or_ne K2 0 with h0 | h0
      · rw [h0]; exact UlK.zero
      exact vp_succ_mem (Ui.ui_s1_lt_omega hs1) (lt_of_lt_of_le zero_lt_one le_self_add) hq hqL hγK hγV hK2o h0
        hK2
    rcases le_total K2 K1 with h | h
    · rw [hMdef, max_eq_left h]; exact hK1q
    · rw [hMdef, max_eq_right h]; exact hK2q
  refine ⟨M + Om (1 + 1) ^ γ, hEo,
    (vp_first_of_cert hs1 hγ0 hγN hEo hvalE (Or.inr ⟨M, rfl, hMo, hopt⟩)).symm,
    Or.inr ⟨M, rfl, hMo, hsupp, hopt⟩⟩

/-- **`VpHt S ⇒ Vm.VmAtomMove S`** (the hypothesis (b) of `Vm.vmRoad`). -/
theorem vmAtom_of_ht (hH : VpHt S) : Vm.VmAtomMove S := vmAtom_of_first (vpFirst_of_cert (vpCert_of_ht hH))

end Googology.Trans.PoR.InaccPsi.R2.Vp
