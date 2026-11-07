import Googology.Trans.PoR.InaccPsi.R2.FaPC

/-!
# Fa: THE CERTIFICATE OF A FIRST VALUE WITH ITS THRESHOLDS

`Vs.vsCert` with the thresholds `K₁` (of the datum of `γ` for `ψ_W`), `K₂` (of `γ` for `ψ_V`) in the conclusion: the
first value of `Hˡ_γ` is `ψ_W(K₂)` with `γ = ψ_V(K₂)`, or `ψ_W(max(K₁, K₂) + W^γ)`.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Fa

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Uo
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Vs

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

/-- **The certificate of a first value with its thresholds.** -/
theorem faCert (hs : s < ω) (hs1 : 1 ≤ s) {γ A : Ordinal.{0}} (hγ0 : γ ≠ 0) (hγV : γ < Om (s + 1 + 1))
    (hγN : γ ∈ ⋃ a, S.CSet a 0) (hA : ulH S s γ 0 < S.psi A (Om (s + 1))) :
    ∃ K1 K2, K1 ∈ S.CSet K1 (S.psi K1 (Om (s + 1))) ∧
      (K1 = 0 ∨ S.psi K1 (Om (s + 1)) ≤ ulDat S (Om (s + 1)) γ) ∧
      (∀ e, e ≠ 0 → (ulDat S (Om (s + 1)) γ < S.psi e (Om (s + 1)) ↔ K1 < e)) ∧
      K2 ∈ S.CSet K2 (S.psi K2 (Om (s + 1 + 1))) ∧ (K2 = 0 ∨ S.psi K2 (Om (s + 1 + 1)) ≤ γ) ∧
      (∀ e, e ≠ 0 → (γ < S.psi e (Om (s + 1 + 1)) ↔ K2 < e)) ∧
      ∃ B0, B0 ∈ S.CSet B0 (S.psi B0 (Om (s + 1))) ∧ S.psi B0 (Om (s + 1)) = ulH S s γ 0 ∧
        ((B0 = K2 ∧ γ = S.psi K2 (Om (s + 1 + 1))) ∨
         (B0 = max K1 K2 + Om (s + 1) ^ γ ∧ max K1 K2 ∈ S.CSet (max K1 K2) (S.psi (max K1 K2) (Om (s + 1))) ∧
          (max K1 K2 = 0 ∨ S.psi (max K1 K2) (Om (s + 1)) ≤ ulDat S (Om (s + 1)) γ ∨
            S.psi (max K1 K2) (Om (s + 1 + 1)) < γ ∨
            (S.psi (max K1 K2) (Om (s + 1 + 1)) ≤ γ ∧ ¬ Om (s + 1) ^ γ ∣ max K1 K2)))) := by
  have h0s : (0 : Ordinal.{0}) < s := lt_of_lt_of_le zero_lt_one hs1
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  have hκV : S.InR (Om (s + 1 + 1)) := InR_Om_succ (s + 1)
  have hvis : ∀ e, (UlK S s (S.psi e (Om (s + 1))) γ ↔ ulDat S (Om (s + 1)) γ < S.psi e (Om (s + 1))) :=
    fun e => uo_K_iff_dat hs (Ui.ui_psi_SC (s := s) e) (Ui.ui_L_lt_psi (s := s) e) (Ui.ui_psi_lt (s := s) e).le hγN
  have hm0 : ulDat S (Om (s + 1)) γ < ulH S s γ 0 :=
    (uo_vis_dat hs (ulH_SC γ 0) (ulH_gt γ 0) (hA.trans (Ui.ui_psi_lt (s := s) A)).le hγN).1 (ulH_D_lt γ 0)
  have hmθ : ulDat S (Om (s + 1)) γ < S.psi A (Om (s + 1)) := hm0.trans hA
  obtain ⟨K1, hK1o, hK1m, hK1⟩ := Vp.vp_thr (S := S) (s := s) hs hmθ
  obtain ⟨a, ha⟩ := mem_iUnion.1 hγN
  have hγa : γ < S.psi a (Om (s + 1 + 1)) := lt_psi_of_mem hκV (CSet_mono le_rfl zero_le ha) hγV
  obtain ⟨K2, hK2o, hK2g, hK2⟩ := Vp.vp_thr (S := S) (s := s + 1) (Ui.ui_s1_lt_omega hs) hγa
  have hne : ∀ {x : Ordinal.{0}}, 0 < x → x ≠ 0 := fun h => h.ne'
  have hhull : ∀ e, e ∈ S.CSet e (S.psi e (Om (s + 1))) → e ≠ 0 →
      (γ ∈ S.CSet e (S.psi e (Om (s + 1))) ↔ K1 < e ∧ K2 < e) := fun e he he0 => by
    rw [Uz.uz_hull_iff hs hγV he, hvis e, hK1 e he0, hK2 e he0]
  have hMo : max K1 K2 ∈ S.CSet (max K1 K2) (S.psi (max K1 K2) (Om (s + 1))) := by
    rcases le_total K2 K1 with h | h
    · rw [max_eq_left h]; exact hK1o
    · rw [max_eq_right h]
      rcases h.lt_or_eq with hlt | heq
      · have hK20 : K2 ≠ 0 := hne (lt_of_le_of_lt zero_le hlt)
        have hg : S.psi K2 (Om (s + 1 + 1)) ≤ γ := hK2g.resolve_left hK20
        have hgu : γ < S.psi (K2 + 1) (Om (s + 1 + 1)) :=
          (hK2 (K2 + 1) (hne (lt_of_le_of_lt zero_le (lt_add_one K2)))).2 (lt_add_one K2)
        have hK2C : S.psi K2 (Om (s + 1 + 1)) ∈ S.CSet a 0 := vs_gap_C hs zero_le hK2o γ ha hg hgu
        have hK2N : K2 ∈ ⋃ a, S.CSet a 0 := mem_iUnion.2 ⟨a, (arg_mem_of_psi_mem hκV hK2C zero_le zero_le hK2o).1⟩
        rcases vsHt hs γ K2 hγN hK2N hK2o hg hgu with hw | hw
        · exact hw
        · exact absurd ((hK1 K2 hK20).2 hlt) (not_lt.2 hw)
      · rw [← heq]; exact hK1o
  set M := max K1 K2 with hMdef
  have hM1 : K1 ≤ M := le_max_left _ _
  have hM2 : K2 ≤ M := le_max_right _ _
  have hMo1 : M + 1 ∈ S.CSet (M + 1) (S.psi (M + 1) (Om (s + 1))) :=
    CSet.add_mem ((psi_mono hκ le_self_add).2 hMo) (CSet.one_mem _ _)
  have hγC1 : γ ∈ S.CSet (M + 1) (S.psi (M + 1) (Om (s + 1))) :=
    (hhull (M + 1) hMo1 (hne (lt_of_le_of_lt zero_le (lt_add_one M)))).2
      ⟨hM1.trans_lt (lt_add_one M), hM2.trans_lt (lt_add_one M)⟩
  have hME1 : M + 1 ≤ M + Om (s + 1) ^ γ :=
    add_le_add_right (one_le_iff_ne_zero.2 (Ui.ui_W_pos s γ).ne') M
  have hγCE : γ ∈ S.CSet (M + Om (s + 1) ^ γ) (S.psi (M + Om (s + 1) ^ γ) (Om (s + 1))) :=
    (psi_mono hκ hME1).2 hγC1
  have hEo : M + Om (s + 1) ^ γ ∈ S.CSet (M + Om (s + 1) ^ γ) (S.psi (M + Om (s + 1) ^ γ) (Om (s + 1))) := by
    have hW := ul_Wpow_mem (S := S) hs hγCE (CSet.one_mem _ _)
    rw [mul_one] at hW
    exact CSet.add_mem ((psi_mono hκ le_self_add).2 hMo) hW
  have hE0 : M + Om (s + 1) ^ γ ≠ 0 := hne (lt_of_lt_of_le (Ui.ui_W_pos s γ) le_add_self)
  have hdvdE : Om (s + 1) ^ γ ∣ M + Om (s + 1) ^ γ := Vp.vp_dvd_self_add (Vp.vp_Wg_indec s γ) M
  have hγψE : γ ≤ S.psi (M + Om (s + 1) ^ γ) (Om (s + 1 + 1)) :=
    (ul_lt_psiV hγCE le_rfl (ul_psiW_le_psiV _ _) hγV).le
  have hvalE := Vp.vp_val_of hs hEo hE0 hγ0 hγV hdvdE hγψE (ul_K_of_mem hγCE)
  by_cases hsp : K1 < K2 ∧ γ = S.psi K2 (Om (s + 1 + 1)) ∧ Om (s + 1) ^ γ ∣ K2
  · obtain ⟨hlt, hg, hd⟩ := hsp
    have hK2W : K2 ∈ S.CSet K2 (S.psi K2 (Om (s + 1))) := by
      have e : M = K2 := max_eq_right hlt.le
      rw [← e]; exact hMo
    have hK20 : K2 ≠ 0 := hne (lt_of_le_of_lt zero_le hlt)
    have hKv : UlK S s (S.psi K2 (Om (s + 1))) γ := (hvis K2).2 ((hK1 K2 hK20).2 hlt)
    exact ⟨K1, K2, hK1o, hK1m, hK1, hK2o, hK2g, hK2, K2, hK2W,
      (Us.us_bv hs K2 hK2W hK20 γ hγ0 hγV hd hg.le hKv (Or.inl hg)).symm, Or.inl ⟨rfl, hg⟩⟩
  have hopt : M = 0 ∨ S.psi M (Om (s + 1)) ≤ ulDat S (Om (s + 1)) γ ∨ S.psi M (Om (s + 1 + 1)) < γ ∨
      (S.psi M (Om (s + 1 + 1)) ≤ γ ∧ ¬ Om (s + 1) ^ γ ∣ M) := by
    rcases le_total K2 K1 with h | h
    · rw [hMdef, max_eq_left h]
      rcases hK1m with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (Or.inl h0)
    · rcases h.lt_or_eq with hlt | heq
      · rw [hMdef, max_eq_right h]
        have hK20 : K2 ≠ 0 := hne (lt_of_le_of_lt zero_le hlt)
        have hg : S.psi K2 (Om (s + 1 + 1)) ≤ γ := hK2g.resolve_left hK20
        rcases hg.lt_or_eq with hg' | hg'
        · exact Or.inr (Or.inr (Or.inl hg'))
        · exact Or.inr (Or.inr (Or.inr ⟨hg, fun hd => hsp ⟨hlt, hg'.symm, hd⟩⟩))
      · rw [hMdef, max_eq_right h, ← heq]
        rcases hK1m with h0 | h0
        · exact Or.inl h0
        · exact Or.inr (Or.inl h0)
  exact ⟨K1, K2, hK1o, hK1m, hK1, hK2o, hK2g, hK2, M + Om (s + 1) ^ γ, hEo,
    (Vp.vp_first_of_cert hs hγ0 hγN hEo hvalE (Or.inr ⟨M, rfl, hMo, hopt⟩)).symm,
    Or.inr ⟨rfl, hMo, hopt⟩⟩

end Googology.Trans.PoR.InaccPsi.R2.Fa
