import Googology.Trans.PoR.InaccPsi.R2.VsHt

/-!
# The atom move at `Ω_{s+1}` for every finite `s ≥ 1`, with no hypothesis

`W = Ω_{s+1}`, `V = Ω_{s+2}`, `ψ = ψ_W`, `Hˡ_γ = Ul.ulH S s γ` (the lifted hierarchy at `W`), `B_n = Bc.bcB S n`,
`c' = c_{n+1} = Bc.bcC S (n + 1)`, `K_q = Ul.UlK S 0 q`, `m(γ) = ulDat S W γ`.  The proofs of `Vp.vpCert_of_ht`,
`Vp.vpFirst_of_cert`, `Vp.vpMove` at `s = 1` with `1` replaced by `s` and the bound `θ` replaced by any `ψ_W(A)`; the
residual is `Vs.vsHt` (proved), and the window `[X, B₂)` of `Vp.VpFirst` is not needed:

* `vsCert` (**every first value `Hˡ_γ(0) < ψ_W(A)` (`0 < γ < V`, `γ` of the notation) is `ψ(B₀)` for an own `B₀` with a
  certificate `Vp.VpCertCore`**: `γ = ψ_V(B₀)`, or `B₀ = K + W^γ`, `K` own with its countable data within those of
  `γ`);
* `vsFirst` (**the first values move: `B_n(Hˡ_γ(0)) = Hˡ_{B_n γ}(0)` for `γ < V`, `Hˡ_γ(0) ∈ K_{c'}`, `Hˡ_γ(0) < ψ_W(A)`**);
* `vsMove` (**the atom move: `B_n γ < V` and `B_n(Hˡ_γ(y)) = Hˡ_{B_n γ}(B_n y)` for `γ < V`, `y < Hˡ_γ(y) < ψ_W(A)`,
  `Hˡ_γ(y) ∈ K_{c'}`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vs

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Uo
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Mv

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

theorem vs_c_psi (hs1 : 1 ≤ s) (n : ℕ) (x : Ordinal.{0}) : Bc.bcC S (n + 1) ≤ S.psi x (Om (s + 1)) :=
  (Vm.vm_c_le n).trans ((Om_le_Om.2 hs1).trans (Ui.ui_L_lt_psi (s := s) x).le)

/-- **Certificates of the first values at every finite `s ≥ 1`**: a first value `Hˡ_γ(0) < ψ_W(A)` (`0 < γ < V`, `γ`
of the notation) is `ψ(B₀)` for an own `B₀` with `γ = ψ_V(B₀)`, or `B₀ = K + W^γ` with `K` own, the countable data of
`K` within those of `γ`, and `K = 0`, `ψ(K) ≤ m(γ)`, `ψ_V(K) < γ`, or `ψ_V(K) ≤ γ` with `W^γ ∤ K`. -/
theorem vsCert (hs : s < ω) (hs1 : 1 ≤ s) {γ A : Ordinal.{0}} (hγ0 : γ ≠ 0) (hγV : γ < Om (s + 1 + 1))
    (hγN : γ ∈ ⋃ a, S.CSet a 0) (hA : ulH S s γ 0 < S.psi A (Om (s + 1))) :
    ∃ B0, B0 ∈ S.CSet B0 (S.psi B0 (Om (s + 1))) ∧ S.psi B0 (Om (s + 1)) = ulH S s γ 0 ∧
      (γ = S.psi B0 (Om (s + 1 + 1)) ∨ ∃ K, B0 = K + Om (s + 1) ^ γ ∧ K ∈ S.CSet K (S.psi K (Om (s + 1))) ∧
        (∀ q, SC q → q ≤ Om 1 → UlK S 0 q γ → UlK S 0 q K) ∧
        (K = 0 ∨ S.psi K (Om (s + 1)) ≤ ulDat S (Om (s + 1)) γ ∨ S.psi K (Om (s + 1 + 1)) < γ ∨
          (S.psi K (Om (s + 1 + 1)) ≤ γ ∧ ¬ Om (s + 1) ^ γ ∣ K))) := by
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
    exact ⟨K2, hK2W, (Us.us_bv hs K2 hK2W hK20 γ hγ0 hγV hd hg.le hKv (Or.inl hg)).symm, Or.inl hg⟩
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
  have hsupp : ∀ q, SC q → q ≤ Om 1 → UlK S 0 q γ → UlK S 0 q M := by
    intro q hq hq1 hγK
    have hqL : q ≤ Om (0 + 1) := by rw [zero_add]; exact hq1
    have hK1q : UlK S 0 q K1 := by
      rcases eq_or_ne K1 0 with h0 | h0
      · rw [h0]; exact UlK.zero
      obtain ⟨z, hzK, hzW, hz⟩ := Uz.uz_dat (s := s) hs h0s hqL hγK
      have hthr : ∀ e, e ≠ 0 → (z < S.psi e (Om (s + 1)) ↔ K1 < e) := fun e he =>
        ((hz _ (Ui.ui_psi_SC (s := s) e) (Ui.ui_L_lt_psi (s := s) e) (Ui.ui_psi_lt (s := s) e).le).symm.trans
          (hvis e)).trans (hK1 e he)
      exact Vp.vp_succ_mem hs h0s hq hqL hzK hzW hK1o h0 hthr
    have hK2q : UlK S 0 q K2 := by
      rcases eq_or_ne K2 0 with h0 | h0
      · rw [h0]; exact UlK.zero
      exact Vp.vp_succ_mem (Ui.ui_s1_lt_omega hs) (lt_of_lt_of_le zero_lt_one le_add_self) hq hqL hγK hγV hK2o
        h0 hK2
    rcases le_total K2 K1 with h | h
    · rw [hMdef, max_eq_left h]; exact hK1q
    · rw [hMdef, max_eq_right h]; exact hK2q
  refine ⟨M + Om (s + 1) ^ γ, hEo,
    (Vp.vp_first_of_cert hs hγ0 hγN hEo hvalE (Or.inr ⟨M, rfl, hMo, hopt⟩)).symm,
    Or.inr ⟨M, rfl, hMo, hsupp, hopt⟩⟩

/-- **The first values move at every finite `s ≥ 1`**: `B_n(Hˡ_γ(0)) = Hˡ_{B_n γ}(0)` for `γ < V` with
`Hˡ_γ(0) < ψ_W(A)` and `Hˡ_γ(0) ∈ K_{c_{n+1}}`. -/
theorem vsFirst (hs : s < ω) (hs1 : 1 ≤ s) {n : ℕ} {γ A : Ordinal.{0}} (hγV : γ < Om (s + 1 + 1))
    (hA : ulH S s γ 0 < S.psi A (Om (s + 1))) (hK0 : UlK S 0 (Bc.bcC S (n + 1)) (ulH S s γ 0)) :
    Bc.bcB S n (ulH S s γ 0) = ulH S s (Bc.bcB S n γ) 0 := by
  have hs0 : s ≠ 0 := (lt_of_lt_of_le zero_lt_one hs1).ne'
  have h0s : (0 : Ordinal.{0}) < s := lt_of_lt_of_le zero_lt_one hs1
  rcases eq_or_ne γ 0 with rfl | hγ0
  · obtain ⟨-, hB, -⟩ := vsB_psi (n := n) hs hs0 Uf.ufD_zero (CSet.zero_mem _ _)
    rw [Bc.bcB_zero, Us.us_psi0 hs, hB, Bc.bcB_zero]
  have hq := Vm.vm_c_SC (S := S) n
  have hq1 := Vm.vm_c_le (S := S) n
  have hq01 : Bc.bcC S (n + 1) ≤ Om (0 + 1) := by rw [zero_add]; exact hq1
  have hqL : Bc.bcC S (n + 1) ≤ S.Lam := Us.us_qΛ (S := S) (i := 0) omega0_pos hq01
  have hzW : ulH S s γ 0 < Om (s + 1) := hA.trans (Ui.ui_psi_lt (s := s) A)
  have hγK : UlK S 0 (Bc.bcC S (n + 1)) γ :=
    ((Uz.uz_L1 hs h0s hq hq01 hγV hzW (ne_of_gt (ulH_SC γ 0).1)).1 hK0).1
  have hDγ := Vm.vm_D_of_K hγK
  obtain ⟨B0, hown, hB0, hcert⟩ := vsCert hs hs1 hγ0 hγV hDγ.1 hA
  have hB0K : UlK S 0 (Bc.bcC S (n + 1)) B0 :=
    uoArg hqL (InR_Om_succ s) hown (by rw [hB0]; exact hK0) (vs_c_psi hs1 n B0)
  have hDB0 := Vm.vm_D_of_K hB0K
  obtain ⟨hDψ, hBψ, hown'⟩ := vsB_psi (n := n) hs hs0 hDB0 hown
  obtain ⟨hDψV, hBψV, -⟩ := vsB_psi (s := s + 1) (n := n) (Ui.ui_s1_lt_omega hs)
    (lt_of_lt_of_le zero_lt_one le_add_self).ne' hDB0 (Vp.vp_ownV hown)
  have hvB : ulH S s γ 0 = S.psi B0 (Om (s + 1)) := hB0.symm
  have hdvd : Om (s + 1) ^ γ ∣ B0 := Us.us_dvd_val hs hown hvB
  have hγψ : γ ≤ S.psi B0 (Om (s + 1 + 1)) := Us.us_val_le hs hown hvB
  have hKγ : UlK S s (S.psi B0 (Om (s + 1))) γ :=
    (ul_vis (Ui.ui_psi_SC (s := s) B0)).1 (by rw [← hvB]; exact ulH_D_lt γ 0)
  obtain ⟨hDWγ, hBWγ⟩ := vsB_Wpow (n := n) hs hDγ
  have hdvd' : Om (s + 1) ^ Bc.bcB S n γ ∣ Bc.bcB S n B0 := by
    have h := Vp.vp_dvd_B (n := n) hDWγ (Vp.vp_Wg_indec s _) (by rw [hBWγ]; exact Vp.vp_Wg_indec s _) hDB0 hdvd
    rwa [hBWγ] at h
  have hγψ' : Bc.bcB S n γ ≤ S.psi (Bc.bcB S n B0) (Om (s + 1 + 1)) := by
    rw [← hBψV]; exact Vp.vpB_le hDγ hDψV hγψ
  have hK' : UlK S s (S.psi (Bc.bcB S n B0) (Om (s + 1))) (Bc.bcB S n γ) := by
    have h := vsK_B (n := n) hs hDγ hDψ (Ui.ui_psi_SC (s := s) B0) (Ui.ui_L_lt_psi (s := s) B0)
      (Ui.ui_psi_lt (s := s) B0).le (by rw [hBψ]; exact Ui.ui_psi_SC (s := s) _)
      (by rw [hBψ]; exact Ui.ui_L_lt_psi (s := s) _) (by rw [hBψ]; exact (Ui.ui_psi_lt (s := s) _).le)
    rw [hBψ] at h
    exact h.2 hKγ
  have hpos : ∀ {x : Ordinal.{0}}, MvD S x → x ≠ 0 → Bc.bcB S n x ≠ 0 := fun hx hx0 => by
    have h := (mvB_lt_iff (k := n) Uf.ufD_zero hx).2 (pos_iff_ne_zero.2 hx0)
    rw [Bc.bcB_zero] at h
    exact h.ne'
  have hB'0 := hpos hDB0 (Vp.vp_B0_ne hs hγ0 hvB)
  have hγ'0 := hpos hDγ hγ0
  have hγ'V : Bc.bcB S n γ < Om (s + 1 + 1) := hγψ'.trans_lt (Ui.ui_psi_lt (s := s + 1) _)
  have hval' := Vp.vp_val_of hs hown' hB'0 hγ'0 hγ'V hdvd' hγψ' hK'
  have hγ'N : Bc.bcB S n γ ∈ ⋃ a, S.CSet a 0 := by
    unfold Bc.bcB; exact mem_iUnion.2 (Term.exists_mem_CSet S _)
  have hcert' : Vp.VpCertCore S s (Bc.bcB S n γ) (Bc.bcB S n B0) := by
    rcases hcert with heq | ⟨K, hBK, hownK, hsupp, hK⟩
    · left
      rw [← hBψV, ← heq]
    · have hDK := Vm.vm_D_of_K (hsupp _ hq hq1 hγK)
      have hBB : Bc.bcB S n B0 = Bc.bcB S n K + Om (s + 1) ^ Bc.bcB S n γ := by
        rw [hBK, (mvB_add (k := n) hDK hDWγ).2, hBWγ]
      obtain ⟨-, -, hownK'⟩ := vsB_psi (n := n) hs hs0 hDK hownK
      right
      refine ⟨Bc.bcB S n K, hBB, hownK', ?_⟩
      rcases hK with hK0 | hKm | hKV | ⟨hKV, hKd⟩
      · left; rw [hK0, Bc.bcB_zero]
      · right; left
        obtain ⟨hDψK, hBψK, -⟩ := vsB_psi (n := n) hs hs0 hDK hownK
        obtain ⟨hDd, hBd⟩ := vsDatW_B (n := n) hs hDγ
        rw [← hBψK, hBd]
        exact Vp.vpB_le hDψK hDd hKm
      · right; right; left
        obtain ⟨hDψK, hBψK, -⟩ := vsB_psi (s := s + 1) (n := n) (Ui.ui_s1_lt_omega hs)
          (lt_of_lt_of_le zero_lt_one le_add_self).ne' hDK (Vp.vp_ownV hownK)
        rw [← hBψK]
        exact (mvB_lt_iff hDψK hDγ).2 hKV
      · right; right; right
        obtain ⟨hDψK, hBψK, -⟩ := vsB_psi (s := s + 1) (n := n) (Ui.ui_s1_lt_omega hs)
          (lt_of_lt_of_le zero_lt_one le_add_self).ne' hDK (Vp.vp_ownV hownK)
        refine ⟨by rw [← hBψK]; exact Vp.vpB_le hDψK hDγ hKV, fun hd => hKd ?_⟩
        rw [← hBWγ] at hd
        exact (Vp.vp_dvd_B_iff (n := n) hDWγ (Vp.vp_Wg_indec s _) (by rw [hBWγ]; exact Vp.vp_Wg_indec s _) hDK).1 hd
  rw [hvB, hBψ]
  exact (Vp.vp_first_of_cert hs hγ'0 hγ'N hown' hval' hcert').symm

/-- **The atom move at every finite `s ≥ 1`, no further hypothesis**: for `γ < V`, `y < Hˡ_γ(y) < ψ_W(A)`,
`Hˡ_γ(y) ∈ K_{c_{n+1}}`: `B_n γ < V` and `B_n(Hˡ_γ(y)) = Hˡ_{B_n γ}(B_n y)`. -/
theorem vsMove (hs : s < ω) (hs1 : 1 ≤ s) {n : ℕ} {γ y A : Ordinal.{0}} (hγ : γ < Om (s + 1 + 1))
    (hy : y < ulH S s γ y) (hθ : ulH S s γ y < S.psi A (Om (s + 1)))
    (hK : UlK S 0 (Bc.bcC S (n + 1)) (ulH S s γ y)) :
    Bc.bcB S n γ < Om (s + 1 + 1) ∧ Bc.bcB S n (ulH S s γ y) = ulH S s (Bc.bcB S n γ) (Bc.bcB S n y) := by
  have hs0 : s ≠ 0 := (lt_of_lt_of_le zero_lt_one hs1).ne'
  have h0s : (0 : Ordinal.{0}) < s := lt_of_lt_of_le zero_lt_one hs1
  have hq := Vm.vm_c_SC (S := S) n
  have hq1 := Vm.vm_c_le (S := S) n
  have hq01 : Bc.bcC S (n + 1) ≤ Om (0 + 1) := by rw [zero_add]; exact hq1
  have hqL : Bc.bcC S (n + 1) ≤ S.Lam := Us.us_qΛ (S := S) (i := 0) omega0_pos hq01
  have hzW : ulH S s γ y < Om (s + 1) := hθ.trans (Ui.ui_psi_lt (s := s) A)
  obtain ⟨hγK, hyK⟩ := (Uz.uz_L1 hs h0s hq hq01 hγ hzW (ne_of_gt hy)).1 hK
  have hDγ := Vm.vm_D_of_K hγK
  have hDz := Vm.vm_D_of_K hK
  obtain ⟨B, c, D, hown, hc, hcD, hcond, hcase⟩ := Vp.vp_dec (S := S) (s := s) hs hy hθ
  have hDy : D ≤ y := by rw [← hcD]; exact le_add_self
  have hcy : c ≤ y := by rw [← hcD]; exact le_self_add
  have hDW : D < Om (s + 1) := (hDy.trans_lt hy).trans hzW
  obtain ⟨hψe, howne⟩ := Vp.vp_run (S := S) (s := s) hs hγ hown hc hDW hcond
  rw [hcD] at hψe
  have heK : UlK S 0 (Bc.bcC S (n + 1)) (B + Om (s + 1) ^ γ * D) :=
    uoArg hqL (InR_Om_succ s) howne (by rw [hψe]; exact hK) (vs_c_psi hs1 n _)
  have h0θ : ulH S s γ 0 < S.psi A (Om (s + 1)) := ((ulH_le_iff γ).2 zero_le).trans_lt hθ
  have h0K : UlK S 0 (Bc.bcC S (n + 1)) (ulH S s γ 0) := Uz.uz_fv_K hs h0s hq hq01 hγ hγK
  have hparts : UlK S 0 (Bc.bcC S (n + 1)) B ∧ UlK S 0 (Bc.bcC S (n + 1)) D ∧ UlK S 0 (Bc.bcC S (n + 1)) c := by
    rcases hcase with hc0 | ⟨hcf, hmax⟩
    · rw [hc0] at hc hcD
      rw [zero_add] at hcD
      refine ⟨uoArg hqL (InR_Om_succ s) hown (by rw [← hc]; exact h0K) (vs_c_psi hs1 n B), by rw [hcD]; exact hyK,
        by rw [hc0]; exact UlK.zero⟩
    · have hcK : UlK S 0 (Bc.bcC S (n + 1)) c :=
        Uw.uw_fc_max hs h0s hq hq01 hγ hyK (hy.trans hzW) hcf hcy hmax
      refine ⟨uoArg hqL (InR_Om_succ s) hown (by rw [← hc, hcf]; exact hcK) (vs_c_psi hs1 n B), ?_, hcK⟩
      have e : D = y - c := by rw [← hcD, Ordinal.add_sub_cancel]
      rw [e]; exact (ulK_dec hq y hyK).1 c hcK hcy
  obtain ⟨hBK, hDK, hcK⟩ := hparts
  have hDB := Vm.vm_D_of_K hBK
  have hDD := Vm.vm_D_of_K hDK
  have hDc := Vm.vm_D_of_K hcK
  have hDe := Vm.vm_D_of_K heK
  obtain ⟨hDWD, hBWD⟩ := vsB_W (n := n) hs hDγ hDD
  obtain ⟨-, hBe⟩ := mvB_add (k := n) hDB hDWD
  rw [hBWD] at hBe
  obtain ⟨-, hBz, hownBe⟩ := vsB_psi (n := n) hs hs0 hDe howne
  rw [hψe] at hBz
  rw [hBe] at hBz hownBe
  obtain ⟨hDψ, hBψB, hownB'⟩ := vsB_psi (n := n) hs hs0 hDB hown
  obtain ⟨hDψV, hBψV, -⟩ := vsB_psi (s := s + 1) (n := n) (Ui.ui_s1_lt_omega hs)
    (lt_of_lt_of_le zero_lt_one le_add_self).ne' hDB (Vp.vp_ownV hown)
  have hγψ : γ ≤ S.psi B (Om (s + 1 + 1)) := Us.us_val_le hs hown hc
  have hγ'ψ : Bc.bcB S n γ ≤ S.psi (Bc.bcB S n B) (Om (s + 1 + 1)) := by
    rw [← hBψV]; exact Vp.vpB_le hDγ hDψV hγψ
  have hγ'V : Bc.bcB S n γ < Om (s + 1 + 1) := hγ'ψ.trans_lt (Ui.ui_psi_lt (s := s + 1) _)
  have hbase : ulH S s (Bc.bcB S n γ) (Bc.bcB S n c) = S.psi (Bc.bcB S n B) (Om (s + 1)) := by
    rcases hcase with hc0 | ⟨hcf, -⟩
    · rw [hc0] at hc ⊢
      rw [Bc.bcB_zero, ← vsFirst hs hs1 hγ h0θ h0K, hc, hBψB]
    · have hψc : S.psi B (Om (s + 1)) = c := hc.symm.trans hcf
      have hfixB : ulH S s γ (S.psi B (Om (s + 1))) = S.psi B (Om (s + 1)) := by rw [hψc, hcf]
      have hB0 : B ≠ 0 := by
        rintro rfl
        have hp0 : S.psi 0 (Om (s + 1)) = ulH S s 0 0 := (Us.us_psi0 hs).symm
        have hf0 : ulH S s 0 (S.psi 0 (Om (s + 1))) = S.psi 0 (Om (s + 1)) :=
          ucG_fix_mono zero_le hfixB ((ulD_le_self 0).trans_lt (Ui.ui_psi_SC (s := s) 0).1)
        rw [hp0] at hf0
        exact Us.us_val0_ne hf0
      obtain ⟨hdiv, hlt, hKγ⟩ := (Us.us_fix_iff hs hown hB0 hγ).1 hfixB
      have hDγ1 : MvD S (γ + 1) := (mvB_add (k := n) hDγ (Rk.rk_one_D (S := S))).1
      obtain ⟨hDW1, hBW1⟩ := vsB_Wpow (n := n) hs hDγ1
      have hdiv' : Om (s + 1) ^ (Bc.bcB S n γ + 1) ∣ Bc.bcB S n B := by
        have h := Vp.vp_dvd_B (n := n) hDW1 (Vp.vp_Wg_indec s _) (by rw [hBW1]; exact Vp.vp_Wg_indec s _) hDB hdiv
        rwa [hBW1, Rk.rkB_succ hDγ] at h
      have hlt' : Bc.bcB S n γ < S.psi (Bc.bcB S n B) (Om (s + 1 + 1)) := by
        rw [← hBψV]; exact (mvB_lt_iff hDγ hDψV).2 hlt
      have hK' : UlK S s (S.psi (Bc.bcB S n B) (Om (s + 1))) (Bc.bcB S n γ) := by
        have h := vsK_B (n := n) hs hDγ hDψ (Ui.ui_psi_SC (s := s) B) (Ui.ui_L_lt_psi (s := s) B)
          (Ui.ui_psi_lt (s := s) B).le (by rw [hBψB]; exact Ui.ui_psi_SC (s := s) _)
          (by rw [hBψB]; exact Ui.ui_L_lt_psi (s := s) _) (by rw [hBψB]; exact (Ui.ui_psi_lt (s := s) _).le)
        rw [hBψB] at h
        exact h.2 hKγ
      have hB'0 : Bc.bcB S n B ≠ 0 := by
        have h := (mvB_lt_iff (k := n) Uf.ufD_zero hDB).2 (pos_iff_ne_zero.2 hB0)
        rw [Bc.bcB_zero] at h
        exact h.ne'
      have hfix' := (Us.us_fix_iff hs hownB' hB'0 hγ'V).2 ⟨hdiv', hlt', hK'⟩
      have hBc : Bc.bcB S n c = S.psi (Bc.bcB S n B) (Om (s + 1)) := by rw [← hψc, hBψB]
      rw [hBc, hfix']
  have hdvd' : Om (s + 1) ^ Bc.bcB S n γ ∣ Bc.bcB S n B := Us.us_dvd_val hs hownB' hbase
  have hv' : Bc.bcB S n D <
      S.psi (Bc.bcB S n B + Om (s + 1) ^ Bc.bcB S n γ * Bc.bcB S n D) (Om (s + 1)) := by
    rw [← hBz]; exact (mvB_lt_iff hDD hDz).2 (hDy.trans_lt hy)
  have hcond' := Vp.vp_valid (S := S) (s := s) hs hdvd' hbase hv'
  have hD'W : Bc.bcB S n D < Om (s + 1) := hv'.trans (Ui.ui_psi_lt (s := s) _)
  have hrun := Us.us_run hs hγ'V hownB' hbase hD'W hcond'
  have hBy : Bc.bcB S n y = Bc.bcB S n c + Bc.bcB S n D := by rw [← hcD]; exact (mvB_add hDc hDD).2
  refine ⟨hγ'V, ?_⟩
  rw [hBz, hrun, hBy]

end Googology.Trans.PoR.InaccPsi.R2.Vs
