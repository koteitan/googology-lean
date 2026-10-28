import Googology.Trans.PoR.InaccPsi.R2.HjVTop

/-!
# HjVSc: THE STEP OF THE LEVEL `L + ν + 1` FROM THE STEP OF THE LEVEL `L + ν`, AND THE STEP OF A LIMIT LEVEL

PORT of `Hi.HiVSc` to a level datum `Λ : Hj.HjLv`: the prefix `Ω₁` of the level `Ω₁ + ν` (read `x + ν`) is replaced by
`Λ.L` (read `Λ.l x`), so every level below is `Λ.L + ν`, read `Λ.l x + ν`.  What differs: the statements carry the
parameter `Λ`; the facts `Ω₁ ≤ L`, `x ≤ ℓ(x) < Γ_{x+1}`, the level gate (`Hj.hjv_cl_gate`) and Lemma EXACT for `ℓ`
come from `Λ`.  With `Λ = Hj.hjL1` it is `Hi.HiVSc` again.

The port of `Hg.HgfMSc` to the levels `L + ν` read as `Λ.l x + ν`:

* the successor (`hjVScStart`, `hjVScT`, `hjVScT_spec`): at a pseudo-base `P` of level `L + ν + 1`, the step of
  level `L + ν` at `P` starts the offset recursion over `P` as a base of level `L + ν` (`Hj.HjVQ.toB`), and the
  union of all its offsets (`Hj.hjVTU`) is the step of level `L + ν + 1` (bound `hdNx (L + ν+1) F`), with the
  specification `Hj.HjVSpec`;
* the limit (`HjVLm`, `hjVLmCh`, `hjVLmT`, `hjVLmT_spec`): at a pseudo-base of a limit level `L + λ`, the gated
  `ω`-chain of the steps of the levels `L + λ_k` (`Hg.HgdCh`) has the union `hjVLmT` with the specification.

No new axiom.  New definitions: `hjVScT`, `HjVLm`, `hjVLmD`, `hjVLmCh`, `hjVLmT`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hj

open Googology.Trans.PoR.InaccPsi.R2.Hi

open Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

variable {Λ : HjLv}

theorem hjv_lt_of_eq {κ ν : Ordinal.{0}} (e : ν = κ + 1) : κ < ν := by rw [e]; exact lt_add_one κ

/-! ## The successor level -/

theorem hjv_Nx_eq {κ ν : Ordinal.{0}} (e : ν = κ + 1) (a Q : Ordinal.{0}) : hdNx (a + ν) Q = hcN (a + κ) Q :=
  hdNx_of_eq (hjv_succ_e e a) Q

section Succ

variable {κ ν : Ordinal.{0}} (e : ν = κ + 1) (P : HjVQ Λ ν)

/-- **The step of level `L + κ` at `P` starts the offset recursion over `P` as a base of level `L + κ`.** -/
theorem hjVScStart (U S0 : HgVD) (h0 : HjVSpec (P.down (hjv_lt_of_eq e)) U S0) : HjVStart (P.toB e) S0 where
  B := by
    rw [h0.B, add_zero]
    exact hdNx_fixP (P.toB e).F_fix
  Zb := fun x hx hx1 => by
    rw [h0.Z x hx hx1]
    show (if P.γ < x then evZ (hdNx (Λ.l x + κ) (P.Fr x)) else P.Zo x) ≤ (P.toB e).Zl x
    by_cases hγ : P.γ < x
    · rw [if_pos hγ, (P.toB e).Zl_eq hx hγ]
      exact (hb_evZ_lt_fix2 (hc_fix_down ((show (2 : Ordinal.{0}) ≤ ω from
        (by exact_mod_cast (natCast_lt_omega0 2).le)).trans (hjv_ωl Λ hx hx1).le)
        (hcN_fix _ _)) (hdNx_lt_N (hcN_gt _ _))).le
    · rw [if_neg hγ, (P.toB e).Zl_low hγ]; rfl
  st := fun h2 hZ => {
    ix := by
      show S0.ix = veblen (Λ.L + κ) (P.F + 1 + 0)
      refine hg_ix_of_B (veblen_veblen_of_lt ((hg_one_lt_Om1.trans_le Λ.OL).trans_le le_self_add) _) ?_
      rw [h0.B, add_zero]
      exact hdNx_fixP (P.toB e).F_fix
    γ := fun x _ _ => by
      show S0.γ < x ↔ max P.γ (S0.g 0) < x
      rw [h0.γ, S0.g_zero, max_eq_left zero_le]; rfl
    b := fun x hx hx1 hγ => by
      have hγ' : P.γ < x := by
        have : max P.γ (S0.g 0) < x := hγ
        rw [S0.g_zero, max_eq_left zero_le] at this; exact this
      show S0.b x = glA (Λ.l x + κ) (P.Fr x + S0.R 0 x) x
      rw [S0.R_zero, add_zero, h0.b x hx hx1 hγ']
      exact ((P.toB e).Fr_glA hx hx1 hγ').symm
    Z := fun x hx hx1 => by
      rw [h0.Z x hx hx1]
      unfold HgPB.Zst
      show (if P.γ < x then evZ (hdNx (Λ.l x + κ) (P.Fr x)) else P.Zo x) =
        if max P.γ (S0.g 0) < x then evZ (glA (Λ.l x + κ) (P.Fr x + S0.R 0 x) x) else (P.toB e).Zl x
      rw [S0.g_zero, max_eq_left zero_le, S0.R_zero, add_zero]
      by_cases hγ : P.γ < x
      · rw [if_pos hγ, if_pos hγ]; exact congrArg evZ ((P.toB e).Fr_glA hx hx1 hγ).symm
      · rw [if_neg hγ, if_neg hγ, (P.toB e).Zl_low hγ]; rfl }
  high0 := fun c σ hFc hc hσ hσ1 hg => by
    rw [h0.B] at hc
    exact h0.high c σ hFc hc hσ hσ1 hg

variable {St : ∀ (Q : HjVQ Λ κ) (U : HgVD), HgSStart (hjVPB Q) U → HgVD} (hSt : ∀ Q U h, HjVSpec Q U (St Q U h))
  (U : HgVD) (hU : HgSStart (hjVPB P) U)

/-- **THE STEP OF LEVEL `L + κ + 1` AT `P`**: the union of all offsets over `P` as a base of level `L + κ`, started
at the step of level `L + κ` at `P`. -/
noncomputable def hjVScT : HgVD :=
  hjVTU hSt (hjVScStart e P U (St (P.down (hjv_lt_of_eq e)) U hU) (hSt _ U hU))

/-- **THE STEP OF LEVEL `L + κ + 1` HAS THE SPECIFICATION.** -/
theorem hjVScT_spec : HjVSpec P U (hjVScT e P hSt U hU) := by
  set S0 := St (P.down (hjv_lt_of_eq e)) U hU with hS0
  have h0 : HjVSpec (P.down (hjv_lt_of_eq e)) U S0 := hSt _ U hU
  have hS := hjVScStart e P U S0 h0
  have hUB : U.B = P.F := hg_B_of_start hU
  have hFS : P.F < S0.B := by rw [h0.B]; exact hdNx_gt _ _
  have hUS : ∀ c, c < U.B → c < S0.B := fun c hc => hc.trans (by rw [hUB]; exact hFS)
  refine ⟨by rw [hjv_Nx_eq e]; rfl, rfl, fun x _ _ _ => by rw [hjv_Nx_eq e]; rfl,
    fun x _ _ => by rw [hjv_Nx_eq e]; rfl,
    fun c x hc => ?_, fun c hc => ?_, fun c σ hFc hc hσ hσ1 hg => ?_, fun x hx hx1 hγ => ?_, fun x hx hx1 => ?_⟩
  · show (hjVTU hSt hS).R c x = U.R c x
    rw [hjVTU_R0 hSt hS (hUS c hc)]; exact h0.extR c x hc
  · show (hjVTU hSt hS).g c = U.g c
    rw [hjVTU_g0 hSt hS (hUS c hc)]; exact h0.extg c hc
  · rw [hjv_Nx_eq e] at hc; exact hjVTU_high hSt hS rfl hc hFc hσ hσ1 hg
  · show (hjVTU hSt hS).R P.F x = P.Fr x
    rw [hjVTU_R0 hSt hS hFS]; exact h0.RF x hx hx1 hγ
  · show (hjVTU hSt hS).g P.F < x ↔ P.γ < x
    rw [hjVTU_g0 hSt hS hFS]; exact h0.gF x hx hx1

/-- **The step of level `L + κ + 1` extends the step of level `L + κ`.** -/
theorem hjVScT_ext {c : Ordinal.{0}} (hc : c < (St (P.down (hjv_lt_of_eq e)) U hU).B) (x : Ordinal.{0}) :
    (hjVScT e P hSt U hU).R c x = (St (P.down (hjv_lt_of_eq e)) U hU).R c x ∧
      (hjVScT e P hSt U hU).g c = (St (P.down (hjv_lt_of_eq e)) U hU).g c :=
  ⟨hjVTU_R0 hSt _ hc x, hjVTU_g0 hSt _ hc⟩

end Succ

/-! ## The limit level -/

/-- **The data of a limit level**: an increasing sequence `β_k` cofinal in a limit `λ < Ω₁`. -/
structure HjVLm (l : Ordinal.{0}) where
  β : ℕ → Ordinal.{0}
  lt : ∀ k, β k < l
  mono : ∀ k, β k ≤ β (k + 1)
  cof : ∀ t, t < l → ∃ k, t < β k
  lim : IsSuccLimit l
  lv : l < Om1

namespace HjVLm

variable {l : Ordinal.{0}} (M : HjVLm l)

theorem mono' {j k : ℕ} (h : j ≤ k) : M.β j ≤ M.β k := by
  induction k, h using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact ih.trans (M.mono k)

/-- `c < hdNx (a + λ) Q` lies below some `hdNx (a + β_k) Q`. -/
theorem cofNx (a : Ordinal.{0}) {Q c : Ordinal.{0}} (hc : c < hdNx (a + l) Q) : ∃ k, c < hdNx (a + M.β k) Q := by
  have hlim : IsSuccLimit (a + l) := isSuccLimit_add a M.lim
  obtain ⟨k, hk⟩ := hdNx_cof hlim (β := fun k => a + M.β k) (fun k => (add_lt_add_iff_left a).2 (M.lt k))
    (fun k => add_le_add le_rfl (M.mono k)) (fun t ht => by
      rcases lt_or_ge t a with hta | hta
      · exact ⟨0, hta.trans_le le_self_add⟩
      · obtain ⟨t', rfl⟩ := exists_add_of_le hta
        obtain ⟨k, hk⟩ := M.cof t' ((add_lt_add_iff_left a).1 ht)
        exact ⟨k, (add_lt_add_iff_left a).2 hk⟩) hc
  obtain ⟨k', hk'⟩ := M.cof (M.β k + 1) (M.lim.add_one_lt (M.lt k))
  refine ⟨k', hk.trans_le ?_⟩
  rw [← hdNx_succ, add_assoc]
  exact hdNx_mono (add_le_add le_rfl hk'.le) Q

theorem Nx_lt (a : Ordinal.{0}) (k : ℕ) (Q : Ordinal.{0}) : hdNx (a + M.β k) Q < hdNx (a + l) Q :=
  (hdNx_le (hc_LuP_of_fix (hcN_fix _ Q) |> hd_LuP_mono le_self_add) (hcN_gt _ Q)).trans_lt
    (hdN_lt_Nx (by rw [add_assoc]; exact (add_lt_add_iff_left a).2 (M.lim.add_one_lt (M.lt k))))

end HjVLm

section Lim

variable {l : Ordinal.{0}} (M : HjVLm l) (St : ∀ k (Q : HjVQ Λ (M.β k)) (U : HgVD), HgSStart (hjVPB Q) U → HgVD)
  (hSt : ∀ k Q U h, HjVSpec Q U (St k Q U h)) (P : HjVQ Λ l) (U : HgVD) (hU : HgSStart (hjVPB P) U)
  (hcoh : ∀ k c x, c < (St k (P.down (M.lt k)) U hU).B →
    (St (k + 1) (P.down (M.lt (k + 1))) U hU).R c x = (St k (P.down (M.lt k)) U hU).R c x ∧
    (St (k + 1) (P.down (M.lt (k + 1))) U hU).g c = (St k (P.down (M.lt k)) U hU).g c)

/-- The member `k` of the chain at `P`. -/
noncomputable abbrev hjVLmD (k : ℕ) : HgVD := St k (P.down (M.lt k)) U hU

include hSt in
theorem hjVLmD_spec (k : ℕ) : HjVSpec (P.down (M.lt k)) U (hjVLmD M St P U hU k) := hSt k _ U hU

include hcoh hSt in
/-- **THE GATED `ω`-CHAIN OF THE LOWER STEPS AT `P`**: union bound `hdNx (L + λ) F`, union base reading
`hdNx (x+λ) (F(x))`. -/
noncomputable def hjVLmCh : HgdCh where
  D := hjVLmD M St P U hU
  B := hdNx (Λ.L + l) P.F
  b := fun x => hdNx (Λ.l x + l) (P.Fr x)
  γ := P.γ
  Zo := P.Zo
  γ_lt := P.γ_lt
  γ0 := fun k => (hjVLmD_spec M St hSt P U hU k).γ
  γ_cl := fun Z hZ hZ1 h => P.S_cl Z hZ hZ1 h
  B_mono := fun k => by
    rw [(hjVLmD_spec M St hSt P U hU k).B, (hjVLmD_spec M St hSt P U hU (k + 1)).B]
    exact hdNx_mono (add_le_add le_rfl (M.mono k)) _
  B_lt := fun k => by rw [(hjVLmD_spec M St hSt P U hU k).B]; exact M.Nx_lt Λ.L k _
  B_cof := fun c hc => by
    obtain ⟨k, hk⟩ := M.cofNx Λ.L hc
    exact ⟨k, by rw [(hjVLmD_spec M St hSt P U hU k).B]; exact hk⟩
  R_ext := fun k c x hc => (hcoh k c x hc).1
  g_ext := fun k c hc => (hcoh k c 0 hc).2
  B_lt1 := P.S_lt1
  B_fix := hdNx_fix ((hg_one_lt_Om1.trans_le Λ.OL).trans_le le_self_add) _
  B_mem := fun S _ _ ha hb => P.S_mem S ha hb
  b_ge := fun k x hx hx1 hγ => by
    rw [(hjVLmD_spec M St hSt P U hU k).b x hx hx1 hγ]; exact hdNx_mono (add_le_add le_rfl (M.lt k).le) _
  b_cof := fun x hx hx1 hγ μ hμ => by
    obtain ⟨k, hk⟩ := M.cofNx (Λ.l x) hμ
    exact ⟨k, by rw [(hjVLmD_spec M St hSt P U hU k).b x hx hx1 hγ]; exact hk⟩
  b_fix := fun x hx hx1 _ => hdNx_fix (one_lt_omega0.trans (hjv_ωl Λ hx hx1)) _
  b_gt := fun x hx hx1 hγ => (P.Fr_gtx hx hx1 hγ).trans (hdNx_gt _ _)
  b_lt := fun x hx hx1 hγ => P.S_lt1x hx hx1 hγ
  b_pi := fun _ _ hB hγ => P.S_pi hB hγ
  Z_low := fun k x hx hx1 hγ => by
    rw [(hjVLmD_spec M St hSt P U hU k).Z x hx hx1]
    show (if P.γ < x then _ else P.Zo x) ≤ P.Zo x
    rw [if_neg hγ]
  Zo_fix := fun x => ha_fix1_of_fix2 (P.Zo_fix x)
  Zo_G1 := P.Zo_G1

/-- **THE STEP OF THE LIMIT LEVEL `L + λ` AT `P`**: the union of the chain of the lower steps. -/
noncomputable def hjVLmT : HgVD := (hjVLmCh M St hSt P U hU hcoh).U

/-- **THE STEP OF A LIMIT LEVEL HAS THE SPECIFICATION.** -/
theorem hjVLmT_spec : HjVSpec P U (hjVLmT M St hSt P U hU hcoh) := by
  set C := hjVLmCh M St hSt P U hU hcoh with hC
  have hUB : U.B = P.F := hg_B_of_start hU
  have hF0 : P.F < (C.D 0).B := by
    show P.F < (hjVLmD M St P U hU 0).B
    rw [(hjVLmD_spec M St hSt P U hU 0).B]; exact hdNx_gt _ _
  have hU0 : ∀ c, c < U.B → c < (C.D 0).B := fun c hc => hc.trans (by rw [hUB]; exact hF0)
  refine ⟨rfl, rfl, fun _ _ _ _ => rfl, fun x _ _ => rfl, fun c x hc => ?_, fun c hc => ?_,
    fun c σ hFc hc hσ hσ1 hg => ?_, fun x hx hx1 hγ => ?_, fun x hx hx1 => ?_⟩
  · show C.U.R c x = U.R c x
    rw [C.U_R (k := 0) (hU0 c hc)]; exact (hjVLmD_spec M St hSt P U hU 0).extR c x hc
  · show C.U.g c = U.g c
    rw [C.U_g (k := 0) (hU0 c hc)]; exact (hjVLmD_spec M St hSt P U hU 0).extg c hc
  · obtain ⟨k, hk⟩ := C.B_cof c hc
    have hg' : (hjVLmD M St P U hU k).g c < σ := by
      have e : C.U.g c = (C.D k).g c := C.U_g (k := k) hk
      show (C.D k).g c < σ
      rw [← e]; exact hg
    have hk' : c < hdNx (Λ.L + M.β k) P.F := by
      have := (hjVLmD_spec M St hSt P U hU k).B; exact this ▸ hk
    exact (hjVLmD_spec M St hSt P U hU k).high c σ hFc hk' hσ hσ1 hg'
  · show C.U.R P.F x = P.Fr x
    rw [C.U_R (k := 0) hF0]; exact (hjVLmD_spec M St hSt P U hU 0).RF x hx hx1 hγ
  · show C.U.g P.F < x ↔ P.γ < x
    rw [C.U_g (k := 0) hF0]; exact (hjVLmD_spec M St hSt P U hU 0).gF x hx hx1

/-- **The step of a limit level extends every member of the chain.** -/
theorem hjVLmT_ext (k : ℕ) {c : Ordinal.{0}} (hc : c < (hjVLmD M St P U hU k).B) (x : Ordinal.{0}) :
    (hjVLmT M St hSt P U hU hcoh).R c x = (hjVLmD M St P U hU k).R c x ∧
      (hjVLmT M St hSt P U hU hcoh).g c = (hjVLmD M St P U hU k).g c :=
  ⟨(hjVLmCh M St hSt P U hU hcoh).U_R (k := k) hc x, (hjVLmCh M St hSt P U hU hcoh).U_g (k := k) hc⟩

end Lim

end Googology.Trans.PoR.InaccPsi.R2.Hj
