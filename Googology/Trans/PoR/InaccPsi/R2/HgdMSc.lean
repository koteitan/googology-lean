import Googology.Trans.PoR.InaccPsi.R2.HgPB
import Googology.Trans.PoR.InaccPsi.R2.HgS
import Googology.Trans.PoR.InaccPsi.R2.HgSRec
import Googology.Trans.PoR.InaccPsi.R2.HgSU
import Googology.Trans.PoR.InaccPsi.R2.HgX
import Googology.Trans.PoR.InaccPsi.R2.HgLv
import Googology.Trans.PoR.InaccPsi.R2.HgLvRec
import Googology.Trans.PoR.InaccPsi.R2.HgLvTop
import Googology.Trans.PoR.InaccPsi.R2.HgRec
import Googology.Trans.PoR.InaccPsi.R2.HgCh
import Googology.Trans.PoR.InaccPsi.R2.HgdX
import Googology.Trans.PoR.InaccPsi.R2.HgdCh
import Googology.Trans.PoR.InaccPsi.R2.HgdStep
import Googology.Trans.PoR.InaccPsi.R2.HgdLv
import Googology.Trans.PoR.InaccPsi.R2.HgdLvRec
import Googology.Trans.PoR.InaccPsi.R2.HgdLvTop
import Googology.Trans.PoR.InaccPsi.R2.HgdM
import Googology.Trans.PoR.InaccPsi.R2.HgdMLv
import Googology.Trans.PoR.InaccPsi.R2.HgdMRec
import Googology.Trans.PoR.InaccPsi.R2.HgdMTop

/-!
# HgdMSc: THE STEP OF A SUCCESSOR LEVEL AND THE STEP OF A LIMIT LEVEL

(Textual copy of `Hd.HdMSc` for `Hg.HgVD`: bound fields `< Γ_{x+2}` in place of `≤ B_x(x)` (`Hc.hcBR`); the proofs
are unchanged except where the bound enters.  Names: prefix `hg`/`Hg` (from `hc`/`Hc`), `hgd`/`Hgd` (from `hd`/`Hd`),
`hgf`/`Hgf` (from `hf`/`Hf`), `hge`/`Hge` (from `he`/`He`).)

* **Successor level** (`hgdScStart`, `hgdScT`, `hgdScT_spec`): for a step `St` of level `α` with the specification and a
  pseudo-base `P` of level `ν = α+1`, the step `St` at `P` (viewed at level `α`) starts the gated offset recursion over
  `P` viewed as a base of level `α` (`Hg.HgdQ.toB`), and the union of all its offsets (`Hg.hgdMTU`) has the
  specification of level `α+1` (bound `N_α(F) = hdNx (α+1) F`).
* **Limit level** (`hgdLmCh`, `hgdLmT`, `hgdLmT_spec`): for a limit level `λ`, an increasing sequence of constant levels
  `β_k` cofinal in `λ`, steps `St_k` of level `β_k` with the specification, coherent along `k` (each extends the
  previous one at every pseudo-base of level `λ`), the systems `St_k` at a pseudo-base `P` of level `λ` form a gated
  `ω`-chain (`Hg.HgdCh`), whose union has the specification of level `λ` (bound `hdNx λ F`).

No new axiom.  New definitions: `hgdScT`, `hgdLmCh`, `hgdLmT`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hg

open Googology.Trans.PoR.InaccPsi.R2.Hc
open Googology.Trans.PoR.InaccPsi.R2.Hd

open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The successor level -/

theorem hgd_lt_of_eq {α ν : Ordinal.{0}} (e : ν = α + 1) : α < ν := by rw [e]; exact lt_add_one α

section Succ

variable {α ν : Ordinal.{0}} (hα : HdLvl α) (e : ν = α + 1) (P : HgdQ ν)

/-- **The step of level `α` at `P` starts the offset recursion over `P` as a base of level `α`.** -/
theorem hgdScStart (U S0 : HgVD) (h0 : HgdQSpec (P.down hα (hgd_lt_of_eq e)) U S0) : HgdMStart (P.toB hα e) S0 where
  B := by
    rw [h0.B, add_zero]
    exact hdNx_fixP (P.toB hα e).F_fix
  Zb := fun x hx hx1 => by
    rw [h0.Z x hx hx1]
    show (if P.γ < x then evZ (hdNx α (P.Fr x)) else P.Zo x) ≤
      (if P.γ < x then hcN α (P.Fr x) else P.Zo x)
    split_ifs with hγ
    · exact (hb_evZ_lt_fix2 (hc_fix_down hα.two_lt.le (hcN_fix α _)) (hdNx_lt_N (hcN_gt α _))).le
    · exact le_rfl
  st := fun h2 hZ => {
    ix := by
      show S0.ix = veblen α (P.F + 1 + 0)
      refine hg_ix_of_B (veblen_veblen_of_lt hα.one_lt _) ?_
      rw [h0.B, add_zero]
      exact hdNx_fixP (P.toB hα e).F_fix
    γ := fun x _ _ => by
      show S0.γ < x ↔ max P.γ (S0.g 0) < x
      rw [h0.γ, S0.g_zero, max_eq_left zero_le]; rfl
    b := fun x hx hx1 hγ => by
      have hγ' : P.γ < x := by
        have : max P.γ (S0.g 0) < x := hγ
        rw [S0.g_zero, max_eq_left zero_le] at this; exact this
      show S0.b x = glA α (P.Fr x + S0.R 0 x) x
      rw [S0.R_zero, add_zero, h0.b x hx hx1 hγ']
      exact ((P.toB hα e).Fr_glA hx hx1 hγ').symm
    Z := fun x hx hx1 => by
      rw [h0.Z x hx hx1]
      unfold HgPB.Zst
      show (if P.γ < x then evZ (hdNx α (P.Fr x)) else P.Zo x) =
        if max P.γ (S0.g 0) < x then evZ (glA α (P.Fr x + S0.R 0 x) x) else (P.toB hα e).Zl x
      rw [S0.g_zero, max_eq_left zero_le, S0.R_zero, add_zero]
      by_cases hγ : P.γ < x
      · rw [if_pos hγ, if_pos hγ]; exact congrArg evZ ((P.toB hα e).Fr_glA hx hx1 hγ).symm
      · rw [if_neg hγ, if_neg hγ, (P.toB hα e).Zl_low hγ]; rfl }
  high0 := fun c σ hFc hc hσ hσ1 hg => by
    rw [h0.B] at hc
    exact h0.high c σ hFc hc hσ hσ1 hg

variable {St : ∀ (Q : HgdQ α) (U : HgVD), HgSStart (hgdQPB Q) U → HgVD} (hSt : ∀ Q U h, HgdQSpec Q U (St Q U h))
  (U : HgVD) (hU : HgSStart (hgdQPB P) U)

/-- **THE STEP OF LEVEL `α+1` AT `P`**: the union of all offsets over `P` as a base of level `α`, started at the step
of level `α` at `P`. -/
noncomputable def hgdScT : HgVD :=
  hgdMTU hSt (hgdScStart hα e P U (St (P.down hα (hgd_lt_of_eq e)) U hU) (hSt _ U hU))

/-- **THE STEP OF LEVEL `α+1` HAS THE SPECIFICATION.** -/
theorem hgdScT_spec : HgdQSpec P U (hgdScT hα e P hSt U hU) := by
  set S0 := St (P.down hα (hgd_lt_of_eq e)) U hU with hS0
  have h0 : HgdQSpec (P.down hα (hgd_lt_of_eq e)) U S0 := hSt _ U hU
  have hS := hgdScStart hα e P U S0 h0
  have hUB : U.B = P.F := hg_B_of_start hU
  have hFS : P.F < S0.B := by rw [h0.B]; exact hdNx_gt _ _
  have hUS : ∀ c, c < U.B → c < S0.B := fun c hc => hc.trans (by rw [hUB]; exact hFS)
  have hN : ∀ Q, hcN α Q = hdNx ν Q := fun Q => (hgdNx_of_eq e Q).symm
  refine ⟨by rw [← hN]; rfl, rfl, fun x _ _ _ => by rw [← hN]; rfl, fun x _ _ => by rw [← hN]; rfl,
    fun c x hc => ?_, fun c hc => ?_, fun c σ hFc hc hσ hσ1 hg => ?_, fun x hx hx1 hγ => ?_, fun x hx hx1 => ?_⟩
  · show (hgdMTU hSt hS).R c x = U.R c x
    rw [hgdMTU_R0 hSt hS (hUS c hc)]; exact h0.extR c x hc
  · show (hgdMTU hSt hS).g c = U.g c
    rw [hgdMTU_g0 hSt hS (hUS c hc)]; exact h0.extg c hc
  · rw [← hN] at hc; exact hgdMTU_high hSt hS hc hFc hσ hσ1 hg
  · show (hgdMTU hSt hS).R P.F x = P.Fr x
    rw [hgdMTU_R0 hSt hS hFS]; exact h0.RF x hx hx1 hγ
  · show (hgdMTU hSt hS).g P.F < x ↔ P.γ < x
    rw [hgdMTU_g0 hSt hS hFS]; exact h0.gF x hx hx1

/-- **The step of level `α+1` extends the step of level `α`.** -/
theorem hgdScT_ext {c : Ordinal.{0}} (hc : c < (St (P.down hα (hgd_lt_of_eq e)) U hU).B) (x : Ordinal.{0}) :
    (hgdScT hα e P hSt U hU).R c x = (St (P.down hα (hgd_lt_of_eq e)) U hU).R c x ∧
      (hgdScT hα e P hSt U hU).g c = (St (P.down hα (hgd_lt_of_eq e)) U hU).g c :=
  ⟨hgdMTU_R0 hSt _ hc x, hgdMTU_g0 hSt _ hc⟩

end Succ

/-! ## The limit level -/

/-- **The data of a limit level**: an increasing sequence of constant levels `β_k` cofinal in a limit `λ`. -/
structure HgdLm (l : Ordinal.{0}) where
  β : ℕ → Ordinal.{0}
  lv : ∀ k, HdLvl (β k)
  lt : ∀ k, β k < l
  mono : ∀ k, β k ≤ β (k + 1)
  cof : ∀ t, t < l → ∃ k, t < β k
  lim : IsSuccLimit l

namespace HgdLm

variable {l : Ordinal.{0}} (M : HgdLm l)

theorem mono' {j k : ℕ} (h : j ≤ k) : M.β j ≤ M.β k := by
  induction k, h using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact ih.trans (M.mono k)

/-- `c < hdNx λ Q` lies below some `hdNx β_k Q`. -/
theorem cofNx {Q c : Ordinal.{0}} (hc : c < hdNx l Q) : ∃ k, c < hdNx (M.β k) Q := by
  obtain ⟨k, hk⟩ := hdNx_cof M.lim M.lt M.mono M.cof hc
  obtain ⟨k', hk'⟩ := M.cof (M.β k + 1) (M.lim.add_one_lt (M.lt k))
  exact ⟨k', hk.trans_le (by rw [← hdNx_succ]; exact hgdNx_mono hk'.le Q)⟩

theorem Nx_lt (k : ℕ) (Q : Ordinal.{0}) : hdNx (M.β k) Q < hdNx l Q :=
  (hdNx_le (hc_LuP_of_fix (hcN_fix _ Q) |> hgd_LuP_mono le_self_add) (hcN_gt _ Q)).trans_lt
    (hdN_lt_Nx (M.lim.add_one_lt (M.lt k)))

end HgdLm

section Lim

variable {l : Ordinal.{0}} (M : HgdLm l) (St : ∀ k (Q : HgdQ (M.β k)) (U : HgVD), HgSStart (hgdQPB Q) U → HgVD)
  (hSt : ∀ k Q U h, HgdQSpec Q U (St k Q U h)) (P : HgdQ l) (U : HgVD) (hU : HgSStart (hgdQPB P) U)
  (hcoh : ∀ k c x, c < (St k (P.down (M.lv k) (M.lt k)) U hU).B →
    (St (k + 1) (P.down (M.lv (k + 1)) (M.lt (k + 1))) U hU).R c x = (St k (P.down (M.lv k) (M.lt k)) U hU).R c x ∧
    (St (k + 1) (P.down (M.lv (k + 1)) (M.lt (k + 1))) U hU).g c = (St k (P.down (M.lv k) (M.lt k)) U hU).g c)

/-- The member `k` of the chain at `P`. -/
noncomputable abbrev hgdLmD (k : ℕ) : HgVD := St k (P.down (M.lv k) (M.lt k)) U hU

include hSt in
theorem hgdLmD_spec (k : ℕ) : HgdQSpec (P.down (M.lv k) (M.lt k)) U (hgdLmD M St P U hU k) := hSt k _ U hU

include hcoh hSt in
/-- **THE GATED `ω`-CHAIN OF THE LOWER STEPS AT `P`**: union bound `hdNx λ F`, union base reading
`hdNx λ (F(x))`. -/
noncomputable def hgdLmCh : HgdCh where
  D := hgdLmD M St P U hU
  B := hdNx l P.F
  b := fun x => hdNx l (P.Fr x)
  γ := P.γ
  Zo := P.Zo
  γ_lt := P.γ_lt
  γ0 := fun k => (hgdLmD_spec M St hSt P U hU k).γ
  γ_cl := fun Z hZ hZ1 h => P.S_cl Z hZ hZ1 h
  B_mono := fun k => by
    rw [(hgdLmD_spec M St hSt P U hU k).B, (hgdLmD_spec M St hSt P U hU (k + 1)).B]; exact hgdNx_mono (M.mono k) _
  B_lt := fun k => by rw [(hgdLmD_spec M St hSt P U hU k).B]; exact M.Nx_lt k _
  B_cof := fun c hc => by
    obtain ⟨k, hk⟩ := M.cofNx hc
    exact ⟨k, by rw [(hgdLmD_spec M St hSt P U hU k).B]; exact hk⟩
  R_ext := fun k c x hc => (hcoh k c x hc).1
  g_ext := fun k c hc => (hcoh k c 0 hc).2
  B_lt1 := P.S_lt1
  B_fix := veblen_veblen_of_lt (one_lt_omega0.trans_le P.lv.1) _
  B_mem := fun S _ _ ha hb => P.S_mem S ha hb
  b_ge := fun k x hx hx1 hγ => by
    rw [(hgdLmD_spec M St hSt P U hU k).b x hx hx1 hγ]; exact hgdNx_mono (M.lt k).le _
  b_cof := fun x hx hx1 hγ μ hμ => by
    obtain ⟨k, hk⟩ := M.cofNx hμ
    exact ⟨k, by rw [(hgdLmD_spec M St hSt P U hU k).b x hx hx1 hγ]; exact hk⟩
  b_fix := fun x _ _ _ => veblen_veblen_of_lt (one_lt_omega0.trans_le P.lv.1) _
  b_gt := fun x hx hx1 hγ => (P.Fr_gt hx hx1 hγ).trans (hdNx_gt _ _)
  b_lt := fun x hx hx1 hγ => P.S_lt_G1 hx hx1 hγ
  b_pi := fun _ _ hB hγ => P.S_pi hB hγ
  Z_low := fun k x hx hx1 hγ => by
    rw [(hgdLmD_spec M St hSt P U hU k).Z x hx hx1]
    show (if P.γ < x then _ else P.Zo x) ≤ P.Zo x
    rw [if_neg hγ]
  Zo_fix := fun x => ha_fix1_of_fix2 (P.Zo_fix x)
  Zo_G1 := P.Zo_G1

/-- **THE STEP OF THE LIMIT LEVEL `λ` AT `P`**: the union of the chain of the lower steps. -/
noncomputable def hgdLmT : HgVD := (hgdLmCh M St hSt P U hU hcoh).U

/-- **THE STEP OF A LIMIT LEVEL HAS THE SPECIFICATION.** -/
theorem hgdLmT_spec : HgdQSpec P U (hgdLmT M St hSt P U hU hcoh) := by
  set C := hgdLmCh M St hSt P U hU hcoh with hC
  have hUB : U.B = P.F := hg_B_of_start hU
  have hF0 : P.F < (C.D 0).B := by
    show P.F < (hgdLmD M St P U hU 0).B
    rw [(hgdLmD_spec M St hSt P U hU 0).B]; exact hdNx_gt _ _
  have hU0 : ∀ c, c < U.B → c < (C.D 0).B := fun c hc => hc.trans (by rw [hUB]; exact hF0)
  refine ⟨rfl, rfl, fun _ _ _ _ => rfl, fun x _ _ => rfl, fun c x hc => ?_, fun c hc => ?_,
    fun c σ hFc hc hσ hσ1 hg => ?_, fun x hx hx1 hγ => ?_, fun x hx hx1 => ?_⟩
  · show C.U.R c x = U.R c x
    rw [C.U_R (k := 0) (hU0 c hc)]; exact (hgdLmD_spec M St hSt P U hU 0).extR c x hc
  · show C.U.g c = U.g c
    rw [C.U_g (k := 0) (hU0 c hc)]; exact (hgdLmD_spec M St hSt P U hU 0).extg c hc
  · obtain ⟨k, hk⟩ := C.B_cof c hc
    have hg' : (hgdLmD M St P U hU k).g c < σ := by
      have e : C.U.g c = (C.D k).g c := C.U_g (k := k) hk
      show (C.D k).g c < σ
      rw [← e]; exact hg
    have hk' : c < hdNx (M.β k) P.F := by
      have := (hgdLmD_spec M St hSt P U hU k).B; exact this ▸ hk
    exact (hgdLmD_spec M St hSt P U hU k).high c σ hFc hk' hσ hσ1 hg'
  · show C.U.R P.F x = P.Fr x
    rw [C.U_R (k := 0) hF0]; exact (hgdLmD_spec M St hSt P U hU 0).RF x hx hx1 hγ
  · show C.U.g P.F < x ↔ P.γ < x
    rw [C.U_g (k := 0) hF0]; exact (hgdLmD_spec M St hSt P U hU 0).gF x hx hx1

/-- **The step of a limit level extends every member of the chain.** -/
theorem hgdLmT_ext (k : ℕ) {c : Ordinal.{0}} (hc : c < (hgdLmD M St P U hU k).B) (x : Ordinal.{0}) :
    (hgdLmT M St hSt P U hU hcoh).R c x = (hgdLmD M St P U hU k).R c x ∧
      (hgdLmT M St hSt P U hU hcoh).g c = (hgdLmD M St P U hU k).g c :=
  ⟨(hgdLmCh M St hSt P U hU hcoh).U_R (k := k) hc x, (hgdLmCh M St hSt P U hU hcoh).U_g (k := k) hc⟩

end Lim

end Googology.Trans.PoR.InaccPsi.R2.Hg
