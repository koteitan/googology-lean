import Googology.Trans.PoR.InaccPsi.R2.HnMLv

/-!
# HnPkL: THE STEP OF A GATED LIMIT BAND LEVEL `Ω₁·Ω₁ + Ω₁·M` FROM A COHERENT `ω`-SEQUENCE OF PACKAGES

PORT of `Hl.HlPkL` (the same proofs) to the band level datum `Hn.HnLv`.  What differs: the levels of the sequence
`HnkSeq` are `Ω₁·Ω₁ + Ω₁·M_k` read `x·x + x·M_k` (in `Hl.HlkSeq`: `Ω₁·M_k` read `x·M_k`), so the comparisons carry the
prefix `Ω₁·Ω₁` / `x·x`, and the cofinality of the chain bounds uses `hn_cof1` (prefix `Ω₁·Ω₁`, resp. `x·x`) in place
of `Hk.hk_mul_cof1`.

No new axiom.  New definitions: `HnkExt`, `HnkSeq`, `HnkSeq.D`, `hnkCh`, `hnkStL`, `hnkPkL`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hn

open Googology.Trans.PoR.InaccPsi.R2.Hl

open Googology.Trans.PoR.InaccPsi.R2.Hk

open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
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

/-- **The extension statement between two packages**: at every pseudo-base `Q` of the level of `K` (`L + 0`), the
step of `K` at `Q` extends the step of `K'` at `Q` read at the lower level (`HnVQ.lowr`). -/
def HnkExt (K' K : HnPk) : Prop :=
  ∀ (hg : K'.Λ.g ≤ K.Λ.g) (hL : K'.Λ.L + Om1 ≤ K.Λ.L) (hl : ∀ x, InE x → x < Om1 → K.Λ.g < x → K'.Λ.l x + x ≤ K.Λ.l x)
    (Q : HnVQ K.Λ 0) (U : HgVD) (hU : HgSStart (hnVPB Q) U) (c x : Ordinal.{0}),
    c < (K'.St0 (Q.lowr K'.Λ hg hL hl) U hU).B →
    (K.St0 Q U hU).R c x = (K'.St0 (Q.lowr K'.Λ hg hL hl) U hU).R c x ∧
    (K.St0 Q U hU).g c = (K'.St0 (Q.lowr K'.Λ hg hL hl) U hU).g c

/-- **A coherent sequence of packages below a limit level datum `Λ`** (`L = Ω₁·M`, `ℓ(x) = x·M`): packages `K_k` at
the levels `Ω₁·M_k`, `M_k` strictly increasing and cofinal in `M`, each step extending the previous one. -/
structure HnkSeq (Λ : HnLv) where
  M : Ordinal.{0}
  K : ℕ → HnPk
  Ms : ℕ → Ordinal.{0}
  L_eq : Λ.L = Om1 * Om1 + Om1 * M
  l_eq : ∀ x, Λ.g < x → Λ.l x = x * x + x * M
  KL : ∀ k, (K k).Λ.L = Om1 * Om1 + Om1 * Ms k
  Kl : ∀ k x, (K k).Λ.g < x → (K k).Λ.l x = x * x + x * Ms k
  lt : ∀ k, Ms k < M
  mono : ∀ k, Ms k < Ms (k + 1)
  cof : ∀ t, t < M → ∃ k, t < Ms k
  Kg : ∀ k, (K k).Λ.g ≤ Λ.g
  Kgm : ∀ k, (K k).Λ.g ≤ (K (k + 1)).Λ.g
  ext : ∀ k, HnkExt (K k) (K (k + 1))

namespace HnkSeq

variable {Λ : HnLv} (H : HnkSeq Λ)

theorem hL (k : ℕ) : (H.K k).Λ.L + Om1 ≤ Λ.L := by
  rw [H.KL, H.L_eq, add_assoc]; exact add_le_add le_rfl (HkSeq.mul_le (H.lt k))

theorem hl (k : ℕ) : ∀ x, InE x → x < Om1 → Λ.g < x → (H.K k).Λ.l x + x ≤ Λ.l x := fun x _ _ hg => by
  rw [H.Kl k x ((H.Kg k).trans_lt hg), H.l_eq x hg, add_assoc]; exact add_le_add le_rfl (HkSeq.mul_le (H.lt k))

theorem hLs (k : ℕ) : (H.K k).Λ.L + Om1 ≤ (H.K (k + 1)).Λ.L := by
  rw [H.KL, H.KL, add_assoc]; exact add_le_add le_rfl (HkSeq.mul_le (H.mono k))

theorem hls (k : ℕ) : ∀ x, InE x → x < Om1 → (H.K (k + 1)).Λ.g < x →
    (H.K k).Λ.l x + x ≤ (H.K (k + 1)).Λ.l x := fun x _ _ hg => by
  rw [H.Kl k x ((H.Kgm k).trans_lt hg), H.Kl (k + 1) x hg, add_assoc]
  exact add_le_add le_rfl (HkSeq.mul_le (H.mono k))

section Q

variable (Q : HnVQ Λ 0) (U : HgVD) (hU : HgSStart (hnVPB Q) U)

/-- The member `k` of the chain at `Q`: the step of the package `K_k` at `Q`. -/
noncomputable abbrev D (k : ℕ) : HgVD := (H.K k).St0 (Q.lowr (H.K k).Λ (H.Kg k) (H.hL k) (H.hl k)) U hU

theorem D_spec (k : ℕ) : HnVSpec (Q.lowr (H.K k).Λ (H.Kg k) (H.hL k) (H.hl k)) U (H.D Q U hU k) := (H.K k).h0 _ U hU

theorem D_ext (k : ℕ) {c : Ordinal.{0}} (hc : c < (H.D Q U hU k).B) (x : Ordinal.{0}) :
    (H.D Q U hU (k + 1)).R c x = (H.D Q U hU k).R c x ∧ (H.D Q U hU (k + 1)).g c = (H.D Q U hU k).g c :=
  H.ext k (H.Kgm k) (H.hLs k) (H.hls k) (Q.lowr (H.K (k + 1)).Λ (H.Kg (k + 1)) (H.hL (k + 1)) (H.hl (k + 1))) U hU
    c x hc

theorem D_B (k : ℕ) : (H.D Q U hU k).B = hdNx (Om1 * Om1 + Om1 * H.Ms k + 0) Q.F := by
  rw [(H.D_spec Q U hU k).B, H.KL]; rfl

theorem D_b (k : ℕ) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : Q.γ < x) :
    (H.D Q U hU k).b x = hdNx (x * x + x * H.Ms k + 0) (Q.Fr x) := by
  rw [(H.D_spec Q U hU k).b x hx hx1 hγ, H.Kl k x (((H.Kg k).trans Q.lg).trans_lt hγ)]; rfl

end Q

end HnkSeq

section Ch

variable {Λ : HnLv} (H : HnkSeq Λ) (Q : HnVQ Λ 0) (U : HgVD) (hU : HgSStart (hnVPB Q) U)

/-- **THE GATED `ω`-CHAIN OF THE STEPS OF THE PACKAGES `K_k` AT `Q`**: union bound `hdNx (Ω₁·M) F`, union base
reading `hdNx (x·M) (F(x))`. -/
noncomputable def hnkCh : HgdCh where
  D := H.D Q U hU
  B := hdNx (Λ.L + 0) Q.F
  b := fun x => hdNx (Λ.l x + 0) (Q.Fr x)
  γ := Q.γ
  Zo := Q.Zo
  γ_lt := Q.γ_lt
  γ0 := fun k => (H.D_spec Q U hU k).γ
  γ_cl := fun Z hZ hZ1 h => Q.S_cl Z hZ hZ1 h
  B_mono := fun k => by
    rw [H.D_B, H.D_B]
    exact hdNx_mono (add_le_add (add_le_add le_rfl (mul_le_mul_left' (H.mono k).le _)) le_rfl) _
  B_lt := fun k => by rw [(H.D_spec Q U hU k).B]; exact Q.lw_S_lt _ (H.hL k)
  B_cof := fun c hc => by
    obtain ⟨b, hb, hcb⟩ := hjw_Nx_cof (hnv_L0 Λ 0) Q.F_P hc
    rw [add_zero, H.L_eq] at hb
    obtain ⟨k, hk⟩ := hn_cof1 (fun _ h => hn_sq_succ gl_Om1_E h) gv_Om1_pos H.mono H.cof hb
    refine ⟨k, ?_⟩
    rw [H.D_B]
    exact hcb.trans (hdN_lt_Nx (by rw [add_zero]; exact hk))
  R_ext := fun k c x hc => (H.D_ext Q U hU k hc x).1
  g_ext := fun k c hc => (H.D_ext Q U hU k hc 0).2
  B_lt1 := Q.S_lt1
  B_fix := hdNx_fix ((hg_one_lt_Om1.trans_le Λ.OL).trans_le le_self_add) _
  B_mem := fun S _ _ ha hb => Q.S_mem S ha hb
  b_ge := fun k x hx hx1 hγ => by
    rw [(H.D_spec Q U hU k).b x hx hx1 hγ]
    show hdNx ((H.K k).Λ.l x + 0) (Q.Fr x) ≤ hdNx (Λ.l x + 0) (Q.Fr x)
    rw [add_zero, add_zero]; exact hdNx_mono (le_self_add.trans (H.hl k x hx hx1 (Q.lg.trans_lt hγ))) _
  b_cof := fun x hx hx1 hγ μ hμ => by
    obtain ⟨b, hb, hμb⟩ := hjw_Nx_cof (omega0_pos.trans (hnv_ωl Λ hx hx1 (ν := 0))).ne' (Q.Fr_P hx hx1 hγ) hμ
    rw [add_zero, H.l_eq x (Q.lg.trans_lt hγ)] at hb
    obtain ⟨k, hk⟩ := hn_cof1 (fun _ h => hn_sq_succ hx h) hx.pos H.mono H.cof hb
    refine ⟨k, ?_⟩
    rw [H.D_b Q U hU k hx hx1 hγ]
    exact hμb.trans (hdN_lt_Nx (by rw [add_zero]; exact hk))
  b_fix := fun x hx hx1 _ => hdNx_fix (one_lt_omega0.trans (hnv_ωl Λ hx hx1)) _
  b_gt := fun x hx hx1 hγ => (Q.Fr_gtx hx hx1 hγ).trans (hdNx_gt _ _)
  b_lt := fun x hx hx1 hγ => Q.S_lt1x hx hx1 hγ
  b_pi := fun _ _ hB hγ => Q.S_pi hB hγ
  Z_low := fun k x hx hx1 hγ => by
    rw [(H.D_spec Q U hU k).Z x hx hx1]
    show (if Q.γ < x then _ else Q.Zo x) ≤ Q.Zo x
    rw [if_neg hγ]
  Zo_fix := fun x => ha_fix1_of_fix2 (Q.Zo_fix x)
  Zo_G1 := Q.Zo_G1

/-- **THE STEP OF THE LIMIT LEVEL `Ω₁·M` AT `Q`**: the union of the chain of the steps of the packages `K_k`. -/
noncomputable def hnkStL : HgVD := (hnkCh H Q U hU).U

/-- **The union extends every member of the chain.** -/
theorem hnkStL_ext (k : ℕ) {c : Ordinal.{0}} (hc : c < (H.D Q U hU k).B) (x : Ordinal.{0}) :
    (hnkStL H Q U hU).R c x = (H.D Q U hU k).R c x ∧ (hnkStL H Q U hU).g c = (H.D Q U hU k).g c :=
  ⟨(hnkCh H Q U hU).U_R (k := k) hc x, (hnkCh H Q U hU).U_g (k := k) hc⟩

/-- **THE STEP OF THE LIMIT LEVEL HAS THE SPECIFICATION.** -/
theorem hnkStL_spec : HnVSpec Q U (hnkStL H Q U hU) := by
  set C := hnkCh H Q U hU with hC
  have hUB : U.B = Q.F := hg_B_of_start hU
  have hF0 : Q.F < (C.D 0).B := by
    show Q.F < (H.D Q U hU 0).B
    rw [(H.D_spec Q U hU 0).B]; exact hdNx_gt _ _
  have hU0 : ∀ c, c < U.B → c < (C.D 0).B := fun c hc => hc.trans (by rw [hUB]; exact hF0)
  refine ⟨rfl, rfl, fun _ _ _ _ => rfl, fun x _ _ => rfl, fun c x hc => ?_, fun c hc => ?_,
    fun c σ hFc hc hσ hσ1 hg => ?_, fun x hx hx1 hγ => ?_, fun x hx hx1 => ?_⟩
  · show C.U.R c x = U.R c x
    rw [C.U_R (k := 0) (hU0 c hc)]; exact (H.D_spec Q U hU 0).extR c x hc
  · show C.U.g c = U.g c
    rw [C.U_g (k := 0) (hU0 c hc)]; exact (H.D_spec Q U hU 0).extg c hc
  · obtain ⟨k, hk⟩ := C.B_cof c hc
    have hg' : (H.D Q U hU k).g c < σ := by
      have e : C.U.g c = (C.D k).g c := C.U_g (k := k) hk
      show (C.D k).g c < σ
      rw [← e]; exact hg
    have hlk' : c < hdNx ((H.K k).Λ.L + 0) Q.F := by
      have := (H.D_spec Q U hU k).B; exact this ▸ hk
    exact (H.D_spec Q U hU k).high c σ hFc hlk' hσ hσ1 hg'
  · show C.U.R Q.F x = Q.Fr x
    rw [C.U_R (k := 0) hF0]; exact (H.D_spec Q U hU 0).RF x hx hx1 hγ
  · show C.U.g Q.F < x ↔ Q.γ < x
    rw [C.U_g (k := 0) hF0]; exact (H.D_spec Q U hU 0).gF x hx hx1

end Ch

/-- **THE LIMIT PACKAGE** at the level datum `Λ` of a coherent sequence. -/
noncomputable def hnkPkL {Λ : HnLv} (H : HnkSeq Λ) : HnPk :=
  ⟨Λ, fun Q U hU => hnkStL H Q U hU, fun Q U hU => hnkStL_spec H Q U hU⟩

theorem hnkPkL_Λ {Λ : HnLv} (H : HnkSeq Λ) : (hnkPkL H).Λ = Λ := rfl

end Googology.Trans.PoR.InaccPsi.R2.Hn
