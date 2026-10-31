import Googology.Trans.PoR.InaccPsi.R2.WmLow

/-!
# WmPkL: THE LIMIT PACKAGE OF AN `ω`-SEQUENCE OF PACKAGES AT ANY LEVEL DATUM, WITH NO GATE MONOTONICITY

`Hn.HnkSeq` / `Hn.hnkPkL` build the package of a limit level from a coherent `ω`-sequence, but only for the band
levels `Ω₁·Ω₁ + Ω₁·M`, and they ask the gates of the sequence to be non-decreasing (`Kgm`) because the extension
statement `Hn.HnkExt` lowers by the package gate.  With `WmExt` (lowering by the pseudo-base gate) the gates of the
members need only be below the gate of the limit level datum.

* `WmSeq Λ` (**a coherent `ω`-sequence below ANY level datum `Λ`**: levels `L_k + Ω₁ ≤ L_{k+1}`, `L_k + Ω₁ ≤ L`,
  readings likewise above the gate of `Λ`, cofinal levels and readings, member gates `≤ Λ.g`, `WmExt K_k K_{k+1}`);
* `wmCh` (**the gated `ω`-chain of the steps of the members at a pseudo-base `Q`**), `wmStL`, `wmStL_spec`
  (**the union is a step of the level `L + 0` with its specification**), `wmPkL` (**THE LIMIT PACKAGE**);
* `wmPkL_ext` (**the limit package extends every member in the new sense**), `wmPkL_ext_below` (**and every package
  that some member extends**, through `Wm.wmExt_trans`).

No new axiom.  New definitions: `WmSeq`, `WmSeq.D`, `wmCh`, `wmStL`, `wmPkL`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wm

open Googology.Trans.PoR.InaccPsi.R2.Wh Googology.Trans.PoR.InaccPsi.R2.Ho
open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gf
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **A COHERENT `ω`-SEQUENCE OF PACKAGES BELOW A LEVEL DATUM `Λ`** (any level): levels and readings increase by
`Ω₁` / `x` along the sequence and below `Λ`, they are cofinal (with room for `+1`), the member gates are at most the
gate of `Λ`, and each member extends the previous one in the new sense. -/
structure WmSeq (Λ : HnLv) where
  K : ℕ → HnPk
  hL : ∀ k, (K k).Λ.L + Om1 ≤ Λ.L
  hl : ∀ k x, InE x → x < Om1 → Λ.g < x → (K k).Λ.l x + x ≤ Λ.l x
  hLs : ∀ k, (K k).Λ.L + Om1 ≤ (K (k + 1)).Λ.L
  hls : ∀ k x, InE x → x < Om1 → Λ.g < x → (K k).Λ.l x + x ≤ (K (k + 1)).Λ.l x
  cof : ∀ t, t < Λ.L → ∃ k, t + 1 < (K k).Λ.L
  lcof : ∀ x, InE x → x < Om1 → Λ.g < x → ∀ t, t < Λ.l x → ∃ k, t + 1 < (K k).Λ.l x
  Kg : ∀ k, (K k).Λ.g ≤ Λ.g
  ext : ∀ k, WmExt (K k) (K (k + 1))

namespace WmSeq

variable {Λ : HnLv} (H : WmSeq Λ)

section Q

variable (Q : HnVQ Λ 0) (U : HgVD) (hU : HgSStart (hnVPB Q) U)

theorem Kg' (k : ℕ) : (H.K k).Λ.g ≤ Q.γ := (H.Kg k).trans Q.lg

theorem hl' (k : ℕ) : ∀ x, InE x → x < Om1 → Q.γ < x → (H.K k).Λ.l x + x ≤ Λ.l x := fun x hx hx1 hγ =>
  H.hl k x hx hx1 (Q.lg.trans_lt hγ)

/-- The pseudo-base `Q` lowered to the member `k`. -/
noncomputable abbrev Qk (k : ℕ) : HnVQ (H.K k).Λ 0 := wmLowr Q (H.K k).Λ (H.Kg' Q k) (H.hL k) (H.hl' Q k)

/-- The member `k` of the chain at `Q`: the step of `K_k` at `Q` lowered. -/
noncomputable abbrev D (k : ℕ) : HgVD := (H.K k).St0 (H.Qk Q k) U hU

theorem D_spec (k : ℕ) : HnVSpec (H.Qk Q k) U (H.D Q U hU k) := (H.K k).h0 _ U hU

theorem D_ext (k : ℕ) {c : Ordinal.{0}} (hc : c < (H.D Q U hU k).B) (x : Ordinal.{0}) :
    (H.D Q U hU (k + 1)).R c x = (H.D Q U hU k).R c x ∧ (H.D Q U hU (k + 1)).g c = (H.D Q U hU k).g c :=
  H.ext k (H.Qk Q (k + 1)) (H.Kg' Q k) (H.hLs k)
    (fun x hx hx1 hγ => H.hls k x hx hx1 (Q.lg.trans_lt hγ)) U hU c x hc

theorem D_B (k : ℕ) : (H.D Q U hU k).B = hdNx ((H.K k).Λ.L + 0) Q.F := (H.D_spec Q U hU k).B

theorem D_b (k : ℕ) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : Q.γ < x) :
    (H.D Q U hU k).b x = hdNx ((H.K k).Λ.l x + 0) (Q.Fr x) := (H.D_spec Q U hU k).b x hx hx1 hγ

end Q

end WmSeq

section Ch

variable {Λ : HnLv} (H : WmSeq Λ) (Q : HnVQ Λ 0) (U : HgVD) (hU : HgSStart (hnVPB Q) U)

/-- **THE GATED `ω`-CHAIN OF THE STEPS OF THE MEMBERS AT `Q`**: union bound `hdNx (L + 0) F`, union base reading
`hdNx (ℓ(x) + 0) (F(x))`, gate `Q.γ`. -/
noncomputable def wmCh : HgdCh where
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
    exact hdNx_mono (add_le_add (le_self_add.trans (H.hLs k)) le_rfl) _
  B_lt := fun k => by rw [H.D_B]; exact Q.lw_S_lt _ (H.hL k)
  B_cof := fun c hc => by
    obtain ⟨b, hb, hcb⟩ := hjw_Nx_cof (hnv_L0 Λ 0) Q.F_P hc
    rw [add_zero] at hb
    obtain ⟨k, hk⟩ := H.cof b hb
    refine ⟨k, ?_⟩
    rw [H.D_B]
    exact hcb.trans (hdN_lt_Nx (by rw [add_zero]; exact hk))
  R_ext := fun k c x hc => (H.D_ext Q U hU k hc x).1
  g_ext := fun k c hc => (H.D_ext Q U hU k hc 0).2
  B_lt1 := Q.S_lt1
  B_fix := hdNx_fix ((hg_one_lt_Om1.trans_le Λ.OL).trans_le le_self_add) _
  B_mem := fun S _ _ ha hb => Q.S_mem S ha hb
  b_ge := fun k x hx hx1 hγ => by
    rw [H.D_b Q U hU k hx hx1 hγ, add_zero, add_zero]
    exact hdNx_mono (le_self_add.trans (H.hl' Q k x hx hx1 hγ)) _
  b_cof := fun x hx hx1 hγ μ hμ => by
    obtain ⟨b, hb, hμb⟩ := hjw_Nx_cof (omega0_pos.trans (hnv_ωl Λ hx hx1 (ν := 0))).ne' (Q.Fr_P hx hx1 hγ) hμ
    rw [add_zero] at hb
    obtain ⟨k, hk⟩ := H.lcof x hx hx1 (Q.lg.trans_lt hγ) b hb
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

/-- **THE STEP OF THE LIMIT LEVEL AT `Q`**: the union of the chain. -/
noncomputable def wmStL : HgVD := (wmCh H Q U hU).U

/-- **The union extends every member of the chain.** -/
theorem wmStL_ext (k : ℕ) {c : Ordinal.{0}} (hc : c < (H.D Q U hU k).B) (x : Ordinal.{0}) :
    (wmStL H Q U hU).R c x = (H.D Q U hU k).R c x ∧ (wmStL H Q U hU).g c = (H.D Q U hU k).g c :=
  ⟨(wmCh H Q U hU).U_R (k := k) hc x, (wmCh H Q U hU).U_g (k := k) hc⟩

/-- **THE STEP OF THE LIMIT LEVEL HAS THE SPECIFICATION.** -/
theorem wmStL_spec : HnVSpec Q U (wmStL H Q U hU) := by
  set C := wmCh H Q U hU with hC
  have hUB : U.B = Q.F := hg_B_of_start hU
  have hF0 : Q.F < (C.D 0).B := by
    show Q.F < (H.D Q U hU 0).B
    rw [H.D_B]; exact hdNx_gt _ _
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
    have hlk' : c < hdNx ((H.K k).Λ.L + 0) (H.Qk Q k).F := by
      have := H.D_B Q U hU k; exact this ▸ hk
    exact (H.D_spec Q U hU k).high c σ hFc hlk' hσ hσ1 hg'
  · show C.U.R Q.F x = Q.Fr x
    rw [C.U_R (k := 0) hF0]; exact (H.D_spec Q U hU 0).RF x hx hx1 hγ
  · show C.U.g Q.F < x ↔ Q.γ < x
    rw [C.U_g (k := 0) hF0]; exact (H.D_spec Q U hU 0).gF x hx hx1

end Ch

/-- **THE LIMIT PACKAGE** at the level datum `Λ` of a coherent sequence (no gate monotonicity). -/
noncomputable def wmPkL {Λ : HnLv} (H : WmSeq Λ) : HnPk :=
  ⟨Λ, fun Q U hU => wmStL H Q U hU, fun Q U hU => wmStL_spec H Q U hU⟩

theorem wmPkL_Λ {Λ : HnLv} (H : WmSeq Λ) : (wmPkL H).Λ = Λ := rfl

/-- **THE LIMIT PACKAGE EXTENDS EVERY MEMBER**, in the new sense. -/
theorem wmPkL_ext {Λ : HnLv} (H : WmSeq Λ) (k : ℕ) : WmExt (H.K k) (wmPkL H) := by
  intro Q hg hL hl U hU c x hc
  exact wmStL_ext H Q U hU k hc x

/-- **THE LIMIT PACKAGE EXTENDS EVERY PACKAGE `A` THAT SOME MEMBER EXTENDS** (with the level and reading
comparisons `A < K_k` above the larger gate). -/
theorem wmPkL_ext_below {Λ : HnLv} (H : WmSeq Λ) (k : ℕ) {A : HnPk} (hA : WmExt A (H.K k))
    (hLA : A.Λ.L + Om1 ≤ (H.K k).Λ.L)
    (hlA : ∀ x, InE x → x < Om1 → max A.Λ.g Λ.g < x → A.Λ.l x + x ≤ (H.K k).Λ.l x) :
    WmExt A (wmPkL H) :=
  wmExt_trans hA (wmPkL_ext H k) hLA (H.hL k) ((H.Kg k).trans (le_max_right _ _)) hlA
    (fun x hx hx1 h => H.hl k x hx hx1 ((le_max_right _ _).trans_lt h))

end Googology.Trans.PoR.InaccPsi.R2.Wm
