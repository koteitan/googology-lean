import Googology.Trans.PoR.InaccPsi.R2.HoOU

/-!
# HoSeq: THE STEP OF A LIMIT LEVEL FROM A COHERENT `ω`-SEQUENCE OF PACKAGES, FOR ANY SHAPE OF LEVELS

PORT of `Hn.HnPkL` to an abstract sequence of levels: in `Hn.HnkSeq` the levels are `Ω₁·Ω₁ + Ω₁·M_k` read
`x·x + x·M_k` below a limit level `Ω₁·Ω₁ + Ω₁·M`; here the sequence only asks that the levels of the packages `K_k`
increase by at least `Ω₁` (resp. `x`), lie `Ω₁` (resp. `x`) below the limit level, and are cofinal in it (`cofL`,
`cofl`).  So the same construction serves the limit band levels `Ω₁²·v + Ω₁·λ` and the limit prefixes `Ω₁²·λ`.

* `HoSeq`, `HoSeq.D` (the member `k` at a pseudo-base), `hoCh` (the gated `ω`-chain), `hoStL`, `hoStL_spec`
  (**the union has the specification of the limit level**), `hoPkL` (**THE LIMIT PACKAGE**).

No new axiom.  New definitions: `HoSeq`, `HoSeq.D`, `hoCh`, `hoStL`, `hoPkL`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ho

open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **A coherent sequence of packages below a limit level datum `Λ`**: the levels of `K_k` increase by `Ω₁`
(resp. `x` above the gates), lie `Ω₁` (resp. `x`) below `Λ`, and are cofinal in `Λ`; each step extends the previous
one. -/
structure HoSeq (Λ : HnLv) where
  K : ℕ → HnPk
  Kg : ∀ k, (K k).Λ.g ≤ Λ.g
  Kgm : ∀ k, (K k).Λ.g ≤ (K (k + 1)).Λ.g
  hL : ∀ k, (K k).Λ.L + Om1 ≤ Λ.L
  hl : ∀ k x, InE x → x < Om1 → Λ.g < x → (K k).Λ.l x + x ≤ Λ.l x
  hLs : ∀ k, (K k).Λ.L + Om1 ≤ (K (k + 1)).Λ.L
  hls : ∀ k x, InE x → x < Om1 → (K (k + 1)).Λ.g < x → (K k).Λ.l x + x ≤ (K (k + 1)).Λ.l x
  cofL : ∀ b, b < Λ.L → ∃ k, b + 1 < (K k).Λ.L
  cofl : ∀ x, InE x → x < Om1 → Λ.g < x → ∀ b, b < Λ.l x → ∃ k, b + 1 < (K k).Λ.l x
  ext : ∀ k, HnkExt (K k) (K (k + 1))

namespace HoSeq

variable {Λ : HnLv} (H : HoSeq Λ)

section Q

variable (Q : HnVQ Λ 0) (U : HgVD) (hU : HgSStart (hnVPB Q) U)

/-- The member `k` of the chain at `Q`: the step of the package `K_k` at `Q`. -/
noncomputable abbrev D (k : ℕ) : HgVD := (H.K k).St0 (Q.lowr (H.K k).Λ (H.Kg k) (H.hL k) (H.hl k)) U hU

theorem D_spec (k : ℕ) : HnVSpec (Q.lowr (H.K k).Λ (H.Kg k) (H.hL k) (H.hl k)) U (H.D Q U hU k) := (H.K k).h0 _ U hU

theorem D_ext (k : ℕ) {c : Ordinal.{0}} (hc : c < (H.D Q U hU k).B) (x : Ordinal.{0}) :
    (H.D Q U hU (k + 1)).R c x = (H.D Q U hU k).R c x ∧ (H.D Q U hU (k + 1)).g c = (H.D Q U hU k).g c :=
  H.ext k (H.Kgm k) (H.hLs k) (H.hls k) (Q.lowr (H.K (k + 1)).Λ (H.Kg (k + 1)) (H.hL (k + 1)) (H.hl (k + 1))) U hU
    c x hc

theorem D_B (k : ℕ) : (H.D Q U hU k).B = hdNx ((H.K k).Λ.L + 0) Q.F := (H.D_spec Q U hU k).B

theorem D_b (k : ℕ) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : Q.γ < x) :
    (H.D Q U hU k).b x = hdNx ((H.K k).Λ.l x + 0) (Q.Fr x) := (H.D_spec Q U hU k).b x hx hx1 hγ

end Q

end HoSeq

section Ch

variable {Λ : HnLv} (H : HoSeq Λ) (Q : HnVQ Λ 0) (U : HgVD) (hU : HgSStart (hnVPB Q) U)

/-- **THE GATED `ω`-CHAIN OF THE STEPS OF THE PACKAGES `K_k` AT `Q`**: union bound `hdNx (L + 0) F`, union base
reading `hdNx (ℓ(x) + 0) (F(x))`. -/
noncomputable def hoCh : HgdCh where
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
  B_lt := fun k => by rw [(H.D_spec Q U hU k).B]; exact Q.lw_S_lt _ (H.hL k)
  B_cof := fun c hc => by
    obtain ⟨b, hb, hcb⟩ := hjw_Nx_cof (hnv_L0 Λ 0) Q.F_P hc
    rw [add_zero] at hb
    obtain ⟨k, hk⟩ := H.cofL b hb
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
    rw [add_zero] at hb
    obtain ⟨k, hk⟩ := H.cofl x hx hx1 (Q.lg.trans_lt hγ) b hb
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

/-- **THE STEP OF THE LIMIT LEVEL AT `Q`**: the union of the chain of the steps of the packages `K_k`. -/
noncomputable def hoStL : HgVD := (hoCh H Q U hU).U

/-- **The union extends every member of the chain.** -/
theorem hoStL_ext (k : ℕ) {c : Ordinal.{0}} (hc : c < (H.D Q U hU k).B) (x : Ordinal.{0}) :
    (hoStL H Q U hU).R c x = (H.D Q U hU k).R c x ∧ (hoStL H Q U hU).g c = (H.D Q U hU k).g c :=
  ⟨(hoCh H Q U hU).U_R (k := k) hc x, (hoCh H Q U hU).U_g (k := k) hc⟩

/-- **THE STEP OF THE LIMIT LEVEL HAS THE SPECIFICATION.** -/
theorem hoStL_spec : HnVSpec Q U (hoStL H Q U hU) := by
  set C := hoCh H Q U hU with hC
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
noncomputable def hoPkL {Λ : HnLv} (H : HoSeq Λ) : HnPk :=
  ⟨Λ, fun Q U hU => hoStL H Q U hU, fun Q U hU => hoStL_spec H Q U hU⟩

theorem hoPkL_Λ {Λ : HnLv} (H : HoSeq Λ) : (hoPkL H).Λ = Λ := rfl

/-- **The limit package extends every member of the sequence** (the statement `Hn.HnkExt`). -/
theorem hoPkL_ext {Λ : HnLv} (H : HoSeq Λ) (k : ℕ) : HnkExt (H.K k) (hoPkL H) := by
  intro hg hL hl Q U hU c x hc
  exact hoStL_ext H Q U hU k hc x

end Googology.Trans.PoR.InaccPsi.R2.Ho
