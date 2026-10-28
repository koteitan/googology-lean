import Googology.Trans.PoR.InaccPsi.R2.HjWG

/-!
# HjLim: THE LEVEL `Ω₁·ω` READ AS `x·ω`; THE STEPS AND THE SYSTEMS PAST IT; THE FRONTIER `ι(Γ(φ(Ω₁·ω·2, G+1)))`

The level datum `Ω₁·ω` (read `x·ω`, Lemma EXACT `π(ρ·ω) = σ·ω` from `Exact.pi_mul`) is a limit of the packages
`Hj.hjPkN n` (levels `Ω₁·(n+1)`).  A pseudo-base `Q` of level `Ω₁·ω` is one of every level `Ω₁·(n+1)`
(`HjVQ.lowr`, the same point); the steps of the packages at `Q` form a gated `ω`-chain (each extends the previous one:
the step of the package `n+1` is the union over the levels `Ω₁·(n+1) + κ` started at the step of the package `n`), and
its union is a step of the level `Ω₁·ω` with the specification (`hjStW`, `hjStW_spec`): the package `hjPkW`.
Over `G`, the systems `Hj.hjGU n` form a gated `ω`-chain whose union `hjGW0` has the bound `φ(Ω₁·ω, G+1)` and the
shape of a start at `hjPkW`; the recursion `Hj.hjGCg` from it gives the systems `hjGUW n` with the bounds
`φ(Ω₁·ω + Ω₁·(n+1), G+1)`, base gate `0`.  All are located; ENUM-REACH and CapV hold at every range restart below
`ι(Γ(φ(Ω₁·ω·2, G+1)))`, UNCONDITIONALLY.

* `hj_lt_mulw`, `hjLw`, `HjVQ.lowr`, `hjWCh`, `hjStW` (**THE STEP OF THE LEVEL `Ω₁·ω`**), `hjStW_spec`, `hjPkW`;
* `hjGWCh`, `hjGW0` (**THE SYSTEM AT `φ(Ω₁·ω, G+1)`**), `hjGW0_shape`, `hjGUW`, `hjGUW_B`, `hjPkW_L`;
* `hjGW0_loc`, `hjGUW_loc`, `hjGUW_blk`, `hjGE2`, `hjGE2_cofB`, `hjGE2_cof`, `hjGE2_enum`, `hjGE2_capV`, `hjGE2_road`,
  `hjGE2_lt1`, `hjGE2_lt_Om2`, `hjGE2_P`, `hjGE2_fr_order`.

No new axiom.  New definitions: `hjLw`, `HjVQ.lowr`, `hjWCh`, `hjStW`, `hjPkW`, `hjGWCh`, `hjGW0`, `hjGUW`, `hjGE2`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hj

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

/-- **`b < a·ω` lies below some `a·(n+1)`.** -/
theorem hj_lt_mulw {a b : Ordinal.{0}} (ha : 0 < a) (hb : b < a * ω) :
    ∃ n : ℕ, b < a * ((n + 1 : ℕ) : Ordinal.{0}) := by
  have hdiv : b / a < ω := (lt_mul_iff_div_lt ha.ne').1 hb
  obtain ⟨n, hn⟩ := lt_omega0.1 hdiv
  refine ⟨n, ?_⟩
  have := lt_mul_div_add b ha.ne'
  rw [hn] at this
  rwa [Nat.cast_succ, mul_add_one]

theorem hj_mul_succ_le {a : Ordinal.{0}} (n : ℕ) : a * ((n + 1 : ℕ) : Ordinal.{0}) + a ≤ a * ω := by
  rw [← mul_add_one]
  exact mul_le_mul_left' (Order.add_one_le_of_lt (natCast_lt_omega0 _)) _

/-! ## The level datum `Ω₁·ω` -/

theorem hjLw_eq : (Om1 : Ordinal.{0}) * ω = veblen 0 (Om 1 + 1) := by
  rw [veblen_zero_apply, opow_add, opow_one, show ω ^ Om (1 : Ordinal.{0}) = Om 1 from hj_Om_E, Br.Om1_eq]

/-- **The level datum `Ω₁·ω`, read as `x·ω`.** -/
noncomputable def hjLw : HjLv where
  L := Om1 * ω
  l := fun x => x * ω
  q := ω
  OL := le_mul_of_one_le_right' one_lt_omega0.le
  L_G := hjG_Ow_lt 0
  L_eq := by rw [Br.Om1_eq]
  L_mem := fun _ _ _ => by
    rw [hjLw_eq]
    exact CSet.phi_mem (CSet.zero_mem _ _) (CSet.succ_mem (CSet.Om_mem (CSet.one_mem _ _)))
  L_code := fun _ hZ _ => by
    rw [hjLw_eq]
    exact GxCl.phi (GxCl.small hZ.1) (GxCl.add GxCl.om (GxCl.small (one_lt_omega0.trans
      (omega0_lt_inE (Low.opow_eq_self_of_SC hZ)))))
  l_ge := fun _ => le_mul_of_one_le_right' one_lt_omega0.le
  l_lt := fun _ hx hx1 => InE.mul_lt (lgG_facts hx hx1).2.2.2.1 (lgG_facts hx hx1).2.1
    (omega0_lt_inE (lgG_facts hx hx1).2.2.2.1)
  l_pi := fun _ _ hB => pi_mul hB ω (omega0_lt_inE hB.1)

/-! ## A pseudo-base of a higher level at a lower level datum -/

namespace HjVQ

variable {Λ' : HjLv} (Q : HjVQ Λ' 0) (Λ : HjLv) (hL : Λ.L + Om1 ≤ Λ'.L)
  (hl : ∀ x, InE x → x < Om1 → Λ.l x + x ≤ Λ'.l x)

include hL in
theorem lw_le : Λ.L + 0 ≤ Λ'.L + 0 := by rw [add_zero, add_zero]; exact le_self_add.trans hL

include hL in
theorem lw_lt : Λ.L + 0 < Λ'.L + 0 := by
  rw [add_zero, add_zero]; exact ((lt_add_iff_pos_right _).2 gv_Om1_pos).trans_le hL

include hL in
theorem lw_fix : veblen (Λ.L + 0) Q.F = Q.F := by
  obtain ⟨a, ha⟩ := Q.F_P; rw [← ha]; exact veblen_veblen_of_lt (lw_lt Λ hL) a

include hL in
theorem lw_S_lt : hdNx (Λ.L + 0) Q.F < hdNx (Λ'.L + 0) Q.F := by
  refine (hdNx_lt_N (hcN_gt _ _)).trans (hdN_lt_Nx ?_)
  rw [add_zero, add_zero]
  exact ((add_lt_add_iff_left _).2 hg_one_lt_Om1).trans_le hL

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hl hx hx1

theorem lw_lle : Λ.l x + 0 ≤ Λ'.l x + 0 := by rw [add_zero, add_zero]; exact le_self_add.trans (hl x hx hx1)

theorem lw_llt : Λ.l x + 0 < Λ'.l x + 0 := by
  rw [add_zero, add_zero]; exact ((lt_add_iff_pos_right _).2 hx.pos).trans_le (hl x hx hx1)

theorem lw_rfix (hγ : Q.γ < x) : veblen (Λ.l x + 0) (Q.Fr x) = Q.Fr x := by
  obtain ⟨a, ha⟩ := Q.Fr_P hx hx1 hγ; rw [← ha]; exact veblen_veblen_of_lt (lw_llt Λ hl hx hx1) a

end Base

/-- **A PSEUDO-BASE OF LEVEL `L' + 0` IS ONE OF A LOWER LEVEL `L + 0`** (`L + Ω₁ ≤ L'`, `ℓ(x) + x ≤ ℓ'(x)`; the same
point, reading and outer low field). -/
noncomputable def lowr : HjVQ Λ 0 where
  F := Q.F
  Fr := Q.Fr
  γ := Q.γ
  Zo := Q.Zo
  lv := gv_Om1_pos
  γ_ge := zero_le
  γ_lt := Q.γ_lt
  F_P := hd_LuP_mono (lw_le Λ hL) Q.F_P
  G_lt := Q.G_lt
  S_lt1 := (Q.lw_S_lt Λ hL).trans Q.S_lt1
  F_mem := Q.F_mem
  S_mem := fun S _ _ ha hb => by
    rw [hdNx_fixP (Q.lw_fix Λ hL)]
    exact CSet.phi_mem (hjv_L_mem Λ S (zero_le.trans_lt hb)) (CSet.succ_mem (Q.F_mem S ha hb))
  F_code := fun Z hZ hZ1 y hy hQy hyZ => Q.F_code Z hZ hZ1 y hy hQy (hyZ.trans (Q.lw_S_lt Λ hL))
  F_cl := fun Z hZ hZ1 y hy hQy hyZ => Q.F_cl Z hZ hZ1 y hy hQy (hyZ.trans (Q.lw_S_lt Λ hL))
  S_cl := fun Z hZ hZ1 h => Q.F_cl Z hZ hZ1 _ h (hdNx_gt _ _).le (Q.lw_S_lt Λ hL)
  Fr_gt := fun hx hx1 hγ => (lw_lle Λ hl hx hx1).trans_lt (Q.Fr_gt hx hx1 hγ)
  Fr_P := fun hx hx1 hγ => hd_LuP_mono (lw_lle Λ hl hx hx1) (Q.Fr_P hx hx1 hγ)
  S_Zo := fun hx hx1 hγ => (hdNx_mono (lw_lle Λ hl hx hx1) _).trans_lt (Q.S_Zo hx hx1 hγ)
  Zo_fix := Q.Zo_fix
  Zo_G1 := Q.Zo_G1
  Fr_pi := Q.Fr_pi
  S_pi := fun {σ ρ} hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hγρ : Q.γ < ρ := hγ.trans hB.2.2.1
    obtain ⟨f1, f2⟩ := Q.Fr_pi hB hγ
    have h := hjv_glA_pi Λ hB hB.1.pos f1 (Q.Fr_lt1 hB.2.1 hρ1 hγρ)
    rw [f2, hjv_glA_fixP Λ hB.2.1 hρ1 (hB.1.pos.trans hB.2.2.1) (Q.lw_rfix Λ hl hB.2.1 hρ1 hγρ)
      ((lw_lle Λ hl hB.2.1 hρ1).trans_lt (Q.Fr_gt hB.2.1 hρ1 hγρ)) (Q.Fr_lt1 hB.2.1 hρ1 hγρ),
      hjv_glA_fixP Λ hB.1 hσ1 hB.1.pos (Q.lw_rfix Λ hl hB.1 hσ1 hγ)
      ((lw_lle Λ hl hB.1 hσ1).trans_lt (Q.Fr_gt hB.1 hσ1 hγ)) (Q.Fr_lt1 hB.1 hσ1 hγ)] at h
    exact h

theorem lowr_PB : hjVPB (Q.lowr Λ hL hl) = hjVPB Q := rfl

end HjVQ

/-! ## The step of the level `Ω₁·ω` -/

theorem hjPkN_hL (n : ℕ) : (hjPkN n).Λ.L + Om1 ≤ hjLw.L := by
  rw [hjPkN_L]; exact hj_mul_succ_le n

theorem hjPkN_hl (n : ℕ) : ∀ x, InE x → x < Om1 → (hjPkN n).Λ.l x + x ≤ hjLw.l x := fun x _ _ => by
  rw [hjPkN_l]; exact hj_mul_succ_le n

section StW

variable (Q : HjVQ hjLw 0) (U : HgVD) (hU : HgSStart (hjVPB Q) U)

/-- The member `n` of the chain at `Q`: the step of the package `n` at `Q`. -/
noncomputable abbrev hjWD (n : ℕ) : HgVD := (hjPkN n).St0 (Q.lowr (hjPkN n).Λ (hjPkN_hL n) (hjPkN_hl n)) U hU

theorem hjWD_spec (n : ℕ) : HjVSpec (Q.lowr (hjPkN n).Λ (hjPkN_hL n) (hjPkN_hl n)) U (hjWD Q U hU n) :=
  (hjPkN n).h0 _ U hU

theorem hjWD_ext (n : ℕ) {c : Ordinal.{0}} (hc : c < (hjWD Q U hU n).B) (x : Ordinal.{0}) :
    (hjWD Q U hU (n + 1)).R c x = (hjWD Q U hU n).R c x ∧ (hjWD Q U hU (n + 1)).g c = (hjWD Q U hU n).g c :=
  ⟨hjwU_R0 (Q.lowr (hjPkN (n + 1)).Λ (hjPkN_hL (n + 1)) (hjPkN_hl (n + 1))).toW (hjPkN n).St0 (hjPkN n).h0 _
      (hjw_shape_dn _ ((hjPkN n).h0 _ U hU)) hc x,
    hjwU_g0 (Q.lowr (hjPkN (n + 1)).Λ (hjPkN_hL (n + 1)) (hjPkN_hl (n + 1))).toW (hjPkN n).St0 (hjPkN n).h0 _
      (hjw_shape_dn _ ((hjPkN n).h0 _ U hU)) hc⟩

theorem hjWD_B (n : ℕ) : (hjWD Q U hU n).B = hdNx (Om1 * ((n + 1 : ℕ) : Ordinal.{0}) + 0) Q.F := by
  rw [(hjWD_spec Q U hU n).B, hjPkN_L]; rfl

theorem hjWD_b (n : ℕ) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : Q.γ < x) :
    (hjWD Q U hU n).b x = hdNx (x * ((n + 1 : ℕ) : Ordinal.{0}) + 0) (Q.Fr x) := by
  rw [(hjWD_spec Q U hU n).b x hx hx1 hγ, hjPkN_l]; rfl

/-- **THE GATED `ω`-CHAIN OF THE STEPS OF THE PACKAGES AT `Q`**: union bound `hdNx (Ω₁·ω) F`, union base reading
`hdNx (x·ω) (F(x))`. -/
noncomputable def hjWCh : HgdCh where
  D := hjWD Q U hU
  B := hdNx (hjLw.L + 0) Q.F
  b := fun x => hdNx (hjLw.l x + 0) (Q.Fr x)
  γ := Q.γ
  Zo := Q.Zo
  γ_lt := Q.γ_lt
  γ0 := fun k => (hjWD_spec Q U hU k).γ
  γ_cl := fun Z hZ hZ1 h => Q.S_cl Z hZ hZ1 h
  B_mono := fun k => by
    rw [(hjWD_spec Q U hU k).B, (hjWD_spec Q U hU (k + 1)).B]
    show hdNx ((hjPkN k).Λ.L + 0) Q.F ≤ hdNx ((hjPkN k).Λ.L + Om1 + 0) Q.F
    rw [add_zero, add_zero]; exact hdNx_mono le_self_add _
  B_lt := fun k => by rw [(hjWD_spec Q U hU k).B]; exact Q.lw_S_lt _ (hjPkN_hL k)
  B_cof := fun c hc => by
    obtain ⟨b, hb, hcb⟩ := hjw_Nx_cof (hjv_L0 hjLw 0) Q.F_P hc
    rw [add_zero] at hb
    obtain ⟨n, hn⟩ := hj_lt_mulw gv_Om1_pos hb
    refine ⟨n + 1, ?_⟩
    rw [hjWD_B]
    refine hcb.trans_le ((hcN_mono hn.le _).trans (hdN_lt_Nx ?_).le)
    rw [add_zero, Nat.cast_succ (n + 1), mul_add_one]
    exact (add_lt_add_iff_left _).2 hg_one_lt_Om1
  R_ext := fun k c x hc => (hjWD_ext Q U hU k hc x).1
  g_ext := fun k c hc => (hjWD_ext Q U hU k hc 0).2
  B_lt1 := Q.S_lt1
  B_fix := hdNx_fix ((hg_one_lt_Om1.trans_le hjLw.OL).trans_le le_self_add) _
  B_mem := fun S _ _ ha hb => Q.S_mem S ha hb
  b_ge := fun k x hx hx1 hγ => by
    rw [(hjWD_spec Q U hU k).b x hx hx1 hγ]
    show hdNx ((hjPkN k).Λ.l x + 0) (Q.Fr x) ≤ hdNx (hjLw.l x + 0) (Q.Fr x)
    rw [add_zero, add_zero]; exact hdNx_mono (le_self_add.trans (hjPkN_hl k x hx hx1)) _
  b_cof := fun x hx hx1 hγ μ hμ => by
    obtain ⟨b, hb, hμb⟩ := hjw_Nx_cof (omega0_pos.trans (hjv_ωl hjLw hx hx1 (ν := 0))).ne' (Q.Fr_P hx hx1 hγ) hμ
    rw [add_zero] at hb
    obtain ⟨n, hn⟩ := hj_lt_mulw hx.pos hb
    refine ⟨n + 1, ?_⟩
    rw [hjWD_b Q U hU (n + 1) hx hx1 hγ]
    refine hμb.trans_le ((hcN_mono hn.le _).trans (hdN_lt_Nx ?_).le)
    rw [add_zero, Nat.cast_succ (n + 1), mul_add_one]
    exact (add_lt_add_iff_left _).2 (one_lt_omega0.trans (omega0_lt_inE hx))
  b_fix := fun x hx hx1 _ => hdNx_fix (one_lt_omega0.trans (hjv_ωl hjLw hx hx1)) _
  b_gt := fun x hx hx1 hγ => (Q.Fr_gtx hx hx1 hγ).trans (hdNx_gt _ _)
  b_lt := fun x hx hx1 hγ => Q.S_lt1x hx hx1 hγ
  b_pi := fun _ _ hB hγ => Q.S_pi hB hγ
  Z_low := fun k x hx hx1 hγ => by
    rw [(hjWD_spec Q U hU k).Z x hx hx1]
    show (if Q.γ < x then _ else Q.Zo x) ≤ Q.Zo x
    rw [if_neg hγ]
  Zo_fix := fun x => ha_fix1_of_fix2 (Q.Zo_fix x)
  Zo_G1 := Q.Zo_G1

/-- **THE STEP OF THE LEVEL `Ω₁·ω` AT `Q`**: the union of the chain of the steps of the packages. -/
noncomputable def hjStW : HgVD := (hjWCh Q U hU).U

/-- **THE STEP OF THE LEVEL `Ω₁·ω` HAS THE SPECIFICATION.** -/
theorem hjStW_spec : HjVSpec Q U (hjStW Q U hU) := by
  set C := hjWCh Q U hU with hC
  have hUB : U.B = Q.F := hg_B_of_start hU
  have hF0 : Q.F < (C.D 0).B := by
    show Q.F < (hjWD Q U hU 0).B
    rw [(hjWD_spec Q U hU 0).B]; exact hdNx_gt _ _
  have hU0 : ∀ c, c < U.B → c < (C.D 0).B := fun c hc => hc.trans (by rw [hUB]; exact hF0)
  refine ⟨rfl, rfl, fun _ _ _ _ => rfl, fun x _ _ => rfl, fun c x hc => ?_, fun c hc => ?_,
    fun c σ hFc hc hσ hσ1 hg => ?_, fun x hx hx1 hγ => ?_, fun x hx hx1 => ?_⟩
  · show C.U.R c x = U.R c x
    rw [C.U_R (k := 0) (hU0 c hc)]; exact (hjWD_spec Q U hU 0).extR c x hc
  · show C.U.g c = U.g c
    rw [C.U_g (k := 0) (hU0 c hc)]; exact (hjWD_spec Q U hU 0).extg c hc
  · obtain ⟨k, hk⟩ := C.B_cof c hc
    have hg' : (hjWD Q U hU k).g c < σ := by
      have e : C.U.g c = (C.D k).g c := C.U_g (k := k) hk
      show (C.D k).g c < σ
      rw [← e]; exact hg
    have hk' : c < hdNx ((hjPkN k).Λ.L + 0) Q.F := by
      have := (hjWD_spec Q U hU k).B; exact this ▸ hk
    exact (hjWD_spec Q U hU k).high c σ hFc hk' hσ hσ1 hg'
  · show C.U.R Q.F x = Q.Fr x
    rw [C.U_R (k := 0) hF0]; exact (hjWD_spec Q U hU 0).RF x hx hx1 hγ
  · show C.U.g Q.F < x ↔ Q.γ < x
    rw [C.U_g (k := 0) hF0]; exact (hjWD_spec Q U hU 0).gF x hx hx1

end StW

/-- **THE PACKAGE AT THE LEVEL `Ω₁·ω`.** -/
noncomputable def hjPkW : HjPk := ⟨hjLw, hjStW, hjStW_spec⟩

/-- **The level of the `n`-th successor of the package at `Ω₁·ω` is `Ω₁·ω + Ω₁·n`.** -/
theorem hjPkW_L : ∀ n : ℕ, (hjPkI hjPkW n).Λ.L = Om1 * ω + Om1 * (n : Ordinal.{0})
  | 0 => by show Om1 * ω = _; rw [Nat.cast_zero, mul_zero, add_zero]
  | n + 1 => by
    show (hjPkI hjPkW n).Λ.L + Om1 = _
    rw [hjPkW_L n, Nat.cast_succ, mul_add_one, add_assoc]

/-! ## Over `G`: the system at `φ(Ω₁·ω, G+1)` -/

theorem hjGU_B_lt (n : ℕ) : (hjGU n).B < hjGE := by
  rw [hjGU_B]; exact hd_veb_left_lt (mul_lt_mul_of_pos_left (natCast_lt_omega0 _) gv_Om1_pos) _

theorem hjGU_ext (n : ℕ) {c : Ordinal.{0}} (hc : c < (hjGU n).B) (x : Ordinal.{0}) :
    (hjGU (n + 1)).R c x = (hjGU n).R c x ∧ (hjGU (n + 1)).g c = (hjGU n).g c :=
  ⟨hjwU_R0 (hjGW (hjPkN (n + 1)).Λ) (hjPkN (n + 1)).St0 (hjPkN (n + 1)).h0 _ (hjGC (n + 1)).2 hc x,
    hjwU_g0 (hjGW (hjPkN (n + 1)).Λ) (hjPkN (n + 1)).St0 (hjPkN (n + 1)).h0 _ (hjGC (n + 1)).2 hc⟩

theorem hjGU_b' (n : ℕ) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    (hjGU n).b x = hdNx (x * ((n + 2 : ℕ) : Ordinal.{0})) (lgG x) := by
  rw [hjGU_b, hjPkN_l, Nat.cast_succ (n + 1), mul_add_one]

theorem hjG_xw_fix {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : veblen (x * ω) (lgG x) = lgG x :=
  hjG_fix hx hx1 ((one_lt_omega0.trans (omega0_lt_inE hx)).le.trans (hjLw.l_ge x)) (hjLw.l_lt x hx hx1)

/-- **THE GATED `ω`-CHAIN OF THE SYSTEMS `hjGU n` OVER `G`**: union bound `φ(Ω₁·ω, G+1)`, union base reading
`φ(x·ω, Γ_{x+1}+1)`. -/
noncomputable def hjGWCh : HgfCh where
  D := hjGU
  B := hjGE
  b := fun x => veblen (x * ω) (lgG x + 1)
  γ := 0
  Zo := (hjGW hjLw).hjwZo
  γ_lt := gv_Om1_pos
  γ0 := fun _ => le_rfl
  γ_cl := fun _ hZ _ _ => hZ.1
  B_mono := fun k => by
    rw [hjGU_B, hjGU_B]
    exact (hd_veb_left_lt (mul_lt_mul_of_pos_left (Nat.cast_lt.2 (by omega)) gv_Om1_pos) _).le
  B_lt := hjGU_B_lt
  B_cof := fun c hc => hjGE_cofB hc
  R_ext := fun k c x hc => (hjGU_ext k hc x).1
  g_ext := fun k c hc => (hjGU_ext k hc 0).2
  B_lt1 := hjGE_lt1
  B_fix := veblen_veblen_of_lt (hg_one_lt_Om1.trans_le hjLw.OL) _
  B_mem := fun S a b ha _ => CSet.phi_mem (hjLw.L_mem S a b) (CSet.succ_mem (gmS_G0_mem S ha))
  b_ge := fun k x hx hx1 _ => by
    rw [hjGU_b' k hx hx1, ← hdNx_fixP (hjG_xw_fix hx hx1)]
    exact hdNx_mono (mul_le_mul_left' (natCast_lt_omega0 _).le _) _
  b_cof := fun x hx hx1 _ ν hν => by
    obtain ⟨b, hb, hνb⟩ := hgVeb_cof (mul_pos hx.pos omega0_pos).ne' (hjG_xw_fix hx hx1) hν
    obtain ⟨n, hn⟩ := hj_lt_mulw hx.pos hb
    refine ⟨n, ?_⟩
    rw [hjGU_b' n hx hx1]
    refine hνb.trans_le ((hcN_mono hn.le _).trans (hdN_lt_Nx ?_).le)
    rw [Nat.cast_succ (n + 1), mul_add_one]
    exact (add_lt_add_iff_left _).2 (one_lt_omega0.trans (omega0_lt_inE hx))
  b_fix := fun x hx _ _ => veblen_veblen_of_lt ((one_lt_omega0.trans (omega0_lt_inE hx)).trans_le
    (hjLw.l_ge x)) _
  b_gt := fun x hx hx1 _ => (lgG_facts hx hx1).2.1.trans ((lt_add_one _).trans_le (right_le_veblen _ _))
  b_lt := fun x hx hx1 _ => by
    rw [← hdNx_fixP (hjG_xw_fix hx hx1)]
    exact hjG_lt1 hx hx1 ((one_lt_omega0.trans (omega0_lt_inE hx)).le.trans (hjLw.l_ge x))
      (hjLw.l_lt x hx hx1)
  b_pi := fun σ ρ hB _ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    rw [← hdNx_fixP (hjG_xw_fix hB.2.1 hρ1), ← hdNx_fixP (hjG_xw_fix hB.1 hσ1)]
    exact hjG_S_pi hB (hjLw.l_pi σ ρ hB) ((one_lt_omega0.trans (omega0_lt_inE hB.2.1)).le.trans (hjLw.l_ge ρ))
      (hjLw.l_lt ρ hB.2.1 hρ1) ((one_lt_omega0.trans (omega0_lt_inE hB.1)).le.trans (hjLw.l_ge σ))
      (hjLw.l_lt σ hB.1 hσ1)
  Z_low := fun _ x hx _ h => absurd hx.pos h
  Zo_fix := fun x => hc_fix_down one_le_two ((hjGW hjLw).hjwZo_fix x)
  Zo_G1 := fun x hx hx1 => (hjGW hjLw).hjwZo_G1 x hx hx1

/-- **THE SYSTEM AT `φ(Ω₁·ω, G+1)`** (base gate `0`, base reading `φ(x·ω, Γ_{x+1}+1)`). -/
noncomputable def hjGW0 : HgVD := hjGWCh.U

theorem hjGW0_B : hjGW0.B = hjGE := rfl

/-- **`hjGW0` is a start over `G` at the package `hjPkW`.** -/
theorem hjGW0_shape : HjWShape (hjGW hjPkW.Λ) 0 hjGW0 := by
  refine ⟨by show veblen (Om1 * ω) (gcG 0 + 1) = veblen (Om1 * ω + 0) (gcG 0 + 1); rw [add_zero],
    fun x _ _ => ?_, fun x _ _ _ => ?_, fun x hx _ => ?_, fun _ σ _ _ hσ _ _ => hσ.pos⟩
  · show (0 : Ordinal.{0}) < x ↔ max 0 0 < x
    rw [max_self]
  · show veblen (x * ω) (lgG x + 1) = veblen (x * ω + 0) (lgG x + 1)
    rw [add_zero]
  · show (if (0 : Ordinal.{0}) < x then evZ (veblen (x * ω) (lgG x + 1)) else (hjGW hjLw).hjwZo x) =
      if max 0 0 < x then evZ (veblen (x * ω + 0) (lgG x + 1)) else (hjGW hjLw).hjwZo x
    rw [max_self, add_zero]

/-- **THE SYSTEM AT `φ(Ω₁·ω + Ω₁·(n+1), G+1)`**: the union of all levels `Ω₁·ω + Ω₁·n + κ` over `G`. -/
noncomputable def hjGUW (n : ℕ) : HgVD := (hjGCg hjPkW hjGW0 hjGW0_shape (n + 1)).1

theorem hjGUW_γ (n : ℕ) : (hjGUW n).γ = 0 := rfl

theorem hjGUW_B (n : ℕ) :
    (hjGUW n).B = veblen (Om1 * ω + Om1 * ((n + 1 : ℕ) : Ordinal.{0})) (gcG 0 + 1) := by
  show hdNx ((hjPkI hjPkW n).Λ.L + Om1) (gcG 0) = _
  rw [hdNx_fixP (hjG_FP _), hjPkW_L, Nat.cast_succ n, mul_add_one, add_assoc]

/-! ## The location -/

/-- **`φ(Ω₁·ω, G+1)` IS LOCATED**: `Λ⁺ = ι(Γ(φ(Ω₁·ω, G+1))·ω)`, `P(…) < L(0)` (UNCONDITIONAL). -/
theorem hjGW0_loc (S : InaccSeq.{0}) :
    ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG hjGE * ω) ∧
      upsilon (xtB1 X) = Pv S (gcG hjGE * ω) ∧ Pv S (gcG hjGE * ω) < Nc.ncL S 0 :=
  hgV_locD hjGW0 S (hg_K_pos S)

/-- **`φ(Ω₁·ω + Ω₁·(n+1), G+1)` IS LOCATED** for every `n < ω` (UNCONDITIONAL). -/
theorem hjGUW_loc (S : InaccSeq.{0}) (n : ℕ) :
    ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG (hjGUW n).B * ω) ∧
      upsilon (xtB1 X) = Pv S (gcG (hjGUW n).B * ω) ∧ Pv S (gcG (hjGUW n).B * ω) < Nc.ncL S 0 :=
  hgV_locD (hjGUW n) S (hg_K_pos S)

/-- **Theorem BLK^O below `P(Γ(φ(Ω₁·ω + Ω₁·(n+1), G+1))·ω)`, with the exact reaches** (UNCONDITIONAL). -/
theorem hjGUW_blk (S : InaccSeq.{0}) (n : ℕ) :
    let X := gsX (hjGUW n).step.toRS _ (hjGUW n).E_lt_B.le (hjGUW n).B_lt_NB S
      (hgV_locD_g (hjGUW n) S (hg_K_pos S))
    (∀ c' d, c' < d → d < upsilon (xtB1 X) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 X ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧ d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 X →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec X l)) ∧
    (∀ α < upsilon (xtB1 X), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  hgV_locD_blk (hjGUW n) S (hg_K_pos S)

/-- **`φ(Ω₁·ω·2, G+1) = φ(Ω₁·ω + Ω₁·ω, G+1)`.** -/
noncomputable def hjGE2 : Ordinal.{0} := veblen (Om1 * ω + Om1 * ω) (gcG 0 + 1)

theorem hjG_Ow2_lt (α : Ordinal.{0}) : (Om1 : Ordinal.{0}) * ω + Om1 * ω < gcG α :=
  (inE_indec (Low.opow_eq_self_of_SC (gcG_SC α))).add_lt (hjG_Ow_lt α) (hjG_Ow_lt α)

theorem hjG_Ow2_ne : (Om1 : Ordinal.{0}) * ω + Om1 * ω ≠ 0 := (hjG_Ow_ne.bot_lt.trans_le le_self_add).ne'

/-- **Every ordinal below `φ(Ω₁·ω·2, G+1)` lies below some `φ(Ω₁·ω + Ω₁·(n+1), G+1)`.** -/
theorem hjGE2_cofB {β : Ordinal.{0}} (hβ : β < hjGE2) : ∃ n : ℕ, β < (hjGUW n).B := by
  obtain ⟨b, hb, hβb⟩ := hgVeb_cof hjG_Ow2_ne (gn_veb_fix (gcG_SC 0) (hjG_Ow2_lt 0)) hβ
  obtain ⟨d, hd, hbd⟩ := (lt_add_iff hjG_Ow_ne).1 hb
  obtain ⟨n, hn⟩ := hj_lt_mulw gv_Om1_pos hd
  refine ⟨n, hβb.trans_le ?_⟩
  show hcN b (gcG 0) ≤ hdNx ((hjPkI hjPkW n).Λ.L + Om1) (gcG 0)
  rw [hjPkW_L]
  have hlt : b < Om1 * ω + Om1 * (n : Ordinal.{0}) + Om1 := by
    calc b ≤ Om1 * ω + d := hbd
    _ < Om1 * ω + Om1 * ((n + 1 : ℕ) : Ordinal.{0}) := (add_lt_add_iff_left _).2 hn
    _ = _ := by rw [Nat.cast_succ, mul_add_one, add_assoc]
  exact (hdN_lt_Nx ((isSuccLimit_add _ gl_Om1_lim).add_one_lt hlt)).le

theorem hjGE2_lim : IsSuccLimit hjGE2 := ev_isSuccLimit_of_inE (gg_veblen_eps hjG_Ow2_ne)

/-- **The located bounds `ι(Γ(φ(Ω₁·ω + Ω₁·(n+1), G+1))·ω)` are cofinal below `ι(Γ(φ(Ω₁·ω·2, G+1)))`.** -/
theorem hjGE2_cof (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : l < iota S (gcG hjGE2)) :
    ∃ n : ℕ, l < iota S (gcG (hjGUW n).B * ω) := by
  have hlim : IsSuccLimit (gcG hjGE2) := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (gcG_SC _))
  rw [iota_limit hlim] at hl
  haveI : Nonempty (Iio (gcG hjGE2)) := ⟨⟨0, hlim.bot_lt⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hl
  obtain ⟨β, hβ, heβ⟩ := gcG_lt_of_lt_limit hjGE2_lim e.2
  obtain ⟨n, hβn⟩ := hjGE2_cofB hβ
  refine ⟨n, he.trans_le (iota_mono _ _ ((heβ.trans (gcG_lt hβn)).trans_le ?_).le)⟩
  exact le_mul_of_one_le_right' one_lt_omega0.le

/-- **ENUM-REACH at every range restart below `ι(Γ(φ(Ω₁·ω·2, G+1)))`, fixed points included** (UNCONDITIONAL). -/
theorem hjGE2_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG hjGE2)) :
    CdUpper S l ∧ CdLower S l := by
  obtain ⟨n, h⟩ := hjGE2_cof S hl
  exact hgV_locD_enum (hjGUW n) S (hg_K_pos S) hr h

/-- **CapV at every range restart below `ι(Γ(φ(Ω₁·ω·2, G+1)))`** (UNCONDITIONAL). -/
theorem hjGE2_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG hjGE2)) :
    CdCapV S l := by
  obtain ⟨n, h⟩ := hjGE2_cof S hl
  exact hgV_locD_capV (hjGUW n) S (hg_K_pos S) hr h

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(φ(Ω₁·ω·2, G+1)))` (CapV also `υ_λ < L(ω)`), (CL), EQ,
TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem hjGE2_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG hjGE2) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG hjGE2) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG hjGE2) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gv_road_of S _ (fun _ hr h => hjGE2_enum S hr h) (fun _ hr h => hjGE2_capV S hr h) hU hL hV hC hEQ hrest hB2

theorem hjGE2_lt1 : hjGE2 < gcG 1 := by
  have hG1 := gcG_SC 1
  have hE := Low.opow_eq_self_of_SC hG1
  have hfix : veblen (Om1 * ω + Om1 * ω) (gcG 1) = gcG 1 := gn_veb_fix hG1 (hjG_Ow2_lt 1)
  have h2 := (isNormal_veblen (Om1 * ω + Om1 * ω)).strictMono
    ((ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt zero_lt_one))
  unfold hjGE2; rwa [hfix] at h2

/-- **`Γ(φ(Ω₁·ω·2, G+1)) < Ω₂`.** -/
theorem hjGE2_lt_Om2 : gcG hjGE2 < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG hjGE2 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) (hjGE2_lt1.trans hG1))
  exact h2.trans Tf.tfBG_lt_Om2

/-- **`P(Γ(φ(Ω₁·ω·2, G+1))) < L(0)`.** -/
theorem hjGE2_P (S : InaccSeq.{0}) : Pv S (gcG hjGE2) < Nc.ncL S 0 := ga_Pv_lt_L0 S hjGE2_lt_Om2.le

/-- **The order of the frontiers**: `φ(Ω₁·ω, G+1) < φ(Ω₁·ω·2, G+1)`, `ι(Γ(φ(Ω₁·ω, G+1))·ω) ≤ ι(Γ(φ(Ω₁·ω·2, G+1))) ≤
ι(Ω₂)` and `P(Γ(φ(Ω₁·ω·2, G+1))) ≤ P(Ω₂) < L(0)`. -/
theorem hjGE2_fr_order (S : InaccSeq.{0}) :
    hjGE < hjGE2 ∧ iota S (gcG hjGE * ω) ≤ iota S (gcG hjGE2) ∧ iota S (gcG hjGE2) ≤ iota S (Om (1 + 1)) ∧
      Pv S (gcG hjGE2) ≤ Pv S (Om (1 + 1)) ∧ Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hlt : hjGE < hjGE2 :=
    hd_veb_left_lt ((lt_add_iff_pos_right _).2 (mul_pos gv_Om1_pos omega0_pos)) _
  have hV : InE (gcG hjGE2) := Low.opow_eq_self_of_SC (gcG_SC _)
  refine ⟨hlt, iota_mono _ _ (InE.mul_lt hV (gcG_lt hlt) (omega0_lt_inE hV)).le,
    iota_mono _ _ hjGE2_lt_Om2.le, Nm.Pv_mono hjGE2_lt_Om2.le, ga_Pv_lt_L0 S le_rfl⟩

end Googology.Trans.PoR.InaccPsi.R2.Hj
