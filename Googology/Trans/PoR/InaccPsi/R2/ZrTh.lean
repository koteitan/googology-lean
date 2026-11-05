import Googology.Trans.PoR.InaccPsi.R2.ZrBase
import Googology.Trans.PoR.InaccPsi.R2.ZjRead
import Googology.Trans.PoR.InaccPsi.R2.UxB

/-!
# Zr: the base `l₀` of the (B-hi) ∪ (C) induction is `ι(Ω₂)`, with the name `Ω₂` and the code `π_{Ω₂}`

`K_0 = Ω₁`, `K_{j+1} = ψ_{Ω₂}(Ω_ω + K_j)` (`Le.leKe S 0 Ω_ω`), `W = Ω₁^{Ω₁}`, `P(η) = ψ_{Ω₁}(Ω_ω + θ·η)`.

* `zrK_sup` (**the plateau**: `x < ψ_{Ω₂}(Ω_ω + Ω₂) ⇔ ∃ j, x < K_j`, `Le.leKe_sup` at the exponent `0`);
* `zrK_mem`, `zrK_good`, `zrK_dvd` (`K_j` lies in every hull that reaches `Ω_ω + K_{j-1}`; every `K_{j+1}` is a good
  name and a multiple of `W`);
* `zrGP_K` (**`P(K_{j+1} + W)` is a `Γ`-point**, `Lw.lw_GP_step`);
* `zrPv_le_sup` (**`P(Ω₂) ≤ sup_j P(K_{j+1} + W)`**: `θ·Ω₂ = Ω₂`, `Ls.lsPsi_le_mem` at `A = Ω_ω`, `D = Ω₂`, every
  `ζ < Ω₂` of the hull lies below some `K_j`);
* `zrGP_Om2` (**`P(Ω₂)` is a `Γ`-point**, `Lw.lw_GP_of_cof`), `zrIota_ri` (**`ι(Ω₂)` is a restart index** and
  `P(Ω₂) = υ_{ι(Ω₂)}`, `Lw.lw_restart_of_GP`);
* `zrBase_eq` (**`l₀ = Zo.zoBase S = ι(Ω₂)`**), `zrBase_eta` (its name is `Ω₂`), `zrBase_code` (its code is the
  π-code `π_{Ω₂} = ψ_{Ω₂}(Ω_ω + Ω₂)`), `zrBase_A` (`A_{η_{l₀}} = Ω_ω + Ω₂`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zr

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Zo Googology.Trans.PoR.InaccPsi.R2.Le

variable {S : InaccSeq.{0}}

/-- `K_j = ψ_{Ω₂}`-iterates over `Ω_ω` at the exponent `0`. -/
noncomputable abbrev zrK (S : InaccSeq.{0}) (j : ℕ) : Ordinal.{0} := leKe S 0 (Om ω) j

theorem zrK_succ (j : ℕ) : zrK S (j + 1) = S.psi (Om ω + zrK S j) (Om (1 + 1)) := by
  show S.psi (Om ω + leWe 0 * leKe S 0 (Om ω) j) (Om (1 + 1)) = _
  rw [leWe_zero, one_mul]

theorem zrK_own : ∀ d, d ≤ leWe (0 + 1) →
    Om ω ∈ S.CSet (Om ω + d) (S.psi (Om ω + d) (Om (1 + 1))) := fun d _ => Zj.zjOmW_own d

theorem zrK_exp : (0 : Ordinal.{0}) < S.psi (Om ω + leWe 0) (Om (1 + 1)) :=
  (Om_pos one_ne_zero).trans (psiS_bounds (S := S) _ 1).1

theorem zrK_lt_succ (j : ℕ) : zrK S j < zrK S (j + 1) := leKe_lt_succ zrK_own zrK_exp j

theorem zrK_mono : StrictMono (zrK S) := strictMono_nat_of_lt_succ zrK_lt_succ

/-- **The plateau**: `x < ψ_{Ω₂}(Ω_ω + Ω₂) ⇔ ∃ j, x < K_j`. -/
theorem zrK_sup {x : Ordinal.{0}} (hx : x < S.psi (Om ω + Om (1 + 1)) (Om (1 + 1))) : ∃ j, x < zrK S j := by
  have h12 : (0 + 1 : Ordinal.{0}) ≤ Om (1 + 1) := by
    rw [zero_add]; exact (Order.one_le_iff_pos.2 (Om_pos one_ne_zero)).trans (Om_le_Om.2 le_self_add)
  have hβd : leWe (0 + 1) ∣ Om ω := Zj.zjWe_dvd h12
  refine leKe_sup zrK_own zrK_exp hβd ?_
  unfold leTe; rw [zero_add, leWe_one]; exact hx

theorem zrK_lt_Om2 (j : ℕ) : zrK S j < Om (1 + 1) := leKe_lt_Om2 0 (Om ω) j

/-- `K_j` lies in every hull `Cl(a, b)` that reaches `Ω_ω + K_i` for `i < j`. -/
theorem zrK_mem {a b : Ordinal.{0}} : ∀ j : ℕ, (∀ i < j, Om ω + zrK S i < a) → zrK S j ∈ S.CSet a b
  | 0, _ => CSet.Om_mem (CSet.one_mem a b)
  | j + 1, h => by
    rw [zrK_succ]
    exact CSet.psi_mem (h j (Nat.lt_succ_self j)) (InR_Om_succ 1)
      (CSet.Om_mem (CSet.add_mem (CSet.one_mem a b) (CSet.one_mem a b)))
      (CSet.add_mem (ConjT.OmW_mem S a b) (zrK_mem j fun i hi => h i (hi.trans (Nat.lt_succ_self j))))

theorem zrK_SC (j : ℕ) : SC (zrK S (j + 1)) := by
  rw [zrK_succ]; exact SC_psi (InR_Om_succ 1) _

theorem zrK_gt_Om1 (j : ℕ) : Om 1 < zrK S (j + 1) := by
  rw [zrK_succ]; exact (psiS_bounds (S := S) _ 1).1

/-- `x ≤ θ·x`. -/
theorem zr_le_th_mul (x : Ordinal.{0}) : x ≤ ConjT.th S * x := by
  have hpos : (0 : Ordinal.{0}) < ConjT.th S := (Om_pos one_ne_zero).trans (psiS_bounds (S := S) _ 1).1
  calc x = 1 * x := (one_mul x).symm
    _ ≤ ConjT.th S * x := mul_le_mul_right' (Order.one_le_iff_pos.2 hpos) x

/-- **`K_{j+1}` is a good name.** -/
theorem zrK_good (j : ℕ) : Bt.Good S (zrK S (j + 1)) := by
  unfold Bt.Good
  refine zrK_mem (j + 1) fun i hi => ?_
  have h1 : zrK S i < zrK S (j + 1) := zrK_mono hi
  have h2 : zrK S (j + 1) ≤ ConjT.th S * zrK S (j + 1) := zr_le_th_mul _
  unfold ConjT.Aη
  exact ((add_lt_add_iff_left _).2 (h1.trans_le h2)).trans (lt_add_one _)

theorem zrK_dvd (j : ℕ) : W ∣ zrK S (j + 1) := Lw.lw_W_dvd_SC (zrK_SC j) (zrK_gt_Om1 j)

/-- **`P(K_{j+1} + W)` is a `Γ`-point.** -/
theorem zrGP_K (j : ℕ) : IsGP (Pv S (zrK S (j + 1) + W)) := Lw.lw_GP_step (zrK_good j) (zrK_dvd j)

/-- `θ·Ω₂ = Ω₂`, so `A_{Ω₂} = Ω_ω + Ω₂`. -/
theorem zr_th_Om2 : ConjT.th S * Om (1 + 1) = Om (1 + 1) :=
  Ux.uxK_mul_SC (SC_psi (InR_Om_succ 1) _) Gg.gg_SC_Om2 (psi_lt (InR_Om_succ 1) _)

theorem zrA_Om2 : ConjT.Aη S (Om (1 + 1)) = Om ω + Om (1 + 1) := by
  unfold ConjT.Aη; rw [zr_th_Om2]

theorem zrK_W_le (j : ℕ) : zrK S (j + 1) + W ≤ Om (1 + 1) := by
  have hW : W < Om (1 + 1) :=
    Lw.lw_W_lt_SC Gg.gg_SC_Om2 (Om_lt_Om.2 (lt_add_of_pos_right 1 zero_lt_one))
  exact (Gg.gg_SC_Om2.isPrincipal (zrK_lt_Om2 _) hW).le

/-- The sup of the `Γ`-points `P(K_{j+1} + W)`. -/
noncomputable abbrev zrSig (S : InaccSeq.{0}) : Ordinal.{0} := ⨆ j : ℕ, Pv S (zrK S (j + 1) + W)

theorem zrSig_bdd : BddAbove (Set.range fun j : ℕ => Pv S (zrK S (j + 1) + W)) := Ordinal.bddAbove_of_small

theorem zrG_le_sig (j : ℕ) : Pv S (zrK S (j + 1) + W) ≤ zrSig S := le_ciSup zrSig_bdd j

theorem zrG_mono {i j : ℕ} (h : i ≤ j) : Pv S (zrK S (i + 1) + W) ≤ Pv S (zrK S (j + 1) + W) :=
  Pv_mono (add_le_add (zrK_mono.monotone (Nat.succ_le_succ h)) le_rfl)

theorem zrSig_SC : SC (zrSig S) := by
  have hlt : ∀ y, y < zrSig S ↔ ∃ j, y < Pv S (zrK S (j + 1) + W) := fun y => lt_ciSup_iff zrSig_bdd
  refine ⟨(Pv_SC S _).1.trans_le (zrG_le_sig 0), fun x hx y hy => ?_⟩
  obtain ⟨i, hi⟩ := (hlt _).1 hx
  obtain ⟨j, hj⟩ := (hlt _).1 hy
  have hi' := hi.trans_le (zrG_mono (le_max_left i j))
  have hj' := hj.trans_le (zrG_mono (le_max_right i j))
  exact ((Pv_SC S _).2 _ hi' _ hj').trans_le (zrG_le_sig _)

/-- `ψ_{Ω₁}(Ω_ω + K_j) < P(K_{j+1} + W)`. -/
theorem zrK_psi_lt (j : ℕ) : S.psi (Om ω + zrK S j) (Om 1) < Pv S (zrK S (j + 1) + W) := by
  have hlt : zrK S j < ConjT.th S * (zrK S (j + 1) + W) :=
    (zrK_lt_succ j).trans_le (le_self_add.trans (zr_le_th_mul _))
  show S.psi (Om ω + zrK S j) (Om 1) < S.psi (Om ω + ConjT.th S * (zrK S (j + 1) + W)) (Om 1)
  refine psi_lt_psi_of_mem Low.InR_Om_one ((add_lt_add_iff_left _).2 hlt) ?_
  refine CSet.add_mem (ConjT.OmW_mem S _ _) (zrK_mem j fun i hi => ?_)
  exact (add_lt_add_iff_left _).2 ((zrK_mono hi).trans hlt)

/-- **`P(Ω₂) ≤ sup_j P(K_{j+1} + W)`.** -/
theorem zrPv_le_sup : Pv S (Om (1 + 1)) ≤ zrSig S := by
  show S.psi (ConjT.Aη S (Om (1 + 1))) (Om 1) ≤ _
  rw [zrA_Om2]
  have hE2 : ω ^ Om (1 + 1 : Ordinal.{0}) = Om (1 + 1) := Low.opow_eq_self_of_SC Gg.gg_SC_Om2
  have hg : ω ^ Om (1 + 1 : Ordinal.{0}) ∣ Om ω := by
    rw [← Zj.zjOmW_eq]
    exact opow_dvd_opow ω (Om_le_Om.2 (by
      rw [one_add_one_eq_two]; exact_mod_cast (natCast_lt_omega0 2).le))
  refine Ls.lsPsi_le_mem zrSig_SC ?_ hg hE2.ge fun ζ hζ hζ2 => ?_
  · refine lt_of_lt_of_le ?_ (zrG_le_sig 0)
    have h := zrK_psi_lt (S := S) 0
    exact (psi_mono (S := S) Low.InR_Om_one le_self_add).1.trans_lt h
  · have hσP : zrSig S ≤ Pv S (Om (1 + 1)) := ciSup_le fun j => Pv_mono (zrK_W_le j)
    have hσ : zrSig S ≤ S.psi (Om ω + Om (1 + 1)) (Om (1 + 1)) :=
      (hσP.trans (Pv_lt_Om1 S _).le).trans (psiS_bounds (S := S) _ 1).1.le
    have hmem : ζ ∈ S.CSet (Om ω + Om (1 + 1)) (S.psi (Om ω + Om (1 + 1)) (Om (1 + 1))) :=
      CSet_mono le_rfl hσ hζ
    have hζπ := lt_psi_of_mem (InR_Om_succ 1) hmem hζ2
    obtain ⟨j, hj⟩ := zrK_sup hζπ
    exact (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left _).2 hj.le)).1.trans_lt
      ((zrK_psi_lt j).trans_le (zrG_le_sig j))

/-- **`P(Ω₂)` is a `Γ`-point.** -/
theorem zrGP_Om2 : IsGP (Pv S (Om (1 + 1))) :=
  Lw.lw_GP_of_cof (Pv_SC S _).1 (Pv_SC S _).isSuccLimit fun b hb => by
    have hb' : b < zrSig S := hb.trans_le zrPv_le_sup
    obtain ⟨j, hj⟩ := (lt_ciSup_iff zrSig_bdd).1 hb'
    exact ⟨_, hj, Pv_mono (zrK_W_le j), zrGP_K j⟩

/-- **`ι(Ω₂)` is a restart index**, with `P(Ω₂) = υ_{ι(Ω₂)}`. -/
theorem zrIota_ri : IsRestartIdx (iota S (Om (1 + 1))) ∧ Pv S (Om (1 + 1)) = upsilon (iota S (Om (1 + 1))) :=
  Lw.lw_restart_of_GP zrGP_Om2

/-- **The base `l₀` is `ι(Ω₂)`.** -/
theorem zrBase_eq : zoBase S = iota S (Om (1 + 1)) :=
  le_antisymm (zoBase_le zrIota_ri.1 le_rfl) zoBase_spec.2

theorem zrBase_rho : upsilon (zoBase S) = Pv S (Om (1 + 1)) := by
  rw [zrBase_eq]; exact zrIota_ri.2.symm

/-- **The name of `l₀` is `Ω₂`.** -/
theorem zrBase_eta : cdEta S (zoBase S) = Om (1 + 1) := by
  rw [zrBase_eq]; exact cdEta_unique (Ga.ga_Om2_good S) rfl

theorem zrBase_A : ConjT.Aη S (cdEta S (zoBase S)) = Om ω + Om (1 + 1) := by
  rw [zrBase_eta, zrA_Om2]

/-- **The code of `l₀` is the π-code `π_{Ω₂}`** (the last exponent of `Ω₂` is `Ω₂`). -/
theorem zrBase_code : cdCode S (zoBase S) = cdPi S (Om (1 + 1)) := by
  have hE2 : ω ^ Om (1 + 1 : Ordinal.{0}) = Om (1 + 1) := Low.opow_eq_self_of_SC Gg.gg_SC_Om2
  have h0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := (Om_pos (by
    rw [one_add_one_eq_two]; exact two_ne_zero)).ne'
  have hle : Om (1 + 1 : Ordinal.{0}) ≤ cdExp (Om (1 + 1)) := cdExp_max h0 (by rw [hE2])
  unfold cdCode
  rw [zrBase_eta]
  unfold cdCodeOf
  rw [if_neg (not_lt.2 hle)]

/-- **`Θ_{l₀}(m_{l₀}) = Θ_{l₀}(Ω₂) = otp(Cl(Ω_ω + Ω₂, P(Ω₂)) ∩ Ω₂)`.** -/
theorem zrBase_theta : cdTheta S (zoBase S) (cdCode S (zoBase S)) = cdTheta S (zoBase S) (Om (1 + 1)) := by
  have hpv : Pv S (cdEta S (zoBase S)) = upsilon (zoBase S) := by rw [zrBase_eta, zrBase_rho]
  have h := cdTheta_pi (S := S) hpv
  rw [zrBase_eta] at h
  rw [zrBase_code]; exact h

end Googology.Trans.PoR.InaccPsi.R2.Zr
