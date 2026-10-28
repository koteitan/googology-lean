import Googology.Trans.PoR.InaccPsi.R2.HiV

/-!
# HiVQ: PSEUDO-BASES AND BASES OF THE LEVEL `Ω₁ + ν` (READ `x + ν`), AND THE GATED OFFSET OF THAT LEVEL

The copy of `Hg.HgfM` (pseudo-bases `Hg.HgfQ μ`, bases `Hg.HgfB μ`, the gated offset `Hg.hgfQOff`, the specification
`Hg.HgfQSpec`) for the uncountable level `Ω₁ + ν` (`ν < Ω₁` a constant) read as `x + ν` at the bases `x > ν`:

* a pseudo-base of level `Ω₁ + ν` (`HiVQ ν`): `F ∈ range φ(Ω₁+ν, ·)` with a reading `F(x) ∈ range φ(x+ν, ·)` above a
  gate `γ ≥ ν`; `HiVQ.toP` (a level-`ω` pseudo-base), `HiVQ.down` (the same point at every level `Ω₁ + ν'`, `ν' < ν`);
* a base of level `Ω₁ + ν` with two gates (`HiVB ν`); `HiVQ.toB` (a pseudo-base of level `Ω₁ + ν + 1` is a base of
  level `Ω₁ + ν`);
* **THE GATED OFFSET OF LEVEL `Ω₁ + ν`** (`hiVOff A E λ`): `φ(Ω₁+ν, F + 1 + λ)`, reading `ϑˣ(Ω₁·(x+ν) + F(x) + λ(x))`,
  gate `max(γN, g_E(λ))` (the level gate `ν < Z` of a code is `Hi.hiv_cl_gate`);
* `HiVSpec`: the specification of a step of level `Ω₁ + ν` (bound `hdNx (Ω₁+ν) F`).

No new axiom.  New definitions: `HiVQ`, `HiVQ.toP`, `hiVPB`, `HiVQ.down`, `HiVB`, `HiVB.Zl`, `HiVQ.toB`, `hiVOff`,
`HiVSpec`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hi

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

/-- **The code of the level `Ω₁ + ν`** over `Z` (`ν < Z`). -/
theorem hiv_L_code {ν Z : Ordinal.{0}} (hνZ : ν < Z) : GxCl Z {gcG 0} (Om1 + ν) := by
  rw [Br.Om1_eq]; exact GxCl.add GxCl.om (GxCl.small hνZ)

theorem hiv_L_mem (S : InaccSeq.{0}) {ν a b : Ordinal.{0}} (hνb : ν < b) : Om1 + ν ∈ S.CSet a b := by
  rw [Br.Om1_eq]; exact CSet.add_mem (CSet.Om_mem (CSet.one_mem _ _)) (CSet.of_lt hνb)

theorem hiv_fixk {ν v : Ordinal.{0}} (hv : LuP (Om1 + ν) v) (k : ℕ) : veblen (k : Ordinal.{0}) v = v := by
  obtain ⟨a, rfl⟩ := hv
  exact veblen_veblen_of_lt (((natCast_lt_omega0 k).trans (omega0_lt_inE gl_Om1_E)).trans_le le_self_add) a

theorem hiv_rfixk {ν x v : Ordinal.{0}} (hx : InE x) (hv : LuP (x + ν) v) (k : ℕ) :
    veblen (k : Ordinal.{0}) v = v := by
  obtain ⟨a, rfl⟩ := hv
  exact veblen_veblen_of_lt (((natCast_lt_omega0 k).trans (omega0_lt_inE hx)).trans_le le_self_add) a

theorem hiv_rfixω {ν x v : Ordinal.{0}} (hx : InE x) (hv : LuP (x + ν) v) : veblen ω v = v := by
  obtain ⟨a, rfl⟩ := hv
  exact veblen_veblen_of_lt ((omega0_lt_inE hx).trans_le le_self_add) a

theorem hiv_Lω {ν v : Ordinal.{0}} (hv : LuP (Om1 + ν) v) : veblen ω v = v := by
  obtain ⟨a, rfl⟩ := hv
  exact veblen_veblen_of_lt ((omega0_lt_inE gl_Om1_E).trans_le le_self_add) a

/-! ## Pseudo-bases of level `Ω₁ + ν` -/

/-- **A pseudo-base of level `Ω₁ + ν`**: `F ∈ range φ(Ω₁+ν, ·)`, `G < F`, its reading `F(x) ∈ range φ(x+ν, ·)` above
the gate `γ ≥ ν`, an outer low field `Z_o` above `hdNx (x+ν) (F(x))`. -/
structure HiVQ (ν : Ordinal.{0}) where
  F : Ordinal.{0}
  Fr : Ordinal.{0} → Ordinal.{0}
  γ : Ordinal.{0}
  Zo : Ordinal.{0} → Ordinal.{0}
  lv : ν < Om1
  γ_ge : ν ≤ γ
  γ_lt : γ < Om1
  F_P : LuP (Om1 + ν) F
  G_lt : gcG 0 < F
  S_lt1 : hdNx (Om1 + ν) F < gcG 1
  F_mem : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → γ < b → F ∈ S.CSet a b
  S_mem : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → γ < b → hdNx (Om1 + ν) F ∈ S.CSet a b
  F_code : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y, GxCl Z {gcG 0} y → F ≤ y → y < hdNx (Om1 + ν) F →
    GxCl Z {gcG 0} F
  F_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y, GxCl Z {gcG 0} y → F ≤ y → y < hdNx (Om1 + ν) F → γ < Z
  S_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z {gcG 0} (hdNx (Om1 + ν) F) → γ < Z
  Fr_gt : ∀ {x}, InE x → x < Om1 → γ < x → x + ν < Fr x
  Fr_P : ∀ {x}, InE x → x < Om1 → γ < x → LuP (x + ν) (Fr x)
  S_Zo : ∀ {x}, InE x → x < Om1 → γ < x → hdNx (x + ν) (Fr x) < Zo x
  Zo_fix : ∀ x, veblen 2 (Zo x) = Zo x
  Zo_G1 : ∀ x, InE x → x < Om1 → Zo x < gq 1 x
  Fr_pi : ∀ {σ ρ}, Bases σ ρ → γ < σ → Fr ρ ∈ TB ρ σ ∧ pi σ ρ (Fr ρ) = Fr σ
  S_pi : ∀ {σ ρ}, Bases σ ρ → γ < σ →
    hdNx (ρ + ν) (Fr ρ) ∈ TB ρ σ ∧ pi σ ρ (hdNx (ρ + ν) (Fr ρ)) = hdNx (σ + ν) (Fr σ)

namespace HiVQ

variable {ν : Ordinal.{0}} (Q : HiVQ ν)

theorem F_fixk (k : ℕ) : veblen (k : Ordinal.{0}) Q.F = Q.F := hiv_fixk Q.F_P k

theorem F_E : InE Q.F := by have := Q.F_fixk 0; rwa [Nat.cast_zero, veblen_zero_apply] at this

theorem F_lt_S : Q.F < hdNx (Om1 + ν) Q.F := hdNx_gt _ _

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : Q.γ < x)
include hx hx1 hγ

theorem ν_lt : ν < x := Q.γ_ge.trans_lt hγ

theorem S_lt1x : hdNx (x + ν) (Q.Fr x) < gq 1 x := (Q.S_Zo hx hx1 hγ).trans (Q.Zo_G1 x hx hx1)

theorem Fr_lt1 : Q.Fr x < gq 1 x := (hdNx_gt _ _).trans (Q.S_lt1x hx hx1 hγ)

theorem Fr_fixk (k : ℕ) : veblen (k : Ordinal.{0}) (Q.Fr x) = Q.Fr x := hiv_rfixk hx (Q.Fr_P hx hx1 hγ) k

theorem Fr_fixω : veblen ω (Q.Fr x) = Q.Fr x := hiv_rfixω hx (Q.Fr_P hx hx1 hγ)

theorem Fr_gtx : x < Q.Fr x := le_self_add.trans_lt (Q.Fr_gt hx hx1 hγ)

end Base

theorem F_fixω : veblen ω Q.F = Q.F := hiv_Lω Q.F_P

/-- **`hcS F` is a code over `Z` ⇒ the gate lies below `Z`.** -/
theorem hS_cl {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (h : GxCl Z {gcG 0} (hcS Q.F)) : Q.γ < Z := by
  rw [hcS_fix Q.F_fixω] at h
  exact Q.F_cl Z hZ hZ1 _ (hd_cl_succ_fix hc_one_le_om hZ hZ1 Q.G_lt.le h) le_rfl Q.F_lt_S

theorem hS_mem (S : InaccSeq.{0}) {a b : Ordinal.{0}} (ha : 0 < a) (hb : Q.γ < b) : hcS Q.F ∈ S.CSet a b := by
  rw [hcS_fix Q.F_fixω]
  exact CSet.phi_mem (gr_cst_mem ha _ ω (omega0_lt_gamma 1)) (CSet.succ_mem (Q.F_mem S ha hb))

theorem hS_le : hcS Q.F ≤ hdNx (Om1 + ν) Q.F :=
  hdS_le_Nx ((omega0_lt_inE gl_Om1_E).le.trans le_self_add) _

theorem hS_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hγ : Q.γ < σ) :
    hcS (Q.Fr ρ) ∈ TB ρ σ ∧ pi σ ρ (hcS (Q.Fr ρ)) = hcS (Q.Fr σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hγρ : Q.γ < ρ := hγ.trans hB.2.2.1
  have hωσ : ω < σ := omega0_lt_inE hB.1
  obtain ⟨f1, f2⟩ := Q.Fr_pi hB hγ
  have h := glA_pi hB (mem_TB_of_lt hB hωσ) (hc_om_T hB.2.1 hρ1).2 f1 (gm1_T hB.2.1 hρ1 (Q.Fr_lt1 hB.2.1 hρ1 hγρ)).2
  rw [pi_lt hB hωσ, f2, hc_glA_fixW hB.2.1 hρ1 (Q.Fr_fixω hB.2.1 hρ1 hγρ) (Q.Fr_gtx hB.2.1 hρ1 hγρ)
    (Q.Fr_lt1 hB.2.1 hρ1 hγρ), hc_glA_fixW hB.1 hσ1 (Q.Fr_fixω hB.1 hσ1 hγ) (Q.Fr_gtx hB.1 hσ1 hγ)
    (Q.Fr_lt1 hB.1 hσ1 hγ)] at h
  exact h

/-- **A PSEUDO-BASE OF LEVEL `Ω₁ + ν` IS ONE OF LEVEL `ω`.** -/
noncomputable def toP : HgdP where
  F := Q.F
  Fr := Q.Fr
  γ := Q.γ
  Zo := Q.Zo
  γ_lt := Q.γ_lt
  F_fix := Q.F_fixk
  G_lt := Q.G_lt
  S_lt1 := Q.hS_le.trans_lt Q.S_lt1
  F_mem := Q.F_mem
  S_mem := fun S _ _ ha hb => Q.hS_mem S ha hb
  F_code := fun Z hZ hZ1 y hy hQy hyZ => Q.F_code Z hZ hZ1 y hy hQy (hyZ.trans_le Q.hS_le)
  F_cl := fun Z hZ hZ1 y hy hQy hyZ => Q.F_cl Z hZ hZ1 y hy hQy (hyZ.trans_le Q.hS_le)
  S_cl := fun Z hZ hZ1 h => Q.hS_cl hZ hZ1 h
  Fr_gt := fun hx hx1 hγ => Q.Fr_gtx hx hx1 hγ
  Fr_fix := fun hx hx1 hγ k => Q.Fr_fixk hx hx1 hγ k
  S_Zo := fun {x} hx hx1 hγ => (hdS_le_Nx ((omega0_lt_inE hx).le.trans le_self_add) _).trans_lt (Q.S_Zo hx hx1 hγ)
  Zo_fix := Q.Zo_fix
  Zo_G1 := Q.Zo_G1
  Fr_pi := Q.Fr_pi
  S_pi := fun hB hγ => Q.hS_pi hB hγ

/-- **A PSEUDO-BASE OF LEVEL `Ω₁ + ν` IS ONE OF EVERY LEVEL `Ω₁ + ν'`, `ν' < ν`.** -/
noncomputable def down {ν' : Ordinal.{0}} (hν' : ν' < ν) : HiVQ ν' where
  F := Q.F
  Fr := Q.Fr
  γ := Q.γ
  Zo := Q.Zo
  lv := hν'.trans Q.lv
  γ_ge := hν'.le.trans Q.γ_ge
  γ_lt := Q.γ_lt
  F_P := hd_LuP_mono (add_le_add le_rfl hν'.le) Q.F_P
  G_lt := Q.G_lt
  S_lt1 := (hdNx_mono (add_le_add le_rfl hν'.le) _).trans_lt Q.S_lt1
  F_mem := Q.F_mem
  S_mem := fun S _ _ ha hb => by
    have hfix : veblen (Om1 + ν') Q.F = Q.F := by
      obtain ⟨a, ha⟩ := Q.F_P; rw [← ha]; exact veblen_veblen_of_lt ((add_lt_add_iff_left _).2 hν') a
    rw [hdNx_fixP hfix]
    exact CSet.phi_mem (hiv_L_mem S ((hν'.le.trans Q.γ_ge).trans_lt hb)) (CSet.succ_mem (Q.F_mem S ha hb))
  F_code := fun Z hZ hZ1 y hy hQy hyZ =>
    Q.F_code Z hZ hZ1 y hy hQy (hyZ.trans_le (hdNx_mono (add_le_add le_rfl hν'.le) _))
  F_cl := fun Z hZ hZ1 y hy hQy hyZ =>
    Q.F_cl Z hZ hZ1 y hy hQy (hyZ.trans_le (hdNx_mono (add_le_add le_rfl hν'.le) _))
  S_cl := fun Z hZ hZ1 h => by
    have hfix : veblen (Om1 + ν') Q.F = Q.F := by
      obtain ⟨a, ha⟩ := Q.F_P; rw [← ha]; exact veblen_veblen_of_lt ((add_lt_add_iff_left _).2 hν') a
    rw [hdNx_fixP hfix] at h
    exact Q.F_cl Z hZ hZ1 _ (hd_cl_succ_fix (hiv_L1 ν') hZ hZ1 Q.G_lt.le h) le_rfl Q.F_lt_S
  Fr_gt := fun hx hx1 hγ => (add_lt_add_iff_left _).2 hν' |>.trans (Q.Fr_gt hx hx1 hγ)
  Fr_P := fun hx hx1 hγ => hd_LuP_mono (add_le_add le_rfl hν'.le) (Q.Fr_P hx hx1 hγ)
  S_Zo := fun hx hx1 hγ => (hdNx_mono (add_le_add le_rfl hν'.le) _).trans_lt (Q.S_Zo hx hx1 hγ)
  Zo_fix := Q.Zo_fix
  Zo_G1 := Q.Zo_G1
  Fr_pi := Q.Fr_pi
  S_pi := fun {σ ρ} hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hγρ : Q.γ < ρ := hγ.trans hB.2.2.1
    have hfix : ∀ {y}, InE y → y < Om1 → Q.γ < y → veblen (y + ν') (Q.Fr y) = Q.Fr y := fun hy hy1 hγy => by
      obtain ⟨a, ha⟩ := Q.Fr_P hy hy1 hγy; rw [← ha]; exact veblen_veblen_of_lt ((add_lt_add_iff_left _).2 hν') a
    obtain ⟨f1, f2⟩ := Q.Fr_pi hB hγ
    have hν'σ : ν' < σ := (hν'.trans_le Q.γ_ge).trans hγ
    have h := hiv_glA_pi hB hν'σ f1 (Q.Fr_lt1 hB.2.1 hρ1 hγρ)
    have hgt : ∀ {y}, InE y → y < Om1 → Q.γ < y → y + ν' < Q.Fr y := fun hy hy1 hγy =>
      (add_lt_add_iff_left _).2 hν' |>.trans (Q.Fr_gt hy hy1 hγy)
    rw [f2, hiv_glA_fixP hB.2.1 hρ1 (hν'σ.trans hB.2.2.1) (hfix hB.2.1 hρ1 hγρ) (hgt hB.2.1 hρ1 hγρ)
      (Q.Fr_lt1 hB.2.1 hρ1 hγρ), hiv_glA_fixP hB.1 hσ1 hν'σ (hfix hB.1 hσ1 hγ) (hgt hB.1 hσ1 hγ)
      (Q.Fr_lt1 hB.1 hσ1 hγ)] at h
    exact h

theorem down_F {ν' : Ordinal.{0}} (hν' : ν' < ν) : (Q.down hν').F = Q.F := rfl

end HiVQ

/-- **The stage at a pseudo-base of level `Ω₁ + ν`** (the stage at it as a level-`ω` pseudo-base). -/
noncomputable abbrev hiVPB {ν : Ordinal.{0}} (Q : HiVQ ν) : HgPB := hgdPB Q.toP

theorem hiVPB_down {ν ν' : Ordinal.{0}} (Q : HiVQ ν) (hν' : ν' < ν) : hiVPB (Q.down hν') = hiVPB Q := rfl

/-! ## Bases of level `Ω₁ + ν` -/

/-- **A base of level `Ω₁ + ν` WITH TWO GATES**: a fixed point `F` of `φ(Ω₁+ν, ·)`, a CODE GATE `γ` and a READING
GATE `γN ≥ max(γ, ν)` (the reading `F(x)`, a fixed point of `φ(x+ν, ·)`, and `N_{x+ν}(F(x))` above it). -/
structure HiVB (ν : Ordinal.{0}) where
  F : Ordinal.{0}
  Fr : Ordinal.{0} → Ordinal.{0}
  γ : Ordinal.{0}
  γN : Ordinal.{0}
  Zo : Ordinal.{0} → Ordinal.{0}
  lv : ν < Om1
  γ_le : γ ≤ γN
  lvN : ν ≤ γN
  γN_lt : γN < Om1
  F_fix : veblen (Om1 + ν) F = F
  G_le : gcG 0 ≤ F
  N_lt1 : hcN (Om1 + ν) F < gcG 1
  F_mem : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → γ < b → F ∈ S.CSet a b
  N_mem : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → γN < b → hcN (Om1 + ν) F ∈ S.CSet a b
  F_code : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y, GxCl Z {gcG 0} y → F ≤ y → y < hcN (Om1 + ν) F →
    GxCl Z {gcG 0} F
  F_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y, GxCl Z {gcG 0} y → F ≤ y → y < hcN (Om1 + ν) F → γ < Z
  N_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z {gcG 0} (hcN (Om1 + ν) F) → γN < Z
  γN_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → γ < Z → ν < Z → γN < Z
  Fr_gt : ∀ {x}, InE x → x < Om1 → γN < x → x + ν < Fr x
  Fr_fix : ∀ {x}, InE x → x < Om1 → γN < x → veblen (x + ν) (Fr x) = Fr x
  N_Zo : ∀ {x}, InE x → x < Om1 → γN < x → hcN (x + ν) (Fr x) < Zo x
  Zo_fix : ∀ x, veblen 2 (Zo x) = Zo x
  Zo_G1 : ∀ x, InE x → x < Om1 → Zo x < gq 1 x
  Fr_pi : ∀ {σ ρ}, Bases σ ρ → γN < σ → Fr ρ ∈ TB ρ σ ∧ pi σ ρ (Fr ρ) = Fr σ
  N_pi : ∀ {σ ρ}, Bases σ ρ → γN < σ →
    hcN (ρ + ν) (Fr ρ) ∈ TB ρ σ ∧ pi σ ρ (hcN (ρ + ν) (Fr ρ)) = hcN (σ + ν) (Fr σ)

namespace HiVB

variable {ν : Ordinal.{0}} (A : HiVB ν)

open Classical in
/-- **The low field of `A`**: `N_{x+ν}(F(x))` above `γN`, `Z_o(x)` at or below it. -/
noncomputable def Zl (x : Ordinal.{0}) : Ordinal.{0} :=
  if A.γN < x then hcN (max ω x + ν) (A.Fr x) else A.Zo x

theorem Zl_eq {x : Ordinal.{0}} (hx : InE x) (h : A.γN < x) : A.Zl x = hcN (x + ν) (A.Fr x) := by
  unfold HiVB.Zl; rw [if_pos h, max_eq_right (omega0_lt_inE hx).le]

theorem Zl_low {x : Ordinal.{0}} (h : ¬ A.γN < x) : A.Zl x = A.Zo x := by unfold HiVB.Zl; rw [if_neg h]

theorem Zl_le_Zo (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : A.Zl x ≤ A.Zo x := by
  by_cases h : A.γN < x
  · rw [A.Zl_eq hx h]; exact (A.N_Zo hx hx1 h).le
  · rw [A.Zl_low h]

theorem Zl_G1 (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : A.Zl x < gq 1 x :=
  (A.Zl_le_Zo x hx hx1).trans_lt (A.Zo_G1 x hx hx1)

theorem Zl_fix (x : Ordinal.{0}) : veblen 2 (A.Zl x) = A.Zl x := by
  unfold HiVB.Zl; split_ifs
  · exact hc_fix_down ((show (2 : Ordinal.{0}) ≤ ω from (by exact_mod_cast (natCast_lt_omega0 2).le)).trans
      ((le_max_left ω x).trans le_self_add)) (hcN_fix _ _)
  · exact A.Zo_fix x

theorem γ_lt : A.γ < Om1 := A.γ_le.trans_lt A.γN_lt

theorem F_E : InE A.F := hc_fix_E A.F_fix

theorem N_E : InE (hcN (Om1 + ν) A.F) := hcN_E _ _

theorem F_lt_N : A.F < hcN (Om1 + ν) A.F := hcN_gt _ _

theorem N_lim : IsSuccLimit (hcN (Om1 + ν) A.F) := hcN_lim _ _

theorem Fr_lt_N (x : Ordinal.{0}) : A.Fr x < hcN (x + ν) (A.Fr x) := hcN_gt _ _

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : A.γN < x)
include hx hx1 hγ

theorem ν_lt : ν < x := A.lvN.trans_lt hγ

theorem N_lt1x : hcN (x + ν) (A.Fr x) < gq 1 x := (A.N_Zo hx hx1 hγ).trans (A.Zo_G1 x hx hx1)

theorem Fr_lt1 : A.Fr x < gq 1 x := (A.Fr_lt_N x).trans (A.N_lt1x hx hx1 hγ)

/-- **`ϑˣ(Ω₁·(x+ν) + F(x)) = hdNx (x+ν) (F(x))`.** -/
theorem Fr_glA : glA (x + ν) (A.Fr x) x = hdNx (x + ν) (A.Fr x) :=
  hiv_glA_fixP hx hx1 (A.ν_lt hx hx1 hγ) (A.Fr_fix hx hx1 hγ) (A.Fr_gt hx hx1 hγ) (A.Fr_lt1 hx hx1 hγ)

theorem t1_lt1 {r : Ordinal.{0}} (hr : r < hcN (x + ν) (A.Fr x)) : A.Fr x + r + 1 < gq 1 x := by
  have hNE := hcN_E (x + ν) (A.Fr x)
  exact ((ev_isSuccLimit_of_inE hNE).add_one_lt ((inE_indec hNE).add_lt (A.Fr_lt_N x) hr)).trans
    (A.N_lt1x hx hx1 hγ)

theorem t_lt1 {r : Ordinal.{0}} (hr : r < hcN (x + ν) (A.Fr x)) : A.Fr x + r < gq 1 x :=
  (lt_add_one _).trans (A.t1_lt1 hx hx1 hγ hr)

/-- **`ϑˣ(Ω₁·(x+ν) + F(x) + r) < N_{x+ν}(F(x))`** for `r < N_{x+ν}(F(x))`. -/
theorem glA_lt_N {r : Ordinal.{0}} (hr : r < hcN (x + ν) (A.Fr x)) :
    glA (x + ν) (A.Fr x + r) x < hcN (x + ν) (A.Fr x) :=
  hiv_glA_lt hx hx1 (A.ν_lt hx hx1 hγ) (A.Fr_glA hx hx1 hγ) (A.Fr_lt1 hx hx1 hγ) (A.N_lt1x hx hx1 hγ) hr

/-- **`ϑˣ(Ω₁·(x+ν) + F(x) + r) = φ(x+ν, i₀ + r)`** below `N_{x+ν}(F(x))`. -/
theorem lvglAV {r i0 : Ordinal.{0}} (hi0 : veblen (x + ν) i0 = hdNx (x + ν) (A.Fr x))
    (hr : r < hcN (x + ν) (A.Fr x)) : glA (x + ν) (A.Fr x + r) x = veblen (x + ν) (i0 + r) :=
  hiv_lvglAV hx hx1 (A.ν_lt hx hx1 hγ) (A.Fr_glA hx hx1 hγ) (A.Fr_lt1 hx hx1 hγ) (A.N_lt1x hx hx1 hγ) hi0 hr

end Base

theorem j_lt {l : Ordinal.{0}} (hl : l < hcN (Om1 + ν) A.F) : A.F + 1 + l < veblen (Om1 + ν) (A.F + 1 + l) := by
  set y := A.F + 1 + l with hy
  have hyN : y < hcN (Om1 + ν) A.F := (inE_indec A.N_E).add_lt (A.N_lim.add_one_lt A.F_lt_N) hl
  rcases (right_le_veblen (Om1 + ν) y).lt_or_eq with h | h
  · exact h
  · exfalso
    have hFy : A.F < y := (lt_add_one _).trans_le le_self_add
    exact absurd (hcN_le h.symm hFy) (not_le.2 hyN)

theorem add_lt_N {l : Ordinal.{0}} (hl : l < hcN (Om1 + ν) A.F) : A.F + 1 + l < hcN (Om1 + ν) A.F :=
  (inE_indec A.N_E).add_lt (A.N_lim.add_one_lt A.F_lt_N) hl

theorem j1_lt {l : Ordinal.{0}} (hl : l < hcN (Om1 + ν) A.F) :
    A.F + 1 + l + 1 < veblen (Om1 + ν) (A.F + 1 + l + 1) := by
  have h := A.j_lt (A.N_lim.add_one_lt hl)
  rwa [← add_assoc] at h

theorem lt_Q {l : Ordinal.{0}} (hl : l < hcN (Om1 + ν) A.F) : l < veblen (Om1 + ν) (A.F + 1 + l) :=
  le_add_self.trans_lt (A.j_lt hl)

theorem Q_lt_N {l : Ordinal.{0}} (hl : l < hcN (Om1 + ν) A.F) : veblen (Om1 + ν) (A.F + 1 + l) < hcN (Om1 + ν) A.F := by
  have h := (isNormal_veblen (Om1 + ν)).strictMono (A.add_lt_N hl)
  rwa [hcN_fix] at h

theorem Q1_lt_N {l : Ordinal.{0}} (hl : l < hcN (Om1 + ν) A.F) :
    veblen (Om1 + ν) (A.F + 1 + l + 1) < hcN (Om1 + ν) A.F := by
  have h := A.Q_lt_N (A.N_lim.add_one_lt hl)
  rwa [← add_assoc] at h

theorem G_lt_Q (l : Ordinal.{0}) : gcG 0 < veblen (Om1 + ν) (A.F + 1 + l) :=
  A.G_le.trans_lt (((lt_add_one _).trans_le le_self_add).trans_le (right_le_veblen _ _))

theorem Q_lt_Q {μ l : Ordinal.{0}} (h : μ < l) :
    veblen (Om1 + ν) (A.F + 1 + μ) < veblen (Om1 + ν) (A.F + 1 + l) :=
  (isNormal_veblen _).strictMono ((add_lt_add_iff_left _).2 h)

theorem cover {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlN : l < hcN (Om1 + ν) A.F) :
    ∃ μ, μ < l ∧ l < veblen (Om1 + ν) (A.F + 1 + μ) := by
  have h := A.lt_Q hlN
  obtain ⟨t, ht, hlt⟩ := ((isNormal_veblen _).lt_iff_exists_lt (isSuccLimit_add _ hl)).1 h
  obtain ⟨d, hf, htd⟩ := (lt_add_iff hl.bot_lt.ne').1 ht
  exact ⟨d, hf, hlt.trans_le ((isNormal_veblen _).monotone htd)⟩

theorem gate_of_j (E : HgVD) {Z l : Ordinal.{0}} (hlB : l < E.B) (hlN : l < hcN (Om1 + ν) A.F) (hZ : SC Z)
    (hZ1 : Z ≤ Om 1) (h : GxCl Z {gcG 0} (A.F + 1 + l)) : max A.γ (E.g l) < Z := by
  have hFj : A.F ≤ A.F + 1 + l := le_self_add.trans le_self_add
  have hjN := A.add_lt_N hlN
  have hF := A.F_code Z hZ hZ1 _ h hFj hjN
  have hl := hcX_cl_idx hZ hZ1 A.F_E A.G_le hF h
  have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1
  refine max_lt (A.F_cl Z hZ hZ1 _ h hFj hjN) ?_
  exact E.code_gate Z hZ1' hZ.1 (fun _ _ hu hv => hZ.isPrincipal hu hv) (fun _ _ hu hv => hZ.2 _ hu _ hv)
    {gcG 0} (fun s hs => Or.inl (Set.mem_singleton_iff.1 hs)) l hl hlB

/-- **The reading gate at `F + 1 + λ`**: a code `F + 1 + λ` over `Z` with `ν < Z` ⇒ `max(γN, g_E(λ)) < Z`. -/
theorem gate_of_jN (E : HgVD) {Z l : Ordinal.{0}} (hlB : l < E.B) (hlN : l < hcN (Om1 + ν) A.F) (hZ : SC Z)
    (hZ1 : Z ≤ Om 1) (h : GxCl Z {gcG 0} (A.F + 1 + l)) (hνZ : ν < Z) : max A.γN (E.g l) < Z := by
  have h1 := A.gate_of_j E hlB hlN hZ hZ1 h
  exact max_lt (A.γN_cl Z hZ hZ1 (max_lt_iff.1 h1).1 hνZ) (max_lt_iff.1 h1).2

end HiVB

/-! ## A pseudo-base of level `Ω₁ + ν + 1` is a base of level `Ω₁ + ν` -/

theorem hiv_succ_e {ν' ν : Ordinal.{0}} (e : ν' = ν + 1) (a : Ordinal.{0}) : a + ν' = a + ν + 1 := by
  rw [e, add_assoc]

namespace HiVQ

variable {ν' : Ordinal.{0}} (P : HiVQ ν')

/-- **A PSEUDO-BASE OF LEVEL `Ω₁ + ν + 1` IS A BASE OF LEVEL `Ω₁ + ν`** (`ν' = ν + 1`). -/
noncomputable def toB {ν : Ordinal.{0}} (e : ν' = ν + 1) : HiVB ν where
  F := P.F
  Fr := P.Fr
  γ := P.γ
  γN := P.γ
  Zo := P.Zo
  lv := (show ν < ν' by rw [e]; exact lt_add_one ν).trans P.lv
  γ_le := le_rfl
  lvN := (show ν ≤ ν' by rw [e]; exact le_self_add).trans P.γ_ge
  γN_lt := P.γ_lt
  F_fix := hc_fix_of_LuP (hiv_succ_e e Om1 ▸ P.F_P)
  G_le := P.G_lt.le
  N_lt1 := by rw [← hdNx_of_eq (hiv_succ_e e Om1)]; exact P.S_lt1
  F_mem := P.F_mem
  N_mem := fun S _ _ ha hb => by rw [← hdNx_of_eq (hiv_succ_e e Om1)]; exact P.S_mem S ha hb
  F_code := fun Z hZ hZ1 y hy hQy hyZ =>
    P.F_code Z hZ hZ1 y hy hQy (by rw [hdNx_of_eq (hiv_succ_e e Om1)]; exact hyZ)
  F_cl := fun Z hZ hZ1 y hy hQy hyZ =>
    P.F_cl Z hZ hZ1 y hy hQy (by rw [hdNx_of_eq (hiv_succ_e e Om1)]; exact hyZ)
  N_cl := fun Z hZ hZ1 h => P.S_cl Z hZ hZ1 (by rw [hdNx_of_eq (hiv_succ_e e Om1)]; exact h)
  γN_cl := fun _ _ _ h _ => h
  Fr_gt := fun {x} hx hx1 hγ => (show x + ν < x + ν' by rw [e]; exact (add_lt_add_iff_left _).2 (lt_add_one ν)).trans
    (P.Fr_gt hx hx1 hγ)
  Fr_fix := fun {x} hx hx1 hγ => hc_fix_of_LuP (hiv_succ_e e x ▸ P.Fr_P hx hx1 hγ)
  N_Zo := fun {x} hx hx1 hγ => by rw [← hdNx_of_eq (hiv_succ_e e x)]; exact P.S_Zo hx hx1 hγ
  Zo_fix := P.Zo_fix
  Zo_G1 := P.Zo_G1
  Fr_pi := P.Fr_pi
  N_pi := fun {σ ρ} hB hγ => by
    rw [← hdNx_of_eq (hiv_succ_e e ρ), ← hdNx_of_eq (hiv_succ_e e σ)]; exact P.S_pi hB hγ

theorem toB_F {ν : Ordinal.{0}} (e : ν' = ν + 1) : (P.toB e).F = P.F := rfl

end HiVQ

/-! ## The gated offset of level `Ω₁ + ν` -/

section Off

variable {ν : Ordinal.{0}} (A : HiVB ν) (E : HgVD) (l : Ordinal.{0}) (hlB : l < E.B)
  (hlN : l < hcN (Om1 + ν) A.F) (hZ : ∀ x, InE x → x < Om1 → E.Z x ≤ A.Zl x)

include hlB hZ in
theorem hiVOff_R_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : max A.γN (E.g l) < x) :
    E.R l x < hcN (x + ν) (A.Fr x) := by
  have h := (E.R_lt_Z x hx hx1 l hlB (max_lt_iff.1 hγ).2).trans_le (hZ x hx hx1)
  rwa [A.Zl_eq hx (max_lt_iff.1 hγ).1] at h

include hlB in
theorem hiVOff_t_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hγ : max A.γN (E.g l) < σ) :
    A.Fr ρ + E.R l ρ ∈ TB ρ σ ∧ pi σ ρ (A.Fr ρ + E.R l ρ) = A.Fr σ + E.R l σ := by
  obtain ⟨f1, f2⟩ := A.Fr_pi hB (max_lt_iff.1 hγ).1
  obtain ⟨e1, e2⟩ := E.ex σ ρ hB l hlB (max_lt_iff.1 hγ).2
  obtain ⟨s1, s2⟩ := pi_add hB f1 e1
  rw [f2, e2] at s2
  exact ⟨s1, s2⟩

include hlB hZ in
theorem hiVOff_glA_pi {σ ρ s : Ordinal.{0}} (hB : Bases σ ρ) (hγ : max A.γN (E.g l) < σ) (hsσ : s < σ) :
    glA (ρ + ν) (A.Fr ρ + E.R l ρ + s) ρ ∈ TB ρ σ ∧
      pi σ ρ (glA (ρ + ν) (A.Fr ρ + E.R l ρ + s) ρ) = glA (σ + ν) (A.Fr σ + E.R l σ + s) σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hγρ : max A.γN (E.g l) < ρ := hγ.trans hB.2.2.1
  obtain ⟨t1, t2⟩ := hiVOff_t_pi A E l hlB hB hγ
  obtain ⟨u1, u2⟩ := pi_add hB t1 (mem_TB_of_lt hB hsσ)
  rw [t2, pi_lt hB hsσ] at u2
  have hs1 : A.Fr ρ + E.R l ρ + s < gq 1 ρ := by
    have hq := (gm1_facts hB.2.1 hρ1).2.2.2
    exact (inE_indec hq).add_lt (A.t_lt1 hB.2.1 hρ1 (max_lt_iff.1 hγρ).1
      (hiVOff_R_lt A E l hlB hZ hB.2.1 hρ1 hγρ)) (hsσ.trans (hB.2.2.1.trans (gm1_facts hB.2.1 hρ1).2.1))
  have h := hiv_glA_pi hB (A.lvN.trans_lt (max_lt_iff.1 hγ).1) u1 hs1
  rw [u2] at h
  exact h

include hlB hlN hZ in
/-- **THE GATED OFFSET OF LEVEL `Ω₁ + ν`**: over a base `A` of level `Ω₁ + ν`, the offset `λ` read by `E` gives the
pseudo-base `φ(Ω₁+ν, F + 1 + λ)` of level `Ω₁ + ν`, reading `ϑˣ(Ω₁·(x+ν) + F(x) + λ(x))`, gate `max(γN, g_E(λ))`,
outer low field `Z_l`. -/
noncomputable def hiVOff : HiVQ ν where
  F := veblen (Om1 + ν) (A.F + 1 + l)
  Fr := fun x => glA (x + ν) (A.Fr x + E.R l x) x
  γ := max A.γN (E.g l)
  Zo := A.Zl
  lv := A.lv
  γ_ge := A.lvN.trans (le_max_left _ _)
  γ_lt := max_lt A.γN_lt (E.g_lt l hlB)
  F_P := ⟨_, rfl⟩
  G_lt := A.G_lt_Q l
  S_lt1 := by rw [hdNx_veb]; exact (A.Q1_lt_N hlN).trans A.N_lt1
  F_mem := fun S _ _ ha hb => CSet.phi_mem (hiv_L_mem S ((A.lvN.trans (le_max_left _ _)).trans_lt hb))
    (CSet.add_mem (CSet.succ_mem (A.F_mem S ha ((A.γ_le.trans (le_max_left _ _)).trans_lt hb)))
      (E.mem S _ _ ha l hlB ((le_max_right _ _).trans_lt hb)).1)
  S_mem := fun S _ _ ha hb => by
    rw [hdNx_veb]
    exact CSet.phi_mem (hiv_L_mem S ((A.lvN.trans (le_max_left _ _)).trans_lt hb)) (CSet.succ_mem
      (CSet.add_mem (CSet.succ_mem (A.F_mem S ha ((A.γ_le.trans (le_max_left _ _)).trans_lt hb)))
        (E.mem S _ _ ha l hlB ((le_max_right _ _).trans_lt hb)).1))
  F_code := fun Z hZ hZ1 _ hy hQy hyZ => by
    rw [hdNx_veb] at hyZ
    exact GxCl.phi (hiv_L_code (hiv_cl_gate A.lv hZ hZ1 (A.j_lt hlN) (A.G_lt_Q l) hy hQy hyZ))
      (hd_cl_lev (hiv_L1 ν) hZ1 (A.j_lt hlN) (A.G_lt_Q l) hy hQy hyZ)
  F_cl := fun Z hZ hZ1 _ hy hQy hyZ => by
    rw [hdNx_veb] at hyZ
    exact A.gate_of_jN E hlB hlN hZ hZ1 (hd_cl_lev (hiv_L1 ν) hZ1 (A.j_lt hlN) (A.G_lt_Q l) hy hQy hyZ)
      (hiv_cl_gate A.lv hZ hZ1 (A.j_lt hlN) (A.G_lt_Q l) hy hQy hyZ)
  S_cl := fun Z hZ hZ1 h => by
    rw [hdNx_veb] at h
    have hG1 : gcG 0 < veblen (Om1 + ν) (A.F + 1 + l + 1) := by
      have := A.G_lt_Q (l + 1); rwa [← add_assoc] at this
    have h1 := hd_cl_lev (hiv_L1 ν) hZ1 (A.j1_lt hlN) hG1 h le_rfl
      ((isNormal_veblen (Om1 + ν)).strictMono (lt_add_one _))
    have h2 := ha_cl_succ hZ.1 (fun s hs => by rw [Set.mem_singleton_iff.1 hs]; exact ev_isSuccLimit_of_inE gr_G_inE)
      h1 _ rfl
    exact A.gate_of_jN E hlB hlN hZ hZ1 h2 (hiv_cl_gate A.lv hZ hZ1 (A.j1_lt hlN) hG1 h
      le_rfl ((isNormal_veblen (Om1 + ν)).strictMono (lt_add_one _)))
  Fr_gt := fun hx hx1 hγ => (hiv_glA_facts hx hx1 (A.ν_lt hx hx1 (max_lt_iff.1 hγ).1)
    (A.t_lt1 hx hx1 (max_lt_iff.1 hγ).1 (hiVOff_R_lt A E l hlB hZ hx hx1 hγ))).1
  Fr_P := fun hx hx1 hγ => hiv_glA_P hx hx1 (A.ν_lt hx hx1 (max_lt_iff.1 hγ).1)
    (A.t_lt1 hx hx1 (max_lt_iff.1 hγ).1 (hiVOff_R_lt A E l hlB hZ hx hx1 hγ))
  S_Zo := fun {x} hx hx1 hγ => by
    have hA := (max_lt_iff.1 hγ).1
    have hR1 : E.R l x + 1 < hcN (x + ν) (A.Fr x) :=
      (hcN_lim _ _).add_one_lt (hiVOff_R_lt A E l hlB hZ hx hx1 hγ)
    show hdNx (x + ν) (glA (x + ν) (A.Fr x + E.R l x) x) < A.Zl x
    rw [← hiv_glA_succ hx hx1 (A.ν_lt hx hx1 hA)
      (A.t1_lt1 hx hx1 hA (hiVOff_R_lt A E l hlB hZ hx hx1 hγ)), A.Zl_eq hx hA, add_assoc]
    exact A.glA_lt_N hx hx1 hA hR1
  Zo_fix := A.Zl_fix
  Zo_G1 := fun x hx hx1 => A.Zl_G1 x hx hx1
  Fr_pi := fun {σ ρ} hB hγ => by
    have h := hiVOff_glA_pi A E l hlB hZ hB hγ (omega0_lt_inE hB.1).pos
    rwa [add_zero, add_zero] at h
  S_pi := fun {σ ρ} hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hγρ : max A.γN (E.g l) < ρ := hγ.trans hB.2.2.1
    have h := hiVOff_glA_pi A E l hlB hZ hB hγ (one_lt_omega0.trans (omega0_lt_inE hB.1))
    rw [hiv_glA_succ hB.2.1 hρ1 (A.ν_lt hB.2.1 hρ1 (max_lt_iff.1 hγρ).1)
      (A.t1_lt1 hB.2.1 hρ1 (max_lt_iff.1 hγρ).1 (hiVOff_R_lt A E l hlB hZ hB.2.1 hρ1 hγρ)),
      hiv_glA_succ hB.1 hσ1 (A.ν_lt hB.1 hσ1 (max_lt_iff.1 hγ).1)
      (A.t1_lt1 hB.1 hσ1 (max_lt_iff.1 hγ).1 (hiVOff_R_lt A E l hlB hZ hB.1 hσ1 hγ))] at h
    exact h

theorem hiVOff_F : (hiVOff A E l hlB hlN hZ).F = veblen (Om1 + ν) (A.F + 1 + l) := rfl

theorem hiVOff_Fr (x : Ordinal.{0}) : (hiVOff A E l hlB hlN hZ).Fr x = glA (x + ν) (A.Fr x + E.R l x) x := rfl

theorem hiVOff_γ : (hiVOff A E l hlB hlN hZ).γ = max A.γN (E.g l) := rfl

end Off

/-! ## The specification of a step of level `Ω₁ + ν` -/

/-- **The specification of a system `T` built from a start `U` of the stage at the pseudo-base `P` of level
`Ω₁ + ν`.** -/
structure HiVSpec {ν : Ordinal.{0}} (P : HiVQ ν) (U T : HgVD) : Prop where
  B : T.B = hdNx (Om1 + ν) P.F
  γ : T.γ = P.γ
  b : ∀ x, InE x → x < Om1 → P.γ < x → T.b x = hdNx (x + ν) (P.Fr x)
  Z : ∀ x, InE x → x < Om1 → T.Z x = if P.γ < x then evZ (hdNx (x + ν) (P.Fr x)) else P.Zo x
  extR : ∀ c x, c < U.B → T.R c x = U.R c x
  extg : ∀ c, c < U.B → T.g c = U.g c
  high : ∀ c σ, P.F ≤ c → c < hdNx (Om1 + ν) P.F → InE σ → σ < Om1 → T.g c < σ → P.γ < σ
  RF : ∀ x, InE x → x < Om1 → P.γ < x → T.R P.F x = P.Fr x
  gF : ∀ x, InE x → x < Om1 → (T.g P.F < x ↔ P.γ < x)

end Googology.Trans.PoR.InaccPsi.R2.Hi
