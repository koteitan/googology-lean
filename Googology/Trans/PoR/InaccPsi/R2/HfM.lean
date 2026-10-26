import Googology.Trans.PoR.InaccPsi.R2.HfNx

/-!
# HfM: PSEUDO-BASES AND BASES OF EVERY COUNTABLE LEVEL `ω ≤ μ < Ω₁`, AND THE GATED OFFSET OF LEVEL `μ`

`Hd.HdP` / `Hd.HdA` are the level-`ω` objects.  Here the level is any countable `μ` with `ω ≤ μ < Ω₁` (`Hf.HfLvl`):

* a pseudo-base of level `μ` (`HfQ μ`) is a point `F` of `range φ(μ, ·)` (`G < F`) with a reading `F(x)` in
  `range φ(μ, ·)` above a gate `γ ≥ μ` (`γ_ge`), Lemma EXACT for `F(ρ)` and `hdNx μ (F(ρ))`, the code-gate conditions of
  `[F, hdNx μ F)` and an outer low field above `hdNx μ (F(x))`.  `HfQ.toP` views it as a level-`ω` pseudo-base
  (`Hd.HdP`), so the stage at it is `Hd.hdPB`; `HfQ.down` views it at every countable level `β < μ`;
* a base of level `μ` WITH TWO GATES (`HfB μ`) is a fixed point `F` of `φ(μ, ·)` with a CODE GATE `γ` (membership of
  `F`, the code-gate conditions of `[F, N_μ(F))`) and a READING GATE `γN ≥ max(γ, μ)` (a reading fixed by `φ(μ, ·)`,
  Lemma EXACT for `F(ρ)` and `N_μ(F(ρ))`, an outer low field above `N_μ(F(x))`), `γN` below every `Z` above `γ`, `μ`;
  `HfQ.toB` views a pseudo-base of level `μ+1` as a base of level `μ`;
* **THE GATED OFFSET OF LEVEL `μ`** (`hfQOff A E λ`): over a base `A` of level `μ`, the offset `λ < N_μ(F)` read by
  `E` gives the pseudo-base `φ(μ, F + 1 + λ)` of level `μ`, reading `ϑˣ(Ω₁·μ + F(x) + λ(x))`, gate `max(γN, g_E(λ))`;
* `HfQSpec`: the specification of a step of level `μ` (bound `hdNx μ F`).

No new axiom.  New definitions: `HfQ`, `HfQ.toP`, `hfQPB`, `HfQ.down`, `HfB`, `HfB.Zl`, `HfQ.toB`, `hfQOff`,
`HfQSpec`.  The level-generic helpers (`Hd.hd_succ_lt`, `Hd.hd_cl_succ_fix`, `Hd.hd_LuP_mono`, `Hd.hdNx_mono`,
`Hd.hdS_le_Nx`, `Hd.hdNx_of_eq`) are used from `Hd`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hf

open Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He

open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## Pseudo-bases of level `μ` -/

/-- **A pseudo-base of level `μ`**: a point `F` of `range φ(μ, ·)`, `G < F`, its reading `F(x)` in `range φ(μ, ·)`
above the gate `γ`, an outer low field `Z_o` above `hdNx μ (F(x))`. -/
structure HfQ (μ : Ordinal.{0}) where
  F : Ordinal.{0}
  Fr : Ordinal.{0} → Ordinal.{0}
  γ : Ordinal.{0}
  Zo : Ordinal.{0} → Ordinal.{0}
  lv : HfLvl μ
  γ_ge : μ ≤ γ
  γ_lt : γ < Om1
  F_P : LuP μ F
  G_lt : gcG 0 < F
  S_lt1 : hdNx μ F < gcG 1
  F_mem : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → γ < b → F ∈ S.CSet a b
  S_mem : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → γ < b → hdNx μ F ∈ S.CSet a b
  F_code : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y, GxCl Z {gcG 0} y → F ≤ y → y < hdNx μ F →
    GxCl Z {gcG 0} F
  F_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y, GxCl Z {gcG 0} y → F ≤ y → y < hdNx μ F → γ < Z
  S_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z {gcG 0} (hdNx μ F) → γ < Z
  Fr_gt : ∀ {x}, InE x → x < Om1 → γ < x → x < Fr x
  Fr_P : ∀ {x}, InE x → x < Om1 → γ < x → LuP μ (Fr x)
  S_Zo : ∀ {x}, InE x → x < Om1 → γ < x → hdNx μ (Fr x) < Zo x
  Zo_fix : ∀ x, veblen 2 (Zo x) = Zo x
  Zo_BR : ∀ x, InE x → x < Om1 → Zo x ≤ hcBR x
  Fr_pi : ∀ {σ ρ}, Bases σ ρ → γ < σ → Fr ρ ∈ TB ρ σ ∧ pi σ ρ (Fr ρ) = Fr σ
  S_pi : ∀ {σ ρ}, Bases σ ρ → γ < σ → hdNx μ (Fr ρ) ∈ TB ρ σ ∧ pi σ ρ (hdNx μ (Fr ρ)) = hdNx μ (Fr σ)

namespace HfQ

variable {μ : Ordinal.{0}} (Q : HfQ μ)

theorem F_fixk (k : ℕ) : veblen (k : Ordinal.{0}) Q.F = Q.F := Q.lv.fixk Q.F_P k

theorem F_E : InE Q.F := hc_fix_E (Q.lv.fix1 Q.F_P)

theorem S_E : InE (hdNx μ Q.F) := hdNx_E Q.lv.ne _

theorem F_lt_S : Q.F < hdNx μ Q.F := hdNx_gt _ _

theorem S_le_N (P : Ordinal.{0}) (hP : Q.F < hcN μ P) : hdNx μ Q.F < hcN μ P := hdNx_lt_N hP

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : Q.γ < x)
include hx hx1 hγ

theorem S_lt_BR : hdNx μ (Q.Fr x) < hcBR x := (Q.S_Zo hx hx1 hγ).trans_le (Q.Zo_BR x hx hx1)

theorem S_lt1x : hdNx μ (Q.Fr x) < gq 1 x := (Q.S_lt_BR hx hx1 hγ).trans (hcBR_lt1 hx hx1)

theorem Fr_lt1 : Q.Fr x < gq 1 x := (hdNx_gt _ _).trans (Q.S_lt1x hx hx1 hγ)

theorem Fr_fixk (k : ℕ) : veblen (k : Ordinal.{0}) (Q.Fr x) = Q.Fr x := Q.lv.fixk (Q.Fr_P hx hx1 hγ) k

end Base

/-- **`hcS F` is a code over `Z` ⇒ the gate lies below `Z`.** -/
theorem hS_cl {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (h : GxCl Z {gcG 0} (hcS Q.F)) : Q.γ < Z := by
  rcases Q.lv.1.lt_or_eq with hω | hω
  · have hfix : veblen ω Q.F = Q.F := by obtain ⟨a, ha⟩ := Q.F_P; rw [← ha]; exact veblen_veblen_of_lt hω a
    rw [hcS_fix hfix] at h
    exact Q.F_cl Z hZ hZ1 _ (hd_cl_succ_fix hc_one_le_om hZ hZ1 Q.G_lt.le h) le_rfl Q.F_lt_S
  · subst hω; rw [← hdNx_om] at h; exact Q.S_cl Z hZ hZ1 h

theorem hS_mem (S : InaccSeq.{0}) {a b : Ordinal.{0}} (ha : 0 < a) (hb : Q.γ < b) : hcS Q.F ∈ S.CSet a b := by
  rcases Q.lv.1.lt_or_eq with hω | hω
  · have hfix : veblen ω Q.F = Q.F := by obtain ⟨a, ha⟩ := Q.F_P; rw [← ha]; exact veblen_veblen_of_lt hω a
    rw [hcS_fix hfix]
    exact CSet.phi_mem (gr_cst_mem ha _ ω (omega0_lt_gamma 1)) (CSet.succ_mem (Q.F_mem S ha hb))
  · subst hω; rw [← hdNx_om]; exact Q.S_mem S ha hb

theorem hS_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hγ : Q.γ < σ) :
    hcS (Q.Fr ρ) ∈ TB ρ σ ∧ pi σ ρ (hcS (Q.Fr ρ)) = hcS (Q.Fr σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hγρ : Q.γ < ρ := hγ.trans hB.2.2.1
  rcases Q.lv.1.lt_or_eq with hω | hω
  · have hfix : ∀ {y}, InE y → y < Om1 → Q.γ < y → veblen ω (Q.Fr y) = Q.Fr y := fun hy hy1 hγy => by
      obtain ⟨a, ha⟩ := Q.Fr_P hy hy1 hγy; rw [← ha]; exact veblen_veblen_of_lt hω a
    have hωσ : ω < σ := omega0_lt_inE hB.1
    obtain ⟨f1, f2⟩ := Q.Fr_pi hB hγ
    have h := glA_pi hB (mem_TB_of_lt hB hωσ) (hc_om_T hB.2.1 hρ1).2 f1 (gm1_T hB.2.1 hρ1 (Q.Fr_lt1 hB.2.1 hρ1 hγρ)).2
    rw [pi_lt hB hωσ, f2, hc_glA_fixW hB.2.1 hρ1 (hfix hB.2.1 hρ1 hγρ) (Q.Fr_gt hB.2.1 hρ1 hγρ)
      (Q.Fr_lt1 hB.2.1 hρ1 hγρ), hc_glA_fixW hB.1 hσ1 (hfix hB.1 hσ1 hγ) (Q.Fr_gt hB.1 hσ1 hγ)
      (Q.Fr_lt1 hB.1 hσ1 hγ)] at h
    exact h
  · subst hω; rw [← hdNx_om, ← hdNx_om]; exact Q.S_pi hB hγ

/-- **A PSEUDO-BASE OF LEVEL `μ` IS ONE OF LEVEL `ω`.** -/
noncomputable def toP : HdP where
  F := Q.F
  Fr := Q.Fr
  γ := Q.γ
  Zo := Q.Zo
  γ_lt := Q.γ_lt
  F_fix := Q.F_fixk
  G_lt := Q.G_lt
  S_lt1 := (hdS_le_Nx Q.lv.1 _).trans_lt Q.S_lt1
  F_mem := Q.F_mem
  S_mem := fun S _ _ ha hb => Q.hS_mem S ha hb
  F_code := fun Z hZ hZ1 y hy hQy hyZ => Q.F_code Z hZ hZ1 y hy hQy (hyZ.trans_le (hdS_le_Nx Q.lv.1 _))
  F_cl := fun Z hZ hZ1 y hy hQy hyZ => Q.F_cl Z hZ hZ1 y hy hQy (hyZ.trans_le (hdS_le_Nx Q.lv.1 _))
  S_cl := fun Z hZ hZ1 h => Q.hS_cl hZ hZ1 h
  Fr_gt := Q.Fr_gt
  Fr_fix := fun hx hx1 hγ k => Q.Fr_fixk hx hx1 hγ k
  S_Zo := fun hx hx1 hγ => (hdS_le_Nx Q.lv.1 _).trans_lt (Q.S_Zo hx hx1 hγ)
  Zo_fix := Q.Zo_fix
  Zo_BR := Q.Zo_BR
  Fr_pi := Q.Fr_pi
  S_pi := fun hB hγ => Q.hS_pi hB hγ

/-- **A PSEUDO-BASE OF LEVEL `μ` IS ONE OF EVERY COUNTABLE LEVEL `β < μ`.** -/
noncomputable def down {β : Ordinal.{0}} (hβ : HfLvl β) (hβμ : β < μ) : HfQ β where
  F := Q.F
  Fr := Q.Fr
  γ := Q.γ
  Zo := Q.Zo
  lv := hβ
  γ_ge := hβμ.le.trans Q.γ_ge
  γ_lt := Q.γ_lt
  F_P := hd_LuP_mono hβμ.le Q.F_P
  G_lt := Q.G_lt
  S_lt1 := (hdNx_mono hβμ.le _).trans_lt Q.S_lt1
  F_mem := Q.F_mem
  S_mem := fun S _ _ ha hb => by
    have hfix : veblen β Q.F = Q.F := by obtain ⟨a, ha⟩ := Q.F_P; rw [← ha]; exact veblen_veblen_of_lt hβμ a
    rw [hdNx_fixP hfix]
    exact CSet.phi_mem (he_cst_mem S (hβμ.le.trans Q.γ_ge) hb) (CSet.succ_mem (Q.F_mem S ha hb))
  F_code := fun Z hZ hZ1 y hy hQy hyZ => Q.F_code Z hZ hZ1 y hy hQy (hyZ.trans_le (hdNx_mono hβμ.le _))
  F_cl := fun Z hZ hZ1 y hy hQy hyZ => Q.F_cl Z hZ hZ1 y hy hQy (hyZ.trans_le (hdNx_mono hβμ.le _))
  S_cl := fun Z hZ hZ1 h => by
    have hfix : veblen β Q.F = Q.F := by obtain ⟨a, ha⟩ := Q.F_P; rw [← ha]; exact veblen_veblen_of_lt hβμ a
    rw [hdNx_fixP hfix] at h
    exact Q.F_cl Z hZ hZ1 _ (hd_cl_succ_fix hβ.one_le hZ hZ1 Q.G_lt.le h) le_rfl Q.F_lt_S
  Fr_gt := Q.Fr_gt
  Fr_P := fun hx hx1 hγ => hd_LuP_mono hβμ.le (Q.Fr_P hx hx1 hγ)
  S_Zo := fun hx hx1 hγ => (hdNx_mono hβμ.le _).trans_lt (Q.S_Zo hx hx1 hγ)
  Zo_fix := Q.Zo_fix
  Zo_BR := Q.Zo_BR
  Fr_pi := Q.Fr_pi
  S_pi := fun {σ ρ} hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hγρ : Q.γ < ρ := hγ.trans hB.2.2.1
    have hfix : ∀ {y}, InE y → y < Om1 → Q.γ < y → veblen β (Q.Fr y) = Q.Fr y := fun hy hy1 hγy => by
      obtain ⟨a, ha⟩ := Q.Fr_P hy hy1 hγy; rw [← ha]; exact veblen_veblen_of_lt hβμ a
    obtain ⟨f1, f2⟩ := Q.Fr_pi hB hγ
    have hβσ : β < σ := (hβμ.trans_le Q.γ_ge).trans hγ
    have h := hfm_glA_pi hβσ hB f1 (Q.Fr_lt1 hB.2.1 hρ1 hγρ)
    rw [f2, hfm_glA_fixP hβ hB.2.1 hρ1 (hβσ.trans hB.2.2.1) (hfix hB.2.1 hρ1 hγρ) (Q.Fr_gt hB.2.1 hρ1 hγρ)
      (Q.Fr_lt1 hB.2.1 hρ1 hγρ), hfm_glA_fixP hβ hB.1 hσ1 hβσ (hfix hB.1 hσ1 hγ) (Q.Fr_gt hB.1 hσ1 hγ)
      (Q.Fr_lt1 hB.1 hσ1 hγ)] at h
    exact h

theorem down_F {β : Ordinal.{0}} (hβ : HfLvl β) (hβμ : β < μ) : (Q.down hβ hβμ).F = Q.F := rfl

theorem down_down {β β' : Ordinal.{0}} (hβ : HfLvl β) (hβ' : HfLvl β') (hββ' : β < β') (hβ'μ : β' < μ) :
    (Q.down hβ' hβ'μ).down hβ hββ' = Q.down hβ (hββ'.trans hβ'μ) := rfl

end HfQ

/-- **The stage at a pseudo-base of level `μ`** (the stage at it as a level-`ω` pseudo-base). -/
noncomputable abbrev hfQPB {μ : Ordinal.{0}} (Q : HfQ μ) : HcPB := hdPB Q.toP

theorem hfQPB_down {μ β : Ordinal.{0}} (Q : HfQ μ) (hβ : HfLvl β) (hβμ : β < μ) :
    hfQPB (Q.down hβ hβμ) = hfQPB Q := rfl

/-! ## Bases of level `μ` -/

/-- **A base of level `μ` WITH TWO GATES**: a fixed point `F` of `φ(μ, ·)`, a CODE GATE `γ` (the gate of the code
`F`: membership and the code-gate conditions of `[F, N_μ(F))`) and a READING GATE `γN ≥ max(γ, μ)` (the reading
`F(x)`, a fixed point of `φ(μ, ·)`, and `N_μ(F(x))` above it), an outer low field `Z_o` above `N_μ(F(x))`. -/
structure HfB (μ : Ordinal.{0}) where
  F : Ordinal.{0}
  Fr : Ordinal.{0} → Ordinal.{0}
  γ : Ordinal.{0}
  γN : Ordinal.{0}
  Zo : Ordinal.{0} → Ordinal.{0}
  lv : HfLvl μ
  γ_le : γ ≤ γN
  lvN : μ ≤ γN
  γN_lt : γN < Om1
  F_fix : veblen μ F = F
  G_le : gcG 0 ≤ F
  N_lt1 : hcN μ F < gcG 1
  F_mem : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → γ < b → F ∈ S.CSet a b
  N_mem : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → γN < b → hcN μ F ∈ S.CSet a b
  F_code : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y, GxCl Z {gcG 0} y → F ≤ y → y < hcN μ F →
    GxCl Z {gcG 0} F
  F_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y, GxCl Z {gcG 0} y → F ≤ y → y < hcN μ F → γ < Z
  N_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z {gcG 0} (hcN μ F) → γN < Z
  γN_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → γ < Z → μ < Z → γN < Z
  Fr_gt : ∀ {x}, InE x → x < Om1 → γN < x → x < Fr x
  Fr_fix : ∀ {x}, InE x → x < Om1 → γN < x → veblen μ (Fr x) = Fr x
  N_Zo : ∀ {x}, InE x → x < Om1 → γN < x → hcN μ (Fr x) < Zo x
  Zo_fix : ∀ x, veblen 2 (Zo x) = Zo x
  Zo_BR : ∀ x, InE x → x < Om1 → Zo x ≤ hcBR x
  Fr_pi : ∀ {σ ρ}, Bases σ ρ → γN < σ → Fr ρ ∈ TB ρ σ ∧ pi σ ρ (Fr ρ) = Fr σ
  N_pi : ∀ {σ ρ}, Bases σ ρ → γN < σ → hcN μ (Fr ρ) ∈ TB ρ σ ∧ pi σ ρ (hcN μ (Fr ρ)) = hcN μ (Fr σ)

namespace HfB

variable {μ : Ordinal.{0}} (A : HfB μ)

open Classical in
/-- **The low field of `A`**: `N_μ(F(x))` above `γ`, `Z_o(x)` at or below it. -/
noncomputable def Zl (x : Ordinal.{0}) : Ordinal.{0} := if A.γN < x then hcN μ (A.Fr x) else A.Zo x

theorem Zl_eq {x : Ordinal.{0}} (h : A.γN < x) : A.Zl x = hcN μ (A.Fr x) := by unfold HfB.Zl; rw [if_pos h]

theorem Zl_low {x : Ordinal.{0}} (h : ¬ A.γN < x) : A.Zl x = A.Zo x := by unfold HfB.Zl; rw [if_neg h]

theorem Zl_le_Zo (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : A.Zl x ≤ A.Zo x := by
  unfold HfB.Zl; split_ifs with h
  · exact (A.N_Zo hx hx1 h).le
  · exact le_rfl

theorem Zl_BR (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : A.Zl x ≤ hcBR x :=
  (A.Zl_le_Zo x hx hx1).trans (A.Zo_BR x hx hx1)

theorem Zl_fix (x : Ordinal.{0}) : veblen 2 (A.Zl x) = A.Zl x := by
  unfold HfB.Zl; split_ifs
  · exact hc_fix_down A.lv.two_lt.le (hcN_fix μ _)
  · exact A.Zo_fix x

theorem γ_lt : A.γ < Om1 := A.γ_le.trans_lt A.γN_lt

theorem F_E : InE A.F := hc_fix_E A.F_fix

theorem N_E : InE (hcN μ A.F) := hcN_E _ _

theorem F_lt_N : A.F < hcN μ A.F := hcN_gt _ _

theorem N_lim : IsSuccLimit (hcN μ A.F) := hcN_lim _ _

theorem Fr_lt_N (x : Ordinal.{0}) : A.Fr x < hcN μ (A.Fr x) := hcN_gt _ _

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : A.γN < x)
include hx hx1 hγ

theorem N_lt1x : hcN μ (A.Fr x) < gq 1 x :=
  ((A.N_Zo hx hx1 hγ).trans_le (A.Zo_BR x hx hx1)).trans (hcBR_lt1 hx hx1)

theorem Fr_lt1 : A.Fr x < gq 1 x := (A.Fr_lt_N x).trans (A.N_lt1x hx hx1 hγ)

/-- **`ϑˣ(Ω₁·μ + F(x)) = hdNx μ (F(x))`.** -/
theorem Fr_glA : glA μ (A.Fr x) x = hdNx μ (A.Fr x) :=
  hfm_glA_fixP A.lv hx hx1 (A.lvN.trans_lt hγ) (A.Fr_fix hx hx1 hγ) (A.Fr_gt hx hx1 hγ) (A.Fr_lt1 hx hx1 hγ)

theorem t1_lt1 {r : Ordinal.{0}} (hr : r < hcN μ (A.Fr x)) : A.Fr x + r + 1 < gq 1 x := by
  have hNE := hcN_E μ (A.Fr x)
  exact ((ev_isSuccLimit_of_inE hNE).add_one_lt ((inE_indec hNE).add_lt (A.Fr_lt_N x) hr)).trans
    (A.N_lt1x hx hx1 hγ)

theorem t_lt1 {r : Ordinal.{0}} (hr : r < hcN μ (A.Fr x)) : A.Fr x + r < gq 1 x :=
  (lt_add_one _).trans (A.t1_lt1 hx hx1 hγ hr)

/-- **`ϑˣ(Ω₁·μ + F(x) + r) < N_μ(F(x))`** for `r < N_μ(F(x))`. -/
theorem glA_lt_N {r : Ordinal.{0}} (hr : r < hcN μ (A.Fr x)) : glA μ (A.Fr x + r) x < hcN μ (A.Fr x) :=
  hfm_glA_lt A.lv hx hx1 (A.lvN.trans_lt hγ) (A.Fr_glA hx hx1 hγ) (A.Fr_lt1 hx hx1 hγ) (A.N_lt1x hx hx1 hγ) hr

end Base

theorem j_lt {l : Ordinal.{0}} (hl : l < hcN μ A.F) : A.F + 1 + l < veblen μ (A.F + 1 + l) := by
  set y := A.F + 1 + l with hy
  have hyN : y < hcN μ A.F := (inE_indec A.N_E).add_lt (A.N_lim.add_one_lt A.F_lt_N) hl
  rcases (right_le_veblen μ y).lt_or_eq with h | h
  · exact h
  · exfalso
    have hFy : A.F < y := (lt_add_one _).trans_le le_self_add
    exact absurd (hcN_le h.symm hFy) (not_le.2 hyN)

theorem add_lt_N {l : Ordinal.{0}} (hl : l < hcN μ A.F) : A.F + 1 + l < hcN μ A.F :=
  (inE_indec A.N_E).add_lt (A.N_lim.add_one_lt A.F_lt_N) hl

theorem j1_lt {l : Ordinal.{0}} (hl : l < hcN μ A.F) : A.F + 1 + l + 1 < veblen μ (A.F + 1 + l + 1) := by
  have h := A.j_lt (A.N_lim.add_one_lt hl)
  rwa [← add_assoc] at h

theorem lt_Q {l : Ordinal.{0}} (hl : l < hcN μ A.F) : l < veblen μ (A.F + 1 + l) :=
  le_add_self.trans_lt (A.j_lt hl)

theorem Q_lt_N {l : Ordinal.{0}} (hl : l < hcN μ A.F) : veblen μ (A.F + 1 + l) < hcN μ A.F := by
  have h := (isNormal_veblen μ).strictMono (A.add_lt_N hl)
  rwa [hcN_fix] at h

theorem Q1_lt_N {l : Ordinal.{0}} (hl : l < hcN μ A.F) : veblen μ (A.F + 1 + l + 1) < hcN μ A.F := by
  have h := A.Q_lt_N (A.N_lim.add_one_lt hl)
  rwa [← add_assoc] at h

theorem G_lt_Q (l : Ordinal.{0}) : gcG 0 < veblen μ (A.F + 1 + l) :=
  A.G_le.trans_lt (((lt_add_one _).trans_le le_self_add).trans_le (right_le_veblen _ _))

theorem Q_lt_Q {ν l : Ordinal.{0}} (h : ν < l) : veblen μ (A.F + 1 + ν) < veblen μ (A.F + 1 + l) :=
  (isNormal_veblen _).strictMono ((add_lt_add_iff_left _).2 h)

theorem cover {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlN : l < hcN μ A.F) :
    ∃ ν, ν < l ∧ l < veblen μ (A.F + 1 + ν) := by
  have h := A.lt_Q hlN
  obtain ⟨t, ht, hlt⟩ := ((isNormal_veblen _).lt_iff_exists_lt (isSuccLimit_add _ hl)).1 h
  obtain ⟨d, hf, htd⟩ := (lt_add_iff hl.bot_lt.ne').1 ht
  exact ⟨d, hf, hlt.trans_le ((isNormal_veblen _).monotone htd)⟩

theorem gate_of_j (E : HcVD) {Z l : Ordinal.{0}} (hlB : l < E.B) (hlN : l < hcN μ A.F) (hZ : SC Z)
    (hZ1 : Z ≤ Om 1) (h : GxCl Z {gcG 0} (A.F + 1 + l)) : max A.γ (E.g l) < Z := by
  have hFj : A.F ≤ A.F + 1 + l := le_self_add.trans le_self_add
  have hjN := A.add_lt_N hlN
  have hF := A.F_code Z hZ hZ1 _ h hFj hjN
  have hl := hcX_cl_idx hZ hZ1 A.F_E A.G_le hF h
  have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1
  refine max_lt (A.F_cl Z hZ hZ1 _ h hFj hjN) ?_
  exact E.code_gate Z hZ1' hZ.1 (fun _ _ hu hv => hZ.isPrincipal hu hv) (fun _ _ hu hv => hZ.2 _ hu _ hv)
    {gcG 0} (fun s hs => Or.inl (Set.mem_singleton_iff.1 hs)) l hl hlB

/-- **The reading gate at `F + 1 + λ`**: a code `F + 1 + λ` over `Z` with `μ < Z` ⇒ `max(γN, g_E(λ)) < Z`. -/
theorem gate_of_jN (E : HcVD) {Z l : Ordinal.{0}} (hlB : l < E.B) (hlN : l < hcN μ A.F) (hZ : SC Z)
    (hZ1 : Z ≤ Om 1) (h : GxCl Z {gcG 0} (A.F + 1 + l)) (hμZ : μ < Z) : max A.γN (E.g l) < Z := by
  have h1 := A.gate_of_j E hlB hlN hZ hZ1 h
  exact max_lt (A.γN_cl Z hZ hZ1 (max_lt_iff.1 h1).1 hμZ) (max_lt_iff.1 h1).2

end HfB

/-! ## A pseudo-base of level `μ+1` is a base of level `μ` -/

namespace HfQ

variable {ν : Ordinal.{0}} (P : HfQ ν)

/-- **A PSEUDO-BASE OF LEVEL `μ+1` IS A BASE OF LEVEL `μ`** (`ν = μ + 1`). -/
noncomputable def toB {μ : Ordinal.{0}} (hμ : HfLvl μ) (e : ν = μ + 1) : HfB μ where
  F := P.F
  Fr := P.Fr
  γ := P.γ
  γN := P.γ
  Zo := P.Zo
  lv := hμ
  γ_le := le_rfl
  lvN := (hd_lt_of_eq e).le.trans P.γ_ge
  γN_lt := P.γ_lt
  F_fix := hc_fix_of_LuP (e ▸ P.F_P)
  G_le := P.G_lt.le
  N_lt1 := by rw [← hdNx_of_eq e]; exact P.S_lt1
  F_mem := P.F_mem
  N_mem := fun S _ _ ha hb => by rw [← hdNx_of_eq e]; exact P.S_mem S ha hb
  F_code := fun Z hZ hZ1 y hy hQy hyZ => P.F_code Z hZ hZ1 y hy hQy (by rw [hdNx_of_eq e]; exact hyZ)
  F_cl := fun Z hZ hZ1 y hy hQy hyZ => P.F_cl Z hZ hZ1 y hy hQy (by rw [hdNx_of_eq e]; exact hyZ)
  N_cl := fun Z hZ hZ1 h => P.S_cl Z hZ hZ1 (by rw [hdNx_of_eq e]; exact h)
  γN_cl := fun _ _ _ h _ => h
  Fr_gt := P.Fr_gt
  Fr_fix := fun hx hx1 hγ => hc_fix_of_LuP (e ▸ P.Fr_P hx hx1 hγ)
  N_Zo := fun hx hx1 hγ => by rw [← hdNx_of_eq e]; exact P.S_Zo hx hx1 hγ
  Zo_fix := P.Zo_fix
  Zo_BR := P.Zo_BR
  Fr_pi := P.Fr_pi
  N_pi := fun hB hγ => by rw [← hdNx_of_eq e, ← hdNx_of_eq e]; exact P.S_pi hB hγ

theorem toB_F {μ : Ordinal.{0}} (hμ : HfLvl μ) (e : ν = μ + 1) : (P.toB hμ e).F = P.F := rfl

end HfQ

/-! ## The gated offset of level `μ` -/

section Off

variable {μ : Ordinal.{0}} (A : HfB μ) (E : HcVD) (l : Ordinal.{0}) (hlB : l < E.B) (hlN : l < hcN μ A.F)
  (hZ : ∀ x, InE x → x < Om1 → E.Z x ≤ A.Zl x)

include hlB hZ in
theorem hfQOff_R_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : max A.γN (E.g l) < x) :
    E.R l x < hcN μ (A.Fr x) := by
  have h := (E.R_lt_Z x hx hx1 l hlB (max_lt_iff.1 hγ).2).trans_le (hZ x hx hx1)
  rwa [A.Zl_eq (max_lt_iff.1 hγ).1] at h

include hlB hZ in
theorem hfQOff_R1_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : max A.γN (E.g l) < x) :
    E.R l x + 1 < hcN μ (A.Fr x) :=
  (hcN_lim _ _).add_one_lt (hfQOff_R_lt A E l hlB hZ hx hx1 hγ)

include hlB in
theorem hfQOff_t_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hγ : max A.γN (E.g l) < σ) :
    A.Fr ρ + E.R l ρ ∈ TB ρ σ ∧ pi σ ρ (A.Fr ρ + E.R l ρ) = A.Fr σ + E.R l σ := by
  obtain ⟨f1, f2⟩ := A.Fr_pi hB (max_lt_iff.1 hγ).1
  obtain ⟨e1, e2⟩ := E.ex σ ρ hB l hlB (max_lt_iff.1 hγ).2
  obtain ⟨s1, s2⟩ := pi_add hB f1 e1
  rw [f2, e2] at s2
  exact ⟨s1, s2⟩

include hlB hZ in
theorem hfQOff_glA_pi {σ ρ s : Ordinal.{0}} (hB : Bases σ ρ) (hγ : max A.γN (E.g l) < σ) (hsσ : s < σ) :
    glA μ (A.Fr ρ + E.R l ρ + s) ρ ∈ TB ρ σ ∧
      pi σ ρ (glA μ (A.Fr ρ + E.R l ρ + s) ρ) = glA μ (A.Fr σ + E.R l σ + s) σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hγρ : max A.γN (E.g l) < ρ := hγ.trans hB.2.2.1
  obtain ⟨t1, t2⟩ := hfQOff_t_pi A E l hlB hB hγ
  obtain ⟨u1, u2⟩ := pi_add hB t1 (mem_TB_of_lt hB hsσ)
  rw [t2, pi_lt hB hsσ] at u2
  have hs1 : A.Fr ρ + E.R l ρ + s < gq 1 ρ := by
    have hq := (gm1_facts hB.2.1 hρ1).2.2.2
    exact (inE_indec hq).add_lt (A.t_lt1 hB.2.1 hρ1 (max_lt_iff.1 hγρ).1
      (hfQOff_R_lt A E l hlB hZ hB.2.1 hρ1 hγρ)) (hsσ.trans (hB.2.2.1.trans (gm1_facts hB.2.1 hρ1).2.1))
  have h := hfm_glA_pi (A.lvN.trans_lt (max_lt_iff.1 hγ).1) hB u1 hs1
  rw [u2] at h
  exact h

include hlB hlN hZ in
/-- **THE GATED OFFSET OF LEVEL `μ`**: over a base `A` of level `μ`, the offset `λ` read by `E` gives the pseudo-base
`φ(μ, F + 1 + λ)` of level `μ`, reading `ϑˣ(Ω₁·μ + F(x) + λ(x))`, gate `max(γ, g_E(λ))`, outer low field `Z_l`. -/
noncomputable def hfQOff : HfQ μ where
  F := veblen μ (A.F + 1 + l)
  Fr := fun x => glA μ (A.Fr x + E.R l x) x
  γ := max A.γN (E.g l)
  Zo := A.Zl
  lv := A.lv
  γ_ge := A.lvN.trans (le_max_left _ _)
  γ_lt := max_lt A.γN_lt (E.g_lt l hlB)
  F_P := ⟨_, rfl⟩
  G_lt := A.G_lt_Q l
  S_lt1 := by rw [hdNx_veb]; exact (A.Q1_lt_N hlN).trans A.N_lt1
  F_mem := fun S _ _ ha hb => CSet.phi_mem (he_cst_mem S (A.lvN.trans (le_max_left _ _)) hb)
    (CSet.add_mem (CSet.succ_mem (A.F_mem S ha ((A.γ_le.trans (le_max_left _ _)).trans_lt hb)))
      (E.mem S _ _ ha l hlB ((le_max_right _ _).trans_lt hb)).1)
  S_mem := fun S _ _ ha hb => by
    rw [hdNx_veb]
    exact CSet.phi_mem (he_cst_mem S (A.lvN.trans (le_max_left _ _)) hb) (CSet.succ_mem
      (CSet.add_mem (CSet.succ_mem (A.F_mem S ha ((A.γ_le.trans (le_max_left _ _)).trans_lt hb)))
        (E.mem S _ _ ha l hlB ((le_max_right _ _).trans_lt hb)).1))
  F_code := fun Z hZ hZ1 _ hy hQy hyZ => by
    rw [hdNx_veb] at hyZ
    exact GxCl.phi (GxCl.small (he_cl_level A.lv.one_le A.lv.lt_Om hZ hZ1 (A.j_lt hlN) (A.G_lt_Q l) hy hQy hyZ))
      (hd_cl_lev A.lv.one_le hZ1 (A.j_lt hlN) (A.G_lt_Q l) hy hQy hyZ)
  F_cl := fun Z hZ hZ1 _ hy hQy hyZ => by
    rw [hdNx_veb] at hyZ
    exact A.gate_of_jN E hlB hlN hZ hZ1 (hd_cl_lev A.lv.one_le hZ1 (A.j_lt hlN) (A.G_lt_Q l) hy hQy hyZ)
      (he_cl_level A.lv.one_le A.lv.lt_Om hZ hZ1 (A.j_lt hlN) (A.G_lt_Q l) hy hQy hyZ)
  S_cl := fun Z hZ hZ1 h => by
    rw [hdNx_veb] at h
    have hG1 : gcG 0 < veblen μ (A.F + 1 + l + 1) := by
      have := A.G_lt_Q (l + 1); rwa [← add_assoc] at this
    have h1 := hd_cl_lev A.lv.one_le hZ1 (A.j1_lt hlN) hG1 h le_rfl
      ((isNormal_veblen μ).strictMono (lt_add_one _))
    have h2 := ha_cl_succ hZ.1 (fun s hs => by rw [Set.mem_singleton_iff.1 hs]; exact ev_isSuccLimit_of_inE gr_G_inE)
      h1 _ rfl
    exact A.gate_of_jN E hlB hlN hZ hZ1 h2 (he_cl_level A.lv.one_le A.lv.lt_Om hZ hZ1 (A.j1_lt hlN) hG1 h
      le_rfl ((isNormal_veblen μ).strictMono (lt_add_one _)))
  Fr_gt := fun hx hx1 hγ => (hfm_glA_facts A.lv hx hx1 (A.lvN.trans_lt (max_lt_iff.1 hγ).1)
    (A.t_lt1 hx hx1 (max_lt_iff.1 hγ).1 (hfQOff_R_lt A E l hlB hZ hx hx1 hγ))).1
  Fr_P := fun hx hx1 hγ => hfm_glA_P A.lv hx hx1 (A.lvN.trans_lt (max_lt_iff.1 hγ).1)
    (A.t_lt1 hx hx1 (max_lt_iff.1 hγ).1 (hfQOff_R_lt A E l hlB hZ hx hx1 hγ))
  S_Zo := fun {x} hx hx1 hγ => by
    have hA := (max_lt_iff.1 hγ).1
    have hR1 := hfQOff_R1_lt A E l hlB hZ hx hx1 hγ
    show hdNx μ (glA μ (A.Fr x + E.R l x) x) < A.Zl x
    rw [← hfm_glA_succ A.lv hx hx1 (A.lvN.trans_lt hA) (A.t1_lt1 hx hx1 hA (hfQOff_R_lt A E l hlB hZ hx hx1 hγ)),
      A.Zl_eq hA, add_assoc]
    exact A.glA_lt_N hx hx1 hA hR1
  Zo_fix := A.Zl_fix
  Zo_BR := A.Zl_BR
  Fr_pi := fun {σ ρ} hB hγ => by
    have h := hfQOff_glA_pi A E l hlB hZ hB hγ (omega0_lt_inE hB.1).pos
    rwa [add_zero, add_zero] at h
  S_pi := fun {σ ρ} hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hγρ : max A.γN (E.g l) < ρ := hγ.trans hB.2.2.1
    have h := hfQOff_glA_pi A E l hlB hZ hB hγ (one_lt_omega0.trans (omega0_lt_inE hB.1))
    rw [hfm_glA_succ A.lv hB.2.1 hρ1 (A.lvN.trans_lt (max_lt_iff.1 hγρ).1) (A.t1_lt1 hB.2.1 hρ1 (max_lt_iff.1 hγρ).1
      (hfQOff_R_lt A E l hlB hZ hB.2.1 hρ1 hγρ)), hfm_glA_succ A.lv hB.1 hσ1 (A.lvN.trans_lt (max_lt_iff.1 hγ).1)
      (A.t1_lt1 hB.1 hσ1 (max_lt_iff.1 hγ).1
      (hfQOff_R_lt A E l hlB hZ hB.1 hσ1 hγ))] at h
    exact h

theorem hfQOff_F : (hfQOff A E l hlB hlN hZ).F = veblen μ (A.F + 1 + l) := rfl

theorem hfQOff_Fr (x : Ordinal.{0}) : (hfQOff A E l hlB hlN hZ).Fr x = glA μ (A.Fr x + E.R l x) x := rfl

theorem hfQOff_γ : (hfQOff A E l hlB hlN hZ).γ = max A.γN (E.g l) := rfl

end Off

/-! ## The specification of a step of level `μ` -/

/-- **The specification of a system `T` built from a start `U` of the stage at the pseudo-base `P` of level `μ`.** -/
structure HfQSpec {μ : Ordinal.{0}} (P : HfQ μ) (U T : HcVD) : Prop where
  B : T.B = hdNx μ P.F
  γ : T.γ = P.γ
  b : ∀ x, InE x → x < Om1 → P.γ < x → T.b x = hdNx μ (P.Fr x)
  Z : ∀ x, InE x → x < Om1 → T.Z x = if P.γ < x then evZ (hdNx μ (P.Fr x)) else P.Zo x
  extR : ∀ c x, c < U.B → T.R c x = U.R c x
  extg : ∀ c, c < U.B → T.g c = U.g c
  high : ∀ c σ, P.F ≤ c → c < hdNx μ P.F → InE σ → σ < Om1 → T.g c < σ → P.γ < σ
  RF : ∀ x, InE x → x < Om1 → P.γ < x → T.R P.F x = P.Fr x
  gF : ∀ x, InE x → x < Om1 → (T.g P.F < x ↔ P.γ < x)

/-- **The level-`ω` step at a pseudo-base of level `ω` has the specification of level `ω`.** -/
theorem hfQ_spec_om (P : HfQ ω) (U : HcVD) (h : HcSStart (hfQPB P) U) :
    HfQSpec P U (hdStep P.toP U h) := by
  have hs := hdStep_spec P.toP U h
  exact ⟨by rw [hs.B, hdNx_om]; rfl, hs.γ, fun x hx hx1 hγ => by rw [hs.b x hx hx1 hγ, hdNx_om]; rfl,
    fun x hx hx1 => by rw [hs.Z x hx hx1, hdNx_om]; rfl, hs.extR, hs.extg,
    fun c σ hFc hc hσ hσ1 hg => hs.high c σ hFc (by rw [← hdNx_om]; exact hc) hσ hσ1 hg, hs.RF, hs.gF⟩

end Googology.Trans.PoR.InaccPsi.R2.Hf
