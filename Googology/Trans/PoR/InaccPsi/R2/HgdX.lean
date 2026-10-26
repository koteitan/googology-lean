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
import Googology.Trans.PoR.InaccPsi.R2.HdLev

/-!
# HgdX: BASES OF LEVEL `ω`, PSEUDO-BASES OF EVERY FINITE LEVEL, AND THE GATED OFFSET `φ(ω, F + 1 + λ)`

(Textual copy of `Hd.HdX` for `Hg.HgVD`: bound fields `< Γ_{x+2}` in place of `≤ B_x(x)` (`Hc.hcBR`); the proofs
are unchanged except where the bound enters.  Names: prefix `hg`/`Hg` (from `hc`/`Hc`), `hgd`/`Hgd` (from `hd`/`Hd`),
`hgf`/`Hgf` (from `hf`/`Hf`), `hge`/`Hge` (from `he`/`He`).)

A base of level `ω` (`HgdA`) is a fixed point `F` of `φ(ω, ·)` (a code, `G ≤ F`) with a reading `F(x)` above a gate
`γ` (a fixed point of `φ(ω, ·)` above `x`), Lemma EXACT for `F(ρ)` and `N_ω(F(ρ))`, the code-gate conditions of
`[F, N_ω(F))`, and an outer low field `Z_o(x)` above `N_ω(F(x))`.  Its low field is `Z_l(x) = N_ω(F(x))` above `γ`,
`Z_o(x)` below.

A level-`ω` pseudo-base (`HgdP`) is a common fixed point `F` of every `φ(k, ·)`, `k < ω`, `G < F`, with a reading
`F(x)` (a common fixed point above `x`), Lemma EXACT for `F(ρ)` and `hcS(F(ρ))`, the code-gate conditions of
`[F, hcS(F))` and an outer low field above `hcS(F(x))`.  `HgdP.toX j` is the same object as a pseudo-base of level
`j+1` (`Hg.HgX j`), with `(toX (j+1)).down = toX j` by definition.

**THE GATED OFFSET** (`hgdOff A E λ`): over a base `A` of level `ω` and an offset `λ < N_ω(F)` read by a system `E`
whose bound field lies below `Z_l`, the point `Q_λ = φ(ω, F + 1 + λ)` is a level-`ω` pseudo-base with reading
`ϑˣ(Ω₁·ω + F(x) + λ(x))`, gate `max(γ, g_E(λ))` and outer low field `Z_l` of `A`.

* `HgdA`, `HgdA.Zl` and its facts, `HgdA.Fr_glA`, `HgdA.j_lt`, `HgdA.Q_lt_N`, `HgdA.cover`, `HgdA.gate_of_j`;
* `HgdP`, `HgdP.toX` (**A LEVEL-`ω` PSEUDO-BASE IS A PSEUDO-BASE OF EVERY FINITE LEVEL**), `HgdP.toX_down`, `hgdPB`;
* `hgdOff` (**THE GATED OFFSET OF LEVEL `ω`**), `hgdOff_F`, `hgdOff_Fr`, `hgdOff_γ`, `hgdOff_Zo`.

No new axiom.  New definitions: `HgdA`, `HgdA.Zl`, `HgdP`, `HgdP.toX`, `hgdPB`, `hgdOff`.
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

/-! ## Bases of level `ω` -/

/-- **A base of level `ω`**: a fixed point `F` of `φ(ω, ·)`, its reading `F(x)` above the gate `γ`, an outer low
field `Z_o`. -/
structure HgdA where
  F : Ordinal.{0}
  Fr : Ordinal.{0} → Ordinal.{0}
  γ : Ordinal.{0}
  Zo : Ordinal.{0} → Ordinal.{0}
  γ_lt : γ < Om1
  F_fix : veblen ω F = F
  G_le : gcG 0 ≤ F
  N_lt1 : hcNw F < gcG 1
  F_mem : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → γ < b → F ∈ S.CSet a b
  N_mem : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → γ < b → hcNw F ∈ S.CSet a b
  F_code : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y, GxCl Z {gcG 0} y → F ≤ y → y < hcNw F →
    GxCl Z {gcG 0} F
  F_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y, GxCl Z {gcG 0} y → F ≤ y → y < hcNw F → γ < Z
  N_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z {gcG 0} (hcNw F) → γ < Z
  Fr_gt : ∀ {x}, InE x → x < Om1 → γ < x → x < Fr x
  Fr_fix : ∀ {x}, InE x → x < Om1 → γ < x → veblen ω (Fr x) = Fr x
  N_Zo : ∀ {x}, InE x → x < Om1 → γ < x → hcNw (Fr x) < Zo x
  Zo_fix : ∀ x, veblen 2 (Zo x) = Zo x
  Zo_G1 : ∀ x, InE x → x < Om1 → Zo x < gq 1 x
  Fr_pi : ∀ {σ ρ}, Bases σ ρ → γ < σ → Fr ρ ∈ TB ρ σ ∧ pi σ ρ (Fr ρ) = Fr σ
  N_pi : ∀ {σ ρ}, Bases σ ρ → γ < σ → hcNw (Fr ρ) ∈ TB ρ σ ∧ pi σ ρ (hcNw (Fr ρ)) = hcNw (Fr σ)

namespace HgdA

variable (A : HgdA)

open Classical in
/-- **The low field of `A`**: `N_ω(F(x))` above `γ`, `Z_o(x)` at or below it. -/
noncomputable def Zl (x : Ordinal.{0}) : Ordinal.{0} := if A.γ < x then hcNw (A.Fr x) else A.Zo x

theorem Zl_eq {x : Ordinal.{0}} (h : A.γ < x) : A.Zl x = hcNw (A.Fr x) := by unfold HgdA.Zl; rw [if_pos h]

theorem Zl_low {x : Ordinal.{0}} (h : ¬ A.γ < x) : A.Zl x = A.Zo x := by unfold HgdA.Zl; rw [if_neg h]

theorem Zl_le_Zo (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : A.Zl x ≤ A.Zo x := by
  unfold HgdA.Zl; split_ifs with h
  · exact (A.N_Zo hx hx1 h).le
  · exact le_rfl

theorem Zl_G1 (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : A.Zl x < gq 1 x :=
  (A.Zl_le_Zo x hx hx1).trans_lt (A.Zo_G1 x hx hx1)

theorem Zl_fix (x : Ordinal.{0}) : veblen 2 (A.Zl x) = A.Zl x := by
  unfold HgdA.Zl; split_ifs
  · exact hdNw_fix2 _
  · exact A.Zo_fix x

theorem F_E : InE A.F := hc_fixW_E A.F_fix

theorem N_E : InE (hcNw A.F) := hcNw_E _

theorem F_lt_N : A.F < hcNw A.F := hcNw_gt _

theorem N_lim : IsSuccLimit (hcNw A.F) := hcNw_lim _

theorem Fr_lt_N (x : Ordinal.{0}) : A.Fr x < hcNw (A.Fr x) := hcNw_gt _

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : A.γ < x)
include hx hx1 hγ

theorem N_lt1x : hcNw (A.Fr x) < gq 1 x :=
  (A.N_Zo hx hx1 hγ).trans (A.Zo_G1 x hx hx1)

theorem Fr_lt1 : A.Fr x < gq 1 x := (A.Fr_lt_N x).trans (A.N_lt1x hx hx1 hγ)

/-- **`ϑˣ(Ω₁·ω + F(x)) = hcS(F(x))`.** -/
theorem Fr_glA : glA ω (A.Fr x) x = hcS (A.Fr x) :=
  hc_glA_fixW hx hx1 (A.Fr_fix hx hx1 hγ) (A.Fr_gt hx hx1 hγ) (A.Fr_lt1 hx hx1 hγ)

/-- **`R < N_ω(F(x))` ⇒ the offset term `F(x) + R + 1` lies below `Γ_{x+2}`.** -/
theorem t1_lt1 {r : Ordinal.{0}} (hr : r < hcNw (A.Fr x)) : A.Fr x + r + 1 < gq 1 x := by
  have hNE := hcNw_E (A.Fr x)
  exact ((ev_isSuccLimit_of_inE hNE).add_one_lt ((inE_indec hNE).add_lt (A.Fr_lt_N x) hr)).trans
    (A.N_lt1x hx hx1 hγ)

theorem t_lt1 {r : Ordinal.{0}} (hr : r < hcNw (A.Fr x)) : A.Fr x + r < gq 1 x :=
  (lt_add_one _).trans (A.t1_lt1 hx hx1 hγ hr)

/-- **`ϑˣ(Ω₁·ω + F(x) + r) < N_ω(F(x))`** for `r < N_ω(F(x))`. -/
theorem glA_lt_N {r : Ordinal.{0}} (hr : r < hcNw (A.Fr x)) : glA ω (A.Fr x + r) x < hcNw (A.Fr x) :=
  hd_glA_lt hx hx1 (A.Fr_glA hx hx1 hγ) (A.Fr_lt1 hx hx1 hγ) (A.N_lt1x hx hx1 hγ) hr

end Base

/-- **`F + 1 + λ` is not a fixed point of `φ(ω, ·)`** for `λ < N_ω(F)`. -/
theorem j_lt {l : Ordinal.{0}} (hl : l < hcNw A.F) : A.F + 1 + l < veblen ω (A.F + 1 + l) := by
  set y := A.F + 1 + l with hy
  have hyN : y < hcNw A.F := (inE_indec A.N_E).add_lt (A.N_lim.add_one_lt A.F_lt_N) hl
  rcases (right_le_veblen ω y).lt_or_eq with h | h
  · exact h
  · exfalso
    have hFy : A.F < y := (lt_add_one _).trans_le le_self_add
    exact absurd (hcNw_le h.symm hFy) (not_le.2 hyN)

theorem add_lt_N {l : Ordinal.{0}} (hl : l < hcNw A.F) : A.F + 1 + l < hcNw A.F :=
  (inE_indec A.N_E).add_lt (A.N_lim.add_one_lt A.F_lt_N) hl

/-- **`F + 1 + λ + 1` is not a fixed point of `φ(ω, ·)`** for `λ < N_ω(F)`. -/
theorem j1_lt {l : Ordinal.{0}} (hl : l < hcNw A.F) : A.F + 1 + l + 1 < veblen ω (A.F + 1 + l + 1) := by
  have h := A.j_lt (A.N_lim.add_one_lt hl)
  rwa [← add_assoc] at h

theorem lt_Q {l : Ordinal.{0}} (hl : l < hcNw A.F) : l < veblen ω (A.F + 1 + l) :=
  le_add_self.trans_lt (A.j_lt hl)

theorem Q_lt_N {l : Ordinal.{0}} (hl : l < hcNw A.F) : veblen ω (A.F + 1 + l) < hcNw A.F := by
  have h := (isNormal_veblen ω).strictMono (A.add_lt_N hl)
  rwa [hcNw_fix] at h

theorem Q1_lt_N {l : Ordinal.{0}} (hl : l < hcNw A.F) : veblen ω (A.F + 1 + l + 1) < hcNw A.F := by
  have h := A.Q_lt_N (A.N_lim.add_one_lt hl)
  rwa [← add_assoc] at h

theorem G_lt_Q (l : Ordinal.{0}) : gcG 0 < veblen ω (A.F + 1 + l) :=
  A.G_le.trans_lt (((lt_add_one _).trans_le le_self_add).trans_le (right_le_veblen _ _))

theorem Q_lt_Q {μ l : Ordinal.{0}} (h : μ < l) : veblen ω (A.F + 1 + μ) < veblen ω (A.F + 1 + l) :=
  (isNormal_veblen _).strictMono ((add_lt_add_iff_left _).2 h)

/-- **A limit `λ < N_ω(F)` lies below `Q_μ` for some `μ < λ`.** -/
theorem cover {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlN : l < hcNw A.F) :
    ∃ μ, μ < l ∧ l < veblen ω (A.F + 1 + μ) := by
  have h := A.lt_Q hlN
  obtain ⟨t, ht, hlt⟩ := ((isNormal_veblen _).lt_iff_exists_lt (isSuccLimit_add _ hl)).1 h
  obtain ⟨d, hd, htd⟩ := (lt_add_iff hl.bot_lt.ne').1 ht
  exact ⟨d, hd, hlt.trans_le ((isNormal_veblen _).monotone htd)⟩

/-- **The code-gate condition at `F + 1 + λ`**: a code `F + 1 + λ` over `Z` ⇒ `max(γ, g_E(λ)) < Z`. -/
theorem gate_of_j (E : HgVD) {Z l : Ordinal.{0}} (hlB : l < E.B) (hlN : l < hcNw A.F) (hZ : SC Z)
    (hZ1 : Z ≤ Om 1) (h : GxCl Z {gcG 0} (A.F + 1 + l)) : max A.γ (E.g l) < Z := by
  have hFj : A.F ≤ A.F + 1 + l := le_self_add.trans le_self_add
  have hjN := A.add_lt_N hlN
  have hF := A.F_code Z hZ hZ1 _ h hFj hjN
  have hl := hgX_cl_idx hZ hZ1 A.F_E A.G_le hF h
  have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1
  refine max_lt (A.F_cl Z hZ hZ1 _ h hFj hjN) ?_
  exact E.code_gate Z hZ1' hZ.1 (fun _ _ hu hv => hZ.isPrincipal hu hv) (fun _ _ hu hv => hZ.2 _ hu _ hv)
    {gcG 0} (fun s hs => Or.inl (Set.mem_singleton_iff.1 hs)) l hl hlB

end HgdA

/-! ## Level-`ω` pseudo-bases -/

/-- **A level-`ω` pseudo-base**: a common fixed point `F` of every `φ(k, ·)`, `k < ω`, `G < F`, its reading `F(x)`
above the gate `γ`, an outer low field `Z_o` above `hcS(F(x))`. -/
structure HgdP where
  F : Ordinal.{0}
  Fr : Ordinal.{0} → Ordinal.{0}
  γ : Ordinal.{0}
  Zo : Ordinal.{0} → Ordinal.{0}
  γ_lt : γ < Om1
  F_fix : ∀ k : ℕ, veblen (k : Ordinal.{0}) F = F
  G_lt : gcG 0 < F
  S_lt1 : hcS F < gcG 1
  F_mem : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → γ < b → F ∈ S.CSet a b
  S_mem : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → γ < b → hcS F ∈ S.CSet a b
  F_code : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y, GxCl Z {gcG 0} y → F ≤ y → y < hcS F → GxCl Z {gcG 0} F
  F_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y, GxCl Z {gcG 0} y → F ≤ y → y < hcS F → γ < Z
  S_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z {gcG 0} (hcS F) → γ < Z
  Fr_gt : ∀ {x}, InE x → x < Om1 → γ < x → x < Fr x
  Fr_fix : ∀ {x}, InE x → x < Om1 → γ < x → ∀ k : ℕ, veblen (k : Ordinal.{0}) (Fr x) = Fr x
  S_Zo : ∀ {x}, InE x → x < Om1 → γ < x → hcS (Fr x) < Zo x
  Zo_fix : ∀ x, veblen 2 (Zo x) = Zo x
  Zo_G1 : ∀ x, InE x → x < Om1 → Zo x < gq 1 x
  Fr_pi : ∀ {σ ρ}, Bases σ ρ → γ < σ → Fr ρ ∈ TB ρ σ ∧ pi σ ρ (Fr ρ) = Fr σ
  S_pi : ∀ {σ ρ}, Bases σ ρ → γ < σ → hcS (Fr ρ) ∈ TB ρ σ ∧ pi σ ρ (hcS (Fr ρ)) = hcS (Fr σ)

namespace HgdP

variable (P : HgdP)

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : P.γ < x)
include hx hx1 hγ

theorem S_lt_G1 : hcS (P.Fr x) < gq 1 x := (P.S_Zo hx hx1 hγ).trans (P.Zo_G1 x hx hx1)

theorem Fr_lt1 : P.Fr x < gq 1 x := (hcS_gt _).trans (P.S_lt_G1 hx hx1 hγ)

end Base

/-- **`N_{j+1}(F) = φ(j+2, F+1)`.** -/
theorem N_eq (j : ℕ) : hbN (j + 1) P.F = veblen ((j + 1 + 1 : ℕ) : Ordinal.{0}) (P.F + 1) := by
  have := hbN_veb (j + 1) P.F; rwa [P.F_fix (j + 1 + 1)] at this

/-- **A LEVEL-`ω` PSEUDO-BASE IS A PSEUDO-BASE OF LEVEL `j+1`.** -/
noncomputable def toX (j : ℕ) : HgX j where
  F := P.F
  Fr := P.Fr
  γ := P.γ
  Zo := P.Zo
  γ_lt := P.γ_lt
  F_fix := P.F_fix (j + 1)
  G_le := P.G_lt.le
  N_lt1 := (hbN_lt_S (j + 1) P.F).trans P.S_lt1
  F_mem := P.F_mem
  N_mem := fun S _ _ ha hb => by
    rw [P.N_eq j]
    exact CSet.phi_mem (hgX_nat_mem S ha _ _) (CSet.succ_mem (P.F_mem S ha hb))
  F_code := fun Z hZ hZ1 y hy hQy hyZ => P.F_code Z hZ hZ1 y hy hQy (hyZ.trans (hbN_lt_S _ _))
  F_cl := fun Z hZ hZ1 y hy hQy hyZ => P.F_cl Z hZ hZ1 y hy hQy (hyZ.trans (hbN_lt_S _ _))
  N_cl := fun Z hZ hZ1 h => by
    rw [P.N_eq j] at h
    exact P.F_cl Z hZ hZ1 _ (hgX_cl_succ_fix (j + 1) hZ hZ1 P.G_lt.le h) le_rfl (hcS_gt _)
  Fr_gt := P.Fr_gt
  Fr_glA := fun hx hx1 hγ => hb_glA_fixP hx hx1 j (P.Fr_fix hx hx1 hγ (j + 1)) (P.Fr_gt hx hx1 hγ)
    (P.Fr_lt1 hx hx1 hγ)
  N_Zo := fun hx hx1 hγ => (hbN_lt_S (j + 1) _).trans (P.S_Zo hx hx1 hγ)
  Zo_fix := P.Zo_fix
  Zo_G1 := P.Zo_G1
  Fr_pi := P.Fr_pi
  N_pi := fun {σ ρ} hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hγρ : P.γ < ρ := hγ.trans hB.2.2.1
    have hkσ : ((j + 1 + 1 : ℕ) : Ordinal.{0}) < σ := (natCast_lt_omega0 _).trans (omega0_lt_inE hB.1)
    obtain ⟨f1, f2⟩ := P.Fr_pi hB hγ
    have h := glA_pi hB (mem_TB_of_lt hB hkσ) (hb_lev_T hB.2.1 hρ1 (j + 1 + 1)).2 f1
      (gm1_T hB.2.1 hρ1 (P.Fr_lt1 hB.2.1 hρ1 hγρ)).2
    rw [pi_lt hB hkσ, f2, hb_glA_fixP hB.2.1 hρ1 (j + 1) (P.Fr_fix hB.2.1 hρ1 hγρ (j + 1 + 1))
      (P.Fr_gt hB.2.1 hρ1 hγρ) (P.Fr_lt1 hB.2.1 hρ1 hγρ), hb_glA_fixP hB.1 hσ1 (j + 1)
      (P.Fr_fix hB.1 hσ1 hγ (j + 1 + 1)) (P.Fr_gt hB.1 hσ1 hγ) (P.Fr_lt1 hB.1 hσ1 hγ)] at h
    exact h
  G_lt := P.G_lt
  Fr_fix := fun hx hx1 hγ => P.Fr_fix hx hx1 hγ (j + 1)

theorem toX_down (j : ℕ) : (P.toX (j + 1)).down = P.toX j := rfl

theorem toX_PB (j : ℕ) : hgXPB (P.toX j) = hgXPB (P.toX 0) := rfl

end HgdP

/-- **The stage at a level-`ω` pseudo-base.** -/
noncomputable abbrev hgdPB (P : HgdP) : HgPB := hgXPB (P.toX 0)

/-! ## The gated offset of level `ω` -/

section Off

variable (A : HgdA) (E : HgVD) (l : Ordinal.{0}) (hlB : l < E.B) (hlN : l < hcNw A.F)
  (hZ : ∀ x, InE x → x < Om1 → E.Z x ≤ A.Zl x)

include hlB hZ in
theorem hgdOff_R_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : max A.γ (E.g l) < x) :
    E.R l x < hcNw (A.Fr x) := by
  have h := (E.R_lt_Z x hx hx1 l hlB (max_lt_iff.1 hγ).2).trans_le (hZ x hx hx1)
  rwa [A.Zl_eq (max_lt_iff.1 hγ).1] at h

include hlB hZ in
theorem hgdOff_R1_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : max A.γ (E.g l) < x) :
    E.R l x + 1 < hcNw (A.Fr x) :=
  (hcNw_lim _).add_one_lt (hgdOff_R_lt A E l hlB hZ hx hx1 hγ)

include hlB in
theorem hgdOff_t_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hγ : max A.γ (E.g l) < σ) :
    A.Fr ρ + E.R l ρ ∈ TB ρ σ ∧ pi σ ρ (A.Fr ρ + E.R l ρ) = A.Fr σ + E.R l σ := by
  obtain ⟨f1, f2⟩ := A.Fr_pi hB (max_lt_iff.1 hγ).1
  obtain ⟨e1, e2⟩ := E.ex σ ρ hB l hlB (max_lt_iff.1 hγ).2
  obtain ⟨s1, s2⟩ := pi_add hB f1 e1
  rw [f2, e2] at s2
  exact ⟨s1, s2⟩

include hlB hZ in
theorem hgdOff_glA_pi {σ ρ s : Ordinal.{0}} (hB : Bases σ ρ) (hγ : max A.γ (E.g l) < σ) (hsσ : s < σ) :
    glA ω (A.Fr ρ + E.R l ρ + s) ρ ∈ TB ρ σ ∧
      pi σ ρ (glA ω (A.Fr ρ + E.R l ρ + s) ρ) = glA ω (A.Fr σ + E.R l σ + s) σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hγρ : max A.γ (E.g l) < ρ := hγ.trans hB.2.2.1
  have hωσ : ω < σ := omega0_lt_inE hB.1
  obtain ⟨t1, t2⟩ := hgdOff_t_pi A E l hlB hB hγ
  obtain ⟨u1, u2⟩ := pi_add hB t1 (mem_TB_of_lt hB hsσ)
  rw [t2, pi_lt hB hsσ] at u2
  have hs1 : A.Fr ρ + E.R l ρ + s < gq 1 ρ := by
    have hq := (gm1_facts hB.2.1 hρ1).2.2.2
    exact (inE_indec hq).add_lt (A.t_lt1 hB.2.1 hρ1 (max_lt_iff.1 hγρ).1
      (hgdOff_R_lt A E l hlB hZ hB.2.1 hρ1 hγρ)) (hsσ.trans (hB.2.2.1.trans (gm1_facts hB.2.1 hρ1).2.1))
  have h := glA_pi hB (mem_TB_of_lt hB hωσ) (hc_om_T hB.2.1 hρ1).2 u1 (gm1_T hB.2.1 hρ1 hs1).2
  rw [pi_lt hB hωσ, u2] at h
  exact h

include hlB hlN hZ in
/-- **THE GATED OFFSET OF LEVEL `ω`**: over a base `A` of level `ω`, the offset `λ` read by `E` gives the level-`ω`
pseudo-base `φ(ω, F + 1 + λ)`, reading `ϑˣ(Ω₁·ω + F(x) + λ(x))`, gate `max(γ, g_E(λ))`, outer low field `Z_l` of
`A`. -/
noncomputable def hgdOff : HgdP where
  F := veblen ω (A.F + 1 + l)
  Fr := fun x => glA ω (A.Fr x + E.R l x) x
  γ := max A.γ (E.g l)
  Zo := A.Zl
  γ_lt := max_lt A.γ_lt (E.g_lt l hlB)
  F_fix := fun k => hd_veb_fix k _
  G_lt := A.G_lt_Q l
  S_lt1 := by rw [hcS_veb_eq]; exact (A.Q1_lt_N hlN).trans A.N_lt1
  F_mem := fun S _ _ ha hb => CSet.phi_mem (gr_cst_mem ha _ ω (omega0_lt_gamma 1))
    (CSet.add_mem (CSet.succ_mem (A.F_mem S ha ((le_max_left _ _).trans_lt hb)))
      (E.mem S _ _ ha l hlB ((le_max_right _ _).trans_lt hb)).1)
  S_mem := fun S _ _ ha hb => by
    rw [hcS_veb_eq]
    exact CSet.phi_mem (gr_cst_mem ha _ ω (omega0_lt_gamma 1)) (CSet.succ_mem
      (CSet.add_mem (CSet.succ_mem (A.F_mem S ha ((le_max_left _ _).trans_lt hb)))
        (E.mem S _ _ ha l hlB ((le_max_right _ _).trans_lt hb)).1))
  F_code := fun Z hZ hZ1 _ hy hQy hyZ => by
    rw [hcS_veb_eq] at hyZ
    exact GxCl.phi (GxCl.small (omega0_lt_inE (Low.opow_eq_self_of_SC hZ)))
      (hd_cl_lev hc_one_le_om hZ1 (A.j_lt hlN) (A.G_lt_Q l) hy hQy hyZ)
  F_cl := fun Z hZ hZ1 _ hy hQy hyZ => by
    rw [hcS_veb_eq] at hyZ
    exact A.gate_of_j E hlB hlN hZ hZ1 (hd_cl_lev hc_one_le_om hZ1 (A.j_lt hlN) (A.G_lt_Q l) hy hQy hyZ)
  S_cl := fun Z hZ hZ1 h => by
    rw [hcS_veb_eq] at h
    have hG1 : gcG 0 < veblen ω (A.F + 1 + l + 1) := by
      have := A.G_lt_Q (l + 1); rwa [← add_assoc] at this
    have h1 := hd_cl_lev hc_one_le_om hZ1 (A.j1_lt hlN) hG1 h le_rfl
      ((isNormal_veblen ω).strictMono (lt_add_one _))
    have h2 := ha_cl_succ hZ.1 (fun s hs => by rw [Set.mem_singleton_iff.1 hs]; exact ev_isSuccLimit_of_inE gr_G_inE)
      h1 _ rfl
    exact A.gate_of_j E hlB hlN hZ hZ1 h2
  Fr_gt := fun hx hx1 hγ => (hd_glA_facts hx hx1 (A.t_lt1 hx hx1 (max_lt_iff.1 hγ).1
    (hgdOff_R_lt A E l hlB hZ hx hx1 hγ))).1
  Fr_fix := fun hx hx1 hγ k => hd_glA_fix hx hx1 k (A.t_lt1 hx hx1 (max_lt_iff.1 hγ).1
    (hgdOff_R_lt A E l hlB hZ hx hx1 hγ))
  S_Zo := fun {x} hx hx1 hγ => by
    have hA := (max_lt_iff.1 hγ).1
    have hR1 := hgdOff_R1_lt A E l hlB hZ hx hx1 hγ
    show hcS (glA ω (A.Fr x + E.R l x) x) < A.Zl x
    rw [← hd_glA_succ hx hx1 (A.t1_lt1 hx hx1 hA (hgdOff_R_lt A E l hlB hZ hx hx1 hγ)),
      A.Zl_eq hA, add_assoc]
    exact A.glA_lt_N hx hx1 hA hR1
  Zo_fix := A.Zl_fix
  Zo_G1 := A.Zl_G1
  Fr_pi := fun {σ ρ} hB hγ => by
    have h := hgdOff_glA_pi A E l hlB hZ hB hγ (omega0_lt_inE hB.1).pos
    rwa [add_zero, add_zero] at h
  S_pi := fun {σ ρ} hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hγρ : max A.γ (E.g l) < ρ := hγ.trans hB.2.2.1
    have h := hgdOff_glA_pi A E l hlB hZ hB hγ (one_lt_omega0.trans (omega0_lt_inE hB.1))
    rw [hd_glA_succ hB.2.1 hρ1 (A.t1_lt1 hB.2.1 hρ1 (max_lt_iff.1 hγρ).1
      (hgdOff_R_lt A E l hlB hZ hB.2.1 hρ1 hγρ)), hd_glA_succ hB.1 hσ1 (A.t1_lt1 hB.1 hσ1 (max_lt_iff.1 hγ).1
      (hgdOff_R_lt A E l hlB hZ hB.1 hσ1 hγ))] at h
    exact h

theorem hgdOff_F : (hgdOff A E l hlB hlN hZ).F = veblen ω (A.F + 1 + l) := rfl

theorem hgdOff_Fr (x : Ordinal.{0}) : (hgdOff A E l hlB hlN hZ).Fr x = glA ω (A.Fr x + E.R l x) x := rfl

theorem hgdOff_γ : (hgdOff A E l hlB hlN hZ).γ = max A.γ (E.g l) := rfl

theorem hgdOff_Zo : (hgdOff A E l hlB hlN hZ).Zo = A.Zl := rfl

end Off

end Googology.Trans.PoR.InaccPsi.R2.Hg
