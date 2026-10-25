import Googology.Trans.PoR.InaccPsi.R2.HcSU

/-!
# HcX: PSEUDO-BASES OF EVERY FINITE VEBLEN LEVEL

(Textual copy of `Hb.HbX` for `Hc.HcVD`: bound fields `≤ B_x(x)` (`Hc.hcBR`) in place of `≤ B_ω(x)`;
the proofs are unchanged.)

A base of level `j+1` (`HcA j`) is a fixed point `F` of `φ(j+1, ·)` (a code, `G ≤ F`) with a reading `F(x)` above a
gate `γ`, `ϑˣ(Ω₁·(j+1) + F(x)) = N_j(F(x))`, Lemma EXACT for `F(ρ)` and `N_{j+1}(F(ρ))`, the code-gate conditions of
`[F, N_{j+1}(F))` and an outer low field `Z_o(x)` above `N_{j+1}(F(x))`.  Its low field is `Z_l(x) = N_{j+1}(F(x))`
above `γ`, `Z_o(x)` below.  A pseudo-base (`HcX j`) asks moreover `G < F` and that `F(x)` is a fixed point of
`φ(j+1, ·)`; then the stage at `F` itself (`hcXPB`: `Q = F`, `P = F(x)`, low field `Z_o`) is a `Hc.HcPB`.

* `HcA`, `HcA.Zl`, `HcX`, `hcXPB` (**THE STAGE AT A PSEUDO-BASE OF ANY LEVEL**), `HcX.down` (**a pseudo-base of
  level `j+2` is one of level `j+1`**), `hcXoff` (**THE OFFSET `λ` OVER A BASE `A` OF LEVEL `j+2`, `λ` READ BY `E`**:
  the pseudo-base `φ(j+2, F + 1 + λ)` of level `j+1`, reading `ϑˣ(Ω₁·(j+2) + F(x) + λ(x))`, gate `max(γ, g_E(λ))`,
  outer low field `Z_l` of `A`);
* `hcX_glA_lt` (`ϑˣ(Ω₁·(k+1) + P + r) < N_{k+1}(P)` for `r < N_{k+1}(P)`), `hcX_cl_idx`, `hcXoff_*`.

No new axiom.  New definitions: `HcA`, `HcA.Zl`, `HcX`, `hcXPB`, `HcX.down`, `hcXoff`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hc

open Googology.Trans.PoR.InaccPsi.R2.Hb

open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## Helpers -/

theorem hcX_nat_small (k : ℕ) {Z : Ordinal.{0}} (hZ : SC Z) : (k : Ordinal.{0}) < Z :=
  (natCast_lt_omega0 k).trans (omega0_lt_inE (Low.opow_eq_self_of_SC hZ))

theorem hcX_nat_mem (S : InaccSeq.{0}) {a : Ordinal.{0}} (ha : 0 < a) (b : Ordinal.{0}) (k : ℕ) :
    (k : Ordinal.{0}) ∈ S.CSet a b :=
  gr_cst_mem ha b _ ((natCast_lt_omega0 k).trans (omega0_lt_gamma 1))

/-- **`F + 1 + λ` a code, `F` a code ⇒ `λ` a code.** -/
theorem hcX_cl_idx {Z F l : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (hFE : InE F) (hGF : gcG 0 ≤ F)
    (hF : GxCl Z {gcG 0} F) (h : GxCl Z {gcG 0} (F + 1 + l)) : GxCl Z {gcG 0} l := by
  rw [add_assoc] at h
  have h1l := gwY_cl_of_add hZ hZ1 hFE hGF hF h
  rcases lt_or_ge l ω with hlω | hlω
  · exact GxCl.small (hlω.trans (omega0_lt_inE (Low.opow_eq_self_of_SC hZ)))
  · rwa [one_add_of_omega0_le hlω] at h1l

theorem hcX_fixE {k : ℕ} {P : Ordinal.{0}} (hP : veblen (k : Ordinal.{0}) P = P) : InE P := by
  have h := hb_fix_down (Nat.zero_le k) hP
  rw [Nat.cast_zero, veblen_zero_apply] at h; exact h

theorem hcX_succ_lt (k : ℕ) (a : Ordinal.{0}) : a + 1 < veblen ((k + 1 : ℕ) : Ordinal.{0}) (a + 1) := by
  rcases (right_le_veblen ((k + 1 : ℕ) : Ordinal.{0}) (a + 1)).lt_or_eq with h | h
  · exact h
  · exfalso
    have hl : IsSuccLimit (veblen ((k + 1 : ℕ) : Ordinal.{0}) (a + 1)) :=
      ev_isSuccLimit_of_inE (gg_veblen_eps (by exact_mod_cast Nat.succ_ne_zero k))
    rw [← h, ← Order.succ_eq_add_one] at hl
    exact Order.not_isSuccLimit_succ _ hl

/-- **A fixed point `P` of `φ(k+1, ·)`, `G ≤ P`: a code in `[φ(k+1, P+1), …)` up to `φ(k+1, P+2)` forces `P` a
code.** -/
theorem hcX_cl_succ_fix (k : ℕ) {Z P : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (hGP : gcG 0 ≤ P)
    (h : GxCl Z {gcG 0} (veblen ((k + 1 : ℕ) : Ordinal.{0}) (P + 1))) : GxCl Z {gcG 0} P := by
  have hG : gcG 0 < veblen ((k + 1 : ℕ) : Ordinal.{0}) (P + 1) :=
    (hGP.trans_lt (lt_add_one P)).trans_le (right_le_veblen _ _)
  have h1 := hb_cl_lev (k := k + 1) (by omega) hZ1 (hcX_succ_lt k P) hG h le_rfl
    ((isNormal_veblen _).strictMono (lt_add_one _))
  exact ha_cl_succ hZ.1 (fun s hs => by rw [Set.mem_singleton_iff.1 hs]; exact ev_isSuccLimit_of_inE gr_G_inE)
    h1 _ rfl

section Lev

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **`ϑˣ(Ω₁·(k+1) + P + r) < N_{k+1}(P)`** for `r < N_{k+1}(P)` when `ϑˣ(Ω₁·(k+1) + P) = N_k(P)`. -/
theorem hcX_glA_lt (k : ℕ) {P r : Ordinal.{0}} (hP0 : glA ((k + 1 : ℕ) : Ordinal.{0}) P x = hbN k P)
    (hPq : P < gq 1 x) (hHq : hbN (k + 1) P < gq 1 x) (hr : r < hbN (k + 1) P) :
    glA ((k + 1 : ℕ) : Ordinal.{0}) (P + r) x < hbN (k + 1) P := by
  obtain ⟨i0, hi0⟩ := hb_LuP_of_fix k (hbN_fix k P)
  have hHE := hbN_E (k + 1) P
  have hi0H : i0 < hbN (k + 1) P :=
    (right_le_veblen _ i0).trans_lt (by rw [hi0]; exact hbN_lt_succ k P)
  have hir : i0 + r < hbN (k + 1) P := (inE_indec hHE).add_lt hi0H hr
  have hlt : veblen ((k + 1 : ℕ) : Ordinal.{0}) (i0 + r) < hbN (k + 1) P := by
    have := (isNormal_veblen ((k + 1 : ℕ) : Ordinal.{0})).strictMono hir; rwa [hbN_fix] at this
  have hrq : P + r < gq 1 x := (inE_indec (gm1_facts hx hx1).2.2.2).add_lt hPq (hr.trans hHq)
  rw [hb_glAV hx hx1 k hPq (by rw [hP0, hi0]) r hrq (fun ν' h' _ => hb_nofixV k hi0 le_self_add
    (((isNormal_veblen _).monotone ((add_le_add_iff_left _).2 h')).trans_lt hlt))]
  exact hlt

end Lev

/-! ## Bases and pseudo-bases -/

/-- **A base of level `j+1`**: a fixed point `F` of `φ(j+1, ·)`, its reading `F(x)` above the gate `γ`, an outer low
field `Z_o`. -/
structure HcA (j : ℕ) where
  F : Ordinal.{0}
  Fr : Ordinal.{0} → Ordinal.{0}
  γ : Ordinal.{0}
  Zo : Ordinal.{0} → Ordinal.{0}
  γ_lt : γ < Om1
  F_fix : veblen ((j + 1 : ℕ) : Ordinal.{0}) F = F
  G_le : gcG 0 ≤ F
  N_lt1 : hbN (j + 1) F < gcG 1
  F_mem : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → γ < b → F ∈ S.CSet a b
  N_mem : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → γ < b → hbN (j + 1) F ∈ S.CSet a b
  F_code : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y, GxCl Z {gcG 0} y → F ≤ y → y < hbN (j + 1) F →
    GxCl Z {gcG 0} F
  F_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y, GxCl Z {gcG 0} y → F ≤ y → y < hbN (j + 1) F → γ < Z
  N_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z {gcG 0} (hbN (j + 1) F) → γ < Z
  Fr_gt : ∀ {x}, InE x → x < Om1 → γ < x → x < Fr x
  Fr_glA : ∀ {x}, InE x → x < Om1 → γ < x → glA ((j + 1 : ℕ) : Ordinal.{0}) (Fr x) x = hbN j (Fr x)
  N_Zo : ∀ {x}, InE x → x < Om1 → γ < x → hbN (j + 1) (Fr x) < Zo x
  Zo_fix : ∀ x, veblen 2 (Zo x) = Zo x
  Zo_BR : ∀ x, InE x → x < Om1 → Zo x ≤ hcBR x
  Fr_pi : ∀ {σ ρ}, Bases σ ρ → γ < σ → Fr ρ ∈ TB ρ σ ∧ pi σ ρ (Fr ρ) = Fr σ
  N_pi : ∀ {σ ρ}, Bases σ ρ → γ < σ → hbN (j + 1) (Fr ρ) ∈ TB ρ σ ∧ pi σ ρ (hbN (j + 1) (Fr ρ)) = hbN (j + 1) (Fr σ)

namespace HcA

variable {j : ℕ} (A : HcA j)

open Classical in
/-- **The low field of `A`**: `N_{j+1}(F(x))` above `γ`, `Z_o(x)` at or below it. -/
noncomputable def Zl (x : Ordinal.{0}) : Ordinal.{0} := if A.γ < x then hbN (j + 1) (A.Fr x) else A.Zo x

theorem Zl_eq {x : Ordinal.{0}} (h : A.γ < x) : A.Zl x = hbN (j + 1) (A.Fr x) := by unfold HcA.Zl; rw [if_pos h]

theorem Zl_low {x : Ordinal.{0}} (h : ¬ A.γ < x) : A.Zl x = A.Zo x := by unfold HcA.Zl; rw [if_neg h]

theorem Zl_le_Zo (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : A.Zl x ≤ A.Zo x := by
  unfold HcA.Zl; split_ifs with h
  · exact (A.N_Zo hx hx1 h).le
  · exact le_rfl

theorem Zl_BR (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : A.Zl x ≤ hcBR x :=
  (A.Zl_le_Zo x hx hx1).trans (A.Zo_BR x hx hx1)

theorem Zl_fix (hj : 1 ≤ j) (x : Ordinal.{0}) : veblen 2 (A.Zl x) = A.Zl x := by
  unfold HcA.Zl; split_ifs
  · have := hb_fix_down (j := 2) (by omega) (hbN_fix (j + 1) (A.Fr x))
    rwa [show ((2 : ℕ) : Ordinal.{0}) = 2 by norm_num] at this
  · exact A.Zo_fix x

theorem F_E : InE A.F := hcX_fixE A.F_fix

theorem N_E : InE (hbN (j + 1) A.F) := hbN_E _ _

theorem F_lt_N : A.F < hbN (j + 1) A.F := hbN_gt _ _

theorem N_lim : IsSuccLimit (hbN (j + 1) A.F) := ev_isSuccLimit_of_inE A.N_E

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : A.γ < x)
include hx hx1 hγ

theorem N_lt1x : hbN (j + 1) (A.Fr x) < gq 1 x :=
  ((A.N_Zo hx hx1 hγ).trans_le (A.Zo_BR x hx hx1)).trans (hcBR_lt1 hx hx1)

theorem Fr_lt_N : A.Fr x < hbN (j + 1) (A.Fr x) := hbN_gt _ _

theorem Fr_lt1 : A.Fr x < gq 1 x := (A.Fr_lt_N hx hx1 hγ).trans (A.N_lt1x hx hx1 hγ)

end Base

/-- **`F + 1 + λ` is not a fixed point of `φ(j+1, ·)`** for `λ < N_{j+1}(F)`. -/
theorem j_lt {l : Ordinal.{0}} (hl : l < hbN (j + 1) A.F) :
    A.F + 1 + l < veblen ((j + 1 : ℕ) : Ordinal.{0}) (A.F + 1 + l) := by
  set y := A.F + 1 + l with hy
  have hyN : y < hbN (j + 1) A.F := (inE_indec A.N_E).add_lt (A.N_lim.add_one_lt A.F_lt_N) hl
  rcases (right_le_veblen _ y).lt_or_eq with h | h
  · exact h
  · exfalso
    have hFy : A.F < y := (lt_add_one _).trans_le le_self_add
    exact absurd (hbN_le (j + 1) h.symm hFy) (not_le.2 hyN)

theorem add_lt_N {l : Ordinal.{0}} (hl : l < hbN (j + 1) A.F) : A.F + 1 + l < hbN (j + 1) A.F :=
  (inE_indec A.N_E).add_lt (A.N_lim.add_one_lt A.F_lt_N) hl

theorem lt_Q {l : Ordinal.{0}} (hl : l < hbN (j + 1) A.F) : l < veblen ((j + 1 : ℕ) : Ordinal.{0}) (A.F + 1 + l) :=
  le_add_self.trans_lt (A.j_lt hl)

theorem Q_lt_N {l : Ordinal.{0}} (hl : l < hbN (j + 1) A.F) :
    veblen ((j + 1 : ℕ) : Ordinal.{0}) (A.F + 1 + l) < hbN (j + 1) A.F := by
  have h := (isNormal_veblen ((j + 1 : ℕ) : Ordinal.{0})).strictMono (A.add_lt_N hl)
  rwa [hbN_fix] at h

theorem G_lt_Q (l : Ordinal.{0}) : gcG 0 < veblen ((j + 1 : ℕ) : Ordinal.{0}) (A.F + 1 + l) :=
  A.G_le.trans_lt (((lt_add_one _).trans_le le_self_add).trans_le (right_le_veblen _ _))

theorem Q_lt_Q {μ l : Ordinal.{0}} (h : μ < l) :
    veblen ((j + 1 : ℕ) : Ordinal.{0}) (A.F + 1 + μ) < veblen ((j + 1 : ℕ) : Ordinal.{0}) (A.F + 1 + l) :=
  (isNormal_veblen _).strictMono ((add_lt_add_iff_left _).2 h)

/-- **A limit `λ < N_{j+1}(F)` lies below `Q_μ` for some `μ < λ`.** -/
theorem cover {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlN : l < hbN (j + 1) A.F) :
    ∃ μ, μ < l ∧ l < veblen ((j + 1 : ℕ) : Ordinal.{0}) (A.F + 1 + μ) := by
  have h := A.lt_Q hlN
  obtain ⟨t, ht, hlt⟩ := ((isNormal_veblen _).lt_iff_exists_lt (isSuccLimit_add _ hl)).1 h
  obtain ⟨d, hd, htd⟩ := (lt_add_iff hl.bot_lt.ne').1 ht
  exact ⟨d, hd, hlt.trans_le ((isNormal_veblen _).monotone htd)⟩

/-- **The code-gate condition at `F + 1 + λ`**: a code `F + 1 + λ` over `Z` ⇒ `max(γ, g_E(λ)) < Z`. -/
theorem gate_of_j (E : HcVD) {Z l : Ordinal.{0}} (hlB : l < E.B) (hlN : l < hbN (j + 1) A.F) (hZ : SC Z)
    (hZ1 : Z ≤ Om 1) (h : GxCl Z {gcG 0} (A.F + 1 + l)) : max A.γ (E.g l) < Z := by
  have hFj : A.F ≤ A.F + 1 + l := le_self_add.trans le_self_add
  have hjN := A.add_lt_N hlN
  have hF := A.F_code Z hZ hZ1 _ h hFj hjN
  have hl := hcX_cl_idx hZ hZ1 A.F_E A.G_le hF h
  have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1
  refine max_lt (A.F_cl Z hZ hZ1 _ h hFj hjN) ?_
  exact E.code_gate Z hZ1' hZ.1 (fun _ _ hu hv => hZ.isPrincipal hu hv) (fun _ _ hu hv => hZ.2 _ hu _ hv)
    {gcG 0} (fun s hs => Or.inl (Set.mem_singleton_iff.1 hs)) l hl hlB

end HcA

/-- **A pseudo-base of level `j+1`**: a base with `G < F` whose reading is a fixed point of `φ(j+1, ·)`. -/
structure HcX (j : ℕ) extends HcA j where
  G_lt : gcG 0 < F
  Fr_fix : ∀ {x}, InE x → x < Om1 → γ < x → veblen ((j + 1 : ℕ) : Ordinal.{0}) (Fr x) = Fr x

namespace HcX

variable {j : ℕ} (X : HcX j)

theorem evF_le : evZ X.F ≤ hbN (j + 1) X.F := by
  have := hb_fix_down (j := 1) (Nat.succ_le_succ (Nat.zero_le j)) (hbN_fix (j + 1) X.F)
  rw [Nat.cast_one] at this
  exact evZ_le X.F_lt_N this

theorem evF_lt1 : evZ X.F < gcG 1 := X.evF_le.trans_lt X.N_lt1

theorem evF_mem (S : InaccSeq.{0}) {a b : Ordinal.{0}} (ha : 0 < a) (hb : X.γ < b) : evZ X.F ∈ S.CSet a b := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [← hbN1_eq]; exact X.N_mem S ha hb
  · have hF2 : veblen 2 X.F = X.F := by
      have := hb_fix_down (j := 2) (by omega) X.F_fix; rwa [show ((2 : ℕ) : Ordinal.{0}) = 2 by norm_num] at this
    have e : evZ X.F = veblen 2 (X.F + 1) := by have := gz_evZ_veb2 X.F; rwa [hF2] at this
    rw [e]
    exact CSet.phi_mem (gr_cst_mem ha _ 2 (gw_two_lt_w.trans (omega0_lt_gamma 1))) (CSet.succ_mem (X.F_mem S ha hb))

theorem evF_cl {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (h : GxCl Z {gcG 0} (evZ X.F)) : X.γ < Z := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [← hbN1_eq] at h; exact X.N_cl Z hZ hZ1 h
  · have hF2 : veblen 2 X.F = X.F := by
      have := hb_fix_down (j := 2) (by omega) X.F_fix; rwa [show ((2 : ℕ) : Ordinal.{0}) = 2 by norm_num] at this
    have e : evZ X.F = veblen ((1 + 1 : ℕ) : Ordinal.{0}) (X.F + 1) := by
      have := gz_evZ_veb2 X.F; rw [hF2] at this; rw [this]; norm_num
    rw [e] at h
    have hF := hcX_cl_succ_fix 1 hZ hZ1 X.G_le h
    exact X.F_cl Z hZ hZ1 _ hF le_rfl X.F_lt_N

theorem Fr_fix1 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : X.γ < x) : veblen 1 (X.Fr x) = X.Fr x := by
  have := hb_fix_down (j := 1) (by omega) (X.Fr_fix hx hx1 hγ); rwa [Nat.cast_one] at this

theorem evFr_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hγ : X.γ < σ) :
    evZ (X.Fr ρ) ∈ TB ρ σ ∧ pi σ ρ (evZ (X.Fr ρ)) = evZ (X.Fr σ) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [← hbN1_eq, ← hbN1_eq]; exact X.N_pi hB hγ
  · have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hγρ : X.γ < ρ := hγ.trans hB.2.2.1
    have h2 : ∀ {y}, InE y → y < Om1 → X.γ < y → veblen 2 (X.Fr y) = X.Fr y := fun hy hy1 hγy => by
      have := hb_fix_down (j := 2) (by omega) (X.Fr_fix hy hy1 hγy)
      rwa [show ((2 : ℕ) : Ordinal.{0}) = 2 by norm_num] at this
    have h2σ : (2 : Ordinal.{0}) < σ := gw_two_lt_w.trans (omega0_lt_inE hB.1)
    obtain ⟨f1, f2⟩ := X.Fr_pi hB hγ
    have h := glA_pi hB (mem_TB_of_lt hB h2σ) (gw_two_T hB.2.1 hρ1).2 f1
      (gm1_T hB.2.1 hρ1 (X.Fr_lt1 hB.2.1 hρ1 hγρ)).2
    rw [pi_lt hB h2σ, f2, ha_glA2_P hB.2.1 hρ1 (h2 hB.2.1 hρ1 hγρ) (X.Fr_gt hB.2.1 hρ1 hγρ) (X.Fr_lt1 hB.2.1 hρ1 hγρ),
      ha_glA2_P hB.1 hσ1 (h2 hB.1 hσ1 hγ) (X.Fr_gt hB.1 hσ1 hγ) (X.Fr_lt1 hB.1 hσ1 hγ)] at h
    exact h

end HcX

/-- **THE STAGE AT A PSEUDO-BASE `F` OF ANY LEVEL**: `Q = F`, `P = F(x)`, gate `γ`, low field `Z_o`. -/
noncomputable def hcXPB {j : ℕ} (X : HcX j) : HcPB where
  Q := X.F
  P := X.Fr
  Zl := X.Zo
  γP := X.γ
  γP_lt := X.γ_lt
  Q_fix := by have := hb_fix_down (j := 1) (by omega) X.F_fix; rwa [Nat.cast_one] at this
  G_lt_Q := X.G_lt
  evQ_lt1 := X.evF_lt1
  Q_mem := fun S _ _ ha hb => X.F_mem S ha hb
  evQ_mem := fun S _ _ ha hb => X.evF_mem S ha hb
  Q_code := fun Z hZ hZ1 y hy hQy hyZ => X.F_code Z hZ hZ1 y hy hQy (hyZ.trans_le X.evF_le)
  Q_cl := fun Z hZ hZ1 y hy hQy hyZ => X.F_cl Z hZ hZ1 y hy hQy (hyZ.trans_le X.evF_le)
  evQ_cl := fun Z hZ hZ1 h => X.evF_cl hZ hZ1 h
  P_fix := fun hx hx1 hγ => X.Fr_fix1 hx hx1 hγ
  P_gt := fun hx hx1 hγ => X.Fr_gt hx hx1 hγ
  P_Zl := fun _ hx hx1 hγ => (X.Fr_lt_N hx hx1 hγ).trans (X.N_Zo hx hx1 hγ)
  Zl_fix := X.Zo_fix
  Zl_BR := X.Zo_BR
  P_pi := fun hB hγ => X.Fr_pi hB hγ
  evP_pi := fun hB hγ => X.evFr_pi hB hγ

theorem hcXPB_Q {j : ℕ} (X : HcX j) : (hcXPB X).Q = X.F := rfl

theorem hcXPB_P {j : ℕ} (X : HcX j) : (hcXPB X).P = X.Fr := rfl

theorem hcXPB_γ {j : ℕ} (X : HcX j) : (hcXPB X).γP = X.γ := rfl

theorem hcXPB_Zl {j : ℕ} (X : HcX j) : (hcXPB X).Zl = X.Zo := rfl

/-! ## Going down one level -/

/-- **A pseudo-base of level `j+2` is one of level `j+1`.** -/
noncomputable def HcX.down {j : ℕ} (X : HcX (j + 1)) : HcX j where
  F := X.F
  Fr := X.Fr
  γ := X.γ
  Zo := X.Zo
  γ_lt := X.γ_lt
  F_fix := hb_fix_down (Nat.le_succ _) X.F_fix
  G_le := X.G_le
  N_lt1 := (hbN_mono (Nat.le_succ _) X.F).trans_lt X.N_lt1
  F_mem := X.F_mem
  N_mem := fun S _ _ ha hb => by
    have e : hbN (j + 1) X.F = veblen ((j + 1 + 1 : ℕ) : Ordinal.{0}) (X.F + 1) := by
      have := hbN_veb (j + 1) X.F; rwa [X.F_fix] at this
    rw [e]
    exact CSet.phi_mem (hcX_nat_mem S ha _ _) (CSet.succ_mem (X.F_mem S ha hb))
  F_code := fun Z hZ hZ1 y hy hQy hyZ =>
    X.F_code Z hZ hZ1 y hy hQy (hyZ.trans_le (hbN_mono (Nat.le_succ _) X.F))
  F_cl := fun Z hZ hZ1 y hy hQy hyZ => X.F_cl Z hZ hZ1 y hy hQy (hyZ.trans_le (hbN_mono (Nat.le_succ _) X.F))
  N_cl := fun Z hZ hZ1 h => by
    have e : hbN (j + 1) X.F = veblen ((j + 1 + 1 : ℕ) : Ordinal.{0}) (X.F + 1) := by
      have := hbN_veb (j + 1) X.F; rwa [X.F_fix] at this
    rw [e] at h
    exact X.F_cl Z hZ hZ1 _ (hcX_cl_succ_fix (j + 1) hZ hZ1 X.G_le h) le_rfl X.F_lt_N
  Fr_gt := X.Fr_gt
  Fr_glA := fun hx hx1 hγ => hb_glA_fixP hx hx1 j (hb_fix_down (Nat.le_succ _) (X.Fr_fix hx hx1 hγ))
    (X.Fr_gt hx hx1 hγ) (X.Fr_lt1 hx hx1 hγ)
  N_Zo := fun hx hx1 hγ => (hbN_mono (Nat.le_succ _) _).trans_lt (X.N_Zo hx hx1 hγ)
  Zo_fix := X.Zo_fix
  Zo_BR := X.Zo_BR
  Fr_pi := X.Fr_pi
  N_pi := fun {σ ρ} hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hγρ : X.γ < ρ := hγ.trans hB.2.2.1
    have hkσ : ((j + 1 + 1 : ℕ) : Ordinal.{0}) < σ := (natCast_lt_omega0 _).trans (omega0_lt_inE hB.1)
    obtain ⟨f1, f2⟩ := X.Fr_pi hB hγ
    have h := glA_pi hB (mem_TB_of_lt hB hkσ) (hb_lev_T hB.2.1 hρ1 (j + 1 + 1)).2 f1
      (gm1_T hB.2.1 hρ1 (X.Fr_lt1 hB.2.1 hρ1 hγρ)).2
    rw [pi_lt hB hkσ, f2, hb_glA_fixP hB.2.1 hρ1 (j + 1) (X.Fr_fix hB.2.1 hρ1 hγρ) (X.Fr_gt hB.2.1 hρ1 hγρ)
      (X.Fr_lt1 hB.2.1 hρ1 hγρ), hb_glA_fixP hB.1 hσ1 (j + 1) (X.Fr_fix hB.1 hσ1 hγ) (X.Fr_gt hB.1 hσ1 hγ)
      (X.Fr_lt1 hB.1 hσ1 hγ)] at h
    exact h
  G_lt := X.G_lt
  Fr_fix := fun hx hx1 hγ => hb_fix_down (Nat.le_succ _) (X.Fr_fix hx hx1 hγ)

theorem HcX.down_F {j : ℕ} (X : HcX (j + 1)) : X.down.F = X.F := rfl

theorem HcX.down_Fr {j : ℕ} (X : HcX (j + 1)) : X.down.Fr = X.Fr := rfl

theorem HcX.down_γ {j : ℕ} (X : HcX (j + 1)) : X.down.γ = X.γ := rfl

theorem HcX.down_Zo {j : ℕ} (X : HcX (j + 1)) : X.down.Zo = X.Zo := rfl

theorem hcXPB_down {j : ℕ} (X : HcX (j + 1)) : hcXPB X.down = hcXPB X := rfl

/-! ## The offset `λ` over a base of level `j+2` -/

section Off

variable (j : ℕ) (A : HcA (j + 1)) (E : HcVD) (l : Ordinal.{0}) (hlB : l < E.B) (hlN : l < hbN (j + 1 + 1) A.F)
  (hZ : ∀ x, InE x → x < Om1 → E.Z x ≤ A.Zl x)

include hlB hZ in
theorem hcXoff_R_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : max A.γ (E.g l) < x) :
    E.R l x < hbN (j + 1 + 1) (A.Fr x) := by
  have h := (E.R_lt_Z x hx hx1 l hlB (max_lt_iff.1 hγ).2).trans_le (hZ x hx hx1)
  rwa [A.Zl_eq (max_lt_iff.1 hγ).1] at h

include hlB hZ in
theorem hcXoff_t1_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : max A.γ (E.g l) < x) :
    A.Fr x + E.R l x + 1 < hbN (j + 1 + 1) (A.Fr x) := by
  have hNE := hbN_E (j + 1 + 1) (A.Fr x)
  exact (ev_isSuccLimit_of_inE hNE).add_one_lt ((inE_indec hNE).add_lt (A.Fr_lt_N hx hx1 (max_lt_iff.1 hγ).1)
    (hcXoff_R_lt j A E l hlB hZ hx hx1 hγ))

include hlB hZ in
theorem hcXoff_t1_lt1 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : max A.γ (E.g l) < x) :
    A.Fr x + E.R l x + 1 < gq 1 x :=
  (hcXoff_t1_lt j A E l hlB hZ hx hx1 hγ).trans (A.N_lt1x hx hx1 (max_lt_iff.1 hγ).1)

include hlB hZ in
theorem hcXoff_facts {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : max A.γ (E.g l) < x) :
    x < glA ((j + 1 + 1 : ℕ) : Ordinal.{0}) (A.Fr x + E.R l x) x ∧
      glA ((j + 1 + 1 : ℕ) : Ordinal.{0}) (A.Fr x + E.R l x) x < gq 1 x ∧
      veblen ((j + 1 : ℕ) : Ordinal.{0}) (glA ((j + 1 + 1 : ℕ) : Ordinal.{0}) (A.Fr x + E.R l x) x) =
        glA ((j + 1 + 1 : ℕ) : Ordinal.{0}) (A.Fr x + E.R l x) x := by
  have ht1 := hcXoff_t1_lt1 j A E l hlB hZ hx hx1 hγ
  obtain ⟨htT, ht1'⟩ := gm1_T hx hx1 ((lt_add_one _).trans ht1)
  obtain ⟨hkT, hk1⟩ := hb_lev_T hx hx1 (j + 1 + 1)
  obtain ⟨-, hxa, -, -, -, -⟩ := glA_facts hx hx1 (hb_one_le (j + 1)) hkT hk1 htT ht1'
  have hP := glA_P hx hx1 (hb_one_le (j + 1)) hkT hk1 htT ht1'
  have hA := (max_lt_iff.1 hγ).1
  refine ⟨hxa, ?_, hb_fix_of_LuP (j + 1) hP⟩
  exact (hcX_glA_lt hx hx1 (j + 1) (A.Fr_glA hx hx1 hA) (A.Fr_lt1 hx hx1 hA) (A.N_lt1x hx hx1 hA)
    (hcXoff_R_lt j A E l hlB hZ hx hx1 hγ)).trans (A.N_lt1x hx hx1 hA)

include hlB hZ in
theorem hcXoff_t_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hγ : max A.γ (E.g l) < σ) :
    A.Fr ρ + E.R l ρ ∈ TB ρ σ ∧ pi σ ρ (A.Fr ρ + E.R l ρ) = A.Fr σ + E.R l σ := by
  obtain ⟨f1, f2⟩ := A.Fr_pi hB (max_lt_iff.1 hγ).1
  obtain ⟨e1, e2⟩ := E.ex σ ρ hB l hlB (max_lt_iff.1 hγ).2
  obtain ⟨s1, s2⟩ := pi_add hB f1 e1
  rw [f2, e2] at s2
  exact ⟨s1, s2⟩

theorem hcXoff_Nveb : hbN (j + 1) (veblen ((j + 1 + 1 : ℕ) : Ordinal.{0}) (A.F + 1 + l)) =
    veblen ((j + 1 + 1 : ℕ) : Ordinal.{0}) (A.F + 1 + l + 1) := hbN_veb (j + 1) _

include hlN in
theorem hcXoff_N_lt : veblen ((j + 1 + 1 : ℕ) : Ordinal.{0}) (A.F + 1 + l + 1) < hbN (j + 1 + 1) A.F := by
  have h1 : A.F + 1 + l + 1 < hbN (j + 1 + 1) A.F := A.N_lim.add_one_lt (A.add_lt_N hlN)
  have h2 := (isNormal_veblen ((j + 1 + 1 : ℕ) : Ordinal.{0})).strictMono h1
  rwa [hbN_fix] at h2

include hlB hlN hZ in
/-- **THE OFFSET `λ` OVER A BASE `A` OF LEVEL `j+2`**, `λ` read by `E`: the pseudo-base `φ(j+2, F + 1 + λ)` of level
`j+1`, reading `ϑˣ(Ω₁·(j+2) + F(x) + λ(x))`, gate `max(γ, g_E(λ))`, outer low field `Z_l` of `A`. -/
noncomputable def hcXoff : HcX j where
  F := veblen ((j + 1 + 1 : ℕ) : Ordinal.{0}) (A.F + 1 + l)
  Fr := fun x => glA ((j + 1 + 1 : ℕ) : Ordinal.{0}) (A.Fr x + E.R l x) x
  γ := max A.γ (E.g l)
  Zo := A.Zl
  γ_lt := max_lt A.γ_lt (E.g_lt l hlB)
  F_fix := hb_fix_veb (j + 1) _
  G_le := (A.G_lt_Q l).le
  N_lt1 := by rw [hcXoff_Nveb]; exact (hcXoff_N_lt j A l hlN).trans A.N_lt1
  F_mem := fun S _ _ ha hb => CSet.phi_mem (hcX_nat_mem S ha _ _)
    (CSet.add_mem (CSet.succ_mem (A.F_mem S ha ((le_max_left _ _).trans_lt hb)))
      (E.mem S _ _ ha l hlB ((le_max_right _ _).trans_lt hb)).1)
  N_mem := fun S _ _ ha hb => by
    rw [hcXoff_Nveb]
    exact CSet.phi_mem (hcX_nat_mem S ha _ _) (CSet.succ_mem
      (CSet.add_mem (CSet.succ_mem (A.F_mem S ha ((le_max_left _ _).trans_lt hb)))
        (E.mem S _ _ ha l hlB ((le_max_right _ _).trans_lt hb)).1))
  F_code := fun Z hZ hZ1 _ hy hQy hyZ => by
    rw [hcXoff_Nveb] at hyZ
    exact GxCl.phi (GxCl.small (hcX_nat_small _ hZ))
      (hb_cl_lev (k := j + 1 + 1) (by omega) hZ1 (A.j_lt hlN) (A.G_lt_Q l) hy hQy hyZ)
  F_cl := fun Z hZ hZ1 _ hy hQy hyZ => by
    rw [hcXoff_Nveb] at hyZ
    exact A.gate_of_j E hlB hlN hZ hZ1 (hb_cl_lev (k := j + 1 + 1) (by omega) hZ1 (A.j_lt hlN) (A.G_lt_Q l) hy hQy hyZ)
  N_cl := fun Z hZ hZ1 h => by
    rw [hcXoff_Nveb] at h
    exact A.gate_of_j E hlB hlN hZ hZ1 (hcX_cl_succ_fix (j + 1) hZ hZ1 (A.G_le.trans (le_self_add.trans le_self_add)) h)
  Fr_gt := fun hx hx1 hγ => (hcXoff_facts j A E l hlB hZ hx hx1 hγ).1
  Fr_glA := fun hx hx1 hγ => hb_glA_fixP hx hx1 j (hcXoff_facts j A E l hlB hZ hx hx1 hγ).2.2
    (hcXoff_facts j A E l hlB hZ hx hx1 hγ).1 (hcXoff_facts j A E l hlB hZ hx hx1 hγ).2.1
  N_Zo := fun {x} hx hx1 hγ => by
    have ht1 := hcXoff_t1_lt1 j A E l hlB hZ hx hx1 hγ
    have hA := (max_lt_iff.1 hγ).1
    show hbN (j + 1) (glA ((j + 1 + 1 : ℕ) : Ordinal.{0}) (A.Fr x + E.R l x) x) < A.Zl x
    rw [← hb_glA_succ hx hx1 (j + 1) ht1, A.Zl_eq hA, add_assoc (A.Fr x) (E.R l x) 1]
    refine hcX_glA_lt hx hx1 (j + 1) (A.Fr_glA hx hx1 hA) (A.Fr_lt1 hx hx1 hA) (A.N_lt1x hx hx1 hA) ?_
    have := hcXoff_t1_lt j A E l hlB hZ hx hx1 hγ
    rw [add_assoc (A.Fr x) (E.R l x) 1] at this
    exact (le_add_self).trans_lt this
  Zo_fix := A.Zl_fix (by omega)
  Zo_BR := A.Zl_BR
  Fr_pi := fun {σ ρ} hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hkσ : ((j + 1 + 1 : ℕ) : Ordinal.{0}) < σ := (natCast_lt_omega0 _).trans (omega0_lt_inE hB.1)
    obtain ⟨t1, t2⟩ := hcXoff_t_pi j A E l hlB hZ hB hγ
    have h := glA_pi hB (mem_TB_of_lt hB hkσ) (hb_lev_T hB.2.1 hρ1 (j + 1 + 1)).2 t1
      (gm1_T hB.2.1 hρ1 ((lt_add_one _).trans (hcXoff_t1_lt1 j A E l hlB hZ hB.2.1 hρ1 (hγ.trans hB.2.2.1)))).2
    rw [pi_lt hB hkσ, t2] at h
    exact h
  N_pi := fun {σ ρ} hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hγρ : max A.γ (E.g l) < ρ := hγ.trans hB.2.2.1
    have hkσ : ((j + 1 + 1 : ℕ) : Ordinal.{0}) < σ := (natCast_lt_omega0 _).trans (omega0_lt_inE hB.1)
    obtain ⟨t1, t2⟩ := hcXoff_t_pi j A E l hlB hZ hB hγ
    obtain ⟨o1, o2⟩ := one_TB hB
    obtain ⟨u1, u2⟩ := pi_add hB t1 o1
    rw [t2, o2] at u2
    have h := glA_pi hB (mem_TB_of_lt hB hkσ) (hb_lev_T hB.2.1 hρ1 (j + 1 + 1)).2 u1
      (gm1_T hB.2.1 hρ1 (hcXoff_t1_lt1 j A E l hlB hZ hB.2.1 hρ1 hγρ)).2
    rw [pi_lt hB hkσ, u2, hb_glA_succ hB.2.1 hρ1 (j + 1) (hcXoff_t1_lt1 j A E l hlB hZ hB.2.1 hρ1 hγρ),
      hb_glA_succ hB.1 hσ1 (j + 1) (hcXoff_t1_lt1 j A E l hlB hZ hB.1 hσ1 hγ)] at h
    exact h
  G_lt := A.G_lt_Q l
  Fr_fix := fun hx hx1 hγ => (hcXoff_facts j A E l hlB hZ hx hx1 hγ).2.2

theorem hcXoff_F : (hcXoff j A E l hlB hlN hZ).F = veblen ((j + 1 + 1 : ℕ) : Ordinal.{0}) (A.F + 1 + l) := rfl

theorem hcXoff_Fr (x : Ordinal.{0}) :
    (hcXoff j A E l hlB hlN hZ).Fr x = glA ((j + 1 + 1 : ℕ) : Ordinal.{0}) (A.Fr x + E.R l x) x := rfl

theorem hcXoff_γ : (hcXoff j A E l hlB hlN hZ).γ = max A.γ (E.g l) := rfl

theorem hcXoff_Zo : (hcXoff j A E l hlB hlN hZ).Zo = A.Zl := rfl

end Off

end Googology.Trans.PoR.InaccPsi.R2.Hc
