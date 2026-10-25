import Googology.Trans.PoR.InaccPsi.R2.GwYFr

/-!
# THE BASE DATA AT EVERY `ζ_{G+n}` AND `ζ_{Γ_{x+1}+n}`, GENERIC IN `n`

`R2.GwZb` and `R2.GwZx` give the base data of the union at `ζ_{G+1}` (and of the steps above it) at the pseudo-base
`ζ_{Γ_{x+1}+1}`.  Here the same facts hold at every pseudo-base `Z_n(x) = ζ_{Γ_{x+1}+n}` (`Gw.gwZn`), by one induction
on `n`:

* `gzZ` (**`ζ_{G+n}`**: `gzZ 0 = G`, `gzZ (n+1) = evZ(gzZ n)`), `gz_evZ_veb2` (`evZ(φ(2, a)) = φ(2, a+1)`), `gzZ_eq`
  (**`ζ_{G+n} = φ(2, G + n)`**), `gzZ_E`, `gzZ_strictMono`, `gzZ_G_le`, `gz_evZ_lt_G1`, `gzZ_lt1`
  (`ζ_{G+n} < Γ_{Ω₁+2}`),
  `gzZ_mem` (in every hull `C(a, b)`, `0 < a`), `gzZ_cl` (a code over every strongly critical `Z`);
* `gz_eN_of_low` (**`ε_{P+1} = ϑˣ(Ω₁ + P)`** for every `ε`-number `P ∈ (x, Γ_{x+2})` with `ϑˣ(Ω₁ + σ) < P`, `σ < P`),
  `gz_base` (**both hypotheses at every `Z_n(x)`**), `gz_low`, `gz_eNZ`, `gz_glAZ` (**`ϑˣ(Ω₁ + Z_n + ν) =
  ε_{Z_n+1+ν}` for `ν < Z_{n+1}`**), `gz_b_eN` (**`ε_{b+1} = ϑˣ(Ω₁ + Z_{n+1} + ν + 1)` for `b = φ(1, Z_{n+1} + ν)`**);
* `gz_glA2_succ` (**`ϑˣ(Ω₁·2 + t + 1) = evZ(ϑˣ(Ω₁·2 + t))`**), `gz_glA2` (**`ϑˣ(Ω₁·2 + Γ_{x+1} + n) = Z_{n+1}(x)`**),
  `gz_Z_pi` (**Lemma EXACT: `π_{σ,ρ}(Z_n(ρ)) = Z_n(σ)`**), `gz_eNZ_pi`, `gz_evAZ_pi`, `gz_b_pi_Z` (**Lemma EXACT for
  `φ(1, Z_{n+1}(ρ) + ν(ρ))`, `ω ≤ ν(ρ) < Z_{n+2}(ρ)`**).

No new axiom.  New definition: `gzZ`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gz

open Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gr
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The ordinals `ζ_{G+n}` -/

/-- **`ζ_{G+n}`**: `gzZ 0 = G = Γ_{Ω₁+1}`, `gzZ (n+1) = evZ(gzZ n)`. -/
noncomputable def gzZ : ℕ → Ordinal.{0}
  | 0 => gcG 0
  | n + 1 => evZ (gzZ n)

theorem gzZ_succ (n : ℕ) : gzZ (n + 1) = evZ (gzZ n) := rfl

theorem gzZ_one : gzZ 1 = gwZ := rfl

theorem gzZ_two : gzZ 2 = gwZ2 := rfl

theorem gzZ_E : ∀ n : ℕ, InE (gzZ n)
  | 0 => Low.opow_eq_self_of_SC (gcG_SC 0)
  | _ + 1 => evZ_E _

theorem gzZ_lt_succ (n : ℕ) : gzZ n < gzZ (n + 1) := lt_evZ _

theorem gzZ_strictMono : StrictMono gzZ := strictMono_nat_of_lt_succ gzZ_lt_succ

theorem gzZ_G_le (n : ℕ) : gcG 0 ≤ gzZ n := gzZ_strictMono.monotone (Nat.zero_le n)

theorem gzZ_G_lt (n : ℕ) : gcG 0 < gzZ (n + 1) := (gzZ_G_le n).trans_lt (gzZ_lt_succ n)

/-- **`evZ(φ(2, a)) = φ(2, a + 1)`.** -/
theorem gz_evZ_veb2 (a : Ordinal.{0}) : evZ (veblen 2 a) = veblen 2 (a + 1) := by
  refine le_antisymm (evZ_le ((isNormal_veblen 2).strictMono (lt_add_one a)) (veblen_veblen_of_lt one_lt_two _)) ?_
  obtain ⟨i, hi⟩ := gw_LuP2 (veblen 2 a)
  have hai : a < i := by
    have h := lt_evZ (veblen 2 a)
    rw [← hi] at h
    exact (isNormal_veblen 2).strictMono.lt_iff_lt.1 h
  rw [← hi]
  exact (isNormal_veblen 2).strictMono.monotone (Order.add_one_le_of_lt hai)

/-- **`ζ_{G+n} = φ(2, G + n)`.** -/
theorem gzZ_eq : ∀ n : ℕ, gzZ n = veblen 2 (gcG 0 + n)
  | 0 => by rw [Nat.cast_zero, add_zero]; exact (gn_veb_fix (gcG_SC 0) gw_two_lt_G).symm
  | n + 1 => by rw [gzZ_succ, gzZ_eq n, gz_evZ_veb2, Nat.cast_succ, add_assoc]

/-- `evZ(τ) < Γ_{Ω₁+2}` for `τ < Γ_{Ω₁+2}`. -/
theorem gz_evZ_lt_G1 {τ : Ordinal.{0}} (hτ : τ < gcG 1) : evZ τ < gcG 1 := by
  have h2 : veblen 2 (τ + 1) < gcG 1 :=
    (gcG_SC 1).2 2 (gw_two_lt_G.trans (gcG_lt zero_lt_one)) _ ((gcG_SC 1).add_one_lt hτ)
  have h3 : evZ τ ≤ veblen 2 (τ + 1) :=
    evZ_le ((lt_add_one τ).trans_le (right_le_veblen 2 _)) (veblen_veblen_of_lt one_lt_two _)
  exact h3.trans_lt h2

/-- **`ζ_{G+n} < Γ_{Ω₁+2}`.** -/
theorem gzZ_lt1 : ∀ n : ℕ, gzZ n < gcG 1
  | 0 => gcG_lt zero_lt_one
  | n + 1 => gz_evZ_lt_G1 (gzZ_lt1 n)

theorem gz_nat_lt_gam1 (n : ℕ) : (n : Ordinal.{0}) < gamma 1 := (natCast_lt_omega0 n).trans (omega0_lt_gamma 1)

/-- **`ζ_{G+n}` lies in every hull `C(a, b)`, `0 < a`.** -/
theorem gzZ_mem (S : InaccSeq.{0}) {a b : Ordinal.{0}} (ha : 0 < a) (n : ℕ) : gzZ n ∈ S.CSet a b := by
  rw [gzZ_eq]
  exact CSet.phi_mem (gr_cst_mem ha b 2 (gw_two_lt_w.trans (omega0_lt_gamma 1)))
    (CSet.add_mem (gmS_G0_mem S ha) (gr_cst_mem ha b n (gz_nat_lt_gam1 n)))

/-- **`ζ_{G+n}` is a code over every strongly critical `Z`.** -/
theorem gzZ_cl {Z : Ordinal.{0}} (hZ : SC Z) (n : ℕ) : GxCl Z {gcG 0} (gzZ n) := by
  rw [gzZ_eq]
  have hω : ω < Z := omega0_lt_inE (Low.opow_eq_self_of_SC hZ)
  exact GxCl.phi (GxCl.small (gw_two_lt_w.trans hω))
    (GxCl.add (GxCl.atom (Set.mem_singleton _)) (GxCl.small ((natCast_lt_omega0 n).trans hω)))

/-! ## The base data at every `Z_n(x) = ζ_{Γ_{x+1}+n}` -/

theorem gz_Zs (x : Ordinal.{0}) (n : ℕ) : gwZn x (n + 1) = evZ (gwZn x n) := rfl

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **`ε_{P+1} = ϑˣ(Ω₁ + P)`** for an `ε`-number `P ∈ (x, Γ_{x+2})` with `ϑˣ(Ω₁ + σ) < P` for every `σ < P`. -/
theorem gz_eN_of_low {P : Ordinal.{0}} (hPE : InE P) (hxP : x < P) (hPq : P < gq 1 x)
    (hlow : ∀ σ, σ < P → glA 1 σ x < P) : eN P = glA 1 P x := by
  obtain ⟨hPT, hP1⟩ := gm1_T hx hx1 hPq
  obtain ⟨h1T, h11⟩ := gl_one_T hx hx1
  obtain ⟨-, -, -, haE, -, hta⟩ := glA_facts hx hx1 le_rfl h1T h11 hPT hP1
  refine le_antisymm (eN_le hta haE) ?_
  have hP1' : LuP 1 (eN P) := by
    have h := vzP_one.2 (eN_E P); unfold VzP at h; rwa [Nat.cast_one] at h
  exact glA_min hx hx1 le_rfl h1T h11 hPT hP1 hP1' (hxP.trans (lt_eN _)) (lt_eN _)
    ((lu_one_lt_E hPE).trans (lt_eN _)) (fun σ hσ => (hlow σ hσ).trans (lt_eN _))

/-- **The two base facts at every `Z_n(x)`**: `ϑˣ(Ω₁ + σ) < Z_n` for `σ < Z_n`, and `ε_{Z_n+1} = ϑˣ(Ω₁ + Z_n)`. -/
theorem gz_base : ∀ n : ℕ, (∀ σ, σ < gwZn x n → glA 1 σ x < gwZn x n) ∧ eN (gwZn x n) = glA 1 (gwZn x n) x
  | 0 => by
    obtain ⟨-, -, -, hGE, -⟩ := lgG_facts hx hx1
    have h1G : (1 : Ordinal.{0}) < lgG x := one_lt_omega0.trans (omega0_lt_inE hGE)
    have hlow : ∀ σ, σ < gwZn x 0 → glA 1 σ x < gwZn x 0 := fun σ hσ => glA_lt_G hx hx1 h1G hσ
    exact ⟨hlow, gz_eN_of_low hx hx1 (gwZn_E hx hx1 0) (gwZn_gt hx hx1 0) (gwZn_lt hx hx1 0) hlow⟩
  | n + 1 => by
    obtain ⟨hlow, hbase⟩ := gz_base n
    have hPE := gwZn_E hx hx1 n
    have hlowS : ∀ σ, σ < gwZn x (n + 1) → glA 1 σ x < gwZn x (n + 1) := by
      intro σ hσ
      rw [gz_Zs] at hσ ⊢
      rcases lt_or_ge σ (gwZn x n) with hσP | hσP
      · exact (hlow σ hσP).trans (lt_evZ _)
      · obtain ⟨ν, rfl⟩ := exists_add_of_le hσP
        have hν : ν < evZ (gwZn x n) := lt_of_le_of_lt le_add_self hσ
        have hq : gwZn x n + ν < gq 1 x := hσ.trans (gwZn_lt hx hx1 (n + 1))
        rw [gw_glA_eqP hx hx1 hPE (gwZn_gt hx hx1 n) hbase.symm hlow ν hq
          (fun ν' h _ => gw_lt_evA hPE (lt_of_le_of_lt h hν))]
        exact evA_lt_evZ hPE (add_lt_evZ (one_lt_omega0.trans (omega0_lt_inE (evZ_E _))) hν)
    exact ⟨hlowS, gz_eN_of_low hx hx1 (gwZn_E hx hx1 (n + 1)) (gwZn_gt hx hx1 (n + 1)) (gwZn_lt hx hx1 (n + 1))
      hlowS⟩

theorem gz_low (n : ℕ) {σ : Ordinal.{0}} (hσ : σ < gwZn x n) : glA 1 σ x < gwZn x n := (gz_base hx hx1 n).1 σ hσ

/-- **`ε_{Z_n+1} = ϑˣ(Ω₁ + Z_n)`.** -/
theorem gz_eNZ (n : ℕ) : eN (gwZn x n) = glA 1 (gwZn x n) x := (gz_base hx hx1 n).2

/-- **`ϑˣ(Ω₁ + Z_n + ν) = ε_{Z_n+1+ν}`** for every `ν < Z_{n+1}`. -/
theorem gz_glAZ (n : ℕ) {ν : Ordinal.{0}} (hν : ν < gwZn x (n + 1)) :
    glA 1 (gwZn x n + ν) x = evA (gwZn x n) (1 + ν) := by
  have hPE := gwZn_E hx hx1 n
  rw [gz_Zs] at hν
  have hq : gwZn x n + ν < gq 1 x := (add_lt_evZ (lt_evZ _) hν).trans (gwZn_lt hx hx1 (n + 1))
  exact gw_glA_eqP hx hx1 hPE (gwZn_gt hx hx1 n) (gz_eNZ hx hx1 n).symm (fun σ hσ => gz_low hx hx1 n hσ) ν hq
    (fun ν' h _ => gw_lt_evA hPE (lt_of_le_of_lt h hν))

/-- **`ε_{b(x)+1} = ϑˣ(Ω₁ + Z_{n+1} + ν + 1)` for `b(x) = φ(1, Z_{n+1} + ν)`** (`ω ≤ ν < Z_{n+2}`). -/
theorem gz_b_eN (n : ℕ) {ν : Ordinal.{0}} (hω : ω ≤ ν) (hν : ν < gwZn x (n + 2)) :
    eN (veblen 1 (gwZn x (n + 1) + ν)) = glA 1 (gwZn x (n + 1) + (ν + 1)) x := by
  have hν1 : ν + 1 < gwZn x (n + 2) := (ev_isSuccLimit_of_inE (evZ_E _)).add_one_lt hν
  rw [gz_glAZ hx hx1 (n + 1) hν1, one_add_of_omega0_le (hω.trans le_self_add), go_eN_veb, add_assoc]
  show veblen 1 _ = Ordinal.epsilon (evIx (evZ (gwZn x n)) + (ν + 1))
  rw [gw_evIx_Z]
  rfl

/-- **`ϑˣ(Ω₁·2 + t + 1) = evZ(ϑˣ(Ω₁·2 + t))`.** -/
theorem gz_glA2_succ {t : Ordinal.{0}} (ht : t + 1 < gq 1 x) : glA 2 (t + 1) x = evZ (glA 2 t x) := by
  have ht' : t < gq 1 x := (lt_add_one t).trans ht
  obtain ⟨htT, ht1⟩ := gm1_T hx hx1 ht'
  obtain ⟨hsT, hs1⟩ := gm1_T hx hx1 ht
  obtain ⟨h2T, h21⟩ := gw_two_T hx hx1
  have h12 : (1 : Ordinal.{0}) ≤ 2 := one_le_two
  obtain ⟨-, hxa, -, -, h2a, hta⟩ := glA_facts hx hx1 h12 h2T h21 htT ht1
  have hlt : glA 2 t x < glA 2 (t + 1) x := glA_lt_of hx hx1 h12 h2T h21 htT hsT hs1 (lt_add_one t)
  refine le_antisymm ?_ ?_
  · refine glA_min hx hx1 h12 h2T h21 hsT hs1 (gw_LuP2 _) (hxa.trans (lt_evZ _))
      ((ev_isSuccLimit_of_inE (evZ_E _)).add_one_lt (hta.trans (lt_evZ _))) (h2a.trans (lt_evZ _)) ?_
    intro σ hσ
    have hσt : σ ≤ t := Order.lt_add_one_iff.1 hσ
    obtain ⟨hσT, hσ1⟩ := gm1_T hx hx1 (lt_of_le_of_lt hσt ht')
    exact lt_of_le_of_lt ((glA_le_iff hx hx1 h12 h2T h21 hσT hσ1 htT ht1).2 hσt) (lt_evZ _)
  · obtain ⟨i, hi⟩ := glA_P hx hx1 h12 h2T h21 hsT hs1
    have hfix : Ordinal.epsilon (glA 2 (t + 1) x) = glA 2 (t + 1) x := by
      rw [← hi]; exact veblen_veblen_of_lt one_lt_two i
    exact evZ_le hlt hfix

theorem gz_G_nat_lt (n : ℕ) : lgG x + n < gq 1 x := by
  have hq := (gm1_facts hx hx1).2.2.2
  exact (inE_indec hq).add_lt (mg_lgG_lt_G1 hx hx1) ((natCast_lt_omega0 n).trans (omega0_lt_inE hq))

/-- **`ϑˣ(Ω₁·2 + Γ_{x+1} + n) = Z_{n+1}(x) = ζ_{Γ_{x+1}+n+1}`.** -/
theorem gz_glA2 : ∀ n : ℕ, glA 2 (lgG x + n) x = gwZn x (n + 1)
  | 0 => by rw [Nat.cast_zero, add_zero]; exact gw_glA2_eq hx hx1
  | n + 1 => by
    have hq := gz_G_nat_lt hx hx1 (n + 1)
    rw [Nat.cast_succ, ← add_assoc] at hq ⊢
    rw [gz_glA2_succ hx hx1 hq, gz_glA2 n]
    rfl

end Base

section Pi

variable {σ ρ : Ordinal.{0}} (hB : Bases σ ρ)
include hB

/-- **Lemma EXACT for `Z_n(ρ)`**: `π_{σ,ρ}(ζ_{Γ_{ρ+1}+n}) = ζ_{Γ_{σ+1}+n}`. -/
theorem gz_Z_pi : ∀ n : ℕ, gwZn ρ n ∈ TB ρ σ ∧ pi σ ρ (gwZn ρ n) = gwZn σ n
  | 0 => Go.goGl.ba_pi σ ρ hB
  | n + 1 => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have h2σ : (2 : Ordinal.{0}) < σ :=
      (show (2 : Ordinal.{0}) < ω from nat_lt_omega0 2).trans (omega0_lt_inE hB.1)
    have hnσ : (n : Ordinal.{0}) < σ := (natCast_lt_omega0 n).trans (omega0_lt_inE hB.1)
    obtain ⟨g1, g2⟩ : lgG ρ ∈ TB ρ σ ∧ pi σ ρ (lgG ρ) = lgG σ := Go.goGl.ba_pi σ ρ hB
    obtain ⟨s1, s2⟩ := pi_add hB g1 (mem_TB_of_lt hB hnσ)
    rw [g2, pi_lt hB hnσ] at s2
    have hs1 : lgG ρ + n < Om1 := (gm1_T hB.2.1 hρ1 (gz_G_nat_lt hB.2.1 hρ1 n)).2
    have h := glA_pi hB (mem_TB_of_lt hB h2σ) (gw_two_T hB.2.1 hρ1).2 s1 hs1
    rw [pi_lt hB h2σ, s2, gz_glA2 hB.2.1 hρ1 n, gz_glA2 hB.1 hσ1 n] at h
    exact h

/-- **Lemma EXACT for `ε_{Z_n(ρ)+1}`.** -/
theorem gz_eNZ_pi (n : ℕ) : eN (gwZn ρ n) ∈ TB ρ σ ∧ pi σ ρ (eN (gwZn ρ n)) = eN (gwZn σ n) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨z1, z2⟩ := gz_Z_pi hB n
  obtain ⟨o1, o2⟩ := one_TB hB
  have h := glA_pi hB o1 (gl_one_T hB.2.1 hρ1).2 z1 (gm1_T hB.2.1 hρ1 (gwZn_lt hB.2.1 hρ1 n)).2
  rw [o2, z2, ← gz_eNZ hB.2.1 hρ1, ← gz_eNZ hB.1 hσ1] at h
  exact h

/-- **Lemma EXACT for `ε_{Z_n+1+ν}`** at the pseudo-base `Z_n(ρ)`. -/
theorem gz_evAZ_pi (n : ℕ) {ν : Ordinal.{0}} (hνT : ν ∈ TB ρ σ) (hν : ν < gwZn ρ (n + 1))
    (hν' : pi σ ρ ν < gwZn σ (n + 1)) :
    evA (gwZn ρ n) (1 + ν) ∈ TB ρ σ ∧ pi σ ρ (evA (gwZn ρ n) (1 + ν)) = evA (gwZn σ n) (1 + pi σ ρ ν) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨o1, o2⟩ := one_TB hB
  obtain ⟨z1, z2⟩ := gz_Z_pi hB n
  obtain ⟨s1, s2⟩ := pi_add hB z1 hνT
  rw [z2] at s2
  have hν0 : ν < evZ (gwZn ρ n) := hν
  have hq : gwZn ρ n + ν < gq 1 ρ := (add_lt_evZ (lt_evZ _) hν0).trans (gwZn_lt hB.2.1 hρ1 (n + 1))
  have hs1 : gwZn ρ n + ν < Om1 := (gm1_T hB.2.1 hρ1 hq).2
  have h := glA_pi hB o1 (gl_one_T hB.2.1 hρ1).2 s1 hs1
  rw [o2, s2, gz_glAZ hB.2.1 hρ1 n hν, gz_glAZ hB.1 hσ1 n hν'] at h
  exact h

/-- **Lemma EXACT for `φ(1, Z_{n+1}(ρ) + ν(ρ))`** (`ω ≤ ν(ρ) < Z_{n+2}(ρ)`, `π(ν(ρ)) = ν(σ) < Z_{n+2}(σ)`). -/
theorem gz_b_pi_Z (n : ℕ) {ν ν' : Ordinal.{0}} (hνT : ν ∈ TB ρ σ) (hν : ν < gwZn ρ (n + 2))
    (hν' : ν' < gwZn σ (n + 2)) (hω : ω ≤ ν) (hπ : pi σ ρ ν = ν') :
    veblen 1 (gwZn ρ (n + 1) + ν) ∈ TB ρ σ ∧
      pi σ ρ (veblen 1 (gwZn ρ (n + 1) + ν)) = veblen 1 (gwZn σ (n + 1) + ν') := by
  obtain ⟨e1, e2⟩ := gz_evAZ_pi hB (n + 1) hνT hν (by rw [hπ]; exact hν')
  have hωσ : ω < σ := omega0_lt_inE hB.1
  have hωT : ω ∈ TB ρ σ := mem_TB_of_lt hB hωσ
  have hω' : ω ≤ ν' := by
    rw [← hπ, ← pi_lt hB hωσ]
    exact ((pi_bijOn hB).2.le_iff_le hωT hνT).2 hω
  rw [hπ, one_add_of_omega0_le hω'] at e2
  rw [one_add_of_omega0_le hω] at e1 e2
  rw [gz_Zs ρ n, gz_Zs σ n, gw_veb_Z, gw_veb_Z]
  exact ⟨e1, e2⟩

end Pi

end Googology.Trans.PoR.InaccPsi.R2.Gz
