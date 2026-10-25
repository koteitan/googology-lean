import Googology.Trans.PoR.InaccPsi.R2.HcWRec

/-!
# HdLev: THE LEVEL FACTS AT THE VEBLEN LEVEL `ω` USED BY THE GATED OFFSET RECURSION

The offsets `λ` of a base `F` of level `ω` (a fixed point of `φ(ω, ·)`) give the points `Q_λ = φ(ω, F + 1 + λ)`, read
at a base `x` as `ϑˣ(Ω₁·ω + F(x) + λ(x))`.  Here are the facts about these readings that the recursion uses:

* `hd_cl_lev` (**a code in `[φ(a, j), φ(a, j+1))` forces `j` to be a code**, every level `a ≥ 1`; `Hb.hb_cl_lev` was
  stated for finite levels only);
* at an `ε`-number base `x`: `hd_glA_P`, `hd_glA_fix` (`ϑˣ(Ω₁·ω + t)` is a value of `φ(ω, ·)`, hence a fixed point of
  every `φ(k, ·)`), `hd_glA_succ` (**`ϑˣ(Ω₁·ω + t + 1) = hcS(ϑˣ(Ω₁·ω + t))`**), `hd_lvglAV` (**the closed form
  `ϑˣ(Ω₁·ω + P + r) = φ(ω, i₀ + r)` with `φ(ω, i₀) = hcS(P)`** below `N_ω(P)`), `hd_glA_lt`
  (`ϑˣ(Ω₁·ω + P + r) < N_ω(P)` for `r < N_ω(P)`);
* `hdNw_veb` (`N_ω(φ(ω+1, a)) = φ(ω+1, a+1)`), `hdNw_fix2`, `hdNw_fix1`.

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hd

open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **A code in `[φ(a, j), φ(a, j+1))` forces `j` to be a code** (`a ≥ 1`, `j` not a fixed point of `φ(a, ·)`,
`G < φ(a, j)`). -/
theorem hd_cl_lev {a : Ordinal.{0}} (ha : 1 ≤ a) {Z j : Ordinal.{0}} (hZ1 : Z ≤ Om 1) (hj : j < veblen a j)
    (hGQ : gcG 0 < veblen a j) {y : Ordinal.{0}} (hy : GxCl Z {gcG 0} y)
    (hQy : veblen a j ≤ y) (hyZ : y < veblen a (j + 1)) : GxCl Z {gcG 0} j := by
  have hFE : InE (veblen a j) := gg_veblen_eps (Order.one_le_iff_ne_zero.1 ha)
  have hOF : Om 1 < veblen a j := (gcG_Om1_lt 0).trans hGQ
  induction hy with
  | small h => exact absurd (hQy.trans_lt (h.trans_le hZ1)) (not_lt.2 hOF.le)
  | om => exact absurd hQy (not_le.2 hOF)
  | atom h =>
    rw [Set.mem_singleton_iff] at h
    rw [h] at hQy; exact absurd hQy (not_le.2 hGQ)
  | @add u v hu hv ihu ihv =>
    rcases le_or_gt (veblen a j) u with hFu | huF
    · exact ihu hFu (lt_of_le_of_lt le_self_add hyZ)
    · rcases le_or_gt (veblen a j) v with hFv | hvF
      · exact ihv hFv (lt_of_le_of_lt le_add_self hyZ)
      · exact absurd hQy (not_le.2 ((inE_indec hFE).add_lt huF hvF))
  | @phi c b hc hb ihc ihb =>
    have hbyZ : b < veblen a (j + 1) := lt_of_le_of_lt (right_le_veblen c b) hyZ
    rcases lt_or_ge c a with hca | hca
    · refine ihb ?_ hbyZ
      refine not_lt.1 fun hbF => ?_
      have hlt : veblen c b < veblen a j := by
        have h1 : veblen c b < veblen c (veblen a j) := (isNormal_veblen c).strictMono hbF
        rwa [veblen_veblen_of_lt hca] at h1
      exact absurd hQy (not_le.2 hlt)
    · rcases hca.lt_or_eq with hca' | hca'
      · exfalso
        have e3 : veblen a (veblen c b) = veblen c b := veblen_veblen_of_lt hca' b
        have h1 : j ≤ veblen c b := by
          have : veblen a j ≤ veblen a (veblen c b) := by rw [e3]; exact hQy
          exact (isNormal_veblen _).strictMono.le_iff_le.1 this
        have h2 : veblen c b < j + 1 := by
          have : veblen a (veblen c b) < veblen a (j + 1) := by rw [e3]; exact hyZ
          exact (isNormal_veblen _).strictMono.lt_iff_lt.1 this
        have e : veblen c b = j := le_antisymm (Order.lt_add_one_iff.1 h2) h1
        have : veblen a j = j := by rw [← e]; exact e3
        exact absurd this hj.ne'
      · subst hca'
        have h1 : j ≤ b := (isNormal_veblen _).strictMono.le_iff_le.1 hQy
        have h2 : b < j + 1 := (isNormal_veblen _).strictMono.lt_iff_lt.1 hyZ
        have : b = j := le_antisymm (Order.lt_add_one_iff.1 h2) h1
        rw [← this]; exact hb

/-- **`N_ω(φ(ω+1, a)) = φ(ω+1, a+1)`.** -/
theorem hdNw_veb (a : Ordinal.{0}) : hcNw (veblen (ω + 1) a) = veblen (ω + 1) (a + 1) := hcN_veb ω a

theorem hdNw_fix2 (Q : Ordinal.{0}) : veblen 2 (hcNw Q) = hcNw Q := by
  have := hc_fixW_k (hcNw_fix Q) 2; rwa [show ((2 : ℕ) : Ordinal.{0}) = 2 by norm_num] at this

theorem hdNw_fix1 (Q : Ordinal.{0}) : veblen 1 (hcNw Q) = hcNw Q := ha_fix1_of_fix2 (hdNw_fix2 Q)

theorem hdS_fix1 (Q : Ordinal.{0}) : veblen 1 (hcS Q) = hcS Q := by
  have := hcS_veb 1 Q; rwa [Nat.cast_one] at this

theorem hdS_fix2 (Q : Ordinal.{0}) : veblen 2 (hcS Q) = hcS Q := by
  have := hcS_veb 2 Q; rwa [show ((2 : ℕ) : Ordinal.{0}) = 2 by norm_num] at this

/-- **`φ(ω, a)` is a fixed point of every `φ(k, ·)`.** -/
theorem hd_veb_fix (k : ℕ) (a : Ordinal.{0}) : veblen (k : Ordinal.{0}) (veblen ω a) = veblen ω a :=
  veblen_veblen_of_lt (natCast_lt_omega0 k) a

theorem hd_veb_fix1 (a : Ordinal.{0}) : veblen 1 (veblen ω a) = veblen ω a :=
  veblen_veblen_of_lt one_lt_omega0 a

/-- **`hcS(Q) < N_ω(P)`** for `Q < N_ω(P)`. -/
theorem hdS_lt_Nw {P Q : Ordinal.{0}} (hQ : Q < hcNw P) : hcS Q < hcNw P := by
  have h1 : hcS Q ≤ veblen ω (Q + 1) := hcS_le (hd_veb_fix · (Q + 1)) ((lt_add_one Q).trans_le (right_le_veblen _ _))
  have h2 := (isNormal_veblen ω).strictMono ((hcNw_lim P).add_one_lt hQ)
  rw [hcNw_fix] at h2
  exact h1.trans_lt h2

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem hd_glA_P {t : Ordinal.{0}} (ht : t < gq 1 x) : LuP ω (glA ω t x) := by
  obtain ⟨htT, ht1⟩ := gm1_T hx hx1 ht
  obtain ⟨hωT, hω1⟩ := hc_om_T hx hx1
  exact glA_P hx hx1 hc_one_le_om hωT hω1 htT ht1

/-- **`ϑˣ(Ω₁·ω + t)` is a fixed point of every `φ(k, ·)`.** -/
theorem hd_glA_fix (k : ℕ) {t : Ordinal.{0}} (ht : t < gq 1 x) :
    veblen (k : Ordinal.{0}) (glA ω t x) = glA ω t x := hc_LuPw_iff.1 (hd_glA_P hx hx1 ht) k

theorem hd_glA_fix1 {t : Ordinal.{0}} (ht : t < gq 1 x) : veblen 1 (glA ω t x) = glA ω t x := by
  have := hd_glA_fix hx hx1 1 ht; rwa [Nat.cast_one] at this

/-- **`ϑˣ(Ω₁·ω + t + 1) = hcS(ϑˣ(Ω₁·ω + t))`.** -/
theorem hd_glA_succ {t : Ordinal.{0}} (ht : t + 1 < gq 1 x) : glA ω (t + 1) x = hcS (glA ω t x) := by
  obtain ⟨i, hi⟩ := hd_glA_P hx hx1 ((lt_add_one t).trans ht)
  rw [hc_glA_succV hx hx1 hc_one_le_om (hc_om_q hx hx1) ht hi.symm, ← hcS_veb_eq, hi]

theorem hd_glA_facts {t : Ordinal.{0}} (ht : t < gq 1 x) :
    x < glA ω t x ∧ glA ω t x < Om1 ∧ t < glA ω t x := by
  obtain ⟨htT, ht1⟩ := gm1_T hx hx1 ht
  obtain ⟨hωT, hω1⟩ := hc_om_T hx hx1
  obtain ⟨-, hxa, ha1, -, -, hta⟩ := glA_facts hx hx1 hc_one_le_om hωT hω1 htT ht1
  exact ⟨hxa, ha1, hta⟩

/-- **THE CLOSED FORM BELOW `N_ω(P)`**: `ϑˣ(Ω₁·ω + P) = hcS(P)` (a fixed point `P` of `φ(ω, ·)`), `φ(ω, i₀) =
hcS(P)` ⇒ `ϑˣ(Ω₁·ω + P + r) = φ(ω, i₀ + r)` for `r < N_ω(P)`. -/
theorem hd_lvglAV {P r i0 : Ordinal.{0}} (hP0 : glA ω P x = hcS P) (hPq : P < gq 1 x) (hNq : hcNw P < gq 1 x)
    (hi0 : veblen ω i0 = hcS P) (hr : r < hcNw P) : glA ω (P + r) x = veblen ω (i0 + r) := by
  have hNE := hcNw_E P
  have hSN : hcS P < hcNw P := hdS_lt_Nw (hcNw_gt P)
  have hi0H : i0 < hcNw P := (right_le_veblen ω i0).trans_lt (by rw [hi0]; exact hSN)
  have hir : i0 + r < hcNw P := (inE_indec hNE).add_lt hi0H hr
  have hlt : veblen ω (i0 + r) < hcNw P := by
    have := (isNormal_veblen ω).strictMono hir; rwa [hcNw_fix] at this
  have hrq : P + r < gq 1 x := (inE_indec (gm1_facts hx hx1).2.2.2).add_lt hPq (hr.trans hNq)
  have hPi : P < veblen ω i0 := by rw [hi0]; exact hcS_gt P
  exact hc_glAV hx hx1 hc_one_le_om (hc_om_q hx hx1) hPq (by rw [hP0, hi0]) r hrq (fun ν' h' _ =>
    hc_nofixW hPi le_self_add (((isNormal_veblen _).monotone ((add_le_add_iff_left _).2 h')).trans_lt hlt))

/-- **`ϑˣ(Ω₁·ω + P + r) < N_ω(P)`** for `r < N_ω(P)`. -/
theorem hd_glA_lt {P r : Ordinal.{0}} (hP0 : glA ω P x = hcS P) (hPq : P < gq 1 x) (hNq : hcNw P < gq 1 x)
    (hr : r < hcNw P) : glA ω (P + r) x < hcNw P := by
  obtain ⟨i0, hi0⟩ := hcS_LuP P
  rw [hd_lvglAV hx hx1 hP0 hPq hNq hi0 hr]
  have hNE := hcNw_E P
  have hi0H : i0 < hcNw P := (right_le_veblen ω i0).trans_lt (by
    rw [hi0]; exact hdS_lt_Nw (hcNw_gt P))
  have hir : i0 + r < hcNw P := (inE_indec hNE).add_lt hi0H hr
  have := (isNormal_veblen ω).strictMono hir; rwa [hcNw_fix] at this

end Base

end Googology.Trans.PoR.InaccPsi.R2.Hd
