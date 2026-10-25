import Googology.Trans.PoR.InaccPsi.R2.GwZU
import Googology.Trans.PoR.InaccPsi.R2.GwCl

/-!
# THE INDEX OF A BOUND ABOVE `ζ_{G+1}` IS A CODE; THE INDICES BELOW `ζ_{G+2}`

`Gw.gw_cl_of_G_add` reads `c` from a code `G + c` through the remainder modulo the atom `G`.  The same works modulo
any `ε`-number `P ≥ G` (`gwY_cl_mod`, `gwY_cl_of_add`): for `P = ζ_{G+1}` a code `ζ_{G+1} + c` gives the code `c`, so
the code-gate condition of a union at an index `ζ_{G+1} + λ` is the code-gate condition of `λ` (`gwY_cl_gate`).
The indices `ζ_{G+1} + d`, `0 < d < ζ_{G+2}`, are not `ε`-fixed points (`gwY_lt_veb`), each `d` lies below
`φ(1, ζ_{G+1} + d')` for some `d' < d` (`gwY_cover`), and `φ(1, ζ_{G+1} + d) < Γ_{Ω₁+2}` (`gwY_veb_lt1`).

* `gwY_cl_mod`, `gwY_cl_of_add`, `gwZ_cl` (`ζ_{G+1}` is a code over every strongly critical `Z`), `gwY_lt_veb`,
  `gwY_self_lt`, `gwY_veb_lt_Z`, `gwY_veb_lt1`, `gwY_cover`, `gwY_cl_gate`, `gwZ_mem` (`ζ_{G+1}` lies in every
  hull `C(a, b)`, `0 < a`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gw

open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx

section Cl

variable {Z P : Ordinal.{0}}

theorem gwY_mod_eq (hP0 : 0 < P) {q r : Ordinal.{0}} (hr : r < P) : (P * q + r) % P = r := by
  rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]

theorem gwY_dvd_prin (hPE : InE P) {v : Ordinal.{0}} (hp : IsPrincipal (· + ·) v) (hv0 : v ≠ 0) (hPv : P ≤ v) :
    v % P = 0 := by
  obtain ⟨e, he⟩ := Bt.prin_eq_opow hp hv0
  have hPe : P ≤ e := by
    by_contra hlt
    push Not at hlt
    have := (opow_lt_opow_iff_right one_lt_omega0).2 hlt
    rw [hPE, ← he] at this
    exact absurd hPv (not_le.2 this)
  have hd := opow_dvd_opow ω hPe
  rw [hPE, ← he] at hd
  exact (Ordinal.dvd_iff_mod_eq_zero).1 hd

/-- **The remainder of a code modulo an `ε`-number `P ≥ G` is a code.** -/
theorem gwY_cl_mod (hZ : SC Z) (hZ1 : Z ≤ Om 1) (hPE : InE P) (hGP : gcG 0 ≤ P) {y : Ordinal.{0}}
    (h : GxCl Z {gcG 0} y) : GxCl Z {gcG 0} (y % P) := by
  have hOP : Om 1 < P := (gcG_Om1_lt 0).trans_le hGP
  have hP0 : 0 < P := hPE.pos
  have hPp : IsPrincipal (· + ·) P := by
    have := isPrincipal_add_omega0_opow P
    rwa [hPE] at this
  induction h with
  | @small x hx => rw [Ordinal.mod_eq_of_lt ((hx.trans_le hZ1).trans hOP)]; exact GxCl.small hx
  | om => rw [Ordinal.mod_eq_of_lt hOP]; exact GxCl.om
  | @atom s hs =>
    rw [Set.mem_singleton_iff] at hs
    subst hs
    rcases hGP.lt_or_eq with hlt | heq
    · rw [Ordinal.mod_eq_of_lt hlt]; exact GxCl.atom (Set.mem_singleton _)
    · rw [← heq, Ordinal.mod_self]; exact GxCl.zero hZ.1
  | @add x y _ hy ihx ihy =>
    have hx' := Ordinal.div_add_mod x P
    have hy' := Ordinal.div_add_mod y P
    have hr : x % P < P := Ordinal.mod_lt x hP0.ne'
    rcases lt_or_ge y P with hyP | hyP
    · have e : x + y = P * (x / P) + (x % P + y) := by
        conv_lhs => rw [← hx']
        rw [add_assoc]
      rw [e, gwY_mod_eq hP0 (hPp hr hyP)]
      exact GxCl.add ihx hy
    · have hq : 1 ≤ y / P := by
        rw [Order.one_le_iff_pos]
        exact Ordinal.div_pos hP0.ne' |>.2 hyP
      obtain ⟨b', hb'⟩ := exists_add_of_le hq
      have hs : y % P < P := Ordinal.mod_lt y hP0.ne'
      have e1 : x % P + P * (1 + b') = P * (1 + b') := by
        rw [mul_add, mul_one, ← add_assoc, hPp.add_eq_right hr]
      have e : x + y = P * (x / P + y / P) + y % P := by
        conv_lhs => rw [← hx', ← hy']
        rw [hb', ← add_assoc (P * (x / P) + x % P), add_assoc (P * (x / P)) (x % P), e1, ← mul_add]
      rw [e, gwY_mod_eq hP0 hs]
      exact ihy
  | @phi a b ha hb _ _ =>
    rcases lt_or_ge (veblen a b) P with hv | hv
    · rw [Ordinal.mod_eq_of_lt hv]; exact GxCl.phi ha hb
    · rw [gwY_dvd_prin hPE (gr_veb_prin a b) veblen_pos.ne' hv]; exact GxCl.zero hZ.1

/-- **`P + c` a code (`P ≥ G` an `ε`-number and a code) ⇒ `c` a code.** -/
theorem gwY_cl_of_add (hZ : SC Z) (hZ1 : Z ≤ Om 1) (hPE : InE P) (hGP : gcG 0 ≤ P) (hPc : GxCl Z {gcG 0} P)
    {c : Ordinal.{0}} (h : GxCl Z {gcG 0} (P + c)) : GxCl Z {gcG 0} c := by
  have hP0 : 0 < P := hPE.pos
  rcases le_or_gt (P * ω) c with hc | hc
  · rwa [add_eq_right_iff_mul_omega0_le.2 hc] at h
  · have hc' := Ordinal.div_add_mod c P
    have hs : c % P < P := Ordinal.mod_lt c hP0.ne'
    have hq : c / P < ω := (Ordinal.lt_mul_iff_div_lt hP0.ne').1 hc
    obtain ⟨n, hn⟩ := lt_omega0.1 hq
    have e : P + c = P * (1 + c / P) + c % P := by
      conv_lhs => rw [← hc']
      rw [mul_add, mul_one, add_assoc]
    have hm := gwY_cl_mod hZ hZ1 hPE hGP h
    rw [e, gwY_mod_eq hP0 hs] at hm
    have hPn : ∀ k : ℕ, GxCl Z {gcG 0} (P * k) := fun k => by
      induction k with
      | zero => rw [Nat.cast_zero, mul_zero]; exact GxCl.zero hZ.1
      | succ k ih => rw [Nat.cast_succ, mul_add_one]; exact GxCl.add ih hPc
    rw [← hc', hn]
    exact GxCl.add (hPn n) hm

end Cl

/-- **`ζ_{G+1} = φ(2, G+1)` is a code over every strongly critical `Z`.** -/
theorem gwZ_cl {Z : Ordinal.{0}} (hZ : SC Z) : GxCl Z {gcG 0} gwZ := by
  rw [gwZ_eq_veb2]
  have h2 : GxCl Z {gcG 0} (2 : Ordinal.{0}) := by
    have h1 : GxCl Z {gcG 0} (1 : Ordinal.{0}) := GxCl.small (gw_one_lt_SC hZ)
    have := GxCl.add h1 h1
    rwa [one_add_one_eq_two] at this
  have hG1 : GxCl Z {gcG 0} (gcG 0 + 1) := GxCl.add (GxCl.atom (Set.mem_singleton _)) (GxCl.small (gw_one_lt_SC hZ))
  exact GxCl.phi h2 hG1

/-- **`ζ_{G+1}` lies in every hull `C(a, b)` with `0 < a`.** -/
theorem gwZ_mem (S : InaccSeq.{0}) {a b : Ordinal.{0}} (ha : 0 < a) : gwZ ∈ S.CSet a b := by
  rw [gwZ_eq_veb2]
  exact CSet.phi_mem (gr_cst_mem ha b 2 (gw_two_lt_w.trans (omega0_lt_gamma 1))) (CSet.succ_mem (gmS_G0_mem S ha))

theorem gwY_Z_lt : gwZ < evZ gwZ := lt_evZ _

/-- **`ζ_{G+1} + d < φ(1, ζ_{G+1} + d)` for `0 < d < ζ_{G+2}`.** -/
theorem gwY_lt_veb {d : Ordinal.{0}} (hd0 : 0 < d) (hd : d < evZ gwZ) : gwZ + d < veblen 1 (gwZ + d) := by
  rcases (right_le_veblen 1 (gwZ + d)).lt_or_eq with h | h
  · exact h
  · exfalso
    have hfix : Ordinal.epsilon (gwZ + d) = gwZ + d := h.symm
    have h1 := evZ_le (lt_add_of_pos_right gwZ hd0) hfix
    exact absurd (add_lt_evZ gwY_Z_lt hd) (not_lt.2 h1)

theorem gwY_self_lt {d : Ordinal.{0}} (hd : d < evZ gwZ) : d < veblen 1 (gwZ + d) := by
  rcases eq_or_ne d 0 with rfl | hd0
  · rw [add_zero]; exact gwZ_E.pos.trans_le (right_le_veblen 1 _)
  · exact (le_add_self : d ≤ gwZ + d).trans_lt (gwY_lt_veb (pos_iff_ne_zero.2 hd0) hd)

theorem gwY_veb_lt_Z {d : Ordinal.{0}} (hd : d < evZ gwZ) : veblen 1 (gwZ + d) < evZ gwZ := by
  have := (isNormal_veblen 1).strictMono (add_lt_evZ gwY_Z_lt hd)
  rwa [show veblen 1 (evZ gwZ) = evZ gwZ from epsilon_evZ _] at this

theorem gwY_Z_lt1 : evZ gwZ < gcG 1 := by
  have hE := Low.opow_eq_self_of_SC (gcG_SC 1)
  refine lt_of_le_of_ne (evZ_le gwZ_lt_G1 (gn_veb_fix (gcG_SC 1) (one_lt_omega0.trans (omega0_lt_inE hE)))) ?_
  intro e
  have h2 : veblen 2 (gwZ + 1) < gcG 1 :=
    (gcG_SC 1).2 2 (gw_two_lt_G.trans (gcG_lt zero_lt_one)) _ ((gcG_SC 1).add_one_lt gwZ_lt_G1)
  have h3 : evZ gwZ ≤ veblen 2 (gwZ + 1) := by
    have hlt : gwZ < veblen 2 (gwZ + 1) :=
      (lt_add_one gwZ).trans_le (right_le_veblen 2 _)
    exact evZ_le hlt (veblen_veblen_of_lt one_lt_two _)
  rw [e] at h3
  exact absurd (h3.trans_lt h2) (lt_irrefl _)

theorem gwY_veb_lt1 {d : Ordinal.{0}} (hd : d < evZ gwZ) : veblen 1 (gwZ + d) < gcG 1 :=
  (gwY_veb_lt_Z hd).trans gwY_Z_lt1

/-- **`0 < μ < ζ_{G+2}` ⇒ `μ < φ(1, ζ_{G+1} + d)` for some `d < μ`.** -/
theorem gwY_cover {μ : Ordinal.{0}} (hμ0 : 0 < μ) (hμ : μ < evZ gwZ) :
    ∃ d, d < μ ∧ μ < veblen 1 (gwZ + d) := by
  rcases zero_or_succ_or_isSuccLimit μ with h0 | ⟨d, hd⟩ | hlim
  · exact absurd h0 hμ0.ne'
  · have hd' : μ = d + 1 := by rw [← hd, Order.succ_eq_add_one]
    have hdμ : d < μ := by rw [hd']; exact lt_add_one d
    refine ⟨d, hdμ, ?_⟩
    rw [hd']
    exact (ev_isSuccLimit_of_inE (omega0_opow_epsilon _)).add_one_lt (gwY_self_lt (hdμ.trans hμ))
  · have h := gwY_self_lt hμ
    obtain ⟨t, ht, hμt⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 h
    obtain ⟨d, hd, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    exact ⟨d, hd, hμt.trans_le ((isNormal_veblen 1).monotone htd)⟩

/-- **THE CODE-GATE CONDITION OF AN INDEX ABOVE `ζ_{G+1}`**: if `φ(1, ζ_{G+1} + c)` is a code over a strongly critical
`Z ≤ Ω₁` and `c` (`0 < c < ζ_{G+2}`) is a code of `E`, then `g_E(c) < Z`. -/
theorem gwY_cl_gate (E : GwZD) {c Z : Ordinal.{0}} (hcB : c < E.B) (hc0 : 0 < c) (hcZ : c < evZ gwZ)
    (hZ : SC Z) (hZ1 : Z ≤ Om 1) (h : GxCl Z {gcG 0} (veblen 1 (gwZ + c))) : E.g c < Z := by
  have hGZ : gcG 0 ≤ gwZ := gw_G_lt_Z.le
  have hOt : Om 1 < gwZ + c := ((gcG_Om1_lt 0).trans_le hGZ).trans_le le_self_add
  have h1 := gr_cl_veb1 hZ1 hOt (gwY_lt_veb hc0 hcZ) h
  have h2 := gwY_cl_of_add hZ hZ1 gwZ_E hGZ (gwZ_cl hZ) h1
  have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1
  exact E.code_gate Z hZ1' hZ.1 (fun _ _ hu hv => hZ.isPrincipal hu hv) (fun _ _ hu hv => hZ.2 _ hu _ hv)
    {gcG 0} (fun s hs => Or.inl (Set.mem_singleton_iff.1 hs)) c h2 hcB

end Googology.Trans.PoR.InaccPsi.R2.Gw
