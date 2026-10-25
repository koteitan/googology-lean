import Googology.Trans.PoR.InaccPsi.R2.GzZb

/-!
# THE INDICES `ζ_{G+n} + d`, `d < ζ_{G+n+1}`, GENERIC IN `n`

`R2.GwYCl` treats the indices above `ζ_{G+1}`.  The same facts hold above every `ζ_{G+n}` (`Gz.gzZ`):

* `gzY_lt_veb` (**`ζ_{G+n} + d < φ(1, ζ_{G+n} + d)` for `0 < d < ζ_{G+n+1}`**), `gzY_self_lt`, `gzY_veb_lt_Z`,
  `gzY_veb_lt1`, `gzY_cover` (**`0 < μ < ζ_{G+n+1}` ⇒ `μ < φ(1, ζ_{G+n} + d)` for some `d < μ`**), `gzY_G_lt_B`;
* `gzY_cl_gate` (**THE CODE-GATE CONDITION OF AN INDEX ABOVE `ζ_{G+n}`**: `φ(1, ζ_{G+n} + c)` a code over a strongly
  critical `Z ≤ Ω₁` and `c` a code of `E` ⇒ `g_E(c) < Z`; through `Gw.gwY_cl_of_add` at `P = ζ_{G+n}`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gz

open Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx

section Idx

variable (n : ℕ)

/-- **`ζ_{G+n} + d < φ(1, ζ_{G+n} + d)` for `0 < d < ζ_{G+n+1}`.** -/
theorem gzY_lt_veb {d : Ordinal.{0}} (hd0 : 0 < d) (hd : d < gzZ (n + 1)) :
    gzZ n + d < veblen 1 (gzZ n + d) := by
  rcases (right_le_veblen 1 (gzZ n + d)).lt_or_eq with h | h
  · exact h
  · exfalso
    have hfix : Ordinal.epsilon (gzZ n + d) = gzZ n + d := h.symm
    have h1 := evZ_le (lt_add_of_pos_right (gzZ n) hd0) hfix
    exact absurd (add_lt_evZ (gzZ_lt_succ n) hd) (not_lt.2 h1)

theorem gzY_self_lt {d : Ordinal.{0}} (hd : d < gzZ (n + 1)) : d < veblen 1 (gzZ n + d) := by
  rcases eq_or_ne d 0 with rfl | hd0
  · rw [add_zero]; exact (gzZ_E n).pos.trans_le (right_le_veblen 1 _)
  · exact (le_add_self : d ≤ gzZ n + d).trans_lt (gzY_lt_veb n (pos_iff_ne_zero.2 hd0) hd)

theorem gzY_veb_lt_Z {d : Ordinal.{0}} (hd : d < gzZ (n + 1)) : veblen 1 (gzZ n + d) < gzZ (n + 1) := by
  have := (isNormal_veblen 1).strictMono (add_lt_evZ (gzZ_lt_succ n) hd)
  rwa [show veblen 1 (evZ (gzZ n)) = evZ (gzZ n) from epsilon_evZ _] at this

theorem gzY_veb_lt1 {d : Ordinal.{0}} (hd : d < gzZ (n + 1)) : veblen 1 (gzZ n + d) < gcG 1 :=
  (gzY_veb_lt_Z n hd).trans (gzZ_lt1 (n + 1))

/-- **`0 < μ < ζ_{G+n+1}` ⇒ `μ < φ(1, ζ_{G+n} + d)` for some `d < μ`.** -/
theorem gzY_cover {μ : Ordinal.{0}} (hμ0 : 0 < μ) (hμ : μ < gzZ (n + 1)) :
    ∃ d, d < μ ∧ μ < veblen 1 (gzZ n + d) := by
  rcases zero_or_succ_or_isSuccLimit μ with h0 | ⟨d, hd⟩ | hlim
  · exact absurd h0 hμ0.ne'
  · have hd' : μ = d + 1 := by rw [← hd, Order.succ_eq_add_one]
    have hdμ : d < μ := by rw [hd']; exact lt_add_one d
    refine ⟨d, hdμ, ?_⟩
    rw [hd']
    exact (ev_isSuccLimit_of_inE (omega0_opow_epsilon _)).add_one_lt (gzY_self_lt n (hdμ.trans hμ))
  · have h := gzY_self_lt n hμ
    obtain ⟨t, ht, hμt⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 h
    obtain ⟨d, hd, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    exact ⟨d, hd, hμt.trans_le ((isNormal_veblen 1).monotone htd)⟩

theorem gzY_G_lt_B {l : Ordinal.{0}} (hl : 0 < l) : gcG 0 < veblen 1 (gzZ n + l) :=
  ((gzZ_G_le n).trans_lt (lt_add_of_pos_right _ hl)).trans_le (right_le_veblen 1 _)

/-- **THE CODE-GATE CONDITION OF AN INDEX ABOVE `ζ_{G+n}`**: if `φ(1, ζ_{G+n} + c)` is a code over a strongly
critical `Z ≤ Ω₁` and `c` (`0 < c < ζ_{G+n+1}`) is a code of `E`, then `g_E(c) < Z`. -/
theorem gzY_cl_gate (E : GwZD) {c Z : Ordinal.{0}} (hcB : c < E.B) (hc0 : 0 < c) (hcZ : c < gzZ (n + 1))
    (hZ : SC Z) (hZ1 : Z ≤ Om 1) (h : GxCl Z {gcG 0} (veblen 1 (gzZ n + c))) : E.g c < Z := by
  have hGZ : gcG 0 ≤ gzZ n := gzZ_G_le n
  have hOt : Om 1 < gzZ n + c := ((gcG_Om1_lt 0).trans_le hGZ).trans_le le_self_add
  have h1 := gr_cl_veb1 hZ1 hOt (gzY_lt_veb n hc0 hcZ) h
  have h2 := gwY_cl_of_add hZ hZ1 (gzZ_E n) hGZ (gzZ_cl hZ n) h1
  have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1
  exact E.code_gate Z hZ1' hZ.1 (fun _ _ hu hv => hZ.isPrincipal hu hv) (fun _ _ hu hv => hZ.2 _ hu _ hv)
    {gcG 0} (fun s hs => Or.inl (Set.mem_singleton_iff.1 hs)) c h2 hcB

end Idx

end Googology.Trans.PoR.InaccPsi.R2.Gz
