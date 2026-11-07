import Googology.Trans.PoR.InaccPsi.R2.QdNx
import Googology.Trans.PoR.InaccPsi.R2.QcCg

/-!
# QdCg: THE STEP OF A DIGIT SYSTEM FROM `B₂` ON READS `vD` WITH THE GATES `qdGt`

As `Qc.qc_sG`, `Qc.qc_sR`: a digit system `Qd.QdDS` at a base `E ∈ [B₂, B₃)` read by `vD` with the gates
`max Eg (qdGt c)` has its step `QdDS.step S` read by `vD` with the gates `max Eg (qdGt c)` on every code below `ε_{E+1}`
(the Cantor clauses `Qd.vD_cnf`, `Qd.qdGt_cnf`).

* `qd_maxQ`, `qd_sG` (**the gates of the step**), `qd_sR` (**the step reads `vD`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Yr
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Va
  Googology.Trans.PoR.InaccPsi.R2.Zm Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Qc

/-- **The gate of a part up to the finite ones**: `max g (qdGt a) = max g (qdQt a)` for `ω ≤ g`. -/
theorem qd_maxQ {g : Ordinal.{0}} (hω : ω ≤ g) (a : Ordinal.{0}) : max g (qdGt a) = max g (qdQt a) := by
  unfold qdQt
  split_ifs with ha
  · obtain ⟨n, rfl⟩ := lt_omega0.1 ha
    rw [qdGt_nat, max_eq_left ((natCast_lt_omega0 n).le.trans hω), max_eq_left zero_le]
  · rfl

section Step

variable (M : QdDS) (hω : ω ≤ M.Eg) (hQ : qdQEt M.E ≤ M.Eg) (hXE : ucB ≤ M.E)
  (hV : ∀ x, InE x → x < Om1 → M.Eg < x → M.V x = qdA M.E x)
  (hR : ∀ c, c < M.E → ∀ x, InE x → x < Om1 → M.G c < x → M.R c x = vD c x)
  (hG : ∀ c, c < M.E → c ≠ 0 → M.G c = max M.Eg (qdGt c))

include hω hQ hXE hG in
/-- **The gates of the step are `max Eg (qdGt c)`.** -/
theorem qd_sG : ∀ c, c < eN M.E → c ≠ 0 → M.sG c = max M.Eg (qdGt c) := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcN hc0
  rcases lt_or_ge c M.E with hcE | hcE
  · rw [M.sG_lt hcE]; exact hG c hcE hc0
  obtain ⟨hk0, hd0, hdE, hrk, hdec⟩ := zm_dec M.E_E hcE
  obtain ⟨hko, hro⟩ := M.parts_lt hcE hcN
  set k := log M.E c
  set d := c / M.E ^ k
  set r := c % M.E ^ k
  have hv : M.E ^ k * d + r < eN M.E := hdec ▸ hcN
  have hsG := M.sG_eq hk0 hd0.ne' hdE hrk hv
  have hyG := qdGt_cnf M.E_E hXE hk0.ne' hd0.ne' hdE hrk hv (hv.trans M.eN_lt_B3)
  rw [hdec] at hsG hyG
  rw [hsG, hyG, IH k hko (hko.trans hcN) hk0.ne', hG d hdE hd0.ne', qd_maxQ hω k, qd_maxQ hω d]
  rcases eq_or_ne r 0 with hr0 | hr0
  · rw [hr0, M.sG_zero, qdGt_zero]
    exact va_max3 hQ
  · rw [IH r hro (hro.trans hcN) hr0]
    exact va_max4 hQ

include hXE hV hR in
/-- **The step reads `vD`.** -/
theorem qd_sR : ∀ c, c < eN M.E → ∀ x, InE x → x < Om1 → M.Eg < x → M.sG c < x → M.sR c x = vD c x := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcN x hx hx1 hgx hg
  rcases lt_or_ge c M.E with hcE | hcE
  · rw [M.sR_lt hcE]; rw [M.sG_lt hcE] at hg; exact hR c hcE x hx hx1 hg
  obtain ⟨hk0, hd0, hdE, hrk, hdec⟩ := zm_dec M.E_E hcE
  obtain ⟨hko, hro⟩ := M.parts_lt hcE hcN
  set k := log M.E c
  set d := c / M.E ^ k
  set r := c % M.E ^ k
  have hv : M.E ^ k * d + r < eN M.E := hdec ▸ hcN
  have hsG := M.sG_eq hk0 hd0.ne' hdE hrk hv
  rw [hdec] at hsG
  rw [hsG] at hg
  have hgk : M.sG k < x := (le_max_left _ _).trans_lt hg
  have hgd : M.G d < x := (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hg)
  have hgr : M.sG r < x := (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hg)
  have hsR := M.sR_eq hk0 hd0.ne' hdE hrk hv x
  have hvR := vD_cnf M.E_E hXE hk0.ne' hd0.ne' hdE hrk hv (hv.trans M.eN_lt_B3) x
  rw [hdec] at hsR hvR
  rw [hsR, hvR, hV x hx hx1 hgx, IH k hko (hko.trans hcN) x hx hx1 hgx hgk, hR d hdE x hx hx1 hgd,
    IH r hro (hro.trans hcN) x hx hx1 hgx hgr]

end Step

end Googology.Trans.PoR.InaccPsi.R2.Qd
