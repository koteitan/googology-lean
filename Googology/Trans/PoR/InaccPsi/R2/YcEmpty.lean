import Googology.Trans.PoR.InaccPsi.R2.YcNoGo
import Googology.Trans.PoR.InaccPsi.R2.XfG1

/-!
# YcEmpty: THE INTERFACE `Xk.XkVD k` IS EMPTY FOR EVERY `1 ≤ k ≤ G` — `skLaySys` IS FALSE AS STATED

The hull `Cl(1, b)` contains `ψ_π(e)` only for `e < 1`; by the defining property of `ψ_{Ω₂}(1) = Γ(1)`
(`InaccSeq.lt_psi_of_mem`, `Gm.gmS_psi`) every element of `Cl(1, b) ∩ Ω₂`, `b ≤ Γ(1)`, lies below `Γ(1)`
(`ycCl1_lt`).  `Xk.XkVD k` asks its index `ix` (`B = φ(1, ix)`, `Γ(k) ≤ B < Γ(k+1)`) to lie in EVERY hull
`Cl(a, b)` with `0 < a` above the gate (field `ix_mem`, copied from `Hg.HgVD`, where `0 < a` suffices because the
only atom is `G = ψ_{Ω₂}(0)`).  At `a = 1` this forces `ix < Γ(1)`, hence `B < Γ(1)`, against `Γ(k) ≤ B`:

* `ycCl1_lt` (**`Cl(1, b) ∩ Ω₂ ⊆ Γ(1)` for `b ≤ Γ(1)`**), `ycG_notMem` (**`Γ(k) ∉ Cl(1, b)`**, `1 ≤ k ≤ G`,
  `b ≤ Γ(1)`), `ycG_lt_Om2`;
* `ycVD_empty` (**NO `Xk.XkVD k` EXISTS FOR `1 ≤ k`, `k + 1 ≤ G`**), `ycC_empty` (no `Xk.XkC k` has a bound above
  `Γ(1)`: field `L_mem` at the code `Γ(1)`);
* `ycLaySys_false` (**`¬ Xk.XkLaySys S k` for `1 ≤ k`, `k + 1 ≤ G`: the skeleton leaf `skLaySys` IS REFUTED**),
  `ycLayFront_vac` (**`Xk.XkLayFront S k` holds VACUOUSLY**, so `Xx.xxLayFront` (`skLayFront`), `Xx.xxLaySys_base`
  (`skLaySysBase`), `Xx.xxLayLo_of_sys`, `Xx.xxVD_loc` say nothing for `k ≥ 1`);
* non-emptiness at `k = 0` is `Xk.xkVD_zero_ne`; the repaired interface (`k < a` in place of `0 < a`) is
  `Yc.YcVD` (`R2.YcVD`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gm

variable (S : InaccSeq.{0})

/-- **`Cl(1, b) ∩ Ω₂ ⊆ Γ(1)`** for every `b ≤ Γ(1)` (the defining property of `ψ_{Ω₂}(1) = Γ(1)`). -/
theorem ycCl1_lt {b x : Ordinal.{0}} (hb : b ≤ gcG 1) (hx : x ∈ S.CSet 1 b) (hx2 : x < Om (1 + 1)) :
    x < gcG 1 := by
  have hpsi : S.psi 1 (Om (1 + 1)) = gcG 1 := gmS_psi S 1 Xf.xf_one_lt_G.le
  rw [← hpsi] at hb ⊢
  exact lt_psi_of_mem (InR_Om_succ 1) (CSet_mono le_rfl hb hx) hx2

/-- **`Γ(c) < Ω₂`** for `c ≤ G`. -/
theorem ycG_lt_Om2 (S : InaccSeq.{0}) {c : Ordinal.{0}} (hc : c ≤ gcG 0) : gcG c < Om (1 + 1) := by
  rw [← gmS_psi S c hc]; exact psi_lt (InR_Om_succ 1) _

/-- **`Γ(k) ∉ Cl(1, b)`** for `1 ≤ k ≤ G` and `b ≤ Γ(1)`. -/
theorem ycG_notMem {k b : Ordinal.{0}} (hk : 1 ≤ k) (hkG : k ≤ gcG 0) (hb : b ≤ gcG 1) :
    gcG k ∉ S.CSet 1 b := fun h =>
  absurd (ycCl1_lt S hb h (ycG_lt_Om2 S hkG)) (not_lt.2 (gcG_le hk))

theorem yc_Om1_lt_G1 : Om1 < gcG 1 := Gl.gl_Om1_lt_G0.trans (gcG_lt zero_lt_one)

/-- **NO `Xk.XkVD k` EXISTS** for `1 ≤ k`, `k + 1 ≤ G` (field `ix_mem` at `a = 1`). -/
theorem ycVD_empty (S : InaccSeq.{0}) {k : Ordinal.{0}} (hk : 1 ≤ k) (hkG : k + 1 ≤ gcG 0) (D : Xk.XkVD k) : False := by
  have hix := D.ix_mem S 1 (D.γ + 1) zero_lt_one (lt_add_one _)
  have hb : D.γ + 1 ≤ gcG 1 := (Order.add_one_le_of_lt (D.γ_lt.trans yc_Om1_lt_G1))
  have hB2 : D.B < Om (1 + 1) := D.B_lt1.trans (ycG_lt_Om2 S hkG)
  have hixB : D.ix ≤ D.B := by rw [D.B_ix]; exact right_le_veblen _ _
  have hlt : D.ix < gcG 1 := ycCl1_lt S hb hix (hixB.trans_lt hB2)
  have hfix : veblen 1 (gcG 1) = gcG 1 := Gn.gn_veb_fix (gcG_SC 1) (by
    have := Xf.xf_one_lt_G.trans (gcG_lt (zero_lt_one (α := Ordinal.{0}))); exact this)
  have hBlt : D.B < gcG 1 := by
    rw [D.B_ix, ← hfix]; exact (isNormal_veblen 1).strictMono hlt
  exact absurd (hBlt.trans_le' ((gcG_le hk).trans D.G_le)) (lt_irrefl _)

/-- **No `Xk.XkC k` has a bound above `Γ(1)`** (field `L_mem` at the code `Γ(1)`). -/
theorem ycC_empty (S : InaccSeq.{0}) {k : Ordinal.{0}} (C : Xk.XkC k) (h : gcG 1 < C.Bd) : False := by
  have hm := C.L_mem (gcG 1) h S 1 (C.g (gcG 1) + 1) zero_lt_one (lt_add_one _)
  have hb : C.g (gcG 1) + 1 ≤ gcG 1 := Order.add_one_le_of_lt ((C.g_lt _ h).trans yc_Om1_lt_G1)
  exact ycG_notMem S le_rfl Xf.xf_one_lt_G.le hb hm

/-- **THE SKELETON LEAF `skLaySys` IS REFUTED**: `Xk.XkLaySys S k` is false for every `1 ≤ k`, `k + 1 ≤ G` (the
level `ℓ = 0 < Γ(k)` would need a system). -/
theorem ycLaySys_false {k : Ordinal.{0}} (hk : 1 ≤ k) (hkG : k + 1 ≤ gcG 0) : ¬ Xk.XkLaySys S k := fun h => by
  obtain ⟨D, -, -⟩ := h 0 (gcG_SC k).1
  exact ycVD_empty S hk hkG D

/-- **`skLaySys` refuted at every `k` of the skeleton statement** (`1 ≤ k`, `k + 1 < ε₀`). -/
theorem ycLaySys_false_eps {k : Ordinal.{0}} (hk : 1 ≤ k) (hke : k + 1 < ε₀) : ¬ Xk.XkLaySys S k :=
  ycLaySys_false S hk (hke.le.trans (gc_eps0_le_Om1.trans (gcG_Om1_lt 0).le))

/-- **`Xk.XkLayFront S k` holds VACUOUSLY** for `1 ≤ k`, `k + 1 ≤ G` (no system to apply it to). -/
theorem ycLayFront_vac {k : Ordinal.{0}} (hk : 1 ≤ k) (hkG : k + 1 ≤ gcG 0) : Xk.XkLayFront S k :=
  fun D _ _ _ _ => (ycVD_empty S hk hkG D).elim

end Googology.Trans.PoR.InaccPsi.R2.Yc
