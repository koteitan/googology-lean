import Googology.Trans.PoR.InaccPsi.R2.QcBd
import Googology.Trans.PoR.InaccPsi.R2.CitedTf

/-!
# QcBdV: THE BOUND OF THE LAYER TOPS, WITH THE VEBLEN LEVELS UNDER LEMMA IMG THERE

`Qc.QcBd x v` (`v` below a point `ϑˣ(Ω₁·N)` of a level `Ω₁ ≤ N < ε_{Ω₁+1}` with its data below `x`) is where Lemma
IMG is a theorem (`Qc.qc_img_bd`).  The ladder and union steps (`Yw.YwLH`, `Yw.YwUF`) ask their tops in a bound only
to have Lemma IMG there and to have them countable.  Here the bound also admits the points of the Veblen levels
`Ω₁ ≤ N < Γ_{Ω₁+1}` (`Qd.QdBd`), under the hypothesis `Qd.QdImgH` (Lemma IMG there, not proved):

* `Qd.QdBd`, `Qd.QdImgH`, `Qd.qd_arg_lt`, `Qd.qd_bd_pt`, `Qd.qdBd_lt`;
* `YBd x v := QcBd x v ∨ (QdImgH ∧ QdBd x v)`, `yBd_of_qc`, `yBd_img` (**Lemma IMG at every `v` with `YBd ρ v`**),
  `yBd_lt` (`v < Ω₁`).

No new axiom.  New definitions: `Qd.QdBd`, `Qd.QdImgH`, `YBd`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Gn

/-- **`v` is below a point `ϑˣ(Ω₁·N)` of a Veblen level `Ω₁ ≤ N < Γ_{Ω₁+1}` with its data below `x`.** -/
def QdBd (x v : Ordinal.{0}) : Prop :=
  ∃ N, Om1 ≤ N ∧ N < ggGam ∧ Tf.tfDat N < x ∧ v < vt x (Om1 * N)

/-- **Lemma IMG below every point of a Veblen level** (a hypothesis), in every restart context. -/
def QdImgH : Prop := ∀ ρ τ δ v : Ordinal.{0}, RstK ρ τ δ → QdBd ρ v → GnI ρ δ v

theorem qd_img_bd (hI : QdImgH) {ρ τ δ v : Ordinal.{0}} (h : RstK ρ τ δ) (hb : QdBd ρ v) : GnI ρ δ v :=
  hI ρ τ δ v h hb

theorem qd_gg_lt_Om2 : ggGam < (OmTwo : Ordinal.{0}) := by
  rw [Uc.uc_Om2_eq]; exact Tf.tf_gg_lt_BG.trans Tf.tfBG_lt_Om2

/-- The arguments `Ω₁·M + σ`, `M < Γ_{Ω₁+1}`, `σ < Ω₁`, are below `Ω₂`. -/
theorem qd_arg_lt {M σ : Ordinal.{0}} (hM : M < ggGam) (hσΩ : σ < Om1) : Om1 * M + σ < OmTwo := by
  have hE : InE (OmTwo : Ordinal.{0}) := Low.opow_eq_self_of_SC Uc.uc_SC_Om2
  have hO1 : (Om1 : Ordinal.{0}) < OmTwo := Uc.uc_Om1_lt_Om2
  exact (inE_indec hE).add_lt (hE.mul_lt hO1 (hM.trans qd_gg_lt_Om2)) (hσΩ.trans hO1)

section Bd

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- The point `ϑˣ(Ω₁·N)` is in `Tˣ ∩ Ω₁`, at least `x` and additively principal. -/
theorem qd_bd_pt {N : Ordinal.{0}} (hN1 : Om1 ≤ N) (hNG : N < ggGam) (hNx : Tf.tfDat N < x) :
    vt x (Om1 * N) ∈ Tset x ∧ vt x (Om1 * N) < Om1 ∧ x ≤ vt x (Om1 * N) ∧ Indec (vt x (Om1 * N)) := by
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  have hargT := tfArg_mem hx hx1 hN1 (hNG.trans Tf.tf_gg_lt_BG) (mem_T_of_le hx hx1 hNx.le) h0T h0Ω
  rw [add_zero] at hargT
  obtain ⟨hT, hx', h1, hI, -⟩ := vt_memTwo hx hx1 hargT (by simpa using qd_arg_lt hNG h0Ω)
  exact ⟨hT, h1, hx', hI⟩

theorem qdBd_lt {v : Ordinal.{0}} (h : QdBd x v) : v < Om1 := by
  obtain ⟨N, h1, h2, h3, h4⟩ := h
  exact h4.trans (qd_bd_pt hx hx1 h1 h2 h3).2.1

end Bd

end Googology.Trans.PoR.InaccPsi.R2.Qd

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gn

/-- **The bound of the layer tops**: below a point of a generic level (`QcBd`), or, under Lemma IMG at the Veblen
levels, below a point of a Veblen level (`Qd.QdBd`). -/
def YBd (x v : Ordinal.{0}) : Prop := QcBd x v ∨ (Qd.QdImgH ∧ Qd.QdBd x v)

theorem yBd_of_qc {x v : Ordinal.{0}} (h : QcBd x v) : YBd x v := Or.inl h

/-- **Lemma IMG at every `v` with `YBd ρ v`** (in a restart context). -/
theorem yBd_img {ρ τ δ v : Ordinal.{0}} (h : RstK ρ τ δ) (hb : YBd ρ v) : GnI ρ δ v := by
  rcases hb with hb | ⟨hI, hb⟩
  · exact qc_img_bd h hb
  · exact Qd.qd_img_bd hI h hb

theorem yBd_lt {x v : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hb : YBd x v) : v < Om1 := by
  rcases hb with hb | ⟨-, hb⟩
  · exact qcBd_lt hx hx1 hb
  · exact Qd.qdBd_lt hx hx1 hb

end Googology.Trans.PoR.InaccPsi.R2.Qc
