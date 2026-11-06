import Googology.Trans.PoR.InaccPsi.R2.QcBdC
import Googology.Trans.PoR.InaccPsi.R2.ZmDS
import Googology.Trans.PoR.InaccPsi.R2.QcAt

/-!
# QcDS: A DIGIT SYSTEM AT AN `ε`-NUMBER BASE BELOW `B₂`

`Zm.ZmDS` is a digit system at an `ε`-number base `E < X`: offsets `o < E` read `R(o)(x)`, codes of `Tl.TlCl`, readings
below `X^x`.  `QDS` is the same at a base `E < B₂ = Uc.ucB`, with the codes of `Uc.UcCl` and the readings below a point
of a generic level (`Qc.QcBd`, where Lemma IMG holds, `Qc.qc_img_bd`).  Every `ZmDS` is one (`ZmDS.toQ`: `TlCl ⊆ UcCl`,
`X < B₂`, `v < X^x ⇒ QcBd x v`).

* `QDS`, `Zm.ZmDS.toQ`; `QDS.E_E`, `QDS.V_lt`, `QDS.Eg_lt`, `QDS.R_bd` (**every reading is `QcBd`**), `QDS.rR_facts`.

No new axiom.  New definitions: `QDS`, `Zm.ZmDS.toQ`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Uc
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yw
  Googology.Trans.PoR.InaccPsi.R2.Zm Googology.Trans.PoR.InaccPsi.R2.Lu

/-- **A digit system at an `ε`-number base `E = φ(1, E_i) ∈ [B_Γ, B₂)`**: offsets `o < E`, reading `R(o)(x) < V(x)`,
gate `G(o)`, `ε_{V(x)+1} = ϑˣ(Ω₁ + W(x))`, codes of `UcCl`, readings below a point of a generic level. -/
structure QDS where
  E : Ordinal.{0}
  Ei : Ordinal.{0}
  V : Ordinal.{0} → Ordinal.{0}
  W : Ordinal.{0} → Ordinal.{0}
  R : Ordinal.{0} → Ordinal.{0} → Ordinal.{0}
  G : Ordinal.{0} → Ordinal.{0}
  Eg : Ordinal.{0}
  B : Ordinal.{0}
  Dv : Ordinal.{0} → Ordinal.{0}
  E_eq : veblen 1 Ei = E
  BG_le : tfBG ≤ E
  BG_B : tfBG ≤ B
  B_le : B ≤ E
  B_cl : ∀ Z, SC Z → Eg < Z → UcCl Z B
  E_X : E < ucB
  Ei_cl : ∀ Z, SC Z → Eg < Z → UcCl Z Ei
  nfx : ∀ y, B < y → y ≤ E → gamma y ≠ y
  Eg_le : ∀ c, c ≠ 0 → Eg ≤ G c
  Dv_T : ∀ x, InE x → x < Om1 → Eg < x → Dv x ∈ Tset x ∧ InE (Dv x) ∧ x < Dv x ∧ QcBd x (Dv x)
  Dv_pi : ∀ σ ρ, Bases σ ρ → Eg < σ → Dv ρ ∈ TB ρ σ ∧ Googology.Trans.PoR.InaccPsi.R2.pi σ ρ (Dv ρ) = Dv σ
  V_T : ∀ x, InE x → x < Om1 → Eg < x →
    V x ∈ Tset x ∧ InE (V x) ∧ Dv x ≤ V x ∧ QcBd x (V x)
  Vq : ∀ x, InE x → x < Om1 → Eg < x → ∃ σ, σ ∈ Tset x ∧ σ < Om1 ∧ σ < Dv x + V x ∧ V x < gq σ x
  W_T : ∀ x, InE x → x < Om1 → Eg < x → W x ∈ Tset x ∧ W x < Om1 ∧ eN (V x) = glA 1 (W x) x
  V_pi : ∀ σ ρ, Bases σ ρ → Eg < σ → V ρ ∈ TB ρ σ ∧ Googology.Trans.PoR.InaccPsi.R2.pi σ ρ (V ρ) = V σ
  W_pi : ∀ σ ρ, Bases σ ρ → Eg < σ → W ρ ∈ TB ρ σ ∧ Googology.Trans.PoR.InaccPsi.R2.pi σ ρ (W ρ) = W σ
  R0 : ∀ x, R 0 x = 0
  G0 : G 0 = 0
  G1 : G 1 ≤ max Eg 1
  lt : ∀ c x, InE x → x < Om1 → c < E → G c < x → R c x < V x
  pos : ∀ c x, InE x → x < Om1 → c ≠ 0 → c < E → G c < x → 0 < R c x
  mono : ∀ b c x, InE x → x < Om1 → b < c → c < E → G b < x → G c < x → R b x < R c x
  succ : ∀ c x, R (c + 1) x = R c x + 1
  g_le : ∀ c, G c ≤ G (c + 1)
  g_succ : ∀ c Z, IsSuccLimit Z → Eg < Z → G c < Z → G (c + 1) < Z
  lim : ∀ c x, InE x → x < Om1 → IsSuccLimit c → c < E → G c < x → IsSuccLimit (R c x)
  cof : ∀ c x, InE x → x < Om1 → IsSuccLimit c → c < E → G c < x → ∀ ν, ν < R c x →
    ∃ b, b < c ∧ G b < x ∧ ν ≤ R b x
  nc : ∀ c x, InE x → x < Om1 → IsSuccLimit c → c < E → G c < x →
    ∃ σ, σ ∈ Tset x ∧ σ < Om1 ∧ σ < Dv x + R c x ∧ Dv x + R c x < gq σ x
  top : ∀ x, InE x → x < Om1 → Eg < x → ∀ ν, ν < V x → ∃ b, b < E ∧ G b < x ∧ ν ≤ R b x
  ex : ∀ σ ρ c, Bases σ ρ → c < E → G c < σ →
    R c ρ ∈ TB ρ σ ∧ Googology.Trans.PoR.InaccPsi.R2.pi σ ρ (R c ρ) = R c σ
  dig : ∀ σ ρ d, Bases σ ρ → d < E → G d < σ → ∀ P P' : Ordinal.{0},
    (∀ β, β ∈ TB ρ σ → β < V ρ →
      ω ^ (P + β) ∈ TB ρ σ ∧ Googology.Trans.PoR.InaccPsi.R2.pi σ ρ (ω ^ (P + β)) =
        ω ^ (P' + Googology.Trans.PoR.InaccPsi.R2.pi σ ρ β)) →
    ω ^ P * R d ρ ∈ TB ρ σ ∧ Googology.Trans.PoR.InaccPsi.R2.pi σ ρ (ω ^ P * R d ρ) = ω ^ P' * R d σ
  cl : ∀ c Z, SC Z → c < E → G c < Z → UcCl Z c
  gate : ∀ c Z, SC Z → Z ≤ Om1 → Eg < Z → c < E → UcCl Z c → G c < Z

/-- **Every digit system below `X` is one below `B₂`.** -/
noncomputable def _root_.Googology.Trans.PoR.InaccPsi.R2.Zm.ZmDS.toQ (M : ZmDS) : QDS where
  E := M.E
  Ei := M.Ei
  V := M.V
  W := M.W
  R := M.R
  G := M.G
  Eg := M.Eg
  B := M.B
  Dv := M.Dv
  E_eq := M.E_eq
  BG_le := M.BG_le
  BG_B := M.BG_B
  B_le := M.B_le
  B_cl := fun Z hZ h => UcCl.tl (M.B_cl Z hZ h)
  E_X := M.E_X.trans uc_X_lt_B
  Ei_cl := fun Z hZ h => UcCl.tl (M.Ei_cl Z hZ h)
  nfx := M.nfx
  Eg_le := M.Eg_le
  Dv_T := fun x hx hx1 hg => by
    obtain ⟨h1, h2, h3, h4⟩ := M.Dv_T x hx hx1 hg
    exact ⟨h1, h2, h3, qcBd_of_X hx h4⟩
  Dv_pi := M.Dv_pi
  V_T := fun x hx hx1 hg => by
    obtain ⟨h1, h2, h3, h4⟩ := M.V_T x hx hx1 hg
    exact ⟨h1, h2, h3, qcBd_of_X hx h4⟩
  Vq := M.Vq
  W_T := M.W_T
  V_pi := M.V_pi
  W_pi := M.W_pi
  R0 := M.R0
  G0 := M.G0
  G1 := M.G1
  lt := M.lt
  pos := M.pos
  mono := M.mono
  succ := M.succ
  g_le := M.g_le
  g_succ := M.g_succ
  lim := M.lim
  cof := M.cof
  nc := M.nc
  top := M.top
  ex := M.ex
  dig := M.dig
  cl := fun c Z hZ hc hg => UcCl.tl (M.cl c Z hZ hc hg)
  gate := fun c Z hZ hZ1 hEg hc h => M.gate c Z hZ hZ1 hEg hc (uc_cl_lt_X h (hc.trans M.E_X))

namespace QDS

variable (M : QDS)

theorem E_E : InE M.E := by rw [← M.E_eq]; exact zm_veb_E _

theorem E_lim : IsSuccLimit M.E := ev_isSuccLimit_of_inE M.E_E

theorem one_lt_E : (1 : Ordinal.{0}) < M.E := lu_one_lt_E M.E_E

theorem V_lt (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) (hEg : M.Eg < x) : M.V x < Om1 :=
  qcBd_lt hx hx1 (M.V_T x hx hx1 hEg).2.2.2

theorem Eg_lt {c x : Ordinal.{0}} (hc0 : c ≠ 0) (hg : M.G c < x) : M.Eg < x := (M.Eg_le c hc0).trans_lt hg

/-- **Every reading below the base is below a point of a generic level.** -/
theorem R_bd {c x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hc : c < M.E) (hg : M.G c < x) :
    QcBd x (M.R c x) := by
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [M.R0]
    exact qcBd_mono zero_le (qcBd_of_X hx (hx.pos.trans (ywX_facts hx hx1).2.1))
  · exact qcBd_mono (M.lt c x hx hx1 hc hg).le (M.V_T x hx hx1 (M.Eg_lt hc0 hg)).2.2.2

/-- **The reading of an index `B + 1 + o`** is in `Tˣ ∩ Ω₁`, and so is its `gq`, both below a generic-level point. -/
theorem rR_facts {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hEg : M.Eg < x) {o : Ordinal.{0}} (ho : o < M.E)
    (hg : M.G o < x) :
    M.Dv x + M.R o x ∈ Tset x ∧ M.Dv x + M.R o x < Om1 ∧
      QcBd x (M.Dv x + M.R o x) ∧ QcBd x (gq (M.Dv x + M.R o x) x) := by
  have hS : QcBd x (M.Dv x + M.R o x) := qcBd_add hx hx1 (M.Dv_T x hx hx1 hEg).2.2.2 (M.R_bd hx hx1 ho hg)
  have hST := qcBd_T hx hx1 hS
  exact ⟨hST, qcBd_lt hx hx1 hS, hS, qcBd_gq hx hx1 hST hS⟩

end QDS

end Googology.Trans.PoR.InaccPsi.R2.Qc
