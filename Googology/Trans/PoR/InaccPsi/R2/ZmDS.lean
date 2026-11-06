import Googology.Trans.PoR.InaccPsi.R2.ZgSq
import Googology.Trans.PoR.InaccPsi.R2.TeExp
import Googology.Trans.PoR.InaccPsi.R2.GoD
import Googology.Trans.PoR.InaccPsi.R2.XkBase

/-!
# ZmDS: A DIGIT SYSTEM AT AN `ε`-NUMBER BASE `E ≥ B_Γ` — THE INTERFACE OF THE GENERIC HEREDITARY STEP

The offsets `o < E` of the atom indices `B_Γ + 1 + o` past `B_Γ`, with a reading `R(o)(x)` below the reading
`V(x)` of the base `E`, gates, the order, successor, limits and cofinality, Lemma EXACT for the readings, the digit
lemma (`π(ω^P·R(d)(ρ)) = ω^{P'}·R(d)(σ)` once the atoms `ω^{P+β}`, `β < V(ρ)`, are exact), the codes of `TlCl`
exactly the offsets with gate below `Z`, and `ε_{V(x)+1} = ϑˣ(Ω₁ + W(x))` with `W` exact.  The first instance is the
`Yr` codes below `B_Γ` with `V = D = ϑˣ(Ω₁·Ω₁ + Ω₁)` (`zmYr`).

* `zm_eN_nfix` (`ε_{y+1}` is never a fixed point of `φ(1, ·)`), `zm_eN_lt_fix`, `zmD_facts`, `zmD_eN`
  (**`ε_{D(x)+1} = ϑˣ(Ω₁ + D(x))`**), `zmD_pi`, `zmDN_pi`;
* `ZmDS`, `zmYr` (**the `Yr` codes below `B_Γ` as a digit system with `V = D`**).

No new axiom.  New definitions: `ZmDS`, `zmYr`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zm

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Ge
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Zg Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Xk

/-! ## `ε`-numbers and fixed points of `φ(1, ·)` -/

theorem zm_veb_E (b : Ordinal.{0}) : InE (veblen 1 b) := omega0_opow_epsilon b

/-- **`ε_{y+1}` is never a fixed point of `φ(1, ·)`.** -/
theorem zm_eN_nfix (y : Ordinal.{0}) : veblen 1 (eN y) ≠ eN y := by
  intro h
  have h1 : y < veblen 1 (y + 1) := (lt_add_one y).trans_le (right_le_veblen 1 (y + 1))
  have h2 : eN y ≤ veblen 1 (y + 1) := eN_le h1 (zm_veb_E _)
  have h3 : y + 1 < eN y := (ev_isSuccLimit_of_inE (eN_E y)).add_one_lt (lt_eN y)
  have h4 : veblen 1 (y + 1) < veblen 1 (eN y) := (isNormal_veblen 1).strictMono h3
  rw [h] at h4
  exact absurd h2 (not_le.2 h4)

/-- A fixed point of `φ(1, ·)` is an `ε`-number. -/
theorem zm_fix_E {u : Ordinal.{0}} (hu : veblen 1 u = u) : InE u := by
  have := zm_veb_E u; rwa [hu] at this

/-- **`ε_{y+1} < u`** for every fixed point `u > y` of `φ(1, ·)`. -/
theorem zm_eN_lt_fix {y u : Ordinal.{0}} (hyu : y < u) (hu : veblen 1 u = u) : eN y < u := by
  refine lt_of_le_of_ne (eN_le hyu (zm_fix_E hu)) fun h => ?_
  exact zm_eN_nfix y (by rw [h]; exact hu)

/-- `B_Γ = φ(1, B_Γ)`. -/
theorem zm_BG_fix : veblen 1 tfBG = tfBG := tfBG_SC.veblen_right (gg_one_lt_of_SC tfBG_SC)

/-! ## The reading `D(x) = ϑˣ(Ω₁·Ω₁ + Ω₁)` of `B_Γ` -/

section DFacts

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem zmD_facts : ywV 1 0 x ∈ Tset x ∧ x < ywV 1 0 x ∧ ywV 1 0 x < Om1 ∧ InE (ywV 1 0 x) := by
  obtain ⟨hxD, hDT, -⟩ := ywD_closed hx hx1
  obtain ⟨-, hD1, hDE⟩ := zgD_T hx hx1
  exact ⟨hDT, hxD, hD1, hDE⟩

/-- **The next non-fixed value of `Γ` after `D(x)`**: `gq (D(x)+1) x` is above `D(x)`, a fixed point of `φ(1, ·)`,
and below `X^x`. -/
theorem zm_gq_facts : ywV 1 0 x < gq (ywV 1 0 x + 1) x ∧ gq (ywV 1 0 x + 1) x ∈ Tset x ∧
    gq (ywV 1 0 x + 1) x < Om1 ∧ veblen 1 (gq (ywV 1 0 x + 1) x) = gq (ywV 1 0 x + 1) x ∧
    gq (ywV 1 0 x + 1) x < ywX x := by
  obtain ⟨hDT1, hD11, hX⟩ := zbDo_T hx hx1 (o := 1) (one_lt_omega0.trans_le (omega0_le_of_isSuccLimit gc_eps0_lim))
  obtain ⟨hGT, -, hG1, hGE, -⟩ := geq_facts hx hx1 hDT1 hD11
  have hDG : ywV 1 0 x < gq (ywV 1 0 x + 1) x := (lt_add_one _).trans (gmq_gt hx hx1 hDT1 hD11)
  have h1G : (1 : Ordinal.{0}) < gq (ywV 1 0 x + 1) x := one_lt_omega0.trans (omega0_lt_inE hGE)
  exact ⟨hDG, hGT, hG1, xk_fix hx hx1 hDT1 hD11 le_rfl h1G, hX⟩

/-- **`ε_{D(x)+1} = ϑˣ(Ω₁ + D(x))`.** -/
theorem zmD_eN : eN (ywV 1 0 x) = glA 1 (ywV 1 0 x) x := by
  obtain ⟨hGT, hxG, hG1, hGE⟩ := zmD_facts hx hx1
  obtain ⟨-, -, hYC⟩ := ywD_closed hx hx1
  obtain ⟨h1T, h11⟩ := gl_one_T hx hx1
  obtain ⟨-, -, -, haE, -, hta⟩ := glA_facts hx hx1 le_rfl h1T h11 hGT hG1
  refine le_antisymm (eN_le hta haE) ?_
  have hP1 : LuP 1 (eN (ywV 1 0 x)) := by
    have h := vzP_one.2 (eN_E (ywV 1 0 x)); unfold VzP at h; rwa [Nat.cast_one] at h
  have h1G : (1 : Ordinal.{0}) < ywV 1 0 x := one_lt_omega0.trans (omega0_lt_inE hGE)
  refine glA_min hx hx1 le_rfl h1T h11 hGT hG1 hP1 (hxG.trans (lt_eN _)) (lt_eN _)
    (h1G.trans (lt_eN _)) (fun σ hσ => ?_)
  have hσT : σ ∈ Tset x := vz_T_down hx hx1 hGT hG1 hσ.le
  have hσ1 : σ < Om1 := hσ.trans hG1
  have hσq : σ < gq σ x := gmq_gt hx hx1 hσT hσ1
  have h1q : (1 : Ordinal.{0}) < gq σ x :=
    one_lt_omega0.trans (omega0_lt_inE (geq_facts hx hx1 hσT hσ1).2.2.2.1)
  exact ((xkA_lt hx hx1 hσT hσ1 h1q hσq).trans (hYC σ hσT hσ)).trans (lt_eN _)

end DFacts

section DPi

variable {σ ρ : Ordinal.{0}} (hB : Bases σ ρ)
include hB

theorem zmD_pi : ywV 1 0 ρ ∈ TB ρ σ ∧ Googology.Trans.PoR.InaccPsi.R2.pi σ ρ (ywV 1 0 ρ) = ywV 1 0 σ := by
  have h1σ : (1 : Ordinal.{0}) < σ := lu_one_lt_E hB.1
  have h0σ : (0 : Ordinal.{0}) < σ := hB.1.pos
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hD := ywV_pi hB (mem_TB_of_lt hB h1σ) ((lu_one_lt_E hB.2.1).trans hρ1) (mem_TB_of_lt hB h0σ)
    (hB.2.1.pos.trans hρ1)
  rw [pi_lt hB h1σ, pi_lt hB h0σ] at hD
  exact hD

theorem zmDN_pi : eN (ywV 1 0 ρ) ∈ TB ρ σ ∧
    Googology.Trans.PoR.InaccPsi.R2.pi σ ρ (eN (ywV 1 0 ρ)) = eN (ywV 1 0 σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨o1, o2⟩ := one_TB hB
  obtain ⟨d1, d2⟩ := zmD_pi hB
  have h := glA_pi hB o1 (gl_one_T hB.2.1 hρ1).2 d1 (zmD_facts hB.2.1 hρ1).2.2.1
  rw [o2, d2, ← zmD_eN hB.2.1 hρ1, ← zmD_eN hB.1 hσ1] at h
  exact h

end DPi

/-! ## The index readings below `gq(D(x)+1)` are not closed -/

section NC

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **An index reading `D(x) + r` below `gq(D(x)+1)`, `r` a limit, is not closed** (`σ = D(x) + 1`). -/
theorem zm_nc_of {r : Ordinal.{0}} (hr : r < gq (ywV 1 0 x + 1) x) (hl : IsSuccLimit r) :
    ∃ σ, σ ∈ Tset x ∧ σ < Om1 ∧ σ < ywV 1 0 x + r ∧ ywV 1 0 x + r < gq σ x := by
  obtain ⟨hDT, -, hD1, -⟩ := zmD_facts hx hx1
  obtain ⟨h1T, h11⟩ := gl_T_succ hx hx1 hDT hD1
  obtain ⟨hDq, -, -, hqfix, -⟩ := zm_gq_facts hx hx1
  have h1r : (1 : Ordinal.{0}) < r := by simpa using hl.add_one_lt hl.bot_lt
  exact ⟨_, h1T, h11, (add_lt_add_iff_left _).2 h1r, (inE_indec (zm_fix_E hqfix)).add_lt hDq hr⟩

/-- **A base reading `D(x) ≤ V < gq(D(x)+1)` is not closed** (`σ = D(x) + 1`). -/
theorem zm_Vq_of {V : Ordinal.{0}} (hDV : ywV 1 0 x ≤ V) (hVq : V < gq (ywV 1 0 x + 1) x) (hVE : InE V) :
    ∃ σ, σ ∈ Tset x ∧ σ < Om1 ∧ σ < ywV 1 0 x + V ∧ V < gq σ x := by
  obtain ⟨hDT, -, hD1, -⟩ := zmD_facts hx hx1
  obtain ⟨h1T, h11⟩ := gl_T_succ hx hx1 hDT hD1
  exact ⟨_, h1T, h11, (add_lt_add_iff_left _).2 (lu_one_lt_E hVE), hVq⟩

theorem zm_gq_X : gq (ywV 1 0 x + 1) x < ywX x := (zm_gq_facts hx hx1).2.2.2.2

/-- **`gq σ x` below `X^x`** for `σ ∈ Tˣ ∩ X^x`. -/
theorem zm_gq_lt_X {σ : Ordinal.{0}} (hσT : σ ∈ Tset x) (hσ1 : σ < Om1) (hσX : σ < ywX x) : gq σ x < ywX x := by
  rw [← ywV_zero]
  exact ywV_lt_X hx hx1 (mem_T_of_le hx hx1 zero_le) (hx.pos.trans hx1) hσT hσ1 (hx.pos.trans (ywX_facts hx hx1).2.1)
    hσX

/-- **The facts of a non-closure witness `σ < D(x) + V`, `V < X^x`.** -/
theorem zm_q_facts {d V σ : Ordinal.{0}} (hDV : d ≤ V) (hVX : V < ywX x) (hσT : σ ∈ Tset x)
    (hσ1 : σ < Om1) (hσV : σ < d + V) :
    veblen 1 (gq σ x) = gq σ x ∧ gq σ x < ywX x ∧ InE (gq σ x) := by
  have hXE : InE (ywX x) := (ywX_facts hx hx1).2.2.2
  have hσX : σ < ywX x := hσV.trans ((inE_indec hXE).add_lt (hDV.trans_lt hVX) hVX)
  obtain ⟨-, -, -, hqE, -⟩ := geq_facts hx hx1 hσT hσ1
  exact ⟨xk_fix hx hx1 hσT hσ1 le_rfl (lu_one_lt_E hqE), zm_gq_lt_X hx hx1 hσT hσ1 hσX, hqE⟩

/-- **`D(x)` as a segment base reading.** -/
theorem zmD_T : ywV 1 0 x ∈ Tset x ∧ InE (ywV 1 0 x) ∧ x < ywV 1 0 x ∧ ywV 1 0 x < ywX x :=
  ⟨(zmD_facts hx hx1).1, (zmD_facts hx hx1).2.2.2, (zmD_facts hx hx1).2.1,
    (zm_gq_facts hx hx1).1.trans (zm_gq_X hx hx1)⟩

end NC

/-- A fixed point of `Γ` is a fixed point of `φ(1, ·)`. -/
theorem zm_fix_of_gamma {y : Ordinal.{0}} (h : gamma y = y) : veblen 1 y = y := by
  have h1G : (1 : Ordinal.{0}) < gamma y := one_lt_omega0.trans (omega0_lt_inE
    (Low.opow_eq_self_of_SC (Lq.lq_gamma_SC y)))
  have hfix : veblen 1 (gamma y) = gamma y := by
    conv_lhs => rw [← veblen_gamma_zero y]
    rw [veblen_veblen_of_lt h1G, veblen_gamma_zero]
  rwa [h] at hfix

/-! ## The interface -/

/-- **A digit system at an `ε`-number base `E = φ(1, E_i) ≥ B_Γ`**: offsets `o < E`, reading `R(o)(x) < V(x)`, gate
`G(o)`, `ε_{V(x)+1} = ϑˣ(Ω₁ + W(x))`. -/
structure ZmDS where
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
  B_cl : ∀ Z, SC Z → TlCl Z B
  E_X : E < tlX
  Ei_cl : ∀ Z, SC Z → Eg < Z → TlCl Z Ei
  nfx : ∀ y, B < y → y ≤ E → gamma y ≠ y
  Eg_le : ∀ c, c ≠ 0 → Eg ≤ G c
  Dv_T : ∀ x, InE x → x < Om1 → Dv x ∈ Tset x ∧ InE (Dv x) ∧ x < Dv x ∧ Dv x < ywX x
  Dv_pi : ∀ σ ρ, Bases σ ρ → Dv ρ ∈ TB ρ σ ∧ Googology.Trans.PoR.InaccPsi.R2.pi σ ρ (Dv ρ) = Dv σ
  V_T : ∀ x, InE x → x < Om1 → Eg < x →
    V x ∈ Tset x ∧ InE (V x) ∧ Dv x ≤ V x ∧ V x < ywX x
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
  cl : ∀ c Z, SC Z → c < E → G c < Z → TlCl Z c
  gate : ∀ c Z, SC Z → Z ≤ Om1 → Eg < Z → c < E → TlCl Z c → G c < Z

/-! ## The first instance: the `Yr` codes below `B_Γ` -/

/-- **THE `Yr` CODES BELOW `B_Γ` AS A DIGIT SYSTEM** (`V = W = D`). -/
noncomputable def zmYr : ZmDS where
  E := tfBG
  Ei := tfBG
  V := ywV 1 0
  W := ywV 1 0
  R := yrR
  G := yrG
  Eg := 0
  B := tfBG
  Dv := ywV 1 0
  E_eq := zm_BG_fix
  BG_le := le_rfl
  BG_B := le_rfl
  B_le := le_rfl
  B_cl := fun _ hZ => zbBG_tl hZ.1
  Dv_T := fun x hx hx1 => zmD_T hx hx1
  Dv_pi := fun _ _ hB => zmD_pi hB
  E_X := tl_BG_lt_X
  Ei_cl := fun _ hZ _ => zbBG_tl hZ.1
  nfx := fun y h1 h2 => absurd h2 (not_le.2 h1)
  Eg_le := fun _ _ => zero_le
  V_T := fun x hx hx1 _ => ⟨(zmD_facts hx hx1).1, (zmD_facts hx hx1).2.2.2, le_rfl,
    (zm_gq_facts hx hx1).1.trans (zm_gq_X hx hx1)⟩
  Vq := fun x hx hx1 _ => zm_Vq_of hx hx1 le_rfl (zm_gq_facts hx hx1).1 (zmD_facts hx hx1).2.2.2
  W_T := fun x hx hx1 _ => ⟨(zmD_facts hx hx1).1, (zmD_facts hx hx1).2.2.1, zmD_eN hx hx1⟩
  V_pi := fun _ _ hB _ => zmD_pi hB
  W_pi := fun _ _ hB _ => zmD_pi hB
  R0 := yrR_zero
  G0 := yrG_zero
  G1 := by
    have h1 : yrG ((1 : ℕ) : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) := by
      rw [yrG_low (Yh.yh_nat_lt_G 1), glG_nat]
    have h2 : yrG (1 : Ordinal.{0}) ≤ 1 := by simpa using h1.le
    exact h2.trans (le_max_right _ _)
  lt := fun c x hx hx1 hc hg => zgN_lt_D hx hx1 (yrR_N hx hx1 hc hg)
  pos := fun c x hx hx1 hc0 hc hg => yrR_pos hx hx1 hc0 hc hg
  mono := fun b c x hx hx1 hbc hc hgb hgc => yrR_mono hx hx1 hc hbc hgc hgb
  succ := yrR_succ
  g_le := yrG_le_succ
  g_succ := fun c _ hZ _ hg => yrG_succ hZ c hg
  lim := fun c x hx hx1 hl hc hg => yr_lim_of_cof hx hx1 hl hc hg (yrR_cof hx hx1 c hc)
  cof := fun c x hx hx1 _ hc hg ν hν => yrR_cof hx hx1 c hc hg ν hν
  nc := fun c x hx hx1 hl hc hg => zm_nc_of hx hx1
    ((zgN_lt_D hx hx1 (yrR_N hx hx1 hc hg)).trans (zm_gq_facts hx hx1).1)
    (yr_lim_of_cof hx hx1 hl hc hg (yrR_cof hx hx1 c hc))
  top := fun x hx hx1 _ ν hν => by
    obtain ⟨n, hn⟩ := zgCofD hx hx1 hν
    exact ⟨yrTw n, yrTw_lt_BG n, by rw [yrTw_g]; exact hx.pos, hn⟩
  ex := fun σ ρ c hB hc hg => yr_pi hB c hc hg
  dig := fun σ ρ d hB hd hgd P P' hP => by
    have h0σ : (0 : Ordinal.{0}) < σ := hB.1.pos
    have hρ1 : ρ < Om1 := hB.2.2.2
    obtain ⟨m, hm⟩ := yrTw_cof _ hd
    have hmB := yrTw_lt_BG m
    have hgm : yrG (yrTw m) < σ := by rw [yrTw_g]; exact h0σ
    have hDρ : yrR (yrTw m) ρ < ywV 1 0 ρ :=
      zgN_lt_D hB.2.1 hρ1 (yrR_N hB.2.1 hρ1 hmB (hgm.trans hB.2.2.1))
    exact yr_dig hB (yrTw_E m) (yrTw_ge m) hmB hgm (fun j hj hgj => yr_pi hB j (hj.trans hmB) hgj) d hm hgd P P'
      (fun β hβT hβ => hP β hβT (hβ.trans hDρ))
  cl := fun c Z hZ hc hg => (zgYr hZ.1 c hc hg).1
  gate := fun c Z hZ hZ1 _ hc h => zgGate hZ hZ1 hc h

/-- **Cofinally many codes of gate at most `max Eg 1`** (used for `ZbDirect`; the generic step always has it). -/
def ZmDS.Gc0 (M : ZmDS) : Prop := ∀ c, c < M.E → ∃ c', c ≤ c' ∧ c' < M.E ∧ M.G c' ≤ max M.Eg 1

theorem zmYr_gc0 : zmYr.Gc0 := fun c hc => by
  obtain ⟨n, hn⟩ := yrTw_cof c hc
  exact ⟨yrTw n, hn.le, yrTw_lt_BG n, (yrTw_g n).le.trans zero_le⟩

end Googology.Trans.PoR.InaccPsi.R2.Zm
