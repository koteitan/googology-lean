import Googology.Trans.PoR.InaccPsi.R2.ZmNx

/-!
# ZmRa: RAISING THE GATES OF A DIGIT SYSTEM

A digit system stays one when the gates of all nonzero codes are raised to `max g (G c)` and the base gate to
`max Eg g` (every field asks a gate below `x`, `σ` or `Z` only as a hypothesis, or bounds a gate by a base-dependent
quantity).  This lets a base whose reading needs a gate `g` (a code index with gate `g`) sit on the systems below.

* `ZmDS.raise` (**the raised system**), `raise_G`, `raise_Eg`, `raise_R`, `raise_E`.

No new axiom.  New definition: `ZmDS.raise`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zm

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Zb Googology.Trans.PoR.InaccPsi.R2.Zg Googology.Trans.PoR.InaccPsi.R2.Gl

namespace ZmDS

variable (M : ZmDS) (g : Ordinal.{0})

/-- The raised gate. -/
noncomputable def rgt (c : Ordinal.{0}) : Ordinal.{0} := if c = 0 then 0 else max g (M.G c)

theorem rgt_ne {c : Ordinal.{0}} (h : c ≠ 0) : M.rgt g c = max g (M.G c) := by unfold rgt; rw [if_neg h]

theorem rgt_zero : M.rgt g 0 = 0 := by unfold rgt; rw [if_pos rfl]

theorem G_le_rgt (c : Ordinal.{0}) : M.G c ≤ M.rgt g c := by
  rcases eq_or_ne c 0 with rfl | h
  · rw [rgt_zero, M.G0]
  · rw [M.rgt_ne g h]; exact le_max_right _ _

/-- From a raised gate below `x` (nonzero code): `g < x`. -/
theorem g_lt_of {c x : Ordinal.{0}} (h0 : c ≠ 0) (h : M.rgt g c < x) : g < x := by
  rw [M.rgt_ne g h0] at h; exact (le_max_left _ _).trans_lt h

theorem rgt_lt {c x : Ordinal.{0}} (hg : g < x) (h : M.G c < x) : M.rgt g c < x := by
  rcases eq_or_ne c 0 with rfl | h0
  · rw [rgt_zero]; exact (zero_le).trans_lt hg
  · rw [M.rgt_ne g h0]; exact max_lt hg h

/-- **THE RAISED SYSTEM**: gates `max g (G c)` (`c ≠ 0`), base gate `max Eg g`. -/
noncomputable def raise : ZmDS where
  E := M.E
  Ei := M.Ei
  V := M.V
  W := M.W
  R := M.R
  G := M.rgt g
  Eg := max M.Eg g
  B := M.B
  Dv := M.Dv
  E_eq := M.E_eq
  BG_le := M.BG_le
  BG_B := M.BG_B
  B_le := M.B_le
  B_cl := M.B_cl
  Dv_T := M.Dv_T
  Dv_pi := M.Dv_pi
  E_X := M.E_X
  Ei_cl := fun Z hZ h => M.Ei_cl Z hZ ((le_max_left _ _).trans_lt h)
  nfx := M.nfx
  Eg_le := fun c hc => by rw [M.rgt_ne g hc]; exact max_le_max (M.Eg_le c hc) le_rfl |>.trans_eq (max_comm _ _)
  V_T := fun x hx hx1 h => M.V_T x hx hx1 ((le_max_left _ _).trans_lt h)
  Vq := fun x hx hx1 h => M.Vq x hx hx1 ((le_max_left _ _).trans_lt h)
  W_T := fun x hx hx1 h => M.W_T x hx hx1 ((le_max_left _ _).trans_lt h)
  V_pi := fun σ ρ hB h => M.V_pi σ ρ hB ((le_max_left _ _).trans_lt h)
  W_pi := fun σ ρ hB h => M.W_pi σ ρ hB ((le_max_left _ _).trans_lt h)
  R0 := M.R0
  G0 := M.rgt_zero g
  G1 := by
    rw [M.rgt_ne g one_ne_zero]
    exact max_le ((le_max_right _ _).trans (le_max_left _ _)) (M.G1.trans (max_le_max (le_max_left _ _) le_rfl))
  lt := fun c x hx hx1 hc hg => M.lt c x hx hx1 hc ((M.G_le_rgt g c).trans_lt hg)
  pos := fun c x hx hx1 hc0 hc hg => M.pos c x hx hx1 hc0 hc ((M.G_le_rgt g c).trans_lt hg)
  mono := fun b c x hx hx1 hbc hc hgb hgc =>
    M.mono b c x hx hx1 hbc hc ((M.G_le_rgt g b).trans_lt hgb) ((M.G_le_rgt g c).trans_lt hgc)
  succ := M.succ
  g_le := fun c => by
    rcases eq_or_ne c 0 with rfl | h0
    · rw [rgt_zero]; exact zero_le
    · rw [M.rgt_ne g h0, M.rgt_ne g (by simp)]; exact max_le_max le_rfl (M.g_le c)
  g_succ := fun c Z hZ hEg hg => by
    have hgZ : g < Z := (le_max_right _ _).trans_lt hEg
    exact M.rgt_lt g hgZ (M.g_succ c Z hZ ((le_max_left _ _).trans_lt hEg) ((M.G_le_rgt g c).trans_lt hg))
  lim := fun c x hx hx1 hl hc hg => M.lim c x hx hx1 hl hc ((M.G_le_rgt g c).trans_lt hg)
  nc := fun c x hx hx1 hl hc hg => M.nc c x hx hx1 hl hc ((M.G_le_rgt g c).trans_lt hg)
  cof := fun c x hx hx1 hl hc hg ν hν => by
    obtain ⟨b, hb, hgb, hνb⟩ := M.cof c x hx hx1 hl hc ((M.G_le_rgt g c).trans_lt hg) ν hν
    exact ⟨b, hb, M.rgt_lt g (M.g_lt_of g hl.bot_lt.ne' hg) hgb, hνb⟩
  top := fun x hx hx1 hEg ν hν => by
    obtain ⟨b, hb, hgb, hνb⟩ := M.top x hx hx1 ((le_max_left _ _).trans_lt hEg) ν hν
    exact ⟨b, hb, M.rgt_lt g ((le_max_right _ _).trans_lt hEg) hgb, hνb⟩
  ex := fun σ ρ c hB hc hg => M.ex σ ρ c hB hc ((M.G_le_rgt g c).trans_lt hg)
  dig := fun σ ρ d hB hd hg P P' hP => M.dig σ ρ d hB hd ((M.G_le_rgt g d).trans_lt hg) P P' hP
  cl := fun c Z hZ hc hg => M.cl c Z hZ hc ((M.G_le_rgt g c).trans_lt hg)
  gate := fun c Z hZ hZ1 hEg hc h =>
    M.rgt_lt g ((le_max_right _ _).trans_lt hEg) (M.gate c Z hZ hZ1 ((le_max_left _ _).trans_lt hEg) hc h)

theorem raise_E : (M.raise g).E = M.E := rfl
theorem raise_R : (M.raise g).R = M.R := rfl
theorem raise_V : (M.raise g).V = M.V := rfl
theorem raise_Eg : (M.raise g).Eg = max M.Eg g := rfl
theorem raise_G {c : Ordinal.{0}} (h : c ≠ 0) : (M.raise g).G c = max g (M.G c) := M.rgt_ne g h

end ZmDS

end Googology.Trans.PoR.InaccPsi.R2.Zm
