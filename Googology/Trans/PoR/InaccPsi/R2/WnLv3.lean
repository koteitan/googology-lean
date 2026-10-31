import Googology.Trans.PoR.InaccPsi.R2.WnLv
import Googology.Trans.PoR.InaccPsi.R2.HnWP

/-!
# WnLv3: THE LEVEL DATUM OF REGION (A3) (levels `G < L < Γ(1)`, readings above `Γ_{x+1}`), ITS PSEUDO-BASES AND
# PACKAGES

`G = Γ_{Ω₁+1}`, `Γ(1) = Γ_{Ω₁+2}`.  A band level datum `Hn.HnLv` has `L < G` and `ℓ(x) < Γ_{x+1}` (fields `L_G`,
`l_lt`), so it cannot carry a level of region (A3) (`wnHnLv_lt_T0`, `wnHnLv_noRead`).  Moreover at a level `L > G`
the point `G` is not in the range of `φ(L, ·)` (`wnG_notRange`), so the start "over `G`" of regions (A1)/(A2)
(`Hn.HnWShape` over a base with `F = G`) does not exist at (A3) levels: the system with the bound `φ(L, G+1)` is the
step of the level-`L` package at the PSEUDO-BASE `φ(L, G)` (`wnA3_bound`: `φ(L, G+1) = hdNx L (φ(L, G))`).

* `WnLv3` (**THE (A3) LEVEL DATUM**: `G < L < Γ(1)`, reading `Γ_{x+1} < ℓ(x) < Γ_{x+2}` above the gate, the
  same code gate, hull membership and Lemma EXACT fields as `Hn.HnLv`);
* `wnLv3T0` (**NON-VACUITY**: the datum of the first (A3) level `t₀ = ε_{G+1}`, read `ε_{Γ_{x+1}+1}`, gate `0`);
* `WnQ3` (pseudo-bases of level `L + ν` over an (A3) datum; the fields of `Hn.HnVQ`), `WnQ3.toP` (**an (A3)
  pseudo-base is a level-`ω` pseudo-base `Hg.HgdP`**), `WnSpec3` (the specification of a step, as `Hn.HnVSpec`),
  `WnPk3` (**THE (A3) PACKAGE**: a datum and a step at every pseudo-base of its level, with the specification);
* `WnEnt3 S n` (**the (A3) invariant at the ladder level `t_n`**: a package at `t_n` with gate `< K`, and a
  pseudo-base at `φ(t_n, G)` with gate `< K` started by some system), `wnEnt3_sys` (it gives the system at
  `φ(t_n, G+1)` with gate `< K`), `wnQ3_bounds` (the fields `G < F`, `hdNx L F < Γ(1)` hold at `F = φ(t_n, G)`).

No new axiom.  New definitions: `WnLv3`, `wnRd3`, `wnLv3T0`, `WnQ3`, `WnQ3.toP`, `WnSpec3`, `WnPk3`, `WnEnt3`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wn

open Googology.Trans.PoR.InaccPsi.R2.Ho
open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gf
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd
open Googology.Trans.PoR.InaccPsi.R2.Wh Googology.Trans.PoR.InaccPsi.R2.Gk

/-! ## REFUTE FIRST: the band level datum cannot carry an (A3) level, and `G` is no base there -/

/-- **Every band level datum lies below the first (A3) level `t₀ = ε_{G+1}`.** -/
theorem wnHnLv_lt_T0 (Λ : HnLv) : Λ.L < Wj.wjT 0 := Λ.L_G.trans (Wj.wjT_spec 0).1

/-- **No band level datum reads `ε_{Γ_{x+1}+1}`** (the reading of `t₀`) at any `ε`-number `x < Ω₁`. -/
theorem wnHnLv_noRead (Λ : HnLv) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : Λ.l x ≠ eN (lgG x) :=
  fun h => absurd ((Λ.l_lt x hx hx1).trans (lt_eN (lgG x))) (by rw [h]; exact lt_irrefl _)

/-- **At a level `L > G` the point `G` is not in the range of `φ(L, ·)`.** -/
theorem wnG_notRange {L : Ordinal.{0}} (hL : gcG 0 < L) : ¬ LuP L (gcG 0) := by
  rintro ⟨i, hi⟩
  have : L ≤ veblen L i := by simpa using left_le_veblen L i
  rw [hi] at this
  exact absurd hL (not_lt.2 this)

/-- **The (A3) bound is the next point of `range φ(L, ·)` above the pseudo-base `φ(L, G)`.** -/
theorem wnA3_bound (L : Ordinal.{0}) : veblen L (gcG 0 + 1) = hdNx L (veblen L (gcG 0)) := (hdNx_veb L _).symm

/-! ## The (A3) level datum -/

/-- **THE (A3) LEVEL DATUM**: `L = Ω₁·u + Ω₁·q` (`q < Ω₁`), `G < L < Γ(1)`, read as `ℓ(x)` with `x ≤ ℓ(x)`,
`Γ_{x+1} < ℓ(x) < Γ_{x+2}` above the gate; the level gate `g < Ω₁` is below every strongly critical `Z ≤ Ω₁` over
which some code in `[L, Ω₁·u + Ω₁²)` exists; `L` lies in every hull `C(a, b)` with `0 < a`, `g < b`; Lemma EXACT for
`ℓ` holds at the base pairs `(σ, ρ)` with `g < σ`. -/
structure WnLv3 where
  L : Ordinal.{0}
  l : Ordinal.{0} → Ordinal.{0}
  u : Ordinal.{0}
  q : Ordinal.{0}
  g : Ordinal.{0}
  g_lt : g < Om1
  q_lt : q < Om1
  G_lt : gcG 0 < L
  L_G1 : L < gcG 1
  L_eq : L = Om 1 * u + Om 1 * q
  g_cl : ∀ Z y : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z {gcG 0} y → L ≤ y → y < Om 1 * u + Om 1 * Om 1 → g < Z
  L_mem : ∀ (S : InaccSeq.{0}) (a b : Ordinal.{0}), 0 < a → g < b → L ∈ S.CSet a b
  l_ge : ∀ x, x ≤ l x
  l_gtG : ∀ x, InE x → x < Om1 → g < x → lgG x < l x
  l_lt : ∀ x, InE x → x < Om1 → l x < gq 1 x
  l_pi : ∀ σ ρ, Bases σ ρ → g < σ → l ρ ∈ TB ρ σ ∧ pi σ ρ (l ρ) = l σ

namespace WnLv3

variable (Λ : WnLv3)

theorem ωL (ν : Ordinal.{0}) : ω < Λ.L + ν :=
  ((omega0_lt_inE gl_G0_E).trans Λ.G_lt).trans_le le_self_add

theorem ωl {x : Ordinal.{0}} (hx : InE x) (ν : Ordinal.{0}) : ω < Λ.l x + ν :=
  ((omega0_lt_inE hx).trans_le (Λ.l_ge x)).trans_le le_self_add

theorem fixk {ν v : Ordinal.{0}} (hv : LuP (Λ.L + ν) v) (k : ℕ) : veblen (k : Ordinal.{0}) v = v := by
  obtain ⟨a, rfl⟩ := hv
  exact veblen_veblen_of_lt ((natCast_lt_omega0 k).trans (Λ.ωL ν)) a

theorem fixω {ν v : Ordinal.{0}} (hv : LuP (Λ.L + ν) v) : veblen ω v = v := by
  obtain ⟨a, rfl⟩ := hv
  exact veblen_veblen_of_lt (Λ.ωL ν) a

theorem rfixk {x ν v : Ordinal.{0}} (hx : InE x) (hv : LuP (Λ.l x + ν) v) (k : ℕ) :
    veblen (k : Ordinal.{0}) v = v := by
  obtain ⟨a, rfl⟩ := hv
  exact veblen_veblen_of_lt ((natCast_lt_omega0 k).trans (Λ.ωl hx ν)) a

theorem rfixω {x ν v : Ordinal.{0}} (hx : InE x) (hv : LuP (Λ.l x + ν) v) : veblen ω v = v := by
  obtain ⟨a, rfl⟩ := hv
  exact veblen_veblen_of_lt (Λ.ωl hx ν) a

end WnLv3

/-! ## Non-vacuity: the datum of `t₀ = ε_{G+1}` -/

/-- The reading of `t₀`: `ε_{Γ_{x+1}+1}` (at least `x`). -/
noncomputable def wnRd3 (x : Ordinal.{0}) : Ordinal.{0} := max x (eN (lgG x))

theorem wnRd3_eq {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : wnRd3 x = eN (lgG x) :=
  max_eq_right ((lgG_facts hx hx1).2.1.trans (lt_eN _)).le

theorem wnT0_E : InE (Wj.wjT 0) := (Wj.wjT_spec 0).2.2.1

theorem wnT0_Om1_lt : Om1 < Wj.wjT 0 := gl_Om1_lt_G0.trans (Wj.wjT_spec 0).1

/-- **NON-VACUITY: THE (A3) LEVEL DATUM OF `t₀ = φ(1, G+1) = ε_{G+1}`** (reading `ε_{Γ_{x+1}+1}`, gate `0`). -/
noncomputable def wnLv3T0 : WnLv3 where
  L := Wj.wjT 0
  l := wnRd3
  u := Wj.wjT 0
  q := 0
  g := 0
  g_lt := gv_Om1_pos
  q_lt := gv_Om1_pos
  G_lt := (Wj.wjT_spec 0).1
  L_G1 := (Wj.wjT_spec 0).2.1
  L_eq := by
    rw [mul_zero, add_zero, ← Br.Om1_eq]
    have h := wn_Om1_mul_pow wnT0_E wnT0_Om1_lt one_ne_zero
    rw [opow_one] at h
    exact h.symm
  g_cl := fun _ _ hZ _ _ _ _ => hZ.1
  L_mem := fun S a b ha _ => CSet.phi_mem (CSet.one_mem _ _) (CSet.succ_mem (gmS_G0_mem S ha))
  l_ge := fun _ => le_max_left _ _
  l_gtG := fun x hx hx1 _ => by rw [wnRd3_eq hx hx1]; exact lt_eN _
  l_lt := fun x hx hx1 => by rw [wnRd3_eq hx hx1]; exact eNG_lt1 hx hx1 0
  l_pi := fun σ ρ hB _ => by
    rw [wnRd3_eq hB.2.1 hB.2.2.2, wnRd3_eq hB.1 (hB.2.2.1.trans hB.2.2.2)]
    exact eNG_pi hB 0

theorem wnLv3T0_L : wnLv3T0.L = Wj.wjT 0 := rfl

theorem wnLv3T0_g : wnLv3T0.g = 0 := rfl

theorem wnLv3T0_l {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : wnLv3T0.l x = eN (lgG x) := wnRd3_eq hx hx1

/-! ## Pseudo-bases of an (A3) level -/

/-- **A pseudo-base of level `L + ν`** over an (A3) datum (the fields of `Hn.HnVQ`). -/
structure WnQ3 (Λ : WnLv3) (ν : Ordinal.{0}) where
  F : Ordinal.{0}
  Fr : Ordinal.{0} → Ordinal.{0}
  γ : Ordinal.{0}
  Zo : Ordinal.{0} → Ordinal.{0}
  lv : ν < Om1
  γ_ge : ν ≤ γ
  lg : Λ.g ≤ γ
  γ_lt : γ < Om1
  F_P : LuP (Λ.L + ν) F
  G_lt : gcG 0 < F
  S_lt1 : hdNx (Λ.L + ν) F < gcG 1
  F_mem : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → γ < b → F ∈ S.CSet a b
  S_mem : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → γ < b → hdNx (Λ.L + ν) F ∈ S.CSet a b
  F_code : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y, GxCl Z {gcG 0} y → F ≤ y → y < hdNx (Λ.L + ν) F →
    GxCl Z {gcG 0} F
  F_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y, GxCl Z {gcG 0} y → F ≤ y → y < hdNx (Λ.L + ν) F → γ < Z
  S_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z {gcG 0} (hdNx (Λ.L + ν) F) → γ < Z
  Fr_gt : ∀ {x}, InE x → x < Om1 → γ < x → Λ.l x + ν < Fr x
  Fr_P : ∀ {x}, InE x → x < Om1 → γ < x → LuP (Λ.l x + ν) (Fr x)
  S_Zo : ∀ {x}, InE x → x < Om1 → γ < x → hdNx (Λ.l x + ν) (Fr x) < Zo x
  Zo_fix : ∀ x, veblen 2 (Zo x) = Zo x
  Zo_G1 : ∀ x, InE x → x < Om1 → Zo x < gq 1 x
  Fr_pi : ∀ {σ ρ}, Bases σ ρ → γ < σ → Fr ρ ∈ TB ρ σ ∧ pi σ ρ (Fr ρ) = Fr σ
  S_pi : ∀ {σ ρ}, Bases σ ρ → γ < σ →
    hdNx (Λ.l ρ + ν) (Fr ρ) ∈ TB ρ σ ∧ pi σ ρ (hdNx (Λ.l ρ + ν) (Fr ρ)) = hdNx (Λ.l σ + ν) (Fr σ)

namespace WnQ3

variable {Λ : WnLv3} {ν : Ordinal.{0}} (Q : WnQ3 Λ ν)

theorem F_fixk (k : ℕ) : veblen (k : Ordinal.{0}) Q.F = Q.F := Λ.fixk Q.F_P k

theorem F_fixω : veblen ω Q.F = Q.F := Λ.fixω Q.F_P

theorem F_lt_S : Q.F < hdNx (Λ.L + ν) Q.F := hdNx_gt _ _

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : Q.γ < x)
include hx hx1 hγ

theorem Fr_lt1 : Q.Fr x < gq 1 x := (hdNx_gt _ _).trans ((Q.S_Zo hx hx1 hγ).trans (Q.Zo_G1 x hx hx1))

theorem Fr_fixk (k : ℕ) : veblen (k : Ordinal.{0}) (Q.Fr x) = Q.Fr x := Λ.rfixk hx (Q.Fr_P hx hx1 hγ) k

theorem Fr_fixω : veblen ω (Q.Fr x) = Q.Fr x := Λ.rfixω hx (Q.Fr_P hx hx1 hγ)

theorem Fr_gtx : x < Q.Fr x := ((Λ.l_ge x).trans le_self_add).trans_lt (Q.Fr_gt hx hx1 hγ)

end Base

theorem hS_le : hcS Q.F ≤ hdNx (Λ.L + ν) Q.F := hdS_le_Nx (Λ.ωL ν).le _

theorem hS_cl {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (h : GxCl Z {gcG 0} (hcS Q.F)) : Q.γ < Z := by
  rw [hcS_fix Q.F_fixω] at h
  exact Q.F_cl Z hZ hZ1 _ (hd_cl_succ_fix hc_one_le_om hZ hZ1 Q.G_lt.le h) le_rfl Q.F_lt_S

theorem hS_mem (S : InaccSeq.{0}) {a b : Ordinal.{0}} (ha : 0 < a) (hb : Q.γ < b) : hcS Q.F ∈ S.CSet a b := by
  rw [hcS_fix Q.F_fixω]
  exact CSet.phi_mem (gr_cst_mem ha _ ω (omega0_lt_gamma 1)) (CSet.succ_mem (Q.F_mem S ha hb))

theorem hS_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hγ : Q.γ < σ) :
    hcS (Q.Fr ρ) ∈ TB ρ σ ∧ pi σ ρ (hcS (Q.Fr ρ)) = hcS (Q.Fr σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hγρ : Q.γ < ρ := hγ.trans hB.2.2.1
  have hωσ : ω < σ := omega0_lt_inE hB.1
  obtain ⟨f1, f2⟩ := Q.Fr_pi hB hγ
  have h := glA_pi hB (mem_TB_of_lt hB hωσ) (hc_om_T hB.2.1 hρ1).2 f1 (gm1_T hB.2.1 hρ1 (Q.Fr_lt1 hB.2.1 hρ1 hγρ)).2
  rw [pi_lt hB hωσ, f2, hc_glA_fixW hB.2.1 hρ1 (Q.Fr_fixω hB.2.1 hρ1 hγρ) (Q.Fr_gtx hB.2.1 hρ1 hγρ)
    (Q.Fr_lt1 hB.2.1 hρ1 hγρ), hc_glA_fixW hB.1 hσ1 (Q.Fr_fixω hB.1 hσ1 hγ) (Q.Fr_gtx hB.1 hσ1 hγ)
    (Q.Fr_lt1 hB.1 hσ1 hγ)] at h
  exact h

/-- **AN (A3) PSEUDO-BASE IS A LEVEL-`ω` PSEUDO-BASE.** -/
noncomputable def toP : HgdP where
  F := Q.F
  Fr := Q.Fr
  γ := Q.γ
  Zo := Q.Zo
  γ_lt := Q.γ_lt
  F_fix := Q.F_fixk
  G_lt := Q.G_lt
  S_lt1 := Q.hS_le.trans_lt Q.S_lt1
  F_mem := Q.F_mem
  S_mem := fun S _ _ ha hb => Q.hS_mem S ha hb
  F_code := fun Z hZ hZ1 y hy hQy hyZ => Q.F_code Z hZ hZ1 y hy hQy (hyZ.trans_le Q.hS_le)
  F_cl := fun Z hZ hZ1 y hy hQy hyZ => Q.F_cl Z hZ hZ1 y hy hQy (hyZ.trans_le Q.hS_le)
  S_cl := fun Z hZ hZ1 h => Q.hS_cl hZ hZ1 h
  Fr_gt := fun hx hx1 hγ => Q.Fr_gtx hx hx1 hγ
  Fr_fix := fun hx hx1 hγ k => Q.Fr_fixk hx hx1 hγ k
  S_Zo := fun {x} hx hx1 hγ => (hdS_le_Nx (Λ.ωl hx ν).le _).trans_lt (Q.S_Zo hx hx1 hγ)
  Zo_fix := Q.Zo_fix
  Zo_G1 := Q.Zo_G1
  Fr_pi := Q.Fr_pi
  S_pi := fun hB hγ => Q.hS_pi hB hγ

end WnQ3

/-- **The specification of a step at an (A3) pseudo-base** (the fields of `Hn.HnVSpec`): the system `T` has the
bound `hdNx (L+ν) F`, the gate `γ`, the base reading `hdNx (ℓ(x)+ν) (F(x))`, extends `U`, reads `F` as `F(x)`. -/
structure WnSpec3 {Λ : WnLv3} {ν : Ordinal.{0}} (P : WnQ3 Λ ν) (U T : HgVD) : Prop where
  B : T.B = hdNx (Λ.L + ν) P.F
  γ : T.γ = P.γ
  b : ∀ x, InE x → x < Om1 → P.γ < x → T.b x = hdNx (Λ.l x + ν) (P.Fr x)
  Z : ∀ x, InE x → x < Om1 → T.Z x = if P.γ < x then evZ (hdNx (Λ.l x + ν) (P.Fr x)) else P.Zo x
  extR : ∀ c x, c < U.B → T.R c x = U.R c x
  extg : ∀ c, c < U.B → T.g c = U.g c
  high : ∀ c σ, P.F ≤ c → c < hdNx (Λ.L + ν) P.F → InE σ → σ < Om1 → T.g c < σ → P.γ < σ
  RF : ∀ x, InE x → x < Om1 → P.γ < x → T.R P.F x = P.Fr x
  gF : ∀ x, InE x → x < Om1 → (T.g P.F < x ↔ P.γ < x)

/-- **THE (A3) PACKAGE** (as `Hn.HnPk`): an (A3) datum and, at every pseudo-base `Q` of its level and every system
`U` starting it, a system with the specification. -/
structure WnPk3 where
  Λ : WnLv3
  St0 : ∀ (Q : WnQ3 Λ 0) (U : HgVD), HgSStart (hgdPB Q.toP) U → HgVD
  h0 : ∀ Q U h, WnSpec3 Q U (St0 Q U h)

/-! ## The (A3) invariant at the ladder levels `t_n` -/

/-- **THE (A3) INVARIANT AT `t_n`**: a package at the level `t_n` with gate `< K`, and a pseudo-base of level
`t_n` at the point `φ(t_n, G)` with gate `< K` that is started by some system `U`. -/
def WnEnt3 (S : InaccSeq.{0}) (n : ℕ) : Prop :=
  ∃ K : WnPk3, K.Λ.L = Wj.wjT n ∧ K.Λ.g < Td.tdK S ∧
    ∃ (Q : WnQ3 K.Λ 0) (U : HgVD) (_ : HgSStart (hgdPB Q.toP) U),
      Q.F = veblen (Wj.wjT n) (gcG 0) ∧ Q.γ < Td.tdK S

/-- **The invariant gives the system at `φ(t_n, G+1)` with gate `< K`.** -/
theorem wnEnt3_sys {S : InaccSeq.{0}} {n : ℕ} (h : WnEnt3 S n) :
    ∃ V : HgVD, V.B = veblen (Wj.wjT n) (gcG 0 + 1) ∧ V.γ < Td.tdK S := by
  obtain ⟨K, hL, -, Q, U, hU, hF, hγ⟩ := h
  refine ⟨K.St0 Q U hU, ?_, ?_⟩
  · rw [(K.h0 Q U hU).B, add_zero, hF, hL, hdNx_veb]
  · rw [(K.h0 Q U hU).γ]; exact hγ

/-- **The bound fields of the pseudo-base at `φ(t_n, G)` hold**: `G < φ(t_n, G)` and `hdNx t_n (φ(t_n, G)) < Γ(1)`. -/
theorem wnQ3_bounds (n : ℕ) : gcG 0 < veblen (Wj.wjT n) (gcG 0) ∧
    hdNx (Wj.wjT n + 0) (veblen (Wj.wjT n) (gcG 0)) < gcG 1 ∧ LuP (Wj.wjT n + 0) (veblen (Wj.wjT n) (gcG 0)) := by
  obtain ⟨hG, -, -, h4⟩ := Wj.wjT_spec n
  refine ⟨hG.trans_le (by simpa using left_le_veblen (Wj.wjT n) (gcG 0)), ?_, ⟨gcG 0, by rw [add_zero]⟩⟩
  rw [add_zero, hdNx_veb]; exact h4

end Googology.Trans.PoR.InaccPsi.R2.Wn
