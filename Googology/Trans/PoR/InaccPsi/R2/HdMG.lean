import Googology.Trans.PoR.InaccPsi.R2.HdMRecL

/-!
# HdMG: `G` AS A BASE OF EVERY CONSTANT LEVEL; EVERY `φ(α+1, G+1)`, `ω ≤ α < ε₀`, IS LOCATED; THE FRONTIER
# `ι(Γ(φ(ε₀, G+1)))`

`G = Γ_{Ω₁+1}` (reading `Γ_{x+1}`, gate `0`, outer low field `φ(ε₀, Γ_{x+1}+1)`) is a base of every constant level
`α` (`hdGB α`).  The systems `hdGL ν` (bound `N_{ω+ν}(G) = φ(ω+ν+1, G+1)`, base gate `0`) are defined by one recursion
on `ν < ε₀`: `hdGL 0 = Hd.hdGT` (the system at `φ(ω+1, G+1)`); `hdGL (ν+1)` is the union of all gated offsets over
`G` at level `ω+ν+1` with the step `Hd.hdLS (ν+1)`, started at `hdGL ν`; at a limit `λ` the systems `hdGL λ_k` form a
gated `ω`-chain whose union (bound `φ(ω+λ, G+1)`) starts the offset recursion over `G` at level `ω+λ` with the step
`Hd.hdLS λ`.  The invariant (`hdGL_inv`): every `hdGL ν` has bound `φ(ω+ν+1, G+1)`, gate `0`, base reading
`N_{ω+ν}(Γ_{x+1})`, bound field `evZ` of it, and extends every `hdGL ν'`, `ν' ≤ ν`.  So every `φ(α+1, G+1)`,
`ω ≤ α < ε₀`, is located (`hdGL_loc`), and ENUM-REACH, CapV hold at every range restart below
`ι(Γ(φ(ε₀, G+1)))` (`hdGE_enum`, `hdGE_capV`, `hdGE_road`), unconditionally.

* `hd_veb_left_lt`, `hdBE`, `hd_G_fixL`, `hd_G_fixLx`, `hd_NL_eq`, `hd_NL_glA`, `hd_GL_pi`, `hd_GL_lt1`,
  `hdGB` (**`G` AS A BASE OF EVERY CONSTANT LEVEL**), `hdG_start` (a system of the right shape starts the offset
  recursion over `G`);
* `HdGOK`, `HdGCoh`, `hdGLCh` (the chain at a limit), `hdGLSucc`, `hdGLLim`, `hdGL` (**THE RECURSION ON THE LEVEL**),
  `hdGL_inv` (**THE INVARIANT**), `hdGL_B`, `hdGL_γ`, `hdGL_loc`, `hdGL_blk` (BLK^O below each);
* `hdGE` (`φ(ε₀, G+1)`), `hdGE_cof`, `hdGE_enum`, `hdGE_capV`, `hdGE_road` (**THE ROAD**), `hdGE_P`, `hdGE_fr_order`.

No new axiom.  New definitions: `hdBE`, `hdGB`, `HdGOK`, `HdGCoh`, `hdGLCh`, `hdGLSucc`, `hdGLLim`, `hdGL`, `hdGE`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hd

open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb Googology.Trans.PoR.InaccPsi.R2.Gp
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## `G` at every constant level -/

/-- `φ(a, b+1) < φ(a', b+1)` for `a < a'`. -/
theorem hd_veb_left_lt {a a' : Ordinal.{0}} (h : a < a') (b : Ordinal.{0}) : veblen a (b + 1) < veblen a' (b + 1) := by
  have h1 := (isNormal_veblen a).strictMono (hd_succ_lt (pos_iff_ne_zero.1 (zero_le.trans_lt h)) b)
  rwa [veblen_veblen_of_lt h] at h1

/-- **The outer low field `φ(ε₀, Γ_{x+1}+1)`.** -/
noncomputable def hdBE (x : Ordinal.{0}) : Ordinal.{0} := veblen ε₀ (lgG x + 1)

theorem hd_eps0_ne : (ε₀ : Ordinal.{0}) ≠ 0 := hc_eps0_E.pos.ne'

theorem hd_lt_G {α : Ordinal.{0}} (h : α < ε₀) : α < gcG 0 :=
  h.trans_le (gc_eps0_le (Low.opow_eq_self_of_SC (gcG_SC 0)))

/-- **`G` is a fixed point of every `φ(α, ·)`, `α < ε₀`.** -/
theorem hd_G_fixL {α : Ordinal.{0}} (h : α < ε₀) : veblen α (gcG 0) = gcG 0 := gn_veb_fix (gcG_SC 0) (hd_lt_G h)

/-- **`N_α(G) = φ(α+1, G+1)`** for `α + 1 < ε₀`. -/
theorem hd_NL_eq {α : Ordinal.{0}} (h : α + 1 < ε₀) : hcN α (gcG 0) = veblen (α + 1) (gcG 0 + 1) := by
  have := hcN_veb α (gcG 0); rwa [hd_G_fixL h] at this

/-- **`φ(α, G+1) < Γ_{Ω₁+2}`** for `α < ε₀`. -/
theorem hd_GL_lt1 {α : Ordinal.{0}} (h : α < ε₀) : veblen α (gcG 0 + 1) < gcG 1 := by
  have hG1 := gcG_SC 1
  have hE := Low.opow_eq_self_of_SC hG1
  have hfix : veblen α (gcG 1) = gcG 1 := gn_veb_fix hG1 (h.trans_le (gc_eps0_le hE))
  have h2 := (isNormal_veblen α).strictMono ((ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt zero_lt_one))
  rwa [hfix] at h2

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem hd_lt_Gx {α : Ordinal.{0}} (h : α < ε₀) : α < lgG x :=
  (h.trans_le (gc_eps0_le hx)).trans (lgG_facts hx hx1).2.1

theorem hd_G_fixLx {α : Ordinal.{0}} (h : α < ε₀) (h1 : 1 ≤ α) : veblen α (lgG x) = lgG x :=
  hc_G_fix hx hx1 h1 (hd_lt_Gx hx hx1 h)

/-- **`N_α(Γ_{x+1}) = φ(α+1, Γ_{x+1}+1) = ϑˣ(Ω₁·(α+1) + Γ_{x+1})`** for `α + 1 < ε₀`. -/
theorem hd_NL_glA {α : Ordinal.{0}} (h : α + 1 < ε₀) :
    hcN α (lgG x) = veblen (α + 1) (lgG x + 1) ∧ hcN α (lgG x) = glA (α + 1) (lgG x) x := by
  have e : hcN α (lgG x) = veblen (α + 1) (lgG x + 1) := by
    have := hcN_veb α (lgG x); rwa [hd_G_fixLx hx hx1 h le_add_self] at this
  exact ⟨e, by rw [e, hc_glA_GG hx hx1 le_add_self (hd_lt_Gx hx hx1 h)]⟩

/-- **`φ(α, Γ_{x+1}+1) < B_x(x)`** for `α < ε₀`. -/
theorem hd_veb_lt_BR {α : Ordinal.{0}} (h : α < ε₀) : veblen α (lgG x + 1) < hcBR x :=
  hd_veb_left_lt (h.trans_le (gc_eps0_le hx)) _

theorem hd_BE_le_BR : hdBE x ≤ hcBR x := by
  rcases (gc_eps0_le hx).lt_or_eq with h | h
  · exact (hd_veb_left_lt h _).le
  · unfold hdBE hcBR; rw [h]

end Base

/-- **Lemma EXACT for `φ(α, Γ_{ρ+1}+1) = ϑᵖ(Ω₁·α + Γ_{ρ+1})`**, every constant level `α`. -/
theorem hd_GL_pi {α σ ρ : Ordinal.{0}} (hα : HdLvl α) (hB : Bases σ ρ) :
    veblen α (lgG ρ + 1) ∈ TB ρ σ ∧ pi σ ρ (veblen α (lgG ρ + 1)) = veblen α (lgG σ + 1) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨g1, g2⟩ : lgG ρ ∈ TB ρ σ ∧ pi σ ρ (lgG ρ) = lgG σ := Go.goGl.ba_pi σ ρ hB
  have h := hdm_glA_pi hα hB g1 (mg_lgG_lt_G1 hB.2.1 hρ1)
  rw [g2, hc_glA_GG hB.2.1 hρ1 hα.one_le (hd_lt_Gx hB.2.1 hρ1 hα.2),
    hc_glA_GG hB.1 hσ1 hα.one_le (hd_lt_Gx hB.1 hσ1 hα.2)] at h
  exact h

/-- **`G` AS A BASE OF EVERY CONSTANT LEVEL `α`**: reading `Γ_{x+1}`, gate `0`, outer low field `φ(ε₀, Γ_{x+1}+1)`. -/
noncomputable def hdGB (α : Ordinal.{0}) (hα : HdLvl α) : HdB α where
  F := gcG 0
  Fr := lgG
  γ := 0
  Zo := hdBE
  lv := hα
  γ_lt := Ordinal.omega_pos 1
  F_fix := hd_G_fixL hα.2
  G_le := le_rfl
  N_lt1 := by rw [hd_NL_eq hα.succ.2]; exact hd_GL_lt1 hα.succ.2
  F_mem := fun S _ _ ha _ => gmS_G0_mem S ha
  N_mem := fun S _ _ ha _ => by
    rw [hd_NL_eq hα.succ.2]
    exact CSet.phi_mem (hα.succ.mem S ha _) (CSet.succ_mem (gmS_G0_mem S ha))
  F_code := fun _ _ _ _ _ _ _ => GxCl.atom (Set.mem_singleton _)
  F_cl := fun _ hZ _ _ _ _ _ => hZ.1
  N_cl := fun _ hZ _ _ => hZ.1
  Fr_gt := fun hx hx1 _ => (lgG_facts hx hx1).2.1
  Fr_fix := fun hx hx1 _ => hd_G_fixLx hx hx1 hα.2 hα.one_le
  N_Zo := fun hx hx1 _ => by
    rw [(hd_NL_glA hx hx1 hα.succ.2).1]; exact hd_veb_left_lt hα.succ.2 _
  Zo_fix := fun _ => veblen_veblen_of_lt ((show (2 : Ordinal.{0}) < ω from gw_two_lt_w).trans
    (omega0_lt_inE hc_eps0_E)) _
  Zo_BR := fun _ hx hx1 => hd_BE_le_BR hx hx1
  Fr_pi := fun {σ ρ} hB _ => Go.goGl.ba_pi σ ρ hB
  N_pi := fun {σ ρ} hB _ => by
    rw [(hd_NL_glA hB.2.1 hB.2.2.2 hα.succ.2).1, (hd_NL_glA hB.1 (hB.2.2.1.trans hB.2.2.2) hα.succ.2).1]
    exact hd_GL_pi hα.succ hB

/-- **A system with bound `φ(α, G+1)`, gate `0`, base reading `φ(α, Γ_{x+1}+1)` and bound field `evZ` of it STARTS
THE OFFSET RECURSION OVER `G` AT LEVEL `α`.** -/
theorem hdG_start {α : Ordinal.{0}} (hα : HdLvl α) (T : HcVD) (hB : T.B = veblen α (gcG 0 + 1)) (hγ : T.γ = 0)
    (hb : ∀ x, InE x → x < Om1 → T.b x = veblen α (lgG x + 1))
    (hZ : ∀ x, InE x → x < Om1 → T.Z x = evZ (veblen α (lgG x + 1))) : HdMStart (hdGB α hα) T where
  B := by rw [add_zero]; exact hB
  Zb := fun x hx hx1 => by
    rw [hZ x hx hx1, (hdGB α hα).Zl_eq hx.pos]
    exact (hb_evZ_lt_fix2 (hc_fix_down hα.two_lt.le (hcN_fix α _)) hc_next_lt_N).le
  st := fun h2 hZ' => {
    ix := by
      show T.ix = veblen α (gcG 0 + 1 + 0)
      rw [add_zero]; exact hc_ix_of_B (veblen_veblen_of_lt hα.one_lt _) hB
    γ := fun x hx _ => by
      show T.γ < x ↔ max 0 (T.g 0) < x
      rw [hγ, T.g_zero, max_self]
    b := fun x hx hx1 _ => by
      show T.b x = glA α (lgG x + T.R 0 x) x
      rw [T.R_zero, add_zero, hb x hx hx1, hc_glA_GG hx hx1 hα.one_le (hd_lt_Gx hx hx1 hα.2)]
    Z := fun x hx hx1 => by
      unfold HcPB.Zst
      show T.Z x = if max 0 (T.g 0) < x then evZ (glA α (lgG x + T.R 0 x) x) else (hdGB α hα).Zl x
      rw [T.g_zero, max_self, if_pos hx.pos, T.R_zero, add_zero, hZ x hx hx1,
        hc_glA_GG hx hx1 hα.one_le (hd_lt_Gx hx hx1 hα.2)] }
  high0 := fun _ _ _ _ hσ _ _ => hσ.pos

/-! ## The recursion on the level -/

/-- **The shape of the system at level `ω + ν`**: bound `N_{ω+ν}(G)`, gate `0`, base reading `N_{ω+ν}(Γ_{x+1})`,
bound field `evZ` of it. -/
def HdGOK (ν : Ordinal.{0}) (T : HcVD) : Prop :=
  T.B = hcN (ω + ν) (gcG 0) ∧ T.γ = 0 ∧ (∀ x, InE x → x < Om1 → T.b x = hcN (ω + ν) (lgG x)) ∧
    ∀ x, InE x → x < Om1 → T.Z x = evZ (hcN (ω + ν) (lgG x))

/-- **The condition at a limit**: every earlier system has the shape, and later systems extend earlier ones. -/
def HdGCoh (l : Ordinal.{0}) (IH : ∀ ν, ν < l → HcVD) : Prop :=
  (∀ ν (h : ν < l), HdGOK ν (IH ν h)) ∧ ∀ ν ν' (h : ν < l) (h' : ν' < l), ν ≤ ν' → ∀ c x, c < (IH ν h).B →
    (IH ν' h').R c x = (IH ν h).R c x ∧ (IH ν' h').g c = (IH ν h).g c

section LimCh

variable (l : Ordinal.{0}) (hl : IsSuccLimit l) (hle : l < ε₀) (IH : ∀ ν, ν < l → HcVD) (H : HdGCoh l IH)

include hle in
theorem hdGL_NxG : hdNx (ω + l) (gcG 0) = veblen (ω + l) (gcG 0 + 1) := hdNx_fixP (hd_G_fixL (hd_lev hle).2)

include hle in
theorem hdGL_Nxx {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    hdNx (ω + l) (lgG x) = veblen (ω + l) (lgG x + 1) :=
  hdNx_fixP (hd_G_fixLx hx hx1 (hd_lev hle).2 (hd_lev hle).one_le)

include H in
/-- **THE CHAIN AT A LIMIT LEVEL**: the systems at the levels `ω + λ_k`; union bound `φ(ω+λ, G+1)`. -/
noncomputable def hdGLCh : HdCh where
  D := fun k => IH (gpFs l k) (gpFs_lt hl hle k)
  B := hdNx (ω + l) (gcG 0)
  b := fun x => hdNx (ω + l) (lgG x)
  γ := 0
  Zo := hdBE
  γ_lt := Ordinal.omega_pos 1
  γ0 := fun k => (H.1 _ _).2.1
  γ_cl := fun _ hZ _ _ => hZ.1
  B_mono := fun k => by
    rw [(H.1 _ _).1, (H.1 _ _).1]; exact hcN_mono ((hdLmOf l hl hle).mono k) _
  B_lt := fun k => by
    rw [(H.1 _ _).1]; exact hdN_lt_Nx ((hdLmOf l hl hle).lim.add_one_lt ((hdLmOf l hl hle).lt k))
  B_cof := fun c hc => by
    obtain ⟨k, hk⟩ := hdNx_cof (hdLmOf l hl hle).lim (hdLmOf l hl hle).lt (hdLmOf l hl hle).mono
      (hdLmOf l hl hle).cof hc
    exact ⟨k, by rw [(H.1 _ _).1]; exact hk⟩
  R_ext := fun k c x hc => (H.2 _ _ _ _ (gpFs_mono hl hle k).le c x hc).1
  g_ext := fun k c hc => (H.2 _ _ _ _ (gpFs_mono hl hle k).le c 0 hc).2
  B_lt1 := by rw [hdGL_NxG l hle]; exact hd_GL_lt1 (hd_lev hle).2
  B_fix := hdNx_fix (hd_lev hle).one_lt _
  B_mem := fun S _ _ ha _ => by
    rw [hdGL_NxG l hle]
    exact CSet.phi_mem ((hd_lev hle).mem S ha _) (CSet.succ_mem (gmS_G0_mem S ha))
  b_ge := fun k x hx hx1 _ => by
    rw [(H.1 _ _).2.2.1 x hx hx1]
    exact (hdN_lt_Nx ((hdLmOf l hl hle).lim.add_one_lt ((hdLmOf l hl hle).lt k))).le
  b_cof := fun x hx hx1 _ μ hμ => by
    obtain ⟨k, hk⟩ := hdNx_cof (hdLmOf l hl hle).lim (hdLmOf l hl hle).lt (hdLmOf l hl hle).mono
      (hdLmOf l hl hle).cof hμ
    exact ⟨k, by rw [(H.1 _ _).2.2.1 x hx hx1]; exact hk⟩
  b_fix := fun x _ _ _ => hdNx_fix (hd_lev hle).one_lt _
  b_gt := fun x hx hx1 _ => (lgG_facts hx hx1).2.1.trans (hdNx_gt _ _)
  b_lt := fun x hx hx1 _ => by rw [hdGL_Nxx l hle hx hx1]; exact hd_veb_lt_BR hx hx1 (hd_lev hle).2
  b_pi := fun σ ρ hB _ => by
    rw [hdGL_Nxx l hle hB.2.1 hB.2.2.2, hdGL_Nxx l hle hB.1 (hB.2.2.1.trans hB.2.2.2)]
    exact hd_GL_pi (hd_lev hle) hB
  Z_low := fun _ x hx _ hγ => absurd hx.pos hγ
  Zo_fix := fun _ => veblen_veblen_of_lt (one_lt_omega0.trans (omega0_lt_inE hc_eps0_E)) _
  Zo_BR := fun _ hx hx1 => hd_BE_le_BR hx hx1

theorem hdGLCh_start : HdMStart (hdGB (ω + l) (hd_lev hle)) (hdGLCh l hl hle IH H).U :=
  hdG_start (hd_lev hle) _ (hdGL_NxG l hle) rfl (fun x hx hx1 => hdGL_Nxx l hle hx hx1)
    (fun x hx _ => by
      show (if (0 : Ordinal.{0}) < x then evZ (hdNx (ω + l) (lgG x)) else hdBE x) = _
      rw [if_pos hx.pos, hdGL_Nxx l hle hx (by assumption)])

end LimCh

open Classical in
/-- **The successor case**: the union of all gated offsets over `G` at level `ω + ν + 1`, started at `T`. -/
noncomputable def hdGLSucc (ν : Ordinal.{0}) (T : HcVD) : HcVD :=
  if H : ∃ hν : ν + 1 < ε₀, HdMStart (hdGB (ω + (ν + 1)) (hd_lev hν)) T then
    hdMTU (St := hdLS (ν + 1)) (fun Q U h => hdLS_spec H.choose Q U h) H.choose_spec
  else T

open Classical in
/-- **The limit case**: the union of the chain, then all gated offsets over `G` at level `ω + λ`. -/
noncomputable def hdGLLim (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ ν, ν < l → HcVD) : HcVD :=
  if H : ∃ hle : l < ε₀, HdGCoh l IH then
    hdMTU (St := hdLS l) (fun Q U h => hdLS_spec H.choose Q U h)
      (hdGLCh_start l hl H.choose IH H.choose_spec)
  else hcWU

/-- **THE SYSTEM AT `φ(ω+ν+1, G+1)`, BY ONE RECURSION ON THE LEVEL.** -/
noncomputable def hdGL (ν : Ordinal.{0}) : HcVD :=
  Ordinal.limitRecOn (motive := fun _ => HcVD) ν hdGT hdGLSucc hdGLLim

theorem hdGL_zero : hdGL 0 = hdGT := by unfold hdGL; rw [Ordinal.limitRecOn_zero]

theorem hdGL_succ (ν : Ordinal.{0}) : hdGL (ν + 1) = hdGLSucc ν (hdGL ν) := by
  unfold hdGL; rw [Ordinal.limitRecOn_add_one]

theorem hdGL_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : hdGL l = hdGLLim l hl (fun ν _ => hdGL ν) := by
  unfold hdGL; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem hdGT_OK : HdGOK 0 hdGT := by
  refine ⟨by rw [add_zero]; exact hdGT_B.trans hdNG_eq.symm, rfl, fun x _ _ => by rw [add_zero]; rfl,
    fun x hx _ => ?_⟩
  rw [add_zero]
  show (if (0 : Ordinal.{0}) < x then evZ (hcNw (lgG x)) else hcBW x) = _
  rw [if_pos hx.pos]; rfl

/-- **The union over `G` at level `α` has the shape at the level `α`.** -/
theorem hdG_TU_OK {ν : Ordinal.{0}} (hν : ν < ε₀) {S0 : HcVD} (hS : HdMStart (hdGB (ω + ν) (hd_lev hν)) S0) :
    HdGOK ν (hdMTU (St := hdLS ν) (fun Q U h => hdLS_spec hν Q U h) hS) :=
  ⟨rfl, rfl, fun _ _ _ => rfl, fun x hx _ => by
    show (if (0 : Ordinal.{0}) < x then evZ (hcN (ω + ν) (lgG x)) else hdBE x) = _
    rw [if_pos hx.pos]⟩

/-- **The shape at level `ω + ν` starts the offset recursion over `G` at level `ω + ν + 1`.** -/
theorem hdG_OK_start {ν : Ordinal.{0}} (hν : ν + 1 < ε₀) {T : HcVD} (h : HdGOK ν T) :
    HdMStart (hdGB (ω + (ν + 1)) (hd_lev hν)) T := by
  have hl1 : ω + ν + 1 < ε₀ := by rw [← hd_lev_e]; exact (hd_lev hν).2
  refine hdG_start (hd_lev hν) T ?_ h.2.1 (fun x hx hx1 => ?_) (fun x hx hx1 => ?_)
  · rw [h.1, hd_NL_eq hl1, hd_lev_e]
  · rw [h.2.2.1 x hx hx1, (hd_NL_glA hx hx1 hl1).1, hd_lev_e]
  · rw [h.2.2.2 x hx hx1, (hd_NL_glA hx hx1 hl1).1, hd_lev_e]

/-- **THE INVARIANT**: every `hdGL ν`, `ν < ε₀`, has the shape at level `ω + ν` and extends every `hdGL ν'`,
`ν' ≤ ν`. -/
theorem hdGL_inv : ∀ ν, ν < ε₀ → HdGOK ν (hdGL ν) ∧ ∀ ν', ν' ≤ ν → ∀ c x, c < (hdGL ν').B →
    (hdGL ν).R c x = (hdGL ν').R c x ∧ (hdGL ν).g c = (hdGL ν').g c := by
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hν
  rcases zero_or_succ_or_isSuccLimit ν with h0 | ⟨μ, hμ⟩ | hlim
  · subst h0
    rw [hdGL_zero]
    refine ⟨hdGT_OK, fun ν' hν' c x _ => ?_⟩
    rw [nonpos_iff_eq_zero.1 hν', hdGL_zero]; exact ⟨rfl, rfl⟩
  · have hμ' : ν = μ + 1 := by rw [← hμ, succ_eq_add_one]
    subst hμ'
    have hμε : μ < ε₀ := (lt_add_one μ).trans hν
    obtain ⟨hok, hext⟩ := IH μ (lt_add_one μ) hμε
    have hS := hdG_OK_start hν hok
    have e : hdGL (μ + 1) = hdMTU (St := hdLS (μ + 1)) (fun Q U h => hdLS_spec hν Q U h) hS := by
      rw [hdGL_succ]; unfold hdGLSucc; rw [dif_pos ⟨hν, hS⟩]
    rw [e]
    refine ⟨hdG_TU_OK hν hS, fun ν' hν' c x hc => ?_⟩
    rcases hν'.lt_or_eq with hlt | heq
    · have hle : ν' ≤ μ := Order.lt_add_one_iff.1 hlt
      have hcμ : c < (hdGL μ).B := by
        rw [hok.1]; rw [(IH ν' (lt_of_le_of_lt hle (lt_add_one μ)) (hle.trans_lt hμε)).1.1] at hc
        exact hc.trans_le (hcN_mono ((add_le_add_iff_left ω).2 hle) _)
      obtain ⟨r2, g2⟩ := hext ν' hle c x hc
      exact ⟨(hdMTU_R0 _ hS hcμ x).trans r2, (hdMTU_g0 _ hS hcμ).trans g2⟩
    · subst heq; rw [e]; exact ⟨rfl, rfl⟩
  · have hcoh : HdGCoh ν (fun ν' _ => hdGL ν') :=
      ⟨fun ν' h => (IH ν' h (h.trans hν)).1, fun ν₁ ν₂ h₁ h₂ h12 c x hc =>
        (IH ν₂ h₂ (h₂.trans hν)).2 ν₁ h12 c x hc⟩
    have hS := hdGLCh_start ν hlim hν (fun ν' _ => hdGL ν') hcoh
    have e : hdGL ν = hdMTU (St := hdLS ν) (fun Q U h => hdLS_spec hν Q U h) hS := by
      rw [hdGL_limit hlim]; unfold hdGLLim; rw [dif_pos ⟨hν, hcoh⟩]
    rw [e]
    refine ⟨hdG_TU_OK hν hS, fun ν' hν' c x hc => ?_⟩
    rcases hν'.lt_or_eq with hlt | heq
    · obtain ⟨k, hk⟩ := gpFs_cof hlim hν ν' hlt
      have hkl := gpFs_lt hlim hν k
      obtain ⟨hokk, hextk⟩ := IH _ hkl (hkl.trans hν)
      have hck : c < (hdGL (gpFs ν k)).B := by
        rw [hokk.1]; rw [(IH ν' hlt (hlt.trans hν)).1.1] at hc
        exact hc.trans_le (hcN_mono ((add_le_add_iff_left ω).2 hk.le) _)
      set C := hdGLCh ν hlim hν (fun ν' _ => hdGL ν') hcoh with hC
      have hcC : c < C.U.B := hck.trans (C.B_lt k)
      obtain ⟨r2, g2⟩ := hextk ν' hk.le c x hc
      refine ⟨(hdMTU_R0 _ hS hcC x).trans ((C.U_R (k := k) hck x).trans r2),
        (hdMTU_g0 _ hS hcC).trans ((C.U_g (k := k) hck).trans g2)⟩
    · subst heq; rw [e]; exact ⟨rfl, rfl⟩

theorem hdGL_B {ν : Ordinal.{0}} (hν : ν < ε₀) : (hdGL ν).B = veblen (ω + ν + 1) (gcG 0 + 1) := by
  rw [(hdGL_inv ν hν).1.1, hd_NL_eq (by rw [← hd_lev_e]; exact (hd_lev (hc_eps0_lim.add_one_lt hν)).2)]

theorem hdGL_γ {ν : Ordinal.{0}} (hν : ν < ε₀) : (hdGL ν).γ = 0 := (hdGL_inv ν hν).1.2.1

/-- **EVERY `φ(ω+ν+1, G+1)`, `ν < ε₀`, IS LOCATED**: `Λ⁺ = ι(Γ(φ(ω+ν+1, G+1))·ω)`, `P(…) < L(0)`. -/
theorem hdGL_loc (S : InaccSeq.{0}) {ν : Ordinal.{0}} (hν : ν < ε₀) :
    ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG (veblen (ω + ν + 1) (gcG 0 + 1)) * ω) ∧
      upsilon (xtB1 X) = Pv S (gcG (veblen (ω + ν + 1) (gcG 0 + 1)) * ω) ∧
      Pv S (gcG (veblen (ω + ν + 1) (gcG 0 + 1)) * ω) < Nc.ncL S 0 := by
  rw [← hdGL_B hν]; exact hcV_locD (hdGL ν) S (by rw [hdGL_γ hν]; exact Td.tdK_SC.1)

/-- **Theorem BLK^O below `P(Γ(φ(ω+ν+1, G+1))·ω)`, with the exact reaches**, every `ν < ε₀` (UNCONDITIONAL). -/
theorem hdGL_blk (S : InaccSeq.{0}) {ν : Ordinal.{0}} (hν : ν < ε₀) :
    let X := gsX (hdGL ν).step.toRS _ (hdGL ν).E_lt_B.le (hdGL ν).B_lt_NB S
      (hcV_locD_g (hdGL ν) S (by rw [hdGL_γ hν]; exact Td.tdK_SC.1))
    (∀ c' d, c' < d → d < upsilon (xtB1 X) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 X ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧ d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 X →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec X l)) ∧
    (∀ α < upsilon (xtB1 X), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  hcV_locD_blk (hdGL ν) S (by rw [hdGL_γ hν]; exact Td.tdK_SC.1)

/-! ## The frontier `ι(Γ(φ(ε₀, G+1)))` -/

/-- **`φ(ε₀, G+1)`.** -/
noncomputable def hdGE : Ordinal.{0} := veblen ε₀ (gcG 0 + 1)

/-- The levels `ω + ω↑↑k` are cofinal in `ε₀`. -/
noncomputable def hdEseq (k : ℕ) : Ordinal.{0} := ω + (fun a : Ordinal.{0} => ω ^ a)^[k] 0

theorem hdEseq_lt (k : ℕ) : hdEseq k < ε₀ := (hd_lev (iterate_omega0_opow_lt_epsilon_zero k)).2

theorem hdEseq_mono (k : ℕ) : hdEseq k ≤ hdEseq (k + 1) := by
  unfold hdEseq
  refine (add_le_add_iff_left ω).2 ?_
  rw [Function.iterate_succ_apply']
  exact right_le_opow _ one_lt_omega0

theorem hdEseq_cof (t : Ordinal.{0}) (ht : t < ε₀) : ∃ k, t < hdEseq k := by
  obtain ⟨n, hn⟩ := lt_epsilon_zero.1 ht
  exact ⟨n, hn.trans_le le_add_self⟩

theorem hd_eps0_lt_G : (ε₀ : Ordinal.{0}) < gcG 0 := gc_eps0_le_Om1.trans_lt (gcG_Om1_lt 0)

theorem hdGE_eq : hdGE = hdNx ε₀ (gcG 0) := (hdNx_fixP (gn_veb_fix (gcG_SC 0) hd_eps0_lt_G)).symm

/-- **Every ordinal below `φ(ε₀, G+1)` lies below some `φ(ω+ν+1, G+1)`, `ν < ε₀`.** -/
theorem hdGE_cofB {β : Ordinal.{0}} (hβ : β < hdGE) : ∃ ν, ν < ε₀ ∧ β < (hdGL ν).B := by
  rw [hdGE_eq] at hβ
  obtain ⟨k, hk⟩ := hdNx_cof hc_eps0_lim hdEseq_lt hdEseq_mono hdEseq_cof hβ
  have hν := iterate_omega0_opow_lt_epsilon_zero k
  exact ⟨_, hν, by rw [(hdGL_inv _ hν).1.1]; exact hk⟩

theorem hdGE_lt1 : hdGE < gcG 1 := by
  have hG1 := gcG_SC 1
  have hE := Low.opow_eq_self_of_SC hG1
  have hfix : veblen ε₀ (gcG 1) = gcG 1 := gn_veb_fix hG1 (hd_eps0_lt_G.trans (gcG_lt zero_lt_one))
  have h2 := (isNormal_veblen ε₀).strictMono ((ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt zero_lt_one))
  rw [hfix] at h2
  exact h2

theorem hdGE_lim : IsSuccLimit hdGE := ev_isSuccLimit_of_inE (gg_veblen_eps hd_eps0_ne)

/-- **The located bounds `ι(Γ(φ(ω+ν+1, G+1))·ω)`, `ν < ε₀`, are cofinal below `ι(Γ(φ(ε₀, G+1)))`.** -/
theorem hdGE_cof (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : l < iota S (gcG hdGE)) :
    ∃ ν, ν < ε₀ ∧ l < iota S (gcG (hdGL ν).B * ω) := by
  have hlim : IsSuccLimit (gcG hdGE) := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (gcG_SC _))
  rw [iota_limit hlim] at hl
  haveI : Nonempty (Iio (gcG hdGE)) := ⟨⟨0, hlim.bot_lt⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hl
  obtain ⟨β, hβ, heβ⟩ := gcG_lt_of_lt_limit hdGE_lim e.2
  obtain ⟨ν, hν, hβν⟩ := hdGE_cofB hβ
  refine ⟨ν, hν, he.trans_le (iota_mono _ _ ((heβ.trans (gcG_lt hβν)).trans_le ?_).le)⟩
  exact le_mul_of_one_le_right' one_lt_omega0.le

/-- **ENUM-REACH at every range restart below `ι(Γ(φ(ε₀, G+1)))`, fixed points included** (UNCONDITIONAL). -/
theorem hdGE_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG hdGE)) :
    CdUpper S l ∧ CdLower S l := by
  obtain ⟨ν, hν, h⟩ := hdGE_cof S hl
  exact hcV_locD_enum (hdGL ν) S (by rw [hdGL_γ hν]; exact Td.tdK_SC.1) hr h

/-- **CapV at every range restart below `ι(Γ(φ(ε₀, G+1)))`** (UNCONDITIONAL). -/
theorem hdGE_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG hdGE)) :
    CdCapV S l := by
  obtain ⟨ν, hν, h⟩ := hdGE_cof S hl
  exact hcV_locD_capV (hdGL ν) S (by rw [hdGL_γ hν]; exact Td.tdK_SC.1) hr h

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(φ(ε₀, G+1)))` (CapV also `υ_λ < L(ω)`), (CL), EQ,
TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem hdGE_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG hdGE) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG hdGE) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG hdGE) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gv_road_of S _ (fun _ hr h => hdGE_enum S hr h) (fun _ hr h => hdGE_capV S hr h) hU hL hV hC hEQ hrest hB2

/-- **`Γ(φ(ε₀, G+1)) < Ω₂`.** -/
theorem hdGE_lt_Om2 : gcG hdGE < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG hdGE < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) (hdGE_lt1.trans hG1))
  exact h2.trans Tf.tfBG_lt_Om2

/-- **`P(Γ(φ(ε₀, G+1))) < L(0)`.** -/
theorem hdGE_P (S : InaccSeq.{0}) : Pv S (gcG hdGE) < Nc.ncL S 0 := ga_Pv_lt_L0 S hdGE_lt_Om2.le

/-- **The order of the frontiers**: `ι(Γ(φ(ω+1, G+1))·ω) ≤ ι(Γ(φ(ω+ν+1, G+1))·ω) ≤ ι(Γ(φ(ε₀, G+1))) ≤ ι(Ω₂)`
for every `ν < ε₀`, and `P(Γ(φ(ε₀, G+1))) ≤ P(Ω₂) < L(0)`. -/
theorem hdGE_fr_order (S : InaccSeq.{0}) {ν : Ordinal.{0}} (hν : ν < ε₀) :
    iota S (gcG hdNG * ω) ≤ iota S (gcG (veblen (ω + ν + 1) (gcG 0 + 1)) * ω) ∧
      iota S (gcG (veblen (ω + ν + 1) (gcG 0 + 1)) * ω) ≤ iota S (gcG hdGE) ∧
      iota S (gcG hdGE) ≤ iota S (Om (1 + 1)) ∧ Pv S (gcG hdGE) ≤ Pv S (Om (1 + 1)) ∧
      Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hV : InE (gcG hdGE) := Low.opow_eq_self_of_SC (gcG_SC _)
  have hl1 : ω + ν + 1 < ε₀ := by rw [← hd_lev_e]; exact (hd_lev (hc_eps0_lim.add_one_lt hν)).2
  have hle : hdNG ≤ veblen (ω + ν + 1) (gcG 0 + 1) := by
    unfold hdNG
    rcases (add_le_add_left (le_self_add : ω ≤ ω + ν) 1 : ω + 1 ≤ ω + ν + 1).lt_or_eq with h | h
    · exact (hd_veb_left_lt h _).le
    · rw [h]
  refine ⟨iota_mono _ _ (mul_le_mul_left (gcG_le hle) _), iota_mono _ _
    (InE.mul_lt hV (gcG_lt (hd_veb_left_lt hl1 _)) (omega0_lt_inE hV)).le,
    iota_mono _ _ hdGE_lt_Om2.le, Nm.Pv_mono hdGE_lt_Om2.le, ga_Pv_lt_L0 S le_rfl⟩

end Googology.Trans.PoR.InaccPsi.R2.Hd
