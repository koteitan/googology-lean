import Googology.Trans.PoR.InaccPsi.R2.HfCh

/-!
# HfMG: `G` AS A BASE OF EVERY COUNTABLE LEVEL WITH TWO GATES; EVERY `φ(α+1, G+1)`, `ω ≤ α < K`, IS LOCATED;
# THE FRONTIER `ι(Γ(φ(K, G+1)))`

`G = Γ_{Ω₁+1}` is a base of every countable level `α ≥ ω` (`hfGB α`) with the CODE GATE `0` (the code `G`) and the
READING GATE `α` (the readings `Γ_{x+1}`, `N_α(Γ_{x+1})` at bases `x > α`), outer low field `hfZg x = B_x(x)`.  So the
start condition `high0` of the offset recursion holds at `G` (it asks the code gate only), which `He.he_high0_fails`
shows impossible with one gate.

The systems `hfGL ν` (bound `N_{ω+ν}(G) = φ(ω+ν+1, G+1)`, base gate `≤ ω+ν`) are defined by one recursion on
`ν < Ω₁`: `hfGL 0 = Hd.hdGT`; `hfGL (ν+1)` is the union of all gated offsets over `G` at level `ω+ν+1` with the step
`Hf.hfLS (ν+1)`, started at `hfGL ν` with its base gate RAISED to the level (`He.heRegateG`); at a limit `λ` the
systems `hfGL λ_k` (`λ_k = He.heFs λ k`, gates `≤ ω+λ_k`) form an `ω`-chain with growing gates (`Hf.HfCh`) whose
union (gate `ω+λ`, bound `φ(ω+λ, G+1)`) starts the offset recursion over `G` at level `ω+λ` with the step `Hf.hfLS λ`.
The invariant (`hfGL_inv`): every `hfGL ν`, `ν < Ω₁`, has bound `N_{ω+ν}(G)`, gate `≤ ω+ν`, base reading
`N_{ω+ν}(Γ_{x+1})` and bound field `evZ` of it above `ω+ν`, `hfZg` below, and extends every `hfGL ν'`, `ν' ≤ ν`.

The location of a system needs its base gate below `K = ψ_{Ω₁}(Ω_ω)` (`Hc.hcV_locD`).  So every `φ(ω+ν+1, G+1)` with
`ν < K` is located (`hfGL_loc`), and BLK^O, the exact reaches, ENUM-REACH and CapV hold at every range restart below
`ι(Γ(φ(K, G+1)))` (`hfGE_enum`, `hfGE_capV`, `hfGE_blk`, `hfGE_road`), unconditionally.

* `hfZg`, `hf_G_fix`, `hf_NL_eq`, `hf_GL_lt1`, `hf_G_fixLx`, `hf_NL_glA`, `hf_GL_pi`, `hfGB` (**`G` AS A BASE OF EVERY
  COUNTABLE LEVEL, TWO GATES**), `hfG_start`;
* `HfGOK`, `HfGCoh`, `hfGLCh`, `hfGLCh_start`, `hfG_OK_start` (**THE START AT `G` OF THE NEXT LEVEL: THE GATE RAISED
  TO THE LEVEL**), `hfGLSucc`, `hfGLLim`, `hfGL`, `hfGL_inv` (**THE INVARIANT**), `hfGL_B`, `hfGL_γ`, `hfGL_loc`,
  `hfGL_blk`;
* `hfGE` (`φ(K, G+1)`), `hfGE_cofB`, `hfGE_cof`, `hfGE_enum`, `hfGE_capV`, `hfGE_blk`, `hfGE_road`, `hfGE_P`,
  `hfGE_fr_order`.

No new axiom.  New definitions: `hfZg`, `hfGB`, `HfGOK`, `HfGCoh`, `hfGLCh`, `hfGLSucc`, `hfGLLim`, `hfGL`, `hfGE`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hf

open Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
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

/-! ## `G` at every countable level -/

/-- **The outer low field at `G`**: `B_x(x) = φ(x, Γ_{x+1}+1)` (at an `ε`-number `x`). -/
noncomputable def hfZg (x : Ordinal.{0}) : Ordinal.{0} := veblen (max ω x) (lgG x + 1)

theorem hfZg_fix2 (x : Ordinal.{0}) : veblen 2 (hfZg x) = hfZg x :=
  veblen_veblen_of_lt (gw_two_lt_w.trans_le (le_max_left ω x)) _

theorem hfZg_fix1 (x : Ordinal.{0}) : veblen 1 (hfZg x) = hfZg x :=
  veblen_veblen_of_lt (one_lt_omega0.trans_le (le_max_left ω x)) _

theorem hfZg_eq {x : Ordinal.{0}} (hx : InE x) : hfZg x = hcBR x := by
  unfold hfZg hcBR; rw [max_eq_right (omega0_lt_inE hx).le]

/-- **`G` is a fixed point of every `φ(α, ·)`, `α` countable.** -/
theorem hf_G_fix {α : Ordinal.{0}} (h : α < Om1) : veblen α (gcG 0) = gcG 0 :=
  gn_veb_fix (gcG_SC 0) ((hf_om h).trans (gcG_Om1_lt 0))

/-- **`N_α(G) = φ(α+1, G+1)`**, `α` countable. -/
theorem hf_NL_eq {α : Ordinal.{0}} (h : α < Om1) : hcN α (gcG 0) = veblen (α + 1) (gcG 0 + 1) := by
  have := hcN_veb α (gcG 0); rwa [hf_G_fix (gl_Om1_lim.add_one_lt h)] at this

/-- **`φ(β, G+1) < Γ_{Ω₁+2}`**, `β` countable. -/
theorem hf_GL_lt1 {β : Ordinal.{0}} (h : β < Om1) : veblen β (gcG 0 + 1) < gcG 1 := by
  have hG1 := gcG_SC 1
  have hE := Low.opow_eq_self_of_SC hG1
  have hfix : veblen β (gcG 1) = gcG 1 := gn_veb_fix hG1 ((hf_om h).trans (gcG_Om1_lt 1))
  have h2 := (isNormal_veblen β).strictMono ((ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt zero_lt_one))
  rwa [hfix] at h2

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem hf_lt_Gx {α : Ordinal.{0}} (h : α < x) : α < lgG x := h.trans (lgG_facts hx hx1).2.1

theorem hf_G_fixLx {α : Ordinal.{0}} (h1 : 1 ≤ α) (h : α < x) : veblen α (lgG x) = lgG x :=
  hc_G_fix hx hx1 h1 (hf_lt_Gx hx hx1 h)

/-- **`N_α(Γ_{x+1}) = φ(α+1, Γ_{x+1}+1) = ϑˣ(Ω₁·(α+1) + Γ_{x+1})`** for `α + 1 < x`. -/
theorem hf_NL_glA {α : Ordinal.{0}} (h : α + 1 < x) :
    hcN α (lgG x) = veblen (α + 1) (lgG x + 1) ∧ hcN α (lgG x) = glA (α + 1) (lgG x) x := by
  have e : hcN α (lgG x) = veblen (α + 1) (lgG x + 1) := by
    have := hcN_veb α (lgG x); rwa [hf_G_fixLx hx hx1 le_add_self h] at this
  exact ⟨e, by rw [e, hc_glA_GG hx hx1 le_add_self (hf_lt_Gx hx hx1 h)]⟩

/-- **`φ(β, Γ_{x+1}+1) < B_x(x)`** for `β < x`. -/
theorem hf_veb_lt_BR {β : Ordinal.{0}} (h : β < x) : veblen β (lgG x + 1) < hcBR x := hd_veb_left_lt h _

/-- **`evZ(N_β(Γ_{x+1})) < hfZg x`** for `β < x`. -/
theorem hf_evN_lt_Zg {β : Ordinal.{0}} (h : β < x) : evZ (hcN β (lgG x)) < hfZg x := by
  have hl := ev_isSuccLimit_of_inE hx
  rw [(hf_NL_glA hx hx1 (hl.add_one_lt h)).1, hfZg_eq hx]
  exact hb_evZ_lt_fix2 (by rw [← hfZg_eq hx]; exact hfZg_fix2 x) (hf_veb_lt_BR hx hx1 (hl.add_one_lt h))

end Base

/-- **Lemma EXACT for `φ(β, Γ_{ρ+1}+1) = ϑᵖ(Ω₁·β + Γ_{ρ+1})`**, every level `1 ≤ β < σ`. -/
theorem hf_GL_pi {β σ ρ : Ordinal.{0}} (h1 : 1 ≤ β) (hβσ : β < σ) (hB : Bases σ ρ) :
    veblen β (lgG ρ + 1) ∈ TB ρ σ ∧ pi σ ρ (veblen β (lgG ρ + 1)) = veblen β (lgG σ + 1) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨g1, g2⟩ : lgG ρ ∈ TB ρ σ ∧ pi σ ρ (lgG ρ) = lgG σ := Go.goGl.ba_pi σ ρ hB
  have h := hfm_glA_pi hβσ hB g1 (mg_lgG_lt_G1 hB.2.1 hρ1)
  rw [g2, hc_glA_GG hB.2.1 hρ1 h1 (hf_lt_Gx hB.2.1 hρ1 (hβσ.trans hB.2.2.1)),
    hc_glA_GG hB.1 hσ1 h1 (hf_lt_Gx hB.1 hσ1 hβσ)] at h
  exact h

/-- **A code `φ(β, G+1)` over `Z` (`1 ≤ β < Ω₁`) has `β < Z`** (`He.he_cl_level`). -/
theorem hf_cl_GL {β : Ordinal.{0}} (h1 : 1 ≤ β) (hβ1 : β < Om1) {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1)
    (h : GxCl Z {gcG 0} (veblen β (gcG 0 + 1))) : β < Z :=
  he_cl_level h1 (hf_om hβ1) hZ hZ1 (hd_succ_lt (Order.one_le_iff_ne_zero.1 h1) _)
    ((lt_add_one _).trans_le (right_le_veblen β _)) h le_rfl ((isNormal_veblen β).strictMono (lt_add_one _))

/-- **`G` AS A BASE OF EVERY COUNTABLE LEVEL `α`, WITH TWO GATES**: code gate `0`, reading gate `α`, reading
`Γ_{x+1}`, outer low field `hfZg`. -/
noncomputable def hfGB (α : Ordinal.{0}) (hα : HfLvl α) : HfB α where
  F := gcG 0
  Fr := lgG
  γ := 0
  γN := α
  Zo := hfZg
  lv := hα
  γ_le := zero_le
  lvN := le_rfl
  γN_lt := hα.2
  F_fix := hf_G_fix hα.2
  G_le := le_rfl
  N_lt1 := by rw [hf_NL_eq hα.2]; exact hf_GL_lt1 hα.succ.2
  F_mem := fun S _ _ ha _ => gmS_G0_mem S ha
  N_mem := fun S _ _ ha hb => by
    rw [hf_NL_eq hα.2]
    exact CSet.phi_mem (CSet.succ_mem (he_cst_mem S le_rfl hb)) (CSet.succ_mem (gmS_G0_mem S ha))
  F_code := fun _ _ _ _ _ _ _ => GxCl.atom (Set.mem_singleton _)
  F_cl := fun _ hZ _ _ _ _ _ => hZ.1
  N_cl := fun _ hZ hZ1 h => by
    rw [hf_NL_eq hα.2] at h
    exact (lt_add_one α).trans (hf_cl_GL le_add_self hα.succ.2 hZ hZ1 h)
  γN_cl := fun _ _ _ _ h => h
  Fr_gt := fun hx hx1 _ => (lgG_facts hx hx1).2.1
  Fr_fix := fun hx hx1 h => hf_G_fixLx hx hx1 hα.one_le h
  N_Zo := fun {x} hx hx1 h => by
    have h1 : α + 1 < x := (ev_isSuccLimit_of_inE hx).add_one_lt h
    rw [(hf_NL_glA hx hx1 h1).1, hfZg_eq hx]; exact hf_veb_lt_BR hx hx1 h1
  Zo_fix := hfZg_fix2
  Zo_BR := fun _ hx _ => (hfZg_eq hx).le
  Fr_pi := fun {σ ρ} hB _ => Go.goGl.ba_pi σ ρ hB
  N_pi := fun {σ ρ} hB h => by
    have h1 : α + 1 < σ := (ev_isSuccLimit_of_inE hB.1).add_one_lt h
    rw [(hf_NL_glA hB.2.1 hB.2.2.2 (h1.trans hB.2.2.1)).1, (hf_NL_glA hB.1 (hB.2.2.1.trans hB.2.2.2) h1).1]
    exact hf_GL_pi le_add_self h1 hB

/-- **A system with bound `φ(α, G+1)`, base gate `α`, base reading `φ(α, Γ_{x+1}+1)` above `α` and bound field `evZ`
of it above `α`, `hfZg` below, STARTS THE OFFSET RECURSION OVER `G` AT LEVEL `α`.** -/
theorem hfG_start {α : Ordinal.{0}} (hα : HfLvl α) (T : HcVD) (hB : T.B = veblen α (gcG 0 + 1)) (hγ : T.γ = α)
    (hb : ∀ x, InE x → x < Om1 → α < x → T.b x = veblen α (lgG x + 1))
    (hZ : ∀ x, InE x → x < Om1 → T.Z x = if α < x then evZ (veblen α (lgG x + 1)) else hfZg x) :
    HfMStart (hfGB α hα) T where
  B := by rw [add_zero]; exact hB
  Zb := fun x hx hx1 => by
    rw [hZ x hx hx1]
    show (if α < x then evZ (veblen α (lgG x + 1)) else hfZg x) ≤ if α < x then hcN α (lgG x) else hfZg x
    split_ifs
    · exact (hb_evZ_lt_fix2 (hc_fix_down hα.two_lt.le (hcN_fix α _)) hc_next_lt_N).le
    · exact le_rfl
  st := fun h2 hZ' => {
    ix := by
      show T.ix = veblen α (gcG 0 + 1 + 0)
      rw [add_zero]; exact hc_ix_of_B (veblen_veblen_of_lt hα.one_lt _) hB
    γ := fun x _ _ => by
      show T.γ < x ↔ max α (T.g 0) < x
      rw [hγ, T.g_zero, max_eq_left zero_le]
    b := fun x hx hx1 h => by
      have h' : α < x := by
        have : max α (T.g 0) < x := h
        rwa [T.g_zero, max_eq_left zero_le] at this
      show T.b x = glA α (lgG x + T.R 0 x) x
      rw [T.R_zero, add_zero, hb x hx hx1 h', hc_glA_GG hx hx1 hα.one_le (hf_lt_Gx hx hx1 h')]
    Z := fun x hx hx1 => by
      unfold HcPB.Zst
      show T.Z x = if max α (T.g 0) < x then evZ (glA α (lgG x + T.R 0 x) x) else (hfGB α hα).Zl x
      rw [T.g_zero, max_eq_left zero_le, T.R_zero, add_zero, hZ x hx hx1]
      by_cases h : α < x
      · rw [if_pos h, if_pos h, hc_glA_GG hx hx1 hα.one_le (hf_lt_Gx hx hx1 h)]
      · rw [if_neg h, if_neg h, (hfGB α hα).Zl_low h]; rfl }
  high0 := fun _ _ _ _ hσ _ _ => hσ.pos

/-! ## The recursion on the level -/

/-- **The shape of the system at level `ω + ν`**: bound `N_{ω+ν}(G)`, gate `≤ ω+ν`, base reading `N_{ω+ν}(Γ_{x+1})`
above `ω+ν`, bound field `evZ` of it above `ω+ν` and `hfZg` below. -/
def HfGOK (ν : Ordinal.{0}) (T : HcVD) : Prop :=
  T.B = hcN (ω + ν) (gcG 0) ∧ T.γ ≤ ω + ν ∧ (∀ x, InE x → x < Om1 → ω + ν < x → T.b x = hcN (ω + ν) (lgG x)) ∧
    ∀ x, InE x → x < Om1 → T.Z x = if ω + ν < x then evZ (hcN (ω + ν) (lgG x)) else hfZg x

/-- **The condition at a limit**: every earlier system has the shape, and later systems extend earlier ones. -/
def HfGCoh (l : Ordinal.{0}) (IH : ∀ ν, ν < l → HcVD) : Prop :=
  (∀ ν (h : ν < l), HfGOK ν (IH ν h)) ∧ ∀ ν ν' (h : ν < l) (h' : ν' < l), ν ≤ ν' → ∀ c x, c < (IH ν h).B →
    (IH ν' h').R c x = (IH ν h).R c x ∧ (IH ν' h').g c = (IH ν h).g c

theorem hfGL_kle {l : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l < Om1) (k : ℕ) : ω + heFs l k ≤ ω + l :=
  (add_le_add_iff_left ω).2 (heFs_lt hl (hf_om hle) k).le

section LimCh

variable (l : Ordinal.{0}) (hl : IsSuccLimit l) (hle : l < Om1) (IH : ∀ ν, ν < l → HcVD) (H : HfGCoh l IH)

include hle in
theorem hfGL_NxG : hdNx (ω + l) (gcG 0) = veblen (ω + l) (gcG 0 + 1) := hdNx_fixP (hf_G_fix (hf_lev hle).2)

include hle in
theorem hfGL_Nxx {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (h : ω + l < x) :
    hdNx (ω + l) (lgG x) = veblen (ω + l) (lgG x + 1) :=
  hdNx_fixP (hf_G_fixLx hx hx1 (hf_lev hle).one_le h)

include H in
/-- **THE CHAIN AT A LIMIT LEVEL**: the systems at the levels `ω + λ_k` (gates `≤ ω + λ_k`); union bound
`φ(ω+λ, G+1)`, union gate `ω + λ`. -/
noncomputable def hfGLCh : HfCh where
  D := fun k => IH (heFs l k) (heFs_lt hl (hf_om hle) k)
  B := hdNx (ω + l) (gcG 0)
  b := fun x => hdNx (ω + l) (lgG x)
  γ := ω + l
  Zo := hfZg
  γ_lt := (hf_lev hle).2
  γ0 := fun k => (H.1 _ _).2.1.trans (hfGL_kle hl hle k)
  γ_cl := fun _ hZ hZ1 h => by
    rw [hfGL_NxG l hle] at h
    exact hf_cl_GL (hf_lev hle).one_le (hf_lev hle).2 hZ hZ1 h
  B_mono := fun k => by
    rw [(H.1 _ _).1, (H.1 _ _).1]; exact hcN_mono ((hfLmOf l hl hle).mono k) _
  B_lt := fun k => by
    rw [(H.1 _ _).1]; exact hdN_lt_Nx ((hfLmOf l hl hle).lim.add_one_lt ((hfLmOf l hl hle).lt k))
  B_cof := fun c hc => by
    obtain ⟨k, hk⟩ := hdNx_cof (hfLmOf l hl hle).lim (hfLmOf l hl hle).lt (hfLmOf l hl hle).mono
      (hfLmOf l hl hle).cof hc
    exact ⟨k, by rw [(H.1 _ _).1]; exact hk⟩
  R_ext := fun k c x hc => (H.2 _ _ _ _ (heFs_mono hl (hf_om hle) k).le c x hc).1
  g_ext := fun k c hc => (H.2 _ _ _ _ (heFs_mono hl (hf_om hle) k).le c 0 hc).2
  B_lt1 := by rw [hfGL_NxG l hle]; exact hf_GL_lt1 (hf_lev hle).2
  B_fix := hdNx_fix (hf_lev hle).one_lt _
  B_mem := fun S _ _ ha hb => by
    rw [hfGL_NxG l hle]
    exact CSet.phi_mem (he_cst_mem S le_rfl hb) (CSet.succ_mem (gmS_G0_mem S ha))
  b_ge := fun k x hx hx1 hγ => by
    rw [(H.1 _ _).2.2.1 x hx hx1 ((hfGL_kle hl hle k).trans_lt hγ)]
    exact (hdN_lt_Nx ((hfLmOf l hl hle).lim.add_one_lt ((hfLmOf l hl hle).lt k))).le
  b_cof := fun x hx hx1 hγ μ hμ => by
    obtain ⟨k, hk⟩ := hdNx_cof (hfLmOf l hl hle).lim (hfLmOf l hl hle).lt (hfLmOf l hl hle).mono
      (hfLmOf l hl hle).cof hμ
    exact ⟨k, by rw [(H.1 _ _).2.2.1 x hx hx1 ((hfGL_kle hl hle k).trans_lt hγ)]; exact hk⟩
  b_fix := fun x _ _ _ => hdNx_fix (hf_lev hle).one_lt _
  b_gt := fun x hx hx1 _ => (lgG_facts hx hx1).2.1.trans (hdNx_gt _ _)
  b_lt := fun x hx hx1 hγ => by rw [hfGL_Nxx l hle hx hx1 hγ]; exact hf_veb_lt_BR hx hx1 hγ
  b_pi := fun σ ρ hB hγ => by
    rw [hfGL_Nxx l hle hB.2.1 hB.2.2.2 (hγ.trans hB.2.2.1), hfGL_Nxx l hle hB.1 (hB.2.2.1.trans hB.2.2.2) hγ]
    exact hf_GL_pi (hf_lev hle).one_le hγ hB
  Z_low := fun k x hx hx1 hγ => by
    rw [(H.1 _ _).2.2.2 x hx hx1]
    split_ifs with h
    · exact (hf_evN_lt_Zg hx hx1 h).le
    · exact le_rfl
  Zo_fix := hfZg_fix1
  Zo_BR := fun _ hx _ => (hfZg_eq hx).le

theorem hfGLCh_start : HfMStart (hfGB (ω + l) (hf_lev hle)) (hfGLCh l hl hle IH H).U :=
  hfG_start (hf_lev hle) _ (hfGL_NxG l hle) rfl (fun x hx hx1 h => hfGL_Nxx l hle hx hx1 h)
    (fun x hx hx1 => by
      show (if ω + l < x then evZ (hdNx (ω + l) (lgG x)) else hfZg x) = _
      by_cases h : ω + l < x
      · rw [if_pos h, if_pos h, hfGL_Nxx l hle hx hx1 h]
      · rw [if_neg h, if_neg h])

end LimCh

/-- **THE START AT `G` OF THE NEXT LEVEL**: a system of the shape at level `ω + ν`, with its base gate RAISED to the
level `ω + ν + 1` (`He.heRegateG`), starts the offset recursion over `G` at level `ω + (ν + 1)`. -/
theorem hfG_OK_start {ν : Ordinal.{0}} (hν : ν + 1 < Om1) {T : HcVD} (h : HfGOK ν T) :
    ∃ (hB : T.B = veblen (ω + (ν + 1)) (gcG 0 + 1)) (hγ : T.γ ≤ ω + (ν + 1)),
      HfMStart (hfGB (ω + (ν + 1)) (hf_lev hν))
        (heRegateG T (hf_lev hν).one_le (hf_lev hν).2 hB hγ) := by
  have hl1 : ω + ν < Om1 := (hf_lev ((lt_add_one ν).trans hν)).2
  have hB : T.B = veblen (ω + (ν + 1)) (gcG 0 + 1) := by rw [h.1, hf_NL_eq hl1, hf_lev_e]
  have hγ : T.γ ≤ ω + (ν + 1) := h.2.1.trans (by rw [hf_lev_e]; exact le_self_add)
  refine ⟨hB, hγ, hfG_start (hf_lev hν) _ hB (heRegateG_γ T _ _ hB hγ) (fun x hx hx1 hx' => ?_)
    (fun x hx hx1 => ?_)⟩
  · have hx'' : ω + ν < x := (lt_add_one _).trans (by rw [← hf_lev_e]; exact hx')
    show T.b x = _
    rw [h.2.2.1 x hx hx1 hx'', (hf_NL_glA hx hx1 (by rw [← hf_lev_e]; exact hx')).1, hf_lev_e]
  · show T.Z x = _
    rw [h.2.2.2 x hx hx1]
    have hiff : ω + ν < x ↔ ω + (ν + 1) < x := by
      rw [hf_lev_e]
      exact ⟨fun h' => (ev_isSuccLimit_of_inE hx).add_one_lt h', fun h' => (lt_add_one _).trans h'⟩
    by_cases h' : ω + ν < x
    · rw [if_pos h', if_pos (hiff.1 h'), (hf_NL_glA hx hx1 (by rw [← hf_lev_e]; exact hiff.1 h')).1, hf_lev_e]
    · rw [if_neg h', if_neg (fun h'' => h' (hiff.2 h''))]

open Classical in
/-- **The successor case**: the union of all gated offsets over `G` at level `ω + ν + 1`, started at `T` with its
gate raised to the level. -/
noncomputable def hfGLSucc (ν : Ordinal.{0}) (T : HcVD) : HcVD :=
  if H : ∃ hν : ν + 1 < Om1, HfGOK ν T then
    hfMTU (St := hfLS (ν + 1)) (fun Q U h => hfLS_spec H.choose Q U h)
      (hfG_OK_start H.choose H.choose_spec).choose_spec.choose_spec
  else T

open Classical in
/-- **The limit case**: the union of the chain (gate raised to `ω + λ`), then all gated offsets over `G` at level
`ω + λ`. -/
noncomputable def hfGLLim (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ ν, ν < l → HcVD) : HcVD :=
  if H : ∃ hle : l < Om1, HfGCoh l IH then
    hfMTU (St := hfLS l) (fun Q U h => hfLS_spec H.choose Q U h)
      (hfGLCh_start l hl H.choose IH H.choose_spec)
  else hcWU

/-- **THE SYSTEM AT `φ(ω+ν+1, G+1)`, BY ONE RECURSION ON THE LEVEL `ν < Ω₁`.** -/
noncomputable def hfGL (ν : Ordinal.{0}) : HcVD :=
  Ordinal.limitRecOn (motive := fun _ => HcVD) ν hdGT hfGLSucc hfGLLim

theorem hfGL_zero : hfGL 0 = hdGT := by unfold hfGL; rw [Ordinal.limitRecOn_zero]

theorem hfGL_succ (ν : Ordinal.{0}) : hfGL (ν + 1) = hfGLSucc ν (hfGL ν) := by
  unfold hfGL; rw [Ordinal.limitRecOn_add_one]

theorem hfGL_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : hfGL l = hfGLLim l hl (fun ν _ => hfGL ν) := by
  unfold hfGL; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem hfGT_OK : HfGOK 0 hdGT := by
  obtain ⟨h1, h2, h3, h4⟩ := hdGT_OK
  refine ⟨h1, by rw [h2]; exact zero_le, fun x hx hx1 _ => h3 x hx hx1, fun x hx hx1 => ?_⟩
  rw [h4 x hx hx1, if_pos (by rw [add_zero]; exact omega0_lt_inE hx)]

/-- **The union over `G` at level `ω + ν` has the shape at the level `ω + ν`.** -/
theorem hfG_TU_OK {ν : Ordinal.{0}} (hν : ν < Om1) {S0 : HcVD} (hS : HfMStart (hfGB (ω + ν) (hf_lev hν)) S0) :
    HfGOK ν (hfMTU (St := hfLS ν) (fun Q U h => hfLS_spec hν Q U h) hS) :=
  ⟨rfl, le_rfl, fun _ _ _ _ => rfl, fun x _ _ => rfl⟩

/-- **THE INVARIANT**: every `hfGL ν`, `ν < Ω₁`, has the shape at level `ω + ν` and extends every `hfGL ν'`,
`ν' ≤ ν`. -/
theorem hfGL_inv : ∀ ν, ν < Om1 → HfGOK ν (hfGL ν) ∧ ∀ ν', ν' ≤ ν → ∀ c x, c < (hfGL ν').B →
    (hfGL ν).R c x = (hfGL ν').R c x ∧ (hfGL ν).g c = (hfGL ν').g c := by
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hν
  rcases zero_or_succ_or_isSuccLimit ν with h0 | ⟨μ, hμ⟩ | hlim
  · subst h0
    rw [hfGL_zero]
    refine ⟨hfGT_OK, fun ν' hν' c x _ => ?_⟩
    rw [nonpos_iff_eq_zero.1 hν', hfGL_zero]; exact ⟨rfl, rfl⟩
  · have hμ' : ν = μ + 1 := by rw [← hμ, succ_eq_add_one]
    subst hμ'
    have hμε : μ < Om1 := (lt_add_one μ).trans hν
    obtain ⟨hok, hext⟩ := IH μ (lt_add_one μ) hμε
    have hH : ∃ hν' : μ + 1 < Om1, HfGOK μ (hfGL μ) := ⟨hν, hok⟩
    set hS := (hfG_OK_start hH.choose hH.choose_spec).choose_spec.choose_spec with hhS
    have e : hfGL (μ + 1) = hfMTU (St := hfLS (μ + 1)) (fun Q U h => hfLS_spec hH.choose Q U h) hS := by
      rw [hfGL_succ]; unfold hfGLSucc; rw [dif_pos hH]
    rw [e]
    refine ⟨hfG_TU_OK hH.choose hS, fun ν' hν' c x hc => ?_⟩
    rcases hν'.lt_or_eq with hlt | heq
    · have hle : ν' ≤ μ := Order.lt_add_one_iff.1 hlt
      have hcμ : c < (hfGL μ).B := by
        rw [hok.1]; rw [(IH ν' (lt_of_le_of_lt hle (lt_add_one μ)) (hle.trans_lt hμε)).1.1] at hc
        exact hc.trans_le (hcN_mono ((add_le_add_iff_left ω).2 hle) _)
      obtain ⟨r2, g2⟩ := hext ν' hle c x hc
      exact ⟨(hfMTU_R0 _ hS hcμ x).trans r2, (hfMTU_g0 _ hS hcμ).trans g2⟩
    · subst heq; rw [e]; exact ⟨rfl, rfl⟩
  · have hcoh : HfGCoh ν (fun ν' _ => hfGL ν') :=
      ⟨fun ν' h => (IH ν' h (h.trans hν)).1, fun ν₁ ν₂ h₁ h₂ h12 c x hc =>
        (IH ν₂ h₂ (h₂.trans hν)).2 ν₁ h12 c x hc⟩
    have hS := hfGLCh_start ν hlim hν (fun ν' _ => hfGL ν') hcoh
    have e : hfGL ν = hfMTU (St := hfLS ν) (fun Q U h => hfLS_spec hν Q U h) hS := by
      rw [hfGL_limit hlim]; unfold hfGLLim; rw [dif_pos ⟨hν, hcoh⟩]
    rw [e]
    refine ⟨hfG_TU_OK hν hS, fun ν' hν' c x hc => ?_⟩
    rcases hν'.lt_or_eq with hlt | heq
    · obtain ⟨k, hk⟩ := heFs_cof hlim (hf_om hν) ν' hlt
      have hkl := heFs_lt hlim (hf_om hν) k
      obtain ⟨hokk, hextk⟩ := IH _ hkl (hkl.trans hν)
      have hck : c < (hfGL (heFs ν k)).B := by
        rw [hokk.1]; rw [(IH ν' hlt (hlt.trans hν)).1.1] at hc
        exact hc.trans_le (hcN_mono ((add_le_add_iff_left ω).2 hk.le) _)
      set C := hfGLCh ν hlim hν (fun ν' _ => hfGL ν') hcoh with hC
      have hcC : c < C.U.B := hck.trans (C.B_lt k)
      obtain ⟨r2, g2⟩ := hextk ν' hk.le c x hc
      refine ⟨(hfMTU_R0 _ hS hcC x).trans ((C.U_R (k := k) hck x).trans r2),
        (hfMTU_g0 _ hS hcC).trans ((C.U_g (k := k) hck).trans g2)⟩
    · subst heq; rw [e]; exact ⟨rfl, rfl⟩

theorem hfGL_B {ν : Ordinal.{0}} (hν : ν < Om1) : (hfGL ν).B = veblen (ω + ν + 1) (gcG 0 + 1) := by
  rw [(hfGL_inv ν hν).1.1, hf_NL_eq (hf_lev hν).2]

theorem hfGL_γ {ν : Ordinal.{0}} (hν : ν < Om1) : (hfGL ν).γ ≤ ω + ν := (hfGL_inv ν hν).1.2.1

/-! ## Location below `K = ψ_{Ω₁}(Ω_ω)` -/

theorem hf_K_lt (S : InaccSeq.{0}) : Td.tdK S < Om1 := by rw [Br.Om1_eq]; exact Td.tdK_lt_Om1

theorem hf_lev_K (S : InaccSeq.{0}) {ν : Ordinal.{0}} (hν : ν < Td.tdK S) : ω + ν < Td.tdK S :=
  (Td.tdK_SC (S := S)).isPrincipal (omega0_lt_inE (Low.opow_eq_self_of_SC Td.tdK_SC)) hν

theorem hfGL_γK (S : InaccSeq.{0}) {ν : Ordinal.{0}} (hν : ν < Td.tdK S) : (hfGL ν).γ < Td.tdK S :=
  (hfGL_γ (hν.trans (hf_K_lt S))).trans_lt (hf_lev_K S hν)

/-- **EVERY `φ(ω+ν+1, G+1)`, `ν < K`, IS LOCATED**: `Λ⁺ = ι(Γ(φ(ω+ν+1, G+1))·ω)`, `P(…) < L(0)`. -/
theorem hfGL_loc (S : InaccSeq.{0}) {ν : Ordinal.{0}} (hν : ν < Td.tdK S) :
    ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG (veblen (ω + ν + 1) (gcG 0 + 1)) * ω) ∧
      upsilon (xtB1 X) = Pv S (gcG (veblen (ω + ν + 1) (gcG 0 + 1)) * ω) ∧
      Pv S (gcG (veblen (ω + ν + 1) (gcG 0 + 1)) * ω) < Nc.ncL S 0 := by
  rw [← hfGL_B (hν.trans (hf_K_lt S))]; exact hcV_locD (hfGL ν) S (hfGL_γK S hν)

/-- **Theorem BLK^O below `P(Γ(φ(ω+ν+1, G+1))·ω)`, with the exact reaches**, every `ν < K` (UNCONDITIONAL). -/
theorem hfGL_blk (S : InaccSeq.{0}) {ν : Ordinal.{0}} (hν : ν < Td.tdK S) :
    let X := gsX (hfGL ν).step.toRS _ (hfGL ν).E_lt_B.le (hfGL ν).B_lt_NB S (hcV_locD_g (hfGL ν) S (hfGL_γK S hν))
    (∀ c' d, c' < d → d < upsilon (xtB1 X) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 X ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧ d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 X →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec X l)) ∧
    (∀ α < upsilon (xtB1 X), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  hcV_locD_blk (hfGL ν) S (hfGL_γK S hν)

theorem hfK_lim (S : InaccSeq.{0}) : IsSuccLimit (Td.tdK S) :=
  ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC Td.tdK_SC)

/-- **The base gate of `hfGL ν` is EXACTLY the level `ω + ν`** for `0 < ν < Ω₁`. -/
theorem hfGL_γ_eq {ν : Ordinal.{0}} (hν : ν < Om1) (h0 : ν ≠ 0) : (hfGL ν).γ = ω + ν := by
  rcases zero_or_succ_or_isSuccLimit ν with h | ⟨μ, hμ⟩ | hlim
  · exact absurd h h0
  · have hμ' : ν = μ + 1 := by rw [← hμ, succ_eq_add_one]
    subst hμ'
    have hH : ∃ hν' : μ + 1 < Om1, HfGOK μ (hfGL μ) := ⟨hν, (hfGL_inv μ ((lt_add_one μ).trans hν)).1⟩
    rw [hfGL_succ]; unfold hfGLSucc; rw [dif_pos hH]; rfl
  · have hcoh : HfGCoh ν (fun ν' _ => hfGL ν') :=
      ⟨fun ν' h => (hfGL_inv ν' (h.trans hν)).1, fun ν₁ ν₂ h₁ h₂ h12 c x hc =>
        (hfGL_inv ν₂ (h₂.trans hν)).2 ν₁ h12 c x hc⟩
    rw [hfGL_limit hlim]; unfold hfGLLim; rw [dif_pos ⟨hν, hcoh⟩]; rfl

/-- **THE WALL AT THE LEVEL `K`**: the system `hfGL K` exists (bound `φ(K+1, G+1)`, every Lemma of the recursion
holds), but its base gate is `K` itself, so the location theorem `Hc.hcV_locD` (base gate `< K`, the only lower bound
`Td.tdK_le_rho` of the restarts) does not apply. -/
theorem hfGL_wall (S : InaccSeq.{0}) :
    (hfGL (Td.tdK S)).B = veblen (Td.tdK S + 1) (gcG 0 + 1) ∧ (hfGL (Td.tdK S)).γ = Td.tdK S ∧
      ¬ (hfGL (Td.tdK S)).γ < Td.tdK S := by
  have hK1 : Td.tdK S < Om1 := hf_K_lt S
  have hωK : ω + Td.tdK S = Td.tdK S :=
    isPrincipal_add_iff_add_left_eq_self.1 (Td.tdK_SC (S := S)).isPrincipal ω
      (omega0_lt_inE (Low.opow_eq_self_of_SC Td.tdK_SC))
  have hγ := hfGL_γ_eq hK1 (hfK_lim S).bot_lt.ne'
  rw [hωK] at hγ
  refine ⟨by rw [hfGL_B hK1, hωK], hγ, by rw [hγ]; exact lt_irrefl _⟩

/-! ## The frontier `ι(Γ(φ(K, G+1)))` -/

/-- **`φ(K, G+1)`**, `K = ψ_{Ω₁}(Ω_ω)`. -/
noncomputable def hfGE (S : InaccSeq.{0}) : Ordinal.{0} := veblen (Td.tdK S) (gcG 0 + 1)

theorem hfGE_eq (S : InaccSeq.{0}) : hfGE S = hdNx (Td.tdK S) (gcG 0) :=
  (hdNx_fixP (hf_G_fix (hf_K_lt S))).symm

/-- **Every ordinal below `φ(K, G+1)` lies below some `φ(ω+ν+1, G+1)`, `ν < K`.** -/
theorem hfGE_cofB (S : InaccSeq.{0}) {β : Ordinal.{0}} (hβ : β < hfGE S) :
    ∃ ν, ν < Td.tdK S ∧ β < (hfGL ν).B := by
  rw [hfGE_eq] at hβ
  have hK := hfK_lim S
  have hK1 := hf_om (hf_K_lt S)
  obtain ⟨k, hk⟩ := hdNx_cof hK (heFs_lt hK hK1) (fun k => (heFs_mono hK hK1 k).le) (heFs_cof hK hK1) hβ
  have hν := heFs_lt hK hK1 k
  refine ⟨_, hν, ?_⟩
  rw [(hfGL_inv _ (hν.trans (hf_K_lt S))).1.1]
  exact hk.trans_le (hcN_mono le_add_self _)

theorem hfGE_lt1 (S : InaccSeq.{0}) : hfGE S < gcG 1 := hf_GL_lt1 (hf_K_lt S)

theorem hfGE_lim (S : InaccSeq.{0}) : IsSuccLimit (hfGE S) :=
  ev_isSuccLimit_of_inE (gg_veblen_eps (hfK_lim S).bot_lt.ne')

/-- **The located bounds `ι(Γ(φ(ω+ν+1, G+1))·ω)`, `ν < K`, are cofinal below `ι(Γ(φ(K, G+1)))`.** -/
theorem hfGE_cof (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : l < iota S (gcG (hfGE S))) :
    ∃ ν, ν < Td.tdK S ∧ l < iota S (gcG (hfGL ν).B * ω) := by
  have hlim : IsSuccLimit (gcG (hfGE S)) := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (gcG_SC _))
  rw [iota_limit hlim] at hl
  haveI : Nonempty (Iio (gcG (hfGE S))) := ⟨⟨0, hlim.bot_lt⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hl
  obtain ⟨β, hβ, heβ⟩ := gcG_lt_of_lt_limit (hfGE_lim S) e.2
  obtain ⟨ν, hν, hβν⟩ := hfGE_cofB S hβ
  refine ⟨ν, hν, he.trans_le (iota_mono _ _ ((heβ.trans (gcG_lt hβν)).trans_le ?_).le)⟩
  exact le_mul_of_one_le_right' one_lt_omega0.le

/-- **ENUM-REACH at every range restart below `ι(Γ(φ(K, G+1)))`, fixed points included** (UNCONDITIONAL). -/
theorem hfGE_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (hfGE S))) :
    CdUpper S l ∧ CdLower S l := by
  obtain ⟨ν, hν, h⟩ := hfGE_cof S hl
  exact hcV_locD_enum (hfGL ν) S (hfGL_γK S hν) hr h

/-- **CapV at every range restart below `ι(Γ(φ(K, G+1)))`** (UNCONDITIONAL). -/
theorem hfGE_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (hfGE S))) :
    CdCapV S l := by
  obtain ⟨ν, hν, h⟩ := hfGE_cof S hl
  exact hcV_locD_capV (hfGL ν) S (hfGL_γK S hν) hr h

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(φ(K, G+1)))` (CapV also `υ_λ < L(ω)`), (CL), EQ,
TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem hfGE_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG (hfGE S)) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG (hfGE S)) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG (hfGE S)) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gv_road_of S _ (fun _ hr h => hfGE_enum S hr h) (fun _ hr h => hfGE_capV S hr h) hU hL hV hC hEQ hrest hB2

/-- **`Γ(φ(K, G+1)) < Ω₂`.** -/
theorem hfGE_lt_Om2 (S : InaccSeq.{0}) : gcG (hfGE S) < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG (hfGE S) < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) ((hfGE_lt1 S).trans hG1))
  exact h2.trans Tf.tfBG_lt_Om2

/-- **`P(Γ(φ(K, G+1))) < L(0)`.** -/
theorem hfGE_P (S : InaccSeq.{0}) : Pv S (gcG (hfGE S)) < Nc.ncL S 0 := ga_Pv_lt_L0 S (hfGE_lt_Om2 S).le

/-- **The order of the frontiers**: `ι(Γ(φ(ε₀, G+1))) ≤ ι(Γ(φ(ω+ν+1, G+1))·ω) ≤ ι(Γ(φ(K, G+1))) ≤ ι(Ω₂)` for every
`ε₀ ≤ ω+ν`, `ν < K`, and `P(Γ(φ(K, G+1))) ≤ P(Ω₂) < L(0)`. -/
theorem hfGE_fr_order (S : InaccSeq.{0}) {ν : Ordinal.{0}} (hν : ν < Td.tdK S) (hε : ε₀ ≤ ω + ν) :
    iota S (gcG hdGE) ≤ iota S (gcG (veblen (ω + ν + 1) (gcG 0 + 1)) * ω) ∧
      iota S (gcG (veblen (ω + ν + 1) (gcG 0 + 1)) * ω) ≤ iota S (gcG (hfGE S)) ∧
      iota S (gcG (hfGE S)) ≤ iota S (Om (1 + 1)) ∧ Pv S (gcG (hfGE S)) ≤ Pv S (Om (1 + 1)) ∧
      Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hV : InE (gcG (hfGE S)) := Low.opow_eq_self_of_SC (gcG_SC _)
  have hl1 : ω + ν + 1 < Td.tdK S := (hfK_lim S).add_one_lt (hf_lev_K S hν)
  have hle : hdGE ≤ veblen (ω + ν + 1) (gcG 0 + 1) :=
    (hd_veb_left_lt (hε.trans_lt (lt_add_one _)) _).le
  refine ⟨(iota_mono _ _ (gcG_le hle)).trans (iota_mono _ _ (le_mul_of_one_le_right' one_lt_omega0.le)),
    iota_mono _ _ (InE.mul_lt hV (gcG_lt (hd_veb_left_lt hl1 _)) (omega0_lt_inE hV)).le,
    iota_mono _ _ (hfGE_lt_Om2 S).le, Nm.Pv_mono (hfGE_lt_Om2 S).le, ga_Pv_lt_L0 S le_rfl⟩

end Googology.Trans.PoR.InaccPsi.R2.Hf
