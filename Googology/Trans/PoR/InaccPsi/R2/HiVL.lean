import Googology.Trans.PoR.InaccPsi.R2.HiVSc

/-!
# HiVL: THE STEP OF EVERY LEVEL `Ω₁ + ν` (`ν < Ω₁`), BY ONE RECURSION ON THE LEVEL

The port of `Hg.HgfMRecL` to the levels `Ω₁ + ν` read as `x + ν`.  The level `Ω₁ + 0`: a pseudo-base of level `Ω₁`
is a gated abstract base (`HiVQ.toQB : Hi.HiQB`) and its step is the union over all countable levels over it
(`Hi.hiQU`, `hiv0_spec`).  The successor `Ω₁ + ν + 1`: one more offset recursion (`Hi.hiVScT`); the limit `Ω₁ + λ`:
the chain of the steps of the levels `Ω₁ + λ_k`, `λ_k = He.heFs λ k` (`Hi.hiVLmT`).  `hiVLS ν` is defined by
`Ordinal.limitRecOn`; `hiVLS_inv`: every `hiVLS ν`, `ν < Ω₁`, has the specification `Hi.HiVSpec` and extends every
`hiVLS ν'`, `ν' < ν`, at the same pseudo-base.

* `HiVQ.toQB`, `hiVLS0`, `hiv0_spec`, `HiVStTy`, `hiVLSucc`, `hiVLmOf`, `HiVLCoh`, `hiVLmSt`, `hiVLLim`, `hiVLS` (**THE
  STEP OF EVERY LEVEL `Ω₁ + ν`**), `HiVLExt`, `hiVLS_inv` (**THE INVARIANT**), `hiVLS_spec`.

No new axiom.  New definitions: `HiVQ.toQB`, `HiVStTy`, `hiVLS0`, `hiVLSucc`, `hiVLmOf`, `HiVLCoh`, `hiVLmSt`,
`hiVLLim`, `hiVLS`, `HiVLExt`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hi

open Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The level `Ω₁ + 0` -/

namespace HiVQ

variable (Q : HiVQ 0)

theorem fix0 {α : Ordinal.{0}} (hα : α < Om1) : veblen α Q.F = Q.F := by
  obtain ⟨a, ha⟩ := Q.F_P; rw [← ha]; exact veblen_veblen_of_lt (by rw [add_zero]; exact hα) a

theorem rfix0 {α x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : Q.γ < x) (hα : α < x) :
    veblen α (Q.Fr x) = Q.Fr x := by
  obtain ⟨a, ha⟩ := Q.Fr_P hx hx1 hγ; rw [← ha]; exact veblen_veblen_of_lt (by rw [add_zero]; exact hα) a

theorem NQ_lt_S {α : Ordinal.{0}} (hα : α < Om1) : hcN α Q.F < hdNx (Om1 + 0) Q.F := by
  rw [add_zero]; exact hdN_lt_Nx (gl_Om1_lim.add_one_lt hα)

theorem NQ_eq {α : Ordinal.{0}} (hα : α < Om1) : hcN α Q.F = veblen (α + 1) (Q.F + 1) := by
  have := hcN_veb α Q.F; rwa [Q.fix0 (gl_Om1_lim.add_one_lt hα)] at this

theorem NP_glA0 {α x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : Q.γ < x) (h : α + 1 < x) :
    hcN α (Q.Fr x) = glA (α + 1) (Q.Fr x) x := by
  have hfix : veblen (α + 1) (Q.Fr x) = Q.Fr x := Q.rfix0 hx hx1 hγ h
  have e : hcN α (Q.Fr x) = veblen (α + 1) (Q.Fr x + 1) := by
    have := hcN_veb α (Q.Fr x); rwa [hfix] at this
  rw [e, hc_glA_fixG hx hx1 le_add_self (h.trans (gm1_facts hx hx1).2.1) hfix
    (h.trans (Q.Fr_gtx hx hx1 hγ)) (Q.Fr_gtx hx hx1 hγ) (Q.Fr_lt1 hx hx1 hγ)]

/-- **A PSEUDO-BASE OF LEVEL `Ω₁ + 0` IS A GATED ABSTRACT BASE** (`Hi.HiQB`). -/
noncomputable def toQB : HiQB where
  Q := Q.F
  P := Q.Fr
  γ := Q.γ
  Zo := Q.Zo
  γ_lt := Q.γ_lt
  Q_fix := fun α hα => Q.fix0 hα
  G_lt := Q.G_lt
  Q_lt1 := (hdNx_gt _ _).trans Q.S_lt1
  N_lt1 := fun α hα => (Q.NQ_lt_S hα).trans Q.S_lt1
  Q_mem := fun S _ _ ha hb => Q.F_mem S ha hb
  N_mem := fun α hα S _ _ ha hb => by
    rw [Q.NQ_eq hα]
    exact CSet.phi_mem (CSet.succ_mem (he_cst_mem S le_rfl (max_lt_iff.1 hb).2))
      (CSet.succ_mem (Q.F_mem S ha (max_lt_iff.1 hb).1))
  Q_code := fun α hα Z hZ hZ1 y hy hQy hyN => Q.F_code Z hZ hZ1 y hy hQy (hyN.trans (Q.NQ_lt_S hα))
  Q_cl := fun α hα Z hZ hZ1 y hy hQy hyN => Q.F_cl Z hZ hZ1 y hy hQy (hyN.trans (Q.NQ_lt_S hα))
  N_cl := fun α hα Z hZ hZ1 hN => by
    rw [Q.NQ_eq hα] at hN
    have hα1 : α + 1 < Om 1 := by rw [← Br.Om1_eq]; exact gl_Om1_lim.add_one_lt hα
    have hαZ : α + 1 < Z := he_cl_level le_add_self hα1 hZ hZ1
      (hd_succ_lt (lt_of_le_of_lt zero_le (lt_add_one α)).ne' _)
      (Q.G_lt.trans ((lt_add_one _).trans_le (right_le_veblen _ _))) hN le_rfl
      ((isNormal_veblen _).strictMono (lt_add_one _))
    have hQ := hd_cl_succ_fix le_add_self hZ hZ1 Q.G_lt.le hN
    exact max_lt (Q.F_cl Z hZ hZ1 _ hQ le_rfl Q.F_lt_S) ((lt_add_one α).trans hαZ)
  P_gt := fun α hα x hx hx1 hγ => Q.Fr_gtx hx hx1 (max_lt_iff.1 hγ).1
  P_fix := fun α hα x hx hx1 hγ => Q.rfix0 hx hx1 (max_lt_iff.1 hγ).1 (max_lt_iff.1 hγ).2
  N_Zo := fun α hα x hx hx1 hγ => by
    have h := Q.S_Zo hx hx1 (max_lt_iff.1 hγ).1
    rw [add_zero] at h
    exact (hdN_lt_Nx ((ev_isSuccLimit_of_inE hx).add_one_lt (max_lt_iff.1 hγ).2)).trans h
  Zo_fix := Q.Zo_fix
  Zo_G1 := Q.Zo_G1
  P_pi := fun α hα σ ρ hB hγ => Q.Fr_pi hB (max_lt_iff.1 hγ).1
  N_pi := fun α {σ ρ} hα hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hγσ : Q.γ < σ := (max_lt_iff.1 hγ).1
    have hγρ : Q.γ < ρ := hγσ.trans hB.2.2.1
    have h : α + 1 < σ := (ev_isSuccLimit_of_inE hB.1).add_one_lt (max_lt_iff.1 hγ).2
    obtain ⟨f1, f2⟩ := Q.Fr_pi hB hγσ
    have hh := glA_pi hB (mem_TB_of_lt hB h) (h.trans hσ1) f1 (gm1_T hB.2.1 hρ1 (Q.Fr_lt1 hB.2.1 hρ1 hγρ)).2
    rw [pi_lt hB h, f2, ← Q.NP_glA0 hB.2.1 hρ1 hγρ (h.trans hB.2.2.1), ← Q.NP_glA0 hB.1 hσ1 hγσ h] at hh
    exact hh
  Pn_lt := fun hx hx1 hγ => by have := Q.S_lt1x hx hx1 hγ; rwa [add_zero] at this
  Pn_pi := fun hB hγ => by have := Q.S_pi hB hγ; rwa [add_zero, add_zero] at this
  Qn_mem := fun S _ _ ha hb => by have := Q.S_mem S ha hb; rwa [add_zero] at this
  Qn_cl := fun Z hZ hZ1 h => Q.S_cl Z hZ hZ1 (by rw [add_zero]; exact h)

end HiVQ

/-- **The type of a step of level `Ω₁ + ν`.** -/
abbrev HiVStTy (ν : Ordinal.{0}) : Type 1 := ∀ (Q : HiVQ ν) (U : HgVD), HgSStart (hiVPB Q) U → HgVD

/-- **The step of level `Ω₁ + 0`**: the union over all countable levels over the gated abstract base. -/
noncomputable def hiVLS0 : HiVStTy 0 := fun Q U h => hiQU Q.toQB U h

/-- **THE STEP OF LEVEL `Ω₁ + 0` HAS THE SPECIFICATION.** -/
theorem hiv0_spec (Q : HiVQ 0) (U : HgVD) (h : HgSStart (hiVPB Q) U) : HiVSpec Q U (hiVLS0 Q U h) where
  B := by rw [add_zero]; rfl
  γ := rfl
  b := fun x _ _ _ => by rw [add_zero]; rfl
  Z := fun x _ _ => by rw [add_zero]; rfl
  extR := fun c x hc => (hiQU_ext Q.toQB U h hc).1 x
  extg := fun c hc => (hiQU_ext Q.toQB U h hc).2
  high := fun c σ hFc hc hσ hσ1 hg => hiQU_high Q.toQB U h hFc (by rw [add_zero] at hc; exact hc) hσ hσ1 hg
  RF := fun x hx hx1 hγ => hiQU_RQ Q.toQB U h hx hx1 hγ
  gF := fun x hx hx1 => hiQU_gQ Q.toQB U h hx hx1

/-! ## The successor and limit cases -/

open Classical in
/-- **The successor case**: one more offset recursion (when the step of level `Ω₁ + ν` has the specification). -/
noncomputable def hiVLSucc (ν : Ordinal.{0}) (St : HiVStTy ν) : HiVStTy (ν + 1) := fun P U h =>
  if H : ∀ Q U h, HiVSpec Q U (St Q U h) then hiVScT rfl P H U h else U

/-- **The fundamental sequence of the limit level `Ω₁ + λ`**: `Ω₁ + heFs λ k`. -/
noncomputable def hiVLmOf (l : Ordinal.{0}) (hl : IsSuccLimit l) (hle : l < Om1) : HiVLm l where
  β := fun k => heFs l k
  lt := fun k => heFs_lt hl (hgf_om hle) k
  mono := fun k => (heFs_mono hl (hgf_om hle) k).le
  cof := fun t ht => heFs_cof hl (hgf_om hle) t ht
  lim := hl
  lv := hle

/-- **The condition at a limit**: every earlier step has the specification, and later steps extend earlier ones at
the same pseudo-base. -/
def HiVLCoh (l : Ordinal.{0}) (IH : ∀ ν, ν < l → HiVStTy ν) : Prop :=
  (∀ ν (h : ν < l), ∀ Q U h', HiVSpec Q U (IH ν h Q U h')) ∧
    ∀ ν ν' (h : ν < l) (h' : ν' < l) (hνν' : ν < ν') (Q : HiVQ ν') (U : HgVD)
      (hU : HgSStart (hiVPB Q) U) (c x : Ordinal.{0}),
      c < (IH ν h (Q.down hνν') U hU).B →
      (IH ν' h' Q U hU).R c x = (IH ν h (Q.down hνν') U hU).R c x ∧
      (IH ν' h' Q U hU).g c = (IH ν h (Q.down hνν') U hU).g c

section LimDef

variable (l : Ordinal.{0}) (hl : IsSuccLimit l) (hle : l < Om1) (IH : ∀ ν, ν < l → HiVStTy ν)
  (H : HiVLCoh l IH)

/-- The steps of the levels `Ω₁ + λ_k`. -/
noncomputable abbrev hiVLmSt (k : ℕ) : HiVStTy ((hiVLmOf l hl hle).β k) :=
  IH (heFs l k) (heFs_lt hl (hgf_om hle) k)

include H in
theorem hiVLmSt_spec (k : ℕ) : ∀ Q U h, HiVSpec Q U (hiVLmSt l hl hle IH k Q U h) :=
  H.1 (heFs l k) (heFs_lt hl (hgf_om hle) k)

include H in
theorem hiVLmSt_coh (P : HiVQ l) (U : HgVD) (hU : HgSStart (hiVPB P) U) (k : ℕ) (c x : Ordinal.{0})
    (hc : c < (hiVLmSt l hl hle IH k (P.down ((hiVLmOf l hl hle).lt k)) U hU).B) :
    (hiVLmSt l hl hle IH (k + 1) (P.down ((hiVLmOf l hl hle).lt (k + 1))) U hU).R c x =
      (hiVLmSt l hl hle IH k (P.down ((hiVLmOf l hl hle).lt k)) U hU).R c x ∧
    (hiVLmSt l hl hle IH (k + 1) (P.down ((hiVLmOf l hl hle).lt (k + 1))) U hU).g c =
      (hiVLmSt l hl hle IH k (P.down ((hiVLmOf l hl hle).lt k)) U hU).g c :=
  H.2 (heFs l k) (heFs l (k + 1)) (heFs_lt hl (hgf_om hle) k) (heFs_lt hl (hgf_om hle) (k + 1))
    (heFs_mono hl (hgf_om hle) k) _ U hU c x hc

end LimDef

open Classical in
/-- **The limit case**: the union of the chain of the steps of the levels `Ω₁ + λ_k` (when the condition holds). -/
noncomputable def hiVLLim (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ ν, ν < l → HiVStTy ν) : HiVStTy l :=
  fun P U h =>
  if hle : l < Om1 then
    if H : HiVLCoh l IH then
      hiVLmT (hiVLmOf l hl hle) (hiVLmSt l hl hle IH) (hiVLmSt_spec l hl hle IH H) P U h
        (hiVLmSt_coh l hl hle IH H P U h)
    else U
  else U

/-- **THE STEP OF EVERY LEVEL `Ω₁ + ν`, BY ONE RECURSION ON THE LEVEL.** -/
noncomputable def hiVLS (ν : Ordinal.{0}) : HiVStTy ν :=
  Ordinal.limitRecOn (motive := fun ν => HiVStTy ν) ν hiVLS0 hiVLSucc hiVLLim

theorem hiVLS_zero : hiVLS 0 = hiVLS0 := by unfold hiVLS; rw [Ordinal.limitRecOn_zero]

theorem hiVLS_succ (ν : Ordinal.{0}) : hiVLS (ν + 1) = hiVLSucc ν (hiVLS ν) := by
  unfold hiVLS; rw [Ordinal.limitRecOn_add_one]

theorem hiVLS_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : hiVLS l = hiVLLim l hl (fun ν _ => hiVLS ν) := by
  unfold hiVLS; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

/-- The extension statement between two levels at one pseudo-base. -/
def HiVLExt (ν' ν : Ordinal.{0}) (hν' : ν' < ν) : Prop :=
  ∀ (Q : HiVQ ν) (U : HgVD) (hU : HgSStart (hiVPB Q) U) (c x : Ordinal.{0}),
    c < (hiVLS ν' (Q.down hν') U hU).B →
    (hiVLS ν Q U hU).R c x = (hiVLS ν' (Q.down hν') U hU).R c x ∧
    (hiVLS ν Q U hU).g c = (hiVLS ν' (Q.down hν') U hU).g c

/-- **THE INVARIANT**: every `hiVLS ν`, `ν < Ω₁`, has the specification of level `Ω₁ + ν` and extends every
`hiVLS ν'`, `ν' < ν`, at the same pseudo-base. -/
theorem hiVLS_inv : ∀ ν (hν : ν < Om1), (∀ Q U h, HiVSpec Q U (hiVLS ν Q U h)) ∧
    ∀ ν' (hν' : ν' < ν), HiVLExt ν' ν hν' := by
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hν
  rcases zero_or_succ_or_isSuccLimit ν with h0 | ⟨μ, hμ⟩ | hlim
  · subst h0
    refine ⟨fun Q U h => ?_, fun ν' hν' => absurd hν' (not_lt.2 zero_le)⟩
    rw [hiVLS_zero]
    exact hiv0_spec Q U h
  · have hμ' : ν = μ + 1 := by rw [← hμ, succ_eq_add_one]
    subst hμ'
    have hμε : μ < Om1 := (lt_add_one μ).trans hν
    obtain ⟨hsp, hext⟩ := IH μ (lt_add_one μ) hμε
    have e : ∀ P U h, hiVLS (μ + 1) P U h = hiVScT rfl P hsp U h := fun P U h => by
      rw [hiVLS_succ]; unfold hiVLSucc; rw [dif_pos hsp]
    refine ⟨fun P U h => by rw [e]; exact hiVScT_spec rfl P hsp U h, fun ν' hν' => ?_⟩
    intro P U hU c x hc
    rw [e]
    rcases (Order.lt_add_one_iff.1 hν').lt_or_eq with hlt | heq
    · have hB' : (hiVLS ν' (P.down hν') U hU).B = hdNx (Om1 + ν') P.F :=
        ((IH ν' hν' (hν'.trans hν)).1 _ U hU).B
      have hBμ : (hiVLS μ (P.down (hiv_lt_of_eq rfl)) U hU).B = hdNx (Om1 + μ) P.F :=
        (hsp (P.down (hiv_lt_of_eq rfl)) U hU).B
      have hc' : c < (hiVLS μ (P.down (hiv_lt_of_eq rfl)) U hU).B := by
        rw [hBμ]; rw [hB'] at hc; exact hc.trans_le (hdNx_mono (add_le_add le_rfl hlt.le) _)
      obtain ⟨r1, g1⟩ := hiVScT_ext rfl P hsp U hU hc' x
      obtain ⟨r2, g2⟩ := hext ν' hlt (P.down (hiv_lt_of_eq rfl)) U hU c x hc
      exact ⟨r1.trans r2, g1.trans g2⟩
    · subst heq
      exact hiVScT_ext rfl P hsp U hU hc x
  · have hcoh : HiVLCoh ν (fun ν' _ => hiVLS ν') :=
      ⟨fun ν' h => (IH ν' h (h.trans hν)).1, fun ν₁ ν₂ h₁ h₂ h12 Q U hU c x hc =>
        (IH ν₂ h₂ (h₂.trans hν)).2 ν₁ h12 Q U hU c x hc⟩
    have e : ∀ P U h, hiVLS ν P U h = hiVLmT (hiVLmOf ν hlim hν) (hiVLmSt ν hlim hν (fun ν' _ => hiVLS ν'))
        (hiVLmSt_spec ν hlim hν _ hcoh) P U h (hiVLmSt_coh ν hlim hν _ hcoh P U h) := fun P U h => by
      rw [hiVLS_limit hlim]; unfold hiVLLim; rw [dif_pos hν, dif_pos hcoh]
    refine ⟨fun P U h => by rw [e]; exact hiVLmT_spec _ _ _ _ _ _ _, fun ν' hν' => ?_⟩
    intro P U hU c x hc
    rw [e]
    obtain ⟨k, hk⟩ := heFs_cof hlim (hgf_om hν) ν' hν'
    have hkl := heFs_lt hlim (hgf_om hν) k
    obtain ⟨hspk, hextk⟩ := IH _ hkl (hkl.trans hν)
    have hc' : c < (hiVLS (heFs ν k) (P.down hkl) U hU).B := by
      rw [(hspk (P.down hkl) U hU).B]
      rw [((IH ν' hν' (hν'.trans hν)).1 (P.down hν') U hU).B] at hc
      exact hc.trans_le (hdNx_mono (add_le_add le_rfl hk.le) _)
    obtain ⟨r1, g1⟩ := hiVLmT_ext (hiVLmOf ν hlim hν) (hiVLmSt ν hlim hν (fun ν' _ => hiVLS ν'))
      (hiVLmSt_spec ν hlim hν _ hcoh) P U hU (hiVLmSt_coh ν hlim hν _ hcoh P U hU) k hc' x
    obtain ⟨r2, g2⟩ := hextk ν' hk (P.down hkl) U hU c x hc
    exact ⟨r1.trans r2, g1.trans g2⟩

/-- **THE STEP OF EVERY LEVEL `Ω₁ + ν` HAS THE SPECIFICATION.** -/
theorem hiVLS_spec {ν : Ordinal.{0}} (hν : ν < Om1) (Q : HiVQ ν) (U : HgVD) (h : HgSStart (hiVPB Q) U) :
    HiVSpec Q U (hiVLS ν Q U h) := (hiVLS_inv ν hν).1 Q U h

end Googology.Trans.PoR.InaccPsi.R2.Hi
