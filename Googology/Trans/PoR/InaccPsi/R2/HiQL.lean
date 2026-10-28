import Googology.Trans.PoR.InaccPsi.R2.HiQB

/-!
# HiQL: THE RECURSION ON THE LEVEL OVER A GATED BASE `Q`: EVERY `φ(ω+ν+1, Q+1)`, `ν < Ω₁`

`Hg.hgQL` is the recursion on the level over a base `Q` with base gate `0`.  Here the base `B : Hi.HiQB` has a gate
`γ`: the level `ω + ν` is read through the gate `max(γ, ω+ν)` (the reading gate of `Hg.HhQB.toB`), and the
systems keep the HIGH property (a code `c ∈ [Q, T.B)` with gate below an `ε`-number `σ` forces `γ < σ`), the start
condition of the offset recursion over `Q` (`Hg.HgfMStart`, field `high0`).  The recursion and its invariant
(`hiQL_inv`) follow `Hg.hgQL` with these two changes; the step of level `ω + ν` is `Hg.hgfLS ν`, the base is
`Hg.HhQB.toB`, the limit chain is the gated chain `Hg.HgfCh`.

* `hiQ_start` (a system of the right shape starts the offset recursion over `Q` at level `α`), `HiQOK`, `HiQCoh`,
  `hiQLCh`, `hiQLCh_start`, `hiQ_OK_start`, `hiQLSucc`, `hiQLLim`, `hiQL` (**THE RECURSION ON THE LEVEL OVER A GATED
  `Q`**), `hiQL_inv` (**THE INVARIANT**), `hiQL_B`, `hiQL_γ`.

No new axiom.  New definitions: `HiQOK`, `HiQCoh`, `hiQLCh`, `hiQLSucc`, `hiQLLim`, `hiQL`.
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
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **The HIGH property of `T` over `Q`**: a code `c ∈ [Q, T.B)` with gate below an `ε`-number `σ` forces `γ < σ`. -/
def HiHigh (B : HiQB) (T : HgVD) : Prop :=
  ∀ c σ, B.Q ≤ c → c < T.B → InE σ → σ < Om1 → T.g c < σ → B.γ < σ

/-- **A system with bound `φ(α, Q+1)`, base gate `max(γ, α)`, base reading `φ(α, P(x)+1)` and bound field `evZ` of it
above the gate, `Z_o` below, and the HIGH property, STARTS THE OFFSET RECURSION OVER `Q` AT LEVEL `α`.** -/
theorem hiQ_start (B : HiQB) {α : Ordinal.{0}} (hα : HfLvl α) (T : HgVD) (hB : T.B = veblen α (B.Q + 1))
    (hγ : T.γ = max B.γ α) (hb : ∀ x, InE x → x < Om1 → max B.γ α < x → T.b x = veblen α (B.P x + 1))
    (hZ : ∀ x, InE x → x < Om1 → T.Z x = if max B.γ α < x then evZ (veblen α (B.P x + 1)) else B.Zo x)
    (hh : HiHigh B T) : HgfMStart (B.toB α hα) T where
  B := by rw [add_zero]; exact hB
  Zb := fun x hx hx1 => by
    rw [hZ x hx hx1]
    show (if max B.γ α < x then evZ (veblen α (B.P x + 1)) else B.Zo x) ≤
      if max B.γ α < x then hcN α (B.P x) else B.Zo x
    split_ifs
    · exact (hb_evZ_lt_fix2 (hc_fix_down hα.two_lt.le (hcN_fix α _)) hc_next_lt_N).le
    · exact le_rfl
  st := fun h2 hZ' => {
    ix := by
      show T.ix = veblen α (B.Q + 1 + 0)
      rw [add_zero]; exact hg_ix_of_B (veblen_veblen_of_lt hα.one_lt _) hB
    γ := fun x _ _ => by
      show T.γ < x ↔ max (max B.γ α) (T.g 0) < x
      rw [hγ, T.g_zero, max_eq_left zero_le]
    b := fun x hx hx1 h => by
      have h' : max B.γ α < x := by
        have : max (max B.γ α) (T.g 0) < x := h
        rwa [T.g_zero, max_eq_left zero_le] at this
      show T.b x = glA α (B.P x + T.R 0 x) x
      rw [T.R_zero, add_zero, hb x hx hx1 h',
        B.glA_P hx hx1 (max_lt_iff.1 h').1 hα.one_le (max_lt_iff.1 h').2]
    Z := fun x hx hx1 => by
      unfold HgPB.Zst
      show T.Z x = if max (max B.γ α) (T.g 0) < x then evZ (glA α (B.P x + T.R 0 x) x)
        else (B.toB α hα).Zl x
      rw [T.g_zero, max_eq_left zero_le, T.R_zero, add_zero, hZ x hx hx1]
      by_cases h : max B.γ α < x
      · rw [if_pos h, if_pos h, B.glA_P hx hx1 (max_lt_iff.1 h).1 hα.one_le (max_lt_iff.1 h).2]
      · rw [if_neg h, if_neg h, (B.toB α hα).Zl_low h]; rfl }
  high0 := fun c σ hFc hc hσ hσ1 hg => hh c σ hFc hc hσ hσ1 hg

/-! ## The recursion on the level -/

/-- **The shape of the system at level `ω + ν` over a gated `Q`.** -/
def HiQOK (B : HiQB) (ν : Ordinal.{0}) (T : HgVD) : Prop :=
  T.B = hcN (ω + ν) B.Q ∧ T.γ ≤ max B.γ (ω + ν) ∧
    (∀ x, InE x → x < Om1 → max B.γ (ω + ν) < x → T.b x = hcN (ω + ν) (B.P x)) ∧
    (∀ x, InE x → x < Om1 → T.Z x = if max B.γ (ω + ν) < x then evZ (hcN (ω + ν) (B.P x)) else B.Zo x) ∧
    HiHigh B T

/-- **The condition at a limit**. -/
def HiQCoh (B : HiQB) (l : Ordinal.{0}) (IH : ∀ ν, ν < l → HgVD) : Prop :=
  (∀ ν (h : ν < l), HiQOK B ν (IH ν h)) ∧ ∀ ν ν' (h : ν < l) (h' : ν' < l), ν ≤ ν' → ∀ c x, c < (IH ν h).B →
    (IH ν' h').R c x = (IH ν h).R c x ∧ (IH ν' h').g c = (IH ν h).g c

theorem hi_max_mono (γ : Ordinal.{0}) {a b : Ordinal.{0}} (h : a ≤ b) : max γ a ≤ max γ b :=
  max_le_max le_rfl h

section LimCh

variable (B : HiQB) (l : Ordinal.{0}) (hl : IsSuccLimit l) (hle : l < Om1) (IH : ∀ ν, ν < l → HgVD)
  (H : HiQCoh B l IH)

include hle in
theorem hiQL_NxQ : hdNx (ω + l) B.Q = veblen (ω + l) (B.Q + 1) := hdNx_fixP (B.Q_fix _ (hgf_lev hle).2)

include hle in
theorem hiQL_Nxx {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (h : max B.γ (ω + l) < x) :
    hdNx (ω + l) (B.P x) = veblen (ω + l) (B.P x + 1) :=
  hdNx_fixP (B.P_fixL hx hx1 (max_lt_iff.1 h).1 (max_lt_iff.1 h).2)

include H in
/-- **THE CHAIN AT A LIMIT LEVEL** over a gated `Q`. -/
noncomputable def hiQLCh : HgfCh where
  D := fun k => IH (heFs l k) (heFs_lt hl (hgf_om hle) k)
  B := hdNx (ω + l) B.Q
  b := fun x => hdNx (ω + l) (B.P x)
  γ := max B.γ (ω + l)
  Zo := B.Zo
  γ_lt := max_lt B.γ_lt (hgf_lev hle).2
  γ0 := fun k => (H.1 _ _).2.1.trans (hi_max_mono _ (hgQL_kle hl hle k))
  γ_cl := fun _ hZ hZ1 h => by
    rw [hiQL_NxQ B l hle] at h
    exact B.cl_levG (hgf_lev hle).one_le (hgf_lev hle).2 hZ hZ1 h
  B_mono := fun k => by
    rw [(H.1 _ _).1, (H.1 _ _).1]; exact hcN_mono ((hgfLmOf l hl hle).mono k) _
  B_lt := fun k => by
    rw [(H.1 _ _).1]; exact hdN_lt_Nx ((hgfLmOf l hl hle).lim.add_one_lt ((hgfLmOf l hl hle).lt k))
  B_cof := fun c hc => by
    obtain ⟨k, hk⟩ := hdNx_cof (hgfLmOf l hl hle).lim (hgfLmOf l hl hle).lt (hgfLmOf l hl hle).mono
      (hgfLmOf l hl hle).cof hc
    exact ⟨k, by rw [(H.1 _ _).1]; exact hk⟩
  R_ext := fun k c x hc => (H.2 _ _ _ _ (heFs_mono hl (hgf_om hle) k).le c x hc).1
  g_ext := fun k c hc => (H.2 _ _ _ _ (heFs_mono hl (hgf_om hle) k).le c 0 hc).2
  B_lt1 := by rw [hiQL_NxQ B l hle]; exact B.veb_lt1 (hgf_lev hle).2
  B_fix := hdNx_fix (hgf_lev hle).one_lt _
  B_mem := fun S _ _ ha hb => by
    rw [hiQL_NxQ B l hle]
    exact CSet.phi_mem (he_cst_mem S le_rfl (max_lt_iff.1 hb).2)
      (CSet.succ_mem (B.Q_mem S ha (max_lt_iff.1 hb).1))
  b_ge := fun k x hx hx1 hγ => by
    rw [(H.1 _ _).2.2.1 x hx hx1 ((hi_max_mono _ (hgQL_kle hl hle k)).trans_lt hγ)]
    exact (hdN_lt_Nx ((hgfLmOf l hl hle).lim.add_one_lt ((hgfLmOf l hl hle).lt k))).le
  b_cof := fun x hx hx1 hγ μ hμ => by
    obtain ⟨k, hk⟩ := hdNx_cof (hgfLmOf l hl hle).lim (hgfLmOf l hl hle).lt (hgfLmOf l hl hle).mono
      (hgfLmOf l hl hle).cof hμ
    exact ⟨k, by rw [(H.1 _ _).2.2.1 x hx hx1 ((hi_max_mono _ (hgQL_kle hl hle k)).trans_lt hγ)]; exact hk⟩
  b_fix := fun x _ _ _ => hdNx_fix (hgf_lev hle).one_lt _
  b_gt := fun x hx hx1 hγ => (B.P_gtL hx hx1 (max_lt_iff.1 hγ).1).trans (hdNx_gt _ _)
  b_lt := fun x hx hx1 hγ => by
    rw [hiQL_Nxx B l hle hx hx1 hγ]
    exact (B.veb_lt_Zo hx hx1 (max_lt_iff.1 hγ).1 (max_lt_iff.1 hγ).2).trans (B.Zo_G1 x hx hx1)
  b_pi := fun σ ρ hB hγ => by
    rw [hiQL_Nxx B l hle hB.2.1 hB.2.2.2 (hγ.trans hB.2.2.1),
      hiQL_Nxx B l hle hB.1 (hB.2.2.1.trans hB.2.2.2) hγ]
    exact B.vebP_pi (hgf_lev hle).one_le (max_lt_iff.1 hγ).2 hB (max_lt_iff.1 hγ).1
  Z_low := fun k x hx hx1 _ => by
    rw [(H.1 _ _).2.2.2.1 x hx hx1]
    split_ifs with h
    · exact (B.evN_lt_Zo hx hx1 (max_lt_iff.1 h).1 (max_lt_iff.1 h).2).le
    · exact le_rfl
  Zo_fix := B.Zo_fix1
  Zo_G1 := fun x hx hx1 => B.Zo_G1 x hx hx1

theorem hiQLCh_high : HiHigh B (hiQLCh B l hl hle IH H).U := by
  intro c σ hFc hc hσ hσ1 hg
  set C := hiQLCh B l hl hle IH H with hC
  obtain ⟨k, hk⟩ := C.B_cof c hc
  rw [C.U_g hk] at hg
  exact (H.1 _ _).2.2.2.2 c σ hFc hk hσ hσ1 hg

theorem hiQLCh_start : HgfMStart (B.toB (ω + l) (hgf_lev hle)) (hiQLCh B l hl hle IH H).U :=
  hiQ_start B (hgf_lev hle) _ (hiQL_NxQ B l hle) rfl (fun x hx hx1 h => hiQL_Nxx B l hle hx hx1 h)
    (fun x hx hx1 => by
      show (if max B.γ (ω + l) < x then evZ (hdNx (ω + l) (B.P x)) else B.Zo x) = _
      by_cases h : max B.γ (ω + l) < x
      · rw [if_pos h, if_pos h, hiQL_Nxx B l hle hx hx1 h]
      · rw [if_neg h, if_neg h])
    (hiQLCh_high B l hl hle IH H)

end LimCh

theorem hi_lev_iff {γ ν x : Ordinal.{0}} (hx : InE x) : max γ (ω + ν) < x ↔ max γ (ω + (ν + 1)) < x := by
  rw [hgf_lev_e, max_lt_iff, max_lt_iff]
  exact and_congr_right fun _ => ⟨fun h' => (ev_isSuccLimit_of_inE hx).add_one_lt h', fun h' => (lt_add_one _).trans h'⟩

/-- **THE START AT `Q` OF THE NEXT LEVEL**: the gate raised to `max(γ, ω + ν + 1)` (`Hg.hgRegate`). -/
theorem hiQ_OK_start (B : HiQB) {ν : Ordinal.{0}} (hν : ν + 1 < Om1) {T : HgVD} (h : HiQOK B ν T) :
    ∃ (hγ : T.γ ≤ max B.γ (ω + (ν + 1))) (h3 : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z {gcG 0} T.B →
      max B.γ (ω + (ν + 1)) < Z) (h4 : T.B = gcG 0 → max B.γ (ω + (ν + 1)) = 0),
      HgfMStart (B.toB (ω + (ν + 1)) (hgf_lev hν))
        (hgRegate T (max B.γ (ω + (ν + 1))) hγ (max_lt B.γ_lt (hgf_lev hν).2) h3 h4) := by
  have hl1 : ω + ν < Om1 := (hgf_lev ((lt_add_one ν).trans hν)).2
  have hB : T.B = veblen (ω + (ν + 1)) (B.Q + 1) := by rw [h.1, B.N_eq hl1, hgf_lev_e]
  have hγ : T.γ ≤ max B.γ (ω + (ν + 1)) := h.2.1.trans (hi_max_mono _ (by rw [hgf_lev_e]; exact le_self_add))
  have h3 : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z {gcG 0} T.B → max B.γ (ω + (ν + 1)) < Z :=
    fun Z hZ hZ1 hc => by
      rw [hB] at hc
      exact B.cl_levG (hgf_lev hν).one_le (hgf_lev hν).2 hZ hZ1 hc
  have h4 : T.B = gcG 0 → max B.γ (ω + (ν + 1)) = 0 := fun e => by
    exfalso
    rw [hB] at e
    have : gcG 0 < veblen (ω + (ν + 1)) (B.Q + 1) :=
      B.G_lt.trans ((lt_add_one _).trans_le (right_le_veblen _ _))
    rw [e] at this; exact lt_irrefl _ this
  refine ⟨hγ, h3, h4, hiQ_start B (hgf_lev hν) _ hB rfl (fun x hx hx1 hx' => ?_) (fun x hx hx1 => ?_) ?_⟩
  · have hx'' : max B.γ (ω + ν) < x := (hi_lev_iff hx).2 hx'
    show T.b x = _
    rw [h.2.2.1 x hx hx1 hx'', (B.NP_glA hx hx1 (max_lt_iff.1 hx').1
      (by rw [← hgf_lev_e]; exact (max_lt_iff.1 hx').2)).1, hgf_lev_e]
  · show T.Z x = _
    rw [h.2.2.2.1 x hx hx1]
    by_cases h' : max B.γ (ω + ν) < x
    · have h'' := (hi_lev_iff hx).1 h'
      rw [if_pos h', if_pos h'', (B.NP_glA hx hx1 (max_lt_iff.1 h'').1
        (by rw [← hgf_lev_e]; exact (max_lt_iff.1 h'').2)).1, hgf_lev_e]
    · rw [if_neg h', if_neg (fun h'' => h' ((hi_lev_iff hx).2 h''))]
  · intro c σ hFc hc hσ hσ1 hg
    exact h.2.2.2.2 c σ hFc hc hσ hσ1 hg

open Classical in
/-- **The successor case** over a gated `Q`. -/
noncomputable def hiQLSucc (B : HiQB) (ν : Ordinal.{0}) (T : HgVD) : HgVD :=
  if H : ∃ hν : ν + 1 < Om1, HiQOK B ν T then
    hgfMTU (St := hgfLS (ν + 1)) (fun Q U h => hgfLS_spec H.choose Q U h)
      (hiQ_OK_start B H.choose H.choose_spec).choose_spec.choose_spec.choose_spec
  else T

open Classical in
/-- **The limit case** over a gated `Q`. -/
noncomputable def hiQLLim (B : HiQB) (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ ν, ν < l → HgVD) (T0 : HgVD) :
    HgVD :=
  if H : ∃ hle : l < Om1, HiQCoh B l IH then
    hgfMTU (St := hgfLS l) (fun Q U h => hgfLS_spec H.choose Q U h)
      (hiQLCh_start B l hl H.choose IH H.choose_spec)
  else T0

/-- **THE SYSTEM AT `φ(ω+ν+1, Q+1)` OVER A GATED `Q`, BY ONE RECURSION ON THE LEVEL `ν < Ω₁`.** -/
noncomputable def hiQL (B : HiQB) (U : HgVD) (hU : HiQStart B U) (ν : Ordinal.{0}) : HgVD :=
  Ordinal.limitRecOn (motive := fun _ => HgVD) ν (hiQT B U hU) (fun ν T => hiQLSucc B ν T)
    (fun l hl IH => hiQLLim B l hl IH (hiQT B U hU))

section Rec

variable (B : HiQB) (U : HgVD) (hU : HiQStart B U)

theorem hiQL_zero : hiQL B U hU 0 = hiQT B U hU := by unfold hiQL; rw [Ordinal.limitRecOn_zero]

theorem hiQL_succ (ν : Ordinal.{0}) : hiQL B U hU (ν + 1) = hiQLSucc B ν (hiQL B U hU ν) := by
  unfold hiQL; rw [Ordinal.limitRecOn_add_one]

theorem hiQL_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) :
    hiQL B U hU l = hiQLLim B l hl (fun ν _ => hiQL B U hU ν) (hiQT B U hU) := by
  unfold hiQL; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem hiQT_OK : HiQOK B 0 (hiQT B U hU) := by
  refine ⟨by rw [add_zero]; rfl, by rw [hiQT_γ]; exact le_max_left _ _, fun x _ _ _ => by rw [add_zero]; rfl,
    fun x hx _ => ?_, fun c σ hFc hc hσ hσ1 hg => hiQT_high B U hU hc hFc hσ hσ1 hg⟩
  rw [add_zero]
  show (if B.γ < x then evZ (hcNw (B.P x)) else B.Zo x) = _
  have hiff : B.γ < x ↔ max B.γ ω < x := ⟨fun h => max_lt h (omega0_lt_inE hx), fun h => (max_lt_iff.1 h).1⟩
  by_cases h : B.γ < x
  · rw [if_pos h, if_pos (hiff.1 h)]; rfl
  · rw [if_neg h, if_neg (fun h' => h (hiff.2 h'))]

theorem hiQ_TU_OK {ν : Ordinal.{0}} (hν : ν < Om1) {S0 : HgVD} (hS : HgfMStart (B.toB (ω + ν) (hgf_lev hν)) S0) :
    HiQOK B ν (hgfMTU (St := hgfLS ν) (fun Q U h => hgfLS_spec hν Q U h) hS) :=
  ⟨rfl, le_rfl, fun _ _ _ _ => rfl, fun x _ _ => rfl,
    fun c σ hFc hc hσ hσ1 hg => hgfMT_high (fun Q U h => hgfLS_spec hν Q U h) hS hc hFc hσ hσ1 hg⟩

/-- **THE INVARIANT**: every `hiQL ν`, `ν < Ω₁`, has the shape at level `ω + ν` and extends every `hiQL ν'`,
`ν' ≤ ν`. -/
theorem hiQL_inv : ∀ ν, ν < Om1 → HiQOK B ν (hiQL B U hU ν) ∧ ∀ ν', ν' ≤ ν → ∀ c x, c < (hiQL B U hU ν').B →
    (hiQL B U hU ν).R c x = (hiQL B U hU ν').R c x ∧ (hiQL B U hU ν).g c = (hiQL B U hU ν').g c := by
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hν
  rcases zero_or_succ_or_isSuccLimit ν with h0 | ⟨μ, hμ⟩ | hlim
  · subst h0
    rw [hiQL_zero]
    refine ⟨hiQT_OK B U hU, fun ν' hν' c x _ => ?_⟩
    rw [nonpos_iff_eq_zero.1 hν', hiQL_zero]; exact ⟨rfl, rfl⟩
  · have hμ' : ν = μ + 1 := by rw [← hμ, succ_eq_add_one]
    subst hμ'
    have hμε : μ < Om1 := (lt_add_one μ).trans hν
    obtain ⟨hok, hext⟩ := IH μ (lt_add_one μ) hμε
    have hH : ∃ hν' : μ + 1 < Om1, HiQOK B μ (hiQL B U hU μ) := ⟨hν, hok⟩
    set hS := (hiQ_OK_start B hH.choose hH.choose_spec).choose_spec.choose_spec.choose_spec with hhS
    have e : hiQL B U hU (μ + 1) = hgfMTU (St := hgfLS (μ + 1)) (fun Q U h => hgfLS_spec hH.choose Q U h) hS := by
      rw [hiQL_succ]; unfold hiQLSucc; rw [dif_pos hH]
    rw [e]
    refine ⟨hiQ_TU_OK B hH.choose hS, fun ν' hν' c x hc => ?_⟩
    rcases hν'.lt_or_eq with hlt | heq
    · have hle : ν' ≤ μ := Order.lt_add_one_iff.1 hlt
      have hcμ : c < (hiQL B U hU μ).B := by
        rw [hok.1]; rw [(IH ν' (lt_of_le_of_lt hle (lt_add_one μ)) (hle.trans_lt hμε)).1.1] at hc
        exact hc.trans_le (hcN_mono ((add_le_add_iff_left ω).2 hle) _)
      obtain ⟨r2, g2⟩ := hext ν' hle c x hc
      exact ⟨(hgfMTU_R0 _ hS hcμ x).trans r2, (hgfMTU_g0 _ hS hcμ).trans g2⟩
    · subst heq; rw [e]; exact ⟨rfl, rfl⟩
  · have hcoh : HiQCoh B ν (fun ν' _ => hiQL B U hU ν') :=
      ⟨fun ν' h => (IH ν' h (h.trans hν)).1, fun ν₁ ν₂ h₁ h₂ h12 c x hc =>
        (IH ν₂ h₂ (h₂.trans hν)).2 ν₁ h12 c x hc⟩
    have hS := hiQLCh_start B ν hlim hν (fun ν' _ => hiQL B U hU ν') hcoh
    have e : hiQL B U hU ν = hgfMTU (St := hgfLS ν) (fun Q U h => hgfLS_spec hν Q U h) hS := by
      rw [hiQL_limit B U hU hlim]; unfold hiQLLim; rw [dif_pos ⟨hν, hcoh⟩]
    rw [e]
    refine ⟨hiQ_TU_OK B hν hS, fun ν' hν' c x hc => ?_⟩
    rcases hν'.lt_or_eq with hlt | heq
    · obtain ⟨k, hk⟩ := heFs_cof hlim (hgf_om hν) ν' hlt
      have hkl := heFs_lt hlim (hgf_om hν) k
      obtain ⟨hokk, hextk⟩ := IH _ hkl (hkl.trans hν)
      have hck : c < (hiQL B U hU (heFs ν k)).B := by
        rw [hokk.1]; rw [(IH ν' hlt (hlt.trans hν)).1.1] at hc
        exact hc.trans_le (hcN_mono ((add_le_add_iff_left ω).2 hk.le) _)
      set C := hiQLCh B ν hlim hν (fun ν' _ => hiQL B U hU ν') hcoh with hC
      have hcC : c < C.U.B := hck.trans (C.B_lt k)
      obtain ⟨r2, g2⟩ := hextk ν' hk.le c x hc
      refine ⟨(hgfMTU_R0 _ hS hcC x).trans ((C.U_R (k := k) hck x).trans r2),
        (hgfMTU_g0 _ hS hcC).trans ((C.U_g (k := k) hck).trans g2)⟩
    · subst heq; rw [e]; exact ⟨rfl, rfl⟩

theorem hiQL_B {ν : Ordinal.{0}} (hν : ν < Om1) : (hiQL B U hU ν).B = veblen (ω + ν + 1) (B.Q + 1) := by
  rw [(hiQL_inv B U hU ν hν).1.1, B.N_eq (hgf_lev hν).2]

theorem hiQL_γ {ν : Ordinal.{0}} (hν : ν < Om1) : (hiQL B U hU ν).γ ≤ max B.γ (ω + ν) :=
  (hiQL_inv B U hU ν hν).1.2.1

end Rec

end Googology.Trans.PoR.InaccPsi.R2.Hi
