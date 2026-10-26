import Googology.Trans.PoR.InaccPsi.R2.HgQ

/-!
# HgQL: THE RECURSION ON THE LEVEL OVER AN ABSTRACT BASE `Q`: EVERY `φ(ω+ν+1, Q+1)`, `ν < Ω₁`

The copy of `Hf.HfMG` for an abstract base `B : Hg.HgQB` with a start `U` of the stage at `Q` (in place of `G`, the
readings `Γ_{x+1}` and the start `Hc.hcWU`).  `Q` is a base of every countable level (`HgQB.toB α`, code gate `0`,
reading gate `α`).  The systems `hgQL ν` (bound `N_{ω+ν}(Q) = φ(ω+ν+1, Q+1)`, base gate `≤ ω+ν`) are defined by one
recursion on `ν < Ω₁`: `hgQL 0 = Hg.hgQT` (the system at `φ(ω+1, Q+1)`); `hgQL (ν+1)` is the union of all gated
offsets over `Q` at level `ω+ν+1` with the step `Hg.hgfLS (ν+1)`, started at `hgQL ν` with its base gate raised to the
level (`Hg.hgRegateQ`); at a limit `λ` the systems `hgQL λ_k` (`λ_k = He.heFs λ k`) form a gated `ω`-chain
(`Hg.HgfCh`) whose union starts the offset recursion at level `ω+λ`.

* `HgQB.glA_P`, `HgQB.veb_lt_Zo`, `HgQB.vebP_pi`, `hgQ_start` (a system of the right shape starts the offset
  recursion over `Q` at level `α`);
* `HgQOK`, `HgQCoh`, `hgQLCh`, `hgQLCh_start`, `hgQ_OK_start`, `hgQLSucc`, `hgQLLim`, `hgQL` (**THE RECURSION ON THE
  LEVEL OVER `Q`**), `hgQL_inv` (**THE INVARIANT**), `hgQL_B`, `hgQL_γ`, `hgQL_γ_eq`.

No new axiom.  New definitions: `HgQOK`, `HgQCoh`, `hgQLCh`, `hgQLSucc`, `hgQLLim`, `hgQL`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hg

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

namespace HgQB

variable (B : HgQB)

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **`ϑˣ(Ω₁·α + P(x)) = φ(α, P(x)+1)`** for `1 ≤ α < x`. -/
theorem glA_P {α : Ordinal.{0}} (h1 : 1 ≤ α) (h : α < x) : glA α (B.P x) x = veblen α (B.P x + 1) :=
  hc_glA_fixG hx hx1 h1 (h.trans (gm1_facts hx hx1).2.1) (B.P_fix hx hx1 α h) (h.trans (B.P_gt hx hx1))
    (B.P_gt hx hx1) (B.P_lt hx hx1)

/-- **`φ(β, P(x)+1) < Z_o(x)`** for `β < x`. -/
theorem veb_lt_Zo {β : Ordinal.{0}} (h : β < x) : veblen β (B.P x + 1) < B.Zo x :=
  hc_next_lt_N.trans (B.N_lt_Zo hx hx1 h)

theorem evN_lt_Zo {β : Ordinal.{0}} (h : β < x) : evZ (hcN β (B.P x)) < B.Zo x :=
  hb_evZ_lt_fix2 (B.Zo_fix x) (B.N_lt_Zo hx hx1 h)

end Base

/-- **Lemma EXACT for `φ(β, P(ρ)+1) = ϑᵖ(Ω₁·β + P(ρ))`**, every level `1 ≤ β < σ`. -/
theorem vebP_pi {β σ ρ : Ordinal.{0}} (h1 : 1 ≤ β) (hβσ : β < σ) (hB : Bases σ ρ) :
    veblen β (B.P ρ + 1) ∈ TB ρ σ ∧ pi σ ρ (veblen β (B.P ρ + 1)) = veblen β (B.P σ + 1) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨g1, g2⟩ := B.P_pi hB
  have h := glA_pi hB (mem_TB_of_lt hB hβσ) (hβσ.trans hσ1) g1 (B.P_T hB.2.1 hρ1).2
  rw [pi_lt hB hβσ, g2, B.glA_P hB.2.1 hρ1 h1 (hβσ.trans hB.2.2.1), B.glA_P hB.1 hσ1 h1 hβσ] at h
  exact h

end HgQB

/-- **A system with bound `φ(α, Q+1)`, base gate `α`, base reading `φ(α, P(x)+1)` above `α` and bound field `evZ` of
it above `α`, `Z_o` below, STARTS THE OFFSET RECURSION OVER `Q` AT LEVEL `α`.** -/
theorem hgQ_start (B : HgQB) {α : Ordinal.{0}} (hα : HfLvl α) (T : HgVD) (hB : T.B = veblen α (B.Q + 1))
    (hγ : T.γ = α) (hb : ∀ x, InE x → x < Om1 → α < x → T.b x = veblen α (B.P x + 1))
    (hZ : ∀ x, InE x → x < Om1 → T.Z x = if α < x then evZ (veblen α (B.P x + 1)) else B.Zo x) :
    HgfMStart (B.toB α hα) T where
  B := by rw [add_zero]; exact hB
  Zb := fun x hx hx1 => by
    rw [hZ x hx hx1]
    show (if α < x then evZ (veblen α (B.P x + 1)) else B.Zo x) ≤ if α < x then hcN α (B.P x) else B.Zo x
    split_ifs
    · exact (hb_evZ_lt_fix2 (hc_fix_down hα.two_lt.le (hcN_fix α _)) hc_next_lt_N).le
    · exact le_rfl
  st := fun h2 hZ' => {
    ix := by
      show T.ix = veblen α (B.Q + 1 + 0)
      rw [add_zero]; exact hg_ix_of_B (veblen_veblen_of_lt hα.one_lt _) hB
    γ := fun x _ _ => by
      show T.γ < x ↔ max α (T.g 0) < x
      rw [hγ, T.g_zero, max_eq_left zero_le]
    b := fun x hx hx1 h => by
      have h' : α < x := by
        have : max α (T.g 0) < x := h
        rwa [T.g_zero, max_eq_left zero_le] at this
      show T.b x = glA α (B.P x + T.R 0 x) x
      rw [T.R_zero, add_zero, hb x hx hx1 h', B.glA_P hx hx1 hα.one_le h']
    Z := fun x hx hx1 => by
      unfold HgPB.Zst
      show T.Z x = if max α (T.g 0) < x then evZ (glA α (B.P x + T.R 0 x) x) else (B.toB α hα).Zl x
      rw [T.g_zero, max_eq_left zero_le, T.R_zero, add_zero, hZ x hx hx1]
      by_cases h : α < x
      · rw [if_pos h, if_pos h, B.glA_P hx hx1 hα.one_le h]
      · rw [if_neg h, if_neg h, (B.toB α hα).Zl_low h]; rfl }
  high0 := fun _ _ _ _ hσ _ _ => hσ.pos

/-! ## The recursion on the level -/

/-- **The shape of the system at level `ω + ν` over `Q`.** -/
def HgQOK (B : HgQB) (ν : Ordinal.{0}) (T : HgVD) : Prop :=
  T.B = hcN (ω + ν) B.Q ∧ T.γ ≤ ω + ν ∧ (∀ x, InE x → x < Om1 → ω + ν < x → T.b x = hcN (ω + ν) (B.P x)) ∧
    ∀ x, InE x → x < Om1 → T.Z x = if ω + ν < x then evZ (hcN (ω + ν) (B.P x)) else B.Zo x

/-- **The condition at a limit**. -/
def HgQCoh (B : HgQB) (l : Ordinal.{0}) (IH : ∀ ν, ν < l → HgVD) : Prop :=
  (∀ ν (h : ν < l), HgQOK B ν (IH ν h)) ∧ ∀ ν ν' (h : ν < l) (h' : ν' < l), ν ≤ ν' → ∀ c x, c < (IH ν h).B →
    (IH ν' h').R c x = (IH ν h).R c x ∧ (IH ν' h').g c = (IH ν h).g c

theorem hgQL_kle {l : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l < Om1) (k : ℕ) : ω + heFs l k ≤ ω + l :=
  (add_le_add_iff_left ω).2 (heFs_lt hl (hgf_om hle) k).le

section LimCh

variable (B : HgQB) (l : Ordinal.{0}) (hl : IsSuccLimit l) (hle : l < Om1) (IH : ∀ ν, ν < l → HgVD)
  (H : HgQCoh B l IH)

include hle in
theorem hgQL_NxQ : hdNx (ω + l) B.Q = veblen (ω + l) (B.Q + 1) := hdNx_fixP (B.Q_fix _ (hgf_lev hle).2)

include hle in
theorem hgQL_Nxx {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (h : ω + l < x) :
    hdNx (ω + l) (B.P x) = veblen (ω + l) (B.P x + 1) :=
  hdNx_fixP (B.P_fix hx hx1 _ h)

include H in
/-- **THE CHAIN AT A LIMIT LEVEL** over `Q`. -/
noncomputable def hgQLCh : HgfCh where
  D := fun k => IH (heFs l k) (heFs_lt hl (hgf_om hle) k)
  B := hdNx (ω + l) B.Q
  b := fun x => hdNx (ω + l) (B.P x)
  γ := ω + l
  Zo := B.Zo
  γ_lt := (hgf_lev hle).2
  γ0 := fun k => (H.1 _ _).2.1.trans (hgQL_kle hl hle k)
  γ_cl := fun _ hZ hZ1 h => by
    rw [hgQL_NxQ B l hle] at h
    exact B.cl_lev (hgf_lev hle).one_le (hgf_lev hle).2 hZ hZ1 h
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
  B_lt1 := by rw [hgQL_NxQ B l hle]; exact B.veb_lt1 (hgf_lev hle).2
  B_fix := hdNx_fix (hgf_lev hle).one_lt _
  B_mem := fun S _ _ ha hb => by
    rw [hgQL_NxQ B l hle]
    exact CSet.phi_mem (he_cst_mem S le_rfl hb) (CSet.succ_mem (B.Q_mem S ha))
  b_ge := fun k x hx hx1 hγ => by
    rw [(H.1 _ _).2.2.1 x hx hx1 ((hgQL_kle hl hle k).trans_lt hγ)]
    exact (hdN_lt_Nx ((hgfLmOf l hl hle).lim.add_one_lt ((hgfLmOf l hl hle).lt k))).le
  b_cof := fun x hx hx1 hγ μ hμ => by
    obtain ⟨k, hk⟩ := hdNx_cof (hgfLmOf l hl hle).lim (hgfLmOf l hl hle).lt (hgfLmOf l hl hle).mono
      (hgfLmOf l hl hle).cof hμ
    exact ⟨k, by rw [(H.1 _ _).2.2.1 x hx hx1 ((hgQL_kle hl hle k).trans_lt hγ)]; exact hk⟩
  b_fix := fun x _ _ _ => hdNx_fix (hgf_lev hle).one_lt _
  b_gt := fun x hx hx1 _ => (B.P_gt hx hx1).trans (hdNx_gt _ _)
  b_lt := fun x hx hx1 hγ => by
    rw [hgQL_Nxx B l hle hx hx1 hγ]; exact (B.veb_lt_Zo hx hx1 hγ).trans (B.Zo_lt1 hx hx1)
  b_pi := fun σ ρ hB hγ => by
    rw [hgQL_Nxx B l hle hB.2.1 hB.2.2.2 (hγ.trans hB.2.2.1),
      hgQL_Nxx B l hle hB.1 (hB.2.2.1.trans hB.2.2.2) hγ]
    exact B.vebP_pi (hgf_lev hle).one_le hγ hB
  Z_low := fun k x hx hx1 hγ => by
    rw [(H.1 _ _).2.2.2 x hx hx1]
    split_ifs with h
    · exact (B.evN_lt_Zo hx hx1 h).le
    · exact le_rfl
  Zo_fix := B.Zo_fix1
  Zo_G1 := fun _ hx hx1 => B.Zo_lt1 hx hx1

theorem hgQLCh_start : HgfMStart (B.toB (ω + l) (hgf_lev hle)) (hgQLCh B l hl hle IH H).U :=
  hgQ_start B (hgf_lev hle) _ (hgQL_NxQ B l hle) rfl (fun x hx hx1 h => hgQL_Nxx B l hle hx hx1 h)
    (fun x hx hx1 => by
      show (if ω + l < x then evZ (hdNx (ω + l) (B.P x)) else B.Zo x) = _
      by_cases h : ω + l < x
      · rw [if_pos h, if_pos h, hgQL_Nxx B l hle hx hx1 h]
      · rw [if_neg h, if_neg h])

end LimCh

/-- **THE START AT `Q` OF THE NEXT LEVEL**: the gate raised to the level `ω + ν + 1` (`Hg.hgRegateQ`). -/
theorem hgQ_OK_start (B : HgQB) {ν : Ordinal.{0}} (hν : ν + 1 < Om1) {T : HgVD} (h : HgQOK B ν T) :
    ∃ (hB : T.B = veblen (ω + (ν + 1)) (B.Q + 1)) (hγ : T.γ ≤ ω + (ν + 1)),
      HgfMStart (B.toB (ω + (ν + 1)) (hgf_lev hν))
        (hgRegateQ T B.G_lt (hgf_lev hν).one_le (hgf_lev hν).2 hB hγ) := by
  have hl1 : ω + ν < Om1 := (hgf_lev ((lt_add_one ν).trans hν)).2
  have hB : T.B = veblen (ω + (ν + 1)) (B.Q + 1) := by rw [h.1, B.N_eq hl1, hgf_lev_e]
  have hγ : T.γ ≤ ω + (ν + 1) := h.2.1.trans (by rw [hgf_lev_e]; exact le_self_add)
  refine ⟨hB, hγ, hgQ_start B (hgf_lev hν) _ hB (hgRegateQ_γ T _ _ _ hB hγ) (fun x hx hx1 hx' => ?_)
    (fun x hx hx1 => ?_)⟩
  · have hx'' : ω + ν < x := (lt_add_one _).trans (by rw [← hgf_lev_e]; exact hx')
    show T.b x = _
    rw [h.2.2.1 x hx hx1 hx'', (B.NP_glA hx hx1 (by rw [← hgf_lev_e]; exact hx')).1, hgf_lev_e]
  · show T.Z x = _
    rw [h.2.2.2 x hx hx1]
    have hiff : ω + ν < x ↔ ω + (ν + 1) < x := by
      rw [hgf_lev_e]
      exact ⟨fun h' => (ev_isSuccLimit_of_inE hx).add_one_lt h', fun h' => (lt_add_one _).trans h'⟩
    by_cases h' : ω + ν < x
    · rw [if_pos h', if_pos (hiff.1 h'), (B.NP_glA hx hx1 (by rw [← hgf_lev_e]; exact hiff.1 h')).1, hgf_lev_e]
    · rw [if_neg h', if_neg (fun h'' => h' (hiff.2 h''))]

open Classical in
/-- **The successor case** over `Q`. -/
noncomputable def hgQLSucc (B : HgQB) (ν : Ordinal.{0}) (T : HgVD) : HgVD :=
  if H : ∃ hν : ν + 1 < Om1, HgQOK B ν T then
    hgfMTU (St := hgfLS (ν + 1)) (fun Q U h => hgfLS_spec H.choose Q U h)
      (hgQ_OK_start B H.choose H.choose_spec).choose_spec.choose_spec
  else T

open Classical in
/-- **The limit case** over `Q`. -/
noncomputable def hgQLLim (B : HgQB) (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ ν, ν < l → HgVD) (T0 : HgVD) :
    HgVD :=
  if H : ∃ hle : l < Om1, HgQCoh B l IH then
    hgfMTU (St := hgfLS l) (fun Q U h => hgfLS_spec H.choose Q U h)
      (hgQLCh_start B l hl H.choose IH H.choose_spec)
  else T0

/-- **THE SYSTEM AT `φ(ω+ν+1, Q+1)`, BY ONE RECURSION ON THE LEVEL `ν < Ω₁`.** -/
noncomputable def hgQL (B : HgQB) (U : HgVD) (hU : HgQStart B U) (ν : Ordinal.{0}) : HgVD :=
  Ordinal.limitRecOn (motive := fun _ => HgVD) ν (hgQT B U hU) (fun ν T => hgQLSucc B ν T)
    (fun l hl IH => hgQLLim B l hl IH (hgQT B U hU))

section Rec

variable (B : HgQB) (U : HgVD) (hU : HgQStart B U)

theorem hgQL_zero : hgQL B U hU 0 = hgQT B U hU := by unfold hgQL; rw [Ordinal.limitRecOn_zero]

theorem hgQL_succ (ν : Ordinal.{0}) : hgQL B U hU (ν + 1) = hgQLSucc B ν (hgQL B U hU ν) := by
  unfold hgQL; rw [Ordinal.limitRecOn_add_one]

theorem hgQL_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) :
    hgQL B U hU l = hgQLLim B l hl (fun ν _ => hgQL B U hU ν) (hgQT B U hU) := by
  unfold hgQL; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem hgQT_OK : HgQOK B 0 (hgQT B U hU) := by
  refine ⟨by rw [add_zero]; rfl, by rw [hgQT_γ]; exact zero_le, fun x _ _ _ => by rw [add_zero]; rfl,
    fun x hx _ => ?_⟩
  rw [add_zero]
  show (if (0 : Ordinal.{0}) < x then evZ (hcNw (B.P x)) else B.Zo x) = _
  rw [if_pos hx.pos, if_pos (omega0_lt_inE hx)]; rfl

theorem hgQ_TU_OK {ν : Ordinal.{0}} (hν : ν < Om1) {S0 : HgVD} (hS : HgfMStart (B.toB (ω + ν) (hgf_lev hν)) S0) :
    HgQOK B ν (hgfMTU (St := hgfLS ν) (fun Q U h => hgfLS_spec hν Q U h) hS) :=
  ⟨rfl, le_rfl, fun _ _ _ _ => rfl, fun x _ _ => rfl⟩

/-- **THE INVARIANT**: every `hgQL ν`, `ν < Ω₁`, has the shape at level `ω + ν` and extends every `hgQL ν'`,
`ν' ≤ ν`. -/
theorem hgQL_inv : ∀ ν, ν < Om1 → HgQOK B ν (hgQL B U hU ν) ∧ ∀ ν', ν' ≤ ν → ∀ c x, c < (hgQL B U hU ν').B →
    (hgQL B U hU ν).R c x = (hgQL B U hU ν').R c x ∧ (hgQL B U hU ν).g c = (hgQL B U hU ν').g c := by
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hν
  rcases zero_or_succ_or_isSuccLimit ν with h0 | ⟨μ, hμ⟩ | hlim
  · subst h0
    rw [hgQL_zero]
    refine ⟨hgQT_OK B U hU, fun ν' hν' c x _ => ?_⟩
    rw [nonpos_iff_eq_zero.1 hν', hgQL_zero]; exact ⟨rfl, rfl⟩
  · have hμ' : ν = μ + 1 := by rw [← hμ, succ_eq_add_one]
    subst hμ'
    have hμε : μ < Om1 := (lt_add_one μ).trans hν
    obtain ⟨hok, hext⟩ := IH μ (lt_add_one μ) hμε
    have hH : ∃ hν' : μ + 1 < Om1, HgQOK B μ (hgQL B U hU μ) := ⟨hν, hok⟩
    set hS := (hgQ_OK_start B hH.choose hH.choose_spec).choose_spec.choose_spec with hhS
    have e : hgQL B U hU (μ + 1) = hgfMTU (St := hgfLS (μ + 1)) (fun Q U h => hgfLS_spec hH.choose Q U h) hS := by
      rw [hgQL_succ]; unfold hgQLSucc; rw [dif_pos hH]
    rw [e]
    refine ⟨hgQ_TU_OK B hH.choose hS, fun ν' hν' c x hc => ?_⟩
    rcases hν'.lt_or_eq with hlt | heq
    · have hle : ν' ≤ μ := Order.lt_add_one_iff.1 hlt
      have hcμ : c < (hgQL B U hU μ).B := by
        rw [hok.1]; rw [(IH ν' (lt_of_le_of_lt hle (lt_add_one μ)) (hle.trans_lt hμε)).1.1] at hc
        exact hc.trans_le (hcN_mono ((add_le_add_iff_left ω).2 hle) _)
      obtain ⟨r2, g2⟩ := hext ν' hle c x hc
      exact ⟨(hgfMTU_R0 _ hS hcμ x).trans r2, (hgfMTU_g0 _ hS hcμ).trans g2⟩
    · subst heq; rw [e]; exact ⟨rfl, rfl⟩
  · have hcoh : HgQCoh B ν (fun ν' _ => hgQL B U hU ν') :=
      ⟨fun ν' h => (IH ν' h (h.trans hν)).1, fun ν₁ ν₂ h₁ h₂ h12 c x hc =>
        (IH ν₂ h₂ (h₂.trans hν)).2 ν₁ h12 c x hc⟩
    have hS := hgQLCh_start B ν hlim hν (fun ν' _ => hgQL B U hU ν') hcoh
    have e : hgQL B U hU ν = hgfMTU (St := hgfLS ν) (fun Q U h => hgfLS_spec hν Q U h) hS := by
      rw [hgQL_limit B U hU hlim]; unfold hgQLLim; rw [dif_pos ⟨hν, hcoh⟩]
    rw [e]
    refine ⟨hgQ_TU_OK B hν hS, fun ν' hν' c x hc => ?_⟩
    rcases hν'.lt_or_eq with hlt | heq
    · obtain ⟨k, hk⟩ := heFs_cof hlim (hgf_om hν) ν' hlt
      have hkl := heFs_lt hlim (hgf_om hν) k
      obtain ⟨hokk, hextk⟩ := IH _ hkl (hkl.trans hν)
      have hck : c < (hgQL B U hU (heFs ν k)).B := by
        rw [hokk.1]; rw [(IH ν' hlt (hlt.trans hν)).1.1] at hc
        exact hc.trans_le (hcN_mono ((add_le_add_iff_left ω).2 hk.le) _)
      set C := hgQLCh B ν hlim hν (fun ν' _ => hgQL B U hU ν') hcoh with hC
      have hcC : c < C.U.B := hck.trans (C.B_lt k)
      obtain ⟨r2, g2⟩ := hextk ν' hk.le c x hc
      refine ⟨(hgfMTU_R0 _ hS hcC x).trans ((C.U_R (k := k) hck x).trans r2),
        (hgfMTU_g0 _ hS hcC).trans ((C.U_g (k := k) hck).trans g2)⟩
    · subst heq; rw [e]; exact ⟨rfl, rfl⟩

theorem hgQL_B {ν : Ordinal.{0}} (hν : ν < Om1) : (hgQL B U hU ν).B = veblen (ω + ν + 1) (B.Q + 1) := by
  rw [(hgQL_inv B U hU ν hν).1.1, B.N_eq (hgf_lev hν).2]

theorem hgQL_γ {ν : Ordinal.{0}} (hν : ν < Om1) : (hgQL B U hU ν).γ ≤ ω + ν := (hgQL_inv B U hU ν hν).1.2.1

end Rec

end Googology.Trans.PoR.InaccPsi.R2.Hg
