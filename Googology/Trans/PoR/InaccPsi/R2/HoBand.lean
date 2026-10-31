import Googology.Trans.PoR.InaccPsi.R2.HoSeq

/-!
# HoBand: ONE RECURSION OF GATED PACKAGES OVER THE BAND LEVELS `Ω₁²·v + Ω₁·μ`, `μ < Ω₁`, AT EVERY PREFIX `v`

PORT of `Hn.HnRec` (prefix `Ω₁·Ω₁`, start `Hn.hnPkSq`) to every prefix `Ω₁²·v`, `1 ≤ v < Ω₁`, started at any
package `P₀` of the level `Ω₁²·v` (read `x·x·v` above the gate `hlGt v`): the successor is `Hn.HnPk.succ`, and at a
limit `λ` the level datum is `hoLv v λ` and the package is the limit package `Ho.hoPkL` of the coherent sequence at
`heFs λ k`.  What differs from `Hn.HnRec`: the prefix `Ω₁²·v` with its gate `hlGt v` (the gate of a band package lies
between `hlGt v` and `max (hlGt v) (hlGt μ)`), the start `P₀` as data, the limit package through the abstract
sequence `Ho.HoSeq`.

* `ho_sqv_lim`, `ho_sqv_succ` (`a·a·v` is a limit for an `ε`-number `a`);
* `HoBCoh`, `hoBSeqOf`, `hoBLimF`, `hoBPk P₀ μ` (**THE BAND PACKAGES**), `hoBPk_inv` (**THE INVARIANT**);
* `HoBF` (a band family: the packages with their invariants), `hoBF` (**THE BAND FAMILY OF THE PREFIX PACKAGE `P₀`**),
  `HoBF.good`.

No new axiom.  New definitions: `HoBCoh`, `hoBSeqOf`, `hoBLimF`, `hoBPk`, `HoBF`, `hoBF`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ho

open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
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

theorem ho_sqv_lim {a v : Ordinal.{0}} (ha : IsSuccLimit a) (hv1 : 1 ≤ v) : IsSuccLimit (a * a * v) :=
  isSuccLimit_mul_left (isSuccLimit_mul_left ha ha.bot_lt) (zero_lt_one.trans_le hv1)

theorem ho_sqv_succ {a v b : Ordinal.{0}} (ha : IsSuccLimit a) (hv1 : 1 ≤ v) (hb : b < a * a * v) :
    b + 1 < a * a * v := (ho_sqv_lim ha hv1).add_one_lt hb

section Band

variable {v : Ordinal.{0}} (hv1 : 1 ≤ v) (hv : v < Om1)

/-- **The condition at a limit**: the earlier packages have the levels `Ω₁²·v + Ω₁·μ` read `x·x·v + x·μ`, gates
between `hlGt v` and `max (hlGt v) (hlGt μ)`, the gates grow, and later steps extend earlier ones. -/
def HoBCoh (v l : Ordinal.{0}) (IH : ∀ μ, μ < l → HnPk) : Prop :=
  (∀ μ (h : μ < l), (IH μ h).Λ.L = Om1 * Om1 * v + Om1 * μ ∧
    ∀ x, (IH μ h).Λ.g < x → (IH μ h).Λ.l x = x * x * v + x * μ) ∧
    (∀ μ (h : μ < l), hlGt v ≤ (IH μ h).Λ.g ∧ (IH μ h).Λ.g ≤ max (hlGt v) (hlGt μ)) ∧
    ∀ μ' μ (h' : μ' < l) (h : μ < l), μ' < μ → (IH μ' h').Λ.g ≤ (IH μ h).Λ.g ∧ HnkExt (IH μ' h') (IH μ h)

/-- **The coherent sequence at a limit `λ < Ω₁`**: the packages at `heFs λ k`, below the band datum `hoLv v λ`. -/
noncomputable def hoBSeqOf (l : Ordinal.{0}) (hl : IsSuccLimit l) (hle : l < Om1) (IH : ∀ μ, μ < l → HnPk)
    (H : HoBCoh v l IH) : HoSeq (hoLv v l hv1 hv hle) where
  K := fun k => IH (heFs l k) (heFs_lt hl (hl_om hle) k)
  Kg := fun k => (H.2.1 _ _).2.trans (max_le_max le_rfl (hlGt_mono (heFs_lt hl (hl_om hle) k).le))
  Kgm := fun k => (H.2.2 _ _ _ _ (heFs_mono hl (hl_om hle) k)).1
  hL := fun k => by
    rw [(H.1 _ _).1, hoLv_L, add_assoc]; exact add_le_add le_rfl (HkSeq.mul_le (heFs_lt hl (hl_om hle) k))
  hl := fun k x _ _ hg => by
    have hgk := ((H.2.1 (heFs l k) (heFs_lt hl (hl_om hle) k)).2.trans
      (max_le_max le_rfl (hlGt_mono (heFs_lt hl (hl_om hle) k).le))).trans_lt hg
    rw [(H.1 (heFs l k) (heFs_lt hl (hl_om hle) k)).2 x hgk, hoLv_l hv1 hv hle hg, add_assoc]
    exact add_le_add le_rfl (HkSeq.mul_le (heFs_lt hl (hl_om hle) k))
  hLs := fun k => by
    rw [(H.1 _ _).1, (H.1 _ _).1, add_assoc]; exact add_le_add le_rfl (HkSeq.mul_le (heFs_mono hl (hl_om hle) k))
  hls := fun k x _ _ hg => by
    rw [(H.1 _ _).2 x (((H.2.2 _ _ _ _ (heFs_mono hl (hl_om hle) k)).1).trans_lt hg), (H.1 _ _).2 x hg, add_assoc]
    exact add_le_add le_rfl (HkSeq.mul_le (heFs_mono hl (hl_om hle) k))
  cofL := fun b hb => by
    rw [hoLv_L] at hb
    obtain ⟨k, hk⟩ := hn_cof1 (fun _ h => ho_sqv_succ gl_Om1_lim hv1 h) gv_Om1_pos (heFs_mono hl (hl_om hle))
      (heFs_cof hl (hl_om hle)) hb
    exact ⟨k, by rw [(H.1 _ _).1]; exact hk⟩
  cofl := fun x hx _ hg b hb => by
    rw [hoLv_l hv1 hv hle hg] at hb
    obtain ⟨k, hk⟩ := hn_cof1 (fun _ h => ho_sqv_succ (ev_isSuccLimit_of_inE hx) hv1 h) hx.pos
      (heFs_mono hl (hl_om hle)) (heFs_cof hl (hl_om hle)) hb
    refine ⟨k, ?_⟩
    have hgk := ((H.2.1 (heFs l k) (heFs_lt hl (hl_om hle) k)).2.trans
      (max_le_max le_rfl (hlGt_mono (heFs_lt hl (hl_om hle) k).le))).trans_lt hg
    rw [(H.1 (heFs l k) (heFs_lt hl (hl_om hle) k)).2 x hgk]; exact hk
  ext := fun k => (H.2.2 _ _ _ _ (heFs_mono hl (hl_om hle) k)).2

open Classical in
/-- **The limit case**: the limit package of the coherent sequence (when `λ < Ω₁` and the condition holds). -/
noncomputable def hoBLimF (P₀ : HnPk) (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ μ, μ < l → HnPk) : HnPk :=
  if h : l < Om1 ∧ HoBCoh v l IH then hoPkL (hoBSeqOf hv1 hv l hl h.1 IH h.2) else P₀

/-- **THE PACKAGES OF ALL BAND LEVELS `Ω₁²·v + Ω₁·μ`, BY ONE RECURSION ON `μ`**, started at `P₀`. -/
noncomputable def hoBPk (P₀ : HnPk) (μ : Ordinal.{0}) : HnPk :=
  Ordinal.limitRecOn (motive := fun _ => HnPk) μ P₀ (fun _ K => K.succ) (hoBLimF hv1 hv P₀)

variable (P₀ : HnPk)

theorem hoBPk_zero : hoBPk hv1 hv P₀ 0 = P₀ := by unfold hoBPk; rw [Ordinal.limitRecOn_zero]

theorem hoBPk_succ (μ : Ordinal.{0}) : hoBPk hv1 hv P₀ (μ + 1) = (hoBPk hv1 hv P₀ μ).succ := by
  unfold hoBPk; rw [Ordinal.limitRecOn_add_one]

theorem hoBPk_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) :
    hoBPk hv1 hv P₀ l = hoBLimF hv1 hv P₀ l hl (fun μ _ => hoBPk hv1 hv P₀ μ) := by
  unfold hoBPk; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem hoB_B_mono {K' K : HnPk} {μ' μ : Ordinal.{0}} (hK' : K'.Λ.L = Om1 * Om1 * v + Om1 * μ')
    (hK : K.Λ.L = Om1 * Om1 * v + Om1 * μ) (h : μ' ≤ μ) (F : Ordinal.{0}) :
    hdNx (K'.Λ.L + 0) F ≤ hdNx (K.Λ.L + 0) F := by
  rw [hK', hK]
  exact hdNx_mono (add_le_add (add_le_add le_rfl (mul_le_mul_left' h _)) le_rfl) _

theorem hoB_mul_le {a w b c : Ordinal.{0}} (h : b < c) : a * a * w + a * b + a ≤ a * a * w + a * c := by
  rw [add_assoc]; exact add_le_add le_rfl (HkSeq.mul_le h)

variable (hP0L : P₀.Λ.L = Om1 * Om1 * v) (hP0l : ∀ x, P₀.Λ.g < x → P₀.Λ.l x = x * x * v)
  (hP0g : P₀.Λ.g = hlGt v)
include hP0L hP0l hP0g

/-- **THE INVARIANT**: for every `μ < Ω₁` the package `hoBPk μ` has the level `Ω₁²·v + Ω₁·μ` read `x·x·v + x·μ`,
gate between `hlGt v` and `max (hlGt v) (hlGt μ)`, and for every `μ' < μ` its gate is `≥` that of `hoBPk μ'` and its
step extends the step of `hoBPk μ'` at every pseudo-base. -/
theorem hoBPk_inv : ∀ μ, μ < Om1 → ((hoBPk hv1 hv P₀ μ).Λ.L = Om1 * Om1 * v + Om1 * μ ∧
    ∀ x, (hoBPk hv1 hv P₀ μ).Λ.g < x → (hoBPk hv1 hv P₀ μ).Λ.l x = x * x * v + x * μ) ∧
    (hlGt v ≤ (hoBPk hv1 hv P₀ μ).Λ.g ∧ (hoBPk hv1 hv P₀ μ).Λ.g ≤ max (hlGt v) (hlGt μ)) ∧
    ∀ μ', μ' < μ → (hoBPk hv1 hv P₀ μ').Λ.g ≤ (hoBPk hv1 hv P₀ μ).Λ.g ∧
      HnkExt (hoBPk hv1 hv P₀ μ') (hoBPk hv1 hv P₀ μ) := by
  intro μ
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμ
  rcases zero_or_succ_or_isSuccLimit μ with h0 | ⟨ν, hν⟩ | hlim
  · subst h0
    rw [hoBPk_zero]
    refine ⟨⟨by rw [hP0L, mul_zero, add_zero], fun x hx => by rw [hP0l x hx, mul_zero, add_zero]⟩,
      ⟨hP0g.ge, hP0g.le.trans (le_max_left _ _)⟩, fun μ' h => absurd h (not_lt.2 zero_le)⟩
  · have hν' : μ = ν + 1 := by rw [← hν, succ_eq_add_one]
    subst hν'
    have hνε : ν < Om1 := (lt_add_one ν).trans hμ
    obtain ⟨⟨hL, hl⟩, ⟨hglo, hg⟩, hext⟩ := IH ν (lt_add_one ν) hνε
    refine ⟨⟨?_, fun x hgx => ?_⟩, ⟨?_, ?_⟩, fun μ' hμ' => ⟨?_, ?_⟩⟩
    · rw [hoBPk_succ]; show (hoBPk hv1 hv P₀ ν).Λ.L + Om1 = _; rw [hL, mul_add_one, add_assoc]
    · rw [hoBPk_succ] at hgx ⊢; show (hoBPk hv1 hv P₀ ν).Λ.l x + x = _; rw [hl x hgx, mul_add_one, add_assoc]
    · rw [hoBPk_succ]; exact hglo
    · rw [hoBPk_succ]; show (hoBPk hv1 hv P₀ ν).Λ.g ≤ _
      exact hg.trans (max_le_max le_rfl (hlGt_mono (le_add_right le_rfl)))
    · rw [hoBPk_succ]; show (hoBPk hv1 hv P₀ μ').Λ.g ≤ (hoBPk hv1 hv P₀ ν).Λ.g
      rcases (Order.lt_add_one_iff.1 hμ').lt_or_eq with hlt | heq
      · exact (hext μ' hlt).1
      · rw [heq]
    · rw [hoBPk_succ]
      intro hg' hL' hl' Q U hU c x hc
      have hsh := hnw_shape_dn Q ((hoBPk hv1 hv P₀ ν).h0 Q.dn U hU)
      show (hnwU Q.toW (hoBPk hv1 hv P₀ ν).St0 (hoBPk hv1 hv P₀ ν).h0
          ((hoBPk hv1 hv P₀ ν).St0 Q.dn U hU) hsh).R c x = _ ∧
        (hnwU Q.toW (hoBPk hv1 hv P₀ ν).St0 (hoBPk hv1 hv P₀ ν).h0
          ((hoBPk hv1 hv P₀ ν).St0 Q.dn U hU) hsh).g c = _
      rcases (Order.lt_add_one_iff.1 hμ').lt_or_eq with hlt | heq
      · obtain ⟨⟨hL1, hl1⟩, -⟩ := IH μ' (hlt.trans (lt_add_one ν)) (hlt.trans hνε)
        have hLa : (hoBPk hv1 hv P₀ μ').Λ.L + Om1 ≤ (hoBPk hv1 hv P₀ ν).Λ.L := by
          rw [hL1, hL]; exact hoB_mul_le hlt
        have hla : ∀ x, InE x → x < Om1 → (hoBPk hv1 hv P₀ ν).Λ.g < x →
            (hoBPk hv1 hv P₀ μ').Λ.l x + x ≤ (hoBPk hv1 hv P₀ ν).Λ.l x :=
          fun x _ _ hgx => by rw [hl1 x ((hext μ' hlt).1.trans_lt hgx), hl x hgx]; exact hoB_mul_le hlt
        have hc0 : c < ((hoBPk hv1 hv P₀ ν).St0 Q.dn U hU).B := by
          rw [((hoBPk hv1 hv P₀ ν).h0 Q.dn U hU).B]
          rw [((hoBPk hv1 hv P₀ μ').h0 _ U hU).B] at hc
          exact hc.trans_le (hoB_B_mono hL1 hL hlt.le _)
        obtain ⟨r1, g1⟩ := (hext μ' hlt).2 (hext μ' hlt).1 hLa hla Q.dn U hU c x hc
        exact ⟨(hnwU_R0 Q.toW (hoBPk hv1 hv P₀ ν).St0 (hoBPk hv1 hv P₀ ν).h0 _ hsh hc0 x).trans r1,
          (hnwU_g0 Q.toW (hoBPk hv1 hv P₀ ν).St0 (hoBPk hv1 hv P₀ ν).h0 _ hsh hc0).trans g1⟩
      · subst heq
        exact ⟨hnwU_R0 Q.toW (hoBPk hv1 hv P₀ μ').St0 (hoBPk hv1 hv P₀ μ').h0 _ hsh hc x,
          hnwU_g0 Q.toW (hoBPk hv1 hv P₀ μ').St0 (hoBPk hv1 hv P₀ μ').h0 _ hsh hc⟩
  · have hcoh : HoBCoh v μ (fun μ' _ => hoBPk hv1 hv P₀ μ') :=
      ⟨fun μ' h => (IH μ' h (h.trans hμ)).1, fun μ' h => (IH μ' h (h.trans hμ)).2.1,
        fun μ₁ μ₂ h₁ h₂ h12 => (IH μ₂ h₂ (h₂.trans hμ)).2.2 μ₁ h12⟩
    have e : hoBPk hv1 hv P₀ μ = hoPkL (hoBSeqOf hv1 hv μ hlim hμ (fun μ' _ => hoBPk hv1 hv P₀ μ') hcoh) := by
      rw [hoBPk_limit hv1 hv P₀ hlim]; unfold hoBLimF; rw [dif_pos ⟨hμ, hcoh⟩]
    have eg : (hoBPk hv1 hv P₀ μ).Λ.g = max (hlGt v) (hlGt μ) := by rw [e]; rfl
    refine ⟨⟨by rw [e]; rfl, fun x h => by rw [e] at h ⊢; exact hoLv_l hv1 hv hμ h⟩,
      ⟨eg.ge.trans' (le_max_left _ _), eg.le⟩, fun μ' hμ' => ⟨?_, ?_⟩⟩
    · rw [eg]
      exact (IH μ' hμ' (hμ'.trans hμ)).2.1.2.trans (max_le_max le_rfl (hlGt_mono hμ'.le))
    rw [e]
    intro hg' hL' hl' Q U hU c x hc
    let H := hoBSeqOf hv1 hv μ hlim hμ (fun μ' _ => hoBPk hv1 hv P₀ μ') hcoh
    obtain ⟨k, hk⟩ := heFs_cof hlim (hl_om hμ) μ' hμ'
    have hkl := heFs_lt hlim (hl_om hμ) k
    obtain ⟨⟨hLk, hlk⟩, -, hextk⟩ := IH _ hkl (hkl.trans hμ)
    obtain ⟨⟨hL1, hl1⟩, -⟩ := IH μ' hμ' (hμ'.trans hμ)
    have hLa : (hoBPk hv1 hv P₀ μ').Λ.L + Om1 ≤ (hoBPk hv1 hv P₀ (heFs μ k)).Λ.L := by
      rw [hL1, hLk]; exact hoB_mul_le hk
    have hla : ∀ x, InE x → x < Om1 → (hoBPk hv1 hv P₀ (heFs μ k)).Λ.g < x →
        (hoBPk hv1 hv P₀ μ').Λ.l x + x ≤ (hoBPk hv1 hv P₀ (heFs μ k)).Λ.l x :=
      fun x _ _ hgx => by rw [hl1 x ((hextk μ' hk).1.trans_lt hgx), hlk x hgx]; exact hoB_mul_le hk
    have hc' : c < (H.D Q U hU k).B := by
      rw [(H.D_spec Q U hU k).B]
      rw [((hoBPk hv1 hv P₀ μ').h0 _ U hU).B] at hc
      exact hc.trans_le (hoB_B_mono hL1 hLk hk.le _)
    obtain ⟨r1, g1⟩ := hoStL_ext H Q U hU k hc' x
    obtain ⟨r2, g2⟩ := (hextk μ' hk).2 (hextk μ' hk).1 hLa hla (Q.lowr (H.K k).Λ (H.Kg k) (H.hL k) (H.hl k)) U hU
      c x hc
    exact ⟨r1.trans r2, g1.trans g2⟩

theorem hoBPk_lim_Λ {l : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l < Om1) :
    (hoBPk hv1 hv P₀ l).Λ = hoLv v l hv1 hv hle := by
  have hcoh : HoBCoh v l (fun μ' _ => hoBPk hv1 hv P₀ μ') :=
    ⟨fun μ' h => (hoBPk_inv hv1 hv P₀ hP0L hP0l hP0g μ' (h.trans hle)).1,
      fun μ' h => (hoBPk_inv hv1 hv P₀ hP0L hP0l hP0g μ' (h.trans hle)).2.1,
      fun _ _ _ h₂ h12 => (hoBPk_inv hv1 hv P₀ hP0L hP0l hP0g _ (h₂.trans hle)).2.2 _ h12⟩
  rw [hoBPk_limit hv1 hv P₀ hl]; unfold hoBLimF; rw [dif_pos ⟨hle, hcoh⟩]; rfl

/-- **The gate of `hoBPk ν` below an `ε`-number `σ` forces `ν < σ`.** -/
theorem hoBPk_g_lt : ∀ ν, ν < Om1 → ∀ σ, InE σ → (hoBPk hv1 hv P₀ ν).Λ.g < σ → ν < σ := by
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hν σ hσ hg
  rcases zero_or_succ_or_isSuccLimit ν with h0 | ⟨μ, hμ⟩ | hlim
  · rw [h0]; exact hσ.pos
  · have hμ' : ν = μ + 1 := by rw [← hμ, succ_eq_add_one]
    subst hμ'
    have hg' : (hoBPk hv1 hv P₀ μ).Λ.g < σ := by rw [hoBPk_succ] at hg; exact hg
    exact (ev_isSuccLimit_of_inE hσ).add_one_lt (IH μ (lt_add_one μ) ((lt_add_one μ).trans hν) σ hσ hg')
  · rw [hoBPk_lim_Λ hv1 hv P₀ hP0L hP0l hP0g hlim hν] at hg
    exact (hoLv_gt hv1 hv hν hσ hg).2

end Band

/-! ## Band families -/

/-- **A BAND FAMILY AT THE PREFIX `Ω₁²·v`**: packages `K μ` (`μ < Ω₁`) of the levels `Ω₁²·v + Ω₁·μ` read
`x·x·v + x·μ`, gates between `hlGt v` and `max (hlGt v) (hlGt μ)`, growing, forcing `μ < σ`; successors are
`Hn.HnPk.succ`, limits have the datum `hoLv v λ`; later steps extend earlier ones. -/
structure HoBF (v : Ordinal.{0}) (hv1 : 1 ≤ v) (hv : v < Om1) where
  K : Ordinal.{0} → HnPk
  L : ∀ μ, μ < Om1 → (K μ).Λ.L = Om1 * Om1 * v + Om1 * μ
  l : ∀ μ, μ < Om1 → ∀ x, (K μ).Λ.g < x → (K μ).Λ.l x = x * x * v + x * μ
  glo : ∀ μ, μ < Om1 → hlGt v ≤ (K μ).Λ.g
  ghi : ∀ μ, μ < Om1 → (K μ).Λ.g ≤ max (hlGt v) (hlGt μ)
  gmono : ∀ μ' μ, μ' < μ → μ < Om1 → (K μ').Λ.g ≤ (K μ).Λ.g
  ext : ∀ μ' μ, μ' < μ → μ < Om1 → HnkExt (K μ') (K μ)
  succ : ∀ μ, K (μ + 1) = (K μ).succ
  lim : ∀ l (hl : IsSuccLimit l) (hle : l < Om1), (K l).Λ = hoLv v l hv1 hv hle
  glt : ∀ μ, μ < Om1 → ∀ σ, InE σ → (K μ).Λ.g < σ → μ < σ

namespace HoBF

variable {v : Ordinal.{0}} {hv1 : 1 ≤ v} {hv : v < Om1} (Kf : HoBF v hv1 hv)

/-- **Every band package is below the next prefix.** -/
theorem good {μ : Ordinal.{0}} (hμ : μ < Om1) : HoGood v (Kf.K μ).Λ :=
  hoGood_of hμ (Kf.L μ hμ) (Kf.l μ hμ) (Kf.glo μ hμ) (fun x hx _ hg => Kf.glt μ hμ x hx hg)

theorem good_succ {μ : Ordinal.{0}} (hμ : μ < Om1) : HoGood v (Kf.K μ).Λ.succ := by
  have h := Kf.good (gl_Om1_lim.add_one_lt hμ)
  rwa [Kf.succ] at h

theorem g_lt_x {μ x : Ordinal.{0}} (hx : InE x) (hvx : hlGt v < x) (hμ : μ < x) (hμ1 : μ < Om1) : (Kf.K μ).Λ.g < x :=
  (Kf.ghi μ hμ1).trans_lt (max_lt hvx ((hlGt_le μ).trans_lt hμ))

end HoBF

/-- **THE BAND FAMILY OF A PREFIX PACKAGE `P₀`** (`hoBPk`). -/
noncomputable def hoBF {v : Ordinal.{0}} (hv1 : 1 ≤ v) (hv : v < Om1) (P₀ : HnPk)
    (hP0L : P₀.Λ.L = Om1 * Om1 * v) (hP0l : ∀ x, P₀.Λ.g < x → P₀.Λ.l x = x * x * v) (hP0g : P₀.Λ.g = hlGt v) :
    HoBF v hv1 hv where
  K := hoBPk hv1 hv P₀
  L := fun μ hμ => (hoBPk_inv hv1 hv P₀ hP0L hP0l hP0g μ hμ).1.1
  l := fun μ hμ => (hoBPk_inv hv1 hv P₀ hP0L hP0l hP0g μ hμ).1.2
  glo := fun μ hμ => (hoBPk_inv hv1 hv P₀ hP0L hP0l hP0g μ hμ).2.1.1
  ghi := fun μ hμ => (hoBPk_inv hv1 hv P₀ hP0L hP0l hP0g μ hμ).2.1.2
  gmono := fun _ μ h hμ => ((hoBPk_inv hv1 hv P₀ hP0L hP0l hP0g μ hμ).2.2 _ h).1
  ext := fun _ μ h hμ => ((hoBPk_inv hv1 hv P₀ hP0L hP0l hP0g μ hμ).2.2 _ h).2
  succ := fun μ => hoBPk_succ hv1 hv P₀ μ
  lim := fun _ hl hle => hoBPk_lim_Λ hv1 hv P₀ hP0L hP0l hP0g hl hle
  glt := hoBPk_g_lt hv1 hv P₀ hP0L hP0l hP0g

theorem hoBF_K0 {v : Ordinal.{0}} (hv1 : 1 ≤ v) (hv : v < Om1) (P₀ : HnPk) (hP0L : P₀.Λ.L = Om1 * Om1 * v)
    (hP0l : ∀ x, P₀.Λ.g < x → P₀.Λ.l x = x * x * v) (hP0g : P₀.Λ.g = hlGt v) :
    (hoBF hv1 hv P₀ hP0L hP0l hP0g).K 0 = P₀ := hoBPk_zero hv1 hv P₀

end Googology.Trans.PoR.InaccPsi.R2.Ho
