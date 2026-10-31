import Googology.Trans.PoR.InaccPsi.R2.WsBr

/-!
# WsBrI: THE ONE INDUCTION OF THE (A2) CLASSIFICATION, GIVEN THE `ε`-NUMBER BASES

* gate lemmas of the base-`e` normal form (`ws_gh_cnf`, `ws_gh_pre`, `ws_gh_part`, `ws_glQ_succ`);
* `WsBase L` (**every `ε`-number code `e ∈ [ε_{Ω₁+1}, L)` has an `ω`- or `Ω₁`-sequence of levels**), `WsBaseI L`
  (the same given the sequences of all smaller limit codes), `LvC`;
* `ws_br` (**ONE WELL-FOUNDED INDUCTION**: from `WsBase L`, every limit code `c < L` has a sequence of codes and,
  if it is a level other than `Ω₁` and not a successor level, a sequence of levels);
* `wsCls_of_baseI`, `wsCls_of_base` (**`WsBase L ⇒ WsCls wsA2 L`**: the (A2) classification below `L` reduced to its `ε`-number
  codes).

No new axiom.  New definitions: `WsBase`, `WsBaseI`, `LvC`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ws

open Googology.Trans.PoR.InaccPsi.R2.Wm Googology.Trans.PoR.InaccPsi.R2.Wh Googology.Trans.PoR.InaccPsi.R2.Ho
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
open Googology.Trans.PoR.InaccPsi.R2.Wo Googology.Trans.PoR.InaccPsi.R2.Wn Googology.Trans.PoR.InaccPsi.R2.Wp WsC
open Googology.Trans.PoR.InaccPsi.R2.Gk

/-! ## Gate lemmas -/

theorem ws_mx4 (a b c d : Ordinal.{0}) :
    max 1 (max (max a b) (max c d)) = max (max (max a b) c) (max 1 d) := by
  apply le_antisymm
  · exact max_le (le_max_of_le_right (le_max_left _ _))
      (max_le (le_max_of_le_left (le_max_left _ _))
        (max_le (le_max_of_le_left (le_max_right _ _)) (le_max_of_le_right (le_max_right _ _))))
  · exact max_le (max_le (le_max_of_le_right (le_max_of_le_left le_rfl))
      (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))
      (max_le (le_max_left _ _) (le_max_of_le_right (le_max_of_le_right (le_max_right _ _))))

/-- **The gate of a base-`e` normal form.** -/
theorem ws_gh_cnf {e j q t : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (hj : j ≠ 0) (hq0 : q ≠ 0) (hqe : q < e)
    (ht : t < e ^ j) (hv : e ^ j * q + t < eN e) (hB : e ^ j * q + t < gcG 0) :
    gh (e ^ j * q + t) = max 1 (max (max (glQE e) (glQ j)) (max (glQ q) (glG t))) := by
  unfold gh; rw [glG_cnf he hOe hj hq0 hqe ht hv hB]

/-- **The gate of a prefix plus a rest.** -/
theorem ws_gh_pre {e j q t : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (hj : j ≠ 0) (hq0 : q ≠ 0) (hqe : q < e)
    (ht : t < e ^ j) (hv : e ^ j * q + t < eN e) (hB : e ^ j * q + t < gcG 0) :
    gh (e ^ j * q + t) = max (max (max (glQE e) (glQ j)) (glQ q)) (gh t) := by
  rw [ws_gh_cnf he hOe hj hq0 hqe ht hv hB, ws_mx4]; rfl

/-- **The gate of a pure term `e^j·q`.** -/
theorem ws_gh_term {e j q : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (hj : j ≠ 0) (hq0 : q ≠ 0) (hqe : q < e)
    (hv : e ^ j * q < eN e) (hB : e ^ j * q < gcG 0) :
    gh (e ^ j * q) = max 1 (max (max (glQE e) (glQ j)) (glQ q)) := by
  have h := ws_gh_cnf (t := 0) he hOe hj hq0 hqe (opow_pos _ he.pos) (by rwa [add_zero]) (by rwa [add_zero])
  rw [add_zero, glG_zero, max_eq_left zero_le] at h
  exact h

theorem ws_glQ_succ (a : Ordinal.{0}) : glQ a ≤ glQ (a + 1) := by
  unfold glQ
  by_cases ha : a < ω
  · rw [if_pos ha]; exact zero_le
  · have ha1 : ¬ a + 1 < ω := fun h => ha ((lt_add_one a).trans h)
    rw [if_neg ha, if_neg ha1]; exact glG_le_succ_all a

theorem ws_glQ_le_gh (a : Ordinal.{0}) : glQ a ≤ gh a := (glQ_le a).trans (glG_le_gh a)

/-- **A part with `glQ q ≤ glG b` has `gh q` below every `ε`-number above `gh b`.** -/
theorem ws_gh_part {q b σ : Ordinal.{0}} (hσ : InE σ) (hq : glQ q ≤ glG b) (hb : gh b < σ) : gh q < σ := by
  rw [gh_lt_iff hσ]
  by_cases hqω : q < ω
  · obtain ⟨n, rfl⟩ := lt_omega0.1 hqω
    rw [glG_nat]; exact (natCast_lt_omega0 n).trans (omega0_lt_inE hσ)
  · have : glQ q = glG q := if_neg hqω
    rw [← this]; exact hq.trans_lt ((gh_lt_iff hσ).1 hb)

theorem ws_glQ_lim {d : Ordinal.{0}} (hd : IsSuccLimit d) : glQ d = glG d :=
  if_neg (not_lt.2 (omega0_le_of_isSuccLimit hd))

/-- `gh d = max 1 (glQ d)` for a limit `d`. -/
theorem ws_gh_lim {d : Ordinal.{0}} (hd : IsSuccLimit d) : gh d = max 1 (glQ d) := by
  unfold gh; rw [ws_glQ_lim hd]

/-- **A code in the bracket of `e` with exponent `j`**: its gate bounds the gate of its digit. -/
theorem ws_dig_part {e j b σ : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (hj : j ≠ 0) (hjb : e ^ j ≤ b)
    (hbe : b < e ^ j * e) (hbN : b < eN e) (hbG : b < gcG 0) (hσ : InE σ) (hgb : gh b < σ) :
    gh (b / e ^ j) < σ := by
  have hp : e ^ j ≠ 0 := opow_ne_zero _ he.pos.ne'
  have hq0 : b / e ^ j ≠ 0 := ((Ordinal.div_pos hp).2 hjb).ne'
  have hqe : b / e ^ j < e := (Ordinal.div_lt hp).2 hbe
  have hr : b % e ^ j < e ^ j := Ordinal.mod_lt b hp
  have hdec : e ^ j * (b / e ^ j) + b % e ^ j = b := Ordinal.div_add_mod b _
  have hgl := glG_cnf he hOe hj hq0 hqe hr (by rw [hdec]; exact hbN) (by rw [hdec]; exact hbG)
  rw [hdec] at hgl
  refine ws_gh_part hσ ?_ hgb
  rw [hgl]; exact le_max_of_le_right (le_max_left _ _)

/-- **A code in `[e, eN e)`**: its gate bounds the gate of its exponent. -/
theorem ws_log_part {e b σ : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (heb : e ≤ b) (hbN : b < eN e)
    (hbG : b < gcG 0) (hσ : InE σ) (hgb : gh b < σ) : gh (log e b) < σ := by
  obtain ⟨hgu, hEb⟩ := gl_same he hOe heb hbN
  have hgl := glG_dec hEb hbG
  rw [hgu] at hgl
  refine ws_gh_part hσ ?_ hgb
  rw [hgl]; exact le_max_of_le_left (le_max_right _ _)

/-! ## The bases and the induction -/

/-- **THE `ε`-NUMBER BASES BELOW `L`**: every `ε`-number code `e ∈ [ε_{Ω₁+1}, L)` has a sequence of levels. -/
def WsBase (L : Ordinal.{0}) : Prop := ∀ e, InE e → gfE ≤ e → e < L → BCls ML e

/-- **THE `ε`-NUMBER BASES BELOW `L`, WITH THE INDUCTION HYPOTHESIS**: every `ε`-number code `e ∈ [ε_{Ω₁+1}, L)`
has a sequence of levels once every limit code below `e` has a sequence of codes. -/
def WsBaseI (L : Ordinal.{0}) : Prop :=
  ∀ e, InE e → gfE ≤ e → e < L → (∀ c, c < e → IsSuccLimit c → BCls (fun _ => True) c) → BCls ML e

theorem wsBaseI_of {L : Ordinal.{0}} (h : WsBase L) : WsBaseI L := fun e he hEe heL _ => h e he hEe heL

/-- The level condition: `Ω₁ < c`, `Ω₁ ∣ c`, not a successor level. -/
def LvC (c : Ordinal.{0}) : Prop := Om1 < c ∧ Om1 ∣ c ∧ ¬ ∃ ℓ', WpLev ℓ' ∧ c = ℓ' + Om1

theorem ws_E_pow_facts {e j : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (hj : j ≠ 0) :
    e ≤ e ^ j ∧ Om1 < e ^ j ∧ Om1 ∣ e ^ j := by
  have hle : e ≤ e ^ j :=
    calc e = e ^ (1 : Ordinal.{0}) := (opow_one e).symm
    _ ≤ e ^ j := opow_le_opow_right he.pos (Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 hj))
  refine ⟨hle, hOe.trans_le hle, ?_⟩
  rw [wp_E_opow he hOe j]
  refine wm_Om1_dvd_pow ?_
  exact Order.one_le_iff_pos.2 (mul_pos he.pos (pos_iff_ne_zero.2 hj))

theorem ws_ML_mul {e j q : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (hj : j ≠ 0) (hq : 0 < q) :
    ML (e ^ j * q) := by
  obtain ⟨-, h2, h3⟩ := ws_E_pow_facts he hOe hj
  exact ⟨h2.le.trans (le_mul_of_one_le_right' (Order.one_le_iff_pos.2 hq)), Dvd.dvd.mul_right h3 _⟩

theorem ws_pow_principal {e j a : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (hj : j ≠ 0) (ha : a < e ^ j) :
    a + Om1 < e ^ j := by
  have h := (ws_E_pow_facts he hOe hj).2.1
  rw [gu_pow_eq he] at h ha ⊢
  exact isPrincipal_add_omega0_opow _ ha h

theorem ws_pow_LvC {e j : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (hj : j ≠ 0) : LvC (e ^ j) := by
  obtain ⟨-, h2, h3⟩ := ws_E_pow_facts he hOe hj
  refine ⟨h2, h3, fun ⟨ℓ', _, he'⟩ => ?_⟩
  have hlt : ℓ' < e ^ j := by rw [he']; exact lt_add_of_pos_right _ wh_Om1_pos
  exact absurd he' (ws_pow_principal he hOe hj hlt).ne'

/-- **ONE WELL-FOUNDED INDUCTION**: from the `ε`-number bases below `L ≤ G`, every limit code `c < L` has a
sequence of codes, and a sequence of levels when `c` is a level other than `Ω₁` and not a successor level. -/
theorem ws_br {L : Ordinal.{0}} (hL : L ≤ gcG 0) (hb : WsBaseI L) : ∀ c, c < L → IsSuccLimit c →
    BCls (fun _ => True) c ∧ (LvC c → BCls ML c) := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcL hlim
  have hcG : c < gcG 0 := hcL.trans_le hL
  rcases lt_or_ge c gfE with hcE | hcE
  · -- below `ε_{Ω₁+1}`: the sequences of `R2.Wo` / `R2.Wm`
    refine ⟨?_, fun hlv => ?_⟩
    · by_cases hF : WmExpFs c
      · obtain ⟨es, -, h2, h3, h4, h5⟩ := hF
        refine Or.inl ⟨es, fun _ => trivial, h2, h3, h4, fun k => ?_⟩
        unfold gh; rw [glG_low ((h3 k).trans hcE), glG_low hcE]; exact max_le_max le_rfl (h5 k)
      · obtain ⟨s, hs⟩ := wo_seq_exp c hcE hlim hF
        exact Or.inr ⟨s, wsA2_seq_of_A1 hcE hs, fun _ _ => trivial⟩
    · have hℓ : WmLev c := ⟨hlv.1.le, hlv.2.1, hcE⟩
      have h1 : c ≠ Om1 := hlv.1.ne'
      have h2 : ¬ ∃ ℓ', WmLev ℓ' ∧ c = ℓ' + Om1 := fun ⟨ℓ', hl, he⟩ =>
        hlv.2.2 ⟨ℓ', ⟨hl.1, hl.2.1, hl.2.2.trans gfE_lt_G0⟩, he⟩
      by_cases hF : WmFs c
      · obtain ⟨ls, h1', h2', h3', h4', h5'⟩ := hF
        refine Or.inl ⟨ls, h1', h2', h3', fun t ht => ?_, fun k => ?_⟩
        · obtain ⟨k, hk⟩ := h4' t ht; exact ⟨k, (lt_add_one t).trans hk⟩
        · unfold gh; rw [glG_low ((h3' k).trans hcE), glG_low hcE]; exact max_le_max le_rfl (h5' k)
      · obtain ⟨s, hs1, hs2⟩ := wo_fs1 hℓ h1 h2 hF
        exact Or.inr ⟨s, wsA2_seq_of_A1 hcE hs1, hs2⟩
  -- the base-`e` normal form `c = e^j·d + r`
  obtain ⟨hk, hd0, hdE, hr, hdec, hjc, hrc, hdc⟩ := gl_parts hcE
  have hE : InE (guE c) := guE_E c
  have hOe : Om1 < guE c := gl_Om1_lt_E hcE
  have hEe : gfE ≤ guE c := gl_gfE_le_E hcE
  have hec : guE c ≤ c := gl_E_le hcE
  have hcN : c < eN (guE c) := gl_lt_eN hcE
  set e := guE c with he_def
  set j := log e c with hj_def
  set d := c / e ^ j with hd_def
  set r := c % e ^ j with hr_def
  have he1 : (1 : Ordinal.{0}) < e := Lu.lu_one_lt_E hE
  obtain ⟨hej, hOej, hdvj⟩ := ws_E_pow_facts hE hOe hk
  have hpj : e ^ j ≠ 0 := opow_ne_zero _ hE.pos.ne'
  have hMm : ∀ q, 0 < q → ML (e ^ j * q) := fun q hq => ws_ML_mul hE hOe hk hq
  rcases eq_or_ne r 0 with hr0 | hr0
  swap
  · -- the rest `r ≠ 0`
    have hrlim : IsSuccLimit r := by
      rcases zero_or_succ_or_isSuccLimit r with h | ⟨r', hr'⟩ | h
      · exact absurd h hr0
      · rw [← Ordinal.add_one_eq_succ] at hr'
        exfalso; rw [← hdec, ← hr', ← add_assoc] at hlim; exact not_isSuccLimit_add_one _ hlim
      · exact h
    obtain ⟨IHc, IHl⟩ := IH r hrc (hrc.trans hcL) hrlim
    have hgall : ∀ t, t < r → gh (e ^ j * d + t) = max (max (max (glQE e) (glQ j)) (glQ d)) (gh t) := by
      intro t ht
      have hlt : e ^ j * d + t < c := by
        conv_rhs => rw [← hdec]
        exact (add_lt_add_iff_left _).2 ht
      exact ws_gh_pre hE hOe hk hd0 hdE (ht.trans hr) (hlt.trans hcN) (hlt.trans hcG)
    have hgc : gh (e ^ j * d + r) = max (max (max (glQE e) (glQ j)) (glQ d)) (gh r) :=
      ws_gh_pre hE hOe hk hd0 hdE hr (by rw [hdec]; exact hcN) (by rw [hdec]; exact hcG)
    have hgx : ∀ x, InE x → gh (e ^ j * d + r) < x →
        max (max (glQE e) (glQ j)) (glQ d) < x ∧ gh r < x := fun x _ h => by
      rw [hgc] at h; exact max_lt_iff.1 h
    refine ⟨?_, fun hlv => ?_⟩
    · have := ws_pre (M := fun _ => True) IHc hgall hgc.ge hgx (fun _ _ => trivial)
      rwa [hdec] at this
    · have hA : Om1 ∣ e ^ j * d := Dvd.dvd.mul_right hdvj _
      have hAlev : WpLev (e ^ j * d) :=
        ⟨hOej.le.trans (le_mul_of_one_le_right' (Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 hd0))), hA,
          (le_self_add.trans_lt (by rw [hdec]; exact hcG))⟩
      have hrd : Om1 ∣ r := (Ordinal.dvd_add_iff hA).1 (by rw [hdec]; exact hlv.2.1)
      have hrO : Om1 ≤ r := Ordinal.le_of_dvd hr0 hrd
      have hrne : r ≠ Om1 := fun h => hlv.2.2 ⟨e ^ j * d, hAlev, by rw [← h, hdec]⟩
      have hrlv : LvC r := by
        refine ⟨lt_of_le_of_ne hrO hrne.symm, hrd, fun ⟨ℓ', hl', he'⟩ => hlv.2.2 ⟨e ^ j * d + ℓ', ⟨?_, ?_, ?_⟩, ?_⟩⟩
        · exact hAlev.1.trans le_self_add
        · exact dvd_add hA hl'.2.1
        · exact (lt_add_of_pos_right _ wh_Om1_pos).trans (by rw [add_assoc, ← he', hdec]; exact hcG)
        · rw [add_assoc, ← he', hdec]
      have hML : ∀ t, ML t → ML (e ^ j * d + t) := fun t ht => ⟨ht.1.trans le_add_self, dvd_add hA ht.2⟩
      have := ws_pre (M := ML) (IHl hrlv) hgall hgc.ge hgx hML
      rwa [hdec] at this
  -- `r = 0`: `c = e^j·d`; it suffices to give a sequence of levels
  have hc : c = e ^ j * d := by rw [← hdec, hr0, add_zero]
  suffices hML : BCls ML c from ⟨bcls_mono (fun _ _ => trivial) hML, fun _ => hML⟩
  rcases zero_or_succ_or_isSuccLimit d with hd | ⟨d', hd'⟩ | hdl
  · exact absurd hd hd0
  · rw [← Ordinal.add_one_eq_succ] at hd'
    rcases eq_or_ne d' 0 with hd'0 | hd'0
    · -- `c = e^j`
      rw [hd'0, zero_add] at hd'
      have hcj : c = e ^ j := by rw [hc, ← hd', mul_one]
      rcases zero_or_succ_or_isSuccLimit j with hj0 | ⟨j', hj'⟩ | hjl
      · exact absurd hj0 hk
      · rw [← Ordinal.add_one_eq_succ] at hj'
        rcases eq_or_ne j' 0 with hj'0 | hj'0
        · -- `c = e`: the base
          have hce : c = e := by rw [hcj, ← hj', hj'0, zero_add, opow_one]
          have := hb e hE hEe (hec.trans_lt hcL)
            (fun c' hc' hl' => (IH c' (hc'.trans_le hec) ((hc'.trans_le hec).trans hcL) hl').1)
          rwa [← hce] at this
        · -- `c = e^{j'}·e`: the digit transfer over the base `e`
          have heL : e < L := hec.trans_lt hcL
          have hbase := bcls_mono (fun _ _ => trivial) (hb e hE hEe heL
            (fun c' hc' hl' => (IH c' (hc'.trans_le hec) ((hc'.trans_le hec).trans hcL) hl').1))
          have hce : c = e ^ j' * e := by rw [hcj, ← hj', opow_add, opow_one]
          have hpj' : e ^ j' ≠ 0 := opow_ne_zero _ hE.pos.ne'
          have hcN' : e ^ j' * e < eN e := hce ▸ hcN
          have hcG' : e ^ j' * e < gcG 0 := hce ▸ hcG
          have h0 := ws_gh_term (q := 1) hE hOe hk one_ne_zero he1 (by rw [mul_one, ← hcj]; exact hcN)
            (by rw [mul_one, ← hcj]; exact hcG)
          rw [mul_one] at h0
          have hgc : gh (e ^ j' * e) = max 1 (max (max (glQE e) (glQ j)) (glQ 1)) := by
            rw [← hce, hcj]; exact h0
          have hjj : glQ j' ≤ glQ j := hj' ▸ ws_glQ_succ j'
          have hge : gh e = max 1 (glQE e) := by unfold gh; rw [glG_base hE hOe (hec.trans_lt hcG)]
          have hgq : ∀ q, 0 < q → q < e → gh (e ^ j' * q) = max 1 (max (max (glQE e) (glQ j')) (glQ q)) :=
            fun q hq hqe => ws_gh_term hE hOe hj'0 hq.ne' hqe
              ((mul_lt_mul_of_pos_left hqe (pos_iff_ne_zero.2 hpj')).trans hcN')
              ((mul_lt_mul_of_pos_left hqe (pos_iff_ne_zero.2 hpj')).trans hcG')
          rw [hce]
          refine ws_dig hpj' hbase (fun q hq hqe hgq' => ?_) (fun x hx hgx => ?_)
            (fun b σ hσ hjb hbe hgb => ?_) (fun q hq => ws_ML_mul hE hOe hj'0 hq)
          · rw [hgq q hq hqe, hgc]
            have hQ : glQ q ≤ max 1 (glQE e) := (ws_glQ_le_gh q).trans (hgq'.trans hge.le)
            refine max_le (le_max_left _ _) (max_le (max_le ?_ ?_) ?_)
            · exact le_max_of_le_right (le_max_of_le_left (le_max_left _ _))
            · exact le_max_of_le_right (le_max_of_le_left (le_max_of_le_right hjj))
            · exact hQ.trans (max_le (le_max_left _ _) (le_max_of_le_right (le_max_of_le_left (le_max_left _ _))))
          · rw [hgc] at hgx
            obtain ⟨h1, h2⟩ := max_lt_iff.1 hgx
            obtain ⟨h3, -⟩ := max_lt_iff.1 h2
            obtain ⟨h4, h5⟩ := max_lt_iff.1 h3
            refine ⟨by rw [hge]; exact max_lt h1 h4, fun q hq hqe hgq' => ?_⟩
            rw [hgq q hq hqe]
            refine max_lt h1 (max_lt (max_lt h4 (hjj.trans_lt h5)) ?_)
            exact (ws_glQ_le_gh q).trans_lt hgq'
          · exact ws_dig_part hE hOe hj'0 hjb hbe (hbe.trans hcN') (hbe.trans hcG') hσ hgb
      · -- `c = e^j`, `j` a limit: the power transfer
        have IHj := (IH j hjc (hjc.trans hcL) hjl).1
        have hgp : ∀ j', 1 ≤ j' → e ^ j' < eN e → e ^ j' < gcG 0 →
            gh (e ^ j') = max 1 (max (max (glQE e) (glQ j')) (glQ 1)) := fun j' hj1 hN hG => by
          have hj0 : j' ≠ 0 := (zero_lt_one.trans_le hj1).ne'
          have h := ws_gh_term (q := 1) hE hOe hj0 one_ne_zero he1 (by rwa [mul_one]) (by rwa [mul_one])
          rwa [mul_one] at h
        have hjN : e ^ j < eN e := hcj ▸ hcN
        have hjG : e ^ j < gcG 0 := hcj ▸ hcG
        have hlow : ∀ j', 1 ≤ j' → j' < j → e ^ j' < e ^ j := fun j' _ h => (opow_lt_opow_iff_right he1).2 h
        have hgJ := hgp j (Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 hk)) hjN hjG
        rw [hcj]
        refine ws_pow he1 IHj (fun j' hj1 hjj hgj => ?_) (fun x hx hgx => ?_)
          (fun b σ hσ heb hbe hgb => ws_log_part hE hOe heb (hbe.trans hjN) (hbe.trans hjG) hσ hgb)
          (fun j' hj1 => by
            have := ws_ML_mul (q := 1) hE hOe (zero_lt_one.trans_le hj1).ne' zero_lt_one
            rwa [mul_one] at this)
        · rw [hgp j' hj1 ((hlow j' hj1 hjj).trans hjN) ((hlow j' hj1 hjj).trans hjG), hgJ]
          have hQ : glQ j' ≤ max 1 (glQ j) := (ws_glQ_le_gh j').trans (hgj.trans (ws_gh_lim hjl).le)
          refine max_le (le_max_left _ _) (max_le (max_le (le_max_of_le_right (le_max_of_le_left
            (le_max_left _ _))) (hQ.trans (max_le (le_max_left _ _) ?_))) (le_max_of_le_right
            (le_max_right _ _)))
          exact le_max_of_le_right (le_max_of_le_left (le_max_right _ _))
        · rw [hgJ] at hgx
          obtain ⟨h1, h2⟩ := max_lt_iff.1 hgx
          obtain ⟨h3, h3'⟩ := max_lt_iff.1 h2
          obtain ⟨h4, h5⟩ := max_lt_iff.1 h3
          refine ⟨by rw [ws_gh_lim hjl]; exact max_lt h1 h5, fun j' hj1 hjj hgj => ?_⟩
          rw [hgp j' hj1 ((hlow j' hj1 hjj).trans hjN) ((hlow j' hj1 hjj).trans hjG)]
          exact max_lt h1 (max_lt (max_lt h4 ((ws_glQ_le_gh j').trans_lt hgj)) h3')
    · -- `c = e^j·d' + e^j`, `d' ≠ 0`: the prefix transfer over `e^j`
      have hjc' : e ^ j < c := by
        rw [hc, ← hd']
        calc e ^ j = e ^ j * 1 := (mul_one _).symm
        _ < e ^ j * (d' + 1) := mul_lt_mul_of_pos_left
          (Order.lt_add_one_iff.2 (Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 hd'0))) (pos_iff_ne_zero.2 hpj)
      have hjlim : IsSuccLimit (e ^ j) := by
        exact isSuccLimit_opow_left (ev_isSuccLimit_of_inE hE) hk
      obtain ⟨-, IHl⟩ := IH (e ^ j) hjc' (hjc'.trans hcL) hjlim
      have hce : c = e ^ j * d' + e ^ j := by rw [hc, ← hd', mul_add_one]
      have hd'e : d' < e := (lt_add_one d').trans (hd' ▸ hdE)
      have hgall : ∀ t, t < e ^ j → gh (e ^ j * d' + t) = max (max (max (glQE e) (glQ j)) (glQ d')) (gh t) := by
        intro t ht
        have hlt : e ^ j * d' + t < c := by rw [hce]; exact (add_lt_add_iff_left _).2 ht
        exact ws_gh_pre hE hOe hk hd'0 hd'e ht (hlt.trans hcN) (hlt.trans hcG)
      have hgc : gh (e ^ j * d' + e ^ j) = max 1 (max (max (glQE e) (glQ j)) (glQ (d' + 1))) := by
        rw [← hce, hc, ← hd']
        exact ws_gh_term hE hOe hk (by rw [hd']; exact hd0) (by rw [hd']; exact hdE) (by rw [hd', ← hc]; exact hcN)
          (by rw [hd', ← hc]; exact hcG)
      have hgj : gh (e ^ j) = max 1 (max (max (glQE e) (glQ j)) (glQ 1)) := by
        have h := ws_gh_term (q := 1) hE hOe hk one_ne_zero he1 (by rw [mul_one]; exact hjc'.trans hcN)
          (by rw [mul_one]; exact hjc'.trans hcG)
        rwa [mul_one] at h
      have hA : Om1 ∣ e ^ j * d' := Dvd.dvd.mul_right hdvj _
      have hML : ∀ t, ML t → ML (e ^ j * d' + t) := fun t ht => ⟨ht.1.trans le_add_self, dvd_add hA ht.2⟩
      rw [hce]
      refine ws_pre (IHl (ws_pow_LvC hE hOe hk)) hgall ?_ (fun x _ hgx => ?_) hML
      · rw [hgc, hgj]
        refine max_le (max_le (max_le (le_max_of_le_right (le_max_of_le_left (le_max_left _ _)))
          (le_max_of_le_right (le_max_of_le_left (le_max_right _ _))))
          (le_max_of_le_right (le_max_of_le_right (ws_glQ_succ d')))) ?_
        refine max_le (le_max_left _ _) (max_le (le_max_of_le_right (le_max_left _ _)) ?_)
        rw [glQ_one]; exact zero_le
      · rw [hgc] at hgx
        obtain ⟨h1, h2⟩ := max_lt_iff.1 hgx
        obtain ⟨h3, h4⟩ := max_lt_iff.1 h2
        refine ⟨max_lt h3 ((ws_glQ_succ d').trans_lt h4), ?_⟩
        rw [hgj, glQ_one]; exact max_lt h1 (max_lt h3 (zero_le.trans_lt h1))
  · -- `c = e^j·d`, `d` a limit: the digit transfer
    have IHd := (IH d hdc (hdc.trans hcL) hdl).1
    have hgq : ∀ q, 0 < q → q < e → e ^ j * q ≤ c →
        gh (e ^ j * q) = max 1 (max (max (glQE e) (glQ j)) (glQ q)) := fun q hq hqe hqc =>
      ws_gh_term hE hOe hk hq.ne' hqe (hqc.trans_lt hcN) (hqc.trans_lt hcG)
    have hgc := hgq d (pos_iff_ne_zero.2 hd0) hdE hc.ge
    have hgcc : gh c = max 1 (max (max (glQE e) (glQ j)) (glQ d)) := (congrArg gh hc).trans hgc
    have hdc' : ∀ q, q < d → e ^ j * q ≤ c := fun q hq => by
      rw [hc]; exact mul_le_mul_left' hq.le _
    rw [hc]
    refine ws_dig hpj IHd (fun q hq hqd hgq' => ?_) (fun x hx hgx => ?_)
      (fun b σ hσ hjb hbd hgb => ?_) hMm
    · have hQ : glQ q ≤ max 1 (glQ d) := (ws_glQ_le_gh q).trans (hgq'.trans (ws_gh_lim hdl).le)
      refine (hgq q hq (hqd.trans hdE) (hdc' q hqd)).le.trans (le_trans ?_ hgc.ge)
      exact max_le (le_max_left _ _) (max_le (le_max_of_le_right (le_max_left _ _))
        (hQ.trans (max_le (le_max_left _ _) (le_max_of_le_right (le_max_right _ _)))))
    · have hgx' := hgc.ge.trans_lt hgx
      obtain ⟨h1, h2⟩ := max_lt_iff.1 hgx'
      obtain ⟨h3, h4⟩ := max_lt_iff.1 h2
      refine ⟨by rw [ws_gh_lim hdl]; exact max_lt h1 h4, fun q hq hqd hgq' => ?_⟩
      rw [hgq q hq (hqd.trans hdE) (hdc' q hqd)]
      exact max_lt h1 (max_lt h3 ((ws_glQ_le_gh q).trans_lt hgq'))
    · have hbe : b < e ^ j * e := hbd.trans (mul_lt_mul_of_pos_left hdE (pos_iff_ne_zero.2 hpj))
      have hbc : b < c := by rw [hc]; exact hbd
      exact ws_dig_part hE hOe hk hjb hbe (hbc.trans hcN) (hbc.trans hcG) hσ hgb

/-- **THE (A2) CLASSIFICATION BELOW `L` FROM THE `ε`-NUMBER BASES BELOW `L`** (with the induction hypothesis). -/
theorem wsCls_of_baseI {L : Ordinal.{0}} (hL : L ≤ gcG 0) (hb : WsBaseI L) : WsCls wsA2 L := by
  intro ℓ hℓ hL' h1 h2 h3
  have hlim : IsSuccLimit ℓ := by
    refine Ordinal.isSuccLimit_iff.2 ⟨(wh_Om1_pos.trans_le hℓ.1).ne', isSuccPrelimit_of_succ_lt fun a ha => ?_⟩
    rw [← Ordinal.add_one_eq_succ]; exact lev_lim hℓ ha
  have hlv : LvC ℓ := ⟨lt_of_le_of_ne hℓ.1 (Ne.symm h1), hℓ.2.1, h2⟩
  rcases (ws_br hL hb ℓ hL' hlim).2 hlv with ⟨cs, h1', h2', h3', h4', h5'⟩ | ⟨s, hs, hsM⟩
  · exact absurd ⟨cs, h1', h2', h3', fun t ht => h4' (t + 1) (lev_lim hℓ ht), h5'⟩ h3
  · exact ⟨s, hs, hsM⟩

/-- **THE (A2) CLASSIFICATION BELOW `L` FROM THE `ε`-NUMBER BASES BELOW `L`.** -/
theorem wsCls_of_base {L : Ordinal.{0}} (hL : L ≤ gcG 0) (hb : WsBase L) : WsCls wsA2 L :=
  wsCls_of_baseI hL (wsBaseI_of hb)

end Googology.Trans.PoR.InaccPsi.R2.Ws
