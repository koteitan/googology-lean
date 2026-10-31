import Googology.Trans.PoR.InaccPsi.R2.XcSeq

/-!
# XcBr: THE (A3) CLASSIFICATION BELOW `t₀ = ε_{G+1}` WITH NO HYPOTHESIS

A code `c ∈ [G, t₀)` is `G^j·d + r` (`d < G`, `r < G^j`; `Go.GoD.parts`), and its gate is
`wtD.g c = max (max (hQ j) (Q d)) (wtD.g r)` (`Go.GoD.hG_cnf`).  The only `ε`-number in `[G, t₀)` is `G`, so the
(A3) induction has ONE base, `G` itself, which has the `ω`-sequence `φ^k(glCfn …)` of gate-`0` (A2) codes
(`xc_base_G`).  Below `G` the sequences are those of the (A2) classification (`Ws.ws_br` with `Wx.wx_baseI`).

* gate lemmas `xcg_cnf`, `xg_pre`, `xg_term`, `xc_dig_part`, `xc_log_part`;
* `xc_base_G` (**THE BASE**: `G` has an `ω`-sequence of levels with gates `≤ xg G = 1`);
* `xc_br` (**ONE WELL-FOUNDED INDUCTION OVER EVERY CODE BELOW `t₀`**: every limit code has a sequence of codes, and a
  sequence of levels when it is a level other than `Ω₁` and not a successor level);
* `xcCls` (**THE (A3) CLASSIFICATION `WsCls xcA3 t₀`**, unconditional).

No new axiom.  New definitions: `LvC3`, `xcCf`.
-/

set_option autoImplicit false

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
open Googology.Trans.PoR.InaccPsi.R2.Wo Googology.Trans.PoR.InaccPsi.R2.Wn Googology.Trans.PoR.InaccPsi.R2.Wp
  Googology.Trans.PoR.InaccPsi.R2.Ws Googology.Trans.PoR.InaccPsi.R2.Wt Googology.Trans.PoR.InaccPsi.R2.Wy
  Googology.Trans.PoR.InaccPsi.R2.Wx
  Googology.Trans.PoR.InaccPsi.R2.Xc

namespace Googology.Trans.PoR.InaccPsi.R2.Xc

/-! ## Gate lemmas -/

theorem xc_parts {c : Ordinal.{0}} (hc : gcG 0 ≤ c) (hcN : c < Wj.wjT 0) :
    log (gcG 0) c ≠ 0 ∧ c / gcG 0 ^ log (gcG 0) c ≠ 0 ∧ c / gcG 0 ^ log (gcG 0) c < gcG 0 ∧
      c % gcG 0 ^ log (gcG 0) c < gcG 0 ^ log (gcG 0) c ∧
      gcG 0 ^ log (gcG 0) c * (c / gcG 0 ^ log (gcG 0) c) + c % gcG 0 ^ log (gcG 0) c = c ∧
      log (gcG 0) c < c ∧ c % gcG 0 ^ log (gcG 0) c < c :=
  goGl.parts hc (xc_lt_B hcN)

theorem xcg_cnf {j q t : Ordinal.{0}} (hj : j ≠ 0) (hq0 : q ≠ 0) (hqG : q < gcG 0) (ht : t < gcG 0 ^ j)
    (hv : gcG 0 ^ j * q + t < Wj.wjT 0) :
    wtD.g (gcG 0 ^ j * q + t) = max (max (goGl.hQ j) (goGl.Q q)) (wtD.g t) :=
  goGl.hG_cnf hj hq0 hqG ht (xc_lt_B hv)

theorem xg_pre {j q t : Ordinal.{0}} (hj : j ≠ 0) (hq0 : q ≠ 0) (hqG : q < gcG 0) (ht : t < gcG 0 ^ j)
    (hv : gcG 0 ^ j * q + t < Wj.wjT 0) :
    xg (gcG 0 ^ j * q + t) = max (max (goGl.hQ j) (goGl.Q q)) (xg t) := by
  unfold xg; rw [xcg_cnf hj hq0 hqG ht hv]; exact max_left_comm _ _ _

theorem xg_term {j q : Ordinal.{0}} (hj : j ≠ 0) (hq0 : q ≠ 0) (hqG : q < gcG 0) (hv : gcG 0 ^ j * q < Wj.wjT 0) :
    xg (gcG 0 ^ j * q) = max 1 (max (goGl.hQ j) (goGl.Q q)) := by
  have h := xcg_cnf (t := 0) hj hq0 hqG (opow_pos _ gl_G0_E.pos) (by rwa [add_zero])
  rw [add_zero, show wtD.g 0 = 0 from goGl.hG_zero, max_eq_left zero_le] at h
  unfold xg; rw [h]

theorem xg_small {σ : Ordinal.{0}} (hσ : InE σ) (n : ℕ) : xg (n : Ordinal.{0}) < σ :=
  (xg_lt_iff hσ).2 ((wtD.g_nat n).trans (omega0_lt_inE hσ))

theorem xg_part_Q {q b σ : Ordinal.{0}} (hσ : InE σ) (hqG : q < gcG 0) (hq : goGl.Q q ≤ wtD.g b)
    (hb : xg b < σ) : xg q < σ := by
  by_cases hqω : q < ω
  · obtain ⟨n, rfl⟩ := lt_omega0.1 hqω; exact xg_small hσ n
  · refine (xg_lt_iff hσ).2 ?_
    have e : goGl.Q q = wtD.g q := by rw [goGl.Q_inf (not_lt.1 hqω), xcG_low hqG]; rfl
    rw [← e]; exact hq.trans_lt ((xg_lt_iff hσ).1 hb)

theorem xc_hQ_inf {j : Ordinal.{0}} (hj : ¬ j < ω) : goGl.hQ j = wtD.g j := by
  unfold GoD.hQ; rw [if_neg hj]; rfl

theorem xg_part_hQ {j b σ : Ordinal.{0}} (hσ : InE σ) (h : goGl.hQ j ≤ wtD.g b) (hb : xg b < σ) : xg j < σ := by
  by_cases hjω : j < ω
  · obtain ⟨n, rfl⟩ := lt_omega0.1 hjω; exact xg_small hσ n
  · refine (xg_lt_iff hσ).2 ?_
    rw [← xc_hQ_inf hjω]; exact h.trans_lt ((xg_lt_iff hσ).1 hb)

theorem xc_hQ_succ (j : Ordinal.{0}) : goGl.hQ j ≤ goGl.hQ (j + 1) := by
  unfold GoD.hQ
  by_cases hj : j < ω
  · rw [if_pos hj]; exact zero_le
  · have hj1 : ¬ j + 1 < ω := fun h => hj ((lt_add_one j).trans h)
    rw [if_neg hj, if_neg hj1]; exact goGl.hG_le_succ_all j

theorem xc_hQ_le (j : Ordinal.{0}) : goGl.hQ j ≤ xg j := (goGl.hQ_le j).trans (le_max_right _ _)

theorem xc_Q_le {q : Ordinal.{0}} (hqG : q < gcG 0) : goGl.Q q ≤ xg q := by
  refine le_trans ?_ (le_max_right _ _)
  rw [xcG_low hqG]; exact goGl.Q_le q

/-- `xg j = max 1 (hQ j)` for a limit `j`. -/
theorem xg_lim_hQ {j : Ordinal.{0}} (hj : IsSuccLimit j) : xg j = max 1 (goGl.hQ j) := by
  unfold xg; rw [xc_hQ_inf (not_lt.2 (omega0_le_of_isSuccLimit hj))]

/-- `xg d = max 1 (Q d)` for a limit `d < G`. -/
theorem xg_lim_Q {d : Ordinal.{0}} (hd : IsSuccLimit d) (hdG : d < gcG 0) : xg d = max 1 (goGl.Q d) := by
  unfold xg; rw [goGl.Q_inf (omega0_le_of_isSuccLimit hd), xcG_low hdG]; rfl

/-- **A code in the bracket `[G^j, G^j·G)`**: its gate bounds the gate of its digit. -/
theorem xc_dig_part {j b σ : Ordinal.{0}} (hj : j ≠ 0) (hjb : gcG 0 ^ j ≤ b) (hbe : b < gcG 0 ^ j * gcG 0)
    (hbN : b < Wj.wjT 0) (hσ : InE σ) (hgb : xg b < σ) : xg (b / gcG 0 ^ j) < σ := by
  have hp : gcG 0 ^ j ≠ 0 := opow_ne_zero _ gl_G0_E.pos.ne'
  have hq0 : b / gcG 0 ^ j ≠ 0 := ((Ordinal.div_pos hp).2 hjb).ne'
  have hqe : b / gcG 0 ^ j < gcG 0 := (Ordinal.div_lt hp).2 hbe
  have hr : b % gcG 0 ^ j < gcG 0 ^ j := Ordinal.mod_lt b hp
  have hdec : gcG 0 ^ j * (b / gcG 0 ^ j) + b % gcG 0 ^ j = b := Ordinal.div_add_mod b _
  have hgl := xcg_cnf hj hq0 hqe hr (by rw [hdec]; exact hbN)
  rw [hdec] at hgl
  exact xg_part_Q hσ hqe (by rw [hgl]; exact le_max_of_le_left (le_max_right _ _)) hgb

/-- **A code in `[G, t₀)`**: its gate bounds the gate of its exponent. -/
theorem xc_log_part {b σ : Ordinal.{0}} (hGb : gcG 0 ≤ b) (hbN : b < Wj.wjT 0) (hσ : InE σ) (hgb : xg b < σ) :
    xg (log (gcG 0) b) < σ := by
  refine xg_part_hQ hσ ?_ hgb
  show goGl.hQ _ ≤ goGl.hG b
  rw [goGl.hG_dec hGb (xc_lt_B hbN)]; exact le_max_of_le_left (le_max_left _ _)

/-! ## The base `G` -/

theorem xc_cfn_E : ∀ n k : ℕ, InE (glCfn n k)
  | 0, k => glPsi_E (by exact_mod_cast Nat.succ_pos k) 0
  | n + 1, k => by
    show InE (veblen (glCfn n k) 0)
    have h1 : (1 : Ordinal.{0}) ≤ glCfn n k := (wo_one_lt_inE (xc_cfn_E n k)).le
    exact luP_E h1 (luP_veblen _ 0)

theorem xc_cfn_le_succ (n k : ℕ) : glCfn n k ≤ glCfn (n + 1) k := by
  show glCfn n k ≤ veblen (glCfn n k) 0
  simpa using left_le_veblen (glCfn n k) 0

theorem xc_cfn_mono_n {m n : ℕ} (h : m ≤ n) (k : ℕ) : glCfn m k ≤ glCfn n k := by
  induction n with
  | zero => rw [Nat.le_zero.1 h]
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with hm | hm
    · exact (ih (Nat.lt_succ_iff.1 hm)).trans (xc_cfn_le_succ n k)
    · rw [le_antisymm h hm]

theorem xc_cfn_mono_k (n : ℕ) {k l : ℕ} (h : k ≤ l) : glCfn n k ≤ glCfn n l := by
  induction l with
  | zero => rw [Nat.le_zero.1 h]
  | succ l ih =>
    rcases Nat.lt_or_ge k (l + 1) with hk | hk
    · exact (ih (Nat.lt_succ_iff.1 hk)).trans ((glBn_spec n).2.2.2.2.1 l).2.2.2.le
    · rw [le_antisymm h hk]

/-- **The `ω`-sequence of `G`**: `glCfn k k`. -/
noncomputable def xcCf (k : ℕ) : Ordinal.{0} := glCfn k k

/-- **THE BASE `G`**: an `ω`-sequence of levels (gate-`0` (A2) codes `glCfn k k`), gates `≤ xg G = 1`. -/
theorem xc_base_G : XCls xcA3 ML (gcG 0) := by
  have hO : ∀ k, Om1 < xcCf k := fun k =>
    Om1_lt_eW.trans_le ((glBn_spec k).2.2.2.2.1 k).1
  refine Or.inl ⟨xcCf, fun k => ⟨(hO k).le, wp_Om1_dvd_E (xc_cfn_E k k) (hO k)⟩, fun k => ?_,
    fun k => ((glBn_spec k).2.2.2.2.1 k).2.1.trans (glBn_spec k).1, fun t ht => ?_, fun k => ?_⟩
  · show glCfn k k < glCfn (k + 1) (k + 1)
    exact ((glBn_spec k).2.2.2.2.1 k).2.2.2.trans_le (xc_cfn_le_succ k (k + 1))
  · obtain ⟨n, hn⟩ := glBn_cof ht
    obtain ⟨k, hk⟩ := (glBn_spec n).2.2.2.2.2 t hn
    refine ⟨max n k, hk.trans_le ?_⟩
    exact (xc_cfn_mono_n (le_max_left n k) k).trans (xc_cfn_mono_k _ (le_max_right n k))
  · show xg (glCfn k k) ≤ xg (gcG 0)
    have hlt : glCfn k k < gcG 0 := ((glBn_spec k).2.2.2.2.1 k).2.1.trans (glBn_spec k).1
    unfold xg
    rw [xcG_low hlt, ((glBn_spec k).2.2.2.2.1 k).2.2.1, wtD_gG]

/-! ## The induction -/

/-- **The level condition for `xcA3`**: `Ω₁ < c`, `Ω₁ ∣ c`, not a successor level. -/
def LvC3 (c : Ordinal.{0}) : Prop := Om1 < c ∧ Om1 ∣ c ∧ ¬ ∃ ℓ', xcA3.Lev ℓ' ∧ c = ℓ' + Om1

theorem lvC_of_3 {c : Ordinal.{0}} (hcG : c < gcG 0) (h : LvC3 c) : LvC c :=
  ⟨h.1, h.2.1, fun ⟨ℓ', hl, he⟩ => h.2.2 ⟨ℓ', ⟨hl.1, hl.2.1, hl.2.2.trans xc_G_lt_t0⟩, he⟩⟩

theorem xc_ML_mul {j q : Ordinal.{0}} (hj : j ≠ 0) (hq : 0 < q) : ML (gcG 0 ^ j * q) :=
  ⟨(xc_Om1_lt_pow hj).le.trans (le_mul_of_one_le_right' (Order.one_le_iff_pos.2 hq)),
    Dvd.dvd.mul_right (xc_Om1_dvd_pow hj) _⟩

theorem xc_pow_LvC3 {j : Ordinal.{0}} (hj : j ≠ 0) : LvC3 (gcG 0 ^ j) := by
  refine ⟨xc_Om1_lt_pow hj, xc_Om1_dvd_pow hj, fun ⟨ℓ', _, he⟩ => ?_⟩
  have hlt : ℓ' < gcG 0 ^ j := by rw [he]; exact lt_add_of_pos_right _ wh_Om1_pos
  exact absurd he (goGl.pow_indec ℓ' Om1 hlt (xc_Om1_lt_pow hj)).ne'

/-- **ONE WELL-FOUNDED INDUCTION OVER EVERY CODE BELOW `t₀`**: every limit code `c < t₀` has a sequence of codes,
and a sequence of levels when `c` is a level other than `Ω₁` and not a successor level. -/
theorem xc_br : ∀ c, c < Wj.wjT 0 → IsSuccLimit c →
    XCls xcA3 (fun _ => True) c ∧ (LvC3 c → XCls xcA3 ML c) := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcL hlim
  rcases lt_or_ge c (gcG 0) with hcG | hcG
  · obtain ⟨h1, h2⟩ := ws_br le_rfl wx_baseI c hcG hlim
    exact ⟨xcls_of_A2 hcG h1, fun hlv => xcls_of_A2 hcG (h2 (lvC_of_3 hcG hlv))⟩
  obtain ⟨hk, hd0, hdE, hr, hdec, hjc, hrc⟩ := xc_parts hcG hcL
  set j := log (gcG 0) c with hj_def
  set d := c / gcG 0 ^ j with hd_def
  set r := c % gcG 0 ^ j with hr_def
  have he1 : (1 : Ordinal.{0}) < gcG 0 := wo_one_lt_inE gl_G0_E
  have hpj : gcG 0 ^ j ≠ 0 := opow_ne_zero _ gl_G0_E.pos.ne'
  have hdvj : Om1 ∣ gcG 0 ^ j := xc_Om1_dvd_pow hk
  have hOej : Om1 < gcG 0 ^ j := xc_Om1_lt_pow hk
  have hMm : ∀ q, 0 < q → ML (gcG 0 ^ j * q) := fun q hq => xc_ML_mul hk hq
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
    have hgall : ∀ t, t < r → xg (gcG 0 ^ j * d + t) = max (max (goGl.hQ j) (goGl.Q d)) (xg t) := by
      intro t ht
      have hlt : gcG 0 ^ j * d + t < c := by
        conv_rhs => rw [← hdec]
        exact (add_lt_add_iff_left _).2 ht
      exact xg_pre hk hd0 hdE (ht.trans hr) (hlt.trans hcL)
    have hgc : xg (gcG 0 ^ j * d + r) = max (max (goGl.hQ j) (goGl.Q d)) (xg r) :=
      xg_pre hk hd0 hdE hr (by rw [hdec]; exact hcL)
    have hgx : ∀ x, InE x → xg (gcG 0 ^ j * d + r) < x → max (goGl.hQ j) (goGl.Q d) < x ∧ xg r < x :=
      fun x _ h => by rw [hgc] at h; exact max_lt_iff.1 h
    refine ⟨?_, fun hlv => ?_⟩
    · have := xc_pre (C := xcA3) (M := fun _ => True) IHc hgall hgc.ge hgx (fun _ _ => trivial)
      rwa [hdec] at this
    · have hA : Om1 ∣ gcG 0 ^ j * d := Dvd.dvd.mul_right hdvj _
      have hAlev : xcA3.Lev (gcG 0 ^ j * d) :=
        ⟨hOej.le.trans (le_mul_of_one_le_right' (Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 hd0))), hA,
          (le_self_add.trans_lt (by rw [hdec]; exact hcL))⟩
      have hrd : Om1 ∣ r := (Ordinal.dvd_add_iff hA).1 (by rw [hdec]; exact hlv.2.1)
      have hrO : Om1 ≤ r := Ordinal.le_of_dvd hr0 hrd
      have hrne : r ≠ Om1 := fun h => hlv.2.2 ⟨gcG 0 ^ j * d, hAlev, by rw [← h, hdec]⟩
      have hrlv : LvC3 r := by
        refine ⟨lt_of_le_of_ne hrO hrne.symm, hrd, fun ⟨ℓ', hl', he'⟩ =>
          hlv.2.2 ⟨gcG 0 ^ j * d + ℓ', ⟨?_, ?_, ?_⟩, ?_⟩⟩
        · exact hAlev.1.trans le_self_add
        · exact dvd_add hA hl'.2.1
        · exact (lt_add_of_pos_right _ wh_Om1_pos).trans (by rw [add_assoc, ← he', hdec]; exact hcL)
        · rw [add_assoc, ← he', hdec]
      have hML : ∀ t, ML t → ML (gcG 0 ^ j * d + t) := fun t ht => ⟨ht.1.trans le_add_self, dvd_add hA ht.2⟩
      have := xc_pre (C := xcA3) (M := ML) (IHl hrlv) hgall hgc.ge hgx hML
      rwa [hdec] at this
  -- `r = 0`: `c = G^j·d`
  have hc : c = gcG 0 ^ j * d := by rw [← hdec, hr0, add_zero]
  suffices hML : XCls xcA3 ML c from ⟨xcls_mono (fun _ _ => trivial) hML, fun _ => hML⟩
  rcases zero_or_succ_or_isSuccLimit d with hd | ⟨d', hd'⟩ | hdl
  · exact absurd hd hd0
  · rw [← Ordinal.add_one_eq_succ] at hd'
    rcases eq_or_ne d' 0 with hd'0 | hd'0
    · -- `c = G^j`
      rw [hd'0, zero_add] at hd'
      have hcj : c = gcG 0 ^ j := by rw [hc, ← hd', mul_one]
      rcases zero_or_succ_or_isSuccLimit j with hj0 | ⟨j', hj'⟩ | hjl
      · exact absurd hj0 hk
      · rw [← Ordinal.add_one_eq_succ] at hj'
        rcases eq_or_ne j' 0 with hj'0 | hj'0
        · -- `c = G`: the base
          have hce : c = gcG 0 := by rw [hcj, ← hj', hj'0, zero_add, opow_one]
          rw [hce]; exact xc_base_G
        · -- `c = G^{j'}·G`: the digit transfer over the base `G`
          have hbase := xcls_mono (fun _ _ => trivial) xc_base_G
          have hce : c = gcG 0 ^ j' * gcG 0 := by rw [hcj, ← hj', opow_add, opow_one]
          have hpj' : gcG 0 ^ j' ≠ 0 := opow_ne_zero _ gl_G0_E.pos.ne'
          have hcN' : gcG 0 ^ j' * gcG 0 < Wj.wjT 0 := hce ▸ hcL
          have hgc : xg (gcG 0 ^ j' * gcG 0) = max 1 (goGl.hQ j) := by
            rw [← hce, hcj]
            have h := xg_term (q := 1) hk one_ne_zero he1 (by rw [mul_one, ← hcj]; exact hcL)
            rwa [mul_one, goGl.Q_one, max_eq_left zero_le] at h
          have hjj : goGl.hQ j' ≤ goGl.hQ j := hj' ▸ xc_hQ_succ j'
          have hge : xg (gcG 0) = 1 := by unfold xg; rw [wtD_gG, max_eq_left zero_le]
          have hgq : ∀ q, 0 < q → q < gcG 0 → xg (gcG 0 ^ j' * q) = max 1 (max (goGl.hQ j') (goGl.Q q)) :=
            fun q hq hqe => xg_term hj'0 hq.ne' hqe
              ((mul_lt_mul_of_pos_left hqe (pos_iff_ne_zero.2 hpj')).trans hcN')
          rw [hce]
          refine xc_dig (C := xcA3) hpj' hbase (fun q hq hqe hgq' => ?_) (fun x hx hgx => ?_)
            (fun b σ hσ hjb hbe hgb => ?_) (fun q hq => xc_ML_mul hj'0 hq)
          · show xg _ ≤ xg _
            rw [hgq q hq hqe, hgc]
            have hQ : goGl.Q q ≤ 1 := (xc_Q_le hqe).trans (hgq'.trans hge.le)
            exact max_le (le_max_left _ _) (max_le (le_max_of_le_right hjj) (hQ.trans (le_max_left _ _)))
          · change xg _ < x at hgx
            rw [hgc] at hgx
            obtain ⟨h1, h2⟩ := max_lt_iff.1 hgx
            refine ⟨by show xg _ < x; rw [hge]; exact h1, fun q hq hqe hgq' => ?_⟩
            show xg _ < x
            rw [hgq q hq hqe]
            exact max_lt h1 (max_lt (hjj.trans_lt h2) ((xc_Q_le hqe).trans_lt hgq'))
          · exact xc_dig_part hj'0 hjb hbe (hbe.trans hcN') hσ hgb
      · -- `c = G^j`, `j` a limit: the power transfer
        have IHj := (IH j hjc (hjc.trans hcL) hjl).1
        have hgp : ∀ j', 1 ≤ j' → gcG 0 ^ j' < Wj.wjT 0 → xg (gcG 0 ^ j') = max 1 (goGl.hQ j') :=
          fun j' hj1 hN => by
            have hj0 : j' ≠ 0 := (zero_lt_one.trans_le hj1).ne'
            have h := xg_term (q := 1) hj0 one_ne_zero he1 (by rwa [mul_one])
            rwa [mul_one, goGl.Q_one, max_eq_left zero_le] at h
        have hjN : gcG 0 ^ j < Wj.wjT 0 := hcj ▸ hcL
        have hlow : ∀ j', j' < j → gcG 0 ^ j' < gcG 0 ^ j := fun j' h => (opow_lt_opow_iff_right he1).2 h
        have hgJ := hgp j (Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 hk)) hjN
        rw [hcj]
        refine xc_pow (C := xcA3) he1 IHj (fun j' hj1 hjj hgj => ?_) (fun x hx hgx => ?_)
          (fun b σ hσ heb hbe hgb => xc_log_part heb (hbe.trans hjN) hσ hgb)
          (fun j' hj1 => by
            have := xc_ML_mul (q := 1) (zero_lt_one.trans_le hj1).ne' zero_lt_one
            rwa [mul_one] at this)
        · show xg _ ≤ xg _
          rw [hgp j' hj1 ((hlow j' hjj).trans hjN), hgJ]
          have hQ : goGl.hQ j' ≤ max 1 (goGl.hQ j) := (xc_hQ_le j').trans (hgj.trans (xg_lim_hQ hjl).le)
          exact max_le (le_max_left _ _) hQ
        · change xg _ < x at hgx
          rw [hgJ] at hgx
          obtain ⟨h1, h2⟩ := max_lt_iff.1 hgx
          refine ⟨by show xg j < x; rw [xg_lim_hQ hjl]; exact max_lt h1 h2, fun j' hj1 hjj hgj => ?_⟩
          show xg _ < x
          rw [hgp j' hj1 ((hlow j' hjj).trans hjN)]
          exact max_lt h1 ((xc_hQ_le j').trans_lt hgj)
    · -- `c = G^j·d' + G^j`, `d' ≠ 0`: the prefix transfer over `G^j`
      have hjc' : gcG 0 ^ j < c := by
        rw [hc, ← hd']
        calc gcG 0 ^ j = gcG 0 ^ j * 1 := (mul_one _).symm
        _ < gcG 0 ^ j * (d' + 1) := mul_lt_mul_of_pos_left
          (Order.lt_add_one_iff.2 (Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 hd'0))) (pos_iff_ne_zero.2 hpj)
      have hjlim : IsSuccLimit (gcG 0 ^ j) := isSuccLimit_opow_left (ev_isSuccLimit_of_inE gl_G0_E) hk
      obtain ⟨-, IHl⟩ := IH (gcG 0 ^ j) hjc' (hjc'.trans hcL) hjlim
      have hce : c = gcG 0 ^ j * d' + gcG 0 ^ j := by rw [hc, ← hd', mul_add_one]
      have hd'e : d' < gcG 0 := (lt_add_one d').trans (hd' ▸ hdE)
      have hgall : ∀ t, t < gcG 0 ^ j →
          xg (gcG 0 ^ j * d' + t) = max (max (goGl.hQ j) (goGl.Q d')) (xg t) := by
        intro t ht
        have hlt : gcG 0 ^ j * d' + t < c := by rw [hce]; exact (add_lt_add_iff_left _).2 ht
        exact xg_pre hk hd'0 hd'e ht (hlt.trans hcL)
      have hgc : xg (gcG 0 ^ j * d' + gcG 0 ^ j) = max 1 (max (goGl.hQ j) (goGl.Q (d' + 1))) := by
        rw [← hce, hc, ← hd']
        exact xg_term hk (by rw [hd']; exact hd0) (by rw [hd']; exact hdE) (by rw [hd', ← hc]; exact hcL)
      have hgj : xg (gcG 0 ^ j) = max 1 (goGl.hQ j) := by
        have h := xg_term (q := 1) hk one_ne_zero he1 (by rw [mul_one]; exact hjc'.trans hcL)
        rwa [mul_one, goGl.Q_one, max_eq_left zero_le] at h
      have hA : Om1 ∣ gcG 0 ^ j * d' := Dvd.dvd.mul_right hdvj _
      have hML : ∀ t, ML t → ML (gcG 0 ^ j * d' + t) := fun t ht => ⟨ht.1.trans le_add_self, dvd_add hA ht.2⟩
      rw [hce]
      refine xc_pre (C := xcA3) (IHl (xc_pow_LvC3 hk)) hgall ?_ (fun x _ hgx => ?_) hML
      · show max _ (xg _) ≤ xg _
        rw [hgc, hgj]
        exact max_le (max_le (le_max_of_le_right (le_max_left _ _))
          (le_max_of_le_right (le_max_of_le_right (goGl.Q_le_succ d'))))
          (max_le (le_max_left _ _) (le_max_of_le_right (le_max_left _ _)))
      · change xg _ < x at hgx
        rw [hgc] at hgx
        obtain ⟨h1, h2⟩ := max_lt_iff.1 hgx
        obtain ⟨h3, h4⟩ := max_lt_iff.1 h2
        refine ⟨max_lt h3 ((goGl.Q_le_succ d').trans_lt h4), ?_⟩
        show xg _ < x; rw [hgj]; exact max_lt h1 h3
  · -- `c = G^j·d`, `d` a limit: the digit transfer
    have hdc : d < c := hdE.trans_le hcG
    have IHd := (IH d hdc (hdc.trans hcL) hdl).1
    have hgq : ∀ q, 0 < q → q < gcG 0 → gcG 0 ^ j * q ≤ c →
        xg (gcG 0 ^ j * q) = max 1 (max (goGl.hQ j) (goGl.Q q)) := fun q hq hqe hqc =>
      xg_term hk hq.ne' hqe (hqc.trans_lt hcL)
    have hgc := hgq d (pos_iff_ne_zero.2 hd0) hdE hc.ge
    have hdc' : ∀ q, q < d → gcG 0 ^ j * q ≤ c := fun q hq => by
      rw [hc]; exact mul_le_mul_left' hq.le _
    rw [hc]
    refine xc_dig (C := xcA3) hpj IHd (fun q hq hqd hgq' => ?_) (fun x hx hgx => ?_)
      (fun b σ hσ hjb hbd hgb => ?_) hMm
    · show xg _ ≤ xg _
      have hQ : goGl.Q q ≤ max 1 (goGl.Q d) :=
        (xc_Q_le (hqd.trans hdE)).trans (hgq'.trans (xg_lim_Q hdl hdE).le)
      rw [hgq q hq (hqd.trans hdE) (hdc' q hqd), hgc]
      exact max_le (le_max_left _ _) (max_le (le_max_of_le_right (le_max_left _ _))
        (hQ.trans (max_le (le_max_left _ _) (le_max_of_le_right (le_max_right _ _)))))
    · change xg _ < x at hgx
      rw [hgc] at hgx
      obtain ⟨h1, h2⟩ := max_lt_iff.1 hgx
      obtain ⟨h3, h4⟩ := max_lt_iff.1 h2
      refine ⟨by show xg d < x; rw [xg_lim_Q hdl hdE]; exact max_lt h1 h4, fun q hq hqd hgq' => ?_⟩
      show xg _ < x
      rw [hgq q hq (hqd.trans hdE) (hdc' q hqd)]
      exact max_lt h1 (max_lt h3 ((xc_Q_le (hqd.trans hdE)).trans_lt hgq'))
    · have hbe : b < gcG 0 ^ j * gcG 0 := hbd.trans (mul_lt_mul_of_pos_left hdE (pos_iff_ne_zero.2 hpj))
      have hbc : b < c := by rw [hc]; exact hbd
      exact xc_dig_part hk hjb hbe (hbc.trans hcL) hσ hgb

/-- **THE (A3) CLASSIFICATION BELOW `t₀`**, unconditional. -/
theorem xcCls : WsCls xcA3 (Wj.wjT 0) := by
  intro ℓ hℓ hL' h1 h2 h3
  have hlim : IsSuccLimit ℓ := by
    refine Ordinal.isSuccLimit_iff.2 ⟨(wh_Om1_pos.trans_le hℓ.1).ne', isSuccPrelimit_of_succ_lt fun a ha => ?_⟩
    rw [← Ordinal.add_one_eq_succ]; exact WsC.lev_lim hℓ ha
  have hlv : LvC3 ℓ := ⟨lt_of_le_of_ne hℓ.1 (Ne.symm h1), hℓ.2.1, h2⟩
  rcases (xc_br ℓ hL' hlim).2 hlv with ⟨cs, h1', h2', h3', h4', h5'⟩ | ⟨s, hs, hsM⟩
  · exact absurd ⟨cs, h1', h2', h3', fun t ht => h4' (t + 1) (WsC.lev_lim hℓ ht), h5'⟩ h3
  · exact ⟨s, hs, hsM⟩

end Googology.Trans.PoR.InaccPsi.R2.Xc
