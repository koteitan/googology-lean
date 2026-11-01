import Googology.Trans.PoR.InaccPsi.R2.XuBase3

/-!
# XuBr: THE (A3) CLASSIFICATION BELOW EVERY `ε`-NUMBER BOUND `B ∈ [t₀, Γ(1))`, WITH NO HYPOTHESIS

A code `c ∈ [t₀, B)` is `e^j·d + r` with `e = guE c ≥ t₀` (`Gl.gl_parts`); its gate is
`max 1 (max (max (xuQE e) (xuQ j)) (max (xuQ d) (xuG r)))` (`xu_gg_cnf`).  One well-founded induction: below `t₀`
the (A3) classification of `Xc.xc_br` (the gates agree, `Xu.xu_cls_of_xc`); above, the prefix, digit and power
transfers of `Xc.xc_pre`, `Xc.xc_dig`, `Xc.xc_pow` over the brackets, and at the `ε`-number codes the bases
`Xu.xu_base`.

* gate lemmas `xu_gg_cnf`, `xu_gg_pre`, `xu_gg_term`, `xu_dig_part`, `xu_log_part`;
* `XuLvC` (the level condition), `xu_br` (**ONE WELL-FOUNDED INDUCTION OVER EVERY CODE BELOW `B`**);
* `xuCls` (**THE (A3) CLASSIFICATION `WsCls (xuC B) B`**, unconditional, for every `ε`-number `B ∈ [t₀, Γ(1))`),
  `xuClsN` (**at every `t_n`**: `WsCls (xuCn n) t_n`).

No new axiom.  New definition: `XuLvC`.
-/

set_option autoImplicit false

open Googology.Trans.PoR.InaccPsi.R2.Wm Googology.Trans.PoR.InaccPsi.R2.Wh Googology.Trans.PoR.InaccPsi.R2.Ho
open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gf
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb
  Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gk
open Googology.Trans.PoR.InaccPsi.R2.Wo Googology.Trans.PoR.InaccPsi.R2.Wn Googology.Trans.PoR.InaccPsi.R2.Ws
  Googology.Trans.PoR.InaccPsi.R2.Wt Googology.Trans.PoR.InaccPsi.R2.Xc Googology.Trans.PoR.InaccPsi.R2.Wx
  Googology.Trans.PoR.InaccPsi.R2.Gv

namespace Googology.Trans.PoR.InaccPsi.R2.Xu

/-! ## Gate lemmas -/

section Gate

variable {e : Ordinal.{0}} (he : InE e) (hte : Wj.wjT 0 ≤ e)
include he hte

theorem xu_gg_cnf {j q t : Ordinal.{0}} (hj : j ≠ 0) (hq0 : q ≠ 0) (hqe : q < e) (ht : t < e ^ j)
    (hv : e ^ j * q + t < eN e) (hB : e ^ j * q + t < gcG 1) :
    xuGg (e ^ j * q + t) = max 1 (max (max (xuQE e) (xuQ j)) (max (xuQ q) (xuG t))) := by
  unfold xuGg; rw [xuG_cnf he hte hj hq0 hqe ht hv hB]

theorem xu_gg_pre {j q t : Ordinal.{0}} (hj : j ≠ 0) (hq0 : q ≠ 0) (hqe : q < e) (ht : t < e ^ j)
    (hv : e ^ j * q + t < eN e) (hB : e ^ j * q + t < gcG 1) :
    xuGg (e ^ j * q + t) = max (max (max (xuQE e) (xuQ j)) (xuQ q)) (xuGg t) := by
  rw [xu_gg_cnf he hte hj hq0 hqe ht hv hB, ws_mx4]; rfl

theorem xu_gg_term {j q : Ordinal.{0}} (hj : j ≠ 0) (hq0 : q ≠ 0) (hqe : q < e) (hv : e ^ j * q < eN e)
    (hB : e ^ j * q < gcG 1) : xuGg (e ^ j * q) = max 1 (max (max (xuQE e) (xuQ j)) (xuQ q)) := by
  have h := xu_gg_cnf (t := 0) he hte hj hq0 hqe (opow_pos _ he.pos) (by rwa [add_zero]) (by rwa [add_zero])
  rw [add_zero, xuG_zero, max_eq_left zero_le] at h
  exact h

theorem xu_gg_pow {j : Ordinal.{0}} (hj : j ≠ 0) (hv : e ^ j < eN e) (hB : e ^ j < gcG 1) :
    xuGg (e ^ j) = max 1 (max (xuQE e) (xuQ j)) := by
  have h := xu_gg_term (q := 1) he hte hj one_ne_zero (Lu.lu_one_lt_E he) (by rwa [mul_one]) (by rwa [mul_one])
  rwa [mul_one, xuQ_one, max_eq_left zero_le] at h

theorem xu_dig_part {j b σ : Ordinal.{0}} (hj : j ≠ 0) (hjb : e ^ j ≤ b)
    (hbe : b < e ^ j * e) (hbN : b < eN e) (hbG : b < gcG 1) (hσ : InE σ) (hgb : xuGg b < σ) :
    xuGg (b / e ^ j) < σ := by
  have hp : e ^ j ≠ 0 := opow_ne_zero _ he.pos.ne'
  have hq0 : b / e ^ j ≠ 0 := ((Ordinal.div_pos hp).2 hjb).ne'
  have hqe : b / e ^ j < e := (Ordinal.div_lt hp).2 hbe
  have hr : b % e ^ j < e ^ j := Ordinal.mod_lt b hp
  have hdec : e ^ j * (b / e ^ j) + b % e ^ j = b := Ordinal.div_add_mod b _
  have hgl := xuG_cnf he hte hj hq0 hqe hr (by rw [hdec]; exact hbN) (by rw [hdec]; exact hbG)
  rw [hdec] at hgl
  refine xu_gg_part hσ ?_ hgb
  rw [hgl]; exact le_max_of_le_right (le_max_left _ _)

theorem xu_log_part {b σ : Ordinal.{0}} (heb : e ≤ b) (hbN : b < eN e)
    (hbG : b < gcG 1) (hσ : InE σ) (hgb : xuGg b < σ) : xuGg (log e b) < σ := by
  obtain ⟨hgu, -⟩ := gl_same he (xu_Om1_lt_t0.trans_le hte) heb hbN
  have hgl := xuG_dec (hte.trans heb) hbG
  rw [hgu] at hgl
  refine xu_gg_part hσ ?_ hgb
  rw [hgl]; exact le_max_of_le_left (le_max_right _ _)

end Gate

/-! ## The induction -/

section Br

variable {B : Ordinal.{0}} (hBE : InE B) (hBt : Wj.wjT 0 ≤ B) (hB1 : B < gcG 1)

/-- **The level condition below `B`**: `Ω₁ < c`, `Ω₁ ∣ c`, not a successor level. -/
def XuLvC (B c : Ordinal.{0}) : Prop :=
  Om1 < c ∧ Om1 ∣ c ∧ ¬ ∃ ℓ', (Om1 ≤ ℓ' ∧ Om1 ∣ ℓ' ∧ ℓ' < B) ∧ c = ℓ' + Om1

include hBE hBt hB1 in
/-- **ONE WELL-FOUNDED INDUCTION OVER EVERY CODE BELOW `B`**: every limit code `c < B` has a sequence of codes,
and a sequence of levels when `c` is a level other than `Ω₁` and not a successor level. -/
theorem xu_br : ∀ c, c < B → IsSuccLimit c →
    XCls (xuC B hBE hBt hB1) (fun _ => True) c ∧ (XuLvC B c → XCls (xuC B hBE hBt hB1) ML c) := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcL hlim
  have hcB1 : c < gcG 1 := hcL.trans hB1
  rcases lt_or_ge c (Wj.wjT 0) with hct | hct
  · obtain ⟨h1, h2⟩ := xc_br c hct hlim
    refine ⟨xu_cls_of_xc hBE hBt hB1 hct h1, fun hlv => xu_cls_of_xc hBE hBt hB1 hct (h2 ?_)⟩
    exact ⟨hlv.1, hlv.2.1, fun ⟨ℓ', hl, he⟩ => hlv.2.2 ⟨ℓ', ⟨hl.1, hl.2.1, hl.2.2.trans_le hBt⟩, he⟩⟩
  have hcE := xu_gfE_le hct
  obtain ⟨hk, hd0, hdE, hr, hdec, hjc, hrc, hdc⟩ := gl_parts hcE
  have hE : InE (guE c) := guE_E c
  have hte : Wj.wjT 0 ≤ guE c := xu_E_ge hct
  have hOe : Om1 < guE c := xu_Om1_lt_t0.trans_le hte
  have hec : guE c ≤ c := gl_E_le hcE
  have hcN : c < eN (guE c) := gl_lt_eN hcE
  set e := guE c with he_def
  set j := log e c with hj_def
  set d := c / e ^ j with hd_def
  set r := c % e ^ j with hr_def
  have he1 : (1 : Ordinal.{0}) < e := Lu.lu_one_lt_E hE
  have hpj : e ^ j ≠ 0 := opow_ne_zero _ hE.pos.ne'
  obtain ⟨-, hOej, hdvj⟩ := ws_E_pow_facts hE hOe hk
  have hMm : ∀ q, 0 < q → ML (e ^ j * q) := fun q hq => ws_ML_mul hE hOe hk hq
  have hlt1 : ∀ y, y ≤ c → y < gcG 1 := fun y hy => hy.trans_lt hcB1
  have hltN : ∀ y, y ≤ c → y < eN e := fun y hy => hy.trans_lt hcN
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
    have hgall : ∀ t, t < r → xuGg (e ^ j * d + t) = max (max (max (xuQE e) (xuQ j)) (xuQ d)) (xuGg t) := by
      intro t ht
      have hlt : e ^ j * d + t ≤ c := by
        conv_rhs => rw [← hdec]
        exact ((add_lt_add_iff_left _).2 ht).le
      exact xu_gg_pre hE hte hk hd0 hdE (ht.trans hr) (hltN _ hlt) (hlt1 _ hlt)
    have hgc : xuGg (e ^ j * d + r) = max (max (max (xuQE e) (xuQ j)) (xuQ d)) (xuGg r) :=
      xu_gg_pre hE hte hk hd0 hdE hr (by rw [hdec]; exact hcN) (by rw [hdec]; exact hcB1)
    have hgx : ∀ x, InE x → xuGg (e ^ j * d + r) < x →
        max (max (xuQE e) (xuQ j)) (xuQ d) < x ∧ xuGg r < x :=
      fun x _ h => by rw [hgc] at h; exact max_lt_iff.1 h
    refine ⟨?_, fun hlv => ?_⟩
    · have := xc_pre (C := xuC B hBE hBt hB1) (M := fun _ => True) IHc hgall hgc.ge hgx (fun _ _ => trivial)
      rwa [hdec] at this
    · have hA : Om1 ∣ e ^ j * d := Dvd.dvd.mul_right hdvj _
      have hAlev : Om1 ≤ e ^ j * d ∧ Om1 ∣ e ^ j * d ∧ e ^ j * d < B :=
        ⟨hOej.le.trans (le_mul_of_one_le_right' (Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 hd0))), hA,
          (le_self_add.trans_lt (by rw [hdec]; exact hcL))⟩
      have hrd : Om1 ∣ r := (Ordinal.dvd_add_iff hA).1 (by rw [hdec]; exact hlv.2.1)
      have hrO : Om1 ≤ r := Ordinal.le_of_dvd hr0 hrd
      have hrne : r ≠ Om1 := fun h => hlv.2.2 ⟨e ^ j * d, hAlev, by rw [← h, hdec]⟩
      have hrlv : XuLvC B r := by
        refine ⟨lt_of_le_of_ne hrO hrne.symm, hrd, fun ⟨ℓ', hl', he'⟩ =>
          hlv.2.2 ⟨e ^ j * d + ℓ', ⟨?_, ?_, ?_⟩, ?_⟩⟩
        · exact hAlev.1.trans le_self_add
        · exact dvd_add hA hl'.2.1
        · exact (lt_add_of_pos_right _ wh_Om1_pos).trans (by rw [add_assoc, ← he', hdec]; exact hcL)
        · rw [add_assoc, ← he', hdec]
      have hML : ∀ t, ML t → ML (e ^ j * d + t) := fun t ht => ⟨ht.1.trans le_add_self, dvd_add hA ht.2⟩
      have := xc_pre (C := xuC B hBE hBt hB1) (M := ML) (IHl hrlv) hgall hgc.ge hgx hML
      rwa [hdec] at this
  -- `r = 0`: `c = e^j·d`
  have hc : c = e ^ j * d := by rw [← hdec, hr0, add_zero]
  suffices hML : XCls (xuC B hBE hBt hB1) ML c from ⟨xcls_mono (fun _ _ => trivial) hML, fun _ => hML⟩
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
          rw [hce]
          refine xu_base hBE hBt hB1 hE hte (hec.trans_lt hcB1) (fun c' hc' hl' => ?_)
          exact (IH c' (hc'.trans_le hec) ((hc'.trans_le hec).trans hcL) hl').1
        · -- `c = e^{j'}·e`: the digit transfer over the base `e`
          have hbase : XCls (xuC B hBE hBt hB1) (fun _ => True) e := by
            refine xcls_mono (fun _ _ => trivial) (xu_base hBE hBt hB1 hE hte (hec.trans_lt hcB1) ?_)
            intro c' hc' hl'
            exact (IH c' (hc'.trans_le hec) ((hc'.trans_le hec).trans hcL) hl').1
          have hce : c = e ^ j' * e := by rw [hcj, ← hj', opow_add, opow_one]
          have hpj' : e ^ j' ≠ 0 := opow_ne_zero _ hE.pos.ne'
          have hcN' : e ^ j' * e ≤ c := hce.ge
          have hgc : xuGg (e ^ j' * e) = max 1 (max (xuQE e) (xuQ j)) := by
            rw [← hce, hcj]; exact xu_gg_pow hE hte hk (hcj ▸ hcN) (hcj ▸ hcB1)
          have hjj : xuQ j' ≤ xuQ j := hj' ▸ xuQ_succ j' (hj' ▸ (hjc.trans hcB1))
          have hge : xuGg e = max 1 (xuQE e) := by
            unfold xuGg; rw [xuG_base hE hte (hec.trans_lt hcB1)]
          have hgq : ∀ q, 0 < q → q < e → xuGg (e ^ j' * q) = max 1 (max (max (xuQE e) (xuQ j')) (xuQ q)) :=
            fun q hq hqe => by
              have hle : e ^ j' * q ≤ c := hcN'.trans' (mul_le_mul_left' hqe.le _)
              exact xu_gg_term hE hte hj'0 hq.ne' hqe (hltN _ hle) (hlt1 _ hle)
          rw [hce]
          refine xc_dig (C := xuC B hBE hBt hB1) hpj' hbase (fun q hq hqe hgq' => ?_) (fun x hx hgx => ?_)
            (fun b σ hσ hjb hbe hgb => ?_) (fun q hq => ws_ML_mul hE hOe hj'0 hq)
          · show xuGg _ ≤ xuGg _
            rw [hgq q hq hqe, hgc]
            have hQ : xuQ q ≤ max 1 (xuQE e) := (xuQ_le_gg q).trans (hgq'.trans hge.le)
            exact max_le (le_max_left _ _) (max_le (max_le (le_max_of_le_right (le_max_left _ _))
              (le_max_of_le_right (le_max_of_le_right hjj)))
              (hQ.trans (max_le (le_max_left _ _) (le_max_of_le_right (le_max_left _ _)))))
          · change xuGg _ < x at hgx
            rw [hgc] at hgx
            obtain ⟨h1, h2⟩ := max_lt_iff.1 hgx
            obtain ⟨h3, h4⟩ := max_lt_iff.1 h2
            refine ⟨by show xuGg _ < x; rw [hge]; exact max_lt h1 h3, fun q hq hqe hgq' => ?_⟩
            show xuGg _ < x
            rw [hgq q hq hqe]
            exact max_lt h1 (max_lt (max_lt h3 (hjj.trans_lt h4)) ((xuQ_le_gg q).trans_lt hgq'))
          · exact xu_dig_part hE hte hj'0 hjb hbe (hbe.trans_le hcN' |>.trans hcN)
              (hbe.trans_le hcN' |>.trans hcB1) hσ hgb
      · -- `c = e^j`, `j` a limit: the power transfer
        have IHj := (IH j hjc (hjc.trans hcL) hjl).1
        have hgp : ∀ j', 1 ≤ j' → j' ≤ j → xuGg (e ^ j') = max 1 (max (xuQE e) (xuQ j')) := fun j' hj1 hjj => by
          have hle : e ^ j' ≤ c := hcj ▸ opow_le_opow_right hE.pos hjj
          exact xu_gg_pow hE hte (zero_lt_one.trans_le hj1).ne' (hltN _ hle) (hlt1 _ hle)
        have hgJ := hgp j (Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 hk)) le_rfl
        rw [hcj]
        refine xc_pow (C := xuC B hBE hBt hB1) he1 IHj (fun j' hj1 hjj hgj => ?_) (fun x hx hgx => ?_)
          (fun b σ hσ heb hbe hgb => xu_log_part hE hte heb (hbe.trans_le hcj.ge |>.trans hcN)
            (hbe.trans_le hcj.ge |>.trans hcB1) hσ hgb)
          (fun j' hj1 => by
            have := ws_ML_mul (q := 1) hE hOe (zero_lt_one.trans_le hj1).ne' zero_lt_one
            rwa [mul_one] at this)
        · show xuGg _ ≤ xuGg _
          rw [hgp j' hj1 hjj.le, hgJ]
          have hQ : xuQ j' ≤ max 1 (xuQ j) := (xuQ_le_gg j').trans (hgj.trans (xu_gg_lim hjl).le)
          exact max_le (le_max_left _ _) (max_le (le_max_of_le_right (le_max_left _ _))
            (hQ.trans (max_le (le_max_left _ _) (le_max_of_le_right (le_max_right _ _)))))
        · change xuGg _ < x at hgx
          rw [hgJ] at hgx
          obtain ⟨h1, h2⟩ := max_lt_iff.1 hgx
          obtain ⟨h3, h4⟩ := max_lt_iff.1 h2
          refine ⟨by show xuGg j < x; rw [xu_gg_lim hjl]; exact max_lt h1 h4, fun j' hj1 hjj hgj => ?_⟩
          show xuGg _ < x
          rw [hgp j' hj1 hjj.le]
          exact max_lt h1 (max_lt h3 ((xuQ_le_gg j').trans_lt hgj))
    · -- `c = e^j·d' + e^j`, `d' ≠ 0`: the prefix transfer over `e^j`
      have hjc' : e ^ j < c := by
        rw [hc, ← hd']
        calc e ^ j = e ^ j * 1 := (mul_one _).symm
        _ < e ^ j * (d' + 1) := mul_lt_mul_of_pos_left
          (Order.lt_add_one_iff.2 (Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 hd'0))) (pos_iff_ne_zero.2 hpj)
      have hjlim : IsSuccLimit (e ^ j) := isSuccLimit_opow_left (ev_isSuccLimit_of_inE hE) hk
      obtain ⟨-, IHl⟩ := IH (e ^ j) hjc' (hjc'.trans hcL) hjlim
      have hce : c = e ^ j * d' + e ^ j := by rw [hc, ← hd', mul_add_one]
      have hd'e : d' < e := (lt_add_one d').trans (hd' ▸ hdE)
      have hgall : ∀ t, t < e ^ j →
          xuGg (e ^ j * d' + t) = max (max (max (xuQE e) (xuQ j)) (xuQ d')) (xuGg t) := by
        intro t ht
        have hlt : e ^ j * d' + t ≤ c := by rw [hce]; exact ((add_lt_add_iff_left _).2 ht).le
        exact xu_gg_pre hE hte hk hd'0 hd'e ht (hltN _ hlt) (hlt1 _ hlt)
      have hgc : xuGg (e ^ j * d' + e ^ j) = max 1 (max (max (xuQE e) (xuQ j)) (xuQ (d' + 1))) := by
        rw [← hce, hc, ← hd']
        exact xu_gg_term hE hte hk (by rw [hd']; exact hd0) (by rw [hd']; exact hdE)
          (by rw [hd', ← hc]; exact hcN) (by rw [hd', ← hc]; exact hcB1)
      have hgj : xuGg (e ^ j) = max 1 (max (xuQE e) (xuQ j)) :=
        xu_gg_pow hE hte hk (hjc'.trans hcN) (hjc'.trans hcB1)
      have hA : Om1 ∣ e ^ j * d' := Dvd.dvd.mul_right hdvj _
      have hML : ∀ t, ML t → ML (e ^ j * d' + t) := fun t ht => ⟨ht.1.trans le_add_self, dvd_add hA ht.2⟩
      have hpowlv : XuLvC B (e ^ j) := by
        refine ⟨hOej, hdvj, fun ⟨ℓ', _, he'⟩ => ?_⟩
        have hlt : ℓ' < e ^ j := by rw [he']; exact lt_add_of_pos_right _ wh_Om1_pos
        exact absurd he' (ws_pow_principal hE hOe hk hlt).ne'
      have hd'1 : d' + 1 < gcG 1 := (hd' ▸ hdE).trans (hec.trans_lt hcB1)
      rw [hce]
      refine xc_pre (C := xuC B hBE hBt hB1) (IHl hpowlv) hgall ?_ (fun x _ hgx => ?_) hML
      · show max _ (xuGg _) ≤ xuGg _
        rw [hgc, hgj]
        exact max_le (max_le (le_max_of_le_right (le_max_left _ _))
          (le_max_of_le_right (le_max_of_le_right (xuQ_succ d' hd'1))))
          (max_le (le_max_left _ _) (le_max_of_le_right (le_max_left _ _)))
      · change xuGg _ < x at hgx
        rw [hgc] at hgx
        obtain ⟨h1, h2⟩ := max_lt_iff.1 hgx
        obtain ⟨h3, h4⟩ := max_lt_iff.1 h2
        refine ⟨max_lt h3 ((xuQ_succ d' hd'1).trans_lt h4), ?_⟩
        show xuGg _ < x; rw [hgj]; exact max_lt h1 h3
  · -- `c = e^j·d`, `d` a limit: the digit transfer
    have hdc : d < c := hdE.trans_le hec
    have IHd := (IH d hdc (hdc.trans hcL) hdl).1
    have hgq : ∀ q, 0 < q → q < e → e ^ j * q ≤ c →
        xuGg (e ^ j * q) = max 1 (max (max (xuQE e) (xuQ j)) (xuQ q)) := fun q hq hqe hqc =>
      xu_gg_term hE hte hk hq.ne' hqe (hltN _ hqc) (hlt1 _ hqc)
    have hgc := hgq d (pos_iff_ne_zero.2 hd0) hdE hc.ge
    have hdc' : ∀ q, q < d → e ^ j * q ≤ c := fun q hq => by
      rw [hc]; exact mul_le_mul_left' hq.le _
    rw [hc]
    refine xc_dig (C := xuC B hBE hBt hB1) hpj IHd (fun q hq hqd hgq' => ?_) (fun x hx hgx => ?_)
      (fun b σ hσ hjb hbd hgb => ?_) hMm
    · show xuGg _ ≤ xuGg _
      have hQ : xuQ q ≤ max 1 (xuQ d) := (xuQ_le_gg q).trans (hgq'.trans (xu_gg_lim hdl).le)
      rw [hgq q hq (hqd.trans hdE) (hdc' q hqd), hgc]
      exact max_le (le_max_left _ _) (max_le (le_max_of_le_right (le_max_left _ _))
        (hQ.trans (max_le (le_max_left _ _) (le_max_of_le_right (le_max_right _ _)))))
    · change xuGg _ < x at hgx
      rw [hgc] at hgx
      obtain ⟨h1, h2⟩ := max_lt_iff.1 hgx
      obtain ⟨h3, h4⟩ := max_lt_iff.1 h2
      refine ⟨by show xuGg d < x; rw [xu_gg_lim hdl]; exact max_lt h1 h4, fun q hq hqd hgq' => ?_⟩
      show xuGg _ < x
      rw [hgq q hq (hqd.trans hdE) (hdc' q hqd)]
      exact max_lt h1 (max_lt h3 ((xuQ_le_gg q).trans_lt hgq'))
    · have hbe : b < e ^ j * e := hbd.trans (mul_lt_mul_of_pos_left hdE (pos_iff_ne_zero.2 hpj))
      have hbc : b < c := by rw [hc]; exact hbd
      exact xu_dig_part hE hte hk hjb hbe (hbc.trans hcN) (hbc.trans hcB1) hσ hgb

/-- **THE (A3) CLASSIFICATION BELOW `B`**, unconditional. -/
theorem xuCls : WsCls (xuC B hBE hBt hB1) B := by
  intro ℓ hℓ hL' h1 h2 h3
  have hlim : IsSuccLimit ℓ := by
    refine Ordinal.isSuccLimit_iff.2 ⟨(wh_Om1_pos.trans_le hℓ.1).ne', isSuccPrelimit_of_succ_lt fun a ha => ?_⟩
    rw [← Ordinal.add_one_eq_succ]; exact WsC.lev_lim hℓ ha
  have hlv : XuLvC B ℓ := ⟨lt_of_le_of_ne hℓ.1 (Ne.symm h1), hℓ.2.1, fun ⟨ℓ', hl, he⟩ => h2 ⟨ℓ', hl, he⟩⟩
  rcases (xu_br hBE hBt hB1 ℓ hL' hlim).2 hlv with ⟨cs, h1', h2', h3', h4', h5'⟩ | ⟨s, hs, hsM⟩
  · exact absurd ⟨cs, h1', h2', h3', fun t ht => h4' (t + 1) (WsC.lev_lim hℓ ht), h5'⟩ h3
  · exact ⟨s, hs, hsM⟩

end Br

/-- **THE (A3) CLASSIFICATION BELOW EVERY `t_n`**, unconditional. -/
theorem xuClsN (n : ℕ) : WsCls (xuCn n) (Wj.wjT n) := xuCls _ _ _

end Googology.Trans.PoR.InaccPsi.R2.Xu
