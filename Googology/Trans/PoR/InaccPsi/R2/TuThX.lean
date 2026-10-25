import Googology.Trans.PoR.InaccPsi.R2.TuRoad

/-!
# The image `Θ̂_L` on the exponents below `W^{Ω₂}`: normal form, sums, bounds, divisibility, monotonicity

`Θ = gxTh ρ_λ (ldAtR λ)`, `Θ̂_L = Td.tdThL`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `log_W = Sg.sgLW`, `H_λ = cdHull S λ`.
Every `x ∈ H_λ`, `0 < x < W^{Ω₂}`, is `W^g·d + r` with `g = log_W x < Ω₂`, `d = x / W^g < Ω₂`, `r = x mod W^g`.

* `tuThL_code` (`Θ̂_L e = Θ e` for `e < Ω₂`), `tuSgLW_lt` (`log_W x < x`, `log_W x < Ω₂`), `tuThX_cnf`
  (`Θ̂_L x = Ω^{Θ g}·Θ d + Θ̂_L r`);
* `tuThX_bound` (**`x < W^f` gives `Θ̂_L x < Ω^{Θ f}`** for a code `f < Ω₂`), `tuThX_lt` (**`Θ̂_L` is strictly
  increasing on `H_λ ∩ W^{Ω₂}`**);
* `tuThX_add` (**`Θ̂_L(e + y) = Θ̂_L e + Θ̂_L y` when `W^{log_W y + 1} ∣ e`**), `tuThX_term`
  (`Θ̂_L(W^f·c) = Ω^{Θ f}·Θ c`), `tuThX_dvd` (**`W^f ∣ e` gives `Ω^{Θ f} ∣ Θ̂_L e`**).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tu

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sq
  Googology.Trans.PoR.InaccPsi.R2.Sj Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Ta
  Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tg Googology.Trans.PoR.InaccPsi.R2.Tj
  Googology.Trans.PoR.InaccPsi.R2.Tn

variable {S : InaccSeq.{0}}

/-- `W^{a+b} = W^a·W^b`. -/
theorem tuWe_add (a b : Ordinal.{0}) : leWe (a + b) = leWe a * leWe b := by
  unfold leWe; rw [mul_add, opow_add]

/-- **`log_W x < x` and `log_W x < Ω₂`** for `0 < x < W^{Ω₂}`. -/
theorem tuSgLW_lt {x : Ordinal.{0}} (h0 : 0 < x) (hx : x < leWe (Om (1 + 1))) :
    sgLW x < x ∧ sgLW x < Om (1 + 1) := by
  have hW : sgLW x < Om (1 + 1) := by
    by_contra hc; push Not at hc
    exact absurd ((leWe_mono hc).trans (sgLW_le h0)) (not_le.2 hx)
  refine ⟨?_, hW⟩
  rcases lt_or_ge x (Om (1 + 1)) with hxW | hxW
  · have hs : sgLW x = 0 := by
      unfold sgLW; exact Ordinal.div_eq_zero_of_lt ((Ordinal.log_le_self _ _).trans_lt hxW)
    rw [hs]; exact h0
  · exact hW.trans_le hxW

/-- `log_W (W^f·c) = f`, `(W^f·c)/W^f = c`, `(W^f·c) mod W^f = 0` for `1 ≤ c < Ω₂`. -/
theorem tuSgLW_term {f c : Ordinal.{0}} (hc1 : 1 ≤ c) (hcW : c < Om (1 + 1)) :
    sgLW (leWe f * c) = f ∧ leWe f * c / leWe f = c ∧ leWe f * c % leWe f = 0 := by
  have hW0 : leWe f ≠ 0 := (leWe_pos f).ne'
  refine ⟨?_, Ordinal.mul_div_cancel _ hW0, by
    have h := Ordinal.mul_add_mod_self (leWe f) c 0; rwa [add_zero, Ordinal.zero_mod] at h⟩
  have h1 : leWe f ≤ leWe f * c := (mul_one _).symm.le.trans (mul_le_mul_left' hc1 _)
  have h2 : leWe f * c < leWe (f + 1) := by
    rw [leWe_succ]; exact mul_lt_mul_of_pos_left hcW (leWe_pos f)
  obtain ⟨a1, a2⟩ := sjLogW h1 h2
  exact le_antisymm (Order.lt_add_one_iff.1 a2) a1

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`Θ̂_L e = Θ e` for `e < Ω₂`.** -/
theorem tuThL_code {e : Ordinal.{0}} (heW : e < Om (1 + 1)) : tdThL S l e = gxTh (upsilon l) (ldAtR S l) e := by
  rcases eq_or_ne e 0 with rfl | he0
  · rw [tjThL_zero, gxTh_zero]
  exact tuThL_small (gg_one_lt_of_SC (leRho hl hX).1).le (pos_iff_ne_zero.2 he0) heW

/-- **The normal form of `Θ̂_L x`** for `x ∈ H_λ`, `0 < x < W^{Ω₂}`. -/
theorem tuThX_cnf {x : Ordinal.{0}} (hxH : x ∈ cdHull S l) (h0 : 0 < x) (hx : x < leWe (Om (1 + 1))) :
    tdThL S l x = leOe (gxTh (upsilon l) (ldAtR S l) (sgLW x)) * gxTh (upsilon l) (ldAtR S l) (x / leWe (sgLW x)) +
      tdThL S l (x % leWe (sgLW x)) := by
  obtain ⟨hs, hsW⟩ := tuSgLW_lt h0 hx
  have h1ρ : (1 : Ordinal.{0}) ≤ upsilon l := (gg_one_lt_of_SC (leRho hl hX).1).le
  have hrH : x % leWe (sgLW x) ∈ cdHull S l := leModP_mem (Om (1 + 1) * sgLW x) hxH
  have hxG : x < veblen (Om (1 + 1)) 1 := hx.trans tuWW_G.1
  have hrG : x % leWe (sgLW x) < veblen (Om (1 + 1)) 1 :=
    ((Ordinal.mod_lt _ (leWe_pos _).ne').trans_le (sgLW_le h0)).trans hxG
  rw [tjThL_cnf h1ρ ⟨h0, hs⟩ (tgTm_spec hl hX _ hrH hrG).1, tuThL_code hl hX hsW]

/-- The parts of `x ∈ H_λ`, `0 < x < W^{Ω₂}`: `g = log_W x`, `d = x / W^g` are codes below `Ω₂`, `1 ≤ d`, and
`r = x mod W^g ∈ H_λ`, `r < W^g`. -/
theorem tuParts {x : Ordinal.{0}} (hxH : x ∈ cdHull S l) (h0 : 0 < x) (hx : x < leWe (Om (1 + 1))) :
    GxCl (upsilon l) (ldAtR S l) (sgLW x) ∧ sgLW x < Om (1 + 1) ∧
      GxCl (upsilon l) (ldAtR S l) (x / leWe (sgLW x)) ∧ 1 ≤ x / leWe (sgLW x) ∧ x / leWe (sgLW x) < Om (1 + 1) ∧
      x % leWe (sgLW x) ∈ cdHull S l ∧ x % leWe (sgLW x) < leWe (sgLW x) ∧
      x = leWe (sgLW x) * (x / leWe (sgLW x)) + x % leWe (sgLW x) := by
  obtain ⟨-, hsW⟩ := tuSgLW_lt h0 hx
  set g := sgLW x with hg
  have hW0 : leWe g ≠ 0 := (leWe_pos g).ne'
  have hWe : leWe g ≤ x := sgLW_le h0
  have hgH : g ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hxH)
  have hE2 : x < leWe g * Om (1 + 1) := by rw [← leWe_succ]; exact sgLW_lt x
  have hqW : x / leWe g < Om (1 + 1) := (Ordinal.lt_mul_iff_div_lt hW0).1 hE2
  have hqH : x / leWe g ∈ cdHull S l := by
    refine leDivOp_mem (K := Om (1 + 1) * g) (dvd_mul_right _ _) hxH ?_
    have : leWe (g + 1) = ω ^ (Om (1 + 1) * g + Om (1 + 1)) := by unfold leWe; rw [mul_add_one]
    rw [← this]; exact sgLW_lt x
  exact ⟨(ldHull_iff hl hX hsW).1 hgH, hsW, (ldHull_iff hl hX hqW).1 hqH,
    Order.one_le_iff_pos.2 ((Ordinal.div_pos hW0).2 hWe), hqW, leModP_mem (Om (1 + 1) * g) hxH,
    Ordinal.mod_lt _ hW0, (Ordinal.div_add_mod x (leWe g)).symm⟩

/-- **`x < W^f` gives `Θ̂_L x < Ω^{Θ f}`** for `x ∈ H_λ`, `x < W^{Ω₂}` and a code `f < Ω₂`. -/
theorem tuThX_bound : ∀ x, x ∈ cdHull S l → x < leWe (Om (1 + 1)) → ∀ f, GxCl (upsilon l) (ldAtR S l) f →
    f < Om (1 + 1) → x < leWe f → tdThL S l x < leOe (gxTh (upsilon l) (ldAtR S l) f) := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hxH hx f hf hfW hxf
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [tjThL_zero]; exact leOe_pos _
  have h0 := pos_iff_ne_zero.2 hx0
  obtain ⟨hgc, hgW, -, -, hdW, hrH, hrg, -⟩ := tuParts hl hX hxH h0 hx
  set g := sgLW x with hg
  have hgf : g < f := by
    by_contra hc; push Not at hc
    exact absurd ((leWe_mono hc).trans (sgLW_le h0)) (not_le.2 hxf)
  have hrx : x % leWe g < x := hrg.trans_le (sgLW_le h0)
  have hIH := IH _ hrx hrH (hrx.trans hx) g hgc hgW hrg
  have hΘd : gxTh (upsilon l) (ldAtR S l) (x / leWe g) < Om 1 := snTh_lt_Om1 hl hX hdW.le
  rw [tuThX_cnf hl hX hxH h0 hx, ← hg]
  calc leOe (gxTh (upsilon l) (ldAtR S l) g) * gxTh (upsilon l) (ldAtR S l) (x / leWe g) +
        tdThL S l (x % leWe g)
      < leOe (gxTh (upsilon l) (ldAtR S l) g) * gxTh (upsilon l) (ldAtR S l) (x / leWe g) +
        leOe (gxTh (upsilon l) (ldAtR S l) g) := (add_lt_add_iff_left _).2 hIH
    _ = leOe (gxTh (upsilon l) (ldAtR S l) g) * (gxTh (upsilon l) (ldAtR S l) (x / leWe g) + 1) :=
        (mul_add_one _ _).symm
    _ ≤ leOe (gxTh (upsilon l) (ldAtR S l) g) * Om 1 :=
        mul_le_mul_left' (Order.add_one_le_of_lt hΘd) _
    _ = leOe (gxTh (upsilon l) (ldAtR S l) g + 1) := (leOe_succ _).symm
    _ ≤ leOe (gxTh (upsilon l) (ldAtR S l) f) := leOe_mono (Order.add_one_le_of_lt (gxTh_lt hgc hgf))

/-- `Θ̂_L x < Ω^{Ω₁}` for `x ∈ H_λ`, `x < W^{Ω₂}`. -/
theorem tuThX_lt_OO {x : Ordinal.{0}} (hxH : x ∈ cdHull S l) (hx : x < leWe (Om (1 + 1))) :
    tdThL S l x < leOe (Om 1) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [tjThL_zero]; exact leOe_pos _
  obtain ⟨hgc, hgW, -, -, -, -, -, -⟩ := tuParts hl hX hxH (pos_iff_ne_zero.2 hx0) hx
  have hgc' := rqCode_succ hl hX hgc (ldOm2_SC.isSuccLimit.add_one_lt hgW)
  refine (tuThX_bound hl hX x hxH hx _ hgc' (ldOm2_SC.isSuccLimit.add_one_lt hgW) (sgLW_lt x)).trans ?_
  exact leOe_lt (snTh_lt_Om1 hl hX (ldOm2_SC.isSuccLimit.add_one_lt hgW).le)

/-- **`Θ̂_L` is strictly increasing on `H_λ ∩ W^{Ω₂}`.** -/
theorem tuThX_lt : ∀ x, x ∈ cdHull S l → ∀ y, y ∈ cdHull S l → y < leWe (Om (1 + 1)) → x < y →
    tdThL S l x < tdThL S l y := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hxH y hyH hy hxy
  have hy0 : 0 < y := lt_of_le_of_lt zero_le hxy
  have hx : x < leWe (Om (1 + 1)) := hxy.trans hy
  obtain ⟨hgc, hgW, hdc, hd1, hdW, hrH, hrg, hydec⟩ := tuParts hl hX hyH hy0 hy
  set g := sgLW y with hg
  have hΘd1 : 1 ≤ gxTh (upsilon l) (ldAtR S l) (y / leWe g) := by
    have h := gxTh_mono (Z := upsilon l) (At := ldAtR S l) hd1
    rwa [sqTh_one hl hX] at h
  have hTy : leOe (gxTh (upsilon l) (ldAtR S l) g) ≤ tdThL S l y := by
    rw [tuThX_cnf hl hX hyH hy0 hy, ← hg]
    exact ((mul_one _).symm.le.trans (mul_le_mul_left' hΘd1 _)).trans le_self_add
  rcases lt_or_ge x (leWe g) with hxg | hxg
  · exact (tuThX_bound hl hX x hxH hx g hgc hgW hxg).trans_le hTy
  have hx0 : 0 < x := (leWe_pos g).trans_le hxg
  have hsx : sgLW x = g := by
    obtain ⟨a1, a2⟩ := sjLogW hxg (hxy.trans (sgLW_lt y))
    exact le_antisymm (Order.lt_add_one_iff.1 a2) a1
  obtain ⟨-, -, hdxc, -, hdxW, hrxH, hrxg, hxdec⟩ := tuParts hl hX hxH hx0 hx
  rw [hsx] at hdxc hdxW hrxH hrxg hxdec
  have hdd : x / leWe g ≤ y / leWe g :=
    (Ordinal.le_div (leWe_pos g).ne').2 ((Ordinal.mul_div_le x _).trans hxy.le)
  rw [tuThX_cnf hl hX hxH hx0 hx, tuThX_cnf hl hX hyH hy0 hy, hsx, ← hg]
  rcases hdd.lt_or_eq with hlt | heq
  · have hΘlt := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hdxc hlt
    have hb := tuThX_bound hl hX _ hrxH ((hrxg.trans_le hxg).trans hx) g hgc hgW hrxg
    calc leOe (gxTh (upsilon l) (ldAtR S l) g) * gxTh (upsilon l) (ldAtR S l) (x / leWe g) +
          tdThL S l (x % leWe g)
        < leOe (gxTh (upsilon l) (ldAtR S l) g) * gxTh (upsilon l) (ldAtR S l) (x / leWe g) +
          leOe (gxTh (upsilon l) (ldAtR S l) g) := (add_lt_add_iff_left _).2 hb
      _ = leOe (gxTh (upsilon l) (ldAtR S l) g) * (gxTh (upsilon l) (ldAtR S l) (x / leWe g) + 1) :=
          (mul_add_one _ _).symm
      _ ≤ leOe (gxTh (upsilon l) (ldAtR S l) g) * gxTh (upsilon l) (ldAtR S l) (y / leWe g) :=
          mul_le_mul_left' (Order.add_one_le_of_lt hΘlt) _
      _ ≤ _ := le_self_add
  · rw [heq]
    refine (add_lt_add_iff_left _).2 ?_
    have hrr : x % leWe g < y % leWe g := by
      have h := hxy
      rw [hxdec, hydec, heq] at h
      exact (add_lt_add_iff_left _).1 h
    have hrxx : x % leWe g < x := hrxg.trans_le hxg
    exact IH _ hrxx hrxH _ hrH (hrg.trans_le (sgLW_le hy0) |>.trans hy) hrr

omit hl hX in
/-- `W^{s+1} ∣ e`, `e ≠ 0` give `s + 1 ≤ log_W e` and `W^{s+1} ∣ e mod W^{log_W e}`. -/
theorem tuDvd_parts {e s : Ordinal.{0}} (he0 : 0 < e) (hd : leWe (s + 1) ∣ e) :
    s + 1 ≤ sgLW e ∧ leWe (s + 1) ∣ e % leWe (sgLW e) := by
  obtain ⟨q, hq⟩ := hd
  have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hq; exact absurd hq he0.ne'
  have hle : leWe (s + 1) ≤ e := by
    rw [hq]; exact (mul_one _).symm.le.trans (mul_le_mul_left' (Order.one_le_iff_ne_zero.2 hq0) _)
  have hs : s + 1 ≤ sgLW e := (sjLogW hle (sgLW_lt e)).1
  refine ⟨hs, ?_⟩
  obtain ⟨t, ht⟩ := exists_add_of_le hs
  rw [ht, tuWe_add (s + 1) t, hq, Ordinal.mul_mod_mul]
  exact dvd_mul_right _ _

omit hl hX in
/-- `W^f ∣ e` and `f ≤ g` give `W^f ∣ e mod W^g`. -/
theorem tuDvd_mod {e f g : Ordinal.{0}} (hd : leWe f ∣ e) (hfg : f ≤ g) : leWe f ∣ e % leWe g := by
  obtain ⟨t, rfl⟩ := exists_add_of_le hfg
  obtain ⟨q, rfl⟩ := hd
  rw [tuWe_add f t, Ordinal.mul_mod_mul]
  exact dvd_mul_right _ _

/-- **`Θ̂_L(W^f·c) = Ω^{Θ f}·Θ c`** for codes `f, c < Ω₂`, `1 ≤ c`. -/
theorem tuThX_term {f c : Ordinal.{0}} (hfW : f < Om (1 + 1)) (hc1 : 1 ≤ c) (hcW : c < Om (1 + 1))
    (hH : leWe f * c ∈ cdHull S l) :
    tdThL S l (leWe f * c) = leOe (gxTh (upsilon l) (ldAtR S l) f) * gxTh (upsilon l) (ldAtR S l) c := by
  have hlt : leWe f * c < leWe (Om (1 + 1)) := by
    calc leWe f * c < leWe f * Om (1 + 1) := mul_lt_mul_of_pos_left hcW (leWe_pos f)
      _ = leWe (f + 1) := (leWe_succ f).symm
      _ ≤ leWe (Om (1 + 1)) := leWe_mono (Order.add_one_le_of_lt hfW)
  have h0 : 0 < leWe f * c := mul_pos (leWe_pos f) (zero_lt_one.trans_le hc1)
  obtain ⟨e1, e2, e3⟩ := tuSgLW_term (f := f) hc1 hcW
  rw [tuThX_cnf hl hX hH h0 hlt, e1, e2, e3, tjThL_zero, add_zero]

/-- **`Θ̂_L(e + y) = Θ̂_L e + Θ̂_L y` when `W^{log_W y + 1} ∣ e`** (`e, y ∈ H_λ`, `e + y < W^{Ω₂}`). -/
theorem tuThX_add : ∀ e, e ∈ cdHull S l → ∀ y, y ∈ cdHull S l → e + y < leWe (Om (1 + 1)) →
    leWe (sgLW y + 1) ∣ e → tdThL S l (e + y) = tdThL S l e + tdThL S l y := by
  intro e
  induction e using WellFoundedLT.induction with
  | ind e IH =>
  intro heH y hyH hlt hd
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [add_zero, tjThL_zero, add_zero]
  rcases eq_or_ne e 0 with rfl | he0
  · rw [zero_add, tjThL_zero, zero_add]
  have he0' : 0 < e := pos_iff_ne_zero.2 he0
  have heW : e < leWe (Om (1 + 1)) := le_self_add.trans_lt hlt
  obtain ⟨hs, hdr⟩ := tuDvd_parts he0' hd
  obtain ⟨-, -, -, -, hdW, hrH, hrg, hedec⟩ := tuParts hl hX heH he0' heW
  set g := sgLW e with hg
  set d := e / leWe g with hd_def
  set r := e % leWe g with hr_def
  have hW0 : leWe g ≠ 0 := (leWe_pos g).ne'
  have hyg : y < leWe g := (sgLW_lt y).trans_le (leWe_mono hs)
  have hry : r + y < leWe g := (isPrincipal_add_omega0_opow (Om (1 + 1) * g)) hrg hyg
  have hey : e + y = leWe g * d + (r + y) := by
    conv_lhs => rw [hedec]
    rw [add_assoc]
  have hdiv : (e + y) / leWe g = d := by
    rw [hey, Ordinal.mul_add_div _ hW0, Ordinal.div_eq_zero_of_lt hry, add_zero]
  have hmod : (e + y) % leWe g = r + y := by
    rw [hey, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hry]
  have hsg : sgLW (e + y) = g := by
    have h1 : leWe g ≤ e + y := (sgLW_le he0').trans le_self_add
    have h2 : e + y < leWe (g + 1) := by
      rw [hey, leWe_succ]
      calc leWe g * d + (r + y) < leWe g * d + leWe g := (add_lt_add_iff_left _).2 hry
        _ = leWe g * (d + 1) := (mul_add_one _ _).symm
        _ ≤ leWe g * Om (1 + 1) := mul_le_mul_left' (Order.add_one_le_of_lt hdW) _
    obtain ⟨a1, a2⟩ := sjLogW h1 h2
    exact le_antisymm (Order.lt_add_one_iff.1 a2) a1
  have hrx : r < e := hrg.trans_le (sgLW_le he0')
  have hrylt : r + y < leWe (Om (1 + 1)) := (add_le_add_left hrx.le y).trans_lt hlt
  have hIH := IH r hrx hrH y hyH hrylt hdr
  have heyH : e + y ∈ cdHull S l := CSet.add_mem heH hyH
  have hey0 : 0 < e + y := he0'.trans_le le_self_add
  rw [tuThX_cnf hl hX heyH hey0 hlt, hsg, hdiv, hmod, hIH, tuThX_cnf hl hX heH he0' heW, ← hg, add_assoc]

/-- **`W^f ∣ e` gives `Ω^{Θ f} ∣ Θ̂_L e`** (`e ∈ H_λ`, `e < W^{Ω₂}`, `f < Ω₂` a code). -/
theorem tuThX_dvd : ∀ e, e ∈ cdHull S l → e < leWe (Om (1 + 1)) → ∀ f, GxCl (upsilon l) (ldAtR S l) f →
    f < Om (1 + 1) → leWe f ∣ e → leOe (gxTh (upsilon l) (ldAtR S l) f) ∣ tdThL S l e := by
  intro e
  induction e using WellFoundedLT.induction with
  | ind e IH =>
  intro heH heW f hf hfW hd
  rcases eq_or_ne e 0 with rfl | he0
  · rw [tjThL_zero]; exact dvd_zero _
  have he0' : 0 < e := pos_iff_ne_zero.2 he0
  obtain ⟨hgc, -, -, -, -, hrH, hrg, -⟩ := tuParts hl hX heH he0' heW
  set g := sgLW e with hg
  have hfg : f ≤ g := by
    obtain ⟨q, hq⟩ := hd
    have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hq; exact he0 hq
    have hle : leWe f ≤ e := by
      rw [hq]; exact (mul_one _).symm.le.trans (mul_le_mul_left' (Order.one_le_iff_ne_zero.2 hq0) _)
    exact (sjLogW hle (sgLW_lt e)).1
  have hrx : e % leWe g < e := hrg.trans_le (sgLW_le he0')
  have hIH := IH _ hrx hrH (hrx.trans heW) f hf hfW (tuDvd_mod hd hfg)
  rw [tuThX_cnf hl hX heH he0' heW, ← hg]
  exact dvd_add ((tuOe_dvd (gxTh_mono hfg)).trans (dvd_mul_right _ _)) hIH

end Main

end Googology.Trans.PoR.InaccPsi.R2.Tu
