import Googology.Trans.PoR.InaccPsi.R2.TuStepY

/-!
# The image `Θ̂_L` on the exponents below `ε = ε_{Ω₂+1}`: normal form, bounds, monotonicity, sums, divisibility

`Θ = gxTh ρ_λ (ldAtR λ)`, `Θ̂_L = Td.tdThL`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `log_W = Sg.sgLW`, `H_λ = cdHull S λ`,
`ε = φ(1, Ω₂ + 1)`.  Every `x ∈ H_λ`, `0 < x < ε`, is `W^g·d + r` with `g = log_W x < x`, `d = x / W^g` a code below
`Ω₂`, `r = x mod W^g < W^g`.

* `tuEps_lt_G` (`ε < G = φ(Ω₂, 1)`), `tuPartsG`, `tuThG_cnf` (`Θ̂_L x = Ω^{Θ̂_L g}·Θ d + Θ̂_L r`);
* `tuThG_mono` (**`Θ̂_L` is strictly increasing on `H_λ ∩ ε`, and `x < W^f` gives `Θ̂_L x < Ω^{Θ̂_L f}`**; one
  induction);
* `tuThG_add` (`Θ̂_L(e + y) = Θ̂_L e + Θ̂_L y` for `W^{log_W y + 1} ∣ e`), `tuThG_term`, `tuThG_addT`,
  `tuThG_addW` (`Θ̂_L(e + W^f) = Θ̂_L e + Ω^{Θ̂_L f}` for `W^f ∣ e`), `tuThG_succ`, `tuThG_dvd`
  (`W^f ∣ e` gives `Ω^{Θ̂_L f} ∣ Θ̂_L e`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tu

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj Googology.Trans.PoR.InaccPsi.R2.Sn
  Googology.Trans.PoR.InaccPsi.R2.Sq Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td
  Googology.Trans.PoR.InaccPsi.R2.Tg Googology.Trans.PoR.InaccPsi.R2.Tj Googology.Trans.PoR.InaccPsi.R2.Tn

variable {S : InaccSeq.{0}}

/-- `ε_{Ω₂+1} < φ(Ω₂, 1)`. -/
theorem tuEps_lt_G : veblen 1 (Om (1 + 1 : Ordinal.{0}) + 1) < veblen (Om (1 + 1)) 1 := by
  have h1 : (1 : Ordinal.{0}) < Om (1 + 1) := gg_one_lt_of_SC ldOm2_SC
  have hfix : veblen 1 (veblen (Om (1 + 1 : Ordinal.{0})) 1) = veblen (Om (1 + 1)) 1 :=
    veblen_veblen_of_lt h1 1
  have hlt : Om (1 + 1 : Ordinal.{0}) + 1 < veblen (Om (1 + 1)) 1 :=
    Ph.ph_veblen_prin _ _ tgOm_lt_G (h1.trans tgOm_lt_G)
  calc veblen 1 (Om (1 + 1) + 1) < veblen 1 (veblen (Om (1 + 1)) 1) := (veblen_lt_veblen_iff_right).2 hlt
    _ = veblen (Om (1 + 1)) 1 := hfix

/-- `ε` is a limit, `Ω₂ < ε`, `W^ε = ε`. -/
theorem tuEps_lim : IsSuccLimit (veblen 1 (Om (1 + 1 : Ordinal.{0}) + 1)) := taVeb_lim one_ne_zero

theorem tuOm2_lt_eps : Om (1 + 1 : Ordinal.{0}) < veblen 1 (Om (1 + 1) + 1) :=
  (lt_add_one _).trans_le (right_le_veblen _ _)

/-- `log_W x < x`, `log_W x ∈ H_λ`, for `0 < x < ε` in `H_λ`. -/
theorem tuSg_lt {x : Ordinal.{0}} (h0 : 0 < x) (hx : x < veblen 1 (Om (1 + 1) + 1)) : sgLW x < x :=
  sgLW_lt_self (Order.one_le_iff_pos.2 h0) hx

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The normal form of `Θ̂_L x`** for `x ∈ H_λ`, `0 < x < ε`. -/
theorem tuThG_cnf {x : Ordinal.{0}} (hxH : x ∈ cdHull S l) (h0 : 0 < x) (hx : x < veblen 1 (Om (1 + 1) + 1)) :
    tdThL S l x = leOe (tdThL S l (sgLW x)) * gxTh (upsilon l) (ldAtR S l) (x / leWe (sgLW x)) +
      tdThL S l (x % leWe (sgLW x)) := by
  have h1ρ : (1 : Ordinal.{0}) ≤ upsilon l := (gg_one_lt_of_SC (leRho hl hX).1).le
  have hrH : x % leWe (sgLW x) ∈ cdHull S l := leModP_mem (Om (1 + 1) * sgLW x) hxH
  have hrG : x % leWe (sgLW x) < veblen (Om (1 + 1)) 1 :=
    ((Ordinal.mod_lt _ (leWe_pos _).ne').trans_le (sgLW_le h0)).trans (hx.trans tuEps_lt_G)
  rw [tjThL_cnf h1ρ ⟨h0, tuSg_lt h0 hx⟩ (tgTm_spec hl hX _ hrH hrG).1]

/-- The parts of `x ∈ H_λ`, `0 < x < ε`. -/
theorem tuPartsG {x : Ordinal.{0}} (hxH : x ∈ cdHull S l) (h0 : 0 < x) (hx : x < veblen 1 (Om (1 + 1) + 1)) :
    sgLW x ∈ cdHull S l ∧ sgLW x < x ∧
      GxCl (upsilon l) (ldAtR S l) (x / leWe (sgLW x)) ∧ 1 ≤ x / leWe (sgLW x) ∧ x / leWe (sgLW x) < Om (1 + 1) ∧
      x % leWe (sgLW x) ∈ cdHull S l ∧ x % leWe (sgLW x) < leWe (sgLW x) ∧
      x = leWe (sgLW x) * (x / leWe (sgLW x)) + x % leWe (sgLW x) := by
  set g := sgLW x with hg
  have hW0 : leWe g ≠ 0 := (leWe_pos g).ne'
  have hWe : leWe g ≤ x := sgLW_le h0
  have hE2 : x < leWe g * Om (1 + 1) := by rw [← leWe_succ]; exact sgLW_lt x
  have hqW : x / leWe g < Om (1 + 1) := (Ordinal.lt_mul_iff_div_lt hW0).1 hE2
  have hqH : x / leWe g ∈ cdHull S l := by
    refine leDivOp_mem (K := Om (1 + 1) * g) (dvd_mul_right _ _) hxH ?_
    have : leWe (g + 1) = ω ^ (Om (1 + 1) * g + Om (1 + 1)) := by unfold leWe; rw [mul_add_one]
    rw [← this]; exact sgLW_lt x
  exact ⟨ldDivK_mem ldOm2_SC (leLog_mem hxH), tuSg_lt h0 hx, (ldHull_iff hl hX hqW).1 hqH,
    Order.one_le_iff_pos.2 ((Ordinal.div_pos hW0).2 hWe), hqW, leModP_mem (Om (1 + 1) * g) hxH,
    Ordinal.mod_lt _ hW0, (Ordinal.div_add_mod x (leWe g)).symm⟩

/-- **`Θ̂_L` is strictly increasing on `H_λ ∩ ε`, and `x < W^y` gives `Θ̂_L x < Ω^{Θ̂_L y}`.** -/
theorem tuThG_mono : ∀ y, y ∈ cdHull S l → y < veblen 1 (Om (1 + 1) + 1) →
    (∀ x, x ∈ cdHull S l → x < y → tdThL S l x < tdThL S l y) ∧
    (∀ x, x ∈ cdHull S l → x < veblen 1 (Om (1 + 1) + 1) → x < leWe y → tdThL S l x < leOe (tdThL S l y)) := by
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hyH hyE
  -- the strict increase at `y`
  have hM : ∀ x, x ∈ cdHull S l → x < y → tdThL S l x < tdThL S l y := by
    intro x hxH hxy
    have hy0 : 0 < y := lt_of_le_of_lt zero_le hxy
    obtain ⟨hgH, hgy, hdc, hd1, hdW, hrH, hrg, hydec⟩ := tuPartsG hl hX hyH hy0 hyE
    set g := sgLW y with hg
    have hΘd1 : 1 ≤ gxTh (upsilon l) (ldAtR S l) (y / leWe g) := by
      have h := gxTh_mono (Z := upsilon l) (At := ldAtR S l) hd1
      rwa [sqTh_one hl hX] at h
    have hTy : leOe (tdThL S l g) ≤ tdThL S l y := by
      rw [tuThG_cnf hl hX hyH hy0 hyE, ← hg]
      exact ((mul_one _).symm.le.trans (mul_le_mul_left' hΘd1 _)).trans le_self_add
    have hxE : x < veblen 1 (Om (1 + 1) + 1) := hxy.trans hyE
    rcases lt_or_ge x (leWe g) with hxg | hxg
    · exact ((IH g hgy hgH (hgy.trans hyE)).2 x hxH hxE hxg).trans_le hTy
    have hx0 : 0 < x := (leWe_pos g).trans_le hxg
    have hsx : sgLW x = g := by
      obtain ⟨a1, a2⟩ := sjLogW hxg (hxy.trans (sgLW_lt y))
      exact le_antisymm (Order.lt_add_one_iff.1 a2) a1
    obtain ⟨-, -, hdxc, -, hdxW, hrxH, hrxg, hxdec⟩ := tuPartsG hl hX hxH hx0 hxE
    rw [hsx] at hdxc hdxW hrxH hrxg hxdec
    have hdd : x / leWe g ≤ y / leWe g :=
      (Ordinal.le_div (leWe_pos g).ne').2 ((Ordinal.mul_div_le x _).trans hxy.le)
    rw [tuThG_cnf hl hX hxH hx0 hxE, tuThG_cnf hl hX hyH hy0 hyE, hsx, ← hg]
    have hb := (IH g hgy hgH (hgy.trans hyE)).2 _ hrxH ((hrxg.trans_le hxg).trans hxE) hrxg
    rcases hdd.lt_or_eq with hlt | heq
    · have hΘlt := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hdxc hlt
      calc leOe (tdThL S l g) * gxTh (upsilon l) (ldAtR S l) (x / leWe g) + tdThL S l (x % leWe g)
          < leOe (tdThL S l g) * gxTh (upsilon l) (ldAtR S l) (x / leWe g) + leOe (tdThL S l g) :=
            (add_lt_add_iff_left _).2 hb
        _ = leOe (tdThL S l g) * (gxTh (upsilon l) (ldAtR S l) (x / leWe g) + 1) := (mul_add_one _ _).symm
        _ ≤ leOe (tdThL S l g) * gxTh (upsilon l) (ldAtR S l) (y / leWe g) :=
            mul_le_mul_left' (Order.add_one_le_of_lt hΘlt) _
        _ ≤ _ := le_self_add
    · rw [heq]
      refine (add_lt_add_iff_left _).2 ?_
      have hrr : x % leWe g < y % leWe g := by
        have h := hxy
        rw [hxdec, hydec, heq] at h
        exact (add_lt_add_iff_left _).1 h
      have hry : y % leWe g < y := hrg.trans_le (sgLW_le hy0)
      exact (IH _ hry hrH (hry.trans hyE)).1 _ hrxH hrr
  refine ⟨hM, ?_⟩
  -- the bound at `y`, by induction on `x`
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IHx =>
  intro hxH hxE hxy
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [tjThL_zero]; exact leOe_pos _
  have h0 := pos_iff_ne_zero.2 hx0
  obtain ⟨hgH, hgx, -, -, hdW, hrH, hrg, -⟩ := tuPartsG hl hX hxH h0 hxE
  set g := sgLW x with hg
  have hgy : g < y := by
    by_contra hc; push Not at hc
    exact absurd ((leWe_mono hc).trans (sgLW_le h0)) (not_le.2 hxy)
  have hrx : x % leWe g < x := hrg.trans_le (sgLW_le h0)
  have hrb : tdThL S l (x % leWe g) < leOe (tdThL S l g) :=
    (IH g hgy hgH (hgy.trans hyE)).2 _ hrH (hrx.trans hxE) hrg
  have hΘd : gxTh (upsilon l) (ldAtR S l) (x / leWe g) < Om 1 := snTh_lt_Om1 hl hX hdW.le
  rw [tuThG_cnf hl hX hxH h0 hxE, ← hg]
  calc leOe (tdThL S l g) * gxTh (upsilon l) (ldAtR S l) (x / leWe g) + tdThL S l (x % leWe g)
      < leOe (tdThL S l g) * gxTh (upsilon l) (ldAtR S l) (x / leWe g) + leOe (tdThL S l g) :=
        (add_lt_add_iff_left _).2 hrb
    _ = leOe (tdThL S l g) * (gxTh (upsilon l) (ldAtR S l) (x / leWe g) + 1) := (mul_add_one _ _).symm
    _ ≤ leOe (tdThL S l g) * Om 1 := mul_le_mul_left' (Order.add_one_le_of_lt hΘd) _
    _ = leOe (tdThL S l g + 1) := (leOe_succ _).symm
    _ ≤ leOe (tdThL S l y) := leOe_mono (Order.add_one_le_of_lt (hM g hgH hgy))

/-- **`Θ̂_L x < Θ̂_L y`** for `x < y` in `H_λ ∩ ε`. -/
theorem tuThG_lt {x y : Ordinal.{0}} (hxH : x ∈ cdHull S l) (hyH : y ∈ cdHull S l)
    (hyE : y < veblen 1 (Om (1 + 1) + 1)) (hxy : x < y) : tdThL S l x < tdThL S l y :=
  (tuThG_mono hl hX y hyH hyE).1 x hxH hxy

theorem tuThG_le {x y : Ordinal.{0}} (hxH : x ∈ cdHull S l) (hyH : y ∈ cdHull S l)
    (hyE : y < veblen 1 (Om (1 + 1) + 1)) (hxy : x ≤ y) : tdThL S l x ≤ tdThL S l y := by
  rcases hxy.lt_or_eq with h | rfl
  · exact (tuThG_lt hl hX hxH hyH hyE h).le
  · exact le_rfl

/-- **`Θ̂_L(e + y) = Θ̂_L e + Θ̂_L y` when `W^{log_W y + 1} ∣ e`** (`e, y ∈ H_λ`, `e + y < ε`). -/
theorem tuThG_add : ∀ e, e ∈ cdHull S l → ∀ y, y ∈ cdHull S l → e + y < veblen 1 (Om (1 + 1) + 1) →
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
  have heE : e < veblen 1 (Om (1 + 1) + 1) := le_self_add.trans_lt hlt
  obtain ⟨hs, hdr⟩ := tuDvd_parts he0' hd
  obtain ⟨-, -, -, -, hdW, hrH, hrg, hedec⟩ := tuPartsG hl hX heH he0' heE
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
  have hrylt : r + y < veblen 1 (Om (1 + 1) + 1) := (add_le_add_left hrx.le y).trans_lt hlt
  have hIH := IH r hrx hrH y hyH hrylt hdr
  have heyH : e + y ∈ cdHull S l := CSet.add_mem heH hyH
  have hey0 : 0 < e + y := he0'.trans_le le_self_add
  rw [tuThG_cnf hl hX heyH hey0 hlt, hsg, hdiv, hmod, hIH, tuThG_cnf hl hX heH he0' heE, ← hg, add_assoc]

/-- `Θ̂_L(W^f·c) = Ω^{Θ̂_L f}·Θ c` for `1 ≤ c < Ω₂`, `W^f·c < ε`. -/
theorem tuThG_term {f c : Ordinal.{0}} (hc1 : 1 ≤ c) (hcW : c < Om (1 + 1)) (hH : leWe f * c ∈ cdHull S l)
    (hlt : leWe f * c < veblen 1 (Om (1 + 1) + 1)) :
    tdThL S l (leWe f * c) = leOe (tdThL S l f) * gxTh (upsilon l) (ldAtR S l) c := by
  have h0 : 0 < leWe f * c := mul_pos (leWe_pos f) (zero_lt_one.trans_le hc1)
  obtain ⟨e1, e2, e3⟩ := tuSgLW_term (f := f) hc1 hcW
  rw [tuThG_cnf hl hX hH h0 hlt, e1, e2, e3, tjThL_zero, add_zero]

/-- `Θ̂_L(e + W^f·c) = Θ̂_L e + Ω^{Θ̂_L f}·Θ c` for `W^{f+1} ∣ e`. -/
theorem tuThG_addT {e f c : Ordinal.{0}} (heH : e ∈ cdHull S l) (hfH : f ∈ cdHull S l)
    (hcH : c ∈ cdHull S l) (hc1 : 1 ≤ c) (hcW : c < Om (1 + 1)) (hd : leWe (f + 1) ∣ e)
    (hlt : e + leWe f * c < veblen 1 (Om (1 + 1) + 1)) :
    tdThL S l (e + leWe f * c) = tdThL S l e + leOe (tdThL S l f) * gxTh (upsilon l) (ldAtR S l) c := by
  have hyH : leWe f * c ∈ cdHull S l := leMulWe_mem hfH hcH
  obtain ⟨hs, -, -⟩ := tuSgLW_term (f := f) hc1 hcW
  rw [tuThG_add hl hX e heH _ hyH hlt (by rw [hs]; exact hd),
    tuThG_term hl hX hc1 hcW hyH (le_add_self.trans_lt hlt)]

/-- **`Θ̂_L(e + W^f) = Θ̂_L e + Ω^{Θ̂_L f}` for `W^f ∣ e`** (`e, f ∈ H_λ`, `e + W^f < ε`). -/
theorem tuThG_addW {e f : Ordinal.{0}} (heH : e ∈ cdHull S l) (hfH : f ∈ cdHull S l) (hd : leWe f ∣ e)
    (hlt : e + leWe f < veblen 1 (Om (1 + 1) + 1)) :
    tdThL S l (e + leWe f) = tdThL S l e + leOe (tdThL S l f) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  set m := leWe (f + 1) * (e / leWe (f + 1)) with hm
  set s := e % leWe (f + 1) with hs
  have hmH : m ∈ cdHull S l := Ts.ts_mod_mem le_add_self e heH
  have hsH : s ∈ cdHull S l := leModP_mem (Om (1 + 1) * (f + 1)) heH
  have hes : e = m + s := (Ordinal.div_add_mod e _).symm
  have hsW : s < leWe (f + 1) := Ordinal.mod_lt _ (leWe_pos _).ne'
  have hsd : leWe f ∣ s := tuDvd_mod hd le_self_add
  set d := s / leWe f with hd_def
  have hsdec : s = leWe f * d := by
    obtain ⟨q, hq⟩ := hsd
    rw [hd_def, hq, Ordinal.mul_div_cancel _ (leWe_pos _).ne']
  have hdW : d < Om (1 + 1) := by
    have : s < leWe f * Om (1 + 1) := by rw [← leWe_succ]; exact hsW
    exact (Ordinal.lt_mul_iff_div_lt (leWe_pos _).ne').1 this
  have hdH : d ∈ cdHull S l := by
    refine leDivOp_mem (K := Om (1 + 1) * f) (dvd_mul_right _ _) hsH ?_
    have : leWe (f + 1) = ω ^ (Om (1 + 1) * f + Om (1 + 1)) := by unfold leWe; rw [mul_add_one]
    rw [← this]; exact hsW
  have hdc : GxCl (upsilon l) (ldAtR S l) d := (ldHull_iff hl hX hdW).1 hdH
  have hmd : leWe (f + 1) ∣ m := dvd_mul_right _ _
  have hd1W : d + 1 < Om (1 + 1) := ldOm2_SC.isSuccLimit.add_one_lt hdW
  have hd1H : d + 1 ∈ cdHull S l := CSet.succ_mem hdH
  have he2 : e + leWe f = m + leWe f * (d + 1) := by rw [hes, hsdec, mul_add_one, add_assoc]
  rw [he2, tuThG_addT hl hX hmH hfH hd1H le_add_self hd1W hmd (he2 ▸ hlt), gxTh_add hρSC hAt hdc,
    sqTh_one hl hX, mul_add_one, ← add_assoc]
  congr 1
  rw [hes, hsdec]
  rcases eq_or_ne d 0 with h0 | h0
  · rw [h0, mul_zero, add_zero, gxTh_zero, mul_zero, add_zero]
  · exact (tuThG_addT hl hX hmH hfH hdH (Order.one_le_iff_ne_zero.2 h0) hdW hmd
      ((le_self_add.trans_eq (by rw [hes, hsdec])).trans_lt hlt)).symm

/-- `Θ̂_L(e + 1) = Θ̂_L e + 1`. -/
theorem tuThG_succ {e : Ordinal.{0}} (heH : e ∈ cdHull S l) (hlt : e + 1 < veblen 1 (Om (1 + 1) + 1)) :
    tdThL S l (e + 1) = tdThL S l e + 1 := by
  have h := tuThG_addW hl hX heH (CSet.zero_mem _ _) (by rw [leWe_zero]; exact one_dvd _) (by rwa [leWe_zero])
  rwa [leWe_zero, tjThL_zero, leOe_zero] at h

/-- **`W^f ∣ e` gives `Ω^{Θ̂_L f} ∣ Θ̂_L e`** (`e, f ∈ H_λ`, `e < ε`). -/
theorem tuThG_dvd : ∀ e, e ∈ cdHull S l → e < veblen 1 (Om (1 + 1) + 1) → ∀ f, f ∈ cdHull S l →
    leWe f ∣ e → leOe (tdThL S l f) ∣ tdThL S l e := by
  intro e
  induction e using WellFoundedLT.induction with
  | ind e IH =>
  intro heH heE f hfH hd
  rcases eq_or_ne e 0 with rfl | he0
  · rw [tjThL_zero]; exact dvd_zero _
  have he0' : 0 < e := pos_iff_ne_zero.2 he0
  obtain ⟨hgH, hge, -, -, -, hrH, hrg, -⟩ := tuPartsG hl hX heH he0' heE
  set g := sgLW e with hg
  have hfg : f ≤ g := by
    obtain ⟨q, hq⟩ := hd
    have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hq; exact he0 hq
    have hle : leWe f ≤ e := by
      rw [hq]; exact (mul_one _).symm.le.trans (mul_le_mul_left' (Order.one_le_iff_ne_zero.2 hq0) _)
    exact (sjLogW hle (sgLW_lt e)).1
  have hrx : e % leWe g < e := hrg.trans_le (sgLW_le he0')
  have hIH := IH _ hrx hrH (hrx.trans heE) f hfH (tuDvd_mod hd hfg)
  rw [tuThG_cnf hl hX heH he0' heE, ← hg]
  exact dvd_add ((tuOe_dvd (tuThG_le hl hX hfH hgH (hge.trans heE) hfg)).trans (dvd_mul_right _ _)) hIH

end Main

end Googology.Trans.PoR.InaccPsi.R2.Tu
