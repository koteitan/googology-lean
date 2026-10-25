import Googology.Trans.PoR.InaccPsi.R2.TnRoad

/-!
# Heads of codes `P + x` (`W^f ∣ P`, `x ≤ W^f`) and the cofinality of codes below `ω^{κ·e}·κ`

`W^E = Ω₂^E = ω^{Ω₂·E}` (`Le.leWe`), `Ω^x = Ω₁^x` (`Le.leOe`), codes `Le.LeCl κ Q` (generator `κ` strongly
critical, `Q` strongly critical), `G = φ(Ω₂, 1)`, `Ĝ = φ(Ω₁, 1)`.

* `tuCl_pred` (**a code `a + 1` gives the code `a`**);
* `tuExp_code` (**a code `P + W^f` with `W^f ∣ P` gives the code `f`**: the part `W^f·(m + 1)`, `m < ω`, of the
  code below `W^f·ω` has the logarithm `Ω₂·f`);
* `tuHead` (**THE HEAD LEMMA: a code `z` with `P + W^g ≤ z ≤ P + W^f`, `g ≤ f`, `W^f ∣ P` gives the code `P` and a
  code `h ∈ [g, f]`**; no hypothesis on `f`, `g`);
* `tuCofK` (**a code `x < ω^{κ·e}·κ` is below `ω^{κ·e}·c'` for some `c' < Q`**; no hypothesis on `e`);
* `tuWe_G`, `tuOe_Gh` (`W^f < G`, `W^f ∣ G` for `f < G`; the same for `Ω^x` and `Ĝ`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tu

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Sg
  Googology.Trans.PoR.InaccPsi.R2.Sj Googology.Trans.PoR.InaccPsi.R2.Sw

variable {S : InaccSeq.{0}}

/-- **A code `a + 1` gives the code `a`.** -/
theorem tuCl_pred {κ Q a : Ordinal.{0}} (hQ : SC Q) (hκ : SC κ) (h : LeCl κ Q (a + 1)) : LeCl κ Q a := by
  have hω0 : (ω : Ordinal.{0}) ≠ 0 := omega0_pos.ne'
  have h1 : LeCl κ Q (1 : Ordinal.{0}) := LeCl.small (gg_one_lt_of_SC hQ)
  have hd := swCl_divOp hQ hκ h1 (a + 1) h
  rw [opow_one] at hd
  have hr : a % ω < ω := Ordinal.mod_lt a hω0
  have hr1 : a % ω + 1 < ω := isSuccLimit_omega0.add_one_lt hr
  have e1 : (a + 1) / ω = a / ω := by
    conv_lhs => rw [← Ordinal.div_add_mod a ω, add_assoc]
    rw [Ordinal.mul_add_div _ hω0, Ordinal.div_eq_zero_of_lt hr1, add_zero]
  rw [e1] at hd
  have hm := rvCl_mulOp hQ h1 hκ _ hd
  rw [opow_one] at hm
  have hsm : LeCl κ Q (a % ω) := LeCl.small (hr.trans (Lw.lw_omega_lt_SC hQ))
  have := LeCl.add hm hsm
  rwa [Ordinal.div_add_mod] at this

/-- `(q + 1) mod ω = (q mod ω) + 1`. -/
theorem tuMod_succ (q : Ordinal.{0}) : (q + 1) % ω = q % ω + 1 := by
  have hω0 : (ω : Ordinal.{0}) ≠ 0 := omega0_pos.ne'
  have hr1 : q % ω + 1 < ω := isSuccLimit_omega0.add_one_lt (Ordinal.mod_lt q hω0)
  conv_lhs => rw [← Ordinal.div_add_mod q ω, add_assoc]
  rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr1]

/-- **A code `P + W^f` with `W^f ∣ P` gives the code `f`.** -/
theorem tuExp_code {Q P f : Ordinal.{0}} (hQ : SC Q) (hd : leWe f ∣ P)
    (hz : LeCl (Om (1 + 1)) Q (P + leWe f)) : LeCl (Om (1 + 1)) Q f := by
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  obtain ⟨q, rfl⟩ := hd
  have hm := LeCl.mod hQ.1 ldOm2_SC.isPrincipal (Om (1 + 1) * f + 1) hz
  have e1 : ω ^ (Om (1 + 1) * f + 1) = leWe f * ω := by unfold leWe; rw [opow_add, opow_one]
  have e2 : leWe f * q + leWe f = leWe f * (q + 1) := (mul_add_one _ _).symm
  rw [e1, e2, Ordinal.mul_mod_mul, tuMod_succ] at hm
  have hlog := (leClDec hQ ldOm2_SC _ hm).2
  have hm0 : q % ω + 1 ≠ 0 := (zero_lt_one.trans_le le_add_self).ne'
  have hlt : q % ω + 1 < ω := isSuccLimit_omega0.add_one_lt (Ordinal.mod_lt q omega0_pos.ne')
  have e3 : log ω (leWe f * (q % ω + 1)) = Om (1 + 1) * f := by
    unfold leWe
    have := log_opow_mul_add (b := ω) (u := Om (1 + 1) * f) (v := q % ω + 1) (w := 0) one_lt_omega0 hm0
      (opow_pos _ omega0_pos)
    rw [add_zero] at this
    rw [this, log_eq_zero hlt, add_zero]
  rw [e3] at hlog
  have := sjCl_div hQ ldOm2_SC _ hlog
  rwa [Ordinal.mul_div_cancel _ hW0] at this

/-- `W^g ∣ W^f` for `g ≤ f`. -/
theorem tuWe_dvd {g f : Ordinal.{0}} (h : g ≤ f) : leWe g ∣ leWe f :=
  opow_dvd_opow ω (mul_le_mul_left' h _)

/-- `Ω^y ∣ Ω^x` for `y ≤ x`. -/
theorem tuOe_dvd {y x : Ordinal.{0}} (h : y ≤ x) : leOe y ∣ leOe x :=
  opow_dvd_opow ω (mul_le_mul_left' h _)

/-- **THE HEAD LEMMA**: a code `z` with `P + W^g ≤ z ≤ P + W^f` (`g ≤ f`, `W^f ∣ P`) gives the code `P` and a code
`h` with `g ≤ h ≤ f`. -/
theorem tuHead {Q P g f z : Ordinal.{0}} (hQ : SC Q) (hd : leWe f ∣ P) (h1 : P + leWe g ≤ z)
    (h2 : z ≤ P + leWe f) (hz : LeCl (Om (1 + 1)) Q z) :
    LeCl (Om (1 + 1)) Q P ∧ ∃ h, g ≤ h ∧ h ≤ f ∧ LeCl (Om (1 + 1)) Q h := by
  obtain ⟨x, rfl⟩ := exists_add_of_le (le_self_add.trans h1 : P ≤ z)
  have hx1 : leWe g ≤ x := (add_le_add_iff_left P).1 h1
  have hx2 : x ≤ leWe f := (add_le_add_iff_left P).1 h2
  rcases hx2.lt_or_eq with hx | rfl
  · -- `x < W^f`: the remainder `x` is a code, its leading exponent `h = log_W x` is a code
    have hxm : (P + x) % leWe f = x := by
      obtain ⟨q, rfl⟩ := hd
      rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hx]
    have hxc : LeCl (Om (1 + 1)) Q x := by
      have h := LeCl.mod hQ.1 ldOm2_SC.isPrincipal (Om (1 + 1) * f) hz
      have e : ω ^ (Om (1 + 1) * f) = leWe f := rfl
      rwa [e, hxm] at h
    obtain ⟨hhc, -, -⟩ := swCl_cnf hQ hxc
    obtain ⟨hgh, hhf⟩ := sjLogW hx1 hx
    have hh1 : LeCl (Om (1 + 1)) Q (sgLW x + 1) := LeCl.add hhc (LeCl.small (gg_one_lt_of_SC hQ))
    have hd1 : leWe (sgLW x + 1) ∣ P := (tuWe_dvd (Order.add_one_le_of_lt hhf)).trans hd
    have hxl : x < leWe (sgLW x + 1) := sgLW_lt x
    have hP : leWe (sgLW x + 1) * ((P + x) / leWe (sgLW x + 1)) = P := by
      obtain ⟨p, rfl⟩ := hd1
      rw [Ordinal.mul_add_div _ (leWe_pos _).ne', Ordinal.div_eq_zero_of_lt hxl, add_zero]
    have := (swCl_headW hQ hh1 hz).1
    rw [hP] at this
    exact ⟨this, sgLW x, hgh, hhf.le, hhc⟩
  · -- `x = W^f`: the exponent `f` is a code, and `(P + W^f)/W^f = q + 1`
    have hfc := tuExp_code hQ hd hz
    obtain ⟨q, rfl⟩ := hd
    have e : (leWe f * q + leWe f) / leWe f = q + 1 := by
      rw [← mul_add_one, Ordinal.mul_div_cancel _ (leWe_pos _).ne']
    have hq := swCl_divW hQ hfc hz
    rw [e] at hq
    have hgf : g ≤ f := by
      by_contra hc; push Not at hc
      exact absurd hx1 (not_le.2 (leWe_lt hc))
    exact ⟨swCl_mulW hQ hfc (tuCl_pred hQ ldOm2_SC hq), f, hgf, le_rfl, hfc⟩

/-- **A code `x < ω^{κ·e}·κ` is below `ω^{κ·e}·c'` for some `c' < Q`.** -/
theorem tuCofK {κ Q e x : Ordinal.{0}} (hQ : SC Q) (hκ : SC κ) (hx : LeCl κ Q x) (hxe : x < ω ^ (κ * e) * κ) :
    ∃ c', c' < Q ∧ x < ω ^ (κ * e) * c' := by
  have hκ0 : κ ≠ 0 := hκ.1.ne'
  rcases lt_or_ge x (ω ^ (κ * e)) with hlt | hge
  · exact ⟨1, gg_one_lt_of_SC hQ, by rwa [mul_one]⟩
  have hx0 : x ≠ 0 := (lt_of_lt_of_le (opow_pos _ omega0_pos) hge).ne'
  have e0 : ω ^ (κ * e) * κ = ω ^ (κ * e + κ) := by rw [opow_add, gg_SC_eps hκ]
  have hL1 : κ * e ≤ log ω x := (opow_le_iff_le_log one_lt_omega0 hx0).1 hge
  have hL2 : log ω x < κ * e + κ := (lt_opow_iff_log_lt one_lt_omega0 hx0).1 (e0 ▸ hxe)
  have hLc := (leClDec hQ hκ x hx).2
  have hr := LeCl.mod hQ.1 hκ.isPrincipal κ hLc
  rw [gg_SC_eps hκ] at hr
  have hq : log ω x / κ = e := by
    refine le_antisymm ?_ ((Ordinal.le_div hκ0).2 hL1)
    have : log ω x < κ * (e + 1) := by rwa [mul_add_one]
    exact Order.lt_add_one_iff.1 ((Ordinal.div_lt hκ0).2 this)
  have hrκ : log ω x % κ < κ := Ordinal.mod_lt _ hκ0
  have hrQ : log ω x % κ < Q := LeCl.lt_of_lt hQ hr hrκ
  refine ⟨ω ^ (log ω x % κ + 1), ldOpow_lt_SC hQ (hQ.isSuccLimit.add_one_lt hrQ), ?_⟩
  have hL : log ω x = κ * e + log ω x % κ := by
    conv_lhs => rw [← Ordinal.div_add_mod (log ω x) κ]
    rw [hq]
  calc x < ω ^ (log ω x + 1) := by
        rw [← Order.succ_eq_add_one]; exact lt_opow_succ_log_self one_lt_omega0 x
    _ = ω ^ (κ * e) * ω ^ (log ω x % κ + 1) := by
        conv_lhs => rw [hL]
        rw [add_assoc, opow_add]

/-- `W^f < G` and `W^f ∣ G` for `f < G`. -/
theorem tuWe_G {f : Ordinal.{0}} (hf : f < veblen (Om (1 + 1)) 1) :
    leWe f < veblen (Om (1 + 1)) 1 ∧ leWe f ∣ veblen (Om (1 + 1)) 1 := by
  have hG := gg_veblen_eps (x := Om (1 + 1 : Ordinal.{0})) (y := 1) ldOm2_SC.1.ne'
  have hk : Om (1 + 1) * f < veblen (Om (1 + 1)) 1 := by
    calc Om (1 + 1) * f ≤ ω ^ Om (1 + 1) * ω ^ f :=
          mul_le_mul' (gg_SC_eps ldOm2_SC).ge (right_le_opow f one_lt_omega0)
      _ = ω ^ (Om (1 + 1) + f) := (opow_add _ _ _).symm
      _ < ω ^ veblen (Om (1 + 1)) 1 :=
          (opow_lt_opow_iff_right one_lt_omega0).2 (Ph.ph_veblen_prin _ _ Tg.tgOm_lt_G hf)
      _ = veblen (Om (1 + 1)) 1 := hG
  refine ⟨?_, ?_⟩
  · unfold leWe; rw [← hG]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hk
  · unfold leWe; rw [← hG]; exact opow_dvd_opow ω hk.le

/-- `Ω^x < Ĝ` and `Ω^x ∣ Ĝ` for `x < Ĝ`. -/
theorem tuOe_Gh {x : Ordinal.{0}} (hx : x < veblen (Om 1) 1) :
    leOe x < veblen (Om 1) 1 ∧ leOe x ∣ veblen (Om 1) 1 := by
  have hG := gg_veblen_eps (x := Om (1 : Ordinal.{0})) (y := 1) (Om_pos one_ne_zero).ne'
  have hΩG : Om (1 : Ordinal.{0}) < veblen (Om 1) 1 := (lt_add_one _).trans Tn.tnOm1_lt_Gh
  have hk : Om 1 * x < veblen (Om 1) 1 := by
    calc Om 1 * x ≤ ω ^ Om 1 * ω ^ x :=
          mul_le_mul' (gg_SC_eps Ph.ph_SC_Om1).ge (right_le_opow x one_lt_omega0)
      _ = ω ^ (Om 1 + x) := (opow_add _ _ _).symm
      _ < ω ^ veblen (Om 1) 1 :=
          (opow_lt_opow_iff_right one_lt_omega0).2 (Ph.ph_veblen_prin _ _ hΩG hx)
      _ = veblen (Om 1) 1 := hG
  refine ⟨?_, ?_⟩
  · unfold leOe; rw [← hG]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hk
  · unfold leOe; rw [← hG]; exact opow_dvd_opow ω hk.le

end Googology.Trans.PoR.InaccPsi.R2.Tu
