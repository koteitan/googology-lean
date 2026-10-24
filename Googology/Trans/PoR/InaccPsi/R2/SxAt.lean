import Googology.Trans.PoR.InaccPsi.R2.SuGu
import Googology.Trans.PoR.InaccPsi.R2.GlR8

/-!
# Every ordinal below `Γ_{x+1}` is the reading of a code of `R2.Gl`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`R2.Gl` reads the codes `c < Γ_{Ω₁+1}` at the base `x` (`Gl.glR c x`, an atom `ϑˣ(Ω₁·α(x) + η(x))` for every
`ε`-number code, Cantor normal form above it).  The readings lie below `Γ_{x+1} = lgG x` (the least strongly critical
ordinal above `x`).  Here the converse:

* `sxSC_P` (a strongly critical `b` is in `P_γ` for every `γ < b`), `sxG_le_SC` (**`lgG x` is at most every strongly
  critical `b > x`**: the tops `gT n x` stay below `b` by the minimality of the atoms);
* `sxAtom_ex` (**every `ε`-number `A ∈ (x, Γ_{x+1})` is an atom `ϑˣ(Ω₁·β + t)` with `1 ≤ β` and `β, t < A`**: `β` is
  the Veblen level of `A`, below `A` because no strongly critical ordinal lies in `(x, Γ_{x+1})`, and `t` is the least
  argument whose atom reaches `A`);
* `sxGl_ex` (**every `v < Γ_{x+1}` is `glR c x` for a code `c < Γ_{Ω₁+1}` with gate below `x`**: one induction on
  `v`; `v = A^K·D + W` in the bracket `[A, ε_{A+1})` of its largest `ε`-number `A`, the atom data of `A` and `K, D, W`
  are readings of smaller ordinals, and `glPsi`, `^`, `·`, `+` give the code).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Sx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gk

/-- A strongly critical `b` is a value of `φ_γ` for every `γ < b`. -/
theorem sxSC_P {b γ : Ordinal.{0}} (hb : SC b) (hγ : γ < b) : LuP γ b := by
  have hbE : InE b := Low.opow_eq_self_of_SC hb
  have hbl : IsSuccLimit b := ev_isSuccLimit_of_inE hbE
  have hfix : ∀ δ, δ < b → veblen δ b = b := fun δ hδ =>
    le_antisymm (((isNormal_veblen δ).le_iff_forall_le hbl).2 fun c hc => (hb.2 δ hδ c hc).le)
      (right_le_veblen δ b)
  rcases eq_or_ne γ 0 with rfl | hγ0
  · refine ⟨b, ?_⟩
    rw [veblen_zero_apply]; exact hbE
  · exact (mem_range_veblen hγ0).2 fun δ hδ => hfix δ (hδ.trans hγ)

/-- `ε_{e+1} < Γ_{Ω₁+1}` for `e < Γ_{Ω₁+1}`. -/
theorem sx_eN_lt_G0 {e : Ordinal.{0}} (he : e < gcG 0) : eN e < gcG 0 := by
  have hE : InE (veblen 1 (e + 1)) := by
    have := veblen_veblen_of_lt (o₁ := 0) (o₂ := 1) zero_lt_one (e + 1)
    rw [veblen_zero_apply] at this; exact this
  have h1 : e < veblen 1 (e + 1) := (lt_add_one e).trans_le (right_le_veblen 1 (e + 1))
  exact (eN_le h1 hE).trans_lt (gl_veb_lt_G0 gl_one_lt_G0 (gl_G0_lim.add_one_lt he))

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **`Γ_{x+1}` is at most every strongly critical `b > x`.** -/
theorem sxG_le_SC {b : Ordinal.{0}} (hb : SC b) (hxb : x < b) : lgG x ≤ b := by
  have hbE : InE b := Low.opow_eq_self_of_SC hb
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have h01 : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  have h2b : (2 : Ordinal.{0}) < b := (natCast_lt_omega0 2).trans (omega0_lt_inE hbE)
  have key : ∀ n : ℕ, gT n x < b := by
    intro n
    induction n with
    | zero =>
      show eN x < b
      have h1 : eN x ≤ b := eN_le hxb hbE
      refine lt_of_le_of_ne h1 (fun h => ?_)
      obtain ⟨h1T, h11⟩ := gl_one_T hx hx1
      have hn := glA_notP hx hx1 le_rfl h1T h11 h0T h01
      rw [glA_one_zero hx hx1, h] at hn
      exact hn (sxSC_P hb (by rw [one_add_one_eq_two]; exact h2b))
    | succ n ih =>
      obtain ⟨hgT, hxg, hg1, hgE⟩ := gT_facts hx hx1 n
      have hg1' : (1 : Ordinal.{0}) ≤ gT n x := Order.one_le_iff_pos.2 hgE.pos
      have e : gT (n + 1) x = glA (gT n x) 0 x := by
        show vt x (Om1 * gT n x) = vt x (Om1 * gT n x + 0)
        rw [add_zero]
      rw [e]
      have hle : glA (gT n x) 0 x ≤ b :=
        glA_min hx hx1 hg1' hgT hg1 h0T h01 (sxSC_P hb ih) hxb hbE.pos ih
          (fun σ hσ => absurd hσ (not_lt.2 zero_le))
      refine lt_of_le_of_ne hle (fun h => ?_)
      have hn := glA_notP hx hx1 hg1' hgT hg1 h0T h01
      rw [h] at hn
      exact hn (sxSC_P hb ((ev_isSuccLimit_of_inE hbE).add_one_lt ih))
  exact lgG_le fun n => (key n).le

/-- **Every `ε`-number `A ∈ (x, Γ_{x+1})` is an atom `ϑˣ(Ω₁·β + t)`** with `1 ≤ β`, `β < A`, `t < A`. -/
theorem sxAtom_ex {A : Ordinal.{0}} (hA : InE A) (hxA : x < A) (hAG : A < lgG x) :
    ∃ β t, 1 ≤ β ∧ β < A ∧ t < A ∧ glA β t x = A := by
  have hω : ω ^ A = A := hA
  set β := invVeblen₁ A with hβdef
  have h1 : (1 : Ordinal.{0}) ≤ β := by
    have : ω ^ A ∈ Set.range (veblen (1 : Ordinal.{0})) := by
      rw [hω]; have h := vzP_one.2 hA; unfold VzP at h; rwa [Nat.cast_one] at h
    exact mem_range_veblen_iff_le_invVeblen₁.1 this
  set y := invVeblen₂ A with hy
  have hey : veblen β y = A := by
    have := veblen_invVeblen₁_invVeblen₂ A
    rw [hω] at this; exact this
  have hnot : ¬ LuP (β + 1) A := by
    intro hP
    have : ω ^ A ∈ Set.range (veblen (β + 1)) := by rw [hω]; exact hP
    exact absurd (mem_range_veblen_iff_le_invVeblen₁.1 this) (not_le.2 (lt_add_one β))
  have hβA : β < A := by
    refine lt_of_le_of_ne (invVeblen₁_le A) (fun h => ?_)
    have h2 : veblen A 0 ≤ A := by
      calc veblen A 0 ≤ veblen A y := (veblen_le_veblen_iff_right).2 zero_le
        _ = veblen β y := by rw [h]
        _ = A := hey
    have h3 : veblen A 0 = A := le_antisymm h2 (by simpa using left_le_veblen A 0)
    exact absurd hAG (not_lt.2 (sxG_le_SC hx hx1 (gl_SC_of_fix h3 hA.pos) hxA))
  have hyA : y < A := by
    refine lt_of_le_of_ne (hey ▸ right_le_veblen _ _) (fun h => ?_)
    have : veblen β A = A := by
      calc veblen β A = veblen β y := by rw [h]
        _ = A := hey
    exact hnot (luP_succ.2 this)
  obtain ⟨hβT, hβ1⟩ := gl_T_of_lt_G hx hx1 (hβA.trans hAG)
  obtain ⟨hyT, hy1⟩ := gl_T_of_lt_G hx hx1 (hyA.trans hAG)
  set Sx := {t : Ordinal.{0} | A ≤ glA β t x} with hSx
  have hyS : y ∈ Sx := by
    show A ≤ glA β y x
    rw [← hey]; exact glA_veb_le hx hx1 h1 hβT hβ1 hyT hy1
  have hne : Sx.Nonempty := ⟨y, hyS⟩
  set t := sInf Sx with htdef
  have htS : A ≤ glA β t x := csInf_mem hne
  have hty : t ≤ y := csInf_le' hyS
  have htA : t < A := hty.trans_lt hyA
  obtain ⟨htT, ht1⟩ := gl_T_of_lt_G hx hx1 (htA.trans hAG)
  have hprev : ∀ σ, σ < t → glA β σ x < A := fun σ hσ => by
    have := notMem_of_lt_csInf' hσ
    simpa [hSx] using this
  have hle : glA β t x ≤ A :=
    glA_min hx hx1 h1 hβT hβ1 htT ht1 ⟨y, hey⟩ hxA htA hβA hprev
  exact ⟨β, t, h1, hβA, htA, le_antisymm hle htS⟩

/-- **Every `v < Γ_{x+1}` is the reading of a code `c < Γ_{Ω₁+1}` with gate below `x`.** -/
theorem sxGl_ex : ∀ v, v < lgG x → ∃ c, c < gcG 0 ∧ glG c < x ∧ glR c x = v := by
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  rcases lt_or_ge v (eN x) with hvE | hvE
  · obtain ⟨c, hc, hg, hr⟩ := Sr.srCode_ex hx hx1.le hvE
    exact ⟨c, hc.trans gfE_lt_G0, by rw [glG_low hc]; exact hg, by rw [glR_low hc]; exact hr⟩
  have hxv : x ≤ v := (lt_eN x).le.trans hvE
  obtain ⟨N, -, hN1, hN2⟩ :=
    evA_bracket hx hxv ((lt_add_one v).trans_le (le_evA_idx x (v + 1)))
  have hN0 : N ≠ 0 := by
    rintro rfl
    have e1 : evA x 1 = eN x := by rw [← zero_add (1 : Ordinal.{0}), evA_add_one, evA_zero hx]
    simp only [zero_add, e1] at hN2
    exact absurd hvE (not_le.2 hN2)
  set A := evA x N with hAdef
  have hAE : InE A := evA_E _ _
  have hAs : evA x (N + 1) = eN A := evA_add_one x N
  rw [hAs] at hN2
  have hxA : x < A := by
    have := (evA_lt_iff (x := x)).2 (pos_iff_ne_zero.2 hN0)
    rwa [evA_zero hx] at this
  have hAG : A < lgG x := hN1.trans_lt hv
  have hωx := omega0_lt_inE hx
  -- the atom of `A`
  obtain ⟨β, t, hβ1, hβA, htA, hAt⟩ := sxAtom_ex hx hx1 hAE hxA hAG
  obtain ⟨b, hbB, hgb, hrb⟩ := IH β (hβA.trans_le hN1) ((hβA.trans hAG))
  obtain ⟨τ, hτB, hgτ, hrτ⟩ := IH t (htA.trans_le hN1) ((htA.trans hAG))
  have hb1 : 1 ≤ b := by
    refine Order.one_le_iff_ne_zero.2 fun h0 => ?_
    rw [h0, glR_zero] at hrb
    exact absurd (hrb ▸ hβ1) (not_le.2 zero_lt_one)
  set e := glPsi b τ with hedef
  have he : InE e := glPsi_E hb1 τ
  have hOe : Om1 < e := (glPsi_gt hb1 hbB τ).1
  have heB : e < gcG 0 := glPsi_lt_G hbB hτB
  have hrE : glR e x = A := by
    rw [hedef, glR_psi hb1 hbB hτB, hrb, hrτ, glBA_eq hx hx1, hAt]
  have hgE : glG e < x := by
    rw [hedef, glG_psi hb1 hbB hτB]
    exact max_lt ((glQ_le b).trans_lt hgb) ((glQ_le τ).trans_lt hgτ)
  have hA1 : (1 : Ordinal.{0}) < A := Lu.lu_one_lt_E hAE
  have hv0 : v ≠ 0 := (lt_of_lt_of_le hAE.pos hN1).ne'
  -- `v = A^K·D + W`
  set K := log A v with hKdef
  set D := v / A ^ K with hDdef
  set W := v % A ^ K with hWdef
  have hKv : K < v := gu_log_lt hAE hN1 hN2
  have hK0 : K ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (le_log_of_opow_le hA1 (by rw [opow_one]; exact hN1))).ne'
  have hAK : A ^ K ≤ v := opow_log_le_self A hv0
  have hAK0 : A ^ K ≠ 0 := (opow_pos K hAE.pos).ne'
  have hDA : D < A := div_opow_log_lt v hA1
  have hD0 : D ≠ 0 := (div_opow_log_pos A hv0).ne'
  have hWK : W < A ^ K := Ordinal.mod_lt v hAK0
  have hdec : A ^ K * D + W = v := Ordinal.div_add_mod v (A ^ K)
  obtain ⟨k, hk, hgk, hrk⟩ := IH K hKv (hKv.trans hv)
  obtain ⟨d, hd, hgd, hrd⟩ := IH D (hDA.trans_le hN1) ((hDA.trans_le hN1).trans hv)
  obtain ⟨w, hw, hgw, hrw⟩ := IH W (hWK.trans_le hAK) ((hWK.trans_le hAK).trans hv)
  have hk0 : k ≠ 0 := by rintro rfl; rw [glR_zero] at hrk; exact hK0 hrk.symm
  have hd0 : d ≠ 0 := by rintro rfl; rw [glR_zero] at hrd; exact hD0 hrd.symm
  have hlt_of : ∀ {p q : Ordinal.{0}}, p < gcG 0 → glG p < x → q < gcG 0 → glG q < x →
      glR p x < glR q x → p < q := by
    intro p q hp hgp hq hgq h
    rcases lt_trichotomy p q with h' | h' | h'
    · exact h'
    · rw [h'] at h; exact absurd h (lt_irrefl _)
    · exact absurd h (not_lt.2 (glR_mono hx hx1 hp h' hgp hgq).le)
  have hdE : d < e := hlt_of hd hgd heB hgE (by rw [hrd, hrE]; exact hDA)
  -- `k < ε_{e+1}`
  have hkE : k < eN e := by
    by_contra hke
    push Not at hke
    have hEk : gfE ≤ k := (gfE_le_glPsi hb1 hbB τ).trans ((lt_eN e).le.trans hke)
    have h1 : eN e ≤ guE k := gl_E_max (eN_E e) (hOe.trans (lt_eN e)) hke
    have hgEk : glG (guE k) < x := gl_E_g hEk hk hgk
    have hEkB : guE k < gcG 0 := (gl_E_le hEk).trans_lt hk
    have h2 : glR e x < glR (guE k) x := glR_mono hx hx1 hEkB ((lt_eN e).trans_le h1) hgEk hgE
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h3, -⟩ :=
      gl_eps_read hx hx1 (guE_E k) (gl_Om1_lt_E hEk) hEkB hgEk
    have h4 : eN A ≤ glR (guE k) x := eN_le (hrE ▸ h2) h3
    have h5 : glR (guE k) x ≤ glR k x := by
      rcases (gl_E_le hEk).lt_or_eq with h | h
      · exact (glR_mono hx hx1 hk h hgk hgEk).le
      · rw [h]
    rw [hrk] at h5
    exact absurd (h4.trans h5) (not_le.2 (hKv.trans hN2))
  have hEG : eN e < gcG 0 := sx_eN_lt_G0 heB
  have hEk : e ^ k < eN e := gu_pow_lt_eN he hkE
  have hEkB : e ^ k < gcG 0 := hEk.trans hEG
  obtain ⟨hrEk, hgEk⟩ := gl_pow he hOe hk0 hEk hEkB
  have hbase : glBA (glR (glK e) x) (glR (glI e) x) x = A := by
    rw [← glR_base he hOe heB x, hrE]
  have hQE : glQE e < x := by rw [← glG_base he hOe heB]; exact hgE
  have hgEk' : glG (e ^ k) < x := by
    rw [hgEk]; exact max_lt hQE ((glQ_le k).trans_lt hgk)
  have hrEk' : glR (e ^ k) x = A ^ K := by rw [hrEk x, hbase, hrk]
  have hwE : w < e ^ k := hlt_of hw hgw hEkB hgEk' (by rw [hrw, hrEk']; exact hWK)
  have hv' : e ^ k * d + w < eN e := by
    have hk1 : k + 1 < eN e := (ev_isSuccLimit_of_inE (eN_E e)).add_one_lt hkE
    calc e ^ k * d + w < e ^ k * d + e ^ k := (add_lt_add_iff_left _).2 hwE
      _ = e ^ k * (d + 1) := by rw [mul_add_one]
      _ ≤ e ^ k * e := mul_le_mul_right (Order.add_one_le_of_lt hdE) _
      _ = e ^ (k + 1) := by rw [opow_add, opow_one]
      _ < eN e := gu_pow_lt_eN he hk1
  have hB' : e ^ k * d + w < gcG 0 := hv'.trans hEG
  refine ⟨e ^ k * d + w, hB', ?_, ?_⟩
  · rw [glG_cnf he hOe hk0 hd0 hdE hwE hv' hB']
    exact max_lt (max_lt hQE ((glQ_le k).trans_lt hgk)) (max_lt ((glQ_le d).trans_lt hgd) hgw)
  · rw [glR_cnf he hOe hk0 hd0 hdE hwE hv' hB', hbase, hrk, hrd, hrw]
    exact hdec

end Base

end Googology.Trans.PoR.InaccPsi.R2.Sx
