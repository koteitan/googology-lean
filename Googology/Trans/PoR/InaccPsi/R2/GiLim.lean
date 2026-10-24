import Googology.Trans.PoR.InaccPsi.R2.GiLoc

/-!
# THE LAST TERM OF A LIMIT CODE `c ∈ (ε_{Ω₁+1}, ε_{Ω₁+1}²)`: the data of its union step

For a limit code `c = ε_{Ω₁+1}·γ + a` above `ε_{Ω₁+1}` the reading is `c(x) = l'(x) + ω^{logend(c(x))}` with
`ω^{logend} ∣ l'(x)`, `l'(x) ≤ c'(x)` for a smaller code `c' ≥ ε_{Ω₁+1}` with gate at most that of `c`, and Lemma
IMG for the logend.  Three cases:

* `a` a limit: `logend = logend(a(x))` (the term `tlg l d` of `R2.GfSub`, Lemma IMG `pkg_ot`), `c' = ε_{Ω₁+1}·γ + a'`;
* `a = 0`, `γ = γ' + 1`: `logend = ε_{x+1}` (Lemma IMG `pkg_eN`), `c' = ε_{Ω₁+1}·γ'`;
* `a = 0`, `γ` a limit: `c(x) = ε_{x+1}·γ''(x) + ω^{ε_{x+1} + logend(γ(x))}`, `logend = ε_{x+1} + t(x)` (Lemma IMG
  `pkg_eMt`), `c' = ε_{Ω₁+1}·γ''` (or `ε_{Ω₁+1}` when `γ'' = 0`).

* `giLD_ne` (**the data `GiLD` of `R2.GiRS` exists for every limit code in `(ε_{Ω₁+1}, ε_{Ω₁+1}²)`**).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gi

open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
open Ordinal Order Set Googology.Notation.InaccPsi
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Gb

theorem gi_eN_dvd {x e : Ordinal.{0}} (he : e ≤ eN x) (q : Ordinal.{0}) : ω ^ e ∣ eN x * q := by
  have h1 : ω ^ e ∣ eN x := by
    rw [← show ω ^ eN x = eN x from eN_E x]; exact opow_dvd_opow ω he
  exact dvd_trans h1 (dvd_mul_right _ _)

theorem gi_E_le_mul {γ : Ordinal.{0}} (h : γ ≠ 0) : gfE ≤ gfE * γ := by
  calc gfE = gfE * 1 := (mul_one _).symm
    _ ≤ gfE * γ := mul_le_mul_left' (one_le_iff_ne_zero.2 h) _

/-- **The data exists at every limit code `c ∈ (ε_{Ω₁+1}, ε_{Ω₁+1}²)`.** -/
theorem giLD_ne {c : Ordinal.{0}} (hl : IsSuccLimit c) (hEc : gfE < c) (hc : c < giB) : Nonempty (GiLD giK giR c) := by
  have hγW := gi_div_lt hc
  set γ := c / gfE with hγ
  set a := c % gfE with ha
  have haE : a < gfE := gh_mod_lt c
  have hcdec : c = gfE * γ + a := (gi_dec c).symm
  have hγ0 : γ ≠ 0 := by
    intro h0
    have : c < gfE := by rw [hcdec, h0, mul_zero, zero_add]; exact haE
    exact absurd hEc (not_lt.2 this.le)
  have hgc : giG c = max (giQ γ) (gtc a) := by rw [hcdec, giQ_code haE]
  have hRc : ∀ x, giR c x = eN x * rdc γ x + rdc a x := fun x => by rw [hcdec, giR_code haE]
  rcases eq_or_ne a 0 with ha0 | ha0
  · -- `a = 0`
    have hRc0 : ∀ x, giR c x = eN x * rdc γ x := fun x => by rw [hRc, ha0, rdc_zero, add_zero]
    have hgc0 : giG c = giQ γ := by rw [hgc, ha0, gtc_zero, max_eq_left zero_le]
    rcases zero_or_succ_or_isSuccLimit γ with h0 | ⟨γ', hsucc⟩ | hγl
    · exact absurd h0 hγ0
    · -- `γ = γ' + 1`
      rw [succ_eq_add_one] at hsucc
      have hγ'W : γ' < gfE := (lt_add_one γ').trans (by rw [hsucc]; exact hγW)
      have hγne : γ' ≠ 0 := by
        rintro rfl
        rw [zero_add] at hsucc
        have : c = gfE := by rw [hcdec, ha0, add_zero, ← hsucc, mul_one]
        exact absurd hEc (by rw [this]; exact lt_irrefl _)
      have hRs : ∀ x, giR c x = eN x * rdc γ' x + ω ^ eN x := fun x => by
        rw [hRc0, ← hsucc, (rdc_succ γ' hγ'W x).1, mul_add_one, show ω ^ eN x = eN x from eN_E x]
      have hlg : ∀ x, lg (giR c x) = eN x := fun x => by
        rw [hRs]; exact Ge.lg_add_opow (gi_eN_dvd le_rfl _)
      have hRp : ∀ x, giR (gfE * γ') x = eN x * rdc γ' x := fun x => by
        have := giR_code (γ := γ') eW_E.pos x
        rwa [add_zero, rdc_zero, add_zero] at this
      refine ⟨{
        cp := gfE * γ'
        lp := (fun x => eN x * rdc γ' x)
        cp_ge := (gi_E_le_mul hγne)
        cp_lt := ?_
        cp_g := ?_
        dec := ?_
        pkg := ?_ }⟩
      all_goals try simp only [giK_gt]
      · rw [hcdec, ha0, add_zero, ← hsucc]
        exact (mul_lt_mul_iff_right₀ eW_E.pos).2 (lt_add_one γ')
      · have e1 : giG (gfE * γ') = giQ γ' := by
          have := giQ_code (γ := γ') eW_E.pos
          rwa [add_zero, gtc_zero, max_eq_left zero_le] at this
        rw [e1, hgc0, ← hsucc]
        unfold giQ
        by_cases h1 : γ' < ω
        · rw [if_pos h1]; exact zero_le
        · rw [if_neg h1, if_neg (fun h => h1 ((lt_add_one γ').trans h))]; exact (rdc_succ γ' hγ'W 0).2.1
      · intro x _ _ _
        refine ⟨by rw [hlg x]; exact hRs x, by rw [hlg x]; exact gi_eN_dvd le_rfl _,
          by rw [hlg x]; exact (eN_E x).pos.ne', by rw [hRp x]⟩
      · intro ρ τ δ h hg
        exact GhPkg.congr h (GhPkg.of_img h.pkg_eN) (fun y _ _ _ => (hlg y).symm) hg
    · -- `γ` a limit
      obtain ⟨γ'', l, d, hγ''γ, hg'', hgl, hd, hlW, hF⟩ := rdc_lim_facts hγl hγW
      have hγω : ω ≤ γ := (isSuccLimit_iff_omega0_dvd.1 hγl).2 |> fun h =>
        Ordinal.le_of_dvd hγ0 h
      have hQγ : giQ γ = gtc γ := by unfold giQ; rw [if_neg (not_lt.2 hγω)]
      have hgγ : ∀ x, giG c < x → gtc γ < x := fun x h => by rw [hgc0, hQγ] at h; exact h
      have hdec : ∀ x, InE x → gtc γ < x →
          giR c x = eN x * rdc γ'' x + ω ^ (eN x + OT.ev (tlg l d) x) ∧
            ω ^ (eN x + OT.ev (tlg l d) x) ∣ eN x * rdc γ'' x ∧ lg (giR c x) = eN x + OT.ev (tlg l d) x := by
        intro x hx hgx
        obtain ⟨e1, e2, e3, -, -, -⟩ := hF x hx hgx
        have h1 : giR c x = eN x * rdc γ'' x + ω ^ (eN x + OT.ev (tlg l d) x) := by
          rw [hRc0, e1, mul_add, eN_mul_opow, e3]
        have h2 : ω ^ (eN x + OT.ev (tlg l d) x) ∣ eN x * rdc γ'' x := by
          rw [e3] at e2
          obtain ⟨k, hk⟩ := e2
          exact ⟨k, by rw [hk, ← mul_assoc, eN_mul_opow]⟩
        exact ⟨h1, h2, by rw [h1]; exact Ge.lg_add_opow h2⟩
      have hRp : ∀ x, giR (gfE * γ'') x = eN x * rdc γ'' x := fun x => by
        have := giR_code (γ := γ'') eW_E.pos x
        rwa [add_zero, rdc_zero, add_zero] at this
      refine ⟨{
        cp := if γ'' = 0 then gfE else gfE * γ''
        lp := (fun x => eN x * rdc γ'' x)
        cp_ge := ?_
        cp_lt := ?_
        cp_g := ?_
        dec := ?_
        pkg := ?_ }⟩
      all_goals try simp only [giK_gt]
      · split_ifs with h0
        · exact le_rfl
        · exact gi_E_le_mul h0
      · split_ifs with h0
        · exact hEc
        · rw [hcdec, ha0, add_zero]
          exact (mul_lt_mul_iff_right₀ eW_E.pos).2 hγ''γ
      · split_ifs with h0
        · rw [giG_E]; exact zero_le
        · have e1 : giG (gfE * γ'') = giQ γ'' := by
            have := giQ_code (γ := γ'') eW_E.pos
            rwa [add_zero, gtc_zero, max_eq_left zero_le] at this
          rw [e1, hgc0, hQγ]
          exact (giQ_le γ'').trans hg''
      · intro x hx _ hgx
        obtain ⟨h1, h2, h3⟩ := hdec x hx (hgγ x hgx)
        refine ⟨by rw [h3]; exact h1, by rw [h3]; exact h2, by rw [h3]; exact (add_pos_of_pos_of_nonneg
          (eN_E x).pos zero_le).ne', ?_⟩
        split_ifs with h0
        · rw [h0, rdc_zero, mul_zero]; exact zero_le
        · rw [hRp x]
      · intro ρ τ δ h hg
        have hρE := upsPt_inE h.ρU
        have hgρ := hgγ ρ hg
        obtain ⟨-, -, e3, -, -, e6⟩ := hF ρ hρE hgρ
        have hcb : OT.CB (tlg l d) ρ := cb_tlg hρE.pos (hgl.trans_lt hgρ) (hd.trans_lt hgρ)
        have h1 : 1 ≤ OT.ev (tlg l d) ρ := by rw [← e3]; exact one_le_iff_pos.2 (Gc.gc_lg_pos e6)
        refine GhPkg.congr h (GhPkg.of_img (h.pkg_eMt 0 hcb h1)) (fun y hyE _ hgy => ?_) hg
        rw [(hdec y hyE (hgγ y hgy)).2.2]
        simp [nS]
  · -- `a` a limit
    have hal : IsSuccLimit a := by
      rcases zero_or_succ_or_isSuccLimit a with h0 | ⟨a', hsucc⟩ | hal
      · exact absurd h0 ha0
      · exfalso
        rw [succ_eq_add_one] at hsucc
        have e : c = succ (gfE * γ + a') := by rw [hcdec, ← hsucc, ← add_assoc, succ_eq_add_one]
        rw [e] at hl
        exact Order.not_isSuccLimit_succ _ hl
      · exact hal
    obtain ⟨a', l, d, ha'a, hga', hgl, hd, -, hF⟩ := rdc_lim_facts hal haE
    have ha'E : a' < gfE := ha'a.trans haE
    have hga : ∀ x, giG c < x → gtc a < x := fun x h => by rw [hgc] at h; exact (le_max_right _ _).trans_lt h
    have hdec : ∀ x, InE x → gtc a < x →
        giR c x = (eN x * rdc γ x + rdc a' x) + ω ^ lg (rdc a x) ∧
          ω ^ lg (rdc a x) ∣ eN x * rdc γ x + rdc a' x ∧ lg (giR c x) = lg (rdc a x) ∧ lg (rdc a x) ≠ 0 := by
      intro x hx hgx
      obtain ⟨e1, e2, -, hω, -, e6⟩ := hF x hx hgx
      have hne : rdc a x ≠ 0 := (omega0_pos.trans_le hω).ne'
      have hle : lg (rdc a x) ≤ eN x := (lg_le hne).trans (rdc_lt_eN hx a hgx).le
      have hdv : ω ^ lg (rdc a x) ∣ eN x * rdc γ x + rdc a' x := Ge.dvd_add' (gi_eN_dvd hle _) e2
      have hsum : giR c x = (eN x * rdc γ x + rdc a' x) + ω ^ lg (rdc a x) := by
        rw [hRc, add_assoc, ← e1]
      exact ⟨hsum, hdv, by rw [hsum]; exact Ge.lg_add_opow hdv, (Gc.gc_lg_pos e6).ne'⟩
    refine ⟨{
      cp := gfE * γ + a'
      lp := (fun x => eN x * rdc γ x + rdc a' x)
      cp_ge := (gi_E_le_mul hγ0).trans le_self_add
      cp_lt := ?_
      cp_g := ?_
      dec := ?_
      pkg := ?_ }⟩
    all_goals try simp only [giK_gt]
    · rw [hcdec]; exact (add_lt_add_iff_left _).2 ha'a
    · rw [giQ_code ha'E, hgc]; exact max_le_max le_rfl hga'
    · intro x hx _ hgx
      obtain ⟨h1, h2, h3, h4⟩ := hdec x hx (hga x hgx)
      exact ⟨by rw [h3]; exact h1, by rw [h3]; exact h2, by rw [h3]; exact h4, by rw [giR_code ha'E]⟩
    · intro ρ τ δ h hg
      have hρE := upsPt_inE h.ρU
      have hgρ := hga ρ hg
      obtain ⟨-, -, e3, -, -, e6⟩ := hF ρ hρE hgρ
      have hcb : OT.CB (tlg l d) ρ := cb_tlg hρE.pos (hgl.trans_lt hgρ) (hd.trans_lt hgρ)
      have h1 : 1 ≤ OT.ev (tlg l d) ρ := by rw [← e3]; exact one_le_iff_pos.2 (Gc.gc_lg_pos e6)
      refine GhPkg.congr h (GhPkg.of_img (h.pkg_ot hcb h1)) (fun y hyE _ hgy => ?_) hg
      obtain ⟨-, -, f3, -, -, -⟩ := hF y hyE (hga y hgy)
      rw [(hdec y hyE (hga y hgy)).2.2.1, f3]

end Googology.Trans.PoR.InaccPsi.R2.Gi
