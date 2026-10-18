import Googology.Trans.PoR.InaccPsi.R2.MwPhi

/-!
# `SfEQlong` at the long codes below `Γ_{Ω₁+1}`: the hull transport with the φ-law

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `ρ_λ = υ_λ`, `δ_λ = υ_{λ+ω+1}`, `η_λ` the name, `e = cdExp(η_λ)`, `m_λ` the
code, `Θ_λ` the reading, `r(λ) = k_λ(Θ_λ(m_λ))`.  `GgCl Z` are the codes over `Z` (from `[0, Z)` and `Ω₁` by `+`,
`φ`), `ggTh Z` their order type, `ggGam = Γ_{Ω₁+1}` the least strongly critical ordinal above `Ω₁` (`R2.GgCl`).

* `mwSC_of_fix` (`φ(x, 0) = x`, `x > 0` gives `x` strongly critical), `mwDec` (**an `ε`-number `x` with
  `Ω₁ < x < ggGam` is `φ(a, b)` with `a, b < x`**);
* `mwGg_move` (**the hull transport below `ggGam`**, by induction on the code): for strongly critical countable
  `ρ, ρ'` with `B_n ρ = ρ'`, a strongly critical `X` with `ρ < X < L(ω)`, and a code `x` over `ρ` below `ggGam`:
  `x ∈ MvD`, `B_n x` is a code over `ρ'` below `ggGam`, `ggTh ρ x < X`, and **`ggTh ρ' (B_n x) = B_n(ggTh ρ x)`**
  (the cases of `Mv.mvGg_move`, and the new case `x = φ(a, b)`: `Ph.phTh_phi` and `Mw.mwB_phi`);
* `mwDelta_SC` (`δ_λ` is strongly critical below `L(ω)`);
* `mwEQlong_gam` (**`B_n r(λ) = r(λ')` at every long code with `e < Γ_{Ω₁+1}`**, given `L(ω+1) ≤ ν_C`);
* `MwEQtop S` (a hypothesis name): `SfEQlong` at the long codes with `Γ_{Ω₁+1} ≤ e`;
  `mwEQlong_top`: `L(ω+1) ≤ ν_C` and `MwEQtop` give `SfEQlong`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Mw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Cx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mv

variable {S : InaccSeq.{0}}

/-- `φ(x, 0) = x` and `x > 0` give `x` strongly critical. -/
theorem mwSC_of_fix {x : Ordinal.{0}} (h0 : 0 < x) (hfix : veblen x 0 = x) : SC x := by
  refine ⟨h0, fun a ha b hb => ?_⟩
  have e : veblen a x = x := by
    conv_lhs => rw [← hfix]
    rw [veblen_veblen_of_lt ha]; exact hfix
  calc veblen a b < veblen a x := veblen_lt_veblen_iff_right.2 hb
    _ = x := e

/-- **An `ε`-number `x` with `Ω₁ < x < ggGam` is `φ(a, b)` with `a, b < x`.** -/
theorem mwDec {x : Ordinal.{0}} (hE : ω ^ x = x) (h1 : Om 1 < x) (hG : x < ggGam) :
    veblen (invVeblen₁ x) (invVeblen₂ x) = x ∧ invVeblen₁ x < x ∧ invVeblen₂ x < x := by
  have hdec : veblen (invVeblen₁ x) (invVeblen₂ x) = x := by rw [veblen_invVeblen₁_invVeblen₂, hE]
  have hb : invVeblen₂ x < x := by have := invVeblen₂_lt x; rwa [hE] at this
  have hle : invVeblen₁ x ≤ x := by
    have := left_le_veblen (invVeblen₁ x) (invVeblen₂ x)
    rwa [hdec] at this
  refine ⟨hdec, lt_of_le_of_ne hle fun e => ?_, hb⟩
  have h0 : 0 < x := lt_of_le_of_lt zero_le h1
  have hfix : veblen x 0 = x := by
    apply le_antisymm
    · calc veblen x 0 ≤ veblen x (invVeblen₂ x) := veblen_le_veblen_iff_right.2 zero_le
        _ = x := by nth_rewrite 1 [← e]; exact hdec
    · exact left_le_veblen x 0
  exact absurd (ggGam_le (mwSC_of_fix h0 hfix) h1) (not_le.2 hG)

theorem mwGam_opow {a : Ordinal.{0}} (ha : a < ggGam) : ω ^ a < ggGam := by
  have := ggGam_spec.1.2 0 ggGam_spec.1.1 a ha
  rwa [veblen_zero_apply] at this

/-- **The hull transport under `B_n` for the codes below `ggGam`.** -/
theorem mwGg_move {k : ℕ} {ρ ρ' X : Ordinal.{0}} (hρ : SC ρ) (hρ1 : ρ < Om 1) (hρ' : SC ρ')
    (hρ'1 : ρ' < Om 1) (hB : Bc.bcB S k ρ = ρ') (hX : SC X) (hρX : ρ < X)
    (hXL : X < Nc.ncL S ω) :
    ∀ x, GgCl ρ x → x < ggGam → MvD S x ∧ GgCl ρ' (Bc.bcB S k x) ∧ Bc.bcB S k x < ggGam ∧
      ggTh ρ x < X ∧ ggTh ρ' (Bc.bcB S k x) = Bc.bcB S k (ggTh ρ x) := by
  have hρL : ρ < Nc.ncL S ω := hρX.trans hXL
  have hXp : IsPrincipal (· + ·) X := hX.isPrincipal
  have hGp : IsPrincipal (· + ·) ggGam := ggGam_spec.1.isPrincipal
  have hXo : ∀ a < X, ω ^ a < X := fun a ha => by
    have := hX.2 0 hX.1 a ha; rwa [veblen_zero_apply] at this
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx hxG
  rcases lt_trichotomy x (Om 1) with hx1 | hx1 | hx1
  · -- a countable code: below `ρ`
    have hxρ : x < ρ := hx.lt_of_lt_Om1 hρ hx1
    have hxL : x < Nc.ncL S ω := hxρ.trans hρL
    have hBx : Bc.bcB S k x < ρ' := by rw [← hB]; exact (Bc.bcB_lt_iff hxL hρL).2 hxρ
    refine ⟨mvD_of_lt hxL, GgCl.small hBx, hBx.trans (hρ'1.trans ggGam_spec.2), ?_, ?_⟩
    · rw [ggTh_small hxρ.le]; exact hxρ.trans hρX
    · rw [ggTh_small hxρ.le, ggTh_small hBx.le]
  · -- `Ω₁`
    subst hx1
    obtain ⟨hD, hBO⟩ := mvB_Om1 (S := S) (k := k)
    refine ⟨hD, by rw [hBO]; exact GgCl.om, by rw [hBO]; exact ggGam_spec.2, ?_, ?_⟩
    · rw [ggTh_Om1 hρ hρ1]; exact hρX
    · rw [hBO, ggTh_Om1 hρ hρ1, ggTh_Om1 hρ' hρ'1, hB]
  · have hx0 : x ≠ 0 := (lt_of_le_of_lt zero_le hx1).ne'
    by_cases hE : ω ^ x = x
    · -- `x = φ(a, b)` with `a, b < x`
      obtain ⟨hdec, hax, hbx⟩ := mwDec hE hx1 hxG
      set a := invVeblen₁ x with ha_def
      set b := invVeblen₂ x with hb_def
      obtain ⟨hga, hgb⟩ := Ph.phDec hρ.1 hx a b hdec hbx
      obtain ⟨hDa, hga', haG, hta, hea⟩ := IH a hax hga (hax.trans hxG)
      obtain ⟨hDb, hgb', hbG, htb, heb⟩ := IH b hbx hgb (hbx.trans hxG)
      have hax' : a < veblen a b := by rw [hdec]; exact hax
      have hbx' : b < veblen a b := by rw [hdec]; exact hbx
      obtain ⟨hDx, hBx⟩ := mwB_phi (k := k) hDa hDb hax' hbx'
      have hth : ggTh ρ (veblen a b) = veblen (ggTh ρ a) (ggTh ρ b) := Ph.phTh_phi hρ a hga b hgb
      have hta' : ggTh ρ a < veblen (ggTh ρ a) (ggTh ρ b) := by
        rw [← hth]; exact ggTh_lt hga hax'
      have htb' : ggTh ρ b < veblen (ggTh ρ a) (ggTh ρ b) := by
        rw [← hth]; exact ggTh_lt hgb hbx'
      obtain ⟨-, hBt⟩ := mwB_phi (k := k) (mvD_of_lt (hta.trans hXL)) (mvD_of_lt (htb.trans hXL)) hta' htb'
      rw [← hdec]
      refine ⟨hDx, ?_, ?_, ?_, ?_⟩
      · rw [hBx]; exact GgCl.phi hga' hgb'
      · rw [hBx]; exact ggGam_spec.1.2 _ haG _ hbG
      · rw [hth]; exact hX.2 _ hta _ htb
      · rw [hBx, Ph.phTh_phi hρ' _ hga' _ hgb', hea, heb, hth, hBt]
    · -- `x` is not an `ε`-number: `x = ω^a` or `x = ω^a + r`
      obtain ⟨a, ha⟩ : ∃ a, a = log ω x := ⟨_, rfl⟩
      have hlead : ω ^ a ≤ x := by rw [ha]; exact opow_log_le_self ω hx0
      have hxlt : x < ω ^ a * ω := by
        rw [← opow_succ, ha]; exact lt_opow_succ_log_self one_lt_omega0 x
      have hga : GgCl ρ a := by rw [ha]; exact (ggDec hρ x hx).2
      have hgl : GgCl ρ (ω ^ a) := GgCl.opow hρ.1 hga
      have hgr : GgCl ρ (x - ω ^ a) := (ggDec hρ x hx).1 _ hgl hlead
      have hdec : ω ^ a + (x - ω ^ a) = x := Ordinal.add_sub_cancel_of_le hlead
      by_cases hr : x - ω ^ a = 0
      · have hxa : ω ^ a = x := by rw [hr, add_zero] at hdec; exact hdec
        have hax : a < x := by
          rcases (right_le_opow a one_lt_omega0).lt_or_eq with h | h
          · rwa [hxa] at h
          · exfalso; apply hE; rw [← hxa]; exact congrArg (ω ^ ·) h.symm
        obtain ⟨hDa, hga', haG, hta, hea⟩ := IH a hax hga (hax.trans hxG)
        have hne : ω ^ a ≠ a := fun h => hax.ne (h.symm.trans hxa)
        obtain ⟨hDx, hBx⟩ := mvB_opow (k := k) hDa hne
        subst hxa
        have hta' : ω ^ ggTh ρ a < X := hXo _ hta
        refine ⟨hDx, ?_, ?_, ?_, ?_⟩
        · rw [hBx]; exact GgCl.opow hρ'.1 hga'
        · rw [hBx]; exact mwGam_opow haG
        · rw [ggTh_opow hρ hga]; exact hta'
        · rw [hBx, ggTh_opow hρ' hga', hea, ggTh_opow hρ hga, Tp.tpOpowB (hta'.trans hXL)]
      · obtain ⟨r, hr'⟩ : ∃ r, r = x - ω ^ a := ⟨_, rfl⟩
        rw [← hr'] at hgr hdec hr
        have hlx : ω ^ a < x := by
          rw [← hdec]; exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hr)
        have hrx : r < x := by
          refine lt_of_le_of_ne (by rw [← hdec]; exact le_add_self) fun e => ?_
          have h' : ω ^ a + x = x := by
            calc ω ^ a + x = ω ^ a + r := by rw [e]
              _ = x := hdec
          have := Ordinal.add_eq_right_iff_mul_omega0_le.1 h'
          exact absurd (lt_of_lt_of_le hxlt this) (lt_irrefl _)
        obtain ⟨hDl, hgl', hlG, htl, hel⟩ := IH _ hlx hgl (hlx.trans hxG)
        obtain ⟨hDr, hgr', hrG, htr, her⟩ := IH r hrx hgr (hrx.trans hxG)
        obtain ⟨hDx, hBx⟩ := mvB_add (k := k) hDl hDr
        have hts : ggTh ρ (ω ^ a + r) = ggTh ρ (ω ^ a) + ggTh ρ r := ggTh_add hρ hgl r
        rw [← hdec]
        refine ⟨hDx, ?_, ?_, ?_, ?_⟩
        · rw [hBx]; exact GgCl.add hgl' hgr'
        · rw [hBx]; exact hGp hlG hrG
        · rw [hts]; exact hXp htl htr
        · rw [hBx, ggTh_add hρ' hgl', hel, her, hts, Bc.bcB_add (htl.trans hXL) (htr.trans hXL)]

/-- `δ_λ` is strongly critical when it is below `L(ω)`. -/
theorem mwDelta_SC {l : Ordinal.{0}} (h : cdDelta l < Nc.ncL S ω) : SC (cdDelta l) := by
  have hX : upsilon (l + ω + 1) < Nm.Pv S (Om ω + Nc.ncPp S * ω) := by
    rw [← Lw.lw_L_eq S]; exact h
  exact mvUps_SC (Order.succ_ne_bot _) hX

/-- **`B_n r(λ) = r(λ')` at every long code `m_λ` with `e(η_λ) < Γ_{Ω₁+1}`**, given `L(ω+1) ≤ ν_C`. -/
theorem mwEQlong_gam (hν : Nc.ncL S (ω + 1) ≤ nuC) {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l)
    (h1 : Bc.bcC S n < upsilon l) (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l')
    (hB : Bc.bcB S n (upsilon l) = upsilon l') (hm : upsilon l < cdCode S l)
    (he : cdExp (cdEta S l) < ggGam) : Bc.bcB S n (cdR S l) = cdR S l' := by
  have hl := hR.1
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hX : upsilon l < Nm.Pv S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0})) := by
    rw [← Lw.lw_L_eq S]; exact h2
  have hX' : upsilon l' < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S, ← hB]; exact Bc.bcB_bound' S n _ h2
  obtain ⟨hρSC, hρ1⟩ := mvNamed_SC hl hX
  obtain ⟨hρSC', hρ1'⟩ := mvNamed_SC hl' hX'
  obtain ⟨e, he_def⟩ : ∃ e, e = cdExp (cdEta S l) := ⟨_, rfl⟩
  rw [← he_def] at he
  have hge : GgCl (upsilon l) e := by rw [he_def]; exact mvCode_mem hl hX (he_def ▸ he)
  have hδSC : SC (cdDelta l) := mwDelta_SC (hδr.trans hLw)
  obtain ⟨hDe, -, heG', hte, hθe⟩ := mwGg_move (k := n) hρSC hρ1 hρSC' hρ1' hB hδSC
    (cdRho_lt_delta l) (hδr.trans hLw) e hge he
  -- the last exponent moves
  have hθ : ggGam ≤ ConjT.th S := ggGam_le (ConjT.SC_th S) (psiS_bounds (S := S) (Om ω) 1).1
  obtain ⟨η', -, hBη', hη', hexp'⟩ := mvExp_move hl.1 h1 h2 (he_def ▸ he.trans_le hθ) (he_def ▸ hDe.1)
  rw [← he_def] at hexp'
  have hl'eq : l' = Bt.iota S η' := Tp.tpUps_inj (hB.symm.trans hBη')
  -- the codes
  have hωC : (ω : Ordinal.{0}) < Bc.bcC S n := Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)
  have hωe : (ω : Ordinal.{0}) < e := by
    have hce : cdCode S l ≤ e := by rw [he_def]; exact cdCodeOf_le_exp S _
    exact (hωC.trans h1).trans (hm.trans_le hce)
  have hO2 : e < Om (1 + 1) := he.trans (ggGam_lt_Om2 S)
  have hcode : cdCode S l = e := by
    show cdCodeOf S (cdEta S l) = e
    rw [cdCodeOf_of_lt (he_def ▸ hO2), ← he_def]
    unfold cdOff; rw [if_neg (not_lt.2 hωe.le)]
  have hBω : (ω : Ordinal.{0}) < Bc.bcB S n e := by
    have hωL : (ω : Ordinal.{0}) < Nc.ncL S ω := hωC.trans (Bc.bcC_lt S n)
    have := (mvB_lt_iff (k := n) (mvD_of_lt hωL) hDe).2 hωe
    rwa [Bc.bcB_fix hωC] at this
  have hcode' : cdCode S l' = Bc.bcB S n e := by
    rw [hl'eq]
    show cdCodeOf S (cdEta S (Bt.iota S η')) = _
    rw [hη', cdCodeOf_of_lt (hexp' ▸ heG'.trans (ggGam_lt_Om2 S)), hexp']
    unfold cdOff; rw [if_neg (not_lt.2 hBω.le)]
  -- the readings
  have hΘ : cdTheta S l (cdCode S l) = ggTh (upsilon l) e := by
    rw [hcode]; exact mvTheta_eq hl hX he.le
  have hΘ' : cdTheta S l' (cdCode S l') = ggTh (upsilon l') (Bc.bcB S n e) := by
    rw [hcode']; exact mvTheta_eq hl' hX' heG'.le
  show Bc.bcB S n (cdk l (cdTheta S l (cdCode S l))) = cdk l' (cdTheta S l' (cdCode S l'))
  rw [hΘ, hΘ', hθe]
  exact (mvk_move hν hl hl' h1 hδr hB hte).symm

/-- `SfEQlong` at the long codes with `Γ_{Ω₁+1} ≤ e(η_λ)`. -/
def MwEQtop (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    ggGam ≤ cdExp (cdEta S l) → Bc.bcB S n (cdR S l) = cdR S l'

/-- **`L(ω+1) ≤ ν_C` and `MwEQtop` give `SfEQlong`.** -/
theorem mwEQlong_top (hν : Nc.ncL S (ω + 1) ≤ nuC) (htop : MwEQtop S) : Sf.SfEQlong S := by
  intro n l l' hR h1 hr hl' hB hm
  by_cases he : cdExp (cdEta S l) < ggGam
  · exact mwEQlong_gam hν hR h1 hr hl' hB hm he
  · exact htop n l l' hR h1 hr hl' hB hm (not_lt.1 he)

/-- **`MwEQtop` gives `MvEQtop`** under `L(ω+1) ≤ ν_C` (so `MwEQtop` is the weaker hypothesis). -/
theorem mwEQtop_mv (hν : Nc.ncL S (ω + 1) ≤ nuC) (htop : MwEQtop S) : MvEQtop S :=
  fun n l l' hR h1 hr hl' hB hm _ => mwEQlong_top hν htop n l l' hR h1 hr hl' hB hm

end Googology.Trans.PoR.InaccPsi.R2.Mw
