import Googology.Trans.PoR.InaccPsi.R2.GkU2

/-!
# CODES BELOW `ζ_{Ω₁+1}`: readings below `ζ_{x+1} ≤ Γ_{x+1}`, cofinality, countability

* `gu_evA_lt_gq0` (**every `ε_{x+a}`, `a < ζ_{x+1}`, lies below `Γ_{x+1}`**, from `Lx.lx_vt_lt_G`), `guR_lt_evZ`
  (**every reading lies below `ζ_{x+1} = evZ x`**), `guR_lt0`;
* `guR_pow` (the reading of `E^k`), `gu_omega_le` (an infinite code has an infinite reading), `guR_one_add`;
* `GuCof`, `gu_lim_of_cof`, `gu_baseCof` (**the codes below `ε_{Ω₁+n}` have readings cofinal in `ε_{x+n(x)}`**:
  `n = 1` by the towers of `R2.GhEps`, `n` a successor by the towers `E', E'^{E'}, …`, `n` a limit by cofinality at
  `n`), `gu_cofPow`, `guR_cof` (**cofinality**, one induction), `guR_cofE` (the field `cof`);
* `gu_count` (the codes with gate below `y` below a code are countably many).

No new axiom.  New definition: `GuCof`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gk

open Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Gi
  Googology.Trans.PoR.InaccPsi.R2.Gb
open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2

section Lt0

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem gu_gq0_eq : gq 0 x = lgG x := by
  have e : gq 0 x = Lp.gk 0 x := by rw [← gq_nat, Nat.cast_zero]
  rw [e, Ga.gk_zero_eq hx hx1]

/-- **Every `ε_{x+a}` with `a < ζ_{x+1}` lies below `Γ_{x+1}`.** -/
theorem gu_evA_lt_gq0 : ∀ a, a < evZ x → evA x a < gq 0 x := by
  rw [gu_gq0_eq hx hx1]
  obtain ⟨-, hxG, -, hGE, -⟩ := lgG_facts hx hx1
  have hGl : IsSuccLimit (lgG x) := ev_isSuccLimit_of_inE hGE
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH =>
  intro haZ
  rcases zero_or_succ_or_isSuccLimit a with h0 | ⟨a', ha'⟩ | hlim
  · rw [h0, evA_zero hx]; exact hxG
  · rw [succ_eq_add_one] at ha'
    have ha'a : a' < a := by rw [← ha']; exact lt_add_one a'
    have h1 := IH a' ha'a (ha'a.trans haZ)
    have hσ : a' + 1 < lgG x := hGl.add_one_lt ((le_evA_idx x a').trans_lt h1)
    have h2 := Lx.lx_vt_lt_G hx hx1 hσ
    rw [vt_Om1_add_evZ hx hx1 (by rw [ha']; exact haZ)] at h2
    rw [← ha']
    exact (evA_le_iff.2 le_add_self).trans_lt h2
  · have hle : a ≤ lgG x := by
      refine le_of_forall_lt fun b hb => ?_
      exact (le_evA_idx x b).trans_lt (IH b hb (hb.trans haZ))
    have hlt : a < lgG x := by
      rcases hle.lt_or_eq with h | h
      · exact h
      · exfalso
        have hfix : evA x a ≤ a := by
          rw [evA_lim x hlim]
          exact Ordinal.iSup_le fun b => (IH b.1 b.2 (b.2.trans haZ)).le.trans (le_of_eq h.symm)
        exact absurd (lt_evA_self hx haZ) (not_lt.2 hfix)
    have hω : ω ≤ a := omega0_le_of_isSuccLimit hlim
    have h2 := Lx.lx_vt_lt_G hx hx1 hlt
    rwa [vt_Om1_add_evZ hx hx1 haZ, one_add_of_omega0_le hω] at h2

theorem gu_guA_lt_gq0 {m : Ordinal.{0}} (hm : 1 ≤ m) (hmZ : m < evZ x) : guA x m < gq 0 x := by
  rw [guA_eq hx hm]; exact gu_evA_lt_gq0 hx hx1 m hmZ

end Lt0

/-- **Every reading lies below `ζ_{x+1}`.** -/
theorem guR_lt_evZ {x : Ordinal.{0}} (hx : InE x) : ∀ c, c < guB → guG c < x → guR c x < evZ x := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  rcases lt_or_ge c gfE with hcE | hcE
  · rw [guG_low hcE] at hg
    rw [guR_low hcE]
    refine (rdc_lt_eN hx c hg).trans ?_
    have h1 : (1 : Ordinal.{0}) < evZ x := (one_lt_omega0.trans (omega0_lt_inE hx)).trans (lt_evZ x)
    have := evA_lt_evZ hx h1
    rwa [show (1 : Ordinal.{0}) = 0 + 1 by simp, evA_add_one, evA_zero hx] at this
  obtain ⟨-, -, -, hnB, hnc⟩ := guN_spec hcE hc
  obtain ⟨g0, -, -, -⟩ := gu_parts_g (omega0_lt_inE hx) hcE hc hg
  have hn := IH _ hnc hnB g0
  have h1 := guR_top hx hc hcE hg
  rw [guA_eq hx (le_add_self)] at h1
  exact h1.trans (evA_lt_evZ hx ((ev_isSuccLimit_of_inE (evZ_E x)).add_one_lt hn))

theorem guR_lt0 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {c : Ordinal.{0}} (hc : c < guB)
    (hg : guG c < x) : guR c x < gq 0 x := by
  rcases lt_or_ge c gfE with hcE | hcE
  · rw [guG_low hcE] at hg
    rw [guR_low hcE]
    exact (rdc_lt_eN hx c hg).trans (gh_eN_lt_gq0 hx hx1)
  obtain ⟨-, -, -, hnB, hnc⟩ := guN_spec hcE hc
  obtain ⟨g0, -, -, -⟩ := gu_parts_g (omega0_lt_inE hx) hcE hc hg
  have hn := guR_lt_evZ hx _ hnB g0
  exact (guR_top hx hc hcE hg).trans (gu_guA_lt_gq0 hx hx1 le_add_self
    ((ev_isSuccLimit_of_inE (evZ_E x)).add_one_lt hn))

/-! ## Powers, `1 + a` -/

/-- **The reading of `E^k`** (`E = ε_{Ω₁+m}`, `k ≠ 0`, `E^k < ε_{E+1}`): `ε_{x+m(x)}^{k(x)}`; gate `max(Q m, Q k)`. -/
theorem guR_pow {m k : Ordinal.{0}} (hm : 1 ≤ m) (hk : k ≠ 0) (hv : evA Om1 m ^ k < evA Om1 (m + 1))
    (hB : evA Om1 m ^ k < guB) :
    (∀ x, guR (evA Om1 m ^ k) x = guA x (guR m x) ^ guR k x) ∧ guG (evA Om1 m ^ k) = max (guQ m) (guQ k) := by
  have hE1 : (1 : Ordinal.{0}) < evA Om1 m := Lu.lu_one_lt_E (evA_E _ _)
  have e : evA Om1 m ^ k = evA Om1 m ^ k * 1 + 0 := by rw [mul_one, add_zero]
  have hr : (0 : Ordinal.{0}) < evA Om1 m ^ k := opow_pos _ (evA_E _ _).pos
  refine ⟨fun x => ?_, ?_⟩
  · rw [e, guR_cnf hm hk one_ne_zero hE1 hr (e ▸ hv) (e ▸ hB), guR_one, guR_zero, mul_one, add_zero]
  · rw [e, guG_cnf hm hk one_ne_zero hE1 hr (e ▸ hv) (e ▸ hB), guQ_one, guG_zero]
    simp

theorem guR_pos' {x c : Ordinal.{0}} (hx : InE x) (hc0 : c ≠ 0) (hc : c < guB) : 1 ≤ guR c x :=
  one_le_iff_pos.2 (guR_pos hx c hc0 hc)

/-- **An infinite code has an infinite reading.** -/
theorem gu_omega_le {x a : Ordinal.{0}} (hx : InE x) (ha : ω ≤ a) (haB : a < guB) : ω ≤ guR a x := by
  rcases lt_or_ge a gfE with haE | haE
  · rw [guR_low haE]
    rcases lt_or_ge a Om1 with ha1 | ha1
    · rw [(rdc_const ha1 x).1]; exact ha
    have ha0 : a ≠ 0 := (lt_of_lt_of_le omega0_pos ha).ne'
    obtain ⟨hq, -, -, -, -, -⟩ := parts ha0
    have hl0 : log Om1 a ≠ 0 :=
      (lt_of_lt_of_le zero_lt_one (le_log_of_opow_le gf_one_lt_Om1 (by rw [opow_one]; exact ha1))).ne'
    have hlE : log Om1 a < gfE := (log_le_self Om1 a).trans_lt haE
    rw [rdc_dec ha0 haE]
    calc ω ≤ x := (omega0_lt_inE hx).le
      _ = x ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ x ^ rdc (log Om1 a) x := opow_le_opow_right hx.pos (one_le_iff_pos.2 (rdc_pos hx hl0 hlE))
      _ ≤ x ^ rdc (log Om1 a) x * (a / Om1 ^ log Om1 a) := le_mul_of_one_le_right' (one_le_iff_pos.2 hq)
      _ ≤ _ := le_self_add
  calc ω ≤ eN x := omega0_le_eN x
    _ ≤ guA x (guR (guN a) x) := gu_eN_le_guA x (gu_one_le_N hx haE haB)
    _ ≤ guR a x := (gu_lead hx haE haB).2

theorem guR_one_add {x a : Ordinal.{0}} (hx : InE x) (haB : a < guB) : guR (1 + a) x = 1 + guR a x := by
  rcases lt_or_ge a ω with haω | haω
  · obtain ⟨n, hn⟩ := lt_omega0.1 haω
    have : (1 : Ordinal.{0}) + n = ((1 + n : ℕ) : Ordinal.{0}) := by push_cast; rfl
    rw [hn, this, guR_nat, guR_nat]; push_cast; rfl
  · rw [one_add_of_omega0_le haω, one_add_of_omega0_le (gu_omega_le hx haω haB)]

/-! ## Cofinality -/

/-- Cofinality at the code `j`: every `ν` below its reading is at most the reading of a smaller code. -/
def GuCof (x j : Ordinal.{0}) : Prop :=
  guG j < x → ∀ ν, ν < guR j x → ∃ b, b < j ∧ guG b < x ∧ ν ≤ guR b x

section Cof

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx

/-- **A limit code has a limit reading.** -/
theorem gu_lim_of_cof {κ : Ordinal.{0}} (hl : IsSuccLimit κ) (hκB : κ < guB) (hg : guG κ < x)
    (hc : GuCof x κ) : IsSuccLimit (guR κ x) := by
  have hκ0 : κ ≠ 0 := hl.bot_lt.ne'
  rcases zero_or_succ_or_isSuccLimit (guR κ x) with h0 | ⟨ν, hν⟩ | hlim
  · exact absurd h0 (guR_pos hx κ hκ0 hκB).ne'
  · exfalso
    rw [succ_eq_add_one] at hν
    obtain ⟨b, hb, hgb, hνb⟩ := hc hg ν (by rw [← hν]; exact lt_add_one ν)
    have hbκ : guR b x < guR κ x := guR_mono hx hκB hb hg hgb
    have hbe : guR b x = ν := le_antisymm (Order.lt_add_one_iff.1 (hν ▸ hbκ)) hνb
    have hb1 : b + 1 < κ := hl.add_one_lt hb
    have hgb1 : guG (b + 1) < x := guG_succ (ev_isSuccLimit_of_inE hx) b (hb1.trans hκB) hgb
    have := guR_mono hx hκB hb1 hg hgb1
    rw [guR_succ b (hb1.trans hκB), hbe, hν] at this
    exact lt_irrefl _ this
  · exact hlim

omit hx in
theorem gu_sub_one_ge {a R : Ordinal.{0}} (h : a + 1 ≤ R) : a ≤ R - 1 := by
  have h1R : 1 ≤ R := le_trans le_add_self h
  have e := Ordinal.add_sub_cancel_of_le h1R
  rcases lt_or_ge a ω with haω | haω
  · obtain ⟨n, rfl⟩ := lt_omega0.1 haω
    rw [← e] at h
    have : (n : Ordinal.{0}) + 1 = 1 + n := by
      rw [show ((n : Ordinal.{0}) + 1) = ((n + 1 : ℕ) : Ordinal.{0}) by push_cast; rfl,
        show ((1 : Ordinal.{0}) + n) = ((1 + n : ℕ) : Ordinal.{0}) by push_cast; rfl, Nat.add_comm]
    rw [this] at h
    exact (add_le_add_iff_left 1).1 h
  · have hR1 : ω ≤ R - 1 := by
      by_contra hc
      push Not at hc
      obtain ⟨m, hm⟩ := lt_omega0.1 hc
      have : R < ω := by
        rw [← e, hm]
        exact (natCast_lt_omega0 (1 + m)).trans_le' (by push_cast; rfl)
      exact absurd ((haω.trans le_self_add).trans h) (not_le.2 this)
    rw [← e, one_add_of_omega0_le hR1] at h
    exact le_self_add.trans h

/-- **The codes below `ε_{Ω₁+n}` have readings cofinal in `ε_{x+n(x)}`**, given cofinality at `n`. -/
theorem gu_baseCof {n : Ordinal.{0}} (hn1 : 1 ≤ n) (hnB : n < guB) (hgn : guG n < x) (hcn : GuCof x n) :
    ∀ ν, ν < guA x (guR n x) → ∃ t, t < evA Om1 n ∧ guG t < x ∧ ν < guR t x := by
  have hωx := omega0_lt_inE hx
  intro ν hν
  rcases zero_or_succ_or_isSuccLimit n with h0 | ⟨n', hn'⟩ | hlim
  · exact absurd (h0 ▸ hn1) (not_le.2 zero_lt_one)
  · rw [succ_eq_add_one] at hn'
    rcases eq_or_ne n' 0 with h0 | hn'0
    · -- `n = 1`: the towers below `ε_{Ω₁+1}`
      have hn : n = 1 := by rw [← hn', h0, zero_add]
      rw [hn, guR_one, guA_one] at hν
      obtain ⟨i, hi⟩ := ghTw_cof hx hν
      refine ⟨ghTw i, by rw [hn, gu_evA_one]; exact ghTw_lt i, ?_, ?_⟩
      · rw [guG_low (ghTw_lt i)]; exact (ghTw_gtc i).trans_lt (Lu.lu_one_lt_E hx)
      · rw [guR_low (ghTw_lt i)]; exact hi
    -- `n = n' + 1`: the towers over `E' = ε_{Ω₁+n'}`
    have hn'1 : 1 ≤ n' := one_le_iff_ne_zero.2 hn'0
    have hn'n : n' < n := by rw [← hn']; exact lt_add_one n'
    have hn'B : n' < guB := hn'n.trans hnB
    have hgn' : guG n' < x := (guG_le_succ n' (hn' ▸ hnB)).trans_lt (hn' ▸ hgn)
    set E' := evA Om1 n' with hE'def
    have hE' : InE E' := evA_E _ _
    have hEn : evA Om1 n = eN E' := by rw [← hn', evA_add_one]
    set B' := guA x (guR n' x) with hB'def
    have hB' : InE B' := guA_E _ _
    rw [← hn', guR_succ n' (hn' ▸ hnB), guA_succ x (guR_pos' hx hn'0 hn'B)] at hν
    -- the towers `T 0 = E'`, `T (i+1) = E'^{T i}`
    let T : ℕ → Ordinal.{0} := fun i => (fun a => E' ^ a)^[i] E'
    have hT : ∀ i : ℕ, T i < eN E' ∧ T i ≠ 0 ∧ guG (T i) < x ∧ (fun a => B' ^ a)^[i] B' ≤ guR (T i) x := by
      intro i
      induction i with
      | zero =>
        refine ⟨lt_eN E', hE'.pos.ne', ?_, ?_⟩
        · show guG E' < x
          rw [guG_base hn'1 hn'B]; exact (guQ_le _).trans_lt hgn'
        · show B' ≤ guR E' x
          rw [guR_base hn'1 hn'B]
      | succ i ih =>
        obtain ⟨h1, h2, h3, h4⟩ := ih
        have hpow : E' ^ T i < eN E' := gu_pow_lt_eN hE' h1
        have hpB : E' ^ T i < guB := hpow.trans_le (by rw [← hEn]; exact (gu_evA_lt hnB).le)
        obtain ⟨hR, hG⟩ := guR_pow hn'1 h2 (by rw [evA_add_one]; exact hpow) hpB
        have e : T (i + 1) = E' ^ T i := Function.iterate_succ_apply' _ _ _
        refine ⟨by rw [e]; exact hpow, by rw [e]; exact opow_ne_zero _ hE'.pos.ne', ?_, ?_⟩
        · rw [e, hG]
          exact max_lt ((guQ_le _).trans_lt hgn') ((guQ_le _).trans_lt h3)
        · rw [e, hR, Function.iterate_succ_apply']
          exact opow_le_opow_right hB'.pos h4
    have hcofT : ∀ i : ℕ, (fun a : Ordinal.{0} => ω ^ a)^[i] (B' + 1) ≤ (fun a => B' ^ a)^[i + 1] B' := by
      intro i
      induction i with
      | zero =>
        show B' + 1 ≤ B' ^ B'
        have : B' ^ (1 : Ordinal.{0}) < B' ^ B' :=
          (opow_lt_opow_iff_right (Lu.lu_one_lt_E hB')).2 (Lu.lu_one_lt_E hB')
        rw [opow_one] at this
        exact add_one_le_of_lt this
      | succ i ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply' (fun a => B' ^ a)]
        calc ω ^ ((fun a : Ordinal.{0} => ω ^ a)^[i] (B' + 1)) ≤ ω ^ ((fun a => B' ^ a)^[i + 1] B') :=
              opow_le_opow_right omega0_pos ih
          _ ≤ B' ^ ((fun a => B' ^ a)^[i + 1] B') :=
              opow_le_opow_left _ (omega0_lt_inE hB').le
    obtain ⟨i, hi⟩ := lt_nfp_iff.1 hν
    obtain ⟨h1, -, h3, h4⟩ := hT (i + 1)
    exact ⟨T (i + 1), by rw [hEn]; exact h1, h3, hi.trans_le ((hcofT i).trans h4)⟩
  · -- `n` a limit: the pseudo-bases `ε_{Ω₁+m}`, `m < n`
    have hRl := gu_lim_of_cof hx hlim hnB hgn hcn
    have hωR : ω ≤ guR n x := omega0_le_of_isSuccLimit hRl
    have hsub : guR n x - 1 = guR n x := by
      have h := Ordinal.add_sub_cancel 1 (guR n x)
      rwa [one_add_of_omega0_le hωR] at h
    rw [guA, hsub, evA_lim _ hRl] at hν
    obtain ⟨⟨a, ha⟩, hνa⟩ := Ordinal.lt_iSup_iff.1 hν
    obtain ⟨m, hmn, hgm, ham⟩ := hcn hgn (a + 1) (hRl.add_one_lt ha)
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [guR_zero] at ham
      exact absurd ham (not_le.2 (lt_of_le_of_lt zero_le (lt_add_one a)))
    have hm1 : 1 ≤ m := one_le_iff_ne_zero.2 hm0
    have hmB : m < guB := hmn.trans hnB
    refine ⟨evA Om1 m, evA_lt_iff.2 hmn, ?_, ?_⟩
    · rw [guG_base hm1 hmB]; exact (guQ_le _).trans_lt hgm
    · rw [guR_base hm1 hmB, guA]
      exact hνa.trans_le (evA_le_iff.2 (gu_sub_one_ge ham))

end Cof

end Googology.Trans.PoR.InaccPsi.R2.Gk
