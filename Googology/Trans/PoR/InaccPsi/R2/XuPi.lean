import Googology.Trans.PoR.InaccPsi.R2.XuCof

/-!
# XuPi: CODES BELOW `Γ(1)`: Lemma EXACT at every pair of bases

The atom of an `ε`-number code `e = xuPsi α η ≥ t₀` is `ϑˣ(Ω₁·α(x) + η(x))` with `α(x), η(x) < Γ_{x+2}`, so its base
change is [W07a] Def 5.1 (`Gl.glA_pi`, `Gl.glA_eN_pi`), and the rest is the argument of `R2.GlR6` with the brackets
`e ≥ t₀`; below `t₀` it is Lemma EXACT (`Go.GoD.ex`) and the digit rule (`Go.GoD.dig`) of `Wt.wtD`, the latter usable
since every `ε`-number code `e ≥ t₀` reads at least `ε_{Γ_{x+1}+1}` (`Xu.xu_eps_ge`).

* `xu_mulE` (**`e·κ` is a code**, `(e·κ)(x) = e(x)·κ(x)`), `xu_base_pi`, `xu_BK_pi`, `xu_dig`;
* `xu_pi` (**LEMMA EXACT for every code `c < Γ(1)`** at every pair of bases `σ < ρ` above its gate; no `υ`-point
  hypothesis; one induction).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xu

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Wt Googology.Trans.PoR.InaccPsi.R2.Gk
  Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gm
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Hi

theorem xuQ_one_add (a : Ordinal.{0}) : xuQ (1 + a) = xuQ a := by
  rcases lt_or_ge a ω with ha | ha
  · obtain ⟨n, rfl⟩ := lt_omega0.1 ha
    have : (1 : Ordinal.{0}) + n = ((1 + n : ℕ) : Ordinal.{0}) := by push_cast; rfl
    rw [this, xuQ_nat, xuQ_nat]
  · rw [one_add_of_omega0_le ha]

/-- **`e·κ` as a code** (`e` an `ε`-number code, `1 ≤ κ < ε_{e+1}`). -/
theorem xu_mulE {e : Ordinal.{0}} (he : InE e) (hte : Wj.wjT 0 ≤ e) (heB : e < gcG 1) : ∀ κ, κ ≠ 0 → κ < eN e →
    e * κ < eN e ∧ e * κ < gcG 1 ∧ xuG (e * κ) ≤ max (xuQE e) (xuG κ) ∧
      ∀ x, InE x → x < Om1 → xuG κ < x → xuR (e * κ) x = xuR e x * xuR κ x := by
  have hE1 : (1 : Ordinal.{0}) < e := Lu.lu_one_lt_E he
  have hNB : eN e ≤ gcG 1 := eN_le heB xu_G1_E
  intro κ
  induction κ using WellFoundedLT.induction with
  | ind κ IH =>
  intro hk0 hkN
  have hv : e * κ < eN e := (eN_E e).mul_lt (lt_eN e) hkN
  refine ⟨hv, hv.trans_le hNB, ?_⟩
  rcases lt_or_ge κ e with hkE | hkE
  · have e1 : e * κ = e ^ (1 : Ordinal.{0}) * κ + 0 := by rw [opow_one, add_zero]
    have hr : (0 : Ordinal.{0}) < e ^ (1 : Ordinal.{0}) := opow_pos _ he.pos
    refine ⟨?_, fun x _ _ _ => ?_⟩
    · rw [e1, xuG_cnf he hte one_ne_zero hk0 hkE hr (e1 ▸ hv) (e1 ▸ hv.trans_le hNB), xuQ_one, xuG_zero]
      simp only [zero_le, max_eq_left, max_eq_right]
      exact max_le (le_max_left _ _) ((xuQ_le κ).trans (le_max_right _ _))
    · rw [e1, xuR_cnf he hte one_ne_zero hk0 hkE hr (e1 ▸ hv) (e1 ▸ hv.trans_le hNB), xuR_one, opow_one,
        xuR_zero, add_zero, ← xuR_base he hte heB]
  have hkB : κ < gcG 1 := hkN.trans_le hNB
  obtain ⟨hEk, hgfk⟩ := gl_same he (xu_Om1_lt_t0.trans_le hte) hkE hkN
  have hkt : Wj.wjT 0 ≤ κ := hte.trans hkE
  obtain ⟨ha, hq0, hqE, hs, hdec, hak, hsk, -⟩ := gl_parts hgfk
  rw [hEk] at ha hq0 hqE hs hdec hak hsk
  set a := log e κ with hadef
  set q := κ / e ^ a with hqdef
  set s := κ % e ^ a with hsdef
  have h1a : 1 + a ≠ 0 := (lt_of_lt_of_le zero_lt_one le_self_add).ne'
  have hEs : e * s < e ^ (1 + a) := by
    rw [opow_add, opow_one]; exact (mul_lt_mul_iff_right₀ he.pos).2 hs
  have e1 : e * κ = e ^ (1 + a) * q + e * s := by
    rw [← hdec, mul_add, ← mul_assoc, opow_add, opow_one]
  have hsN : s < eN e := hsk.trans hkN
  have hgEs : xuG (e * s) ≤ max (xuQE e) (xuG s) := by
    rcases eq_or_ne s 0 with h0 | h0
    · rw [h0, mul_zero, xuG_zero]; exact zero_le
    · exact (IH s hsk h0 hsN).2.2.1
  have hgk : xuG κ = max (max (xuQE e) (xuQ a)) (max (xuQ q) (xuG s)) := by
    rw [xuG_dec hkt hkB, hEk]
  refine ⟨?_, fun x hx hx1 hgx => ?_⟩
  · rw [e1, xuG_cnf he hte h1a hq0 hqE hEs (e1 ▸ hv) (e1 ▸ hv.trans_le hNB), xuQ_one_add, hgk]
    refine max_le (max_le (le_max_left _ _) ((le_max_right _ _).trans ((le_max_left _ _).trans
      (le_max_right _ _)))) (max_le ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
      (hgEs.trans (max_le (le_max_left _ _) ((le_max_right _ _).trans ((le_max_right _ _).trans
      (le_max_right _ _))))))
  · have hωx := omega0_lt_inE hx
    obtain ⟨-, g1, -, g3⟩ := xu_parts_g hωx hkt hkB hgx
    rw [hEk] at g1 g3
    rw [e1, xuR_cnf he hte h1a hq0 hqE hEs (e1 ▸ hv) (e1 ▸ hv.trans_le hNB), xuR_dec hkt hkB, hEk,
      ← xuR_base he hte heB]
    have hRs : xuR (e * s) x = xuR e x * xuR s x := by
      rcases eq_or_ne s 0 with h0 | h0
      · rw [h0, mul_zero, xuR_zero, mul_zero]
      · exact (IH s hsk h0 hsN).2.2.2 x hx hx1 g3
    rw [hRs, xuR_one_add hx hx1 (hak.trans hkB) g1, opow_add, opow_one, mul_assoc, ← mul_add]

section Pi

variable {σ ρ : Ordinal.{0}} (hB : Bases σ ρ)
include hB

/-- **`π(e(ρ)) = e(σ)`** for an `ε`-number code `e`, and the same for the next `ε`-number, from Lemma EXACT at its
level and its index. -/
theorem xu_base_pi {e : Ordinal.{0}} (he : InE e) (hte : Wj.wjT 0 ≤ e) (heB : e < gcG 1) (hge : xuG e < σ)
    (hexα : xuR (xuK e) ρ ∈ TB ρ σ ∧ pi σ ρ (xuR (xuK e) ρ) = xuR (xuK e) σ)
    (hex : xuR (xuI e) ρ ∈ TB ρ σ ∧ pi σ ρ (xuR (xuI e) ρ) = xuR (xuI e) σ) :
    xuR e ρ ∈ TB ρ σ ∧ pi σ ρ (xuR e ρ) = xuR e σ ∧
      eN (xuR e ρ) ∈ TB ρ σ ∧ pi σ ρ (eN (xuR e ρ)) = eN (xuR e σ) := by
  have hσE := hB.1
  have hρE := hB.2.1
  have hρ1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨rρ, -, -, -, -, -, hkRρ, -, hk1ρ, -, hη1, -, -⟩ := xu_eps_read hρE hρ1 he hte heB (hge.trans hB.2.2.1)
  obtain ⟨rσ, -, -, -, -, -, -, -, -, -, -, -, -⟩ := xu_eps_read hσE hσ1 he hte heB hge
  obtain ⟨a1, a2⟩ := glA_pi hB hexα.1 hk1ρ hex.1 hη1
  obtain ⟨b1, b2⟩ := glA_eN_pi hB hkRρ hexα.1 hk1ρ hex.1 hη1
  rw [hex.2, hexα.2] at a2 b2
  rw [rρ, rσ]
  exact ⟨a1, a2, b1, b2⟩

/-- **`π(B·K) = B'·K'`** for the atom `B = e(ρ)` of an `ε`-number code and a code `κ` (finite: `pi_mul_nat`; infinite:
the code `e·κ`). -/
theorem xu_BK_pi {e κ : Ordinal.{0}} (he : InE e) (hte : Wj.wjT 0 ≤ e) (heB : e < gcG 1) (hge : xuG e < σ)
    (hκ0 : κ ≠ 0) (hκN : κ < eN e) (hgκ : xuG κ < σ)
    (hexe : xuR e ρ ∈ TB ρ σ ∧ pi σ ρ (xuR e ρ) = xuR e σ)
    (hexm2 : ω ≤ κ → xuR (e * κ) ρ ∈ TB ρ σ ∧ pi σ ρ (xuR (e * κ) ρ) = xuR (e * κ) σ) :
    xuR e ρ * xuR κ ρ ∈ TB ρ σ ∧ pi σ ρ (xuR e ρ * xuR κ ρ) = xuR e σ * xuR κ σ := by
  rcases lt_or_ge κ ω with hω | hω
  · obtain ⟨j, rfl⟩ := lt_omega0.1 hω
    rw [xuR_nat, xuR_nat]
    exact pi_mul_nat hB hexe.1 hexe.2 j
  · obtain ⟨-, -, -, hR⟩ := xu_mulE he hte heB κ hκ0 hκN
    rw [← hR ρ hB.2.1 hB.2.2.2 (hgκ.trans hB.2.2.1), ← hR σ hB.1 (hB.2.2.1.trans hB.2.2.2) hgκ]
    exact hexm2 hω

/-- **The digits**: `π(ω^P·d(ρ)) = ω^{P'}·d(σ)` for every code `d` below an `ε`-number code `e` with gate below `σ`,
once the atoms `ω^{P+β}` (`β ∈ Tᵖ[σ]`, `β < e(ρ)`) are exact and Lemma EXACT holds below `e`. -/
theorem xu_dig {e : Ordinal.{0}} (he : InE e) (hte : Wj.wjT 0 ≤ e) (heB : e < gcG 1) (hge : xuG e < σ)
    (hEX : ∀ j, j < e → xuG j < σ → xuR j ρ ∈ TB ρ σ ∧ pi σ ρ (xuR j ρ) = xuR j σ) :
    ∀ d, d < e → xuG d < σ → ∀ P P' : Ordinal.{0},
      (∀ β, β ∈ TB ρ σ → β < xuR e ρ →
        ω ^ (P + β) ∈ TB ρ σ ∧ pi σ ρ (ω ^ (P + β)) = ω ^ (P' + pi σ ρ β)) →
      ω ^ P * xuR d ρ ∈ TB ρ σ ∧ pi σ ρ (ω ^ P * xuR d ρ) = ω ^ P' * xuR d σ := by
  have hσE := hB.1
  have hρE := hB.2.1
  have hρ1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hωσ := omega0_lt_inE hσE
  have h0T : (0 : Ordinal.{0}) ∈ TB ρ σ := mem_TB_of_lt hB hσE.pos
  have h0pi : pi σ ρ 0 = 0 := pi_lt hB hσE.pos
  have hgeρ : xuG e < ρ := hge.trans hB.2.2.1
  intro d
  induction d using WellFoundedLT.induction with
  | ind d IH =>
  intro hdE hgd P P' hat
  rcases eq_or_ne d 0 with rfl | hd0
  · rw [xuR_zero, xuR_zero, mul_zero, mul_zero]; exact ⟨h0T, h0pi⟩
  have hMρ := xu_mono_top hρE hρ1
  have hge0 : eN (lgG ρ) ≤ xuR e ρ := by
    obtain ⟨-, -, hke, hηe, -⟩ := xu_eps_read hρE hρ1 he hte heB hgeρ
    exact xu_eps_ge hρE hρ1 he hte heB hgeρ (hMρ _ (hke.trans heB)).1 (hMρ _ (hηe.trans heB)).1
  rcases lt_or_ge d (Wj.wjT 0) with hdW | hdW
  · -- a code below `t₀`: the digit rule of `Wt.wtD`
    rw [xuG_low hdW] at hgd
    rw [xuR_low hdW, xuR_low hdW]
    exact wtD.dig σ ρ hB d (xu_lt_wtB hdW) hgd P P' (fun β hβ hβb => hat β hβ (hβb.trans_le hge0))
  -- a code of a lower bracket
  have hdB : d < gcG 1 := hdE.trans heB
  obtain ⟨hk, hd0', -, -, hdec, hkd, hrd, hdd⟩ := gl_parts (xu_gfE_le hdW)
  obtain ⟨g0n, g0k, g0d, g0r⟩ := xu_parts_g hωσ hdW hdB hgd
  have hlt : ∀ j, j < d → j < e := fun j hj => hj.trans hdE
  set ed := guE d with heddef
  have hEdE : InE ed := guE_E d
  have htd : Wj.wjT 0 ≤ ed := xu_E_ge hdW
  have hedd : ed ≤ d := gl_E_le (xu_gfE_le hdW)
  have hedB : ed < gcG 1 := hedd.trans_lt hdB
  have hged : xuG ed < σ := xu_E_g hdW hdB hgd
  have hkN : log ed d < eN ed := hkd.trans (gl_lt_eN (xu_gfE_le hdW))
  have hexe : xuR ed ρ ∈ TB ρ σ ∧ pi σ ρ (xuR ed ρ) = xuR ed σ := by
    rcases hedd.lt_or_eq with h | h
    · exact hEX _ (hlt _ h) hged
    · have hgq : xuQE ed < σ := by rw [xuG_base hEdE htd hedB] at hged; exact hged
      obtain ⟨b1, b2, -, -⟩ := xu_base_pi hB hEdE htd hedB hged
        (hEX _ (hlt _ ((xuData_spec hEdE (xu_G_lt_of htd) hedB).2.1.trans_le hedd))
          (xuG_of_Q hωσ ((xuQE_le_K ed).trans_lt hgq)))
        (hEX _ (hlt _ ((xuData_spec hEdE (xu_G_lt_of htd) hedB).2.2.1.trans_le hedd))
          (xuG_of_Q hωσ ((xuQE_le_I ed).trans_lt hgq)))
      exact ⟨b1, b2⟩
  have hBK := xu_BK_pi hB hEdE htd hedB hged hk hkN g0k hexe (fun hω => by
    have hk1 : 1 < log ed d := lt_of_lt_of_le one_lt_omega0 hω
    have hEkd : ed * log ed d < d := (gu_mulE_lt_pow hEdE hk1 hkN).trans_le (by
      exact (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0')).trans (le_self_add.trans_eq hdec))
    obtain ⟨-, -, hg, -⟩ := xu_mulE hEdE htd hedB _ hk hkN
    refine hEX _ (hlt _ hEkd) (hg.trans_lt (max_lt ?_ g0k))
    rw [xuG_base hEdE htd hedB] at hged; exact hged)
  have hgdρ : xuG d < ρ := hgd.trans hB.2.2.1
  have hlead : xuR ed ρ * xuR (log ed d) ρ < xuR e ρ := by
    have hEdρ := (xu_eps_read hρE hρ1 hEdE htd hedB (hged.trans hB.2.2.1)).2.2.2.2.2.2.2.2.2.2.2.1
    have h1 : xuR ed ρ * xuR (log ed d) ρ ≤ xuR ed ρ ^ xuR (log ed d) ρ := by
      rw [gu_pow_eq hEdρ]; exact right_le_opow _ one_lt_omega0
    have h2 := (xu_lead hρE hρ1 hdW hdB hgdρ).1
    rw [← xu_At_eq hdW hdB] at h2
    have h3 : xuR ed ρ ^ xuR (log ed d) ρ ≤
        xuR ed ρ ^ xuR (log ed d) ρ * xuR (d / ed ^ log ed d) ρ :=
      le_mul_of_one_le_right' (xuR_pos' hρE hρ1 hd0' (hdd.trans hdB) (g0d.trans hB.2.2.1))
    exact (h1.trans (h3.trans h2)).trans_lt (xuR_mono hρE hρ1 heB hdE hgeρ hgdρ)
  have hat' : ∀ β, β ∈ TB ρ σ → β < xuR e ρ →
      ω ^ ((P + xuR ed ρ * xuR (log ed d) ρ) + β) ∈ TB ρ σ ∧
      pi σ ρ (ω ^ ((P + xuR ed ρ * xuR (log ed d) ρ) + β)) =
        ω ^ ((P' + xuR ed σ * xuR (log ed d) σ) + pi σ ρ β) := by
    intro β hβ hβB
    obtain ⟨s1, s2⟩ := pi_add hB hBK.1 hβ
    have hRE := (xu_eps_read hρE hρ1 he hte heB hgeρ).2.2.2.2.2.2.2.2.2.2.2.1
    have := hat _ s1 ((inE_indec hRE).add_lt hlead hβB)
    rw [s2, hBK.2] at this
    rw [add_assoc, add_assoc]; exact this
  obtain ⟨u1, u2⟩ := IH _ hdd (hlt _ hdd) g0d _ _ hat'
  obtain ⟨v1, v2⟩ := IH _ hrd (hlt _ hrd) g0r P P' hat
  have e1 : ∀ x Q : Ordinal.{0}, InE (xuR ed x) → ω ^ Q * xuR d x =
      ω ^ (Q + xuR ed x * xuR (log ed d) x) * xuR (d / ed ^ log ed d) x +
        ω ^ Q * xuR (d % ed ^ log ed d) x := by
    intro x Q hx
    rw [xuR_dec hdW hdB, ← xu_At_eq hdW hdB, mul_add, ← mul_assoc, gu_pow_eq hx, ← opow_add]
  have hEdρ := (xu_eps_read hρE hρ1 hEdE htd hedB (hged.trans hB.2.2.1)).2.2.2.2.2.2.2.2.2.2.2.1
  have hEdσ := (xu_eps_read hσE hσ1 hEdE htd hedB hged).2.2.2.2.2.2.2.2.2.2.2.1
  rw [e1 ρ P hEdρ, e1 σ P' hEdσ]
  obtain ⟨w1, w2⟩ := pi_add hB u1 v1
  exact ⟨w1, by rw [w2, u2, v2]⟩

/-- **LEMMA EXACT for every code `c < Γ(1)`** at every pair of bases `σ < ρ` with the gate below `σ`:
`c(ρ) ∈ Tᵖ[σ]` and `π_{σ,ρ}(c(ρ)) = c(σ)`. -/
theorem xu_pi : ∀ c, c < gcG 1 → xuG c < σ → xuR c ρ ∈ TB ρ σ ∧ pi σ ρ (xuR c ρ) = xuR c σ := by
  have hσE := hB.1
  have hρE := hB.2.1
  have hρ1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hωσ := omega0_lt_inE hσE
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  rcases lt_or_ge c (Wj.wjT 0) with hct | hct
  · rw [xuG_low hct] at hg
    rw [xuR_low hct, xuR_low hct]
    exact wtD.ex σ ρ hB c (xu_lt_wtB hct) hg
  have hcE := xu_gfE_le hct
  by_cases hcI : InE c
  · have hkc := (xuData_spec hcI (xu_G_lt_of hct) hc).2.1
    have hηc := (xuData_spec hcI (xu_G_lt_of hct) hc).2.2.1
    have hgq : xuQE c < σ := by rw [xuG_base hcI hct hc] at hg; exact hg
    have hgη : xuG (xuI c) < σ := xuG_of_Q hωσ ((xuQE_le_I c).trans_lt hgq)
    have hgk : xuG (xuK c) < σ := xuG_of_Q hωσ ((xuQE_le_K c).trans_lt hgq)
    obtain ⟨b1, b2, -, -⟩ := xu_base_pi hB hcI hct hc hg (IH _ hkc (hkc.trans hc) hgk)
      (IH _ hηc (hηc.trans hc) hgη)
    exact ⟨b1, b2⟩
  have hEc := gl_E_lt_self hcE hcI
  set e := guE c with hedef
  have he : InE e := guE_E c
  have hte : Wj.wjT 0 ≤ e := xu_E_ge hct
  have heB : e < gcG 1 := hEc.trans hc
  have hge : xuG e < σ := xu_E_g hct hc hg
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc, hdc⟩ := gl_parts hcE
  obtain ⟨g0n, g0k, g0d, g0r⟩ := xu_parts_g hωσ hct hc hg
  have hcN' : c < eN e := gl_lt_eN hcE
  have hkN : log e c < eN e := hkc.trans hcN'
  have hηc : xuI e < c := xu_idx_lt hct hc
  have hkc' : xuK e < c := xu_lev_lt hct hc
  have g0l : xuG (xuK e) < σ := xu_parts_lev hωσ hct hc hg
  obtain ⟨b1, b2, b3, b4⟩ := xu_base_pi hB he hte heB hge (IH _ hkc' (hkc'.trans hc) g0l) (IH _ hηc (hηc.trans hc) g0n)
  have hBK := xu_BK_pi hB he hte heB hge hk hkN g0k ⟨b1, b2⟩ (fun hω => by
    have hk1 : 1 < log e c := lt_of_lt_of_le one_lt_omega0 hω
    have hEkc : e * log e c < c := (gu_mulE_lt_pow he hk1 hkN).trans_le (by
      exact (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0)).trans (le_self_add.trans_eq hdec))
    obtain ⟨-, hB', hg', -⟩ := xu_mulE he hte heB _ hk hkN
    refine IH _ hEkc hB' (hg'.trans_lt (max_lt ?_ g0k))
    rw [xuG_base he hte heB] at hge; exact hge)
  set Bρ := xuR e ρ with hBρdef
  set Bσ := xuR e σ with hBσdef
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hBρE, hρB', -, -⟩ := xu_eps_read hρE hρ1 he hte heB (hge.trans hB.2.2.1)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hBσE, hσB', -, -⟩ := xu_eps_read hσE hσ1 he hte heB hge
  have hρB : ρ < Bρ := (lt_eN ρ).trans_le hρB'
  have hσB : σ < Bσ := (lt_eN σ).trans_le hσB'
  have hBO : Bρ < Om1 := (xuR_T hρE hρ1 heB (hge.trans hB.2.2.1)).2
  have hNO : eN Bρ < Om1 := eN_lt_Om1K hBO
  have hKN : xuR (log e c) ρ < eN Bρ := by
    rcases lt_or_ge (log e c) e with hkE | hkE
    · exact (xuR_mono hρE hρ1 heB hkE (hge.trans hB.2.2.1) (g0k.trans hB.2.2.1)).trans (lt_eN _)
    · obtain ⟨hEk, hgfk⟩ := gl_same he (xu_Om1_lt_t0.trans_le hte) hkE (hkc.trans hcN')
      have := xuR_top hρE hρ1 (hkc.trans hc) (hte.trans hkE) (g0k.trans hB.2.2.1)
      rwa [hEk] at this
  -- the atoms `ω^{B·K+β}`
  have hat : ∀ β, β ∈ TB ρ σ → β < Bρ → ω ^ (Bρ * xuR (log e c) ρ + β) ∈ TB ρ σ ∧
      pi σ ρ (ω ^ (Bρ * xuR (log e c) ρ + β)) = ω ^ (Bσ * xuR (log e c) σ + pi σ ρ β) := by
    intro β hβ hβB
    have hlt : Bρ * xuR (log e c) ρ + β < eN Bρ :=
      (inE_indec (eN_E Bρ)).add_lt ((eN_E Bρ).mul_lt (lt_eN Bρ) hKN) (hβB.trans (lt_eN Bρ))
    rcases lt_or_ge (log e c) ω with hkω | hkω
    · obtain ⟨j, hj⟩ := lt_omega0.1 hkω
      obtain ⟨j0, rfl⟩ : ∃ j0 : ℕ, j = j0 + 1 :=
        Nat.exists_eq_succ_of_ne_zero (by rintro rfl; exact hk (by rw [hj]; rfl))
      rw [hj, xuR_nat, xuR_nat]
      obtain ⟨m1, m2⟩ := pi_mul_nat hB b1 b2 j0
      obtain ⟨n1, n2⟩ := pi_add hB m1 hβ
      have hc1 : ((j0 + 1 : ℕ) : Ordinal.{0}) = 1 + (j0 : Ordinal.{0}) := by
        rw [Nat.add_comm]; push_cast; rfl
      have eρ : Bρ * ((j0 + 1 : ℕ) : Ordinal.{0}) + β = Bρ + (Bρ * (j0 : Ordinal.{0}) + β) := by
        rw [hc1, mul_add, mul_one, add_assoc]
      have eσ : Bσ * ((j0 + 1 : ℕ) : Ordinal.{0}) + pi σ ρ β = Bσ + (Bσ * (j0 : Ordinal.{0}) + pi σ ρ β) := by
        rw [hc1, mul_add, mul_one, add_assoc]
      rw [hj, xuR_nat] at hlt
      obtain ⟨a1, a2⟩ := gu_atom_pi hB hBρE hBσE hρB hσB b1 b2 b3 b4 hNO n1 (by rw [← eρ]; exact hlt)
      rw [n2, m2] at a2
      rw [eρ, eσ]
      exact ⟨a1, a2⟩
    · have hKω : ω ≤ xuR (log e c) ρ := xu_omega_le hρE hρ1 hkω (hkc.trans hc) (g0k.trans hB.2.2.1)
      have hKω' : ω ≤ xuR (log e c) σ := xu_omega_le hσE hσ1 hkω (hkc.trans hc) g0k
      have hab : ∀ X K : Ordinal.{0}, ω ≤ K → ∀ b, X * K + b = X + (X * K + b) := by
        intro X K hK b
        rw [← add_assoc]
        congr 1
        calc X * K = X * (1 + K) := by rw [one_add_of_omega0_le hK]
          _ = X + X * K := by rw [mul_add, mul_one]
      obtain ⟨n1, n2⟩ := pi_add hB hBK.1 hβ
      rw [hBK.2] at n2
      obtain ⟨a1, a2⟩ := gu_atom_pi hB hBρE hBσE hρB hσB b1 b2 b3 b4 hNO n1
        (by rw [← hab _ _ hKω]; exact hlt)
      rw [n2] at a2
      rw [hab Bρ _ hKω β, hab Bσ _ hKω' (pi σ ρ β)]
      exact ⟨a1, a2⟩
  have hdig := xu_dig hB he hte heB hge (fun j hj hgj => IH j (hj.trans hEc) (hj.trans heB) hgj)
    _ hdE g0d _ _ hat
  obtain ⟨r1, r2⟩ := IH _ hrc (hrc.trans hc) g0r
  rw [xuR_dec hct hc, xuR_dec hct hc, ← xu_At_eq hct hc, ← xu_At_eq hct hc, gu_pow_eq hBρE, gu_pow_eq hBσE]
  obtain ⟨w1, w2⟩ := pi_add hB hdig.1 r1
  exact ⟨w1, by rw [w2, hdig.2, r2]⟩

end Pi

end Googology.Trans.PoR.InaccPsi.R2.Xu
