import Googology.Trans.PoR.InaccPsi.R2.YhCof

/-!
# YhPi: CODES BELOW `Γ(N)`: LEMMA EXACT AT EVERY PAIR OF BASES (every layer, every base atom)

`π_{σ,ρ}(c(ρ)) = c(σ)` for every code `c < Γ(N)` (`N < ε₀`) with gate below `σ`, no `υ`-point hypothesis.  New
against `Xu.xu_pi`: the brackets of the base atoms, read `Γ_{x+1+i}` (`Gb.gq_pi`), with
`ε_{Γ_{x+1+i}+1} = ϑˣ(Ω₁ + Γ_{x+1+i})` (`yh_eN_gq`, the argument of `Gn.gn_eNG` at every `i < ε₀`); the digits
below `G` use the digit rule of `Go.goGl` (`G` read `Γ_{x+1}`).

* `yh_eN_gq`, `yh_eN_gq_pi`, `yh_omega_le`, `yhR_one_add`, `yh_mulE` (**`e·κ` is a code**, `(e·κ)(x) = e(x)·κ(x)`);
* `yh_base_pi`, `yh_BK_pi`, `yh_dig`, `yh_pi` (**LEMMA EXACT for every code `c < Γ(N)`**, one induction).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yh

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Xu
  Googology.Trans.PoR.InaccPsi.R2.Xx Googology.Trans.PoR.InaccPsi.R2.Xk Googology.Trans.PoR.InaccPsi.R2.Go

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **`ε_{Γ_{x+1+i}+1} = ϑˣ(Ω₁ + Γ_{x+1+i})`** for every `i < ε₀`. -/
theorem yh_eN_gq {i : Ordinal.{0}} (hi : i < ε₀) : eN (gq i x) = glA 1 (gq i x) x := by
  obtain ⟨hGT, hxG, hG1, hGE, -, hiT, hi1⟩ := yh_gqN hx hx1 hi
  obtain ⟨h1T, h11⟩ := gl_one_T hx hx1
  obtain ⟨-, -, -, haE, -, hta⟩ := glA_facts hx hx1 le_rfl h1T h11 hGT hG1
  refine le_antisymm (eN_le hta haE) ?_
  have hP1 : LuP 1 (eN (gq i x)) := by
    have h := vzP_one.2 (eN_E (gq i x)); unfold VzP at h; rwa [Nat.cast_one] at h
  have h1G : (1 : Ordinal.{0}) < gq i x := one_lt_omega0.trans (omega0_lt_inE hGE)
  refine glA_min hx hx1 le_rfl h1T h11 hGT hG1 hP1 (hxG.trans (lt_eN _)) (lt_eN _)
    (h1G.trans (lt_eN _)) (fun σ hσ => ?_)
  exact (xkA_lt hx hx1 hiT hi1 h1G hσ).trans (lt_eN _)

theorem yh_omega_le {N a : Ordinal.{0}} (hN : N < ε₀) (ha : ω ≤ a) (haN : a < gcG N) (hg : yhG a < x) :
    ω ≤ yhR a x := by
  rcases lt_or_ge a (gcG 0) with haG | haG
  · rw [yhR_low haG]; rw [yhG_low haG] at hg; exact gl_omega_le hx hx1 ha haG hg
  · have h1 := yhR_le_mono hx hx1 hN haN haG hg (by rw [yhG_atom]; exact hx.pos)
    rw [yhR_atom] at h1
    exact (omega0_lt_inE hx).le.trans ((yh_gqN hx hx1 (lt_of_le_of_lt zero_le hN)).2.1.le.trans h1)

theorem yhR_one_add {N a : Ordinal.{0}} (hN : N < ε₀) (haN : a < gcG N) (hg : yhG a < x) :
    yhR (1 + a) x = 1 + yhR a x := by
  rcases lt_or_ge a ω with haω | haω
  · obtain ⟨n, rfl⟩ := lt_omega0.1 haω
    have : (1 : Ordinal.{0}) + n = ((1 + n : ℕ) : Ordinal.{0}) := by push_cast; rfl
    rw [this, yhR_nat, yhR_nat]; push_cast; rfl
  · rw [one_add_of_omega0_le haω, one_add_of_omega0_le (yh_omega_le hx hx1 hN haω haN hg)]

end Base

/-- **`e·κ` as a code** (`e ∈ [G, Γ(N))` an `ε`-number code, `1 ≤ κ < ε_{e+1}`). -/
theorem yh_mulE {N e : Ordinal.{0}} (hN : N < ε₀) (he : InE e) (hGe : gcG 0 ≤ e) (heN : e < gcG N) :
    ∀ κ, κ ≠ 0 → κ < eN e →
    e * κ < eN e ∧ e * κ < gcG N ∧ yhG (e * κ) ≤ max (yhQE e) (yhG κ) ∧
      ∀ x, InE x → x < Om1 → yhG κ < x → yhR (e * κ) x = yhR e x * yhR κ x := by
  have hE1 : (1 : Ordinal.{0}) < e := Lu.lu_one_lt_E he
  have hNB : eN e ≤ gcG N := eN_le heN (Low.opow_eq_self_of_SC (gcG_SC N))
  have hOe : Om1 < e := gl_Om1_lt_G0.trans_le hGe
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
    · rw [e1, yhG_cnf he hGe one_ne_zero hk0 hkE hr (e1 ▸ hv), yhQ_one, yhG_zero]
      simp only [zero_le, max_eq_left, max_eq_right]
      exact max_le (le_max_left _ _) ((yhQ_le κ).trans (le_max_right _ _))
    · rw [e1, yhR_cnf he hGe one_ne_zero hk0 hkE hr (e1 ▸ hv), yhR_one, opow_one, yhR_zero, add_zero,
        ← yhR_base he hGe]
  have hkB : κ < gcG N := hkN.trans_le hNB
  obtain ⟨hEk, hgfk⟩ := gl_same he hOe hkE hkN
  have hkG : gcG 0 ≤ κ := hGe.trans hkE
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
  have hgEs : yhG (e * s) ≤ max (yhQE e) (yhG s) := by
    rcases eq_or_ne s 0 with h0 | h0
    · rw [h0, mul_zero, yhG_zero]; exact zero_le
    · exact (IH s hsk h0 hsN).2.2.1
  have hgk : yhG κ = max (max (yhQE e) (yhQ a)) (max (yhQ q) (yhG s)) := by
    rw [yhG_dec hkG, hEk]
  have hQa : ∀ a' : Ordinal.{0}, yhQ (1 + a') = yhQ a' := by
    intro a'
    rcases lt_or_ge a' ω with haω | haω
    · obtain ⟨n, rfl⟩ := lt_omega0.1 haω
      have : (1 : Ordinal.{0}) + n = ((1 + n : ℕ) : Ordinal.{0}) := by push_cast; rfl
      rw [this, yhQ_nat, yhQ_nat]
    · rw [one_add_of_omega0_le haω]
  refine ⟨?_, fun x hx hx1 hgx => ?_⟩
  · rw [e1, yhG_cnf he hGe h1a hq0 hqE hEs (e1 ▸ hv), hQa a, hgk]
    refine max_le (max_le (le_max_left _ _) ((le_max_right _ _).trans ((le_max_left _ _).trans
      (le_max_right _ _)))) (max_le ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
      (hgEs.trans (max_le (le_max_left _ _) ((le_max_right _ _).trans ((le_max_right _ _).trans
      (le_max_right _ _))))))
  · have hωx := omega0_lt_inE hx
    obtain ⟨g1, -, g3⟩ := yh_parts_g hωx hkG hgx
    rw [hEk] at g1 g3
    rw [e1, yhR_cnf he hGe h1a hq0 hqE hEs (e1 ▸ hv), yhR_dec hkG, hEk, ← yhR_base he hGe]
    have hRs : yhR (e * s) x = yhR e x * yhR s x := by
      rcases eq_or_ne s 0 with h0 | h0
      · rw [h0, mul_zero, yhR_zero, mul_zero]
      · exact (IH s hsk h0 hsN).2.2.2 x hx hx1 g3
    rw [hRs, yhR_one_add hx hx1 hN (hak.trans hkB) g1, opow_add, opow_one, mul_assoc, ← mul_add]

section Pi

variable {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) {N : Ordinal.{0}} (hN : N < ε₀)
include hB hN

theorem yh_eN_gq_pi {i : Ordinal.{0}} (hi : i < ε₀) :
    eN (gq i ρ) ∈ TB ρ σ ∧ pi σ ρ (eN (gq i ρ)) = eN (gq i σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨o1, o2⟩ := one_TB hB
  obtain ⟨g1, g2⟩ := gq_pi hB (hi.trans_le (gc_eps0_le hB.1))
  have hG1 : gq i ρ < Om1 := (yh_gqN hB.2.1 hρ1 hi).2.2.1
  have h := glA_pi hB o1 (gl_one_T hB.2.1 hρ1).2 g1 hG1
  rw [o2, g2, ← yh_eN_gq hB.2.1 hρ1 hi, ← yh_eN_gq hB.1 hσ1 hi] at h
  exact h

/-- **`π(e(ρ)) = e(σ)`** for an `ε`-number code `e ∈ [G, Γ(N))`, and the same for the next `ε`-number. -/
theorem yh_base_pi {e : Ordinal.{0}} (he : InE e) (hGe : gcG 0 ≤ e) (heN : e < gcG N) (hge : yhG e < σ)
    (hexα : ¬ YhAt e → yhR (yhK e) ρ ∈ TB ρ σ ∧ pi σ ρ (yhR (yhK e) ρ) = yhR (yhK e) σ)
    (hex : ¬ YhAt e → yhR (yhI e) ρ ∈ TB ρ σ ∧ pi σ ρ (yhR (yhI e) ρ) = yhR (yhI e) σ) :
    yhR e ρ ∈ TB ρ σ ∧ pi σ ρ (yhR e ρ) = yhR e σ ∧
      eN (yhR e ρ) ∈ TB ρ σ ∧ pi σ ρ (eN (yhR e ρ)) = eN (yhR e σ) := by
  have hσE := hB.1
  have hρE := hB.2.1
  have hρ1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  by_cases hA : YhAt e
  · obtain ⟨i, rfl⟩ := yhAt_iff.1 hA
    have hiε : i < ε₀ := (gcG_strictMono.lt_iff_lt.1 heN).trans hN
    rw [yhR_atom, yhR_atom]
    obtain ⟨a1, a2⟩ := gq_pi hB (hiε.trans_le (gc_eps0_le hσE))
    obtain ⟨b1, b2⟩ := yh_eN_gq_pi hB hN hiε
    exact ⟨a1, a2, b1, b2⟩
  have hGe' : gcG 0 < e := lt_of_le_of_ne hGe (fun h => hA (h ▸ yhAt_gcG 0))
  obtain ⟨rρ, -, -, -, -, -, hkRρ, -, hk1ρ, -, hη1, -, -⟩ :=
    yh_eps_data hρE hρ1 hN he hGe' hA heN (hge.trans hB.2.2.1)
  obtain ⟨rσ, -, -, -, -, -, -, -, -, -, -, -, -⟩ := yh_eps_data hσE hσ1 hN he hGe' hA heN hge
  obtain ⟨a1, a2⟩ := glA_pi hB (hexα hA).1 hk1ρ (hex hA).1 hη1
  obtain ⟨b1, b2⟩ := glA_eN_pi hB hkRρ (hexα hA).1 hk1ρ (hex hA).1 hη1
  rw [(hex hA).2, (hexα hA).2] at a2 b2
  rw [rρ, rσ]
  exact ⟨a1, a2, b1, b2⟩

/-- **`π(B·K) = B'·K'`** for the reading `B = e(ρ)` of an `ε`-number code and a code `κ`. -/
theorem yh_BK_pi {e κ : Ordinal.{0}} (he : InE e) (hGe : gcG 0 ≤ e) (heN : e < gcG N) (hκ0 : κ ≠ 0)
    (hκN : κ < eN e) (hgκ : yhG κ < σ)
    (hexe : yhR e ρ ∈ TB ρ σ ∧ pi σ ρ (yhR e ρ) = yhR e σ)
    (hexm2 : ω ≤ κ → yhR (e * κ) ρ ∈ TB ρ σ ∧ pi σ ρ (yhR (e * κ) ρ) = yhR (e * κ) σ) :
    yhR e ρ * yhR κ ρ ∈ TB ρ σ ∧ pi σ ρ (yhR e ρ * yhR κ ρ) = yhR e σ * yhR κ σ := by
  rcases lt_or_ge κ ω with hω | hω
  · obtain ⟨j, rfl⟩ := lt_omega0.1 hω
    rw [yhR_nat, yhR_nat]
    exact pi_mul_nat hB hexe.1 hexe.2 j
  · obtain ⟨-, -, -, hR⟩ := yh_mulE hN he hGe heN κ hκ0 hκN
    rw [← hR ρ hB.2.1 hB.2.2.2 (hgκ.trans hB.2.2.1), ← hR σ hB.1 (hB.2.2.1.trans hB.2.2.2) hgκ]
    exact hexm2 hω

/-- **The digits**: `π(ω^P·d(ρ)) = ω^{P'}·d(σ)` for every code `d` below an `ε`-number code `e ∈ [G, Γ(N))` with
gate below `σ`, once the atoms `ω^{P+β}` (`β ∈ Tᵖ[σ]`, `β < e(ρ)`) are exact and Lemma EXACT holds below `e`. -/
theorem yh_dig {e : Ordinal.{0}} (he : InE e) (hGe : gcG 0 ≤ e) (heN : e < gcG N) (hge : yhG e < σ)
    (hEX : ∀ j, j < e → yhG j < σ → yhR j ρ ∈ TB ρ σ ∧ pi σ ρ (yhR j ρ) = yhR j σ) :
    ∀ d, d < e → yhG d < σ → ∀ P P' : Ordinal.{0},
      (∀ β, β ∈ TB ρ σ → β < yhR e ρ →
        ω ^ (P + β) ∈ TB ρ σ ∧ pi σ ρ (ω ^ (P + β)) = ω ^ (P' + pi σ ρ β)) →
      ω ^ P * yhR d ρ ∈ TB ρ σ ∧ pi σ ρ (ω ^ P * yhR d ρ) = ω ^ P' * yhR d σ := by
  have hσE := hB.1
  have hρE := hB.2.1
  have hρ1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hωσ := omega0_lt_inE hσE
  have h0T : (0 : Ordinal.{0}) ∈ TB ρ σ := mem_TB_of_lt hB hσE.pos
  have h0pi : pi σ ρ 0 = 0 := pi_lt hB hσE.pos
  have hgeρ : yhG e < ρ := hge.trans hB.2.2.1
  intro d
  induction d using WellFoundedLT.induction with
  | ind d IH =>
  intro hdE hgd P P' hat
  rcases eq_or_ne d 0 with rfl | hd0
  · rw [yhR_zero, yhR_zero, mul_zero, mul_zero]; exact ⟨h0T, h0pi⟩
  have hMρ := yh_mono_top hρE hρ1 hN
  have hge0 : lgG ρ ≤ yhR e ρ := by
    rw [Gm.mg_gq0 hρE hρ1]
    exact yh_G_le_read hρE hρ1 hN he hGe heN hgeρ (fun j hj => (hMρ j (hj.trans heN)).1)
  rcases lt_or_ge d (gcG 0) with hdG | hdG
  · -- a code below `G`: the digit rule of `Go.goGl`
    rw [yhG_low hdG] at hgd
    rw [yhR_low hdG, yhR_low hdG]
    exact goGl.dig σ ρ hB d hdG hgd P P' (fun β hβ hβb => hat β hβ (hβb.trans_le hge0))
  -- a code of a lower bracket
  have hdN : d < gcG N := hdE.trans heN
  obtain ⟨hk, hd0', -, -, hdec, hkd, hrd, hdd⟩ := gl_parts (yh_gfE_le hdG)
  obtain ⟨g0k, g0d, g0r⟩ := yh_parts_g hωσ hdG hgd
  have hlt : ∀ j, j < d → j < e := fun j hj => hj.trans hdE
  set ed := guE d with heddef
  have hEdE : InE ed := guE_E d
  have hGed : gcG 0 ≤ ed := yh_G_le_E hdG
  have hedd : ed ≤ d := gl_E_le (yh_gfE_le hdG)
  have hedN : ed < gcG N := hedd.trans_lt hdN
  have hged : yhG ed < σ := yh_E_g hdG hgd
  have hkN : log ed d < eN ed := hkd.trans (gl_lt_eN (yh_gfE_le hdG))
  have hexe : yhR ed ρ ∈ TB ρ σ ∧ pi σ ρ (yhR ed ρ) = yhR ed σ := by
    rcases hedd.lt_or_eq with h | h
    · exact hEX _ (hlt _ h) hged
    · have hgq : yhQE ed < σ := by rw [yhG_base hEdE hGed] at hged; exact hged
      refine ⟨(yh_base_pi hB hN hEdE hGed hedN hged (fun hA => ?_) (fun hA => ?_)).1,
        (yh_base_pi hB hN hEdE hGed hedN hged (fun hA => ?_) (fun hA => ?_)).2.1⟩ <;>
      · have hGe' : gcG 0 < ed := lt_of_le_of_ne hGed (fun h => hA (h ▸ yhAt_gcG 0))
        obtain ⟨-, hke, hie, -⟩ := yhData_spec hEdE hGe' hA
        obtain ⟨gk, gi⟩ := yh_E_parts hωσ hA hgq
        first
          | exact hEX _ (hlt _ (hke.trans_le hedd)) gk
          | exact hEX _ (hlt _ (hie.trans_le hedd)) gi
  have hBK := yh_BK_pi hB hN hEdE hGed hedN hk hkN g0k hexe (fun hω => by
    have hk1 : 1 < log ed d := lt_of_lt_of_le one_lt_omega0 hω
    have hEkd : ed * log ed d < d := (gu_mulE_lt_pow hEdE hk1 hkN).trans_le (by
      exact (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0')).trans (le_self_add.trans_eq hdec))
    obtain ⟨-, -, hg, -⟩ := yh_mulE hN hEdE hGed hedN _ hk hkN
    refine hEX _ (hlt _ hEkd) (hg.trans_lt (max_lt ?_ g0k))
    rw [yhG_base hEdE hGed] at hged; exact hged)
  have hgdρ : yhG d < ρ := hgd.trans hB.2.2.1
  have hEdρ : InE (yhR ed ρ) := by
    rw [yhR_base hEdE hGed]; exact (yhA_facts hρE hρ1 hN hEdE hGed hedN (hged.trans hB.2.2.1)).1
  have hEdσ : InE (yhR ed σ) := by
    rw [yhR_base hEdE hGed]; exact (yhA_facts hσE hσ1 hN hEdE hGed hedN hged).1
  have hlead : yhR ed ρ * yhR (log ed d) ρ < yhR e ρ := by
    have h1 : yhR ed ρ * yhR (log ed d) ρ ≤ yhR ed ρ ^ yhR (log ed d) ρ := by
      rw [gu_pow_eq hEdρ]; exact right_le_opow _ one_lt_omega0
    have h2 : yhR ed ρ ^ yhR (log ed d) ρ * yhR (d / ed ^ log ed d) ρ ≤ yhR d ρ := by
      rw [yhR_dec hdG, ← yhR_base hEdE hGed]; exact le_self_add
    have h3 : yhR ed ρ ^ yhR (log ed d) ρ ≤
        yhR ed ρ ^ yhR (log ed d) ρ * yhR (d / ed ^ log ed d) ρ :=
      le_mul_of_one_le_right' (one_le_iff_pos.2 (yhR_pos hρE hρ1 hN hd0' (hdd.trans hdN) (g0d.trans hB.2.2.1)))
    exact (h1.trans (h3.trans h2)).trans_lt (yhR_mono hρE hρ1 hN heN hdE hgeρ hgdρ)
  have hat' : ∀ β, β ∈ TB ρ σ → β < yhR e ρ →
      ω ^ ((P + yhR ed ρ * yhR (log ed d) ρ) + β) ∈ TB ρ σ ∧
      pi σ ρ (ω ^ ((P + yhR ed ρ * yhR (log ed d) ρ) + β)) =
        ω ^ ((P' + yhR ed σ * yhR (log ed d) σ) + pi σ ρ β) := by
    intro β hβ hβB
    obtain ⟨s1, s2⟩ := pi_add hB hBK.1 hβ
    have hRE : InE (yhR e ρ) := by
      rw [yhR_base he hGe]; exact (yhA_facts hρE hρ1 hN he hGe heN hgeρ).1
    have := hat _ s1 ((inE_indec hRE).add_lt hlead hβB)
    rw [s2, hBK.2] at this
    rw [add_assoc, add_assoc]; exact this
  obtain ⟨u1, u2⟩ := IH _ hdd (hlt _ hdd) g0d _ _ hat'
  obtain ⟨v1, v2⟩ := IH _ hrd (hlt _ hrd) g0r P P' hat
  have e1 : ∀ x Q : Ordinal.{0}, InE (yhR ed x) → ω ^ Q * yhR d x =
      ω ^ (Q + yhR ed x * yhR (log ed d) x) * yhR (d / ed ^ log ed d) x +
        ω ^ Q * yhR (d % ed ^ log ed d) x := by
    intro x Q hx
    rw [yhR_dec hdG, ← yhR_base hEdE hGed, mul_add, ← mul_assoc, gu_pow_eq hx, ← opow_add]
  rw [e1 ρ P hEdρ, e1 σ P' hEdσ]
  obtain ⟨w1, w2⟩ := pi_add hB u1 v1
  exact ⟨w1, by rw [w2, u2, v2]⟩

/-- **LEMMA EXACT for every code `c < Γ(N)`** at every pair of bases `σ < ρ` with the gate below `σ`. -/
theorem yh_pi : ∀ c, c < gcG N → yhG c < σ → yhR c ρ ∈ TB ρ σ ∧ pi σ ρ (yhR c ρ) = yhR c σ := by
  have hσE := hB.1
  have hρE := hB.2.1
  have hρ1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hωσ := omega0_lt_inE hσE
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  rcases lt_or_ge c (gcG 0) with hcG | hcG
  · rw [yhG_low hcG] at hg
    rw [yhR_low hcG, yhR_low hcG]
    exact gl_pi hB c hcG hg
  have hcE := yh_gfE_le hcG
  -- Lemma EXACT at the level and the index of a non-atom `ε`-number code `e ≤ c` with gate below `σ`
  have hLI : ∀ e, InE e → gcG 0 ≤ e → e ≤ c → yhG e < σ →
      (¬ YhAt e → yhR (yhK e) ρ ∈ TB ρ σ ∧ pi σ ρ (yhR (yhK e) ρ) = yhR (yhK e) σ) ∧
      (¬ YhAt e → yhR (yhI e) ρ ∈ TB ρ σ ∧ pi σ ρ (yhR (yhI e) ρ) = yhR (yhI e) σ) := by
    intro e he hGe hec hge
    have hgq : yhQE e < σ := by rw [yhG_base he hGe] at hge; exact hge
    refine ⟨fun hA => ?_, fun hA => ?_⟩
    · have hGe' : gcG 0 < e := lt_of_le_of_ne hGe (fun h => hA (h ▸ yhAt_gcG 0))
      have hke := (yhData_spec he hGe' hA).2.1
      exact IH _ (hke.trans_le hec) ((hke.trans_le hec).trans hc) (yh_E_parts hωσ hA hgq).1
    · have hGe' : gcG 0 < e := lt_of_le_of_ne hGe (fun h => hA (h ▸ yhAt_gcG 0))
      have hie := (yhData_spec he hGe' hA).2.2.1
      exact IH _ (hie.trans_le hec) ((hie.trans_le hec).trans hc) (yh_E_parts hωσ hA hgq).2
  by_cases hcI : InE c
  · obtain ⟨l1, l2⟩ := hLI c hcI hcG le_rfl hg
    obtain ⟨b1, b2, -, -⟩ := yh_base_pi hB hN hcI hcG hc hg l1 l2
    exact ⟨b1, b2⟩
  have hEc := gl_E_lt_self hcE hcI
  set e := guE c with hedef
  have he : InE e := guE_E c
  have hGe : gcG 0 ≤ e := yh_G_le_E hcG
  have hOe : Om1 < e := gl_Om1_lt_G0.trans_le hGe
  have heN : e < gcG N := hEc.trans hc
  have hge : yhG e < σ := yh_E_g hcG hg
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc, hdc⟩ := gl_parts hcE
  obtain ⟨g0k, g0d, g0r⟩ := yh_parts_g hωσ hcG hg
  have hcN' : c < eN e := gl_lt_eN hcE
  have hkN : log e c < eN e := hkc.trans hcN'
  obtain ⟨l1, l2⟩ := hLI e he hGe hEc.le hge
  obtain ⟨b1, b2, b3, b4⟩ := yh_base_pi hB hN he hGe heN hge l1 l2
  have hBK := yh_BK_pi hB hN he hGe heN hk hkN g0k ⟨b1, b2⟩ (fun hω => by
    have hk1 : 1 < log e c := lt_of_lt_of_le one_lt_omega0 hω
    have hEkc : e * log e c < c := (gu_mulE_lt_pow he hk1 hkN).trans_le (by
      exact (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0)).trans (le_self_add.trans_eq hdec))
    obtain ⟨-, hB', hg', -⟩ := yh_mulE hN he hGe heN _ hk hkN
    refine IH _ hEkc hB' (hg'.trans_lt (max_lt ?_ g0k))
    rw [yhG_base he hGe] at hge; exact hge)
  set Bρ := yhR e ρ with hBρdef
  set Bσ := yhR e σ with hBσdef
  obtain ⟨hBρE, hρB, -, -, hBO⟩ := yhA_facts hρE hρ1 hN he hGe heN (hge.trans hB.2.2.1)
  obtain ⟨hBσE, hσB, -, -, -⟩ := yhA_facts hσE hσ1 hN he hGe heN hge
  rw [← yhR_base he hGe] at hBρE hρB hBO hBσE hσB
  have hNO : eN Bρ < Om1 := eN_lt_Om1K hBO
  have hKN : yhR (log e c) ρ < eN Bρ := by
    rcases lt_or_ge (log e c) e with hkE | hkE
    · exact (yhR_mono hρE hρ1 hN heN hkE (hge.trans hB.2.2.1) (g0k.trans hB.2.2.1)).trans (lt_eN _)
    · obtain ⟨hEk, hgfk⟩ := gl_same he hOe hkE (hkc.trans hcN')
      have := yhR_top hρE hρ1 hN (hkc.trans hc) (hGe.trans hkE) (g0k.trans hB.2.2.1)
      rwa [hEk, ← yhR_base he hGe] at this
  -- the atoms `ω^{B·K+β}`
  have hat : ∀ β, β ∈ TB ρ σ → β < Bρ → ω ^ (Bρ * yhR (log e c) ρ + β) ∈ TB ρ σ ∧
      pi σ ρ (ω ^ (Bρ * yhR (log e c) ρ + β)) = ω ^ (Bσ * yhR (log e c) σ + pi σ ρ β) := by
    intro β hβ hβB
    have hlt : Bρ * yhR (log e c) ρ + β < eN Bρ :=
      (inE_indec (eN_E Bρ)).add_lt ((eN_E Bρ).mul_lt (lt_eN Bρ) hKN) (hβB.trans (lt_eN Bρ))
    rcases lt_or_ge (log e c) ω with hkω | hkω
    · obtain ⟨j, hj⟩ := lt_omega0.1 hkω
      obtain ⟨j0, rfl⟩ : ∃ j0 : ℕ, j = j0 + 1 :=
        Nat.exists_eq_succ_of_ne_zero (by rintro rfl; exact hk (by rw [hj]; rfl))
      rw [hj, yhR_nat, yhR_nat]
      obtain ⟨m1, m2⟩ := pi_mul_nat hB b1 b2 j0
      obtain ⟨n1, n2⟩ := pi_add hB m1 hβ
      have hc1 : ((j0 + 1 : ℕ) : Ordinal.{0}) = 1 + (j0 : Ordinal.{0}) := by
        rw [Nat.add_comm]; push_cast; rfl
      have eρ : Bρ * ((j0 + 1 : ℕ) : Ordinal.{0}) + β = Bρ + (Bρ * (j0 : Ordinal.{0}) + β) := by
        rw [hc1, mul_add, mul_one, add_assoc]
      have eσ : Bσ * ((j0 + 1 : ℕ) : Ordinal.{0}) + pi σ ρ β = Bσ + (Bσ * (j0 : Ordinal.{0}) + pi σ ρ β) := by
        rw [hc1, mul_add, mul_one, add_assoc]
      rw [hj, yhR_nat] at hlt
      obtain ⟨a1, a2⟩ := gu_atom_pi hB hBρE hBσE hρB hσB b1 b2 b3 b4 hNO n1 (by rw [← eρ]; exact hlt)
      rw [n2, m2] at a2
      rw [eρ, eσ]
      exact ⟨a1, a2⟩
    · have hKω : ω ≤ yhR (log e c) ρ := yh_omega_le hρE hρ1 hN hkω (hkc.trans hc) (g0k.trans hB.2.2.1)
      have hKω' : ω ≤ yhR (log e c) σ := yh_omega_le hσE hσ1 hN hkω (hkc.trans hc) g0k
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
  have hdig := yh_dig hB hN he hGe heN hge (fun j hj hgj => IH j (hj.trans hEc) (hj.trans heN) hgj)
    _ hdE g0d _ _ hat
  obtain ⟨r1, r2⟩ := IH _ hrc (hrc.trans hc) g0r
  rw [yhR_dec hcG, yhR_dec hcG, ← yhR_base he hGe, ← yhR_base he hGe, gu_pow_eq hBρE, gu_pow_eq hBσE]
  obtain ⟨w1, w2⟩ := pi_add hB hdig.1 r1
  exact ⟨w1, by rw [w2, hdig.2, r2]⟩

end Pi

end Googology.Trans.PoR.InaccPsi.R2.Yh
