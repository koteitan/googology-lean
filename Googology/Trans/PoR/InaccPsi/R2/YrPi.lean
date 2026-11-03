import Googology.Trans.PoR.InaccPsi.R2.YrCof
import Googology.Trans.PoR.InaccPsi.R2.YhPi

/-!
# YrPi: CODES BELOW `B_Γ`, READ ATOM INDICES: LEMMA EXACT AT EVERY PAIR OF BASES

`π_{σ,ρ}(c(ρ)) = c(σ)` for every code `c < B_Γ` with gate below `σ`.  The argument of `Yh.yh_pi`; the atom `Γ(i)`
reads `ϑᵖ(Ω₁·Ω₁ + i(ρ))` and `π(ϑᵖ(Ω₁·Ω₁ + i(ρ))) = ϑ^σ(Ω₁·Ω₁ + π(i(ρ))) = ϑ^σ(Ω₁·Ω₁ + i(σ))` (`Ge.geq_pi` and
Lemma EXACT at the index, one induction), `ε_{Γ_{x+1+ν}+1} = ϑˣ(Ω₁ + Γ_{x+1+ν})` for every admissible `ν`
(`yr_eN_gq`).

* `yr_eN_gq`, `yr_eN_gq_pi`, `yr_omega_le`, `yrR_one_add`, `yr_mulE`;
* `yr_base_pi`, `yr_BK_pi`, `yr_dig`, `yr_pi` (**LEMMA EXACT for every code `c < B_Γ`**, one induction).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yr

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Xu
  Googology.Trans.PoR.InaccPsi.R2.Xx Googology.Trans.PoR.InaccPsi.R2.Xk Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Yh

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **`ε_{Γ_{x+1+i}+1} = ϑˣ(Ω₁ + Γ_{x+1+i})`** for every admissible `i`. -/
theorem yr_eN_gq {i : Ordinal.{0}} (hi : YrN x i) : eN (gq i x) = glA 1 (gq i x) x := by
  obtain ⟨hGT, hxG, hG1, hGE, -⟩ := yr_facts hx hx1 hi
  obtain ⟨hiT, hi1⟩ := yr_T hi
  obtain ⟨h1T, h11⟩ := gl_one_T hx hx1
  obtain ⟨-, -, -, haE, -, hta⟩ := glA_facts hx hx1 le_rfl h1T h11 hGT hG1
  refine le_antisymm (eN_le hta haE) ?_
  have hP1 : LuP 1 (eN (gq i x)) := by
    have h := vzP_one.2 (eN_E (gq i x)); unfold VzP at h; rwa [Nat.cast_one] at h
  have h1G : (1 : Ordinal.{0}) < gq i x := one_lt_omega0.trans (omega0_lt_inE hGE)
  refine glA_min hx hx1 le_rfl h1T h11 hGT hG1 hP1 (hxG.trans (lt_eN _)) (lt_eN _)
    (h1G.trans (lt_eN _)) (fun σ hσ => ?_)
  exact (xkA_lt hx hx1 hiT hi1 h1G hσ).trans (lt_eN _)

theorem yr_omega_le {a : Ordinal.{0}} (ha : ω ≤ a) (haB : a < Tf.tfBG) (hg : yrG a < x) :
    ω ≤ yrR a x := by
  rcases lt_or_ge a (gcG 0) with haG | haG
  · rw [yrR_low haG]; rw [yrG_low haG] at hg; exact gl_omega_le hx hx1 ha haG hg
  · have h1 := yrR_le_mono hx hx1 haB haG hg (by rw [yrG_G0]; exact hx.pos)
    rw [yrR_G0] at h1
    exact (omega0_lt_inE hx).le.trans ((gfq0_facts hx hx1).2.1.le.trans h1)

theorem yrR_one_add {a : Ordinal.{0}} (haB : a < Tf.tfBG) (hg : yrG a < x) :
    yrR (1 + a) x = 1 + yrR a x := by
  rcases lt_or_ge a ω with haω | haω
  · obtain ⟨n, rfl⟩ := lt_omega0.1 haω
    have : (1 : Ordinal.{0}) + n = ((1 + n : ℕ) : Ordinal.{0}) := by push_cast; rfl
    rw [this, yrR_nat, yrR_nat]; push_cast; rfl
  · rw [one_add_of_omega0_le haω, one_add_of_omega0_le (yr_omega_le hx hx1 haω haB hg)]

end Base

/-- **`e·κ` as a code** (`e ∈ [G, B_Γ)` an `ε`-number code, `1 ≤ κ < ε_{e+1}`). -/
theorem yr_mulE {e : Ordinal.{0}} (he : InE e) (hGe : gcG 0 ≤ e) (heB : e < Tf.tfBG) :
    ∀ κ, κ ≠ 0 → κ < eN e →
    e * κ < eN e ∧ e * κ < Tf.tfBG ∧ yrG (e * κ) ≤ max (yrQE e) (yrG κ) ∧
      ∀ x, InE x → x < Om1 → yrG κ < x → yrR (e * κ) x = yrR e x * yrR κ x := by
  have hE1 : (1 : Ordinal.{0}) < e := Lu.lu_one_lt_E he
  have hNB : eN e ≤ Tf.tfBG := eN_le heB (Low.opow_eq_self_of_SC Tf.tfBG_SC)
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
    · rw [e1, yrG_cnf he hGe one_ne_zero hk0 hkE hr (e1 ▸ hv), yrQ_one, yrG_zero]
      simp only [zero_le, max_eq_left, max_eq_right]
      exact max_le (le_max_left _ _) ((yrQ_le κ).trans (le_max_right _ _))
    · rw [e1, yrR_cnf he hGe one_ne_zero hk0 hkE hr (e1 ▸ hv), yrR_one, opow_one, yrR_zero, add_zero,
        ← yrR_base he hGe]
  have hkBB : κ < Tf.tfBG := hkN.trans_le hNB
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
  have hgEs : yrG (e * s) ≤ max (yrQE e) (yrG s) := by
    rcases eq_or_ne s 0 with h0 | h0
    · rw [h0, mul_zero, yrG_zero]; exact zero_le
    · exact (IH s hsk h0 hsN).2.2.1
  have hgk : yrG κ = max (max (yrQE e) (yrQ a)) (max (yrQ q) (yrG s)) := by
    rw [yrG_dec hkG, hEk]
  have hQa : ∀ a' : Ordinal.{0}, yrQ (1 + a') = yrQ a' := by
    intro a'
    rcases lt_or_ge a' ω with haω | haω
    · obtain ⟨n, rfl⟩ := lt_omega0.1 haω
      have : (1 : Ordinal.{0}) + n = ((1 + n : ℕ) : Ordinal.{0}) := by push_cast; rfl
      rw [this, yrQ_nat, yrQ_nat]
    · rw [one_add_of_omega0_le haω]
  refine ⟨?_, fun x hx hx1 hgx => ?_⟩
  · rw [e1, yrG_cnf he hGe h1a hq0 hqE hEs (e1 ▸ hv), hQa a, hgk]
    refine max_le (max_le (le_max_left _ _) ((le_max_right _ _).trans ((le_max_left _ _).trans
      (le_max_right _ _)))) (max_le ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
      (hgEs.trans (max_le (le_max_left _ _) ((le_max_right _ _).trans ((le_max_right _ _).trans
      (le_max_right _ _))))))
  · have hωx := omega0_lt_inE hx
    obtain ⟨g1, -, g3⟩ := yr_parts_g hωx hkG hgx
    rw [hEk] at g1 g3
    rw [e1, yrR_cnf he hGe h1a hq0 hqE hEs (e1 ▸ hv), yrR_dec hkG, hEk, ← yrR_base he hGe]
    have hRs : yrR (e * s) x = yrR e x * yrR s x := by
      rcases eq_or_ne s 0 with h0 | h0
      · rw [h0, mul_zero, yrR_zero, mul_zero]
      · exact (IH s hsk h0 hsN).2.2.2 x hx hx1 g3
    rw [hRs, yrR_one_add hx hx1 (hak.trans hkBB) g1, opow_add, opow_one, mul_assoc, ← mul_add]

/-- **The index of an atom bracket `e < B_Γ`** is below `e` and keeps the gate. -/
theorem yr_idx_of {e z : Ordinal.{0}} (hωz : ω < z) (hA : YhAt e) (heB : e < Tf.tfBG) (hge : yrG e < z) :
    yhJ e < e ∧ yrG (yhJ e) < z := by
  obtain ⟨i, rfl⟩ := yhAt_iff.1 hA
  obtain ⟨hii, hie⟩ := yr_atom_idx rfl heB
  rw [yhJ_gcG]
  exact ⟨hie, yr_E_atom hωz hii hge⟩

section Pi

variable {σ ρ : Ordinal.{0}} (hB : Bases σ ρ)
include hB

theorem yr_eN_gq_pi {i i' : Ordinal.{0}} (hiρ : YrN ρ i) (hiσ : YrN σ i')
    (hi : i ∈ TB ρ σ ∧ pi σ ρ i = i') :
    eN (gq i ρ) ∈ TB ρ σ ∧ pi σ ρ (eN (gq i ρ)) = eN (gq i' σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨o1, o2⟩ := one_TB hB
  obtain ⟨g1, g2⟩ := Ge.geq_pi hB hi hiρ.2.1
  have hG1 : gq i ρ < Om1 := (yr_facts hB.2.1 hρ1 hiρ).2.2.1
  have h := glA_pi hB o1 (gl_one_T hB.2.1 hρ1).2 g1 hG1
  rw [o2, g2, ← yr_eN_gq hB.2.1 hρ1 hiρ, ← yr_eN_gq hB.1 hσ1 hiσ] at h
  exact h

/-- **`π(e(ρ)) = e(σ)`** for an `ε`-number code `e ∈ [G, B_Γ)`, and the same for the next `ε`-number. -/
theorem yr_base_pi {e : Ordinal.{0}} (he : InE e) (hGe : gcG 0 ≤ e) (heB : e < Tf.tfBG) (hge : yrG e < σ)
    (hexi : YhAt e → yrR (yhJ e) ρ ∈ TB ρ σ ∧ pi σ ρ (yrR (yhJ e) ρ) = yrR (yhJ e) σ)
    (hexα : ¬ YhAt e → yrR (yhK e) ρ ∈ TB ρ σ ∧ pi σ ρ (yrR (yhK e) ρ) = yrR (yhK e) σ)
    (hex : ¬ YhAt e → yrR (yhI e) ρ ∈ TB ρ σ ∧ pi σ ρ (yrR (yhI e) ρ) = yrR (yhI e) σ) :
    yrR e ρ ∈ TB ρ σ ∧ pi σ ρ (yrR e ρ) = yrR e σ ∧
      eN (yrR e ρ) ∈ TB ρ σ ∧ pi σ ρ (eN (yrR e ρ)) = eN (yrR e σ) := by
  have hσE := hB.1
  have hρE := hB.2.1
  have hρ1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  by_cases hA : YhAt e
  · obtain ⟨i, rfl⟩ := yhAt_iff.1 hA
    obtain ⟨hii, hie⟩ := yr_atom_idx rfl heB
    have hgi : yrG i < σ := yr_E_atom (omega0_lt_inE hσE) hii hge
    have hiρ := yrR_N hρE hρ1 (hie.trans heB) (hgi.trans hB.2.2.1)
    have hiσ := yrR_N hσE hσ1 (hie.trans heB) hgi
    have hexi' := hexi hA
    rw [yhJ_gcG] at hexi'
    rw [yrR_atom hii, yrR_atom hii]
    obtain ⟨a1, a2⟩ := Ge.geq_pi hB hexi' hiρ.2.1
    obtain ⟨b1, b2⟩ := yr_eN_gq_pi hB hiρ hiσ hexi'
    exact ⟨a1, a2, b1, b2⟩
  have hGe' : gcG 0 < e := lt_of_le_of_ne hGe (fun h => hA (h ▸ yhAt_gcG 0))
  obtain ⟨rρ, -, -, -, -, -, hkRρ, -, hk1ρ, -, hη1, -, -⟩ :=
    yr_eps_data hρE hρ1 he hGe' hA heB (hge.trans hB.2.2.1)
  obtain ⟨rσ, -, -, -, -, -, -, -, -, -, -, -, -⟩ := yr_eps_data hσE hσ1 he hGe' hA heB hge
  obtain ⟨a1, a2⟩ := glA_pi hB (hexα hA).1 hk1ρ (hex hA).1 hη1
  obtain ⟨b1, b2⟩ := glA_eN_pi hB hkRρ (hexα hA).1 hk1ρ (hex hA).1 hη1
  rw [(hex hA).2, (hexα hA).2] at a2 b2
  rw [rρ, rσ]
  exact ⟨a1, a2, b1, b2⟩

/-- **`π(B·K) = B'·K'`** for the reading `B = e(ρ)` of an `ε`-number code and a code `κ`. -/
theorem yr_BK_pi {e κ : Ordinal.{0}} (he : InE e) (hGe : gcG 0 ≤ e) (heB : e < Tf.tfBG) (hκ0 : κ ≠ 0)
    (hκN : κ < eN e) (hgκ : yrG κ < σ)
    (hexe : yrR e ρ ∈ TB ρ σ ∧ pi σ ρ (yrR e ρ) = yrR e σ)
    (hexm2 : ω ≤ κ → yrR (e * κ) ρ ∈ TB ρ σ ∧ pi σ ρ (yrR (e * κ) ρ) = yrR (e * κ) σ) :
    yrR e ρ * yrR κ ρ ∈ TB ρ σ ∧ pi σ ρ (yrR e ρ * yrR κ ρ) = yrR e σ * yrR κ σ := by
  rcases lt_or_ge κ ω with hω | hω
  · obtain ⟨j, rfl⟩ := lt_omega0.1 hω
    rw [yrR_nat, yrR_nat]
    exact pi_mul_nat hB hexe.1 hexe.2 j
  · obtain ⟨-, -, -, hR⟩ := yr_mulE he hGe heB κ hκ0 hκN
    rw [← hR ρ hB.2.1 hB.2.2.2 (hgκ.trans hB.2.2.1), ← hR σ hB.1 (hB.2.2.1.trans hB.2.2.2) hgκ]
    exact hexm2 hω

/-- **The digits**: `π(ω^P·d(ρ)) = ω^{P'}·d(σ)` for every code `d` below an `ε`-number code `e ∈ [G, B_Γ)` with
gate below `σ`, once the atoms `ω^{P+β}` (`β ∈ Tᵖ[σ]`, `β < e(ρ)`) are exact and Lemma EXACT holds below `e`. -/
theorem yr_dig {e : Ordinal.{0}} (he : InE e) (hGe : gcG 0 ≤ e) (heB : e < Tf.tfBG) (hge : yrG e < σ)
    (hEX : ∀ j, j < e → yrG j < σ → yrR j ρ ∈ TB ρ σ ∧ pi σ ρ (yrR j ρ) = yrR j σ) :
    ∀ d, d < e → yrG d < σ → ∀ P P' : Ordinal.{0},
      (∀ β, β ∈ TB ρ σ → β < yrR e ρ →
        ω ^ (P + β) ∈ TB ρ σ ∧ pi σ ρ (ω ^ (P + β)) = ω ^ (P' + pi σ ρ β)) →
      ω ^ P * yrR d ρ ∈ TB ρ σ ∧ pi σ ρ (ω ^ P * yrR d ρ) = ω ^ P' * yrR d σ := by
  have hσE := hB.1
  have hρE := hB.2.1
  have hρ1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hωσ := omega0_lt_inE hσE
  have h0T : (0 : Ordinal.{0}) ∈ TB ρ σ := mem_TB_of_lt hB hσE.pos
  have h0pi : pi σ ρ 0 = 0 := pi_lt hB hσE.pos
  have hgeρ : yrG e < ρ := hge.trans hB.2.2.1
  intro d
  induction d using WellFoundedLT.induction with
  | ind d IH =>
  intro hdE hgd P P' hat
  rcases eq_or_ne d 0 with rfl | hd0
  · rw [yrR_zero, yrR_zero, mul_zero, mul_zero]; exact ⟨h0T, h0pi⟩
  have hMρ := yr_mono_top hρE hρ1
  have hge0 : lgG ρ ≤ yrR e ρ := by
    rw [Gm.mg_gq0 hρE hρ1]
    exact yr_G_le_read hρE hρ1 he hGe heB hgeρ (fun j hj => (hMρ j (hj.trans heB)).1)
  rcases lt_or_ge d (gcG 0) with hdG | hdG
  · -- a code below `G`: the digit rule of `Go.goGl`
    rw [yrG_low hdG] at hgd
    rw [yrR_low hdG, yrR_low hdG]
    exact goGl.dig σ ρ hB d hdG hgd P P' (fun β hβ hβb => hat β hβ (hβb.trans_le hge0))
  -- a code of a lower bracket
  have hdB : d < Tf.tfBG := hdE.trans heB
  obtain ⟨hk, hd0', -, -, hdec, hkd, hrd, hdd⟩ := gl_parts (yh_gfE_le hdG)
  obtain ⟨g0k, g0d, g0r⟩ := yr_parts_g hωσ hdG hgd
  have hlt : ∀ j, j < d → j < e := fun j hj => hj.trans hdE
  set ed := guE d with heddef
  have hEdE : InE ed := guE_E d
  have hGed : gcG 0 ≤ ed := yh_G_le_E hdG
  have hedd : ed ≤ d := gl_E_le (yh_gfE_le hdG)
  have hedB : ed < Tf.tfBG := hedd.trans_lt hdB
  have hged : yrG ed < σ := yr_E_g hdG hgd
  have hkN : log ed d < eN ed := hkd.trans (gl_lt_eN (yh_gfE_le hdG))
  have hexe : yrR ed ρ ∈ TB ρ σ ∧ pi σ ρ (yrR ed ρ) = yrR ed σ := by
    rcases hedd.lt_or_eq with h | h
    · exact hEX _ (hlt _ h) hged
    · have hgq : yrQE ed < σ := by rw [yrG_base hEdE hGed] at hged; exact hged
      have hexi : YhAt ed → yrR (yhJ ed) ρ ∈ TB ρ σ ∧ pi σ ρ (yrR (yhJ ed) ρ) = yrR (yhJ ed) σ := fun hA => by
        obtain ⟨h1, h2⟩ := yr_idx_of hωσ hA hedB hged
        exact hEX _ (hlt _ (h1.trans_le hedd)) h2
      refine ⟨(yr_base_pi hB hEdE hGed hedB hged hexi (fun hA => ?_) (fun hA => ?_)).1,
        (yr_base_pi hB hEdE hGed hedB hged hexi (fun hA => ?_) (fun hA => ?_)).2.1⟩ <;>
      · have hGe' : gcG 0 < ed := lt_of_le_of_ne hGed (fun h => hA (h ▸ yhAt_gcG 0))
        obtain ⟨-, hke, hie, -⟩ := yhData_spec hEdE hGe' hA
        obtain ⟨gk, gi⟩ := yr_E_parts hωσ hA hgq
        first
          | exact hEX _ (hlt _ (hke.trans_le hedd)) gk
          | exact hEX _ (hlt _ (hie.trans_le hedd)) gi
  have hBK := yr_BK_pi hB hEdE hGed hedB hk hkN g0k hexe (fun hω => by
    have hk1 : 1 < log ed d := lt_of_lt_of_le one_lt_omega0 hω
    have hEkd : ed * log ed d < d := (gu_mulE_lt_pow hEdE hk1 hkN).trans_le (by
      exact (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0')).trans (le_self_add.trans_eq hdec))
    obtain ⟨-, -, hg, -⟩ := yr_mulE hEdE hGed hedB _ hk hkN
    refine hEX _ (hlt _ hEkd) (hg.trans_lt (max_lt ?_ g0k))
    rw [yrG_base hEdE hGed] at hged; exact hged)
  have hgdρ : yrG d < ρ := hgd.trans hB.2.2.1
  have hEdρ : InE (yrR ed ρ) := by
    rw [yrR_base hEdE hGed]; exact (yrA_facts hρE hρ1 hEdE hGed hedB (hged.trans hB.2.2.1)).1
  have hEdσ : InE (yrR ed σ) := by
    rw [yrR_base hEdE hGed]; exact (yrA_facts hσE hσ1 hEdE hGed hedB hged).1
  have hlead : yrR ed ρ * yrR (log ed d) ρ < yrR e ρ := by
    have h1 : yrR ed ρ * yrR (log ed d) ρ ≤ yrR ed ρ ^ yrR (log ed d) ρ := by
      rw [gu_pow_eq hEdρ]; exact right_le_opow _ one_lt_omega0
    have h2 : yrR ed ρ ^ yrR (log ed d) ρ * yrR (d / ed ^ log ed d) ρ ≤ yrR d ρ := by
      rw [yrR_dec hdG, ← yrR_base hEdE hGed]; exact le_self_add
    have h3 : yrR ed ρ ^ yrR (log ed d) ρ ≤
        yrR ed ρ ^ yrR (log ed d) ρ * yrR (d / ed ^ log ed d) ρ :=
      le_mul_of_one_le_right' (one_le_iff_pos.2 (yrR_pos hρE hρ1 hd0' (hdd.trans hdB) (g0d.trans hB.2.2.1)))
    exact (h1.trans (h3.trans h2)).trans_lt (yrR_mono hρE hρ1 heB hdE hgeρ hgdρ)
  have hat' : ∀ β, β ∈ TB ρ σ → β < yrR e ρ →
      ω ^ ((P + yrR ed ρ * yrR (log ed d) ρ) + β) ∈ TB ρ σ ∧
      pi σ ρ (ω ^ ((P + yrR ed ρ * yrR (log ed d) ρ) + β)) =
        ω ^ ((P' + yrR ed σ * yrR (log ed d) σ) + pi σ ρ β) := by
    intro β hβ hβB
    obtain ⟨s1, s2⟩ := pi_add hB hBK.1 hβ
    have hRE : InE (yrR e ρ) := by
      rw [yrR_base he hGe]; exact (yrA_facts hρE hρ1 he hGe heB hgeρ).1
    have := hat _ s1 ((inE_indec hRE).add_lt hlead hβB)
    rw [s2, hBK.2] at this
    rw [add_assoc, add_assoc]; exact this
  obtain ⟨u1, u2⟩ := IH _ hdd (hlt _ hdd) g0d _ _ hat'
  obtain ⟨v1, v2⟩ := IH _ hrd (hlt _ hrd) g0r P P' hat
  have e1 : ∀ x Q : Ordinal.{0}, InE (yrR ed x) → ω ^ Q * yrR d x =
      ω ^ (Q + yrR ed x * yrR (log ed d) x) * yrR (d / ed ^ log ed d) x +
        ω ^ Q * yrR (d % ed ^ log ed d) x := by
    intro x Q hx
    rw [yrR_dec hdG, ← yrR_base hEdE hGed, mul_add, ← mul_assoc, gu_pow_eq hx, ← opow_add]
  rw [e1 ρ P hEdρ, e1 σ P' hEdσ]
  obtain ⟨w1, w2⟩ := pi_add hB u1 v1
  exact ⟨w1, by rw [w2, u2, v2]⟩

/-- **LEMMA EXACT for every code `c < B_Γ`** at every pair of bases `σ < ρ` with the gate below `σ`. -/
theorem yr_pi : ∀ c, c < Tf.tfBG → yrG c < σ → yrR c ρ ∈ TB ρ σ ∧ pi σ ρ (yrR c ρ) = yrR c σ := by
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
  · rw [yrG_low hcG] at hg
    rw [yrR_low hcG, yrR_low hcG]
    exact gl_pi hB c hcG hg
  have hcE := yh_gfE_le hcG
  -- Lemma EXACT at the level and the index of a non-atom `ε`-number code `e ≤ c` with gate below `σ`
  have hLI : ∀ e, InE e → gcG 0 ≤ e → e ≤ c → yrG e < σ →
      (YhAt e → yrR (yhJ e) ρ ∈ TB ρ σ ∧ pi σ ρ (yrR (yhJ e) ρ) = yrR (yhJ e) σ) ∧
      (¬ YhAt e → yrR (yhK e) ρ ∈ TB ρ σ ∧ pi σ ρ (yrR (yhK e) ρ) = yrR (yhK e) σ) ∧
      (¬ YhAt e → yrR (yhI e) ρ ∈ TB ρ σ ∧ pi σ ρ (yrR (yhI e) ρ) = yrR (yhI e) σ) := by
    intro e he hGe hec hge
    have hgq : yrQE e < σ := by rw [yrG_base he hGe] at hge; exact hge
    refine ⟨fun hA => ?_, fun hA => ?_, fun hA => ?_⟩
    · obtain ⟨h1, h2⟩ := yr_idx_of hωσ hA (hec.trans_lt hc) hge
      exact IH _ (h1.trans_le hec) ((h1.trans_le hec).trans hc) h2
    · have hGe' : gcG 0 < e := lt_of_le_of_ne hGe (fun h => hA (h ▸ yhAt_gcG 0))
      have hke := (yhData_spec he hGe' hA).2.1
      exact IH _ (hke.trans_le hec) ((hke.trans_le hec).trans hc) (yr_E_parts hωσ hA hgq).1
    · have hGe' : gcG 0 < e := lt_of_le_of_ne hGe (fun h => hA (h ▸ yhAt_gcG 0))
      have hie := (yhData_spec he hGe' hA).2.2.1
      exact IH _ (hie.trans_le hec) ((hie.trans_le hec).trans hc) (yr_E_parts hωσ hA hgq).2
  by_cases hcI : InE c
  · obtain ⟨l0, l1, l2⟩ := hLI c hcI hcG le_rfl hg
    obtain ⟨b1, b2, -, -⟩ := yr_base_pi hB hcI hcG hc hg l0 l1 l2
    exact ⟨b1, b2⟩
  have hEc := gl_E_lt_self hcE hcI
  set e := guE c with hedef
  have he : InE e := guE_E c
  have hGe : gcG 0 ≤ e := yh_G_le_E hcG
  have hOe : Om1 < e := gl_Om1_lt_G0.trans_le hGe
  have heB : e < Tf.tfBG := hEc.trans hc
  have hge : yrG e < σ := yr_E_g hcG hg
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc, hdc⟩ := gl_parts hcE
  obtain ⟨g0k, g0d, g0r⟩ := yr_parts_g hωσ hcG hg
  have hcB' : c < eN e := gl_lt_eN hcE
  have hkN : log e c < eN e := hkc.trans hcB'
  obtain ⟨l0, l1, l2⟩ := hLI e he hGe hEc.le hge
  obtain ⟨b1, b2, b3, b4⟩ := yr_base_pi hB he hGe heB hge l0 l1 l2
  have hBK := yr_BK_pi hB he hGe heB hk hkN g0k ⟨b1, b2⟩ (fun hω => by
    have hk1 : 1 < log e c := lt_of_lt_of_le one_lt_omega0 hω
    have hEkc : e * log e c < c := (gu_mulE_lt_pow he hk1 hkN).trans_le (by
      exact (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0)).trans (le_self_add.trans_eq hdec))
    obtain ⟨-, hB', hg', -⟩ := yr_mulE he hGe heB _ hk hkN
    refine IH _ hEkc hB' (hg'.trans_lt (max_lt ?_ g0k))
    rw [yrG_base he hGe] at hge; exact hge)
  set Bρ := yrR e ρ with hBρdef
  set Bσ := yrR e σ with hBσdef
  obtain ⟨hBρE, hρB, -, -, hBO⟩ := yrA_facts hρE hρ1 he hGe heB (hge.trans hB.2.2.1)
  obtain ⟨hBσE, hσB, -, -, -⟩ := yrA_facts hσE hσ1 he hGe heB hge
  rw [← yrR_base he hGe] at hBρE hρB hBO hBσE hσB
  have hNO : eN Bρ < Om1 := eN_lt_Om1K hBO
  have hKN : yrR (log e c) ρ < eN Bρ := by
    rcases lt_or_ge (log e c) e with hkE | hkE
    · exact (yrR_mono hρE hρ1 heB hkE (hge.trans hB.2.2.1) (g0k.trans hB.2.2.1)).trans (lt_eN _)
    · obtain ⟨hEk, hgfk⟩ := gl_same he hOe hkE (hkc.trans hcB')
      have := yrR_top hρE hρ1 (hkc.trans hc) (hGe.trans hkE) (g0k.trans hB.2.2.1)
      rwa [hEk, ← yrR_base he hGe] at this
  -- the atoms `ω^{B·K+β}`
  have hat : ∀ β, β ∈ TB ρ σ → β < Bρ → ω ^ (Bρ * yrR (log e c) ρ + β) ∈ TB ρ σ ∧
      pi σ ρ (ω ^ (Bρ * yrR (log e c) ρ + β)) = ω ^ (Bσ * yrR (log e c) σ + pi σ ρ β) := by
    intro β hβ hβB
    have hlt : Bρ * yrR (log e c) ρ + β < eN Bρ :=
      (inE_indec (eN_E Bρ)).add_lt ((eN_E Bρ).mul_lt (lt_eN Bρ) hKN) (hβB.trans (lt_eN Bρ))
    rcases lt_or_ge (log e c) ω with hkω | hkω
    · obtain ⟨j, hj⟩ := lt_omega0.1 hkω
      obtain ⟨j0, rfl⟩ : ∃ j0 : ℕ, j = j0 + 1 :=
        Nat.exists_eq_succ_of_ne_zero (by rintro rfl; exact hk (by rw [hj]; rfl))
      rw [hj, yrR_nat, yrR_nat]
      obtain ⟨m1, m2⟩ := pi_mul_nat hB b1 b2 j0
      obtain ⟨n1, n2⟩ := pi_add hB m1 hβ
      have hc1 : ((j0 + 1 : ℕ) : Ordinal.{0}) = 1 + (j0 : Ordinal.{0}) := by
        rw [Nat.add_comm]; push_cast; rfl
      have eρ : Bρ * ((j0 + 1 : ℕ) : Ordinal.{0}) + β = Bρ + (Bρ * (j0 : Ordinal.{0}) + β) := by
        rw [hc1, mul_add, mul_one, add_assoc]
      have eσ : Bσ * ((j0 + 1 : ℕ) : Ordinal.{0}) + pi σ ρ β = Bσ + (Bσ * (j0 : Ordinal.{0}) + pi σ ρ β) := by
        rw [hc1, mul_add, mul_one, add_assoc]
      rw [hj, yrR_nat] at hlt
      obtain ⟨a1, a2⟩ := gu_atom_pi hB hBρE hBσE hρB hσB b1 b2 b3 b4 hNO n1 (by rw [← eρ]; exact hlt)
      rw [n2, m2] at a2
      rw [eρ, eσ]
      exact ⟨a1, a2⟩
    · have hKω : ω ≤ yrR (log e c) ρ := yr_omega_le hρE hρ1 hkω (hkc.trans hc) (g0k.trans hB.2.2.1)
      have hKω' : ω ≤ yrR (log e c) σ := yr_omega_le hσE hσ1 hkω (hkc.trans hc) g0k
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
  have hdig := yr_dig hB he hGe heB hge (fun j hj hgj => IH j (hj.trans hEc) (hj.trans heB) hgj)
    _ hdE g0d _ _ hat
  obtain ⟨r1, r2⟩ := IH _ hrc (hrc.trans hc) g0r
  rw [yrR_dec hcG, yrR_dec hcG, ← yrR_base he hGe, ← yrR_base he hGe, gu_pow_eq hBρE, gu_pow_eq hBσE]
  obtain ⟨w1, w2⟩ := pi_add hB hdig.1 r1
  exact ⟨w1, by rw [w2, hdig.2, r2]⟩

end Pi

end Googology.Trans.PoR.InaccPsi.R2.Yr
