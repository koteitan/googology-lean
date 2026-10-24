import Googology.Trans.PoR.InaccPsi.R2.SuRoad

/-!
# Offset code systems whose codes may contain `ψ_{Ω₂}`-atoms: `Su.SuCS` with the hull condition only for `0 < a`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Su.SuCS` asks every code `c` (and every `ω^e·c`) to lie in EVERY hull `Cl(a, b)` containing its gate, also for
`a = 0`.  A code `c ≥ Γ_{Ω₁+1} = ψ_{Ω₂}(0)` is in `Cl(a, b)` only for `0 < a`.  The field is used once, in the supply
(`Su.SuCS.suSup`), where `Ω_ω < a`.  `TbCS` is `Su.SuCS` with this field weakened to `0 < a`; every other field and
every proof is that of `R2.SuCS`:

* `TbCS.ofSu` (**every `Su.SuCS` is a `TbCS`** with the same reading, gate, bounds);
* `tbCode_uniq`, `tbCd` (**the code of an offset**), `tbCd_spec`, `tbCd_eq`, `tbCd_zero`, `tbLt_of_R`;
* `tbCode_lim`, `tbLim_pi` (**`π_{σ,ρ}(-1 + e(R c ρ)) = -1 + e(R c σ)`, `ω² ∣ R c ρ ⇒ ω² ∣ R c σ`**);
* `tbF` (**the offset map**: `π_{ρ,a}` on the multiples of `ω²`, the residue kept), `tbF_res`, `tbF_eq`, `tbOff`
  (**`Sl.SlOff (tbF ρ a) Os (V ρ)`**);
* `tbGood` (`η + y` is good for `y < V(P(η))`), `tbV_lt_Om1`, `tbCode_shift` (**`η_{ι(η)+g} = η + g`,
  `m_{ι(η)+g} = -1 + e(g)` for `0 < g < V(P(η))`**);
* `tbSup` (**the supply `υ_{μ+V(ρ_μ)} ≤ Θ_μ(G') ≤ r(μ)`** at every Range restart `μ` of code `G_{k+1}+1`, along the
  inverse reading `x ↦ tbCd ρ_μ x`).

No new axiom.  New definitions: `TbCS` (a structure of facts), `TbCS.ofSu`, `tbCd`, `tbF` (ordinal functions).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

/-- **An offset code system** (hull condition for `0 < a` only): readings `R c x` of the codes `c < B` at the
bases `x`, gates `G c`, the bound `V x`,
with Lemma EXACT for the readings and for the last exponents of limit codes. -/
structure TbCS where
  R : Ordinal.{0} → Ordinal.{0} → Ordinal.{0}
  G : Ordinal.{0} → Ordinal.{0}
  B : Ordinal.{0}
  V : Ordinal.{0} → Ordinal.{0}
  B_lim : IsSuccLimit B
  B_le : ∀ (S : InaccSeq.{0}) (k : ℕ), B ≤ Lc.lcTh S (k + 1)
  zero_R : ∀ x, R 0 x = 0
  zero_G : G 0 = 0
  succ_R : ∀ b x, b < B → R (b + 1) x = R b x + 1
  succ_G : ∀ b Z, b < B → IsSuccLimit Z → G b < Z → G (b + 1) < Z
  R_mono : ∀ x b c, InE x → c < B → b < c → G b < x → G c < x → R b x < R c x
  R_lt : ∀ x c, InE x → x < Om1 → c < B → G c < x → R c x < V x
  R_ex : ∀ x ν, InE x → x < Om1 → ν < V x → ∃ c, c < B ∧ G c < x ∧ R c x = ν
  R_pi : ∀ σ ρ c, Bases σ ρ → c < B → G c < σ → R c ρ ∈ TB ρ σ ∧ pi σ ρ (R c ρ) = R c σ
  R_ld : ∀ σ ρ c, Bases σ ρ → IsSuccLimit c → c < B → G c < σ →
    cdExp (R c ρ) ∈ TB ρ σ ∧ pi σ ρ (cdExp (R c ρ)) = cdExp (R c σ)
  R_mem : ∀ (S : InaccSeq.{0}) (a b c : Ordinal.{0}), 0 < a → c < B → G c < b →
    ∀ e ∈ S.CSet a b, ω ^ e * c ∈ S.CSet a b
  V_E : ∀ x, InE x → x < Om1 → InE (V x)
  V_gt : ∀ x, InE x → x < Om1 → x < V x
  V_le : ∀ x u, InE x → x < Om1 → x < u → UpsPt u → V x ≤ u

namespace TbCS

/-- **Every `Su.SuCS` is a `TbCS`.** -/
def ofSu (K : Su.SuCS) : TbCS where
  R := K.R
  G := K.G
  B := K.B
  V := K.V
  B_lim := K.B_lim
  B_le := K.B_le
  zero_R := K.zero_R
  zero_G := K.zero_G
  succ_R := K.succ_R
  succ_G := K.succ_G
  R_mono := K.R_mono
  R_lt := K.R_lt
  R_ex := K.R_ex
  R_pi := K.R_pi
  R_ld := K.R_ld
  R_mem := fun S a b c _ hc hg => K.R_mem S a b c hc hg
  V_E := K.V_E
  V_gt := K.V_gt
  V_le := K.V_le

variable (K : TbCS) {S : InaccSeq.{0}}

/-! ## The code of an offset -/

theorem pos_B : (0 : Ordinal.{0}) < K.B := K.B_lim.bot_lt

theorem succ_lt {b : Ordinal.{0}} (h : b < K.B) : b + 1 < K.B := K.B_lim.add_one_lt h

/-- **The code is unique.** -/
theorem tbCode_uniq {x c c' : Ordinal.{0}} (hx : InE x) (hc : c < K.B) (hc' : c' < K.B)
    (hg : K.G c < x) (hg' : K.G c' < x) (e : K.R c x = K.R c' x) : c = c' := by
  rcases lt_trichotomy c c' with h | h | h
  · exact absurd e (K.R_mono x c c' hx hc' h hg hg').ne
  · exact h
  · exact absurd e (K.R_mono x c' c hx hc h hg' hg).ne'

/-- A smaller reading has a smaller code. -/
theorem tbLt_of_R {x b c : Ordinal.{0}} (hx : InE x) (hb : b < K.B) (_hc : c < K.B)
    (hgb : K.G b < x) (hgc : K.G c < x) (h : K.R b x < K.R c x) : b < c := by
  rcases lt_trichotomy b c with h' | h' | h'
  · exact h'
  · rw [h'] at h; exact absurd h (lt_irrefl _)
  · exact absurd h (not_lt.2 (K.R_mono x c b hx hb h' hgc hgb).le)

/-- **The code of `ν` at the base `x`.** -/
noncomputable def tbCd (x ν : Ordinal.{0}) : Ordinal.{0} := by
  classical
  exact if h : ∃ c, c < K.B ∧ K.G c < x ∧ K.R c x = ν then Classical.choose h else 0

theorem tbCd_spec {x ν : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hν : ν < K.V x) :
    K.tbCd x ν < K.B ∧ K.G (K.tbCd x ν) < x ∧ K.R (K.tbCd x ν) x = ν := by
  have h := K.R_ex x ν hx hx1 hν
  rw [tbCd, dif_pos h]
  exact Classical.choose_spec h

theorem tbCd_eq {x c : Ordinal.{0}} (hx : InE x) (hc : c < K.B) (hg : K.G c < x) :
    K.tbCd x (K.R c x) = c := by
  have h : ∃ c', c' < K.B ∧ K.G c' < x ∧ K.R c' x = K.R c x := ⟨c, hc, hg, rfl⟩
  rw [tbCd, dif_pos h]
  obtain ⟨h1, h2, h3⟩ := Classical.choose_spec h
  exact K.tbCode_uniq hx h1 hc h2 hg h3

theorem tbCd_zero {x : Ordinal.{0}} (hx : InE x) : K.tbCd x 0 = 0 := by
  have := K.tbCd_eq hx K.pos_B (by rw [K.zero_G]; exact hx.pos)
  rwa [K.zero_R] at this

theorem R_pos {x c : Ordinal.{0}} (hx : InE x) (hc : c < K.B) (hc0 : c ≠ 0) (hg : K.G c < x) :
    0 < K.R c x := by
  have := K.R_mono x 0 c hx hc (pos_iff_ne_zero.2 hc0) (by rw [K.zero_G]; exact hx.pos) hg
  rwa [K.zero_R] at this

/-! ## Limit codes: the last exponent moves with the base change -/

/-- A code whose reading is a nonzero multiple of `ω` is a limit code. -/
theorem tbCode_lim {x c : Ordinal.{0}} (hc : c < K.B) (h0 : K.R c x ≠ 0) (hd : ω ∣ K.R c x) :
    IsSuccLimit c := by
  rcases zero_or_succ_or_isSuccLimit c with h | ⟨b, hb⟩ | hl
  · rw [h, K.zero_R] at h0; exact absurd rfl h0
  · exfalso
    have hbc : c = b + 1 := by rw [← succ_eq_add_one]; first | exact hb | exact hb.symm
    have hbB : b < K.B := lt_of_lt_of_le (lt_add_one b) (hbc ▸ hc.le)
    rw [hbc, K.succ_R b x hbB] at hd
    exact Sr.srNot_dvd_succ _ hd
  · exact hl

/-- **The last exponent moves with the base change**: `π_{σ,ρ}(-1 + e(R c ρ)) = -1 + e(R c σ)`, and
`ω² ∣ R c ρ ⇒ ω² ∣ R c σ` (limit codes with gate below `σ`). -/
theorem tbLim_pi {σ ρ c : Ordinal.{0}} (hB : Bases σ ρ) (hc : c < K.B) (hl : IsSuccLimit c)
    (hg : K.G c < σ) :
    pi σ ρ (cdOff (cdExp (K.R c ρ))) = cdOff (cdExp (K.R c σ)) ∧
      (ω ^ 2 ∣ K.R c ρ → ω ^ 2 ∣ K.R c σ) := by
  obtain ⟨hT, hpi⟩ := K.R_ld σ ρ c hB hl hc hg
  have hσE : InE σ := hB.1
  have hρE : InE ρ := hB.2.1
  have hc0 : c ≠ 0 := hl.bot_lt.ne'
  have hrρ : K.R c ρ ≠ 0 := (K.R_pos hρE hc hc0 (hg.trans hB.2.2.1)).ne'
  have hrσ : K.R c σ ≠ 0 := (K.R_pos hσE hc hc0 hg).ne'
  set e := cdExp (K.R c ρ) with hedef
  set e' := cdExp (K.R c σ) with he'def
  have hωσ : ω < σ := Sl.slE_omega_lt hσE
  have hdv : ∀ (y : Ordinal.{0}), y ≠ 0 → 2 ≤ cdExp y → ω ^ 2 ∣ y := fun y hy h2 => by
    have h2' : ((2 : ℕ) : Ordinal.{0}) ≤ cdExp y := by exact_mod_cast h2
    have := (opow_dvd_opow ω h2').trans (cdExp_dvd hy)
    rwa [Ordinal.opow_natCast] at this
  have h2e : ω ^ 2 ∣ K.R c ρ → 2 ≤ e := fun h => by
    have h' : ω ^ ((2 : ℕ) : Ordinal.{0}) ∣ K.R c ρ := by rwa [Ordinal.opow_natCast]
    exact_mod_cast cdExp_max hrρ h'
  rcases lt_or_ge e ω with heω | heω
  · have hee : e' = e := by rw [← hpi]; exact pi_lt hB (heω.trans hωσ)
    refine ⟨?_, fun h => hdv _ hrσ (by rw [← he'def, hee]; exact h2e h)⟩
    rw [hee]
    exact pi_lt hB ((cdOff_le e).trans_lt (heω.trans hωσ))
  · have hωT : ω ∈ TB ρ σ := (TB_inter_lt hB (Sl.slE_omega_lt hρE)).2 hωσ
    have hπω : pi σ ρ ω = ω := pi_lt hB hωσ
    have hωe' : ω ≤ e' := by
      rcases heω.lt_or_eq with h | h
      · have := (pi_bijOn hB).2 hωT hT h
        rw [hπω, hpi] at this; exact this.le
      · rw [← hpi, ← h, hπω]
    rw [Sr.srOff_ge heω, Sr.srOff_ge hωe']
    refine ⟨hpi, fun _ => hdv _ hrσ ?_⟩
    exact ((natCast_lt_omega0 2).le.trans hωe')

/-! ## The offset map -/

/-- **The offset map**: `π_{ρ,a}` (through the codes) on the multiples of `ω²`, the residue kept. -/
noncomputable def tbF (ρ a x : Ordinal.{0}) : Ordinal.{0} :=
  ω ^ 2 * (K.R (K.tbCd a (ω ^ 2 * (x / ω ^ 2))) ρ / ω ^ 2) + x % ω ^ 2

theorem tbF_res (ρ a q t : Ordinal.{0}) (ht : t < ω ^ 2) :
    K.tbF ρ a (ω ^ 2 * q + t) = K.tbF ρ a (ω ^ 2 * q) + t := by
  have h1 := Sr.srW_div q t ht
  have h2 := Sr.srW_div q 0 Sr.srW_pos
  rw [add_zero] at h2
  unfold tbF
  rw [h1.1, h1.2, h2.1, h2.2, add_zero]

/-- `ω² ∣ R (tbCd a w) ρ` for `ω² ∣ w` (gate below `ρ`). -/
theorem tbFw_dvd {ρ a w : Ordinal.{0}} (hB : Bases ρ a) (hw : w < K.V a) (hd : ω ^ 2 ∣ w)
    (hg : K.G (K.tbCd a w) < ρ) : ω ^ 2 ∣ K.R (K.tbCd a w) ρ := by
  obtain ⟨hAW, -, hr⟩ := K.tbCd_spec hB.2.1 hB.2.2.2 hw
  rcases eq_or_ne w 0 with rfl | hw0
  · rw [K.tbCd_zero hB.2.1, K.zero_R]; exact dvd_zero _
  have hdω : ω ∣ K.R (K.tbCd a w) a := by
    rw [hr]; exact (dvd_pow_self ω two_ne_zero).trans hd
  have hl := K.tbCode_lim hAW (by rw [hr]; exact hw0) hdω
  exact (K.tbLim_pi hB hAW hl hg).2 (by rw [hr]; exact hd)

theorem tbF_eq {ρ a g : Ordinal.{0}} (hB : Bases ρ a) (hg : g < K.V a) (hd : ω ^ 2 ∣ g)
    (hgt : K.G (K.tbCd a g) < ρ) : K.tbF ρ a g = K.R (K.tbCd a g) ρ := by
  have hm : g % ω ^ 2 = 0 := (Ordinal.dvd_iff_mod_eq_zero).1 hd
  have e : ω ^ 2 * (g / ω ^ 2) = g := by
    have := Ordinal.div_add_mod g (ω ^ 2); rwa [hm, add_zero] at this
  have hF := K.tbFw_dvd hB hg hd hgt
  have hm' : K.R (K.tbCd a g) ρ % ω ^ 2 = 0 := (Ordinal.dvd_iff_mod_eq_zero).1 hF
  have e' : ω ^ 2 * (K.R (K.tbCd a g) ρ / ω ^ 2) = K.R (K.tbCd a g) ρ := by
    have := Ordinal.div_add_mod (K.R (K.tbCd a g) ρ) (ω ^ 2); rwa [hm', add_zero] at this
  unfold tbF
  rw [e, hm, add_zero, e']

/-- **The offset map is an `Sl.SlOff` with bound `V ρ`** when every gate is below `ρ`. -/
theorem tbOff {ρ a : Ordinal.{0}} (hB : Bases ρ a) (Os : Finset Ordinal.{0}) (hOs : ∀ d ∈ Os, d < K.V a)
    (hgt : ∀ d ∈ Os, K.G (K.tbCd a (ω ^ 2 * (d / ω ^ 2))) < ρ) :
    Sl.SlOff (K.tbF ρ a) Os (K.V ρ) := by
  have hρE : InE ρ := hB.1
  have haE : InE a := hB.2.1
  have ha1 : a < Om1 := hB.2.2.2
  have hρ1 : ρ < Om1 := hB.2.2.1.trans ha1
  have hwd : ∀ d, ω ^ 2 * (d / ω ^ 2) ≤ d := fun d =>
    le_self_add.trans_eq (Ordinal.div_add_mod d (ω ^ 2))
  have hVa : 0 < K.V a := haE.pos.trans (K.V_gt a haE ha1)
  have hW : ∀ d ∈ insert 0 Os, ω ^ 2 * (d / ω ^ 2) < K.V a ∧
      K.G (K.tbCd a (ω ^ 2 * (d / ω ^ 2))) < ρ := by
    intro d hd
    rcases Finset.mem_insert.1 hd with rfl | hd
    · simp only [Ordinal.zero_div, mul_zero]
      rw [K.tbCd_zero haE, K.zero_G]; exact ⟨hVa, hρE.pos⟩
    · exact ⟨(hwd d).trans_lt (hOs d hd), hgt d hd⟩
  have hdecF : ∀ d ∈ insert 0 Os, ω ^ 2 * (K.R (K.tbCd a (ω ^ 2 * (d / ω ^ 2))) ρ / ω ^ 2) =
      K.R (K.tbCd a (ω ^ 2 * (d / ω ^ 2))) ρ := by
    intro d hd
    obtain ⟨h1, h2⟩ := hW d hd
    have hF := K.tbFw_dvd hB h1 (dvd_mul_right _ _) h2
    have hm' := (Ordinal.dvd_iff_mod_eq_zero).1 hF
    have := Ordinal.div_add_mod (K.R (K.tbCd a (ω ^ 2 * (d / ω ^ 2))) ρ) (ω ^ 2)
    rwa [hm', add_zero] at this
  refine ⟨?_, fun q t ht => K.tbF_res ρ a q t ht, fun q => ?_, ?_, fun d hd => ?_⟩
  · unfold tbF
    simp only [Ordinal.zero_div, mul_zero, Ordinal.zero_mod, add_zero]
    rw [K.tbCd_zero haE, K.zero_R, Ordinal.zero_div, mul_zero]
  · have h := (Sr.srW_div q 0 Sr.srW_pos).2
    rw [add_zero] at h
    unfold tbF
    rw [h, add_zero]; exact dvd_mul_right _ _
  · intro d hd d' hd' hdd
    have hd0 : d ∈ insert 0 Os := Finset.mem_coe.1 hd
    have hd0' : d' ∈ insert 0 Os := Finset.mem_coe.1 hd'
    have ed := Ordinal.div_add_mod d (ω ^ 2)
    have ed' := Ordinal.div_add_mod d' (ω ^ 2)
    have hr := Ordinal.mod_lt d Sr.srW_pos.ne'
    have hr' := Ordinal.mod_lt d' Sr.srW_pos.ne'
    have hqq : d / ω ^ 2 ≤ d' / ω ^ 2 := by
      by_contra hlt
      push Not at hlt
      have : d' < d := by
        calc d' = ω ^ 2 * (d' / ω ^ 2) + d' % ω ^ 2 := ed'.symm
          _ < ω ^ 2 * (d' / ω ^ 2) + ω ^ 2 := (add_lt_add_iff_left _).2 hr'
          _ = ω ^ 2 * (d' / ω ^ 2 + 1) := by rw [mul_add_one]
          _ ≤ ω ^ 2 * (d / ω ^ 2) := mul_le_mul_right (Order.add_one_le_of_lt hlt) _
          _ ≤ d := hwd d
      exact absurd hdd (not_lt.2 this.le)
    unfold tbF
    rcases hqq.lt_or_eq with hlt | heq
    · obtain ⟨hw1, hg1⟩ := hW d hd0
      obtain ⟨hw2, hg2⟩ := hW d' hd0'
      obtain ⟨hA1, ha1', hr1⟩ := K.tbCd_spec haE ha1 hw1
      obtain ⟨hA2, ha2', hr2⟩ := K.tbCd_spec haE ha1 hw2
      have hww : ω ^ 2 * (d / ω ^ 2) < ω ^ 2 * (d' / ω ^ 2) := (mul_lt_mul_iff_right₀ Sr.srW_pos).2 hlt
      have hAA := K.tbLt_of_R haE hA1 hA2 ha1' ha2' (by rw [hr1, hr2]; exact hww)
      have hFF := K.R_mono ρ _ _ hρE hA2 hAA hg1 hg2
      rw [← hdecF d hd0, ← hdecF d' hd0'] at hFF
      have hΦ := (mul_lt_mul_iff_right₀ Sr.srW_pos).1 hFF
      calc _ < ω ^ 2 * (K.R (K.tbCd a (ω ^ 2 * (d / ω ^ 2))) ρ / ω ^ 2) + ω ^ 2 :=
            (add_lt_add_iff_left _).2 hr
        _ = ω ^ 2 * (K.R (K.tbCd a (ω ^ 2 * (d / ω ^ 2))) ρ / ω ^ 2 + 1) := by rw [mul_add_one]
        _ ≤ ω ^ 2 * (K.R (K.tbCd a (ω ^ 2 * (d' / ω ^ 2))) ρ / ω ^ 2) :=
            mul_le_mul_right (Order.add_one_le_of_lt hΦ) _
        _ ≤ _ := le_self_add
    · have hrr : d % ω ^ 2 < d' % ω ^ 2 := by
        have h1 : ω ^ 2 * (d / ω ^ 2) + d % ω ^ 2 < ω ^ 2 * (d / ω ^ 2) + d' % ω ^ 2 := by
          calc _ = d := ed
            _ < d' := hdd
            _ = ω ^ 2 * (d' / ω ^ 2) + d' % ω ^ 2 := ed'.symm
            _ = _ := by rw [heq]
        exact (add_lt_add_iff_left _).1 h1
      rw [← heq]
      exact (add_lt_add_iff_left _).2 hrr
  · have hd0 : d ∈ insert 0 Os := Finset.mem_insert_of_mem hd
    obtain ⟨hw1, hg1⟩ := hW d hd0
    obtain ⟨hA1, -, -⟩ := K.tbCd_spec haE ha1 hw1
    unfold tbF
    rw [hdecF d hd0]
    have hE := K.V_E ρ hρE hρ1
    have hW2 : ω ^ 2 < K.V ρ := by
      rw [pow_two]; exact hE.mul_lt (Sl.slE_omega_lt hE) (Sl.slE_omega_lt hE)
    exact (inE_indec hE).add_lt (K.R_lt ρ _ hρE hρ1 hA1 hg1) ((Ordinal.mod_lt d Sr.srW_pos.ne').trans hW2)

/-! ## Names and codes of the inner restarts below `V(P(η))` -/

theorem tbV_le_succ {η : Ordinal.{0}} (hg : Bt.Good S η) : K.V (Nm.Pv S η) ≤ Nm.Pv S (η + 1) := by
  have h1 : Nm.Pv S η < Om1 := by rw [Br.Om1_eq]; exact Nm.Pv_lt_Om1 S η
  have e : upsilon (Bt.iota S (η + 1)) = Nm.Pv S (η + 1) := Bt.ups_iota S (η + 1)
  have hu : UpsPt (Nm.Pv S (η + 1)) := by
    rw [← e]; exact upsPt_upsilon (lt_of_lt_of_le zero_lt_one (Bt.one_le_iota _))
  exact K.V_le _ _ (Sl.slPv_E η) h1 (Nm.Pv_lt_succ hg) hu

theorem tbV_lt_Om1 {η : Ordinal.{0}} (hg : Bt.Good S η) : K.V (Nm.Pv S η) < Om 1 :=
  (K.tbV_le_succ hg).trans_lt (Nm.Pv_lt_Om1 S _)

/-- `η + y` is good for every `y < V(P(η))`. -/
theorem tbGood {η y : Ordinal.{0}} (hg : Bt.Good S η) (hy : y < K.V (Nm.Pv S η)) : Bt.Good S (η + y) := by
  refine Rz.rz_good_shift hg ?_
  by_cases hyP : y < Nm.Pv S η
  · exact hyP.trans_le (Nm.Pv_mono le_self_add)
  · have h1 : 1 ≤ y := Order.one_le_iff_ne_zero.2 fun h0 => by
      rw [h0] at hyP; exact hyP (Sl.slPv_E (S := S) η).pos
    exact (hy.trans_le (K.tbV_le_succ hg)).trans_le (Nm.Pv_mono (add_le_add le_rfl h1))

/-- **`η_{ι(η)+g} = η + g` and `m_{ι(η)+g} = -1 + e(g)`** for `0 < g < V(P(η))` (`ω^{Ω₁} ∣ η`). -/
theorem tbCode_shift {η g : Ordinal.{0}} (hg : Bt.Good S η) (hdiv : ω ^ Om 1 ∣ η) (hg0 : g ≠ 0)
    (hgP : g < K.V (Nm.Pv S η)) :
    cdEta S (Bt.iota S η + g) = η + g ∧ cdCode S (Bt.iota S η + g) = cdOff (cdExp g) := by
  have hg1 : g < Om 1 := hgP.trans (K.tbV_lt_Om1 hg)
  have hι : Bt.iota S (η + g) = Bt.iota S η + g :=
    Pp.ppIota_add η g fun y hy => K.tbGood hg (hy.trans hgP)
  have he : cdEta S (Bt.iota S η + g) = η + g := cdEta_unique (K.tbGood hg hgP) hι
  refine ⟨he, ?_⟩
  unfold cdCode
  rw [he]
  have hexp := Ls.lsExp_add hdiv hg0 hg1
  have h2 : cdExp (η + g) < Om (1 + 1) := by
    rw [hexp]
    exact ((Ls.lsExp_le hg0).trans_lt hg1).trans (Om_lt_Om.2 (lt_add_one 1))
  rw [cdCodeOf_of_lt h2, hexp]

/-! ## The supply below `V(ρ_μ)` -/

/-- **The supply up to `V(ρ_μ)`**: `υ_{μ+V(ρ_μ)} ≤ Θ_μ(G') ≤ r(μ)` at every Range restart `μ` with code
`G_{k+1} + 1`, along the inverse reading `x ↦ tbCd ρ_μ x`. -/
theorem tbSup (k : ℕ) {μ : Ordinal.{0}} (hR : CdRange S μ) (hc : cdCode S μ = Ls.lsG S (k + 1) + 1) :
    upsilon (μ + K.V (upsilon μ)) ≤ cdTheta S μ (Ls.lsG S (k + 1)) ∧
      upsilon (μ + K.V (upsilon μ)) ≤ cdR S μ := by
  obtain ⟨hgμ, -, hpv⟩ := Ra.raName hR
  have hρE : InE (upsilon μ) := by rw [← hpv]; exact Sl.slPv_E _
  have hρΩ : upsilon μ < Om 1 := So.soRho_lt_Om1 hR
  have hρ1 : upsilon μ < Om1 := by rw [Br.Om1_eq]; exact hρΩ
  have hspec := fun x (hx : x < K.V (upsilon μ)) => K.tbCd_spec hρE hρ1 hx
  have hVE := K.V_E _ hρE hρ1
  refine So.soSup_gen hR hc (So.soE_lim hVE) (fun y hy => K.tbGood hgμ (by rw [hpv]; exact hy))
    (by have := K.tbV_lt_Om1 hgμ; rw [hpv] at this; exact this.le) (K.tbCd (upsilon μ)) ?_ ?_ ?_ ?_
  · intro x hx
    have hx' : x < K.V (upsilon μ) := (lt_add_one x).trans hx
    obtain ⟨hA, hg, hr⟩ := hspec x hx'
    have hg1 : K.G (K.tbCd (upsilon μ) x + 1) < upsilon μ := K.succ_G _ _ hA (So.soE_lim hρE) hg
    have := K.tbCd_eq hρE (K.succ_lt hA) hg1
    rw [K.succ_R _ _ hA, hr] at this
    exact this
  · intro y x hyx hx
    rcases hyx.lt_or_eq with h | h
    · obtain ⟨hA, hg, hr⟩ := hspec x hx
      obtain ⟨hA', hg', hr'⟩ := hspec y (h.trans hx)
      exact (K.tbLt_of_R hρE hA' hA hg' hg (by rw [hr, hr']; exact h)).le
    · rw [h]
  · intro x hx a b ha hb
    obtain ⟨hA, hg, -⟩ := hspec x hx
    refine CSet.add_mem (ConjT.OmW_mem S a b) ?_
    have := K.R_mem S a b _ (lt_of_le_of_lt zero_le ha) hA (hg.trans_le hb) _ (Ls.lsTh_mem ha 2)
    rwa [Ls.lsTh_opow] at this
  · intro x hx
    obtain ⟨hA, -, -⟩ := hspec x hx
    exact hA.trans_le (K.B_le S k)

end TbCS

end Googology.Trans.PoR.InaccPsi.R2.Tb
