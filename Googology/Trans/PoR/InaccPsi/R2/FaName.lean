import Googology.Trans.PoR.InaccPsi.R2.FaClose
import Googology.Trans.PoR.InaccPsi.R2.XiCont
import Googology.Trans.PoR.InaccPsi.R2.SfNF

/-!
# Fa: THE CODES OF THE RESTARTS NEAR A RESTART, AND THE READING OF THE CODE BELOW THE NEXT HIGH NAME

The induction above `ι(Ω₂)` runs on the code `m_λ`, not on the restart.  Let `η = η_λ = η₀ + ω^e`, `m = m_λ`, `m' = faM m` (`cdOff m' = m`).

* `fa_code_up`: a restart `λ' ∈ (λ, ι(η + ω^{m'}))` has `m_λ' < m` (its name is `η + ζ`, `ζ < ω^{m'}`, so `e(η + ζ) < m'`);
* `fa_code_down`: a restart `μ ∈ (ι(η₀), λ)` has `m_μ < m`;
* `fa_T_C`: `T x ∈ Cl(E, ψ₂ E)` for `x ∈ D ∩ Cl(E, ψ₂ E)`;
* `fa_G_lt`: for a closed atom `w = ψ₂(E) > θ`, `E < Ω_ω·2`: `G(E) < A + w`;
* `fa_read_lt` (**`Θ_λ(c) < P(η + ω^{faM c})`** for a code `c ∈ [1, P')`).

No new axiom.  New definition: `faM`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Fa

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Zr Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xi
  Googology.Trans.PoR.InaccPsi.R2.Kz Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Ul
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

theorem fa_nat_sub (k : ℕ) : ((k : Ordinal.{0}) + 1) - 1 = k := by
  have e : ((k : Ordinal.{0}) + 1) = 1 + (k : Ordinal.{0}) := by
    have : ((k + 1 : ℕ) : Ordinal.{0}) = ((1 + k : ℕ) : Ordinal.{0}) := by rw [add_comm]
    simpa using this
  rw [e, Ordinal.add_sub_cancel]

/-- The inverse of `cdOff`: `cdOff (faM m) = m`. -/
noncomputable def faM (m : Ordinal.{0}) : Ordinal.{0} := if m < ω then m + 1 else m

theorem cdOff_faM (m : Ordinal.{0}) : cdOff (faM m) = m := by
  unfold faM cdOff
  by_cases h : m < ω
  · have h1 : m + 1 < ω := isSuccLimit_omega0.add_one_lt h
    rw [if_pos h, if_pos h1]
    obtain ⟨n, rfl⟩ := lt_omega0.1 h
    exact fa_nat_sub n
  · rw [if_neg h, if_neg h]

theorem le_faM (m : Ordinal.{0}) : m ≤ faM m := by
  unfold faM; split_ifs
  · exact le_self_add
  · exact le_rfl

theorem faM_lt_SC {m q : Ordinal.{0}} (hq : SC q) (hm : m < q) : faM m < q := by
  unfold faM; split_ifs
  · exact hq.add_one_lt hm
  · exact hm

theorem cdOff_lt_of_lt_faM {m e : Ordinal.{0}} (hm : m ≠ 0) (he : e < faM m) : cdOff e < m := by
  unfold faM at he
  by_cases h : m < ω
  · rw [if_pos h] at he
    have hem : e ≤ m := Order.lt_add_one_iff.1 he
    have heω : e < ω := hem.trans_lt h
    unfold cdOff
    rw [if_pos heω]
    rcases eq_or_ne e 0 with rfl | h0
    · rw [Ordinal.zero_sub]; exact pos_iff_ne_zero.2 hm
    · have h1 : (1 : Ordinal.{0}) ≤ e := one_le_iff_ne_zero.2 h0
      obtain ⟨n, rfl⟩ := lt_omega0.1 heω
      have hn0 : n ≠ 0 := by rintro rfl; exact h0 (by simp)
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have e1 : (((k + 1 : ℕ) : Ordinal.{0}) - 1) = (k : Ordinal.{0}) := by
        rw [Nat.cast_succ]; exact fa_nat_sub k
      rw [e1]
      refine lt_of_lt_of_le ?_ hem
      exact_mod_cast Nat.lt_succ_self k
  · rw [if_neg h] at he
    exact (cdOff_le e).trans_lt he

/-- `ω^{m'} ∤ η'` for `η < η' < η + ω^{m'}`. -/
theorem fa_not_dvd {η η' a : Ordinal.{0}} (h1 : η < η') (h2 : η' < η + ω ^ a) : ¬ ω ^ a ∣ η' := by
  intro hd
  have hp : (0 : Ordinal.{0}) < ω ^ a := opow_pos a omega0_pos
  set b := ω ^ a * (η / ω ^ a) with hb
  have hbη : b ≤ η := by
    conv_rhs => rw [← Ordinal.div_add_mod η (ω ^ a)]
    exact le_self_add
  have hbd : ω ^ a ∣ b := dvd_mul_right _ _
  have hle := dvd_next hd hbd (hbη.trans_lt h1)
  have hmod : η % ω ^ a + ω ^ a = ω ^ a :=
    Ordinal.add_of_omega0_opow_le (Ordinal.mod_lt η hp.ne') le_rfl
  have e : η + ω ^ a = b + ω ^ a := by
    conv_lhs => rw [← Ordinal.div_add_mod η (ω ^ a)]
    rw [add_assoc, hmod]
  rw [e] at h2
  exact absurd hle (not_le.2 h2)

/-- **A restart inside `(λ, ι(η + ω^{m'}))` has a smaller code.** -/
theorem fa_code_up {l l' : Ordinal.{0}} (hl0 : l ≠ 0) (hge : l < l') {ηx : Ordinal.{0}} (hX : upsilon l < Pv S ηx)
    (hm0 : cdCode S l ≠ 0) (hm2 : cdCode S l < Om (1 + 1))
    (hl' : l' < iota S (cdEta S l + ω ^ faM (cdCode S l))) : cdCode S l' < cdCode S l := by
  obtain ⟨hg, he, -, -⟩ := cdEta_pv_spec hl0 hX
  have hl'0 : l' ≠ 0 := (lt_of_le_of_lt zero_le hge).ne'
  obtain ⟨hg', he', hlt'⟩ := cdEta_spec (S := S) (one_le_iff_ne_zero.2 hl'0) hl'
  have h1 : cdEta S l < cdEta S l' := by
    by_contra hc
    have h := iota_mono (S := S) (cdEta S l) _ (not_lt.1 hc)
    rw [he, he'] at h
    exact absurd hge (not_lt.2 h)
  have hne : cdEta S l' ≠ 0 := (lt_of_le_of_lt zero_le h1).ne'
  have hnd := fa_not_dvd h1 hlt'
  have hexp : cdExp (cdEta S l') < faM (cdCode S l) := by
    by_contra hc
    exact hnd ((opow_dvd_opow ω (not_lt.1 hc)).trans (cdExp_dvd hne))
  have hO2 : SC (Om (1 + 1 : Ordinal.{0})) := SC_Om (by simp)
  have hexp2 : cdExp (cdEta S l') < Om (1 + 1) := hexp.trans (faM_lt_SC hO2 hm2)
  show cdCodeOf S (cdEta S l') < _
  rw [cdCodeOf_of_lt hexp2]
  exact cdOff_lt_of_lt_faM hm0 hexp

/-- **A restart inside `(ι(η₀), λ)` has a smaller code** (`η_λ = η₀ + ω^e`, `2 ≤ e`). -/
theorem fa_code_down {l μ η0 e : Ordinal.{0}} (hl0 : l ≠ 0) {ηx : Ordinal.{0}} (hX : upsilon l < Pv S ηx)
    (hAL : ConjT.Aη S (cdEta S l) < S.Lam) (hdec : cdEta S l = η0 + ω ^ e) (hd : ω ^ e ∣ η0) (he2 : 2 ≤ e)
    (h0 : iota S η0 < μ) (h1 : μ < l) : cdCode S μ < cdCode S l := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hO2 : SC (Om (1 + 1 : Ordinal.{0})) := SC_Om (by simp)
  obtain ⟨hg, he, -, hpv⟩ := cdEta_pv_spec hl0 hX
  have hμ0 : μ ≠ 0 := (lt_of_le_of_lt zero_le h0).ne'
  have hμι : μ < iota S (cdEta S l) := by rw [he]; exact h1
  obtain ⟨hgμ, heμ, hltμ⟩ := cdEta_spec (S := S) (one_le_iff_ne_zero.2 hμ0) hμι
  set x := cdEta S μ with hxdef
  set η := cdEta S l with hηdef
  have hx0 : η0 < x := by
    by_contra hc
    have h := iota_mono (S := S) η0 _ (not_lt.1 hc)
    rw [heμ] at h
    exact absurd h0 (not_lt.2 h)
  have hxm : x < η0 + ω ^ e := by rw [← hdec]; exact hltμ
  obtain ⟨hxe, -⟩ := cdWin hd hx0 hxm
  have hAx : ConjT.Aη S x < ConjT.Aη S η := A_lt_A_iff.2 hltμ
  have hxne : x ≠ 0 := (lt_of_le_of_lt zero_le hx0).ne'
  by_cases hE : e < Om (1 + 1)
  · have hη2 : cdExp η = e := by rw [hdec]; exact xi_exp_add η0 e
    have hxe2 : cdExp x < Om (1 + 1) := hxe.trans hE
    show cdCodeOf S x < cdCodeOf S η
    rw [cdCodeOf_of_lt hxe2, cdCodeOf_of_lt (by rw [hη2]; exact hE), hη2]
    have he1 : (2 : Ordinal.{0}) = ((2 : ℕ) : Ordinal.{0}) := by norm_num
    by_cases heω : e < ω
    · have hxω : cdExp x < ω := hxe.trans heω
      unfold cdOff
      rw [if_pos hxω, if_pos heω]
      obtain ⟨n, hn⟩ := lt_omega0.1 heω
      obtain ⟨k, hk⟩ := lt_omega0.1 hxω
      rw [hn, hk]
      rw [hn, hk] at hxe
      have hkn : k < n := by exact_mod_cast hxe
      rw [hn, he1] at he2
      have hn2 : 2 ≤ n := by exact_mod_cast he2
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have e1 : (((n' + 1 : ℕ) : Ordinal.{0}) - 1) = (n' : Ordinal.{0}) := by
        rw [Nat.cast_succ]; exact fa_nat_sub n'
      rw [e1]
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · have : ((0 : ℕ) : Ordinal.{0}) - 1 = 0 := by simp
        rw [this]
        have hn'0 : 0 < n' := by omega
        exact_mod_cast hn'0
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        have e2 : (((k' + 1 : ℕ) : Ordinal.{0}) - 1) = (k' : Ordinal.{0}) := by
          rw [Nat.cast_succ]; exact fa_nat_sub k'
        rw [e2]
        have : k' < n' := by omega
        exact_mod_cast this
    · unfold cdOff
      rw [if_neg heω]
      split_ifs with hxω
      · exact (Ordinal.sub_le_self _ _).trans_lt hxe
      · exact hxe
  · have hη2 : cdExp η = e := by rw [hdec]; exact xi_exp_add η0 e
    have hpi : cdCodeOf S η = S.psi (ConjT.Aη S η) (Om (1 + 1)) := by
      unfold cdCodeOf
      rw [if_neg (by rw [hη2]; exact hE)]
      rfl
    show cdCodeOf S x < cdCodeOf S η
    rw [hpi]
    have hPx : Pv S x ≤ S.psi (ConjT.Aη S η) (Om (1 + 1)) :=
      (Pv_lt_Om1 S x).le.trans (psiS_bounds (S := S) (ConjT.Aη S η) 1).1.le
    by_cases hxO : cdExp x < Om (1 + 1)
    · rw [cdCodeOf_of_lt hxO]
      have hcomp : Comp (cdExp x) x := by
        obtain ⟨η1, hdec1, -⟩ := cdExp_decomp hxne
        exact ⟨η1, 0, opow_pos _ omega0_pos, by rw [add_zero]; exact hdec1⟩
      have hLam : Pv S x ≤ S.Lam := (Pv_lt_Om1 S x).le.trans ((Low.Om_one_le_I 0).trans (S.I_lt_Lam 0).le)
      have hQ := (MQ_of_mem_CSet (S := S) (e := ConjT.Aη S x + 1) (g := Pv S x) le_rfl le_rfl hLam hgμ).1
      have hmem0 : ω ^ cdExp x ∈ S.CSet (ConjT.Aη S x + 1) (Pv S x) := (hQ.1 _ hcomp).1
      have hmem : ω ^ cdExp x ∈ S.CSet (ConjT.Aη S η) (S.psi (ConjT.Aη S η) (Om (1 + 1))) :=
        CSet_mono (Order.add_one_le_of_lt hAx) hPx hmem0
      have h2 : ω ^ cdExp x < Om (1 + 1) := by
        rw [← Low.opow_eq_self_of_SC hO2]
        exact (opow_lt_opow_iff_right one_lt_omega0).2 hxO
      exact ((cdOff_le _).trans (right_le_opow _ one_lt_omega0)).trans_lt (lt_psi_of_mem hκ2 hmem h2)
    · have hpix : cdCodeOf S x = S.psi (ConjT.Aη S x) (Om (1 + 1)) := by
        unfold cdCodeOf
        rw [if_neg hxO]
        rfl
      rw [hpix]
      have hown := Sf.sfOwn hgμ (hAx.trans hAL)
      refine psi_lt_psi_of_mem hκ2 hAx (CSet_mono hAx.le hPx ?_)
      exact hown

section Read

variable {l ηx K : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) (hKB : KzB S K)

include hl hX hKB

/-- **`T` stays in `Cl(E, ψ₂ E)`.** -/
theorem fa_T_C {E x : Ordinal.{0}} (hx : VbDK S l K x) (hxC : x ∈ S.CSet E (S.psi E (Om (1 + 1)))) :
    vbTK S l K x ∈ S.CSet E (S.psi E (Om (1 + 1))) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  refine kzT_cl hl hX hKB (psi_lt hκ2 E).le
    (fun e he heE => (vbTK_le_self hl hX hKB he).trans_lt heE) (fun c hc hc2 hcC => ?_) x hx hxC
  exact CSet.of_lt ((vbTK_le_self hl hX hKB hc).trans_lt (lt_psi_of_mem hκ2 hcC hc2))

/-- `T r < ψ₂ E` for `r < Ω₃` in the closure. -/
theorem fa_T_lt_psi {E x : Ordinal.{0}} (hx : VbDK S l K x) (hxC : x ∈ S.CSet E (S.psi E (Om (1 + 1))))
    (hx3 : x < Om (1 + 1 + 1)) : vbTK S l K x < S.psi E (Om (1 + 1)) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  refine lt_psi_of_mem hκ2 (fa_T_C hl hX hKB hx hxC) ?_
  have h := vbTK_lt_lev hl hX hKB hx 1 (by simpa using hx3)
  simpa using h

/-- `T x < x` for `Ω₂ ≤ x < Ω_ω`. -/
theorem fa_T_lt_self {x : Ordinal.{0}} (hx : VbDK S l K x) (h2 : Om (1 + 1) ≤ x) (hW : x < Om ω) : vbTK S l K x < x := by
  obtain ⟨k, hk⟩ := Pp.ppLt_Om_omega hW
  have key : ∀ k : ℕ, x < Om ((k : Ordinal.{0}) + 1 + 1) → vbTK S l K x < x := by
    intro k
    induction k with
    | zero =>
      intro h
      simp only [Nat.cast_zero, zero_add] at h
      exact absurd h (not_lt.2 h2)
    | succ k ih =>
      intro h
      by_cases hk' : x < Om ((k : Ordinal.{0}) + 1 + 1)
      · exact ih hk'
      · have h1 := vbTK_lt_lev hl hX hKB hx (k + 1) h
        rw [Nat.cast_succ] at h1
        exact h1.trans_le (not_lt.1 hk')
  refine key k (hk.trans_le ?_)
  rw [Nat.cast_succ]
  exact Om_le_Om.2 le_self_add

end Read

section Read2

variable {l ηx K : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) (hKB : KzB S K)
  (hown : ConjT.Aη S (cdEta S l) ∈ S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)))
  (hρ : S.psi (ConjT.Aη S (cdEta S l)) (Om 1) = upsilon l) (hWK : Om ω < K)
  (hAK : ConjT.Aη S (cdEta S l) < K)

include hl hX hKB

/-- **`G(E) < A + ψ₂ E`** for a closed atom other than `θ`, `E < Ω_ω·2`. -/
theorem fa_G_lt {E : Ordinal.{0}} (hWK : Om ω < K) (hED : VbDK S l K E) (hEn : E ∈ S.CSet E (S.psi E (Om (1 + 1))))
    (hWE : Om ω ≤ E) (hEP : E < Om ω + Om ω) (hne : E ≠ Om ω) :
    faG S l K E < ConjT.Aη S (cdEta S l) + S.psi E (Om (1 + 1)) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have h30 : Om (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := Kx.kx3SC.1.ne'
  have h23 : (Om (1 + 1) : Ordinal.{0}) < Om (1 + 1 + 1) := Om_lt_Om.2 (lt_add_one _)
  set w := S.psi E (Om (1 + 1)) with hw
  have hwS : SC w := Ui.ui_psi_SC (s := 1) E
  obtain ⟨haD, hrD⟩ := fa_parts3 (S := S) (l := l) hKB hED
  have hPC := faPC_C (S := S) E w
  have h3C : Om (1 + 1 + 1 : Ordinal.{0}) ∈ S.CSet E w :=
    CSet.Om_mem (CSet.add_mem (CSet.add_mem (CSet.one_mem _ _) (CSet.one_mem _ _)) (CSet.one_mem _ _))
  have haC : Om (1 + 1 + 1) * (E / Om (1 + 1 + 1)) ∈ S.CSet E w := by
    have h1 := hPC.div E hEn _ (show Om (1 + 1 + 1) ∈ S.CSet E w from h3C)
    rw [fa_3e] at h1
    have h2 := hPC.opow_mul h3C _ h1
    rwa [fa_3e] at h2
  have hrC : E % Om (1 + 1 + 1) ∈ S.CSet E w := by
    have h1 := hPC.mod E hEn (Om (1 + 1 + 1))
    rwa [fa_3e] at h1
  have hr3 : E % Om (1 + 1 + 1) < Om (1 + 1 + 1) := Ordinal.mod_lt _ h30
  have hTr : vbTK S l K (E % Om (1 + 1 + 1)) < w := fa_T_lt_psi hl hX hKB hrD hrC hr3
  have hdec : Om (1 + 1 + 1) * (E / Om (1 + 1 + 1)) + E % Om (1 + 1 + 1) = E := Ordinal.div_add_mod _ _
  have hTa : vbTK S l K (Om (1 + 1 + 1) * (E / Om (1 + 1 + 1))) < E := by
    rcases eq_or_ne (E % Om (1 + 1 + 1)) 0 with hr0 | hr0
    · have haE : Om (1 + 1 + 1) * (E / Om (1 + 1 + 1)) = E := by
        have := hdec
        rwa [hr0, add_zero] at this
      rw [haE]
      have hdW3 : Om (1 + 1 + 1) ∣ (Om ω : Ordinal.{0}) := by
        have h := opow_dvd_opow ω (Om_lt_Om.2 Vp.vp_three_lt_omega).le
        rwa [Kx.kx3e, Gg.gg_SC_eps (SC_Om omega0_ne_zero)] at h
      have hPD := faPC_D (S := S) (l := l) hKB
      have hWD : VbDK S l K (Om ω) := ⟨ConjT.OmW_mem S _ _, ConjT.OmW_mem S _ _, hWK⟩
      have hsub : VbDK S l K (E - Om ω) := hPD.sub hED hWD hWE
      have hEe : Om ω + (E - Om ω) = E := Ordinal.add_sub_cancel_of_le hWE
      have hdE : Om (1 + 1 + 1) ∣ E := by
        rw [← haE]; exact dvd_mul_right _ _
      have hd1 : Om (1 + 1 + 1) ∣ E - Om ω := by
        rw [← hEe] at hdE
        exact (Ordinal.dvd_add_iff hdW3).1 hdE
      have hne0 : E - Om ω ≠ 0 := by
        intro h0
        rw [h0, add_zero] at hEe
        exact hne hEe.symm
      have h3le : Om (1 + 1 + 1) ≤ E - Om ω := Ordinal.le_of_dvd hne0 hd1
      have hltW : E - Om ω < Om ω := by
        have : Om ω + (E - Om ω) < Om ω + Om ω := by rw [hEe]; exact hEP
        exact (add_lt_add_iff_left _).1 this
      have hlt := fa_T_lt_self hl hX hKB hsub (h23.le.trans h3le) hltW
      have e1 : vbTK S l K E = Om ω + vbTK S l K (E - Om ω) := by
        conv_lhs => rw [← hEe]
        rw [kzT_add hl hX hKB hWD hsub, vbTK_OmW hl hX hKB hWK]
      rw [e1]
      conv_rhs => rw [← hEe]
      exact (add_lt_add_iff_left _).2 hlt
    · have haE : Om (1 + 1 + 1) * (E / Om (1 + 1 + 1)) < E := by
        conv_rhs => rw [← hdec]
        exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hr0)
      exact (vbTK_le_self hl hX hKB haD).trans_lt haE
  have hψ : S.psi (vbTK S l K (Om (1 + 1 + 1) * (E / Om (1 + 1 + 1)))) (Om (1 + 1)) < w :=
    psi_lt_psi_of_mem hκ2 hTa (fa_T_C hl hX hKB haD haC)
  unfold faG
  rw [add_assoc, add_assoc]
  refine (add_lt_add_iff_left _).2 ?_
  have h1w : (1 : Ordinal.{0}) < w := by
    have h := Ui.ui_L_lt_psi (S := S) (s := 1) E
    exact one_lt_omega0.trans_le (Vp.vp_omega_le_Om1.trans h.le)
  have h2 : (1 : Ordinal.{0}) + (S.psi (vbTK S l K (Om (1 + 1 + 1) * (E / Om (1 + 1 + 1)))) (Om (1 + 1)) + vbTK S l K (E % Om (1 + 1 + 1))) < w := by
    have h3 : S.psi (vbTK S l K (Om (1 + 1 + 1) * (E / Om (1 + 1 + 1)))) (Om (1 + 1)) + vbTK S l K (E % Om (1 + 1 + 1)) < w :=
      hwS.isPrincipal hψ hTr
    exact hwS.isPrincipal h1w h3
  exact h2

omit hl hX hKB in
theorem fa_Om1_lt_th' : Om (1 : Ordinal.{0}) < ConjT.th S := Ui.ui_L_lt_psi (s := 1) (Om ω)

include hown hρ hWK hAK

/-- **The reading of `θ` is below the next high name.** -/
theorem fa_read_th (hWA : Om ω < ConjT.Aη S (cdEta S l)) {m' : Ordinal.{0}} (hm' : m' ≠ 0) :
    gxTh (upsilon l) (ldAtR S l) (ConjT.th S) < Pv S (cdEta S l + ω ^ m') := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have h3W : Om (1 + 1 + 1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 Vp.vp_three_lt_omega
  have hWD : VbDK S l K (Om ω) := ⟨ConjT.OmW_mem S _ _, ConjT.OmW_mem S _ _, hWK⟩
  have hWn : (Om ω : Ordinal.{0}) ∈ S.CSet (Om ω) (S.psi (Om ω) (Om (1 + 1))) := ConjT.OmW_mem S _ _
  obtain ⟨hG, hGn, -⟩ := faG_law hl hX hKB hown hρ hWD hWn hWA h3W.le
  have hdW3 : Om (1 + 1 + 1) ∣ (Om ω : Ordinal.{0}) := by
    have h := opow_dvd_opow ω h3W.le
    rwa [Kx.kx3e, Gg.gg_SC_eps (SC_Om omega0_ne_zero)] at h
  have hGe : faG S l K (Om ω) = ConjT.Aη S (cdEta S l) + ConjT.th S := by
    unfold faG
    have h0 : (Om ω : Ordinal.{0}) % Om (1 + 1 + 1) = 0 := (Ordinal.dvd_iff_mod_eq_zero).1 hdW3
    have hdec : Om (1 + 1 + 1) * ((Om ω : Ordinal.{0}) / Om (1 + 1 + 1)) = Om ω := by
      have := Ordinal.div_add_mod (Om ω : Ordinal.{0}) (Om (1 + 1 + 1))
      rwa [h0, add_zero] at this
    rw [h0, hdec, vbTK_OmW hl hX hKB hWK, vbTK_zero hl hX hKB, add_zero, add_assoc]
    congr 1
    exact one_add_of_omega0_le (Vp.vp_omega_le_Om1.trans fa_Om1_lt_th'.le)
  have hlt : faG S l K (Om ω) < ConjT.Aη S (cdEta S l + ω ^ m') := by
    rw [hGe, A_add]
    refine (add_lt_add_iff_left _).2 ?_
    have hθ0 : 0 < ConjT.th S := (Ui.ui_psi_SC (s := 1) (Om ω)).1
    have h1 : (1 : Ordinal.{0}) < ω ^ m' := by
      have := Ordinal.left_le_opow (ω : Ordinal.{0}) (pos_iff_ne_zero.2 hm')
      exact one_lt_omega0.trans_le this
    have := (mul_lt_mul_iff_right₀ hθ0).2 h1
    rwa [mul_one] at this
  show gxTh (upsilon l) (ldAtR S l) (S.psi (Om ω) (Om (1 + 1))) < S.psi (ConjT.Aη S (cdEta S l + ω ^ m')) (Om 1)
  rw [hG]
  exact psi_lt_psi_of_mem hκ1 hlt ((psi_mono hκ1 hlt.le).2 hGn)

/-- **`Θ_λ(c) < P(η + ω^{faM c})`** for a code `c ∈ [1, P')`. -/
theorem fa_read_lt (hWA : Om ω < ConjT.Aη S (cdEta S l)) {c : Ordinal.{0}} (hc : GxCl (upsilon l) (ldAtR S l) c)
    (hc2 : c < Om (1 + 1)) (hc0 : c ≠ 0) (hcP : c < Nc.ncPp S) :
    gxTh (upsilon l) (ldAtR S l) c < Pv S (cdEta S l + ω ^ faM c) := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have h3W : Om (1 + 1 + 1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 Vp.vp_three_lt_omega
  have hm0 : faM c ≠ 0 := (lt_of_lt_of_le (pos_iff_ne_zero.2 hc0) (le_faM c)).ne'
  have hθ2 : ConjT.th S < Om (1 + 1) := psi_lt hκ2 _
  have hU : UpsPt (Pv S (cdEta S l + ω ^ faM c)) := by
    have e : Pv S (cdEta S l + ω ^ faM c) = upsilon (iota S (cdEta S l + ω ^ faM c)) := (ups_iota S _).symm
    rw [e]
    exact upsPt_upsilon (lt_of_lt_of_le zero_lt_one (one_le_iota _))
  rcases lt_or_ge c (ConjT.th S) with hcθ | hθc
  ·     exact (gxTh_lt hc hcθ).trans (fa_read_th hl hX hKB hown hρ hWK hAK hWA hm0)
  have hcD := fa_hull_D hl hX hKB hown hρ hWK hAK hc hc2
  obtain ⟨w, hwD, hwL, hwc, hmax⟩ := faZB hl hX hKB hown hρ hWK c hc2 hcD hθc
  have hw2 : w < Om (1 + 1) := hwc.trans_lt hc2
  have hwH : GxCl (upsilon l) (ldAtR S l) w := (ldHull_iff hl hX hw2).1 hwD.1
  refine fa_seg hl hX hKB hown hρ hWK hAK hwL hwc hmax hc hc2 hwH _ ?_ hU
  obtain ⟨E, hEn, hWE, -, rfl⟩ := hwL
  obtain ⟨hED, hEA⟩ := fa_arg hl hX (r := 1) le_rfl hwD hEn
  by_cases hE : E = Om ω
  · subst hE
    exact fa_read_th hl hX hKB hown hρ hWK hAK hWA hm0
  have hEP : E < Om ω + Om ω := by
    by_contra hcc
    have h := (psi_mono (S := S) hκ2 (not_lt.1 hcc)).1
    exact absurd (h.trans hwc) (not_le.2 hcP)
  obtain ⟨hG, hGn, -⟩ := faG_law hl hX hKB hown hρ hED hEn hEA (h3W.le.trans hWE)
  have hlt : faG S l K E < ConjT.Aη S (cdEta S l + ω ^ faM c) := by
    refine (fa_G_lt hl hX hKB hWK hED hEn hWE hEP hE).trans_le ?_
    rw [A_add]
    refine (add_le_add_iff_left _).2 ?_
    have hθ0 : ConjT.th S ≠ 0 := (Ui.ui_psi_SC (s := 1) (Om ω)).1.ne'
    refine le_trans ?_ (Ordinal.le_mul_right _ (pos_iff_ne_zero.2 hθ0))
    exact hwc.trans ((le_faM c).trans (right_le_opow _ one_lt_omega0))
  show gxTh (upsilon l) (ldAtR S l) (S.psi E (Om (1 + 1))) < S.psi (ConjT.Aη S (cdEta S l + ω ^ faM c)) (Om 1)
  rw [hG]
  exact psi_lt_psi_of_mem hκ1 hlt ((psi_mono hκ1 hlt.le).2 hGn)

end Read2

end Googology.Trans.PoR.InaccPsi.R2.Fa
