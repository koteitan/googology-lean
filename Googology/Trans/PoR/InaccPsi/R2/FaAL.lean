import Googology.Trans.PoR.InaccPsi.R2.FaAtom
import Googology.Trans.PoR.InaccPsi.R2.KzBand
import Googology.Trans.PoR.InaccPsi.R2.ZsCap

/-!
# Fa: THE READING MOVES THE ATOMS ABOVE `θ`

`T = Kz.vbTK S λ K` on `D_K`, `θ = ConjT.th S = ψ₂(Ω_ω)`, `θ₂ = ψ₃(Ω_ω)`, `A = A_{η_λ}`, `Hˡ¹ = Ul.ulH S 1`, `Φ_μ = Ul.ulH S 0 μ`.

* `fa0_*` (the lemmas at `s = 0` with `Ω₁`, `Ω₂` written literally);
* `faK0_iff` (**`x ∈ K⁽¹⁾_q ⇔ T x ∈ K⁽⁰⁾_{T q}`**);
* `faG` (**the argument of a reading**: `faG B = A + 1 + ψ₂(T(Ω₃·(B/Ω₃))) + T(B % Ω₃)`), `faG_law` (**`T(ψ₂ B) = Θ(ψ₂ B) = ψ₁(faG B)`,
  `faG B` own**, for own `B ∈ D_K`, `Ω_ω ≤ B < A`), `faG_add` (**`faG(B + Ω₂^γ·D) = faG B + Ω₁^{T γ}·T D`**), `faG_dvd`
  (**`Ω₂^{γ+1} ∣ B` gives `Ω₁^{T γ + 1} ∣ faG B`** for `T γ < θ`);
* `faAL` (**`T(Hˡ¹_γ(y)) = Φ_{T γ}(T y)`** for `θ < Hˡ¹_γ(y) < Ω₂` in `D_K`, `γ < θ₂`, `y < Hˡ¹_γ(y)`: and `γ, y ∈ D_K`, `T γ < θ`).

No new axiom.  New definition: `faG`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Fa

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Kz Googology.Trans.PoR.InaccPsi.R2.Ul

variable {S : InaccSeq.{0}}

/-! ## The lemmas at `s = 0` -/

theorem fa0_SC (e : Ordinal.{0}) : SC (S.psi e (Om 1)) := SC_psi Low.InR_Om_one e

theorem fa0_lt (e : Ordinal.{0}) : S.psi e (Om 1) < Om 1 := psi_lt Low.InR_Om_one e

theorem fa0_fix_iff {B γ : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1))) (hB0 : B ≠ 0)
    (hγV : γ < Om (1 + 1)) :
    ulH S 0 γ (S.psi B (Om 1)) = S.psi B (Om 1) ↔
      Om 1 ^ (γ + 1) ∣ B ∧ γ < S.psi B (Om (1 + 1)) ∧ UlK S 0 (S.psi B (Om 1)) γ := by
  have h := Us.us_fix_iff (S := S) (s := 0) omega0_pos (B := B) (γ := γ)
  simp only [zero_add] at h
  exact h hown hB0 hγV

theorem fa0_dvd_val {B γ c : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1)))
    (hc : ulH S 0 γ c = S.psi B (Om 1)) : Om 1 ^ γ ∣ B := by
  have h := Us.us_dvd_val (S := S) (s := 0) omega0_pos (B := B) (γ := γ) (c := c)
  simp only [zero_add] at h
  exact h hown hc

theorem fa0_valid {γ B c D : Ordinal.{0}} (hB : Om 1 ^ γ ∣ B) (hc : ulH S 0 γ c = S.psi B (Om 1))
    (hv : D < S.psi (B + Om 1 ^ γ * D) (Om 1)) : ∀ d, d ≤ D → d < ulH S 0 γ (c + d) := by
  have h := Vp.vp_valid (S := S) (s := 0) omega0_pos (γ := γ) (B := B) (c := c) (D := D)
  simp only [zero_add] at h
  exact h hB hc hv

theorem fa0_run {γ B c D : Ordinal.{0}} (hγV : γ < Om (1 + 1)) (hown : B ∈ S.CSet B (S.psi B (Om 1)))
    (hc : ulH S 0 γ c = S.psi B (Om 1)) (hD : D < Om 1) (hcond : ∀ d, d ≤ D → d < ulH S 0 γ (c + d)) :
    S.psi (B + Om 1 ^ γ * D) (Om 1) = ulH S 0 γ (c + D) := by
  have h := Us.us_run (S := S) (s := 0) omega0_pos (γ := γ) (B := B) (c := c) (D := D)
  simp only [zero_add] at h
  exact h hγV hown hc hD hcond

theorem fa0_val_of {B γ : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1))) (hB0 : B ≠ 0)
    (hγ0 : γ ≠ 0) (hγV : γ < Om (1 + 1)) (hdvd : Om 1 ^ γ ∣ B)
    (hle : γ ≤ S.psi B (Om (1 + 1))) (hK : UlK S 0 (S.psi B (Om 1)) γ) :
    S.psi B (Om 1) ∈ range (ulH S 0 γ) := by
  have h := Vp.vp_val_of (S := S) (s := 0) omega0_pos (B := B) (γ := γ)
  simp only [zero_add] at h
  exact h hown hB0 hγ0 hγV hdvd hle hK

theorem fa0_first_of {γ B0 K : Ordinal.{0}} (hγ0 : γ ≠ 0)
    (hown : B0 ∈ S.CSet B0 (S.psi B0 (Om 1))) (hval : S.psi B0 (Om 1) ∈ range (ulH S 0 γ))
    (hB0K : B0 = K + Om 1 ^ γ) (hownK : K ∈ S.CSet K (S.psi K (Om 1)))
    (hK : ¬ UlK S 0 (S.psi K (Om 1)) γ) : ulH S 0 γ 0 = S.psi B0 (Om 1) := by
  have h := fa_first_of (S := S) (s := 0) omega0_pos (γ := γ) (B0 := B0) (K := K) hγ0
  simp only [zero_add] at h
  exact h hown hval hB0K hownK (Or.inr (Or.inl hK))

/-- `Ω₁^x ∣ y` for a strongly critical `y > Ω₁`, `x ≤ y`. -/
theorem fa_dvd_SC {x y : Ordinal.{0}} (hy : SC y) (h1 : Om 1 < y) (hx : x ≤ y) : Om 1 ^ x ∣ y := by
  have hO : ω ^ (Om 1 : Ordinal.{0}) = Om 1 := Bt.Om1_opow
  have hyE : ω ^ y = y := gg_SC_eps hy
  have e : Om 1 ^ x = ω ^ (Om 1 * x) := by
    conv_lhs => rw [← hO]
    rw [← opow_mul]
  have hmul : IsPrincipal (· * ·) y := by
    have h := isPrincipal_mul_omega0_opow_opow y
    rwa [hyE, hyE] at h
  have hle : Om 1 * x ≤ y := by
    rcases hx.lt_or_eq with h | rfl
    · exact (hmul h1 h).le
    · exact (isPrincipal_mul_iff_mul_left_eq.1 hmul _ (Om_pos one_ne_zero) h1).le
  conv_rhs => rw [← hyE]
  rw [e]
  exact opow_dvd_opow _ hle

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {K : Ordinal.{0}} (hKB : KzB S K)

include hl hX hKB

/-- `T q` is strongly critical in `(0, Ω₁]` for `q ∈ (Ω₁, Ω₂]`. -/
theorem faK0_q {q : Ordinal.{0}} (hqD : VbDK S l K q) (hqS : SC q) (h1 : Om 1 < q) (h2 : q ≤ Om (1 + 1)) :
    SC (vbTK S l K q) ∧ vbTK S l K q ≤ Om 1 := by
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  have e2 : vbTK S l K (Om (1 + 1)) = Om 1 := by
    have h := vbTK_Om (S := S) hl hX hKB (k := 1) le_rfl
    simpa using h
  have h2D : VbDK S l K (Om (1 + 1 : Ordinal.{0})) := by
    have := fa_Om1_D (S := S) (l := l) hKB 1; simpa using this
  refine ⟨?_, ?_⟩
  · rcases h2.lt_or_eq with h | rfl
    · rw [vbTK_code hl hX hKB h hqD.1]
      exact gxTh_SC hZ (ldAt_GxAt _ _) hqS (hZ1.trans h1)
    · rw [e2]; exact SC_Om one_ne_zero
  · have h := (vbTK_le_iff hl hX hKB hqD h2D).1 h2
    rwa [e2] at h

/-- **`x ∈ K⁽¹⁾_q ⇔ T x ∈ K⁽⁰⁾_{T q}`.** -/
theorem faK0_iff {q : Ordinal.{0}} (hqD : VbDK S l K q) (hqS : SC q) (h1 : Om 1 < q) (h2 : q ≤ Om (1 + 1)) :
    ∀ x, VbDK S l K x → (UlK S 1 q x ↔ UlK S 0 (vbTK S l K q) (vbTK S l K x)) := by
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  obtain ⟨hTS, hT2⟩ := faK0_q hl hX hKB hqD hqS h1 h2
  have hqL : q ≤ S.Lam := (hqD.2.2.trans (kzK_lt_Lam hKB)).le
  have hTL : vbTK S l K q ≤ S.Lam := ((vbTK_mem hl hX hKB hqD).2.trans (kzK_lt_Lam hKB)).le
  refine rxMs_ind (S := S) (T := upsilon l) fun x IH hx => ?_
  have hxE : RxEK S (upsilon l) K x := vbDK_E hl hX hx
  by_cases hxq : x < q
  · exact ⟨fun _ => UlK.small (vbTK_mono hl hX hKB hx hqD hxq), fun _ => UlK.small hxq⟩
  have hqx : q ≤ x := not_lt.1 hxq
  have hTqx : vbTK S l K q ≤ vbTK S l K x := (vbTK_le_iff hl hX hKB hqD hx).1 hqx
  have h0' : (Om (0 : Ordinal.{0})) < vbTK S l K q := by rw [Om_zero]; exact hTS.1
  by_cases hx2' : x < Om (1 + 1)
  · constructor
    · intro hK
      exact absurd (ulK_lt_W one_lt_omega0 hqS h1 hK hx2') hxq
    · intro hK
      have hTx : vbTK S l K x < Om (0 + 1) := by
        have h := vbTK_lt_lev hl hX hKB hx 0 (by simpa using hx2')
        simpa using h
      exact absurd hTqx (not_le.2 (ulK_lt_W omega0_pos hTS h0' hK hTx))
  have hx2le : Om (1 + 1) ≤ x := not_lt.1 hx2'
  have hx1 : Om 1 < x := (Om_lt_Om.2 (lt_add_one 1)).trans_le hx2le
  have h0 : x ≠ 0 := ((Om_pos one_ne_zero).trans hx1).ne'
  by_cases hΩ : ∃ j : ℕ, x = Om (j : Ordinal.{0})
  · obtain ⟨j, rfl⟩ := hΩ
    have hj : 2 ≤ j := by
      have h := Om_le_Om.1 hx2le
      rw [one_add_one_eq_two] at h
      have h' : ((2 : ℕ) : Ordinal.{0}) ≤ j := by rw [Nat.cast_ofNat]; exact h
      exact_mod_cast h'
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have e := vbTK_Om (S := S) hl hX hKB (k := i) (by omega)
    rw [Nat.cast_succ, e]
    have hn' := (UlK.nat (S := S) (s := 1) (q := q) (i + 1))
    rw [Nat.cast_succ] at hn'
    exact ⟨fun _ => UlK.om (UlK.nat i), fun _ => UlK.om hn'⟩
  by_cases hxW : x = Om ω
  · subst hxW
    rw [vbTK_OmW hl hX hKB hx.2.2]
    have hω : ∀ s q', UlK S s q' (ω : Ordinal.{0}) := fun s q' => by
      have := UlK.opow (UlK.one (S := S) (s := s) (q := q')); rwa [opow_one] at this
    exact ⟨fun _ => UlK.om (hω _ _), fun _ => UlK.om (hω _ _)⟩
  have hx2 : Om (1 + 1) < x := lt_of_le_of_ne hx2le (fun e => hΩ ⟨2, by rw [← e]; norm_num⟩)
  by_cases hSx : SC x
  · obtain ⟨j, hj, d, hdE, hdn, rfl, hst⟩ := kzE_atom hKB hZ1.le hxE hSx hx1 (kzNe hKB hxE hΩ hxW)
    have hj2 : 2 ≤ j := by
      by_contra hc
      have hj1 : j = 1 := by omega
      subst hj1
      have := (psiS_bounds (S := S) d ((1 : ℕ) : Ordinal.{0})).2
      rw [Nat.cast_one] at this hx2
      exact absurd (hx2.trans this) (lt_irrefl _)
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hj' : 1 ≤ j' := by omega
    have hdD : VbDK S l K d := vbDK_atom hl hX hx hdE hdn hj
    have hms := rxMs_lt_stage (kzE_lt_Lam hKB hdE) hst
    rw [Nat.cast_succ] at hdn hx hqx hxq hTqx hx2 hx1 h0 hxE hms ⊢
    obtain ⟨hTat, hTown⟩ := vbTK_atom hl hX hKB hj' hdD hdn
    rw [hTat] at hTqx ⊢
    have hπ : S.InR (Om ((j' : Ordinal.{0}) + 1 + 1)) := InR_Om_succ _
    have hπ' : S.InR (Om ((j' : Ordinal.{0}) + 1)) := InR_Om_succ _
    have hj1 : (1 : Ordinal.{0}) ≤ j' := by exact_mod_cast hj'
    have hne1 : Om ((j' : Ordinal.{0}) + 1 + 1) ≠ Om (1 + 1) := by
      intro e
      have e1 : (j' : Ordinal.{0}) + 1 + 1 = 1 + 1 := le_antisymm (Om_le_Om.1 e.le) (Om_le_Om.1 e.ge)
      have e3 : ((j' + 1 + 1 : ℕ) : Ordinal.{0}) = ((1 + 1 : ℕ) : Ordinal.{0}) := by
        rw [Nat.cast_succ, Nat.cast_succ, Nat.cast_succ, Nat.cast_one]; exact e1
      have e4 := Nat.cast_inj.1 e3
      omega
    have hne2 : Om ((j' : Ordinal.{0}) + 1) ≠ Om (0 + 1) := by
      intro e
      have e1 : (j' : Ordinal.{0}) + 1 = 0 + 1 := le_antisymm (Om_le_Om.1 e.le) (Om_le_Om.1 e.ge)
      have e3 : ((j' + 1 : ℕ) : Ordinal.{0}) = ((0 + 1 : ℕ) : Ordinal.{0}) := by
        rw [Nat.cast_succ, Nat.cast_succ, Nat.cast_zero]; exact e1
      have e4 := Nat.cast_inj.1 e3
      omega
    have hiff := IH d hms hdD
    have hOm1 : ∀ s q' (i : ℕ), UlK S s q' (Om ((i : Ordinal.{0}) + 1)) := fun s q' i => by
      have := UlK.nat (S := S) (s := s) (q := q') (i + 1)
      rw [Nat.cast_succ] at this
      exact UlK.om this
    have hOm2 : ∀ s q' (i : ℕ), UlK S s q' (Om ((i : Ordinal.{0}) + 1 + 1)) := fun s q' i => by
      have := hOm1 s q' (i + 1)
      rwa [Nat.cast_succ] at this
    constructor
    · intro hK
      have hdK := Uo.uoArg hqL hπ hdn hK hqx
      exact UlK.coll hπ' hne2 (hOm1 _ _ _) (hiff.1 hdK)
    · intro hK
      have hdK := Uo.uoArg hTL hπ' hTown hK hTqx
      exact UlK.coll hπ hne1 (hOm2 _ _ _) (hiff.2 hdK)
  by_cases hε : ω ^ x = x
  · obtain ⟨hv, ha0, ha, hb⟩ := rxVeb hx1 hε hSx
    obtain ⟨haD, hbD, -, -, hha, hhb⟩ := vbDK_veb hx hxE hv hb
    have hIa := IH _ (rxMs_lt_val hha ha) haD
    have hIb := IH _ (rxMs_lt_val hhb hb) hbD
    have hT := vbTK_veb hl hX hKB hx hv ha0.ne' hb hx2.le
    have hTa : vbTK S l K (invVeblen₁ x) < vbTK S l K x := vbTK_mono hl hX hKB haD hx ha
    have hTb : vbTK S l K (invVeblen₂ x) < vbTK S l K x := vbTK_mono hl hX hKB hbD hx hb
    constructor
    · intro hK
      have hK' : UlK S 1 q (veblen (invVeblen₁ x) (invVeblen₂ x)) := by rw [hv]; exact hK
      obtain ⟨h3, h4⟩ := Qt.ulK_veb_parts hK' (by rw [hv]; exact ha) (by rw [hv]; exact hb)
      rw [hT]
      exact UlK.phi (hIa.1 h3) (hIb.1 h4)
    · intro hK
      rw [hT] at hK hTa hTb
      obtain ⟨h3, h4⟩ := Qt.ulK_veb_parts hK hTa hTb
      rw [← hv]
      exact UlK.phi (hIa.2 h3) (hIb.2 h4)
  -- the Cantor normal form
  have hlx : log ω x < x := ruLog_lt hx1 hε
  obtain ⟨hlD, -, hlh⟩ := vbDK_log hx hxE
  obtain ⟨hrD, -, hrh⟩ := vbDK_rem hx hxE
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
  have hpos : (0 : Ordinal.{0}) < ω ^ log ω x := opow_pos _ omega0_pos
  have hdm : x = ω ^ log ω x * n + x % ω ^ log ω x := by
    rw [← hn]; exact (Ordinal.div_add_mod x _).symm
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      have hlt : x < ω ^ log ω x * 1 :=
        (Ordinal.lt_mul_iff_div_lt hpos.ne').2 (by rw [hn, h]; exact zero_lt_one)
      rw [mul_one] at hlt
      exact absurd (opow_log_le_self ω h0) (not_le.2 hlt)
    · exact h
  have hn0 : (n : Ordinal.{0}) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hIl := IH _ (rxMs_lt_val hlh hlx) hlD
  have hIr := IH _ (rxMs_lt_val hrh (mod_opow_log_lt_self ω h0)) hrD
  have hrlt : x % ω ^ log ω x < ω ^ log ω x := Ordinal.mod_lt x hpos.ne'
  have hT := kzT_cnf hl hX hKB n hn1 hlD hrD hrlt
  rw [← hdm] at hT
  have hPC := faPC_D (S := S) (l := l) hKB
  have hoD : VbDK S l K (ω ^ log ω x) := hPC.opow hlD
  have hTo : vbTK S l K (ω ^ log ω x) = ω ^ vbTK S l K (log ω x) := by
    have h := kzT_cnf hl hX hKB 1 le_rfl hlD hPC.zero hpos
    rwa [Nat.cast_one, mul_one, add_zero, vbTK_zero hl hX hKB, mul_one, add_zero] at h
  have hTr : vbTK S l K (x % ω ^ log ω x) < ω ^ vbTK S l K (log ω x) := by
    rw [← hTo]; exact vbTK_mono hl hX hKB hrD hoD hrlt
  have hlogT : log ω (vbTK S l K x) = vbTK S l K (log ω x) := by
    rw [hT, log_opow_mul_add one_lt_omega0 hn0 hTr, log_eq_zero (natCast_lt_omega0 n), add_zero]
  have hmodT : vbTK S l K x % ω ^ vbTK S l K (log ω x) = vbTK S l K (x % ω ^ log ω x) := by
    rw [hT, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hTr]
  constructor
  · intro hK
    obtain ⟨-, -, h3, h4, -⟩ := ulK_split hqS hK h0
    rw [hT]
    exact UlK.add ((UlK.opow (hIl.1 h3)).mul_nat n) (hIr.1 h4)
  · intro hK
    have hT0 : vbTK S l K x ≠ 0 := by
      rw [hT]
      refine (lt_of_lt_of_le (mul_pos (opow_pos _ omega0_pos) (pos_iff_ne_zero.2 hn0)) le_self_add).ne'
    obtain ⟨-, -, h3, h4, -⟩ := ulK_split hTS hK hT0
    rw [hlogT] at h3 h4
    rw [hmodT] at h4
    rw [hdm]
    exact UlK.add ((UlK.opow (hIl.2 h3)).mul_nat n) (hIr.2 h4)

omit hl hX hKB in
theorem fa_3e : ω ^ Om (1 + 1 + 1 : Ordinal.{0}) = Om (1 + 1 + 1) := Kx.kx3e

omit hl hX in
theorem fa_O3_D : VbDK S l K (Om (1 + 1 + 1 : Ordinal.{0})) := by
  have := fa_Om2_D (S := S) (l := l) hKB 1; simpa using this

omit hl hX in
/-- The two parts of `B` in base `Ω₃` are in `D_K`. -/
theorem fa_parts3 {B : Ordinal.{0}} (hB : VbDK S l K B) :
    VbDK S l K (Om (1 + 1 + 1) * (B / Om (1 + 1 + 1))) ∧ VbDK S l K (B % Om (1 + 1 + 1)) := by
  have hPC := faPC_D (S := S) (l := l) hKB
  have h3 := fa_O3_D (S := S) (l := l) hKB
  constructor
  · have h1 := hPC.div B hB _ h3
    rw [fa_3e] at h1
    have h2 := hPC.opow_mul h3 _ h1
    rwa [fa_3e] at h2
  · have h1 := hPC.mod B hB (Om (1 + 1 + 1))
    rwa [fa_3e] at h1

end Rst

/-- **The argument of a reading** at an own `B`. -/
noncomputable def faG (S : InaccSeq.{0}) (l K B : Ordinal.{0}) : Ordinal.{0} :=
  ConjT.Aη S (cdEta S l) + 1 + S.psi (vbTK S l K (Om (1 + 1 + 1) * (B / Om (1 + 1 + 1)))) (Om (1 + 1)) +
    vbTK S l K (B % Om (1 + 1 + 1))

section Law

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {K : Ordinal.{0}} (hKB : KzB S K)
  (hown : ConjT.Aη S (cdEta S l) ∈ S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)))
  (hρ : S.psi (ConjT.Aη S (cdEta S l)) (Om 1) = upsilon l)

include hl hX hKB hown hρ

/-- **`T(ψ₂ B) = Θ(ψ₂ B) = ψ₁(faG B)`, `faG B` own.** -/
theorem faG_law {B : Ordinal.{0}} (hBD : VbDK S l K B) (hBn : B ∈ S.CSet B (S.psi B (Om (1 + 1))))
    (hBA : B < ConjT.Aη S (cdEta S l)) (h3B : Om (1 + 1 + 1) ≤ B) :
    gxTh (upsilon l) (ldAtR S l) (S.psi B (Om (1 + 1))) = S.psi (faG S l K B) (Om 1) ∧
      faG S l K B ∈ S.CSet (faG S l K B) (S.psi (faG S l K B) (Om 1)) ∧
      vbTK S l K (S.psi B (Om (1 + 1))) = S.psi (faG S l K B) (Om 1) := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have h30 : Om (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := Kx.kx3SC.1.ne'
  set A := ConjT.Aη S (cdEta S l) with hAdef
  set a := Om (1 + 1 + 1) * (B / Om (1 + 1 + 1)) with hadef
  set δ := B % Om (1 + 1 + 1) with hδdef
  obtain ⟨haD, hδD⟩ := fa_parts3 (S := S) (l := l) hKB hBD
  have hBe : a + δ = B := Ordinal.div_add_mod B _
  have had : a ≤ B := Ordinal.mul_div_le B _
  have hδ3 : δ < Om (1 + 1 + 1) := Ordinal.mod_lt B h30
  have hda : B < a + Om (1 + 1 + 1) := by
    conv_lhs => rw [← hBe]
    exact (add_lt_add_iff_left _).2 hδ3
  have han : a ∈ S.CSet a (S.psi a (Om (1 + 1))) := by
    have hpart : a ∈ S.CSet B (S.psi B (Om (1 + 1))) := by
      have h := (Vh.vhC_div _ hBn (Om (1 + 1 + 1))).1; rwa [Kx.kx3e] at h
    refine Kx.kwFUG (a₁ := a) (b := B) (K := a) (fun {k e} he h1 h2 => ?_) hpart
    have h := (Kw.kwC_div e he (Om (1 + 1 + 1))).1
    rw [Kx.kx3e, Kx.kxDiv h1 (h2.trans hda)] at h
    exact h
  have h1q : 1 ≤ B / Om (1 + 1 + 1) := not_lt.1 fun h => absurd h3B (not_le.2 (by
    have := (Ordinal.lt_mul_iff_div_lt h30).2 h; rwa [mul_one] at this))
  have ha3le : Om (1 + 1 + 1) ≤ a := le_mul_left _ (zero_lt_one.trans_le h1q)
  have haA : a < A := had.trans_lt hBA
  have hd3 : Om (1 + 1 + 1) ∣ a := dvd_mul_right _ _
  have hlaw := kzTop hl hX hKB hown hρ a ⟨haD, han, hd3, ha3le⟩ haA
  have hhat := kzHat hl hX hKB hown haD han haA hlaw
  unfold KuLawK at hlaw
  set L := S.psi (vbTK S l K a) (Om (1 + 1)) with hLdef
  have hhat' : A + 1 + L ∈ S.CSet (A + 1 + L) (S.psi (A + 1 + L) (Om 1)) := by rw [add_assoc]; exact hhat
  have hÂa : a ≤ A + 1 + L := haA.le.trans (le_self_add.trans le_self_add)
  have hBn' : a + δ ∈ S.CSet (a + δ) (S.psi (a + δ) (Om (1 + 1))) := by rw [hBe]; exact hBn
  have hδA : a + δ < A := by rw [hBe]; exact hBA
  have hOff := kzOff hl hX hKB haD hd3 han hhat' hÂa hlaw hδD hδ3 hBn' hδA
  rw [hBe] at hOff
  have hδC : δ ∈ S.CSet B (S.psi B (Om (1 + 1))) := by
    have haC : a ∈ S.CSet B (S.psi B (Om (1 + 1))) := by
      have h := (Vh.vhC_div _ hBn (Om (1 + 1 + 1))).1; rwa [Kx.kx3e] at h
    have h := (rxCDec B hBn).1 a haC had
    rwa [← hBe, Ordinal.add_sub_cancel, hBe] at h
  have hTδC : vbTK S l K δ ∈ S.CSet (A + 1 + L + vbTK S l K δ) (S.psi (A + 1 + L + vbTK S l K δ) (Om 1)) := by
    refine kzT_cl hl hX hKB (psi_lt hκ2 B).le
      (fun e he hea => (vbTK_le_self hl hX hKB he).trans_lt
        ((hea.trans hBA).trans_le (le_self_add.trans (le_self_add.trans le_self_add))))
      (fun c hc hc2 hcC => ?_) δ hδD hδC
    rw [vbTK_code hl hX hKB hc2 hc.1]
    refine CSet.of_lt ?_
    rw [← hOff]
    exact gxTh_lt ((ldHull_iff hl hX hc2).1 hc.1) (lt_psi_of_mem hκ2 hcC hc2)
  have hG : faG S l K B = A + 1 + L + vbTK S l K δ := rfl
  have hown' : faG S l K B ∈ S.CSet (faG S l K B) (S.psi (faG S l K B) (Om 1)) := by
    rw [hG]; exact CSet.add_mem ((psi_mono hκ1 le_self_add).2 hhat') hTδC
  have hzC : S.psi B (Om (1 + 1)) ∈ cdHull S l :=
    (fa_collW (S := S) (l := l) (k := 0) hKB hBD hBA |> fun h => by simpa using h.1)
  refine ⟨hOff, hown', ?_⟩
  rw [vbTK_code hl hX hKB (psi_lt hκ2 B) hzC]
  exact hOff

omit hl hX hKB hown hρ in
/-- The base-`Ω₃` parts of `B + Ω₂^γ·D`. -/
theorem fa_add_parts {B γ D : Ordinal.{0}} (hγ : γ < Om (1 + 1 + 1)) (hD : D < Om (1 + 1)) :
    (B + Om (1 + 1) ^ γ * D) / Om (1 + 1 + 1) = B / Om (1 + 1 + 1) ∧
      (B + Om (1 + 1) ^ γ * D) % Om (1 + 1 + 1) = B % Om (1 + 1 + 1) + Om (1 + 1) ^ γ * D := by
  have h30 : Om (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := Kx.kx3SC.1.ne'
  have h23 : (Om (1 + 1) : Ordinal.{0}) < Om (1 + 1 + 1) := Om_lt_Om.2 (lt_add_one _)
  have hmul : IsPrincipal (· * ·) (Om (1 + 1 + 1) : Ordinal.{0}) := by
    have h := isPrincipal_mul_omega0_opow_opow (Om (1 + 1 + 1) : Ordinal.{0})
    rwa [Kx.kx3e, Kx.kx3e] at h
  have hopow : Om (1 + 1) ^ γ < Om (1 + 1 + 1) := by
    rw [Ui.ui_W_eq 1 γ]
    have h1 : Om (1 + 1) * γ < Om (1 + 1 + 1) := hmul h23 hγ
    have := (isNormal_opow one_lt_omega0).strictMono h1
    rwa [Kx.kx3e] at this
  have hw : Om (1 + 1) ^ γ * D < Om (1 + 1 + 1) := hmul hopow (hD.trans h23)
  have hsum : B % Om (1 + 1 + 1) + Om (1 + 1) ^ γ * D < Om (1 + 1 + 1) :=
    Kx.kx3SC.isPrincipal (Ordinal.mod_lt B h30) hw
  have e : B + Om (1 + 1) ^ γ * D = Om (1 + 1 + 1) * (B / Om (1 + 1 + 1)) + (B % Om (1 + 1 + 1) + Om (1 + 1) ^ γ * D) := by
    rw [← add_assoc, Ordinal.div_add_mod]
  constructor
  · rw [e, Ordinal.mul_add_div _ h30, Ordinal.div_eq_zero_of_lt hsum, add_zero]
  · rw [e, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hsum]

omit hown hρ in
/-- **`faG(B + Ω₂^γ·D) = faG B + Ω₁^{T γ}·T D`.** -/
theorem faG_add {B γ D : Ordinal.{0}} (hBD : VbDK S l K B) (hγD : VbDK S l K γ) (hDD : VbDK S l K D)
    (hγ : γ < Om (1 + 1 + 1)) (hD : D < Om (1 + 1)) :
    faG S l K (B + Om (1 + 1) ^ γ * D) = faG S l K B + Om 1 ^ vbTK S l K γ * vbTK S l K D := by
  obtain ⟨e1, e2⟩ := fa_add_parts (B := B) hγ hD
  have hPC := faPC_D (S := S) (l := l) hKB
  obtain ⟨-, hδD⟩ := fa_parts3 (S := S) (l := l) hKB hBD
  have hW := fa_Om1_D (S := S) (l := l) hKB 1
  have hW' : VbDK S l K (Om (1 + 1 : Ordinal.{0})) := by simpa using hW
  have hWγ : VbDK S l K (Om (1 + 1) * γ) := by
    have := hPC.opow_mul hW' γ hγD; rwa [Ui.ui_W_opow 1] at this
  have hwD : VbDK S l K (Om (1 + 1) ^ γ * D) := by
    rw [Ui.ui_W_eq 1 γ]; exact hPC.opow_mul hWγ _ hDD
  have hTw : vbTK S l K (Om (1 + 1) ^ γ * D) = Om 1 ^ vbTK S l K γ * vbTK S l K D := by
    have h := faT_Wmul hl hX hKB (k := 0) hγD hDD
    simpa using h
  unfold faG
  rw [e1, e2, kzT_add hl hX hKB hδD hwD, hTw]
  exact (add_assoc _ _ _).symm

/-- **`Ω₂^{γ+1} ∣ B` gives `Ω₁^{T γ + 1} ∣ faG B`** for `Ω_ω ≤ B`, `T γ < θ`. -/
theorem faG_dvd {B γ : Ordinal.{0}} (hWK : Om ω < K) (hBD : VbDK S l K B) (hγD : VbDK S l K γ)
    (hγ : γ < Om (1 + 1 + 1)) (hTγ : vbTK S l K γ < ConjT.th S) (hWB : Om ω ≤ B)
    (hdvd : Om (1 + 1) ^ (γ + 1) ∣ B) : Om 1 ^ (vbTK S l K γ + 1) ∣ faG S l K B := by
  have hPC := faPC_D (S := S) (l := l) hKB
  have h30 : Om (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := Kx.kx3SC.1.ne'
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨haD, hδD⟩ := fa_parts3 (S := S) (l := l) hKB hBD
  set x := vbTK S l K γ + 1 with hxdef
  have hxθ : x ≤ ConjT.th S := Order.add_one_le_of_lt hTγ
  have hθS : SC (ConjT.th S) := Ui.ui_psi_SC (s := 1) (Om ω)
  have h1θ : Om 1 < ConjT.th S := Ui.ui_L_lt_psi (s := 1) (Om ω)
  have hOW : SC (Om ω : Ordinal.{0}) := SC_Om omega0_ne_zero
  have hθW : ConjT.th S < Om ω := (psi_lt hκ2 _).trans (Om_lt_Om.2 (Ui.ui_s1_lt_omega one_lt_omega0))
  have h1W : Om 1 < (Om ω : Ordinal.{0}) := h1θ.trans hθW
  have hdA : Om 1 ^ x ∣ ConjT.Aη S (cdEta S l) := by
    show Om 1 ^ x ∣ Om ω + ConjT.th S * cdEta S l
    exact dvd_add (fa_dvd_SC hOW h1W (hxθ.trans hθW.le)) (Dvd.dvd.mul_right (fa_dvd_SC hθS h1θ hxθ) _)
  -- `a ≥ Ω_ω`
  have hdW3 : Om (1 + 1 + 1) ∣ (Om ω : Ordinal.{0}) := by
    have h := opow_dvd_opow ω (Om_le_Om.2 (show (1 + 1 + 1 : Ordinal.{0}) ≤ ω from (Vp.vp_three_lt_omega).le))
    rwa [Kx.kx3e, gg_SC_eps hOW] at h
  have hWa : Om ω ≤ Om (1 + 1 + 1) * (B / Om (1 + 1 + 1)) := Uw.uw_le_trunc h30 hdW3 hWB
  have hWD : VbDK S l K (Om ω) := ⟨ConjT.OmW_mem S _ _, ConjT.OmW_mem S _ _, hWK⟩
  have hTa : Om ω ≤ vbTK S l K (Om (1 + 1 + 1) * (B / Om (1 + 1 + 1))) := by
    have h := (vbTK_le_iff hl hX hKB hWD haD).1 hWa
    rwa [vbTK_OmW hl hX hKB hWK] at h
  set L := S.psi (vbTK S l K (Om (1 + 1 + 1) * (B / Om (1 + 1 + 1)))) (Om (1 + 1)) with hLdef
  have hθL : ConjT.th S ≤ L := (psi_mono hκ2 hTa).1
  have hLS : SC L := Ui.ui_psi_SC (s := 1) _
  have hdL : Om 1 ^ x ∣ L := fa_dvd_SC hLS (h1θ.trans_le hθL) (hxθ.trans hθL)
  have hωL : (ω : Ordinal.{0}) ≤ L := (Vp.vp_omega_le_Om1.trans h1θ.le).trans hθL
  have hδ : Om (1 + 1) ^ (γ + 1) ∣ B % Om (1 + 1 + 1) := by
    have hd3 : Om (1 + 1) ^ (γ + 1) ∣ Om (1 + 1 + 1) * (B / Om (1 + 1 + 1)) := by
      refine Dvd.dvd.mul_right ?_ _
      rw [Ui.ui_W_eq 1 (γ + 1)]
      have hle : Om (1 + 1) * (γ + 1) ≤ Om (1 + 1 + 1) := by
        have hmul : IsPrincipal (· * ·) (Om (1 + 1 + 1) : Ordinal.{0}) := by
          have h := isPrincipal_mul_omega0_opow_opow (Om (1 + 1 + 1) : Ordinal.{0})
          rwa [Kx.kx3e, Kx.kx3e] at h
        have h1 : γ + 1 < Om (1 + 1 + 1) := Kx.kx3SC.isPrincipal hγ (one_lt_omega0.trans_le
          (Vp.vp_omega_le_Om1.trans (Om_le_Om.2 (le_self_add.trans le_self_add))))
        exact (hmul (Om_lt_Om.2 (lt_add_one _)) h1).le
      have h := opow_dvd_opow ω hle
      rwa [Kx.kx3e] at h
    have hd := hdvd
    rw [← Ordinal.div_add_mod B (Om (1 + 1 + 1))] at hd
    exact (Ordinal.dvd_add_iff hd3).1 hd
  have hTδ := (faT_Wdvd hl hX hKB (k := 0) (hPC.add hγD hPC.one) hδD).1
    (by simp only [Nat.cast_zero, zero_add]; exact hδ)
  rw [fa_T_succ hl hX hKB hγD] at hTδ
  have hTδ' : Om 1 ^ x ∣ vbTK S l K (B % Om (1 + 1 + 1)) := by
    simp only [Nat.cast_zero, zero_add] at hTδ; exact hTδ
  have e : faG S l K B = ConjT.Aη S (cdEta S l) + (L + vbTK S l K (B % Om (1 + 1 + 1))) := by
    show ConjT.Aη S (cdEta S l) + 1 + L + vbTK S l K (B % Om (1 + 1 + 1)) = _
    rw [add_assoc (ConjT.Aη S (cdEta S l)) 1 L, one_add_of_omega0_le hωL, add_assoc]
  rw [e]
  exact dvd_add hdA (dvd_add hdL hTδ')

/-- **THE READING MOVES THE ATOMS ABOVE `θ`**, for a run `y = c + D` of `Hˡ¹_γ`: `T(Hˡ¹_γ(y)) = Φ_{T γ}(T c + T D)`. -/
theorem faALc {γ y B c D : Ordinal.{0}} (hWK : Om ω < K) (hγ : γ < S.psi (Om ω) (Om (1 + 1 + 1)))
    (hy : y < ulH S 1 γ y) (hzW : ulH S 1 γ y < Om (1 + 1)) (hzD : VbDK S l K (ulH S 1 γ y))
    (hθz : ConjT.th S < ulH S 1 γ y) (hown' : B ∈ S.CSet B (S.psi B (Om (1 + 1))))
    (hc : ulH S 1 γ c = S.psi B (Om (1 + 1))) (hcD : c + D = y)
    (hcond : ∀ d, d ≤ D → d < ulH S 1 γ (c + d))
    (hcase : c = 0 ∨ (ulH S 1 γ c = c ∧ ∀ q, ulH S 1 γ q = q → q ≤ y → q ≤ c)) :
    VbDK S l K γ ∧ VbDK S l K y ∧ VbDK S l K D ∧ VbDK S l K c ∧ vbTK S l K γ < ConjT.th S ∧
      (∀ d, d ≤ vbTK S l K D → d < ulH S 0 (vbTK S l K γ) (vbTK S l K c + d)) ∧
      ulH S 0 (vbTK S l K γ) (vbTK S l K c) = S.psi (faG S l K B) (Om 1) ∧
      vbTK S l K y = vbTK S l K c + vbTK S l K D ∧
      vbTK S l K (ulH S 1 γ y) = ulH S 0 (vbTK S l K γ) (vbTK S l K y) ∧
      VbDK S l K B ∧ B < ConjT.Aη S (cdEta S l) ∧ Om ω ≤ B := by
  have hPC := faPC_D (S := S) (l := l) hKB
  have hs : (1 : Ordinal.{0}) < ω := one_lt_omega0
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hκ3 : S.InR (Om (1 + 1 + 1 : Ordinal.{0})) := InR_Om_succ (1 + 1)
  have hγV : γ < Om (1 + 1 + 1) := hγ.trans (psi_lt hκ3 _)
  have hW : VbDK S l K (Om (1 + 1 : Ordinal.{0})) := by
    have := fa_Om1_D (S := S) (l := l) hKB 1; simpa using this
  have hA : ulH S 1 γ y < S.psi K (Om (1 + 1)) := lt_psi_of_mem hκ hzD.2.1 hzW
  have hDy : D ≤ y := by rw [← hcD]; exact le_add_self
  have hDW : D < Om (1 + 1) := (hDy.trans_lt hy).trans hzW
  obtain ⟨hψe, howne⟩ := Vp.vp_run (S := S) (s := 1) hs hγV hown' hc hDW hcond
  rw [hcD] at hψe
  have hzeD : VbDK S l K (S.psi (B + Om (1 + 1) ^ γ * D) (Om (1 + 1))) := by rw [hψe]; exact hzD
  obtain ⟨heD, heA⟩ := fa_arg hl hX (r := 1) le_rfl hzeD howne
  have hBe : B ≤ B + Om (1 + 1) ^ γ * D := le_self_add
  have hBA : B < ConjT.Aη S (cdEta S l) := hBe.trans_lt heA
  have h0A : ulH S 1 γ 0 < S.psi K (Om (1 + 1)) := ((ulH_le_iff γ).2 zero_le).trans_lt hA
  have hOW : SC (Om ω : Ordinal.{0}) := SC_Om omega0_ne_zero
  have hownW2 : (Om ω : Ordinal.{0}) ∈ S.CSet (Om ω) (S.psi (Om ω) (Om (1 + 1))) := ConjT.OmW_mem S _ _
  have hownW3 : (Om ω : Ordinal.{0}) ∈ S.CSet (Om ω) (S.psi (Om ω) (Om (1 + 1 + 1))) := ConjT.OmW_mem S _ _
  have hW0 : (Om ω : Ordinal.{0}) ≠ 0 := hOW.1.ne'
  have h3W : Om (1 + 1 + 1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 Vp.vp_three_lt_omega
  have hdW3 : Om (1 + 1 + 1) ∣ (Om ω : Ordinal.{0}) := by
    have h := opow_dvd_opow ω h3W.le
    rwa [Kx.kx3e, gg_SC_eps hOW] at h
  -- `θ` is the first value of `Hˡ¹_{θ₂}`
  have hΘ2 : ulH S 1 (S.psi (Om ω) (Om (1 + 1 + 1))) 0 = ConjT.th S := Us.us_bv_atom hs hownW2 hW0 hdW3
  have hθS : SC (ConjT.th S) := Ui.ui_psi_SC (s := 1) (Om ω)
  have h1θ : Om 1 < ConjT.th S := Ui.ui_L_lt_psi (s := 1) (Om ω)
  have hfixθ : ulD S 1 γ < ConjT.th S → ulH S 1 γ (ConjT.th S) = ConjT.th S := fun hd =>
    Uc.ucG_fix_lower hγ ⟨0, hΘ2⟩ hd
  have hθy : ulD S 1 γ < ConjT.th S → ConjT.th S < y := fun hd => by
    have h := hθz
    rw [← hfixθ hd] at h
    exact (ulH_lt_iff γ).1 h
  -- the parts
  have hparts : VbDK S l K γ ∧ VbDK S l K D ∧ VbDK S l K B ∧ VbDK S l K c ∧ Om ω ≤ B ∧
      (c = 0 → γ ≠ 0 ∧ ∃ K1, K1 ∈ S.CSet K1 (S.psi K1 (Om (1 + 1))) ∧ VbDK S l K K1 ∧ Om ω ≤ K1 ∧
        B = K1 + Om (1 + 1) ^ γ ∧ ¬ UlK S 1 (S.psi K1 (Om (1 + 1))) γ) := by
    rcases hcase with hc0 | ⟨hcf, hmax⟩
    · -- the first run
      subst hc0
      rw [zero_add] at hcD
      subst hcD
      have hdθ : ConjT.th S ≤ ulD S 1 γ := not_lt.1 fun hd => by
        have h1 := hcond (ConjT.th S) (hθy hd).le
        rw [zero_add, hfixθ hd] at h1
        exact lt_irrefl _ h1
      have hγ0 : γ ≠ 0 := by
        rintro rfl
        exact absurd ((hdθ.trans (ulD_le_self 0))) (not_le.2 hθS.1)
      have hγN : γ ∈ ⋃ a, S.CSet a 0 := by
        obtain ⟨a, ha⟩ := mem_iUnion.1 (fa_nota hX.le hzD.1)
        have hzC : ulH S 1 γ D ∈ S.CSet a (S.psi a (Om (0 + 1))) := CSet_mono le_rfl zero_le ha
        have hK0 : UlK S 0 (S.psi a (Om (0 + 1))) (ulH S 1 γ D) := ul_K_of_mem hzC
        have hq : SC (S.psi a (Om (0 + 1))) := Ui.ui_psi_SC (s := 0) a
        have hqL : S.psi a (Om (0 + 1)) ≤ Om (0 + 1) := (Ui.ui_psi_lt (s := 0) a).le
        have h := (Uz.uz_L1_mp hs zero_lt_one hq hqL hγV hzW (ne_of_gt hy) hK0).1
        have hlam : S.psi a (Om (0 + 1)) ≤ S.Lam := Us.us_qΛ (i := 0) omega0_pos hqL
        exact fa_nota (A := a) (by rw [zero_add]) (Uw.uw_K_CSet hlam h)
      obtain ⟨K1, K2, hK1o, hK1m, hK1, hK2o, hK2g, hK2, B0, hown0, hB0, hform⟩ :=
        faCert (S := S) (s := 1) hs le_rfl hγ0 hγV hγN h0A
      have hBB : B0 = B := Ui.ui_own_unique (s := 1) hown0 hown' (hB0.trans hc)
      subst hBB
      have hviz : ∀ e, UlK S 1 (S.psi e (Om (1 + 1))) γ ↔ ulDat S (Om (1 + 1)) γ < S.psi e (Om (1 + 1)) := fun e =>
        Uo.uo_K_iff_dat hs (Ui.ui_psi_SC (s := 1) e) (Ui.ui_L_lt_psi (s := 1) e) (Ui.ui_psi_lt (s := 1) e).le hγN
      have hdat : ConjT.th S ≤ ulDat S (Om (1 + 1)) γ := not_lt.1 fun h => by
        exact absurd ((ul_vis hθS).2 ((hviz (Om ω)).2 h)) (not_lt.2 hdθ)
      have hK1W : Om ω ≤ K1 := not_lt.1 fun h =>
        absurd ((hK1 (Om ω) hW0).2 h) (not_lt.2 hdat)
      have hK2W : K2 < Om ω := (hK2 (Om ω) hW0).1 hγ
      have hle21 : K2 ≤ K1 := (hK2W.trans_le hK1W).le
      rcases hform with ⟨hBK, -⟩ | ⟨hBM, -, -⟩
      · exfalso
        have h1 : ulD S 1 γ < S.psi B0 (Om (1 + 1)) := by rw [hB0]; exact ulH_D_lt γ 0
        rw [hBK] at h1
        exact absurd (hdθ.trans_lt h1) (not_lt.2 (psi_mono hκ hK2W.le).1)
      · rw [max_eq_left hle21] at hBM
        have e1 : B0 + Om (1 + 1) ^ γ * D = K1 + Om (1 + 1) ^ γ * (1 + D) := by
          rw [hBM, mul_add, mul_one, add_assoc]
        have hD1 : 1 + D ≠ 0 := (lt_of_lt_of_le zero_lt_one le_self_add).ne'
        have hD2 : 1 + D < Om (1 + 1) :=
          (Ui.ui_SC_W 1).isPrincipal (Ui.ui_one_lt_SC (Ui.ui_SC_W _)) hDW
        have hγD : VbDK S l K γ := by
          have he := heD
          rw [e1] at he
          exact hPC.dig_exp (r := 1) hW he γ (fa_dig hD1 hD2)
        have hWγ : VbDK S l K (Om (1 + 1) * γ) := by
          have := hPC.opow_mul hW γ hγD; rwa [Ui.ui_W_opow 1] at this
        have hK1D : VbDK S l K K1 :=
          fa_K1_D hl hX hKB (k := 0) hγD hγN (by simp only [Nat.cast_zero, zero_add]; exact hK1o)
            (by simp only [Nat.cast_zero, zero_add]; exact hK1)
        have hBD : VbDK S l K B0 := by
          rw [hBM]
          refine hPC.add hK1D ?_
          rw [Ui.ui_W_eq 1 γ]
          have := hPC.opow_mul hWγ _ hPC.one
          rwa [mul_one] at this
        have hsub : VbDK S l K (Om (1 + 1) ^ γ * D) := by
          have := hPC.sub heD hBD hBe
          rwa [Ordinal.add_sub_cancel] at this
        have hDD : VbDK S l K D := by
          have h := hPC.div _ hsub _ hWγ
          rwa [← Ui.ui_W_eq 1 γ, Ordinal.mul_div_cancel _ (Ui.ui_W_pos _ γ).ne'] at h
        have hK1N : ¬ UlK S 1 (S.psi K1 (Om (1 + 1))) γ := by
          intro h
          have h' := (hviz K1).1 h
          have hK10 : K1 ≠ 0 := ((hOW.1).trans_le hK1W).ne'
          exact lt_irrefl K1 ((hK1 K1 hK10).1 h')
        have hK1W' : Om ω ≤ B0 := hK1W.trans (by rw [hBM]; exact le_self_add)
        exact ⟨hγD, hDD, hBD, hPC.zero, hK1W', fun _ => ⟨hγ0, K1, hK1o, hK1D, hK1W, hBM, hK1N⟩⟩
    · -- a later run
      have hψc : S.psi B (Om (1 + 1)) = c := hc.symm.trans hcf
      have hfixB : ulH S 1 γ (S.psi B (Om (1 + 1))) = S.psi B (Om (1 + 1)) := by rw [hψc, hcf]
      have hcθ : ConjT.th S ≤ c := by
        by_cases hd : ulD S 1 γ < ConjT.th S
        · exact hmax _ (hfixθ hd) (hθy hd).le
        · rw [← hcf]; exact (not_lt.1 hd).trans (ulH_D_lt γ c).le
      have hWB : Om ω ≤ B := not_lt.1 fun h => by
        have h1 := Ui.ui_psi_lt_of_own (s := 1) hown' h
        rw [hψc] at h1
        exact absurd h1 (not_lt.2 hcθ)
      have hB0 : B ≠ 0 := ((hOW.1).trans_le hWB).ne'
      obtain ⟨hdiv, -, -⟩ := (Us.us_fix_iff hs hown' hB0 hγV).1 hfixB
      have hD0 : D ≠ 0 := by
        rintro rfl
        rw [add_zero] at hcD
        rw [← hcD, hcf] at hy
        exact lt_irrefl _ hy
      obtain ⟨hγD, hDD, hBD⟩ := hPC.run (r := 1) hW heD hdiv hD0 hDW
      have hcD' : VbDK S l K c := by
        rw [← hψc]
        have := fa_coll (S := S) (l := l) hKB (j := 1) hBD hBA
        simpa using this
      have hc0 : c ≠ 0 := ((hθS.1).trans_le hcθ).ne'
      exact ⟨hγD, hDD, hBD, hcD', hWB, fun h => absurd h hc0⟩
  obtain ⟨hγD, hDD, hBD, hcD', hWB, hfirst⟩ := hparts
  have hyD : VbDK S l K y := by rw [← hcD]; exact hPC.add hcD' hDD
  have h3Om : Om (1 + 1 + 1 : Ordinal.{0}) ≤ Om ω := h3W.le
  have hWe : Om ω ≤ B + Om (1 + 1) ^ γ * D := hWB.trans hBe
  have hWA : Om ω < ConjT.Aη S (cdEta S l) := hWe.trans_lt heA
  -- `T γ < θ`
  have hWD : VbDK S l K (Om ω) := ⟨ConjT.OmW_mem S _ _, ConjT.OmW_mem S _ _, hWK⟩
  have hTθ2 : vbTK S l K (S.psi (Om ω) (Om (1 + 1 + 1))) = ConjT.th S := by
    have h := (vbTK_atom hl hX hKB (k := 1) le_rfl hWD (by simpa using hownW3)).1
    rw [vbTK_OmW hl hX hKB hWK] at h
    simpa using h
  have hθ2D : VbDK S l K (S.psi (Om ω) (Om (1 + 1 + 1))) := by
    have := fa_coll (S := S) (l := l) hKB (j := 2) hWD hWA
    simpa [one_add_one_eq_two] using this
  have hTγ : vbTK S l K γ < ConjT.th S := by
    have h := vbTK_mono hl hX hKB hγD hθ2D hγ
    rwa [hTθ2] at h
  have hθ2 : ConjT.th S < Om (1 + 1) := psi_lt hκ _
  have hγ'V : vbTK S l K γ < Om (1 + 1) := hTγ.trans hθ2
  -- the moves
  have h3B : Om (1 + 1 + 1) ≤ B := h3Om.trans hWB
  obtain ⟨-, hownG, hTB⟩ := faG_law hl hX hKB hown hρ hBD hown' hBA h3B
  obtain ⟨-, hownGe, hTe⟩ := faG_law hl hX hKB hown hρ heD howne heA (h3Om.trans hWe)
  rw [faG_add hl hX hKB hBD hγD hDD hγV hDW, hψe] at hTe
  rw [faG_add hl hX hKB hBD hγD hDD hγV hDW] at hownGe
  have hAG : ConjT.Aη S (cdEta S l) ≤ faG S l K B := le_self_add.trans (le_self_add.trans le_self_add)
  have hG0 : faG S l K B ≠ 0 := (((hOW.1).trans hWA).trans_le hAG).ne'
  have hθG : ConjT.th S ≤ S.psi (faG S l K B) (Om (1 + 1)) := (psi_mono hκ (hWA.le.trans hAG)).1
  have hqD : VbDK S l K (S.psi B (Om (1 + 1))) := by
    have := fa_coll (S := S) (l := l) hKB (j := 1) hBD hBA
    simpa using this
  have hK0B : ∀ {B' : Ordinal.{0}}, VbDK S l K B' → B' < ConjT.Aη S (cdEta S l) →
      vbTK S l K (S.psi B' (Om (1 + 1))) = S.psi (faG S l K B') (Om 1) →
      (UlK S 1 (S.psi B' (Om (1 + 1))) γ ↔ UlK S 0 (S.psi (faG S l K B') (Om 1)) (vbTK S l K γ)) := fun {B'} hB'D hB'A hT' => by
    have hq'D : VbDK S l K (S.psi B' (Om (1 + 1))) := by
      have := fa_coll (S := S) (l := l) hKB (j := 1) hB'D hB'A
      simpa using this
    have h := faK0_iff hl hX hKB hq'D (Ui.ui_psi_SC (s := 1) B') (Ui.ui_L_lt_psi (s := 1) B')
      (Ui.ui_psi_lt (s := 1) B').le γ hγD
    rwa [hT'] at h
  have hbase : ulH S 0 (vbTK S l K γ) (vbTK S l K c) = S.psi (faG S l K B) (Om 1) := by
    by_cases hc0 : c = 0
    · subst hc0
      obtain ⟨hγ0, K1, hK1o, hK1D, hK1W, hBM, hK1N⟩ := hfirst rfl
      have hγ'0 : vbTK S l K γ ≠ 0 := by
        have h := vbTK_mono hl hX hKB hPC.zero hγD (pos_iff_ne_zero.2 hγ0)
        rw [vbTK_zero hl hX hKB] at h
        exact h.ne'
      have hK1le : K1 ≤ B := by rw [hBM]; exact le_self_add
      have hK1A : K1 < ConjT.Aη S (cdEta S l) := hK1le.trans_lt hBA
      obtain ⟨-, hownK, hTK⟩ := faG_law hl hX hKB hown hρ hK1D hK1o hK1A (h3Om.trans hK1W)
      have hGB : faG S l K B = faG S l K K1 + Om 1 ^ vbTK S l K γ := by
        have h := faG_add hl hX hKB hK1D hγD hPC.one hγV (Ui.ui_one_lt_SC (Ui.ui_SC_W 1))
        rw [mul_one, fa_T_one hl hX hKB, mul_one] at h
        rw [hBM]; exact h
      have hdvdG : Om 1 ^ vbTK S l K γ ∣ faG S l K B := by
        rw [hGB]
        have hI : Indec (Om 1 ^ vbTK S l K γ) := by
          have := Vp.vp_Wg_indec (0 : Ordinal.{0}) (vbTK S l K γ); simpa using this
        exact Vp.vp_dvd_self_add hI _
      have hKγ : UlK S 1 (S.psi B (Om (1 + 1))) γ :=
        (ul_vis (Ui.ui_psi_SC (s := 1) B)).1 (by rw [← hc]; exact ulH_D_lt γ 0)
      have hK' := (hK0B hBD hBA hTB).1 hKγ
      have hval := fa0_val_of hownG hG0 hγ'0 hγ'V hdvdG (hTγ.le.trans hθG) hK'
      have hNK : ¬ UlK S 0 (S.psi (faG S l K K1) (Om 1)) (vbTK S l K γ) := fun h =>
        hK1N ((hK0B hK1D hK1A hTK).2 h)
      rw [vbTK_zero hl hX hKB]
      exact fa0_first_of hγ'0 hownG hval hGB hownK hNK
    · obtain ⟨hcf, -⟩ := hcase.resolve_left hc0
      have hψc : S.psi B (Om (1 + 1)) = c := hc.symm.trans hcf
      have hfixB : ulH S 1 γ (S.psi B (Om (1 + 1))) = S.psi B (Om (1 + 1)) := by rw [hψc, hcf]
      have hB0 : B ≠ 0 := ((hOW.1).trans_le hWB).ne'
      obtain ⟨hdiv, -, hKγ⟩ := (Us.us_fix_iff hs hown' hB0 hγV).1 hfixB
      have hd' := faG_dvd hl hX hKB hown hρ hWK hBD hγD hγV hTγ hWB hdiv
      have hK' := (hK0B hBD hBA hTB).1 hKγ
      have hfix' := (fa0_fix_iff hownG hG0 hγ'V).2 ⟨hd', hTγ.trans_le hθG, hK'⟩
      have hTc : vbTK S l K c = S.psi (faG S l K B) (Om 1) := by rw [← hψc, hTB]
      rw [hTc, hfix']
  have hdvd' := fa0_dvd_val hownG hbase
  have hv' : vbTK S l K D < S.psi (faG S l K B + Om 1 ^ vbTK S l K γ * vbTK S l K D) (Om 1) := by
    rw [← hTe]; exact vbTK_mono hl hX hKB hDD hzD (hDy.trans_lt hy)
  have hcond' := fa0_valid hdvd' hbase hv'
  have hD'1 : vbTK S l K D < Om 1 := hv'.trans (fa0_lt _)
  have hrun := fa0_run hγ'V hownG hbase hD'1 hcond'
  have hTy : vbTK S l K y = vbTK S l K c + vbTK S l K D := by
    rw [← hcD]; exact kzT_add hl hX hKB hcD' hDD
  refine ⟨hγD, hyD, hDD, hcD', hTγ, hcond', hbase, hTy, ?_, hBD, hBA, hWB⟩
  rw [hTe, hrun, hTy]

/-- **THE READING MOVES THE ATOMS ABOVE `θ`**: `T(Hˡ¹_γ(y)) = Φ_{T γ}(T y)`. -/
theorem faAL {γ y : Ordinal.{0}} (hWK : Om ω < K) (hγ : γ < S.psi (Om ω) (Om (1 + 1 + 1)))
    (hy : y < ulH S 1 γ y) (hzW : ulH S 1 γ y < Om (1 + 1)) (hzD : VbDK S l K (ulH S 1 γ y))
    (hθz : ConjT.th S < ulH S 1 γ y) :
    VbDK S l K γ ∧ VbDK S l K y ∧ vbTK S l K γ < ConjT.th S ∧
      vbTK S l K (ulH S 1 γ y) = ulH S 0 (vbTK S l K γ) (vbTK S l K y) := by
  have hA : ulH S 1 γ y < S.psi K (Om (1 + 1)) := lt_psi_of_mem (InR_Om_succ 1) hzD.2.1 hzW
  obtain ⟨B, c, D, hown', hc, hcD, hcond, hcase⟩ := Vp.vp_dec (S := S) (s := 1) one_lt_omega0 hy hA
  obtain ⟨h1, h2, -, -, h3, -, -, -, h4, -⟩ :=
    faALc hl hX hKB hown hρ hWK hγ hy hzW hzD hθz hown' hc hcD hcond hcase
  exact ⟨h1, h2, h3, h4⟩

end Law

end Googology.Trans.PoR.InaccPsi.R2.Fa
