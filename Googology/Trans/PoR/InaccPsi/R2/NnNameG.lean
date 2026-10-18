import Googology.Trans.PoR.InaccPsi.R2.NnTheta
import Googology.Trans.PoR.InaccPsi.R2.LwLev

/-!
# The name of a `Γ`-point that is not a fixed point of `GG`: `e(η_F) = Ω₁·Ω₁ + logend(a)`; the notation
statement there

`W = Ω₁^{Ω₁}`, `U = Ω₁^{Ω₁+1}`, `GG` the enumeration of the `Γ`-points, `D = deriv GG` (the fixed points of `GG`,
`R2.LwLev`).  At a named restart `F = υ_F`:

* `nn_ggfix_of_big` (**a last exponent `> Ω₁·Ω₁ + Ω₁` names a fixed point of `GG`**): Theorem START at `U`
  (`Lw.lw_start_U`) puts a value of `D` in `(y, F]` for every `y < F`;
* `nn_ggfix_of_U`: a name `η₀ + U·k` (`ω^{e+1} ∣ η₀`, `k < ω`) names a value of `D` (START at `U`, `k` times);
* `nnName_gg` (**THE NAME OF A `Γ`-POINT `F = GG(a)` WITH `GG(F) ≠ F`**): `e(η_F) = Ω₁·Ω₁ + logend(a)`.  The last
  exponent is `≥ Ω₁·Ω₁` (`Nn.nn_gp_big`), `< Ω₁·Ω₁ + Ω₁` (the two lemmas above); then `η_F = η₀ + W·β`, START and
  SEG at `W` (`Nm.start_GG`, `Nm.seg_GG`) with `β - 1 < Zu(η₀ + W, W)` (else a window plateau, `Nm.linvG_HCl` at
  level `Ω₁`);
* `nnTheta_gg`: `Θ_F(Ω₁·Ω₁ + d) = F·F + d` (`d < F`; no code in `[Ω₁·F, Ω₁·Ω₁)`);
* `nnCode_gg`, `nnTH_gg` (**THE NOTATION STATEMENT AT THE `Γ`-POINTS THAT ARE NOT FIXED POINTS OF `GG`**):
  `Θ_F(m_F) = O_X(F)` for every term system with linear and square terms (both `F·F + logend(a)`, Theorem GG).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Nn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Br Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Fx Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Lw

variable {S : InaccSeq.{0}}

theorem nn_U_eq : Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) = ω ^ (Om 1 * Om 1 + Om 1) := by
  rw [Om1_pow, mul_add_one]

theorem nn_U_mem {a b : Ordinal.{0}} (hb : 1 < b) : Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) ∈ S.CSet a b := by
  have := lw_mem_U_mul (S := S) (a := a) hb; rwa [mul_one] at this

theorem nn_W_mem {a b : Ordinal.{0}} (hb : 1 < b) : W ∈ S.CSet a b := by
  have := mem_W_mul (S := S) (a := a) hb; rwa [mul_one] at this

theorem nn_one_lt_Pv (S : InaccSeq.{0}) (η : Ordinal.{0}) : 1 < Pv S η :=
  one_lt_SC (Pv_SC S η)

/-- **A last exponent `> Ω₁·Ω₁ + Ω₁` names a fixed point of `GG`.** -/
theorem nn_ggfix_of_big {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) (hbig : Om 1 * Om 1 + Om 1 + 1 ≤ cdExp (cdEta S F)) : GG F = F := by
  set η := cdEta S F with hηd
  obtain ⟨-, hι, -, hP⟩ := cdEta_pv_spec (S := S) hF.1 hX
  rw [hfix] at hP
  obtain ⟨hE, -, hww, hlim, -⟩ := nn_fix_facts hF hfix
  have hη0 : η ≠ 0 := by
    intro h0
    rw [← hηd] at hι
    rw [h0, iota_zero] at hι
    have : (1 : Ordinal.{0}) < F :=
      lt_of_le_of_lt (Order.one_le_iff_pos.2 (mul_pos omega0_pos omega0_pos)) hww
    exact this.ne hι
  obtain ⟨η', hdec, -⟩ := cdExp_decomp hη0
  set e := cdExp η with he
  set U := Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) with hU
  refine le_antisymm ?_ (GG_strictMono.id_le F)
  rw [GG_normal.apply_of_isSuccLimit hlim]
  refine ciSup_le' fun y => ?_
  set l := y.1 + 1 with hl
  have hlF : l < F := hlim.add_one_lt y.2
  have hlι : l < iota S η := by rw [← hηd] at hι; rw [hι]; exact hlF
  obtain ⟨ζ, hζη, hζg, hζι⟩ := cd_good_name (Order.one_le_iff_pos.2 (lt_of_le_of_lt zero_le (lt_add_one y.1)))
    hlι
  have hPζ : Pv S ζ = upsilon l := by
    have h := ups_iota S ζ
    rw [hζι] at h; exact h.symm
  have hyζ : y.1 < Pv S ζ := by rw [hPζ]; exact (lt_add_one y.1).trans_le upsilon_normal.strictMono.le_apply
  set ζ1 := ζ + U with hζ1
  have hd1 : U ∣ ζ1 := by
    have hU0 : U ≠ 0 := (Om1_pow_pos _).ne'
    have hab : ζ % U + U = U := nn_absorb (x := Om 1 * Om 1 + Om 1)
      (by rw [← nn_U_eq]; exact mod_lt ζ hU0) nn_U_eq.ge
    refine ⟨ζ / U + 1, ?_⟩
    rw [hζ1, mul_add_one]
    conv_lhs => rw [← div_add_mod ζ U]
    rw [add_assoc, hab]
  have hgood1 : Bt.Good S ζ1 := good_add hζg (nn_U_mem (nn_one_lt_Pv S _))
  have hst := lw_start_U hgood1 hd1
  set s := Pv S (ζ1 + U) with hs
  have hsfix : GG s = s := by
    obtain ⟨c, hc⟩ : s ∈ range (deriv GG) := by rw [hst]; exact nxt_mem _ _
    rw [← hc]; exact lw_D_fix c
  have hys : y.1 < s := by
    calc y.1 < Pv S ζ := hyζ
      _ ≤ Pv S ζ1 := Pv_mono le_self_add
      _ < s := by rw [hst]; exact lt_nxt lw_D_normal lw_D_zero _
  have hsF : s ≤ F := by
    have hUU : U + U < ω ^ e := by
      have h2 : U + U < ω ^ (Om 1 * Om 1 + Om 1 + 1) := by
        have e1 : U + U = ω ^ (Om 1 * Om 1 + Om 1) * 2 := by
          rw [hU, nn_U_eq, ← one_add_one_eq_two, mul_add_one, mul_one]
        have e2 : ω ^ (Om 1 * Om 1 + Om 1 + 1) = ω ^ (Om 1 * Om 1 + Om 1) * ω := by rw [opow_add, opow_one]
        rw [e1, e2]
        exact (mul_lt_mul_iff_right₀ (opow_pos _ omega0_pos)).2 (natCast_lt_omega0 2)
      exact h2.trans_le (opow_le_opow_right omega0_pos hbig)
    have hlt : ζ + (U + U) < η := by rw [hdec]; exact nn_add_lt_block (hdec ▸ hζη) hUU
    rw [hs, hζ1, add_assoc, ← hP]
    exact Pv_mono hlt.le
  refine le_of_lt ?_
  calc GG y.1 < GG s := GG_strictMono hys
    _ = s := hsfix
    _ ≤ F := hsF

/-- **A name `η₀ + U·k` with `U ∣ η₀`, `η₀` good, names a value of `D = deriv GG`** (START at `U`, `k` times). -/
theorem nn_ggfix_of_U {η0 : Ordinal.{0}} (hg0 : Bt.Good S η0)
    (hd0 : Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) ∣ η0) :
    ∀ m : ℕ, Bt.Good S (η0 + Om 1 ^ (Om 1 + 1) * (m : Ordinal.{0})) ∧
      (m ≠ 0 → GG (Pv S (η0 + Om 1 ^ (Om 1 + 1) * (m : Ordinal.{0}))) =
        Pv S (η0 + Om 1 ^ (Om 1 + 1) * (m : Ordinal.{0}))) := by
  intro m
  induction m with
  | zero => simp only [Nat.cast_zero, mul_zero, add_zero]; exact ⟨hg0, fun h => absurd rfl h⟩
  | succ m ih =>
    obtain ⟨hgm, -⟩ := ih
    set U := Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) with hU
    have he : η0 + U * ((m + 1 : ℕ) : Ordinal.{0}) = (η0 + U * (m : Ordinal.{0})) + U := by
      rw [Nat.cast_succ, mul_add_one, add_assoc]
    have hdm : U ∣ η0 + U * (m : Ordinal.{0}) := dvd_add hd0 (dvd_mul_right _ _)
    have hst := lw_start_U hgm hdm
    rw [he]
    refine ⟨good_add hgm (nn_U_mem (nn_one_lt_Pv S _)), fun _ => ?_⟩
    rw [hst]
    obtain ⟨c, hc⟩ := nxt_mem (deriv GG) (Pv S (η0 + U * (m : Ordinal.{0})))
    rw [← hc]; exact lw_D_fix c


/-- **THE NAME OF A `Γ`-POINT `F = GG(a)` WITH `GG(F) ≠ F`**: `e(η_F) = Ω₁·Ω₁ + logend(a)`. -/
theorem nnName_gg {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hG : IsGP F)
    (hGF : GG F ≠ F) (hX : upsilon F < Pv S ηx) :
    cdExp (cdEta S F) = Om 1 * Om 1 + lg (invGG F) := by
  have hbig := nn_gp_big hF hfix hG hX
  set η := cdEta S F with hηd
  obtain ⟨hg, hι, -, hP⟩ := cdEta_pv_spec (S := S) hF.1 hX
  rw [← hηd] at hg hι hP
  rw [hfix] at hP
  obtain ⟨hE, hp, hww, hlim, hU⟩ := nn_fix_facts hF hfix
  have hFO : F < Om 1 := fx_fix_lt_Om1 hfix hX
  have hη0 : η ≠ 0 := by
    intro h0
    rw [h0, iota_zero] at hι
    have : (1 : Ordinal.{0}) < F :=
      lt_of_le_of_lt (Order.one_le_iff_pos.2 (mul_pos omega0_pos omega0_pos)) hww
    exact this.ne hι
  set e := cdExp η with he
  have hde : ω ^ e ∣ η := cdExp_dvd hη0
  have hUe1 : ω ^ (e + 1) ≠ 0 := nn_opow_ne _
  set η0 := ω ^ (e + 1) * (η / ω ^ (e + 1)) with hη0d
  set t := η % ω ^ (e + 1) with htd
  have hηt : η = η0 + t := (div_add_mod η _).symm
  have hd0 : ω ^ (e + 1) ∣ η0 := dvd_mul_right _ _
  have ht1 : t < ω ^ (e + 1) := mod_lt η hUe1
  have hdt : ω ^ e ∣ t := by
    have h1 : ω ^ e ∣ η0 := (opow_dvd_opow ω le_self_add).trans hd0
    have h2 : ω ^ e ∣ η0 + t := hηt ▸ hde
    exact (dvd_add_iff h1).1 h2
  obtain ⟨k, hk⟩ := hdt
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    have : ω ^ (e + 1) ∣ η := by rw [hηt, hk, add_zero]; exact hd0
    exact absurd (cdExp_max hη0 this) (not_le.2 (lt_add_one e))
  have hkω : k < ω := by
    have : ω ^ e * k < ω ^ e * ω := by rw [← hk, ← opow_succ]; exact ht1
    exact (mul_lt_mul_iff_right₀ (opow_pos _ omega0_pos)).1 this
  have hg0 : Bt.Good S η0 := nnPrefix_good hd0 ht1 (hηt ▸ hg)
  -- `e < Ω₁·Ω₁ + Ω₁`
  have hsm : e < Om 1 * Om 1 + Om 1 := by
    by_contra h
    push Not at h
    rcases h.lt_or_eq with hlt | heq
    · exact hGF (nn_ggfix_of_big hF hfix hX (Order.add_one_le_of_lt hlt))
    · have hUe : Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) = ω ^ e := by rw [nn_U_eq, heq]
      have hdU : Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) ∣ η0 := by
        rw [hUe]; exact (opow_dvd_opow ω le_self_add).trans hd0
      obtain ⟨m, rfl⟩ := lt_omega0.1 hkω
      have hm : m ≠ 0 := fun h => hk0 (by rw [h]; rfl)
      have hfixη := (nn_ggfix_of_U hg0 hdU m).2 hm
      rw [hUe, ← hk, ← hηt, hP] at hfixη
      exact hGF hfixη
  -- `e = Ω₁·Ω₁ + e'`, `t = W·β`
  set e' := e - Om 1 * Om 1 with he'd
  have hee : e = Om 1 * Om 1 + e' := (Ordinal.add_sub_cancel_of_le hbig).symm
  have he'O : e' < Om 1 := by
    have : Om 1 * Om 1 + e' < Om 1 * Om 1 + Om 1 := by rw [← hee]; exact hsm
    exact (add_lt_add_iff_left _).1 this
  set β := ω ^ e' * k with hβd
  have htβ : t = W * β := by
    rw [hk, hee, opow_add, mul_assoc]
    show ω ^ (Om 1 * Om 1) * (ω ^ e' * k) = Om 1 ^ Om 1 * (ω ^ e' * k)
    rw [Om1_pow]
  have hβ0 : β ≠ 0 := mul_ne_zero (nn_opow_ne _) hk0
  have hβO : β < Om 1 := nn_mul_lt_Om1 (nn_opow_lt_Om1 he'O) (hkω.trans (omega0_lt_Om one_ne_zero))
  have hlgβ : lg β = e' := by
    obtain ⟨m, rfl⟩ := lt_omega0.1 hkω
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by
      have : m ≠ 0 := fun h => hk0 (by rw [h]; rfl)
      omega⟩
    have := cpExp_mul_succ e' (m' : Ordinal.{0})
    rw [hβd, Nat.cast_succ]; exact this
  have hdW : W ∣ η0 := by
    show Om 1 ^ Om 1 ∣ η0
    rw [Om1_pow]
    exact (opow_dvd_opow ω ((le_self_add.trans_eq hee.symm).trans le_self_add)).trans hd0
  -- START and the segment at `W`
  have hst := start_GG hg0 hdW
  obtain ⟨c1, hc1⟩ := nn_nxt_succ GG_normal GG_zero (Pv S η0)
  rw [hc1] at hst
  set β1 := η0 + W with hβ1d
  set β' := β - 1 with hβ'd
  have hββ : 1 + β' = β := Ordinal.add_sub_cancel_of_le (Order.one_le_iff_ne_zero.2 hβ0)
  have hηβ1 : η = β1 + W * β' := by
    rw [hηt, htβ, ← hββ, mul_add, mul_one, hβ1d, add_assoc]
  have hβ'O : β' < Om 1 := (Ordinal.sub_le_self _ _).trans_lt hβO
  have hg1 : Bt.Good S β1 := good_add hg0 (nn_W_mem (nn_one_lt_Pv S _))
  have hd1 : W ∣ β1 := dvd_add hdW dvd_rfl
  set Zβ := Zu S β1 W with hZβ
  have hR3 : β' < Zβ := by
    by_contra hle
    push Not at hle
    set β2 := β1 + W * Zβ with hβ2d
    have hPβ2 : Pv S β2 = Zβ := Zu_fix S β1 _
    have hsplit : Zβ + (β' - Zβ) = β' := Ordinal.add_sub_cancel_of_le hle
    have hηβ2 : η = β2 + W * (β' - Zβ) := by
      rw [hηβ1, hβ2d, add_assoc β1, ← mul_add, hsplit]
    have hUE : Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) ≠ 0 := (Om1_pow_pos _).ne'
    set r0 := η0 % Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) with hr0d
    have hr0dv : W ∣ r0 := by
      have h1 : W ∣ Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) *
          (η0 / Om 1 ^ (Om (1 : Ordinal.{0}) + 1)) :=
        (opow_dvd_opow (Om 1) le_self_add).trans (dvd_mul_right _ _)
      have h2 : W ∣ Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) *
          (η0 / Om 1 ^ (Om (1 : Ordinal.{0}) + 1)) + r0 := by
        rw [hr0d, div_add_mod]; exact hdW
      exact (dvd_add_iff h1).1 h2
    obtain ⟨b0, hb0⟩ := hr0dv
    have hb0O : b0 < Om 1 := by
      have : W * b0 < W * Om 1 := by
        rw [← hb0]
        show η0 % Om 1 ^ (Om 1 + 1) < Om 1 ^ Om 1 * Om 1
        rw [← opow_succ]; exact mod_lt η0 hUE
      exact (mul_lt_mul_iff_right₀ (Om1_pow_pos _)).1 this
    have hw : ∀ y'' ≤ W * (β' - Zβ), ¬ HCl S (ConjT.Aη S β2) (Pv S β2) (β2 + y'') := by
      intro y'' hy''
      have hm : y'' / W ≤ β' - Zβ := Ordinal.div_le_of_le_mul hy''
      have hmO : y'' / W < Om 1 := hm.trans_lt ((Ordinal.sub_le_self _ _).trans_lt hβ'O)
      have hZO : Zβ < Om 1 := Zu_lt_Om1 S _ _
      have hz0O : b0 + 1 + Zβ + y'' / W < Om 1 :=
        fx_Om1_prin (fx_Om1_prin (fx_Om1_prin hb0O one_lt_Om1) hZO) hmO
      have hrep : β2 + y'' = Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) *
          (η0 / Om 1 ^ (Om (1 : Ordinal.{0}) + 1)) + Om 1 ^ Om (1 : Ordinal.{0}) * (b0 + 1 + Zβ + y'' / W) +
          y'' % W := by
        rw [hβ2d, hβ1d]
        conv_lhs => rw [← div_add_mod η0 (Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1)),
          ← div_add_mod y'' W]
        rw [← hr0d, hb0]
        simp only [mul_add, mul_one, add_assoc]
      refine nn_not_HCl_digit (Pv_SC S β2) (Pv_lt_Om1 S β2) le_rfl hrep hz0O
        (mod_lt _ (Om1_pow_pos _).ne') ?_
      rw [hPβ2]; exact le_add_self.trans le_self_add
    have := (nnWPlat hw).2
    rw [← hηβ2] at this
    exact this hg
  have hseg := seg_GG hg1 hd1 hst β' hR3.le
  have hseg' := hseg
  rw [← hηβ1, hP] at hseg
  set c := c1 + 1 + β' with hcd
  have hc0 : c ≠ 0 := (lt_of_lt_of_le (add_pos_of_right zero_lt_one c1) le_self_add).ne'
  have hna : GG c ≠ c := by
    intro h
    have hGc : IsGP c := by rw [← h]; exact isGP_GG (pos_iff_ne_zero.2 hc0)
    have hu : upsilon c = c := nn_gp_fix hGc
    have hp' := (cp_fix_facts (ri_of_fp (pos_iff_ne_zero.2 hc0) hu) hu).2.1
    rcases eq_or_ne β' 0 with h0 | h0
    · rw [hcd, h0, add_zero] at hu
      exact nn_succ_not_fix c1 hu
    · have hceq : c = β' := by
        rcases lt_or_eq_of_le (le_add_self : β' ≤ c1 + 1 + β') with hlt | heq
        · exact absurd (hp' (lt_add_of_pos_right (c1 + 1) (pos_iff_ne_zero.2 h0)) hlt) (lt_irrefl _)
        · exact heq.symm
      have hPβ : Pv S (β1 + W * β') ≤ β' := by rw [hseg', h, hceq]
      exact absurd (csInf_le' hPβ : Zβ ≤ β') (not_le.2 hR3)
  have hinv : invGG F = c := by rw [hseg]; exact invGG_GG c
  rw [hinv]
  have hlgc : lg c = e' := by
    rw [← hlgβ, ← hββ]
    rcases eq_or_ne β' 0 with h0 | h0
    · rw [hcd, h0, add_zero, add_zero, nn_lg_succ c1]
      have := nn_lg_succ 0
      rw [zero_add] at this
      exact this.symm
    · have h1 : lg c = lg β' := cpExp_add (c1 + 1) h0
      have h2 : lg (1 + β') = lg β' := cpExp_add 1 h0
      rw [h1, h2]
  rw [hlgc, ← hee]


/-! ## The reading at `Ω₁·Ω₁ + d` -/

theorem nn_sq_mem {a b : Ordinal.{0}} : Om (1 : Ordinal.{0}) * Om 1 ∈ S.CSet a b := by
  have h1 : Om (1 : Ordinal.{0}) ∈ S.CSet a b := CSet.Om_mem (CSet.one_mem a b)
  rw [← Om1_opow, ← opow_add, ← veblen_zero_apply]
  exact CSet.phi_mem (CSet.zero_mem _ _) (CSet.add_mem h1 h1)

/-- A code read at a named fixed point `F` below `Ω₁·Ω₁` is below `Ω₁·F`. -/
theorem nnHull_lt_sq {F ηx y : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) (hy : y ∈ cdHull S F) (hyl : y < Om 1 * Om 1) : y < Om 1 * F := by
  have hpv0 : Pv S (cdEta S F) = upsilon F := cdEta_pv hF.1 hX
  unfold cdHull at hy
  rw [← hpv0] at hy
  have hpv : Pv S (cdEta S F) = F := hpv0.trans hfix
  have hkey : ∀ e, HCl S (ConjT.Aη S (cdEta S F)) (Pv S (cdEta S F)) e → e < ConjT.Aη S (cdEta S F) →
      S.psi e (Om 1) < Pv S (cdEta S F) := fun e he hea =>
    psi_lt_psi_of_mem Low.InR_Om_one hea he.mem_CSet
  have hH := CSet_sub_HCl hkey y hy
  obtain ⟨q, z, r, hz, hr, hyq⟩ := linvG_HCl (g := 1) (Pv_SC S _) (Pv_lt_Om1 S _)
    (Order.one_le_iff_pos.2 nn_Om1_pos) hH
  rw [opow_one] at hr hyq
  have hsq : Om (1 : Ordinal.{0}) ^ ((1 : Ordinal.{0}) + 1) = Om 1 * Om 1 := by
    rw [opow_add, opow_one]
  rw [hsq] at hyq
  have hq0 : q = 0 := by
    by_contra hq
    have : Om (1 : Ordinal.{0}) * Om 1 ≤ y := by
      rw [hyq]; exact (le_mul_left _ (pos_iff_ne_zero.2 hq)).trans (le_self_add.trans le_self_add)
    exact absurd hyl (not_lt.2 this)
  rw [hq0, mul_zero, zero_add] at hyq
  rw [hpv] at hz
  rw [hyq]
  calc Om (1 : Ordinal.{0}) * z + r < Om 1 * z + Om 1 := (add_lt_add_iff_left _).2 hr
    _ = Om 1 * (z + 1) := (mul_add_one _ _).symm
    _ ≤ Om 1 * F := mul_le_mul_right (Order.add_one_le_of_lt hz) _

/-- **`Θ_F(Ω₁·Ω₁ + d) = F·F + d`** for `d ≤ F` at a named fixed point `F`. -/
theorem nnOtp_sq {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) : ∀ d, d ≤ F → cdOtp (cdHull S F) (Om 1 * Om 1 + d) = F * F + d := by
  have hFO : F < Om 1 := fx_fix_lt_Om1 hfix hX
  have hgap : cdOtp (cdHull S F) (Om 1 * Om 1) = F * F := by
    have hle : Om 1 * F ≤ Om 1 * Om 1 := mul_le_mul_right hFO.le _
    rw [← cdOtp_eq_of_gap _ hle (fun c hc h1 h2 => absurd (nnHull_lt_sq hF hfix hX hc h2) (not_lt.2 h1)),
      nnOtp_block hF hfix hX _ le_rfl, Ordinal.mul_div_cancel _ fx_Om1_ne, Ordinal.mul_mod,
      min_eq_left zero_le, add_zero]
  intro d
  induction d using WellFoundedLT.induction with
  | ind d IH =>
  intro hdF
  refine le_antisymm ?_ ?_
  · rw [cdOtp_eq]
    refine ciSup_le' fun c => ?_
    split_ifs with hc
    · rcases lt_or_ge c.1 (Om 1 * Om 1) with h1 | h1
      · have := cdOtp_lt_of_mem hc h1
        rw [hgap] at this
        exact (Order.add_one_le_of_lt this).trans le_self_add
      · obtain ⟨r, hr⟩ := exists_add_of_le h1
        have hrd : r < d := by
          have : Om 1 * Om 1 + r < Om 1 * Om 1 + d := by rw [← hr]; exact c.2
          exact (add_lt_add_iff_left _).1 this
        rw [hr, IH r hrd (hrd.le.trans hdF), add_assoc]
        exact add_le_add le_rfl (Order.add_one_le_of_lt hrd)
    · exact zero_le
  · refine le_of_forall_lt fun v hv => ?_
    by_cases hvF : v < F * F
    · rw [← hgap] at hvF
      exact hvF.trans_le (cdOtp_mono _ le_self_add)
    · push Not at hvF
      set r := v - F * F with hr
      have hvr : F * F + r = v := Ordinal.add_sub_cancel_of_le hvF
      have hrd : r < d := (sub_lt_of_le hvF).2 hv
      have hrF : r < F := hrd.trans_le hdF
      have hmem : Om 1 * Om 1 + r ∈ cdHull S F := by
        unfold cdHull; rw [hfix]; exact CSet.add_mem nn_sq_mem (CSet.of_lt hrF)
      have h1 := cdOtp_lt_of_mem hmem ((add_lt_add_iff_left _).2 hrd)
      rwa [IH r hrd (hrd.le.trans hdF), hvr] at h1

/-- **The code of a `Γ`-point that is not a fixed point of `GG`**: `m_F = Ω₁·Ω₁ + logend(a)`. -/
theorem nnCode_gg {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hG : IsGP F)
    (hGF : GG F ≠ F) (hX : upsilon F < Pv S ηx) :
    cdCode S F = Om 1 * Om 1 + lg (invGG F) := by
  have hname := nnName_gg hF hfix hG hGF hX
  have hFO : F < Om 1 := fx_fix_lt_Om1 hfix hX
  have hV : GG (invGG F) = F := nn_GG_inv hG
  have ha0 : invGG F ≠ 0 := by
    intro h0; rw [h0, GG_zero] at hV; exact (pos_iff_ne_zero.2 hF.1).ne hV
  have haF : invGG F < F := by
    refine lt_of_le_of_ne (by have := GG_strictMono.id_le (invGG F); rwa [hV] at this) fun e => ?_
    rw [e] at hV; exact hGF hV
  have hlt : cdExp (cdEta S F) < Om (1 + 1) := by
    rw [hname]
    have hE2 : ω ^ Om (1 + 1 : Ordinal.{0}) = Om (1 + 1) :=
      Low.opow_eq_self_of_SC (SC_Om (by rw [one_add_one_eq_two]; exact two_ne_zero))
    have h12 : Om (1 : Ordinal.{0}) < Om (1 + 1) := Om_lt_Om.2 (lt_add_one 1)
    have hm : Om 1 * Om 1 < Om (1 + 1) := Om1_mul_lt_eps hE2 h12 h12
    have hlgO : lg (invGG F) < Om (1 + 1) := (((lg_le ha0).trans_lt haF).trans hFO).trans h12
    exact (SC_Om (by rw [one_add_one_eq_two]; exact two_ne_zero)).isPrincipal hm hlgO
  have hω : ω ≤ cdExp (cdEta S F) := by
    rw [hname]
    refine le_trans ?_ le_self_add
    calc ω ≤ Om (1 : Ordinal.{0}) := (omega0_lt_Om one_ne_zero).le
      _ ≤ Om 1 * Om 1 := le_mul_left _ nn_Om1_pos
  unfold cdCode
  rw [cdCodeOf_of_lt hlt, cpOff_of_ge hω, hname]

/-- **THE NOTATION STATEMENT AT THE `Γ`-POINTS THAT ARE NOT FIXED POINTS OF `GG`**: `Θ_F(m_F) = O_X(F)` for
every term system with linear and square terms. -/
theorem nnTH_gg {X : XtSys} (hX0 : NnLin X) (hS : NnSq X) {F ηx : Ordinal.{0}} (hF : IsRestartIdx F)
    (hfix : upsilon F = F) (hG : IsGP F) (hGF : GG F ≠ F) (hX : upsilon F < Pv S ηx) :
    cdTheta S F (cdCode S F) = xtOrec X F := by
  have hV : GG (invGG F) = F := nn_GG_inv hG
  have ha0 : invGG F ≠ 0 := by
    intro h0; rw [h0, GG_zero] at hV; exact (pos_iff_ne_zero.2 hF.1).ne hV
  have haF : invGG F < F := by
    refine lt_of_le_of_ne (by have := GG_strictMono.id_le (invGG F); rwa [hV] at this) fun e => ?_
    rw [e] at hV; exact hGF hV
  have hFO : F < Om1 := by rw [Om1_eq]; exact fx_fix_lt_Om1 hfix hX
  unfold cdTheta
  rw [nnCode_gg hF hfix hG hGF hX, nnOtp_sq hF hfix hX _ ((lg_le ha0).trans haF.le),
    nnGG hX0 hS F hF hFO hG hGF]

/-- **`Cp.CpTHfix` at the `Γ`-points that are not fixed points of `GG`** (`VzOrec`, the range). -/
theorem nnTHfix_gg {l : Ordinal.{0}} (hr : CdRange S l) (hfix : upsilon l = l) (hG : IsGP l)
    (hGl : GG l ≠ l) : cdTheta S l (cdCode S l) = VzOrec l := by
  rw [← xtVz_orec]; exact nnTH_gg nnLin_vz nnSq_vz hr.1 hfix hG hGl (cp_name_L hr.2.2.1)

/-- **`famTHfix` of `xtFamW2` at the `Γ`-points that are not fixed points of `GG`.** -/
theorem nnTHfam_gg (k : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hfix : upsilon l = l) (hG : IsGP l)
    (hGl : GG l ≠ l) : cdTheta S l (cdCode S l) = xtFamW2.off k l :=
  nnTH_gg (nnLin_LL k) (nnSq_LL k) hr.1 hfix hG hGl (cp_name_L hr.2.2.1)

end Googology.Trans.PoR.InaccPsi.R2.Nn
