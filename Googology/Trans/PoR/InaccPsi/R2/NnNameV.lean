import Googology.Trans.PoR.InaccPsi.R2.NnName
import Googology.Trans.PoR.InaccPsi.R2.NnPlat
import Googology.Trans.PoR.InaccPsi.R2.FxName

/-!
# The name of a fixed point of `υ` that is not a `Γ`-point: `e(η_F) = Ω₁·γ + logend(α)`

`P(η) = ψ_{Ω₁}(Ω_ω + θ·η)`, `ι` the index of Theorem GEN, `η_F = cdEta S F` the good name of a restart `F`
(`P(η_F) = ρ_F`), `e(η) = cdExp η` the last exponent of the Cantor normal form, `W = Ω₁^{Ω₁}`.

* `nn_add_lt_block`: `ζ < η₀ + ω^e`, `δ < ω^e` give `ζ + δ < η₀ + ω^e`;
* `nn_gp_of_big` (**a name with a last exponent `≥ Ω₁·Ω₁` names a `Γ`-point**): at a fixed point `F = υ_F`
  with a name, `Ω₁·Ω₁ ≤ e(η_F)` gives `IsGP F` (below `F` the good names `ζ` have the values `υ_l`, `l < F`; then
  `ζ + Ω₁^{g+1}` is good, a multiple of `Ω₁^{g+1}`, and Theorem START puts a value of `V_{g+1}` in `(y, F]`);
* `nn_not_HCl_tail`, `nn_not_HCl_digit`: the level invariants `Nm.tinv_HCl`, `Nm.linvG_HCl` as exclusions;
* `nnName_ng` (**THE NAME OF A FIXED POINT THAT IS NOT A `Γ`-POINT**): at a restart `F` with `υ_F = F`, not a
  `Γ`-point, with a name: `e(η_F) = Ω₁·γ + logend(α)`, `γ = levG F`, `F = V_γ(α)`.  Write
  `η_F = η₀ + Ω₁^E·β` (`ω^{e+1} ∣ η₀`, `e = Ω₁·E + e'`, `β = ω^{e'}·k`): `E ≠ 0` (else `F ≤ e < F` by
  `Fx.fxExp_fix` and `Nm.linv0_HCl` at the good name), `E < Ω₁` (else `nn_gp_of_big`); `η₀` is good (the prefix);
  START's hypothesis at `η₀`, `E < P(η₀ + Ω₁^E)` and `β - 1 < Zu(η₀ + Ω₁^E, Ω₁^E)` hold (otherwise a window plateau
  `Nn.nnWPlat` makes `η_F` bad: `Nm.tinv_HCl` and `Nm.linvG_HCl` exclude hull members from the window); then
  START and SEG give `F = V_E(c₁ + 1 + (β - 1))` of exact level `E`, `logend = e'`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Nn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Br Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Fx

variable {S : InaccSeq.{0}}

theorem nn_add_lt_block {η0 e ζ δ : Ordinal.{0}} (hζ : ζ < η0 + ω ^ e) (hδ : δ < ω ^ e) :
    ζ + δ < η0 + ω ^ e := by
  rcases le_or_gt ζ η0 with h | h
  · exact (add_le_add h le_rfl).trans_lt ((add_lt_add_iff_left η0).2 hδ)
  · obtain ⟨x, rfl⟩ := exists_add_of_le h.le
    have hx : x < ω ^ e := (add_lt_add_iff_left _).1 hζ
    rw [add_assoc]
    exact (add_lt_add_iff_left _).2 (isPrincipal_add_omega0_opow e hx hδ)

theorem nn_Om1_pos : (0 : Ordinal.{0}) < Om 1 := zero_lt_one.trans one_lt_Om1

theorem nn_W_ne : W ≠ 0 := W_pos.ne'

theorem nn_pow_lt_W {δ : Ordinal.{0}} (hδ : δ < Om 1) : Om (1 : Ordinal.{0}) ^ δ < W :=
  Om1_pow_lt_iff.2 hδ

theorem nn_opow_lt_Om1 {x : Ordinal.{0}} (hx : x < Om 1) : ω ^ x < Om 1 := by
  calc ω ^ x < ω ^ Om (1 : Ordinal.{0}) := (opow_lt_opow_iff_right one_lt_omega0).2 hx
    _ = Om 1 := Om1_opow

theorem nn_mul_lt_Om1 {x y : Ordinal.{0}} (hx : x < Om 1) (hy : y < Om 1) : x * y < Om 1 := by
  rw [← Om1_eq] at hx hy ⊢; exact Om1_mul_lt hx hy

/-- `ω^x ≤ U` absorbs every `r < ω^x`: `r + U = U`. -/
theorem nn_absorb {r x U : Ordinal.{0}} (hr : r < ω ^ x) (hU : ω ^ x ≤ U) : r + U = U :=
  add_of_omega0_opow_le hr hU

/-! ## A last exponent `≥ Ω₁·Ω₁` names a `Γ`-point -/

/-- **A name with a last exponent `≥ Ω₁·Ω₁` names a `Γ`-point.** -/
theorem nn_gp_of_big {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) (hbig : Om 1 * Om 1 ≤ cdExp (cdEta S F)) : IsGP F := by
  set η := cdEta S F with hηd
  obtain ⟨-, hι, -, hP⟩ := cdEta_pv_spec (S := S) hF.1 hX
  rw [hfix] at hP
  obtain ⟨hE, -, hww, hlim, -⟩ := nn_fix_facts hF hfix
  have hF0 : 0 < F := hE.pos
  have hη0 : η ≠ 0 := by
    intro h0
    rw [← hηd] at hι
    rw [h0, iota_zero] at hι
    have : (1 : Ordinal.{0}) < F :=
      lt_of_le_of_lt (Order.one_le_iff_pos.2 (mul_pos omega0_pos omega0_pos)) hww
    exact this.ne hι
  obtain ⟨η', hdec, -⟩ := cdExp_decomp hη0
  set e := cdExp η with he
  refine ⟨hF0, fun g hgF => le_antisymm ?_ (VG_id_le g F)⟩
  rw [(VG_normal g).apply_of_isSuccLimit hlim]
  refine ciSup_le' fun y => ?_
  -- a fixed point of `V_g` in `(y, F]`
  set y' := max y.1 g with hy'
  have hy'F : y' < F := max_lt y.2 hgF
  set l := y' + 1 with hl
  have hlF : l < F := hlim.add_one_lt hy'F
  have hlι : l < iota S η := by rw [← hηd] at hι; rw [hι]; exact hlF
  obtain ⟨ζ, hζη, hζg, hζι⟩ := cd_good_name (Order.one_le_iff_pos.2 (lt_of_le_of_lt zero_le (lt_add_one y')))
    hlι
  have hPζ : Pv S ζ = upsilon l := by
    have h := ups_iota S ζ
    rw [hζι] at h; exact h.symm
  have hy'ζ : y' < Pv S ζ := by rw [hPζ]; exact (lt_add_one y').trans_le upsilon_normal.strictMono.le_apply
  have hgζ : g < Pv S ζ := (le_max_right _ _).trans_lt hy'ζ
  set U := Om (1 : Ordinal.{0}) ^ (g + 1) with hU
  have hUe : U = ω ^ (Om 1 * (g + 1)) := Om1_pow _
  set ζ1 := ζ + U with hζ1
  have hd1 : U ∣ ζ1 := by
    have hU0 : U ≠ 0 := (Om1_pow_pos _).ne'
    have hab : ζ % U + U = U := nn_absorb (x := Om 1 * (g + 1)) (by rw [← hUe]; exact mod_lt ζ hU0)
      hUe.ge
    refine ⟨ζ / U + 1, ?_⟩
    rw [hζ1, mul_add_one]
    conv_lhs => rw [← div_add_mod ζ U]
    rw [add_assoc, hab]
  have hg1 : g + 1 < Pv S ζ1 := (Pv_SC S ζ1).add_one_lt (hgζ.trans_le (Pv_mono le_self_add))
  have hgood1 : Bt.Good S ζ1 := good_add hζg (mem_Om1_pow hg1)
  have hC : ∀ δ < g + 1, δ < nxt (VG δ) (Pv S ζ1) := fun δ hδ =>
    ((Order.lt_add_one_iff.1 hδ).trans_lt (hg1.trans' (lt_add_one g))).trans
      (lt_nxt (VG_normal δ) (VG_at_zero δ) _)
  have hst := start_all S (g + 1) ζ1 hgood1 hd1 hC
  set s := Pv S (ζ1 + U) with hs
  have hsfix : VG g s = s := by
    have : s ∈ range (VG (g + 1)) := by rw [hst]; exact nxt_mem _ _
    exact mem_range_VG_succ.1 this
  have hys : y.1 < s := by
    calc y.1 ≤ y' := le_max_left _ _
      _ < Pv S ζ := hy'ζ
      _ ≤ Pv S ζ1 := Pv_mono le_self_add
      _ < s := by rw [hst]; exact lt_nxt (VG_normal _) (VG_at_zero _) _
  have hsF : s ≤ F := by
    have hUU : U + U < ω ^ e := by
      have h2 : U + U < ω ^ (Om 1 * (g + 1) + 1) := by
        have e1 : U + U = ω ^ (Om 1 * (g + 1)) * 2 := by
          rw [← hUe, ← one_add_one_eq_two, mul_add_one, mul_one]
        have e2 : ω ^ (Om 1 * (g + 1) + 1) = ω ^ (Om 1 * (g + 1)) * ω := by rw [opow_add, opow_one]
        rw [e1, e2]
        exact (mul_lt_mul_iff_right₀ (opow_pos _ omega0_pos)).2 (natCast_lt_omega0 2)
      refine h2.trans_le (opow_le_opow_right omega0_pos ?_)
      have hg2 : g + 1 + 1 ≤ Om 1 := by
        have hgO : g < Om 1 := hgF.trans (fx_fix_lt_Om1 hfix hX)
        have hl1 : IsSuccLimit (Om (1 : Ordinal.{0})) := fx_Om1_lim
        exact (hl1.add_one_lt (hl1.add_one_lt hgO)).le
      calc Om 1 * (g + 1) + 1 ≤ Om 1 * (g + 1) + Om 1 :=
            add_le_add le_rfl (Order.one_le_iff_pos.2 nn_Om1_pos)
        _ = Om 1 * (g + 1 + 1) := (mul_add_one _ _).symm
        _ ≤ Om 1 * Om 1 := mul_le_mul_right hg2 _
        _ ≤ e := hbig
    have hlt : ζ + (U + U) < η := by rw [hdec]; exact nn_add_lt_block (hdec ▸ hζη) hUU
    rw [hs, hζ1, add_assoc, ← hP]
    exact Pv_mono hlt.le
  refine le_of_lt ?_
  calc VG g y.1 < VG g s := VG_strictMono g hys
    _ = s := hsfix
    _ ≤ F := hsF

/-! ## The level invariants as exclusions -/

/-- An ordinal whose remainder modulo `W` is at least `Ω₁^D`, `D ≥ Z`, is not in `HCl(a, Z)`. -/
theorem nn_not_HCl_tail {a Z D q0 r x : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1) (hZD : Z ≤ D)
    (hx : x = W * q0 + r) (hr : r < W) (hrD : Om (1 : Ordinal.{0}) ^ D ≤ r) : ¬ HCl S a Z x := by
  intro h
  obtain ⟨q, d, δ, hδ, hd, hxe⟩ := tinv_HCl hZ hZ1 h
  have hdW : d < W := hd.trans (nn_pow_lt_W (hδ.trans hZ1))
  obtain ⟨-, hdr⟩ := div_unique nn_W_ne hdW hr (hxe.symm.trans hx)
  rw [hdr] at hd
  exact absurd (hrD.trans_lt hd) (not_lt.2 (Om1_pow_le_iff.2 (hδ.le.trans hZD)))

theorem nn_digit_lt {E z r : Ordinal.{0}} (hz : z < Om 1) (hr : r < Om (1 : Ordinal.{0}) ^ E) :
    Om (1 : Ordinal.{0}) ^ E * z + r < Om 1 ^ (E + 1) := by
  calc Om (1 : Ordinal.{0}) ^ E * z + r < Om 1 ^ E * z + Om 1 ^ E := (add_lt_add_iff_left _).2 hr
    _ = Om 1 ^ E * (z + 1) := (mul_add_one _ _).symm
    _ ≤ Om 1 ^ E * Om 1 := mul_le_mul_right (Order.add_one_le_of_lt hz) _
    _ = Om 1 ^ (E + 1) := (opow_succ _ _).symm

/-- An ordinal whose `Ω₁^E`-digit is at least `Z` is not in `HCl(a, Z)`. -/
theorem nn_not_HCl_digit {a Z E q0 z0 r0 x : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1) (hE : E ≤ Om 1)
    (hx : x = Om (1 : Ordinal.{0}) ^ (E + 1) * q0 + Om 1 ^ E * z0 + r0) (hz0 : z0 < Om 1)
    (hr0 : r0 < Om (1 : Ordinal.{0}) ^ E) (hZz : Z ≤ z0) : ¬ HCl S a Z x := by
  intro h
  obtain ⟨q, z, r, hz, hr, hxe⟩ := linvG_HCl hZ hZ1 hE h
  have hzΩ : z < Om 1 := hz.trans hZ1
  have hU : Om (1 : Ordinal.{0}) ^ (E + 1) ≠ 0 := (Om1_pow_pos _).ne'
  have e1 : Om (1 : Ordinal.{0}) ^ (E + 1) * q + (Om 1 ^ E * z + r) =
      Om 1 ^ (E + 1) * q0 + (Om 1 ^ E * z0 + r0) := by
    rw [← add_assoc, ← add_assoc, ← hxe, ← hx]
  obtain ⟨-, h2⟩ := div_unique hU (nn_digit_lt hzΩ hr) (nn_digit_lt hz0 hr0) e1
  obtain ⟨h3, -⟩ := div_unique (Om1_pow_pos E).ne' hr hr0 h2
  rw [h3] at hz
  exact absurd hz (not_lt.2 hZz)


/-! ## The name of a fixed point that is not a `Γ`-point -/

/-- **A name with a last exponent `< Ω₁·Ω₁`**: the fixed point is not a `Γ`-point and
`e(η_F) = Ω₁·γ + logend(α)`, `γ = levG F`, `F = V_γ(α)`. -/
theorem nn_name_small {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) (hsmall : cdExp (cdEta S F) < Om 1 * Om 1) :
    ¬ IsGP F ∧ cdExp (cdEta S F) = Om 1 * levG F + lg (invG (levG F) F) := by
  set η := cdEta S F with hηd
  obtain ⟨hg, hι, -, hP⟩ := cdEta_pv_spec (S := S) hF.1 hX
  rw [← hηd] at hg hι hP
  rw [hfix] at hP
  obtain ⟨hE, hp, hww, hlim, hU⟩ := nn_fix_facts hF hfix
  have hF0 : 0 < F := hE.pos
  have hFO : F < Om 1 := fx_fix_lt_Om1 hfix hX
  have hη0 : η ≠ 0 := by
    intro h0
    rw [h0, iota_zero] at hι
    have : (1 : Ordinal.{0}) < F :=
      lt_of_le_of_lt (Order.one_le_iff_pos.2 (mul_pos omega0_pos omega0_pos)) hww
    exact this.ne hι
  set e := cdExp η with he
  have hde : ω ^ e ∣ η := cdExp_dvd hη0
  -- `η = η₀ + t`, `ω^{e+1} ∣ η₀`, `t = ω^e·k`, `1 ≤ k < ω`
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
  -- `e = Ω₁·E + e'`
  set E := e / Om 1 with hEd
  set e' := e % Om 1 with he'd
  have hee : e = Om 1 * E + e' := (div_add_mod e (Om 1)).symm
  have he'O : e' < Om 1 := mod_lt e fx_Om1_ne
  -- `E ≠ 0`
  have hE0 : E ≠ 0 := by
    intro hE0
    have heO : e < Om 1 := by rw [hee, hE0, mul_zero, zero_add]; exact he'O
    have hFe : F ≤ e := fxExp_fix hF hfix hX
    have hH := nnGood_HCl hg
    rw [hP] at hH
    obtain ⟨q, z, hz, hqz⟩ := linv0_HCl (hP ▸ Pv_SC S η) (hP ▸ Pv_lt_Om1 S η) hH
    have htO : t < Om 1 := by
      rw [hk]; exact nn_mul_lt_Om1 (nn_opow_lt_Om1 heO) (hkω.trans (omega0_lt_Om one_ne_zero))
    have hsum : η0 % Om 1 + t < Om 1 := fx_Om1_prin (mod_lt η0 fx_Om1_ne) htO
    have e2 : η = Om 1 * (η0 / Om 1) + (η0 % Om 1 + t) := by
      rw [hηt]; conv_lhs => rw [← div_add_mod η0 (Om 1)]
      rw [add_assoc]
    obtain ⟨-, hzz⟩ := div_unique fx_Om1_ne (hz.trans hFO) hsum (hqz.symm.trans e2)
    have hte : e ≤ t := by
      rw [hk]
      exact (right_le_opow e one_lt_omega0).trans (le_mul_left _ (pos_iff_ne_zero.2 hk0))
    have : F ≤ z := hFe.trans (hte.trans (hzz ▸ le_add_self))
    exact absurd hz (not_lt.2 this)
  -- `E < Ω₁`
  have hEO : E < Om 1 := by
    by_contra hge
    push Not at hge
    have hbig : Om 1 * Om 1 ≤ cdExp (cdEta S F) := by
      rw [← hηd, ← he, hee]; exact (mul_le_mul_right hge _).trans le_self_add
    exact absurd hsmall (not_lt.2 hbig)
  -- `t = Ω₁^E·β`, `β = ω^{e'}·k`
  set β := ω ^ e' * k with hβd
  have htβ : t = Om (1 : Ordinal.{0}) ^ E * β := by
    rw [hk, hee, opow_add, ← Om1_pow, mul_assoc]
  have hβ0 : β ≠ 0 := mul_ne_zero (nn_opow_ne _) hk0
  have hβO : β < Om 1 := nn_mul_lt_Om1 (nn_opow_lt_Om1 he'O) (hkω.trans (omega0_lt_Om one_ne_zero))
  have hlgβ : lg β = e' := by
    obtain ⟨m, rfl⟩ := lt_omega0.1 hkω
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by
      have : m ≠ 0 := fun h => hk0 (by rw [h]; rfl)
      omega⟩
    have := cpExp_mul_succ e' (m' : Ordinal.{0})
    rw [hβd, Nat.cast_succ]; exact this
  have hEd' : Om (1 : Ordinal.{0}) ^ E ∣ η0 := by
    rw [Om1_pow]
    exact (opow_dvd_opow ω ((le_self_add.trans_eq hee.symm).trans le_self_add)).trans hd0
  have hWO : Om (1 : Ordinal.{0}) ^ (E + 1) ≤ W := Om1_pow_le_iff.2 ((fx_Om1_lim).add_one_lt hEO).le
  have htW : t < W := by
    rw [htβ]
    calc Om (1 : Ordinal.{0}) ^ E * β < Om 1 ^ E * Om 1 := (mul_lt_mul_iff_right₀ (Om1_pow_pos _)).2 hβO
      _ = Om 1 ^ (E + 1) := (opow_succ _ _).symm
      _ ≤ W := hWO
  -- (R0) `η₀` is good
  have hg0 : Bt.Good S η0 := nnPrefix_good hd0 ht1 (hηt ▸ hg)
  -- the representation modulo `W`
  have hmodW : ∀ y'', y'' < W → ∀ c, c < W → η0 + c + y'' = W * (η0 / W) + (η0 % W + c + y'') ∧
      η0 % W + c + y'' < W := by
    intro y'' hy'' c hc
    refine ⟨?_, (Om1_pow_principal _) ((Om1_pow_principal _) (mod_lt η0 nn_W_ne) hc) hy''⟩
    conv_lhs => rw [← div_add_mod η0 W]
    rw [add_assoc, add_assoc, add_assoc]
  -- (R1) START's hypothesis at `η₀`
  have hC : ∀ δ < E, δ < nxt (VG δ) (Pv S η0) := by
    by_contra hC
    push Not at hC
    set D := {δ | δ < E ∧ nxt (VG δ) (Pv S η0) ≤ δ} with hD
    have hne : D.Nonempty := hC
    obtain ⟨hδE, hδle⟩ := csInf_mem hne
    set δ0 := sInf D with hδ0
    have hmin : ∀ δ < δ0, δ < nxt (VG δ) (Pv S η0) := fun δ hδ => by
      have := notMem_of_lt_csInf' (s := D) hδ
      by_contra hle
      push Not at hle
      exact this ⟨hδ.trans hδE, hle⟩
    have hdδ : Om (1 : Ordinal.{0}) ^ δ0 ∣ η0 := (opow_dvd_opow (Om 1) hδE.le).trans hEd'
    have hst := start_all S δ0 η0 hg0 hdδ hmin
    set β0 := η0 + Om (1 : Ordinal.{0}) ^ δ0 with hβ0d
    have hPβ0 : Pv S β0 ≤ δ0 := by rw [hβ0d, hst]; exact hδle
    have hab : Om (1 : Ordinal.{0}) ^ δ0 + t = t := by
      refine nn_absorb (x := Om 1 * E) ?_ ?_
      · rw [← Om1_pow]; exact Om1_pow_lt_iff.2 hδE
      · rw [← Om1_pow, htβ]; exact le_mul_of_one_le_right' (Order.one_le_iff_ne_zero.2 hβ0)
    have hηβ0 : η = β0 + t := by rw [hηt, hβ0d, add_assoc, hab]
    have hw : ∀ y'' ≤ t, ¬ HCl S (ConjT.Aη S β0) (Pv S β0) (β0 + y'') := by
      intro y'' hy''
      obtain ⟨hrep, hlt⟩ := hmodW y'' (hy''.trans_lt htW) _ (nn_pow_lt_W (hδE.trans hEO))
      exact nn_not_HCl_tail (Pv_SC S β0) (Pv_lt_Om1 S β0) hPβ0 hrep hlt
        (le_add_self.trans le_self_add)
    have := (nnWPlat hw).2
    rw [← hηβ0] at this
    exact this hg
  -- START at `E`
  have hst := start_all S E η0 hg0 hEd' hC
  obtain ⟨c1, hc1⟩ := nn_nxt_succ (VG_normal E) (VG_at_zero E) (Pv S η0)
  rw [hc1] at hst
  set β1 := η0 + Om (1 : Ordinal.{0}) ^ E with hβ1d
  set β' := β - 1 with hβ'd
  have hββ : 1 + β' = β := Ordinal.add_sub_cancel_of_le (Order.one_le_iff_ne_zero.2 hβ0)
  have hηβ1 : η = β1 + Om (1 : Ordinal.{0}) ^ E * β' := by
    rw [hηt, htβ, ← hββ, mul_add, mul_one, hβ1d, add_assoc]
  have hβ'O : β' < Om 1 := (Ordinal.sub_le_self _ _).trans_lt hβO
  have htW' : Om (1 : Ordinal.{0}) ^ E * β' < W := by
    refine lt_of_le_of_lt ?_ htW
    rw [htβ, ← hββ, mul_add, mul_one]; exact le_add_self
  -- (R2) `E < P(β₁)`
  have hR2 : E < Pv S β1 := by
    by_contra hle
    push Not at hle
    have hw : ∀ y'' ≤ Om (1 : Ordinal.{0}) ^ E * β', ¬ HCl S (ConjT.Aη S β1) (Pv S β1) (β1 + y'') := by
      intro y'' hy''
      obtain ⟨hrep, hlt⟩ := hmodW y'' (hy''.trans_lt htW') _ (nn_pow_lt_W hEO)
      exact nn_not_HCl_tail (Pv_SC S β1) (Pv_lt_Om1 S β1) hle hrep hlt (le_add_self.trans le_self_add)
    have := (nnWPlat hw).2
    rw [← hηβ1] at this
    exact this hg
  have hg1 : Bt.Good S β1 := good_add hg0 (mem_Om1_pow hR2)
  have hd1 : Om (1 : Ordinal.{0}) ^ E ∣ β1 := dvd_add hEd' dvd_rfl
  -- (R3) `β' < Zu(β₁, Ω₁^E)`
  set Zβ := Zu S β1 (Om 1 ^ E) with hZβ
  have hR3 : β' < Zβ := by
    by_contra hle
    push Not at hle
    set β2 := β1 + Om (1 : Ordinal.{0}) ^ E * Zβ with hβ2d
    have hPβ2 : Pv S β2 = Zβ := Zu_fix S β1 _
    have hsplit : Zβ + (β' - Zβ) = β' := Ordinal.add_sub_cancel_of_le hle
    have hηβ2 : η = β2 + Om (1 : Ordinal.{0}) ^ E * (β' - Zβ) := by
      rw [hηβ1, hβ2d, add_assoc β1, ← mul_add, hsplit]
    -- the digit of `η₀` at `Ω₁^E`
    have hUE : Om (1 : Ordinal.{0}) ^ (E + 1) ≠ 0 := (Om1_pow_pos _).ne'
    set r0 := η0 % Om (1 : Ordinal.{0}) ^ (E + 1) with hr0d
    have hr0dv : Om (1 : Ordinal.{0}) ^ E ∣ r0 := by
      have h1 : Om (1 : Ordinal.{0}) ^ E ∣ Om 1 ^ (E + 1) * (η0 / Om 1 ^ (E + 1)) :=
        (opow_dvd_opow (Om 1) le_self_add).trans (dvd_mul_right _ _)
      have h2 : Om (1 : Ordinal.{0}) ^ E ∣ Om 1 ^ (E + 1) * (η0 / Om 1 ^ (E + 1)) + r0 := by
        rw [hr0d, div_add_mod]; exact hEd'
      exact (dvd_add_iff h1).1 h2
    obtain ⟨b0, hb0⟩ := hr0dv
    have hb0O : b0 < Om 1 := by
      have : Om (1 : Ordinal.{0}) ^ E * b0 < Om 1 ^ E * Om 1 := by
        rw [← hb0, ← opow_succ]; exact mod_lt η0 hUE
      exact (mul_lt_mul_iff_right₀ (Om1_pow_pos _)).1 this
    have hw : ∀ y'' ≤ Om (1 : Ordinal.{0}) ^ E * (β' - Zβ),
        ¬ HCl S (ConjT.Aη S β2) (Pv S β2) (β2 + y'') := by
      intro y'' hy''
      have hm : y'' / Om (1 : Ordinal.{0}) ^ E ≤ β' - Zβ := Ordinal.div_le_of_le_mul hy''
      have hmO : y'' / Om (1 : Ordinal.{0}) ^ E < Om 1 := hm.trans_lt ((Ordinal.sub_le_self _ _).trans_lt hβ'O)
      have hZO : Zβ < Om 1 := Zu_lt_Om1 S _ _
      have hz0O : b0 + 1 + Zβ + y'' / Om (1 : Ordinal.{0}) ^ E < Om 1 :=
        fx_Om1_prin (fx_Om1_prin (fx_Om1_prin hb0O one_lt_Om1) hZO) hmO
      have hrep : β2 + y'' = Om (1 : Ordinal.{0}) ^ (E + 1) * (η0 / Om 1 ^ (E + 1)) +
          Om 1 ^ E * (b0 + 1 + Zβ + y'' / Om 1 ^ E) + y'' % Om 1 ^ E := by
        rw [hβ2d, hβ1d]
        conv_lhs => rw [← div_add_mod η0 (Om (1 : Ordinal.{0}) ^ (E + 1)), ← div_add_mod y'' (Om (1 : Ordinal.{0}) ^ E)]
        rw [← hr0d, hb0]
        simp only [mul_add, mul_one, add_assoc]
      refine nn_not_HCl_digit (Pv_SC S β2) (Pv_lt_Om1 S β2) (le_of_lt hEO) hrep hz0O
        (mod_lt _ (Om1_pow_pos E).ne') ?_
      rw [hPβ2]; exact le_add_self.trans le_self_add
    have := (nnWPlat hw).2
    rw [← hηβ2] at this
    exact this hg
  -- SEG: `F = V_E(c₁ + 1 + β')`
  have hseg := seg_all S E β1 (c1 + 1) hg1 hd1 hR2 hst β' hR3.le
  rw [← hηβ1, hP] at hseg
  set c := c1 + 1 + β' with hcd
  have hc0 : c ≠ 0 := (lt_of_lt_of_le (add_pos_of_right zero_lt_one c1) le_self_add).ne'
  have hna : VG E c ≠ c := by
    intro h
    have hu : upsilon c = c := ups_fix_of_VG hE0 ⟨c, h⟩
    have hp' := (cp_fix_facts (ri_of_fp (pos_iff_ne_zero.2 hc0) hu) hu).2.1
    rcases eq_or_ne β' 0 with h0 | h0
    · rw [hcd, h0, add_zero] at hu
      exact nn_succ_not_fix c1 hu
    · have hceq : c = β' := by
        rcases lt_or_eq_of_le (le_add_self : β' ≤ c1 + 1 + β') with hlt | heq
        · exact absurd (hp' (lt_add_of_pos_right (c1 + 1) (pos_iff_ne_zero.2 h0)) hlt) (lt_irrefl _)
        · exact heq.symm
      have hPβ : Pv S (β1 + Om 1 ^ E * β') ≤ β' := by
        rw [seg_all S E β1 (c1 + 1) hg1 hd1 hR2 hst β' hR3.le, ← hcd, h, hceq]
      exact absurd (csInf_le' hPβ : Zβ ≤ β') (not_le.2 hR3)
  have hEF : E < VG E c := by
    rw [← hseg]
    exact hR2.trans_le (by rw [← hP]; exact Pv_mono (by rw [hηβ1]; exact le_self_add))
  obtain ⟨-, -, hGc, hlev, hinv⟩ := nn_V_exact hE0 hc0 hna hEF
  rw [← hseg] at hlev hinv hGc
  refine ⟨hGc, ?_⟩
  rw [hlev, hinv]
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

/-- **THE NAME OF A FIXED POINT THAT IS NOT A `Γ`-POINT**: `e(η_F) = Ω₁·γ + logend(α)`, `γ = levG F`,
`F = V_γ(α)`. -/
theorem nnName_ng {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hG : ¬ IsGP F)
    (hX : upsilon F < Pv S ηx) :
    cdExp (cdEta S F) = Om 1 * levG F + lg (invG (levG F) F) := by
  by_cases hs : cdExp (cdEta S F) < Om 1 * Om 1
  · exact (nn_name_small hF hfix hX hs).2
  · exact absurd (nn_gp_of_big hF hfix hX (not_lt.1 hs)) hG

/-- **The name of a `Γ`-point has a last exponent `≥ Ω₁·Ω₁`.** -/
theorem nn_gp_big {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hG : IsGP F)
    (hX : upsilon F < Pv S ηx) : Om 1 * Om 1 ≤ cdExp (cdEta S F) := by
  by_contra hs
  exact (nn_name_small hF hfix hX (not_le.1 hs)).1 hG

end Googology.Trans.PoR.InaccPsi.R2.Nn
