import Googology.Trans.PoR.InaccPsi.R2.SlReal

/-!
# The linear renaming `a ↦ ρ_μ` of the offsets: realizers at `m*` and `L(n+1)` past `υ_{a+a}`, up to `υ_{a·ω}`

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.

`a = m*` or `a = L(n+1)`: a named point with `ι(η_a) = a = P(η_a)`, `ω^{Ω₁} ∣ η_a`.  The inner restarts below
`υ_{a·ω}` are `a + g`, `g = a·k + e` (`k < ω`, `e < a`, `ω² ∣ g`), with the name `η_a + g`, the short code
`m = -1 + e(g)` (`e(g) = e(e)` for `e > 0`, `e(a·k) = a`), and the reach `υ_{a+g+ω+1} + m`.  The realizer
renames the base point inside the offsets: `f(a·k + e) = ρ_μ·k + e` (the base change `a ↦ ρ_μ = υ_μ`), so the
image restart `μ + f(g)` has the name `η_μ + f(g)`, the code `m` (for `e > 0`) or `ρ_μ` (for `e = 0`, the image
of the code `a`), and EQ holds: `r(μ + f(g)) = υ_{μ+f(g)+ω+1} + (image of m)`.

* `slLin ρ a d = ρ·(d/a) + d mod a` (**the linear renaming**) and its laws: `slLin_zero`, `slLin_res`
  (`f(ω²·q + r) = f(ω²·q) + r`), `slLin_dvd`, `slLin_lt` (strictly increasing on the offsets with remainders
  `< ρ`), `slLin_bd` (`< ρ·ω` below `a·ω`), `slOff_lin` (**`SlOff`**);
* `slGood` (`η + y` is good for `y < P(η)·ω`), `slCode_shift` (**`η_{ι(η)+g} = η + g`, `m_{ι(η)+g} = -1+e(g)`
  for `0 < g < P(η)·ω`**), `slExp_lin` (`e(x·k + e) = e(e)` for `0 < e < x`, `x` an `ε`-number),
  `slExp_mul` (`e(x·k) = x` for `0 < k < ω`), `slUps_inj` (`υ_{λ+h} + υ_λ·j + p` determines `h, j, p`);
* `SlSupW S k` (**the supply for the renaming**: `υ_{μ+ρ_μ·ω} ≤ r(μ)` at every Range restart with the code
  `G_{k+1} + 1`), `slSupW_of_strict` (**LC-STRICT at `k` (`Ls.LsStrictCode`) gives it**), `slSupW_sup`
  (it gives `Ls.LsSupCode`);
* `slReal_named` (**`LrReal S a υ_{a+a·ω}`** at a named point, from the family below `a`, `SlSupW`, UPPER at the
  inner restarts, LOWER at their images, `CxStdPairTop`), `slReal_M`, `slReal_L` (**at `m*` and at every
  `L(n+1)`, given `L(ω) ≤ ν_C`**).

No new axiom.  New definitions: `slLin`, `SlSupW`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Sl

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr

variable {S : InaccSeq.{0}}

/-! ## The linear renaming -/

/-- **The linear renaming** `a·k + e ↦ ρ·k + e` (`e < a`). -/
noncomputable def slLin (ρ a d : Ordinal.{0}) : Ordinal.{0} := ρ * (d / a) + d % a

theorem slLin_zero (ρ a : Ordinal.{0}) : slLin ρ a 0 = 0 := by
  simp [slLin]

theorem slMod_dvd {a x : Ordinal.{0}} (ha : ω ^ 2 ∣ a) (hx : ω ^ 2 ∣ x) : ω ^ 2 ∣ x % a := by
  have h := Ordinal.div_add_mod x a
  rw [← h] at hx
  exact (dvd_add_iff (dvd_mul_of_dvd_left ha _)).1 hx

theorem slLin_res {ρ a : Ordinal.{0}} (ha0 : a ≠ 0) (ha : ω ^ 2 ∣ a) (q r : Ordinal.{0})
    (hr : r < ω ^ 2) : slLin ρ a (ω ^ 2 * q + r) = slLin ρ a (ω ^ 2 * q) + r := by
  set x := ω ^ 2 * q with hx
  have hxd : ω ^ 2 ∣ x % a := slMod_dvd ha (dvd_mul_right _ q)
  have hxa : x % a + r < a :=
    (lr_addL (a := x % a) hr).trans_le (lr_dvd_add_le hxd ha (Ordinal.mod_lt x ha0))
  have e1 : x + r = a * (x / a) + (x % a + r) := by rw [← add_assoc, Ordinal.div_add_mod]
  have hdiv : (x + r) / a = x / a := by
    rw [e1, Ordinal.mul_add_div _ ha0, Ordinal.div_eq_zero_of_lt hxa, add_zero]
  have hmod : (x + r) % a = x % a + r := by
    rw [e1, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hxa]
  unfold slLin
  rw [hdiv, hmod, add_assoc]

theorem slLin_dvd {ρ a : Ordinal.{0}} (hρ : ω ^ 2 ∣ ρ) (ha : ω ^ 2 ∣ a) (q : Ordinal.{0}) :
    ω ^ 2 ∣ slLin ρ a (ω ^ 2 * q) :=
  dvd_add (dvd_mul_of_dvd_left hρ _) (slMod_dvd ha (dvd_mul_right _ q))

/-- `slLin` is strictly increasing on the offsets whose remainder is `< ρ`. -/
theorem slLin_lt {ρ a d d' : Ordinal.{0}} (ha0 : a ≠ 0) (hdd : d < d') (hr : d % a < ρ) :
    slLin ρ a d < slLin ρ a d' := by
  unfold slLin
  have hk : d / a ≤ d' / a := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 := Ordinal.lt_mul_succ_div d' ha0
    have h2 : a * succ (d' / a) ≤ a * (d / a) := mul_le_mul_right (Order.succ_le_of_lt hlt) a
    exact absurd ((h1.trans_le (h2.trans (Ordinal.mul_div_le d a))).trans hdd) (lt_irrefl _)
  rcases hk.lt_or_eq with hk | hk
  · calc ρ * (d / a) + d % a < ρ * (d / a) + ρ := lr_addL (a := ρ * (d / a)) hr
      _ = ρ * (d / a + 1) := (mul_add_one _ _).symm
      _ ≤ ρ * (d' / a) := mul_le_mul_right (Order.add_one_le_of_lt hk) ρ
      _ ≤ ρ * (d' / a) + d' % a := le_self_add
  · rw [hk]
    refine lr_addL (a := ρ * (d' / a)) ?_
    have e1 : a * (d' / a) + d % a = d := by rw [← hk]; exact Ordinal.div_add_mod d a
    have e2 : a * (d' / a) + d' % a = d' := Ordinal.div_add_mod d' a
    have h3 : a * (d' / a) + d % a < a * (d' / a) + d' % a := by rw [e1, e2]; exact hdd
    exact (add_lt_add_iff_left _).1 h3

theorem slLin_bd {ρ a d : Ordinal.{0}} (ha0 : a ≠ 0) (hd : d < a * ω) (hr : d % a < ρ) :
    slLin ρ a d < ρ * ω := by
  unfold slLin
  have hk : d / a < ω := (Ordinal.lt_mul_iff_div_lt ha0).1 hd
  calc ρ * (d / a) + d % a < ρ * (d / a) + ρ := lr_addL (a := ρ * (d / a)) hr
    _ = ρ * (d / a + 1) := (mul_add_one _ _).symm
    _ ≤ ρ * ω := mul_le_mul_right (Order.add_one_le_of_lt hk) ρ

/-- **The linear renaming is an offset map** on a set of offsets below `a·ω` with remainders `< ρ`. -/
theorem slOff_lin {ρ a : Ordinal.{0}} (ha0 : a ≠ 0) (ha : ω ^ 2 ∣ a) (hρ : ω ^ 2 ∣ ρ) (hρ0 : 0 < ρ)
    {Os : Finset Ordinal.{0}} (hOs : ∀ d ∈ Os, d < a * ω ∧ d % a < ρ) :
    SlOff (slLin ρ a) Os (ρ * ω) := by
  refine ⟨slLin_zero ρ a, slLin_res ha0 ha, slLin_dvd hρ ha, ?_, fun d hd => slLin_bd ha0 (hOs d hd).1
    (hOs d hd).2⟩
  have hrem : ∀ d ∈ insert 0 Os, d % a < ρ := by
    intro d hd
    rcases Finset.mem_insert.1 hd with rfl | hd
    · simpa using hρ0
    · exact (hOs d hd).2
  intro d hd d' _ hdd
  exact slLin_lt ha0 hdd (hrem d (Finset.mem_coe.1 hd))

/-! ## Names, codes and exponents -/

theorem slPv_E (η : Ordinal.{0}) : InE (Nm.Pv S η) := Low.opow_eq_self_of_SC (Nm.Pv_SC S η)

/-- `η + y` is good for every `y < P(η)·ω`. -/
theorem slGood {η y : Ordinal.{0}} (hg : Bt.Good S η) (hy : y < Nm.Pv S η * ω) : Bt.Good S (η + y) := by
  refine Rz.rz_good_shift hg ?_
  by_cases hyP : y < Nm.Pv S η
  · exact hyP.trans_le (Nm.Pv_mono le_self_add)
  · have h1 : 1 ≤ y := Order.one_le_iff_ne_zero.2 fun h0 => by
      rw [h0] at hyP; exact hyP (slPv_E (S := S) η).pos
    exact (hy.trans (slE_mul_omega_lt (slPv_E (η + 1)) (Nm.Pv_lt_succ hg))).trans_le
      (Nm.Pv_mono (add_le_add le_rfl h1))

theorem slPvW_lt_Om1 (η : Ordinal.{0}) (hg : Bt.Good S η) : Nm.Pv S η * ω < Om 1 :=
  (slE_mul_omega_lt (slPv_E (η + 1)) (Nm.Pv_lt_succ hg)).trans (Nm.Pv_lt_Om1 S _)

/-- **`η_{ι(η)+g} = η + g` and `m_{ι(η)+g} = -1 + e(g)`** for `0 < g < P(η)·ω` (`ω^{Ω₁} ∣ η`). -/
theorem slCode_shift {η g : Ordinal.{0}} (hg : Bt.Good S η) (hdiv : ω ^ Om 1 ∣ η) (hg0 : g ≠ 0)
    (hgP : g < Nm.Pv S η * ω) :
    cdEta S (Bt.iota S η + g) = η + g ∧ cdCode S (Bt.iota S η + g) = cdOff (cdExp g) := by
  have hg1 : g < Om 1 := hgP.trans (slPvW_lt_Om1 η hg)
  have hι : Bt.iota S (η + g) = Bt.iota S η + g :=
    Pp.ppIota_add η g fun y hy => slGood hg (hy.trans hgP)
  have he : cdEta S (Bt.iota S η + g) = η + g := cdEta_unique (slGood hg hgP) hι
  refine ⟨he, ?_⟩
  unfold cdCode
  rw [he]
  have hexp := Ls.lsExp_add hdiv hg0 hg1
  have h2 : cdExp (η + g) < Om (1 + 1) := by
    rw [hexp]
    exact ((Ls.lsExp_le hg0).trans_lt hg1).trans (Om_lt_Om.2 (lt_add_one 1))
  rw [cdCodeOf_of_lt h2, hexp]

/-- `e(x·k + e) = e(e)` for `0 < e < x`, `x` an `ε`-number. -/
theorem slExp_lin {x k e : Ordinal.{0}} (hx : InE x) (he0 : e ≠ 0) (hex : e < x) :
    cdExp (x * k + e) = cdExp e := by
  have hle : cdExp e < x := (Ls.lsExp_le he0).trans_lt hex
  have hd1 : ω ^ (cdExp e + 1) ∣ x * k := by
    refine dvd_mul_of_dvd_left ?_ k
    have h : ω ^ (cdExp e + 1) ∣ ω ^ x := opow_dvd_opow ω (Order.add_one_le_of_lt hle)
    rwa [hx] at h
  have hd0 : ω ^ cdExp e ∣ x * k := (opow_dvd_opow ω le_self_add).trans hd1
  have hne : x * k + e ≠ 0 := fun h => he0 (le_antisymm (h ▸ le_add_self) zero_le)
  exact cdExp_eq hne (dvd_add hd0 (cdExp_dvd he0)) fun h => cdExp_not_dvd he0 ((dvd_add_iff hd1).1 h)

/-- `e(x·k) = x` for `0 < k < ω`, `x` an `ε`-number. -/
theorem slExp_mul {x : Ordinal.{0}} (hx : InE x) {k : ℕ} (hk : 0 < k) : cdExp (x * (k : Ordinal.{0})) = x := by
  have hk0 : (0 : Ordinal.{0}) < k := by exact_mod_cast hk
  have hne : x * (k : Ordinal.{0}) ≠ 0 := (mul_pos hx.pos hk0).ne'
  refine cdExp_eq hne ?_ ?_
  · have h : ω ^ x = x := hx
    rw [h]; exact dvd_mul_right _ _
  · intro h
    have e : ω ^ (x + 1) = x * ω := by
      rw [opow_add, opow_one]; exact congrArg (· * ω) hx
    rw [e] at h
    have h1 := Ordinal.le_of_dvd hne h
    have h2 : x * (k : Ordinal.{0}) < x * ω := (mul_lt_mul_iff_right₀ hx.pos).2 (natCast_lt_omega0 k)
    exact absurd (h1.trans_lt h2) (lt_irrefl _)

/-- **`υ_{λ+h} + υ_λ·j + p` determines `h`, `j` and `p`** (`0 < h`, `p < υ_λ`). -/
theorem slUps_inj {l h h' p p' : Ordinal.{0}} {j j' : ℕ} (hh : 0 < h) (hh' : 0 < h')
    (hp : p < upsilon l) (hp' : p' < upsilon l)
    (e : upsilon (l + h) + upsilon l * (j : Ordinal.{0}) + p =
      upsilon (l + h') + upsilon l * (j' : Ordinal.{0}) + p') : h = h' ∧ j = j' ∧ p = p' := by
  have hm := upsilon_normal.strictMono
  have hs : ∀ {h : Ordinal.{0}} {p : Ordinal.{0}} (j : ℕ), 0 < h → p < upsilon l →
      upsilon l * (j : Ordinal.{0}) + p < upsilon (l + h) := by
    intro h p j hh hp
    have hE : InE (upsilon (l + h)) :=
      upsPt_inE (upsPt_upsilon (lt_of_le_of_lt zero_le (lt_add_of_pos_right l hh)))
    have hlh : upsilon l < upsilon (l + h) := hm (lt_add_of_pos_right l hh)
    exact hE.add_lt (slE_mul_nat_lt hE hlh j) (hp.trans hlh)
  rw [add_assoc, add_assoc] at e
  have hseg := lr_seg_unique (y := upsilon (l + h) + (upsilon l * (j : Ordinal.{0}) + p)) le_self_add
    (Ls.lsUps_add_lt (hs j hh hp)) (by rw [e]; exact le_self_add) (by rw [e]; exact Ls.lsUps_add_lt (hs j' hh' hp'))
  have hhh : h = h' := add_left_cancel hseg
  subst hhh
  have e2 := add_left_cancel e
  have hl0 : upsilon l ≠ 0 := (lt_of_le_of_lt zero_le hp).ne'
  have hd : (j : Ordinal.{0}) = j' := by
    have := congrArg (· / upsilon l) e2
    simp only at this
    rwa [Ordinal.mul_add_div _ hl0, Ordinal.mul_add_div _ hl0, Ordinal.div_eq_zero_of_lt hp,
      Ordinal.div_eq_zero_of_lt hp', add_zero, add_zero] at this
  have hmd : p = p' := by
    have := congrArg (· % upsilon l) e2
    simp only at this
    rwa [Ordinal.mul_add_mod_self, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hp,
      Ordinal.mod_eq_of_lt hp'] at this
  exact ⟨rfl, by exact_mod_cast hd, hmd⟩

/-! ## The supply for the renaming -/

/-- **The supply for the linear renaming**: every Range restart `μ` with `m_μ = G_{k+1} + 1` reaches
`υ_{μ+ρ_μ·ω}`. -/
def SlSupW (S : InaccSeq.{0}) (k : ℕ) : Prop :=
  ∀ μ, CdRange S μ → cdCode S μ = Ls.lsG S (k + 1) + 1 → upsilon (μ + upsilon μ * ω) ≤ cdR S μ

/-- `SlSupW` gives `Ls.LsSupCode`. -/
theorem slSupW_sup {k : ℕ} (h : SlSupW S k) : Ls.LsSupCode S k := fun μ hR hc =>
  (upsilon_normal.strictMono.monotone (add_le_add le_rfl (Ordinal.le_mul_left _ omega0_pos))).trans
    (h μ hR hc)

/-- **LC-STRICT at `k` gives the supply for the renaming**: `υ_{μ+ρ_μ·ω} = P(η_μ + ρ_μ·ω) ≤ H(η_μ + G_k) ≤ r(μ)`. -/
theorem slSupW_of_strict {k : ℕ} (h : Ls.LsStrictCode S k) : SlSupW S k := by
  intro μ hR hc
  have hpv := Ls.lsPv_range hR
  obtain ⟨hgμ, hιμ, -⟩ := cdEta_spec (S := S) (Order.one_le_iff_ne_zero.2 hR.1.1)
    (cd_lt_iota (η0 := Om ω + Nc.ncPp S * (ω + 1)) (by rw [← Lw.lw_L_eq]; exact hR.2.2.1))
  refine Lc.lcR_of_strict (h μ hR hc) (by rw [hc]; exact le_self_add) ?_
  have hsh : Bt.iota S (cdEta S μ + upsilon μ * ω) = μ + upsilon μ * ω := by
    rw [Pp.ppIota_add _ _ (fun y hy => slGood hgμ (by rw [hpv]; exact hy)), hιμ]
  rw [← hsh, Bt.ups_iota]
  refine (Nm.Pv_mono (add_le_add le_rfl ?_)).trans le_add_self
  have h1 : upsilon μ * ω < Om 1 := by rw [← hpv]; exact slPvW_lt_Om1 _ hgμ
  exact (h1.trans (Ls.lsG_Om1 (S := S) k)).le

/-! ## The realizers at a named point -/

/-- **Realizer maps at a named point `a` up to `υ_{a+a·ω}`**, along the linear renaming `a ↦ ρ_μ`. -/
theorem slReal_named {a ηa : Ordinal.{0}} {k : ℕ}
    (hg : Bt.Good S ηa) (hι : Bt.iota S ηa = a) (hP : Nm.Pv S ηa = a) (hdiv : ω ^ Om 1 ∣ ηa)
    (hri : IsRestartIdx a) (hzl : Rz.rzLam < a)
    (hν : a < nuC) (hνβ : upsilon (a + a * ω) ≤ nuC) (hβL : upsilon (a + a * ω) < Nc.ncL S (ω + 1))
    (hcof : ∀ γ < a, ∃ μ, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < a ∧
      cdCode S μ = Ls.lsG S (k + 1) + 1)
    (hk : SlSupW S k)
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hstd : Cx.CxStdPairTop S) (haL : a ≤ Nc.ncL S (ω + 1)) :
    LrReal S a (upsilon (a + a * ω)) := by
  have hm := upsilon_normal.strictMono
  have hua : upsilon a = a := by
    have h := Bt.ups_iota S ηa; rw [hι] at h; exact h.trans hP
  have ha1' : a < Om 1 := by rw [← hP]; exact Nm.Pv_lt_Om1 S ηa
  have ha1 : a < Om1 := by rw [Br.Om1_eq]; exact ha1'
  have haE : InE a := by rw [← hP]; exact slPv_E ηa
  have ha0 : a ≠ 0 := hri.1
  have haW1 : a * ω < Om 1 := by rw [← hP]; exact slPvW_lt_Om1 ηa hg
  have hB0a : cdB0 < a := by
    obtain ⟨μ, hR, -, h2, -⟩ := hcof 0 (pos_iff_ne_zero.2 hri.1)
    refine lt_of_le_of_lt hR.2.1 ?_
    rw [← hua] at h2; exact hm.lt_iff_lt.1 h2
  have hWβ : ω ^ 2 ∣ a * ω := dvd_mul_of_dvd_left hri.2 ω
  have h2 : ω + 1 < ω ^ 2 := by
    have := lr_omega_mul_add_one_lt 1
    rwa [Nat.cast_one, mul_one] at this
  have hinner : ∀ g, g < a * ω → ω ^ 2 ∣ g → g + ω + 1 < a * ω := by
    intro g hgβ hgd
    rw [add_assoc]; exact (lr_addL (a := g) h2).trans_le (lr_dvd_add_le hgd hWβ hgβ)
  have hgP : ∀ g, g < a * ω → g < Nm.Pv S ηa * ω := fun g h => by rw [hP]; exact h
  -- the codes at the inner restarts `a + g`
  have hcodeA : ∀ g, 0 < g → g < a * ω → cdCode S (a + g) = cdOff (cdExp g) := by
    intro g hg0 hgβ
    have := (slCode_shift hg hdiv hg0.ne' (hgP g hgβ)).2
    rwa [hι] at this
  -- the code `-1 + e(g)` as `a·j + p`, and its image under the renaming as `ρ·j + p`
  have hform0 : ∀ g, 0 < g → g < a * ω → ∃ j : ℕ, ∃ p, p < a ∧
      cdOff (cdExp g) = a * (j : Ordinal.{0}) + p ∧
      ∀ ρ, InE ρ → g % a < ρ → cdOff (cdExp (slLin ρ a g)) = ρ * (j : Ordinal.{0}) + p := by
    intro g hg0 hgβ
    have hkω : g / a < ω := (Ordinal.lt_mul_iff_div_lt ha0).1 hgβ
    obtain ⟨n, hn⟩ := lt_omega0.1 hkω
    have hgdec : g = a * (n : Ordinal.{0}) + g % a := by
      rw [← hn]; exact (Ordinal.div_add_mod g a).symm
    by_cases he : g % a = 0
    · have hn0 : 0 < n := by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · exfalso
          rw [h0, he, Nat.cast_zero, mul_zero, add_zero] at hgdec
          exact hg0.ne' hgdec
        · exact h0
      refine ⟨1, 0, haE.pos, ?_, fun ρ hρ _ => ?_⟩
      · rw [hgdec, he, add_zero, slExp_mul haE hn0, cdOff, if_neg (not_lt.2 (slE_omega_lt haE).le)]
        simp
      · unfold slLin
        rw [hn, he, add_zero, slExp_mul hρ hn0, cdOff, if_neg (not_lt.2 (slE_omega_lt hρ).le)]
        simp
    · have hea : g % a < a := Ordinal.mod_lt g ha0
      refine ⟨0, cdOff (cdExp (g % a)), (cdOff_le _).trans_lt ((Ls.lsExp_le he).trans_lt hea), ?_,
        fun ρ hρ hr => ?_⟩
      · rw [Nat.cast_zero, mul_zero, zero_add]
        conv_lhs => rw [hgdec]
        rw [slExp_lin haE he hea]
      · rw [Nat.cast_zero, mul_zero, zero_add]
        unfold slLin
        rw [slExp_lin hρ he hr]
  -- the reaches at the inner restarts
  have hrA : ∀ g, 0 < g → g < a * ω → ω ^ 2 ∣ g →
      cdR S (a + g) = upsilon (a + (g + ω + 1)) + cdOff (cdExp g) := by
    intro g hg0 hgβ hgd
    have hri' : IsRestartIdx (a + g) := ⟨fun h => hri.1 (le_antisymm (h ▸ le_self_add) zero_le),
      dvd_add hri.2 hgd⟩
    have hC : upsilon (a + g + ω + 1) < nuC := by
      refine lt_of_lt_of_le (hm ?_) hνβ
      rw [add_assoc, add_assoc]; exact lr_addL (a := a) (by rw [← add_assoc]; exact hinner g hgβ hgd)
    have hsh : cdCode S (a + g) ≤ upsilon (a + g) := by
      rw [hcodeA g hg0 hgβ]
      exact (Ls.lsOff_le g hg0.ne').trans (le_add_self.trans hm.le_apply)
    rw [Ls.lsR_short hri' hC hsh, hcodeA g hg0 hgβ]
    unfold cdDelta; simp only [add_assoc]
  have hfh : ∀ ρ x, ω ^ 2 ∣ x → slLin ρ a (x + ω + 1) = slLin ρ a x + ω + 1 := by
    rintro ρ x ⟨q, rfl⟩
    rw [add_assoc, slLin_res ha0 hri.2 q _ h2, add_assoc]
  have hreal := slReal_ren (S := S) (l := a) (β := a * ω) hri (by rw [hua]; exact ha1)
    (by rw [hua]; exact hν) hνβ ?_ ?_ ?_ hstd (by rw [hua]; exact haL)
  · rwa [hua] at hreal
  · -- UPPER at the inner restarts
    intro g hg0 hgβ hgd
    refine hU _ ⟨⟨fun h => hri.1 (le_antisymm (h ▸ le_self_add) zero_le), dvd_add hri.2 hgd⟩,
      hB0a.le.trans le_self_add, (hm (lr_addL (a := a) hgβ)).trans hβL, ?_⟩
      (Or.inl (hzl.le.trans le_self_add))
    rw [hcodeA g hg0 hgβ]
    exact (Ls.lsOff_le g hg0.ne').trans_lt ((hgβ.trans haW1).trans (Lw.lw_Om1_lt_Pp S))
  · -- the form of the inner reaches
    intro g hg0 hgβ hgd
    obtain ⟨j, p, hpa, hcp, -⟩ := hform0 g hg0 hgβ
    refine Or.inr ⟨g + ω + 1, j, p, lt_of_le_of_lt zero_le (lt_add_one _), hinner g hgβ hgd,
      by rw [hua]; exact hpa, ?_⟩
    rw [hrA g hg0 hgβ hgd, hcp, hua]
    exact (add_assoc _ _ _).symm
  · -- the Range restarts, the renaming, the supply and the carry
    intro γ hγ Os hOs
    rw [hua] at hγ
    have hzua : upsilon Rz.rzLam < a := by rw [← hua]; exact hm hzl
    have hMa : Os.sup (fun d => d % a) < a :=
      (Finset.sup_lt_iff haE.pos).2 fun d _ => Ordinal.mod_lt d ha0
    obtain ⟨μ, hR, hγμ, hμa, hc⟩ := hcof (max γ (max (Os.sup (fun d => d % a)) (upsilon Rz.rzLam)))
      (max_lt hγ (max_lt hMa hzua))
    have hγ' : γ < upsilon μ := (le_max_left _ _).trans_lt hγμ
    have hMρ : Os.sup (fun d => d % a) < upsilon μ :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hγμ
    have hzμ : Rz.rzLam < μ :=
      hm.lt_iff_lt.1 (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hγμ)
    have hμa' : μ < a := by rw [← hua] at hμa; exact hm.lt_iff_lt.1 hμa
    have hρE : InE (upsilon μ) := upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 hR.1.1))
    have hρW : ω ^ 2 ∣ upsilon μ := by
      have h3 : ((2 : ℕ) : Ordinal.{0}) ≤ upsilon μ :=
        ((natCast_lt_omega0 2).trans (slE_omega_lt hρE)).le
      have h4 : ω ^ ((2 : ℕ) : Ordinal.{0}) ∣ ω ^ upsilon μ := opow_dvd_opow ω h3
      have h5 : ω ^ upsilon μ = upsilon μ := hρE
      rwa [Ordinal.opow_natCast, h5] at h4
    have hOs' : ∀ d ∈ Os, d < a * ω ∧ d % a < upsilon μ := fun d hd =>
      ⟨hOs d hd, (Finset.le_sup (f := fun d => d % a) hd).trans_lt hMρ⟩
    have hoff := slOff_lin ha0 hri.2 hρW hρE.pos hOs'
    have hμBa : μ + upsilon μ * ω < a := haE.add_lt hμa' (slE_mul_omega_lt haE hμa)
    refine ⟨μ, slLin (upsilon μ) a, upsilon μ * ω, hR, hγ', by rw [hua]; exact hμa, hμBa.le,
      dvd_mul_of_dvd_left hρW ω, hk μ hR hc, hoff, ?_⟩
    intro g hgO hg0 hgd
    have hgβ := hOs g hgO
    have hgr : g % a < upsilon μ := (hOs' g hgO).2
    obtain ⟨j0, p0, hp0, hcp, hcpρ⟩ := hform0 g hg0 hgβ
    have hfg := hcpρ (upsilon μ) hρE hgr
    have hpv := Ls.lsPv_range hR
    obtain ⟨hgμ, hιμ, -⟩ := cdEta_spec (S := S) (Order.one_le_iff_ne_zero.2 hR.1.1)
      (cd_lt_iota (η0 := Om ω + Nc.ncPp S * (ω + 1)) (by rw [← Lw.lw_L_eq]; exact hR.2.2.1))
    have hdivμ := Ls.lsDiv_of_code hc
    have hfgB : slLin (upsilon μ) a g < upsilon μ * ω := hoff.bd g hgO
    have hfg0 : slLin (upsilon μ) a g ≠ 0 := by
      have := hoff.mono (Finset.mem_coe.2 (Finset.mem_insert_self 0 Os))
        (Finset.mem_coe.2 (Finset.mem_insert_of_mem hgO)) hg0
      rw [hoff.zero] at this; exact this.ne'
    have hcM : cdCode S (μ + slLin (upsilon μ) a g) = cdOff (cdExp (slLin (upsilon μ) a g)) := by
      have := (slCode_shift hgμ hdivμ hfg0 (by rw [hpv]; exact hfgB)).2
      rwa [hιμ] at this
    have hgdW : ω ^ 2 ∣ slLin (upsilon μ) a g := by obtain ⟨q, rfl⟩ := hgd; exact hoff.dvd q
    have hriμ : IsRestartIdx (μ + slLin (upsilon μ) a g) :=
      ⟨fun h => hR.1.1 (le_antisymm (h ▸ le_self_add) zero_le), dvd_add hR.1.2 hgdW⟩
    have hfW : slLin (upsilon μ) a g + ω ^ 2 ≤ upsilon μ * ω :=
      lr_dvd_add_le hgdW (dvd_mul_of_dvd_left hρW ω) hfgB
    have hμfa : μ + slLin (upsilon μ) a g + ω + 1 < a := by
      calc μ + slLin (upsilon μ) a g + ω + 1 = μ + (slLin (upsilon μ) a g + (ω + 1)) := by
            rw [add_assoc, add_assoc]
        _ < μ + (slLin (upsilon μ) a g + ω ^ 2) :=
            lr_addL (a := μ) (lr_addL (a := slLin (upsilon μ) a g) h2)
        _ ≤ μ + upsilon μ * ω := lr_addLe (a := μ) hfW
        _ < a := hμBa
    have hCμ : upsilon (μ + slLin (upsilon μ) a g + ω + 1) < nuC :=
      ((hm hμfa).trans_eq hua).trans hν
    have hshμ : cdCode S (μ + slLin (upsilon μ) a g) ≤ upsilon (μ + slLin (upsilon μ) a g) := by
      rw [hcM]; exact (Ls.lsOff_le _ hfg0).trans (le_add_self.trans hm.le_apply)
    have hrμ : cdR S (μ + slLin (upsilon μ) a g) =
        upsilon (μ + (slLin (upsilon μ) a g + ω + 1)) + (upsilon μ * (j0 : Ordinal.{0}) + p0) := by
      rw [Ls.lsR_short hriμ hCμ hshμ, hcM, hfg]; unfold cdDelta; simp only [add_assoc]
    have hRμ : CdRange S (μ + slLin (upsilon μ) a g) := by
      refine ⟨hriμ, hR.2.1.trans le_self_add, ?_, ?_⟩
      · exact ((hm (lt_of_le_of_lt (le_self_add.trans le_self_add) hμfa)).trans_eq hua).trans_le haL
      · rw [hcM]
        refine (Ls.lsOff_le _ hfg0).trans_lt ((hfgB.trans ?_).trans (Lw.lw_Om1_lt_Pp S))
        rw [← hpv]; exact slPvW_lt_Om1 _ hgμ
    refine ⟨hL _ hRμ (Or.inl (hzμ.le.trans le_self_add)), fun hbig => ?_, fun h hhO j p hh0 hpγ hr => ?_⟩
    · exfalso
      rw [hrA g hg0 hgβ hgd] at hbig
      have hgl : g < a + (g + ω + 1) :=
        lt_of_lt_of_le (lt_of_le_of_lt le_self_add (lt_add_one (g + ω))) le_add_self
      have hcl : cdOff (cdExp g) < upsilon (a + (g + ω + 1)) :=
        (Ls.lsOff_le g hg0.ne').trans_lt (hgl.trans_le hm.le_apply)
      have h1 := Ls.lsUps_add_lt hcl
      have h3 : upsilon (succ (a + (g + ω + 1))) ≤ upsilon (a + a * ω) := by
        refine hm.monotone ?_
        rw [lr_succ_add]
        exact lr_addLe (a := a) (Order.succ_le_of_lt (hinner g hgβ hgd))
      exact absurd (hbig.trans_lt (h1.trans_le h3)) (lt_irrefl _)
    · have hcp' : cdOff (cdExp g) = upsilon a * (j0 : Ordinal.{0}) + p0 := by rw [hua]; exact hcp
      have e : upsilon (a + (g + ω + 1)) + upsilon a * (j0 : Ordinal.{0}) + p0 =
          upsilon (a + h) + upsilon a * (j : Ordinal.{0}) + p := by
        rw [add_assoc, ← hcp', ← hrA g hg0 hgβ hgd, hr]
      have hpa : p < upsilon a := by rw [hua]; exact hpγ.trans (hγ'.trans hμa)
      obtain ⟨hh, hj, hpp⟩ := slUps_inj (lt_of_le_of_lt zero_le (lt_add_one _)) hh0
        (by rw [hua]; exact hp0) hpa e
      rw [← hh, ← hj, ← hpp, hrμ, hfh _ g hgd, add_assoc]

/-- **The realizers at `m*` up to `υ_{m*+m*·ω} < L(1)`**, given `L(ω) ≤ ν_C` and the supply `SlSupW`. -/
theorem slReal_M {k : ℕ} (hlow : Nc.ncL S ω ≤ nuC) (hk : SlSupW S k)
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (hstd : Cx.CxStdPairTop S) :
    LrReal S (Nc.ncL S 0) (upsilon (Nc.ncL S 0 + Nc.ncL S 0 * ω)) ∧
      upsilon (Nc.ncL S 0 + Nc.ncL S 0 * ω) < Nc.ncL S 1 := by
  obtain ⟨hg, hι, hP, hdiv, hri, hzl⟩ := Ls.lsM_named (S := S)
  obtain ⟨hg1, hι1, hP1, -, -, -⟩ := Ls.lsL_named (S := S) 0
  have hm := upsilon_normal.strictMono
  have hb : upsilon (Nc.ncL S 0 + Nc.ncL S 0 * ω) < Nc.ncL S 1 := by
    have hu1 : upsilon (Nc.ncL S 1) = Nc.ncL S 1 := by
      have h := Bt.ups_iota S (Om ω + Nc.ncPp S * ((0 + 1 : ℕ) : Ordinal.{0}))
      rw [hι1] at h; simpa using h.trans hP1
    have hE1 : InE (Nc.ncL S 1) := by
      have := slPv_E (S := S) (Om ω + Nc.ncPp S * ((0 + 1 : ℕ) : Ordinal.{0}))
      rw [hP1] at this; simpa using this
    have h01 := Rl.rlM_lt_L1 (S := S)
    rw [← hu1]
    exact hm (hE1.add_lt h01 (slE_mul_omega_lt hE1 h01))
  have hL1w : Nc.ncL S 1 ≤ Nc.ncL S ω := Pp.ppL_mono one_lt_omega0.le
  have hLw1 : Nc.ncL S ω < Nc.ncL S (ω + 1) := Qq.qqL_lt_succ S
  refine ⟨slReal_named hg hι hP hdiv hri hzl ((Rl.rlM_lt_L1 (S := S)).trans_le (hL1w.trans hlow))
    (hb.le.trans (hL1w.trans hlow)) (hb.trans_le hL1w |>.trans hLw1) (Ls.lsNames_M (S := S) k) hk hU hL
    hstd (Pp.ppL_mono zero_le), hb⟩

/-- **The realizers at `L(n+1)` up to `υ_{a+a·ω} < L(n+2)`**, given `L(ω) ≤ ν_C` and the supply `SlSupW`. -/
theorem slReal_L {k : ℕ} (hlow : Nc.ncL S ω ≤ nuC) (hk : SlSupW S k)
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (hstd : Cx.CxStdPairTop S) (n : ℕ) :
    LrReal S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) * ω)) ∧
      upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) * ω) <
        Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) := by
  obtain ⟨hg, hι, hP, hdiv, hri, hzl⟩ := Ls.lsL_named (S := S) n
  obtain ⟨hg1, hι1, hP1, -, -, -⟩ := Ls.lsL_named (S := S) (n + 1)
  have hm := upsilon_normal.strictMono
  have hb : upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) * ω) <
      Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) := by
    have hu1 : upsilon (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})) = Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) := by
      have h := Bt.ups_iota S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0}))
      rw [hι1] at h; exact h.trans hP1
    have hE1 : InE (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})) := by
      have := slPv_E (S := S) (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0}))
      rw [hP1] at this; exact this
    have h01 := Pp.ppL_lt_succ (S := S) n
    rw [← hu1]
    exact hm (hE1.add_lt h01 (slE_mul_omega_lt hE1 h01))
  have h2w : Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) ≤ Nc.ncL S ω := (Pp.ppL_lt_omega (n + 1)).le
  have hLw1 : Nc.ncL S ω < Nc.ncL S (ω + 1) := Qq.qqL_lt_succ S
  refine ⟨slReal_named hg hι hP hdiv hri hzl ((Pp.ppL_lt_omega n).trans_le hlow)
    (hb.le.trans (h2w.trans hlow)) ((hb.trans_le h2w).trans hLw1) (Ls.lsNames_L (S := S) n k) hk hU hL
    hstd ((Pp.ppL_lt_omega n).le.trans hLw1.le), hb⟩

end Googology.Trans.PoR.InaccPsi.R2.Sl
