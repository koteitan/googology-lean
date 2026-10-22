import Googology.Trans.PoR.InaccPsi.R2.RhFn

/-!
# The hierarchies `H^γ_β` over `Γ` at every `γ`, and the flattened levels `Φ_μ`, `μ < Ω₁·Ω₁`

`Γ_ = Ordinal.gamma`, `F_β = Rh.rhF β = veblenWith Γ_ β`.

* `riG γ` (**the base of the `γ`-th hierarchy**): `riG 0 = Γ_`, and for `γ ≠ 0` `riG γ` enumerates the common fixed
  points of the normal functions `b ↦ H^{γ'}_b(0)`, `γ' < γ` (`derivFamily`); `riH γ β = veblenWith (riG γ) β`
  (`H^0_β = F_β`; `H^1_0` enumerates the `x` with `F_x(0) = x`);
* `riG_normal`, `riG_range` (the values are values of `Γ_`), `riH_normal`, `riH_SC` (the values are strongly
  critical), `riH_fix_lower_beta`, `riH_fix_lower_gamma` (**a value of `H^γ_β` is a fixed point of `H^γ_j`, `j < β`,
  and of `H^{γ'}_j`, `γ' < γ`, `j` below it**), `riH_range` (**a strongly critical `v` that is a fixed point of every
  `H^γ_j`, `j < β`, and of every `H^{γ'}_j`, `γ' < γ`, `j < v`, is a value of `H^γ_β`**), `riG_strictMono0`
  (`γ ↦ riG γ 0` is strictly increasing, so `γ ≤ riG γ 0`);
* the flattened levels: `riP μ = H^{μ/Ω₁}_{μ mod Ω₁}`, `riDat μ = max(μ/Ω₁, μ mod Ω₁)` (the countable data of `μ`);
  `riP_lt` (`riP μ = F_μ` for `μ < Ω₁`), `riP_fix_lower` (**a value `v` of `Φ_μ` is a fixed point of every `Φ_j`, `j <
  μ`, with `riDat j < v`**), `riP_range` (**a strongly critical `v` with `riDat μ < v` that is a fixed point of every
  `Φ_j`, `j < μ`, `riDat j < v`, is a value of `Φ_μ`**), `riDat_le_riP` (`riDat μ ≤ Φ_μ(o)`),
  `riP_ne_self_of_dat` (`τ ≠ 0` with `τ ≤ riDat μ` is not a fixed point of `Φ_μ`);
* `riU_mem` (**`u_μ = Ω₁^μ ∈ Cl(a, b)` when `riDat μ < b`**), `riU_mul_mem`.

No new axiom.  New definitions: `riG`, `riH`, `riP`, `riDat`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ri

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb
  Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rh

variable {S : InaccSeq.{0}}

/-! ## The bases `riG γ` and the hierarchies `riH γ` -/

/-- **The base of the `γ`-th hierarchy**: `riG 0 = Γ_`; for `γ ≠ 0`, `riG γ` enumerates the common fixed points of
`b ↦ veblenWith (riG γ') b 0`, `γ' < γ`. -/
noncomputable def riG (γ : Ordinal.{0}) : Ordinal.{0} → Ordinal.{0} :=
  if γ = 0 then gamma else derivFamily fun (x : Iio γ) => fun b => veblenWith (riG x.1) b 0
termination_by γ
decreasing_by exact x.2

/-- **The `γ`-th hierarchy**: `riH γ β = veblenWith (riG γ) β`. -/
noncomputable def riH (γ β : Ordinal.{0}) : Ordinal.{0} → Ordinal.{0} := veblenWith (riG γ) β

theorem riG_zero : riG 0 = gamma := by rw [riG, if_pos rfl]

theorem riG_of_ne {γ : Ordinal.{0}} (h : γ ≠ 0) :
    riG γ = derivFamily fun (x : Iio γ) => fun b => riH x.1 b 0 := by
  rw [riG, if_neg h]; rfl

theorem riH_zero_left (β : Ordinal.{0}) : riH 0 β = rhF β := by
  unfold riH rhF; rw [riG_zero]

theorem riH_zero (γ : Ordinal.{0}) : riH γ 0 = riG γ := veblenWith_zero _

/-- **`riG γ` is normal and its values are values of `Γ_`.** -/
theorem riG_props (γ : Ordinal.{0}) : Order.IsNormal (riG γ) ∧ ∀ o, riG γ o ∈ range gamma := by
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  rcases eq_or_ne γ 0 with rfl | hγ
  · rw [riG_zero]; exact ⟨isNormal_gamma, fun o => ⟨o, rfl⟩⟩
  have hpos : ∀ γ' < γ, 0 < riG γ' 0 := fun γ' h => by
    obtain ⟨e, he⟩ := (IH γ' h).2 0; rw [← he]; exact gamma_pos
  have hN : ∀ x : Iio γ, Order.IsNormal (fun b => riH x.1 b 0) := fun x =>
    isNormal_veblenWith_zero (IH x.1 x.2).1 (hpos x.1 x.2)
  rw [riG_of_ne hγ]
  refine ⟨isNormal_derivFamily _, fun o => ?_⟩
  have h0 : (0 : Ordinal.{0}) < γ := pos_iff_ne_zero.2 hγ
  have hfp := derivFamily_fp (f := fun (x : Iio γ) => fun b => riH x.1 b 0) (i := ⟨0, h0⟩) (hN ⟨0, h0⟩) o
  rw [← hfp]
  show riH 0 _ 0 ∈ range gamma
  rw [riH_zero_left]
  unfold rhF
  exact veblenWith_mem_range isNormal_gamma

theorem riG_normal (γ : Ordinal.{0}) : Order.IsNormal (riG γ) := (riG_props γ).1

theorem riG_range (γ o : Ordinal.{0}) : riG γ o ∈ range gamma := (riG_props γ).2 o

theorem riG_pos (γ : Ordinal.{0}) : 0 < riG γ 0 := by
  obtain ⟨e, he⟩ := riG_range γ 0; rw [← he]; exact gamma_pos

theorem riH_normal (γ β : Ordinal.{0}) : Order.IsNormal (riH γ β) := isNormal_veblenWith (riG_normal γ) β

theorem riH_zero_normal (γ : Ordinal.{0}) : Order.IsNormal (fun b => riH γ b 0) :=
  isNormal_veblenWith_zero (riG_normal γ) (riG_pos γ)

theorem riH_lt (γ β : Ordinal.{0}) {a b : Ordinal.{0}} : riH γ β a < riH γ β b ↔ a < b :=
  (riH_normal γ β).strictMono.lt_iff_lt

theorem riH_le (γ β : Ordinal.{0}) {a b : Ordinal.{0}} : riH γ β a ≤ riH γ β b ↔ a ≤ b :=
  (riH_normal γ β).strictMono.le_iff_le

theorem riH_le_self (γ β o : Ordinal.{0}) : o ≤ riH γ β o := (riH_normal γ β).strictMono.le_apply

theorem riH_left_le (γ β o : Ordinal.{0}) : β ≤ riH γ β o :=
  left_le_veblenWith (riG_normal γ) (riG_pos γ) β o

/-- The values of `riH γ β` are values of `riG γ`. -/
theorem riH_mem_G (γ β o : Ordinal.{0}) : riH γ β o ∈ range (riG γ) :=
  veblenWith_mem_range (riG_normal γ)

/-- **The values of `riH γ β` are strongly critical.** -/
theorem riH_SC (γ β o : Ordinal.{0}) : SC (riH γ β o) := by
  obtain ⟨c, hc⟩ := riH_mem_G γ β o
  obtain ⟨e, he⟩ := riG_range γ c
  rw [← hc, ← he]; exact lq_gamma_SC e

/-- A value of `riG γ`, `γ ≠ 0`, is a fixed point of `b ↦ riH γ' b 0` for every `γ' < γ`. -/
theorem riG_fix_diag {γ γ' v : Ordinal.{0}} (hγ' : γ' < γ) (hv : v ∈ range (riG γ)) : riH γ' v 0 = v := by
  have hγ : γ ≠ 0 := (lt_of_le_of_lt zero_le hγ').ne'
  rw [riG_of_ne hγ] at hv
  exact (mem_range_derivFamily (f := fun (x : Iio γ) => fun b => riH x.1 b 0)
    (fun x => riH_zero_normal x.1)).1 hv ⟨γ', hγ'⟩

/-- **A value of `riH γ β` is a fixed point of every `riH γ j`, `j < β`.** -/
theorem riH_fix_lower_beta {γ j β : Ordinal.{0}} (h : j < β) (o : Ordinal.{0}) :
    riH γ j (riH γ β o) = riH γ β o :=
  veblenWith_veblenWith_of_lt (riG_normal γ) h o

/-- **A value `v` of `riG γ` is a fixed point of every `riH γ' j`, `γ' < γ`, `j < v`.** -/
theorem riH_fix_lower_gamma {γ γ' j v : Ordinal.{0}} (hγ' : γ' < γ) (hv : v ∈ range (riG γ)) (hj : j < v) :
    riH γ' j v = v := by
  have hd := riG_fix_diag hγ' hv
  rw [← hd]
  exact veblenWith_veblenWith_of_lt (riG_normal γ') hj 0

/-- A fixed point of `riH γ β` is a fixed point of every `riH γ j`, `j ≤ β`. -/
theorem riH_fix_mono {γ j β x : Ordinal.{0}} (h : j ≤ β) (hx : riH γ β x = x) : riH γ j x = x :=
  veblenWith_eq_self_of_le (riG_normal γ) h hx

/-- A fixed point of `riH γ β` is a value of `riH γ (β + 1)`. -/
theorem riH_of_fix {γ β x : Ordinal.{0}} (h : riH γ β x = x) : ∃ e, riH γ (β + 1) e = x := by
  unfold riH; rw [veblenWith_add_one (riG_normal γ)]
  exact (le_iff_deriv (riH_normal γ β)).1 h.le

/-- **A value of `riG γ`**: a strongly critical `v` that is a fixed point of every `riH γ' j`, `γ' < γ`, `j < v`. -/
theorem riG_range_of {γ v : Ordinal.{0}} (hSC : SC v) (hfix : ∀ γ' < γ, ∀ j < v, riH γ' j v = v) :
    v ∈ range (riG γ) := by
  rcases eq_or_ne γ 0 with rfl | hγ
  · rw [riG_zero]; exact lq_SC_gamma hSC
  rw [riG_of_ne hγ]
  refine (mem_range_derivFamily (f := fun (x : Iio γ) => fun b => riH x.1 b 0)
    (fun x => riH_zero_normal x.1)).2 fun x => ?_
  show riH x.1 v 0 = v
  have hv0 : v ≠ 0 := hSC.1.ne'
  obtain ⟨c, hc⟩ := (mem_range_veblenWith (riG_normal x.1) hv0).2 fun b hb => hfix x.1 x.2 b hb
  have hc' : riH x.1 v c = v := hc
  have hle : riH x.1 v 0 ≤ v := ((riH_le _ _).2 zero_le).trans_eq hc'
  exact le_antisymm hle (left_le_veblenWith (riG_normal x.1) (riG_pos x.1) v 0)

/-- **A value of `riH γ β`**: a strongly critical `v` that is a fixed point of every `riH γ j`, `j < β`, and of every
`riH γ' j`, `γ' < γ`, `j < v`. -/
theorem riH_range {γ β v : Ordinal.{0}} (hSC : SC v) (hlow : ∀ γ' < γ, ∀ j < v, riH γ' j v = v)
    (hfix : ∀ j < β, riH γ j v = v) : ∃ e, riH γ β e = v := by
  rcases eq_or_ne β 0 with rfl | hβ
  · rw [riH_zero]; exact riG_range_of hSC hlow
  · exact (mem_range_veblenWith (riG_normal γ) hβ).2 hfix

/-- **`γ ↦ riG γ 0` is strictly increasing.** -/
theorem riG_strictMono0 : StrictMono (fun γ => riG γ 0) := by
  intro γ γ'' h
  show riG γ 0 < riG γ'' 0
  set v := riG γ'' 0 with hv
  have hfix : riH γ v 0 = v := riG_fix_diag h ⟨0, rfl⟩
  have hv0 : 0 < v := riG_pos γ''
  set f := riG γ with hf
  have hN := riG_normal γ
  have h1 : f 0 < f (f 0) := hN.strictMono (riG_pos γ)
  have h2 : f 0 ≤ deriv f 0 := by
    have := hN.monotone (zero_le : (0 : Ordinal.{0}) ≤ deriv f 0)
    rwa [deriv_fp hN] at this
  have h3 : f (f 0) ≤ deriv f 0 := by
    have := hN.monotone h2
    rwa [deriv_fp hN] at this
  have h4 : riH γ 1 0 ≤ riH γ v 0 :=
    (veblenWith_zero_le_veblenWith_zero hN (riG_pos γ)).2 (Order.one_le_iff_pos.2 hv0)
  have h5 : riH γ 1 0 = deriv f 0 := by unfold riH; rw [veblenWith_one hN]
  calc f 0 < f (f 0) := h1
    _ ≤ deriv f 0 := h3
    _ = riH γ 1 0 := h5.symm
    _ ≤ riH γ v 0 := h4
    _ = v := hfix

/-- `γ ≤ riG γ 0`. -/
theorem riG_le0 (γ : Ordinal.{0}) : γ ≤ riG γ 0 := riG_strictMono0.le_apply

/-- `γ ≤ riH γ β o` and `β ≤ riH γ β o`. -/
theorem riH_data_le (γ β o : Ordinal.{0}) : γ ≤ riH γ β o ∧ β ≤ riH γ β o := by
  refine ⟨(riG_le0 γ).trans ?_, riH_left_le γ β o⟩
  obtain ⟨e, he⟩ := riH_mem_G γ β o
  rw [← he]; exact (riG_normal γ).monotone zero_le

/-! ## The flattened levels `Φ_μ = riP μ`, `μ < Ω₁·Ω₁` -/

/-- **The level `μ`**: `Φ_μ = riH (μ / Ω₁) (μ mod Ω₁)`. -/
noncomputable def riP (μ : Ordinal.{0}) : Ordinal.{0} → Ordinal.{0} := riH (μ / Om 1) (μ % Om 1)

/-- **The countable data of a level `μ`**: `max(μ / Ω₁, μ mod Ω₁)`. -/
noncomputable def riDat (μ : Ordinal.{0}) : Ordinal.{0} := max (μ / Om 1) (μ % Om 1)

theorem riDat_div_le (μ : Ordinal.{0}) : μ / Om 1 ≤ riDat μ := le_max_left _ _

theorem riDat_mod_le (μ : Ordinal.{0}) : μ % Om 1 ≤ riDat μ := le_max_right _ _

theorem riDat_lt_iff {μ q : Ordinal.{0}} : riDat μ < q ↔ μ / Om 1 < q ∧ μ % Om 1 < q := max_lt_iff

theorem ri_div_mod (μ : Ordinal.{0}) : Om 1 * (μ / Om 1) + μ % Om 1 = μ := Ordinal.div_add_mod μ (Om 1)

theorem riP_lt {μ : Ordinal.{0}} (h : μ < Om 1) : riP μ = rhF μ := by
  unfold riP
  rw [Ordinal.div_eq_zero_of_lt h, Ordinal.mod_eq_of_lt h, riH_zero_left]

theorem riDat_lt_Om1 {μ : Ordinal.{0}} (h : μ < Om 1) : riDat μ = μ := by
  unfold riDat; rw [Ordinal.div_eq_zero_of_lt h, Ordinal.mod_eq_of_lt h]; exact max_eq_right zero_le

theorem riP_normal (μ : Ordinal.{0}) : Order.IsNormal (riP μ) := riH_normal _ _

theorem riP_lt_iff (μ : Ordinal.{0}) {a b : Ordinal.{0}} : riP μ a < riP μ b ↔ a < b := riH_lt _ _

theorem riP_le_iff (μ : Ordinal.{0}) {a b : Ordinal.{0}} : riP μ a ≤ riP μ b ↔ a ≤ b := riH_le _ _

theorem riP_le_self (μ o : Ordinal.{0}) : o ≤ riP μ o := riH_le_self _ _ _

theorem riP_SC (μ o : Ordinal.{0}) : SC (riP μ o) := riH_SC _ _ _

theorem riP_left_le (μ o : Ordinal.{0}) : μ % Om 1 ≤ riP μ o := riH_left_le _ _ _

/-- `(Ω₁·a + b) / Ω₁ = a` and `(Ω₁·a + b) mod Ω₁ = b` for `b < Ω₁`. -/
theorem ri_lvl {a b : Ordinal.{0}} (hb : b < Om 1) : (Om 1 * a + b) / Om 1 = a ∧ (Om 1 * a + b) % Om 1 = b := by
  have h0 : (Om 1 : Ordinal.{0}) ≠ 0 := rd_Om1_ne
  exact ⟨by rw [Ordinal.mul_add_div _ h0, Ordinal.div_eq_zero_of_lt hb, add_zero],
    by rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hb]⟩

theorem riP_lvl {a b : Ordinal.{0}} (hb : b < Om 1) : riP (Om 1 * a + b) = riH a b := by
  unfold riP; rw [(ri_lvl hb).1, (ri_lvl hb).2]

theorem riDat_lvl {a b : Ordinal.{0}} (hb : b < Om 1) : riDat (Om 1 * a + b) = max a b := by
  unfold riDat; rw [(ri_lvl hb).1, (ri_lvl hb).2]

theorem ri_mod_lt (μ : Ordinal.{0}) : μ % Om 1 < Om 1 := Ordinal.mod_lt μ rd_Om1_ne

/-- The order of levels: `j < μ` iff `j / Ω₁ < μ / Ω₁`, or equal quotients and `j mod Ω₁ < μ mod Ω₁`. -/
theorem ri_lt_cases {j μ : Ordinal.{0}} (h : j < μ) :
    j / Om 1 < μ / Om 1 ∨ (j / Om 1 = μ / Om 1 ∧ j % Om 1 < μ % Om 1) := by
  have hdle : j / Om 1 ≤ μ / Om 1 := Ordinal.div_le_left h.le _
  rcases lt_or_eq_of_le hdle with h1 | he
  · exact Or.inl h1
  · refine Or.inr ⟨he, ?_⟩
    have h' := h
    rw [← ri_div_mod j, ← ri_div_mod μ, he] at h'
    exact (add_lt_add_iff_left _).1 h'

/-- **A value `v` of `Φ_μ` is a fixed point of every `Φ_j`, `j < μ`, with `riDat j < v`.** -/
theorem riP_fix_lower {j μ v : Ordinal.{0}} (h : j < μ) (hv : v ∈ range (riP μ)) (hj : riDat j < v) :
    riP j v = v := by
  obtain ⟨o, rfl⟩ := hv
  rcases ri_lt_cases h with h1 | ⟨he, h2⟩
  · exact riH_fix_lower_gamma h1 (riH_mem_G _ _ o) ((riDat_mod_le j).trans_lt hj)
  · unfold riP; rw [he]; exact riH_fix_lower_beta h2 o

/-- **A value of `Φ_μ`**: a countable strongly critical `v` with `riDat μ < v` that is a fixed point of every `Φ_j`,
`j < μ`, `riDat j < v`. -/
theorem riP_range {μ v : Ordinal.{0}} (hSC : SC v) (hv1 : v < Om 1) (hμ : riDat μ < v)
    (hfix : ∀ j < μ, riDat j < v → riP j v = v) : ∃ e, riP μ e = v := by
  have hq := (riDat_lt_iff.1 hμ).1
  have hr := (riDat_lt_iff.1 hμ).2
  refine riH_range hSC (fun γ' hγ' b hb => ?_) (fun b hb => ?_)
  · have hb1 : b < Om 1 := hb.trans hv1
    have hj : Om 1 * γ' + b < μ := by
      calc Om 1 * γ' + b < Om 1 * γ' + Om 1 := (add_lt_add_iff_left _).2 hb1
        _ = Om 1 * (γ' + 1) := by rw [mul_add_one]
        _ ≤ Om 1 * (μ / Om 1) := mul_le_mul_right (Order.add_one_le_of_lt hγ') _
        _ ≤ μ := by conv_rhs => rw [← ri_div_mod μ]
                    exact le_self_add
    have := hfix _ hj (by rw [riDat_lvl hb1]; exact max_lt (hγ'.trans hq) hb)
    rwa [riP_lvl hb1] at this
  · have hb1 : b < Om 1 := hb.trans (ri_mod_lt μ)
    have hj : Om 1 * (μ / Om 1) + b < μ := by
      conv_rhs => rw [← ri_div_mod μ]
      exact (add_lt_add_iff_left _).2 hb
    have := hfix _ hj (by rw [riDat_lvl hb1]; exact max_lt hq (hb.trans hr))
    rwa [riP_lvl hb1] at this

/-- A value of `Φ_μ` lies in the range of `Γ_`, and `Φ_μ` agrees with the level's hierarchy. -/
theorem riP_mem_G (μ o : Ordinal.{0}) : riP μ o ∈ range (riG (μ / Om 1)) := riH_mem_G _ _ _

/-- **A fixed point of `Φ_μ` is a fixed point of every `Φ_j`, `j ≤ μ`, with `riDat j < x`**. -/
theorem riP_fix_mono {j μ x : Ordinal.{0}} (h : j ≤ μ) (hx : riP μ x = x) (hj : riDat j < x) : riP j x = x := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact hx
  · exact riP_fix_lower hlt ⟨x, hx⟩ hj

/-! ## The multipliers `u_μ` in the closures -/

/-- `Ω₁·μ ∈ Cl(a, b)` when `riDat μ < b`. -/
theorem riOm1_mul_mem {μ a b : Ordinal.{0}} (hμ : riDat μ < b) : Om 1 * μ ∈ S.CSet a b := by
  have hq := (riDat_lt_iff.1 hμ).1
  have hr := (riDat_lt_iff.1 hμ).2
  have hO : Om 1 ∈ S.CSet a b := CSet.Om_mem (CSet.one_mem _ _)
  have h2 : Om 1 + Om 1 ∈ S.CSet a b := CSet.add_mem hO hO
  have hm1 : ω ^ (Om 1 + Om 1) * (μ / Om 1) ∈ S.CSet a b := Nm.mem_opow_mul h2 hq
  have hm2 : ω ^ Om 1 * (μ % Om 1) ∈ S.CSet a b := Nm.mem_opow_mul hO hr
  have hE : ω ^ (Om 1 : Ordinal.{0}) = Om 1 := Bt.Om1_opow
  have e : Om 1 * μ = ω ^ (Om 1 + Om 1) * (μ / Om 1) + ω ^ Om 1 * (μ % Om 1) := by
    rw [opow_add, hE]
    conv_lhs => rw [← ri_div_mod μ]
    rw [mul_add, mul_assoc]
  rw [e]
  exact CSet.add_mem hm1 hm2

/-- **`u_μ = Ω₁^μ ∈ Cl(a, b)` when `riDat μ < b`.** -/
theorem riU_mem {μ a b : Ordinal.{0}} (hμ : riDat μ < b) : Le.leOe μ ∈ S.CSet a b := by
  unfold Le.leOe; rw [← veblen_zero_apply]
  exact CSet.phi_mem (CSet.zero_mem _ _) (riOm1_mul_mem hμ)

/-- `u_μ·D ∈ Cl(a, b)` for `riDat μ < b`, `D < b`. -/
theorem riU_mul_mem {μ a b D : Ordinal.{0}} (hμ : riDat μ < b) (hD : D < b) :
    Le.leOe μ * D ∈ S.CSet a b := by
  unfold Le.leOe; exact Nm.mem_opow_mul (riOm1_mul_mem hμ) hD

/-- **`riDat μ ≤ Φ_μ(o)`.** -/
theorem riDat_le_riP (μ o : Ordinal.{0}) : riDat μ ≤ riP μ o :=
  max_le (riH_data_le _ _ o).1 (riH_data_le _ _ o).2

/-- **`τ ≠ 0` with `τ ≤ riDat μ` is not a fixed point of `Φ_μ`.** -/
theorem riP_ne_self_of_dat {μ τ : Ordinal.{0}} (h0 : τ ≠ 0) (hτ : τ ≤ riDat μ) : riP μ τ ≠ τ := by
  intro hfix
  have h1 : riP μ 0 ≤ τ := hfix ▸ (riP_le_iff μ).2 zero_le
  have h2 : riP μ 0 = riP μ τ := by rw [hfix]; exact le_antisymm h1 (hτ.trans (riDat_le_riP μ 0))
  exact h0 ((riP_normal μ).strictMono.injective h2).symm

end Googology.Trans.PoR.InaccPsi.R2.Ri
