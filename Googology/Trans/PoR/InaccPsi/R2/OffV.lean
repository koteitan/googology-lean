import Googology.Trans.PoR.InaccPsi.R2.OffPhi

/-!
# Theorem BLK^O in `R₂^C` below `V_ω(1)` (the Veblen hierarchy over `υ`)

The project's Veblen hierarchy over `υ`: `V_1(α) = Ξ_α`, `V_{n+1}` enumerates the fixed points of
`V_n`; here `V 0 = υ`, `V (n+1) = deriv (V n)` (Mathlib's derivative), so `V 1 = Ξ`, `V 2 1 = Φ_1`.
The level `γ(λ)` of a restart index `λ` is the largest `n` with `λ` in the range of `V n` (`0` if `λ`
is not a fixed point of `υ`).  Theorem OFF-V: `O(λ) = c(λ)` at level `0`, and
`O(λ) = ρ_λ·n + logend(α)` at `λ = V_n(α)` of level `n ≥ 1`.  Below
`V_ω(1) = sup_n V_{n+1}(1)` every level is finite and these offsets are the terms `x·m + k` of
`RstK.top_gen` and `rs_rst`, so the parametric block theorem `blk_gen` applies.

* `V`, `V_normal`, `V_fp`, `range_V_anti`, `V_lt_Om1`; `Vw1` (`Vw1_lt_Om1`, `Vw1_ups`, `fin_level`).
* `lev`, `invV`, `offV`; `topInV`, `rsInV` (the inputs of Lemmas TOP and RS), `specV`.
* `blkV` (**Theorem BLK^O below `V_ω(1)`**), `reach_Vn` (`lh(V_n(α)) = δ + V_n(α)·n + logend(α)`),
  `reach_Phi1` (`lh(Φ_1) = δ + Φ_1·2`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-! ## The hierarchy -/

/-- `V 0 = υ`, `V (n+1) = deriv (V n)`. -/
noncomputable def V : ℕ → Ordinal.{0} → Ordinal.{0}
  | 0 => upsilon
  | n + 1 => deriv (V n)

theorem V_succ (n : ℕ) : V (n + 1) = deriv (V n) := rfl

theorem V_normal : ∀ n, IsNormal (V n)
  | 0 => upsilon_normal
  | n + 1 => isNormal_deriv (V n)

theorem V_strictMono (n : ℕ) : StrictMono (V n) := (V_normal n).strictMono

theorem V_at_zero : ∀ n, V n 0 = 0
  | 0 => upsilon_zero
  | n + 1 => by rw [V_succ, deriv_zero_right]; exact nfp_eq_self (V_at_zero n)

theorem V_one : V 1 = Xi := rfl

theorem V_fp (n : ℕ) (o : Ordinal.{0}) : V n (V (n + 1) o) = V (n + 1) o :=
  deriv_fp (V_normal n) o

theorem mem_range_V_succ (n : ℕ) {a : Ordinal.{0}} : a ∈ Set.range (V (n + 1)) ↔ V n a = a :=
  mem_range_deriv (V_normal n)

theorem range_V_succ_sub (n : ℕ) : Set.range (V (n + 2)) ⊆ Set.range (V (n + 1)) := by
  rintro _ ⟨o, rfl⟩; exact ⟨V (n + 2) o, V_fp (n + 1) o⟩

theorem range_V_anti {p q : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q) :
    Set.range (V q) ⊆ Set.range (V p) := by
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hpq
  clear hpq hp
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
    rw [show p' + 1 + (d + 1) = (p' + d) + 2 by omega]
    refine (range_V_succ_sub (p' + d)).trans ?_
    rw [show p' + d + 1 = p' + 1 + d by omega]; exact ih

theorem ups_fp_of_range {q : ℕ} (hq : 1 ≤ q) {a : Ordinal.{0}} (ha : a ∈ Set.range (V q)) :
    upsilon a = a :=
  (mem_range_V_succ 0).1 (range_V_anti le_rfl hq ha)

theorem V_lt_Om1 : ∀ n : ℕ, ∀ o, o < Om1 → V n o < Om1 := by
  intro n
  induction n with
  | zero => exact ups_lt_Om1
  | succ n ihn =>
    intro o
    induction o using WellFoundedLT.induction with
    | ind o IH =>
    intro ho
    rcases zero_or_succ_or_isSuccLimit o with rfl | ⟨j, rfl⟩ | hl
    · rw [V_at_zero]; exact omega_pos 1
    · have hj : j < Om1 := lt_of_le_of_lt (le_succ j) ho
      rw [V_succ, succ_eq_add_one, deriv_add_one, ← iSup_iterate_eq_nfp]
      have ha : deriv (V n) j + 1 < Om1 := Om1_add_lt (IH j (lt_succ j) hj)
        (lt_trans one_lt_omega0 omega0_lt_omega_one)
      refine Ordinal.iSup_lt_omega_one (fun k => ?_)
      induction k with
      | zero => exact ha
      | succ k ihk => rw [Function.iterate_succ_apply']; exact ihn _ ihk
    · have hc := countable_Iio_of_lt_Om1 ho
      haveI : Countable (Set.Iio o) := hc.to_subtype
      have hs : (⨆ i : Set.Iio o, V (n + 1) i) < Om1 :=
        Ordinal.iSup_lt_omega_one (fun i => IH i i.2 (i.2.trans ho))
      refine lt_of_le_of_lt (((V_normal (n + 1)).isLUB_image_Iio_of_isSuccLimit hl).2 ?_) hs
      rintro _ ⟨i, hi, rfl⟩
      exact le_ciSup (f := fun i : Set.Iio o => V (n + 1) i)
        ⟨Om1, by rintro _ ⟨j, rfl⟩; exact (IH j j.2 (j.2.trans ho)).le⟩ ⟨i, hi⟩

theorem V_Phi1 : V 2 1 = Phi1 := by
  rw [V_succ, show (1 : Ordinal.{0}) = 0 + 1 by simp, deriv_add_one, deriv_zero_right,
    nfp_eq_self (V_at_zero 1), zero_add, V_one]; rfl

/-! ## `V_ω(1)` and the levels -/

/-- `V_ω(1) = sup_n V_{n+1}(1)`. -/
noncomputable def Vw1 : Ordinal.{0} := ⨆ n : ℕ, V (n + 1) 1

theorem Vw1_bdd : BddAbove (Set.range fun n : ℕ => V (n + 1) 1) :=
  ⟨Om1, by rintro _ ⟨n, rfl⟩; exact (V_lt_Om1 _ 1 (lt_trans one_lt_omega0 omega0_lt_omega_one)).le⟩

theorem Vw1_lt_Om1 : Vw1 < Om1 :=
  Ordinal.iSup_lt_omega_one (fun _ => V_lt_Om1 _ 1 (lt_trans one_lt_omega0 omega0_lt_omega_one))

theorem V_le_Vw1 (n : ℕ) : V (n + 1) 1 ≤ Vw1 := le_ciSup Vw1_bdd n

theorem Vw1_ups : upsilon Vw1 = Vw1 := by
  unfold Vw1
  rw [upsilon_normal.map_iSup Vw1_bdd]
  congr 1
  funext n
  exact ups_fp_of_range (by omega) ⟨1, rfl⟩

theorem V_one_pos (n : ℕ) : 0 < V n 1 := by
  have := V_strictMono n (zero_lt_one : (0 : Ordinal.{0}) < 1); rwa [V_at_zero] at this

theorem Vw1_pos : 0 < Vw1 := lt_of_lt_of_le (V_one_pos 1) (V_le_Vw1 0)

theorem Vw1_ri : IsRestartIdx Vw1 := ri_of_fp Vw1_pos Vw1_ups

/-- Below `V_ω(1)` every positive point has a finite level. -/
theorem fin_level {a : Ordinal.{0}} (ha0 : 0 < a) (ha : a < Vw1) :
    ∃ n : ℕ, a ∉ Set.range (V (n + 1)) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, a < V (n + 1) 1 := by
    by_contra hne
    have hne : ∀ n : ℕ, V (n + 1) 1 ≤ a := fun n => not_lt.1 (fun h' => hne ⟨n, h'⟩)
    exact absurd ha (not_lt.2 (ciSup_le' hne))
  refine ⟨n, ?_⟩
  rintro ⟨o, rfl⟩
  rcases eq_or_ne o 0 with rfl | ho
  · rw [V_at_zero] at ha0; exact lt_irrefl _ ha0
  · exact absurd hn (not_lt.2 ((V_strictMono _).monotone (one_le_iff_ne_zero.2 ho)))

open Classical in
/-- The level of `a`: the largest `n` with `a ∈ range (V n)` (`0` if `υ_a ≠ a`). -/
noncomputable def lev (a : Ordinal.{0}) : ℕ :=
  if h : ∃ n : ℕ, a ∉ Set.range (V (n + 1)) then Nat.find h else 0

theorem lev_spec {a : Ordinal.{0}} (h : ∃ n : ℕ, a ∉ Set.range (V (n + 1))) :
    a ∉ Set.range (V (lev a + 1)) ∧ ∀ j : ℕ, 1 ≤ j → j ≤ lev a → a ∈ Set.range (V j) := by
  classical
  have e : lev a = Nat.find h := by unfold lev; rw [dif_pos h]
  rw [e]
  refine ⟨Nat.find_spec h, fun j hj1 hj => ?_⟩
  have := Nat.find_min h (show j - 1 < Nat.find h by omega)
  rw [not_not, show j - 1 + 1 = j by omega] at this
  exact this

theorem lev_ge {a : Ordinal.{0}} (h : ∃ n : ℕ, a ∉ Set.range (V (n + 1))) {q : ℕ} (_hq : 1 ≤ q)
    (ha : a ∈ Set.range (V q)) : q ≤ lev a := by
  by_contra hlt
  exact (lev_spec h).1 (range_V_anti (by omega) (by omega) ha)

theorem lev_eq_zero {a : Ordinal.{0}} (h : ∃ n : ℕ, a ∉ Set.range (V (n + 1))) :
    lev a = 0 ↔ upsilon a ≠ a := by
  constructor
  · intro h0 hfix
    have := (lev_spec h).1
    rw [h0] at this
    exact this ((mem_range_V_succ 0).2 hfix)
  · intro hnf
    by_contra hne
    exact hnf (ups_fp_of_range le_rfl ((lev_spec h).2 1 le_rfl (by omega)))

/-- `invV n a = min{o : V n o = a}`. -/
noncomputable def invV (n : ℕ) (a : Ordinal.{0}) : Ordinal.{0} := sInf {o | V n o = a}

theorem invV_spec {n : ℕ} {a : Ordinal.{0}} (h : a ∈ Set.range (V n)) : V n (invV n a) = a :=
  csInf_mem h

theorem invV_V (n : ℕ) (o : Ordinal.{0}) : invV n (V n o) = o :=
  (V_strictMono n).injective (invV_spec ⟨o, rfl⟩)

/-! ## The offset below `V_ω(1)` -/

/-- The offset (Theorem OFF-V below `V_ω(1)`): `c(λ)` at level `0`, `ρ_λ·n + logend(α)` at
`λ = V_n(α)` of level `n ≥ 1`. -/
noncomputable def offV (a : Ordinal.{0}) : Ordinal.{0} :=
  if lev a = 0 then cL a else upsilon a * ((lev a : ℕ) : Ordinal.{0}) + lg (invV (lev a) a)

theorem offV_zero {a : Ordinal.{0}} (h : lev a = 0) : offV a = cL a := by simp [offV, h]

theorem offV_pos {a : Ordinal.{0}} (h : lev a ≠ 0) :
    offV a = upsilon a * ((lev a : ℕ) : Ordinal.{0}) + lg (invV (lev a) a) := by simp [offV, h]

/-- Facts at a point of level `n ≥ 1`. -/
theorem level_facts {a : Ordinal.{0}} (ha0 : 0 < a) (h : ∃ n : ℕ, a ∉ Set.range (V (n + 1)))
    (hn : lev a ≠ 0) :
    upsilon a = a ∧ V (lev a) (invV (lev a) a) = a ∧ invV (lev a) a ≠ 0 ∧
      invV (lev a) a < a ∧ lg (invV (lev a) a) < a := by
  have hn1 : 1 ≤ lev a := Nat.one_le_iff_ne_zero.2 hn
  have hr := (lev_spec h).2 (lev a) hn1 le_rfl
  have hV := invV_spec hr
  have hfix := ups_fp_of_range hn1 hr
  set α := invV (lev a) a
  have hα0 : α ≠ 0 := by intro h0; rw [h0, V_at_zero] at hV; rw [← hV] at ha0; exact lt_irrefl _ ha0
  have hαa : α < a := by
    refine lt_of_le_of_ne (by have := (V_strictMono (lev a)).id_le α; rwa [hV] at this)
      (fun e => ?_)
    have hfa : V (lev a) a = a := by have := hV; rw [e] at this; exact this
    exact (lev_spec h).1 ((mem_range_V_succ (lev a)).2 hfa)
  exact ⟨hfix, hV, hα0, hαa, lt_of_le_of_lt (lg_le hα0) hαa⟩

theorem offV_lt_succ {a : Ordinal.{0}} (ha0 : 0 < a) (h : ∃ n : ℕ, a ∉ Set.range (V (n + 1)))
    (hn : lev a ≠ 0) : offV a < upsilon a * (((lev a + 1 : ℕ)) : Ordinal.{0}) := by
  obtain ⟨hfix, -, -, -, hlg⟩ := level_facts ha0 h hn
  rw [offV_pos hn, Nat.cast_succ, mul_add_one]
  exact (add_lt_add_iff_left _).2 (by rw [hfix]; exact hlg)

theorem offV_ge {a : Ordinal.{0}} (hn : lev a ≠ 0) :
    upsilon a * ((lev a : ℕ) : Ordinal.{0}) ≤ offV a := by
  rw [offV_pos hn]; exact le_self_add

theorem cL_le_offV {a : Ordinal.{0}} (hl : IsRestartIdx a) (h : ∃ n : ℕ, a ∉ Set.range (V (n + 1))) :
    cL a ≤ offV a := by
  by_cases hn : lev a = 0
  · rw [offV_zero hn]
  · have ha0 : 0 < a := pos_iff_ne_zero.2 hl.1
    obtain ⟨hfix, -⟩ := level_facts ha0 h hn
    rw [cL_fp ha0 hfix]
    refine le_trans ?_ (offV_ge hn)
    rw [hfix]; exact le_mul_left a (by exact_mod_cast Nat.pos_of_ne_zero hn)

theorem offV_lt_δ {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < Vw1) :
    offV l < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have h := fin_level hl0 hlB
  have hU : UpsPt (upsilon (l + ω + 1)) := upsPt_upsilon (lt_of_lt_of_le hl0 (le_self_add.trans
    le_self_add))
  have hlt : upsilon l < upsilon (l + ω + 1) := upsilon_normal.strictMono
    (lt_of_lt_of_le (lt_add_of_pos_right l omega0_pos) le_self_add)
  by_cases hn : lev l = 0
  · rw [offV_zero hn]; exact lt_of_le_of_lt (cL_le_ups hl) hlt
  · exact (offV_lt_succ hl0 h hn).trans (RstK.mul_nat_lt (indec_of_upsPt hU) hlt _)

theorem one_le_offV {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < Vw1) : 1 ≤ offV l :=
  (one_le_cL hl).trans (cL_le_offV hl (fin_level (pos_iff_ne_zero.2 hl.1) hlB))

theorem offV_succ {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < Vw1) (h2 : cL l < 2) :
    offV l = 1 := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have h := fin_level hl0 hlB
  have hnf : upsilon l ≠ l := by
    intro hfix
    rw [cL_fp hl0 hfix] at h2
    have := one_lt_of_ups_fp hl0 hfix
    exact absurd h2 (not_lt.2 (by
      rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num]; exact add_one_le_of_lt this))
  rw [offV_zero ((lev_eq_zero h).2 hnf)]
  exact le_antisymm (lt_succ_iff.1 (by simpa [one_add_one_eq_two] using h2)) (one_le_cL hl)

/-- At `μ = V_q(β)` (`q ≥ 1`): `ρ_μ·q + logend(β) ≤ O(μ)`. -/
theorem offV_ge_range {q : ℕ} (hq : 1 ≤ q) {β : Ordinal.{0}} (hβ0 : 0 < β) (hB : V q β < Vw1) :
    upsilon (V q β) * (q : Ordinal.{0}) + lg β ≤ offV (V q β) := by
  have hμ0 : 0 < V q β := by
    have := V_strictMono q hβ0; rwa [V_at_zero] at this
  have h := fin_level hμ0 hB
  have hge := lev_ge h hq ⟨β, rfl⟩
  have hn : lev (V q β) ≠ 0 := by omega
  have hfix : upsilon (V q β) = V q β := ups_fp_of_range hq ⟨β, rfl⟩
  rcases eq_or_lt_of_le hge with e | hlt
  · rw [offV_pos hn, ← e, invV_V]
  · refine le_trans ?_ (offV_ge hn)
    have h1 : ((q + 1 : ℕ) : Ordinal.{0}) ≤ ((lev (V q β) : ℕ) : Ordinal.{0}) := by exact_mod_cast hlt
    refine le_trans ?_ (mul_le_mul_right h1 _)
    rw [Nat.cast_succ, mul_add_one]
    refine add_le_add le_rfl ?_
    rw [hfix]; exact (lg_le hβ0.ne').trans ((V_strictMono q).id_le β)

/-- **The input of Lemma TOP below `V_ω(1)`.** -/
theorem topInV {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < Vw1) : TopIn offV l := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  have h := fin_level hl0 hlB
  by_cases hn : lev l = 0
  · have hfix : upsilon l ≠ l := (lev_eq_zero h).1 hn
    obtain ⟨ν1, hν1l, hν1⟩ := cL_sep hl
    obtain ⟨ν2, hν2l, hν2⟩ := fix_bound_gen hl0 hfix
    refine ⟨0, cL l, upsilon (max ν1 ν2), by rw [offV_zero hn, tm_zero], cL_lt_ups hl hfix,
      fun _ => one_le_cL hl, upsilon_normal.strictMono (max_lt hν1l hν2l), fun μ hμ hμl hνμ => ?_⟩
    have hνμ' : max ν1 ν2 < μ := upsilon_normal.strictMono.lt_iff_lt.1 hνμ
    have hμf : upsilon μ ≠ μ := fun e =>
      absurd (hν2 μ e hμl) (not_le.2 (lt_of_le_of_lt (le_max_right _ _) hνμ'))
    have hμh := fin_level (pos_iff_ne_zero.2 hμ.1) (hμl.trans hlB)
    rw [offV_zero ((lev_eq_zero hμh).2 hμf), tm_zero]
    exact hν1 μ hμ (lt_of_le_of_lt (le_max_left _ _) hνμ') hμl
  · obtain ⟨hfix, hV, hα0, hαl, hlg⟩ := level_facts hl0 h hn
    set n := lev l with hndef
    set α := invV n l with hαdef
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn
    obtain ⟨β0, hβ0α, hβ0⟩ := lg_sep hα0
    have hx0 : max (V n β0) α < upsilon l := by
      rw [hfix]; exact max_lt (by rw [← hV]; exact V_strictMono n hβ0α) hαl
    refine ⟨n, lg α, max (V n β0) α, by rw [offV_pos hn, tm], by rw [hfix]; exact hlg,
      fun h0 => absurd h0 hn, hx0, fun μ hμ hμl hx0μ => ?_⟩
    have hμ0 : 0 < μ := pos_iff_ne_zero.2 hμ.1
    have hμh := fin_level hμ0 (hμl.trans hlB)
    rw [tm]
    by_cases hm : lev μ = 0
    · rw [offV_zero hm]
      refine lt_of_lt_of_le (cL_lt_ups hμ ((lev_eq_zero hμh).1 hm)) (le_trans ?_ le_self_add)
      exact le_mul_left _ (by exact_mod_cast hn1)
    obtain ⟨hμfix, hVμ, -, -, -⟩ := level_facts hμ0 hμh hm
    rcases lt_trichotomy (lev μ) n with hlt | heq | hgt
    · refine lt_of_lt_of_le (offV_lt_succ hμ0 hμh hm) (le_trans ?_ le_self_add)
      exact mul_le_mul_right (by exact_mod_cast hlt) _
    · rw [heq] at hVμ
      rw [offV_pos hm, heq]
      refine (add_lt_add_iff_left _).2 (hβ0 _ ?_ ?_)
      · have : V n β0 < V n (invV n μ) :=
          calc V n β0 ≤ max (V n β0) α := le_max_left _ _
            _ < upsilon μ := hx0μ
            _ = μ := hμfix
            _ = V n (invV n μ) := hVμ.symm
        exact (V_strictMono n).lt_iff_lt.1 this
      · have : V n (invV n μ) < V n α := by rw [hVμ, hV]; exact hμl
        exact (V_strictMono n).lt_iff_lt.1 this
    · exfalso
      have hr := (lev_spec hμh).2 (n + 1) (by omega) (by omega)
      have hfμ : V n μ = μ := (mem_range_V_succ n).1 hr
      have : μ < α := by
        have h1 : V n μ < V n α := by rw [hfμ, hV]; exact hμl
        exact (V_strictMono n).lt_iff_lt.1 h1
      rw [hμfix] at hx0μ
      exact absurd (lt_of_le_of_lt (le_max_right _ _) hx0μ) (not_lt.2 this.le)

/-- Restarts `V_q(β)` with `logend(β) ≥ r` are cofinal below `V_q(a)`, `a` a limit, `r < logend(a)`. -/
theorem targets_V {q : ℕ} (hq : 1 ≤ q) {a l r : Ordinal.{0}} (hVa : V q a = l) (hlB : l < Vw1)
    (hlim : IsSuccLimit a) (hr : r < lg a) :
    ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ tm q r (upsilon μ) ≤ offV μ := by
  intro ν hν
  rw [← hVa] at hν
  obtain ⟨_, ⟨β', hβ', rfl⟩, hνβ'⟩ :=
    (lt_isLUB_iff ((V_normal q).isLUB_image_Iio_of_isSuccLimit hlim)).1 hν
  have ha0 : a ≠ 0 := hlim.ne_bot
  obtain ⟨β, hβ, hβa, hrβ⟩ := lg_dense ha0 hr (max β' r)
    (max_lt hβ' (lt_of_lt_of_le hr (lg_le ha0)))
  have hβ0 : 0 < β := lt_of_le_of_lt zero_le hβ
  have hμ0 : 0 < V q β := by have := V_strictMono q hβ0; rwa [V_at_zero] at this
  have hμl : V q β < l := by rw [← hVa]; exact V_strictMono q hβa
  have hfix : upsilon (V q β) = V q β := ups_fp_of_range hq ⟨β, rfl⟩
  refine ⟨V q β, ri_of_fp hμ0 hfix, hνβ'.trans (V_strictMono q (lt_of_le_of_lt (le_max_left _ _) hβ)),
    hμl, ?_⟩
  rw [tm]
  exact le_trans (add_le_add le_rfl hrβ) (offV_ge_range hq hβ0 (hμl.trans hlB))

/-- **The input of Lemma RS below `V_ω(1)`.** -/
theorem rsInV {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < Vw1) (h2 : 2 ≤ cL l) :
    RsIn offV l := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have h := fin_level hl0 hlB
  have hconst : ∀ z < cL l, ∃ (m : ℕ) (k : Ordinal.{0}), z = tm m k (upsilon l) ∧ k < upsilon l ∧
      ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ tm m k (upsilon μ) ≤ offV μ := by
    intro z hz
    refine ⟨0, z, (tm_zero z _).symm, lt_of_lt_of_le hz (cL_le_ups hl), fun ν hν => ?_⟩
    have hz' : max z 1 < cL l := max_lt hz (lt_of_lt_of_le one_lt_two h2)
    obtain ⟨μ, hμ, hνμ, hμl, hzμ⟩ := cL_dense hl (le_max_right z 1) hz' ν hν
    refine ⟨μ, hμ, hνμ, hμl, ?_⟩
    rw [tm_zero]
    exact ((le_max_left z 1).trans hzμ).trans
      (cL_le_offV hμ (fin_level (pos_iff_ne_zero.2 hμ.1) (hμl.trans hlB)))
  intro z hz
  by_cases hn : lev l = 0
  · rw [offV_zero hn] at hz; exact hconst z hz
  obtain ⟨hfix, hV, hα0, hαl, hlg⟩ := level_facts hl0 h hn
  set n := lev l with hndef
  set α := invV n l with hαdef
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn
  rw [offV_pos hn, hfix] at hz
  -- `z = l·q + r`
  have hdm : l * (z / l) + z % l = z := div_add_mod z l
  have hr : z % l < l := mod_lt z hl.1
  have hzq : z / l < ((n + 1 : ℕ) : Ordinal.{0}) := by
    refine (lt_mul_iff_div_lt hl.1).1 ?_
    rw [Nat.cast_succ, mul_add_one]
    exact lt_of_lt_of_le hz (add_le_add le_rfl (le_of_lt hlg))
  obtain ⟨q, hq⟩ := lt_omega0.1 (hzq.trans (natCast_lt_omega0 _))
  rw [hq] at hdm hzq
  have hqn : q ≤ n := by exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast hzq)
  have hE : InE l := inE_of_fp hl0 hfix
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · rw [Nat.cast_zero, mul_zero, zero_add] at hdm
    exact hconst z (by rw [cL_fp hl0 hfix, ← hdm]; exact hr)
  refine ⟨q, z % l, by rw [tm, hfix, hdm], by rw [hfix]; exact hr, ?_⟩
  rcases eq_or_lt_of_le hqn with rfl | hqlt
  · -- `q = n`: targets `V_n(β)` below `V_n(α)`
    have hrα : z % l < lg α := by
      rw [← hdm] at hz; exact (add_lt_add_iff_left _).1 hz
    have hαlim : IsSuccLimit α := by
      refine Ordinal.isSuccLimit_iff.2 ⟨hα0, isSuccPrelimit_iff_omega0_dvd.2 ?_⟩
      have := (le_lg_iff hα0 1).1 (one_le_iff_ne_zero.2 (fun h0 => by
        rw [h0] at hrα; exact absurd hrα (not_lt.2 zero_le)))
      rwa [opow_one] at this
    exact targets_V hn1 hV hlB hαlim hrα
  · -- `1 ≤ q < n`: targets `V_q(β)` below `V_q(λ) = λ`
    have hVq : V q l = l := by
      have hr' := range_V_anti (show 1 ≤ q + 1 by omega) (show q + 1 ≤ n by omega)
        ((lev_spec h).2 n hn1 le_rfl)
      exact (mem_range_V_succ q).1 hr'
    have hllim : IsSuccLimit l := by
      obtain ⟨p, hp⟩ := (ri_iff.1 hl).2
      have hp0 : p ≠ 0 := by intro h0; rw [h0, mul_zero] at hp; exact hl.1 hp
      rw [hp]
      exact isSuccLimit_mul_left (isSuccLimit_mul_right omega0_pos isSuccLimit_omega0)
        (pos_iff_ne_zero.2 hp0)
    have hlgl : lg l = l := by
      refine le_antisymm (lg_le hl.1) ((le_lg_iff hl.1 l).2 ?_)
      unfold InE at hE; rw [hE]
    exact targets_V hq0 hVq hlB hllim (by rw [hlgl]; exact hr)

/-- `offV` is an offset specification up to `V_ω(1)`. -/
theorem specV : OffSpec offV Vw1 :=
  ⟨(ri_iff.1 Vw1_ri).2, Vw1_lt_Om1, fun _ hl hlB => offV_lt_δ hl hlB,
    fun _ hl hlB => one_le_offV hl hlB, fun _ hl hlB => topInV hl hlB,
    fun _ hl hlB h2 => offV_succ hl hlB h2, fun _ hl hlB h2 => rsInV hl hlB h2⟩

/-- **Theorem BLK^O below `V_ω(1)`** in `R₂^C` (the project's Theorem BLK^O with the closed form of
Theorem OFF-V for every restart index below `V_ω(1)`): (i) the `<₂`-pairs with right end below
`V_ω(1) = υ_{V_ω(1)}` are exactly `(υ_{μ+ω·j}, υ_{μ+ω·j+1})`, `j ≥ 1`, `μ < V_ω(1)` zero or a restart
index; (ii) a restart `ρ_λ` (`λ < V_ω(1)`) has no `<₁`-predecessor and no `<₂`-successor, and
`{γ : ρ_λ ≤₁ γ} = [ρ_λ, δ_λ + O(λ)]` with `O(V_n(α)) = V_n(α)·n + logend(α)` at level `n ≥ 1` and
`O(λ) = c(λ)` at level `0`; (iii) every point below `V_ω(1)` that is not a `υ`-point has its `R₁⁺`
reach. -/
theorem blkV :
    (∀ c d, c < d → d < Vw1 → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < Vw1 ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < Vw1 →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + offV l)) ∧
    (∀ α < Vw1, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) := by
  have h := blk_gen specV
  rw [Vw1_ups] at h
  exact h

/-- `lh(V_n(α)) = δ + V_n(α)·n + logend(α)` at a point `V_n(α)` of level `n ≥ 1` below `V_ω(1)`
(`α ≥ 1`, `α < V_n(α)`). -/
theorem reach_Vn {n : ℕ} (hn : 1 ≤ n) {α : Ordinal.{0}} (hα0 : α ≠ 0) (hαV : α < V n α)
    (hB : V n α < Vw1) :
    IsReach R2C (V n α) (upsilon (V n α + ω + 1) + (V n α * (n : Ordinal.{0}) + lg α)) := by
  have h0 : 0 < V n α := by
    have := V_strictMono n (pos_iff_ne_zero.2 hα0); rwa [V_at_zero] at this
  have hfix := ups_fp_of_range hn ⟨α, rfl⟩
  have h := fin_level h0 hB
  have hlev : lev (V n α) = n := by
    refine le_antisymm ?_ (lev_ge h hn ⟨α, rfl⟩)
    by_contra hlt
    have hr := (lev_spec h).2 (n + 1) (by omega) (by omega)
    have hf : V n (V n α) = V n α := (mem_range_V_succ n).1 hr
    exact absurd hf (ne_of_gt (V_strictMono n hαV))
  have hR := (blkV.2.1 _ (ri_of_fp h0 hfix) hB).2.2
  rwa [offV_pos (by omega), hlev, invV_V, hfix] at hR

/-- `lh(Φ_1) = δ + Φ_1·2` (`Φ_1 = V_2(1)`). -/
theorem reach_Phi1 : IsReach R2C Phi1 (upsilon (Phi1 + ω + 1) + Phi1 * 2) := by
  have hB : V 2 1 < Vw1 := by
    refine lt_of_lt_of_le ?_ (V_le_Vw1 2)
    have h3 : (1 : Ordinal.{0}) < V 3 1 :=
      one_lt_of_ups_fp (V_one_pos 3) (ups_fp_of_range (by norm_num) ⟨1, rfl⟩)
    have := V_strictMono 2 h3
    rwa [V_fp 2 1] at this
  have hα : (1 : Ordinal.{0}) < V 2 1 := by
    rw [V_Phi1]; exact lt_of_lt_of_le one_lt_omega0 omega_lt_Phi1.le
  have h := reach_Vn (show 1 ≤ 2 by norm_num) one_ne_zero hα hB
  have hlg1 : lg (1 : Ordinal.{0}) = 0 := by exact_mod_cast lg_nat (n := 1) one_ne_zero
  rw [V_Phi1, hlg1, add_zero] at h
  exact_mod_cast h

end Googology.Trans.PoR.InaccPsi.R2
