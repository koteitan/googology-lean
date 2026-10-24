import Googology.Trans.PoR.InaccPsi.R2.GhU

/-!
# THE CODE `ε_{Ω₁+1}`: the union of all layers `gfB c`, `c < ε_{Ω₁+1}`, with top `Γ_{x+1+ε_{x+1}}`

The layers `Gf.gfB c` (`R2.GfTow`, top `ϑˣ(Ω₁·Ω₁ + 1 + c(x))`) for all codes `c < ε_{Ω₁+1}` form a union step
(`R2.GhU`) with the offset `l(x) = ε_{x+1}`:

* `gh_eN_pi` (**Lemma EXACT for `ε_{x+1}` for all bases**, `Bases σ ρ` only: `ε_{ρ+1} = ϑ^ρ(Ω₁)`, `vt_Om1_eq`,
  membership from `vt_Om1_mem`, the clause `π(ϑ^ρ(ξ)) = ϑ^σ(π(ξ))` for `ξ < Ω₂`, `pi_vt_two`, and `π(Ω₁) = Ω₁`),
  `gh_eNm_pi` (the same for `ε_{x+1}·n`);
* `gh_lg_eN` (`logend(ε_{x+1}) = ε_{x+1}`), `gh_lg_eNm`, `gh_eN_lim`, `gh_eN_lt_gq0` (**`ε_{x+1} < Γ_{x+1}`**),
  `gh_eNm_lt_gq0`;
* the `Ω₁`-tower `ghTw k` (`1, Ω₁, Ω₁^{Ω₁}, …`), `ghTw_lt`, `ghTw_gtc` (gate `≤ 1`), `ghTw_cof` (**every `ν < ε_{x+1}`
  is below the reading of some `ghTw k`**, at every `ε`-number `x`);
* `ghF0` (the data), `ghEB` (**THE GATED LAYER OF THE CODE `ε_{Ω₁+1}`**: gate `0`, top `ϑˣ(Ω₁·Ω₁ + ε_{x+1}) =
  Γ_{x+1+ε_{x+1}}` at every `ε`-number base), `ghEB_E`, `ghEB_top`.

No new axiom.  New definitions: `ghTw`, `ghF0`, `ghEB`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ly Lu
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf

/-! ## `ε_{x+1}` -/

/-- **Lemma EXACT for `ε_{x+1}` for every pair of bases**: `ε_{ρ+1} ∈ Tᵖ[σ]` and `π_{σ,ρ}(ε_{ρ+1}) = ε_{σ+1}`
(`ε_{ρ+1} = ϑ^ρ(Ω₁)`; no `υ`-point hypothesis). -/
theorem gh_eN_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) : eN ρ ∈ TB ρ σ ∧ pi σ ρ (eN ρ) = eN σ := by
  obtain ⟨hσE, hρE, hσρ, hρ1⟩ := hB
  have hB' : Bases σ ρ := ⟨hσE, hρE, hσρ, hρ1⟩
  have hσ1 : σ < Om1 := hσρ.trans hρ1
  have eρ : vt ρ Om1 = eN ρ := by
    have := vt_Om1_eq hρE hρ1 0
    rwa [Nat.cast_zero, add_zero, zero_add, eK_one] at this
  have eσ : vt σ Om1 = eN σ := by
    have := vt_Om1_eq hσE hσ1 0
    rwa [Nat.cast_zero, add_zero, zero_add, eK_one] at this
  obtain ⟨hvT, hPar, -⟩ := vt_Om1_mem hρE hρ1 0
  rw [Nat.cast_zero, add_zero] at hvT hPar
  have h1σ : (1 : Ordinal.{0}) < σ := lu_one_lt_E hσE
  refine ⟨?_, ?_⟩
  · rw [← eρ]
    refine ⟨hvT, fun p hp => ?_⟩
    rcases hPar hp with rfl | rfl
    · exact Set.mem_Iio.2 hσE.pos
    · exact Set.mem_Iio.2 h1σ
  · obtain ⟨hOT, hOp⟩ := pi_Om1 hB'
    rw [← eρ, pi_vt_two hB' hOT tqc_Om1_lt_OmTwo, hOp, eσ]

theorem gh_eNm_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (j : ℕ) :
    eN ρ * (j : Ordinal.{0}) ∈ TB ρ σ ∧ pi σ ρ (eN ρ * (j : Ordinal.{0})) = eN σ * j :=
  pi_eNm hB (gh_eN_pi hB).1 (gh_eN_pi hB).2 j

theorem gh_lg_eN (x : Ordinal.{0}) : lg (eN x) = eN x := by
  have h := Ge.lg_add_opow (u := 0) (e := eN x) (dvd_zero _)
  rwa [zero_add, show ω ^ eN x = eN x from eN_E x] at h

theorem gh_eN_lim (x : Ordinal.{0}) : IsSuccLimit (eN x) := by
  have hpos : 0 < eN x := (eN_E x).pos
  refine ⟨not_isMin_iff_ne_bot.2 hpos.ne', isSuccPrelimit_iff_omega0_dvd.2 ?_⟩
  rw [← show ω ^ eN x = eN x from eN_E x]
  calc ω = ω ^ (1 : Ordinal.{0}) := (opow_one ω).symm
    _ ∣ ω ^ eN x := opow_dvd_opow ω (one_le_iff_pos.2 hpos)

/-- `logend(ε_{x+1}·(n+1)) = ε_{x+1}`, and `ε_{x+1}·(n+1) = ε_{x+1}·n + ω^{ε_{x+1}}`. -/
theorem gh_lg_eNm (x : Ordinal.{0}) (n : ℕ) :
    eN x * ((n + 1 : ℕ) : Ordinal.{0}) = eN x * (n : Ordinal.{0}) + ω ^ eN x ∧
      ω ^ eN x ∣ eN x * (n : Ordinal.{0}) ∧ lg (eN x * ((n + 1 : ℕ) : Ordinal.{0})) = eN x := by
  have e1 : eN x * ((n + 1 : ℕ) : Ordinal.{0}) = eN x * (n : Ordinal.{0}) + ω ^ eN x := by
    rw [Nat.cast_succ, mul_add_one, show ω ^ eN x = eN x from eN_E x]
  have e2 : ω ^ eN x ∣ eN x * (n : Ordinal.{0}) := by
    rw [show ω ^ eN x = eN x from eN_E x]; exact dvd_mul_right _ _
  exact ⟨e1, e2, by rw [e1]; exact Ge.lg_add_opow e2⟩

/-- **`ε_{x+1} < Γ_{x+1}`.** -/
theorem gh_eN_lt_gq0 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : eN x < gq 0 x := by
  have h1 := eN_le_gT hx hx1 0
  have h2 := gT_lt_lgG hx hx1 0
  have e : gq 0 x = Lp.gk 0 x := by rw [← gq_nat, Nat.cast_zero]
  rw [e, Ga.gk_zero_eq hx hx1]
  exact h1.trans_lt h2

theorem gh_eNm_lt_gq0 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (j : ℕ) :
    eN x * (j : Ordinal.{0}) < gq 0 x := by
  have hE := (gfq0_facts hx hx1).2.2.2
  exact hE.mul_lt (gh_eN_lt_gq0 hx hx1) ((natCast_lt_omega0 j).trans (omega0_lt_inE hE))

/-! ## The `Ω₁`-tower: cofinal readings -/

/-- The `Ω₁`-tower `1, Ω₁, Ω₁^{Ω₁}, …` (codes below `ε_{Ω₁+1}` with gate `≤ 1`). -/
noncomputable def ghTw (k : ℕ) : Ordinal.{0} := (fun l : Ordinal.{0} => Om1 ^ l)^[k] 1

theorem ghTw_succ (k : ℕ) : ghTw (k + 1) = Om1 ^ ghTw k := Function.iterate_succ_apply' _ _ _

theorem ghTw_lt : ∀ k : ℕ, ghTw k < gfE
  | 0 => gf_one_lt_Om1.trans Om1_lt_eW
  | k + 1 => by rw [ghTw_succ]; exact Om1_pow_lt_eW (ghTw_lt k)

theorem ghTw_gtc : ∀ k : ℕ, gtc (ghTw k) ≤ 1
  | 0 => by show gtc 1 ≤ 1; rw [(rdc_const gf_one_lt_Om1 0).2]
  | k + 1 => by rw [ghTw_succ, (rdc_pow (ghTw_lt k) 0).2]; exact max_le (ghTw_gtc k) le_rfl

theorem ghTw_rdc (x : Ordinal.{0}) (k : ℕ) : rdc (ghTw (k + 1)) x = x ^ rdc (ghTw k) x := by
  rw [ghTw_succ, (rdc_pow (ghTw_lt k) x).1]

/-- **The tower readings are cofinal in `ε_{x+1}`**: `(ω^·)^[k](x+1) ≤ rdc (ghTw (k+2)) x`. -/
theorem ghTw_ge {x : Ordinal.{0}} (hx : InE x) : ∀ k : ℕ,
    (fun a : Ordinal.{0} => ω ^ a)^[k] (x + 1) ≤ rdc (ghTw (k + 2)) x
  | 0 => by
    show x + 1 ≤ rdc (ghTw (0 + 1 + 1)) x
    rw [ghTw_rdc, ghTw_rdc, show ghTw 0 = 1 from rfl, (rdc_const gf_one_lt_Om1 x).1, opow_one]
    have hω := omega0_lt_inE hx
    have h11 : (1 : Ordinal.{0}) + 1 ≤ x := by
      rw [show (1 : Ordinal.{0}) + 1 = ((2 : ℕ) : Ordinal.{0}) by norm_num]
      exact ((natCast_lt_omega0 2).trans hω).le
    calc x + 1 ≤ x + x := add_le_add le_rfl (one_le_iff_pos.2 hx.pos)
      _ = x * (1 + 1) := by rw [mul_add_one, mul_one]
      _ ≤ x * x := mul_le_mul_left' h11 x
      _ = x ^ ((1 : Ordinal.{0}) + 1) := by rw [opow_add, opow_one]
      _ ≤ x ^ x := opow_le_opow_right hx.pos h11
  | k + 1 => by
    rw [Function.iterate_succ_apply', ghTw_rdc x (k + 2)]
    calc ω ^ ((fun a : Ordinal.{0} => ω ^ a)^[k] (x + 1)) ≤ ω ^ rdc (ghTw (k + 2)) x :=
          opow_le_opow_right omega0_pos (ghTw_ge hx k)
      _ ≤ x ^ rdc (ghTw (k + 2)) x := opow_le_opow_left _ (omega0_lt_inE hx).le

theorem ghTw_cof {x : Ordinal.{0}} (hx : InE x) {ν : Ordinal.{0}} (hν : ν < eN x) :
    ∃ k : ℕ, ν < rdc (ghTw k) x := by
  obtain ⟨k, hk⟩ := lt_nfp_iff.1 hν
  exact ⟨k + 2, hk.trans_le (ghTw_ge hx k)⟩

/-! ## The union at the code `ε_{Ω₁+1}` -/

theorem gh_gtc0_lt : gtc (0 : Ordinal.{0}) < gfE := by rw [gtc_zero]; exact eW_E.pos

/-- **The data of the union at the code `ε_{Ω₁+1}`**: the family `gfB c`, `c < ε_{Ω₁+1}` (offsets `1 + c(x)`), the
offset `ε_{x+1}`, gate `0`. -/
noncomputable def ghF0 : GhUF 0 where
  I := {c : Ordinal.{0} // c < gfE}
  K := fun c => gfB c.1 c.2
  gi := fun c => gtc c.1
  o := fun c x => 1 + rdc c.1 x
  l := eN
  lp := fun _ => 0
  i0 := ⟨0, eW_E.pos⟩
  ip := ⟨0, eW_E.pos⟩
  g_le := fun c => (gfB_g c.2).le
  gi0 := gtc_zero
  gip := gtc_zero.le
  E_eq := fun c x hx hx1 hg => gfB_E c.2 hx hx1 hg
  o_lt := fun c x hx _ _ hg => gfO_lt c.2 hx hg
  l_lt := fun x hx hx1 _ => gh_eN_lt_gq0 hx hx1
  lim := fun x _ _ _ => gh_eN_lim x
  cof := fun x hx _ _ ν hν => by
    obtain ⟨k, hk⟩ := ghTw_cof hx hν
    exact ⟨⟨ghTw k, ghTw_lt k⟩, (ghTw_gtc k).trans_lt (lu_one_lt_E hx), hk.le.trans le_add_self⟩
  pi := fun _ _ _ _ hB _ => gh_eN_pi hB
  dec := fun x _ _ _ => by
    refine ⟨?_, dvd_zero _, (eN_E x).pos⟩
    rw [gh_lg_eN, zero_add, show ω ^ eN x = eN x from eN_E x]
  lp_le := fun _ _ _ _ => zero_le
  pkg := fun ρ τ δ h hg => GhPkg.congr h (GhPkg.of_img h.pkg_eN) (fun y _ _ _ => (gh_lg_eN y).symm) hg

/-- **THE GATED LAYER OF THE CODE `ε_{Ω₁+1}`**: gate `0`, top `ϑˣ(Ω₁·Ω₁ + ε_{x+1}) = Γ_{x+1+ε_{x+1}}`. -/
noncomputable def ghEB : GdB := ghLimB ghF0

theorem ghEB_g : ghEB.g = 0 := rfl

theorem ghEB_E (x : Ordinal.{0}) : ghEB.K.E x = gq (eN x) x := rfl

theorem ghEB_top {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : ghEB.K.sys.top x = gq (eN x) x := by
  have hg : (0 : Ordinal.{0}) < x := hx.pos
  rw [ghEB.K.top_eq x hx hx1 hg, ghEB_E]
  exact (ghF0.top_facts hx hx1 hg).2.2.2.1

end Googology.Trans.PoR.InaccPsi.R2.Gh
