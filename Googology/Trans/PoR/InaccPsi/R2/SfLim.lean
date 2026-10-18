import Googology.Trans.PoR.InaccPsi.R2.SfPv

/-!
# The limit step of the shift (`TpLimMove`) is proved, so the shift reduces to (S1)

`θ = ψ_{Ω₂}(Ω_ω)`, `A_η = Ω_ω + θ·η`, `P(η) = ψ_{Ω₁}(A_η)`, `ι` the index of Theorem GEN
(`υ_{ι(η)} = P(η)`), `B_n = Bc.bcB S n`, `c = Ω_ω + P'·ω`.  A name `g` is *own* when
`A_g ∈ Cl(A_g, P(g))`.

* `sfOwn_nat`, `sfIota_nat`, `sfIota_omega`: for an own `g`, every `g + k` is own, `ι(g + k) = ι(g) + k`
  and `ι(g + ω) = ι(g) + ω`;
* `sfThW`: the normal form `φ(0, θ + 1)` of `θ·ω` (`σ` fixes it, it lies in every `Cl(a, b)`, `a > Ω_ω`);
* `sfLimMove` (**(S3) `TpLimMove S`, no hypothesis beyond Theorem GEN**): with `υ_{μ+ω·j} = P(g)`,
  `g` good (so `υ_{μ+ω·(j+1)} = P(g + ω)`), `sfB_add` at `δ = ω` gives `B_n(P(g)) = P(g')`,
  `B_n(P(g + ω)) = P(g' + ω)` with `g'` own; the hypothesis at `k = 0` gives `ι(g') = μ' + ω·j`, so
  `P(g' + ω) = υ_{μ'+ω·(j+1)}`;
* `sfShift`: **`TpRstMove S` alone gives `TpShift S`**.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

/-! ## The index along an own name -/

/-- Every `g + k` is own when `g` is. -/
theorem sfOwn_nat {g : Ordinal.{0}}
    (h : ConjT.Aη S g ∈ S.CSet (ConjT.Aη S g) (S.psi (ConjT.Aη S g) (Om 1))) :
    ∀ k : ℕ, ConjT.Aη S (g + k) ∈ S.CSet (ConjT.Aη S (g + k)) (S.psi (ConjT.Aη S (g + k)) (Om 1))
  | 0 => by simpa using h
  | k + 1 => by
    have ih := sfOwn_nat h k
    have e : ConjT.Aη S (g + ((k + 1 : ℕ) : Ordinal.{0})) = ConjT.Aη S (g + k) + ConjT.th S := by
      rw [ConjT.A_succ, Nat.cast_succ, add_assoc]
    rw [e]
    exact sfOwn_th ih (ConjT.OmW_le_A S _)

/-- `ι(g + k) = ι(g) + k` for an own `g`. -/
theorem sfIota_nat {g : Ordinal.{0}}
    (h : ConjT.Aη S g ∈ S.CSet (ConjT.Aη S g) (S.psi (ConjT.Aη S g) (Om 1))) :
    ∀ k : ℕ, Bt.iota S (g + k) = Bt.iota S g + k
  | 0 => by simp
  | k + 1 => by
    rw [Nat.cast_succ, ← add_assoc, Bt.iota_good (sfGood_of_own (sfOwn_nat h k)), sfIota_nat h k,
      add_assoc]

/-- `ι(g + ω) = ι(g) + ω` for an own `g`. -/
theorem sfIota_omega {g : Ordinal.{0}}
    (h : ConjT.Aη S g ∈ S.CSet (ConjT.Aη S g) (S.psi (ConjT.Aη S g) (Om 1))) :
    Bt.iota S (g + ω) = Bt.iota S g + ω := by
  have hlim : IsSuccLimit (g + ω) := isSuccLimit_add g isSuccLimit_omega0
  rw [Bt.iota_limit hlim]
  apply le_antisymm
  · refine ciSup_le' fun e => ?_
    obtain ⟨d, hd, hed⟩ := (lt_add_iff_of_isSuccLimit isSuccLimit_omega0).1 e.2
    obtain ⟨k, rfl⟩ := lt_omega0.1 hd
    calc Bt.iota S e.1 ≤ Bt.iota S (g + k) := Bt.iota_mono _ _ hed.le
      _ = Bt.iota S g + k := sfIota_nat h k
      _ ≤ Bt.iota S g + ω := (add_le_add_iff_left _).2 (natCast_lt_omega0 k).le
  · by_contra hlt
    push Not at hlt
    obtain ⟨d, hd, hk⟩ := (lt_add_iff_of_isSuccLimit isSuccLimit_omega0).1 hlt
    obtain ⟨k, rfl⟩ := lt_omega0.1 hd
    have hmem : g + (k : Ordinal.{0}) < g + ω := (add_lt_add_iff_left _).2 (natCast_lt_omega0 k)
    have := le_ciSup (Bt.iota_bdd (S := S) (g + ω)) ⟨g + k, hmem⟩
    rw [sfIota_nat h k] at this
    exact absurd hk (not_lt.2 this)

/-! ## The term of `θ·ω` -/

/-- `θ·ω = φ(0, θ + 1)`. -/
def sfThW : Term := phi Term.zero (add sfThT tOne)

theorem sfCmp_tOne_ThT : cmp tOne sfThT = .lt := by
  show cmp (phi Term.zero Term.zero) sfThT = .lt
  rw [cmp_phi_left_lt (t := sfThT) rfl (cmp_zero_left (by simp [sfThT]))]
  exact cmp_zero_left (by simp [sfThT])

theorem sfCmp_ThT_ThW : cmp sfThT sfThW = .lt := by
  show cmp sfThT (phi Term.zero (add sfThT tOne)) = .lt
  rw [cmp_phi_right_gt (t := sfThT) rfl (cmp_zero_right (by simp [sfThT])),
    cmp_add_right sfThT tOne (t := sfThT) rfl, cmp_self]
  simp

theorem sfNF_ThT_one : NF (add sfThT tOne) :=
  ⟨sfThT_NF, NF_tOne, rfl, tOne_ne_zero, by
    rw [show head tOne = tOne from rfl, sfCmp_tOne_ThT]; simp⟩

theorem sfThW_NF : NF sfThW := by
  refine ⟨trivial, sfNF_ThT_one, cmp_zero_left (by simp), ?_⟩
  show cmp (add sfThT tOne) sfThW = .lt
  rw [cmp_add_left sfThT tOne (t := sfThW) rfl, sfCmp_ThT_ThW]; simp

theorem sfThW_free : bcFree sfThW := ⟨trivial, sfThT_free, bcFree_tOne⟩

theorem sfThW_val (S : InaccSeq.{0}) : val S sfThW = ConjT.th S * ω := by
  show veblen (val S Term.zero) (val S sfThT + val S tOne) = _
  rw [sfThT_val, val_tOne, show val S Term.zero = 0 from rfl, veblen_zero_apply, opow_add,
    opow_one, sfTh_opow]

/-! ## (S3) -/

/-- **(S3) `TpLimMove S` holds** (no hypothesis beyond Theorem GEN). -/
theorem sfLimMove : Tp.TpLimMove S := by
  intro n μ μ' j hμ hlo hhi hk
  have hμ0 : μ ≠ 0 := hμ.1
  have hj : μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) = μ + ω * (j : Ordinal.{0}) + ω := by
    rw [Nat.cast_succ, mul_add_one, add_assoc]
  have hj' : μ' + ω * ((j + 1 : ℕ) : Ordinal.{0}) = μ' + ω * (j : Ordinal.{0}) + ω := by
    rw [Nat.cast_succ, mul_add_one, add_assoc]
  set ζ0 := μ + ω * (j : Ordinal.{0}) with hζ0
  have h1 : 1 ≤ ζ0 := Order.one_le_iff_ne_zero.2 fun h0 => hμ0 (by
    rw [hζ0] at h0; exact (add_eq_zero_iff.1 h0).1)
  have hL : Bc.bcC S (n + 1) = Pv S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0})) :=
    Lw.lw_L_eq S _
  have hιL : ζ0 + ω < Bt.iota S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0})) := by
    rw [← hj]; exact Cd.cd_lt_iota (hL ▸ hhi)
  have hι1 : ζ0 + 1 ≤ Bt.iota S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0})) :=
    ((add_lt_add_iff_left ζ0).2 one_lt_omega0).le.trans hιL.le
  obtain ⟨g, hg, hιg, hpg, -⟩ := Tp.tpUps_pv (S := S) h1 hι1
  have hpgω : Pv S (g + ω) = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) := by
    have hlt : Pv S g < Bc.bcC S (n + 1) := by
      rw [hpg]
      refine lt_of_le_of_lt ?_ hhi
      exact upsilon_normal.strictMono.monotone (by rw [hj]; exact le_self_add)
    have hown := sfOwn hg (sfA_lt hlt).2
    rw [show Pv S (g + ω) = upsilon (Bt.iota S (g + ω)) from (Bt.ups_iota S (g + ω)).symm,
      sfIota_omega hown, hιg, hj]
  have hlo' : Bc.bcC S n ≤ Pv S g := by
    rw [hpg]; exact hlo.trans (upsilon_normal.strictMono.monotone le_self_add)
  have hhi' : Pv S (g + ω) < Bc.bcC S (n + 1) := by rw [hpgω]; exact hhi
  obtain ⟨ζ', hown', hB0, hBω⟩ := sfB_add hg sfThW_NF sfThW_free (sfThW_val S)
    (fun a b h => ConjT.th_omega_mem S h) hlo' hhi'
  have hk0 := hk 0
  simp only [Nat.cast_zero, add_zero] at hk0
  rw [← hpg, hB0] at hk0
  have hι' : Bt.iota S (Om ω + Nc.ncPp S * ω + ζ') = μ' + ω * (j : Ordinal.{0}) := by
    have := (Bt.ups_iota S (Om ω + Nc.ncPp S * ω + ζ')).trans hk0
    exact Tp.tpUps_inj this
  rw [← hpgω, hBω, show Pv S (Om ω + Nc.ncPp S * ω + ζ' + ω) =
      upsilon (Bt.iota S (Om ω + Nc.ncPp S * ω + ζ' + ω)) from (Bt.ups_iota S _).symm,
    sfIota_omega hown', hι', hj']

/-- **`TpRstMove S` alone gives the shift `TpShift S`** ((S2), (S3) proved). -/
theorem sfShift (h1 : Tp.TpRstMove S) : Tp.TpShift S :=
  Tp.tpShift_of_pv h1 sfPvStep sfLimMove

end Googology.Trans.PoR.InaccPsi.R2.Sf
