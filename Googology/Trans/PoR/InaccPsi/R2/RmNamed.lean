import Googology.Trans.PoR.InaccPsi.R2.RmSat

/-!
# Range restarts below `L(n+1)` and `L(ω)`, and what the realizer hypotheses of the road contain

`L(ξ) = Nc.ncL S ξ`, `m* = L(0)`, `P' = Nc.ncPp S`, `c_k = ψ_{Ω₂}(Ω_ω + Ω_{k+1})` (cofinal in `P'`,
`Pp.ppPp_cof`), `ρ_λ = υ_λ`, `B₀ = Cd.cdB0`, Range = `CdRange`.

* `rm_next` (the next multiple of `ω²` above `x` is at most `x + ω²`), `rm_ck_lt` (`c_k + ω² < c_{k+1}`);
* `rm_idx_cof` (**restart indices between `L(n)` and `L(n+1)`, cofinal in the index of `L(n+1)`**): every
  `ζ < λ_{n+1} = ι(Ω_ω + P'·(n+1))` lies below a restart index `μ < λ_{n+1}` with `L(n) < ρ_μ < L(n+1)`
  (`μ` is the next multiple of `ω²` above `ι(Ω_ω + P'·n + c_k)`, and `ι` is `+ ω²` on the good block
  above it, `Pp.ppIota_add`, `Pp.ppGood_ck`);
* `rmL_cof_iff` (**`RmCof S L(n+1) ↔ ρ_{B₀} < L(n+1)`**), `rmW_cof_iff` (**`RmCof S L(ω) ↔ ρ_{B₀} < L(ω)`**);
* `rmNamed_real` (**`ρ_{B₀} < m*` gives `RlReal` at `m*`, at every `L(n+1)` and at `L(ω)` for every target
  `t ≤ a·ω^ω`**), `rmNamed_iff` (**the realizer hypotheses of `Rl.rlNamed_of_real` imply `ρ_{B₀} < m*`, and
  `ρ_{B₀} < m*` is equivalent to `RmCof` at all three points**).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rm

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rl
  Googology.Trans.PoR.InaccPsi.R2.Nc Googology.Trans.PoR.InaccPsi.R2.Pp Googology.Trans.PoR.InaccPsi.R2.Bt

variable {S : InaccSeq.{0}}

/-- **The next multiple of `ω²`**: `x < ω²·(x / ω² + 1) ≤ x + ω²`, a restart index. -/
theorem rm_next (x : Ordinal.{0}) :
    x < ω * ω * (x / (ω * ω) + 1) ∧ ω * ω * (x / (ω * ω) + 1) ≤ x + ω * ω ∧
      IsRestartIdx (ω * ω * (x / (ω * ω) + 1)) := by
  have hw : (ω : Ordinal.{0}) * ω ≠ 0 := (mul_pos omega0_pos omega0_pos).ne'
  have e := div_add_mod x (ω * ω)
  refine ⟨?_, ?_, ?_⟩
  · rw [mul_add_one]
    conv_lhs => rw [← e]
    exact (add_lt_add_iff_left _).2 (mod_lt x hw)
  · rw [mul_add_one]
    conv_rhs => rw [← e]
    exact add_le_add le_self_add le_rfl
  · refine ri_iff.2 ⟨mul_ne_zero hw (ne_of_gt (lt_of_le_of_lt zero_le (lt_add_one _))),
      dvd_mul_right _ _⟩

/-- `c_k` as a function of `k`. -/
noncomputable abbrev rmC (S : InaccSeq.{0}) (k : ℕ) : Ordinal.{0} :=
  S.psi (Om ω + Om ((k + 1 : ℕ) : Ordinal.{0})) (Om (1 + 1))

theorem rm_ck_lt (k : ℕ) : rmC S k + ω * ω < rmC S (k + 1) := by
  have hSC : SC (rmC S (k + 1)) := SC_psi (InR_Om_succ 1) _
  have hlt : rmC S k < rmC S (k + 1) := by
    refine psi_lt_psi (InR_Om_succ 1) ?_ (ppOmk_mem (ppOmega_lt_SC (SC_psi (InR_Om_succ 1) _)) k)
    gcongr
    exact Om_lt_Om.2 (Nat.cast_lt.2 (Nat.lt_succ_self _))
  exact hSC.isPrincipal hlt (ppSC_ww hSC)

theorem rm_eta_succ (n : ℕ) :
    Om ω + ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) = Om ω + ncPp S * (n : Ordinal.{0}) + ncPp S := by
  rw [Nat.cast_succ, mul_add_one, add_assoc]

/-- **Restart indices between `L(n)` and `L(n+1)`, cofinal in the index of `L(n+1)`.** -/
theorem rm_idx_cof (n : ℕ) {ζ : Ordinal.{0}}
    (hζ : ζ < iota S (Om ω + ncPp S * ((n + 1 : ℕ) : Ordinal.{0}))) :
    ∃ μ, IsRestartIdx μ ∧ ζ < μ ∧ μ < iota S (Om ω + ncPp S * ((n + 1 : ℕ) : Ordinal.{0})) ∧
      ncL S (n : Ordinal.{0}) < upsilon μ ∧ upsilon μ < ncL S ((n + 1 : ℕ) : Ordinal.{0}) := by
  set base := Om ω + ncPp S * (n : Ordinal.{0}) with hbase
  have e1 := rm_eta_succ (S := S) n
  rw [e1] at hζ ⊢
  have hlim : IsSuccLimit (base + ncPp S) := isSuccLimit_add _ (ncPp_SC S).isSuccLimit
  have hζ' := hζ
  rw [Bt.iota_limit hlim] at hζ'
  haveI : Nonempty (Iio (base + ncPp S)) := ⟨⟨0, hlim.bot_lt⟩⟩
  obtain ⟨e', he'⟩ := (lt_ciSup_iff (Bt.iota_bdd _)).1 hζ'
  have hk : ∃ k : ℕ, e'.1 ≤ base + rmC S k := by
    rcases lt_or_ge e'.1 base with h | h
    · exact ⟨0, h.le.trans le_self_add⟩
    · obtain ⟨d, hd⟩ := exists_add_of_le h
      have hdP : d < ncPp S := by
        have := e'.2; rw [hd] at this; exact (add_lt_add_iff_left _).1 this
      obtain ⟨k, hk⟩ := ppPp_cof d hdP
      exact ⟨k, by rw [hd]; exact add_le_add le_rfl hk.le⟩
  obtain ⟨k, hk⟩ := hk
  set x := iota S (base + rmC S k)
  have hζx : ζ < x := he'.trans_le (Bt.iota_mono _ _ hk)
  obtain ⟨h1, h2, hri⟩ := rm_next x
  set μ := ω * ω * (x / (ω * ω) + 1)
  have hstep : iota S (base + rmC S k + ω * ω) = x + ω * ω :=
    ppIota_add _ _ (fun y hy => ppGood_ck n k hy)
  have hg : Bt.Good S (base + rmC S (k + 1)) := by
    have := ppGood_ck (S := S) n (k + 1) (y := 0) (mul_pos omega0_pos omega0_pos)
    rwa [add_zero] at this
  have hμ1 : μ ≤ iota S (base + rmC S (k + 1)) := by
    refine h2.trans ?_
    rw [← hstep]
    refine Bt.iota_mono _ _ ?_
    rw [add_assoc]
    exact add_le_add le_rfl (rm_ck_lt k).le
  have hμlt : μ < iota S (base + ncPp S) := by
    refine hμ1.trans_lt ?_
    calc iota S (base + rmC S (k + 1)) < iota S (base + rmC S (k + 1)) + 1 := lt_add_one _
      _ = iota S (base + rmC S (k + 1) + 1) := (Bt.iota_good hg).symm
      _ ≤ iota S (base + ncPp S) := by
          refine Bt.iota_mono _ _ ?_
          rw [add_assoc]
          exact add_le_add le_rfl (Order.add_one_le_of_lt (ppC_lt (k + 1)))
  refine ⟨μ, hri, hζx.trans h1, hμlt, ?_, ?_⟩
  · rw [ppL_eq_ups (n : Ordinal.{0})]
    exact upsilon_normal.strictMono ((Bt.iota_mono _ _ le_self_add).trans_lt h1)
  · rw [ppL_eq_ups, e1]
    exact upsilon_normal.strictMono hμlt

/-- **`RmCof S L(n+1) ↔ ρ_{B₀} < L(n+1)`.** -/
theorem rmL_cof_iff (n : ℕ) :
    RmCof S (ncL S ((n + 1 : ℕ) : Ordinal.{0})) ↔ upsilon cdB0 < ncL S ((n + 1 : ℕ) : Ordinal.{0}) := by
  refine ⟨fun h => rm_B0_lt_of_cof h (Lw.lw_L_SC S _).1, fun hB γ hγ => ?_⟩
  set lam := iota S (Om ω + ncPp S * ((n + 1 : ℕ) : Ordinal.{0})) with hlam
  have eL : ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon lam := ppL_eq_ups _
  have hlim : IsSuccLimit lam := by
    refine Ordinal.isSuccLimit_iff.2 ⟨(ppIota_succ_restart n).1, isSuccPrelimit_iff_succ_lt.2 ?_⟩
    intro b hb
    obtain ⟨μ, -, hbμ, hμ, -⟩ := rm_idx_cof (S := S) n hb
    exact (Order.succ_le_of_lt hbμ).trans_lt hμ
  have hγ' : γ < upsilon lam := eL ▸ hγ
  have hB' : cdB0 < lam := upsilon_normal.strictMono.lt_iff_lt.1 (eL ▸ hB)
  obtain ⟨ζ, hζ, hγζ⟩ := (upsilon_normal.lt_iff_exists_lt hlim).1 hγ'
  obtain ⟨μ, hri, hζμ, -, h1, h2⟩ := rm_idx_cof (S := S) n (max_lt hζ hB')
  have hBμ : cdB0 ≤ μ := (le_max_right _ _).trans hζμ.le
  have hlev : cdMstar S ≤ upsilon μ := (cdMstar_le_L S _).trans h1.le
  have hω : upsilon μ < ncL S ω := h2.trans (ppL_lt_omega n)
  have hr : CdRange S μ := by
    refine (cdRange_iff_level2 hri hBμ hlev hω).2 fun j hj => ?_
    rcases le_or_gt j n with hjn | hjn
    · have h' : ncL S (n : Ordinal.{0}) < ncL S (j : Ordinal.{0}) := by rw [← hj]; exact h1
      exact absurd h' (not_lt.2 (Qq.qqL_mono S hjn))
    · have h' : ncL S (j : Ordinal.{0}) < ncL S ((n + 1 : ℕ) : Ordinal.{0}) := by rw [← hj]; exact h2
      exact absurd h' (not_lt.2 (Qq.qqL_mono S (show n + 1 ≤ j from hjn)))
  exact ⟨μ, hr, hγζ.trans_le (upsilon_normal.strictMono.monotone ((le_max_left _ _).trans hζμ.le)), h2⟩

/-- **`RmCof S L(ω) ↔ ρ_{B₀} < L(ω)`.** -/
theorem rmW_cof_iff : RmCof S (ncL S ω) ↔ upsilon cdB0 < ncL S ω := by
  refine ⟨fun h => rm_B0_lt_of_cof h (Lw.lw_L_SC S _).1, fun hB γ hγ => ?_⟩
  obtain ⟨m, hm⟩ := Qq.qqL_cof S γ hγ
  obtain ⟨m', hm'⟩ := Qq.qqL_cof S _ hB
  set N := max m m'
  have hmono : ∀ j : ℕ, j ≤ N → ncL S (j : Ordinal.{0}) ≤ ncL S ((N + 1 : ℕ) : Ordinal.{0}) :=
    fun j hj => Qq.qqL_mono S (hj.trans (Nat.le_succ N))
  obtain ⟨μ, hr, h1, h2⟩ := (rmL_cof_iff (S := S) N).2
    (hm'.trans_le (hmono m' (le_max_right _ _))) γ (hm.trans_le (hmono m (le_max_left _ _)))
  exact ⟨μ, hr, h1, h2.trans (ppL_lt_omega N)⟩

/-- **`ρ_{B₀} < m*` is equivalent to `RmCof` at `m*`, at every `L(n+1)` and at `L(ω)`.** -/
theorem rmNamed_cof_iff :
    upsilon cdB0 < ncL S 0 ↔ (RmCof S (ncL S 0) ∧ (∀ n : ℕ, RmCof S (ncL S ((n + 1 : ℕ) : Ordinal.{0}))) ∧
      RmCof S (ncL S ω)) := by
  constructor
  · intro hB
    have hle : ∀ ξ, ncL S 0 ≤ ncL S ξ := fun ξ => ppL_mono zero_le
    refine ⟨rmM_cof_iff.2 hB, fun n => (rmL_cof_iff n).2 ?_, rmW_cof_iff.2 ?_⟩
    · exact hB.trans_le (hle _)
    · exact hB.trans_le (hle _)
  · rintro ⟨h0, -, -⟩
    exact rmM_cof_iff.1 h0

/-- **`ρ_{B₀} < m*` gives the realizer maps at the three named points for every target `t ≤ a·ω^ω`.** -/
theorem rmNamed_real (hB : upsilon cdB0 < ncL S 0) :
    (∀ t, t ≤ ncL S 0 * ω ^ ω → RlReal S (ncL S 0) t) ∧
    (∀ n : ℕ, ∀ t, t ≤ ncL S ((n + 1 : ℕ) : Ordinal.{0}) * ω ^ ω →
      RlReal S (ncL S ((n + 1 : ℕ) : Ordinal.{0})) t) ∧
    (∀ t, t ≤ ncL S ω * ω ^ ω → RlReal S (ncL S ω) t) := by
  obtain ⟨h0, hn, hw⟩ := rmNamed_cof_iff.1 hB
  exact ⟨fun t ht => rmReal_lin (rm_L_inE 0) h0 ht, fun n t ht => rmReal_lin (rm_L_inE _) (hn n) ht,
    fun t ht => rmReal_lin (rm_L_inE ω) hw ht⟩

/-- **The realizer hypotheses of `Rl.rlNamed_of_real` (and of `Rl.rlRoad_front`, `Rl.rlRoad_rz`) contain
`ρ_{B₀} < m*`, which is all that the targets `t ≤ a·ω^ω` need.** -/
theorem rmNamed_iff (h0 : RlRealCof S (ncL S 0) (ncL S 1))
    (hn : ∀ n : ℕ, RlRealCof S (ncL S ((n + 1 : ℕ) : Ordinal.{0})) (ncL S ((n + 2 : ℕ) : Ordinal.{0})))
    (hw : RlRealCof S (ncL S ω) (ncL S (ω + 1))) :
    upsilon cdB0 < ncL S 0 ∧ RlReal S (ncL S 0) (ncL S 0 * ω ^ ω) ∧
      (∀ n : ℕ, RlReal S (ncL S ((n + 1 : ℕ) : Ordinal.{0})) (ncL S ((n + 1 : ℕ) : Ordinal.{0}) * ω ^ ω)) ∧
      RlReal S (ncL S ω) (ncL S ω * ω ^ ω) := by
  have hB := (rmNamed_need h0 hn hw).2.2.2
  obtain ⟨r0, rn, rw⟩ := rmNamed_real hB
  exact ⟨hB, r0 _ le_rfl, fun n => rn n _ le_rfl, rw _ le_rfl⟩

end Googology.Trans.PoR.InaccPsi.R2.Rm
