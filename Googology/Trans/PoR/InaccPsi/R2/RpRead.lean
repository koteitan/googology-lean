import Googology.Trans.PoR.InaccPsi.R2.RpPair

/-!
# The covering at `m*` and every `L(n+1)` from the readings of the codes `G(x+1) = ψ_{Ω₂}(Ω_ω + θ₂·(x+1))`

`θ = ψ_{Ω₂}(Ω_ω)`, `θ₂ = ψ_{Ω₃}(Ω_ω)`, `G(ζ) = ψ_{Ω₂}(Ω_ω + θ₂·ζ)` (`Lc.lcG`; `G(0) = θ`), `G' = G_{k+1} =
G(θ_{k+1}·ω²)` (`Ls.lsG S (k+1)`), `A = A_{η_μ}`, `ρ_μ = ψ_{Ω₁}(A)`, `Θ_μ(m) = otp(Cl(A, ρ_μ) ∩ m)`,
`υ_{μ+γ} = ψ_{Ω₁}(A + θ·γ)` (`Rg.rgUps_eq`), the atoms `Ls.lsAt S A ρ_μ`.

* `RpRead S μ` (**the reading of the codes `G(x+1)` from below**): `υ_{μ+x+1} ≤ Θ_μ(G(x+1))` for every `x < ρ_μ`;
  `RpReadAll S k`: `RpRead` at every Range restart `μ` below `L(ω)` with code `G' + 1`;
* `rpG_le` (`G(x) ≤ G'` for `x < Ω₁`), `rpSup_of_read` (**`RpRead` gives `υ_{μ+γ} ≤ Θ_μ(G')` for every
  `γ < ρ_μ`**), `rpCover_of_read` (**`RpReadAll S k` gives `Rg.RgCoverAt` at `m*` and at every `L(n+1)`**, with
  the names of `Ls.lsNames_M`, `Ls.lsNames_L`), `rpSupAt_of_read` (hence `Ra.RaSupAt` there);
* `RpStep S μ` (**one block**: `υ_{μ+x} ≤ Θ_μ(G(x))` gives `υ_{μ+x+1} ≤ Θ_μ(G(x+1))`), `rpRead_of_step`
  (**`RpStep` gives `RpRead`**: the base `υ_μ = ρ_μ = Θ_μ(Ω₁) ≤ Θ_μ(θ)` and the limit steps (`υ` is normal,
  `G` and `Θ_μ` are monotone) are proved);
* `RpBlk S μ` (**the block covering**: for `x < ρ_μ` and `ζ < θ` an atom `t < G(x+1)` with
  `ψ_{Ω₁}(A + θ·x + ζ) ≤ Θ_μ(t)`), `rpRead_of_blk` (**`RpBlk` gives `RpRead`**: `Rg.rgPsi_le_cover` with the
  division `ζ = θ·(ζ/θ) + ζ mod θ`);
* `rpRoad_read` (**the road `Rg.rgRoad_cov` with `RpLnOut` and the supply from `RpReadAll`**),
  `rpReadAll_of_blk`, `rpReadAll_of_step`.

No new axiom.  New definitions (hypothesis names only): `RpRead`, `RpReadAll`, `RpStep`, `RpBlk`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **The reading of the codes `G(x+1)` from below** at `μ`. -/
def RpRead (S : InaccSeq.{0}) (μ : Ordinal.{0}) : Prop :=
  ∀ x < upsilon μ, upsilon (μ + (x + 1)) ≤ cdTheta S μ (Lc.lcG S (x + 1))

/-- `RpRead` at every Range restart below `L(ω)` with code `G' + 1`. -/
def RpReadAll (S : InaccSeq.{0}) (k : ℕ) : Prop :=
  ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → cdCode S μ = Ls.lsG S (k + 1) + 1 → RpRead S μ

/-- **One block**: `υ_{μ+x} ≤ Θ_μ(G(x))` gives `υ_{μ+x+1} ≤ Θ_μ(G(x+1))`. -/
def RpStep (S : InaccSeq.{0}) (μ : Ordinal.{0}) : Prop :=
  ∀ x, x + 1 < upsilon μ → upsilon (μ + x) ≤ cdTheta S μ (Lc.lcG S x) →
    upsilon (μ + (x + 1)) ≤ cdTheta S μ (Lc.lcG S (x + 1))

/-- **The block covering** at `μ`: for `x < ρ_μ`, `ζ < θ` an atom `t < G(x+1)` with
`ψ_{Ω₁}(A + θ·x + ζ) ≤ Θ_μ(t)`. -/
def RpBlk (S : InaccSeq.{0}) (μ : Ordinal.{0}) : Prop :=
  ∀ x < upsilon μ, ∀ ζ < ConjT.th S, ∃ t ∈ Ls.lsAt S (ConjT.Aη S (cdEta S μ)) (upsilon μ),
    t < Lc.lcG S (x + 1) ∧
      S.psi (ConjT.Aη S (cdEta S μ) + (ConjT.th S * x + ζ)) (Om 1) ≤ cdTheta S μ t

theorem rpG_mono {x y : Ordinal.{0}} (h : x ≤ y) : Lc.lcG S x ≤ Lc.lcG S y :=
  (psi_mono (S := S) (InR_Om_succ 1) (add_le_add le_rfl (mul_le_mul_of_nonneg_left h zero_le))).1

theorem rpOm1_lt_th (k : ℕ) : Om (1 : Ordinal.{0}) < Lc.lcTh S (k + 1) := by
  have h := (psiS_bounds (S := S) (Om ω) ((k + 1 : ℕ) : Ordinal.{0})).1
  exact (Om_le_Om.2 (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))).trans_lt h

/-- `G(x) ≤ G'` for `x < Ω₁`. -/
theorem rpG_le {x : Ordinal.{0}} (k : ℕ) (hx : x < Om 1) : Lc.lcG S x ≤ Ls.lsG S (k + 1) := by
  refine rpG_mono ((hx.trans (rpOm1_lt_th (S := S) k)).le.trans ?_)
  exact Ordinal.le_mul_left _ (pow_pos omega0_pos 2)

theorem rpLt_Om1 {μ x : Ordinal.{0}} (hR : CdRange S μ) (hx : x < upsilon μ) : x + 1 < Om 1 := by
  have hSC : SC (upsilon μ) := by rw [← Ls.lsPv_range hR]; exact Nm.Pv_SC S _
  exact Rg.rgGam_lt hR (hSC.add_one_lt hx)

/-- **`RpRead` gives `υ_{μ+γ} ≤ Θ_μ(G')` for every `γ < ρ_μ`.** -/
theorem rpSup_of_read {μ : Ordinal.{0}} (k : ℕ) (hR : CdRange S μ) (h : RpRead S μ) :
    ∀ γ < upsilon μ, upsilon (μ + γ) ≤ cdTheta S μ (Ls.lsG S (k + 1)) := by
  intro γ hγ
  calc upsilon (μ + γ) ≤ upsilon (μ + (γ + 1)) :=
        upsilon_normal.strictMono.monotone (add_le_add le_rfl le_self_add)
    _ ≤ cdTheta S μ (Lc.lcG S (γ + 1)) := h γ hγ
    _ ≤ cdTheta S μ (Ls.lsG S (k + 1)) := cdTheta_mono S μ (rpG_le k (rpLt_Om1 hR hγ))

/-- **`RpReadAll S k` gives `Rg.RgCoverAt` at `m*` and at every `L(n+1)`.** -/
theorem rpCover_of_read {k : ℕ} (h : RpReadAll S k) :
    Rg.RgCoverAt S (Nc.ncL S 0) ∧ ∀ n : ℕ, Rg.RgCoverAt S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) := by
  have key : ∀ μ γ, CdRange S μ → upsilon μ < Nc.ncL S ω → γ < upsilon μ →
      cdCode S μ = Ls.lsG S (k + 1) + 1 →
      ω ^ Om 1 ∣ cdEta S μ ∧ ∃ s, SC s ∧ Om 1 < s ∧ s ≤ cdCode S μ ∧
        Rg.RgCov S (ConjT.Aη S (cdEta S μ)) (upsilon μ) s (ConjT.th S * γ) := by
    intro μ γ hR hω hγ hc
    have hd := Ls.lsDiv_of_code hc
    refine ⟨hd, Ls.lsG S (k + 1), Ls.lsG_SC _, Ls.lsG_Om1 _, by rw [hc]; exact le_self_add, ?_⟩
    refine (Rg.rgUps_le_iff_cover hR hω hd hγ (Ls.lsG_SC _) (Ls.lsG_Om1 _) (Ls.lsG_Om2 _)).1 ?_
    exact rpSup_of_read k hR (h μ hR hω hc) γ hγ
  refine ⟨fun γ hγ => ?_, fun n γ hγ => ?_⟩
  · obtain ⟨μ, hR, h1, h2, hc⟩ := Ls.lsNames_M (S := S) k γ hγ
    exact ⟨μ, hR, h1, h2, key μ γ hR (h2.trans_le (Pp.ppL_mono zero_le)) h1 hc⟩
  · obtain ⟨μ, hR, h1, h2, hc⟩ := Ls.lsNames_L (S := S) n k γ hγ
    exact ⟨μ, hR, h1, h2, key μ γ hR (h2.trans (Pp.ppL_lt_omega n)) h1 hc⟩

/-- **`RpReadAll S k` gives `Ra.RaSupAt` at `m*` and at every `L(n+1)`.** -/
theorem rpSupAt_of_read {k : ℕ} (h : RpReadAll S k) :
    Ra.RaSupAt S (Nc.ncL S 0) ∧ ∀ n : ℕ, Ra.RaSupAt S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) :=
  ⟨Rg.rgSupAt_of_cover (rpCover_of_read h).1, fun n => Rg.rgSupAt_of_cover ((rpCover_of_read h).2 n)⟩

/-- **`RpStep` gives `RpRead`** (the base and the limit steps are proved). -/
theorem rpRead_of_step {μ : Ordinal.{0}} (hR : CdRange S μ) (h : RpStep S μ) : RpRead S μ := by
  have hpv := Ls.lsPv_range hR
  have hSC : SC (upsilon μ) := by rw [← hpv]; exact Nm.Pv_SC S _
  have hbase : ∀ x, upsilon μ ≤ cdTheta S μ (Lc.lcG S x) := fun x => by
    rw [← cdTheta_Om1 hpv]; exact cdTheta_mono S μ (psiS_bounds (S := S) _ 1).1.le
  have P : ∀ x < upsilon μ, upsilon (μ + x) ≤ cdTheta S μ (Lc.lcG S x) := by
    intro x
    induction x using WellFoundedLT.induction with
    | ind x IH =>
    intro hx
    rcases zero_or_succ_or_isSuccLimit x with rfl | ⟨y, rfl⟩ | hlim
    · rw [add_zero]; exact hbase 0
    · have hy : y < upsilon μ := (Order.lt_succ y).trans hx
      rw [Order.succ_eq_add_one] at hx ⊢
      exact h y hx (IH y (Order.lt_succ y) hy)
    · refine (upsilon_normal.le_iff_forall_le (isSuccLimit_add μ hlim)).2 fun a ha => ?_
      rcases lt_or_ge a μ with haμ | haμ
      · exact (upsilon_normal.strictMono haμ).le.trans (hbase x)
      · obtain ⟨z, rfl⟩ := exists_add_of_le haμ
        have hz : z < x := (add_lt_add_iff_left μ).1 ha
        exact (IH z hz (hz.trans hx)).trans (cdTheta_mono S μ (rpG_mono hz.le))
  intro x hx
  exact P (x + 1) (hSC.add_one_lt hx)

/-- **`RpBlk` gives `RpRead`.** -/
theorem rpRead_of_blk {μ : Ordinal.{0}} (hR : CdRange S μ) (hd : ω ^ Om 1 ∣ cdEta S μ) (h : RpBlk S μ) :
    RpRead S μ := by
  intro x hx
  have hx1 : x + 1 ≤ upsilon μ := Order.add_one_le_of_lt hx
  rw [Rg.rgUps_eq hR hx1]
  refine Rg.rgPsi_le_cover (Ls.lsPv_range hR) (SC_psi (InR_Om_succ 1) _) (psiS_bounds (S := S) _ 1).1
    (psi_lt (InR_Om_succ 1) _).le (Rg.rgDvd_A hd) (Rg.rgD_le (rpLt_Om1 hR hx)) ?_
  intro ζ _ hζ
  right
  have hθ0 : ConjT.th S ≠ 0 := (Rg.rgTh_SC S).1.ne'
  have hq : ζ / ConjT.th S ≤ x := Order.lt_add_one_iff.1 ((Ordinal.lt_mul_iff_div_lt hθ0).1 hζ)
  obtain ⟨t, ht, htlt, hle⟩ := h (ζ / ConjT.th S) (hq.trans_lt hx) (ζ % ConjT.th S)
    (Ordinal.mod_lt ζ hθ0)
  rw [Ordinal.div_add_mod] at hle
  exact ⟨t, ht, htlt.trans_le (rpG_mono (add_le_add hq le_rfl)), hle⟩

/-- **The road `Rg.rgRoad_cov` with `RpLnOut` and the supply from `RpReadAll S k`.** -/
theorem rpRoad_read {k : ℕ} (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S) (hread : RpReadAll S k)
    (h0 : Lr.LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Nc.ncL S 0)))
    (hn : ∀ n : ℕ, Lr.LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
    (hout : RpLnOut S)
    (hgap : Lr.LrGap S (Nc.ncL S ω) (Nc.ncL S (ω + 1)) (upsilon (Nc.ncL S ω + Nc.ncL S ω)))
    (hmove : Cx.CxStdMoveTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Rg.rgRoad_cov hU hO hL hV hVt hEQ htop (rpCover_of_read hread).1 (rpCover_of_read hread).2 h0 hn
    (rpPair_of_out (Rg.rgCAP_of_enum hU hV hVt).1 (Rg.rgCAP_of_enum hU hV hVt).2 hout) hgap hmove

/-- `RpBlk` at every Range restart below `L(ω)` with code `G' + 1` gives `RpReadAll S k`. -/
theorem rpReadAll_of_blk {k : ℕ}
    (h : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → cdCode S μ = Ls.lsG S (k + 1) + 1 → RpBlk S μ) :
    RpReadAll S k :=
  fun μ hR hω hc => rpRead_of_blk hR (Ls.lsDiv_of_code hc) (h μ hR hω hc)

/-- `RpStep` at every Range restart below `L(ω)` with code `G' + 1` gives `RpReadAll S k`. -/
theorem rpReadAll_of_step {k : ℕ}
    (h : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → cdCode S μ = Ls.lsG S (k + 1) + 1 → RpStep S μ) :
    RpReadAll S k :=
  fun μ hR hω hc => rpRead_of_step hR (h μ hR hω hc)

end Googology.Trans.PoR.InaccPsi.R2.Rp
