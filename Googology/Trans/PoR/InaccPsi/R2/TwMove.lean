import Googology.Trans.PoR.InaccPsi.R2.TwBase
import Googology.Trans.PoR.InaccPsi.R2.TiCode

/-!
# `B_n` on the codes below `X`: `B_n(F_β(y)) = F_{B_n β}(B_n y)`

`B_n = Bc.bcB S n`, `c_{n+1} = L(n+2) = Bc.bcC S (n + 1)`, `ψ = ψ_{Ω₂}`, `F_β = Rh.rhF β`, `w_β = Ω₂^β = Le.leWe β`,
`X = Tl.tlX`, `TlCl Z` the codes over `Z` with the atoms `F_β(y)` (`R2.TlCl`), `tlDat` their data (`R2.TlDat`),
`MvD` the domain of `B_n`.  The atom case moves the run of the atom (`Tw.twRun`): its own argument `B + w_β·D` goes to
`B_n B + w_{B_n β}·B_n D`, whose collapse is computed again by the `ψ_{Ω₂} ↔ F_β` lemma (`Ts.ts_eq_all`, validity from
`Ts.ts_valid`).

* `twB_S` (`B_n(twS β) = twS(B_n β)`), `tw_X_opow_nat`;
* `twMove_base` (**the move of a run**: for a base `B` (own, `w_β ∣ B`, `F_β(c) = ψ(B)`) whose image is a base for
  `B_n β` at `B_n c`, and a valid `D`: `B_n(F_β(c + D)) = ψ(B_n(B + w_β·D)) = F_{B_n β}(B_n(c + D))`, the image of
  the own argument is own);
* `twB_code` (**for a code `μ` over a strongly critical `x < L(ω)` with `B_n x ≤ Ω₁`: `μ` is in the domain of
  `B_n`, `B_n μ` is a code over `B_n x`, `B_n μ < X`, `tlDat (B_n μ) = B_n (tlDat μ)`, and for an atom `μ = F_β(y)`
  (`β = tlLev μ`, `y` its index): `B_n μ = F_{B_n β}(B_n y) = ψ(B_n e)` for its own argument `e`, `B_n e` own**);
* `twB_cl`, `twB_lt_X`, `twB_dat` (the case `x = c_{n+1}`), `twB_atom` (**`B_n(F_β(y)) = F_{B_n β}(B_n y)` for codes
  `β`, `y` over `c_{n+1}` with `y < F_β(y)`, `Ω₁ < F_β(y)`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Ts Googology.Trans.PoR.InaccPsi.R2.Mv

variable {S : InaccSeq.{0}}

/-- `ω^g·k < X` for `g < X`. -/
theorem tw_X_opow_nat {g : Ordinal.{0}} (hg : g < tlX) (k : ℕ) : ω ^ g * k < tlX := by
  calc ω ^ g * k < ω ^ g * ω := (mul_lt_mul_iff_right₀ (opow_pos g omega0_pos)).2 (natCast_lt_omega0 k)
    _ = ω ^ (g + 1) := by rw [opow_add, opow_one]
    _ < ω ^ tlX := (opow_lt_opow_iff_right one_lt_omega0).2 (tlX_SC.add_one_lt hg)
    _ = tlX := Gg.gg_SC_eps tlX_SC

/-- **`B_n(twS β) = twS(B_n β)`.** -/
theorem twB_S {n : ℕ} {β : Ordinal.{0}} (hD : MvD S β) :
    MvD S (twS β) ∧ Bc.bcB S n (twS β) = twS (Bc.bcB S n β) := by
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  have hlt : Bc.bcB S n β < Om 1 ↔ β < Om 1 := by
    have := mvB_lt_iff (k := n) hD hDO; rwa [hBO] at this
  have hgt : Om 1 < Bc.bcB S n β ↔ Om 1 < β := by
    have := mvB_lt_iff (k := n) hDO hD; rwa [hBO] at this
  have heq : Bc.bcB S n β = Om 1 ↔ β = Om 1 := by
    constructor
    · intro h
      rcases lt_trichotomy β (Om 1) with h' | h' | h'
      · exact absurd (hlt.2 h') (by rw [h]; exact lt_irrefl _)
      · exact h'
      · exact absurd (hgt.2 h') (by rw [h]; exact lt_irrefl _)
    · intro h; rw [h, hBO]
  have hO1 : MvD S (Om 1 + 1) ∧ Bc.bcB S n (Om 1 + 1) = Om 1 + 1 := by
    obtain ⟨h1, h2⟩ := mvB_add (k := n) hDO (Rk.rk_one_D (S := S))
    rw [hBO, Mw.mwB_one] at h2
    exact ⟨h1, h2⟩
  unfold twS
  by_cases h1 : β < Om 1
  · rw [if_pos h1, if_pos (hlt.2 h1)]; exact hO1
  by_cases h2 : β = Om 1
  · rw [if_neg h1, if_pos h2, if_neg (fun h => h1 (hlt.1 h)), if_pos (heq.2 h2)]
    exact ⟨Rk.rk_one_D, Mw.mwB_one n⟩
  · rw [if_neg h1, if_neg h2, if_neg (fun h => h1 (hlt.1 h)), if_neg (fun h => h2 (heq.1 h))]
    exact ⟨mvD_of_lt (Lw.lw_L_SC S ω).1, Bc.bcB_zero n⟩

/-- **The move of a run**: for a base `B` of `F_β` at `c` (own, `w_β ∣ B`, `F_β(c) = ψ_{Ω₂}(B)`) whose image `B_n B` is
a base of `F_{B_n β}` at `B_n c`, and a valid `D < Ω₂` with `β < F_β(c + D)`: the own argument `e = B + w_β·D` of
`F_β(c + D)` is in the domain of `B_n`, `B_n e` is own, and
`B_n(F_β(c + D)) = ψ_{Ω₂}(B_n e) = F_{B_n β}(B_n(c + D))`. -/
theorem twMove_base {n : ℕ} {β B c D : Ordinal.{0}} (hβD : MvD S β)
    (hown : B ∈ S.CSet B (S.psi B (Om (1 + 1)))) (hBD : MvD S B)
    (hown' : Bc.bcB S n B ∈ S.CSet (Bc.bcB S n B) (S.psi (Bc.bcB S n B) (Om (1 + 1))))
    (hdvd : leWe β ∣ B) (hdvd' : leWe (Bc.bcB S n β) ∣ Bc.bcB S n B)
    (hc : rhF β c = S.psi B (Om (1 + 1)))
    (hc' : rhF (Bc.bcB S n β) (Bc.bcB S n c) = S.psi (Bc.bcB S n B) (Om (1 + 1)))
    (hcD : MvD S c) (hDD : MvD S D) (hD : D < Om (1 + 1)) (hval : ∀ d, d ≤ D → d < rhF β (c + d))
    (hβz : β < rhF β (c + D))
    (hW : MvD S (leWe β * D) ∧ Bc.bcB S n (leWe β * D) = leWe (Bc.bcB S n β) * Bc.bcB S n D) :
    MvD S (B + leWe β * D) ∧ B + leWe β * D ∈ S.CSet (B + leWe β * D) (S.psi (B + leWe β * D) (Om (1 + 1))) ∧
      S.psi (B + leWe β * D) (Om (1 + 1)) = rhF β (c + D) ∧ MvD S (rhF β (c + D)) ∧
      Bc.bcB S n (B + leWe β * D) ∈
        S.CSet (Bc.bcB S n (B + leWe β * D)) (S.psi (Bc.bcB S n (B + leWe β * D)) (Om (1 + 1))) ∧
      Bc.bcB S n (rhF β (c + D)) = S.psi (Bc.bcB S n (B + leWe β * D)) (Om (1 + 1)) ∧
      Bc.bcB S n (rhF β (c + D)) = rhF (Bc.bcB S n β) (Bc.bcB S n (c + D)) := by
  obtain ⟨hψe, howne⟩ := twRun_eq hown hdvd hc hD hval hβz
  obtain ⟨hDe, hBe⟩ := mvB_add (k := n) hBD hW.1
  rw [hW.2] at hBe
  obtain ⟨hDz, hBz⟩ := Mx.mxB_atom (n := n) hDe howne
  rw [hψe] at hDz hBz
  have hDlt : D < rhF β (c + D) := hval D le_rfl
  have h1 : Bc.bcB S n β < Bc.bcB S n (rhF β (c + D)) := (mvB_lt_iff hβD hDz).2 hβz
  have h2 : Bc.bcB S n D < Bc.bcB S n (rhF β (c + D)) := (mvB_lt_iff hDD hDz).2 hDlt
  rw [hBz, hBe] at h1 h2
  have hown2 : Bc.bcB S n B + leWe (Bc.bcB S n β) * Bc.bcB S n D ∈
      S.CSet (Bc.bcB S n B + leWe (Bc.bcB S n β) * Bc.bcB S n D)
        (S.psi (Bc.bcB S n B + leWe (Bc.bcB S n β) * Bc.bcB S n D) (Om (1 + 1))) :=
    CSet.add_mem ((psi_mono (InR_Om_succ 1) le_self_add).2 hown') (tsU_mul_mem h1 h2)
  have hval' := ts_valid hdvd' hc' h2
  obtain ⟨-, heq'⟩ := ts_eq_all hown' hdvd' hc' (h2.trans (ts_psi_lt _)) hval'
  obtain ⟨-, hBcD⟩ := mvB_add (k := n) hcD hDD
  refine ⟨hDe, howne, hψe, hDz, by rw [hBe]; exact hown2, hBz, ?_⟩
  rw [hBz, hBe, heq', hBcD]

/-- **`B_n` on the codes below `X`**: for a code `μ` over a strongly critical `x < L(ω)` with `B_n x ≤ Ω₁`, `μ` is in
the domain of `B_n`, `B_n μ` is a code over `B_n x`, `B_n μ < X`, `tlDat (B_n μ) = B_n (tlDat μ)`; for an atom `μ`
(strongly critical, `> Ω₁`) with level `β = tlLev μ` and index `y`: its own argument `e` is in the domain of `B_n`,
`B_n e` is own, and `B_n μ = ψ_{Ω₂}(B_n e) = F_{B_n β}(B_n y)`. -/
theorem twB_code {n : ℕ} {x : Ordinal.{0}} (hxS : SC x) (hxL : x < Nc.ncL S ω) (hBx : Bc.bcB S n x ≤ Om 1) :
    ∀ μ, TlCl x μ → MvD S μ ∧ TlCl (Bc.bcB S n x) (Bc.bcB S n μ) ∧ Bc.bcB S n μ < tlX ∧
      tlDat (Bc.bcB S n μ) = Bc.bcB S n (tlDat μ) ∧
      (SC μ → Om1 < μ → ∃ e, e ∈ S.CSet e (S.psi e (Om (1 + 1))) ∧ S.psi e (Om (1 + 1)) = μ ∧ MvD S e ∧
        Bc.bcB S n e ∈ S.CSet (Bc.bcB S n e) (S.psi (Bc.bcB S n e) (Om (1 + 1))) ∧
        Bc.bcB S n μ = S.psi (Bc.bcB S n e) (Om (1 + 1)) ∧
        Bc.bcB S n μ = rhF (Bc.bcB S n (tlLev μ)) (Bc.bcB S n (tlI (tlLev μ) μ))) := by
  have hx1 : x ≤ Om1 := by rw [tw_Om1_eq]; exact (hxL.trans (InaccSeq.psi_lt Low.InR_Om_one _)).le
  have hBx1 : Bc.bcB S n x ≤ Om1 := by rw [tw_Om1_eq]; exact hBx
  have hD0 : MvD S (0 : Ordinal.{0}) := mvD_of_lt (lt_of_le_of_lt zero_le hxL)
  have hBxpos : 0 < Bc.bcB S n x := by
    have := (Bc.bcB_lt_iff (k := n) (lt_of_le_of_lt zero_le hxL) hxL).2 hxS.1
    rwa [Bc.bcB_zero] at this
  have hdL : ∀ w, TlCl x w → tlDat w < Nc.ncL S ω := fun w hw => (tl_cl_dat hxS w hw).trans hxL
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  have hDO1 : MvD S Om1 := by rw [tw_Om1_eq]; exact hDO
  have hBO1 : Bc.bcB S n Om1 = Om1 := by rw [tw_Om1_eq]; exact hBO
  have hDOs : MvD S (Om 1 + 1) ∧ Bc.bcB S n (Om 1 + 1) = Om 1 + 1 := by
    obtain ⟨h1, h2⟩ := mvB_add (k := n) hDO (Rk.rk_one_D (S := S))
    rw [hBO, Mw.mwB_one] at h2
    exact ⟨h1, h2⟩
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hz
  have hzX := tw_cl_lt hx1 hz
  rcases lt_trichotomy z Om1 with h | rfl | h
  · have hzx : z < x := hz.lt_of_lt_Om1 hxS h
    have hBzx := (Bc.bcB_lt_iff (k := n) (hzx.trans hxL) hxL).2 hzx
    have hBz1 : Bc.bcB S n z < Om1 := hBzx.trans_le hBx1
    exact ⟨mvD_of_lt (hzx.trans hxL), TlCl.small hBzx, hBz1.trans tlX_gt,
      by rw [tlDat_small h, tlDat_small hBz1], fun _ h1 => absurd h1 (not_lt.2 h.le)⟩
  · exact ⟨hDO1, by rw [hBO1]; exact TlCl.om, by rw [hBO1]; exact tlX_gt,
      by rw [hBO1, tlDat_Om1, Bc.bcB_zero], fun _ h1 => absurd h1 (lt_irrefl _)⟩
  have hz0 : z ≠ 0 := (Rj.rj_Om1_pos.trans h).ne'
  have hOz : ∀ {w : Ordinal.{0}}, MvD S w → Om1 < w → Om1 < Bc.bcB S n w := fun hDw hw => by
    have := (mvB_lt_iff (k := n) hDO1 hDw).2 hw; rwa [hBO1] at this
  by_cases hE : ω ^ z = z
  · by_cases hI : invVeblen₁ z < z
    · -- a Veblen normal form `φ(o, b)`
      set o := invVeblen₁ z with ho
      set b := invVeblen₂ z with hb
      have hbz : b < z := Tf.tf_inv2_lt hE
      obtain ⟨hco, hcb⟩ := tl_cl_inv hx1 z hz h hE hI
      have hev : veblen o b = z := by rw [ho, hb, veblen_invVeblen₁_invVeblen₂, hE]
      have ho0 : o ≠ 0 := by
        intro e
        rw [e, veblen_zero_apply] at hev
        have : ω ^ b = ω ^ z := by rw [hev, hE]
        exact absurd ((opow_right_inj one_lt_omega0).1 this) hbz.ne
      obtain ⟨hDo, hCo, hBoX, hdo, -⟩ := IH o hI hco
      obtain ⟨hDb, hCb, hBbX, hdb, -⟩ := IH b hbz hcb
      obtain ⟨hDz, hBz⟩ := Mw.mwB_phi (k := n) hDo hDb (by rw [hev]; exact hI) (by rw [hev]; exact hbz)
      rw [hev] at hBz hDz
      have hBo0 : Bc.bcB S n o ≠ 0 := by
        intro e
        have h1 := (mvB_lt_iff (k := n) hD0 hDo).2 (pos_iff_ne_zero.2 ho0)
        rw [Bc.bcB_zero, e] at h1
        exact lt_irrefl _ h1
      have hBb : Bc.bcB S n b < veblen (Bc.bcB S n o) (Bc.bcB S n b) := by
        rw [← hBz]; exact (mvB_lt_iff hDb hDz).2 hbz
      have hBo : Bc.bcB S n o < Bc.bcB S n z := (mvB_lt_iff hDo hDz).2 hI
      have hBzX : Bc.bcB S n z < tlX := by rw [hBz]; exact tlX_SC.2 _ hBoX _ hBbX
      refine ⟨hDz, by rw [hBz]; exact TlCl.phi hCo hCb, hBzX, ?_,
        fun hSC _ => absurd hI (tl_SC_facts hSC).2⟩
      have hOz' : Om1 < Bc.bcB S n z := hOz hDz h
      have hBE : ω ^ Bc.bcB S n z = Bc.bcB S n z := by rw [hBz]; exact Gg.gg_veblen_eps hBo0
      have hBI : invVeblen₁ (Bc.bcB S n z) < Bc.bcB S n z := by
        rw [hBz, invVeblen₁_veblen hBb, ← hBz]; exact hBo
      rw [tlDat_phi hOz' hBzX hBE hBI, tlDat_phi h hzX hE hI, hBz, invVeblen₁_veblen hBb,
        invVeblen₂_veblen hBo0 hBb, hdo, hdb]
      rcases le_total (tlDat o) (tlDat b) with hle | hle
      · rw [max_eq_right hle, max_eq_right (Ri.riB_mono (hdL b hcb) hle)]
      · rw [max_eq_left hle, max_eq_left (Ri.riB_mono (hdL o hco) hle)]
    · -- an atom `F_β(y)`
      have hSC := tl_SC_of h hI
      obtain ⟨hnf, hyz, hlz⟩ := tl_nf hSC h hzX
      obtain ⟨hcβ, hcy⟩ := tl_cl_atom hx1 z hz hSC h
      generalize hβdef : tlLev z = β at hnf hyz hlz hcβ hcy ⊢
      generalize hydef : tlI β z = y at hnf hyz hcy ⊢
      obtain ⟨hDβ, hCβ, hBβX, hdβ, -⟩ := IH β hlz hcβ
      obtain ⟨hDy, hCy, hByX, hdy, -⟩ := IH y hyz hcy
      have hβX : β < tlX := hlz.trans hzX
      have h1' : Om 1 < rhF β y := by rw [hnf, ← tw_Om1_eq]; exact h
      have hyz' : y < rhF β y := by rw [hnf]; exact hyz
      have hzX' : rhF β y < tlX := by rw [hnf]; exact hzX
      obtain ⟨B, c, D, hown, hdvd, hc, hcD, hD2, hval, hcc, hDc, hcase⟩ :=
        twRun (S := S) hxS hx1 hcy hβX hyz' h1' hzX'
      have hcz : c < z := (le_self_add.trans_eq hcD).trans_lt hyz
      have hDz : D < z := (le_add_self.trans_eq hcD).trans_lt hyz
      obtain ⟨hDc', -, -, -, hlastc⟩ := IH c hcz hcc
      obtain ⟨hDD, -, -, -, -⟩ := IH D hDz hDc
      -- the class of the codes below `z`
      have hPdec : ∀ v, (v < z ∧ TlCl x v) → v ≠ 0 →
          (log ω v < z ∧ TlCl x (log ω v)) ∧ (v - ω ^ log ω v < z ∧ TlCl x (v - ω ^ log ω v)) :=
        fun v hv hv0 => ⟨⟨(log_le_self _ _).trans_lt hv.1, (tlDec hxS v hv.2).2⟩,
          ⟨(Ordinal.sub_le_self _ _).trans_lt hv.1,
            (tlDec hxS v hv.2).1 _ (TlCl.opow hxS.1 (tlDec hxS v hv.2).2) (opow_log_le_self ω hv0)⟩⟩
      have hPW : ∀ v, (v < z ∧ TlCl x v) → v < Om (1 + 1) := fun v hv => (hv.1.trans hzX).trans tw_X_lt_Om2
      have hWe : ∀ γ, γ < z → TlCl x γ → 1 ≤ β →
          MvD S (leWe β) ∧ Bc.bcB S n (leWe β) = leWe (Bc.bcB S n β) ∧
            MvD S (leWe β * γ) ∧ Bc.bcB S n (leWe β * γ) = leWe (Bc.bcB S n β) * Bc.bcB S n γ :=
        fun γ hγ hcγ hβ1 => leB_We (S := S) (n := n) (fun v => v < z ∧ TlCl x v)
          (fun v hv => (IH v hv.1 hv.2).1) hPdec hPW ⟨hlz, hcβ⟩ hβ1 ⟨hγ, hcγ⟩
      have hW : MvD S (leWe β * D) ∧ Bc.bcB S n (leWe β * D) = leWe (Bc.bcB S n β) * Bc.bcB S n D := by
        rcases eq_or_ne β 0 with h0 | h0
        · rw [h0, Bc.bcB_zero, leWe_zero, one_mul, one_mul]; exact ⟨hDD, rfl⟩
        · obtain ⟨-, -, h3, h4⟩ := hWe D hDz hDc (Order.one_le_iff_ne_zero.2 h0)
          exact ⟨h3, h4⟩
      have hβ'1 : 1 ≤ β → 1 ≤ Bc.bcB S n β := fun hβ1 => by
        rcases hβ1.lt_or_eq with hlt | heq
        · rw [← Mw.mwB_one (S := S) n]; exact ((mvB_lt_iff Rk.rk_one_D hDβ).2 hlt).le
        · rw [← heq, Mw.mwB_one]
      -- the base and its image
      have hbase : MvD S B ∧
          Bc.bcB S n B ∈ S.CSet (Bc.bcB S n B) (S.psi (Bc.bcB S n B) (Om (1 + 1))) ∧
          leWe (Bc.bcB S n β) ∣ Bc.bcB S n B ∧
          rhF (Bc.bcB S n β) (Bc.bcB S n c) = S.psi (Bc.bcB S n B) (Om (1 + 1)) := by
        rcases hcase with ⟨hβ0, hB0, hc0⟩ | ⟨hβ1, hBw, hcs⟩ | ⟨hc1, hcf, -⟩
        · subst hB0 hc0
          rw [hβ0, Bc.bcB_zero, hDOs.2]
          refine ⟨hD0, CSet.zero_mem _ _, dvd_zero _, ?_⟩
          rw [rhF_zero, Tf.tf_psi S 0 zero_le, add_zero, tw_Om1_eq]
        · subst hBw hcs
          obtain ⟨hDw, hBw, -, -⟩ := hWe D hDz hDc hβ1
          obtain ⟨-, hBs⟩ := twB_S (n := n) hDβ
          rw [hBw, hBs]
          exact ⟨hDw, tw_own_U hBβX, dvd_rfl, (tw_psiU_s (hβ'1 hβ1) hBβX).1.symm⟩
        · have hcSC : SC c := by rw [← hcf]; exact rhF_SC β c
          have hc1' : Om1 < c := by rw [tw_Om1_eq]; exact hc1
          have hcX : c < tlX := hcz.trans hzX
          obtain ⟨ec, hownc, hψc, hDec, hownc', hBc, hBcF⟩ := hlastc hcSC hc1'
          have hψB : S.psi B (Om (1 + 1)) = c := by rw [← hc, hcf]
          have hBe : B = ec := ts_own_unique hown hownc (by rw [hψB, hψc])
          subst hBe
          obtain ⟨hlc, hnfc, -⟩ := tlLev_spec hcSC hc1' hcX
          have hlev : β < tlLev c := not_le.1 fun hle => hnfc (rhF_fix_mono hle hcf)
          obtain ⟨hcl, -⟩ := tl_cl_atom hx1 c hcc hcSC hc1'
          obtain ⟨hDl, -, -, -, -⟩ := IH (tlLev c) (hlc.trans hcz) hcl
          have hlt' : Bc.bcB S n β < Bc.bcB S n (tlLev c) := (mvB_lt_iff hDβ hDl).2 hlev
          have hfix' : rhF (Bc.bcB S n β) (Bc.bcB S n c) = Bc.bcB S n c := by
            rw [hBcF]; exact rhF_fix_lower hlt' _
          have hconv := ts_conv (S := S) (Bc.bcB S n β) _ hownc' (by rw [← hBc]; exact hfix')
          exact ⟨hDec, hownc', (tsU_dvd le_self_add).trans hconv, by rw [hfix', hBc]⟩
      obtain ⟨hDB, hownB', hdvd', hc'⟩ := hbase
      have hβz : β < rhF β (c + D) := by rw [hcD, hnf]; exact hlz
      obtain ⟨hDe, howne, hψe, hDz', hownBe, hBz1, hBz2⟩ :=
        twMove_base (n := n) hDβ hown hDB hownB' hdvd hdvd' hc hc' hDc' hDD hD2 hval hβz hW
      rw [hcD, hnf] at hψe hDz' hBz1 hBz2
      -- the image atom
      have hByz : Bc.bcB S n y < Bc.bcB S n z := (mvB_lt_iff hDy hDz').2 hyz
      have hOBz : Om1 < Bc.bcB S n z := hOz hDz' h
      have hBzX : Bc.bcB S n z < tlX := by
        rw [hBz2]
        have := (rhF_lt (Bc.bcB S n β)).2 hByX; rwa [ts_X_fix hBβX] at this
      refine ⟨hDz', by rw [hBz2]; exact TlCl.atom hCβ hCy (by rw [← hBz2]; exact hOBz), hBzX, ?_,
        fun _ _ => ⟨_, howne, hψe, hDe, hownBe, hBz1, hBz2⟩⟩
      rcases eq_or_ne β 0 with h0 | h0
      · -- level `0`: the data of `Γ_y` is that of `y − (Ω₁ + 1)`
        subst h0
        rw [rhF_zero] at hnf hyz' h1' hzX'
        rw [Bc.bcB_zero, rhF_zero] at hBz2
        have hy1 : Om1 < y := Tf.tf_Om1_lt_gamma.1 (by rw [tw_Om1_eq]; exact h1')
        have hyO : Om1 + 1 ≤ y := Order.add_one_le_of_lt hy1
        have hc0 : TlCl x (y - (Om1 + 1)) :=
          (tlDec hxS y hcy).1 _ (TlCl.add TlCl.om (TlCl.one hxS.1)) hyO
        have hc0z : y - (Om1 + 1) < z := (Ordinal.sub_le_self _ _).trans_lt hyz
        obtain ⟨hDc0, -, -, hdc0, -⟩ := IH _ hc0z hc0
        have hy_eq : Om1 + 1 + (y - (Om1 + 1)) = y := Ordinal.add_sub_cancel_of_le hyO
        have hO1' : MvD S (Om1 + 1) ∧ Bc.bcB S n (Om1 + 1) = Om1 + 1 := by rw [tw_Om1_eq]; exact hDOs
        obtain ⟨-, hBy⟩ := mvB_add (k := n) hO1'.1 hDc0
        rw [hy_eq, hO1'.2] at hBy
        have hBy1 : Om1 < Bc.bcB S n y := by rw [hBy]; exact (lt_add_one _).trans_le le_self_add
        have hByg : Bc.bcB S n y < gamma (Bc.bcB S n y) := by rw [← hBz2]; exact hByz
        have hgX : gamma (Bc.bcB S n y) < tlX := by rw [← hBz2]; exact hBzX
        rw [hBz2, tlDat_gamma hBy1 hByg hgX, ← hnf, tlDat_gamma hy1 (by rw [hnf]; exact hyz)
          (by rw [hnf]; exact hzX), hBy, Ordinal.add_sub_cancel, hdc0]
      · -- level `β ≥ 1`: the larger data of the level and the index
        have hBβ0 : Bc.bcB S n β ≠ 0 := by
          intro e
          have h1 := (mvB_lt_iff (k := n) hD0 hDβ).2 (pos_iff_ne_zero.2 h0)
          rw [Bc.bcB_zero, e] at h1
          exact lt_irrefl _ h1
        have hByF : Bc.bcB S n y < rhF (Bc.bcB S n β) (Bc.bcB S n y) := by rw [← hBz2]; exact hByz
        rw [hBz2, tlDat_F hBβ0 (by rw [← hBz2]; exact hOBz) (by rw [← hBz2]; exact hBzX) hByF,
          ← hnf, tlDat_F h0 (by rw [hnf]; exact h) (by rw [hnf]; exact hzX)
          (by rw [hnf]; exact hyz), hdβ, hdy]
        rcases le_total (tlDat β) (tlDat y) with hle | hle
        · rw [max_eq_right hle, max_eq_right (Ri.riB_mono (hdL y hcy) hle)]
        · rw [max_eq_left hle, max_eq_left (Ri.riB_mono (hdL β hcβ) hle)]
  · -- Cantor normal form
    obtain ⟨hsub, hlog⟩ := tlDec hxS z hz
    set g := log ω z with hgdef
    have hgz : g < z := Tf.tf_log_lt h hE
    obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt z one_lt_omega0)
    have hk0 : k ≠ 0 := by
      intro e
      have h1 := Ordinal.div_opow_log_pos ω hz0
      rw [hk, e, Nat.cast_zero] at h1
      exact lt_irrefl _ h1
    have hdec : ω ^ g * k + z % ω ^ g = z := by
      have := Ordinal.div_add_mod z (ω ^ g); rwa [hk] at this
    have hrg : z % ω ^ g < ω ^ g := Ordinal.mod_lt z (opow_pos _ omega0_pos).ne'
    have hwk : TlCl x (ω ^ g * k) := TlCl.mul_nat hxS.1 (TlCl.opow hxS.1 hlog) k
    have hle : ω ^ g * k ≤ z := by
      conv_rhs => rw [← hdec]
      exact le_self_add
    have hr : TlCl x (z % ω ^ g) := by
      have e : z - ω ^ g * k = z % ω ^ g := by
        nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
      rw [← e]; exact hsub _ hwk hle
    have hrz : z % ω ^ g < z := Rj.rj_mod_lt hz0
    obtain ⟨hDg, hCg, hBgX, hdg, -⟩ := IH g hgz hlog
    obtain ⟨hDr, hCr, hBrX, hdr, -⟩ := IH _ hrz hr
    obtain ⟨hDw, hBw⟩ := Rk.rkB_opow_nat (n := n) hDg k
    obtain ⟨hDz, hBz⟩ := mvB_add (k := n) hDw hDr
    rw [hdec] at hBz hDz
    obtain ⟨hDog, hBog⟩ := Ld.ldB_opow (n := n) hDg
    have hBr : Bc.bcB S n (z % ω ^ g) < ω ^ Bc.bcB S n g := by
      rw [← hBog]; exact (mvB_lt_iff hDr hDog).2 hrg
    have hBzX : Bc.bcB S n z < tlX := by
      rw [hBz, hBw]; exact (Lq.lq_SC_indec tlX_SC).add_lt (tw_X_opow_nat hBgX k) hBrX
    refine ⟨hDz, by rw [hBz, hBw]; exact TlCl.add (TlCl.mul_nat hBxpos (TlCl.opow hBxpos hCg) k) hCr, hBzX,
      ?_, fun hSC _ => absurd (tl_SC_facts hSC).1 hE⟩
    have hOz' : Om1 < Bc.bcB S n z := hOz hDz h
    have hlogB : log ω (Bc.bcB S n z) = Bc.bcB S n g := by
      rw [hBz, hBw, log_opow_mul_add one_lt_omega0 (by exact_mod_cast hk0) hBr,
        Ordinal.log_eq_zero (natCast_lt_omega0 k), add_zero]
    have hmodB : Bc.bcB S n z % ω ^ log ω (Bc.bcB S n z) = Bc.bcB S n (z % ω ^ g) := by
      rw [hlogB, hBz, hBw, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hBr]
    have hBE : ω ^ Bc.bcB S n z ≠ Bc.bcB S n z := by
      intro e
      have h1 : log ω (Bc.bcB S n z) = Bc.bcB S n z := by
        conv_lhs => rw [← e]
        exact log_opow one_lt_omega0 _
      rw [hlogB] at h1
      exact absurd h1 ((mvB_lt_iff hDg hDz).2 hgz).ne
    rw [tlDat_cnf hOz' hBzX hBE, hmodB, hlogB, hdg, hdr, tlDat_cnf h hzX hE]
    rcases le_total (tlDat g) (tlDat (z % ω ^ g)) with hle' | hle'
    · rw [max_eq_right hle', max_eq_right (Ri.riB_mono (hdL _ hr) hle')]
    · rw [max_eq_left hle', max_eq_left (Ri.riB_mono (hdL g hlog) hle')]

/-- **A code over `c_{n+1}` is in the domain of `B_n`; its image is a code over `B_n c_{n+1}` below `X`, with
`tlDat (B_n μ) = B_n (tlDat μ)`.** -/
theorem twB_cl {n : ℕ} {μ : Ordinal.{0}} (hμ : TlCl (Bc.bcC S (n + 1)) μ) :
    MvD S μ ∧ TlCl (Bc.bcB S n (Bc.bcC S (n + 1))) (Bc.bcB S n μ) ∧ Bc.bcB S n μ < tlX ∧
      tlDat (Bc.bcB S n μ) = Bc.bcB S n (tlDat μ) := by
  obtain ⟨a, b, c, d, -⟩ := twB_code (Lw.lw_L_SC S _) (Bc.bcC_lt S (n + 1)) (Tc.tcB_c_le n) μ hμ
  exact ⟨a, b, c, d⟩

/-- **`B_n` keeps the codes below `X`** over `c_{n+1}`. -/
theorem twB_lt_X {n : ℕ} {μ : Ordinal.{0}} (hμ : TlCl (Bc.bcC S (n + 1)) μ) : Bc.bcB S n μ < tlX :=
  (twB_cl hμ).2.2.1

/-- **`tlDat (B_n z) = B_n (tlDat z)`** for every code `z` over `c_{n+1}`. -/
theorem twB_dat {n : ℕ} {z : Ordinal.{0}} (hz : TlCl (Bc.bcC S (n + 1)) z) :
    tlDat (Bc.bcB S n z) = Bc.bcB S n (tlDat z) := (twB_cl hz).2.2.2

/-- **`B_n(F_β(y)) = F_{B_n β}(B_n y)`** for codes `β`, `y` over `c_{n+1}` with `y < F_β(y)` and `Ω₁ < F_β(y)`; the
atom is in the domain of `B_n`, and so is its own argument `e`, with `B_n(F_β(y)) = ψ_{Ω₂}(B_n e)`, `B_n e` own. -/
theorem twB_atom {n : ℕ} {β y : Ordinal.{0}} (hβ : TlCl (Bc.bcC S (n + 1)) β) (hy : TlCl (Bc.bcC S (n + 1)) y)
    (hyz : y < rhF β y) (h1 : Om1 < rhF β y) :
    MvD S (rhF β y) ∧ Bc.bcB S n (rhF β y) = rhF (Bc.bcB S n β) (Bc.bcB S n y) ∧
      ∃ e, e ∈ S.CSet e (S.psi e (Om (1 + 1))) ∧ S.psi e (Om (1 + 1)) = rhF β y ∧ MvD S e ∧
        Bc.bcB S n e ∈ S.CSet (Bc.bcB S n e) (S.psi (Bc.bcB S n e) (Om (1 + 1))) ∧
        Bc.bcB S n (rhF β y) = S.psi (Bc.bcB S n e) (Om (1 + 1)) := by
  obtain ⟨hD, -, -, -, hlast⟩ := twB_code (Lw.lw_L_SC S _) (Bc.bcC_lt S (n + 1)) (Tc.tcB_c_le n) _
    (TlCl.atom hβ hy h1)
  obtain ⟨e, h2, h3, h4, h5, h6, h7⟩ := hlast (rhF_SC β y) h1
  rw [tlLev_F hyz, tlI_rhF] at h7
  exact ⟨hD, h7, e, h2, h3, h4, h5, h6⟩

end Googology.Trans.PoR.InaccPsi.R2.Tw
