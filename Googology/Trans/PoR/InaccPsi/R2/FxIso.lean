import Googology.Trans.PoR.InaccPsi.R2.FxName

/-!
# ENUM-REACH at the isolated fixed points of `υ` below `cpB1`

`F = υ_F` is **isolated** (`Cp.CpIso F`) when the restart indices of some `(ν, F)` are not fixed points of `υ`.

* `fx_ri_of_fix`: a fixed point `G ≠ 0` of `υ` is a restart index;
* `fxIso_eta` (**the name of an isolated fixed point**): `η_F = η₁ + Ω₁` for a good multiple `η₁` of `Ω₁`
  with `P(η₁) < F`.  Let `η*` be the least `η` with `ι(η) ≥ F` (so `P(η*) = F`, `P(η) < F` below `η*`) and
  `η* = Ω₁·q + r`.  For `r ≠ 0` take `η₁ = Ω₁·q`, for `q = q' + 1`, `r = 0` take `η₁ = Ω₁·q'`: `η₁` is good
  (else the plateau `Fx.fxPlat` keeps `P = P(η₁) < F` up to `η₁ + Ω₁ ≥ η*`), so Theorem START gives
  `P(η₁ + Ω₁) = nxt V₁(P(η₁)) = F`, `η₁ + Ω₁` is good with index `F`, and it is the name.  A limit `q`
  (with `r = 0`) is impossible: each strict rise of `P` along `Ω₁·q''`, `q'' < q`, is a step of START, so the
  fixed points of `υ` would be cofinal below `F`;
* `fxIso_code`: `m_F = Ω₁`; `fxIso_theta`: `Θ_F(m_F) = Θ_F(Ω₁) = ρ_F = F`;
* `fxIso_exact` (**the notation statement at an isolated fixed point `F < cpB1`**): `Θ_F(m_F) = VzOrec(F)`
  (both are `F`), hence UPPER and LOWER at `F`, `r(F) = δ_F + F` the exact reach; `fxIso_capV`,
  `fxIso_capAt`: the caps (`r(F) < υ_{F+ω+2} ≤ cap(F) = P(η_F + Ω₁)`);
* `fxIso_range`: an isolated fixed point `F ≥ B₀` with `ρ_F < L(ω+1)` is in the range (`m_F = Ω₁ < P′`).

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Fx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Br Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp

variable {S : InaccSeq.{0}}

/-- A fixed point `G ≠ 0` of `υ` is a restart index. -/
theorem fx_ri_of_fix {G : Ordinal.{0}} (hG0 : G ≠ 0) (hfix : upsilon G = G) : IsRestartIdx G := by
  have hU : UpsPt G := hfix ▸ upsPt_upsilon (pos_iff_ne_zero.2 hG0)
  have hE : ω ^ G = G := upsPt_inE hU
  have hω : ω ≤ G :=
    calc ω = ω ^ (1 : Ordinal.{0}) := (opow_one ω).symm
      _ ≤ ω ^ G := opow_le_opow_right omega0_pos (Order.one_le_iff_ne_zero.2 hG0)
      _ = G := hE
  have h2 : (2 : Ordinal.{0}) ≤ G := (natCast_lt_omega0 2).le.trans hω
  refine ri_iff.2 ⟨hG0, ?_⟩
  rw [← cp_ww_eq]
  calc ω ^ (2 : Ordinal.{0}) ∣ ω ^ G := opow_dvd_opow ω h2
    _ = G := hE

theorem fx_Om1_pos : (0 : Ordinal.{0}) < Om 1 := zero_lt_one.trans one_lt_Om1

/-- `P(η) = υ_{ι(η)}`. -/
theorem fx_Pv_eq (η : Ordinal.{0}) : Pv S η = upsilon (iota S η) := (ups_iota S η).symm

/-- Theorem START at level `1`: `P(η₁ + Ω₁) = nxt V₁(P(η₁))` for a good multiple `η₁` of `Ω₁`. -/
theorem fx_start1 {η1 : Ordinal.{0}} (hg : Bt.Good S η1) (hd : Om 1 ∣ η1) :
    Pv S (η1 + Om 1) = nxt (VG 1) (Pv S η1) := by
  have h := start_all S 1 η1 hg (by rwa [opow_one]) fun δ hδ => by
    rw [Order.lt_one_iff] at hδ
    subst hδ
    exact lt_of_le_of_lt zero_le (lt_nxt (VG_normal 0) (VG_at_zero 0) _)
  rwa [opow_one] at h

/-- A fixed point of `υ` is a value of `V₁`. -/
theorem fx_mem_VG1 {F : Ordinal.{0}} (hfix : upsilon F = F) : F ∈ range (VG 1) := by
  have h : F ∈ range (VG (0 + 1)) := mem_range_VG_succ.2 (by rw [VG_zero]; exact hfix)
  rwa [zero_add] at h

/-- The last exponent of `η₁ + Ω₁` is `Ω₁`. -/
theorem fx_exp_add_Om1 (η1 : Ordinal.{0}) : cdExp (η1 + Om 1) = Om 1 := by
  rw [cpExp_add _ fx_Om1_ne]
  have h := cpExp_mul_succ (Om 1) 0
  rwa [zero_add, mul_one, Om1_opow] at h

/-- **The name of an isolated fixed point**: `η_F = η₁ + Ω₁`, `η₁` a good multiple of `Ω₁`, `P(η₁) < F`. -/
theorem fxIso_eta {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hiso : CpIso F)
    (hX : upsilon F < Pv S ηx) :
    ∃ η1, Bt.Good S η1 ∧ Om 1 ∣ η1 ∧ Pv S η1 < F ∧ cdEta S F = η1 + Om 1 := by
  obtain ⟨-, hι, -, -⟩ := cdEta_pv_spec (S := S) hF.1 hX
  obtain ⟨-, -, hww⟩ := cp_fix_facts hF hfix
  have h1F : (1 : Ordinal.{0}) < F :=
    lt_of_le_of_lt (Order.one_le_iff_pos.2 (mul_pos omega0_pos omega0_pos)) hww
  have hFmem := fx_mem_VG1 hfix
  -- the step: a good multiple `η₁` of `Ω₁` with `P(η₁) < F ≤ P(η₁ + Ω₁)` names `F` by `η₁ + Ω₁`
  have step : ∀ η1, Bt.Good S η1 → Om 1 ∣ η1 → Pv S η1 < F → F ≤ Pv S (η1 + Om 1) →
      cdEta S F = η1 + Om 1 := by
    intro η1 hg1 hd1 hlt1 hge1
    have hle : Pv S (η1 + Om 1) ≤ F := by
      rw [fx_start1 hg1 hd1]; exact nxt_le (VG_normal 1) (VG_at_zero 1) hFmem hlt1
    have hPF : Pv S (η1 + Om 1) = F := le_antisymm hle hge1
    have hgood : Bt.Good S (η1 + Om 1) := good_add hg1 (CSet.Om_mem (CSet.one_mem _ _))
    exact cdEta_unique hgood (iota_of_fix hPF hfix)
  -- the least `η` with `F ≤ ι(η)`
  have hne : ({η | F ≤ iota S η} : Set Ordinal.{0}).Nonempty := ⟨cdEta S F, hι.ge⟩
  set ηs := sInf {η | F ≤ iota S η} with hηs
  have hs : F ≤ iota S ηs := csInf_mem hne
  have hsle : ηs ≤ cdEta S F := csInf_le' (show cdEta S F ∈ {η | F ≤ iota S η} from hι.ge)
  have hmin : ∀ η < ηs, iota S η < F := fun η h =>
    not_le.1 (notMem_of_lt_csInf' (s := {η | F ≤ iota S η}) h)
  have hιs : iota S ηs = F := le_antisymm (hι ▸ iota_mono _ _ hsle) hs
  have hPs : Pv S ηs = F := by rw [fx_Pv_eq, hιs, hfix]
  have hPlt : ∀ η < ηs, Pv S η < F := fun η h => by
    rw [fx_Pv_eq]
    calc upsilon (iota S η) < upsilon F := upsilon_normal.strictMono (hmin η h)
      _ = F := hfix
  have hdec : ηs = Om 1 * (ηs / Om 1) + ηs % Om 1 := (div_add_mod ηs (Om 1)).symm
  have hr1 : ηs % Om 1 < Om 1 := mod_lt _ fx_Om1_ne
  rcases eq_or_ne (ηs % Om 1) 0 with hr0 | hr0
  · -- `η* = Ω₁·q`
    rw [hr0, add_zero] at hdec
    set q := ηs / Om 1 with hq
    rcases zero_or_succ_or_isSuccLimit q with hq0 | ⟨q', hq'⟩ | hql
    · exfalso
      rw [hq0, mul_zero] at hdec
      rw [hdec, iota_zero] at hιs
      exact h1F.ne hιs
    · have hsplit : ηs = Om 1 * q' + Om 1 := by rw [hdec, ← hq', succ_eq_add_one, mul_add_one]
      have hlt1 : Pv S (Om 1 * q') < F := hPlt _ (by rw [hsplit]; exact lt_add_of_pos_right _ fx_Om1_pos)
      by_cases hg1 : Bt.Good S (Om 1 * q')
      · exact ⟨_, hg1, dvd_mul_right _ _, hlt1,
          step _ hg1 (dvd_mul_right _ _) hlt1 (by rw [← hsplit, hPs])⟩
      · exfalso
        have h := fxPlat_Om1 hg1
        rw [← hsplit, hPs] at h
        exact hlt1.ne h.symm
    · -- a limit `q`: the fixed points of `υ` would be cofinal below `F`
      exfalso
      obtain ⟨ν, hνF, hν⟩ := hiso
      have hlimS : IsSuccLimit ηs := by rw [hdec]; exact isSuccLimit_mul_right fx_Om1_pos hql
      haveI : Nonempty (Iio ηs) := ⟨⟨0, hlimS.bot_lt⟩⟩
      have hsup : ν < ⨆ e : Iio ηs, iota S e.1 := by rw [← iota_limit hlimS, hιs]; exact hνF
      obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd ηs)).1 hsup
      have he2 : e.1 < Om 1 * q := hdec ▸ e.2
      obtain ⟨q0, hq0, heq0⟩ := (lt_mul_iff_of_isSuccLimit hql).1 he2
      have hνq0 : ν < iota S (Om 1 * q0) := he.trans_le (iota_mono _ _ heq0.le)
      have hq0s : Om 1 * q0 < ηs := by rw [hdec]; exact (mul_lt_mul_iff_right₀ fx_Om1_pos).2 hq0
      have hx0F : Pv S (Om 1 * q0) < F := hPlt _ hq0s
      have hνx0 : ν < Pv S (Om 1 * q0) := by
        rw [fx_Pv_eq]; exact hνq0.trans_le upsilon_normal.strictMono.le_apply
      -- the first `q₂` with `P(Ω₁·q₂) > P(Ω₁·q₀)`
      have hqmem : q ∈ {q'' | Pv S (Om 1 * q0) < Pv S (Om 1 * q'')} := by
        show Pv S (Om 1 * q0) < Pv S (Om 1 * q)
        rw [← hdec, hPs]; exact hx0F
      set q2 := sInf {q'' | Pv S (Om 1 * q0) < Pv S (Om 1 * q'')} with hq2def
      have hq2 : Pv S (Om 1 * q0) < Pv S (Om 1 * q2) := csInf_mem ⟨q, hqmem⟩
      have hq2le : q2 ≤ q := csInf_le' hqmem
      have hbelow : ∀ q'' < q2, Pv S (Om 1 * q'') ≤ Pv S (Om 1 * q0) := fun q'' h =>
        not_lt.1 (notMem_of_lt_csInf' (s := {q'' | Pv S (Om 1 * q0) < Pv S (Om 1 * q'')}) h)
      have hq0q2 : q0 < q2 := by
        by_contra h
        rw [not_lt] at h
        exact absurd hq2 (not_lt.2 (Pv_mono (mul_le_mul_right h _)))
      rcases zero_or_succ_or_isSuccLimit q2 with h0 | ⟨q3, hq3⟩ | hl2
      · rw [h0] at hq0q2; exact absurd hq0q2 (not_lt.2 zero_le)
      · have hq3lt : q3 < q2 := by rw [← hq3]; exact lt_succ q3
        have hq0q3 : q0 ≤ q3 := Order.lt_succ_iff.1 (hq3 ▸ hq0q2)
        have hPq3 : Pv S (Om 1 * q3) = Pv S (Om 1 * q0) :=
          le_antisymm (hbelow q3 hq3lt) (Pv_mono (mul_le_mul_right hq0q3 _))
        have hsplit : Om 1 * q2 = Om 1 * q3 + Om 1 := by rw [← hq3, succ_eq_add_one, mul_add_one]
        by_cases hg3 : Bt.Good S (Om 1 * q3)
        · have hst := fx_start1 hg3 (dvd_mul_right _ _)
          rw [← hsplit, hPq3] at hst
          have hGfix : upsilon (Pv S (Om 1 * q2)) = Pv S (Om 1 * q2) := by
            rw [hst]; exact ups_fix_of_VG one_ne_zero (nxt_mem _ _)
          have hGF : Pv S (Om 1 * q2) < F := by
            rcases hq2le.lt_or_eq with hlt | heq
            · exact hPlt _ (by rw [hdec]; exact (mul_lt_mul_iff_right₀ fx_Om1_pos).2 hlt)
            · exfalso
              have : q = succ q3 := by rw [← heq, hq3]
              exact hql.isSuccPrelimit.succ_ne q3 this.symm
          have hG0 : Pv S (Om 1 * q2) ≠ 0 := (Pv_SC S _).1.ne'
          have hri := fx_ri_of_fix hG0 hGfix
          have := hν _ hri (hνx0.trans hq2) hGF
          rw [hGfix] at this
          exact lt_irrefl _ this
        · have h := fxPlat_Om1 hg3
          rw [← hsplit, hPq3] at h
          rw [h] at hq2
          exact lt_irrefl _ hq2
      · have hle : Pv S (Om 1 * q2) ≤ Pv S (Om 1 * q0) := by
          have h := cont_le (S := S) (η0 := 0) (B := Pv S (Om 1 * q0))
            (isSuccLimit_mul_right fx_Om1_pos hl2) fun c hc => by
              obtain ⟨q'', hq'', hc'⟩ := (lt_mul_iff_of_isSuccLimit hl2).1 hc
              rw [zero_add]
              exact (Pv_mono hc'.le).trans (hbelow q'' hq'')
          rwa [zero_add] at h
        exact absurd hq2 (not_lt.2 hle)
  · -- `η* = Ω₁·q + r`, `r ≠ 0`
    have hlt1 : Pv S (Om 1 * (ηs / Om 1)) < F :=
      hPlt _ (by conv_rhs => rw [hdec]
                 exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hr0))
    by_cases hg1 : Bt.Good S (Om 1 * (ηs / Om 1))
    · refine ⟨_, hg1, dvd_mul_right _ _, hlt1, step _ hg1 (dvd_mul_right _ _) hlt1 ?_⟩
      rw [← hPs]
      refine Pv_mono ?_
      conv_lhs => rw [hdec]
      exact (add_lt_add_iff_left _).2 hr1 |>.le
    · exfalso
      have h := (fxPlat hg1 hr1).1
      rw [← hdec, hPs] at h
      exact hlt1.ne h.symm

/-- **`m_F = Ω₁`** at an isolated fixed point with a name. -/
theorem fxIso_code {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hiso : CpIso F)
    (hX : upsilon F < Pv S ηx) : cdCode S F = Om 1 := by
  obtain ⟨η1, -, -, -, he⟩ := fxIso_eta hF hfix hiso hX
  have hexp : cdExp (cdEta S F) = Om 1 := by rw [he]; exact fx_exp_add_Om1 η1
  unfold cdCode
  rw [cdCodeOf_of_lt (by rw [hexp]; exact Om_lt_Om.2 (lt_add_of_pos_right 1 zero_lt_one)), hexp,
    cpOff_of_ge (omega0_lt_Om one_ne_zero).le]

/-- **`Θ_F(m_F) = F`** at an isolated fixed point with a name. -/
theorem fxIso_theta {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hiso : CpIso F)
    (hX : upsilon F < Pv S ηx) : cdTheta S F (cdCode S F) = F := by
  rw [fxIso_code hF hfix hiso hX, cdTheta_Om1 (cdEta_pv hF.1 hX), hfix]

/-- **The notation statement at an isolated fixed point `F < cpB1`**: `Θ_F(m_F) = VzOrec(F)`, so UPPER,
LOWER, and `r(F) = δ_F + F` is the exact reach of `ρ_F`. -/
theorem fxIso_exact {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hFB : F < cpB1)
    (hiso : CpIso F) (hX : upsilon F < Pv S ηx) :
    cdTheta S F (cdCode S F) = VzOrec F ∧ cdCode S F = Om 1 ∧ VzOrec F = F ∧
      cdR S F = cdDelta F + F ∧ IsReach R2C (upsilon F) (cdR S F) ∧ CdUpper S F ∧ CdLower S F := by
  have hO := cpVz_iso hF hfix (hFB.trans cpB1_lt_Om1) hiso
  have hθ := fxIso_theta (S := S) hF hfix hiso hX
  have heq : cdTheta S F (cdCode S F) = VzOrec F := hθ.trans hO.symm
  have hex := (cpExact_iff (S := S) hF hFB).2 heq
  have hFδ : F < cdDelta F := by
    have := cdRho_lt_delta F; rwa [hfix] at this
  have hR : cdR S F = cdDelta F + F := by
    show cdk F (cdTheta S F (cdCode S F)) = _
    rw [hθ]; exact cpk_eq hF hFB hFδ
  exact ⟨heq, fxIso_code hF hfix hiso hX, hO, hR, cdExact_iff.1 hex, hex.1, hex.2⟩

/-- **The cap of the value** at an isolated fixed point `F < cpB1`. -/
theorem fxIso_capV {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hFB : F < cpB1)
    (hiso : CpIso F) (hX : upsilon F < Pv S ηx) : CdCapV S F := by
  obtain ⟨-, -, -, hR, -, -, -⟩ := fxIso_exact (S := S) hF hfix hFB hiso hX
  obtain ⟨η1, -, -, -, he⟩ := fxIso_eta (S := S) hF hfix hiso hX
  obtain ⟨hg', hι', -, hpv'⟩ := cdEta_pv_spec (S := S) hF.1 hX
  obtain ⟨-, hp, hww⟩ := cp_fix_facts hF hfix
  have hFδ : F < cdDelta F := by
    have := cdRho_lt_delta F; rwa [hfix] at this
  have hω : ω < F := lt_of_le_of_lt (le_mul_left _ omega0_pos) hww
  have h1 : (1 : Ordinal.{0}) < F := one_lt_omega0.trans hω
  have hw2 : (ω + 1 + 1 : Ordinal.{0}) < Pv S (cdEta S F) := by
    rw [hpv', hfix]; exact hp (hp hω h1) h1
  have hP : Pv S (cdEta S F + (ω + 1 + 1)) = upsilon (F + ω + 1 + 1) := by
    rw [fx_Pv_eq, cpIota_add hg' hw2, hι']; simp only [add_assoc]
  have hexp : cdExp (cdEta S F) = Om 1 := by rw [he]; exact fx_exp_add_Om1 η1
  have hle : ω + 1 + 1 ≤ ω ^ cdExp (cdEta S F) := by
    rw [hexp, Om1_opow]
    exact (fx_Om1_prin (fx_Om1_prin (omega0_lt_Om one_ne_zero) one_lt_Om1) one_lt_Om1).le
  unfold CdCapV cdCapB
  rw [hR]
  calc cdDelta F + F < upsilon (F + ω + 1 + 1) := cp_delta_add_lt hFδ
    _ = Pv S (cdEta S F + (ω + 1 + 1)) := hP.symm
    _ ≤ Pv S (cdEta S F + ω ^ cdExp (cdEta S F)) := Pv_mono (add_le_add le_rfl hle)

/-- **`ρ_F` is not self-crossing** at an isolated fixed point `F < cpB1`. -/
theorem fxIso_capAt {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hFB : F < cpB1)
    (hiso : CpIso F) (hX : upsilon F < Pv S ηx) : CdCapAt S F :=
  cdCapAt_of_upper (fxIso_exact hF hfix hFB hiso hX).2.2.2.2.2.1 (fxIso_capV hF hfix hFB hiso hX)

/-- **An isolated fixed point `F ≥ B₀` with `ρ_F < L(ω+1)` is in the range** (`m_F = Ω₁ < P′`). -/
theorem fxIso_range {F : Ordinal.{0}} (hF : IsRestartIdx F) (hB : cdB0 ≤ F) (hfix : upsilon F = F)
    (hiso : CpIso F) (hX : upsilon F < Nc.ncL S (ω + 1)) : CdRange S F := by
  refine ⟨hF, hB, hX, ?_⟩
  rw [fxIso_code hF hfix hiso (cp_name_L hX)]
  exact Lw.lw_Om1_lt_Pp S

end Googology.Trans.PoR.InaccPsi.R2.Fx
