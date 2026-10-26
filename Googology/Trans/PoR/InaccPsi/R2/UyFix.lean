import Googology.Trans.PoR.InaccPsi.R2.UvTr
import Googology.Trans.PoR.InaccPsi.R2.UhTerm
import Googology.Trans.PoR.InaccPsi.R2.CitedUc
import Googology.Trans.PoR.InaccPsi.R2.UcAt

/-!
# The code `π`-fix below `B₂` and the levels `Ω₁·M < B₂` of `ϑ`-nodes

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`B₂ = Uc.ucB = ψ_{Ω₂}(ε_{Ω₂+1})`, `E₁ = Gg.ggE = ε_{Ω₁+1}`, `X = Tl.tlX`, `π = pi σ τ`, `ucDat` the data of
`R2.UcDat` (the largest countable leaf of the canonical term of a code below `B₂`).

* `uy_map_fix` (**`ucMap f λ = λ` when `f` fixes every component of `λ`**), `uy_dat_cnf`, `uy_dat_phi` (the Cantor
  and the Veblen clause of `ucDat` on all of `(Ω₁, B₂)`, also below `X`);
* `uy_pi_fix` (**(C1) the code `π`-fix: `z < B₂`, `ucDat z < σ` ⇒ `z ∈ Tᵗ[σ]` and `π z = z`**), by induction over
  the clauses of `ucDat`: below `E₁` it is `Uh.uh_pi_fix`; a power `ω^l` with `l ≥ E₁` by `R2.ucOpow_TB`; an
  `ε`-number `φ(a, c)` by `R2.ucPhi_TB`; an atom `F_λ(y) < X` or `H_λ(y) ≥ X` by `R2.ucAtom_TB` (the atom `Γ_ν` with
  `ν = Ω₁ + 1 + d` through `R2.pi_Om1`, `R2.pi_add`);
* `UyLev` (**a level over `κ`**: `1 ≤ M`, `Ω₁·M < B₂`, `ucDat M < κ`, `ucDat(Ω₁·M) < κ`), `uyLev_of_uh`
  (**`Uh.UhLev κ M ⇒ UyLev κ M`**), and the node lemmas `uy_Om1_mul_TB` (**`Ω₁·M ∈ Tᵗ[σ]`, `π(Ω₁·M) = Ω₁·M`**),
  `uy_arg_T` (**`Ω₁·M + x ∈ Tᵗ ∩ Ω₂`**), `uyLt_vt_self` (**`x < ϑᵗ(Ω₁·M + x)`**: `R2.luLt_vt_self` for `M < Ω₁`,
  `R2.ucLevel_lt` for `M ≥ Ω₁`), `uyVt_tr` (**both translations of [W07a] Def 6.2 at a level over `κ < τ`**: the
  subcase `Γ^* < α` of `R2.uvVt_trL`; `ucDat(Ω₁·M) < κ < τ < α`).

No new axiom.  New definition: `UyLev`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uy

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Rh

/-- **`ucMap f λ = λ` when `f` fixes every component of `λ`.** -/
theorem uy_map_fix (f : Ordinal.{0} → Ordinal.{0}) :
    ∀ γ : Ordinal.{0}, (∀ x ∈ ucComps γ, f x = x) → ucMap f γ = γ := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hf
  by_cases h1 : γ < OmTwo
  · rw [ucMap_small f h1]; exact hf γ (by rw [ucComps_small h1]; exact mem_singleton _)
  by_cases h2 : γ < ucE
  · have h1' := not_lt.1 h1
    have hc := ucComps_big h1' h2
    have hl : ucMap f (log OmTwo γ) = log OmTwo γ :=
      IH _ (uc_log_lt h1' h2) (fun x hx => hf x (by rw [hc]; exact Or.inl hx))
    have hr : ucMap f (γ % OmTwo ^ log OmTwo γ) = γ % OmTwo ^ log OmTwo γ :=
      IH _ (uc_mod_lt h1') (fun x hx => hf x (by rw [hc]; exact Or.inr (Or.inr hx)))
    have hd : f (γ / OmTwo ^ log OmTwo γ) = γ / OmTwo ^ log OmTwo γ :=
      hf _ (by rw [hc]; exact Or.inr (Or.inl rfl))
    rw [ucMap_big f h1' h2, hl, hr, hd]
    exact uc_cnf_eq γ
  · exact ucMap_out f (not_lt.1 h2)

/-- **The Cantor clause of `ucDat` on `(Ω₁, B₂)`.** -/
theorem uy_dat_cnf {z : Ordinal.{0}} (h1 : Om1 < z) (hB : z < ucB) (hE : ω ^ z ≠ z) :
    ucDat z = max (ucDat (log ω z)) (ucDat (z % ω ^ log ω z)) := by
  rcases lt_or_ge z tlX with hX | hX
  · have hl : log ω z < z := Tf.tf_log_lt h1 hE
    have hr : z % ω ^ log ω z < z := Rj.rj_mod_lt (Rj.rj_Om1_pos.trans h1).ne'
    rw [ucDat_lt_X hX, tlDat_cnf h1 hX hE, ucDat_lt_X (hl.trans hX), ucDat_lt_X (hr.trans hX)]
  · exact ucDat_cnf hX hB hE

/-- **The Veblen clause of `ucDat` on `(Ω₁, B₂)`.** -/
theorem uy_dat_phi {z : Ordinal.{0}} (h1 : Om1 < z) (hB : z < ucB) (hE : ω ^ z = z) (hI : invVeblen₁ z < z) :
    ucDat z = max (ucDat (invVeblen₁ z)) (ucDat (invVeblen₂ z)) := by
  rcases lt_or_ge z tlX with hX | hX
  · have hc : invVeblen₂ z < z := Tf.tf_inv2_lt hE
    rw [ucDat_lt_X hX, tlDat_phi h1 hX hE hI, ucDat_lt_X (hI.trans hX), ucDat_lt_X (hc.trans hX)]
  · exact ucDat_phi hX hB hE hI

/-- `x · k` for a finite `k` keeps the `π`-fix. -/
theorem uy_fix_mul_nat {σ τ x : Ordinal.{0}} (h : Bases σ τ) (hx : x ∈ TB τ σ ∧ pi σ τ x = x) :
    ∀ k : ℕ, x * (k : Ordinal.{0}) ∈ TB τ σ ∧ pi σ τ (x * (k : Ordinal.{0})) = x * (k : Ordinal.{0}) := by
  intro k
  induction k with
  | zero =>
    have h0σ : (0 : Ordinal.{0}) < σ := Si.si_inE_pos h.1
    simp only [Nat.cast_zero, mul_zero]; exact ⟨mem_TB_of_lt h h0σ, pi_lt h h0σ⟩
  | succ k ihk =>
    obtain ⟨c1, c2⟩ := pi_add h ihk.1 hx.1
    rw [Nat.cast_succ, mul_add_one]; exact ⟨c1, by rw [c2, ihk.2, hx.2]⟩

/-- **(C1) The code `π`-fix**: for bases `σ < τ`, every `z < B₂` with `ucDat z < σ` lies in `Tᵗ[σ]` and
`π_{σ,τ}(z) = z`. -/
theorem uy_pi_fix {σ τ : Ordinal.{0}} (h : Bases σ τ) :
    ∀ z, z < ucB → ucDat z < σ → z ∈ TB τ σ ∧ pi σ τ z = z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hzB hzd
  have h0σ : (0 : Ordinal.{0}) < σ := Si.si_inE_pos h.1
  have h1σ : (1 : Ordinal.{0}) < σ := Ub.ub_one_lt h.1
  rcases lt_or_ge z Gg.ggE with hzE | hzE
  · rw [Uv.uvDat_eq_rj hzE] at hzd
    exact Uh.uh_pi_fix h z hzE hzd
  have h1 : Om1 < z := Rj.rj_Om1_lt_E.trans_le hzE
  have hsub : ∀ b, b < z → ucDat b ≤ ucDat z → b ∈ TB τ σ ∧ pi σ τ b = b :=
    fun b hb hbd => IH b hb (hb.trans hzB) (hbd.trans_lt hzd)
  by_cases hE : ω ^ z = z
  · by_cases hI : invVeblen₁ z < z
    · -- an `ε`-number `z = φ(a, c)`
      set a := invVeblen₁ z with hadef
      set c := invVeblen₂ z with hcdef
      have hcz : c < z := Tf.tf_inv2_lt hE
      have hev : veblen a c = z := by rw [hadef, hcdef, veblen_invVeblen₁_invVeblen₂, hE]
      have ha0 : a ≠ 0 := by
        intro e
        rw [e, veblen_zero_apply] at hev
        have : ω ^ c = ω ^ z := by rw [hev, hE]
        exact absurd ((opow_right_inj one_lt_omega0).1 this) hcz.ne
      have hdat := uy_dat_phi h1 hzB hE hI
      obtain ⟨haT, haπ⟩ := hsub a hI ((le_max_left _ _).trans hdat.ge)
      obtain ⟨hcT, hcπ⟩ := hsub c hcz ((le_max_right _ _).trans hdat.ge)
      have hP := ucPhi_TB h (one_le_iff_ne_zero.2 ha0) (by rw [hev]; exact hI) (by rw [hev]; exact hcz)
        (by rw [hev]; exact h1) (by rw [hev]; exact hzB)
      rw [hev] at hP
      exact ⟨hP.1.2 ⟨haT, hcT⟩, by rw [hP.2 haT hcT, haπ, hcπ, hev]⟩
    -- an atom
    have hSC : SC z := tl_SC_of h1 hI
    have hA := ucAtom_TB h hSC h1 hzB
    rcases lt_or_ge z tlX with hX | hX
    · -- `z = F_λ(y) < X`
      obtain ⟨hnf, hyz, hlz⟩ := tl_nf hSC h1 hX
      have hparts : ucParts z = {tlLev z, tlI (tlLev z) z} := by rw [ucParts, if_pos hX]
      have hreb : ucRebuild (pi σ τ) z = rhF (pi σ τ (tlLev z)) (pi σ τ (tlI (tlLev z) z)) := by
        rw [ucRebuild, if_pos hX]
      have hd : ucDat z = tlDat z := ucDat_lt_X hX
      have hfix : (tlLev z ∈ TB τ σ ∧ pi σ τ (tlLev z) = tlLev z) ∧
          (tlI (tlLev z) z ∈ TB τ σ ∧ pi σ τ (tlI (tlLev z) z) = tlI (tlLev z) z) := by
        by_cases h0 : tlLev z = 0
        · -- the atom `Γ_ν`, `ν = Ω₁ + 1 + d`
          have hdz := tlDat_atom0 h1 hX hE hI h0
          have hdz' : Tf.tfIdx z - (Om1 + 1) < z := tl_atom0_lt h1 hX hI h0
          refine ⟨by rw [h0]; exact ⟨mem_TB_of_lt h h0σ, pi_lt h h0σ⟩, ?_⟩
          rw [h0, tlI_zero]
          have hgz : gamma (Tf.tfIdx z) = z := Tf.tf_SC_gamma h1 hI
          have hν1 : Om1 < Tf.tfIdx z := Tf.tf_Om1_lt_gamma.1 (by rw [hgz]; exact h1)
          have hνd : Om1 + 1 + (Tf.tfIdx z - (Om1 + 1)) = Tf.tfIdx z :=
            Ordinal.add_sub_cancel_of_le (Order.add_one_le_of_lt hν1)
          have hdd : ucDat (Tf.tfIdx z - (Om1 + 1)) = ucDat z := by
            rw [hd, hdz, ucDat_lt_X (hdz'.trans hX)]
          obtain ⟨hdT, hdπ⟩ := hsub _ hdz' hdd.le
          obtain ⟨o1, o2⟩ := pi_Om1 h
          obtain ⟨c1, c2⟩ := pi_add h o1 (mem_TB_of_lt h h1σ)
          obtain ⟨e1, e2⟩ := pi_add h c1 hdT
          rw [← hνd]
          exact ⟨e1, by rw [e2, c2, o2, pi_lt h h1σ, hdπ]⟩
        · have hdz := tlDat_atomF h1 hX hE hI h0
          have hl : ucDat (tlLev z) ≤ ucDat z := by
            rw [hd, hdz, ucDat_lt_X (hlz.trans hX)]; exact le_max_left _ _
          have hy : ucDat (tlI (tlLev z) z) ≤ ucDat z := by
            rw [hd, hdz, ucDat_lt_X (hyz.trans hX)]; exact le_max_right _ _
          exact ⟨hsub _ hlz hl, hsub _ hyz hy⟩
      have hall : ∀ x ∈ ucParts z, x ∈ TB τ σ := by
        rw [hparts]
        rintro x (hx | hx)
        · rw [hx]; exact hfix.1.1
        · rw [mem_singleton_iff] at hx; rw [hx]; exact hfix.2.1
      refine ⟨hA.1.2 hall, ?_⟩
      rw [hA.2 hall, hreb, hfix.1.2, hfix.2.2, hnf]
    · -- `z = H_λ(y) ≥ X`
      have hne := uc_nf_of_lt hSC h1 hzB
      obtain ⟨-, hlv, -, -, -⟩ := ucLev_spec hSC h1 hne
      obtain ⟨hnf, hyz⟩ := uc_nf hSC h1 hne
      have hdat := ucDat_atom hX hzB hE hI
      have hparts : ucParts z = ucComps (ucLev z) ∪ {ucI (ucLev z) z} := by
        rw [ucParts, if_neg (not_lt.2 hX)]
      have hreb : ucRebuild (pi σ τ) z = ucH (ucMap (pi σ τ) (ucLev z)) (pi σ τ (ucI (ucLev z) z)) := by
        rw [ucRebuild, if_neg (not_lt.2 hX)]
      have hcf : ∀ x ∈ ucComps (ucLev z), x ∈ TB τ σ ∧ pi σ τ x = x := fun x hx =>
        hsub x ((le_ucC hx).trans_lt hlv)
          (((ucFold_le_of_mem ucDat _ x hx).trans (le_max_left _ _)).trans hdat.ge)
      have hyf := hsub _ hyz ((le_max_right _ _).trans hdat.ge)
      have hall : ∀ x ∈ ucParts z, x ∈ TB τ σ := by
        rw [hparts]
        rintro x (hx | hx)
        · exact (hcf x hx).1
        · rw [mem_singleton_iff] at hx; rw [hx]; exact hyf.1
      refine ⟨hA.1.2 hall, ?_⟩
      rw [hA.2 hall, hreb, uy_map_fix _ _ (fun x hx => (hcf x hx).2), hyf.2, hnf]
  · -- not an `ε`-number: `z = ω^l·v + r`
    have hz0 : z ≠ 0 := (Rj.rj_Om1_pos.trans h1).ne'
    obtain ⟨hdec, -, hvω, -⟩ := Si.si_dec hz0
    have hdat := uy_dat_cnf h1 hzB hE
    have hlz : log ω z < z := Tf.tf_log_lt h1 hE
    have hrz : z % ω ^ log ω z < z := Rj.rj_mod_lt hz0
    obtain ⟨hlT, hlπ⟩ := hsub _ hlz ((le_max_left _ _).trans hdat.ge)
    obtain ⟨hrT, hrπ⟩ := hsub _ hrz ((le_max_right _ _).trans hdat.ge)
    have hwz : ω ^ log ω z ≤ z := opow_log_le_self ω hz0
    have hwT : ω ^ log ω z ∈ TB τ σ ∧ pi σ τ (ω ^ log ω z) = ω ^ log ω z := by
      by_cases hl : ω ^ log ω z = log ω z
      · rw [hl]; exact ⟨hlT, hlπ⟩
      · have hlE : Gg.ggE ≤ log ω z :=
          le_log_of_opow_le one_lt_omega0 (by rw [Gg.ggE_spec.1]; exact hzE)
        obtain ⟨o1, o2⟩ := ucOpow_TB h hlE hl (hwz.trans_lt hzB)
        exact ⟨o1.2 hlT, by rw [o2 hlT, hlπ]⟩
    obtain ⟨k, hk⟩ := Ordinal.lt_omega0.1 hvω
    have hm := uy_fix_mul_nat h hwT k
    obtain ⟨c1, c2⟩ := pi_add h hm.1 hrT
    rw [← hdec, hk]
    exact ⟨c1, by rw [c2, hm.2, hrπ]⟩

/-! ## The levels of `ϑ`-nodes below `B₂` -/

/-- **A level over `κ`**: `1 ≤ M`, `Ω₁·M < B₂`, with countable data `ucDat M < κ` and `ucDat(Ω₁·M) < κ`. -/
def UyLev (κ M : Ordinal.{0}) : Prop := 1 ≤ M ∧ Om1 * M < ucB ∧ ucDat M < κ ∧ ucDat (Om1 * M) < κ

theorem UyLev.mono {κ κ' M : Ordinal.{0}} (hκ : κ ≤ κ') (h : UyLev κ M) : UyLev κ' M :=
  ⟨h.1, h.2.1, h.2.2.1.trans_le hκ, h.2.2.2.trans_le hκ⟩

/-- **`Uh.UhLev κ M ⇒ UyLev κ M`** (`Ω₁·M < ε_{Ω₁+1}`, `ucDat = rjDat` there, `Ur.urDat_le`). -/
theorem uyLev_of_uh {κ M : Ordinal.{0}} (h : Uh.UhLev κ M) : UyLev κ M := by
  have hΓE : Om1 * M < Gg.ggE := Si.si_E_inE.mul_lt Rj.rj_Om1_lt_E h.2.1
  have hEB : Gg.ggE < ucB := Uv.uv_E_lt_B
  refine ⟨h.1, hΓE.trans hEB, ?_, ?_⟩
  · rw [Uv.uvDat_eq_rj h.2.1]; exact h.2.2
  · rw [Uv.uvDat_eq_rj hΓE]; exact (Ur.urDat_le h.2.1).trans_lt h.2.2

/-- `M ≤ Ω₁·M < B₂`. -/
theorem uyLev_lt_B {κ M : Ordinal.{0}} (h : UyLev κ M) : M < ucB :=
  (le_mul_right M Rj.rj_Om1_pos).trans_lt h.2.1

/-- **`Ω₁·M ∈ Tᵗ[σ]` and `π_{σ,τ}(Ω₁·M) = Ω₁·M`** for a level over `κ ≤ σ`. -/
theorem uy_Om1_mul_TB {κ σ τ M : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) (hM : UyLev κ M) :
    Om1 * M ∈ TB τ σ ∧ pi σ τ (Om1 * M) = Om1 * M :=
  uy_pi_fix h _ hM.2.1 (hM.2.2.2.trans_le hκσ)

/-- **`Ω₁·M + x ∈ Tᵗ` and `< Ω₂`** for a level `M` over `κ` (`κ < τ` a base) and `x ∈ Tᵗ ∩ Ω₁`. -/
theorem uy_arg_T {κ τ M x : Ordinal.{0}} (hB : Bases κ τ) (hM : UyLev κ M) (hx : x ∈ Tset τ) (hx1 : x < Om1) :
    Om1 * M + x ∈ Tset τ ∧ Om1 * M + x < OmTwo := by
  have hΓ := (uy_Om1_mul_TB hB le_rfl hM).1.1
  refine ⟨vzT_add hB.2.1 hB.2.2.2 hΓ hx, ?_⟩
  exact (Lq.lq_SC_indec uc_SC_Om2).add_lt (hM.2.1.trans ucB_lt_Om2) (hx1.trans uc_Om1_lt_Om2)

/-- **The countable part is below the value**: `x < ϑᵗ(Ω₁·M + x)` for a level `M` over `κ < τ` and
`x ∈ Tᵗ ∩ Ω₁` ([W07a] Lemma 3.30: `R2.luLt_vt_self` for `M < Ω₁`, `R2.ucLevel_lt` for `M ≥ Ω₁`). -/
theorem uyLt_vt_self {κ τ M x : Ordinal.{0}} (hB : Bases κ τ) (hM : UyLev κ M) (hx : x ∈ Tset τ)
    (hx1 : x < Om1) : x < vt τ (Om1 * M + x) := by
  rcases lt_or_ge M Om1 with hM1 | hM1
  · have hMκ : M < κ := by rw [← ucDat_small hM1]; exact hM.2.2.1
    exact luLt_vt_self hB.2.1 hB.2.2.2 hM.1 (hMκ.trans hB.2.2.1) hx hx1
  · exact (ucLevel_lt hB.2.1 hB.2.2.2 hM1 (uyLev_lt_B hM)
      (Uh.uh_T_le hB.2.1 hB.2.2.2 (hM.2.2.1.trans hB.2.2.1).le) hx hx1).2

/-- **Both translations of [W07a] Def 6.2 at a level over `κ < τ`** (the subcase `Γ^* < α` of `R2.uvVt_trL`:
`ucDat(Ω₁·M) < κ < τ < α`): the same statement as `R2.uhVt_tr`, for every level `Ω₁·M < B₂`. -/
theorem uyVt_tr {κ τ : Ordinal.{0}} (hB : Bases κ τ) {n : ℕ} (hn : 1 ≤ n) {M ρ : Ordinal.{0}}
    (hM : UyLev κ M) (hρ1 : ρ < Om1) :
    (Om1 * M + ρ ∈ Tset (Dl τ n) → vt (Dl τ n) (Om1 * M + ρ) < Dp τ n →
      vt (Dl τ n) (Om1 * M + ρ) = vt τ (Om1 * M + (Dl τ n + ρ))) ∧
    (Om1 * M + (Dl τ n + ρ) ∈ Tset τ → vt τ (Om1 * M + (Dl τ n + ρ)) < Dp τ n →
      vt τ (Om1 * M + (Dl τ n + ρ)) = vt (Dl τ n) (Om1 * M + ρ)) := by
  have hα : ucDat (Om1 * M) < Dl τ n :=
    hM.2.2.2.trans (hB.2.2.1.trans (Dl_E hB.2.1 hB.2.2.2 hn).1)
  obtain ⟨h1, h2⟩ := uvVt_trL hB.2.1 hB.2.2.2 hn hM.1 hM.2.1 hα hρ1
  exact ⟨fun a b => (h1 a b).2, fun a b => (h2 a b).2⟩

/-! ## The data of a level and the data of `Ω₁·M` -/

/-- `Ω₁ < x < E₁` is not an `ε`-number. -/
theorem uy_not_eps {x : Ordinal.{0}} (h1 : Om1 < x) (h2 : x < Gg.ggE) : ω ^ x ≠ x := by
  intro hE
  exact absurd (Gg.ggE_le hE (by rw [← Rj.rj_Om1]; exact h1)) (not_le.2 h2)

/-- The data of `x = ω^g·v + r ∈ (Ω₁, B₂)` (`0 < v < ω`, `r < ω^g`, `x` not an `ε`-number): `max(ucDat g, ucDat r)`. -/
theorem uy_dat_form {g v r : Ordinal.{0}} (hv : v ≠ 0) (hvω : v < ω) (hr : r < ω ^ g)
    (h1 : Om1 < ω ^ g * v + r) (hB : ω ^ g * v + r < ucB) (hE : ω ^ (ω ^ g * v + r) ≠ ω ^ g * v + r) :
    ucDat (ω ^ g * v + r) = max (ucDat g) (ucDat r) := by
  obtain ⟨hl, hm⟩ := Si.si_log_mod hv hvω hr
  rw [uy_dat_cnf h1 hB hE, hm, hl]

/-- `ucDat(Ω₁ + c) = c` for `c < Ω₁`. -/
theorem uy_dat_Om1_add_small {c : Ordinal.{0}} (hc : c < Om1) : ucDat (Om1 + c) = c := by
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [add_zero, ucDat_Om1]
  have hx : Om1 + c = ω ^ Om1 * 1 + c := by rw [Rj.rj_Om1_opow, mul_one]
  have h1 : Om1 < Om1 + c := Si.si_Om1_lt_Om1_add hc0
  have h2 : Om1 + c < Gg.ggE := Si.si_E_inE.add_lt Rj.rj_Om1_lt_E (hc.trans Rj.rj_Om1_lt_E)
  have hcw : c < ω ^ Om1 := by rw [Rj.rj_Om1_opow]; exact hc
  have hE := uy_not_eps h1 h2
  rw [hx] at h1 h2 hE ⊢
  rw [uy_dat_form one_ne_zero one_lt_omega0 hcw h1 (h2.trans Uv.uv_E_lt_B) hE, ucDat_Om1, ucDat_small hc]
  exact max_eq_right zero_le

/-- `ucDat(Ω₁ + l) = ucDat l` for `l ≥ Ω₁`, `Ω₁ + l < B₂`. -/
theorem uy_dat_Om1_add {l : Ordinal.{0}} (hl1 : Om1 ≤ l) (hB : Om1 + l < ucB) : ucDat (Om1 + l) = ucDat l := by
  have hl0 : l ≠ 0 := (Rj.rj_Om1_pos.trans_le hl1).ne'
  have hg := Si.si_Om1_le_log hl1
  rcases hg.lt_or_eq with hgt | heq
  · have hlt' : Om1 < ω ^ log ω l := by
      rw [← Rj.rj_Om1_opow]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hgt
    rw [Ordinal.add_of_omega0_opow_le hlt' (opow_log_le_self ω hl0)]
  · obtain ⟨hdec, hv0, hvω, hr⟩ := Si.si_dec hl0
    have hOm : ω ^ log ω l = ω ^ Om1 := by rw [← heq]
    have hlE : l < Gg.ggE := by
      refine (lt_opow_succ_log_self one_lt_omega0 l).trans (Si.si_E_inE.opow_lt ?_)
      rw [← heq, Order.succ_eq_add_one]
      exact Si.si_E_inE.add_lt Rj.rj_Om1_lt_E (Ub.ub_one_lt Si.si_E_inE)
    have h1E : Om1 + l < Gg.ggE := Si.si_E_inE.add_lt Rj.rj_Om1_lt_E hlE
    set v := l / ω ^ log ω l with hvdef
    set s := l % ω ^ log ω l with hsdef
    have hs : s < ω ^ Om1 := by rw [← hOm]; exact hr
    have hsum : Om1 + l = ω ^ Om1 * (1 + v) + s := by
      conv_lhs => rw [← hdec, hOm]
      rw [Rj.rj_Om1_opow, mul_add, mul_one, add_assoc]
    have hv1 : 1 + v ≠ 0 := (lt_of_lt_of_le zero_lt_one le_self_add).ne'
    have hv1ω : 1 + v < ω := by
      obtain ⟨m, hm⟩ := Ordinal.lt_omega0.1 hvω
      rw [hm]; exact_mod_cast natCast_lt_omega0 (1 + m)
    have h1 : Om1 < Om1 + l := Si.si_Om1_lt_Om1_add hl0
    have hE := uy_not_eps h1 h1E
    have hB' := hB
    rw [hsum] at h1 hE hB'
    rw [hsum, uy_dat_form hv1 hv1ω hs h1 hB' hE]
    rcases hl1.lt_or_eq with hlt | hle
    · have hl' : l = ω ^ Om1 * v + s := by rw [← hOm]; exact hdec.symm
      have hE' := uy_not_eps hlt hlE
      have h1' := hlt
      have hB'' : l < ucB := hlE.trans Uv.uv_E_lt_B
      rw [hl'] at hE' h1' hB''
      rw [hl', uy_dat_form hv0 hvω hs h1' hB'' hE']
    · -- `l = Ω₁`: `s = 0`
      have hs0 : s = 0 := by
        rw [hsdef, ← heq, Rj.rj_Om1_opow, ← hle, Ordinal.mod_self]
      rw [← hle, hs0, ucDat_Om1, ucDat_small Rj.rj_Om1_pos, max_self]

/-- If `Ω₁·M` is an `ε`-number and `Ω₁ < M`, then `M` is one (`Ω₁·M` is multiplicatively principal). -/
theorem uy_eps_of_mul {M : Ordinal.{0}} (h1 : Om1 < M) (hE : ω ^ (Om1 * M) = Om1 * M) : ω ^ M = M := by
  have hMz : M ≤ Om1 * M := le_mul_right M Rj.rj_Om1_pos
  have hP : IsPrincipal (· * ·) (Om1 * M) := by
    have := isPrincipal_mul_omega0_opow_opow (Om1 * M)
    rwa [hE, hE] at this
  rcases hMz.lt_or_eq with hlt | heq
  · exact absurd (hP (h1.trans_le hMz) hlt) (lt_irrefl _)
  · rw [heq]; exact hE

/-- **The data of a level from the data of `Ω₁·M`**: for an `ε`-number `κ`, `M ≠ 0`, `Ω₁·M < B₂`:
`ucDat(Ω₁·M) < κ ⇒ ucDat M < κ` (the finite coefficients of `M` are absorbed by `κ`). -/
theorem uy_dat_of_mul {κ : Ordinal.{0}} (hκ : InE κ) :
    ∀ M, M ≠ 0 → Om1 * M < ucB → ucDat (Om1 * M) < κ → ucDat M < κ := by
  have hκω : ω ≤ κ := by
    have h1 : ω ≤ ω ^ κ := left_le_opow ω (InE.pos hκ)
    have h2 : ω ^ κ = κ := hκ
    exact h2 ▸ h1
  have hOm : InE (Om1 : Ordinal.{0}) := Rj.rj_Om1_opow
  intro M
  induction M using WellFoundedLT.induction with
  | ind M IH =>
  intro hM0 hMB hMd
  obtain ⟨hdec, hv0, hvω, hr⟩ := Si.si_dec hM0
  have hrM : M % ω ^ log ω M < M := Rj.rj_mod_lt hM0
  set l := log ω M with hldef
  set v := M / ω ^ l with hvdef
  set r := M % ω ^ l with hrdef
  have hwl : Om1 * ω ^ l = ω ^ (Om1 + l) := Si.si_Om1_opow_eq l
  have hz : Om1 * M = ω ^ (Om1 + l) * v + Om1 * r := by
    conv_lhs => rw [← hdec]
    rw [mul_add, ← mul_assoc, hwl]
  have hrz : Om1 * r < ω ^ (Om1 + l) := by
    rw [← hwl]; exact (mul_lt_mul_iff_right₀ Rj.rj_Om1_pos).2 hr
  have hwz : ω ^ (Om1 + l) ≤ Om1 * M := by
    rw [hz]; exact (le_mul_left _ (pos_iff_ne_zero.2 hv0)).trans le_self_add
  have hlB : Om1 + l < ucB := ((right_le_opow _ one_lt_omega0).trans hwz).trans_lt hMB
  have hrB : Om1 * r < ucB := ((mul_lt_mul_iff_right₀ Rj.rj_Om1_pos).2 hrM).trans hMB
  rcases lt_or_ge l Om1 with hl | hl
  · -- a countable level: `M < ω^{l+1} ≤ κ`
    have hM1 : M < Om1 := (lt_opow_succ_log_self one_lt_omega0 M).trans
      (hOm.opow_lt (by rw [Order.succ_eq_add_one]; exact hOm.add_lt hl (Ub.ub_one_lt hOm)))
    rw [ucDat_small hM1]
    rcases eq_or_ne l 0 with h0 | h0
    · have hMω : M < ω := by
        have := lt_opow_succ_log_self one_lt_omega0 M
        rwa [← hldef, h0, Order.succ_eq_add_one, zero_add, opow_one] at this
      exact hMω.trans_le hκω
    · have hz1 : Om1 < Om1 * M := by
        refine lt_of_lt_of_le ?_ hwz
        have := (opow_lt_opow_iff_right one_lt_omega0).2 (Si.si_Om1_lt_Om1_add h0)
        rwa [Rj.rj_Om1_opow] at this
      have hzE : Om1 * M < Gg.ggE := Si.si_E_inE.mul_lt Rj.rj_Om1_lt_E (hM1.trans Rj.rj_Om1_lt_E)
      have hE := uy_not_eps hz1 hzE
      rw [hz] at hz1 hE hMB hMd
      rw [uy_dat_form hv0 hvω hrz hz1 hMB hE, uy_dat_Om1_add_small hl] at hMd
      have hlκ : l < κ := (le_max_left _ _).trans_lt hMd
      exact (lt_opow_succ_log_self one_lt_omega0 M).trans
        (hκ.opow_lt (by rw [Order.succ_eq_add_one]; exact hκ.add_lt hlκ (Ub.ub_one_lt hκ)))
  · have hM1 : Om1 ≤ M := hl.trans ((right_le_opow l one_lt_omega0).trans (opow_log_le_self ω hM0))
    rcases hM1.lt_or_eq with hM1 | hM1
    · by_cases hME : ω ^ M = M
      · -- an `ε`-number `M > Ω₁`: `Ω₁·M = M`
        have hadd : Om1 + M = M := Ordinal.add_of_omega0_opow_le (by rw [hME]; exact hM1) hME.le
        have hzM : Om1 * M = M := by
          calc Om1 * M = Om1 * ω ^ M := by rw [hME]
            _ = ω ^ (Om1 + M) := Si.si_Om1_opow_eq M
            _ = M := by rw [hadd, hME]
        rwa [hzM] at hMd
      · have hzE : ω ^ (Om1 * M) ≠ Om1 * M := fun h => hME (uy_eps_of_mul hM1 h)
        have hz1 : Om1 < Om1 * M := hM1.trans_le (le_mul_right M Rj.rj_Om1_pos)
        have hMB0 : M < ucB := (le_mul_right M Rj.rj_Om1_pos).trans_lt hMB
        rw [hz] at hzE hz1 hMB hMd
        rw [uy_dat_form hv0 hvω hrz hz1 hMB hzE, uy_dat_Om1_add hl hlB] at hMd
        rw [uy_dat_cnf hM1 hMB0 hME, ← hldef, ← hrdef]
        refine max_lt ((le_max_left _ _).trans_lt hMd) ?_
        rcases eq_or_ne r 0 with h0 | h0
        · rw [h0, ucDat_small Rj.rj_Om1_pos]; exact InE.pos hκ
        · exact IH r hrM h0 hrB ((le_max_right _ _).trans_lt hMd)
    · rw [← hM1, ucDat_Om1]; exact InE.pos hκ

/-- **`UyLev` is the level condition of the twin citation**: for an `ε`-number `κ`, `UyLev κ M` iff `1 ≤ M`,
`Ω₁·M < B₂` and `ucDat(Ω₁·M) < κ` (the extra conjunct `ucDat M < κ` follows by `uy_dat_of_mul`). -/
theorem uyLev_iff {κ M : Ordinal.{0}} (hκ : InE κ) :
    UyLev κ M ↔ 1 ≤ M ∧ Om1 * M < ucB ∧ ucDat (Om1 * M) < κ :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2.2⟩, fun h =>
    ⟨h.1, h.2.1, uy_dat_of_mul hκ M (one_le_iff_ne_zero.1 h.1) h.2.1 h.2.2, h.2.2⟩⟩

/-- **A new level**: `E₁ = ε_{Ω₁+1}` is a level over every `κ > 1` (`Ω₁·E₁ = E₁`, data `1`), but not a level of
`Uh.UhLev`. -/
theorem uyLev_E {κ : Ordinal.{0}} (hκ : 1 < κ) : UyLev κ Gg.ggE ∧ ¬ Uh.UhLev κ Gg.ggE := by
  have hd : ucDat Gg.ggE = 1 := by rw [← Uv.uv_Om1_mul_E]; exact Uv.uvDat_E
  refine ⟨⟨one_le_iff_ne_zero.2 (Rj.rj_Om1_pos.trans Rj.rj_Om1_lt_E).ne', ?_, ?_, ?_⟩, fun h => lt_irrefl _ h.2.1⟩
  · rw [Uv.uv_Om1_mul_E]; exact Uv.uv_E_lt_B
  · rw [hd]; exact hκ
  · rw [Uv.uvDat_E]; exact hκ

end Googology.Trans.PoR.InaccPsi.R2.Uy
