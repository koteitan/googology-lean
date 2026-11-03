import Googology.Trans.PoR.InaccPsi.R2.YjTop

/-!
# The bases `a + Ω₂·γ` above a base `a` with `Ω₂² ∣ a`: layers, atoms, finite support, the reading law

`κ₂ = Ω₂`, `H_λ = Cl(A_{η_λ}, ρ_λ)`, `ldAtR λ` its atoms below `Ω₂`, `Θ = gxTh ρ_λ (ldAtR λ)`,
`F^β = ψ_{Ω₂}(β + Ω₂)` (`Ld.ldTop`).  For a base `a` (own for every offset, `Ω₂² ∣ a`):
`L^a_0 = Ω₁`, `L^a_{j+1} = ψ_{Ω₂}(a + Ω₂·L^a_j)` (`ytLg`), `G^a = ψ_{Ω₂}(a + Ω₂·Ω₂)` (`ytG`).
This is `Ld.ldG2_base` / `ldG2_cls` / `ldG2_supp` / `ldLg` (base `0`, image `A + 1`) at a base `a` with image `Â`.

* `ytLg_sup` (**`G^a = sup_j L^a_j`**), `ytG_gt` (**`γ < ψ_{Ω₂}(a + Ω₂·γ)` for `γ < G^a`**), `ytG_ge`;
* `ytBase_own` (**`a + Ω₂·γ` is own** for every `γ < G^a`);
* `ytCls` (**every atom below `ψ_{Ω₂}(a + Ω₂·γ)` is `≤ ψ_{Ω₂}(a)`, or in the block of a code `γ'' < γ`**),
  `ytClsAll` (every atom in `(ψ_{Ω₂}(a), G^a)` is `ψ_{Ω₂}(a + Ω₂·γ + c)`, `γ < G^a`, `c < F^{a+Ω₂·γ}` codes),
  `ytSupp` (**finite support** at a limit `γ`);
* `ytLaw` (**`Θ(ψ_{Ω₂}(a + Ω₂·γ)) = ψ_{Ω₁}(Â + Ω₁·Θγ)`** for every code `γ < G^a`, given `Θ(ψ_{Ω₂} a) = ψ_{Ω₁} Â`
  with `Â` own), `ytLawTh` (`Θ(ψ_{Ω₂}(a + Ω₂·γ + c)) = ψ_{Ω₁}(Â + Ω₁·Θγ + Θc)`).

No new axiom.  New definitions: `ytLg`, `ytG` (ordinal terms, no statement depends on them beyond this file's).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Sf
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ld

variable {S : InaccSeq.{0}}

/-- `L^a_0 = Ω₁`, `L^a_{j+1} = ψ_{Ω₂}(a + Ω₂·L^a_j)`. -/
noncomputable def ytLg (S : InaccSeq.{0}) (a : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => Om 1
  | j + 1 => S.psi (a + Om (1 + 1) * ytLg S a j) (Om (1 + 1))

/-- `G^a = ψ_{Ω₂}(a + Ω₂·Ω₂)`. -/
noncomputable def ytG (S : InaccSeq.{0}) (a : Ordinal.{0}) : Ordinal.{0} :=
  S.psi (a + Om (1 + 1) * Om (1 + 1)) (Om (1 + 1))

theorem ytG_SC (a : Ordinal.{0}) : SC (ytG S a) := SC_psi (InR_Om_succ 1) _
theorem ytG_lt_Om2 (a : Ordinal.{0}) : ytG S a < Om (1 + 1) := psi_lt (InR_Om_succ 1) _
theorem ytOm1_lt_G (a : Ordinal.{0}) : Om (1 : Ordinal.{0}) < ytG S a := (psiS_bounds (S := S) _ 1).1

theorem ytLg_lt_Om2 (a : Ordinal.{0}) : ∀ j, ytLg S a j < Om (1 + 1)
  | 0 => gg_Om1_lt_Om2
  | _ + 1 => psi_lt (InR_Om_succ 1) _

theorem ytLg_SC (a : Ordinal.{0}) : ∀ j, SC (ytLg S a j)
  | 0 => Ph.ph_SC_Om1
  | _ + 1 => SC_psi (InR_Om_succ 1) _

/-- own for one offset `≤ Ω₂` gives own for every offset. -/
theorem ytOwnAll {a : Ordinal.{0}}
    (hown : ∀ d, d ≤ Om (1 + 1) → a ∈ S.CSet (a + d) (S.psi (a + d) (Om (1 + 1)))) :
    ∀ d, a ∈ S.CSet (a + d) (S.psi (a + d) (Om (1 + 1))) := by
  intro d
  rcases le_total d (Om (1 + 1)) with h | h
  · exact hown d h
  · exact (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left a).2 h)).2 (hown _ le_rfl)

section Lay

variable {a : Ordinal.{0}}
  (hown : ∀ d, d ≤ Om (1 + 1) → a ∈ S.CSet (a + d) (S.psi (a + d) (Om (1 + 1))))

include hown

theorem ytLg_lt_succ : ∀ j, ytLg S a j < ytLg S a (j + 1)
  | 0 => (psiS_bounds (S := S) _ 1).1
  | j + 1 => by
    have IH := ytLg_lt_succ j
    have hle : ytLg S a (j + 1) ≤ ytLg S a (j + 2) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left a).2 (ldOm2_mul_mono IH.le))).1
    refine psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left a).2 (ldOm2_mul_lt IH)) ?_
    exact CSet.add_mem (ytOwnAll hown _)
      (ldMulK_small ldOm2_SC (mxOm2_mem _ _) _ (IH.trans_le hle))

theorem ytLg_mono {j j' : ℕ} (h : j ≤ j') : ytLg S a j ≤ ytLg S a j' :=
  (strictMono_nat_of_lt_succ (fun k => ytLg_lt_succ hown k)).monotone h

omit hown in
/-- `γ < ψ_{Ω₂}(a + Ω₂·γ)` below every `L^a_j`. -/
theorem ytLg_gt : ∀ j γ, γ < ytLg S a j → γ < S.psi (a + Om (1 + 1) * γ) (Om (1 + 1))
  | 0, γ, h => h.trans (psiS_bounds (S := S) _ 1).1
  | j + 1, γ, h => by
    rcases lt_or_ge γ (ytLg S a j) with h' | h'
    · exact ytLg_gt j γ h'
    · exact h.trans_le (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left a).2 (ldOm2_mul_mono h'))).1

omit hown in
theorem ytLg_le_G : ∀ j, ytLg S a j ≤ ytG S a
  | 0 => (ytOm1_lt_G a).le
  | j + 1 => (psi_mono (S := S) (InR_Om_succ 1)
      ((add_le_add_iff_left a).2 (ldOm2_mul_mono (ytLg_lt_Om2 a j).le))).1

/-- **`G^a = sup_j L^a_j`** (for `Ω₂² ∣ a`). -/
theorem ytLg_sup (hdvd : Om (1 + 1) * Om (1 + 1) ∣ a) {x : Ordinal.{0}} (hx : x < ytG S a) :
    ∃ j, x < ytLg S a j := by
  have hκ0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hbdd : BddAbove (Set.range (ytLg S a)) := Ordinal.bddAbove_of_small
  have hlt : ∀ y, y < ⨆ j, ytLg S a j ↔ ∃ j, y < ytLg S a j := fun y => lt_ciSup_iff hbdd
  have hKQ : ∀ j, ytLg S a j < ⨆ j, ytLg S a j := fun j => (hlt _).2 ⟨j + 1, ytLg_lt_succ hown j⟩
  have hΩQ : Om (1 : Ordinal.{0}) < ⨆ j, ytLg S a j := hKQ 0
  have hQSC : SC (⨆ j, ytLg S a j) := by
    refine ⟨(Om_pos one_ne_zero).trans hΩQ, fun x hx y hy => ?_⟩
    obtain ⟨i, hi⟩ := (hlt _).1 hx
    obtain ⟨k, hk⟩ := (hlt _).1 hy
    have hi' := hi.trans_le (ytLg_mono hown (le_max_left i k))
    have hk' := hk.trans_le (ytLg_mono hown (le_max_right i k))
    exact ((ytLg_SC a (max i k)).2 _ hi' _ hk').trans (hKQ _)
  obtain ⟨r, hr⟩ := hdvd
  have hFQ : ytG S a ≤ ⨆ j, ytLg S a j := by
    refine ldPsi2_le2 hQSC hΩQ fun e he hq _ => ?_
    rcases lt_or_ge e a with hea | hea
    · have h1 : S.psi e (Om (1 + 1)) ≤ ytLg S a 1 :=
        (psi_mono (S := S) (InR_Om_succ 1) (hea.le.trans le_self_add)).1
      exact h1.trans_lt (hKQ 1)
    obtain ⟨e', rfl⟩ := exists_add_of_le hea
    have he' : e' < Om (1 + 1) * Om (1 + 1) := (add_lt_add_iff_left a).1 he
    have hq2 : e' / Om (1 + 1) < Om (1 + 1) := (Ordinal.lt_mul_iff_div_lt hκ0).1 he'
    have hdig : (a + e') / Om (1 + 1) % Om (1 + 1) = e' / Om (1 + 1) := by
      rw [hr, mul_assoc, Ordinal.mul_add_div _ hκ0, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hq2]
    rw [hdig] at hq
    obtain ⟨j, hj⟩ := (hlt _).1 hq
    have he'' : e' < Om (1 + 1) * ytLg S a j := by
      calc e' < Om (1 + 1) * (e' / Om (1 + 1) + 1) := by
            rw [mul_add_one]
            conv_lhs => rw [← Ordinal.div_add_mod e' (Om (1 + 1))]
            exact (add_lt_add_iff_left _).2 (Ordinal.mod_lt e' hκ0)
        _ ≤ Om (1 + 1) * ytLg S a j := ldOm2_mul_mono (Order.add_one_le_of_lt hj)
    have := hKQ (j + 1)
    exact ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left a).2 he''.le)).1).trans_lt this
  exact (hlt x).1 (hx.trans_le hFQ)

/-- `ψ_{Ω₂}(a + Ω₂·γ) ≥ G^a` for `γ ≥ G^a`. -/
theorem ytG_ge (hdvd : Om (1 + 1) * Om (1 + 1) ∣ a) {γ : Ordinal.{0}} (hγ : ytG S a ≤ γ) :
    ytG S a ≤ S.psi (a + Om (1 + 1) * γ) (Om (1 + 1)) := by
  by_contra h
  push Not at h
  obtain ⟨j, hj⟩ := ytLg_sup hown hdvd h
  have h1 : ytLg S a (j + 1) ≤ S.psi (a + Om (1 + 1) * γ) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left a).2
      (ldOm2_mul_mono ((ytLg_le_G j).trans hγ)))).1
  exact absurd (hj.trans_le ((ytLg_lt_succ hown j).le.trans h1)) (lt_irrefl _)

/-- **`γ < ψ_{Ω₂}(a + Ω₂·γ)` for every `γ < G^a`.** -/
theorem ytG_gt (hdvd : Om (1 + 1) * Om (1 + 1) ∣ a) {γ : Ordinal.{0}} (hγ : γ < ytG S a) :
    γ < S.psi (a + Om (1 + 1) * γ) (Om (1 + 1)) := by
  obtain ⟨j, hj⟩ := ytLg_sup hown hdvd hγ
  exact ytLg_gt j γ hj

/-- **`a + Ω₂·γ` is own** for every `γ < G^a`. -/
theorem ytBase_own (hdvd : Om (1 + 1) * Om (1 + 1) ∣ a) {γ : Ordinal.{0}} (hγ : γ < ytG S a) :
    ∀ d, d ≤ Om (1 + 1) → a + Om (1 + 1) * γ ∈
      S.CSet (a + Om (1 + 1) * γ + d) (S.psi (a + Om (1 + 1) * γ + d) (Om (1 + 1))) := by
  intro d _
  have h1 : a ∈ S.CSet (a + Om (1 + 1) * γ + d) (S.psi (a + Om (1 + 1) * γ + d) (Om (1 + 1))) := by
    rw [add_assoc]; exact ytOwnAll hown _
  refine CSet.add_mem h1 (ldMulK_small ldOm2_SC (mxOm2_mem _ _) γ ?_)
  exact (ytG_gt hown hdvd hγ).trans_le (psi_mono (S := S) (InR_Om_succ 1) le_self_add).1

/-- `ψ_{Ω₂}(a) < ψ_{Ω₂}(a + x)` for `x ≠ 0`. -/
theorem ytBase_lt {x : Ordinal.{0}} (hx : x ≠ 0) : S.psi a (Om (1 + 1)) < S.psi (a + x) (Om (1 + 1)) :=
  psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right a (pos_iff_ne_zero.2 hx)) (ytOwnAll hown x)

end Lay

/-! ## The atoms below `ψ_{Ω₂}(a + Ω₂·γ)` -/

section Atoms

variable {l ηx a : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hown : ∀ d, d ≤ Om (1 + 1) → a ∈ S.CSet (a + d) (S.psi (a + d) (Om (1 + 1))))
  (hdvd : Om (1 + 1) * Om (1 + 1) ∣ a)

include hl hX hown hdvd

/-- **Every atom of `H_λ` below `ψ_{Ω₂}(a + Ω₂·γ)` (`γ ≤ G^a`) is `≤ ψ_{Ω₂}(a)` or in the block of a code
`γ'' < γ`.** -/
theorem ytCls {γ t : Ordinal.{0}} (hγG : γ ≤ ytG S a) (ht : t ∈ ldAtR S l)
    (htγ : t < S.psi (a + Om (1 + 1) * γ) (Om (1 + 1))) :
    t ≤ S.psi a (Om (1 + 1)) ∨ ∃ γ'', GxCl (upsilon l) (ldAtR S l) γ'' ∧ γ'' < γ ∧
      ((∃ c, GxCl (upsilon l) (ldAtR S l) c ∧ c < ldTop S (a + Om (1 + 1) * γ'') ∧
        t = S.psi (a + Om (1 + 1) * γ'' + c) (Om (1 + 1))) ∨ t = ldTop S (a + Om (1 + 1) * γ'')) := by
  have hκ0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  obtain ⟨x, hx, -, rfl⟩ := ht
  rcases lt_or_ge x a with hxa | hxa
  · exact Or.inl (psi_mono (S := S) (InR_Om_succ 1) hxa.le).1
  right
  obtain ⟨y, rfl⟩ := exists_add_of_le hxa
  have hyγ : y < Om (1 + 1) * γ := by
    by_contra h
    push Not at h
    exact absurd htγ (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left a).2 h)).1)
  have hγ'' : y / Om (1 + 1) < γ := (Ordinal.lt_mul_iff_div_lt hκ0).1 hyγ
  have hγ''G : y / Om (1 + 1) < ytG S a := hγ''.trans_le hγG
  have hγ''2 : y / Om (1 + 1) < Om (1 + 1) := hγ''G.trans (ytG_lt_Om2 a)
  obtain ⟨r, hr⟩ := hdvd
  have hdiv : (a + y) / Om (1 + 1) % Om (1 + 1) = y / Om (1 + 1) := by
    rw [hr, mul_assoc, Ordinal.mul_add_div _ hκ0, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hγ''2]
  have hmod : (a + y) % Om (1 + 1) = y % Om (1 + 1) := by
    rw [hr, mul_assoc, Ordinal.mul_add_mod_self]
  have hγ''H : y / Om (1 + 1) ∈ cdHull S l := by
    have := ldModK_mem (S := S) ldOm2_SC (ldDivK_mem (S := S) ldOm2_SC hx)
    rwa [hdiv] at this
  have hcH : y % Om (1 + 1) ∈ cdHull S l := by
    have := ldModK_mem (S := S) ldOm2_SC hx
    rwa [hmod] at this
  have hc2 : y % Om (1 + 1) < Om (1 + 1) := Ordinal.mod_lt y hκ0
  have hdec : a + y = a + Om (1 + 1) * (y / Om (1 + 1)) + y % Om (1 + 1) := by
    rw [add_assoc, Ordinal.div_add_mod]
  refine ⟨y / Om (1 + 1), (ldHull_iff hl hX hγ''2).1 hγ''H, hγ'', ?_⟩
  have hown'' := ytBase_own hown ⟨r, hr⟩ hγ''G
  rcases lt_or_ge (y % Om (1 + 1)) (ldTop S (a + Om (1 + 1) * (y / Om (1 + 1)))) with hcF | hcF
  · exact Or.inl ⟨_, (ldHull_iff hl hX hc2).1 hcH, hcF, by rw [← hdec]⟩
  · refine Or.inr (le_antisymm ?_ ?_)
    · rw [hdec]
      exact (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left _).2 hc2.le)).1
    · rw [hdec]
      exact ldTop_ge hown'' (dvd_add ⟨Om (1 + 1) * r, by rw [hr, mul_assoc]⟩ (dvd_mul_right _ _)) hcF

omit hl hX hown in
theorem ytDvd1 : Om (1 + 1) ∣ a := by
  obtain ⟨r, hr⟩ := hdvd; exact ⟨Om (1 + 1) * r, by rw [hr, mul_assoc]⟩

omit hl hX hown in
theorem ytDvdG (γ : Ordinal.{0}) : Om (1 + 1) ∣ a + Om (1 + 1) * γ :=
  dvd_add (ytDvd1 hdvd) (dvd_mul_right _ _)

/-- **Every atom of `H_λ` in `(ψ_{Ω₂}(a), G^a)` is `ψ_{Ω₂}(a + Ω₂·γ + c)`** with codes `γ < G^a`,
`c < F^{a+Ω₂·γ}`. -/
theorem ytClsAll {t : Ordinal.{0}} (ht : t ∈ ldAtR S l) (htG : t < ytG S a) :
    t ≤ S.psi a (Om (1 + 1)) ∨ ∃ γ, GxCl (upsilon l) (ldAtR S l) γ ∧ γ < ytG S a ∧
      ∃ c, GxCl (upsilon l) (ldAtR S l) c ∧ c < ldTop S (a + Om (1 + 1) * γ) ∧
        t = S.psi (a + Om (1 + 1) * γ + c) (Om (1 + 1)) := by
  have hGG : t < S.psi (a + Om (1 + 1) * ytG S a) (Om (1 + 1)) := htG.trans_le (ytG_ge hown hdvd le_rfl)
  rcases ytCls hl hX hown hdvd le_rfl ht hGG with hle | ⟨γ'', hγ''c, hγ''G, hcase⟩
  · exact Or.inl hle
  right
  rcases hcase with ⟨c, hc, hcF, rfl⟩ | rfl
  · exact ⟨γ'', hγ''c, hγ''G, c, hc, hcF, rfl⟩
  · have hγ1G : γ'' + 1 < ytG S a := (ytG_SC a).isSuccLimit.succ_lt hγ''G
    have hγ12 : γ'' + 1 < Om (1 + 1) := hγ1G.trans (ytG_lt_Om2 a)
    refine ⟨γ'' + 1, (ldHull_iff hl hX hγ12).1 (CSet.succ_mem ((ldHull_iff hl hX
      ((lt_add_one _).trans hγ12)).2 hγ''c)), hγ1G, 0, GxCl.zero (mvUps_pos hl),
      (Om_pos one_ne_zero).trans (ldOm1_lt_Top _), ?_⟩
    unfold ldTop; rw [add_zero, mul_add_one, add_assoc]

/-- **Finite support at a limit `γ`**: a code below `ψ_{Ω₂}(a + Ω₂·γ)` is below `F^{a+Ω₂·γ*}` for a code
`γ* < γ` above any given code `γ' < γ`. -/
theorem ytSupp {γ : Ordinal.{0}} (hγG : γ ≤ ytG S a) (hlim : IsSuccLimit γ) :
    ∀ c, GxCl (upsilon l) (ldAtR S l) c → c < S.psi (a + Om (1 + 1) * γ) (Om (1 + 1)) →
      ∀ γ', GxCl (upsilon l) (ldAtR S l) γ' → γ' < γ → ∃ γs, GxCl (upsilon l) (ldAtR S l) γs ∧
        γ' ≤ γs ∧ γs < γ ∧ c < ldTop S (a + Om (1 + 1) * γs) := by
  intro c hc
  induction hc with
  | @small x h =>
    intro _ γ' hγ' hγ'γ
    have hρ1 : upsilon l < Om 1 := by
      have hpv := cdEta_pv (S := S) hl.1 hX
      rw [← hpv]; exact psi_lt Low.InR_Om_one _
    exact ⟨γ', hγ', le_rfl, hγ'γ, ((h.trans hρ1).trans (ldOm1_lt_Top _))⟩
  | om => exact fun _ γ' hγ' hγ'γ => ⟨γ', hγ', le_rfl, hγ'γ, ldOm1_lt_Top _⟩
  | @atom s hs =>
    intro hsγ γ' hγ' hγ'γ
    rcases ytCls hl hX hown hdvd hγG hs hsγ with hle | ⟨γ'', hγ''c, hγ''γ, hcase⟩
    · refine ⟨γ', hγ', le_rfl, hγ'γ, hle.trans_lt ?_⟩
      exact (ytBase_lt hown ldOm2_SC.1.ne').trans_le (ldTop_mono le_self_add)
    have hsle : s ≤ ldTop S (a + Om (1 + 1) * γ'') := by
      rcases hcase with ⟨c, -, hcF, rfl⟩ | rfl
      · exact (ldTop_lt (ytBase_own hown hdvd (hγ''γ.trans_le hγG)) hcF).le
      · exact le_rfl
    have hγ1 : γ'' + 1 < γ := hlim.succ_lt hγ''γ
    have hγ1G : γ'' + 1 < ytG S a := hγ1.trans_le hγG
    have hγ1c : GxCl (upsilon l) (ldAtR S l) (γ'' + 1) := by
      have h2 : γ'' + 1 < Om (1 + 1) := hγ1G.trans (ytG_lt_Om2 a)
      exact (ldHull_iff hl hX h2).1 (CSet.succ_mem ((ldHull_iff hl hX ((lt_add_one _).trans h2)).2 hγ''c))
    have hs1 : s < ldTop S (a + Om (1 + 1) * (γ'' + 1)) := by
      refine hsle.trans_lt ?_
      have e : ldTop S (a + Om (1 + 1) * γ'') = S.psi (a + Om (1 + 1) * (γ'' + 1)) (Om (1 + 1)) := by
        unfold ldTop; rw [mul_add_one, add_assoc]
      rw [e]
      exact ldBase_lt_top (ytBase_own hown hdvd hγ1G)
    rcases le_total γ' (γ'' + 1) with h | h
    · exact ⟨γ'' + 1, hγ1c, h, hγ1, hs1⟩
    · exact ⟨γ', hγ', le_rfl, hγ'γ, hs1.trans_le (ldTop_mono ((add_le_add_iff_left a).2 (ldOm2_mul_mono h)))⟩
  | @add x y _ _ ihx ihy =>
    intro hxy γ' hγ' hγ'γ
    obtain ⟨γ1, hγ1, h1, h1γ, hx1⟩ := ihx (lt_of_le_of_lt le_self_add hxy) γ' hγ' hγ'γ
    obtain ⟨γ2, hγ2, h2, h2γ, hy2⟩ := ihy (lt_of_le_of_lt le_add_self hxy) γ1 hγ1 h1γ
    exact ⟨γ2, hγ2, h1.trans h2, h2γ, (ldTop_SC _).isPrincipal
      (hx1.trans_le (ldTop_mono ((add_le_add_iff_left a).2 (ldOm2_mul_mono h2)))) hy2⟩
  | @phi x y _ _ ihx ihy =>
    intro hxy γ' hγ' hγ'γ
    obtain ⟨γ1, hγ1, h1, h1γ, hx1⟩ := ihx (lt_of_le_of_lt (left_le_veblen x y) hxy) γ' hγ' hγ'γ
    obtain ⟨γ2, hγ2, h2, h2γ, hy2⟩ := ihy (lt_of_le_of_lt (right_le_veblen x y) hxy) γ1 hγ1 h1γ
    exact ⟨γ2, hγ2, h1.trans h2, h2γ, (ldTop_SC _).2 _
      (hx1.trans_le (ldTop_mono ((add_le_add_iff_left a).2 (ldOm2_mul_mono h2)))) _ hy2⟩

end Atoms

/-! ## The reading law of the bases `a + Ω₂·γ` -/

theorem ytHat_own {Â x : Ordinal.{0}} (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hx : x < S.psi (Â + Om 1 * x) (Om 1)) :
    Â + Om 1 * x ∈ S.CSet (Â + Om 1 * x) (S.psi (Â + Om 1 * x) (Om 1)) :=
  CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ)
    (ldMulK_small Ph.ph_SC_Om1 (CSet.Om_mem (CSet.one_mem _ _)) x hx)

theorem ytA_lt {l a : Ordinal.{0}} (haA : a + Om (1 + 1) * Om (1 + 1) < ConjT.Aη S (cdEta S l))
    {γ : Ordinal.{0}} (hγ : γ < Om (1 + 1)) :
    a + Om (1 + 1) * γ + Om (1 + 1) < ConjT.Aη S (cdEta S l) := by
  rw [add_assoc, ← mul_add_one]
  exact lt_of_le_of_lt ((add_le_add_iff_left a).2 (ldOm2_mul_mono (Order.add_one_le_of_lt hγ))) haA

section Law

variable {l ηx a Â : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hown : ∀ d, d ≤ Om (1 + 1) → a ∈ S.CSet (a + d) (S.psi (a + d) (Om (1 + 1))))
  (hdvd : Om (1 + 1) * Om (1 + 1) ∣ a) (haH : a ∈ cdHull S l)
  (haA : a + Om (1 + 1) * Om (1 + 1) < ConjT.Aη S (cdEta S l))
  (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
  (hbase : gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) = S.psi Â (Om 1))

include hl hX hown hdvd haH haA hÂ hbase

/-- **`Θ(ψ_{Ω₂}(a + Ω₂·γ)) = ψ_{Ω₁}(Â + Ω₁·Θγ)`** for every code `γ < G^a`. -/
theorem ytLaw : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ < ytG S a →
    gxTh (upsilon l) (ldAtR S l) (S.psi (a + Om (1 + 1) * γ) (Om (1 + 1))) =
      S.psi (Â + Om 1 * gxTh (upsilon l) (ldAtR S l) γ) (Om 1) := by
  have hpv := cdEta_pv (S := S) hl.1 hX
  have hρSC : SC (upsilon l) := hpv ▸ SC_psi Low.InR_Om_one _
  have hρ1 : upsilon l < Om 1 := hpv ▸ psi_lt Low.InR_Om_one _
  have hρ0 : 0 < upsilon l := hρSC.1
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΩ1C : ∀ a b, Om (1 : Ordinal.{0}) ∈ S.CSet a b := fun a b => CSet.Om_mem (CSet.one_mem a b)
  have hκ0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hA0 : a + Om (1 + 1) < ConjT.Aη S (cdEta S l) := by
    have := ytA_lt (S := S) haA (γ := 0) ldOm2_SC.1
    rwa [mul_zero, add_zero] at this
  have hbat : S.psi a (Om (1 + 1)) ∈ ldAtR S l := ldBlk_base_atom haH hA0
  have hρÂ : upsilon l < S.psi Â (Om 1) := by
    rw [← hbase]; exact (ldAtom_ge hρSC hρ1 hAt hbat).2.1
  have hβH : ∀ γ', γ' ∈ cdHull S l → a + Om (1 + 1) * γ' ∈ cdHull S l :=
    fun γ' h => CSet.add_mem haH (ldG2_H h)
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγ hγG
  have hγ2 : γ < Om (1 + 1) := hγG.trans (ytG_lt_Om2 a)
  have hγH : γ ∈ cdHull S l := (ldHull_iff hl hX hγ2).2 hγ
  have hown' : ∀ γ', GxCl (upsilon l) (ldAtR S l) γ' → γ' < γ →
      Â + Om 1 * gxTh (upsilon l) (ldAtR S l) γ' ∈ S.CSet (Â + Om 1 * gxTh (upsilon l) (ldAtR S l) γ')
        (S.psi (Â + Om 1 * gxTh (upsilon l) (ldAtR S l) γ') (Om 1)) := by
    intro γ' hγ' hγ'γ
    refine ytHat_own hÂ ?_
    rw [← IH γ' hγ'γ hγ' (hγ'γ.trans hγG)]
    exact gxTh_lt hγ' (ytG_gt hown hdvd (hγ'γ.trans hγG))
  have hblk : ∀ γ', GxCl (upsilon l) (ldAtR S l) γ' → γ' < γ →
      ∀ c, GxCl (upsilon l) (ldAtR S l) c → c < ldTop S (a + Om (1 + 1) * γ') →
        gxTh (upsilon l) (ldAtR S l) (S.psi (a + Om (1 + 1) * γ' + c) (Om (1 + 1))) =
          S.psi (Â + Om 1 * gxTh (upsilon l) (ldAtR S l) γ' + gxTh (upsilon l) (ldAtR S l) c) (Om 1) := by
    intro γ' hγ' hγ'γ
    have hγ'G := hγ'γ.trans hγG
    have hγ'H : γ' ∈ cdHull S l := (ldHull_iff hl hX (hγ'G.trans (ytG_lt_Om2 a))).2 hγ'
    exact ldBlk_step hl hX (ytBase_own hown hdvd hγ'G) (ytDvdG hdvd γ') (hβH γ' hγ'H)
      (ytA_lt haA (hγ'G.trans (ytG_lt_Om2 a))) (hown' γ' hγ' hγ'γ) (IH γ' hγ'γ hγ' hγ'G)
  rcases zero_or_succ_or_isSuccLimit γ with h0 | ⟨γ', hγ'⟩ | hlim
  · subst h0
    rw [mul_zero, add_zero, gxTh_zero, mul_zero, add_zero]
    exact hbase
  · rw [succ_eq_add_one] at hγ'
    subst hγ'
    have hγ'γ : γ' < γ' + 1 := lt_add_one γ'
    have hγ'G := hγ'γ.trans hγG
    have hγ'2 := hγ'G.trans (ytG_lt_Om2 a)
    have hγ'H : γ' ∈ cdHull S l := mem_of_add_one_mem hγH
    have hγ'c : GxCl (upsilon l) (ldAtR S l) γ' := (ldHull_iff hl hX hγ'2).1 hγ'H
    have h := ldBlk_next hl hX (ytBase_own hown hdvd hγ'G) (ytDvdG hdvd γ') (hβH γ' hγ'H)
      (ytA_lt haA hγ'2) (hown' γ' hγ'c hγ'γ) (IH γ' hγ'γ hγ'c hγ'G)
    have e : ldTop S (a + Om (1 + 1) * γ') = S.psi (a + Om (1 + 1) * (γ' + 1)) (Om (1 + 1)) := by
      unfold ldTop; rw [mul_add_one, add_assoc]
    rw [e] at h
    rw [h, gxTh_add hρSC hAt hγ'c, gxTh_small (gg_one_lt_of_SC hρSC).le, mul_add_one, add_assoc]
  · have hγ0 : γ ≠ 0 := hlim.ne_bot
    have hΘ0 : 0 < gxTh (upsilon l) (ldAtR S l) γ := by
      have := gxTh_lt (Z := upsilon l) (At := ldAtR S l) (GxCl.zero hρ0) (pos_iff_ne_zero.2 hγ0)
      rwa [gxTh_zero] at this
    have hsat : S.psi (a + Om (1 + 1) * γ) (Om (1 + 1)) ∈ ldAtR S l :=
      ldBlk_base_atom (hβH γ hγH) (ytA_lt haA hγ2)
    set Θγ := gxTh (upsilon l) (ldAtR S l) γ with hΘγ
    have hÂX : Â ∈ S.CSet (Â + Om 1 * Θγ) (S.psi (Â + Om 1 * Θγ) (Om 1)) :=
      (psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ
    have hÂlt : S.psi Â (Om 1) < S.psi (Â + Om 1 * Θγ) (Om 1) :=
      psi_lt_psi_of_mem Low.InR_Om_one (lt_add_of_pos_right Â (mul_pos (Om_pos one_ne_zero) hΘ0)) hÂX
    have hρX : upsilon l < S.psi (Â + Om 1 * Θγ) (Om 1) := hρÂ.trans hÂlt
    apply le_antisymm
    · refine ldAtom_le hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) hρX ?_
      intro t ht htγ
      rcases ytCls hl hX hown hdvd hγG.le ht htγ with hle | ⟨γ'', hγ''c, hγ''γ, hcase⟩
      · exact (gxTh_mono hle).trans_lt (by rw [hbase]; exact hÂlt)
      obtain ⟨γ1, hγ1c, hγ1γ, c, hc, hcF, rfl⟩ : ∃ γ1, GxCl (upsilon l) (ldAtR S l) γ1 ∧ γ1 < γ ∧
          ∃ c, GxCl (upsilon l) (ldAtR S l) c ∧ c < ldTop S (a + Om (1 + 1) * γ1) ∧
            t = S.psi (a + Om (1 + 1) * γ1 + c) (Om (1 + 1)) := by
        rcases hcase with ⟨c, hc, hcF, rfl⟩ | rfl
        · exact ⟨γ'', hγ''c, hγ''γ, c, hc, hcF, rfl⟩
        · have hγ1 : γ'' + 1 < γ := hlim.succ_lt hγ''γ
          have hγ12 : γ'' + 1 < Om (1 + 1) := (hγ1.trans hγG).trans (ytG_lt_Om2 a)
          have hγ1c : GxCl (upsilon l) (ldAtR S l) (γ'' + 1) :=
            (ldHull_iff hl hX hγ12).1 (CSet.succ_mem ((ldHull_iff hl hX ((lt_add_one _).trans hγ12)).2 hγ''c))
          refine ⟨γ'' + 1, hγ1c, hγ1, 0, GxCl.zero hρ0, (Om_pos one_ne_zero).trans (ldOm1_lt_Top _), ?_⟩
          unfold ldTop; rw [add_zero, mul_add_one, add_assoc]
      have hγ1G := hγ1γ.trans hγG
      rw [hblk γ1 hγ1c hγ1γ c hc hcF]
      have hcs : gxTh (upsilon l) (ldAtR S l) c <
          S.psi (Â + Om 1 * gxTh (upsilon l) (ldAtR S l) γ1 + gxTh (upsilon l) (ldAtR S l) c) (Om 1) := by
        rw [← hblk γ1 hγ1c hγ1γ c hc hcF]
        exact gxTh_lt hc (ldTop_gt (ytBase_own hown hdvd hγ1G) (ytDvdG hdvd γ1) hcF)
      have hc1 := hcs.trans (psi_lt Low.InR_Om_one _)
      have hΘ1 : gxTh (upsilon l) (ldAtR S l) γ1 < Θγ := gxTh_lt hγ1c hγ1γ
      have harg : Â + Om 1 * gxTh (upsilon l) (ldAtR S l) γ1 + gxTh (upsilon l) (ldAtR S l) c <
          Â + Om 1 * Θγ := by
        rw [add_assoc Â]
        refine (add_lt_add_iff_left Â).2 ?_
        calc Om 1 * gxTh (upsilon l) (ldAtR S l) γ1 + gxTh (upsilon l) (ldAtR S l) c
            < Om 1 * gxTh (upsilon l) (ldAtR S l) γ1 + Om 1 := (add_lt_add_iff_left _).2 hc1
          _ = Om 1 * (gxTh (upsilon l) (ldAtR S l) γ1 + 1) := (mul_add_one _ _).symm
          _ ≤ Om 1 * Θγ := mul_le_mul_right (Order.add_one_le_of_lt hΘ1) _
      have hγ1X : gxTh (upsilon l) (ldAtR S l) γ1 < S.psi (Â + Om 1 * Θγ) (Om 1) := by
        have h1 := gxTh_lt hγ1c (ytG_gt hown hdvd hγ1G)
        rw [IH γ1 hγ1γ hγ1c hγ1G] at h1
        refine h1.trans_le (psi_mono (S := S) Low.InR_Om_one ?_).1
        exact (add_le_add_iff_left Â).2 (mul_le_mul_right hΘ1.le _)
      refine psi_lt_psi_of_mem Low.InR_Om_one harg (CSet.add_mem (CSet.add_mem hÂX
        (ldMulK_small Ph.ph_SC_Om1 (hΩ1C _ _) _ hγ1X)) (CSet.of_lt ?_))
      exact hcs.trans_le (psi_mono (S := S) Low.InR_Om_one harg.le).1
    · obtain ⟨hTSC, -, hTs⟩ := ldAtom_ge hρSC hρ1 hAt hsat
      refine ldPsi1_le hTSC fun e he hmod => ?_
      rcases le_or_gt e Â with heÂ | heÂ
      · refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one heÂ).1 ?_
        rw [← hbase]; exact hTs _ hbat (ytBase_lt hown (mul_ne_zero hκ0 hγ0))
      obtain ⟨r', rfl⟩ := exists_add_of_le heÂ.le
      have hr'lt : r' < Om 1 * Θγ := (add_lt_add_iff_left Â).1 he
      have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
      have hx : r' / Om 1 < Θγ := (Ordinal.lt_mul_iff_div_lt hΩ0).1 hr'lt
      have hdec : r' = Om 1 * (r' / Om 1) + r' % Om 1 := (Ordinal.div_add_mod r' _).symm
      have hy : r' % Om 1 < gxTh (upsilon l) (ldAtR S l) (S.psi (a + Om (1 + 1) * γ) (Om (1 + 1))) := by
        rcases lt_or_ge r' (Om 1) with h1 | h1
        · rw [ldMod_add_lt Â h1] at hmod
          rw [Ordinal.mod_eq_of_lt h1]; exact le_add_self.trans_lt hmod
        · rw [ldMod_add_ge Â h1] at hmod; exact hmod
      obtain ⟨γ', hγ'c, hγ'γ, hγ'x⟩ := gxTh_onto hx
      obtain ⟨c, hc, hcγ, hcy⟩ := gxTh_onto hy
      obtain ⟨γs, hγs, hγ'γs, hγsγ, hcF⟩ := ytSupp hl hX hown hdvd hγG.le hlim c hc hcγ γ' hγ'c hγ'γ
      have hγsG := hγsγ.trans hγG
      have hγsH : γs ∈ cdHull S l := (ldHull_iff hl hX (hγsG.trans (ytG_lt_Om2 a))).2 hγs
      have htat := ldBlk_atom hl hX (hβH γs hγsH) (ytA_lt haA (hγsG.trans (ytG_lt_Om2 a))) hc hcF
      have htγ : S.psi (a + Om (1 + 1) * γs + c) (Om (1 + 1)) < S.psi (a + Om (1 + 1) * γ) (Om (1 + 1)) := by
        refine (ldTop_lt (ytBase_own hown hdvd hγsG) hcF).trans_le ?_
        have e : ldTop S (a + Om (1 + 1) * γs) = S.psi (a + Om (1 + 1) * (γs + 1)) (Om (1 + 1)) := by
          unfold ldTop; rw [mul_add_one, add_assoc]
        rw [e]
        exact (psi_mono (S := S) (InR_Om_succ 1)
          ((add_le_add_iff_left a).2 (ldOm2_mul_mono (Order.add_one_le_of_lt hγsγ)))).1
      have h1 := hTs _ htat htγ
      rw [hblk γs hγs hγsγ c hc hcF, hcy] at h1
      refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one ?_).1 h1
      rw [add_assoc Â]
      refine (add_le_add_iff_left Â).2 ?_
      conv_lhs => rw [hdec]
      refine add_le_add (mul_le_mul_right ?_ _) le_rfl
      rw [← hγ'x]
      exact gxTh_mono hγ'γs

/-- **`Θ(ψ_{Ω₂}(a + Ω₂·γ + c)) = ψ_{Ω₁}(Â + Ω₁·Θγ + Θc)`** for codes `γ < G^a`, `c < F^{a+Ω₂·γ}`. -/
theorem ytLawTh {γ c : Ordinal.{0}} (hγ : GxCl (upsilon l) (ldAtR S l) γ) (hγG : γ < ytG S a)
    (hc : GxCl (upsilon l) (ldAtR S l) c) (hcF : c < ldTop S (a + Om (1 + 1) * γ)) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (a + Om (1 + 1) * γ + c) (Om (1 + 1))) =
      S.psi (Â + Om 1 * gxTh (upsilon l) (ldAtR S l) γ + gxTh (upsilon l) (ldAtR S l) c) (Om 1) := by
  have hlaw := ytLaw hl hX hown hdvd haH haA hÂ hbase γ hγ hγG
  have hγ2 := hγG.trans (ytG_lt_Om2 a)
  have hγH : γ ∈ cdHull S l := (ldHull_iff hl hX hγ2).2 hγ
  have hownγ := ytHat_own hÂ (x := gxTh (upsilon l) (ldAtR S l) γ) (by
    rw [← hlaw]; exact gxTh_lt hγ (ytG_gt hown hdvd hγG))
  exact ldBlk_step hl hX (ytBase_own hown hdvd hγG) (ytDvdG hdvd γ) (CSet.add_mem haH (ldG2_H hγH))
    (ytA_lt haA hγ2) hownγ hlaw c hc hcF

end Law

end Googology.Trans.PoR.InaccPsi.R2.Yt
