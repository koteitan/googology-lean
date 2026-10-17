import Googology.Trans.PoR.InaccPsi.R2.EpsK
import Googology.Trans.PoR.InaccPsi.R2.BlkGen

/-!
# Terms below `ε_{x+ω}`: Lemma EXACT, the uniform comparison, the representation, Lemma RS

The terms `TW`: a constant (`cst a`), the `ε`-number `ε_{x+n}` (`ep n`; `ep 0` is `x`), a sum (`sm`), and
`ω^t` (`pw t`).  For an `ε`-number `x` above the constants the value is below `ε_{x+lv+1}` (`lv` the
largest index of an `ep`), and every ordinal below `ε_{ρ+ω}` is a value at `ρ` (`repW`).

* `TW`, `TW.val`, `TW.CBw`, `TW.csw`, `TW.lv`, `TW.noE`; `val_lt_eK` (`t(x) < ε_{x+lv(t)+1}`),
  `val_noE` (a term without `ep` is constant), `le_val_of_not_noE`;
* `pi_val` (**Lemma EXACT for `TW`**: for `υ`-points `σ < ρ` and constants below `σ`, `t(ρ) ∈ Tᵖ[σ]` and
  `π_{σ,ρ}(t(ρ)) = t(σ)`; `pi_eK`, `pi_add`, `pi_opowK`), `uniW_le`, `uniW_lt`, `uniW_eq` (**the uniform
  comparison**: two terms compare at `ρ` as at `σ`);
* `repW` (**representation**: every ordinal below `ε_{ρ+N+1}` is `t(ρ)` with constants below `ρ`);
* `rs_rstW` (**Lemma RS with the target `t(ρ) ≥ ρ`**, from `rs_rstF`), `rsStep_W` (Lemma RS for every
  term, `rs_rstT` for a constant term).

No new axiom.

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-- Terms below `ε_{x+ω}`: a constant, `ε_{x+n}`, a sum, or `ω^t`. -/
inductive TW : Type 1
  | cst : Ordinal.{0} → TW
  | ep : ℕ → TW
  | sm : TW → TW → TW
  | pw : TW → TW

namespace TW

/-- The value of a term at `x`. -/
noncomputable def val : TW → Ordinal.{0} → Ordinal.{0}
  | cst a, _ => a
  | ep n, x => eK n x
  | sm a b, x => val a x + val b x
  | pw t, x => ω ^ val t x

/-- All constants below `s`. -/
def CBw : TW → Ordinal.{0} → Prop
  | cst a, s => a < s
  | ep _, _ => True
  | sm a b, s => CBw a s ∧ CBw b s
  | pw t, s => CBw t s

/-- The constants. -/
def csw : TW → List Ordinal.{0}
  | cst a => [a]
  | ep _ => []
  | sm a b => csw a ++ csw b
  | pw t => csw t

/-- The largest index of an `ep`. -/
def lv : TW → ℕ
  | cst _ => 0
  | ep n => n
  | sm a b => max (lv a) (lv b)
  | pw t => lv t

/-- No `ep` occurs. -/
def noE : TW → Prop
  | cst _ => True
  | ep _ => False
  | sm a b => noE a ∧ noE b
  | pw t => noE t

@[simp] theorem val_cst (a x : Ordinal.{0}) : val (cst a) x = a := rfl
@[simp] theorem val_ep (n : ℕ) (x : Ordinal.{0}) : val (ep n) x = eK n x := rfl
@[simp] theorem val_sm (a b : TW) (x : Ordinal.{0}) : val (sm a b) x = val a x + val b x := rfl
@[simp] theorem val_pw (t : TW) (x : Ordinal.{0}) : val (pw t) x = ω ^ val t x := rfl

theorem cbw_iff : ∀ (t : TW) (s : Ordinal.{0}), CBw t s ↔ ∀ c ∈ csw t, c < s
  | cst a, s => by simp [CBw, csw]
  | ep n, s => by simp [CBw, csw]
  | sm a b, s => by
      simp only [CBw, csw, List.mem_append]
      rw [cbw_iff a s, cbw_iff b s]
      constructor
      · rintro ⟨h1, h2⟩ c (hc | hc)
        · exact h1 c hc
        · exact h2 c hc
      · intro h; exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩
  | pw t, s => cbw_iff t s

theorem CBw_mono {t : TW} {s s' : Ordinal.{0}} (h : CBw t s) (hs : s ≤ s') : CBw t s' :=
  (cbw_iff t s').2 (fun c hc => lt_of_lt_of_le ((cbw_iff t s).1 h c hc) hs)

end TW

open TW

/-! ## Values -/

/-- **`t(x) < ε_{x+lv(t)+1}`** for an `ε`-number `x` above the constants. -/
theorem val_lt_eK {x : Ordinal.{0}} (hx : InE x) : ∀ t : TW, CBw t x → val t x < eK (lv t + 1) x
  | cst a, h => lt_of_lt_of_le h (le_eK _ x)
  | ep n, _ => eK_lt_succ n x
  | sm a b, h => by
    have hE := eK_E_succ (lv (sm a b)) x
    have h1 : val a x < eK (lv (sm a b) + 1) x :=
      lt_of_lt_of_le (val_lt_eK hx a h.1) (eK_le (Nat.succ_le_succ (le_max_left _ _)) x)
    have h2 : val b x < eK (lv (sm a b) + 1) x :=
      lt_of_lt_of_le (val_lt_eK hx b h.2) (eK_le (Nat.succ_le_succ (le_max_right _ _)) x)
    exact (inE_indec hE).add_lt h1 h2
  | pw t, h => by
    have hE := eK_E_succ (lv t) x
    have h1 := (opow_lt_opow_iff_right one_lt_omega0).2 (val_lt_eK hx t h)
    have hE' : ω ^ eK (lv t + 1) x = eK (lv t + 1) x := hE
    rw [hE'] at h1
    exact h1

theorem val_lt_Om1 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {t : TW} (h : CBw t x) :
    val t x < Om1 :=
  (val_lt_eK hx t h).trans (eK_lt_Om1 hx1 _)

/-- A term without `ep` has a constant value. -/
theorem val_noE : ∀ t : TW, noE t → ∀ x y, val t x = val t y
  | cst _, _, _, _ => rfl
  | ep _, h, _, _ => absurd h id
  | sm a b, h, x, y => by simp only [val_sm, val_noE a h.1 x y, val_noE b h.2 x y]
  | pw t, h, x, y => by simp only [val_pw, val_noE t h x y]

/-- A term with an `ep` has value `≥ x`. -/
theorem le_val_of_not_noE {x : Ordinal.{0}} : ∀ t : TW, ¬ noE t → x ≤ val t x
  | cst _, h => absurd trivial h
  | ep n, _ => le_eK n x
  | sm a b, h => by
    simp only [noE, not_and_or] at h
    rcases h with h | h
    · exact (le_val_of_not_noE a h).trans le_self_add
    · exact (le_val_of_not_noE b h).trans le_add_self
  | pw t, h => (le_val_of_not_noE t h).trans (right_le_opow _ one_lt_omega0)

/-! ## Lemma EXACT -/

/-- **Lemma EXACT for `TW`**: for `υ`-points `σ < ρ` (`Bases σ ρ`) and a term with constants below `σ`,
`t(ρ) ∈ Tᵖ[σ]` and `π_{σ,ρ}(t(ρ)) = t(σ)`. -/
theorem pi_val {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) :
    ∀ t : TW, CBw t σ → val t ρ ∈ TB ρ σ ∧ pi σ ρ (val t ρ) = val t σ
  | cst a, h => ⟨mem_TB_of_lt hB h, pi_lt hB h⟩
  | ep n, _ => ⟨eK_TB hB n, pi_eK hσ hρ hB n⟩
  | sm a b, h => by
    obtain ⟨h1, h2⟩ := pi_val hσ hρ hB a h.1
    obtain ⟨h3, h4⟩ := pi_val hσ hρ hB b h.2
    obtain ⟨h5, h6⟩ := pi_add hB h1 h3
    simp only [val_sm]
    exact ⟨h5, by rw [h6, h2, h4]⟩
  | pw t, h => by
    obtain ⟨h1, h2⟩ := pi_val hσ hρ hB t h
    have hb := val_lt_eK hB.2.1 t (CBw_mono h hB.2.2.1.le)
    obtain ⟨h3, h4⟩ := pi_opowK hσ hρ hB h1 (lv t) hb
    simp only [val_pw]
    exact ⟨h3, by rw [h4, h2]⟩

/-- **Uniform comparison** (`≤`) of two terms at `υ`-points `σ < ρ`, constants below `σ`. -/
theorem uniW_le {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : TW}
    (ht : CBw t σ) (hu : CBw u σ) : val t ρ ≤ val u ρ ↔ val t σ ≤ val u σ := by
  obtain ⟨h1, h2⟩ := pi_val hσ hρ hB t ht
  obtain ⟨h3, h4⟩ := pi_val hσ hρ hB u hu
  rw [← h2, ← h4]
  exact ((pi_bijOn hB).2.le_iff_le h1 h3).symm

theorem uniW_lt {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : TW}
    (ht : CBw t σ) (hu : CBw u σ) : val t ρ < val u ρ ↔ val t σ < val u σ := by
  rw [← not_le, ← not_le, uniW_le hσ hρ hB hu ht]

theorem uniW_eq {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : TW}
    (ht : CBw t σ) (hu : CBw u σ) : val t ρ = val u ρ ↔ val t σ = val u σ := by
  rw [le_antisymm_iff, le_antisymm_iff, uniW_le hσ hρ hB ht hu, uniW_le hσ hρ hB hu ht]

/-! ## The representation -/

/-- **Representation**: every ordinal below `ε_{ρ+N+1}` is the value at `ρ` of a term of `TW` with
constants below `ρ`. -/
theorem repW {ρ : Ordinal.{0}} (hρ : InE ρ) (N : ℕ) :
    ∀ v, v < eK (N + 1) ρ → ∃ t : TW, CBw t ρ ∧ val t ρ = v := by
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  rcases lt_or_ge v ρ with hvρ | hρv
  · exact ⟨cst v, hvρ, rfl⟩
  by_cases hI : Indec v
  · by_cases hE : InE v
    · obtain ⟨m, -, hm1, hm2⟩ := eK_bracket N hρv hv
      exact ⟨ep m, trivial, (eK_eq_of_inE hm1 hm2 hE).symm⟩
    · obtain ⟨L, rfl⟩ := indec_eq_opow hI
      have hL : L < ω ^ L := lt_of_le_of_ne (right_le_opow _ one_lt_omega0)
        (fun h => hE (by unfold InE; rw [← h]; exact h.symm))
      obtain ⟨t, ht, e⟩ := IH L hL (hL.trans hv)
      exact ⟨pw t, ht, by rw [val_pw, e]⟩
  · have hD : DecompR0 v := not_not.1 hI
    rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
    · exact absurd h0 (lt_of_lt_of_le hρ.pos hρv).ne'
    obtain ⟨s1, h1, e1⟩ := IH u1 hu1 (hu1.trans hv)
    obtain ⟨s2, h2, e2⟩ := IH u2 hu2 (hu2.trans hv)
    exact ⟨sm s1 s2, ⟨h1, h2⟩, by rw [val_sm, e1, e2, hsum]⟩

/-! ## Lemma RS -/

/-- **Lemma RS with the target `t(ρ)`** (`t(ρ) ≥ ρ`, constants below `ρ`): if restarts `ρ_μ` with
`ρ_μ ≤₁ δ_μ + t(ρ_μ)` lie above every `κ' < ρ` (with `δ_μ < ρ`), then `ρ ≤₁ δ + t(ρ) + 1`. -/
theorem rs_rstW {r : Ordinal.{0}} (h : RstK (upsilon r) (upsilon (r + ω)) (upsilon (r + ω + 1)))
    {s : TW} (hs : CBw s (upsilon r)) (hρs : upsilon r ≤ val s (upsilon r))
    (htarget : ∀ κ' < upsilon r, ∃ μ, κ' < upsilon μ ∧ upsilon (μ + ω + 1) < upsilon r ∧
      RstK (upsilon μ) (upsilon (μ + ω)) (upsilon (μ + ω + 1)) ∧
      ∀ g, upsilon μ ≤ g → g ≤ upsilon (μ + ω + 1) + val s (upsilon μ) → le1 (upsilon μ) g) :
    le1 (upsilon r) (upsilon (r + ω + 1) + val s (upsilon r) + 1) := by
  classical
  have hnx := upsilon_isNext r
  have hCs : ∀ σ, (∀ c ∈ (csw s).toFinset, c < σ) → CBw s σ := fun σ hσ =>
    (cbw_iff s σ).2 (fun c hc => hσ c (List.mem_toFinset.2 hc))
  refine rs_rstF (T := val s) (C := (csw s).toFinset) h
    (fun c hc => (cbw_iff s _).1 hs c (List.mem_toFinset.1 hc)) hρs
    ((val_lt_eK h.ρE s hs).trans (eK_lt_ups h.ρU h.ρ1 _ _ hnx.1 hnx.2.1)) ?_ ?_ htarget
  · intro σ hσ hB hCσ _
    exact (pi_val hσ h.ρU hB s (hCs σ hCσ)).2
  · intro σ hσE hσρ heσ hCσ
    exact (val_lt_eK hσE s (hCs σ hCσ)).trans (eK_lt_of hσE h.ρU h.ρ1 hσρ heσ _)

/-- **Lemma RS for every term of `TW`** with constants below `ρ_λ`: `rs_rstW` when `t(ρ_λ) ≥ ρ_λ`;
otherwise `t` has no `ep` and is a constant, and `rs_rstT` applies. -/
theorem rsStep_W {l : Ordinal.{0}} {s : TW} (hs : CBw s (upsilon l)) : RsStep l (val s) := by
  by_cases hρs : upsilon l ≤ val s (upsilon l)
  · exact fun R htg => rs_rstW R hs hρs htg
  · have hn : noE s := by
      by_contra hn
      exact hρs (le_val_of_not_noE s hn)
    set c := val s (upsilon l) with hc
    have e : val s = OT.ev (OT.k c) := funext (fun y => by rw [OT.ev_k, hc, val_noE s hn y])
    have hcb : OT.CB (OT.k c) (upsilon l) := not_le.1 hρs
    rw [e]
    exact fun R htg => rs_rstT R hcb htg

end Googology.Trans.PoR.InaccPsi.R2
