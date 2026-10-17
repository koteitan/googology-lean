import Googology.Trans.PoR.InaccPsi.R2.EvZ


/-!
# Terms below the next fixed point of `ε`: Lemma EXACT, the uniform comparison, the representation, Lemma RS

The terms `TZ`: a constant (`cst a`), `ε_{x+t}` for a term `t` (`ee t`), a sum (`sm`), and `ω^t` (`pw t`).  These
are the Veblen terms `φ(1, ·)` in `x`: every value at an `ε`-number `x` above the constants is below `evZ x`, the
least fixed point of `ε` above `x` (`ζ_{x+1}`), and every ordinal below `evZ ρ` is a value at `ρ` (`repZ`).

* `TZ`, `TZ.val`, `TZ.CBz`, `TZ.csz`, `TZ.noE`; `valZ_lt` (`t(x) < evZ x`), `valZ_noE`, `le_valZ_of_not_noE`;
* `pi_valZ` (**Lemma EXACT for `TZ`**: `t(ρ) ∈ Tᵖ[σ]` and `π_{σ,ρ}(t(ρ)) = t(σ)`, by `pi_evAZ` and `pi_opowZ`),
  `uniZ_le`, `uniZ_lt`, `uniZ_eq` (the uniform comparison);
* `repZ` (**representation below `evZ ρ`**: an `ε`-number `v = ε_{ρ+c}` there has its index `c < v`);
* `rs_rstZ` (Lemma RS with the target `t(ρ) ≥ ρ`, from `rs_rstF`), `rsStep_Z` (Lemma RS for every term).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-- The terms `φ(1, ·)` in `x`: a constant, `ε_{x+t}`, a sum, or `ω^t`. -/
inductive TZ : Type 1
  | cst : Ordinal.{0} → TZ
  | ee : TZ → TZ
  | sm : TZ → TZ → TZ
  | pw : TZ → TZ

namespace TZ

/-- The value of a term at `x`. -/
noncomputable def val : TZ → Ordinal.{0} → Ordinal.{0}
  | cst a, _ => a
  | ee t, x => evA x (val t x)
  | sm a b, x => val a x + val b x
  | pw t, x => ω ^ val t x

/-- All constants below `s`. -/
def CBz : TZ → Ordinal.{0} → Prop
  | cst a, s => a < s
  | ee t, s => CBz t s
  | sm a b, s => CBz a s ∧ CBz b s
  | pw t, s => CBz t s

/-- The constants. -/
def csz : TZ → List Ordinal.{0}
  | cst a => [a]
  | ee t => csz t
  | sm a b => csz a ++ csz b
  | pw t => csz t

/-- No `ee` occurs. -/
def noE : TZ → Prop
  | cst _ => True
  | ee _ => False
  | sm a b => noE a ∧ noE b
  | pw t => noE t

@[simp] theorem val_cst (a x : Ordinal.{0}) : val (cst a) x = a := rfl
@[simp] theorem val_ee (t : TZ) (x : Ordinal.{0}) : val (ee t) x = evA x (val t x) := rfl
@[simp] theorem val_sm (a b : TZ) (x : Ordinal.{0}) : val (sm a b) x = val a x + val b x := rfl
@[simp] theorem val_pw (t : TZ) (x : Ordinal.{0}) : val (pw t) x = ω ^ val t x := rfl

theorem cbz_iff : ∀ (t : TZ) (s : Ordinal.{0}), CBz t s ↔ ∀ c ∈ csz t, c < s
  | cst a, s => by simp [CBz, csz]
  | ee t, s => cbz_iff t s
  | sm a b, s => by
      simp only [CBz, csz, List.mem_append]
      rw [cbz_iff a s, cbz_iff b s]
      constructor
      · rintro ⟨h1, h2⟩ c (hc | hc)
        · exact h1 c hc
        · exact h2 c hc
      · intro h; exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩
  | pw t, s => cbz_iff t s

theorem CBz_mono {t : TZ} {s s' : Ordinal.{0}} (h : CBz t s) (hs : s ≤ s') : CBz t s' :=
  (cbz_iff t s').2 (fun c hc => lt_of_lt_of_le ((cbz_iff t s).1 h c hc) hs)

end TZ

open TZ

/-! ## Values -/

/-- **`t(x) < evZ x`** for an `ε`-number `x` above the constants. -/
theorem valZ_lt {x : Ordinal.{0}} (hx : InE x) : ∀ t : TZ, CBz t x → val t x < evZ x
  | cst _, h => h.trans (lt_evZ x)
  | ee t, h => evA_lt_evZ hx (valZ_lt hx t h)
  | sm a b, h => add_lt_evZ (valZ_lt hx a h.1) (valZ_lt hx b h.2)
  | pw t, h => opow_lt_evZ (valZ_lt hx t h)

theorem valZ_lt_Om1 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {t : TZ} (h : CBz t x) :
    val t x < Om1 :=
  (valZ_lt hx t h).trans (evZ_lt_Om1 hx hx1)

/-- A term without `ee` has a constant value. -/
theorem valZ_noE : ∀ t : TZ, noE t → ∀ x y, val t x = val t y
  | cst _, _, _, _ => rfl
  | ee _, h, _, _ => absurd h id
  | sm a b, h, x, y => by simp only [val_sm, valZ_noE a h.1 x y, valZ_noE b h.2 x y]
  | pw t, h, x, y => by simp only [val_pw, valZ_noE t h x y]

/-- A term with an `ee` has value `≥ x`. -/
theorem le_valZ_of_not_noE {x : Ordinal.{0}} (hx : InE x) : ∀ t : TZ, ¬ noE t → x ≤ val t x
  | cst _, h => absurd trivial h
  | ee t, _ => le_evA hx _
  | sm a b, h => by
    simp only [noE, not_and_or] at h
    rcases h with h | h
    · exact (le_valZ_of_not_noE hx a h).trans le_self_add
    · exact (le_valZ_of_not_noE hx b h).trans le_add_self
  | pw t, h => (le_valZ_of_not_noE hx t h).trans (right_le_opow _ one_lt_omega0)

/-! ## Lemma EXACT -/

/-- **Lemma EXACT for `TZ`**: for `υ`-points `σ < ρ` (`Bases σ ρ`) and a term with constants below `σ`,
`t(ρ) ∈ Tᵖ[σ]` and `π_{σ,ρ}(t(ρ)) = t(σ)`. -/
theorem pi_valZ {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) :
    ∀ t : TZ, CBz t σ → val t ρ ∈ TB ρ σ ∧ pi σ ρ (val t ρ) = val t σ
  | cst a, h => ⟨mem_TB_of_lt hB h, pi_lt hB h⟩
  | ee t, h => by
    obtain ⟨h1, h2⟩ := pi_valZ hσ hρ hB t h
    have hZρ := valZ_lt hB.2.1 t (CBz_mono h hB.2.2.1.le)
    have hZσ := valZ_lt hB.1 t h
    rw [← h2] at hZσ
    obtain ⟨h3, h4⟩ := pi_evAZ hB h1 hZρ hZσ
    simp only [val_ee]
    exact ⟨h3, by rw [h4, h2]⟩
  | sm a b, h => by
    obtain ⟨h1, h2⟩ := pi_valZ hσ hρ hB a h.1
    obtain ⟨h3, h4⟩ := pi_valZ hσ hρ hB b h.2
    obtain ⟨h5, h6⟩ := pi_add hB h1 h3
    simp only [val_sm]
    exact ⟨h5, by rw [h6, h2, h4]⟩
  | pw t, h => by
    obtain ⟨h1, h2⟩ := pi_valZ hσ hρ hB t h
    have hb := valZ_lt_Om1 hB.2.1 hB.2.2.2 (t := t) (CBz_mono h hB.2.2.1.le)
    obtain ⟨h3, h4⟩ := pi_opowZ hσ hρ hB h1 hb
    simp only [val_pw]
    exact ⟨h3, by rw [h4, h2]⟩

/-- **Uniform comparison** (`≤`) of two terms at `υ`-points `σ < ρ`, constants below `σ`. -/
theorem uniZ_le {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : TZ}
    (ht : CBz t σ) (hu : CBz u σ) : val t ρ ≤ val u ρ ↔ val t σ ≤ val u σ := by
  obtain ⟨h1, h2⟩ := pi_valZ hσ hρ hB t ht
  obtain ⟨h3, h4⟩ := pi_valZ hσ hρ hB u hu
  rw [← h2, ← h4]
  exact ((pi_bijOn hB).2.le_iff_le h1 h3).symm

theorem uniZ_lt {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : TZ}
    (ht : CBz t σ) (hu : CBz u σ) : val t ρ < val u ρ ↔ val t σ < val u σ := by
  rw [← not_le, ← not_le, uniZ_le hσ hρ hB hu ht]

theorem uniZ_eq {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : TZ}
    (ht : CBz t σ) (hu : CBz u σ) : val t ρ = val u ρ ↔ val t σ = val u σ := by
  rw [le_antisymm_iff, le_antisymm_iff, uniZ_le hσ hρ hB ht hu, uniZ_le hσ hρ hB hu ht]

/-! ## The representation -/

/-- **Representation**: every ordinal below `evZ ρ` is the value at `ρ` of a term of `TZ` with constants below
`ρ`. -/
theorem repZ {ρ : Ordinal.{0}} (hρ : InE ρ) :
    ∀ v, v < evZ ρ → ∃ t : TZ, CBz t ρ ∧ val t ρ = v := by
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  rcases lt_or_ge v ρ with hvρ | hρv
  · exact ⟨cst v, hvρ, rfl⟩
  by_cases hI : Indec v
  · by_cases hE : InE v
    · obtain ⟨c, hc⟩ := evA_surj hρ hE hρv
      have hcv : c < v := by
        have hcZ : c < evZ ρ := lt_of_le_of_lt (hc ▸ le_evA_idx ρ c) hv
        rw [← hc]; exact lt_evA_self hρ hcZ
      obtain ⟨t, ht, e⟩ := IH c hcv (hcv.trans hv)
      exact ⟨ee t, ht, by rw [val_ee, e, hc]⟩
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

/-- **Lemma RS with the target `t(ρ)`** (`t(ρ) ≥ ρ`, constants below `ρ`). -/
theorem rs_rstZ {r : Ordinal.{0}} (h : RstK (upsilon r) (upsilon (r + ω)) (upsilon (r + ω + 1)))
    {s : TZ} (hs : CBz s (upsilon r)) (hρs : upsilon r ≤ val s (upsilon r))
    (htarget : ∀ κ' < upsilon r, ∃ μ, κ' < upsilon μ ∧ upsilon (μ + ω + 1) < upsilon r ∧
      RstK (upsilon μ) (upsilon (μ + ω)) (upsilon (μ + ω + 1)) ∧
      ∀ g, upsilon μ ≤ g → g ≤ upsilon (μ + ω + 1) + val s (upsilon μ) → le1 (upsilon μ) g) :
    le1 (upsilon r) (upsilon (r + ω + 1) + val s (upsilon r) + 1) := by
  classical
  have hnx := upsilon_isNext r
  have hCs : ∀ σ, (∀ c ∈ (csz s).toFinset, c < σ) → CBz s σ := fun σ hσ =>
    (cbz_iff s σ).2 (fun c hc => hσ c (List.mem_toFinset.2 hc))
  refine rs_rstF (T := val s) (C := (csz s).toFinset) h
    (fun c hc => (cbz_iff s _).1 hs c (List.mem_toFinset.1 hc)) hρs
    ((valZ_lt h.ρE s hs).trans_le (evZ_le_ups h.ρE h.ρ1 hnx.1 hnx.2.1)) ?_ ?_ htarget
  · intro σ hσ hB hCσ _
    exact (pi_valZ hσ h.ρU hB s (hCs σ hCσ)).2
  · intro σ hσE hσρ _ hCσ
    exact (valZ_lt hσE s (hCs σ hCσ)).trans_le (evZ_le_ltInf hσE (hσρ.trans h.ρ1) hσρ h.ρU.2)

/-- **Lemma RS for every term of `TZ`** with constants below `ρ_λ`. -/
theorem rsStep_Z {l : Ordinal.{0}} (hl : 0 < l) {s : TZ} (hs : CBz s (upsilon l)) : RsStep l (val s) := by
  by_cases hρs : upsilon l ≤ val s (upsilon l)
  · exact fun R htg => rs_rstZ R hs hρs htg
  · have hn : noE s := by
      by_contra hn
      exact hρs (le_valZ_of_not_noE (upsPt_inE (upsPt_upsilon hl)) s hn)
    set c := val s (upsilon l) with hc
    have e : val s = OT.ev (OT.k c) := funext (fun y => by rw [OT.ev_k, hc, valZ_noE s hn y])
    have hcb : OT.CB (OT.k c) (upsilon l) := not_le.1 hρs
    rw [e]
    exact fun R htg => rs_rstT R hcb htg

end Googology.Trans.PoR.InaccPsi.R2
