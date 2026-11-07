import Googology.Trans.PoR.InaccPsi.R2.FaOps

/-!
# Fa: THE CLOSED ATOMS AND THE `υ`-POINTS

`T = Kz.vbTK S λ K` on `D_K`, `θ = ψ₂(Ω_ω)`, `θ₂ = ψ₃(Ω_ω)`, `Θ` the reading at `λ`.  A **closed atom** (`FaLvB`) is `ψ₂(E)` for an own
`E ≥ Ω_ω` divisible by `θ₂`.

* `fa_dat` (**the datum at `Ω₂` of a member of `D_K` is in `D_K`**);
* `fa_Lv_fix` (**a closed atom is fixed by every visible `Hˡ¹_γ`, `γ < θ₂`**);
* `faZB` (**the largest closed atom at or below `x ∈ D_K`, `θ ≤ x < Ω₂`, is in `D_K`**);
* `fa_Lv_ups` (**the reading of a closed atom is a `υ`-point**), `fa_ups_Lv` (**a code `≥ θ` whose reading is a `υ`-point is a closed atom**).

No new axiom.  New definition: `FaLvB`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Fa

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Kz Googology.Trans.PoR.InaccPsi.R2.Ul

variable {S : InaccSeq.{0}}

/-- **A closed atom**: `ψ₂(E)`, `E ≥ Ω_ω` own, `θ₂ ∣ E`. -/
def FaLvB (S : InaccSeq.{0}) (u : Ordinal.{0}) : Prop :=
  ∃ E, E ∈ S.CSet E (S.psi E (Om (1 + 1))) ∧ Om ω ≤ E ∧ S.psi (Om ω) (Om (1 + 1 + 1)) ∣ E ∧ S.psi E (Om (1 + 1)) = u

theorem fa_θ2_SC : SC (S.psi (Om ω) (Om (1 + 1 + 1))) := Ui.ui_psi_SC (s := 1 + 1) (Om ω)

theorem fa_θ2_eps : ω ^ S.psi (Om ω) (Om (1 + 1 + 1)) = S.psi (Om ω) (Om (1 + 1 + 1)) := gg_SC_eps fa_θ2_SC

theorem fa_O2_pow_θ2 : Om (1 + 1 : Ordinal.{0}) ^ S.psi (Om ω) (Om (1 + 1 + 1)) = S.psi (Om ω) (Om (1 + 1 + 1)) := by
  have hS := fa_θ2_SC (S := S)
  have h2 : (Om (1 + 1) : Ordinal.{0}) < S.psi (Om ω) (Om (1 + 1 + 1)) := Ui.ui_L_lt_psi (s := 1 + 1) (Om ω)
  have hmul : IsPrincipal (· * ·) (S.psi (Om ω) (Om (1 + 1 + 1))) := by
    have h := isPrincipal_mul_omega0_opow_opow (S.psi (Om ω) (Om (1 + 1 + 1)))
    rwa [fa_θ2_eps, fa_θ2_eps] at h
  rw [Ui.ui_W_eq 1, isPrincipal_mul_iff_mul_left_eq.1 hmul _ ((Om_pos (by
    exact (add_pos_of_nonneg_of_pos zero_le zero_lt_one).ne'))) h2, fa_θ2_eps]

theorem fa_θ_le_Lv {u : Ordinal.{0}} (hu : FaLvB S u) : ConjT.th S ≤ u := by
  obtain ⟨E, -, hWE, -, rfl⟩ := hu
  exact (psi_mono (InR_Om_succ 1) hWE).1

theorem fa_Lv_SC {u : Ordinal.{0}} (hu : FaLvB S u) : SC u := by
  obtain ⟨E, -, -, -, rfl⟩ := hu
  exact Ui.ui_psi_SC (s := 1) E

/-- **A closed atom is fixed by every visible `Hˡ¹_γ`, `γ < θ₂`.** -/
theorem fa_Lv_fix {u γ : Ordinal.{0}} (hu : FaLvB S u) (hγ : γ < S.psi (Om ω) (Om (1 + 1 + 1)))
    (hK : UlK S 1 u γ) : ulH S 1 γ u = u := by
  obtain ⟨E, hown, hWE, hd, rfl⟩ := hu
  have hκ3 : S.InR (Om (1 + 1 + 1 : Ordinal.{0})) := InR_Om_succ (1 + 1)
  have hE0 : E ≠ 0 := ((SC_Om omega0_ne_zero).1.trans_le hWE).ne'
  have hγV : γ < Om (1 + 1 + 1) := hγ.trans (psi_lt hκ3 _)
  have hle : γ + 1 ≤ S.psi (Om ω) (Om (1 + 1 + 1)) := Order.add_one_le_of_lt hγ
  have hdiv : Om (1 + 1) ^ (γ + 1) ∣ E := by
    refine (opow_dvd_opow _ hle).trans ?_
    rw [fa_O2_pow_θ2]; exact hd
  have hlt : γ < S.psi E (Om (1 + 1 + 1)) := hγ.trans_le (psi_mono hκ3 hWE).1
  exact (Us.us_fix_iff one_lt_omega0 hown hE0 hγV).2 ⟨hdiv, hlt, hK⟩

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {K : Ordinal.{0}} (hKB : KzB S K)

include hl hX hKB

/-- **The datum at `Ω₂` of a member of `D_K` is in `D_K`.** -/
theorem fa_dat : ∀ x, VbDK S l K x → ∃ z, VbDK S l K z ∧ z < Om (1 + 1) ∧
    ∀ v, SC v → Om 1 < v → v ≤ Om (1 + 1) → (UlK S 1 v x ↔ z < v) := by
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  have hPC := faPC_D (S := S) (l := l) hKB
  have hh : ∀ {z : Ordinal.{0}}, z < Om (1 + 1) → ∀ v, SC v → Om 1 < v → v ≤ Om (1 + 1) → UlK S 1 v z → z < v :=
    fun hz v hv h1 _ hK => ulK_lt_W one_lt_omega0 hv h1 hK hz
  refine rxMs_ind (S := S) (T := upsilon l) fun x IH hx => ?_
  have hxE : RxEK S (upsilon l) K x := vbDK_E hl hX hx
  by_cases hx2 : x < Om (1 + 1)
  · exact ⟨x, hx, hx2, fun v hv h1 h2 => ⟨hh hx2 v hv h1 h2, UlK.small⟩⟩
  have hx2le : Om (1 + 1) ≤ x := not_lt.1 hx2
  have hx1 : Om 1 < x := (Om_lt_Om.2 (lt_add_one 1)).trans_le hx2le
  have h0 : x ≠ 0 := ((Om_pos one_ne_zero).trans hx1).ne'
  have hall : (∀ v, UlK S 1 v x) → ∃ z, VbDK S l K z ∧ z < Om (1 + 1) ∧
      ∀ v, SC v → Om 1 < v → v ≤ Om (1 + 1) → (UlK S 1 v x ↔ z < v) := fun h =>
    ⟨0, hPC.zero, (Ui.ui_SC_W 1).1, fun v hv _ _ => ⟨fun _ => hv.1, fun _ => h v⟩⟩
  by_cases hΩ : ∃ j : ℕ, x = Om (j : Ordinal.{0})
  · obtain ⟨j, rfl⟩ := hΩ
    exact hall fun v => UlK.om (UlK.nat j)
  by_cases hxW : x = Om ω
  · subst hxW
    exact hall fun v => UlK.om (by
      have := UlK.opow (UlK.one (S := S) (s := 1) (q := v)); rwa [opow_one] at this)
  have hx2' : Om (1 + 1) < x := lt_of_le_of_ne hx2le (fun e => hΩ ⟨2, by rw [← e]; norm_num⟩)
  by_cases hSx : SC x
  · obtain ⟨j, hj, d, hdE, hdn, rfl, hst⟩ := kzE_atom hKB hZ1.le hxE hSx hx1 (kzNe hKB hxE hΩ hxW)
    have hj2 : 2 ≤ j := by
      by_contra hc
      have hj1 : j = 1 := by omega
      subst hj1
      have := (psiS_bounds (S := S) d ((1 : ℕ) : Ordinal.{0})).2
      rw [Nat.cast_one] at this hx2'
      exact absurd (hx2'.trans this) (lt_irrefl _)
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hj' : 1 ≤ j' := by omega
    have hdD : VbDK S l K d := vbDK_atom hl hX hx hdE hdn hj
    have hms := rxMs_lt_stage (kzE_lt_Lam hKB hdE) hst
    rw [Nat.cast_succ] at hdn hx hx2 hx2le hx2' hx1 h0 hxE hms
    obtain ⟨z, hzD, hz2, hz⟩ := IH d hms hdD
    refine ⟨z, hzD, hz2, fun v hv h1 h2 => ?_⟩
    have hπ : S.InR (Om ((j' : Ordinal.{0}) + 1 + 1)) := InR_Om_succ _
    have hne : Om ((j' : Ordinal.{0}) + 1 + 1) ≠ Om (1 + 1) := by
      intro e
      have e1 : (j' : Ordinal.{0}) + 1 + 1 = 1 + 1 := le_antisymm (Om_le_Om.1 e.le) (Om_le_Om.1 e.ge)
      have e3 : ((j' + 1 + 1 : ℕ) : Ordinal.{0}) = ((1 + 1 : ℕ) : Ordinal.{0}) := by
        rw [Nat.cast_succ, Nat.cast_succ, Nat.cast_succ, Nat.cast_one]; exact e1
      have e4 := Nat.cast_inj.1 e3
      omega
    have hOmK : UlK S 1 v (Om ((j' : Ordinal.{0}) + 1 + 1)) := by
      have := UlK.nat (S := S) (s := 1) (q := v) (j' + 1 + 1)
      rw [Nat.cast_succ, Nat.cast_succ] at this
      exact UlK.om this
    have hvx : v ≤ S.psi d (Om ((j' : Ordinal.{0}) + 1 + 1)) := h2.trans hx2le
    have hvL : v ≤ S.Lam := (hv.1.trans_le hvx |> fun _ => (hvx.trans_lt (hx.2.2.trans (kzK_lt_Lam hKB))).le)
    rw [← hz v hv h1 h2]
    exact ⟨fun hK => Uo.uoArg hvL hπ hdn hK hvx, fun hK => UlK.coll hπ hne hOmK hK⟩
  by_cases hε : ω ^ x = x
  · obtain ⟨hv, ha0, ha, hb⟩ := rxVeb hx1 hε hSx
    obtain ⟨haD, hbD, -, -, hha, hhb⟩ := vbDK_veb hx hxE hv hb
    obtain ⟨z1, hz1D, hz1, hz1K⟩ := IH _ (rxMs_lt_val hha ha) haD
    obtain ⟨z2, hz2D, hz2, hz2K⟩ := IH _ (rxMs_lt_val hhb hb) hbD
    have hM : VbDK S l K (max z1 z2) := by
      rcases le_total z1 z2 with h | h
      · rw [max_eq_right h]; exact hz2D
      · rw [max_eq_left h]; exact hz1D
    refine ⟨max z1 z2, hM, max_lt hz1 hz2, fun v hvS h1 h2 => ?_⟩
    rw [max_lt_iff, ← hz1K v hvS h1 h2, ← hz2K v hvS h1 h2]
    constructor
    · intro hK
      have hK' : UlK S 1 v (veblen (invVeblen₁ x) (invVeblen₂ x)) := by rw [hv]; exact hK
      exact Qt.ulK_veb_parts hK' (by rw [hv]; exact ha) (by rw [hv]; exact hb)
    · rintro ⟨h3, h4⟩
      have := UlK.phi h3 h4; rwa [hv] at this
  -- the Cantor normal form
  have hlx : log ω x < x := ruLog_lt hx1 hε
  obtain ⟨hlD, -, hlh⟩ := vbDK_log hx hxE
  obtain ⟨hrD, -, hrh⟩ := vbDK_rem hx hxE
  obtain ⟨z1, hz1D, hz1, hz1K⟩ := IH _ (rxMs_lt_val hlh hlx) hlD
  obtain ⟨z2, hz2D, hz2, hz2K⟩ := IH _ (rxMs_lt_val hrh (mod_opow_log_lt_self ω h0)) hrD
  have hM : VbDK S l K (max z1 z2) := by
    rcases le_total z1 z2 with h | h
    · rw [max_eq_right h]; exact hz2D
    · rw [max_eq_left h]; exact hz1D
  refine ⟨max z1 z2, hM, max_lt hz1 hz2, fun v hv h1 h2 => ?_⟩
  rw [max_lt_iff, ← hz1K v hv h1 h2, ← hz2K v hv h1 h2]
  constructor
  · intro hK
    obtain ⟨-, -, h3, h4, -⟩ := ulK_split hv hK h0
    exact ⟨h3, h4⟩
  · rintro ⟨h3, h4⟩
    obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
    have hdm : ω ^ log ω x * n + x % ω ^ log ω x = x := by
      rw [← hn]; exact Ordinal.div_add_mod x _
    have := UlK.add ((UlK.opow h3).mul_nat n) h4
    rwa [hdm] at this

end Rst

theorem fa_θ2_dvd_W : S.psi (Om ω) (Om (1 + 1 + 1)) ∣ (Om ω : Ordinal.{0}) := by
  have hOW : SC (Om ω : Ordinal.{0}) := SC_Om omega0_ne_zero
  have h3W : Om (1 + 1 + 1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 Vp.vp_three_lt_omega
  have hle : S.psi (Om ω) (Om (1 + 1 + 1)) ≤ Om ω := (psi_lt (InR_Om_succ (1 + 1)) _).le.trans h3W.le
  have h := opow_dvd_opow ω hle
  rwa [fa_θ2_eps, gg_SC_eps hOW] at h

theorem fa_θ2_dvd_O3 : S.psi (Om ω) (Om (1 + 1 + 1)) ∣ (Om (1 + 1 + 1) : Ordinal.{0}) := by
  have h := opow_dvd_opow ω (psi_lt (S := S) (InR_Om_succ (1 + 1)) (Om ω)).le
  rwa [fa_θ2_eps, Kx.kx3e] at h

theorem fa_Lv_θ : FaLvB S (ConjT.th S) :=
  ⟨Om ω, ConjT.OmW_mem S _ _, le_rfl, fa_θ2_dvd_W, rfl⟩

section Law

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {K : Ordinal.{0}} (hKB : KzB S K)
  (hown : ConjT.Aη S (cdEta S l) ∈ S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)))
  (hρ : S.psi (ConjT.Aη S (cdEta S l)) (Om 1) = upsilon l) (hWK : Om ω < K)

include hl hX hKB hown hρ hWK

/-- **The largest closed atom at or below `x ∈ D_K`, `θ ≤ x < Ω₂`, is in `D_K`.** -/
theorem faZB : ∀ x, x < Om (1 + 1) → VbDK S l K x → ConjT.th S ≤ x →
    ∃ w, VbDK S l K w ∧ FaLvB S w ∧ w ≤ x ∧ ∀ u, FaLvB S u → u ≤ x → u ≤ w := by
  have hPC := faPC_D (S := S) (l := l) hKB
  have hs : (1 : Ordinal.{0}) < ω := one_lt_omega0
  have hκ : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have h1θ : Om 1 < ConjT.th S := Ui.ui_L_lt_psi (s := 1) (Om ω)
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx2 hx hθx
  have hx1 : Om 1 < x := h1θ.trans_le hθx
  have h0 : x ≠ 0 := ((Om_pos one_ne_zero).trans hx1).ne'
  -- two candidates
  have hcomb : ∀ q1 q2, q1 < x → q2 < x → VbDK S l K q1 → VbDK S l K q2 →
      (∀ u, FaLvB S u → u ≤ x → u ≤ q1 ∨ u ≤ q2) →
      ∃ w, VbDK S l K w ∧ FaLvB S w ∧ w ≤ x ∧ ∀ u, FaLvB S u → u ≤ x → u ≤ w := by
    intro q1 q2 h1 h2 hq1 hq2 hkey
    have hstep : ∀ q, q < x → VbDK S l K q → ConjT.th S ≤ q →
        ∃ w, VbDK S l K w ∧ FaLvB S w ∧ w ≤ x ∧ ∀ u, FaLvB S u → u ≤ q → u ≤ w := fun q hq hqD hθq => by
      obtain ⟨w, a1, a2, a3, a4⟩ := IH q hq (hq.trans hx2) hqD hθq
      exact ⟨w, a1, a2, a3.trans hq.le, a4⟩
    by_cases h3 : ConjT.th S ≤ q1
    · obtain ⟨w1, a1, a2, a3, a4⟩ := hstep q1 h1 hq1 h3
      by_cases h4 : ConjT.th S ≤ q2
      · obtain ⟨w2, b1, b2, b3, b4⟩ := hstep q2 h2 hq2 h4
        rcases le_total w1 w2 with h | h
        · exact ⟨w2, b1, b2, b3, fun u hu hux => by
            rcases hkey u hu hux with h' | h'
            · exact (a4 u hu h').trans h
            · exact b4 u hu h'⟩
        · exact ⟨w1, a1, a2, a3, fun u hu hux => by
            rcases hkey u hu hux with h' | h'
            · exact a4 u hu h'
            · exact (b4 u hu h').trans h⟩
      · exact ⟨w1, a1, a2, a3, fun u hu hux => by
          rcases hkey u hu hux with h' | h'
          · exact a4 u hu h'
          · exact absurd ((fa_θ_le_Lv hu).trans h') h4⟩
    · have h4 : ConjT.th S ≤ q2 := by
        rcases hkey _ fa_Lv_θ hθx with h' | h'
        · exact absurd h' h3
        · exact h'
      obtain ⟨w2, b1, b2, b3, b4⟩ := hstep q2 h2 hq2 h4
      exact ⟨w2, b1, b2, b3, fun u hu hux => by
        rcases hkey u hu hux with h' | h'
        · exact absurd ((fa_θ_le_Lv hu).trans h') h3
        · exact b4 u hu h'⟩
  by_cases hSx : SC x
  · have hA : x < S.psi K (Om (1 + 1)) := lt_psi_of_mem hκ hx.2.1 hx2
    obtain ⟨E, hownE, hE⟩ := Ui.ui_own_of_SC (s := 1) hs hSx hx1 hA
    have hWE : Om ω ≤ E := not_lt.1 fun h => by
      have h1 := Ui.ui_psi_lt_of_own (s := 1) hownE h
      rw [hE] at h1
      exact absurd h1 (not_lt.2 hθx)
    by_cases hdE : S.psi (Om ω) (Om (1 + 1 + 1)) ∣ E
    · exact ⟨x, hx, ⟨E, hownE, hWE, hdE, hE⟩, le_rfl, fun u _ h => h⟩
    have hne := Vp.vp_nf_ex (S := S) (s := 1) hs hSx hx1 hA
    obtain ⟨hlV, -, -, -, -⟩ := Vp.vpLev_spec hSx hx1 hne
    obtain ⟨hI, hIlt⟩ := Vp.vp_nf hSx hx1 hne
    set γ := Vp.vpLev S 1 x with hγdef
    set y := Vp.vpI S 1 γ x with hydef
    have hγθ : γ < S.psi (Om ω) (Om (1 + 1 + 1)) := by
      by_contra hc
      have hd := Us.us_dvd_val hs hownE (hI.trans hE.symm)
      have h1 : Om (1 + 1) ^ S.psi (Om ω) (Om (1 + 1 + 1)) ∣ Om (1 + 1) ^ γ := opow_dvd_opow _ (not_lt.1 hc)
      rw [fa_O2_pow_θ2] at h1
      exact hdE (h1.trans hd)
    have hθlt : ConjT.th S < x := lt_of_le_of_ne hθx fun e => by
      have hEW : E = Om ω := Ui.ui_own_unique (s := 1) hownE (ConjT.OmW_mem S _ _) (hE.trans e.symm)
      rw [hEW] at hdE
      exact hdE fa_θ2_dvd_W
    have hyz : y < ulH S 1 γ y := by rw [hI]; exact hIlt
    have hzW : ulH S 1 γ y < Om (1 + 1) := by rw [hI]; exact hx2
    have hzD : VbDK S l K (ulH S 1 γ y) := by rw [hI]; exact hx
    have hA' : ulH S 1 γ y < S.psi K (Om (1 + 1)) := by rw [hI]; exact hA
    have hθz : ConjT.th S < ulH S 1 γ y := by rw [hI]; exact hθlt
    obtain ⟨B, c, D, hownB, hc, hcD, hcond, hcase⟩ := Vp.vp_dec (S := S) (s := 1) hs hyz hA'
    obtain ⟨hγD, -, -, hcDD, -⟩ := faALc hl hX hKB hown hρ hWK hγθ hyz hzW hzD hθz hownB hc hcD hcond hcase
    obtain ⟨z, hzDD, hz2, hzK⟩ := fa_dat hl hX hKB γ hγD
    have hzx : z < x := by
      refine (hzK x hSx hx1 hx2.le).1 ((ul_vis hSx).1 ?_)
      have := ulH_D_lt (S := S) (s := 1) γ y
      rwa [hI] at this
    have hcy : c ≤ y := by rw [← hcD]; exact le_self_add
    refine hcomb c z (hcy.trans_lt hIlt) hzx hcDD hzDD fun u hu hux => ?_
    by_cases hzu : z < u
    · left
      have huS := fa_Lv_SC hu
      have h1u : Om 1 < u := h1θ.trans_le (fa_θ_le_Lv hu)
      have hu2 : u ≤ Om (1 + 1) := hux.trans hx2.le
      have hK := (hzK u huS h1u hu2).2 hzu
      have hfix := fa_Lv_fix hu hγθ hK
      have huy : u ≤ y := by
        have h1 : ulH S 1 γ u ≤ ulH S 1 γ y := by rw [hfix, hI]; exact hux
        exact (ulH_le_iff γ).1 h1
      rcases hcase with hc0 | ⟨-, hmax⟩
      · subst hc0
        rw [zero_add] at hcD
        subst hcD
        have h2 := hcond u huy
        rw [zero_add, hfix] at h2
        exact absurd h2 (lt_irrefl _)
      · exact hmax u hfix huy
    · right; exact not_lt.1 hzu
  by_cases hε : ω ^ x = x
  · have hdec := veblen_invVeblen₁_invVeblen₂ x
    rw [hε] at hdec
    have hxE : RxEK S (upsilon l) K x := vbDK_E hl hX hx
    obtain ⟨hv, ha0, ha, hb⟩ := rxVeb hx1 hε hSx
    obtain ⟨haD, hbD, -, -, -, -⟩ := vbDK_veb hx hxE hv hb
    refine hcomb _ _ ha hb haD hbD fun u hu hux => ?_
    by_contra hc
    push Not at hc
    have := (fa_Lv_SC hu).2 _ hc.1 _ hc.2
    rw [hv] at this
    exact absurd hux (not_le.2 this)
  · have hlx : log ω x < x := ruLog_lt hx1 hε
    have hrx := mod_opow_log_lt_self ω h0
    have hxE : RxEK S (upsilon l) K x := vbDK_E hl hX hx
    obtain ⟨hlD, -, -⟩ := vbDK_log hx hxE
    obtain ⟨hrD, -, -⟩ := vbDK_rem hx hxE
    refine hcomb _ _ hlx hrx hlD hrD fun u hu hux => ?_
    by_contra hc
    push Not at hc
    have huS := fa_Lv_SC hu
    obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
    have hdm : ω ^ log ω x * n + x % ω ^ log ω x = x := by
      rw [← hn]; exact Ordinal.div_add_mod x _
    have h1 : ω ^ log ω x < u := by
      have := huS.2 0 huS.1 _ hc.1; rwa [veblen_zero_apply] at this
    have hmul : IsPrincipal (· * ·) u := by
      have h := isPrincipal_mul_omega0_opow_opow u
      rwa [gg_SC_eps huS, gg_SC_eps huS] at h
    have hnu : (n : Ordinal.{0}) < u := (natCast_lt_omega0 n).trans (omega0_lt_inE (gg_SC_eps huS))
    have h2 : x < u := by
      rw [← hdm]; exact huS.isPrincipal (hmul h1 hnu) hc.2
    exact absurd hux (not_le.2 h2)

/-- `T θ₂ = θ`, and `θ₂ ∈ D_K`. -/
theorem fa_T_θ2 (hWA : Om ω < ConjT.Aη S (cdEta S l)) :
    VbDK S l K (S.psi (Om ω) (Om (1 + 1 + 1))) ∧ vbTK S l K (S.psi (Om ω) (Om (1 + 1 + 1))) = ConjT.th S := by
  have hWD : VbDK S l K (Om ω) := ⟨ConjT.OmW_mem S _ _, ConjT.OmW_mem S _ _, hWK⟩
  have hownW3 : (Om ω : Ordinal.{0}) ∈ S.CSet (Om ω) (S.psi (Om ω) (Om (1 + 1 + 1))) := ConjT.OmW_mem S _ _
  have h := (vbTK_atom hl hX hKB (k := 1) le_rfl hWD (by simpa using hownW3)).1
  rw [vbTK_OmW hl hX hKB hWK] at h
  refine ⟨?_, by simpa using h⟩
  have := fa_coll (S := S) (l := l) hKB (j := 2) hWD hWA
  simpa [one_add_one_eq_two] using this

/-- **`faG E` is `A_{η'}`** for a closed `E`. -/
theorem fa_G_eta {E : Ordinal.{0}} (hED : VbDK S l K E) (hEA : E < ConjT.Aη S (cdEta S l)) (hWE : Om ω ≤ E)
    (hd : S.psi (Om ω) (Om (1 + 1 + 1)) ∣ E) : ∃ η', faG S l K E = ConjT.Aη S η' := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have h30 : Om (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := Kx.kx3SC.1.ne'
  obtain ⟨hθ2D, hTθ2⟩ := fa_T_θ2 hl hX hKB hown hρ hWK (hWE.trans_lt hEA)
  obtain ⟨haD, hδD⟩ := fa_parts3 (S := S) (l := l) hKB hED
  have hdW3 : Om (1 + 1 + 1) ∣ (Om ω : Ordinal.{0}) := by
    have h := opow_dvd_opow ω (Om_lt_Om.2 Vp.vp_three_lt_omega).le
    rwa [Kx.kx3e, gg_SC_eps (SC_Om omega0_ne_zero)] at h
  have hWa : Om ω ≤ Om (1 + 1 + 1) * (E / Om (1 + 1 + 1)) := Uw.uw_le_trunc h30 hdW3 hWE
  have hWD : VbDK S l K (Om ω) := ⟨ConjT.OmW_mem S _ _, ConjT.OmW_mem S _ _, hWK⟩
  have hTa : Om ω ≤ vbTK S l K (Om (1 + 1 + 1) * (E / Om (1 + 1 + 1))) := by
    have h := (vbTK_le_iff hl hX hKB hWD haD).1 hWa
    rwa [vbTK_OmW hl hX hKB hWK] at h
  set L := S.psi (vbTK S l K (Om (1 + 1 + 1) * (E / Om (1 + 1 + 1)))) (Om (1 + 1)) with hLdef
  have hθL : ConjT.th S ≤ L := (psi_mono hκ2 hTa).1
  have hLS : SC L := Ui.ui_psi_SC (s := 1) _
  have hθS : SC (ConjT.th S) := Ui.ui_psi_SC (s := 1) (Om ω)
  have hθe := gg_SC_eps hθS
  have hdL : ConjT.th S ∣ L := by
    have h := opow_dvd_opow ω hθL
    rwa [hθe, gg_SC_eps hLS] at h
  have hωL : (ω : Ordinal.{0}) ≤ L := ((Vp.vp_omega_le_Om1.trans (Ui.ui_L_lt_psi (s := 1) (Om ω)).le)).trans hθL
  have hδ : S.psi (Om ω) (Om (1 + 1 + 1)) ∣ E % Om (1 + 1 + 1) := by
    have hd3 : S.psi (Om ω) (Om (1 + 1 + 1)) ∣ Om (1 + 1 + 1) * (E / Om (1 + 1 + 1)) :=
      Dvd.dvd.mul_right fa_θ2_dvd_O3 _
    have hdd := hd
    rw [← Ordinal.div_add_mod E (Om (1 + 1 + 1))] at hdd
    exact (Ordinal.dvd_add_iff hd3).1 hdd
  have hTδ : ConjT.th S ∣ vbTK S l K (E % Om (1 + 1 + 1)) := by
    have h := (faT_dvd hl hX hKB hθ2D _ hδD).1 (by rw [fa_θ2_eps]; exact hδ)
    rwa [hTθ2, hθe] at h
  obtain ⟨L1, hL1⟩ := hdL
  obtain ⟨t, ht⟩ := hTδ
  refine ⟨cdEta S l + L1 + t, ?_⟩
  show ConjT.Aη S (cdEta S l) + 1 + L + vbTK S l K (E % Om (1 + 1 + 1)) = Om ω + ConjT.th S * (cdEta S l + L1 + t)
  rw [add_assoc (ConjT.Aη S (cdEta S l)) 1 L, one_add_of_omega0_le hωL, ht, hL1]
  show Om ω + ConjT.th S * cdEta S l + ConjT.th S * L1 + ConjT.th S * t = _
  rw [mul_add, mul_add, add_assoc, add_assoc, add_assoc]

/-- **The reading of a closed atom is a `υ`-point.** -/
theorem fa_Lv_ups {E : Ordinal.{0}} (hED : VbDK S l K E) (hEn : E ∈ S.CSet E (S.psi E (Om (1 + 1))))
    (hEA : E < ConjT.Aη S (cdEta S l)) (hWE : Om ω ≤ E) (hd : S.psi (Om ω) (Om (1 + 1 + 1)) ∣ E) :
    UpsPt (gxTh (upsilon l) (ldAtR S l) (S.psi E (Om (1 + 1)))) := by
  have h3W : Om (1 + 1 + 1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 Vp.vp_three_lt_omega
  obtain ⟨hG, -, -⟩ := faG_law hl hX hKB hown hρ hED hEn hEA (h3W.le.trans hWE)
  obtain ⟨η', hη'⟩ := fa_G_eta hl hX hKB hown hρ hWK hED hEA hWE hd
  rw [hG, hη', ← ups_iota S η']
  exact upsPt_upsilon (lt_of_lt_of_le zero_lt_one (one_le_iota η'))

/-- **Every reading is below `ψ₁(A + Ω₂ + θ)`.** -/
theorem fa_Θ_lt (hAK : ConjT.Aη S (cdEta S l) < K) : ∀ c, GxCl (upsilon l) (ldAtR S l) c →
    gxTh (upsilon l) (ldAtR S l) c < S.psi (ConjT.Aη S (cdEta S l) + Om (1 + 1) + ConjT.th S) (Om 1) := by
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  set A := ConjT.Aη S (cdEta S l) with hAdef
  have hown2 : A + Om (1 + 1) ∈ S.CSet (A + Om (1 + 1)) (S.psi (A + Om (1 + 1)) (Om 1)) :=
    CSet.add_mem ((psi_mono hκ1 le_self_add).2 hown) (Mx.mxOm2_mem _ _)
  have hθ0 : 0 < ConjT.th S := (Ui.ui_psi_SC (s := 1) (Om ω)).1
  have hlt2 : A + Om (1 + 1) < A + Om (1 + 1) + ConjT.th S := lt_add_of_pos_right _ hθ0
  have hstrict : S.psi (A + Om (1 + 1)) (Om 1) < S.psi (A + Om (1 + 1) + ConjT.th S) (Om 1) :=
    psi_lt_psi_of_mem hκ1 hlt2 ((psi_mono hκ1 hlt2.le).2 hown2)
  have hS : SC (S.psi (A + Om (1 + 1) + ConjT.th S) (Om 1)) := fa0_SC _
  have hρ2 : upsilon l ≤ S.psi (A + Om (1 + 1)) (Om 1) := by
    rw [← hρ]; exact (psi_mono hκ1 le_self_add).1
  intro c hc
  induction hc with
  | @small x h =>
    rw [gxTh_small h.le]
    exact (h.trans_le hρ2).trans hstrict
  | om =>
    rw [gxTh_Om1 hZ hZ1 hAt]
    exact hρ2.trans_lt hstrict
  | @atom s hs =>
    obtain ⟨a, ha, haA, rfl⟩ := hs
    have hρK : upsilon l ≤ S.psi K (Om (1 + 1)) := (hZ1.trans (Ui.ui_L_lt_psi (s := 1) K)).le
    have haD : VbDK S l K a := ⟨ha, CSet_mono hAK.le hρK ha, haA.trans hAK⟩
    have hUp := kzUp_at hl hX hKB hown hρ a haD haA
    refine hUp.trans_lt (lt_of_le_of_lt ((psi_mono hκ1 ?_).1) hstrict)
    rw [add_assoc]
    exact add_le_add le_rfl ((Ui.ui_SC_W 1).isPrincipal (Ui.ui_one_lt_SC (Ui.ui_SC_W 1)) (psi_lt hκ2 _)).le
  | @add x y hx hy ihx ihy =>
    rw [gxTh_add hZ hAt hx y]
    exact hS.isPrincipal ihx ihy
  | @phi x y hx hy ihx ihy =>
    rw [gxTh_phi hZ hAt x hx y hy]
    exact hS.2 _ ihx _ ihy

/-- **A code `≥ θ` of the hull whose reading is a `υ`-point is a closed atom.** -/
theorem fa_ups_Lv (hAK : ConjT.Aη S (cdEta S l) < K) {c : Ordinal.{0}} (hcD : VbDK S l K c) (hc2 : c < Om (1 + 1))
    (hθc : ConjT.th S ≤ c) (hU : UpsPt (gxTh (upsilon l) (ldAtR S l) c)) : FaLvB S c := by
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hcc : GxCl (upsilon l) (ldAtR S l) c := (ldHull_iff hl hX hc2).1 hcD.1
  have h1θ : Om 1 < ConjT.th S := Ui.ui_L_lt_psi (s := 1) (Om ω)
  have hc1 : Om 1 < c := h1θ.trans_le hθc
  have hPC := faPC_D (S := S) (l := l) hKB
  have h3W : Om (1 + 1 + 1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 Vp.vp_three_lt_omega
  have h30 : Om (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := Kx.kx3SC.1.ne'
  set u := gxTh (upsilon l) (ldAtR S l) c with hudef
  obtain ⟨ξ, hξ0, hξ⟩ := upsPt_iff_upsilon.1 hU
  have hξ1 : 1 ≤ ξ := Order.one_le_iff_pos.2 hξ0
  -- the name of the bound
  set A := ConjT.Aη S (cdEta S l) with hAdef
  have hθS : SC (ConjT.th S) := Ui.ui_psi_SC (s := 1) (Om ω)
  have hθe := gg_SC_eps hθS
  have hθ2 : ConjT.th S < Om (1 + 1) := psi_lt hκ2 _
  have hη0 : ConjT.Aη S (cdEta S l + Om (1 + 1) + 1) = A + Om (1 + 1) + ConjT.th S := by
    have hmul : IsPrincipal (· * ·) (Om (1 + 1) : Ordinal.{0}) := by
      have h := isPrincipal_mul_omega0_opow_opow (Om (1 + 1) : Ordinal.{0})
      rwa [gg_SC_eps ldOm2_SC, gg_SC_eps ldOm2_SC] at h
    have e : ConjT.th S * Om (1 + 1) = Om (1 + 1) := isPrincipal_mul_iff_mul_left_eq.1 hmul _ hθS.1 hθ2
    show Om ω + ConjT.th S * (cdEta S l + Om (1 + 1) + 1) = Om ω + ConjT.th S * cdEta S l + Om (1 + 1) + ConjT.th S
    rw [mul_add, mul_add, e, mul_one, add_assoc, add_assoc, add_assoc]
  have huη : upsilon ξ ≤ S.psi (Om ω + ConjT.th S * (cdEta S l + Om (1 + 1) + 1)) (Om 1) := by
    rw [← hξ]
    have h := (fa_Θ_lt hl hX hKB hown hρ hWK hAK c hcc).le
    rw [← hη0] at h
    exact h
  obtain ⟨η₁, -, hη₁⟩ := ups_below_named S hξ1 huη
  have huS : SC u := by rw [hξ, hη₁]; exact SC_psi hκ1 _
  have huE : ω ^ u = u := gg_SC_eps huS
  have hcE : ω ^ c = c := by
    have hp := gxTh_opow hZ hAt hcc
    rw [← hudef, huE] at hp
    have hoc : GxCl (upsilon l) (ldAtR S l) (ω ^ c) := hcc.opow hZ.1
    rcases lt_trichotomy (ω ^ c) c with h | h | h
    · exact absurd (gxTh_lt hoc h) (by rw [hp]; exact lt_irrefl _)
    · exact h
    · exact absurd (gxTh_lt hcc h) (by rw [hp]; exact lt_irrefl _)
  have hcS : SC c := by
    by_contra hS
    obtain ⟨hv, -, ha, hb⟩ := rxVeb hc1 hcE hS
    obtain ⟨hac, hbc⟩ := gxDecV hZ.1 hAt hcc _ _ hv hb
    have hphi := gxTh_phi hZ hAt _ hac _ hbc
    rw [hv] at hphi
    have h1 := gxTh_lt hac ha
    have h2 := gxTh_lt hbc hb
    rw [← hudef] at h1 h2
    have := huS.2 _ h1 _ h2
    rw [← hphi] at this
    exact lt_irrefl _ this
  have hA : c < S.psi K (Om (1 + 1)) := lt_psi_of_mem hκ2 hcD.2.1 hc2
  obtain ⟨E, hownE, hE⟩ := Ui.ui_own_of_SC (s := 1) one_lt_omega0 hcS hc1 hA
  have hWE : Om ω ≤ E := not_lt.1 fun h => by
    have h1 := Ui.ui_psi_lt_of_own (s := 1) hownE h
    rw [hE] at h1
    exact absurd h1 (not_lt.2 hθc)
  subst hE
  obtain ⟨hED, hEA⟩ := fa_arg hl hX (r := 1) le_rfl hcD hownE
  obtain ⟨hG, hownG, -⟩ := faG_law hl hX hKB hown hρ hED hownE hEA (h3W.le.trans hWE)
  -- `faG E = A_{η*}`
  have hlt0 : upsilon ξ < Pv S (cdEta S l + Om (1 + 1) + 1) := by
    show upsilon ξ < S.psi (ConjT.Aη S (cdEta S l + Om (1 + 1) + 1)) (Om 1)
    rw [← hξ, hη0]
    exact fa_Θ_lt hl hX hKB hown hρ hWK hAK _ hcc
  obtain ⟨hg, -, hηlt, hpv⟩ := cdEta_pv_spec (S := S) hξ0.ne' hlt0
  have hAlt : ConjT.Aη S (cdEta S ξ) < S.Lam := by
    have h1 : ConjT.Aη S (cdEta S ξ) < ConjT.Aη S (cdEta S l + Om (1 + 1) + 1) := by
      show Om ω + ConjT.th S * cdEta S ξ < Om ω + ConjT.th S * _
      exact (add_lt_add_iff_left _).2 ((mul_lt_mul_iff_right₀ hθS.1).2 hηlt)
    rw [hη0] at h1
    refine h1.trans ((?_ : A + Om (1 + 1) + ConjT.th S < K).trans (kzK_lt_Lam hKB))
    have h2K : Om (1 + 1 : Ordinal.{0}) < K := (Om_lt_Om.2 (Ui.ui_s1_lt_omega one_lt_omega0)).trans_le hKB.ge
    exact hKB.sc.isPrincipal (hKB.sc.isPrincipal hAK h2K) (hθ2.trans h2K)
  have hownA := Sf.sfOwn hg hAlt
  have heq : S.psi (faG S l K E) (Om 1) = S.psi (ConjT.Aη S (cdEta S ξ)) (Om 1) := by
    rw [← hG]; show u = _; rw [hξ]; exact hpv.symm
  have hG2 : faG S l K E = ConjT.Aη S (cdEta S ξ) :=
    Ui.ui_own_unique (s := 0) (by simpa using hownG) (by simpa using hownA) (by simpa using heq)
  obtain ⟨haD, hδD⟩ := fa_parts3 (S := S) (l := l) hKB hED
  have hdW3 : Om (1 + 1 + 1) ∣ (Om ω : Ordinal.{0}) := by
    have h := opow_dvd_opow ω h3W.le
    rwa [Kx.kx3e, gg_SC_eps (SC_Om omega0_ne_zero)] at h
  have hWa : Om ω ≤ Om (1 + 1 + 1) * (E / Om (1 + 1 + 1)) := Uw.uw_le_trunc h30 hdW3 hWE
  have hWD : VbDK S l K (Om ω) := ⟨ConjT.OmW_mem S _ _, ConjT.OmW_mem S _ _, hWK⟩
  have hTa : Om ω ≤ vbTK S l K (Om (1 + 1 + 1) * (E / Om (1 + 1 + 1))) := by
    have h := (vbTK_le_iff hl hX hKB hWD haD).1 hWa
    rwa [vbTK_OmW hl hX hKB hWK] at h
  set L := S.psi (vbTK S l K (Om (1 + 1 + 1) * (E / Om (1 + 1 + 1)))) (Om (1 + 1)) with hLdef
  have hθL : ConjT.th S ≤ L := (psi_mono hκ2 hTa).1
  have hLS : SC L := Ui.ui_psi_SC (s := 1) _
  have hdL : ConjT.th S ∣ L := by
    have h := opow_dvd_opow ω hθL
    rwa [hθe, gg_SC_eps hLS] at h
  have hωL : (ω : Ordinal.{0}) ≤ L := ((Vp.vp_omega_le_Om1.trans h1θ.le)).trans hθL
  have hsum : ConjT.th S * cdEta S l + (L + vbTK S l K (E % Om (1 + 1 + 1))) = ConjT.th S * cdEta S ξ := by
    have h : Om ω + (ConjT.th S * cdEta S l + (L + vbTK S l K (E % Om (1 + 1 + 1)))) =
        Om ω + ConjT.th S * cdEta S ξ := by
      have e1 : faG S l K E = A + 1 + L + vbTK S l K (E % Om (1 + 1 + 1)) := rfl
      have e2 : ConjT.Aη S (cdEta S ξ) = Om ω + ConjT.th S * cdEta S ξ := rfl
      rw [← e2, ← hG2, e1, add_assoc A 1 L, one_add_of_omega0_le hωL]
      show Om ω + (ConjT.th S * cdEta S l + (L + vbTK S l K (E % Om (1 + 1 + 1)))) =
        Om ω + ConjT.th S * cdEta S l + L + vbTK S l K (E % Om (1 + 1 + 1))
      rw [add_assoc (Om ω + ConjT.th S * cdEta S l) L, add_assoc (Om ω : Ordinal.{0}) (ConjT.th S * cdEta S l)]
    exact (add_left_cancel_iff).1 h
  have hTδ : ConjT.th S ∣ vbTK S l K (E % Om (1 + 1 + 1)) := by
    have h1 : ConjT.th S ∣ ConjT.th S * cdEta S l + L := dvd_add (dvd_mul_right _ _) hdL
    have h2 : ConjT.th S ∣ ConjT.th S * cdEta S l + L + vbTK S l K (E % Om (1 + 1 + 1)) := by
      rw [add_assoc, hsum]; exact dvd_mul_right _ _
    exact (Ordinal.dvd_add_iff h1).1 h2
  obtain ⟨hθ2D, hTθ2⟩ := fa_T_θ2 hl hX hKB hown hρ hWK (hWE.trans_lt hEA)
  have hδ : S.psi (Om ω) (Om (1 + 1 + 1)) ∣ E % Om (1 + 1 + 1) := by
    have h := (faT_dvd hl hX hKB hθ2D _ hδD).2 (by rw [hTθ2, hθe]; exact hTδ)
    rwa [fa_θ2_eps] at h
  refine ⟨E, hownE, hWE, ?_, rfl⟩
  rw [← Ordinal.div_add_mod E (Om (1 + 1 + 1))]
  exact dvd_add (Dvd.dvd.mul_right fa_θ2_dvd_O3 _) hδ

end Law

end Googology.Trans.PoR.InaccPsi.R2.Fa
