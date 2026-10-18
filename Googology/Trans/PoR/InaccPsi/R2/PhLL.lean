import Googology.Trans.PoR.InaccPsi.R2.PhVz
import Googology.Trans.PoR.InaccPsi.R2.XtW2

/-!
# The layers: terms for every code below the code of the top

A layer `L` (`R2.XtLay`) with top `T(x)` and a code `ω^e` of the top (`Θ_y(ω^e) = T(y)` at every strongly critical
`y < Ω₁`) that has terms for the codes below `ω^e`:

* `phTh_opow_mul` (**`Θ_y(ω^e·g) = ω^{Θ_y(e)}·Θ_y(g)`** for codes `e`, `g`), `phDivCode` (**division of a code by
  `ω^e`**: `c = ω^e·g + r` with codes `g`, `r`, `r < ω^e`);
* `phPoly_next` (**the next layer `T(x)·γ + s(x)` has terms for the codes below `ω^{e + Ω₁}`**: `c = ω^e·g + r`
  with the constant `g < Ω₁` and the term of `r`), `phTop_next`;
* `phPoly_iter` (`L.iter n`, codes below `ω^{e + Ω₁·n}`), `phPoly_lim` (**the limit layer has terms for the codes
  below `ω^{e + Ω₁·ω}`**), `phTop_lim`;
* `phLLe k = phB + Ω₁·ω·k`, `phPoly_LL` (**`xtLL k` has terms for every code below `ω^{phB + Ω₁·ω·k}`, the code
  of `B(x)·x^{ω·k}`**), `phTop_LL` (`Θ_y(ω^{phLLe k}) = top_{LL k}(y)`), `phPoly_LLiter`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ph

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Bt

variable {Z y : Ordinal.{0}}

theorem ph_sub_log_lt {c : Ordinal.{0}} (hc0 : c ≠ 0) : c - ω ^ log ω c < c := by
  have hwc : ω ^ log ω c ≤ c := opow_log_le_self ω hc0
  have hcr : ω ^ log ω c + (c - ω ^ log ω c) = c := Ordinal.add_sub_cancel_of_le hwc
  rcases (Ordinal.sub_le_self c (ω ^ log ω c)).lt_or_eq with h | h
  · exact h
  · exfalso
    have h1 : ω ^ log ω c + c = c := by conv_rhs => rw [← hcr]
                                        rw [h]
    have h2 := add_eq_right_iff_mul_omega0_le.1 h1
    rw [← opow_succ] at h2
    exact absurd (lt_opow_succ_log_self one_lt_omega0 c) (not_lt.2 h2)

/-- The codes are closed under `g ↦ ω^e·g`. -/
theorem ph_cl_opow_mul (hy : SC y) {e : Ordinal.{0}} (he : GgCl y e) :
    ∀ g, GgCl y g → GgCl y (ω ^ e * g) := by
  intro g
  induction g using WellFoundedLT.induction with
  | ind g IH =>
  intro hg
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [mul_zero]; exact GgCl.zero hy.1
  obtain ⟨hsub, hlog⟩ := ggDec hy g hg
  have hwg := opow_log_le_self ω hg0
  have hgr := Ordinal.add_sub_cancel_of_le hwg
  rw [← hgr, mul_add, ← opow_add]
  exact GgCl.add (GgCl.opow hy.1 (GgCl.add he hlog))
    (IH _ (ph_sub_log_lt hg0) (hsub _ (GgCl.opow hy.1 hlog) hwg))

/-- **`Θ_y(ω^e·g) = ω^{Θ_y(e)}·Θ_y(g)`** for codes `e`, `g` over a strongly critical `y`. -/
theorem phTh_opow_mul (hy : SC y) {e : Ordinal.{0}} (he : GgCl y e) :
    ∀ g, GgCl y g → ggTh y (ω ^ e * g) = ω ^ ggTh y e * ggTh y g := by
  intro g
  induction g using WellFoundedLT.induction with
  | ind g IH =>
  intro hg
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [mul_zero, phTh_zero, mul_zero]
  obtain ⟨hsub, hlog⟩ := ggDec hy g hg
  have hwg : ω ^ log ω g ≤ g := opow_log_le_self ω hg0
  have hr := hsub _ (GgCl.opow hy.1 hlog) hwg
  have hgr : ω ^ log ω g + (g - ω ^ log ω g) = g := Ordinal.add_sub_cancel_of_le hwg
  have IHr := IH _ (ph_sub_log_lt hg0) hr
  have hel : GgCl y (e + log ω g) := GgCl.add he hlog
  calc ggTh y (ω ^ e * g) = ggTh y (ω ^ (e + log ω g) + ω ^ e * (g - ω ^ log ω g)) := by
        conv_lhs => rw [← hgr]
        rw [mul_add, ← opow_add]
    _ = ω ^ ggTh y e * ggTh y g := by
        rw [ggTh_add hy (GgCl.opow hy.1 hel), ggTh_opow hy hel, IHr, ggTh_add hy he, opow_add]
        conv_rhs => rw [← hgr]
        rw [ggTh_add hy (GgCl.opow hy.1 hlog), ggTh_opow hy hlog, mul_add]

/-- **Division of a code by `ω^e`**: `c = ω^e·g + r` with codes `g`, `r` and `r < ω^e`. -/
theorem phDivCode (hZ : SC Z) {e : Ordinal.{0}} (he : GgCl Z e) :
    ∀ c, GgCl Z c → ∃ g r, GgCl Z g ∧ GgCl Z r ∧ r < ω ^ e ∧ c = ω ^ e * g + r := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc
  rcases eq_or_ne c 0 with rfl | hc0
  · exact ⟨0, 0, GgCl.zero hZ.1, GgCl.zero hZ.1, opow_pos _ omega0_pos, by rw [mul_zero, add_zero]⟩
  obtain ⟨hsub, hlog⟩ := ggDec hZ c hc
  rcases lt_or_ge (log ω c) e with hL | hL
  · refine ⟨0, c, GgCl.zero hZ.1, hc, ?_, by rw [mul_zero, zero_add]⟩
    exact (lt_opow_succ_log_self one_lt_omega0 c).trans_le
      (opow_le_opow_right omega0_pos (Order.succ_le_of_lt hL))
  · have hwc : ω ^ log ω c ≤ c := opow_log_le_self ω hc0
    have hr := hsub _ (GgCl.opow hZ.1 hlog) hwc
    obtain ⟨g', r', hg', hr', hr'e, e'⟩ := IH _ (ph_sub_log_lt hc0) hr
    have hcr : ω ^ log ω c + (c - ω ^ log ω c) = c := Ordinal.add_sub_cancel_of_le hwc
    have hLe := (ggDec hZ _ hlog).1 e he hL
    refine ⟨ω ^ (log ω c - e) + g', r', GgCl.add (GgCl.opow hZ.1 hLe) hg', hr', hr'e, ?_⟩
    rw [mul_add, ← opow_add, Ordinal.add_sub_cancel_of_le hL, add_assoc, ← e', hcr]

/-! ## The next layer -/

theorem phTh_Om1_opow (hy : SC y) (hy1 : y < Om 1) : ggTh y (ω ^ Om 1) = y := by
  rw [Om1_opow, ggTh_Om1 hy hy1]

theorem ph_cl_Om1_mul_omega (hZ : SC Z) : GgCl Z (Om 1 * ω) := by
  have e : Om (1 : Ordinal.{0}) * ω = ω ^ (Om 1 + 1) := by rw [opow_add, opow_one, Om1_opow]
  rw [e]; exact GgCl.opow hZ.1 (ph_cl_Om1_one hZ)

theorem phTh_Om1_mul_omega (hy : SC y) (hy1 : y < Om 1) : ggTh y (Om 1 * ω) = y * ω := by
  have e : Om (1 : Ordinal.{0}) * ω = ω ^ (Om 1 + 1) := by rw [opow_add, opow_one, Om1_opow]
  rw [e, ggTh_opow hy (ph_cl_Om1_one hy), phTh_Om1_one hy hy1, opow_add, opow_one, gg_SC_eps hy]

/-- **The next layer has terms for every code below `ω^{e + Ω₁}`.** -/
theorem phPoly_next (L : XtLay) {e : Ordinal.{0}} (he : ∀ Z, SC Z → GgCl Z e)
    (htop : ∀ y, SC y → y < Om 1 → L.sys.top y = ggTh y (ω ^ e)) (hP : GgPoly L.sys (ω ^ e)) :
    GgPoly L.xtNext.sys (ω ^ (e + Om 1)) := by
  refine phPoly_of_SC fun Z hZ _ c hc hcE => ?_
  obtain ⟨g, r, hg, hr, hre, hcgr⟩ := phDivCode hZ (he Z hZ) c hc
  have hg1 : g < Om 1 := by
    have h1 : ω ^ e * g < ω ^ e * Om 1 := by
      calc ω ^ e * g ≤ c := by rw [hcgr]; exact le_self_add
        _ < ω ^ (e + Om 1) := hcE
        _ = ω ^ e * Om 1 := by rw [opow_add, Om1_opow]
    exact (mul_lt_mul_iff_right₀ (opow_pos _ omega0_pos)).1 h1
  have hgZ : g < Z := hg.lt_of_lt_Om1 hZ hg1
  obtain ⟨s, hs⟩ := hP Z r hr hre
  refine ⟨(g, s), fun y hy hy1 hZy => ?_⟩
  obtain ⟨h1, h2⟩ := hs y hy hy1 hZy
  refine ⟨⟨lt_of_lt_of_le hgZ hZy, h1⟩, ?_⟩
  show L.sys.top y * g + L.sys.val s y = ggTh y c
  have hey := he y hy
  have hgy := hg.mono hZy
  rw [h2, htop y hy hy1, hcgr, ggTh_add hy (ph_cl_opow_mul hy hey g hgy), phTh_opow_mul hy hey g hgy,
    ggTh_opow hy hey, ggTh_small (hgZ.le.trans hZy)]

theorem ph_cl_opow (hZ : SC Z) {e : Ordinal.{0}} (he : GgCl Z e) : GgCl Z (ω ^ e) := GgCl.opow hZ.1 he

/-- The top of the next layer: `T(y)·y = Θ_y(ω^{e + Ω₁})`. -/
theorem phTop_next (L : XtLay) {e : Ordinal.{0}} (he : ∀ Z, SC Z → GgCl Z e)
    (htop : ∀ y, SC y → y < Om 1 → L.sys.top y = ggTh y (ω ^ e)) :
    ∀ y, SC y → y < Om 1 → L.xtNext.sys.top y = ggTh y (ω ^ (e + Om 1)) := by
  intro y hy hy1
  show L.sys.top y * y = _
  rw [htop y hy hy1, ggTh_opow hy (GgCl.add (he y hy) GgCl.om), ggTh_add hy (he y hy), ggTh_Om1 hy hy1,
    opow_add, ggTh_opow hy (he y hy), gg_SC_eps hy]

/-- **The layers `L.iter n`**: terms for the codes below `ω^{e + Ω₁·n}`, top `Θ_y(ω^{e + Ω₁·n})`. -/
theorem phPoly_iter (L : XtLay) {e : Ordinal.{0}} (he : ∀ Z, SC Z → GgCl Z e)
    (htop : ∀ y, SC y → y < Om 1 → L.sys.top y = ggTh y (ω ^ e)) (hP : GgPoly L.sys (ω ^ e)) :
    ∀ n : ℕ, GgPoly (L.iter n).sys (ω ^ (e + Om 1 * n)) ∧
      ∀ y, SC y → y < Om 1 → (L.iter n).sys.top y = ggTh y (ω ^ (e + Om 1 * n)) := by
  have hen : ∀ n : ℕ, ∀ Z, SC Z → GgCl Z (e + Om 1 * n) := fun n Z hZ =>
    GgCl.add (he Z hZ) (GgCl.mul_nat hZ.1 GgCl.om n)
  intro n
  induction n with
  | zero => simp only [Nat.cast_zero, mul_zero, add_zero]; exact ⟨hP, htop⟩
  | succ n ih =>
    have e1 : e + Om 1 * ((n + 1 : ℕ) : Ordinal.{0}) = e + Om 1 * n + Om 1 := by
      rw [Nat.cast_succ, mul_add_one, add_assoc]
    rw [e1]
    exact ⟨phPoly_next (L.iter n) (hen n) ih.2 ih.1, phTop_next (L.iter n) (hen n) ih.2⟩

/-- **The limit layer has terms for every code below `ω^{e + Ω₁·ω}`.** -/
theorem phPoly_lim (L : XtLay) {e : Ordinal.{0}} (he : ∀ Z, SC Z → GgCl Z e)
    (htop : ∀ y, SC y → y < Om 1 → L.sys.top y = ggTh y (ω ^ e)) (hP : GgPoly L.sys (ω ^ e)) :
    GgPoly L.xtLim.sys (ω ^ (e + Om 1 * ω)) := by
  intro Z c hc hcE
  have hn : ∃ n : ℕ, c < ω ^ (e + Om 1 * n) := by
    rcases eq_or_ne c 0 with rfl | hc0
    · exact ⟨0, opow_pos _ omega0_pos⟩
    have hL : log ω c < e + Om 1 * ω := (lt_opow_iff_log_lt one_lt_omega0 hc0).1 hcE
    have hm : ∃ n : ℕ, log ω c < e + Om 1 * n := by
      rcases lt_or_ge (log ω c) e with h | h
      · exact ⟨0, by rw [Nat.cast_zero, mul_zero, add_zero]; exact h⟩
      · obtain ⟨t, ht⟩ := exists_add_of_le h
        rw [ht] at hL
        have ht' : t < Om 1 * ω := (add_lt_add_iff_left _).1 hL
        obtain ⟨m, hm, htm⟩ := (lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 ht'
        obtain ⟨n, rfl⟩ := lt_omega0.1 hm
        exact ⟨n, by rw [ht]; exact (add_lt_add_iff_left _).2 htm⟩
    obtain ⟨n, hn⟩ := hm
    exact ⟨n, (lt_opow_succ_log_self one_lt_omega0 c).trans_le
      (opow_le_opow_right omega0_pos (Order.succ_le_of_lt hn))⟩
  obtain ⟨n, hcn⟩ := hn
  obtain ⟨s, hs⟩ := (phPoly_iter L he htop hP n).1 Z c hc hcn
  exact ⟨⟨n, s⟩, fun y hy hy1 hZy => hs y hy hy1 hZy⟩

/-- The top of the limit layer: `T(y)·y^ω = Θ_y(ω^{e + Ω₁·ω})`. -/
theorem phTop_lim (L : XtLay) {e : Ordinal.{0}} (he : ∀ Z, SC Z → GgCl Z e)
    (htop : ∀ y, SC y → y < Om 1 → L.sys.top y = ggTh y (ω ^ e)) :
    ∀ y, SC y → y < Om 1 → L.xtLim.sys.top y = ggTh y (ω ^ (e + Om 1 * ω)) := by
  intro y hy hy1
  show L.sys.top y * y ^ ω = _
  rw [htop y hy hy1, ggTh_opow hy (GgCl.add (he y hy) (ph_cl_Om1_mul_omega hy)), ggTh_add hy (he y hy),
    phTh_Om1_mul_omega hy hy1, opow_add, ggTh_opow hy (he y hy), opow_mul, gg_SC_eps hy]

/-! ## The limit layers `xtLL k` -/

/-- The exponent `phB + Ω₁·ω·k` of the code of the top `B(x)·x^{ω·k}` of `xtLL k`. -/
noncomputable def phLLe (k : ℕ) : Ordinal.{0} := phB + Om 1 * ω * k

theorem ph_cl_LLe (k : ℕ) (hZ : SC Z) : GgCl Z (phLLe k) :=
  GgCl.add (ph_cl_B hZ) (GgCl.mul_nat hZ.1 (ph_cl_Om1_mul_omega hZ) k)

theorem ph_B_eps : ω ^ phB = phB := gg_veblen_eps omega0_ne_zero

/-- **`xtLL k` has terms for every code below `ω^{phLLe k}`, and its top is `Θ_y(ω^{phLLe k})`.** -/
theorem phPoly_LL : ∀ k : ℕ, GgPoly (xtLL k).sys (ω ^ phLLe k) ∧
    ∀ y, SC y → y < Om 1 → (xtLL k).sys.top y = ggTh y (ω ^ phLLe k)
  | 0 => by
    have e0 : phLLe 0 = phB := by rw [phLLe, Nat.cast_zero, mul_zero, add_zero]
    rw [e0, ph_B_eps]
    exact ⟨phPoly_vz, fun y hy hy1 => (phTh_B hy hy1).symm⟩
  | k + 1 => by
    have e1 : phLLe (k + 1) = phLLe k + Om 1 * ω := by
      rw [phLLe, phLLe, Nat.cast_succ, mul_add_one, add_assoc]
    rw [e1]
    obtain ⟨hP, ht⟩ := phPoly_LL k
    exact ⟨phPoly_lim (xtLL k) (fun _ hZ => ph_cl_LLe k hZ) ht hP,
      phTop_lim (xtLL k) (fun _ hZ => ph_cl_LLe k hZ) ht⟩

/-- **`(xtLL k).iter n` has terms for every code below `ω^{phLLe k + Ω₁·n}`.** -/
theorem phPoly_LLiter (k n : ℕ) : GgPoly ((xtLL k).iter n).sys (ω ^ (phLLe k + Om 1 * n)) ∧
    ∀ y, SC y → y < Om 1 → ((xtLL k).iter n).sys.top y = ggTh y (ω ^ (phLLe k + Om 1 * n)) :=
  phPoly_iter (xtLL k) (fun _ hZ => ph_cl_LLe k hZ) (phPoly_LL k).2 (phPoly_LL k).1 n

end Googology.Trans.PoR.InaccPsi.R2.Ph
