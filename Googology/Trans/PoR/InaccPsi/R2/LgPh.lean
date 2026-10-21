import Googology.Trans.PoR.InaccPsi.R2.LgUni
import Googology.Trans.PoR.InaccPsi.R2.LgLay

/-!
# Terms for the codes past `Γ_{Ω₁+1}` in the layers over `Γ`: `LgPoly` for `lgUSys`, `lgLL k`, `(lgLL k).iter n`

The arithmetic of `R2.PhLL` and `R2.PhVz` (`phDivCode`, `phTh_opow_mul`, `phPoly_next`, `phPoly_iter`, `phPoly_lim`,
`phTop_next`, `phTop_lim`, `phPoly_of_SC`) with the codes `LgCl` and the reading `Θ' = lgTh` of `R2.LgCl`:

* `lgPoly_U` (**`lgUSys` has terms for the codes below `Γ_{Ω₁+1}`**: below it `LgCl = GgCl` and `Θ' = Θ`), `lgU_top'`
  (`Γ(y) = Θ'_y(ω^{Γ_{Ω₁+1}})`);
* `lgPoly_next`, `lgPoly_iter`, `lgPoly_lim` (the terms pass to the next layer, every `L.iter n`, the limit layer);
* `lgLLe k = Γ_{Ω₁+1} + Ω₁·ω·k`, `lgPoly_LL` (**`lgLL k` has terms for every code below `ω^{lgLLe k}`, its top is
  `Θ'_y(ω^{lgLLe k})`**), `lgPoly_LLiter` (the same for `(lgLL k).iter n` with `ω^{lgLLe k + Ω₁·n}`).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Ph

/-- **Reduction to strongly critical `Z`.** -/
theorem lgPoly_of_SC {X : XtSys} {E : Ordinal.{0}}
    (h : ∀ Z, SC Z → Z < Om 1 → ∀ c, LgCl Z c → c < E → ∃ s : X.Tm, ∀ y, SC y → y < Om 1 → Z ≤ y →
      X.CB s y ∧ X.val s y = lgTh y c) : LgPoly X E := by
  intro Z c hc hcE
  by_cases hex : ∃ y, SC y ∧ y < Om 1 ∧ Z ≤ y
  · have hmem : sInf {y | SC y ∧ y < Om 1 ∧ Z ≤ y} ∈ {y | SC y ∧ y < Om 1 ∧ Z ≤ y} := csInf_mem hex
    obtain ⟨h1, h2, h3⟩ := hmem
    obtain ⟨s, hs⟩ := h _ h1 h2 c (hc.mono h3) hcE
    exact ⟨s, fun y hy hy1 hZy => hs y hy hy1 (csInf_le' ⟨hy, hy1, hZy⟩)⟩
  · push Not at hex
    exact ⟨X.cst 0, fun y hy hy1 hZy => absurd hZy (not_le.2 (hex y hy hy1))⟩

variable {Z y : Ordinal.{0}}

theorem lgTh_zero (y : Ordinal.{0}) : lgTh y 0 = 0 := ggOtp_zero _

theorem lg_cl_Om1_one (hZ : SC Z) : LgCl Z (Om 1 + 1) := LgCl.add LgCl.om (LgCl.small (gg_one_lt_of_SC hZ))

theorem lgTh_Om1_one (hy : SC y) (hy1 : y < Om 1) : lgTh y (Om 1 + 1) = y + 1 := by
  rw [lgTh_add hy LgCl.om, lgTh_Om1 hy hy1, lgTh_small (gg_one_lt_of_SC hy).le]

theorem lg_sub_log_lt {c : Ordinal.{0}} (hc0 : c ≠ 0) : c - ω ^ log ω c < c := by
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
theorem lg_cl_opow_mul (hy : SC y) {e : Ordinal.{0}} (he : LgCl y e) :
    ∀ g, LgCl y g → LgCl y (ω ^ e * g) := by
  intro g
  induction g using WellFoundedLT.induction with
  | ind g IH =>
  intro hg
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [mul_zero]; exact LgCl.zero hy.1
  obtain ⟨hsub, hlog⟩ := lgDec hy g hg
  have hwg := opow_log_le_self ω hg0
  have hgr := Ordinal.add_sub_cancel_of_le hwg
  rw [← hgr, mul_add, ← opow_add]
  exact LgCl.add (LgCl.opow hy.1 (LgCl.add he hlog))
    (IH _ (lg_sub_log_lt hg0) (hsub _ (LgCl.opow hy.1 hlog) hwg))

/-- **`Θ'_y(ω^e·g) = ω^{Θ'_y(e)}·Θ'_y(g)`** for codes `e`, `g` over a strongly critical `y`. -/
theorem lgTh_opow_mul (hy : SC y) {e : Ordinal.{0}} (he : LgCl y e) :
    ∀ g, LgCl y g → lgTh y (ω ^ e * g) = ω ^ lgTh y e * lgTh y g := by
  intro g
  induction g using WellFoundedLT.induction with
  | ind g IH =>
  intro hg
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [mul_zero, lgTh_zero, mul_zero]
  obtain ⟨hsub, hlog⟩ := lgDec hy g hg
  have hwg : ω ^ log ω g ≤ g := opow_log_le_self ω hg0
  have hr := hsub _ (LgCl.opow hy.1 hlog) hwg
  have hgr : ω ^ log ω g + (g - ω ^ log ω g) = g := Ordinal.add_sub_cancel_of_le hwg
  have IHr := IH _ (lg_sub_log_lt hg0) hr
  have hel : LgCl y (e + log ω g) := LgCl.add he hlog
  calc lgTh y (ω ^ e * g) = lgTh y (ω ^ (e + log ω g) + ω ^ e * (g - ω ^ log ω g)) := by
        conv_lhs => rw [← hgr]
        rw [mul_add, ← opow_add]
    _ = ω ^ lgTh y e * lgTh y g := by
        rw [lgTh_add hy (LgCl.opow hy.1 hel), lgTh_opow hy hel, IHr, lgTh_add hy he, opow_add]
        conv_rhs => rw [← hgr]
        rw [lgTh_add hy (LgCl.opow hy.1 hlog), lgTh_opow hy hlog, mul_add]

/-- **Division of a code by `ω^e`**: `c = ω^e·g + r` with codes `g`, `r` and `r < ω^e`. -/
theorem lgDivCode (hZ : SC Z) {e : Ordinal.{0}} (he : LgCl Z e) :
    ∀ c, LgCl Z c → ∃ g r, LgCl Z g ∧ LgCl Z r ∧ r < ω ^ e ∧ c = ω ^ e * g + r := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc
  rcases eq_or_ne c 0 with rfl | hc0
  · exact ⟨0, 0, LgCl.zero hZ.1, LgCl.zero hZ.1, opow_pos _ omega0_pos, by rw [mul_zero, add_zero]⟩
  obtain ⟨hsub, hlog⟩ := lgDec hZ c hc
  rcases lt_or_ge (log ω c) e with hL | hL
  · refine ⟨0, c, LgCl.zero hZ.1, hc, ?_, by rw [mul_zero, zero_add]⟩
    exact (lt_opow_succ_log_self one_lt_omega0 c).trans_le
      (opow_le_opow_right omega0_pos (Order.succ_le_of_lt hL))
  · have hwc : ω ^ log ω c ≤ c := opow_log_le_self ω hc0
    have hr := hsub _ (LgCl.opow hZ.1 hlog) hwc
    obtain ⟨g', r', hg', hr', hr'e, e'⟩ := IH _ (lg_sub_log_lt hc0) hr
    have hcr : ω ^ log ω c + (c - ω ^ log ω c) = c := Ordinal.add_sub_cancel_of_le hwc
    have hLe := (lgDec hZ _ hlog).1 e he hL
    refine ⟨ω ^ (log ω c - e) + g', r', LgCl.add (LgCl.opow hZ.1 hLe) hg', hr', hr'e, ?_⟩
    rw [mul_add, ← opow_add, Ordinal.add_sub_cancel_of_le hL, add_assoc, ← e', hcr]

/-! ## The next layer -/

theorem lgTh_Om1_opow (hy : SC y) (hy1 : y < Om 1) : lgTh y (ω ^ Om 1) = y := by
  rw [Om1_opow, lgTh_Om1 hy hy1]

theorem lg_cl_Om1_mul_omega (hZ : SC Z) : LgCl Z (Om 1 * ω) := by
  have e : Om (1 : Ordinal.{0}) * ω = ω ^ (Om 1 + 1) := by rw [opow_add, opow_one, Om1_opow]
  rw [e]; exact LgCl.opow hZ.1 (lg_cl_Om1_one hZ)

theorem lgTh_Om1_mul_omega (hy : SC y) (hy1 : y < Om 1) : lgTh y (Om 1 * ω) = y * ω := by
  have e : Om (1 : Ordinal.{0}) * ω = ω ^ (Om 1 + 1) := by rw [opow_add, opow_one, Om1_opow]
  rw [e, lgTh_opow hy (lg_cl_Om1_one hy), lgTh_Om1_one hy hy1, opow_add, opow_one, gg_SC_eps hy]

/-- **The next layer has terms for every code below `ω^{e + Ω₁}`.** -/
theorem lgPoly_next (L : XtLay) {e : Ordinal.{0}} (he : ∀ Z, SC Z → LgCl Z e)
    (htop : ∀ y, SC y → y < Om 1 → L.sys.top y = lgTh y (ω ^ e)) (hP : LgPoly L.sys (ω ^ e)) :
    LgPoly L.xtNext.sys (ω ^ (e + Om 1)) := by
  refine lgPoly_of_SC fun Z hZ _ c hc hcE => ?_
  obtain ⟨g, r, hg, hr, hre, hcgr⟩ := lgDivCode hZ (he Z hZ) c hc
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
  show L.sys.top y * g + L.sys.val s y = lgTh y c
  have hey := he y hy
  have hgy := hg.mono hZy
  rw [h2, htop y hy hy1, hcgr, lgTh_add hy (lg_cl_opow_mul hy hey g hgy), lgTh_opow_mul hy hey g hgy,
    lgTh_opow hy hey, lgTh_small (hgZ.le.trans hZy)]

theorem lg_cl_opow (hZ : SC Z) {e : Ordinal.{0}} (he : LgCl Z e) : LgCl Z (ω ^ e) := LgCl.opow hZ.1 he

/-- The top of the next layer: `T(y)·y = Θ'_y(ω^{e + Ω₁})`. -/
theorem lgTop_next (L : XtLay) {e : Ordinal.{0}} (he : ∀ Z, SC Z → LgCl Z e)
    (htop : ∀ y, SC y → y < Om 1 → L.sys.top y = lgTh y (ω ^ e)) :
    ∀ y, SC y → y < Om 1 → L.xtNext.sys.top y = lgTh y (ω ^ (e + Om 1)) := by
  intro y hy hy1
  show L.sys.top y * y = _
  rw [htop y hy hy1, lgTh_opow hy (LgCl.add (he y hy) LgCl.om), lgTh_add hy (he y hy), lgTh_Om1 hy hy1,
    opow_add, lgTh_opow hy (he y hy), gg_SC_eps hy]

/-- **The layers `L.iter n`**: terms for the codes below `ω^{e + Ω₁·n}`, top `Θ'_y(ω^{e + Ω₁·n})`. -/
theorem lgPoly_iter (L : XtLay) {e : Ordinal.{0}} (he : ∀ Z, SC Z → LgCl Z e)
    (htop : ∀ y, SC y → y < Om 1 → L.sys.top y = lgTh y (ω ^ e)) (hP : LgPoly L.sys (ω ^ e)) :
    ∀ n : ℕ, LgPoly (L.iter n).sys (ω ^ (e + Om 1 * n)) ∧
      ∀ y, SC y → y < Om 1 → (L.iter n).sys.top y = lgTh y (ω ^ (e + Om 1 * n)) := by
  have hen : ∀ n : ℕ, ∀ Z, SC Z → LgCl Z (e + Om 1 * n) := fun n Z hZ =>
    LgCl.add (he Z hZ) (LgCl.mul_nat hZ.1 LgCl.om n)
  intro n
  induction n with
  | zero => simp only [Nat.cast_zero, mul_zero, add_zero]; exact ⟨hP, htop⟩
  | succ n ih =>
    have e1 : e + Om 1 * ((n + 1 : ℕ) : Ordinal.{0}) = e + Om 1 * n + Om 1 := by
      rw [Nat.cast_succ, mul_add_one, add_assoc]
    rw [e1]
    exact ⟨lgPoly_next (L.iter n) (hen n) ih.2 ih.1, lgTop_next (L.iter n) (hen n) ih.2⟩

/-- **The limit layer has terms for every code below `ω^{e + Ω₁·ω}`.** -/
theorem lgPoly_lim (L : XtLay) {e : Ordinal.{0}} (he : ∀ Z, SC Z → LgCl Z e)
    (htop : ∀ y, SC y → y < Om 1 → L.sys.top y = lgTh y (ω ^ e)) (hP : LgPoly L.sys (ω ^ e)) :
    LgPoly L.xtLim.sys (ω ^ (e + Om 1 * ω)) := by
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
  obtain ⟨s, hs⟩ := (lgPoly_iter L he htop hP n).1 Z c hc hcn
  exact ⟨⟨n, s⟩, fun y hy hy1 hZy => hs y hy hy1 hZy⟩

/-- The top of the limit layer: `T(y)·y^ω = Θ'_y(ω^{e + Ω₁·ω})`. -/
theorem lgTop_lim (L : XtLay) {e : Ordinal.{0}} (he : ∀ Z, SC Z → LgCl Z e)
    (htop : ∀ y, SC y → y < Om 1 → L.sys.top y = lgTh y (ω ^ e)) :
    ∀ y, SC y → y < Om 1 → L.xtLim.sys.top y = lgTh y (ω ^ (e + Om 1 * ω)) := by
  intro y hy hy1
  show L.sys.top y * y ^ ω = _
  rw [htop y hy hy1, lgTh_opow hy (LgCl.add (he y hy) (lg_cl_Om1_mul_omega hy)), lgTh_add hy (he y hy),
    lgTh_Om1_mul_omega hy hy1, opow_add, lgTh_opow hy (he y hy), opow_mul, gg_SC_eps hy]

/-! ## The layers over `Γ` -/

/-- **`lgUSys` has terms for every code below `Γ_{Ω₁+1}`.** -/
theorem lgPoly_U : LgPoly lgUSys ggGam := by
  intro Z c hc hcE
  obtain ⟨s, hs⟩ := lgUPoly Z c (lgCl_lt_Gam hc hcE) hcE
  exact ⟨s, fun y hy hy1 hZy => ⟨(hs y hy hy1 hZy).1, by rw [(hs y hy hy1 hZy).2, lgTh_eq_ggTh hcE.le]⟩⟩

/-- The exponent `Γ_{Ω₁+1} + Ω₁·ω·k` of the code of the top `Γ(x)·x^{ω·k}` of `lgLL k`. -/
noncomputable def lgLLe (k : ℕ) : Ordinal.{0} := ggGam + Om 1 * ω * k

theorem lg_cl_LLe (k : ℕ) (hZ : SC Z) : LgCl Z (lgLLe k) :=
  LgCl.add LgCl.gam (LgCl.mul_nat hZ.1 (lg_cl_Om1_mul_omega hZ) k)

/-- **`lgLL k` has terms for every code below `ω^{lgLLe k}`, and its top is `Θ'_y(ω^{lgLLe k})`.** -/
theorem lgPoly_LL : ∀ k : ℕ, LgPoly (lgLL k).sys (ω ^ lgLLe k) ∧
    ∀ y, SC y → y < Om 1 → (lgLL k).sys.top y = lgTh y (ω ^ lgLLe k)
  | 0 => by
    have e0 : lgLLe 0 = ggGam := by rw [lgLLe, Nat.cast_zero, mul_zero, add_zero]
    rw [e0, lg_Gam_eps]
    exact ⟨lgPoly_U, fun y hy hy1 => (lgTh_Gam hy hy1).symm⟩
  | k + 1 => by
    have e1 : lgLLe (k + 1) = lgLLe k + Om 1 * ω := by
      rw [lgLLe, lgLLe, Nat.cast_succ, mul_add_one, add_assoc]
    rw [e1]
    obtain ⟨hP, ht⟩ := lgPoly_LL k
    exact ⟨lgPoly_lim (lgLL k) (fun _ hZ => lg_cl_LLe k hZ) ht hP,
      lgTop_lim (lgLL k) (fun _ hZ => lg_cl_LLe k hZ) ht⟩

/-- **`(lgLL k).iter n` has terms for every code below `ω^{lgLLe k + Ω₁·n}`.** -/
theorem lgPoly_LLiter (k n : ℕ) : LgPoly ((lgLL k).iter n).sys (ω ^ (lgLLe k + Om 1 * n)) ∧
    ∀ y, SC y → y < Om 1 → ((lgLL k).iter n).sys.top y = lgTh y (ω ^ (lgLLe k + Om 1 * n)) :=
  lgPoly_iter (lgLL k) (fun _ hZ => lg_cl_LLe k hZ) (lgPoly_LL k).2 (lgPoly_LL k).1 n

end Googology.Trans.PoR.InaccPsi.R2
