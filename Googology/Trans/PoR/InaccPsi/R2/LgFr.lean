import Googology.Trans.PoR.InaccPsi.R2.LgImg
import Googology.Trans.PoR.InaccPsi.R2.LgLoc

/-!
# The first limit of frontiers of `lgUSys`: `Λ⁺(lgUSys) = ι(Γ_{Ω₁+1}·ω)`

The top code of `lgUSys` is `Γ_{Ω₁+1} = ggGam` itself (`lg_ggTh_Gam`), the first code that `R2.FpLoc` and `Ph.phFrGen`
do not take (they ask `T < ggGam`).  Here:

* `lg_Gam_psi` (**`ψ_{Ω₂}(0) = Γ_{Ω₁+1}`**: every member of `Cl(0, Γ_{Ω₁+1})` below `Ω₂` is below `Γ_{Ω₁+1}`),
  `lg_Gam_mem` (`Γ_{Ω₁+1}` lies in every hull `Cl(a, b)` with `a > 0`), `lg_good_mul` (`Γ_{Ω₁+1}·k`, `Γ_{Ω₁+1}·ω`
  are good names);
* `lgFr_exp`, `lgFr_mul`, `lgB1_ge`: `Fp.fpFr_exp`, `Fp.fpFr_mul`, `Fp.fpB1_ge` for a top code `T ≤ ggGam` (THEOREM
  UNI takes `E ≤ ggGam`);
* `lgFrPt` (**`ι(Γ_{Ω₁+1}·(n+1))` is a named fixed point and a frontier of `lgUSys`**, by THEOREM UNI with `E =
  Γ_{Ω₁+1}`), `lgU_B1_eq` (**`Λ⁺(lgUSys) = ι(Γ_{Ω₁+1}·ω)`**), `lgU_B1_ups` (**`ρ_{Λ⁺(lgUSys)} = P(Γ_{Ω₁+1}·ω) <
  L(0)`**).

No new axiom beyond `R2.CitedLg` (through `R2.LgImg`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Cp

variable {S : InaccSeq.{0}}

theorem lg_two_lt_Om1 : (1 + 1 : Ordinal.{0}) < Om 1 :=
  ph_SC_Om1.isPrincipal (gg_one_lt_of_SC ph_SC_Om1) (gg_one_lt_of_SC ph_SC_Om1)

/-- **`ψ_{Ω₂}(0) = Γ_{Ω₁+1}`.** -/
theorem lg_Gam_psi (S : InaccSeq.{0}) : S.psi 0 (Om (1 + 1)) = ggGam := by
  refine le_antisymm (psi_le_of_good (CSet.Om_mem (CSet.add_mem (CSet.one_mem _ _) (CSet.one_mem _ _)))
    ?_) (ggGam_le (SC_psi (InR_Om_succ 1) 0) (psiS_bounds (S := S) 0 1).1)
  intro x hx
  induction hx with
  | small h => exact fun _ => h
  | zero => exact fun _ => ggGam_spec.1.1
  | inacc n =>
    intro h
    have h1 : Om (1 + 1 : Ordinal.{0}) < Om (S.I n) :=
      Om_lt_Om.2 (lg_two_lt_Om1.trans_le (Low.Om_one_le_I n))
    rw [S.fix n] at h1
    exact absurd h (not_lt.2 h1.le)
  | inaccW =>
    intro h
    have h1 : Om (1 + 1 : Ordinal.{0}) < Om (S.I 0) :=
      Om_lt_Om.2 (lg_two_lt_Om1.trans_le (Low.Om_one_le_I 0))
    rw [S.fix 0] at h1
    exact absurd h (not_lt.2 (h1.le.trans (S.I_le_Iw 0)))
  | @add x y _ _ ihx ihy =>
    intro h
    exact ggGam_spec.1.isPrincipal (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y _ _ ihx ihy =>
    intro h
    exact ggGam_spec.1.2 _ (ihx (lt_of_le_of_lt (left_le_veblen x y) h)) _
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h))
  | @om x _ _ =>
    intro h
    have h2 : x < 1 + 1 := Om_lt_Om.1 h
    rcases (Order.lt_add_one_iff.1 h2).lt_or_eq with h0 | h1
    · rw [Order.lt_one_iff] at h0; rw [h0, Om_zero]; exact ggGam_spec.1.1
    · rw [h1]; exact ggGam_spec.2
  | @coll π e _ _ _ _ _ => exact absurd (Set.mem_Iio.1 e.2) (not_lt.2 zero_le)

theorem lg_Gam_mem {a b : Ordinal.{0}} (ha : 0 < a) : ggGam ∈ S.CSet a b := by
  rw [← lg_Gam_psi S]
  exact CSet.psi_mem ha (InR_Om_succ 1) (CSet.Om_mem (CSet.add_mem (CSet.one_mem _ _) (CSet.one_mem _ _)))
    (CSet.zero_mem _ _)

theorem lg_cset_mul_nat {a b x : Ordinal.{0}} (hx : x ∈ S.CSet a b) : ∀ n : ℕ, x * n ∈ S.CSet a b
  | 0 => by rw [Nat.cast_zero, mul_zero]; exact CSet.zero_mem _ _
  | n + 1 => by rw [Nat.cast_succ, mul_add_one]; exact CSet.add_mem (lg_cset_mul_nat hx n) hx

theorem lg_Gam_eps : ω ^ ggGam = ggGam := Low.opow_eq_self_of_SC ggGam_spec.1

theorem lg_good_mul (n : ℕ) : Bt.Good S (ω ^ ggGam * ((n : Ordinal.{0}) + 1)) := by
  rw [lg_Gam_eps, ← Nat.cast_succ]
  exact lg_cset_mul_nat (lg_Gam_mem (lt_of_le_of_lt zero_le (lt_add_one _))) (n + 1)

theorem lg_good_mul_w : Bt.Good S (ω ^ ggGam * ω) := by
  rw [show ω ^ ggGam * ω = veblen 0 (ggGam + 1) by rw [veblen_zero_apply, opow_add, opow_one]]
  exact CSet.phi_mem (CSet.zero_mem _ _) (CSet.succ_mem (lg_Gam_mem (lt_of_le_of_lt zero_le (lt_add_one _))))

/-! ## The frontier lemmas of `R2.FpLoc` for a top code `T ≤ ggGam` -/

section Gen

variable {X : XtSys} {T : Ordinal.{0}} (hT : T ≤ ggGam) (hP : GgPoly X T)
  (htop : ∀ y, SC y → y < Om 1 → X.top y = ggTh y T)
include hT hP htop

/-- **A named frontier has `e(η_λ) ≥ T`** (`T ≤ ggGam`). -/
theorem lgFr_exp {l ηx : Ordinal.{0}} (hl : XtFr X l) (hfix : upsilon l = l) (hX : upsilon l < Pv S ηx) :
    T ≤ cdExp (cdEta S l) := by
  by_contra h
  push Not at h
  have hO := ggUni hT hP l ηx hl.1 hfix hX h.le
  have hSC := ggSC_fix hl.1 hfix hX
  have hl1 : l < Om 1 := Fx.fx_fix_lt_Om1 hfix hX
  have h2 := ggTh_lt (ggExpMem hl.1 hfix hX (h.trans_le hT)) h
  have h3 := hl.2
  rw [hO, hfix, htop l hSC hl1] at h3
  exact absurd h3 h2.ne

/-- **Every frontier `λ ∈ (ω², ι(ω^T·ω))` is `ι(ω^T·k)`.** -/
theorem lgFr_mul (htopE : ∀ x, InE x → x < Om1 → eN x < X.top x) {l : Ordinal.{0}} (hl : XtFr X l)
    (hww : ω * ω < l) (hlt : l < iota S (ω ^ T * ω)) (hl1 : l < Om1) :
    ∃ k : ℕ, l = iota S (ω ^ T * (k : Ordinal.{0})) := by
  have hfix := ggFr_fix htopE hl hl1 hww
  have hX : upsilon l < Pv S (ω ^ T * ω) := by
    have h := upsilon_normal.strictMono hlt
    rw [ups_iota S] at h
    exact h
  have he := lgFr_exp (S := S) hT hP htop hl hfix hX
  obtain ⟨-, hι, hηlt, -⟩ := cdEta_pv_spec (S := S) hl.1.1 hX
  obtain ⟨η0, hdec, hd⟩ := cdExp_decomp (gg_name_ne hl.1 hfix hX)
  have hT1 : ω ^ T ∣ ω ^ cdExp (cdEta S l) := opow_dvd_opow ω he
  have hdv : ω ^ T ∣ cdEta S l := by rw [hdec]; exact dvd_add (hT1.trans hd) hT1
  obtain ⟨q, hq⟩ := hdv
  have hqw : q < ω := by
    rw [hq] at hηlt
    exact (mul_lt_mul_iff_right₀ (opow_pos _ omega0_pos)).1 hηlt
  obtain ⟨k, rfl⟩ := lt_omega0.1 hqw
  exact ⟨k, by rw [← hι, hq]⟩

/-- **`ι(ω^T·ω) ≤ Λ⁺(X)`** (`T ≤ ggGam`). -/
theorem lgB1_ge (hTO : Om 1 ≤ T) (htopE : ∀ x, InE x → x < Om1 → eN x < X.top x) (hPk : XtTopPkg X) :
    iota S (ω ^ T * ω) ≤ xtB1 X := by
  classical
  by_contra hlt
  push Not at hlt
  obtain ⟨h0, hcof⟩ := xtB1_spec hPk
  have hb1 : xtB1 X < Om1 := xtB1_lt_Om1 hPk
  obtain ⟨μ1, hμ1, -, hμ1B⟩ := hcof 0 h0
  have hww1 : ω * ω ≤ μ1 := by
    obtain ⟨q, hq⟩ := (ri_iff.1 hμ1.1).2
    rw [hq]
    have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hq; exact (ri_iff.1 hμ1.1).1 hq
    exact le_mul_left _ (pos_iff_ne_zero.2 hq0)
  have hT0 : T ≠ 0 := (lt_of_lt_of_le (zero_lt_one.trans (gg_one_lt_of_SC ph_SC_Om1)) hTO).ne'
  have hwlim : IsSuccLimit (ω ^ T * ω) := by
    have e : ω ^ T * ω = ω ^ (T + 1) := by rw [opow_add, opow_one]
    rw [e]; exact ph_opow_lim (by simp)
  have hlt' := hlt
  rw [iota_limit hwlim] at hlt'
  haveI : Nonempty (Iio (ω ^ T * ω)) := ⟨⟨0, hwlim.bot_lt⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hlt'
  obtain ⟨m, hm, hem⟩ := (lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 e.2
  obtain ⟨j, rfl⟩ := lt_omega0.1 hm
  have hbj : xtB1 X < iota S (ω ^ T * (j : Ordinal.{0})) := he.trans_le (iota_mono _ _ hem.le)
  let f : ℕ → Ordinal.{0} := fun k =>
    if iota S (ω ^ T * (k : Ordinal.{0})) < xtB1 X then iota S (ω ^ T * (k : Ordinal.{0})) else 0
  have hfb : ∀ k, f k < xtB1 X := fun k => by
    show (if iota S (ω ^ T * (k : Ordinal.{0})) < xtB1 X then iota S (ω ^ T * (k : Ordinal.{0})) else 0) < _
    split_ifs with h
    · exact h
    · exact h0
  have hνb : max (ω * ω) ((Finset.range j).sup f) < xtB1 X :=
    max_lt (hww1.trans_lt hμ1B) ((Finset.sup_lt_iff h0).2 fun k _ => hfb k)
  obtain ⟨μ, hμ, h1, h2⟩ := hcof _ hνb
  have hww : ω * ω < μ := (le_max_left _ _).trans_lt h1
  obtain ⟨k, hk⟩ := lgFr_mul (S := S) hT hP htop htopE hμ hww (h2.trans hlt) (h2.trans hb1)
  have hkj : k < j := by
    by_contra hkj
    push Not at hkj
    have hjk : ω ^ T * (j : Ordinal.{0}) ≤ ω ^ T * (k : Ordinal.{0}) := by gcongr
    have h3 := iota_mono (S := S) _ _ hjk
    rw [← hk] at h3
    exact absurd (h2.trans hbj) (not_lt.2 h3)
  have hfk : f k = μ := by
    show (if iota S (ω ^ T * (k : Ordinal.{0})) < xtB1 X then iota S (ω ^ T * (k : Ordinal.{0})) else 0) = μ
    rw [if_pos (by rw [← hk]; exact h2), hk]
  have h4 : f k ≤ max (ω * ω) ((Finset.range j).sup f) :=
    (Finset.le_sup (f := f) (Finset.mem_range.2 hkj)).trans (le_max_right _ _)
  rw [hfk] at h4
  exact absurd h1 (not_lt.2 h4)

end Gen

/-! ## The frontiers of `lgUSys` -/

theorem lgU_top_code (y : Ordinal.{0}) (hy : SC y) (hy1 : y < Om 1) : lgUSys.top y = ggTh y ggGam :=
  (lg_ggTh_Gam hy hy1).symm

theorem lgU_topE (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : eN x < lgUSys.top x :=
  gT_lt_lgG hx hx1 0

theorem lg_Om1_le_Gam : Om 1 ≤ ggGam := ggGam_spec.2.le

/-- **`ι(Γ_{Ω₁+1}·(n+1))` is a named fixed point and a frontier of `lgUSys`.** -/
theorem lgFrPt (n : ℕ) :
    XtFr lgUSys (iota S (ω ^ ggGam * ((n : Ordinal.{0}) + 1))) ∧
      upsilon (iota S (ω ^ ggGam * ((n : Ordinal.{0}) + 1))) = iota S (ω ^ ggGam * ((n : Ordinal.{0}) + 1)) := by
  set η := ω ^ ggGam * ((n : Ordinal.{0}) + 1) with hη
  have hT0 : ggGam ≠ 0 := ggGam_spec.1.1.ne'
  have hg : Bt.Good S η := lg_good_mul n
  have hlim : IsSuccLimit η := by rw [hη, mul_add_one]; exact isSuccLimit_add _ (ph_opow_lim hT0)
  have hfix := ggFix (S := S) hlim (ph_gap lg_Om1_le_Gam n)
  have hF0 : iota S η ≠ 0 := (lt_of_lt_of_le zero_lt_one (one_le_iota η)).ne'
  have hri := Fx.fx_ri_of_fix hF0 hfix
  have hEta : cdEta S (iota S η) = η := cdEta_unique hg rfl
  have hX : upsilon (iota S η) < Pv S (η + 1) := by
    show upsilon (iota S η) < S.psi (ConjT.Aη S (η + 1)) (Om 1)
    rw [← ups_iota S (η + 1), iota_good hg]
    exact upsilon_normal.strictMono (lt_add_one _)
  have he : cdExp (cdEta S (iota S η)) = ggGam := by rw [hEta, hη, cpExp_mul_succ]
  have hO := lgUni hri hfix hX he.le
  have hSC := ggSC_fix hri hfix hX
  have hF1 := Fx.fx_fix_lt_Om1 hfix hX
  refine ⟨⟨hri, ?_⟩, hfix⟩
  rw [hO, he, hfix, lgUSys_top, lg_ggTh_Gam hSC hF1]

/-- **`Λ⁺(lgUSys) = ι(Γ_{Ω₁+1}·ω)`.** -/
theorem lgU_B1_eq : xtB1 lgUSys = iota S (ggGam * ω) := by
  rw [← lg_Gam_eps]
  refine le_antisymm ?_ (lgB1_ge (S := S) le_rfl lgUPoly lgU_top_code lg_Om1_le_Gam lgU_topE lgUSys_topPkg)
  have hwlim : IsSuccLimit (ω ^ ggGam * ω) := by
    have e : ω ^ ggGam * ω = ω ^ (ggGam + 1) := by rw [opow_add, opow_one]
    rw [e]; exact ph_opow_lim (by simp)
  refine csInf_le (OrderBot.bddBelow _) (Set.mem_insert_of_mem _ ⟨lt_of_lt_of_le zero_lt_one (one_le_iota _),
    fun ν hν => ?_⟩)
  rw [iota_limit hwlim] at hν
  haveI : Nonempty (Iio (ω ^ ggGam * ω)) := ⟨⟨0, hwlim.bot_lt⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hν
  obtain ⟨m, hm, hem⟩ := (lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 e.2
  obtain ⟨j, rfl⟩ := lt_omega0.1 hm
  have hj : ω ^ ggGam * (j : Ordinal.{0}) ≤ ω ^ ggGam * ((j : Ordinal.{0}) + 1) := by gcongr; exact le_self_add
  refine ⟨_, (lgFrPt j).1, he.trans_le (iota_mono _ _ (hem.le.trans hj)), ?_⟩
  refine cd_iota_lt_of_good (lg_good_mul j) ?_
  refine (mul_lt_mul_iff_right₀ (opow_pos _ omega0_pos)).2 ?_
  rw [← Nat.cast_succ]; exact natCast_lt_omega0 _

theorem lg_Gamw_lt_Om2 (S : InaccSeq.{0}) : ggGam * ω < Om (1 + 1) := by
  rw [show ggGam * ω = ω ^ (ggGam + 1) by rw [opow_add, opow_one, lg_Gam_eps]]
  have hSC := gg_SC_Om2
  have h1 : ggGam + 1 < Om (1 + 1) := hSC.isPrincipal (ggGam_lt_Om2 S) (gg_one_lt_of_SC hSC)
  have := hSC.2 0 hSC.1 _ h1
  rwa [veblen_zero_apply] at this

/-- **`ρ_{Λ⁺(lgUSys)} = P(Γ_{Ω₁+1}·ω) < L(0)`**, and `Λ⁺(lgUSys) < L(ω+1)`. -/
theorem lgU_B1_ups : upsilon (xtB1 lgUSys) = Pv S (ggGam * ω) ∧ Pv S (ggGam * ω) < Nc.ncL S 0 := by
  have hups : upsilon (xtB1 lgUSys) = Pv S (ggGam * ω) := by rw [lgU_B1_eq (S := S), ups_iota S]
  refine ⟨hups, ?_⟩
  have h1 : iota S (ggGam * ω) < iota S (Om ω) :=
    (iota_mono _ _ (lg_Gamw_lt_Om2 S).le).trans_lt (cd_iota_lt_of_good lg_Om2_good ph_Om2_lt_Omw)
  have hL0 : Nc.ncL S 0 = upsilon (iota S (Om ω)) := by
    rw [Lw.lw_L_eq, mul_zero, add_zero]; exact (ups_iota S _).symm
  rw [← hups, lgU_B1_eq (S := S), hL0]
  exact upsilon_normal.strictMono h1

end Googology.Trans.PoR.InaccPsi.R2
