import Googology.Trans.PoR.InaccPsi.R2.LyBig
import Googology.Trans.PoR.InaccPsi.R2.LyW2

/-!
# The layers `B(x)^{n+2}`: BLK^O, the reaches, ENUM-REACH and the road up to `Λ_{B^ω}`

`lyBN n` (`R2.LyBig`): `lyBN 0 = lyBig vzLay` (terms `Σ ω^{B(x) + dᵢ(x)}·kᵢ + s(x)`, top `B(x)²`), `lyBN (n+1) =
lyBig (lyBN n)`; the exponent is `B(x)·(n+2)` and the top `B(x)^{n+2}` (`lyBN_E`, `lyBN_top`).  Each contains the top
of the previous one as a term (`ω^{E(x) + 0}`), `lyBN 0` contains the tops `B(x)` of `vzLay` and `B(x)·x^x` of `lyPB`
(`ω^{B(x) + ω^{x+x}}`).  With `Λ⁺_n = lyLamB n = xtB1 (lyBN n)` (`R2.LyCmp`):

* `lyLamB_lt` (**`Λ⁺_n < Λ⁺_{n+1}`**), `lyBN_eq` (`O_m = O_n` below `Λ⁺_n`), `lyBN_vz` (`O_n = VzOrec` below `cpB1`),
  `lyPB_lt_B` (`Λ⁺(lyPB) < Λ(lyBN 0)`), `lyW2_lt_B` (**`Λ_{ω²} < Λ_{B^ω}`**);
* `lyFamB : XtFam` (bounds `Λ⁺_n`, offsets `O_n`), `Λ_{B^ω} = lyFamB.famSup`; the instances of `R2.XtFam`:
  `lyB_blk` (**BLK^O below `υ_{Λ_{B^ω}}`**), `lyB_nuC` (`υ_{Λ_{B^ω}} ≤ ρ_L < ν_C`), `lyB_init` (**UPPER and LOWER at every
  non-fixed restart of the range below `Λ_{B^ω}`**), `lyB_capV`, `lyB_of_cp`, `lyBRoad3`, `lyBRoad`, `lyBRoad_cap`,
  `lyBRoad2`;
* the reaches: `lyBN_reachLam` (**`lh(ρ) = δ + B(ρ)^{n+2}`** at `Λ(lyBN n)`), `lyBN_reachB1` (**`lh(ρ) = δ + B(ρ)^{n+2} +
  1`** at `Λ⁺_n`), `lyB_reachT` (**`lh(ρ) = δ + ω^{B(ρ) + d(ρ)}`** at the frontier of every term `ω^{B(x) + d(x)}`, `d` a
  `φ(n, ·)`-term with constants below `ρ_{Λ(lyBN 0)}`: all `B(x)·x^{e(x)}`, `x·e(x) < B(x)`).

No new axiom beyond `R2.CitedXt`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ly

open Ordinal Order Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp

theorem vzLay_EB : ∀ x, InE x → x < Om1 → VzB x ≤ vzLay.E x := fun _ _ _ => le_rfl

/-- The layers `lyBN n` with the bound `B(x) ≤ E(x)`. -/
noncomputable def lyBNp : ℕ → {L : XtLay // ∀ x, InE x → x < Om1 → VzB x ≤ L.E x}
  | 0 => ⟨lyBig vzLay vzLay_EB, lyBig_EB vzLay vzLay_EB⟩
  | n + 1 => ⟨lyBig (lyBNp n).1 (lyBNp n).2, lyBig_EB (lyBNp n).1 (lyBNp n).2⟩

/-- **The `n`-th layer of the powers of `B`**: top `B(x)^{n+2}`. -/
noncomputable def lyBN (n : ℕ) : XtLay := (lyBNp n).1

theorem lyBN_succ (n : ℕ) : lyBN (n + 1) = lyBig (lyBN n) (lyBNp n).2 := rfl

theorem lyBN_E (n : ℕ) (x : Ordinal.{0}) : (lyBN n).E x = VzB x * ((n + 2 : ℕ) : Ordinal.{0}) := by
  induction n with
  | zero =>
    show VzB x + VzB x = _
    rw [show ((0 + 2 : ℕ) : Ordinal.{0}) = 2 by norm_num, Ordinal.mul_two]
  | succ n ih =>
    show (lyBN n).E x + VzB x = _
    have e : ((n + 1 + 2 : ℕ) : Ordinal.{0}) = ((n + 2 : ℕ) : Ordinal.{0}) + 1 := by
      rw [show n + 1 + 2 = n + 2 + 1 by omega]; exact Nat.cast_succ _
    rw [ih, e, mul_add_one]

theorem lyBN_top (n : ℕ) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    (lyBN n).sys.top x = VzB x ^ ((n + 2 : ℕ) : Ordinal.{0}) := by
  rw [(lyBN n).top_eq x hx hx1, lyBN_E, opow_mul, show ω ^ VzB x = VzB x from xt_B_E hx hx1]

theorem lyBN_EB (n : ℕ) : ∀ x, InE x → x < Om1 → VzB x ≤ (lyBN n).E x := (lyBNp n).2

/-- `ω^a + 1 < ω^b` for `0 < a < b`. -/
theorem ly_opow_gap {a b : Ordinal.{0}} (ha : 0 < a) (hab : a < b) : ω ^ a + 1 < ω ^ b := by
  have h1 : 1 < ω ^ a := by
    have := (opow_lt_opow_iff_right one_lt_omega0).2 ha; rwa [opow_zero] at this
  calc ω ^ a + 1 < ω ^ a + ω ^ a := (add_lt_add_iff_left _).2 h1
    _ = ω ^ a * 2 := (Ordinal.mul_two _).symm
    _ ≤ ω ^ a * ω := mul_le_mul_right (le_of_lt (by exact_mod_cast natCast_lt_omega0 2)) _
    _ = ω ^ (a + 1) := (opow_add_one _ _).symm
    _ ≤ ω ^ b := opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hab)

/-- `lyBig L` contains the top of `L` (the term `ω^{E(x) + 0}`). -/
theorem lyBig_topIn (L : XtLay) (hEB : ∀ x, InE x → x < Om1 → VzB x ≤ L.E x) :
    LyTopIn (lyBig L hEB).sys L.sys := by
  refine ⟨lbPowTm L hEB (VzTm.cst 0), fun x hx hx1 => ⟨lbPowTm_cb L hEB hx (show (0 : Ordinal.{0}) < x from hx.1),
    ?_⟩, fun l hl hl1 => ?_⟩
  · rw [lbPowTm_val, VzTm.val_cst, add_zero, L.top_eq x (upsPt_inE hx) hx1]
  · have hρE := ups_inE hl
    have hρ1 := ups_lt_Om1 l hl1
    rw [L.top_eq _ hρE hρ1, lyBig_top]
    have hE0 : 0 < L.E (upsilon l) := (lt_of_lt_of_le hρE.pos (vzB_omega hρE hρ1).2.1.le).trans_le (hEB _ hρE hρ1)
    exact ly_opow_gap hE0 (lt_add_of_pos_right _ (xt_B_E hρE hρ1).pos)

theorem lyBN_topIn (n : ℕ) : LyTopIn (lyBN (n + 1)).sys (lyBN n).sys := lyBig_topIn (lyBN n) (lyBNp n).2

/-- `Λ⁺_n`: the first limit of the frontiers of `lyBN n`. -/
noncomputable def lyLamB (n : ℕ) : Ordinal.{0} := xtB1 (lyBN n).sys

/-- **`Λ⁺_n < Λ⁺_{n+1}`.** -/
theorem lyLamB_lt (n : ℕ) : lyLamB n < lyLamB (n + 1) :=
  lyB1_lt (lyBN (n + 1)).topPkg (lyBN n).topPkg (lyBN_topIn n)

theorem lyLamB_strictMono : StrictMono lyLamB := strictMono_nat_of_lt_succ lyLamB_lt

theorem lyLamB_lt_Om1 (n : ℕ) : lyLamB n < Om1 := xtB1_lt_Om1 (lyBN n).topPkg

/-- `O_m = O_n` below `Λ⁺_n` for `n ≤ m`. -/
theorem lyBN_eq {n m : ℕ} (h : n ≤ m) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (hμn : μ < lyLamB n) :
    xtOrec (lyBN m).sys μ = xtOrec (lyBN n).sys μ := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    rw [← ih]
    exact lyEq (lyBN m).topPkg (lyBN_topIn m) hμ (hμn.trans_le (lyLamB_strictMono.monotone hnm))

theorem lyBN0_topIn_vz : LyTopIn (lyBN 0).sys vzLay.sys := lyBig_topIn vzLay vzLay_EB

/-- `cpB1 < Λ(lyBN 0)`. -/
theorem lyBN_cp_lt : Cp.cpB1 < xtLam (lyBN 0).sys := by
  rw [← xtVz_B1]; exact lyLamGt vzLay.topPkg lyBN0_topIn_vz

/-- **`O_n = VzOrec` below `cpB1`.** -/
theorem lyBN_vz (n : ℕ) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h : μ < Cp.cpB1) :
    xtOrec (lyBN n).sys μ = VzOrec μ := by
  have h0 : μ < lyLamB 0 := h.trans (lyBN_cp_lt.trans (lyBN 0).xtLamLt)
  rw [lyBN_eq (Nat.zero_le n) hμ h0,
    lyEq vzLay.topPkg lyBN0_topIn_vz hμ (by rw [show xtB1 vzLay.sys = Cp.cpB1 from xtVz_B1]; exact h)]
  exact congrFun xtVz_orec μ

theorem lyBN0_powv (d : VzTm) (x : Ordinal.{0}) :
    (lyBN 0).sys.val (lbPowTm vzLay vzLay_EB d) x = ω ^ (VzB x + d.val x) :=
  lbPowTm_val vzLay vzLay_EB d x

/-- `lyBN 0` contains the top `B(x)·x^x = ω^{B(x) + ω^{x+x}}` of `lyPB`. -/
theorem lyBN0_topIn_PB : LyTopIn (lyBN 0).sys lyPB.sys := by
  refine ⟨lbPowTm vzLay vzLay_EB (VzTm.pw (VzTm.sm VzTm.bs VzTm.bs)), fun x hx hx1 =>
    ⟨lbPowTm_cb vzLay vzLay_EB hx (show VzTm.CBt (VzTm.pw (VzTm.sm VzTm.bs VzTm.bs)) x from ⟨trivial, trivial⟩),
      ?_⟩, fun l hl hl1 => ?_⟩
  · have hxE := upsPt_inE hx
    rw [lyBN0_powv, lyPB_top, VzTm.val_pw, VzTm.val_sm, VzTm.val_bs, ← ly_mul_opow hxE,
      show ω ^ x = x from hxE, ← vzLay_top, ly_top_pow vzLay hxE hx1]
    rfl
  · have hρE := ups_inE hl
    have hρ1 := ups_lt_Om1 l hl1
    have hBE := xt_B_E hρE hρ1
    have hρB := (vzB_omega hρE hρ1).2.1
    rw [lyPB_top, ← vzLay_top, ly_top_pow vzLay hρE hρ1]
    show ω ^ (VzB (upsilon l) + upsilon l * upsilon l) + 1 < ω ^ (VzB (upsilon l) + VzB (upsilon l))
    exact ly_opow_gap (hBE.pos.trans_le le_self_add) ((add_lt_add_iff_left _).2 (hBE.mul_lt hρB hρB))

/-- **`Λ⁺(lyPB) < Λ(lyBN 0)`.** -/
theorem lyPB_lt_B : xtB1 lyPB.sys < xtLam (lyBN 0).sys := lyLamGt lyPB.topPkg lyBN0_topIn_PB

/-- **The family of the layers `lyBN n`**: bounds `Λ⁺_n`, offsets `O_n`. -/
noncomputable def lyFamB : XtFam where
  bd := lyLamB
  off := fun n => xtOrec (lyBN n).sys
  spec := fun n => xtSpec1 (lyBN n).topPkg
  mono := lyLamB_lt
  nonfix := fun n _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (lyLamB_lt_Om1 n))

theorem lyFamB_sup : lyFamB.famSup = ⨆ n : ℕ, lyLamB n := rfl

theorem lyFamB_iso : lyFamB.famIsoOff := fun k _ hl hlk hfix hiso =>
  xtIso hl hfix (hlk.trans (lyLamB_lt_Om1 k)) hiso (X := (lyBN k).sys)

/-- **`Λ_{ω²} < Λ_{B^ω}`.** -/
theorem lyW2_lt_B : xtFamW2.famSup < lyFamB.famSup :=
  lyW2_lt_Lam.trans (lyPB.xtLamLt.trans (lyPB_lt_B.trans ((lyBN 0).xtLamLt.trans (lyFamB.famBd_lt 0))))

theorem lyB_cp_le : Cp.cpB1 ≤ lyFamB.famSup :=
  (lyBN_cp_lt.trans ((lyBN 0).xtLamLt.trans (lyFamB.famBd_lt 0))).le

/-! ## The reaches -/

/-- **The reach at the frontier of `lyBN n`**: `lh(ρ) = δ + B(ρ)^{n+2}`. -/
theorem lyBN_reachLam (n : ℕ) :
    IsReach R2C (upsilon (xtLam (lyBN n).sys))
      (upsilon (xtLam (lyBN n).sys + ω + 1) + VzB (upsilon (xtLam (lyBN n).sys)) ^ ((n + 2 : ℕ) : Ordinal.{0})) := by
  have hl := xtLam_ri (X := (lyBN n).sys)
  rw [← lyBN_top n (ups_inE hl) (ups_lt_Om1 _ xtLam_lt_Om1), ← xtOrec_Lam]
  exact xtReach1 (lyBN n).topPkg hl (lyBN n).xtLamLt

/-- **The reach at `Λ⁺_n`**: `lh(ρ) = δ + B(ρ)^{n+2} + 1`. -/
theorem lyBN_reachB1 (n : ℕ) :
    IsReach R2C (upsilon (lyLamB n))
      (upsilon (lyLamB n + ω + 1) + (VzB (upsilon (lyLamB n)) ^ ((n + 2 : ℕ) : Ordinal.{0}) + 1)) := by
  have hl := lyB1_ri (lyBN n).topPkg
  have h := lyReachB1 (lyBN (n + 1)).topPkg (lyBN n).topPkg (lyBN_topIn n)
  rwa [lyBN_top n (ups_inE hl) (ups_lt_Om1 _ (lyLamB_lt_Om1 n))] at h

/-- **The reach at the frontier of every term `ω^{B(x) + d(x)}`** of `lyBN 0` (`d` a `φ(n, ·)`-term with constants
below `ρ_{Λ(lyBN 0)}`): `lh(ρ) = δ + ω^{B(ρ) + d(ρ)}`. -/
theorem lyB_reachT {d : VzTm} (hd : d.CBt (upsilon (xtLam (lyBN 0).sys))) :
    IsReach R2C (upsilon (xtLamT (lyBN 0).sys (lbPowTm vzLay vzLay_EB d)))
      (upsilon (xtLamT (lyBN 0).sys (lbPowTm vzLay vzLay_EB d) + ω + 1) +
        ω ^ (VzB (upsilon (xtLamT (lyBN 0).sys (lbPowTm vzLay vzLay_EB d))) +
          d.val (upsilon (xtLamT (lyBN 0).sys (lbPowTm vzLay vzLay_EB d))))) := by
  have hU := ups_ri (xtLam_ri (X := (lyBN 0).sys))
  have hCB := lbPowTm_cb vzLay vzLay_EB hU hd
  have h1 : 1 ≤ (lyBN 0).sys.val (lbPowTm vzLay vzLay_EB d) (upsilon (xtLam (lyBN 0).sys)) := by
    show 1 ≤ (lyBig vzLay vzLay_EB).sys.val (lbPowTm vzLay vzLay_EB d) _
    rw [lbPowTm_val]; exact one_le_iff_pos.2 (opow_pos _ omega0_pos)
  have := xtReach_LamT hCB h1
  rw [lbPowTm_val] at this
  exact this

/-! ## The instances of `R2.XtFam` for `Λ_{B^ω}` -/

/-- **Theorem BLK^O below `υ_{Λ_{B^ω}}`** in `R₂^C`. -/
theorem lyB_blk :
    (∀ c d, c < d → d < upsilon lyFamB.famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < lyFamB.famSup ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < lyLamB k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (lyBN k).sys l)) ∧
    (∀ α < upsilon lyFamB.famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  lyFamB.famBlk

/-- **Where the first non-standard pair lies**: `ρ_L <₂ ν_C = ρ_ξ` with `Λ_{B^ω} ≤ L < ξ`. -/
theorem lyB_nuC : ∃ L ξ, IsRestartIdx L ∧ IsRestartIdx ξ ∧ lyFamB.famSup ≤ L ∧ L < ξ ∧
    upsilon lyFamB.famSup ≤ upsilon L ∧ upsilon L < nuC ∧ nuC = upsilon ξ ∧ le2 (upsilon L) nuC :=
  lyFamB.famNuC

variable {S : InaccSeq.{0}}

/-- **UPPER and LOWER at every restart of the range below `Λ_{B^ω}` that is not a fixed point of `υ`.** -/
theorem lyB_init {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < lyFamB.famSup) (hfix : l < upsilon l) :
    CdUpper S l ∧ CdLower S l :=
  lyFamB.famInit hr hl hfix

/-- **The cap of the values at every restart of the range below `Λ_{B^ω}` that is not a fixed point of `υ`.** -/
theorem lyB_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < lyFamB.famSup) (hfix : l < upsilon l) :
    CdCapV S l :=
  lyFamB.famCapV hr hl hfix

/-- **The hypotheses of `lyFamB.famRoad3` from those of `cpRoad3`.** -/
theorem lyB_of_cp (hU : CpUPPERhigh S) (hL : CpLOWERhigh S) (hT : CpTHfix S) :
    (∀ l, CdRange S l → lyFamB.famSup ≤ l → CdUpper S l) ∧
      (∀ l, CdRange S l → lyFamB.famSup ≤ l → CdLower S l) ∧ lyFamB.famTHfix S :=
  lyFamB.famOf_cp lyB_cp_le (fun k _ hμ h1 _ => lyBN_vz k hμ h1) hU hL hT

/-- **The road with UPPER and LOWER asked only at `λ ≥ Λ_{B^ω}`**, `Θ_F(m_F) = O_k(F)` at the fixed points
`F < Λ⁺_k` of the range, the cap of the values outside `Λ_{B^ω}`, (CL), EQ, TCrest, (EMB₂). -/
theorem lyBRoad3 (hU : ∀ l, CdRange S l → lyFamB.famSup ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → lyFamB.famSup ≤ l → CdLower S l) (hT : lyFamB.famTHfix S)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut lyFamB.famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lyFamB.famRoad3 hU hL hT hV hC hEQ hrest hB2

/-- **The road with UPPER, LOWER and the cap of the values asked only outside `Λ_{B^ω}`.** -/
theorem lyBRoad (hU : ∀ l, CdRange S l → XtOut lyFamB.famSup l → CdUpper S l)
    (hL : ∀ l, CdRange S l → XtOut lyFamB.famSup l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut lyFamB.famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lyFamB.famRoad hU hL hV hC hEQ hrest hB2

/-- **The road with the caps asked only outside `Λ_{B^ω}`**: CAP-0, CAP-1 outside, (CL), (TC), (EMB₂). -/
theorem lyBRoad_cap
    (h0 : ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → XtOut lyFamB.famSup l → CdCapAt S l)
    (h1 : ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < Nc.ncL S ω →
      cdCode S l < Nc.ncPp S → XtOut lyFamB.famSup l → CdCapAt S l) (hC : CdCL S) (hTC : CdTC S)
    (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lyFamB.famRoad_cap h0 h1 hC hTC hB2

/-- **The road with UPPER asked only at `λ ≥ Λ_{B^ω}` and at the non-isolated fixed points** (the code `F ≤ m_F` at
the isolated fixed points below `Λ_{B^ω}`), LOWER and the cap of the values outside, (CL), EQ, TCrest, (EMB₂). -/
theorem lyBRoad2 (hU : ∀ l, CdRange S l → (lyFamB.famSup ≤ l ∨ (upsilon l = l ∧ ¬ CpIso l)) → CdUpper S l)
    (hc : ∀ l, CdRange S l → l < lyFamB.famSup → upsilon l = l → CpIso l → l ≤ cdCode S l)
    (hL : ∀ l, CdRange S l → XtOut lyFamB.famSup l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut lyFamB.famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lyFamB.famRoad2 lyFamB_iso hU hc hL hV hC hEQ hrest hB2

end Googology.Trans.PoR.InaccPsi.R2.Ly
