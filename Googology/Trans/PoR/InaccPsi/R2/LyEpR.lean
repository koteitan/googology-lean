import Googology.Trans.PoR.InaccPsi.R2.LyEp
import Googology.Trans.PoR.InaccPsi.R2.LyFam
import Googology.Trans.PoR.InaccPsi.R2.LyLim

/-!
# Up to `ε_{B(x)+1}`: BLK^O, the reaches, ENUM-REACH and the road below `Λ⁺(lyEB)`

`lyEB = lyEp vzLay` (`R2.LyEp`): the terms `Σ ω^{B(x) + dᵢ(x)}·kᵢ + s(x)` (`dᵢ` terms over `B`, `R2.LyTm`), top
`ε_{B(x)+1}`.  Its offset `O_E`, frontier `Λ(lyEB)` (where `O_E = ε_{B(ρ)+1}`) and first limit of frontiers `Λ⁺(lyEB)`:

* `lyEB_topIn_BN` (`lyEB` contains every top `B(x)^{n+2}`), `lyEB_topIn_vz` (and `B(x)`), `lyEB_vz`
  (`O_E = VzOrec` below `cpB1`), `lyBw_le` / `lyBw_lt_E` (**`Λ_{B^ω} < Λ(lyEB)`**);
* `lyBw_ri` (**`Λ_{B^ω}` is a restart index**), `lyBw_at` (**`O_E(Λ_{B^ω}) = B(ρ)^ω`**), `lyBw_reach`
  (**`lh(ρ_{Λ_{B^ω}}) = δ + B(ρ)^ω`**), by `R2.LyLim`;
* `lyE_blk` (**BLK^O below `υ_{Λ⁺(lyEB)}`**), `lyE_reach` (**`lh(ρ_λ) = δ_λ + O_E(λ)` at every restart `λ <
  Λ⁺(lyEB)`**), `lyE_reachLam` (**`lh(ρ) = δ + ε_{B(ρ)+1}` at `Λ(lyEB)`**), `lyE_reachT` (**`lh(ρ) = δ + ω^{B(ρ) +
  d(ρ)}`** at the frontier of every term `ω^{B(x) + d(x)}`, `d` over `B`: all `B(x)^{e(x)}`, `e(x) < ε_{B(x)+1}`);
* `lyE_nuC` (`υ_{Λ⁺(lyEB)} ≤ ρ_L < ν_C`), `lyE_init` (**UPPER and LOWER at every non-fixed restart of the range below
  `Λ⁺(lyEB)`**), `lyE_capV`, `lyE_capAt`, `lyE_of_cp`, `lyERoad3`, `lyERoad`, `lyERoad_cap` (the roads of `R2.XtEnum`
  with the rest asked only outside `Λ⁺(lyEB)`), `lyE_iso` (`O_E(F) = F` at the isolated fixed points),
  `lyE_fix_code` (ENUM-REACH there from the code `F ≤ m_F ≤ Ω₁`).

No new axiom beyond `R2.CitedXt`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ly

open Ordinal Order Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp

theorem vzLay_Ee : ∀ x, InE x → x < Om1 → vzLay.E x < eN (VzB x) := fun x _ _ => lt_eN (VzB x)

/-- **The term system of the exponents over `B`, on `B`**: top `ε_{B(x)+1}`. -/
noncomputable def lyEB : XtSys := lyEp vzLay vzLay_EB vzLay_Ee

theorem lyEB_top (x : Ordinal.{0}) : lyEB.top x = eN (VzB x) := rfl

theorem lyEB_topPkg : XtTopPkg lyEB := lyEp_topPkg vzLay vzLay_EB vzLay_Ee

theorem lyEB_powv (d : LyTm) (x : Ordinal.{0}) :
    lyEB.val (lePowTm vzLay vzLay_EB vzLay_Ee d) x = ω ^ (VzB x + d.val x) :=
  lePowTm_val vzLay vzLay_EB vzLay_Ee d x

/-- The term `B(x)·(k+1)` over `B`. -/
def lyBk : ℕ → LyTm
  | 0 => LyTm.bB
  | k + 1 => LyTm.sm (lyBk k) LyTm.bB

theorem lyBk_val (k : ℕ) (x : Ordinal.{0}) : (lyBk k).val x = VzB x * ((k + 1 : ℕ) : Ordinal.{0}) := by
  induction k with
  | zero => show VzB x = _; rw [zero_add, Nat.cast_one, mul_one]
  | succ k ih =>
    show (lyBk k).val x + VzB x = _
    rw [ih, Nat.cast_succ (k + 1), mul_add_one]

theorem lyBk_cb (k : ℕ) (x : Ordinal.{0}) : (lyBk k).CBt x := by
  induction k with
  | zero => trivial
  | succ k ih => exact ⟨ih, trivial⟩

theorem ly_lt_eNB {x a : Ordinal.{0}} (ha : a < eN (VzB x)) : a + 1 < eN (VzB x) :=
  (inE_indec (eN_E _)).add_lt ha (one_lt_omega0.trans (omega0_lt_inE (eN_E _)))

/-- `lyEB` contains the top `B(x)^{n+2} = ω^{B(x) + B(x)·(n+1)}` of `lyBN n`. -/
theorem lyEB_topIn_BN (n : ℕ) : LyTopIn lyEB (lyBN n).sys := by
  have e : ((n + 2 : ℕ) : Ordinal.{0}) = 1 + ((n + 1 : ℕ) : Ordinal.{0}) := by
    rw [← Nat.cast_one, ← Nat.cast_add]; congr 1; omega
  refine ⟨lePowTm vzLay vzLay_EB vzLay_Ee (lyBk n), fun x hx hx1 =>
    ⟨lePowTm_cb vzLay vzLay_EB vzLay_Ee hx (lyBk_cb n x), ?_⟩, fun l hl hl1 => ?_⟩
  · rw [lyEB_powv, lyBk_val, (lyBN n).top_eq x (upsPt_inE hx) hx1, lyBN_E, e, mul_add, mul_one]
  · have hρE := ups_inE hl
    have hρ1 := ups_lt_Om1 l hl1
    have heE := eN_E (VzB (upsilon l))
    have hB := lt_eN (VzB (upsilon l))
    rw [(lyBN n).top_eq _ hρE hρ1, lyBN_E, lyEB_top]
    refine ly_lt_eNB (heE.opow_lt (heE.mul_lt hB ?_))
    exact (natCast_lt_omega0 _).trans (omega0_lt_inE heE)

/-- `lyEB` contains the top `B(x) = ω^{B(x) + 0}` of `vzLay`. -/
theorem lyEB_topIn_vz : LyTopIn lyEB vzLay.sys := by
  refine ⟨lePowTm vzLay vzLay_EB vzLay_Ee (LyTm.vz (VzTm.cst 0)), fun x hx hx1 =>
    ⟨lePowTm_cb vzLay vzLay_EB vzLay_Ee hx (show (0 : Ordinal.{0}) < x from hx.1), ?_⟩, fun l hl hl1 => ?_⟩
  · rw [lyEB_powv, LyTm.val_vz, VzTm.val_cst, add_zero, show ω ^ VzB x = VzB x from
      xt_B_E (upsPt_inE hx) hx1]
    rfl
  · exact ly_lt_eNB (lt_eN _)

/-- **`O_E = VzOrec` below `cpB1`.** -/
theorem lyEB_vz {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h : μ < Cp.cpB1) : xtOrec lyEB μ = VzOrec μ := by
  rw [lyEq vzLay.topPkg lyEB_topIn_vz hμ (by rw [show xtB1 vzLay.sys = Cp.cpB1 from xtVz_B1]; exact h)]
  exact congrFun xtVz_orec μ

/-! ## The limit `Λ_{B^ω}` of the layers `lyBN n` -/

/-- The chain of the layers `lyBN n` inside `lyEB`. -/
noncomputable def lyChainB : LyChain lyEB where
  Y := fun k => (lyBN k).sys
  pkg := fun k => (lyBN k).topPkg
  inX := lyEB_topIn_BN
  next := fun k => lyLamGt (lyBN k).topPkg (lyBN_topIn k)
  topMono := fun k x hx hx1 => by
    rw [lyBN_top k hx hx1, lyBN_top (k + 1) hx hx1]
    exact opow_le_opow_right (xt_B_E hx hx1).pos (by exact_mod_cast (show k + 2 ≤ k + 1 + 2 by omega))

theorem lyChainB_sup : lyChainB.fam.famSup = lyFamB.famSup := rfl

theorem lyBw_hG (k : ℕ) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    (lyChainB.Y k).top x < VzB x ^ ω := by
  show (lyBN k).sys.top x < _
  rw [lyBN_top k hx hx1]
  exact (opow_lt_opow_iff_right (one_lt_omega0.trans (omega0_lt_inE (xt_B_E hx hx1)))).2 (natCast_lt_omega0 _)

theorem lyBw_hG' {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {v : Ordinal.{0}} (hv : v < VzB x ^ ω) :
    ∃ k, v < (lyChainB.Y k).top x := by
  have hB1 : 1 < VzB x := one_lt_omega0.trans (omega0_lt_inE (xt_B_E hx hx1))
  obtain ⟨c, hc, hvc⟩ := (lt_opow_of_isSuccLimit (zero_lt_one.trans hB1).ne' isSuccLimit_omega0).1 hv
  obtain ⟨n, rfl⟩ := lt_omega0.1 hc
  refine ⟨n, ?_⟩
  show v < (lyBN n).sys.top x
  rw [lyBN_top n hx hx1]
  exact hvc.trans_le (opow_le_opow_right (zero_lt_one.trans hB1) (by exact_mod_cast (show n ≤ n + 2 by omega)))

/-- **`Λ_{B^ω}` is a restart index.** -/
theorem lyBw_ri : IsRestartIdx lyFamB.famSup := lyChainB.sup_ri

/-- **`O_E(Λ_{B^ω}) = B(ρ)^ω`** for `ρ = ρ_{Λ_{B^ω}}`. -/
theorem lyBw_at : xtOrec lyEB lyFamB.famSup = VzB (upsilon lyFamB.famSup) ^ ω :=
  lyChainB.lyLimAt (fun x => VzB x ^ ω) (fun k _ hx hx1 => lyBw_hG k hx hx1)
    (fun _ hx hx1 _ hv => lyBw_hG' hx hx1 hv)

/-- **`Λ_{B^ω} < Λ(lyEB)`, and the reach at `Λ_{B^ω}`**: `lh(ρ) = δ + B(ρ)^ω`. -/
theorem lyBw_reach : lyFamB.famSup < xtLam lyEB ∧
    IsReach R2C (upsilon lyFamB.famSup)
      (upsilon (lyFamB.famSup + ω + 1) + VzB (upsilon lyFamB.famSup) ^ ω) :=
  lyChainB.lyLimReach (fun x => VzB x ^ ω) (fun k _ hx hx1 => lyBw_hG k hx hx1)
    (fun _ hx hx1 _ hv => lyBw_hG' hx hx1 hv) fun x hx hx1 => by
      have heE := eN_E (VzB x)
      exact ly_pow_lt heE (lt_eN _) (omega0_lt_inE heE)

/-- `Λ(lyEB) < Λ⁺(lyEB)`. -/
theorem lyE_lam_lt : xtLam lyEB < xtB1 lyEB := lyLamLtB1 lyEB_topPkg

/-- **`Λ_{ω²} < Λ_{B^ω} < Λ⁺(lyEB)`.** -/
theorem lyE_order : xtFamW2.famSup < lyFamB.famSup ∧ lyFamB.famSup < xtB1 lyEB :=
  ⟨lyW2_lt_B, lyBw_reach.1.trans lyE_lam_lt⟩

/-! ## The reaches -/

theorem lyE_nonfix : XtNonfix (xtOrec lyEB) (xtB1 lyEB) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 lyEB_topPkg))

/-- **The exact reach of every restart below `Λ⁺(lyEB)`**: `lh(ρ_λ) = δ_λ + O_E(λ)`. -/
theorem lyE_reach {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < xtB1 lyEB) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec lyEB l) :=
  xtReach1 lyEB_topPkg hl hlB

/-- **The reach at the frontier of `lyEB`**: `lh(ρ) = δ + ε_{B(ρ)+1}`. -/
theorem lyE_reachLam :
    IsReach R2C (upsilon (xtLam lyEB))
      (upsilon (xtLam lyEB + ω + 1) + eN (VzB (upsilon (xtLam lyEB)))) := by
  rw [← lyEB_top, ← xtOrec_Lam]
  exact xtReach1 lyEB_topPkg xtLam_ri lyE_lam_lt

/-- **The reach at the frontier of every term `ω^{B(x) + d(x)}`** (`d` over `B`, constants below
`ρ_{Λ(lyEB)}`): `lh(ρ) = δ + ω^{B(ρ) + d(ρ)}`. -/
theorem lyE_reachT {d : LyTm} (hd : d.CBt (upsilon (xtLam lyEB))) :
    IsReach R2C (upsilon (xtLamT lyEB (lePowTm vzLay vzLay_EB vzLay_Ee d)))
      (upsilon (xtLamT lyEB (lePowTm vzLay vzLay_EB vzLay_Ee d) + ω + 1) +
        ω ^ (VzB (upsilon (xtLamT lyEB (lePowTm vzLay vzLay_EB vzLay_Ee d))) +
          d.val (upsilon (xtLamT lyEB (lePowTm vzLay vzLay_EB vzLay_Ee d))))) := by
  have hU := ups_ri (xtLam_ri (X := lyEB))
  have hCB := lePowTm_cb vzLay vzLay_EB vzLay_Ee hU hd
  have h1 : 1 ≤ lyEB.val (lePowTm vzLay vzLay_EB vzLay_Ee d) (upsilon (xtLam lyEB)) := by
    rw [lyEB_powv]; exact one_le_iff_pos.2 (opow_pos _ omega0_pos)
  have := xtReach_LamT hCB h1
  rw [lePowTm_val] at this
  exact this

/-- **Theorem BLK^O below `υ_{Λ⁺(lyEB)}`** in `R₂^C`. -/
theorem lyE_blk :
    (∀ c d, c < d → d < upsilon (xtB1 lyEB) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 lyEB ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 lyEB →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec lyEB l)) ∧
    (∀ α < upsilon (xtB1 lyEB), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtBlk1 lyEB_topPkg

/-- **Where the first non-standard pair lies**: `ρ_L <₂ ν_C = ρ_ξ` with `Λ⁺(lyEB) ≤ L < ξ`. -/
theorem lyE_nuC : ∃ L ξ, IsRestartIdx L ∧ IsRestartIdx ξ ∧ xtB1 lyEB ≤ L ∧ L < ξ ∧
    upsilon (xtB1 lyEB) ≤ upsilon L ∧ upsilon L < nuC ∧ nuC = upsilon ξ ∧ le2 (upsilon L) nuC := by
  obtain ⟨L, ξ, hL, hξ, hLξ, he, h2, -, -, -⟩ := level2_restart
  have hLν : upsilon L < nuC := by rw [he]; exact upsilon_normal.strictMono hLξ
  have hle : xtB1 lyEB ≤ L := left_ge_of_spec (xtSpec1 lyEB_topPkg) hL hLν h2
  exact ⟨L, ξ, hL, hξ, hle, hLξ, upsilon_normal.strictMono.monotone hle, hLν, he, h2⟩

variable {S : InaccSeq.{0}}

/-- **UPPER and LOWER at every restart of the range below `Λ⁺(lyEB)` that is not a fixed point of `υ`.** -/
theorem lyE_init {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lyEB) (hfix : l < upsilon l) :
    CdUpper S l ∧ CdLower S l :=
  xtInit (xtSpec1 lyEB_topPkg) lyE_nonfix hr hl hfix

/-- **The cap of the values at every restart of the range below `Λ⁺(lyEB)` that is not a fixed point.** -/
theorem lyE_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lyEB) (hfix : l < upsilon l) :
    CdCapV S l := by
  have hww := cp_ww_lt_B0.trans_le hr.2.1
  exact xtCapV_nonfix (xtSpec1 lyEB_topPkg) hr.1 hww hfix hl (cp_name_L hr.2.2.1)
    (lyE_nonfix l hr.1 hww hfix hl)

theorem lyE_capAt {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hB : cdB0 ≤ l) (hlΛ : l < xtB1 lyEB)
    (hfix : l < upsilon l) (hname : upsilon l < Pv S η1) : CdCapAt S l := by
  have hww := cp_ww_lt_B0.trans_le hB
  exact xtCapAt_nonfix (xtSpec1 lyEB_topPkg) hl hww hfix hlΛ hname (lyE_nonfix l hl hww hfix hlΛ)

/-- **Below `Λ⁺(lyEB)`, ENUM-REACH is the equation `Θ_λ(m_λ) = O_E(λ)`.** -/
theorem lyE_iff {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < xtB1 lyEB) :
    (CdUpper S l ∧ CdLower S l ↔ cdTheta S l (cdCode S l) = xtOrec lyEB l) :=
  xtExact_iff (xtSpec1 lyEB_topPkg) hl hlB

/-- **The hypotheses of `lyERoad3` from those of `cpRoad3`.** -/
theorem lyE_of_cp (hU : CpUPPERhigh S) (hL : CpLOWERhigh S) (hT : CpTHfix S) :
    (∀ l, CdRange S l → xtB1 lyEB ≤ l → CdUpper S l) ∧ (∀ l, CdRange S l → xtB1 lyEB ≤ l → CdLower S l) ∧
      (∀ l, CdRange S l → l < xtB1 lyEB → upsilon l = l → cdTheta S l (cdCode S l) = xtOrec lyEB l) := by
  have hcp : Cp.cpB1 ≤ xtB1 lyEB :=
    (lyB_cp_le.trans lyE_order.2.le)
  refine ⟨fun l hr h => hU l hr (hcp.trans h), fun l hr h => hL l hr (hcp.trans h), fun l hr hlB hfix => ?_⟩
  rcases lt_or_ge l Cp.cpB1 with h | h
  · rw [lyEB_vz hr.1 h]; exact hT l hr h hfix
  · exact (lyE_iff hr.1 hlB).1 ⟨hU l hr h, hL l hr h⟩

/-- **The road with UPPER and LOWER asked only at `λ ≥ Λ⁺(lyEB)`**, `Θ_F(m_F) = O_E(F)` at the fixed points of
the range below `Λ⁺(lyEB)`, the cap of the values outside `Λ⁺(lyEB)`, (CL), EQ, TCrest, (EMB₂). -/
theorem lyERoad3 (hU : ∀ l, CdRange S l → xtB1 lyEB ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 lyEB ≤ l → CdLower S l)
    (hT : ∀ l, CdRange S l → l < xtB1 lyEB → upsilon l = l → cdTheta S l (cdCode S l) = xtOrec lyEB l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lyEB) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad3 (xtSpec1 lyEB_topPkg) lyE_nonfix hU hL hT hV hC hEQ hrest hB2

/-- **The road with UPPER, LOWER and the cap of the values asked only outside `Λ⁺(lyEB)`.** -/
theorem lyERoad (hU : ∀ l, CdRange S l → XtOut (xtB1 lyEB) l → CdUpper S l)
    (hL : ∀ l, CdRange S l → XtOut (xtB1 lyEB) l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lyEB) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad (xtSpec1 lyEB_topPkg) lyE_nonfix hU hL hV hC hEQ hrest hB2

/-- **The road with the caps asked only outside `Λ⁺(lyEB)`**: CAP-0, CAP-1 outside, (CL), (TC), (EMB₂). -/
theorem lyERoad_cap
    (h0 : ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → XtOut (xtB1 lyEB) l → CdCapAt S l)
    (h1 : ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < Nc.ncL S ω →
      cdCode S l < Nc.ncPp S → XtOut (xtB1 lyEB) l → CdCapAt S l) (hC : CdCL S) (hTC : CdTC S)
    (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad_cap (xtSpec1 lyEB_topPkg) lyE_nonfix h0 h1 hC hTC hB2

/-- **The offset at an isolated fixed point below `Λ⁺(lyEB)`**: `O_E(F) = F`. -/
theorem lyE_iso {F : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hFB : F < xtB1 lyEB)
    (hiso : CpIso F) : xtOrec lyEB F = F :=
  xtIso hF hfix (hFB.trans (xtB1_lt_Om1 lyEB_topPkg)) hiso

/-- **ENUM-REACH at an isolated fixed point of the range below `Λ⁺(lyEB)` reduces to the code**:
`F ≤ m_F ⇒ UPPER(F)` and `m_F ≤ Ω₁ ⇒ LOWER(F)`. -/
theorem lyE_fix_code {F : Ordinal.{0}} (hr : CdRange S F) (hfix : upsilon F = F) (hFB : F < xtB1 lyEB)
    (hiso : CpIso F) : (F ≤ cdCode S F → CdUpper S F) ∧ (cdCode S F ≤ Om1 → CdLower S F) :=
  xtFix_code (xtSpec1 lyEB_topPkg) hr.1 hfix hFB (lyE_iso hr.1 hfix hFB hiso) (cp_name_L hr.2.2.1)

end Googology.Trans.PoR.InaccPsi.R2.Ly
