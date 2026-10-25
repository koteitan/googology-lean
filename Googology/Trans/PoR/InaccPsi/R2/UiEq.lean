import Googology.Trans.PoR.InaccPsi.R2.UiUB

/-!
# The `ψ_{Ω_{s+1}} ↔ H^s_γ` lemma at every level `γ < ε_{Ω_{s+1}+1}`, for every finite `s`

`ψ = S.psi · W`, `W = Ω_{s+1}`, `L = Ω_s`, `E = uiE s`, `H_γ = uiH s γ`, `uiC s γ` the largest component, `UiLt s q x`
(all components of `x` below `q`).  An argument `B` is *own* when `B ∈ Cl(B, ψ(B))`.  This is `R2.UcEq` (`s = 1`) for
every `s < ω`; the level `0` is done here from the hull alone (no Veblen hierarchy over `L`): `H_0` enumerates the
strongly critical points above `L`.

* `ui_mem` (**the hull converse**: `x < E` with all components below `b` and `W·x` lie in `Cl(a, b)`), `ui_Wpow_mem`
  (`W^γ·D ∈ Cl(a, b)`), `uiLt_succ`, `uiC_le_succ`, `ui_own_comps` (**the components of an own `B < E` are below
  `ψ(B)`**);
* `UiFWD`, `UiCONV`, `ui_lb0` (**`H_0(c + d) ≤ ψ(B + d)`** along a valid `D`), `ui_fix0` (**`ψ(B)` is a fixed point of
  `H_0` for every own `B ≠ 0` with `W ∣ B`**), `ui_fwd0`, `ui_fwd_conv` (**FWD(γ)**: `ψ(B)` is a fixed point of `H_γ`
  for every own `B ≠ 0` with `W^{γ+1} ∣ B` and `uiC s γ < ψ(B)`; **CONV(γ)**: `W^{γ+1} ∣ B` for every own `B < E` with
  `ψ(B)` a fixed point of `H_γ`; at every level `γ < E`);
* `ui_eq` (**`ψ(B + W^γ·D) = H_γ(c + D)` and `D < ψ(B + W^γ·D)`** for an own `B < E` with `W^γ ∣ B`, `H_γ(c) =
  ψ(B)`, `D < W` with `d < H_γ(c + d)` for every `d ≤ D`, given FWD below `γ`), `ui_eq_all` (FWD discharged),
  `ui_psiU_mul_all` (**`ψ(W^γ·(1 + D)) = H_γ(c + D)`** for `H_γ(c) = ψ(W^γ)`, `uiC s γ < ψ(W^γ)`).

No new axiom.  New definitions: the statement names `UiFWD`, `UiCONV`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ui

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uc

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

/-- **The hull converse**: `x < E` with all components below `b > 0` lies in `Cl(a, b)`, and so does `W·x`. -/
theorem ui_mem (hs : s < ω) {a b : Ordinal.{0}} (hb : 0 < b) :
    ∀ x, x < uiE s → UiLt s b x → x ∈ S.CSet a b ∧ (Om (s + 1)) * x ∈ S.CSet a b := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hxE hx
  by_cases hx2 : x < Om (s + 1)
  · have hxb := (uiLt_small hx2).1 hx
    exact ⟨CSet.of_lt hxb, ui_W_mul_mem hs hxb⟩
  have hx2' := not_lt.1 hx2
  have hx0 : x ≠ 0 := ui_ne_zero hx2'
  set e := log (Om (s + 1)) x with hedef
  set d := x / Om (s + 1) ^ e with hddef
  set r := x % Om (s + 1) ^ e with hrdef
  have he1 : 1 ≤ e := one_le_iff_ne_zero.2 (log_pos (ui_one_lt_W s) hx0 hx2').ne'
  have hcnf : Om (s + 1) ^ e * d + r = x := (ui_cnf_eq s) x
  have hr : r < Om (s + 1) ^ e := Ordinal.mod_lt _ ((ui_W_pos s) e).ne'
  have hd : d < Om (s + 1) := (ui_div_lt s) x
  have hd0 : d ≠ 0 := (ui_div_pos hx2').ne'
  have hx' := hx
  rw [← hcnf, uiLt_cnf he1 hd0 hd hr (by rw [hcnf]; exact hxE)] at hx'
  obtain ⟨hxe, hdb, hxr⟩ := hx'
  have hel := ui_log_lt hx2' hxE
  have hrl := ui_mod_lt hx2'
  obtain ⟨-, heM⟩ := IH e hel (hel.trans hxE) hxe
  obtain ⟨hrM, hrM2⟩ := IH r hrl (hrl.trans hxE) hxr
  have hW : Om (s + 1) ^ e * d ∈ S.CSet a b := by
    rw [ui_W_eq s]; exact Nm.mem_opow_mul heM hdb
  have hW2 : (Om (s + 1)) * (Om (s + 1) ^ e * d) ∈ S.CSet a b := by
    have h1 : (Om (s + 1)) * (Om (s + 1) ^ e * d) = ω ^ ((Om (s + 1)) + (Om (s + 1)) * e) * d := by
      rw [← mul_assoc]
      have h2 : ((Om (s + 1)) : Ordinal.{0}) * Om (s + 1) ^ e = Om (s + 1) ^ (1 + e) := by rw [opow_add, opow_one]
      rw [h2, (ui_W_eq s), mul_add, mul_one]
    rw [h1]; exact Nm.mem_opow_mul (CSet.add_mem (ui_W_mem hs _ _) heM) hdb
  refine ⟨?_, ?_⟩
  · rw [← hcnf]; exact CSet.add_mem hW hrM
  · rw [← hcnf, mul_add]; exact CSet.add_mem hW2 hrM2

/-- `W^γ·D ∈ Cl(a, b)` for `γ < E` with all components below `b`, `D < b`. -/
theorem ui_Wpow_mem (hs : s < ω) {a b γ D : Ordinal.{0}} (hγ : γ < uiE s) (hγb : UiLt s b γ) (hD : D < b) :
    Om (s + 1) ^ γ * D ∈ S.CSet a b := by
  rw [ui_W_eq s]; exact Nm.mem_opow_mul (ui_mem hs (zero_le.trans_lt hD) γ hγ hγb).2 hD

theorem uiLt_succ {q x : Ordinal.{0}} (hq : SC q) (hE : x + 1 < uiE s) (hx : UiLt s q x) : UiLt s q (x + 1) :=
  uiLt_add hq hE hx ((uiLt_small (ui_one_lt_W s)).2 (ui_one_lt_SC hq))

/-- `uiC s j ≤ uiC s (j + 1)`. -/
theorem uiC_le_succ (s : Ordinal.{0}) : ∀ j : Ordinal.{0}, uiC s j ≤ uiC s (j + 1) := by
  intro j
  induction j using WellFoundedLT.induction with
  | ind j IH =>
  by_cases h1 : j < Om (s + 1)
  · rw [uiC_small h1, uiC_small ((ui_SC_W s).add_one_lt h1)]; exact le_self_add
  by_cases h2 : j + 1 < uiE s
  · have hjE : j < uiE s := (lt_add_one j).trans h2
    have h1' := not_lt.1 h1
    set e := log (Om (s + 1)) j with hedef
    set d := j / Om (s + 1) ^ e with hddef
    set r := j % Om (s + 1) ^ e with hrdef
    have he1 : 1 ≤ e := one_le_iff_ne_zero.2 (log_pos (ui_one_lt_W s) (ui_ne_zero h1') h1').ne'
    have hcnf : Om (s + 1) ^ e * d + r = j := (ui_cnf_eq s) j
    have hr : r < Om (s + 1) ^ e := Ordinal.mod_lt _ ((ui_W_pos s) e).ne'
    have hr1 : r + 1 < Om (s + 1) ^ e := ((ui_W_indec s) e).add_lt hr
      (((ui_one_lt_W s)).trans_le ((opow_one ((Om (s + 1)) : Ordinal.{0})).symm.trans_le
        ((opow_le_opow_iff_right (ui_one_lt_W s)).2 he1)))
    have hd : d < Om (s + 1) := (ui_div_lt s) j
    have hd0 : d ≠ 0 := (ui_div_pos h1').ne'
    have e1 : j + 1 = Om (s + 1) ^ e * d + (r + 1) := by rw [← add_assoc, hcnf]
    unfold uiC
    rw [e1, uiFold_cnf id he1 hd0 hd hr1 (by rw [← e1]; exact h2)]
    conv_lhs => rw [← hcnf, uiFold_cnf id he1 hd0 hd hr (by rw [hcnf]; exact hjE)]
    exact max_le_max le_rfl (max_le_max le_rfl (IH r (ui_mod_lt h1')))
  · have hj : uiE s ≤ j := by
      by_contra h; exact h2 ((ui_E_indec s) (not_le.1 h) ((ui_one_lt_W s).trans (uiE_gt s)))
    unfold uiC; rw [uiFold_out id hj]; exact zero_le


/-- **The components of an own `B < E` are below `ψ(B)`.** -/
theorem ui_own_comps (hs : s < ω) {B : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om (s + 1)))) (hBE : B < uiE s) :
    UiLt s (S.psi B (Om (s + 1))) B := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  have hq2 : S.psi B (Om (s + 1)) < Om (s + 1) := ui_psi_lt B
  refine ui_hull hs (ui_psi_SC B) (ui_L_lt_psi B) hq2 hBE.le (fun e he heC _ => ?_) B hown
  exact lt_psi_of_mem hκ (CSet.psi_mem he hκ (mem_CSet_psi hκ B) heC) (psi_lt hκ _)

/-! ## The fixed-point statements -/

/-- **FWD(γ)**: `ψ(B)` is a fixed point of `H_γ` for every own `B ≠ 0` with `W^{γ+1} ∣ B` and `uiC s γ < ψ(B)`. -/
def UiFWD (s : Ordinal.{0}) (S : InaccSeq.{0}) (γ : Ordinal.{0}) : Prop :=
  ∀ B : Ordinal.{0}, B ∈ S.CSet B (S.psi B (Om (s + 1))) → Om (s + 1) ^ (γ + 1) ∣ B → B ≠ 0 →
    uiC s γ < S.psi B (Om (s + 1)) → uiH s γ (S.psi B (Om (s + 1))) = S.psi B (Om (s + 1))

/-- **CONV(γ)**: `W^{γ+1} ∣ B` for every own `B < E` with `ψ(B)` a fixed point of `H_γ`. -/
def UiCONV (s : Ordinal.{0}) (S : InaccSeq.{0}) (γ : Ordinal.{0}) : Prop :=
  ∀ B : Ordinal.{0}, B ∈ S.CSet B (S.psi B (Om (s + 1))) → B < uiE s →
    uiH s γ (S.psi B (Om (s + 1))) = S.psi B (Om (s + 1)) → Om (s + 1) ^ (γ + 1) ∣ B

/-- **The lower bound at level `0`**: for an own `B` with `ψ(B) = H_0(c)` and `d < H_0(c + d)` for every `d ≤ D`:
`H_0(c + d) ≤ ψ(B + d)` for every `d ≤ D` (`H_0` enumerates the strongly critical points above `L`). -/
theorem ui_lb0 {B c D : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om (s + 1))))
    (hc : uiH s 0 c = S.psi B (Om (s + 1))) (hcond : ∀ d, d ≤ D → d < uiH s 0 (c + d)) :
    ∀ d, d ≤ D → uiH s 0 (c + d) ≤ S.psi (B + d) (Om (s + 1)) := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  intro d
  induction d using WellFoundedLT.induction with
  | ind d IH =>
  intro hd
  -- the collapses `ψ(B + d')`, `d' < d`, are below `ψ(B + d)`
  have hmono : ∀ d', d' < d → S.psi (B + d') (Om (s + 1)) < S.psi (B + d) (Om (s + 1)) := by
    intro d' hd'
    have h1 : d' < S.psi (B + d) (Om (s + 1)) :=
      (hcond d' (hd'.le.trans hd)).trans_le ((IH d' hd' (hd'.le.trans hd)).trans
        (psi_mono (S := S) hκ ((add_le_add_iff_left B).2 hd'.le)).1)
    have hmem : B + d' ∈ S.CSet (B + d) (S.psi (B + d) (Om (s + 1))) :=
      CSet.add_mem ((psi_mono (S := S) hκ (le_self_add : B ≤ B + d)).2 hown) (CSet.of_lt h1)
    exact psi_lt_psi_of_mem hκ ((add_lt_add_iff_left B).2 hd') hmem
  rcases zero_or_succ_or_isSuccLimit d with h0 | ⟨d0, rfl⟩ | hlim
  · rw [h0, add_zero, add_zero, hc]
  · rw [Order.succ_eq_add_one] at hmono hd ⊢
    have h1 := (IH d0 (Order.lt_succ d0) ((Order.le_succ d0).trans hd)).trans_lt (hmono d0 (lt_add_one d0))
    obtain ⟨e, he⟩ := uiH_zero_range (s := s) (ui_psi_SC (S := S) (B + (d0 + 1))) (ui_L_lt_psi _)
    rw [← he] at h1 ⊢
    rw [← add_assoc]
    exact (uiH_le_iff (s := s) 0).2 (Order.add_one_le_of_lt ((uiH_lt_iff (s := s) 0).1 h1))
  · refine ((uiH_normal (s := s) 0).le_iff_forall_le (isSuccLimit_add c hlim)).2 fun z hz => ?_
    rcases lt_or_ge z c with hzc | hcz
    · exact ((uiH_le_iff (s := s) 0).2 hzc.le).trans (by
        rw [hc]; exact (psi_mono (S := S) hκ le_self_add).1)
    · have hσe : c + (z - c) = z := Ordinal.add_sub_cancel_of_le hcz
      have hσ : z - c < d := by rw [← hσe] at hz; exact (add_lt_add_iff_left c).1 hz
      rw [← hσe]
      exact (IH _ hσ (hσ.le.trans hd)).trans (hmono _ hσ).le

/-- **`ψ(B)` is a fixed point of `H_0`** for every own `B ≠ 0` with `W ∣ B` (else `ψ(B) = H_0(c + D) ≤ ψ(B_p + D)`
with `B_p + D < B` in `Cl(B, ψ(B))`, `ψ(B_p) = H_0(c)` the first own collapse at or above the largest fixed point of
`H_0` (or `ψ(0)`) below `ψ(B)`). -/
theorem ui_fix0 (hs : s < ω) {B : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om (s + 1))))
    (hdvd : Om (s + 1) ∣ B) (hB0 : B ≠ 0) :
    uiH s 0 (S.psi B (Om (s + 1))) = S.psi B (Om (s + 1)) := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  set x := S.psi B (Om (s + 1)) with hxdef
  set τ := S.psi 0 (Om (s + 1)) with hτdef
  have hxSC : SC x := ui_psi_SC B
  have hx2 : x < Om (s + 1) := ui_psi_lt B
  have hτx : τ < x := ui_psi0_lt hB0
  have hτ1 : Om s < τ := ui_L_lt_psi 0
  by_contra hnf
  obtain ⟨y, hy⟩ := uiH_zero_range (s := s) hxSC (ui_L_lt_psi B)
  have hyx : y < x := by
    refine lt_of_le_of_ne (hy ▸ uiH_le_self (s := s) 0 y) fun e => hnf ?_
    rw [← e] at hy ⊢; rw [hy]
  obtain ⟨p, hbase, hpx, hmax⟩ := ui_base_below (uiH_normal (s := s) 0) hτx hnf
  have hτp : τ ≤ p := by
    rcases hbase with e | ⟨h, -⟩
    · exact e.ge
    · exact h.le
  have hpSC : SC p := by
    rcases hbase with e | ⟨-, h⟩
    · rw [e]; exact ui_psi_SC 0
    · rw [← h]; exact uiH_SC (s := s) 0 p
  obtain ⟨Bp, hownp, hpBp, hBpx⟩ : ∃ Bp, Bp ∈ S.CSet Bp (S.psi Bp (Om (s + 1))) ∧
      p ≤ S.psi Bp (Om (s + 1)) ∧ S.psi Bp (Om (s + 1)) < x := by
    rcases hbase with e | -
    · exact ⟨0, CSet.zero_mem _ _, e.le, hτx⟩
    · exact ui_own_below hs hpSC (hτ1.trans_le hτp) hpx
  obtain ⟨c, hc⟩ := uiH_zero_range (s := s) (ui_psi_SC (S := S) Bp) (ui_L_lt_psi Bp)
  have hcy : c < y := (uiH_lt_iff (s := s) 0).1 (by rw [hc, hy]; exact hBpx)
  set D := y - c with hDdef
  have hcD : c + D = y := Ordinal.add_sub_cancel_of_le hcy.le
  have hcond : ∀ d, d ≤ D → d < uiH s 0 (c + d) := by
    intro d hd
    by_contra hle
    push Not at hle
    have hz : uiH s 0 (c + d) = c + d :=
      le_antisymm (hle.trans le_add_self) (uiH_le_self (s := s) 0 _)
    have hzy : c + d ≤ y := by rw [← hcD]; exact (add_le_add_iff_left c).2 hd
    have hcz : uiH s 0 c ≤ c + d := by rw [← hz]; exact (uiH_le_iff (s := s) 0).2 le_self_add
    have hpz : p ≤ c + d := hpBp.trans (by rw [← hc]; exact hcz)
    rcases hpz.lt_or_eq with hpz | hpz
    · exact absurd (hmax _ hz (hτp.trans_lt hpz) (hzy.trans_lt hyx)) (not_le.2 hpz)
    · have hcp : uiH s 0 c = uiH s 0 (c + d) := by
        refine le_antisymm ((uiH_le_iff (s := s) 0).2 le_self_add) ?_
        rw [hz, ← hpz, hc]; exact hpBp
      have hcc : c = c + d := (uiH_normal (s := s) 0).strictMono.injective hcp
      have hd0 : d = 0 := by
        have : c + d = c + 0 := by rw [add_zero, ← hcc]
        exact add_left_cancel this
      rw [hd0, add_zero] at hle
      exact absurd hle (not_le.2 (uiH_SC (s := s) 0 c).1)
  have hDx : D < x := (Ordinal.sub_le_self y c).trans_lt hyx
  have hlb := ui_lb0 hownp hc hcond D le_rfl
  rw [hcD, hy] at hlb
  have hBpB : Bp < B := (ui_own_lt_iff hownp hown).1 hBpx
  have hlt2 : Bp + D < B := Rd.rd_add_lt_of_dvd (ui_W_indec' s) hdvd hBpB (hDx.trans hx2)
  have hmem : Bp + D ∈ S.CSet B x :=
    CSet.add_mem ((psi_mono (S := S) hκ hBpB.le).2 hownp) (CSet.of_lt hDx)
  have hψmem : S.psi (Bp + D) (Om (s + 1)) ∈ S.CSet B x :=
    CSet.psi_mem hlt2 hκ (mem_CSet_psi hκ B) hmem
  have := lt_psi_of_mem hκ hψmem (ui_psi_lt _)
  exact absurd (hlb.trans_lt this) (lt_irrefl _)

/-- **FWD(0).** -/
theorem ui_fwd0 (hs : s < ω) : UiFWD s S 0 := fun B hown hB hB0 _ =>
  ui_fix0 hs hown (by rwa [zero_add, opow_one] at hB) hB0

/-- **FWD(γ) and CONV(γ) at every level `γ < E`.** -/
theorem ui_fwd_conv (hs : s < ω) : ∀ γ : Ordinal.{0}, γ < uiE s → UiFWD s S γ ∧ UiCONV s S γ := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγ
  constructor
  · -- FWD
    intro B hown hB hB0 hCx
    rcases eq_or_ne γ 0 with rfl | hγ0
    · exact ui_fwd0 hs B hown hB hB0 hCx
    set x := S.psi B (Om (s + 1)) with hxdef
    have hx2 : x < Om (s + 1) := ui_psi_lt B
    have hxSC : SC x := ui_psi_SC B
    have hx1 : (Om s) < x := ui_L_lt_psi B
    have hxΓ : uiH s 0 x = x := by
      have h1 : Om (s + 1) ^ ((0 : Ordinal.{0}) + 1) ∣ B :=
        (opow_dvd_opow _ (by rw [zero_add]; exact one_le_iff_ne_zero.2 (by
          rw [← Order.one_le_iff_ne_zero]; exact le_add_self))).trans hB
      have h0 : uiC s 0 < x := by rw [uiC_small (ui_SC_W s).1]; exact hxSC.1
      exact (IH 0 (pos_iff_ne_zero.2 hγ0) ((ui_SC_W s).1.trans (uiE_gt s))).1 B hown h1 hB0 h0
    have hlimx : IsSuccLimit x := hxSC.isSuccLimit
    set u := Om (s + 1) ^ γ with hudef
    have hu0 : u ≠ 0 := ((ui_W_pos s) γ).ne'
    have hupos : 0 < u := (ui_W_pos s) γ
    obtain ⟨m, hm⟩ := hB
    rw [(ui_W_succ s), ← hudef, mul_assoc] at hm
    have hγLt : ∀ w, uiC s γ < w → UiLt s w γ := fun w hw => (uiC_lt_iff (zero_le.trans_lt hw) γ).1 hw
    have key : ∀ z < x, uiH s γ z < x := by
      intro z hz
      have hxI : Indec x := Lq.lq_SC_indec hxSC
      set a := Om s + uiC s γ + z + 1 with hadef
      have hax : a < x := hxSC.add_one_lt (hxI.add_lt (hxI.add_lt hx1 hCx) hz)
      set p := uiH s 0 a with hpdef
      have hpx : p < x := by rw [← hxΓ]; exact (uiH_lt_iff (s := s) 0).2 hax
      have hpSC : SC p := uiH_SC (s := s) 0 a
      have hap : a < p := uiH_zero_lt _
      have hCp : uiC s γ < p := by
        refine lt_of_le_of_lt ?_ hap
        rw [hadef]; exact le_add_self.trans (le_self_add.trans le_self_add)
      have hz1p : z + 1 < p := by
        refine lt_of_le_of_lt ?_ hap
        rw [hadef, add_assoc]; exact le_add_self
      have hp1 : (Om s) < p := by
        refine lt_of_le_of_lt ?_ hap
        rw [hadef]; exact le_self_add.trans (le_self_add.trans le_self_add)
      obtain ⟨Bp, hownp, hBpB, hpBp, -⟩ := ui_own_below_lt hs hown hpSC hp1 hpx
      set e := u * (Bp / u) + u with hedef
      have hBpe : Bp ≤ e := by
        calc Bp = u * (Bp / u) + Bp % u := (Ordinal.div_add_mod Bp u).symm
          _ ≤ e := add_le_add_right (Ordinal.mod_lt Bp hu0).le _
      have hpe : p ≤ S.psi e (Om (s + 1)) := hpBp.trans (psi_mono hκ hBpe).1
      have hCe : uiC s γ < S.psi e (Om (s + 1)) := hCp.trans_le hpe
      have hBpmem : Bp ∈ S.CSet e (S.psi e (Om (s + 1))) := (psi_mono hκ hBpe).2 hownp
      have hmod : u * (Bp / u) ∈ S.CSet e (S.psi e (Om (s + 1))) := by
        exact ui_mod_mem (S := S) (one_le_iff_ne_zero.2 hγ0) Bp hBpmem
      have huM : u ∈ S.CSet e (S.psi e (Om (s + 1))) := by
        have := ui_Wpow_mem (S := S) (a := e) hs hγ (hγLt _ hCe) (ui_one_lt_SC (ui_psi_SC e))
        rwa [mul_one] at this
      have howne : e ∈ S.CSet e (S.psi e (Om (s + 1))) := CSet.add_mem hmod huM
      have hue : u ∣ e := ⟨Bp / u + 1, by rw [hedef, mul_add, mul_one]⟩
      have hue0 : 0 < e := lt_of_lt_of_le hupos le_add_self
      have hed : ∀ d, d < S.psi e (Om (s + 1)) →
          e + u * d ∈ S.CSet (e + u * d) (S.psi (e + u * d) (Om (s + 1))) ∧
            ∃ w, uiH s γ w = S.psi (e + u * d) (Om (s + 1)) := by
        intro d hd
        have hle : S.psi e (Om (s + 1)) ≤ S.psi (e + u * d) (Om (s + 1)) := (psi_mono hκ le_self_add).1
        have hownd : e + u * d ∈ S.CSet (e + u * d) (S.psi (e + u * d) (Om (s + 1))) :=
          CSet.add_mem ((psi_mono hκ le_self_add).2 howne)
            (ui_Wpow_mem hs hγ (hγLt _ (hCe.trans_le hle)) (hd.trans_le hle))
        refine ⟨hownd, ucG_range (ui_psi_SC _) (ui_L_lt_psi _)
          (hCe.trans_le hle) fun j hj hcj => ?_⟩
        exact (IH j hj (hj.trans hγ)).1 _ hownd
          ((opow_dvd_opow _ (Order.add_one_le_of_lt hj)).trans (dvd_add hue (dvd_mul_right _ _)))
          (lt_of_lt_of_le hue0 le_self_add).ne' hcj
      have hmono : ∀ d d', d < d' → d' < S.psi e (Om (s + 1)) →
          S.psi (e + u * d) (Om (s + 1)) < S.psi (e + u * d') (Om (s + 1)) := fun d d' hdd hd' =>
        ui_psi_lt_of_own (hed d (hdd.trans hd')).1
          ((add_lt_add_iff_left e).2 ((mul_lt_mul_iff_right₀ hupos).2 hdd))
      have hcount : ∀ d, d < S.psi e (Om (s + 1)) → ∀ w, uiH s γ w = S.psi (e + u * d) (Om (s + 1)) →
          d ≤ w := by
        intro d
        induction d using WellFoundedLT.induction with
        | ind d IHd =>
        intro hd w hw
        by_contra hwd
        push Not at hwd
        obtain ⟨w', hw'⟩ := (hed w (hwd.trans hd)).2
        have h1 := IHd w hwd (hwd.trans hd) w' hw'
        have h2 : uiH s γ w' < uiH s γ w := by rw [hw', hw]; exact hmono w d hwd hd
        exact absurd ((uiH_lt_iff (s := s) γ).1 h2) (not_lt.2 h1)
      have hz1e : z + 1 < S.psi e (Om (s + 1)) := hz1p.trans_le hpe
      obtain ⟨w, hw⟩ := (hed (z + 1) hz1e).2
      have hzw : z < w := (lt_add_one z).trans_le (hcount (z + 1) hz1e w hw)
      have hlt : e + u * (z + 1) < B := by
        have hq : Bp / u < Om (s + 1) * m := by
          rw [hm] at hBpB; exact (Ordinal.lt_mul_iff_div_lt hu0).1 hBpB
        have hx2' : x < Om (s + 1) := hx2
        have hc1 : 1 + (z + 1) < Om (s + 1) :=
          (Lq.lq_SC_indec (ui_SC_W s)).add_lt (ui_one_lt_W s) ((ui_SC_W s).add_one_lt (hz.trans hx2'))
        have e1 : e + u * (z + 1) = u * (Bp / u + (1 + (z + 1))) := by
          simp only [hedef, mul_add, mul_one, add_assoc]
        rw [e1, hm]
        exact (mul_lt_mul_iff_right₀ hupos).2
          (Rd.rd_add_lt_of_dvd (Lq.lq_SC_indec (ui_SC_W s)) (dvd_mul_right _ _) hq hc1)
      have hψlt : S.psi (e + u * (z + 1)) (Om (s + 1)) < x :=
        psi_lt_psi_of_mem hκ hlt ((psi_mono hκ hlt.le).2 (hed (z + 1) hz1e).1)
      calc (uiH s) γ z < uiH s γ w := (uiH_lt_iff (s := s) γ).2 hzw
        _ = _ := hw
        _ < x := hψlt
    exact le_antisymm (((uiH_normal (s := s) γ).le_iff_forall_le hlimx).2 fun z hz => (key z hz).le)
      (uiH_le_self (s := s) γ x)
  · -- CONV
    intro B hown hBE hfix
    set p := S.psi B (Om (s + 1)) with hpdef
    have hpSC : SC p := ui_psi_SC B
    have hcomp : UiLt s p B := ui_own_comps hs hown hBE
    have hu : Om (s + 1) ^ γ ∣ B := by
      rcases zero_or_succ_or_isSuccLimit γ with hz | ⟨j, rfl⟩ | hl
      · rw [hz, opow_zero]; exact one_dvd B
      · rw [Order.succ_eq_add_one] at hfix hγ ⊢
        have hC1 := uiH_C_lt (s := s) (j + 1) p
        rw [hfix] at hC1
        have hCj : uiC s j < p := ((uiC_le_succ s) j).trans_lt hC1
        have hfixj : uiH s j p = p := ucG_fix_mono le_self_add hfix hCj
        exact (IH j (Order.lt_succ j) ((lt_add_one j).trans hγ)).2 B hown hBE hfixj
      · by_contra hnd
        have hR0 : B % Om (s + 1) ^ γ ≠ 0 := fun h => hnd (Ordinal.dvd_of_mod_eq_zero h)
        have hRlt : B % Om (s + 1) ^ γ < Om (s + 1) ^ γ := Ordinal.mod_lt _ ((ui_W_pos s) γ).ne'
        have hRc : UiLt s p (B % Om (s + 1) ^ γ) := (uiLt_div_mod hpSC.1 hBE hcomp γ).2
        have hRE : B % Om (s + 1) ^ γ < uiE s := hRlt.trans (ui_W_lt_E hγ)
        set R := B % Om (s + 1) ^ γ with hRdef
        set j0 := log (Om (s + 1)) R with hj0
        have hj0l : j0 < γ := by
          have h1 : Om (s + 1) ^ j0 ≤ R := opow_log_le_self _ hR0
          exact (opow_lt_opow_iff_right (ui_one_lt_W s)).1 (h1.trans_lt hRlt)
        have hj0c : UiLt s p j0 := by
          rcases lt_or_ge R (Om (s + 1)) with hR2 | hR2
          · rw [hj0, log_eq_zero hR2]; exact uiLt_zero hpSC.1
          · have hcn := uiLt_cnf (q := p) (one_le_iff_ne_zero.2 (log_pos (ui_one_lt_W s) hR0 hR2).ne')
              (ui_div_pos hR2).ne' ((ui_div_lt s) R) (Ordinal.mod_lt _ ((ui_W_pos s) _).ne')
              (by rw [(ui_cnf_eq s)]; exact hRE)
            rw [(ui_cnf_eq s)] at hcn
            exact (hcn.1 hRc).1
        have hj1l : j0 + 1 < γ := hl.add_one_lt hj0l
        have hj1E : j0 + 1 < uiE s := hj1l.trans hγ
        have hj1c : uiC s (j0 + 1) < p := (uiC_lt_iff hpSC.1 _).2 (uiLt_succ hpSC hj1E hj0c)
        have hfixj : uiH s (j0 + 1) p = p := ucG_fix_mono hj1l.le hfix hj1c
        have hdiv := (IH (j0 + 1) hj1l hj1E).2 B hown hBE hfixj
        have hd2 : Om (s + 1) ^ (j0 + 1 + 1) ∣ Om (s + 1) ^ γ * (B / Om (s + 1) ^ γ) :=
          (opow_dvd_opow _ (Order.add_one_le_of_lt hj1l)).trans (dvd_mul_right _ _)
        have hdR : Om (s + 1) ^ (j0 + 1 + 1) ∣ R := by
          have h := hdiv
          rw [← Ordinal.div_add_mod B (Om (s + 1) ^ γ)] at h
          exact (Ordinal.dvd_add_iff hd2).1 h
        have h1 : Om (s + 1) ^ (j0 + 1 + 1) ≤ R := Ordinal.le_of_dvd hR0 hdR
        have h2 : R < Om (s + 1) ^ (j0 + 1) := lt_opow_succ_log_self (ui_one_lt_W s) R
        have h3 : Om (s + 1) ^ (j0 + 1) ≤ Om (s + 1) ^ (j0 + 1 + 1) := opow_le_opow_right (ui_SC_W s).1 le_self_add
        exact absurd (h3.trans h1) (not_le.2 h2)
    set u := Om (s + 1) ^ γ with hudef
    set u2 := Om (s + 1) ^ (γ + 1) with hu2def
    have hu2 : u2 = u * (Om (s + 1)) := (ui_W_succ s) γ
    have huu2 : u ∣ u2 := opow_dvd_opow _ le_self_add
    have hupos : 0 < u := (ui_W_pos s) γ
    have hu0 : u ≠ 0 := hupos.ne'
    obtain ⟨m, hm⟩ := hu
    by_contra hnd
    set D0 := m % (Om (s + 1)) with hD0
    set B0 := u2 * (m / (Om (s + 1))) with hB0
    have hBe : B0 + u * D0 = B := by
      rw [hm, hB0, hD0, hu2, mul_assoc, ← mul_add, Ordinal.div_add_mod]
    have hD0lt : D0 < Om (s + 1) := Ordinal.mod_lt m (ui_SC_W s).1.ne'
    have hD00 : D0 ≠ 0 := by
      intro e
      apply hnd
      rw [← hBe, e, mul_zero, add_zero, hB0]
      exact dvd_mul_right _ _
    have hmdiv : B / u = m := by rw [hm, Ordinal.mul_div_cancel _ hu0]
    have hD0p : D0 < p := by
      have := ui_dig_lt hpSC.1 hBE hcomp γ
      rwa [← hudef, hmdiv] at this
    have hlt' : u * D0 < u2 := by rw [hu2]; exact (mul_lt_mul_iff_right₀ hupos).2 hD0lt
    have hBdiv : B / u2 = m / (Om (s + 1)) := by
      calc B / u2 = (u2 * (m / (Om (s + 1))) + u * D0) / u2 := by rw [← hB0, hBe]
        _ = m / (Om (s + 1)) := by
          rw [Ordinal.mul_add_div _ ((ui_W_pos s) _).ne', Ordinal.div_eq_zero_of_lt hlt', add_zero]
    have hB0m : B0 ∈ S.CSet B p := by
      have := ui_mod_mem (S := S) (s := s) (m := γ + 1) le_add_self B hown
      rwa [← hu2def, hBdiv] at this
    have hB0B : B0 < B := by
      rw [← hBe]; exact lt_add_of_pos_right _ (mul_pos hupos (pos_iff_ne_zero.2 hD00))
    have hB0p : S.psi B0 (Om (s + 1)) < p := psi_lt_psi_of_mem hκ hB0B hB0m
    have hle := uiUB (S := S) hs hγ B0 (S.psi B0 (Om (s + 1))) D0
      (by rw [hB0]; exact huu2.trans (dvd_mul_right _ _)) (hB0B.trans hBE) (uiH_le_self (s := s) _ _) hD0lt.le
    rw [hBe] at hle
    have hlt : S.psi B0 (Om (s + 1)) + D0 < p := (Lq.lq_SC_indec hpSC).add_lt hB0p hD0p
    have h2 : uiH s γ (S.psi B0 (Om (s + 1)) + D0) < p := by
      conv_rhs => rw [← hfix]
      exact (uiH_lt_iff (s := s) γ).2 hlt
    exact absurd (hle.trans_lt h2) (lt_irrefl _)

/-! ## The bridge at level `γ` -/

/-- **`ψ(B + W^γ·D) = H_γ(c + D)`, and `D < ψ(B + W^γ·D)`**, when `d < H_γ(c + d)` for every `d ≤ D`, for an own
`B < E` with `W^γ ∣ B` and `H_γ(c) = ψ(B)`, `D < W`, given FWD below `γ < E`. -/
theorem ui_eq (hs : s < ω) {γ : Ordinal.{0}} (hγ : γ < uiE s) (hF : ∀ j < γ, UiFWD s S j)
    {B c : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om (s + 1)))) (hB : Om (s + 1) ^ γ ∣ B) (hBE : B < uiE s)
    (hc : uiH s γ c = S.psi B (Om (s + 1))) :
    ∀ D, D < Om (s + 1) → (∀ d, d ≤ D → d < uiH s γ (c + d)) →
      D < S.psi (B + Om (s + 1) ^ γ * D) (Om (s + 1)) ∧
        S.psi (B + Om (s + 1) ^ γ * D) (Om (s + 1)) = uiH s γ (c + D) := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  set u := Om (s + 1) ^ γ with hudef
  have hupos : 0 < u := (ui_W_pos s) γ
  intro D
  induction D using WellFoundedLT.induction with
  | ind D IH =>
  intro hDΩ hcond
  have hIH : ∀ d, d < D → S.psi (B + u * d) (Om (s + 1)) = uiH s γ (c + d) :=
    fun d hd => (IH d hd (hd.trans hDΩ) fun d' hd' => hcond d' (hd'.trans hd.le)).2
  have heq : S.psi (B + u * D) (Om (s + 1)) = uiH s γ (c + D) := by
    rcases eq_or_ne D 0 with rfl | hD0
    · rw [mul_zero, add_zero, add_zero, hc]
    set v := S.psi (B + u * D) (Om (s + 1)) with hv
    have hvSC : SC v := ui_psi_SC _
    have hBv : S.psi B (Om (s + 1)) < v :=
      ui_psi_lt_of_own hown (lt_add_of_pos_right _ (mul_pos hupos (pos_iff_ne_zero.2 hD0)))
    have hCv : uiC s γ < v := (uiH_C_lt (s := s) γ c).trans (hc ▸ hBv)
    have hγv : UiLt s v γ := (uiC_lt_iff hvSC.1 γ).1 hCv
    have hlt : ∀ d, d < D → uiH s γ (c + d) < v := by
      intro d hd
      have hle : S.psi (B + u * d) (Om (s + 1)) ≤ v :=
        (psi_mono (S := S) hκ ((add_le_add_iff_left B).2 (mul_le_mul_left' hd.le _))).1
      have hdv : d < v := (hcond d hd.le).trans_le (by rw [← hIH d hd]; exact hle)
      have hmem : B + u * d ∈ S.CSet (B + u * D) v :=
        CSet.add_mem ((psi_mono (S := S) hκ (le_self_add : B ≤ B + u * D)).2 hown) (ui_Wpow_mem hs hγ hγv hdv)
      rw [← hIH d hd]
      exact psi_lt_psi_of_mem hκ ((add_lt_add_iff_left B).2 ((mul_lt_mul_iff_right₀ hupos).2 hd)) hmem
    apply le_antisymm
    · exact uiUB hs hγ B c D hB hBE hc.ge hDΩ.le
    · rcases zero_or_succ_or_isSuccLimit D with h0 | ⟨d0, rfl⟩ | hlim
      · exact absurd h0 hD0
      · rw [Order.succ_eq_add_one] at hlt hDΩ ⊢
        have hd0v : d0 < v := (hcond d0 (Order.le_succ d0)).trans (hlt d0 (lt_add_one d0))
        have hDv : d0 + 1 < v := hvSC.add_one_lt hd0v
        have hown1 : B + u * (d0 + 1) ∈ S.CSet (B + u * (d0 + 1)) v :=
          CSet.add_mem ((psi_mono (S := S) hκ (le_self_add : B ≤ B + u * (d0 + 1))).2 hown)
            (ui_Wpow_mem hs hγ hγv hDv)
        have hne : B + u * (d0 + 1) ≠ 0 :=
          (lt_of_lt_of_le (mul_pos hupos (lt_of_le_of_lt zero_le (lt_add_one d0))) le_add_self).ne'
        have hfix : ∀ j < γ, uiC s j < v → ucG (uiC s) (Om s) j v = v := fun j hj hcj =>
          hF j hj _ hown1 ((opow_dvd_opow _ (Order.add_one_le_of_lt hj)).trans
            (dvd_add hB (dvd_mul_right _ _))) hne hcj
        obtain ⟨e, he⟩ := ucG_range (d := uiC s) (L := Om s) hvSC
          (ui_L_lt_psi _) hCv hfix
        have hle' : c + (d0 + 1) ≤ e := by
          refine not_lt.1 fun hlt' => ?_
          have hle : e ≤ c + d0 := by
            rw [← add_assoc] at hlt'; exact Order.lt_add_one_iff.1 hlt'
          have := ((ucG_le_iff (d := uiC s) (L := Om s) γ).2 hle).trans_lt (hlt d0 (lt_add_one d0))
          rw [he] at this
          exact lt_irrefl _ this
        calc (uiH s) γ (c + (d0 + 1)) ≤ ucG (uiC s) (Om s) γ e := (ucG_le_iff (d := uiC s) (L := Om s) γ).2 hle'
          _ = v := he
      · refine not_lt.1 fun hlt' => ?_
        obtain ⟨e, he, hve⟩ := ((uiH_normal (s := s) γ).lt_iff_exists_lt (isSuccLimit_add c hlim)).1 hlt'
        rcases lt_or_ge e c with hec | hce
        · have : uiH s γ e < v := ((uiH_lt_iff (s := s) γ).2 hec).trans_le (by rw [hc]; exact hBv.le)
          exact absurd hve (not_lt.2 this.le)
        · have hσe : c + (e - c) = e := Ordinal.add_sub_cancel_of_le hce
          have hσ : e - c < D := by rw [← hσe] at he; exact (add_lt_add_iff_left c).1 he
          have := hlt _ hσ
          rw [hσe] at this
          exact absurd hve (not_lt.2 this.le)
  exact ⟨by rw [heq]; exact hcond D le_rfl, heq⟩

/-- **The `ψ_{W} ↔ H_γ` lemma at every level `γ < E`** (FWD discharged). -/
theorem ui_eq_all (hs : s < ω) {γ B c D : Ordinal.{0}} (hγ : γ < uiE s) (hown : B ∈ S.CSet B (S.psi B (Om (s + 1))))
    (hB : Om (s + 1) ^ γ ∣ B) (hBE : B < uiE s) (hc : uiH s γ c = S.psi B (Om (s + 1))) (hD : D < Om (s + 1))
    (hcond : ∀ d, d ≤ D → d < uiH s γ (c + d)) :
    D < S.psi (B + Om (s + 1) ^ γ * D) (Om (s + 1)) ∧ S.psi (B + Om (s + 1) ^ γ * D) (Om (s + 1)) = uiH s γ (c + D) :=
  ui_eq hs hγ (fun j hj => (ui_fwd_conv hs j (hj.trans hγ)).1) hown hB hBE hc D hD hcond

/-- **`ψ(W^γ·(1 + D)) = H_γ(c + D)`** for `γ < E` with `uiC s γ < ψ(W^γ) = H_γ(c)`, and a valid `D < W`. -/
theorem ui_psiU_mul_all (hs : s < ω) {γ c D : Ordinal.{0}} (hγ : γ < uiE s)
    (hC : uiC s γ < S.psi (Om (s + 1) ^ γ) (Om (s + 1)))
    (hc : uiH s γ c = S.psi (Om (s + 1) ^ γ) (Om (s + 1))) (hD : D < Om (s + 1))
    (hcond : ∀ d, d ≤ D → d < uiH s γ (c + d)) :
    D < S.psi (Om (s + 1) ^ γ * (1 + D)) (Om (s + 1)) ∧
      S.psi (Om (s + 1) ^ γ * (1 + D)) (Om (s + 1)) = uiH s γ (c + D) := by
  have hown : Om (s + 1) ^ γ ∈ S.CSet (Om (s + 1) ^ γ) (S.psi (Om (s + 1) ^ γ) (Om (s + 1))) := by
    have := ui_Wpow_mem (S := S) (a := Om (s + 1) ^ γ) hs hγ ((uiC_lt_iff (zero_le.trans_lt hC) γ).1 hC)
      (ui_one_lt_SC (ui_psi_SC _))
    rwa [mul_one] at this
  have h := ui_eq_all hs hγ hown dvd_rfl (ui_W_lt_E hγ) hc hD hcond
  rwa [← mul_one (Om (s + 1) ^ γ), mul_assoc, one_mul, ← mul_add] at h

end Googology.Trans.PoR.InaccPsi.R2.Ui
