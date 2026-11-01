import Googology.Trans.PoR.InaccPsi.R2.XxLoc
import Googology.Trans.PoR.InaccPsi.R2.XxStep
import Googology.Trans.PoR.InaccPsi.R2.YcVD

/-!
# YcFront: THE FRONTIER LEMMA OVER `Γ(k)` FOR THE REPAIRED SYSTEMS `Yc.YcVD k`, EVERY `k + 1 < ε₀`

`Xx.xxLayFront` (the skeleton leaf `skLayFront`) is stated over `Xk.XkVD k`, which is EMPTY for `k ≥ 1`
(`Yc.ycVD_empty`), so it is vacuous there.  The construction of `R2.XxStep` (the codes `B + n` read `b(x) + n`,
gate `γ`, on top of the system; the reading system `Xx.XxRS k` with bound `B + ω`; the location `Xx.xxLoc`) uses
the hull fields only in the code system (`GsCS.mem`: codes `c < a`; `GsCS.B_mem`: `B + ω < a`), where `c ≥ B` or
`B + ω < a` gives `k < a` (`yc_k_lt_B`), and `c < a ≤ k` makes `c < ε₀` a constant (`Gc.gc_cst_mem`).  So the
construction goes through for the repaired interface with these two changes and nothing else; this module is that
construction for `Yc.YcVD k` (the declarations of `R2.XxStep` from `xx_B_lim` on, renamed `xx ↦ yc`, the fields
`mem`, `B_mem` of `ycK` re-proved; the code-gate lemmas `Xx.xx_cl_restrict`, `Xx.xx_cl_B`, `Xx.xx_nat_mem`,
`Xx.xx_omega_mem`, the location `Xx.xxLoc`, `Xx.xxEnum`, `Xx.xxCapV` and `Xx.XxRS` are used as they are):

* `YcVD.pkg` (Lemma IMG below the bound field, `Xk.xkPkg_cst`), `yc_k_lt_B` (**`k < B`**), `ycG`, `ycR`, `ycK`,
  `ycLD`, `ycRSk`, `ycVRS` (**THE READING SYSTEM OF THE CODES BELOW `B + ω`**, an `Xx.XxRS k`);
* `ycVD_loc`, `ycVD_enum`, `ycVD_capV` (**the bound of every `YcVD k` with gate below `K` is located**);
* `ycLayFront` (**`Yc.YcLayFront S k` FOR EVERY `k + 1 < ε₀`: the repaired `skLayFront`**), `ycLayFront_zero'`.

When the merge repairs `Xk.XkVD` in place (`0 < a` ↦ `k < a` in `ix_mem`, `mem`), the same two changes in
`Xx.xxK` make `Xx.xxLayFront` non-vacuous and this module redundant.

No new axiom.  New definitions: `ycG`, `ycR`, `ycK`, `ycRSk`, `ycVRS`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yc

open Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq Googology.Trans.PoR.InaccPsi.R2.Gr
  Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Xk
  Googology.Trans.PoR.InaccPsi.R2.Xx
open Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gj Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **LEMMA IMG (gated) FOR A SPECIFIED FUNCTION BELOW THE BOUND FIELD OF A `YcVD k`** (`k + 1 < ε₀`; the argument of
`Xk.XkVD.pkg`). -/
theorem YcVD.pkg {k : Ordinal.{0}} (D : YcVD k) (hk : k + 1 < ε₀) {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
    {g : Ordinal.{0}} {C : Finset Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (hgρ : g < ρ)
    (hC : ∀ c ∈ C, c < ρ) (hT : T ρ ≤ D.Z ρ) (hex : GjEx g C T) : GhPkg g ρ δ T :=
  xkPkg_cst h le_add_self hk hgρ hC (hT.trans_lt (D.Z_G1 ρ h.ρE h.ρ1)) hex

section Step

variable {k : Ordinal.{0}} (D : YcVD k)

theorem yc_B_lim : IsSuccLimit D.B := ev_isSuccLimit_of_inE D.B_E

theorem yc_B_pos : 0 < D.B := D.B_E.pos

theorem yc_Om1_lt_B : Om 1 < D.B := (gcG_Om1_lt k).trans_le D.G_le

theorem yc_E_lt_B : gfE < D.B := gfE_lt_G0.trans_le ((gcG_le zero_le).trans D.G_le)

theorem yc_k_lt_eps (hk : k + 1 < ε₀) : k < ε₀ := (lt_add_one k).trans hk

/-- **`k < B`**: `k < ε₀ ≤ Ω₁ < Γ(k) ≤ B`. -/
theorem yc_k_lt_B (hk : k + 1 < ε₀) : k < D.B :=
  ((yc_k_lt_eps hk).trans_le gc_eps0_le_Om1).trans ((gcG_Om1_lt k).trans_le D.G_le)

theorem yc_Bw_lt1 : D.B + ω < gcG (k + 1) := by
  have hE : InE (gcG (k + 1)) := gg_SC_eps (gcG_SC (k + 1))
  exact (inE_indec hE).add_lt D.B_lt1 (omega0_lt_inE hE)

theorem yc_B_lt_Bw : D.B < D.B + ω := lt_add_of_pos_right _ omega0_pos

theorem yc_Bw_lt_eN : D.B + ω < eN D.B := by
  have hE : InE (eN D.B) := eN_E D.B
  exact (inE_indec hE).add_lt (lt_eN _) (omega0_lt_inE hE)

theorem yc_high_eq {c : Ordinal.{0}} (hBc : D.B ≤ c) (hc : c < D.B + ω) : ∃ n : ℕ, c = D.B + n := by
  have e : D.B + (c - D.B) = c := Ordinal.add_sub_cancel_of_le hBc
  have h1 : c - D.B < ω := (add_lt_add_iff_left D.B).1 (by rw [e]; exact hc)
  obtain ⟨n, hn⟩ := lt_omega0.1 h1
  exact ⟨n, by rw [← hn, e]⟩

/-- **The gate**: that of `D` below `B`, the base gate `γ` from `B` on. -/
noncomputable def ycG (c : Ordinal.{0}) : Ordinal.{0} := if c < D.B then D.g c else D.γ

/-- **The reading**: that of `D` below `B`, `b(x) + (c − B)` from `B` on. -/
noncomputable def ycR (c x : Ordinal.{0}) : Ordinal.{0} := if c < D.B then D.R c x else D.b x + (c - D.B)

theorem ycG_low {c : Ordinal.{0}} (hc : c < D.B) : ycG D c = D.g c := if_pos hc

theorem ycG_high {c : Ordinal.{0}} (hc : D.B ≤ c) : ycG D c = D.γ := if_neg (not_lt.2 hc)

theorem ycR_low {c x : Ordinal.{0}} (hc : c < D.B) : ycR D c x = D.R c x := if_pos hc

theorem ycR_high_gen {c x : Ordinal.{0}} (hc : D.B ≤ c) : ycR D c x = D.b x + (c - D.B) := if_neg (not_lt.2 hc)

theorem ycR_high (n : ℕ) (x : Ordinal.{0}) : ycR D (D.B + n) x = D.b x + n := by
  rw [ycR_high_gen D le_self_add, Ordinal.add_sub_cancel]

theorem yc_R_succ (b x : Ordinal.{0}) : ycR D (b + 1) x = ycR D b x + 1 := by
  rcases lt_or_ge b D.B with hb | hb
  · rw [ycR_low D hb, ycR_low D ((yc_B_lim D).add_one_lt hb), D.R_succ]
  · have e : D.B + (b - D.B) = b := Ordinal.add_sub_cancel_of_le hb
    have e1 : (b + 1) - D.B = (b - D.B) + 1 := by
      conv_lhs => rw [← e, add_assoc]
      exact Ordinal.add_sub_cancel _ _
    rw [ycR_high_gen D hb, ycR_high_gen D (hb.trans le_self_add), e1, add_assoc]

theorem yc_G_le_succ (b : Ordinal.{0}) : ycG D b ≤ ycG D (b + 1) := by
  rcases lt_or_ge b D.B with hb | hb
  · rw [ycG_low D hb, ycG_low D ((yc_B_lim D).add_one_lt hb)]; exact D.g_le_succ b
  · rw [ycG_high D hb, ycG_high D (hb.trans le_self_add)]

section Base

variable (hk : k + 1 < ε₀) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hk hx hx1

/-- **The readings lie below `Γ_{x+2+k}`.** -/
theorem yc_R_lt {c : Ordinal.{0}} (hc : c < D.B + ω) (hg : ycG D c < x) : ycR D c x < gq (k + 1) x := by
  rcases lt_or_ge c D.B with hcB | hcB
  · rw [ycR_low D hcB]; rw [ycG_low D hcB] at hg
    exact (D.R_lt_Z x hx hx1 c hcB hg).trans (D.Z_G1 x hx hx1)
  · rw [ycG_high D hcB] at hg
    obtain ⟨n, rfl⟩ := yc_high_eq D hcB hc
    rw [ycR_high]
    have hq := (xx_facts hx hx1 hk).2.2.2
    have hb : D.b x < gq (k + 1) x :=
      ((lt_eN _).trans (D.b_Z x hx hx1 hg)).trans (D.Z_G1 x hx hx1)
    exact (inE_indec hq).add_lt hb ((natCast_lt_omega0 n).trans (omega0_lt_inE hq))

omit hk in
theorem yc_R_mono {b c : Ordinal.{0}} (hc : c < D.B + ω) (hbc : b < c) (hgb : ycG D b < x)
    (hgc : ycG D c < x) : ycR D b x < ycR D c x := by
  rcases lt_or_ge c D.B with hcB | hcB
  · have hbB := hbc.trans hcB
    rw [ycR_low D hcB, ycR_low D hbB]
    rw [ycG_low D hcB] at hgc; rw [ycG_low D hbB] at hgb
    exact D.mono x hx hx1 c hcB b hbc hgc hgb
  · rw [ycG_high D hcB] at hgc
    obtain ⟨n, rfl⟩ := yc_high_eq D hcB hc
    rw [ycR_high]
    rcases lt_or_ge b D.B with hbB | hbB
    · rw [ycR_low D hbB]; rw [ycG_low D hbB] at hgb
      exact (D.R_lt_b x hx hx1 hgc b hbB hgb).trans_le le_self_add
    · obtain ⟨m, rfl⟩ := yc_high_eq D hbB (hbc.trans hc)
      rw [ycR_high]
      have hmn : (m : Ordinal.{0}) < n := (add_lt_add_iff_left D.B).1 hbc
      exact (add_lt_add_iff_left _).2 hmn

end Base

/-- **The code system of the codes below `B + ω`.** -/
noncomputable def ycK (hk : k + 1 < ε₀) : GsCS where
  B := D.B + ω
  gt := ycG D
  B_V := by
    have hk1 : k + 1 ≤ D.B + ω :=
      ((hk.trans_le gc_eps0_le_Om1).trans (yc_Om1_lt_B D)).le.trans le_self_add
    exact (yc_Bw_lt1 D).trans_le (gcG_le hk1)
  gt_zero := by rw [ycG_low D (yc_B_pos D)]; exact D.g_zero
  gt_lt := fun c hc => by
    rcases lt_or_ge c D.B with hcB | hcB
    · rw [ycG_low D hcB]; exact D.g_lt c hcB
    · rw [ycG_high D hcB]; exact D.γ_lt
  gt_succ := fun b Z hZ hb hg => by
    rcases lt_or_ge b D.B with hbB | hbB
    · have hb1 := (yc_B_lim D).add_one_lt hbB
      rw [ycG_low D hbB] at hg
      rw [ycG_low D hb1]; exact D.g_succ Z hZ b hb1 hg
    · rw [ycG_high D hbB] at hg
      rw [ycG_high D (hbB.trans le_self_add)]; exact hg
  mem := fun S a b c hc hca hg => by
    rcases lt_or_ge c D.B with hcB | hcB
    · rw [ycG_low D hcB] at hg
      rcases lt_or_ge k a with hka | hka
      · exact (D.mem S a b hka c hcB hg).1
      · exact gc_cst_mem a b c ((hca.trans_le hka).trans (yc_k_lt_eps hk))
    · rw [ycG_high D hcB] at hg
      obtain ⟨n, rfl⟩ := yc_high_eq D hcB hc
      have hka : k < a := (yc_k_lt_B D hk).trans_le (le_self_add.trans hca.le)
      have hB : D.B ∈ S.CSet a b := by
        rw [D.B_ix]; exact CSet.phi_mem (CSet.one_mem _ _) (D.ix_mem S a b hka hg)
      exact CSet.add_mem hB (xx_nat_mem n)
  κ := D.γ
  κ_lt := D.γ_lt
  B_mem := fun S a b ha hγb => by
    have hka : k < a := ((yc_k_lt_B D hk).trans (yc_B_lt_Bw D)).trans ha
    have hB : D.B ∈ S.CSet a b := by
      rw [D.B_ix]; exact CSet.phi_mem (CSet.one_mem _ _) (D.ix_mem S a b hka hγb)
    exact CSet.add_mem hB xx_omega_mem
  code_gate := fun Z hZ1 hZ0 hZa hZp c hc hcB => by
    have hAt : ∀ s ∈ {s | ∃ c', c' < D.B + ω ∧ ycG D c' < Z ∧ s = gcG c'}, s ∈ XkAt k ∨ gcG (k + 1) ≤ s := by
      rintro s ⟨c', -, -, rfl⟩
      rcases le_or_gt c' k with h | h
      · exact Or.inl ⟨c', h, rfl⟩
      · exact Or.inr (gcG_le (Order.add_one_le_of_lt h))
    rcases lt_or_ge c D.B with hcB' | hcB'
    · rw [ycG_low D hcB']
      refine D.code_gate Z hZ1 hZ0 hZa hZp _ (fun s hs => (hAt s hs).imp_right fun h => D.B_lt1.le.trans h) c hc hcB'
    · rw [ycG_high D hcB']
      have hZ1' : Z ≤ Om 1 := by rw [← Br.Om1_eq]; exact hZ1
      have h1 := xx_cl_restrict hAt hc (hcB.trans (yc_Bw_lt1 D))
      exact D.γ_cl Z (gr_SC_of hZ0 hZp) hZ1' (xx_cl_B hZ1' D.B_E D.G_le h1 hcB' (hcB.trans (yc_Bw_lt_eN D)))
  count := fun c y hc hy hy1 => by
    have hq1 : gq (k + 1) y < Om (1 : Ordinal.{0}) := by rw [← Br.Om1_eq]; exact (xx_facts hy hy1 hk).2.2.1
    haveI := Gc.gc_countable hq1
    let f : {b : Iio c // ycG D b.1 < y} → Iio (gq (k + 1) y) := fun b =>
      ⟨ycR D b.1.1 y, yc_R_lt D hk hy hy1 (lt_of_lt_of_le b.1.2 hc) b.2⟩
    refine Function.Injective.countable (f := f) fun b b' hbb => ?_
    have e : ycR D b.1.1 y = ycR D b'.1.1 y := congrArg Subtype.val hbb
    rcases lt_trichotomy b.1.1 b'.1.1 with h | h | h
    · exact absurd e (yc_R_mono D hy hy1 (lt_of_lt_of_le b'.1.2 hc) h b.2 b'.2).ne
    · exact Subtype.ext (Subtype.ext h)
    · exact absurd e (yc_R_mono D hy hy1 (lt_of_lt_of_le b.1.2 hc) h b'.2 b.2).ne'

theorem ycK_B (hk : k + 1 < ε₀) : (ycK D hk).B = D.B + ω := rfl

theorem ycK_gt (hk : k + 1 < ε₀) : (ycK D hk).gt = ycG D := rfl

/-- **The decomposition of a limit code** for the reading system: below `B` from `D.ld` (Lemma IMG from
`Xk.XkVD.pkg`), at `B` the `ε`-number `b(x)` itself (Lemma IMG for `b`). -/
theorem ycLD (hk : k + 1 < ε₀) (c : Ordinal.{0}) (hl : IsSuccLimit c) (hEc : gfE < c) (hc : c < D.B + ω) :
    Nonempty (GsmLD (ycK D hk) (ycR D) c) := by
  rcases lt_or_ge c D.B with hcB | hcB
  · obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := D.ld c hl hcB
    have hcpB : cp < D.B := hcp.trans hcB
    have hlg : ∀ x, InE x → x < Om1 → D.g c < x → lg (ycR D c x) = T x := fun x hx hx1 hg => by
      obtain ⟨e1, e2, -, -⟩ := hdec x hx hx1 hg
      rw [ycR_low D hcB, e1]; exact Ge.lg_add_opow e2
    refine ⟨{
      cp := if gfE ≤ cp then cp else gfE
      lp := lp
      cp_ge := ?_
      cp_lt := ?_
      cp_g := ?_
      dec := ?_
      pkg := ?_ }⟩
    · split_ifs with h
      · exact h
      · exact le_rfl
    · split_ifs with h
      · exact hcp
      · exact hEc
    · show ycG D _ ≤ ycG D c
      rw [ycG_low D hcB]
      split_ifs with h
      · rw [ycG_low D hcpB]; exact hgcp
      · rw [ycG_low D (yc_E_lt_B D), D.g_E]; exact zero_le
    · intro x hx hx1 hg
      have hg' : D.g c < x := by rw [← ycG_low D hcB]; exact hg
      obtain ⟨e1, e2, e3, e4⟩ := hdec x hx hx1 hg'
      rw [hlg x hx hx1 hg', ycR_low D hcB]
      refine ⟨e1, e2, e3, ?_⟩
      split_ifs with h
      · rw [ycR_low D hcpB]; exact e4
      · push Not at h
        rw [ycR_low D (yc_E_lt_B D)]
        exact e4.trans (D.mono x hx hx1 gfE (yc_E_lt_B D) cp h (by rw [D.g_E]; exact hx.pos)
          (hgcp.trans_lt hg')).le
    · intro ρ τ δ h hg
      change ycG D c < ρ at hg
      have hg' : D.g c < ρ := by rw [← ycG_low D hcB]; exact hg
      show GhPkg (ycG D c) ρ δ (fun y => lg (ycR D c y))
      rw [ycG_low D hcB]
      have hρE := h.ρE
      obtain ⟨e1, -, -, -⟩ := hdec ρ hρE h.ρ1 hg'
      have hTρ : T ρ ≤ D.Z ρ := by
        have h1 : T ρ ≤ D.R c ρ := by
          rw [e1]; exact (right_le_opow _ one_lt_omega0).trans le_add_self
        exact (h1.trans_lt (D.R_lt_Z ρ hρE h.ρ1 c hcB hg')).le
      have hP := YcVD.pkg D hk h (C := ∅) hg' (by simp) hTρ
        (GjEx.of_bases fun σ ρ' hB hgσ => hex σ ρ' hB hgσ)
      exact GhPkg.congr h hP (fun y hyE hy1 hgy => (hlg y hyE hy1 hgy).symm) hg'
  · obtain ⟨n, rfl⟩ := yc_high_eq D hcB hc
    have hn : n = 0 := by
      by_contra hn
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      have e : D.B + ((m + 1 : ℕ) : Ordinal.{0}) = Order.succ (D.B + m) := by
        rw [Order.succ_eq_add_one, add_assoc]; push_cast; rfl
      rw [e] at hl
      exact Order.not_isSuccLimit_succ _ hl
    subst hn
    have hB0 : D.B + ((0 : ℕ) : Ordinal.{0}) = D.B := by push_cast; rw [add_zero]
    have hlgb : ∀ x, InE x → x < Om1 → D.γ < x → lg (ycR D (D.B + ((0 : ℕ) : Ordinal.{0})) x) = D.b x :=
      fun x hx hx1 hγ => by
        have hbE := D.b_E x hx hx1 hγ
        rw [ycR_high, Nat.cast_zero, add_zero]
        conv_lhs => rw [← hbE, ← zero_add (ω ^ D.b x)]
        exact Ge.lg_add_opow (dvd_zero _)
    refine ⟨{
      cp := gfE
      lp := fun _ => 0
      cp_ge := le_rfl
      cp_lt := by rw [hB0]; exact yc_E_lt_B D
      cp_g := by show ycG D gfE ≤ ycG D _; rw [ycG_low D (yc_E_lt_B D), D.g_E]; exact zero_le
      dec := ?_
      pkg := ?_ }⟩
    · intro x hx hx1 hg
      change ycG D _ < x at hg
      rw [ycG_high D le_self_add] at hg
      have hbE := D.b_E x hx hx1 hg
      rw [hlgb x hx hx1 hg]
      refine ⟨?_, dvd_zero _, hbE.pos.ne', zero_le⟩
      rw [ycR_high, Nat.cast_zero, add_zero, zero_add, hbE]
    · intro ρ τ δ h hg
      change ycG D _ < ρ at hg
      show GhPkg (ycG D _) ρ δ (fun y => lg (ycR D _ y))
      rw [ycG_high D le_self_add] at hg ⊢
      have hρE := h.ρE
      have hT : D.b ρ ≤ D.Z ρ := ((lt_eN _).trans (D.b_Z ρ hρE h.ρ1 hg)).le
      have hP := YcVD.pkg D hk h (C := ∅) hg (by simp) hT
        (GjEx.of_bases fun σ ρ' hB hgσ => D.b_pi σ ρ' hB hgσ)
      exact GhPkg.congr h hP (fun y hyE hy1 hgy => (hlgb y hyE hy1 hgy).symm) hg

/-- **THE READING SYSTEM OF THE CODES BELOW `B + ω`** (as an `Xk.XkRS k`). -/
noncomputable def ycRSk (hk : k + 1 < ε₀) : XkRS k where
  K := ycK D hk
  R := ycR D
  E_lt := (yc_E_lt_B D).trans (yc_B_lt_Bw D)
  B_lim := isSuccLimit_add _ isSuccLimit_omega0
  gt_E := by show ycG D gfE = 0; rw [ycG_low D (yc_E_lt_B D)]; exact D.g_E
  gt_lowE := fun c hc => by
    show ycG D c = gtc c; rw [ycG_low D (hc.trans (yc_E_lt_B D))]; exact D.g_lowE c hc
  R_E := fun x _ _ => by show ycR D gfE x = eN x; rw [ycR_low D (yc_E_lt_B D)]; exact D.R_E x
  lt0 := fun c x hx hx1 hc hg => yc_R_lt D hk hx hx1 hc hg
  mono := fun b c x hx hx1 hc hbc hgb hgc => yc_R_mono D hx hx1 hc hbc hgb hgc
  succ := fun b x _ => yc_R_succ D b x
  gt_le_succ := yc_G_le_succ D
  cof := fun c x hx hx1 hc hEc hg ν hν => by
    show ∃ b, gfE ≤ b ∧ b < c ∧ ycG D b < x ∧ ν ≤ ycR D b x
    change ycG D c < x at hg
    rcases lt_or_ge c D.B with hcB | hcB
    · rw [ycG_low D hcB] at hg
      rw [ycR_low D hcB] at hν
      obtain ⟨b, hbc, hgb, hνb⟩ := D.cof x hx hx1 c hcB hg ν hν
      have hbB := hbc.trans hcB
      rcases lt_or_ge b gfE with hbE | hbE
      · refine ⟨gfE, le_rfl, hEc, by rw [ycG_low D (yc_E_lt_B D), D.g_E]; exact hx.pos, ?_⟩
        rw [ycR_low D (yc_E_lt_B D)]
        exact hνb.trans (D.mono x hx hx1 gfE (yc_E_lt_B D) b hbE (by rw [D.g_E]; exact hx.pos) hgb).le
      · exact ⟨b, hbE, hbc, by rw [ycG_low D hbB]; exact hgb, by rw [ycR_low D hbB]; exact hνb⟩
    · rw [ycG_high D hcB] at hg
      obtain ⟨n, rfl⟩ := yc_high_eq D hcB hc
      rw [ycR_high] at hν
      rcases Nat.eq_zero_or_eq_succ_pred n with hn | hn
      · subst hn
        rw [Nat.cast_zero, add_zero] at hν
        obtain ⟨d, hdB, hgd, hνd⟩ := D.b_cof x hx hx1 hg ν hν
        rcases lt_or_ge d gfE with hdE | hdE
        · refine ⟨gfE, le_rfl, by push_cast; rw [add_zero]; exact yc_E_lt_B D,
            by rw [ycG_low D (yc_E_lt_B D), D.g_E]; exact hx.pos, ?_⟩
          rw [ycR_low D (yc_E_lt_B D)]
          exact (hνd.trans (D.mono x hx hx1 gfE (yc_E_lt_B D) d hdE (by rw [D.g_E]; exact hx.pos) hgd)).le
        · exact ⟨d, hdE, by push_cast; rw [add_zero]; exact hdB, by rw [ycG_low D hdB]; exact hgd,
            by rw [ycR_low D hdB]; exact hνd.le⟩
      · set m := n.pred
        rw [hn] at hν ⊢
        refine ⟨D.B + m, (yc_E_lt_B D).le.trans le_self_add, ?_, by rw [ycG_high D le_self_add]; exact hg, ?_⟩
        · exact (add_lt_add_iff_left D.B).2 (by exact_mod_cast Nat.lt_succ_self m)
        · rw [ycR_high]
          have e : D.b x + ((m.succ : ℕ) : Ordinal.{0}) = D.b x + m + 1 := by
            rw [add_assoc]; push_cast; rfl
          rw [e] at hν
          exact Order.lt_add_one_iff.1 hν
  ex := fun σ ρ c hB hc hg => by
    show ycR D c ρ ∈ TB ρ σ ∧ pi σ ρ (ycR D c ρ) = ycR D c σ
    change ycG D c < σ at hg
    rcases lt_or_ge c D.B with hcB | hcB
    · rw [ycG_low D hcB] at hg
      rw [ycR_low D hcB, ycR_low D hcB]
      exact D.ex σ ρ hB c hcB hg
    · rw [ycG_high D hcB] at hg
      obtain ⟨n, rfl⟩ := yc_high_eq D hcB hc
      rw [ycR_high, ycR_high]
      obtain ⟨h1, h2⟩ := D.b_pi σ ρ hB hg
      have hnσ : (n : Ordinal.{0}) < σ := (natCast_lt_omega0 n).trans (omega0_lt_inE hB.1)
      obtain ⟨h3, h4⟩ := pi_add hB h1 (mem_TB_of_lt hB hnσ)
      exact ⟨h3, by rw [h4, h2, pi_lt hB hnσ]⟩
  ld := fun c hl hEc hc => ycLD D hk c hl hEc hc

/-- **The reading system over `Γ(k)` of the codes below `B + ω`** (`Xx.XxRS k`). -/
noncomputable def ycVRS (hk : k + 1 < ε₀) : XxRS k where
  toXkRS := ycRSk D hk
  W_lt := hk

theorem ycVRS_gt_B (hk : k + 1 < ε₀) : (ycVRS D hk).K.gt D.B = D.γ := ycG_high D le_rfl

end Step

/-! ## The frontier lemma over `Γ(k)` -/

section Front

variable {k : Ordinal.{0}} (D : YcVD k) (hk : k + 1 < ε₀) (S : InaccSeq.{0}) (hγ : D.γ < Td.tdK S)
include hk hγ

theorem ycVRS_g : (ycVRS D hk).K.gt D.B < Td.tdK S := by rw [ycVRS_gt_B]; exact hγ

/-- **THE BOUND OF EVERY SYSTEM OVER `Γ(k)` WITH BASE GATE BELOW `K` IS LOCATED**: `Λ⁺ = ι(Γ(B)·ω)`,
`P(Γ(B)·ω) < L(0)`. -/
theorem ycVD_loc :
    xtB1 (xxX (ycVRS D hk) D.B (yc_E_lt_B D).le (yc_B_lt_Bw D) S (ycVRS_g D hk S hγ)) = iota S (gcG D.B * ω) ∧
    upsilon (xtB1 (xxX (ycVRS D hk) D.B (yc_E_lt_B D).le (yc_B_lt_Bw D) S (ycVRS_g D hk S hγ))) =
      Pv S (gcG D.B * ω) ∧ Pv S (gcG D.B * ω) < Nc.ncL S 0 :=
  xxLoc (ycVRS D hk) D.B (yc_E_lt_B D).le (yc_B_lt_Bw D) S (ycVRS_g D hk S hγ)

theorem ycVD_enum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG D.B * ω)) :
    CdUpper S l ∧ CdLower S l :=
  xxEnum (ycVRS D hk) D.B (yc_E_lt_B D).le (yc_B_lt_Bw D) S (ycVRS_g D hk S hγ) hr hl

theorem ycVD_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG D.B * ω)) : CdCapV S l :=
  xxCapV (ycVRS D hk) D.B (yc_E_lt_B D).le (yc_B_lt_Bw D) S (ycVRS_g D hk S hγ) hr hl

end Front

/-- **THE FRONTIER LEMMA OVER `Γ(k)` FOR EVERY `k` WITH `k + 1 < ε₀`** (skeleton leaf `skLayFront`): for every system
over the base atom `Γ(k)` with gate below `K`, UPPER, LOWER and CapV hold at every range restart below
`ι(Γ(B)·ω)`. -/
theorem ycLayFront (S : InaccSeq.{0}) {k : Ordinal.{0}} (hk : k + 1 < ε₀) : YcLayFront S k :=
  fun D hγ _ hr hl => ⟨(ycVD_enum D hk S hγ hr hl).1, (ycVD_enum D hk S hγ hr hl).2, ycVD_capV D hk S hγ hr hl⟩

/-- **`k = 0`** (reproves `Xk.xkLayFront_zero`). -/
theorem ycLayFront_zero' (S : InaccSeq.{0}) : YcLayFront S 0 :=
  ycLayFront S (by rw [zero_add]; exact one_lt_omega0.trans (omega0_lt_epsilon 0))

end Googology.Trans.PoR.InaccPsi.R2.Yc
