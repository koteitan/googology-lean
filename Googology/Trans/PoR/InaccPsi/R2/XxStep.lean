import Googology.Trans.PoR.InaccPsi.R2.XxLoc
import Googology.Trans.PoR.InaccPsi.R2.XkLay

/-!
# XxStep: THE CODES `B + n` ON TOP OF A SYSTEM OVER `Γ(k)`, AND THE FRONTIER LEMMA OVER `Γ(k)` FOR EVERY `k + 1 < ε₀`

`Hg.hgV_locD_enum` (the frontier of the bound `B` of an `Hg.HgVD`) puts the code `B` into a reading system by the
hereditary step `Hg.HgVD.step` (codes `B^j·d + r < ε_{B+1}`, the modules `Hg.HgVHC` … `Hg.HgVStep`).  The location of
`B` needs much less: the codes `B + n` (`n < ω`), read `b(x) + n` with the base gate `γ`.  For a system over the base
atom `Γ(k)` (`Xk.XkVD k`, `k + 1 < ε₀`) this gives the reading system `xxVRS D : Xx.XxRS k` with bound `B + ω`:

* `xx_cl_restrict`, `xx_cl_B` (the code-gate lemmas `Gr.gr_cl_restrict`, `Gr.gr_cl_B` with the atoms `Γ(k')`,
  `k' ≤ k`, of the layer `k`);
* `xxG`, `xxR` (gate and reading: those of `D` below `B`, `γ` and `b(x) + (c − B)` from `B` on), `xxK` (the code
  system, bound `B + ω`), `xxRSk`, `xxVRS` (**THE READING SYSTEM OF THE CODES BELOW `B + ω`**);
* `xxVD_loc`, `xxVD_enum`, `xxVD_capV` (**the bound of every `XkVD k` with gate below `K` is located**:
  `Λ⁺ = ι(Γ(B)·ω)`, `P(Γ(B)·ω) < L(0)`, UPPER, LOWER and CapV at every range restart below it);
* `xxLayFront` (**`Xk.XkLayFront S k` FOR EVERY `k` WITH `k + 1 < ε₀`**: the skeleton leaf `skLayFront`),
  `xxLayFront_zero` (`k = 0`: reproves `Xk.xkLayFront_zero`), `xx_hgV_loc_zero` (the statements of
  `Hg.hgV_locD_enum` and `Hg.hgV_locD_capV` for every `Hg.HgVD` again, through `Xk.XkVD.ofHg`).

No new axiom.  New definitions: `xxG`, `xxR`, `xxK`, `xxRSk`, `xxVRS`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xx

open Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq Googology.Trans.PoR.InaccPsi.R2.Gr
  Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Xk
open Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gj Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## Code-gate lemmas with the atoms of the layer `k` -/

section Cl

variable {Z : Ordinal.{0}}

/-- **Codes below `N` use no atom `≥ N`** (atoms `Γ(k')`, `k' ≤ k`, and atoms `≥ N`). -/
theorem xx_cl_restrict {k : Ordinal.{0}} {At : Set Ordinal.{0}} {N y : Ordinal.{0}}
    (hAt : ∀ s ∈ At, s ∈ XkAt k ∨ N ≤ s) (h : GxCl Z At y) (hy : y < N) : GxCl Z (XkAt k) y := by
  induction h with
  | small h => exact GxCl.small h
  | om => exact GxCl.om
  | @atom s hs =>
    rcases hAt s hs with e | e
    · exact GxCl.atom e
    · exact absurd (hy.trans_le e) (lt_irrefl _)
  | @add x y _ _ ihx ihy =>
    exact GxCl.add (ihx (lt_of_le_of_lt le_self_add hy)) (ihy (lt_of_le_of_lt le_add_self hy))
  | @phi x y _ _ ihx ihy =>
    exact GxCl.phi (ihx (lt_of_le_of_lt (left_le_veblen x y) hy)) (ihy (lt_of_le_of_lt (right_le_veblen x y) hy))

/-- **A code in `[B, ε_{B+1})` over the atoms of the layer `k` has `B` as a code** (`B ≥ Γ(k)` an `ε`-number). -/
theorem xx_cl_B {k : Ordinal.{0}} (hZ1 : Z ≤ Om 1) {B : Ordinal.{0}} (hB : InE B) (hGB : gcG k ≤ B)
    {y : Ordinal.{0}} (h : GxCl Z (XkAt k) y) (hBy : B ≤ y) (hyN : y < eN B) : GxCl Z (XkAt k) B := by
  have hGO := gcG_Om1_lt k
  have hBp : IsPrincipal (· + ·) B := by
    have := isPrincipal_add_omega0_opow B
    rwa [hB] at this
  induction h with
  | small h => exact absurd ((hGO.trans_le hGB).trans_le hBy) (not_lt.2 (h.le.trans hZ1))
  | om => exact absurd (hGO.trans_le hGB) (not_lt.2 hBy)
  | @atom s hs =>
    obtain ⟨k', hk', rfl⟩ := hs
    have h1 : gcG k' ≤ B := (gcG_le hk').trans hGB
    rw [le_antisymm hBy h1]
    exact GxCl.atom ⟨k', hk', rfl⟩
  | @add x y _ _ ihx ihy =>
    rcases lt_or_ge y B with hyB | hyB
    · rcases lt_or_ge x B with hxB | hxB
      · exact absurd (hBp hxB hyB) (not_lt.2 hBy)
      · exact ihx hxB (lt_of_le_of_lt le_self_add hyN)
    · exact ihy hyB (lt_of_le_of_lt le_add_self hyN)
  | @phi a b _ hb _ ihb =>
    rcases eq_or_ne a 0 with rfl | ha
    · rw [veblen_zero_apply] at hBy hyN
      rcases lt_or_ge b B with hbB | hbB
      · exfalso
        have : ω ^ b < ω ^ B := (opow_lt_opow_iff_right one_lt_omega0).2 hbB
        rw [hB] at this
        exact absurd hBy (not_le.2 this)
      · exact ihb hbB ((right_le_opow b one_lt_omega0).trans_lt hyN)
    · have hE : InE (veblen a b) := gg_veblen_eps ha
      rcases hBy.lt_or_eq with hlt | heq
      · exact absurd hyN (not_lt.2 (eN_le hlt hE))
      · rw [heq]; exact GxCl.phi ‹_› hb

end Cl

theorem xx_nat_mem {S : InaccSeq.{0}} {a b : Ordinal.{0}} : ∀ n : ℕ, (n : Ordinal.{0}) ∈ S.CSet a b
  | 0 => by exact_mod_cast CSet.zero_mem a b
  | n + 1 => by push_cast; exact CSet.succ_mem (xx_nat_mem n)

theorem xx_omega_mem {S : InaccSeq.{0}} {a b : Ordinal.{0}} : (ω : Ordinal.{0}) ∈ S.CSet a b := by
  have e : (ω : Ordinal.{0}) = veblen 0 1 := by rw [veblen_zero_apply, opow_one]
  rw [e]; exact CSet.phi_mem (CSet.zero_mem a b) (CSet.one_mem a b)

/-! ## The codes `B + n` -/

section Step

variable {k : Ordinal.{0}} (D : XkVD k)

theorem xx_B_lim : IsSuccLimit D.B := ev_isSuccLimit_of_inE D.B_E

theorem xx_B_pos : 0 < D.B := D.B_E.pos

theorem xx_Om1_lt_B : Om 1 < D.B := (gcG_Om1_lt k).trans_le D.G_le

theorem xx_E_lt_B : gfE < D.B := gfE_lt_G0.trans_le ((gcG_le zero_le).trans D.G_le)

theorem xx_Bw_lt1 : D.B + ω < gcG (k + 1) := by
  have hE : InE (gcG (k + 1)) := gg_SC_eps (gcG_SC (k + 1))
  exact (inE_indec hE).add_lt D.B_lt1 (omega0_lt_inE hE)

theorem xx_B_lt_Bw : D.B < D.B + ω := lt_add_of_pos_right _ omega0_pos

theorem xx_Bw_lt_eN : D.B + ω < eN D.B := by
  have hE : InE (eN D.B) := eN_E D.B
  exact (inE_indec hE).add_lt (lt_eN _) (omega0_lt_inE hE)

theorem xx_high_eq {c : Ordinal.{0}} (hBc : D.B ≤ c) (hc : c < D.B + ω) : ∃ n : ℕ, c = D.B + n := by
  have e : D.B + (c - D.B) = c := Ordinal.add_sub_cancel_of_le hBc
  have h1 : c - D.B < ω := (add_lt_add_iff_left D.B).1 (by rw [e]; exact hc)
  obtain ⟨n, hn⟩ := lt_omega0.1 h1
  exact ⟨n, by rw [← hn, e]⟩

/-- **The gate**: that of `D` below `B`, the base gate `γ` from `B` on. -/
noncomputable def xxG (c : Ordinal.{0}) : Ordinal.{0} := if c < D.B then D.g c else D.γ

/-- **The reading**: that of `D` below `B`, `b(x) + (c − B)` from `B` on. -/
noncomputable def xxR (c x : Ordinal.{0}) : Ordinal.{0} := if c < D.B then D.R c x else D.b x + (c - D.B)

theorem xxG_low {c : Ordinal.{0}} (hc : c < D.B) : xxG D c = D.g c := if_pos hc

theorem xxG_high {c : Ordinal.{0}} (hc : D.B ≤ c) : xxG D c = D.γ := if_neg (not_lt.2 hc)

theorem xxR_low {c x : Ordinal.{0}} (hc : c < D.B) : xxR D c x = D.R c x := if_pos hc

theorem xxR_high_gen {c x : Ordinal.{0}} (hc : D.B ≤ c) : xxR D c x = D.b x + (c - D.B) := if_neg (not_lt.2 hc)

theorem xxR_high (n : ℕ) (x : Ordinal.{0}) : xxR D (D.B + n) x = D.b x + n := by
  rw [xxR_high_gen D le_self_add, Ordinal.add_sub_cancel]

theorem xx_R_succ (b x : Ordinal.{0}) : xxR D (b + 1) x = xxR D b x + 1 := by
  rcases lt_or_ge b D.B with hb | hb
  · rw [xxR_low D hb, xxR_low D ((xx_B_lim D).add_one_lt hb), D.R_succ]
  · have e : D.B + (b - D.B) = b := Ordinal.add_sub_cancel_of_le hb
    have e1 : (b + 1) - D.B = (b - D.B) + 1 := by
      conv_lhs => rw [← e, add_assoc]
      exact Ordinal.add_sub_cancel _ _
    rw [xxR_high_gen D hb, xxR_high_gen D (hb.trans le_self_add), e1, add_assoc]

theorem xx_G_le_succ (b : Ordinal.{0}) : xxG D b ≤ xxG D (b + 1) := by
  rcases lt_or_ge b D.B with hb | hb
  · rw [xxG_low D hb, xxG_low D ((xx_B_lim D).add_one_lt hb)]; exact D.g_le_succ b
  · rw [xxG_high D hb, xxG_high D (hb.trans le_self_add)]

section Base

variable (hk : k + 1 < ε₀) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hk hx hx1

/-- **The readings lie below `Γ_{x+2+k}`.** -/
theorem xx_R_lt {c : Ordinal.{0}} (hc : c < D.B + ω) (hg : xxG D c < x) : xxR D c x < gq (k + 1) x := by
  rcases lt_or_ge c D.B with hcB | hcB
  · rw [xxR_low D hcB]; rw [xxG_low D hcB] at hg
    exact (D.R_lt_Z x hx hx1 c hcB hg).trans (D.Z_G1 x hx hx1)
  · rw [xxG_high D hcB] at hg
    obtain ⟨n, rfl⟩ := xx_high_eq D hcB hc
    rw [xxR_high]
    have hq := (xx_facts hx hx1 hk).2.2.2
    have hb : D.b x < gq (k + 1) x :=
      ((lt_eN _).trans (D.b_Z x hx hx1 hg)).trans (D.Z_G1 x hx hx1)
    exact (inE_indec hq).add_lt hb ((natCast_lt_omega0 n).trans (omega0_lt_inE hq))

omit hk in
theorem xx_R_mono {b c : Ordinal.{0}} (hc : c < D.B + ω) (hbc : b < c) (hgb : xxG D b < x)
    (hgc : xxG D c < x) : xxR D b x < xxR D c x := by
  rcases lt_or_ge c D.B with hcB | hcB
  · have hbB := hbc.trans hcB
    rw [xxR_low D hcB, xxR_low D hbB]
    rw [xxG_low D hcB] at hgc; rw [xxG_low D hbB] at hgb
    exact D.mono x hx hx1 c hcB b hbc hgc hgb
  · rw [xxG_high D hcB] at hgc
    obtain ⟨n, rfl⟩ := xx_high_eq D hcB hc
    rw [xxR_high]
    rcases lt_or_ge b D.B with hbB | hbB
    · rw [xxR_low D hbB]; rw [xxG_low D hbB] at hgb
      exact (D.R_lt_b x hx hx1 hgc b hbB hgb).trans_le le_self_add
    · obtain ⟨m, rfl⟩ := xx_high_eq D hbB (hbc.trans hc)
      rw [xxR_high]
      have hmn : (m : Ordinal.{0}) < n := (add_lt_add_iff_left D.B).1 hbc
      exact (add_lt_add_iff_left _).2 hmn

end Base

/-- **The code system of the codes below `B + ω`.** -/
noncomputable def xxK (hk : k + 1 < ε₀) : GsCS where
  B := D.B + ω
  gt := xxG D
  B_V := by
    have hk1 : k + 1 ≤ D.B + ω :=
      ((hk.trans_le gc_eps0_le_Om1).trans (xx_Om1_lt_B D)).le.trans le_self_add
    exact (xx_Bw_lt1 D).trans_le (gcG_le hk1)
  gt_zero := by rw [xxG_low D (xx_B_pos D)]; exact D.g_zero
  gt_lt := fun c hc => by
    rcases lt_or_ge c D.B with hcB | hcB
    · rw [xxG_low D hcB]; exact D.g_lt c hcB
    · rw [xxG_high D hcB]; exact D.γ_lt
  gt_succ := fun b Z hZ hb hg => by
    rcases lt_or_ge b D.B with hbB | hbB
    · have hb1 := (xx_B_lim D).add_one_lt hbB
      rw [xxG_low D hbB] at hg
      rw [xxG_low D hb1]; exact D.g_succ Z hZ b hb1 hg
    · rw [xxG_high D hbB] at hg
      rw [xxG_high D (hbB.trans le_self_add)]; exact hg
  mem := fun S a b c hc hca hg => by
    have ha : 0 < a := lt_of_le_of_lt zero_le hca
    rcases lt_or_ge c D.B with hcB | hcB
    · rw [xxG_low D hcB] at hg
      exact (D.mem S a b ha c hcB hg).1
    · rw [xxG_high D hcB] at hg
      obtain ⟨n, rfl⟩ := xx_high_eq D hcB hc
      have hB : D.B ∈ S.CSet a b := by
        rw [D.B_ix]; exact CSet.phi_mem (CSet.one_mem _ _) (D.ix_mem S a b ha hg)
      exact CSet.add_mem hB (xx_nat_mem n)
  κ := D.γ
  κ_lt := D.γ_lt
  B_mem := fun S a b ha hγb => by
    have ha0 : 0 < a := lt_of_le_of_lt zero_le ha
    have hB : D.B ∈ S.CSet a b := by
      rw [D.B_ix]; exact CSet.phi_mem (CSet.one_mem _ _) (D.ix_mem S a b ha0 hγb)
    exact CSet.add_mem hB xx_omega_mem
  code_gate := fun Z hZ1 hZ0 hZa hZp c hc hcB => by
    have hAt : ∀ s ∈ {s | ∃ c', c' < D.B + ω ∧ xxG D c' < Z ∧ s = gcG c'}, s ∈ XkAt k ∨ gcG (k + 1) ≤ s := by
      rintro s ⟨c', -, -, rfl⟩
      rcases le_or_gt c' k with h | h
      · exact Or.inl ⟨c', h, rfl⟩
      · exact Or.inr (gcG_le (Order.add_one_le_of_lt h))
    rcases lt_or_ge c D.B with hcB' | hcB'
    · rw [xxG_low D hcB']
      refine D.code_gate Z hZ1 hZ0 hZa hZp _ (fun s hs => (hAt s hs).imp_right fun h => D.B_lt1.le.trans h) c hc hcB'
    · rw [xxG_high D hcB']
      have hZ1' : Z ≤ Om 1 := by rw [← Br.Om1_eq]; exact hZ1
      have h1 := xx_cl_restrict hAt hc (hcB.trans (xx_Bw_lt1 D))
      exact D.γ_cl Z (gr_SC_of hZ0 hZp) hZ1' (xx_cl_B hZ1' D.B_E D.G_le h1 hcB' (hcB.trans (xx_Bw_lt_eN D)))
  count := fun c y hc hy hy1 => by
    have hq1 : gq (k + 1) y < Om (1 : Ordinal.{0}) := by rw [← Br.Om1_eq]; exact (xx_facts hy hy1 hk).2.2.1
    haveI := Gc.gc_countable hq1
    let f : {b : Iio c // xxG D b.1 < y} → Iio (gq (k + 1) y) := fun b =>
      ⟨xxR D b.1.1 y, xx_R_lt D hk hy hy1 (lt_of_lt_of_le b.1.2 hc) b.2⟩
    refine Function.Injective.countable (f := f) fun b b' hbb => ?_
    have e : xxR D b.1.1 y = xxR D b'.1.1 y := congrArg Subtype.val hbb
    rcases lt_trichotomy b.1.1 b'.1.1 with h | h | h
    · exact absurd e (xx_R_mono D hy hy1 (lt_of_lt_of_le b'.1.2 hc) h b.2 b'.2).ne
    · exact Subtype.ext (Subtype.ext h)
    · exact absurd e (xx_R_mono D hy hy1 (lt_of_lt_of_le b.1.2 hc) h b'.2 b.2).ne'

theorem xxK_B (hk : k + 1 < ε₀) : (xxK D hk).B = D.B + ω := rfl

theorem xxK_gt (hk : k + 1 < ε₀) : (xxK D hk).gt = xxG D := rfl

/-- **The decomposition of a limit code** for the reading system: below `B` from `D.ld` (Lemma IMG from
`Xk.XkVD.pkg`), at `B` the `ε`-number `b(x)` itself (Lemma IMG for `b`). -/
theorem xxLD (hk : k + 1 < ε₀) (c : Ordinal.{0}) (hl : IsSuccLimit c) (hEc : gfE < c) (hc : c < D.B + ω) :
    Nonempty (GsmLD (xxK D hk) (xxR D) c) := by
  rcases lt_or_ge c D.B with hcB | hcB
  · obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := D.ld c hl hcB
    have hcpB : cp < D.B := hcp.trans hcB
    have hlg : ∀ x, InE x → x < Om1 → D.g c < x → lg (xxR D c x) = T x := fun x hx hx1 hg => by
      obtain ⟨e1, e2, -, -⟩ := hdec x hx hx1 hg
      rw [xxR_low D hcB, e1]; exact Ge.lg_add_opow e2
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
    · show xxG D _ ≤ xxG D c
      rw [xxG_low D hcB]
      split_ifs with h
      · rw [xxG_low D hcpB]; exact hgcp
      · rw [xxG_low D (xx_E_lt_B D), D.g_E]; exact zero_le
    · intro x hx hx1 hg
      have hg' : D.g c < x := by rw [← xxG_low D hcB]; exact hg
      obtain ⟨e1, e2, e3, e4⟩ := hdec x hx hx1 hg'
      rw [hlg x hx hx1 hg', xxR_low D hcB]
      refine ⟨e1, e2, e3, ?_⟩
      split_ifs with h
      · rw [xxR_low D hcpB]; exact e4
      · push Not at h
        rw [xxR_low D (xx_E_lt_B D)]
        exact e4.trans (D.mono x hx hx1 gfE (xx_E_lt_B D) cp h (by rw [D.g_E]; exact hx.pos)
          (hgcp.trans_lt hg')).le
    · intro ρ τ δ h hg
      change xxG D c < ρ at hg
      have hg' : D.g c < ρ := by rw [← xxG_low D hcB]; exact hg
      show GhPkg (xxG D c) ρ δ (fun y => lg (xxR D c y))
      rw [xxG_low D hcB]
      have hρE := h.ρE
      obtain ⟨e1, -, -, -⟩ := hdec ρ hρE h.ρ1 hg'
      have hTρ : T ρ ≤ D.Z ρ := by
        have h1 : T ρ ≤ D.R c ρ := by
          rw [e1]; exact (right_le_opow _ one_lt_omega0).trans le_add_self
        exact (h1.trans_lt (D.R_lt_Z ρ hρE h.ρ1 c hcB hg')).le
      have hP := XkVD.pkg D hk h (C := ∅) hg' (by simp) hTρ
        (GjEx.of_bases fun σ ρ' hB hgσ => hex σ ρ' hB hgσ)
      exact GhPkg.congr h hP (fun y hyE hy1 hgy => (hlg y hyE hy1 hgy).symm) hg'
  · obtain ⟨n, rfl⟩ := xx_high_eq D hcB hc
    have hn : n = 0 := by
      by_contra hn
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      have e : D.B + ((m + 1 : ℕ) : Ordinal.{0}) = Order.succ (D.B + m) := by
        rw [Order.succ_eq_add_one, add_assoc]; push_cast; rfl
      rw [e] at hl
      exact Order.not_isSuccLimit_succ _ hl
    subst hn
    have hB0 : D.B + ((0 : ℕ) : Ordinal.{0}) = D.B := by push_cast; rw [add_zero]
    have hlgb : ∀ x, InE x → x < Om1 → D.γ < x → lg (xxR D (D.B + ((0 : ℕ) : Ordinal.{0})) x) = D.b x :=
      fun x hx hx1 hγ => by
        have hbE := D.b_E x hx hx1 hγ
        rw [xxR_high, Nat.cast_zero, add_zero]
        conv_lhs => rw [← hbE, ← zero_add (ω ^ D.b x)]
        exact Ge.lg_add_opow (dvd_zero _)
    refine ⟨{
      cp := gfE
      lp := fun _ => 0
      cp_ge := le_rfl
      cp_lt := by rw [hB0]; exact xx_E_lt_B D
      cp_g := by show xxG D gfE ≤ xxG D _; rw [xxG_low D (xx_E_lt_B D), D.g_E]; exact zero_le
      dec := ?_
      pkg := ?_ }⟩
    · intro x hx hx1 hg
      change xxG D _ < x at hg
      rw [xxG_high D le_self_add] at hg
      have hbE := D.b_E x hx hx1 hg
      rw [hlgb x hx hx1 hg]
      refine ⟨?_, dvd_zero _, hbE.pos.ne', zero_le⟩
      rw [xxR_high, Nat.cast_zero, add_zero, zero_add, hbE]
    · intro ρ τ δ h hg
      change xxG D _ < ρ at hg
      show GhPkg (xxG D _) ρ δ (fun y => lg (xxR D _ y))
      rw [xxG_high D le_self_add] at hg ⊢
      have hρE := h.ρE
      have hT : D.b ρ ≤ D.Z ρ := ((lt_eN _).trans (D.b_Z ρ hρE h.ρ1 hg)).le
      have hP := XkVD.pkg D hk h (C := ∅) hg (by simp) hT
        (GjEx.of_bases fun σ ρ' hB hgσ => D.b_pi σ ρ' hB hgσ)
      exact GhPkg.congr h hP (fun y hyE hy1 hgy => (hlgb y hyE hy1 hgy).symm) hg

/-- **THE READING SYSTEM OF THE CODES BELOW `B + ω`** (as an `Xk.XkRS k`). -/
noncomputable def xxRSk (hk : k + 1 < ε₀) : XkRS k where
  K := xxK D hk
  R := xxR D
  E_lt := (xx_E_lt_B D).trans (xx_B_lt_Bw D)
  B_lim := isSuccLimit_add _ isSuccLimit_omega0
  gt_E := by show xxG D gfE = 0; rw [xxG_low D (xx_E_lt_B D)]; exact D.g_E
  gt_lowE := fun c hc => by
    show xxG D c = gtc c; rw [xxG_low D (hc.trans (xx_E_lt_B D))]; exact D.g_lowE c hc
  R_E := fun x _ _ => by show xxR D gfE x = eN x; rw [xxR_low D (xx_E_lt_B D)]; exact D.R_E x
  lt0 := fun c x hx hx1 hc hg => xx_R_lt D hk hx hx1 hc hg
  mono := fun b c x hx hx1 hc hbc hgb hgc => xx_R_mono D hx hx1 hc hbc hgb hgc
  succ := fun b x _ => xx_R_succ D b x
  gt_le_succ := xx_G_le_succ D
  cof := fun c x hx hx1 hc hEc hg ν hν => by
    show ∃ b, gfE ≤ b ∧ b < c ∧ xxG D b < x ∧ ν ≤ xxR D b x
    change xxG D c < x at hg
    rcases lt_or_ge c D.B with hcB | hcB
    · rw [xxG_low D hcB] at hg
      rw [xxR_low D hcB] at hν
      obtain ⟨b, hbc, hgb, hνb⟩ := D.cof x hx hx1 c hcB hg ν hν
      have hbB := hbc.trans hcB
      rcases lt_or_ge b gfE with hbE | hbE
      · refine ⟨gfE, le_rfl, hEc, by rw [xxG_low D (xx_E_lt_B D), D.g_E]; exact hx.pos, ?_⟩
        rw [xxR_low D (xx_E_lt_B D)]
        exact hνb.trans (D.mono x hx hx1 gfE (xx_E_lt_B D) b hbE (by rw [D.g_E]; exact hx.pos) hgb).le
      · exact ⟨b, hbE, hbc, by rw [xxG_low D hbB]; exact hgb, by rw [xxR_low D hbB]; exact hνb⟩
    · rw [xxG_high D hcB] at hg
      obtain ⟨n, rfl⟩ := xx_high_eq D hcB hc
      rw [xxR_high] at hν
      rcases Nat.eq_zero_or_eq_succ_pred n with hn | hn
      · subst hn
        rw [Nat.cast_zero, add_zero] at hν
        obtain ⟨d, hdB, hgd, hνd⟩ := D.b_cof x hx hx1 hg ν hν
        rcases lt_or_ge d gfE with hdE | hdE
        · refine ⟨gfE, le_rfl, by push_cast; rw [add_zero]; exact xx_E_lt_B D,
            by rw [xxG_low D (xx_E_lt_B D), D.g_E]; exact hx.pos, ?_⟩
          rw [xxR_low D (xx_E_lt_B D)]
          exact (hνd.trans (D.mono x hx hx1 gfE (xx_E_lt_B D) d hdE (by rw [D.g_E]; exact hx.pos) hgd)).le
        · exact ⟨d, hdE, by push_cast; rw [add_zero]; exact hdB, by rw [xxG_low D hdB]; exact hgd,
            by rw [xxR_low D hdB]; exact hνd.le⟩
      · set m := n.pred
        rw [hn] at hν ⊢
        refine ⟨D.B + m, (xx_E_lt_B D).le.trans le_self_add, ?_, by rw [xxG_high D le_self_add]; exact hg, ?_⟩
        · exact (add_lt_add_iff_left D.B).2 (by exact_mod_cast Nat.lt_succ_self m)
        · rw [xxR_high]
          have e : D.b x + ((m.succ : ℕ) : Ordinal.{0}) = D.b x + m + 1 := by
            rw [add_assoc]; push_cast; rfl
          rw [e] at hν
          exact Order.lt_add_one_iff.1 hν
  ex := fun σ ρ c hB hc hg => by
    show xxR D c ρ ∈ TB ρ σ ∧ pi σ ρ (xxR D c ρ) = xxR D c σ
    change xxG D c < σ at hg
    rcases lt_or_ge c D.B with hcB | hcB
    · rw [xxG_low D hcB] at hg
      rw [xxR_low D hcB, xxR_low D hcB]
      exact D.ex σ ρ hB c hcB hg
    · rw [xxG_high D hcB] at hg
      obtain ⟨n, rfl⟩ := xx_high_eq D hcB hc
      rw [xxR_high, xxR_high]
      obtain ⟨h1, h2⟩ := D.b_pi σ ρ hB hg
      have hnσ : (n : Ordinal.{0}) < σ := (natCast_lt_omega0 n).trans (omega0_lt_inE hB.1)
      obtain ⟨h3, h4⟩ := pi_add hB h1 (mem_TB_of_lt hB hnσ)
      exact ⟨h3, by rw [h4, h2, pi_lt hB hnσ]⟩
  ld := fun c hl hEc hc => xxLD D hk c hl hEc hc

/-- **The reading system over `Γ(k)` of the codes below `B + ω`** (`Xx.XxRS k`). -/
noncomputable def xxVRS (hk : k + 1 < ε₀) : XxRS k where
  toXkRS := xxRSk D hk
  W_lt := hk

theorem xxVRS_gt_B (hk : k + 1 < ε₀) : (xxVRS D hk).K.gt D.B = D.γ := xxG_high D le_rfl

end Step

/-! ## The frontier lemma over `Γ(k)` -/

section Front

variable {k : Ordinal.{0}} (D : XkVD k) (hk : k + 1 < ε₀) (S : InaccSeq.{0}) (hγ : D.γ < Td.tdK S)
include hk hγ

theorem xxVRS_g : (xxVRS D hk).K.gt D.B < Td.tdK S := by rw [xxVRS_gt_B]; exact hγ

/-- **THE BOUND OF EVERY SYSTEM OVER `Γ(k)` WITH BASE GATE BELOW `K` IS LOCATED**: `Λ⁺ = ι(Γ(B)·ω)`,
`P(Γ(B)·ω) < L(0)`. -/
theorem xxVD_loc :
    xtB1 (xxX (xxVRS D hk) D.B (xx_E_lt_B D).le (xx_B_lt_Bw D) S (xxVRS_g D hk S hγ)) = iota S (gcG D.B * ω) ∧
    upsilon (xtB1 (xxX (xxVRS D hk) D.B (xx_E_lt_B D).le (xx_B_lt_Bw D) S (xxVRS_g D hk S hγ))) =
      Pv S (gcG D.B * ω) ∧ Pv S (gcG D.B * ω) < Nc.ncL S 0 :=
  xxLoc (xxVRS D hk) D.B (xx_E_lt_B D).le (xx_B_lt_Bw D) S (xxVRS_g D hk S hγ)

theorem xxVD_enum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG D.B * ω)) :
    CdUpper S l ∧ CdLower S l :=
  xxEnum (xxVRS D hk) D.B (xx_E_lt_B D).le (xx_B_lt_Bw D) S (xxVRS_g D hk S hγ) hr hl

theorem xxVD_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG D.B * ω)) : CdCapV S l :=
  xxCapV (xxVRS D hk) D.B (xx_E_lt_B D).le (xx_B_lt_Bw D) S (xxVRS_g D hk S hγ) hr hl

end Front

/-- **THE FRONTIER LEMMA OVER `Γ(k)` FOR EVERY `k` WITH `k + 1 < ε₀`** (skeleton leaf `skLayFront`): for every system
over the base atom `Γ(k)` with gate below `K`, UPPER, LOWER and CapV hold at every range restart below
`ι(Γ(B)·ω)`. -/
theorem xxLayFront (S : InaccSeq.{0}) {k : Ordinal.{0}} (hk : k + 1 < ε₀) : XkLayFront S k :=
  fun D hγ _ hr hl => ⟨(xxVD_enum D hk S hγ hr hl).1, (xxVD_enum D hk S hγ hr hl).2, xxVD_capV D hk S hγ hr hl⟩

/-- **`k = 0`** (reproves `Xk.xkLayFront_zero`). -/
theorem xxLayFront_zero (S : InaccSeq.{0}) : XkLayFront S 0 :=
  xxLayFront S (by rw [zero_add]; exact one_lt_omega0.trans (omega0_lt_epsilon 0))

/-- **`k = 0` again for `Hg.HgVD`** (the statements of `Hg.hgV_locD_enum` and `Hg.hgV_locD_capV`, through
`Xk.XkVD.ofHg`, without the hereditary step `Hg.HgVD.step`). -/
theorem xx_hgV_loc_zero (S : InaccSeq.{0}) (V : Hg.HgVD) (hγ : V.γ < Td.tdK S) {l : Ordinal.{0}} (hr : CdRange S l)
    (hl : l < iota S (gcG V.B * ω)) : CdUpper S l ∧ CdLower S l ∧ CdCapV S l :=
  xxLayFront_zero S (XkVD.ofHg V) hγ l hr hl

end Googology.Trans.PoR.InaccPsi.R2.Xx
