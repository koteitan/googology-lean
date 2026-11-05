import Googology.Trans.PoR.InaccPsi.R2.ZmDS

/-!
# ZmRS: A DIGIT SYSTEM GIVES A READING SYSTEM `Zb.ZbRS` AND `ZbDirect S E`

For a digit system `M` at a base `E > B_Γ` the atom indices `B_Γ + 1 + o`, `o < E`, read
`D(x) + M.R(o)(x)` with the gate `M.G(o)`.  The indices are no fixed points of `Γ` (`M.nfx`); the inversion of the
atom (`zmInv`) and the gated cover (`zmCover`) are the arguments of `Zg.zgInv3`, `Zg.zgCover3` for a general digit
system.

* `ZmDS.E_E`, `ZmDS.R_gq`, `ZmDS.nonfix`, `ZmDS.zmInv`, `ZmDS.zmCover`;
* `ZmDS.toRS` (**the reading system of the indices `B_Γ + 1 + o`, `o < E`**), `ZmDS.direct`
  (**`ZbDirect S E`** for a base gate below `K`), `ZmDS.UV` (**UPPER ∧ LOWER ∧ CapV below `ι(Γ(B)·ω)` for every `B < E`**).

No new axiom.  New definitions: `ZmDS.rR`, `ZmDS.rG`, `ZmDS.toRS`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zm

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Ge
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Zg Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Xk

namespace ZmDS

variable (M : ZmDS)

theorem E_E : InE M.E := by rw [← M.E_eq]; exact zm_veb_E _

theorem E_lim : IsSuccLimit M.E := ev_isSuccLimit_of_inE M.E_E

theorem one_lt_E : (1 : Ordinal.{0}) < M.E := lu_one_lt_E M.E_E

theorem V_lt (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) (hEg : M.Eg < x) : M.V x < Om1 :=
  (M.V_T x hx hx1 hEg).2.2.2.trans (zm_gq_facts hx hx1).2.2.1

theorem Eg_lt {c x : Ordinal.{0}} (hc0 : c ≠ 0) (hg : M.G c < x) : M.Eg < x := (M.Eg_le c hc0).trans_lt hg

/-- A reading below the base is below `gq(D(x)+1)`. -/
theorem R_gq {c x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hc : c < M.E) (hg : M.G c < x) :
    M.R c x < gq (ywV 1 0 x + 1) x := by
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [M.R0]; exact (hx.pos.trans (zmD_facts hx hx1).2.1).trans (zm_gq_facts hx hx1).1
  · exact (M.lt c x hx hx1 hc hg).trans (M.V_T x hx hx1 (M.Eg_lt hc0 hg)).2.2.2

/-- `B_Γ + 1 + o < E` for `o < E` (`E > B_Γ`). -/
theorem idx_lt (h : tfBG < M.E) {o : Ordinal.{0}} (ho : o < M.E) : tfBG + 1 + o < M.E :=
  (inE_indec M.E_E).add_lt ((inE_indec M.E_E).add_lt h M.one_lt_E) ho

theorem om_idx (o : Ordinal.{0}) : Om1 + 1 + (tfBG + 1 + o) = tfBG + 1 + o := by
  have hE : ω ^ tfBG = tfBG := Low.opow_eq_self_of_SC tfBG_SC
  have h1 : Om1 + 1 + tfBG = tfBG :=
    Ordinal.add_of_omega0_opow_le (c := tfBG) (by rw [hE]; exact tl_Om1_succ_lt_BG) (by rw [hE])
  rw [← add_assoc, ← add_assoc, h1]

/-- **No fixed point of `Γ` among the indices `B_Γ + 1 + o`, `o < E`.** -/
theorem nonfix (h : tfBG < M.E) {o : Ordinal.{0}} (ho : o < M.E) :
    Om1 + 1 + (tfBG + 1 + o) < gamma (Om1 + 1 + (tfBG + 1 + o)) := by
  rw [om_idx]
  set ν := tfBG + 1 + o with hν
  rcases (isNormal_gamma.strictMono.le_apply (x := ν)).lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  have h1G : (1 : Ordinal.{0}) < gamma ν := one_lt_omega0.trans (omega0_lt_inE
    (Low.opow_eq_self_of_SC (Lq.lq_gamma_SC ν)))
  have hfix : veblen 1 (gamma ν) = gamma ν := by
    conv_lhs => rw [← veblen_gamma_zero ν]
    rw [veblen_veblen_of_lt h1G, veblen_gamma_zero]
  rw [← heq] at hfix
  have hB : tfBG < ν := by
    rw [hν]; exact lt_of_lt_of_le (lt_add_one tfBG) le_self_add
  exact M.nfx ν hB (M.idx_lt h ho).le hfix

theorem zmInv (h : tfBG < M.E) {Z o : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om1) (ho : o < M.E)
    (hc : TlCl Z (gcG (tfBG + 1 + o))) : TlCl Z o := by
  rw [tf_gcG] at hc
  have hlt := M.nonfix h ho
  have hO : Om1 < gamma (Om1 + 1 + (tfBG + 1 + o)) := by
    rw [← tf_gcG, Br.Om1_eq]; exact gcG_Om1_lt _
  obtain ⟨-, hI⟩ := tl_cl_atom hZ1 _ hc (Lq.lq_gamma_SC _) hO
  rw [tlLev_gamma hlt] at hI
  have hI' : tlI 0 (gamma (Om1 + 1 + (tfBG + 1 + o))) = Om1 + 1 + (tfBG + 1 + o) := by
    rw [← rhF_zero]; exact tlI_rhF 0 _
  rw [hI'] at hI
  have hω : ω ≤ tfBG + 1 + o := (omega0_le_of_isSuccLimit zgBG_lim).trans (le_self_add.trans le_self_add)
  rw [add_assoc, one_add_of_omega0_le hω] at hI
  have hb := (tl_cl_Om1_add hZ).1 hI
  have hx : TlCl Z (tfBG + 1) := TlCl.add (zbBG_tl hZ.1) (TlCl.one hZ.1)
  have := (tlDec hZ _ hb).1 _ hx le_self_add
  rwa [Ordinal.add_sub_cancel] at this

/-- The reading of the index `c = B_Γ + 1 + o`. -/
noncomputable def rR (c x : Ordinal.{0}) : Ordinal.{0} := ywV 1 0 x + M.R (zbO c) x

/-- The gate of the index `c = B_Γ + 1 + o`. -/
noncomputable def rG (c : Ordinal.{0}) : Ordinal.{0} := M.G (zbO c)

theorem rR_eq (o x : Ordinal.{0}) : M.rR (tfBG + 1 + o) x = ywV 1 0 x + M.R o x := by
  unfold rR; rw [zbO_add]

theorem rG_eq (o : Ordinal.{0}) : M.rG (tfBG + 1 + o) = M.G o := by
  unfold rG; rw [zbO_add]

/-- **The gated cover** below `Γ_{Ω₁+1+c}` for a limit index `c ∈ (B_Γ+1, E)`. -/
theorem zmCover (h : tfBG < M.E) {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1) {c : Ordinal.{0}}
    (hl : IsSuccLimit c) (hc0 : tfBG + 1 < c) (hc : c < M.E) (hgc : M.rG c < Z) :
    ∀ d, GxCl Z (zbU.At Z) d → d < gcG c →
      ∃ b, tfBG + 1 ≤ b ∧ b < c ∧ M.rG b < Z ∧ d < gcG b := by
  have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1.le
  have hZl : IsSuccLimit Z := ev_isSuccLimit_of_inE (gg_SC_eps hZ)
  have hEgZ : M.Eg < Z := by
    obtain ⟨o, rfl⟩ := exists_add_of_le hc0.le
    have ho0 : o ≠ 0 := by rintro rfl; rw [add_zero] at hc0; exact lt_irrefl _ hc0
    rw [rG_eq] at hgc; exact M.Eg_lt ho0 hgc
  have hg0 : M.rG (tfBG + 1) < Z := by
    have e : M.rG (tfBG + 1) = M.rG (tfBG + 1 + 0) := by rw [add_zero]
    rw [e, rG_eq, M.G0]; exact hZ.1
  intro d hd
  induction hd with
  | small h' => exact fun _ => ⟨tfBG + 1, le_rfl, hc0, hg0, (h'.trans hZ1).trans (gcG_Om1_lt _)⟩
  | om => exact fun _ => ⟨tfBG + 1, le_rfl, hc0, hg0, gcG_Om1_lt _⟩
  | @atom s hs =>
    intro h'
    obtain ⟨b, rfl⟩ := zbU_atom_gcG hs
    have hbc : b < c := gcG_lt_iff.1 h'
    rcases lt_or_ge b (tfBG + 1) with hb | hb
    · exact ⟨tfBG + 1, le_rfl, hc0, hg0, gcG_lt hb⟩
    obtain ⟨o, rfl⟩ := exists_add_of_le hb
    have ho : o < M.E := le_add_self.trans_lt (hbc.trans hc)
    rcases hs with hs | ⟨c', hc', -, e⟩
    · have hT := M.zmInv h hZ hZ1' ho hs.2.2.2
      have hgo := M.gate o Z hZ hZ1' hEgZ ho hT
      refine ⟨tfBG + 1 + (o + 1), le_self_add, ?_, ?_, ?_⟩
      · rw [← add_assoc]; exact hl.add_one_lt hbc
      · rw [rG_eq]; exact M.g_succ o Z hZl hEgZ hgo
      · rw [← add_assoc]; exact gcG_lt (lt_add_one _)
    · exfalso
      have h1 : c' < tfBG + 1 + o := hc'.trans ((lt_add_one _).trans_le le_self_add)
      exact absurd e (gcG_lt h1).ne'
  | @add a b _ _ iha ihb =>
    intro h'
    obtain ⟨b1, h1, h1', g1, e1⟩ := iha (lt_of_le_of_lt le_self_add h')
    obtain ⟨b2, h2, h2', g2, e2⟩ := ihb (lt_of_le_of_lt le_add_self h')
    rcases le_total b1 b2 with hle | hle
    · exact ⟨b2, h2, h2', g2, (gcG_SC _).isPrincipal (e1.trans_le (gcG_le hle)) e2⟩
    · exact ⟨b1, h1, h1', g1, (gcG_SC _).isPrincipal e1 (e2.trans_le (gcG_le hle))⟩
  | @phi a b _ _ iha ihb =>
    intro h'
    obtain ⟨b1, h1, h1', g1, e1⟩ := iha (lt_of_le_of_lt (left_le_veblen a b) h')
    obtain ⟨b2, h2, h2', g2, e2⟩ := ihb (lt_of_le_of_lt (right_le_veblen a b) h')
    rcases le_total b1 b2 with hle | hle
    · exact ⟨b2, h2, h2', g2, (gcG_SC _).2 _ (e1.trans_le (gcG_le hle)) _ e2⟩
    · exact ⟨b1, h1, h1', g1, (gcG_SC _).2 _ e1 _ (e2.trans_le (gcG_le hle))⟩

section Rd

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem rR_facts {o : Ordinal.{0}} (ho : o < M.E) (hg : M.G o < x) :
    ywV 1 0 x + M.R o x ∈ Tset x ∧ ywV 1 0 x + M.R o x < Om1 ∧
      ywV 1 0 x + M.R o x < gq (ywV 1 0 x + 1) x ∧ gq (ywV 1 0 x + M.R o x) x < ywX x := by
  obtain ⟨hDq, hqT, hq1, hqfix, hqX⟩ := zm_gq_facts hx hx1
  have hqE := zm_fix_E hqfix
  have hS : ywV 1 0 x + M.R o x < gq (ywV 1 0 x + 1) x := (inE_indec hqE).add_lt hDq (M.R_gq hx hx1 ho hg)
  have hST := vz_T_down hx hx1 hqT hq1 hS.le
  have hSX : ywV 1 0 x + M.R o x < ywX x := hS.trans hqX
  refine ⟨hST, hS.trans hq1, hS, ?_⟩
  rw [← ywV_zero]
  exact ywV_lt_X hx hx1 (mem_T_of_le hx hx1 zero_le) (hx.pos.trans hx1) hST (hS.trans hq1)
    (hx.pos.trans (ywX_facts hx hx1).2.1) hSX

end Rd

/-- **THE READING SYSTEM OF THE INDICES `B_Γ + 1 + o`, `o < E`.** -/
noncomputable def toRS (S : InaccSeq.{0}) (h : tfBG < M.E) : ZbRS where
  c0 := tfBG + 1
  Bd := M.E
  gt := M.rG
  R := M.rR
  L0 := (zbBGn 0).1
  c0_ne := (lt_of_le_of_lt zero_le (lt_add_one tfBG)).ne'
  c0_lt := (inE_indec M.E_E).add_lt h M.one_lt_E
  Bd_X := M.E_X.le
  gt_c0 := by
    have e : M.rG (tfBG + 1) = M.rG (tfBG + 1 + 0) := by rw [add_zero]
    rw [e, rG_eq, M.G0]
  L0_g := zbBGn_g 0
  L0_E := fun x _ _ => by
    rw [zbBGn_E 0 x]
    have e : M.rR (tfBG + 1) x = M.rR (tfBG + 1 + 0) x := by rw [add_zero]
    rw [e, rR_eq, M.R0, Nat.cast_zero]
  L0_top := fun y hy hy1 => by
    have h' := (zbBGn_codes S 0).1 y hy hy1 (by rw [zbBGn_g]; exact hy.1)
    rw [h']; unfold zbT; norm_num
  L0_poly := by
    have h' := (zbBGn_codes S 0).2
    unfold zbT at h'; norm_num at h'
    exact h'
  RT := fun c x hx hx1 h1 h2 hg => by
    obtain ⟨o, rfl⟩ := exists_add_of_le h1
    rw [rG_eq] at hg
    rw [rR_eq]
    obtain ⟨hT, h1', -, hX⟩ := M.rR_facts hx hx1 (le_add_self.trans_lt h2) hg
    exact ⟨hT, h1', hX⟩
  mono := fun b c x hx hx1 h1 hbc hc hgb hgc => by
    obtain ⟨o₂, rfl⟩ := exists_add_of_le (h1.trans hbc.le)
    obtain ⟨o₁, rfl⟩ := exists_add_of_le h1
    rw [rG_eq] at hgb hgc
    rw [rR_eq, rR_eq]
    exact (add_lt_add_iff_left _).2 (M.mono o₁ o₂ x hx hx1 ((add_lt_add_iff_left _).1 hbc)
      (le_add_self.trans_lt hc) hgb hgc)
  succ := fun b x hb => by
    obtain ⟨o, rfl⟩ := exists_add_of_le hb
    rw [add_assoc (tfBG + 1) o 1, rR_eq, rR_eq, M.succ, add_assoc]
  gt_le_succ := fun b => by
    rcases lt_or_ge b (tfBG + 1) with hb | hb
    · unfold rG
      rw [show zbO b = 0 from Ordinal.sub_eq_zero_iff_le.2 hb.le, M.G0]; exact zero_le
    · obtain ⟨o, rfl⟩ := exists_add_of_le hb
      rw [add_assoc (tfBG + 1) o 1, rG_eq, rG_eq]
      exact M.g_le o
  lim_R := fun c x hl hc0 hc hx hx1 hg => by
    obtain ⟨o, rfl⟩ := exists_add_of_le hc0.le
    rw [rG_eq] at hg
    have ho : o < M.E := le_add_self.trans_lt hc
    have hol : IsSuccLimit o := by
      rcases zero_or_succ_or_isSuccLimit o with h0 | ⟨s, hs⟩ | h'
      · subst h0; rw [add_zero] at hc0; exact absurd hc0 (lt_irrefl _)
      · exfalso
        have h' : IsSuccLimit (Order.succ (tfBG + 1 + s)) := by
          rw [succ_eq_add_one, add_assoc, ← succ_eq_add_one s, hs]; exact hl
        exact Order.not_isSuccLimit_succ _ h'
      · exact h'
    rw [rR_eq]
    have hRl := M.lim o x hx hx1 hol ho hg
    have h1r : (1 : Ordinal.{0}) < M.R o x := by simpa using hRl.add_one_lt hRl.bot_lt
    exact ⟨isSuccLimit_add _ hRl, ywV 1 0 x + 1, (add_lt_add_iff_left _).2 h1r,
      (M.rR_facts hx hx1 ho hg).2.2.1⟩
  cof := fun c x _ hc0 hc hx hx1 hg ν hν => by
    obtain ⟨o, rfl⟩ := exists_add_of_le hc0.le
    rw [rG_eq] at hg
    rw [rR_eq] at hν
    have ho : o < M.E := le_add_self.trans_lt hc
    have hol : IsSuccLimit o := by
      rcases zero_or_succ_or_isSuccLimit o with h0 | ⟨s, hs⟩ | h'
      · subst h0; rw [add_zero] at hc0; exact absurd hc0 (lt_irrefl _)
      · exfalso
        have h' : IsSuccLimit (Order.succ (tfBG + 1 + s)) := by
          rw [succ_eq_add_one, add_assoc, ← succ_eq_add_one s, hs]; exact ‹IsSuccLimit _›
        exact Order.not_isSuccLimit_succ _ h'
      · exact h'
    rcases le_or_gt ν (ywV 1 0 x) with hνD | hDν
    · refine ⟨tfBG + 1 + 0, le_self_add, (add_lt_add_iff_left _).2 hol.bot_lt, ?_, ?_⟩
      · rw [rG_eq, M.G0]; exact hx.pos
      · rw [rR_eq, M.R0, add_zero]; exact hνD
    · obtain ⟨e, rfl⟩ := exists_add_of_le hDν.le
      have he : e < M.R o x := (add_lt_add_iff_left _).1 hν
      obtain ⟨b, hb, hgb, heb⟩ := M.cof o x hx hx1 hol ho hg e he
      exact ⟨tfBG + 1 + b, le_self_add, (add_lt_add_iff_left _).2 hb, by rw [rG_eq]; exact hgb,
        by rw [rR_eq]; exact (add_le_add_iff_left _).2 heb⟩
  ex := fun σ ρ c hB h1 h2 hg => by
    obtain ⟨o, rfl⟩ := exists_add_of_le h1
    change M.rG _ < σ at hg
    rw [rG_eq] at hg
    show M.rR _ ρ ∈ TB ρ σ ∧ Googology.Trans.PoR.InaccPsi.R2.pi σ ρ (M.rR _ ρ) = M.rR _ σ
    rw [rR_eq, rR_eq]
    obtain ⟨d1, d2⟩ := zmD_pi hB
    obtain ⟨r1, r2⟩ := M.ex σ ρ o hB (le_add_self.trans_lt h2) hg
    obtain ⟨s1, s2⟩ := pi_add hB d1 r1
    exact ⟨s1, by rw [s2, d2, r2]⟩
  cover := fun c Z hl hc0 hc hZ hZ1 hgc d hd hdT => M.zmCover h hZ hZ1 hl hc0 hc hgc d hd hdT
  cl := fun c Z h1 h2 hZ hg => by
    obtain ⟨o, rfl⟩ := exists_add_of_le h1
    change M.rG _ < Z at hg
    rw [rG_eq] at hg
    have ho : o < M.E := le_add_self.trans_lt h2
    refine GxCl.atom (Or.inl ⟨gcG_SC _, gcG_Om1_lt _, ZbRS.gcG_lt_X (h2.trans_le M.E_X.le), ?_⟩)
    have harg : TlCl Z (Om1 + 1 + (tfBG + 1 + o)) :=
      TlCl.add (TlCl.add TlCl.om (TlCl.one hZ.1))
        (TlCl.add (TlCl.add (zbBG_tl hZ.1) (TlCl.one hZ.1)) (M.cl o Z hZ ho hg))
    rw [tf_gcG]
    exact TlCl.gam hZ.1 harg ((lt_add_one _).trans_le le_self_add)

/-- **`ZbDirect S E`**: a layer for every index `B_Γ ≤ B < E` (`B = B_Γ + 1 + o`: the layer of `B_Γ + 1 + o'`,
`o ≤ o' < E` with gate `≤ max Eg 1`, `M.Gc0`). -/
theorem direct (S : InaccSeq.{0}) (h : tfBG < M.E) (hK : M.Eg < Td.tdK S) (hc : M.Gc0) : ZbDirect S M.E := by
  intro B hB1 hB2
  rcases hB1.lt_or_eq with hlt | heq
  · obtain ⟨o, rfl⟩ := exists_add_of_le (Order.add_one_le_of_lt hlt)
    have ho : o < M.E := le_add_self.trans_lt hB2
    obtain ⟨o', hoo', ho', hg'⟩ := hc o ho
    have hg : (M.toRS S h).gt (tfBG + 1 + o') < Td.tdK S := by
      show M.rG _ < Td.tdK S
      rw [rG_eq]; exact hg'.trans_lt (max_lt hK (gg_one_lt_of_SC Td.tdK_SC))
    exact zbLayAt_mono ((add_le_add_iff_left _).2 hoo')
      ((M.toRS S h).layAt S le_self_add (M.idx_lt h ho') hg)
  · rw [← heq]; exact zbLayAt_BG S

/-- **UPPER ∧ LOWER ∧ CapV at every range restart below `ι(Γ_{Ω₁+1+B}·ω)`, every `B < E`.** -/
theorem UV (S : InaccSeq.{0}) (h : tfBG < M.E) (hK : M.Eg < Td.tdK S) (hc : M.Gc0) {B l : Ordinal.{0}}
    (hB : B < M.E) (hr : CdRange S l) (hl : l < iota S (gcG B * ω)) : CdUpper S l ∧ CdLower S l ∧ CdCapV S l :=
  zbUV_of_direct (M.direct S h hK hc) l hr B hB hl

end ZmDS

end Googology.Trans.PoR.InaccPsi.R2.Zm
