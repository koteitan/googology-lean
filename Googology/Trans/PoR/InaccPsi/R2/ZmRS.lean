import Googology.Trans.PoR.InaccPsi.R2.ZmDS

/-!
# ZmRS: A DIGIT SYSTEM GIVES A READING SYSTEM `Zb.ZbRS` AND `ZbDirect S E`

For a digit system `M` at a base `E > B_Γ` the atom indices `B_Γ + 1 + o`, `o < E`, read
`D(x) + M.R(o)(x)` with the gate `M.G(o)`.  The indices are no fixed points of `Γ` (`M.nfx`); the inversion of the
atom (`zmInv`) and the gated cover (`zmCover`) are the arguments of `Zg.zgInv3`, `Zg.zgCover3` for a general digit
system.

* `ZmDS.E_E`, `ZmDS.R_gq`, `ZmDS.nonfix`, `ZmDS.zmInv`, `ZmDS.zmCover`;
* `ZmBase` (a base layer for the index `B + 1`), `ZmDS.zmBaseBG` (the one of `B_Γ + 1`), `ZmDS.toRS` (**the reading
  system of the indices `B + 1 + o`, `o < E`, over the base `B` read `Dv(x)`**), `ZmDS.direct`
  (**`ZbDirect S E`** for a base gate below `K`), `ZmDS.UV` (**UPPER ∧ LOWER ∧ CapV below `ι(Γ(B)·ω)` for every `B < E`**).

No new axiom.  New definitions: `ZmBase`, `ZmDS.zmBaseBG`, `ZmDS.rR`, `ZmDS.rG`, `ZmDS.toRS`.
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
  (M.V_T x hx hx1 hEg).2.2.2.trans (ywX_facts hx hx1).2.2.1

theorem Eg_lt {c x : Ordinal.{0}} (hc0 : c ≠ 0) (hg : M.G c < x) : M.Eg < x := (M.Eg_le c hc0).trans_lt hg

/-- A reading below the base is below `X^x`. -/
theorem R_X {c x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hc : c < M.E) (hg : M.G c < x) :
    M.R c x < ywX x := by
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [M.R0]; exact hx.pos.trans (ywX_facts hx hx1).2.1
  · exact (M.lt c x hx hx1 hc hg).trans (M.V_T x hx hx1 (M.Eg_lt hc0 hg)).2.2.2

/-- `B + 1 + o < E` for `o < E` (`E > B`). -/
theorem idx_lt (h : M.B < M.E) {o : Ordinal.{0}} (ho : o < M.E) : M.B + 1 + o < M.E :=
  (inE_indec M.E_E).add_lt ((inE_indec M.E_E).add_lt h M.one_lt_E) ho

theorem om_B : Om1 + 1 + M.B = M.B := by
  have hE : ω ^ tfBG = tfBG := Low.opow_eq_self_of_SC tfBG_SC
  have h1 : Om1 + 1 + tfBG = tfBG :=
    Ordinal.add_of_omega0_opow_le (c := tfBG) (by rw [hE]; exact tl_Om1_succ_lt_BG) (by rw [hE])
  obtain ⟨d, hd⟩ := exists_add_of_le M.BG_B
  rw [hd, ← add_assoc, h1]

theorem om_idx (o : Ordinal.{0}) : Om1 + 1 + (M.B + 1 + o) = M.B + 1 + o := by
  rw [← add_assoc, ← add_assoc, M.om_B]

/-- **No fixed point of `Γ` among the indices `B_Γ + 1 + o`, `o < E`.** -/
theorem nonfix (h : M.B < M.E) {o : Ordinal.{0}} (ho : o < M.E) :
    Om1 + 1 + (M.B + 1 + o) < gamma (Om1 + 1 + (M.B + 1 + o)) := by
  rw [M.om_idx]
  set ν := M.B + 1 + o with hν
  rcases (isNormal_gamma.strictMono.le_apply (x := ν)).lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  have hB : M.B < ν := by
    rw [hν]; exact lt_of_lt_of_le (lt_add_one M.B) le_self_add
  exact M.nfx ν hB (M.idx_lt h ho).le heq.symm

theorem zmInv (h : M.B < M.E) {Z o : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om1) (hEgZ : M.Eg < Z) (ho : o < M.E)
    (hc : TlCl Z (gcG (M.B + 1 + o))) : TlCl Z o := by
  rw [tf_gcG] at hc
  have hlt := M.nonfix h ho
  have hO : Om1 < gamma (Om1 + 1 + (M.B + 1 + o)) := by
    rw [← tf_gcG, Br.Om1_eq]; exact gcG_Om1_lt _
  obtain ⟨-, hI⟩ := tl_cl_atom hZ1 _ hc (Lq.lq_gamma_SC _) hO
  rw [tlLev_gamma hlt] at hI
  have hI' : tlI 0 (gamma (Om1 + 1 + (M.B + 1 + o))) = Om1 + 1 + (M.B + 1 + o) := by
    rw [← rhF_zero]; exact tlI_rhF 0 _
  rw [hI'] at hI
  have hω : ω ≤ M.B + 1 + o :=
    (omega0_le_of_isSuccLimit zgBG_lim).trans (M.BG_B.trans (le_self_add.trans le_self_add))
  rw [add_assoc, one_add_of_omega0_le hω] at hI
  have hb := (tl_cl_Om1_add hZ).1 hI
  have hx : TlCl Z (M.B + 1) := TlCl.add (M.B_cl Z hZ hEgZ) (TlCl.one hZ.1)
  have := (tlDec hZ _ hb).1 _ hx le_self_add
  rwa [Ordinal.add_sub_cancel] at this

/-- The reading of the index `c = B + 1 + o`. -/
noncomputable def rR (c x : Ordinal.{0}) : Ordinal.{0} := M.Dv x + M.R (c - (M.B + 1)) x

/-- The gate of the index `c = B + 1 + o`. -/
noncomputable def rG (c : Ordinal.{0}) : Ordinal.{0} := M.G (c - (M.B + 1))

theorem rR_eq (o x : Ordinal.{0}) : M.rR (M.B + 1 + o) x = M.Dv x + M.R o x := by
  unfold rR; rw [Ordinal.add_sub_cancel]

theorem rG_eq (o : Ordinal.{0}) : M.rG (M.B + 1 + o) = M.G o := by
  unfold rG; rw [Ordinal.add_sub_cancel]

/-- **The gated cover** below `Γ_{Ω₁+1+c}` for a limit index `c ∈ (B_Γ+1, E)`. -/
theorem zmCover (h : M.B < M.E) {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1) {c : Ordinal.{0}}
    (hl : IsSuccLimit c) (hc0 : M.B + 1 < c) (hc : c < M.E) (hgc : M.rG c < Z) :
    ∀ d, GxCl Z (zbU.At Z) d → d < gcG c →
      ∃ b, M.B + 1 ≤ b ∧ b < c ∧ M.rG b < Z ∧ d < gcG b := by
  have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1.le
  have hZl : IsSuccLimit Z := ev_isSuccLimit_of_inE (gg_SC_eps hZ)
  have hEgZ : M.Eg < Z := by
    obtain ⟨o, rfl⟩ := exists_add_of_le hc0.le
    have ho0 : o ≠ 0 := by rintro rfl; rw [add_zero] at hc0; exact lt_irrefl _ hc0
    rw [rG_eq] at hgc; exact M.Eg_lt ho0 hgc
  have hg0 : M.rG (M.B + 1) < Z := by
    have e : M.rG (M.B + 1) = M.rG (M.B + 1 + 0) := by rw [add_zero]
    rw [e, rG_eq, M.G0]; exact hZ.1
  intro d hd
  induction hd with
  | small h' => exact fun _ => ⟨M.B + 1, le_rfl, hc0, hg0, (h'.trans hZ1).trans (gcG_Om1_lt _)⟩
  | om => exact fun _ => ⟨M.B + 1, le_rfl, hc0, hg0, gcG_Om1_lt _⟩
  | @atom s hs =>
    intro h'
    obtain ⟨b, rfl⟩ := zbU_atom_gcG hs
    have hbc : b < c := gcG_lt_iff.1 h'
    rcases lt_or_ge b (M.B + 1) with hb | hb
    · exact ⟨M.B + 1, le_rfl, hc0, hg0, gcG_lt hb⟩
    obtain ⟨o, rfl⟩ := exists_add_of_le hb
    have ho : o < M.E := le_add_self.trans_lt (hbc.trans hc)
    rcases hs with hs | ⟨c', hc', -, e⟩
    · have hT := M.zmInv h hZ hZ1' hEgZ ho hs.2.2.2
      have hgo := M.gate o Z hZ hZ1' hEgZ ho hT
      refine ⟨M.B + 1 + (o + 1), le_self_add, ?_, ?_, ?_⟩
      · rw [← add_assoc]; exact hl.add_one_lt hbc
      · rw [rG_eq]; exact M.g_succ o Z hZl hEgZ hgo
      · rw [← add_assoc]; exact gcG_lt (lt_add_one _)
    · exfalso
      have h1 : c' < M.B + 1 + o := (hc'.trans_le M.BG_B).trans ((lt_add_one _).trans_le le_self_add)
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

theorem rR_facts (hEg : M.Eg < x) {o : Ordinal.{0}} (ho : o < M.E) (hg : M.G o < x) :
    M.Dv x + M.R o x ∈ Tset x ∧ M.Dv x + M.R o x < Om1 ∧
      M.Dv x + M.R o x < ywX x ∧ gq (M.Dv x + M.R o x) x < ywX x := by
  obtain ⟨hXT, -, hX1, hXE⟩ := ywX_facts hx hx1
  have hDX : M.Dv x < ywX x := (M.Dv_T x hx hx1 hEg).2.2.2
  have hSX : M.Dv x + M.R o x < ywX x := (inE_indec hXE).add_lt hDX (M.R_X hx hx1 ho hg)
  have hST := vz_T_down hx hx1 hXT hX1 hSX.le
  exact ⟨hST, hSX.trans hX1, hSX, zm_gq_lt_X hx hx1 hST (hSX.trans hX1) hSX⟩

end Rd

/-- **A base layer for the index `B + 1`**: gate `0`, reading `gq(Dv(x))`, top `Γ_{Ω₁+1+B+1}`. -/
structure ZmBase (S : InaccSeq.{0}) (M : ZmDS) where
  L0 : GdB
  L0_g : L0.g ≤ M.Eg
  L0_E : ∀ x, InE x → x < Om1 → L0.K.E x = gq (M.Dv x) x
  L0_top : ∀ y, SC y → y < Om 1 → M.Eg < y → L0.K.E y = gxTh y (zbU.At y) (gcG (M.B + 1))
  L0_poly : ZbPolyG zbU L0.K.sys (gcG (M.B + 1))
  Dv_ge : ∀ x, InE x → x < Om1 → M.Eg < x → ywV 1 0 x ≤ M.Dv x

/-- **The base layer of `B_Γ + 1`** (`Zb.zbBGn 0`) for a system with base `B_Γ` read `D(x)`. -/
noncomputable def zmBaseBG (S : InaccSeq.{0}) (hB : M.B = tfBG) (hD : M.Dv = ywV 1 0) : ZmBase S M where
  L0 := (zbBGn 0).1
  L0_g := by rw [zbBGn_g 0]; exact zero_le
  L0_E := fun x _ _ => by rw [zbBGn_E 0 x, hD, Nat.cast_zero, add_zero]
  L0_top := fun y hy hy1 _ => by
    have h' := (zbBGn_codes S 0).1 y hy hy1 (by rw [zbBGn_g]; exact hy.1)
    rw [h', hB]; unfold zbT; norm_num
  L0_poly := by
    have h' := (zbBGn_codes S 0).2
    unfold zbT at h'; norm_num at h'
    rw [hB]; exact h'
  Dv_ge := fun x _ _ _ => by rw [hD]

/-- **THE READING SYSTEM OF THE INDICES `B + 1 + o`, `o < E`.** -/
noncomputable def toRS (S : InaccSeq.{0}) (h : M.B < M.E) (Lb : ZmBase S M) : ZbRS where
  c0 := M.B + 1
  Bd := M.E
  gt := fun c => max M.Eg (M.rG c)
  R := M.rR
  L0 := Lb.L0.mono (Lb.L0_g.trans (le_max_left _ _))
  c0_ne := (lt_of_le_of_lt zero_le (lt_add_one M.B)).ne'
  c0_lt := (inE_indec M.E_E).add_lt h M.one_lt_E
  Bd_X := M.E_X.le
  L0_g := rfl
  L0_E := fun x hx hx1 => by
    show Lb.L0.K.E x = gq (M.rR (M.B + 1) x) x
    rw [Lb.L0_E x hx hx1]
    have e : M.rR (M.B + 1) x = M.rR (M.B + 1 + 0) x := by rw [add_zero]
    rw [e, rR_eq, M.R0, add_zero]
  L0_top := fun y hy hy1 hg => Lb.L0_top y hy hy1 ((le_max_left _ _).trans_lt hg)
  L0_poly := Lb.L0_poly.mono (Lb.L0_g.trans (le_max_left _ _))
  RT := fun c x hx hx1 h1 h2 hg => by
    obtain ⟨o, rfl⟩ := exists_add_of_le h1
    have hEg : M.Eg < x := (le_max_left _ _).trans_lt hg
    have hgo : M.G o < x := by have h' := (le_max_right _ _).trans_lt hg; rwa [rG_eq] at h'
    rw [rR_eq]
    obtain ⟨hT, h1', -, hX⟩ := M.rR_facts hx hx1 hEg (le_add_self.trans_lt h2) hgo
    exact ⟨hT, h1', hX⟩
  mono := fun b c x hx hx1 h1 hbc hc hgb hgc => by
    obtain ⟨o₂, rfl⟩ := exists_add_of_le (h1.trans hbc.le)
    obtain ⟨o₁, rfl⟩ := exists_add_of_le h1
    have hgb' : M.G o₁ < x := by have h' := (le_max_right _ _).trans_lt hgb; rwa [rG_eq] at h'
    have hgc' : M.G o₂ < x := by have h' := (le_max_right _ _).trans_lt hgc; rwa [rG_eq] at h'
    rw [rR_eq, rR_eq]
    exact (add_lt_add_iff_left _).2 (M.mono o₁ o₂ x hx hx1 ((add_lt_add_iff_left _).1 hbc)
      (le_add_self.trans_lt hc) hgb' hgc')
  succ := fun b x hb => by
    obtain ⟨o, rfl⟩ := exists_add_of_le hb
    rw [add_assoc (M.B + 1) o 1, rR_eq, rR_eq, M.succ, add_assoc]
  gt_le_succ := fun b => by
    refine max_le_max le_rfl ?_
    rcases lt_or_ge b (M.B + 1) with hb | hb
    · unfold rG
      rw [show b - (M.B + 1) = 0 from Ordinal.sub_eq_zero_iff_le.2 hb.le, M.G0]; exact zero_le
    · obtain ⟨o, rfl⟩ := exists_add_of_le hb
      rw [add_assoc (M.B + 1) o 1, rG_eq, rG_eq]
      exact M.g_le o
  lim_R := fun c x hl hc0 hc hx hx1 hg => by
    obtain ⟨o, rfl⟩ := exists_add_of_le hc0.le
    have hgo : M.G o < x := by have h' := (le_max_right _ _).trans_lt hg; rwa [rG_eq] at h'
    have ho : o < M.E := le_add_self.trans_lt hc
    have hol : IsSuccLimit o := by
      rcases zero_or_succ_or_isSuccLimit o with h0 | ⟨s, hs⟩ | h'
      · subst h0; rw [add_zero] at hc0; exact absurd hc0 (lt_irrefl _)
      · exfalso
        have h' : IsSuccLimit (Order.succ (M.B + 1 + s)) := by
          rw [succ_eq_add_one, add_assoc, ← succ_eq_add_one s, hs]; exact hl
        exact Order.not_isSuccLimit_succ _ h'
      · exact h'
    rw [rR_eq]
    have hRl := M.lim o x hx hx1 hol ho hgo
    obtain ⟨σ, -, -, hσ1, hσ2⟩ := M.nc o x hx hx1 hol ho hgo
    exact ⟨isSuccLimit_add _ hRl, σ, hσ1, hσ2⟩
  cof := fun c x hl hc0 hc hx hx1 hg ν hν => by
    obtain ⟨o, rfl⟩ := exists_add_of_le hc0.le
    have hEg : M.Eg < x := (le_max_left _ _).trans_lt hg
    have hgo : M.G o < x := by have h' := (le_max_right _ _).trans_lt hg; rwa [rG_eq] at h'
    rw [rR_eq] at hν
    have ho : o < M.E := le_add_self.trans_lt hc
    have hol : IsSuccLimit o := by
      rcases zero_or_succ_or_isSuccLimit o with h0 | ⟨s, hs⟩ | h'
      · subst h0; rw [add_zero] at hc0; exact absurd hc0 (lt_irrefl _)
      · exfalso
        have h' : IsSuccLimit (Order.succ (M.B + 1 + s)) := by
          rw [succ_eq_add_one, add_assoc, ← succ_eq_add_one s, hs]; exact hl
        exact Order.not_isSuccLimit_succ _ h'
      · exact h'
    rcases le_or_gt ν (M.Dv x) with hνD | hDν
    · refine ⟨M.B + 1 + 0, le_self_add, (add_lt_add_iff_left _).2 hol.bot_lt, ?_, ?_⟩
      · show max M.Eg (M.rG _) < x
        rw [rG_eq, M.G0]; exact max_lt hEg hx.pos
      · rw [rR_eq, M.R0, add_zero]; exact hνD
    · obtain ⟨e, rfl⟩ := exists_add_of_le hDν.le
      have he : e < M.R o x := (add_lt_add_iff_left _).1 hν
      obtain ⟨b, hb, hgb, heb⟩ := M.cof o x hx hx1 hol ho hgo e he
      exact ⟨M.B + 1 + b, le_self_add, (add_lt_add_iff_left _).2 hb,
        by show max M.Eg (M.rG _) < x; rw [rG_eq]; exact max_lt hEg hgb,
        by rw [rR_eq]; exact (add_le_add_iff_left _).2 heb⟩
  ex := fun σ ρ c hB h1 h2 hg => by
    obtain ⟨o, rfl⟩ := exists_add_of_le h1
    change max M.Eg (M.rG _) < σ at hg
    have hEg : M.Eg < σ := (le_max_left _ _).trans_lt hg
    have hgo : M.G o < σ := by have h' := (le_max_right _ _).trans_lt hg; rwa [rG_eq] at h'
    show M.rR _ ρ ∈ TB ρ σ ∧ Googology.Trans.PoR.InaccPsi.R2.pi σ ρ (M.rR _ ρ) = M.rR _ σ
    rw [rR_eq, rR_eq]
    obtain ⟨d1, d2⟩ := M.Dv_pi σ ρ hB hEg
    obtain ⟨r1, r2⟩ := M.ex σ ρ o hB (le_add_self.trans_lt h2) hgo
    obtain ⟨s1, s2⟩ := pi_add hB d1 r1
    exact ⟨s1, by rw [s2, d2, r2]⟩
  cover := fun c Z hl hc0 hc hZ hZ1 hgc d hd hdT => by
    have hEgZ : M.Eg < Z := (le_max_left _ _).trans_lt hgc
    obtain ⟨b, h1, h2, h3, h4⟩ := M.zmCover h hZ hZ1 hl hc0 hc ((le_max_right _ _).trans_lt hgc) d hd hdT
    exact ⟨b, h1, h2, max_lt hEgZ h3, h4⟩
  cl := fun c Z h1 h2 hZ hg => by
    obtain ⟨o, rfl⟩ := exists_add_of_le h1
    change max M.Eg (M.rG _) < Z at hg
    have hEgZ : M.Eg < Z := (le_max_left _ _).trans_lt hg
    have hgo : M.G o < Z := by have h' := (le_max_right _ _).trans_lt hg; rwa [rG_eq] at h'
    have ho : o < M.E := le_add_self.trans_lt h2
    refine GxCl.atom (Or.inl ⟨gcG_SC _, gcG_Om1_lt _, ZbRS.gcG_lt_X (h2.trans_le M.E_X.le), ?_⟩)
    have harg : TlCl Z (Om1 + 1 + (M.B + 1 + o)) :=
      TlCl.add (TlCl.add TlCl.om (TlCl.one hZ.1))
        (TlCl.add (TlCl.add (M.B_cl Z hZ hEgZ) (TlCl.one hZ.1)) (M.cl o Z hZ ho hgo))
    rw [tf_gcG]
    exact TlCl.gam hZ.1 harg ((lt_add_one _).trans_le le_self_add)
  D_le := fun c x hx hx1 hc0 hc hg => by
    obtain ⟨o, rfl⟩ := exists_add_of_le hc0.le
    show ywV 1 0 x ≤ M.rR (M.B + 1 + o) x
    rw [rR_eq]
    exact (Lb.Dv_ge x hx hx1 ((le_max_left _ _).trans_lt hg)).trans le_self_add
  BG_top := fun y hy hy1 => zbBG_top S hy hy1
  BG_poly := zbBG_poly S
  BG_c0 := M.BG_B.trans (le_self_add.trans gcG_strictMono.le_apply)

/-- **`ZbDirect S E`** for a system with base `B_Γ` read `D(x)`: a layer for every index `B_Γ ≤ B < E`
(`B = B_Γ + 1 + o`: the layer of `B_Γ + 1 + o'`, `o ≤ o' < E` with gate `≤ max Eg 1`, `M.Gc0`). -/
theorem direct (hB : M.B = tfBG) (hD : M.Dv = ywV 1 0) (S : InaccSeq.{0}) (h : tfBG < M.E)
    (hK : M.Eg < Td.tdK S) (hc : M.Gc0) : ZbDirect S M.E := by
  have h' : M.B < M.E := hB ▸ h
  intro B hB1 hB2
  rcases hB1.lt_or_eq with hlt | heq
  · rw [← hB] at hlt
    obtain ⟨o, rfl⟩ := exists_add_of_le (Order.add_one_le_of_lt hlt)
    have ho : o < M.E := le_add_self.trans_lt hB2
    obtain ⟨o', hoo', ho', hg'⟩ := hc o ho
    have hg : (M.toRS S h' (M.zmBaseBG S hB hD)).gt (M.B + 1 + o') < Td.tdK S := by
      show max M.Eg (M.rG _) < Td.tdK S
      rw [rG_eq]; exact max_lt hK (hg'.trans_lt (max_lt hK (gg_one_lt_of_SC Td.tdK_SC)))
    exact zbLayAt_mono ((add_le_add_iff_left _).2 hoo')
      ((M.toRS S h' (M.zmBaseBG S hB hD)).layAt S le_self_add (M.idx_lt h' ho') hg)
  · rw [← heq]; exact zbLayAt_BG S

/-- **UPPER ∧ LOWER ∧ CapV at every range restart below `ι(Γ_{Ω₁+1+B}·ω)`, every `B < E`.** -/
theorem UV (hB : M.B = tfBG) (hD : M.Dv = ywV 1 0) (S : InaccSeq.{0}) (h : tfBG < M.E) (hK : M.Eg < Td.tdK S)
    (hc : M.Gc0) {B l : Ordinal.{0}} (hB' : B < M.E) (hr : CdRange S l) (hl : l < iota S (gcG B * ω)) :
    CdUpper S l ∧ CdLower S l ∧ CdCapV S l :=
  zbUV_of_direct (M.direct hB hD S h hK hc) l hr B hB' hl

end ZmDS

end Googology.Trans.PoR.InaccPsi.R2.Zm
