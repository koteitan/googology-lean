import Googology.Trans.PoR.InaccPsi.R2.ZbRS

/-!
# ZbE0: THE READING SYSTEM OF THE INDICES `B_Γ + 1 + o`, `o < ε₀` — `ZbDirect S (B_Γ + ε₀)`

The atom `Γ_{Ω₁+1+(B_Γ+1+o)} = Γ_{B_Γ+1+o}` (`o < ε₀` a constant) reads `ϑˣ(Ω₁·Ω₁ + D(x) + o)`, `D(x) = ϑˣ(Ω₁·Ω₁ +
Ω₁)` the reading of `B_Γ` (`Yw.ywBG`): the offsets `D(x) + o` are not fixed points of `ν ↦ ϑˣ(Ω₁·Ω₁ + ν)` at limits
(`D(x) + o < ϑˣ(Ω₁·Ω₁ + D(x) + 1)`), so the union step works at every limit `o` (`Zb.zb_lt_lim_iff`), while
`Yr.YrN` fails for every offset `≥ D(x)`.  `zbE0 S : Zb.ZbRS` (gate `0`, base layer `Zb.zbBGn 0 = Yw.ywBG1B`), so
`Zb.ZbRS.direct` gives `ZbDirect S (B_Γ + ε₀)`: UPPER ∧ LOWER ∧ CapV at every range restart below
`ι(Γ_{Ω₁+1+B}·ω)` for every `B < B_Γ + ε₀`, i.e. below `ι(Γ_{B_Γ+ε₀})`.

* `zbO` (the offset `c − (B_Γ+1)`), `zbR0` (the reading), `zbBG_tl`, `zbDo_T`, `zbE0` (**THE READING SYSTEM**);
* `zbDirect_e0` (**`ZbDirect S (B_Γ + ε₀)`, UNCONDITIONAL**), `zbUV_e0`.

No new axiom.  New definitions: `zbO`, `zbR0`, `zbE0`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Ge
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gb

/-- The offset of a code past `B_Γ + 1`. -/
noncomputable def zbO (c : Ordinal.{0}) : Ordinal.{0} := c - (tfBG + 1)

/-- **The reading** `D(x) + o` of the code `B_Γ + 1 + o`. -/
noncomputable def zbR0 (c x : Ordinal.{0}) : Ordinal.{0} := ywV 1 0 x + zbO c

theorem zbO_add (o : Ordinal.{0}) : zbO (tfBG + 1 + o) = o := Ordinal.add_sub_cancel _ _

theorem zbBd_eq : tfBG + 1 + ε₀ = tfBG + ε₀ := by
  rw [add_assoc, one_add_of_omega0_le (omega0_le_of_isSuccLimit gc_eps0_lim)]

theorem zbO_lt {c : Ordinal.{0}} (h1 : tfBG + 1 ≤ c) (h2 : c < tfBG + ε₀) : zbO c < ε₀ := by
  obtain ⟨o, rfl⟩ := exists_add_of_le h1
  rw [zbO_add]
  rw [← zbBd_eq] at h2
  exact (add_lt_add_iff_left _).1 h2

theorem zbBG_tl {Z : Ordinal.{0}} (hZ : 0 < Z) : TlCl Z tfBG := by
  rw [tl_BG_eq]
  exact TlCl.atom (TlCl.one hZ) (TlCl.add TlCl.om (TlCl.one hZ)) (by rw [← tl_BG_eq]; exact tfBG_gt)

section Off

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem zbDo_T {o : Ordinal.{0}} (ho : o < ε₀) :
    ywV 1 0 x + o ∈ Tset x ∧ ywV 1 0 x + o < Om1 ∧ gq (ywV 1 0 x + o) x < ywX x := by
  obtain ⟨-, hDT, -⟩ := ywD_closed hx hx1
  have hox : o < x := ho.trans_le (gc_eps0_le hx)
  obtain ⟨-, hxX, hX1, hXE⟩ := ywX_facts hx hx1
  have hT : ywV 1 0 x + o ∈ Tset x := vzT_add hx hx1 hDT (mem_T_of_le hx hx1 hox.le)
  have hlt : ywV 1 0 x + o < ywX x := (inE_indec hXE).add_lt (ywD_lt_X hx hx1) (hox.trans hxX)
  refine ⟨hT, hlt.trans hX1, ?_⟩
  rw [← ywV_zero]
  exact ywV_lt_X hx hx1 (mem_T_of_le hx hx1 zero_le) (hx.pos.trans hx1) hT (hlt.trans hX1) (hx.pos.trans hxX) hlt

end Off

/-- **THE READING SYSTEM OF THE INDICES `B_Γ + 1 + o`, `o < ε₀`** (gate `0`). -/
noncomputable def zbE0 (S : InaccSeq.{0}) : ZbRS where
  c0 := tfBG + 1
  Bd := tfBG + ε₀
  gt := fun _ => 0
  R := zbR0
  L0 := (zbBGn 0).1
  c0_ne := (lt_of_le_of_lt zero_le (lt_add_one tfBG)).ne'
  c0_lt := (add_lt_add_iff_left _).2 (one_lt_omega0.trans_le (omega0_le_of_isSuccLimit gc_eps0_lim))
  Bd_X := (tlX_SC.isPrincipal tl_BG_lt_X (gc_eps0_le_Om1.trans_lt (by rw [← Br.Om1_eq]; exact tlX_gt))).le
  L0_g := zbBGn_g 0
  L0_E := fun x _ _ => by
    rw [zbBGn_E 0 x]
    show gq (ywV 1 0 x + ((0 : ℕ) : Ordinal.{0})) x = gq (ywV 1 0 x + zbO (tfBG + 1)) x
    rw [show tfBG + 1 = tfBG + 1 + 0 from (add_zero _).symm, zbO_add, Nat.cast_zero]
  L0_top := fun y hy hy1 _ => by
    have h := (zbBGn_codes S 0).1 y hy hy1 (by rw [zbBGn_g]; exact hy.1)
    rw [h]; unfold zbT; norm_num
  L0_poly := by
    have h := (zbBGn_codes S 0).2
    unfold zbT at h; norm_num at h
    exact h
  RT := fun c x hx hx1 h1 h2 _ => zbDo_T hx hx1 (zbO_lt h1 h2)
  mono := fun b c x _ _ h1 hbc _ _ _ => by
    show ywV 1 0 x + zbO b < ywV 1 0 x + zbO c
    obtain ⟨ob, rfl⟩ := exists_add_of_le h1
    obtain ⟨oc, rfl⟩ := exists_add_of_le (h1.trans hbc.le)
    rw [zbO_add, zbO_add]
    exact (add_lt_add_iff_left _).2 ((add_lt_add_iff_left _).1 hbc)
  succ := fun b x hb => by
    show ywV 1 0 x + zbO (b + 1) = ywV 1 0 x + zbO b + 1
    obtain ⟨o, rfl⟩ := exists_add_of_le hb
    rw [add_assoc (tfBG + 1) o 1, zbO_add, zbO_add, add_assoc]
  gt_le_succ := fun _ => le_rfl
  lim_R := fun c x hl hc0 hc hx hx1 _ => by
    show IsSuccLimit (ywV 1 0 x + zbO c) ∧ ∃ σ, σ < ywV 1 0 x + zbO c ∧ ywV 1 0 x + zbO c < gq σ x
    obtain ⟨o, rfl⟩ := exists_add_of_le hc0.le
    rw [zbO_add]
    have ho0 : o ≠ 0 := by rintro rfl; rw [add_zero] at hc0; exact lt_irrefl _ hc0
    have hol : IsSuccLimit o := by
      rcases zero_or_succ_or_isSuccLimit o with h | ⟨s, hs⟩ | h
      · exact absurd h ho0
      · exfalso
        have h' : IsSuccLimit (Order.succ (tfBG + 1 + s)) := by
          rw [succ_eq_add_one, add_assoc, ← succ_eq_add_one s, hs]; exact hl
        exact Order.not_isSuccLimit_succ _ h'
      · exact h
    have hoε : o < ε₀ := by
      have := zbO_lt (c := tfBG + 1 + o) le_self_add hc
      rwa [zbO_add] at this
    obtain ⟨hDT, -, -⟩ := zbDo_T hx hx1 (o := 1) (one_lt_omega0.trans_le (omega0_le_of_isSuccLimit gc_eps0_lim))
    obtain ⟨-, hD1, -⟩ := zbDo_T hx hx1 (o := 1) (one_lt_omega0.trans_le (omega0_le_of_isSuccLimit gc_eps0_lim))
    obtain ⟨-, hxG, -, hGE, -⟩ := geq_facts hx hx1 hDT hD1
    have h1o : (1 : Ordinal.{0}) < o := by simpa using hol.add_one_lt hol.bot_lt
    have hox : o < x := hoε.trans_le (gc_eps0_le hx)
    refine ⟨isSuccLimit_add _ hol, ywV 1 0 x + 1, (add_lt_add_iff_left _).2 h1o, ?_⟩
    calc ywV 1 0 x + o ≤ ywV 1 0 x + 1 + o := by gcongr; exact le_self_add
      _ < gq (ywV 1 0 x + 1) x := (inE_indec hGE).add_lt (gmq_gt hx hx1 hDT hD1) (hox.trans hxG)
  cof := fun c x _ hc0 _ hx _ _ ν hν => by
    change ν < ywV 1 0 x + zbO c at hν
    obtain ⟨o, rfl⟩ := exists_add_of_le hc0.le
    rw [zbO_add] at hν
    rcases le_or_gt ν (ywV 1 0 x) with hνD | hDν
    · refine ⟨tfBG + 1, le_rfl, hc0, hx.pos, ?_⟩
      show ν ≤ ywV 1 0 x + zbO (tfBG + 1)
      rw [show tfBG + 1 = tfBG + 1 + 0 from (add_zero _).symm, zbO_add, add_zero]
      exact hνD
    · obtain ⟨e, rfl⟩ := exists_add_of_le hDν.le
      have heo : e < o := (add_lt_add_iff_left _).1 hν
      refine ⟨tfBG + 1 + e, le_self_add, (add_lt_add_iff_left _).2 heo, ?_, ?_⟩
      · exact hx.pos
      · show ywV 1 0 x + e ≤ ywV 1 0 x + zbO (tfBG + 1 + e)
        rw [zbO_add]
  ex := fun σ ρ c hB h1 h2 _ => by
    show ywV 1 0 ρ + zbO c ∈ TB ρ σ ∧ Googology.Trans.PoR.InaccPsi.R2.pi σ ρ (ywV 1 0 ρ + zbO c) =
      ywV 1 0 σ + zbO c
    have h1σ : (1 : Ordinal.{0}) < σ := lu_one_lt_E hB.1
    have h0σ : (0 : Ordinal.{0}) < σ := hB.1.pos
    have hoσ : zbO c < σ := (zbO_lt h1 h2).trans_le (gc_eps0_le hB.1)
    have hD := ywV_pi hB (mem_TB_of_lt hB h1σ) ((lu_one_lt_E hB.2.1).trans hB.2.2.2) (mem_TB_of_lt hB h0σ)
      (hB.2.1.pos.trans hB.2.2.2)
    rw [pi_lt hB h1σ, pi_lt hB h0σ] at hD
    obtain ⟨h3, h4⟩ := pi_add hB hD.1 (mem_TB_of_lt hB hoσ)
    exact ⟨h3, by rw [h4, hD.2, pi_lt hB hoσ]⟩
  cover := fun c Z hl hc0 _ hZ hZ1 _ d hd hdT => by
    obtain ⟨b, hb, hdb⟩ := zbCover hZ1.le hl d hd hdT
    exact ⟨max b (tfBG + 1), le_max_right _ _, max_lt hb hc0, hZ.1,
      hdb.trans_le (gcG_le (le_max_left _ _))⟩
  cl := fun c Z h1 h2 hZ _ => by
    refine GxCl.atom (Or.inl ⟨gcG_SC _, gcG_Om1_lt _, ZbRS.gcG_lt_X (h2.trans_le ?_), ?_⟩)
    · exact (tlX_SC.isPrincipal tl_BG_lt_X (gc_eps0_le_Om1.trans_lt (by rw [← Br.Om1_eq]; exact tlX_gt))).le
    · obtain ⟨o, rfl⟩ := exists_add_of_le h1
      have ho : o < ε₀ := by have := zbO_lt h1 h2; rwa [zbO_add] at this
      have hoZ : o < Z := ho.trans_le (gc_eps0_le (gg_SC_eps hZ))
      have harg : TlCl Z (Om1 + 1 + (tfBG + 1 + o)) :=
        TlCl.add (TlCl.add TlCl.om (TlCl.one hZ.1))
          (TlCl.add (TlCl.add (zbBG_tl hZ.1) (TlCl.one hZ.1)) (TlCl.small hoZ))
      rw [tf_gcG]
      exact TlCl.gam hZ.1 harg ((lt_add_one _).trans_le le_self_add)
  D_le := fun c x _ _ _ _ _ => show ywV 1 0 x ≤ ywV 1 0 x + zbO c from le_self_add
  BG_top := fun y hy hy1 => zbBG_top S hy hy1
  BG_poly := zbBG_poly S
  BG_c0 := le_self_add.trans gcG_strictMono.le_apply

/-- **`ZbDirect S (B_Γ + ε₀)`, UNCONDITIONAL.** -/
theorem zbDirect_e0 (S : InaccSeq.{0}) : ZbDirect S (tfBG + ε₀) :=
  (zbE0 S).direct S rfl fun _ => Td.tdK_SC.1

/-- **UPPER ∧ LOWER ∧ CapV at every range restart below `ι(Γ_{Ω₁+1+B}·ω)`, every `B < B_Γ + ε₀`** (UNCONDITIONAL). -/
theorem zbUV_e0 (S : InaccSeq.{0}) {B l : Ordinal.{0}} (hB : B < tfBG + ε₀) (hr : CdRange S l)
    (hl : l < iota S (gcG B * ω)) : CdUpper S l ∧ CdLower S l ∧ CdCapV S l :=
  zbUV_of_direct (zbDirect_e0 S) l hr B hB hl

end Googology.Trans.PoR.InaccPsi.R2.Zb
