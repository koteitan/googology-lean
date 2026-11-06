import Googology.Trans.PoR.InaccPsi.R2.ZgTl

/-!
# ZgB2: THE READING SYSTEM OF THE INDICES `B_Γ + 1 + o`, `o < B_Γ` — `ZbDirect S (B_Γ·2)`

The atom `Γ_{Ω₁+1+(B_Γ+1+o)}` (`o < B_Γ` a `Yr` code) reads `ϑˣ(Ω₁·Ω₁ + D(x) + Yr.yrR o x)`, `D(x) = ϑˣ(Ω₁·Ω₁ +
Ω₁)` the reading of `B_Γ`; gate `Yr.yrG o`.  Every admissible reading `Yr.yrR o x` is below `D(x)` (`zgN_lt_D`), so
the offsets `D(x) + yrR o x` are not fixed points of `ν ↦ ϑˣ(Ω₁·Ω₁ + ν)` at limits.  `zgB2 : Zb.ZbRS` (order
`Yr.yrR_mono`, successor `Yr.yrR_succ`, limits `Yr.yr_lim_of_cof` / `Yr.yrR_cof`, Lemma EXACT `Yr.yr_pi`, the
atom a code of `zbU` by `Zg.zgYr`, the gated cover `zgCover`).  Gates of every countable size occur; `ZbDirect`
asks a gate below `K` only for the layer of a larger index with the same top, so the tower `Yr.yrTw` (gate `0`,
cofinal in `B_Γ`) gives `ZbDirect S (B_Γ·2)` (`zgDirect2`).

* `zgN_lt_D`, `zgAtom`, `zgInv` (**`TlCl Z (Γ_{Ω₁+1+(B_Γ+1+o)})` ⇒ `TlCl Z o`**), `zgGate`, `zgCover`;
* `zgB2` (**THE READING SYSTEM**), `zbLayAt_mono`, `zgDirect2` (**`ZbDirect S (B_Γ + B_Γ)`, UNCONDITIONAL**),
  `zgUV2`.

No new axiom.  New definitions: `zgR2`, `zgB2`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Ge
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Rh

/-- **Every admissible offset is below `D(x) = ϑˣ(Ω₁·Ω₁ + Ω₁)`.** -/
theorem zgN_lt_D {x v : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (h : YrN x v) : v < ywV 1 0 x := by
  by_contra hc
  push Not at hc
  obtain ⟨-, hDT, hD⟩ := ywD_closed hx hx1
  obtain ⟨h1T, h1Ω⟩ := yw_one hx hx1
  obtain ⟨-, -, -, hDE, -, -, -⟩ := ywV_facts hx hx1 h1T h1Ω (mem_T_of_le hx hx1 zero_le) (hx.pos.trans hx1)
  obtain ⟨σ, hσ, hlt⟩ := h.2.2 _ (ev_isSuccLimit_of_inE hDE) hc
  have hσT : σ ∈ Tset x := vz_T_down hx hx1 h.1 h.2.1 (hσ.le.trans hc)
  exact absurd (hD σ hσT hσ) (not_lt.2 hlt.le)

/-- `B_Γ + 1 + o` is not a fixed point of `Γ` (`Ω₁ + 1 + (B_Γ + 1 + o) < Γ_{…}`). -/
theorem zg_nonfix {o : Ordinal.{0}} (ho : o < tfBG) :
    Om1 + 1 + (tfBG + 1 + o) < gamma (Om1 + 1 + (tfBG + 1 + o)) := by
  set ν := Om1 + 1 + (tfBG + 1 + o) with hν
  have hE : ω ^ tfBG = tfBG := Low.opow_eq_self_of_SC tfBG_SC
  have h1 : Om1 + 1 + tfBG = tfBG :=
    Ordinal.add_of_omega0_opow_le (c := tfBG) (by rw [hE]; exact tl_Om1_succ_lt_BG) (by rw [hE])
  have hνe : ν = tfBG + (1 + o) := by rw [hν, ← add_assoc, ← add_assoc, h1, add_assoc]
  have hB : tfBG < ν := by
    rw [hνe]; exact lt_add_of_pos_right _ (lt_of_lt_of_le zero_lt_one le_self_add)
  rcases (isNormal_gamma.strictMono.le_apply (x := ν)).lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  have hSC : SC ν := by rw [heq]; exact Lq.lq_gamma_SC ν
  have hP := tl_SC_prin hSC
  have h1o : 1 + o < ν := (tfBG_SC.isPrincipal (gg_one_lt_of_SC tfBG_SC) ho).trans hB
  have : tfBG + (1 + o) < ν := hP hB h1o
  rw [← hνe] at this
  exact lt_irrefl _ this

/-- **The index of the atom is a code**: `TlCl Z (Γ_{Ω₁+1+(B_Γ+1+o)})` ⇒ `TlCl Z o` (`Z ≤ Ω₁` strongly critical). -/
theorem zgInv {Z o : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om1) (ho : o < tfBG)
    (h : TlCl Z (gcG (tfBG + 1 + o))) : TlCl Z o := by
  rw [tf_gcG] at h
  have hlt := zg_nonfix ho
  have hO : Om1 < gamma (Om1 + 1 + (tfBG + 1 + o)) := by
    rw [← tf_gcG, Br.Om1_eq]; exact gcG_Om1_lt _
  obtain ⟨-, hI⟩ := tl_cl_atom hZ1 _ h (Lq.lq_gamma_SC _) hO
  rw [tlLev_gamma hlt] at hI
  have hI' : tlI 0 (gamma (Om1 + 1 + (tfBG + 1 + o))) = Om1 + 1 + (tfBG + 1 + o) := by
    rw [← rhF_zero]; exact tlI_rhF 0 _
  rw [hI'] at hI
  have hω : ω ≤ tfBG + 1 + o := (omega0_le_of_isSuccLimit (ev_isSuccLimit_of_inE
    (Low.opow_eq_self_of_SC tfBG_SC))).trans (le_self_add.trans le_self_add)
  rw [add_assoc, one_add_of_omega0_le hω] at hI
  have hb := (tl_cl_Om1_add hZ).1 hI
  have hx : TlCl Z (tfBG + 1) := TlCl.add (zbBG_tl hZ.1) (TlCl.one hZ.1)
  have := (tlDec hZ _ hb).1 _ hx le_self_add
  rwa [Ordinal.add_sub_cancel] at this

/-- **The gate of a `TlCl` code below `B_Γ`** (`Zb.zb_tl_K`, `Yr.yr_code_gate`). -/
theorem zgGate {Z o : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om1) (ho : o < tfBG) (h : TlCl Z o) : yrG o < Z :=
  yr_code_gate hZ hZ1 zbKAt_hA o (zb_tl_K hZ hZ1 o ho h)

/-- **The atom `Γ_{Ω₁+1+(B_Γ+1+o)}` is an atom of `zbU` over `Z` above the gate.** -/
theorem zgAtom {Z o : Ordinal.{0}} (hZ : SC Z) (ho : o < tfBG) (hg : yrG o < Z) :
    GxCl Z (zbU.At Z) (gcG (tfBG + 1 + o)) := by
  have hBd : tfBG + 1 + o < tlX := tlX_SC.isPrincipal (tlX_SC.isPrincipal tl_BG_lt_X
    ((gg_one_lt_of_SC tfBG_SC).trans tl_BG_lt_X)) (ho.trans tl_BG_lt_X)
  refine GxCl.atom (Or.inl ⟨gcG_SC _, gcG_Om1_lt _, ZbRS.gcG_lt_X hBd, ?_⟩)
  have harg : TlCl Z (Om1 + 1 + (tfBG + 1 + o)) :=
    TlCl.add (TlCl.add TlCl.om (TlCl.one hZ.1))
      (TlCl.add (TlCl.add (zbBG_tl hZ.1) (TlCl.one hZ.1)) (zgYr hZ.1 o ho hg).1)
  rw [tf_gcG]
  exact TlCl.gam hZ.1 harg ((lt_add_one _).trans_le le_self_add)

theorem zbO_c0 : zbO (tfBG + 1) = 0 := Ordinal.sub_self _

theorem zbO_lt2 {c : Ordinal.{0}} (h1 : tfBG + 1 ≤ c) (h2 : c < tfBG + tfBG) : zbO c < tfBG := by
  obtain ⟨o, rfl⟩ := exists_add_of_le h1
  rw [zbO_add]
  rw [add_assoc] at h2
  exact le_add_self.trans_lt ((add_lt_add_iff_left _).1 h2)

/-- **The gated cover**: a code of `zbU` over `Z` below `Γ_{Ω₁+1+c}` (`c` a limit index in `(B_Γ+1, B_Γ·2)`) is
below `Γ_{Ω₁+1+b}` for some `b ∈ [B_Γ+1, c)` with gate `yrG (b − (B_Γ+1)) < Z`. -/
theorem zgCover {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1) {c : Ordinal.{0}} (hl : IsSuccLimit c)
    (hc0 : tfBG + 1 < c) (hc : c < tfBG + tfBG) :
    ∀ d, GxCl Z (zbU.At Z) d → d < gcG c →
      ∃ b, tfBG + 1 ≤ b ∧ b < c ∧ yrG (zbO b) < Z ∧ d < gcG b := by
  have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1.le
  have hg0 : yrG (zbO (tfBG + 1)) < Z := by rw [zbO_c0, yrG_zero]; exact hZ.1
  intro d hd
  induction hd with
  | small h => exact fun _ => ⟨tfBG + 1, le_rfl, hc0, hg0, (h.trans hZ1).trans (gcG_Om1_lt _)⟩
  | om => exact fun _ => ⟨tfBG + 1, le_rfl, hc0, hg0, gcG_Om1_lt _⟩
  | @atom s hs =>
    intro h
    obtain ⟨b, rfl⟩ := zbU_atom_gcG hs
    have hbc : b < c := gcG_lt_iff.1 h
    rcases lt_or_ge b (tfBG + 1) with hb | hb
    · exact ⟨tfBG + 1, le_rfl, hc0, hg0, gcG_lt hb⟩
    obtain ⟨o, rfl⟩ := exists_add_of_le hb
    have ho : o < tfBG := by have := zbO_lt2 hb (hbc.trans hc); rwa [zbO_add] at this
    rcases hs with hs | ⟨c', hc', -, e⟩
    · have hgo := zgGate hZ hZ1' ho (zgInv hZ hZ1' ho hs.2.2.2)
      refine ⟨tfBG + 1 + o + 1, le_self_add.trans le_self_add, hl.add_one_lt hbc, ?_, gcG_lt (lt_add_one _)⟩
      rw [add_assoc (tfBG + 1) o 1, zbO_add]
      exact yrG_succ (ev_isSuccLimit_of_inE (gg_SC_eps hZ)) o hgo
    · exfalso
      have h1 : c' < tfBG + 1 + o := hc'.trans ((lt_add_one _).trans_le le_self_add)
      exact absurd e (gcG_lt h1).ne'
  | @add a b _ _ iha ihb =>
    intro h
    obtain ⟨b1, h1, h1', g1, e1⟩ := iha (lt_of_le_of_lt le_self_add h)
    obtain ⟨b2, h2, h2', g2, e2⟩ := ihb (lt_of_le_of_lt le_add_self h)
    rcases le_total b1 b2 with hle | hle
    · exact ⟨b2, h2, h2', g2, (gcG_SC _).isPrincipal (e1.trans_le (gcG_le hle)) e2⟩
    · exact ⟨b1, h1, h1', g1, (gcG_SC _).isPrincipal e1 (e2.trans_le (gcG_le hle))⟩
  | @phi a b _ _ iha ihb =>
    intro h
    obtain ⟨b1, h1, h1', g1, e1⟩ := iha (lt_of_le_of_lt (left_le_veblen a b) h)
    obtain ⟨b2, h2, h2', g2, e2⟩ := ihb (lt_of_le_of_lt (right_le_veblen a b) h)
    rcases le_total b1 b2 with hle | hle
    · exact ⟨b2, h2, h2', g2, (gcG_SC _).2 _ (e1.trans_le (gcG_le hle)) _ e2⟩
    · exact ⟨b1, h1, h1', g1, (gcG_SC _).2 _ e1 _ (e2.trans_le (gcG_le hle))⟩

/-- **The reading** `D(x) + yrR o x` of the index `B_Γ + 1 + o`. -/
noncomputable def zgR2 (c x : Ordinal.{0}) : Ordinal.{0} := ywV 1 0 x + yrR (zbO c) x

section Off

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem zgDo_T {o : Ordinal.{0}} (ho : o < tfBG) (hg : yrG o < x) :
    ywV 1 0 x + yrR o x ∈ Tset x ∧ ywV 1 0 x + yrR o x < Om1 ∧ gq (ywV 1 0 x + yrR o x) x < ywX x ∧
      yrR o x < ywV 1 0 x := by
  obtain ⟨-, hDT, -⟩ := ywD_closed hx hx1
  obtain ⟨hrT, -⟩ := yrR_T hx hx1 ho hg
  have hrD := zgN_lt_D hx hx1 (yrR_N hx hx1 ho hg)
  obtain ⟨-, -, hX1, hXE⟩ := ywX_facts hx hx1
  have hT : ywV 1 0 x + yrR o x ∈ Tset x := vzT_add hx hx1 hDT hrT
  have hlt : ywV 1 0 x + yrR o x < ywX x :=
    (inE_indec hXE).add_lt (ywD_lt_X hx hx1) (hrD.trans (ywD_lt_X hx hx1))
  refine ⟨hT, hlt.trans hX1, ?_, hrD⟩
  rw [← ywV_zero]
  exact ywV_lt_X hx hx1 (mem_T_of_le hx hx1 zero_le) (hx.pos.trans hx1) hT (hlt.trans hX1)
    (hx.pos.trans (ywX_facts hx hx1).2.1) hlt

end Off

/-- **THE READING SYSTEM OF THE INDICES `B_Γ + 1 + o`, `o < B_Γ`** (gate `yrG o`). -/
noncomputable def zgB2 (S : InaccSeq.{0}) : ZbRS where
  c0 := tfBG + 1
  Bd := tfBG + tfBG
  gt := fun c => yrG (zbO c)
  R := zgR2
  L0 := (zbBGn 0).1
  c0_ne := (lt_of_le_of_lt zero_le (lt_add_one tfBG)).ne'
  c0_lt := (add_lt_add_iff_left _).2 (gg_one_lt_of_SC tfBG_SC)
  Bd_X := (tlX_SC.isPrincipal tl_BG_lt_X tl_BG_lt_X).le
  L0_g := by rw [zbBGn_g 0]; show (0 : Ordinal.{0}) = yrG (zbO (tfBG + 1)); rw [zbO_c0, yrG_zero]
  L0_E := fun x _ _ => by
    rw [zbBGn_E 0 x]
    show gq (ywV 1 0 x + ((0 : ℕ) : Ordinal.{0})) x = gq (ywV 1 0 x + yrR (zbO (tfBG + 1)) x) x
    rw [zbO_c0, yrR_zero, Nat.cast_zero]
  L0_top := fun y hy hy1 _ => by
    have h := (zbBGn_codes S 0).1 y hy hy1 (by rw [zbBGn_g]; exact hy.1)
    rw [h]; unfold zbT; norm_num
  L0_poly := by
    have h := (zbBGn_codes S 0).2
    unfold zbT at h; norm_num at h
    exact h
  RT := fun c x hx hx1 h1 h2 hg => by
    obtain ⟨a, b, d, -⟩ := zgDo_T hx hx1 (zbO_lt2 h1 h2) hg
    exact ⟨a, b, d⟩
  mono := fun b c x hx hx1 h1 hbc hc hgb hgc => by
    show ywV 1 0 x + yrR (zbO b) x < ywV 1 0 x + yrR (zbO c) x
    have hoc := zbO_lt2 (h1.trans hbc.le) hc
    obtain ⟨ob, rfl⟩ := exists_add_of_le h1
    obtain ⟨oc, rfl⟩ := exists_add_of_le (h1.trans hbc.le)
    rw [zbO_add] at hgb ⊢; rw [zbO_add] at hgc hoc ⊢
    exact (add_lt_add_iff_left _).2 (yrR_mono hx hx1 hoc ((add_lt_add_iff_left _).1 hbc) hgc hgb)
  succ := fun b x hb => by
    show ywV 1 0 x + yrR (zbO (b + 1)) x = ywV 1 0 x + yrR (zbO b) x + 1
    obtain ⟨o, rfl⟩ := exists_add_of_le hb
    rw [add_assoc (tfBG + 1) o 1, zbO_add, zbO_add, yrR_succ, add_assoc]
  gt_le_succ := fun b => by
    show yrG (zbO b) ≤ yrG (zbO (b + 1))
    rcases lt_or_ge b (tfBG + 1) with hb | hb
    · rw [show zbO b = 0 from Ordinal.sub_eq_zero_iff_le.2 hb.le, yrG_zero]; exact zero_le
    · obtain ⟨o, rfl⟩ := exists_add_of_le hb
      rw [add_assoc (tfBG + 1) o 1, zbO_add, zbO_add]
      exact yrG_le_succ o
  lim_R := fun c x hl hc0 hc hx hx1 hg => by
    show IsSuccLimit (ywV 1 0 x + yrR (zbO c) x) ∧
      ∃ σ, σ < ywV 1 0 x + yrR (zbO c) x ∧ ywV 1 0 x + yrR (zbO c) x < gq σ x
    have hoB := zbO_lt2 hc0.le hc
    obtain ⟨o, rfl⟩ := exists_add_of_le hc0.le
    change yrG (zbO (tfBG + 1 + o)) < x at hg
    rw [zbO_add] at hg hoB ⊢
    have ho0 : o ≠ 0 := by rintro rfl; rw [add_zero] at hc0; exact lt_irrefl _ hc0
    have hol : IsSuccLimit o := by
      rcases zero_or_succ_or_isSuccLimit o with h | ⟨s, hs⟩ | h
      · exact absurd h ho0
      · exfalso
        have h' : IsSuccLimit (Order.succ (tfBG + 1 + s)) := by
          rw [succ_eq_add_one, add_assoc, ← succ_eq_add_one s, hs]; exact hl
        exact Order.not_isSuccLimit_succ _ h'
      · exact h
    have hrl : IsSuccLimit (yrR o x) := yr_lim_of_cof hx hx1 hol hoB hg (yrR_cof hx hx1 o hoB)
    obtain ⟨-, -, -, hrD⟩ := zgDo_T hx hx1 hoB hg
    obtain ⟨hDT, hD1, -⟩ := zbDo_T hx hx1 (o := 1) (one_lt_omega0.trans_le (omega0_le_of_isSuccLimit gc_eps0_lim))
    obtain ⟨-, -, -, hGE, -⟩ := geq_facts hx hx1 hDT hD1
    have h1r : (1 : Ordinal.{0}) < yrR o x := by simpa using hrl.add_one_lt hrl.bot_lt
    refine ⟨isSuccLimit_add _ hrl, ywV 1 0 x + 1, (add_lt_add_iff_left _).2 h1r, ?_⟩
    calc ywV 1 0 x + yrR o x ≤ ywV 1 0 x + 1 + yrR o x := by gcongr; exact le_self_add
      _ < gq (ywV 1 0 x + 1) x := (inE_indec hGE).add_lt (gmq_gt hx hx1 hDT hD1)
          (hrD.trans ((lt_add_one _).trans (gmq_gt hx hx1 hDT hD1)))
  cof := fun c x _ hc0 hc hx hx1 hg ν hν => by
    change ν < ywV 1 0 x + yrR (zbO c) x at hν
    have hoB := zbO_lt2 hc0.le hc
    obtain ⟨o, rfl⟩ := exists_add_of_le hc0.le
    change yrG (zbO (tfBG + 1 + o)) < x at hg
    rw [zbO_add] at hν hg hoB
    have hg0 : yrG (zbO (tfBG + 1)) < x := by rw [zbO_c0, yrG_zero]; exact hx.pos
    rcases le_or_gt ν (ywV 1 0 x) with hνD | hDν
    · refine ⟨tfBG + 1, le_rfl, hc0, hg0, ?_⟩
      show ν ≤ ywV 1 0 x + yrR (zbO (tfBG + 1)) x
      rw [zbO_c0, yrR_zero, add_zero]; exact hνD
    · obtain ⟨e, rfl⟩ := exists_add_of_le hDν.le
      have heo : e < yrR o x := (add_lt_add_iff_left _).1 hν
      obtain ⟨b, hbo, hgb, heb⟩ := yrR_cof hx hx1 o hoB hg e heo
      refine ⟨tfBG + 1 + b, le_self_add, (add_lt_add_iff_left _).2 hbo, ?_, ?_⟩
      · show yrG (zbO (tfBG + 1 + b)) < x
        rw [zbO_add]; exact hgb
      · show ywV 1 0 x + e ≤ ywV 1 0 x + yrR (zbO (tfBG + 1 + b)) x
        rw [zbO_add]; exact (add_le_add_iff_left _).2 heb
  ex := fun σ ρ c hB h1 h2 hg => by
    show ywV 1 0 ρ + yrR (zbO c) ρ ∈ TB ρ σ ∧ Googology.Trans.PoR.InaccPsi.R2.pi σ ρ (ywV 1 0 ρ + yrR (zbO c) ρ) =
      ywV 1 0 σ + yrR (zbO c) σ
    have h1σ : (1 : Ordinal.{0}) < σ := lu_one_lt_E hB.1
    have h0σ : (0 : Ordinal.{0}) < σ := hB.1.pos
    have hD := ywV_pi hB (mem_TB_of_lt hB h1σ) ((lu_one_lt_E hB.2.1).trans hB.2.2.2) (mem_TB_of_lt hB h0σ)
      (hB.2.1.pos.trans hB.2.2.2)
    rw [pi_lt hB h1σ, pi_lt hB h0σ] at hD
    obtain ⟨hr1, hr2⟩ := yr_pi hB (zbO c) (zbO_lt2 h1 h2) hg
    obtain ⟨h3, h4⟩ := pi_add hB hD.1 hr1
    exact ⟨h3, by rw [h4, hD.2, hr2]⟩
  cover := fun c Z hl hc0 hc hZ hZ1 _ d hd hdT => zgCover hZ hZ1 hl hc0 hc d hd hdT
  cl := fun c Z h1 h2 hZ hg => by
    have ho := zbO_lt2 h1 h2
    obtain ⟨o, rfl⟩ := exists_add_of_le h1
    change yrG (zbO (tfBG + 1 + o)) < Z at hg
    rw [zbO_add] at hg ho
    exact zgAtom hZ ho hg
  D_le := fun c x _ _ _ _ _ => show ywV 1 0 x ≤ ywV 1 0 x + yrR (zbO c) x from le_self_add
  BG_top := fun y hy hy1 => zbBG_top S hy hy1
  BG_poly := zbBG_poly S
  BG_c0 := le_self_add.trans gcG_strictMono.le_apply

/-- **A layer for a larger index is a layer for a smaller one** (the same top code). -/
theorem zbLayAt_mono {S : InaccSeq.{0}} {B B' : Ordinal.{0}} (h : B ≤ B') (hL : ZbLayAt S B') : ZbLayAt S B := by
  obtain ⟨L, T, hT, rest⟩ := hL
  exact ⟨L, T, (gcG_le h).trans hT, rest⟩

/-- **`ZbDirect S (B_Γ + B_Γ)`, UNCONDITIONAL**: a layer for every index `B_Γ ≤ B < B_Γ·2` (`B = B_Γ + 1 + o`: the
layer of `B_Γ + 1 + a_n`, `a_n` the tower `Yr.yrTw` above `o`, gate `0`). -/
theorem zgDirect2 (S : InaccSeq.{0}) : ZbDirect S (tfBG + tfBG) := by
  intro B hB1 hB2
  rcases hB1.lt_or_eq with hlt | heq
  · have h1 : tfBG + 1 ≤ B := Order.add_one_le_of_lt hlt
    have ho := zbO_lt2 h1 hB2
    obtain ⟨n, hn⟩ := yrTw_cof _ ho
    obtain ⟨o, rfl⟩ := exists_add_of_le h1
    rw [zbO_add] at hn
    have hB' : tfBG + 1 + yrTw n < tfBG + tfBG := by
      rw [add_assoc]
      exact (add_lt_add_iff_left _).2 (tfBG_SC.isPrincipal (gg_one_lt_of_SC tfBG_SC) (yrTw_lt_BG n))
    have hg : (zgB2 S).gt (tfBG + 1 + yrTw n) < Td.tdK S := by
      show yrG (zbO (tfBG + 1 + yrTw n)) < Td.tdK S
      rw [zbO_add, yrTw_g]; exact Td.tdK_SC.1
    exact zbLayAt_mono ((add_lt_add_iff_left _).2 hn).le ((zgB2 S).layAt S le_self_add hB' hg)
  · rw [← heq]; exact zbLayAt_BG S

/-- **UPPER ∧ LOWER ∧ CapV at every range restart below `ι(Γ_{Ω₁+1+B}·ω)`, every `B < B_Γ·2`** (UNCONDITIONAL). -/
theorem zgUV2 (S : InaccSeq.{0}) {B l : Ordinal.{0}} (hB : B < tfBG + tfBG) (hr : CdRange S l)
    (hl : l < iota S (gcG B * ω)) : CdUpper S l ∧ CdLower S l ∧ CdCapV S l :=
  zbUV_of_direct (zgDirect2 S) l hr B hB hl

end Googology.Trans.PoR.InaccPsi.R2.Zg
