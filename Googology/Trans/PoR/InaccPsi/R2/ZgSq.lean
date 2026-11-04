import Googology.Trans.PoR.InaccPsi.R2.ZgPi

/-!
# ZgSq: THE INDICES `B_Γ + 1 + (B_Γ·q + r)`, `q, r < B_Γ` — `ZbDirect S (B_Γ·B_Γ)`

The offsets `B_Γ·q + r` with `Yr` codes `q, r < B_Γ` (gate `max (yrG q) (yrG r)`) read
`D(x)·(1 + Yr.yrR q x) + Yr.yrR r x`.  Lemma EXACT: `D·y = ω^D·y` through `Yr.yr_dig` with the exponent lemma
`Zg.zgOpowD`; the inversion of the cover: `Zg.zgDig`; cofinality at `B_Γ·q` (`q` a limit) by
`Ordinal.lt_mul_iff_of_isSuccLimit` and `Yr.yrR_cof`, at `B_Γ·(q'+1)` by `Zg.zgCofD`.
`zgSq : Zb.ZbRS`, `zgDirectSq : ZbDirect S (B_Γ·B_Γ)` (UNCONDITIONAL).

No new axiom.  New definitions: `zgR3`, `zgG3`, `zgSq`.
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

theorem zgSQ_eq : tfBG * tfBG = ω ^ (tfBG + tfBG) := by
  rw [opow_add, Low.opow_eq_self_of_SC tfBG_SC]

theorem zgSQ_prin : IsPrincipal (· + ·) (tfBG * tfBG) := by
  rw [zgSQ_eq]; exact isPrincipal_add_omega0_opow _

theorem zgBG_lt_SQ : tfBG < tfBG * tfBG := by
  have := (mul_lt_mul_iff_right₀ (tfBG_SC.1)).2 (gg_one_lt_of_SC tfBG_SC)
  rwa [mul_one] at this

theorem zgSQ_lt_X : tfBG * tfBG < tlX := by
  rw [zgSQ_eq]
  have h1 : tfBG + tfBG < tlX := tlX_SC.isPrincipal tl_BG_lt_X tl_BG_lt_X
  have := tlX_SC.2 0 tlX_SC.1 _ h1
  rwa [veblen_zero_apply] at this

theorem zgDec3 {c : Ordinal.{0}} (h1 : tfBG + 1 ≤ c) (h2 : c < tfBG * tfBG) :
    ∃ q r, q < tfBG ∧ r < tfBG ∧ c = tfBG + 1 + (tfBG * q + r) := by
  obtain ⟨o, rfl⟩ := exists_add_of_le h1
  have ho : o < tfBG * tfBG := le_add_self.trans_lt h2
  refine ⟨o / tfBG, o % tfBG, (Ordinal.lt_mul_iff_div_lt zgBG_ne).1 ho, Ordinal.mod_lt o zgBG_ne, ?_⟩
  rw [Ordinal.div_add_mod]

theorem zgIdx3 {q r : Ordinal.{0}} (hq : q < tfBG) (hr : r < tfBG) : tfBG + 1 + (tfBG * q + r) < tfBG * tfBG := by
  have h1 : tfBG + 1 < tfBG * tfBG := zgSQ_prin zgBG_lt_SQ ((gg_one_lt_of_SC tfBG_SC).trans zgBG_lt_SQ)
  have h2 : tfBG * q + r < tfBG * tfBG := by
    calc tfBG * q + r < tfBG * q + tfBG := (add_lt_add_iff_left _).2 hr
      _ = tfBG * (q + 1) := (mul_add_one _ _).symm
      _ ≤ tfBG * tfBG := mul_le_mul_right (Order.add_one_le_of_lt hq) _
  exact zgSQ_prin h1 h2

theorem zgQM3 (q : Ordinal.{0}) {r : Ordinal.{0}} (hr : r < tfBG) :
    zgQ (tfBG + 1 + (tfBG * q + r)) = q ∧ zgM (tfBG + 1 + (tfBG * q + r)) = r := by
  unfold zgQ zgM; rw [zbO_add]; exact zgQM' _ hr

theorem zgLex3 {q₁ q₂ r₁ r₂ : Ordinal.{0}} (hr₂ : r₂ < tfBG)
    (h : tfBG * q₁ + r₁ < tfBG * q₂ + r₂) : q₁ < q₂ ∨ (q₁ = q₂ ∧ r₁ < r₂) := by
  rcases lt_trichotomy q₁ q₂ with hl | he | hg
  · exact Or.inl hl
  · subst he; exact Or.inr ⟨rfl, (add_lt_add_iff_left _).1 h⟩
  · exfalso
    have : tfBG * q₂ + r₂ < tfBG * q₁ + r₁ := by
      calc tfBG * q₂ + r₂ < tfBG * q₂ + tfBG := (add_lt_add_iff_left _).2 hr₂
        _ = tfBG * (q₂ + 1) := (mul_add_one _ _).symm
        _ ≤ tfBG * q₁ := mul_le_mul_right (Order.add_one_le_of_lt hg) _
        _ ≤ tfBG * q₁ + r₁ := le_self_add
    exact absurd h (not_lt.2 this.le)

/-- No fixed point of `Γ` among the indices below `B_Γ·B_Γ` past `B_Γ`. -/
theorem zg_nonfix3 {o : Ordinal.{0}} (ho : o < tfBG * tfBG) :
    Om1 + 1 + (tfBG + 1 + o) < gamma (Om1 + 1 + (tfBG + 1 + o)) := by
  set ν := Om1 + 1 + (tfBG + 1 + o) with hν
  have hE : ω ^ tfBG = tfBG := Low.opow_eq_self_of_SC tfBG_SC
  have h1 : Om1 + 1 + tfBG = tfBG :=
    Ordinal.add_of_omega0_opow_le (c := tfBG) (by rw [hE]; exact tl_Om1_succ_lt_BG) (by rw [hE])
  have hνe : ν = tfBG + (1 + o) := by rw [hν, ← add_assoc, ← add_assoc, h1, add_assoc]
  have hB : tfBG < ν := by
    rw [hνe]; exact lt_add_of_pos_right _ (lt_of_lt_of_le zero_lt_one le_self_add)
  have hBS : ν < tfBG * tfBG := by
    rw [hνe]
    exact zgSQ_prin zgBG_lt_SQ (zgSQ_prin ((gg_one_lt_of_SC tfBG_SC).trans zgBG_lt_SQ) ho)
  rcases (isNormal_gamma.strictMono.le_apply (x := ν)).lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  have hνE : ω ^ ν = ν := by rw [heq]; exact Low.opow_eq_self_of_SC (Lq.lq_gamma_SC ν)
  have h2 : ν < tfBG + tfBG := by
    have := hBS; rw [zgSQ_eq, ← hνE] at this
    exact (opow_lt_opow_iff_right one_lt_omega0).1 this
  have h3 : ν < tfBG * ω := h2.trans (zgW_prin zgBG_lt_W zgBG_lt_W)
  rw [zgW_eq, ← hνE] at h3
  have h4 := (opow_lt_opow_iff_right one_lt_omega0).1 h3
  exact absurd (Order.add_one_le_of_lt hB) (not_le.2 h4)

theorem zgInv3 {Z o : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om1) (ho : o < tfBG * tfBG)
    (h : TlCl Z (gcG (tfBG + 1 + o))) : TlCl Z o := by
  rw [tf_gcG] at h
  have hlt := zg_nonfix3 ho
  have hO : Om1 < gamma (Om1 + 1 + (tfBG + 1 + o)) := by
    rw [← tf_gcG, Br.Om1_eq]; exact gcG_Om1_lt _
  obtain ⟨-, hI⟩ := tl_cl_atom hZ1 _ h (Lq.lq_gamma_SC _) hO
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

/-- **The gated cover** below `Γ_{Ω₁+1+c}` for a limit index `c ∈ (B_Γ+1, B_Γ·B_Γ)`. -/
theorem zgCover3 {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1) {c : Ordinal.{0}} (hl : IsSuccLimit c)
    (hc0 : tfBG + 1 < c) (hc : c < tfBG * tfBG) :
    ∀ d, GxCl Z (zbU.At Z) d → d < gcG c →
      ∃ b, tfBG + 1 ≤ b ∧ b < c ∧ max (yrG (zgQ b)) (yrG (zgM b)) < Z ∧ d < gcG b := by
  have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1.le
  have hg0 : max (yrG (zgQ (tfBG + 1))) (yrG (zgM (tfBG + 1))) < Z := by
    rw [zgQ_c0, zgM_c0, yrG_zero, max_self]; exact hZ.1
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
    obtain ⟨q, r, hq, hr, rfl⟩ := zgDec3 hb (hbc.trans hc)
    rcases hs with hs | ⟨c', hc', -, e⟩
    · have hT := zgInv3 hZ hZ1' (le_add_self.trans_lt (hbc.trans hc)) hs.2.2.2
      obtain ⟨-, -, hgq, hgr⟩ := zgDig hZ hZ1' hq hr hT
      have hr1 : r + 1 < tfBG := zgBG_lim.add_one_lt hr
      refine ⟨tfBG + 1 + (tfBG * q + (r + 1)), le_self_add, ?_, ?_, ?_⟩
      · rw [← add_assoc (tfBG * _) r 1, ← add_assoc (tfBG + 1) _ 1]; exact hl.add_one_lt hbc
      · rw [(zgQM3 q hr1).1, (zgQM3 q hr1).2]
        exact max_lt hgq (yrG_succ (ev_isSuccLimit_of_inE (gg_SC_eps hZ)) r hgr)
      · rw [← add_assoc (tfBG * _) r 1, ← add_assoc (tfBG + 1) _ 1]; exact gcG_lt (lt_add_one _)
    · exfalso
      have h1 : c' < tfBG + 1 + (tfBG * q + r) := hc'.trans ((lt_add_one _).trans_le le_self_add)
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

/-- **The reading** `D(x)·(1 + yrR q x) + yrR r x` of the index `B_Γ + 1 + (B_Γ·q + r)`. -/
noncomputable def zgR3 (c x : Ordinal.{0}) : Ordinal.{0} := ywV 1 0 x * (1 + yrR (zgQ c) x) + yrR (zgM c) x

/-- **The gate** `max (yrG q) (yrG r)`. -/
noncomputable def zgG3 (c : Ordinal.{0}) : Ordinal.{0} := max (yrG (zgQ c)) (yrG (zgM c))

theorem zgR3_eq (q : Ordinal.{0}) {r : Ordinal.{0}} (hr : r < tfBG) (x : Ordinal.{0}) :
    zgR3 (tfBG + 1 + (tfBG * q + r)) x = ywV 1 0 x * (1 + yrR q x) + yrR r x := by
  unfold zgR3; rw [(zgQM3 q hr).1, (zgQM3 q hr).2]

theorem zgG3_eq (q : Ordinal.{0}) {r : Ordinal.{0}} (hr : r < tfBG) :
    zgG3 (tfBG + 1 + (tfBG * q + r)) = max (yrG q) (yrG r) := by
  unfold zgG3; rw [(zgQM3 q hr).1, (zgQM3 q hr).2]

theorem zgV3_lt {D y₁ y₂ z₁ z₂ : Ordinal.{0}} (hy : y₁ < y₂) (hz : z₁ < D) :
    D * (1 + y₁) + z₁ < D * (1 + y₂) + z₂ := by
  calc D * (1 + y₁) + z₁ < D * (1 + y₁) + D := (add_lt_add_iff_left _).2 hz
    _ = D * (1 + y₁ + 1) := (mul_add_one _ _).symm
    _ ≤ D * (1 + y₂) := mul_le_mul_right (by rw [add_assoc]; exact add_le_add le_rfl (Order.add_one_le_of_lt hy)) _
    _ ≤ _ := le_self_add

section Rd3

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem zgV3 {q r : Ordinal.{0}} (hq : q < tfBG) (hr : r < tfBG) (hgq : yrG q < x) (hgr : yrG r < x) :
    yrR q x < ywV 1 0 x ∧ yrR r x < ywV 1 0 x ∧
    ywV 1 0 x * (1 + yrR q x) + yrR r x < ywX x ∧ ywV 1 0 x * (1 + yrR q x) + yrR r x ∈ Tset x ∧
    ywV 1 0 x * (1 + yrR q x) + yrR r x < gq (ywV 1 0 x + 1) x := by
  have hy := zgN_lt_D hx hx1 (yrR_N hx hx1 hq hgq)
  have hz := zgN_lt_D hx hx1 (yrR_N hx hx1 hr hgr)
  obtain ⟨hXT, hxX, hX1, hXE⟩ := ywX_facts hx hx1
  have hDX := ywD_lt_X hx hx1
  have h1X : (1 : Ordinal.{0}) < ywX x := (lu_one_lt_E hx).trans hxX
  have hV : ywV 1 0 x * (1 + yrR q x) + yrR r x < ywX x :=
    (inE_indec hXE).add_lt (mul_lt_inE hXE hDX ((inE_indec hXE).add_lt h1X (hy.trans hDX))) (hz.trans hDX)
  obtain ⟨hDT, hD1, -⟩ := zbDo_T hx hx1 (o := 1) (one_lt_omega0.trans_le (omega0_le_of_isSuccLimit gc_eps0_lim))
  obtain ⟨-, -, -, hGE, -⟩ := geq_facts hx hx1 hDT hD1
  have hDG : ywV 1 0 x < gq (ywV 1 0 x + 1) x := (lt_add_one _).trans (gmq_gt hx hx1 hDT hD1)
  have h1G : (1 : Ordinal.{0}) < gq (ywV 1 0 x + 1) x := (lu_one_lt_E hx).trans ((ywD_closed hx hx1).1.trans hDG)
  exact ⟨hy, hz, hV, vz_T_down hx hx1 hXT hX1 hV.le,
    (inE_indec hGE).add_lt (mul_lt_inE hGE hDG ((inE_indec hGE).add_lt h1G (hy.trans hDG))) (hz.trans hDG)⟩

end Rd3

/-- **THE READING SYSTEM OF THE INDICES `B_Γ + 1 + (B_Γ·q + r)`, `q, r < B_Γ`** (gate `max (yrG q) (yrG r)`). -/
noncomputable def zgSq (S : InaccSeq.{0}) : ZbRS where
  c0 := tfBG + 1
  Bd := tfBG * tfBG
  gt := zgG3
  R := zgR3
  L0 := (zbBGn 0).1
  c0_ne := (lt_of_le_of_lt zero_le (lt_add_one tfBG)).ne'
  c0_lt := zgSQ_prin zgBG_lt_SQ ((gg_one_lt_of_SC tfBG_SC).trans zgBG_lt_SQ)
  Bd_X := zgSQ_lt_X.le
  gt_c0 := by unfold zgG3; rw [zgQ_c0, zgM_c0, yrG_zero, max_self]
  L0_g := zbBGn_g 0
  L0_E := fun x _ _ => by
    rw [zbBGn_E 0 x]
    show gq (ywV 1 0 x + ((0 : ℕ) : Ordinal.{0})) x = gq (zgR3 (tfBG + 1) x) x
    unfold zgR3; rw [zgQ_c0, zgM_c0, yrR_zero, Nat.cast_zero, add_zero, add_zero, add_zero, mul_one]
  L0_top := fun y hy hy1 => by
    have h := (zbBGn_codes S 0).1 y hy hy1 (by rw [zbBGn_g]; exact hy.1)
    rw [h]; unfold zbT; norm_num
  L0_poly := by
    have h := (zbBGn_codes S 0).2
    unfold zbT at h; norm_num at h
    exact h
  RT := fun c x hx hx1 h1 h2 hg => by
    obtain ⟨q, r, hq, hr, rfl⟩ := zgDec3 h1 h2
    rw [zgG3_eq q hr] at hg
    rw [zgR3_eq q hr]
    obtain ⟨-, -, hX, hT, -⟩ := zgV3 hx hx1 hq hr (le_max_left _ _ |>.trans_lt hg) (le_max_right _ _ |>.trans_lt hg)
    obtain ⟨-, -, hX1, -⟩ := ywX_facts hx hx1
    refine ⟨hT, hX.trans hX1, ?_⟩
    rw [← ywV_zero]
    exact ywV_lt_X hx hx1 (mem_T_of_le hx hx1 zero_le) (hx.pos.trans hx1) hT (hX.trans hX1)
      (hx.pos.trans (ywX_facts hx hx1).2.1) hX
  mono := fun b c x hx hx1 h1 hbc hc hgb hgc => by
    obtain ⟨q₂, r₂, hq₂, hr₂, rfl⟩ := zgDec3 (h1.trans hbc.le) hc
    obtain ⟨q₁, r₁, hq₁, hr₁, rfl⟩ := zgDec3 h1 (hbc.trans hc)
    change zgG3 _ < x at hgb hgc
    rw [zgG3_eq q₁ hr₁] at hgb; rw [zgG3_eq q₂ hr₂] at hgc
    show zgR3 _ x < zgR3 _ x
    rw [zgR3_eq q₁ hr₁, zgR3_eq q₂ hr₂]
    have hz₁ := (zgV3 hx hx1 hq₁ hr₁ (le_max_left _ _ |>.trans_lt hgb) (le_max_right _ _ |>.trans_lt hgb)).2.1
    rcases zgLex3 hr₂ ((add_lt_add_iff_left _).1 hbc) with hqq | ⟨rfl, hrr⟩
    · exact zgV3_lt (yrR_mono hx hx1 hq₂ hqq (le_max_left _ _ |>.trans_lt hgc)
        (le_max_left _ _ |>.trans_lt hgb)) hz₁
    · exact (add_lt_add_iff_left _).2 (yrR_mono hx hx1 hr₂ hrr (le_max_right _ _ |>.trans_lt hgc)
        (le_max_right _ _ |>.trans_lt hgb))
  succ := fun b x hb => by
    show zgR3 (b + 1) x = zgR3 b x + 1
    obtain ⟨o, rfl⟩ := exists_add_of_le hb
    unfold zgR3 zgQ zgM
    rw [add_assoc (tfBG + 1) o 1, zbO_add, zbO_add]
    conv_lhs => rw [← Ordinal.div_add_mod o tfBG]
    conv_rhs => rw [← Ordinal.div_add_mod o tfBG]
    have hr1 : o % tfBG + 1 < tfBG := zgBG_lim.add_one_lt (Ordinal.mod_lt o zgBG_ne)
    rw [add_assoc, (zgQM' _ hr1).1, (zgQM' _ hr1).2, (zgQM' _ (Ordinal.mod_lt o zgBG_ne)).1,
      (zgQM' _ (Ordinal.mod_lt o zgBG_ne)).2, yrR_succ, add_assoc]
  gt_le_succ := fun b => by
    show zgG3 b ≤ zgG3 (b + 1)
    rcases lt_or_ge b (tfBG + 1) with hb | hb
    · unfold zgG3 zgQ zgM
      rw [show zbO b = 0 from Ordinal.sub_eq_zero_iff_le.2 hb.le, Ordinal.zero_mod, Ordinal.zero_div, yrG_zero,
        max_self]; exact zero_le
    · obtain ⟨o, rfl⟩ := exists_add_of_le hb
      unfold zgG3 zgQ zgM
      rw [add_assoc (tfBG + 1) o 1, zbO_add, zbO_add]
      conv_lhs => rw [← Ordinal.div_add_mod o tfBG]
      conv_rhs => rw [← Ordinal.div_add_mod o tfBG]
      have hr1 : o % tfBG + 1 < tfBG := zgBG_lim.add_one_lt (Ordinal.mod_lt o zgBG_ne)
      rw [add_assoc, (zgQM' _ hr1).1, (zgQM' _ hr1).2, (zgQM' _ (Ordinal.mod_lt o zgBG_ne)).1,
        (zgQM' _ (Ordinal.mod_lt o zgBG_ne)).2]
      exact max_le_max le_rfl (yrG_le_succ _)
  lim_R := fun c x hl hc0 hc hx hx1 hg => by
    obtain ⟨q, r, hq, hr, rfl⟩ := zgDec3 hc0.le hc
    change zgG3 _ < x at hg
    rw [zgG3_eq q hr] at hg
    have hgq := le_max_left _ _ |>.trans_lt hg
    have hgr := le_max_right _ _ |>.trans_lt hg
    show IsSuccLimit (zgR3 _ x) ∧ ∃ σ, σ < zgR3 _ x ∧ zgR3 _ x < gq σ x
    rw [zgR3_eq q hr]
    obtain ⟨hy, hz, -, -, hG⟩ := zgV3 hx hx1 hq hr hgq hgr
    obtain ⟨-, -, hDE⟩ := zgD_T hx hx1
    have hDl := ev_isSuccLimit_of_inE hDE
    have hDm : ywV 1 0 x ≤ ywV 1 0 x * (1 + yrR q x) := by
      have := mul_le_mul_right (show (1 : Ordinal.{0}) ≤ 1 + yrR q x from le_self_add) (ywV 1 0 x)
      rwa [mul_one] at this
    have hml : IsSuccLimit (ywV 1 0 x * (1 + yrR q x)) :=
      isSuccLimit_mul_left hDl (lt_of_lt_of_le zero_lt_one le_self_add)
    rcases eq_or_ne r 0 with rfl | hr0
    · have hq0 : q ≠ 0 := by rintro rfl; simp at hc0
      have hy0 := yrR_pos hx hx1 hq0 hq hgq
      rw [yrR_zero, add_zero]
      refine ⟨hml, ywV 1 0 x + 1, ?_, by rw [yrR_zero, add_zero] at hG; exact hG⟩
      calc ywV 1 0 x + 1 < ywV 1 0 x + ywV 1 0 x := (add_lt_add_iff_left _).2 (by simpa using hDl.add_one_lt hDl.bot_lt)
        _ = ywV 1 0 x * (1 + 1) := by rw [mul_add, mul_one]
        _ ≤ ywV 1 0 x * (1 + yrR q x) := mul_le_mul_right (add_le_add le_rfl (one_le_iff_pos.2 hy0)) _
    · have hrl : IsSuccLimit r := by
        rcases zero_or_succ_or_isSuccLimit r with h | ⟨s, hs⟩ | h
        · exact absurd h hr0
        · exfalso
          have h' : IsSuccLimit (Order.succ (tfBG + 1 + (tfBG * q + s))) := by
            rw [succ_eq_add_one, add_assoc (tfBG + 1), add_assoc (tfBG * q), ← succ_eq_add_one s, hs]; exact hl
          exact Order.not_isSuccLimit_succ _ h'
        · exact h
      have hRl : IsSuccLimit (yrR r x) := yr_lim_of_cof hx hx1 hrl hr hgr (yrR_cof hx hx1 r hr)
      have h1r : (1 : Ordinal.{0}) < yrR r x := by simpa using hRl.add_one_lt hRl.bot_lt
      refine ⟨isSuccLimit_add _ hRl, ywV 1 0 x + 1, ?_, hG⟩
      calc ywV 1 0 x + 1 < ywV 1 0 x + yrR r x := (add_lt_add_iff_left _).2 h1r
        _ ≤ _ := add_le_add hDm le_rfl
  cof := fun c x _ hc0 hc hx hx1 hg ν hν => by
    obtain ⟨q, r, hq, hr, rfl⟩ := zgDec3 hc0.le hc
    change zgG3 _ < x at hg
    rw [zgG3_eq q hr] at hg
    have hgq := le_max_left _ _ |>.trans_lt hg
    have hgr := le_max_right _ _ |>.trans_lt hg
    change ν < zgR3 _ x at hν
    rw [zgR3_eq q hr] at hν
    have h0B : (0 : Ordinal.{0}) < tfBG := tfBG_SC.1
    have hidx : ∀ q' r', r' < tfBG → tfBG + 1 ≤ tfBG + 1 + (tfBG * q' + r') := fun _ _ _ => le_self_add
    show ∃ b, tfBG + 1 ≤ b ∧ b < tfBG + 1 + (tfBG * q + r) ∧ zgG3 b < x ∧ ν ≤ zgR3 b x
    rcases eq_or_ne r 0 with rfl | hr0
    · rw [yrR_zero, add_zero] at hν
      have hq0 : q ≠ 0 := by rintro rfl; simp at hc0
      rcases zero_or_succ_or_isSuccLimit q with h | ⟨q', hq'⟩ | hql
      · exact absurd h hq0
      · rw [succ_eq_add_one] at hq'
        subst hq'
        have hq'B : q' < tfBG := (lt_add_one q').trans hq
        have hgq' : yrG q' < x := (yrG_le_succ q').trans_lt hgq
        rw [yrR_succ, ← add_assoc, mul_add_one] at hν
        have hlt0 : tfBG + 1 + (tfBG * q' + 0) < tfBG + 1 + (tfBG * (q' + 1) + 0) := by
          rw [add_zero, add_zero, mul_add_one]
          exact (add_lt_add_iff_left _).2 (lt_add_of_pos_right _ h0B)
        rcases le_or_gt ν (ywV 1 0 x * (1 + yrR q' x)) with hνD | hDν
        · refine ⟨_, hidx q' 0 h0B, hlt0, ?_, ?_⟩
          · rw [zgG3_eq q' h0B, yrG_zero, max_lt_iff]; exact ⟨hgq', hx.pos⟩
          · rw [zgR3_eq q' h0B, yrR_zero, add_zero]; exact hνD
        · obtain ⟨e, rfl⟩ := exists_add_of_le hDν.le
          have he : e < ywV 1 0 x := (add_lt_add_iff_left _).1 hν
          obtain ⟨k, hk⟩ := zgCofD hx hx1 he
          have hkB := yrTw_lt_BG k
          refine ⟨_, hidx q' _ hkB, ?_, ?_, ?_⟩
          · calc tfBG + 1 + (tfBG * q' + yrTw k) < tfBG + 1 + (tfBG * q' + tfBG) :=
                  (add_lt_add_iff_left _).2 ((add_lt_add_iff_left _).2 hkB)
              _ = _ := by rw [add_zero, mul_add_one]
          · rw [zgG3_eq q' hkB, yrTw_g, max_lt_iff]; exact ⟨hgq', hx.pos⟩
          · rw [zgR3_eq q' hkB]; exact (add_le_add_iff_left _).2 hk
      · have hyl : IsSuccLimit (yrR q x) := yr_lim_of_cof hx hx1 hql hq hgq (yrR_cof hx hx1 q hq)
        rw [one_add_of_omega0_le (omega0_le_of_isSuccLimit hyl)] at hν
        obtain ⟨c', hc', hνc⟩ := (lt_mul_iff_of_isSuccLimit hyl).1 hν
        obtain ⟨b', hb', hgb', hcb'⟩ := yrR_cof hx hx1 q hq hgq c' hc'
        have hb'B : b' < tfBG := hb'.trans hq
        refine ⟨_, hidx b' 0 h0B, ?_, ?_, ?_⟩
        · rw [add_zero, add_zero]
          exact (add_lt_add_iff_left _).2 ((mul_lt_mul_iff_right₀ h0B).2 hb')
        · rw [zgG3_eq b' h0B, yrG_zero, max_lt_iff]; exact ⟨hgb', hx.pos⟩
        · rw [zgR3_eq b' h0B, yrR_zero, add_zero]
          exact hνc.le.trans (mul_le_mul_right (hcb'.trans le_add_self) _)
    · have hlt : tfBG + 1 + (tfBG * q + 0) < tfBG + 1 + (tfBG * q + r) :=
        (add_lt_add_iff_left _).2 ((add_lt_add_iff_left _).2 (pos_iff_ne_zero.2 hr0))
      rcases le_or_gt ν (ywV 1 0 x * (1 + yrR q x)) with hνD | hDν
      · refine ⟨_, hidx q 0 h0B, hlt, ?_, ?_⟩
        · rw [zgG3_eq q h0B, yrG_zero, max_lt_iff]; exact ⟨hgq, hx.pos⟩
        · rw [zgR3_eq q h0B, yrR_zero, add_zero]; exact hνD
      · obtain ⟨e, rfl⟩ := exists_add_of_le hDν.le
        have he : e < yrR r x := (add_lt_add_iff_left _).1 hν
        obtain ⟨b', hb', hgb', heb'⟩ := yrR_cof hx hx1 r hr hgr e he
        have hb'B : b' < tfBG := hb'.trans hr
        refine ⟨_, hidx q b' hb'B, (add_lt_add_iff_left _).2 ((add_lt_add_iff_left _).2 hb'), ?_, ?_⟩
        · rw [zgG3_eq q hb'B, max_lt_iff]; exact ⟨hgq, hgb'⟩
        · rw [zgR3_eq q hb'B]; exact (add_le_add_iff_left _).2 heb'
  ex := fun σ ρ c hB h1 h2 hg => by
    obtain ⟨q, r, hq, hr, rfl⟩ := zgDec3 h1 h2
    change zgG3 _ < σ at hg
    rw [zgG3_eq q hr] at hg
    have hgq := le_max_left _ _ |>.trans_lt hg
    have hgr := le_max_right _ _ |>.trans_lt hg
    show zgR3 _ ρ ∈ TB ρ σ ∧ Googology.Trans.PoR.InaccPsi.R2.pi σ ρ (zgR3 _ ρ) = zgR3 _ σ
    rw [zgR3_eq q hr, zgR3_eq q hr]
    have h1σ : (1 : Ordinal.{0}) < σ := lu_one_lt_E hB.1
    have h0σ : (0 : Ordinal.{0}) < σ := hB.1.pos
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hD := ywV_pi hB (mem_TB_of_lt hB h1σ) ((lu_one_lt_E hB.2.1).trans hρ1) (mem_TB_of_lt hB h0σ)
      (hB.2.1.pos.trans hρ1)
    rw [pi_lt hB h1σ, pi_lt hB h0σ] at hD
    obtain ⟨m, hm⟩ := yrTw_cof _ hq
    have hmB := yrTw_lt_BG m
    have hgm : yrG (yrTw m) < σ := by rw [yrTw_g]; exact h0σ
    have heρ := yr_pi hB (yrTw m) hmB hgm
    have hDρ : yrR (yrTw m) ρ < ywV 1 0 ρ :=
      zgN_lt_D hB.2.1 hρ1 (yrR_N hB.2.1 hρ1 hmB (hgm.trans hB.2.2.1))
    have hDσ : yrR (yrTw m) σ < ywV 1 0 σ := zgN_lt_D hB.1 hσ1 (yrR_N hB.1 hσ1 hmB hgm)
    have hP : ∀ β, β ∈ TB ρ σ → β < yrR (yrTw m) ρ →
        ω ^ (ywV 1 0 ρ + β) ∈ TB ρ σ ∧ Googology.Trans.PoR.InaccPsi.R2.pi σ ρ (ω ^ (ywV 1 0 ρ + β)) =
          ω ^ (ywV 1 0 σ + Googology.Trans.PoR.InaccPsi.R2.pi σ ρ β) := fun β hβT hβ => by
      have hπ : Googology.Trans.PoR.InaccPsi.R2.pi σ ρ β < yrR (yrTw m) σ := by
        rw [← heρ.2]; exact (pi_bijOn hB).2 hβT heρ.1 hβ
      exact zgOpowD hB hβT (hβ.trans hDρ) (hπ.trans hDσ)
    have hmul := yr_dig hB (yrTw_E m) (yrTw_ge m) hmB hgm
      (fun j hj hgj => yr_pi hB j (hj.trans hmB) hgj) q hm hgq _ _ hP
    rw [(zgD_T hB.2.1 hρ1).2.2, (zgD_T hB.1 hσ1).2.2] at hmul
    obtain ⟨hr1, hr2⟩ := yr_pi hB r hr hgr
    have e : ∀ t : Ordinal.{0}, ywV 1 0 t * (1 + yrR q t) + yrR r t =
        ywV 1 0 t + ywV 1 0 t * yrR q t + yrR r t := fun t => by rw [mul_add, mul_one]
    rw [e ρ, e σ]
    obtain ⟨h3, h4⟩ := pi_add hB hD.1 hmul.1
    obtain ⟨h5, h6⟩ := pi_add hB h3 hr1
    exact ⟨h5, by rw [h6, h4, hD.2, hmul.2, hr2]⟩
  cover := fun c Z hl hc0 hc hZ hZ1 _ d hd hdT => zgCover3 hZ hZ1 hl hc0 hc d hd hdT
  cl := fun c Z h1 h2 hZ hg => by
    obtain ⟨q, r, hq, hr, rfl⟩ := zgDec3 h1 h2
    change zgG3 _ < Z at hg
    rw [zgG3_eq q hr] at hg
    refine GxCl.atom (Or.inl ⟨gcG_SC _, gcG_Om1_lt _, ZbRS.gcG_lt_X (h2.trans zgSQ_lt_X), ?_⟩)
    have hBq : TlCl Z (tfBG * q) := by
      have := tl_cl_opow_mul hZ (zbBG_tl hZ.1) q (zgYr hZ.1 q hq (le_max_left _ _ |>.trans_lt hg)).1
      rwa [Low.opow_eq_self_of_SC tfBG_SC] at this
    have harg : TlCl Z (Om1 + 1 + (tfBG + 1 + (tfBG * q + r))) :=
      TlCl.add (TlCl.add TlCl.om (TlCl.one hZ.1))
        (TlCl.add (TlCl.add (zbBG_tl hZ.1) (TlCl.one hZ.1))
          (TlCl.add hBq (zgYr hZ.1 r hr (le_max_right _ _ |>.trans_lt hg)).1))
    rw [tf_gcG]
    exact TlCl.gam hZ.1 harg ((lt_add_one _).trans_le le_self_add)

/-- **`ZbDirect S (B_Γ·B_Γ)`, UNCONDITIONAL**: a layer for every index `B_Γ ≤ B < B_Γ·B_Γ` (`B = B_Γ + 1 +
(B_Γ·q + r)`: the layer of `B_Γ + 1 + B_Γ·a_m`, `a_m > q` the tower `Yr.yrTw`, gate `0`). -/
theorem zgDirectSq (S : InaccSeq.{0}) : ZbDirect S (tfBG * tfBG) := by
  intro B hB1 hB2
  rcases hB1.lt_or_eq with hlt | heq
  · obtain ⟨q, r, hq, hr, rfl⟩ := zgDec3 (Order.add_one_le_of_lt hlt) hB2
    obtain ⟨m, hm⟩ := yrTw_cof _ hq
    have hmB := yrTw_lt_BG m
    have h0B : (0 : Ordinal.{0}) < tfBG := tfBG_SC.1
    have hg : (zgSq S).gt (tfBG + 1 + (tfBG * yrTw m + 0)) < Td.tdK S := by
      show zgG3 _ < Td.tdK S
      rw [zgG3_eq _ h0B, yrTw_g, yrG_zero, max_self]; exact Td.tdK_SC.1
    have hle : tfBG + 1 + (tfBG * q + r) ≤ tfBG + 1 + (tfBG * yrTw m + 0) := by
      refine (add_le_add_iff_left _).2 ?_
      calc tfBG * q + r ≤ tfBG * q + tfBG := (add_le_add_iff_left _).2 hr.le
        _ = tfBG * (q + 1) := (mul_add_one _ _).symm
        _ ≤ tfBG * yrTw m := mul_le_mul_right (Order.add_one_le_of_lt hm) _
        _ = _ := (add_zero _).symm
    exact zbLayAt_mono hle ((zgSq S).layAt S le_self_add (zgIdx3 hmB h0B) hg)
  · rw [← heq]; exact zbLayAt_BG S

/-- **UPPER ∧ LOWER ∧ CapV at every range restart below `ι(Γ_{Ω₁+1+B}·ω)`, every `B < B_Γ·B_Γ`**
(UNCONDITIONAL). -/
theorem zgUVSq (S : InaccSeq.{0}) {B l : Ordinal.{0}} (hB : B < tfBG * tfBG) (hr : CdRange S l)
    (hl : l < iota S (gcG B * ω)) : CdUpper S l ∧ CdLower S l ∧ CdCapV S l :=
  zbUV_of_direct (zgDirectSq S) l hr B hB hl

end Googology.Trans.PoR.InaccPsi.R2.Zg
