import Googology.Trans.PoR.InaccPsi.R2.ZgB2

/-!
# ZgBw: THE INDICES `B_Γ + 1 + (B_Γ·n + r)`, `n < ω`, `r < B_Γ` — `ZbDirect S (B_Γ·ω)`

The offsets with the atom `B_Γ` up to `B_Γ·ω`: the index `B_Γ + 1 + (B_Γ·n + r)` (`r < B_Γ` a `Yr` code) reads
`ϑˣ(Ω₁·Ω₁ + D(x)·(1+n) + Yr.yrR r x)`, gate `Yr.yrG r`.  At the limit indices `B_Γ·(n+1)` the cofinality uses the
tower `Yr.yrTw`: its readings are cofinal in `D(x)` (`zgCofD`, from the minimality of `D(x)` among the closed
points, `Zb.zbKind1`).  `zgBw : Zb.ZbRS`, `zgDirectW : ZbDirect S (B_Γ·ω)` (UNCONDITIONAL).

* `zgCofD`, `zg_nonfixW`, `zgInvW`, `zgDec`, `zgQM`, `zgCoverW`;
* `zgBw` (**THE READING SYSTEM**), `zgDirectW` (**`ZbDirect S (B_Γ·ω)`**), `zgUVW`.

No new axiom.  New definitions: `zgQ`, `zgM`, `zgRw`, `zgBw`.
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

section CofD

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **The readings of the tower `Yr.yrTw` are cofinal in `D(x)`.** -/
theorem zgCofD {e : Ordinal.{0}} (he : e < ywV 1 0 x) : ∃ n, e ≤ yrR (yrTw n) x := by
  by_contra hc
  push Not at hc
  set t : ℕ → Ordinal.{0} := fun n => yrR (yrTw n) x with ht
  have hbdd : BddAbove (Set.range t) := ⟨e, by rintro _ ⟨n, rfl⟩; exact (hc n).le⟩
  have hN : ∀ n, YrN x (t n) := fun n => yrR_N hx hx1 (yrTw_lt_BG n) (by rw [yrTw_g]; exact hx.pos)
  have hsucc : ∀ n, t (n + 1) = gq (t n) x := fun n => by
    show yrR (gcG (yrTw n)) x = gq (yrR (yrTw n) x) x
    exact yrR_atom (yr_idx_BG (yrTw_lt_BG n)) x
  have hxs : x < iSup t := by
    have h0 : t 0 = gq 0 x := yrR_G0 x
    exact ((Gf.gfq0_facts hx hx1).2.1.trans_le (h0 ▸ le_rfl)).trans_le (le_ciSup hbdd 0)
  have hcl : YwClosed x (iSup t) := by
    intro σ _ hσ
    obtain ⟨n, hn⟩ := (lt_ciSup_iff hbdd).1 hσ
    calc gq σ x < gq (t n) x := yr_lt hx hx1 (hN n) hn
      _ = t (n + 1) := (hsucc n).symm
      _ ≤ iSup t := le_ciSup hbdd (n + 1)
  have hD := (zbKind1 hx hx1).2.2.1 _ hxs ((ywC_one_iff hx hx1).2 hcl)
  have hse : iSup t ≤ e := ciSup_le fun n => (hc n).le
  exact absurd (hD.trans hse) (not_le.2 he)

theorem zgD_T : ywV 1 0 x ∈ Tset x ∧ ywV 1 0 x < Om1 ∧ InE (ywV 1 0 x) := by
  obtain ⟨h1T, h1Ω⟩ := yw_one hx hx1
  obtain ⟨hT, -, h1, hE, -⟩ := ywV_facts hx hx1 h1T h1Ω (mem_T_of_le hx hx1 zero_le) (hx.pos.trans hx1)
  exact ⟨hT, h1, hE⟩

theorem zgDn_T (n : ℕ) : ywV 1 0 x * (n : Ordinal.{0}) ∈ Tset x ∧ ywV 1 0 x * (n : Ordinal.{0}) < ywX x := by
  obtain ⟨hDT, -, -⟩ := zgD_T hx hx1
  obtain ⟨-, -, -, hXE⟩ := ywX_facts hx hx1
  induction n with
  | zero => simp only [Nat.cast_zero, mul_zero]; exact ⟨mem_T_of_le hx hx1 zero_le, (ywX_facts hx hx1).2.1.trans_le' zero_le⟩
  | succ n ih =>
    rw [Nat.cast_succ, mul_add_one]
    exact ⟨vzT_add hx hx1 ih.1 hDT, (inE_indec hXE).add_lt ih.2 (ywD_lt_X hx hx1)⟩

omit hx hx1 in
theorem zgDn_lt {G : Ordinal.{0}} (hGE : InE G) (hDG : ywV 1 0 x < G) (n : ℕ) : ywV 1 0 x * (n : Ordinal.{0}) < G := by
  induction n with
  | zero => simp only [Nat.cast_zero, mul_zero]; exact hGE.pos
  | succ n ih => rw [Nat.cast_succ, mul_add_one]; exact (inE_indec hGE).add_lt ih hDG

end CofD

/-- **No fixed point of `Γ` among the indices `B_Γ + 1 + o`, `o < B_Γ·ω`.** -/
theorem zg_nonfixW {o : Ordinal.{0}} (ho : o < tfBG * ω) :
    Om1 + 1 + (tfBG + 1 + o) < gamma (Om1 + 1 + (tfBG + 1 + o)) := by
  set ν := Om1 + 1 + (tfBG + 1 + o) with hν
  have hE : ω ^ tfBG = tfBG := Low.opow_eq_self_of_SC tfBG_SC
  have h1 : Om1 + 1 + tfBG = tfBG :=
    Ordinal.add_of_omega0_opow_le (c := tfBG) (by rw [hE]; exact tl_Om1_succ_lt_BG) (by rw [hE])
  have hνe : ν = tfBG + (1 + o) := by rw [hν, ← add_assoc, ← add_assoc, h1, add_assoc]
  have hB : tfBG < ν := by
    rw [hνe]; exact lt_add_of_pos_right _ (lt_of_lt_of_le zero_lt_one le_self_add)
  have hBw : ν < tfBG * ω := by
    rw [hνe]
    have hw : tfBG * ω = ω ^ (tfBG + 1) := by rw [opow_add, opow_one, hE]
    have hP : IsPrincipal (· + ·) (tfBG * ω) := by rw [hw]; exact isPrincipal_add_omega0_opow _
    have hBl : tfBG < tfBG * ω := by
      have := (mul_lt_mul_iff_right₀ (tfBG_SC.1)).2 one_lt_omega0
      rwa [mul_one] at this
    exact hP hBl (hP ((gg_one_lt_of_SC tfBG_SC).trans hBl) ho)
  rcases (isNormal_gamma.strictMono.le_apply (x := ν)).lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  have hSC : SC ν := by rw [heq]; exact Lq.lq_gamma_SC ν
  obtain ⟨γ, hγ⟩ := (isPrincipal_add_iff_zero_or_omega0_opow.1 (tl_SC_prin hSC)).resolve_left hSC.1.ne'
  have hw : tfBG * ω = ω ^ (tfBG + 1) := by rw [opow_add, opow_one, hE]
  rw [← hγ, ← hE] at hB
  rw [← hγ, hw] at hBw
  have h1' := (opow_lt_opow_iff_right one_lt_omega0).1 hB
  have h2' := (opow_lt_opow_iff_right one_lt_omega0).1 hBw
  exact absurd (Order.add_one_le_of_lt h1') (not_le.2 h2')

theorem zgBG_ne : tfBG ≠ 0 := tfBG_SC.1.ne'

theorem zgBG_lim : IsSuccLimit tfBG := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC tfBG_SC)

theorem zgW_eq : tfBG * ω = ω ^ (tfBG + 1) := by
  rw [opow_add, opow_one, Low.opow_eq_self_of_SC tfBG_SC]

theorem zgW_prin : IsPrincipal (· + ·) (tfBG * ω) := by rw [zgW_eq]; exact isPrincipal_add_omega0_opow _

theorem zgBG_lt_W : tfBG < tfBG * ω := by
  have := (mul_lt_mul_iff_right₀ (tfBG_SC.1)).2 one_lt_omega0
  rwa [mul_one] at this

theorem zgW_lt_X : tfBG * ω < tlX := by
  rw [zgW_eq]
  have h1 : tfBG + 1 < tlX := tlX_SC.isPrincipal tl_BG_lt_X ((gg_one_lt_of_SC tfBG_SC).trans tl_BG_lt_X)
  have := tlX_SC.2 0 tlX_SC.1 _ h1
  rwa [veblen_zero_apply] at this

/-- `(B_Γ·q + r)/B_Γ = q`, `(B_Γ·q + r) mod B_Γ = r` for `r < B_Γ`. -/
theorem zgQM' (q : Ordinal.{0}) {r : Ordinal.{0}} (hr : r < tfBG) :
    (tfBG * q + r) / tfBG = q ∧ (tfBG * q + r) % tfBG = r := by
  refine ⟨?_, ?_⟩
  · rw [Ordinal.mul_add_div q zgBG_ne r, Ordinal.div_eq_zero_of_lt hr, add_zero]
  · rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]

/-- The quotient `n` of the offset by `B_Γ`. -/
noncomputable def zgQ (c : Ordinal.{0}) : Ordinal.{0} := zbO c / tfBG

/-- The remainder `r` of the offset modulo `B_Γ`. -/
noncomputable def zgM (c : Ordinal.{0}) : Ordinal.{0} := zbO c % tfBG

/-- **The reading** `D(x)·(1 + n) + yrR r x` of the index `B_Γ + 1 + (B_Γ·n + r)`. -/
noncomputable def zgRw (c x : Ordinal.{0}) : Ordinal.{0} := ywV 1 0 x * (1 + zgQ c) + yrR (zgM c) x

theorem zgQM (n : ℕ) {r : Ordinal.{0}} (hr : r < tfBG) :
    zgQ (tfBG + 1 + (tfBG * n + r)) = n ∧ zgM (tfBG + 1 + (tfBG * n + r)) = r := by
  unfold zgQ zgM; rw [zbO_add]; exact zgQM' _ hr

theorem zgRw_eq (n : ℕ) {r : Ordinal.{0}} (hr : r < tfBG) (x : Ordinal.{0}) :
    zgRw (tfBG + 1 + (tfBG * n + r)) x = ywV 1 0 x * ((n + 1 : ℕ) : Ordinal.{0}) + yrR r x := by
  unfold zgRw; rw [(zgQM n hr).1, (zgQM n hr).2]
  congr 2; push_cast; rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, add_comm]

theorem zgDec {c : Ordinal.{0}} (h1 : tfBG + 1 ≤ c) (h2 : c < tfBG * ω) :
    ∃ n : ℕ, ∃ r, r < tfBG ∧ c = tfBG + 1 + (tfBG * n + r) := by
  obtain ⟨o, rfl⟩ := exists_add_of_le h1
  have ho : o < tfBG * ω := le_add_self.trans_lt h2
  have hq : o / tfBG < ω := (Ordinal.lt_mul_iff_div_lt zgBG_ne).1 ho
  obtain ⟨n, hn⟩ := lt_omega0.1 hq
  refine ⟨n, o % tfBG, Ordinal.mod_lt o zgBG_ne, ?_⟩
  rw [← hn, Ordinal.div_add_mod]

theorem zgIdx_lt (n : ℕ) {r : Ordinal.{0}} (hr : r < tfBG) : tfBG + 1 + (tfBG * n + r) < tfBG * ω := by
  have h1 : tfBG + 1 < tfBG * ω := zgW_prin zgBG_lt_W ((gg_one_lt_of_SC tfBG_SC).trans zgBG_lt_W)
  have h2 : tfBG * n + r < tfBG * ω := by
    calc tfBG * n + r < tfBG * n + tfBG := (add_lt_add_iff_left _).2 hr
      _ = tfBG * ((n + 1 : ℕ) : Ordinal.{0}) := by push_cast; rw [mul_add_one]
      _ < tfBG * ω := (mul_lt_mul_iff_right₀ tfBG_SC.1).2 (natCast_lt_omega0 _)
  exact zgW_prin h1 h2

theorem zgLex {n₁ n₂ : ℕ} {r₁ r₂ : Ordinal.{0}} (hr₂ : r₂ < tfBG)
    (h : tfBG * n₁ + r₁ < tfBG * n₂ + r₂) : n₁ < n₂ ∨ (n₁ = n₂ ∧ r₁ < r₂) := by
  rcases lt_trichotomy n₁ n₂ with hl | he | hg
  · exact Or.inl hl
  · subst he; exact Or.inr ⟨rfl, (add_lt_add_iff_left _).1 h⟩
  · exfalso
    have : tfBG * n₂ + r₂ < tfBG * n₁ + r₁ := by
      calc tfBG * n₂ + r₂ < tfBG * n₂ + tfBG := (add_lt_add_iff_left _).2 hr₂
        _ = tfBG * ((n₂ + 1 : ℕ) : Ordinal.{0}) := by push_cast; rw [mul_add_one]
        _ ≤ tfBG * n₁ := mul_le_mul_right (by exact_mod_cast hg) _
        _ ≤ tfBG * n₁ + r₁ := le_self_add
    exact absurd h (not_lt.2 this.le)

theorem zgRlt {D y₁ y₂ : Ordinal.{0}} {n₁ n₂ : ℕ} (hn : n₁ < n₂) (hy : y₁ < D) :
    D * ((n₁ + 1 : ℕ) : Ordinal.{0}) + y₁ < D * ((n₂ + 1 : ℕ) : Ordinal.{0}) + y₂ := by
  calc D * ((n₁ + 1 : ℕ) : Ordinal.{0}) + y₁ < D * ((n₁ + 1 : ℕ) : Ordinal.{0}) + D := (add_lt_add_iff_left _).2 hy
    _ = D * ((n₁ + 1 + 1 : ℕ) : Ordinal.{0}) := by
        rw [Nat.cast_succ (n₁ + 1), mul_add_one]
    _ ≤ D * ((n₂ + 1 : ℕ) : Ordinal.{0}) := mul_le_mul_right (by exact_mod_cast Nat.succ_le_succ hn) _
    _ ≤ _ := le_self_add

/-- **No fixed point**, inversion: `TlCl Z (Γ_{Ω₁+1+(B_Γ+1+o)})`, `o < B_Γ·ω` ⇒ `TlCl Z o`. -/
theorem zgInvW {Z o : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om1) (ho : o < tfBG * ω)
    (h : TlCl Z (gcG (tfBG + 1 + o))) : TlCl Z o := by
  rw [tf_gcG] at h
  have hlt := zg_nonfixW ho
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

/-- **The gated cover** below `Γ_{Ω₁+1+c}` for a limit index `c ∈ (B_Γ+1, B_Γ·ω)`. -/
theorem zgCoverW {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1) {c : Ordinal.{0}} (hl : IsSuccLimit c)
    (hc0 : tfBG + 1 < c) (hc : c < tfBG * ω) :
    ∀ d, GxCl Z (zbU.At Z) d → d < gcG c →
      ∃ b, tfBG + 1 ≤ b ∧ b < c ∧ yrG (zgM b) < Z ∧ d < gcG b := by
  have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1.le
  have hg0 : yrG (zgM (tfBG + 1)) < Z := by
    unfold zgM; rw [zbO_c0, Ordinal.zero_mod, yrG_zero]; exact hZ.1
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
    obtain ⟨n, r, hr, rfl⟩ := zgDec hb (hbc.trans hc)
    rcases hs with hs | ⟨c', hc', -, e⟩
    · have hT := zgInvW hZ hZ1' (le_add_self.trans_lt (hbc.trans hc)) hs.2.2.2
      have hxn : TlCl Z (tfBG * n) := TlCl.mul_nat hZ.1 (zbBG_tl hZ.1) n
      have hTr : TlCl Z r := by
        have := (tlDec hZ _ hT).1 _ hxn le_self_add
        rwa [Ordinal.add_sub_cancel] at this
      have hgo := zgGate hZ hZ1' hr hTr
      have hr1 : r + 1 < tfBG := zgBG_lim.add_one_lt hr
      refine ⟨tfBG + 1 + (tfBG * n + (r + 1)), le_self_add, ?_, ?_, ?_⟩
      · rw [← add_assoc (tfBG * _) r 1, ← add_assoc (tfBG + 1) _ 1]; exact hl.add_one_lt hbc
      · rw [(zgQM n hr1).2]; exact yrG_succ (ev_isSuccLimit_of_inE (gg_SC_eps hZ)) r hgo
      · rw [← add_assoc (tfBG * _) r 1, ← add_assoc (tfBG + 1) _ 1]; exact gcG_lt (lt_add_one _)
    · exfalso
      have h1 : c' < tfBG + 1 + (tfBG * n + r) := hc'.trans ((lt_add_one _).trans_le le_self_add)
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

section Rd

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem zgRw_T (n : ℕ) {r : Ordinal.{0}} (hr : r < tfBG) (hg : yrG r < x) :
    ywV 1 0 x * ((n + 1 : ℕ) : Ordinal.{0}) + yrR r x ∈ Tset x ∧
    ywV 1 0 x * ((n + 1 : ℕ) : Ordinal.{0}) + yrR r x < ywX x ∧ yrR r x < ywV 1 0 x := by
  obtain ⟨-, -, -, hrD⟩ := zgDo_T hx hx1 hr hg
  obtain ⟨hrT, -⟩ := yrR_T hx hx1 hr hg
  obtain ⟨hnT, hnX⟩ := zgDn_T hx hx1 (n + 1)
  obtain ⟨-, -, -, hXE⟩ := ywX_facts hx hx1
  exact ⟨vzT_add hx hx1 hnT hrT, (inE_indec hXE).add_lt hnX (hrD.trans (ywD_lt_X hx hx1)), hrD⟩

/-- `D(x) + 1 < D(x)·(n+1) + y < ϑˣ(Ω₁·Ω₁ + D(x) + 1)` for `y < D(x)`, `0 < n` or `1 < y`. -/
theorem zgRw_sig (n : ℕ) {y : Ordinal.{0}} (hy : y < ywV 1 0 x) (h : 0 < n ∨ 1 < y) :
    ywV 1 0 x + 1 < ywV 1 0 x * ((n + 1 : ℕ) : Ordinal.{0}) + y ∧
    ywV 1 0 x * ((n + 1 : ℕ) : Ordinal.{0}) + y < gq (ywV 1 0 x + 1) x := by
  obtain ⟨hDT, hD1, -⟩ := zbDo_T hx hx1 (o := 1) (one_lt_omega0.trans_le (omega0_le_of_isSuccLimit gc_eps0_lim))
  obtain ⟨-, -, -, hGE, -⟩ := geq_facts hx hx1 hDT hD1
  have hDG : ywV 1 0 x < gq (ywV 1 0 x + 1) x := (lt_add_one _).trans (gmq_gt hx hx1 hDT hD1)
  obtain ⟨-, -, hDE⟩ := zgD_T hx hx1
  have hDl := ev_isSuccLimit_of_inE hDE
  refine ⟨?_, (inE_indec hGE).add_lt (zgDn_lt hGE hDG (n + 1)) (hy.trans hDG)⟩
  have hn1 : ywV 1 0 x ≤ ywV 1 0 x * (n : Ordinal.{0}) + ywV 1 0 x := le_add_self
  rw [Nat.cast_succ, mul_add_one]
  rcases h with hn | hy1
  · have h1 : ywV 1 0 x ≤ ywV 1 0 x * (n : Ordinal.{0}) := by
      have := mul_le_mul_right (show (1 : Ordinal.{0}) ≤ n by exact_mod_cast hn) (ywV 1 0 x)
      rwa [mul_one] at this
    calc ywV 1 0 x + 1 < ywV 1 0 x + ywV 1 0 x := (add_lt_add_iff_left _).2 (by simpa using hDl.add_one_lt hDl.bot_lt)
      _ ≤ ywV 1 0 x * (n : Ordinal.{0}) + ywV 1 0 x := add_le_add h1 le_rfl
      _ ≤ _ := le_self_add
  · calc ywV 1 0 x + 1 < ywV 1 0 x + y := (add_lt_add_iff_left _).2 hy1
      _ ≤ _ := add_le_add hn1 le_rfl

end Rd

theorem zgM_c0 : zgM (tfBG + 1) = 0 := by unfold zgM; rw [zbO_c0, Ordinal.zero_mod]

theorem zgQ_c0 : zgQ (tfBG + 1) = 0 := by unfold zgQ; rw [zbO_c0, Ordinal.zero_div]

theorem zgIdx_succ (n : ℕ) (r : Ordinal.{0}) :
    tfBG + 1 + (tfBG * n + r) + 1 = tfBG + 1 + (tfBG * n + (r + 1)) := by
  rw [add_assoc (tfBG + 1), add_assoc (tfBG * _)]

/-- **THE READING SYSTEM OF THE INDICES `B_Γ + 1 + (B_Γ·n + r)`, `n < ω`, `r < B_Γ`** (gate `yrG r`). -/
noncomputable def zgBw (S : InaccSeq.{0}) : ZbRS where
  c0 := tfBG + 1
  Bd := tfBG * ω
  gt := fun c => yrG (zgM c)
  R := zgRw
  L0 := (zbBGn 0).1
  c0_ne := (lt_of_le_of_lt zero_le (lt_add_one tfBG)).ne'
  c0_lt := zgW_prin zgBG_lt_W ((gg_one_lt_of_SC tfBG_SC).trans zgBG_lt_W)
  Bd_X := zgW_lt_X.le
  L0_g := by rw [zbBGn_g 0]; show (0 : Ordinal.{0}) = yrG (zgM (tfBG + 1)); rw [zgM_c0, yrG_zero]
  L0_E := fun x _ _ => by
    rw [zbBGn_E 0 x]
    show gq (ywV 1 0 x + ((0 : ℕ) : Ordinal.{0})) x = gq (zgRw (tfBG + 1) x) x
    unfold zgRw; rw [zgQ_c0, zgM_c0, yrR_zero, Nat.cast_zero, add_zero, add_zero, add_zero, mul_one]
  L0_top := fun y hy hy1 _ => by
    have h := (zbBGn_codes S 0).1 y hy hy1 (by rw [zbBGn_g]; exact hy.1)
    rw [h]; unfold zbT; norm_num
  L0_poly := by
    have h := (zbBGn_codes S 0).2
    unfold zbT at h; norm_num at h
    exact h
  RT := fun c x hx hx1 h1 h2 hg => by
    obtain ⟨n, r, hr, rfl⟩ := zgDec h1 h2
    change yrG (zgM _) < x at hg
    rw [(zgQM n hr).2] at hg
    rw [zgRw_eq n hr]
    obtain ⟨hT, hX, -⟩ := zgRw_T hx hx1 n hr hg
    obtain ⟨-, -, hX1, -⟩ := ywX_facts hx hx1
    refine ⟨hT, hX.trans hX1, ?_⟩
    rw [← ywV_zero]
    exact ywV_lt_X hx hx1 (mem_T_of_le hx hx1 zero_le) (hx.pos.trans hx1) hT (hX.trans hX1)
      (hx.pos.trans (ywX_facts hx hx1).2.1) hX
  mono := fun b c x hx hx1 h1 hbc hc hgb hgc => by
    obtain ⟨n₂, r₂, hr₂, rfl⟩ := zgDec (h1.trans hbc.le) hc
    obtain ⟨n₁, r₁, hr₁, rfl⟩ := zgDec h1 (hbc.trans hc)
    change yrG (zgM _) < x at hgb hgc
    rw [(zgQM n₁ hr₁).2] at hgb; rw [(zgQM n₂ hr₂).2] at hgc
    show zgRw _ x < zgRw _ x
    rw [zgRw_eq n₁ hr₁, zgRw_eq n₂ hr₂]
    rcases zgLex hr₂ ((add_lt_add_iff_left _).1 hbc) with hn | ⟨rfl, hr⟩
    · exact zgRlt hn (zgRw_T hx hx1 n₁ hr₁ hgb).2.2
    · exact (add_lt_add_iff_left _).2 (yrR_mono hx hx1 hr₂ hr hgc hgb)
  succ := fun b x hb => by
    show zgRw (b + 1) x = zgRw b x + 1
    obtain ⟨o, rfl⟩ := exists_add_of_le hb
    unfold zgRw zgQ zgM
    rw [add_assoc (tfBG + 1) o 1, zbO_add, zbO_add]
    conv_lhs => rw [← Ordinal.div_add_mod o tfBG]
    conv_rhs => rw [← Ordinal.div_add_mod o tfBG]
    have hr1 : o % tfBG + 1 < tfBG := zgBG_lim.add_one_lt (Ordinal.mod_lt o zgBG_ne)
    rw [add_assoc, (zgQM' _ hr1).1, (zgQM' _ hr1).2, (zgQM' _ (Ordinal.mod_lt o zgBG_ne)).1,
      (zgQM' _ (Ordinal.mod_lt o zgBG_ne)).2, yrR_succ, add_assoc]
  gt_le_succ := fun b => by
    show yrG (zgM b) ≤ yrG (zgM (b + 1))
    rcases lt_or_ge b (tfBG + 1) with hb | hb
    · unfold zgM
      rw [show zbO b = 0 from Ordinal.sub_eq_zero_iff_le.2 hb.le, Ordinal.zero_mod, yrG_zero]; exact zero_le
    · obtain ⟨o, rfl⟩ := exists_add_of_le hb
      unfold zgM
      rw [add_assoc (tfBG + 1) o 1, zbO_add, zbO_add]
      conv_lhs => rw [← Ordinal.div_add_mod o tfBG]
      conv_rhs => rw [← Ordinal.div_add_mod o tfBG]
      have hr1 : o % tfBG + 1 < tfBG := zgBG_lim.add_one_lt (Ordinal.mod_lt o zgBG_ne)
      rw [add_assoc, (zgQM' _ hr1).2, (zgQM' _ (Ordinal.mod_lt o zgBG_ne)).2]
      exact yrG_le_succ _
  lim_R := fun c x hl hc0 hc hx hx1 hg => by
    obtain ⟨n, r, hr, rfl⟩ := zgDec hc0.le hc
    change yrG (zgM _) < x at hg
    rw [(zgQM n hr).2] at hg
    show IsSuccLimit (zgRw _ x) ∧ ∃ σ, σ < zgRw _ x ∧ zgRw _ x < gq σ x
    rw [zgRw_eq n hr]
    obtain ⟨-, -, hrD⟩ := zgRw_T hx hx1 n hr hg
    obtain ⟨-, -, hDE⟩ := zgD_T hx hx1
    rcases eq_or_ne r 0 with rfl | hr0
    · have hn : 0 < n := by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · subst h0; simp at hc0
        · exact h0
      rw [yrR_zero, add_zero]
      obtain ⟨h1, h2⟩ := zgRw_sig hx hx1 n (y := 0) hDE.pos (Or.inl hn)
      rw [add_zero] at h1 h2
      refine ⟨?_, ywV 1 0 x + 1, h1, h2⟩
      rw [Nat.cast_succ, mul_add_one]
      exact isSuccLimit_add _ (ev_isSuccLimit_of_inE hDE)
    · have hrl : IsSuccLimit r := by
        rcases zero_or_succ_or_isSuccLimit r with h | ⟨s, hs⟩ | h
        · exact absurd h hr0
        · exfalso
          have h' : IsSuccLimit (Order.succ (tfBG + 1 + (tfBG * n + s))) := by
            rw [succ_eq_add_one, zgIdx_succ, ← succ_eq_add_one s, hs]; exact hl
          exact Order.not_isSuccLimit_succ _ h'
        · exact h
      have hRl : IsSuccLimit (yrR r x) := yr_lim_of_cof hx hx1 hrl hr hg (yrR_cof hx hx1 r hr)
      have h1r : (1 : Ordinal.{0}) < yrR r x := by simpa using hRl.add_one_lt hRl.bot_lt
      obtain ⟨h1, h2⟩ := zgRw_sig hx hx1 n hrD (Or.inr h1r)
      exact ⟨isSuccLimit_add _ hRl, ywV 1 0 x + 1, h1, h2⟩
  cof := fun c x hl hc0 hc hx hx1 hg ν hν => by
    obtain ⟨n, r, hr, rfl⟩ := zgDec hc0.le hc
    change yrG (zgM _) < x at hg
    rw [(zgQM n hr).2] at hg
    change ν < zgRw _ x at hν
    rw [zgRw_eq n hr] at hν
    have hg0 : ∀ m : ℕ, yrG (zgM (tfBG + 1 + (tfBG * m + 0))) < x := fun m => by
      rw [(zgQM m tfBG_SC.1).2, yrG_zero]; exact hx.pos
    rcases eq_or_ne r 0 with rfl | hr0
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · subst h0; simp at hc0
        · exact ⟨n - 1, by omega⟩
      rw [yrR_zero, add_zero, Nat.cast_succ (m + 1), mul_add_one] at hν
      have hlt : tfBG + 1 + (tfBG * (m : Ordinal.{0}) + 0) < tfBG + 1 + (tfBG * ((m + 1 : ℕ) : Ordinal.{0}) + 0) := by
        rw [add_zero, add_zero, Nat.cast_succ, mul_add_one]
        exact (add_lt_add_iff_left _).2 (lt_add_of_pos_right _ tfBG_SC.1)
      rcases le_or_gt ν (ywV 1 0 x * ((m + 1 : ℕ) : Ordinal.{0})) with hνD | hDν
      · refine ⟨tfBG + 1 + (tfBG * m + 0), le_self_add, hlt, hg0 m, ?_⟩
        show ν ≤ zgRw _ x
        rw [zgRw_eq m tfBG_SC.1, yrR_zero, add_zero]; exact hνD
      · obtain ⟨e, rfl⟩ := exists_add_of_le hDν.le
        have he : e < ywV 1 0 x := (add_lt_add_iff_left _).1 hν
        obtain ⟨k, hk⟩ := zgCofD hx hx1 he
        have hkB := yrTw_lt_BG k
        refine ⟨tfBG + 1 + (tfBG * m + yrTw k), le_self_add, ?_, ?_, ?_⟩
        · calc tfBG + 1 + (tfBG * m + yrTw k) < tfBG + 1 + (tfBG * m + tfBG) :=
                (add_lt_add_iff_left _).2 ((add_lt_add_iff_left _).2 hkB)
            _ = _ := by rw [add_zero, Nat.cast_succ, mul_add_one]
        · rw [(zgQM m hkB).2, yrTw_g]; exact hx.pos
        · show ywV 1 0 x * ((m + 1 : ℕ) : Ordinal.{0}) + e ≤ zgRw _ x
          rw [zgRw_eq m hkB]; exact (add_le_add_iff_left _).2 hk
    · have hlt : tfBG + 1 + (tfBG * (n : Ordinal.{0}) + 0) < tfBG + 1 + (tfBG * n + r) :=
        (add_lt_add_iff_left _).2 ((add_lt_add_iff_left _).2 (pos_iff_ne_zero.2 hr0))
      rcases le_or_gt ν (ywV 1 0 x * ((n + 1 : ℕ) : Ordinal.{0})) with hνD | hDν
      · refine ⟨tfBG + 1 + (tfBG * n + 0), le_self_add, hlt, hg0 n, ?_⟩
        show ν ≤ zgRw _ x
        rw [zgRw_eq n tfBG_SC.1, yrR_zero, add_zero]; exact hνD
      · obtain ⟨e, rfl⟩ := exists_add_of_le hDν.le
        have he : e < yrR r x := (add_lt_add_iff_left _).1 hν
        obtain ⟨b', hb', hgb', heb'⟩ := yrR_cof hx hx1 r hr hg e he
        have hb'B : b' < tfBG := hb'.trans hr
        refine ⟨tfBG + 1 + (tfBG * n + b'), le_self_add,
          (add_lt_add_iff_left _).2 ((add_lt_add_iff_left _).2 hb'), ?_, ?_⟩
        · rw [(zgQM n hb'B).2]; exact hgb'
        · show ywV 1 0 x * ((n + 1 : ℕ) : Ordinal.{0}) + e ≤ zgRw _ x
          rw [zgRw_eq n hb'B]; exact (add_le_add_iff_left _).2 heb'
  ex := fun σ ρ c hB h1 h2 hg => by
    obtain ⟨n, r, hr, rfl⟩ := zgDec h1 h2
    change yrG (zgM _) < σ at hg
    rw [(zgQM n hr).2] at hg
    show zgRw _ ρ ∈ TB ρ σ ∧ Googology.Trans.PoR.InaccPsi.R2.pi σ ρ (zgRw _ ρ) = zgRw _ σ
    rw [zgRw_eq n hr, zgRw_eq n hr]
    have h1σ : (1 : Ordinal.{0}) < σ := lu_one_lt_E hB.1
    have h0σ : (0 : Ordinal.{0}) < σ := hB.1.pos
    have hD := ywV_pi hB (mem_TB_of_lt hB h1σ) ((lu_one_lt_E hB.2.1).trans hB.2.2.2) (mem_TB_of_lt hB h0σ)
      (hB.2.1.pos.trans hB.2.2.2)
    rw [pi_lt hB h1σ, pi_lt hB h0σ] at hD
    have hDn := pi_mul_nat hB hD.1 hD.2 (n + 1)
    obtain ⟨hr1, hr2⟩ := yr_pi hB r hr hg
    obtain ⟨h3, h4⟩ := pi_add hB hDn.1 hr1
    exact ⟨h3, by rw [h4, hDn.2, hr2]⟩
  cover := fun c Z hl hc0 hc hZ hZ1 _ d hd hdT => zgCoverW hZ hZ1 hl hc0 hc d hd hdT
  cl := fun c Z h1 h2 hZ hg => by
    obtain ⟨n, r, hr, rfl⟩ := zgDec h1 h2
    change yrG (zgM _) < Z at hg
    rw [(zgQM n hr).2] at hg
    refine GxCl.atom (Or.inl ⟨gcG_SC _, gcG_Om1_lt _, ZbRS.gcG_lt_X (h2.trans zgW_lt_X), ?_⟩)
    have harg : TlCl Z (Om1 + 1 + (tfBG + 1 + (tfBG * n + r))) :=
      TlCl.add (TlCl.add TlCl.om (TlCl.one hZ.1))
        (TlCl.add (TlCl.add (zbBG_tl hZ.1) (TlCl.one hZ.1))
          (TlCl.add (TlCl.mul_nat hZ.1 (zbBG_tl hZ.1) n) (zgYr hZ.1 r hr hg).1))
    rw [tf_gcG]
    exact TlCl.gam hZ.1 harg ((lt_add_one _).trans_le le_self_add)
  D_le := fun c x _ _ _ _ _ => show ywV 1 0 x ≤ ywV 1 0 x * (1 + zgQ c) + yrR (zgM c) x from
    (Ordinal.le_mul_left _ (lt_of_lt_of_le zero_lt_one le_self_add)).trans le_self_add
  BG_top := fun y hy hy1 => zbBG_top S hy hy1
  BG_poly := zbBG_poly S
  BG_c0 := le_self_add.trans gcG_strictMono.le_apply

/-- **`ZbDirect S (B_Γ·ω)`, UNCONDITIONAL**: a layer for every index `B_Γ ≤ B < B_Γ·ω` (`B = B_Γ + 1 + (B_Γ·n + r)`:
the layer of `B_Γ + 1 + (B_Γ·n + a_m)`, `a_m` the tower `Yr.yrTw` above `r`, gate `0`). -/
theorem zgDirectW (S : InaccSeq.{0}) : ZbDirect S (tfBG * ω) := by
  intro B hB1 hB2
  rcases hB1.lt_or_eq with hlt | heq
  · obtain ⟨n, r, hr, rfl⟩ := zgDec (Order.add_one_le_of_lt hlt) hB2
    obtain ⟨m, hm⟩ := yrTw_cof _ hr
    have hmB := yrTw_lt_BG m
    have hg : (zgBw S).gt (tfBG + 1 + (tfBG * n + yrTw m)) < Td.tdK S := by
      show yrG (zgM _) < Td.tdK S
      rw [(zgQM n hmB).2, yrTw_g]; exact Td.tdK_SC.1
    exact zbLayAt_mono ((add_le_add_iff_left _).2 ((add_le_add_iff_left _).2 hm.le))
      ((zgBw S).layAt S le_self_add (zgIdx_lt n hmB) hg)
  · rw [← heq]; exact zbLayAt_BG S

/-- **UPPER ∧ LOWER ∧ CapV at every range restart below `ι(Γ_{Ω₁+1+B}·ω)`, every `B < B_Γ·ω`** (UNCONDITIONAL). -/
theorem zgUVW (S : InaccSeq.{0}) {B l : Ordinal.{0}} (hB : B < tfBG * ω) (hr : CdRange S l)
    (hl : l < iota S (gcG B * ω)) : CdUpper S l ∧ CdLower S l ∧ CdCapV S l :=
  zbUV_of_direct (zgDirectW S) l hr B hB hl

end Googology.Trans.PoR.InaccPsi.R2.Zg
